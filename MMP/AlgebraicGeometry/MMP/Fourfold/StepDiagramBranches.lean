module
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization

/-!
# Projective lc fourfolds: step diagrams and branches of divisors

This file collects three facts about the steps of a program from a projective lc fourfold pair
over `ℂ`.

A permitted step `X → Z ← X⁺` of a projective lc fourfold pair `(X, B)` is a step diagram, with
`D⁻ = K_X + B` and `D⁺ = K_{X⁺} + B⁺`, where `K_{X⁺}` and `B⁺` are the birational transforms
`(f⁺)⁻¹_* f_* K_X` and `(f⁺)⁻¹_* f_* B`. The fields of the diagram come from the step, except
three: `dim X⁺ = 4` because birational varieties have the same dimension; `f⁺_* 𝒪_{X⁺} = 𝒪_Z`
by Stein factorization of the proper birational `f⁺` onto the normal `Z`; and each adjoint
divisor is `ℚ`-Cartier because a positive multiple of it (of its negative, for `D⁻`) is a
relatively ample Cartier divisor.

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a step diagram and `Σ ⊆ Z` its bad locus, the complement of the
largest open of `Z` over which both `f⁻` and `f⁺` are isomorphisms. Every closed point `z ∈ Σ`
has a positive-dimensional fibre under `f⁻` or under `f⁺`: otherwise both fibres are finite, and
a proper birational morphism onto a normal variety is an isomorphism over its finite-fibre
locus, which would contain `z`.

Let `Y` be a variety over a field `k` and `Q = ⋃ᵢ Qᵢ` a union of prime divisors of `Y`. For an
irreducible closed subset `V ⊆ Q` of codimension two in `Y`, some prime divisor `P` of the
normalization `Qᵢ^ν` of some component maps onto `V`, for `ν : Qᵢ^ν ⟶ Qᵢ ⊆ Y`.

## Main results

* `MMP.Fourfold.IsPermittedStep.isFourfoldStepDiagram`: a permitted step of a fourfold is a
  step diagram.
* `MMP.Fourfold.mem_biregularLocus_of_topologicalKrullDim_le`: a proper birational morphism of
  complex varieties onto a normal variety is an isomorphism near every point whose fibre has
  dimension at most `0`.
* `MMP.Fourfold.IsFourfoldStepDiagram.pos_dim_fibre_of_mem_badLocusBase`: for a closed point
  `z ∈ Σ`, `0 < dim (f⁻)⁻¹(z)` or `0 < dim (f⁺)⁻¹(z)`.
* `MMP.Fourfold.exists_primeDivisor_image_primeDivisorNormalization_eq`: some prime divisor of
  `∐ᵢ Qᵢ^ν` maps onto `V`.

## Implementation notes

* A prime divisor of the disjoint union `∐ᵢ Qᵢ^ν` is a prime divisor of one `Qᵢ^ν`, so the
  branch statement is an existence over the index `i` and a prime divisor of
  `MMP.Fourfold.primeDivisorNormalizationScheme (Q i)`; its image is that of its support under
  `MMP.Fourfold.primeDivisorNormalization (Q i)`, as in `MMP.Fourfold.branchNumber`.
* The branch is found by an order-theoretic argument on the points of `Y`. Let `η` be the
  generic point of `V`, `Qᵢ` a component containing it and `g` the generic point of `Qᵢ`. Since
  `ν` is surjective and closed, some specialization `x` of a point `ξ` over `g` lies over `η`;
  the closure of `x` is the branch. Its codimension, the coheight of `x`, is `1`: it is positive
  since `ξ ≠ x`, and at most one since `ν`, being integral, is strictly monotone for
  specialization (incomparability, `Ideal.IsIntegral.comap_lt_comap`), so a longer chain above
  `x` would give, with the generic point of `Y`, a chain of length three above `η`. Finiteness
  of the normalization is not used.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace MMP.Fourfold

/-! ### Every surface in a divisor has a branch on the normalization -/

/-- The normalization of a prime divisor, followed by its inclusion, maps onto the divisor. -/
private theorem exists_primeDivisorNormalization_eq {Y : Scheme} (S : MMP.Mori.PrimeDivisor Y)
    {y : Y} (hy : y ∈ S.support) : ∃ x, primeDivisorNormalization S x = y := by
  haveI := S.integral
  obtain ⟨s, rfl⟩ : y ∈ Set.range S.idealSheaf.subschemeι := by
    rwa [S.idealSheaf.range_subschemeι]
  letI := Stacks.AlgebraicGeometry.Normalization.quasiCompact_fromGenericPointResidueFields
    S.idealSheaf.subscheme (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  set f := Stacks.AlgebraicGeometry.Normalization.fromGenericPointResidueFields
    S.idealSheaf.subscheme
  have : IsDominant f.fromNormalization := by
    have hf : IsDominant f := inferInstance
    rw [← f.toNormalization_fromNormalization] at hf
    exact IsDominant.of_comp f.toNormalization _
  obtain ⟨x, hx⟩ := f.fromNormalization.surjective s
  refine ⟨x, ?_⟩
  rw [primeDivisorNormalization, Scheme.Hom.comp_apply]
  exact congrArg S.idealSheaf.subschemeι hx

/-- **Incomparability.** Over an integral ring map, two comparable primes with the same
contraction are equal. -/
private theorem eq_of_le_of_comap_eq_of_isIntegral {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) {P Q : Ideal S} [P.IsPrime] (hPQ : P ≤ Q)
    (h : P.comap φ = Q.comap φ) : P = Q := by
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hφ⟩
  by_contra hne
  exact (Ideal.IsIntegral.comap_lt_comap (R := R) (lt_of_le_of_ne hPQ hne)).ne h

/-- Incomparability on spectra: for an integral ring map `φ`, two points of `Spec S` related by
specialization and with the same image under `Spec φ` are equal. -/
private theorem eq_of_specializes_of_isIntegral_specMap {R S : CommRingCat} (φ : R ⟶ S)
    (hφ : φ.hom.IsIntegral) (p q : PrimeSpectrum S) (hpq : p ⤳ q)
    (hc : Spec.map φ p = Spec.map φ q) : p = q := by
  rw [← PrimeSpectrum.le_iff_specializes] at hpq
  exact PrimeSpectrum.ext (eq_of_le_of_comap_eq_of_isIntegral _ hφ hpq
    (congrArg PrimeSpectrum.asIdeal hc))

/-- Incomparability for an integral morphism of affine schemes. -/
private theorem eq_of_specializes_of_isIntegralHom_of_isAffine {X Z : Scheme} [IsAffine X]
    [IsAffine Z] (f : X ⟶ Z) [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') :
    t = t' := by
  have hg : (f.appTop).hom.IsIntegral := f.isIntegral_app ⊤ (isAffineOpen_top Z)
  have hc : (Spec.map f.appTop) (X.isoSpec.hom t) = (Spec.map f.appTop) (X.isoSpec.hom t') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he]
  have heq := congrArg X.isoSpec.inv (eq_of_specializes_of_isIntegral_specMap _ hg _ _
    (h.map X.isoSpec.hom.continuous) hc)
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at heq

/-- **Incomparability.** The fibres of an integral morphism carry no nontrivial
specializations. -/
private theorem eq_of_specializes_of_isIntegralHom {X Z : Scheme} (f : X ⟶ Z) [IsIntegralHom f]
    {t t' : X} (h : t ⤳ t') (he : f t = f t') : t = t' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f t')) isOpen_univ
  have ht' : t' ∈ f ⁻¹ᵁ U := hmem
  have ht : t ∈ f ⁻¹ᵁ U := h.mem_open (f ⁻¹ᵁ U).isOpen ht'
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  let a : (f ⁻¹ᵁ U).toScheme := ⟨t, ht⟩
  let b : (f ⁻¹ᵁ U).toScheme := ⟨t', ht'⟩
  have hab : a ⤳ b := subtype_specializes_iff _ _ |>.2 h
  have hfab : (f ∣_ U) a = (f ∣_ U) b := Subtype.ext
    ((morphismRestrict_base_coe f U a).trans (he.trans (morphismRestrict_base_coe f U b).symm))
  exact congrArg Subtype.val (eq_of_specializes_of_isIntegralHom_of_isAffine (f ∣_ U) hab hfab)

/-- An integral morphism is strictly monotone for the specialization orders. -/
private theorem strictMono_of_isIntegralHom {X Z : Scheme} (f : X ⟶ Z) [IsIntegralHom f] :
    StrictMono f := by
  intro a b hab
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
  refine ⟨hab.1.map f.continuous, fun h => hab.2 ?_⟩
  rw [eq_of_specializes_of_isIntegralHom f hab.1 ((hab.1.map f.continuous).antisymm h).eq]

/-- A strictly monotone map whose image lies strictly below a single element `b` raises
coheight by at least one: a chain above `x` maps to a chain above `f x`, which `b` extends. -/
private theorem coheight_le_of_strictMono_of_lt {α β : Type*} [Preorder α] [Preorder β]
    {f : α → β} (hf : StrictMono f) {b : β} (hb : ∀ a, f a < b) (x : α) (n : ℕ)
    (hn : coheight (f x) ≤ n + 1) : coheight x ≤ n := by
  rw [Order.coheight_le_iff']
  intro p hp
  have hlast : (p.map f hf).last < b := hb _
  have hq := (Order.length_le_coheight_head (p := (p.map f hf).snoc b hlast)).trans
    (by simpa [hp] using hn)
  simp only [RelSeries.snoc_length, LTSeries.map_length, Nat.cast_add, Nat.cast_one] at hq
  exact Nat.cast_le.2 (Nat.le_of_succ_le_succ (by exact_mod_cast hq))

/-- The generic point of an integral scheme lies strictly above every point of a prime
divisor. -/
public theorem lt_genericPoint_of_mem_support {Y : Scheme} [IsIntegral Y]
    (S : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ S.support) : y < genericPoint Y := by
  have hle : ∀ z : Y, z ≤ genericPoint Y := fun z =>
    (Scheme.le_iff_specializes).2 ((genericPoint_spec Y).specializes (Set.mem_univ z))
  refine lt_of_le_not_ge (hle y) fun h => ?_
  have hgy : y ≤ S.genericPoint := (Scheme.le_iff_specializes).2
    (specializes_iff_mem_closure.2 (AlgebraicGeometry.PrimeDivisor.support_eq_closure S ▸ hy))
  have : IsMax S.genericPoint := fun z _ => (hle z).trans (h.trans hgy)
  rw [← Order.coheight_eq_zero] at this
  exact zero_ne_one (this ▸ AlgebraicGeometry.PrimeDivisor.coheight_genericPoint S)

/-- **Every surface has a branch.** Let `Y` be a variety over `k`, `Q` a family of prime
divisors of `Y` and `V` an irreducible closed subset of codimension two in `Y` contained in
`⋃ᵢ Qᵢ`. Then some prime divisor `P` of the normalization of some `Qᵢ` maps onto `V`. -/
@[mmp "lem_oai4_c2_normalization_branch_positive"]
public theorem exists_primeDivisor_image_primeDivisorNormalization_eq {k : Type*} [Field k]
    {Y : Scheme} (sY : Y ⟶ Spec (.of k)) [IsVariety k sY] {ι : Type*}
    (Q : ι → MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (hV : codimension V = 2)
    (hVQ : (V : Set Y) ⊆ ⋃ i, (Q i).support) :
    ∃ (i : ι) (P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme (Q i))),
      primeDivisorNormalization (Q i) '' P.support = V := by
  set η : Y := irreducibleSetEquivPoints V
  have hVη : IrreducibleCloseds.closureSingleton η = V :=
    (irreducibleSetEquivPoints (α := Y)).symm_apply_apply V
  have hclη : closure ({η} : Set Y) = V := congrArg SetLike.coe hVη
  have hcohη : coheight η = 2 := by
    rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hVη, hV]
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hVQ (hclη ▸ subset_closure (Set.mem_singleton η)))
  set S := Q i
  set ν := primeDivisorNormalization S
  have hνc : IsClosedMap ν := ν.isClosedMap
  set g := S.genericPoint
  have hSg : S.support = closure {g} := AlgebraicGeometry.PrimeDivisor.support_eq_closure S
  have hcohg : coheight g = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint S
  obtain ⟨ξ, hξ⟩ := exists_primeDivisorNormalization_eq S
    (hSg ▸ subset_closure (Set.mem_singleton g))
  obtain ⟨x, hxξ, hx⟩ : η ∈ ν '' closure {ξ} := by
    rwa [← hνc.closure_image_eq_of_continuous ν.continuous, Set.image_singleton, hξ, ← hSg]
  have hxlt : x < ξ := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2
      (specializes_iff_mem_closure.2 hxξ)) fun h => ?_
    have h1 : g ≤ η := by
      rw [← hξ, ← hx, Scheme.le_iff_specializes]
      exact ((Scheme.le_iff_specializes).1 h).map ν.continuous
    have h2 : η ≤ g := (Scheme.le_iff_specializes).2
      (specializes_iff_mem_closure.2 (hSg ▸ hi))
    have hgη : g = η :=
      ((Scheme.le_iff_specializes).1 h2).antisymm ((Scheme.le_iff_specializes).1 h1) |>.eq
    rw [hgη, hcohη] at hcohg
    norm_num at hcohg
  have hcohx : coheight x = 1 :=
    le_antisymm (coheight_le_of_strictMono_of_lt (strictMono_of_isIntegralHom ν)
      (b := genericPoint Y) (fun a => lt_genericPoint_of_mem_support S
        (range_primeDivisorNormalization_subset S ⟨a, rfl⟩)) x 1
      (by rw [hx, hcohη]; rfl)) (le_trans le_add_self (Order.coheight_add_one_le hxlt))
  refine ⟨i, ⟨Stacks.Chow.integralComponentAt x, Stacks.Chow.isIntegral_integralComponentAt x,
    ?_⟩, ?_⟩
  · change codimension (IrreducibleCloseds.closureSingleton
      (Stacks.Chow.genericPointOf _ (Stacks.Chow.isIntegral_integralComponentAt x))) = 1
    rw [Stacks.Chow.genericPointOf_integralComponentAt,
      Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hcohx]
  · change ν '' ((Stacks.Chow.integralComponentAt x).support : Set _) = V
    rw [Stacks.Chow.coe_support_integralComponentAt,
      ← hνc.closure_image_eq_of_continuous ν.continuous, Set.image_singleton, hx, hclη]

/-! ### Permitted steps and step diagrams -/

section StepDiagram

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori

/-- A `ℚ`-divisor with a relatively ample Cartier multiple is `ℚ`-Cartier. -/
private theorem isQCartier_of_hasRelativelyAmpleMultiple {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} {f : X ⟶ Y}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsQCartier := by
  obtain ⟨m, hm, L, hL, hLD, -⟩ := h
  exact ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩

/-- If `-D` is `ℚ`-Cartier then so is `D`. -/
private theorem isQCartier_of_neg {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} (h : (-D).IsQCartier) :
    D.IsQCartier := by
  obtain ⟨m, hm, hC⟩ := h
  exact ⟨-m, neg_ne_zero.mpr hm, by rwa [neg_smul, ← smul_neg]⟩

section

variable {X X' Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- A permitted step `(X⁺, B⁺, f⁺)` for `(X, B, R, f)`, with `X` a fourfold over `ℂ`, is a step
diagram `(X, B) → Z ← (X⁺, B⁺)`: `D⁻ = K + B` and `D⁺ = (f⁺)⁻¹_* f_* K + (f⁺)⁻¹_* f_* B`. -/
@[mmp "lem_oai4_c3_permitted_step_is_step_diagram"]
public theorem IsPermittedStep.isFourfoldStepDiagram {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (h : IsPermittedStep sX sZ sX' K B R f fp) (hdim : topologicalKrullDim X = 4) :
    IsFourfoldStepDiagram sX sZ sX' K B f fp := by
  have hc := h.isContractionOfRay.toIsContraction
  have hs := h.isSmallMorphism_step
  have : MMP.Mori.IsVariety ℂ sX := hc.isNormalVariety_source.1
  have : MMP.Mori.IsVariety ℂ sZ := hc.isNormalVariety_target.1
  have : MMP.Mori.IsVariety ℂ sX' := hs.isNormalVariety_source.1
  have : IsProper fp := hs.isProper
  exact
  { isProjectiveVariety_minus := h.isProjectiveVariety
    isNormalVariety_minus := hc.isNormalVariety_source
    dim_minus := hdim
    isProjectiveVariety_plus := h.isProjectiveVariety_step
    isNormalVariety_plus := hs.isNormalVariety_source
    dim_plus := by
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX'
        hs.isBirationalMorphism, MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
        sZ sX h.isBirationalMorphism, hdim]
    isProjectiveVariety_target := h.isProjectiveVariety_target
    isNormalVariety_target := hc.isNormalVariety_target
    comp_eq_minus := hc.comp_eq
    comp_eq_plus := hs.comp_eq
    isProjectiveMorphism_minus := hc.isProjectiveMorphism
    isProjectiveMorphism_plus := h.isProjectiveMorphism_step
    isBirationalMorphism_minus := h.isBirationalMorphism
    isIso_app_minus := hc.isIso_app
    isIso_app_plus := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      sX' sZ hs.isNormalVariety_source.1 hc.isNormalVariety_target fp
      hs.isBirationalMorphism).1
    isSmallMorphism_plus := hs
    isCanonicalDivisor := h.isCanonicalDivisor
    nonneg := h.isLogCanonicalPair.2.1
    isQCartier_minus :=
      isQCartier_of_neg (isQCartier_of_hasRelativelyAmpleMultiple h.hasRelativelyAmpleMultiple)
    isQCartier_plus := isQCartier_of_hasRelativelyAmpleMultiple h.hasRelativelyAmpleMultiple_step
    hasRelativelyAmpleMultiple_minus := h.hasRelativelyAmpleMultiple
    hasRelativelyAmpleMultiple_plus := h.hasRelativelyAmpleMultiple_step }

end

/-! ### Bad points of a step diagram have a positive-dimensional fibre -/

/-- A proper birational morphism of complex varieties onto a normal variety is an isomorphism
over a neighbourhood of every point whose fibre has dimension at most `0`. -/
public theorem mem_biregularLocus_of_topologicalKrullDim_le {U R : Scheme.{0}}
    {sU : U ⟶ Spec (.of ℂ)} {sR : R ⟶ Spec (.of ℂ)} (hU : AlgebraicGeometry.IsVariety ℂ sU)
    (hR : AlgebraicGeometry.IsVariety ℂ sR)
    [IsNormal R] (f : U ⟶ R) (hf : f ≫ sR = sU) [IsProper f] (hb : IsBirationalMorphism f)
    {z : R} (hz : topologicalKrullDim (f ⁻¹' {z}) ≤ 0) : z ∈ biregularLocus f := by
  have := hU.toIsIntegral
  have := hR.toIsIntegral
  obtain ⟨⟨hO, hiso⟩, -, -⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq
    ℂ hU hR f hf (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  exact le_biregularLocus (V := ⟨_, hO⟩) hiso
    (MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le f z hz)

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, every closed point `z` of the bad locus
`badLocusBase fm fp` has a positive-dimensional fibre under `f⁻` or under `f⁺`: otherwise both
fibres have dimension at most `0`, and `z` lies in both biregular loci. -/
@[mmp "lem_oai4_c1_bad_locus_positive_fibres"]
public theorem IsFourfoldStepDiagram.pos_dim_fibre_of_mem_badLocusBase
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) {z : Z} (hz : IsClosed ({z} : Set Z))
    (hmem : z ∈ badLocusBase fm fp) :
    0 < topologicalKrullDim (fm ⁻¹' {z}) ∨ 0 < topologicalKrullDim (fp ⁻¹' {z}) := by
  by_contra! hne
  have hZ := h.isNormalVariety_target
  have := hZ.2
  have : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have := h.isProper_plus
  exact hmem ⟨mem_biregularLocus_of_topologicalKrullDim_le h.isNormalVariety_minus.1 hZ.1 fm
      h.comp_eq_minus h.isBirationalMorphism_minus hne.1,
    mem_biregularLocus_of_topologicalKrullDim_le h.isNormalVariety_plus.1 hZ.1 fp
      h.comp_eq_plus h.isBirationalMorphism_plus hne.2⟩

end StepDiagram

end MMP.Fourfold
