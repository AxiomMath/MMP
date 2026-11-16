module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Slc.NormalizedSections
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Abundance.SlcCurveNormalizedSections
import MMP.AlgebraicGeometry.MMP.Abundance.NormalizedSectionDegreeZero
import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix

/-!
# Normalized sections with prescribed values on an slc curve

Let `(C, Δ)` be an slc curve over an algebraically closed field `k` of characteristic zero,
with normalization `n : C̄ = ⨆ᵢ Cᵢ ⟶ C`, and let `g : C ⟶ Z` be a proper morphism to an affine
scheme `Z` of finite type over `k` such that `K_C + Δ` is `g`-nef. Let `m > 0` with `mΔ`
integral. A normalized section `u₀` of `𝒪_C(24m(K_C + Δ))` on a union `C₀` of irreducible
components of `C` extends to a normalized section `u` on all of `C` which does not vanish at any
point of a prescribed finite set `Q` of closed points outside `C₀`.

## Main results

* `MMP.Flips.NormalizationComponents.exists_isNormalizedSlcSection_extend_of_finite`
* `MMP.Flips.NormalizationComponents.exists_mem_pluricanonicalSections_sub_dlogPow_of_affine`,
  `MMP.Flips.NormalizationComponents.exists_mem_pluricanonicalSections_sub_dlogPow_of_proper_pos`:
  on one smooth affine curve, or one smooth proper curve with `deg(K + Δ) > 0`, a section with
  leading coefficient `1` at the points of `⌊Δ⌋` and no zero at prescribed points.

* `MMP.Flips.NormalizationComponents.topologicalKrullDim_X`,
  `MMP.Flips.NormalizationComponents.isSmoothScheme_n`,
  `MMP.Flips.NormalizationComponents.component_dichotomy`: the components `Cᵢ` are smooth curves,
  each proper and contracted by `g`, or affine.
* `MMP.Flips.VanishesTo`, `MMP.Flips.exists_vanishesTo_sub_const_smul`: orders of rational
  pluricanonical forms on a curve, and the fibre of `𝒪(nK + E)` at a point.
* `MMP.Flips.sum_nonneg_of_isRelativelyNef`: a relatively nef divisor has nonnegative degree on a
  contracted smooth proper curve.

## Implementation notes

A normalized section of `𝒪_C(24m(K_C + Δ))` is a family of normalized sections on the
components `Cᵢ` of the normalization
(`MMP.Flips.NormalizationComponents.isNormalizedSlcSection_iff_forall_isNormalizedSection`). On
the components in `C₀` we take the prescribed `u₀`; on every other component `Cᵢ` we choose a
normalized section not vanishing over `Q`. Such a `Cᵢ` is either affine, or proper and contracted
by `g`, so that `deg(K_{Cᵢ} + Δᵢ) ≥ 0`. In the affine case and the proper case of positive
degree, sections with prescribed fibres at finitely many points exist (on the affine curve
directly, on the proper curve by Riemann–Roch), and a general `k`-affine combination of them is
nonvanishing at all the points over `Q`. In degree zero the normalized section has no zeros.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 8.7, 12.2.11
-/

public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips.NormalizationComponents

open MMP.Mori

variable {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
  {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents sC hC)

private theorem isClosedImmersion_sigmaι (i : N.ι) : IsClosedImmersion (Limits.Sigma.ι N.X i) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  have : Set.range (Limits.Sigma.ι N.X i) = sigmaMk N.X '' Set.range (Sigma.mk i) := by
    ext x
    simp [← sigmaMk_mk]
  rw [this]
  exact (sigmaMk N.X).isClosedMap _ isClosed_range_sigmaMk

private theorem n_eq (i : N.ι) :
    ∃ φ : (∐ N.X) ≅ Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC,
    N.n i = Limits.Sigma.ι N.X i ≫ φ.hom ≫ slcCurveNormalization C hC := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  refine ⟨φ, ?_⟩
  rw [hφ]
  simp

/-- Each component map `nᵢ : Cᵢ ⟶ C` of the normalization is finite. -/
theorem isFinite_n [LocallyOfFiniteType sC] (i : N.ι) : IsFinite (N.n i) := by
  obtain ⟨φ, h⟩ := n_eq N i
  have := isClosedImmersion_sigmaι N i
  have : IsFinite (slcCurveNormalization C hC) := isFinite_normalizationOverField k sC
  rw [h]
  infer_instance

open Stacks.AlgebraicGeometry.Normalization in
/-- Every nonempty component `Cᵢ` has a point lying over a generic point of `C`. -/
theorem exists_point_generic (i : N.ι) [Nonempty (N.X i)] :
    ∃ x : N.X i, (N.n i) x ∈ genericPoints C := by
  obtain ⟨φ, h⟩ := n_eq N i
  let _ := quasiCompact_fromGenericPointResidueFields C hC
  let f := fromGenericPointResidueFields C
  have hdom : IsDominant (f.toNormalization) := inferInstance
  have hopen : IsOpen (Set.range ((Limits.Sigma.ι N.X i ≫ φ.hom : N.X i ⟶ _))) :=
    (inferInstance : IsOpenImmersion (Limits.Sigma.ι N.X i ≫ φ.hom)).base_open.isOpen_range
  obtain ⟨x0⟩ : Nonempty (N.X i) := inferInstance
  obtain ⟨y, x, hx⟩ := hdom.denseRange.exists_mem_open hopen ⟨_, ⟨x0, rfl⟩⟩
  refine ⟨x, ?_⟩
  have h1 : (N.n i) x = f y := by
    rw [h, ← Category.assoc, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply]
    show (Scheme.Hom.toNormalization f ≫ Scheme.Hom.fromNormalization f) y = f y
    rw [Scheme.Hom.toNormalization_fromNormalization]
  rw [h1]
  obtain ⟨⟨η, z⟩, rfl⟩ := (sigmaMk _).surjective y
  rw [sigmaMk_mk]
  rw [← Scheme.Hom.comp_apply, ι_fromGenericPointResidueFields, C.fromSpecResidueField_apply]
  exact η.2

private theorem one_le_topologicalKrullDim_of_specializes {X : Type*} [TopologicalSpace X]
    [T0Space X] {a b : X} (hab : a ⤳ b) (hne : a ≠ b) : 1 ≤ topologicalKrullDim X := by
  let cl : X → IrreducibleCloseds X := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : cl b < cl a := by
    refine lt_of_le_of_ne ?_ ?_
    · change closure {b} ⊆ closure {a}
      exact hab.closure_subset
    · intro heq
      have h2 : a ∈ closure ({b} : Set X) := by
        have : a ∈ (cl a : Set X) := subset_closure rfl
        rwa [← heq] at this
      exact hne (hab.antisymm (specializes_iff_mem_closure.mpr h2)).eq
  exact Order.one_le_krullDim_iff.2 ⟨cl b, cl a, hlt⟩

/-- The components `Cᵢ` of the normalization of a curve are curves: `dim Cᵢ = 1`. -/
theorem topologicalKrullDim_X [LocallyOfFiniteType sC] (hn : IsNFold sC 1) (i : N.ι) :
    topologicalKrullDim (N.X i) = 1 := by
  have := isFinite_n N i
  have hC1 : topologicalKrullDim C ≤ 1 :=
    _root_.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun Z hZ => (hn.2.2 Z hZ).le
  refine le_antisymm ((topologicalKrullDim_le_of_isIntegralHom (N.n i)).trans hC1) ?_
  obtain ⟨x, hx⟩ := exists_point_generic N i
  have hZ : closure {(N.n i) x} ∈ irreducibleComponents C := hx
  have hdimZ := hn.2.2 _ hZ
  have hc : ∃ c ∈ closure ({(N.n i) x} : Set C), c ≠ (N.n i) x := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have : DiscreteTopology (closure ({(N.n i) x} : Set C)) := by
      have : Subsingleton (closure ({(N.n i) x} : Set C)) :=
        ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
      infer_instance
    have h0 := topologicalKrullDim_zero_of_discreteTopology (closure ({(N.n i) x} : Set C))
    rw [hdimZ] at h0
    exact absurd h0 (by norm_num)
  obtain ⟨c, hcZ, hcne⟩ := hc
  obtain ⟨x', rfl⟩ : c ∈ Set.range (N.n i) :=
    closure_minimal (Set.singleton_subset_iff.2 (Set.mem_range_self x))
      (N.n i).isClosedMap.isClosed_range hcZ
  have hxx' : x ≠ x' := fun h => hcne (by rw [h])
  by_cases hηx : x = genericPoint (N.X i)
  · exact one_le_topologicalKrullDim_of_specializes (genericPoint_specializes x')
      (by rwa [← hηx])
  · exact one_le_topologicalKrullDim_of_specializes (genericPoint_specializes x) (Ne.symm hηx)

/-- The components `Cᵢ` of the normalization of an slc curve are smooth over `k`. -/
theorem isSmoothScheme_n [PerfectField k] {Δ : QWeilDivisor C} (hΔ : IsSlcCurve sC Δ)
    (i : N.ι) :
    IsSmoothScheme (N.n i ≫ sC) := by
  obtain ⟨φ, h⟩ := n_eq N i
  have := hΔ.smooth_normalization sC hC
  have : Smooth (N.n i ≫ sC) := by
    rw [h, Category.assoc, Category.assoc]
    infer_instance
  exact MMP.Mori.isSmoothScheme_of_smooth ‹_›

private theorem isProper_of_const [IsAlgClosed k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] (h : X ⟶ Z)
    (hh : h ≫ sZ = sX) [IsProper h] [AlgebraicGeometry.IsReduced X] [Nonempty X] (z : Z)
    (hz : ∀ x, h x = z) : IsProper sX := by
  have hrange : Set.range h = {z} := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨x, hz x⟩, fun _ ⟨x', hx'⟩ => hx' ▸ hz x'⟩
  have hcl : IsClosed ({z} : Set Z) := hrange ▸ h.isClosedMap.isClosed_range
  have : IsClosedImmersion (Z.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hcl
  have hsurj : Surjective (h.fiberι z) := ⟨fun x => by
    rw [← Set.mem_range, Scheme.Hom.range_fiberι]
    exact hz x⟩
  have : IsClosedImmersion (h.fiberι z) :=
    (inferInstance : IsClosedImmersion (Limits.pullback.fst h (Z.fromSpecResidueField z)))
  have : IsIso (h.fiberι z) := isIso_of_isClosedImmersion_of_surjective _
  have hX : sX = inv (h.fiberι z) ≫ h.fiberToSpecResidueField z ≫
      (Z.fromSpecResidueField z ≫ sZ) := by
    have h' : h = inv (h.fiberι z) ≫ h.fiberToSpecResidueField z ≫ Z.fromSpecResidueField z := by
      rw [← h.fiber_fac z, IsIso.inv_hom_id_assoc]
    rw [← hh]
    conv_lhs => rw [h']
    simp only [Category.assoc]
  have hiso : IsIso (Z.fromSpecResidueField z ≫ sZ) := by
    rw [← SpecMap_residueFieldIsoBase_inv sZ z hcl]
    infer_instance
  rw [hX]
  infer_instance

private theorem finite_of_closed_points {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] (F : Set X) (hF : IsClosed F) (hcl : ∀ x ∈ F, IsClosed {x}) : F.Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  refine Set.Finite.sUnion hSfin fun T hT => ?_
  obtain ⟨g, hg⟩ := QuasiSober.sober (hSirr T hT) (hSclosed T hT)
  have := hcl g (Set.subset_sUnion_of_mem hT hg.mem)
  rw [← hg.def, this.closure_eq]
  exact Set.finite_singleton g

private theorem isAffine_of_nonconst {X Z : Scheme.{u}} [IsAffine Z] [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] (hdim : topologicalKrullDim X = 1)
    (h : X ⟶ Z) [IsProper h]
    (hnc : ∃ x, h x ≠ h (genericPoint X)) : IsAffine X := by
  have : IsNoetherian X := ⟨⟩
  have hclosed : ∀ x : X, x ≠ genericPoint X → IsClosed {x} := fun x hx =>
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X hdim hx
  have hfib : ∀ z, (h ⁻¹' {z}).Finite := by
    intro z
    by_cases hη : h (genericPoint X) = z
    · refine (Set.finite_singleton (genericPoint X)).subset ?_
      intro x hx
      by_contra hxη
      have hhx : IsClosed {h x} := by simpa using h.isClosedMap _ (hclosed x hxη)
      have hzcl : IsClosed {h (genericPoint X)} := by
        have : h x = h (genericPoint X) := by rw [hη]; exact hx
        rwa [this] at hhx
      obtain ⟨x1, hx1⟩ := hnc
      have hm := specializes_iff_mem_closure.mp ((genericPoint_specializes x1).map h.continuous)
      rw [hzcl.closure_eq] at hm
      exact hx1 hm
    · by_cases hne : (h ⁻¹' {z}).Nonempty
      · obtain ⟨x0, hx0⟩ := hne
        have hx0η : x0 ≠ genericPoint X := fun e => hη (by rw [← e]; exact hx0)
        have hzcl : IsClosed {z} := by
          have := h.isClosedMap _ (hclosed x0 hx0η)
          have h2 : h '' {x0} = {z} := by simpa using hx0
          rwa [h2] at this
        refine finite_of_closed_points _ (hzcl.preimage h.continuous) fun x hx => hclosed x ?_
        intro e
        exact hη (by rw [← e]; exact hx)
      · rw [Set.not_nonempty_iff_eq_empty.1 hne]
        exact Set.finite_empty
  have : LocallyQuasiFinite h := LocallyQuasiFinite.of_finite_preimage_singleton h hfib
  have : IsFinite h := IsFinite.of_isProper_of_locallyQuasiFinite h
  exact isAffine_of_isAffineHom h

private theorem not_isProper_of_isAffine {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsAffine X] (hdim : topologicalKrullDim X = 1) :
    ¬ IsProper sX := by
  intro hp
  have : IsFinite sX := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hp, inferInstance⟩
  have h1 := topologicalKrullDim_le_of_isIntegralHom sX
  have h0 : topologicalKrullDim (Spec (.of k)) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [hdim] at h1
  exact absurd (h1.trans h0) (by norm_num)

/-- The components `Cᵢ` of the normalization of an slc curve are quasi-compact. -/
theorem compactSpace_X {Δ : QWeilDivisor C} (hΔ : IsSlcCurve sC Δ) (i : N.ι) :
    CompactSpace (N.X i) := by
  have : LocallyOfFiniteType sC := hΔ.1.1.2.1
  have : QuasiCompact sC := hΔ.1.1.2.2
  have := isFinite_n N i
  exact QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ sC)

/-- For `g : C ⟶ Z` proper to an affine `Z`, each component `Cᵢ` is either proper over `k` and
contracted to a point by `nᵢ ≫ g`, or affine and not proper over `k`. -/
theorem component_dichotomy [IsAlgClosed k] {Δ : QWeilDivisor C} (hΔ : IsSlcCurve sC Δ)
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] [IsAffine Z]
    (g : C ⟶ Z) [IsProper g] (hg : g ≫ sZ = sC) (i : N.ι) :
    (IsProper (N.n i ≫ sC) ∧
      ∀ x, (N.n i ≫ g) x = (N.n i ≫ g) (genericPoint (N.X i))) ∨
    (IsAffine (N.X i) ∧ ¬ IsProper (N.n i ≫ sC)) := by
  have hft : LocallyOfFiniteType sC := hΔ.1.1.2.1
  have hfin := isFinite_n N i
  have hdim := topologicalKrullDim_X N hΔ.1 i
  have : CompactSpace (N.X i) := compactSpace_X N hΔ i
  by_cases hc : ∀ x, (N.n i ≫ g) x = (N.n i ≫ g) (genericPoint (N.X i))
  · exact Or.inl ⟨isProper_of_const sZ (N.n i ≫ g) (by rw [Category.assoc, hg]) _ hc, hc⟩
  · right
    push Not at hc
    have haff : IsAffine (N.X i) := isAffine_of_nonconst hdim (N.n i ≫ g) hc
    exact ⟨haff, not_isProper_of_isAffine _ hdim⟩

end MMP.Flips.NormalizationComponents

namespace MMP.Flips

open MMP.Mori

section Order

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

private theorem ord_one' (x : X) : X.ord (1 : X.functionField) x = 0 := by
  simpa using MMP.Mori.ord_zpow x (one_ne_zero (α := X.functionField)) 0

private theorem ord_pow' {g : X.functionField} (hg : g ≠ 0) (x : X) (n : ℕ) :
    X.ord (g ^ n) x = n * X.ord g x := by
  simpa using MMP.Mori.ord_zpow x hg n

/-- In a Noetherian domain of dimension at most one, a nonzero nonunit has positive order. -/
private theorem ofAdd_one_le_ordFrac {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x : R}
    (hx0 : x ≠ 0) (hx : ¬ IsUnit x) :
    ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      Ring.ordFrac R (algebraMap R K x) := by
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  have : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [ne_eq, Ideal.span_singleton_eq_top])
  have hpos : 0 < Ring.ord R x := Module.length_pos
  rw [Ring.ordFrac_eq_ord R hx0, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm]
  have : 1 ≤ n := by
    rw [← hn] at hpos
    exact_mod_cast hpos
  exact_mod_cast (Multiplicative.ofAdd_le.mpr (by exact_mod_cast this))

/-- A nonzero section vanishing at a point `η` of codimension one has positive order at `η`. -/
private theorem one_le_ord_of_notMem_basicOpen {V : X.Opens} [Nonempty V] (s : Γ(X, V)) {η : X}
    (hηV : η ∈ V) (hη : Order.coheight η = 1) (hs : η ∉ X.basicOpen s) (hs0 : s ≠ 0) :
    1 ≤ X.ord (X.germToFunctionField V s) η := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  have hg0 : X.presheaf.germ V η hηV s ≠ 0 := fun h =>
    hs0 (germ_injective_of_isIntegral X η hηV (by rw [h, map_zero]))
  have hf : X.germToFunctionField V s ≠ 0 := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hηV]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg0
  rw [Scheme.le_ord_iff hη hf, ← Scheme.algebraMap_germ_eq_germToFunctionField _ hηV]
  exact ofAdd_one_le_ordFrac hg0 (by rwa [Scheme.mem_basicOpen X s η hηV] at hs)

/-- A section has nonnegative order at every point of its domain. -/
private theorem ord_germToFunctionField_nonneg' {V : X.Opens} [Nonempty V] (s : Γ(X, V))
    (hs0 : s ≠ 0) {η : X} (hηV : η ∈ V) : 0 ≤ X.ord (X.germToFunctionField V s) η := by
  have h := Scheme.ord_le_smul hηV hs0 (1 : X.functionField)
  rwa [ord_one', Algebra.smul_def, mul_one] at h

/-- On an integral normal scheme every prime divisor `E` has a uniformizer: a rational function
`t` with `ord_E t = 1`. -/
private theorem exists_ord_genericPoint_eq_one' (E : MMP.Mori.PrimeDivisor X) :
    ∃ t : X.functionField, t ≠ 0 ∧ X.ord t E.genericPoint = 1 := by
  have := E.isDiscreteValuationRing_localRing
  have h1 := E.coheight_genericPoint
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le h1.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hne : algebraMap E.localRing X.functionField ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  refine ⟨algebraMap E.localRing X.functionField ϖ, hne, ?_⟩
  rw [Scheme.ord_eq_iff h1 hne]
  exact Ring.ordFrac_irreducible hϖ

/-- The generic point of a prime divisor is not the generic point of `X`. -/
private theorem genericPoint_ne_genericPoint (Γ : MMP.Mori.PrimeDivisor X) :
    Γ.genericPoint ≠ genericPoint X := fun h => by
  have h1 := Γ.coheight_genericPoint
  rw [h, show genericPoint X = (⊤ : X) from rfl, Order.coheight_top] at h1
  exact zero_ne_one h1

private theorem exists_section_vanishing [IsAffine X] (hdim : topologicalKrullDim X = 1)
    {Γ Q : MMP.Mori.PrimeDivisor X} (hne : Γ ≠ Q) :
    ∃ t : Γ(X, ⊤), t ≠ 0 ∧ 1 ≤ X.ord (X.germToFunctionField ⊤ t) Γ.genericPoint ∧
      X.ord (X.germToFunctionField ⊤ t) Q.genericPoint = 0 := by
  have hcl : IsClosed ({Γ.genericPoint} : Set X) :=
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X hdim
      (genericPoint_ne_genericPoint Γ)
  let V : X.Opens := ⟨({Γ.genericPoint} : Set X)ᶜ, hcl.isOpen_compl⟩
  have hQV : Q.genericPoint ∈ V := fun h =>
    hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (Set.mem_singleton_iff.mp h).symm)
  obtain ⟨t, htV, hQt⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨Q.genericPoint, hQV⟩ trivial
  have hΓt : Γ.genericPoint ∉ X.basicOpen t := fun h => htV h rfl
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hQt
    exact hQt
  refine ⟨t, ht0, one_le_ord_of_notMem_basicOpen t trivial Γ.coheight_genericPoint hΓt ht0, ?_⟩
  have hu : IsUnit (X.presheaf.germ ⊤ Q.genericPoint trivial t) :=
    (Scheme.mem_basicOpen X t Q.genericPoint trivial).mp hQt
  have hQ' : Q.genericPoint ∈ (⊤ : X.Opens) := trivial
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hQ']
  exact Q.ord_algebraMap_of_isUnit hu

private theorem exists_regular_high_order [IsAffine X] (hdim : topologicalKrullDim X = 1)
    (Q : MMP.Mori.PrimeDivisor X) (S : Finset (MMP.Mori.PrimeDivisor X)) (hQ : Q ∉ S) (N : ℕ) :
    ∃ s : X.functionField, s ≠ 0 ∧ (∀ Γ : MMP.Mori.PrimeDivisor X, 0 ≤ X.ord s Γ.genericPoint) ∧
      X.ord s Q.genericPoint = 0 ∧ ∀ Γ ∈ S, (N : ℤ) ≤ X.ord s Γ.genericPoint := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1, one_ne_zero, fun Γ => by simp [ord_one'], ord_one' _, by simp⟩
  | insert Γ₀ S hΓ₀ ih =>
    obtain ⟨s, hs0, hs, hsQ, hsS⟩ := ih (fun h => hQ (Finset.mem_insert_of_mem h))
    have hΓ₀Q : Γ₀ ≠ Q := fun h => hQ (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨t, ht0, ht1, htQ⟩ := exists_section_vanishing hdim hΓ₀Q
    have : Nonempty (⊤ : X.Opens) := ⟨⟨Q.genericPoint, trivial⟩⟩
    set τ := X.germToFunctionField ⊤ t with hτ
    have hτ0 : τ ≠ 0 := fun h => ht0 (X.germToFunctionField_injective ⊤ (a₁ := t) (a₂ := 0)
      (by simpa using h))
    have hτnn : ∀ Γ : MMP.Mori.PrimeDivisor X, 0 ≤ X.ord τ Γ.genericPoint := fun Γ =>
      ord_germToFunctionField_nonneg' t ht0 (trivial : Γ.genericPoint ∈ (⊤ : X.Opens))
    refine ⟨s * τ ^ N, mul_ne_zero hs0 (pow_ne_zero _ hτ0), fun Γ => ?_, ?_, ?_⟩
    · rw [Scheme.ord_mul hs0 (pow_ne_zero _ hτ0), ord_pow' hτ0]
      have := hs Γ
      have := hτnn Γ
      positivity
    · rw [Scheme.ord_mul hs0 (pow_ne_zero _ hτ0), ord_pow' hτ0, hsQ, htQ]
      simp
    · intro Γ hΓ
      rw [Scheme.ord_mul hs0 (pow_ne_zero _ hτ0), ord_pow' hτ0]
      rcases Finset.mem_insert.mp hΓ with rfl | hΓS
      · have := hs Γ
        nlinarith [ht1, (Nat.cast_nonneg N : (0 : ℤ) ≤ N)]
      · have := hsS Γ hΓS
        have := hτnn Γ
        nlinarith [(Nat.cast_nonneg N : (0 : ℤ) ≤ N)]

/-- On an affine curve, for every divisor `D` and prime divisor `Q` there is a rational function
`f` with `ord_Γ f ≥ -D_Γ` for all `Γ` and `ord_Q f = -D_Q`. -/
private theorem exists_function_exact_order [IsAffine X] (hdim : topologicalKrullDim X = 1)
    (D : MMP.Mori.Divisor X) (Q : MMP.Mori.PrimeDivisor X) :
    ∃ f : X.functionField, f ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor X, -D.coeff Γ ≤ X.ord f Γ.genericPoint) ∧
      X.ord f Q.genericPoint = -D.coeff Q := by
  classical
  obtain ⟨π, hπ0, hπ⟩ := exists_ord_genericPoint_eq_one' Q
  set f₀ : X.functionField := π ^ (-D.coeff Q)
  have hf₀0 : f₀ ≠ 0 := zpow_ne_zero _ hπ0
  have hf₀ord : ∀ x, X.ord f₀ x = (-D.coeff Q) * X.ord π x := fun x => MMP.Mori.ord_zpow x hπ0 _
  have hfin : {Γ : MMP.Mori.PrimeDivisor X | X.ord f₀ Γ.genericPoint ≠ 0}.Finite := by
    have h1 := (Stacks.Chow.locallyFiniteSupport_ord X f₀).finite_inter_support_of_isCompact
      (isCompact_univ : IsCompact (Set.univ : Set X))
    refine (h1.preimage (f := fun Γ : MMP.Mori.PrimeDivisor X => Γ.genericPoint)
      (fun a _ b _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)).subset
      fun Γ hΓ => ⟨trivial, hΓ⟩
  have hBfin :
      {Γ : MMP.Mori.PrimeDivisor X | Γ ≠ Q ∧ X.ord f₀ Γ.genericPoint < -D.coeff Γ}.Finite := by
    refine (hfin.union (D.support.finite_toSet)).subset ?_
    rintro Γ ⟨-, hΓ⟩
    by_cases h0 : D.coeff Γ = 0
    · left
      simp only [h0, neg_zero] at hΓ
      exact hΓ.ne
    · right
      simpa [DivisorWithCoeffs.coeff_apply] using h0
  set B := hBfin.toFinset with hB
  have hQB : Q ∉ B := by simp [hB]
  set N : ℕ := B.sup (fun Γ => (-D.coeff Γ - X.ord f₀ Γ.genericPoint).toNat)
  obtain ⟨s, hs0, hs, hsQ, hsB⟩ := exists_regular_high_order hdim Q B hQB N
  have hQ0 : X.ord f₀ Q.genericPoint = -D.coeff Q := by rw [hf₀ord, hπ, mul_one]
  have hford : ∀ x, X.ord (s * f₀) x = X.ord s x + X.ord f₀ x := fun x => Scheme.ord_mul hs0 hf₀0
  refine ⟨s * f₀, mul_ne_zero hs0 hf₀0, fun Γ => ?_, by rw [hford, hsQ, hQ0, zero_add]⟩
  rw [hford]
  by_cases hΓQ : Γ = Q
  · subst hΓQ
    rw [hsQ, hQ0]
    simp
  by_cases hΓB : Γ ∈ B
  · have h1 := hsB Γ hΓB
    have h2 : (-D.coeff Γ - X.ord f₀ Γ.genericPoint).toNat ≤ N :=
      Finset.le_sup (f := fun Γ => (-D.coeff Γ - X.ord f₀ Γ.genericPoint).toNat) hΓB
    have h3 : -D.coeff Γ - X.ord f₀ Γ.genericPoint ≤ N := by
      have := Int.self_le_toNat (-D.coeff Γ - X.ord f₀ Γ.genericPoint)
      omega
    omega
  · have : ¬ (Γ ≠ Q ∧ X.ord f₀ Γ.genericPoint < -D.coeff Γ) := fun h =>
      hΓB (by simpa [hB] using h)
    have h4 : -D.coeff Γ ≤ X.ord f₀ Γ.genericPoint := by
      by_contra hlt
      exact this ⟨hΓQ, not_le.mp hlt⟩
    have := hs Γ
    omega

end Order

section Machinery

/-- A rational form `τ` *vanishes to order `≥ a` along `Q`*: it is `0` or `ord_Q τ ≥ a`. -/
def VanishesTo {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] {n : ℕ} (Q : MMP.Mori.PrimeDivisor C) (a : ℤ)
    (τ : RationalPluriForms sC 1 (n : ℕ)) : Prop :=
  τ = 0 ∨ a ≤ Q.ordForm τ

section VanishesTo

variable {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C]
  [IsLocallyNoetherian C] {n : ℕ} {Q : MMP.Mori.PrimeDivisor C} {a : ℤ}

/-- Vanishing to order `≥ a` is preserved by sums. -/
theorem VanishesTo.add [IsNormal C] {τ τ' : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (h' : VanishesTo Q a τ') : VanishesTo Q a (τ + τ') := by
  rcases h with h | h
  · rwa [h, zero_add]
  rcases h' with h' | h'
  · rw [h', add_zero]
    exact Or.inr h
  by_cases h0 : τ + τ' = 0
  · exact Or.inl h0
  exact Or.inr ((le_min h h').trans (Q.min_ordForm_le_ordForm_add h0))

/-- Vanishing to order `≥ a` is preserved by negation. -/
theorem VanishesTo.neg {τ : RationalPluriForms sC 1 (n : ℕ)} (h : VanishesTo Q a τ) :
    VanishesTo Q a (-τ) := by
  rcases h with h | h
  · exact Or.inl (by rw [h, neg_zero])
  · exact Or.inr (by rwa [PrimeDivisor.ordForm_neg])

/-- Vanishing to order `≥ a` is preserved by differences. -/
theorem VanishesTo.sub [IsNormal C] {τ τ' : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (h' : VanishesTo Q a τ') : VanishesTo Q a (τ - τ') := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

/-- Vanishing to order `≥ a` is preserved by multiplication by a constant. -/
theorem VanishesTo.const_smul {τ : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (c : k) : VanishesTo Q a (c • τ) := by
  by_cases hc : c = 0
  · exact Or.inl (by rw [hc, zero_smul])
  rcases h with h | h
  · exact Or.inl (by rw [h, smul_zero])
  · exact Or.inr (by rwa [MMP.Fourfold.ordForm_const_smul Q hc])

/-- Vanishing to order `≥ a` implies vanishing to every order `b ≤ a`. -/
theorem VanishesTo.mono {b : ℤ} {τ : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (hb : b ≤ a) : VanishesTo Q b τ :=
  h.imp id hb.trans

end VanishesTo

/-- Membership in the global sections `H⁰(C, 𝒪(nK + E))` is the order condition at every prime
divisor. -/
theorem mem_pluricanonicalSections_top_iff {k : Type u} [Field k] {C : Scheme.{u}}
    {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {n : ℕ}
    {E : Divisor C} {τ : RationalPluriForms sC 1 (n : ℕ)} :
    τ ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤ ↔
      ∀ Q : MMP.Mori.PrimeDivisor C, VanishesTo Q (-E.coeff Q) τ := by
  have htop : (⊤ : C.Opens) ≠ ⊥ := by
    intro h
    have hx : (Nonempty.some (inferInstance : Nonempty C)) ∈ (⊤ : C.Opens) := trivial
    rw [h] at hx
    exact hx
  rw [mem_pluricanonicalSections_of_ne_bot htop]
  refine ⟨fun h Q => ?_, fun h Q _ hτ => ?_⟩
  · by_cases hτ : τ = 0
    · exact Or.inl hτ
    · refine Or.inr ?_
      have := h Q ⟨Q.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl, trivial⟩ hτ
      omega
  · rcases h Q with h | h
    · exact (hτ h).elim
    · omega

/-- **The `n`-th power of a canonical form.** On a curve with canonical divisor `K` there is a
nonzero rational `n`-canonical form `θ` with `ord_Γ θ = n · coeff_Γ K` along every prime
divisor `Γ`. -/
theorem exists_ordForm_eq_mul_coeff {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    (Q : MMP.Mori.PrimeDivisor C) (n : ℕ) :
    ∃ θ : RationalPluriForms sC 1 (n : ℕ), θ ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor C, Γ.ordForm θ = n * K.coeff Γ := by
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim C = 1 := hK.1
  let := stalkAlgebra sC Q.genericPoint
  let := functionFieldAlgebra sC
  have := isScalarTower_stalk_functionField sC Q.genericPoint
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hC hK
  obtain ⟨σ, hσ, h0⟩ := Q.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sC) (d := 1)
    (by rw [hdim]; rfl)
  have htr : (Algebra.trdeg k C.functionField).toNat = 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sC) (by rw [hdim]; rfl)
  set b := topFormsBasis Q.localRing hσ h0
  set g : C.functionField := (ZTensorPower.basis b 1).repr ω ()
  have hg : g ≠ 0 := by
    intro h
    have := basis_unit_repr_smul (ZTensorPower.basis b 1) ω
    rw [show (ZTensorPower.basis b 1).repr ω () = g from rfl, h, zero_smul] at this
    exact hω0 this.symm
  have hθ0 := smul_ne_zero (pow_ne_zero n hg) ((ZTensorPower.basis b n).ne_zero ())
  refine ⟨g ^ n • ZTensorPower.basis b n (), hθ0, fun Γ => ?_⟩
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul htr b
  have h1 := hN 1 ω hω0
  have h2 := hN n (g ^ n • ZTensorPower.basis b n ()) hθ0
  rw [hω] at h1
  rw [h2]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_apply,
    if_true]
  rw [ord_pow' hg]
  change K.coeff Γ = C.ord g Γ.genericPoint + 1 * N at h1
  rw [h1]
  ring

/-- On a curve, the rational `m`-canonical forms are a line over `k(C)`: every form is a multiple
of a given nonzero one. -/
theorem exists_eq_smul_of_ne_zero {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [LocallyOfFiniteType sC] (hdim : topologicalKrullDim C = 1) {m : ℤ}
    (Q : MMP.Mori.PrimeDivisor C) {u : RationalPluriForms sC 1 m} (hu : u ≠ 0)
    (w : RationalPluriForms sC 1 m) : ∃ h : C.functionField, w = h • u := by
  let := stalkAlgebra sC Q.genericPoint
  let := functionFieldAlgebra sC
  have := isScalarTower_stalk_functionField sC Q.genericPoint
  obtain ⟨σ, hσ, h0⟩ := Q.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sC) (d := 1)
    (by rw [hdim]; rfl)
  let B := ZTensorPower.basis (topFormsBasis Q.localRing hσ h0) m
  have hu' := basis_unit_repr_smul B u
  have hw' := basis_unit_repr_smul B w
  have hru : B.repr u () ≠ 0 := by
    intro h
    rw [h, zero_smul] at hu'
    exact hu hu'.symm
  refine ⟨B.repr w () / B.repr u (), ?_⟩
  have key : (B.repr w () / B.repr u ()) • (B.repr u () • B ()) = B.repr w () • B () := by
    rw [smul_smul, div_mul_cancel₀ _ hru]
  rw [hu'] at key
  exact hw'.symm.trans key.symm

/-- An element of the maximal ideal of `𝒪_{X,Γ}` vanishes along `Γ`. -/
theorem one_le_ord_algebraMap_of_mem_maximalIdeal {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (Γ : MMP.Mori.PrimeDivisor X) {a : Γ.localRing}
    (ha : a ∈ IsLocalRing.maximalIdeal Γ.localRing) (ha0 : a ≠ 0) :
    1 ≤ X.ord (algebraMap Γ.localRing X.functionField a) Γ.genericPoint := by
  have := Γ.isDiscreteValuationRing_localRing
  have hz := Γ.coheight_genericPoint
  have hne : algebraMap Γ.localRing X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha0
  rw [Scheme.le_ord_iff hz hne]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Γ.genericPoint) := krullDimLE_of_coheight_le hz.le
  exact ofAdd_one_le_ordFrac ha0 ((IsLocalRing.mem_maximalIdeal _).1 ha)

/-- **The fibre of `𝒪(nK + E)` at a point is spanned by a section of exact order.** If `u` has
exact order `-e` along `Q` and `w` has order `≥ -e`, then `w - c • u` has order `≥ 1 - e` for some
constant `c`. -/
theorem exists_vanishesTo_sub_const_smul
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1) {n : ℕ}
    (Q : MMP.Mori.PrimeDivisor C) (e : ℤ) {u w : RationalPluriForms sC 1 (n : ℕ)} (hu : u ≠ 0)
    (hue : Q.ordForm u + e = 0) (hw : VanishesTo Q (-e) w) :
    ∃ c : k, VanishesTo Q (1 - e) (w - c • u) := by
  classical
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  let := stalkAlgebra sC Q.genericPoint
  let := functionFieldAlgebra sC
  have := isScalarTower_stalk_functionField sC Q.genericPoint
  rcases hw with hw0 | hw
  · exact ⟨0, Or.inl (by rw [hw0, zero_smul, sub_zero])⟩
  obtain ⟨h, rfl⟩ := exists_eq_smul_of_ne_zero hdim Q hu w
  by_cases hh : h = 0
  · exact ⟨0, Or.inl (by rw [hh, zero_smul, zero_smul, sub_zero])⟩
  have hd : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  rw [Q.ordForm_smul_of_topologicalKrullDim_eq hd hh hu] at hw
  obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    Q.genericPoint hh fun Γ hΓ => by
      have hΓQ : Γ = Q := MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
        exact specializes_iff_mem_closure.2 hΓ)
      subst hΓQ
      omega
  have hcl : IsClosed ({Q.genericPoint} : Set C) :=
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hdim
      (genericPoint_ne_genericPoint Q)
  obtain ⟨c, hc⟩ := MMP.Mori.SurfaceAux.residue_surjective sC Q.genericPoint hcl
    (Ideal.Quotient.mk _ r)
  have hmem : r - algebraMap k Q.localRing c ∈ IsLocalRing.maximalIdeal Q.localRing := by
    rw [← Ideal.Quotient.eq, ← hc]
    rfl
  refine ⟨c, ?_⟩
  have hsmul : h • u - c • u = algebraMap Q.localRing C.functionField
      (r - algebraMap k Q.localRing c) • u := by
    rw [MMP.Fourfold.RationalPluriForms.smul_def, ← sub_smul, map_sub, hr,
      ← IsScalarTower.algebraMap_apply]
  rw [hsmul]
  by_cases h0 : r - algebraMap k Q.localRing c = 0
  · exact Or.inl (by rw [h0, map_zero, zero_smul])
  have h0' : algebraMap Q.localRing C.functionField (r - algebraMap k Q.localRing c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 h0
  refine Or.inr ?_
  rw [Q.ordForm_smul_of_topologicalKrullDim_eq hd h0' hu]
  have := one_le_ord_algebraMap_of_mem_maximalIdeal Q hmem h0
  omega

end Machinery

section Good

/-- **Prescribing the fibres at a finite set of points** (the induction of FA 12.2.11,
case (12.2.11.4)). If for every `T ⊆ S` with `|T| < |S|` and every `Q₀ ∉ T` there is a section of
`𝒪(nK + E - T)` of exact order at `Q₀`, then global sections of `𝒪(nK + E)` surject onto the
fibres at the points of `S`: the points are added one at a time. -/
private theorem exists_mem_pluricanonicalSections_sub_vanishes_of_hex
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1) (n : ℕ) (E : Divisor C)
    (S : Finset (MMP.Mori.PrimeDivisor C))
    (hex : ∀ (T : Finset (MMP.Mori.PrimeDivisor C)) (Q₀ : MMP.Mori.PrimeDivisor C), Q₀ ∉ T →
      T.card + 1 ≤ S.card →
      ∃ u ∈ pluricanonicalSections sC 1 (n : ℕ) (E - ∑ Q ∈ T, Finsupp.single Q 1) ⊤, u ≠ 0 ∧
        Q₀.ordForm u + (E - ∑ Q ∈ T, Finsupp.single Q 1).coeff Q₀ = 0)
    (τ : MMP.Mori.PrimeDivisor C → RationalPluriForms sC 1 (n : ℕ))
    (hτ : ∀ Q ∈ S, τ Q = 0 ∨ 0 ≤ Q.ordForm (τ Q) + E.coeff Q) :
    ∃ s ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤,
      ∀ Q ∈ S, s - τ Q = 0 ∨ 1 ≤ Q.ordForm (s - τ Q) + E.coeff Q := by
  classical
  suffices H : ∀ T ⊆ S, ∃ s ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤,
      ∀ Q ∈ T, VanishesTo Q (1 - E.coeff Q) (s - τ Q) by
    obtain ⟨s, hs, hsT⟩ := H S subset_rfl
    exact ⟨s, hs, fun Q hQ => (hsT Q hQ).imp id fun h => by omega⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun _ => ⟨0, zero_mem _, fun Q hQ => absurd hQ (Finset.notMem_empty Q)⟩
  | @insert Q₀ T hQ₀ ih =>
    intro hTS
    obtain ⟨s, hs, hsT⟩ := ih ((Finset.subset_insert _ _).trans hTS)
    set E' : Divisor C := E - ∑ Q ∈ T, Finsupp.single Q 1 with hE'
    have hcoeff' : ∀ Q, E'.coeff Q = E.coeff Q - if Q ∈ T then 1 else 0 := fun Q => by
      simp only [hE', DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, Finsupp.finset_sum_apply,
        Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hcard : T.card + 1 ≤ S.card := by
      have := Finset.card_le_card hTS
      rwa [Finset.card_insert_of_notMem hQ₀] at this
    obtain ⟨u, hu, hu0, hue⟩ := hex T Q₀ hQ₀ hcard
    have hE'Q₀ : E'.coeff Q₀ = E.coeff Q₀ := by rw [hcoeff', if_neg hQ₀, sub_zero]
    rw [hE'Q₀] at hue
    have hw : VanishesTo Q₀ (-E.coeff Q₀) (τ Q₀ - s) := by
      refine VanishesTo.sub ?_ (mem_pluricanonicalSections_top_iff.1 hs Q₀)
      exact (hτ Q₀ (hTS (Finset.mem_insert_self _ _))).imp id fun h => by omega
    obtain ⟨c, hc⟩ := exists_vanishesTo_sub_const_smul hC hdim Q₀ (E.coeff Q₀) hu0 hue hw
    have hu' := mem_pluricanonicalSections_top_iff.1 hu
    refine ⟨s + c • u, ?_, fun Q hQ => ?_⟩
    · refine mem_pluricanonicalSections_top_iff.2 fun Q =>
        ((mem_pluricanonicalSections_top_iff.1 hs Q).add ?_)
      refine ((hu' Q).const_smul c).mono ?_
      rw [hcoeff']
      split_ifs <;> omega
    · rcases Finset.mem_insert.1 hQ with rfl | hQT
      · rw [show s + c • u - τ Q = -(τ Q - s - c • u) by abel]
        exact hc.neg
      · rw [show s + c • u - τ Q = (s - τ Q) + c • u by abel]
        refine (hsT Q hQT).add (((hu' Q).const_smul c).mono ?_)
        rw [hcoeff', if_pos hQT]
        omega

end Good

section GoodSec

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The sections of `𝒪(nK + G)` that are congruent to `(dz_P/z_P)^n` modulo `𝔪_P 𝒪(nK + G)_P` at
the points `P` of `⌊Δ⌋` (for the fixed uniformizers `z_P`). -/
private def GoodSec (Δ : QDivisor X) (n : ℕ) (G : Divisor X)
    (z : MMP.Mori.PrimeDivisor X → X.functionField) (s : RationalPluriForms sX 1 n) : Prop :=
  s ∈ pluricanonicalSections sX 1 n G ⊤ ∧
    ∀ P : MMP.Mori.PrimeDivisor X, 1 ≤ Δ.coeff P →
      VanishesTo P (1 - G.coeff P) (s - dlogPow sX (z P) n)

/-- `(dz/z)^n` for a uniformizer `z` at `P` is nonzero of order `-n` at `P`. -/
theorem dlogPow_ne_zero_and_ordForm_eq (hC : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) (P : MMP.Mori.PrimeDivisor X) {z : X.functionField}
    (hz : X.ord z P.genericPoint = 1) (n : ℕ) :
    dlogPow sX z n ≠ 0 ∧ P.ordForm (dlogPow sX z n) = -(n : ℤ) := by
  obtain ⟨hd0, hdord⟩ := ordForm_dlogPow_one_of_ord_eq_one hC hdim P z hz
  obtain ⟨hdn0, hdn⟩ := ordForm_dlogPow_eq_mul hC hdim z hd0 n
  exact ⟨hdn0, by rw [hdn P, hdord]; ring⟩

/-- A good section is nonzero of exact order `-n` at the points of `⌊Δ⌋`. -/
private theorem GoodSec.nonvanishing {Δ : QDivisor X} {n : ℕ} {G : Divisor X}
    {z : MMP.Mori.PrimeDivisor X → X.functionField} {s : RationalPluriForms sX 1 n}
    (hC : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 1) (hs : GoodSec Δ n G z s)
    (P : MMP.Mori.PrimeDivisor X) (hP : 1 ≤ Δ.coeff P)
    (hz : X.ord (z P) P.genericPoint = 1) (hGP : G.coeff P = n) :
    s ≠ 0 ∧ P.ordForm s + G.coeff P = 0 := by
  obtain ⟨hmem, hvan⟩ := hs
  obtain ⟨hdn0, hdnP⟩ := dlogPow_ne_zero_and_ordForm_eq hC hdim P hz n
  have hv := hvan P hP
  have hm := mem_pluricanonicalSections_top_iff.1 hmem P
  by_cases hs0 : s = 0
  · exfalso
    subst hs0
    rcases hv with h | h
    · exact hdn0 (by simpa using h.symm)
    · rw [zero_sub, PrimeDivisor.ordForm_neg, hdnP] at h
      omega
  refine ⟨hs0, ?_⟩
  have h := hm.resolve_left hs0
  by_contra hne
  have h1 : 1 ≤ P.ordForm s + G.coeff P := by omega
  have hdl : VanishesTo P (1 - G.coeff P) (dlogPow sX (z P) n) := by
    rw [show dlogPow sX (z P) n = s - (s - dlogPow sX (z P) n) by abel]
    exact VanishesTo.sub (Or.inr (by omega)) hv
  rcases hdl with h | h
  · exact hdn0 h
  · rw [hdnP] at h
    omega

/-- A good section is a normalized section (when the elliptic clause is vacuous). -/
private theorem GoodSec.isNormalizedSection (ε : EllipticNormalizationDatum k)
    {Δ : QDivisor X} {n : ℕ} {G : Divisor X}
    {z : MMP.Mori.PrimeDivisor X → X.functionField} {s : RationalPluriForms sX 1 n}
    (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 1)
    (hΔ : Δ.IsEffective) (hn : 0 < n) (hG : Divisor.toQDivisor G = (n : ℤ) • Δ)
    (hz : ∀ P, X.ord (z P) P.genericPoint = 1) (hs : GoodSec Δ n G z s)
    (hell : ¬ (IsProper sX ∧ (∃ K : Divisor X, K.IsCanonicalDivisor sX 1 ∧ K.h0 k sX = 1) ∧
      Δ = 0 ∧ 12 ∣ n)) :
    IsNormalizedSection ε sX Δ n G s where
  isNormalVariety := hC
  isSmoothScheme := hsm
  dim_eq := hdim
  isEffective := hΔ
  pos := hn
  toQDivisor_eq := hG
  mem := hs.1
  elliptic := fun hp hg hΔ0 h12 => absurd ⟨hp, hg, hΔ0, h12⟩ hell
  vanishes := fun _ P hP => ⟨z P, hz P, (hs.2 P hP).imp id fun h => by omega⟩

end GoodSec

section GenPos

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- Nonvanishing at `P`: `s ≠ 0` and `ord_P(s) + e = 0`. -/
private def NonVan {n : ℕ} (P : MMP.Mori.PrimeDivisor X) (e : ℤ)
    (s : RationalPluriForms sX 1 n) : Prop :=
  s ≠ 0 ∧ P.ordForm s + e = 0

private theorem nonVan_iff {n : ℕ} {P : MMP.Mori.PrimeDivisor X} {e : ℤ}
    {s : RationalPluriForms sX 1 n} (hs : VanishesTo P (-e) s) :
    NonVan P e s ↔ ¬ VanishesTo P (1 - e) s := by
  unfold NonVan VanishesTo at *
  constructor
  · rintro ⟨h0, h1⟩ (h | h)
    · exact h0 h
    · omega
  · intro h
    push Not at h
    obtain ⟨h0, h1⟩ := h
    rcases hs with h | h
    · exact absurd h h0
    · exact ⟨h0, by omega⟩

/-- If two combinations `s + λ(t - s)` and `s + λ'(t - s)` with `λ ≠ λ'` vanish to order `≥ a`
along `P`, so does `t - s`. -/
private theorem vanishes_of_two {n : ℕ} {P : MMP.Mori.PrimeDivisor X} {a : ℤ}
    {s t : RationalPluriForms sX 1 n} {l l' : k} (hll : l ≠ l')
    (h1 : VanishesTo P a (s + l • (t - s))) (h2 : VanishesTo P a (s + l' • (t - s))) :
    VanishesTo P a (t - s) := by
  have h3 : VanishesTo P a ((l - l') • (t - s)) := by
    rw [show (l - l') • (t - s) = (s + l • (t - s)) - (s + l' • (t - s)) by
      rw [sub_smul]
      abel]
    exact h1.sub h2
  have h4 := h3.const_smul (l - l')⁻¹
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hll), one_smul] at h4

/-- **General position** (proof of FA 8.7, the "general point of the affine span"): if for each
`P ∈ R` there is a good section nonvanishing at `P`, there is a good section nonvanishing at all
the points of `R`. The `k`-affine combinations `s + λ(t - s)` of good sections are good, and each
point excludes at most one `λ`. -/
private theorem exists_goodSec_nonVan {Δ : QDivisor X} {n : ℕ} {G : Divisor X}
    {z : MMP.Mori.PrimeDivisor X → X.functionField}
    (h0 : ∃ s₀ : RationalPluriForms sX 1 n, GoodSec Δ n G z s₀)
    (R : Finset (MMP.Mori.PrimeDivisor X))
    (ht : ∀ P ∈ R, ∃ t : RationalPluriForms sX 1 n,
      GoodSec Δ n G z t ∧ NonVan P (G.coeff P) t) :
    ∃ s : RationalPluriForms sX 1 n, GoodSec Δ n G z s ∧
      ∀ P ∈ R, NonVan P (G.coeff P) s := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    obtain ⟨s₀, h⟩ := h0
    exact ⟨s₀, h, by simp⟩
  | insert P R hP ih =>
    obtain ⟨s, hs, hsR⟩ := ih (fun Q hQ => ht Q (Finset.mem_insert_of_mem hQ))
    obtain ⟨t, htg, htP⟩ := ht P (Finset.mem_insert_self _ _)
    set u : k → RationalPluriForms sX 1 n := fun l => s + l • (t - s) with hu_def
    have hmem : ∀ (w : RationalPluriForms sX 1 n), w ∈ pluricanonicalSections sX 1 n G ⊤ →
        ∀ Q, VanishesTo Q (-G.coeff Q) w := fun w hw Q => mem_pluricanonicalSections_top_iff.1 hw Q
    have hu : ∀ l, GoodSec Δ n G z (u l) := by
      intro l
      refine ⟨mem_pluricanonicalSections_top_iff.2 fun Q => ?_, fun P' hP' => ?_⟩
      · exact (hmem s hs.1 Q).add (((hmem t htg.1 Q).sub (hmem s hs.1 Q)).const_smul l)
      · have : u l - dlogPow sX (z P') n = (s - dlogPow sX (z P') n) +
            l • ((t - dlogPow sX (z P') n) - (s - dlogPow sX (z P') n)) := by
          rw [sub_sub_sub_cancel_right]
          simp only [hu_def]
          abel
        rw [this]
        exact (hs.2 P' hP').add (((htg.2 P' hP').sub (hs.2 P' hP')).const_smul l)
    have hbad : ∀ Q ∈ insert P R,
        {l : k | ¬ NonVan Q (G.coeff Q) (u l)}.Subsingleton := by
      intro Q hQ l hl l' hl'
      by_contra hne
      have hl1 : VanishesTo Q (1 - G.coeff Q) (u l) :=
        not_not.1 fun h => hl ((nonVan_iff (hmem _ (hu l).1 Q)).2 h)
      have hl2 : VanishesTo Q (1 - G.coeff Q) (u l') :=
        not_not.1 fun h => hl' ((nonVan_iff (hmem _ (hu l').1 Q)).2 h)
      have hts := vanishes_of_two hne hl1 hl2
      rcases Finset.mem_insert.1 hQ with rfl | hQR
      · have : t = u l + (1 - l) • (t - s) := by
          simp only [hu_def]
          rw [sub_smul, one_smul]
          abel
        refine (nonVan_iff (hmem t htg.1 Q)).1 htP ?_
        rw [this]
        exact hl1.add (hts.const_smul _)
      · have : s = u l - l • (t - s) := by
          simp only [hu_def]
          abel
        refine (nonVan_iff (hmem s hs.1 Q)).1 (hsR Q hQR) ?_
        rw [this]
        exact hl1.sub (hts.const_smul _)
    have hfin : {l : k | ∃ Q ∈ insert P R, ¬ NonVan Q (G.coeff Q) (u l)}.Finite := by
      have : {l : k | ∃ Q ∈ insert P R, ¬ NonVan Q (G.coeff Q) (u l)} =
          ⋃ Q ∈ (insert P R : Finset _), {l : k | ¬ NonVan Q (G.coeff Q) (u l)} := by
        ext l
        simp
      rw [this]
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun Q hQ => (hbad Q hQ).finite
    obtain ⟨l, hl⟩ := hfin.infinite_compl.nonempty
    exact ⟨u l, hu l, fun Q hQ => not_not.1 fun h => hl ⟨Q, hQ, h⟩⟩

end GenPos

section Producer

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A rational function with the right orders gives a section of `𝒪(nK + E')` of exact order at
`Q`: multiply it with a `θ` of divisor `nK`. -/
private theorem exists_form_of_function
    (hC : IsNormalVariety k sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) (n : ℕ)
    (E' : Divisor X) (f : X.functionField) (hf0 : f ≠ 0)
    (hf : ∀ Γ : MMP.Mori.PrimeDivisor X, -((n : ℤ) • K + E').coeff Γ ≤ X.ord f Γ.genericPoint)
    (Q : MMP.Mori.PrimeDivisor X)
    (hfQ : X.ord f Q.genericPoint = -((n : ℤ) • K + E').coeff Q) :
    ∃ u ∈ pluricanonicalSections sX 1 (n : ℕ) E' ⊤, u ≠ 0 ∧ Q.ordForm u + E'.coeff Q = 0 := by
  have : LocallyOfFiniteType sX := hC.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by rw [hK.1]
  obtain ⟨θ, hθ0, hθ⟩ := exists_ordForm_eq_mul_coeff hC hK Q n
  have hcoeff : ∀ Γ, ((n : ℤ) • K + E').coeff Γ = n * K.coeff Γ + E'.coeff Γ := fun Γ => by
    simp [DivisorWithCoeffs.coeff_apply]
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X,
      Γ.ordForm (f • θ) = X.ord f Γ.genericPoint + n * K.coeff Γ := fun Γ => by
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hd hf0 hθ0, hθ]
  refine ⟨f • θ, mem_pluricanonicalSections_top_iff.2 fun Γ => Or.inr ?_,
    smul_ne_zero hf0 hθ0, ?_⟩
  · have := hf Γ
    rw [hcoeff] at this
    rw [hord]
    omega
  · rw [hord]
    rw [hcoeff] at hfQ
    omega

private theorem nonVan_of_sub_vanishes {n : ℕ} {P : MMP.Mori.PrimeDivisor X} {e : ℤ}
    {s u : RationalPluriForms sX 1 n} (hs : VanishesTo P (-e) s) (hu : NonVan P e u)
    (hsu : VanishesTo P (1 - e) (s - u)) : NonVan P e s := by
  rw [nonVan_iff hs]
  intro hv
  refine (nonVan_iff (P := P) (e := e) (s := u) (Or.inr (by linarith [hu.2]))).1 hu ?_
  rw [show u = s - (s - u) by abel]
  exact hv.sub hsu

/-- **Existence of good sections nonvanishing at prescribed points.** If every `𝒪(nK + G - T)`
with `|T| ≤ |⌊Δ⌋|` has a section of exact order at any given point outside `T`, there is a good
section nonvanishing at all the points of a finite set `R` disjoint from `⌊Δ⌋`: prescribe the
fibres at `⌊Δ⌋ ∪ {P}` for each `P ∈ R` and take a general combination
(`exists_goodSec_nonVan`). -/
private theorem exists_goodSec_nonVan_of_hex
    (hC : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 1)
    (n : ℕ) {Δ : QDivisor X} {G : Divisor X} (hG : Divisor.toQDivisor G = (n : ℤ) • Δ)
    (z : MMP.Mori.PrimeDivisor X → X.functionField)
    (hz : ∀ P, X.ord (z P) P.genericPoint = 1)
    (F : Finset (MMP.Mori.PrimeDivisor X)) (hF : ∀ P, P ∈ F ↔ 1 ≤ Δ.coeff P)
    (R : Finset (MMP.Mori.PrimeDivisor X)) (hRF : ∀ P ∈ R, P ∉ F)
    (hex : ∀ (T : Finset (MMP.Mori.PrimeDivisor X)) (Q₀ : MMP.Mori.PrimeDivisor X), Q₀ ∉ T →
      T.card ≤ F.card →
      ∃ u ∈ pluricanonicalSections sX 1 (n : ℕ) (G - ∑ Q ∈ T, Finsupp.single Q 1) ⊤, u ≠ 0 ∧
        Q₀.ordForm u + (G - ∑ Q ∈ T, Finsupp.single Q 1).coeff Q₀ = 0) :
    ∃ s : RationalPluriForms sX 1 n, GoodSec Δ n G z s ∧ ∀ P ∈ R, NonVan P (G.coeff P) s := by
  classical
  have hGP : ∀ P ∈ F, (n : ℤ) ≤ G.coeff P := by
    intro P hP
    have h1 := congrArg (fun D => DivisorWithCoeffs.coeff D P) hG
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
    have h2 := (hF P).1 hP
    have : ((n : ℤ) : ℚ) ≤ (G.coeff P : ℚ) := by
      rw [h1]
      push_cast
      nlinarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
    exact_mod_cast this
  have hτF : ∀ P ∈ F, dlogPow sX (z P) n = 0 ∨ 0 ≤ P.ordForm (dlogPow sX (z P) n) + G.coeff P :=
    fun P hP => Or.inr (by
      rw [(dlogPow_ne_zero_and_ordForm_eq hC hdim P (hz P) n).2]
      have := hGP P hP
      omega)
  have hgood : ∀ s : RationalPluriForms sX 1 n, s ∈ pluricanonicalSections sX 1 n G ⊤ →
      (∀ Q ∈ F, s - dlogPow sX (z Q) n = 0 ∨ 1 ≤ Q.ordForm (s - dlogPow sX (z Q) n) + G.coeff Q) →
      GoodSec Δ n G z s := fun s hs h =>
    ⟨hs, fun P hP => (h P ((hF P).2 hP)).imp id fun h' => by omega⟩
  have h0 : ∃ s₀ : RationalPluriForms sX 1 n, GoodSec Δ n G z s₀ := by
    obtain ⟨s, hs, hsF⟩ := exists_mem_pluricanonicalSections_sub_vanishes_of_hex hC hdim n G F
      (fun T Q₀ hQ₀ hT => hex T Q₀ hQ₀ (by omega)) (fun Q => dlogPow sX (z Q) n) hτF
    exact ⟨s, hgood s hs hsF⟩
  refine exists_goodSec_nonVan h0 R fun P hP => ?_
  have hPF := hRF P hP
  obtain ⟨uP, huP, huP0, huPe⟩ := hex ∅ P (Finset.notMem_empty _) (Nat.zero_le _)
  simp only [Finset.sum_empty, sub_zero] at huP huPe
  obtain ⟨s, hs, hsS⟩ := exists_mem_pluricanonicalSections_sub_vanishes_of_hex hC hdim n G
    (insert P F) (fun T Q₀ hQ₀ hT => hex T Q₀ hQ₀ (by
      rw [Finset.card_insert_of_notMem hPF] at hT
      omega))
    (fun Q => if Q = P then uP else dlogPow sX (z Q) n) (by
      intro Q hQ
      rcases Finset.mem_insert.1 hQ with rfl | hQF
      · simp only [if_true]
        exact Or.inr (by omega)
      · by_cases hQP : Q = P
        · exact (hPF (hQP ▸ hQF)).elim
        · simp only [hQP, if_false]
          exact hτF Q hQF)
  have hgs : GoodSec Δ n G z s := by
    refine hgood s hs fun Q hQ => ?_
    have hQP : Q ≠ P := fun h => hPF (h ▸ hQ)
    simpa [hQP] using hsS Q (Finset.mem_insert_of_mem hQ)
  refine ⟨s, hgs, ?_⟩
  have h2 := hsS P (Finset.mem_insert_self _ _)
  simp only [if_true] at h2
  refine nonVan_of_sub_vanishes (mem_pluricanonicalSections_top_iff.1 hs P) ⟨huP0, huPe⟩ ?_
  exact h2.imp id fun h => by omega

end Producer

section RR

/-- Global sections of `M` and of its restriction to the open `U = ⊤` have the same dimension. -/
private theorem finrank_globalSectionsOver_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : X.Modules) {U : X.Opens} (hU : U = ⊤) :
    Module.finrank k ((globalSectionsOver (U.ι ≫ f)).obj (M.restrict U.ι)) =
      Module.finrank k ((globalSectionsOver f).obj M) := by
  have heq : U.ι ''ᵁ ⊤ = ⊤ := by subst hU; ext; simp
  let g : ((globalSectionsOver f).obj M) →ₗ[k]
      ((globalSectionsOver (U.ι ≫ f)).obj (M.restrict U.ι)) :=
    { toFun := fun s => (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom s
      map_add' := fun s t => map_add _ s t
      map_smul' := fun a (s : Γ(M, ⊤)) => by
        change (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom
            ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a) • s) =
          ((U.ι.appIso ⊤).inv (((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop).hom a)) •
            ((M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom s)
        refine (M.val.map_smul (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op _ s).trans ?_
        congr 1
        have h := Scheme.Hom.app_appIso_inv U.ι ⊤
        exact (congrArg (fun φ => φ.hom ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a)))
          h).symm }
  have hbij : Function.Bijective g := by
    have : IsIso (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op) := by
      have : (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤) = eqToHom heq := Subsingleton.elim _ _
      rw [this, eqToHom_op, eqToHom_map]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso
      (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op)
  exact (LinearEquiv.ofBijective g hbij).finrank_eq.symm

/-- **Riemann–Roch in large degree for `𝒪_C(D)`.** On a smooth proper curve over `k = k̄` with
canonical divisor `K`, `h⁰(D) = deg D + 1 - g` once `deg D > deg K = 2g - 2`, where
`g = h⁰(K)`. -/
private theorem h0_eq_sum_coeff_add_one_sub_h0_canonical
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) (D : Divisor C)
    (hdeg : (K.sum fun _ a => a) < D.sum fun _ a => a) :
    (D.h0 k sC : ℤ) = (D.sum fun _ a => a) + 1 - K.h0 k sC := by
  obtain ⟨hcurve, hsmooth, hprop, hiso⟩ := curve_instances hC hsm hp hK.1 hsm
  set pY := (smoothLocus sC).ι ≫ sC
  have hdim : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1 := by
    have : IsIso (smoothLocus sC).ι := by rw [hsm, ← Scheme.topIso_hom]; infer_instance
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (smoothLocus sC).ι)).isHomeomorph, hK.1]
    exact le_rfl
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have := (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D).isInvertibleModule_divisorialSheaf
  have h1 := degreeOn_smoothLocus_eq_sum hC hsm hp hK.1 hdim D
  have hK0 := sum_coeff_canonical_eq hC hsm hp hK
  have hg := h0_canonical_eq_genus hC hsm hp hK
  have hKz : ((K.sum fun _ a => a : ℤ) : ℚ) = K.sum fun _ a => (a : ℚ) := by simp [Finsupp.sum]
  have hKint : (K.sum fun _ a => a : ℤ) = 2 * (K.h0 k sC : ℤ) - 2 := by
    have : ((K.sum fun _ a => a : ℤ) : ℚ) = 2 * (K.h0 k sC : ℚ) - 2 := hKz.trans hK0
    exact_mod_cast this
  change invertibleCurveDegree k pY hdim
    ((Scheme.Modules.pullback (smoothLocus sC).ι).obj D.divisorialSheaf) = _ at h1
  let e := (Scheme.Modules.restrictFunctorIsoPullback (smoothLocus sC).ι).app D.divisorialSheaf
  set M := (Scheme.Modules.pullback (smoothLocus sC).ι).obj D.divisorialSheaf
  have hM : SheafOfModules.IsInvertible (smoothLocus sC).toScheme.sheaf.obj
      (smoothLocus sC).toScheme.ringCatSheaf.property M :=
    (inferInstance : SheafOfModules.IsInvertible (smoothLocus sC).toScheme.presheaf
      (smoothLocus sC).toScheme.ringCatSheaf.2 M)
  have hrr := finrank_cohomologyOverField_zero_sub_one_eq k pY hdim M hM
  rw [finrank_cohomologyOverField_unit_zero_eq_one pY] at hrr
  have hvan := isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree
    k pY M hM (by
      change _ ≤ invertibleCurveDegree k pY hdim M
      rw [h1, ← hg]
      omega)
  have hone : Module.finrank k (cohomologyOverField k pY M 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero hvan
    Module.finrank_zero_of_subsingleton
  change _ = invertibleCurveDegree k pY hdim M + _ - _ at hrr
  rw [hone, h1, ← hg] at hrr
  push_cast at hrr
  rw [sub_zero] at hrr
  rw [← hrr]
  congr 1
  calc D.h0 k sC = Module.finrank k ((globalSectionsOver sC).obj D.divisorialSheaf) := rfl
    _ = Module.finrank k ((globalSectionsOver pY).obj
          (D.divisorialSheaf.restrict (smoothLocus sC).ι)) :=
        (finrank_globalSectionsOver_restrict sC _ hsm).symm
    _ = Module.finrank k ((globalSectionsOver pY).obj
          ((Scheme.Modules.pullback (smoothLocus sC).ι).obj D.divisorialSheaf)) :=
        ((globalSectionsOver pY).mapIso e).toLinearEquiv.finrank_eq
    _ = _ := (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver pY _).finrank_eq.symm

/-- On an integral scheme, the valuation along `Γ` of an element of the factor of `K(X)` is the
order of vanishing of its image in the function field. -/
private theorem valuation_eq_ordHom {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (Γ : MMP.Mori.PrimeDivisor X)
    (y : X.presheaf.stalk (componentGenericPoint X Γ.component)) :
    Γ.valuation y = X.ordHom Γ.genericPoint Γ.coheight_genericPoint
      ((MMP.Positivity.componentToFunctionField Γ.component).hom y) := by
  let := Γ.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions Γ.genericPoint_mem_component
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
  let ψ := IsLocalization.algEquiv (nonZeroDivisors Γ.localRing)
    (X.presheaf.stalk (componentGenericPoint X Γ.component)) (FractionRing Γ.localRing)
  change Ring.ordFrac Γ.localRing (ψ y) = Ring.ordFrac (X.presheaf.stalk Γ.genericPoint) _
  have key := MMP.Positivity.ordFrac_map_of_comp (R := Γ.localRing)
    (K₁ := FractionRing Γ.localRing) (K₂ := X.functionField)
    ((MMP.Positivity.componentToFunctionField Γ.component).hom.comp (ψ.symm : _ →+* _)) ?_ (ψ y)
  · simpa using key.symm
  · intro r
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]
    change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom r =
      (X.presheaf.stalkSpecializes _).hom r
    rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- The generization from the factor of `K(X)` on a component to the function field is
injective. -/
private theorem eq_zero_of_componentToFunctionField_eq_zero {X : Scheme.{u}} [IsIntegral X]
    (Z : irreducibleComponents X) (y : X.presheaf.stalk (componentGenericPoint X Z))
    (hy : (MMP.Positivity.componentToFunctionField Z).hom y = 0) : y = 0 := by
  by_contra hy0
  exact ((MMP.Mori.isUnit_of_ne_zero_stalk Z hy0).map
    (MMP.Positivity.componentToFunctionField Z).hom).ne_zero hy

/-- **A rational function of exact order at a point in large degree.** If `deg D > deg K + 1`,
some nonzero `f ∈ H⁰(C, 𝒪_C(D))` has exact order `-coeff_Q D` along `Q`. -/
private theorem exists_ord_ge_neg_coeff_and_ord_eq
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) (D : Divisor C)
    (hdeg : (K.sum fun _ a => a) + 1 < D.sum fun _ a => a) (Q : MMP.Mori.PrimeDivisor C) :
    ∃ f : C.functionField, f ≠ 0 ∧ (∀ Γ : MMP.Mori.PrimeDivisor C,
      -D.coeff Γ ≤ C.ord f Γ.genericPoint) ∧ C.ord f Q.genericPoint + D.coeff Q = 0 := by
  classical
  set D' : Divisor C := D - Finsupp.single Q 1 with hD'
  have hdegD' : (D'.sum fun _ a => a) = (D.sum fun _ a => a) - 1 := by
    rw [hD', Finsupp.sum_sub_index (fun _ _ _ => rfl)]
    simp
  have h1 := h0_eq_sum_coeff_add_one_sub_h0_canonical hC hsm hp hK D (by omega)
  have h2 := h0_eq_sum_coeff_add_one_sub_h0_canonical hC hsm hp hK D' (by omega)
  have hne : D'.divisorialSubmodule ⊤ ≠ D.divisorialSubmodule ⊤ := by
    intro heq
    have : D'.h0 k sC = D.h0 k sC := by unfold Divisor.h0; rw [heq]
    omega
  have hle : D'.divisorialSubmodule ⊤ ≤ D.divisorialSubmodule ⊤ :=
    Divisor.divisorialSubmodule_mono (sub_le_self _ (Finsupp.single_nonneg.2 zero_le_one)) ⊤
  obtain ⟨φ, hφD, hφD'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have huniv : ∀ Z : irreducibleComponents C, Z.1 = Set.univ := fun Z =>
    Z.2.eq_of_le (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _)
  have hmemE : ∀ E : MMP.Mori.PrimeDivisor C, (E.support ∩ (⊤ : C.Opens)).Nonempty := fun E =>
    ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, trivial⟩
  have hp' : ∀ (Z : irreducibleComponents C) (hZ : componentGenericPoint C Z ∈ (⊤ : C.Opens)),
      (MMP.Positivity.componentToFunctionField Z).hom (φ ⟨Z, hZ⟩) =
        (MMP.Positivity.componentToFunctionField Q.component).hom
          (φ ⟨Q.component, Q.componentGenericPoint_mem_of_nonempty (hmemE Q)⟩) := by
    intro Z hZ
    have : Z = Q.component := Subtype.ext ((huniv _).trans (huniv _).symm)
    subst this
    rfl
  set f := (MMP.Positivity.componentToFunctionField Q.component).hom
    (φ ⟨Q.component, Q.componentGenericPoint_mem_of_nonempty (hmemE Q)⟩) with hf
  have hord : ∀ (E : MMP.Mori.PrimeDivisor C) (a : ℤ),
      E.OrdGE a (φ ⟨E.component, E.componentGenericPoint_mem_of_nonempty (hmemE E)⟩) ↔
        f = 0 ∨ a ≤ C.ord f E.genericPoint := by
    intro E a
    have hfE := hp' E.component (E.componentGenericPoint_mem_of_nonempty (hmemE E))
    unfold MMP.Mori.PrimeDivisor.OrdGE
    rw [valuation_eq_ordHom, hfE]
    by_cases hf0 : f = 0
    · simp only [hf0, true_or, iff_true]
      left
      exact eq_zero_of_componentToFunctionField_eq_zero _ _ (hfE.trans hf0)
    · rw [Scheme.le_ord_iff E.coheight_genericPoint hf0]
      have : φ ⟨E.component, E.componentGenericPoint_mem_of_nonempty (hmemE E)⟩ ≠ 0 := fun h =>
        hf0 (by rw [← hfE, h, map_zero])
      simp only [this, hf0, false_or]
      rfl
  have hf0 : f ≠ 0 := fun h0 => hφD' fun E hE => (hord E _).2 (Or.inl h0)
  have hD : ∀ Γ : MMP.Mori.PrimeDivisor C, -D.coeff Γ ≤ C.ord f Γ.genericPoint := fun Γ =>
    ((hord Γ _).1 (hφD Γ (hmemE Γ))).resolve_left hf0
  have hD'coeff : ∀ Γ, D'.coeff Γ = D.coeff Γ - if Γ = Q then 1 else 0 := fun Γ => by
    simp [hD', DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, eq_comm]
  refine ⟨f, hf0, hD, ?_⟩
  by_contra hQ
  apply hφD'
  intro E hE
  refine (hord E _).2 (Or.inr ?_)
  have := hD E
  rw [hD'coeff]
  split_ifs with hEQ
  · subst hEQ
    omega
  · omega

end RR

section Hex

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- On an affine curve every `𝒪(nK + G - T)` has a section of exact order at any point. -/
private theorem hex_of_affine [IsAffine X] (hC : IsNormalVariety k sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 1) (n : ℕ) (G : Divisor X)
    (T : Finset (MMP.Mori.PrimeDivisor X)) (Q₀ : MMP.Mori.PrimeDivisor X) :
    ∃ u ∈ pluricanonicalSections sX 1 (n : ℕ) (G - ∑ Q ∈ T, Finsupp.single Q 1) ⊤, u ≠ 0 ∧
      Q₀.ordForm u + (G - ∑ Q ∈ T, Finsupp.single Q 1).coeff Q₀ = 0 := by
  obtain ⟨f, hf0, hf, hfQ⟩ := exists_function_exact_order hK.1
    ((n : ℤ) • K + (G - ∑ Q ∈ T, Finsupp.single Q 1)) Q₀
  exact exists_form_of_function hC hK n _ f hf0 hf Q₀ hfQ

/-- On a proper curve, `𝒪(nK + G - T)` has a section of exact order at any point once its degree
exceeds `deg K + 1`, by Riemann–Roch. -/
private theorem hex_of_degree (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hp : IsProper sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) (n : ℕ) (G : Divisor X)
    (c : ℕ)
    (hdeg : (K.sum fun _ a => a) + 1 + (c : ℤ) < n * (K.sum fun _ a => a) + G.sum fun _ a => a)
    (T : Finset (MMP.Mori.PrimeDivisor X)) (Q₀ : MMP.Mori.PrimeDivisor X) (hT : T.card ≤ c) :
    ∃ u ∈ pluricanonicalSections sX 1 (n : ℕ) (G - ∑ Q ∈ T, Finsupp.single Q 1) ⊤, u ≠ 0 ∧
      Q₀.ordForm u + (G - ∑ Q ∈ T, Finsupp.single Q 1).coeff Q₀ = 0 := by
  classical
  set E' : Divisor X := G - ∑ Q ∈ T, Finsupp.single Q 1 with hE'
  have hdegE' : (E'.sum fun _ a => a) = (G.sum fun _ a => a) - T.card := by
    rw [hE', Finsupp.sum_sub_index (fun _ _ _ => rfl),
      ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  set D : Divisor X := (n : ℤ) • K + E' with hD
  have hdegD : (D.sum fun _ a => a) = n * (K.sum fun _ a => a) + E'.sum fun _ a => a := by
    rw [hD, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_smul_index' (fun _ => rfl)]
    simp [Finsupp.sum, Finset.mul_sum]
  obtain ⟨f, hf0, hf, hfQ⟩ := exists_ord_ge_neg_coeff_and_ord_eq hC hsm hp hK D
    (by
      rw [hdegD, hdegE']
      have : (T.card : ℤ) ≤ c := by exact_mod_cast hT
      omega) Q₀
  exact exists_form_of_function hC hK n E' f hf0 hf Q₀ (by rw [hD] at hfQ; omega)

end Hex

section Nef

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The degree of `K` as a `ℚ`-divisor is the degree of `K`. -/
private theorem sum_toQDivisor (K : Divisor X) :
    (Divisor.toQDivisor K).sum (fun _ a => a) = ((K.sum fun _ a => a : ℤ) : ℚ) := by
  have : Divisor.toQDivisor K = Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero K := rfl
  rw [this, Finsupp.sum_mapRange_index (fun _ => rfl)]
  simp [Finsupp.sum]

/-- `deg G = m · deg Δ` when `G = mΔ` coefficientwise. -/
private theorem cast_sum_eq_mul_sum {Δ : QDivisor X} {m : ℕ} {G : Divisor X}
    (hG : Divisor.toQDivisor G = (m : ℤ) • Δ) :
    ((G.sum fun _ a => a : ℤ) : ℚ) = m * Δ.sum fun _ a => a := by
  rw [← sum_toQDivisor, hG, Finsupp.sum_smul_index' (fun _ => rfl)]
  simp [Finsupp.sum, Finset.mul_sum]

private theorem isIso_curveSubschemeAtι_genericPoint :
    IsIso (curveSubschemeAtι (genericPoint X)) := by
  have hsurj : Surjective (curveSubschemeAtι (genericPoint X)) := by
    refine ⟨fun x => ?_⟩
    unfold curveSubschemeAtι
    rw [← Set.mem_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    have : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
    simp [this]
  exact isIso_of_isClosedImmersion_of_surjective _

/-- On a proper scheme of dimension one, the generic point is the generic point of a proper curve
(the scheme itself). -/
theorem isProperCurve_genericPoint (hdim : topologicalKrullDim X = 1) (hp : IsProper sX) :
    IsProperCurve sX (genericPoint X) := by
  have := isIso_curveSubschemeAtι_genericPoint (X := X)
  refine ⟨?_, ?_⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (curveSubschemeAtι (genericPoint X)))).isHomeomorph, hdim]
  · infer_instance

/-- The curve itself, as a proper curve of its ambient scheme. -/
noncomputable def genericCurve (hdim : topologicalKrullDim X = 1) (hp : IsProper sX) :
    ProperCurve sX := ⟨genericPoint X, isProperCurve_genericPoint hdim hp⟩

/-- On a smooth proper curve, the degree of `𝒪(E)` along the curve itself is the sum of the
coefficients of `E`. -/
theorem degreeOn_genericPoint_eq_sum (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hp : IsProper sX) (hdim : topologicalKrullDim X = 1) (E : Divisor X) :
    E.degreeOn k sX (genericCurve hdim hp).ι (genericCurve hdim hp).dim_le
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm E) = E.sum fun _ a => a := by
  have : LocallyOfFiniteType sX := hC.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hC.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨-, -, hprop, -⟩ := curve_instances hC hsm hp hdim hsm
  have : IsIso (smoothLocus sX).ι := by
    rw [hsm, ← Scheme.topIso_hom]
    infer_instance
  have hιC : IsIso (genericCurve hdim hp).ι := isIso_curveSubschemeAtι_genericPoint
  have hdim' : topologicalKrullDim (smoothLocus sX).toScheme ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (smoothLocus sX).ι)).isHomeomorph, hdim]
  rw [← degreeOn_smoothLocus_eq_sum hC hsm hp hdim hdim' E]
  have := (MMP.Fourfold.isCartier_of_isSmoothScheme hsm E).isInvertibleModule_divisorialSheaf
  unfold Divisor.degreeOn
  exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX (genericCurve hdim hp).ι
    (smoothLocus sX).ι (genericCurve hdim hp).dim_le hdim'
    ((asIso (genericCurve hdim hp).ι).trans (asIso (smoothLocus sX).ι).symm) (by simp) _

/-- **Nefness gives nonnegative degree.** If `K + Δ` is nef over `Z` and the smooth proper curve
`X` is contracted by `f : X ⟶ Z`, then `deg(K + Δ) ≥ 0`. -/
theorem sum_nonneg_of_isRelativelyNef {Z : Scheme.{u}} [QuasiCompact sX]
    (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hp : IsProper sX)
    (hdim : topologicalKrullDim X = 1) {K : Divisor X} {Δ : QDivisor X} (f : X ⟶ Z)
    (hconst : ∀ x, f x = f (genericPoint X))
    (hnef : QDivisor.IsRelativelyNef sX f (Divisor.toQDivisor K + Δ)) :
    0 ≤ (K.sum fun _ a => (a : ℚ)) + Δ.sum fun _ a => a := by
  have hD := hnef.1
  have hcon : (genericCurve hdim hp).IsContractedBy f := fun x _ => hconst x
  have h0 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hD
    (genericCurve hdim hp) hcon
  set D : QDivisor X := Divisor.toQDivisor K + Δ with hDdef
  have hcI := QDivisor.isCartierDivisor_cartierIndex_smul hD
  set E : Divisor X := hcI.toDivisor with hEdef
  have hE : Divisor.toQDivisor E = ((D.cartierIndex hD : ℕ) : ℤ) • D := hcI.toQDivisor_toDivisor
  have hpos : (0 : ℚ) < D.cartierIndex hD := by exact_mod_cast QDivisor.cartierIndex_pos hD
  have hDsum : D.sum (fun _ a => a) = (K.sum fun _ a => (a : ℚ)) + Δ.sum fun _ a => a := by
    rw [hDdef, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_toQDivisor]
    simp [Finsupp.sum]
  rw [← hDsum]
  unfold QDivisor.intersectionNumber at h0
  have h1 : ((E.degreeOn k sX (genericCurve hdim hp).ι (genericCurve hdim hp).dim_le
      hcI.isCartier_toDivisor : ℤ) : ℚ) = (E.sum fun _ a => a : ℤ) := by
    exact_mod_cast degreeOn_genericPoint_eq_sum hC hsm hp hdim E
  have h2 : 0 ≤ ((E.sum fun _ a => a : ℤ) : ℚ) / (D.cartierIndex hD : ℕ) := by
    rwa [← h1]
  rwa [cast_sum_eq_mul_sum hE, mul_div_cancel_left₀ _ hpos.ne'] at h2

end Nef

end MMP.Flips

namespace MMP.Flips.NormalizationComponents

open MMP.Mori

variable {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
  {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents sC hC)

section LAff

variable [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The prime divisors of coefficient `≥ 1` in `Δ` are the elements of the finset obtained by
filtering its support. -/
private theorem mem_filter_one_le_coeff_iff (Δ : QDivisor X)
    [DecidablePred fun P => (1 : ℚ) ≤ Δ.coeff P] (P : MMP.Mori.PrimeDivisor X) :
    P ∈ Δ.support.filter (fun P => 1 ≤ Δ.coeff P) ↔ 1 ≤ Δ.coeff P := by
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
  intro h h0
  rw [show Δ.coeff P = 0 by simpa [DivisorWithCoeffs.coeff_apply] using h0] at h
  norm_num at h

/-- Scaling `G = mΔ` by `c` gives `cG = (cm)Δ`. -/
private theorem toQDivisor_smul_eq {Δ : QDivisor X} {m : ℕ} {G : Divisor X}
    (hG : Divisor.toQDivisor G = (m : ℤ) • Δ) (c : ℕ) :
    Divisor.toQDivisor ((c : ℤ) • G) = ((c * m : ℕ) : ℤ) • Δ := by
  rw [map_zsmul, hG, smul_smul]
  push_cast; rfl

/-- For `P` in the floor of `Δ` (coefficient exactly `1`), `G.coeff P = n`. -/
private theorem coeff_eq_of_coeff_eq_one {Δ : QDivisor X} {n : ℕ} {G : Divisor X}
    (hG : Divisor.toQDivisor G = (n : ℤ) • Δ) {P : MMP.Mori.PrimeDivisor X}
    (h1 : 1 ≤ Δ.coeff P) (h2 : Δ.coeff P ≤ 1) : G.coeff P = n := by
  have h := congrArg (fun D => DivisorWithCoeffs.coeff D P) hG
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h
  have : Δ.coeff P = 1 := le_antisymm h2 h1
  rw [this] at h
  have : ((G.coeff P : ℤ) : ℚ) = ((n : ℤ) : ℚ) := by rw [h]; push_cast; ring
  exact_mod_cast this

/-- **The affine case.** On a smooth affine curve, for uniformizers `z_P` at every point `P`,
there is a section `s` of `𝒪(nK + G)`, `G = nΔ`, congruent to `(dz_P/z_P)^n` modulo
`𝔪_P 𝒪(nK + G)_P` at the points `P` of `⌊Δ⌋` and not vanishing at any point of a finite set
`R`. -/
public theorem exists_mem_pluricanonicalSections_sub_dlogPow_of_affine [IsAffine X]
    (hC : IsNormalVariety k sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {n : ℕ}
    {Δ : QDivisor X} (hΔ1 : ∀ P, Δ.coeff P ≤ 1)
    {G : Divisor X} (hG : Divisor.toQDivisor G = (n : ℤ) • Δ)
    (z : MMP.Mori.PrimeDivisor X → X.functionField) (hz : ∀ P, X.ord (z P) P.genericPoint = 1)
    (R : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ s : RationalPluriForms sX 1 n, s ∈ pluricanonicalSections sX 1 n G ⊤ ∧
      (∀ P, 1 ≤ Δ.coeff P → s - dlogPow sX (z P) n = 0 ∨
          1 ≤ P.ordForm (s - dlogPow sX (z P) n) + G.coeff P) ∧
      ∀ P ∈ R, s ≠ 0 ∧ P.ordForm s + G.coeff P = 0 := by
  classical
  have hdim : topologicalKrullDim X = 1 := hK.1
  set F := Δ.support.filter (fun P => 1 ≤ Δ.coeff P)
  have hF := mem_filter_one_le_coeff_iff Δ
  obtain ⟨s, hs, hsR⟩ := exists_goodSec_nonVan_of_hex hC hdim n hG z hz F hF
    (R.filter (· ∉ F)) (fun P hP => (Finset.mem_filter.1 hP).2)
    (fun T Q₀ _ _ => hex_of_affine hC hK n G T Q₀)
  refine ⟨s, hs.1, fun P hP => (hs.2 P hP).imp id fun h => by omega, fun P hP => ?_⟩
  by_cases hPF : P ∈ F
  · exact hs.nonvanishing hC hdim P ((hF P).1 hPF) (hz P)
      (coeff_eq_of_coeff_eq_one hG ((hF P).1 hPF) (hΔ1 P))
  · exact hsR P (Finset.mem_filter.2 ⟨hP, hPF⟩)

/-- On a smooth affine curve there is a normalized section of `𝒪(n(K + Δ))` not vanishing at any
point of a finite set `R`
(`exists_mem_pluricanonicalSections_sub_dlogPow_of_affine`; the elliptic clause is vacuous). -/
private theorem exists_normalizedSection_of_affine [IsAffine X] (ε : EllipticNormalizationDatum k)
    (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hnp : ¬ IsProper sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {n : ℕ} (hn : 0 < n)
    {Δ : QDivisor X} (hΔ0 : Δ.IsEffective) (hΔ1 : ∀ P, Δ.coeff P ≤ 1)
    {G : Divisor X} (hG : Divisor.toQDivisor G = (n : ℤ) • Δ)
    (R : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ s : RationalPluriForms sX 1 n, IsNormalizedSection ε sX Δ n G s ∧
      ∀ P ∈ R, s ≠ 0 ∧ P.ordForm s + G.coeff P = 0 := by
  choose z hz0 hz using fun P : MMP.Mori.PrimeDivisor X => exists_ord_genericPoint_eq_one' P
  obtain ⟨s, hmem, hvan, hsR⟩ :=
    exists_mem_pluricanonicalSections_sub_dlogPow_of_affine hC hK hΔ1 hG z hz R
  have hs : GoodSec Δ n G z s := ⟨hmem, fun P hP => (hvan P hP).imp id fun h => by omega⟩
  exact ⟨s, hs.isNormalizedSection ε hC hsm hK.1 hΔ0 hn hG hz (fun h => hnp h.1), hsR⟩

end LAff

section LProp

variable [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- For a `ℚ`-divisor with nonnegative coefficients, the number of components of coefficient
`≥ 1` is at most the degree. -/
private theorem card_filter_one_le_sum {α : Type*} (Δ : α →₀ ℚ) (hΔ : ∀ a, 0 ≤ Δ a) :
    ((Δ.support.filter (fun a => 1 ≤ Δ a)).card : ℚ) ≤ Δ.sum fun _ a => a := by
  classical
  calc ((Δ.support.filter (fun a => 1 ≤ Δ a)).card : ℚ)
      = ∑ a ∈ Δ.support.filter (fun a => 1 ≤ Δ a), (1 : ℚ) := by simp
    _ ≤ ∑ a ∈ Δ.support.filter (fun a => 1 ≤ Δ a), Δ a :=
      Finset.sum_le_sum fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑ a ∈ Δ.support, Δ a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ => hΔ a

/-- **The degree estimate.** For integers `a = deg K` and `b = deg G` with `b = m · D`, `m ≥ 1`,
`a + D > 0` and `c ≤ 1 + D`, we have `a + c < 24m · a + 24 · b`. The integrality of `b` is what
turns `m · a + b > 0` into `m · a + b ≥ 1`. -/
private theorem add_lt_twentyfour_mul {a b : ℤ} {D : ℚ} {m c : ℕ} (hm : 0 < m)
    (hb : (b : ℚ) = m * D) (hd : 0 < (a : ℚ) + D) (hc : (c : ℚ) ≤ 1 + D) :
    a + (c : ℤ) < ((24 * m : ℕ) : ℤ) * a + 24 * b := by
  have hmq : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℤ) < m * a + b := by
    have : (0 : ℚ) < m * a + b := by rw [hb]; nlinarith
    exact_mod_cast this
  have h1 : (1 : ℚ) ≤ m * a + b := by exact_mod_cast hpos
  have : (a : ℚ) + c < (24 * m : ℚ) * a + 24 * b := by
    rw [hb] at h1 ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hmq) hd.le]
  push_cast
  exact_mod_cast this

/-- **The proper case of positive degree.** On a smooth proper curve with `deg(K + Δ) > 0`, for
uniformizers `z_P` at every point `P`, there is a section `s` of `𝒪(24m(K + Δ))` congruent to
`(dz_P/z_P)^{24m}` modulo `𝔪_P 𝒪(24m(K + Δ))_P` at the points `P` of `⌊Δ⌋` and not vanishing
at any point of a finite set `R`. -/
public theorem exists_mem_pluricanonicalSections_sub_dlogPow_of_proper_pos
    (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hp : IsProper sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {m : ℕ} (hm : 0 < m)
    {Δ : QDivisor X} (hΔ0 : Δ.IsEffective) (hΔ1 : ∀ P, Δ.coeff P ≤ 1)
    {G'' : Divisor X} (hG'' : Divisor.toQDivisor G'' = (m : ℤ) • Δ)
    (hdeg : 0 < (K.sum fun _ a => (a : ℚ)) + Δ.sum fun _ a => a)
    (z : MMP.Mori.PrimeDivisor X → X.functionField) (hz : ∀ P, X.ord (z P) P.genericPoint = 1)
    (R : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ s : RationalPluriForms sX 1 (24 * m : ℕ),
      s ∈ pluricanonicalSections sX 1 (24 * m) ((24 : ℤ) • G'') ⊤ ∧
      (∀ P, 1 ≤ Δ.coeff P → s - dlogPow sX (z P) (24 * m) = 0 ∨
          1 ≤ P.ordForm (s - dlogPow sX (z P) (24 * m)) + ((24 : ℤ) • G'').coeff P) ∧
      ∀ P ∈ R, s ≠ 0 ∧ P.ordForm s + ((24 : ℤ) • G'').coeff P = 0 := by
  classical
  have hdim : topologicalKrullDim X = 1 := hK.1
  set n : ℕ := 24 * m with hn
  have hn0 : 0 < n := by omega
  set G : Divisor X := (24 : ℤ) • G'' with hGdef
  have hG : Divisor.toQDivisor G = (n : ℤ) • Δ := toQDivisor_smul_eq hG'' 24
  set F := Δ.support.filter (fun P => 1 ≤ Δ.coeff P)
  have hF := mem_filter_one_le_coeff_iff Δ
  have hFcard : (F.card : ℚ) ≤ Δ.sum fun _ a => a := card_filter_one_le_sum Δ hΔ0
  have hKq : (K.sum fun _ a => (a : ℚ)) = ((K.sum fun _ a => a : ℤ) : ℚ) := by
    simp [Finsupp.sum]
  have hbud := add_lt_twentyfour_mul (a := K.sum fun _ a => a) (b := G''.sum fun _ a => a)
    (D := Δ.sum fun _ a => a) (m := m) (c := F.card + 1) hm (cast_sum_eq_mul_sum hG'')
    (by rw [← hKq]; exact hdeg) (by push_cast; linarith)
  have hGsum : (G.sum fun _ a => a) = 24 * (G''.sum fun _ a => a) := by
    rw [hGdef, Finsupp.sum_smul_index' (fun _ => rfl)]
    simp [Finsupp.sum, Finset.mul_sum]
  have hdeg' : (K.sum fun _ a => a) + 1 + (F.card : ℤ) <
      n * (K.sum fun _ a => a) + G.sum fun _ a => a := by
    have hnz : (n : ℤ) = 24 * m := by omega
    rw [hGsum, hnz]
    push_cast at hbud ⊢
    linarith
  obtain ⟨s, hs, hsR⟩ := exists_goodSec_nonVan_of_hex hC hdim n hG z hz F hF
    (R.filter (· ∉ F)) (fun P hP => (Finset.mem_filter.1 hP).2)
    (fun T Q₀ _ hT => hex_of_degree hC hsm hp hK n G F.card hdeg' T Q₀ hT)
  refine ⟨s, hs.1, fun P hP => (hs.2 P hP).imp id fun h =>
    show 1 ≤ P.ordForm (s - dlogPow sX (z P) n) + G.coeff P by omega, fun P hP => ?_⟩
  by_cases hPF : P ∈ F
  · exact hs.nonvanishing hC hdim P ((hF P).1 hPF) (hz P)
      (coeff_eq_of_coeff_eq_one hG ((hF P).1 hPF) (hΔ1 P))
  · exact hsR P (Finset.mem_filter.2 ⟨hP, hPF⟩)

/-- On a smooth proper curve with `deg(K + Δ) > 0` there is a normalized section of
`𝒪(24m(K + Δ))` not vanishing at any point of a finite set `R`
(`exists_mem_pluricanonicalSections_sub_dlogPow_of_proper_pos`). The elliptic clause is vacuous,
since `Δ = 0` and `g = 1` would give `deg(K + Δ) = 0`. -/
private theorem exists_normalizedSection_of_proper_pos (ε : EllipticNormalizationDatum k)
    (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hp : IsProper sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {m : ℕ} (hm : 0 < m)
    {Δ : QDivisor X} (hΔ0 : Δ.IsEffective) (hΔ1 : ∀ P, Δ.coeff P ≤ 1)
    {G'' : Divisor X} (hG'' : Divisor.toQDivisor G'' = (m : ℤ) • Δ)
    (hdeg : 0 < (K.sum fun _ a => (a : ℚ)) + Δ.sum fun _ a => a)
    (R : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ s : RationalPluriForms sX 1 (24 * m : ℕ),
      IsNormalizedSection ε sX Δ (24 * m) ((24 : ℤ) • G'') s ∧
      ∀ P ∈ R, s ≠ 0 ∧ P.ordForm s + ((24 : ℤ) • G'').coeff P = 0 := by
  choose z hz0 hz using fun P : MMP.Mori.PrimeDivisor X => exists_ord_genericPoint_eq_one' P
  obtain ⟨s, hmem, hvan, hsR⟩ := exists_mem_pluricanonicalSections_sub_dlogPow_of_proper_pos
    hC hsm hp hK hm hΔ0 hΔ1 hG'' hdeg z hz R
  have hs : GoodSec Δ (24 * m) ((24 : ℤ) • G'') z s :=
    ⟨hmem, fun P hP => (hvan P hP).imp id fun h => by omega⟩
  have hell : ¬ (IsProper sX ∧ (∃ K' : Divisor X, K'.IsCanonicalDivisor sX 1 ∧ K'.h0 k sX = 1) ∧
      Δ = 0 ∧ 12 ∣ 24 * m) := by
    rintro ⟨-, ⟨K', hK', hK'1⟩, hΔ, -⟩
    have h2 := sum_coeff_canonical_eq hC hsm hp hK
    have : K.h0 k sX = K'.h0 k sX :=
      (h0_canonical_eq_genus hC hsm hp hK).trans (h0_canonical_eq_genus hC hsm hp hK').symm
    rw [this, hK'1] at h2
    rw [hΔ] at hdeg
    simp only [Finsupp.sum_zero_index, add_zero] at hdeg
    rw [h2] at hdeg
    norm_num at hdeg
  exact ⟨s, hs.isNormalizedSection ε hC hsm hK.1 hΔ0 (by omega) (toQDivisor_smul_eq hG'' 24) hz
    hell, hsR⟩

end LProp

section LZero

variable [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The proper case of degree zero.** On a smooth proper curve with `deg(K + Δ) = 0` the
normalized section of `𝒪(24m(K + Δ))` has no zeros. -/
private theorem exists_normalizedSection_of_proper_zero (ε : EllipticNormalizationDatum k)
    (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hp : IsProper sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {m : ℕ} (hm : 0 < m)
    {Δ : QDivisor X} (hΔ0 : Δ.IsEffective) (hΔ1 : ∀ P, Δ.coeff P ≤ 1)
    {G'' : Divisor X} (hG'' : Divisor.toQDivisor G'' = (m : ℤ) • Δ)
    (hdeg : (K.sum fun _ a => (a : ℚ)) + Δ.sum (fun _ a => a) = 0) :
    ∃ s : RationalPluriForms sX 1 (24 * m : ℕ),
      IsNormalizedSection ε sX Δ (24 * m) ((24 : ℤ) • G'') s ∧
      ∀ P : MMP.Mori.PrimeDivisor X, s ≠ 0 ∧ P.ordForm s + ((24 : ℤ) • G'').coeff P = 0 := by
  have hbd : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).IsBoundary sX := by
    refine ⟨⟨hC.1.toIsSeparated, hC.1.toLocallyOfFiniteType, hC.1.toQuasiCompact⟩,
      inferInstance, satisfiesS2_iff_forall_min_le_depth.mpr
        ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp inferInstance).1,
      fun Γ => ⟨?_, ?_⟩⟩
    · exact hΔ0 Γ.1
    · exact hΔ1 Γ.1
  have hG' : Divisor.toQDivisor ((2 : ℤ) • G'') = ((2 * m : ℕ) : ℤ) • Δ :=
    toQDivisor_smul_eq hG'' 2
  obtain ⟨s, hs, hs0, hsP⟩ := exists_isNormalizedSection_of_degree_eq_zero ε sX hC hsm hp hK.1 hK
    hbd (by omega : 0 < 2 * m) hG' hdeg
  have e24 : (12 : ℕ) • (2 : ℤ) • G'' = (24 : ℤ) • G'' := by
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]; norm_num
  simp only [e24] at hs hsP
  rw [show 24 * m = 12 * (2 * m) by ring]
  exact ⟨s, hs, fun P => ⟨hs0, hsP P⟩⟩

end LZero

section Bdry

/-- The sum over `s` of the terms `f i` selected by `a = g i`, for injective `g`, is `0` or a
single term. -/
private theorem sum_ite_eq_zero_or {ι α : Type*} [DecidableEq α] (s : Finset ι) (g : ι → α)
    (hg : Function.Injective g) (a : α) (f : ι → ℚ) :
    (∑ i ∈ s, if a = g i then f i else 0) = 0 ∨
      ∃ i ∈ s, (∑ j ∈ s, if a = g j then f j else 0) = f i := by
  classical
  by_cases h : ∃ i ∈ s, a = g i
  · obtain ⟨i, hi, hai⟩ := h
    right
    refine ⟨i, hi, ?_⟩
    have : (∑ j ∈ s, if a = g j then f j else 0) = if a = g i then f i else 0 :=
      Finset.sum_eq_single_of_mem i hi (fun j _ hji => by
        have : ¬ a = g j := fun hj' => hji (hg (hj'.symm.trans hai))
        simp [this])
    rw [this]
    simp [hai]
  · left
    push Not at h
    exact Finset.sum_eq_zero fun i hi => by simp [h i hi]

/-- The coefficients of the boundary `Δᵢ` lie in `[0, 1]`. -/
theorem componentBoundaryCoeff_mem_Icc {Δ : QWeilDivisor C} (hΔ : IsSlcCurve sC Δ)
    (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)) :
    0 ≤ N.componentBoundaryCoeff Δ i P ∧ N.componentBoundaryCoeff Δ i P ≤ 1 := by
  classical
  unfold NormalizationComponents.componentBoundaryCoeff
  split_ifs with hnode
  · exact ⟨zero_le_one, le_rfl⟩
  · have hΔ' := hΔ.2.2.2.2.2
    have hinj : Function.Injective (fun Γ : WeilDivisorPrime C => Γ.1.genericPoint) :=
      fun a b h => Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)
    rcases sum_ite_eq_zero_or Δ.support (fun Γ : WeilDivisorPrime C => Γ.1.genericPoint) hinj
      ((N.n i).base P.genericPoint) Δ with h | ⟨Γ, -, h⟩
    · rw [h]
      exact ⟨le_rfl, zero_le_one⟩
    · rw [h]
      exact hΔ' Γ

/-- `m` times the coefficients of `Δᵢ` are integers. -/
theorem exists_int_eq_mul_componentBoundaryCoeff {Δ : QWeilDivisor C} {m : ℕ}
    (hint : ∀ Γ, ((m : ℚ) * Δ Γ).den = 1) (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)) :
    ∃ j : ℤ, (j : ℚ) = m * N.componentBoundaryCoeff Δ i P := by
  classical
  unfold NormalizationComponents.componentBoundaryCoeff
  split_ifs with hnode
  · exact ⟨m, by simp⟩
  · have hinj : Function.Injective (fun Γ : WeilDivisorPrime C => Γ.1.genericPoint) :=
      fun a b h => Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)
    rcases sum_ite_eq_zero_or Δ.support (fun Γ : WeilDivisorPrime C => Γ.1.genericPoint) hinj
      ((N.n i).base P.genericPoint) Δ with h | ⟨Γ, -, h⟩
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨((m : ℚ) * Δ Γ).num, by rw [h]; exact Rat.coe_int_num_of_den_eq_one (hint Γ)⟩

end Bdry

section Glue

/-- If `m` times every coefficient of `Δ` is an integer, then `mΔ` is an integral divisor. -/
theorem exists_divisor_eq_smul {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (Δ : QDivisor X) (m : ℕ) (h : ∀ P, ∃ j : ℤ, (j : ℚ) = m * Δ.coeff P) :
    ∃ G : Divisor X, Divisor.toQDivisor G = (m : ℤ) • Δ := by
  classical
  let G : Divisor X := Finsupp.mapRange (fun q : ℚ => (m * q).num) (by simp) Δ
  refine ⟨G, ?_⟩
  refine DivisorWithCoeffs.ext' fun P => ?_
  obtain ⟨j, hj⟩ := h P
  have hden : ((m : ℚ) * Δ.coeff P).den = 1 := by
    rw [← hj]
    exact Rat.den_intCast j
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]
  have : (G.coeff P : ℤ) = ((m : ℚ) * Δ.coeff P).num := by
    simp only [DivisorWithCoeffs.coeff_apply, G]
    exact Finsupp.mapRange_apply (f := fun q : ℚ => (m * q).num) (hf := by simp) (a := P) (g := Δ)
  rw [this, Rat.coe_int_num_of_den_eq_one hden]
  push_cast
  ring

end Glue

section Comp

variable [IsAlgClosed k]

/-- **One component of the normalization**: a normalized section of `𝒪_{Cᵢ}(24m(K_{Cᵢ} + Δᵢ))`
not vanishing at any point over the finite set `Q` of `C`. -/
private theorem exists_isNormalizedSection_ordForm_add_eq_zero (ε : EllipticNormalizationDatum k)
    {Δ : QWeilDivisor C} (hΔ : IsSlcCurve sC Δ)
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] [IsAffine Z]
    (g : C ⟶ Z) [IsProper g] (hg : g ≫ sZ = sC)
    (hnef : ∀ i, ∃ (Ki : Divisor (N.X i)) (Δi : QDivisor (N.X i)),
      Ki.IsCanonicalDivisor (N.n i ≫ sC) 1 ∧ N.IsComponentBoundary Δ i Δi ∧
        haveI := (N.isNormalVariety i).1.toLocallyOfFiniteType
        haveI : QuasiCompact (N.n i ≫ sC) := (N.isNormalVariety i).1.toQuasiCompact
        QDivisor.IsRelativelyNef (N.n i ≫ sC) (N.n i ≫ g) (Divisor.toQDivisor Ki + Δi))
    {m : ℕ} (hm : 0 < m) (hint : ∀ Γ, ((m : ℚ) * Δ Γ).den = 1)
    (Q : Set C) (hQfin : Q.Finite) (i : N.ι) :
    ∃ s : RationalPluriForms (N.n i ≫ sC) 1 (24 * m),
      (∃ (Δi : QDivisor (N.X i)) (Gi : Divisor (N.X i)),
        N.IsComponentBoundary Δ i Δi ∧ IsNormalizedSection ε (N.n i ≫ sC) Δi (24 * m) Gi s) ∧
      ∀ q ∈ Q, ∀ P : MMP.Mori.PrimeDivisor (N.X i), (N.n i).base P.genericPoint = q →
        s ≠ 0 ∧ ((P.ordForm s : ℤ) : ℚ) +
          ((24 * m : ℕ) : ℚ) * N.componentBoundaryCoeff Δ i P = 0 := by
  classical
  obtain ⟨Ki, Δi, hK, hbd, hnefi⟩ := hnef i
  have hft : LocallyOfFiniteType sC := hΔ.1.1.2.1
  have hfin : IsFinite (N.n i) := isFinite_n N i
  have hCv : IsNormalVariety k (N.n i ≫ sC) := N.isNormalVariety i
  have hsm : IsSmoothScheme (N.n i ≫ sC) := isSmoothScheme_n N hΔ i
  have hdim : topologicalKrullDim (N.X i) = 1 := topologicalKrullDim_X N hΔ.1 i
  have hΔ0 : Δi.IsEffective := fun P => by
    rw [hbd.2 P]
    exact (componentBoundaryCoeff_mem_Icc N hΔ i P).1
  have hΔ1 : ∀ P, Δi.coeff P ≤ 1 := fun P => by
    rw [hbd.2 P]
    exact (componentBoundaryCoeff_mem_Icc N hΔ i P).2
  obtain ⟨G'', hG''⟩ := exists_divisor_eq_smul Δi m (fun P => by
    rw [hbd.2 P]
    exact exists_int_eq_mul_componentBoundaryCoeff N hint i P)
  have hRfin : {P : MMP.Mori.PrimeDivisor (N.X i) | (N.n i).base P.genericPoint ∈ Q}.Finite :=
    (Scheme.Hom.finite_preimage (N.n i) hQfin).preimage
      (f := fun P : MMP.Mori.PrimeDivisor (N.X i) => P.genericPoint)
      (fun _ _ _ _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)
  set R := hRfin.toFinset with hR
  have hn0 : 0 < 24 * m := by omega
  have hG : Divisor.toQDivisor ((24 : ℤ) • G'') = ((24 * m : ℕ) : ℤ) • Δi :=
    toQDivisor_smul_eq hG'' 24
  obtain ⟨s, hs, hsR⟩ : ∃ s : RationalPluriForms (N.n i ≫ sC) 1 (24 * m : ℕ),
      IsNormalizedSection ε (N.n i ≫ sC) Δi (24 * m) ((24 : ℤ) • G'') s ∧
      ∀ P ∈ R, s ≠ 0 ∧ P.ordForm s + ((24 : ℤ) • G'').coeff P = 0 := by
    rcases component_dichotomy N hΔ sZ g hg i with ⟨hp, hconst⟩ | ⟨haff, hnp⟩
    · haveI := (N.isNormalVariety i).1.toLocallyOfFiniteType
      haveI : QuasiCompact (N.n i ≫ sC) := (N.isNormalVariety i).1.toQuasiCompact
      have hdeg := sum_nonneg_of_isRelativelyNef hCv hsm hp hdim (N.n i ≫ g) hconst hnefi
      rcases hdeg.eq_or_lt with h0 | hpos
      · obtain ⟨s, hs, hsP⟩ := exists_normalizedSection_of_proper_zero ε hCv hsm hp hK hm hΔ0 hΔ1
          hG'' h0.symm
        exact ⟨s, hs, fun P _ => hsP P⟩
      · exact exists_normalizedSection_of_proper_pos ε hCv hsm hp hK hm hΔ0 hΔ1 hG'' hpos R
    · exact exists_normalizedSection_of_affine ε hCv hsm hnp hK hn0 hΔ0 hΔ1 hG R
  refine ⟨s, ⟨Δi, (24 : ℤ) • G'', hbd, hs⟩, fun q hq P hP => ?_⟩
  have hPR : P ∈ R := hRfin.mem_toFinset.2 (by rwa [Set.mem_setOf_eq, hP])
  obtain ⟨hs0, hord⟩ := hsR P hPR
  refine ⟨hs0, ?_⟩
  have h1 : (((24 : ℤ) • G'').coeff P : ℤ) = 24 * G''.coeff P := by
    simp [DivisorWithCoeffs.coeff_apply]
  have h2 : ((G''.coeff P : ℤ) : ℚ) = m * N.componentBoundaryCoeff Δ i P := by
    have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hG''
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    rw [this, hbd.2 P]
    simp
  have h3 : ((P.ordForm s : ℤ) : ℚ) + 24 * ((G''.coeff P : ℤ) : ℚ) = 0 := by
    rw [h1] at hord
    exact_mod_cast hord
  rw [h2] at h3
  push_cast
  linarith

end Comp

/-- **Normalized sections with prescribed values on an slc curve** (FA 8.7, the extension
property of the proof of 12.2.11). Let `(C, Δ)` be an slc curve over an algebraically closed
field `k` of characteristic zero, with normalization components `Cᵢ` (`N`), `g : C ⟶ Z` proper
to an affine `Z` of finite type over `k` with `K_C + Δ` `g`-nef (on each `Cᵢ`,
`K_{Cᵢ} + Δᵢ` is `(nᵢ ≫ g)`-nef), and `m > 0` with `mΔ` integral. Let `I₀` be the components
of a union `C₀` of irreducible components of `C`, `u₀ᵢ` (`i ∈ I₀`) normalized sections of
`𝒪_{Cᵢ}(24m(K_{Cᵢ} + Δᵢ))`, and `Q` a finite set of closed points of `C` outside `C₀`. Then
there is a normalized section `u` of `𝒪_C(24m(K_C + Δ))` (`IsNormalizedSlcSection`) with
`uᵢ = u₀ᵢ` for `i ∈ I₀` and `u(q) ≠ 0` for every `q ∈ Q`. -/
@[mmp "lem_fa8_slc_curve_normalized_prescribed"]
public theorem exists_isNormalizedSlcSection_extend_of_finite [IsAlgClosed k] [CharZero k]
    (ε : EllipticNormalizationDatum k) {Δ : QWeilDivisor C} (hΔ : IsSlcCurve sC Δ)
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] [IsAffine Z]
    (g : C ⟶ Z) [IsProper g] (hg : g ≫ sZ = sC)
    (hnef : ∀ i, ∃ (Ki : Divisor (N.X i)) (Δi : QDivisor (N.X i)),
      Ki.IsCanonicalDivisor (N.n i ≫ sC) 1 ∧ N.IsComponentBoundary Δ i Δi ∧
        haveI := (N.isNormalVariety i).1.toLocallyOfFiniteType
        haveI : QuasiCompact (N.n i ≫ sC) := (N.isNormalVariety i).1.toQuasiCompact
        QDivisor.IsRelativelyNef (N.n i ≫ sC) (N.n i ≫ g) (Divisor.toQDivisor Ki + Δi))
    {m : ℕ} (hm : 0 < m) (hint : ∀ Γ, ((m : ℚ) * Δ Γ).den = 1)
    (I₀ : Set N.ι) (u₀ : ∀ i ∈ I₀, RationalPluriForms (N.n i ≫ sC) 1 (24 * m))
    (hu₀ : ∀ i (hi : i ∈ I₀), ∃ (Δi : QDivisor (N.X i)) (Gi : Divisor (N.X i)),
      N.IsComponentBoundary Δ i Δi ∧ IsNormalizedSection ε (N.n i ≫ sC) Δi (24 * m) Gi (u₀ i hi))
    (Q : Set C) (hQfin : Q.Finite)
    (hQ : ∀ q ∈ Q, IsClosed {q} ∧ ∀ i ∈ I₀, q ∉ Set.range (N.n i).base) :
    ∃ u : ∀ i : N.ι, RationalPluriForms (N.n i ≫ sC) 1 (24 * m),
      N.IsNormalizedSlcSection ε Δ (24 * m) u ∧ (∀ i (hi : i ∈ I₀), u i = u₀ i hi) ∧
      ∀ q ∈ Q, ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint = q →
        u i ≠ 0 ∧
          ((P.ordForm (u i) : ℤ) : ℚ) +
            ((24 * m : ℕ) : ℚ) * N.componentBoundaryCoeff Δ i P = 0 := by
  classical
  choose s hs hsQ using fun i =>
    exists_isNormalizedSection_ordForm_add_eq_zero N ε hΔ sZ g hg hnef hm hint Q hQfin i
  refine ⟨fun i => if hi : i ∈ I₀ then u₀ i hi else s i, ?_, ?_, ?_⟩
  · have hint' : ∀ Γ, (((24 * m : ℕ) : ℚ) * Δ Γ).den = 1 := by
      intro Γ
      have h : (((24 * m : ℕ) : ℚ) * Δ Γ) = ((24 : ℤ) : ℚ) * ((m : ℚ) * Δ Γ) := by
        push_cast; ring
      rw [h, ← Rat.coe_int_num_of_den_eq_one (hint Γ), ← Int.cast_mul]
      exact Rat.den_intCast _
    refine (isNormalizedSlcSection_iff_forall_isNormalizedSection N ε hΔ
      ⟨12 * m, by ring⟩ (by omega) hint' _).2 fun i => ?_
    by_cases hi : i ∈ I₀
    · simpa [hi] using hu₀ i hi
    · simpa [hi] using hs i
  · intro i hi
    simp [hi]
  · intro q hq i P hP
    by_cases hi : i ∈ I₀
    · exact absurd ⟨P.genericPoint, hP⟩ ((hQ q hq).2 i hi)
    · simpa [hi] using hsQ i q hq P hP

end MMP.Flips.NormalizationComponents
