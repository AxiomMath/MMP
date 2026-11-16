module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.Resolution.Blowup.ProjectiveBirationalIsBlowup
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import MMP.AlgebraicGeometry.Singularities.SncStrata.CrepantBirationalLift
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Realizing a projective refinement of a stratum on an ambient crepant model

Let `(X, B)` be a smooth projective variety with an snc subboundary `B` (rational coefficients
at most one, possibly negative), let `Z ⊆ X` be a *floor stratum* (a stratum of the reduced
coefficient-one part `B^{=1}`), and let `a : Z' ⟶ Z` be a projective birational morphism.
Then `a` is realized on an ambient crepant model: there are a projective log resolution
`p : X' ⟶ X` of `(X, B)`, whose crepant boundary `B'` (`K_{X'} + B' = p^*(K_X + B)`) is again an
snc subboundary, and a floor stratum `F ⊆ X'` of `B'` with a proper birational morphism
`g : F ⟶ Z'` such that `a ∘ g` is the restriction of `p` to `F`.

## Main results

* `MMP.Fourfold.IsSNCSubboundaryPair.exists_isLogResolution_isSNCStratum_comp_eq`.

## Implementation notes

Strata are reduced closed subschemes, given by closed immersions `ιZ : Z ⟶ X`, `ιF : F ⟶ X'`
whose images are strata of `MMP.Fourfold.coeffOnePart`. The compatibility of `F ⟶ Z'` with
the map `F ⟶ Z` induced by `p` is the identity `g ≫ a ≫ ιZ = ιF ≫ p`; as `ιZ` is a
monomorphism this pins the map `F ⟶ Z` as `g ≫ a`. Crepancy is
`MMP.Mori.IsCrepantBoundary` for a canonical divisor `K_X` of dimension `n`. The base field is
an algebraically closed field of characteristic zero; the source works over `ℂ`.

The proof writes the reduction of `Z'` as a blow-up `Bl_I Z` for a nonzero ideal `I` of `𝒪_Z`,
and lets `J = ι_* I ⊆ 𝒪_X` be its inverse image, so that `J 𝒪_Z = I`. A log resolution
`p : X' ⟶ X` of `(X, B)` principalizing `J` factors through `Bl_J X`; the crepant boundary `B'`
of `(X, B)` on `X'` is an snc subboundary, and the birational lift of `Z` along `p` is a floor
stratum `F ⊆ X'` mapping birationally onto `Z`. Its image in `Bl_J X` lies in the strict
transform of `Z`, which is `Bl_I Z`, so `F ⟶ Z` factors through the reduction of `Z'`,
properly and birationally. As `Z'` need not be reduced, the result is composed with the
reduction `Z'_red ⟶ Z'`, which is birational since `Z'` is reduced over a dense open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Closed subschemes with reduced sources -/

/-- A closed immersion with reduced source, whose ideal contains the kernel of `i` and whose
support is the range of `i`, is isomorphic to its source. -/
private lemma exists_iso_subscheme {A P : Scheme.{0}} (i : A ⟶ P) [IsClosedImmersion i]
    [IsReduced A] (K : P.IdealSheafData) (hK : i.ker ≤ K)
    (hs : (K.support : Set P) = Set.range i) :
    ∃ e : K.subscheme ≅ A, e.hom ≫ i = K.subschemeι := by
  let a : K.subscheme ⟶ A := IsClosedImmersion.lift i K.subschemeι (by rwa [K.ker_subschemeι])
  have ha : a ≫ i = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion a := by
    have : IsClosedImmersion (a ≫ i) := by rw [ha]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion a i
  have : Surjective a := ⟨fun x => by
    obtain ⟨c, hc⟩ : i x ∈ Set.range K.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hs]; exact ⟨x, rfl⟩
    exact ⟨c, i.isEmbedding.injective (by rw [← Scheme.Hom.comp_apply, ha]; exact hc)⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective a
  exact ⟨asIso a, ha⟩

/-- Two closed immersions with reduced sources and the same range are isomorphic over the
target. -/
private lemma exists_iso_of_range_eq {A B P : Scheme.{0}} (i₁ : A ⟶ P) (i₂ : B ⟶ P)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced A] [IsReduced B]
    (h : Set.range i₁ = Set.range i₂) : ∃ e : A ≅ B, e.hom ≫ i₂ = i₁ := by
  let K : P.IdealSheafData := i₁.ker ⊔ i₂.ker
  have hK : (K.support : Set P) = Set.range i₁ := by
    simp only [K, Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      Scheme.Hom.support_ker, i₁.isClosedEmbedding.isClosed_range.closure_eq,
      i₂.isClosedEmbedding.isClosed_range.closure_eq, ← h, Set.inter_self]
  obtain ⟨e₁, h₁⟩ := exists_iso_subscheme i₁ K le_sup_left hK
  obtain ⟨e₂, h₂⟩ := exists_iso_subscheme i₂ K le_sup_right (hK.trans h)
  refine ⟨e₁.symm ≪≫ e₂, ?_⟩
  simp [h₂, ← h₁]

/-- **Lifting through a closed immersion.** A quasi-compact morphism `φ : F ⟶ X` from a reduced
scheme whose image lies in the range of a closed immersion `ι : Z ⟶ X` factors through `ι`. -/
private lemma exists_comp_eq_of_range_subset {F Z X : Scheme.{0}} [IsReduced F]
    (ι : Z ⟶ X) [IsClosedImmersion ι] (φ : F ⟶ X) [QuasiCompact φ]
    (hφ : Set.range φ ⊆ Set.range ι) : ∃ g : F ⟶ Z, g ≫ ι = φ := by
  haveI : IsSchemeTheoreticallyDominant φ.toImage := inferInstance
  haveI : IsReduced φ.image := IsSchemeTheoreticallyDominant.isReduced φ.toImage
  let K : X.IdealSheafData := ι.ker ⊔ φ.imageι.ker
  have hrange : Set.range φ.imageι = closure (Set.range φ) := by
    rw [← Scheme.Hom.support_ker]
    exact φ.ker.range_subschemeι
  have hK : (K.support : Set X) = Set.range φ.imageι := by
    simp only [K, Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq,
      φ.imageι.isClosedEmbedding.isClosed_range.closure_eq]
    refine Set.inter_eq_right.mpr ?_
    rw [hrange]
    exact closure_minimal hφ ι.isClosedEmbedding.isClosed_range
  obtain ⟨e, he⟩ := exists_iso_subscheme φ.imageι K le_sup_right hK
  let l : K.subscheme ⟶ Z := IsClosedImmersion.lift ι K.subschemeι (by
    rw [K.ker_subschemeι]; exact le_sup_left)
  refine ⟨φ.toImage ≫ e.inv ≫ l, ?_⟩
  rw [Category.assoc, Category.assoc, IsClosedImmersion.lift_fac, ← he, Iso.inv_hom_id_assoc,
    Scheme.Hom.toImage_imageι]

/-- A reduced closed subscheme with irreducible range is integral. -/
private lemma isIntegral_of_isIrreducible_range {A P : Scheme.{0}} (ι : A ⟶ P)
    [IsClosedImmersion ι] [IsReduced A] (hirr : IsIrreducible (Set.range ι.base)) :
    IsIntegral A := by
  haveI : IrreducibleSpace (Set.range ι.base) := Subtype.irreducibleSpace hirr
  haveI : IrreducibleSpace A := (ι.isEmbedding.toHomeomorph).symm.surjective.irreducibleSpace
    (ι.isEmbedding.toHomeomorph).symm.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced A

/-- A reduced closed subscheme whose range is an snc stratum is integral. -/
private lemma isIntegral_of_isSNCStratum {A P : Scheme.{0}} (ι : A ⟶ P) [IsClosedImmersion ι]
    [IsReduced A] {R : Type*} [Zero R] {D : DivisorWithCoeffs R P}
    (h : IsSNCStratum D (Set.range ι.base)) : IsIntegral A :=
  isIntegral_of_isIrreducible_range ι (by obtain ⟨_, _, hmax⟩ := h; exact hmax.prop.1)

/-! ### Log resolutions principalizing an ideal -/

/-- The union of two closed subsets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_sup {T : Type*} [TopologicalSpace T] {A B : Closeds T}
    (hA : IsPureCodimOne A) (hB : IsPureCodimOne B) : IsPureCodimOne (A ⊔ B) := by
  intro W hW
  have hsub : (W : Set T) ⊆ (A : Set T) ∪ B := hW.1
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp W.isIrreducible.isPreirreducible)
    _ _ A.isClosed B.isClosed hsub with h | h
  · exact hA W ⟨h, fun W' hW' hle ↦ hW.2 (hW'.trans Set.subset_union_left) hle⟩
  · exact hB W ⟨h, fun W' hW' hle ↦ hW.2 (hW'.trans Set.subset_union_right) hle⟩

/-- The support of an effective Cartier divisor on a scheme locally of finite type over a field
is of pure codimension one. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {D : Y.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : IsPureCodimOne D.support := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by rw [hWη]; exact subset_closure rfl
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hD (hW.1 hηW)
    fun y hy hyη => ?_
  have hle : W ≤ e.symm y := by
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    exact hyη
  have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ D.support := by
    change closure {y} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed
  have heq : e.symm y = W := le_antisymm (hW.2 hsub hle) hle
  rw [← heq, e.apply_symm_apply]

/-- The preimage in a subspace `C` of a preirreducible subset of `C` is preirreducible. -/
private theorem isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private theorem exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rw [← this]; exact hy
  exact subset_closure ⟨_, this, rfl⟩

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private theorem coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]; rfl

private theorem codimension_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    codimension (primeIrr E) = 1 := E.codimension_one

private theorem exists_mem_of_subset_iUnion {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)}
    (W : IrreducibleCloseds X) (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) :
    ∃ E ∈ s, W ≤ primeIrr E := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]; exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨E, hE, fun x hx ↦ by
    change x ∈ (primeIrr E : Set X); rw [coe_primeIrr]; exact hWz hx⟩

/-- A closed subset of pure codimension one of an snc divisor is an snc divisor. -/
private theorem isSNCSubset_of_le {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {S C : Closeds X}
    (hS : IsSNCSubset sX S) (hC : IsPureCodimOne C) (hCS : C ≤ S) : IsSNCSubset sX C := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact Or.inl (le_bot_iff.mp hCS)
  right
  refine ⟨s.filter (fun E ↦ E.support ⊆ C), ?_, ?_⟩
  · refine subset_antisymm (Set.iUnion₂_subset fun E hE ↦ (Finset.mem_filter.mp hE).2)
      fun x hx ↦ ?_
    obtain ⟨W, hW, hxW⟩ := exists_maximal_ge C.isClosed
      (IrreducibleCloseds.closureSingleton x) (by
        change closure {x} ⊆ (C : Set X)
        exact closure_minimal (by simpa using hx) C.isClosed)
    obtain ⟨E, hE, hWE⟩ := exists_mem_of_subset_iUnion W (hs ▸ hW.1.trans hCS)
    have hWE' : W = primeIrr E := by
      by_contra hne
      have := Order.coheight_add_one_le (lt_of_le_of_ne hWE hne)
      rw [← codimension_eq_coheight, ← codimension_eq_coheight, codimension_primeIrr,
        hC W hW] at this
      exact absurd this (by decide)
    refine Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hE, ?_⟩, ?_⟩ <;>
      rw [← coe_primeIrr, ← hWE']
    exacts [hW.1, hxW (subset_closure rfl)]
  · refine hsnc.of_support_subset ?_
    intro E hE
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE ⊢
    simp only [Finsupp.single_apply] at hE ⊢
    rw [Finset.sum_ite_eq'] at hE ⊢
    split_ifs at hE with h1
    · rw [if_pos (Finset.mem_filter.mp h1).1]; exact one_ne_zero
    · exact absurd rfl hE

/-- **A log resolution principalizing an ideal.** For a variety `X` over a field of
characteristic zero, an `ℝ`-divisor `D` and a nonzero ideal sheaf `J`, there is a projective log
resolution `f : Y ⟶ X` of `(X, D)` on which `J 𝒪_Y` is invertible. -/
private theorem exists_isLogResolution_isEffectiveCartierDivisor_comap {k : Type} [Field k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX)
    (D : RDivisor X) (J : X.IdealSheafData) (hJ : J ≠ ⊥) :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ X), AlgebraicGeometry.IsVariety k (f ≫ sX) ∧ IsProjective f ∧
      MMP.Mori.IsLogResolution sX D f ∧ Stacks.Divisors.IsEffectiveCartierDivisor (J.comap f) := by
  haveI : IsIntegral X := hX.toIsIntegral
  set IS := Scheme.IdealSheafData.vanishingIdeal D.supp
  have hsupp : (J * IS).support = J.support ⊔ D.supp := by
    rw [Scheme.IdealSheafData.support_mul]; rfl
  have hI : J * IS ≠ ⊥ := by
    intro h
    have hξ : genericPoint X ∈ (J * IS).support := by
      rw [h, Scheme.IdealSheafData.support_bot]; trivial
    rw [hsupp] at hξ
    rcases hξ with h1 | h2
    · exact genericPoint_notMem_supportSet J hJ (by simpa using h1)
    · exact genericPoint_notMem_supp D h2
  obtain ⟨Y, f, hYv, hproj, hbir, hsm, -, hcart, hsnc, hpure⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap sX hX (J * IS) hI
  rw [Stacks.IdealSheaf.comap_mul] at hcart
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have hSp : IsPureCodimOne (D.supp.preimage f.continuous) := by
    have := isPureCodimOne_support_of_isEffectiveCartierDivisor (f ≫ sX)
      (isEffectiveCartierDivisor_right_of_mul _ _ hcart)
    rwa [Scheme.IdealSheafData.support_comap] at this
  have hsupY : ((J * IS).comap f).support =
      J.support.preimage f.continuous ⊔ D.supp.preimage f.continuous := by
    rw [Scheme.IdealSheafData.support_comap, hsupp]; rfl
  rw [hsupY] at hsnc
  exact ⟨Y, f, hYv, hproj, ⟨⟨hproj.isProper, hbir, hsm⟩, hpure,
    isSNCSubset_of_le hsnc (isPureCodimOne_sup hpure hSp) (sup_le_sup_left le_sup_right _)⟩,
    isEffectiveCartierDivisor_left_of_mul _ _ hcart⟩

/-! ### The crepant boundary on a log resolution -/

/-- A prime divisor lies in the support of a reduced sum `∑_{E ∈ S} E` exactly when it is in
`S`. -/
private theorem mem_support_sum_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (G : MMP.Mori.PrimeDivisor X) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- A non-exceptional prime divisor of a resolution `Y` is the transform of a prime divisor `P` of
`X`, with the same crepant-boundary coefficient. -/
private theorem exists_coeff_eq_of_not_isExceptional {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {n : ℕ}
    {KX : Divisor X} (hPw : IsPairWith sX n KX B) {Y : Scheme.{0}} {f : Y ⟶ X}
    {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f} {B' : QDivisor Y}
    (hB'c : IsCrepantBoundary sX n KX B f hY hf B') (G : MMP.Mori.PrimeDivisor Y)
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, B'.coeff G = B.coeff P ∧
      f G.genericPoint = P.genericPoint := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw _ hG
  refine ⟨P, neg_injective ((hB'c G).eq hd), (inseparable_iff_closure_eq.2 ?_).eq⟩
  rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX),
    hc, AlgebraicGeometry.PrimeDivisor.support_eq_closure]

/-- The support of the crepant boundary `B'` on a resolution `f` lies in `Ex(f) ∪ f⁻¹(Supp B)`. -/
private theorem genericPoint_mem_of_mem_support {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {n : ℕ}
    {KX : Divisor X} (hPw : IsPairWith sX n KX B) {Y : Scheme.{0}} {f : Y ⟶ X}
    {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f} {B' : QDivisor Y}
    (hB'c : IsCrepantBoundary sX n KX B f hY hf B') {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ B'.support) : G.genericPoint ∈
      (exceptionalSet f ⊔ (QDivisor.toRDivisor B).supp.preimage f.continuous : Closeds Y) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  obtain ⟨P, hc, hη⟩ := exists_coeff_eq_of_not_isExceptional hPw hB'c G hGe
  refine Or.inr ?_
  change f G.genericPoint ∈ (QDivisor.toRDivisor B).supp
  rw [hη, DivisorWithCoeffs.mem_supp_iff]
  refine ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
  rw [QDivisor.coeff_toRDivisor, ← hc]
  have : B'.coeff G ≠ 0 := by
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hG
  exact_mod_cast this

/-- **The crepant boundary of an snc subboundary on a log resolution is an snc subboundary.** -/
private theorem exists_isSNCSubboundaryPair_isCrepantBoundary {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B)
    {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n) {Y : Scheme.{0}} (f : Y ⟶ X)
    (hYv : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hproj : IsProjective f)
    (hlog : MMP.Mori.IsLogResolution sX (QDivisor.toRDivisor B) f) :
    ∃ B' : QDivisor Y, IsSNCSubboundaryPair (f ≫ sX) B' ∧
      ∀ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f),
        IsCrepantBoundary sX n KX B f hY hf B' := by
  classical
  have hX : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hres : IsSmoothResolution sX f := hlog.toIsSmoothResolution
  obtain ⟨hY, -, -⟩ := hres.isNormalVariety hX
  have hf := hres.isBirationalMorphism
  have hqc := isQCartier_of_isSmoothScheme hB.isSmoothScheme (Divisor.toQDivisor KX + B)
  have hPw : IsPairWith sX n KX B := ⟨hX, hKX, hqc⟩
  obtain ⟨⟨B', hB'c, -⟩, -⟩ :=
    IsPair.existsUnique_isCrepantBoundary ⟨hX, n, KX, hKX, hqc⟩ hKX f hY hf
  have hsupp := fun G (hG : G ∈ B'.support) ↦ genericPoint_mem_of_mem_support hPw hB'c hG
  have hsncB : DivisorWithCoeffs.IsSNC sX (∑ E ∈ B.support, Finsupp.single E (1 : ℤ)) :=
    hB.isSNC.of_support_subset fun E hE => (mem_support_sum_single _ E).1 hE
  refine ⟨B', ⟨?_, hres.isSmoothScheme, ?_, fun G => ?_⟩, fun _ _ => hB'c⟩
  · exact (MMP.Mori.isProjectiveVariety_iff k (f ≫ sX)).2 ⟨hYv,
      isProjectiveMorphism_of_isProjective_of_isAffine (f ≫ sX)
        (hproj.comp hB.isProjectiveVariety.isProjective.isProjective)⟩
  · rcases hlog.isSNCSubset with hbot | ⟨S, hS, hsncS⟩
    · haveI : LocallyOfFinitePresentation (f ≫ sX) := by
        haveI := (MMP.Mori.isSmoothScheme_iff _).1 hres.isSmoothScheme
        infer_instance
      refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) (f ≫ sX)
        hres.isSmoothScheme).of_support_subset fun G hG => ?_
      have := hsupp G hG
      rw [hbot, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at this
      exact absurd this (Set.notMem_empty _)
    · refine hsncS.of_support_subset fun G hG => (mem_support_sum_single S G).2 ?_
      have h := hsupp G hG
      rw [← SetLike.mem_coe, ← hS] at h
      obtain ⟨E, hE, hGE⟩ := Set.mem_iUnion₂.mp h
      rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hGE] at hE
  · by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
    · obtain ⟨c, T, -, -, -, hTc, -, -, hle⟩ := le_isDiscrepancy_of_isSNC hX hB.isSmoothScheme hKX
        subset_rfl hsncB (fun E _ => hB.coeff_le_one E) _ hGe (hB'c G)
      have h1 : 0 ≤ ∑ E ∈ T, (1 - B.coeff E) :=
        Finset.sum_nonneg fun E _ => sub_nonneg.2 (hB.coeff_le_one E)
      have h2 : (0 : ℚ) ≤ (c : ℚ) - T.card := sub_nonneg.2 (by exact_mod_cast hTc)
      linarith
    · obtain ⟨P, hc, -⟩ := exists_coeff_eq_of_not_isExceptional hPw hB'c G hGe
      rw [hc]
      exact hB.coeff_le_one P

/-! ### Strict transforms -/

/-- **A morphism into a blow-up lying over an integral closed subscheme factors through its
strict transform.** Let `ι : Z ⟶ X` be an integral closed subscheme whose generic point is not
in `V(J)`, and `r : F ⟶ Bl_J X` a morphism from an integral scheme lying over a dominant
`q : F ⟶ Z`. Then `q` factors through `Bl_{J 𝒪_Z} Z ⟶ Z`. -/
private theorem exists_comp_blowUpToBase_eq {Z X F : Scheme.{0}} [IsIntegral Z] (ι : Z ⟶ X)
    [IsClosedImmersion ι] (J : X.IdealSheafData)
    (hη : ι (genericPoint Z) ∉ (J.support : Set X)) [IsIntegral F] (r : F ⟶ blowUp J)
    [QuasiCompact r] (q : F ⟶ Z) [IsDominant q] (hr : r ≫ blowUpToBase J = q ≫ ι) :
    ∃ ℓ : F ⟶ blowUp (J.comap ι), ℓ ≫ blowUpToBase (J.comap ι) = q := by
  have hJ' : J.comap ι ≠ ⊥ := by
    intro h
    apply hη
    have : genericPoint Z ∈ ((J.comap ι).support : Set Z) := by rw [h]; simp
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this
  haveI : IsIntegral (blowUp (J.comap ι)) := isIntegral_blowUp _ hJ'
  have hV : ¬ Set.range ι ⊆ (J.support : Set X) := fun h => hη (h ⟨_, rfl⟩)
  obtain ⟨hrange, -⟩ :=
    MMP.Resolution.Bridges.range_canonicalLift_eq_closure_and_ker_eq_vanishingIdeal ι J hV
  haveI := MMP.Resolution.Bridges.isClosedImmersion_canonicalLift ι J
  have hsub : Set.range r ⊆ Set.range (MMP.Resolution.canonicalLift ι J) := by
    rw [hrange]
    rintro _ ⟨x, rfl⟩
    have hspec : r (genericPoint F) ⤳ r x :=
      ((genericPoint_spec F).specializes (Set.mem_univ x)).map r.continuous
    refine (closure_mono (Set.singleton_subset_iff.mpr ?_)) (specializes_iff_mem_closure.mp hspec)
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hr, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant]
    exact ⟨⟨_, rfl⟩, hη⟩
  obtain ⟨ℓ, hℓ⟩ := exists_comp_eq_of_range_subset (MMP.Resolution.canonicalLift ι J) r hsub
  refine ⟨ℓ, ?_⟩
  rw [← cancel_mono ι, Category.assoc, ← MMP.Resolution.canonicalLift_comp_blowUpToBase,
    ← Category.assoc, hℓ, hr]

/-! ### Birationality -/

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{0}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- Pull-backs of rational functions compose along dominant morphisms of integral schemes. -/
private theorem functionFieldMap_comp_apply {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap (a ≫ b) t := by
  have := Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A) (genericPoint B) (genericPoint C)
    (map_genericPoint_of_isDominant a) (map_genericPoint_of_isDominant b)
    (map_genericPoint_of_isDominant (a ≫ b))
  exact (congrArg (fun φ => φ.hom t) this).symm

/-- If `g ≫ a` and `a` are birational, `a` is proper and `g` is locally of finite type, then `g`
is birational. -/
private theorem isBirationalMorphism_of_comp {F Z' Z : Scheme.{0}} [IsIntegral F]
    [IsIntegral Z'] [IsIntegral Z] [IsLocallyNoetherian Z] (g : F ⟶ Z')
    (a : Z' ⟶ Z) [IsProper a] [LocallyOfFiniteType g] (ha : IsBirationalMorphism a)
    (hga : IsBirationalMorphism (g ≫ a)) : IsBirationalMorphism g := by
  haveI := hga.isDominant
  haveI := ha.isDominant
  have hη : g (genericPoint F) = genericPoint Z' := by
    have hm : g (genericPoint F) ∈ a ⁻¹' {genericPoint Z} := by
      change a (g _) = _
      rw [← Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
    rwa [preimage_genericPoint a
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism ha)] at hm
  haveI : IsDominant g := ⟨by
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec Z').def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint F, hη⟩)⟩
  refine isBirationalMorphism_of_isBirational g
    (AlgebraicGeometry.isBirational_of_surjective_functionFieldMap g fun t => ?_)
  obtain ⟨z, hz⟩ := hga.functionFieldMap_bijective.2 t
  exact ⟨functionFieldMap a z, by rw [functionFieldMap_comp_apply g a, hz]⟩

/-! ### The reduction -/

/-- The source of a birational morphism to an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_of_isBirationalMorphism {Z' Z : Scheme.{0}} [IrreducibleSpace Z]
    {a : Z' ⟶ Z} (ha : IsBirationalMorphism a) : IrreducibleSpace Z' := by
  haveI := ha.isDominant
  haveI : Nonempty Z' := a.denseRange.nonempty
  obtain ⟨W, hWd, hW⟩ := exists_isOpenImmersion_of_isBirationalMorphism ha
  obtain ⟨w, hw⟩ := hWd.nonempty
  have hrng : IsIrreducible (Set.range (W.ι ≫ a)) :=
    ⟨⟨_, ⟨⟨w, hw⟩, rfl⟩⟩, (IrreducibleSpace.isIrreducible_univ Z).2.open_subset
      (W.ι ≫ a).isOpenEmbedding.isOpen_range (Set.subset_univ _)⟩
  haveI : IrreducibleSpace (Set.range (W.ι ≫ a)) := Subtype.irreducibleSpace hrng
  haveI : IrreducibleSpace W :=
    (W.ι ≫ a).isOpenEmbedding.toHomeomorph.symm.surjective.irreducibleSpace
      (W.ι ≫ a).isOpenEmbedding.toHomeomorph.symm.continuous
  have hWirr : IsIrreducible (W : Set Z') := by
    simpa using (IrreducibleSpace.isIrreducible_univ W).image W.ι W.ι.continuous.continuousOn
  exact (irreducibleSpace_def _).2 (by rw [Set.top_eq_univ, ← hWd.closure_eq]; exact hWirr.closure)

/-- The reduction `X_red ⟶ X` is surjective. -/
private theorem surjective_reduction (X : Scheme.{0}) :
    Function.Surjective (Scheme.IdealSheafData.vanishingIdeal ⊤ : X.IdealSheafData).subschemeι :=
  fun x => by
    have : x ∈ Set.range
        (Scheme.IdealSheafData.vanishingIdeal ⊤ : X.IdealSheafData).subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      trivial
    exact this

/-- The reduction of an irreducible scheme is integral. -/
private theorem isIntegral_reduction (X : Scheme.{0}) [IrreducibleSpace X] :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⊤ : X.IdealSheafData).subscheme := by
  let ρ := (Scheme.IdealSheafData.vanishingIdeal ⊤ : X.IdealSheafData).subschemeι
  let e := ρ.isEmbedding.toHomeomorphOfSurjective (surjective_reduction X)
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal ⊤ : X.IdealSheafData).subscheme :=
    e.symm.surjective.irreducibleSpace e.symm.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The reduction `X_red ⟶ X` of a scheme which is reduced on a dense open is birational. -/
private theorem isBirationalMorphism_reduction {X : Scheme.{0}} (W : X.Opens)
    (hWd : Dense (W : Set X)) [IsReduced W] :
    IsBirationalMorphism
      (Scheme.IdealSheafData.vanishingIdeal ⊤ : X.IdealSheafData).subschemeι := by
  set ρ := (Scheme.IdealSheafData.vanishingIdeal ⊤ : X.IdealSheafData).subschemeι
  have hρs := surjective_reduction X
  haveI : IsDominant ρ := ⟨hρs.denseRange⟩
  haveI : Surjective (ρ ∣_ W) := ⟨fun y => by
    obtain ⟨x, hx⟩ := hρs y.1
    exact ⟨⟨x, by change ρ x ∈ W; rw [hx]; exact y.2⟩,
      Subtype.ext ((morphismRestrict_base_coe ρ W _).trans hx)⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (ρ ∣_ W)
  haveI : IsOpenImmersion ((ρ ⁻¹ᵁ W).ι ≫ ρ) := by
    rw [← morphismRestrict_ι]; infer_instance
  exact isBirationalMorphism_of_isOpenImmersion ρ (ρ ⁻¹ᵁ W)
    (hWd.preimage (ρ.isEmbedding.toHomeomorphOfSurjective hρs).isOpenMap)

/-! ### The integral case -/

/-- An integral closed subscheme of a projective variety is a quasi-projective variety. -/
private theorem isQuasiProjectiveVariety_comp {k : Type} [Field k] {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (hXp : AlgebraicGeometry.IsProjectiveVariety k sX) (ιZ : Z ⟶ X)
    [IsClosedImmersion ιZ] [IsIntegral Z] : IsQuasiProjectiveVariety k (ιZ ≫ sX) := by
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hXp.toIsVariety
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : IsSeparated sX := hXv.toIsSeparated
  have hvar : AlgebraicGeometry.IsVariety k (ιZ ≫ sX) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance }
  rw [isQuasiProjectiveVariety_iff_isHQuasiProjective]
  refine ⟨hvar, ?_⟩
  obtain ⟨N, ιV, hιV, hιVs⟩ := hXp.isProjective
  exact ⟨N, ιZ ≫ ιV, inferInstance, inferInstance, by rw [Category.assoc, hιVs]⟩

/-- Let `p : Y ⟶ X` be proper with `J 𝒪_Y` invertible, `ιZ : Z ⟶ X` a closed integral subscheme
not contained in `Supp J`, and `a : Z' ⟶ Z` the blowup of `J 𝒪_Z`. A birational `q : F ⟶ Z`
with `q ≫ ιZ = ιF ≫ p` lifts to a proper birational `g : F ⟶ Z'`. -/
private theorem exists_isProper_isBirationalMorphism_comp_eq {X Y Z Z' F : Scheme.{0}}
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsIntegral Z'] [IsIntegral F]
    (ιZ : Z ⟶ X) [IsClosedImmersion ιZ] (J : X.IdealSheafData) [QuasiSeparated (blowUpToBase J)]
    (hηJ : ιZ (genericPoint Z) ∉ (J.support : Set X)) (p : Y ⟶ X) [IsProper p]
    (hpJ : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap p))
    (ιF : F ⟶ Y) [IsClosedImmersion ιF] (q : F ⟶ Z) (hq : q ≫ ιZ = ιF ≫ p)
    (hqb : IsBirationalMorphism q) (a : Z' ⟶ Z) (ha : IsProjectiveMorphism a)
    (ha' : IsBirationalMorphism a) (e : Z' ≅ blowUp (J.comap ιZ))
    (he : e.hom ≫ blowUpToBase (J.comap ιZ) = a) :
    ∃ g : F ⟶ Z', IsProper g ∧ IsBirationalMorphism g ∧ g ≫ a ≫ ιZ = ιF ≫ p := by
  haveI : IsDominant q := hqb.isDominant
  let h : Y ⟶ blowUp J := blowUpLift J p hpJ
  have hh : h ≫ blowUpToBase J = p := blowUpLift_comp J p hpJ
  haveI : QuasiCompact (ιF ≫ h) := by
    have : QuasiCompact ((ιF ≫ h) ≫ blowUpToBase J) := by
      rw [Category.assoc, hh]
      infer_instance
    exact QuasiCompact.of_comp _ (blowUpToBase J)
  obtain ⟨ℓ, hℓ⟩ := exists_comp_blowUpToBase_eq ιZ J hηJ (ιF ≫ h) q
    (by rw [Category.assoc, hh, hq])
  set g : F ⟶ Z' := ℓ ≫ e.inv with hgdef
  have hga : g ≫ a = q := by rw [hgdef, Category.assoc, ← he, Iso.inv_hom_id_assoc, hℓ]
  have hgcomm : g ≫ a ≫ ιZ = ιF ≫ p := by rw [← Category.assoc, hga, hq]
  haveI : IsProper a := isProper_of_isProjectiveMorphism a ha
  haveI : IsProper (g ≫ a ≫ ιZ) := by
    rw [hgcomm]
    infer_instance
  haveI : LocallyOfFiniteType g := LocallyOfFiniteType.of_comp (f := g) (g := a ≫ ιZ) inferInstance
  exact ⟨g, IsProper.of_comp g (a ≫ ιZ), isBirationalMorphism_of_comp g a ha' (hga ▸ hqb), hgcomm⟩

/-- `IsSNCSubboundaryPair.exists_isLogResolution_isSNCStratum_comp_eq` when `Z'` is integral. -/
private theorem exists_isLogResolution_isSNCStratum_comp_eq_of_isIntegral
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B)
    {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {Z : Scheme.{0}} (ιZ : Z ⟶ X) [IsClosedImmersion ιZ] [IsReduced Z]
    (hZ : IsSNCStratum (coeffOnePart B) (Set.range ιZ.base))
    {Z' : Scheme.{0}} [IsIntegral Z'] (a : Z' ⟶ Z) (ha : IsProjectiveMorphism a)
    (ha' : IsBirationalMorphism a) :
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (p : X' ⟶ X) (hp : IsLogResolution sX B p) (B' : QDivisor X'),
      IsSNCSubboundaryPair (p ≫ sX) B' ∧
      (∀ hX' : IsNormalVariety k (p ≫ sX),
        IsCrepantBoundary sX n KX B p hX' hp.isBirationalMorphism B') ∧
      ∃ (F : Scheme.{0}) (ιF : F ⟶ X') (_ : IsClosedImmersion ιF) (_ : IsReduced F)
        (g : F ⟶ Z'),
        IsSNCStratum (coeffOnePart B') (Set.range ιF.base) ∧
        IsProper g ∧ IsBirationalMorphism g ∧ g ≫ a ≫ ιZ = ιF ≫ p := by
  classical
  have hXp : AlgebraicGeometry.IsProjectiveVariety k sX := hB.isProjectiveVariety
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hXp.toIsVariety
  have hXn : IsNormalVariety k sX := ⟨hXv, inferInstance⟩
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : IsIntegral Z := isIntegral_of_isSNCStratum ιZ hZ
  haveI := isQuasiProjectiveVariety_comp hXp ιZ
  obtain ⟨I, hI0, -, e, he⟩ := MMP.exists_blowUp_iso_of_isProjective_of_isBirational (ιZ ≫ sX) a
    ha.isProjective (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism ha')
  obtain ⟨J, rfl⟩ : ∃ J : X.IdealSheafData, J.comap ιZ = I :=
    ⟨I.map ιZ, Scheme.IdealSheafData.comap_map_of_isClosedImmersion I ιZ⟩
  have hηJ : ιZ (genericPoint Z) ∉ (J.support : Set X) := fun h ↦
    genericPoint_notMem_supportSet _ hI0 (by simp; exact h)
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hηJ (by simp)
  obtain ⟨Y, p, hYv, hpproj, hplog, hpJ⟩ :=
    exists_isLogResolution_isEffectiveCartierDivisor_comap sX hXv (QDivisor.toRDivisor B) J hJ0
  have hres : IsSmoothResolution sX p := hplog.toIsSmoothResolution
  obtain ⟨hYn, -, -⟩ := hres.isNormalVariety hXn
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : IsNormal Y := hYn.2
  haveI : IsProper p := hres.isProper
  have hpH : IsProjectiveMorphism p := IsProjectiveMorphism.of_comp p sX
    (isProjectiveMorphism_of_isProjective_of_isAffine _ (hpproj.comp hXp.isProjective.isProjective))
  have hp : IsLogResolution sX B p := ⟨hplog, hpH⟩
  obtain ⟨B', hB', hcrep⟩ :=
    exists_isSNCSubboundaryPair_isCrepantBoundary hB hKX p hYv hpproj hplog
  have hlift := IsSNCSubboundaryPair.exists_stratumAdjunctionData_isBirationalMorphism hB hB' rfl
    hpH hres.isBirationalMorphism hKX ⟨hYn, hcrep hYn _⟩ hZ
  obtain ⟨S, ι, BS, ⟨F₀⟩, hS⟩ := hlift.1
  obtain ⟨F, ιF, CF, F', g', hFstr, hg'ι, hg'b, -⟩ := hlift.2 F₀ hS
  haveI := F₀.isIntegral_stratum
  haveI := F₀.isClosedImmersion
  haveI := F'.isIntegral_stratum
  haveI := F'.isClosedImmersion
  obtain ⟨φ, hφ⟩ := exists_iso_of_range_eq ι ιZ hS
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (ιZ ≫ sX)
  set q : F ⟶ Z := g' ≫ φ.hom with hqdef
  have hq : q ≫ ιZ = ιF ≫ p := by rw [hqdef, Category.assoc, hφ, hg'ι]
  have hqb : IsBirationalMorphism q :=
    isBirationalMorphism_comp hg'b (isBirationalMorphism_of_isIso _)
  obtain ⟨g, hgprop, hgb, hgcomm⟩ :=
    exists_isProper_isBirationalMorphism_comp_eq ιZ J hηJ p hpJ ιF q hq hqb a ha ha' e he
  exact ⟨Y, inferInstance, inferInstance, inferInstance, p, hp, B', hB',
    fun hX' => hcrep hX' _, F, ιF, inferInstance, inferInstance, g, hFstr, hgprop, hgb, hgcomm⟩

/-- **A projective refinement of a floor stratum is realized on an ambient crepant model.**
Let `(X, B)` be a smooth projective variety over `k` with an snc subboundary `B`
(`MMP.Fourfold.IsSNCSubboundaryPair`), `K_X` a canonical divisor of dimension `n`, `Z ⊆ X` a
reduced stratum of `B^{=1}` (`MMP.Fourfold.IsSNCStratum`, `MMP.Fourfold.coeffOnePart`), and
`a : Z' ⟶ Z` a projective birational morphism. Then there are a projective log resolution
`p : X' ⟶ X` of `(X, B)` (`MMP.Fourfold.IsLogResolution`) and the crepant boundary `B'` of
`(X, B)` on `X'` (`MMP.Mori.IsCrepantBoundary`), which is an snc subboundary, together with a
reduced stratum `F ⊆ X'` of `B'^{=1}` and a proper birational morphism `g : F ⟶ Z'` with
`g ≫ a ≫ ιZ = ιF ≫ p`. -/
@[mmp "lem_fourfold_stratum_refinement_ambient_model"]
public theorem IsSNCSubboundaryPair.exists_isLogResolution_isSNCStratum_comp_eq
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsSNCSubboundaryPair sX B)
    {n : ℕ} {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {Z : Scheme.{0}} (ιZ : Z ⟶ X) [IsClosedImmersion ιZ] [IsReduced Z]
    (hZ : IsSNCStratum (coeffOnePart B) (Set.range ιZ.base))
    {Z' : Scheme.{0}} (a : Z' ⟶ Z) (ha : IsProjectiveMorphism a)
    (ha' : IsBirationalMorphism a) :
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (p : X' ⟶ X) (hp : IsLogResolution sX B p) (B' : QDivisor X'),
      IsSNCSubboundaryPair (p ≫ sX) B' ∧
      (∀ hX' : IsNormalVariety k (p ≫ sX),
        IsCrepantBoundary sX n KX B p hX' hp.isBirationalMorphism B') ∧
      ∃ (F : Scheme.{0}) (ιF : F ⟶ X') (_ : IsClosedImmersion ιF) (_ : IsReduced F)
        (g : F ⟶ Z'),
        IsSNCStratum (coeffOnePart B') (Set.range ιF.base) ∧
        IsProper g ∧ IsBirationalMorphism g ∧ g ≫ a ≫ ιZ = ιF ≫ p := by
  haveI : IsIntegral Z := isIntegral_of_isSNCStratum ιZ hZ
  obtain ⟨W, hWd, hW⟩ := exists_isOpenImmersion_of_isBirationalMorphism ha'
  haveI : IsReduced W := isReduced_of_isOpenImmersion (W.ι ≫ a)
  haveI := irreducibleSpace_of_isBirationalMorphism ha'
  haveI := isIntegral_reduction Z'
  set ρ := (Scheme.IdealSheafData.vanishingIdeal ⊤ : Z'.IdealSheafData).subschemeι
  have hρb : IsBirationalMorphism ρ := isBirationalMorphism_reduction W hWd
  obtain ⟨X', h1, h2, h3, p, hp, B', hB', hcrep, F, ιF, hιF, hF, gR, hFstr, hgRp, hgRb, hgRc⟩ :=
    exists_isLogResolution_isSNCStratum_comp_eq_of_isIntegral hB hKX ιZ hZ (ρ ≫ a)
      (by
        obtain ⟨N, i, hi, hia⟩ := ha
        exact ⟨N, ρ ≫ i, inferInstance, by rw [Category.assoc, hia]⟩)
      (isBirationalMorphism_comp hρb ha')
  haveI := isIntegral_of_isSNCStratum ιF hFstr
  exact ⟨X', h1, h2, h3, p, hp, B', hB', hcrep, F, ιF, hιF, hF, gR ≫ ρ, hFstr,
    by haveI := hgRp; infer_instance, isBirationalMorphism_comp hgRb hρb,
    by simpa only [Category.assoc] using hgRc⟩

end MMP.Fourfold
