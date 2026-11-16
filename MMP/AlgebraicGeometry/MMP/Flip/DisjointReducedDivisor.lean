module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.MMP.Flip.NullDivisorTransfer
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Positivity.Kleiman.RhoOneCurveTest
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts

/-!
# A flip whose flipping and flipped curves avoid a reduced divisor is disjoint from it

Let `f : X ⟶ Z ⟵ X⁺ : f⁺` be an `L`-flip (`MMP.Fourfold.IsFlipOf`) of projective normal varieties,
with `X` `ℚ`-factorial, `ρ(X/Z) = dim N¹(X/Z) = 1`, and `K_X + B` negative on the curves contracted
by `f` for an effective klt boundary `B`. Let `G` be a reduced divisor on `X` with strict transform
`G⁺ = (f⁺)⁻¹_* f_* G`. If no flipping curve of `f` lies in `Supp G` and no flipping curve of `f⁺`
lies in `Supp G⁺`, then `Supp G` is disjoint from every curve contracted by `f`.

The proof: a contracted curve `A` meeting a component `G₀` of `G` without lying in it has
`G₀ · A > 0`; with `λ = (G₀ · A)/(-L · A)`, the divisor `G₀ + λ L` is numerically trivial on
the contracted ray, so it is transported across the flip, giving `G₀⁺ · A⁺ < 0` on every flipped
curve `A⁺`, which then lies in `G₀⁺`.

## Main results

* `MMP.Fourfold.IsFlipOf.disjoint_supp_of_isContractedBy`.

## Implementation notes

The non-containment hypotheses are stated for flipping curves (`MMP.Flips.IsFlippingCurve`), the
positive-dimensional components of the fibres of `f` and `f⁺` over closed points; for a small
contraction of a threefold these are exactly the contracted curves. The relative Picard number is
`MMP.Flips.relativePicardNumber`, the dimension of `N¹(X/Z)`. The conclusion is disjointness of
the closure of the generic point of a contracted curve `A` from `Supp G`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.Fourfold

open TopologicalSpace

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/- ### Curves inside flipping curves -/

section Curves

variable {k : Type} [Field k] {X Z : Scheme.{0}}

/-- A point of positive-dimensional closure is not closed: the generic point of a proper curve is
not a closed point. -/
private theorem point_ne_of_isClosed {sX : X ⟶ Spec (.of k)} (A : ProperCurve sX)
    {p : X} (hp : IsClosed ({p} : Set X)) : A.point ≠ p := by
  rintro rfl
  have h1 := (MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq A.point).symm.trans A.dim_eq
  rw [hp.closure_eq] at h1
  have : topologicalKrullDim ({A.point} : Set X) = 0 := topologicalKrullDim_eq_zero_of_subsingleton
  rw [this] at h1
  exact absurd h1 (by decide)

/-- **A proper curve through a closed point of an irreducible closed set, avoiding a closed set.**
-/
private theorem exists_properCurve_of_mem_closure (sX : X ⟶ Spec (.of k)) [IsProper sX]
    [IsLocallyNoetherian X] {η p : X} (hp : IsClosed ({p} : Set X)) (hηp : p ∈ closure {η})
    {T : Set X} (hT : IsClosed T) (hpT : p ∈ T) (hηT : η ∉ T) :
    ∃ A : ProperCurve sX, closure {A.point} ⊆ closure {η} ∧ p ∈ closure {A.point} ∧
      A.point ∉ T := by
  obtain ⟨y, hηy, hyp, hyT, hy⟩ := exists_isProperCurve_of_specializes sX
    (specializes_iff_mem_closure.mpr hηp) hp hT hpT hηT
  exact ⟨⟨y, hy⟩, specializes_iff_closure_subset.mp hηy, specializes_iff_mem_closure.mp hyp, hyT⟩

/-- A set containing two distinct points, one specializing to the other, has positive dimension. -/
private theorem topologicalKrullDim_pos_of_specializes {α : Type*} [TopologicalSpace α]
    [T0Space α] {T : Set α} {a b : α} (ha : a ∈ T) (hb : b ∈ T) (hab : a ⤳ b) (hne : a ≠ b) :
    0 < topologicalKrullDim T := by
  let A : IrreducibleCloseds T :=
    ⟨closure {⟨a, ha⟩}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds T :=
    ⟨closure {⟨b, hb⟩}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hsp : (⟨a, ha⟩ : T) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  have hBA : B < A := by
    refine lt_of_le_of_ne ?_ fun h => hne ?_
    · change closure {(⟨b, hb⟩ : T)} ⊆ closure {⟨a, ha⟩}
      exact hsp.closure_subset
    · have hmem : (⟨a, ha⟩ : T) ∈ closure {(⟨b, hb⟩ : T)} := by
        change (⟨a, ha⟩ : T) ∈ (B : Set T)
        rw [h]
        exact subset_closure rfl
      have hba : (⟨b, hb⟩ : T) ⤳ ⟨a, ha⟩ := specializes_iff_mem_closure.mpr hmem
      exact congrArg Subtype.val (hsp.antisymm hba).eq
  exact Order.krullDim_pos_iff.mpr ⟨B, A, hBA⟩

/-- An irreducible subset of a finite union of closed sets containing a maximal member of the
family is that member. -/
private theorem subset_of_isIrreducible_of_maximal {α : Type*} [TopologicalSpace α]
    {S : Set (Set α)} (hSf : S.Finite) (hScl : ∀ s ∈ S, IsClosed s) {F t U : Set α}
    (hFS : F = ⋃₀ S) (ht : Maximal (· ∈ S) t) (hU : IsIrreducible U) (hUF : U ⊆ F)
    (htU : t ⊆ U) : U ⊆ t := by
  obtain ⟨s, hs, hUs⟩ := (isIrreducible_iff_sUnion_isClosed.mp hU) hSf.toFinset
    (fun s hs => hScl s (hSf.mem_toFinset.mp hs)) (by rwa [Set.Finite.coe_toFinset, ← hFS])
  exact hUs.trans (ht.2 (hSf.mem_toFinset.mp hs) (htU.trans hUs))

/-- A flipping curve is closed. -/
private theorem isClosed_of_isFlippingCurve {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {f : X ⟶ Z} {C : Set X} (hC : MMP.Flips.IsFlippingCurve k sX sZ f C) : IsClosed C := by
  obtain ⟨-, -, -, -, z, hz, hCmax, -⟩ := hC
  have hF : IsClosed {x : X | f x = z} := hz.preimage f.continuous
  exact closure_subset_iff_isClosed.mp
    (hCmax.2 ⟨hCmax.1.1.closure, closure_minimal hCmax.1.2 hF⟩ subset_closure)

/-- **A contracted curve lies in a flipping curve.** A proper curve `A` contracted by a proper
morphism `f : X ⟶ Z` of varieties lies in an irreducible component, of positive dimension, of the
fibre of `f` over the closed point `f(A)`. -/
private theorem exists_isFlippingCurve_of_isContractedBy {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} [IsLocallyNoetherian X] [CompactSpace X]
    (hXv : MMP.Mori.IsVariety k sX) (hZv : MMP.Mori.IsVariety k sZ) (hcomp : f ≫ sZ = sX)
    [IsProper f] (A : ProperCurve sX) (hA : A.IsContractedBy f) :
    ∃ C : Set X, MMP.Flips.IsFlippingCurve k sX sZ f C ∧ closure {A.point} ⊆ C := by
  have : IsNoetherian X := ⟨⟩
  obtain ⟨c, hcA, hc⟩ := (isClosed_closure (s := ({A.point} : Set X))).exists_closed_singleton
    ⟨A.point, subset_closure rfl⟩
  set z := f c
  have hz : IsClosed ({z} : Set Z) := by simpa using f.isClosedMap _ hc
  have hAz : closure {A.point} ⊆ {x : X | f x = z} := fun x hx => (hA x hx).trans (hA c hcA).symm
  have hFc : IsClosed {x : X | f x = z} := hz.preimage f.continuous
  obtain ⟨S, hSf, hScl, hSirr, hFS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
  obtain ⟨s, hs, hAs⟩ := (isIrreducible_iff_sUnion_isClosed.mp
    (isIrreducible_singleton (x := A.point)).closure) hSf.toFinset
    (fun s hs => hScl s (hSf.mem_toFinset.mp hs))
    (by rwa [Set.Finite.coe_toFinset, ← hFS])
  obtain ⟨t', hst', ht'max⟩ := hSf.exists_le_maximal (hSf.mem_toFinset.mp hs)
  have ht'S : t' ∈ S := ht'max.prop
  have ht'F : t' ⊆ {x : X | f x = z} := hFS ▸ Set.subset_sUnion_of_mem ht'S
  have hAt' : closure {A.point} ⊆ t' := hAs.trans hst'
  refine ⟨t', ⟨hXv, hZv, hcomp, inferInstance, z, hz, ⟨⟨hSirr t' ht'S, ht'F⟩, ?_⟩,
    topologicalKrullDim_pos_of_specializes (hAt' (subset_closure rfl)) (hAt' hcA)
      (specializes_iff_mem_closure.mpr hcA) (point_ne_of_isClosed A hc)⟩, hAt'⟩
  rintro U ⟨hUirr, hUF⟩ htU
  exact subset_of_isIrreducible_of_maximal hSf hScl hFS ht'max hUirr hUF htU

/-- **A flipping curve all of whose curves lie in a closed set lies in it.** If every proper
curve contracted by `f` has its generic point in the closed set `T`, then every flipping curve of
`f` lies in `T`: otherwise a proper curve through a closed point of the flipping curve, inside it
and not inside `T`, would be a contracted curve outside `T`. -/
private theorem subset_of_isFlippingCurve {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {f : X ⟶ Z} [IsProper sX] [IsLocallyNoetherian X] [CompactSpace X] {C : Set X}
    (hC : MMP.Flips.IsFlippingCurve k sX sZ f C) {T : Set X} (hT : IsClosed T)
    (h : ∀ B : ProperCurve sX, B.IsContractedBy f → B.point ∈ T) : C ⊆ T := by
  have hCcl := isClosed_of_isFlippingCurve hC
  obtain ⟨-, -, -, -, z, -, hCmax, hdim⟩ := hC
  have hgen := hCmax.1.1.isGenericPoint_genericPoint_closure
  rw [hCcl.closure_eq] at hgen
  set η := hCmax.1.1.genericPoint
  have hηC : closure {η} = C := hgen
  by_contra hCT
  have hηT : η ∉ T := fun hη => hCT (hηC ▸ closure_minimal (Set.singleton_subset_iff.mpr hη) hT)
  obtain ⟨p, hpC, hp⟩ := hCcl.exists_closed_singleton hCmax.1.1.nonempty
  have hηp : η ≠ p := by
    rintro rfl
    rw [hp.closure_eq] at hηC
    rw [← hηC] at hdim
    have : topologicalKrullDim ({η} : Set X) = 0 := topologicalKrullDim_eq_zero_of_subsingleton
    rw [this] at hdim
    exact lt_irrefl _ hdim
  obtain ⟨B, hBC, -, hBT⟩ := exists_properCurve_of_mem_closure sX hp (hηC ▸ hpC) (hT.union hp)
    (Or.inr rfl) (fun h => h.elim hηT hηp)
  refine hBT (Or.inl (h B fun x hx => ?_))
  rw [hηC] at hBC
  exact (hCmax.1.2 (hBC hx)).trans (hCmax.1.2 (hBC (subset_closure rfl))).symm

/-- **A proper birational morphism without flipping curves is an isomorphism.** Every fibre over a
closed point is finite, since an infinite fibre has an irreducible component of positive
dimension; so the open finite-fibre locus contains every closed point and is everything, and the
morphism is an isomorphism over it. -/
private theorem isIso_of_forall_not_isFlippingCurve {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} [IsIntegral X] [IsIntegral Z] [IsNormal Z]
    [IsLocallyNoetherian X] [CompactSpace X] [CompactSpace Z]
    (hXv : MMP.Mori.IsVariety k sX) (hZv : MMP.Mori.IsVariety k sZ) (hcomp : f ≫ sZ = sX)
    [IsProper f] (hb : IsBirational f) (h : ∀ C, ¬ MMP.Flips.IsFlippingCurve k sX sZ f C) :
    IsIso f := by
  have : IsNoetherian X := ⟨⟩
  obtain ⟨hU, hI⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1
    inferInstance
  have hall : MMP.Resolution.Bridges.finiteFibreLocus f = Set.univ := by
    by_contra hne
    obtain ⟨z, hz, hzc⟩ := hU.isClosed_compl.exists_closed_singleton
      (Set.nonempty_compl.mpr hne)
    have hinf : (f ⁻¹' {z}).Infinite := hz
    have hFc : IsClosed (f ⁻¹' {z}) := hzc.preimage f.continuous
    obtain ⟨S, hSf, hScl, hSirr, hFS⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
    obtain ⟨t, htS, htinf⟩ : ∃ t ∈ S, t.Infinite := by
      by_contra! hfin
      exact hinf (hFS ▸ hSf.sUnion fun t ht => hfin t ht)
    obtain ⟨t', htt', ht'max⟩ := hSf.exists_le_maximal htS
    have ht'S : t' ∈ S := ht'max.prop
    have ha := (hScl t' ht'S).closure_eq ▸ (hSirr t' ht'S).isGenericPoint_genericPoint_closure
    obtain ⟨c, hct, hca⟩ :=
      (htinf.diff (Set.finite_singleton (hSirr t' ht'S).genericPoint)).nonempty
    have ht'F : t' ⊆ f ⁻¹' {z} := hFS ▸ Set.subset_sUnion_of_mem ht'S
    refine h t' ⟨hXv, hZv, hcomp, inferInstance, z, hzc,
      ⟨⟨hSirr t' ht'S, ht'F⟩, ?_⟩,
      topologicalKrullDim_pos_of_specializes ha.mem (htt' hct) (ha.specializes (htt' hct))
        fun h => hca h.symm⟩
    rintro U ⟨hUirr, hUF⟩ htU
    exact subset_of_isIrreducible_of_maximal hSf hScl hFS ht'max hUirr hUF htU
  have hI' : IsIso (f ∣_ ⊤) :=
    (show (⟨_, hU⟩ : Z.Opens) = ⊤ from TopologicalSpace.Opens.ext hall) ▸ hI
  exact (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit => (⊤ : Z.Opens)) (by simp)).mpr fun _ => hI'

end Curves

/- ### Intersection numbers with proper curves -/

section Intersection

variable {k : Type} [Field k] {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]

/-- `((D + q E) · C) = (D · C) + q (E · C)`. -/
private theorem intersectionNumber_add_smul {D E : QDivisor X} (hD : D.IsQCartier)
    (hE : E.IsQCartier) (q : ℚ) (C : ProperCurve sX) :
    (D + q • E).intersectionNumber k sX C.ι C.dim_le
        (hD.add (MMP.Flips.QDivisor.IsQCartier.qsmul hE q)) =
      D.intersectionNumber k sX C.ι C.dim_le hD +
        q * E.intersectionNumber k sX C.ι C.dim_le hE := by
  rw [QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D (q • E) hD
      (MMP.Flips.QDivisor.IsQCartier.qsmul hE q),
    intersectionNumber_smul sX C.ι C.dim_le E hE q]

/-- An effective `ℚ`-Cartier divisor `D` has positive intersection number with a proper curve
meeting `Supp D` but not contained in it. -/
private theorem intersectionNumber_pos_of_mem_closure {D : QDivisor X} (hD : D.IsQCartier)
    (h0 : 0 ≤ D) (C : ProperCurve sX) (hC : C.point ∉ D.supp) {x : X}
    (hx : x ∈ closure {C.point}) (hxD : x ∈ D.supp) :
    0 < D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨hnn, hiff⟩ := intersectionNumber_nonneg_and_eq_zero_iff sX D hD h0 C hC
  exact lt_of_le_of_ne hnn fun h => hiff.mp h.symm x (specializes_iff_mem_closure.mpr hx) hxD

/-- A proper curve on which an effective `ℚ`-Cartier divisor `D` is negative lies in `Supp D`. -/
private theorem point_mem_supp_of_intersectionNumber_neg {D : QDivisor X} (hD : D.IsQCartier)
    (h0 : 0 ≤ D) (C : ProperCurve sX) (h : D.intersectionNumber k sX C.ι C.dim_le hD < 0) :
    C.point ∈ D.supp := by
  by_contra hC
  exact absurd (intersectionNumber_nonneg_and_eq_zero_iff sX D hD h0 C hC).1 (not_le.mpr h)

/-- A principal divisor has intersection number `0` with every proper curve. -/
private theorem intersectionNumber_principalDivisor [CompactSpace X] (ψ : (RationalFunctions X)ˣ)
    (C : ProperCurve sX) :
    (Divisor.toQDivisor (principalDivisor ψ)).intersectionNumber k sX C.ι C.dim_le
      (QDivisor.isQCartier_toQDivisor (Divisor.isCartier_principalDivisor ψ)) = 0 := by
  have hc := Divisor.isCartier_principalDivisor ψ
  have := hc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  have h1 : (principalDivisor ψ).degreeOn k sX C.ι C.dim_le hc =
      (0 : Divisor X).degreeOn k sX C.ι C.dim_le Divisor.isCartier_zero :=
    degreeOn_eq_of_iso k sX C.ι C.dim_le
      (Divisor.linearlyEquivalent_principalDivisor_zero ψ).divisorialSheafIso
  rw [QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le _ hc, h1,
    Divisor.degreeOn_zero' k sX C.ι C.dim_le, Int.cast_zero]

/-- `ℚ`-linearly equivalent `ℚ`-Cartier divisors have the same intersection number with every
proper curve. -/
private theorem intersectionNumber_eq_of_qLinearlyEquivalent [CompactSpace X]
    {D₁ D₂ : QDivisor X} (h : D₁.QLinearlyEquivalent D₂) (h₁ : D₁.IsQCartier)
    (h₂ : D₂.IsQCartier) (C : ProperCurve sX) :
    D₁.intersectionNumber k sX C.ι C.dim_le h₁ = D₂.intersectionNumber k sX C.ι C.dim_le h₂ := by
  obtain ⟨m, hm, ψ, hψ⟩ := h
  have hE := QDivisor.isQCartier_toQDivisor (Divisor.isCartier_principalDivisor ψ)
  have heq : (m : ℚ) • D₁ = (m : ℚ) • D₂ + Divisor.toQDivisor (principalDivisor ψ) := by
    rw [← hψ, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, smul_sub]
    abel
  have key := intersectionNumber_congr sX C.ι C.dim_le (MMP.Flips.QDivisor.IsQCartier.qsmul h₁ m)
    ((MMP.Flips.QDivisor.IsQCartier.qsmul h₂ m).add hE) heq
  rw [intersectionNumber_smul sX C.ι C.dim_le D₁ h₁ m,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le _ _
      (MMP.Flips.QDivisor.IsQCartier.qsmul h₂ m) hE,
    intersectionNumber_smul sX C.ι C.dim_le D₂ h₂ m, intersectionNumber_principalDivisor,
    add_zero] at key
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne') key

end Intersection

/- ### Strict transforms of effective divisors -/

section Transform

variable {X Y X' : Scheme.{0}}

/-- The strict transform `(f⁺)⁻¹_* f_* D` of an effective divisor is effective. -/
private theorem flipTransform_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (f : X ⟶ Y) (fp : X' ⟶ Y) {D : DivisorWithCoeffs R X} (hD : 0 ≤ D) :
    0 ≤ flipTransform f fp D :=
  DivisorWithCoeffs.mapPrimeDivisors_nonneg _ (DivisorWithCoeffs.mapPrimeDivisors_nonneg _ hD)

/-- For effective divisors `D₁ ≤ D₂`, the support of the strict transform of `D₁` lies in that of
the strict transform of `D₂`. -/
private theorem supp_flipTransform_subset (f : X ⟶ Y) (fp : X' ⟶ Y) {D₁ D₂ : Divisor X}
    (h₁ : 0 ≤ D₁) (h₁₂ : D₁ ≤ D₂) :
    ((flipTransform f fp D₁).supp : Set X') ⊆ (flipTransform f fp D₂).supp := by
  intro x hx
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hxE⟩
  have hD : D₂ = D₁ + (D₂ - D₁) := by abel
  have h0 := flipTransform_nonneg f fp (sub_nonneg.mpr h₁₂)
  have h1 := flipTransform_nonneg f fp h₁
  rw [hD, map_add]
  have hpos : 0 < flipTransform f fp D₁ E := lt_of_le_of_ne (h1 E) (Ne.symm hE)
  exact (add_pos_of_pos_of_nonneg hpos (h0 E)).ne'

end Transform

/- ### Signs in relative Picard number one -/

section Sign

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}}
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  {sZ : Z ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (hZ : IsNormalVariety k sZ) {f : X ⟶ Z}
  (hf : MMP.Flips.IsContraction k sZ sX f) (hfp : IsProjective f)
  (hρ : MMP.Flips.relativePicardNumber sX f = 1)

include hX hZ hf hfp hρ

/-- In relative Picard number one, a `ℚ`-Cartier divisor positive on one contracted curve is
positive on all of them. -/
private theorem intersectionNumber_pos_of_pos {C₀ C : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (hC : C.IsContractedBy f) {D : QDivisor X} (hD : D.IsQCartier)
    (h : 0 < D.intersectionNumber k sX C₀.ι C₀.dim_le hD) :
    0 < D.intersectionNumber k sX C.ι C.dim_le hD :=
  (MMP.Flips.isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one sX sZ hX
    hZ f hf hfp hρ C hC D hD).mp
    ((MMP.Flips.isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one sX sZ
      hX hZ f hf hfp hρ C₀ hC₀ D hD).mpr h)

/-- In relative Picard number one, a `ℚ`-Cartier divisor of degree zero on one contracted curve has
degree zero on all of them. -/
private theorem intersectionNumber_eq_zero_of_eq_zero {C₀ C : ProperCurve sX}
    (hC₀ : C₀.IsContractedBy f) (hC : C.IsContractedBy f) {D : QDivisor X} (hD : D.IsQCartier)
    (h : D.intersectionNumber k sX C₀.ι C₀.dim_le hD = 0) :
    D.intersectionNumber k sX C.ι C.dim_le hD = 0 := by
  have hD' : (-D).IsQCartier := by
    simpa using MMP.Flips.QDivisor.IsQCartier.qsmul hD (-1)
  rcases lt_trichotomy (D.intersectionNumber k sX C.ι C.dim_le hD) 0 with hlt | heq | hgt
  · have := intersectionNumber_pos_of_pos hX hZ hf hfp hρ hC hC₀ hD'
      (by rw [QDivisor.intersectionNumber_neg k sX C.ι C.dim_le hD hD']; linarith)
    rw [QDivisor.intersectionNumber_neg k sX C₀.ι C₀.dim_le hD hD'] at this
    linarith
  · exact heq
  · have := intersectionNumber_pos_of_pos hX hZ hf hfp hρ hC hC₀ hD hgt
    linarith

end Sign

/- ### A flip is not an isomorphism -/

section Isomorphism

variable {k : Type} [Field k] {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X']
  [IsNormal X'] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}

/-- A pulled-back `ℚ`-Cartier divisor has degree zero on every curve contracted by the morphism. -/
private theorem intersectionNumber_pullback_eq_zero_of_isContractedBy {V W : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} (hV : MMP.Mori.IsVariety k sV)
    (hW : MMP.Mori.IsVariety k sW) [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {M : QDivisor W}
    (hM : M.IsQCartier)
    (hMu : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ M.supp)
    (C : ProperCurve sV) (hC : C.IsContractedBy u) :
    (QDivisor.pullback (f := u) M hM hMu).intersectionNumber k sV C.ι C.dim_le
      ((QDivisor.isPullback_pullback hM hMu).isQCartier hM) = 0 := by
  haveI := hV
  haveI := hW
  haveI : AlgebraicGeometry.IsCurve k (C.ι ≫ sV) := C.isCurve
  refine MMP.Mori.intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hM
    (QDivisor.isPullback_pullback hM hMu) ⟨u C.point, ?_⟩
  ext w
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp,
    ProperCurve.range_ι, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hC y hy
  · rintro rfl
    exact ⟨C.point, subset_closure rfl, rfl⟩

/-- **A small modification onto an isomorphism transports intersection numbers to zero.** Let
`f : X ⟶ Z` and `f⁺ : X⁺ ⟶ Z` be small morphisms with `f⁺` an isomorphism. If a `ℚ`-Cartier
divisor `D` on `X` has `ℚ`-Cartier strict transform `D⁺ = (f⁺)⁻¹_* f_* D`, then `D` is the
pull-back of `D⁺` along `(f⁺)⁻¹ ∘ f`, since both morphisms are local isomorphisms at the generic
points of prime divisors; so `D` has degree zero on every curve contracted by `f`. -/
private theorem intersectionNumber_eq_zero_of_isIso {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : IsSmallMorphism sX sZ f) (hfp : IsSmallMorphism sX' sZ fp) [IsIso fp] {D : QDivisor X}
    (hD : D.IsQCartier) (hD' : QDivisor.IsQCartier (flipTransform f fp D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    D.intersectionNumber k sX C.ι C.dim_le hD = 0 := by
  haveI : IsProper f := hf.isProper
  haveI : IsProper fp := hfp.isProper
  haveI := hf.isBirationalMorphism.isDominant
  have hZ := hf.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set g : X ⟶ X' := f ≫ inv fp with hgdef
  have hgen : ∀ W : irreducibleComponents X,
      g (componentGenericPoint X W) ∉ (flipTransform f fp D).supp := fun W => by
    rw [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact genericPoint_notMem_supp _
  have hg : g ≫ sX' = sX := by
    rw [← hfp.comp_eq, hgdef, Category.assoc, IsIso.inv_hom_id_assoc, hf.comp_eq]
  have hgC : C.IsContractedBy g := fun y hy => by
    simp only [hgdef, Scheme.Hom.comp_apply, hC y hy]
  -- `D` is the pull-back of its strict transform along `g`
  have hpb : QDivisor.pullback (f := g) (flipTransform f fp D) hD' hgen = D := by
    ext E
    obtain ⟨P', hP'gen, -⟩ :=
      exists_eq_genericPoint_flipTransform_apply.{0, 0} hfp.isBirationalMorphism hf
        E (inv fp (f E.genericPoint)) (by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl)
    have hgE : g E.genericPoint = P'.genericPoint := by
      rw [hgdef, Scheme.Hom.comp_apply, hP'gen]
    obtain ⟨Pm, hEPm, hfl⟩ := exists_eq_genericPoint_flipTransform_apply hf.isBirationalMorphism hfp
      P' E.genericPoint (by rw [← hP'gen, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl)
    have hPm : Pm = E := (AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEPm).symm
    obtain ⟨-, Q, -, -, hEQ⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ
      hfp.isBirationalMorphism hf E
    have h1 : IsIso (f.stalkMap E.genericPoint) :=
      isIso_stalkMap_of_map_eq_genericPoint hf.isBirationalMorphism
        (map_genericPoint_eq_of_image_eq E Q hEQ)
    have h2 : IsIso ((inv fp).stalkMap (f E.genericPoint)) :=
      ((isIso_iff_isIso_stalkMap (inv fp)).mp inferInstance).2 _
    haveI : IsIso (g.stalkMap E.genericPoint) := by
      rw [hgdef, Scheme.Hom.stalkMap_comp]
      exact IsIso.comp_isIso' h2 h1
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
      coeff_eq_of_isPullback_qDivisor E P' hgE hD' (QDivisor.isPullback_pullback hD' hgen),
      hfl D, hPm]
  exact (intersectionNumber_congr sX C.ι C.dim_le _ _ hpb.symm).trans
    (intersectionNumber_pullback_eq_zero_of_isContractedBy hf.isNormalVariety_source.1
      hfp.isNormalVariety_source.1 hg hD' hgen C hgC)

end Isomorphism

/- ### A contracted curve meeting an effective divisor -/

section Meeting

variable {k : Type} [Field k] {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsProper sX] {sZ : Z ⟶ Spec (.of k)}
  {f : X ⟶ Z} [IsProper f]

/-- **A divisor containing no flipping curve is positive on a contracted curve it meets.** Let
`D` be an effective `ℚ`-Cartier divisor whose support contains no flipping curve of `f`. If a
curve `A` contracted by `f` meets `Supp D`, then the flipping curve `C ⊇ A` is not contained in
`Supp D`, and a proper curve `A' ⊆ C` through a closed point of `A ∩ Supp D` and not contained in
`Supp D` has `D · A' > 0`. -/
private theorem exists_isContractedBy_intersectionNumber_pos (hXv : MMP.Mori.IsVariety k sX)
    (hZv : MMP.Mori.IsVariety k sZ) (hcomp : f ≫ sZ = sX) {D : QDivisor X} (hD : D.IsQCartier)
    (h0 : 0 ≤ D) (hDf : ∀ C : Set X, MMP.Flips.IsFlippingCurve k sX sZ f C → ¬ C ⊆ D.supp)
    (A : ProperCurve sX) (hA : A.IsContractedBy f) {x : X} (hxA : x ∈ closure {A.point})
    (hxD : x ∈ D.supp) :
    ∃ A' : ProperCurve sX, A'.IsContractedBy f ∧
      0 < D.intersectionNumber k sX A'.ι A'.dim_le hD := by
  obtain ⟨C, hCf, hAC⟩ := exists_isFlippingCurve_of_isContractedBy hXv hZv hcomp A hA
  have hCcl := isClosed_of_isFlippingCurve hCf
  obtain ⟨-, -, -, -, z, -, hCmax, -⟩ := id hCf
  have hηC : closure {hCmax.1.1.genericPoint} = C := by
    have := hCmax.1.1.isGenericPoint_genericPoint_closure
    rwa [hCcl.closure_eq] at this
  have hηD : hCmax.1.1.genericPoint ∉ D.supp := fun h => hDf C hCf
    (hηC ▸ closure_minimal (Set.singleton_subset_iff.mpr h) D.supp.isClosed)
  obtain ⟨p, ⟨hpA, hpD⟩, hp⟩ := (isClosed_closure.inter D.supp.isClosed).exists_closed_singleton
    ⟨x, hxA, hxD⟩
  obtain ⟨A', hA'C, hpA', hA'D⟩ :=
    exists_properCurve_of_mem_closure sX hp (by rw [hηC]; exact hAC hpA) D.supp.isClosed hpD hηD
  rw [hηC] at hA'C
  exact ⟨A', fun y hy => (hCmax.1.2 (hA'C hy)).trans (hCmax.1.2 (hA'C (subset_closure rfl))).symm,
    intersectionNumber_pos_of_mem_closure hD h0 A' hA'D hpA' hpD⟩

end Meeting

/- ### Transport of signs across the flip -/

section Flip

variable {k : Type} [Field k] {X Z X' : Scheme.{0}}
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
  {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
  {L : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z} (hflip : IsFlipOf sX sZ sX' L f fp)

include hflip

/-- The flipping divisor `L` is negative on every curve contracted by `f`. -/
private theorem intersectionNumber_neg_of_isFlipOf [QuasiCompact sX] (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : L.intersectionNumber k sX C.ι C.dim_le hflip.isQCartier < 0 := by
  have hLn : (-L).IsQCartier := by
    simpa using MMP.Flips.QDivisor.IsQCartier.qsmul hflip.isQCartier (-1)
  have := Oai4C1.TwoEnds.intersectionNumber_pos_of_hasRelativelyAmpleMultiple _ hLn
    hflip.hasRelativelyAmpleMultiple C hC
  rw [QDivisor.intersectionNumber_neg k sX C.ι C.dim_le hflip.isQCartier hLn] at this
  linarith

/-- **A flip has a flipped curve.** If `f` contracts some curve, then `f⁺` has a flipping curve:
otherwise `f⁺` is an isomorphism, and `L` would have degree zero on the curves contracted by `f`,
on which it is negative. -/
private theorem exists_isFlippingCurve_flip [QuasiCompact sX] (A : ProperCurve sX)
    (hA : A.IsContractedBy f) : ∃ C, MMP.Flips.IsFlippingCurve k sX' sZ fp C := by
  have hsp := hflip.isSmallMorphism_flip
  have hZn := hflip.isContraction.isNormalVariety_target
  haveI : IsIntegral X' := hsp.isNormalVariety_source.1.toIsIntegral
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsProper fp := hsp.isProper
  by_contra! h
  haveI : IsIso fp := isIso_of_forall_not_isFlippingCurve hsp.isNormalVariety_source.1 hZn.1
    hsp.comp_eq
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hsp.isBirationalMorphism) h
  have := intersectionNumber_eq_zero_of_isIso hflip.isSmallMorphism hsp hflip.isQCartier
    hflip.isQCartier_flip A hA
  linarith [intersectionNumber_neg_of_isFlipOf hflip A hA]

/-- **Positivity on a flipping curve turns into negativity on the flipped curves.** In relative
Picard number one, a `ℚ`-Cartier divisor `D` positive on one curve contracted by `f` has a
`ℚ`-Cartier strict transform `D⁺`, negative on every curve contracted by `f⁺`. With
`μ = (D · A') / (-L · A') > 0`, the divisor `D + μ L` has degree zero on `A'`, hence on every curve
contracted by `f`; the null-divisor transfer makes `(D + μ L)⁺` `ℚ`-linearly equivalent to a
pull-back from `Z`, so of degree zero on the curves contracted by `f⁺`, and
`D⁺ = (D + μ L)⁺ - μ L⁺` is negative on them, `L⁺` being `f⁺`-ample. -/
private theorem exists_isQCartier_flipTransform_intersectionNumber_neg [QuasiCompact sX]
    [QuasiCompact sX'] [IsAlgClosed k] [CharZero k]
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hZ : MMP.Mori.IsProjectiveVariety k sZ)
    (hQ : IsQFactorial sX) (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hB : IsKltPair sX B)
    (hKB : ∃ h : (Divisor.toQDivisor K + B).IsQCartier, ∀ A : ProperCurve sX,
      A.IsContractedBy f →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B) h
          (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    {D : QDivisor X} (hD : D.IsQCartier) {A' : ProperCurve sX} (hA' : A'.IsContractedBy f)
    (hDA' : 0 < D.intersectionNumber k sX A'.ι A'.dim_le hD) :
    ∃ hD' : QDivisor.IsQCartier (flipTransform f fp D), ∀ C : ProperCurve sX',
      C.IsContractedBy fp → QDivisor.intersectionNumber k sX' C.ι C.dim_le _ hD' < 0 := by
  have hXn := hflip.isContraction.isNormalVariety_source
  have hZn := hflip.isContraction.isNormalVariety_target
  have hsp := hflip.isSmallMorphism_flip
  have hL := hflip.isQCartier
  have hL' := hflip.isQCartier_flip
  have hfproj := hflip.isContraction.isProjectiveMorphism.isProjective
  haveI : IsProper f := hfproj.isProper
  have hLA' := intersectionNumber_neg_of_isFlipOf hflip A' hA'
  -- `P = D + μ L` is numerically trivial over `Z`
  set μ : ℚ := D.intersectionNumber k sX A'.ι A'.dim_le hD /
    -L.intersectionNumber k sX A'.ι A'.dim_le hL with hμ
  have hμpos : 0 < μ := div_pos hDA' (neg_pos.mpr hLA')
  have hP := hD.add (MMP.Flips.QDivisor.IsQCartier.qsmul hL μ)
  have hPA' : (D + μ • L).intersectionNumber k sX A'.ι A'.dim_le hP = 0 := by
    rw [intersectionNumber_add_smul hD hL μ A', hμ, div_neg, neg_mul, div_mul_cancel₀ _ hLA'.ne]
    ring
  -- transfer across the flip: `P⁺ ∼_ℚ (f⁺)^* M`
  obtain ⟨hPq, M, hM, -, hfpM, -, hlin⟩ :=
    IsFlipOf.exists_qLinearlyEquivalent_pullback_of_curveForm_eq_zero hflip hX hZ hQ hρ hK hB hKB
      hP fun C hC => by
        rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX,
          intersectionNumber_eq_zero_of_eq_zero hXn hZn
            ⟨hZn.1, hXn.1, hflip.isContraction.comp_eq, inferInstance,
              hflip.isContraction.isIso_app⟩ hfproj hρ hA' hC hP hPA',
          Rat.cast_zero]
  -- `D⁺ = P⁺ - μ L⁺`
  have heq : flipTransform f fp D = flipTransform f fp (D + μ • L) +
      (-μ) • flipTransform f fp L := by
    rw [map_add, map_rat_smul, neg_smul, add_neg_cancel_right]
  have hD'' := hPq.add (MMP.Flips.QDivisor.IsQCartier.qsmul hL' (-μ))
  refine ⟨heq ▸ hD'', fun C hC => ?_⟩
  rw [intersectionNumber_congr sX' C.ι C.dim_le _ hD'' heq,
    intersectionNumber_add_smul hPq hL' (-μ) C,
    intersectionNumber_eq_of_qLinearlyEquivalent hlin hPq
      ((QDivisor.isPullback_pullback hM hfpM).isQCartier hM) C,
    intersectionNumber_pullback_eq_zero_of_isContractedBy hsp.isNormalVariety_source.1 hZn.1
      hsp.comp_eq hM hfpM C hC]
  have := Oai4C1.TwoEnds.intersectionNumber_pos_of_hasRelativelyAmpleMultiple _ hL'
    hflip.hasRelativelyAmpleMultiple_flip C hC
  nlinarith

end Flip

/-- A reduced effective divisor contains each of its components with multiplicity one. -/
private theorem single_le_of_isReducedEffective {X : Scheme.{0}} {G : Divisor X}
    (hG : MMP.Intersection.IsReducedEffective G) {P : MMP.Mori.PrimeDivisor X}
    (hP : G.coeff P ≠ 0) : Finsupp.single P 1 ≤ G := by
  intro Q
  rcases eq_or_ne Q P with rfl | hQP
  · rw [Finsupp.single_eq_same, ← DivisorWithCoeffs.coeff_apply, (hG Q).resolve_left hP]
  · rw [Finsupp.single_eq_of_ne hQP, ← DivisorWithCoeffs.coeff_apply]
    rcases hG Q with h | h <;> simp [h]

end Helpers

/-- **A flip avoiding a reduced divisor.** In the setting of
`MMP.Fourfold.IsFlipOf.exists_qLinearlyEquivalent_pullback_of_curveForm_eq_zero`, let `G` be a
reduced divisor on `X`. If no flipping curve of `f` lies in `Supp G` and no flipping curve of
`fp` lies in the support of the strict transform `flipTransform f fp G`, then `Supp G` is
disjoint from every curve contracted by `f`. -/
@[mmp "lem_fourfold_projective_flip_disjoint_reduced_divisor"]
public theorem IsFlipOf.disjoint_supp_of_isContractedBy
    {k : Type} [Field k] {X Z X' : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {L : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hflip : IsFlipOf sX sZ sX' L f fp)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hZ : MMP.Mori.IsProjectiveVariety k sZ)
    (hQ : IsQFactorial sX) (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hB : IsKltPair sX B)
    (hKB : ∃ h : (Divisor.toQDivisor K + B).IsQCartier, ∀ A : ProperCurve sX,
      A.IsContractedBy f →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B) h
          (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    {G : Divisor X} (hG : MMP.Intersection.IsReducedEffective G)
    (hGA : ∀ C : Set X, MMP.Flips.IsFlippingCurve k sX sZ f C → ¬ C ⊆ G.supp)
    (hGA' : ∀ C : Set X', MMP.Flips.IsFlippingCurve k sX' sZ fp C →
      ¬ C ⊆ (flipTransform f fp G).supp)
    (A : ProperCurve sX) (hA : A.IsContractedBy f) :
    Disjoint (closure ({A.point} : Set X)) (G.supp : Set X) := by
  -- the setting
  have hXn := hflip.isContraction.isNormalVariety_source
  have hZn := hflip.isContraction.isNormalVariety_target
  have hsp := hflip.isSmallMorphism_flip
  have hX'n := hsp.isNormalVariety_source
  haveI : IsIntegral X' := hX'n.1.toIsIntegral
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'n.1.toQuasiCompact
  haveI : IsAlgClosed k := hB.1.isAlgClosed
  haveI : CharZero k := hB.1.charZero
  haveI : IsProper f := hflip.isContraction.isProjectiveMorphism.isProjective.isProper
  haveI : IsProper fp := hsp.isProper
  haveI : IsProper sX := ((MMP.Mori.isProjectiveVariety_iff k sX).mp hX).2.isProjective.isProper
  haveI : IsProper sZ := ((MMP.Mori.isProjectiveVariety_iff k sZ).mp hZ).2.isProjective.isProper
  haveI : IsProper sX' := by rw [← hsp.comp_eq]; infer_instance
  -- a component `G₀` of `G` meeting `A` is positive on some curve `A'` contracted by `f`
  rw [Set.disjoint_iff]
  rintro x ⟨hxA, hxG⟩
  obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxG
  have hG₀0 : (0 : Divisor X) ≤ Finsupp.single P 1 := Finsupp.single_nonneg.mpr zero_le_one
  set D₀ : QDivisor X := Divisor.toQDivisor (Finsupp.single P 1) with hD₀def
  have hD₀ : D₀.IsQCartier := isQCartier_of_isQFactorial sX hQ D₀
  have hD₀0 : 0 ≤ D₀ := fun Q => by
    change (0 : ℚ) ≤ ((Finsupp.single P (1 : ℤ) Q : ℤ) : ℚ)
    exact_mod_cast hG₀0 Q
  have hsuppD₀ : (D₀.supp : Set X) ⊆ G.supp := by
    rw [hD₀def, Divisor.supp_toQDivisor]
    exact (DivisorWithCoeffs.supp_single_le P 1).trans (DivisorWithCoeffs.support_subset_supp hP)
  obtain ⟨A', hA', hD₀A'⟩ := exists_isContractedBy_intersectionNumber_pos
    hXn.1 hZn.1 hflip.isContraction.comp_eq hD₀ hD₀0
    (fun C hC hCD => hGA C hC (hCD.trans hsuppD₀))
    A hA hxA (by
      rw [hD₀def, Divisor.supp_toQDivisor]
      exact DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff_apply]) hxP)
  -- so `G₀⁺` is negative on every curve contracted by `f⁺`, and every flipping curve of `f⁺`
  -- lies in `Supp G₀⁺ ⊆ Supp G⁺`
  obtain ⟨hG₀', hneg⟩ :=
    exists_isQCartier_flipTransform_intersectionNumber_neg hflip hX hZ hQ hρ hK hB hKB hD₀ hA' hD₀A'
  have hsupp' : ((flipTransform f fp D₀).supp : Set X') ⊆ (flipTransform f fp G).supp := by
    rw [hD₀def, MMP.Mori.flipTransform_toQDivisor, Divisor.supp_toQDivisor]
    exact supp_flipTransform_subset f fp hG₀0 (single_le_of_isReducedEffective hG hP)
  obtain ⟨C, hC⟩ := exists_isFlippingCurve_flip hflip A' hA'
  exact hGA' C hC ((subset_of_isFlippingCurve hC (flipTransform f fp D₀).supp.isClosed
    fun B' hB' => point_mem_supp_of_intersectionNumber_neg hG₀' (flipTransform_nonneg f fp hD₀0)
      B' (hneg B' hB')).trans hsupp')

end MMP.Fourfold
