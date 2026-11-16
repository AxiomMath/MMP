module

public import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary

/-!
# Discrepancies of blow-ups, crepant boundaries and proper models

This file collects three facts about discrepancies of pairs `(X, Δ)` over a field `k`
(Kollár–Mori, §2.3).

*Blow-ups of smooth varieties.* Let `X` be a smooth variety over a field of characteristic
zero, `Δ = ∑ aᵢ Dᵢ` a `ℚ`-divisor and `Z ⊆ X` an irreducible closed subset of
codimension `c ≥ 2`. If `E` is the component of the exceptional divisor of `Bl_Z X ⟶ X`
dominating `Z`, then `(X, Δ)` is a pair and `a(E, X, Δ) = c - 1 - ∑ aᵢ mult_Z Dᵢ`. Near `η_Z`
the centre is smooth, `E` is the exceptional divisor of a smooth blow-up, its valuation is the
`𝔪_Z`-adic order on `𝒪_{X,Z}`, and a generator of `ω_X` pulls back to a form of order `c - 1`
along `E`; local equations of the prime divisors through `η_Z` and the Hartogs relation then
account for `Δ`.

*Crepant boundaries.* For a proper birational morphism `f : Y ⟶ X` from a normal variety, the
crepant boundary `Δ_Y` of `(X, Δ)` is `f⁻¹_* Δ - ∑_E a(E, X, Δ) E`, the sum over the
`f`-exceptional prime divisors `E` of `Y`, and `f_* Δ_Y = Δ`. Since `f` is an isomorphism over
the points of codimension at most one of `X`, the coefficients are compared one prime divisor at
a time, at points where `f` is a local isomorphism.

*Proper models.* With `f` and `Δ_Y` as above, over an algebraically closed field of
characteristic zero, `discrep(X, Δ) = min {discrep(Y, Δ_Y), inf_E a(E, X, Δ)}`, the infimum over
the `f`-exceptional prime divisors `E` of `Y`. Exceptional divisors over `Y` are exceptional over
`X` with the same discrepancy, and an exceptional divisor over `X` either lives on `Y` as an
exceptional divisor over `Y`, or has the valuation of an `f`-exceptional prime divisor of `Y`.

## Main results

* `MMP.Mori.isDiscrepancy_blowUp`: the discrepancy of the exceptional divisor of a blow-up of a
  smooth variety.
* `MMP.Mori.IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional`: the decomposition of
  `Δ_Y` into the birational transform of `Δ` and its exceptional part, and `f_* Δ_Y = Δ`.
* `MMP.Mori.IsCrepantBoundary.discrep_eq_min`: the discrepancy of `(X, Δ)` computed on `Y`.

## Implementation notes

* `mult_Z Γ` (`MMP.Mori.PrimeDivisor.multiplicityAlong`) is `ℕ∞`-valued; it is finite here, and
  enters the blow-up formula through `ENat.toNat`.
* Since `coeff_E(Δ_Y) = -a(E, X, Δ)` for every prime divisor `E` of `Y`, the sum
  `-∑_E a(E, X, Δ) E` is written as the restriction `Finsupp.filter` of `Δ_Y` to the
  `f`-exceptional prime divisors. The comparison of coefficients needs no perfectness of `k`.
* The inner minimum in `IsCrepantBoundary.discrep_eq_min` is an infimum in `EReal`, written as
  in `MMP.Mori.discrep`, with `sInf ∅ = ⊤`; `K_Y` is any canonical divisor of `Y` of the same
  dimension.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.26, 2.29 and
  the proof of 2.32.
-/

@[expose] public section

universe u

namespace MMP.Mori

section BlowUp

open CategoryTheory TopologicalSpace
open AlgebraicGeometry hiding IsVariety
open scoped WithZero

/-! ### Local algebra at a regular point -/

open scoped Classical in
/-- Local equations of the prime divisors through a point with regular local ring. -/
private theorem exists_localEquation {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {x : X}
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : x ∈ Γ.support) :
    ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
      Γ.idealSheaf.stalkIdeal x = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = Γ then 1 else 0 := by
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hsp : Γ.genericPoint ⤳ x := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  set q := MMP.Intersection.primeOfSpecializes hsp with hq
  have hq1 : q.height = 1 := by
    let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk Γ.genericPoint)
    rw [ringKrullDim_stalk_eq_coheight, Γ.coheight_genericPoint] at e
    exact_mod_cast e.symm
  set I := IdealSheafData.stalk Γ.idealSheaf x with hI
  have hxs : x ∈ Γ.idealSheaf.support := hΓ
  have hIp : I.IsPrime := by
    have := Γ.integral
    obtain ⟨y, hy⟩ : x ∈ Set.range Γ.idealSheaf.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    rw [hI, ← hy, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact RingHom.ker_isPrime _
  have hI0 : I ≠ ⊥ := by
    intro h0
    have := Γ.isDiscreteValuationRing_localRing
    have hmap := MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes Γ.idealSheaf hsp
    rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint, ← hI, h0, Ideal.map_bot] at hmap
    exact IsDiscreteValuationRing.not_a_field _ hmap
  have hIq : I ≤ q :=
    (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes Γ.idealSheaf hsp).mp
      (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Γ)
  obtain ⟨π, hπI, hπ⟩ := hIp.exists_mem_prime_of_ne_bot hI0
  have hqπ : q = Ideal.span {π} := Ideal.eq_span_singleton_of_height_eq_one hq1 (hIq hπI) hπ
  have hIπ : I = Ideal.span {π} :=
    le_antisymm (hqπ ▸ hIq) ((Ideal.span_singleton_le_iff_mem _).mpr hπI)
  refine ⟨π, hπ.ne_zero, by rwa [Scheme.IdealSheafData.stalkIdeal_eq_stalk],
    fun Γ' hΓ' => ?_⟩
  have hsp' : Γ'.genericPoint ⤳ x :=
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ' hΓ'
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp' π]
  have hπK : algebraMap Γ'.localRing X.functionField
      ((X.presheaf.stalkSpecializes hsp').hom π) ≠ 0 := by
    rw [MMP.Mori.algebraMap_stalkSpecializes hsp' π]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
  split_ifs with hΓΓ'
  · subst hΓΓ'
    have := Γ'.isDiscreteValuationRing_localRing
    let := (X.presheaf.stalkSpecializes hsp').hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp'
    have hmax : IsLocalRing.maximalIdeal Γ'.localRing =
        Ideal.span {(X.presheaf.stalkSpecializes hsp').hom π} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (X.presheaf.stalk Γ'.genericPoint),
        hqπ, Ideal.map_span, Set.image_singleton]
      rfl
    have hirr : Irreducible ((X.presheaf.stalkSpecializes hsp').hom π) :=
      IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
        (fun h => by rw [h, map_zero] at hπK; exact hπK rfl) hmax
    rw [Scheme.ord_eq_iff Γ'.coheight_genericPoint hπK]
    have : Ring.KrullDimLE 1 Γ'.localRing :=
      krullDimLE_of_coheight_le Γ'.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hirr
  · refine Γ'.ord_algebraMap_of_isUnit ?_
    by_contra hnu
    have hmem : π ∈ MMP.Intersection.primeOfSpecializes hsp' := by
      change (X.presheaf.stalkSpecializes hsp').hom π ∈ IsLocalRing.maximalIdeal _
      exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hle : q ≤ MMP.Intersection.primeOfSpecializes hsp' := by
      rwa [hqπ, Ideal.span_singleton_le_iff_mem]
    have h1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hsp hsp' hle
    apply hΓΓ'
    by_contra hne
    have hle : Γ'.genericPoint ≤ Γ.genericPoint := h1
    have hlt : Γ'.genericPoint < Γ.genericPoint := lt_of_le_not_ge hle fun h =>
      hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Specializes.antisymm (show Γ'.genericPoint ⤳ Γ.genericPoint from h) h1).eq)
    have h2 := Order.coheight_add_one_le hlt
    rw [Γ.coheight_genericPoint, Γ'.coheight_genericPoint] at h2
    exact absurd h2 (by decide)

/-- The order of `1` at any point vanishes. -/
private theorem ord_one_eq_zero {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) :
    Y.ord 1 y = 0 := by
  have := Scheme.ord_mul (x := y) (one_ne_zero (α := Y.functionField)) one_ne_zero
  rw [mul_one] at this
  omega

open scoped Classical in
/-- **Local equations at a regular point.** At a point `x` with regular local ring there is a
family of nonzero rational functions `p Γ`, one for each prime divisor `Γ`, such that `p Γ` is a
local equation of `Γ` in `𝒪_{X,x}` when `x ∈ Γ`, `p Γ = 1` otherwise, and `ord_Γ' (p Γ) = δ_{ΓΓ'}`
for every prime divisor `Γ'` through `x`. -/
private theorem exists_localEquations {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {x : X}
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ p : MMP.Mori.PrimeDivisor X → X.functionField, (∀ Γ, p Γ ≠ 0) ∧
      (∀ Γ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support →
        X.ord (p Γ) Γ'.genericPoint = if Γ' = Γ then 1 else 0) ∧
      (∀ Γ : MMP.Mori.PrimeDivisor X, x ∉ Γ.support → p Γ = 1) ∧
      ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
        Γ.idealSheaf.stalkIdeal x = Ideal.span {π} ∧ p Γ = algebraMap _ X.functionField π := by
  refine ⟨fun Γ => if h : x ∈ Γ.support then
      algebraMap _ X.functionField (exists_localEquation hreg Γ h).choose else 1,
    fun Γ => ?_, fun Γ Γ' hΓ' => ?_, fun Γ h => dif_neg h, fun Γ h =>
      ⟨_, (exists_localEquation hreg Γ h).choose_spec.1,
        (exists_localEquation hreg Γ h).choose_spec.2.1, dif_pos h⟩⟩
  · dsimp only
    by_cases h : x ∈ Γ.support
    · rw [dif_pos h]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (exists_localEquation hreg Γ h).choose_spec.1)
    · rw [dif_neg h]
      exact one_ne_zero
  · dsimp only
    by_cases h : x ∈ Γ.support
    · rw [dif_pos h]
      exact (exists_localEquation hreg Γ h).choose_spec.2.2 Γ' hΓ'
    · rw [dif_neg h, ord_one_eq_zero, if_neg (by rintro rfl; exact h hΓ')]

/-- Over a perfect field, the smooth points are the points with regular local ring. -/
private theorem mem_smoothLocus_iff_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (y : Y) :
    y ∈ smoothLocus s ↔ IsRegularLocalRing (Y.presheaf.stalk y) := by
  rw [MMP.Mori.mem_smoothLocus_iff, ← InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  exact Set.ext_iff.mp (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k s) y

/-- Over a perfect field, a scheme is smooth when all its local rings are regular. -/
private theorem isSmoothScheme_of_forall_isRegularLocalRing {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (h : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) : IsSmoothScheme s :=
  eq_top_iff.mpr fun y _ => (mem_smoothLocus_iff_isRegularLocalRing s y).mpr (h y)

/-- Over a perfect field, the local rings of a smooth scheme are regular. -/
private theorem isRegularLocalRing_stalk_of_smooth {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] (y : Y) :
    IsRegularLocalRing (Y.presheaf.stalk y) :=
  (mem_smoothLocus_iff_isRegularLocalRing s y).mp <| by
    rw [show smoothLocus s = ⊤ from MMP.Flips.isSmoothScheme_of_smooth s]
    trivial

/-- Regularity of a local ring is read through an open immersion. -/
private theorem isRegularLocalRing_of_isOpenImmersion {P Y : Scheme.{u}} (j : P ⟶ Y)
    [IsOpenImmersion j] (p : P) (h : IsRegularLocalRing (Y.presheaf.stalk (j p))) :
    IsRegularLocalRing (P.presheaf.stalk p) := by
  have : IsIso (j.stalkMap p) := inferInstanceAs (IsIso (j.toLRSHom.stalkMap p))
  exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv

/-- Open immersions preserve the coheight of points. -/
private theorem coheight_apply_of_isOpenImmersion {P Y : Scheme.{u}} (j : P ⟶ Y)
    [IsOpenImmersion j] (p : P) : Order.coheight (j p) = Order.coheight p := by
  have : IsIso (j.stalkMap p) := inferInstanceAs (IsIso (j.toLRSHom.stalkMap p))
  have h1 := ringKrullDim_stalk_eq_coheight (j p)
  have h2 := ringKrullDim_stalk_eq_coheight p
  rw [ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv] at h1
  exact_mod_cast h1.symm.trans h2

/-- **A neighbourhood of `η_Z` in which `Z` is smooth.** If `X` is a variety over a perfect
field, `Z ⊆ X` an irreducible closed subset with generic point `x` and `𝒪_{X,x}` regular, there
is an open `U ∋ x` such that `U` and `Z ∩ U` (with the inverse image of the reduced structure of
`Z`) are smooth over `k`, and `Z ∩ U` has generic point `x` and codimension `coheight x`. -/
private theorem exists_smoothBlowup {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (V : IrreducibleCloseds X) (x : X)
    (hx : x = V.isIrreducible.genericPoint)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (_ : MMP.Resolution.IsSmoothBlowup (U.ι ≫ sX)
        ((Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds X)).comap U.ι))
      (hirr : IsIrreducible (((Scheme.IdealSheafData.vanishingIdeal
        (⟨V, V.isClosed⟩ : Closeds X)).comap U.ι).support : Set U)),
      U.ι hirr.genericPoint = x ∧
        codimension (⟨_, hirr, ((Scheme.IdealSheafData.vanishingIdeal
          (⟨V, V.isClosed⟩ : Closeds X)).comap U.ι).support.isClosed⟩ : IrreducibleCloseds U) =
          Order.coheight x := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds X) with hZ
  have hZsupp : (Z.support : Set X) = V := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsIntegral Z.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ V.isIrreducible
  set ζ := genericPoint Z.subscheme with hζ
  have hζx : Z.subschemeι ζ = x := by
    have h1 : IsGenericPoint (Z.subschemeι ζ) (V : Set X) := by
      change closure _ = _
      rw [MMP.Resolution.closure_subschemeι_genericPoint, hZsupp]
    have h2 : IsGenericPoint V.isIrreducible.genericPoint (V : Set X) := by
      have := V.isIrreducible.isGenericPoint_genericPoint_closure
      rwa [V.isClosed.closure_eq] at this
    rw [hx]; exact h1.eq h2
  set S := smoothLocus (Z.subschemeι ≫ sX) with hS
  have hζreg : IsRegularLocalRing Z.subscheme.functionField := inferInstance
  have hζS : ζ ∈ S := (mem_smoothLocus_iff_isRegularLocalRing _ ζ).mpr hζreg
  set T : Set X := Z.subschemeι '' (S : Set Z.subscheme)ᶜ with hT
  have hTc : IsClosed T :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ S.isOpen.isClosed_compl
  have hxT : x ∉ T := by
    rintro ⟨z, hz, hzx⟩
    rw [← hζx] at hzx
    exact hz (Z.subschemeι.isClosedEmbedding.injective hzx ▸ hζS)
  set R := smoothLocus sX with hR
  have hxR : x ∈ R := (mem_smoothLocus_iff_isRegularLocalRing sX x).mpr hreg
  set U : X.Opens := R ⊓ ⟨Tᶜ, hTc.isOpen_compl⟩ with hU
  have hxU : x ∈ U := ⟨hxR, hxT⟩
  set I := Z.comap U.ι with hI
  have hIsupp : (I.support : Set U) = U.ι ⁻¹' V := by
    rw [hI, Scheme.IdealSheafData.support_comap]
    change U.ι ⁻¹' (Z.support : Set X) = _
    rw [hZsupp]
  have hUsm : IsSmoothScheme (U.ι ≫ sX) :=
    isSmoothScheme_of_forall_isRegularLocalRing _ fun u =>
      isRegularLocalRing_of_isOpenImmersion U.ι u
        ((mem_smoothLocus_iff_isRegularLocalRing sX _).mp u.2.1)
  have e : I.subschemeι ≫ U.ι = (Z.comapIso U.ι).hom ≫
      Limits.pullback.snd U.ι Z.subschemeι ≫ Z.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition]
  have hIsm : IsSmoothScheme (I.subschemeι ≫ U.ι ≫ sX) := by
    refine isSmoothScheme_of_forall_isRegularLocalRing _ fun y => ?_
    set j := (Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι with hj
    have hjy : Z.subschemeι (j y) = U.ι (I.subschemeι y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hj, Category.assoc, ← e]
    refine isRegularLocalRing_of_isOpenImmersion j y
      ((mem_smoothLocus_iff_isRegularLocalRing (Z.subschemeι ≫ sX) _).mp ?_)
    by_contra hns
    exact (I.subschemeι y).2.2 ⟨j y, hns, hjy⟩
  have hxgen : IsGenericPoint x (V : Set X) := by
    have := V.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [V.isClosed.closure_eq, ← hx] at this
  let xU : U.toScheme := ⟨x, hxU⟩
  have hxU' : U.ι xU = x := rfl
  have hpre' : IsGenericPoint xU (I.support : Set U.toScheme) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, hxU', hxgen.specializes_iff_mem]
    change _ ↔ y ∈ (I.support : Set U.toScheme)
    rw [hIsupp]
    rfl
  have hirr : IsIrreducible (I.support : Set U.toScheme) := hpre'.isIrreducible
  have hgen : hirr.genericPoint = xU := by
    have h1 := hirr.isGenericPoint_genericPoint_closure
    rw [I.support.isClosed.closure_eq] at h1
    exact h1.eq hpre'
  refine ⟨U, hxU, ⟨hUsm, hIsm⟩, hirr, by rw [hgen]; rfl, ?_⟩
  have hcl : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U.toScheme) =
      IrreducibleCloseds.closureSingleton xU := by
    ext1
    exact hpre'.symm
  rw [hcl, MMP.Flips.codimension_closureSingleton]
  exact coheight_apply_of_isOpenImmersion U.ι xU |>.symm

/-! ### Forms and function fields -/

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- Pulling a form back along `a : A ⟶ X` and then along `c : Z ⟶ A` is pulling it back along
`c ≫ a`, when both induce isomorphisms of function fields. -/
private theorem ordForm_pullback_pullback {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {A Z : Scheme.{u}} [IsIntegral A] [IsIntegral Z] [IsLocallyNoetherian Z]
    (a : A ⟶ X) (c : Z ⟶ A) [IsDominant a] [IsDominant c] [LocallyOfFiniteType (a ≫ sX)]
    [IsDominant (c ≫ a)]
    (hbija : Function.Bijective (functionFieldMap a))
    (hbijc : Function.Bijective (functionFieldMap c)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (E : MMP.Mori.PrimeDivisor Z) {m : ℤ} (τ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms (a ≫ sX) c (pullbackRationalPluriForms sX a τ)) =
      E.ordForm (pullbackRationalPluriForms sX (c ≫ a) τ) := by
  refine congrArg E.ordForm ?_
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (a ≫ sX)
  let := functionFieldAlgebra (c ≫ a ≫ sX)
  let := functionFieldMapAlgebra a
  let := functionFieldMapAlgebra c
  let := functionFieldMapAlgebra (c ≫ a)
  have := isScalarTower_functionFieldMap sX a
  have := isScalarTower_functionFieldMap (a ≫ sX) c
  have : IsScalarTower k X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (c ≫ a)
  have : IsScalarTower X.functionField A.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply c a x).symm
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX a hbija hd
  have hdA : (Algebra.trdeg k A.functionField).toNat = d := by
    rwa [← trdeg_functionField_eq_of_bijective sX a hbija]
  obtain ⟨ω₁, hω₁⟩ := exists_isPullbackGenerator_of_bijective (a ≫ sX) c hbijc hdA
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω
    (MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₁ hω.2.1 hω.2.2) τ

/-- Membership in powers of the maximal ideal is read through an isomorphism of local rings. -/
private theorem mem_maximalIdeal_pow_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (a : R) :
    e a ∈ IsLocalRing.maximalIdeal S ^ n ↔ a ∈ IsLocalRing.maximalIdeal R ^ n := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨b, hb, hba⟩ => e.injective hba ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) :
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

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
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

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] :
    IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-! ### The divisor `E` near the generic point of `Z` -/

set_option backward.isDefEq.respectTransparency false in
/-- **`E` is the exceptional divisor of the smooth blow-up of `Z ∩ U`.** If `U ∋ η_Z` is an open
of `X` on which `Z ∩ U` is a smooth blow-up centre, then the divisor `D` over `X` (on an open of
`Bl_Z X`, dominating `Z`) and the exceptional divisor of `Bl_{Z ∩ U} U ⟶ U ⟶ X` have the same
valuation: `Bl_{Z ∩ U} U` is the preimage of `U` in `Bl_Z X`, and `η_E` is a point of
coheight one over `η_Z` there, hence the generic point of the exceptional divisor. -/
private theorem valuation_eq_smoothBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (Z : IrreducibleCloseds X) (I : X.IdealSheafData) (hIZ : (I.support : Set X) = Z)
    (D : DivisorOver k sX) (j : D.Y ⟶ Stacks.Blowup.blowUp I) [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = Z.isIrreducible.genericPoint)
    (U : X.Opens) (hxU : Z.isIrreducible.genericPoint ∈ U)
    (hsb : MMP.Resolution.IsSmoothBlowup (U.ι ≫ sX) (I.comap U.ι))
    (hirr : IsIrreducible ((I.comap U.ι).support : Set U))
    (hc1 : 1 ≤ codimension (⟨_, hirr, (I.comap U.ι).support.isClosed⟩ : IrreducibleCloseds U))
    (hnv : IsNormalVariety k ((blowUpToBase (I.comap U.ι) ≫ U.ι) ≫ sX))
    (hbir : IsBirationalMorphism (blowUpToBase (I.comap U.ι) ≫ U.ι)) :
    D.valuation = (⟨_, _, hnv, hbir,
      MMP.Resolution.exceptionalPrimeDivisor (U.ι ≫ sX) _ hsb hirr hc1⟩ :
        DivisorOver k sX).valuation := by
  set J := I.comap U.ι with hJ
  set E' := MMP.Resolution.exceptionalPrimeDivisor (U.ι ≫ sX) J hsb hirr hc1 with hE'
  set D' : DivisorOver k sX := ⟨_, _, hnv, hbir, E'⟩ with hD'
  obtain ⟨hmap, H⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap U.ι I
  have : IsOpenImmersion hmap := by rw [← H.isoPullback_hom_snd]; infer_instance
  -- `D.Y` maps to `AlgebraicGeometry.blowUp I` by an open immersion over `X`
  set ψ : D.Y ⟶ AlgebraicGeometry.blowUp I := j ≫ (AlgebraicGeometry.blowUpIso I).inv with hψ
  have : IsOpenImmersion ψ := by rw [hψ]; infer_instance
  have hψf : ψ ≫ blowUpToBase I = D.f := by
    have h0 : (AlgebraicGeometry.blowUpIso I).inv ≫ blowUpToBase I =
        Stacks.Blowup.blowUpToBase I := by
      rw [Iso.inv_comp_eq, AlgebraicGeometry.blowUpIso_hom_blowUpToBase]
    rw [hψ, Category.assoc, h0, hj]
  have hrange : Set.range hmap = blowUpToBase I ⁻¹' (U : Set X) := by
    rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr H.isoPullback.hom.surjective, Set.image_univ,
      Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
  set O : D.Y.Opens := ψ ⁻¹ᵁ hmap.opensRange with hO
  have hηO : D.E.genericPoint ∈ O := by
    change ψ D.E.genericPoint ∈ Set.range hmap
    rw [hrange, Set.mem_preimage, ← Scheme.Hom.comp_apply, hψf, hE]
    exact hxU
  have hOr : Set.range (O.ι ≫ ψ) ⊆ Set.range hmap := by
    rintro _ ⟨p, rfl⟩
    exact p.2
  set φ : O.toScheme ⟶ AlgebraicGeometry.blowUp J := IsOpenImmersion.lift hmap (O.ι ≫ ψ) hOr
    with hφ
  have hφfac : φ ≫ hmap = O.ι ≫ ψ := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (φ ≫ hmap) := by rw [hφfac]; infer_instance
  have : IsOpenImmersion φ := IsOpenImmersion.of_comp φ hmap
  set V := φ.opensRange with hV
  set e := φ.isoOpensRange with he
  have heι : e.hom ≫ V.ι = φ := Scheme.Hom.isoOpensRange_hom_ι φ
  -- the image of `η_E` is the generic point of the exceptional divisor
  set y := φ ⟨D.E.genericPoint, hηO⟩ with hy
  have hyZ : U.ι (blowUpToBase J y) = Z.isIrreducible.genericPoint := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply φ hmap,
      hφfac, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψf]
    exact hE
  have hyE : y ∈ E'.support := by
    have h1 : (E'.support : Set (blowUp J)) = blowUpToBase J ⁻¹' (J.support : Set U) := by
      change ((J.comap (blowUpToBase J)).support : Set (blowUp J)) = _
      rw [Scheme.IdealSheafData.support_comap]; rfl
    have h2 : (J.support : Set U) = U.ι ⁻¹' (I.support : Set X) := by
      rw [hJ, Scheme.IdealSheafData.support_comap]; rfl
    rw [h1, Set.mem_preimage, h2, Set.mem_preimage, hyZ, hIZ]
    have := Z.isIrreducible.isGenericPoint_genericPoint_closure
    rw [Z.isClosed.closure_eq] at this
    exact this.mem
  have hycoh : Order.coheight y = 1 := by
    rw [hy, coheight_apply_of_isOpenImmersion φ,
      ← coheight_apply_of_isOpenImmersion O.ι]
    exact MMP.Mori.PrimeDivisor.coheight_genericPoint D.E
  have hyη : y = E'.genericPoint := by
    have hsp : E'.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hyE
    by_contra hne
    have hle : y ≤ E'.genericPoint := hsp
    have hlt : y < E'.genericPoint := lt_of_le_not_ge hle fun h =>
      hne (Specializes.antisymm (show y ⤳ E'.genericPoint from h) hsp).eq
    have h2 := Order.coheight_add_one_le hlt
    rw [hycoh, MMP.Mori.PrimeDivisor.coheight_genericPoint E'] at h2
    exact absurd h2 (by decide)
  have hηV : D'.E.genericPoint ∈ V := by
    change E'.genericPoint ∈ Set.range φ
    exact ⟨⟨D.E.genericPoint, hηO⟩, hyη⟩
  refine MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' O V hηO hηV e ?_ ?_
  · change e.hom ≫ V.ι ≫ blowUpToBase J ≫ U.ι = O.ι ≫ D.f
    rw [← Category.assoc, heι, H.w, ← Category.assoc, hφfac, Category.assoc, hψf]
  · apply Subtype.ext
    change (e.hom ≫ V.ι) _ = _
    rw [heι]
    exact hyη

/-- **The form of order `c - 1` and the valuation of `E`.** There is a rational top form `σ` with
`ord_Γ σ = 0` for every prime divisor `Γ` through `η_Z` and `ord_E(f^*σ) = c - 1`, and the
valuation of `E` on `𝒪_{X,Z}` is the `𝔪_Z`-adic order. Both are computed on the smooth blow-up
`Bl_{Z ∩ U} U` near `η_Z`, whose exceptional divisor has the valuation of `E`. -/
private theorem exists_form_and_valuation {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsVariety k sX) [Smooth sX]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} (hn : topologicalKrullDim X = n)
    (Z : IrreducibleCloseds X) {c : ℕ} (hc : (c : ℕ∞) = codimension Z) (hc2 : 2 ≤ c)
    (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨Z, Z.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = Z.isIrreducible.genericPoint) :
    (∃ σ : RationalPluriForms sX n 1, σ ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor X, Z.isIrreducible.genericPoint ∈ Γ.support →
        Γ.ordForm σ = 0) ∧ D.ordPullback σ = (c : ℤ) - 1) ∧
    ∀ g : X.presheaf.stalk Z.isIrreducible.genericPoint, g ≠ 0 → ∃ M : ℕ,
      IsGreatest {s : ℕ | g ∈ IsLocalRing.maximalIdeal
        (X.presheaf.stalk Z.isIrreducible.genericPoint) ^ s} M ∧
      D.valuation (algebraMap _ X.functionField g) = WithZero.exp (-(M : ℤ)) := by
  classical
  set x := Z.isIrreducible.genericPoint
  have hXn : IsNormalVariety k sX := ⟨hX, inferInstance⟩
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hreg := isRegularLocalRing_stalk_of_smooth sX x
  -- a form generating the top forms near `x`
  obtain ⟨β⟩ := MMP.Positivity.exists_basis_topForms hXn hn
  let ω₀ : RationalPluriForms sX n 1 := (ZTensorPower.basis β 1) ()
  have hω₀ : ω₀ ≠ 0 := (ZTensorPower.basis β 1).ne_zero ()
  let T : Finset (MMP.Mori.PrimeDivisor X) :=
    (finite_ordForm_ne_zero ω₀).toFinset.filter fun Γ => x ∈ Γ.support
  obtain ⟨p, hp0, hpΓ, hp1, hpmem⟩ := exists_localEquations hreg
  let h₀ : X.functionField := ∏ Γ ∈ T, p Γ ^ (-(Γ.ordForm ω₀))
  have hh₀ : h₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun Γ _ => zpow_ne_zero _ (hp0 Γ)
  set σ : RationalPluriForms sX n 1 := h₀ • ω₀ with hσdef
  have hσ0 : σ ≠ 0 := smul_ne_zero hh₀ hω₀
  have hσΓ : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → Γ.ordForm σ = 0 := by
    intro Γ hΓ
    rw [hσdef, Γ.ordForm_smul_of_topologicalKrullDim_eq hn hh₀ hω₀,
      MMP.Threefold.Bridges.ord_prod_zpow _ _ _ hp0]
    simp_rw [hpΓ _ Γ hΓ]
    by_cases hT : Γ ∈ T
    · rw [Finset.sum_eq_single Γ]
      · simp
      · intro Γ' _ hne
        simp [Ne.symm hne]
      · exact fun h => (h hT).elim
    · have h0 : Γ.ordForm ω₀ = 0 := by
        by_contra hne
        exact hT (Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hne, hΓ⟩)
      rw [h0, add_zero]
      refine Finset.sum_eq_zero fun Γ' hΓ' => ?_
      have : Γ ≠ Γ' := fun e => hT (e ▸ hΓ')
      simp [this]
  -- an open neighbourhood `W` of `x` on which `σ` generates
  let F := (finite_ordForm_ne_zero σ).toFinset
  have hFc : IsClosed (⋃ Γ ∈ F, (Γ.support : Set X)) :=
    F.finite_toSet.isClosed_biUnion fun Γ _ => Γ.idealSheaf.support.isClosed
  let W : X.Opens := ⟨_, hFc.isOpen_compl⟩
  have hxW : x ∈ W := by
    change x ∉ ⋃ Γ ∈ F, (Γ.support : Set X)
    simp only [Set.mem_iUnion, not_exists]
    intro Γ hΓF hxΓ
    exact ((Set.Finite.mem_toFinset _).mp hΓF) (hσΓ Γ hxΓ)
  have hgen : GeneratesOn (0 : QDivisor X) 1 W σ := by
    refine ⟨hσ0, fun Γ ⟨y, hyΓ, hyW⟩ => ?_⟩
    have : Γ.ordForm σ = 0 := by
      by_contra hne
      exact hyW (Set.mem_biUnion ((Set.Finite.mem_toFinset _).mpr hne) hyΓ)
    simp [this]
  -- the smooth blow-up of `Z` near `x`
  obtain ⟨U, hxU, hsb, hirr, hgenpt, hcodI⟩ := exists_smoothBlowup hX Z x rfl hreg
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, hxU⟩)
  have hbijU : Function.Bijective (functionFieldMap U.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨⟨x, hxU⟩, trivial⟩
  have hUnv := isNormalVariety_ι hXn U
  have : LocallyOfFiniteType (U.ι ≫ sX) := hUnv.1.toLocallyOfFiniteType
  have hdU : topologicalKrullDim U = n := by
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (U.ι ≫ sX)
    rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX U.ι hbijU, toENat_trdeg_functionField (sX := sX),
      hn]
  -- the pulled-back form generates near the generic point of `Z ∩ U`
  set τU := pullbackRationalPluriForms sX U.ι σ with hτU
  have hτgen : GeneratesOn (0 : QDivisor U) 1 (U.ι ⁻¹ᵁ W) τU := by
    refine ⟨pullbackRationalPluriForms_ne_zero U.ι hbijU hd hσ0, fun Wd hWd => ?_⟩
    have hP : ((OpenWeilRestriction.primeDivisorMap U.ι Wd).support ∩ W).Nonempty := by
      rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff]
      exact (congrArg (· ∈ W) (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι Wd)).mpr
        ((Wd.genericPoint_mem_iff _).2 hWd)
    have e1 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso U.ι hbijU hd Wd
      (OpenWeilRestriction.primeDivisorMap U.ι Wd)
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm σ
    have e2 := hgen.2 _ hP
    rw [hτU, e1]
    simpa using e2
  have hcI : (c : ℕ∞) = codimension (⟨_, hirr, ((Scheme.IdealSheafData.vanishingIdeal
      (⟨Z, Z.isClosed⟩ : Closeds X)).comap U.ι).support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [hcodI, hc, MMP.Flips.codimension_eq_coheight_genericPoint]
  obtain ⟨hordE, hformE⟩ :=
    MMP.Threefold.Resolution.ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback
      (U.ι ≫ sX) hUnv.1 _ hsb hirr hcI hc2 hdU
  obtain ⟨hvarB, hsmB, -, hbirπ, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (U.ι ≫ sX) hUnv.1 hdU _ hsb hirr hcI hc2
  set y := hirr.genericPoint with hy
  have hyW : y ∈ U.ι ⁻¹ᵁ W := by
    change U.ι y ∈ W
    rwa [hgenpt]
  have hform1 := hformE 1 τU ⟨_, hyW, hτgen⟩
  -- the divisor over `X` given by the exceptional divisor of the blow-up
  have hc1 : 1 ≤ codimension (⟨_, hirr, ((Scheme.IdealSheafData.vanishingIdeal
      (⟨Z, Z.isClosed⟩ : Closeds X)).comap U.ι).support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [← hcI]; exact_mod_cast (by omega : 1 ≤ c)
  set I := (Scheme.IdealSheafData.vanishingIdeal (⟨Z, Z.isClosed⟩ : Closeds X)).comap U.ι
    with hI
  set π := blowUpToBase I with hπ
  have : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have : IsDominant π := MMP.Threefold.Resolution.isDominant_blowUpToBase I hirr hc1
  have : LocallyOfFiniteType (π ≫ U.ι ≫ sX) := hvarB.toLocallyOfFiniteType
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ U.ι ≫ sX)
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have : IsNormal (blowUp I) := AlgebraicGeometry.isNormal_of_smooth (π ≫ U.ι ≫ sX)
  have : IsDominant (π ≫ U.ι) := inferInstance
  set Eex := MMP.Resolution.exceptionalPrimeDivisor (U.ι ≫ sX) I hsb hirr hc1 with hEex
  have hnv : IsNormalVariety k ((π ≫ U.ι) ≫ sX) := by
    rw [Category.assoc]; exact ⟨hvarB, inferInstance⟩
  have hbir : IsBirationalMorphism (π ≫ U.ι) := by
    obtain ⟨O, hO, hOi⟩ := exists_isOpenImmersion_of_isBirationalMorphism hbirπ
    have : IsOpenImmersion (O.ι ≫ π ≫ U.ι) := by
      rw [← Category.assoc]; infer_instance
    exact isBirationalMorphism_of_isOpenImmersion (π ≫ U.ι) O hO
  let D' : DivisorOver k sX := ⟨blowUp I, π ≫ U.ι, hnv, hbir, Eex⟩
  have hDD' : D.valuation = D'.valuation :=
    valuation_eq_smoothBlowup Z _ (Scheme.IdealSheafData.coe_support_vanishingIdeal _) D j hj hE
      U hxU hsb hirr hc1 hnv hbir
  refine ⟨⟨σ, hσ0, hσΓ, ?_⟩, ?_⟩
  · rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hXn hn
      (D := D) (D' := D') hDD' σ]
    change MMP.Mori.PrimeDivisor.ordForm Eex (pullbackRationalPluriForms sX (π ≫ U.ι) σ) = _
    rw [← ordForm_pullback_pullback U.ι π hbijU hbirπ.functionFieldMap_bijective hd Eex σ,
      hform1]
    push_cast
    ring
  -- the valuation of `E` on `𝒪_{X,Z}`
  have hval : ∀ g : X.presheaf.stalk (U.ι y), g ≠ 0 → ∃ M : ℕ,
      IsGreatest {s : ℕ | g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι y)) ^ s} M ∧
        D.valuation (algebraMap _ X.functionField g) = WithZero.exp (-(M : ℤ)) := by
    intro g hg
    have : IsIso (U.ι.stalkMap y) := inferInstance
    set e := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv with he
    set g' := e g with hg'
    have hg'0 : g' ≠ 0 := fun h0 => hg (e.injective (h0.trans (map_zero e).symm))
    have hmem : ∀ s : ℕ, (s : ℤ) ≤ (blowUp I).ord (functionFieldMap π
        (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint ↔
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι y)) ^ s := fun s =>
      (hordE g' hg'0 s).trans (mem_maximalIdeal_pow_iff_of_bijective e s g)
    set N := (blowUp I).ord (functionFieldMap π
        (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint with hN
    have hN0 : ((0 : ℕ) : ℤ) ≤ N := (hmem 0).mpr (by simp)
    have hffm : functionFieldMap (π ≫ U.ι) (algebraMap _ X.functionField g) =
        functionFieldMap π (algebraMap _ (U : Scheme).functionField g') := by
      rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Mori.functionFieldMap_algebraMap_stalk]
      rfl
    have hne : functionFieldMap (π ≫ U.ι) (algebraMap _ X.functionField g) ≠ 0 :=
      (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hg))
    refine ⟨N.toNat, ⟨(hmem _).mp (by omega), fun s hs => ?_⟩, ?_⟩
    · have := (hmem s).mpr hs
      omega
    · rw [hDD']
      change MMP.Mori.PrimeDivisor.divisorialValuation Eex (functionFieldMap (π ≫ U.ι) _) = _
      rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord Eex hne, hffm, ← hN]
      congr 2
      push_cast at hN0
      omega
  rwa [hgenpt] at hval

/-- If `η_Z` does not lie on `Γ`, the multiplicity of `Γ` along `Z` is zero. -/
private theorem multiplicityAlong_eq_zero_of_notMem {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (Γ : MMP.Mori.PrimeDivisor X) (Z : IrreducibleCloseds X)
    (h : Z.isIrreducible.genericPoint ∉ Γ.support) : Γ.multiplicityAlong Z = 0 := by
  have htop : Γ.idealSheaf.stalkIdeal Z.isIrreducible.genericPoint = ⊤ := by
    rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
    exact MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support Γ h
  rw [MMP.Mori.PrimeDivisor.multiplicityAlong, htop]
  refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp
  · exfalso
    have : (⊤ : Ideal (X.presheaf.stalk Z.isIrreducible.genericPoint)) ≤
        IsLocalRing.maximalIdeal _ := hs.trans (Ideal.pow_le_self hs0.ne')
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp this)

/-- The order along `E` of an element of `𝒪_{X,Z}` is its `𝔪_Z`-adic order. -/
private theorem ord_eq_of_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : DivisorOver k sX) {z : X}
    {g : X.presheaf.stalk z} (hg : g ≠ 0) {M : ℕ}
    (hv : E.valuation (algebraMap _ X.functionField g) = WithZero.exp (-(M : ℤ))) :
    haveI := E.isIntegral
    haveI := E.isLocallyNoetherian
    haveI := E.isDominant
    E.Y.ord (functionFieldMap E.f (algebraMap _ X.functionField g)) E.E.genericPoint = M := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := E.isNormal
  have hg' : algebraMap _ X.functionField g ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hg)
  change E.E.valuationOver E.f _ = _ at hv
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
    E.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hg')] at hv
  exact neg_inj.mp (WithZero.exp_injective hv)

/-- The order along the dominating exceptional divisor of the pull-back of any local generator
of `𝒪_X(m(K_X + Δ))` near the generic point of `Z`. -/
private theorem ordPullback_eq_of_generatesOn {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsVariety k sX) [Smooth sX]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (Δ : QDivisor X)
    (Z : IrreducibleCloseds X) {c : ℕ} (hc : (c : ℕ∞) = codimension Z) (hc2 : 2 ≤ c)
    (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨Z, Z.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = Z.isIrreducible.genericPoint)
    {m : ℕ} {U : X.Opens} (hU : Z.isIrreducible.genericPoint ∈ U)
    {τ : RationalPluriForms sX n m} (hτ : GeneratesOn Δ m U τ) :
    (m : ℚ) * ((c : ℚ) - 1 - Δ.sum fun Γ a => a * ((Γ.multiplicityAlong Z).toNat : ℚ)) =
      D.ordPullback τ := by
  classical
  set x := Z.isIrreducible.genericPoint
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hXn : IsNormalVariety k sX := ⟨hX, inferInstance⟩
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hreg := isRegularLocalRing_stalk_of_smooth sX x
  obtain ⟨⟨σ, hσ0, hσΓ, hσE⟩, hvx⟩ := exists_form_and_valuation sX hX hn Z hc hc2 D j hj hE
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hXn hn
  -- local equations
  obtain ⟨p, hp0, hpΓ, hp1, hpmem⟩ := exists_localEquations hreg
  have hpE : ∀ Γ : MMP.Mori.PrimeDivisor X,
      D.Y.ord (functionFieldMap D.f (p Γ)) D.E.genericPoint =
      ((Γ.multiplicityAlong Z).toNat : ℤ) := by
    intro Γ
    by_cases h : x ∈ Γ.support
    · obtain ⟨π, hπ0, hπI, hp⟩ := hpmem Γ h
      obtain ⟨M, hM, hvM⟩ := hvx _ hπ0
      rw [hp, ord_eq_of_valuation_eq D hπ0 hvM, Γ.multiplicityAlong_eq_of_stalkIdeal_eq_span Z hπI]
      have : (⨆ (s : ℕ) (_ : π ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ s), (s : ℕ∞)) =
          M :=
        le_antisymm (iSup₂_le fun j hj => by exact_mod_cast hM.2 hj)
          (le_iSup₂ (f := fun (s : ℕ) (_ : π ∈ IsLocalRing.maximalIdeal _ ^ s) => (s : ℕ∞))
            M hM.1)
      rw [this, ENat.toNat_coe]
    · simp [hp1 Γ h, ord_one_eq_zero, multiplicityAlong_eq_zero_of_notMem Γ Z h]
  -- the Hartogs relation
  set cτ := (ZTensorPower.basis β (m : ℤ)).repr τ () with hcτ
  set cσ := (ZTensorPower.basis β 1).repr σ () with hcσ
  have hcτ0 : cτ ≠ 0 := repr_ne_zero_of_ne_zero β hτ.1
  have hcσ0 : cσ ≠ 0 := repr_ne_zero_of_ne_zero β hσ0
  let S := Δ.support
  let G : Option (Option S) → X.functionField := fun j =>
    Option.elim j cτ fun j => Option.elim j cσ fun Γ => p Γ.1
  let w : Option (Option S) → ℝ := fun j =>
    Option.elim j 1 fun j => Option.elim j (-(m : ℝ)) fun Γ => (m : ℝ) * (Δ Γ.1 : ℝ)
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | Γ)
    exacts [hcτ0, hcσ0, hp0 _]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E G hG w
    fun Γ' hΓ' => by
      rw [hE] at hΓ'
      obtain ⟨NΓ, hNΓ⟩ := Γ'.exists_ordForm_eq_ord_add_mul hd β
      have e1 := hNΓ m τ hτ.1
      have e2 := hNΓ 1 σ hσ0
      rw [hσΓ Γ' hΓ'] at e2
      have e3 := hτ.2 Γ' ⟨_, hΓ', hU⟩
      simp only [Fintype.sum_option, G, w, Option.elim]
      have e4 : ∑ Γ : S, (X.ord (p Γ.1) Γ'.genericPoint : ℝ) * ((m : ℝ) * (Δ Γ.1 : ℝ)) =
          (m : ℝ) * (Δ Γ' : ℝ) := by
        simp_rw [hpΓ _ Γ' hΓ']
        by_cases hS : Γ' ∈ S
        · rw [Finset.sum_eq_single ⟨Γ', hS⟩]
          · simp
          · rintro ⟨Γ, hΓS⟩ - hne
            have : Γ' ≠ Γ := fun h => hne (Subtype.ext h.symm)
            simp [this]
          · simp
        · have hB : Δ Γ' = 0 := Finsupp.notMem_support_iff.mp hS
          rw [hB, Rat.cast_zero, mul_zero]
          refine Finset.sum_eq_zero fun Γ _ => ?_
          have : Γ' ≠ Γ.1 := fun h => hS (h ▸ Γ.2)
          simp [this]
      rw [e4]
      have e3' : (Γ'.ordForm τ : ℝ) + (m : ℝ) * (Δ Γ' : ℝ) = 0 := by
        have := congrArg (fun q : ℚ => (q : ℝ)) e3
        push_cast at this
        simpa [DivisorWithCoeffs.coeff_apply] using this
      have e1' : (Γ'.ordForm τ : ℝ) = X.ord cτ Γ'.genericPoint + (m : ℝ) * NΓ := by
        exact_mod_cast e1
      have e2' : (0 : ℝ) = X.ord cσ Γ'.genericPoint + NΓ := by
        exact_mod_cast (by simpa using e2)
      linear_combination e3' - e1' + (m : ℝ) * e2'
  simp only [Fintype.sum_option, G, w, Option.elim] at key
  simp_rw [hpE] at key
  have h1 : ((D.ordPullback τ : ℤ) : ℝ) =
      (D.Y.ord (functionFieldMap D.f cτ) D.E.genericPoint : ℝ) + (m : ℝ) * N := by
    exact_mod_cast hN m τ hτ.1
  have h2 : ((c : ℝ) - 1) = (D.Y.ord (functionFieldMap D.f cσ) D.E.genericPoint : ℝ) + N := by
    have := hN 1 σ hσ0
    rw [hσE, one_mul] at this
    have h := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at h
    linarith
  have hmult : (((Δ.sum fun Γ a => a * ((Γ.multiplicityAlong Z).toNat : ℚ)) : ℚ) : ℝ) =
      ∑ Γ : S, (((Γ.1.multiplicityAlong Z).toNat : ℤ) : ℝ) * (Δ Γ.1 : ℝ) := by
    rw [Finsupp.sum, Rat.cast_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun Γ _ => ?_
    push_cast
    ring
  have e5 : ∑ Γ : S, (((Γ.1.multiplicityAlong Z).toNat : ℤ) : ℝ) * ((m : ℝ) * (Δ Γ.1 : ℝ)) =
      (m : ℝ) * ∑ Γ : S, (((Γ.1.multiplicityAlong Z).toNat : ℤ) : ℝ) * (Δ Γ.1 : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_mul, Rat.cast_sub, Rat.cast_sub, hmult, Rat.cast_intCast, h1]
  push_cast
  linear_combination (m : ℝ) * h2 - key + e5

/-- The characteristic-zero version of the blow-up discrepancy formula; `isDiscrepancy_blowUp`
specializes it. -/
public theorem isDiscrepancy_blowUp_of_charZero {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsVariety k sX) [Smooth sX]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (Δ : QDivisor X)
    (Z : IrreducibleCloseds X) {c : ℕ} (hc : (c : ℕ∞) = codimension Z) (hc2 : 2 ≤ c)
    (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨Z, Z.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = Z.isIrreducible.genericPoint) :
    IsPair sX Δ ∧
      IsDiscrepancy sX n K Δ D
        ((c : ℚ) - 1 - Δ.sum fun Γ a => a * ((Γ.multiplicityAlong Z).toNat : ℚ)) := by
  have hQ : (Divisor.toQDivisor K + Δ).IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme (MMP.Flips.isSmoothScheme_of_smooth sX) _
  have hP : IsPair sX Δ := ⟨⟨hX, inferInstance⟩, n, K, hK, hQ⟩
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, U, hxU, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hP hK hmC
    (D.f D.E.genericPoint)
  exact ⟨hP, ⟨hX, inferInstance⟩, hK, m, hm, hmC, U, hxU, τ, hτ,
    ordPullback_eq_of_generatesOn sX hX hK Δ Z hc hc2 D j hj hE (hE ▸ hxU) hτ⟩

/-- **Discrepancy of the exceptional divisor of a blow-up** (Kollár–Mori 2.29). Let `X` be a
smooth variety over an algebraically closed field `k` of characteristic zero, with canonical
divisor `K` of dimension `n`, `Δ` a `ℚ`-divisor on `X`, and `Z ⊆ X` an irreducible closed subset
of codimension `c ≥ 2`. Let `D = (Y, f, E)` be a divisor over `X` whose model `Y`
is an open subscheme of the blow-up `Bl_Z X` of the vanishing ideal of `Z` (through `j`, with
`f = j ≫ p`) and with `f(η_E) = η_Z`, i.e. `E` is the component of the exceptional divisor
dominating `Z`. Then `(X, Δ)` is a pair and
`a(E, X, Δ) = c - 1 - ∑_Γ coeff_Γ(Δ) · mult_Z Γ`. -/
@[mmp "lem_km2b_blowup_discrepancy"]
public theorem isDiscrepancy_blowUp {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsVariety k sX) [Smooth sX]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (Δ : QDivisor X)
    (Z : IrreducibleCloseds X) {c : ℕ} (hc : (c : ℕ∞) = codimension Z) (hc2 : 2 ≤ c)
    (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨Z, Z.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = Z.isIrreducible.genericPoint) :
    IsPair sX Δ ∧
      IsDiscrepancy sX n K Δ D
        ((c : ℚ) - 1 - Δ.sum fun Γ a => a * ((Γ.multiplicityAlong Z).toNat : ℚ)) :=
  isDiscrepancy_blowUp_of_charZero sX hX hK Δ Z hc hc2 D j hj hE

end BlowUp

section CrepantBoundary

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (hs : IsSeparated s) : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A specialization between equal points induces an isomorphism of stalks. -/
private theorem isIso_stalkSpecializes {X : Scheme.{u}} {x y : X} (hsp : x ⤳ y)
    (h : x = y) : IsIso (X.presheaf.stalkSpecializes hsp) := by
  subst h
  simp only [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

/-- A bijective algebra map is a localization at the trivial submonoid. -/
private theorem isLocalization_bot_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    IsLocalization (⊥ : Submonoid R) S :=
  IsLocalization.of_le_isUnit_of_bijective
    (by rw [Algebra.algebraMapSubmonoid, Submonoid.map_bot]; exact bot_le) h

section

variable {k : Type*} [CommRing k] {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

/-- Along a bijective map of fields over `k`, `Ω^d_{K/k} ⟶ Ω^d_{L/k}` is injective: the inverse
map is a left inverse. -/
private theorem topFormsMap_injective_of_bijective (h : Function.Bijective (algebraMap K L))
    (d : ℕ) :
    Function.Injective (topFormsMap k K L d) := by
  let e := RingEquiv.ofBijective (algebraMap K L) h
  let : Algebra L K := e.symm.toRingHom.toAlgebra
  have : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k K c = e.symm (algebraMap k L c)
    rw [IsScalarTower.algebraMap_apply k K L]
    exact (e.symm_apply_apply _).symm
  have : IsScalarTower K L K := IsScalarTower.of_algebraMap_eq fun c =>
    (e.symm_apply_apply c).symm
  intro x y hxy
  have h1 := congrArg (topFormsMap k L K d) hxy
  rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
    MMP.Threefold.Mori.Helpers.topFormsMap_comp] at h1
  have hid := topFormsMap_eq_self (k := k) (RingHom.id K) (fun _ => rfl) (d := d)
  rwa [hid, hid] at h1

end

section

variable {k : Type*} [CommRing k] {d : ℕ}
variable {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L] [Algebra k A]
  [Algebra k B] [Algebra k K] [Algebra k L] [Algebra A K] [Algebra B L] [Algebra A B]
  [Algebra K L] [Algebra A L] [IsScalarTower k A K] [IsScalarTower k B L] [IsScalarTower k A B]
  [IsScalarTower k K L] [IsScalarTower k A L] [IsScalarTower A B L] [IsScalarTower A K L]

/-- A generator of `Ω^d_{A/k}` with nonzero image in `Ω^d_{K/k}` is carried, along bijective
maps `A ⟶ B` and `K ⟶ L`, to a generator of `Ω^d_{B/k}` with nonzero image in `Ω^d_{L/k}`. -/
private theorem exists_generator_of_bijective (hAB : Function.Bijective (algebraMap A B))
    (hKL : Function.Bijective (algebraMap K L))
    (h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0) :
    ∃ σ : ⋀[B]^d Ω[B⁄k], Submodule.span B {σ} = ⊤ ∧ topFormsMap k B L d σ ≠ 0 := by
  obtain ⟨σ, hσ, h0⟩ := h
  have := isLocalization_bot_of_bijective hAB
  refine ⟨topFormsMap k A B d σ, span_singleton_topFormsMap ⊥ hσ, ?_⟩
  rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
    ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := K) (C := L)]
  exact fun h1 => h0 (topFormsMap_injective_of_bijective hKL d (h1.trans (map_zero _).symm))

end

section

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}
variable {K K' : Type*} [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K']
  [IsScalarTower k K K']
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K] [Algebra A' K'] [IsScalarTower k A' K']
  [IsFractionRing A' K'] [Algebra A A'] [IsScalarTower k A A'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [IsScalarTower k A K']

/-- The order of a form is invariant under bijective maps `A ⟶ A'`, `K ⟶ K'` compatible with the
valuations, with no hypothesis on `k`: if `Ω^d_{A/k}` has a generator the orders are computed
from it and its image; otherwise neither side has one and both orders are `0`. -/
private theorem ordAt_pullbackForms_eq_of_bijective (hbij : Function.Bijective (algebraMap A A'))
    (hbijK : Function.Bijective (algebraMap K K'))
    {v : K → ℤ} {v' : K' → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hmul' : ∀ x y : K', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : A', IsUnit a → v' (algebraMap A' K' a) = 0)
    (hvv : ∀ x, v' (algebraMap K K' x) = v x) (τ : PluriForms k K d m) :
    ordAt A' v' (pullbackForms (K' := K') m τ) = ordAt A v τ := by
  classical
  by_cases h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  · obtain ⟨σ, hσ, h0⟩ := h
    have := isLocalization_bot_of_bijective hbijK
    have hK := span_singleton_topFormsMap (K := K) (nonZeroDivisors A) hσ
    have hω : IsPullbackGenerator K' (topFormsMap k A K d σ) :=
      ⟨hK, span_singleton_topFormsMap ⊥ hK, fun h1 =>
        h0 (topFormsMap_injective_of_bijective hbijK d (h1.trans (map_zero _).symm))⟩
    exact MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq hbij hmul hunit hmul' hunit' hvv
      hσ hω τ
  · have h' : ¬ ∃ σ : ⋀[A']^d Ω[A'⁄k], Submodule.span A' {σ} = ⊤ ∧
        topFormsMap k A' K' d σ ≠ 0 := by
      intro h'
      apply h
      let eA := RingEquiv.ofBijective (algebraMap A A') hbij
      let eK := RingEquiv.ofBijective (algebraMap K K') hbijK
      let : Algebra A' A := eA.symm.toRingHom.toAlgebra
      let : Algebra K' K := eK.symm.toRingHom.toAlgebra
      let : Algebra A' K := ((algebraMap A K).comp (algebraMap A' A)).toAlgebra
      have hA : ∀ c : k, algebraMap k A c = eA.symm (algebraMap k A' c) := fun c => by
        rw [IsScalarTower.algebraMap_apply k A A']
        exact (eA.symm_apply_apply _).symm
      have hKc : ∀ c : k, algebraMap k K c = eK.symm (algebraMap k K' c) := fun c => by
        rw [IsScalarTower.algebraMap_apply k K K']
        exact (eK.symm_apply_apply _).symm
      have : IsScalarTower k A' A := IsScalarTower.of_algebraMap_eq hA
      have : IsScalarTower k K' K := IsScalarTower.of_algebraMap_eq hKc
      have : IsScalarTower A' A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : IsScalarTower k A' K := IsScalarTower.of_algebraMap_eq fun c => by
        change _ = algebraMap A K (eA.symm (algebraMap k A' c))
        rw [← hA, ← IsScalarTower.algebraMap_apply]
      have : IsScalarTower A' K' K := IsScalarTower.of_algebraMap_eq fun a => by
        change algebraMap A K (eA.symm a) = eK.symm (algebraMap A' K' a)
        apply eK.injective
        rw [RingEquiv.apply_symm_apply]
        change algebraMap K K' (algebraMap A K (eA.symm a)) = _
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A A' K']
        congr 1
        exact eA.apply_symm_apply a
      exact exists_generator_of_bijective (A := A') (B := A) (K := K') (L := K)
        eA.symm.bijective eK.symm.bijective h'
    simp only [ordAt, h, h', dite_false]

end

/-- The order of a rational pluricanonical form is unchanged by pulling back along a prime
divisor `F` of `Y` dominating a prime divisor `P` of `X`: `ord_F(f^*τ) = ord_P(τ)` when
`f(η_F) = η_P` and `f^♯ : 𝒪_{X,P} ⟶ 𝒪_{Y,F}` is an isomorphism, `f^* : k(X) → k(Y)` being an
isomorphism. The isomorphisms carry a generator of `Ω^d_{𝒪_{X,P}/k}` to one of `Ω^d_{𝒪_{Y,F}/k}`
and back, so both sides are computed from the same generator, or both vanish. -/
private theorem ordForm_pullbackRationalPluriForms_of_isIso {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal X] [IsNormal Y] {sX : X ⟶ Spec (.of k)} (f : Y ⟶ X)
    [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ} (F : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f F.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap F.genericPoint)] {m : ℤ} (τ : RationalPluriForms sX d m) :
    F.ordForm (pullbackRationalPluriForms sX f τ) = P.ordForm τ := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := stalkAlgebra sX P.genericPoint
  have := isScalarTower_stalk_functionField sX P.genericPoint
  let := stalkAlgebra (f ≫ sX) F.genericPoint
  have := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
  have hsp : f F.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : X.presheaf.stalk P.genericPoint ⟶ Y.presheaf.stalk F.genericPoint :=
    X.presheaf.stalkSpecializes hsp ≫ f.stalkMap F.genericPoint
  have := isIso_stalkSpecializes hsp heq
  have hφ : IsIso φ := by infer_instance
  let : Algebra P.localRing F.localRing := φ.hom.toAlgebra
  let : Algebra P.localRing Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap P.localRing X.functionField)).toAlgebra
  have : IsScalarTower P.localRing X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hφK : ∀ r : P.localRing, algebraMap P.localRing Y.functionField r =
      algebraMap F.localRing Y.functionField (φ.hom r) := fun r => by
    change functionFieldMap f _ = algebraMap _ Y.functionField ((f.stalkMap F.genericPoint).hom
        ((X.presheaf.stalkSpecializes hsp).hom r))
    rw [← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]
  have : IsScalarTower P.localRing F.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq hφK
  have : IsScalarTower k P.localRing F.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
          Y.presheaf.germ ⊤ F.genericPoint (Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
          X.presheaf.germ ⊤ P.genericPoint (Opens.mem_top _)) ≫ φ := by
      simp only [φ, Scheme.Hom.comp_appTop, Category.assoc,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
      rfl
    exact congrArg CommRingCat.Hom.hom h
  have : IsScalarTower k P.localRing Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
      IsScalarTower.algebraMap_apply k P.localRing X.functionField]
    rfl
  have hbijA : Function.Bijective (algebraMap P.localRing F.localRing) :=
    (ConcreteCategory.isIso_iff_bijective φ).mp hφ
  exact ordAt_pullbackForms_eq_of_bijective (k := k) hbijA hbij
    P.ord_mul_of_ne_zero (fun _ ha => P.ord_algebraMap_of_isUnit ha)
    F.ord_mul_of_ne_zero (fun _ ha => F.ord_algebraMap_of_isUnit ha)
    (fun x => MMP.Positivity.ord_functionFieldMap_of_isIso f F P heq x) τ

section Coefficients

variable {X Y : Scheme.{u}} {R : Type*} [AddCommMonoid R]

/-- The coefficient of `F` in `∑ dᵢ φ(Dᵢ)` is `0` when `F` is the image of no prime divisor. -/
private theorem mapPrimeDivisors_apply_eq_zero
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {F : MMP.Mori.PrimeDivisor Y} (h : ∀ D, φ D ≠ some F) (Δ : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ Δ F = 0 := by
  induction Δ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, Finsupp.add_apply, ha, hb, add_zero]
  | single D r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hD : φ D with _ | G
    · rfl
    · have : G ≠ F := fun hG => h D (hD.trans (congrArg some hG))
      exact Finsupp.single_eq_of_ne this.symm

/-- The coefficient of `F` in `∑ dᵢ φ(Dᵢ)` is `d_P` when `P` is the only prime divisor with
`φ(P) = F`. -/
private theorem mapPrimeDivisors_apply_eq
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {F : MMP.Mori.PrimeDivisor Y} {P : MMP.Mori.PrimeDivisor X} (hP : φ P = some F)
    (h : ∀ D, φ D = some F → D = P) (Δ : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ Δ F = Δ P := by
  induction Δ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, Finsupp.add_apply, ha, hb, Finsupp.add_apply]
  | single D r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hD : φ D with _ | G
    · have : D ≠ P := by rintro rfl; rw [hP] at hD; cases hD
      exact (Finsupp.single_eq_of_ne this.symm).symm
    · by_cases hG : G = F
      · subst hG
        obtain rfl := h D hD
        simp
      · have : D ≠ P := by rintro rfl; rw [hP] at hD; exact hG (Option.some.inj hD).symm
        change Finsupp.single G r F = Finsupp.single D r P
        rw [Finsupp.single_eq_of_ne (Ne.symm hG), Finsupp.single_eq_of_ne this.symm]

end Coefficients

section Crepant

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The coefficient of the crepant boundary along a prime divisor `F` of `Y` lying over a prime
divisor `P` of `X`, at whose generic point `f` is a local isomorphism, is `coeff_P(Δ)`. -/
private theorem coeff_eq_of_isIso_stalkMap {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {Y : Scheme.{u}} {f : Y ⟶ X} {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (F : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor X)
    (heq : f F.genericPoint = P.genericPoint) [IsIso (f.stalkMap F.genericPoint)] :
    ΔY.coeff F = Δ.coeff P := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsDominant f := hf.isDominant
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, ha⟩ := hΔY F
  have h1 : (DivisorOver.ordPullback ⟨Y, f, hY, hf, F⟩ τ) = P.ordForm τ :=
    ordForm_pullbackRationalPluriForms_of_isIso f hf.functionFieldMap_bijective F P heq τ
  have h2 := hτ.2 P ⟨P.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
    heq ▸ hU⟩
  rw [h1] at ha
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ hm'
  linear_combination -ha - h2

/-- A prime divisor `F` of `Y` is exceptional for a morphism `f : Y ⟶ X` exactly when `f(η_F)`
has codimension at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight
    [IsSeparated (X ↘ Limits.terminal Scheme)]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) :
    RationalMap.IsExceptional (X := Y) f.toRationalMap F ↔
      2 ≤ Order.coheight (f F.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hη : F.genericPoint ∈ (F.idealSheaf.support : Set Y) := by
    change F.genericPoint ∈ F.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  refine ⟨fun h ↦ h _ (subset_closure ⟨_, hη, rfl⟩), fun h x hx ↦ ?_⟩
  have hsub : closure (f '' (F.idealSheaf.support : Set Y)) ⊆ closure {f F.genericPoint} := by
    refine closure_minimal ?_ isClosed_closure
    change f '' (F.support : Set Y) ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have := image_closure_subset_closure_image (f := f) (s := {F.genericPoint}) f.continuous
    rwa [Set.image_singleton] at this
  have hsp : f F.genericPoint ⤳ x := specializes_iff_mem_closure.mpr (hsub hx)
  exact h.trans (Order.coheight_anti (show x ≤ f F.genericPoint from hsp))

end Crepant

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

open Classical in
/-- **The crepant boundary is the strict transform plus an exceptional part** (Kollár–Mori 2.26).
Let `(X, Δ)` be a pair with canonical divisor `K` of dimension `n`, and `f : Y ⟶ X` a proper
birational morphism from a normal variety `Y`. If `Δ_Y` is the crepant boundary of `(X, Δ)` on
`Y`, then `Δ_Y = f⁻¹_* Δ + ∑_E coeff_E(Δ_Y) E = f⁻¹_* Δ - ∑_E a(E, X, Δ) E`, the sum over the
`f`-exceptional prime divisors `E` of `Y`, and `f_* Δ_Y = Δ`. -/
@[mmp "lem_km2b_crepant_boundary_strict_transform_part"]
public theorem IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hP : IsPair sX Δ) {Y : Scheme.{u}} {f : Y ⟶ X}
    [IsProper f] {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) :
    ΔY = inverseTransformDivisor f Δ +
        Finsupp.filter (fun E => RationalMap.IsExceptional (X := Y) f.toRationalMap E) ΔY ∧
      RationalMap.transformDivisor (X := Y) f.toRationalMap ΔY = Δ := by
  have hX : IsNormalVariety k sX := hP.1
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsSeparated sX := hX.1.toIsSeparated
  have := isSeparated_toTerminal hX.1.toIsSeparated
  -- `f` is an isomorphism over the points of codimension at most one of `X`
  have hbir : ∀ y : X, Order.coheight y ≤ 1 → y ∈ biregularLocus f := by
    intro y hy
    by_contra hn
    have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
      (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX f (hY := hX.1) (hX := hY.1)
        hf) y hn
    exact absurd (h2.trans hy) (by decide)
  refine ⟨Finsupp.ext fun F ↦ ?_, Finsupp.ext fun P ↦ ?_⟩
  · rw [Finsupp.add_apply, Finsupp.filter_apply]
    change ΔY F = DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor f) Δ F + _
    by_cases hE : RationalMap.IsExceptional (X := Y) f.toRationalMap F
    · rw [if_pos hE, mapPrimeDivisors_apply_eq_zero, zero_add]
      intro D hD
      have h2 := (isExceptional_toRationalMap_iff_two_le_coheight f F).mp hE
      rw [(MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD).1, D.coheight_genericPoint] at h2
      exact absurd h2 (by decide)
    · rw [if_neg hE, add_zero]
      have hV := hbir _ <| Order.le_of_lt_succ <| not_le.mp <|
        mt (isExceptional_toRationalMap_iff_two_le_coheight f F).mpr hE
      have hc : Order.coheight (f F.genericPoint) = 1 := by
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hV]
        exact F.coheight_genericPoint
      set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
      have hPη : P.genericPoint = f F.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc
      have hFP := MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hPη.symm hV
      have huniq : ∀ D, inverseTransformPrimeDivisor f D = some F → D = P := fun D hD ↦
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
            hD).1.symm.trans hPη.symm)
      have := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hV
      rw [mapPrimeDivisors_apply_eq hFP huniq]
      exact coeff_eq_of_isIso_stalkMap hΔY F P hPη.symm
  · obtain ⟨E, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [htr]
    exact coeff_eq_of_isIso_stalkMap hΔY E P heq

end CrepantBoundary

section ProperModel

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- A divisor `(W, g, F)` over `Y`, for a birational morphism `f : Y ⟶ X` of varieties, regarded
as the divisor `(W, f ∘ g, F)` over `X`. -/
private noncomputable def compDivisorOver {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) : DivisorOver k sX :=
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI := E.isIntegral
  { Y := E.Y
    f := E.f ≫ f
    isNormalVariety := by rw [Category.assoc]; exact E.isNormalVariety
    isBirationalMorphism := isBirationalMorphism_comp E.isBirationalMorphism hf
    E := E.E }

private theorem valuation_compDivisorOver {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) :
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  ext t
  change E.E.divisorialValuation (functionFieldMap (E.f ≫ f) t) =
    E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- A divisor `(Y, f, E)` over a separated normal scheme `X` is exceptional if and only if
`f(η_E)` has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hc : ((TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) :
      TopologicalSpace.Closeds X) : Set X) = closure {D.f D.E.genericPoint} :=
    D.center_eq_closure_genericPoint
  rw [hc]
  exact ⟨fun h => h _ (subset_closure rfl),
    fun h x hx => h.trans (Order.coheight_anti (specializes_iff_mem_closure.mpr hx))⟩

/-- **Exceptional over `Y` is exceptional over `X`** (Kollár–Mori, proof of 2.32). If `f` is
proper birational and `(W, g, F)` is exceptional over `Y`, then `(W, f ∘ g, F)` is exceptional
over `X`: otherwise the center of `F` on `X` is a prime divisor `D`, `f` is an isomorphism over a
neighbourhood of `η_D`, and the center of `F` on `Y` would be the strict transform of `D`. -/
private theorem isExceptional_compDivisorOver {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    [IsProper f] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (E : DivisorOver k (f ≫ sX)) (hE : E.IsExceptional) :
    (compDivisorOver f hY hf E).IsExceptional := by
  have := isSeparated_toTerminal hX.1.toIsSeparated
  have := isSeparated_toTerminal hY.1.toIsSeparated
  rw [isExceptional_iff_two_le_coheight] at hE ⊢
  change 2 ≤ Order.coheight (f (E.f E.E.genericPoint))
  by_cases hx : f (E.f E.E.genericPoint) ∈ MMP.Mori.biregularLocus f
  · rwa [MMP.Positivity.coheight_map_of_mem_biregularLocus f hx]
  · exact MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
      (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX f (hY := hX.1) (hX := hY.1)
        hf) _ hx

/-- An exceptional divisor `(W, g, F)` over `Y` gives the exceptional divisor `(W, g ≫ f, F)`
over `X`, with `a(F, X, Δ) = a(F, Y, Δ_Y)`. -/
private theorem exists_of_isExceptional_over_model {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsAlgClosed k] [CharZero k] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hP : IsPair sX Δ) (hK : K.IsCanonicalDivisor sX n)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    [IsProper f] {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (D : DivisorOver k (f ≫ sX)) (a : ℚ) (hD : D.IsExceptional)
    (ha : IsDiscrepancy (f ≫ sX) n KY ΔY D a) :
    ∃ D' : DivisorOver k sX, D'.IsExceptional ∧ IsDiscrepancy sX n K Δ D' a := by
  haveI : IsDominant f := hf.isDominant
  exact ⟨compDivisorOver f hY hf D, isExceptional_compDivisorOver hP.1 hY hf D hD,
    ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP f hY hf hK hKY (Or.inl hΔY)).2 D _
    (valuation_compDivisorOver f hY hf D) a).1 ha⟩

/-- For a birational morphism `f : Y ⟶ X`, a valuation `ξ` of `k(Y)` restricting on `k(X)` to the
valuation of a divisor `(W, g, F)` over `X` is a divisor of `k(Y)`: it is `ord_F` on `W`,
transported along `k(Y) ≅ k(X) ≅ k(W)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (hf : IsBirationalMorphism f) (D : DivisorOver k sX)
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap f) = D.valuation) :
    MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
  let eP := MMP.Mori.functionFieldAlgEquiv sX f hf.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hf.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
  change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
  rw [h1, hs]
  rfl

/-- **The center on a proper model.** For a proper dominant morphism `f : Y ⟶ X` of integral
schemes and a divisor `D` over `X`, a valuation `ξ` of `k(Y)` restricting on `k(X)` to `ord_D`
dominates the local ring of some point of `Y`: the valuation ring of `ξ` dominates
`𝒪_{X, c_X(D)}`, and the valuative criterion for `f` lifts `Spec 𝒪_ξ ⟶ X` to `Y`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] [IsProper f] (D : DivisorOver k sX)
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap f) = D.valuation) :
    ∃ y : Y, (∀ a : Y.presheaf.stalk y, ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
        ξ (algebraMap _ Y.functionField a) < 1 := by
  set z := D.f D.E.genericPoint
  have hw : ∀ b : X.presheaf.stalk z,
      ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) := fun b => by
    simpa only [Valuation.comap_apply] using
      congrArg (fun v => v (algebraMap _ X.functionField b)) h
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk z →+* R :=
    ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
  have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : @IsProper _ _ f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := R
      K := Y.functionField
      i₁ := Y.fromSpecStalk (genericPoint Y)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk f,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
      Y.fromSpecStalk (genericPoint Y) := hl₁
  set y := l (IsLocalRing.closedPoint R)
  have hy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
      Y.presheaf.stalkSpecializes hy := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk y)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : Y.presheaf.stalk y,
      algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨y, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]; exact (g.hom a).2
  · rw [hga]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- **A divisor over `X` lives on a proper model** (Kollár–Mori, proof of 2.32). For a proper
birational morphism `f : Y ⟶ X` of normal varieties, every divisor `(W, g, F)` over `X` has the
valuation of a divisor over `Y`: `f⁻¹ ∘ g` is defined on an open `W' ∋ η_F`, and `(W', f⁻¹ ∘ g,
F ∩ W')` is a divisor over `Y` with the valuation of `F`. -/
private theorem exists_divisorOver_comap_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    [IsProper f] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (D : DivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ D' : DivisorOver k (f ≫ sX), D'.valuation.comap (functionFieldMap f) = D.valuation := by
  haveI : IsDominant f := hf.isDominant
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  let e := RingEquiv.ofBijective (functionFieldMap f) hf.functionFieldMap_bijective
  let ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) :=
    D.valuation.comap e.symm.toRingHom
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    change D.valuation (e.symm (e t)) = D.valuation t
    rw [e.symm_apply_apply]
  obtain ⟨y, h1, h2⟩ := exists_dominated_point_of_comap_eq f D ξ hξ
  obtain ⟨D', -, hv, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX)
    (isDivisorOfFunctionField_of_comap_eq f hf D ξ hξ) y h1 h2
  exact ⟨D'.toDivisorOver, by rw [← hξ]; exact congrArg (·.comap (functionFieldMap f)) hv⟩

/-- An exceptional divisor `(W, g, F)` over `X` either is, near `η_F`, an exceptional divisor
over `Y` with `a(F, Y, Δ_Y) = a(F, X, Δ)`, or has the valuation of an `f`-exceptional prime
divisor `E` of `Y`, and then `a(F, X, Δ) = a(E, X, Δ)`. -/
private theorem exists_of_isExceptional_over_base {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsAlgClosed k] [CharZero k] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hP : IsPair sX Δ) (hK : K.IsCanonicalDivisor sX n)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    [IsProper f] {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (D : DivisorOver k sX) (a : ℚ) (hD : D.IsExceptional) (ha : IsDiscrepancy sX n K Δ D a) :
    (∃ D' : DivisorOver k (f ≫ sX), D'.IsExceptional ∧
        IsDiscrepancy (f ≫ sX) n KY ΔY D' a) ∨
      ∃ E : PrimeDivisor Y, RationalMap.IsExceptional (X := Y) f.toRationalMap E ∧
        IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, E⟩ a := by
  haveI : IsDominant f := hf.isDominant
  have := isSeparated_toTerminal hP.1.1.toIsSeparated
  have := isSeparated_toTerminal hY.1.toIsSeparated
  obtain ⟨D', hv⟩ := exists_divisorOver_comap_valuation_eq hP.1 hY hf D
  have hcen : D.f D.E.genericPoint = f (D'.f D'.E.genericPoint) :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hP.1.1
      (D' := compDivisorOver f hY hf D') ((valuation_compDivisorOver f hY hf D').trans hv).symm
  have hD2 := (isExceptional_iff_two_le_coheight D).1 hD
  rw [hcen] at hD2
  by_cases hD' : D'.IsExceptional
  · exact Or.inl ⟨D', hD', ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP f hY hf hK hKY
      (Or.inl hΔY)).2 D' D hv.symm a).2 ha⟩
  right
  set y := D'.f D'.E.genericPoint with hy
  have hy2 : Order.coheight y < 2 :=
    lt_of_not_ge fun h => hD' ((isExceptional_iff_two_le_coheight D').2 h)
  have hy0 : Order.coheight y ≠ 0 := by
    intro h0
    have hmax : IsMax y := Order.coheight_eq_zero.mp h0
    have hgy : y = genericPoint Y :=
      Specializes.antisymm (hmax (genericPoint_specializes y)) (genericPoint_specializes y) |>.eq
    rw [hgy, MMP.Positivity.map_genericPoint_eq_of_isDominant] at hD2
    have hmaxX : IsMax (genericPoint X) := fun z _ ↦ genericPoint_specializes z
    rw [Order.coheight_eq_zero.mpr hmaxX] at hD2
    exact absurd hD2 (by decide)
  have hy1 : Order.coheight y = 1 := by
    generalize Order.coheight y = c at hy2 hy0
    lift c to ℕ using hy2.ne_top
    norm_cast at *
    omega
  set E : PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy1
  have hE : E.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy1
  have hvE : (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).valuation = D.valuation := by
    rw [← hv, MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hY D' E hE.symm]
    ext t
    change MMP.Mori.PrimeDivisor.divisorialValuation E (functionFieldMap f t) =
      MMP.Mori.PrimeDivisor.divisorialValuation E (functionFieldMap (𝟙 Y) (functionFieldMap f t))
    rw [MMP.Mori.functionFieldMap_id_apply]
  refine ⟨E, ?_, ?_⟩
  · refine (isExceptional_iff_two_le_coheight (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX)).2 ?_
    change 2 ≤ Order.coheight (f E.genericPoint)
    rwa [hE]
  · obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
      (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX)
    obtain rfl := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hvE.symm
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hvE.symm) ha ha'
    exact ha'

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The discrepancy of a pair on a proper model** (Kollár–Mori, proof of 2.32). Let `(X, Δ)`
be a pair over an algebraically closed field of characteristic zero, `K` a canonical divisor of
`X` of dimension `n`, `f : Y ⟶ X` a proper birational morphism from a normal variety `Y` with
canonical divisor `K_Y`, and `Δ_Y` the crepant boundary of `(X, Δ)` on `Y`. Then
`discrep(X, Δ) = min {discrep(Y, Δ_Y), inf_E a(E, X, Δ)}`, the infimum over the `f`-exceptional
prime divisors `E` of `Y`. -/
@[mmp "lem_km2b_discrep_via_proper_model"]
public theorem IsCrepantBoundary.discrep_eq_min [IsAlgClosed k] [CharZero k] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hP : IsPair sX Δ) (hK : K.IsCanonicalDivisor sX n)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    [IsProper f] {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) :
    discrep sX n K Δ = min (discrep (f ≫ sX) n KY ΔY)
      (sInf {x : EReal | ∃ (E : PrimeDivisor Y) (a : ℚ),
        RationalMap.IsExceptional (X := Y) f.toRationalMap E ∧
          IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, E⟩ a ∧ x = ((a : ℝ) : EReal)}) := by
  refine le_antisymm (le_min ?_ ?_) ?_
  · refine le_discrep_iff.mpr fun D a hD ha => ?_
    obtain ⟨D', hD', ha'⟩ := exists_of_isExceptional_over_model hP hK hKY hΔY D a hD ha
    exact discrep_le hD' ha'
  · refine le_sInf ?_
    rintro _ ⟨E, a, hE, ha, rfl⟩
    exact discrep_le (D := ⟨Y, f, hY, hf, E⟩) hE ha
  · refine le_discrep_iff.mpr fun D a hD ha => ?_
    rcases exists_of_isExceptional_over_base hP hK hKY hΔY D a hD ha with
      ⟨D', hD', ha'⟩ | ⟨E, hE, ha'⟩
    · exact (min_le_left _ _).trans (discrep_le hD' ha')
    · exact (min_le_right _ _).trans (sInf_le ⟨E, a, hE, ha', rfl⟩)

end ProperModel

end MMP.Mori

end
