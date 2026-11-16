module

public import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary

/-!
# Log discrepancies of divisorial valuations on fourfolds

Two computations of log discrepancies `a(ξ; X, B)` of divisorial valuations over a pair
`(X, B)`.

*The generic blowup valuation of a surface.* Let `(X, B)` be a fourfold pair,
`B = ∑ b_h B_h` with prime `B_h`, and `V ⊆ X` an irreducible surface such that `X` is smooth at
the generic point `η_V`. Let `v_V` be the generic blowup valuation of `V`, the order along the
exceptional divisor `E` of the blowup `π : X' → X` of `V` near `η_V`. Since
`K_{X'} = π^*K_X + E` and `π^*B_h = π⁻¹_*B_h + m_h E` near the generic point of `E`, where
`m_h = mult_{η_V} B_h`, the log discrepancy is
`a(v_V; X, B) = 2 - ∑_h m_h b_h = 2 - mult_{η_V} B`.

*The log-smooth formula.* Let `(π, T)` be a log-smooth datum for a klt pair `(X, B)`:
`π : W ⟶ X` is a projective birational morphism from a smooth variety and `T = ∑ⱼ Tⱼ` is a
reduced snc divisor on `W` containing the exceptional locus of `π` and the support of the crepant
pull-back `B_W`. Write `aⱼ = a(ord_{Tⱼ}; X, B)`. For a normalized divisorial valuation `ξ` of
`k(X) = k(W)`, with centre `c_W(ξ)` on `W`, the set `J(ξ)` of components containing the centre
and the reduced snc discrepancy `e_T(ξ)`, the log discrepancy splits as
`a(ξ; X, B) = ∑_{j ∈ J(ξ)} ξ(Tⱼ) aⱼ + e_T(ξ)`.

## Main results

* `MMP.Fourfold.IsSurfaceGenericBlowupValuation.isLogDiscrepancy_two_sub_multiplicityAt`:
  for every divisor `E` over `X`, proper over `X`, realizing `v_V`, the number
  `2 - mult_{η_V} B` is a log discrepancy of `E` on `(X, B)`, and it is the only one.
* `MMP.Fourfold.IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy`: the
  log-smooth formula.

## Implementation notes

* `∑_h m_h b_h` is the multiplicity `MMP.Mori.DivisorWithCoeffs.multiplicityAt` of `B` at
  `η_V`, where `m_h = MMP.Mori.PrimeDivisor.multiplicityAt B_h η_V` is `0` when `V ⊄ B_h`.
* Log discrepancies are predicates on their values (`MMP.Intersection.IsLogDiscrepancy`, for
  top forms of degree `n` and a divisor over `X`); `a(v_V; X, B)` is the log discrepancy of any
  proper realization of `v_V`, and the statement is made for each of them.
* Dimension four, the dimension of `V`, and the regularity of `𝒪_{X,η_V}` are part of
  `MMP.Fourfold.IsSurfaceGenericBlowupValuation`. Over a field of characteristic zero,
  regularity of `𝒪_{X,η_V}` is smoothness of `X` at `η_V`.
* The proof of the generic blowup formula: `𝒪_{X,η_V}` is regular, hence factorial, so every
  prime divisor `B_h` through `η_V` has a local equation `g_h`. Dividing a rational top form by
  these gives a form `σ` with `ord_Γ σ = 0` for every prime divisor `Γ` through `η_V`, and
  `ord_E(f^*σ) = 1`, computed on the blow-up of `V` near `η_V`, where `X` and `V` are smooth.
  The Hartogs relation between a local generator of `𝒪_X(m(K_X + B))`, `σ` and the `g_h` gives
  the Kollár–Mori discrepancy `1 - mult_{η_V} B`.
* For the log-smooth formula the base field `k` is assumed perfect; the source works in
  characteristic zero, which implies it. The valuation `ξ` of `k(X)` is the valuation of a proper
  divisor `D` over `X`, regarded as a valuation of `k(W)` through `functionFieldMap π`. `ξ(Tⱼ)`
  is read off a local equation `zⱼ ∈ 𝒪_{W,η}` of `Tⱼ` at the generic point `η` of the centre:
  `ξ zⱼ = exp (-ξ(Tⱼ))` in Mathlib's multiplicative convention; the formula holds for every
  choice of local equations. The proof passes to the crepant pair `(W, B_W)`, raises the boundary
  to `T` (each `aⱼ Tⱼ` is Cartier on the smooth `W`), and localizes to the open where `T` is
  `∑_{j ∈ J(ξ)} Tⱼ`.

## References

* [OpenAI, *Projective lc fourfolds*], the log discrepancy of the generic blowup and the
  log-smooth formula.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Fourfold

open MMP.Mori

/-! ### The generic blowup valuation of a surface -/

/-- The centre of a divisor realizing `v_V` is the generic point of `V`. -/
private theorem map_genericPoint_eq
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v)
    (E : DivisorOver k sX) (hE : E.valuation = v) :
    E.f E.E.genericPoint = V.isIrreducible.genericPoint := by
  obtain ⟨D, -, hvD, hVD⟩ := hv.2.2.2.2.1
  have hX : MMP.Mori.IsVariety k sX := hv.1.1
  have hc := MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX (hE.trans hvD)
  have h1 : IsGenericPoint (E.f E.E.genericPoint) (V : Set X) := by
    change closure _ = _
    rw [hVD, ← hc, E.center_eq_closure_genericPoint]
  exact h1.eq (V.isIrreducible.isGenericPoint_genericPoint V.isClosed)

open scoped Classical in
/-- Local equations of the prime divisors through `η_V`: the local ring there is factorial. -/
private theorem exists_localEquation
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : V.isIrreducible.genericPoint ∈ Γ.support) :
    ∃ π : X.presheaf.stalk V.isIrreducible.genericPoint, π ≠ 0 ∧
      Γ.idealSheaf.stalkIdeal V.isIrreducible.genericPoint = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, V.isIrreducible.genericPoint ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = Γ then 1 else 0 := by
  set x := V.isIrreducible.genericPoint with hx
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) := hv.2.2.2.1
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hsp : Γ.genericPoint ⤳ x := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  set q := MMP.Intersection.primeOfSpecializes hsp with hq
  -- the prime of `η_Γ` has height one
  have hq1 : q.height = 1 := by
    let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk Γ.genericPoint)
    rw [ringKrullDim_stalk_eq_coheight, Γ.coheight_genericPoint] at e
    exact_mod_cast e.symm
  -- the stalk of the ideal of `Γ`
  set I := IdealSheafData.stalk Γ.idealSheaf x with hI
  have hxs : x ∈ Γ.idealSheaf.support := hΓ
  have hIp : I.IsPrime := by
    have := Γ.integral
    obtain ⟨y, hy⟩ : x ∈ Set.range Γ.idealSheaf.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hxs
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
  refine ⟨π, hπ.ne_zero, by rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]; exact hIπ,
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
      rw [hqπ, Ideal.span_singleton_le_iff_mem]; exact hmem
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

private theorem ord_one_eq_zero {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) :
    Y.ord 1 y = 0 := by
  have := Scheme.ord_mul (x := y) (one_ne_zero (α := Y.functionField)) one_ne_zero
  rw [mul_one] at this
  omega

open scoped Classical in
/-- A local equation of `Γ` at `η_V` when `Γ` passes through `η_V`, and `1` otherwise. -/
private noncomputable def localEquationFn
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v) (Γ : MMP.Mori.PrimeDivisor X) :
    X.functionField :=
  if h : V.isIrreducible.genericPoint ∈ Γ.support then
    algebraMap _ X.functionField (exists_localEquation hv Γ h).choose
  else 1

private theorem localEquationFn_ne_zero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v) (Γ : MMP.Mori.PrimeDivisor X) :
    localEquationFn hv Γ ≠ 0 := by
  by_cases h : V.isIrreducible.genericPoint ∈ Γ.support
  · simp only [localEquationFn, dif_pos h]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (exists_localEquation hv Γ h).choose_spec.1)
  · simp only [localEquationFn, dif_neg h]
    exact one_ne_zero

open scoped Classical in
private theorem ord_localEquationFn
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v) (Γ : MMP.Mori.PrimeDivisor X)
    {Γ' : MMP.Mori.PrimeDivisor X} (hΓ' : V.isIrreducible.genericPoint ∈ Γ'.support) :
    X.ord (localEquationFn hv Γ) Γ'.genericPoint = if Γ' = Γ then 1 else 0 := by
  by_cases h : V.isIrreducible.genericPoint ∈ Γ.support
  · simp only [localEquationFn, dif_pos h]
    exact (exists_localEquation hv Γ h).choose_spec.2.2 Γ' hΓ'
  · have hne : Γ' ≠ Γ := by
      rintro rfl
      exact h hΓ'
    simp only [localEquationFn, dif_neg h, if_neg hne, ord_one_eq_zero]

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

/-- Regularity of a local ring is read through an open immersion. -/
private theorem isRegularLocalRing_of_isOpenImmersion {P Y : Scheme.{u}} (j : P ⟶ Y)
    [IsOpenImmersion j] (p : P) (h : IsRegularLocalRing (Y.presheaf.stalk (j p))) :
    IsRegularLocalRing (P.presheaf.stalk p) := by
  have : IsIso (j.stalkMap p) := inferInstanceAs (IsIso (j.toLRSHom.stalkMap p))
  exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv

/-- **A smooth neighbourhood of `η_V` in which `V` is smooth.** If `X` is a variety over a
perfect field, `V ⊆ X` an irreducible closed subset with generic point `x` of coheight two and
`𝒪_{X,x}` regular, there is an open `U ∋ x` such that `U` and `V ∩ U` (with its reduced
structure, the inverse image of that of `V`) are smooth over `k`, and `V ∩ U` has codimension
two in `U` with generic point `x`. -/
private theorem exists_smoothBlowup {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (V : IrreducibleCloseds X) (x : X)
    (hx : x = V.isIrreducible.genericPoint)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) (hcod : Order.coheight x = 2) :
    ∃ (U : X.Opens) (_ : x ∈ U) (I : U.toScheme.IdealSheafData)
      (_ : MMP.Resolution.IsSmoothBlowup (U.ι ≫ sX) I) (hirr : IsIrreducible (I.support : Set U)),
      U.ι hirr.genericPoint = x ∧
        codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) = 2 := by
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
    rw [hx]
    exact h1.eq (V.isIrreducible.isGenericPoint_genericPoint V.isClosed)
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
  -- `U` is smooth
  have hUsm : IsSmoothScheme (U.ι ≫ sX) :=
    isSmoothScheme_of_forall_isRegularLocalRing _ fun u =>
      isRegularLocalRing_of_isOpenImmersion U.ι u
        ((mem_smoothLocus_iff_isRegularLocalRing sX _).mp u.2.1)
  -- `V ∩ U` is smooth
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
  -- irreducibility and the generic point
  have hxgen : IsGenericPoint x (V : Set X) := by
    rw [hx]
    exact V.isIrreducible.isGenericPoint_genericPoint V.isClosed
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
  have hgen : hirr.genericPoint = xU :=
    (hirr.isGenericPoint_genericPoint I.support.isClosed).eq hpre'
  refine ⟨U, hxU, I, ⟨hUsm, hIsm⟩, hirr, by rw [hgen]; rfl, ?_⟩
  have hcl : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U.toScheme) =
      IrreducibleCloseds.closureSingleton xU := by
    ext1
    exact hpre'.symm
  rw [hcl, MMP.Flips.codimension_closureSingleton]
  have h1 := ringKrullDim_stalk_eq_coheight xU
  rw [ringKrullDim_eq_of_ringEquiv (U.stalkIso xU).commRingCatIsoToRingEquiv] at h1
  have h2 := ringKrullDim_stalk_eq_coheight x
  change ringKrullDim (X.presheaf.stalk x) = _ at h1
  rw [h2, hcod] at h1
  exact_mod_cast h1.symm

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
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
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
  have key : pullbackRationalPluriForms (a ≫ sX) c (pullbackRationalPluriForms sX a τ) =
      pullbackRationalPluriForms sX (c ≫ a) τ := by
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
  exact congrArg E.ordForm key

/-- The order of the pull-back of `h • τ` along a divisor over `X`. -/
private theorem ordPullback_smul {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : DivisorOver k sX) {m : ℤ}
    {h : X.functionField} (hh : h ≠ 0) {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    D.ordPullback (h • τ) =
      D.Y.ord (functionFieldMap D.f h) D.E.genericPoint + D.ordPullback τ := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isDominant
  let := functionFieldAlgebra sX
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hX hn
  have hhτ : h • τ ≠ 0 := smul_ne_zero hh hτ
  rw [hN m _ hhτ, hN m τ hτ]
  have hr : (ZTensorPower.basis β m).repr (h • τ) () =
      h * (ZTensorPower.basis β m).repr τ () := by
    have := congrArg (fun f => f ()) ((ZTensorPower.basis β m).repr.map_smul h τ)
    simp only [Finsupp.smul_apply, smul_eq_mul] at this
    exact this
  have hc0 := repr_ne_zero_of_ne_zero β hτ
  rw [hr, map_mul, Scheme.ord_mul ((map_ne_zero _).mpr hh) ((map_ne_zero _).mpr hc0)]
  ring

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

/-- A form generating the top forms at `η_V`, whose pull-back has order one along `E`. -/
private theorem exists_form
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v)
    (E : DivisorOver k sX) (hE : E.valuation = v) :
    ∃ σ : RationalPluriForms sX 4 1, σ ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor X, V.isIrreducible.genericPoint ∈ Γ.support →
        Γ.ordForm σ = 0) ∧
      E.ordPullback σ = 1 := by
  classical
  set x := V.isIrreducible.genericPoint with hx
  have hX : IsNormalVariety k sX := hv.1
  have hn : topologicalKrullDim X = 4 := hv.2.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  -- a form generating the top forms near `x`
  obtain ⟨β⟩ := MMP.Positivity.exists_basis_topForms hX hn
  let ω₀ : RationalPluriForms sX 4 1 := (ZTensorPower.basis β 1) ()
  have hω₀ : ω₀ ≠ 0 := (ZTensorPower.basis β 1).ne_zero ()
  let T : Finset (MMP.Mori.PrimeDivisor X) :=
    (finite_ordForm_ne_zero ω₀).toFinset.filter fun Γ => x ∈ Γ.support
  let h₀ : X.functionField := ∏ Γ ∈ T, localEquationFn hv Γ ^ (-(Γ.ordForm ω₀))
  have hh₀ : h₀ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun Γ _ => zpow_ne_zero _ (localEquationFn_ne_zero hv Γ)
  set σ : RationalPluriForms sX 4 1 := h₀ • ω₀ with hσdef
  have hσ0 : σ ≠ 0 := smul_ne_zero hh₀ hω₀
  have hσΓ : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → Γ.ordForm σ = 0 := by
    intro Γ hΓ
    rw [hσdef, Γ.ordForm_smul_of_topologicalKrullDim_eq hn hh₀ hω₀,
      MMP.Threefold.Bridges.ord_prod_zpow _ _ _ (localEquationFn_ne_zero hv)]
    simp_rw [ord_localEquationFn hv _ hΓ]
    by_cases hT : Γ ∈ T
    · rw [Finset.sum_eq_single Γ]
      · simp
      · intro Γ' _ hne
        simp [Ne.symm hne]
      · intro h; exact absurd hT h
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
  -- the smooth blow-up of `V` near `x`
  have hcod : Order.coheight x = 2 := by
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
    have hcl : closure ({x} : Set X) = V :=
      V.isIrreducible.isGenericPoint_genericPoint V.isClosed
    rw [hcl, hv.2.2.1, hn] at h1
    have h4' : (((2 : ℕ∞) + Order.coheight x : ℕ∞) : WithBot ℕ∞) = ((4 : ℕ∞) : WithBot ℕ∞) := by
      rw [WithBot.coe_add]
      exact h1
    have h4 : (2 : ℕ∞) + Order.coheight x = 4 := WithBot.coe_injective h4'
    generalize Order.coheight x = c at h4 ⊢
    induction c using ENat.recTopCoe with
    | top => simp at h4
    | coe c =>
      have : 2 + c = 4 := by exact_mod_cast h4
      have : c = 2 := by omega
      subst this; rfl
  obtain ⟨U, hxU, I, hsb, hirr, hgenpt, hcodI⟩ :=
    exists_smoothBlowup hX.1 V x rfl hv.2.2.2.1 hcod
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, hxU⟩)
  have hbijU : Function.Bijective (functionFieldMap U.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨⟨x, hxU⟩, trivial⟩
  have hUnv := isNormalVariety_ι hX U
  have : LocallyOfFiniteType (U.ι ≫ sX) := hUnv.1.toLocallyOfFiniteType
  have hdU : topologicalKrullDim U = 4 := by
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (U.ι ≫ sX)
    rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX U.ι hbijU, toENat_trdeg_functionField (sX := sX),
      hn]
  -- the pulled-back form generates near the generic point of `V ∩ U`
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
  have hc2 : (2 : ℕ) ≤ 2 := le_rfl
  have hcI : ((2 : ℕ) : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [hcodI]; rfl
  obtain ⟨hordE, hformE⟩ :=
    MMP.Threefold.Resolution.ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback
      (U.ι ≫ sX) hUnv.1 I hsb hirr hcI hc2 hdU
  obtain ⟨hvarB, hsmB, -, hbirπ, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (U.ι ≫ sX) hUnv.1 hdU I hsb hirr hcI hc2
  set y := hirr.genericPoint with hy
  have hyW : y ∈ U.ι ⁻¹ᵁ W := by
    change U.ι y ∈ W
    rw [hgenpt]; exact hxW
  have hform1 := hformE 1 τU ⟨_, hyW, hτgen⟩
  -- the divisor over `X` given by the exceptional divisor of the blow-up
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [hcodI]; decide
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
  -- its valuation is `v`
  have hvx : ∀ z (_ : z = x) (g : X.presheaf.stalk z), g ≠ 0 → ∃ M : ℕ,
      IsGreatest {n : ℕ | g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) ^ n} M ∧
        v (algebraMap _ X.functionField g) = WithZero.exp (-(M : ℤ)) := by
    rintro z rfl
    exact hv.2.2.2.2.2
  have hD' : D'.valuation = v := by
    refine (eq_of_forall_stalk_eq (U.ι y) fun g => ?_).symm
    by_cases hg : g = 0
    · simp [hg]
    obtain ⟨M, hM, hvM⟩ := hvx _ hgenpt g hg
    have : IsIso (U.ι.stalkMap y) := inferInstance
    set e := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv with he
    set g' := e g with hg'
    have hg'0 : g' ≠ 0 := fun h0 => hg (e.injective (h0.trans (map_zero e).symm))
    have hmem : ∀ s : ℕ, (s : ℤ) ≤ (blowUp I).ord (functionFieldMap π
        (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint ↔
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι y)) ^ s := fun s =>
      (hordE g' hg'0 s).trans (mem_maximalIdeal_pow_iff_of_bijective e s g)
    have hffm : functionFieldMap (π ≫ U.ι) (algebraMap _ X.functionField g) =
        functionFieldMap π (algebraMap _ (U : Scheme).functionField g') := by
      rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Mori.functionFieldMap_algebraMap_stalk]
      rfl
    have hord : (blowUp I).ord (functionFieldMap π
        (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint = M := by
      have h1 := (hmem M).mpr hM.1
      have h2 : ¬ ((M + 1 : ℕ) : ℤ) ≤ (blowUp I).ord (functionFieldMap π
          (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint := fun h => by
        have : M + 1 ≤ M := hM.2 (show M + 1 ∈ {n : ℕ | g ∈ _} from (hmem (M + 1)).mp h)
        omega
      push_cast at h2
      omega
    have hne : functionFieldMap (π ≫ U.ι) (algebraMap _ X.functionField g) ≠ 0 :=
      (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hg))
    rw [hvM]
    symm
    change MMP.Mori.PrimeDivisor.divisorialValuation Eex (functionFieldMap (π ≫ U.ι) _) = _
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord Eex hne, hffm, hord]
  refine ⟨σ, hσ0, hσΓ, ?_⟩
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn
    (D := E) (D' := D') (hE.trans hD'.symm) σ]
  change MMP.Mori.PrimeDivisor.ordForm Eex (pullbackRationalPluriForms sX (π ≫ U.ι) σ) = 1
  rw [← ordForm_pullback_pullback U.ι π hbijU hbirπ.functionFieldMap_bijective hd Eex σ, hform1]
  norm_num

/-- The order along `E` of an element of the local ring at `η_V` is its `𝔪_V`-adic order. -/
private theorem ord_eq_of_isGreatest
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (E : DivisorOver k sX) (hE : E.valuation = v)
    {g : X.presheaf.stalk V.isIrreducible.genericPoint} (hg : g ≠ 0) {M : ℕ}
    (hv : v (algebraMap _ X.functionField g) = WithZero.exp (-(M : ℤ))) :
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
  rw [← hE] at hv
  change E.E.valuationOver E.f _ = _ at hv
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
    E.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hg')] at hv
  exact neg_inj.mp (WithZero.exp_injective hv)

private theorem ord_functionFieldMap_localEquationFn
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v)
    (E : DivisorOver k sX) (hE : E.valuation = v) (Γ : MMP.Mori.PrimeDivisor X) :
    haveI := E.isIntegral
    haveI := E.isLocallyNoetherian
    haveI := E.isDominant
    E.Y.ord (functionFieldMap E.f (localEquationFn hv Γ)) E.E.genericPoint =
      ((Γ.multiplicityAt V.isIrreducible.genericPoint).toNat : ℤ) := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isDominant
  by_cases h : V.isIrreducible.genericPoint ∈ Γ.support
  · simp only [localEquationFn, dif_pos h]
    obtain ⟨hπ0, hπI, -⟩ := (exists_localEquation hv Γ h).choose_spec
    obtain ⟨M, hM, hvM⟩ := hv.2.2.2.2.2 _ hπ0
    rw [ord_eq_of_isGreatest E hE hπ0 hvM, Γ.multiplicityAt_eq_localMultiplicity hπI]
    have : localMultiplicity (exists_localEquation hv Γ h).choose = M :=
      le_antisymm (iSup₂_le fun j hj => by exact_mod_cast hM.2 hj) (le_localMultiplicity hM.1)
    rw [this, ENat.toNat_coe]
  · simp [localEquationFn, dif_neg h, Γ.multiplicityAt_eq_zero_of_notMem h, ord_one_eq_zero]

/-- The value of the discrepancy. -/
private theorem discrepancy_eq
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X}
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v)
    (E : DivisorOver k sX) (hE : E.valuation = v) {n : ℕ} {K : Divisor X} {c : ℚ}
    (hc : IsDiscrepancy sX n K B E c) :
    c = 1 - B.multiplicityAt V.isIrreducible.genericPoint := by
  classical
  set x := V.isIrreducible.genericPoint with hx
  obtain ⟨hX, hK, m, hm, -, W, hW, τ, hτ, hτc⟩ := hc
  have hn : topologicalKrullDim X = 4 := hv.2.1
  obtain rfl : n = 4 := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hn
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hEx : E.f E.E.genericPoint = x := map_genericPoint_eq hv E hE
  obtain ⟨σ, hσ0, hσΓ, hσE⟩ := exists_form hv E hE
  obtain ⟨β, N, hN⟩ := E.exists_ordPullback_eq hX hn
  -- the Hartogs relation
  set cτ := (ZTensorPower.basis β (m : ℤ)).repr τ () with hcτ
  set cσ := (ZTensorPower.basis β 1).repr σ () with hcσ
  have hcτ0 : cτ ≠ 0 := repr_ne_zero_of_ne_zero β hτ.1
  have hcσ0 : cσ ≠ 0 := repr_ne_zero_of_ne_zero β hσ0
  let S := B.support
  let G : Option (Option S) → X.functionField := fun j =>
    Option.elim j cτ fun j => Option.elim j cσ fun Γ => localEquationFn hv Γ.1
  let w : Option (Option S) → ℝ := fun j =>
    Option.elim j 1 fun j => Option.elim j (-(m : ℝ)) fun Γ => (m : ℝ) * (B Γ.1 : ℝ)
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | Γ)
    exacts [hcτ0, hcσ0, localEquationFn_ne_zero hv _]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := E.f) E.E G hG w
    fun Γ' hΓ' => by
      rw [hEx] at hΓ'
      obtain ⟨NΓ, hNΓ⟩ := Γ'.exists_ordForm_eq_ord_add_mul hd β
      have e1 := hNΓ m τ hτ.1
      have e2 := hNΓ 1 σ hσ0
      rw [hσΓ Γ' hΓ'] at e2
      have e3 := hτ.2 Γ' ⟨_, hΓ', hEx ▸ hW⟩
      simp only [Fintype.sum_option, G, w, Option.elim]
      have e4 : ∑ Γ : S, (X.ord (localEquationFn hv Γ.1) Γ'.genericPoint : ℝ) *
          ((m : ℝ) * (B Γ.1 : ℝ)) = (m : ℝ) * (B Γ' : ℝ) := by
        simp_rw [ord_localEquationFn hv _ hΓ']
        by_cases hS : Γ' ∈ S
        · rw [Finset.sum_eq_single ⟨Γ', hS⟩]
          · simp
          · rintro ⟨Γ, hΓS⟩ - hne
            have : Γ' ≠ Γ := fun h => hne (Subtype.ext h.symm)
            simp [this]
          · simp
        · have hB : B Γ' = 0 := Finsupp.notMem_support_iff.mp hS
          rw [hB, Rat.cast_zero, mul_zero]
          refine Finset.sum_eq_zero fun Γ _ => ?_
          have : Γ' ≠ Γ.1 := fun h => hS (h ▸ Γ.2)
          simp [this]
      rw [e4]
      have e3' : (Γ'.ordForm τ : ℝ) + (m : ℝ) * (B Γ' : ℝ) = 0 := by
        have := congrArg (fun q : ℚ => (q : ℝ)) e3
        push_cast at this
        simpa [DivisorWithCoeffs.coeff_apply] using this
      have e1' : (Γ'.ordForm τ : ℝ) = X.ord cτ Γ'.genericPoint + (m : ℝ) * NΓ := by
        exact_mod_cast e1
      have e2' : (0 : ℝ) = X.ord cσ Γ'.genericPoint + NΓ := by
        exact_mod_cast (by simpa using e2)
      linear_combination e3' - e1' + (m : ℝ) * e2'
  simp only [Fintype.sum_option, G, w, Option.elim] at key
  simp_rw [ord_functionFieldMap_localEquationFn hv E hE] at key
  have h1 : ((m : ℤ) : ℝ) * (c : ℝ) = (E.Y.ord (functionFieldMap E.f cτ) E.E.genericPoint : ℝ) +
      (m : ℝ) * N := by
    have := hN m τ hτ.1
    have h1' : (m : ℚ) * c = ((E.Y.ord (functionFieldMap E.f cτ) E.E.genericPoint : ℤ) : ℚ) +
        (m : ℚ) * N := by
      rw [hτc, this]; push_cast; ring
    have := congrArg (fun q : ℚ => (q : ℝ)) h1'
    push_cast at this ⊢
    linear_combination this
  have h2 : (1 : ℝ) = (E.Y.ord (functionFieldMap E.f cσ) E.E.genericPoint : ℝ) + N := by
    have := hN 1 σ hσ0
    rw [hσE] at this
    exact_mod_cast (by simpa using this)
  have hmult : ((B.multiplicityAt x : ℚ) : ℝ) =
      ∑ Γ : S, (((Γ.1.multiplicityAt x).toNat : ℤ) : ℝ) * (B Γ.1 : ℝ) := by
    rw [DivisorWithCoeffs.multiplicityAt, Finsupp.sum, Rat.cast_sum]
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun Γ _ => ?_
    simp [nsmul_eq_mul]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hfin : (m : ℝ) * (c : ℝ) = (m : ℝ) * ((1 : ℝ) - ((B.multiplicityAt x : ℚ) : ℝ)) := by
    rw [hmult]
    have e5 : ∑ Γ : S, (((Γ.1.multiplicityAt x).toNat : ℤ) : ℝ) * ((m : ℝ) * (B Γ.1 : ℝ)) =
        (m : ℝ) * ∑ Γ : S, (((Γ.1.multiplicityAt x).toNat : ℤ) : ℝ) * (B Γ.1 : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    push_cast at h1
    linear_combination h1 - (m : ℝ) * h2 + key - e5
  exact_mod_cast mul_left_cancel₀ hm'.ne' hfin

/-- Existence of the log discrepancy `2 - mult_{η_V} B` of a proper realization of `v_V`. -/
private theorem exists_isLogDiscrepancy_two_sub_multiplicityAt
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} (hB : MMP.Mori.IsPair sX B)
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v)
    (E : MMP.Mori.DivisorOver k sX) (hEp : IsProper E.f) (hE : E.valuation = v) :
    ∃ n : ℕ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) E
        (2 - ((B.multiplicityAt V.isIrreducible.genericPoint : ℚ) : ℝ)) := by
  obtain ⟨n, K, hK, -⟩ := hB.2
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB hK E
  have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hEp
  rw [discrepancy_eq hv E hE hc] at h
  refine ⟨n, ?_⟩
  convert h using 1
  push_cast
  ring

/-- **The log discrepancy of the generic blowup valuation.** Let `(X, B)` be a pair over a field
of characteristic zero, `V ⊆ X` an irreducible surface of the fourfold `X` with `X` smooth at
`η_V`, and `v = v_V` its generic blowup valuation. Then for every divisor `E` over `X`, proper
over `X`, with valuation `v_V`, `a(E; X, B) = 2 - ∑_h m_h b_h`, where `B = ∑_h b_h B_h` and
`m_h = mult_{η_V} B_h`: this value is a log discrepancy of `E`, and every log discrepancy of `E`
equals it. -/
@[mmp "lem_oai4_c3_generic_blowup_discrepancy"]
public theorem IsSurfaceGenericBlowupValuation.isLogDiscrepancy_two_sub_multiplicityAt
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} (hB : MMP.Mori.IsPair sX B)
    {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation sX V v)
    (E : MMP.Mori.DivisorOver k sX) (hEp : IsProper E.f) (hE : E.valuation = v) :
    (∃ n : ℕ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) E
        (2 - ((B.multiplicityAt V.isIrreducible.genericPoint : ℚ) : ℝ))) ∧
      ∀ (n : ℕ) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) E a →
          a = 2 - ((B.multiplicityAt V.isIrreducible.genericPoint : ℚ) : ℝ) := by
  obtain ⟨n₀, h₀⟩ := exists_isLogDiscrepancy_two_sub_multiplicityAt hB hv E hEp hE
  exact ⟨⟨n₀, h₀⟩, fun n a ha => MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h₀⟩

/-! ### Adding a multiple of a prime divisor to the boundary on a smooth variety -/

/-- On a smooth variety, adding `c P` to the boundary lowers a log discrepancy by `c` times the
coefficient of `E` in the pull-back of `P`. -/
private theorem isLogDiscrepancy_add_single {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {n : ℕ} {B : RDivisor X} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) (P : MMP.Mori.PrimeDivisor X) (c : ℝ) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    ∃ P' : Divisor D.Y,
      (∃ hB, MMP.Mori.Divisor.IsPullback D.f (Finsupp.single P 1 : Divisor X) hB P') ∧
      MMP.Intersection.IsLogDiscrepancy sX n (B + Finsupp.single P c) D
        (a - c * (P'.coeff D.E : ℝ)) := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have := D.isBirationalMorphism.isDominant
  have : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  have hC₀ : Divisor.IsCartier (Finsupp.single P 1 : Divisor X) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P
  have hB₀ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f
    (Finsupp.single P (1 : ℤ) : Divisor X)
  obtain ⟨C₀', hC₀'⟩ := hC₀.exists_isPullback hB₀
  refine ⟨C₀', ⟨hB₀, hC₀'⟩, hnv, hprop, ω, hω0, hK, m + 1, Fin.snoc r c,
    Fin.snoc C (Finsupp.single P 1), Fin.snoc C' C₀', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hC₀
    · simpa using hC j
  · intro Γ
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, DivisorWithCoeffs.coeff_add, ← hrel Γ]
    have : ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single P (1 : ℤ) : Divisor X) Γ : ℤ) : ℝ) =
        (if P = Γ then 1 else 0) := by
      change ((Finsupp.single P (1 : ℤ)) Γ : ℝ) = _
      rw [Finsupp.single_apply]
      split_ifs <;> simp
    rw [this]
    have h2 : DivisorWithCoeffs.coeff (Finsupp.single P c : RDivisor X) Γ =
        if P = Γ then c else 0 := by
      change (Finsupp.single P c) Γ = _
      rw [Finsupp.single_apply]
    rw [h2]
    split_ifs <;> simp [add_assoc]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · refine ⟨by simpa using hB₀, ?_⟩
      simpa using hC₀'
    · simpa using hpb j
  · rw [Fin.sum_univ_castSucc, ha]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- On a smooth variety, adding `∑_{P ∈ s} c_P P` to the boundary lowers a log discrepancy by
`∑_{P ∈ s} c_P μ_P`, where `μ_P` is the coefficient of `E` in the pull-back of `P`. -/
private theorem isLogDiscrepancy_add_sum {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {n : ℕ} {B : RDivisor X} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) (s : Finset (MMP.Mori.PrimeDivisor X))
    (c μ : MMP.Mori.PrimeDivisor X → ℝ)
    (hμ : haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      ∀ P ∈ s, ∀ P' : Divisor D.Y,
        (∃ hB, MMP.Mori.Divisor.IsPullback D.f (Finsupp.single P 1 : Divisor X) hB P') →
          (P'.coeff D.E : ℝ) = μ P) :
    MMP.Intersection.IsLogDiscrepancy sX n (B + ∑ P ∈ s, Finsupp.single P (c P)) D
      (a - ∑ P ∈ s, c P * μ P) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert P s hP ih =>
    obtain ⟨P', hP', h'⟩ := isLogDiscrepancy_add_single hsm
      (ih fun Q hQ => hμ Q (Finset.mem_insert_of_mem hQ)) P (c P)
    rw [hμ P (Finset.mem_insert_self _ _) P' hP'] at h'
    have e1 : B + ∑ Q ∈ insert P s, Finsupp.single Q (c Q) =
        B + ∑ Q ∈ s, Finsupp.single Q (c Q) + Finsupp.single P (c P) := by
      rw [Finset.sum_insert hP]; abel
    have e2 : a - ∑ Q ∈ insert P s, c Q * μ Q = a - ∑ Q ∈ s, c Q * μ Q - c P * μ P := by
      rw [Finset.sum_insert hP]; ring
    rwa [e1, e2]

/-! ### Coefficients of the pull-back of a prime divisor with invertible ideal -/

/-- The pull-back of `P` has coefficient `0` along `E` when `f(η_E) ∉ P`. -/
private theorem coeff_isPullback_single_eq_zero {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (P : MMP.Mori.PrimeDivisor Y)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉
        MMP.Mori.DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor Y)}
    {P' : Divisor X} (h : MMP.Mori.Divisor.IsPullback f (Finsupp.single P 1 : Divisor Y) hB P')
    (E : MMP.Mori.PrimeDivisor X) (hE : f E.genericPoint ∉ P.support) : P'.coeff E = 0 := by
  obtain ⟨N, hN, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder P hP h E
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap,
    (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support P.idealSheaf _).2 hE,
    Ideal.map_top, MMP.Threefold.Resolution.idealOrder_top] at hN
  rw [hc]
  obtain rfl : N = 0 := by exact_mod_cast hN.symm
  simp

/-- If `z` generates the ideal of `P` at `x = f(η_E)` and `v_E(z) = exp (-m)`, the pull-back of
`P` has coefficient `m` along `E`. -/
private theorem coeff_isPullback_single_eq_of_stalk_eq_span {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {f : X ⟶ Y} [IsDominant f] (P : MMP.Mori.PrimeDivisor Y)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉
        MMP.Mori.DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor Y)}
    {P' : Divisor X} (h : MMP.Mori.Divisor.IsPullback f (Finsupp.single P 1 : Divisor Y) hB P')
    (E : MMP.Mori.PrimeDivisor X) {x : Y} (hx : f E.genericPoint = x) (z : Y.presheaf.stalk x)
    (hz : IdealSheafData.stalk P.idealSheaf x = Ideal.span {z}) (m : ℤ)
    (hm : E.valuationOver f (algebraMap _ Y.functionField z) = WithZero.exp (-m)) :
    P'.coeff E = m := by
  subst hx
  obtain ⟨N, hN, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder P hP h E
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap, hz, Ideal.map_span,
    Set.image_singleton] at hN
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, functionFieldMap_algebraMap_stalk] at hm
  set g : E.localRing := (f.stalkMap E.genericPoint).hom z with hgdef
  have := E.isDiscreteValuationRing_localRing
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hm
    exact WithZero.exp_ne_zero hm.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨K, u, hgu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
  rw [hgu, MMP.Threefold.Resolution.idealOrder_span_unit_mul_pow hϖ u K] at hN
  have hu : E.divisorialValuation (algebraMap E.localRing X.functionField u) = 1 := by
    refine le_antisymm ((E.divisorialValuation_le_one_iff _).2 ⟨u, rfl⟩) (not_lt.1 fun hlt => ?_)
    exact (IsLocalRing.mem_maximalIdeal _).1
      ((E.divisorialValuation_algebraMap_lt_one_iff _).1 hlt) u.isUnit
  rw [hgu, map_mul, map_mul, hu, one_mul, map_pow, map_pow,
    E.divisorialValuation_algebraMap_of_irreducible hϖ, ← WithZero.exp_nsmul] at hm
  have hK : (K : ℤ) = m := by
    simpa only [nsmul_eq_mul, mul_neg, mul_one, neg_inj] using WithZero.exp_injective hm
  have hKN : K = N := by exact_mod_cast hN
  rw [hc, ← hKN, hK]

/-! ### The log-smooth formula -/

/-- A divisorial valuation proper over `X` lifts along a log-smooth datum to `W`. -/
private theorem exists_divisorOver_of_comap_eq {k : Type u} [Field k] {X W : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {B : QDivisor X} {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T)
    (D : DivisorOver k sX) (hD : IsProper D.f)
    (ξ : Valuation W.functionField ℤᵐ⁰)
    (hξ : haveI := hπ.isBirationalMorphism.isDominant;
      ξ.comap (functionFieldMap π) = D.valuation) :
    ∃ D' : DivisorOver k (π ≫ sX), IsProper D'.f ∧ ξ = D'.valuation := by
  haveI := hπ.isBirationalMorphism.isDominant
  have hbW := hπ.isBirationalMorphism.functionFieldMap_bijective
  -- `ξ` dominates the local ring of a point of `W` (valuative criterion for `π`)
  obtain ⟨x, h1, h2⟩ : ∃ x : W, (∀ a : W.presheaf.stalk x,
      ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
    have hgp : IsProper π := hπ.isProjective.isProper
    set z := D.f D.E.genericPoint
    have hw : ∀ b : X.presheaf.stalk z,
        ξ (functionFieldMap π (algebraMap _ X.functionField b)) =
          D.valuation (algebraMap _ X.functionField b) := by
      intro b
      have := congrArg (fun v => v (algebraMap _ X.functionField b)) hξ
      simpa only [Valuation.comap_apply] using this
    let R := ξ.valuationSubring
    let φ : X.presheaf.stalk z →+* R :=
      ((functionFieldMap π).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
        fun b => (ξ.mem_valuationSubring_iff _).2 (by
          rw [RingHom.comp_apply, hw]
          exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
    have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
    have hex : ValuativeCriterion.Existence π := by
      have h : @IsProper _ _ π := hgp
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1.existence
    let S : ValuativeCommSq π :=
      { R := R
        K := W.functionField
        i₁ := W.fromSpecStalk (genericPoint W)
        i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
        commSq := ⟨by
          rw [← functionFieldMap_fromSpecStalk π,
            ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
            ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
          rfl⟩ }
    obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
        W.fromSpecStalk (genericPoint W) := hl₁
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
    let f := Scheme.stalkClosedPointTo l
    have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
        W.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (W.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hfa : ∀ a : W.presheaf.stalk x,
        algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hf).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hfa]; exact (f.hom a).2
    · rw [hfa]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))
  -- `ξ` is a divisor of `k(W)`: `ord_E` on `D.Y`, along `k(W) ≅ k(X) ≅ k(D.Y)`
  haveI : AlgebraicGeometry.IsVariety k (π ≫ sX) := hπ.isNormalVariety.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (π ≫ sX) ξ := by
    haveI := D.isIntegral
    haveI := D.isNormal
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (π ≫ sX)
    letI := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX π hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap π s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap π s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap π s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (π ≫ sX) hdiv x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv.symm⟩

/-- If `T` is reduced and `B` is supported in `T`, then `B + ∑_{P ∈ T} (1 - b_P) P = T`. -/
private theorem toRDivisor_add_sum_single_one_sub {W : Scheme.{u}} {T : Divisor W}
    {B : QDivisor W} (hT : MMP.Intersection.IsReducedEffective T) (hB : B.support ⊆ T.support) :
    QDivisor.toRDivisor B + ∑ P ∈ T.support, Finsupp.single P (1 - (B.coeff P : ℝ)) =
      Divisor.toRDivisor T := by
  classical
  refine Finsupp.ext fun P => ?_
  have e1 : (QDivisor.toRDivisor B) P = (B P : ℝ) := rfl
  have e2 : (Divisor.toRDivisor T) P = (T P : ℝ) := rfl
  rw [Finsupp.add_apply, e1, e2, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with hPT
  · have hT1 : T P = 1 := (hT P).resolve_left (Finsupp.mem_support_iff.1 hPT)
    change (B.coeff P : ℝ) + (1 - (B.coeff P : ℝ)) = ((T P : ℤ) : ℝ)
    rw [hT1]; push_cast; ring
  · have hBP : B P = 0 := Finsupp.notMem_support_iff.1 fun h => hPT (hB h)
    rw [Finsupp.notMem_support_iff.1 hPT, hBP]
    simp

/-- A point lies in `sncComplement T S` iff it avoids every component of `T` not containing `S`. -/
private theorem mem_sncComplement_iff {W : Scheme.{u}} (T : Divisor W) (S : Set W) (x : W) :
    x ∈ sncComplement T S ↔ ∀ E ∈ T.support, ¬ S ⊆ E.support → x ∉ E.support := by
  change x ∈ (sncComplement T S : Set W) ↔ _
  simp [sncComplement]

/-- The inclusion of an open subscheme `U` is biregular over `U`. -/
private theorem isBiregular_ι_self {W : Scheme.{u}} (U : W.Opens) : IsBiregular U.ι U := by
  have h1 : U.ι ∣_ U = (U.ι ⁻¹ᵁ U).ι := by
    rw [← cancel_mono U.ι, morphismRestrict_ι]
  show IsIso (U.ι ∣_ U)
  rw [h1, U.ι_preimage_self, isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
  change y ∈ Set.range (⊤ : U.toScheme.Opens).ι
  rw [Scheme.Opens.range_ι]
  trivial

/-- On the open `W° = sncComplement T S`, a reduced effective divisor `T` restricts to the sum of
its components containing `S`. -/
private theorem toRDivisor_restrictOpen_sncComplement {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {T : Divisor W}
    (hT : MMP.Intersection.IsReducedEffective T) (S : Set W) :
    QDivisor.toRDivisor ((Divisor.toQDivisor T).restrictOpen (sncComplement T S)) =
      Divisor.toRDivisor (inverseTransformDivisor (sncComplement T S).ι
        (MMP.Intersection.reducedDivisorOf (sncIndexSet T S))) := by
  classical
  set U := sncComplement T S
  have hbireg : ∀ y : U.toScheme, U.ι y ∈ biregularLocus U.ι :=
    fun y => le_biregularLocus (isBiregular_ι_self U) y.2

  refine Finsupp.ext fun F => ?_
  set P := OpenWeilRestriction.primeDivisorMap U.ι F with hPdef
  have hinv : inverseTransformPrimeDivisor U.ι P = some F :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι F).symm (hbireg _)
  have huniq : ∀ P'', inverseTransformPrimeDivisor U.ι P'' = some F → P'' = P := by
    intro P'' hP''
    have h1 := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hP'').1
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [hPdef, OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact h1.symm
  have e1 : (QDivisor.toRDivisor ((Divisor.toQDivisor T).restrictOpen U)) F =
      ((T P : ℤ) : ℝ) := by
    change (((T P : ℤ) : ℚ) : ℝ) = _
    push_cast; rfl
  have e2 : (Divisor.toRDivisor (inverseTransformDivisor U.ι
      (MMP.Intersection.reducedDivisorOf (sncIndexSet T S)))) F =
      (((MMP.Intersection.reducedDivisorOf (sncIndexSet T S)) P : ℤ) : ℝ) := by
    change ((DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor U.ι) _ F : ℤ) : ℝ) = _
    rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hinv huniq]
  rw [e1, e2]
  congr 1
  have hc' := MMP.Intersection.coeff_reducedDivisorOf (sncIndexSet T S) P
  rw [DivisorWithCoeffs.coeff_apply] at hc'
  rw [hc']
  have hPU : P.genericPoint ∈ U := by
    rw [hPdef, OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact F.genericPoint.2
  have hPmem : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  by_cases hPT : P ∈ T.support
  · have hPJ : P ∈ sncIndexSet T S := by
      refine Finset.mem_filter.2 ⟨hPT, ?_⟩
      by_contra hZP
      exact (mem_sncComplement_iff T S _).1 hPU P hPT hZP hPmem
    rw [if_pos hPJ]
    exact (hT P).resolve_left (Finsupp.mem_support_iff.1 hPT)
  · have hPJ : P ∉ sncIndexSet T S := fun h => hPT (Finset.mem_filter.1 h).1
    rw [if_neg hPJ]
    exact Finsupp.notMem_support_iff.1 hPT

/-- The log-smooth formula, once the centre `Z` of `ξ` on `W` is known. -/
private theorem logSmoothFormula_of_isCentre {k : Type u} [Field k] [PerfectField k]
    {X W : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {B : QDivisor X} {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) {n : ℕ}
    (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j ∈ T.support, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    (D : DivisorOver k sX) (hD : IsProper D.f) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a)
    (ξ : Valuation W.functionField ℤᵐ⁰)
    (hξ : haveI := hπ.isBirationalMorphism.isDominant;
      ξ.comap (functionFieldMap π) = D.valuation)
    (Z : IrreducibleCloseds W) (hZ : MMP.Intersection.IsCentre k (π ≫ sX) ξ Z) :
      ∃ e : ℝ, IsReducedSNCDiscrepancy (π ≫ sX) T ξ e ∧
        ∀ (z : sncIndexSet T Z → W.presheaf.stalk Z.isIrreducible.genericPoint)
          (m : sncIndexSet T Z → ℤ),
          (∀ j, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
            Ideal.span {z j}) →
          (∀ j, ξ (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j)) →
          a = ∑ j, (m j : ℝ) * aT j + e := by
  classical
  have hZ₀ := hZ
  obtain ⟨D', hD', hξD', hZD'⟩ := hZ
  subst hZD'
  haveI := hπ.isBirationalMorphism.isDominant
  have hX : IsNormalVariety k sX := ha.1
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  have hsm : IsSmoothScheme (π ≫ sX) := hπ.isSmoothScheme
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (π ≫ sX) := hW.1
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : CompactSpace W := (hW.1.toQuasiCompact).compactSpace_of_compactSpace
  -- dimensions
  have hdimX : topologicalKrullDim X = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  have hdimW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX)
      hπ.isBirationalMorphism).symm.trans hdimX
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := D.isIntegral
    haveI : AlgebraicGeometry.IsVariety k (D.f ≫ sX) := D.isNormalVariety.1
    have hY : topologicalKrullDim D.Y = ((0 : ℕ) : WithBot ℕ∞) := by
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (D.f ≫ sX)
        D.isBirationalMorphism, hdimX]
    let _ : PartialOrder D.Y := specializationOrder D.Y
    have h1 : Order.krullDim D.Y = ((0 : ℕ) : WithBot ℕ∞) := by
      rw [← hY]
      exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := D.Y))).symm
    have h2 := Order.coheight_le_krullDim D.E.genericPoint
    rw [D.E.coheight_genericPoint, h1] at h2
    exact absurd h2 (by decide)
  -- the crepant boundary and a canonical divisor of `X`
  obtain ⟨n₀, K, BW, hcb, hBWT⟩ := hπ.crepant
  obtain ⟨F₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimW hn0
  have hK₀ : K.IsCanonicalDivisor sX n₀ := (hcb F₀).2.1
  obtain rfl : n = n₀ := by exact_mod_cast hdimX.symm.trans hK₀.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := hπ.isKltPair.1.isPair
  -- `a = 1 + c`, `c` the Kollár–Mori discrepancy
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK₀ D
  have hac : a = 1 + (c : ℝ) :=
    MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha
  -- crepant transfer to `(W, B_W)`
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sX) hsm hdimW
  obtain ⟨-, hcr⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP π hW
    hπ.isBirationalMorphism hK₀ hKW (Or.inl hcb)
  have hvD : D.valuation = D'.valuation.comap (functionFieldMap π) := by
    rw [← hξD']; exact hξ.symm
  have hcW := (hcr D' D hvD c).2 hc
  have hLW := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcW hD'
  -- the coefficients of `B_W`
  have haTj : ∀ j ∈ T.support, aT j = 1 - (BW.coeff j : ℝ) := fun j hj => by
    rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy (hcb j) (haT j hj)]
    push_cast; ring
  have hBW : QDivisor.toRDivisor BW + ∑ j ∈ T.support, Finsupp.single j (aT j) =
      Divisor.toRDivisor T := by
    rw [Finset.sum_congr rfl fun j hj => by rw [haTj j hj]]
    exact toRDivisor_add_sum_single_one_sub hπ.isReducedEffective hBWT
  -- the coefficients of the pull-backs of the `Tⱼ` along `E`
  haveI := D'.isIntegral
  haveI := D'.isLocallyNoetherian
  haveI := D'.isNormal
  haveI := D'.isDominant
  haveI : CompactSpace D'.Y :=
    (D'.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  let μ : MMP.Mori.PrimeDivisor W → ℝ := fun P =>
    ((Divisor.pullback (Finsupp.single P 1 : Divisor W)
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f _)).coeff D'.E : ℝ)
  have hμP : ∀ (P : MMP.Mori.PrimeDivisor W) (P' : Divisor D'.Y),
      (∃ hB, MMP.Mori.Divisor.IsPullback D'.f (Finsupp.single P 1 : Divisor W) hB P') →
        (P'.coeff D'.E : ℝ) = μ P := by
    rintro P P' ⟨hB, hP'⟩
    simp only [μ]
    rw [hP'.eq (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P)
      (Divisor.isPullback_pullback _ _)]
  -- shift the boundary from `B_W` to `T`
  have hLT := isLogDiscrepancy_add_sum hsm hLW T.support aT μ (fun P _ P' hP' => hμP P P' hP')
  rw [hBW] at hLT
  -- the generic point of the centre
  have hgen : D'.center.isIrreducible.genericPoint = D'.f D'.E.genericPoint :=
    (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).eq
      (D'.center_eq_closure_genericPoint).symm
  have hηZ : ∀ E ∈ T.support, ¬ (D'.center : Set W) ⊆ E.support →
      D'.center.isIrreducible.genericPoint ∉ E.support := by
    intro E _ hE hmem
    apply hE
    rw [← (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed)]
    refine closure_minimal (Set.singleton_subset_iff.2 hmem) ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
    exact isClosed_closure
  set U := sncComplement T (D'.center : Set W)
  have hηU : D'.center.isIrreducible.genericPoint ∈ U := (mem_sncComplement_iff _ _ _).2 hηZ
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hηmem : D'.center.isIrreducible.genericPoint ∈ (D'.center : Set W) :=
    (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).mem
  -- localize the pair `(W, T)` to `U`
  have hPWT : IsPairWith (π ≫ sX) n KW (Divisor.toQDivisor T) :=
    ⟨hW, hKW, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨cT, hcT⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPWT.isPair hKW D'
  have heT : 1 + (c : ℝ) - ∑ j ∈ T.support, aT j * μ j = 1 + (cT : ℝ) := by
    refine MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hcT ?_
    rwa [QDivisor.toRDivisor_toQDivisor]
  obtain ⟨hYU, hfU, E', hE', hvU, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPWT D' U ⟨_, hηmem, hηU⟩
  have hcU := (hiff cT).1 hcT
  have hpU : IsProper (D'.f ∣_ U) := by
    haveI : IsProper D'.f := hD'
    infer_instance
  have hLU := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcU hpU
  -- assemble
  refine ⟨1 + (cT : ℝ), ⟨hW.1, hsm, hπ.isReducedEffective, hπ.isSNC, D'.center, hZ₀, ⟨⟨_, hηU⟩⟩,
    n, ⟨_, D'.f ∣_ U, hYU, hfU, E'⟩, hpU, ?_, ?_⟩, ?_⟩
  · rwa [hξD']
  · rwa [← toRDivisor_restrictOpen_sncComplement hπ.isReducedEffective]
  · intro z m hz hm
    have hμm : ∀ j : sncIndexSet T (D'.center : Set W), μ j = (m j : ℝ) := by
      intro j
      have hc := coeff_isPullback_single_eq_of_stalk_eq_span (j : MMP.Mori.PrimeDivisor W)
        (MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf (π ≫ sX) hsm j)
        (Divisor.isPullback_pullback (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _)
          (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f _))
        D'.E hgen.symm (z j) (hz j) (m j) (by rw [hξD'] at hm; exact hm j)
      simp only [μ]
      exact_mod_cast hc
    have hμ0 : ∀ j ∈ T.support, j ∉ sncIndexSet T (D'.center : Set W) → aT j * μ j = 0 := by
      intro j hjT hjJ
      have hZj : ¬ (D'.center : Set W) ⊆ j.support := fun h => hjJ (Finset.mem_filter.2 ⟨hjT, h⟩)
      have hc := coeff_isPullback_single_eq_zero j
        (MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf (π ≫ sX) hsm j)
        (Divisor.isPullback_pullback (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _)
          (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f _))
        D'.E (by rw [← hgen]; exact hηZ j hjT hZj)
      simp [μ, hc]
    have hsum : ∑ j ∈ T.support, aT j * μ j =
        ∑ j : sncIndexSet T (D'.center : Set W), (m j : ℝ) * aT j := by
      have h2 : ∑ j ∈ sncIndexSet T (D'.center : Set W), aT j * μ j =
          ∑ j : sncIndexSet T (D'.center : Set W), (m j : ℝ) * aT j := by
        rw [← Finset.sum_coe_sort (sncIndexSet T (D'.center : Set W))]
        exact Finset.sum_congr rfl fun j _ => by rw [hμm j, mul_comm]
      rw [← h2]
      exact (Finset.sum_subset (Finset.filter_subset _ _) hμ0).symm
    rw [hac, ← hsum]
    linarith

section LogSmooth

variable {k : Type u} [Field k] [PerfectField k] {X W : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- **The log-smooth formula.** Let `(π, T)` be a log-smooth datum for a klt pair `(X, B)`, with
`aⱼ = a(ord_{Tⱼ}; X, B)` for the components `Tⱼ` of `T`, and let `ξ` be the normalized divisorial
valuation of a proper divisor `D` over `X`, viewed as a valuation of `k(W)` along `π`. Then `ξ`
has a centre `Z = c_W(ξ)` on `W`, and with `J(ξ)` the components of `T` containing `Z`,
`a(ξ; X, B) = ∑_{j ∈ J(ξ)} ξ(Tⱼ) aⱼ + e_T(ξ)`, where `ξ(Tⱼ) = mⱼ` for `ξ zⱼ = exp (-mⱼ)` and
`zⱼ` a local equation of `Tⱼ` at the generic point of `Z`. -/
@[mmp "lem_oai4_snc_valuations"]
public theorem IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy
    {B : QDivisor X} {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) {n : ℕ}
    (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j ∈ T.support, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    (D : DivisorOver k sX) (hD : IsProper D.f) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a)
    (ξ : Valuation W.functionField ℤᵐ⁰)
    (hξ : haveI := hπ.isBirationalMorphism.isDominant;
      ξ.comap (functionFieldMap π) = D.valuation) :
    ∃ Z : IrreducibleCloseds W, MMP.Intersection.IsCentre k (π ≫ sX) ξ Z ∧
      ∃ e : ℝ, IsReducedSNCDiscrepancy (π ≫ sX) T ξ e ∧
        ∀ (z : sncIndexSet T Z → W.presheaf.stalk Z.isIrreducible.genericPoint)
          (m : sncIndexSet T Z → ℤ),
          (∀ j, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
            Ideal.span {z j}) →
          (∀ j, ξ (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j)) →
          a = ∑ j, (m j : ℝ) * aT j + e := by
  obtain ⟨D', hD', hξD'⟩ := exists_divisorOver_of_comap_eq sX hπ D hD ξ hξ
  have hZ : MMP.Intersection.IsCentre k (π ≫ sX) ξ D'.center := ⟨D', hD', hξD', rfl⟩
  exact ⟨D'.center, hZ, logSmoothFormula_of_isCentre sX hπ aT haT D hD ha ξ hξ _ hZ⟩

end LogSmooth

end MMP.Fourfold
