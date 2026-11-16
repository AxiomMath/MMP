module

public import MMP.AlgebraicGeometry.Vanishing.RelativeKawamataViehweg
public import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous

/-!
# Higher direct images of `𝒪_Y(⌈B_f⌉)` on a log resolution of a klt pair

Let `(X, Δ)` be a klt pair with `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective, let `f : Y ⟶ X` be a projective log resolution of
`(X, Δ)`, and let `B = B_f = ∑_E max {a(E, X, Δ), 0} E` be the positive part of the discrepancy.
Then `R^j f_* 𝒪_Y(⌈B⌉) = 0` for every `j > 0`.

Writing `A = A_f` for the negative part, `⌈B⌉ - K_Y ≡ -f^*(K_X + Δ) + A + {-B}`, where `A + {-B}`
has snc support and coefficients in `[0, 1)` because `(X, Δ)` is klt; twisting by `r f^*H` for an
ample `H` on `X` and applying relative Kawamata–Viehweg vanishing
(`MMP.Mori.isZero_rightDerived_pushforward_exteriorPower_tensor_divisorialSheaf`) together with
the projection formula gives the vanishing.

## Main results

* `MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_roundUp`: `R^j f_* 𝒪_Y(⌈B_f⌉) = 0`
  for `j > 0`.
* `MMP.Mori.DivisorWithCoeffs.isSNC_of_forall_genericPoint_mem`: a `ℚ`-divisor whose components
  have generic points in an snc subset is snc.
* `MMP.Mori.IsDiscrepancy.exists_eq_neg_coeff_of_not_isExceptional`: a non-exceptional divisor
  over `(X, Δ)` lying over the prime divisor `P` has discrepancy `-coeff_P(Δ)`.
* `MMP.Mori.IsDiscrepancy.genericPoint_mem_of_ne_zero`: a divisor on `Y` with nonzero
  discrepancy has its generic point in `Ex(f) ∪ f⁻¹(Supp Δ)`.
* `MMP.Mori.isCanonicalDivisor_divisorOfForm_pullback`: on a smooth birational model, `div f^*ω`
  is canonical when `div ω` is.

## Implementation notes

* `X` carries its structure morphism `sX : X ⟶ Spec k`, and `Y` the composite `f ≫ sX`.
* A projective log resolution is `MMP.Mori.IsLogResolution` of the `ℝ`-divisor underlying `Δ`
  together with `AlgebraicGeometry.IsProjective f`.
* `B = B_f` is given by `MMP.Mori.IsDiscrepancyPositivePart`, which needs `Y` to be a normal
  variety over `k`; this is the hypothesis `hY`.
* `R^j f_*` is the `j`-th right derived functor of `Scheme.Modules.pushforward f`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Theorem 5.22.
-/

@[expose] public section

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry

universe u

/-- A `ℚ`-divisor whose components have their generic points in an snc subset `S` is snc: each
such component is one of the prime divisors whose union is `S`. -/
theorem DivisorWithCoeffs.isSNC_of_forall_genericPoint_mem {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {S : TopologicalSpace.Closeds Y} (hS : IsSNCSubset sY S) (D : QDivisor Y)
    (hD : ∀ E, D E ≠ 0 → E.genericPoint ∈ S) : D.IsSNC sY := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℚ) sY hsm).of_support_subset
      fun E hE => ?_
    have h := hD E (Finsupp.mem_support_iff.1 hE)
    rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at h
    exact h.elim
  · refine hsnc.of_support_subset fun E hE => ?_
    have h := hD E (Finsupp.mem_support_iff.1 hE)
    rw [← SetLike.mem_coe, ← hs, Set.mem_iUnion₂] at h
    obtain ⟨E', hE', hm⟩ := h
    obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hm
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, hE']

/-- The discrepancy of a non-exceptional divisor `(Y, f, E)` over a pair `(X, Δ)` is
`-coeff_P(Δ)`, where `P` is the prime divisor of `X` with generic point `f(η_E)`. -/
theorem IsDiscrepancy.exists_eq_neg_coeff_of_not_isExceptional {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) (hE : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint = P.genericPoint ∧ a = -Δ.coeff P := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hmτ⟩ := ha
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 P hPU
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  refine ⟨P, hx, mul_left_cancel₀ hm0 ?_⟩
  linear_combination hmτ + e

/-- A divisor over `(X, Δ)` with nonzero discrepancy is exceptional or lies over `Supp Δ`. -/
theorem IsDiscrepancy.genericPoint_mem_of_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {Y : Scheme.{u}} {f : Y ⟶ X} {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {E : MMP.Mori.PrimeDivisor Y} {a : ℚ} (ha : IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, E⟩ a)
    (ha0 : a ≠ 0) :
    E.genericPoint ∈ exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous := by
  by_cases hex : (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet E hex
      (MMP.Flips.primeDivisor_genericPoint_mem_support E))
  obtain ⟨Q, hfE, hQ⟩ := ha.exists_eq_neg_coeff_of_not_isExceptional hex
  refine Or.inr (DivisorWithCoeffs.mem_supp_iff.2 ⟨Q, ?_, ?_⟩)
  · rw [QDivisor.coeff_toRDivisor, Rat.cast_ne_zero]
    rintro h
    exact ha0 (by rw [hQ, h, neg_zero])
  · exact hfE ▸ MMP.Flips.primeDivisor_genericPoint_mem_support Q

/-- On a smooth birational model `f : Y ⟶ X`, the pull-back `f^*ω` of a rational `n`-form with
canonical divisor `div ω` has canonical divisor. -/
theorem isCanonicalDivisor_divisorOfForm_pullback {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (hYsm : IsSmoothScheme (f ≫ sX)) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n := by
  have hn := hK.topologicalKrullDim_eq
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hf).symm.trans
      hn)
  exact hK₀.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
        hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0)

end MMP.Mori

section

/-!
## Proof: Higher direct images of `𝒪_Y(⌈B_f⌉)` on a log resolution of a klt pair

Let `(X, Δ)` be a klt pair, `X` projective over an algebraically closed field `k` of
characteristic zero, and `f : Y ⟶ X` a projective log resolution. Write `K_X = div ω` for a
rational top form `ω` and `K_Y = div f^*ω`. The discrepancies are the coefficients of
`C = K_Y - f^*(K_X + Δ)`, so `B = B_f` has coefficients `max (C_E, 0)`, and `-C` is the crepant
boundary; since the pair is klt every `C_E > -1`. Hence `Δ' = ⌈B⌉ - C = A_f + {-B_f}` has
coefficients in `[0, 1)`, and its support lies in `Ex(f) ∪ f⁻¹(Supp Δ)`, which is snc.

Choose an ample Cartier divisor `H` on `X`, an integer `m > 0` with `m (K_X + Δ) = C_X` Cartier,
and `r` with `(m r) H - C_X` ample. Its pull-back to `Y` is `m M` for
`M = r f^*H - f^*(K_X + Δ)`, which is therefore nef, and `⌈B⌉ - K_Y + r f^*H = M + Δ'`. Relative
Kawamata–Viehweg vanishing gives `R^j f_*(ω_Y ⊗ 𝒪_Y(⌈B⌉ - K_Y + r f^*H)) = 0` for `j > 0`. As
`ω_Y ≅ 𝒪_Y(K_Y)` on the smooth `Y`, this module is `𝒪_Y(⌈B⌉) ⊗ f^*𝒪_X(r H)`, and the projection
formula with the invertible `𝒪_X(r H)` gives `R^j f_* 𝒪_Y(⌈B⌉) = 0`.

## Implementation notes

The bound `C_E > -1` comes from `MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary`
applied to the crepant boundary `-C`, which treats exceptional and non-exceptional `E` at once;
so the effectivity of `Δ`, which the source uses to see that `Supp B_f ⊆ Ex(f)`, is not needed
for the vanishing.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Theorem 5.22
-/

namespace MMP.FourfoldProofs.Km5dKltLogResolutionVanishingProof

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel
open Stacks.Ample (IsInvertibleModule)
open Stacks.RelativeVeryAmple (tensorModules tensorModulesMapIso)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (tensorRightModules)

/-- If `-1 < c`, then `⌈max c 0⌉ - c` lies in `[0, 1)`: the coefficient of `A + {-B}` at a
divisor of discrepancy `c` over a klt pair. -/
private theorem ceil_max_zero_sub_mem_Ico {c : ℚ} (hc : -1 < c) :
    0 ≤ (⌈max c 0⌉ : ℚ) - c ∧ (⌈max c 0⌉ : ℚ) - c < 1 := by
  rcases le_or_gt 0 c with h | h
  · rw [max_eq_left h]
    exact ⟨by linarith [Int.le_ceil c], by linarith [Int.ceil_lt_add_one c]⟩
  · rw [max_eq_right h.le, Int.ceil_zero, Int.cast_zero]
    constructor <;> linarith

section AmpleTwist

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- A projective variety carries an ample Cartier divisor. -/
private theorem exists_isCartier_isAmple {k : Type} [Field k] (sY : Y ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] :
    ∃ H : Divisor Y, ∃ hH : H.IsCartier, H.IsAmple hH := by
  have hX := (AlgebraicGeometry.isProjectiveVariety_iff k sY).1 ‹_›
  haveI : IsIntegral Y := hX.1.toIsIntegral
  obtain ⟨-, L, hLinv, hLamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sY hX.2.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple Y L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY L hLamp
  obtain ⟨I, hI, -, -, n, hn, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint Y))
  obtain ⟨H, -, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor I hI
  haveI := hHc.isInvertibleModule_divisorialSheaf
  exact ⟨H, hHc, (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
    (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)⟩

/-- If `𝒪_Y(D) ≅ 𝒪(L)` and `𝒪_Y(E) ≅ 𝒪(E')` for Cartier divisors `L`, `E'`, then
`𝒪_Y(ND + E) ≅ 𝒪(NL + E')`. -/
private theorem nonempty_divisorialSheaf_nsmul_add_iso {D E : Divisor Y} (hD : D.IsCartier)
    (hE : E.IsCartier) {L E' : Y.CartierDivisor}
    (a : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf L)
    (b : E.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E') (N : ℕ) :
    Nonempty ((N • D + E).divisorialSheaf ≅
      MMP.CartierDivisor.sheaf (N • L + E')) := by
  induction N with
  | zero => exact ⟨eqToIso (by simp) ≪≫ b ≪≫ eqToIso (by simp)⟩
  | succ N ih =>
    obtain ⟨c⟩ := ih
    have h₁ : (N + 1 : ℕ) • D + E = (N • D + E) + D := by rw [succ_nsmul]; abel
    have h₂ : (N • L + E') + L = (N + 1 : ℕ) • L + E' := by rw [succ_nsmul]; abel
    exact ⟨eqToIso (by rw [h₁]) ≪≫ (((hD.nsmul N).add hE).divisorialSheafTensorIso hD).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso c).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso a ≪≫
      MMP.CartierDivisorSheaf.sheafMulIso _ _ ≪≫ eqToIso (by rw [h₂])⟩

/-- **Ample twists.** If `D` and `E` are Cartier divisors with `𝒪(D)` ample, then `𝒪(ND + E)`
is ample for all large `N`. -/
private theorem eventually_isAmple_nsmul_add [IsIntegral Y] {D E : Divisor Y} (hD : D.IsCartier)
    (hE : E.IsCartier) (hA : D.IsAmple hD) :
    ∀ᶠ N : ℕ in Filter.atTop, (N • D + E).IsAmple ((hD.nsmul N).add hE) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨L, ⟨a⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨E', ⟨b⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf E.divisorialSheaf
  have hL : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf L) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ a).1 hA
  filter_upwards [MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add L E' hL] with N hN
  obtain ⟨c⟩ := nonempty_divisorialSheaf_nsmul_add_iso hD hE a b N
  haveI := ((hD.nsmul N).add hE).isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ c).2 hN

end AmpleTwist

section Canonical

/-- On a smooth variety a canonical divisor `K` of dimension `n` has `𝒪_X(K) ≅ ⋀ⁿ Ω_{X/k}`:
the defining isomorphism lives on the smooth locus, which is all of `X`. -/
private lemma nonempty_divisorialSheaf_iso_exteriorPower {k : Type} [Field k] {X : Scheme.{0}}
    {f : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) :=
  MMP.Flips.nonempty_iso_of_restrict_iso hsm (hK.iso ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (smoothLocus f).ι).app _ ≪≫
      Scheme.Modules.exteriorPowerPullbackIso (smoothLocus f).ι _ n ≪≫
      (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
        (Scheme.Hom.etaleRelativeDifferentialsIso (smoothLocus f).ι f _ rfl)).symm)

end Canonical

section ProjectionFormula

/-- For an invertible `L` on `X`, vanishing of `R^j f_*(ℱ ⊗ f^*L) ≅ R^j f_*ℱ ⊗ L` (projection
formula) gives vanishing of `R^j f_*ℱ`. -/
private theorem isZero_rightDerived_pushforward_of_isZero_tensor_pullback {X Y : Scheme.{0}}
    (f : Y ⟶ X) (L : X.Modules) [IsInvertibleModule X L] (M : Y.Modules) (j : ℕ)
    (h : Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj
      (tensorModules Y M ((Scheme.Modules.pullback f).obj L)))) :
    Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj M) := by
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 inferInstance
  have : (tensorRightModules X L).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  exact (Limits.IsZero.of_full_of_faithful_of_isZero (tensorRightModules X L) _ ((h.of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ j).app _).symm).of_iso
      (Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso f L M j).symm)).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ j).app M)

end ProjectionFormula

end MMP.FourfoldProofs.Km5dKltLogResolutionVanishingProof

end

section

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km5dKltLogResolutionVanishingProof in
open Stacks.RelativeVeryAmple (tensorModulesMapIso) in
/-- Let `(X, Δ)` be a klt pair with `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective, let `f : Y ⟶ X` be a projective log resolution of
`(X, Δ)` and `B = B_f` the positive part of the discrepancy
(`MMP.Mori.IsDiscrepancyPositivePart`). Then `R^j f_* 𝒪_Y(⌈B⌉) = 0` for every `j > 0`. -/
@[mmp "lem_km5d_klt_log_resolution_vanishing"]
public theorem isZero_rightDerived_pushforward_divisorialSheaf_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (_hΔ : 0 ≤ Δ)
    {Y : Scheme.{0}} (f : Y ⟶ X) (hres : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hproj : IsProjective f) (hY : IsNormalVariety k (f ≫ sX)) {B : QDivisor Y}
    (hB : IsDiscrepancyPositivePart sX n K Δ f hY hres.isBirationalMorphism B)
    (j : ℕ) (hj : 0 < j) :
    haveI : IsLocallyNoetherian Y := hY.1.isLocallyNoetherian
    haveI : IsNormal Y := hY.2
    Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj
      B.roundUp.divisorialSheaf) := by
  haveI : IsLocallyNoetherian Y := hY.1.isLocallyNoetherian
  haveI : IsNormal Y := hY.2
  have hbir := hres.isBirationalMorphism
  have hP : IsPairWith sX n K Δ := hklt.1
  have hXp := (AlgebraicGeometry.isProjectiveVariety_iff k sX).1 ‹_›
  haveI : AlgebraicGeometry.IsVariety k sX := hXp.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsDominant f := hbir.isDominant
  haveI : IsProper f := hres.isProper
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hXp.2
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : LocallyOfFiniteType sX := hXp.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have hsm : IsSmoothScheme (f ≫ sX) := hres.isSmoothScheme
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  -- `K = div ω` for a rational top form `ω`, and `K_Y = div f^*ω`
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hP.1 hP.2.1
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hωK
  set KY := divisorOfForm (pullbackRationalPluriForms sX f ω) with hKY
  have hQ : (Divisor.toQDivisor (divisorOfForm ω) + Δ).IsQCartier := hP.2.2
  have hsupp := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier f hQ
  set P := QDivisor.pullback (f := f) (Divisor.toQDivisor (divisorOfForm ω) + Δ) hQ hsupp
    with hPdef
  set C : QDivisor Y := Divisor.toQDivisor KY - P with hCdef
  have hdisc : ∀ E : MMP.Mori.PrimeDivisor Y,
      IsDiscrepancy sX n (divisorOfForm ω) Δ ⟨Y, f, hY, hbir, E⟩ (C.coeff E) :=
    fun E => isDiscrepancy_coeff_divisorOfForm_sub_pullback hP.1 ω hω0 hP.2.1 Δ hQ f hY hbir E
  have hBC : ∀ E, B.coeff E = max (C.coeff E) 0 := fun E => by
    obtain ⟨a, ha, hBa⟩ := hB.2 E
    rw [hBa, ha.eq (hdisc E)]
  have hcrep : IsCrepantBoundary sX n (divisorOfForm ω) Δ f hY hbir (-C) := fun E => by
    simpa [DivisorWithCoeffs.coeff_neg] using hdisc E
  have hC1 : ∀ E, -1 < C.coeff E := fun E => by
    have := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary hklt hY hbir hcrep E
    rw [DivisorWithCoeffs.coeff_neg] at this
    linarith
  -- the boundary `Δ' = ⌈B⌉ - C = A + {-B}` has coefficients in `[0, 1)`
  set Δ' : QDivisor Y := Divisor.toQDivisor B.roundUp - C with hΔ'def
  have hΔ'E : ∀ E, Δ' E = ⌈max (C.coeff E) 0⌉ - C.coeff E := fun E => by
    rw [← hBC E]
    rfl
  have hΔ'01 : ∀ E, 0 ≤ Δ' E ∧ Δ' E < 1 := fun E => by
    rw [hΔ'E]
    exact ceil_max_zero_sub_mem_Ico (hC1 E)
  -- `Supp Δ' ⊆ Ex(f) ∪ f⁻¹(Supp Δ)`, which is snc
  have hΔ'snc : Δ'.IsSNC (f ≫ sX) := by
    refine DivisorWithCoeffs.isSNC_of_forall_genericPoint_mem hsm hres.isSNCSubset Δ' fun E hE => ?_
    exact (hdisc E).genericPoint_mem_of_ne_zero fun h => hE (by rw [hΔ'E, h]; simp)
  -- an ample Cartier divisor `H` on `X`; `Y` is projective
  obtain ⟨H, hHc, hHamp⟩ := exists_isCartier_isAmple sX
  haveI := hHc.isInvertibleModule_divisorialSheaf
  have hfp : IsProjectiveMorphism f := isProjectiveMorphism_of_isQuasiProjective f
    H.divisorialSheaf hHamp (isQuasiProjective_of_isProjective hproj)
  have hYp : IsProjectiveMorphism (f ≫ sX) := hfp.comp hXp.2
  haveI : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := ⟨hYp⟩
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  -- `m (K_X + Δ) = C_X` Cartier, with pull-back `D'`, so `D' = m f^*(K_X + Δ)`
  obtain ⟨m, hm, CX, hCX, hCXc⟩ := hQ.exists_pos
  obtain ⟨D', hD', hD'pb⟩ := QDivisor.isPullback_pullback (f := f) hQ hsupp m hm CX hCX hCXc
  -- `r H - (K_X + Δ)` is ample: `(m r) H - C_X` is ample
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.1 (eventually_isAmple_nsmul_add hHc hCXc.neg hHamp)
  have hmr : r ≤ m * r := Nat.le_mul_of_pos_left r hm
  have hEamp := hr (m * r) hmr
  -- the pull-back `G = f^*H`
  have hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f H
  obtain ⟨G, hG⟩ := hHc.exists_isPullback hHf
  -- `E_Y = (m r) G - D'` is the pull-back of the ample `E_X = (m r) H - C_X`
  have hdom : ∀ D : Divisor X, ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ D.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f
  have hEpb : ((m * r) • H + -CX).IsPullback f (hdom _) ((m * r) • G + -D') := by
    have h := ((hG.zsmul hHc ((m * r : ℕ) : ℤ) (hdom _)).add (hHc.zsmul _) (hCXc.zsmul _)
      (hdom _) (hD'pb.zsmul hCXc (-1) (hdom _))).of_eq (hB₂ := hdom ((m * r) • H + -CX))
      (by rw [natCast_zsmul, neg_one_zsmul])
    rwa [natCast_zsmul, neg_one_zsmul] at h
  -- `M = r G - f^*(K_X + Δ)` is nef, as `m M = E_Y`
  set M : QDivisor Y := (r : ℚ) • Divisor.toQDivisor G - P with hMdef
  have hEM : Divisor.toQDivisor ((m * r) • G + -D') = (m : ℚ) • M := by
    rw [map_add, map_neg, map_nsmul, hD', hMdef]
    module
  haveI := ((hHc.nsmul (m * r)).add hCXc.neg).isInvertibleModule_divisorialSheaf
  have hMnef : M.IsNef k (f ≫ sX) :=
    (QDivisor.isNef_and_isBig_of_isBirationalMorphism (f ≫ sX) sX hY.1 hYp hXp.1 hXp.2 f rfl hfp
      hbir ((m * r) • H + -CX).divisorialSheaf hEamp m hm _ (hcart _)
      (Divisor.IsPullback.divisorialSheafIso (hBc := (hHc.nsmul _).add hCXc.neg) hEpb) M hEM).1
  -- `⌈B⌉ - K_Y + r G = M + Δ'`, and relative Kawamata–Viehweg vanishing
  set L : Divisor Y := B.roundUp - KY + (r : ℤ) • G with hLdef
  have hLM : Divisor.toQDivisor L = M + Δ' := by
    rw [hLdef, hMdef, hΔ'def, hCdef, map_add, map_sub, map_zsmul]
    module
  have hnY : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hbir).symm.trans
      hP.2.1.topologicalKrullDim_eq
  have hKV := isZero_rightDerived_pushforward_exteriorPower_tensor_divisorialSheaf sX (f ≫ sX)
    hsm f rfl hbir hnY L M Δ' hMnef hΔ'snc (fun E => (hΔ'01 E).1) (fun E => (hΔ'01 E).2)
    (hLM ▸ QDivisor.NumericallyEquivalent.refl (QDivisor.isQCartier_toQDivisor (hcart L))) j hj
  -- `ω_Y ≅ 𝒪_Y(K_Y)`, so `ω_Y ⊗ 𝒪_Y(⌈B⌉ - K_Y + r G) ≅ 𝒪_Y(⌈B⌉) ⊗ f^*𝒪_X(r H)`
  have hKYc : KY.IsCanonicalDivisor (f ≫ sX) n :=
    isCanonicalDivisor_divisorOfForm_pullback hP.1 hω0 hP.2.1 hY hbir hsm
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_exteriorPower hsm hKYc
  have hrpb : ((r : ℤ) • H).IsPullback f (hdom _) ((r : ℤ) • G) := hG.zsmul hHc _ (hdom _)
  haveI := (hHc.zsmul (r : ℤ)).isInvertibleModule_divisorialSheaf
  let e := ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso eK.symm).app L.divisorialSheaf ≪≫
    (hcart KY).divisorialSheafTensorIso (hcart L) ≪≫
    eqToIso (congrArg Divisor.divisorialSheaf (show KY + L = B.roundUp + (r : ℤ) • G by
      rw [hLdef]; abel)) ≪≫
    ((hcart _).divisorialSheafTensorIso (hcart _)).symm ≪≫
    tensorModulesMapIso Y (Iso.refl _)
      (Divisor.IsPullback.divisorialSheafIso (hBc := hHc.zsmul _) hrpb)
  exact isZero_rightDerived_pushforward_of_isZero_tensor_pullback f ((r : ℤ) • H).divisorialSheaf
    _ j (hKV.of_iso (((Scheme.Modules.pushforward f).rightDerived j).mapIso e).symm)

end MMP.Mori

end

end
