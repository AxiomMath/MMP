module

public import MMP.AlgebraicGeometry.Vanishing.KodairaSerreDual
public import MMP.AlgebraicGeometry.Divisor.NumericallyTrivialTwistH0Bounded
public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical

/-!
# The Euler characteristic of a divisor is a numerical invariant

Let `X` be a smooth projective variety over an algebraically closed field `k` of characteristic
zero, and let `D`, `D'` be divisors on `X` that are numerically equivalent. Then
`χ(X, 𝒪_X(D)) = χ(X, 𝒪_X(D'))`. The proof writes `D' = D + N` with `N` numerically trivial,
twists by a large multiple of an ample divisor so that Kodaira vanishing turns the polynomial
`χ(𝒪_X(D + uN + vH))` into `h⁰`, and uses that `h⁰(D + vH + uN)` is bounded in `u`.

## Main results

* `MMP.Mori.Divisor.eulerCharacteristic_divisorialSheaf_eq_of_numericallyEquivalent`

## Implementation notes

The Euler characteristic `AlgebraicGeometry.eulerCharacteristic` is defined for coherent sheaves,
so coherence of `𝒪_X(D)` and `𝒪_X(D')` is an instance argument; it holds for every divisor on a
smooth projective variety.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Prop. 2.57
-/

@[expose] public section

section

/-!
## Proof: The Euler characteristic of a divisor is a numerical invariant

Let `X` be a smooth projective variety over an algebraically closed field `k` of characteristic
zero and `D ≡ D'` numerically equivalent divisors. Put `N = D' - D` and fix an ample divisor `H`
and a canonical divisor `K`. For every divisor `E` and `F` the function `u ↦ χ(𝒪_X(E + uF))` is a
polynomial (Snapper). For `v ≫ 0` the divisor `D + vH - K` is ample, hence so is
`D + uN + vH - K` for all `u`, and Kodaira vanishing gives `χ(D + uN + vH) = h⁰(D + uN + vH)`;
the latter is bounded in `u`, so the polynomial `u ↦ χ(D + uN + vH)` is constant. Hence the
polynomials `v ↦ χ(D' + vH)` and `v ↦ χ(D + vH)` agree for `v ≫ 0`, so they are equal, and
`v = 0` gives `χ(D') = χ(D)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Prop. 2.57
-/

namespace MMP.FourfoldProofs.Km2cEulerCharacteristicNumericalProof

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

section Polynomial

/-- If `|q(n)|` is bounded over `n : ℕ`, then `q(1) = q(0)`. -/
private theorem eval_one_eq_eval_zero_of_bddAbove (q : Polynomial ℚ)
    (h : BddAbove (Set.range fun n : ℕ => |q.eval (n : ℚ)|)) : q.eval 1 = q.eval 0 := by
  suffices hd : q.degree ≤ 0 by rw [Polynomial.eq_C_of_degree_le_zero hd]; simp
  by_contra hd
  obtain ⟨C, hC⟩ := h
  obtain ⟨n, hn⟩ := (((Polynomial.abs_tendsto_atTop q (not_le.mp hd)).comp
    tendsto_natCast_atTop_atTop).eventually (Filter.eventually_gt_atTop C)).exists
  exact absurd (hC ⟨n, rfl⟩) (not_le.mpr hn)

/-- Two polynomials agreeing at all large natural numbers are equal. -/
private theorem eq_of_eventually_eval_natCast_eq {p q : Polynomial ℚ} (n₀ : ℕ)
    (h : ∀ n : ℕ, n₀ ≤ n → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + n₀ : ℕ) : ℚ)) ?_ ?_
  · intro a b hab
    simp only [Nat.cast_inj] at hab
    omega
  · intro n
    have := h (n + n₀) (by omega)
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, this, sub_self]

/-- Substituting `(1, X)` into a polynomial in two variables. -/
private theorem eval_aeval_one_X (P : MvPolynomial (Fin 2) ℚ) (u : ℚ) :
    (MvPolynomial.aeval ![(1 : Polynomial ℚ), Polynomial.X] P).eval u =
      MvPolynomial.eval ![1, u] P := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact Subsingleton.elim _ _
  · funext i; fin_cases i <;> simp

end Polynomial

section Weil

/-- The order of a Cartier divisor at a point is additive in the divisor. -/
@[simp]
theorem cartierMultiplicity_add {X : Scheme.{0}} [IsLocallyNoetherian X] [IsIntegral X]
    (a b : X.CartierDivisor) (x : X) :
    cartierMultiplicity (a + b) x = cartierMultiplicity a x + cartierMultiplicity b x := by
  unfold cartierMultiplicity
  rw [map_add, map_add]
  rfl

/-- The order of the zero Cartier divisor at any point is zero. -/
@[simp]
theorem cartierMultiplicity_zero {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsIntegral X] (x : X) : cartierMultiplicity (0 : X.CartierDivisor) x = 0 := by
  have h := cartierMultiplicity_add (0 : X.CartierDivisor) 0 x
  rw [add_zero] at h
  omega

/-- The Weil divisor of a Cartier divisor, as an additive map into `MMP.Mori.Divisor X`. -/
noncomputable def weilOfCartier (X : Scheme.{0}) [IsNoetherian X] [IsIntegral X] :
    X.CartierDivisor →+ MMP.Mori.Divisor X where
  toFun τ := weilDivisorEquivFinsupp (cartierWeilDivisor τ)
  map_zero' := Finsupp.ext fun Z => cartierMultiplicity_zero Z.genericPoint
  map_add' a b := Finsupp.ext fun Z => cartierMultiplicity_add a b Z.genericPoint

/-- If the sheaf of the Cartier divisor `τ` is ample, then `weilOfCartier X τ` is ample. -/
theorem isAmple_weilOfCartier {X : Scheme.{0}} [IsNoetherian X] [IsIntegral X] [IsNormal X]
    (hcart : ∀ E : MMP.Mori.Divisor X, E.IsCartier)
    (hiso : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ))
    (τ : X.CartierDivisor)
    (h : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf τ)) :
    (weilOfCartier X τ).IsAmple (hcart _) := by
  obtain ⟨e⟩ := hiso τ
  haveI := (hcart (weilOfCartier X τ)).isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    e).mpr h

end Weil

section Snapper

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- (Snapper) If every divisor is the Weil divisor of a Cartier divisor with the same sheaf,
then `u ↦ χ(𝒪_X(E + uF))` is a polynomial for all divisors `E`, `F`. -/
private theorem exists_polynomial_eulerSum [IsProper f] [IsNoetherian X] [IsIntegral X]
    [IsNormal X] (hΦ : Function.Surjective (weilOfCartier X))
    (hiso : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ))
    {n : ℕ} (hn : topologicalKrullDim X = n) (E F : MMP.Mori.Divisor X) :
    ∃ p : Polynomial ℚ, ∀ u : ℤ, p.eval (u : ℚ) =
      (ProperFlatFibreEulerCharacteristic.eulerSum k f (E + u • F).divisorialSheaf : ℚ) := by
  obtain ⟨τE, rfl⟩ := hΦ E
  obtain ⟨τF, rfl⟩ := hΦ F
  obtain ⟨P, -, hP⟩ :=
    MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum k f n hn ![τE, τF]
  refine ⟨MvPolynomial.aeval ![(1 : Polynomial ℚ), Polynomial.X] P, fun u => ?_⟩
  rw [eval_aeval_one_X]
  have h := hP ![1, u]
  have hm : (fun i => ((![1, u] i : ℤ) : ℚ)) = ![1, (u : ℚ)] := by
    funext i; fin_cases i <;> simp
  rw [hm] at h
  rw [h]
  have hsum : (∑ i, ![1, u] i • ![τE, τF] i) = τE + u • τF := by
    simp [Fin.sum_univ_two]
  rw [hsum]
  obtain ⟨e⟩ := hiso (τE + u • τF)
  rw [map_add, map_zsmul] at e
  have := ProperFlatFibreEulerCharacteristic.eulerSum_congr k f e
  rw [this, ProperFlatFibreEulerCharacteristic.eulerSum]
  symm
  refine ((Int.castAddHom ℚ).map_finsum_of_injective Int.cast_injective _).trans
    (finsum_congr fun j => ?_)
  simp

end Snapper

section Degree

open MMP.Mori

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) [QuasiCompact f]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Numerical equivalence of Cartier divisors is equality of degrees on all curves. -/
private theorem numericallyEquivalent_toQDivisor_iff {E E' : MMP.Mori.Divisor X}
    (hE : E.IsCartier) (hE' : E'.IsCartier) :
    (Divisor.toQDivisor E).NumericallyEquivalent k f (Divisor.toQDivisor E') ↔
      ∀ (C : Scheme.{0}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ f)]
        (hC : topologicalKrullDim C = 1),
        E.degreeOn k f i hC.le hE = E'.degreeOn k f i hC.le hE' := by
  rw [QDivisor.numericallyEquivalent_iff _ _ (QDivisor.isQCartier_toQDivisor hE)
    (QDivisor.isQCartier_toQDivisor hE')]
  refine forall_congr' fun C => forall_congr' fun i => ?_
  refine ⟨fun h _ _ _ hC => ?_, fun h _ _ _ hC => ?_⟩
  · have := h hC
    rw [QDivisor.intersectionNumber_toQDivisor k f i hC.le E hE,
      QDivisor.intersectionNumber_toQDivisor k f i hC.le E' hE'] at this
    exact_mod_cast this
  · rw [QDivisor.intersectionNumber_toQDivisor k f i hC.le E hE,
      QDivisor.intersectionNumber_toQDivisor k f i hC.le E' hE', h hC]

end Degree

section Vanishing

open MMP.Mori

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- If `B - K_X` is ample then `χ(𝒪_X(B)) = h⁰(𝒪_X(B))`, by Kodaira vanishing. -/
private theorem eulerSum_eq_h0 [IsAlgClosed k] [CharZero k] [MMP.Mori.IsProjectiveVariety k f]
    (hsm : MMP.Mori.IsSmoothScheme f) [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {n : ℕ} {K B : MMP.Mori.Divisor X} (hK : K.IsCanonicalDivisor f n)
    (hA : ∃ h : (B - K).IsCartier, (B - K).IsAmple h) :
    ProperFlatFibreEulerCharacteristic.eulerSum k f B.divisorialSheaf = B.h0 k f := by
  rw [ProperFlatFibreEulerCharacteristic.eulerSum, finsum_eq_single _ 0 (fun j hj => ?_)]
  · simp only [pow_zero, one_mul, Nat.cast_inj]
    exact (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f _).finrank_eq
  · have hs := subsingleton_derivedCohomologyOverField_divisorialSheaf_of_isAmple_sub f hsm K B
      hK hA j (by omega)
    have : Module.finrank k (cohomologyOverField k f B.divisorialSheaf j) = 0 := by
      rw [(Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
        j).finrank_eq]
      exact Module.finrank_zero_of_subsingleton
    simp [this]

/-- If `B - K` is ample and `N` has degree zero on every curve, then `B + uN - K` is ample for
every integer `u`: it is numerically equivalent to `B - K`. -/
private theorem isAmple_add_zsmul_sub [MMP.Mori.IsProjectiveVariety k f] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [QuasiCompact f] (hcart : ∀ E : MMP.Mori.Divisor X, E.IsCartier)
    {K B N : MMP.Mori.Divisor X} (hA : (Divisor.toQDivisor (B - K)).IsAmple)
    (hN : ∀ (C : Scheme.{0}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ f)] (hC : topologicalKrullDim C = 1), N.degreeOn k f i hC.le (hcart N) = 0)
    (u : ℤ) : ∃ h : (B + u • N - K).IsCartier, (B + u • N - K).IsAmple h := by
  have hnef0 : (0 : QDivisor X).IsNef k f := by
    simpa using (QDivisor.isNef_toQDivisor_iff (k := k) (sX := f) (0 : MMP.Mori.Divisor X)
      Divisor.isCartier_zero).mpr
      ⟨Divisor.isCartier_zero, fun C i _ _ _ hC => (Divisor.degreeOn_zero' k f i hC.le).ge⟩
  refine ⟨hcart _, QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef f hA hnef0
    (B := Divisor.toQDivisor (B + u • N - K)) ?_ 1 one_pos _ (by simp) (hcart _)⟩
  rw [add_zero]
  refine (numericallyEquivalent_toQDivisor_iff f (hcart _) (hcart _)).mpr fun C i _ _ _ hC => ?_
  rw [Divisor.degreeOn_congr (show B + u • N - K = (B - K) + u • N by abel) _
      ((hcart _).add (hcart _)),
    Divisor.degreeOn_add k f i hC.le _ _ (hcart _) (hcart (u • N)),
    Divisor.degreeOn_zsmul' k f i hC.le N (hcart N) u, hN C i hC, mul_zero, add_zero]

end Vanishing

section Constancy

open MMP.Mori

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  (f : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k f] [IsLocallyNoetherian X] [IsNormal X]
  [QuasiCompact f] [IsProper f] [IsNoetherian X] [IsIntegral X]

/-- **The Euler characteristic is constant along a numerically trivial direction once Kodaira
vanishing applies.** If `N` is numerically trivial and `B + uN - K_X` is ample for every integer
`u`, then `χ(B + N) = χ(B)`. -/
private theorem eulerSum_add_eq_of_isAmple (hsm : MMP.Mori.IsSmoothScheme f)
    (hΦ : Function.Surjective (weilOfCartier X))
    (hiso : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ))
    {n : ℕ} (hn : topologicalKrullDim X = n) {K B N : MMP.Mori.Divisor X}
    (hK : K.IsCanonicalDivisor f n) (hN : (Divisor.toQDivisor N).IsNumericallyTrivial k f)
    (hA : ∀ u : ℤ, ∃ h : (B + u • N - K).IsCartier, (B + u • N - K).IsAmple h) :
    ProperFlatFibreEulerCharacteristic.eulerSum k f (B + N).divisorialSheaf =
      ProperFlatFibreEulerCharacteristic.eulerSum k f B.divisorialSheaf := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨p, hp⟩ := exists_polynomial_eulerSum f hΦ hiso hn B N
  have hp' (u : ℤ) : p.eval (u : ℚ) = ((B + u • N).h0 k f : ℚ) := by
    rw [hp u, eulerSum_eq_h0 f hsm hK (hA u)]
    simp
  obtain ⟨c, hc⟩ := Divisor.bddAbove_range_h0_add_zsmul_of_isNumericallyTrivial f hsm B N hN
  have h := eval_one_eq_eval_zero_of_bddAbove p ⟨c, ?_⟩
  · have h1 := hp 1
    have h0 := hp 0
    rw [Int.cast_one, one_zsmul] at h1
    rw [Int.cast_zero, zero_smul, add_zero] at h0
    exact_mod_cast h1.symm.trans (h.trans h0)
  rintro _ ⟨j, rfl⟩
  show |p.eval (j : ℚ)| ≤ c
  have h := hp' j
  simp only [Int.cast_natCast] at h
  rw [h, abs_of_nonneg (by positivity)]
  exact_mod_cast hc ⟨(j : ℤ), rfl⟩

end Constancy

end MMP.FourfoldProofs.Km2cEulerCharacteristicNumericalProof

end

section

open CategoryTheory AlgebraicGeometry MMP.FourfoldProofs.Km2cEulerCharacteristicNumericalProof

namespace MMP.Mori

namespace Divisor

/-- **The Euler characteristic is numerical** (Kollár–Mori, Prop. 2.57). Let `X` be a smooth
projective variety over an algebraically closed field `k` of characteristic zero and `D`, `D'`
numerically equivalent divisors on `X`. Then `χ(X, 𝒪_X(D)) = χ(X, 𝒪_X(D'))`. -/
@[mmp "prop_km2c_euler_characteristic_numerical"]
public theorem eulerCharacteristic_divisorialSheaf_eq_of_numericallyEquivalent
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact f] [IsProper f]
    {D D' : Divisor X} [D.divisorialSheaf.IsCoherent] [D'.divisorialSheaf.IsCoherent]
    (hDD' : (Divisor.toQDivisor D).NumericallyEquivalent k f (Divisor.toQDivisor D')) :
    eulerCharacteristic k f D.divisorialSheaf = eulerCharacteristic k f D'.divisorialSheaf := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : Smooth f := hsm.smooth
  haveI : IsSmoothVariety k f := ⟨⟩
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨hcart, -, ⟨-, hΦ⟩, hiso, hinv, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k f
  replace hΦ : Function.Surjective (weilOfCartier X) := hΦ
  replace hiso : ∀ τ : X.CartierDivisor,
      Nonempty ((weilOfCartier X τ).divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := hiso
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim X = n := by
    have h := Stacks.Chow.topologicalKrullDim_closure_singleton_eq k f (genericPoint X)
    rw [(genericPoint_spec X).def,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph] at h
    exact ⟨_, h⟩
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isSmoothScheme f hsm hn
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isProjectiveMorphism f M hMa
    AlgebraicGeometry.IsProjectiveVariety.isProjective
  obtain ⟨H, ⟨eH⟩⟩ := hinv L hL
  obtain ⟨τH, rfl⟩ := hΦ H
  have hHa : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf τH) := by
    obtain ⟨e⟩ := hiso τH
    haveI := (hcart (weilOfCartier X τH)).isInvertibleModule_divisorialSheaf
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (e.symm ≪≫ eH)).mpr hLa
  obtain ⟨τA, hτA⟩ := hΦ (D - K)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add_of_isProper f τH τA hHa)
  have hAmp (m : ℕ) (hm : m₀ ≤ m) :
      (Divisor.toQDivisor (D + (m : ℤ) • weilOfCartier X τH - K)).IsAmple := by
    have h := isAmple_weilOfCartier hcart hiso _ (hm₀ m hm)
    rw [map_add, map_nsmul, hτA, show m • weilOfCartier X τH + (D - K) =
      D + (m : ℤ) • weilOfCartier X τH - K by rw [natCast_zsmul]; abel] at h
    exact ⟨1, one_pos, _, by simp, hcart _, h⟩
  have hdeg : ∀ (C : Scheme.{0}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ f)] (hC : topologicalKrullDim C = 1),
      (D' - D).degreeOn k f i hC.le (hcart _) = 0 := by
    intro C i _ _ _ hC
    have h := (numericallyEquivalent_toQDivisor_iff f (hcart D) (hcart D')).mp hDD' C i hC
    rw [Divisor.degreeOn_congr (show D' = D + (D' - D) by abel) (hcart D')
      ((hcart D).add (hcart _)), Divisor.degreeOn_add k f i hC.le _ _ (hcart D) (hcart _)] at h
    omega
  have hNtriv : (Divisor.toQDivisor (D' - D)).IsNumericallyTrivial k f :=
    (QDivisor.isNumericallyTrivial_iff _).mpr ⟨QDivisor.isQCartier_toQDivisor (hcart _),
      fun C i _ _ _ hC => by
        rw [QDivisor.intersectionNumber_toQDivisor k f i hC.le _ (hcart _), hdeg C i hC]
        simp⟩
  obtain ⟨q₁, hq₁⟩ := exists_polynomial_eulerSum f hΦ hiso hn D' (weilOfCartier X τH)
  obtain ⟨q₀, hq₀⟩ := exists_polynomial_eulerSum f hΦ hiso hn D (weilOfCartier X τH)
  have hq : q₁ = q₀ := eq_of_eventually_eval_natCast_eq m₀ fun m hm => by
    have h := eulerSum_add_eq_of_isAmple f hsm hΦ hiso hn hK hNtriv
      (isAmple_add_zsmul_sub f hcart (hAmp m hm) hdeg)
    rw [show D + (m : ℤ) • weilOfCartier X τH + (D' - D) =
      D' + (m : ℤ) • weilOfCartier X τH by abel] at h
    rw [← Int.cast_natCast, hq₁, hq₀]
    exact_mod_cast h
  have h := congrArg (Polynomial.eval ((0 : ℤ) : ℚ)) hq
  rw [hq₁ 0, hq₀ 0] at h
  simp only [zero_smul, add_zero, Int.cast_inj] at h
  exact h.symm

end Divisor

end MMP.Mori

end
