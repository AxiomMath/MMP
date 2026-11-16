module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripEulerPolynomialNonzero
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripEulerCharacteristic
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.PolynomialZerosStrip
public import MMP.AlgebraicGeometry.Resolution.Surface.RegularSurfaceBlowup

/-!
# Restricted sections in the strip for an irrational nef threshold

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r > 0` of `H` with respect to
`K_X + Δ`, and suppose `r` is irrational. Let `p, q > 0` be integers with `aq - rp > 0`, let
`(j₀, c)` be a tie-breaker of a `(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` with test
boundary `A'`, and put `F = F_{j₀}`. Then for every `N` there are integers `p', q' ≥ N` with
`p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and `0 < aq' - rp' < aq - rp` such that
`H⁰(F, 𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)|_F) ≠ 0`.

The restricted Euler characteristic function `Q` of `(F; f^*H|_F, f^*(a(K_X + Δ))|_F; A'|_F)` is a
nonzero polynomial of degree at most `n - 1`; a nonzero polynomial cannot vanish at all lattice
points of a strip `0 < aq' - rp' < ε` of irrational slope far out, and in the strip `Q` equals
the dimension of the space of restricted sections.

## Main results

* `MMP.Mori.IsStripTieBreaker.exists_nontrivial_cohomologyOverField_restrict`: the statement
  above.

## Implementation notes

The prime divisor `F = F_{j₀}` is the integral closed subscheme `(F j₀).idealSheaf.subscheme`
with inclusion `ι = (F j₀).idealSheaf.subschemeι`, a scheme over `k` through `ι ≫ f ≫ sX`. The
restricted sheaf `𝒪_Y(B' + ⌈A'⌉)|_F` is `ι^*` of the divisorial sheaf, where `B'` is a pull-back
of `p'H + q'a(K_X + Δ)` (`MMP.Mori.stripDivisor`) along `f`; the conclusion holds for every such
pull-back. "`H⁰ ≠ 0`" is `Nontrivial` of the degree-zero cohomology over `k`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-!
## Proof outline

Let `Q` be the Euler characteristic function of `(F; f^*H|_F, f^*(a(K_X + Δ))|_F; A'|_F)` on the
smooth projective prime divisor `F = F_{j₀}`. It is a nonzero function, and it is the evaluation
of a polynomial. A nonzero real polynomial in two variables that vanishes at every lattice point
`(p', q')` far out in the strip `0 < aq' - rp' < aq - rp` forces `r ∈ ℚ`; since `r` is irrational,
some lattice point of the strip with `p', q' ≥ max(N, ⌈(1 + c)p⌉, ⌈(1 + c)q⌉)` has `Q(p', q') ≠ 0`,
and there `Q(p', q') = dim_k H⁰(F, 𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)|_F)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4 Step 9
-/

/-- A dimension `d ≠ ⊥` with `d + 1 = n` for some `n : ℕ` is a natural number. -/
private theorem exists_eq_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (hd : d ≠ ⊥)
    (h : d + 1 = n) : ∃ m : ℕ, d = m := by
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd
  induction e with
  | top =>
    have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) = n := by exact_mod_cast h
    simp at h'
  | coe e => exact ⟨e, rfl⟩

/-- A nonzero function `Q : ℤ² → ℤ` that is the evaluation of a rational polynomial does not
vanish at every lattice point far out in the strip `0 < ay - rx < ε` when `r` is irrational. -/
private theorem exists_strip_eval_ne_zero {Q : (Fin 2 → ℤ) → ℤ} (hQ : Q ≠ 0)
    {P : MvPolynomial (Fin 2) ℚ} (hP : ∀ u, MvPolynomial.eval (fun i => (u i : ℚ)) P = Q u)
    {a : ℤ} (ha : 0 < a) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hirr : Irrational r) (N : ℤ) :
    ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ 0 < a * y - r * x ∧ a * y - r * x < ε ∧ Q ![x, y] ≠ 0 := by
  have hev (x y : ℤ) : MvPolynomial.eval ![(x : ℝ), (y : ℝ)]
      (MvPolynomial.map (algebraMap ℚ ℝ) P) = (Q ![x, y] : ℝ) := by
    have : ![(x : ℝ), (y : ℝ)] = algebraMap ℚ ℝ ∘ fun i => ((![x, y] i : ℤ) : ℚ) := by
      ext i; fin_cases i <;> simp
    rw [this, ← MvPolynomial.map_eval, hP]
    simp
  have hPR : MvPolynomial.map (algebraMap ℚ ℝ) P ≠ 0 := fun h0 => hQ <| funext fun u => by
    have hP0 : P = 0 := MvPolynomial.map_injective _ (algebraMap ℚ ℝ).injective (by simpa using h0)
    simpa [hP0] using (hP u).symm
  by_contra! hall
  obtain ⟨t, ht⟩ := MMP.Positivity.exists_rat_eq_of_eval_eq_zero_of_strip hPR ha hε hr
    ⟨N, fun x y hx hy h1 h2 => by rw [hev, hall x y hx hy h1 h2, Int.cast_zero]⟩
  exact hirr ⟨t, ht.symm⟩

/-- **Restricted sections in the strip for an irrational threshold** (Kollár–Mori 3.4, Step 9).
Let `(X, Δ, a, H)` be a rationality datum with irrational nef threshold `r > 0` of `H` with
respect to `K_X + Δ`, `p, q > 0` integers with `0 < aq - rp`, `(j₀, c)` a tie-breaker of a
`(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` with test boundary `A'`, and
`ι : F_{j₀} ⟶ Y` the closed immersion. Then for every integer `N` there are integers
`p', q' ≥ N` with `(1 + c) p ≤ p'`, `(1 + c) q ≤ q'` and `0 < aq' - rp' < aq - rp` such that
for every pull-back `B'` of `p'H + q'a(K_X + Δ)` along `f`,
`H⁰(F_{j₀}, ι^* 𝒪_Y(B' + ⌈A'⌉)) ≠ 0`. -/
@[mmp "lem_km3b_strip_restricted_sections_irrational"]
public theorem IsStripTieBreaker.exists_nontrivial_cohomologyOverField_restrict
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hr0 : 0 < r) (hirr : Irrational r) (hpq : 0 < (a * q : ℝ) - r * p) (N : ℤ) :
    ∃ p' q' : ℤ, N ≤ p' ∧ N ≤ q' ∧ (1 + c) * p ≤ p' ∧ (1 + c) * q ≤ q' ∧
      0 < (a * q' : ℝ) - r * p' ∧ (a * q' : ℝ) - r * p' < a * q - r * p ∧
      ∀ (hM : ∀ Z : irreducibleComponents Y,
          f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp)
        (B' : Divisor Y), (stripDivisor K Δ a H p' q').IsPullback f hM B' →
        Nontrivial (cohomologyOverField k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)
          ((Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj
            (B' + (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp).divisorialSheaf)
          0) := by
  set ι := (F j₀).idealSheaf.subschemeι
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c
  haveI hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have hKX : K.IsCanonicalDivisor sX n := h.isKltPair.1.2.1
  haveI : AlgebraicGeometry.IsVariety k sX := h.isKltPair.1.1.1
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans hKX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  haveI : IsSmoothVariety k (f ≫ sX) := { toSmooth := inferInstance }
  haveI : IsProper f := h.isLogResolution.isProper
  have hFmem : F j₀ ∈ (∑ j, Finsupp.single (F j) (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    classical simp [Finsupp.single_apply, h.injective.eq_iff]
  have hsmF : IsSmoothScheme (ι ≫ f ≫ sX) := h.isSNC.1 (F j₀) hFmem
  haveI : IsIntegral (F j₀).idealSheaf.subscheme := (F j₀).integral
  haveI hsF : Smooth (ι ≫ f ≫ sX) := (isSmoothScheme_iff _).mp hsmF
  haveI hvF : AlgebraicGeometry.IsVariety k (ι ≫ f ≫ sX) := ⟨⟩
  haveI : IsSmoothVariety k (ι ≫ f ≫ sX) := { toIsVariety := hvF, toSmooth := hsF }
  haveI : CompactSpace (F j₀).idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace ι
  haveI : IsLocallyNoetherian (F j₀).idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ f ≫ sX)
  haveI : IsNormal (F j₀).idealSheaf.subscheme := isNormal_of_smooth_over_field (ι ≫ f ≫ sX)
  haveI : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ f ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion ι).comp hPY.isProjective)
  obtain ⟨m, hdimF⟩ : ∃ m : ℕ, topologicalKrullDim (F j₀).idealSheaf.subscheme = m := by
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX)
      (F j₀).genericPoint
    rw [(F j₀).coheight_genericPoint, hdim,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← MMP.Mori.topologicalKrullDim_subscheme_eq] at h1
    refine exists_eq_of_add_one_eq ?_ (by exact_mod_cast h1)
    rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
    infer_instance
  obtain ⟨hcY, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sX)
  obtain ⟨-, -, -, -, hinvF, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (ι ≫ f ≫ sX)
  -- the pull-backs `H' = f^*H`, `B'' = f^*⌊a(K_X + Δ)⌋` and their restrictions to `F`
  have : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  have hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _ Z
  have hBf : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _ Z
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hDc : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsCartier := by
    have hr0' : (a • (Divisor.toQDivisor K + Δ)).roundDown = D₀ := by
      rw [← hD₀]
      ext E
      change ((Divisor.toQDivisor D₀).roundDown).coeff E = D₀.coeff E
      rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]
    exact hr0' ▸ hD₀c
  obtain ⟨H', hH'⟩ := h.isCartier_H.exists_isPullback hHf
  obtain ⟨B'', hB''⟩ := hDc.exists_isPullback hBf
  haveI := (hcY H').isInvertibleModule_divisorialSheaf
  haveI := (hcY B'').isInvertibleModule_divisorialSheaf
  obtain ⟨HF, eH⟩ := hinvF ((Scheme.Modules.pullback ι).obj H'.divisorialSheaf) inferInstance
  obtain ⟨BF, eB⟩ := hinvF ((Scheme.Modules.pullback ι).obj B''.divisorialSheaf) inferInstance
  -- `Q` is a nonzero function and the evaluation of a polynomial `P`
  have hQ := IsStripTieBreaker.eulerPolynomial_restrict_ne_zero h hr hr0 hpq hH' hB'' eH eB
  obtain ⟨P, -, hP⟩ := MMP.Mori.Divisor.exists_totalDegree_le_eval_eq_eulerPolynomial k
    (ι ≫ f ≫ sX) hsmF hdimF ![HF, BF] (A.restrictPrimeDivisor (F j₀))
  -- a lattice point of the strip where `Q` does not vanish
  obtain ⟨x, y, hx, hy, h1, h2, hQne⟩ :=
    exists_strip_eval_ne_zero hQ hP h.pos hpq hr0 hirr (max N (max ⌈(1 + c) * p⌉ ⌈(1 + c) * q⌉))
  simp only [max_le_iff, Int.ceil_le] at hx hy
  refine ⟨x, y, hx.1, hy.1, hx.2.1, hy.2.2, h1, h2, fun hM B' hB' => ?_⟩
  rw [IsStripTieBreaker.eulerPolynomial_restrict_eq_finrank h hr hpq hx.2.1 hy.2.2 h2.le hH'
    hB'' eH eB hB'] at hQne
  exact Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero (by exact_mod_cast hQne))

end MMP.Mori

end
