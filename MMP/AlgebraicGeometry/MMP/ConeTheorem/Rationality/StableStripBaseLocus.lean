module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripVanishing
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.PolynomialZerosStrip
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.EulerPolynomialLeadingCoeff
public import MMP.AlgebraicGeometry.Resolution.LogResolutionAmpleSubtraction
@[expose] public section

universe u

/-!
# The stable strip base locus is proper when the nef threshold has large denominator

Let `(X, Δ, a, H)` be a rationality datum of dimension `n` with nef threshold `r > 0` of `H`
with respect to `K_X + Δ`, and suppose that `r` is not of the form `u / v` with integers `u, v`
and `0 < v ≤ a(n + 1)` (for instance, `r` irrational). Then every stable base locus `Z` of the
`(r, 1)`-strip is a proper closed subset of `X`.

The proof takes a log resolution `g : Y ⟶ X` with `K_Y = g^*(K_X + Δ) + A`. The Euler
characteristic `P(p, q) = χ(Y, p g^*H + q g^*(a(K_X + Δ)) + ⌈A⌉)` is a nonzero polynomial of
degree at most `n`; were it to vanish on all lattice points of the strip `0 < aq - rp < 1` with
`p, q ≥ N`, then `r` would be rational with denominator at most `a(n + 1)`. At a lattice point
where `P(p, q) ≠ 0`, the higher cohomology vanishes, so `h⁰(X, pH + qa(K_X + Δ)) = P(p, q) ≠ 0`
and the strip base locus `L(p, q) = Z` is not all of `X`.

## Main results

* `MMP.Mori.IsRationalityDatum.ne_top_of_isStableStripBaseLocus`: the statement above.

## Implementation notes

The nef threshold is `MMP.Mori.QDivisor.IsNefThreshold` of `H` with respect to `K_X + Δ`, the
stable base locus is `MMP.Mori.IsStableStripBaseLocus` with `ε = 1`, and `Z ≠ X` is
`Z ≠ ⊤` in `TopologicalSpace.Closeds X`. The arithmetic hypothesis on `r` is read in `ℝ`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Steps 5–8
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.MmpFoundationKm3bRationalityIrrationalNonemptyWithSncContainmentProof

/-- The evaluation of the image of `P ∈ ℚ[σ]` in `ℝ[σ]` at a rational point is the image of the
evaluation of `P`. -/
private theorem eval_map_algebraMap {σ : Type*} (P : MvPolynomial σ ℚ) (g : σ → ℚ) :
    MvPolynomial.eval (fun i => (g i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      ((MvPolynomial.eval g P : ℚ) : ℝ) := by
  rw [MvPolynomial.eval_map]
  change _ = algebraMap ℚ ℝ (MvPolynomial.eval₂ (RingHom.id ℚ) g P)
  rw [MvPolynomial.eval₂_comp_left]
  rfl

/-- A nonzero polynomial `P ∈ ℚ[p, q]` of degree at most `n` does not vanish on all lattice
points `p, q ≥ N` of the strip `0 < aq - rp < 1` unless `r = u / v` with `0 < v ≤ a(n + 1)`. -/
private theorem exists_strip_eval_ne_zero {P : MvPolynomial (Fin 2) ℚ} (hP : P ≠ 0) {n : ℕ}
    (hPn : P.totalDegree ≤ n) {a : ℤ} (ha : 0 < a) {r : ℝ} (hr0 : 0 < r)
    (hrat : ∀ u v : ℤ, 0 < v → v ≤ a * (n + 1) → r ≠ (u : ℝ) / v) (N : ℤ) :
    ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ 0 < a * y - r * x ∧ a * y - r * x < 1 ∧
      MvPolynomial.eval (fun i => ((![x, y] i : ℤ) : ℚ)) P ≠ 0 := by
  set PR := MvPolynomial.map (algebraMap ℚ ℝ) P
  have hPR : PR ≠ 0 := fun h0 =>
    hP (MvPolynomial.map_injective _ (algebraMap ℚ ℝ).injective (by simpa using h0))
  have hPRn : PR.totalDegree ≤ n :=
    (Finset.sup_le fun s hs => Finset.le_sup (f := fun s => s.sum fun _ e => e)
      (MvPolynomial.support_map_subset _ _ hs)).trans hPn
  have heval (x y : ℤ) : MvPolynomial.eval ![(x : ℝ), (y : ℝ)] PR =
      MvPolynomial.eval (fun i => ((![x, y] i : ℤ) : ℚ)) P := by
    have hv : ![(x : ℝ), (y : ℝ)] = fun i => (((![x, y] i : ℤ) : ℚ) : ℝ) := by
      funext i; fin_cases i <;> simp
    rw [hv, eval_map_algebraMap]
  by_contra! hall
  simp_rw [← Rat.cast_eq_zero (α := ℝ), ← heval] at hall
  obtain ⟨t, rfl⟩ := MMP.Positivity.exists_rat_eq_of_eval_eq_zero_of_strip hPR ha one_pos hr0
    ⟨N, hall⟩
  have hden := MMP.Positivity.den_le_of_eval_eq_zero_of_strip hPR hPRn ha one_pos
    (by exact_mod_cast hr0) ⟨N, hall⟩
  rw [div_one] at hden
  refine hrat t.num t.den (by exact_mod_cast t.den_pos) (by exact_mod_cast hden) ?_
  rw [Rat.cast_def]
  push_cast
  rfl

/-- If the higher cohomology of `𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉)` vanishes, the Euler characteristic
function at `u` is `h⁰(Y, 𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉))`. -/
private theorem eulerPolynomial_eq_finrank_zero {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Spec (.of k)) {ι : Type*} [Fintype ι]
    (D : ι → Divisor Y) (A : QDivisor Y) (u : ι → ℤ) {L : Divisor Y}
    (hL : ∑ i, u i • D i + A.roundUp = L)
    (h : ∀ j : ℕ, 0 < j → Subsingleton (cohomologyOverField k f L.divisorialSheaf j)) :
    Divisor.eulerPolynomial k f D A u =
      Module.finrank k (cohomologyOverField k f L.divisorialSheaf 0) := by
  rw [Divisor.eulerPolynomial, hL, finsum_eq_single _ 0 fun j hj => by
    have := h j (Nat.pos_of_ne_zero hj)
    rw [Module.finrank_zero_of_subsingleton]; simp]
  simp

/-- If `h⁰(Y, 𝒪_Y(B_Y + E)) ≠ 0`, where `B_Y = g^*B` and `E` is effective and
`g`-exceptional, a nonzero section descends to a nonzero global section of `𝒪_X(B)`; so the
generic point of `X` is not in the base locus of `B`. -/
private theorem genericPoint_notMem_baseLocus_of_isPullback_add {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) (hX : MMP.Mori.IsVariety k sX)
    (hY : MMP.Mori.IsVariety k (g ≫ sX))
    [IsProper g] (hg : IsBirationalMorphism g) {B : Divisor X} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp}
    {BY : Divisor Y} (hBY : B.IsPullback g hB BY)
    {E : Divisor Y} (hEc : E.IsCartier) (hE : 0 ≤ E)
    (hEexc : ∀ P : MMP.Mori.PrimeDivisor Y, E.coeff P ≠ 0 →
      RationalMap.IsExceptional g.toRationalMap P)
    (hne : Module.finrank k (cohomologyOverField k (g ≫ sX) (BY + E).divisorialSheaf 0) ≠ 0) :
    genericPoint X ∉ (B.baseLocus : Set X) := by
  have := hg.isDominant
  have := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hne)
  obtain ⟨c, hc⟩ := exists_ne (0 : cohomologyOverField k (g ≫ sX) (BY + E).divisorialSheaf 0)
  let τ : (BY + E).divisorialSubmodule ⊤ :=
    (cohomologyOverFieldZeroLinearIso k (g ≫ sX) _).toLinearEquiv c
  have hτ : τ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hc
  obtain ⟨e, -⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sX g
    hX hY hg B hBc hB BY hBY E hEc hE hEexc
  let τ' : (BY + E).divisorialSubmodule (g ⁻¹ᵁ ⊤) := ⟨τ.1, τ.2⟩
  set σ : B.divisorialSubmodule ⊤ := e.inv.app ⊤ τ'
  have hστ : (e.hom.app ⊤ σ : (BY + E).divisorialSubmodule (g ⁻¹ᵁ ⊤)) = τ' :=
    congrArg (fun φ => (φ.app ⊤).hom τ') e.inv_hom_id
  have hσ : σ ≠ 0 := by
    intro h0
    have : τ' = 0 := by
      rw [← hστ, h0]
      exact (Scheme.Modules.Hom.app e.hom ⊤).hom.map_zero
    exact hτ (Subtype.ext (congrArg Subtype.val this))
  exact fun h => MMP.Fourfold.genericPoint_notMem_supp _ (Divisor.baseLocus_le_supp B σ hσ h)

/-- The support of a multiple of a divisor lies in the support of the divisor. -/
private theorem supp_zsmul_le {X : Scheme.{u}} (D : Divisor X) (m : ℤ) :
    (m • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨E, hE, hx⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, fun h0 => hE ?_, hx⟩
  rw [DivisorWithCoeffs.coeff_smul, h0, smul_zero]

/-- The round-down of a `ℚ`-divisor with integral coefficients is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{u}} (D : Divisor X) :
    (Divisor.toQDivisor D).roundDown = D := by
  ext E
  rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]

/-- A nonempty scheme has a nonzero unit ideal sheaf. -/
private theorem top_ne_bot_idealSheafData (X : Scheme.{u}) [Nonempty X] :
    (⊤ : X.IdealSheafData) ≠ ⊥ := fun hI => by
  have h1 := congrArg Scheme.IdealSheafData.support hI
  rw [Scheme.IdealSheafData.support_top, Scheme.IdealSheafData.support_bot] at h1
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ ((⊤ : TopologicalSpace.Closeds X) : Set X) := trivial
  rw [← h1, TopologicalSpace.Closeds.coe_bot] at hx
  exact hx

/-- On a projective log resolution `g : Y ⟶ X` of a rationality datum, the Euler characteristic
`χ(Y, x H' + y B' + ⌈A⌉)` is nonzero at some lattice point `x, y ≥ N` of the strip
`0 < ay - rx < 1`, unless `r = u / v` with `0 < v ≤ a(n + 1)`. -/
private theorem exists_strip_eulerPolynomial_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsProper sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (hd : IsRationalityDatum sX n K Δ a H) (hn : topologicalKrullDim X = n)
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {g : Y ⟶ X}
    [IsProper (g ≫ sX)] (hg : IsLogResolution sX (QDivisor.toRDivisor Δ) g)
    (hY : MMP.Mori.IsProjectiveVariety k (g ≫ sX))
    (hnY : topologicalKrullDim Y = n) {H' B' : Divisor Y}
    {hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp}
    (hH' : H.IsPullback g hHg H')
    {hBg : ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp}
    (hB' : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsPullback g hBg B') (A : QDivisor Y)
    {r : ℝ} (hr0 : 0 < r) (hrat : ∀ u v : ℤ, 0 < v → v ≤ a * (n + 1) → r ≠ (u : ℝ) / v)
    (N : ℤ) :
    ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ 0 < a * y - r * x ∧ a * y - r * x < 1 ∧
      Divisor.eulerPolynomial k (g ≫ sX) ![H', B'] A ![x, y] ≠ 0 := by
  obtain ⟨-, hcoeff, hpos⟩ :=
    hd.coeff_eulerPolynomial_of_isLogResolution hn hg hY hHg hH' hBg hB' A
  obtain ⟨P, hPdeg, hP⟩ := Divisor.exists_totalDegree_le_eval_eq_eulerPolynomial k (g ≫ sX)
    hg.isSmoothScheme hnY ![H', B'] A
  have hP0 : P ≠ 0 := by
    rintro rfl
    have h1 := hcoeff 0 hP
    rw [MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, eq_comm, div_eq_zero_iff] at h1
    exact h1.elim (by exact_mod_cast hpos.ne') (by exact_mod_cast n.factorial_ne_zero)
  obtain ⟨x, y, hx, hy, h1, h2, hne⟩ := exists_strip_eval_ne_zero hP0 hPdeg hd.pos hr0 hrat N
  exact ⟨x, y, hx, hy, h1, h2, by rw [hP] at hne; exact_mod_cast hne⟩

end MMP.FourfoldProofs.MmpFoundationKm3bRationalityIrrationalNonemptyWithSncContainmentProof

namespace MMP.Mori

open MMP.FourfoldProofs.MmpFoundationKm3bRationalityIrrationalNonemptyWithSncContainmentProof in
/-- **The stable strip base locus is proper** (Kollár–Mori 3.4). Let `(X, Δ, a, H)` be a
rationality datum of dimension `n` and `r > 0` the nef threshold of `H` with respect to
`K_X + Δ`, and suppose `r ≠ u / v` for all integers `u, v` with `0 < v ≤ a(n + 1)`. If `Z` is a
stable base locus of the `(r, 1)`-strip, then `Z ≠ X`. -/
@[mmp "lem_mmp_foundation_km3b_rationality_irrational_nonempty_with_snc_containment"]
public theorem IsRationalityDatum.ne_top_of_isStableStripBaseLocus
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hd : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hr0 : 0 < r)
    (hrat : ∀ u v : ℤ, 0 < v → v ≤ a * (n + 1) → r ≠ (u : ℝ) / v)
    {Z : TopologicalSpace.Closeds X} (hZ : IsStableStripBaseLocus K Δ a H r 1 Z) :
    Z ≠ ⊤ := by
  classical
  obtain ⟨N, hN⟩ := hZ
  have : AlgebraicGeometry.IsProperVariety k sX := hd.isProperVariety
  obtain ⟨Y, g, hg, hY, hYln, hYn, hYc, -, -, -, -, -, -, -, -⟩ :=
    exists_isLogResolution_isAmple_pullback_sub_sum sX Δ ⊤ (top_ne_bot_idealSheafData X) _
      ((QDivisor.isNef_toQDivisor_iff H hd.isCartier_H).2 hd.isNef_H)
      ⟨1, one_pos, H, by simp, hd.isCartier_H, hd.isBig_H⟩
  have : AlgebraicGeometry.IsVariety k (g ≫ sX) := hY.toIsVariety
  have : IsIntegral Y := ‹AlgebraicGeometry.IsVariety k (g ≫ sX)›.toIsIntegral
  have : IsProper g := hg.isProper
  have : IsProper (g ≫ sX) := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := g ≫ sX))).isProper
  have hYnv : IsNormalVariety k (g ≫ sX) := ⟨inferInstance, hYn⟩
  have hbir : IsBirationalMorphism g := hg.isBirationalMorphism
  have : IsDominant g := hbir.isDominant
  have hKX : K.IsCanonicalDivisor sX n := hd.isKltPair.1.2.1
  obtain ⟨Δ', hΔ'⟩ :=
    (hd.isKltPair.isPair.existsUnique_isCrepantBoundary hKX g hYnv hbir).1.exists
  obtain ⟨hAeff, hAexc⟩ := MMP.Positivity.IsKltPair.isEffective_roundUp_neg_of_isCrepantBoundary
    hd.isKltPair hd.isEffective hYnv hbir hΔ'
  have hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g _ Z
  have hBg : ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g _ Z
  obtain ⟨D₀, hD₀, hD₀c⟩ := hd.isCartierDivisor
  have hDc : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsCartier := by
    rwa [← hD₀, roundDown_toQDivisor]
  obtain ⟨H', hH'⟩ := hd.isCartier_H.exists_isPullback hHg
  obtain ⟨B'', hB''⟩ := hDc.exists_isPullback hBg
  obtain ⟨x, y, hx, hy, h1, h2, hne⟩ := exists_strip_eulerPolynomial_ne_zero hd hKX.1 hg hY
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hbir).symm.trans
      hKX.1) hH' hB'' (-Δ') hr0 hrat (max N 1)
  rw [eulerPolynomial_eq_finrank_zero _ _ _ _ (L := x • H' + y • B'' + (-Δ').roundUp)
    (by simp [Fin.sum_univ_two])
    fun i hi => hd.cohomology_subsingleton_of_isLogResolution hr hg hY ⟨hYnv, by rwa [neg_neg]⟩
      hH' hB'' ((le_max_right _ _).trans hx) h1 h2 hi] at hne
  have hgen := genericPoint_notMem_baseLocus_of_isPullback_add sX g
    inferInstance hYnv.1 hbir ((hd.isCartier_H.zsmul x).add (hDc.zsmul y))
    (Divisor.IsPullback.add (hd.isCartier_H.zsmul x) (hDc.zsmul y)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g _)
      (hH'.zsmul hd.isCartier_H x fun Z hZ => hHg Z (supp_zsmul_le H x hZ))
      (hB''.zsmul hDc y fun Z hZ => hBg Z (supp_zsmul_le _ y hZ)))
    (MMP.Fourfold.isCartier_of_isSmoothScheme hg.isSmoothScheme _) hAeff hAexc
    (by exact_mod_cast hne)
  rintro rfl
  apply hgen
  change genericPoint X ∈ (stripBaseLocus K Δ a H x y : Set X)
  rw [hN x y ((le_max_left _ _).trans hx) ((le_max_left _ _).trans hy) h1 h2]
  trivial

end MMP.Mori
