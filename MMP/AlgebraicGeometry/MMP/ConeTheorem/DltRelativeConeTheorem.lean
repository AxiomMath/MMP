module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RelativeConeTheorem
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
public import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary

/-!
# The relative cone theorem for dlt pairs

Let `(X, Δ)` be a dlt pair with `X` a `ℚ`-factorial projective variety over an algebraically
closed field `k` of characteristic zero, and let `f : X ⟶ S` be a morphism of projective
varieties. Then there are countably many rational curves `Cⱼ ⊆ X`, each contracted by `f` and
with `0 < -((K_X + Δ) · Cⱼ) ≤ 2 dim X`, such that the relative closed cone of curves decomposes as

`NE̅(X/S) = NE̅(X/S)_{(K_X + Δ) ≥ 0} + ∑ⱼ ℝ_{≥0} [Cⱼ]`.

Every `(K_X + Δ)`-negative extremal ray `R = ℝ_{≥0} v` of `NE̅(X/S)` is spanned by a rational
curve `C` contracted by `f` with `0 < -((K_X + Δ) · C) ≤ 2 dim X`: for a small rational `δ > 0`
the pair `(X, (1 - δ)Δ)` is klt and `R` is still `(K_X + (1 - δ)Δ)`-negative, so the klt relative
cone theorem writes `v` as a non-negative combination of curves of bounded
`(K_X + (1 - δ)Δ)`-degree, all of which lie in `R` by extremality. Since `(K_X + Δ) · C` has
denominator bounded by the Cartier index of `K_X + Δ`, the bound `2 dim X` survives the limit
`δ → 0`. As `NE̅(X/S)` is the sum of its extremal rays, this gives the decomposition.

## Main results

* `MMP.Mori.IsDltPair.exists_relativeClosedConeOfCurves_eq_add_hull`: the decomposition.

## Implementation notes

The countable family of curves is indexed by a countable type `ι`; the sum `∑ⱼ ℝ_{≥0}[Cⱼ]` of
the rays is the convex cone they span, `PointedCone.hull ℝ`, whose elements are the finite
non-negative combinations of the classes `[Cⱼ]`. A curve is an `MMP.Mori.ProperCurve`, and it is
rational when its reduced closed subscheme is (`MMP.Mori.IsRationalCurve`). The pairing with
`K_X + Δ` on `N₁(X/S)` is `MMP.Fourfold.QDivisor.relativeCurveForm`. The dimension of `X` is the
integer `n` of the dlt pair. The boundary of a dlt pair has coefficients in `[0, 1]`, so it is
effective without a further hypothesis.

Instead of the set of negative extremal rays, the countable family of curves is the union, over
the rational numbers `δᵢ = min(δ₀, 1) / (i + 2)`, of those curves of the klt cone theorem for
`(X, (1 - δᵢ)Δ)` whose `(K_X + Δ)`-degree satisfies the required bounds. This avoids the
countability of the set of curve classes.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Theorem 3.35 (for
  3.25(1)) in case 3.21(0).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Pointwise MMP.Fourfold

namespace MMP.Mori

/-! ### Extremal faces and cones spanned by generators -/

/-- If an element of the cone spanned by a set `G` of elements of a convex cone `N` lies in an
extremal face `F` of `N`, then it is `0` or some generator lies in `F`. -/
private theorem eq_zero_or_exists_mem_of_mem_hull {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : PointedCone ℝ V} {F G : Set V} (hF : IsExtremalFace ℝ (N : Set V) F)
    (hG : G ⊆ N) {b : V} (hb : b ∈ PointedCone.hull ℝ G) (hbF : b ∈ F) :
    b = 0 ∨ ∃ g ∈ G, g ∈ F := by
  have hle : PointedCone.hull ℝ G ≤ N := Submodule.span_le.mpr hG
  induction hb using Submodule.span_induction with
  | mem g hg => exact Or.inr ⟨g, hg, hbF⟩
  | zero => exact Or.inl rfl
  | add x y hx hy ihx ihy =>
    obtain ⟨hxF, hyF⟩ := hF.2.2.2 x (hle hx) y (hle hy) hbF
    rcases ihx hxF with rfl | h
    · rcases ihy hyF with rfl | h
      · exact Or.inl (add_zero 0)
      · exact Or.inr h
    · exact Or.inr h
  | smul a x hx ih =>
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl (zero_smul _ _)
    · have ha' : (0 : ℝ) < a := lt_of_le_of_ne a.2 (fun h => ha (NNReal.coe_eq_zero.mp h.symm))
      have hxF : x ∈ F := by
        have := hF.2.1.2 _ hbF (a : ℝ)⁻¹ (inv_pos.mpr ha')
        rwa [show a • x = (a : ℝ) • x from rfl, smul_smul, inv_mul_cancel₀ ha'.ne',
          one_smul] at this
      rcases ih hxF with rfl | h
      · exact Or.inl (smul_zero _)
      · exact Or.inr h

/-! ### Curve forms -/

section CurveForm

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The relative curve form of `D + (1 - δ)Δ` is that of `D + Δ` minus `δ` times that of `Δ`. -/
private theorem relativeCurveForm_add_one_sub_smul {S : Scheme.{0}} (f : X ⟶ S)
    (D Δ : QDivisor X) (δ : ℚ) (h : (D + (1 - δ) • Δ).IsQCartier) (hDΔ : (D + Δ).IsQCartier)
    (hΔ : Δ.IsQCartier) (hδΔ : ((-δ) • Δ).IsQCartier) :
    QDivisor.relativeCurveForm sX f (D + (1 - δ) • Δ) h =
      QDivisor.relativeCurveForm sX f (D + Δ) hDΔ -
        (δ : ℝ) • QDivisor.relativeCurveForm sX f Δ hΔ := by
  have e : D + (1 - δ) • Δ = (D + Δ) + (-δ) • Δ := by
    rw [sub_smul, one_smul, neg_smul]; abel
  have h' : ((D + Δ) + (-δ) • Δ).IsQCartier := e ▸ h
  have hc : QDivisor.curveForm sX (D + (1 - δ) • Δ) h =
      QDivisor.curveForm sX ((D + Δ) + (-δ) • Δ) h' := by
    congr 1
  rw [QDivisor.relativeCurveForm_eq_comp, QDivisor.relativeCurveForm_eq_comp,
    QDivisor.relativeCurveForm_eq_comp, hc, QDivisor.curveForm_add sX _ _ hDΔ hδΔ,
    QDivisor.curveForm_smul sX _ _ hΔ]
  ext z
  simp [sub_eq_add_neg]

/-- The relative curve form on the class of a contracted curve is the intersection number. -/
private theorem relativeCurveForm_relativeClass {S : Scheme.{0}} (f : X ⟶ S) (D : QDivisor X)
    (h : D.IsQCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    QDivisor.relativeCurveForm sX f D h (C.relativeClass f hC) =
      (D.intersectionNumber k sX C.ι C.dim_le h : ℝ) := by
  rw [QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply,
    ← MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
  rfl

/-- The Cartier index of `D` times the relative curve form of `D` on the class of a contracted
curve is an integer. -/
private theorem exists_cartierIndex_mul_relativeCurveForm_eq_intCast {S : Scheme.{0}}
    (f : X ⟶ S) (D : QDivisor X) (h : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    ∃ N : ℤ, (D.cartierIndex h : ℝ) * QDivisor.relativeCurveForm sX f D h (C.relativeClass f hC) =
      N := by
  refine ⟨(QDivisor.isCartierDivisor_cartierIndex_smul h).toDivisor.degreeOn k sX C.ι C.dim_le
    (QDivisor.isCartierDivisor_cartierIndex_smul h).isCartier_toDivisor, ?_⟩
  rw [relativeCurveForm_relativeClass, QDivisor.intersectionNumber]
  have := QDivisor.cartierIndex_pos h
  push_cast
  field_simp

end CurveForm

/-! ### The degree bound -/

/-- The arithmetic of the degree bound: if a curve has class `t v` with
`0 < t (α + δβ) ≤ 2n`, where `α = -((K + Δ) · v) > 0`, `β = (Δ · v)` and `δ` is small, and if
`m ((K + Δ) · C) = -m t α` is an integer, then `0 < t α ≤ 2n`. -/
private theorem pos_and_le_of_mul_eq_intCast {α β δ t : ℝ} {m n : ℕ} {N : ℤ} (hα : 0 < α)
    (hδ : 0 ≤ δ) (hm : 0 < m) (hi : δ * ((|β| + 1) * (4 * n * m + 2)) < α) (ht : 0 ≤ t)
    (hpos : 0 < t * (α + δ * β)) (hle : t * (α + δ * β) ≤ 2 * n) (hN : (m : ℝ) * (t * α) = N) :
    0 < t * α ∧ t * α ≤ 2 * n := by
  set u := δ * |β| with hu
  have hu0 : 0 ≤ u := mul_nonneg hδ (abs_nonneg β)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb1 : u * (4 * n * m + 2) < α := by
    refine lt_of_le_of_lt ?_ hi
    rw [hu, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hδ
    have : (0 : ℝ) ≤ 4 * n * m + 2 := by positivity
    nlinarith
  have h2 : 2 * u < α := by nlinarith [mul_nonneg (mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ m)) hu0]
  have h3 : 4 * n * m * u < α := by nlinarith
  have hβ1 : -u ≤ δ * β := by
    rw [hu, ← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le β) hδ
  have hβ2 : -(δ * β) ≤ u := by
    rw [hu, ← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs β) hδ
  have hA : α / 2 < α + δ * β := by linarith
  have htpos : 0 < t := lt_of_le_of_ne ht (by rintro rfl; simp at hpos)
  have hta : t * α ≤ 4 * n := by nlinarith [mul_le_mul_of_nonneg_left hA.le ht]
  have h4 : t * α ≤ 2 * n + t * u := by nlinarith [mul_le_mul_of_nonneg_left hβ2 ht]
  have h5 : m * (t * u) < 1 := by
    have : m * (t * u) * α ≤ 4 * n * m * u := by
      have := mul_le_mul_of_nonneg_left hta (mul_nonneg (by linarith : (0 : ℝ) ≤ m) hu0)
      nlinarith
    by_contra h
    nlinarith [not_lt.mp h]
  have hNlt : (N : ℝ) < 2 * n * m + 1 := by
    rw [← hN]; nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ m)]
  have hNle : (N : ℝ) ≤ 2 * n * m := by
    have : N < 2 * n * m + 1 := by exact_mod_cast hNlt
    exact_mod_cast Int.lt_add_one_iff.mp this
  refine ⟨mul_pos htpos hα, ?_⟩
  rw [← hN] at hNle
  nlinarith

/-! ### Negative extremal rays -/

/-- The core of the dlt cone theorem, in linear algebra. Let `N` be a convex cone, `L`, `M`
linear forms and `δᵢ > 0` a sequence with `inf δᵢ = 0`. Suppose that for every `i` the cone `N`
is contained in `{z ∈ N | 0 ≤ (L - δᵢ M) z}` plus the cone spanned by generators `gᵢⱼ ∈ N` with
`0 < -(L - δᵢ M) gᵢⱼ ≤ 2n`, and that `m · L gᵢⱼ` is always an integer. Then every `L`-negative
vector `w` of an extremal ray of `N` is a non-negative multiple of a generator `gᵢⱼ` with
`0 < -L gᵢⱼ ≤ 2n`. -/
private theorem exists_eq_smul_of_isExtremalRay {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : PointedCone ℝ V} (L M : V →ₗ[ℝ] ℝ) {δ : ℕ → ℝ} (hδ0 : ∀ i, 0 < δ i)
    (hδ : ∀ ε, 0 < ε → ∃ i, δ i < ε) {ι : ℕ → Type*} (g : ∀ i, ι i → V) (hgN : ∀ i j, g i j ∈ N)
    (hdec : ∀ i, (N : Set V) ⊆ {z | z ∈ N ∧ 0 ≤ (L - δ i • M) z} +
      (PointedCone.hull ℝ (Set.range (g i)) : Set V))
    {n m : ℕ} (hm : 0 < m)
    (hbd : ∀ i j, 0 < -(L - δ i • M) (g i j) ∧ -(L - δ i • M) (g i j) ≤ 2 * n)
    (hint : ∀ i j, ∃ z : ℤ, (m : ℝ) * L (g i j) = z)
    {R : Set V} (hR : IsExtremalRay ℝ (N : Set V) R) {w : V} (hwR : w ∈ R) (hLw : L w < 0) :
    ∃ i j, (0 < -L (g i j) ∧ -L (g i j) ≤ 2 * n) ∧ ∃ c : ℝ, 0 ≤ c ∧ w = c • g i j := by
  obtain ⟨hRf, v, hv0, rfl⟩ := hR
  obtain ⟨c, hc0, rfl⟩ := hwR
  rw [map_smul, smul_eq_mul] at hLw
  have hαpos : 0 < -L v := neg_pos.mpr <| by
    by_contra h
    nlinarith [mul_nonneg hc0 (not_lt.mp h)]
  have hKc : 0 < (|M v| + 1) * (4 * n * m + 2) := by positivity
  obtain ⟨i, hi⟩ := hδ _ (div_pos hαpos hKc)
  rw [lt_div_iff₀ hKc] at hi
  have hP : ∀ t : ℝ, (L - δ i • M) (t • v) = -(t * (-L v + δ i * M v)) := fun t => by
    simp only [map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring
  -- `v` is still `(L - δᵢ M)`-negative, so its decomposition has no part in the half-space.
  have hLδv : 0 < -L v + δ i * M v := by
    have : δ i * |M v| ≤ δ i * ((|M v| + 1) * (4 * n * m + 2)) :=
      mul_le_mul_of_nonneg_left
        (by nlinarith [abs_nonneg (M v), (by positivity : (0 : ℝ) ≤ 4 * n * m)]) (hδ0 i).le
    nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le (M v)) (hδ0 i).le]
  have hG : Set.range (g i) ⊆ N := Set.range_subset_iff.mpr (hgN i)
  have hvR : v ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨a, ⟨haN, haL⟩, b, hb, hab⟩ := hdec i (hRf.1 hvR)
  obtain ⟨⟨ca, hca0, rfl⟩, hbR⟩ :=
    hRf.2.2.2 a haN b (Submodule.span_le.mpr hG hb) (hab ▸ hvR)
  rw [hP] at haL
  obtain rfl : v = b := by simpa [show ca = 0 by nlinarith] using hab.symm
  -- so `v` lies in the span of the generators in `R`, hence is a multiple of one of them.
  obtain h0 | ⟨_, ⟨j, rfl⟩, t, ht0, htv⟩ := eq_zero_or_exists_mem_of_mem_hull hRf hG hb hbR
  · exact absurd h0 hv0
  obtain ⟨hpos, hle⟩ := hbd i j
  obtain ⟨N, hN⟩ := hint i j
  rw [← htv, hP, neg_neg] at hpos hle
  rw [← htv, map_smul, smul_eq_mul] at hN
  obtain ⟨htα, htα'⟩ := pos_and_le_of_mul_eq_intCast hαpos (hδ0 i).le hm hi ht0 hpos hle
    (n := n) (N := -N) (by push_cast; rw [← hN]; ring)
  have hLg : -L (g i j) = t * -L v := by rw [← htv, map_smul, smul_eq_mul, mul_neg]
  have htpos : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at htα)
  refine ⟨i, j, ⟨hLg ▸ htα, hLg ▸ htα'⟩, c / t, div_nonneg hc0 ht0, ?_⟩
  rw [← htv, smul_smul, div_mul_cancel₀ _ htpos.ne']

/-- **The relative cone theorem for dlt pairs.** Let `(X, Δ)` be a dlt pair (canonical divisor
`K`, `n = dim X`) with `X` `ℚ`-factorial, over an algebraically closed field of characteristic
zero, and `f : X ⟶ S` a morphism of projective varieties. Then there is a countable family of
rational curves `C j` contracted by `f`, with `0 < -((K + Δ) · [C j]) ≤ 2n`, such that
`relativeClosedConeOfCurves sX f` is the sum of its part where `K + Δ` is non-negative and the
convex cone spanned by the classes `[C j]`. -/
@[mmp "thm_km3c_dlt_relative_cone_theorem"]
public theorem IsDltPair.exists_relativeClosedConeOfCurves_eq_add_hull
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sS : S ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sS] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ S) (hf : f ≫ sS = sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsDltPair sX n K Δ) (hX : IsQFactorial sX) :
    ∃ (ι : Type) (_ : Countable ι) (C : ι → ProperCurve sX)
      (hC : ∀ j, (C j).IsContractedBy f),
      (∀ j, IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({(C j).point} : Set X)))) ∧
      (∀ j, 0 < -QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
          ((C j).relativeClass f (hC j)) ∧
        -QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
          ((C j).relativeClass f (hC j)) ≤ 2 * n) ∧
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
        {z | z ∈ relativeClosedConeOfCurves sX f ∧
          0 ≤ QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2 z} +
        (PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass f (hC j)) :
          Set (RelativeNumericalCurveClasses sX f)) := by
  have hQ := isQCartier_of_isQFactorial sX hX
  obtain ⟨δ₀, hδ₀, hklt⟩ := hΔ.exists_forall_isKltPair_one_sub_smul hX
    (isQuasiProjective_of_isProjective
      (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sX)).isProjective)
  -- The klt cone theorem for `(X, (1 - δᵢ)Δ)`, `δᵢ = min(δ₀, 1) / (i + 2)`.
  obtain ⟨δs, hδs_pos, hδs_lt, hδs_small⟩ : ∃ δs : ℕ → ℚ, (∀ i, 0 < δs i) ∧
      (∀ i, δs i < δ₀ ∧ δs i ≤ 1) ∧ ∀ ε : ℝ, 0 < ε → ∃ i, ((δs i : ℚ) : ℝ) < ε := by
    have hδ₁ : 0 < min δ₀ 1 := lt_min hδ₀ one_pos
    refine ⟨fun i => min δ₀ 1 / (i + 2), fun i => by positivity, fun i => ?_, fun ε hε => ?_⟩
    · have h := div_lt_self hδ₁ (by norm_cast; omega : (1 : ℚ) < i + 2)
      exact ⟨h.trans_le (min_le_left _ _), h.le.trans (min_le_right _ _)⟩
    · obtain ⟨i, hi⟩ := exists_nat_gt ((min δ₀ 1 : ℚ) / ε)
      refine ⟨i, ?_⟩
      rw [div_lt_iff₀ hε] at hi
      push_cast at hi ⊢
      rw [div_lt_iff₀ (by positivity)]
      linarith
  have hkltI : ∀ i, MMP.Mori.IsKltPair sX n K ((1 - δs i) • Δ) := fun i =>
    hklt _ (hδs_pos i) (hδs_lt i).1
  choose ι hι C hC hrat hbd hdec using fun i =>
    (hkltI i).exists_relativeClosedConeOfCurves_eq_add_hull sS f hf
      (smul_nonneg (sub_nonneg.mpr (hδs_lt i).2) (Finsupp.le_def.mpr fun P => (hΔ.2.1 P).1))
  set L := QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + Δ) hΔ.1.2.2
  have hLδ : ∀ i, QDivisor.relativeCurveForm sX f (Divisor.toQDivisor K + (1 - δs i) • Δ)
      (hkltI i).1.2.2 = L - ((δs i : ℚ) : ℝ) • QDivisor.relativeCurveForm sX f Δ (hQ Δ) :=
    fun i => relativeCurveForm_add_one_sub_smul sX f _ _ _ _ _ _ (hQ _)
  let J := Σ i, {j : ι i // 0 < -L ((C i j).relativeClass f (hC i j)) ∧
    -L ((C i j).relativeClass f (hC i j)) ≤ 2 * n}
  refine ⟨J, inferInstance, fun p => C p.1 p.2.1, fun p => hC p.1 p.2.1,
    fun p => hrat p.1 p.2.1, fun p => p.2.2, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨s, R, w, hRw, rfl⟩ :=
      exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sX sS f hf hz
    classical
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 ≤ L (w i))]
    refine Set.add_mem_add ⟨Submodule.sum_mem _ fun i _ => (hRw i).1.1.1 (hRw i).2, ?_⟩
      (Submodule.sum_mem _ fun i hi => ?_)
    · rw [map_sum]
      exact Finset.sum_nonneg fun i hi => (Finset.mem_filter.mp hi).2
    obtain ⟨i', j, hj, c, hc, hw⟩ := exists_eq_smul_of_isExtremalRay L _ (N :=
        relativeClosedConeOfCurves sX f) (fun i => Rat.cast_pos.mpr (hδs_pos i)) hδs_small
      (fun i j => (C i j).relativeClass f (hC i j))
      (fun i j => subset_closure (relativeClass_mem_relativeConeOfCurves _))
      (fun i => by simpa only [hLδ] using (hdec i).subset)
      (QDivisor.cartierIndex_pos hΔ.1.2.2) (fun i j => by simpa only [hLδ] using hbd i j)
      (fun i j => exists_cartierIndex_mul_relativeCurveForm_eq_intCast sX f _ hΔ.1.2.2
        (C i j) (hC i j))
      (hRw i).1 (hRw i).2 (not_le.mp (Finset.mem_filter.mp hi).2)
    rw [hw]
    exact PointedCone.smul_mem _ hc (Submodule.subset_span ⟨⟨i', j, hj⟩, rfl⟩)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    refine (relativeClosedConeOfCurves sX f).add_mem ha.1 (Submodule.span_le.mpr ?_ hb)
    rintro _ ⟨p, rfl⟩
    exact subset_closure (relativeClass_mem_relativeConeOfCurves _)

end MMP.Mori
