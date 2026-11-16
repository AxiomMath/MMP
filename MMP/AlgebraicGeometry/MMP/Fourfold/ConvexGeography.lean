module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Four elementary lemmas of the fourfold source

Four self-contained lemmas of convex geometry, Diophantine approximation and linear groups.

## Main results

* `MMP.Fourfold.exists_isExtremalRay_neg_of_exists_neg`: a linear functional that is negative
  somewhere on a closed convex cone, on which a second functional is strictly positive away from
  zero, is negative on a nonzero extremal ray of the cone.
* `MMP.Fourfold.exists_rat_approx_one_sided`: one-sided rational approximation, with a
  prescribed Cartier grid, of a point of a rational affine subspace of `ℝ^s` that is not rational.
* `MMP.Fourfold.rational_cone_coefficients`: a rational vector in the nonnegative real cone of
  finitely many rational vectors is a nonnegative rational combination of them.
* `MMP.Fourfold.finite_of_gauge_invariant_of_hasEigenvalue_pow`: a subgroup of `GL(V)`, `V`
  complex and finite-dimensional, that preserves a positive homogeneous gauge and whose
  eigenvalues are all `N`-th roots of unity is finite.

## Implementation notes

Extremal rays are `MMP.Mori.IsExtremalRay`. The one-sided approximation is proved by
simultaneous Dirichlet approximation along a rational frame of the smallest rational affine
subspace through the point (`MMP.Fourfold.exists_rational_frame`), then by subtracting two
approximations to fix the sign of one irrational coordinate; this replaces the compact torus
argument. The finiteness of the group is proved by showing that its elements have bounded
operator norm, satisfy `g ^ N = 1`, and are uniformly separated, using that
`∑ i < N, X ^ i` is invertible at `1`.
-/

@[expose] public section

namespace MMP.Fourfold

section RationalCone

open Finset Matrix

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- A nonnegative representation whose supporting vectors are dependent can be replaced by one
with strictly smaller support. -/
theorem exists_card_filter_ne_zero_lt_of_not_linearIndependent (w : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ¬ LinearIndependent ℝ (fun i : {i // c i ≠ 0} => w i)) :
    ∃ c' : ι → ℝ, (∀ i, 0 ≤ c' i) ∧ ∑ i, c' i • w i = ∑ i, c i • w i ∧
      (univ.filter fun i => c' i ≠ 0).card < (univ.filter fun i => c i ≠ 0).card := by
  rw [Fintype.not_linearIndependent_iff] at hd
  obtain ⟨g, hg, i1, hi1⟩ := hd
  classical
  let d : ι → ℝ := fun i => if h : c i ≠ 0 then g ⟨i, h⟩ else 0
  have hd0 : ∀ i, c i = 0 → d i = 0 := fun i h => by simp [d, h]
  have hsum : ∑ i, d i • w i = 0 := by
    have : ∑ i, d i • w i = ∑ i : {i // c i ≠ 0}, g i • w i := by
      calc ∑ i, d i • w i = ∑ i ∈ univ.filter (fun i => c i ≠ 0), d i • w i := by
            rw [Finset.sum_filter_of_ne]
            intro i _ hne; by_contra h; exact hne (by simp [hd0 i (by simpa using h)])
        _ = ∑ i : {i // c i ≠ 0}, d i • w i :=
            Finset.sum_subtype _ (by simp) (fun i => d i • w i)
        _ = _ := by apply Finset.sum_congr rfl; intro i _; simp [d, i.2]
    rw [this, hg]
  have hdne : d i1 ≠ 0 := by simpa [d, i1.2] using hi1
  obtain ⟨e, he, hepos, hesum⟩ : ∃ e : ι → ℝ, (∀ i, c i = 0 → e i = 0) ∧ (∃ i, 0 < e i) ∧
      ∑ i, e i • w i = 0 := by
    rcases lt_or_gt_of_ne hdne with h | h
    · exact ⟨fun i => - d i, fun i hi => by simp [hd0 i hi], ⟨i1, by simpa using h⟩, by
        simp [neg_smul, Finset.sum_neg_distrib, hsum]⟩
    · exact ⟨d, hd0, ⟨i1, h⟩, hsum⟩
  obtain ⟨j, hj⟩ := hepos
  have hT : (univ.filter fun i => 0 < e i).Nonempty := ⟨j, by simp [hj]⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ (fun i => c i / e i) hT
  simp only [mem_filter, mem_univ, true_and] at hi0 hmin
  set t := c i0 / e i0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc _) hi0.le
  have hci0 : c i0 ≠ 0 := fun h => by simp [he i0 h] at hi0
  refine ⟨fun i => c i - t * e i, ?_, ?_, ?_⟩
  · intro i
    by_cases h : 0 < e i
    · have := hmin i h
      have : t * e i ≤ c i := by rwa [le_div_iff₀ h] at this
      linarith
    · have : e i ≤ 0 := not_lt.mp h
      nlinarith [hc i]
  · simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hesum, smul_zero,
      sub_zero]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i0, by simp [hci0], by simp [ht, div_mul_cancel₀ _ hi0.ne']⟩
    · intro i; simp only [mem_filter, mem_univ, true_and]
      intro h h'; apply h; simp [h', he i h']

/-- If rational vectors are linearly independent over `ℝ`, a rational vector that is a real
combination of them has rational coefficients. -/
theorem exists_rat_coeff_of_linearIndependent {κ : Type*} [Fintype κ] {r : ℕ}
    (u : κ → Fin r → ℚ) (hu : LinearIndependent ℝ (fun i j => (u i j : ℝ))) (x : Fin r → ℚ)
    (c : κ → ℝ) (hx : ∀ j, (x j : ℝ) = ∑ i, c i * (u i j : ℝ)) :
    ∃ q : κ → ℚ, x = ∑ i, q i • u i ∧ ∀ i, c i = q i := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) κ ℚ, ∀ j i, U j i = u i j :=
    ⟨fun j i => u i j, fun _ _ => rfl⟩
  have hinj : Function.Injective (Matrix.toLin' U) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    rw [Fintype.linearIndependent_iff] at hu
    have := hu (fun i => (q i : ℝ)) (by
      ext j
      have := congrFun hq j
      simp only [Matrix.toLin'_apply, Pi.zero_apply] at this
      have h2 := congrArg (fun a : ℚ => (a : ℝ)) this
      simpa [Matrix.mulVec, dotProduct, hU, mul_comm] using h2)
    funext i
    exact Rat.cast_eq_zero.mp (this i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' U)
    (LinearMap.ker_eq_bot.mpr hinj)
  have hGU : LinearMap.toMatrix' g * U = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  generalize LinearMap.toMatrix' g = G at hGU
  have hUc : U.map (Rat.cast : ℚ → ℝ) *ᵥ c = fun j => (x j : ℝ) := by
    funext j; rw [hx j]; simp [Matrix.mulVec, dotProduct, Matrix.map_apply, hU, mul_comm]
  have hmap : (G * U).map (Rat.cast : ℚ → ℝ) = G.map Rat.cast * U.map Rat.cast :=
    Matrix.map_mul (f := Rat.castHom ℝ)
  have hc : c = fun i => ((G *ᵥ x) i : ℝ) := by
    have h1 : c = ((G * U).map (Rat.cast : ℚ → ℝ)) *ᵥ c := by
      rw [hGU]; simp
    rw [h1, hmap]
    have h4 : (G.map (Rat.cast : ℚ → ℝ) * U.map Rat.cast) *ᵥ c
        = G.map (Rat.cast : ℚ → ℝ) *ᵥ (U.map Rat.cast *ᵥ c) := (Matrix.mulVec_mulVec ..).symm
    rw [h4, hUc]
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine ⟨G *ᵥ x, ?_, fun i => by rw [hc]⟩
  have : x = U *ᵥ (G *ᵥ x) := by
    apply funext fun j => ?_
    apply Rat.cast_injective (α := ℝ)
    have h3 := congrFun hUc j
    rw [← h3, hc]
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  conv_lhs => rw [this]
  funext j
  simp [Matrix.mulVec, dotProduct, hU, mul_comm]

/-- A nonnegative representation can be chosen with linearly independent supporting vectors. -/
theorem exists_linearIndependent_support (w : ι → E) (x : E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hx : ∑ i, c i • w i = x) :
    ∃ c' : ι → ℝ, (∀ i, 0 ≤ c' i) ∧ ∑ i, c' i • w i = x ∧
      LinearIndependent ℝ (fun i : {i // c' i ≠ 0} => w i) := by
  classical
  induction' hn : (univ.filter fun i => c i ≠ 0).card using Nat.strong_induction_on
    with n ih generalizing c
  by_cases hli : LinearIndependent ℝ (fun i : {i // c i ≠ 0} => w i)
  · exact ⟨c, hc, hx, hli⟩
  · obtain ⟨c', hc', hx', hlt⟩ :=
      exists_card_filter_ne_zero_lt_of_not_linearIndependent w c hc hli
    exact ih _ (hn ▸ hlt) c' hc' (hx'.trans hx) rfl

/-- **Rational coefficients in a rational cone.** If `x ∈ ℚ^r` lies in the nonnegative real cone
spanned by `v₁, …, v_s ∈ ℚ^r`, then `x = ∑ qᵢ vᵢ` with all `qᵢ ∈ ℚ` nonnegative. -/
@[mmp "lem_fourfold_rational_cone_coefficients"]
theorem rational_cone_coefficients {r s : ℕ} (v : Fin s → Fin r → ℚ) (x : Fin r → ℚ)
    (h : ∃ c : Fin s → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ j, (x j : ℝ) = ∑ i, c i * (v i j : ℝ)) :
    ∃ q : Fin s → ℚ, (∀ i, 0 ≤ q i) ∧ x = ∑ i, q i • v i := by
  classical
  obtain ⟨c, hc, hx⟩ := h
  obtain ⟨c', hc', hx', hli⟩ := exists_linearIndependent_support
    (fun i j => (v i j : ℝ)) (fun j => (x j : ℝ)) c hc (by
      funext j; simp [hx j])
  obtain ⟨q, hq, hcq⟩ := exists_rat_coeff_of_linearIndependent
    (fun i : {i // c' i ≠ 0} => v i) hli x (fun i => c' i) (fun j => by
      have := congrFun hx' j
      rw [← this]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.sum_subtype (univ.filter fun i => c' i ≠ 0) (p := fun i => c' i ≠ 0)
        (f := fun i => c' i * (v i j : ℝ)) (by simp)]
      rw [Finset.sum_filter_of_ne]
      intro i _ hne; by_contra hh; exact hne (by simp [hh]))
  refine ⟨fun i => if h : c' i ≠ 0 then q ⟨i, h⟩ else 0, ?_, ?_⟩
  · intro i
    by_cases h : c' i ≠ 0
    · have := hcq ⟨i, h⟩
      have h0 := hc' i
      change 0 ≤ dite _ _ _
      simp only [ne_eq, h, not_false_eq_true, dite_true]
      exact_mod_cast (this ▸ h0)
    · simp [h]
  · conv_lhs => rw [hq]
    symm
    calc _ = ∑ i ∈ univ.filter (fun i => c' i ≠ 0),
          (if h : c' i ≠ 0 then q ⟨i, h⟩ else 0) • v i := by
          rw [Finset.sum_filter_of_ne]
          intro i _ hne; by_contra hh; exact hne (by simp [hh])
      _ = ∑ i : {i // c' i ≠ 0}, (if h : c' i ≠ 0 then q ⟨i, h⟩ else 0) • v i :=
          Finset.sum_subtype _ (by simp) (fun i => (if h : c' i ≠ 0 then q ⟨i, h⟩ else 0) • v i)
      _ = _ := by apply Finset.sum_congr rfl; intro i _; simp [i.2]

end RationalCone

section NegativeRay

open Set MMP.Mori

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `h` is positive on `C ∖ {0}`, an extreme point `e` of the slice `C ∩ {h = 1}` spans the
extremal ray `{c • e | 0 ≤ c}` of `C`. -/
theorem isExtremalRay_of_mem_extremePoints (C : PointedCone ℝ E) (h : E →ₗ[ℝ] ℝ)
    (hh : ∀ x ∈ C, x ≠ 0 → 0 < h x) {e : E}
    (he : e ∈ Set.extremePoints ℝ ((C : Set E) ∩ {x | h x = 1})) :
    IsExtremalRay ℝ (C : Set E) {w | ∃ c : ℝ, 0 ≤ c ∧ c • e = w} := by
  obtain ⟨⟨heC, he1⟩, hext⟩ := he
  have hne : e ≠ 0 := by rintro rfl; simp at he1
  have hnn : ∀ x ∈ C, 0 ≤ h x := fun x hx => by
    by_cases h0 : x = 0
    · simp [h0]
    · exact (hh x hx h0).le
  have key : ∀ u v : E, u ∈ C → v ∈ C → u + v = (h u + h v) • e → ∃ c : ℝ, 0 ≤ c ∧ c • e = u := by
    intro u v hu hv huv
    by_cases hu0 : u = 0
    · exact ⟨0, le_rfl, by simp [hu0]⟩
    by_cases hv0 : v = 0
    · subst hv0
      refine ⟨h u, hnn u hu, ?_⟩
      simpa using huv.symm
    have hu' := hh u hu hu0
    have hv' := hh v hv hv0
    have hs : 0 < h u + h v := by linarith
    have hmem : e ∈ openSegment ℝ ((h u)⁻¹ • u) ((h v)⁻¹ • v) := by
      refine ⟨h u / (h u + h v), h v / (h u + h v), by positivity, by positivity, by field_simp, ?_⟩
      have : (h u + h v)⁻¹ • (u + v) = e := by
        rw [huv, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
      rw [← this, smul_add, smul_smul, smul_smul]
      congr 2 <;> field_simp
    have hA : (h u)⁻¹ • u ∈ (C : Set E) ∩ {x | h x = 1} :=
      ⟨C.smul_mem (inv_nonneg.mpr hu'.le) hu, by simp [hu'.ne']⟩
    have hB : (h v)⁻¹ • v ∈ (C : Set E) ∩ {x | h x = 1} :=
      ⟨C.smul_mem (inv_nonneg.mpr hv'.le) hv, by simp [hv'.ne']⟩
    have := hext hA hB hmem
    refine ⟨h u, hu'.le, ?_⟩
    rw [← this, smul_smul, mul_inv_cancel₀ hu'.ne', one_smul]
  refine ⟨⟨?_, ⟨⟨0, le_rfl, by simp⟩, ?_⟩, ?_, ?_⟩, ⟨e, hne, rfl⟩⟩
  · rintro w ⟨c, hc, rfl⟩
    exact C.smul_mem hc heC
  · rintro _ ⟨c, hc, rfl⟩ a ha
    exact ⟨a * c, mul_nonneg ha.le hc, by rw [mul_smul]⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    exact ⟨c + d, add_nonneg hc hd, by rw [add_smul]⟩
  · rintro u hu v hv ⟨c, hc, huv⟩
    have hc' : c = h u + h v := by
      have := congrArg h huv
      rw [map_smul, smul_eq_mul, (he1 : h e = 1), mul_one, map_add] at this
      linarith
    have huv' : u + v = (h u + h v) • e := by rw [← hc']; exact huv.symm
    exact ⟨key u v hu hv huv', key v u hv hu (by rw [add_comm, add_comm (h v)]; exact huv')⟩

/-- In finite dimension, the slice `{h = 1}` of a closed cone on which `h` is positive away from
zero is compact. -/
theorem isCompact_inter_eq_one [FiniteDimensional ℝ E] (C : PointedCone ℝ E)
    (hC : IsClosed (C : Set E)) (h : E →ₗ[ℝ] ℝ) (hh : ∀ x ∈ C, x ≠ 0 → 0 < h x) :
    IsCompact ((C : Set E) ∩ {x | h x = 1}) := by
  have hcont : Continuous h := h.continuous_of_finiteDimensional
  have hnorm : ∀ x ∈ C, x ≠ 0 → ‖x‖⁻¹ • x ∈ (C : Set E) ∩ Metric.sphere (0 : E) 1 :=
    fun x hx hx0 => ⟨C.smul_mem (inv_nonneg.mpr (norm_nonneg _)) hx, by simp [norm_smul, hx0]⟩
  refine Metric.isCompact_of_isClosed_isBounded (hC.inter (isClosed_eq hcont continuous_const)) ?_
  rcases ((C : Set E) ∩ Metric.sphere (0 : E) 1).eq_empty_or_nonempty with hS | hS
  · refine Bornology.isBounded_empty.subset fun x hx => ?_
    have h1 := hnorm x hx.1 (by rintro rfl; simp at hx)
    rw [hS] at h1
    simp at h1
  obtain ⟨y, hyS, hymin⟩ :=
    ((isCompact_sphere (0 : E) 1).inter_left hC).exists_isMinOn hS hcont.continuousOn
  have hm : 0 < h y := hh y hyS.1 (by rintro rfl; simpa using hyS.2)
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := (h y)⁻¹)).subset fun x hx => ?_
  have hxne : x ≠ 0 := by rintro rfl; simpa using hx.2
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have := hymin (hnorm x hx.1 hxne)
  change h y ≤ h (‖x‖⁻¹ • x) at this
  rw [map_smul, smul_eq_mul, hx.2, mul_one] at this
  rwa [mem_closedBall_zero_iff, le_inv_comm₀ hxn hm]

/-- The minimisers on `B` of a linear functional form an extreme subset of `B`. -/
theorem isExtreme_inter_eq_of_isMinOn {B : Set E} (d : E →ₗ[ℝ] ℝ) {z : E} (hz : IsMinOn d B z) :
    IsExtreme ℝ B (B ∩ {x | d x = d z}) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy w hw hseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have hx' : d z ≤ d x := hz hx
  have hy' : d z ≤ d y := hz hy
  have hw' : d (a • x + b • y) = d z := hw.2
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hw'
  refine ⟨hx, ?_⟩
  change d x = d z
  by_contra hne
  have : d z < d x := lt_of_le_of_ne hx' (Ne.symm hne)
  have h5 : d z * a + d z * b = d z := by rw [← mul_add, hab, mul_one]
  nlinarith [mul_pos ha (sub_pos.2 this), mul_nonneg hb.le (sub_nonneg.2 hy')]

/-- **A negative functional detects a negative extremal ray.** Let `C` be a closed convex cone in a
finite-dimensional real normed space, `h` a linear functional that is strictly positive on
`C ∖ {0}`, and `d` a linear functional that is negative at some point of `C`. Then `d` is negative
on every nonzero element of some extremal ray of `C`. -/
@[mmp "lem_fourfold_negative_ray_detects"]
theorem exists_isExtremalRay_neg_of_exists_neg [FiniteDimensional ℝ E] (C : PointedCone ℝ E)
    (hC : IsClosed (C : Set E)) (h : E →ₗ[ℝ] ℝ) (hh : ∀ x ∈ C, x ≠ 0 → 0 < h x)
    (d : E →ₗ[ℝ] ℝ) (hd : ∃ x ∈ C, d x < 0) :
    ∃ R : Set E, IsExtremalRay ℝ (C : Set E) R ∧ ∀ u ∈ R, u ≠ 0 → d u < 0 := by
  obtain ⟨x0, hx0C, hx0d⟩ := hd
  have hx0 : x0 ≠ 0 := by rintro rfl; simp at hx0d
  have hdcont : Continuous d := d.continuous_of_finiteDimensional
  set B : Set E := (C : Set E) ∩ {x | h x = 1}
  have hBc : IsCompact B := isCompact_inter_eq_one C hC h hh
  have hh0 : 0 < h x0 := hh x0 hx0C hx0
  have hx1B : (h x0)⁻¹ • x0 ∈ B :=
    ⟨C.smul_mem (inv_nonneg.mpr hh0.le) hx0C, by simp [hh0.ne']⟩
  have hx1d : d ((h x0)⁻¹ • x0) < 0 := by
    rw [map_smul, smul_eq_mul]; exact mul_neg_of_pos_of_neg (inv_pos.mpr hh0) hx0d
  obtain ⟨z, hzB, hzmin⟩ := hBc.exists_isMinOn ⟨_, hx1B⟩ hdcont.continuousOn
  set F : Set E := B ∩ {x | d x = d z}
  have hFc : IsCompact F := hBc.inter_right (isClosed_eq hdcont continuous_const)
  obtain ⟨e, he⟩ := hFc.extremePoints_nonempty ⟨z, hzB, rfl⟩
  have heB : e ∈ Set.extremePoints ℝ B :=
    (isExtreme_inter_eq_of_isMinOn d hzmin).extremePoints_subset_extremePoints he
  have hed : d e = d z := he.1.2
  have hed0 : d e < 0 := by
    rw [hed]; exact lt_of_le_of_lt (hzmin hx1B) hx1d
  refine ⟨_, isExtremalRay_of_mem_extremePoints C h hh heB, ?_⟩
  rintro u ⟨c, hc, rfl⟩ hu
  have hc0 : c ≠ 0 := by rintro rfl; simp at hu
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) hed0

end NegativeRay

section Gauge

open Polynomial Module NNReal

/-- An endomorphism of a finite-dimensional vector space over an algebraically closed field all of
whose eigenvalues vanish is nilpotent. -/
theorem isNilpotent_of_forall_hasEigenvalue_eq_zero {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (φ : End K V)
    (h : ∀ μ, φ.HasEigenvalue μ → μ = 0) : IsNilpotent φ := by
  rw [LinearMap.isNilpotent_iff_charpoly]
  have hs := (IsAlgClosed.splits φ.charpoly).eq_prod_roots
  have hm : φ.charpoly.Monic := LinearMap.charpoly_monic φ
  rw [hm.leadingCoeff, C_1, one_mul] at hs
  have hroots : ∀ a ∈ φ.charpoly.roots, a = 0 := fun a ha =>
    h a (by rwa [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← mem_roots hm.ne_zero])
  have hc : Multiset.card φ.charpoly.roots = finrank K V := by
    rw [← LinearMap.charpoly_natDegree φ]
    exact (IsAlgClosed.splits φ.charpoly).natDegree_eq_card_roots.symm
  conv_lhs => rw [hs, Multiset.eq_replicate_of_mem hroots]
  simp [Multiset.map_replicate, Multiset.prod_replicate, hc]

/-- A nonzero nilpotent endomorphism `n` has a vector `v` with `n v ≠ 0` and `n (n v) = 0`. -/
theorem exists_apply_ne_zero_apply_apply_eq_zero {R W : Type*} [Semiring R] [AddCommMonoid W]
    [Module R W] {n : End R W} (hn : IsNilpotent n) (hn0 : n ≠ 0) :
    ∃ v, n v ≠ 0 ∧ n (n v) = 0 := by
  classical
  have hex : ∃ m, n ^ m = 0 := hn
  set m := Nat.find hex
  have hmspec : n ^ m = 0 := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hmspec
    exact hn0 (by rw [← mul_one n, hmspec, mul_zero])
  have hm1 : m ≠ 1 := fun h1 => hn0 (by rwa [h1, pow_one] at hmspec)
  obtain ⟨j, hj⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hnj : n ^ (j + 1) ≠ 0 := Nat.find_min hex (by omega)
  obtain ⟨v, hv⟩ : ∃ v, (n ^ (j + 1)) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnj (LinearMap.ext hcon)
  refine ⟨(n ^ j) v, by rwa [← Module.End.mul_apply, ← pow_succ'], ?_⟩
  have : n ^ (j + 2) = 0 := by rw [← hj]; exact hmspec
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_two, ← pow_add, add_comm, this]
  rfl

/-- A unipotent endomorphism whose powers are uniformly bounded in norm is the identity. -/
theorem eq_one_of_isNilpotent_sub_one_of_bounded_pow {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (h : End ℂ W) (hn : IsNilpotent (h - 1)) (M : ℝ)
    (hb : ∀ k : ℕ, ∀ v, ‖(h ^ k) v‖ ≤ M * ‖v‖) : h = 1 := by
  by_contra hne
  set n : End ℂ W := h - 1 with hndef
  obtain ⟨v', hw0, hnw⟩ :=
    exists_apply_ne_zero_apply_apply_eq_zero hn fun h0 => hne (sub_eq_zero.mp h0)
  set w := n v' with hw
  have hhn : ∀ x, h x = x + n x := fun x => by simp [hndef]
  have hpow : ∀ k : ℕ, (h ^ k) v' = v' + (k : ℂ) • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hhn, map_add, map_smul, hnw]
      simp [add_smul, ← hw]
      abel
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨k, hk⟩ := exists_nat_gt ((M + 1) * ‖v'‖ / ‖w‖)
  have h1 := hb k v'
  rw [hpow] at h1
  have h2 : (k : ℝ) * ‖w‖ - ‖v'‖ ≤ ‖v' + (k : ℂ) • w‖ := by
    have := norm_sub_norm_le ((k : ℂ) • w) (-v')
    rw [norm_smul, norm_neg] at this
    simp only [Complex.norm_natCast] at this
    calc (k : ℝ) * ‖w‖ - ‖v'‖ ≤ ‖(k : ℂ) • w - -v'‖ := by
          simpa [Complex.norm_natCast, norm_smul] using this
      _ = _ := by rw [sub_neg_eq_add, add_comm]
  rw [div_lt_iff₀ hwpos] at hk
  nlinarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- A gauge that is homogeneous of degree `α` is determined by its values on the unit sphere. -/
theorem coe_eq_norm_rpow_mul_of_homogeneous (p : V → ℝ≥0) {α : ℝ}
    (hhom : ∀ (c : ℂ) (v : V), p (c • v) = ‖c‖₊ ^ α * p v) {v : V} (hv : v ≠ 0) :
    (p v : ℝ) = ‖v‖ ^ α * p ((‖v‖ : ℂ)⁻¹ • v) := by
  have hhom' : ∀ (c : ℂ) (v : V), (p (c • v) : ℝ) = ‖c‖ ^ α * p v := fun c v => by
    simpa [NNReal.coe_rpow] using congrArg NNReal.toReal (hhom c v)
  have := hhom' (‖v‖ : ℂ) ((‖v‖ : ℂ)⁻¹ • v)
  rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast (norm_pos_iff.mpr hv).ne'), one_smul] at this
  simpa using this

/-- Linear maps preserving a continuous positive homogeneous gauge are uniformly bounded in
operator norm. -/
theorem exists_bound_of_gauge [Nontrivial V] (p : V → ℝ≥0) (hp : Continuous p)
    (hpos : ∀ v, v ≠ 0 → 0 < p v) {α : ℝ} (hα : 0 < α)
    (hhom : ∀ (c : ℂ) (v : V), p (c • v) = ‖c‖₊ ^ α * p v)
    (S : Set (V →ₗ[ℂ] V)) (hS : ∀ g ∈ S, ∀ v, p (g v) = p v) :
    ∃ M : ℝ, ∀ g ∈ S, ∀ v, ‖g v‖ ≤ M * ‖v‖ := by
  have hsph : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere _ _
  obtain ⟨y, hy, hymin⟩ := hsph.exists_isMinOn (NormedSpace.sphere_nonempty.mpr zero_le_one)
    hp.continuousOn
  obtain ⟨z, hz, hzmax⟩ := hsph.exists_isMaxOn (NormedSpace.sphere_nonempty.mpr zero_le_one)
    hp.continuousOn
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hc0 : 0 < (p y : ℝ) := by exact_mod_cast hpos y hy0
  have hlow : ∀ v, (p y : ℝ) * ‖v‖ ^ α ≤ p v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [Real.zero_rpow hα.ne']
    have hu : ((‖v‖ : ℂ)⁻¹ • v) ∈ Metric.sphere (0 : V) 1 := by simp [norm_smul, hv]
    have h1 : (p y : ℝ) ≤ p ((‖v‖ : ℂ)⁻¹ • v) := by exact_mod_cast hymin hu
    rw [coe_eq_norm_rpow_mul_of_homogeneous p hhom hv, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (norm_nonneg _) _)
  have hup : ∀ v, (p v : ℝ) ≤ (p z : ℝ) * ‖v‖ ^ α := by
    intro v
    by_cases hv : v = 0
    · subst hv
      have : p 0 = 0 := by
        simpa [Real.zero_rpow hα.ne', NNReal.zero_rpow hα.ne'] using hhom 0 0
      simp [this, Real.zero_rpow hα.ne']
    have hu : ((‖v‖ : ℂ)⁻¹ • v) ∈ Metric.sphere (0 : V) 1 := by simp [norm_smul, hv]
    have h1 : (p ((‖v‖ : ℂ)⁻¹ • v) : ℝ) ≤ p z := by exact_mod_cast hzmax hu
    rw [coe_eq_norm_rpow_mul_of_homogeneous p hhom hv, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨((p z : ℝ) / p y) ^ (1 / α), fun g hg v => ?_⟩
  have h1 : (p y : ℝ) * ‖g v‖ ^ α ≤ (p z : ℝ) * ‖v‖ ^ α := by
    calc (p y : ℝ) * ‖g v‖ ^ α ≤ p (g v) := hlow _
      _ = p v := by rw [hS g hg v]
      _ ≤ _ := hup v
  have h2 : ‖g v‖ ^ α ≤ ((p z : ℝ) / p y) * ‖v‖ ^ α := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]; linarith
  have ht : 0 ≤ (p z : ℝ) / p y := by positivity
  have h3 : ‖g v‖ ^ α ≤ (((p z : ℝ) / p y) ^ (1 / α) * ‖v‖) ^ α := by
    rwa [Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.rpow_mul ht,
      one_div_mul_cancel hα.ne', Real.rpow_one]
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hα).mp h3

/-- If the elements of a subgroup `G ≤ GL(V)` are uniformly bounded in operator norm and all their
eigenvalues are `N`-th roots of unity, then `g ^ N = 1` for all `g ∈ G`. -/
theorem pow_eq_one_of_bounded_of_hasEigenvalue_pow (G : Subgroup (V →ₗ[ℂ] V)ˣ)
    (M : ℝ) (hM : ∀ x ∈ G, ∀ v, ‖(x : V →ₗ[ℂ] V) v‖ ≤ M * ‖v‖) (N : ℕ) (hN : 0 < N)
    (heig : ∀ x ∈ G, ∀ μ : ℂ, Module.End.HasEigenvalue (x : V →ₗ[ℂ] V) μ → μ ^ N = 1)
    (x : (V →ₗ[ℂ] V)ˣ) (hx : x ∈ G) : x ^ N = 1 := by
  set h : Module.End ℂ V := (x : V →ₗ[ℂ] V) ^ N with hh
  have hnil : IsNilpotent (h - 1) := by
    apply isNilpotent_of_forall_hasEigenvalue_eq_zero
    intro μ hμ
    have hmem : μ + 1 ∈ spectrum ℂ h := by
      rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
      have := Module.End.mem_eigenspace_iff.mp hv.1
      rw [Module.End.mem_eigenspace_iff]
      rw [LinearMap.sub_apply, Module.End.one_apply] at this
      rw [add_smul, ← this]; simp
    rw [hh, spectrum.map_pow_of_pos _ hN] at hmem
    obtain ⟨l, hl, hl'⟩ := hmem
    have := heig x hx l (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hl)
    simp only at hl'
    rw [this] at hl'
    linear_combination -hl'
  have hb : ∀ k : ℕ, ∀ v, ‖(h ^ k) v‖ ≤ M * ‖v‖ := by
    intro k v
    have : h ^ k = ((x ^ (N * k) : (V →ₗ[ℂ] V)ˣ) : V →ₗ[ℂ] V) := by
      rw [hh, ← pow_mul]; simp
    rw [this]
    exact hM _ (G.pow_mem hx _) v
  exact Units.ext (eq_one_of_isNilpotent_sub_one_of_bounded_pow h hnil M hb)

/-- In `V →L[ℂ] V`, the identity is isolated among the solutions of `k ^ N = 1`. -/
theorem exists_pos_forall_eq_one_of_pow_eq_one_of_dist_lt {N : ℕ} (hN : 0 < N) :
    ∃ ε > 0, ∀ k : V →L[ℂ] V, k ^ N = 1 → dist k 1 < ε → k = 1 := by
  have hcont : Continuous fun k : V →L[ℂ] V => ∑ i ∈ Finset.range N, k ^ i := by fun_prop
  have h1 : IsUnit (∑ i ∈ Finset.range N, (1 : V →L[ℂ] V) ^ i) := by
    simp only [one_pow, Finset.sum_const, Finset.card_range]
    have : (N : V →L[ℂ] V) = algebraMap ℂ (V →L[ℂ] V) N := by simp
    rw [nsmul_one, this]
    exact (IsUnit.mk0 (N : ℂ) (by exact_mod_cast hN.ne')).map _
  have hopen : IsOpen {k : V →L[ℂ] V | IsUnit (∑ i ∈ Finset.range N, k ^ i)} :=
    Units.isOpen.preimage hcont
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen 1 h1
  refine ⟨ε, hε, fun k hk hd => ?_⟩
  have hu : IsUnit (∑ i ∈ Finset.range N, k ^ i) := hsub hd
  have h0 : (k - 1) * ∑ i ∈ Finset.range N, k ^ i = 0 := by rw [mul_geom_sum, hk, sub_self]
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp h0)

/-- If `Φ a⁻¹` has norm at most `M` and `Φ (a⁻¹ * b)` is at distance at least `ε` from `1`, then
`Φ a` and `Φ b` are at distance at least `ε / M`. -/
theorem div_le_dist_of_le_dist_map_inv_mul {A R : Type*} [Monoid A] [NormedRing R]
    (Φ : A →* R) {a b : Aˣ} {ε M : ℝ} (hM : 0 < M) (ha : ‖Φ ((a⁻¹ : Aˣ) : A)‖ ≤ M)
    (h : ε ≤ dist (Φ ((a⁻¹ * b : Aˣ) : A)) 1) : ε / M ≤ dist (Φ a) (Φ b) := by
  have hid : Φ ((a⁻¹ * b : Aˣ) : A) - 1 = Φ ((a⁻¹ : Aˣ) : A) * (Φ b - Φ a) := by
    rw [mul_sub, ← map_mul, ← map_mul, Units.inv_mul, map_one, Units.val_mul]
  rw [dist_eq_norm, hid] at h
  rw [dist_comm, dist_eq_norm, div_le_iff₀ hM]
  have := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg (Φ b - Φ a)))
  linarith

/-- A subset of a closed ball in a proper space whose distinct points are at distance at least
`ε > 0` from each other is finite. -/
theorem finite_of_subset_closedBall_of_le_dist {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {T : Set X} {x : X} {R ε : ℝ} (hε : 0 < ε) (hT : T ⊆ Metric.closedBall x R)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ε ≤ dist a b) : T.Finite := by
  classical
  obtain ⟨t, -, htfin, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall x R)
    (half_pos hε)
  have hex : ∀ A ∈ T, ∃ c ∈ t, A ∈ Metric.ball c (ε / 2) := fun A hA => by
    have := hcov (hT hA)
    simp only [Set.mem_iUnion] at this
    obtain ⟨c, hc, hAc⟩ := this
    exact ⟨c, hc, hAc⟩
  choose! f hft hfA using hex
  refine Set.Finite.of_injOn (f := f) (t := t) (fun A hA => hft A hA) ?_ htfin
  intro A hA B hB hAB
  by_contra hne
  have h1 := hfA A hA
  have h2 := hfA B hB
  rw [hAB] at h1
  rw [Metric.mem_ball] at h1 h2
  linarith [dist_triangle_right A B (f B), hsep A hA B hB hne]

/-- A subgroup of `GL(V)` of uniformly bounded operator norm in which `g ^ N = 1` for all elements
is finite. -/
theorem finite_of_bounded_of_pow_eq_one (G : Subgroup (V →ₗ[ℂ] V)ˣ) (M : ℝ)
    (hM1 : 0 < M) (hM : ∀ x ∈ G, ∀ v, ‖(x : V →ₗ[ℂ] V) v‖ ≤ M * ‖v‖) (N : ℕ) (hN : 0 < N)
    (hpow : ∀ x ∈ G, x ^ N = 1) : Finite G := by
  let Φ : (V →ₗ[ℂ] V) →* (V →L[ℂ] V) :=
    { toFun := LinearMap.toContinuousLinearMap
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl }
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext v; exact congrArg (fun f : V →L[ℂ] V => f v) hab
  obtain ⟨ε, hε, hiso⟩ := exists_pos_forall_eq_one_of_pow_eq_one_of_dist_lt (V := V) hN
  have hbd : ∀ x ∈ G, ‖Φ (x : V →ₗ[ℂ] V)‖ ≤ M := fun x hx =>
    ContinuousLinearMap.opNorm_le_bound _ hM1.le (fun v => hM x hx v)
  have hsep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      ε / M ≤ dist (Φ (x : V →ₗ[ℂ] V)) (Φ (y : V →ₗ[ℂ] V)) := by
    intro x hx y hy hxy
    refine div_le_dist_of_le_dist_map_inv_mul Φ hM1 (hbd _ (G.inv_mem hx))
      (not_lt.mp fun hlt => hxy ?_)
    have h1 : Φ ((x⁻¹ * y : (V →ₗ[ℂ] V)ˣ) : V →ₗ[ℂ] V) = Φ 1 := by
      rw [map_one]
      refine hiso _ ?_ hlt
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hpow _ (G.mul_mem (G.inv_mem hx) hy),
        Units.val_one, map_one]
    have := Units.ext (u := x⁻¹ * y) (v := 1) (hΦinj h1)
    simpa using (congrArg (x * ·) this).symm
  let T : Set (V →L[ℂ] V) := {A | ∃ x ∈ G, Φ (x : V →ₗ[ℂ] V) = A}
  have hTK : T ⊆ Metric.closedBall 0 M := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hbd x hx)
  have hTfin : T.Finite := finite_of_subset_closedBall_of_le_dist (div_pos hε hM1) hTK (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    exact hsep x hx y hy fun h => hne (by rw [h]))
  have : Finite T := hTfin.to_subtype
  refine Finite.of_injective (β := T)
    (fun x : G => ⟨Φ ((x : (V →ₗ[ℂ] V)ˣ) : V →ₗ[ℂ] V), x, x.2, rfl⟩) fun a b hab =>
    Subtype.ext (Units.ext (hΦinj (congrArg Subtype.val hab)))

/-- **An invariant positive gauge and bounded root orders force a finite image.** Let `V` be a
finite-dimensional complex normed space and `G ≤ GL(V)` a subgroup. Suppose a continuous
`p : V → ℝ≥0` is positive off zero, satisfies `p (c • v) = ‖c‖ ^ α * p v` for a fixed `α > 0`, and
is preserved by `G`. If one `N > 0` makes every eigenvalue of every element of `G` an `N`-th root
of unity, then `G` is finite. (The norm only fixes the topology on `V`.) -/
@[mmp "lem_fourfold_positive_gauge_finite_linear_image"]
theorem finite_of_gauge_invariant_of_hasEigenvalue_pow (G : Subgroup (V →ₗ[ℂ] V)ˣ) (p : V → ℝ≥0)
    (hp : Continuous p) (hpos : ∀ v, v ≠ 0 → 0 < p v) {α : ℝ} (hα : 0 < α)
    (hhom : ∀ (c : ℂ) (v : V), p (c • v) = ‖c‖₊ ^ α * p v)
    (hG : ∀ g ∈ G, ∀ v, p ((g : V →ₗ[ℂ] V) v) = p v) {N : ℕ} (hN : 0 < N)
    (heig : ∀ g ∈ G, ∀ μ : ℂ, Module.End.HasEigenvalue (g : V →ₗ[ℂ] V) μ → μ ^ N = 1) :
    Finite G := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Subsingleton (V →ₗ[ℂ] V) := inferInstance
    have : Subsingleton (V →ₗ[ℂ] V)ˣ := inferInstance
    infer_instance
  · obtain ⟨M, hM⟩ := exists_bound_of_gauge p hp hpos hα hhom
      {g | ∃ x ∈ G, (x : V →ₗ[ℂ] V) = g} (by rintro _ ⟨x, hx, rfl⟩ v; exact hG x hx v)
    have hM' : ∀ x ∈ G, ∀ v, ‖(x : V →ₗ[ℂ] V) v‖ ≤ max M 1 * ‖v‖ := fun x hx v =>
      (hM _ ⟨x, hx, rfl⟩ v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    exact finite_of_bounded_of_pow_eq_one G (max M 1)
      (lt_of_lt_of_le one_pos (le_max_right _ _)) hM' N hN
      (pow_eq_one_of_bounded_of_hasEigenvalue_pow G (max M 1) hM' N hN heig)

end Gauge

section OneSided

open Filter Topology

/-- For every `η > 0` and `K`, some `n > K` brings all of the `n * a i` within `η` of integers. -/
theorem exists_large_approx {m : ℕ} (a : Fin m → ℝ) {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∃ n : ℕ, K < n ∧ ∃ M : Fin m → ℤ, ∀ i, |(n : ℝ) * a i - M i| < η := by
  let x : ℕ → (Fin m → ℝ) := fun n i => Int.fract ((n : ℝ) * a i)
  have hx : ∀ n, x n ∈ Set.Icc (0 : Fin m → ℝ) 1 := fun n =>
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := 1)).tendsto_subseq hx
  have hshift : Tendsto (fun k => x (φ (k + (K + 1)))) atTop (𝓝 y) :=
    hlim.comp (tendsto_add_atTop_nat (K + 1))
  have hdiff : Tendsto (fun k => x (φ (k + (K + 1))) - x (φ k)) atTop (𝓝 0) := by
    simpa using hshift.sub hlim
  rw [tendsto_pi_nhds] at hdiff
  have hev : ∀ᶠ k in atTop, ∀ i, |(x (φ (k + (K + 1))) - x (φ k)) i| < η := by
    rw [eventually_all]
    intro i
    filter_upwards [Metric.tendsto_nhds.mp (hdiff i) η hη] with k hk
    simpa [Real.dist_eq] using hk
  obtain ⟨k, hk⟩ := hev.exists
  have hmono : ∀ k j : ℕ, φ k + j ≤ φ (k + j) := fun k j => by
    induction j with
    | zero => simp
    | succ j ih =>
      have : φ (k + j) < φ (k + (j + 1)) := hφ (by omega)
      omega
  refine ⟨φ (k + (K + 1)) - φ k, ?_,
    fun i => ⌊((φ (k + (K + 1)) : ℕ) : ℝ) * a i⌋ - ⌊((φ k : ℕ) : ℝ) * a i⌋, fun i => ?_⟩
  · have := hmono k (K + 1)
    omega
  · have h2 := hk i
    have hle : φ k ≤ φ (k + (K + 1)) := hφ.monotone (by omega)
    simp only [x, Pi.sub_apply, Int.fract] at h2
    rw [Nat.cast_sub hle]
    push_cast
    convert h2 using 2
    ring

/-- If `|u i| < η` for all `i`, then `|∑ i, u i * c i| ≤ η * ∑ i, |c i|`. -/
theorem abs_sum_mul_le {m : ℕ} (u c : Fin m → ℝ) {η : ℝ} (h : ∀ i, |u i| < η) :
    |∑ i, u i * c i| ≤ η * ∑ i, |c i| := by
  calc |∑ i, u i * c i| ≤ ∑ i, |u i * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, η * |c i| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (h i).le (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- Simultaneous approximation with arbitrarily large multiplier, in which the error pairs
negatively with a prescribed vector whenever no error pairs to zero. -/
theorem exists_large_approx_neg {m : ℕ} (a c : Fin m → ℝ) {η : ℝ} (hη : 0 < η) (K : ℕ)
    (hnz : ∀ n : ℕ, 0 < n → ∀ M : Fin m → ℤ, ∑ i, ((n : ℝ) * a i - M i) * c i ≠ 0) :
    ∃ n : ℕ, K < n ∧ ∃ M : Fin m → ℤ, (∀ i, |(n : ℝ) * a i - M i| < η) ∧
      ∑ i, ((n : ℝ) * a i - M i) * c i < 0 := by
  have hC : 0 < 1 + ∑ i, |c i| := by positivity
  obtain ⟨n2, hn2, M2, hM2⟩ := exists_large_approx a (half_pos hη) K
  by_cases hneg : ∑ i, ((n2 : ℝ) * a i - M2 i) * c i < 0
  · exact ⟨n2, hn2, M2, fun i => (hM2 i).trans (half_lt_self hη), hneg⟩
  have hpos : 0 < ∑ i, ((n2 : ℝ) * a i - M2 i) * c i :=
    lt_of_le_of_ne (not_lt.mp hneg) (hnz n2 (by omega) M2).symm
  set v2 := ∑ i, ((n2 : ℝ) * a i - M2 i) * c i with hv2
  obtain ⟨n1, hn1, M1, hM1⟩ := exists_large_approx a
    (lt_min (half_pos hη) (div_pos hpos hC)) (n2 + K)
  refine ⟨n1 - n2, by omega, fun i => M1 i - M2 i, ?_, ?_⟩
  · intro i
    have h1 := (hM1 i).trans_le (min_le_left _ _)
    have h2 := hM2 i
    rw [Nat.cast_sub (by omega)]
    push_cast
    calc _ = |((n1 : ℝ) * a i - M1 i) - ((n2 : ℝ) * a i - M2 i)| := by ring_nf
      _ ≤ |(n1 : ℝ) * a i - M1 i| + |(n2 : ℝ) * a i - M2 i| := abs_sub _ _
      _ < η := by linarith
  · have h1 : ∀ i, |(n1 : ℝ) * a i - M1 i| < v2 / (1 + ∑ i, |c i|) := fun i =>
      (hM1 i).trans_le (min_le_right _ _)
    have h3 := abs_sum_mul_le _ c h1
    have h4 : ∑ i, ((n1 : ℝ) * a i - M1 i) * c i < v2 := by
      have := (le_abs_self _).trans h3
      have h5 : v2 / (1 + ∑ i, |c i|) * ∑ i, |c i| < v2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hC]
        have : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
        nlinarith
      linarith
    have : ∑ i, (((n1 - n2 : ℕ) : ℝ) * a i - ((M1 i - M2 i : ℤ) : ℝ)) * c i
        = ∑ i, ((n1 : ℝ) * a i - M1 i) * c i - v2 := by
      rw [hv2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; linarith

/-- A finite family of rationals has a common denominator. -/
theorem exists_den {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ z : ℤ, (D : ℚ) * q i = z := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).den_pos, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)
  refine ⟨c * (q i).num, ?_⟩
  rw [hc]
  push_cast
  rw [mul_right_comm, Rat.den_mul_eq_num, mul_comm]

/-- A real vector that is not rational has an irrational coordinate. -/
theorem exists_irrational_of_notMem_range {ι : Type*} {θ : ι → ℝ}
    (hθ : θ ∉ Set.range (fun (q : ι → ℚ) (j : ι) => (q j : ℝ))) : ∃ j, Irrational (θ j) := by
  by_contra! hcon
  choose q hq using fun j => (not_not.mp (hcon j) : θ j ∈ Set.range ((↑) : ℚ → ℝ))
  exact hθ ⟨q, funext hq⟩

/-- The error of the approximation `P + (∑ i, Mᵢ uᵢ) / (N n)` of `t = P + ∑ i, svᵢ uᵢ`. -/
theorem add_sum_div_sub_eq_neg_one_div_mul_sum {m : ℕ} {t P N n : ℝ} (sv u : Fin m → ℝ)
    (ht : t = P + ∑ i, sv i * u i) (M : Fin m → ℤ) (hN : N ≠ 0) (hn : n ≠ 0) :
    P + (∑ i, (M i : ℝ) * u i) / (N * n) - t
      = -(1 / (N * n)) * ∑ i, (n * (N * sv i) - M i) * u i := by
  have : ∑ i, (n * (N * sv i) - M i) * u i = N * n * ∑ i, sv i * u i - ∑ i, (M i : ℝ) * u i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, ht]
  field_simp
  ring

/-- If `P + ∑ i, svᵢ uᵢ` is irrational, with `P` and the `uᵢ` rational, then the errors
`n N svᵢ - Mᵢ` never pair to zero with `u`. -/
theorem sum_sub_mul_ne_zero_of_irrational {m N n : ℕ} {P : ℚ} {u : Fin m → ℚ} {sv : Fin m → ℝ}
    (hN : 0 < N) (hirr : Irrational (P + ∑ i, sv i * u i)) (hn : 0 < n) (M : Fin m → ℤ) :
    ∑ i, ((n : ℝ) * (N * sv i) - M i) * (u i : ℝ) ≠ 0 := by
  intro h0
  refine hirr ⟨P + (∑ i, (M i : ℚ) * u i) / (N * n), ?_⟩
  have := add_sum_div_sub_eq_neg_one_div_mul_sum (P := (P : ℝ)) sv (fun i => (u i : ℝ)) rfl M
    (Nat.cast_ne_zero.mpr hN.ne') (Nat.cast_ne_zero.mpr hn.ne')
  simp only [h0, mul_zero, sub_eq_zero] at this
  push_cast
  linarith

/-- Clearing the denominators of `P + (∑ i, Mᵢ uᵢ) / (N n)` with a common denominator `D` of `P`
and the `uᵢ`. -/
theorem exists_int_eq_mul_add_sum_div {m : ℕ} {P : ℚ} {u : Fin m → ℚ} {D N n r : ℕ}
    (hP : ∃ z : ℤ, (D : ℚ) * P = z) (hu : ∀ i, ∃ z : ℤ, (D : ℚ) * u i = z) (M : Fin m → ℤ)
    (hN : 0 < N) (hn : 0 < n) (hr : 0 < r) :
    ∃ z : ℤ, ((N * r * D * n : ℕ) : ℚ) * (P + (∑ i, (M i : ℚ) * u i) / (N * n)) / r = z := by
  obtain ⟨zp, hzp⟩ := hP
  choose ze hze using hu
  refine ⟨n * N * zp + ∑ i, M i * ze i, ?_⟩
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  rw [← hzp]
  have : ∑ i, (M i : ℚ) * (ze i : ℚ) = D * ∑ i, (M i : ℚ) * u i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hze i]; ring
  rw [this]
  field_simp

/-- If `|u i| < η` for all `i`, `∑ i, |c i| ≤ T` and `η T < δ / R`, then
`|-(1 / L) * ∑ i, u i * c i| < δ / (L * R)`. -/
theorem abs_neg_one_div_mul_sum_lt {m : ℕ} (u c : Fin m → ℝ) {η T δ L R : ℝ}
    (hu : ∀ i, |u i| < η) (hη : 0 < η) (hc : ∑ i, |c i| ≤ T) (hlt : η * T < δ / R)
    (hL : 0 < L) : |-(1 / L) * ∑ i, u i * c i| < δ / (L * R) := by
  have hb := (abs_sum_mul_le u c hu).trans (mul_le_mul_of_nonneg_left hc hη.le)
  rw [abs_mul, abs_neg, abs_div, abs_one, abs_of_pos hL]
  calc 1 / L * |∑ i, u i * c i| ≤ 1 / L * (η * T) := by gcongr
    _ < 1 / L * (δ / R) := by gcongr
    _ = δ / (L * R) := by rw [div_mul_div_comm, one_mul]

/-- **One-sided rational approximation with a prescribed Cartier grid.** Let `W ⊆ ℝ^s` be a
rational affine subspace and `θ ∈ W` a point that is not rational. For all positive integers `r`,
`N` and every `δ > 0`, there are arbitrarily large multiples `k` of `N` and points
`φ ∈ W ∩ ℚ^s` with `k φ / r ∈ ℤ^s`, `‖φ - θ‖ < δ / k` (maximum norm), and `θ j < φ j` for some
index `j` at which `θ j` is irrational. Arbitrarily large means: for every `K` there is such a
`k > K`. -/
@[mmp "lem_fourfold_one_sided_rational_approximation"]
theorem exists_rat_approx_one_sided {s : ℕ} {W : Set (Fin s → ℝ)}
    (hW : IsRationalAffineSubspace W) {θ : Fin s → ℝ} (hθ : θ ∈ W)
    (hθq : θ ∉ Set.range (fun (q : Fin s → ℚ) (j : Fin s) => (q j : ℝ)))
    {r N : ℕ} (hr : 0 < r) (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) (K : ℕ) :
    ∃ k : ℕ, K < k ∧ N ∣ k ∧ ∃ φ : Fin s → ℚ, (fun j => (φ j : ℝ)) ∈ W ∧
      (∀ j, ∃ z : ℤ, (k : ℚ) * φ j / r = z) ∧ ‖(fun j => (φ j : ℝ)) - θ‖ < δ / k ∧
      ∃ j, Irrational (θ j) ∧ θ j < φ j := by
  classical
  obtain ⟨j0, hj0⟩ := exists_irrational_of_notMem_range hθq
  obtain ⟨m, p, e, -, hpH, hfr⟩ := exists_rational_frame θ
  obtain ⟨sv, hsv⟩ := (hfr θ).mp (self_mem_rationalAffineHull θ)
  obtain ⟨D, hDpos, hDpe⟩ := exists_den (Sum.elim p fun x : Fin m × Fin s => e x.1 x.2)
  have hθj : ∀ j, θ j = (p j : ℝ) + ∑ i, sv i * (e i j : ℝ) := fun j => congrFun hsv j
  have hirr : Irrational ((p j0 : ℝ) + ∑ i, sv i * (e i j0 : ℝ)) := by rw [← hθj j0]; exact hj0
  set T : ℝ := ∑ j, ∑ i, |(e i j : ℝ)|
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hrD : 0 < (r : ℝ) * D := by positivity
  set η : ℝ := δ / (2 * (r * D) * (T + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hlt : η * T < δ / (r * D) := by
    rw [hη, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) hrD]
    nlinarith [mul_pos hδ hrD]
  obtain ⟨n, hn, M, hM, hneg⟩ := exists_large_approx_neg (fun i => (N : ℝ) * sv i)
    (fun i => (e i j0 : ℝ)) hηpos K fun n hn M =>
      sum_sub_mul_ne_zero_of_irrational (u := fun i => e i j0) hN hirr hn M
  have hnpos : 0 < n := by omega
  have hNn : (0 : ℝ) < N * n := by positivity
  set k : ℕ := N * r * D * n with hk
  have hkpos : (0 : ℝ) < k := by positivity
  set φ : Fin s → ℚ := fun j => p j + (∑ i, (M i : ℚ) * e i j) / (N * n) with hφ
  have hφR : ∀ j, (φ j : ℝ) = (p j : ℝ) + (∑ i, (M i : ℝ) * (e i j : ℝ)) / (N * n) := fun j => by
    simp only [hφ]; push_cast; rfl
  have hdiff : ∀ j, (φ j : ℝ) - θ j
      = -(1 / ((N : ℝ) * n)) * ∑ i, ((n : ℝ) * (N * sv i) - M i) * (e i j : ℝ) := fun j => by
    rw [hφR]
    exact add_sum_div_sub_eq_neg_one_div_mul_sum sv (fun i => (e i j : ℝ)) (hθj j) M
      (Nat.cast_ne_zero.mpr hN.ne') (Nat.cast_ne_zero.mpr hnpos.ne')
  refine ⟨k, ?_, ⟨r * D * n, by rw [hk]; ring⟩, φ, ?_, fun j => ?_, ?_, j0, hj0, ?_⟩
  · exact hn.trans_le (Nat.le_mul_of_pos_left n (by positivity))
  · apply rationalAffineHull_le hW hθ
    refine (hfr _).mpr ⟨fun i => (M i : ℝ) / (N * n), ?_⟩
    funext j
    rw [hφR, Finset.sum_div]
    simp only [div_mul_eq_mul_div]
  · exact exists_int_eq_mul_add_sum_div (hDpe (.inl j)) (fun i => hDpe (.inr (i, j))) M hN
      hnpos hr
  · refine (pi_norm_lt_iff (by positivity)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    change |(φ j : ℝ) - θ j| < δ / k
    rw [hdiff j, show (k : ℝ) = N * n * (r * D) by rw [hk]; push_cast; ring]
    exact abs_neg_one_div_mul_sum_lt _ (fun i => (e i j : ℝ)) hM hηpos
      (Finset.single_le_sum (f := fun j => ∑ i, |(e i j : ℝ)|)
        (fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ j)) hlt hNn
  · have : 0 < (φ j0 : ℝ) - θ j0 := by
      rw [hdiff j0]
      exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr (by positivity)) hneg
    linarith

end OneSided

end MMP.Fourfold
