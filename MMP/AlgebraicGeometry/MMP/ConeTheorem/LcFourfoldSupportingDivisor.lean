module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConeTheorem.LcRelativeCone
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Intersection.N1CartierCoordinates
public import MMP.AlgebraicGeometry.Positivity.Kleiman.AbsoluteCartier
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConvexGeography
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# A rational supporting divisor for a negative extremal ray of an lc fourfold

Let `(X, B)` be a log canonical pair with `ℚ`-boundary on a normal projective complex fourfold,
with canonical divisor `K`, and let `R` be a `(K + B)`-negative extremal ray of the closed cone
of curves `NE̅(X)`. Then `R` is cut out of `NE̅(X)` by a nef Cartier divisor `L`,
`NE̅(X) ∩ L^⊥ = R`, and `L` can be chosen so that `a L - (K + B)` is ample for some positive
rational number `a`.

The proof uses the lc cone theorem: for an ample `A` and small `ε > 0`,
`NE̅(X) = NE̅(X)_{K+B+εA ≥ 0} + R₁ + ⋯ + Rₘ` with finitely many rays, one of which is `R`, each
spanned by the class of a curve. The supporting forms of `R` form a nonempty open cone in the
rational subspace `R^⊥`, so a rational one exists; clearing denominators gives `L`. A compactness
argument on the slice `NE̅(X) ∩ {A = 1}` makes `a L - (K + B)` positive on `NE̅(X) ∖ 0` for `a`
large, and Kleiman's criterion makes it ample.

## Main results

* `MMP.Fourfold.exists_isNef_curveForm_eq_zero_and_isAmple_of_isNegativeExtremalRayOf`.

## Implementation notes

The ray and its negativity are `MMP.Fourfold.IsNegativeExtremalRayOf` for the `ℚ`-Cartier
`ℚ`-divisor `K + B`. The divisor `L` is a Weil divisor that is Cartier and nef
(`MMP.Mori.Divisor.IsNef`); its zero face is computed with the linear form
`MMP.Fourfold.QDivisor.curveForm` on `N₁(X)_ℝ`, and the ampleness of the `ℚ`-divisor
`a L - (K + B)` is `MMP.Mori.QDivisor.IsAmple`.
-/

@[expose] public section

section

namespace Proof_lem_mmp_projective_fourfold_lc_supporting_divisor

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Convex

open Set

section Join

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

private theorem isCompact_convexJoin {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  have : convexJoin ℝ s t = (fun p : E × E × ℝ => (1 - p.2.2) • p.1 + p.2.2 • p.2.1) ''
      (s ×ˢ t ×ˢ Icc (0 : ℝ) 1) := by
    ext x
    simp only [mem_convexJoin, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, hx⟩
      rw [segment_eq_image] at hx
      obtain ⟨θ, hθ, rfl⟩ := hx
      exact ⟨a, b, θ, ⟨ha, hb, hθ⟩, rfl⟩
    · rintro ⟨a, b, θ, ⟨ha, hb, hθ⟩, rfl⟩
      exact ⟨a, ha, b, hb, by rw [segment_eq_image]; exact ⟨θ, hθ, rfl⟩⟩
  rw [this]
  exact (hs.prod (ht.prod isCompact_Icc)).image (by fun_prop)

private theorem isCompact_convexHull_union {s t : Set E} (hs : IsCompact s) (hsc : Convex ℝ s)
    (ht : t.Finite) : IsCompact (convexHull ℝ (s ∪ t)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs0
  · simpa using ht.isCompact_convexHull ℝ
  rcases t.eq_empty_or_nonempty with rfl | ht0
  · simpa [hsc.convexHull_eq] using hs
  rw [convexHull_union hs0 ht0, hsc.convexHull_eq]
  exact isCompact_convexJoin hs (ht.isCompact_convexHull ℝ)

end Join

section Coordinates

variable {ι : Type*} [Fintype ι]

private theorem exists_dual_pos_of_forall_ne_smul (H : Set (ι → ℝ)) (hH : IsCompact H)
    (hHc : Convex ℝ H) (w : ι → ℝ) (hdisj : ∀ x ∈ H, ∀ t : ℝ, x ≠ t • w) :
    ∃ f : (ι → ℝ) →L[ℝ] ℝ, ∃ m : ℝ, 0 < m ∧ f w = 0 ∧ ∀ x ∈ H, m ≤ f x := by
  let P : Submodule ℝ (ι → ℝ) := ℝ ∙ w
  have hPc : IsClosed (P : Set (ι → ℝ)) := P.closed_of_finiteDimensional
  have hdis : Disjoint H (P : Set (ι → ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hxP
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hxP
    exact hdisj _ hx t rfl
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed hHc hH P.convex hPc hdis
  have hv0 : v < 0 := by simpa using hfv 0 P.zero_mem
  have hfw : f w = 0 := by
    by_contra h
    have := hfv (((v - 1) / f w) • w) (P.smul_mem _ (Submodule.mem_span_singleton_self w))
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h] at this
    linarith
  refine ⟨-f, -u, by linarith, by simp [hfw], fun x hx => ?_⟩
  have := hfu x hx
  simp only [ContinuousLinearMap.neg_apply]
  linarith

private theorem dual_apply_eq_sum [DecidableEq ι] (f : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  conv_lhs => rw [show x = ∑ i, x i • Pi.single i (1 : ℝ) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, mul_comm]

private theorem exists_rat_sum_mul_eq_zero (w : ι → ℚ) (hw : w ≠ 0) (c : ι → ℝ)
    (hc : ∑ i, c i * w i = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ι → ℚ, ∑ i, q i * w i = 0 ∧ ∀ i, |(q i : ℝ) - c i| < δ := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  have hwj : (0 : ℝ) < |(w j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  set W : ℝ := ∑ i, |(w i : ℝ)|
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => abs_nonneg _
  set η : ℝ := δ / (1 + W / |(w j : ℝ)|)
  have hη : 0 < η := div_pos hδ (by positivity)
  have hp : ∀ i, ∃ p : ℚ, |(p : ℝ) - c i| < η := fun i => by
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show c i - η < c i + η by linarith)
    exact ⟨p, abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩⟩
  choose p hp using hp
  set s : ℚ := ∑ i, p i * w i
  refine ⟨fun i => if i = j then p i - s / w j else p i, ?_, fun i => ?_⟩
  · have : ∑ i, (if i = j then p i - s / w j else p i) * w i =
        ∑ i, p i * w i - s / w j * w j := by
      have h1 : ∀ i, (if i = j then p i - s / w j else p i) * w i =
          p i * w i - (if j = i then s / w j * w j else 0) := fun i => by
        by_cases h : i = j
        · subst h; simp; ring
        · simp [h, Ne.symm h]
      simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [this, div_mul_cancel₀ _ hj]
    ring
  · by_cases hij : i = j
    · subst hij
      simp only [if_pos rfl]
      have hs : (s : ℝ) = ∑ k, ((p k : ℝ) - c k) * w k := by
        simp only [s, Rat.cast_sum, Rat.cast_mul, sub_mul, Finset.sum_sub_distrib, hc, sub_zero]
      have hsb : |(s : ℝ)| ≤ η * W := by
        rw [hs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hp k).le (abs_nonneg _)
      push_cast
      calc |(p i : ℝ) - s / w i - c i| ≤ |(p i : ℝ) - c i| + |(s : ℝ) / w i| := by
            rw [show (p i : ℝ) - s / w i - c i = ((p i : ℝ) - c i) + -(s / w i) by ring]
            exact (abs_add_le _ _).trans (by rw [abs_neg])
        _ < η + η * W / |(w i : ℝ)| := by
            rw [abs_div]
            exact add_lt_add_of_lt_of_le (hp i) (div_le_div_of_nonneg_right hsb hwj.le)
        _ = δ := by
            simp only [η]
            field_simp
    · simp only [if_neg hij]
      exact (hp i).trans_le (by
        simp only [η]
        exact div_le_self hδ.le (by linarith [div_nonneg hW hwj.le]))

end Coordinates

section Cone

variable {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

private theorem continuous_of_coordinates (Φ : V ≃L[ℝ] (ι → ℝ)) (f : V →ₗ[ℝ] ℝ) : Continuous f := by
  have : (f : V → ℝ) = (f ∘ₗ (Φ.symm : (ι → ℝ) →ₗ[ℝ] V)) ∘ Φ := by
    funext z; simp
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional _).comp Φ.continuous

private theorem isCompact_unitSlice (Φ : V ≃L[ℝ] (ι → ℝ)) {N : Set V} (hN : IsClosed N) :
    IsCompact {z | z ∈ N ∧ ‖Φ z‖ = 1} := by
  have hc : IsClosed (Φ '' N) := Φ.toHomeomorph.isClosedMap N hN
  have h : {z | z ∈ N ∧ ‖Φ z‖ = 1} = Φ.toHomeomorph ⁻¹' (Φ '' N ∩ Metric.sphere 0 1) := by
    ext z
    simp [Φ.injective.mem_set_image]
  rw [h, Φ.toHomeomorph.isCompact_preimage]
  exact (isCompact_sphere 0 1).inter_left hc

private theorem mem_unitSlice (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V) {z : V} (hz : z ∈ N) (hz0 : z ≠ 0) :
    0 < ‖Φ z‖ ∧ ‖Φ z‖⁻¹ • z ∈ {z | z ∈ N ∧ ‖Φ z‖ = 1} := by
  have hr : 0 < ‖Φ z‖ := norm_pos_iff.mpr fun h => hz0 (Φ.injective (by simp [h]))
  refine ⟨hr, N.smul_mem (inv_nonneg.mpr hr.le) hz, ?_⟩
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

private theorem pos_of_forall_unitSlice (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V) (f : V →ₗ[ℝ] ℝ)
    (h : ∀ z ∈ {z | z ∈ (N : Set V) ∧ ‖Φ z‖ = 1}, 0 < f z) {z : V} (hz : z ∈ N) (hz0 : z ≠ 0) :
    0 < f z := by
  obtain ⟨hr, hmem⟩ := mem_unitSlice Φ N hz hz0
  have := h _ hmem
  rw [map_smul, smul_eq_mul] at this
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hr)).mp this

private theorem exists_pos_mul_norm_le (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V) (hN : IsClosed (N : Set V))
    (α : V →ₗ[ℝ] ℝ) (hα : ∀ z ∈ N, z ≠ 0 → 0 < α z) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ z ∈ N, μ * ‖Φ z‖ ≤ α z := by
  set K := {z | z ∈ (N : Set V) ∧ ‖Φ z‖ = 1}
  have hK : IsCompact K := isCompact_unitSlice Φ hN
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact (Set.eq_empty_iff_forall_notMem.mp hK0 _ (mem_unitSlice Φ N hz hz0).2).elim
  obtain ⟨x₀, hx₀, hmin⟩ :=
    hK.exists_isMinOn hKne (continuous_of_coordinates Φ α).continuousOn
  have hx₀0 : x₀ ≠ 0 := fun h => by
    have := hx₀.2; rw [h, map_zero, norm_zero] at this; exact zero_ne_one this
  refine ⟨α x₀, hα x₀ hx₀.1 hx₀0, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  obtain ⟨hr, hmem⟩ := mem_unitSlice Φ N hz hz0
  have h1 : α x₀ ≤ α (‖Φ z‖⁻¹ • z) := hmin hmem
  rw [map_smul, smul_eq_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 hr.le
  rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_comm] at this

private theorem exists_pos_lt_mul (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V) (hN : IsClosed (N : Set V))
    (ℓ φ : V →ₗ[ℝ] ℝ) (hℓ : ∀ z ∈ N, 0 ≤ ℓ z) (h0 : ∀ z ∈ N, z ≠ 0 → ℓ z = 0 → φ z < 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ N, z ≠ 0 → φ z < a * ℓ z := by
  set K := {z | z ∈ (N : Set V) ∧ ‖Φ z‖ = 1}
  have hK : IsCompact K := isCompact_unitSlice Φ hN
  have hφc := continuous_of_coordinates Φ φ
  have hℓc := continuous_of_coordinates Φ ℓ
  obtain ⟨M, hM⟩ := hK.bddAbove_image hφc.continuousOn
  set K₀ := K ∩ {z | 0 ≤ φ z}
  have hK₀ : IsCompact K₀ := hK.inter_right (isClosed_le continuous_const hφc)
  have key : ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, φ z < a * ℓ z := by
    rcases K₀.eq_empty_or_nonempty with hK₀e | hK₀ne
    · refine ⟨1, one_pos, fun z hz => ?_⟩
      have : φ z < 0 := by
        by_contra h
        exact Set.eq_empty_iff_forall_notMem.mp hK₀e z ⟨hz, not_lt.mp h⟩
      linarith [hℓ z hz.1]
    obtain ⟨x₁, hx₁, hmin⟩ := hK₀.exists_isMinOn hK₀ne hℓc.continuousOn
    have hx₁0 : x₁ ≠ 0 := fun h => by
      have := hx₁.1.2; rw [h, map_zero, norm_zero] at this; exact zero_ne_one this
    have hm₁ : 0 < ℓ x₁ := by
      rcases (hℓ x₁ hx₁.1.1).lt_or_eq with h | h
      · exact h
      · exact absurd hx₁.2 (not_le.mpr (h0 x₁ hx₁.1.1 hx₁0 h.symm))
    refine ⟨(|M| + 1) / ℓ x₁, by positivity, fun z hz => ?_⟩
    by_cases hφz : 0 ≤ φ z
    · have h1 : ℓ x₁ ≤ ℓ z := hmin ⟨hz, hφz⟩
      have h2 : φ z ≤ M := hM ⟨z, hz, rfl⟩
      calc φ z ≤ M := h2
        _ < |M| + 1 := by linarith [le_abs_self M]
        _ = (|M| + 1) / ℓ x₁ * ℓ x₁ := by field_simp
        _ ≤ (|M| + 1) / ℓ x₁ * ℓ z := by gcongr
    · have := hℓ z hz.1
      have : 0 ≤ (|M| + 1) / ℓ x₁ * ℓ z := by positivity
      linarith
  obtain ⟨a, ha, hKa⟩ := key
  refine ⟨a, ha, fun z hz hz0 => ?_⟩
  have := pos_of_forall_unitSlice Φ N (a • ℓ - φ) (fun z hz => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_pos]
    exact hKa z hz) hz hz0
  simpa [sub_pos] using this

end Cone

section Supporting

variable {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A pointed cone is convex. -/
private theorem convex_pointedCone (N : PointedCone ℝ V) : Convex ℝ (N : Set V) :=
  fun _ hx _ hy a b ha hb _ => N.add_mem (N.smul_mem ha hx) (N.smul_mem hb hy)

/-- In a cone `N` in which the ray `ℝ_{≥0} v` is extremal, a finite sum of elements of `N` lying on
the ray has every summand on the ray. -/
private theorem forall_mem_ray_of_sum_mem_ray (N : PointedCone ℝ V) {v : V}
    (hext : ∀ a ∈ N, ∀ b ∈ N, (∃ s : ℝ, 0 ≤ s ∧ a + b = s • v) →
      (∃ s : ℝ, 0 ≤ s ∧ a = s • v) ∧ (∃ s : ℝ, 0 ≤ s ∧ b = s • v))
    {J : Type*} (x : J → V) (hx : ∀ j, x j ∈ N) (S : Finset J) :
    (∃ s : ℝ, 0 ≤ s ∧ ∑ j ∈ S, x j = s • v) → ∀ j ∈ S, ∃ s : ℝ, 0 ≤ s ∧ x j = s • v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    intro h j hj
    rw [Finset.sum_insert ha] at h
    obtain ⟨h1, h2⟩ := hext _ (hx a) _ (N.sum_mem fun j _ => hx j) h
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h1
    · exact ih h2 j hj

/-- A form positive on `N ∖ 0` is nonnegative on `N`. -/
private theorem nonneg_of_forall_ne_zero_pos (N : PointedCone ℝ V) (α : V →ₗ[ℝ] ℝ)
    (hα : ∀ z ∈ N, z ≠ 0 → 0 < α z) {z : V} (hz : z ∈ N) : 0 ≤ α z := by
  by_cases h : z = 0
  · simp [h]
  · exact (hα z hz h).le

/-- The classes `c + s v + ∑ τⱼ gⱼ` with `c ∈ N`, `ψ c ≥ 0` and `s, τⱼ ≥ 0` are closed under
nonnegative combinations, so they contain the cone spanned by any set of them. -/
private theorem exists_decomposition_of_mem_span (N : PointedCone ℝ V) (ψ : V →ₗ[ℝ] ℝ) (v : V)
    {J : Type*} [Fintype J] (g : J → V) {S : Set V}
    (hS : ∀ x ∈ S, ∃ c ∈ N, 0 ≤ ψ c ∧ ∃ s : ℝ, 0 ≤ s ∧ ∃ τ : J → ℝ, (∀ j, 0 ≤ τ j) ∧
      x = c + s • v + ∑ j, τ j • g j)
    {y : V} (hy : y ∈ Submodule.span NNReal S) :
    ∃ c ∈ N, 0 ≤ ψ c ∧ ∃ s : ℝ, 0 ≤ s ∧ ∃ τ : J → ℝ, (∀ j, 0 ≤ τ j) ∧
      y = c + s • v + ∑ j, τ j • g j := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, N.zero_mem, by simp, 0, le_rfl, 0, fun _ => le_rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, hc₁, hψ₁, s₁, hs₁, τ₁, hτ₁, rfl⟩ := hx
    obtain ⟨c₂, hc₂, hψ₂, s₂, hs₂, τ₂, hτ₂, rfl⟩ := hy
    refine ⟨c₁ + c₂, N.add_mem hc₁ hc₂, by rw [map_add]; linarith, s₁ + s₂, by linarith,
      τ₁ + τ₂, fun j => by simp only [Pi.add_apply]; linarith [hτ₁ j, hτ₂ j], ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul r x _ hx =>
    obtain ⟨c, hc, hψc, s, hs, τ, hτ, rfl⟩ := hx
    rw [NNReal.smul_def]
    refine ⟨(r : ℝ) • c, N.smul_mem r.2 hc, by rw [map_smul, smul_eq_mul]; exact mul_nonneg r.2 hψc,
      r * s, mul_nonneg r.2 hs, fun j => r * τ j, fun j => mul_nonneg r.2 (hτ j), ?_⟩
    simp only [smul_add, Finset.smul_sum, smul_smul]

/-- A form `ℓ` vanishing on `v`, bounded below by `m α` on `N ∩ {ψ ≥ 0}` and positive on each
`gⱼ` is nonnegative on every `c + s v + ∑ τⱼ gⱼ` (with `c ∈ N`, `ψ c ≥ 0`, `s, τⱼ ≥ 0`), and
vanishes there only when the class is `s v`. -/
private theorem nonneg_and_eq_smul_of_eq_zero (N : PointedCone ℝ V) (α ψ ℓ : V →ₗ[ℝ] ℝ)
    (hα : ∀ z ∈ N, z ≠ 0 → 0 < α z) {v : V} (hℓv : ℓ v = 0) {J : Type*} [Fintype J]
    (g : J → V) {m : ℝ} (hm : 0 < m) (hℓc : ∀ c ∈ N, 0 ≤ ψ c → m * α c ≤ ℓ c)
    (hℓg : ∀ j, 0 < ℓ (g j)) {c : V} (hc : c ∈ N) (hψc : 0 ≤ ψ c) (s : ℝ) {τ : J → ℝ}
    (hτ : ∀ j, 0 ≤ τ j) :
    0 ≤ ℓ (c + s • v + ∑ j, τ j • g j) ∧
      (ℓ (c + s • v + ∑ j, τ j • g j) = 0 → c + s • v + ∑ j, τ j • g j = s • v) := by
  have hterm : ∀ j, 0 ≤ τ j * ℓ (g j) := fun j => mul_nonneg (hτ j) (hℓg j).le
  have hc' := hℓc c hc hψc
  have hℓc0 : 0 ≤ ℓ c := (mul_nonneg hm.le (nonneg_of_forall_ne_zero_pos N α hα hc)).trans hc'
  have hsum0 : 0 ≤ ∑ j, τ j * ℓ (g j) := Finset.sum_nonneg fun j _ => hterm j
  have hval : ℓ (c + s • v + ∑ j, τ j • g j) = ℓ c + ∑ j, τ j * ℓ (g j) := by
    simp [map_sum, hℓv]
  rw [hval]
  refine ⟨by linarith, fun h0 => ?_⟩
  have hc0 : c = 0 := by
    by_contra hne
    linarith [mul_pos hm (hα c hc hne)]
  have hτ0 : ∀ j, τ j = 0 := fun j =>
    (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp (by linarith) j
      (Finset.mem_univ j))).resolve_right (hℓg j).ne'
  simp [hc0, hτ0]

private theorem exists_rat_supporting (Φ : V ≃L[ℝ] (ι → ℝ)) (N : PointedCone ℝ V)
    (hN : IsClosed (N : Set V)) (α ψ : V →ₗ[ℝ] ℝ)
    (hα : ∀ z ∈ N, z ≠ 0 → 0 < α z) {v : V} (hvN : v ∈ N) (hψv : ψ v < 0)
    (hext : ∀ a ∈ N, ∀ b ∈ N, (∃ s : ℝ, 0 ≤ s ∧ a + b = s • v) →
      (∃ s : ℝ, 0 ≤ s ∧ a = s • v) ∧ (∃ s : ℝ, 0 ≤ s ∧ b = s • v))
    {J : Type*} [Fintype J] (g : J → V) (hgN : ∀ j, g j ∈ N) (hgv : ∀ j, ∀ s : ℝ, g j ≠ s • v)
    (w : ι → ℚ) (hw : ∀ i, Φ v i = w i) :
    ∃ q : ι → ℚ, ∑ i, (q i : ℝ) * Φ v i = 0 ∧ ∃ m : ℝ, 0 < m ∧
      (∀ c ∈ N, 0 ≤ ψ c → m * α c ≤ ∑ i, (q i : ℝ) * Φ c i) ∧
        ∀ j, 0 < ∑ i, (q i : ℝ) * Φ (g j) i := by
  classical
  have hαc := continuous_of_coordinates Φ α
  have hψc := continuous_of_coordinates Φ ψ
  have hg0 : ∀ j, g j ≠ 0 := fun j h => hgv j 0 (by rw [h, zero_smul])
  have hαg : ∀ j, 0 < α (g j) := fun j => hα _ (hgN j) (hg0 j)
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_mul_norm_le Φ N hN α hα
  set S₁ : Set V := {c | c ∈ N ∧ 0 ≤ ψ c ∧ α c = 1}
  set S₂ : Set V := Set.range fun j => (α (g j))⁻¹ • g j
  set T : Set V := {x | α x = 1 ∧ ∃ c ∈ N, 0 ≤ ψ c ∧ ∃ t : J → ℝ, (∀ j, 0 ≤ t j) ∧
    x = c + ∑ j, t j • g j}
  -- `T` is convex and contains `S₁ ∪ S₂`
  have hTconv : Convex ℝ T := by
    rintro x ⟨hx1, c₁, hc₁, hψ₁, t₁, ht₁, rfl⟩ y ⟨hy1, c₂, hc₂, hψ₂, t₂, ht₂, rfl⟩ a b ha hb hab
    refine ⟨by rw [map_add, map_smul, map_smul, hx1, hy1]; simp [hab], a • c₁ + b • c₂,
      N.add_mem (N.smul_mem ha hc₁) (N.smul_mem hb hc₂), ?_, fun j => a * t₁ j + b * t₂ j,
      fun j => by have := ht₁ j; have := ht₂ j; positivity, ?_⟩
    · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; positivity
    · simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
      abel
  have hS₁T : S₁ ⊆ T := fun c ⟨hc, hψ, h1⟩ => ⟨h1, c, hc, hψ, 0, fun _ => le_rfl, by simp⟩
  have hS₂T : S₂ ⊆ T := by
    rintro _ ⟨j, rfl⟩
    refine ⟨by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (hαg j).ne'], 0, N.zero_mem,
      by simp, fun j' => if j' = j then (α (g j))⁻¹ else 0,
      fun j' => by by_cases h : j' = j <;> simp [h, (hαg j).le], ?_⟩
    simp [ite_smul]
  -- no point of `T` lies on the line `ℝ v`
  have hTv : ∀ x ∈ T, ∀ s : ℝ, x ≠ s • v := by
    rintro x ⟨hx1, c, hc, hψc', t, ht, rfl⟩ s hs
    have hxN : c + ∑ j, t j • g j ∈ N :=
      N.add_mem hc (N.sum_mem fun j _ => N.smul_mem (ht j) (hgN j))
    rcases lt_or_ge s 0 with hs0 | hs0
    · have hneg : -(c + ∑ j, t j • g j) ∈ N := by
        rw [hs, ← neg_smul]; exact N.smul_mem (by linarith) hvN
      have := nonneg_of_forall_ne_zero_pos N α hα hneg
      rw [map_neg, hx1] at this
      linarith
    obtain ⟨⟨s₁, hs₁, hc₁⟩, hsum⟩ :=
      hext c hc _ (N.sum_mem fun j _ => N.smul_mem (ht j) (hgN j)) ⟨s, hs0, hs⟩
    have hc0 : c = 0 := by
      have : ψ c = s₁ * ψ v := by rw [hc₁, map_smul, smul_eq_mul]
      have : s₁ = 0 := by nlinarith
      rw [hc₁, this, zero_smul]
    have hterm := forall_mem_ray_of_sum_mem_ray N hext (fun j => t j • g j)
      (fun j => N.smul_mem (ht j) (hgN j)) Finset.univ hsum
    have ht0 : ∀ j, t j = 0 := by
      intro j
      obtain ⟨s', -, hs'⟩ := hterm j (Finset.mem_univ j)
      by_contra htj
      exact hgv j (s' / t j) (by
        rw [div_eq_inv_mul, ← smul_smul, ← hs', smul_smul, inv_mul_cancel₀ htj, one_smul])
    have : c + ∑ j, t j • g j = 0 := by simp [hc0, ht0]
    rw [this, map_zero] at hx1
    exact zero_ne_one hx1
  -- the compact convex set to separate
  have hS₁closed : IsClosed S₁ :=
    hN.inter ((isClosed_le continuous_const hψc).inter (isClosed_eq hαc continuous_const))
  have hS₁img : IsCompact (Φ '' S₁) := by
    refine Metric.isCompact_of_isClosed_isBounded (Φ.toHomeomorph.isClosedMap _ hS₁closed) ?_
    refine (Metric.isBounded_closedBall (x := 0) (r := 1 / μ)).subset ?_
    rintro _ ⟨c, ⟨hc, -, h1⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hμ, mul_comm]
    exact h1 ▸ hμle c hc
  have hS₁conv : Convex ℝ S₁ :=
    (convex_pointedCone N).inter ((convex_halfSpace_ge (f := ψ) ψ.isLinear 0).inter
      (convex_hyperplane (f := α) α.isLinear 1))
  set H := Φ '' convexHull ℝ (S₁ ∪ S₂)
  have hH : H = convexHull ℝ (Φ '' S₁ ∪ Φ '' S₂) := by
    rw [← Set.image_union]
    exact (Φ.toLinearMap.image_convexHull _)
  have hHc : IsCompact H := by
    rw [hH]
    exact isCompact_convexHull_union hS₁img (hS₁conv.linear_image Φ.toLinearMap)
      ((Set.finite_range _).image _)
  have hHconv : Convex ℝ H := hH ▸ convex_convexHull ℝ _
  obtain ⟨f, m, hm, hfv, hfm⟩ := exists_dual_pos_of_forall_ne_smul H hHc hHconv (Φ v) (by
    rintro _ ⟨x, hx, rfl⟩ s hs
    refine hTv x (convexHull_min (Set.union_subset hS₁T hS₂T) hTconv hx) s
      (Φ.injective ?_)
    rw [hs, map_smul])
  have hfS : ∀ x ∈ S₁ ∪ S₂, m ≤ f (Φ x) := fun x hx =>
    hfm _ ⟨x, subset_convexHull ℝ _ hx, rfl⟩
  -- the real coefficients of the supporting form
  set c₀ : ι → ℝ := fun i => f (Pi.single i 1)
  have hℓ₀ : ∀ z, f (Φ z) = ∑ i, c₀ i * Φ z i := fun z => dual_apply_eq_sum f (Φ z)
  have hc₀ : ∑ i, c₀ i * w i = 0 := by
    rw [← hfv, hℓ₀]; simp [hw]
  have hw0 : w ≠ 0 := by
    rintro rfl
    have hv0 : v ≠ 0 := fun h => by rw [h, map_zero] at hψv; exact lt_irrefl _ hψv
    exact hv0 (Φ.injective (funext fun i => by simp [hw]))
  set δ : ℝ := m * μ / (2 * (Fintype.card ι + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨q, hq, hqc⟩ := exists_rat_sum_mul_eq_zero w hw0 c₀ hc₀ hδ
  have hbound : ∀ z ∈ N, |∑ i, (q i : ℝ) * Φ z i - f (Φ z)| ≤ m / 2 * α z := by
    intro z hz
    rw [hℓ₀, ← Finset.sum_sub_distrib]
    calc |∑ i, ((q i : ℝ) * Φ z i - c₀ i * Φ z i)|
        ≤ ∑ i, |(q i : ℝ) * Φ z i - c₀ i * Φ z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, δ * ‖Φ z‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sub_mul, abs_mul]
        exact mul_le_mul (hqc i).le (by simpa using norm_le_pi_norm (Φ z) i) (abs_nonneg _)
          hδ.le
      _ = Fintype.card ι * δ * ‖Φ z‖ := by simp [mul_assoc]
      _ ≤ m / 2 * (μ * ‖Φ z‖) := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simp only [δ]
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
        nlinarith [mul_pos hm hμ]
      _ ≤ m / 2 * α z := mul_le_mul_of_nonneg_left (hμle z hz) (by positivity)
  have hlow : ∀ z ∈ N, 0 < α z → m ≤ f (Φ ((α z)⁻¹ • z)) → m / 2 * α z ≤
      ∑ i, (q i : ℝ) * Φ z i := by
    intro z hz hαz hfz
    rw [map_smul, map_smul, smul_eq_mul] at hfz
    have h1 : m * α z ≤ f (Φ z) := by
      have := mul_le_mul_of_nonneg_left hfz hαz.le
      rwa [← mul_assoc, mul_inv_cancel₀ hαz.ne', one_mul, mul_comm] at this
    have h2 := (abs_le.mp (hbound z hz)).1
    linarith
  refine ⟨q, by simpa [hw] using (show ∑ i, ((q i * w i : ℚ) : ℝ) = 0 by
    rw [← Rat.cast_sum, hq, Rat.cast_zero]), m / 2, by positivity, fun c hc hψc' => ?_,
    fun j => ?_⟩
  · by_cases hc0 : c = 0
    · simp [hc0]
    have hαc' := hα c hc hc0
    refine hlow c hc hαc' (hfS _ (Or.inl ⟨N.smul_mem (inv_nonneg.mpr hαc'.le) hc, ?_, ?_⟩))
    · rw [map_smul, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hαc'.le) hψc'
    · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hαc'.ne']
  · have := hlow (g j) (hgN j) (hαg j) (hfS _ (Or.inr ⟨j, rfl⟩))
    have : 0 < m / 2 * α (g j) := by have := hαg j; positivity
    linarith

end Supporting

end Convex

/-! ### Extremal rays under a linear isomorphism -/

section RayTransport

variable {P Q : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup Q] [Module ℝ Q]

private theorem isExtremalRay_image (f : P ≃ₗ[ℝ] Q) {A R : Set P}
    (h : IsExtremalRay ℝ A R) : IsExtremalRay ℝ (f '' A) (f '' R) := by
  obtain ⟨⟨hRA, ⟨hR0, hRs⟩, hRadd, hRext⟩, v, hv0, hRv⟩ := h
  refine ⟨⟨Set.image_mono hRA, ⟨⟨0, hR0, map_zero f⟩, ?_⟩, ?_, ?_⟩, f v,
    fun h => hv0 (f.injective (by rw [h, map_zero])), ?_⟩
  · rintro _ ⟨r, hr, rfl⟩ c hc
    exact ⟨c • r, hRs r hr c hc, map_smul _ _ _⟩
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    exact ⟨r + r', hRadd r hr r' hr', map_add _ _ _⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ⟨r, hr, hrab⟩
    have : a + b = r := f.injective (by rw [hrab, map_add])
    obtain ⟨haR, hbR⟩ := hRext a ha b hb (this ▸ hr)
    exact ⟨⟨a, haR, rfl⟩, ⟨b, hbR, rfl⟩⟩
  · rw [hRv]
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, (map_smul _ _ _).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, map_smul _ _ _⟩

end RayTransport

/-! ### Curve forms of Cartier divisors -/

section CurveForm

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- Two linear forms on `N₁(X)_ℝ` agreeing on the classes of proper curves are equal. -/
private theorem linearMap_ext_numericalClass_cycle
    {φ ψ : NumericalCurveClasses sX →ₗ[ℝ] ℝ}
    (h : ∀ C : ProperCurve sX,
      φ (OneCycle.numericalClass sX (C.cycle ℝ)) = ψ (OneCycle.numericalClass sX (C.cycle ℝ))) :
    φ = ψ :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun C => LinearMap.ext_ring (h C))

/-- The curve form is additive in the divisor. -/
private theorem curveForm_add (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    QDivisor.curveForm sX (D + D') hDD' =
      QDivisor.curveForm sX D hD + QDivisor.curveForm sX D' hD' := by
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' hD hD' hDD']
  push_cast; rfl

/-- The curve form is `ℚ`-homogeneous in the divisor. -/
private theorem curveForm_smul (q : ℚ) (D : QDivisor X) (hD : D.IsQCartier)
    (hqD : (q • D).IsQCartier) :
    QDivisor.curveForm sX (q • D) hqD = (q : ℝ) • QDivisor.curveForm sX D hD := by
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.smul_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_smul k sX C.ι C.dim_le q D hD hqD]
  push_cast; rfl

/-- The curve form depends only on the divisor. -/
private theorem curveForm_congr {D D' : QDivisor X} (e : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) : QDivisor.curveForm sX D hD = QDivisor.curveForm sX D' hD' := by
  subst e; rfl

/-- The curve form of a Cartier divisor on the class of a proper curve is its degree there. -/
private theorem curveForm_toQDivisor_numericalClass (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier) (C : ProperCurve sX) :
    QDivisor.curveForm sX (Divisor.toQDivisor W) h (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (W.degreeOn k sX C.ι C.dim_le hW : ℝ) := by
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le W hW h]
  push_cast; rfl

/-- The curve form of a Cartier divisor `W` is the intersection form of any Cartier divisor `E`
with `𝒪_X(W) ≅ 𝒪_X(E)`. -/
private theorem curveForm_toQDivisor_eq_intersectionNumber (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier) (E : X.CartierDivisor)
    (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) :
    QDivisor.curveForm sX (Divisor.toQDivisor W) h =
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [curveForm_toQDivisor_numericalClass sX W hW h C,
    NumericalCurveClasses.intersectionNumber_ofCartier, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_cycle]
  exact_mod_cast degreeOn_eq_of_iso k sX C.ι C.dim_le e

/-- The curve form of a Cartier divisor `W` is the degree form of `𝒪_X(W)`. -/
private theorem curveForm_toQDivisor_eq_degree (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier) :
    haveI := hW.isInvertibleModule_divisorialSheaf
    QDivisor.curveForm sX (Divisor.toQDivisor W) h =
      NumericalCurveClasses.degree sX W.divisorialSheaf := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [curveForm_toQDivisor_numericalClass sX W hW h C, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_cycle]
  rfl

end CurveForm

/-! ### Weil divisors of Cartier divisors -/

section WeilOfCartier

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- On an integral Noetherian scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier (A : X.CartierDivisor) :
    ∃ w : Divisor X, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian X := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (X.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (X.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- Every Cartier divisor has a Cartier Weil divisor with the same sheaf. -/
private theorem exists_divisor_iso_sheaf (A : X.CartierDivisor) :
    ∃ w : Divisor X, w.IsCartier ∧
      Nonempty (w.divisorialSheaf ≅ MMP.CartierDivisor.sheaf A) := by
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier A
  obtain ⟨e⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  exact ⟨w, hw.isCartier, ⟨e.symm⟩⟩

end WeilOfCartier

/-! ### Kleiman's criterion and nefness for Weil divisors -/

section Kleiman

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX]

/-- An ample Cartier divisor is positive on `NE̅(X) ∖ 0`. -/
private theorem curveForm_pos_of_isAmple (W : Divisor X) (hW : W.IsCartier) (hA : W.IsAmple hW)
    (h : (Divisor.toQDivisor W).IsQCartier) :
    ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < QDivisor.curveForm sX (Divisor.toQDivisor W) h z := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf W.divisorialSheaf
  rw [curveForm_toQDivisor_eq_intersectionNumber sX W hW h E e]
  exact (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX E).mp
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp hA)

/-- **Kleiman's criterion** for a Cartier Weil divisor. -/
private theorem isAmple_of_curveForm_pos (W : Divisor X) (hW : W.IsCartier)
    (h : (Divisor.toQDivisor W).IsQCartier)
    (hpos : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < QDivisor.curveForm sX (Divisor.toQDivisor W) h z) :
    W.IsAmple hW := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf W.divisorialSheaf
  rw [curveForm_toQDivisor_eq_intersectionNumber sX W hW h E e] at hpos
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    ((isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX E).mpr hpos)

omit [AlgebraicGeometry.IsProjectiveVariety ℂ sX] in
/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf (h : AlgebraicGeometry.IsProjectiveVariety ℂ sX) :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced {Y W : Scheme.{0}} (ι : Y ⟶ W)
    [IsClosedImmersion ι] [IsReduced Y] (T : TopologicalSpace.Closeds W)
    (hT : (T : Set W) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hn
      rw [RingHom.mem_ker]
      exact IsReduced.eq_zero _ ⟨n, hn⟩
    · exact Ideal.le_radical
  have hs : (ι.ker.support : Set W) = Set.range ι := by
    rw [Scheme.Hom.support_ker, (ι.isClosedEmbedding).isClosed_range.closure_eq]
  have : ι.ker.support = T := by
    apply TopologicalSpace.Closeds.ext
    rw [hs, hT]
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A closed immersion from an integral scheme is, up to isomorphism, the closed immersion of the
closure of the image of the generic point. -/
private theorem exists_iso_curveSubschemeAt {Y W : Scheme.{0}} [IsIntegral Y] (ι : Y ⟶ W)
    [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : Set.range ι = closure {ι (genericPoint Y)} := by
    rw [← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec Y).def]
    simp
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced ι (TopologicalSpace.Closeds.closure
      {ι (genericPoint Y)}) hrange.symm]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
  have hf : IsIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  exact ⟨asIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- A Cartier divisor whose curve form is nonnegative on the classes of proper curves is nef. -/
private theorem isNef_of_forall_properCurve (L : Divisor X) (hL : L.IsCartier)
    (h : (Divisor.toQDivisor L).IsQCartier)
    (hnn : ∀ C : ProperCurve sX, 0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor L) h
      (OneCycle.numericalClass sX (C.cycle ℝ))) : L.IsNef ℂ sX := by
  refine ⟨hL, fun C c _ _ _ hC => ?_⟩
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt c
  have hι : curveSubschemeAtι (c (genericPoint C)) = e.inv ≫ c := (Iso.eq_inv_comp e).mpr he
  have hdim : topologicalKrullDim (curveSubschemeAt (c (genericPoint C))) = 1 := by
    rw [← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.inv.homeomorph.isHomeomorph)
  have hprop : IsProper (curveSubschemeAtι (c (genericPoint C)) ≫ sX) := by
    rw [hι, Category.assoc]; infer_instance
  let C₀ : ProperCurve sX := ⟨c (genericPoint C), ⟨hdim, hprop⟩⟩
  have h0 := hnn C₀
  rw [curveForm_toQDivisor_numericalClass sX L hL h C₀] at h0
  have : L.degreeOn ℂ sX c hC.le hL = L.degreeOn ℂ sX C₀.ι C₀.dim_le hL := by
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ sX c C₀.ι hC.le C₀.dim_le e he _
  rw [this]
  exact_mod_cast h0

end Kleiman

/-! ### Sums of Cartier divisors -/

section Sums

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

private theorem isCartier_sum {ι : Type*} (s : Finset ι) (n : ι → ℤ) (W : ι → Divisor X)
    (hW : ∀ i, (W i).IsCartier) : (∑ i ∈ s, n i • W i).IsCartier := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Divisor.isCartier_zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact ((hW a).zsmul _).add ih

private theorem toQDivisor_zsmul (n : ℤ) (W : Divisor X) :
    Divisor.toQDivisor (n • W) = (n : ℚ) • Divisor.toQDivisor W := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

/-- The curve form of an integral combination of Cartier divisors. -/
private theorem curveForm_toQDivisor_sum {ι : Type*} (s : Finset ι) (n : ι → ℤ)
    (W : ι → Divisor X) (hW : ∀ i, (W i).IsCartier)
    (h : (Divisor.toQDivisor (∑ i ∈ s, n i • W i)).IsQCartier) :
    QDivisor.curveForm sX (Divisor.toQDivisor (∑ i ∈ s, n i • W i)) h =
      ∑ i ∈ s, (n i : ℝ) • QDivisor.curveForm sX (Divisor.toQDivisor (W i))
        (QDivisor.isQCartier_toQDivisor (hW i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine linearMap_ext_numericalClass_cycle sX fun C => ?_
    rw [curveForm_toQDivisor_numericalClass sX 0 Divisor.isCartier_zero h C,
      Divisor.degreeOn_zero' k sX C.ι C.dim_le]
    simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha] at h ⊢
    have h1 := QDivisor.isQCartier_toQDivisor ((hW a).zsmul (n a))
    have h2 := QDivisor.isQCartier_toQDivisor (isCartier_sum s n W hW)
    have h12 : (Divisor.toQDivisor (n a • W a) + Divisor.toQDivisor (∑ i ∈ s, n i • W i)).IsQCartier :=
      by rw [← map_add]; exact h
    have h1' : ((n a : ℚ) • Divisor.toQDivisor (W a)).IsQCartier := toQDivisor_zsmul (n a) (W a) ▸ h1
    rw [curveForm_congr sX (map_add _ _ _) h h12, curveForm_add sX _ _ h1 h2 h12, ih h2,
      curveForm_congr sX (toQDivisor_zsmul (n a) (W a)) h1 h1',
      curveForm_smul sX _ _ (QDivisor.isQCartier_toQDivisor (hW a)) h1']
    simp

end Sums

/-! ### Curves over the base point -/

section Absolute

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- Over the base point, the natural map `N₁(X / Spec ℂ) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_structure sX C
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- On `N₁(X/S)` the curve form is the absolute one composed with the natural map. -/
private theorem relativeCurveForm_eq_comp {S : Scheme.{0}} (f : X ⟶ S) (D : QDivisor X)
    (h : D.IsQCartier) :
    QDivisor.relativeCurveForm sX f D h =
      QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- On `N₁(X/S)` the degree form is the absolute one composed with the natural map. -/
private theorem relativeDegree_eq_comp {S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    RelativeNumericalCurveClasses.degree sX f L =
      NumericalCurveClasses.degree sX L ∘ₗ relativeToAbsolute sX f :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

end Absolute

/-! ### The cone theorem in `N₁(X)` -/

section ConeTheorem

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The lc cone theorem for a projective complex fourfold, read in the absolute space `N₁(X)`
(the relative cone theorem over the base point `Spec ℂ`): every `(K + B)`-negative extremal ray is
spanned by the class of a curve; for an ample Cartier `A` and `ε > 0` only finitely many of them
are `(K + B + εA)`-negative; and `NE̅(X)` is the sum of its part where `K + B ≥ 0` and the convex
cone spanned by the negative extremal rays. -/
private theorem closedConeOfCurves_structure (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hD : (Divisor.toQDivisor K + B).IsQCartier) :
    (∀ R', IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R' →
      ∃ C : ProperCurve sX,
        R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w}) ∧
    (∀ (A : Divisor X) (hA : A.IsCartier), A.IsAmple hA → ∀ ε : ℝ, 0 < ε →
      haveI := hA.isInvertibleModule_divisorialSheaf
      {R' | IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R' ∧ ∀ u ∈ R', u ≠ 0 →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B) hD u +
          ε * NumericalCurveClasses.degree sX A.divisorialSheaf u < 0}.Finite) ∧
    (∀ z ∈ closedConeOfCurves sX, ∃ a ∈ closedConeOfCurves sX,
      0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor K + B) hD a ∧
      ∃ b ∈ PointedCone.hull ℝ
        (⋃₀ {R' | IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R'}), z = a + b) := by
  haveI hXp : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  set D := Divisor.toQDivisor K + B with hDdef
  set φ := QDivisor.curveForm sX D hD with hφdef
  set N := closedConeOfCurves sX with hNdef
  have hS : MMP.Mori.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨(MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) := hS
  obtain ⟨hD₀, hray, -, hdec, hfin, -, -⟩ :=
    exists_relativeClosedConeOfCurves_eq_add_hull_of_isLogCanonicalPair hX hS sX
      (Category.comp_id sX) hK.1 hK hB
  have hbij := relativeToAbsolute_bijective sX
  set e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) hbij with hedef
  have hNimg : e '' (relativeClosedConeOfCurves sX sX : Set _) = (N : Set _) := by
    have := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of ℂ))) sX
      (Category.comp_id sX)
    rw [hbij.2.range_eq, Set.inter_univ] at this
    exact this
  have hNpre : e.symm '' (N : Set _) = (relativeClosedConeOfCurves sX sX : Set _) := by
    rw [← hNimg, ← Set.image_comp]; simp
  have hform : ∀ u, QDivisor.relativeCurveForm sX sX D hD u = φ (e u) := fun u => by
    rw [relativeCurveForm_eq_comp]; rfl
  have hneg_img : ∀ R₀, IsNegativeRelativeExtremalRayOf sX sX D R₀ →
      IsNegativeExtremalRayOf sX D (e '' R₀) := by
    rintro R₀ ⟨h1, h2, h3⟩
    refine ⟨hD, hNimg ▸ isExtremalRay_image e h2, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ hu0
    rw [← hform]
    exact h3 u hu (fun h => hu0 (by rw [h, map_zero]))
  have hneg_pre : ∀ R', IsNegativeExtremalRayOf sX D R' →
      IsNegativeRelativeExtremalRayOf sX sX D (e ⁻¹' R') := by
    rintro R' ⟨h1, h2, h3⟩
    refine ⟨hD, ?_, fun u hu hu0 => ?_⟩
    · rw [← e.image_symm_eq_preimage, ← hNpre]; exact isExtremalRay_image e.symm h2
    · rw [hform]
      exact h3 (e u) hu (fun h => hu0 (e.injective (by rw [h, map_zero])))
  refine ⟨fun R' hR' => ?_, fun A hA hAamp ε hε => ?_, fun z hz => ?_⟩
  · obtain ⟨C, hC, -, hRC, -, -⟩ := hray _ (hneg_pre R' hR')
    have hev : e (C.relativeClass sX hC) = OneCycle.numericalClass sX (C.cycle ℝ) :=
      isNaturalRelativeMap_relativeToAbsolute sX sX _
    refine ⟨C, ?_⟩
    rw [← Set.image_preimage_eq R' e.surjective, hRC]
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨c, hc, by rw [map_smul, hev]⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c • C.relativeClass sX hC, ⟨c, hc, rfl⟩, by rw [map_smul, hev]⟩
  · haveI := hA.isInvertibleModule_divisorialSheaf
    refine ((hfin A hA hAamp ε hε).image fun R₀ => e '' R₀).subset ?_
    rintro R' ⟨hR'neg, hR'ψ⟩
    refine ⟨e ⁻¹' R', ⟨hneg_pre R' hR'neg, fun u hu hu0 => ?_⟩,
      Set.image_preimage_eq R' e.surjective⟩
    have := hR'ψ (e u) hu (fun h => hu0 (e.injective (by rw [h, map_zero])))
    rw [relativeCurveForm_eq_comp, relativeDegree_eq_comp]
    exact this
  · obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ ∈ (relativeClosedConeOfCurves sX sX : Set _), e w₀ = z := by
      have : z ∈ (N : Set (NumericalCurveClasses sX)) := hz
      rw [← hNimg] at this
      exact this
    rw [hdec] at hw₀
    obtain ⟨a, ⟨ha, haφ⟩, b, hb, rfl⟩ := Set.mem_add.mp hw₀
    have hhull : ∀ y ∈ Submodule.span NNReal (⋃₀ {R₀ : Set (RelativeNumericalCurveClasses sX sX) |
        IsNegativeRelativeExtremalRayOf sX sX D R₀}),
        e y ∈ PointedCone.hull ℝ (⋃₀ {R' | IsNegativeExtremalRayOf sX D R'}) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨R₀, hR₀, hxR₀⟩ := hx
        exact Submodule.subset_span ⟨e '' R₀, hneg_img R₀ hR₀, x, hxR₀, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [NNReal.smul_def, map_smul, ← NNReal.smul_def]
        exact Submodule.smul_mem _ r hx
    have haN : e a ∈ N := by
      have : e a ∈ e '' (relativeClosedConeOfCurves sX sX : Set _) := ⟨a, ha, rfl⟩
      rw [hNimg] at this
      exact this
    refine ⟨e a, haN, ?_, e b, hhull b hb, map_add _ _ _⟩
    have := hform a
    rw [← this]
    exact haφ

end ConeTheorem

/-! ### Cartier coordinates on `N₁(X)` -/

section Coordinates

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX]

/-- `N₁(X)` has linear coordinates given by intersection with finitely many Cartier divisors. -/
private theorem exists_cartier_coordinates :
    ∃ (t : Set X.CartierDivisor) (_ : Fintype t) (Φ : NumericalCurveClasses sX ≃L[ℝ] (t → ℝ)),
      ∀ z (i : t), Φ z i = NumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ (i : X.CartierDivisor)) z := by
  obtain ⟨hfd, -, hextc, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hextc ∅ (linearIndepOn_empty _ _)
  rw [Set.image_eq_range] at htspan
  obtain ⟨⟨Φ, hΦ⟩, -⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht htspan
  haveI := hfd
  exact ⟨t, @Fintype.ofFinite _ ht.finite, Φ, fun z i => by
    simpa using congrArg (fun f : NumericalCurveClasses sX →ₗ[ℝ] t → ℝ => f z i) hΦ⟩

end Coordinates

/-! ### Ampleness from a supporting divisor -/

section Ampleness

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX]

/-- If a Cartier divisor `L` is nonnegative on `NE̅(X)` and a `ℚ`-Cartier `D` is negative on every
nonzero class of `NE̅(X)` on which `L` vanishes, then `a L - D` is ample for some rational
`a > 0`. -/
private theorem exists_isAmple_smul_sub (L : Divisor X) (hLc : L.IsCartier) (D : QDivisor X)
    (hD : D.IsQCartier)
    (hnn : ∀ z ∈ closedConeOfCurves sX,
      0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor L) (QDivisor.isQCartier_toQDivisor hLc) z)
    (hneg : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      QDivisor.curveForm sX (Divisor.toQDivisor L) (QDivisor.isQCartier_toQDivisor hLc) z = 0 →
        QDivisor.curveForm sX D hD z < 0) :
    ∃ a : ℚ, 0 < a ∧ (a • Divisor.toQDivisor L - D).IsAmple := by
  have hLQ := QDivisor.isQCartier_toQDivisor hLc
  set φ := QDivisor.curveForm sX D hD with hφdef
  set FL := QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ with hFLdef
  set N := closedConeOfCurves sX with hNdef
  have hNclosed : IsClosed (N : Set (NumericalCurveClasses sX)) := by
    rw [hNdef, coe_closedConeOfCurves]; exact isClosed_closure
  obtain ⟨t, _, Φ, -⟩ := exists_cartier_coordinates sX
  obtain ⟨a₀, ha₀, ha₀lt⟩ := exists_pos_lt_mul Φ N hNclosed FL φ hnn hneg
  set a : ℕ := ⌈a₀⌉₊ + 1 with hadef
  have ha : (0 : ℚ) < a := by positivity
  have haa : a₀ ≤ (a : ℝ) := by
    simp only [hadef]; push_cast; linarith [Nat.le_ceil a₀]
  obtain ⟨m', hm', D', hD'eq, hD'c⟩ : ∃ m' : ℕ, 0 < m' ∧ ∃ D' : Divisor X,
      Divisor.toQDivisor D' = ((m' : ℤ) • D) ∧ D'.IsCartier := by
    obtain ⟨m', hm', D', h1, h2⟩ := hD.exists_pos
    exact ⟨m', hm', D', h1, h2⟩
  set W' : Divisor X := ((m' * a : ℕ) : ℤ) • L - D' with hW'def
  have hW'c : W'.IsCartier := (hLc.zsmul _).sub hD'c
  have hW'eq : Divisor.toQDivisor W' = (m' : ℚ) • ((a : ℚ) • Divisor.toQDivisor L - D) := by
    rw [hW'def, map_sub, map_zsmul, hD'eq, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    module
  have hW'Q := QDivisor.isQCartier_toQDivisor hW'c
  have hFW : ∀ z, QDivisor.curveForm sX (Divisor.toQDivisor W') hW'Q z =
      m' * (a * FL z) - m' * φ z := by
    have e1 : Divisor.toQDivisor W' = Divisor.toQDivisor (((m' * a : ℕ) : ℤ) • L) +
        Divisor.toQDivisor (-D') := by
      rw [hW'def, sub_eq_add_neg, map_add]
    have hq1 := QDivisor.isQCartier_toQDivisor (hLc.zsmul (((m' * a : ℕ) : ℤ)))
    have hq2 := QDivisor.isQCartier_toQDivisor hD'c.neg
    have hq12 : (Divisor.toQDivisor (((m' * a : ℕ) : ℤ) • L) +
        Divisor.toQDivisor (-D')).IsQCartier := e1 ▸ hW'Q
    have e2 : Divisor.toQDivisor (-D') = (((-(m' : ℤ)) : ℤ) : ℚ) • D := by
      rw [map_neg, hD'eq, ← Int.cast_smul_eq_zsmul ℚ, ← neg_smul]
      push_cast; rfl
    have hq2' : ((((-(m' : ℤ)) : ℤ) : ℚ) • D).IsQCartier := e2 ▸ hq2
    have hq1' : (((((m' * a : ℕ) : ℤ)) : ℚ) • Divisor.toQDivisor L).IsQCartier :=
      toQDivisor_zsmul _ L ▸ hq1
    intro z
    rw [curveForm_congr sX e1 hW'Q hq12, curveForm_add sX _ _ hq1 hq2 hq12,
      curveForm_congr sX (toQDivisor_zsmul _ L) hq1 hq1', curveForm_smul sX _ _ hLQ hq1',
      curveForm_congr sX e2 hq2 hq2', curveForm_smul sX _ _ hD hq2']
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast; ring
  have hW'amp : W'.IsAmple hW'c := isAmple_of_curveForm_pos sX W' hW'c hW'Q fun z hz hz0 => by
    rw [hFW]
    have h1 := ha₀lt z hz hz0
    have h2 := hnn z hz
    have h3 : a₀ * FL z ≤ a * FL z := mul_le_mul_of_nonneg_right haa h2
    have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'
    nlinarith
  exact ⟨a, ha, m', hm', W', hW'eq, hW'c, hW'amp⟩

end Ampleness

private theorem solution
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ L : Divisor X, L.IsNef ℂ sX ∧
      (∃ hL : (Divisor.toQDivisor L).IsQCartier,
        {z | z ∈ closedConeOfCurves sX ∧ QDivisor.curveForm sX (Divisor.toQDivisor L) hL z = 0} =
          R) ∧
      ∃ a : ℚ, 0 < a ∧ (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple := by
  classical
  haveI hXp : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  set D := Divisor.toQDivisor K + B with hDdef
  obtain ⟨hD, hRray, hRneg⟩ := hR
  set φ := QDivisor.curveForm sX D hD with hφdef
  set N := closedConeOfCurves sX with hNdef
  have hNclosed : IsClosed (N : Set (NumericalCurveClasses sX)) := by
    rw [hNdef, coe_closedConeOfCurves]; exact isClosed_closure
  obtain ⟨hcurve, hfin, hdec⟩ := closedConeOfCurves_structure hX hK hB hD
  -- the ray `R` is spanned by the class `v` of a curve
  obtain ⟨C, hRv⟩ := hcurve R ⟨hD, hRray, hRneg⟩
  set v := OneCycle.numericalClass sX (C.cycle ℝ) with hvdef
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hRN : R ⊆ N := hRray.1.1
  have hvN : v ∈ N := hRN hvR
  have hv0 : v ≠ 0 := by
    obtain ⟨v', hv'0, hRv'⟩ := hRray.2
    have : v' ∈ R := hRv' ▸ ⟨1, zero_le_one, one_smul _ _⟩
    rw [hRv] at this
    obtain ⟨c, -, hc⟩ := this
    intro hv
    rw [hv, smul_zero] at hc
    exact hv'0 hc.symm
  have hφv : φ v < 0 := hRneg v hvR hv0
  -- an ample Cartier divisor `A` and its degree form `α`, positive on `NE̅(X) ∖ 0`
  obtain ⟨H, hHamp⟩ := exists_isAmple_sheaf sX hXp
  obtain ⟨A, hAc, ⟨eA⟩⟩ := exists_divisor_iso_sheaf H
  haveI := hAc.isInvertibleModule_divisorialSheaf
  have hAamp : A.IsAmple hAc := (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).mpr hHamp
  set α := NumericalCurveClasses.degree sX A.divisorialSheaf with hαdef
  have hα : ∀ z ∈ N, z ≠ 0 → 0 < α z := by
    rw [hαdef, ← curveForm_toQDivisor_eq_degree sX A hAc (QDivisor.isQCartier_toQDivisor hAc)]
    exact curveForm_pos_of_isAmple sX A hAc hAamp _
  have hα0 : ∀ z ∈ N, 0 ≤ α z := fun z hz => nonneg_of_forall_ne_zero_pos N α hα hz
  have hαv := hα v hvN hv0
  -- `ψ = D + ε A` is still negative on `R`
  set ε : ℝ := -φ v / (2 * α v) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  set ψ : NumericalCurveClasses sX →ₗ[ℝ] ℝ := φ + ε • α with hψdef
  have hψv : ψ v < 0 := by
    have : ψ v = φ v / 2 := by
      simp only [hψdef, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hεdef]
      field_simp
      ring
    rw [this]; linarith
  -- the finitely many `ψ`-negative extremal rays
  set 𝓕 : Set (Set (NumericalCurveClasses sX)) :=
    {R' | IsNegativeExtremalRayOf sX D R' ∧ ∀ u ∈ R', u ≠ 0 → ψ u < 0} with h𝓕def
  have h𝓕fin : 𝓕.Finite := by
    refine (hfin A hAc hAamp ε hε).subset fun R' hR' => ⟨hR'.1, fun u hu hu0 => ?_⟩
    have := hR'.2 u hu hu0
    simpa [hψdef] using this
  have hR𝓕 : R ∈ 𝓕 := by
    refine ⟨⟨hD, hRray, hRneg⟩, fun u hu hu0 => ?_⟩
    rw [hRv] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    have hc0 : 0 < c := hc.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc0 hψv
  -- generators of the negative extremal rays
  have hgen : ∀ R' : Set (NumericalCurveClasses sX), IsNegativeExtremalRayOf sX D R' →
      ∃ g, g ≠ 0 ∧ R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • g = w} := fun R' h => h.2.1.2
  choose gen hgen0 hgenR using hgen
  set J := ↥(𝓕 \ {R})
  haveI : Finite J := (h𝓕fin.diff).to_subtype
  haveI : Fintype J := Fintype.ofFinite J
  set g : J → NumericalCurveClasses sX := fun j => gen j.1 j.2.1.1 with hgdef
  have hgmem : ∀ j : J, g j ∈ j.1 := fun j => by
    rw [hgenR j.1 j.2.1.1]; exact ⟨1, zero_le_one, one_smul _ _⟩
  have hgN : ∀ j, g j ∈ N := fun j => j.2.1.1.2.1.1.1 (hgmem j)
  have hgv : ∀ j, ∀ s : ℝ, g j ≠ s • v := by
    intro j s hs
    have hαg := hα _ (hgN j) (hgen0 _ _)
    rcases le_or_gt s 0 with hs0 | hs0
    · have hneg : -g j ∈ N := by
        rw [hs, ← neg_smul]; exact N.smul_mem (by linarith) hvN
      have := hα0 _ hneg
      rw [map_neg] at this
      linarith
    · have hgs : gen j.1 j.2.1.1 = s • v := hs
      refine j.2.2 (Set.mem_singleton_iff.mpr ((hgenR j.1 j.2.1.1).trans (Eq.trans ?_ hRv.symm)))
      ext w
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c * s, mul_nonneg hc hs0.le, by rw [hgs, smul_smul]⟩
      · rintro ⟨c, hc, rfl⟩
        refine ⟨c / s, div_nonneg hc hs0.le, ?_⟩
        rw [hgs, smul_smul, div_mul_cancel₀ _ hs0.ne']
  -- extremality of `R`
  have hext : ∀ a ∈ N, ∀ b ∈ N, (∃ s : ℝ, 0 ≤ s ∧ a + b = s • v) →
      (∃ s : ℝ, 0 ≤ s ∧ a = s • v) ∧ (∃ s : ℝ, 0 ≤ s ∧ b = s • v) := by
    rintro a ha b hb ⟨s, hs, hab⟩
    have hmem : a + b ∈ R := hRv ▸ ⟨s, hs, hab.symm⟩
    obtain ⟨h1, h2⟩ := hRray.1.2.2.2 a ha b hb hmem
    rw [hRv] at h1 h2
    obtain ⟨s₁, hs₁, e₁⟩ := h1
    obtain ⟨s₂, hs₂, e₂⟩ := h2
    exact ⟨⟨s₁, hs₁, e₁.symm⟩, ⟨s₂, hs₂, e₂.symm⟩⟩
  -- Cartier coordinates on `N₁(X)`
  obtain ⟨t, _, Φ, hΦapp⟩ := exists_cartier_coordinates sX
  set w : t → ℚ := fun i => ((C.degree ℂ (MMP.CartierDivisor.sheaf
    (i : X.CartierDivisor)) : ℤ) : ℚ) with hwdef
  have hw : ∀ i, Φ v i = w i := fun i => by
    rw [hΦapp, NumericalCurveClasses.intersectionNumber_ofCartier,
      NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, hwdef]
    push_cast; rfl
  -- a rational supporting form `ℓ`
  obtain ⟨q, hqv, m, hm, hqc, hqg⟩ :=
    exists_rat_supporting Φ N hNclosed α ψ hα hvN hψv hext g hgN hgv w hw
  set ℓ : NumericalCurveClasses sX →ₗ[ℝ] ℝ := ∑ i, (q i : ℝ) •
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ (i : X.CartierDivisor))
    with hℓdef
  have hℓ : ∀ z, ℓ z = ∑ i, (q i : ℝ) * Φ z i := fun z => by
    simp [hℓdef, hΦapp]
  have hℓv : ℓ v = 0 := by rw [hℓ]; exact hqv
  have hℓc : ∀ c ∈ N, 0 ≤ ψ c → m * α c ≤ ℓ c := fun c hc h => by rw [hℓ]; exact hqc c hc h
  have hℓg : ∀ j, 0 < ℓ (g j) := fun j => by rw [hℓ]; exact hqg j
  -- every class of `NE̅(X)` is `c + s v + ∑ τ_j g_j` with `ψ(c) ≥ 0`
  set P : NumericalCurveClasses sX → Prop := fun z => ∃ c ∈ N, 0 ≤ ψ c ∧ ∃ s : ℝ, 0 ≤ s ∧
    ∃ τ : J → ℝ, (∀ j, 0 ≤ τ j) ∧ z = c + s • v + ∑ j, τ j • g j with hPdef
  have hPgen : ∀ x, ∀ R' : Set (NumericalCurveClasses sX), IsNegativeExtremalRayOf sX D R' →
      x ∈ R' → P x := by
    intro x R' hR' hx
    have hxN : x ∈ N := hR'.2.1.1.1 hx
    by_cases hRR : R' = R
    · rw [hRR, hRv] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨0, N.zero_mem, by simp, s, hs, 0, fun _ => le_rfl, by simp⟩
    by_cases hR'𝓕 : R' ∈ 𝓕
    · set j : J := ⟨R', hR'𝓕, hRR⟩ with hjdef
      obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ s • gen R' hR' = x := by
        have := hgenR R' hR' ▸ hx
        exact this
      refine ⟨0, N.zero_mem, by simp, 0, le_rfl, fun j' => if j' = j then s else 0,
        fun j' => by by_cases h : j' = j <;> simp [h, hs], ?_⟩
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add,
        add_zero]
      rw [Finset.sum_eq_single j (fun j' _ h => by simp [h])
        (fun h => absurd (Finset.mem_univ j) h), if_pos rfl]
    · have : ∃ u ∈ R', u ≠ 0 ∧ 0 ≤ ψ u := by
        by_contra hcon
        refine hR'𝓕 ⟨hR', fun u hu hu0 => ?_⟩
        by_contra hψu
        exact hcon ⟨u, hu, hu0, not_lt.mp hψu⟩
      obtain ⟨u, hu, hu0, hψu⟩ := this
      rw [hgenR R' hR'] at hu hx
      obtain ⟨cu, hcu, rfl⟩ := hu
      obtain ⟨cx, hcx, rfl⟩ := hx
      have hcu0 : 0 < cu := hcu.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
      have hψg : 0 ≤ ψ (gen R' hR') := by
        rw [map_smul, smul_eq_mul] at hψu
        exact (mul_nonneg_iff_of_pos_left hcu0).mp hψu
      exact ⟨cx • gen R' hR', hxN, by rw [map_smul, smul_eq_mul]; exact mul_nonneg hcx hψg,
        0, le_rfl, 0, fun _ => le_rfl, by simp⟩
  have hdecomp : ∀ z ∈ N, P z := by
    intro z hz
    obtain ⟨a, haN, hφa, b, hb, rfl⟩ := hdec z hz
    obtain ⟨c, hc, hψc, s, hs, τ, hτ, hbeq⟩ := exists_decomposition_of_mem_span N ψ v g
      (S := ⋃₀ {R' | IsNegativeExtremalRayOf sX D R'})
      (fun x ⟨R', hR', hxR'⟩ => hPgen x R' hR' hxR') hb
    refine ⟨a + c, N.add_mem haN hc, ?_, s, hs, τ, hτ, ?_⟩
    · have := hα0 _ haN
      rw [map_add]
      simp only [hψdef, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hψc ⊢
      nlinarith
    · rw [hbeq]
      abel
  -- `ℓ` is nonnegative on `NE̅(X)` and vanishes there exactly on `R`
  have hℓdecomp : ∀ z ∈ N, 0 ≤ ℓ z ∧ (ℓ z = 0 → z ∈ R) := by
    intro z hz
    obtain ⟨c, hc, hψc, s, hs, τ, hτ, rfl⟩ := hdecomp z hz
    obtain ⟨h1, h2⟩ := nonneg_and_eq_smul_of_eq_zero N α ψ ℓ hα hℓv g hm hℓc hℓg hc hψc s hτ
    exact ⟨h1, fun h0 => by rw [hRv]; exact ⟨s, hs, (h2 h0).symm⟩⟩
  -- clearing denominators: the Cartier divisor `L` with curve form `M ℓ`
  obtain ⟨M, hM, hMq⟩ := MMP.Fourfold.exists_den q
  choose n hn using hMq
  choose W hWc hWiso using fun i : t => exists_divisor_iso_sheaf (i : X.CartierDivisor)
  set L : Divisor X := ∑ i, n i • W i with hLdef
  have hLc : L.IsCartier := isCartier_sum Finset.univ n W hWc
  have hLQ := QDivisor.isQCartier_toQDivisor hLc
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hFL : ∀ z, QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ z = M * ℓ z := by
    intro z
    rw [curveForm_toQDivisor_sum sX Finset.univ n W hWc hLQ, hℓ, Finset.mul_sum,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, curveForm_toQDivisor_eq_intersectionNumber sX (W i) (hWc i) _ i
      (hWiso i).some, ← hΦapp, smul_eq_mul]
    have : (n i : ℝ) = M * q i := by exact_mod_cast (hn i).symm
    rw [this]; ring
  have hLnef : L.IsNef ℂ sX := isNef_of_forall_properCurve sX L hLc hLQ fun C' => by
    rw [hFL]
    exact mul_nonneg (Nat.cast_nonneg _) (hℓdecomp _ (coneOfCurves_le_closedConeOfCurves sX
      (numericalClass_cycle_mem_coneOfCurves sX C'))).1
  have hface : {z | z ∈ closedConeOfCurves sX ∧
      QDivisor.curveForm sX (Divisor.toQDivisor L) hLQ z = 0} = R := by
    ext z
    simp only [Set.mem_setOf_eq, hFL]
    constructor
    · rintro ⟨hz, h0⟩
      exact (hℓdecomp z hz).2 ((mul_eq_zero.mp h0).resolve_left hM0)
    · intro hz
      refine ⟨hRN hz, ?_⟩
      rw [hRv] at hz
      obtain ⟨c, -, rfl⟩ := hz
      rw [map_smul, hℓv, smul_zero, mul_zero]
  -- ampleness of `a L - (K + B)`
  obtain ⟨a, ha, hamp⟩ := exists_isAmple_smul_sub sX L hLc D hD
    (fun z hz => by rw [hFL]; exact mul_nonneg (Nat.cast_nonneg _) (hℓdecomp z hz).1)
    (fun z hz hz0 h0 => by
      rw [hFL] at h0
      exact hRneg z ((hℓdecomp z hz).2 ((mul_eq_zero.mp h0).resolve_left hM0)) hz0)
  exact ⟨L, hLnef, ⟨hLQ, hface⟩, a, ha, hamp⟩

end Proof_lem_mmp_projective_fourfold_lc_supporting_divisor

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **A rational supporting divisor for a negative extremal ray of an lc fourfold.** Let `X` be a
normal projective complex fourfold with canonical divisor `K`, let `(X, B)` be a log canonical
pair with `B` a `ℚ`-divisor, and let `R` be a `(K + B)`-negative extremal ray of `NE̅(X)`. Then
there is a nef Cartier divisor `L` with `{z ∈ NE̅(X) | (L · z) = 0} = R` and a rational `a > 0`
such that `a L - (K + B)` is ample. -/
@[mmp "lem_mmp_projective_fourfold_lc_supporting_divisor"]
public theorem exists_isNef_curveForm_eq_zero_and_isAmple_of_isNegativeExtremalRayOf
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ L : Divisor X, L.IsNef ℂ sX ∧
      (∃ hL : (Divisor.toQDivisor L).IsQCartier,
        {z | z ∈ closedConeOfCurves sX ∧ QDivisor.curveForm sX (Divisor.toQDivisor L) hL z = 0} =
          R) ∧
      ∃ a : ℚ, 0 < a ∧ (a • Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsAmple :=
        by revert X sX hX K hK B hB R hR; first | exact Proof_lem_mmp_projective_fourfold_lc_supporting_divisor.solution | exact Proof_lem_mmp_projective_fourfold_lc_supporting_divisor.solution _ | exact Proof_lem_mmp_projective_fourfold_lc_supporting_divisor.solution _ _ | exact Proof_lem_mmp_projective_fourfold_lc_supporting_divisor.solution _ _ _ | exact Proof_lem_mmp_projective_fourfold_lc_supporting_divisor.solution _ _ _ _

end MMP.Fourfold

