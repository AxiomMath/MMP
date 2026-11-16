module

public import MMP.AlgebraicTopology.NerveTheorem
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# Finite homotopy type from convex covers and nearest-point retractions

A finite union `W` of open convex subsets of a real normed space is covered by those convex
sets, and every nonempty finite intersection of them is convex, hence contractible. By the nerve
theorem `W` is therefore homotopy equivalent to a finite simplicial complex. The same holds for
a finite disjoint union of such sets, covered by the convex pieces of all the summands.

This applies to a compact subset `A` of a real inner product space with a *nearest-point
retraction of reach `τ`*: a continuous map `π`, defined on the open `τ`-neighbourhood of `A`,
sending each point `y` to a nearest point `π y ∈ A`, and satisfying Federer's inequality
`2 τ ⟪y - π y, x - π y⟫ ≤ ‖x - π y‖² ‖y - π y‖` for `x ∈ A`. Every compact set of reach at
least `τ` has one (Federer, *Curvature measures*, Theorem 4.8). Cover `A` by the balls of
radius `τ / 2` around a `τ / 16`-net of `A`, and let `W` be their union. For `y ∈ W`, the points
`y` and `π y` lie in one of these balls: if `y` is close to `A` take a ball around a net point
near `π y`; otherwise Federer's inequality bounds `‖π y - x‖` for the centre `x` of a ball
containing `y`. The straight-line homotopy from `π` to the identity of `W` then stays in `W`,
so `A` is homotopy equivalent to `W`, and hence to a finite simplicial complex.

## Main results

* `MMP.Topology.nonempty_homotopyEquiv_sigma`: homotopy equivalences of the summands give a
  homotopy equivalence of the disjoint unions.
* `MMP.Topology.exists_homotopyEquiv_simplicialComplex_sigma_sUnion_convex`: a finite disjoint
  union of finite unions of open convex sets is homotopy equivalent to a finite simplicial
  complex.
* `MMP.Topology.nonempty_homotopyEquiv_of_segment_subset`: a retraction `r : W → A` whose
  segments `[r y, y]` stay in `W` makes `A` homotopy equivalent to `W`.
* `MMP.Topology.exists_nonempty_homotopyEquiv_sUnion_ball_of_nearestPoint`: a compact set with
  a nearest-point retraction of reach `τ` is homotopy equivalent to a finite union of balls.
* `MMP.Topology.exists_homotopyEquiv_simplicialComplex_sigma_of_nearestPoint`: a finite disjoint
  union of spaces homotopy equivalent to such compact sets is homotopy equivalent to a finite
  simplicial complex.

## References

* [H. Federer, *Curvature measures*, Theorem 4.8][federer1959]
* [A. Hatcher, *Algebraic Topology*, Corollary 4G.3][hatcher2002]
-/

open Set Topology Metric ContinuousMap

namespace MMP.Topology

public noncomputable section

section Sigma

variable {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)]

/-- Homotopies of the summands give a homotopy of the induced maps of disjoint unions. -/
theorem homotopic_sigma {f g : ∀ i, C(X i, Y i)} (h : ∀ i, (f i).Homotopic (g i)) :
    (ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (f i)).Homotopic
      (ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (g i)) := by
  let F : ∀ i, (f i).Homotopy (g i) := fun i ↦ (h i).some
  refine ⟨{ toFun := fun p ↦ ⟨p.2.1, F p.2.1 (p.1, p.2.2)⟩
            continuous_toFun := ?_
            map_zero_left := fun x ↦ by simp
            map_one_left := fun x ↦ by simp }⟩
  have hc : Continuous fun q : Σ i, X i × unitInterval ↦
      (⟨q.1, F q.1 (q.2.2, q.2.1)⟩ : Σ i, Y i) :=
    continuous_sigma fun i ↦ continuous_sigmaMk.comp ((F i).continuous.comp continuous_swap)
  exact hc.comp ((Homeomorph.sigmaProdDistrib).continuous.comp continuous_swap)

/-- Summandwise homotopies `g i ∘ f i ≃ id` give a homotopy from the induced composite on the
disjoint union to the identity. -/
theorem homotopic_id_sigma_comp {f : ∀ i, C(X i, Y i)} {g : ∀ i, C(Y i, X i)}
    (h : ∀ i, ((g i).comp (f i)).Homotopic (ContinuousMap.id (X i))) :
    ((ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (g i)).comp
      (ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (f i))).Homotopic
      (ContinuousMap.id (Σ i, X i)) := by
  rw [show (ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (g i)).comp
        (ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (f i)) =
        ContinuousMap.sigma fun i ↦ (sigmaMk i).comp ((g i).comp (f i)) from
      ContinuousMap.ext fun ⟨_, _⟩ ↦ rfl,
    show ContinuousMap.id (Σ i, X i) =
        ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (ContinuousMap.id (X i)) from
      ContinuousMap.ext fun ⟨_, _⟩ ↦ rfl]
  exact homotopic_sigma h

/-- Homotopy equivalences of the summands give a homotopy equivalence of the disjoint
unions. -/
theorem nonempty_homotopyEquiv_sigma (h : ∀ i, Nonempty (X i ≃ₕ Y i)) :
    Nonempty ((Σ i, X i) ≃ₕ Σ i, Y i) := by
  let e : ∀ i, X i ≃ₕ Y i := fun i ↦ (h i).some
  exact ⟨{ toFun := ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (e i).toFun
           invFun := ContinuousMap.sigma fun i ↦ (sigmaMk i).comp (e i).invFun
           left_inv := homotopic_id_sigma_comp fun i ↦ (e i).left_inv
           right_inv := homotopic_id_sigma_comp fun i ↦ (e i).right_inv }⟩

end Sigma

section ConvexCover

/-- A finite disjoint union of finite unions of open convex sets in real normed spaces is
homotopy equivalent to a finite simplicial complex. -/
theorem exists_homotopyEquiv_simplicialComplex_sigma_sUnion_convex {ι : Type*} [Finite ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (𝒞 : ∀ i, Set (Set (E i))) (h𝒞f : ∀ i, (𝒞 i).Finite)
    (h𝒞o : ∀ i, ∀ C ∈ 𝒞 i, IsOpen C) (h𝒞c : ∀ i, ∀ C ∈ 𝒞 i, Convex ℝ C) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty ((Σ i, (⋃₀ 𝒞 i : Set (E i))) ≃ₕ K.space) := by
  classical
  have : ∀ i, Finite (𝒞 i) := fun i ↦ (h𝒞f i).to_subtype
  let : MetricSpace (Σ i, (⋃₀ 𝒞 i : Set (E i))) := Metric.Sigma.metricSpace
  let U : (Σ i, 𝒞 i) → Set (Σ i, (⋃₀ 𝒞 i : Set (E i))) := fun p ↦
    Sigma.mk p.1 '' (Subtype.val ⁻¹' (p.2 : Set (E p.1)))
  refine exists_homotopyEquiv_simplicialComplex_of_contractible_cover U ?_ ?_ ?_
  · rintro ⟨i, C⟩
    exact isOpenMap_sigmaMk _ (continuous_subtype_val.isOpen_preimage _ (h𝒞o i C C.2))
  · refine eq_univ_of_forall fun ⟨i, x, hx⟩ ↦ ?_
    obtain ⟨C, hC, hxC⟩ := hx
    exact mem_iUnion.2 ⟨⟨i, C, hC⟩, ⟨x, _⟩, hxC, rfl⟩
  · rintro I ⟨p₀, hp₀⟩ ⟨⟨i₀, w₀⟩, hy₀⟩
    have hfst : ∀ p ∈ I, p.1 = i₀ := fun p hp ↦ by
      obtain ⟨w, -, hw⟩ := mem_iInter₂.1 hy₀ p hp
      exact congrArg Sigma.fst hw
    let J : Set (Set (E i₀)) := {C | ∃ hC : C ∈ 𝒞 i₀, (⟨i₀, C, hC⟩ : Σ i, 𝒞 i) ∈ I}
    have hJ : J.Nonempty := by
      obtain ⟨i, C⟩ := p₀
      obtain rfl : i = i₀ := hfst _ hp₀
      exact ⟨C, C.2, hp₀⟩
    let T : Set (⋃₀ 𝒞 i₀ : Set (E i₀)) := Subtype.val ⁻¹' ⋂₀ J
    have hEq : (⋂ p ∈ I, U p) = Sigma.mk i₀ '' T := by
      ext ⟨j, w⟩
      simp only [mem_iInter₂]
      constructor
      · intro hw
        obtain ⟨w', -, hw'⟩ := hw p₀ hp₀
        obtain rfl : j = i₀ := (congrArg Sigma.fst hw').symm.trans (hfst _ hp₀)
        refine ⟨w, mem_sInter.2 fun C ⟨hC, hCI⟩ ↦ ?_, rfl⟩
        obtain ⟨w'', hw'', hw''w⟩ := hw _ hCI
        obtain rfl := sigma_mk_injective hw''w
        exact hw''
      · rintro ⟨w', hw', hw'w⟩ ⟨i, C⟩ hp
        obtain rfl : i = i₀ := hfst _ hp
        exact ⟨w', mem_sInter.1 hw' C ⟨C.2, hp⟩, hw'w⟩
    rw [hEq] at hy₀ ⊢
    have hT : (Subtype.val '' T : Set (E i₀)) = ⋂₀ J := by
      rw [Subtype.image_preimage_coe]
      refine inter_eq_right.2 fun x hx ↦ ?_
      obtain ⟨C, hC, hCI⟩ := hJ
      exact ⟨C, hC, mem_sInter.1 hx C ⟨hC, hCI⟩⟩
    obtain ⟨w, hw, -⟩ := hy₀
    have := (convex_sInter fun C hC ↦ h𝒞c i₀ C hC.1).contractibleSpace ⟨w.1, hw⟩
    have : ContractibleSpace T :=
      ((IsEmbedding.subtypeVal.homeomorphImage T).trans (Homeomorph.setCongr hT)).contractibleSpace
    have hemb := @IsEmbedding.sigmaMk _ (fun i ↦ ↥(⋃₀ 𝒞 i : Set (E i))) _ i₀
    exact (hemb.homeomorphImage T).symm.contractibleSpace

end ConvexCover

section NearestPoint

/-- A retraction `r` of `W` onto `A ⊆ W` such that every segment `[r y, y]` lies in `W` makes
`A` homotopy equivalent to `W`. -/
theorem nonempty_homotopyEquiv_of_segment_subset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {A W : Set E}
    (hAW : A ⊆ W) (r : E → E) (hrc : ContinuousOn r W) (hrA : ∀ y ∈ W, r y ∈ A) (hra : ∀ a ∈ A, r a = a)
    (hseg : ∀ y ∈ W, segment ℝ (r y) y ⊆ W) : Nonempty (A ≃ₕ W) := by
  let i : C(A, W) := ⟨Set.inclusion hAW, continuous_inclusion hAW⟩
  let p : C(W, A) := ⟨fun y ↦ ⟨r y, hrA y y.2⟩, (hrc.domRestrict).subtype_mk _⟩
  have hmem : ∀ (t : unitInterval) (y : W), r y + (t : ℝ) • ((y : E) - r y) ∈ W := fun t y ↦
    hseg y y.2 (by rw [segment_eq_image']; exact ⟨t, t.2, rfl⟩)
  refine ⟨{ toFun := i, invFun := p, left_inv := ?_, right_inv := ?_ }⟩
  · rw [show p.comp i = ContinuousMap.id A from
      ContinuousMap.ext fun a ↦ Subtype.ext (show r a = a from hra a a.2)]
  · refine ⟨{ toFun := fun q ↦ ⟨r q.2 + (q.1 : ℝ) • ((q.2 : E) - r q.2), hmem q.1 q.2⟩
              continuous_toFun := ?_
              map_zero_left := fun y ↦ by simp [i, p]; rfl
              map_one_left := fun y ↦ by simp }⟩
    have hr : Continuous fun y : W ↦ r y := hrc.domRestrict
    exact Continuous.subtype_mk ((hr.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((continuous_subtype_val.comp continuous_snd).sub (hr.comp continuous_snd)))) _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A compact set `A` with a nearest-point retraction `π` of reach `τ` (continuous on the
`τ`-neighbourhood of `A`, onto `A`, nearest, and satisfying Federer's inequality) is homotopy
equivalent to a finite union of balls of radius `τ / 2` centred in `A`. -/
theorem exists_nonempty_homotopyEquiv_sUnion_ball_of_nearestPoint {A : Set E}
    (hA : IsCompact A) {τ : ℝ} (hτ : 0 < τ) (π : E → E)
    (hπc : ContinuousOn π (thickening τ A)) (hπA : ∀ y ∈ thickening τ A, π y ∈ A)
    (hπn : ∀ y ∈ thickening τ A, ∀ x ∈ A, ‖y - π y‖ ≤ ‖y - x‖)
    (hπF : ∀ y ∈ thickening τ A, ∀ x ∈ A,
      2 * τ * inner ℝ (y - π y) (x - π y) ≤ ‖x - π y‖ ^ 2 * ‖y - π y‖) :
    ∃ s : Set E, s.Finite ∧ s ⊆ A ∧
      Nonempty (A ≃ₕ (⋃₀ ((fun x ↦ ball x (τ / 2)) '' s) : Set E)) := by
  obtain ⟨s, hsA, hsf, hcov⟩ := hA.finite_cover_balls (e := τ / 16) (by positivity)
  refine ⟨s, hsf, hsA, ?_⟩
  set W : Set E := ⋃₀ ((fun x ↦ ball x (τ / 2)) '' s)
  have memW : ∀ {x y : E}, x ∈ s → dist y x < τ / 2 → y ∈ W := fun hx hy ↦
    ⟨_, ⟨_, hx, rfl⟩, mem_ball.2 hy⟩
  have hWT : W ⊆ thickening τ A := by
    rintro y ⟨_, ⟨x, hx, rfl⟩, hy⟩
    exact mem_thickening_iff.2 ⟨x, hsA hx, (mem_ball.1 hy).trans (by linarith)⟩
  have hAW : A ⊆ W := fun a ha ↦ by
    obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 (hcov ha)
    exact memW hx ((mem_ball.1 hax).trans (by linarith))
  have hra : ∀ a ∈ A, π a = a := fun a ha ↦ by
    simpa [sub_eq_zero, eq_comm] using hπn a (self_subset_thickening hτ A ha) a ha
  refine nonempty_homotopyEquiv_of_segment_subset hAW π (hπc.mono hWT)
    (fun y hy ↦ hπA y (hWT hy)) hra ?_
  rintro y ⟨_, ⟨xk, hxk, rfl⟩, hyk⟩
  have hyT := hWT (memW hxk (mem_ball.1 hyk))
  rw [mem_ball, dist_eq_norm] at hyk
  set p := π y with hp
  have hpA : p ∈ A := hπA y hyT
  have hd : ‖y - p‖ ≤ ‖y - xk‖ := hπn y hyT xk (hsA hxk)
  suffices ∃ x ∈ s, ‖p - x‖ < τ / 2 ∧ ‖y - x‖ < τ / 2 by
    obtain ⟨x, hx, hpx, hyx⟩ := this
    refine ((convex_ball x (τ / 2)).segment_subset ?_ ?_).trans
      (subset_sUnion_of_mem ⟨x, hx, rfl⟩) <;> rwa [mem_ball, dist_eq_norm]
  rcases lt_or_ge ‖y - p‖ (τ / 2 - τ / 16) with hsmall | hlarge
  · obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (hcov hpA)
    rw [mem_ball, dist_eq_norm] at hpx
    refine ⟨x, hx, hpx.trans (by linarith), ?_⟩
    calc ‖y - x‖ = ‖(y - p) + (p - x)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - p‖ + ‖p - x‖ := norm_add_le _ _
      _ < τ / 2 := by linarith
  · refine ⟨xk, hxk, ?_, hyk⟩
    have hF := hπF y hyT xk (hsA hxk)
    have hexp : ‖y - xk‖ ^ 2 =
        ‖y - p‖ ^ 2 - 2 * inner ℝ (y - p) (xk - p) + ‖xk - p‖ ^ 2 := by
      rw [← norm_sub_sq_real, sub_sub_sub_cancel_right]
    rw [← hp] at hF
    have h1 : ‖xk - p‖ ^ 2 * (τ - ‖y - p‖) ≤ τ * (‖y - xk‖ ^ 2 - ‖y - p‖ ^ 2) := by
      linear_combination hF - τ * hexp
    have h2 : ‖xk - p‖ ^ 2 * (τ / 2) ≤ ‖xk - p‖ ^ 2 * (τ - ‖y - p‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have h3 : ‖y - xk‖ ^ 2 - ‖y - p‖ ^ 2 < τ ^ 2 / 4 - (7 * τ / 16) ^ 2 := by
      nlinarith [norm_nonneg (y - p), norm_nonneg (y - xk)]
    have hq : ‖xk - p‖ ^ 2 < (τ / 2) ^ 2 := by
      nlinarith [mul_lt_mul_of_pos_left h3 hτ]
    rw [norm_sub_rev]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hq

/-- A finite disjoint union of spaces, each homotopy equivalent to a compact set with a
nearest-point retraction of positive reach, is homotopy equivalent to a finite simplicial
complex. -/
theorem exists_homotopyEquiv_simplicialComplex_sigma_of_nearestPoint {ι : Type*} [Finite ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)] (A : ∀ i, Set (F i))
    (hX : ∀ i, Nonempty (X i ≃ₕ A i)) (hA : ∀ i, IsCompact (A i))
    (hreach : ∀ i, ∃ τ > 0, ∃ π : F i → F i, ContinuousOn π (thickening τ (A i)) ∧
      (∀ y ∈ thickening τ (A i), π y ∈ A i) ∧
      (∀ y ∈ thickening τ (A i), ∀ x ∈ A i, ‖y - π y‖ ≤ ‖y - x‖) ∧
      (∀ y ∈ thickening τ (A i), ∀ x ∈ A i,
        2 * τ * inner ℝ (y - π y) (x - π y) ≤ ‖x - π y‖ ^ 2 * ‖y - π y‖)) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty ((Σ i, X i) ≃ₕ K.space) := by
  choose τ hτ π hπc hπA hπn hπF using hreach
  choose s hsf hsA hW using fun i ↦ exists_nonempty_homotopyEquiv_sUnion_ball_of_nearestPoint
    (hA i) (hτ i) (π i) (hπc i) (hπA i) (hπn i) (hπF i)
  obtain ⟨N, K, hK, ⟨e⟩⟩ := exists_homotopyEquiv_simplicialComplex_sigma_sUnion_convex
    (fun i ↦ (fun x ↦ ball x (τ i / 2)) '' s i) (fun i ↦ (hsf i).image _)
    (fun i ↦ forall_mem_image.2 fun _ _ ↦ isOpen_ball)
    (fun i ↦ forall_mem_image.2 fun x _ ↦ convex_ball x _)
  obtain ⟨e₁⟩ := nonempty_homotopyEquiv_sigma hX
  obtain ⟨e₂⟩ := nonempty_homotopyEquiv_sigma hW
  exact ⟨N, K, hK, ⟨(e₁.trans e₂).trans e⟩⟩

end NearestPoint

end

end MMP.Topology
