module

public import MMP.AlgebraicTopology.ProperNeighbourhoodRetract.Whitney
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Neighbourhood retractions in spaces locally homeomorphic to `ℝᵐ⁺¹`

Let `Z` be a proper metric space every point of which lies in the source of a chart
`Z ⇀ ℝᵐ⁺¹` (an open partial homeomorphism), and `X ⊆ Z` closed and locally contractible. Then `X`
is a retract of an open neighbourhood (Borsuk). The cover of `Z - X` that Borsuk's construction
needs is built chart by chart: take a locally finite refinement `v_z` of shrunken chart domains,
and in the chart of `v_z` the Whitney boxes of the closed set
`C_z = (ℝᵐ⁺¹ - e_z(v_z)) ∪ e_z(X ∩ v_z)`, pulled back to `v_z`. Near a point of `X` only finitely
many `v_z` occur, each contributing boundedly many boxes through a point; boxes meeting a small
ball about `x ∈ X` are small in the chart, hence in `Z`.

## Main results

* `MMP.NbhdRetract.exists_retraction_of_charts`.
-/

@[expose] public section

open Set Topology Filter Metric

namespace MMP

open MMP

namespace NbhdRetract

open MMP.NbhdRetract

variable {Z : Type*} [MetricSpace Z] {m : ℕ}

/-- A shrunken chart domain: an open neighbourhood of `z` whose closure lies in the source, with
bounded image. -/
theorem exists_isOpen_closure_subset_source (e : OpenPartialHomeomorph Z (Fin (m + 1) → ℝ))
    {z : Z} (hz : z ∈ e.source) :
    ∃ u : Set Z, IsOpen u ∧ z ∈ u ∧ closure u ⊆ e.source ∧ Bornology.IsBounded (e '' u) := by
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 e.open_target (e z) (e.map_source hz)
  set u := e.source ∩ e ⁻¹' ball (e z) (r / 2)
  have hsub : closedBall (e z) (r / 2) ⊆ e.target :=
    (closedBall_subset_ball (by linarith)).trans hrT
  have hK : IsCompact (e.symm '' closedBall (e z) (r / 2)) :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hsub)
  have huK : u ⊆ e.symm '' closedBall (e z) (r / 2) := fun y hy ↦
    ⟨e y, ball_subset_closedBall hy.2, e.left_inv hy.1⟩
  refine ⟨u, e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball,
    ⟨hz, mem_ball_self (by linarith)⟩, ?_, (isBounded_ball (x := e z) (r := r / 2)).subset ?_⟩
  · refine (closure_minimal huK hK.isClosed).trans ?_
    rintro _ ⟨w, hw, rfl⟩
    exact e.map_target (hsub hw)
  · exact image_subset_iff.2 fun _ hy ↦ hy.2

section Chart

variable {e : OpenPartialHomeomorph Z (Fin (m + 1) → ℝ)} {v X : Set Z}

/-- The complement of the closed set `(ℝᵐ⁺¹ - e(v)) ∪ e(X ∩ v)` of a chart is `e(v - X)`. -/
theorem compl_chartSet (hv : v ⊆ e.source) : ((e '' v)ᶜ ∪ e '' (X ∩ v))ᶜ = e '' (v \ X) := by
  ext w
  simp only [compl_union, compl_compl, mem_inter_iff, mem_compl_iff, mem_image]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hn⟩
    exact ⟨y, ⟨hy, fun hyX ↦ hn ⟨y, ⟨hyX, hy⟩, rfl⟩⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyX⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨y', ⟨hy'X, hy'⟩, hyy⟩
    exact hyX (e.injOn (hv hy') (hv hy) hyy ▸ hy'X)

/-- The set `(ℝᵐ⁺¹ - e(v)) ∪ e(X ∩ v)` of a chart is closed. -/
theorem isClosed_chartSet (hvo : IsOpen v) (hv : v ⊆ e.source) (hX : IsClosed X) :
    IsClosed ((e '' v)ᶜ ∪ e '' (X ∩ v)) := by
  rw [← isOpen_compl_iff, compl_chartSet hv]
  exact e.isOpen_image_of_subset_source (hvo.sdiff hX) (sdiff_subset.trans hv)

/-- The set `(ℝᵐ⁺¹ - e(v)) ∪ e(X ∩ v)` of a chart with bounded `e(v)` is nonempty. -/
theorem chartSet_nonempty (hb : Bornology.IsBounded (e '' v)) :
    ((e '' v)ᶜ ∪ e '' (X ∩ v)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, union_empty_iff, compl_empty_iff] at h
  exact NormedSpace.unbounded_univ ℝ (Fin (m + 1) → ℝ) (h.1 ▸ hb)

/-- A point of `v - X` is sent outside the set `(ℝᵐ⁺¹ - e(v)) ∪ e(X ∩ v)`. -/
theorem notMem_chartSet (hv : v ⊆ e.source) {y : Z} (hy : y ∈ v) (hyX : y ∉ X) :
    e y ∉ (e '' v)ᶜ ∪ e '' (X ∩ v) := by
  rw [← mem_compl_iff, compl_chartSet hv]
  exact ⟨y, ⟨hy, hyX⟩, rfl⟩

/-- A point of `X` in the chart source is sent into the set `(ℝᵐ⁺¹ - e(v)) ∪ e(X ∩ v)`. -/
theorem mem_chartSet (hv : v ⊆ e.source) {x : Z} (hx : x ∈ X) (hxs : x ∈ e.source) :
    e x ∈ (e '' v)ᶜ ∪ e '' (X ∩ v) := by
  by_cases hxv : x ∈ v
  · exact Or.inr ⟨x, ⟨hx, hxv⟩, rfl⟩
  · refine Or.inl ?_
    rintro ⟨y, hy, hyx⟩
    exact hxv (e.injOn (hv hy) hxs hyx ▸ hy)

/-- Pulled-back Whitney boxes meeting a small ball about `x` are small and of high level. -/
theorem exists_pos_forall_whitneyBox_small {C : Set (Fin (m + 1) → ℝ)}
    (hvs : closure v ⊆ e.source) (hC : IsClosed C) {x : Z} (hx : x ∈ e.source → e x ∈ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p, (v ∩ e ⁻¹' whitneyBox C p ∩ ball x δ).Nonempty →
      (∀ y ∈ v ∩ e ⁻¹' whitneyBox C p, dist y x < ε / 3) ∧ (2 : ℝ) ^ (-p.1) < ε := by
  by_cases hxc : x ∈ closure v
  · have hxs := hvs hxc
    obtain ⟨σ, hσ, hσx⟩ := Metric.continuousAt_iff.1
      (e.continuousAt_symm (e.map_source hxs)) (ε / 3) (by positivity)
    obtain ⟨δ', hδ', hδ'p⟩ := whitney_small hC (e x) (hx hxs)
      (lt_min (half_pos hσ) hε : 0 < min (σ / 2) ε)
    obtain ⟨δ'', hδ'', hδ''x⟩ := Metric.continuousAt_iff.1
      (e.continuousAt hxs) (min δ' (σ / 2)) (lt_min hδ' (half_pos hσ))
    refine ⟨δ'', hδ'', fun p ⟨y₀, hy₀B, hy₀x⟩ ↦ ?_⟩
    have hy₀w : dist (e y₀) (e x) < min δ' (σ / 2) := hδ''x hy₀x
    have hlev := (hδ'p p ⟨e y₀, hy₀B.2, lt_of_lt_of_le hy₀w (min_le_left _ _)⟩).2
    refine ⟨fun y hy ↦ ?_, lt_of_lt_of_le hlev (min_le_right _ _)⟩
    have h1 : dist (e y) (e y₀) < 2 * whitneyScale p.1 :=
      (dist_triangle_right _ _ (fun j ↦ (p.2 j : ℝ) * whitneyScale p.1)).trans_lt
        (by linarith [mem_ball.1 hy.2.1, mem_ball.1 hy₀B.2.1])
    have h3 : whitneyScale p.1 = (2 : ℝ) ^ (-p.1) / 8 := rfl
    have h4 : dist (e y) (e x) < σ := by
      linarith [dist_triangle (e y) (e y₀) (e x), min_le_left (σ / 2) ε, min_le_right δ' (σ / 2)]
    have := hσx h4
    rwa [e.left_inv (hvs (subset_closure hy.1)), e.left_inv hxs] at this
  · obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hxc)
    exact ⟨δ, hδ, fun p ⟨y, hyB, hyb⟩ ↦ (hδv hyb (subset_closure hyB.1)).elim⟩

/-- A point outside `C` lies in boundedly many pulled-back Whitney boxes of `C`. -/
theorem finite_and_ncard_le_whitneyBox {C : Set (Fin (m + 1) → ℝ)} (hC : IsClosed C)
    (hCne : C.Nonempty) {y : Z} (hy : y ∈ v → e y ∉ C) :
    {p | y ∈ v ∩ e ⁻¹' whitneyBox C p}.Finite ∧
      {p | y ∈ v ∩ e ⁻¹' whitneyBox C p}.ncard ≤ 2 * 2 ^ (m + 1) := by
  by_cases hyv : y ∈ v
  · obtain ⟨h1, h2⟩ := whitney_order hC hCne (hy hyv)
    have hsub : {p | y ∈ v ∩ e ⁻¹' whitneyBox C p} ⊆ {p | e y ∈ whitneyBox C p} :=
      fun p hp ↦ hp.2
    exact ⟨h1.subset hsub, (Set.ncard_le_ncard hsub h1).trans h2⟩
  · simp [hyv]

end Chart

/-- Refining a locally finite family into families of uniformly small sets anchored on `X`
gives the smallness condition of Borsuk's construction. -/
theorem exists_dist_lt_of_locallyFinite {ι κ : Type*} {v : ι → Set Z} (hv : LocallyFinite v)
    {B : ι × κ → Set Z} (hBv : ∀ i, B i ⊆ v i.1) {X : Set Z} {a : ι × κ → Z}
    (ha : ∀ i (h : (B i).Nonempty), dist h.some (a i) = infDist h.some X) {η : κ → ℝ}
    {x : Z} (hx : x ∈ X) {ε : ℝ}
    (hB : ∀ z, ∃ δ > 0, ∀ p, (B (z, p) ∩ ball x δ).Nonempty →
      (∀ y ∈ B (z, p), dist y x < ε / 3) ∧ η p < ε) :
    ∃ δ > 0, ∀ i, (B i ∩ ball x δ).Nonempty → dist (a i) x < ε ∧ η i.2 < ε := by
  obtain ⟨t, ht, htfin⟩ := hv x
  obtain ⟨δt, hδt, hδtt⟩ := Metric.mem_nhds_iff.1 ht
  set P : ι → ℝ → Prop := fun z δ ↦ ∀ p, (B (z, p) ∩ ball x δ).Nonempty →
    (∀ y ∈ B (z, p), dist y x < ε / 3) ∧ η p < ε
  have hPmono : ∀ z δ δ', P z δ → δ' ≤ δ → P z δ' := fun z δ δ' h hδ p hp ↦
    h p (hp.mono (inter_subset_inter_right _ (ball_subset_ball hδ)))
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ δt ∧ ∀ z ∈ htfin.toFinset, P z δ := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ)
      (Filter.Eventually.and (Filter.mem_of_superset (Ioo_mem_nhdsGT hδt)
        fun δ hδ ↦ hδ.2.le : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ δt) ?_)
    refine (Filter.eventually_all_finset _).2 fun z _ ↦ ?_
    obtain ⟨δz, hδz, hPδ⟩ := hB z
    exact Filter.mem_of_superset (Ioo_mem_nhdsGT hδz) fun δ hδ ↦ hPmono z _ _ hPδ hδ.2.le
  obtain ⟨δ, hδ, hδδt, hδP⟩ := hev.exists
  refine ⟨δ, hδ, fun ⟨z, p⟩ hi ↦ ?_⟩
  have hzF : z ∈ htfin.toFinset := by
    obtain ⟨y, hyB, hyb⟩ := hi
    exact htfin.mem_toFinset.2 ⟨y, hBv _ hyB, hδtt (ball_subset_ball hδδt hyb)⟩
  obtain ⟨hdiam, hlev⟩ := hδP z hzF p hi
  have hne : (B (z, p)).Nonempty := hi.mono inter_subset_left
  have hy := hdiam _ hne.some_mem
  have h1 := ha (z, p) hne
  have h2 : infDist hne.some X ≤ dist hne.some x := infDist_le_dist_of_mem hx
  refine ⟨?_, hlev⟩
  have := dist_triangle (a (z, p)) hne.some x
  rw [dist_comm (a (z, p)) hne.some] at this
  linarith [dist_nonneg (x := hne.some) (y := x)]

/-- Refining a locally finite family into families of boundedly overlapping sets gives a
family of locally bounded order. -/
theorem exists_ncard_le_of_locallyFinite {ι κ : Type*} {v : ι → Set Z} (hv : LocallyFinite v)
    {B : ι × κ → Set Z} (hBv : ∀ i, B i ⊆ v i.1) {s : Set Z} {N : ℕ}
    (hB : ∀ y ∈ s, ∀ z, {p | y ∈ B (z, p)}.Finite ∧ {p | y ∈ B (z, p)}.ncard ≤ N) (x : Z) :
    ∃ δ > 0, ∃ d : ℕ, ∀ y ∈ ball x δ, y ∈ s →
      {i | y ∈ B i}.Finite ∧ {i | y ∈ B i}.ncard ≤ d := by
  classical
  obtain ⟨t, ht, htfin⟩ := hv x
  obtain ⟨δt, hδt, hδtt⟩ := Metric.mem_nhds_iff.1 ht
  set F := htfin.toFinset
  refine ⟨δt, hδt, F.card * N, fun y hyb hys ↦ ?_⟩
  have hfib := hB y hys
  set T : Finset (ι × κ) := F.biUnion fun z ↦ (hfib z).1.toFinset.image fun p ↦ (z, p)
  have hsub : {i | y ∈ B i} ⊆ T := by
    rintro ⟨z, p⟩ hi
    simp only [T, Finset.coe_biUnion, Finset.coe_image, mem_iUnion, Finset.mem_coe,
      Set.Finite.mem_toFinset, mem_image, Prod.mk.injEq]
    exact ⟨z, htfin.mem_toFinset.2 ⟨y, hBv _ hi, hδtt hyb⟩, p, hi, rfl, rfl⟩
  have hcard : T.card ≤ F.card * N := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ z ∈ F, ((hfib z).1.toFinset.image fun p ↦ (z, p)).card
        ≤ ∑ _z ∈ F, N := Finset.sum_le_sum fun z _ ↦ by
          refine Finset.card_image_le.trans ?_
          rw [← Set.ncard_eq_toFinset_card _ (hfib z).1]
          exact (hfib z).2
      _ = F.card * N := by simp
  exact ⟨T.finite_toSet.subset hsub,
    (Set.ncard_le_ncard hsub T.finite_toSet).trans (by rwa [Set.ncard_coe_finset])⟩

/-- **Borsuk's neighbourhood retraction in a space locally homeomorphic to `ℝᵐ⁺¹`.** -/
theorem exists_retraction_of_charts [ProperSpace Z]
    (hchart : ∀ z : Z, ∃ e : OpenPartialHomeomorph Z (Fin (m + 1) → ℝ), z ∈ e.source)
    {X : Set Z} (hX : IsClosed X)
    (hloc : ∀ x ∈ X, ∀ ε > 0, ∃ W ⊆ X, W ⊆ ball x ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x ρ ∩ X ⊆ W) :
    ∃ U : Set Z, IsOpen U ∧ X ⊆ U ∧ ∃ r : Z → Z, ContinuousOn r U ∧ MapsTo r U X ∧
      ∀ x ∈ X, r x = x := by
  classical
  rcases X.eq_empty_or_nonempty with rfl | hXne
  · exact ⟨∅, isOpen_empty, subset_rfl, id, continuousOn_empty _, mapsTo_empty _ _, by simp⟩
  obtain ⟨e₀, he₀⟩ := hXne
  choose e he using hchart
  choose u hu hzu hus hub using fun z ↦ exists_isOpen_closure_subset_source (e z) (he z)
  obtain ⟨v, hvo, hvcov, hvlf, hvu⟩ := precise_refinement u hu
    (iUnion_eq_univ_iff.2 fun z ↦ ⟨z, hzu z⟩)
  have hvs : ∀ z, closure (v z) ⊆ (e z).source := fun z ↦ (closure_mono (hvu z)).trans (hus z)
  have hvs' : ∀ z, v z ⊆ (e z).source := fun z ↦ subset_closure.trans (hvs z)
  set C : Z → Set (Fin (m + 1) → ℝ) := fun z ↦ (e z '' v z)ᶜ ∪ e z '' (X ∩ v z)
  have hCcl : ∀ z, IsClosed (C z) := fun z ↦ isClosed_chartSet (hvo z) (hvs' z) hX
  have hCne : ∀ z, (C z).Nonempty := fun z ↦
    chartSet_nonempty ((hub z).subset (image_mono (hvu z)))
  set B : Z × (ℤ × (Fin (m + 1) → ℤ)) → Set Z :=
    fun i ↦ v i.1 ∩ e i.1 ⁻¹' whitneyBox (C i.1) i.2
  have hBo : ∀ i, IsOpen (B i) := fun i ↦
    ((e i.1).continuousOn.mono (hvs' i.1)).isOpen_inter_preimage (hvo i.1)
      (isOpen_whitneyBox _ _)
  set a : Z × (ℤ × (Fin (m + 1) → ℤ)) → Z := fun i ↦
    if h : (B i).Nonempty then (hX.exists_infDist_eq_dist ⟨e₀, he₀⟩ h.some).choose else e₀
    with hadef
  have ha : ∀ i, a i ∈ X := fun i ↦ by
    simp only [hadef]
    split_ifs with h
    · exact (hX.exists_infDist_eq_dist ⟨e₀, he₀⟩ h.some).choose_spec.1
    · exact he₀
  have ha' : ∀ i (h : (B i).Nonempty), dist h.some (a i) = infDist h.some X := fun i h ↦ by
    simp only [hadef, h, ↓reduceDIte]
    exact (hX.exists_infDist_eq_dist ⟨e₀, he₀⟩ h.some).choose_spec.2.symm
  have hcov : ∀ y ∉ X, ∃ i, y ∈ B i := fun y hy ↦ by
    obtain ⟨z, hz⟩ := mem_iUnion.1 (hvcov ▸ mem_univ y)
    obtain ⟨p, hp⟩ := exists_mem_whitneyBox (hCcl z) (hCne z) (notMem_chartSet (hvs' z) hz hy)
    exact ⟨(z, p), hz, hp⟩
  refine exists_retraction hX hloc B a (fun i ↦ (2 : ℝ) ^ (-i.2.1)) hBo ha
    (fun i ↦ by positivity) hcov (fun x hx ε hε ↦ ?_) fun x _ ↦ ?_
  · exact exists_dist_lt_of_locallyFinite hvlf (B := B) (fun _ ↦ inter_subset_left) ha'
      (η := fun p ↦ (2 : ℝ) ^ (-p.1)) hx fun z ↦
        exists_pos_forall_whitneyBox_small (e := e z) (v := v z) (hvs z) (hCcl z)
          (mem_chartSet (hvs' z) hx) hε
  · exact exists_ncard_le_of_locallyFinite hvlf (B := B) (fun _ ↦ inter_subset_left) (s := Xᶜ)
      (fun y hy z ↦ finite_and_ncard_le_whitneyBox (e := e z) (v := v z) (hCcl z) (hCne z)
        fun hyv ↦ notMem_chartSet (hvs' z) hyv hy) x

end NbhdRetract

end MMP
