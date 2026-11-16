module

public import MMP.Topology.Manifold.NeighbourhoodRetract.Cover
public import MMP.Topology.Manifold.NeighbourhoodRetract.Metric
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Contractible

/-!
# Proper neighbourhood deformations in topological manifolds (Fulton, §19.1)

Let `Y` be a Hausdorff, second-countable topological `n`-manifold and `X ⊆ Y` closed, every point
of `X` having a basis of open contractible neighbourhoods in `X`. Then `X` has arbitrarily small
proper neighbourhood deformations (`HasProperNeighbourhoodDeformations X`): inside any
neighbourhood `M` of `X` there are a closed neighbourhood `N` of `X`, a proper retraction
`r : N → X` and a proper homotopy `G : N × [0, 1] → Y`, with values in `M`, from the inclusion to
`r`. This is the setting of the cap product of [BT] 3.1.7 for the oriented real manifolds of
`thm_ext_c19_poincare_alexander_duality`.

No imbedding of `Y` in some `ℝᴺ` is used. Give `Y` a proper metric
(`exists_metricSpace_properSpace`). The set `S = X × ℝ ∪ Y × {0}` is closed and locally
contractible in the `(n + 1)`-manifold `Y × ℝ`, hence (Borsuk, with a Whitney cover built chart
by chart: `NbhdRetract.exists_retraction_of_charts`) a retract `R` of an open neighbourhood,
proper over `S` on a closed neighbourhood. For `y` near `X` the segment `{y} × [0, 1]` stays
where `R` is defined; `G(y, t) = pr_Y R(y, t)` starts at `y` because `(y, 0) ∈ S`, and ends at
`r(y) = pr_Y R(y, 1) ∈ X` because `R(y, 1)` is close to `(y, 1)`, hence off `Y × {0}`.

## Main results

* `MMP.hasProperNeighbourhoodDeformations_of_chartedSpace`: a closed, locally contractible subset
  of a Hausdorff second-countable topological manifold has arbitrarily small proper
  neighbourhood deformations.
* `MMP.exists_isClosed_isProperMap_retraction_homotopy_of_chartedSpace`: the
  deformations can be chosen to fix `X`.
* `MMP.exists_isClosed_isProperMap_retraction_of_chartedSpace`: a closed neighbourhood with a
  proper retraction onto `X`.
* `MMP.exists_isClosed_isProperMap_retraction_homotopy_of_properSpace`,
  `MMP.hasProperNeighbourhoodDeformations_of_properSpace`: the same for a proper metric.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], Appendix, Theorem A.7.
-/

@[expose] public section

open Set Topology Filter Metric unitInterval

namespace MMP

/-- A subset `W` of `Y × ℝ` that slides, along the second coordinate, onto `U × {c}` with `U`
contractible is contractible. -/
theorem contractibleSpace_of_forall_segment_mem {Y : Type*} [TopologicalSpace Y]
    {W : Set (Y × ℝ)} {U : Set Y} [ContractibleSpace U] (c : ℝ) (hWU : ∀ q ∈ W, q.1 ∈ U)
    (hUW : ∀ u ∈ U, (u, c) ∈ W)
    (hseg : ∀ q ∈ W, ∀ s ∈ Icc (0 : ℝ) 1, (q.1, q.2 + s * (c - q.2)) ∈ W) :
    ContractibleSpace W := by
  set p : C(W, U) := ⟨fun q ↦ ⟨q.1.1, hWU _ q.2⟩, by fun_prop⟩
  set i : C(U, W) := ⟨fun u ↦ ⟨(u.1, c), hUW _ u.2⟩, by fun_prop⟩
  have H : (ContinuousMap.id W).Homotopic (i.comp p) := ⟨{
    toFun := fun z ↦ ⟨(z.2.1.1, z.2.1.2 + (z.1 : ℝ) * (c - z.2.1.2)), hseg _ z.2.2 _ z.1.2⟩
    continuous_toFun := by fun_prop
    map_zero_left := fun q ↦ by ext <;> simp
    map_one_left := fun q ↦ by ext <;> simp [i, p] }⟩
  obtain ⟨u, hu⟩ := (contractible_iff_id_nullhomotopic U).1 inferInstance
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨i u, H.trans ?_⟩
  have := (ContinuousMap.Homotopic.refl i).comp (hu.comp (ContinuousMap.Homotopic.refl p))
  rw [ContinuousMap.id_comp, ContinuousMap.const_comp, ContinuousMap.comp_const] at this
  exact this

/-- In a space charted on a real normed space, every point `y` has arbitrarily small contractible
neighbourhoods: for every `ε > 0` there is a contractible `W ⊆ ball y ε` containing a ball
about `y`. -/
theorem exists_contractible_subset_ball_of_chartedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Y : Type*} [PseudoMetricSpace Y] [ChartedSpace E Y] (y : Y) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ W : Set Y, W ⊆ ball y ε ∧ ContractibleSpace W ∧ ∃ ρ > 0, ball y ρ ⊆ W := by
  set e := chartAt E y
  have hy : y ∈ e.source := mem_chart_source _ y
  set O := e.source ∩ ball y ε
  have hO : IsOpen (e '' O) :=
    e.isOpen_image_of_subset_source (e.open_source.inter isOpen_ball) inter_subset_left
  obtain ⟨κ, hκ, hκO⟩ := Metric.isOpen_iff.1 hO (e y) ⟨y, ⟨hy, mem_ball_self hε⟩, rfl⟩
  set W := e.source ∩ e ⁻¹' ball (e y) κ
  have hWo : IsOpen W := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hWim : e '' W = ball (e y) κ := by
    refine Subset.antisymm (by rintro _ ⟨w, hw, rfl⟩; exact hw.2) fun b hb ↦ ?_
    obtain ⟨o, ho, rfl⟩ := hκO hb
    exact ⟨o, ⟨ho.1, hb⟩, rfl⟩
  refine ⟨W, fun w hw ↦ ?_, ?_, ?_⟩
  · obtain ⟨o, ho, hoe⟩ := hκO hw.2
    rw [← e.injOn ho.1 hw.1 hoe]
    exact ho.2
  · have : ContractibleSpace (ball (e y) κ) :=
      (convex_ball (e y) κ).contractibleSpace ⟨e y, mem_ball_self hκ⟩
    exact (e.homeomorphOfImageSubsetSource inter_subset_left hWim).contractibleSpace
  · exact Metric.mem_nhds_iff.1 (hWo.mem_nhds ⟨hy, mem_ball_self hκ⟩)

/-- If every point of `X` (resp. `Y`) has arbitrarily small contractible neighbourhoods in `X`
(resp. `Y`), in metric form, then so does every point of `X × ℝ ∪ Y × {0}` in this subset of
`Y × ℝ`. -/
theorem exists_contractible_prod_union {Y : Type*} [MetricSpace Y] {X : Set Y}
    (hlocX : ∀ x ∈ X, ∀ ε > 0, ∃ W ⊆ X, W ⊆ ball x ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x ρ ∩ X ⊆ W)
    (hlocY : ∀ y : Y, ∀ ε > 0, ∃ W : Set Y, W ⊆ ball y ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball y ρ ⊆ W) :
    ∀ q ∈ X ×ˢ (univ : Set ℝ) ∪ (univ : Set Y) ×ˢ {0}, ∀ ε > 0,
      ∃ W ⊆ X ×ˢ (univ : Set ℝ) ∪ (univ : Set Y) ×ˢ {0}, W ⊆ ball q ε ∧ ContractibleSpace W ∧
        ∃ ρ > 0, ball q ρ ∩ (X ×ˢ (univ : Set ℝ) ∪ (univ : Set Y) ×ˢ {0}) ⊆ W := by
  rintro ⟨y, t⟩ hq ε hε
  by_cases ht : t = 0
  · subst ht
    obtain ⟨U, hUb, hUc, ρ, hρ, hρU⟩ := hlocY y ε hε
    refine ⟨(U ∩ X) ×ˢ ball 0 ε ∪ U ×ˢ {0}, ?_, ?_, ?_, min ρ ε, lt_min hρ hε, ?_⟩
    · rintro ⟨y', t'⟩ (⟨⟨_, hX'⟩, _⟩ | ⟨_, ht'⟩)
      · exact Or.inl ⟨hX', trivial⟩
      · exact Or.inr ⟨trivial, ht'⟩
    · rintro ⟨y', t'⟩ (⟨⟨hU, _⟩, ht'⟩ | ⟨hU, ht'⟩)
      · rw [← ball_prod_same]; exact ⟨hUb hU, ht'⟩
      · rw [← ball_prod_same]
        exact ⟨hUb hU, by rw [mem_singleton_iff.1 ht']; exact mem_ball_self hε⟩
    · have := hUc
      refine contractibleSpace_of_forall_segment_mem (U := U) 0
        (fun q hq ↦ hq.elim (fun h ↦ h.1.1) fun h ↦ h.1) (fun u hu ↦ Or.inr ⟨hu, rfl⟩) ?_
      rintro ⟨y', t'⟩ hq s hs
      rcases hq with ⟨⟨hU, hX'⟩, ht'⟩ | ⟨hU, ht'⟩
      · refine Or.inl ⟨⟨hU, hX'⟩, ?_⟩
        rw [mem_ball, Real.dist_eq] at ht' ⊢
        have : t' + s * (0 - t') - 0 = (1 - s) * (t' - 0) := by ring
        rw [this, abs_mul, abs_of_nonneg (by linarith [hs.2])]
        nlinarith [abs_nonneg (t' - 0), hs.1]
      · refine Or.inr ⟨hU, ?_⟩
        rw [mem_singleton_iff.1 ht']
        simp
    · rintro ⟨y', t'⟩ ⟨hb, hS'⟩
      rw [← ball_prod_same] at hb
      have hU : y' ∈ U := hρU (ball_subset_ball (min_le_left _ _) hb.1)
      rcases hS' with ⟨hX', _⟩ | ⟨_, ht'⟩
      · exact Or.inl ⟨⟨hU, hX'⟩, ball_subset_ball (min_le_right _ _) hb.2⟩
      · exact Or.inr ⟨hU, ht'⟩
  · have hy : y ∈ X := hq.elim (fun h ↦ h.1) fun h ↦ absurd (mem_singleton_iff.1 h.2) ht
    have ht0 : 0 < |t| := abs_pos.2 ht
    set ε' := min ε (|t| / 2)
    have hε' : 0 < ε' := lt_min hε (by positivity)
    obtain ⟨W, hWX, hWb, hWc, ρ, hρ, hρW⟩ := hlocX y hy ε' hε'
    refine ⟨W ×ˢ ball t ε', fun q hq ↦ Or.inl ⟨hWX hq.1, trivial⟩, ?_, ?_, min ρ ε',
      lt_min hρ hε', ?_⟩
    · rw [← ball_prod_same]
      exact prod_mono (hWb.trans (ball_subset_ball (min_le_left _ _)))
        (ball_subset_ball (min_le_left _ _))
    · have := hWc
      refine contractibleSpace_of_forall_segment_mem (U := W) t (fun q hq ↦ hq.1)
        (fun u hu ↦ ⟨hu, mem_ball_self hε'⟩) ?_
      rintro ⟨y', t'⟩ ⟨hW, ht'⟩ s hs
      refine ⟨hW, ?_⟩
      rw [mem_ball, Real.dist_eq] at ht' ⊢
      have : t' + s * (t - t') - t = (1 - s) * (t' - t) := by ring
      rw [this, abs_mul, abs_of_nonneg (by linarith [hs.2])]
      nlinarith [abs_nonneg (t' - t), hs.1]
    · rintro ⟨y', t'⟩ ⟨hb, hS'⟩
      rw [← ball_prod_same] at hb
      rcases hS' with ⟨hX', _⟩ | ⟨_, ht'⟩
      · exact ⟨hρW ⟨ball_subset_ball (min_le_left _ _) hb.1, hX'⟩,
          ball_subset_ball (min_le_right _ _) hb.2⟩
      · exfalso
        have h1 := hb.2
        rw [mem_ball, Real.dist_eq, mem_singleton_iff.1 ht', zero_sub, abs_neg] at h1
        have : ε' ≤ |t| / 2 := min_le_right _ _
        have : min ρ ε' ≤ ε' := min_le_right _ _
        linarith

/-- Every point of `Y × ℝ` lies in the source of an open partial homeomorphism to
`Fin (n + 1) → ℝ`, obtained from a chart of `Y` at its first coordinate. -/
theorem exists_chart_prod_real {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] (z : Y × ℝ) :
    ∃ e : OpenPartialHomeomorph (Y × ℝ) (Fin (n + 1) → ℝ), z ∈ e.source := by
  set Φ : EuclideanSpace ℝ (Fin n) × ℝ ≃ₜ (Fin (n + 1) → ℝ) :=
    ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.prodCongr
      (Homeomorph.funUnique (Fin 1) ℝ).symm).trans (Fin.appendHomeomorph n 1)
  refine ⟨((chartAt (EuclideanSpace ℝ (Fin n)) z.1).prod
    (OpenPartialHomeomorph.refl ℝ)).transHomeomorph Φ, ?_⟩
  rw [OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.prod_source]
  exact ⟨mem_chart_source _ _, by simp⟩

/-- **Proper neighbourhood deformations in a manifold with a proper metric**, fixing `X`: inside
every neighbourhood `M` of `X` there are a closed neighbourhood `N ⊆ M` of `X`, a proper
retraction `r : N → X` and a proper homotopy `G : N × [0, 1] → Y` with values in `M`, from the
inclusion to `r`, that fixes `X` at all times. -/
theorem exists_isClosed_isProperMap_retraction_homotopy_of_properSpace {n : ℕ} {Y : Type*}
    [MetricSpace Y] [ProperSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {X : Set Y}
    (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    {M : Set Y} (hM : M ∈ 𝓝ˢ X) :
    ∃ N : Set Y, IsClosed N ∧ X ⊆ interior N ∧ N ⊆ M ∧
      ∃ r : C(N, X), IsProperMap r ∧ (∀ y : N, (y : Y) ∈ X → (r y : Y) = y) ∧
        ∃ G : C(N × I, Y), IsProperMap G ∧ (∀ y, G (y, 0) = y) ∧ (∀ y, G (y, 1) = r y) ∧
          (∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) ∧ ∀ q, G q ∈ M := by
  set S : Set (Y × ℝ) := X ×ˢ univ ∪ univ ×ˢ {0}
  have hS : IsClosed S := (hX.prod isClosed_univ).union (isClosed_univ.prod isClosed_singleton)
  have hlocX : ∀ x ∈ X, ∀ ε > 0, ∃ W ⊆ X, W ⊆ ball x ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x ρ ∩ X ⊆ W := by
    simpa using exists_contractible_of_isEmbedding IsEmbedding.id hXc
  have hlocS := exists_contractible_prod_union hlocX
    fun y _ hε ↦ exists_contractible_subset_ball_of_chartedSpace
      (E := EuclideanSpace ℝ (Fin n)) y hε
  obtain ⟨U, hU, hSU, R, hRc, hRS, hRid⟩ :=
    NbhdRetract.exists_retraction_of_charts (m := n) exists_chart_prod_real hS hlocS
  obtain ⟨N', hN'c, hN'U, hSN', hN'K, hN'd⟩ :=
    exists_isClosed_subset_isCompact_inter_preimage hS hU hSU hRc hRS hRid
  have hRc' : ContinuousOn R (interior N') := hRc.mono (interior_subset.trans hN'U)
  have hXM : X ⊆ interior M := subset_interior_iff_mem_nhdsSet.2 hM
  -- the points whose unit segment behaves
  set Q : Set (Y × ℝ) := interior N' ∩ (fun q ↦ (q, R q)) ⁻¹'
    {w : (Y × ℝ) × (Y × ℝ) | w.2.1 ∈ interior M ∧ dist w.2.2 w.1.2 < 1 / 2}
  have hQ : IsOpen Q := (continuousOn_id.prodMk hRc').isOpen_inter_preimage isOpen_interior
    ((isOpen_interior.preimage (continuous_fst.comp continuous_snd)).inter
      (isOpen_lt ((continuous_snd.comp continuous_snd).dist (continuous_snd.comp continuous_fst))
        continuous_const))
  set O : Set Y := {y | ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ Q}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro y₀ hy₀
    exact isCompact_Icc.eventually_forall_of_forall_eventually (P := fun y t ↦ (y, t) ∈ Q)
      fun t ht ↦ hQ.mem_nhds (hy₀ t ht)
  have hXO : X ⊆ O := fun x hx t _ ↦ by
    have hq : (x, t) ∈ S := Or.inl ⟨hx, trivial⟩
    refine ⟨hSN' hq, ?_⟩
    change (R (x, t)).1 ∈ interior M ∧ dist (R (x, t)).2 t < 1 / 2
    rw [hRid _ hq]
    exact ⟨hXM hx, by rw [dist_self]; norm_num⟩
  obtain ⟨u, hu, hXu, hucl⟩ := normal_exists_closure_subset hX hO hXO
  set N := closure u
  have hNQ : ∀ y ∈ N, ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ Q := fun y hy ↦ hucl hy
  have hR0 : ∀ y : Y, R (y, 0) = (y, 0) := fun y ↦ hRid _ (Or.inr ⟨trivial, rfl⟩)
  have hNM : N ⊆ M := fun y hy ↦ by
    have := ((hNQ y hy 0 ⟨le_rfl, zero_le_one⟩).2.1)
    change (R (y, 0)).1 ∈ interior M at this
    rw [hR0] at this
    exact interior_subset this
  have hN'U' : ∀ y ∈ N, ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ U := fun y hy t ht ↦
    hN'U (interior_subset (hNQ y hy t ht).1)
  -- the retraction
  have hr1 : ∀ y ∈ N, (R (y, 1)).1 ∈ X := fun y hy ↦ by
    have hmem := hRS (hN'U' y hy 1 ⟨zero_le_one, le_rfl⟩)
    have hd : dist (R (y, 1)).2 1 < 1 / 2 := (hNQ y hy 1 ⟨zero_le_one, le_rfl⟩).2.2
    rcases hmem with ⟨hX', _⟩ | ⟨_, h0⟩
    · exact hX'
    · rw [mem_singleton_iff.1 h0, Real.dist_eq] at hd
      norm_num at hd
  have hint : ∀ y ∈ N, ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ interior N' := fun y hy t ht ↦
    (hNQ y hy t ht).1
  have hNcl : IsClosed N := isClosed_closure
  set r : C(N, X) := ⟨fun y : N ↦ ⟨(R ((y : Y), 1)).1, hr1 y.1 y.2⟩,
    (continuous_fst.comp (hRc'.comp_continuous (by fun_prop)
      fun y : N ↦ hint y.1 y.2 1 ⟨zero_le_one, le_rfl⟩)).subtype_mk _⟩
  set G : C(N × I, Y) := ⟨fun q ↦ (R ((q.1 : Y), (q.2 : ℝ))).1,
    continuous_fst.comp (hRc'.comp_continuous (by fun_prop) fun q ↦ hint q.1 q.1.2 q.2 q.2.2)⟩
  -- the compact sets controlling properness
  have hP : ∀ K : Set Y, IsCompact K → IsCompact (N' ∩ R ⁻¹' ((K ×ˢ Icc (-1) 2) ∩ S)) :=
    fun K hK ↦ hN'K _ ((hK.prod isCompact_Icc).inter_right hS) inter_subset_right
  have hGP : ∀ K : Set Y, ∀ y ∈ N, ∀ t ∈ Icc (0 : ℝ) 1, (R (y, t)).1 ∈ K →
      (y, t) ∈ N' ∩ R ⁻¹' ((K ×ˢ Icc (-1) 2) ∩ S) := by
    intro K y hy t ht hK
    have hN'q : (y, t) ∈ N' := interior_subset (hint y hy t ht)
    refine ⟨hN'q, ⟨hK, ?_⟩, hRS (hN'U hN'q)⟩
    have hd := hN'd _ hN'q
    rw [Prod.dist_eq] at hd
    have h2 := (le_max_right _ _).trans hd
    rw [Real.dist_eq, abs_le] at h2
    constructor <;> linarith [ht.1, ht.2, h2.1, h2.2]
  have hG : IsProperMap G := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨G.continuous, fun K hK ↦ ?_⟩
    have hΦ : IsClosedEmbedding fun q : N × I ↦ ((q.1 : Y), (q.2 : ℝ)) :=
      hNcl.isClosedEmbedding_subtypeVal.prodMap isClosed_Icc.isClosedEmbedding_subtypeVal
    exact (hΦ.isCompact_preimage (hP K hK)).of_isClosed_subset
      (hK.isClosed.preimage G.continuous) fun q hq ↦ hGP K q.1 q.1.2 q.2 q.2.2 hq
  have hr : IsProperMap r := by
    have hvr : IsProperMap (Subtype.val ∘ r) := by
      refine isProperMap_iff_isCompact_preimage.2 ⟨by fun_prop, fun K hK ↦ ?_⟩
      have h1 : IsClosedEmbedding fun y : Y ↦ (y, (1 : ℝ)) := by
        refine ⟨isEmbedding_graph continuous_const, ?_⟩
        have : range (fun y : Y ↦ (y, (1 : ℝ))) = univ ×ˢ {1} := by
          ext ⟨a, b⟩
          simp [eq_comm]
        rw [this]
        exact isClosed_univ.prod isClosed_singleton
      have hΨ : IsClosedEmbedding fun y : N ↦ ((y : Y), (1 : ℝ)) :=
        h1.comp hNcl.isClosedEmbedding_subtypeVal
      exact (hΨ.isCompact_preimage (hP K hK)).of_isClosed_subset
        (hK.isClosed.preimage (by fun_prop)) fun y hy ↦
          hGP K y y.2 1 ⟨zero_le_one, le_rfl⟩ hy
    exact isProperMap_of_comp_of_t2 r.continuous continuous_subtype_val hvr
  refine ⟨N, hNcl, fun x hx ↦ ?_, hNM, r, hr, fun y hy ↦ ?_, G, hG, fun y ↦ ?_, fun y ↦ rfl,
    fun y t hy ↦ ?_, fun q ↦ interior_subset (hNQ _ q.1.2 _ q.2.2).2.1⟩
  · exact interior_mono subset_closure (hu.interior_eq.symm ▸ hXu hx)
  · change (R ((y : Y), 1)).1 = y
    rw [hRid _ (Or.inl ⟨hy, trivial⟩)]
  · change (R ((y : Y), ((0 : I) : ℝ))).1 = y
    rw [Set.Icc.coe_zero, hR0]
  · change (R ((y : Y), (t : ℝ))).1 = y
    rw [hRid _ (Or.inl ⟨hy, trivial⟩)]

/-- **Proper neighbourhood deformations in a manifold with a proper metric**: a closed `X` in a
manifold `Y` with a proper metric, every point of `X` having a basis of open contractible
neighbourhoods in `X`, has arbitrarily small proper neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_of_properSpace {n : ℕ} {Y : Type*} [MetricSpace Y]
    [ProperSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {X : Set Y} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id) :
    HasProperNeighbourhoodDeformations X := fun _ hM ↦
  exists_isClosed_isProperMap_retraction_homotopy_of_properSpace (n := n) hX hXc hM

/-- **Proper neighbourhood deformations fixing `X` in a topological manifold** (Fulton, §19.1):
for `Y` a Hausdorff, second-countable topological `n`-manifold and `X ⊆ Y` closed, every point of
`X` having a basis of open contractible neighbourhoods in `X`, inside every neighbourhood `M` of
`X` there are a closed `N ⊆ M` with `X ⊆ interior N`, a proper retraction `r : N → X` and a
proper homotopy `G : N × [0, 1] → Y` with values in `M`, from the inclusion to `r`, fixing `X`. -/
theorem exists_isClosed_isProperMap_retraction_homotopy_of_chartedSpace {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {X : Set Y} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    {M : Set Y} (hM : M ∈ 𝓝ˢ X) :
    ∃ N : Set Y, IsClosed N ∧ X ⊆ interior N ∧ N ⊆ M ∧
      ∃ r : C(N, X), IsProperMap r ∧ (∀ y : N, (y : Y) ∈ X → (r y : Y) = y) ∧
        ∃ G : C(N × I, Y), IsProperMap G ∧ (∀ y, G (y, 0) = y) ∧ (∀ y, G (y, 1) = r y) ∧
          (∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) ∧ ∀ q, G q ∈ M := by
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) Y
  obtain ⟨m, hm, hp⟩ := exists_metricSpace_properSpace Y
  let : MetricSpace Y := m.replaceTopology hm
  have : ProperSpace Y := hp
  exact exists_isClosed_isProperMap_retraction_homotopy_of_properSpace (n := n) hX hXc hM

/-- **Proper neighbourhood deformations in a topological manifold** (Fulton, §19.1). Let `Y` be a
Hausdorff, second-countable topological `n`-manifold and `X ⊆ Y` closed, every point of `X`
having a basis of open contractible neighbourhoods in `X`. Then inside every neighbourhood `M` of
`X` there are a closed neighbourhood `N ⊆ M` of `X`, a proper retraction `r : N → X` and a proper
homotopy `N × [0, 1] → Y` with values in `M`, from the inclusion to `r`. -/
theorem hasProperNeighbourhoodDeformations_of_chartedSpace {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {X : Set Y} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id) :
    HasProperNeighbourhoodDeformations X := fun _ hM ↦
  exists_isClosed_isProperMap_retraction_homotopy_of_chartedSpace (n := n) hX hXc hM

/-- **A closed neighbourhood with a proper retraction in a topological manifold** (Fulton, §19.1;
[BT] 3.1.7): there is a closed `N ⊆ Y` with `X ⊆ interior N` and a proper retraction
`r : N → X`, for `Y` a Hausdorff, second-countable topological `n`-manifold instead of a space
with a closed imbedding in `ℝᴺ`. -/
theorem exists_isClosed_isProperMap_retraction_of_chartedSpace {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {X : Set Y} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id) :
    ∃ N : Set Y, IsClosed N ∧ X ⊆ interior N ∧
      ∃ r : C(N, X), IsProperMap r ∧ ∀ y : N, (y : Y) ∈ X → (r y : Y) = y :=
  (hasProperNeighbourhoodDeformations_of_chartedSpace (n := n) hX hXc).exists_retraction

end MMP
