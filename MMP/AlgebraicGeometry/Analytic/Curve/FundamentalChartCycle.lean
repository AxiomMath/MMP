module

public import MMP.AlgebraicGeometry.Analytic.Curve.FiniteMapRamifiedDiscs
public import MMP.AlgebraicGeometry.Analytic.Curve.FundamentalClassChartCriterion
public import MMP.AlgebraicGeometry.Analytic.Curve.RiemannSphereConeCycle
public import MMP.AlgebraicGeometry.Analytic.Curve.ProjectiveLineChartCycle
public import MMP.AlgebraicGeometry.Analytic.Curve.OneFormCupPositivityChartCycle

/-!
# Fundamental chart cycles of a smooth projective curve

Let `X` be a smooth projective complex curve and `f : X ⟶ ℙ¹` a finite morphism, a covering map
off a finite set `S ⊆ ℙ¹(ℂ)`. The transfer `f^! w` of a fine fundamental cycle `w` of flat chart
cones on `ℙ¹(ℂ)` whose triangles meet `S` only at their vertex `0` is a fine fundamental chart
cycle of `X` (`hasFundamentalChartCycle`).

A singular simplex `σ` of `ℙ¹(ℂ)` meeting `S` only at its vertex `0` has, through every point of
the fibre over any other point, exactly one lift: on the simplex minus its vertex `0`, which is
convex, lifts through the covering exist and are unique, and they extend continuously to the
vertex `0` since `f` is a closed map with finite fibres (`existsUnique_mem_simplexLifts`). So
lifts restrict bijectively to the lifts of faces (`bijOn_comp_face_of_apex`), and the transfer
of a cycle is a cycle.

## Main definitions

* `MMP.Analytic.ChartConeCellulation.puncturedSimplex`: a standard simplex minus its vertex `0`.

## Main results

* `MMP.Analytic.ChartConeCellulation.existsUnique_mem_simplexLifts`: unique lifts through a
  point, for simplices meeting the branch set only at their vertex `0`.
* `MMP.Analytic.ChartConeCellulation.bijOn_comp_face_of_apex`: restriction of such lifts to faces.
* `MMP.Analytic.ChartConeCellulation.hasFundamentalChartCycle`: fine fundamental chart cycles of
  a smooth projective curve.

## References

* [S. Donaldson, *Riemann Surfaces*], §8 (triangulation by pulling back along a meromorphic
  function).
-/

@[expose] public noncomputable section

open Set Finsupp Topology MMP.SingularChain
open MMP.Analytic MMP.Analytic.CurveCupPositivity

namespace MMP.Analytic.ChartConeCellulation

/-! ### The simplex minus its vertex `0` -/

section Punctured

variable {k : ℕ}

/-- The standard simplex `Δ^{k+1}` minus its vertex `0`, in the ambient space. -/
def puncturedSimplex (k : ℕ) : Set (Fin (k + 2) → ℝ) :=
  stdSimplex ℝ (Fin (k + 2)) ∩ {x | x 0 < 1}

/-- The punctured simplex is convex. -/
theorem convex_puncturedSimplex (k : ℕ) : Convex ℝ (puncturedSimplex k) :=
  (convex_stdSimplex ℝ _).inter
    (convex_halfSpace_lt (f := fun x : Fin (k + 2) → ℝ ↦ x 0) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 1)

/-- The vertex `1` lies in the punctured simplex. -/
theorem single_one_mem_puncturedSimplex (k : ℕ) :
    (Pi.single 1 1 : Fin (k + 2) → ℝ) ∈ puncturedSimplex k :=
  ⟨single_mem_stdSimplex ℝ 1, by simp⟩

/-- The punctured simplex is simply connected. -/
instance simplyConnectedSpace_puncturedSimplex (k : ℕ) :
    SimplyConnectedSpace (puncturedSimplex k) := by
  have := (convex_puncturedSimplex k).contractibleSpace ⟨_, single_one_mem_puncturedSimplex k⟩
  exact SimplyConnectedSpace.ofContractible _

/-- The punctured simplex is locally path-connected. -/
instance locallyPathConnectedSpace_puncturedSimplex (k : ℕ) :
    LocallyPathConnectedSpace (puncturedSimplex k) :=
  Convex.locallyPathConnectedSpace _ (convex_puncturedSimplex k)

/-- The inclusion of the punctured simplex into the simplex. -/
def puncturedIncl (k : ℕ) : C(puncturedSimplex k, stdSimplex ℝ (Fin (k + 2))) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The sum of two distinct coordinates of a point of the standard simplex is at most `1`. -/
theorem stdSimplex_apply_add_le_one {m : ℕ} (t : stdSimplex ℝ (Fin m)) {i j : Fin m}
    (hij : i ≠ j) : t i + t j ≤ 1 := by
  rw [← t.2.2, ← Finset.sum_pair hij]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ ↦ t.2.1 l

/-- A point of the standard simplex with coordinate `0` not less than `1` is the vertex `0`. -/
theorem eq_vertex_zero_of_apply_zero {t : stdSimplex ℝ (Fin (k + 2))} (ht : ¬ t 0 < 1) :
    t = stdSimplex.vertex 0 := by
  have h1 : t 0 = 1 := le_antisymm (stdSimplex.le_one t 0) (not_lt.1 ht)
  ext i
  rw [stdSimplex.vertex_coe]
  by_cases hi : i = 0
  · subst hi
    simp [h1]
  · rw [Pi.single_eq_of_ne hi]
    have := stdSimplex_apply_add_le_one t (Ne.symm hi)
    linarith [stdSimplex_apply_nonneg t i]

/-- Near the vertex `0` means: the coordinate `0` is close to `1`. -/
theorem exists_forall_mem_of_mem_nhds_vertex_zero {N : Set (stdSimplex ℝ (Fin (k + 2)))}
    (hN : N ∈ 𝓝 (stdSimplex.vertex 0)) : ∃ η > 0, ∀ t : stdSimplex ℝ (Fin (k + 2)),
      1 - η < t 0 → t ∈ N := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ε, hε, fun t ht ↦ hball ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq]
  refine lt_of_le_of_lt ((dist_pi_le_iff (by linarith [stdSimplex.le_one t 0])).2
    fun i ↦ ?_) (by linarith : 1 - t 0 < ε)
  have hv : ((stdSimplex.vertex 0 : stdSimplex ℝ (Fin (k + 2))) : Fin (k + 2) → ℝ) i =
      (Pi.single 0 1 : Fin (k + 2) → ℝ) i := congrFun (stdSimplex.vertex_coe 0) i
  change dist (t i) ((stdSimplex.vertex 0 : stdSimplex ℝ (Fin (k + 2))) i) ≤ 1 - t 0
  rw [hv, Real.dist_eq]
  by_cases hi : i = 0
  · subst hi
    simp only [Pi.single_eq_same]
    rw [abs_of_nonpos (by linarith [stdSimplex.le_one t 0])]
    linarith
  · rw [Pi.single_eq_of_ne hi, sub_zero, abs_of_nonneg (stdSimplex_apply_nonneg t i)]
    linarith [stdSimplex_apply_add_le_one t hi]

/-- Points of the punctured simplex arbitrarily close to the vertex `0`. -/
theorem exists_puncturedSimplex_apply_zero_gt {η : ℝ} (hη : 0 < η) :
    ∃ x : puncturedSimplex k, 1 - η < x.1 0 := by
  set a := min (η / 2) (1 / 2)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have ha1 : a ≤ 1 / 2 := min_le_right _ _
  set v : Fin (k + 2) → ℝ := (1 - a) • Pi.single 0 1 + a • Pi.single 1 1
  have hmem : v ∈ stdSimplex ℝ (Fin (k + 2)) :=
    convex_stdSimplex ℝ _ (single_mem_stdSimplex ℝ 0) (single_mem_stdSimplex ℝ 1)
      (by linarith) ha.le (by ring)
  have h0 : v 0 = 1 - a := by simp [v]
  exact ⟨⟨v, hmem, show v 0 < 1 by linarith⟩,
    show 1 - η < v 0 by linarith [min_le_left (η / 2) (1 / 2)]⟩

/-- The points of the punctured simplex with coordinate `0` greater than `c` form a preconnected
set. -/
theorem isPreconnected_setOf_puncturedSimplex_apply_zero_gt (c : ℝ) :
    IsPreconnected {x : puncturedSimplex k | c < x.1 0} := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  refine Convex.isPreconnected ?_
  have : Subtype.val '' {x : puncturedSimplex k | c < x.1 0} =
      puncturedSimplex k ∩ {x | c < x 0} := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ ⟨y.2, hy⟩, fun ⟨hx, hc⟩ ↦ ⟨⟨x, hx⟩, hc, rfl⟩⟩
  rw [this]
  exact (convex_puncturedSimplex k).inter
    (convex_halfSpace_gt (f := fun x : Fin (k + 2) → ℝ ↦ x 0) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ c)

/-- The simplex minus its vertex `0` is dense. -/
theorem dense_setOf_apply_zero_lt_one :
    Dense {t : stdSimplex ℝ (Fin (k + 2)) | t 0 < 1} := by
  refine dense_iff_closure_eq.2 (eq_univ_of_forall fun t ↦ ?_)
  by_cases ht : t 0 < 1
  · exact subset_closure ht
  · rw [eq_vertex_zero_of_apply_zero ht, mem_closure_iff_nhds]
    intro N hN
    obtain ⟨η, hη, hηN⟩ := exists_forall_mem_of_mem_nhds_vertex_zero hN
    obtain ⟨x, hx⟩ := exists_puncturedSimplex_apply_zero_gt (k := k) hη
    exact ⟨puncturedIncl k x, hηN _ hx, x.2.2⟩

/-- The coordinate `0` of a face. -/
theorem face_apply_zero {n : ℕ} (j : Fin (n + 2)) (t : stdSimplex ℝ (Fin (n + 1))) :
    (face n j t) 0 = if j = 0 then 0 else t 0 := by
  simp only [face, ContinuousMap.coe_mk, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  split_ifs with hj
  · subst hj
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    simp only [Finset.mem_filter] at hi
    exact absurd hi.2 (Fin.succAbove_ne 0 i)
  · rw [Finset.sum_eq_single 0]
    · intro i hi hi0
      simp only [Finset.mem_filter] at hi
      exact absurd ((Fin.succAbove_eq_zero_iff hj).1 hi.2) hi0
    · intro h
      exact absurd (by simp [Fin.succAbove_eq_zero_iff hj]) h

end Punctured

/-- A preconnected set sent into a union of pairwise disjoint open sets indexed by a set `F`
lands in one of them. -/
theorem exists_image_subset_of_isPreconnected {A Y ι : Type*} [TopologicalSpace A]
    [TopologicalSpace Y] {L : A → Y} {K : Set A} (hK : IsPreconnected (L '' K)) (hne : K.Nonempty)
    {F : Set ι} {W : ι → Set Y} (hWo : ∀ q, IsOpen (W q)) (hWd : F.PairwiseDisjoint W)
    (hcov : L '' K ⊆ ⋃ q ∈ F, W q) : ∃ q ∈ F, L '' K ⊆ W q := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨q₀, hq₀F, hq₀⟩ := mem_iUnion₂.1 (hcov ⟨x₀, hx₀, rfl⟩)
  have hdis : Disjoint (W q₀) (⋃ q ∈ F \ {q₀}, W q) := by
    rw [disjoint_iUnion₂_right]
    exact fun q hq ↦ hWd hq₀F hq.1 (Ne.symm hq.2)
  have hsub : L '' K ⊆ W q₀ ∪ ⋃ q ∈ F \ {q₀}, W q := by
    intro y hy
    obtain ⟨q, hqF, hq⟩ := mem_iUnion₂.1 (hcov hy)
    by_cases hqq : q = q₀
    · exact Or.inl (hqq ▸ hq)
    · exact Or.inr (mem_biUnion (x := q) ⟨hqF, hqq⟩ hq)
  exact ⟨q₀, hq₀F, hK.subset_left_of_subset_union (hWo q₀) (isOpen_biUnion fun q _ ↦ hWo q)
    hdis hsub ⟨L x₀, ⟨x₀, hx₀, rfl⟩, hq₀⟩⟩

/-! ### Lifts of simplices meeting the branch set only at the vertex `0` -/

section ApexLift

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] {p : Y → Z}
  {S : Set Z} {k : ℕ}

/-- **Lifts of the punctured simplex converge at the vertex `0`.** For a closed map `p` with a
finite fibre over `σ(0)`, a lift `L` of `σ` on the simplex minus its vertex `0` converges, at
the vertex `0`, to a point of the fibre. -/
theorem exists_forall_mem_of_isClosedMap (hcl : IsClosedMap p) (σ : Simplex Z (k + 1))
    (hfin : (p ⁻¹' {σ (stdSimplex.vertex 0)}).Finite)
    (L : C(puncturedSimplex k, Y)) (hL : ∀ x, p (L x) = σ (puncturedIncl k x)) :
    ∃ q, p q = σ (stdSimplex.vertex 0) ∧ ∀ O : Set Y, IsOpen O → q ∈ O →
      ∃ η > 0, ∀ x : puncturedSimplex k, 1 - η < x.1 0 → L x ∈ O := by
  set s := σ (stdSimplex.vertex 0)
  set F := p ⁻¹' {s}
  obtain ⟨U, hU, hUd⟩ := hfin.t2_separation
  have claim : ∀ W : Y → Set Y, (∀ q, IsOpen (W q)) → (∀ q ∈ F, q ∈ W q) →
      (∀ q, W q ⊆ U q) → ∃ q ∈ F, ∃ η > 0, ∀ x : puncturedSimplex k, 1 - η < x.1 0 →
        L x ∈ W q := by
    intro W hWo hWm hWU
    set K := (⋃ q ∈ F, W q)ᶜ
    have hK : IsClosed (p '' K) := hcl _ (isOpen_biUnion fun q _ ↦ hWo q).isClosed_compl
    have hsK : s ∉ p '' K := by
      rintro ⟨y, hyK, hys⟩
      exact hyK (mem_biUnion (x := y) hys (hWm y hys))
    have hN : σ ⁻¹' (p '' K)ᶜ ∈ 𝓝 (stdSimplex.vertex 0) :=
      σ.continuous.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hsK)
    obtain ⟨η, hη, hηN⟩ := exists_forall_mem_of_mem_nhds_vertex_zero hN
    set A := {x : puncturedSimplex k | 1 - η < x.1 0}
    have hAc : IsPreconnected (L '' A) :=
      (isPreconnected_setOf_puncturedSimplex_apply_zero_gt _).image _ L.continuous.continuousOn
    have hcov : L '' A ⊆ ⋃ q ∈ F, W q := by
      rintro _ ⟨x, hx, rfl⟩
      by_contra h
      exact hηN (puncturedIncl k x) hx ⟨L x, h, hL x⟩
    obtain ⟨q₀, hq₀F, hq₀⟩ := exists_image_subset_of_isPreconnected hAc
      (exists_puncturedSimplex_apply_zero_gt (k := k) hη) hWo
      (fun a ha b hb hab ↦ (hUd ha hb hab).mono (hWU a) (hWU b)) hcov
    exact ⟨q₀, hq₀F, η, hη, fun x hx ↦ hq₀ ⟨x, hx, rfl⟩⟩
  obtain ⟨q₀, hq₀F, η₀, hη₀, hq₀⟩ := claim U (fun q ↦ (hU q).2) (fun q _ ↦ (hU q).1)
    fun _ ↦ le_rfl
  refine ⟨q₀, hq₀F, fun O hO hq₀O ↦ ?_⟩
  classical
  obtain ⟨q₁, hq₁F, η₁, hη₁, hq₁⟩ := claim (fun q ↦ if q = q₀ then U q ∩ O else U q)
    (fun q ↦ by split_ifs; exacts [(hU q).2.inter hO, (hU q).2])
    (fun q _ ↦ by split_ifs with h; exacts [⟨(hU q).1, h ▸ hq₀O⟩, (hU q).1])
    (fun q ↦ by split_ifs; exacts [inter_subset_left, le_rfl])
  have hq : q₁ = q₀ := by
    by_contra hne
    obtain ⟨x, hx⟩ := exists_puncturedSimplex_apply_zero_gt (k := k) (lt_min hη₀ hη₁)
    have h1 := hq₀ x (lt_of_le_of_lt (by linarith [min_le_left η₀ η₁]) hx)
    have h2 := hq₁ x (lt_of_le_of_lt (by linarith [min_le_right η₀ η₁]) hx)
    rw [ite_eq_right hne] at h2
    exact (hUd hq₀F hq₁F (Ne.symm hne)).le_bot ⟨h1, h2⟩
  subst hq
  refine ⟨η₁, hη₁, fun x hx ↦ ?_⟩
  have := hq₁ x hx
  rw [ite_eq_left rfl] at this
  exact this.2

variable (hcov : IsCoveringMapOn p Sᶜ) (hcl : IsClosedMap p) (hfin : ∀ z, (p ⁻¹' {z}).Finite)

include hcov

omit hcov in
/-- A simplex meeting `S` only at its vertex `0` sends the punctured simplex into `Sᶜ`. -/
theorem mem_compl_of_apex' {σ : Simplex Z (k + 1)} (hσS : ∀ t, σ t ∈ S → t 0 = 1)
    (x : puncturedSimplex k) : σ (puncturedIncl k x) ∈ Sᶜ := fun h ↦
  (x.2.2.ne (hσS _ h)).elim

/-- **Uniqueness of lifts through a point**, for a simplex meeting `S` only at its vertex `0`. -/
theorem eq_of_mem_simplexLifts {σ : Simplex Z (k + 1)} (hσS : ∀ t, σ t ∈ S → t 0 = 1)
    {T₁ T₂ : Simplex Y (k + 1)} (h₁ : T₁ ∈ simplexLifts p σ) (h₂ : T₂ ∈ simplexLifts p σ)
    {t₀ : stdSimplex ℝ (Fin (k + 2))} (ht₀ : t₀ 0 < 1) (heq : T₁ t₀ = T₂ t₀) : T₁ = T₂ := by
  set a₀ : puncturedSimplex k := ⟨t₀.1, t₀.2, ht₀⟩
  have he : p (T₁ t₀) = (σ.comp (puncturedIncl k)) a₀ := congrFun h₁ t₀
  obtain ⟨F, -, hF⟩ := hcov.existsUnique_continuousMap_lifts (σ.comp (puncturedIncl k)) he
    (mem_compl_of_apex' hσS)
  have hlift : ∀ T ∈ simplexLifts p σ, T t₀ = T₁ t₀ → T.comp (puncturedIncl k) = F :=
    fun T hT hTt ↦ hF _ ⟨hTt, funext fun x ↦ congrFun hT _⟩
  have hc : T₁.comp (puncturedIncl k) = T₂.comp (puncturedIncl k) :=
    (hlift T₁ h₁ rfl).trans (hlift T₂ h₂ heq.symm).symm
  have := Continuous.ext_on (dense_setOf_apply_zero_lt_one (k := k)) T₁.continuous T₂.continuous
    fun t ht ↦ congrArg (fun f : C(puncturedSimplex k, Y) ↦ f ⟨t.1, t.2, ht⟩) hc
  exact ContinuousMap.ext (congrFun this)

include hcl hfin in
/-- **Existence of lifts through a point**, for a simplex meeting `S` only at its vertex `0`. -/
theorem exists_mem_simplexLifts {σ : Simplex Z (k + 1)} (hσS : ∀ t, σ t ∈ S → t 0 = 1)
    {t₀ : stdSimplex ℝ (Fin (k + 2))} (ht₀ : t₀ 0 < 1) {y : Y} (hy : p y = σ t₀) :
    ∃ T' ∈ simplexLifts p σ, T' t₀ = y := by
  classical
  set a₀ : puncturedSimplex k := ⟨t₀.1, t₀.2, ht₀⟩
  obtain ⟨L, ⟨hL0, hLp⟩, -⟩ := hcov.existsUnique_continuousMap_lifts (σ.comp (puncturedIncl k))
    (a₀ := a₀) hy (mem_compl_of_apex' hσS)
  have hL : ∀ x, p (L x) = σ (puncturedIncl k x) := fun x ↦ congrFun hLp x
  obtain ⟨q, hq, hqL⟩ := exists_forall_mem_of_isClosedMap hcl σ (hfin _) L hL
  let T : stdSimplex ℝ (Fin (k + 2)) → Y := fun t ↦ if h : t 0 < 1 then L ⟨t.1, t.2, h⟩ else q
  have hcont : Continuous T := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    by_cases ht : t 0 < 1
    · have hO : IsOpen {t : stdSimplex ℝ (Fin (k + 2)) | t 0 < 1} :=
        isOpen_lt (stdSimplex_continuous_apply 0) continuous_const
      refine (ContinuousOn.continuousAt ?_ (hO.mem_nhds ht))
      rw [continuousOn_iff_continuous_domRestrict]
      have : domRestrict {t : stdSimplex ℝ (Fin (k + 2)) | t 0 < 1} T =
          fun u ↦ L ⟨u.1.1, u.1.2, u.2⟩ := by
        funext u
        exact dite_eq_left u.2
      exact (L.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        _)).congr fun u ↦ (congrFun this u).symm
    · rw [eq_vertex_zero_of_apply_zero ht]
      have hT0 : T (stdSimplex.vertex 0) = q := by
        simp only [T, stdSimplex.vertex_coe, Pi.single_eq_same, lt_irrefl, dite_eq_right,
          not_false_eq_true]
      rw [ContinuousAt, hT0]
      refine (nhds_basis_opens q).tendsto_right_iff.2 fun O ⟨hqO, hO⟩ ↦ ?_
      obtain ⟨η, hη, hηO⟩ := hqL O hO hqO
      have hN : {t : stdSimplex ℝ (Fin (k + 2)) | 1 - η < t 0} ∈ 𝓝 (stdSimplex.vertex 0) :=
        (isOpen_lt continuous_const (stdSimplex_continuous_apply 0)).mem_nhds (by simp [hη])
      filter_upwards [hN] with t ht
      by_cases h : t 0 < 1
      · simpa only [T, dite_eq_left h] using hηO _ ht
      · simpa only [T, dite_eq_right h] using hqO
  refine ⟨⟨T, hcont⟩, ?_, ?_⟩
  · funext t
    change p (T t) = σ t
    by_cases h : t 0 < 1
    · simp only [T, dite_eq_left h]
      exact hL _
    · simp only [T, dite_eq_right h]
      rw [hq, ← eq_vertex_zero_of_apply_zero h]
  · change T t₀ = y
    simpa only [T, dite_eq_left ht₀] using hL0

include hcl hfin in
/-- **Unique lifts through a point**, for a simplex meeting `S` only at its vertex `0`. -/
theorem existsUnique_mem_simplexLifts {σ : Simplex Z (k + 1)} (hσS : ∀ t, σ t ∈ S → t 0 = 1)
    {t₀ : stdSimplex ℝ (Fin (k + 2))} (ht₀ : t₀ 0 < 1) {y : Y} (hy : p y = σ t₀) :
    ∃! T', T' ∈ simplexLifts p σ ∧ T' t₀ = y := by
  obtain ⟨T', hT', hT'y⟩ := exists_mem_simplexLifts hcov hcl hfin hσS ht₀ hy
  exact ⟨T', ⟨hT', hT'y⟩, fun T hT ↦
    eq_of_mem_simplexLifts hcov hσS hT.1 hT' ht₀ (hT.2.trans hT'y.symm)⟩

include hfin in
/-- The lifts of a simplex meeting `S` only at its vertex `0` are finite. -/
theorem finite_simplexLifts_of_apex {σ : Simplex Z (k + 1)} (hσS : ∀ t, σ t ∈ S → t 0 = 1) :
    (simplexLifts p σ).Finite := by
  set t₁ : stdSimplex ℝ (Fin (k + 2)) := stdSimplex.vertex 1
  have ht₁ : t₁ 0 < 1 := by simp [t₁]
  refine Set.Finite.of_finite_image ((hfin (σ t₁)).subset ?_) fun T₁ h₁ T₂ h₂ h ↦
    eq_of_mem_simplexLifts hcov hσS h₁ h₂ ht₁ h
  rintro _ ⟨T, hT, rfl⟩
  exact congrFun hT t₁

include hcl hfin in
/-- **Lifts restrict bijectively to the lifts of faces**, for a simplex meeting `S` only at its
vertex `0`. -/
theorem bijOn_comp_face_of_apex {σ : Simplex Z (k + 2)} (hσS : ∀ t, σ t ∈ S → t 0 = 1)
    (j : Fin (k + 3)) :
    BijOn (fun T' : Simplex Y (k + 2) ↦ T'.comp (face (k + 1) j)) (simplexLifts p σ)
      (simplexLifts p (σ.comp (face (k + 1) j))) := by
  have hfS : ∀ t, σ.comp (face (k + 1) j) t ∈ S → t 0 = 1 := fun t ht ↦ by
    have := hσS _ ht
    rw [face_apply_zero] at this
    split_ifs at this
    · exact absurd this zero_ne_one
    · exact this
  set t₁ : stdSimplex ℝ (Fin (k + 2)) := stdSimplex.vertex 1
  have ht₁ : t₁ 0 < 1 := by simp [t₁]
  have hft₁ : (face (k + 1) j t₁) 0 < 1 := by
    rw [face_apply_zero]; split_ifs <;> simp [t₁]
  refine ⟨mapsTo_comp_simplexLifts p σ j, fun T₁ h₁ T₂ h₂ h ↦ ?_, fun ε hε ↦ ?_⟩
  · exact eq_of_mem_simplexLifts hcov hσS h₁ h₂ hft₁
      (congrArg (fun f : Simplex Y (k + 1) ↦ f t₁) h)
  · obtain ⟨T', hT', hT't⟩ := exists_mem_simplexLifts hcov hcl hfin hσS hft₁
      (congrFun hε t₁)
    exact ⟨T', hT', eq_of_mem_simplexLifts hcov hfS (mapsTo_comp_simplexLifts p σ j hT') hε ht₁
      hT't⟩

end ApexLift

/-! ### Small preimages -/

section Small

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] {p : Y → Z}

/-- **Preimages of small sets are small.** For a closed map `p` with finite fibres and open
neighbourhoods `N q` of the points of `Y`, every point `y` has an open neighbourhood `B` such
that every nonempty preconnected subset of `p⁻¹ B` lies in `N q` for some `q` over `y`. -/
theorem exists_isOpen_forall_isPreconnected_subset (hcl : IsClosedMap p)
    (hfin : ∀ z, (p ⁻¹' {z}).Finite) (N : Y → Set Y) (hNo : ∀ q, IsOpen (N q))
    (hNm : ∀ q, q ∈ N q) (y : Z) :
    ∃ B : Set Z, IsOpen B ∧ y ∈ B ∧ ∀ K ⊆ p ⁻¹' B, IsPreconnected K → K.Nonempty →
      ∃ q, p q = y ∧ K ⊆ N q := by
  obtain ⟨U, hU, hUd⟩ := (hfin y).t2_separation
  set F := p ⁻¹' {y}
  set V : Y → Set Y := fun q ↦ U q ∩ N q
  have hVo : ∀ q, IsOpen (V q) := fun q ↦ (hU q).2.inter (hNo q)
  set K' := (⋃ q ∈ F, V q)ᶜ
  have hK' : IsClosed (p '' K') := hcl _ (isOpen_biUnion fun q _ ↦ hVo q).isClosed_compl
  have hy : y ∉ p '' K' := by
    rintro ⟨x, hx, hxy⟩
    exact hx (mem_biUnion (x := x) hxy ⟨(hU x).1, hNm x⟩)
  refine ⟨(p '' K')ᶜ, hK'.isOpen_compl, hy, fun K hK hKc ⟨x₀, hx₀⟩ ↦ ?_⟩
  have hcov : K ⊆ ⋃ q ∈ F, V q := fun x hx ↦ by
    by_contra h
    exact hK hx ⟨x, h, rfl⟩
  obtain ⟨q₀, hq₀F, hq₀⟩ := mem_iUnion₂.1 (hcov hx₀)
  have hdis : Disjoint (V q₀) (⋃ q ∈ F \ {q₀}, V q) := by
    rw [disjoint_iUnion₂_right]
    exact fun q hq ↦ (hUd hq₀F hq.1 (Ne.symm hq.2)).mono inter_subset_left inter_subset_left
  have hsub : K ⊆ V q₀ ∪ ⋃ q ∈ F \ {q₀}, V q := by
    intro x hx
    obtain ⟨q, hqF, hq⟩ := mem_iUnion₂.1 (hcov hx)
    by_cases hqq : q = q₀
    · exact Or.inl (hqq ▸ hq)
    · exact Or.inr (mem_biUnion (x := q) ⟨hqF, hqq⟩ hq)
  have := hKc.subset_left_of_subset_union (hVo q₀) (isOpen_biUnion fun q _ ↦ hVo q) hdis hsub
    ⟨x₀, hx₀, hq₀⟩
  exact ⟨q₀, hq₀F, this.trans inter_subset_right⟩

end Small

/-! ### Coefficients of a transfer -/

section TransferApply

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {R : Type*} [CommRing R]

/-- A simplex `T'` is a lift of `σ` exactly when `pC.comp T' = σ`. -/
theorem mem_simplexLifts_iff (pC : C(Y, Z)) {k : ℕ} {σ : Simplex Z k} {T' : Simplex Y k} :
    T' ∈ simplexLifts pC σ ↔ pC.comp T' = σ :=
  ⟨fun h ↦ ContinuousMap.ext (congrFun h), fun h ↦ by rw [← h]; rfl⟩

/-- **The coefficient of a lift in a transfer** is the coefficient of its image. -/
theorem transfer_apply (pC : C(Y, Z)) {k : ℕ} (w : Chain R Z k)
    (hfin : ∀ σ ∈ w.support, (simplexLifts pC σ).Finite) (T' : Simplex Y k) :
    transfer R pC k w T' = w (pC.comp T') := by
  classical
  have key : ∀ σ ∈ w.support, transferSimplex R pC σ T' = if pC.comp T' = σ then 1 else 0 := by
    intro σ hσ
    rw [transferSimplex, dite_eq_left (hfin σ hσ), Finsupp.finsetSum_apply]
    simp_rw [single_apply]
    rw [Finset.sum_ite_eq']
    simp only [Set.Finite.mem_toFinset, mem_simplexLifts_iff]
  rw [transfer, linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun σ hσ ↦ by rw [key σ hσ]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

/-- The image of a simplex in the support of a transfer lies in the support of the chain. -/
theorem comp_mem_support_of_mem_support_transfer (pC : C(Y, Z)) {k : ℕ} {w : Chain R Z k}
    (hfin : ∀ σ ∈ w.support, (simplexLifts pC σ).Finite) {T' : Simplex Y k}
    (hT' : T' ∈ (transfer R pC k w).support) : pC.comp T' ∈ w.support := by
  rw [Finsupp.mem_support_iff, transfer_apply pC w hfin] at hT'
  exact Finsupp.mem_support_iff.2 hT'

end TransferApply

/-! ### Readings of lifts -/

/-- On the unit square, the coordinate `0` of `squareCollapse q` is `1 - q.1`. -/
theorem squareCollapse_apply_zero {q : ℝ × ℝ} (hq : q ∈ unitSquare) :
    squareCollapse q 0 = 1 - q.1 := by
  change 1 - (Set.projIcc (0 : ℝ) 1 zero_le_one q.1 : ℝ) = _
  rw [coe_projIcc_of_mem hq.1]

/-- On the unit square, `squareCollapse` sends the edge `q.1 = 0` to the vertex `0`. -/
theorem squareCollapse_eq_vertex_zero {q : ℝ × ℝ} (hq : q ∈ unitSquare) (h0 : q.1 = 0) :
    squareCollapse q = stdSimplex.vertex 0 :=
  eq_vertex_zero_of_apply_zero (k := 1) (by rw [squareCollapse_apply_zero hq, h0]; norm_num)

/-- An open neighbourhood of the unit square contains a box `(-δ, 1 + δ)²`. -/
theorem exists_box_subset {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hsq : unitSquare ⊆ O) :
    ∃ δ > 0, δ < 1 ∧ Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ) ⊆ O := by
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_Icc.prod isCompact_Icc).exists_thickening_subset_open hO hsq
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), by linarith [min_le_right δ (1 / 2)], ?_⟩
  rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hm := min_le_left δ (1 / 2)
  refine hδO (Metric.mem_thickening_iff.2 ⟨(Set.projIcc (0 : ℝ) 1 zero_le_one x.1,
    Set.projIcc (0 : ℝ) 1 zero_le_one x.2), ⟨(Set.projIcc (0 : ℝ) 1 zero_le_one x.1).2,
      (Set.projIcc (0 : ℝ) 1 zero_le_one x.2).2⟩, ?_⟩)
  have key : ∀ t : ℝ, -min δ (1 / 2) < t → t < 1 + min δ (1 / 2) →
      dist t (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) < δ := by
    intro t ht1 ht2
    rw [Real.dist_eq]
    rcases le_or_gt t 0 with h | h
    · rw [Set.projIcc_of_le_left _ h, sub_zero, abs_of_nonpos h]
      linarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [Set.projIcc_of_mem _ ⟨h.le, h'⟩]
        simp [hδ]
      · rw [Set.projIcc_of_right_le _ h'.le, abs_of_pos (by linarith)]
        linarith
  rw [Prod.dist_eq]
  exact max_lt (key _ h1 h2) (key _ h3 h4)

section ConvexLift

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z} {S : Set Z}

/-- Lifts through a covering of a map on a convex set of the plane. -/
theorem exists_liftOn_convex (hcov : IsCoveringMapOn p Sᶜ) {B : Set (ℝ × ℝ)}
    (hB : Convex ℝ B) {a₀ : ℝ × ℝ} (ha₀ : a₀ ∈ B) {φ : ℝ × ℝ → Z} (hφ : ContinuousOn φ B)
    (hφS : MapsTo φ B Sᶜ) {e₀ : Y} (he : p e₀ = φ a₀) :
    ∃ L : ℝ × ℝ → Y, ContinuousOn L B ∧ (∀ x ∈ B, p (L x) = φ x) ∧ L a₀ = e₀ := by
  classical
  have := (hB.contractibleSpace ⟨a₀, ha₀⟩)
  have : SimplyConnectedSpace B := SimplyConnectedSpace.ofContractible _
  have : LocallyPathConnectedSpace B := Convex.locallyPathConnectedSpace _ hB
  obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    ⟨fun x : B ↦ φ x, continuousOn_iff_continuous_domRestrict.1 hφ⟩ (a₀ := ⟨a₀, ha₀⟩) he
    fun x ↦ hφS x.2
  refine ⟨fun x ↦ if h : x ∈ B then F ⟨x, h⟩ else e₀, ?_, fun x hx ↦ ?_, by simp [ha₀, hF0]⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine F.continuous.congr fun x ↦ ?_
    simp [x.2]
  · simp only [dite_eq_left hx]
    exact congrFun hFp ⟨x, hx⟩

/-- Lifts through a covering of a map on a convex set agreeing at a point agree. -/
theorem eqOn_liftOn_convex (hcov : IsCoveringMapOn p Sᶜ) {B : Set (ℝ × ℝ)}
    (hB : Convex ℝ B) {a₀ : ℝ × ℝ} (ha₀ : a₀ ∈ B) {φ : ℝ × ℝ → Z} (hφ : ContinuousOn φ B)
    (hφS : MapsTo φ B Sᶜ) {L₁ L₂ : ℝ × ℝ → Y} (h₁ : ContinuousOn L₁ B) (h₂ : ContinuousOn L₂ B)
    (hp₁ : ∀ x ∈ B, p (L₁ x) = φ x) (hp₂ : ∀ x ∈ B, p (L₂ x) = φ x) (h0 : L₁ a₀ = L₂ a₀) :
    EqOn L₁ L₂ B := by
  have := (hB.contractibleSpace ⟨a₀, ha₀⟩)
  have : SimplyConnectedSpace B := SimplyConnectedSpace.ofContractible _
  have : LocallyPathConnectedSpace B := Convex.locallyPathConnectedSpace _ hB
  have he : p (L₁ a₀) = (⟨fun x : B ↦ φ x, continuousOn_iff_continuous_domRestrict.1 hφ⟩ :
      C(B, Z)) ⟨a₀, ha₀⟩ := hp₁ a₀ ha₀
  obtain ⟨F, -, hF⟩ := hcov.existsUnique_continuousMap_lifts _ he fun x ↦ hφS x.2
  have k₁ := hF ⟨fun x : B ↦ L₁ x, continuousOn_iff_continuous_domRestrict.1 h₁⟩
    ⟨rfl, funext fun x ↦ hp₁ x x.2⟩
  have k₂ := hF ⟨fun x : B ↦ L₂ x, continuousOn_iff_continuous_domRestrict.1 h₂⟩
    ⟨h0.symm, funext fun x ↦ hp₂ x x.2⟩
  intro x hx
  exact congrArg (fun G : C(B, Y) ↦ G ⟨x, hx⟩) (k₁.trans k₂.symm)

end ConvexLift

section Reading

open CategoryTheory AlgebraicGeometry MMP MMP.Analytic.ComplexPoints
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

/-- **A lift of a chart triangle on a thickened square.** In the setting of
`exists_reading_mem_simplexLifts`, `σ` read on an open box `(-δ, 1 + δ)²` inside `U` lifts to a
map `L` continuous on the box and equal to the lift `T'` on the square. Where `L` meets the
preimage of `S`, the reading is a flat cone from that point, the point lies on `x ≤ 0`, and the
base curve avoids the apex on `(-δ, 1 + δ)`.

Off `x ≤ 0` (or everywhere, if `σ` avoids `S`) the box maps into `Sᶜ` for `δ` small, and the lift
through the covering on that convex set extends continuously to `x ≤ 0` by the value at the
vertex `0`, as in `exists_forall_mem_of_isClosedMap`. -/
theorem exists_continuousOn_lift_box [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    [IsSeparated (X ↘ Spec (.of ℂ))]
    (f : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ 1))
    (hf : f ≫ projToSpecCoeff ℂ 1 = X ↘ Spec (.of ℂ)) [IsFinite f]
    {S : Set (ComplexPoints (projToSpecCoeff ℂ 1))} (hS : S.Finite)
    (hcov : IsCoveringMapOn (realize f hf) Sᶜ)
    (σ : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1))
    (c' : EtaleCoordinateChart (projToSpecCoeff ℂ 1) 1)
    (g : ℝ × ℝ → (Fin 1 → ℂ)) (U : Set (ℝ × ℝ)) (hUo : IsOpen U) (hsq : unitSquare ⊆ U)
    (hg : ContDiffOn ℝ 2 g U) (hgT : MapsTo g U c'.toOpenPartialHomeomorph.target)
    (hσ : ∀ q ∈ unitSquare, σ (squareCollapse q) = c'.toOpenPartialHomeomorph.symm (g q))
    (hσS : ∀ t, σ t ∈ S → t 0 = 1)
    (hcone : ∀ s ∈ S, s ∈ range σ → ∃ γ : ℝ → Fin 1 → ℂ, ContDiff ℝ 2 γ ∧
      g = CurveCupPositivity.coneMap coneProfile (c'.toOpenPartialHomeomorph s) γ)
    (T' : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1))
    (hT' : T' ∈ simplexLifts (realize f hf) σ) :
    ∃ δ > 0, Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ) ⊆ U ∧
      ∃ L : ℝ × ℝ → ComplexPoints (X ↘ Spec (.of ℂ)),
        ContinuousOn L (Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ)) ∧
        (∀ x ∈ Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ),
          realize f hf (L x) = c'.toOpenPartialHomeomorph.symm (g x)) ∧
        (∀ q ∈ unitSquare, L q = T' (squareCollapse q)) ∧
        ∀ x ∈ Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ),
          realize f hf (L x) ∈ S → x.1 ≤ 0 ∧
            ∃ γ : ℝ → Fin 1 → ℂ, ContDiff ℝ 2 γ ∧ g = CurveCupPositivity.coneMap coneProfile
              (c'.toOpenPartialHomeomorph (realize f hf (L x))) γ ∧
              ∀ y ∈ Ioo (-δ) (1 + δ), γ y ≠
                c'.toOpenPartialHomeomorph (realize f hf (L x)) := by
  classical
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ 1⟩
  haveI : IsProper (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ 1
  haveI : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  set p := realize f hf
  have hT2X : T2Space (ComplexPoints (X ↘ Spec (.of ℂ))) := t2Space_complexPoints
  have hT2P : T2Space (ComplexPoints (projToSpecCoeff ℂ 1)) :=
    t2Space_complexPoints
  have hcl : IsClosedMap p := isClosedMap_realize_of_isProper f
  have : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  have hfin : ∀ s, (p ⁻¹' {s}).Finite := finite_realize_preimage_singleton f
  set e' := c'.toOpenPartialHomeomorph
  set φ : ℝ × ℝ → ComplexPoints (projToSpecCoeff ℂ 1) := fun x ↦ e'.symm (g x)
  have hφc : ContinuousOn φ U := e'.continuousOn_symm.comp hg.continuousOn hgT
  have hSc : IsClosed S := hS.isClosed
  have hTsq : ∀ q ∈ unitSquare, p (T' (squareCollapse q)) = φ q := fun q hq ↦
    (congrFun hT' _).trans (hσ q hq)
  have hTc : ContinuousOn (fun q ↦ T' (squareCollapse q)) unitSquare :=
    (T'.continuous.comp continuous_squareCollapse).continuousOn
  set v₀ : stdSimplex ℝ (Fin (1 + 2)) := stdSimplex.vertex 0
  have hsqv : ∀ q ∈ unitSquare, σ (squareCollapse q) ∈ S → squareCollapse q = v₀ := fun q hq h ↦
    eq_vertex_zero_of_apply_zero (k := 1) (by rw [hσS _ h]; exact lt_irrefl 1)
  set a₀ : ℝ × ℝ := (1 / 2, 1 / 2)
  have ha₀ : a₀ ∈ unitSquare := ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  have hsqconv : Convex ℝ unitSquare := (convex_Icc _ _).prod (convex_Icc _ _)
  have hboxconv : ∀ δ : ℝ, Convex ℝ (Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ)) := fun δ ↦
    (convex_Ioo _ _).prod (convex_Ioo _ _)
  have hsqbox : ∀ δ > 0, unitSquare ⊆ Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ) := fun δ hδ q hq ↦
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  by_cases hs : σ v₀ ∈ S
  swap
  · -- `σ` avoids `S`
    have hall : ∀ q ∈ unitSquare, φ q ∈ Sᶜ := fun q hq h ↦ by
      have h' : σ (squareCollapse q) ∈ S := by rwa [hσ q hq]
      exact hs (hsqv q hq h' ▸ h')
    obtain ⟨δ, hδ, -, hbox⟩ := exists_box_subset (hφc.isOpen_inter_preimage hUo hSc.isOpen_compl)
      fun q hq ↦ ⟨hsq hq, hall q hq⟩
    have hboxU : Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ) ⊆ U := fun x hx ↦ (hbox hx).1
    obtain ⟨L, hLc, hLp, hL0⟩ := exists_liftOn_convex hcov (hboxconv δ) (hsqbox δ hδ ha₀)
      (hφc.mono hboxU) (fun x hx ↦ (hbox hx).2) (hTsq a₀ ha₀)
    have heq := eqOn_liftOn_convex hcov hsqconv ha₀ (hφc.mono hsq) (fun q hq ↦ hall q hq)
      (hLc.mono (hsqbox δ hδ)) hTc (fun q hq ↦ hLp q (hsqbox δ hδ hq)) hTsq hL0
    exact ⟨δ, hδ, hboxU, L, hLc, hLp, fun q hq ↦ heq hq, fun x hx h ↦
      absurd (by rw [← hLp x hx]; exact h) ((hbox hx).2)⟩
  -- `σ` meets `S` at its vertex `0`
  set s := σ v₀
  obtain ⟨γ, hγ, hgγ⟩ := hcone s hs ⟨v₀, rfl⟩
  set P := e' s
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ unitSquare := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  have hs00 : φ (0, 0) = s := by
    change e'.symm (g (0, 0)) = s
    rw [← hσ _ h00, squareCollapse_eq_vertex_zero h00 rfl]
  have hssrc : s ∈ e'.source := hs00 ▸ e'.map_target (hgT (hsq h00))
  have hφs : ∀ x ∈ U, φ x = s ↔ g x = P := fun x hx ↦
    ⟨fun h ↦ by rw [← e'.right_inv (hgT hx)]; exact congrArg e' h,
      fun h ↦ by simp only [φ, h, P, e'.left_inv hssrc]⟩
  have hgx : ∀ x : ℝ × ℝ, g x = P + coneProfile x.1 • (γ x.2 - P) := fun x ↦ by
    rw [hgγ]; rfl
  have hγne : ∀ y ∈ Icc (0 : ℝ) 1, γ y ≠ P := fun y hy h ↦ by
    have hq : ((1 : ℝ), y) ∈ unitSquare := ⟨⟨zero_le_one, le_rfl⟩, hy⟩
    have h1 : φ (1, y) = s := (hφs _ (hsq hq)).2 (by rw [hgx, h, sub_self, smul_zero, add_zero])
    have h2 := hσS _ (by rw [hσ _ hq]; change φ (1, y) ∈ S; rw [h1]; exact hs)
    rw [squareCollapse_apply_zero hq] at h2
    norm_num at h2
  have hS' : ∀ q ∈ unitSquare, φ q ∉ S \ {s} := fun q hq h ↦ by
    have h' : σ (squareCollapse q) ∈ S := by rw [hσ q hq]; exact h.1
    exact h.2 (by change e'.symm (g q) = s; rw [← hσ q hq, hsqv q hq h'])
  have hOo : IsOpen (U ∩ φ ⁻¹' (S \ {s})ᶜ ∩ {x | γ x.2 ≠ P}) :=
    (hφc.isOpen_inter_preimage hUo (hS.subset sdiff_subset).isClosed.isOpen_compl).inter
      (isClosed_singleton.isOpen_compl.preimage (hγ.continuous.comp continuous_snd))
  obtain ⟨δ, hδ, hδ1, hbox⟩ := exists_box_subset hOo fun q hq ↦
    ⟨⟨hsq hq, hS' q hq⟩, hγne q.2 hq.2⟩
  set box := Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ)
  have hboxU : box ⊆ U := fun x hx ↦ (hbox hx).1.1
  set boxP := box ∩ {x : ℝ × ℝ | 0 < x.1}
  have hpos_conv : Convex ℝ {x : ℝ × ℝ | 0 < x.1} :=
    convex_halfSpace_gt (f := Prod.fst) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 0
  have hboxP : Convex ℝ boxP := (hboxconv δ).inter hpos_conv
  have ha₀P : a₀ ∈ boxP := ⟨hsqbox δ hδ ha₀, by norm_num [a₀]⟩
  have hφP : MapsTo φ boxP Sᶜ := fun x hx h ↦ by
    have hxO := hbox hx.1
    have hxs : φ x = s := by
      by_contra hne
      exact hxO.1.2 ⟨h, hne⟩
    have := (hφs x (hboxU hx.1)).1 hxs
    rw [hgx, add_eq_left, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact (coneProfile_pos hx.2).ne' h0
    · exact hxO.2 (sub_eq_zero.1 h0)
  obtain ⟨L₀, hL₀c, hL₀p, hL₀a⟩ := exists_liftOn_convex hcov hboxP ha₀P
    (hφc.mono fun x hx ↦ hboxU hx.1) hφP (hTsq a₀ ha₀)
  set sqP := unitSquare ∩ {x : ℝ × ℝ | 0 < x.1}
  have hsqPbox : sqP ⊆ boxP := fun x hx ↦ ⟨hsqbox δ hδ hx.1, hx.2⟩
  have heqP : EqOn L₀ (fun q ↦ T' (squareCollapse q)) sqP :=
    eqOn_liftOn_convex hcov (hsqconv.inter hpos_conv) ⟨ha₀, by norm_num [a₀]⟩
      (hφc.mono fun x hx ↦ hsq hx.1) (fun x hx ↦ hφP (hsqPbox hx)) (hL₀c.mono hsqPbox)
      (hTc.mono inter_subset_left) (fun x hx ↦ hL₀p x (hsqPbox hx)) (fun x hx ↦ hTsq x hx.1)
      hL₀a
  set q₀ := T' v₀
  have hq₀ : p q₀ = s := congrFun hT' v₀
  -- the lift converges to `q₀` at the edge `x = 0`
  have hapex : ∀ O : Set (ComplexPoints (X ↘ Spec (.of ℂ))), IsOpen O → q₀ ∈ O →
      ∃ η > 0, ∀ x ∈ boxP, x.1 < η → L₀ x ∈ O := by
    intro O hO hq₀O
    set F := p ⁻¹' {s}
    obtain ⟨V, hV, hVd⟩ := (hfin s).t2_separation
    set W : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))) :=
      fun q ↦ if q = q₀ then V q ∩ O else V q
    have hWo : ∀ q, IsOpen (W q) := fun q ↦ by
      simp only [W]; split_ifs; exacts [(hV q).2.inter hO, (hV q).2]
    have hWV : ∀ q, W q ⊆ V q := fun q ↦ by
      simp only [W]; split_ifs; exacts [inter_subset_left, le_rfl]
    have hWm : ∀ q, q ∈ W q := fun q ↦ by
      simp only [W]; split_ifs with h; exacts [⟨(hV q).1, h ▸ hq₀O⟩, (hV q).1]
    set K := (⋃ q ∈ F, W q)ᶜ
    have hK : IsClosed (p '' K) := hcl _ (isOpen_biUnion fun q _ ↦ hWo q).isClosed_compl
    have hsK : s ∉ p '' K := by
      rintro ⟨y, hyK, hys⟩
      exact hyK (mem_biUnion (x := y) hys (hWm y))
    have hN : e'.symm ⁻¹' (p '' K)ᶜ ∈ 𝓝 P := by
      refine (e'.continuousAt_symm (e'.map_source hssrc)).preimage_mem_nhds ?_
      rw [e'.left_inv hssrc]
      exact hK.isOpen_compl.mem_nhds hsK
    obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
      ((hγ.continuous.sub continuous_const).continuousOn (s := Icc (-1 : ℝ) 2))
    have hρ : ∀ᶠ t in 𝓝 (0 : ℝ), coneProfile t < ε / (|M| + 1) := by
      have := continuous_coneProfile.continuousAt (x := 0)
      rw [ContinuousAt, coneProfile_zero] at this
      exact this.eventually (gt_mem_nhds (div_pos hε (by positivity)))
    obtain ⟨η, hη, hηρ⟩ := Metric.eventually_nhds_iff.1 hρ
    have hstrip : ∀ x ∈ boxP, x.1 < η → L₀ x ∈ ⋃ q ∈ F, W q := by
      intro x hx hxη
      by_contra hK'
      apply hεN (show g x ∈ Metric.ball P ε from ?_) ⟨L₀ x, hK', hL₀p x hx⟩
      rw [Metric.mem_ball, dist_eq_norm, hgx, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (coneProfile_nonneg _)]
      have h1 := hηρ (show dist x.1 0 < η by
        rwa [Real.dist_eq, sub_zero, abs_of_pos hx.2])
      calc coneProfile x.1 * ‖γ x.2 - P‖ ≤ coneProfile x.1 * |M| :=
            mul_le_mul_of_nonneg_left ((hM _ ⟨by linarith [hx.1.2.1], by linarith [hx.1.2.2]⟩).trans
              (le_abs_self M)) (coneProfile_nonneg _)
        _ ≤ ε / (|M| + 1) * |M| := mul_le_mul_of_nonneg_right h1.le (abs_nonneg M)
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [abs_nonneg M]
    set A := boxP ∩ {x : ℝ × ℝ | x.1 < η}
    have hAconv : Convex ℝ A :=
      hboxP.inter (convex_halfSpace_lt (f := Prod.fst) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ η)
    -- points `(t, 1/2)` of the square near the edge
    have hTcont : ContinuousAt (fun t : ℝ ↦ T' (squareCollapse (t, 1 / 2))) 0 :=
      (T'.continuous.comp (continuous_squareCollapse.comp
        (continuous_id.prodMk continuous_const))).continuousAt
    have hT0 : T' (squareCollapse ((0 : ℝ), (1 / 2 : ℝ))) = q₀ := by
      rw [squareCollapse_eq_vertex_zero ⟨⟨le_rfl, zero_le_one⟩, ⟨by norm_num, by norm_num⟩⟩ rfl]
    obtain ⟨τ, hτ, hτW⟩ := Metric.eventually_nhds_iff.1
      (hTcont.eventually ((hWo q₀).mem_nhds (by
        change T' (squareCollapse ((0 : ℝ), (1 / 2 : ℝ))) ∈ W q₀; rw [hT0]; exact hWm q₀)))
    set t := min (min η τ) (1 / 2) / 2
    have ht : 0 < t := by positivity
    have htη : t < η := by simp only [t]; linarith [min_le_left (min η τ) (1 / 2), min_le_left η τ]
    have htτ : t < τ := by simp only [t]; linarith [min_le_left (min η τ) (1 / 2), min_le_right η τ]
    have ht1 : t ≤ 1 := by simp only [t]; linarith [min_le_right (min η τ) (1 / 2)]
    have htsq : ((t, 1 / 2) : ℝ × ℝ) ∈ sqP :=
      ⟨⟨⟨ht.le, ht1⟩, ⟨by norm_num, by norm_num⟩⟩, ht⟩
    have htA : ((t, 1 / 2) : ℝ × ℝ) ∈ A := ⟨hsqPbox htsq, htη⟩
    obtain ⟨q, hqF, hqA⟩ := exists_image_subset_of_isPreconnected
      (hAconv.isPreconnected.image _ (hL₀c.mono inter_subset_left)) ⟨_, htA⟩ hWo
      (fun a ha b hb hab ↦ (hVd ha hb hab).mono (hWV a) (hWV b))
      (by rintro _ ⟨x, hx, rfl⟩; exact hstrip x hx.1 hx.2)
    have hq : q = q₀ := by
      by_contra hne
      have h1 : L₀ (t, 1 / 2) ∈ W q := hqA ⟨_, htA, rfl⟩
      have h2 : L₀ (t, 1 / 2) ∈ W q₀ := by
        rw [heqP htsq]
        exact hτW (by rwa [Real.dist_eq, sub_zero, abs_of_pos ht])
      have hq₀F : q₀ ∈ F := hq₀
      exact (hVd hqF hq₀F hne).le_bot ⟨hWV q h1, hWV q₀ h2⟩
    subst hq
    refine ⟨η, hη, fun x hx hxη ↦ ?_⟩
    have := hqA ⟨x, ⟨hx, hxη⟩, rfl⟩
    simp only [W, ite_eq_left rfl] at this
    exact this.2
  -- the lift on the box
  set L : ℝ × ℝ → ComplexPoints (X ↘ Spec (.of ℂ)) := fun x ↦ if 0 < x.1 then L₀ x else q₀
  have hLc : ContinuousOn L box := by
    intro x hx
    by_cases hx1 : 0 < x.1
    · have hmem : boxP ∈ 𝓝[box] x := by
        rw [show boxP = box ∩ {x : ℝ × ℝ | 0 < x.1} from rfl]
        exact inter_mem_nhdsWithin _ ((isOpen_lt continuous_const continuous_fst).mem_nhds hx1)
      refine ((hL₀c x ⟨hx, hx1⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_
        (by simp only [L, ite_eq_left hx1])
      filter_upwards [hmem] with y hy
      exact ite_eq_left (show 0 < y.1 from hy.2)
    · have hLx : L x = q₀ := by simp only [L, ite_eq_right hx1]
      rw [ContinuousWithinAt, hLx]
      refine (nhds_basis_opens q₀).tendsto_right_iff.2 fun O ⟨hq₀O, hO⟩ ↦ ?_
      obtain ⟨η, hη, hηO⟩ := hapex O hO hq₀O
      have hN : {y : ℝ × ℝ | y.1 < η} ∈ 𝓝 x :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds (by
          change x.1 < η; linarith [not_lt.1 hx1])
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hN] with y hy hyη
      by_cases hy1 : 0 < y.1
      · simpa only [L, ite_eq_left hy1] using hηO y ⟨hy, hy1⟩ hyη
      · simpa only [L, ite_eq_right hy1] using hq₀O
  have hLp : ∀ x ∈ box, p (L x) = φ x := by
    intro x hx
    by_cases hx1 : 0 < x.1
    · simpa only [L, ite_eq_left hx1] using hL₀p x ⟨hx, hx1⟩
    · simp only [L, ite_eq_right hx1]
      rw [hq₀, eq_comm, hφs x (hboxU hx), hgx, coneProfile_of_nonpos (not_lt.1 hx1), zero_smul,
        add_zero]
  refine ⟨δ, hδ, hboxU, L, hLc, hLp, fun q hq ↦ ?_, fun x hx h ↦ ?_⟩
  · by_cases hq1 : 0 < q.1
    · simpa only [L, ite_eq_left hq1] using heqP ⟨hq, hq1⟩
    · simp only [L, ite_eq_right hq1]
      rw [squareCollapse_eq_vertex_zero hq (le_antisymm (not_lt.1 hq1) hq.1.1)]
  · have hx1 : ¬ 0 < x.1 := fun hx1 ↦ by
      have := hLp x hx
      simp only [L, ite_eq_left hx1] at this h
      exact hφP ⟨hx, hx1⟩ (by rw [← hL₀p x ⟨hx, hx1⟩]; exact h)
    have hLx : p (L x) = s := by simpa only [L, ite_eq_right hx1] using hq₀
    refine ⟨not_lt.1 hx1, γ, hγ, by rw [hLx]; exact hgγ, fun y hy ↦ ?_⟩
    rw [hLx]
    exact (hbox (show ((0 : ℝ), y) ∈ box from ⟨⟨by linarith, by linarith⟩, hy⟩)).2

/-- **A locally injective holomorphic function has nonzero derivative.** -/
theorem deriv_ne_zero_of_injOn {G : ℂ → ℂ} {z₀ : ℂ} (hG : AnalyticAt ℂ G z₀) {M : Set ℂ}
    (hM : M ∈ 𝓝 z₀) (hinj : InjOn G M) : deriv G z₀ ≠ 0 := by
  have hnc : ¬ ∀ᶠ z in 𝓝 z₀, G z = G z₀ := by
    intro h
    have h2 : ∀ᶠ z in 𝓝 z₀, z = z₀ :=
      (h.and hM).mono fun z hz ↦ hinj hz.2 (mem_of_mem_nhds hM) hz.1
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h2
    have := hball (y := z₀ + (ε / 2 : ℝ)) (by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]; linarith)
    have h3 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
    exact (by positivity : (0 : ℝ) < ε / 2).ne' (by exact_mod_cast h3)
  obtain ⟨n, ψ, hn, hψa, hψd, hψ0, hψeq⟩ := MMP.Analytic.exists_analyticAt_pow_normalForm hG hnc
  by_cases h1 : n = 1
  · subst h1
    have : deriv G z₀ = deriv (fun z ↦ G z₀ + ψ z ^ 1) z₀ :=
      (show G =ᶠ[𝓝 z₀] fun z ↦ G z₀ + ψ z ^ 1 from hψeq).deriv_eq
    rw [this]
    simpa using hψd
  · exfalso
    have hn2 : 1 < n := by omega
    obtain ⟨E, hz₀E, hEN, hEψ, -, -⟩ := MMP.Analytic.exists_analytic_openPartialHomeomorph hψa hψd
      (Filter.inter_mem hM hψeq)
    have h0 : E z₀ = 0 := by rw [hEψ hz₀E]; exact hψ0
    obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.1
      (E.open_target.mem_nhds (show (0 : ℂ) ∈ E.target from h0 ▸ E.map_source hz₀E))
    set ζ := Complex.exp (2 * Real.pi * Complex.I / n)
    have hζ := Complex.isPrimitiveRoot_exp n (by omega)
    have hζ1 : ζ ≠ 1 := hζ.ne_one hn2
    have hζn : ζ ^ n = 1 := hζ.pow_eq_one
    have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζn hn.ne'
    set w : ℂ := ((r / 2 : ℝ) : ℂ)
    have hw0 : w ≠ 0 := by
      simp only [w, ne_eq, Complex.ofReal_eq_zero]; positivity
    have hwr : ‖w‖ < r := by
      simp only [w, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      linarith
    have hw : w ∈ E.target := hrT (mem_ball_zero_iff.2 hwr)
    have hζw : ζ * w ∈ E.target := hrT (mem_ball_zero_iff.2
      (by rw [norm_mul, hζnorm, one_mul]; exact hwr))
    have hs1 := E.map_target hw
    have hs2 := E.map_target hζw
    have hψ1 : ψ (E.symm w) = w := by rw [← hEψ hs1, E.right_inv hw]
    have hψ2 : ψ (E.symm (ζ * w)) = ζ * w := by rw [← hEψ hs2, E.right_inv hζw]
    have hG1 := (hEN hs1).2
    have hG2 := (hEN hs2).2
    simp only [mem_ofPred_eq] at hG1 hG2
    have heq : E.symm w = E.symm (ζ * w) := hinj (hEN hs1).1 (hEN hs2).1 (by
      rw [hG1, hG2, hψ1, hψ2, mul_pow, hζn, one_mul])
    exact hζ1 (mul_right_cancel₀ hw0
      ((one_mul w).trans (hψ1.symm.trans ((congrArg ψ heq).trans hψ2))).symm)

/-- **The local reading of a lift.** Let `L` be continuous on an open set `Ω ⊆ U`, lifting the
reading `c'⁻¹ ∘ g` of a `C²` map `g`, and `x ∈ Ω` with `L x` in the domain of an étale chart `c`
of `X`. If `L x` lies over `S`, suppose `g` is a flat cone from `L x`'s image over a base curve
avoiding the apex near `x.2`, and `x.1 ≤ 0`. Then `c ∘ L` is `C²` at `x`, and its Jacobian at `x`
is a nonnegative multiple of that of `g`, positive off the preimage of `S`.

Off the preimage of `S`, `c ∘ L = H ∘ g` near `x` for the holomorphic local inverse `H` of
`c' ∘ f ∘ c⁻¹`, whose derivative does not vanish since `f` is a local homeomorphism there. Over
`s ∈ S`, `c ∘ L = (c ∘ φ⁻¹)(u ρ_e(x₁) R(x₂))` near `x` for the local normal form
`c' ∘ f = c'(s) + φ ^ e` (`exists_pow_normalForm_realize`), a smooth `e`-th root `R` of the base
curve minus `c'(s)` (`exists_contDiffOn_pow_eq_sub`) and an `e`-th root of unity `u`
(`exists_pow_eq_one_forall_eq_mul`); both Jacobians vanish on `x₁ ≤ 0`. -/
theorem contDiffAt_chart_comp_lift [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    [IsSeparated (X ↘ Spec (.of ℂ))]
    (f : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ 1))
    (hf : f ≫ projToSpecCoeff ℂ 1 = X ↘ Spec (.of ℂ)) [IsFinite f]
    {S : Set (ComplexPoints (projToSpecCoeff ℂ 1))}
    (hcov : IsCoveringMapOn (realize f hf) Sᶜ)
    (c' : EtaleCoordinateChart (projToSpecCoeff ℂ 1) 1)
    (g : ℝ × ℝ → (Fin 1 → ℂ)) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hg : ContDiffOn ℝ 2 g Ω)
    (hgT : MapsTo g Ω c'.toOpenPartialHomeomorph.target)
    (L : ℝ × ℝ → ComplexPoints (X ↘ Spec (.of ℂ))) (hL : ContinuousOn L Ω)
    (hLp : ∀ x ∈ Ω, realize f hf (L x) = c'.toOpenPartialHomeomorph.symm (g x))
    (c : EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1) {x : ℝ × ℝ} (hx : x ∈ Ω) (hxc : L x ∈ c.W)
    (hram : realize f hf (L x) ∈ S → x.1 ≤ 0 ∧
      ∃ γ : ℝ → Fin 1 → ℂ, ContDiff ℝ 2 γ ∧ g = CurveCupPositivity.coneMap coneProfile
        (c'.toOpenPartialHomeomorph (realize f hf (L x))) γ ∧
        ∀ᶠ y in 𝓝 x.2, γ y ≠
          c'.toOpenPartialHomeomorph (realize f hf (L x))) :
    ContDiffAt ℝ 2 (fun x ↦ c.toOpenPartialHomeomorph (L x)) x ∧ ∃ a : ℝ, 0 ≤ a ∧
      (L x ∉ realize f hf ⁻¹' S → 0 < a) ∧
      ∀ i, FundamentalChartCycle.chartJacobian (fun x ↦ c.toOpenPartialHomeomorph (L x)) x i =
        a * FundamentalChartCycle.chartJacobian g x i := by
  classical
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ 1⟩
  haveI : IsProper (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ 1
  haveI : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  set p := realize f hf
  set e := c.toOpenPartialHomeomorph
  set e' := c'.toOpenPartialHomeomorph
  set κ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hes : e.source = c.W := c.source_toOpenPartialHomeomorph
  have hLx : ContinuousAt L x := hL.continuousAt (hΩ.mem_nhds hx)
  have hgx : ContDiffAt ℝ 2 g x := hg.contDiffAt (hΩ.mem_nhds hx)
  have hxs : L x ∈ e.source := hes ▸ hxc
  have hpx : p (L x) ∈ e'.source := by rw [hLp x hx]; exact e'.map_target (hgT hx)
  have hpW : p (L x) ∈ c'.W := c'.source_toOpenPartialHomeomorph ▸ hpx
  have hpc : Continuous p := continuous_realize f _
  have hκ : ∀ v : Fin 1 → ℂ, κ v = v 0 := fun v ↦ rfl
  have hκs : ∀ z : ℂ, κ.symm z = fun _ ↦ z := fun z ↦ by
    funext i
    have := κ.apply_symm_apply z
    rw [hκ] at this
    rwa [Subsingleton.elim i 0]
  have hκd : ∀ (G : ℝ × ℝ → (Fin 1 → ℂ)) (q : ℝ × ℝ) (v : ℝ × ℝ), DifferentiableAt ℝ G q →
      fderiv ℝ (fun y ↦ κ (G y)) q v = fderiv ℝ G q v 0 := fun G q v hG ↦ by
    have h : HasFDerivAt (fun y ↦ κ (G y)) _ q :=
      (((κ : (Fin 1 → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt).comp q hG.hasFDerivAt
    rw [h.fderiv]; rfl
  have hJg : ∀ i : Fin 1, (star (fderiv ℝ (fun y ↦ κ (g y)) x (1, 0)) *
      fderiv ℝ (fun y ↦ κ (g y)) x (0, 1)).im = FundamentalChartCycle.chartJacobian g x i := by
    intro i
    have hd := hgx.differentiableAt (by norm_num)
    rw [hκd g x _ hd, hκd g x _ hd, Subsingleton.elim i 0]
  have hgκ : ContDiffAt ℝ 2 (fun y ↦ κ (g y)) x :=
    (κ.contDiff.restrict_scalars ℝ).contDiffAt.comp x hgx
  by_cases hS0 : p (L x) ∈ S
  swap
  · -- off the branch set: the holomorphic local inverse
    obtain ⟨E₀, hE₀, hpE₀⟩ := hcov.isLocalHomeomorphOn (L x) hS0
    set G : ℂ → ℂ := fun z ↦ κ (e' (p (e.symm (κ.symm z))))
    set z₀ := κ (e (L x))
    have hz₀ : κ.symm z₀ = e (L x) := κ.symm_apply_apply _
    have hGa : AnalyticAt ℂ G z₀ :=
      ((κ : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt _).comp
        ((c.analyticAt_realize f _ c' hxc hpW).comp_of_eq
          ((κ.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).analyticAt z₀) hz₀)
    have hcs : ContinuousAt (fun z ↦ e.symm (κ.symm z)) z₀ := by
      refine ContinuousAt.comp (f := fun z ↦ κ.symm z) ?_ κ.symm.continuous.continuousAt
      rw [hz₀]; exact e.continuousAt_symm (e.map_source hxs)
    have hcsv : e.symm (κ.symm z₀) = L x := by rw [hz₀, e.left_inv hxs]
    have hM : {z | κ.symm z ∈ e.target ∧ e.symm (κ.symm z) ∈ E₀.source ∧
        p (e.symm (κ.symm z)) ∈ e'.source} ∈ 𝓝 z₀ := by
      refine Filter.inter_mem (κ.symm.continuous.continuousAt.preimage_mem_nhds
        (e.open_target.mem_nhds (by rw [hz₀]; exact e.map_source hxs)))
        (Filter.inter_mem (hcs.preimage_mem_nhds
          (E₀.open_source.mem_nhds (by rw [hcsv]; exact hE₀)))
          ((hpc.continuousAt.comp hcs).preimage_mem_nhds
            (e'.open_source.mem_nhds (by simp only [Function.comp_apply, hcsv]; exact hpx))))
    have hinj : InjOn G {z | κ.symm z ∈ e.target ∧ e.symm (κ.symm z) ∈ E₀.source ∧
        p (e.symm (κ.symm z)) ∈ e'.source} := by
      intro z₁ h₁ z₂ h₂ h
      have h1 : e' (p (e.symm (κ.symm z₁))) = e' (p (e.symm (κ.symm z₂))) := κ.injective h
      have h2 := e'.injOn h₁.2.2 h₂.2.2 h1
      rw [hpE₀] at h2
      have h3 := E₀.injOn h₁.2.1 h₂.2.1 h2
      exact κ.symm.injective (e.symm.injOn h₁.1 h₂.1 h3)
    have hd := deriv_ne_zero_of_injOn hGa hM hinj
    obtain ⟨E, hz₀E, -, hEG, -, hEsymm⟩ :=
      MMP.Analytic.exists_analytic_openPartialHomeomorph hGa hd Filter.univ_mem
    have hNx : Ω ∩ L ⁻¹' e.source ∩ (fun x' ↦ κ (e (L x'))) ⁻¹' E.source ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem (hΩ.mem_nhds hx)
        (hLx.preimage_mem_nhds (e.open_source.mem_nhds hxs)))
        ((κ.continuous.continuousAt.comp ((e.continuousAt hxs).comp hLx)).preimage_mem_nhds
          (E.open_source.mem_nhds hz₀E))
    have hE : ∀ x' ∈ Ω ∩ L ⁻¹' e.source ∩ (fun x' ↦ κ (e (L x'))) ⁻¹' E.source,
        E (κ (e (L x'))) = κ (g x') := fun x' hx' ↦ by
      rw [hEG hx'.2, show G (κ (e (L x'))) = κ (e' (p (e.symm (κ.symm (κ (e (L x'))))))) from rfl,
        κ.symm_apply_apply, e.left_inv hx'.1.2, hLp x' hx'.1.1, e'.right_inv (hgT hx'.1.1)]
    set h : ℂ → Fin 1 → ℂ := fun z _ ↦ E.symm z
    have heq : (fun x' ↦ e (L x')) =ᶠ[𝓝 x] fun x' ↦ h (κ (g x')) := by
      filter_upwards [hNx] with x' hx'
      have h2 : κ (e (L x')) ∈ E.source := hx'.2
      change e (L x') = fun _ ↦ E.symm (κ (g x'))
      rw [← hE x' hx', E.left_inv h2, ← hκs, κ.symm_apply_apply]
    set w := κ (g x)
    have hwE : E z₀ = w := hE x (mem_of_mem_nhds hNx)
    have hwT : w ∈ E.target := hwE ▸ E.map_source hz₀E
    have hhA : AnalyticAt ℂ h w := AnalyticAt.pi fun _ ↦ hEsymm w hwT
    have hEd : HasDerivAt E (deriv G z₀) (E.symm w) := by
      rw [← hwE, E.left_inv hz₀E]
      exact hGa.differentiableAt.hasDerivAt.congr_of_eventuallyEq
        (Filter.eventually_of_mem (E.open_source.mem_nhds hz₀E) fun z hz ↦ hEG hz)
    have hEs := E.hasDerivAt_symm hwT hd hEd
    have hhd : deriv h w = fun _ ↦ (deriv G z₀)⁻¹ :=
      (hasDerivAt_pi.2 fun _ ↦ hEs).deriv
    have hh2 : ContDiffAt ℝ 2 h w := (hhA.contDiffAt (n := 2)).restrict_scalars ℝ
    have hcomp : ContDiffAt ℝ 2 (h ∘ fun y ↦ κ (g y)) x := hh2.comp (g := h) x hgκ
    refine ⟨hcomp.congr_of_eventuallyEq heq, Complex.normSq (deriv G z₀)⁻¹, Complex.normSq_nonneg _,
      fun _ ↦ Complex.normSq_pos.2 (inv_ne_zero hd), fun i ↦ ?_⟩
    change (star (fderiv ℝ (fun x' ↦ e (L x')) x (1, 0) i) *
      fderiv ℝ (fun x' ↦ e (L x')) x (0, 1) i).im = _
    rw [heq.fderiv_eq, im_star_fderiv_comp_eq hhA.differentiableAt
      (hgκ.differentiableAt (by norm_num)) i, hhd, hJg i]
  · -- over the branch set: the normal form and a root of the base curve
    obtain ⟨hx1, γ, hγ, hgγ, hγne⟩ := hram hS0
    set s := p (L x)
    set P := e' s
    have : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
    have hT2 : T2Space (ComplexPoints (X ↘ Spec (.of ℂ))) := t2Space_complexPoints
    have hfin : ∀ s, (p ⁻¹' {s}).Finite := finite_realize_preimage_singleton f
    obtain ⟨n, φ, hn, hqφ, -, -, hnf, hφan⟩ := exists_pow_normalForm_realize f _ c c' hxc hpW
      (not_eventually_realize_eq f _ hfin (L x)) Filter.univ_mem
    have hnf' : ∀ y ∈ φ.source, φ y ^ n = κ (e' (p y)) - κ P := fun y hy ↦ by
      have := (hnf y hy).2
      change κ (e' (p y)) = κ (e' s) + φ y ^ n at this
      rw [this]; ring
    have hgx' : ∀ x' : ℝ × ℝ, κ (g x') - κ P = coneProfile x'.1 * (κ (γ x'.2) - κ P) := by
      intro x'
      rw [hgγ, hκ, hκ, hκ]
      simp only [coneMap_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Complex.real_smul]
      ring
    have hγx : κ (γ x.2) - κ P ≠ 0 := fun h ↦
      hγne.self_of_nhds (κ.injective (sub_eq_zero.1 h))
    set a := (κ (γ x.2) - κ P)⁻¹
    have ha : a ≠ 0 := inv_ne_zero hγx
    have hγκ : Continuous fun y ↦ κ (γ y) := κ.continuous.comp hγ.continuous
    set V := (fun y ↦ a * (κ (γ y) - κ P)) ⁻¹' Complex.slitPlane
    have hVo : IsOpen V :=
      Complex.isOpen_slitPlane.preimage (continuous_const.mul (hγκ.sub continuous_const))
    have hxV : x.2 ∈ V := by
      change a * (κ (γ x.2) - κ P) ∈ Complex.slitPlane
      rw [inv_mul_cancel₀ hγx]; exact Complex.one_mem_slitPlane
    obtain ⟨R, hR, hRγ⟩ := exists_contDiffOn_pow_eq_sub (γ := fun y ↦ κ (γ y)) (s₀ := κ P) hn ha
      ((κ.contDiff.restrict_scalars ℝ).comp hγ).contDiffOn fun y hy ↦ hy
    have hR0 : ∀ y ∈ V, R y ≠ 0 := fun y hy h ↦ by
      have := hRγ y hy
      rw [h, zero_pow hn.ne'] at this
      have hy' : a * (κ (γ y) - κ P) ∈ Complex.slitPlane := hy
      rw [← this, mul_zero] at hy'
      exact Complex.zero_notMem_slitPlane hy'
    have hNx : Ω ∩ L ⁻¹' φ.source ∩ {x' : ℝ × ℝ | x'.2 ∈ V} ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem (hΩ.mem_nhds hx)
        (hLx.preimage_mem_nhds (φ.open_source.mem_nhds hqφ)))
        (continuous_snd.continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV))
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hNx
    set Λ : ℝ × ℝ → ℂ := fun x' ↦ (rootProfile n x'.1 : ℂ) * R x'.2
    have hpowΛ : ∀ x' ∈ Metric.ball x r, Λ x' ^ n = φ (L x') ^ n := fun x' hx' ↦ by
      have hx'' := hball hx'
      rw [hnf' _ hx''.1.2, hLp x' hx''.1.1, e'.right_inv (hgT hx''.1.1), hgx', mul_pow,
        ← Complex.ofReal_pow, rootProfile_pow hn, hRγ _ hx''.2]
    set Q := Metric.ball x r ∩ {x' : ℝ × ℝ | 0 < x'.1}
    have hQ : Convex ℝ Q := (convex_ball x r).inter
      (convex_halfSpace_gt (f := Prod.fst) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 0)
    have : PreconnectedSpace Q := Subtype.preconnectedSpace hQ.isPreconnected
    have hWc : Continuous fun t : Q ↦ φ (L t) :=
      φ.continuousOn.comp_continuous (hL.comp_continuous continuous_subtype_val
        fun t ↦ (hball t.2.1).1.1) fun t ↦ (hball t.2.1).1.2
    have hRc : ContinuousOn R V := hR.continuousOn
    have hΛc : Continuous fun t : Q ↦ Λ t :=
      (Complex.continuous_ofReal.comp ((continuous_rootProfile n).comp
        (continuous_fst.comp continuous_subtype_val))).mul
        (hRc.comp_continuous (continuous_snd.comp continuous_subtype_val)
          fun t ↦ (hball t.2.1).2)
    have hΛne : {t : Q | Λ t ≠ 0} = univ := by
      ext t
      simp only [mem_ofPred_eq, mem_univ, iff_true, Λ]
      exact mul_ne_zero (Complex.ofReal_ne_zero.2 (rootProfile_pos hn t.2.2).ne')
        (hR0 _ (hball t.2.1).2)
    obtain ⟨u, hu, hWu⟩ := exists_pow_eq_one_forall_eq_mul hWc hΛc hn
      (fun t ↦ (hpowΛ t t.2.1).symm) (by rw [hΛne]; exact isPreconnected_univ)
    set Θ : ℝ × ℝ → ℂ := fun x' ↦ u * Λ x'
    have hΘ : ∀ x' ∈ Metric.ball x r, φ (L x') = Θ x' := by
      intro x' hx'
      by_cases h1 : 0 < x'.1
      · exact hWu ⟨x', hx', h1⟩
      · have hρ : rootProfile n x'.1 = 0 := by
          rw [rootProfile, coneProfile_of_nonpos (by
            nlinarith [not_lt.1 h1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]), zero_div]
        have hΛ0 : Λ x' = 0 := by simp only [Λ, hρ, Complex.ofReal_zero, zero_mul]
        have := hpowΛ x' hx'
        rw [hΛ0, zero_pow hn.ne'] at this
        rw [show Θ x' = 0 by simp only [Θ, hΛ0, mul_zero]]
        exact (pow_eq_zero_iff hn.ne').1 this.symm
    set hφ' : ℂ → Fin 1 → ℂ := fun w ↦ e (φ.symm w)
    have heq : (fun x' ↦ e (L x')) =ᶠ[𝓝 x] fun x' ↦ hφ' (Θ x') := by
      filter_upwards [Metric.ball_mem_nhds x hr] with x' hx'
      simp only [hφ', ← hΘ x' hx', φ.left_inv (hball hx').1.2]
    have hΘT : Θ x ∈ φ.target := by
      rw [← hΘ x (Metric.mem_ball_self hr)]; exact φ.map_source hqφ
    have hΘc : ContDiffAt ℝ 2 Θ x := by
      have h1 : ContDiff ℝ 2 fun x' : ℝ × ℝ ↦ (rootProfile n x'.1 : ℂ) :=
        Complex.ofRealCLM.contDiff.comp ((contDiff_rootProfile n (by simp)).comp contDiff_fst)
      have h2 : ContDiffAt ℝ 2 (fun x' : ℝ × ℝ ↦ R x'.2) x :=
        (hR.contDiffAt (hVo.mem_nhds hxV)).comp x contDiff_snd.contDiffAt
      exact contDiffAt_const.mul (h1.contDiffAt.mul h2)
    have hA := hφan _ hΘT
    have hA2 : ContDiffAt ℝ 2 hφ' (Θ x) := (hA.contDiffAt (n := 2)).restrict_scalars ℝ
    have hcomp : ContDiffAt ℝ 2 (hφ' ∘ Θ) x := hA2.comp (g := hφ') x hΘc
    refine ⟨hcomp.congr_of_eventuallyEq heq, 0, le_rfl, fun h ↦ absurd hS0 h, fun i ↦ ?_⟩
    rw [zero_mul]
    change (star (fderiv ℝ (fun x' ↦ e (L x')) x (1, 0) i) *
      fderiv ℝ (fun x' ↦ e (L x')) x (0, 1) i).im = 0
    rw [heq.fderiv_eq, im_star_fderiv_comp_eq hA.differentiableAt
      (hΘc.differentiableAt (by norm_num)) i]
    -- the second partial derivative of `Θ` vanishes on `x₁ ≤ 0`
    have hρx : rootProfile n x.1 = 0 := by
      rw [rootProfile, coneProfile_of_nonpos (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
        zero_div]
    have hcurve : HasDerivAt (fun t : ℝ ↦ ((x.1, x.2 + t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) 0 := by
      refine (hasDerivAt_const _ _).prodMk ?_
      simpa using (hasDerivAt_id (0 : ℝ)).const_add x.2
    have hΘf : HasFDerivAt Θ (fderiv ℝ Θ x) ((fun t : ℝ ↦ ((x.1, x.2 + t) : ℝ × ℝ)) 0) := by
      simpa using (hΘc.differentiableAt (by norm_num)).hasFDerivAt
    have h1 := hΘf.comp_hasDerivAt (0 : ℝ) hcurve
    have h2 : HasDerivAt (fun t : ℝ ↦ Θ (x.1, x.2 + t)) 0 0 := by
      have : (fun t : ℝ ↦ Θ (x.1, x.2 + t)) = fun _ ↦ 0 := by
        funext t; simp only [Θ, Λ, hρx, Complex.ofReal_zero, zero_mul, mul_zero]
      rw [this]; exact hasDerivAt_const _ _
    have h3 : fderiv ℝ Θ x (0, 1) = 0 := h1.unique h2
    rw [h3, mul_zero, Complex.zero_im, mul_zero]

/-- **The reading of a lift of a chart triangle.** Let `f : X ⟶ ℙ¹` be a finite morphism of a
smooth curve, a covering map off a finite set `S`, and `σ` a triangle of `ℙ¹(ℂ)` read in an
étale chart `c'` as a `C²` map `g` on an open neighbourhood `U` of the square, meeting `S` only
at its vertex `0` and, if it does, a flat cone from that point. Every lift `T'` of `σ` with
values in the domain of an étale chart `c` of `X` is read in `c` as a `C²` map `g'` on an open
neighbourhood of the square, whose Jacobian at each point of the square is a nonnegative multiple
of that of `g`, positive off the preimage of `S`.

Off the vertex `0`, the lift is locally the holomorphic inverse of `f` composed with `σ`, which
multiplies the Jacobian by `|h'|² > 0`. Near a ramified vertex `0` of index `e`, it is
`φ⁻¹(u ρ_e(x) R(y))` for the local normal form `c' ∘ f = c'(s) + φ ^ e`, an `e`-th root `R` of
the base curve minus `c'(s)` and an `e`-th root of unity `u`. -/
theorem exists_reading_mem_simplexLifts [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    [IsSeparated (X ↘ Spec (.of ℂ))]
    (f : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ 1))
    (hf : f ≫ projToSpecCoeff ℂ 1 = X ↘ Spec (.of ℂ)) [IsFinite f]
    {S : Set (ComplexPoints (projToSpecCoeff ℂ 1))} (hS : S.Finite)
    (hcov : IsCoveringMapOn (realize f hf) Sᶜ)
    (σ : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1))
    (c' : EtaleCoordinateChart (projToSpecCoeff ℂ 1) 1)
    (g : ℝ × ℝ → (Fin 1 → ℂ)) (U : Set (ℝ × ℝ)) (hUo : IsOpen U) (hsq : unitSquare ⊆ U)
    (hg : ContDiffOn ℝ 2 g U) (hgT : MapsTo g U c'.toOpenPartialHomeomorph.target)
    (hσ : ∀ q ∈ unitSquare, σ (squareCollapse q) = c'.toOpenPartialHomeomorph.symm (g q))
    (hσS : ∀ t, σ t ∈ S → t 0 = 1)
    (hcone : ∀ s ∈ S, s ∈ range σ → ∃ γ : ℝ → Fin 1 → ℂ, ContDiff ℝ 2 γ ∧
      g = CurveCupPositivity.coneMap coneProfile (c'.toOpenPartialHomeomorph s) γ)
    (T' : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1))
    (hT' : T' ∈ simplexLifts (realize f hf) σ)
    (c : EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1) (hc : range T' ⊆ c.W) :
    ∃ (g' : ℝ × ℝ → (Fin 1 → ℂ)) (U' : Set (ℝ × ℝ)), IsOpen U' ∧ unitSquare ⊆ U' ∧
      ContDiffOn ℝ 2 g' U' ∧ MapsTo g' U' c.toOpenPartialHomeomorph.target ∧
      (∀ q ∈ unitSquare, T' (squareCollapse q) = c.toOpenPartialHomeomorph.symm (g' q)) ∧
      ∀ q ∈ unitSquare, ∃ a : ℝ, 0 ≤ a ∧
        (T' (squareCollapse q) ∉ realize f hf ⁻¹' S → 0 < a) ∧
        ∀ i, FundamentalChartCycle.chartJacobian g' q i =
          a * FundamentalChartCycle.chartJacobian g q i := by
  obtain ⟨δ, hδ, hΩU, L, hLc, hLp, hLsq, hLS⟩ :=
    exists_continuousOn_lift_box f hf hS hcov σ c' g U hUo hsq hg hgT hσ hσS hcone T' hT'
  set Ω := Ioo (-δ) (1 + δ) ×ˢ Ioo (-δ) (1 + δ)
  have hΩo : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
  have hsqΩ : unitSquare ⊆ Ω := fun q hq ↦
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  set e := c.toOpenPartialHomeomorph
  have hes : e.source = c.W := c.source_toOpenPartialHomeomorph
  have hloc : ∀ x ∈ Ω ∩ L ⁻¹' c.W, ContDiffAt ℝ 2 (fun x ↦ e (L x)) x ∧ ∃ a : ℝ, 0 ≤ a ∧
      (L x ∉ realize f hf ⁻¹' S → 0 < a) ∧
      ∀ i, FundamentalChartCycle.chartJacobian (fun x ↦ e (L x)) x i =
        a * FundamentalChartCycle.chartJacobian g x i := fun x hx ↦
    contDiffAt_chart_comp_lift f hf hcov c' g hΩo (hg.mono hΩU) (hgT.mono_left hΩU) L hLc
      hLp c hx.1 hx.2 fun h ↦ by
        obtain ⟨h1, γ, hγ, hgγ, hne⟩ := hLS x hx.1 h
        exact ⟨h1, γ, hγ, hgγ, Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx.1.2) hne⟩
  refine ⟨fun x ↦ e (L x), Ω ∩ L ⁻¹' c.W, hLc.isOpen_inter_preimage hΩo c.isOpen,
    fun q hq ↦ ⟨hsqΩ hq, by rw [mem_preimage, hLsq q hq]; exact hc ⟨_, rfl⟩⟩,
    fun x hx ↦ (hloc x hx).1.contDiffWithinAt, fun x hx ↦ e.map_source (hes ▸ hx.2),
    fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · have hq' : L q ∈ e.source := hes ▸ (by rw [hLsq q hq]; exact hc ⟨_, rfl⟩)
    rw [e.left_inv hq', hLsq q hq]
  · obtain ⟨-, a, ha, hpos, hJ⟩ := hloc q
      ⟨hsqΩ hq, by rw [mem_preimage, hLsq q hq]; exact hc ⟨_, rfl⟩⟩
    exact ⟨a, ha, fun h ↦ hpos (by rwa [hLsq q hq]), hJ⟩

end Reading

/-! ### The fundamental chart cycle of a smooth projective curve -/

section Curve

open CategoryTheory AlgebraicGeometry MMP MMP.SingularCochain
open MMP.FundamentalClass MMP.Analytic.ComplexPoints
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]

/-- **Open images off the branch set.** A covering map over `Sᶜ` is open on open subsets of the
preimage of `Sᶜ`. -/
theorem isOpen_image_of_isCoveringMapOn {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {p : Y → Z} {S : Set Z} (hcov : IsCoveringMapOn p Sᶜ) {W : Set Y} (hW : IsOpen W)
    (hWS : W ⊆ p ⁻¹' Sᶜ) : IsOpen (p '' W) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, hpe⟩ := hcov.isLocalHomeomorphOn x (hWS hx)
  have ho : IsOpen (e '' (W ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hW.inter e.open_source) inter_subset_right
  refine Filter.mem_of_superset (ho.mem_nhds ⟨x, ⟨hx, hxe⟩, by rw [hpe]⟩) ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy.1, by rw [hpe]⟩

/-- **A smooth projective curve has fine fundamental chart cycles.** The
cycle is the transfer `f^! w` along a finite morphism `f : X ⟶ ℙ¹` of a fine fundamental cycle
`w` of flat chart cones of `ℙ¹(ℂ)` whose apices include the branch values of `f`, fine enough
that the lifts of its triangles lie in the given neighbourhoods. -/
theorem hasFundamentalChartCycle :
    MMP.Fourfold.Polarization.HasFundamentalChartCycle X := by
  classical
  intro _ B hBo hmem
  have : IsComplexScheme X := MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  -- the finite map to `ℙ¹`, over `ℂ` through `projToSpecCoeff ℂ 1`
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ 1⟩
  obtain ⟨f, hfo, hff, S₀, hfs, hS₀, hcov₀⟩ :=
    exists_isFinite_isCoveringMapOn_projectiveLine (X := X)
  haveI : IsProper (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ 1
  have hf : f ≫ projToSpecCoeff ℂ 1 = X ↘ Spec (.of ℂ) := comp_over f (Spec (.of ℂ))
  set p := realize f hf
  have hp : p = homeomorphUnderlyingSpace.symm ∘ (UnderlyingSpace.mapFun (K := ℂ) f ∘
      homeomorphUnderlyingSpace) := realize_eq_homeomorphUnderlyingSpace f
  have hpc : Continuous p := continuous_realize f hf
  set pC : C(ComplexPoints (X ↘ Spec (.of ℂ)),
    ComplexPoints (projToSpecCoeff ℂ 1)) := ⟨p, hpc⟩
  set S : Set (ComplexPoints (projToSpecCoeff ℂ 1)) :=
    homeomorphUnderlyingSpace ⁻¹' S₀
  have hS : S.Finite := hS₀.preimage homeomorphUnderlyingSpace.injective.injOn
  have hcov : IsCoveringMapOn p Sᶜ := by
    have := (hcov₀.comp_homeomorph homeomorphUnderlyingSpace).homeomorph_comp
      homeomorphUnderlyingSpace.symm
    rw [hp]
    rwa [Homeomorph.symm_symm] at this
  have hT2 : T2Space (ComplexPoints (X ↘ Spec (.of ℂ))) := t2Space_complexPoints
  have hcl : IsClosedMap p := isClosedMap_realize_of_isProper f
  have hfin : ∀ s, (p ⁻¹' {s}).Finite := finite_realize_preimage_singleton f
  have hsurj : Function.Surjective p := by
    rw [hp]
    exact homeomorphUnderlyingSpace.symm.surjective.comp
      ((UnderlyingSpace.mapFun_surjective (K := ℂ) f).comp homeomorphUnderlyingSpace.surjective)
  -- étale charts upstairs and the small neighbourhoods
  have hcX : ∀ q : ComplexPoints (X ↘ Spec (.of ℂ)),
      ∃ c : EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1, q ∈ c.W :=
    fun q ↦ EtaleCoordinateChart.exists_mem_W _
  choose cX hcX using hcX
  set N : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    fun q ↦ B q ∩ (cX q).W
  have hsmall := fun y ↦ exists_isOpen_forall_isPreconnected_subset hcl hfin N
    (fun q ↦ (hBo q).inter (cX q).isOpen) (fun q ↦ ⟨hmem q, hcX q⟩) y
  choose B' hB'o hB'm hB'small using hsmall
  obtain ⟨w, r, Y'', c', g, U, hw, hgood, hdense, ⟨σ₀, hσ₀, p₀, hp₀, hw₀, hJ₀, hinj₀, hsimple₀⟩,
    hSc, -⟩ := exists_cone_cycle_projectiveLine S hS B' hB'o hB'm
  -- the triangles of `w` meet `S` only at their vertex `0`
  have hσS : ∀ σ ∈ w.support, ∀ t, σ t ∈ S → t 0 = 1 := by
    intro σ hσ t ht
    have := (((hSc _ ht).2 σ hσ ⟨t, rfl⟩).2.2 t).1 rfl
    rw [this, squareCollapse_apply_zero ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩, sub_zero]
  have hfinL : ∀ σ ∈ w.support, (simplexLifts p σ).Finite := fun σ hσ ↦
    finite_simplexLifts_of_apex hcov hfin (hσS σ hσ)
  have hbij : ∀ σ ∈ w.support, ∀ i, BijOn (fun T' : Simplex _ (1 + 1) ↦ T'.comp (face 1 i))
      (simplexLifts p σ) (simplexLifts p (σ.comp (face 1 i))) := fun σ hσ i ↦
    bijOn_comp_face_of_apex (k := 0) hcov hcl hfin (hσS σ hσ) i
  set z : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →₀ ℂ :=
    transfer ℂ p (1 + 1) w
  have hz : bd ℂ 1 z = 0 := bd_transfer_eq_zero_of_bijOn ℂ p w hw hfinL hbij
  have hzapp : ∀ T', z T' = w (pC.comp T') := transfer_apply pC w hfinL
  have hzsupp : ∀ T' ∈ z.support, pC.comp T' ∈ w.support := fun T' hT' ↦
    comp_mem_support_of_mem_support_transfer pC hfinL hT'
  have hlift : ∀ T' : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1),
      T' ∈ simplexLifts p (pC.comp T') := fun T' ↦ (mem_simplexLifts_iff pC).2 rfl
  -- the readings of the lifts
  have H : ∀ T' ∈ z.support, ∃ (q : ComplexPoints (X ↘ Spec (.of ℂ)))
      (g' : ℝ × ℝ → (Fin 1 → ℂ)) (U' : Set (ℝ × ℝ)), range T' ⊆ B q ∧ range T' ⊆ (cX q).W ∧
      IsOpen U' ∧ unitSquare ⊆ U' ∧ ContDiffOn ℝ 2 g' U' ∧
      MapsTo g' U' (cX q).toOpenPartialHomeomorph.target ∧
      (∀ x ∈ unitSquare, T' (squareCollapse x) = (cX q).toOpenPartialHomeomorph.symm (g' x)) ∧
      ∀ x ∈ unitSquare, ∃ a : ℝ, 0 ≤ a ∧ (T' (squareCollapse x) ∉ p ⁻¹' S → 0 < a) ∧
        ∀ i, FundamentalChartCycle.chartJacobian g' x i =
          a * FundamentalChartCycle.chartJacobian (g (pC.comp T')) x i := by
    intro T' hT'
    set σ := pC.comp T'
    have hσ := hzsupp T' hT'
    obtain ⟨-, hYσ, hUo, hsq, hgσ, hgT, hread, -⟩ := hgood σ hσ
    obtain ⟨q, -, hq⟩ := hB'small (Y'' σ) (range T') (by
        rintro _ ⟨t, rfl⟩
        exact hYσ ⟨t, (congrFun (hlift T') t)⟩)
      (isPreconnected_range T'.continuous) (range_nonempty _)
    obtain ⟨g', U', hU'o, hsq', hg', hgT', hread', hJ'⟩ :=
      exists_reading_mem_simplexLifts f hf hS hcov σ (c' σ) (g σ) (U σ) hUo hsq hgσ hgT hread
        (hσS σ hσ) (fun s hs hsσ ↦ ((hSc s hs).2 σ hσ hsσ).2.1) T' (hlift T') (cX q)
        (hq.trans inter_subset_right)
    exact ⟨q, g', U', hq.trans inter_subset_left, hq.trans inter_subset_right, hU'o, hsq', hg',
      hgT', hread', hJ'⟩
  have : Nonempty (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    ⟨(hsurj (σ₀ (stdSimplex.vertex 0))).choose⟩
  choose! Yq g' U' hYB hYc hU'o hsq' hg' hgT' hread' hJ' using H
  refine ⟨z, fun T' ↦ r (pC.comp T'), Yq, fun T' ↦ cX (Yq T'), g', U', hz, ?_, ?_, ?_⟩
  · -- the triangles
    intro T' hT'
    obtain ⟨hwr, -, -, hsq, -, -, -, hJ⟩ := hgood _ (hzsupp T' hT')
    refine ⟨by rw [hzapp, hwr], hYB T' hT', hU'o T' hT', hsq' T' hT', hg' T' hT', hgT' T' hT',
      hread' T' hT', fun x hx i ↦ ?_⟩
    obtain ⟨a, ha, -, haJ⟩ := hJ' T' hT' x hx
    change 0 ≤ r (pC.comp T') * FundamentalChartCycle.chartJacobian (g' T') x i
    rw [haJ i, mul_left_comm]
    exact mul_nonneg ha (hJ x (hsq hx) i)
  · -- density
    intro W hW hWne
    have hpS : (p ⁻¹' S).Finite := hS.preimage' fun s _ ↦ hfin s
    have hW' : (W ∩ p ⁻¹' Sᶜ).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      obtain ⟨x, hx⟩ := hWne
      have hWfin : W.Finite := hpS.subset fun y hy ↦ by
        by_contra h
        exact (hne ▸ (⟨hy, h⟩ : y ∈ W ∩ p ⁻¹' Sᶜ) : y ∈ (∅ : Set _))
      apply not_isOpen_singleton_complexPoints x
      have : ({x} : Set _) = W \ (W \ {x}) := by
        ext y; constructor
        · rintro rfl; exact ⟨hx, fun h ↦ h.2 rfl⟩
        · rintro ⟨hy, hy'⟩; by_contra h; exact hy' ⟨hy, h⟩
      rw [this]
      exact hW.sdiff (hWfin.subset sdiff_subset).isClosed
    have hopen : IsOpen (p '' (W ∩ p ⁻¹' Sᶜ)) :=
      isOpen_image_of_isCoveringMapOn hcov
        (hW.inter (hS.isClosed.isOpen_compl.preimage hpc)) inter_subset_right
    obtain ⟨σ, hσ, x, hx, ⟨y, ⟨hyW, hyS⟩, hyσ⟩, hpos⟩ := hdense _ hopen (hW'.image p)
    have hT : ∃ T' ∈ simplexLifts p σ, T' (squareCollapse x) = y := by
      by_cases ht : squareCollapse x 0 < 1
      · exact exists_mem_simplexLifts hcov hcl hfin (hσS σ hσ) ht hyσ
      · have hall : ∀ t, σ t ∈ Sᶜ := fun t htS ↦ by
          have h1 := hσS σ hσ t htS
          have h2 : t = squareCollapse x := by
            rw [eq_vertex_zero_of_apply_zero (k := 1) (t := t) (by rw [h1]; exact lt_irrefl 1),
              eq_vertex_zero_of_apply_zero (k := 1) ht]
          exact hyS (show p y ∈ S by rw [hyσ, ← h2]; exact htS)
        have := Winding.simplyConnectedSpace_stdSimplex 2
        have := Winding.locallyPathConnectedSpace_stdSimplex 2
        obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := hcov.existsUnique_continuousMap_lifts σ hyσ hall
        exact ⟨F, hFp, hF0⟩
    obtain ⟨T', hT'σ, hT'y⟩ := hT
    have hσT : pC.comp T' = σ := (mem_simplexLifts_iff pC).1 hT'σ
    have hT'z : T' ∈ z.support := by
      rw [Finsupp.mem_support_iff, hzapp, hσT]; exact Finsupp.mem_support_iff.1 hσ
    refine ⟨T', hT'z, x, hx, hT'y ▸ hyW, fun i ↦ ?_⟩
    obtain ⟨a, -, ha, haJ⟩ := hJ' T' hT'z x hx
    have ha' := ha (by rw [hT'y]; exact hyS)
    change 0 < r (pC.comp T') * FundamentalChartCycle.chartJacobian (g' T') x i
    rw [haJ i, mul_left_comm, hσT]
    exact mul_pos ha' (hpos i)
  · -- the fundamental class, from a simple point
    set x₀ := σ₀ (squareCollapse p₀)
    have hp₀sq : p₀ ∈ unitSquare := ⟨⟨hp₀.1.1.le, hp₀.1.2.le⟩, ⟨hp₀.2.1.le, hp₀.2.2.le⟩⟩
    have ht₀ : squareCollapse p₀ 0 < 1 := by
      rw [squareCollapse_apply_zero hp₀sq]; linarith [hp₀.1.1]
    have hx₀S : x₀ ∉ S := fun h ↦ by
      have := hσS σ₀ hσ₀ _ h
      linarith
    obtain ⟨y₀, hy₀⟩ := hsurj x₀
    obtain ⟨T₀, hT₀, hT₀y⟩ := exists_mem_simplexLifts hcov hcl hfin (hσS σ₀ hσ₀) ht₀ hy₀
    have hσT₀ : pC.comp T₀ = σ₀ := (mem_simplexLifts_iff pC).1 hT₀
    have hz₀ : z T₀ = 1 := by rw [hzapp, hσT₀, hw₀]
    have hT₀z : T₀ ∈ z.support := by rw [Finsupp.mem_support_iff, hz₀]; exact one_ne_zero
    obtain ⟨a, -, ha, haJ⟩ := hJ' T₀ hT₀z p₀ hp₀sq
    have ha' := ha (by rw [hT₀y]; exact fun h ↦ hx₀S (by rwa [mem_preimage, hy₀] at h))
    refine isVarietyFundamentalClass_of_simplePoint z hz hT₀z (cX (Yq T₀)) (g' T₀) (U' T₀)
      (hU'o T₀ hT₀z) (hsq' T₀ hT₀z) (hg' T₀ hT₀z) (hgT' T₀ hT₀z) (hread' T₀ hT₀z) hp₀ hz₀
      (fun i ↦ by rw [haJ i, hσT₀]; exact mul_pos ha' (hJ₀ i)) (fun t ht ↦ ?_) ?_
    · apply hinj₀
      have h1 := congrArg p ht
      rwa [show p (T₀ t) = σ₀ t from congrFun hT₀ t,
        show p (T₀ (squareCollapse p₀)) = σ₀ (squareCollapse p₀) from congrFun hT₀ _] at h1
    · intro T' hT' hne ⟨t, ht⟩
      have hσ' := hzsupp T' hT'
      have hpt : (pC.comp T') t = x₀ := by
        change p (T' t) = _; rw [ht, hT₀y, hy₀]
      have hσeq : pC.comp T' = σ₀ := by
        by_contra hne'
        exact hsimple₀ _ hσ' hne' ⟨t, hpt⟩
      have htt : t = squareCollapse p₀ := hinj₀ t (by rw [← hσeq]; exact hpt)
      apply hne
      refine eq_of_mem_simplexLifts hcov (hσS σ₀ hσ₀) (by rw [← hσeq]; exact hlift T') hT₀ ht₀ ?_
      exact (congrArg T' htt).symm.trans ht

end Curve

end MMP.Analytic.ChartConeCellulation
