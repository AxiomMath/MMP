module

public import MMP.Analysis.Convex.FiniteDimensional

/-!
# Supporting forms of a face of a closed cone

Let `V` be a finite-dimensional real vector space and `C ⊆ V` a closed convex cone with
`C ∩ (-C) = {0}`. Suppose `C = C' + R₁ + ⋯ + R_k` for a closed convex cone `C' ⊆ C` and rays
`Rᵢ ⊆ C`, and let `F` be a convex extremal face of `C` with `F ∩ C' = {0}`. The linear forms
`λ ∈ V^*` which are nonnegative on `C` and whose zero set on `C` is exactly `F` form a nonempty
subset of the annihilator `⟨F⟩^⊥` of the span of `F`, open in `⟨F⟩^⊥`, and stable under
multiplication by positive reals.

## Main results

* `MMP.Positivity.IsExtremalFace.supportingForms_nonempty_isOpen`

## Implementation notes

The annihilator `⟨F⟩^⊥` is `(Submodule.span ℝ F).dualAnnihilator`, a subspace of
`Module.Dual ℝ V`. Openness in it is for its canonical topology as a finite-dimensional real
vector space, `moduleTopology ℝ`. The decomposition `C = C' + R₁ + ⋯ + R_k` is written, as in
`MMP.Positivity.IsExtremalFace.eq_sum_rays`, with the rays `MMP.Positivity.ray (v i)`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, proof of Theorem 3.7.
-/

@[expose] public section

namespace MMP.Positivity

open MMP.Mori

section Ray

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem isCone_ray (v : E) : IsCone ℝ (ray v) :=
  ⟨⟨0, le_rfl, zero_smul _ _⟩, by
    rintro _ ⟨t, ht, rfl⟩ c hc
    exact ⟨c * t, mul_nonneg hc.le ht, (smul_smul c t v).symm⟩⟩

private theorem add_mem_ray (v : E) : ∀ u ∈ ray v, ∀ w ∈ ray v, u + w ∈ ray v := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  exact ⟨s + t, add_nonneg hs ht, add_smul s t v⟩

omit [Module ℝ E] in
/-- A finite sum of elements of an additive set containing `0` lies in it. -/
private theorem sum_mem_of_add {N : Set E} (h0 : (0 : E) ∈ N)
    (hadd : ∀ u ∈ N, ∀ w ∈ N, u + w ∈ N) {ι : Type*} (s : Finset ι) (c : ι → E)
    (hc : ∀ i ∈ s, c i ∈ N) : ∑ i ∈ s, c i ∈ N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact hadd _ (hc j (Finset.mem_insert_self j s)) _
      (ih fun i hi => hc i (Finset.mem_insert_of_mem hi))

/-- The sums `∑ j, c j` with `c j ∈ D j`, for a finite family of cones `D`, form a cone. -/
theorem isCone_setOf_sum {ι : Type*} [Fintype ι] {D : ι → Set E} (hD : ∀ j, IsCone ℝ (D j)) :
    IsCone ℝ {x | ∃ c : ι → E, (∀ j, c j ∈ D j) ∧ x = ∑ j, c j} := by
  refine ⟨⟨0, fun j => (hD j).1, by simp⟩, ?_⟩
  rintro _ ⟨c, hc, rfl⟩ t ht
  exact ⟨fun j => t • c j, fun j => (hD j).2 _ (hc j) t ht, by rw [Finset.smul_sum]⟩

/-- The sums `∑ j, c j` with `c j ∈ D j`, for a finite family of additively closed cones `D`,
form a convex set. -/
theorem convex_setOf_sum {ι : Type*} [Fintype ι] {D : ι → Set E} (hD : ∀ j, IsCone ℝ (D j))
    (hDadd : ∀ j, ∀ u ∈ D j, ∀ w ∈ D j, u + w ∈ D j) :
    Convex ℝ {x | ∃ c : ι → E, (∀ j, c j ∈ D j) ∧ x = ∑ j, c j} := by
  intro x hx y hy a b ha hb _
  obtain ⟨c, hc, h₁⟩ := smul_mem_of_isCone (isCone_setOf_sum hD) hx ha
  obtain ⟨d, hd, h₂⟩ := smul_mem_of_isCone (isCone_setOf_sum hD) hy hb
  exact ⟨fun j => c j + d j, fun j => hDadd j _ (hc j) _ (hd j),
    by rw [h₁, h₂, Finset.sum_add_distrib]⟩

/-- A ray meeting a cone `F` in a positive multiple of its generator lies in `F`. -/
theorem ray_subset_of_smul_mem {F : Set E} (hF : IsCone ℝ F) {v : E} {t : ℝ} (ht : 0 < t)
    (h : t • v ∈ F) : ray v ⊆ F := by
  rintro _ ⟨c, hc, rfl⟩
  have := smul_mem_of_isCone hF h (div_nonneg hc ht.le)
  rwa [smul_smul, div_mul_cancel₀ _ ht.ne'] at this

/-- If a finite sum of elements of an additively closed `C` lies in an extremal face `F` of `C`,
so does every summand. -/
theorem IsExtremalFace.mem_of_sum_mem {C F : Set E} (hF : IsExtremalFace ℝ C F)
    (hCadd : ∀ u ∈ C, ∀ w ∈ C, u + w ∈ C) {ι : Type*} [Fintype ι] {c : ι → E}
    (hc : ∀ j, c j ∈ C) (h : ∑ j, c j ∈ F) (j : ι) : c j ∈ F := by
  classical
  rw [← Finset.add_sum_erase Finset.univ c (Finset.mem_univ j)] at h
  exact (hF.2.2.2 _ (hc j) _ (sum_mem_of_add (hF.1 hF.2.1.1) hCadd _ _ fun i _ => hc i) h).1

/-- An element of a cone `C` in the span of a convex extremal face `F` of `C` lies in `F`. -/
theorem IsExtremalFace.mem_of_mem_span {C F : Set E} (hF : IsExtremalFace ℝ C F)
    (hFc : Convex ℝ F) {x : E} (hx : x ∈ C) (hxF : x ∈ Submodule.span ℝ F) : x ∈ F := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub_of_mem_span hF.2.1 hFc hxF
  exact (hF.2.2.2 _ hx _ (hF.1 hb) (by simpa using ha)).1

/-- Let `F` be an extremal face of `C` and `W ⊆ C` with `C = W + F` and `W ∩ ⟨F⟩ = 0`. A form is
nonnegative on `C` with zero set `F` if and only if it vanishes on `⟨F⟩` and is positive on
`W ∖ {0}`. -/
theorem IsExtremalFace.supportingForm_iff {C F W : Set E} (hF : IsExtremalFace ℝ C F)
    (hWC : W ⊆ C) (hdecomp : ∀ z ∈ C, ∃ w ∈ W, ∃ f ∈ F, z = w + f)
    (hWS : ∀ w ∈ W, w ∈ Submodule.span ℝ F → w = 0) (l : Module.Dual ℝ E) :
    ((∀ z ∈ C, 0 ≤ l z) ∧ {z | z ∈ C ∧ l z = 0} = F) ↔
      l ∈ (Submodule.span ℝ F).dualAnnihilator ∧ ∀ w ∈ W, w ≠ 0 → 0 < l w := by
  constructor
  · rintro ⟨hl0, hl⟩
    refine ⟨?_, fun w hw hw0 => ?_⟩
    · have : Submodule.span ℝ F ≤ LinearMap.ker l := by
        rw [Submodule.span_le, ← hl]
        exact fun z hz => hz.2
      rw [Submodule.mem_dualAnnihilator]
      exact fun w hw => this hw
    · refine (hl0 w (hWC hw)).lt_of_ne fun h => hw0 (hWS w hw (Submodule.subset_span ?_))
      rw [← hl]
      exact ⟨hWC hw, h.symm⟩
  · rintro ⟨hlA, hlW⟩
    rw [Submodule.mem_dualAnnihilator] at hlA
    have hlF : ∀ f ∈ F, l f = 0 := fun f hf => hlA f (Submodule.subset_span hf)
    refine ⟨fun z hz => ?_, ?_⟩
    · obtain ⟨w, hw, f, hf, rfl⟩ := hdecomp z hz
      rw [map_add, hlF f hf, add_zero]
      rcases eq_or_ne w 0 with rfl | h
      · simp
      · exact (hlW w hw h).le
    · ext z
      constructor
      · rintro ⟨hz, hlz⟩
        obtain ⟨w, hw, f, hf, rfl⟩ := hdecomp z hz
        rw [map_add, hlF f hf, add_zero] at hlz
        obtain rfl : w = 0 := Classical.byContradiction fun h => (hlW w hw h).ne' hlz
        simpa using hf
      · exact fun hz => ⟨hF.1 hz, hlF z hz⟩

end Ray

section Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
private theorem isClosed_ray (v : V) : IsClosed (ray v) := by
  have : ray v = (fun x : ℝ => x • v) '' Set.Ici 0 := by
    ext w
    simp [ray]
  rw [this]
  exact isClosedMap_smul_left v _ isClosed_Ici

omit [FiniteDimensional ℝ V] in
/-- Let `C = C' + ∑ᵢ ray (v i)` and `F` an extremal face of `C` with `F ∩ C' = {0}`. Then `C'`
and the rays `ray (v i) ⊄ F` form a family of closed convex cones in `C`, each meeting `F` only in
`0`, whose sums together with `F` exhaust `C`. -/
theorem IsExtremalFace.exists_cones_sum_add_face {C C' F : Set V} (hC : IsCone ℝ C)
    (hC' : IsCone ℝ C') (hC'c : Convex ℝ C') (hC'cl : IsClosed C') (hC'C : C' ⊆ C) {k : ℕ}
    (v : Fin k → V) (hvC : ∀ i, ray (v i) ⊆ C)
    (hsum : C = {x | ∃ c ∈ C', ∃ r : Fin k → V, (∀ i, r i ∈ ray (v i)) ∧ x = c + ∑ i, r i})
    (hF : IsExtremalFace ℝ C F) (hFC' : F ∩ C' = {0}) :
    ∃ D : Fin (k + 1) → Set V, (∀ j, IsCone ℝ (D j) ∧ (∀ u ∈ D j, ∀ w ∈ D j, u + w ∈ D j) ∧
      IsClosed (D j) ∧ D j ⊆ C ∧ ∀ x ∈ D j, x ∈ F → x = 0) ∧
      ∀ z ∈ C, ∃ c : Fin (k + 1) → V, (∀ j, c j ∈ D j) ∧ ∃ f ∈ F, z = ∑ j, c j + f := by
  classical
  obtain ⟨D, hD0, hDs⟩ : ∃ D : Fin (k + 1) → Set V, D 0 = C' ∧
      ∀ i, D i.succ = if ray (v i) ⊆ F then ({0} : Set V) else ray (v i) :=
    ⟨Fin.cons (α := fun _ => Set V) C'
      (fun i => if ray (v i) ⊆ F then ({0} : Set V) else ray (v i)), rfl, fun _ => rfl⟩
  refine ⟨D, fun j => ?_, fun z hz => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) j
    · rw [hD0]
      exact ⟨hC', fun u hu w hw => add_mem_of_isCone_of_convex hC' hC'c hu hw, hC'cl, hC'C,
        fun x hx hxF => hFC'.subset ⟨hxF, hx⟩⟩
    · rw [hDs i]
      split_ifs with h
      · exact ⟨⟨rfl, fun x hx c _ => by simp_all⟩, fun u hu w hw => by simp_all,
          isClosed_singleton, by simpa using hC.1, fun x hx _ => hx⟩
      · refine ⟨isCone_ray _, add_mem_ray _, isClosed_ray _, hvC i, ?_⟩
        rintro _ ⟨t, ht, rfl⟩ htF
        rcases ht.lt_or_eq with ht | rfl
        · exact absurd (ray_subset_of_smul_mem hF.2.1 ht htF) h
        · exact zero_smul _ _
  rw [hsum] at hz
  obtain ⟨c, hc, r, hr, rfl⟩ := hz
  refine ⟨Fin.cons c (fun i => if ray (v i) ⊆ F then 0 else r i), fun j => ?_,
    ∑ i, (if ray (v i) ⊆ F then r i else 0), ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) j
    · simpa [hD0] using hc
    · simp only [Fin.cons_succ, hDs i]
      split_ifs <;> simp_all
  · refine sum_mem_of_add hF.2.1.1 hF.2.2.1 _ _ fun i _ => ?_
    split_ifs with h
    · exact h (hr i)
    · exact hF.2.1.1
  · rw [Fin.sum_univ_succ, Fin.cons_zero, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.cons_succ]
    split_ifs <;> simp

/-- Let `C ⊆ V` be a closed convex cone with `C ∩ (-C) = {0}`, `C = C' + ∑ᵢ ray (v i)` for a
closed convex cone `C' ⊆ C`, and `F` a convex extremal face of `C` with `F ∩ C' = {0}`. Then there
is a closed convex cone `W ⊆ C` with `C = W + F` and `W ∩ ⟨F⟩ = {0}`. -/
theorem IsExtremalFace.exists_cone_add_face {C C' F : Set V} (hC : IsCone ℝ C)
    (hCc : Convex ℝ C) (hCcl : IsClosed C) (hCs : C ∩ -C = {0}) (hC' : IsCone ℝ C')
    (hC'c : Convex ℝ C') (hC'cl : IsClosed C') (hC'C : C' ⊆ C) {k : ℕ} (v : Fin k → V)
    (hvC : ∀ i, ray (v i) ⊆ C)
    (hsum : C = {x | ∃ c ∈ C', ∃ r : Fin k → V, (∀ i, r i ∈ ray (v i)) ∧ x = c + ∑ i, r i})
    (hF : IsExtremalFace ℝ C F) (hFc : Convex ℝ F) (hFC' : F ∩ C' = {0}) :
    ∃ W : Set V, IsCone ℝ W ∧ Convex ℝ W ∧ IsClosed W ∧ W ⊆ C ∧
      (∀ z ∈ C, ∃ w ∈ W, ∃ f ∈ F, z = w + f) ∧ ∀ w ∈ W, w ∈ Submodule.span ℝ F → w = 0 := by
  have hCadd : ∀ u ∈ C, ∀ w ∈ C, u + w ∈ C := fun u hu w hw =>
    add_mem_of_isCone_of_convex hC hCc hu hw
  obtain ⟨D, hD, hdecomp⟩ :=
    IsExtremalFace.exists_cones_sum_add_face hC hC' hC'c hC'cl hC'C v hvC hsum hF hFC'
  have hWC : ∀ c : Fin (k + 1) → V, (∀ j, c j ∈ D j) → ∑ j, c j ∈ C := fun c hc =>
    sum_mem_of_add hC.1 hCadd _ _ fun j _ => (hD j).2.2.2.1 (hc j)
  refine ⟨{x | ∃ c : Fin (k + 1) → V, (∀ j, c j ∈ D j) ∧ x = ∑ j, c j},
    isCone_setOf_sum fun j => (hD j).1, convex_setOf_sum (fun j => (hD j).1) fun j => (hD j).2.1,
    isClosed_sum_cones hC hCc hCcl hCs D (fun j => (hD j).1) (fun j => (hD j).2.2.1)
      fun j => (hD j).2.2.2.1, ?_, fun z hz => ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hWC c hc
  · obtain ⟨c, hc, f, hf, rfl⟩ := hdecomp z hz
    exact ⟨_, ⟨c, hc, rfl⟩, f, hf, rfl⟩
  · rintro _ ⟨c, hc, rfl⟩ hS
    have hcF := IsExtremalFace.mem_of_sum_mem hF hCadd (fun j => (hD j).2.2.2.1 (hc j))
      (IsExtremalFace.mem_of_mem_span hF hFc (hWC c hc) hS)
    have hc0 : ∀ j, c j = 0 := fun j => (hD j).2.2.2.2 _ (hc j) (hcF j)
    simp [hc0]

/-- A closed convex cone `W` with `W ∩ (-W) = {0}` meeting a subspace `S` only in `0` admits a
linear form vanishing on `S` and positive on `W ∖ {0}`. -/
theorem exists_mem_dualAnnihilator_pos {W : Set V} (hW : IsCone ℝ W) (hWc : Convex ℝ W)
    (hWcl : IsClosed W) (hWs : W ∩ -W = {0}) {S : Submodule ℝ V}
    (hWS : ∀ w ∈ W, w ∈ S → w = 0) :
    ∃ l ∈ S.dualAnnihilator, ∀ w ∈ W, w ≠ 0 → 0 < l w := by
  let e := toEuclidean (E := V)
  have hs' : e.symm ⁻¹' W ∩ -(e.symm ⁻¹' W) = {0} := by
    apply Set.Subset.antisymm
    · intro z ⟨hz, hnz⟩
      have : e.symm z ∈ W ∩ -W := ⟨hz, by simpa using hnz⟩
      rw [hWs] at this
      simpa using this
    · rintro _ rfl
      exact ⟨by simpa using hW.1, by simpa using hW.1⟩
  have hU : e.symm ⁻¹' W ∩ (S.comap e.symm.toLinearMap : Set _) = {0} := by
    apply Set.Subset.antisymm
    · intro z ⟨hz, hzS⟩
      simpa using hWS _ hz hzS
    · rintro _ rfl
      exact ⟨by simpa using hW.1, by simp⟩
  obtain ⟨G, hGU, hGW⟩ := MMP.Resolution.Bridges.exists_dual_eq_zero_pos_of_salient
    (isCone_preimage hW e.symm.toLinearMap) (hWc.linear_preimage e.symm.toLinearMap)
    (hWcl.preimage e.symm.continuous) hs' _ hU
  refine ⟨G.comp e.toLinearMap, ?_, fun w hw hw0 => hGW (e w) ?_ ?_⟩
  · rw [Submodule.mem_dualAnnihilator]
    intro w hw
    refine hGU (e w) ?_
    change e.symm (e w) ∈ S
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  · change e.symm (e w) ∈ W
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  · exact fun h => hw0 (e.injective (h.trans e.map_zero.symm))

/-- In a subspace `A` of the dual, with its canonical topology, a property of forms which on `A`
amounts to positivity on a compact set `K` cuts out an open set. -/
private theorem isOpen_setOf_of_iff_forall_pos {A : Submodule ℝ (Module.Dual ℝ V)} {K : Set V}
    (hK : IsCompact K) (P : Module.Dual ℝ V → Prop) (hP : ∀ l ∈ A, P l ↔ ∀ w ∈ K, 0 < l w) :
    @IsOpen A (moduleTopology ℝ A) {μ : A | P μ} := by
  let : TopologicalSpace A := moduleTopology ℝ A
  have : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  have hset : {μ : A | P μ} = {μ : A | ∀ w ∈ K, 0 < (μ : Module.Dual ℝ V) w} :=
    Set.ext fun μ => hP μ.1 μ.2
  rw [hset]
  let bil : A →ₗ[ℝ] V →ₗ[ℝ] ℝ := A.subtype
  have hn : IsOpen {p : A × V | 0 < bil p.1 p.2} :=
    isOpen_lt continuous_const (IsModuleTopology.continuous_bilinear_of_finite_left bil)
  rw [isOpen_iff_forall_mem_open]
  intro μ hμ
  obtain ⟨u, w, hu, -, hμu, hKw, huw⟩ := generalized_tube_lemma (isCompact_singleton (x := μ)) hK
    hn (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      obtain rfl : a = μ := ha
      exact hμ b hb)
  exact ⟨u, fun ν hν z hz => (huw (Set.mk_mem_prod hν (hKw hz)) : 0 < bil ν z), hu, hμu rfl⟩

/-- In a subspace `A` of the dual, with its canonical topology, a property of forms which on `A`
amounts to positivity on `W ∖ {0}`, for a closed cone `W` on which some form is positive away
from `0`, cuts out an open set. -/
theorem isOpen_setOf_of_iff_pos_on_cone {A : Submodule ℝ (Module.Dual ℝ V)} {W : Set V}
    (hW : IsCone ℝ W) (hWcl : IsClosed W) {G : Module.Dual ℝ V} (hG : ∀ z ∈ W, z ≠ 0 → 0 < G z)
    (P : Module.Dual ℝ V → Prop) (hP : ∀ l ∈ A, P l ↔ ∀ w ∈ W, w ≠ 0 → 0 < l w) :
    @IsOpen A (moduleTopology ℝ A) {μ : A | P μ} := by
  refine isOpen_setOf_of_iff_forall_pos ((isCompact_slice hW hWcl hG 1).inter_right
    (isClosed_eq (LinearMap.continuous_of_finiteDimensional G) (continuous_const (y := 1)))) P
    fun l hl => (hP l hl).trans ⟨fun h w hw => ?_, fun h w hw hw0 => ?_⟩
  · obtain ⟨⟨hw, -⟩, hw1⟩ := hw
    refine h w hw ?_
    rintro rfl
    simp at hw1
  · have hGw := hG w hw hw0
    have hGs : G ((G w)⁻¹ • w) = 1 := by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hGw.ne']
    have := h _ ⟨⟨smul_mem_of_isCone hW hw (inv_nonneg.2 hGw.le), hGs.le⟩, hGs⟩
    rw [map_smul, smul_eq_mul] at this
    exact (mul_pos_iff_of_pos_left (inv_pos.2 hGw)).1 this

end Topology

/-- **Supporting forms of a face.** Let `C ⊆ V` be a closed convex cone with `C ∩ (-C) = {0}`,
`C' ⊆ C` a closed convex cone and `ray (v i) ⊆ C` rays with `C = C' + ∑ᵢ ray (v i)`, and `F` a
convex extremal face of `C` with `F ∩ C' = {0}`. Then the set of `λ ∈ V^*` with `λ ≥ 0` on `C` and
`{z ∈ C : λ z = 0} = F` is nonempty, contained in `(span F)^⊥`, open in `(span F)^⊥`, and stable
under multiplication by positive reals. -/
@[mmp "lem_mmp_foundation_km_cone_face_supporting_open"]
public theorem IsExtremalFace.supportingForms_nonempty_isOpen
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
    {C C' F : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C) (hCcl : IsClosed C)
    (hCs : C ∩ -C = {0}) (hC' : IsCone ℝ C') (hC'c : Convex ℝ C') (hC'cl : IsClosed C')
    (hC'C : C' ⊆ C) {k : ℕ} (v : Fin k → V) (hvC : ∀ i, ray (v i) ⊆ C)
    (hsum : C = {x | ∃ c ∈ C', ∃ r : Fin k → V, (∀ i, r i ∈ ray (v i)) ∧ x = c + ∑ i, r i})
    (hF : IsExtremalFace ℝ C F) (hFc : Convex ℝ F) (hFC' : F ∩ C' = {0}) :
    {l : Module.Dual ℝ V | (∀ z ∈ C, 0 ≤ l z) ∧ {z | z ∈ C ∧ l z = 0} = F}.Nonempty ∧
      {l : Module.Dual ℝ V | (∀ z ∈ C, 0 ≤ l z) ∧ {z | z ∈ C ∧ l z = 0} = F} ⊆
        (Submodule.span ℝ F).dualAnnihilator ∧
      @IsOpen _ (moduleTopology ℝ (Submodule.span ℝ F).dualAnnihilator)
        {μ : (Submodule.span ℝ F).dualAnnihilator |
          (∀ z ∈ C, 0 ≤ (μ : Module.Dual ℝ V) z) ∧
            {z | z ∈ C ∧ (μ : Module.Dual ℝ V) z = 0} = F} ∧
      ∀ l : Module.Dual ℝ V, (∀ z ∈ C, 0 ≤ l z) → {z | z ∈ C ∧ l z = 0} = F →
        ∀ t : ℝ, 0 < t → (∀ z ∈ C, 0 ≤ (t • l) z) ∧ {z | z ∈ C ∧ (t • l) z = 0} = F := by
  obtain ⟨W, hW, hWc, hWcl, hWC, hdecomp, hWS⟩ :=
    IsExtremalFace.exists_cone_add_face hC hCc hCcl hCs hC' hC'c hC'cl hC'C v hvC hsum hF hFc hFC'
  have hiff := IsExtremalFace.supportingForm_iff hF hWC hdecomp hWS
  have hWs : W ∩ -W = {0} := by
    refine Set.Subset.antisymm (fun x hx => ?_) ?_
    · rw [← hCs]
      exact ⟨hWC hx.1, hWC hx.2⟩
    · rintro _ rfl
      exact ⟨hW.1, by simpa using hW.1⟩
  obtain ⟨G, hG⟩ := exists_dual_pos_of_salient hC hCc hCcl hCs
  refine ⟨?_, fun l hl => ((hiff l).1 hl).1, ?_, fun l hl0 hl t ht => ⟨fun z hz => ?_, ?_⟩⟩
  · obtain ⟨l, hlA, hlW⟩ := exists_mem_dualAnnihilator_pos hW hWc hWcl hWs hWS
    exact ⟨l, (hiff l).2 ⟨hlA, hlW⟩⟩
  · exact isOpen_setOf_of_iff_pos_on_cone hW hWcl (fun z hz hz0 => hG z (hWC hz) hz0)
      (fun l => (∀ z ∈ C, 0 ≤ l z) ∧ {z | z ∈ C ∧ l z = 0} = F)
      fun l hl => (hiff l).trans (and_iff_right hl)
  · rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg ht.le (hl0 z hz)
  · rw [← hl]
    ext z
    simp [ht.ne']

end MMP.Positivity

end
