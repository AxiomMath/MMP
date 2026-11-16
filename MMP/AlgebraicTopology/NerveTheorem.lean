module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.PartitionOfUnity

/-!
# The nerve theorem for finite good covers

Let `X` be a paracompact Hausdorff space with a finite open cover `U : ι → Set X` such that
every nonempty intersection `U_I = ⋂ i ∈ I, U i` (`I` a nonempty finset) is contractible. Then
`X` is homotopy equivalent to the geometric realisation of the nerve of `U`, a finite simplicial
complex in `EuclideanSpace ℝ (Fin N)` whose vertices are the standard basis vectors.

The realisation of the nerve is `|N| = {t ∈ Δ | U_{supp t} ≠ ∅}` in `ι → ℝ`. A partition of unity
`φ` subordinate to `U` gives `φ : X → |N|`. For the inverse we use the cubical decomposition
of `|N|`: rescaling a point `t` so that its largest coordinate is `1` identifies `|N|` with the
union of the cubes `{u ∈ [0, 1]^ι | u = 1 on L, u = 0 off I}` over the pairs `∅ ≠ L ⊆ I` with
`U_I ≠ ∅` (this is the barycentric subdivision of the nerve, in cubical form). The faces of the
cube of `(I, L)` are the cubes of `(I \ {j}, L)` and `(I, L ∪ {j})`, so the carrier
`(I, L) ↦ U_L` shrinks along faces. By induction on the dimension `#(I \ L)`, coning off with
the contractions of the `U_L`, one builds a map `g` from the cubes to `X` carried by `U_L`, and,
in the same way but with a parameter and a time coordinate, homotopies `id ≃ g ∘ φ` (carried by
`U_L`, over the closed pieces `⋂_{i ∈ I} tsupport φᵢ`) and `φ ∘ g ≃ id` (carried by the
star-convex sets `{t ∈ Δ | U_{supp t ∪ L} ≠ ∅}`).

## Main results

* `MMP.Topology.exists_homotopyEquiv_simplicialComplex_of_contractible_cover`: the nerve
  theorem, with a finite simplicial complex in `EuclideanSpace ℝ (Fin N)`.
* `MMP.Topology.nonempty_homotopyEquiv_nerveSet`: `X` is homotopy equivalent to the
  realisation `nerveSet U ⊆ ι → ℝ` of the nerve, given a partition of unity subordinate to `U`.
* `MMP.Topology.exists_cubicalExtension`: extension of carried maps over the cubes of the nerve.
* `MMP.Topology.exists_coneExtension`: radial extension into a contractible set.
* `MMP.Topology.isCompact_space_of_finite`, `MMP.Topology.continuousOn_space_of_finite`:
  the space of a finite simplicial complex is compact, and a map continuous on each face is
  continuous on it.

## Implementation notes

The source compares `X` and the nerve through the space of pairs `(x, t)` with `t` in the
simplex of the indices of sets containing `x`, and homotopy pushouts over the simplices of the
nerve. We instead build explicit homotopy inverses by cellular induction over the cubical
subdivision; the homotopies themselves are produced by the same induction, with the cell
structure of the prisms `cube × [0, 1]`.

## References

* [A. Hatcher, *Algebraic Topology*, Corollary 4G.3][hatcher2002]
-/

open Set Function Topology Filter

namespace MMP.Topology

public noncomputable section

section Cone

/-- A contractible subset `V` of `X` carries a contraction, written as a total function
`X → ℝ → X` continuous on `V × ℝ`, starting at the identity and ending at a point of `V`. -/
theorem exists_contraction_of_contractibleSpace {X : Type*} [TopologicalSpace X] {V : Set X}
    [ContractibleSpace V] :
    ∃ p ∈ V, ∃ F : X → ℝ → X, ContinuousOn (fun q : X × ℝ ↦ F q.1 q.2) (V ×ˢ univ) ∧
      (∀ y ∈ V, ∀ s, F y s ∈ V) ∧ (∀ y ∈ V, F y 0 = y) ∧ (∀ y ∈ V, F y 1 = p) := by
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic V
  classical
  let F : X → ℝ → X := fun y s ↦
    if hy : y ∈ V then (H (projIcc 0 1 zero_le_one s, ⟨y, hy⟩) : X) else y
  refine ⟨p, p.2, F, ?_, fun y hy s ↦ by simp [F, hy], fun y hy ↦ by simp [F, hy],
    fun y hy ↦ by simp [F, hy]⟩
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  convert (show Continuous (fun q : (V ×ˢ (univ : Set ℝ) : Set (X × ℝ)) ↦
      (H (projIcc 0 1 zero_le_one q.1.2, ⟨q.1.1, q.2.1⟩) : X)) by fun_prop) using 1
  ext ⟨⟨y, s⟩, hy⟩
  have hy' : y ∈ V := hy.1
  simp [F, hy']

/-- For a gauge `ρ` centred at `c` on a cone `W`, the radial projection `c + (ρ u)⁻¹ • (u - c)` of
a point `u ≠ c` with `u - c ∈ W` lies on the sphere `{u | u - c ∈ W ∧ ρ u = 1}`. -/
theorem radialProj_mem_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : E}
    {W : Set E} (hWs : ∀ v ∈ W, ∀ a : ℝ, 0 ≤ a → a • v ∈ W) {ρ : E → ℝ}
    (hρhom : ∀ v ∈ W, ∀ a : ℝ, 0 ≤ a → ρ (c + a • v) = a * ρ (c + v))
    (hρpos : ∀ v ∈ W, v ≠ 0 → 0 < ρ (c + v)) {u : E} (hu : u - c ∈ W) (huc : u ≠ c) :
    c + (ρ u)⁻¹ • (u - c) ∈ {u | u - c ∈ W ∧ ρ u = 1} := by
  have hpos : 0 < ρ u := by simpa using hρpos _ hu (sub_ne_zero.2 huc)
  refine ⟨by simpa using hWs _ hu _ (inv_nonneg.2 hpos.le), ?_⟩
  rw [hρhom _ hu _ (inv_nonneg.2 hpos.le), add_sub_cancel, inv_mul_cancel₀ hpos.ne']

/-- Contracting a family of maps on a compact set `S` into `V`: for times near `1` and parameters
near `z`, all the values lie in a given neighbourhood of the end point of the contraction. -/
theorem eventually_forall_contraction_mem {Z E X : Type*} [TopologicalSpace Z]
    [TopologicalSpace E] [TopologicalSpace X] {V : Set X} {F : X → ℝ → X}
    (hFc : ContinuousOn (fun q : X × ℝ ↦ F q.1 q.2) (V ×ˢ univ)) {p : X}
    (hF1 : ∀ y ∈ V, F y 1 = p) {S : Set E} (hS : IsCompact S) {A : Set Z} {h : Z → E → X}
    (hh : ContinuousOn (fun q : Z × E ↦ h q.1 q.2) (A ×ˢ S)) (hhV : ∀ z ∈ A, ∀ u ∈ S, h z u ∈ V)
    {z : Z} (hz : z ∈ A) {O : Set X} (hO : O ∈ 𝓝 p) :
    ∀ᶠ a : Z × ℝ in 𝓝 (z, 1), ∀ θ ∈ S, a.1 ∈ A → F (h a.1 θ) a.2 ∈ O := by
  have hloc : ∀ θ ∈ S, ∀ᶠ w : (Z × ℝ) × E in 𝓝 ((z, 1), θ),
      w.1.1 ∈ A → w.2 ∈ S → F (h w.1.1 w.2) w.1.2 ∈ O := by
    intro θ hθ
    have hg : ContinuousWithinAt (fun w : (Z × ℝ) × E ↦ (w.1.1, w.2))
        ((A ×ˢ univ) ×ˢ S) ((z, 1), θ) := by fun_prop
    have hin : ContinuousWithinAt (fun w : (Z × ℝ) × E ↦ (h w.1.1 w.2, w.1.2))
        ((A ×ˢ univ) ×ˢ S) ((z, 1), θ) :=
      (ContinuousWithinAt.comp (g := fun q : Z × E ↦ h q.1 q.2)
        (f := fun w : (Z × ℝ) × E ↦ (w.1.1, w.2)) (x := ((z, 1), θ))
        (hh (z, θ) ⟨hz, hθ⟩) hg fun w hw ↦ ⟨hw.1.1, hw.2⟩).prodMk
        (continuous_snd.comp continuous_fst).continuousWithinAt
    have h1 : ContinuousWithinAt (fun w : (Z × ℝ) × E ↦ F (h w.1.1 w.2) w.1.2)
        ((A ×ˢ univ) ×ˢ S) ((z, 1), θ) :=
      (hFc _ ⟨hhV z hz θ hθ, mem_univ _⟩).comp hin fun w hw ↦ ⟨hhV _ hw.1.1 _ hw.2, mem_univ _⟩
    have hO' : O ∈ 𝓝 (F (h z θ) 1) := by rwa [hF1 _ (hhV z hz θ hθ)]
    filter_upwards [eventually_nhdsWithin_iff.mp (h1.eventually hO')] with w hw hwA hwS
    exact hw ⟨⟨hwA, mem_univ _⟩, hwS⟩
  exact (hS.eventually_forall_of_forall_eventually
    (P := fun (a : Z × ℝ) (θ : E) ↦ a.1 ∈ A → θ ∈ S → F (h a.1 θ) a.2 ∈ O) hloc).mono
    fun a ha θ hθ hA ↦ ha θ hθ hA hθ

/-- The radial contraction of `exists_coneExtension` is continuous: off the centre `c` it is the
contraction `F` applied to `h` at the radial projection, at time `1 - ρ`, and at `c` it is the end
point `p` of `F`. -/
theorem continuousOn_coneContraction {Z E X : Type*} [TopologicalSpace Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq E] [TopologicalSpace X] {V : Set X} {c : E} {W : Set E}
    (hWs : ∀ v ∈ W, ∀ a : ℝ, 0 ≤ a → a • v ∈ W) {ρ : E → ℝ} (hρ : Continuous ρ)
    (hρ0 : ρ c = 0) (hρhom : ∀ v ∈ W, ∀ a : ℝ, 0 ≤ a → ρ (c + a • v) = a * ρ (c + v))
    (hρpos : ∀ v ∈ W, v ≠ 0 → 0 < ρ (c + v))
    (hS : IsCompact {u | u - c ∈ W ∧ ρ u = 1}) {A : Set Z} {h : Z → E → X}
    (hh : ContinuousOn (fun q : Z × E ↦ h q.1 q.2) (A ×ˢ {u | u - c ∈ W ∧ ρ u = 1}))
    (hhV : ∀ z ∈ A, ∀ u, u - c ∈ W → ρ u = 1 → h z u ∈ V) {p : X} {F : X → ℝ → X}
    (hFc : ContinuousOn (fun q : X × ℝ ↦ F q.1 q.2) (V ×ˢ univ)) (hF1 : ∀ y ∈ V, F y 1 = p) :
    ContinuousOn (fun q : Z × E ↦
        if q.2 = c then p else F (h q.1 (c + (ρ q.2)⁻¹ • (q.2 - c))) (1 - ρ q.2))
      (A ×ˢ {u | u - c ∈ W ∧ ρ u ≤ 1}) := by
  have hπS := fun u (hu : u - c ∈ W) (huc : u ≠ c) ↦ radialProj_mem_sphere hWs hρhom hρpos hu huc
  rintro ⟨z, u⟩ ⟨hz, hu, hur⟩
  by_cases huc : u = c
  · subst huc
    simp only [ContinuousWithinAt, ite_true]
    intro O hO
    have hev := eventually_forall_contraction_mem hFc hF1 hS hh
      (fun z hz u hu ↦ hhV z hz u hu.1 hu.2) hz hO
    have htend : Tendsto (fun q : Z × E ↦ (q.1, 1 - ρ q.2)) (𝓝 (z, u)) (𝓝 (z, 1)) := by
      simpa [hρ0] using (by fun_prop : Continuous fun q : Z × E ↦ (q.1, 1 - ρ q.2)).tendsto (z, u)
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [htend.eventually hev] with q hq hqmem
    by_cases hqc : q.2 = u
    · simpa [hqc] using mem_of_mem_nhds hO
    · simpa [hqc] using hq _ (hπS q.2 hqmem.2.1 hqc) hqmem.1
  · have hopen : {q : Z × E | q.2 ≠ c} ∈ 𝓝 (z, u) :=
      (isOpen_ne_fun continuous_snd continuous_const).mem_nhds huc
    rw [← continuousWithinAt_inter hopen]
    have hπc : ContinuousOn (fun u ↦ c + (ρ u)⁻¹ • (u - c)) {u | u - c ∈ W ∧ u ≠ c} := by
      intro u hu
      have hn : ρ u ≠ 0 := (by simpa using hρpos _ hu.1 (sub_ne_zero.2 hu.2) : 0 < ρ u).ne'
      exact (continuousAt_const.add ((hρ.continuousAt.inv₀ hn).smul
        (continuous_id.sub continuous_const).continuousAt)).continuousWithinAt
    have hin : ContinuousOn (fun q : Z × E ↦ (q.1, c + (ρ q.2)⁻¹ • (q.2 - c)))
        ((A ×ˢ {u | u - c ∈ W ∧ ρ u ≤ 1}) ∩ {q | q.2 ≠ c}) :=
      continuousOn_fst.prodMk (hπc.comp continuousOn_snd fun q hq ↦ ⟨hq.1.2.1, hq.2⟩)
    have hcomp : ContinuousOn (fun q : Z × E ↦ F (h q.1 (c + (ρ q.2)⁻¹ • (q.2 - c))) (1 - ρ q.2))
        ((A ×ˢ {u | u - c ∈ W ∧ ρ u ≤ 1}) ∩ {q | q.2 ≠ c}) :=
      hFc.comp ((hh.comp hin fun q hq ↦ ⟨hq.1.1, hπS _ hq.1.2.1 hq.2⟩).prodMk
        (continuous_const.sub (hρ.comp continuous_snd)).continuousOn) fun q hq ↦
        ⟨hhV _ hq.1.1 _ (hπS _ hq.1.2.1 hq.2).1 (hπS _ hq.1.2.1 hq.2).2, mem_univ _⟩
    refine (hcomp _ ⟨⟨hz, hu, hur⟩, huc⟩).congr (fun q hq ↦ ?_) ?_
    · simp [show q.2 ≠ c from hq.2]
    · simp [huc]

/-- **Cone extension.** Let `ρ` be a continuous gauge centred at `c` on a cone `W` (positively
homogeneous along rays from `c` and positive off `c`), with compact "sphere"
`S = {u | u - c ∈ W, ρ u = 1}`. A family of maps `S → V`, parametrised continuously by
`z ∈ A`, into a contractible subset `V` extends to a family of maps on the "ball"
`{u | u - c ∈ W, ρ u ≤ 1}` with values in `V`. -/
theorem exists_coneExtension {Z E X : Type*} [TopologicalSpace Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {V : Set X} [ContractibleSpace V] {c : E}
    {W : Set E} (hWs : ∀ v ∈ W, ∀ a : ℝ, 0 ≤ a → a • v ∈ W) {ρ : E → ℝ} (hρ : Continuous ρ)
    (hρ0 : ρ c = 0) (hρhom : ∀ v ∈ W, ∀ a : ℝ, 0 ≤ a → ρ (c + a • v) = a * ρ (c + v))
    (hρpos : ∀ v ∈ W, v ≠ 0 → 0 < ρ (c + v))
    (hS : IsCompact {u | u - c ∈ W ∧ ρ u = 1}) {A : Set Z} {h : Z → E → X}
    (hh : ContinuousOn (fun q : Z × E ↦ h q.1 q.2) (A ×ˢ {u | u - c ∈ W ∧ ρ u = 1}))
    (hhV : ∀ z ∈ A, ∀ u, u - c ∈ W → ρ u = 1 → h z u ∈ V) :
    ∃ H : Z → E → X,
      ContinuousOn (fun q : Z × E ↦ H q.1 q.2) (A ×ˢ {u | u - c ∈ W ∧ ρ u ≤ 1}) ∧
      (∀ z ∈ A, ∀ u, u - c ∈ W → ρ u ≤ 1 → H z u ∈ V) ∧
      (∀ z ∈ A, ∀ u, u - c ∈ W → ρ u = 1 → H z u = h z u) := by
  classical
  obtain ⟨p, hp, F, hFc, hFV, hF0, hF1⟩ := exists_contraction_of_contractibleSpace (V := V)
  refine ⟨fun z u ↦ if u = c then p else F (h z (c + (ρ u)⁻¹ • (u - c))) (1 - ρ u),
    continuousOn_coneContraction hWs hρ hρ0 hρhom hρpos hS hh hhV hFc hF1,
    fun z hz u hu _ ↦ ?_, fun z hz u hu hur ↦ ?_⟩
  · by_cases huc : u = c
    · simp [huc, hp]
    · have hπ := radialProj_mem_sphere hWs hρhom hρpos hu huc
      simp only [huc, ite_false]
      exact hFV _ (hhV _ hz _ hπ.1 hπ.2) _
  · have huc : u ≠ c := by
      rintro rfl
      rw [hρ0] at hur
      exact zero_ne_one hur
    simp only [huc, ite_false, hur, inv_one, one_smul, add_sub_cancel, sub_self]
    exact hF0 _ (hhV _ hz _ hu hur)

end Cone

section Faces

variable {V : Type*} [Fintype V]

/-- The closed face of the standard simplex in `V → ℝ` spanned by the vertices in `c`. -/
def simplexFace (c : Finset V) : Set (V → ℝ) :=
  {t | (∀ v, 0 ≤ t v) ∧ ∑ v, t v = 1 ∧ ∀ v ∉ c, t v = 0}

/-- A face of the standard simplex is closed. -/
theorem isClosed_simplexFace (c : Finset V) : IsClosed (simplexFace c) := by
  have h1 : IsClosed {t : V → ℝ | ∀ v, 0 ≤ t v} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun v ↦ isClosed_le continuous_const (continuous_apply v)
  have h2 : IsClosed {t : V → ℝ | ∑ v, t v = 1} :=
    isClosed_eq (continuous_finsetSum _ fun v _ ↦ continuous_apply v) continuous_const
  have h3 : IsClosed {t : V → ℝ | ∀ v ∉ c, t v = 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply v) continuous_const
  exact h1.inter (h2.inter h3)

/-- Every coordinate of a point of a face of the standard simplex is at most `1`. -/
theorem le_one_of_mem_simplexFace {c : Finset V} {t : V → ℝ} (ht : t ∈ simplexFace c) (v : V) :
    t v ≤ 1 := by
  rw [← ht.2.1]
  exact Finset.single_le_sum (fun w _ ↦ ht.1 w) (Finset.mem_univ v)

/-- A face of the standard simplex is compact. -/
theorem isCompact_simplexFace (c : Finset V) : IsCompact (simplexFace c) :=
  (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset (isClosed_simplexFace c)
    fun _ ht ↦ Set.mem_univ_pi.2 fun v ↦ ⟨ht.1 v, le_one_of_mem_simplexFace ht v⟩

/-- The face spanned by `c` is contained in the face spanned by any `d ⊇ c`. -/
theorem simplexFace_mono {c d : Finset V} (h : c ⊆ d) : simplexFace c ⊆ simplexFace d :=
  fun _ ht ↦ ⟨ht.1, ht.2.1, fun v hv ↦ ht.2.2 v fun hc ↦ hv (h hc)⟩

/-- The support of a point of the face spanned by `c` is contained in `c`. -/
theorem filter_subset_of_mem_simplexFace {c : Finset V} {t : V → ℝ}
    (ht : t ∈ simplexFace c) : Finset.univ.filter (t · ≠ 0) ⊆ c := by
  intro v hv
  by_contra hvc
  simp only [Finset.mem_filter] at hv
  exact hv.2 (ht.2.2 v hvc)

/-- A point of a face of the standard simplex lies in the face spanned by its support. -/
theorem mem_simplexFace_filter {c : Finset V} {t : V → ℝ} (ht : t ∈ simplexFace c) :
    t ∈ simplexFace (Finset.univ.filter (t · ≠ 0)) :=
  ⟨ht.1, ht.2.1, fun v hv ↦ by simpa using hv⟩

/-- A point of a face of the standard simplex has nonempty support. -/
theorem filter_nonempty_of_mem_simplexFace {c : Finset V} {t : V → ℝ}
    (ht : t ∈ simplexFace c) : (Finset.univ.filter (t · ≠ 0)).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
  have : ∑ v, t v = 0 := Finset.sum_eq_zero fun v _ ↦ by simpa using h (Finset.mem_univ v)
  rw [ht.2.1] at this
  exact one_ne_zero this

/-- The time parameter: `[0, 1]` for homotopies (`b = true`), `{0}` for maps (`b = false`). -/
def timeSet (b : Bool) : Set ℝ := if b then Icc 0 1 else {0}

/-- The ends of the time parameter, where data is prescribed. -/
def endSet (b : Bool) : Set ℝ := if b then {0, 1} else ∅

/-- The ends of the time parameter lie in its range. -/
theorem endSet_subset_timeSet (b : Bool) : endSet b ⊆ timeSet b := by
  cases b
  · simp [endSet]
  · simp only [endSet, timeSet, ite_true]
    rintro x (rfl | rfl) <;> simp

/-- The range of the time parameter is compact. -/
theorem isCompact_timeSet (b : Bool) : IsCompact (timeSet b) := by
  cases b
  · simp [timeSet]
  · simpa [timeSet] using isCompact_Icc

/-- The range of the time parameter is closed. -/
theorem isClosed_timeSet (b : Bool) : IsClosed (timeSet b) := (isCompact_timeSet b).isClosed

/-- The set of ends of the time parameter is closed. -/
theorem isClosed_endSet (b : Bool) : IsClosed (endSet b) := by
  cases b
  · simp [endSet]
  · simp only [endSet, ite_true]
    exact (Set.toFinite ({0, 1} : Set ℝ)).isClosed

/-- The cube `{u | u = 1 on L, 0 ≤ u ≤ 1, u = 0 off I}`; for `L ⊆ I` it is a face of the unit cube,
of dimension `#(I \ L)`. -/
def cubeFace (I L : Finset V) : Set (V → ℝ) :=
  {u | (∀ i ∈ L, u i = 1) ∧ (∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ ∀ i ∉ I, u i = 0}

omit [Fintype V] in
/-- The cube `cubeFace I L` is closed. -/
theorem isClosed_cubeFace (I L : Finset V) : IsClosed (cubeFace I L) := by
  simp only [cubeFace, ofPred_and, ofPred_forall]
  refine (isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
    isClosed_eq (continuous_apply i) continuous_const).inter
    ((isClosed_iInter fun i ↦ (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)).inter
    (isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply i) continuous_const))

omit [Fintype V] in
/-- The cube `cubeFace I L` is compact. -/
theorem isCompact_cubeFace (I L : Finset V) : IsCompact (cubeFace I L) :=
  (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset (isClosed_cubeFace I L)
    fun _ hu ↦ Set.mem_univ_pi.2 fun i ↦ hu.2.1 i

omit [Fintype V] in
/-- `cubeFace I L` is monotone in `I` and antitone in `L`. -/
theorem cubeFace_anti {I I' L L' : Finset V} (hI : I ⊆ I') (hL : L ⊆ L') :
    cubeFace I L' ⊆ cubeFace I' L :=
  fun _ hu ↦ ⟨fun i hi ↦ hu.1 i (hL hi), hu.2.1, fun i hi ↦ hu.2.2 i fun h ↦ hi (hI h)⟩

variable [DecidableEq V]

/-- The boundary of the prism `cubeFace I L ×ˢ timeSet b`. -/
def cubeBoundary (b : Bool) (I L : Finset V) : Set ((V → ℝ) × ℝ) :=
  cubeFace I L ×ˢ endSet b ∪
    ⋃ j ∈ I \ L, (cubeFace (I.erase j) L ∪ cubeFace I (insert j L)) ×ˢ timeSet b

omit [Fintype V] in
/-- The boundary of the prism `cubeFace I L ×ˢ timeSet b` is compact. -/
theorem isCompact_cubeBoundary (b : Bool) (I L : Finset V) :
    IsCompact (cubeBoundary b I L) := by
  refine ((isCompact_cubeFace I L).prod ((isCompact_timeSet b).of_isClosed_subset
    (isClosed_endSet b) (endSet_subset_timeSet b))).union ?_
  exact (I \ L).isCompact_biUnion fun j _ ↦
    ((isCompact_cubeFace _ _).union (isCompact_cubeFace _ _)).prod (isCompact_timeSet b)

omit [Fintype V] in
/-- The boundary of the prism `cubeFace I L ×ˢ timeSet b` is contained in the prism. -/
theorem cubeBoundary_subset (b : Bool) (I L : Finset V) :
    cubeBoundary b I L ⊆ cubeFace I L ×ˢ timeSet b := by
  rintro u (hu | hu)
  · exact ⟨hu.1, endSet_subset_timeSet b hu.2⟩
  · simp only [mem_iUnion] at hu
    obtain ⟨j, -, hu | hu, hτ⟩ := hu
    · exact ⟨cubeFace_anti (Finset.erase_subset j I) le_rfl hu, hτ⟩
    · exact ⟨cubeFace_anti le_rfl (Finset.subset_insert j L) hu, hτ⟩

omit [DecidableEq V] in
/-- The sup norm of `x` is at most `1 / 2` if and only if every coordinate has absolute value at
most `1 / 2`. -/
theorem norm_le_half_iff {x : V → ℝ} : ‖x‖ ≤ 1 / 2 ↔ ∀ i, |x i| ≤ 1 / 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  simp

omit [DecidableEq V] in
/-- The sup norm of `x` is at least `1 / 2` if and only if some coordinate has absolute value at
least `1 / 2`. -/
theorem half_le_norm_iff {x : V → ℝ} : 1 / 2 ≤ ‖x‖ ↔ ∃ i, 1 / 2 ≤ |x i| := by
  rw [← not_iff_not, not_le, pi_norm_lt_iff (by norm_num)]
  simp

/-- `|x - 1 / 2| ≤ 1 / 2` if and only if `x ∈ [0, 1]`. -/
theorem abs_sub_half_le_half_iff {x : ℝ} : |x - 1 / 2| ≤ 1 / 2 ↔ 0 ≤ x ∧ x ≤ 1 := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- `1 / 2 ≤ |x - 1 / 2|` if and only if `x ≤ 0` or `1 ≤ x`. -/
theorem half_le_abs_sub_half_iff {x : ℝ} : 1 / 2 ≤ |x - 1 / 2| ↔ x ≤ 0 ∨ 1 ≤ x := by
  rw [le_abs']
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- The time range `timeSet b` is the set of times at distance at most `1 / 2` from its centre
(for `b = false`, the time is pinned to the centre `0`). -/
theorem abs_sub_le_half_iff_mem_timeSet {b : Bool} {τ : ℝ}
    (hτ : b = false → τ = if b then 1 / 2 else 0) :
    |τ - (if b then 1 / 2 else 0)| ≤ 1 / 2 ↔ τ ∈ timeSet b := by
  cases b
  · simp [hτ rfl, timeSet]
  · simp only [timeSet, ite_true, mem_Icc]
    exact abs_sub_half_le_half_iff

/-- A time of `timeSet b` is in `endSet b` if and only if it is at distance at least `1 / 2` from
the centre of `timeSet b`. -/
theorem half_le_abs_sub_iff_mem_endSet {b : Bool} {τ : ℝ}
    (hτ : b = false → τ = if b then 1 / 2 else 0) (hle : |τ - (if b then 1 / 2 else 0)| ≤ 1 / 2) :
    1 / 2 ≤ |τ - (if b then 1 / 2 else 0)| ↔ τ ∈ endSet b := by
  cases b
  · simp [hτ rfl, endSet]
  · simp only [endSet, ite_true, mem_insert_iff, mem_singleton_iff] at hle ⊢
    obtain ⟨h₀, h₁⟩ := abs_sub_half_le_half_iff.1 hle
    rw [half_le_abs_sub_half_iff]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- For `b = false`, the only time of `timeSet b` is the centre `0`. -/
theorem eq_of_mem_timeSet {b : Bool} {τ : ℝ} (hτ : τ ∈ timeSet b) :
    b = false → τ = if b then 1 / 2 else 0 := by
  rintro rfl
  simpa [timeSet] using hτ

omit [Fintype V] in
/-- The centre of the prism `cubeFace I L ×ˢ timeSet b`. -/
def prismCentre (b : Bool) (I L : Finset V) : (V → ℝ) × ℝ :=
  (fun i ↦ if i ∈ L then 1 else if i ∈ I then 1 / 2 else 0, if b then 1 / 2 else 0)

omit [Fintype V] in
/-- The directions in which the prism `cubeFace I L ×ˢ timeSet b` extends from its centre. -/
def prismCone (b : Bool) (I L : Finset V) : Set ((V → ℝ) × ℝ) :=
  {w | (∀ i, (i ∈ L ∨ i ∉ I) → w.1 i = 0) ∧ (b = false → w.2 = 0)}

omit [Fintype V] in
/-- `u - prismCentre b I L ∈ prismCone b I L` if and only if `u` is `1` on `L`, `0` off `I`, and
(for `b = false`) at time `0`. -/
theorem sub_prismCentre_mem_prismCone_iff {b : Bool} {I L : Finset V} (hLI : L ⊆ I)
    {u : (V → ℝ) × ℝ} : u - prismCentre b I L ∈ prismCone b I L ↔
      (∀ i ∈ L, u.1 i = 1) ∧ (∀ i ∉ I, u.1 i = 0) ∧
        (b = false → u.2 = if b then 1 / 2 else 0) := by
  obtain ⟨t, τ⟩ := u
  simp only [prismCone, prismCentre, mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply,
    sub_eq_zero]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i hi ↦ by simpa [hi] using h₁ i (Or.inl hi), fun i hi ↦ ?_, h₂⟩
    simpa [hi, show i ∉ L from fun h ↦ hi (hLI h)] using h₁ i (Or.inr hi)
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨fun i hi ↦ ?_, h₃⟩
    rcases hi with hi | hi
    · simp [hi, h₁ i hi]
    · simp [hi, show i ∉ L from fun h ↦ hi (hLI h), h₂ i hi]

/-- On the slice through `prismCentre b I L`, the gauge `2 * ‖u - prismCentre b I L‖` is at most
`1` if and only if `u` lies in the prism. -/
theorem two_mul_norm_sub_prismCentre_le_one_iff {b : Bool} {I L : Finset V} (hLI : L ⊆ I)
    {u : (V → ℝ) × ℝ} (hu : u - prismCentre b I L ∈ prismCone b I L) :
    2 * ‖u - prismCentre b I L‖ ≤ 1 ↔
      (∀ i ∈ I, i ∉ L → 0 ≤ u.1 i ∧ u.1 i ≤ 1) ∧ |u.2 - (if b then 1 / 2 else 0)| ≤ 1 / 2 := by
  obtain ⟨h₁, h₂, -⟩ := (sub_prismCentre_mem_prismCone_iff hLI).1 hu
  have : 2 * ‖u - prismCentre b I L‖ ≤ 1 ↔ ‖u - prismCentre b I L‖ ≤ 1 / 2 := by
    constructor <;> intro h <;> linarith
  rw [this, Prod.norm_def, max_le_iff, norm_le_half_iff]
  simp only [prismCentre, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Real.norm_eq_abs]
  refine and_congr ⟨fun h i hi hiL ↦ ?_, fun h i ↦ ?_⟩ Iff.rfl
  · have := h i
    simp only [hiL, hi, ite_false, ite_true] at this
    exact abs_sub_half_le_half_iff.1 this
  · by_cases hiL : i ∈ L
    · norm_num [hiL, h₁ i hiL]
    by_cases hiI : i ∈ I
    · simp only [hiL, hiI, ite_false, ite_true]
      exact abs_sub_half_le_half_iff.2 (h i hiI hiL)
    · norm_num [hiL, hiI, h₂ i hiI]

/-- On the slice through `prismCentre b I L`, the gauge `2 * ‖u - prismCentre b I L‖` is at least
`1` if and only if `u` is on a face of the cube or at an end of the time range. -/
theorem one_le_two_mul_norm_sub_prismCentre_iff {b : Bool} {I L : Finset V} (hLI : L ⊆ I)
    {u : (V → ℝ) × ℝ} (hu : u - prismCentre b I L ∈ prismCone b I L) :
    1 ≤ 2 * ‖u - prismCentre b I L‖ ↔
      (∃ i ∈ I, i ∉ L ∧ (u.1 i ≤ 0 ∨ 1 ≤ u.1 i)) ∨ 1 / 2 ≤ |u.2 - (if b then 1 / 2 else 0)| := by
  obtain ⟨h₁, h₂, -⟩ := (sub_prismCentre_mem_prismCone_iff hLI).1 hu
  have : 1 ≤ 2 * ‖u - prismCentre b I L‖ ↔ 1 / 2 ≤ ‖u - prismCentre b I L‖ := by
    constructor <;> intro h <;> linarith
  rw [this, Prod.norm_def, le_max_iff, half_le_norm_iff]
  simp only [prismCentre, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Real.norm_eq_abs]
  refine or_congr ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨i, hi, hiL, h⟩ ↦ ⟨i, ?_⟩⟩ Iff.rfl
  · by_cases hiL : i ∈ L
    · norm_num [hiL, h₁ i hiL] at hi
    by_cases hiI : i ∈ I
    · simp only [hiL, hiI, ite_false, ite_true] at hi
      exact ⟨i, hiI, hiL, half_le_abs_sub_half_iff.1 hi⟩
    · norm_num [hiL, hiI, h₂ i hiI] at hi
  · simp only [hi, hiL, ite_false, ite_true]
    exact half_le_abs_sub_half_iff.2 h

/-- The prism `cubeFace I L ×ˢ timeSet b` is the unit ball of the gauge
`2 * ‖u - prismCentre b I L‖` on the slice through `prismCentre b I L`. -/
theorem prismBall_eq {b : Bool} {I L : Finset V} (hLI : L ⊆ I) :
    {u | u - prismCentre b I L ∈ prismCone b I L ∧ 2 * ‖u - prismCentre b I L‖ ≤ 1} =
      cubeFace I L ×ˢ timeSet b := by
  ext ⟨t, τ⟩
  simp only [mem_ofPred_eq, mem_prod, cubeFace]
  constructor
  · rintro ⟨hu, hρu⟩
    obtain ⟨h₁, h₂, h₃⟩ := (sub_prismCentre_mem_prismCone_iff hLI).1 hu
    obtain ⟨h₄, h₅⟩ := (two_mul_norm_sub_prismCentre_le_one_iff hLI hu).1 hρu
    refine ⟨⟨h₁, fun i ↦ ?_, h₂⟩, (abs_sub_le_half_iff_mem_timeSet h₃).1 h₅⟩
    by_cases hi : i ∈ L
    · norm_num [show t i = 1 from h₁ i hi]
    by_cases hi' : i ∈ I
    · exact h₄ i hi' hi
    · norm_num [show t i = 0 from h₂ i hi']
  · rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩
    have hu := (sub_prismCentre_mem_prismCone_iff (u := (t, τ)) hLI).2
      ⟨h₁, h₃, eq_of_mem_timeSet h₄⟩
    exact ⟨hu, (two_mul_norm_sub_prismCentre_le_one_iff hLI hu).2
      ⟨fun i _ _ ↦ h₂ i, (abs_sub_le_half_iff_mem_timeSet (eq_of_mem_timeSet h₄)).2 h₄⟩⟩

/-- The boundary `cubeBoundary b I L` of the prism is the unit sphere of the gauge
`2 * ‖u - prismCentre b I L‖` on the slice through `prismCentre b I L`. -/
theorem prismSphere_eq {b : Bool} {I L : Finset V} (hLI : L ⊆ I) :
    {u | u - prismCentre b I L ∈ prismCone b I L ∧ 2 * ‖u - prismCentre b I L‖ = 1} =
      cubeBoundary b I L := by
  have : {u | u - prismCentre b I L ∈ prismCone b I L ∧ 2 * ‖u - prismCentre b I L‖ = 1} =
      {u | u - prismCentre b I L ∈ prismCone b I L ∧ 2 * ‖u - prismCentre b I L‖ ≤ 1} ∩
        {u | u - prismCentre b I L ∈ prismCone b I L ∧ 1 ≤ 2 * ‖u - prismCentre b I L‖} := by
    ext u
    simp only [mem_ofPred_eq, mem_inter_iff, le_antisymm_iff]
    tauto
  rw [this, prismBall_eq hLI]
  ext ⟨t, τ⟩
  simp only [mem_inter_iff, mem_prod, mem_ofPred_eq, cubeBoundary, mem_union, mem_iUnion,
    exists_prop]
  constructor
  · rintro ⟨⟨ht, hτ⟩, hu, hge⟩
    have h₀ := eq_of_mem_timeSet hτ
    rcases (one_le_two_mul_norm_sub_prismCentre_iff hLI hu).1 hge with
      ⟨i, hi, hiL, hz | ho⟩ | hτ'
    · right
      refine ⟨i, Finset.mem_sdiff.2 ⟨hi, hiL⟩, Or.inl ⟨ht.1, ht.2.1, fun w hw ↦ ?_⟩, hτ⟩
      by_cases hwi : w = i
      · subst hwi
        exact le_antisymm hz (ht.2.1 w).1
      · exact ht.2.2 w fun hwc ↦ hw (Finset.mem_erase.2 ⟨hwi, hwc⟩)
    · right
      refine ⟨i, Finset.mem_sdiff.2 ⟨hi, hiL⟩, Or.inr ⟨fun w hw ↦ ?_, ht.2.1, ht.2.2⟩, hτ⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact le_antisymm (ht.2.1 w).2 ho
      · exact ht.1 w hw
    · exact Or.inl ⟨ht, (half_le_abs_sub_iff_mem_endSet h₀
        ((abs_sub_le_half_iff_mem_timeSet h₀).2 hτ)).1 hτ'⟩
  · rintro (⟨ht, hτ⟩ | ⟨i, hi, ht, hτ⟩)
    · have hτ₁ := endSet_subset_timeSet b hτ
      have h₀ := eq_of_mem_timeSet hτ₁
      have hu := (sub_prismCentre_mem_prismCone_iff (u := (t, τ)) hLI).2 ⟨ht.1, ht.2.2, h₀⟩
      exact ⟨⟨ht, hτ₁⟩, hu, (one_le_two_mul_norm_sub_prismCentre_iff hLI hu).2 (Or.inr
        ((half_le_abs_sub_iff_mem_endSet h₀ ((abs_sub_le_half_iff_mem_timeSet h₀).2 hτ₁)).2 hτ))⟩
    · obtain ⟨hiI, hiL⟩ := Finset.mem_sdiff.1 hi
      have ht' : t ∈ cubeFace I L :=
        Or.elim ht (fun h ↦ cubeFace_anti (Finset.erase_subset i I) le_rfl h)
          fun h ↦ cubeFace_anti le_rfl (Finset.subset_insert i L) h
      have hu := (sub_prismCentre_mem_prismCone_iff (u := (t, τ)) hLI).2
        ⟨ht'.1, ht'.2.2, eq_of_mem_timeSet hτ⟩
      refine ⟨⟨ht', hτ⟩, hu, (one_le_two_mul_norm_sub_prismCentre_iff hLI hu).2
        (Or.inl ⟨i, hiI, hiL, ?_⟩)⟩
      exact Or.elim ht (fun ht ↦ Or.inl (ht.2.2 i (Finset.notMem_erase i I)).le)
        fun ht ↦ Or.inr (ht.1 i (Finset.mem_insert_self i L)).ge

omit [Fintype V] in
/-- **Extension over a prism.** A family of maps from the boundary of the prism
`cubeFace I L ×ˢ timeSet b` into a contractible set, parametrised continuously by `z ∈ A`,
extends over the prism. -/
theorem exists_cubeExtension [Finite V] {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    {C : Set Y} [ContractibleSpace C] (b : Bool) {I L : Finset V} (hLI : L ⊆ I) {A : Set Z}
    {h : Z → (V → ℝ) × ℝ → Y}
    (hh : ContinuousOn (fun q : Z × ((V → ℝ) × ℝ) ↦ h q.1 q.2) (A ×ˢ cubeBoundary b I L))
    (hhC : ∀ z ∈ A, ∀ u ∈ cubeBoundary b I L, h z u ∈ C) :
    ∃ H : Z → (V → ℝ) × ℝ → Y,
      ContinuousOn (fun q : Z × ((V → ℝ) × ℝ) ↦ H q.1 q.2)
        (A ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
      (∀ z ∈ A, ∀ u ∈ cubeFace I L ×ˢ timeSet b, H z u ∈ C) ∧
      ∀ z ∈ A, ∀ u ∈ cubeBoundary b I L, H z u = h z u := by
  have := Fintype.ofFinite V
  have hρ : Continuous fun u : (V → ℝ) × ℝ ↦ 2 * ‖u - prismCentre b I L‖ := by fun_prop
  have hB := prismBall_eq (b := b) hLI
  have hS := prismSphere_eq (b := b) hLI
  obtain ⟨H, hHc, hHC, hHeq⟩ := exists_coneExtension (V := C) (c := prismCentre b I L)
    (W := prismCone b I L)
    (fun w hw a _ ↦ ⟨fun i hi ↦ by simp [hw.1 i hi], fun hb ↦ by simp [hw.2 hb]⟩) hρ (by simp)
    (fun w _ a ha ↦ by
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      ring)
    (fun w _ hw ↦ by simpa using norm_pos_iff.2 hw)
    (hS ▸ isCompact_cubeBoundary b I L) (A := A) (h := h) (by rwa [hS])
    (fun z hz u hu hu1 ↦ hhC z hz u (hS ▸ ⟨hu, hu1⟩))
  refine ⟨H, by rwa [← hB], fun z hz u hu ↦ ?_, fun z hz u hu ↦ ?_⟩
  · rw [← hB] at hu
    exact hHC z hz u hu.1 hu.2
  · rw [← hS] at hu
    exact hHeq z hz u hu.1 hu.2

end Faces

section Pasting

variable {Z E Y : Type*} [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace Y]
  {f : Z × E → Y} {s : Set Z}

/-- A function continuous on `s ×ˢ K₁` and on `s ×ˢ K₂`, for closed `K₁` and `K₂`, is continuous on
`s ×ˢ (K₁ ∪ K₂)`. -/
theorem continuousOn_prod_union {K₁ K₂ : Set E} (h₁ : IsClosed K₁) (h₂ : IsClosed K₂)
    (hf₁ : ContinuousOn f (s ×ˢ K₁)) (hf₂ : ContinuousOn f (s ×ˢ K₂)) :
    ContinuousOn f (s ×ˢ (K₁ ∪ K₂)) := by
  have key : ∀ {K : Set E}, IsClosed K → ContinuousOn f (s ×ˢ K) → ∀ p ∈ s ×ˢ (K₁ ∪ K₂),
      ContinuousWithinAt f (s ×ˢ K) p := by
    intro K hK hf p hp
    by_cases hpK : p.2 ∈ K
    · exact hf p ⟨hp.1, hpK⟩
    · refine continuousWithinAt_of_notMem_closure fun hcl ↦ hpK ?_
      have : closure (s ×ˢ K) ⊆ univ ×ˢ K :=
        closure_minimal (prod_mono (subset_univ s) le_rfl) (isClosed_univ.prod hK)
      exact (this hcl).2
  intro p hp
  rw [prod_union]
  exact (key h₁ hf₁ p hp).union (key h₂ hf₂ p hp)

/-- A function continuous on each `s ×ˢ K k`, for a finite family of closed sets `K k`, is
continuous on `s ×ˢ ⋃ k ∈ T, K k`. -/
theorem continuousOn_prod_biUnion {κ : Type*} {T : Finset κ} {K : κ → Set E}
    (hK : ∀ k ∈ T, IsClosed (K k)) (hf : ∀ k ∈ T, ContinuousOn f (s ×ˢ K k)) :
    ContinuousOn f (s ×ˢ ⋃ k ∈ T, K k) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hK hf
    rw [Finset.set_biUnion_insert]
    exact continuousOn_prod_union hK.1 (isClosed_biUnion_finset hK.2) hf.1 (ih hK.2 hf.2)

/-- A function equal to `f₀` at time `0` and to `f₁` at time `1` is continuous on the ends
`s ×ˢ (K ×ˢ endSet true)`, for closed `K`, if `f₀` and `f₁` are continuous at those times. -/
theorem continuousOn_ite_endSet {K : Set E} (hK : IsClosed K) {f₀ f₁ : Z × E × ℝ → Y}
    (h₀ : ContinuousOn f₀ (s ×ˢ (K ×ˢ {0}))) (h₁ : ContinuousOn f₁ (s ×ˢ (K ×ˢ {1}))) :
    ContinuousOn (fun q ↦ if q.2.2 = 0 then f₀ q else f₁ q) (s ×ˢ (K ×ˢ endSet true)) := by
  have : K ×ˢ endSet true = K ×ˢ {0} ∪ K ×ˢ {1} := by
    ext ⟨t, τ⟩
    simp only [endSet, ite_true, mem_prod, mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  rw [this]
  refine continuousOn_prod_union (hK.prod isClosed_singleton) (hK.prod isClosed_singleton)
    (h₀.congr fun q hq ↦ ?_) (h₁.congr fun q hq ↦ ?_)
  · simp [show q.2.2 = 0 from hq.2.2]
  · simp [show q.2.2 = 1 from hq.2.2]

end Pasting

section Cubical

variable {ι X : Type*}

/-- The intersection `U_I = ⋂ i ∈ I, U i` of the members of a cover indexed by `I`. -/
def coverInter (U : ι → Set X) (I : Finset ι) : Set X := ⋂ i ∈ I, U i

/-- `coverInter U I` is antitone in `I`. -/
theorem coverInter_anti (U : ι → Set X) {I J : Finset ι} (h : I ⊆ J) :
    coverInter U J ⊆ coverInter U I := by
  intro x hx
  simp only [coverInter, mem_iInter] at hx ⊢
  exact fun i hi ↦ hx i (h hi)

/-- `x ∈ U_I` if and only if `x ∈ U i` for every `i ∈ I`. -/
theorem mem_coverInter {U : ι → Set X} {I : Finset ι} {x : X} :
    x ∈ coverInter U I ↔ ∀ i ∈ I, x ∈ U i := by
  simp [coverInter]

/-- A cube cell of the nerve: `∅ ≠ L ⊆ I` with `U_I` nonempty. -/
def IsNerveCell (U : ι → Set X) (I L : Finset ι) : Prop :=
  L.Nonempty ∧ L ⊆ I ∧ (coverInter U I).Nonempty

variable [Fintype ι]

/-- The support of a vector. -/
def vecSupp (u : ι → ℝ) : Finset ι := Finset.univ.filter (u · ≠ 0)

/-- The coordinates where a vector takes the value `1`. -/
def vecOnes (u : ι → ℝ) : Finset ι := Finset.univ.filter (u · = 1)

/-- The support of a point of `cubeFace I L` is contained in `I`. -/
theorem vecSupp_subset {I L : Finset ι} {u : ι → ℝ} (hu : u ∈ cubeFace I L) :
    vecSupp u ⊆ I := by
  intro i hi
  by_contra h
  simp only [vecSupp, Finset.mem_filter] at hi
  exact hi.2 (hu.2.2 i h)

/-- A point of `cubeFace I L` takes the value `1` on every coordinate in `L`. -/
theorem subset_vecOnes {I L : Finset ι} {u : ι → ℝ} (hu : u ∈ cubeFace I L) :
    L ⊆ vecOnes u := fun i hi ↦ by simp [vecOnes, hu.1 i hi]

/-- The coordinates where a vector equals `1` lie in its support. -/
theorem vecOnes_subset_vecSupp (u : ι → ℝ) : vecOnes u ⊆ vecSupp u := by
  intro i hi
  simp only [vecOnes, vecSupp, Finset.mem_filter] at hi ⊢
  simp [hi.2]

/-- A vector with coordinates in `[0, 1]` lies in the cube `cubeFace (vecSupp u) (vecOnes u)`. -/
theorem mem_cubeFace_self {u : ι → ℝ} (h : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    u ∈ cubeFace (vecSupp u) (vecOnes u) :=
  ⟨fun i hi ↦ by simpa [vecOnes] using hi, h, fun i hi ↦ by simpa [vecSupp] using hi⟩

/-- For a point `u` of the cube of a nerve cell, `(vecSupp u, vecOnes u)` is a nerve cell. -/
theorem isNerveCell_vecSupp {U : ι → Set X} {I L : Finset ι} (hc : IsNerveCell U I L)
    {u : ι → ℝ} (hu : u ∈ cubeFace I L) : IsNerveCell U (vecSupp u) (vecOnes u) :=
  ⟨hc.1.mono (subset_vecOnes hu), vecOnes_subset_vecSupp u,
    hc.2.2.mono (coverInter_anti U (vecSupp_subset hu))⟩

variable [DecidableEq ι]

/-- For `u ∈ cubeFace I L`, the dimension `#(vecSupp u \ vecOnes u)` of the smallest cube
containing `u` is at most `#(I \ L)`. -/
theorem card_vecSupp_sdiff_le {I L : Finset ι} {u : ι → ℝ} (hu : u ∈ cubeFace I L) :
    (vecSupp u \ vecOnes u).card ≤ (I \ L).card :=
  Finset.card_le_card (Finset.sdiff_subset_sdiff (vecSupp_subset hu) (subset_vecOnes hu))

/-- A point of a cube is in its relative interior, or on one of its codimension-one faces. -/
theorem eq_or_mem_cubeBoundary {I L : Finset ι} {u : ι → ℝ} (hu : u ∈ cubeFace I L) :
    (vecSupp u = I ∧ vecOnes u = L) ∨
      ∃ j ∈ I \ L, u ∈ cubeFace (I.erase j) L ∪ cubeFace I (insert j L) := by
  by_cases h1 : vecSupp u = I
  · by_cases h2 : vecOnes u = L
    · exact Or.inl ⟨h1, h2⟩
    · right
      obtain ⟨j, hj, hjL⟩ := Finset.exists_of_ssubset
        (lt_of_le_of_ne (subset_vecOnes hu) (Ne.symm h2))
      have hjI : j ∈ I := h1 ▸ vecOnes_subset_vecSupp u hj
      refine ⟨j, Finset.mem_sdiff.2 ⟨hjI, hjL⟩, Or.inr ⟨fun i hi ↦ ?_, hu.2.1, hu.2.2⟩⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa [vecOnes] using hj
      · exact hu.1 i hi
  · right
    obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset
      (lt_of_le_of_ne (vecSupp_subset hu) h1)
    have hu0 : u j = 0 := by simpa [vecSupp] using hjs
    have hjL : j ∉ L := fun h ↦ by simp [hu.1 j h] at hu0
    refine ⟨j, Finset.mem_sdiff.2 ⟨hj, hjL⟩, Or.inl ⟨hu.1, hu.2.1, fun i hi ↦ ?_⟩⟩
    by_cases hij : i = j
    · rw [hij, hu0]
    · exact hu.2.2 i fun h ↦ hi (Finset.mem_erase.2 ⟨hij, h⟩)

omit [Fintype ι] in
/-- Erasing `j ∈ I \ L` from `I` lowers `#(I \ L)`. -/
theorem card_erase_sdiff_lt {I L : Finset ι} {j : ι} (hj : j ∈ I \ L) :
    (I.erase j \ L).card < (I \ L).card :=
  Finset.card_lt_card ⟨Finset.sdiff_subset_sdiff (Finset.erase_subset j I) le_rfl,
    fun h ↦ by simpa using h hj⟩

omit [Fintype ι] in
/-- Inserting `j ∈ I \ L` into `L` lowers `#(I \ L)`. -/
theorem card_sdiff_insert_lt {I L : Finset ι} {j : ι} (hj : j ∈ I \ L) :
    (I \ insert j L).card < (I \ L).card :=
  Finset.card_lt_card ⟨Finset.sdiff_subset_sdiff le_rfl (Finset.subset_insert j L),
    fun h ↦ by simpa using h hj⟩

/-- A point on a codimension-one face of the cube of `(I, L)` lies in a cube of dimension
`#(vecSupp u \ vecOnes u) < #(I \ L)`. -/
theorem card_lt_of_mem_codimOne {I L : Finset ι} {j : ι} (hj : j ∈ I \ L) {u : ι → ℝ}
    (hu : u ∈ cubeFace (I.erase j) L ∪ cubeFace I (insert j L)) :
    (vecSupp u \ vecOnes u).card < (I \ L).card := by
  rcases hu with hu | hu
  · exact (card_vecSupp_sdiff_le hu).trans_lt (card_erase_sdiff_lt hj)
  · exact (card_vecSupp_sdiff_le hu).trans_lt (card_sdiff_insert_lt hj)

omit [Fintype ι] in
/-- For a nerve cell `(I, L)` and `j ∈ I \ L`, the pair `(I.erase j, L)` is a nerve cell. -/
theorem isNerveCell_erase {U : ι → Set X} {I L : Finset ι} (hc : IsNerveCell U I L) {j : ι}
    (hj : j ∈ I \ L) : IsNerveCell U (I.erase j) L := by
  obtain ⟨hjI, hjL⟩ := Finset.mem_sdiff.1 hj
  exact ⟨hc.1, fun i hi ↦ Finset.mem_erase.2 ⟨fun h ↦ hjL (h ▸ hi), hc.2.1 hi⟩,
    hc.2.2.mono (coverInter_anti U (Finset.erase_subset j I))⟩

omit [Fintype ι] in
/-- For a nerve cell `(I, L)` and `j ∈ I \ L`, the pair `(I, insert j L)` is a nerve cell. -/
theorem isNerveCell_insert {U : ι → Set X} {I L : Finset ι} (hc : IsNerveCell U I L) {j : ι}
    (hj : j ∈ I \ L) : IsNerveCell U I (insert j L) :=
  ⟨Finset.insert_nonempty j L, Finset.insert_subset (Finset.mem_sdiff.1 hj).1 hc.2.1, hc.2.2⟩

omit [Fintype ι] in
/-- The boundary of the prism over `cubeFace I L`, with the product distributed over the union of
the codimension-one faces. -/
theorem cubeBoundary_eq (b : Bool) (I L : Finset ι) :
    cubeBoundary b I L = cubeFace I L ×ˢ endSet b ∪
      ⋃ j ∈ I \ L,
        (cubeFace (I.erase j) L ×ˢ timeSet b ∪ cubeFace I (insert j L) ×ˢ timeSet b) := by
  simp only [cubeBoundary, union_prod]

omit [Fintype ι] in
/-- One cell of `exists_cubicalExtension`: a family `G` which agrees with `e` on the ends of the
prism over the nerve cell `(I, L)`, and is continuous and carried by `C` on the prisms over the
nerve cells of dimension `< #(I \ L)`, extends from the boundary over the prism over `(I, L)`. -/
theorem exists_cellExtension [Finite ι] {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    {U : ι → Set X} {C : Finset ι → Finset ι → Set Y}
    (hCe : ∀ I L, IsNerveCell U I L → ∀ j ∈ I \ L, C (I.erase j) L ⊆ C I L)
    (hCi : ∀ I L, IsNerveCell U I L → ∀ j ∈ I \ L, C I (insert j L) ⊆ C I L)
    (b : Bool) {A : Finset ι → Set Z} (hA : ∀ I I', I ⊆ I' → A I' ⊆ A I)
    {e G : Z → (ι → ℝ) × ℝ → Y} {I L : Finset ι} (hc : IsNerveCell U I L)
    [ContractibleSpace (C I L)]
    (he : ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ e q.1 q.2) (A I ×ˢ (cubeFace I L ×ˢ endSet b)))
    (heV : ∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet b, e z u ∈ C I L)
    (hGe : ∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet b, G z u = e z u)
    (hG : ∀ I' L', IsNerveCell U I' L' → (I' \ L').card < (I \ L).card →
      ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ G q.1 q.2)
        (A I' ×ˢ (cubeFace I' L' ×ˢ timeSet b)) ∧
      (∀ z ∈ A I', ∀ u ∈ cubeFace I' L' ×ˢ timeSet b, G z u ∈ C I' L')) :
    ∃ H : Z → (ι → ℝ) × ℝ → Y,
      ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ H q.1 q.2)
        (A I ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
      (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ timeSet b, H z u ∈ C I L) ∧
      ∀ z ∈ A I, ∀ u ∈ cubeBoundary b I L, H z u = G z u := by
  have hT : ∀ (I' L' : Finset ι), IsClosed (cubeFace I' L' ×ˢ timeSet b) :=
    fun _ _ ↦ (isClosed_cubeFace _ _).prod (isClosed_timeSet b)
  refine exists_cubeExtension b hc.2.1 ?_ ?_
  · rw [cubeBoundary_eq]
    refine continuousOn_prod_union ((isClosed_cubeFace I L).prod (isClosed_endSet b))
      (isClosed_biUnion_finset fun j _ ↦ (hT _ _).union (hT _ _))
      (he.congr fun q hq ↦ hGe q.1 hq.1 q.2 hq.2)
      (continuousOn_prod_biUnion (fun j _ ↦ (hT _ _).union (hT _ _)) fun j hj ↦ ?_)
    refine continuousOn_prod_union (hT _ _) (hT _ _) ?_
      (hG _ _ (isNerveCell_insert hc hj) (card_sdiff_insert_lt hj)).1
    exact (hG _ _ (isNerveCell_erase hc hj) (card_erase_sdiff_lt hj)).1.mono
      (prod_mono (hA _ _ (Finset.erase_subset j I)) le_rfl)
  · intro z hz u hu
    rw [cubeBoundary_eq] at hu
    rcases hu with hu | hu
    · rw [hGe z hz u hu]
      exact heV z hz u hu
    · simp only [mem_iUnion, exists_prop] at hu
      obtain ⟨j, hj, hu | hu⟩ := hu
      · exact hCe I L hc j hj ((hG _ _ (isNerveCell_erase hc hj) (card_erase_sdiff_lt hj)).2 z
          (hA _ _ (Finset.erase_subset j I) hz) u hu)
      · exact hCi I L hc j hj
          ((hG _ _ (isNerveCell_insert hc hj) (card_sdiff_insert_lt hj)).2 z hz u hu)

omit [Fintype ι] in
/-- The inductive step of `exists_cubicalExtension`: extensions `H I L` over the prisms of the
nerve cells of dimension `d`, agreeing with `G` on their boundaries, glue with `G` to a family
continuous and carried by `C` on the prisms of all nerve cells of dimension `≤ d`. -/
theorem exists_cubicalExtension_succ [Finite ι] {Z Y : Type*} [TopologicalSpace Z]
    [TopologicalSpace Y] {U : ι → Set X} {C : Finset ι → Finset ι → Set Y} {b : Bool}
    {A : Finset ι → Set Z} (hA : ∀ I I', I ⊆ I' → A I' ⊆ A I) {e G : Z → (ι → ℝ) × ℝ → Y} {d : ℕ}
    (hGe : ∀ I L, IsNerveCell U I L → ∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet b, G z u = e z u)
    (hG : ∀ I L, IsNerveCell U I L → (I \ L).card < d →
      ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ G q.1 q.2) (A I ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
      (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ timeSet b, G z u ∈ C I L))
    (H : Finset ι → Finset ι → Z → (ι → ℝ) × ℝ → Y)
    (hH : ∀ I L, IsNerveCell U I L → (I \ L).card = d →
      ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ H I L q.1 q.2)
        (A I ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
      (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ timeSet b, H I L z u ∈ C I L) ∧
      ∀ z ∈ A I, ∀ u ∈ cubeBoundary b I L, H I L z u = G z u) :
    ∃ G' : Z → (ι → ℝ) × ℝ → Y,
      (∀ I L, IsNerveCell U I L → ∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet b, G' z u = e z u) ∧
      ∀ I L, IsNerveCell U I L → (I \ L).card < d + 1 →
        ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ G' q.1 q.2)
          (A I ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
        (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ timeSet b, G' z u ∈ C I L) := by
  classical
  have := Fintype.ofFinite ι
  let G' : Z → (ι → ℝ) × ℝ → Y := fun z p ↦
    if IsNerveCell U (vecSupp p.1) (vecOnes p.1) ∧ (vecSupp p.1 \ vecOnes p.1).card = d
    then H (vecSupp p.1) (vecOnes p.1) z p else G z p
  have hG'low : ∀ I L, (I \ L).card < d → ∀ z, ∀ p ∈ cubeFace I L ×ˢ timeSet b,
      G' z p = G z p := by
    intro I L hd z p hp
    have : (vecSupp p.1 \ vecOnes p.1).card ≠ d :=
      ((card_vecSupp_sdiff_le hp.1).trans_lt hd).ne
    simp [G', this]
  have hG'eq : ∀ I L, IsNerveCell U I L → (I \ L).card = d → ∀ z ∈ A I,
      ∀ p ∈ cubeFace I L ×ˢ timeSet b, G' z p = H I L z p := by
    intro I L hc hd z hz p hp
    rcases eq_or_mem_cubeBoundary hp.1 with ⟨h₁, h₂⟩ | ⟨j, hj, hu⟩
    · simp only [G', h₁, h₂, hc, hd, and_self, ite_true]
    · have hne : (vecSupp p.1 \ vecOnes p.1).card ≠ d :=
        (hd ▸ card_lt_of_mem_codimOne hj hu).ne
      simp only [G', hne, and_false, ite_false]
      refine ((hH I L hc hd).2.2 z hz p ?_).symm
      rw [cubeBoundary_eq]
      exact Or.inr (mem_iUnion₂.2 ⟨j, hj,
        Or.elim hu (fun hu ↦ Or.inl ⟨hu, hp.2⟩) fun hu ↦ Or.inr ⟨hu, hp.2⟩⟩)
  refine ⟨G', fun I L hc z hz p hp ↦ ?_, fun I L hc hd ↦ ?_⟩
  · by_cases hcond : IsNerveCell U (vecSupp p.1) (vecOnes p.1) ∧
        (vecSupp p.1 \ vecOnes p.1).card = d
    · simp only [G', hcond, and_self, ite_true]
      rw [(hH _ _ hcond.1 hcond.2).2.2 z (hA _ _ (vecSupp_subset hp.1) hz) p
        (Or.inl ⟨mem_cubeFace_self hp.1.2.1, hp.2⟩)]
      exact hGe I L hc z hz p hp
    · simp only [G', hcond, ite_false]
      exact hGe I L hc z hz p hp
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | hd
    · refine ⟨(hG I L hc hd).1.congr fun q hq ↦ hG'low I L hd q.1 q.2 hq.2,
        fun z hz p hp ↦ ?_⟩
      rw [hG'low I L hd z p hp]
      exact (hG I L hc hd).2 z hz p hp
    · refine ⟨(hH I L hc hd).1.congr fun q hq ↦ hG'eq I L hc hd q.1 hq.1 q.2 hq.2,
        fun z hz p hp ↦ ?_⟩
      rw [hG'eq I L hc hd z hz p hp]
      exact (hH I L hc hd).2.1 z hz p hp

omit [Fintype ι] in
/-- **Cellular extension over the cubes of the nerve.** Data prescribed on the ends of the prisms
over all nerve cells extends over all prisms, each prism over the cell `(I, L)` being mapped into
the contractible carrier `C I L`. Carriers shrink on passing to codimension-one faces. -/
theorem exists_cubicalExtension [Finite ι] {Z Y : Type*} [TopologicalSpace Z]
    [TopologicalSpace Y]
    (U : ι → Set X) (C : Finset ι → Finset ι → Set Y)
    (hC : ∀ I L, IsNerveCell U I L → ContractibleSpace (C I L))
    (hCe : ∀ I L, IsNerveCell U I L → ∀ j ∈ I \ L, C (I.erase j) L ⊆ C I L)
    (hCi : ∀ I L, IsNerveCell U I L → ∀ j ∈ I \ L, C I (insert j L) ⊆ C I L)
    (b : Bool) (A : Finset ι → Set Z) (hA : ∀ I I', I ⊆ I' → A I' ⊆ A I)
    (e : Z → (ι → ℝ) × ℝ → Y)
    (he : ∀ I L, IsNerveCell U I L →
      ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ e q.1 q.2) (A I ×ˢ (cubeFace I L ×ˢ endSet b)))
    (heV : ∀ I L, IsNerveCell U I L → ∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet b,
      e z u ∈ C I L) :
    ∃ G : Z → (ι → ℝ) × ℝ → Y, ∀ I L, IsNerveCell U I L →
      ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ G q.1 q.2) (A I ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
      (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ timeSet b, G z u ∈ C I L) ∧
      (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet b, G z u = e z u) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ d : ℕ, ∃ G : Z → (ι → ℝ) × ℝ → Y,
      (∀ I L, IsNerveCell U I L → ∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet b, G z u = e z u) ∧
      ∀ I L, IsNerveCell U I L → (I \ L).card < d →
        ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ G q.1 q.2)
          (A I ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
        (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ timeSet b, G z u ∈ C I L) := by
    intro d
    induction d with
    | zero => exact ⟨e, fun _ _ _ _ _ _ _ ↦ rfl, fun _ _ _ h ↦ absurd h (Nat.not_lt_zero _)⟩
    | succ d ih =>
      obtain ⟨G, hGe, hG⟩ := ih
      have hext : ∀ I L, ∃ H : Z → (ι → ℝ) × ℝ → Y, IsNerveCell U I L → (I \ L).card = d →
            ContinuousOn (fun q : Z × ((ι → ℝ) × ℝ) ↦ H q.1 q.2)
              (A I ×ˢ (cubeFace I L ×ˢ timeSet b)) ∧
            (∀ z ∈ A I, ∀ u ∈ cubeFace I L ×ˢ timeSet b, H z u ∈ C I L) ∧
            ∀ z ∈ A I, ∀ u ∈ cubeBoundary b I L, H z u = G z u := by
        intro I L
        by_cases hcd : IsNerveCell U I L ∧ (I \ L).card = d
        · obtain ⟨hc, hd⟩ := hcd
          have := hC I L hc
          obtain ⟨H, h₁, h₂, h₃⟩ := exists_cellExtension hCe hCi b hA hc (he I L hc) (heV I L hc)
            (hGe I L hc) fun I' L' hc' h' ↦ hG I' L' hc' (h'.trans_eq hd)
          exact ⟨H, fun _ _ ↦ ⟨h₁, h₂, h₃⟩⟩
        · exact ⟨G, fun hc hd ↦ absurd ⟨hc, hd⟩ hcd⟩
      choose H hH using hext
      exact exists_cubicalExtension_succ hA hGe hG H hH
  obtain ⟨G, hGe, hG⟩ := key (Fintype.card ι + 1)
  exact ⟨G, fun I L hc ↦ (hG I L hc (Nat.lt_succ_of_le (Finset.card_le_univ _))).imp_right
    (⟨·, hGe I L hc⟩)⟩

end Cubical

section Nerve

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

/-- A function continuous on each member of a finite family of closed sets is continuous on their
union. -/
theorem continuousOn_biUnion_finset {α β κ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {T : Finset κ} {K : κ → Set α} (hK : ∀ k ∈ T, IsClosed (K k))
    (hf : ∀ k ∈ T, ContinuousOn f (K k)) : ContinuousOn f (⋃ k ∈ T, K k) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hK hf
    rw [Finset.set_biUnion_insert]
    exact hf.1.union_of_isClosed (ih hK.2 hf.2) hK.1 (isClosed_biUnion_finset hK.2)

/-- The geometric realisation of the nerve of `U` inside `ι → ℝ`: the points of the standard
simplex whose support indexes members of `U` with a common point. -/
def nerveSet (U : ι → Set X) : Set (ι → ℝ) :=
  {t | t ∈ simplexFace (Finset.univ : Finset ι) ∧ (coverInter U (vecSupp t)).Nonempty}

/-- The nerve cells, as a finset. -/
def nerveCells (U : ι → Set X) : Finset (Finset ι × Finset ι) := by
  classical
  exact Finset.univ.filter fun p ↦ IsNerveCell U p.1 p.2

omit [DecidableEq ι] in
/-- `p ∈ nerveCells U` if and only if `(p.1, p.2)` is a nerve cell. -/
theorem mem_nerveCells {U : ι → Set X} {p : Finset ι × Finset ι} :
    p ∈ nerveCells U ↔ IsNerveCell U p.1 p.2 := by
  classical
  simp [nerveCells]

omit [DecidableEq ι] in
/-- Multiplication by a nonzero scalar does not change the support. -/
theorem vecSupp_smul {a : ℝ} (ha : a ≠ 0) (t : ι → ℝ) : vecSupp (a • t) = vecSupp t := by
  ext i
  simp [vecSupp, ha]

/-- Rescaling a point of the simplex so that its largest coordinate is `1`. -/
def cubeNormalize [Nonempty ι] (t : ι → ℝ) : ι → ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty t)⁻¹ • t

/-- Rescaling a vector so that its coordinates sum to `1`. -/
def simplexNormalize (u : ι → ℝ) : ι → ℝ := (∑ i, u i)⁻¹ • u

omit [DecidableEq ι] in
/-- The largest coordinate of a point of the standard simplex is positive. -/
theorem sup'_pos_of_mem_simplexFace [Nonempty ι] {t : ι → ℝ}
    (ht : t ∈ simplexFace (Finset.univ : Finset ι)) :
    0 < Finset.univ.sup' Finset.univ_nonempty t := by
  obtain ⟨i, hi⟩ := filter_nonempty_of_mem_simplexFace ht
  simp only [Finset.mem_filter] at hi
  exact (lt_of_le_of_ne (ht.1 i) (Ne.symm hi.2)).trans_le
    (Finset.le_sup' t (Finset.mem_univ i))

omit [DecidableEq ι] in
/-- `cubeNormalize` is continuous on the standard simplex. -/
theorem continuousOn_cubeNormalize [Nonempty ι] :
    ContinuousOn (cubeNormalize (ι := ι)) (simplexFace Finset.univ) := by
  intro t ht
  have hc : Continuous fun t : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty t :=
    Continuous.finset_sup'_apply _ fun i _ ↦ continuous_apply i
  exact ((hc.continuousAt.inv₀ (sup'_pos_of_mem_simplexFace ht).ne').smul
    continuousAt_id).continuousWithinAt

omit [DecidableEq ι] in
/-- For `t ∈ nerveSet U`, `cubeNormalize t` lies in the cube of the nerve cell
`(vecSupp (cubeNormalize t), vecOnes (cubeNormalize t))`, and has the same support as `t`. -/
theorem cubeNormalize_mem [Nonempty ι] {U : ι → Set X} {t : ι → ℝ} (ht : t ∈ nerveSet U) :
    IsNerveCell U (vecSupp (cubeNormalize t)) (vecOnes (cubeNormalize t)) ∧
      cubeNormalize t ∈ cubeFace (vecSupp (cubeNormalize t)) (vecOnes (cubeNormalize t)) ∧
      vecSupp (cubeNormalize t) = vecSupp t := by
  have hm := sup'_pos_of_mem_simplexFace ht.1
  set m := Finset.univ.sup' Finset.univ_nonempty t with hmdef
  have hsupp : vecSupp (cubeNormalize t) = vecSupp t := vecSupp_smul (inv_ne_zero hm.ne') t
  have hbd : ∀ i, 0 ≤ cubeNormalize t i ∧ cubeNormalize t i ≤ 1 := by
    intro i
    simp only [cubeNormalize, Pi.smul_apply, smul_eq_mul, ← hmdef]
    refine ⟨mul_nonneg (inv_nonneg.2 hm.le) (ht.1.1 i), ?_⟩
    rw [inv_mul_le_iff₀ hm, mul_one]
    exact Finset.le_sup' t (Finset.mem_univ i)
  refine ⟨⟨?_, vecOnes_subset_vecSupp _, by rw [hsupp]; exact ht.2⟩, mem_cubeFace_self hbd, hsupp⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty t
  refine ⟨i, ?_⟩
  simp only [vecOnes, Finset.mem_filter, Finset.mem_univ, true_and, cubeNormalize,
    Pi.smul_apply, smul_eq_mul, ← hmdef]
  rw [← hi, inv_mul_cancel₀ hm.ne']

omit [DecidableEq ι] in
/-- `simplexNormalize` is a left inverse of `cubeNormalize` on the standard simplex. -/
theorem simplexNormalize_cubeNormalize [Nonempty ι] {t : ι → ℝ}
    (ht : t ∈ simplexFace (Finset.univ : Finset ι)) : simplexNormalize (cubeNormalize t) = t := by
  have hm := sup'_pos_of_mem_simplexFace ht
  simp only [simplexNormalize, cubeNormalize, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    ht.2.1, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hm.ne', one_smul]

omit [DecidableEq ι] in
/-- For nonempty `L`, the coordinates of a point of `cubeFace I L` sum to at least `1`. -/
theorem one_le_sum_of_mem_cubeFace {I L : Finset ι} (hL : L.Nonempty) {u : ι → ℝ}
    (hu : u ∈ cubeFace I L) : 1 ≤ ∑ i, u i := by
  obtain ⟨i, hi⟩ := hL
  rw [← hu.1 i hi]
  exact Finset.single_le_sum (fun j _ ↦ (hu.2.1 j).1) (Finset.mem_univ i)

omit [DecidableEq ι] in
/-- For nonempty `L`, `simplexNormalize` is continuous on `cubeFace I L`. -/
theorem continuousOn_simplexNormalize {I L : Finset ι} (hL : L.Nonempty) :
    ContinuousOn (simplexNormalize (ι := ι)) (cubeFace I L) := by
  intro u hu
  have hc : Continuous fun u : ι → ℝ ↦ ∑ i, u i :=
    continuous_finsetSum _ fun i _ ↦ continuous_apply i
  exact ((hc.continuousAt.inv₀ (zero_lt_one.trans_le
    (one_le_sum_of_mem_cubeFace hL hu)).ne').smul continuousAt_id).continuousWithinAt

omit [DecidableEq ι] in
/-- For nonempty `L` and `u ∈ cubeFace I L`, `simplexNormalize u` lies in the standard simplex and
has support contained in `I`. -/
theorem simplexNormalize_mem {I L : Finset ι} (hL : L.Nonempty) {u : ι → ℝ}
    (hu : u ∈ cubeFace I L) :
    simplexNormalize u ∈ simplexFace (Finset.univ : Finset ι) ∧
      vecSupp (simplexNormalize u) ⊆ I := by
  have hs := zero_lt_one.trans_le (one_le_sum_of_mem_cubeFace hL hu)
  refine ⟨⟨fun i ↦ ?_, ?_, fun i hi ↦ absurd (Finset.mem_univ i) hi⟩, ?_⟩
  · exact mul_nonneg (inv_nonneg.2 hs.le) (hu.2.1 i).1
  · simp only [simplexNormalize, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · rw [simplexNormalize, vecSupp_smul (inv_ne_zero hs.ne')]
    exact vecSupp_subset hu

/-- The carrier `{t ∈ Δ | U_{supp t ∪ L} ≠ ∅}` used to compare the two maps into the nerve. -/
def nerveStar (U : ι → Set X) (L : Finset ι) : Set (ι → ℝ) :=
  {t | t ∈ simplexFace (Finset.univ : Finset ι) ∧ (coverInter U (vecSupp t ∪ L)).Nonempty}

/-- `nerveStar U L` is contained in the realisation `nerveSet U` of the nerve. -/
theorem nerveStar_subset (U : ι → Set X) (L : Finset ι) : nerveStar U L ⊆ nerveSet U :=
  fun _ ht ↦ ⟨ht.1, ht.2.mono (coverInter_anti U Finset.subset_union_left)⟩

/-- `nerveStar U L` is antitone in `L`. -/
theorem nerveStar_anti (U : ι → Set X) {L L' : Finset ι} (h : L ⊆ L') :
    nerveStar U L' ⊆ nerveStar U L :=
  fun _ ht ↦ ⟨ht.1, ht.2.mono (coverInter_anti U (Finset.union_subset_union le_rfl h))⟩

/-- For nonempty `L` with `U_L` nonempty, `nerveStar U L` is contractible. -/
theorem contractibleSpace_nerveStar (U : ι → Set X) {L : Finset ι} (hL : L.Nonempty)
    (hU : (coverInter U L).Nonempty) : ContractibleSpace (nerveStar U L) := by
  set c : ι → ℝ := fun i ↦ if i ∈ L then (L.card : ℝ)⁻¹ else 0 with hc
  have hk : (0 : ℝ) < L.card := by simpa using hL.card_pos
  have hcs : vecSupp c = L := by
    ext i
    by_cases hi : i ∈ L <;> simp [vecSupp, hc, hi, hk.ne']
  have hcmem : c ∈ nerveStar U L := by
    refine ⟨⟨fun i ↦ ?_, ?_, fun i hi ↦ absurd (Finset.mem_univ i) hi⟩, ?_⟩
    · by_cases hi : i ∈ L <;> simp [hc, hi, hk.le]
    · simp [hc, Finset.sum_ite_mem, hk.ne']
    · rwa [hcs, Finset.union_self]
  refine StarConvex.contractibleSpace (x := c) ?_ ⟨c, hcmem⟩
  intro t ht a b ha hb hab
  refine ⟨⟨fun i ↦ ?_, ?_, fun i hi ↦ absurd (Finset.mem_univ i) hi⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hcmem.1.1 i)) (mul_nonneg hb (ht.1.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hcmem.1.2.1, ht.1.2.1, mul_one, hab]
  · refine ht.2.mono (coverInter_anti U ?_)
    intro i hi
    simp only [Finset.mem_union, vecSupp, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rcases hi with hi | hi
    · by_contra h
      push Not at h
      have h1 : c i = 0 := by
        by_contra h'
        exact h.2 (hcs ▸ (show i ∈ vecSupp c by simpa [vecSupp] using h'))
      rw [h1, h.1, mul_zero, mul_zero, add_zero] at hi
      exact hi rfl
    · exact Or.inr hi

omit [Fintype ι] [DecidableEq ι] in
/-- A map `g` from the cubes of the nerve to `X`, continuous on the cube of each nerve cell
`(I, L)` and carried by `U_L`, when the `U_L` are contractible. -/
theorem exists_nerveInverse [Finite ι] [TopologicalSpace X] (U : ι → Set X) (x₀ : X)
    (hCX : ∀ I L, IsNerveCell U I L → ContractibleSpace (coverInter U L)) :
    ∃ g : (ι → ℝ) → X, ∀ I L, IsNerveCell U I L →
      ContinuousOn g (cubeFace I L) ∧ ∀ u ∈ cubeFace I L, g u ∈ coverInter U L := by
  classical
  obtain ⟨G, hG⟩ := exists_cubicalExtension (Z := Unit) U (fun _ L ↦ coverInter U L) hCX
    (fun _ _ _ _ _ ↦ le_rfl) (fun _ L _ j _ ↦ coverInter_anti U (Finset.subset_insert j L))
    false (fun _ ↦ univ) (fun _ _ _ ↦ le_rfl) (fun _ _ ↦ x₀) (fun _ _ _ ↦ continuousOn_const)
    (fun _ _ _ _ _ u hu ↦ by simp [endSet] at hu)
  refine ⟨fun u ↦ G () (u, 0), fun I L hc ↦ ⟨?_, fun u hu ↦
    (hG I L hc).2.1 () (mem_univ _) (u, 0) ⟨hu, by simp [timeSet]⟩⟩⟩
  exact (hG I L hc).1.comp (by fun_prop : Continuous fun u : ι → ℝ ↦
    (((), (u, (0 : ℝ))) : Unit × ((ι → ℝ) × ℝ))).continuousOn
    (fun u hu ↦ ⟨mem_univ _, hu, by simp [timeSet]⟩)

omit [Fintype ι] [DecidableEq ι] in
/-- With contractible `U_L`, a map `g` from the cubes of the nerve carried by `U_L` is homotopic,
over the cube of each nerve cell `(I, L)` and for parameters `x ∈ A I ⊆ U_I`, to the projection
`(x, u) ↦ x`, through maps carried by `U_L`. -/
theorem exists_homotopy_fst_nerveInverse [Finite ι] [TopologicalSpace X] {U : ι → Set X}
    (hCX : ∀ I L, IsNerveCell U I L → ContractibleSpace (coverInter U L)) {A : Finset ι → Set X}
    (hA : ∀ I I', I ⊆ I' → A I' ⊆ A I) (hAU : ∀ I, A I ⊆ coverInter U I) {g : (ι → ℝ) → X}
    (hg : ∀ I L, IsNerveCell U I L →
      ContinuousOn g (cubeFace I L) ∧ ∀ u ∈ cubeFace I L, g u ∈ coverInter U L) :
    ∃ H : X → (ι → ℝ) × ℝ → X, ∀ I L, IsNerveCell U I L →
      ContinuousOn (fun q : X × ((ι → ℝ) × ℝ) ↦ H q.1 q.2)
        (A I ×ˢ (cubeFace I L ×ˢ timeSet true)) ∧
      ∀ x ∈ A I, ∀ u ∈ cubeFace I L ×ˢ endSet true, H x u = if u.2 = 0 then x else g u.1 := by
  classical
  obtain ⟨H, hH⟩ := exists_cubicalExtension (Z := X) U (fun _ L ↦ coverInter U L) hCX
    (fun _ _ _ _ _ ↦ le_rfl) (fun _ L _ j _ ↦ coverInter_anti U (Finset.subset_insert j L))
    true A hA (fun x p ↦ if p.2 = 0 then x else g p.1)
    (fun I L hc ↦ continuousOn_ite_endSet (isClosed_cubeFace I L) (f₀ := Prod.fst)
      (f₁ := fun q ↦ g q.2.1) continuousOn_fst ((hg I L hc).1.comp
        (by fun_prop : Continuous fun q : X × ((ι → ℝ) × ℝ) ↦ q.2.1).continuousOn
        fun q hq ↦ hq.2.1))
    (fun I L hc z hz u hu ↦ by
      by_cases h0 : u.2 = 0
      · simp only [h0, ite_true]
        exact coverInter_anti U hc.2.1 (hAU I hz)
      · simp only [h0, ite_false]
        exact (hg I L hc).2 u.1 hu.1)
  exact ⟨H, fun I L hc ↦ ⟨(hH I L hc).1, (hH I L hc).2.2⟩⟩

/-- For a map `Φ : X → Δ` with `x ∈ U i` whenever `Φ x i ≠ 0`, and a map `g` from the cubes of the
nerve carried by `U_L`, the map `Φ ∘ g` is homotopic to `simplexNormalize` over the cube of each
nerve cell `(I, L)`, through maps into `nerveStar U L`. -/
theorem exists_homotopy_nerveInverse_simplexNormalize [TopologicalSpace X] {U : ι → Set X}
    {g : (ι → ℝ) → X} (hg : ∀ I L, IsNerveCell U I L →
      ContinuousOn g (cubeFace I L) ∧ ∀ u ∈ cubeFace I L, g u ∈ coverInter U L)
    {Φ : X → ι → ℝ} (hΦc : Continuous Φ) (hΦmem : ∀ x, Φ x ∈ simplexFace Finset.univ)
    (hΦU : ∀ x, ∀ i ∈ vecSupp (Φ x), x ∈ U i) :
    ∃ H : (ι → ℝ) × ℝ → ι → ℝ, ∀ I L, IsNerveCell U I L →
      ContinuousOn H (cubeFace I L ×ˢ timeSet true) ∧
      (∀ u ∈ cubeFace I L ×ˢ timeSet true, H u ∈ nerveStar U L) ∧
      ∀ u ∈ cubeFace I L ×ˢ endSet true,
        H u = if u.2 = 0 then Φ (g u.1) else simplexNormalize u.1 := by
  classical
  obtain ⟨H, hH⟩ := exists_cubicalExtension (Z := Unit) U (fun _ L ↦ nerveStar U L)
    (fun I L hc ↦ contractibleSpace_nerveStar U hc.1 (hc.2.2.mono (coverInter_anti U hc.2.1)))
    (fun _ _ _ _ _ ↦ le_rfl) (fun _ L _ j _ ↦ nerveStar_anti U (Finset.subset_insert j L))
    true (fun _ ↦ univ) (fun _ _ _ ↦ le_rfl)
    (fun _ p ↦ if p.2 = 0 then Φ (g p.1) else simplexNormalize p.1)
    (fun I L hc ↦ continuousOn_ite_endSet (isClosed_cubeFace I L)
      (f₀ := fun q ↦ Φ (g q.2.1)) (f₁ := fun q ↦ simplexNormalize q.2.1)
      (hΦc.comp_continuousOn ((hg I L hc).1.comp (by fun_prop : Continuous
        fun q : Unit × ((ι → ℝ) × ℝ) ↦ q.2.1).continuousOn fun q hq ↦ hq.2.1))
      ((continuousOn_simplexNormalize hc.1).comp (by fun_prop : Continuous
        fun q : Unit × ((ι → ℝ) × ℝ) ↦ q.2.1).continuousOn fun q hq ↦ hq.2.1))
    (fun I L hc _ _ u hu ↦ by
      by_cases h0 : u.2 = 0
      · simp only [h0, ite_true]
        refine ⟨hΦmem _, g u.1, mem_coverInter.2 fun i hi ↦ ?_⟩
        rcases Finset.mem_union.1 hi with hi | hi
        · exact hΦU _ i hi
        · exact mem_coverInter.1 ((hg I L hc).2 u.1 hu.1) i hi
      · simp only [h0, ite_false]
        obtain ⟨h1, h2⟩ := simplexNormalize_mem hc.1 hu.1
        exact ⟨h1, hc.2.2.mono (coverInter_anti U (Finset.union_subset h2 hc.2.1))⟩)
  refine ⟨H (), fun I L hc ↦ ⟨?_, fun u hu ↦ (hH I L hc).2.1 () (mem_univ _) u hu,
    fun u hu ↦ (hH I L hc).2.2 () (mem_univ _) u hu⟩⟩
  exact (hH I L hc).1.comp (continuous_const.prodMk continuous_id).continuousOn
    fun u hu ↦ ⟨mem_univ _, hu⟩

omit [DecidableEq ι] in
/-- If `Φ : X → |N|` is continuous with each `x` in the closed piece `A (vecSupp (Φ x))`, and `g`
is a map from the cubes of the nerve carried by the contractible `U_L`, then any map `f` with
`f x = g (cubeNormalize (Φ x))` is homotopic to the identity of `X`. -/
theorem homotopic_id_of_eq_nerveInverse [TopologicalSpace X] [Nonempty ι] {U : ι → Set X}
    (hCX : ∀ I L, IsNerveCell U I L → ContractibleSpace (coverInter U L)) {A : Finset ι → Set X}
    (hAc : ∀ I, IsClosed (A I)) (hA : ∀ I I', I ⊆ I' → A I' ⊆ A I)
    (hAU : ∀ I, A I ⊆ coverInter U I) {g : (ι → ℝ) → X}
    (hg : ∀ I L, IsNerveCell U I L →
      ContinuousOn g (cubeFace I L) ∧ ∀ u ∈ cubeFace I L, g u ∈ coverInter U L)
    {Φ : X → ι → ℝ} (hΦc : Continuous Φ) (hΦN : ∀ x, Φ x ∈ nerveSet U)
    (hΦA : ∀ x, x ∈ A (vecSupp (Φ x))) (f : C(X, X))
    (hf : ∀ x, f x = g (cubeNormalize (Φ x))) : f.Homotopic (ContinuousMap.id X) := by
  obtain ⟨H, hH⟩ := exists_homotopy_fst_nerveInverse hCX hA hAU hg
  have hxA : ∀ x, x ∈ A (vecSupp (cubeNormalize (Φ x))) := fun x ↦ by
    rw [(cubeNormalize_mem (hΦN x)).2.2]
    exact hΦA x
  have hHc : ContinuousOn (fun q : X × ((ι → ℝ) × ℝ) ↦ H q.1 q.2)
      (⋃ p ∈ nerveCells U, A p.1 ×ˢ (cubeFace p.1 p.2 ×ˢ Icc 0 1)) :=
    continuousOn_biUnion_finset (fun p _ ↦ (hAc _).prod ((isClosed_cubeFace _ _).prod isClosed_Icc))
      fun p hp ↦ by simpa [timeSet] using (hH _ _ (mem_nerveCells.1 hp)).1
  have hend : ∀ x, ∀ τ ∈ endSet true, H x (cubeNormalize (Φ x), τ) =
      if τ = 0 then x else g (cubeNormalize (Φ x)) := fun x τ hτ ↦
    (hH _ _ (cubeNormalize_mem (hΦN x)).1).2 x (hxA x) _ ⟨(cubeNormalize_mem (hΦN x)).2.1, hτ⟩
  refine ⟨ContinuousMap.Homotopy.symm ⟨⟨fun p : unitInterval × X ↦
    H p.2 (cubeNormalize (Φ p.2), (p.1 : ℝ)), ?_⟩, ?_, ?_⟩⟩
  · exact hHc.comp_continuous
      (f := fun p : unitInterval × X ↦ (p.2, (cubeNormalize (Φ p.2), (p.1 : ℝ))))
      (continuous_snd.prodMk (((continuousOn_cubeNormalize.comp_continuous hΦc
        fun x ↦ (hΦN x).1).comp continuous_snd).prodMk
          (continuous_subtype_val.comp continuous_fst)))
      fun p ↦ mem_iUnion₂.2 ⟨(_, _), mem_nerveCells.2 (cubeNormalize_mem (hΦN p.2)).1, hxA p.2,
        (cubeNormalize_mem (hΦN p.2)).2.1, p.1.2⟩
  · exact fun x ↦ by simpa [endSet] using hend x 0 (by simp [endSet])
  · exact fun x ↦ by simpa [endSet, hf] using hend x 1 (by simp [endSet])

omit [DecidableEq ι] in
/-- If `Φ : X → Δ` is continuous with `x ∈ U i` whenever `Φ x i ≠ 0`, and `g` is a map from the
cubes of the nerve carried by `U_L`, then any self-map `f` of `nerveSet U` with
`f t = Φ (g (cubeNormalize t))` is homotopic to the identity. -/
theorem homotopic_id_of_eq_comp_nerveInverse [TopologicalSpace X] [Nonempty ι] {U : ι → Set X}
    {g : (ι → ℝ) → X} (hg : ∀ I L, IsNerveCell U I L →
      ContinuousOn g (cubeFace I L) ∧ ∀ u ∈ cubeFace I L, g u ∈ coverInter U L)
    {Φ : X → ι → ℝ} (hΦc : Continuous Φ) (hΦmem : ∀ x, Φ x ∈ simplexFace Finset.univ)
    (hΦU : ∀ x, ∀ i ∈ vecSupp (Φ x), x ∈ U i) (f : C(nerveSet U, nerveSet U))
    (hf : ∀ t, (f t : ι → ℝ) = Φ (g (cubeNormalize t))) :
    f.Homotopic (ContinuousMap.id (nerveSet U)) := by
  classical
  obtain ⟨H, hH⟩ := exists_homotopy_nerveInverse_simplexNormalize hg hΦc hΦmem hΦU
  have hHc : ContinuousOn H (⋃ p ∈ nerveCells U, cubeFace p.1 p.2 ×ˢ Icc 0 1) :=
    continuousOn_biUnion_finset (fun p _ ↦ (isClosed_cubeFace _ _).prod isClosed_Icc)
      fun p hp ↦ by simpa [timeSet] using (hH _ _ (mem_nerveCells.1 hp)).1
  have hHmem : ∀ t ∈ nerveSet U, ∀ τ ∈ Icc (0 : ℝ) 1, H (cubeNormalize t, τ) ∈ nerveSet U :=
    fun t ht τ hτ ↦ nerveStar_subset U _ ((hH _ _ (cubeNormalize_mem ht).1).2.1 _
      ⟨(cubeNormalize_mem ht).2.1, by simpa [timeSet] using hτ⟩)
  have hend : ∀ t ∈ nerveSet U, ∀ τ ∈ endSet true, H (cubeNormalize t, τ) =
      if τ = 0 then Φ (g (cubeNormalize t)) else simplexNormalize (cubeNormalize t) :=
    fun t ht τ hτ ↦ (hH _ _ (cubeNormalize_mem ht).1).2.2 _ ⟨(cubeNormalize_mem ht).2.1, hτ⟩
  refine ⟨⟨⟨fun p : unitInterval × nerveSet U ↦
    ⟨H (cubeNormalize p.2, (p.1 : ℝ)), hHmem p.2 p.2.2 p.1 p.1.2⟩, ?_⟩, ?_, ?_⟩⟩
  · refine Continuous.subtype_mk (hHc.comp_continuous (f := fun p : unitInterval × nerveSet U ↦
      (cubeNormalize (p.2 : ι → ℝ), (p.1 : ℝ))) ?_ fun p ↦ mem_iUnion₂.2 ⟨(_, _),
        mem_nerveCells.2 (cubeNormalize_mem p.2.2).1, (cubeNormalize_mem p.2.2).2.1, p.1.2⟩) _
    exact (continuousOn_cubeNormalize.comp_continuous (continuous_subtype_val.comp continuous_snd)
      fun p ↦ p.2.2.1).prodMk (continuous_subtype_val.comp continuous_fst)
  · intro t
    apply Subtype.ext
    simpa [endSet, hf] using hend t t.2 0 (by simp [endSet])
  · intro t
    apply Subtype.ext
    simpa [endSet, simplexNormalize_cubeNormalize t.2.1] using hend t t.2 1 (by simp [endSet])

omit [DecidableEq ι] in
/-- **The nerve theorem**, with a partition of unity given: if every nonempty finite intersection
of the members of `U` is contractible and `φ` is a partition of unity with `tsupport (φ i) ⊆ U i`,
then `X` is homotopy equivalent to the realisation of the nerve. -/
theorem nonempty_homotopyEquiv_nerveSet [TopologicalSpace X] [Nonempty X] (U : ι → Set X)
    (hU : ∀ I : Finset ι, I.Nonempty → (coverInter U I).Nonempty →
      ContractibleSpace (coverInter U I))
    (φ : ι → C(X, ℝ)) (hφ0 : ∀ i x, 0 ≤ φ i x) (hφ1 : ∀ x, ∑ i, φ i x = 1)
    (hφU : ∀ i, tsupport (φ i) ⊆ U i) : Nonempty (ContinuousMap.HomotopyEquiv X (nerveSet U)) := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty X›
  have : Nonempty ι := not_isEmpty_iff.1 fun h ↦ by simpa using hφ1 x0
  set Φ : X → ι → ℝ := fun x i ↦ φ i x with hΦ
  have hΦc : Continuous Φ := continuous_pi fun i ↦ (φ i).continuous
  have hΦmem : ∀ x, Φ x ∈ simplexFace (Finset.univ : Finset ι) :=
    fun x ↦ ⟨fun i ↦ hφ0 i x, hφ1 x, fun i hi ↦ absurd (Finset.mem_univ i) hi⟩
  have hΦsupp : ∀ x, ∀ i ∈ vecSupp (Φ x), x ∈ tsupport (φ i) :=
    fun x i hi ↦ subset_tsupport _ (Function.mem_support.2 (Finset.mem_filter.1 hi).2)
  have hΦN : ∀ x, Φ x ∈ nerveSet U :=
    fun x ↦ ⟨hΦmem x, x, mem_coverInter.2 fun i hi ↦ hφU i (hΦsupp x i hi)⟩
  have hCX : ∀ I L, IsNerveCell U I L → ContractibleSpace (coverInter U L) :=
    fun I L hc ↦ hU L hc.1 (hc.2.2.mono (coverInter_anti U hc.2.1))
  obtain ⟨g, hg⟩ := exists_nerveInverse U x0 hCX
  have hgCub : ContinuousOn g (⋃ p ∈ nerveCells U, cubeFace p.1 p.2) :=
    continuousOn_biUnion_finset (fun p _ ↦ isClosed_cubeFace _ _)
      fun p hp ↦ (hg _ _ (mem_nerveCells.1 hp)).1
  let toFun : C(X, nerveSet U) := ⟨fun x ↦ ⟨Φ x, hΦN x⟩, hΦc.subtype_mk _⟩
  let invFun : C(nerveSet U, X) :=
    ⟨fun t ↦ g (cubeNormalize t), hgCub.comp_continuous (continuousOn_cubeNormalize.comp_continuous
      continuous_subtype_val fun t ↦ t.2.1) fun t ↦ mem_iUnion₂.2
        ⟨(_, _), mem_nerveCells.2 (cubeNormalize_mem t.2).1, (cubeNormalize_mem t.2).2.1⟩⟩
  refine ⟨⟨toFun, invFun, homotopic_id_of_eq_nerveInverse hCX
    (A := fun I ↦ coverInter (fun i ↦ tsupport (φ i)) I)
    (fun I ↦ isClosed_biInter fun i _ ↦ isClosed_tsupport _) (fun _ _ h ↦ coverInter_anti _ h)
    (fun I x hx ↦ mem_coverInter.2 fun i hi ↦ hφU i (mem_coverInter.1 hx i hi)) hg hΦc hΦN
    (fun x ↦ mem_coverInter.2 (hΦsupp x)) _ fun _ ↦ rfl, ?_⟩⟩
  exact homotopic_id_of_eq_comp_nerveInverse hg hΦc hΦmem (fun x i hi ↦ hφU i (hΦsupp x i hi)) _
    fun _ ↦ rfl

end Nerve

section Realisation

variable {ι X E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

omit [DecidableEq ι] in
/-- A face of the standard simplex is convex. -/
theorem convex_simplexFace (I : Finset ι) : Convex ℝ (simplexFace I) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ ?_, ?_, fun i hi ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx.2.1, hy.2.1, mul_one, hab]
  · simp [hx.2.2 i hi, hy.2.2 i hi]

/-- The face of the standard simplex spanned by `I` is the convex hull of the basis vectors
`Pi.single i 1` for `i ∈ I`. -/
theorem convexHull_image_single (I : Finset ι) :
    convexHull ℝ ((fun i ↦ (Pi.single i (1 : ℝ) : ι → ℝ)) '' (I : Set ι)) = simplexFace I := by
  apply le_antisymm
  · refine convexHull_min ?_ (convex_simplexFace I)
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨fun j ↦ ?_, by simp, fun j hj ↦ ?_⟩
    · by_cases h : j = i <;> simp [h]
    · simp [show j ≠ i from fun h ↦ hj (h ▸ hi)]
  · intro t ht
    have ht' : t = ∑ i ∈ I, t i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      ext j
      by_cases hj : j ∈ I <;> simp [Finset.sum_apply, Pi.single_apply, hj, ht.2.2 j]
    rw [ht']
    refine (convex_convexHull ℝ _).sum_mem (fun i _ ↦ ht.1 i) ?_
      fun i hi ↦ subset_convexHull ℝ _ ⟨i, hi, rfl⟩
    rw [← ht.2.1]
    exact Finset.sum_subset (Finset.subset_univ I) fun j _ hj ↦ ht.2.2 j hj

/-- The vertices `L eᵢ` of the realisation of the nerve. -/
def nerveVertex (L : (ι → ℝ) ≃L[ℝ] E) (i : ι) : E := L (Pi.single i 1)

omit [DecidableEq E] [Fintype ι] in
/-- Distinct indices give distinct vertices. -/
theorem nerveVertex_injective (L : (ι → ℝ) ≃L[ℝ] E) : Injective (nerveVertex L) := by
  intro i j h
  have h' := congrFun (L.injective h) i
  by_contra hij
  simp [hij] at h'

/-- The convex hull of the vertices indexed by `I` is the image under `L` of the face of the
standard simplex spanned by `I`. -/
theorem convexHull_image_nerveVertex (L : (ι → ℝ) ≃L[ℝ] E) (I : Finset ι) :
    convexHull ℝ ((I.image (nerveVertex L) : Finset E) : Set E) = L '' simplexFace I := by
  rw [Finset.coe_image, ← convexHull_image_single]
  have := (LinearMap.image_convexHull (L : (ι → ℝ) →ₗ[ℝ] E)
    ((fun i ↦ (Pi.single i (1 : ℝ) : ι → ℝ)) '' (I : Set ι))).symm
  rwa [image_image] at this

/-- The geometric realisation of the nerve of `U` as a simplicial complex in `E`, with vertices the
images `L eᵢ` of the standard basis vectors. -/
def nerveComplex (U : ι → Set X) (L : (ι → ℝ) ≃L[ℝ] E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ I : Finset ι, I.Nonempty ∧ (coverInter U I).Nonempty ∧
    s = I.image (nerveVertex L)}
  isRelLowerSet_faces := by
    rintro s ⟨I, hI, hU, rfl⟩
    refine ⟨hI.image _, fun t ht htne ↦ ?_⟩
    classical
    refine ⟨I.filter fun i ↦ nerveVertex L i ∈ t, ?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := htne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (ht hx)
      exact ⟨i, Finset.mem_filter.2 ⟨hi, hx⟩⟩
    · exact hU.mono (coverInter_anti U (Finset.filter_subset _ I))
    · ext x
      simp only [Finset.mem_image, Finset.mem_filter]
      refine ⟨fun hx ↦ ?_, fun ⟨_, ⟨_, hx⟩, h⟩ ↦ h ▸ hx⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (ht hx)
      exact ⟨i, ⟨hi, hx⟩, rfl⟩
  indep := by
    rintro s ⟨I, -, -, rfl⟩
    have hli : LinearIndependent ℝ (nerveVertex L) :=
      (Pi.linearIndependent_single_one ι ℝ).map' (L : (ι → ℝ) →ₗ[ℝ] E)
        (LinearEquiv.ker L.toLinearEquiv)
    exact hli.affineIndependent.range.mono (show ((I.image (nerveVertex L) : Finset E) : Set E) ⊆
      range (nerveVertex L) by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact mem_range_self i)
  inter_subset_convexHull := by
    rintro _ _ ⟨I, -, -, rfl⟩ ⟨J, -, -, rfl⟩ x ⟨hxI, hxJ⟩
    rw [convexHull_image_nerveVertex] at hxI hxJ
    obtain ⟨a, ha, rfl⟩ := hxI
    obtain ⟨b, hb, hab⟩ := hxJ
    obtain rfl := L.injective hab
    have hIJ : b ∈ simplexFace (I ∩ J) :=
      ⟨hb.1, hb.2.1, fun i hi ↦ by
        rw [Finset.mem_inter, not_and_or] at hi
        exact hi.elim (ha.2.2 i) (hb.2.2 i)⟩
    have := convexHull_image_nerveVertex L (I ∩ J) ▸ mem_image_of_mem L hIJ
    refine convexHull_mono ?_ this
    rw [Finset.coe_image, Finset.coe_image, Finset.coe_image, Finset.coe_inter]
    exact image_inter_subset _ _ _

/-- The simplicial complex `nerveComplex U L` has finitely many faces. -/
theorem nerveComplex_faces_finite (U : ι → Set X) (L : (ι → ℝ) ≃L[ℝ] E) :
    (nerveComplex U L).faces.Finite :=
  (Set.finite_range fun I : Finset ι ↦ I.image (nerveVertex L)).subset
    fun _ ⟨I, _, _, h⟩ ↦ ⟨I, h.symm⟩

/-- The space of `nerveComplex U L` is the image under `L` of `nerveSet U`. -/
theorem nerveComplex_space (U : ι → Set X) (L : (ι → ℝ) ≃L[ℝ] E) :
    (nerveComplex U L).space = L '' nerveSet U := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨_, ⟨I, -, hU, rfl⟩, hx⟩
    rw [convexHull_image_nerveVertex] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact mem_image_of_mem L ⟨simplexFace_mono (Finset.subset_univ I) ht,
      hU.mono (coverInter_anti U (filter_subset_of_mem_simplexFace ht))⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨vecSupp t, filter_nonempty_of_mem_simplexFace ht.1, ht.2, rfl⟩, ?_⟩
    rw [convexHull_image_nerveVertex]
    exact mem_image_of_mem L (mem_simplexFace_filter ht.1)

end Realisation

section FiniteComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The space of a finite simplicial complex is compact. -/
theorem isCompact_space_of_finite (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    IsCompact K.space :=
  hK.isCompact_biUnion fun s _ ↦ s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)

/-- A map which is continuous on each face of a finite simplicial complex is continuous on its
space. -/
theorem continuousOn_space_of_finite {Y : Type*} [TopologicalSpace Y]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) {f : E → Y}
    (hf : ∀ s ∈ K.faces, ContinuousOn f (convexHull ℝ (s : Set E))) :
    ContinuousOn f K.space := by
  have : ∀ s ∈ hK.toFinset, IsClosed (convexHull ℝ (s : Set E)) :=
    fun s _ ↦ (s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  simpa [Geometry.SimplicialComplex.space] using
    continuousOn_biUnion_finset this fun s hs ↦ hf s (hK.mem_toFinset.1 hs)

end FiniteComplex

/-- **The nerve theorem.** Let `X` be a paracompact Hausdorff space with a finite open cover `U`
such that every nonempty intersection of finitely many (at least one) members of `U` is
contractible. Then `X` is homotopy equivalent to a finite simplicial complex, the realisation of
the nerve of `U`. -/
theorem exists_homotopyEquiv_simplicialComplex_of_contractible_cover {X : Type*}
    [TopologicalSpace X] [ParacompactSpace X] [T2Space X] {ι : Type*} [Finite ι]
    (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hUc : ⋃ i, U i = univ)
    (hU : ∀ I : Finset ι, I.Nonempty → (⋂ i ∈ I, U i).Nonempty →
      ContractibleSpace (⋂ i ∈ I, U i)) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv X K.space) := by
  classical
  have := Fintype.ofFinite ι
  have h1 : Nonempty (ContinuousMap.HomotopyEquiv X (nerveSet U)) := by
    rcases isEmpty_or_nonempty X with hX | hX
    · have : IsEmpty (nerveSet U) := ⟨fun t ↦ by
        obtain ⟨x, -⟩ := t.2.2
        exact hX.false x⟩
      exact ⟨(Homeomorph.empty).toHomotopyEquiv⟩
    · obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUo (by rw [hUc])
      exact nonempty_homotopyEquiv_nerveSet U hU (fun i ↦ φ i) (fun i x ↦ φ.nonneg i x)
        (fun x ↦ by rw [← finsum_eq_sum_of_fintype]; exact φ.sum_eq_one (mem_univ x)) hφ
  let L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin ι).symm).toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Fintype.card ι)) ℝ).symm
  obtain ⟨h⟩ := h1
  exact ⟨_, nerveComplex U L, nerveComplex_faces_finite U L,
    ⟨h.trans ((L.toHomeomorph.image (nerveSet U)).trans
      (Homeomorph.setCongr (nerveComplex_space U L).symm)).toHomotopyEquiv⟩⟩

end

end MMP.Topology
