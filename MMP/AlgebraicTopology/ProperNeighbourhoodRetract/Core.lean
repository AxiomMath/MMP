module

public import MMP.AlgebraicTopology.ProperNeighbourhoodRetract.Cone
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Data.Set.Card

/-!
# Neighbourhood retractions onto locally contractible closed sets (Borsuk)

Let `X` be a closed subset of a metric space `E`, *locally contractible* in the strong sense that
every point of `X` has arbitrarily small contractible neighbourhoods in `X`. Suppose `E - X` is
covered by open sets `B i`, each with a point `a i ∈ X` and a tolerance `η i > 0`, such that

* near a point `x ∈ X` the sets `B i` meeting a small ball about `x` have `a i` close to `x` and
  `η i` small, and
* near a point of `X` every point of `E - X` lies in a bounded number of the `B i`.

Then `X` is a retract of an open neighbourhood. Take a partition of unity `φ` on `E - X`
subordinate to the `B i`, so `z ↦ (φ i z)ᵢ` maps `E - X` into the simplices `Δ s` spanned by the
finite sets `s` of indices of sets containing `z`. Build `R : Δ s → X` by induction on `|s|`: a
vertex `i` goes to `a i`; on a larger simplex, `R` is already defined on the boundary, with image
in a contractible set `W ⊆ X` (chosen of nearly minimal diameter), and the cone filling through a
contraction of `W` extends it. Near `x ∈ X`, all simplices of bounded dimension whose sets meet a
small ball go into a small ball about `x`: this is the control, proved by induction on the
dimension. The retraction is `r = R ∘ φ` off `X` and the identity on `X`.

## Main definitions

* `MMP.NbhdRetract.stage`: `R` on simplices of dimension `< n`.

## Main results

* `MMP.NbhdRetract.control`: the control near `X`.
* `MMP.NbhdRetract.exists_retraction`: the neighbourhood retraction.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], Appendix, Theorem A.7.
* K. Borsuk, *Theory of retracts*, V.7.
-/

@[expose] public section

open Set Topology Filter Metric

namespace MMP

/-- A function continuous on each of finitely many closed sets is continuous on their union. -/
theorem continuousOn_biUnion_finset {α β κ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {g : α → β} (S : Finset κ) {A : κ → Set α} (hA : ∀ i ∈ S, IsClosed (A i))
    (hg : ∀ i ∈ S, ContinuousOn g (A i)) : ContinuousOn g (⋃ i ∈ S, A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.set_biUnion_insert]
    exact (hg j (Finset.mem_insert_self j S)).union_of_isClosed
      (ih (fun i hi ↦ hA i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
      (hA j (Finset.mem_insert_self j S))
      (isClosed_biUnion_finset fun i hi ↦ hA i (Finset.mem_insert_of_mem hi))

namespace NbhdRetract

open ConeFill

variable {E : Type*} [MetricSpace E]

/-- `H` is a contraction of `W` to `c`: from the identity at time `0` to `c` at time `1`. -/
def IsContraction (W : Set E) (H : ℝ → E → E) (c : E) : Prop :=
  ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ W) ∧ (∀ y ∈ W, H 0 y = y) ∧
    (∀ y ∈ W, H 1 y = c) ∧ (∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ W, H τ y ∈ W) ∧ c ∈ W

/-- A contractible subset `W` admits a contraction `H` of `W` to some point `c`. -/
theorem exists_isContraction {W : Set E} [ContractibleSpace W] :
    ∃ H c, IsContraction W H c := by
  classical
  obtain ⟨y₀, ⟨F⟩⟩ := id_nullhomotopic W
  let H : ℝ → E → E := fun τ y ↦
    if hy : y ∈ W then (F (projIcc 0 1 zero_le_one τ, ⟨y, hy⟩) : E) else y
  have hHW : ∀ τ, ∀ y (hy : y ∈ W), H τ y = F (projIcc 0 1 zero_le_one τ, ⟨y, hy⟩) :=
    fun τ y hy ↦ dite_eq_left hy
  refine ⟨H, y₀, ?_, fun y hy ↦ ?_, fun y hy ↦ ?_, fun τ _ y hy ↦ ?_, y₀.2⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert (show Continuous fun p : (Icc (0 : ℝ) 1 ×ˢ W : Set (ℝ × E)) ↦
        (F (projIcc 0 1 zero_le_one p.1.1, ⟨p.1.2, p.2.2⟩) : E) from ?_) using 1
    · funext p
      exact hHW _ _ _
    refine continuous_subtype_val.comp (F.continuous.comp (Continuous.prodMk
      (continuous_projIcc.comp (continuous_fst.comp continuous_subtype_val)) ?_))
    exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  · rw [hHW _ _ hy, projIcc_left]
    simp
  · rw [hHW _ _ hy, projIcc_right]
    simp
  · rw [hHW _ _ hy]
    exact Subtype.coe_prop _

/-- `W` is a candidate set through which to fill `K`: a bounded contractible subset of `X`
containing `K`. -/
def IsFiller (X K W : Set E) : Prop :=
  W ⊆ X ∧ K ⊆ W ∧ Bornology.IsBounded W ∧ ContractibleSpace W

/-- A filler of nearly minimal diameter (up to `τ`), with a contraction. -/
def IsGoodFill (X K : Set E) (τ : ℝ) (W : Set E) (H : ℝ → E → E) (c : E) : Prop :=
  IsFiller X K W ∧ (∀ W', IsFiller X K W' → diam W ≤ diam W' + τ) ∧ IsContraction W H c

/-- If `K` has a filler in `X`, then for every `τ > 0` it has a good filler with a contraction. -/
theorem exists_isGoodFill {X K : Set E} {τ : ℝ} (hK : ∃ W, IsFiller X K W) (hτ : 0 < τ) :
    ∃ W H c, IsGoodFill X K τ W H c := by
  set D := diam '' {W | IsFiller X K W}
  have hD : D.Nonempty := Set.Nonempty.image diam hK
  have hDb : BddBelow D := ⟨0, by rintro _ ⟨W, _, rfl⟩; exact diam_nonneg⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hWlt⟩ := exists_lt_of_csInf_lt hD (lt_add_of_pos_right (sInf D) hτ)
  haveI := hW.2.2.2
  obtain ⟨H, c, hH⟩ := exists_isContraction (W := W)
  exact ⟨W, H, c, hW, fun W' hW' ↦ by linarith [csInf_le hDb ⟨W', hW', rfl⟩], hH⟩

variable (X : Set E) {ι : Type*} (a : ι → E) (η : ι → ℝ) (e₀ : E)

/-- The tolerance of a set of indices: the least `η i`. -/
noncomputable def tol (s : Finset ι) : ℝ := if hs : s.Nonempty then s.inf' hs η else 0

open Classical in
/-- The extension of `g` from the boundary of `Δ s` over `Δ s`: the vertex `a i` when
`s = {i}`; otherwise the cone filling through a good filler of the image of the boundary. -/
noncomputable def fillStep (g : (ι → ℝ) → E) (s : Finset ι) (t : ι → ℝ) : E :=
  if h1 : s.card = 1 then a (Finset.card_eq_one.1 h1).choose
  else if h : ∃ W H c, IsGoodFill X (g '' boundary s) (tol η s) W H c then
    fill s g h.choose_spec.choose h.choose_spec.choose_spec.choose t
  else e₀

open Classical in
/-- `R` on the simplices of dimension `< n`: at stage `n + 1` the points with `n + 1` nonzero
weights are filled from stage `n`. -/
noncomputable def stage : ℕ → (ι → ℝ) → E
  | 0 => fun _ ↦ e₀
  | n + 1 => fun t ↦
    if (Function.support t).ncard ≤ n then stage n t
    else if h : (Function.support t).Finite then fillStep X a η e₀ (stage n) h.toFinset t
    else e₀

variable {X a η e₀}

open Classical in
/-- The defining equation of `stage` at `n + 1`. -/
theorem stage_succ (n : ℕ) (t : ι → ℝ) : stage X a η e₀ (n + 1) t =
    if (Function.support t).ncard ≤ n then stage X a η e₀ n t
    else if h : (Function.support t).Finite then fillStep X a η e₀ (stage X a η e₀ n) h.toFinset t
    else e₀ := rfl

/-- A point of the face `face s` has support contained in `s`. -/
theorem support_subset_of_mem_face {s : Finset ι} {t : ι → ℝ} (ht : t ∈ face s) :
    Function.support t ⊆ s :=
  fun i hi ↦ by_contra fun h ↦ hi (ht.2.1 i h)

/-- A point of `face s` has at most `s.card` nonzero coordinates. -/
theorem ncard_support_le {s : Finset ι} {t : ι → ℝ} (ht : t ∈ face s) :
    (Function.support t).ncard ≤ s.card := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (support_subset_of_mem_face ht) s.finite_toSet

/-- On a point with at most `n` nonzero coordinates, every stage `m ≥ n` agrees with stage `n`. -/
theorem stage_eq_of_le {n m : ℕ} {t : ι → ℝ} (ht : (Function.support t).ncard ≤ n)
    (hnm : n ≤ m) : stage X a η e₀ m t = stage X a η e₀ n t := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [stage_succ, ite_eq_left (ht.trans hnm), ih]

/-- A point of `face s` with more than `s.card - 1` nonzero coordinates has support exactly `s`. -/
theorem toFinset_support_eq {s : Finset ι} {t : ι → ℝ} (ht : t ∈ face s)
    (hc : ¬ (Function.support t).ncard ≤ s.card - 1) (hf : (Function.support t).Finite) :
    hf.toFinset = s := by
  refine Finset.eq_of_subset_of_card_le (fun i hi ↦ support_subset_of_mem_face ht
    ((Set.Finite.mem_toFinset hf).1 hi)) ?_
  rw [← Set.ncard_eq_toFinset_card _ hf]
  omega

/-- For nonempty `s`, a point of `face s` with at most `s.card - 1` nonzero coordinates lies in
`boundary s`. -/
theorem mem_boundary_of_ncard_le {s : Finset ι} {t : ι → ℝ} (ht : t ∈ face s)
    (hc : (Function.support t).ncard ≤ s.card - 1) (hs : s.Nonempty) : t ∈ boundary s := by
  refine ⟨ht, ?_⟩
  by_contra h
  push Not at h
  have : (s : Set ι) ⊆ Function.support t := fun i hi ↦ h i hi
  have := Set.ncard_le_ncard this ((s.finite_toSet).subset (support_subset_of_mem_face ht))
  rw [Set.ncard_coe_finset] at this
  have := hs.card_pos
  omega

/-- A vertex `{i}` has empty boundary. -/
@[simp]
theorem boundary_singleton (i : ι) : boundary ({i} : Finset ι) = ∅ := by
  ext t
  simp only [boundary, mem_ofPred_eq, Finset.mem_singleton, exists_eq_left, mem_empty_iff_false,
    iff_false, not_and]
  intro ht hti
  simpa [hti] using ht.2.2

/-- On a vertex the first stage is the chosen point. -/
theorem stage_one_of_mem_face {i : ι} {t : ι → ℝ} (ht : t ∈ face {i}) :
    stage X a η e₀ 1 t = a i := by
  have hti : t i = 1 := by simpa using ht.2.2
  have hsupp : Function.support t = {i} := by
    ext j
    simp only [Function.mem_support, mem_singleton_iff]
    refine ⟨fun h ↦ by_contra fun hj ↦ h (ht.2.1 j (by simpa using hj)), ?_⟩
    rintro rfl
    simp [hti]
  have hf : (Function.support t).Finite := hsupp ▸ finite_singleton i
  have hfe : hf.toFinset = {i} := by
    ext j
    simp [hsupp]
  rw [stage_succ, ite_eq_right (by rw [hsupp, ncard_singleton]; omega), dite_eq_left hf, hfe,
    fillStep, dite_eq_left (Finset.card_singleton i)]
  congr 1
  exact (Finset.singleton_inj.1 (Finset.card_eq_one.1 (Finset.card_singleton i)).choose_spec).symm

/-- On a simplex of dimension `n ≥ 1` whose boundary has a good filler, stage `n + 1` is the
cone filling of stage `n`. -/
theorem stage_succ_eq_fill {s : Finset ι} {n : ℕ} (hs : s.card = n + 1) (hn : 1 ≤ n)
    (h : ∃ W H c, IsGoodFill X (stage X a η e₀ n '' boundary s) (tol η s) W H c)
    {t : ι → ℝ} (ht : t ∈ face s) :
    stage X a η e₀ (n + 1) t =
      fill s (stage X a η e₀ n) h.choose_spec.choose h.choose_spec.choose_spec.choose t := by
  have hgood := h.choose_spec.choose_spec.choose_spec
  have hne : s.card ≠ 1 := by omega
  by_cases hc : (Function.support t).ncard ≤ n
  · have hb : t ∈ boundary s := mem_boundary_of_ncard_le ht (by omega)
      (Finset.card_pos.1 (by omega))
    rw [stage_succ, ite_eq_left hc, fill_eq_of_mem_boundary hgood.2.2.2.1
      (fun p hp ↦ hgood.1.2.1 ⟨p, hp, rfl⟩) hb]
  · have hf : (Function.support t).Finite :=
      (s.finite_toSet).subset (support_subset_of_mem_face ht)
    have he := toFinset_support_eq ht (by omega) hf
    rw [stage_succ, ite_eq_right hc, dite_eq_left hf, he, fillStep, dite_eq_right hne,
      dite_eq_left h]

/-- If every `η i` is positive, the tolerance of a nonempty set of indices is positive. -/
theorem tol_pos (hη : ∀ i, 0 < η i) {s : Finset ι} (hs : s.Nonempty) : 0 < tol η s := by
  rw [tol, dite_eq_left hs]
  exact (Finset.lt_inf'_iff hs).2 fun i _ ↦ hη i

/-- The tolerance of `s` is at most `η i` for every `i ∈ s`. -/
theorem tol_le {s : Finset ι} {i : ι} (hi : i ∈ s) : tol η s ≤ η i := by
  rw [tol, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le _ hi

/-- A simplex with at least two vertices has nonempty boundary. -/
theorem boundary_nonempty {s : Finset ι} (hs : 2 ≤ s.card) : (boundary s).Nonempty := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hs
  refine ⟨Pi.single j 1, ⟨fun k ↦ ?_, fun k hk ↦ ?_, ?_⟩, i, hi, by simp [hij]⟩
  · by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  · have : k ≠ j := fun h ↦ hk (h ▸ hj)
    simp [this]
  · rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [hk]) (fun h ↦ absurd hj h)]
    simp

variable (X a η e₀) in
/-- **The control near `X`.** For `x ∈ X` and `ε > 0` there is `δ > 0` such that stage `n` is
continuous on every simplex of dimension `< n` whose sets all meet `B(x, δ)`, with values in
`X ∩ B(x, ε)`. -/
theorem control (B : ι → Set E)
    (hloc : ∀ x ∈ X, ∀ ε > 0, ∃ W ⊆ X, W ⊆ ball x ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x ρ ∩ X ⊆ W)
    (ha : ∀ i, a i ∈ X) (hη : ∀ i, 0 < η i)
    (hsmall : ∀ x ∈ X, ∀ ε > 0, ∃ δ > 0, ∀ i, (B i ∩ ball x δ).Nonempty →
      dist (a i) x < ε ∧ η i < ε) (n : ℕ) :
    ∀ x ∈ X, ∀ ε > 0, ∃ δ > 0, ∀ s : Finset ι, s.Nonempty → s.card ≤ n →
      (∀ i ∈ s, (B i ∩ ball x δ).Nonempty) →
        ContinuousOn (stage X a η e₀ n) (face s) ∧
          MapsTo (stage X a η e₀ n) (face s) (X ∩ ball x ε) := by
  classical
  induction n with
  | zero =>
    intro x _ ε _
    exact ⟨1, one_pos, fun s hs hc _ ↦ absurd hs.card_pos (by omega)⟩
  | succ n ih =>
    intro x hx ε hε
    obtain ⟨W, hWX, hWb, hWc, ρ, hρ, hρW⟩ := hloc x hx (ε / 4) (by positivity)
    set ρ' := min ρ (ε / 4)
    have hρ' : 0 < ρ' := lt_min hρ (by positivity)
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih x hx ρ' hρ'
    obtain ⟨δ₂, hδ₂, h₂⟩ := hsmall x hx (ε / 4) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hcard hnear ↦ ?_⟩
    have hnear₁ : ∀ i ∈ s, (B i ∩ ball x δ₁).Nonempty := fun i hi ↦
      (hnear i hi).mono (inter_subset_inter_right _ (ball_subset_ball (min_le_left _ _)))
    have hnear₂ : ∀ i ∈ s, (B i ∩ ball x δ₂).Nonempty := fun i hi ↦
      (hnear i hi).mono (inter_subset_inter_right _ (ball_subset_ball (min_le_right _ _)))
    have hball : ball x ρ' ⊆ ball x ε := ball_subset_ball ((min_le_right _ _).trans (by linarith))
    rcases Nat.lt_or_ge s.card (n + 1) with hlt | hge
    · obtain ⟨hc, hm⟩ := h₁ s hs (by omega) hnear₁
      have heq : EqOn (stage X a η e₀ (n + 1)) (stage X a η e₀ n) (face s) := fun t ht ↦
        stage_eq_of_le ((ncard_support_le ht).trans (by omega)) (Nat.le_succ n)
      exact ⟨hc.congr heq, fun t ht ↦ by
        rw [heq ht]; exact ⟨(hm ht).1, hball (hm ht).2⟩⟩
    have hcard' : s.card = n + 1 := le_antisymm hcard hge
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hcard'
      have heq : EqOn (stage X a η e₀ 1) (fun _ ↦ a i) (face {i}) := fun t ht ↦
        stage_one_of_mem_face ht
      refine ⟨continuousOn_const.congr heq, fun t ht ↦ ?_⟩
      rw [heq ht]
      exact ⟨ha i, mem_ball.2 ((h₂ i (hnear₂ i (Finset.mem_singleton_self i))).1.trans
        (by linarith))⟩
    · set g := stage X a η e₀ n
      have hface : ∀ i ∈ s, ContinuousOn g (face (s.erase i)) ∧
          MapsTo g (face (s.erase i)) (X ∩ ball x ρ') := fun i hi ↦
        h₁ (s.erase i) (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hi]; omega))
          (by rw [Finset.card_erase_of_mem hi]; omega)
          fun j hj ↦ hnear₁ j (Finset.mem_of_mem_erase hj)
      have hgc : ContinuousOn g (boundary s) := by
        rw [boundary_eq_biUnion]
        exact continuousOn_biUnion_finset s (fun i _ ↦ isClosed_face _) fun i hi ↦ (hface i hi).1
      have hgm : MapsTo g (boundary s) (X ∩ ball x ρ') := by
        rw [boundary_eq_biUnion]
        intro t ht
        obtain ⟨i, hi, ht⟩ := mem_iUnion₂.1 ht
        exact (hface i hi).2 ht
      have hKW : IsFiller X (g '' boundary s) W := by
        refine ⟨hWX, ?_, isBounded_ball.subset hWb, hWc⟩
        rintro _ ⟨t, ht, rfl⟩
        exact hρW ⟨ball_subset_ball (min_le_left _ _) (hgm ht).2, (hgm ht).1⟩
      have h := exists_isGoodFill ⟨W, hKW⟩ (tol_pos hη hs)
      have hgood := h.choose_spec.choose_spec.choose_spec
      set W' := h.choose
      set H := h.choose_spec.choose
      set c := h.choose_spec.choose_spec.choose
      have heq : EqOn (stage X a η e₀ (n + 1)) (fill s g H c) (face s) := fun t ht ↦
        stage_succ_eq_fill hcard' hn h ht
      have hgW : MapsTo g (boundary s) W' := fun p hp ↦ hgood.1.2.1 ⟨p, hp, rfl⟩
      refine ⟨(continuousOn_fill hgc hgW hgood.2.2.1 hgood.2.2.2.2.1).congr heq,
        fun t ht ↦ ?_⟩
      rw [heq ht]
      have hy := mapsTo_fill hgood.2.2.2.2.2.1 hgood.2.2.2.2.2.2 hgW ht
      refine ⟨hgood.1.1 hy, mem_ball.2 ?_⟩
      obtain ⟨p, hp⟩ := boundary_nonempty (s := s) (by omega)
      have hdiam : diam W' ≤ diam W + tol η s := hgood.2.1 W hKW
      have hdW : diam W ≤ 2 * (ε / 4) :=
        (diam_mono hWb isBounded_ball).trans (diam_ball (by positivity))
      obtain ⟨i, hi⟩ := hs
      have htol : tol η s < ε / 4 := (tol_le hi).trans_lt (h₂ i (hnear₂ i hi)).2
      have h1 : dist (fill s g H c t) (g p) ≤ diam W' :=
        dist_le_diam_of_mem hgood.1.2.2.1 hy (hgW hp)
      have h2 : dist (g p) x < ρ' := (hgm hp).2
      have h3 : ρ' ≤ ε / 4 := min_le_right _ _
      linarith [dist_triangle (fill s g H c t) (g p) x]

/-- **Borsuk's neighbourhood retraction.** Let `X` be closed in a metric space `E`, with
arbitrarily small contractible neighbourhoods in `X` of each of its points. Let the open sets `B i`
cover `E - X`, with points `a i ∈ X` and tolerances `η i > 0`, such that the sets `B i` meeting a
small ball about a point `x ∈ X` have `a i` and `η i` close to `x` and to `0`, and near each point
of `X` every point of `E - X` lies in a bounded number of the `B i`. Then `X` is a retract of an
open neighbourhood. -/
theorem exists_retraction {X : Set E} (hX : IsClosed X)
    (hloc : ∀ x ∈ X, ∀ ε > 0, ∃ W ⊆ X, W ⊆ ball x ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x ρ ∩ X ⊆ W)
    {ι : Type*} (B : ι → Set E) (a : ι → E) (η : ι → ℝ) (hBo : ∀ i, IsOpen (B i))
    (ha : ∀ i, a i ∈ X) (hη : ∀ i, 0 < η i) (hcov : ∀ y ∉ X, ∃ i, y ∈ B i)
    (hsmall : ∀ x ∈ X, ∀ ε > 0, ∃ δ > 0, ∀ i, (B i ∩ ball x δ).Nonempty →
      dist (a i) x < ε ∧ η i < ε)
    (hord : ∀ x ∈ X, ∃ δ > 0, ∃ d : ℕ, ∀ y ∈ ball x δ, y ∉ X →
      {i | y ∈ B i}.Finite ∧ {i | y ∈ B i}.ncard ≤ d) :
    ∃ U : Set E, IsOpen U ∧ X ⊆ U ∧ ∃ r : E → E, ContinuousOn r U ∧ MapsTo r U X ∧
      ∀ x ∈ X, r x = x := by
  classical
  rcases X.eq_empty_or_nonempty with rfl | ⟨e₀, -⟩
  · exact ⟨∅, isOpen_empty, subset_rfl, id, continuousOn_empty _, mapsTo_empty _ _, by simp⟩
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := (Xᶜ : Set E)) (s := univ)
    isClosed_univ (fun i ↦ Subtype.val ⁻¹' B i) (fun i ↦ (hBo i).preimage continuous_subtype_val)
    (fun z _ ↦ mem_iUnion.2 (hcov z z.2))
  set w : E → ι → ℝ := fun z i ↦ if hz : z ∈ X then 0 else f i ⟨z, hz⟩ with hw
  have hwz : ∀ z (hz : z ∉ X) i, w z i = f i ⟨z, hz⟩ := fun z hz i ↦ by simp [hw, hz]
  have hw_sub : ∀ z (hz : z ∉ X) i, w z i ≠ 0 → z ∈ B i := fun z hz i h ↦ by
    rw [hwz z hz] at h
    exact hf i (subset_tsupport _ h)
  have hw_fin : ∀ z (hz : z ∉ X), (Function.support (w z)).Finite := fun z hz ↦ by
    convert f.locallyFinite.point_finite ⟨z, hz⟩ using 1
    ext i; simp [hwz z hz]
  have hw_face : ∀ z (hz : z ∉ X), w z ∈ face (hw_fin z hz).toFinset := by
    intro z hz
    refine ⟨fun i ↦ by rw [hwz z hz]; exact f.nonneg i _, fun i hi ↦ ?_, ?_⟩
    · simpa using hi
    · rw [← finsum_eq_sum_of_support_subset _ (by simp)]
      simp_rw [hwz z hz]
      exact f.sum_eq_one (mem_univ _)
  have hw_ne : ∀ z (hz : z ∉ X), (hw_fin z hz).toFinset.Nonempty := fun z hz ↦ by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := (hw_face z hz).2.2
    rw [h, Finset.sum_empty] at this
    exact zero_ne_one this
  have hw_cont : ContinuousOn w Xᶜ := by
    refine continuousOn_pi.2 fun i ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    convert (f i).continuous using 1
    funext z; exact hwz z.1 z.2 i
  set R : (ι → ℝ) → E := fun t ↦ stage X a η e₀ (Function.support t).ncard t
  set r : E → E := fun z ↦ if z ∈ X then z else R (w z) with hr
  have key : ∀ x ∈ X, ∀ ε > 0, ∃ δ > 0, ∃ d : ℕ,
      (∀ z ∈ ball x δ, (hz : z ∉ X) →
        r z = stage X a η e₀ d (w z) ∧ (hw_fin z hz).toFinset.card ≤ d) ∧
      ∀ s : Finset ι, s.Nonempty → s.card ≤ d → (∀ i ∈ s, (B i ∩ ball x δ).Nonempty) →
        ContinuousOn (stage X a η e₀ d) (face s) ∧
          MapsTo (stage X a η e₀ d) (face s) (X ∩ ball x ε) := by
    intro x hx ε hε
    obtain ⟨δo, hδo, d, hd⟩ := hord x hx
    obtain ⟨δc, hδc, hc⟩ := control X a η e₀ B hloc ha hη hsmall d x hx ε hε
    refine ⟨min δo δc, lt_min hδo hδc, d, fun z hz hzX ↦ ?_, fun s hs hcard hnear ↦
      hc s hs hcard fun i hi ↦ (hnear i hi).mono
        (inter_subset_inter_right _ (ball_subset_ball (min_le_right _ _)))⟩
    obtain ⟨hfin, hcard⟩ := hd z (ball_subset_ball (min_le_left _ _) hz) hzX
    have hle : (Function.support (w z)).ncard ≤ d :=
      (Set.ncard_le_ncard (fun i hi ↦ hw_sub z hzX i hi) hfin).trans hcard
    refine ⟨?_, by rwa [← Set.ncard_eq_toFinset_card _ (hw_fin z hzX)]⟩
    simp only [hr, R, ite_eq_right hzX]
    exact (stage_eq_of_le le_rfl hle).symm
  have hnearT : ∀ (x : E) (δ : ℝ), ∀ z ∈ ball x δ, ∀ (hz : z ∉ X),
      ∀ i ∈ (hw_fin z hz).toFinset, (B i ∩ ball x δ).Nonempty := fun x δ z hzb hz i hi ↦
    ⟨z, hw_sub z hz i ((Set.Finite.mem_toFinset _).1 hi), hzb⟩
  choose! δ hδ d hd using fun x hx ↦ key x hx 1 one_pos
  refine ⟨⋃ x ∈ X, ball x (δ x), isOpen_biUnion fun _ _ ↦ isOpen_ball,
    fun x hx ↦ mem_biUnion hx (mem_ball_self (hδ x hx)), r, ?_, ?_, fun x hx ↦ ite_eq_left hx⟩
  rotate_left
  · intro z hz
    obtain ⟨x, hx, hzb⟩ := mem_iUnion₂.1 hz
    by_cases hzX : z ∈ X
    · simpa only [hr, ite_eq_left hzX] using hzX
    · obtain ⟨hrz, hcard⟩ := (hd x hx).1 z hzb hzX
      rw [hrz]
      exact ((hd x hx).2 _ (hw_ne z hzX) hcard (hnearT x _ z hzb hzX)).2 (hw_face z hzX) |>.1
  refine fun z hz ↦ ContinuousAt.continuousWithinAt ?_
  by_cases hzX : z ∈ X
  · refine Metric.continuousAt_iff.2 fun ε hε ↦ ?_
    obtain ⟨δ', hδ', d', hd'⟩ := key z hzX ε hε
    refine ⟨min δ' ε, lt_min hδ' hε, fun {y} hy ↦ ?_⟩
    rw [show r z = z from ite_eq_left hzX]
    by_cases hyX : y ∈ X
    · rw [show r y = y from ite_eq_left hyX]
      exact hy.trans_le (min_le_right _ _)
    · have hyb : y ∈ ball z δ' := mem_ball.2 (hy.trans_le (min_le_left _ _))
      obtain ⟨hry, hcard⟩ := hd'.1 y hyb hyX
      rw [hry]
      exact (hd'.2 _ (hw_ne y hyX) hcard (hnearT z _ y hyb hyX)).2 (hw_face y hyX) |>.2
  · obtain ⟨x, hx, hzb⟩ := mem_iUnion₂.1 hz
    obtain ⟨t, ht, hfin⟩ := f.locallyFinite ⟨z, hzX⟩
    set F := hfin.toFinset
    set 𝒮 := F.powerset.filter fun s ↦ s.Nonempty ∧ s.card ≤ d x ∧
      ∀ i ∈ s, (B i ∩ ball x (δ x)).Nonempty
    set T' := Subtype.val '' t ∩ ball x (δ x)
    have hT' : T' ∈ 𝓝 z := inter_mem
      ((hX.isOpen_compl.isOpenEmbedding_subtypeVal.image_mem_nhds).2 ht)
      (isOpen_ball.mem_nhds hzb)
    have hT'X : ∀ y ∈ T', y ∉ X := by rintro _ ⟨⟨p, _, rfl⟩, _⟩; exact p.2
    have hmaps : MapsTo w T' (⋃ s ∈ 𝒮, face s) := by
      rintro _ ⟨⟨p, hp, rfl⟩, hyb⟩
      refine mem_biUnion (x := (hw_fin p.1 p.2).toFinset) ?_ (hw_face p.1 p.2)
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun i hi ↦ ?_, hw_ne p.1 p.2,
        ((hd x hx).1 p.1 hyb p.2).2, hnearT x _ p.1 hyb p.2⟩
      rw [Set.Finite.mem_toFinset] at hi ⊢
      rw [Function.mem_support, hwz p.1 p.2] at hi
      exact ⟨p, hi, hp⟩
    have hcontA : ContinuousOn (stage X a η e₀ (d x)) (⋃ s ∈ 𝒮, face s) :=
      continuousOn_biUnion_finset 𝒮 (fun _ _ ↦ isClosed_face _) fun s hs ↦ by
        obtain ⟨-, hs1, hs2, hs3⟩ := Finset.mem_filter.1 hs
        exact ((hd x hx).2 s hs1 hs2 hs3).1
    have hcomp : ContinuousOn (stage X a η e₀ (d x) ∘ w) T' :=
      hcontA.comp (hw_cont.mono fun y hy ↦ hT'X y hy) hmaps
    refine (hcomp.continuousAt hT').congr ?_
    filter_upwards [hT'] with y hy
    exact ((hd x hx).1 y hy.2 (hT'X y hy)).1.symm

end NbhdRetract

end MMP
