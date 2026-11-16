module

public import MMP.AlgebraicTopology.SingularHomology.ShuffleProduct
public import Mathlib.Data.List.GetD

/-!
# Lattice paths starting with vertical steps

For the cap product of a cochain `φ` of degree `j` pulled back along the projection
`X × Y → Y` with a cross product `σ × τ`, only the lattice paths of the shuffle sum `∇_{p,n}`
whose first `j` steps are vertical (in the `Y` direction) contribute: on the other paths the
front `j`-face of the path simplex projects to a degenerate simplex of `Y`. This file contains the
combinatorics: deleting the first `j` (vertical) steps of these paths gives `(-1)^{pj} ∇_{p,n-j}`.

## Main definitions

* `MMP.LatticePath.IsVerticalStart j l`: the first `j` steps of `l` are vertical.
* `MMP.LatticePath.dropVertical j l`: delete the first `j` vertices and shift the
  second coordinates by `-j`.

## Main results

* `MMP.LatticePath.mapDomain_dropVertical_filter_shuffleSum`: deleting the first `j` vertical
  steps of the paths of `∇_{p, j + q}` that start with `j` vertical steps gives
  `(-1)^{pj} ∇_{p,q}`.
* `MMP.LatticePath.IsUnitPath.isVerticalStart_of_injOn`: a unit path whose first `j + 1`
  second coordinates are pairwise distinct starts with `j` vertical steps.
-/

@[expose] public noncomputable section

open Finsupp

/-- Filtering `mapDomain f x` by `P` is `mapDomain f` of `x` filtered by `P ∘ f`. -/
lemma Finsupp.filter_mapDomain {α β M : Type*} [AddCommMonoid M]
    (P : β → Prop) [DecidablePred P] (f : α → β) (x : α →₀ M) :
    (Finsupp.mapDomain f x).filter P = Finsupp.mapDomain f (x.filter (P ∘ f)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [Finsupp.mapDomain_zero, Finsupp.filter_zero]
  | add x y hx hy => rw [Finsupp.mapDomain_add, Finsupp.filter_add, hx, hy, Finsupp.filter_add,
      Finsupp.mapDomain_add]
  | single a b =>
    rw [Finsupp.mapDomain_single]
    by_cases h : P (f a)
    · rw [Finsupp.filter_single_of_pos _ h, Finsupp.filter_single_of_pos (P ∘ f) h,
        Finsupp.mapDomain_single]
    · rw [Finsupp.filter_single_of_neg _ h, Finsupp.filter_single_of_neg (P ∘ f) h,
        Finsupp.mapDomain_zero]

namespace MMP

namespace LatticePath

/-- The first `j` steps of the lattice path `l` are vertical: its first `j + 1` vertices are
`(0, 0), (0, 1), …, (0, j)`. -/
def IsVerticalStart (j : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  l.take (j + 1) = (List.range (j + 1)).map fun i ↦ (0, i)

/-- `IsVerticalStart j` is decidable. -/
instance (j : ℕ) : DecidablePred (IsVerticalStart j) := fun _ ↦
  inferInstanceAs (Decidable (_ = _))

/-- Delete the first `j` vertices of `l` and shift the second coordinates by `-j`. -/
def dropVertical (j : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (l.drop j).map fun v ↦ (v.1, v.2 - j)

/-- A path has a vertical start of length `0` if and only if its first vertex is `(0, 0)`. -/
lemma isVerticalStart_zero_iff (l : List (ℕ × ℕ)) :
    IsVerticalStart 0 l ↔ l.take 1 = [(0, 0)] := by
  simp [IsVerticalStart]

/-- Deleting no vertical steps leaves the path unchanged. -/
@[simp]
lemma dropVertical_zero (l : List (ℕ × ℕ)) : dropVertical 0 l = l := by
  simp [dropVertical]

/-- A path whose first step is horizontal does not start with `j + 1` vertical steps. -/
@[simp]
lemma not_isVerticalStart_succ_stepFst (j : ℕ) (l : List (ℕ × ℕ)) :
    ¬ IsVerticalStart (j + 1) (stepFst l) := by
  intro h
  unfold IsVerticalStart at h
  rw [List.range_succ_eq_map, List.map_cons, List.map_map] at h
  simp only [stepFst, List.take_succ_cons, List.cons.injEq, true_and] at h
  cases l with
  | nil => simp at h
  | cons v l =>
    rw [List.map_cons, List.take_succ_cons, List.range_succ_eq_map, List.map_cons] at h
    have := (List.cons.inj h).1
    simp at this

/-- A path whose first step is vertical starts with `j + 1` vertical steps if and only if the
remaining path starts with `j` vertical steps. -/
@[simp]
lemma isVerticalStart_succ_stepSnd_iff (j : ℕ) (l : List (ℕ × ℕ)) :
    IsVerticalStart (j + 1) (stepSnd l) ↔ IsVerticalStart j l := by
  unfold IsVerticalStart
  have hinj : Function.Injective fun v : ℕ × ℕ ↦ (v.1, v.2 + 1) := fun v w h ↦ by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [stepSnd, List.take_succ_cons, List.cons.injEq, true_and]
  rw [← List.map_take]
  have : ((fun i ↦ ((0 : ℕ), i)) ∘ Nat.succ) = (fun v : ℕ × ℕ ↦ (v.1, v.2 + 1)) ∘
      (fun i ↦ ((0 : ℕ), i)) := rfl
  rw [this, ← List.map_map]
  exact (List.map_injective_iff.2 hinj).eq_iff

/-- Deleting `j + 1` vertical steps from `stepSnd l` is the same as deleting `j` from `l`. -/
@[simp]
lemma dropVertical_succ_stepSnd (j : ℕ) (l : List (ℕ × ℕ)) :
    dropVertical (j + 1) (stepSnd l) = dropVertical j l := by
  simp only [dropVertical, stepSnd, List.drop_succ_cons, ← List.map_drop, List.map_map]
  congr 1
  funext v
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  omega

/-- A lattice path with unit steps from the origin: the `i`-th vertex has coordinate sum `i`, and
both coordinates are nondecreasing. -/
def IsUnitPath (l : List (ℕ × ℕ)) : Prop :=
  (∀ i (h : i < l.length), l[i].1 + l[i].2 = i) ∧
    ∀ i (h : i + 1 < l.length), l[i].1 ≤ l[i + 1].1 ∧ l[i].2 ≤ l[i + 1].2

/-- The one-vertex path at the origin is a unit path. -/
lemma isUnitPath_singleton : IsUnitPath [(0, 0)] :=
  ⟨fun | 0, _ => rfl, fun i h ↦ by simp at h⟩

/-- Prepending a horizontal step to a unit path gives a unit path. -/
lemma IsUnitPath.stepFst {l : List (ℕ × ℕ)} (hl : IsUnitPath l) : IsUnitPath (stepFst l) := by
  refine ⟨fun i h ↦ ?_, fun i h ↦ ?_⟩
  · rcases i with _ | i
    · rfl
    · simp only [LatticePath.stepFst, List.getElem_cons_succ, List.getElem_map]
      simp only [LatticePath.stepFst, List.length_cons, List.length_map] at h
      have := hl.1 i (by omega)
      omega
  · simp only [LatticePath.stepFst, List.length_cons, List.length_map] at h
    rcases i with _ | i
    · simp only [LatticePath.stepFst, List.getElem_cons_zero, List.getElem_cons_succ,
        List.getElem_map]
      omega
    · simp only [LatticePath.stepFst, List.getElem_cons_succ, List.getElem_map]
      have := hl.2 i (by omega)
      omega

/-- Prepending a vertical step to a unit path gives a unit path. -/
lemma IsUnitPath.stepSnd {l : List (ℕ × ℕ)} (hl : IsUnitPath l) : IsUnitPath (stepSnd l) := by
  refine ⟨fun i h ↦ ?_, fun i h ↦ ?_⟩
  · rcases i with _ | i
    · rfl
    · simp only [LatticePath.stepSnd, List.getElem_cons_succ, List.getElem_map]
      simp only [LatticePath.stepSnd, List.length_cons, List.length_map] at h
      have := hl.1 i (by omega)
      omega
  · simp only [LatticePath.stepSnd, List.length_cons, List.length_map] at h
    rcases i with _ | i
    · simp only [LatticePath.stepSnd, List.getElem_cons_zero, List.getElem_cons_succ,
        List.getElem_map]
      omega
    · simp only [LatticePath.stepSnd, List.getElem_cons_succ, List.getElem_map]
      have := hl.2 i (by omega)
      omega

/-- A nonempty unit path starts at the origin. -/
lemma IsUnitPath.getElem_zero {l : List (ℕ × ℕ)} (hl : IsUnitPath l) (h : 0 < l.length) :
    l[0] = (0, 0) := by
  have := hl.1 0 h
  exact Prod.ext (by omega) (by omega)

/-- The paths of the shuffle sum are unit paths. -/
lemma isUnitPath_of_mem_support_shuffleSum {n p q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum n p q).support) : IsUnitPath l := by
  classical
  induction n generalizing p q l with
  | zero =>
    simp only [shuffleSum] at h
    split_ifs at h
    · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at h
      subst h
      exact isUnitPath_singleton
    · simp at h
  | succ n ih =>
    rw [shuffleSum_succ] at h
    rcases Finset.mem_union.1 (Finsupp.support_add h) with h | h
    · rw [lmap, Finsupp.lmapDomain_apply] at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      rcases p with _ | p
      · simp at hl'
      · exact (ih hl').stepFst
    · have h := Finsupp.support_smul h
      rw [lmap, Finsupp.lmapDomain_apply] at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      rcases q with _ | q
      · simp at hl'
      · exact (ih hl').stepSnd

/-- Every path of the shuffle sum starts at the origin. -/
lemma take_one_of_mem_support_shuffleSum {n p q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum n p q).support) : l.take 1 = [(0, 0)] := by
  have hlen := (mem_support_shuffleSum h).1
  have hu := isUnitPath_of_mem_support_shuffleSum h
  obtain ⟨v, l', rfl⟩ : ∃ v l', l = v :: l' := by
    cases l with
    | nil => simp at hlen
    | cons v l' => exact ⟨v, l', rfl⟩
  have := hu.getElem_zero (by simp)
  simp only [List.getElem_cons_zero] at this
  simp [this]

/-- A unit path whose first `j + 1` second coordinates are pairwise distinct starts with `j`
vertical steps. -/
lemma IsUnitPath.isVerticalStart_of_injOn {l : List (ℕ × ℕ)} (hl : IsUnitPath l) {j : ℕ}
    (hj : j < l.length) (hinj : Set.InjOn (fun i ↦ (l.getD i (0, 0)).2) (Set.Iic j)) :
    IsVerticalStart j l := by
  have key : ∀ i (h : i ≤ j), l[i]'(by omega) = (0, i) := by
    intro i
    induction i with
    | zero => exact fun _ ↦ hl.getElem_zero (by omega)
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have hs := hl.1 (i + 1) (by omega)
      have hm := hl.2 i (by omega)
      rw [h1] at hm
      have hne : (l[i + 1]'(by omega)).2 ≠ i := by
        intro he
        have := @hinj (i + 1) (Set.mem_Iic.2 hi) i (Set.mem_Iic.2 (by omega)) (by
          dsimp only
          rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega), he, h1])
        omega
      simp only at hm
      exact Prod.ext (by omega) (by simp only; omega)
  unfold IsVerticalStart
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    exact key i (by omega)

/-- On a vertical start of length `j`, the `i`-th vertex is `(0, i)` for `i ≤ j`. -/
lemma IsVerticalStart.getD_eq {j : ℕ} {l : List (ℕ × ℕ)} (h : IsVerticalStart j l) {i : ℕ}
    (hi : i ≤ j) : l.getD i (0, 0) = (0, i) := by
  have hlen : j + 1 ≤ l.length := by
    have := congrArg List.length h
    simp at this
    omega
  rw [List.getD_eq_getElem _ _ (by omega)]
  have h2 := List.getElem_of_eq h (i := i) (by simp; omega)
  simpa using h2

/-- After a vertical start of length `j`, the second coordinates are at least `j`. -/
lemma IsVerticalStart.le_snd {j : ℕ} {l : List (ℕ × ℕ)} (h : IsVerticalStart j l)
    (hl : IsUnitPath l) {i : ℕ} (hi : j ≤ i) (hil : i < l.length) : j ≤ (l.getD i (0, 0)).2 := by
  induction i, hi using Nat.le_induction with
  | base => rw [h.getD_eq le_rfl]
  | succ i hji ih =>
    have := ih (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at this ⊢
    exact this.trans (hl.2 i hil).2

/-- The `i`-th vertex of `dropVertical j l` is the `(i + j)`-th vertex of `l` with its second
coordinate decreased by `j`. -/
lemma getD_dropVertical {j : ℕ} {l : List (ℕ × ℕ)} {i : ℕ} (hi : i + j < l.length) :
    (dropVertical j l).getD i (0, 0) =
      ((l.getD (i + j) (0, 0)).1, (l.getD (i + j) (0, 0)).2 - j) := by
  rw [List.getD_eq_getElem _ _ (by simp [dropVertical]; omega),
    List.getD_eq_getElem _ _ hi]
  simp only [dropVertical, List.getElem_map, List.getElem_drop]
  have e : j + i = i + j := Nat.add_comm _ _
  simp only [e]

/-- Deleting the first `j` vertical steps of the paths of `∇_{p, j + q}` that start with `j`
vertical steps gives `(-1)^{pj} ∇_{p,q}`. -/
theorem mapDomain_dropVertical_filter_shuffleSum (p q j : ℕ) :
    Finsupp.mapDomain (dropVertical j)
        ((shuffleSum (p + (j + q)) p (j + q)).filter (IsVerticalStart j)) =
      (-1 : ℤ) ^ (p * j) • shuffleSum (p + q) p q := by
  induction j with
  | zero =>
    have hf : (shuffleSum (p + (0 + q)) p (0 + q)).filter (IsVerticalStart 0) =
        shuffleSum (p + (0 + q)) p (0 + q) := by
      rw [Finsupp.filter_eq_self_iff]
      intro l hl
      rw [isVerticalStart_zero_iff]
      exact take_one_of_mem_support_shuffleSum (Finsupp.mem_support_iff.2 hl)
    rw [hf, show dropVertical 0 = id from funext dropVertical_zero,
      Finsupp.mapDomain_id]
    simp
  | succ j ih =>
    rw [show p + (j + 1 + q) = p + (j + q) + 1 by omega, show j + 1 + q = j + q + 1 by omega,
      shuffleSum_succ, lowerSnd_succ, Finsupp.filter_add, Finsupp.filter_smul, lmap, lmap,
      Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, filter_mapDomain, filter_mapDomain]
    have h1 : (lowerFst (p + (j + q)) p (j + q + 1)).filter (IsVerticalStart (j + 1) ∘ stepFst)
        = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro l hl
      exact absurd hl (not_isVerticalStart_succ_stepFst j l)
    have h2 : IsVerticalStart (j + 1) ∘ stepSnd = IsVerticalStart j :=
      funext fun l ↦ propext (isVerticalStart_succ_stepSnd_iff j l)
    rw [h1, Finsupp.mapDomain_zero, zero_add]
    simp only [h2]
    rw [Finsupp.mapDomain_smul, ← Finsupp.mapDomain_comp,
      show dropVertical (j + 1) ∘ stepSnd = dropVertical j from
        funext (dropVertical_succ_stepSnd j), ih, smul_smul, ← pow_add]
    congr 1
    ring

end LatticePath

end MMP
