module

public import MMP.AlgebraicTopology.SingularHomology.LocalHomologyHomotopy

/-!
# The corner path of the shuffle sum

The *corner path* of `[p] × [q]` is the lattice path `(0, 0), (1, 0), …, (p, 0), (p, 1), …,
(p, q)`, first along the first factor and then along the second. It occurs in the shuffle sum
`∇_{p,q}` with coefficient `1`, and it is the only path of `∇_{p,q}` through the corner
`(p, 0)`. In the triangulation of a prism `Δᵖ × Δ^q` it is the simplex containing the points
near the vertex `(p, 0)`.

## Main definitions

* `MMP.LatticePath.sndPath`: the path `(0, 0), (0, 1), …, (0, q)`.
* `MMP.LatticePath.cornerPath`: the corner path of `[p] × [q]`.

## Main results

* `MMP.LatticePath.eq_cornerPath_of_mem_support`: a path of `∇_{p,q}` through
  `(p, 0)` is the corner path.
* `MMP.LatticePath.shuffleSum_cornerPath`: the corner path has coefficient `1`.
* `MMP.LatticePath.getD_cornerPath`: the `j`-th vertex of the corner path is
  `(min j p, j - p)`.
-/

@[expose] public section

namespace MMP

namespace LatticePath

/-- The lattice path `(0, 0), (0, 1), …, (0, q)`. -/
def sndPath (q : ℕ) : List (ℕ × ℕ) := (List.range (q + 1)).map fun j ↦ (0, j)

/-- Prepending a first step `y` to `sndPath q` gives `sndPath (q + 1)`. -/
lemma stepSnd_sndPath (q : ℕ) : stepSnd (sndPath q) = sndPath (q + 1) := by
  simp [stepSnd, sndPath, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- The corner path `(0, 0), (1, 0), …, (p, 0), (p, 1), …, (p, q)` of `[p] × [q]`. -/
def cornerPath : ℕ → ℕ → List (ℕ × ℕ)
  | 0, q => sndPath q
  | p + 1, q => stepFst (cornerPath p q)

/-- The corner path of `[0] × [q]` is `sndPath q`. -/
@[simp] lemma cornerPath_zero (q : ℕ) : cornerPath 0 q = sndPath q := rfl

/-- The corner path of `[p + 1] × [q]` is the corner path of `[p] × [q]` with a first step `x`
prepended. -/
@[simp] lemma cornerPath_succ (p q : ℕ) : cornerPath (p + 1) q = stepFst (cornerPath p q) := rfl

/-- The paths of `∇_{0,q}` are the single path `(0, 0), …, (0, q)`. -/
lemma eq_sndPath_of_mem_support {m q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum m 0 q).support) : l = sndPath q := by
  classical
  induction m generalizing q l with
  | zero =>
    simp only [shuffleSum, true_and] at h
    split_ifs at h with hq
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      subst h hq
      rfl
    · simp at h
  | succ m ih =>
    rw [shuffleSum_succ, lowerFst_zero, map_zero, zero_add, pow_zero, one_smul] at h
    rcases q with _ | q
    · simp at h
    · obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      rw [ih hl', stepSnd_sndPath]

/-- **The corner path is the only path through the corner.** A path of `∇_{p,q}` through the
vertex `(p, 0)` is the corner path. -/
theorem eq_cornerPath_of_mem_support {m p q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum m p q).support) (hl : (p, 0) ∈ l) : l = cornerPath p q := by
  classical
  induction m generalizing p q l with
  | zero =>
    simp only [shuffleSum] at h
    split_ifs at h with hpq
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      obtain ⟨rfl, rfl⟩ := hpq
      rw [h]
      rfl
    · simp at h
  | succ m ih =>
    rw [shuffleSum_succ] at h
    rcases Finset.mem_union.1 (Finsupp.support_add h) with h | h
    · rcases p with _ | p
      · simp at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      simp only [stepFst, List.mem_cons, Prod.mk.injEq, List.mem_map] at hl
      rcases hl with ⟨h1, -⟩ | ⟨⟨a, b⟩, hab, h1, h2⟩
      · omega
      · simp only at h1 h2
        have : (p, 0) ∈ l' := by
          obtain rfl : a = p := by omega
          rw [← h2]
          exact hab
        rw [cornerPath_succ, ← ih hl' this]
    · have h := Finsupp.support_smul h
      rcases q with _ | q
      · simp at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      simp only [stepSnd, List.mem_cons, Prod.mk.injEq, List.mem_map] at hl
      rcases hl with ⟨rfl, -⟩ | ⟨⟨a, b⟩, -, -, h2⟩
      · rw [eq_sndPath_of_mem_support hl', stepSnd_sndPath]
        rfl
      · omega

/-- The shuffle sum `∇_{0,q}` is the path `sndPath q` with coefficient `1`. -/
lemma shuffleSum_self_sndPath (q : ℕ) : shuffleSum q 0 q = Finsupp.single (sndPath q) 1 := by
  induction q with
  | zero => simp [shuffleSum, sndPath]
  | succ q ih =>
    rw [shuffleSum_succ, lowerFst_zero, lowerSnd_succ, ih]
    simp [lmap, stepSnd_sndPath]

/-- The corner path has coefficient `1` in the shuffle sum `∇_{p,q}`. -/
theorem shuffleSum_cornerPath (p q : ℕ) : shuffleSum (p + q) p q (cornerPath p q) = 1 := by
  classical
  induction p with
  | zero => simp [shuffleSum_self_sndPath]
  | succ p ih =>
    rw [show p + 1 + q = (p + q) + 1 by omega, shuffleSum_succ, lowerFst_succ, Finsupp.add_apply,
      cornerPath_succ, lmap, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_apply_of_injective (fun l l' h ↦ ?_), ih, Finsupp.smul_apply, lmap,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_notin_range, smul_zero, add_zero]
    · rintro ⟨l', hl'⟩
      have hne : ∃ t, cornerPath p q = (0, 0) :: t := by
        cases p with
        | zero => exact ⟨(List.range q).map fun j ↦ (0, j + 1),
            by simp [sndPath, List.range_succ_eq_map, Function.comp_def]⟩
        | succ p => exact ⟨_, rfl⟩
      obtain ⟨t, hvt⟩ := hne
      rw [hvt] at hl'
      simp only [stepSnd, stepFst, List.map_cons, List.cons.injEq] at hl'
      cases l' with
      | nil => simp at hl'
      | cons w l'' =>
        simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hl'
        omega
    · simp only [stepFst, List.cons.injEq, true_and] at h
      exact List.map_injective_iff.2 (fun a b hab ↦ by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext (by omega) hab.2) h

/-- The corner path of `[p] × [q]` has `p + q + 1` vertices. -/
lemma length_cornerPath (p q : ℕ) : (cornerPath p q).length = p + q + 1 := by
  induction p with
  | zero => simp [sndPath]
  | succ p ih => simp [stepFst, ih]; omega

/-- The `j`-th vertex of the corner path of `[p] × [q]` is `(min j p, j - p)`. -/
theorem getD_cornerPath (p q : ℕ) {j : ℕ} (hj : j < p + q + 1) :
    (cornerPath p q).getD j (0, 0) = (min j p, j - p) := by
  induction p generalizing j with
  | zero =>
    simp only [cornerPath_zero, sndPath, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show j < q + 1 by omega), Option.map_some, Option.getD_some]
    simp
  | succ p ih =>
    rcases j with _ | j
    · simp [stepFst]
    · have hlen : j < (cornerPath p q).length := by rw [length_cornerPath]; omega
      have h := ih (j := j) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at h
      rw [cornerPath_succ, stepFst, List.getD_cons_succ, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some, Option.getD_some, h]
      ext <;> simp <;> omega

end LatticePath

end MMP
