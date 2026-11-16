module

public import MMP.AlgebraicTopology.CapProduct.Basic
public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicTopology.CapProduct.ExteriorProductPaths

/-!
# Cap products with pulled-back cochains and cross products of chains

Let `pr : X × Y → Y` be the projection and `φ` a `j`-cochain on `Y` vanishing on degenerate
simplices. For singular simplices `σ` of `X` and `τ` of `Y`, only the shuffles of `σ × τ` whose
last `j` steps are vertical contribute to `pr^* φ ∩ (σ × τ)` (the cap product evaluates the
cochain on the back face): on the others the back `j`-face projects to a degenerate simplex.
Deleting these last steps loses no sign, so they give `σ × (φ ∩ τ)`. The same holds for locally
finite chains:

`pr^* φ ∩ (w × z) = w × (φ ∩ z)`.

## Main results

* `MMP.LatticePath.mapDomain_take_filter_shuffleSum`: truncating the paths of
  `∇_{p, q + j}` that end with `j` vertical steps gives `∇_{p, q}`.
* `MMP.BorelMooreCap.capChain_cochainPullback_crossChain`: the identity on locally
  finite chains.

## References

* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VII.12.17.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicTopology MMP.LatticePath
  MMP.SingularCross MMP.LocallyFiniteChain
  MMP.BorelMooreCross MMP.SingularCochain
  MMP.SingularChain

universe u

namespace MMP

namespace LatticePath

/-- On a unit path, the second coordinate of the vertices is monotone. -/
lemma IsUnitPath.snd_mono {l : List (ℕ × ℕ)} (hl : IsUnitPath l) {i i' : ℕ} (h : i ≤ i')
    (hi' : i' < l.length) : (l.getD i (0, 0)).2 ≤ (l.getD i' (0, 0)).2 := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ i' hii' ih =>
    refine (ih (by omega)).trans ?_
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi']
    exact (hl.2 i' hi').2

/-- On a unit path, the first coordinate of the vertices is monotone. -/
lemma IsUnitPath.fst_mono {l : List (ℕ × ℕ)} (hl : IsUnitPath l) {i i' : ℕ} (h : i ≤ i')
    (hi' : i' < l.length) : (l.getD i (0, 0)).1 ≤ (l.getD i' (0, 0)).1 := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ i' hii' ih =>
    refine (ih (by omega)).trans ?_
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi']
    exact (hl.2 i' hi').1

/-- On a unit path, if the second coordinates of the vertices `k, …, k + j` are pairwise distinct,
the steps between them are vertical: the first coordinate does not change. -/
lemma IsUnitPath.fst_eq_of_injOn {l : List (ℕ × ℕ)} (hl : IsUnitPath l) {k j : ℕ}
    (hk : j + k < l.length) (hinj : Set.InjOn (fun i ↦ (l.getD (i + k) (0, 0)).2) (Set.Iic j)) :
    (l.getD k (0, 0)).1 = (l.getD (j + k) (0, 0)).1 := by
  have key : ∀ i, i ≤ j → (l.getD k (0, 0)).2 + i ≤ (l.getD (i + k) (0, 0)).2 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have hm := hl.snd_mono (show i + k ≤ i + 1 + k by omega) (show i + 1 + k < l.length by omega)
      have hne : (l.getD (i + k) (0, 0)).2 ≠ (l.getD (i + 1 + k) (0, 0)).2 := fun he ↦
        absurd (hinj (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hi) he) (by omega)
      omega
  have hf := hl.fst_mono (show k ≤ j + k by omega) hk
  have hj := key j le_rfl
  have h1 := hl.1 k (by omega)
  have h2 := hl.1 (j + k) hk
  rw [List.getD_eq_getElem _ _ (show k < l.length by omega), List.getD_eq_getElem _ _ hk] at hf hj ⊢
  omega

/-- Every vertex `(a, b)` of a path of `∇_{p,q}` satisfies `a ≤ p` and `b ≤ q`. -/
lemma getD_le_of_mem_support_shuffleSum {n p q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum n p q).support) {i : ℕ} (hi : i < l.length) :
    (l.getD i (0, 0)).1 ≤ p ∧ (l.getD i (0, 0)).2 ≤ q := by
  rw [List.getD_eq_getElem _ _ hi]
  exact (mem_support_shuffleSum h).2 _ (List.getElem_mem hi)

/-- The last vertex of a path of `∇_{p,n}` is `(p, n)`. -/
lemma getD_end_of_mem_support_shuffleSum {N p n : ℕ} {l : List (ℕ × ℕ)}
    (hl : l ∈ (shuffleSum N p n).support) (hN : N = p + n) : l.getD N (0, 0) = (p, n) := by
  have hu := isUnitPath_of_mem_support_shuffleSum hl
  have hlen := (mem_support_shuffleSum hl).1
  have hb := getD_le_of_mem_support_shuffleSum hl (i := N) (by omega)
  have hs := hu.1 N (by omega)
  rw [List.getD_eq_getElem _ _ (show N < l.length by omega)] at hb ⊢
  exact Prod.ext (by omega) (by omega)

/-- The last `j` steps of the lattice path `l` are vertical: its vertices `j` steps before the
end and at the end have the same first coordinate. -/
def IsVerticalEnd (j : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  (l.getD (l.length - 1 - j) (0, 0)).1 = (l.getD (l.length - 1) (0, 0)).1

/-- Ending with `j` vertical steps is decidable. -/
instance (j : ℕ) : DecidablePred (IsVerticalEnd j) := fun _ ↦
  inferInstanceAs (Decidable (_ = _))

/-- On a path of `∇_{p,n}` ending with `j` vertical steps, the vertex `i + k`, `k + j = N`,
`i ≤ j`, is `(p, n - j + i)`. -/
lemma IsVerticalEnd.getD_eq {N p n j k : ℕ} {l : List (ℕ × ℕ)}
    (hl : l ∈ (shuffleSum N p n).support) (hN : N = p + n) (hk : k + j = N)
    (h : IsVerticalEnd j l) {i : ℕ} (hi : i ≤ j) : l.getD (i + k) (0, 0) = (p, n - j + i) := by
  have hu := isUnitPath_of_mem_support_shuffleSum hl
  have hlen := (mem_support_shuffleSum hl).1
  have hend := getD_end_of_mem_support_shuffleSum hl hN
  unfold IsVerticalEnd at h
  rw [show l.length - 1 - j = k by omega, show l.length - 1 = N by omega, hend] at h
  have hm := hu.fst_mono (show k ≤ i + k by omega) (show i + k < l.length by omega)
  have hb := getD_le_of_mem_support_shuffleSum hl (i := i + k) (by omega)
  have hs := hu.1 (i + k) (by omega)
  have hs0 := hu.1 k (by omega)
  rw [List.getD_eq_getElem _ _ (show k < l.length by omega)] at h
  rw [List.getD_eq_getElem _ _ (show k < l.length by omega),
    List.getD_eq_getElem _ _ (show i + k < l.length by omega)] at hm
  rw [List.getD_eq_getElem _ _ (show i + k < l.length by omega)] at hb ⊢
  simp only at h
  exact Prod.ext (by simp only; omega) (by simp only; omega)

/-- A path of `∇_{p,n}` ending with `j ≤ N` vertical steps has `j ≤ n`. -/
lemma IsVerticalEnd.le {N p n j : ℕ} {l : List (ℕ × ℕ)} (hl : l ∈ (shuffleSum N p n).support)
    (hN : N = p + n) (hjN : j ≤ N) (h : IsVerticalEnd j l) : j ≤ n := by
  have hu := isUnitPath_of_mem_support_shuffleSum hl
  have hlen := (mem_support_shuffleSum hl).1
  have e := h.getD_eq hl hN (k := N - j) (by omega) (i := 0) (Nat.zero_le _)
  have hs := hu.1 (0 + (N - j)) (by omega)
  rw [List.getD_eq_getElem _ _ (show 0 + (N - j) < l.length by omega)] at e
  rw [e] at hs
  simp only at hs
  omega

/-- A path of `∇_{p,n}` whose last `j + 1` vertices have pairwise distinct second coordinates
ends with `j` vertical steps. -/
lemma isVerticalEnd_of_injOn {N p n j k : ℕ} {l : List (ℕ × ℕ)}
    (hl : l ∈ (shuffleSum N p n).support) (hk : k + j = N)
    (hinj : Set.InjOn (fun i ↦ (l.getD (i + k) (0, 0)).2) (Set.Iic j)) :
    IsVerticalEnd j l := by
  have hu := isUnitPath_of_mem_support_shuffleSum hl
  have hlen := (mem_support_shuffleSum hl).1
  unfold IsVerticalEnd
  rw [show l.length - 1 - j = k by omega, show l.length - 1 = j + k by omega]
  exact hu.fst_eq_of_injOn (by omega) hinj

/-- The vertex `i + 1` of `stepFst l` is the vertex `i` of `l` moved one step horizontally. -/
lemma getD_stepFst_succ (l : List (ℕ × ℕ)) {i : ℕ} (hi : i < l.length) :
    (stepFst l).getD (i + 1) (0, 0) = ((l.getD i (0, 0)).1 + 1, (l.getD i (0, 0)).2) := by
  rw [List.getD_eq_getElem _ _ (by simp [stepFst]; omega), List.getD_eq_getElem _ _ hi]
  simp [stepFst]

/-- The vertex `i + 1` of `stepSnd l` is the vertex `i` of `l` moved one step vertically. -/
lemma getD_stepSnd_succ (l : List (ℕ × ℕ)) {i : ℕ} (hi : i < l.length) :
    (stepSnd l).getD (i + 1) (0, 0) = ((l.getD i (0, 0)).1, (l.getD i (0, 0)).2 + 1) := by
  rw [List.getD_eq_getElem _ _ (by simp [stepSnd]; omega), List.getD_eq_getElem _ _ hi]
  simp [stepSnd]

/-- For `j + 1 ≤ l.length`, `stepFst l` ends with `j` vertical steps if and only if `l` does. -/
lemma isVerticalEnd_stepFst_iff {j : ℕ} {l : List (ℕ × ℕ)} (hj : j + 1 ≤ l.length) :
    IsVerticalEnd j (stepFst l) ↔ IsVerticalEnd j l := by
  unfold IsVerticalEnd
  have hlen : (stepFst l).length = l.length + 1 := by simp [stepFst]
  rw [hlen, show l.length + 1 - 1 - j = (l.length - 1 - j) + 1 by omega,
    show l.length + 1 - 1 = (l.length - 1) + 1 by omega, getD_stepFst_succ _ (by omega),
    getD_stepFst_succ _ (by omega)]
  exact ⟨fun h ↦ by simp only at h; omega, fun h ↦ by simp only; omega⟩

/-- For `j + 1 ≤ l.length`, `stepSnd l` ends with `j` vertical steps if and only if `l` does. -/
lemma isVerticalEnd_stepSnd_iff {j : ℕ} {l : List (ℕ × ℕ)} (hj : j + 1 ≤ l.length) :
    IsVerticalEnd j (stepSnd l) ↔ IsVerticalEnd j l := by
  unfold IsVerticalEnd
  have hlen : (stepSnd l).length = l.length + 1 := by simp [stepSnd]
  rw [hlen, show l.length + 1 - 1 - j = (l.length - 1 - j) + 1 by omega,
    show l.length + 1 - 1 = (l.length - 1) + 1 by omega, getD_stepSnd_succ _ (by omega),
    getD_stepSnd_succ _ (by omega)]

/-- The first `k + 1` vertices of `stepFst l` are `stepFst` of the first `k` vertices of `l`. -/
lemma take_succ_stepFst (k : ℕ) (l : List (ℕ × ℕ)) :
    (stepFst l).take (k + 1) = stepFst (l.take k) := by
  simp [stepFst, List.map_take]

/-- The first `k + 1` vertices of `stepSnd l` are `stepSnd` of the first `k` vertices of `l`. -/
lemma take_succ_stepSnd (k : ℕ) (l : List (ℕ × ℕ)) :
    (stepSnd l).take (k + 1) = stepSnd (l.take k) := by
  simp [stepSnd, List.map_take]

/-- After `stepSnd`, a path of `∇_{p + 1, j}` does not end with `j + 1` vertical steps. -/
lemma not_isVerticalEnd_succ_stepSnd {N p j : ℕ} {l : List (ℕ × ℕ)}
    (hl : l ∈ (shuffleSum N (p + 1) j).support) (hN : N = p + 1 + j) :
    ¬ IsVerticalEnd (j + 1) (stepSnd l) := by
  intro h
  have hu := isUnitPath_of_mem_support_shuffleSum hl
  have hlen := (mem_support_shuffleSum hl).1
  have hend := getD_end_of_mem_support_shuffleSum hl hN
  have hsum := hu.1 p (by omega)
  unfold IsVerticalEnd at h
  rw [show (stepSnd l).length = l.length + 1 by simp [stepSnd],
    show l.length + 1 - 1 - (j + 1) = p + 1 by omega, show l.length + 1 - 1 = N + 1 by omega,
    getD_stepSnd_succ _ (by omega), getD_stepSnd_succ _ (by omega), hend,
    List.getD_eq_getElem _ _ (by omega)] at h
  simp only at h
  omega

/-- `∇_{0,n}` is the vertical path. -/
lemma shuffleSum_zero_self (n : ℕ) :
    shuffleSum n 0 n = Finsupp.single ((List.range (n + 1)).map fun i ↦ ((0 : ℕ), i)) 1 := by
  induction n with
  | zero => simp [shuffleSum]
  | succ n ih =>
    rw [shuffleSum_succ, lowerFst_zero, lowerSnd_succ, ih]
    simp only [lmap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_zero, Finsupp.mapDomain_single,
      zero_add, pow_zero, one_smul]
    congr 1
    rw [List.range_succ_eq_map (n := n + 1)]
    simp [stepSnd, List.map_map, Function.comp_def]

/-- `x.filter P = x.filter Q` when `P` and `Q` agree on the support of `x`. -/
lemma _root_.Finsupp.filter_congr_of_mem_support {α M : Type*} [Zero M] {P Q : α → Prop}
    [DecidablePred P] [DecidablePred Q] (x : α →₀ M) (h : ∀ a ∈ x.support, (P a ↔ Q a)) :
    x.filter P = x.filter Q := by
  ext a
  by_cases ha : a ∈ x.support <;> simp_all [Finsupp.filter_apply]

/-- Truncating the paths of `∇_{p, q + j}` that end with `j` vertical steps after their first
`p + q + 1` vertices gives `∇_{p,q}`, without a sign. -/
theorem mapDomain_take_filter_shuffleSum (j n p q : ℕ) (hpq : p + q = n) :
    Finsupp.mapDomain (List.take (n + 1))
        ((shuffleSum (n + j) p (q + j)).filter (IsVerticalEnd j)) = shuffleSum n p q := by
  induction n generalizing p q with
  | zero =>
    obtain rfl : p = 0 := by omega
    obtain rfl : q = 0 := by omega
    have hv : IsVerticalEnd j ((List.range (j + 1)).map fun i ↦ ((0 : ℕ), i)) := by
      unfold IsVerticalEnd
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    rw [zero_add, zero_add, shuffleSum_zero_self, Finsupp.filter_single_of_pos _ hv,
      Finsupp.mapDomain_single]
    simp [shuffleSum, List.range_succ_eq_map]
  | succ n ih =>
    rw [show n + 1 + j = n + j + 1 by omega, shuffleSum_succ (n + j) p (q + j),
      shuffleSum_succ n p q]
    simp only [lmap, Finsupp.lmapDomain_apply, Finsupp.filter_add, Finsupp.filter_smul,
      Finsupp.filter_mapDomain, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
      ← Finsupp.mapDomain_comp]
    congr 1
    · rcases p with _ | p
      · rw [lowerFst_zero, Finsupp.filter_zero, Finsupp.mapDomain_zero, lowerFst_zero,
          Finsupp.mapDomain_zero]
      · rw [lowerFst_succ, lowerFst_succ, Finsupp.filter_congr_of_mem_support
          (P := IsVerticalEnd j ∘ stepFst) (Q := IsVerticalEnd j) (shuffleSum (n + j) p (q + j))
          (fun l hl ↦ isVerticalEnd_stepFst_iff (by have := (mem_support_shuffleSum hl).1; omega)),
          show (List.take (n + 1 + 1) ∘ stepFst) = stepFst ∘ List.take (n + 1) from
            funext (take_succ_stepFst (n + 1)), Finsupp.mapDomain_comp, ih p q (by omega)]
    · congr 1
      rcases q with _ | q
      · rw [lowerSnd_zero, Finsupp.mapDomain_zero]
        rcases j with _ | j
        · rw [lowerSnd_zero, Finsupp.filter_zero, Finsupp.mapDomain_zero]
        · obtain rfl : p = n + 1 := by omega
          rw [show 0 + (j + 1) = j + 1 by omega, lowerSnd_succ,
            (Finsupp.filter_eq_zero_iff _ _).2, Finsupp.mapDomain_zero]
          exact fun l hl ↦ Classical.byContradiction fun h0 ↦
            not_isVerticalEnd_succ_stepSnd (Finsupp.mem_support_iff.2 h0) (by omega) hl
      · rw [lowerSnd_succ, show q + 1 + j = q + j + 1 by omega, lowerSnd_succ,
          Finsupp.filter_congr_of_mem_support (P := IsVerticalEnd j ∘ stepSnd)
          (Q := IsVerticalEnd j) (shuffleSum (n + j) p (q + j))
          (fun l hl ↦ isVerticalEnd_stepSnd_iff (by have := (mem_support_shuffleSum hl).1; omega)),
          show (List.take (n + 1 + 1) ∘ stepSnd) = stepSnd ∘ List.take (n + 1) from
            funext (take_succ_stepSnd (n + 1)), Finsupp.mapDomain_comp, ih p q (by omega)]

/-- `mapDomain_take_filter_shuffleSum` in the degrees of the cap product. -/
lemma mapDomain_take_filter_shuffleSum' (p q j : ℕ) :
    Finsupp.mapDomain (List.take (p + q + 1))
        ((shuffleSum (p + (j + q)) p (j + q)).filter (IsVerticalEnd j)) =
      shuffleSum (p + q) p q := by
  have := mapDomain_take_filter_shuffleSum j (p + q) p q rfl
  rwa [show p + q + j = p + (j + q) by omega, show q + j = j + q by omega] at this

/-- For `i < m`, the entry `i` of `l.take m` is the entry `i` of `l`. -/
lemma _root_.List.getD_take_of_lt {α : Type*} {l : List α} {d : α} {m i : ℕ} (hi : i < m) :
    (l.take m).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, hi]

end LatticePath

namespace BorelMooreCap

variable {R : Type u} [CommRing R] {X Y : TopCat.{u}}

/-- The projection `X × Y → Y`. -/
abbrev prSnd (X Y : TopCat.{u}) : TopCat.of (X × Y) ⟶ Y := TopCat.ofHom ContinuousMap.snd

/-- A face of a path simplex, projected to `Y`: `τ` composed with the vertex map of the second
coordinates. -/
lemma prSnd_comp_pathSimplex_comp (N n j : ℕ) (f : Fin (j + 1) → Fin (N + 1)) {p : ℕ}
    (σ : Simp X p) (τ : Simp Y n) (l : List (ℕ × ℕ)) :
    (prSnd X Y).hom.comp ((simplexEquiv _ N (pathSimplex N σ τ l)).comp (smap f)) =
      (simplexEquiv Y n τ).comp (smap (vtx N n (fun i ↦ (l.getD i (0, 0)).2) ∘ f)) := by
  rw [← comp_smap_comp]
  ext t
  change (toC (pathSimplex N σ τ l) (SingularChain.stdSimplexHomeo _ (smap f t))).2 =
    toC τ (SingularChain.stdSimplexHomeo _ (stdSimplex.map (vtx N n fun i ↦ (l.getD i (0, 0)).2) (smap f t)))
  rw [toC_pathSimplex, SingularChain.stdSimplexHomeo_map]
  rfl

/-- The weight of `pr^* φ` on the back `j`-face vanishes on the path simplices of shuffles not
ending with `j` vertical steps, for `φ` vanishing on degenerate simplices. -/
lemma wt_cochainPullback_pathSimplex_eq_zero {p n j k N : ℕ} (hk : k + j = N)
    (φ : Simplex Y j → R)
    (hφ : ∀ (m : ℕ) (s : Simplex Y m) (f : Fin (j + 1) → Fin (m + 1)), Monotone f →
      ¬ Function.Injective f → φ (s.comp (smap f)) = 0)
    (σ : Simp X p) (τ : Simp Y n) {l : List (ℕ × ℕ)} (hl : l ∈ (shuffleSum N p n).support)
    (hgood : ¬ IsVerticalEnd j l) :
    wt (cochainPullback R (prSnd X Y) j φ) (back j N k (by omega)) (pathSimplex N σ τ l) = 0 := by
  have hu := isUnitPath_of_mem_support_shuffleSum hl
  have hlen := (mem_support_shuffleSum hl).1
  change φ ((prSnd X Y).hom.comp _) = _
  rw [prSnd_comp_pathSimplex_comp]
  refine hφ _ _ _ (fun i i' hii' ↦ ?_) (fun hinj ↦ hgood ?_)
  · have hii : (i : ℕ) ≤ i' := hii'
    simp only [Function.comp_apply, vtx, back, Fin.mk_le_mk]
    exact min_le_min_right _ (hu.snd_mono (show (i : ℕ) + k ≤ i' + k by omega) (by omega))
  · refine isVerticalEnd_of_injOn hl hk fun i hi i' hi' he ↦ ?_
    rw [Set.mem_Iic] at hi hi'
    replace he : (l.getD (i + k) (0, 0)).2 = (l.getD (i' + k) (0, 0)).2 := he
    have := @hinj ⟨i, by omega⟩ ⟨i', by omega⟩ (by
      simp only [Function.comp_apply, vtx, back, he])
    simpa using this

/-- The weight `pr^* φ (back face)` on a path simplex of a shuffle: `φ (τ ⌊ [q, …, j + q])` if
the path ends with `j` vertical steps, and `0` otherwise, for `φ` vanishing on degenerate
simplices. -/
lemma wt_cochainPullback_pathSimplex (p q j : ℕ) (φ : Simplex Y j → R)
    (hφ : ∀ (m : ℕ) (s : Simplex Y m) (f : Fin (j + 1) → Fin (m + 1)), Monotone f →
      ¬ Function.Injective f → φ (s.comp (smap f)) = 0)
    (σ : Simp X p) (τ : Simp Y (j + q)) {l : List (ℕ × ℕ)}
    (hl : l ∈ (shuffleSum (p + (j + q)) p (j + q)).support) :
    wt (cochainPullback R (prSnd X Y) j φ) (back j (p + (j + q)) (p + q) (by omega))
        (pathSimplex (p + (j + q)) σ τ l) =
      if IsVerticalEnd j l then wt φ (back j (j + q) q (by omega)) τ else 0 := by
  split_ifs with hgood
  · change φ ((prSnd X Y).hom.comp _) = φ _
    rw [prSnd_comp_pathSimplex_comp]
    congr 3
    funext i
    ext
    have e := hgood.getD_eq hl rfl (k := p + q) (by omega) (i := (i : ℕ)) (by omega)
    simp only [Function.comp_apply, vtx, back_val, e]
    omega
  · exact wt_cochainPullback_pathSimplex_eq_zero (by omega) φ hφ σ τ hl hgood

/-- The front `(p + q)`-face of a path simplex of a shuffle ending with `j` vertical steps is the
path simplex of `σ` and the front face of `τ` along the path with these steps deleted. -/
lemma opS_front_pathSimplex (p q j : ℕ) (σ : Simp X p) (τ : Simp Y (j + q)) {l : List (ℕ × ℕ)}
    (hl : l ∈ (shuffleSum (p + (j + q)) p (j + q)).support) (hgood : IsVerticalEnd j l) :
    opS (front (p + q) (p + (j + q)) (by omega)) (pathSimplex (p + (j + q)) σ τ l) =
      pathSimplex (p + q) σ (opS (front q (j + q) (by omega)) τ) (l.take (p + q + 1)) := by
  have hu := isUnitPath_of_mem_support_shuffleSum hl
  have hlen := (mem_support_shuffleSum hl).1
  have hA : (vtxMap (p + (j + q)) p fun i ↦ (l.getD i (0, 0)).1).comp
      ⟨Convexity.StdSimplex.map (front (p + q) (p + (j + q)) (by omega)), Convexity.StdSimplex.continuous_map ℝ _⟩ =
        vtxMap (p + q) p fun i ↦ ((l.take (p + q + 1)).getD i (0, 0)).1 := by
    ext1 t
    change Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ t) = Convexity.StdSimplex.map _ t
    rw [Convexity.StdSimplex.map_map]
    congr 1
    funext i
    ext
    have hi := i.isLt
    simp only [Function.comp_apply, vtx, front_val]
    rw [List.getD_take_of_lt (by omega)]
  have hq : (l.getD (p + q) (0, 0)).2 = q := by
    have e := hgood.getD_eq hl rfl (k := p + q) (by omega) (i := 0) (Nat.zero_le _)
    rw [zero_add] at e
    rw [e]
    simp only
    omega
  have hB : (vtxMap (p + (j + q)) (j + q) fun i ↦ (l.getD i (0, 0)).2).comp
      ⟨Convexity.StdSimplex.map (front (p + q) (p + (j + q)) (by omega)), Convexity.StdSimplex.continuous_map ℝ _⟩ =
        (⟨Convexity.StdSimplex.map (front q (j + q) (by omega)), Convexity.StdSimplex.continuous_map ℝ _⟩ :
          C(Convexity.StdSimplex ℝ (Fin (q + 1)), Convexity.StdSimplex ℝ (Fin (j + q + 1)))).comp
          (vtxMap (p + q) q fun i ↦ ((l.take (p + q + 1)).getD i (0, 0)).2) := by
    ext1 t
    change Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ t) = Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ t)
    rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
    congr 1
    funext i
    ext
    have hi := i.isLt
    have h1 := hu.snd_mono (show (i : ℕ) ≤ p + q by omega) (by omega)
    simp only [Function.comp_apply, vtx, front_val]
    rw [List.getD_take_of_lt (by omega)]
    omega
  apply toC_injective
  rw [toC_opS, toC_pathSimplex, toC_pathSimplex, toC_opS]
  ext t : 1
  exact Prod.ext (congrArg (toC σ) (DFunLike.congr_fun hA t))
    (congrArg (toC τ) (DFunLike.congr_fun hB t))

/-- The shuffles of `σ × τ` ending with `j` vertical steps. -/
def crossSimplexVerticalEnd (p q j : ℕ) (σ : Simp X p) (τ : Simp Y (j + q)) :
    Simp (TopCat.of (X × Y)) (p + (j + q)) →₀ ℤ :=
  Finsupp.mapDomain (pathSimplex (p + (j + q)) σ τ)
    ((shuffleSum (p + (j + q)) p (j + q)).filter (IsVerticalEnd j))

/-- The front faces of the vertical-end shuffles of `σ × τ` form `σ × (τ ⌊ [0, …, q])`. -/
lemma mapDomain_opS_front_crossSimplexVerticalEnd (p q j : ℕ) (σ : Simp X p)
    (τ : Simp Y (j + q)) :
    Finsupp.mapDomain (opS (front (p + q) (p + (j + q)) (by omega)))
        (crossSimplexVerticalEnd p q j σ τ) =
      crossSimplex (p + q) σ (opS (front q (j + q) (by omega)) τ) := by
  rw [crossSimplexVerticalEnd, ← Finsupp.mapDomain_comp,
    Finsupp.mapDomain_congr (g := pathSimplex (p + q) σ (opS (front q (j + q) (by omega)) τ) ∘
      List.take (p + q + 1)) fun l hl ↦ by
        rw [Finsupp.support_filter, Finset.mem_filter] at hl
        exact opS_front_pathSimplex p q j σ τ hl.1 hl.2,
    Finsupp.mapDomain_comp, mapDomain_take_filter_shuffleSum']
  rfl

/-- Multiplying `σ × τ` by the weight of `pr^* φ` keeps the vertical-end shuffles, with weight
`φ (τ ⌊ [q, …, j + q])`. -/
lemma wt_cochainPullback_mul_crossSimplex (p q j : ℕ) (φ : Simplex Y j → R)
    (hφ : ∀ (m : ℕ) (s : Simplex Y m) (f : Fin (j + 1) → Fin (m + 1)), Monotone f →
      ¬ Function.Injective f → φ (s.comp (smap f)) = 0)
    (σ : Simp X p) (τ : Simp Y (j + q)) (ρ : Simp (TopCat.of (X × Y)) (p + (j + q))) :
    wt (cochainPullback R (prSnd X Y) j φ) (back j (p + (j + q)) (p + q) (by omega)) ρ *
        ((crossSimplex (p + (j + q)) σ τ ρ : ℤ) : R) =
      wt φ (back j (j + q) q (by omega)) τ * ((crossSimplexVerticalEnd p q j σ τ ρ : ℤ) : R) := by
  classical
  rw [crossSimplex, crossSimplexVerticalEnd, mapDomain_apply_eq_sum,
    mapDomain_apply_eq_sum' _ _ _ (shuffleSum (p + (j + q)) p (j + q)).support
      (by rw [Finsupp.support_filter]; exact Finset.filter_subset _ _)]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  split_ifs with h
  · subst h
    rw [wt_cochainPullback_pathSimplex p q j φ hφ σ τ hl, Finsupp.filter_apply]
    split_ifs <;> simp
  · simp

/-- The family `crossSimplexVerticalEnd p q j σ τ` is carrier-decreasing for the carrier
`carP X Y p (j + q)`: every simplex in its support has image in the carrier of `(σ, τ)`. -/
lemma isCarrierDecreasing_crossSimplexVerticalEnd (p q j : ℕ) :
    IsCarrierDecreasing (carP X Y p (j + q))
      (singularSimplexImage (TopCat.of (X × Y)) (n := op ⦋p + (j + q)⦌))
      (fun st ↦ crossSimplexVerticalEnd p q j st.1 st.2) := by
  intro st ρ hρ
  classical
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.1
    (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hρ))
  rintro _ ⟨t, rfl⟩
  change toC (pathSimplex _ st.1 st.2 l) t ∈ _
  rw [toC_pathSimplex]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

variable (R) in
/-- **Cap product with a pulled-back cochain and cross product of chains.** For a `j`-cochain
`φ` of `Y` vanishing on degenerate simplices, a locally finite `p`-chain `w` of `X` and a locally
finite `(j + q)`-chain `z` of `Y`: `pr^* φ ∩ (w × z) = w × (φ ∩ z)`. -/
theorem capChain_cochainPullback_crossChain (p q j : ℕ) (φ : Simplex Y j → R)
    (hφ : ∀ (m : ℕ) (s : Simplex Y m) (f : Fin (j + 1) → Fin (m + 1)), Monotone f →
      ¬ Function.Injective f → φ (s.comp (smap f)) = 0)
    (w : (BM R X).X p) (z : (BM R Y).X (j + q)) :
    capChain R j (p + q) (p + (j + q)) (by omega) (cochainPullback R (prSnd X Y) j φ)
        (crossChain R (p + (j + q)) p (j + q) w z) =
      crossChain R (p + q) p q w (capChain R j q (j + q) rfl φ z) := by
  apply coeff_injective R
  rw [capChain_apply, capChain_apply, coeff_pf, coeff_W, coeff_crossChain,
    coeff_crossChain, coeff_pf, coeff_W]
  set g := wt (cochainPullback R (prSnd X Y) j φ) (back j (p + (j + q)) (p + q) (by omega))
  set g' := wt φ (back j (j + q) q (by omega))
  set c' := lfTensor (coeff R w) (fun τ ↦ g' τ * coeff R z τ) with hc'_def
  have hc : lfTensor (coeff R w) (coeff R z) ∈ lfChains R R (carP X Y p (j + q)) :=
    lfTensor_mem (coeff_mem R w) (coeff_mem R z)
  have hc' : c' ∈ lfChains R R (carP X Y p (j + q)) :=
    lfTensor_mem (coeff_mem R w) (coeff_mem R (W R g' z))
  have step1 : (fun ρ ↦ g ρ * crossFun (p + (j + q)) p (j + q) (coeff R w) (coeff R z) ρ) =
      lfTransferFun (fun st ↦ crossSimplexVerticalEnd p q j st.1 st.2) c' := by
    funext ρ
    have hfin := hc.finite_inter_compact (isCompact_singularSimplexImage ρ)
    obtain ⟨x, hx⟩ := nonempty_singularSimplexImage ρ
    have hF : ∀ st, lfTensor (coeff R w) (coeff R z) st ≠ 0 →
        crossFamily (p + (j + q)) p (j + q) st ρ ≠ 0 → st ∈ hfin.toFinset := fun st h h' ↦ by
      rw [Set.Finite.mem_toFinset]
      exact ⟨h, x, isCarrierDecreasing_crossFamily _ _ _ st ρ h' hx, hx⟩
    have hF' : ∀ st, c' st ≠ 0 → crossSimplexVerticalEnd p q j st.1 st.2 ρ ≠ 0 →
        st ∈ hfin.toFinset := fun st h h' ↦ by
      rw [Set.Finite.mem_toFinset]
      refine ⟨fun h0 ↦ h ?_, x, isCarrierDecreasing_crossSimplexVerticalEnd p q j st ρ h' hx, hx⟩
      simp only [hc'_def, lfTensor] at h0 ⊢
      linear_combination g' st.2 * h0
    rw [crossFun, lfTransferFun_eq_sum _ _ ρ _ hF, lfTransferFun_eq_sum _ _ ρ _ hF',
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun st _ ↦ ?_
    have := wt_cochainPullback_mul_crossSimplex p q j φ hφ st.1 st.2 ρ
    simp only [hc'_def, lfTensor, crossFamily]
    linear_combination (coeff R w st.1 * coeff R z st.2) * this
  have step2 := pushforwardFun_lfTransferFun hc'
    (isCarrierDecreasing_crossSimplexVerticalEnd p q j)
    (opS (front (p + q) (p + (j + q)) (by omega))) (fun t ↦ image_opS_subset _ t)
    compact_nonempty
  rw [step1, step2]
  simp_rw [mapDomain_opS_front_crossSimplexVerticalEnd]
  change _ = lfTransferFun (crossFamily (p + q) p q) (lfTensor (coeff R w) (pushforwardFun
    (opS (front q (j + q) (by omega))) fun τ ↦ g' τ * coeff R z τ))
  have hd : (fun τ ↦ g' τ * coeff R z τ) ∈
      lfChains R R (singularSimplexImage Y (n := op ⦋j + q⦌)) := coeff_mem R (W R g' z)
  rw [← pushforwardFun_prodMap_id_lfTensor' (coeff R w) hd
      (opS (front q (j + q) (by omega))) (fun τ ↦ image_opS_subset _ τ) compact_nonempty,
    lfTransferFun_pushforwardFun hc' (Prod.map id (opS (front q (j + q) (by omega))))
      (fun st ↦ Set.prod_mono subset_rfl (image_opS_subset _ _))
      (isCarrierDecreasing_crossFamily (p + q) p q) compact_nonempty]
  rfl

variable (R) in
/-- `pr^* φ ∩ (w × z) = 0` if `deg z < deg φ`, for `φ` vanishing on degenerate simplices. -/
theorem capChain_cochainPullback_crossChain_eq_zero_of_lt (p n j r : ℕ) (h : j + r = p + n)
    (hn : n < j) (φ : Simplex Y j → R)
    (hφ : ∀ (m : ℕ) (s : Simplex Y m) (f : Fin (j + 1) → Fin (m + 1)), Monotone f →
      ¬ Function.Injective f → φ (s.comp (smap f)) = 0)
    (w : (BM R X).X p) (z : (BM R Y).X n) :
    capChain R j r (p + n) h (cochainPullback R (prSnd X Y) j φ)
      (crossChain R (p + n) p n w z) = 0 := by
  rw [capChain_apply]
  suffices hW : W R (wt (cochainPullback R (prSnd X Y) j φ) (back j (p + n) r (by omega)))
      (crossChain R (p + n) p n w z) = 0 by rw [hW, map_zero]
  apply coeff_injective R
  funext ρ
  rw [coeff_W, coeff_crossChain, coeff_zero]
  change _ * _ = 0
  by_cases hρ : crossFun (p + n) p n (coeff R w) (coeff R z) ρ = 0
  · rw [hρ, mul_zero]
  obtain ⟨st, hst⟩ : ∃ st, lfTensor (coeff R w) (coeff R z) st *
      ((crossFamily (p + n) p n st ρ : ℤ) : R) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hρ (finsum_eq_zero_of_forall_eq_zero hc)
  have hΨ : crossSimplex (p + n) st.1 st.2 ρ ≠ 0 := fun h0 ↦ hst (by
    change _ * ((crossSimplex (p + n) st.1 st.2 ρ : ℤ) : R) = 0
    rw [h0, Int.cast_zero, mul_zero])
  classical
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1
    (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hΨ))
  rw [wt_cochainPullback_pathSimplex_eq_zero (by omega) φ hφ st.1 st.2 hl
    (fun hv ↦ absurd (hv.le hl rfl (by omega)) (by omega)), zero_mul]

end BorelMooreCap

end MMP
