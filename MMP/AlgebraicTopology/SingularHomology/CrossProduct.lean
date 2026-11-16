module

public import MMP.AlgebraicTopology.SingularHomology.ShuffleProduct
public import MMP.AlgebraicTopology.BorelMoore.Basic
public import Mathlib.Data.List.GetD

/-!
# Product simplices of a lattice path

For singular simplices `σ : Δᵖ → X`, `τ : Δ^q → Y` and a lattice path `l` with vertices
`(a_j, b_j)`, `j = 0, …, n`, the *path simplex* is the singular `n`-simplex of `X × Y`
`t ↦ (σ(A t), τ(B t))`, where `A : Δⁿ → Δᵖ` and `B : Δⁿ → Δ^q` are the affine maps sending the
`j`-th vertex to the vertices `a_j` and `b_j`. Deleting a vertex of the path is taking a face of
the path simplex, and relabelling the first coordinates along `δ_k` is replacing `σ` by its face
`σ ∘ δ_k`. The *cross product* `σ × τ` of singular simplices is the image of the shuffle sum
`MMP.LatticePath.shuffleSum`, and the Leibniz rule for lattice paths becomes
`∂(σ × τ) = ∂σ × τ + (-1)^p σ × ∂τ`.

## Main definitions

* `MMP.SingularCross.pathSimplex`: the path simplex.
* `MMP.SingularCross.crossSimplex`: `σ × τ`, a finite integral chain on `X × Y`.

## Main results

* `MMP.SingularCross.singularSimplexImage_subset_of_mem_support`: the simplices of
  `σ × τ` have image in `σ(Δᵖ) × τ(Δ^q)`.

## References

* [S. Eilenberg, S. MacLane, *On the groups H(Π, n), I*][eilenbergmaclane1953], §5.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VI.12.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial Finsupp MMP.LatticePath Convexity

universe u

namespace MMP

namespace SingularCross

/-- The vertex map `Fin (n + 1) → Fin (p + 1)` of a coordinate sequence `f`, clamped to `p`. -/
def vtx (n p : ℕ) (f : ℕ → ℕ) : Fin (n + 1) → Fin (p + 1) :=
  fun j ↦ ⟨min (f j) p, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The affine map `Δⁿ → Δᵖ` with vertex map `vtx n p f`. -/
def vtxMap (n p : ℕ) (f : ℕ → ℕ) : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (p + 1))) :=
  ⟨StdSimplex.map (vtx n p f), StdSimplex.continuous_map ℝ _⟩

/-- The face inclusion `Δⁿ → Δⁿ⁺¹` opposite the `i`-th vertex. -/
def faceMap (n : ℕ) (i : Fin (n + 2)) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 2))) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

/-- Precomposing `vtxMap (n + 1) p f` with the face inclusion `faceMap n i` gives `vtxMap n p g`
when `g` is `f` restricted along `i.succAbove`. -/
lemma vtxMap_comp_faceMap (n p : ℕ) (f g : ℕ → ℕ) (i : Fin (n + 2))
    (h : ∀ j : Fin (n + 1), f (i.succAbove j) = g j) :
    (vtxMap (n + 1) p f).comp (faceMap n i) = vtxMap n p g := by
  ext1 t
  change StdSimplex.map _ (StdSimplex.map _ t) = StdSimplex.map _ t
  rw [← StdSimplex.map_comp]
  congr 1
  funext j
  simp [vtx, h]

/-- Postcomposing `vtxMap n p f` with the face inclusion `faceMap p k` gives `vtxMap n (p + 1) g`
when `f` takes values at most `p` and `g` is `skip k ∘ f`. -/
lemma faceMap_comp_vtxMap (n p : ℕ) (f g : ℕ → ℕ) (k : Fin (p + 2))
    (hf : ∀ j : Fin (n + 1), f j ≤ p) (h : ∀ j : Fin (n + 1), g j = skip k (f j)) :
    (faceMap p k).comp (vtxMap n p f) = vtxMap n (p + 1) g := by
  ext1 t
  change StdSimplex.map _ (StdSimplex.map _ t) = StdSimplex.map _ t
  rw [← StdSimplex.map_comp]
  congr 1
  funext j
  have hk := k.isLt
  have hj := hf j
  ext
  simp only [Function.comp_apply, vtx, h, skip, Fin.succAbove, Fin.lt_def, Fin.coe_castSucc,
    Fin.val_succ]
  split_ifs <;> simp_all <;> omega

variable {X Y : TopCat.{u}}

/-- The singular `n`-simplices of `X`. -/
abbrev Simp (X : TopCat.{u}) (n : ℕ) := (TopCat.toSSet.obj X).obj (op ⦋n⦌)

/-- A singular simplex as a continuous map. -/
abbrev toC {n : ℕ} (σ : Simp X n) : C(StdSimplex ℝ (Fin (n + 1)), X) :=
  X.toSSetObjEquiv (op ⦋n⦌) σ

/-- The path simplex of `σ`, `τ` along the lattice path `l`, a singular `n`-simplex of
`X × Y`. -/
def pathSimplex (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q) (l : List (ℕ × ℕ)) :
    Simp (TopCat.of (X × Y)) n :=
  (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (op ⦋n⦌)).symm
    (((toC σ).comp (vtxMap n p fun j ↦ (l.getD j (0, 0)).1)).prodMk
      ((toC τ).comp (vtxMap n q fun j ↦ (l.getD j (0, 0)).2)))

/-- The continuous map of the path simplex is `t ↦ (σ(A t), τ(B t))`. -/
lemma toC_pathSimplex (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q) (l : List (ℕ × ℕ)) :
    toC (pathSimplex n σ τ l) = ((toC σ).comp (vtxMap n p fun j ↦ (l.getD j (0, 0)).1)).prodMk
      ((toC τ).comp (vtxMap n q fun j ↦ (l.getD j (0, 0)).2)) :=
  Equiv.apply_symm_apply _ _

/-- The `i`-th face of a singular simplex is its composite with the face inclusion
`faceMap n i`. -/
lemma toC_δ {Z : TopCat.{u}} {n : ℕ} (i : Fin (n + 2)) (ρ : Simp Z (n + 1)) :
    toC ((TopCat.toSSet.obj Z).δ i ρ) = (toC ρ).comp (faceMap n i) :=
  rfl

/-- A singular simplex is determined by its continuous map. -/
lemma toC_injective {Z : TopCat.{u}} {n : ℕ} : Function.Injective (toC (X := Z) (n := n)) :=
  (Z.toSSetObjEquiv (op ⦋n⦌)).injective

/-- For a list of length `n + 2`, the `j`-th entry of `l.eraseIdx i` is the
`i.succAbove j`-th entry of `l`. -/
lemma getD_eraseIdx {l : List (ℕ × ℕ)} {n : ℕ} (hl : l.length = n + 2) (i : Fin (n + 2))
    (j : Fin (n + 1)) : (l.eraseIdx i).getD j (0, 0) = l.getD (i.succAbove j) (0, 0) := by
  have hj := j.isLt
  have hlen : (l.eraseIdx i).length = n + 1 := by
    rw [List.length_eraseIdx, if_pos (by omega)]; omega
  rw [List.getD_eq_getElem _ _ (by omega), List.getElem_eraseIdx,
    List.getD_eq_getElem _ _ (by rw [hl]; exact (i.succAbove j).isLt)]
  by_cases h : (j : ℕ) < i
  · rw [dif_pos h]
    congr 1
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [dif_neg h]
    congr 1
    rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    rfl

/-- The `i`-th face of the path simplex of `l` is the path simplex of `l.eraseIdx i`. -/
lemma δ_pathSimplex (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q) (l : List (ℕ × ℕ))
    (hl : l.length = n + 2) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ i (pathSimplex (n + 1) σ τ l) =
      pathSimplex n σ τ (l.eraseIdx i) := by
  apply toC_injective
  rw [toC_δ, toC_pathSimplex, toC_pathSimplex]
  ext1 t
  refine Prod.ext ?_ ?_
  · change (toC σ) (((vtxMap (n + 1) p _).comp (faceMap n i)) t) = _
    rw [vtxMap_comp_faceMap n p _ (fun j ↦ ((l.eraseIdx i).getD j (0, 0)).1) i
      fun j ↦ by rw [getD_eraseIdx hl]]
    rfl
  · change (toC τ) (((vtxMap (n + 1) q _).comp (faceMap n i)) t) = _
    rw [vtxMap_comp_faceMap n q _ (fun j ↦ ((l.eraseIdx i).getD j (0, 0)).2) i
      fun j ↦ by rw [getD_eraseIdx hl]]
    rfl

/-- Below the length of `l`, the `j`-th entry of `l.map f` is `f` of the `j`-th entry of `l`. -/
lemma getD_map_of_lt {l : List (ℕ × ℕ)} (f : ℕ × ℕ → ℕ × ℕ) {j : ℕ} (hj : j < l.length) :
    (l.map f).getD j (0, 0) = f (l.getD j (0, 0)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj,
    List.getElem_map]

/-- The path simplex of `δ_k σ` and `τ` along `l` is the path simplex of `σ` and `τ` along
`cofaceFst k l`, when the first coordinates of `l` are at most `p`. -/
lemma pathSimplex_δ_fst (n : ℕ) {p q : ℕ} (σ : Simp X (p + 1)) (τ : Simp Y q)
    (l : List (ℕ × ℕ)) (hl : l.length = n + 1) (hp : ∀ v ∈ l, v.1 ≤ p) (k : Fin (p + 2)) :
    pathSimplex n ((TopCat.toSSet.obj X).δ k σ) τ l = pathSimplex n σ τ (cofaceFst k l) := by
  apply toC_injective
  rw [toC_pathSimplex, toC_pathSimplex, toC_δ]
  have hmem : ∀ j : Fin (n + 1), l.getD j (0, 0) ∈ l := fun j ↦ by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  ext1 t
  refine Prod.ext ?_ ?_
  · change (toC σ) (((faceMap p k).comp (vtxMap n p _)) t) = _
    rw [faceMap_comp_vtxMap n p _ (fun j ↦ ((cofaceFst k l).getD j (0, 0)).1) k
      (fun j ↦ hp _ (hmem j)) fun j ↦ by
        rw [cofaceFst, getD_map_of_lt _ (by omega)]]
    rfl
  · change (toC τ) ((vtxMap n q _) t) = (toC τ) ((vtxMap n q _) t)
    congr 3
    funext j
    by_cases hj : j < l.length
    · rw [cofaceFst, getD_map_of_lt _ hj]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [cofaceFst]; omega)]

/-- The path simplex of `σ` and `δ_k τ` along `l` is the path simplex of `σ` and `τ` along
`cofaceSnd k l`, when the second coordinates of `l` are at most `q`. -/
lemma pathSimplex_δ_snd (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y (q + 1))
    (l : List (ℕ × ℕ)) (hl : l.length = n + 1) (hq : ∀ v ∈ l, v.2 ≤ q) (k : Fin (q + 2)) :
    pathSimplex n σ ((TopCat.toSSet.obj Y).δ k τ) l = pathSimplex n σ τ (cofaceSnd k l) := by
  apply toC_injective
  rw [toC_pathSimplex, toC_pathSimplex, toC_δ]
  have hmem : ∀ j : Fin (n + 1), l.getD j (0, 0) ∈ l := fun j ↦ by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  ext1 t
  refine Prod.ext ?_ ?_
  · change (toC σ) ((vtxMap n p _) t) = (toC σ) ((vtxMap n p _) t)
    congr 3
    funext j
    by_cases hj : j < l.length
    · rw [cofaceSnd, getD_map_of_lt _ hj]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [cofaceSnd]; omega)]
  · change (toC τ) (((faceMap q k).comp (vtxMap n q _)) t) = _
    rw [faceMap_comp_vtxMap n q _ (fun j ↦ ((cofaceSnd k l).getD j (0, 0)).2) k
      (fun j ↦ hq _ (hmem j)) fun j ↦ by
        rw [cofaceSnd, getD_map_of_lt _ (by omega)]]
    rfl

/-- The cross product `σ × τ` of singular simplices, an integral chain of degree `n` on `X × Y`
(zero unless `n = p + q`): the image of the shuffle sum under the path simplices. -/
def crossSimplex (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q) :
    Simp (TopCat.of (X × Y)) n →₀ ℤ :=
  Finsupp.mapDomain (pathSimplex n σ τ) (shuffleSum n p q)

/-- The faces of `σ × τ`. -/
lemma mapDomain_δ_crossSimplex (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q)
    (i : Fin (n + 2)) :
    Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i) (crossSimplex (n + 1) σ τ) =
      Finsupp.mapDomain (pathSimplex n σ τ) (lmap (fun l ↦ l.eraseIdx i) (shuffleSum (n + 1) p q)) := by
  rw [crossSimplex, ← Finsupp.mapDomain_comp, lmap, Finsupp.lmapDomain_apply,
    ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr fun l hl ↦ δ_pathSimplex n σ τ l
    (mem_support_shuffleSum hl).1 i

/-- The Leibniz rule for the cross product of singular simplices, in terms of lattice paths. -/
lemma sum_δ_crossSimplex (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q) :
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i) (crossSimplex (n + 1) σ τ) =
      Finsupp.mapDomain (pathSimplex n σ τ)
        (∑ k ∈ Finset.range (p + 1), (-1 : ℤ) ^ k • lmap (cofaceFst k) (lowerFst n p q) +
          (-1 : ℤ) ^ p • ∑ l ∈ Finset.range (q + 1),
            (-1 : ℤ) ^ l • lmap (cofaceSnd l) (lowerSnd n p q)) := by
  rw [← bd_shuffleSum, bd]
  simp_rw [mapDomain_δ_crossSimplex]
  rw [Finsupp.mapDomain_finset_sum]
  simp_rw [Finsupp.mapDomain_smul]
  exact Fin.sum_univ_eq_sum_range
    (fun i ↦ (-1 : ℤ) ^ i • Finsupp.mapDomain (pathSimplex n σ τ)
      (lmap (fun l ↦ l.eraseIdx i) (shuffleSum (n + 1) p q))) (n + 2)

/-- The image under the path simplices of the shuffle sum relabelled by `cofaceFst k` is
`δ_k σ × τ`. -/
lemma mapDomain_pathSimplex_cofaceFst (n : ℕ) {p q : ℕ} (σ : Simp X (p + 1)) (τ : Simp Y q)
    (k : Fin (p + 2)) :
    Finsupp.mapDomain (pathSimplex n σ τ) (lmap (cofaceFst k) (shuffleSum n p q)) =
      crossSimplex n ((TopCat.toSSet.obj X).δ k σ) τ := by
  rw [crossSimplex, lmap, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun l hl ↦ ?_
  have h := mem_support_shuffleSum hl
  exact (pathSimplex_δ_fst n σ τ l h.1 (fun v hv ↦ (h.2 v hv).1) k).symm

/-- The image under the path simplices of the shuffle sum relabelled by `cofaceSnd k` is
`σ × δ_k τ`. -/
lemma mapDomain_pathSimplex_cofaceSnd (n : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y (q + 1))
    (k : Fin (q + 2)) :
    Finsupp.mapDomain (pathSimplex n σ τ) (lmap (cofaceSnd k) (shuffleSum n p q)) =
      crossSimplex n σ ((TopCat.toSSet.obj Y).δ k τ) := by
  rw [crossSimplex, lmap, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun l hl ↦ ?_
  have h := mem_support_shuffleSum hl
  exact (pathSimplex_δ_snd n σ τ l h.1 (fun v hv ↦ (h.2 v hv).2) k).symm

/-- The simplices of `σ × τ` have image in `σ(Δᵖ) × τ(Δ^q)`. -/
lemma singularSimplexImage_subset_of_mem_support (n : ℕ) {p q : ℕ} (σ : Simp X p)
    (τ : Simp Y q) {ρ : Simp (TopCat.of (X × Y)) n} (hρ : crossSimplex n σ τ ρ ≠ 0) :
    singularSimplexImage _ ρ ⊆ singularSimplexImage X σ ×ˢ singularSimplexImage Y τ := by
  classical
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.1
    (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hρ))
  rintro _ ⟨t, rfl⟩
  change toC (pathSimplex n σ τ l) t ∈ _
  rw [toC_pathSimplex]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

end SingularCross

end MMP
