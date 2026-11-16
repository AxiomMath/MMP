module

public import MMP.AlgebraicTopology.FundamentalClass.Homeomorphism
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProduct

/-!
# Homotopies and local homology

Let `F : Δⁿ × Δ¹ → X` be a homotopy between the singular simplices `F₀ = F(-, 0)` and
`F₁ = F(-, 1)` whose restriction to `∂Δⁿ × Δ¹` avoids the point `x`. Then `F₀` and `F₁` have
the same class in the local homology `H_n(X, X - x; ℤ)`: the prism `P = F_*(ι_n × ι_1)`, the
push-forward of the Eilenberg–Zilber product of the identity simplices of `Δⁿ` and `Δ¹`,
satisfies `∂ P = F_*(∂ι_n × ι_1) + (-1)ⁿ (F₁ - F₀)`, and the first term is a chain of `X - x`.

## Main definitions

* `MMP.LatticePath.fstPath`: the lattice path `(0, 0), (1, 0), …, (n, 0)`.
* `MMP.SingularCross.pushChain`: the push-forward of integral chains of a
  topological space along a continuous map, from simplicial to continuous-map simplices.

## Main results

* `MMP.SingularCross.crossSimplex_zero`: the product of an `n`-simplex with a
  point is a single simplex.
* `MMP.FundamentalClass.isLocallyHomologous_of_homotopy`: homotopic simplices
  whose homotopy avoids `x` on the boundary are locally homologous at `x`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Theorem 2.10.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial Finsupp Set MMP.LatticePath Convexity
  MMP.SingularChain

universe u

namespace MMP

namespace LatticePath

/-- The lattice path `(0, 0), (1, 0), …, (n, 0)`. -/
def fstPath (n : ℕ) : List (ℕ × ℕ) := (List.range (n + 1)).map fun i ↦ (i, 0)

/-- Extending the path `(0, 0), …, (n, 0)` by a first-coordinate step gives
`(0, 0), …, (n + 1, 0)`. -/
lemma stepFst_fstPath (n : ℕ) : stepFst (fstPath n) = fstPath (n + 1) := by
  simp [stepFst, fstPath, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- The shuffle sum `∇_{n,0}` is the single path `(0, 0), …, (n, 0)`. -/
lemma shuffleSum_self_zero (n : ℕ) : shuffleSum n n 0 = Finsupp.single (fstPath n) 1 := by
  induction n with
  | zero => simp [shuffleSum, fstPath]
  | succ n ih =>
    rw [shuffleSum_succ, lowerFst_succ, lowerSnd_zero, ih]
    simp [lmap, stepFst_fstPath]

/-- The `j`-th vertex of the path `(0, 0), …, (n, 0)` is `(j, 0)`. -/
lemma getD_fstPath {n j : ℕ} (hj : j < n + 1) : (fstPath n).getD j (0, 0) = (j, 0) := by
  simp [fstPath, List.getD_eq_getElem?_getD, hj]

end LatticePath

namespace SingularCross

variable {X Y : TopCat.{u}}

/-- The map of standard simplices induced by the identity is the identity. -/
lemma stdSimplex_map_id {ι : Type*} [Fintype ι] [DecidableEq ι] (t : stdSimplex ℝ ι) :
    stdSimplex.map id t = t := by
  ext y
  simp [stdSimplex.map]
  rfl

/-- The vertex map of the first coordinates of `(0, 0), …, (n, 0)` is the identity of `Δⁿ`. -/
lemma vtxMap_fstPath (n : ℕ) :
    vtxMap n n (fun j ↦ ((fstPath n).getD j (0, 0)).1) = ContinuousMap.id _ := by
  ext1 t
  have : vtx n n (fun j ↦ ((fstPath n).getD j (0, 0)).1) = id := by
    funext j
    apply Fin.ext
    change min ((fstPath n).getD j (0, 0)).1 n = j
    rw [getD_fstPath j.isLt]
    exact min_eq_left (Nat.le_of_lt_succ j.isLt)
  change StdSimplex.map _ t = t
  rw [this, StdSimplex.map_id]

/-- The product of an `n`-simplex with a point is a single simplex. -/
lemma crossSimplex_zero (n : ℕ) (σ : Simp X n) (τ : Simp Y 0) :
    crossSimplex n σ τ = Finsupp.single (pathSimplex n σ τ (fstPath n)) 1 := by
  rw [crossSimplex, shuffleSum_self_zero, mapDomain_single]

/-- The simplex of `σ × τ` along the path `(0, 0), …, (n, 0)` sends `t` to `(σ t, τ (v t))`,
where `v : Δⁿ → Δ⁰` is the vertex map of the second coordinates of the path. -/
lemma toC_pathSimplex_fstPath (n : ℕ) (σ : Simp X n) (τ : Simp Y 0)
    (t : StdSimplex ℝ (Fin (n + 1))) :
    toC (pathSimplex n σ τ (fstPath n)) t =
      (toC σ t, toC τ (vtxMap n 0 (fun j ↦ ((fstPath n).getD j (0, 0)).2) t)) := by
  rw [toC_pathSimplex, vtxMap_fstPath]
  rfl

/-- The push-forward of integral chains of a topological space `Z` along a continuous map
`F : Z → X`, from simplicial singular simplices to continuous maps `Δᵐ → X`. -/
def pushChain {Z : TopCat.{u}} {W : Type*} [TopologicalSpace W] (F : C(Z, W)) (m : ℕ) :
    (Simp Z m →₀ ℤ) →ₗ[ℤ] Chain ℤ W m :=
  lmapDomain ℤ ℤ fun ρ ↦ F.comp ((toC ρ).comp ⟨stdSimplexHomeo _, (stdSimplexHomeo _).continuous⟩)

/-- The push-forward of a single simplex `ρ` with coefficient `a` is the single simplex
`F ∘ ρ` with coefficient `a`. -/
lemma pushChain_single {Z : TopCat.{u}} {W : Type*} [TopologicalSpace W] (F : C(Z, W)) {m : ℕ}
    (ρ : Simp Z m) (a : ℤ) :
    pushChain F m (Finsupp.single ρ a) =
      Finsupp.single (F.comp ((toC ρ).comp ⟨stdSimplexHomeo _, (stdSimplexHomeo _).continuous⟩)) a := by
  simp [pushChain]

/-- The boundary of a push-forward is the push-forward of the alternating sum of the faces. -/
lemma bd_pushChain {Z : TopCat.{u}} {W : Type*} [TopologicalSpace W] (F : C(Z, W)) (m : ℕ)
    (c : Simp Z (m + 1) →₀ ℤ) :
    bd ℤ m (pushChain F (m + 1) c) = pushChain F m
      (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • mapDomain ((TopCat.toSSet.obj Z).δ i) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, hc, hd, mapDomain_add, smul_add, Finset.sum_add_distrib]
  | single ρ a =>
    rw [pushChain_single, ← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, bd_single]
    simp only [mapDomain_single, map_sum, map_smul, pushChain_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [toC_δ]
    simp only [smul_single, smul_eq_mul, mul_one]
    rw [mul_comm]
    congr 1
    ext t
    exact congrArg (fun s ↦ F (toC ρ s)) (stdSimplexHomeo_face m i t)

/-- If every simplex in the support of `c` is mapped by `F` into `A`, then the push-forward of
`c` is a chain of `A`. -/
lemma pushChain_mem_inside {Z : TopCat.{u}} {W : Type*} [TopologicalSpace W] (F : C(Z, W))
    {m : ℕ} {A : Set W} {c : Simp Z m →₀ ℤ}
    (hc : ∀ ρ, c ρ ≠ 0 → range (F.comp (toC ρ)) ⊆ A) : pushChain F m c ∈ inside ℤ m A := by
  classical
  rw [pushChain, lmapDomain_apply, mem_supported]
  intro σ hσ
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finset.mem_coe.1 hσ))
  rintro _ ⟨t, rfl⟩
  exact hc ρ (mem_support_iff.1 hρ) ⟨_, rfl⟩

end SingularCross

namespace FundamentalClass

open SingularCross

/-- The identity simplex of `Δⁿ`. -/
def idSimp (n : ℕ) : Simp (TopCat.of (StdSimplex ℝ (Fin (n + 1)))) n :=
  ((TopCat.of (StdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv (op ⦋n⦌)).symm (ContinuousMap.id _)

/-- The identity simplex of `Δⁿ` is the identity map. -/
lemma toC_idSimp (n : ℕ) : toC (idSimp n) = ContinuousMap.id _ :=
  Equiv.apply_symm_apply _ _

/-- The point `Δ⁰ → Δ¹` at the vertex `1 - l`: the face `δ_l` of the identity simplex. -/
lemma toC_δ_idSimp_one (l : Fin 2) (s : StdSimplex ℝ (Fin 1)) :
    toC ((TopCat.toSSet.obj _).δ l (idSimp 1)) s = StdSimplex.single (l.succAbove 0) := by
  rw [toC_δ, toC_idSimp, Subsingleton.elim s (StdSimplex.single 0)]
  exact StdSimplex.map_single _ _

/-- The faces of `Δⁿ` lie in the coordinate hyperplanes. -/
lemma toC_δ_idSimp_apply {n : ℕ} (k : Fin (n + 2)) (s : StdSimplex ℝ (Fin (n + 1))) :
    (toC ((TopCat.toSSet.obj _).δ k (idSimp (n + 1))) s).weights k = 0 := by
  rw [toC_δ, toC_idSimp]
  change (StdSimplex.map k.succAbove s).weights k = 0
  rw [StdSimplex.weights_map, Finsupp.mapDomain_notin_range]
  rintro ⟨j, hj⟩
  exact Fin.succAbove_ne k j hj

variable {X : Type*} [TopologicalSpace X]

/-- **Homotopic simplices are locally homologous.** Let `F : Δⁿ × Δ¹ → X` be a homotopy whose
restriction to `∂Δⁿ × Δ¹` avoids `x`. Then `F(-, 0)` and `F(-, 1)` have the same class in
`H_n(X, X - x; ℤ)`. -/
theorem isLocallyHomologous_of_homotopy {x : X} {n : ℕ}
    (F : C(stdSimplex ℝ (Fin (n + 1)) × stdSimplex ℝ (Fin 2), X))
    (hF : ∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, (t : Fin (n + 1) → ℝ) i = 0) →
      ∀ s, F (t, s) ≠ x) :
    IsLocallyHomologous x
      (F.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (stdSimplex.vertex 0))))
      (F.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (stdSimplex.vertex 1)))) := by
  set A := TopCat.of (StdSimplex ℝ (Fin (n + 1)))
  set B := TopCat.of (StdSimplex ℝ (Fin 2))
  let F' : C(TopCat.of (A × B), X) := F.comp
    ⟨fun p ↦ ((stdSimplexHomeo _).symm p.1, (stdSimplexHomeo _).symm p.2),
      ((stdSimplexHomeo _).symm.continuous.comp continuous_fst).prodMk
        ((stdSimplexHomeo _).symm.continuous.comp continuous_snd)⟩
  set c := crossSimplex (n + 1) (idSimp n) (idSimp 1)
  have hleib := sum_δ_crossSimplex n (idSimp n) (idSimp 1)
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    BorelMooreCross.mapDomain_pathSimplex_snd n n 0 (idSimp n) (idSimp 1)] at hleib
  set G := Finsupp.mapDomain (pathSimplex n (idSimp n) (idSimp 1))
    (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k • lmap (cofaceFst k) (lowerFst n n 1))
  have hG : pushChain F' n G ∈ inside ℤ n ({x}ᶜ : Set X) := by
    rcases n with _ | m
    · simp [G]
    · have hG' : G = ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) •
          crossSimplex (m + 1) ((TopCat.toSSet.obj A).δ k (idSimp (m + 1))) (idSimp 1) :=
        BorelMooreCross.mapDomain_pathSimplex_fst (m + 1) m 1 (idSimp (m + 1)) (idSimp 1)
      rw [hG', map_sum]
      refine Submodule.sum_mem _ fun k _ ↦ ?_
      rw [map_zsmul]
      refine Submodule.smul_of_tower_mem _ _ (pushChain_mem_inside F' fun ρ hρ ↦ ?_)
      rintro _ ⟨t, rfl⟩
      obtain ⟨⟨s, hs⟩, -⟩ :=
        singularSimplexImage_subset_of_mem_support _ _ _ hρ ⟨t, rfl⟩
      have h0 : (toC ρ t).1.weights k = 0 := hs ▸ toC_δ_idSimp_apply k s
      exact hF _ ⟨k, h0⟩ _
  refine ⟨-((-1 : ℤ) ^ n • pushChain F' (n + 1) c), (-1 : ℤ) ^ n • pushChain F' n G,
    Submodule.smul_of_tower_mem _ _ hG, ?_⟩
  rw [map_neg, map_zsmul, bd_pushChain, hleib, map_add, map_zsmul, map_sum, Fin.sum_univ_two]
  simp only [map_zsmul, crossSimplex_zero, pushChain_single]
  have hv : ∀ l : Fin 2, F'.comp ((toC (pathSimplex n (idSimp n)
      ((TopCat.toSSet.obj B).δ l (idSimp 1)) (fstPath n))).comp
        ⟨stdSimplexHomeo _, (stdSimplexHomeo _).continuous⟩) =
      F.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _
        (stdSimplex.vertex (l.succAbove 0)))) := fun l ↦ by
    ext1 t
    change F ((stdSimplexHomeo _).symm (toC (pathSimplex n (idSimp n)
        ((TopCat.toSSet.obj B).δ l (idSimp 1)) (fstPath n)) (stdSimplexHomeo _ t)).1,
      (stdSimplexHomeo _).symm (toC (pathSimplex n (idSimp n)
        ((TopCat.toSSet.obj B).δ l (idSimp 1)) (fstPath n)) (stdSimplexHomeo _ t)).2) =
        F (t, stdSimplex.vertex (l.succAbove 0))
    rw [toC_pathSimplex_fstPath, toC_δ_idSimp_one, toC_idSimp]
    change F ((stdSimplexHomeo _).symm (stdSimplexHomeo _ t),
      (stdSimplexHomeo _).symm (StdSimplex.single (l.succAbove 0))) =
        F (t, stdSimplex.vertex (l.succAbove 0))
    rw [Homeomorph.symm_apply_apply, stdSimplexHomeo_symm_single]
  rw [hv 0, hv 1]
  simp only [Fin.succAbove_zero, Fin.succ_zero_eq_one, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, smul_add, smul_neg, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow]
  rw [show (1 : Fin 2).succAbove 0 = 0 from rfl]
  abel

end FundamentalClass

end MMP
