module

public import MMP.AlgebraicTopology.SingularHomology.LocalHomologyHomotopy
public import MMP.AlgebraicTopology.PoincareDuality.MayerVietoris
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Homotopy invariance of finite singular chains and acyclicity of star-shaped sets

For a homotopy `F : Y × [0, 1] → Z` from `f = F(-, 0)` to `g = F(-, 1)`, the prism operator
`P σ = (-1)ⁿ F_#(σ × ι₁)` on singular `n`-simplices, built from the Eilenberg–Zilber cross product
of `MMP.SingularCross`, is a chain homotopy: `∂ P + P ∂ = g_# - f_#`, and
`∂ P = g_# - f_#` in degree `0`. If `F` maps `A × [0, 1]` into `B`, then `P` maps chains in `A`
to chains in `B`.

For a set `C` star-shaped about `p` in a real topological vector space, the straight-line
homotopy from the identity to the constant map at `p` keeps `C` inside `C`, and the push-forward
along the constant map is the chain complex of a point, whose positive-degree cycles are
boundaries. Hence every cycle of positive degree in `C` bounds in `C`, and every `0`-chain in `C`
of augmentation `0` bounds in `C`. With the long exact sequence of the pair at the chain level,
`H_{m+1}(C, A) = 0` whenever `A ⊆ C` and `H_m(A)` vanishes (reduced, for `m = 0`).

## Main definitions

The push-forward `f_#` of chains is `MMP.SingularChain.postcomp`.

* `MMP.SingularChain.aug`: the augmentation.
* `MMP.SingularChain.prism`: the prism operator of a homotopy.
* `MMP.SingularChain.straightLineHomotopy`: `(x, t) ↦ x + t (p - x)`.

## Main results

* `MMP.SingularChain.bd_prism_add_prism_bd`, `bd_prism_zero`: homotopy
  invariance.
* `MMP.SingularChain.prism_mem_inside`: support control of the prism.
* `MMP.SingularChain.exists_bd_eq_of_starConvex`,
  `exists_bd_eq_of_starConvex_zero`: star-shaped sets are acyclic.
* `MMP.SingularChain.exists_bd_add_of_starConvex`,
  `exists_bd_add_of_starConvex_zero`: relative vanishing `H_{m+1}(C, A) = 0`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Theorem 2.10 and Corollary 2.11.
-/

@[expose] public noncomputable section

open Finsupp Set MMP.SingularCross MMP.FundamentalClass MMP.LatticePath

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- The boundary of `b σ` for an `(n + 1)`-simplex `σ`: `∂ (b σ) = ∑ᵢ (-1)ⁱ b (σ ∘ δᵢ)`. -/
lemma bd_single_eq_sum (n : ℕ) (σ : Simplex Y (n + 1)) (b : R) :
    bd R n (single σ b) =
      ∑ i : Fin (n + 2), single (σ.comp (face n i)) ((-1 : R) ^ (i : ℕ) * b) := by
  rw [← smul_single_one, map_smul, bd_single, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul, smul_single_one, mul_comm]

section aug

variable (R) in
/-- The augmentation `ε : C_n(Y) → R`, the sum of the coefficients. -/
def aug (n : ℕ) : Chain R Y n →ₗ[R] R :=
  linearCombination R fun _ ↦ 1

/-- The augmentation of `a σ` is `a`. -/
lemma aug_single {n : ℕ} (σ : Simplex Y n) (a : R) : aug R n (single σ a) = a := by
  rw [aug, linearCombination_single, smul_eq_mul, mul_one]

/-- The boundary of a `1`-chain has augmentation `0`. -/
lemma aug_bd_zero (c : Chain R Y 1) : aug R 0 (bd R 0 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, add_zero]
  | single σ a =>
    rw [bd_single_eq_sum, map_sum, Fin.sum_univ_two, aug_single, aug_single]
    simp

/-- The push-forward along a constant map: the constant simplex with the augmentation as
coefficient. -/
lemma postcomp_const (p : Z) (n : ℕ) (c : Chain R Y n) :
    postcomp R (ContinuousMap.const Y p) n c = single (ContinuousMap.const _ p) (aug R n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, hc, hd, map_add, single_add]
  | single σ a =>
    rw [postcomp_single, aug_single]
    rfl

/-- The boundary of a constant simplex: `∂ κ_{k+1} = κ_k` for `k` odd and `0` for `k` even. -/
lemma bd_single_const (p : Z) (k : ℕ) (b : R) :
    bd R k (single (ContinuousMap.const (stdSimplex ℝ (Fin (k + 1 + 1))) p) b) =
      if Even k then 0 else single (ContinuousMap.const _ p) b := by
  rw [bd_single_eq_sum]
  have hc : ∀ i : Fin (k + 2), (ContinuousMap.const (stdSimplex ℝ (Fin (k + 1 + 1))) p).comp
      (face k i) = ContinuousMap.const _ p := fun _ ↦ rfl
  simp only [hc]
  rw [← Finsupp.single_finset_sum, ← Finset.sum_mul,
    Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : R) ^ i) (k + 2), neg_one_geom_sum]
  by_cases hk : Even k
  · rw [if_pos (by simpa [Nat.even_add] using hk), if_pos hk, zero_mul, single_zero]
  · rw [if_neg (by simpa [Nat.even_add] using hk), if_neg hk, one_mul]

end aug

section castChain

variable (R) in
/-- Integral chains as chains with coefficients in `R`. -/
def castChain (n : ℕ) : Chain ℤ Z n →+ Chain R Z n :=
  mapRange.addMonoidHom (Int.castAddHom R)

/-- `castChain` sends the integral chain `a σ` to `(a : R) σ`. -/
lemma castChain_single {n : ℕ} (σ : Simplex Z n) (a : ℤ) :
    castChain R n (single σ a) = single σ (a : R) := by
  simp [castChain]

/-- `castChain` commutes with multiplication by `(-1)ᵏ`. -/
lemma castChain_neg_one_pow_smul {n : ℕ} (k : ℕ) (c : Chain ℤ Z n) :
    castChain R n ((-1 : ℤ) ^ k • c) = (-1 : R) ^ k • castChain R n c := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul R]
  simp

/-- `castChain` commutes with the boundary. -/
lemma bd_castChain (n : ℕ) (c : Chain ℤ Z (n + 1)) :
    bd R n (castChain R (n + 1) c) = castChain R n (bd ℤ n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [castChain_single, bd_single_eq_sum, bd_single_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [castChain_single]
    push_cast
    rfl

/-- `castChain` sends integral chains in `B` to chains in `B`. -/
lemma castChain_mem_inside {n : ℕ} {B : Set Z} {c : Chain ℤ Z n} (hc : c ∈ inside ℤ n B) :
    castChain R n c ∈ inside R n B := by
  classical
  rw [inside, mem_supported] at hc ⊢
  intro x hx
  apply hc
  simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hx ⊢
  intro h0
  apply hx
  simp [castChain, h0]

end castChain

section prism

/-- The coordinate `Δ¹ → [0, 1]`, `t ↦ t₁`; it sends the vertex `0` to `0` and `1` to `1`. -/
def stdSimplexOneToUnitInterval : C(stdSimplex ℝ (Fin 2), unitInterval) :=
  stdSimplexHomeomorphUnitInterval

/-- `stdSimplexOneToUnitInterval` sends the vertex `0` of `Δ¹` to `0`. -/
lemma stdSimplexOneToUnitInterval_vertex_zero :
    stdSimplexOneToUnitInterval (stdSimplex.vertex 0) = 0 := by
  apply Subtype.ext
  simp [stdSimplexOneToUnitInterval, stdSimplex.vertex]

/-- `stdSimplexOneToUnitInterval` sends the vertex `1` of `Δ¹` to `1`. -/
lemma stdSimplexOneToUnitInterval_vertex_one :
    stdSimplexOneToUnitInterval (stdSimplex.vertex 1) = 1 := by
  apply Subtype.ext
  simp [stdSimplexOneToUnitInterval, stdSimplex.vertex]

/-- `Δⁿ × Δ¹`, as an object of `TopCat`. -/
abbrev prismDom (n : ℕ) : TopCat.{0} :=
  TopCat.of (TopCat.of (stdSimplex ℝ (Fin (n + 1))) × TopCat.of (stdSimplex ℝ (Fin 2)))

/-- `Δⁿ × Δ¹` on the convex-space standard simplices, mapped to `prismDom n`. -/
def prismDomMap (n : ℕ) : C(TopCat.of (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) ×
    TopCat.of (Convexity.StdSimplex ℝ (Fin 2))), prismDom n) :=
  ⟨fun p ↦ ((stdSimplexHomeo _).symm p.1, (stdSimplexHomeo _).symm p.2),
    ((stdSimplexHomeo _).symm.continuous.comp continuous_fst).prodMk
      ((stdSimplexHomeo _).symm.continuous.comp continuous_snd)⟩

/-- The integral prism chain `H_#(ι_n × ι_1)` of a map `H : Δⁿ × Δ¹ → Z`. -/
def prismOf {n : ℕ} (H : C(prismDom n, Z)) : Chain ℤ Z (n + 1) :=
  pushChain (H.comp (prismDomMap n)) (n + 1) (crossSimplex (n + 1) (idSimp n) (idSimp 1))

/-- Naturality of the cross product: `H_#(σ × τ) = (H ∘ (σ × τ))_#(ι_p × ι_q)`. -/
lemma pushChain_crossSimplex {A B : TopCat.{0}} (H : C(TopCat.of (A × B), Z)) (n : ℕ) {p q : ℕ}
    (σ : Simp A p) (τ : Simp B q) :
    pushChain H n (crossSimplex n σ τ) =
      pushChain (Z := TopCat.of (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))) ×
          TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1)))))
        (H.comp ((toC σ).prodMap (toC τ))) n (crossSimplex n (idSimp p) (idSimp q)) := by
  simp only [crossSimplex, pushChain, lmapDomain_apply, ← mapDomain_comp]
  refine mapDomain_congr fun l _ ↦ ?_
  ext1 t
  simp only [Function.comp_apply, ContinuousMap.comp_apply, toC_pathSimplex, toC_idSimp]
  rfl

/-- `H : Δⁿ × Δ¹ → Z` composed with the path simplex along `fstPath n` of `ι_n` and the `l`-th
face of `ι_1` is `s ↦ H(s, v)`, for the vertex `v = l.succAbove 0` of `Δ¹`. -/
lemma comp_toC_pathSimplex_fstPath {n : ℕ} (H : C(prismDom n, Z)) (l : Fin 2) :
    (H.comp (prismDomMap n)).comp ((toC (pathSimplex n (idSimp n)
      ((TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))).δ l (idSimp 1))
        (fstPath n))).comp ⟨stdSimplexHomeo _, (stdSimplexHomeo _).continuous⟩) =
      H.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _
        (stdSimplex.vertex (l.succAbove 0)))) := by
  ext1 t
  change H ((stdSimplexHomeo _).symm (toC (pathSimplex n (idSimp n)
        ((TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))).δ l (idSimp 1)) (fstPath n)) (stdSimplexHomeo _ t)).1,
      (stdSimplexHomeo _).symm (toC (pathSimplex n (idSimp n)
        ((TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))).δ l (idSimp 1)) (fstPath n)) (stdSimplexHomeo _ t)).2) =
    H (t, stdSimplex.vertex (l.succAbove 0))
  rw [toC_pathSimplex_fstPath, toC_δ_idSimp_one, toC_idSimp]
  change H ((stdSimplexHomeo _).symm (stdSimplexHomeo _ t),
    (stdSimplexHomeo _).symm (Convexity.StdSimplex.single (l.succAbove 0))) =
      H (t, stdSimplex.vertex (l.succAbove 0))
  rw [Homeomorph.symm_apply_apply, stdSimplexHomeo_symm_single]

/-- The prism formula in degree `0`: `∂ H_#(ι_0 × ι_1) = H(-, 1) - H(-, 0)`. -/
lemma bd_prismOf_zero (H : C(prismDom 0, Z)) :
    bd ℤ 0 (prismOf H) =
      single (H.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (stdSimplex.vertex 1)))) 1
      - single (H.comp ((ContinuousMap.id _).prodMk
          (ContinuousMap.const _ (stdSimplex.vertex 0)))) 1 := by
  have hleib := sum_δ_crossSimplex 0 (idSimp 0) (idSimp 1)
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    BorelMooreCross.mapDomain_pathSimplex_snd 0 0 0 (idSimp 0) (idSimp 1)] at hleib
  rw [prismOf, bd_pushChain, hleib]
  simp only [lowerFst_zero, map_zero, smul_zero, Finset.sum_const_zero, Finsupp.mapDomain_zero,
    zero_add, pow_zero, one_smul, map_sum, map_zsmul, Fin.sum_univ_two, crossSimplex_zero,
    pushChain_single]
  rw [Fin.sum_univ_two, comp_toC_pathSimplex_fstPath H 0, comp_toC_pathSimplex_fstPath H 1]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.succAbove_zero,
    Fin.succ_zero_eq_one]
  have h10 : (1 : Fin 2).succAbove 0 = 0 := rfl
  rw [h10, sub_eq_add_neg]

/-- The prism formula: `∂ H_#(ι_n × ι_1) = ∑ₖ (-1)ᵏ (H ∘ (δₖ × 1))_#(ι_{n-1} × ι_1)
+ (-1)ⁿ (H(-, 1) - H(-, 0))`. -/
lemma bd_prismOf_succ {m : ℕ} (H : C(prismDom (m + 1), Z)) :
    bd ℤ (m + 1) (prismOf H) =
      ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) •
          prismOf (n := m) (H.comp ((face m k).prodMap (ContinuousMap.id _))) +
        (-1 : ℤ) ^ (m + 1) •
          (single (H.comp ((ContinuousMap.id _).prodMk
              (ContinuousMap.const _ (stdSimplex.vertex 1)))) 1 -
            single (H.comp ((ContinuousMap.id _).prodMk
              (ContinuousMap.const _ (stdSimplex.vertex 0)))) 1) := by
  have hleib := sum_δ_crossSimplex (m + 1) (idSimp (m + 1)) (idSimp 1)
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    BorelMooreCross.mapDomain_pathSimplex_snd (m + 1) (m + 1) 0 (idSimp (m + 1)) (idSimp 1),
    BorelMooreCross.mapDomain_pathSimplex_fst (m + 1) m 1 (idSimp (m + 1)) (idSimp 1)] at hleib
  rw [prismOf, bd_pushChain, hleib, map_add, map_zsmul, map_sum, map_sum, Fin.sum_univ_two]
  congr 1
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_zsmul, pushChain_crossSimplex, toC_δ, toC_idSimp, toC_idSimp, prismOf]
    refine congrArg (fun F ↦ (-1 : ℤ) ^ (k : ℕ) •
      pushChain F (m + 1) (crossSimplex (m + 1) (idSimp m) (idSimp 1))) ?_
    ext ⟨s, u⟩
    exact congrArg (fun a ↦ H (a, (stdSimplexHomeo _).symm u)) (stdSimplexHomeo_symm_face m k s)
  · simp only [map_zsmul, crossSimplex_zero, pushChain_single]
    rw [comp_toC_pathSimplex_fstPath H 0, comp_toC_pathSimplex_fstPath H 1]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      Fin.succAbove_zero, Fin.succ_zero_eq_one]
    have h10 : (1 : Fin 2).succAbove 0 = 0 := rfl
    rw [h10, sub_eq_add_neg]

/-- The map `Δⁿ × Δ¹ → Z`, `(s, t) ↦ F(σ s, t₁)`, of a homotopy `F` and a simplex `σ`. -/
def prismMap (F : C(Y × unitInterval, Z)) {n : ℕ} (σ : Simplex Y n) : C(prismDom n, Z) :=
  F.comp (σ.prodMap stdSimplexOneToUnitInterval)

/-- Precomposing `prismMap F σ` with `δₖ × 1` gives `prismMap F (σ ∘ δₖ)`. -/
lemma prismMap_comp_face (F : C(Y × unitInterval, Z)) {m : ℕ} (σ : Simplex Y (m + 1))
    (k : Fin (m + 2)) :
    (prismMap F σ).comp ((face m k).prodMap (ContinuousMap.id _)) =
      prismMap F (σ.comp (face m k)) :=
  rfl

/-- If `F(-, 0) = f`, then `prismMap F σ` restricted to `Δⁿ × {0}` is `f ∘ σ`. -/
lemma prismMap_vertex_zero (F : C(Y × unitInterval, Z)) {f : C(Y, Z)}
    (hf : ∀ y, F (y, 0) = f y) {n : ℕ} (σ : Simplex Y n) :
    (prismMap F σ).comp ((ContinuousMap.id _).prodMk
      (ContinuousMap.const _ (stdSimplex.vertex 0))) = f.comp σ := by
  ext1 t
  change F (σ t, stdSimplexOneToUnitInterval (stdSimplex.vertex 0)) = f (σ t)
  rw [stdSimplexOneToUnitInterval_vertex_zero, hf]

/-- If `F(-, 1) = g`, then `prismMap F σ` restricted to `Δⁿ × {1}` is `g ∘ σ`. -/
lemma prismMap_vertex_one (F : C(Y × unitInterval, Z)) {g : C(Y, Z)}
    (hg : ∀ y, F (y, 1) = g y) {n : ℕ} (σ : Simplex Y n) :
    (prismMap F σ).comp ((ContinuousMap.id _).prodMk
      (ContinuousMap.const _ (stdSimplex.vertex 1))) = g.comp σ := by
  ext1 t
  change F (σ t, stdSimplexOneToUnitInterval (stdSimplex.vertex 1)) = g (σ t)
  rw [stdSimplexOneToUnitInterval_vertex_one, hg]

variable (R) in
/-- The prism operator `P` of a homotopy `F : Y × [0, 1] → Z`:
`P σ = (-1)ⁿ F_#(σ × ι_1)` on an `n`-simplex `σ`. -/
def prism (F : C(Y × unitInterval, Z)) (n : ℕ) : Chain R Y n →ₗ[R] Chain R Z (n + 1) :=
  (-1 : R) ^ n • linearCombination R fun σ ↦ castChain R (n + 1) (prismOf (prismMap F σ))

/-- The prism operator on a single simplex: `P σ = (-1)ⁿ F_#(σ × ι_1)`. -/
lemma prism_single (F : C(Y × unitInterval, Z)) {n : ℕ} (σ : Simplex Y n) :
    prism R F n (single σ 1) = (-1 : R) ^ n • castChain R (n + 1) (prismOf (prismMap F σ)) := by
  rw [prism, LinearMap.smul_apply, linearCombination_single, one_smul]

/-- **Homotopy invariance**, degree `0`: `∂ P c = g_# c - f_# c`. -/
theorem bd_prism_zero (F : C(Y × unitInterval, Z)) {f g : C(Y, Z)} (hf : ∀ y, F (y, 0) = f y)
    (hg : ∀ y, F (y, 1) = g y) (c : Chain R Y 0) :
    bd R 0 (prism R F 0 c) = postcomp R g 0 c - postcomp R f 0 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]; abel
  | single σ a =>
    rw [← smul_single_one]
    simp only [map_smul]
    rw [← smul_sub]
    congr 1
    rw [prism_single, pow_zero, one_smul, bd_castChain, bd_prismOf_zero, prismMap_vertex_zero F hf,
      prismMap_vertex_one F hg, map_sub, castChain_single, castChain_single, postcomp_single,
      postcomp_single, Int.cast_one]

/-- The chain homotopy formula `∂ P σ + P ∂ σ = g ∘ σ - f ∘ σ` on a single simplex `σ` of
positive degree. -/
lemma bd_prism_add_prism_bd_single (F : C(Y × unitInterval, Z)) {f g : C(Y, Z)}
    (hf : ∀ y, F (y, 0) = f y) (hg : ∀ y, F (y, 1) = g y) {n : ℕ} (σ : Simplex Y (n + 1)) :
    bd R (n + 1) (prism R F (n + 1) (single σ 1)) + prism R F n (bd R n (single σ 1)) =
      single (g.comp σ) 1 - single (f.comp σ) 1 := by
  rw [prism_single, map_smul, bd_castChain, bd_prismOf_succ, bd_single, map_sum, map_add,
    map_sum, castChain_neg_one_pow_smul, map_sub, castChain_single, castChain_single, Int.cast_one,
    prismMap_vertex_zero F hf, prismMap_vertex_one F hg]
  set D := single (g.comp σ) (1 : R) - single (f.comp σ) 1
  set S := ∑ k : Fin (n + 2), (-1 : R) ^ (k : ℕ) •
    castChain R (n + 1) (prismOf (prismMap F (σ.comp (face n k))))
  have h1 : ∑ k : Fin (n + 2), castChain R (n + 1) ((-1 : ℤ) ^ (k : ℕ) •
      prismOf (n := n) ((prismMap F σ).comp ((face n k).prodMap (ContinuousMap.id _)))) = S :=
    Finset.sum_congr rfl fun k _ ↦ by rw [castChain_neg_one_pow_smul, prismMap_comp_face]
  have h2 : ∑ k : Fin (n + 2), prism R F n ((-1 : R) ^ (k : ℕ) • single (σ.comp (face n k)) 1) =
      (-1 : R) ^ n • S := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, prism_single, smul_comm]
  rw [h1, h2, smul_add, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, pow_succ,
    mul_neg_one, neg_smul]
  abel

/-- **Homotopy invariance**: the prism operator is a chain homotopy from `f_#` to `g_#`,
`∂ P c + P ∂ c = g_# c - f_# c`. -/
theorem bd_prism_add_prism_bd (F : C(Y × unitInterval, Z)) {f g : C(Y, Z)}
    (hf : ∀ y, F (y, 0) = f y) (hg : ∀ y, F (y, 1) = g y) (n : ℕ) (c : Chain R Y (n + 1)) :
    bd R (n + 1) (prism R F (n + 1) c) + prism R F n (bd R n c) =
      postcomp R g (n + 1) c - postcomp R f (n + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add]
    rw [add_add_add_comm, hc, hd]
    abel
  | single σ a =>
    rw [← smul_single_one]
    simp only [map_smul]
    rw [← smul_add, ← smul_sub, bd_prism_add_prism_bd_single F hf hg, postcomp_single,
      postcomp_single]

/-- **Support of the prism**: if `F` maps `A × [0, 1]` into `B`, then `P` maps chains in `A` to
chains in `B`. -/
theorem prism_mem_inside (F : C(Y × unitInterval, Z)) {A : Set Y} {B : Set Z}
    (h : MapsTo F (A ×ˢ univ) B) {n : ℕ} {c : Chain R Y n} (hc : c ∈ inside R n A) :
    prism R F n c ∈ inside R (n + 1) B := by
  refine VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ ?_) hc
  rw [prism_single]
  refine Submodule.smul_mem _ _ (castChain_mem_inside (pushChain_mem_inside _ fun ρ _ ↦ ?_))
  rintro _ ⟨t, rfl⟩
  exact h ⟨hσ ⟨_, rfl⟩, mem_univ _⟩

end prism

section starConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- The straight-line homotopy `(x, t) ↦ x + t (p - x)` from the identity to the constant map
at `p`. -/
def straightLineHomotopy (p : E) : C(E × unitInterval, E) where
  toFun x := x.1 + ((x.2 : ℝ)) • (p - x.1)
  continuous_toFun := by fun_prop

/-- If `C` is star-shaped about `p`, the straight-line homotopy to `p` maps `C × [0, 1]` into
`C`. -/
lemma straightLineHomotopy_mapsTo {C : Set E} {p : E} (hC : StarConvex ℝ p C) :
    MapsTo (straightLineHomotopy p) (C ×ˢ univ) C := by
  rintro ⟨x, t⟩ ⟨hx, -⟩
  have h := hC hx t.2.1 (sub_nonneg.2 t.2.2) (add_sub_cancel _ _)
  convert h using 1
  change x + (t : ℝ) • (p - x) = (t : ℝ) • p + (1 - (t : ℝ)) • x
  rw [smul_sub, sub_smul, one_smul]
  abel

/-- A nonzero chain in `C` forces `C` to be nonempty. -/
lemma nonempty_of_mem_inside {n : ℕ} {C : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n C)
    (h0 : c ≠ 0) : C.Nonempty := by
  obtain ⟨σ, hσ⟩ := Finsupp.support_nonempty_iff.2 h0
  exact ⟨σ (stdSimplex.vertex 0), hc (Finset.mem_coe.2 hσ) ⟨_, rfl⟩⟩

/-- A multiple of the constant simplex at a point `p ∈ C` is a chain in `C`. -/
lemma single_const_mem_inside {n : ℕ} {C : Set Y} {p : Y} (hp : p ∈ C) (b : R) :
    single (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) p) b ∈ inside R n C :=
  single_mem_supported R _ (by rintro _ ⟨t, rfl⟩; exact hp)

/-- The chain homotopy relation for the straight-line homotopy to `p`, on a cycle:
`c = κ_# c - ∂ P c`. -/
lemma eq_sub_bd_prism_straightLine (p : E) {m : ℕ} {c : Chain R E (m + 1)} (hbd : bd R m c = 0) :
    c = single (ContinuousMap.const _ p) (aug R (m + 1) c) -
      bd R (m + 1) (prism R (straightLineHomotopy p) (m + 1) c) := by
  have h := bd_prism_add_prism_bd (R := R) (straightLineHomotopy p) (f := ContinuousMap.id E)
    (g := ContinuousMap.const E p) (fun y ↦ by simp [straightLineHomotopy])
    (fun y ↦ by simp [straightLineHomotopy]) m c
  rw [hbd, map_zero, add_zero, postcomp_id, postcomp_const] at h
  rw [h]
  abel

/-- **Star-shaped sets are acyclic.** A cycle of positive degree in a star-shaped set `C` is the
boundary of a chain in `C`. -/
theorem exists_bd_eq_of_starConvex {C : Set E} {p : E} (hC : StarConvex ℝ p C) {m : ℕ}
    {c : Chain R E (m + 1)} (hc : c ∈ inside R (m + 1) C) (hbd : bd R m c = 0) :
    ∃ w ∈ inside R (m + 2) C, bd R (m + 1) w = c := by
  by_cases h0 : c = 0
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, h0]⟩
  have hp : p ∈ C := hC.mem (nonempty_of_mem_inside hc h0)
  have hP := prism_mem_inside (R := R) _ (straightLineHomotopy_mapsTo hC) hc
  have heq := eq_sub_bd_prism_straightLine (R := R) p hbd
  set s := aug R (m + 1) c
  set P := prism R (straightLineHomotopy p) (m + 1) c
  by_cases hm : Even m
  · refine ⟨single (ContinuousMap.const _ p) s - P,
      Submodule.sub_mem _ (single_const_mem_inside hp s) hP, ?_⟩
    rw [map_sub, bd_single_const, if_neg (by simpa [Nat.even_add_one] using hm), ← heq]
  · have hs : s = 0 := by
      have h1 := congrArg (bd R m) heq
      rw [hbd, map_sub, bd_bd, sub_zero, bd_single_const, if_neg hm] at h1
      exact (Finsupp.single_eq_zero.1 h1.symm)
    refine ⟨-P, Submodule.neg_mem _ hP, ?_⟩
    rw [map_neg, heq, hs, single_zero, zero_sub]

/-- **Star-shaped sets are acyclic**, degree `0`: a `0`-chain in a star-shaped set `C` with
augmentation `0` is the boundary of a `1`-chain in `C`. -/
theorem exists_bd_eq_of_starConvex_zero {C : Set E} {p : E} (hC : StarConvex ℝ p C)
    {c : Chain R E 0} (hc : c ∈ inside R 0 C) (haug : aug R 0 c = 0) :
    ∃ w ∈ inside R 1 C, bd R 0 w = c := by
  have h := bd_prism_zero (R := R) (straightLineHomotopy p) (f := ContinuousMap.id E)
    (g := ContinuousMap.const E p) (fun y ↦ by simp [straightLineHomotopy])
    (fun y ↦ by simp [straightLineHomotopy]) c
  rw [postcomp_id, postcomp_const, haug, single_zero, zero_sub] at h
  refine ⟨-prism R (straightLineHomotopy p) 0 c,
    Submodule.neg_mem _ (prism_mem_inside _ (straightLineHomotopy_mapsTo hC) hc), ?_⟩
  rw [map_neg, h, neg_neg]

/-- **Relative vanishing** `H_{m+2}(C, A) = 0` for `C` star-shaped and `A ⊆ C` with
`H_{m+1}(A) = 0`: every `(m+2)`-chain in `C` with boundary in `A` is `∂ w + a` with `w` in `C` and
`a` in `A`. -/
theorem exists_bd_add_of_starConvex {C A : Set E} {p : E} (hC : StarConvex ℝ p C) (hAC : A ⊆ C)
    {m : ℕ} (hA : ∀ z ∈ inside R (m + 1) A, bd R m z = 0 →
      ∃ a ∈ inside R (m + 2) A, bd R (m + 1) a = z)
    {c : Chain R E (m + 2)} (hc : c ∈ inside R (m + 2) C)
    (hbd : bd R (m + 1) c ∈ inside R (m + 1) A) :
    ∃ w ∈ inside R (m + 3) C, ∃ a ∈ inside R (m + 2) A, c = bd R (m + 2) w + a := by
  obtain ⟨a, ha, hba⟩ := hA _ hbd (bd_bd m c)
  obtain ⟨w, hw, hbw⟩ := exists_bd_eq_of_starConvex (R := R) hC (m := m + 1)
    (Submodule.sub_mem _ hc (inside_mono _ hAC ha)) (by rw [map_sub, hba, sub_self])
  exact ⟨w, hw, a, ha, by rw [hbw, sub_add_cancel]⟩

/-- **Relative vanishing** `H_1(C, A) = 0` for `C` star-shaped and `A ⊆ C` with reduced
`H̃_0(A) = 0`: every `1`-chain in `C` with boundary in `A` is `∂ w + a` with `w` in `C` and `a` in
`A`. -/
theorem exists_bd_add_of_starConvex_zero {C A : Set E} {p : E} (hC : StarConvex ℝ p C)
    (hAC : A ⊆ C) (hA : ∀ z ∈ inside R 0 A, aug R 0 z = 0 → ∃ a ∈ inside R 1 A, bd R 0 a = z)
    {c : Chain R E 1} (hc : c ∈ inside R 1 C) (hbd : bd R 0 c ∈ inside R 0 A) :
    ∃ w ∈ inside R 2 C, ∃ a ∈ inside R 1 A, c = bd R 1 w + a := by
  obtain ⟨a, ha, hba⟩ := hA _ hbd (aug_bd_zero c)
  obtain ⟨w, hw, hbw⟩ := exists_bd_eq_of_starConvex (R := R) hC (m := 0)
    (Submodule.sub_mem _ hc (inside_mono _ hAC ha)) (by rw [map_sub, hba, sub_self])
  exact ⟨w, hw, a, ha, by rw [hbw, sub_add_cancel]⟩

end starConvex

end SingularChain

end MMP
