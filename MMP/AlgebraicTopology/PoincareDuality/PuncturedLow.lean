module

public import MMP.AlgebraicTopology.PoincareDuality.Punctured
public import MMP.AlgebraicTopology.PoincareDuality.Box
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The low-degree homology of the punctured space `ℝⁿ - 0`

In the finite chain model of singular chains, the reduced homology `H̃_k(ℝⁿ - 0; R)` vanishes for
`k ≤ n - 2`, and hence the local homology `H_k(ℝⁿ, ℝⁿ - 0; R)` vanishes for `k ≤ n - 1`.

* Reduced `H̃₀(A) = 0` (`ReducedZeroVanishing`) for a set `A` any two points of which are joined
  by a path in `A`: a path is a singular `1`-simplex whose boundary is the difference of its
  endpoints.
* Its transport along a homotopy, as for `CycleVanishing.of_homotopy`.
* Reduced Mayer–Vietoris in degree `1`: `H₁(U) = H₁(V) = 0` and `H̃₀(U ∩ V) = 0` give
  `H₁(U ∪ V) = 0`.
* Induction on `n` with the half-axis complements `halfAxisCompl`, and the long exact sequence of
  the pair `(ℝⁿ, ℝⁿ - 0)` at the chain level.

## Main definitions

* `MMP.SingularChain.ReducedZeroVanishing`: `H̃₀(A; R) = 0`.

## Main results

* `MMP.SingularChain.reducedZeroVanishing_of_joinedIn`: `H̃₀(A) = 0` for a path-connected `A`.
* `MMP.SingularChain.CycleVanishing.union_of_reducedZeroVanishing`: reduced Mayer–Vietoris in
  degree `1`.
* `MMP.SingularChain.reducedZeroVanishing_compl_zero`: `H̃₀(ℝⁿ - 0) = 0`, `n ≥ 2`.
* `MMP.SingularChain.cycleVanishing_compl_zero_low`: `H_{j+1}(ℝⁿ - 0) = 0` for
  `j + 2 < n`.
* `MMP.SingularChain.relVanishing_singleton_zero_low`:
  `H_{k+1}(ℝⁿ, ℝⁿ - 0) = 0` for `k + 1 < n`.
* `MMP.SingularChain.isRelBoundary_singleton_zero_zero`:
  `H_0(ℝⁿ, ℝⁿ - 0) = 0` for `n ≥ 1`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.7 and §2.2, Corollary 2.14
  (homology of spheres).
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

section reduced

variable (R) in
/-- Reduced `H̃₀(A; R) = 0`, computed with chains of `Y` lying in `A`: every `0`-chain lying in
`A` of augmentation `0` is the boundary of a `1`-chain lying in `A`. -/
def ReducedZeroVanishing (A : Set Y) : Prop :=
  ∀ c ∈ inside R 0 A, aug R 0 c = 0 → IsBoundaryIn R 0 A c

/-- A singular `0`-simplex is the constant simplex at its value. -/
lemma simplex_zero_eq_const (σ : Simplex Y 0) :
    σ = ContinuousMap.const _ (σ (stdSimplex.vertex 0)) := by
  ext t
  rw [Subsingleton.elim (α := stdSimplex ℝ (Fin 1)) t (stdSimplex.vertex 0)]
  rfl

/-- The singular `1`-simplex of a path. -/
def pathSimplex {x y : Y} (γ : Path x y) : Simplex Y 1 :=
  (γ : C(unitInterval, Y)).comp stdSimplexOneToUnitInterval

/-- The `0`-th face of the simplex of a path from `x` to `y` is the constant simplex at `y`. -/
lemma pathSimplex_comp_face_zero {x y : Y} (γ : Path x y) :
    (pathSimplex γ).comp (face 0 0) = ContinuousMap.const _ y := by
  rw [simplex_zero_eq_const ((pathSimplex γ).comp (face 0 0))]
  congr 1
  change γ (stdSimplexOneToUnitInterval (stdSimplex.map (Fin.succAbove 0) (stdSimplex.vertex 0)))
    = y
  rw [stdSimplex.map_vertex]
  change γ (stdSimplexOneToUnitInterval (stdSimplex.vertex 1)) = y
  rw [stdSimplexOneToUnitInterval_vertex_one, γ.target]

/-- The `1`-st face of the simplex of a path from `x` to `y` is the constant simplex at `x`. -/
lemma pathSimplex_comp_face_one {x y : Y} (γ : Path x y) :
    (pathSimplex γ).comp (face 0 1) = ContinuousMap.const _ x := by
  rw [simplex_zero_eq_const ((pathSimplex γ).comp (face 0 1))]
  congr 1
  change γ (stdSimplexOneToUnitInterval (stdSimplex.map (Fin.succAbove 1) (stdSimplex.vertex 0)))
    = x
  rw [stdSimplex.map_vertex]
  change γ (stdSimplexOneToUnitInterval (stdSimplex.vertex 0)) = x
  rw [stdSimplexOneToUnitInterval_vertex_zero, γ.source]

/-- The boundary of the simplex of a path from `x` to `y` is `[y] - [x]`. -/
lemma bd_single_pathSimplex {x y : Y} (γ : Path x y) :
    bd R 0 (single (pathSimplex γ) 1) =
      single (ContinuousMap.const _ y) 1 - single (ContinuousMap.const _ x) 1 := by
  rw [bd_single_eq_sum, Fin.sum_univ_two, pathSimplex_comp_face_zero, pathSimplex_comp_face_one]
  simp [sub_eq_add_neg]

/-- **`H̃₀` of a path-connected set.** If any two points of `A` are joined by a path in `A`, then
reduced `H̃₀(A) = 0`. -/
theorem reducedZeroVanishing_of_joinedIn {A : Set Y} (hA : ∀ x ∈ A, ∀ y ∈ A, JoinedIn A x y) :
    ReducedZeroVanishing R A := by
  intro c hc haug
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rw [eq_zero_of_mem_inside_empty hc]
    exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  set σ₀ : Simplex Y 0 := ContinuousMap.const _ x₀
  set M : Submodule R (Chain R Y 0) := (inside R 1 A).map (bd R 0)
  set L : Chain R Y 0 →ₗ[R] Chain R Y 0 :=
    LinearMap.id - (aug R 0).smulRight (single σ₀ (1 : R))
  have hle : inside R 0 A ≤ M.comap L := by
    change supported R R _ ≤ _
    rw [supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨σ, hσ, rfl⟩
    have hx : σ (stdSimplex.vertex 0) ∈ A := hσ ⟨_, rfl⟩
    obtain ⟨γ, hγ⟩ := hA x₀ hx₀ _ hx
    refine ⟨single (pathSimplex γ) 1, single_mem_supported R _ ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      exact hγ _
    · rw [bd_single_pathSimplex, ← simplex_zero_eq_const]
      simp [L, aug_single]
      rfl
  obtain ⟨w, hw, hbw⟩ := hle hc
  refine ⟨w, hw, ?_⟩
  rw [hbw]
  simp [L, haug]

/-- Push-forward of chains preserves the augmentation. -/
lemma aug_postcomp (f : C(Y, Z)) (n : ℕ) (c : Chain R Y n) :
    aug R n (postcomp R f n c) = aug R n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add]
  | single σ a => rw [postcomp_single, aug_single, aug_single]

/-- **Homotopy transfer** of reduced `H̃₀ = 0`, as in `CycleVanishing.of_homotopy`. -/
theorem ReducedZeroVanishing.of_homotopy {A : Set Y} {B : Set Z} (f : C(Y, Z)) (g : C(Z, Y))
    (hf : MapsTo f A B) (hg : MapsTo g B A) (F : C(Y × unitInterval, Y))
    (hF₀ : ∀ y, F (y, 0) = g (f y)) (hF₁ : ∀ y, F (y, 1) = y) (hF : MapsTo F (A ×ˢ univ) A)
    (h : ReducedZeroVanishing R B) : ReducedZeroVanishing R A := by
  intro c hc haug
  obtain ⟨w, hw, hbw⟩ := h (postcomp R f 0 c) (postcomp_mem_inside f hf hc)
    (by rw [aug_postcomp, haug])
  have hP := bd_prism_zero (R := R) F (f := g.comp f) (g := ContinuousMap.id Y)
    (fun y ↦ hF₀ y) (fun y ↦ hF₁ y) c
  rw [postcomp_id, ← postcomp_comp, ← hbw, postcomp_bd] at hP
  refine ⟨prism R F 0 c + postcomp R g 1 w,
    Submodule.add_mem _ (prism_mem_inside F hF hc) (postcomp_mem_inside g hg hw), ?_⟩
  rw [map_add, hP, sub_add_cancel]

/-- **Reduced Mayer–Vietoris in degree `1`**: for `U`, `V` open, the vanishing of `H₁(U)`,
`H₁(V)` and of reduced `H̃₀(U ∩ V)` gives the vanishing of `H₁(U ∪ V)`. -/
theorem CycleVanishing.union_of_reducedZeroVanishing {U V : Set Y} (hU : IsOpen U)
    (hV : IsOpen V) (h₁ : CycleVanishing R Y 0 U) (h₂ : CycleVanishing R Y 0 V)
    (h₁₂ : ReducedZeroVanishing R (U ∩ V)) : CycleVanishing R Y 0 (U ∪ V) := by
  intro z hz hbz
  set 𝒰 : Set (Set Y) := {U, V}
  have h𝒰 : ∀ W ∈ 𝒰, IsOpen W := by
    rintro W (rfl | rfl)
    · exact hU
    · exact hV
  have hz' : z ∈ inside R 1 (⋃₀ 𝒰) := by
    simpa [𝒰] using hz
  obtain ⟨a, ha, b, hb, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 1 hz')
  rw [smallChainMap_succ, hbz, map_zero, sub_zero] at hsplit
  have hab : bd R 0 a = -bd R 0 b := by
    have := congrArg (bd R 0) hsplit
    rw [map_sub, bd_bd, hbz, sub_zero, map_add] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hbaUV : bd R 0 a ∈ inside R 0 (U ∩ V) := by
    rw [inside_inter]
    refine ⟨bd_mem_inside ha, ?_⟩
    rw [hab]
    exact Submodule.neg_mem _ (bd_mem_inside hb)
  obtain ⟨d, hd, hbd⟩ := h₁₂ _ hbaUV (aug_bd_zero a)
  rw [inside_inter] at hd
  obtain ⟨eU, heU, hbeU⟩ := h₁ (a - d) (Submodule.sub_mem _ ha hd.1)
    (by rw [map_sub, hbd, sub_self])
  obtain ⟨eV, heV, hbeV⟩ := h₂ (b + d) (Submodule.add_mem _ hb hd.2)
    (by rw [map_add, hbd, hab, add_neg_cancel])
  refine ⟨smallHomotopy R 𝒰 1 z + eU + eV, ?_, ?_⟩
  · refine Submodule.add_mem _ (Submodule.add_mem _ (smallHomotopy_mem_inside_of_mem 𝒰 hz) ?_) ?_
    · exact inside_mono _ subset_union_left heU
    · exact inside_mono _ subset_union_right heV
  · rw [map_add, map_add, hbeU, hbeV]
    calc _ = bd R 1 (smallHomotopy R 𝒰 1 z) + (a + b) := by abel
      _ = z := by rw [← hsplit]; abel

end reduced

section punctured

/-- **`ℝⁿ - 0` is path-connected for `n ≥ 2`**, so its reduced `H̃₀` vanishes. -/
theorem reducedZeroVanishing_compl_zero {n : ℕ} (hn : 2 ≤ n) :
    ReducedZeroVanishing R ({0}ᶜ : Set (Fin n → ℝ)) := by
  have hrank : 1 < Module.rank ℝ (Fin n → ℝ) := by
    rw [rank_fin_fun]
    exact_mod_cast hn
  have hpc := isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : Fin n → ℝ)
  exact reducedZeroVanishing_of_joinedIn fun x hx y hy ↦ hpc.joinedIn x hx y hy

/-- **The homology of `ℝⁿ - 0` vanishes in degrees `1, …, n - 2`**: `H_{j+1}(ℝⁿ - 0; R) = 0`
for `j + 2 < n`. -/
theorem cycleVanishing_compl_zero_low :
    ∀ n j, j + 2 < n → CycleVanishing R (Fin n → ℝ) j {0}ᶜ := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [← halfAxisCompl_union]
    have hU := cycleVanishing_of_starConvex (R := R) (starConvex_halfAxisCompl n one_ne_zero)
    have hV := cycleVanishing_of_starConvex (R := R)
      (starConvex_halfAxisCompl n (neg_ne_zero.2 one_ne_zero))
    have hFmaps : MapsTo (flattenHomotopy n)
        ((halfAxisCompl n 1 ∩ halfAxisCompl n (-1)) ×ˢ univ)
        (halfAxisCompl n 1 ∩ halfAxisCompl n (-1)) := by
      rw [halfAxisCompl_inter]
      rintro ⟨x, t⟩ hp
      change Fin.init (flattenHomotopy n (x, t)) ≠ 0
      rw [flattenHomotopy_apply, Fin.init_snoc]
      exact hp.1
    have hf : MapsTo (initMap n) (halfAxisCompl n 1 ∩ halfAxisCompl n (-1)) {0}ᶜ := by
      rw [halfAxisCompl_inter]
      exact fun x hx ↦ hx
    have hg : MapsTo (snocZeroMap n) {0}ᶜ (halfAxisCompl n 1 ∩ halfAxisCompl n (-1)) := by
      rw [halfAxisCompl_inter]
      intro y hy
      change Fin.init (snocZeroMap n y) ≠ 0
      rw [snocZeroMap_apply, Fin.init_snoc]
      exact hy
    have hF₀ : ∀ x, flattenHomotopy n (x, 0) = snocZeroMap n (initMap n x) := fun x ↦ by
      rw [flattenHomotopy_apply, initMap_apply, snocZeroMap_apply, Set.Icc.coe_zero, zero_mul]
    have hF₁ : ∀ x, flattenHomotopy n (x, 1) = x := fun x ↦ by
      rw [flattenHomotopy_apply, Set.Icc.coe_one, one_mul, Fin.snoc_init_self]
    rcases j with _ | j
    · exact CycleVanishing.union_of_reducedZeroVanishing (isOpen_halfAxisCompl _ 1)
        (isOpen_halfAxisCompl _ (-1)) (hU 0) (hV 0)
        (ReducedZeroVanishing.of_homotopy (initMap n) (snocZeroMap n) hf hg (flattenHomotopy n)
          hF₀ hF₁ hFmaps (reducedZeroVanishing_compl_zero (by omega)))
    · exact CycleVanishing.union (isOpen_halfAxisCompl _ 1) (isOpen_halfAxisCompl _ (-1))
        (hU _) (hV _)
        (CycleVanishing.of_homotopy (initMap n) (snocZeroMap n) hf hg (flattenHomotopy n)
          hF₀ hF₁ hFmaps (ih j (by omega)))

/-- **Local homology of `ℝⁿ` at `0` below the top degree**: `H_{k+1}(ℝⁿ, ℝⁿ - 0; R) = 0` for
`k + 1 < n`. -/
theorem relVanishing_singleton_zero_low :
    ∀ n k, k + 1 < n → RelVanishing R (Fin n → ℝ) k {0} := by
  rintro n (_ | j) hk γ hγ
  · obtain ⟨w, -, f, hf, hγw⟩ := exists_bd_add_of_starConvex_zero (R := R)
      (starConvex_univ (0 : Fin n → ℝ)) (subset_univ ({0}ᶜ : Set (Fin n → ℝ)))
      (reducedZeroVanishing_compl_zero (by omega)) (mem_inside_univ γ) hγ
    exact ⟨w, by rw [hγw, add_sub_cancel_left]; exact hf⟩
  · obtain ⟨w, -, f, hf, hγw⟩ := exists_bd_add_of_starConvex (R := R)
      (starConvex_univ (0 : Fin n → ℝ)) (subset_univ ({0}ᶜ : Set (Fin n → ℝ))) (m := j)
      (cycleVanishing_compl_zero_low n j (by omega)) (mem_inside_univ γ) hγ
    exact ⟨w, by rw [hγw, add_sub_cancel_left]; exact hf⟩

/-- **`H_0(ℝⁿ, ℝⁿ - 0; R) = 0` for `n ≥ 1`**: every `0`-chain of `ℝⁿ` is a boundary plus a chain
lying in `ℝⁿ - 0`. -/
theorem isRelBoundary_singleton_zero_zero {n : ℕ} (hn : 1 ≤ n) (c : Chain R (Fin n → ℝ) 0) :
    IsRelBoundary R 0 {0} c := by
  set p : Fin n → ℝ := fun _ ↦ 1
  have hp : p ∈ ({0}ᶜ : Set (Fin n → ℝ)) := fun h ↦ by
    have := congrFun h ⟨0, hn⟩
    simp [p] at this
  set c' := c - single (ContinuousMap.const (stdSimplex ℝ (Fin 1)) p) (aug R 0 c)
  have haug : aug R 0 c' = 0 := by simp [c', aug_single]
  obtain ⟨w, -, hw⟩ := exists_bd_eq_of_starConvex_zero (R := R)
    (starConvex_univ (0 : Fin n → ℝ)) (mem_inside_univ c') haug
  refine ⟨w, ?_⟩
  rw [hw, sub_sub_cancel]
  exact single_const_mem_inside hp _

end punctured

end SingularChain

end MMP
