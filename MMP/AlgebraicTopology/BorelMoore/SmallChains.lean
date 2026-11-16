module

public import MMP.AlgebraicTopology.CapProduct.Neighbourhood

/-!
# Small locally finite chains for an open cover by two sets

Let `W` and `V` be open subsets covering a space `Y`. Hatcher's chain map `ρ = 1 - ∂ D - D ∂`
of the theorem of small chains, for the cover `{W, V}`, acts on locally finite chains
(`MMP.borelMooreHomology.smallChainMapLF`, with homotopy
`MMP.borelMooreHomology.smallHomotopyMap`). For every locally finite chain `c` of
`Y`, the chains `ρ c` and `D c` are locally finite, `c = ρ c + ∂ (D c) + D (∂ c)`, and every
simplex of `ρ c` lies in `W` or in `V`. Both operators are carried by the simplices of `c`: a
simplex of `ρ c` or of `D c` lies in the image of a simplex of `c`. For a cycle `z`,
`z - ρ z = ∂ (D z)`.

## Main results

* `MMP.borelMooreHomology.smallChainMapLF_small_of_union`: the simplices of `ρ c`
  lie in `W` or in `V`.
* `MMP.borelMooreHomology.eq_smallChainMapLF_add_succ`,
  `MMP.borelMooreHomology.eq_smallChainMapLF_add_zero`:
  `c = ρ c + ∂ (D c) + D (∂ c)`.
* `MMP.borelMooreHomology.sub_smallChainMapLF_eq_d_of_cycle`:
  `z - ρ z = ∂ (D z)` for a cycle `z`.
* `MMP.borelMooreHomology.exists_of_smallChainMapLF_ne_zero`,
  `MMP.borelMooreHomology.exists_of_smallHomotopyMap_ne_zero`: the simplices of
  `ρ c` and `D c` lie in images of simplices of `c`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology Opposite Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}}

/-- **Small chains for two open sets.** If `W` and `V` are open and cover `Y`, every simplex of
`ρ c` (Hatcher's chain map for the cover `{W, V}`) lies in `W` or in `V`. -/
theorem smallChainMapLF_small_of_union {W V : Set Y} (hW : IsOpen W) (hV : IsOpen V)
    (hWV : W ∪ V = univ) (n : ℕ) (c : (borelMooreChainComplex R M Y).X n)
    {τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    (hτ : (((smallChainMapLF R M {W, V}).f n).hom c).1 τ ≠ 0) :
    singularSimplexImage Y τ ⊆ W ∨ singularSimplexImage Y τ ⊆ V := by
  obtain ⟨U, hU, h⟩ := smallChainMapLF_small R M (𝒰 := {W, V})
    (by rintro U (rfl | rfl); exacts [hW, hV]) (by rw [sUnion_pair, hWV]) n c hτ
  rcases hU with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

/-- `c = ρ c + ∂ (D c) + D (∂ c)` for a locally finite chain `c` of positive degree. -/
theorem eq_smallChainMapLF_add_succ (𝒰 : Set (Set Y)) (k : ℕ)
    (c : (borelMooreChainComplex R M Y).X (k + 1)) :
    c = ((smallChainMapLF R M 𝒰).f (k + 1)).hom c +
      ((borelMooreChainComplex R M Y).d (k + 1 + 1) (k + 1)).hom
        ((smallHomotopyMap R M 𝒰 (k + 1)).hom c) +
      (smallHomotopyMap R M 𝒰 k).hom (((borelMooreChainComplex R M Y).d (k + 1) k).hom c) := by
  have h := congrArg (fun f ↦ f.hom c) (id_sub_smallChainMapLF_succ R M 𝒰 k)
  simp only [ModuleCat.hom_sub, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  rw [sub_eq_iff_eq_add] at h
  conv_lhs => rw [h]
  abel

/-- `c = ρ c + ∂ (D c)` for a locally finite chain `c` of degree `0`. -/
theorem eq_smallChainMapLF_add_zero (𝒰 : Set (Set Y)) (c : (borelMooreChainComplex R M Y).X 0) :
    c = ((smallChainMapLF R M 𝒰).f 0).hom c +
      ((borelMooreChainComplex R M Y).d 1 0).hom ((smallHomotopyMap R M 𝒰 0).hom c) := by
  have h := congrArg (fun f ↦ f.hom c) (id_sub_smallChainMapLF_zero R M 𝒰)
  simp only [ModuleCat.hom_sub, ModuleCat.hom_comp, LinearMap.sub_apply, LinearMap.comp_apply,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply] at h
  rw [sub_eq_iff_eq_add] at h
  conv_lhs => rw [h]
  exact add_comm _ _

/-- For a locally finite cycle `z`, `z - ρ z = ∂ (D z)`. -/
theorem sub_smallChainMapLF_eq_d_of_cycle (𝒰 : Set (Set Y)) {n : ℕ}
    (z : (borelMooreChainComplex R M Y).X n)
    (hz : ∀ m, m + 1 = n → (borelMooreChainComplex R M Y).d n m z = 0) :
    z - ((smallChainMapLF R M 𝒰).f n).hom z =
      ((borelMooreChainComplex R M Y).d (n + 1) n).hom ((smallHomotopyMap R M 𝒰 n).hom z) := by
  rcases n with _ | k
  · exact sub_eq_of_eq_add' (eq_smallChainMapLF_add_zero R M 𝒰 z)
  · have h := eq_smallChainMapLF_add_succ R M 𝒰 k z
    rw [show ((borelMooreChainComplex R M Y).d (k + 1) k).hom z = 0 from hz k rfl, map_zero,
      add_zero] at h
    exact sub_eq_of_eq_add' h

/-- A simplex of `ρ c` lies in the image of a simplex of `c`. -/
theorem exists_of_smallChainMapLF_ne_zero (𝒰 : Set (Set Y)) {n : ℕ}
    (c : (borelMooreChainComplex R M Y).X n) {τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)}
    (hτ : (((smallChainMapLF R M 𝒰).f n).hom c).1 τ ≠ 0) :
    ∃ σ, c.1 σ ≠ 0 ∧ singularSimplexImage Y τ ⊆ singularSimplexImage Y σ := by
  rw [smallChainMapLF_f_apply] at hτ
  obtain ⟨σ, hσ⟩ : ∃ σ, smallKernel 𝒰 n σ τ • c.1 σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ (finsum_eq_zero_of_forall_eq_zero h)
  refine ⟨σ, smul_ne_zero_right hσ, ?_⟩
  have := (isAdmissibleKernel_smallKernel 𝒰 n).image_subset σ τ (smul_ne_zero_left hσ)
  rwa [image_id] at this

/-- A simplex of `D c` lies in the image of a simplex of `c`. -/
theorem exists_of_smallHomotopyMap_ne_zero (𝒰 : Set (Set Y)) {n : ℕ}
    (c : (borelMooreChainComplex R M Y).X n) {ω : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)}
    (hω : ((smallHomotopyMap R M 𝒰 n).hom c).1 ω ≠ 0) :
    ∃ σ, c.1 σ ≠ 0 ∧ singularSimplexImage Y ω ⊆ singularSimplexImage Y σ := by
  change kernelFun (smallHomotopyKernel 𝒰 n) c.1 ω ≠ 0 at hω
  obtain ⟨σ, hσ⟩ : ∃ σ, smallHomotopyKernel 𝒰 n σ ω • c.1 σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hω (finsum_eq_zero_of_forall_eq_zero h)
  refine ⟨σ, smul_ne_zero_right hσ, ?_⟩
  have := (isAdmissibleKernel_smallHomotopyKernel 𝒰 n).image_subset σ ω (smul_ne_zero_left hσ)
  rwa [image_id] at this

end borelMooreHomology

end MMP
