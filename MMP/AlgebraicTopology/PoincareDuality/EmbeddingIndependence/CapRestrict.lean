module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Disjoint
public import MMP.AlgebraicTopology.CapProduct.RestrictionCycles

/-!
# The cap product commutes with restriction to an open set, on classes

For an open subset `U` of a Hausdorff space `Y`, an absolute `p`-cocycle `φ` and a locally finite
`n`-cycle `z` of `Y` (`p + q = n`), `[φ|_U] ∩ [z|_U] = [(φ ∩ z)|_U]` in `H_q U`: the chain-level
statement `exists_d_eq_restrictChainMap_capChain_sub` (the two differ by a boundary) read on
classes. This is the naturality of the duality maps of Bredon's induction with respect to
restriction (item 4 of the plan for `lem_ext_c19_borel_moore_independent`).
## Main results

* `MMP.PoincareAlexander.capHomQ_pullCoc_resCycOpen`.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

open MMP

namespace PoincareAlexander

open MMP.PoincareAlexander

open SingularChain SingularCochain LocallyFiniteChain BorelMooreCross BorelMooreCap
  borelMooreHomology

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y]

variable (R) in
/-- The cycle `φ ∩ z`. -/
def capCycle {p q n : ℕ} (h : p + q = n) (φ : relCocycles R (∅ : Set Y) p)
    (z : Cyc (R := R) Y n) : Cyc (R := R) Y q :=
  ⟨capChain R p q n h φ.1 z.1, capChain_mem_cyc _ p q n h φ z⟩

/-- **The cap product commutes with restriction to an open set**:
`[φ|_U] ∩ [z|_U] = [(φ ∩ z)|_U]` in `H_q U`. -/
theorem capHomQ_pullCoc_resCycOpen (U : TopologicalSpace.Opens Y) {p q n : ℕ} (h : p + q = n)
    (φ : relCocycles R (∅ : Set Y) p) (z : Cyc (R := R) Y n) :
    capHomQ R (∅ : Set (TopCat.of U)) p q n h (Submodule.Quotient.mk (pullCoc R (inclHom U) φ))
        (Submodule.Quotient.mk (resCycOpen R U z)) =
      Submodule.Quotient.mk (resCycOpen R U (capCycle R h φ z)) := by
  rw [capHomQ_mk]
  obtain ⟨u, hu, -⟩ := exists_d_eq_restrictChainMap_capChain_sub (U := U) p q n h
    (A := (∅ : Set Y)) φ.2.2 φ.2.1 z
  refine (mk_eq_mk_iff_exists _ _).2 ⟨-u, ?_⟩
  rw [map_neg, hu, neg_sub]
  rfl

end PoincareAlexander

end MMP
