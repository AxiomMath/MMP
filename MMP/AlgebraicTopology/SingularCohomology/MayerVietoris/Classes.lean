module

public import MMP.AlgebraicTopology.SingularCohomology.MayerVietoris.Subspace
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderDisjoint

/-!
# Mayer–Vietoris for singular cohomology, on classes

The cochain-level Mayer–Vietoris statements (a cochain of `S ⊆ Y` is a cochain of `Y` read on
the simplices lying in `S`) read on the cohomology `relCohomology R ∅ n` of the spaces
`TopCat.of S`. A cochain `φ` of `Y` whose coboundary
vanishes on the simplices of `S` gives the cocycle `subCocycle S φ = φ|_S` of `TopCat.of S`
(`ι^* φ` along the inclusion `ι`), and every cocycle of `TopCat.of S` is of this form
(`exists_subCocycle_eq`, extension by zero). Its class vanishes iff `φ` is, on the simplices of
`S`, a coboundary `δ θ` of a cochain of `Y` (`mk_subCocycle_eq_zero_iff_succ`), resp. iff `φ`
vanishes there in degree `0` (`mk_subCocycle_eq_zero_iff_zero`).

For open `A`, `B` with `A ∪ B = Y`, with `I = A ∩ B`:

* (exactness at `H^n A ⊕ H^n B`) cocycles on `A` and on `B` whose classes agree on `I` glue to a
  cocycle of `Y` (`exists_glue_mk_succ`, `exists_glue_mk_zero`);
* (exactness at `H^{n+1} Y`) a cocycle of `Y` whose classes on `A` and `B` vanish is cohomologous
  to `mvCoboundary e` for a cocycle `e` on `I` (`exists_mk_eq_mk_mvCoboundary`); in degree `0`
  it is `0` (`eq_zero_of_mk_subCocycle_eq_zero`);
* (exactness at `H^n I`) `mvCoboundary e` is a coboundary when the class of `e` on `I` is that of
  `a - b` for cocycles `a` on `A`, `b` on `B` (`mk_mvCoboundary_eq_zero_of_sub_mem`,
  `mk_mvCoboundary_eq_zero_succ`).

## Main definitions

* `MMP.PoincareAlexander.subCocycle`: the cocycle `φ|_S` of `TopCat.of S`.
* `MMP.PoincareAlexander.ofCocycle`: the cocycle of `Y` given by a cochain with zero coboundary.
-/

@[expose] public noncomputable section

open Set

universe u

namespace MMP

namespace PoincareAlexander

open SingularChain SingularCochain

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

variable (R) in
/-- The cocycle `φ|_S = ι^* φ` of `TopCat.of S` of a cochain `φ` of `Y` whose coboundary vanishes
on the simplices of `S`. -/
def subCocycle (S : Set Y) {n : ℕ} (φ : Simplex Y n → R)
    (hφ : coboundary R n φ ∈ vanishing R (n + 1) S) :
    relCocycles R (∅ : Set (TopCat.of S)) n :=
  ⟨cochainPullback R (subsetInclusion S) n φ, mem_vanishing_empty _,
    LinearMap.mem_ker.2 (coboundary_cochainPullback_eq_zero S hφ)⟩

/-- The underlying cochain of `subCocycle R S φ hφ` is the pullback of `φ` along the inclusion
of `S`. -/
@[simp]
lemma subCocycle_coe (S : Set Y) {n : ℕ} (φ : Simplex Y n → R)
    (hφ : coboundary R n φ ∈ vanishing R (n + 1) S) :
    (subCocycle R S φ hφ).1 = cochainPullback R (subsetInclusion S) n φ :=
  rfl

/-- Restriction to `S` commutes with subtraction of cochains. -/
lemma subCocycle_sub (S : Set Y) {n : ℕ} {φ ψ : Simplex Y n → R}
    (hφ : coboundary R n φ ∈ vanishing R (n + 1) S)
    (hψ : coboundary R n ψ ∈ vanishing R (n + 1) S) :
    subCocycle R S (φ - ψ) (by simpa only [map_sub] using Submodule.sub_mem _ hφ hψ) =
      subCocycle R S φ hφ - subCocycle R S ψ hψ :=
  Subtype.ext (map_sub _ _ _)

/-- Two cochains of `Y` which agree on the simplices of `S` have the same restriction to `S`. -/
lemma subCocycle_congr (S : Set Y) {n : ℕ} {φ ψ : Simplex Y n → R}
    (hφ : coboundary R n φ ∈ vanishing R (n + 1) S)
    (hψ : coboundary R n ψ ∈ vanishing R (n + 1) S) (h : φ - ψ ∈ vanishing R n S) :
    subCocycle R S φ hφ = subCocycle R S ψ hψ :=
  Subtype.ext ((sub_mem_vanishing_iff S φ ψ).1 h)

/-- Every cocycle of `TopCat.of S` is the restriction of a cochain of `Y` (its extension by
zero). -/
lemma exists_subCocycle_eq (S : Set Y) {n : ℕ} (a : relCocycles R (∅ : Set (TopCat.of S)) n) :
    ∃ (φ : Simplex Y n → R) (hφ : coboundary R n φ ∈ vanishing R (n + 1) S),
      subCocycle R S φ hφ = a :=
  ⟨extendCochainOfSubset R S n a.1,
    coboundary_extendCochainOfSubset_mem_vanishing S (LinearMap.mem_ker.1 a.2.2),
    Subtype.ext (cochainPullback_extendCochainOfSubset S a.1)⟩

/-- The class of a `(k + 1)`-cocycle `φ` of `Z` vanishes iff `φ = δ ψ` for a `k`-cochain `ψ`. -/
lemma mk_eq_zero_iff_succ {Z : TopCat.{u}} {k : ℕ} (φ : relCocycles R (∅ : Set Z) (k + 1)) :
    (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Z) (k + 1)) = 0 ↔
      ∃ ψ : Simplex Z k → R, coboundary R k ψ = φ.1 := by
  rw [Submodule.Quotient.mk_eq_zero]
  change φ.1 ∈ (vanishing R k (∅ : Set Z)).map (coboundary R k) ↔ _
  exact ⟨fun ⟨ψ, _, hψ⟩ ↦ ⟨ψ, hψ⟩, fun ⟨ψ, hψ⟩ ↦ ⟨ψ, mem_vanishing_empty _, hψ⟩⟩

/-- The class of a `0`-cocycle `φ` of `Z` vanishes iff `φ = 0`. -/
lemma mk_eq_zero_iff_zero {Z : TopCat.{u}} (φ : relCocycles R (∅ : Set Z) 0) :
    (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Z) 0) = 0 ↔ φ.1 = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  change φ.1 ∈ (⊥ : Submodule R (Simplex Z 0 → R)) ↔ _
  exact Submodule.mem_bot R

/-- The class of `φ|_S` vanishes iff `φ` is a coboundary on the simplices of `S`. -/
lemma mk_subCocycle_eq_zero_iff_succ (S : Set Y) {k : ℕ} (φ : Simplex Y (k + 1) → R)
    (hφ : coboundary R (k + 1) φ ∈ vanishing R (k + 2) S) :
    (Submodule.Quotient.mk (subCocycle R S φ hφ) :
        relCohomology R (∅ : Set (TopCat.of S)) (k + 1)) = 0 ↔
      ∃ θ : Simplex Y k → R, φ - coboundary R k θ ∈ vanishing R (k + 1) S := by
  rw [mk_eq_zero_iff_succ, subCocycle_coe]
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨extendCochainOfSubset R S k ψ, ?_⟩
    rw [sub_mem_vanishing_iff, ← coboundary_cochainPullback,
      cochainPullback_extendCochainOfSubset, hψ]
  · rintro ⟨θ, hθ⟩
    refine ⟨cochainPullback R (subsetInclusion S) k θ, ?_⟩
    rw [coboundary_cochainPullback, ← (sub_mem_vanishing_iff S _ _).1 hθ]

/-- In degree `0`, the class of `φ|_S` vanishes iff `φ` vanishes on the simplices of `S`. -/
lemma mk_subCocycle_eq_zero_iff_zero (S : Set Y) (φ : Simplex Y 0 → R)
    (hφ : coboundary R 0 φ ∈ vanishing R 1 S) :
    (Submodule.Quotient.mk (subCocycle R S φ hφ) :
        relCohomology R (∅ : Set (TopCat.of S)) 0) = 0 ↔ φ ∈ vanishing R 0 S := by
  rw [mk_eq_zero_iff_zero, subCocycle_coe, mem_vanishing_iff_cochainPullback_eq_zero]

/-- The classes of `φ|_S` and `ψ|_S` agree iff `φ - ψ` is a coboundary on the simplices of `S`. -/
lemma mk_subCocycle_eq_mk_iff_succ (S : Set Y) {k : ℕ} {φ ψ : Simplex Y (k + 1) → R}
    (hφ : coboundary R (k + 1) φ ∈ vanishing R (k + 2) S)
    (hψ : coboundary R (k + 1) ψ ∈ vanishing R (k + 2) S) :
    (Submodule.Quotient.mk (subCocycle R S φ hφ) :
        relCohomology R (∅ : Set (TopCat.of S)) (k + 1)) = Submodule.Quotient.mk
          (subCocycle R S ψ hψ) ↔
      ∃ θ : Simplex Y k → R, φ - ψ - coboundary R k θ ∈ vanishing R (k + 1) S := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, ← subCocycle_sub,
    mk_subCocycle_eq_zero_iff_succ]

/-- In degree `0`, the classes of `φ|_S` and `ψ|_S` agree iff `φ` and `ψ` agree on the simplices
of `S`. -/
lemma mk_subCocycle_eq_mk_iff_zero (S : Set Y) {φ ψ : Simplex Y 0 → R}
    (hφ : coboundary R 0 φ ∈ vanishing R 1 S) (hψ : coboundary R 0 ψ ∈ vanishing R 1 S) :
    (Submodule.Quotient.mk (subCocycle R S φ hφ) :
        relCohomology R (∅ : Set (TopCat.of S)) 0) = Submodule.Quotient.mk
          (subCocycle R S ψ hψ) ↔ φ - ψ ∈ vanishing R 0 S := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, ← subCocycle_sub,
    mk_subCocycle_eq_zero_iff_zero]

section mayerVietoris

variable {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = univ)

/-- A cocycle of `Y` is a cocycle on every subset. -/
lemma coboundary_mem_vanishing_of_cocycle (S : Set Y) {n : ℕ} (φ : relCocycles R (∅ : Set Y) n) :
    coboundary R n φ.1 ∈ vanishing R (n + 1) S := by
  rw [LinearMap.mem_ker.1 φ.2.2]
  exact Submodule.zero_mem _

/-- The cocycle of `Y` given by a cochain which is a cocycle everywhere. -/
def ofCocycle {n : ℕ} (φ : Simplex Y n → R) (hφ : coboundary R n φ = 0) :
    relCocycles R (∅ : Set Y) n :=
  ⟨φ, mem_vanishing_empty _, LinearMap.mem_ker.2 hφ⟩

/-- The underlying cochain of `ofCocycle φ hφ` is `φ`. -/
@[simp]
lemma ofCocycle_coe {n : ℕ} (φ : Simplex Y n → R) (hφ : coboundary R n φ = 0) :
    (ofCocycle φ hφ).1 = φ :=
  rfl

include hA hB hAB in
/-- **Exactness at `H^{k+1} A ⊕ H^{k+1} B`, on classes.** Cocycles on `A` and on `B` whose classes
agree on `A ∩ B` are, up to cohomology, the restrictions of a single cocycle of `Y`. -/
theorem exists_glue_mk_succ {k : ℕ} {a b : Simplex Y (k + 1) → R}
    (ha : coboundary R (k + 1) a ∈ vanishing R (k + 2) A)
    (hb : coboundary R (k + 1) b ∈ vanishing R (k + 2) B)
    (hab : (Submodule.Quotient.mk (subCocycle R (A ∩ B) a (vanishing_anti inter_subset_left ha)) :
        relCohomology R (∅ : Set (TopCat.of (A ∩ B : Set Y))) (k + 1)) =
      Submodule.Quotient.mk (subCocycle R (A ∩ B) b (vanishing_anti inter_subset_right hb))) :
    ∃ φ : relCocycles R (∅ : Set Y) (k + 1),
      (Submodule.Quotient.mk (subCocycle R A φ.1 (coboundary_mem_vanishing_of_cocycle A φ)) :
          relCohomology R (∅ : Set (TopCat.of A)) (k + 1)) = Submodule.Quotient.mk
            (subCocycle R A a ha) ∧
      (Submodule.Quotient.mk (subCocycle R B φ.1 (coboundary_mem_vanishing_of_cocycle B φ)) :
          relCohomology R (∅ : Set (TopCat.of B)) (k + 1)) = Submodule.Quotient.mk
            (subCocycle R B b hb) := by
  obtain ⟨γ, hγ⟩ := (mk_subCocycle_eq_mk_iff_succ _ _ _).1 hab
  obtain ⟨c, hc, hcA, η, hcB⟩ := exists_glue_succ hA hB hAB ha hb γ hγ
  exact ⟨ofCocycle c hc, (mk_subCocycle_eq_mk_iff_succ _ _ _).2 ⟨0, by rwa [map_zero, sub_zero]⟩,
    (mk_subCocycle_eq_mk_iff_succ _ _ _).2 ⟨η, hcB⟩⟩

include hA hB hAB in
/-- **Exactness at `H^0 A ⊕ H^0 B`, on classes.** `0`-cocycles on `A` and on `B` whose classes
agree on `A ∩ B` are, up to cohomology, the restrictions of a single `0`-cocycle of `Y`. -/
theorem exists_glue_mk_zero {a b : Simplex Y 0 → R}
    (ha : coboundary R 0 a ∈ vanishing R 1 A) (hb : coboundary R 0 b ∈ vanishing R 1 B)
    (hab : (Submodule.Quotient.mk (subCocycle R (A ∩ B) a (vanishing_anti inter_subset_left ha)) :
        relCohomology R (∅ : Set (TopCat.of (A ∩ B : Set Y))) 0) =
      Submodule.Quotient.mk (subCocycle R (A ∩ B) b (vanishing_anti inter_subset_right hb))) :
    ∃ φ : relCocycles R (∅ : Set Y) 0,
      (Submodule.Quotient.mk (subCocycle R A φ.1 (coboundary_mem_vanishing_of_cocycle A φ)) :
          relCohomology R (∅ : Set (TopCat.of A)) 0) = Submodule.Quotient.mk
            (subCocycle R A a ha) ∧
      (Submodule.Quotient.mk (subCocycle R B φ.1 (coboundary_mem_vanishing_of_cocycle B φ)) :
          relCohomology R (∅ : Set (TopCat.of B)) 0) = Submodule.Quotient.mk
            (subCocycle R B b hb) := by
  obtain ⟨c, hc, hcA, hcB⟩ := exists_glue_zero hA hB hAB ha hb
    ((mk_subCocycle_eq_mk_iff_zero _ _ _).1 hab)
  exact ⟨ofCocycle c hc, (mk_subCocycle_eq_mk_iff_zero _ _ _).2 hcA,
    (mk_subCocycle_eq_mk_iff_zero _ _ _).2 hcB⟩

include hA hB hAB in
/-- **Exactness at `H^{k+1} Y`, on classes.** A cocycle of `Y` whose classes on `A` and on `B`
vanish is cohomologous to `mvCoboundary e` for a cochain `e` which is a cocycle on `A ∩ B`. -/
theorem exists_mk_eq_mk_mvCoboundary {k : ℕ} (φ : relCocycles R (∅ : Set Y) (k + 1))
    (hφA : (Submodule.Quotient.mk (subCocycle R A φ.1 (coboundary_mem_vanishing_of_cocycle A φ)) :
      relCohomology R (∅ : Set (TopCat.of A)) (k + 1)) = 0)
    (hφB : (Submodule.Quotient.mk (subCocycle R B φ.1 (coboundary_mem_vanishing_of_cocycle B φ)) :
      relCohomology R (∅ : Set (TopCat.of B)) (k + 1)) = 0) :
    ∃ (e : Simplex Y k → R) (he : coboundary R k e ∈ vanishing R (k + 1) (A ∩ B)),
      (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Y) (k + 1)) =
        Submodule.Quotient.mk (ofCocycle (mvCoboundary R A B k e)
          (coboundary_mvCoboundary hA hB hAB he)) := by
  obtain ⟨α, hα⟩ := (mk_subCocycle_eq_zero_iff_succ _ _ _).1 hφA
  obtain ⟨β, hβ⟩ := (mk_subCocycle_eq_zero_iff_succ _ _ _).1 hφB
  have he : coboundary R k (α - β) ∈ vanishing R (k + 1) (A ∩ B) := by
    have := Submodule.sub_mem _ (vanishing_anti inter_subset_right hβ)
      (vanishing_anti inter_subset_left hα)
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  obtain ⟨η, hη⟩ := exists_sub_mvCoboundary_eq_coboundary hA hB hAB
    (LinearMap.mem_ker.1 φ.2.2) α β hα hβ
  refine ⟨α - β, he, ?_⟩
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_iff_succ]
  exact ⟨η, hη.symm⟩

include hA hB hAB in
/-- **Exactness at `H^0 Y`, on classes.** A `0`-cocycle of `Y` whose classes on `A` and on `B`
vanish is `0`. -/
theorem eq_zero_of_mk_subCocycle_eq_zero (φ : relCocycles R (∅ : Set Y) 0)
    (hφA : (Submodule.Quotient.mk (subCocycle R A φ.1 (coboundary_mem_vanishing_of_cocycle A φ)) :
      relCohomology R (∅ : Set (TopCat.of A)) 0) = 0)
    (hφB : (Submodule.Quotient.mk (subCocycle R B φ.1 (coboundary_mem_vanishing_of_cocycle B φ)) :
      relCohomology R (∅ : Set (TopCat.of B)) 0) = 0) : φ = 0 :=
  Subtype.ext (eq_zero_of_small_zero hA hB hAB (LinearMap.mem_ker.1 φ.2.2)
    ⟨(mk_subCocycle_eq_zero_iff_zero _ _ _).1 hφA, (mk_subCocycle_eq_zero_iff_zero _ _ _).1 hφB⟩)

include hA hB hAB in
/-- **Exactness at `H^k (A ∩ B)`, on classes.** If `e = a - b` on `A ∩ B` for
cocycles `a` on `A` and `b` on `B`, then `mvCoboundary e` is a coboundary. -/
theorem mk_mvCoboundary_eq_zero_of_sub_mem {k : ℕ} {e a b : Simplex Y k → R}
    (he : coboundary R k e ∈ vanishing R (k + 1) (A ∩ B))
    (ha : coboundary R k a ∈ vanishing R (k + 1) A) (hb : coboundary R k b ∈ vanishing R (k + 1) B)
    (hab : e - (a - b) ∈ vanishing R k (A ∩ B)) :
    (Submodule.Quotient.mk (ofCocycle (mvCoboundary R A B k e)
        (coboundary_mvCoboundary hA hB hAB he)) : relCohomology R (∅ : Set Y) (k + 1)) = 0 := by
  rw [mk_eq_zero_iff_succ, ofCocycle_coe]
  obtain ⟨η, hη⟩ := exists_mvCoboundary_sub_eq_coboundary hA hB hAB ha hb
  exact ⟨η, by rw [← hη, mvCoboundary_congr hab]⟩

include hA hB hAB in
/-- **Exactness at `H^{k+1} (A ∩ B)`, on classes.** If `e = a - b + δ γ` on `A ∩ B` for cocycles
`a` on `A` and `b` on `B`, then `mvCoboundary e` is a coboundary. -/
theorem mk_mvCoboundary_eq_zero_succ {k : ℕ} {e a b : Simplex Y (k + 1) → R}
    (he : coboundary R (k + 1) e ∈ vanishing R (k + 2) (A ∩ B))
    (ha : coboundary R (k + 1) a ∈ vanishing R (k + 2) A)
    (hb : coboundary R (k + 1) b ∈ vanishing R (k + 2) B) (γ : Simplex Y k → R)
    (hab : e - (a - b) - coboundary R k γ ∈ vanishing R (k + 1) (A ∩ B)) :
    (Submodule.Quotient.mk (ofCocycle (mvCoboundary R A B (k + 1) e)
        (coboundary_mvCoboundary hA hB hAB he)) : relCohomology R (∅ : Set Y) (k + 2)) = 0 := by
  rw [mk_eq_zero_iff_succ, ofCocycle_coe]
  obtain ⟨η, hη⟩ := exists_mvCoboundary_sub_eq_coboundary hA hB hAB ha hb
  obtain ⟨η', hη'⟩ := exists_mvCoboundary_eq_coboundary hA hB hAB γ (e := e - (a - b)) hab
  exact ⟨η + η', by rw [map_add, ← hη, ← hη', ← map_add, add_sub_cancel]⟩

end mayerVietoris

end PoincareAlexander

end MMP
