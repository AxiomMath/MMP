module

public import MMP.AlgebraicTopology.SingularCohomology.MayerVietoris.Basic
public import MMP.AlgebraicTopology.ThomClass.Natural

/-!
# Cochains of a subspace as cochains of the ambient space

For `S ⊆ Y`, a cochain of `Y` read on the simplices lying in `S` is compared with the cochains of
the space `TopCat.of S`, on which `relCohomology` is defined. With `ι : S → Y` the inclusion,
`φ ∈ vanishing R n S` iff `ι^* φ = 0`, and every cochain `a` of `S` is `ι^*` of its extension by
zero.

## Main definitions

* `MMP.SingularCochain.subsetInclusion`: the inclusion `TopCat.of S ⟶ Y`.
* `MMP.SingularCochain.simplexCodRestrict`: a simplex of `Y` lying in `S`, as a simplex of `S`.
* `MMP.SingularCochain.extendCochainOfSubset`: the extension by zero of a cochain of `S`.

## Main results

* `MMP.SingularCochain.mem_vanishing_iff_cochainPullback_eq_zero`: a cochain of `Y` vanishes on
  `S` iff its pull-back to `S` is zero.
* `MMP.SingularCochain.sub_mem_vanishing_iff`: two cochains of `Y` agree on `S` iff their
  pull-backs to `S` are equal.
* `MMP.SingularCochain.cochainPullback_extendCochainOfSubset`: the pull-back of the extension by
  zero of `a` is `a`.
* `MMP.SingularCochain.coboundary_extendCochainOfSubset_mem_vanishing`: the extension by zero of a
  cocycle of `S` is a cocycle on `S` in the ambient sense.
-/

@[expose] public noncomputable section

open Set CategoryTheory

universe u

namespace MMP

namespace SingularCochain

open SingularChain

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- The inclusion of a subset, as a morphism of spaces. -/
abbrev subsetInclusion (S : Set Y) : TopCat.of S ⟶ Y :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- A simplex of `Y` lying in `S`, as a simplex of `S`. -/
def simplexCodRestrict (S : Set Y) {n : ℕ} (σ : Simplex Y n) (h : range σ ⊆ S) :
    Simplex (TopCat.of S) n :=
  ⟨fun t ↦ ⟨σ t, h ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩

@[simp]
lemma coe_simplexCodRestrict_apply (S : Set Y) {n : ℕ} (σ : Simplex Y n) (h : range σ ⊆ S) (t) :
    (simplexCodRestrict S σ h t : Y) = σ t :=
  rfl

/-- Composing `simplexCodRestrict S σ h` with the inclusion of `S` gives back `σ`. -/
@[simp]
lemma comp_simplexCodRestrict (S : Set Y) {n : ℕ} (σ : Simplex Y n) (h : range σ ⊆ S) :
    (subsetInclusion S).hom.comp (simplexCodRestrict S σ h) = σ :=
  rfl

/-- The image of a simplex of `S`, viewed as a simplex of `Y`, lies in `S`. -/
lemma range_comp_subsetInclusion (S : Set Y) {n : ℕ} (τ : Simplex (TopCat.of S) n) :
    range ((subsetInclusion S).hom.comp τ) ⊆ S := by
  rintro _ ⟨t, rfl⟩
  exact (τ t).2

/-- Restricting the codomain of a simplex of `S`, viewed in `Y`, gives back the simplex. -/
@[simp]
lemma simplexCodRestrict_comp (S : Set Y) {n : ℕ} (τ : Simplex (TopCat.of S) n) :
    simplexCodRestrict S ((subsetInclusion S).hom.comp τ) (range_comp_subsetInclusion S τ) = τ :=
  rfl

variable (R) in
open Classical in
/-- The extension by zero of a cochain of `S` to a cochain of `Y`. -/
def extendCochainOfSubset (S : Set Y) (n : ℕ) (a : Simplex (TopCat.of S) n → R) : Simplex Y n → R :=
  fun σ ↦ if h : range σ ⊆ S then a (simplexCodRestrict S σ h) else 0

/-- On a simplex lying in `S`, the extension by zero of `a` is `a` of the restricted simplex. -/
lemma extendCochainOfSubset_of_range_subset (S : Set Y) {n : ℕ}
    (a : Simplex (TopCat.of S) n → R) {σ : Simplex Y n} (h : range σ ⊆ S) :
    extendCochainOfSubset R S n a σ = a (simplexCodRestrict S σ h) := by
  simp [extendCochainOfSubset, h]

/-- On a simplex not lying in `S`, the extension by zero of `a` vanishes. -/
lemma extendCochainOfSubset_of_not_range_subset (S : Set Y) {n : ℕ}
    (a : Simplex (TopCat.of S) n → R) {σ : Simplex Y n} (h : ¬ range σ ⊆ S) :
    extendCochainOfSubset R S n a σ = 0 := by
  simp [extendCochainOfSubset, h]

/-- The pull-back to `S` of the extension by zero of a cochain `a` of `S` is `a`. -/
lemma cochainPullback_extendCochainOfSubset (S : Set Y) {n : ℕ} (a : Simplex (TopCat.of S) n → R) :
    cochainPullback R (subsetInclusion S) n (extendCochainOfSubset R S n a) = a := by
  ext τ
  rw [cochainPullback_apply,
    extendCochainOfSubset_of_range_subset S a (range_comp_subsetInclusion S τ)]
  rfl

/-- A cochain of `Y` vanishes on the simplices of `S` iff its pull-back to `S` is zero. -/
lemma mem_vanishing_iff_cochainPullback_eq_zero (S : Set Y) {n : ℕ} (φ : Simplex Y n → R) :
    φ ∈ vanishing R n S ↔ cochainPullback R (subsetInclusion S) n φ = 0 := by
  refine ⟨fun h ↦ funext fun τ ↦ h _ (range_comp_subsetInclusion S τ), fun h σ hσ ↦ ?_⟩
  have := congrFun h (simplexCodRestrict S σ hσ)
  rwa [cochainPullback_apply, comp_simplexCodRestrict] at this

/-- Two cochains of `Y` agree on the simplices of `S` iff their pull-backs to `S` are equal. -/
lemma sub_mem_vanishing_iff (S : Set Y) {n : ℕ} (φ ψ : Simplex Y n → R) :
    φ - ψ ∈ vanishing R n S ↔
      cochainPullback R (subsetInclusion S) n φ = cochainPullback R (subsetInclusion S) n ψ := by
  rw [mem_vanishing_iff_cochainPullback_eq_zero, map_sub, sub_eq_zero]

/-- The extension by zero of a cocycle of `S` is a cocycle on `S` in the ambient sense. -/
lemma coboundary_extendCochainOfSubset_mem_vanishing (S : Set Y) {n : ℕ}
    {a : Simplex (TopCat.of S) n → R} (ha : coboundary R n a = 0) :
    coboundary R n (extendCochainOfSubset R S n a) ∈ vanishing R (n + 1) S := by
  rw [mem_vanishing_iff_cochainPullback_eq_zero, ← coboundary_cochainPullback,
    cochainPullback_extendCochainOfSubset, ha]

/-- The pull-back to `S` of a cochain of `Y` which is a cocycle on `S` is a cocycle. -/
lemma coboundary_cochainPullback_eq_zero (S : Set Y) {n : ℕ} {φ : Simplex Y n → R}
    (hφ : coboundary R n φ ∈ vanishing R (n + 1) S) :
    coboundary R n (cochainPullback R (subsetInclusion S) n φ) = 0 := by
  rw [coboundary_cochainPullback]
  exact (mem_vanishing_iff_cochainPullback_eq_zero S _).1 hφ

end SingularCochain

end MMP
