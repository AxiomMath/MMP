module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Linear.Yoneda
/-!
# Singular cohomology of pairs (Fulton, §19.1)

For a topological space `Y`, a subset `A ⊆ Y`, a commutative ring `R` and an `R`-module `M`, the
singular cohomology `H^j(Y, A; M)` of the pair `(Y, A)` is the cohomology of the complex of
singular cochains of `Y` with values in `M` that vanish on singular simplices of `A`: the kernel
of the restriction `Hom_R(C_•(Y; R), M) → Hom_R(C_•(A; R), M)`. It is extended by zero to all
degrees `j : ℤ`.

Fulton writes `H^j(Y, Y - X)` for a closed subset `X ⊆ Y`, and `H^j Y = H^j(Y, ∅)`; integer
coefficients are `R = M = ℤ`, and `ℚ`, `ℤ/p` coefficients are `R = M = ℚ`, `ℤ/p` (or `R = ℤ`).

Cohomology is contravariant in pairs: a continuous map `f : Y' → Y` with `A' ⊆ f⁻¹ A` induces
`H^j(Y, A; M) → H^j(Y', A'; M)`. Two cases are Fulton's: the pullback
`f^* : H^j(Y, Y - X) → H^j(Y', Y' - f⁻¹ X)`, and, for `X ⊆ X'`, the forgetful map
`H^j(Y, Y - X) → H^j(Y, Y - X')`, in particular to `H^j Y`.

## Main definitions

* `MMP.singularCochainComplex R M`: the singular cochain complex functor.
* `MMP.relativeSingularCochainComplex R M Y A`: the cochains of the pair `(Y, A)`.
* `MMP.relativeSingularCohomology R M Y A j`: `H^j(Y, A; M)`, for `j : ℤ`.
* `MMP.relativeSingularCohomology.map`: the map induced by a map of pairs.
* `MMP.cohomologyWithSupports R M Y X j`: Fulton's `H^j(Y, Y - X)`.
* `MMP.cohomologyWithSupports.pullback`: `f^*`.
* `MMP.cohomologyWithSupports.forget`: the forgetful map, and
  `MMP.cohomologyWithSupports.toCohomology` to `H^j Y`.

## Main results

* `MMP.relativeSingularCohomology.map_id`, `map_comp`: functoriality.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VI.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite

universe u

namespace MMP

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- The singular cochain complex functor with coefficients in the `R`-module `M`:
`Y ↦ Hom_R(C_•(Y; R), M)`. -/
def singularCochainComplex : TopCat.{u}ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).op ⋙
    HomologicalComplex.opFunctor _ _ ⋙
      ((linearYoneda R (ModuleCat.{u} R)).obj M).mapHomologicalComplex _

/-- The inclusion of a subset `A ⊆ Y`, with the subspace topology, into `Y`. -/
def subspaceInclusion (Y : TopCat.{u}) (A : Set Y) : TopCat.of A ⟶ Y :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of a continuous map `f : Y' → Y` to subsets `A' ⊆ f⁻¹ A`. -/
def subspaceRestrict {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y}
    (h : A' ⊆ f ⁻¹' A) : TopCat.of A' ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun a ↦ ⟨f a, h a.2⟩, by fun_prop⟩

/-- Restricting `f` to `A' → A` and then including `A` into `Y` agrees with including `A'` into
`Y'` and then applying `f`. -/
@[reassoc]
lemma subspaceRestrict_comp_subspaceInclusion {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A' : Set Y'}
    {A : Set Y} (h : A' ⊆ f ⁻¹' A) :
    subspaceRestrict f h ≫ subspaceInclusion Y A = subspaceInclusion Y' A' ≫ f :=
  rfl

/-- The restriction of singular cochains of `Y` to singular cochains of `A ⊆ Y`. -/
def singularCochainRestriction (Y : TopCat.{u}) (A : Set Y) :
    (singularCochainComplex R M).obj (op Y) ⟶ (singularCochainComplex R M).obj (op (TopCat.of A)) :=
  (singularCochainComplex R M).map (subspaceInclusion Y A).op

/-- The singular cochain complex of the pair `(Y, A)`: cochains of `Y` vanishing on `A`, i.e. the
kernel of the restriction to `A`. -/
abbrev relativeSingularCochainComplex (Y : TopCat.{u}) (A : Set Y) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  kernel (singularCochainRestriction R M Y A)

namespace relativeSingularCochainComplex

/-- The map of relative cochain complexes induced by a map of pairs `f : (Y', A') → (Y, A)`. -/
def map {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y} (h : A' ⊆ f ⁻¹' A) :
    relativeSingularCochainComplex R M Y A ⟶ relativeSingularCochainComplex R M Y' A' :=
  kernel.lift _ (kernel.ι _ ≫ (singularCochainComplex R M).map f.op) (by
    have : (singularCochainComplex R M).map f.op ≫ singularCochainRestriction R M Y' A' =
        singularCochainRestriction R M Y A ≫ (singularCochainComplex R M).map
          (subspaceRestrict f h).op := by
      simp only [singularCochainRestriction, ← Functor.map_comp, ← op_comp,
        subspaceRestrict_comp_subspaceInclusion]
    rw [Category.assoc, this, kernel.condition_assoc, zero_comp])

/-- The induced map of relative cochain complexes is compatible with the inclusions into the
absolute cochain complexes. -/
@[reassoc (attr := simp)]
lemma map_ι {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y} (h : A' ⊆ f ⁻¹' A) :
    map R M f h ≫ kernel.ι _ = kernel.ι _ ≫ (singularCochainComplex R M).map f.op :=
  kernel.lift_ι _ _ _

/-- The identity map of pairs induces the identity on relative cochain complexes. -/
lemma map_id (Y : TopCat.{u}) (A : Set Y) :
    map R M (𝟙 Y) (A := A) (A' := A) (fun _ h ↦ h) = 𝟙 _ := by
  refine (cancel_mono (kernel.ι _)).1 ?_
  simp [map]

/-- The map of relative cochain complexes induced by a composite `g ≫ f` of maps of pairs is the
composite of the maps induced by `f` and by `g`. -/
lemma map_comp {Y'' Y' Y : TopCat.{u}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) :
    map R M (g ≫ f) (fun _ hx ↦ hf (hg hx)) = map R M f hf ≫ map R M g hg (A := A') := by
  refine (cancel_mono (kernel.ι _)).1 ?_
  simp [map, op_comp]

end relativeSingularCochainComplex

/-- The singular cohomology `H^j(Y, A; M)` of the pair `(Y, A)` with coefficients in `M`, for
`j : ℤ`: the cohomology of the relative singular cochain complex, extended by zero to negative
degrees. -/
def relativeSingularCohomology (Y : TopCat.{u}) (A : Set Y) (j : ℤ) : ModuleCat.{u} R :=
  ((relativeSingularCochainComplex R M Y A).extend ComplexShape.embeddingUpNat).homology j

namespace relativeSingularCohomology

/-- The map `H^j(Y, A; M) → H^j(Y', A'; M)` induced by a map of pairs `f : (Y', A') → (Y, A)`,
i.e. a continuous map `f : Y' → Y` with `A' ⊆ f⁻¹ A`. -/
def map {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y} (h : A' ⊆ f ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology R M Y A j ⟶ relativeSingularCohomology R M Y' A' j :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.extendMap (relativeSingularCochainComplex.map R M f h) _) j

/-- The identity map of pairs induces the identity on `H^j(Y, A; M)`. -/
lemma map_id (Y : TopCat.{u}) (A : Set Y) (j : ℤ) :
    map R M (𝟙 Y) (A := A) (A' := A) (fun _ h ↦ h) j = 𝟙 _ := by
  simp [map, relativeSingularCochainComplex.map_id, HomologicalComplex.extendMap_id,
    relativeSingularCohomology]

/-- The map on `H^j` induced by a composite `g ≫ f` of maps of pairs is the composite of the maps
induced by `f` and by `g`. -/
lemma map_comp {Y'' Y' Y : TopCat.{u}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) (j : ℤ) :
    map R M (g ≫ f) (fun _ hx ↦ hf (hg hx)) j = map R M f hf j ≫ map R M g hg (A := A') j := by
  dsimp only [map]
  rw [relativeSingularCochainComplex.map_comp, HomologicalComplex.extendMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

end relativeSingularCohomology

/-- Fulton's relative cohomology `H^j(Y, Y - X)` (§19.1), for a subset `X ⊆ Y` (Fulton takes `X`
closed): the singular cohomology of the pair `(Y, Y - X)` with coefficients in `M`. The absolute
cohomology `H^j Y` is `cohomologyWithSupports R M Y Set.univ j`, i.e. `H^j(Y, ∅)`; see
`MMP.cohomologyWithSupports.univ`. -/
abbrev cohomologyWithSupports (Y : TopCat.{u}) (X : Set Y) (j : ℤ) : ModuleCat.{u} R :=
  relativeSingularCohomology R M Y Xᶜ j

namespace cohomologyWithSupports

/-- `H^j Y = H^j(Y, Y - Y) = H^j(Y, ∅)`. -/
lemma univ (Y : TopCat.{u}) (j : ℤ) :
    cohomologyWithSupports R M Y Set.univ j = relativeSingularCohomology R M Y ∅ j := by
  simp [cohomologyWithSupports]

/-- The pullback `f^* : H^j(Y, Y - X) → H^j(Y', Y' - f⁻¹ X)` along a continuous map
`f : Y' → Y`. -/
def pullback {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (X : Set Y) (j : ℤ) :
    cohomologyWithSupports R M Y X j ⟶ cohomologyWithSupports R M Y' (f ⁻¹' X) j :=
  relativeSingularCohomology.map R M f (fun _ hx ↦ hx) j

/-- The forgetful map `H^j(Y, Y - X) → H^j(Y, Y - X')` for `X ⊆ X'`. -/
def forget (Y : TopCat.{u}) {X X' : Set Y} (h : X ⊆ X') (j : ℤ) :
    cohomologyWithSupports R M Y X j ⟶ cohomologyWithSupports R M Y X' j :=
  relativeSingularCohomology.map R M (𝟙 Y) (Set.compl_subset_compl.mpr h) j

/-- The forgetful map `H^j(Y, Y - X) → H^j Y`. -/
def toCohomology (Y : TopCat.{u}) (X : Set Y) (j : ℤ) :
    cohomologyWithSupports R M Y X j ⟶ cohomologyWithSupports R M Y Set.univ j :=
  forget R M Y (Set.subset_univ X) j

/-- The pullback along the identity of `Y` is the identity of `H^j(Y, Y - X)`. -/
lemma pullback_id (Y : TopCat.{u}) (X : Set Y) (j : ℤ) :
    pullback R M (𝟙 Y) X j = 𝟙 _ :=
  relativeSingularCohomology.map_id R M Y _ j

/-- The pullback along `g ≫ f` is the pullback along `f` followed by the pullback along `g`. -/
lemma pullback_comp {Y'' Y' Y : TopCat.{u}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) (X : Set Y) (j : ℤ) :
    pullback R M (g ≫ f) X j = pullback R M f X j ≫ pullback R M g (f ⁻¹' X) j :=
  relativeSingularCohomology.map_comp R M g f _ _ j

/-- The forgetful map for `X ⊆ X` is the identity of `H^j(Y, Y - X)`. -/
lemma forget_refl (Y : TopCat.{u}) (X : Set Y) (j : ℤ) :
    forget R M Y (subset_refl X) j = 𝟙 _ :=
  relativeSingularCohomology.map_id R M Y _ j

/-- The forgetful map for `X ⊆ X''` is the composite of the forgetful maps for `X ⊆ X'` and
`X' ⊆ X''`. -/
lemma forget_trans (Y : TopCat.{u}) {X X' X'' : Set Y} (h : X ⊆ X') (h' : X' ⊆ X'') (j : ℤ) :
    forget R M Y (h.trans h') j = forget R M Y h j ≫ forget R M Y h' j := by
  simpa [forget] using relativeSingularCohomology.map_comp R M (𝟙 Y) (𝟙 Y)
    (Set.compl_subset_compl.mpr h') (Set.compl_subset_compl.mpr h) j

section toCohomologyPullback

variable {R M}

/-- **Forgetting supports commutes with pull-back**, as maps `H^j(Y, Y - X) → H^j Y'`. -/
lemma pullback_comp_toCohomology {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (X : Set Y) (j : ℤ) :
    pullback R M f X j ≫ toCohomology R M Y' (f ⁻¹' X) j =
      toCohomology R M Y X j ≫ relativeSingularCohomology.map R M f
        (A := (Set.univᶜ : Set Y)) (A' := (Set.univᶜ : Set Y'))
        (fun y hy ↦ absurd (Set.mem_univ y) hy) j := by
  simp only [pullback, toCohomology, forget]
  rw [← relativeSingularCohomology.map_comp R M (𝟙 Y') f (A'' := (Set.univᶜ : Set Y'))
      (A' := (f ⁻¹' X)ᶜ) (A := Xᶜ) (fun y hy ↦ absurd (Set.mem_univ y) hy) (fun _ hx ↦ hx) j,
    ← relativeSingularCohomology.map_comp R M f (𝟙 Y) (A'' := (Set.univᶜ : Set Y'))
      (A' := (Set.univᶜ : Set Y)) (A := Xᶜ) (fun y hy ↦ absurd (Set.mem_univ y) hy)
      (fun y hy ↦ absurd (Set.mem_univ y) hy) j]
  simp only [Category.id_comp, Category.comp_id]

/-- **Forgetting supports commutes with pull-back**: the image in `H^j Y'` of `f^* x`, for
`x ∈ H^j(Y, Y - X)`, is the pull-back along `f` of the image of `x` in `H^j Y`. -/
lemma toCohomology_pullback_eq_map {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (X : Set Y) (j : ℤ)
    (x : cohomologyWithSupports R M Y X j) :
    (toCohomology R M Y' (f ⁻¹' X) j).hom ((pullback R M f X j).hom x) =
      (relativeSingularCohomology.map R M f
        (A := (Set.univᶜ : Set Y)) (A' := (Set.univᶜ : Set Y'))
        (fun y hy ↦ absurd (Set.mem_univ y) hy) j).hom ((toCohomology R M Y X j).hom x) := by
  rw [← ModuleCat.comp_apply, pullback_comp_toCohomology f X j, ModuleCat.comp_apply]

/-- Pull-backs of classes with the same image in `H^j Y` have the same image in `H^j Y'`. -/
lemma toCohomology_pullback_eq_of_toCohomology_eq {Y' Y : TopCat.{u}} (f : Y' ⟶ Y)
    {X X' : Set Y} {j : ℤ} {x : cohomologyWithSupports R M Y X j}
    {x' : cohomologyWithSupports R M Y X' j}
    (h : (toCohomology R M Y X j).hom x = (toCohomology R M Y X' j).hom x') :
    (toCohomology R M Y' (f ⁻¹' X) j).hom ((pullback R M f X j).hom x) =
      (toCohomology R M Y' (f ⁻¹' X') j).hom ((pullback R M f X' j).hom x') := by
  rw [toCohomology_pullback_eq_map, toCohomology_pullback_eq_map, h]

end toCohomologyPullback

end cohomologyWithSupports

end MMP
