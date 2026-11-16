module

public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Basic
public import MMP.AlgebraicTopology.OrientationClass.CupCompositeNaturality
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision

/-!
# The Gysin map of a tubular neighbourhood

Let `E → B` be a complex topological vector bundle of rank `r`, with Thom class
`u_E ∈ H^{2r}(E, E - 0_E; R)` (`MMP.ThomClass.thomClass`), and let
`φ : E → Y` be a *tubular neighbourhood* of a closed set `Z ⊆ Y`: an open embedding carrying the
zero section onto `Z`. Restriction along `φ` identifies `H^*(Y, Y - Z)` with `H^*(E, E - 0_E)`
(excision for the open set `φ(E) ⊇ Z`, and invariance under the homeomorphism `E ≅ φ(E)`). The
*Gysin map* is
`φ_! : H^k(B) → H^{k+2r}(Y, Y - Z) → H^{k+2r}(Y)`, `a ↦ (φ^*)⁻¹ (π^* a ∪ u_E)`,
the Thom isomorphism followed by extension by zero and forgetting supports. For the exceptional
divisor `j : R ↪ V'` of a blowup, with the normal disk bundle as tubular neighbourhood, this is
the Gysin map `H^{k-2}(R) → H^k(V')` of the normal line.

Its two basic properties: restricted to `Z` along `φ ∘ 0_E` it is the cup product with the Euler
class `e(E) = 0_E^* u_E` (the self-intersection formula), and it vanishes on `Y - Z`.

Neither property uses the bundle structure: they hold for any open embedding `φ : W → Y` whose
image contains `Z`, any map `ρ : W → B` with a section `s`, and any class `u ∈ H^n(W, W - φ⁻¹ Z)`,
the Gysin map being `a ↦ (φ^*)⁻¹ (ρ^* a ∪ u)` and its restriction along `s ≫ φ` being
`a ∪ s^* u`. In particular a closed set `Z ⊆ Y` with a retraction `r : U → Z` of an open
neighbourhood and a class `u ∈ H^n(Y, Y - Z)` has a Gysin map `H^k(Z) → H^{k+n}(Y)` whose
restriction to `Z` is the cup product with `u|_Z`. For the exceptional divisor `R` of a blowup,
`u` is the orientation class of the divisor and `u|_R` the first Chern class of its normal line
bundle.

## Main definitions

* `MMP.Topology.openEmbeddingPullbackIso`: `H^j(Y, Y - X) ≅ H^j(Y', Y' - φ⁻¹ X)` for an open
  embedding `φ : Y' → Y` whose image contains the closed set `X`.
* `MMP.Topology.eulerClass`: the Euler class `e(E) ∈ H^{2r}(B)`.
* `MMP.Topology.thomCup`: `a ↦ π^* a ∪ u_E`, `H^k(B) → H^{k+2r}(E, E - T)`.
* `MMP.Topology.gysinWithSupports`, `MMP.Topology.gysin`: the Gysin map
  `H^k(B) → H^{k+2r}(Y, Y - Z)`, resp. `H^k(B) → H^{k+2r}(Y)`.
* `MMP.Topology.cupPullback`: `a ↦ ρ^* a ∪ u`, `H^k(B) → H^{k+n}(W, W - T)`.
* `MMP.Topology.retractionGysinWithSupports`, `MMP.Topology.retractionGysin`: the Gysin map
  `H^k(B) → H^{k+n}(Y, Y - Z)`, resp. `H^k(B) → H^{k+n}(Y)`, of `φ`, `ρ` and `u`.

## Main results

* `MMP.Topology.isIso_pullback_of_isOpenEmbedding`: excision along an open embedding.
* `MMP.Topology.pullback_gysin`: `(φ ∘ 0_E)^* (φ_! a) = a ∪ e(E)`.
* `MMP.Topology.pullback_compl_gysin`: `φ_! a` restricts to zero on `Y - Z`.
* `MMP.Topology.pullback_retractionGysin`: `(s ≫ φ)^* (φ_! a) = a ∪ s^* u`.
* `MMP.Topology.pullback_retractionGysin_subspaceInclusion`: for a retraction `r : U → Z` of an
  open neighbourhood and `u ∈ H^n(Y, Y - Z)`, `(φ_! a)|_Z = a ∪ u|_Z`.
* `MMP.Topology.pullback_compl_retractionGysin`: `φ_! a` restricts to zero on `Y - Z`.
* `MMP.Topology.gysin_eq_retractionGysin`: the Gysin map of a tubular neighbourhood is that of
  `ρ = π` and `u = u_E`.

## Implementation notes

Cohomology is singular cohomology with coefficients in a commutative ring `R`, as
`MMP.cohomologyWithSupports`; the rational cohomology `H^q(X; ℚ)` of a space is
the case `R = ℚ`, `X = univ`. Degrees are integers; the Gysin map raises the degree by
`2 * Module.finrank ℂ F`. The tubular neighbourhood is part of the data: `φ` is an open
embedding of the total space of `E` with `φ (range 0_E) = Z`.

## References

* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–11.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §4.D.
-/

@[expose] public noncomputable section

open CategoryTheory Set Bundle Topology MMP MMP.cohomologyWithSupports

universe u

namespace MMP.Topology

variable (R : Type u) [CommRing R]

section map

/-- Restriction maps of relative singular cohomology along equal maps agree, whatever the proofs
of the subset conditions. -/
lemma relativeSingularCohomology_map_congr {Y' Y : TopCat.{u}} {f f' : Y' ⟶ Y} (hff' : f = f')
    {A' : Set Y'} {A : Set Y} (h : A' ⊆ f ⁻¹' A) (h' : A' ⊆ f' ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map R (ModuleCat.of R R) f h j =
      relativeSingularCohomology.map R (ModuleCat.of R R) f' h' j := by
  subst hff'
  rfl

/-- Restriction along `f` followed by restriction along `g` is restriction along `g ≫ f`, applied
to a class `x ∈ H^j(Y, A)`. -/
lemma relativeSingularCohomology_map_map_apply {Y'' Y' Y : TopCat.{u}} (g : Y'' ⟶ Y')
    (f : Y' ⟶ Y) {A'' : Set Y''} {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A')
    (hf : A' ⊆ f ⁻¹' A) (h : A'' ⊆ (g ≫ f) ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f hf j).hom x) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (g ≫ f) h j).hom x :=
  (congrArg (fun m ↦ m.hom x) (relativeSingularCohomology.map_comp R _ g f hg hf j)).symm

/-- Restriction along an isomorphism `f : Y' ≅ Y` is an isomorphism
`H^j(Y, A) ≅ H^j(Y', f⁻¹ A)`. -/
lemma isIso_relativeSingularCohomology_map_of_isIso {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) [IsIso f]
    (A : Set Y) (j : ℤ) :
    IsIso (relativeSingularCohomology.map R (ModuleCat.of R R) f (A' := f ⁻¹' A) Subset.rfl j) := by
  have hA : A ⊆ (inv f) ⁻¹' (f ⁻¹' A) := fun y hy ↦ by
    change (inv f ≫ f) y ∈ A
    rwa [IsIso.inv_hom_id]
  refine ⟨⟨relativeSingularCohomology.map R (ModuleCat.of R R) (inv f) hA j, ?_, ?_⟩⟩
  · exact (relativeSingularCohomology.map_comp R _ (inv f) f hA Subset.rfl j).symm.trans <|
      (relativeSingularCohomology_map_congr R (IsIso.inv_hom_id f) _ (fun _ h ↦ h) j).trans
        (relativeSingularCohomology.map_id R _ Y A j)
  · exact (relativeSingularCohomology.map_comp R _ f (inv f) Subset.rfl hA j).symm.trans <|
      (relativeSingularCohomology_map_congr R (IsIso.hom_inv_id f) _ (fun _ h ↦ h) j).trans
        (relativeSingularCohomology.map_id R _ Y' _ j)

/-- **Excision along an open embedding.** For an open embedding `φ : Y' → Y` whose image contains
the closed set `X`, restriction `H^j(Y, Y - X) → H^j(Y', Y' - φ⁻¹ X)` is an isomorphism. -/
theorem isIso_pullback_of_isOpenEmbedding {Y' Y : TopCat.{u}} (φ : Y' ⟶ Y)
    (hφ : IsOpenEmbedding φ) {X : Set Y} (hX : IsClosed X) (hXφ : X ⊆ range φ) (j : ℤ) :
    IsIso (pullback R (ModuleCat.of R R) φ X j) := by
  let e : Y' ≅ TopCat.of (range φ) := TopCat.isoOfHomeo hφ.isEmbedding.toHomeomorph
  have key : pullback R (ModuleCat.of R R) φ X j =
      pullback R (ModuleCat.of R R) (subspaceInclusion Y (range φ)) X j ≫
        relativeSingularCohomology.map R (ModuleCat.of R R) e.hom
          (A' := e.hom ⁻¹' (subspaceInclusion Y (range φ) ⁻¹' X)ᶜ) Subset.rfl j :=
    (relativeSingularCohomology_map_congr R
      (f' := e.hom ≫ subspaceInclusion Y (range φ)) (by ext; rfl) _ (fun _ hx ↦ hx) j).trans
      (relativeSingularCohomology.map_comp R _ e.hom (subspaceInclusion Y _) _ _ j)
  rw [key]
  exact IsIso.comp_isIso' (isIso_pullback_subspaceInclusion R hφ.isOpen_range hX hXφ j)
    (isIso_relativeSingularCohomology_map_of_isIso R e.hom
      (subspaceInclusion Y (range φ) ⁻¹' X)ᶜ j)

/-- For an open embedding `φ : Y' → Y` whose image contains the closed set `X`, restriction along
`φ` identifies `H^j(Y, Y - X)` with `H^j(Y', Y' - φ⁻¹ X)` (excision and homeomorphism
invariance). -/
def openEmbeddingPullbackIso {Y' Y : TopCat.{u}} (φ : Y' ⟶ Y) (hφ : IsOpenEmbedding φ)
    {X : Set Y} (hX : IsClosed X) (hXφ : X ⊆ range φ) (j : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j ≅
      cohomologyWithSupports R (ModuleCat.of R R) Y' (φ ⁻¹' X) j :=
  haveI := isIso_pullback_of_isOpenEmbedding R φ hφ hX hXφ j
  asIso (cohomologyWithSupports.pullback R (ModuleCat.of R R) φ X j)

/-- The forward map of `openEmbeddingPullbackIso` is restriction along `φ`. -/
@[simp]
lemma openEmbeddingPullbackIso_hom {Y' Y : TopCat.{u}} (φ : Y' ⟶ Y) (hφ : IsOpenEmbedding φ)
    {X : Set Y} (hX : IsClosed X) (hXφ : X ⊆ range φ) (j : ℤ) :
    (openEmbeddingPullbackIso R φ hφ hX hXφ j).hom =
      cohomologyWithSupports.pullback R (ModuleCat.of R R) φ X j :=
  rfl

/-- For a commutative square `g ≫ f = g' ≫ f'`, restricting a class along `f` then `g` agrees with
restricting it along `f'` then `g'`. -/
lemma relativeSingularCohomology_map_map_apply_eq {Y'' Y₁ Y₂ Y : TopCat.{u}} (g : Y'' ⟶ Y₁)
    (f : Y₁ ⟶ Y) (g' : Y'' ⟶ Y₂) (f' : Y₂ ⟶ Y) (hgf : g ≫ f = g' ≫ f') {A'' : Set Y''}
    {A₁ : Set Y₁} {A₂ : Set Y₂} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A₁) (hf : A₁ ⊆ f ⁻¹' A)
    (hg' : A'' ⊆ g' ⁻¹' A₂) (hf' : A₂ ⊆ f' ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f hf j).hom x) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) g' hg' j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f' hf' j).hom x) := by
  have h : A'' ⊆ (g ≫ f) ⁻¹' A := fun _ hx ↦ hf (hg hx)
  have h' : A'' ⊆ (g' ≫ f') ⁻¹' A := fun _ hx ↦ hf' (hg' hx)
  rw [relativeSingularCohomology_map_map_apply R g f hg hf h,
    relativeSingularCohomology_map_map_apply R g' f' hg' hf' h']
  exact congrArg (fun m ↦ m.hom x) (relativeSingularCohomology_map_congr R hgf h h' j)

/-- If `g ≫ f = 𝟙 Y`, restricting a class of `H^j(Y, A)` along `f` and then along `g` returns
the class. -/
lemma relativeSingularCohomology_map_map_apply_of_comp_eq_id {Y' Y : TopCat.{u}} (g : Y ⟶ Y')
    (f : Y' ⟶ Y) (hgf : g ≫ f = 𝟙 Y) {A' : Set Y'} {A : Set Y} (hg : A ⊆ g ⁻¹' A')
    (hf : A' ⊆ f ⁻¹' A) (j : ℤ) (x : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f hf j).hom x) = x := by
  refine (relativeSingularCohomology_map_map_apply R g f hg hf (fun _ hx ↦ hf (hg hx)) j x).trans ?_
  refine (congrArg (fun m ↦ m.hom x)
    (relativeSingularCohomology_map_congr R hgf _ (fun _ h ↦ h) j)).trans ?_
  exact congrArg (fun m ↦ m.hom x) (relativeSingularCohomology.map_id R _ Y A j)

/-- `H^j(W, W)` is trivial. -/
lemma subsingleton_relativeSingularCohomology_univ (W : TopCat.{u}) (j : ℤ) :
    Subsingleton (relativeSingularCohomology R (ModuleCat.of R R) W univ j) := by
  rcases le_or_gt 0 j with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    refine (SingularCochain.relativeSingularCohomologyEquiv R (Y := W) univ
      n).toEquiv.subsingleton_congr.mpr ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    congr 1
    exact Subtype.ext (funext fun σ ↦
      (x.2.1 σ (subset_univ _)).trans (y.2.1 σ (subset_univ _)).symm)
  · exact ModuleCat.subsingleton_of_isZero (isZero_relativeSingularCohomology_of_neg R W univ h)

/-- A class with supports in `X` restricts to zero on `Y - X`. -/
theorem pullback_compl_toCohomology_apply {Y : TopCat.{u}} (X : Set Y) (j : ℤ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y X j) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (subspaceInclusion Y Xᶜ) univ j).hom
      ((toCohomology R (ModuleCat.of R R) Y X j).hom x) = 0 := by
  have hW : (univ : Set (TopCat.of (Xᶜ : Set Y))) ⊆ subspaceInclusion Y Xᶜ ⁻¹' Xᶜ :=
    fun w _ ↦ w.2
  have := subsingleton_relativeSingularCohomology_univ R (TopCat.of (Xᶜ : Set Y)) j
  refine (relativeSingularCohomology_map_map_apply_eq R _ (𝟙 Y) (𝟙 _) _ (by simp) _ _
    (fun _ _ ↦ mem_univ _) hW j x).trans ?_
  rw [Subsingleton.elim ((relativeSingularCohomology.map R (ModuleCat.of R R)
    (subspaceInclusion Y Xᶜ) hW j).hom x) 0, map_zero]

end map

section Retraction

/-! ### The Gysin map of a neighbourhood retraction with a class with supports

Let `φ : W → Y` be an open embedding whose image contains the closed set `Z`, `ρ : W → B` a map
with a section `s : B → W` (`s ≫ ρ = 𝟙`), and `u ∈ H^n(W, W - φ⁻¹ Z)`. Then
`a ↦ (φ^*)⁻¹ (ρ^* a ∪ u)` is a map `H^k(B) → H^{k+n}(Y, Y - Z)`, and its restriction along
`s ≫ φ` is `a ∪ s^* u`. For a tubular neighbourhood of a vector bundle, `ρ` is the projection,
`s` the zero section and `u` the Thom class; for a closed set `Z` with a retraction `ρ` of an open
neighbourhood `W` onto `Z`, `B = Z` and `u` is the restriction of a class in `H^n(Y, Y - Z)`. -/

variable {W B Y : TopCat.{u}} {Z : Set Y}

/-- Pull back along `ρ : W → B` and cup with `u ∈ H^n(W, W - T)`:
`H^k(B) → H^{k+n}(W, W - T)`, `a ↦ ρ^* a ∪ u`. -/
def cupPullback (ρ : W ⟶ B) {T : Set W} (hT : IsClosed T) {n : ℤ}
    (u : cohomologyWithSupports R (ModuleCat.of R R) W T n) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) B univ k →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) W T (k + n) :=
  (forget R (ModuleCat.of R R) _ inter_subset_right _).hom ∘ₗ
    ((cup R _ (isClosed_univ.preimage ρ.hom.continuous) hT k n).flip u) ∘ₗ
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) ρ univ k).hom

/-- The Gysin map with supports `H^k(B) → H^{k+n}(Y, Y - Z)`, `a ↦ (φ^*)⁻¹ (ρ^* a ∪ u)`, of an
open embedding `φ : W → Y` whose image contains `Z`, a map `ρ : W → B` and a class
`u ∈ H^n(W, W - φ⁻¹ Z)`. -/
def retractionGysinWithSupports (φ : W ⟶ Y) (hφ : IsOpenEmbedding φ) (hZ : IsClosed Z)
    (hZφ : Z ⊆ range φ) (ρ : W ⟶ B) {n : ℤ}
    (u : cohomologyWithSupports R (ModuleCat.of R R) W (φ ⁻¹' Z) n) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) B univ k →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y Z (k + n) :=
  (openEmbeddingPullbackIso R φ hφ hZ hZφ _).inv.hom ∘ₗ
    cupPullback R ρ (hZ.preimage φ.hom.continuous) u k

/-- The Gysin map `H^k(B) → H^{k+n}(Y)` of `φ`, `ρ` and `u`: the Gysin map with supports
followed by forgetting the supports. -/
def retractionGysin (φ : W ⟶ Y) (hφ : IsOpenEmbedding φ) (hZ : IsClosed Z)
    (hZφ : Z ⊆ range φ) (ρ : W ⟶ B) {n : ℤ}
    (u : cohomologyWithSupports R (ModuleCat.of R R) W (φ ⁻¹' Z) n) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) B univ k →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y univ (k + n) :=
  (toCohomology R (ModuleCat.of R R) Y Z _).hom ∘ₗ retractionGysinWithSupports R φ hφ hZ hZφ ρ u k

/-- **The self-intersection formula.** For a section `s` of `ρ`, the restriction of the Gysin
class along `s ≫ φ : B → Y` is the cup product with `s^* u`:
`(s ≫ φ)^* (φ_! a) = a ∪ s^* u`. -/
theorem pullback_retractionGysin (φ : W ⟶ Y) (hφ : IsOpenEmbedding φ) (hZ : IsClosed Z)
    (hZφ : Z ⊆ range φ) (ρ : W ⟶ B) (s : B ⟶ W) (hsρ : s ≫ ρ = 𝟙 B) {n : ℤ}
    (u : cohomologyWithSupports R (ModuleCat.of R R) W (φ ⁻¹' Z) n) (k : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) B univ k) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (s ≫ φ) univ _).hom
        (retractionGysin R φ hφ hZ hZφ ρ u k a) =
      (forget R (ModuleCat.of R R) B inter_subset_left _).hom
        (cup R B isClosed_univ isClosed_univ k n a
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) s univ n).hom
            ((toCohomology R (ModuleCat.of R R) W (φ ⁻¹' Z) n).hom u))) := by
  set e := openEmbeddingPullbackIso R φ hφ hZ hZφ (k + n)
  have hT : IsClosed (φ ⁻¹' Z) := hZ.preimage φ.hom.continuous
  set m := cupPullback R ρ hT u k a
  have hs : (univ : Set B)ᶜ ⊆ s ⁻¹' (φ ⁻¹' Z)ᶜ := fun x hx ↦ (hx (mem_univ x)).elim
  have h1 : (cohomologyWithSupports.pullback R (ModuleCat.of R R) (s ≫ φ) univ _).hom
        ((toCohomology R (ModuleCat.of R R) Y Z _).hom (e.inv.hom m)) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) s hs _).hom (e.hom.hom (e.inv.hom m)) :=
    relativeSingularCohomology_map_map_apply_eq R _ (𝟙 Y) _ φ (Category.comp_id _) _ _ _ _ _ _
  have hm : e.hom.hom (e.inv.hom m) = m := by
    rw [← ModuleCat.comp_apply, e.inv_hom_id]
    rfl
  change (cohomologyWithSupports.pullback R (ModuleCat.of R R) (s ≫ φ) univ _).hom
        ((toCohomology R (ModuleCat.of R R) Y Z _).hom (e.inv.hom m)) = _
  rw [h1, hm]
  have hX : IsClosed (ρ ⁻¹' univ) := isClosed_univ.preimage ρ.hom.continuous
  set c := cup R _ hX hT k n
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ρ univ k).hom a) u
  have h2 := relativeSingularCohomology_map_map_apply_eq R s (𝟙 _) (𝟙 _) s (by simp)
    (A₁ := (φ ⁻¹' Z)ᶜ) (A₂ := ((univ : Set B) ∩ univ)ᶜ) (A := (ρ ⁻¹' univ ∩ φ ⁻¹' Z)ᶜ) hs
    (compl_subset_compl.mpr (inter_subset_right (s := ρ ⁻¹' univ) (t := φ ⁻¹' Z)))
    (compl_subset_compl.mpr (inter_subset_left (s := univ) (t := univ)))
    (compl_subset_preimage_compl (inter_subset_inter (subset_univ _) (subset_univ _))) _ c
  refine h2.trans ?_
  have h3 := map_cup s hX hT isClosed_univ isClosed_univ (subset_univ _) (subset_univ _) k n
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ρ univ k).hom a) u
  have h4 := relativeSingularCohomology_map_map_apply_of_comp_eq_id R s ρ hsρ
    (compl_subset_preimage_compl (subset_univ _)) (fun _ hx ↦ hx) k a
  have h5 : (relativeSingularCohomology.map R (ModuleCat.of R R) s
      (compl_subset_preimage_compl (subset_univ (s ⁻¹' (φ ⁻¹' Z)))) _).hom u =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) s univ n).hom
        ((toCohomology R (ModuleCat.of R R) W (φ ⁻¹' Z) n).hom u) := by
    have hu : (univ : Set B)ᶜ ⊆ (s ≫ 𝟙 W) ⁻¹' (φ ⁻¹' Z)ᶜ := fun x hx ↦ (hx (mem_univ x)).elim
    refine ((relativeSingularCohomology_map_map_apply R s (𝟙 _) _ _ hu _ u).trans ?_).symm
    exact congrArg (fun f ↦ f.hom u)
      (relativeSingularCohomology_map_congr R (Category.comp_id s) hu _ _)
  refine (congrArg (relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 B)
    (compl_subset_compl.mpr (inter_subset_left (s := univ) (t := univ))) _).hom h3).trans ?_
  refine congrArg (fun x ↦ (forget R (ModuleCat.of R R) B inter_subset_left _).hom x) ?_
  exact congrArg₂ (fun x y ↦ cup R B isClosed_univ isClosed_univ k n x y) h4 h5

/-- The Gysin class of `φ`, `ρ`, `u` vanishes on the complement of `Z`. -/
theorem pullback_compl_retractionGysin (φ : W ⟶ Y) (hφ : IsOpenEmbedding φ) (hZ : IsClosed Z)
    (hZφ : Z ⊆ range φ) (ρ : W ⟶ B) {n : ℤ}
    (u : cohomologyWithSupports R (ModuleCat.of R R) W (φ ⁻¹' Z) n) (k : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) B univ k) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (subspaceInclusion Y Zᶜ) univ _).hom
      (retractionGysin R φ hφ hZ hZφ ρ u k a) = 0 :=
  pullback_compl_toCohomology_apply R Z _ _

/-- **The self-intersection formula for a neighbourhood retraction.** Let `Z ⊆ Y` be closed,
`U ⊇ Z` open, `r : U → Z` a retraction (`r z = z` on `Z`), and `u ∈ H^n(Y, Y - Z)`. Then the
Gysin class `φ_! a = (φ^*)⁻¹ (r^* a ∪ u|_U)` of `a ∈ H^k(Z)`, restricted to `Z`, is `a ∪ u|_Z`. -/
theorem pullback_retractionGysin_subspaceInclusion (hZ : IsClosed Z) {U : Set Y} (hU : IsOpen U)
    (hZU : Z ⊆ U) (r : C(U, Z)) (hr : ∀ y : U, (y : Y) ∈ Z → (r y : Y) = y) {n : ℤ}
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y Z n) (k : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of Z) univ k) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (subspaceInclusion Y Z) univ _).hom
        (retractionGysin R (subspaceInclusion Y U) hU.isOpenEmbedding_subtypeVal hZ
          (fun z hz ↦ ⟨⟨z, hZU hz⟩, rfl⟩) (TopCat.ofHom r)
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subspaceInclusion Y U) Z n).hom
            u) k a) =
      (forget R (ModuleCat.of R R) (TopCat.of Z) inter_subset_left _).hom
        (cup R (TopCat.of Z) isClosed_univ isClosed_univ k n a
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subspaceInclusion Y Z) univ
            n).hom ((toCohomology R (ModuleCat.of R R) Y Z n).hom u))) := by
  let sZ : TopCat.of Z ⟶ TopCat.of U := TopCat.ofHom ⟨Set.inclusion hZU, continuous_inclusion hZU⟩
  have hsρ : sZ ≫ TopCat.ofHom r = 𝟙 _ := by
    ext z
    exact hr ⟨z.1, hZU z.2⟩ z.2
  have hsφ : sZ ≫ subspaceInclusion Y U = subspaceInclusion Y Z := rfl
  have h := pullback_retractionGysin R (subspaceInclusion Y U) hU.isOpenEmbedding_subtypeVal hZ
    (fun z hz ↦ ⟨⟨z, hZU hz⟩, rfl⟩) (TopCat.ofHom r) sZ hsρ
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subspaceInclusion Y U) Z n).hom u) k a
  rw [hsφ] at h
  refine h.trans (congrArg (fun x ↦ (forget R (ModuleCat.of R R) (TopCat.of Z)
    inter_subset_left _).hom (cup R (TopCat.of Z) isClosed_univ isClosed_univ k n a x)) ?_)
  have hc : (univ : Set U)ᶜ ⊆ (𝟙 (TopCat.of U) ≫ subspaceInclusion Y U) ⁻¹' Zᶜ :=
    fun x hx ↦ (hx (mem_univ x)).elim
  have e1 := relativeSingularCohomology_map_map_apply R (𝟙 (TopCat.of U)) (subspaceInclusion Y U)
    (A'' := (univ : Set U)ᶜ) (A' := (subspaceInclusion Y U ⁻¹' Z)ᶜ) (A := Zᶜ)
    (compl_subset_compl.mpr (subset_univ _)) (compl_subset_preimage_compl subset_rfl) hc n u
  change (relativeSingularCohomology.map R (ModuleCat.of R R) sZ
    (A' := (univ : Set Z)ᶜ) (A := (univ : Set U)ᶜ) (compl_subset_preimage_compl (subset_univ _))
      n).hom
      ((relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 (TopCat.of U))
        (compl_subset_compl.mpr (subset_univ _)) n).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) (subspaceInclusion Y U)
          (A' := (subspaceInclusion Y U ⁻¹' Z)ᶜ) (compl_subset_preimage_compl subset_rfl)
            n).hom u)) = _
  rw [e1]
  exact relativeSingularCohomology_map_map_apply_eq R sZ
    (𝟙 (TopCat.of U) ≫ subspaceInclusion Y U) (subspaceInclusion Y Z) (𝟙 Y) (by ext; rfl)
    (compl_subset_preimage_compl (subset_univ _)) hc (compl_subset_preimage_compl (subset_univ _))
    (compl_subset_compl.mpr (subset_univ _)) n u

end Retraction

section Gysin

variable {B : Type u} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E] in
/-- The projection `π : E → B` of a fibre bundle, as a morphism of topological spaces. -/
def bundleProj : TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E] in
@[simp]
lemma bundleProj_apply (x : TotalSpace F E) : bundleProj F E x = x.proj := rfl

omit [FiniteDimensional ℂ F] in
/-- The zero section `0_E : B → E` of a vector bundle, as a morphism of topological spaces. -/
def bundleZeroSection : TopCat.of B ⟶ TopCat.of (TotalSpace F E) :=
  TopCat.ofHom ⟨zeroSection F E, Trivialization.continuous_zeroSection ℂ⟩

omit [FiniteDimensional ℂ F] in
@[simp]
lemma bundleZeroSection_apply (b : B) : bundleZeroSection F E b = zeroSection F E b := rfl

omit [FiniteDimensional ℂ F] in
/-- The zero section is a section of the projection: `π ∘ 0_E = id`. -/
@[reassoc (attr := simp)]
lemma bundleZeroSection_comp_bundleProj : bundleZeroSection F E ≫ bundleProj F E = 𝟙 _ := rfl

/-- The Euler class `e(E) = 0_E^* u_E ∈ H^{2r}(B)` of a complex vector bundle of rank `r`: the
restriction of the Thom class to the zero section. -/
def eulerClass : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of B) univ
    (2 * Module.finrank ℂ F : ℕ) :=
  (relativeSingularCohomology.map R (ModuleCat.of R R) (bundleZeroSection F E)
    (A' := univᶜ) (fun x hx ↦ (hx (mem_univ x)).elim) _).hom (ThomClass.thomClass R F E)

variable {E} {Y : TopCat.{u}} {Z : Set Y}

/-- Cup product with the Thom class, `H^k(B) → H^{k+2r}(E, E - T)`, for a closed `T ⊆ E`
containing the zero section: `a ↦ π^* a ∪ u_E`. -/
def thomCup {T : Set (TopCat.of (TotalSpace F E))} (hT : IsClosed T)
    (h0T : range (zeroSection F E) ⊆ T) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of B) univ k →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) _ T (k + (2 * Module.finrank ℂ F : ℕ)) :=
  (forget R (ModuleCat.of R R) _ inter_subset_right _).hom ∘ₗ
    ((cup R _ (isClosed_univ.preimage (bundleProj F E).hom.continuous) hT k _).flip
      ((forget R (ModuleCat.of R R) _ h0T _).hom (ThomClass.thomClass R F E))) ∘ₗ
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (bundleProj F E) univ k).hom

/-- The Gysin map with supports `H^k(B) → H^{k+2r}(Y, Y - Z)` of a tubular neighbourhood
`φ : E ≅ U ⊆ Y` of `Z`: pull back along `π`, cup with the Thom class, and identify
`H^*(E, E - 0_E)` with `H^*(Y, Y - Z)` by `φ` and excision. -/
def gysinWithSupports (φ : TopCat.of (TotalSpace F E) ⟶ Y) (hφ : IsOpenEmbedding φ)
    (hZ : IsClosed Z) (hφZ : φ '' range (zeroSection F E) = Z) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of B) univ k →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y Z (k + (2 * Module.finrank ℂ F : ℕ)) :=
  (openEmbeddingPullbackIso R φ hφ hZ (hφZ ▸ image_subset_range _ _) _).inv.hom ∘ₗ
    thomCup R F (hZ.preimage φ.hom.continuous) (hφZ ▸ subset_preimage_image _ _) k

/-- The Gysin map `H^k(B) → H^{k+2r}(Y)` of a tubular neighbourhood `φ : E ≅ U ⊆ Y` of `Z`. -/
def gysin (φ : TopCat.of (TotalSpace F E) ⟶ Y) (hφ : IsOpenEmbedding φ)
    (hZ : IsClosed Z) (hφZ : φ '' range (zeroSection F E) = Z) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of B) univ k →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y univ (k + (2 * Module.finrank ℂ F : ℕ)) :=
  (toCohomology R (ModuleCat.of R R) Y Z _).hom ∘ₗ gysinWithSupports R F φ hφ hZ hφZ k

/-- The Gysin map of a tubular neighbourhood `φ` is `retractionGysin` with `ρ = π` and `u` the
Thom class, its supports enlarged from the zero section to `φ⁻¹ Z`. -/
theorem gysin_eq_retractionGysin (φ : TopCat.of (TotalSpace F E) ⟶ Y) (hφ : IsOpenEmbedding φ)
    (hZ : IsClosed Z) (hφZ : φ '' range (zeroSection F E) = Z) (k : ℤ) :
    gysin R F φ hφ hZ hφZ k = retractionGysin R φ hφ hZ (hφZ ▸ image_subset_range _ _)
      (bundleProj F E) ((forget R (ModuleCat.of R R) _ (hφZ ▸ subset_preimage_image _ _) _).hom
        (ThomClass.thomClass R F E)) k :=
  rfl

/-- The restriction of the Gysin class to `Z`, along `φ ∘ 0_E : B → Y`, is the cup product with
the Euler class: `(φ ∘ 0_E)^* (φ_! a) = a ∪ e(E)`. -/
theorem pullback_gysin (φ : TopCat.of (TotalSpace F E) ⟶ Y) (hφ : IsOpenEmbedding φ)
    (hZ : IsClosed Z) (hφZ : φ '' range (zeroSection F E) = Z) (k : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of B) univ k) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (bundleZeroSection F E ≫ φ) univ
        _).hom (gysin R F φ hφ hZ hφZ k a) =
      (forget R (ModuleCat.of R R) (TopCat.of B) inter_subset_left _).hom
        (cup R (TopCat.of B) isClosed_univ isClosed_univ k _ a (eulerClass R F E)) := by
  rw [gysin_eq_retractionGysin, pullback_retractionGysin R φ hφ hZ _ (bundleProj F E)
    (bundleZeroSection F E) (bundleZeroSection_comp_bundleProj F E)]
  refine congrArg (fun x ↦ (forget R (ModuleCat.of R R) (TopCat.of B) inter_subset_left _).hom
    (cup R (TopCat.of B) isClosed_univ isClosed_univ k _ a x)) ?_
  have h0T : range (zeroSection F E) ⊆ φ ⁻¹' Z := hφZ ▸ subset_preimage_image _ _
  have h₁ : (univ : Set (TopCat.of (TotalSpace F E)))ᶜ ⊆
      (𝟙 (TopCat.of (TotalSpace F E))) ⁻¹' (φ ⁻¹' Z)ᶜ := compl_subset_compl.mpr (subset_univ _)
  have h₂ : (φ ⁻¹' Z)ᶜ ⊆ (𝟙 (TopCat.of (TotalSpace F E))) ⁻¹' (range (zeroSection F E))ᶜ :=
    compl_subset_compl.mpr h0T
  have h₃ : (univ : Set (TopCat.of (TotalSpace F E)))ᶜ ⊆
      (𝟙 _ ≫ 𝟙 (TopCat.of (TotalSpace F E))) ⁻¹' (range (zeroSection F E))ᶜ :=
    fun x hx ↦ (hx (mem_univ x)).elim
  have hA := relativeSingularCohomology_map_map_apply R (𝟙 _) (𝟙 _) h₁ h₂ h₃ _
    (ThomClass.thomClass R F E)
  have hu : (univ : Set (TopCat.of B))ᶜ ⊆
      (bundleZeroSection F E ≫ 𝟙 _ ≫ 𝟙 _) ⁻¹' (range (zeroSection F E))ᶜ :=
    fun x hx ↦ (hx (mem_univ x)).elim
  have hB := relativeSingularCohomology_map_map_apply R (bundleZeroSection F E) (𝟙 _ ≫ 𝟙 _)
    (A'' := (univ : Set (TopCat.of B))ᶜ) (compl_subset_preimage_compl (subset_univ _)) h₃ hu _
    (ThomClass.thomClass R F E)
  refine (congrArg (relativeSingularCohomology.map R (ModuleCat.of R R) (bundleZeroSection F E)
    (A' := (univ : Set (TopCat.of B))ᶜ) (compl_subset_preimage_compl (subset_univ _)) _).hom
      hA).trans (hB.trans ?_)
  exact congrArg (fun f ↦ f.hom (ThomClass.thomClass R F E))
    (relativeSingularCohomology_map_congr R (f' := bundleZeroSection F E) (by simp) hu _ _)

/-- The Gysin class vanishes on the complement of `Z`. -/
theorem pullback_compl_gysin (φ : TopCat.of (TotalSpace F E) ⟶ Y) (hφ : IsOpenEmbedding φ)
    (hZ : IsClosed Z) (hφZ : φ '' range (zeroSection F E) = Z) (k : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of B) univ k) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (subspaceInclusion Y Zᶜ) univ _).hom
      (gysin R F φ hφ hZ hφZ k a) = 0 :=
  pullback_compl_toCohomology_apply R Z _ _

end Gysin

end MMP.Topology
