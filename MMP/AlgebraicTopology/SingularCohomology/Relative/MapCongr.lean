module

public import MMP.AlgebraicTopology.SingularCohomology.Relative

/-!
# Congruence lemmas for pull-backs in relative singular cohomology

Lemmas moving the map `relativeSingularCohomology.map R M f h j` along an equality of maps
`f = f'`, of composites, or of degrees `2 * n = 2 * m` (as casts or `eqToHom`s).

## Main results

* `MMP.relativeSingularCohomology.map_congr_hom`, `map_eq_of_hom_eq`: equal maps give equal
  pull-backs.
* `MMP.relativeSingularCohomology.map_comp_map_eq`: pull-back along a composite.
* `MMP.relativeSingularCohomology.map_hom_map_hom_map_hom_eq`: two chains of pull-backs along maps
  with the same composite agree.
* `MMP.relativeSingularCohomology.map_hom_cast`, `eqToHom_hom_eq_cast`, `eqToHom_comp_map`: the
  pull-back commutes with a change of degree.
-/

@[expose] public noncomputable section

open CategoryTheory Set

namespace MMP

namespace relativeSingularCohomology

variable (R : Type) [CommRing R] (M : ModuleCat.{0} R)

/-- Equal maps `f = f'` give equal pull-backs `map R M f h j = map R M f' h' j`. -/
lemma map_congr_hom {Y' Y : TopCat.{0}} {f f' : Y' ⟶ Y} {A' : Set Y'} {A : Set Y}
    (h : A' ⊆ f ⁻¹' A) (h' : A' ⊆ f' ⁻¹' A) (e : f = f') (j : ℤ) :
    map R M f h j = map R M f' h' j := by
  subst e
  rfl

/-- The pull-back along `f` followed by the pull-back along `g` is the pull-back along any map
`k` equal to `g ≫ f`. -/
lemma map_comp_map_eq {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) {k : Y'' ⟶ Y}
    (e : g ≫ f = k) (j : ℤ) :
    map R M f hf j ≫ map R M g hg j =
      map R M k (e ▸ (fun _ hx ↦ hf (hg hx) : A'' ⊆ (g ≫ f) ⁻¹' A)) j := by
  subst e
  exact (map_comp R M g f hg hf j).symm

/-- The pull-back along `f` commutes with the cast between degrees `2 * n` and `2 * m` when
`n = m`. -/
lemma map_hom_cast {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y}
    (h : A' ⊆ f ⁻¹' A) {n m : ℕ} (e : n = m)
    (x : relativeSingularCohomology R M Y A ((2 * n : ℕ) : ℤ)) :
    (map R M f h ((2 * m : ℕ) : ℤ)).hom (cast (by rw [e]) x) =
      cast (by rw [e]) ((map R M f h ((2 * n : ℕ) : ℤ)).hom x) := by
  subst e
  rfl

/-- For `n = m`, the `eqToHom` between the cohomology modules in degrees `2 * n` and `2 * m` acts
as the cast. -/
lemma eqToHom_hom_eq_cast {Y : TopCat.{0}} {A : Set Y} {n m : ℕ} (e : n = m)
    (h : relativeSingularCohomology R M Y A ((2 * n : ℕ) : ℤ) =
      relativeSingularCohomology R M Y A ((2 * m : ℕ) : ℤ))
    (x : relativeSingularCohomology R M Y A ((2 * n : ℕ) : ℤ)) :
    (eqToHom h).hom x = cast (by rw [e]) x := by
  subst e
  rfl

end relativeSingularCohomology

/-- For `n = m`, the pull-back along `f` commutes with the `eqToHom`s between degrees `2 * n` and
`2 * m`. -/
lemma relativeSingularCohomology.eqToHom_comp_map (R : Type) [CommRing R] (M : ModuleCat.{0} R)
    {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y} (h : A' ⊆ f ⁻¹' A) {n m : ℕ}
    (e : n = m) (h₁ : relativeSingularCohomology R M Y A ((2 * n : ℕ) : ℤ) =
      relativeSingularCohomology R M Y A ((2 * m : ℕ) : ℤ))
    (h₂ : relativeSingularCohomology R M Y' A' ((2 * n : ℕ) : ℤ) =
      relativeSingularCohomology R M Y' A' ((2 * m : ℕ) : ℤ)) :
    eqToHom h₁ ≫ relativeSingularCohomology.map R M f h ((2 * m : ℕ) : ℤ) =
      relativeSingularCohomology.map R M f h ((2 * n : ℕ) : ℤ) ≫ eqToHom h₂ := by
  subst e
  simp

namespace relativeSingularCohomology

variable (R : Type) [CommRing R]

/-- Equal maps `g = g'` give equal pull-backs with coefficients in `R`. -/
lemma map_eq_of_hom_eq {Y' Y : TopCat.{0}} {g g' : Y' ⟶ Y} {A' : Set Y'} {A : Set Y}
    (h : A' ⊆ g ⁻¹' A) (h' : A' ⊆ g' ⁻¹' A) (e : g = g') (j : ℤ) :
    map R (ModuleCat.of R R) g h j = map R (ModuleCat.of R R) g' h' j := by
  subst e
  rfl

/-- Two chains of pull-backs along maps with the same composite agree. -/
lemma map_hom_map_hom_map_hom_eq {Y₀ Y₁ Y₂ Y₃ Z : TopCat.{0}} (g₁ : Y₁ ⟶ Y₀) (g₂ : Y₂ ⟶ Y₁)
    (g₃ : Y₃ ⟶ Y₂) (f₁ : Z ⟶ Y₀) (f₂ : Y₃ ⟶ Z) {A₀ : Set Y₀} {A₁ : Set Y₁} {A₂ : Set Y₂}
    {A₃ : Set Y₃} {B : Set Z} (h₁ : A₁ ⊆ g₁ ⁻¹' A₀) (h₂ : A₂ ⊆ g₂ ⁻¹' A₁) (h₃ : A₃ ⊆ g₃ ⁻¹' A₂)
    (k₁ : B ⊆ f₁ ⁻¹' A₀) (k₂ : A₃ ⊆ f₂ ⁻¹' B) (e : g₃ ≫ g₂ ≫ g₁ = f₂ ≫ f₁) (j : ℤ)
    (u : relativeSingularCohomology R (ModuleCat.of R R) Y₀ A₀ j) :
    (map R _ g₃ h₃ j).hom ((map R _ g₂ h₂ j).hom ((map R _ g₁ h₁ j).hom u)) =
      (map R _ f₂ k₂ j).hom ((map R _ f₁ k₁ j).hom u) := by
  change (map R _ g₁ h₁ j ≫ map R _ g₂ h₂ j ≫ map R _ g₃ h₃ j).hom u =
    (map R _ f₁ k₁ j ≫ map R _ f₂ k₂ j).hom u
  have e₁ := map_comp R (ModuleCat.of R R) g₂ g₁ h₂ h₁ j
  have e₂ := map_comp R (ModuleCat.of R R) g₃ (g₂ ≫ g₁) h₃ (fun _ hx ↦ h₁ (h₂ hx)) j
  have e₃ := map_comp R (ModuleCat.of R R) f₂ f₁ k₂ k₁ j
  rw [← Category.assoc, ← e₁, ← e₂, ← e₃]
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ u) (map_eq_of_hom_eq R _ _ e j)

end relativeSingularCohomology

end MMP
