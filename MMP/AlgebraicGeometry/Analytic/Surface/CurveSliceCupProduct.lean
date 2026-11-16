module

public import MMP.AlgebraicGeometry.Vanishing.KodairaCharZero
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SncFibreHomologyThree

/-!
# Curve slices of a smooth projective surface and the cup product into `H⁴`

Let `X` be a smooth projective complex surface. For a smooth curve `V ⊆ X` which is a prime divisor
with `𝒪_X(V)` invertible and `c₁(𝒪_X(V)) = m c₁(L)`, the Cartier divisor dictionary
`c₁(𝒪_X(V)) ∩ [X] = [V]` and the projection formula give the Gysin formula
`(c₁(𝒪_X(V)) ∪ z) ∩ [X] = i_*(i^* z ∩ [V])` for `z ∈ H²(X^an; ℚ)`. By Poincaré duality on `X`,
a class `y` with `i^* y = r i^* c₁(L)` has `y ∪ c₁(L) = r c₁(L)²`, and for `L` ample,
`c₁(L)² ≠ 0` since `m c₁(L)² ∩ [X]` has degree `deg(L|_V) > 0`. The complex form of the Gysin
relation follows from the rational one through the `ℚ`-linear forms `ℂ → ℚ`, as `H⁴(X^an; ℂ)` is
a line spanned by a rational class.

The formal properties of the cohomology ring used are proved first: pull-back and change of
coefficients are multiplicative and commute, and the cup product is commutative on `H²`.

## Main results

* `MMP.Analytic.SurfaceSlice.pullback_cupNatUniv`, `MMP.Analytic.SurfaceSlice.mapCoeff_cupNatUniv`,
  `MMP.Analytic.SurfaceSlice.pullback_mapCoeff`, `MMP.Analytic.SurfaceSlice.cupNatUniv_two_comm`.
* `MMP.Analytic.SurfaceSlice.cupNatUniv_eq_smul_of_rat`: complex Gysin relations from rational
  ones.
* `MMP.Analytic.SurfaceSlice.exists_isAmple_pullback_eq_chern`: ample modules restrict to ample
  modules along a closed immersion, with the restricted Chern class.
* `MMP.Analytic.SurfaceSlice.exists_capProduct_cupNatUniv_eq_pushforward`: the Gysin formula for a
  prime divisor of a surface.
* `MMP.Analytic.SurfaceSlice.cupNatUniv_eq_smul_of_primeDivisor`: the rational Gysin relation.
* `MMP.Analytic.SurfaceSlice.cupNatUniv_ne_zero_of_primeDivisor`: `c₁(L)² ≠ 0` for `L` ample.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1–19.2.
-/

@[expose] public section

open CategoryTheory MMP MMP.SingularChain MMP.SingularCochain

universe u

namespace MMP.Analytic.SurfaceSlice

variable {R : Type u} [CommRing R]

/-- Pull-back of the class of a cocycle is the class of the pulled-back cocycle. -/
theorem pullback_ofCocycle {Y' Y : TopCat.{u}} (g : Y' ⟶ Y) (k : ℕ) {φ : Simplex Y k → R}
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) k) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ (k : ℤ)).hom
      (cohomologyWithSupports.ofCocycle R Y k φ hφ) =
      cohomologyWithSupports.ofCocycle R Y' k (cochainPullback R g k φ)
        (cochainPullback_mem_relCocycles (A' := (Set.univᶜ : Set Y')) g
          (by intro x hx; exact absurd (Set.mem_univ x) hx) hφ) := by
  apply (relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y') k).injective
  have key := relativeSingularCohomologyEquiv_map (R := R) g (A' := (Set.univᶜ : Set Y'))
    (A := (Set.univᶜ : Set Y)) (fun _ hx ↦ absurd (Set.mem_univ _) hx) k
    (cohomologyWithSupports.ofCocycle R Y k φ hφ)
  refine key.trans ?_
  simp only [cohomologyWithSupports.ofCocycle, LinearEquiv.apply_symm_apply]
  rfl

/-- **Pull-back is multiplicative**: `g^* (a ∪ b) = g^* a ∪ g^* b`. -/
theorem pullback_cupNatUniv {Y' Y : TopCat.{u}} (g : Y' ⟶ Y) (i j : ℕ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ))
    (b : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (j : ℕ)) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ ((i + j : ℕ) : ℤ)).hom
      (cupNatUniv R Y i j a b) =
      cupNatUniv R Y' i j
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ (i : ℤ)).hom a)
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ (j : ℤ)).hom b) := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq i a
  obtain ⟨ψ, hψ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq j b
  rw [cupNatUniv_ofCocycle Y i j hφ hψ, pullback_ofCocycle, pullback_ofCocycle,
    pullback_ofCocycle, cupNatUniv_ofCocycle]
  exact cohomologyWithSupports.ofCocycle_congr (cochainPullback_cup g i j (i + j) rfl φ ψ) _ _

variable {S : Type u} [CommRing S]

/-- Change of coefficients along a ring map commutes with the cup product of cochains. -/
theorem cochainMap_cup (f : R →+* S) {Y : TopCat.{u}} (p q n : ℕ) (h : p + q = n)
    (φ : Simplex Y p → R) (ψ : Simplex Y q → R) :
    singularCohomology.cochainMap f n (cup p q n h φ ψ) =
      cup p q n h (singularCohomology.cochainMap f p φ) (singularCohomology.cochainMap f q ψ) := by
  ext σ
  simp only [singularCohomology.cochainMap_apply, cup_apply, map_mul]

/-- **Change of coefficients is multiplicative**: `f_* (a ∪ b) = f_* a ∪ f_* b`. -/
theorem mapCoeff_cupNatUniv (f : R →+* S) {Y : TopCat.{u}} (i j : ℕ)
    (a : singularCohomology R Y i) (b : singularCohomology R Y j) :
    singularCohomology.mapCoeff f (i + j) (cupNatUniv R Y i j a b) =
      cupNatUniv S Y i j (singularCohomology.mapCoeff f i a)
        (singularCohomology.mapCoeff f j b) := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq i a
  obtain ⟨ψ, hψ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq j b
  rw [cupNatUniv_ofCocycle Y i j hφ hψ, singularCohomology.mapCoeff_ofCocycle,
    singularCohomology.mapCoeff_ofCocycle, singularCohomology.mapCoeff_ofCocycle,
    cupNatUniv_ofCocycle Y i j _ _]
  exact cohomologyWithSupports.ofCocycle_congr (cochainMap_cup f i j (i + j) rfl φ ψ) _ _

/-- Pull-back commutes with change of coefficients. -/
theorem pullback_mapCoeff (f : R →+* S) {Y' Y : TopCat.{u}} (g : Y' ⟶ Y) (k : ℕ)
    (a : singularCohomology R Y k) :
    (cohomologyWithSupports.pullback S (ModuleCat.of S S) g Set.univ (k : ℤ)).hom
      (singularCohomology.mapCoeff f k a) =
      singularCohomology.mapCoeff (Y := Y') f k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ (k : ℤ)).hom a) := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq k a
  rw [singularCohomology.mapCoeff_ofCocycle, pullback_ofCocycle, pullback_ofCocycle]
  erw [singularCohomology.mapCoeff_ofCocycle]
  rfl

/-- **The cup product is commutative on `H²`**: `a ∪ b = b ∪ a` in `H⁴`. -/
theorem cupNatUniv_two_comm {Y : TopCat.{u}}
    (a b : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ ((2 : ℕ) : ℤ)) :
    cupNatUniv R Y 2 2 a b = cupNatUniv R Y 2 2 b a := by
  have hc := cohomologyWithSupports.cup_comm R Y isClosed_univ isClosed_univ
    ((2 : ℕ) : ℤ) ((2 : ℕ) : ℤ) a b
  have hs : (((-1 : Rˣ) ^ (((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ)) : Rˣ) : R) = 1 := by
    rw [show (((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ)) = 2 * 2 by norm_num, zpow_mul]
    simp
  rw [hs, one_smul] at hc
  simp only [cupNatUniv, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
  rw [← hc]
  rfl

/-! ### Rational forms of complex coefficients -/

section Rational

variable {Y : TopCat.{0}}

/-- A `ℚ`-linear form `g : ℂ → ℚ` applied to the values of a complex cochain. -/
noncomputable def ratCochain (g : ℂ →ₗ[ℚ] ℚ) {n : ℕ} (φ : Simplex Y n → ℂ) : Simplex Y n → ℚ :=
  fun σ ↦ g (φ σ)

/-- `ratCochain g φ` takes the value `g (φ σ)` at a simplex `σ`. -/
theorem ratCochain_apply (g : ℂ →ₗ[ℚ] ℚ) {n : ℕ} (φ : Simplex Y n → ℂ) (σ : Simplex Y n) :
    ratCochain g φ σ = g (φ σ) :=
  rfl

/-- `ratCochain g` sends a difference of cochains to the difference. -/
theorem ratCochain_sub (g : ℂ →ₗ[ℚ] ℚ) {n : ℕ} (φ ψ : Simplex Y n → ℂ) :
    ratCochain g (φ - ψ) = ratCochain g φ - ratCochain g ψ := by
  ext σ
  simp [ratCochain_apply]

/-- `g (a * (k : ℂ)) = g a * k` for an integer `k`. -/
theorem map_mul_intCast (g : ℂ →ₗ[ℚ] ℚ) (a : ℂ) (k : ℤ) : g (a * (k : ℂ)) = g a * (k : ℚ) := by
  have : a * (k : ℂ) = (k : ℚ) • a := by
    rw [Rat.smul_def]
    push_cast
    ring
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- `g (k * a) = k * g a` for an integer `k`. -/
theorem map_intCast_mul (g : ℂ →ₗ[ℚ] ℚ) (a : ℂ) (k : ℤ) : g ((k : ℂ) * a) = (k : ℚ) * g a := by
  rw [mul_comm, map_mul_intCast, mul_comm]

/-- `ratCochain g` commutes with the coboundary. -/
theorem coboundary_ratCochain (g : ℂ →ₗ[ℚ] ℚ) (n : ℕ) (φ : Simplex Y n → ℂ) :
    coboundary ℚ n (ratCochain g φ) = ratCochain g (coboundary ℂ n φ) := by
  ext σ
  simp only [ratCochain_apply, coboundary_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := map_intCast_mul g (φ (σ.comp (face n i))) ((-1 : ℤ) ^ (i : ℕ))
  push_cast at this
  exact this.symm

/-- `ratCochain g` sends absolute complex coboundaries to rational coboundaries. -/
theorem ratCochain_mem_relCoboundaries (g : ℂ →ₗ[ℚ] ℚ) {n : ℕ} {φ : Simplex Y n → ℂ}
    (hφ : φ ∈ relCoboundaries ℂ (Set.univᶜ : Set Y) n) :
    ratCochain g φ ∈ relCoboundaries ℚ (Set.univᶜ : Set Y) n := by
  cases n with
  | zero =>
    change φ ∈ (⊥ : Submodule ℂ _) at hφ
    change _ ∈ (⊥ : Submodule ℚ _)
    rw [Submodule.mem_bot] at hφ ⊢
    subst hφ
    ext σ
    simp [ratCochain_apply]
  | succ k =>
    obtain ⟨χ, -, rfl⟩ := hφ
    exact ⟨ratCochain g χ, fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
      coboundary_ratCochain g k χ⟩

/-- `ratCochain g` sends absolute complex cocycles to rational cocycles. -/
theorem ratCochain_mem_relCocycles (g : ℂ →ₗ[ℚ] ℚ) {n : ℕ} {φ : Simplex Y n → ℂ}
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) n) :
    ratCochain g φ ∈ relCocycles ℚ (Set.univᶜ : Set Y) n :=
  ⟨fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp), by
    change coboundary ℚ n _ = 0
    rw [coboundary_ratCochain, show coboundary ℂ n φ = 0 from hφ.2]
    ext σ
    simp [ratCochain_apply]⟩

/-- The class of a cocycle vanishes iff the cocycle is a coboundary. -/
theorem ofCocycle_eq_zero_iff {R : Type} [CommRing R] {k : ℕ} {φ : Simplex Y k → R}
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) k) :
    cohomologyWithSupports.ofCocycle R Y k φ hφ = 0 ↔
      φ ∈ relCoboundaries R (Set.univᶜ : Set Y) k := by
  rw [cohomologyWithSupports.ofCocycle, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  rfl

/-- The class of a difference of cocycles is the difference of their classes. -/
theorem ofCocycle_sub {R : Type} [CommRing R] {k : ℕ} {φ ψ : Simplex Y k → R}
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) k) (hψ : ψ ∈ relCocycles R (Set.univᶜ : Set Y) k) :
    cohomologyWithSupports.ofCocycle R Y k (φ - ψ) (sub_mem hφ hψ) =
      cohomologyWithSupports.ofCocycle R Y k φ hφ -
        cohomologyWithSupports.ofCocycle R Y k ψ hψ := by
  simp only [cohomologyWithSupports.ofCocycle, ← map_sub, ← Submodule.Quotient.mk_sub]
  rfl

/-- The class of a scalar multiple of a cocycle is the scalar multiple of its class. -/
theorem ofCocycle_smul {R : Type} [CommRing R] {k : ℕ} {φ : Simplex Y k → R}
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) k) (c : R) :
    cohomologyWithSupports.ofCocycle R Y k (c • φ) (Submodule.smul_mem _ c hφ) =
      c • cohomologyWithSupports.ofCocycle R Y k φ hφ := by
  simp only [cohomologyWithSupports.ofCocycle, ← map_smul, ← Submodule.Quotient.mk_smul]
  rfl

/-- Two cocycles have the same class iff they differ by a coboundary. -/
theorem ofCocycle_eq_ofCocycle_iff {R : Type} [CommRing R] {k : ℕ} {φ ψ : Simplex Y k → R}
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) k) (hψ : ψ ∈ relCocycles R (Set.univᶜ : Set Y) k) :
    cohomologyWithSupports.ofCocycle R Y k φ hφ = cohomologyWithSupports.ofCocycle R Y k ψ hψ ↔
      φ - ψ ∈ relCoboundaries R (Set.univᶜ : Set Y) k := by
  rw [← sub_eq_zero, ← ofCocycle_sub hφ hψ, ofCocycle_eq_zero_iff]

/-- `ratCochain g` of a cup product with an integral cochain pushed to `ℂ`. -/
theorem ratCochain_cup_cochainMap (g : ℂ →ₗ[ℚ] ℚ) {p q n : ℕ} (h : p + q = n)
    (φ : Simplex Y p → ℂ) (κ : Simplex Y q → ℤ) :
    ratCochain g (cup p q n h φ (singularCohomology.cochainMap (Int.castRingHom ℂ) q κ)) =
      cup p q n h (ratCochain g φ) (singularCohomology.cochainMap (Int.castRingHom ℚ) q κ) := by
  ext σ
  simp only [ratCochain_apply, cup_apply, singularCohomology.cochainMap_apply, eq_intCast]
  exact map_mul_intCast g _ _

/-- `ratCochain g` of a multiple of a cup product of integral cochains pushed to `ℂ`. -/
theorem ratCochain_smul_cup_cochainMap (g : ℂ →ₗ[ℚ] ℚ) {p q n : ℕ} (h : p + q = n) (a : ℂ)
    (κ : Simplex Y p → ℤ) (κ' : Simplex Y q → ℤ) :
    ratCochain g (a • cup p q n h (singularCohomology.cochainMap (Int.castRingHom ℂ) p κ)
      (singularCohomology.cochainMap (Int.castRingHom ℂ) q κ')) =
      g a • cup p q n h (singularCohomology.cochainMap (Int.castRingHom ℚ) p κ)
        (singularCohomology.cochainMap (Int.castRingHom ℚ) q κ') := by
  ext σ
  simp only [ratCochain_apply, Pi.smul_apply, cup_apply, smul_eq_mul,
    singularCohomology.cochainMap_apply, eq_intCast]
  rw [← mul_assoc, map_mul_intCast, map_mul_intCast]
  ring

/-- If the rational class of the square of an integral cocycle is nonzero, so is its complex
class. -/
theorem ofCocycle_cup_cochainMap_ne_zero {k : ℕ} (κ : Simplex Y k → ℤ)
    {hQ : cup k k (k + k) rfl (singularCohomology.cochainMap (Int.castRingHom ℚ) k κ)
      (singularCohomology.cochainMap (Int.castRingHom ℚ) k κ) ∈
        relCocycles ℚ (Set.univᶜ : Set Y) (k + k)}
    (hc : cohomologyWithSupports.ofCocycle ℚ Y (k + k) _ hQ ≠ 0)
    (hC : cup k k (k + k) rfl (singularCohomology.cochainMap (Int.castRingHom ℂ) k κ)
      (singularCohomology.cochainMap (Int.castRingHom ℂ) k κ) ∈
        relCocycles ℂ (Set.univᶜ : Set Y) (k + k)) :
    cohomologyWithSupports.ofCocycle ℂ Y (k + k) _ hC ≠ 0 := by
  intro h0
  rw [ofCocycle_eq_zero_iff] at h0
  obtain ⟨g₁, hg₁⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℂ) ≠ 0)
  have h := ratCochain_mem_relCoboundaries g₁ h0
  have e := ratCochain_smul_cup_cochainMap g₁ rfl 1 κ κ
  rw [one_smul, hg₁, one_smul] at e
  rw [e] at h
  exact hc ((ofCocycle_eq_zero_iff _).2 h)

/-- A complex pull-back relation `g^* [η] = r • g^* [κ]` gives the rational relation
`g^* [g' ∘ η] = g' r • g^* [κ]` for every `ℚ`-linear form `g' : ℂ → ℚ`. -/
theorem pullback_ofCocycle_ratCochain_eq_smul {Y' : TopCat.{0}} (g : Y' ⟶ Y) (g' : ℂ →ₗ[ℚ] ℚ)
    {k : ℕ} {η : Simplex Y k → ℂ} (hη : η ∈ relCocycles ℂ (Set.univᶜ : Set Y) k)
    {κ : Simplex Y k → ℤ} (hκ : κ ∈ relCocycles ℤ (Set.univᶜ : Set Y) k) (r : ℂ)
    (hy : (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ (k : ℤ)).hom
        (cohomologyWithSupports.ofCocycle ℂ Y k η hη) =
      r • (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ (k : ℤ)).hom
        (cohomologyWithSupports.ofCocycle ℂ Y k
          (singularCohomology.cochainMap (Int.castRingHom ℂ) k κ)
          (singularCohomology.cochainMap_mem_relCocycles _ hκ))) :
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g Set.univ (k : ℤ)).hom
        (cohomologyWithSupports.ofCocycle ℚ Y k (ratCochain g' η)
          (ratCochain_mem_relCocycles g' hη)) =
      g' r • (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g Set.univ (k : ℤ)).hom
        (cohomologyWithSupports.ofCocycle ℚ Y k
          (singularCohomology.cochainMap (Int.castRingHom ℚ) k κ)
          (singularCohomology.cochainMap_mem_relCocycles _ hκ)) := by
  rw [pullback_ofCocycle, pullback_ofCocycle] at hy
  have hy' : cochainPullback ℂ g k η -
      r • cochainPullback ℂ g k (singularCohomology.cochainMap (Int.castRingHom ℂ) k κ) ∈
        relCoboundaries ℂ (Set.univᶜ : Set Y') k := by
    refine (ofCocycle_eq_ofCocycle_iff (cochainPullback_mem_relCocycles
      (A' := (Set.univᶜ : Set Y')) g (by intro x hx; exact absurd (Set.mem_univ x) hx) hη)
      (Submodule.smul_mem _ r (cochainPullback_mem_relCocycles (A' := (Set.univᶜ : Set Y')) g
        (by intro x hx; exact absurd (Set.mem_univ x) hx)
        (singularCohomology.cochainMap_mem_relCocycles _ hκ)))).1 ?_
    rwa [ofCocycle_smul]
  rw [pullback_ofCocycle, pullback_ofCocycle]
  have e : cohomologyWithSupports.ofCocycle ℚ Y' k (cochainPullback ℚ g k (ratCochain g' η))
      (cochainPullback_mem_relCocycles (A' := (Set.univᶜ : Set Y')) g
        (by intro x hx; exact absurd (Set.mem_univ x) hx) (ratCochain_mem_relCocycles g' hη)) =
      cohomologyWithSupports.ofCocycle ℚ Y' k
        (g' r • cochainPullback ℚ g k (singularCohomology.cochainMap (Int.castRingHom ℚ) k κ))
        (Submodule.smul_mem _ _ (cochainPullback_mem_relCocycles (A' := (Set.univᶜ : Set Y')) g
          (by intro x hx; exact absurd (Set.mem_univ x) hx)
          (singularCohomology.cochainMap_mem_relCocycles _ hκ))) := by
    refine (ofCocycle_eq_ofCocycle_iff _ _).2 ?_
    convert ratCochain_mem_relCoboundaries g' hy' using 1
    ext σ
    simp only [ratCochain_apply, Pi.sub_apply, Pi.smul_apply, cochainPullback_apply, smul_eq_mul,
      map_sub, singularCohomology.cochainMap_apply, eq_intCast]
    rw [map_mul_intCast]
  rwa [ofCocycle_smul] at e

/-- **Complex Gysin relations from rational ones.** Let `g : Y' → Y` be continuous and
`c ∈ H²(Y; ℤ)` with `c² ≠ 0` in `H⁴(Y; ℚ)`, where `H⁴(Y; ℂ)` has dimension at most one. If
every rational class `y ∈ H²(Y; ℚ)` with `g^* y = r g^* c` satisfies `y ∪ c = r c²`, then so does
every complex class. -/
theorem cupNatUniv_eq_smul_of_rat {Y' : TopCat.{0}} (g : Y' ⟶ Y) (c : singularCohomology ℤ Y 2)
    [FiniteDimensional ℂ (singularCohomology ℂ Y (2 + 2))]
    (h4 : Module.finrank ℂ (singularCohomology ℂ Y (2 + 2)) ≤ 1)
    (hc : cupNatUniv ℚ Y 2 2 (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c)
      (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c) ≠ 0)
    (hG : ∀ (y : singularCohomology ℚ Y 2) (r : ℚ),
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g Set.univ ((2 : ℕ) : ℤ)).hom y =
        r • (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g Set.univ ((2 : ℕ) : ℤ)).hom
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c) →
      cupNatUniv ℚ Y 2 2 y (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c) =
        r • cupNatUniv ℚ Y 2 2 (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c)
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c))
    (y : singularCohomology ℂ Y 2) (r : ℂ)
    (hy : (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ ((2 : ℕ) : ℤ)).hom y =
      r • (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ ((2 : ℕ) : ℤ)).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c)) :
    cupNatUniv ℂ Y 2 2 y (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c) =
      r • cupNatUniv ℂ Y 2 2 (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c)
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c) := by
  obtain ⟨κ, hκ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 2 c
  obtain ⟨η, hη, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 2 y
  simp only [singularCohomology.mapCoeff_ofCocycle] at hc hG hy ⊢
  set κC := singularCohomology.cochainMap (Int.castRingHom ℂ) 2 κ
  set κQ := singularCohomology.cochainMap (Int.castRingHom ℚ) 2 κ
  have hκC' : κC ∈ relCocycles ℂ (Set.univᶜ : Set Y) 2 :=
    singularCohomology.cochainMap_mem_relCocycles _ hκ
  have hκQ' : κQ ∈ relCocycles ℚ (Set.univᶜ : Set Y) 2 :=
    singularCohomology.cochainMap_mem_relCocycles _ hκ
  have hcupg : ∀ (g' : ℂ →ₗ[ℚ] ℚ) (φ : Simplex Y 2 → ℂ),
      ratCochain g' (cup 2 2 (2 + 2) rfl φ κC) = cup 2 2 (2 + 2) rfl (ratCochain g' φ) κQ :=
    fun g' φ ↦ ratCochain_cup_cochainMap g' rfl φ κ
  have hcupκ : ∀ (g' : ℂ →ₗ[ℚ] ℚ) (a : ℂ),
      ratCochain g' (a • cup 2 2 (2 + 2) rfl κC κC) = g' a • cup 2 2 (2 + 2) rfl κQ κQ :=
    fun g' a ↦ ratCochain_smul_cup_cochainMap g' rfl a κ κ
  rw [cupNatUniv_ofCocycle Y 2 2 hκQ' hκQ'] at hc
  have hw : cohomologyWithSupports.ofCocycle ℂ Y (2 + 2) (cup 2 2 (2 + 2) rfl κC κC)
      (cup_mem_relCocycles_compl_univ rfl hκC' hκC') ≠ 0 :=
    ofCocycle_cup_cochainMap_ne_zero κ hc _
  set ζ := cup 2 2 (2 + 2) rfl η κC - r • cup 2 2 (2 + 2) rfl κC κC with hζ
  have hζc : ζ ∈ relCocycles ℂ (Set.univᶜ : Set Y) (2 + 2) :=
    sub_mem (cup_mem_relCocycles_compl_univ rfl hη hκC')
      (Submodule.smul_mem _ r (cup_mem_relCocycles_compl_univ rfl hκC' hκC'))
  suffices h0 : cohomologyWithSupports.ofCocycle ℂ Y (2 + 2) ζ hζc = 0 by
    rwa [cupNatUniv_ofCocycle Y 2 2 hη hκC', cupNatUniv_ofCocycle Y 2 2 hκC' hκC',
      ← ofCocycle_smul, ← sub_eq_zero, ← ofCocycle_sub]
  have h1 := finrank_span_singleton (K := ℂ) hw
  have htop : Submodule.span ℂ {(cohomologyWithSupports.ofCocycle ℂ Y (2 + 2)
      (cup 2 2 (2 + 2) rfl κC κC) (cup_mem_relCocycles_compl_univ rfl hκC' hκC'))} = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by rw [h1]; exact h4))
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1
    (htop ▸ Submodule.mem_top (x := cohomologyWithSupports.ofCocycle ℂ Y (2 + 2) ζ hζc))
  rw [← ofCocycle_smul, ofCocycle_eq_ofCocycle_iff] at ht
  by_cases ht0 : t = 0
  · rw [ht0, zero_smul, zero_sub] at ht
    exact (ofCocycle_eq_zero_iff _).2 (by simpa using neg_mem ht)
  exfalso
  obtain ⟨g', hg'⟩ := Module.Projective.exists_dual_eq_one ℚ ht0
  have hgη := ratCochain_mem_relCocycles g' hη
  have hG' := hG _ (g' r) (pullback_ofCocycle_ratCochain_eq_smul g g' hη hκ r hy)
  rw [cupNatUniv_ofCocycle Y 2 2 hgη hκQ', cupNatUniv_ofCocycle Y 2 2 hκQ' hκQ',
    ← ofCocycle_smul, ofCocycle_eq_ofCocycle_iff] at hG'
  have hζQ : ratCochain g' ζ ∈ relCoboundaries ℚ (Set.univᶜ : Set Y) (2 + 2) := by
    rwa [hζ, ratCochain_sub, hcupg, hcupκ]
  have htQ := ratCochain_mem_relCoboundaries g' ht
  rw [ratCochain_sub, hcupκ, hg', one_smul] at htQ
  exact hc ((ofCocycle_eq_zero_iff _).2 (by simpa only [sub_add_cancel] using add_mem htQ hζQ))

end Rational

/-! ### Restriction of ample modules to a closed subscheme -/

section Restriction

open AlgebraicGeometry

/-- Pull-back of the first Chern class with coefficients in `R` along a morphism over `ℂ`. -/
theorem pullback_mapCoeff_algebraicFirstChernClass (R : Type) [CommRing R] {C X : Scheme.{0}}
    [C.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] (i : C ⟶ X)
    (hi : i ≫ (X ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
        Set.univ ((2 : ℕ) : ℤ)).hom
        (singularCohomology.mapCoeff (Int.castRingHom R) 2 (algebraicFirstChernClass L)) =
      singularCohomology.mapCoeff (Int.castRingHom R) 2
        (algebraicFirstChernClass ((Scheme.Modules.pullback i).obj L)) := by
  set g : Analytification.space (C ↘ Spec (.of ℂ)) ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩
  have hc := algebraicFirstChernClass_pullback i g (fun _ ↦ rfl) L
  have key : (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := Set.univᶜ)
      (A := Set.univᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom (algebraicFirstChernClass L) =
      (cohomologyWithSupports.pullback ℤ (ModuleCat.of ℤ ℤ) g Set.univ ((2 : ℕ) : ℤ)).hom
        (algebraicFirstChernClass L) := rfl
  rw [key] at hc
  rw [hc]
  exact pullback_mapCoeff (Int.castRingHom R) g 2 _

/-- **Ample modules restrict to ample modules**, with the restricted Chern class. For a closed
immersion `i : C → X` of schemes over `ℂ`, `C` proper, and `L` ample on `X`, the pull-back
`N = i^* L` is ample, and `i^* c₁(L) = c₁(N)` in `H²(C^an; ℂ)`. -/
theorem exists_isAmple_pullback_eq_chern {C X : Scheme.{0}} [C.Over (Spec (.of ℂ))]
    [X.Over (Spec (.of ℂ))] [IsProper (C ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]
    (i : C ⟶ X) [IsClosedImmersion i] (hi : i ≫ (X ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L) :
    ∃ (N : C.Modules) (_ : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N),
      MMP.Intersection.IsAmple ℂ N ∧
      (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
        (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
        Set.univ ((2 : ℕ) : ℤ)).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) =
        singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass N) := by
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  have : Stacks.Ample.IsInvertibleModule C ((Scheme.Modules.pullback i).obj L) := inferInstance
  refine ⟨(Scheme.Modules.pullback i).obj L, inferInstance,
    MMP.Intersection.isAmple_of_stacksIsAmple ℂ _ ((Stacks.AmpleBridge.isAmple_iff_isAmple C _).2
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion i L
        ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).1 hL.stacksIsAmple))), ?_⟩
  exact pullback_mapCoeff_algebraicFirstChernClass ℂ i hi L

end Restriction

/-! ### The rational Gysin formula for a prime divisor of a surface -/

section Gysin

open AlgebraicGeometry borelMooreHomology MMP.Fourfold UnderlyingSpace
open scoped MMP.SubschemeOver
open Stacks.Chow (integralComponentAt fieldChowSituation relativeDimension)

/-- The homeomorphism `X(ℂ) ≅ X^an`, as a morphism of spaces. -/
noncomputable abbrev underlyingToAn (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] :
    TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
  TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩

/-- `X(ℂ) ≅ X^an` intertwines the maps induced by a morphism over `ℂ`. -/
theorem map_comp_underlyingToAn {C X : Scheme.{0}} [C.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))]
    (i : C ⟶ X) [i.IsOver (Spec (.of ℂ))] (hi : i ≫ (X ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ)) :
    TopCat.ofHom (map (K := ℂ) i) ≫ underlyingToAn X =
      underlyingToAn C ≫
        TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩ := by
  ext x
  rfl

/-- Pulling back along `X(ℂ) ≅ X^an` is injective. -/
theorem injective_pullback_underlyingToAn (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] (R : Type)
    [CommRing R] (j : ℤ) :
    Function.Injective
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (underlyingToAn X) Set.univ j).hom := by
  let anInv : Analytification.space (X ↘ Spec (.of ℂ)) ⟶ TopCat.of (UnderlyingSpace ℂ X) :=
    TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.continuous⟩
  have hinv : anInv ≫ underlyingToAn X = 𝟙 _ :=
    TopCat.hom_ext (ContinuousMap.ext fun x ↦
      ComplexPoints.homeomorphUnderlyingSpace.symm_apply_apply x)
  have key : ∀ c, (cohomologyWithSupports.pullback R (ModuleCat.of R R) anInv
      (underlyingToAn X ⁻¹' Set.univ) j).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (underlyingToAn X) Set.univ j).hom c) =
        c := by
    intro c
    rw [← ModuleCat.comp_apply, ← cohomologyWithSupports.pullback_comp]
    generalize hφ : anInv ≫ underlyingToAn X = φ
    rw [hinv] at hφ
    subst hφ
    rw [cohomologyWithSupports.pullback_id]
    rfl
  exact Function.LeftInverse.injective key

/-- In degrees `2, 2`, the even cup product `cupUniv` is `cupNatUniv`. -/
theorem cupUniv_one_one {R : Type} [CommRing R] {Y : TopCat.{0}}
    (c d : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ ((2 : ℕ) : ℤ)) :
    cupUniv R Y 1 1 c d = cupNatUniv R Y 2 2 c d := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 2 c
  obtain ⟨ψ, hψ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 2 d
  rw [cupUniv_ofCocycle Y 1 1 hφ hψ (by norm_num), cupNatUniv_ofCocycle Y 2 2 hφ hψ]

/-- Pull-back of absolute classes along `g : Y' → Y`, `H^k(Y) → H^k(Y')`. -/
noncomputable def pullbackUniv {R : Type} [CommRing R] {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ k →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y' Set.univ k :=
  (cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ k).hom

/-- `pullbackUniv g k` is the pull-back `cohomologyWithSupports.pullback` on `Set.univ`. -/
theorem pullbackUniv_apply {R : Type} [CommRing R] {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (k : ℤ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ k) :
    pullbackUniv g k x =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ k).hom x :=
  rfl

/-- Pull-back of absolute classes is multiplicative for `cupNatUniv`. -/
theorem pullbackUniv_cupNatUniv {R : Type} [CommRing R] {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    (i j : ℕ) (a : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ))
    (b : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (j : ℕ)) :
    pullbackUniv g ((i + j : ℕ) : ℤ) (cupNatUniv R Y i j a b) =
      cupNatUniv R Y' i j (pullbackUniv g (i : ℤ) a) (pullbackUniv g (j : ℤ) b) :=
  pullback_cupNatUniv g i j a b

/-- Pull-back along `g` followed by pull-back along `f` is pull-back along `f ≫ g`. -/
theorem pullbackUniv_pullbackUniv {R : Type} [CommRing R] {Y'' Y' Y : TopCat.{0}} (f : Y'' ⟶ Y')
    (g : Y' ⟶ Y) (k : ℕ) (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (k : ℤ)) :
    pullbackUniv f (k : ℤ) (pullbackUniv g (k : ℤ) x) = pullbackUniv (f ≫ g) (k : ℤ) x := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq k x
  exact (congrArg (pullbackUniv f (k : ℤ)) (pullback_ofCocycle g k hφ)).trans
    ((pullback_ofCocycle f k _).trans (pullback_ofCocycle (f ≫ g) k hφ).symm)

/-- Pulling back along `X(ℂ) ≅ X^an` after a morphism `i` over `ℂ` is pulling back along
`C(ℂ) ≅ C^an` after the induced analytic map. -/
theorem pullbackUniv_map_underlyingToAn {R : Type} [CommRing R] {C Z : Scheme.{0}}
    [C.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] (i : C ⟶ Z) [i.IsOver (Spec (.of ℂ))]
    (hi : i ≫ (Z ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ)) (k : ℕ)
    (z : cohomologyWithSupports R (ModuleCat.of R R) (Analytification.space (Z ↘ Spec (.of ℂ)))
      Set.univ (k : ℤ)) :
    pullbackUniv (TopCat.ofHom (map (K := ℂ) i)) (k : ℤ)
        (pullbackUniv (underlyingToAn Z) (k : ℤ) z) =
      pullbackUniv (underlyingToAn C) (k : ℤ)
        (pullbackUniv (TopCat.ofHom
          ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩) (k : ℤ) z) := by
  rw [pullbackUniv_pullbackUniv, pullbackUniv_pullbackUniv, map_comp_underlyingToAn i hi]

/-- The projection formula for absolute classes. -/
theorem pushforward_capProduct_pullbackUniv {R : Type} [CommRing R] {Y' Y : TopCat.{0}}
    (f : Y' ⟶ Y) (hf : IsProperMap f) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ j)
    (a : MMP.borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) f hf (k - j)).hom
        (capProduct R Y' Set.univ j k (pullbackUniv f j c) a) =
      capProduct R Y Set.univ j k c ((pushforward R (ModuleCat.of R R) f hf k).hom a) :=
  pushforward_capProduct_pullback R f hf isClosed_univ
    (hasProperNeighbourhoodDeformations_univ _)
    (by rw [Set.preimage_univ]; exact hasProperNeighbourhoodDeformations_univ _) j k c a

/-- Pull-back of the rational first Chern class along a morphism over `ℂ`. -/
theorem pullbackUniv_mapCoeff_algebraicFirstChernClass {C X : Scheme.{0}} [C.Over (Spec (.of ℂ))]
    [X.Over (Spec (.of ℂ))] (i : C ⟶ X) (hi : i ≫ (X ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ))
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    pullbackUniv (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩ :
        Analytification.space (C ↘ Spec (.of ℂ)) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
      ((2 : ℕ) : ℤ)
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass ((Scheme.Modules.pullback i).obj L)) :=
  pullback_mapCoeff_algebraicFirstChernClass ℚ i hi L

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [QuasiCompact (X ↘ Spec (.of ℂ))] [SmoothOfRelativeDimension (1 + 1) (X ↘ Spec (.of ℂ))]

open Classical in
/-- **The cap product with a prime divisor.** On a smooth projective complex surface `X`, for a
prime divisor `P` whose closure `V` is a curve with invertible `𝒪_X(P)`, a fundamental class `[X]`
and every `z ∈ H²(X^an; ℚ)`, `(c₁(𝒪_X(P)) ∪ z) ∩ [X] = i_*(i^* z ∩ [V])`, `i : V → X` the
inclusion and `[V]` a fundamental class of `V`. -/
theorem exists_capProduct_cupNatUniv_eq_pushforward
    (hX : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim X = ((1 + 1 : ℕ) : WithBot ℕ∞)) (P : MMP.Mori.PrimeDivisor X)
    (hP : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) P.genericPoint = ((1 : ℕ) : ℤ))
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X))]
    (x : X) (hx : relativeDimension
      (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = ((1 + 1 : ℕ) : ℤ)) :
    ∃ μ, IsVarietyFundamentalClass ℚ
        (Chow.natCast_eq_dimension_integralComponentAt P.genericPoint hP) μ ∧
      ∀ z : singularCohomology ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2,
        capProduct ℚ (TopCat.of (UnderlyingSpace ℂ X)) Set.univ ((2 + 2 : ℕ) : ℤ)
            ((2 * (1 + 1) : ℕ) : ℤ)
            (pullbackUniv (underlyingToAn X) ((2 + 2 : ℕ) : ℤ)
              (cupNatUniv ℚ _ 2 2 (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
                (algebraicFirstChernClass
                  (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X)))) z))
            (Chow.pointCycleClass ℚ x hx) =
          (pushforward ℚ (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom (map (K := ℂ) (integralComponentAt P.genericPoint).subschemeι))
            (isProperMap_map (K := ℂ) _)
            ((((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ)) - ((2 * 1 : ℕ) : ℤ))).hom
            (capProduct ℚ _ Set.univ ((2 * 1 : ℕ) : ℤ)
              (((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ))
              (pullbackUniv (underlyingToAn (integralComponentAt P.genericPoint).subscheme)
                ((2 : ℕ) : ℤ)
                (pullbackUniv (TopCat.ofHom ⟨ComplexPoints.realize
                    (integralComponentAt P.genericPoint).subschemeι rfl,
                    ComplexPoints.continuous_realize _ rfl⟩ :
                    Analytification.space ((integralComponentAt P.genericPoint).subscheme ↘
                      Spec (.of ℂ)) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
                  ((2 : ℕ) : ℤ) z))
              μ) := by
  set cD := singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
    (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X)))
  have hdict := (smul_rationalCycleClass_eq_capProductPullback hX hsm (d := 1) hdim
    (MMP.Mori.Divisor.toQDivisor (Finsupp.single P 1)) one_pos (Finsupp.single P 1)
    (by rw [Nat.cast_one, one_smul]) x hx).1
  have hsingle : MMP.Mori.Divisor.toQDivisor (Finsupp.single P (1 : ℤ)) =
      Finsupp.single P (1 : ℚ) :=
    Finsupp.mapRange_single (hf := map_zero _)
  rw [hsingle, Finsupp.linearCombination_single, one_smul, dif_pos hP, Nat.cast_one,
    one_smul, Chow.rationalCycleClass_rationalPointCycle,
    Chow.rationalCycleClass_rationalPointCycle] at hdict
  set μ := (existsUnique_isVarietyFundamentalClass ℚ
    (Chow.natCast_eq_dimension_integralComponentAt P.genericPoint hP)).choose
  have hμ := (existsUnique_isVarietyFundamentalClass ℚ
    (Chow.natCast_eq_dimension_integralComponentAt P.genericPoint hP)).choose_spec.1
  refine ⟨μ, hμ, fun z ↦ ?_⟩
  rw [pullbackUniv_cupNatUniv, ← cupUniv_one_one]
  have hcc := capProduct_capProduct_eq_capProduct_cupUniv ℚ (TopCat.of (UnderlyingSpace ℂ X)) 1 1
    ((2 * (1 + 1) : ℕ) : ℤ) (pullbackUniv (underlyingToAn X) ((2 : ℕ) : ℤ) cD)
    (pullbackUniv (underlyingToAn X) ((2 : ℕ) : ℤ) z)
    (Chow.pointCycleClass ℚ x hx)
  have hcap : capProduct ℚ (TopCat.of (UnderlyingSpace ℂ X)) Set.univ ((2 * 1 : ℕ) : ℤ)
      ((2 * (1 + 1) : ℕ) : ℤ) (pullbackUniv (underlyingToAn X) ((2 : ℕ) : ℤ) cD)
        (Chow.pointCycleClass ℚ x hx) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ)
        (integralComponentAt P.genericPoint).subschemeι))
        (isProperMap_map (K := ℂ) _) (((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ))).hom μ :=
    hdict.symm
  rw [hcap] at hcc
  have h1 : capProduct ℚ (TopCat.of (UnderlyingSpace ℂ X)) Set.univ ((2 + 2 : ℕ) : ℤ)
      ((2 * (1 + 1) : ℕ) : ℤ)
      (cupUniv ℚ (TopCat.of (UnderlyingSpace ℂ X)) 1 1
        (pullbackUniv (underlyingToAn X) ((2 : ℕ) : ℤ) cD)
        (pullbackUniv (underlyingToAn X) ((2 : ℕ) : ℤ) z))
      (Chow.pointCycleClass ℚ x hx) =
      capProduct ℚ (TopCat.of (UnderlyingSpace ℂ X)) Set.univ ((2 * 1 : ℕ) : ℤ)
        (((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ))
        (pullbackUniv (underlyingToAn X) ((2 : ℕ) : ℤ) z)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ)
          (integralComponentAt P.genericPoint).subschemeι))
          (isProperMap_map (K := ℂ) _) (((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ))).hom μ) := by
    rw [hcc]
    rfl
  have h2 := (pushforward_capProduct_pullbackUniv (TopCat.ofHom (map (K := ℂ)
        (integralComponentAt P.genericPoint).subschemeι))
      (isProperMap_map (K := ℂ) _) ((2 * 1 : ℕ) : ℤ) (((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ))
      (pullbackUniv (underlyingToAn X) ((2 : ℕ) : ℤ) z) μ).symm
  rw [h1, h2, pullbackUniv_map_underlyingToAn (integralComponentAt P.genericPoint).subschemeι
    rfl 2 z]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The cycle class of a point of delta-dimension `2` (the generic point) of a smooth projective
surface is a fundamental class. -/
theorem isVarietyFundamentalClass_pointCycleClass_two
    (hdim : topologicalKrullDim X = ((1 + 1 : ℕ) : WithBot ℕ∞))
    (x : X) (hx : relativeDimension
      (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = ((1 + 1 : ℕ) : ℤ)) :
    IsVarietyFundamentalClass ℚ
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) (1 + 1))
      (Chow.pointCycleClass ℚ x hx) := by
  obtain ⟨c, hc, -, -⟩ := existsUnique_isVarietyFundamentalClass ℚ
    (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) (1 + 1))
  rw [Chow.pointCycleClass_eq_of_closure_eq_univ x hx
    (Chow.closure_eq_univ_of_relativeDimension_eq ℂ hdim x hx) _ hc]
  exact hc

open Classical in
/-- **The rational Gysin relation for a prime divisor of a surface.** On a smooth projective
complex surface `X`, let `P` be a prime divisor with curve closure `V`, `𝒪_X(P)` invertible with
`c₁(𝒪_X(P)) = m c₁(L)` in `H²(X^an; ℚ)`, `m > 0`. If `y ∈ H²(X^an; ℚ)` restricts to `V` as
`r c₁(L)|_V`, then `y ∪ c₁(L) = r c₁(L)²`. -/
theorem cupNatUniv_eq_smul_of_primeDivisor
    (hX : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim X = ((1 + 1 : ℕ) : WithBot ℕ∞)) (P : MMP.Mori.PrimeDivisor X)
    (hP : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) P.genericPoint = ((1 : ℕ) : ℤ))
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X))]
    (x : X) (hx : relativeDimension
      (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = ((1 + 1 : ℕ) : ℤ))
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {m : ℕ} (hm : 0 < m)
    (hc : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
        (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X))) =
      (m : ℚ) • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))
    (y : singularCohomology ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2) (r : ℚ)
    (hy : pullbackUniv (TopCat.ofHom ⟨ComplexPoints.realize
        (integralComponentAt P.genericPoint).subschemeι rfl,
        ComplexPoints.continuous_realize _ rfl⟩ :
        Analytification.space ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) ⟶
          Analytification.space (X ↘ Spec (.of ℂ))) ((2 : ℕ) : ℤ) y =
      r • pullbackUniv (TopCat.ofHom ⟨ComplexPoints.realize
        (integralComponentAt P.genericPoint).subschemeι rfl,
        ComplexPoints.continuous_realize _ rfl⟩ :
        Analytification.space ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) ⟶
          Analytification.space (X ↘ Spec (.of ℂ))) ((2 : ℕ) : ℤ)
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))) :
    cupNatUniv ℚ _ 2 2 y (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass L)) =
      r • cupNatUniv ℚ _ 2 2
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) := by
  set cL := singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)
  set cD := singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
    (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X)))
  obtain ⟨μ, -, hG⟩ := exists_capProduct_cupNatUniv_eq_pushforward hX hsm hdim P hP x hx
  have hGy := hG y
  rw [hy, map_smul, map_smul, LinearMap.smul_apply, map_smul, ← hG cL, ← LinearMap.smul_apply,
    ← map_smul, ← map_smul] at hGy
  have hb := bijective_capProduct_univ_of_isVarietyFundamentalClass
    (isVarietyFundamentalClass_pointCycleClass_two hdim x hx) ((2 + 2 : ℕ) : ℤ)
  have h1 := injective_pullback_underlyingToAn X ℚ _ (hb.1 hGy)
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  change cupNatUniv ℚ _ 2 2 cD y = r • cupNatUniv ℚ _ 2 2 cD cL at h1
  rw [hc, LinearMap.map_smul₂, LinearMap.map_smul₂, smul_comm] at h1
  rw [cupNatUniv_two_comm y cL]
  exact smul_right_injective _ hm' h1

open Stacks.Intersection.ExteriorProductProjections in
open Classical in
/-- **`c₁(L)² ≠ 0` on a surface through an ample curve slice.** In the situation of
`cupNatUniv_eq_smul_of_primeDivisor`, if the curve `V` is a smooth projective curve and `L` is
ample, then `c₁(L)² ≠ 0` in `H⁴(X^an; ℚ)`. -/
theorem cupNatUniv_ne_zero_of_primeDivisor
    (hX : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim X = ((1 + 1 : ℕ) : WithBot ℕ∞)) (P : MMP.Mori.PrimeDivisor X)
    (hP : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) P.genericPoint = ((1 : ℕ) : ℤ))
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X))]
    (x : X) (hx : relativeDimension
      (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = ((1 + 1 : ℕ) : ℤ))
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {m : ℕ}
    (hc : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
        (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X))) =
      (m : ℚ) • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))
    [IsProper ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ))]
    [IsCurve ℂ ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ))]
    (hsmC : MMP.Mori.IsSmoothScheme ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)))
    (hdimC : topologicalKrullDim (integralComponentAt P.genericPoint).subscheme = 1)
    (hprojC : MMP.Mori.IsProjectiveVariety ℂ
      ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)))
    (hL : Scheme.Modules.IsAmple X L) :
    cupNatUniv ℚ _ 2 2
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) ≠ 0 := by
  intro h0
  set C := (integralComponentAt P.genericPoint).subscheme
  have : IsIntegral C := Stacks.Chow.isIntegral_integralComponentAt _
  have : IrreducibleSpace C := irreducibleSpace_of_isIntegral C
  set cL := singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)
  obtain ⟨μ, hμ, hG⟩ := exists_capProduct_cupNatUniv_eq_pushforward hX hsm hdim P hP x hx
  have h1 := hG cL
  rw [hc, LinearMap.map_smul₂, h0, smul_zero, map_zero, map_zero, LinearMap.zero_apply,
    pullbackUniv_mapCoeff_algebraicFirstChernClass
      (integralComponentAt P.genericPoint).subschemeι rfl L] at h1
  set N := (Scheme.Modules.pullback
    (integralComponentAt P.genericPoint).subschemeι).obj L
  have hξC : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (C ↘ Spec (.of ℂ)) (_root_.genericPoint C) = ((1 : ℕ) : ℤ) :=
    Chow.relativeDimension_genericPoint_eq ℂ _ (by rw [hdimC]; rfl)
  have hμC : μ = Chow.pointCycleClass ℚ (_root_.genericPoint C) hξC := by
    obtain ⟨c, hcC, huniq, -⟩ := existsUnique_isVarietyFundamentalClass ℚ
      (Chow.natCast_eq_dimension_integralComponentAt P.genericPoint hP)
    rw [huniq μ hμ]
    exact (Chow.pointCycleClass_eq_of_closure_eq_univ (_root_.genericPoint C) hξC
      (genericPoint_spec C).def _ hcC).symm
  rw [hμC] at h1
  have hcomp : TopCat.ofHom (map (K := ℂ)
      (integralComponentAt P.genericPoint).subschemeι) ≫
        TopCat.ofHom (map (K := ℂ) (X ↘ Spec (.of ℂ))) =
      TopCat.ofHom (map (K := ℂ) (C ↘ Spec (.of ℂ))) := by
    ext p
    exact Category.assoc _ _ _
  have h2 := congrArg (pushforward ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (map (K := ℂ) (X ↘ Spec (.of ℂ)))) (isProperMap_map (K := ℂ) _)
    ((((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ)) - ((2 * 1 : ℕ) : ℤ))).hom h1
  rw [map_zero, ← pushforward_comp_apply', pushforward_congr' (R := ℚ) hcomp _
    (isProperMap_map (K := ℂ) _)] at h2
  let p0 : Spec (.of ℂ) := Classical.choice inferInstance
  have hdeg := pushforward_capProductPullback_eq_invertibleCurveDegree_smul hsmC hdimC hprojC N
    (_root_.genericPoint C) hξC p0
  have h3 : (invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdimC.le N : ℚ) •
      Chow.pointCycleClass ℚ p0 (relativeDimension_spec_eq_zero p0) = 0 := by
    rw [← hdeg]
    exact h2.symm
  exact (invertibleCurveDegree_pos_of_isAmple_of_isCurve ℂ (C ↘ Spec (.of ℂ)) hdimC.le N
    (Scheme.Modules.isAmple_pullback_of_isClosedImmersion
      (integralComponentAt P.genericPoint).subschemeι L hL)).ne'
    (by exact_mod_cast eq_zero_of_smul_pointCycleClass_spec_eq_zero p0 h3)

end Gysin

end MMP.Analytic.SurfaceSlice
