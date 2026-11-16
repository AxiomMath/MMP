module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LineBundle
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local

/-!
# Cartier divisors with coefficients on an arbitrary scheme

We define the `K`-module of `K`-Cartier divisors of a scheme `X`, the finite `K`-linear
combinations of Cartier divisors, and study local equations of a Cartier divisor `D`: units of
`Γ(U, 𝒦_X)` whose class in `Γ(U, 𝒦_X^*/𝒪_X^*)` is the restriction of `D`. On an open where `g` is
a local equation of `D`, multiplication by `g⁻¹` trivializes `𝒪_X(D)`.

## Main definitions

* `MMP.Mori.KCartierDivisor`: The `K`-module `Div(X)_K` of `K`-Cartier divisors.
* `MMP.Mori.KCartierDivisor.realization`: The Cartier divisor underlying a `K`-Cartier divisor
  with integer coefficients.
* `MMP.Mori.trivEquiv`: The isomorphism `Γ(W, 𝒪_X) ≃ Γ(W, 𝒪_X(D))`, `r ↦ r g⁻¹`.

## Main results

* `MMP.Mori.IsLocalEquationOn.exists_eq_mul`: Two local equations on `U` differ locally by a unit
  of `𝒪_X`.
* `MMP.Mori.IsLocalEquationOn.exists_isUnit_eq_mul`: A local equation on `U` and a local equation
  at `x ∈ U` differ by a unit of `𝒪_{X,x}`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v

namespace MMP.Mori

variable {X : Scheme.{u}}

/-! ### `K`-Cartier divisors -/

/-- The space `Div(X)_K` of *`K`-Cartier divisors* of a scheme `X`: the free `K`-module of
formal finite `K`-linear combinations `∑ cⱼ Dⱼ` of Cartier divisors `Dⱼ ∈ Div(X)`, the global
sections of `𝒦_X^*/𝒪_X^*`. -/
@[mmp "def_km1b_real_cartier_divisor"]
abbrev KCartierDivisor (K : Type v) [Zero K] (X : Scheme.{u}) : Type (max u v) :=
  X.CartierDivisor →₀ K

namespace KCartierDivisor

variable (K : Type v)

/-- A Cartier divisor `D` regarded as the `K`-Cartier divisor `1 · D`. -/
@[mmp "def_km1b_real_cartier_divisor"]
def ofCartier [Zero K] [One K] (D : X.CartierDivisor) : KCartierDivisor K X :=
  Finsupp.single D 1

variable {K}

/-- The *realization* of a `K`-Cartier divisor `∑ cⱼ Dⱼ` all of whose coefficients are integers:
the Cartier divisor `∑ cⱼ Dⱼ` computed in the group `Div(X)`. The integer `cⱼ` is unique since
`ℤ → K` is injective in characteristic zero. -/
@[mmp "def_km1b_real_cartier_divisor"]
def realization [AddGroupWithOne K] [CharZero K] (c : KCartierDivisor K X)
    (h : ∀ D, ∃ n : ℤ, c D = n) : X.CartierDivisor :=
  c.sum fun D _ => (Classical.choose (h D)) • D

/-- The realization of an integer combination `∑ nⱼ Dⱼ`, regarded as a `K`-Cartier divisor, is
the Cartier divisor `∑ nⱼ Dⱼ`. -/
theorem realization_eq_sum [AddGroupWithOne K] [CharZero K] (n : X.CartierDivisor →₀ ℤ) :
    realization (n.mapRange (Int.cast : ℤ → K) Int.cast_zero) (fun D => ⟨n D, rfl⟩) =
      n.sum fun D m => m • D := by
  classical
  have hc : ∀ D, Classical.choose (show ∃ m : ℤ,
      (n.mapRange (Int.cast : ℤ → K) Int.cast_zero) D = m from ⟨n D, rfl⟩) = n D := fun D =>
    Int.cast_injective (Classical.choose_spec (show ∃ m : ℤ,
      (n.mapRange (Int.cast : ℤ → K) Int.cast_zero) D = m from ⟨n D, rfl⟩)).symm
  unfold realization Finsupp.sum
  rw [Finsupp.support_mapRange_of_injective _ _ Int.cast_injective]
  exact Finset.sum_congr rfl fun D _ => congrArg (· • D) (hc D)

end KCartierDivisor

/-! ### Local equations of a Cartier divisor -/

/-- `Γ(V, 𝒪_X) → Γ(V, 𝒦_X)` is injective. -/
theorem toTotalQuotient_injective (V : X.Opens) :
    Function.Injective (MMP.Intersection.toTotalQuotient (X := X) V) := by
  have := X.mono_toTotalQuotientSheaf
  have : Mono (X.toTotalQuotientSheaf.hom.app (op V)) :=
    (NatTrans.mono_iff_mono_app _).mp
      (Functor.map_mono (TopCat.Sheaf.forget CommRingCat.{u} X) X.toTotalQuotientSheaf) (op V)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback
    (X.toTotalQuotientSheaf.hom.app (op V))

/-- The map `Γ(-, 𝒪_X) → Γ(-, 𝒦_X)` commutes with restriction along `V ⊆ U`. -/
theorem toTotalQuotient_map {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    MMP.Intersection.toTotalQuotient V (X.presheaf.map i.op r) =
      X.totalQuotientSheaf.obj.map i.op (MMP.Intersection.toTotalQuotient U r) :=
  MMP.Intersection.toTotalQuotient_res i.le r

/-- Restricting a section of `𝒦_X` from `U` to `V` and then to `W` is restricting it from `U`
to `W`. -/
theorem totalQuotient_map_map {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V)
    (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    X.totalQuotientSheaf.obj.map j.op (X.totalQuotientSheaf.obj.map i.op σ) =
      X.totalQuotientSheaf.obj.map (j ≫ i).op σ := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- A section of `𝒦_X` over `V` whose germs all come from `𝒪_X` comes from `Γ(V, 𝒪_X)`. -/
theorem exists_toTotalQuotient_eq {V : X.Opens} (σ : X.totalQuotientSheaf.obj.obj (op V))
    (h : ∀ (x : X) (hx : x ∈ V), X.totalQuotientSheaf.presheaf.germ V x hx σ ∈
      (MMP.Intersection.stalkToTotalQuotient x).range) :
    ∃ r : Γ(X, V), MMP.Intersection.toTotalQuotient V r = σ := by
  have key : ∀ x : V, ∃ (W : X.Opens) (hW : W ≤ V) (_ : x.1 ∈ W) (r : Γ(X, W)),
      MMP.Intersection.toTotalQuotient W r = X.totalQuotientSheaf.obj.map (homOfLE hW).op σ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := h x hx
    obtain ⟨W, hxW, r, rfl⟩ := X.presheaf.germ_exist a
    rw [← MMP.Intersection.germ_toTotalQuotient] at ha
    obtain ⟨W', hxW', i₁, i₂, heq⟩ := X.totalQuotientSheaf.presheaf.germ_eq x hxW hx _ _ ha
    refine ⟨W', i₂.le, hxW', X.presheaf.map (homOfLE i₁.le).op r, ?_⟩
    rwa [MMP.Intersection.toTotalQuotient_res i₁.le]
  choose W hW hxW r hr using key
  have hcover : V ≤ iSup W := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hcover r
    (fun i j => toTotalQuotient_injective _ (by
      erw [toTotalQuotient_map, toTotalQuotient_map, hr, hr, totalQuotient_map_map,
        totalQuotient_map_map]
      rfl))
  refine ⟨s, TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf W V (fun i => homOfLE (hW i))
    hcover _ _ fun i => ?_⟩
  have := toTotalQuotient_map (homOfLE (hW i)) s
  erw [hs i] at this
  erw [← this, hr i]

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat

open MMP.Intersection

/-- The underlying section of `resUnit i g` is the restriction of `g` to `V`. -/
@[simp]
theorem coe_resUnit {U V : X.Opens} (i : V ⟶ U) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    (resUnit i g : X.totalQuotientSheaf.obj.obj (op V)) =
      X.totalQuotientSheaf.obj.map i.op (g : X.totalQuotientSheaf.obj.obj (op U)) := rfl

/-- The underlying section of `(resUnit i g)⁻¹` is the restriction of `g⁻¹` to `V`. -/
@[simp]
theorem coe_inv_resUnit {U V : X.Opens} (i : V ⟶ U)
    (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    ((resUnit i g)⁻¹ : (X.totalQuotientSheaf.obj.obj (op V))ˣ) =
      X.totalQuotientSheaf.obj.map i.op (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op U)) := rfl

/-- Two local equations of a Cartier divisor on `U` differ, near every point of `U`, by a unit
of `𝒪_X`. -/
theorem IsLocalEquationOn.exists_eq_mul {D : X.CartierDivisor} {U : X.Opens}
    {g g' : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g)
    (hg' : IsLocalEquationOn D U g') {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (i : W ⟶ U) (_ : x ∈ W) (u : Γ(X, W)ˣ),
      (resUnit i g' : X.totalQuotientSheaf.obj.obj (op W)) =
        toTotalQuotient W u * resUnit i g := by
  obtain ⟨W, h, hxW, u, hu⟩ := hg.exists_unit_mul_eq hg' hx
  exact ⟨W, homOfLE h, hxW, u, hu.symm⟩

/-- A local equation of `D` on `U` and a local equation of `D` at a point `x ∈ U` differ by a
unit of `𝒪_{X,x}`. -/
theorem IsLocalEquationOn.exists_isUnit_eq_mul {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) {x : X}
    (hx : x ∈ U) {f : X.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f) :
    ∃ a : X.presheaf.stalk x, IsUnit a ∧
      f = stalkToTotalQuotient x a * X.totalQuotientSheaf.presheaf.germ U x hx g := by
  obtain ⟨U', hxU', g', hg', rfl⟩ := hf
  let j₁ : U ⊓ U' ⟶ U := homOfLE inf_le_left
  let j₂ : U ⊓ U' ⟶ U' := homOfLE inf_le_right
  obtain ⟨W, k, hxW, u, hu⟩ := IsLocalEquationOn.exists_eq_mul
    (isLocalEquationOn_resUnit j₁ hg) (isLocalEquationOn_resUnit j₂ hg') ⟨hx, hxU'⟩
  refine ⟨X.presheaf.germ W x hxW u, u.isUnit.map _, ?_⟩
  have h := congrArg (X.totalQuotientSheaf.presheaf.germ W x hxW) hu
  rw [map_mul, germ_toTotalQuotient] at h
  simp only [coe_resUnit] at h
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  exact h

section Trivialization

variable {D : X.CartierDivisor} {U : X.Opens} {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ}

/-- For a unit `g` of `Γ(V, 𝒦_X)` and `x ∈ V`, the germs of `g⁻¹` and `g` at `x` multiply to
`1`. -/
theorem germ_inv_mul_germ {V : X.Opens} (g : (X.totalQuotientSheaf.obj.obj (op V))ˣ) {x : X}
    (hx : x ∈ V) :
    X.totalQuotientSheaf.presheaf.germ V x hx (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op V)) *
      X.totalQuotientSheaf.presheaf.germ V x hx g = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

/-- On an open `W ⊆ U` where `g` is a local equation of `D`, `r ↦ r g⁻¹` sends a regular function
to a section of `𝒪_X(D)`. -/
theorem mul_inv_mem_lineBundleSections (hg : IsLocalEquationOn D U g) {W : X.Opens} (i : W ⟶ U)
    (r : Γ(X, W)) :
    toTotalQuotient W r * ((resUnit i g)⁻¹ : (X.totalQuotientSheaf.obj.obj (op W))ˣ) ∈
      lineBundleSections D W := by
  intro x hx f hf
  obtain ⟨a, -, rfl⟩ := IsLocalEquationOn.exists_isUnit_eq_mul hg (i.le hx) hf
  refine ⟨X.presheaf.germ W x hx r * a, ?_⟩
  rw [coe_inv_resUnit, map_mul, map_mul, germ_toTotalQuotient]
  erw [TopCat.Presheaf.germ_res_apply]
  symm
  calc _ = stalkToTotalQuotient x (X.presheaf.germ W x hx r) * stalkToTotalQuotient x a *
        (X.totalQuotientSheaf.presheaf.germ U x (i.le hx)
            (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op U)) *
          X.totalQuotientSheaf.presheaf.germ U x (i.le hx) g) := by ring
    _ = _ := by rw [germ_inv_mul_germ, mul_one]

/-- The `Γ(X, W)`-linear trivialization `Γ(W, 𝒪_X) ≃ Γ(W, 𝒪_X(D))`, `r ↦ r g⁻¹`, on an open
`W ⊆ U` where `g` is a local equation of `D`. -/
def trivEquiv (hg : IsLocalEquationOn D U g) {W : X.Opens} (i : W ⟶ U) :
    Γ(X, W) ≃ₗ[Γ(X, W)] lineBundleSections D W :=
  LinearEquiv.ofBijective
    { toFun r := ⟨_, mul_inv_mem_lineBundleSections hg i r⟩
      map_add' r s := Subtype.ext (by simp only [map_add, add_mul]; rfl)
      map_smul' a r := Subtype.ext (by
        change toTotalQuotient W (a * r) * _ = toTotalQuotient W a * (toTotalQuotient W r * _)
        rw [map_mul, mul_assoc]) }
    ⟨fun r s h => by
      have h' := congrArg (fun σ : lineBundleSections D W =>
        σ.1 * (resUnit i g : X.totalQuotientSheaf.obj.obj (op W))) h
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_assoc, Units.inv_mul, mul_one] at h'
      exact toTotalQuotient_injective W h',
    fun σ => by
      obtain ⟨r, hr⟩ := exists_toTotalQuotient_eq
        (σ.1 * (resUnit i g : X.totalQuotientSheaf.obj.obj (op W))) fun x hx => by
          rw [map_mul, coe_resUnit]
          erw [TopCat.Presheaf.germ_res_apply]
          exact σ.2 x hx _ ⟨U, i.le hx, g, hg, rfl⟩
      refine ⟨r, Subtype.ext ?_⟩
      change toTotalQuotient W r * _ = σ.1
      rw [hr, mul_assoc, Units.mul_inv, mul_one]⟩

/-- The trivialization `trivEquiv hg i` sends `r` to `r g⁻¹`. -/
@[simp]
theorem coe_trivEquiv_apply (hg : IsLocalEquationOn D U g) {W : X.Opens} (i : W ⟶ U)
    (r : Γ(X, W)) :
    (trivEquiv hg i r : X.totalQuotientSheaf.obj.obj (op W)) =
      toTotalQuotient W r * ((resUnit i g)⁻¹ : (X.totalQuotientSheaf.obj.obj (op W))ˣ) :=
  rfl

end Trivialization

end MMP.Mori
