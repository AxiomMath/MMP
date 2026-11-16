module

public import MMP.AlgebraicGeometry.Divisor.LineBundle
public import MMP.AlgebraicGeometry.Divisor.LocalEquation
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import MMP.AlgebraicGeometry.Divisor.OrderPullback
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Local equations of Cartier divisors and the sections of `𝒪_X(D)` (Lazarsfeld §1.1)

Let `D` be a Cartier divisor on a scheme `X`. This file proves the facts about local equations
of Lazarsfeld §1.1 and the stalkwise description of the sections of `𝒪_X(D) ⊆ 𝓜_X`
(`MMP.Intersection.lineBundleSections`), from which the properties of the sheaf
`MMP.CartierDivisor.sheaf D` are derived (for instance
`MMP.CartierDivisor.isTrivializingGenerator_invSection`).

A Cartier divisor is given by local data: local equations `fᵢ` on an open cover, related on
overlaps by units of `𝒪_X`, and conversely such data define a unique divisor; local equations of
a sum are products. If `f` is a local equation of `D` on `U`, then the sections of `𝒪_X(D)` over
an open `V ⊆ U` are the multiples of `f⁻¹`. For effective `D`, `1` is a section of `𝒪_X(D)`.
For a regular section `s` of a line bundle `L`, the ratio `t / s` of a section `t` of `L` is a
section of `𝒪_X(div s)`.

## Main definitions

* `MMP.Intersection.IsRatio`, `MMP.Intersection.ratio`: the ratio `t / s` of a section `t` of a
  line bundle by a regular global section `s`.

## Main results

* `MMP.Intersection.exists_cover_isLocalEquationOn`,
  `MMP.Intersection.IsLocalEquationOn.exists_units_eq_mul`,
  `MMP.Intersection.isLocalEquationOn_add`,
  `MMP.Intersection.exists_cover_isLocalEquationOn_add`: local data of Cartier divisors.
* `MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn`,
  `MMP.Intersection.lineBundleSections_eq_span_of_isLocalEquationOn`: `𝒪_X(D)|_U = 𝒪_U · f⁻¹`.
* `MMP.Intersection.mem_lineBundleSections_iff_mem`: the stalkwise condition
  `lineBundleSections D V` is membership in `MMP.CartierDivisor.sheaf D`.
* `MMP.Intersection.one_mem_lineBundleSections`: `1 ∈ Γ(U, 𝒪_X(D))` for effective `D`.
* `MMP.Intersection.IsRatio.mem`: `t / s ∈ Γ(V, 𝒪_X(div s))`.

## Implementation notes

The ratio `t / s` is glued from the local quotients `(t/e_U) / (s/e_U)` over trivializing opens.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004], §1.1.
-/
@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry MonoidalCategory

namespace MMP.Intersection

variable {X : Scheme.{u}}

section LineBundle

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat

/-- `Γ(V, 𝒪_X) → Γ(V, 𝓜_X)` is injective: `𝒪_X ⟶ 𝓜_X` is a monomorphism of sheaves. -/
theorem injective_toTotalQuotient (V : X.Opens) :
    Function.Injective (toTotalQuotient (X := X) V) := by
  have := X.mono_toTotalQuotientSheaf
  have : Mono (X.toTotalQuotientSheaf.hom.app (op V)) :=
    (NatTrans.mono_iff_mono_app _).mp
      (Functor.map_mono (TopCat.Sheaf.forget CommRingCat.{u} X) X.toTotalQuotientSheaf) (op V)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback
    (X.toTotalQuotientSheaf.hom.app (op V))

/-- Restricting a section of `𝓜_X` along `V ⊆ U` and then along `W ⊆ V` is restricting it along
`W ⊆ U`. -/
theorem totalQuotient_map_map {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V)
    (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    X.totalQuotientSheaf.obj.map j.op (X.totalQuotientSheaf.obj.map i.op σ) =
      X.totalQuotientSheaf.obj.map (j ≫ i).op σ := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- A section of `𝓜_X` over `V` all of whose germs come from `𝒪_X` comes from `Γ(V, 𝒪_X)`. -/
theorem exists_toTotalQuotient_eq_of_germ_mem {V : X.Opens}
    (σ : X.totalQuotientSheaf.obj.obj (op V))
    (h : ∀ (x : X) (hx : x ∈ V), X.totalQuotientSheaf.presheaf.germ V x hx σ ∈
      (stalkToTotalQuotient x).range) :
    ∃ r : Γ(X, V), toTotalQuotient V r = σ := by
  have key : ∀ x : V, ∃ (W : X.Opens) (hW : W ≤ V) (_ : x.1 ∈ W) (r : Γ(X, W)),
      toTotalQuotient W r = X.totalQuotientSheaf.obj.map (homOfLE hW).op σ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := h x hx
    obtain ⟨W, hxW, r, rfl⟩ := X.presheaf.exists_germ_eq a
    rw [← germ_toTotalQuotient] at ha
    obtain ⟨W', hxW', i₁, i₂, heq⟩ := X.totalQuotientSheaf.presheaf.germ_eq x hxW hx _ _ ha
    refine ⟨W', i₂.le, hxW', X.presheaf.map (homOfLE i₁.le).op r, ?_⟩
    rw [toTotalQuotient_res i₁.le]
    exact heq
  choose W hW hxW r hr using key
  have hcover : V ≤ iSup W := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hcover r
    (fun i j => injective_toTotalQuotient _ (by
      erw [toTotalQuotient_res, toTotalQuotient_res, hr, hr, totalQuotient_map_map,
        totalQuotient_map_map]
      rfl))
  refine ⟨s, TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf W V (fun i => homOfLE (hW i))
    hcover _ _ fun i => ?_⟩
  have := toTotalQuotient_res (homOfLE (hW i)).le s
  erw [hs i] at this
  erw [← this, hr i]

/-- A local equation `g` of `D` on `U` and a local equation `f` of `D` at a point `x ∈ U` differ
by a unit of `𝒪_{X,x}`. -/
theorem IsLocalEquationOn.exists_isUnit_eq_mul_germ {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) {x : X}
    (hx : x ∈ U) {f : X.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f) :
    ∃ a : X.presheaf.stalk x, IsUnit a ∧
      f = stalkToTotalQuotient x a * X.totalQuotientSheaf.presheaf.germ U x hx g := by
  obtain ⟨U', hxU', g', hg', rfl⟩ := hf
  let j₁ : U ⊓ U' ⟶ U := homOfLE inf_le_left
  let j₂ : U ⊓ U' ⟶ U' := homOfLE inf_le_right
  obtain ⟨W, k, hxW, u, hu⟩ := IsLocalEquationOn.exists_unit_mul_eq
    (isLocalEquationOn_resUnit j₁ hg) (isLocalEquationOn_resUnit j₂ hg') ⟨hx, hxU'⟩
  refine ⟨X.presheaf.germ W x hxW u, (u.isUnit.map _), ?_⟩
  have h := congrArg (X.totalQuotientSheaf.presheaf.germ W x hxW) hu
  rw [map_mul, germ_toTotalQuotient] at h
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  exact h.symm

/-- **Fulton B.4.4.** If `g` is a local equation of the Cartier divisor `D` on `U`, then on every
open `V ⊆ U` the sections of `𝒪_X(D)` are exactly the `Γ(V, 𝒪_X)`-multiples of `g⁻¹|_V`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
theorem mem_lineBundleSections_iff_of_isLocalEquationOn {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) {V : X.Opens}
    (h : V ≤ U) (σ : X.totalQuotientSheaf.obj.obj (op V)) :
    σ ∈ lineBundleSections D V ↔
      ∃ r : Γ(X, V), r • X.totalQuotientSheaf.obj.map (homOfLE h).op (↑g⁻¹ : _) = σ := by
  constructor
  · intro hσ
    obtain ⟨r, hr⟩ := exists_toTotalQuotient_eq_of_germ_mem
      (σ * X.totalQuotientSheaf.obj.map (homOfLE h).op (g : _)) fun x hx => by
        rw [map_mul]
        erw [TopCat.Presheaf.germ_res_apply]
        exact hσ x hx _ ⟨U, h hx, g, hg, rfl⟩
    refine ⟨r, ?_⟩
    rw [smul_totalQuotient_def, hr, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rintro ⟨r, rfl⟩ x hx f hf
    obtain ⟨a, -, rfl⟩ := IsLocalEquationOn.exists_isUnit_eq_mul_germ hg (h hx) hf
    refine ⟨X.presheaf.germ V x hx r * a, ?_⟩
    rw [smul_totalQuotient_def]
    simp only [map_mul]
    rw [germ_toTotalQuotient]
    erw [TopCat.Presheaf.germ_res_apply]
    have hinv : X.totalQuotientSheaf.presheaf.germ U x (h hx)
        (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op U)) *
          X.totalQuotientSheaf.presheaf.germ U x (h hx) (g : _) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination -(stalkToTotalQuotient x (X.presheaf.germ V x hx r) *
      stalkToTotalQuotient x a) * hinv

/-- **Fulton B.4.4.** If `g` is a local equation of the Cartier divisor `D` on `U`, then on every
open `V ⊆ U` the `Γ(V, 𝒪_X)`-module of sections of `𝒪_X(D)` is generated by `g⁻¹|_V`: the
sheaf `𝒪_X(D)` is Fulton's `𝓛_D ⊆ 𝓚`, generated on `U` by `g⁻¹`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
theorem lineBundleSections_eq_span_of_isLocalEquationOn {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) {V : X.Opens}
    (h : V ≤ U) :
    lineBundleSections D V =
      Submodule.span Γ(X, V) {X.totalQuotientSheaf.obj.map (homOfLE h).op (↑g⁻¹ : _)} := by
  ext σ
  rw [mem_lineBundleSections_iff_of_isLocalEquationOn hg h, Submodule.mem_span_singleton]

/-! ### Local equations: products, units and locality -/

/-- The restriction of `D + D'` to `U` is the sum of the restrictions. -/
theorem restrictDivisor_add (D D' : X.CartierDivisor) (U : X.Opens) :
    restrictDivisor (D + D') U = restrictDivisor D U + restrictDivisor D' U := by
  simp only [restrictDivisor, map_add]

/-- The restriction of `-D` to `U` is the negative of the restriction of `D`. -/
theorem restrictDivisor_neg (D : X.CartierDivisor) (U : X.Opens) :
    restrictDivisor (-D) U = -restrictDivisor D U := by
  simp only [restrictDivisor, map_neg]

/-- The restriction of the zero divisor to `U` is zero. -/
theorem restrictDivisor_zero (U : X.Opens) : restrictDivisor (0 : X.CartierDivisor) U = 0 := by
  simp only [restrictDivisor, map_zero]

/-- If `g` and `g'` are local equations of `D` and `D'` on `U`, then `g * g'` is a local equation
of `D + D'` on `U`. -/
theorem IsLocalEquationOn.mul {D D' : X.CartierDivisor} {U : X.Opens}
    {g g' : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g)
    (hg' : IsLocalEquationOn D' U g') : IsLocalEquationOn (D + D') U (g * g') := by
  unfold IsLocalEquationOn at *
  rw [cartierClass_mul, hg, hg', restrictDivisor_add]

/-- If `g` is a local equation of `D` on `U`, then `g⁻¹` is a local equation of `-D` on `U`. -/
theorem IsLocalEquationOn.inv {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) :
    IsLocalEquationOn (-D) U g⁻¹ := by
  unfold IsLocalEquationOn at *
  rw [cartierClass_inv, hg, restrictDivisor_neg]

/-- `1` is a local equation of the zero divisor on every open `U`. -/
theorem isLocalEquationOn_one (U : X.Opens) :
    IsLocalEquationOn (0 : X.CartierDivisor) U 1 := by
  unfold IsLocalEquationOn
  rw [cartierClass_one, restrictDivisor_zero]

/-- `div(f f') = div f + div f'`. -/
theorem principalDivisor_mul (f f' : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    principalDivisor (f * f') = principalDivisor f + principalDivisor f' :=
  map_add (principalHom X) (Additive.ofMul f) (Additive.ofMul f')

/-- `div(f⁻¹) = -div f`. -/
theorem principalDivisor_inv (f : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    principalDivisor f⁻¹ = -principalDivisor f :=
  map_neg (principalHom X) (Additive.ofMul f)

/-- `f|_U` is a local equation of `div(f)` on `U`. -/
theorem isLocalEquationOn_principalDivisor_res (f : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (U : X.Opens) :
    IsLocalEquationOn (principalDivisor f) U (resUnit (homOfLE le_top) f) :=
  isLocalEquationOn_resUnit _ (isLocalEquationOn_principalDivisor f)

/-- A Cartier divisor is determined by local equations on an open cover. -/
theorem eq_of_isLocalEquationOn {D D' : X.CartierDivisor} {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (g : ∀ i, (X.totalQuotientSheaf.obj.obj (op (U i)))ˣ)
    (hD : ∀ i, IsLocalEquationOn D (U i) (g i)) (hD' : ∀ i, IsLocalEquationOn D' (U i) (g i)) :
    D = D' :=
  TopCat.Sheaf.eq_of_locally_eq' (cartierSheaf X) U ⊤ (fun _ => homOfLE le_top) (hU ▸ le_rfl) D D'
    fun i => (hD i).symm.trans (hD' i)

/-- A section of `𝓜_X` that is locally a unit is a unit. -/
theorem isUnit_of_locally {U : X.Opens} (σ : X.totalQuotientSheaf.obj.obj (op U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (i : W ⟶ U), x ∈ W ∧
      IsUnit (X.totalQuotientSheaf.obj.map i.op σ)) : IsUnit σ := by
  choose W i hxW hu using h
  let V : U → X.Opens := fun x => W x.1 x.2
  have hcover : U ≤ iSup V := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW x hx⟩
  have hc : TopCat.Presheaf.IsCompatible X.totalQuotientSheaf.obj V
      (fun x => ((hu x.1 x.2).unit⁻¹ : (X.totalQuotientSheaf.obj.obj (op (V x)))ˣ).1) := by
    intro x y
    have hx' := congrArg (X.totalQuotientSheaf.obj.map (Opens.infLELeft (V x) (V y)).op)
      (hu x.1 x.2).val_inv_mul
    have hy' := congrArg (X.totalQuotientSheaf.obj.map (Opens.infLERight (V x) (V y)).op)
      (hu y.1 y.2).val_inv_mul
    rw [map_mul, map_one, totalQuotient_map_map] at hx' hy'
    have hσ : X.totalQuotientSheaf.obj.map (Opens.infLELeft (V x) (V y) ≫ i x.1 x.2).op σ =
        X.totalQuotientSheaf.obj.map (Opens.infLERight (V x) (V y) ≫ i y.1 y.2).op σ := rfl
    rw [hσ] at hx'
    dsimp only
    exact left_inv_eq_right_inv hx' (by rwa [mul_comm])
  obtain ⟨τ, hτ, -⟩ := X.totalQuotientSheaf.existsUnique_gluing' V U (fun x => i x.1 x.2) hcover
    _ hc
  refine IsUnit.of_mul_eq_one τ (TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf V U
    (fun x => i x.1 x.2) hcover _ _ fun x => ?_)
  rw [map_mul, hτ x, map_one]
  exact (hu x.1 x.2).mul_val_inv

/-- Membership in `Γ(U, 𝒪_X(D))` is a local property. -/
theorem mem_lineBundleSections_of_locally {D : X.CartierDivisor} {U : X.Opens}
    (σ : X.totalQuotientSheaf.obj.obj (op U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (i : W ⟶ U), x ∈ W ∧
      X.totalQuotientSheaf.obj.map i.op σ ∈ lineBundleSections D W) :
    σ ∈ lineBundleSections D U := by
  intro x hx f hf
  obtain ⟨W, i, hxW, hW⟩ := h x hx
  have := hW x hxW f hf
  rwa [show X.totalQuotientSheaf.presheaf.germ W x hxW (X.totalQuotientSheaf.obj.map i.op σ) =
      X.totalQuotientSheaf.presheaf.germ U x hx σ from
    TopCat.Presheaf.germ_res_apply _ _ _ _ _] at this

/-- On the open `U` itself: if `g` is a local equation of `D` on `U`, the sections of `𝒪_X(D)`
over `U` are the multiples of `g⁻¹`. -/
theorem mem_lineBundleSections_iff_of_isLocalEquationOn' {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g)
    (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    σ ∈ lineBundleSections D U ↔ ∃ r : Γ(X, U), toTotalQuotient U r * ↑g⁻¹ = σ := by
  rw [mem_lineBundleSections_iff_of_isLocalEquationOn hg le_rfl]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-! ### Local data of a Cartier divisor (Lazarsfeld (1.1)) -/

/-- **Lazarsfeld (1.1), local data.** A Cartier divisor has local equations on an open cover. -/
@[mmp "lem_p01a_cartier_divisor_local_data"]
theorem exists_cover_isLocalEquationOn (D : X.CartierDivisor) :
    ∃ (U : X → X.Opens) (f : ∀ x, (X.totalQuotientSheaf.obj.obj (op (U x)))ˣ),
      (∀ x, x ∈ U x) ∧ iSup U = ⊤ ∧ ∀ x, IsLocalEquationOn D (U x) (f x) := by
  choose U hxU f hf using exists_isLocalEquationOn D
  exact ⟨U, f, hxU, eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩, hf⟩

/-- **Lazarsfeld (1.1), local data.** Two local equations `f` on `U` and `g` on `V` of the same
Cartier divisor satisfy `f = u g` on `U ∩ V` for a unit `u ∈ Γ(U ∩ V, 𝒪_X^*)`. -/
@[mmp "lem_p01a_cartier_divisor_local_data"]
theorem IsLocalEquationOn.exists_units_eq_mul {D : X.CartierDivisor} {U V : X.Opens}
    {f : (X.totalQuotientSheaf.obj.obj (op U))ˣ} {g : (X.totalQuotientSheaf.obj.obj (op V))ˣ}
    (hf : IsLocalEquationOn D U f) (hg : IsLocalEquationOn D V g) :
    ∃ u : Γ(X, U ⊓ V)ˣ, resUnit (homOfLE inf_le_left) f =
      Units.map (toTotalQuotient (U ⊓ V)).toMonoidHom u * resUnit (homOfLE inf_le_right) g := by
  obtain ⟨u, hu⟩ := MMP.CartierDivisorSheaf.exists_units_eq_mul_inv
    (isLocalEquationOn_resUnit (homOfLE (inf_le_left : U ⊓ V ≤ U)) hf)
    (isLocalEquationOn_resUnit (homOfLE (inf_le_right : U ⊓ V ≤ V)) hg)
  refine ⟨u, ?_⟩
  change _ = Units.map (MMP.CartierDivisorSheaf.toK (U ⊓ V)).toMonoidHom u * _
  rw [hu, inv_mul_cancel_right]

/-- **Lazarsfeld (1.1), local data, sums.** If `f` and `f'` are local equations of `D` and `D'` on
`U`, then `f f'` is a local equation of `D + D'` on `U`. -/
@[mmp "lem_p01a_cartier_divisor_local_data"]
theorem isLocalEquationOn_add {D D' : X.CartierDivisor} {U : X.Opens}
    {f f' : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hf : IsLocalEquationOn D U f)
    (hf' : IsLocalEquationOn D' U f') : IsLocalEquationOn (D + D') U (f * f') :=
  hf.mul hf'

/-- **Lazarsfeld (1.1), local data, sums.** Two Cartier divisors have local equations `fᵢ`, `fᵢ'`
on a common open cover, and `fᵢ fᵢ'` is then a local equation of `D + D'`. -/
@[mmp "lem_p01a_cartier_divisor_local_data"]
theorem exists_cover_isLocalEquationOn_add (D D' : X.CartierDivisor) :
    ∃ (U : X → X.Opens) (f f' : ∀ x, (X.totalQuotientSheaf.obj.obj (op (U x)))ˣ),
      (∀ x, x ∈ U x) ∧ iSup U = ⊤ ∧ (∀ x, IsLocalEquationOn D (U x) (f x)) ∧
        (∀ x, IsLocalEquationOn D' (U x) (f' x)) ∧
          ∀ x, IsLocalEquationOn (D + D') (U x) (f x * f' x) := by
  choose U hxU f hf using exists_isLocalEquationOn D
  choose U' hxU' f' hf' using exists_isLocalEquationOn D'
  refine ⟨fun x => U x ⊓ U' x, fun x => resUnit (homOfLE inf_le_left) (f x),
    fun x => resUnit (homOfLE inf_le_right) (f' x), fun x => ⟨hxU x, hxU' x⟩,
    eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x, hxU' x⟩,
    fun x => isLocalEquationOn_resUnit _ (hf x), fun x => isLocalEquationOn_resUnit _ (hf' x),
    fun x => (isLocalEquationOn_resUnit _ (hf x)).mul (isLocalEquationOn_resUnit _ (hf' x))⟩

/-! ### The stalkwise condition and `MMP.CartierDivisor.sheaf` -/

/-- The stalkwise condition `lineBundleSections D V` is membership in the sections of the sheaf
`MMP.CartierDivisor.sheaf D`. -/
@[mmp "def_p01a_line_bundle_of_divisor"]
theorem mem_lineBundleSections_iff_mem (D : X.CartierDivisor) (V : X.Opens)
    (σ : X.totalQuotientSheaf.obj.obj (op V)) :
    σ ∈ lineBundleSections D V ↔ MMP.CartierDivisorSheaf.Mem D V σ := by
  constructor
  · intro hσ W h f hf
    obtain ⟨r, hr⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn' hf _).1 (res_mem D h hσ)
    refine ⟨r, ?_⟩
    change toTotalQuotient W r = X.totalQuotientSheaf.obj.map (homOfLE h).op σ * f
    rw [← hr, mul_assoc, Units.inv_mul, mul_one]
  · rintro hσ x hx _ ⟨U', hxU', g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hσ (V ⊓ U') inf_le_left (resUnit (homOfLE inf_le_right) g)
      (isLocalEquationOn_resUnit _ hg)
    have hxV : x ∈ V ⊓ U' := ⟨hx, hxU'⟩
    refine ⟨X.presheaf.germ (V ⊓ U') x hxV a, ?_⟩
    rw [← germ_toTotalQuotient, ha, map_mul]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-! ### Sections of tensor products -/

/-- The image of `s ⊗ t` in `Γ(V, L ⊗ N)`. -/
abbrev tensorSection {L N : X.Modules} {V : X.Opens} (s : Γ(L, V)) (t : Γ(N, V)) :=
  PresheafOfModules.Hom.app (MMP.CartierDivisorSheaf.tensorUnit L N) (op V)
    (s ⊗ₜ[X.sheaf.obj.obj (op V)] t)

/-! ### Effective divisors -/

/-- The map `Γ(-, 𝒪_X) → Γ(-, 𝓜_X)` commutes with restriction along `V ⊆ U`. -/
theorem toTotalQuotient_map {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    toTotalQuotient V (X.presheaf.map i.op r) =
      X.totalQuotientSheaf.obj.map i.op (toTotalQuotient U r) :=
  toTotalQuotient_res i.le r

/-- A regular function whose image in `𝓜_X` is a unit is a non-zero-divisor at every point. -/
theorem germ_mem_nonZeroDivisors_of_isUnit {U : X.Opens} {r : Γ(X, U)}
    (hr : IsUnit (toTotalQuotient U r)) (x : X) (hx : x ∈ U) :
    X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  refine mem_nonZeroDivisors_of_injective (stalkToTotalQuotient_injective x) ?_
  rw [← germ_toTotalQuotient]
  exact (hr.map _).mem_nonZeroDivisors

/-- For an effective divisor, `1 ∈ Γ(U, 𝒪_X(D))`. -/
@[mmp "lem_p01a_effective_divisor_canonical_section"]
theorem one_mem_lineBundleSections {D : X.CartierDivisor} (hD : IsEffective D) (U : X.Opens) :
    (1 : X.totalQuotientSheaf.obj.obj (op U)) ∈ lineBundleSections D U := by
  intro x hx f hf
  obtain ⟨W, hxW, s, hs, hsD⟩ := hD x
  obtain ⟨a, -, rfl⟩ := IsLocalEquationOn.exists_isUnit_eq_mul_germ hsD hxW hf
  refine ⟨a * X.presheaf.germ W x hxW s, ?_⟩
  rw [map_one, one_mul, map_mul, ← germ_toTotalQuotient]
  rfl

/-- The basis section of a sectionwise trivialization is a trivializing generator. -/
theorem isTrivializingGenerator_basis {M : X.Modules} {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) :
    IsTrivializingGenerator M V (Stacks.NonvanishingOpen.basis t) := by
  intro W h
  have key : ∀ r : Γ(X, W), Stacks.NonvanishingOpen.triv t (homOfLE h)
      (r • M.presheaf.map (homOfLE h).op (Stacks.NonvanishingOpen.basis t)) = r := fun r => by
    rw [Stacks.NonvanishingOpen.triv_smul, Stacks.NonvanishingOpen.triv_res_basis, mul_one]
  exact ⟨fun r r' hrr => (key r).symm.trans ((congrArg _ hrr).trans (key r')),
    fun m => ⟨Stacks.NonvanishingOpen.triv t (homOfLE h) m,
      (t.θ W (homOfLE h)).injective (key _)⟩⟩

/-- If `r ∈ Γ(U, 𝒪_X)` is a local equation of `D` on `U`, then a point `x ∈ U` lies outside
`Supp D` exactly when `r` is a unit at `x`. -/
theorem notMem_cartierSupport_iff_isUnit_germ {D : X.CartierDivisor} {U : X.Opens}
    {r : Γ(X, U)} (h : IsUnit (toTotalQuotient U r)) (hD : IsLocalEquationOn D U h.unit)
    {x : X} (hx : x ∈ U) :
    x ∉ cartierSupport D ↔ IsUnit (X.presheaf.germ U x hx r) := by
  have hgerm : (cartierSheaf X).presheaf.germ ⊤ x trivial D =
      (cartierSheaf X).presheaf.germ U x hx (cartierClass U h.unit) := by
    rw [hD, restrictDivisor]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  simp only [cartierSupport, Set.mem_ofPred_eq, not_not, hgerm]
  constructor
  · intro h0
    rw [← map_zero (ConcreteCategory.hom ((cartierSheaf X).presheaf.germ U x hx))] at h0
    obtain ⟨W, hxW, i₁, i₂, heq⟩ := (cartierSheaf X).presheaf.germ_eq x hx hx _ _ h0
    rw [← cartierClass_resUnit, map_zero] at heq
    have h1 : IsLocalEquationOn 0 W (resUnit i₁ h.unit) := by
      unfold IsLocalEquationOn
      rw [heq, restrictDivisor_zero]
    obtain ⟨W', k, hxW', u, hu⟩ := (isLocalEquationOn_one W).exists_unit_mul_eq h1 hxW
    have hu' : (u : Γ(X, W')) = X.presheaf.map (homOfLE k ≫ i₁).op r := by
      apply injective_toTotalQuotient
      rw [toTotalQuotient_map, ← totalQuotient_map_map]
      simp only [Units.val_one, map_one, mul_one] at hu
      exact hu
    rw [← X.presheaf.germ_res_apply (homOfLE k ≫ i₁) x hxW', ← hu']
    exact u.isUnit.map _
  · intro hu
    have hxW : x ∈ X.basicOpen r := (X.mem_basicOpen r x hx).2 hu
    have hres : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r) :=
      X.toRingedSpace.isUnit_res_basicOpen r
    have e : resUnit (homOfLE (X.basicOpen_le r)) h.unit =
        Units.map (toTotalQuotient (X.basicOpen r)).toMonoidHom hres.unit :=
      Units.ext (by simp [toTotalQuotient_res])
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (X.basicOpen_le r)) x hxW,
      ← cartierClass_resUnit, e, cartierClass_map_units, map_zero]

/-- The zero divisor is effective. -/
theorem isEffective_zero : IsEffective (0 : X.CartierDivisor) := by
  intro x
  refine ⟨⊤, trivial, 1, by simp, ?_⟩
  convert isLocalEquationOn_one (X := X) ⊤
  ext
  simp

/-- The sum of two effective divisors is effective. -/
theorem IsEffective.add {D D' : X.CartierDivisor} (hD : IsEffective D) (hD' : IsEffective D') :
    IsEffective (D + D') := by
  intro x
  obtain ⟨U, hxU, s, hs, hsD⟩ := hD x
  obtain ⟨U', hxU', s', hs', hsD'⟩ := hD' x
  have hx : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
  have hmul : IsUnit (toTotalQuotient (U ⊓ U') (X.presheaf.map (homOfLE inf_le_left).op s *
      X.presheaf.map (homOfLE inf_le_right).op s')) := by
    rw [map_mul, toTotalQuotient_res, toTotalQuotient_res]
    exact (hs.map _).mul (hs'.map _)
  refine ⟨U ⊓ U', hx, _, hmul, ?_⟩
  have := (isLocalEquationOn_resUnit (homOfLE (inf_le_left : U ⊓ U' ≤ U)) hsD).mul
    (isLocalEquationOn_resUnit (homOfLE (inf_le_right : U ⊓ U' ≤ U')) hsD')
  convert this using 1
  ext
  simp [toTotalQuotient_res]

/-- A natural multiple of an effective divisor is effective. -/
theorem IsEffective.nsmul {D : X.CartierDivisor} (hD : IsEffective D) (q : ℕ) :
    IsEffective (q • D) := by
  induction q with
  | zero => simpa using isEffective_zero
  | succ q ih => simpa [succ_nsmul] using ih.add hD

/-! ### Multiplication by a global unit of `𝓜_X` -/

/-- Multiplication by `c⁻¹` maps `Γ(V, 𝒪_X(D))` into `Γ(V, 𝒪_X(D + div c))`. -/
theorem mul_mem_lineBundleSections_add_principalDivisor {D : X.CartierDivisor}
    (c : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) {V : X.Opens}
    {σ : X.totalQuotientSheaf.obj.obj (op V)} (hσ : σ ∈ lineBundleSections D V) :
    X.totalQuotientSheaf.obj.map (homOfLE le_top).op (↑c⁻¹ : X.totalQuotientSheaf.obj.obj (op ⊤)) *
      σ ∈ lineBundleSections (D + principalDivisor c) V := by
  rintro x hx _ ⟨U', hxU', g, hg, rfl⟩
  have hD : IsLocalEquationOn D U' (g * resUnit (homOfLE le_top) c⁻¹) := by
    have := hg.mul (isLocalEquationOn_principalDivisor_res c⁻¹ U')
    rwa [principalDivisor_inv, add_neg_cancel_right] at this
  have h := hσ x hx _ ⟨U', hxU', _, hD, rfl⟩
  convert h using 1
  simp only [map_mul, Units.val_mul, Units.coe_map]
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  ring

/-- Multiplication by `c` maps `Γ(V, 𝒪_X(D + div c))` into `Γ(V, 𝒪_X(D))`. -/
theorem mul_mem_lineBundleSections_of_add_principalDivisor {D : X.CartierDivisor}
    (c : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) {V : X.Opens}
    {τ : X.totalQuotientSheaf.obj.obj (op V)}
    (hτ : τ ∈ lineBundleSections (D + principalDivisor c) V) :
    X.totalQuotientSheaf.obj.map (homOfLE le_top).op
      (↑c⁻¹⁻¹ : X.totalQuotientSheaf.obj.obj (op ⊤)) * τ ∈ lineBundleSections D V := by
  have := mul_mem_lineBundleSections_add_principalDivisor c⁻¹ hτ
  rwa [principalDivisor_inv, add_neg_cancel_right] at this

/-- An isomorphism of `𝒪_X`-modules carries trivializing generators to trivializing generators. -/
theorem IsTrivializingGenerator.map_iso {L L' : X.Modules} (φ : L ≅ L') {U : X.Opens}
    {e : Γ(L, U)} (he : IsTrivializingGenerator L U e) :
    IsTrivializingGenerator L' U (φ.hom.val.app (op U) e) := by
  intro V h
  have hfun : (fun r : Γ(X, V) => r • L'.presheaf.map (homOfLE h).op (φ.hom.val.app (op U) e)) =
      (φ.hom.val.app (op V)) ∘ (fun r : Γ(X, V) => r • L.presheaf.map (homOfLE h).op e) := by
    funext r
    refine Eq.trans ?_ ((φ.hom.val.app (op V)).hom.map_smul r _).symm
    congr 1
    exact (PresheafOfModules.naturality_apply φ.hom.val (homOfLE h).op e).symm
  rw [hfun]
  exact (((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op V)).mapIso
    φ).toLinearEquiv.bijective).comp (he V h)

/-! ### Ratios of sections by a regular section -/

/-- Restricting a section of an `𝒪_X`-module along `U ⊆ U` is the identity. -/
theorem modules_map_id (L : X.Modules) {U : X.Opens} (m : Γ(L, U)) :
    L.presheaf.map (homOfLE (le_refl U)).op m = m := by
  rw [show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restricting a section of an `𝒪_X`-module along `V ⊆ U` and then along `W ⊆ V` is restricting
it along `W ⊆ U`. -/
theorem modules_map_map (L : X.Modules) {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V)
    (m : Γ(L, U)) :
    L.presheaf.map (homOfLE h').op (L.presheaf.map (homOfLE h).op m) =
      L.presheaf.map (homOfLE (h'.trans h)).op m := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of `𝓜_X` along `U ⊆ U` is the identity. -/
theorem totalQuotient_map_id {U : X.Opens} (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    X.totalQuotientSheaf.obj.map (homOfLE (le_refl U)).op σ = σ := by
  rw [show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restricting a section of `𝒪_X` along `U ⊆ U` is the identity. -/
theorem presheaf_map_id {U : X.Opens} (r : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_refl U)).op r = r := by
  rw [show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The restriction to `V ⊆ U` of a trivializing generator of `L` on `U` is a trivializing
generator of `L` on `V`. -/
theorem IsTrivializingGenerator.res {L : X.Modules} {U V : X.Opens} {e : Γ(L, U)}
    (he : IsTrivializingGenerator L U e) (h : V ≤ U) :
    IsTrivializingGenerator L V (L.presheaf.map (homOfLE h).op e) := by
  intro W hW
  simp only [modules_map_map]
  exact he W (hW.trans h)

/-- If `e` is a trivializing generator of `L` on `U`, then `r ↦ r • e` is a bijection
`Γ(U, 𝒪_X) → Γ(U, L)`. -/
theorem IsTrivializingGenerator.bijective {L : X.Modules} {U : X.Opens} {e : Γ(L, U)}
    (he : IsTrivializingGenerator L U e) : Function.Bijective fun r : Γ(X, U) => r • e := by
  simpa only [modules_map_id] using he U le_rfl

/-- An invertible module has trivializing generators near every point of every open. -/
theorem exists_isTrivializingGenerator (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens) (_ : U ≤ V) (e : Γ(L, U)), x ∈ U ∧ IsTrivializingGenerator L U e := by
  obtain ⟨W, hW, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ W z := Opens.mem_iSup.mp (hW ▸ Opens.mem_top x)
  obtain ⟨t⟩ := htriv z
  have hxV : x ∈ V ⊓ W z := ⟨hx, hz⟩
  exact ⟨V ⊓ W z, inf_le_left, _, hxV, (isTrivializingGenerator_basis t).res inf_le_right⟩

/-- In a commutative ring, if `p` is a unit, `a p = q` and `q' p = q p'`, then `a p' = q'`. -/
theorem mul_eq_of_mul_eq_of_isUnit {A : Type*} [CommRing A] {a p q p' q' : A} (hp : IsUnit p)
    (h1 : a * p = q) (h : q' * p = q * p') : a * p' = q' := by
  apply hp.mul_right_cancel
  rw [h, ← h1]
  ring

section DivisorOfSection

variable {L : X.Modules} {s : Γ(L, ⊤)} {D : X.CartierDivisor}

variable (L s) in
/-- `ρ ∈ Γ(V, 𝓜_X)` is the ratio `t / s` of a section `t ∈ Γ(V, L)` by the regular global
section `s`: on every trivializing open `U ⊆ V`, with `s|_U = r e` and `t|_U = b e`, `ρ r = b`. -/
def IsRatio {V : X.Opens} (t : Γ(L, V)) (ρ : X.totalQuotientSheaf.obj.obj (op V)) : Prop :=
  ∀ (U : X.Opens) (hU : U ≤ V) (e : Γ(L, U)), IsTrivializingGenerator L U e → ∀ r b : Γ(X, U),
    L.presheaf.map (homOfLE le_top).op s = r • e → L.presheaf.map (homOfLE hU).op t = b • e →
      X.totalQuotientSheaf.obj.map (homOfLE hU).op ρ * toTotalQuotient U r = toTotalQuotient U b

/-- Two trivializations give the same ratio `t / s` on the overlap (cross-multiplied). -/
theorem cross_mul_eq {V : X.Opens} (t : Γ(L, V)) {U U' W : X.Opens} (hU : U ≤ V)
    (hU' : U' ≤ V) (hW : W ≤ U) (hW' : W ≤ U') {e : Γ(L, U)} {e' : Γ(L, U')}
    (he : IsTrivializingGenerator L U e) {r b : Γ(X, U)} {r' b' : Γ(X, U')}
    (hr : L.presheaf.map (homOfLE le_top).op s = r • e)
    (hb : L.presheaf.map (homOfLE hU).op t = b • e)
    (hr' : L.presheaf.map (homOfLE le_top).op s = r' • e')
    (hb' : L.presheaf.map (homOfLE hU').op t = b' • e') :
    X.presheaf.map (homOfLE hW).op b * X.presheaf.map (homOfLE hW').op r' =
      X.presheaf.map (homOfLE hW').op b' * X.presheaf.map (homOfLE hW).op r := by
  obtain ⟨c, hc⟩ := (he.res hW).bijective.2 (L.presheaf.map (homOfLE hW').op e')
  have hinj := (he.res hW).bijective.1
  have hs1 : L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      X.presheaf.map (homOfLE hW).op r • L.presheaf.map (homOfLE hW).op e := by
    rw [← modules_map_map L (le_top : U ≤ ⊤) hW, hr, Scheme.Modules.map_smul]
  have hs2 : L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      X.presheaf.map (homOfLE hW').op r' • L.presheaf.map (homOfLE hW').op e' := by
    rw [← modules_map_map L (le_top : U' ≤ ⊤) hW', hr', Scheme.Modules.map_smul]
  have ht1 : L.presheaf.map (homOfLE (hW.trans hU)).op t =
      X.presheaf.map (homOfLE hW).op b • L.presheaf.map (homOfLE hW).op e := by
    rw [← modules_map_map L hU hW, hb, Scheme.Modules.map_smul]
  have ht2 : L.presheaf.map (homOfLE (hW.trans hU)).op t =
      X.presheaf.map (homOfLE hW').op b' • L.presheaf.map (homOfLE hW').op e' := by
    rw [← modules_map_map L hU' hW', hb', Scheme.Modules.map_smul]
  rw [← hc, smul_smul] at hs2 ht2
  have h1 : X.presheaf.map (homOfLE hW).op r = X.presheaf.map (homOfLE hW').op r' * c :=
    hinj (hs1.symm.trans hs2)
  have h2 : X.presheaf.map (homOfLE hW).op b = X.presheaf.map (homOfLE hW').op b' * c :=
    hinj (ht1.symm.trans ht2)
  rw [h1, h2]
  ring

/-- The identity of `MMP.Intersection.cross_mul_eq`, read in `Γ(W, 𝓜_X)`. -/
theorem toTotalQuotient_cross_mul_eq {V : X.Opens} (t : Γ(L, V)) {U U' W : X.Opens} (hU : U ≤ V)
    (hU' : U' ≤ V) (hW : W ≤ U) (hW' : W ≤ U') {e : Γ(L, U)} {e' : Γ(L, U')}
    (he : IsTrivializingGenerator L U e) {r b : Γ(X, U)} {r' b' : Γ(X, U')}
    (hr : L.presheaf.map (homOfLE le_top).op s = r • e)
    (hb : L.presheaf.map (homOfLE hU).op t = b • e)
    (hr' : L.presheaf.map (homOfLE le_top).op s = r' • e')
    (hb' : L.presheaf.map (homOfLE hU').op t = b' • e') :
    X.totalQuotientSheaf.obj.map (homOfLE hW).op (toTotalQuotient U b) *
        X.totalQuotientSheaf.obj.map (homOfLE hW').op (toTotalQuotient U' r') =
      X.totalQuotientSheaf.obj.map (homOfLE hW').op (toTotalQuotient U' b') *
        X.totalQuotientSheaf.obj.map (homOfLE hW).op (toTotalQuotient U r) := by
  have := congrArg (toTotalQuotient W) (cross_mul_eq t hU hU' hW hW' he hr hb hr' hb')
  simpa only [map_mul, toTotalQuotient_res] using this

/-- Trivializing data for `s` and `t` around every point of `V`. -/
theorem exists_trivializingData [Stacks.Ample.IsInvertibleModule X L]
    {V : X.Opens} (t : Γ(L, V)) {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens) (hU : U ≤ V) (e : Γ(L, U)) (_ : IsTrivializingGenerator L U e)
      (r b : Γ(X, U)), x ∈ U ∧ L.presheaf.map (homOfLE le_top).op s = r • e ∧
        L.presheaf.map (homOfLE hU).op t = b • e := by
  obtain ⟨U, hU, e, hxU, he⟩ := exists_isTrivializingGenerator L hx
  obtain ⟨r, hr⟩ := he.bijective.2 (L.presheaf.map (homOfLE le_top).op s)
  obtain ⟨b, hb⟩ := he.bijective.2 (L.presheaf.map (homOfLE hU).op t)
  exact ⟨U, hU, e, he, r, b, hxU, hr.symm, hb.symm⟩

/-- For a regular global section `s` of an invertible module `L`, the ratio `t / s` is unique. -/
theorem IsRatio.unique [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) {V : X.Opens} {t : Γ(L, V)}
    {ρ ρ' : X.totalQuotientSheaf.obj.obj (op V)} (h : IsRatio L s t ρ) (h' : IsRatio L s t ρ') :
    ρ = ρ' := by
  choose U hU e he r b hxU hr hb using fun x : V => exists_trivializingData (s := s) t x.2
  refine TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf U V (fun x => homOfLE (hU x))
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩) _ _ fun x => ?_
  exact (hs.2.2 _ _ (he x) _ (hr x)).1.mul_right_cancel
    ((h _ (hU x) _ (he x) _ _ (hr x) (hb x)).trans (h' _ (hU x) _ (he x) _ _ (hr x) (hb x)).symm)

/-- For a regular global section `s` of an invertible module `L`, every section `t` of `L` over
`V` has a ratio `t / s ∈ Γ(V, 𝓜_X)`. -/
theorem exists_isRatio [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) {V : X.Opens} (t : Γ(L, V)) :
    ∃ ρ, IsRatio L s t ρ := by
  choose U hU e he r b hxU hr hb using fun x : V => exists_trivializingData (s := s) t x.2
  have hunit : ∀ x, IsUnit (toTotalQuotient (U x) (r x)) := fun x =>
    (hs.2.2 _ _ (he x) _ (hr x)).1
  let ρ : ∀ x, X.totalQuotientSheaf.obj.obj (op (U x)) := fun x =>
    toTotalQuotient (U x) (b x) * ↑(hunit x).unit⁻¹
  have hρ : ∀ x, ρ x * toTotalQuotient (U x) (r x) = toTotalQuotient (U x) (b x) := fun x => by
    simp only [ρ, mul_assoc]
    rw [(hunit x).val_inv_mul, mul_one]
  have hcover : V ≤ iSup U := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩
  have hc : TopCat.Presheaf.IsCompatible X.totalQuotientSheaf.obj U ρ := by
    intro x y
    have hcr := toTotalQuotient_cross_mul_eq t (hU x) (hU y) inf_le_left inf_le_right (he x)
      (hr x) (hb x) (hr y) (hb y)
    have hx' := congrArg (X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left :
      U x ⊓ U y ≤ U x)).op) (hρ x)
    have hy' := congrArg (X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right :
      U x ⊓ U y ≤ U y)).op) (hρ y)
    rw [map_mul] at hx' hy'
    have h1 := mul_eq_of_mul_eq_of_isUnit ((hunit y).map _) hy' hcr
    exact ((hunit x).map _).mul_right_cancel (hx'.trans h1.symm)
  obtain ⟨ρg, hρg, -⟩ := X.totalQuotientSheaf.existsUnique_gluing' U V (fun x => homOfLE (hU x))
    hcover ρ hc
  refine ⟨ρg, fun U' hU' e' he' r' b' hr' hb' => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf (fun x => U' ⊓ U x) U'
    (fun x => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hU' hy⟩, hy, hxU ⟨y, hU' hy⟩⟩) _ _ fun x => ?_
  have hcr := toTotalQuotient_cross_mul_eq t (hU x) hU' inf_le_right inf_le_left (he x)
    (hr x) (hb x) hr' hb'
  have hx' := congrArg (X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right :
    U' ⊓ U x ≤ U x)).op) (hρ x)
  rw [map_mul, ← hρg x, totalQuotient_map_map] at hx'
  change X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : U' ⊓ U x ≤ U')).op
    (X.totalQuotientSheaf.obj.map (homOfLE hU').op ρg * toTotalQuotient U' r') =
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : U' ⊓ U x ≤ U')).op
        (toTotalQuotient U' b')
  rw [map_mul, totalQuotient_map_map]
  exact mul_eq_of_mul_eq_of_isUnit ((hunit x).map _) hx' hcr.symm

/-- The ratio `t / s ∈ Γ(V, 𝓜_X)`. -/
def ratio [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) {V : X.Opens} (t : Γ(L, V)) :
    X.totalQuotientSheaf.obj.obj (op V) :=
  (exists_isRatio hs t).choose

/-- `ratio hs t` is the ratio `t / s`. -/
theorem isRatio_ratio [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) {V : X.Opens} (t : Γ(L, V)) :
    IsRatio L s t (ratio hs t) :=
  (exists_isRatio hs t).choose_spec

/-- If `s` is a regular global section of `L` with divisor `D`, the ratio `t / s` of a section
`t ∈ Γ(V, L)` lies in `Γ(V, 𝒪_X(D))`. -/
theorem IsRatio.mem [Stacks.Ample.IsInvertibleModule X L]
    (hs : IsDivisorOfSection L s D) {V : X.Opens} {t : Γ(L, V)}
    {ρ : X.totalQuotientSheaf.obj.obj (op V)} (h : IsRatio L s t ρ) :
    ρ ∈ lineBundleSections D V := by
  refine mem_lineBundleSections_of_locally _ fun x hx => ?_
  obtain ⟨U, hU, e, he, r, b, hxU, hr, hb⟩ := exists_trivializingData (s := s) t hx
  obtain ⟨hu, hloc⟩ := hs.2.2 U e he r hr
  refine ⟨U, homOfLE hU, hxU, (mem_lineBundleSections_iff_of_isLocalEquationOn' hloc _).2
    ⟨b, ?_⟩⟩
  rw [← h U hU e he r b hr hb, mul_assoc, hu.mul_val_inv, mul_one]

/-- `(t + t') / s = t / s + t' / s`. -/
theorem IsRatio.add {V : X.Opens} {t t' : Γ(L, V)} {ρ ρ' : X.totalQuotientSheaf.obj.obj (op V)}
    (h : IsRatio L s t ρ) (h' : IsRatio L s t' ρ') : IsRatio L s (t + t') (ρ + ρ') := by
  intro U hU e he r b hr hb
  obtain ⟨b₁, hb₁⟩ := he.bijective.2 (L.presheaf.map (homOfLE hU).op t)
  obtain ⟨b₂, hb₂⟩ := he.bijective.2 (L.presheaf.map (homOfLE hU).op t')
  have hb' : b = b₁ + b₂ := he.bijective.1 (by
    change b • e = (b₁ + b₂) • e
    rw [← hb, add_smul, map_add]
    exact congrArg₂ (· + ·) hb₁.symm hb₂.symm)
  rw [map_add, add_mul, h U hU e he r b₁ hr hb₁.symm, h' U hU e he r b₂ hr hb₂.symm, hb',
    map_add]

/-- `(a • t) / s = a · (t / s)` for `a ∈ Γ(V, 𝒪_X)`. -/
theorem IsRatio.smul {V : X.Opens} {t : Γ(L, V)} {ρ : X.totalQuotientSheaf.obj.obj (op V)}
    (h : IsRatio L s t ρ) (a : Γ(X, V)) : IsRatio L s (a • t) (toTotalQuotient V a * ρ) := by
  intro U hU e he r b hr hb
  obtain ⟨b₁, hb₁⟩ := he.bijective.2 (L.presheaf.map (homOfLE hU).op t)
  have hb' : b = X.presheaf.map (homOfLE hU).op a * b₁ := he.bijective.1 (by
    change b • e = (X.presheaf.map (homOfLE hU).op a * b₁) • e
    rw [← hb, mul_smul, Scheme.Modules.map_smul]
    exact congrArg _ hb₁.symm)
  rw [map_mul, mul_assoc, h U hU e he r b₁ hr hb₁.symm, hb', map_mul, toTotalQuotient_res]

/-- The restriction of `t / s` to `V' ⊆ V` is the ratio `t|_{V'} / s`. -/
theorem IsRatio.res {V : X.Opens} {t : Γ(L, V)} {ρ : X.totalQuotientSheaf.obj.obj (op V)}
    (h : IsRatio L s t ρ) {V' : X.Opens} (hV : V' ≤ V) :
    IsRatio L s (L.presheaf.map (homOfLE hV).op t)
      (X.totalQuotientSheaf.obj.map (homOfLE hV).op ρ) := by
  intro U hU e he r b hr hb
  rw [modules_map_map] at hb
  rw [totalQuotient_map_map]
  exact h U (hU.trans hV) e he r b hr hb

/-- `s / s = 1`. -/
theorem isRatio_one : IsRatio L s s 1 := by
  intro U hU e he r b hr hb
  have : r = b := he.bijective.1 (hr.symm.trans hb)
  rw [map_one, one_mul, this]

end DivisorOfSection

end LineBundle

end MMP.Intersection
