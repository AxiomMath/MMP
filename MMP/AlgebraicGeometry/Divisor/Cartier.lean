module

public import MMP.AlgebraicGeometry.Variety.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# Cartier divisors (Lazarsfeld §1.1.A, Fulton B.4)

Let `X` be a scheme, `𝓜_X = 𝒦_X` its sheaf of total quotient rings (the Stacks project's
`AlgebraicGeometry.Scheme.totalQuotientSheaf`, the sheafification of `U ↦ S(U)⁻¹ Γ(U, 𝒪_X)`
where `S(U)` consists of the sections whose germs are non-zero-divisors everywhere on `U`). A
*Cartier divisor* is a global section of `𝓜_X^*/𝒪_X^*`; the Stacks project's
`AlgebraicGeometry.Scheme.CartierDivisor`, with group structure that of the global sections of
a sheaf of abelian groups (unit groups written additively).

This file makes the notions attached to a Cartier divisor precise.

## Main definitions

* `MMP.Intersection.cartierClass`: the class in `Γ(U, 𝓜^*/𝒪^*)` of a unit of `Γ(U, 𝓜_X)`.
* `MMP.Intersection.IsLocalEquationOn`, `MMP.Intersection.IsLocalEquationAt`: local equations
  of a divisor on an open set and at a point.
* `MMP.Intersection.IsEffective`, `MMP.Intersection.EffectiveLE`: effective divisors and the
  order `D ≽ D'`.
* `MMP.Intersection.cartierSupport`: the support `Supp D`.
* `MMP.Intersection.principalDivisor`, `MMP.Intersection.principalSubgroup`,
  `MMP.Intersection.LinearlyEquivalent`: principal divisors and linear equivalence.
* `MMP.Intersection.IsGivenByLocalEquations`: Fulton's description of a divisor by an affine
  open cover and local equations.
* `MMP.Intersection.associatedSubvariety`, `MMP.Intersection.IsAssociatedSubvariety`:
  associated subvarieties of a sheaf of modules.
* `MMP.Intersection.PullbackCondition`, `MMP.Intersection.IsPullback`: pull-backs of divisors.
* `MMP.Intersection.IsSubschemeOfEffective`, `MMP.Intersection.IsEffectiveCartierSubscheme`:
  the closed subscheme of an effective Cartier divisor.

## Implementation notes

The stalk `D_x` of a divisor is its germ in the stalk of `𝓜^*/𝒪^*`, and an element `f` of
`𝓜_{X,x}` is a local equation at `x` when it is the germ of a local equation on some open
neighbourhood of `x`; since `𝓜^*/𝒪^*` is the sheafification of the sectionwise quotient and
the units of a stalk are the germs of units, this is the statement that the class of `f` is the
germ `D_x`.

Lazarsfeld writes a local equation at `x` as a fraction `a/b` of elements of `𝒪_{X,x}`. In
`IsPullback` and in the order along a subvariety this is stated as: the image of `b` in
`𝓜_{X,x}` is a unit and `b · f = a` for a local equation `f` of the divisor at `x`, i.e.
`f = a/b`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace MMP.Intersection

variable {X Y : Scheme.{u}}

/-! ### The sheaf `𝓜^*/𝒪^*` and local equations -/

variable (X) in
/-- The sheaf `𝓜_X^*/𝒪_X^*` (written additively) whose global sections are the Cartier
divisors. -/
@[mmp "def_p01a_cartier_divisor", mmp "def_b_cartier_divisor"]
abbrev cartierSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  unitGroupQuotientSheaf X.toTotalQuotientSheaf

/-- The map `Γ(U, 𝒪_X) → Γ(U, 𝓜_X)`. -/
abbrev toTotalQuotient (U : X.Opens) : Γ(X, U) →+* X.totalQuotientSheaf.obj.obj (op U) :=
  (X.toTotalQuotientSheaf.hom.app (op U)).hom

/-- The map of stalks `𝒪_{X,x} → 𝓜_{X,x}`. -/
abbrev stalkToTotalQuotient (x : X) :
    X.presheaf.stalk x →+* X.totalQuotientSheaf.presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor _ x).map X.toTotalQuotientSheaf.hom).hom

/-- The class in `Γ(U, 𝓜^*/𝒪^*)` of a unit `g` of `Γ(U, 𝓜_X)`. -/
@[mmp "def_p01a_cartier_divisor", mmp "def_b_cartier_divisor"]
def cartierClass (U : X.Opens) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    (cartierSheaf X).obj.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology X) (unitGroupPresheaf X.totalQuotientSheaf) ≫
    (unitGroupQuotientMap X.toTotalQuotientSheaf).hom).app (op U) (Additive.ofMul g)

/-- The restriction `D|_U` of a Cartier divisor to an open set. -/
@[mmp "def_p01a_cartier_divisor"]
def restrictDivisor (D : X.CartierDivisor) (U : X.Opens) : (cartierSheaf X).obj.obj (op U) :=
  (cartierSheaf X).obj.map (homOfLE le_top).op D

/-- A unit `g ∈ Γ(U, 𝓜_X^*)` is a *local equation* of `D` on `U` if its class is `D|_U`. -/
@[mmp "def_p01a_cartier_divisor", mmp "def_b_cartier_divisor"]
def IsLocalEquationOn (D : X.CartierDivisor) (U : X.Opens)
    (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) : Prop :=
  cartierClass U g = restrictDivisor D U

/-- An element `f ∈ 𝓜_{X,x}` is a *local equation* of `D` at `x` if its class is the germ `D_x`,
i.e. it is the germ at `x` of a local equation of `D` on an open neighbourhood of `x`. -/
@[mmp "def_p01a_cartier_divisor"]
def IsLocalEquationAt (D : X.CartierDivisor) (x : X) (f : X.totalQuotientSheaf.presheaf.stalk x) :
    Prop :=
  ∃ (U : X.Opens) (hx : x ∈ U) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ),
    IsLocalEquationOn D U g ∧ X.totalQuotientSheaf.presheaf.germ U x hx (g : _) = f

/-- `f = a / b` in `𝓜_{X,x}` for `a, b ∈ 𝒪_{X,x}`: the image of `b` is a unit and `b · f = a`. -/
def IsFraction {x : X} (f : X.totalQuotientSheaf.presheaf.stalk x)
    (a b : X.presheaf.stalk x) : Prop :=
  IsUnit (stalkToTotalQuotient x b) ∧ stalkToTotalQuotient x b * f = stalkToTotalQuotient x a

/-! ### Effective divisors -/

/-- A divisor is *effective*, `D ≽ 0`, if it admits local equations `fᵢ ∈ Γ(Uᵢ, 𝒪_X)` on an
open cover `{Uᵢ}`: every point lies in an open `U` with a section of `𝒪_X` over `U` whose image
in `Γ(U, 𝓜_X)` is a unit and a local equation of `D` on `U`. -/
@[mmp "def_p01a_effective_divisor"]
def IsEffective (D : X.CartierDivisor) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : Γ(X, U)) (hs : IsUnit (toTotalQuotient U s)),
    IsLocalEquationOn D U hs.unit

/-- `EffectiveLE D' D`, written `D ≽ D'`, holds if `D - D'` is effective. -/
@[mmp "def_p01a_effective_divisor"]
def EffectiveLE (D' D : X.CartierDivisor) : Prop := IsEffective (D - D')

/-- A Cartier divisor is *effective* in Fulton's sense (B.4.5) if it admits local equations
`fᵢ ∈ 𝒪(Uᵢ)` on an affine open cover `{Uᵢ}`. -/
@[mmp "def_b_effective_cartier_divisor"]
def IsEffectiveOnAffineCover (D : X.CartierDivisor) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (s : Γ(X, U))
    (hs : IsUnit (toTotalQuotient U s)), IsLocalEquationOn D U hs.unit

/-! ### Support -/

/-- The *support* `Supp D` of a Cartier divisor: the points `x` at which the germ
`D_x ∈ 𝓜_{X,x}^*/𝒪_{X,x}^*` is not the identity. -/
@[mmp "def_p01a_divisor_support"]
def cartierSupport (D : X.CartierDivisor) : Set X :=
  {x | (cartierSheaf X).presheaf.germ ⊤ x trivial D ≠ 0}

theorem mem_cartierSupport_iff {D : X.CartierDivisor} {x : X} :
    x ∈ cartierSupport D ↔ (cartierSheaf X).presheaf.germ ⊤ x trivial D ≠ 0 :=
  Iff.rfl

/-! ### Principal divisors and linear equivalence -/

variable (X) in
/-- The map `div : Γ(X, 𝓜_X^*) → Div(X)` taking a unit to its image in
`Γ(X, 𝓜_X^*/𝒪_X^*)`, as a homomorphism of groups. -/
@[mmp "def_p01a_principal_divisor"]
def principalHom : Additive (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ →+ X.CartierDivisor :=
  ((toSheafify (Opens.grothendieckTopology X) (unitGroupPresheaf X.totalQuotientSheaf) ≫
    (unitGroupQuotientMap X.toTotalQuotientSheaf).hom).app (op ⊤)).hom

/-- The *principal divisor* `div(f)` of a unit `f ∈ Γ(X, 𝓜_X^*)`: the divisor with local
equation `f` everywhere. -/
@[mmp "def_p01a_principal_divisor"]
def principalDivisor (f : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) : X.CartierDivisor :=
  principalHom X (Additive.ofMul f)

variable (X) in
/-- The subgroup `Princ(X) ⊆ Div(X)` of principal divisors. -/
@[mmp "def_p01a_principal_divisor"]
def principalSubgroup : AddSubgroup X.CartierDivisor := (principalHom X).range

/-- Every principal divisor `div(f)` lies in `principalSubgroup X`. -/
theorem principalDivisor_mem (f : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    principalDivisor f ∈ principalSubgroup X := ⟨_, rfl⟩

/-- A divisor lies in `principalSubgroup X` if and only if it is `div(f)` for some unit `f`. -/
theorem mem_principalSubgroup_iff {D : X.CartierDivisor} :
    D ∈ principalSubgroup X ↔ ∃ f, principalDivisor f = D :=
  ⟨fun ⟨f, hf⟩ => ⟨f.toMul, hf⟩, fun ⟨f, hf⟩ => ⟨Additive.ofMul f, hf⟩⟩

/-- The divisor `div(f)` has `f` as a local equation on all of `X`. -/
theorem isLocalEquationOn_principalDivisor (f : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    IsLocalEquationOn (principalDivisor f) ⊤ f := by
  simp only [IsLocalEquationOn, restrictDivisor, homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Divisors `D₁, D₂` are *linearly equivalent* if `D₁ - D₂` is principal. -/
@[mmp "def_p01a_linear_equivalence"]
def LinearlyEquivalent (D₁ D₂ : X.CartierDivisor) : Prop := D₁ - D₂ ∈ principalSubgroup X

/-- Linear equivalence of Cartier divisors is an equivalence relation. -/
theorem linearlyEquivalent_equivalence : Equivalence (LinearlyEquivalent (X := X)) where
  refl D := by simp [LinearlyEquivalent, (principalSubgroup X).zero_mem]
  symm h := by simpa [LinearlyEquivalent] using (principalSubgroup X).neg_mem h
  trans h₁ h₂ := by
    simpa [LinearlyEquivalent] using (principalSubgroup X).add_mem h₁ h₂

/-- Every divisor is linearly equivalent to itself. -/
@[refl] theorem LinearlyEquivalent.refl (D : X.CartierDivisor) : LinearlyEquivalent D D :=
  linearlyEquivalent_equivalence.refl D

/-- Linear equivalence is symmetric. -/
@[symm] theorem LinearlyEquivalent.symm {D₁ D₂ : X.CartierDivisor} (h : LinearlyEquivalent D₁ D₂) :
    LinearlyEquivalent D₂ D₁ :=
  linearlyEquivalent_equivalence.symm h

/-- Linear equivalence is transitive. -/
theorem LinearlyEquivalent.trans {D₁ D₂ D₃ : X.CartierDivisor} (h₁ : LinearlyEquivalent D₁ D₂)
    (h₂ : LinearlyEquivalent D₂ D₃) : LinearlyEquivalent D₁ D₃ :=
  linearlyEquivalent_equivalence.trans h₁ h₂

/-- Linear equivalence is compatible with addition. -/
theorem LinearlyEquivalent.add {D₁ D₁' D₂ D₂' : X.CartierDivisor}
    (h₁ : LinearlyEquivalent D₁ D₁') (h₂ : LinearlyEquivalent D₂ D₂') :
    LinearlyEquivalent (D₁ + D₂) (D₁' + D₂') := by
  have := (principalSubgroup X).add_mem h₁ h₂
  rwa [LinearlyEquivalent, add_sub_add_comm]

/-- Linear equivalence is compatible with multiplication by natural numbers. -/
theorem LinearlyEquivalent.nsmul {D D' : X.CartierDivisor} (h : LinearlyEquivalent D D')
    (q : ℕ) : LinearlyEquivalent (q • D) (q • D') := by
  have := (principalSubgroup X).nsmul_mem h q
  rwa [LinearlyEquivalent, ← smul_sub]

/-! ### Fulton's description by local equations -/

/-- A Cartier divisor `D` *is given by* an affine open cover `{Uᵢ}` of `X` and local equations
`fᵢ ∈ 𝒦(Uᵢ)^*` (Fulton B.4.1): the `Uᵢ` are affine and cover `X`, each `fᵢ` is a local equation
of `D` on `Uᵢ`, and `fᵢ/fⱼ` is a unit of `𝒪(Uᵢ ∩ Uⱼ)`. -/
@[mmp "def_b_cartier_divisor"]
def IsGivenByLocalEquations (D : X.CartierDivisor) {ι : Type u} (U : ι → X.Opens)
    (f : ∀ i, (X.totalQuotientSheaf.obj.obj (op (U i)))ˣ) : Prop :=
  (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧ (∀ i, IsLocalEquationOn D (U i) (f i)) ∧
    ∀ i j, ∃ g : (Γ(X, U i ⊓ U j))ˣ,
      Units.map (toTotalQuotient (U i ⊓ U j)).toMonoidHom g =
        Units.map (X.totalQuotientSheaf.obj.map (homOfLE inf_le_left).op).hom.toMonoidHom (f i) /
          Units.map (X.totalQuotientSheaf.obj.map (homOfLE inf_le_right).op).hom.toMonoidHom (f j)

/-! ### Associated points and subvarieties -/

/-- The closure `closure {ξ}` of a point `ξ`, as a subvariety with its reduced structure. -/
@[mmp "def_p01a_associated_subvariety"]
def associatedSubvariety (ξ : X) : Scheme.Subvariety X :=
  Scheme.Subvariety.ofIsIrreducible ⟨closure {ξ}, isClosed_closure⟩ isIrreducible_singleton.closure

/-- `V` is an *associated subvariety* of the `𝒪_X`-module `F` if it is the closure, with the
reduced structure, of an associated point of `F`. The associated subvarieties of `X` are those
of `𝒪_X`. -/
@[mmp "def_p01a_associated_subvariety"]
def IsAssociatedSubvariety (F : X.Modules) (V : Scheme.Subvariety X) : Prop :=
  ∃ ξ, Stacks.Divisors.IsAssociatedPoint F ξ ∧ V = associatedSubvariety ξ

/-! ### Pull-backs -/

/-- The condition under which a divisor `D` on `X` has a pull-back along `f : Y ⟶ X`: no
associated point of `Y` maps into `Supp D`. -/
@[mmp "def_p01a_divisor_pullback"]
def PullbackCondition (f : Y ⟶ X) (D : X.CartierDivisor) : Prop :=
  ∀ η ∈ Stacks.Divisors.schemeAssociatedPoints Y, f η ∉ cartierSupport D

/-- A divisor `D'` on `Y` is *a pull-back* of `D` along `f : Y ⟶ X` (where `f` satisfies
`PullbackCondition f D`) if for every `y ∈ Y` there are `a, b ∈ 𝒪_{X,f(y)}` such that `a/b` is a
local equation of `D` at `f(y)`, `f^♯a, f^♯b` are non-zero-divisors of `𝒪_{Y,y}`, and
`f^♯a/f^♯b` is a local equation of `D'` at `y`. -/
@[mmp "def_p01a_divisor_pullback"]
def IsPullback (f : Y ⟶ X) (D : X.CartierDivisor) (D' : Y.CartierDivisor) : Prop :=
  PullbackCondition f D ∧ ∀ y : Y, ∃ a b : X.presheaf.stalk (f y),
    (∃ g, IsLocalEquationAt D (f y) g ∧ IsFraction g a b) ∧
    f.stalkMap y a ∈ nonZeroDivisors (Y.presheaf.stalk y) ∧
    f.stalkMap y b ∈ nonZeroDivisors (Y.presheaf.stalk y) ∧
    ∃ g', IsLocalEquationAt D' y g' ∧ IsFraction g' (f.stalkMap y a) (f.stalkMap y b)

/-! ### The subscheme of an effective divisor -/

/-- The closed subscheme `Z` (given by its ideal sheaf) is *the closed subscheme of the effective
Cartier divisor `D`* (Fulton B.4.5): `X` is covered by affine opens `U` with a local equation
`s ∈ 𝒪(U)` of `D` on `U` such that the ideal of `Z` on `U` is `s 𝒪(U)`. Since an ideal
sheaf is determined by its ideals on an affine open cover, such a `Z` is unique. -/
@[mmp "def_b_subscheme_of_effective_divisor"]
def IsSubschemeOfEffective (D : X.CartierDivisor) (Z : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (_ : x ∈ (U : X.Opens)) (s : Γ(X, U))
    (hs : IsUnit (toTotalQuotient (U : X.Opens) s)),
    IsLocalEquationOn D U hs.unit ∧ Z.ideal U = Ideal.span {s}

/-- A closed subscheme `Z ⊆ X` *is an effective Cartier divisor* (Fulton B.4.5, B.6.2) if it is
the closed subscheme of some effective Cartier divisor. The Stacks project's
`Stacks.Divisors.IsEffectiveCartierDivisor` (the ideal sheaf is invertible) is the same notion,
characterized by `Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`: the ideal sheaf
is locally generated by one non-zero-divisor. -/
@[mmp "def_b_subscheme_of_effective_divisor"]
def IsEffectiveCartierSubscheme (Z : X.IdealSheafData) : Prop :=
  ∃ D : X.CartierDivisor, IsEffectiveOnAffineCover D ∧ IsSubschemeOfEffective D Z

end MMP.Intersection
