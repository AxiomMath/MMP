module

public import MMP.AlgebraicGeometry.Divisor.Cartier
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheaf
public import MMP.AlgebraicGeometry.Divisor.LocalEquation
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.SheafPicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms

/-!
# The line bundle of a divisor, divisors of sections, the Picard group (Lazarsfeld §1.1)

For a Cartier divisor `D` on a scheme `X`, `𝒪_X(D) ⊆ 𝓜_X` is the sheaf
`MMP.CartierDivisor.sheaf D`. Its sections over `V` are the `σ ∈ Γ(V, 𝓜_X)` with
`σ f ∈ 𝒪_{X,x}` for every `x ∈ V` and every local equation `f` of `D` at `x`; this stalkwise
condition is the `Γ(V, 𝒪_X)`-submodule `MMP.Intersection.lineBundleSections D V` of `Γ(V, 𝓜_X)`
(through `𝒪_X ⟶ 𝓜_X`), stable under restriction
(`MMP.Intersection.mem_lineBundleSections_iff_mem`).

## Main definitions

* `MMP.Intersection.lineBundleSections`: the sections of `𝒪_X(D)`, stalkwise.
* `MMP.Intersection.twist`: `ℱ(D) = ℱ ⊗ 𝒪_X(D)`.
* `MMP.Intersection.IsTrivializingGenerator`, `MMP.Intersection.IsRegularSection`,
  `MMP.Intersection.IsDivisorOfSection`: regular sections of a line bundle and their divisors.
* `MMP.Intersection.IsCanonicalDivisor`: canonical divisors `K_X`, with `𝒪_X(K_X) ≅ ω_X = Ω^n_X`.

The Picard group is the Stacks project's `Stacks.SheafPicardGroup.schemePicardGroup`: the
isomorphism classes of invertible `𝒪_X`-modules under tensor product. Invertible modules are the
locally free modules of rank one (Stacks 0B8M,
`Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry MonoidalCategory

namespace MMP.Intersection

variable {X : Scheme.{u}}

/-- `Γ(U, 𝓜_X)` is a `Γ(U, 𝒪_X)`-module through `𝒪_X ⟶ 𝓜_X`. -/
instance moduleTotalQuotient (U : X.Opens) : Module Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
  Module.compHom _ (toTotalQuotient U)

/-- Scalar multiplication on `Γ(U, 𝓜_X)` by `r ∈ Γ(U, 𝒪_X)` is multiplication by the image of
`r` under `𝒪_X ⟶ 𝓜_X`. -/
theorem smul_totalQuotient_def (U : X.Opens) (r : Γ(X, U))
    (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    r • σ = toTotalQuotient U r * σ := rfl

/-- The sections `Γ(V, 𝒪_X(D))`: the `σ ∈ Γ(V, 𝓜_X)` with `σ f ∈ 𝒪_{X,x}` for every `x ∈ V`
and every local equation `f` of `D` at `x`. -/
@[mmp "def_p01a_line_bundle_of_divisor"]
def lineBundleSections (D : X.CartierDivisor) (U : X.Opens) :
    Submodule Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) where
  carrier := {σ | ∀ (x : X) (hx : x ∈ U) (f : X.totalQuotientSheaf.presheaf.stalk x),
    IsLocalEquationAt D x f →
      X.totalQuotientSheaf.presheaf.germ U x hx σ * f ∈ (stalkToTotalQuotient x).range}
  zero_mem' x hx f _ := by simp only [map_zero, zero_mul]; exact zero_mem _
  add_mem' {σ τ} hσ hτ x hx f hf := by
    rw [map_add, add_mul]; exact add_mem (hσ x hx f hf) (hτ x hx f hf)
  smul_mem' r σ hσ x hx f hf := by
    obtain ⟨a, ha⟩ := hσ x hx f hf
    refine ⟨X.presheaf.germ U x hx r * a, ?_⟩
    rw [smul_totalQuotient_def, map_mul, map_mul, germ_toTotalQuotient, ha, mul_assoc]

/-- The restriction to `V ⊆ U` of a section of `𝒪_X(D)` over `U` is a section of `𝒪_X(D)` over
`V`. -/
theorem res_mem (D : X.CartierDivisor) {U V : X.Opens} (h : V ≤ U)
    {σ : X.totalQuotientSheaf.obj.obj (op U)} (hσ : σ ∈ lineBundleSections D U) :
    X.totalQuotientSheaf.obj.map (homOfLE h).op σ ∈ lineBundleSections D V := by
  intro x hx f hf
  have := hσ x (h hx) f hf
  rwa [show X.totalQuotientSheaf.presheaf.germ V x hx
      (X.totalQuotientSheaf.obj.map (homOfLE h).op σ) =
        X.totalQuotientSheaf.presheaf.germ U x (h hx) σ from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]

/-- The map `𝒪_X ⟶ 𝓜_X` commutes with restriction from `U` to `V ⊆ U`. -/
theorem toTotalQuotient_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) :
    toTotalQuotient V (X.presheaf.map (homOfLE h).op r) =
      X.totalQuotientSheaf.obj.map (homOfLE h).op (toTotalQuotient U r) := by
  have := X.toTotalQuotientSheaf.hom.naturality (homOfLE h).op
  exact congrArg (fun φ => φ.hom r) this

/-- The sections of `𝒪_X(D)` over `U` form a module over `𝒪_X(U)`. -/
instance moduleLineBundleSections (D : X.CartierDivisor) (U : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (lineBundleSections D U.unop) :=
  inferInstanceAs (Module Γ(X, U.unop) (lineBundleSections D U.unop))

/-- `ℱ(D) = ℱ ⊗ 𝒪_X(D)` for an `𝒪_X`-module `ℱ`. -/
@[mmp "def_p01a_line_bundle_of_divisor"]
def twist (F : X.Modules) (D : X.CartierDivisor) : X.Modules := F ⊗ MMP.CartierDivisor.sheaf D

/-! ### Regular sections and their divisors -/

/-- A section `e ∈ Γ(U, L)` *trivializes `L` on `U`*: for every open `V ⊆ U`,
`r ↦ r · e|_V` is a bijection `Γ(V, 𝒪_X) → Γ(V, L)`, i.e. `𝒪_U ≅ L|_U` by `1 ↦ e`. -/
@[mmp "def_p01a_divisor_of_section"]
def IsTrivializingGenerator (L : X.Modules) (U : X.Opens) (e : Γ(L, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective fun r : Γ(X, V) => r • L.presheaf.map (homOfLE h).op e

/-- A section `s ∈ Γ(X, L)` of a line bundle is *regular* if for every open `U` trivializing `L`
by a generator `e_U`, the function `s/e_U ∈ Γ(U, 𝒪_X)` (the `r` with `s|_U = r e_U`) is a
non-zero-divisor at every point of `U`. -/
@[mmp "def_p01a_divisor_of_section"]
def IsRegularSection (L : X.Modules) (s : Γ(L, ⊤)) : Prop :=
  ∀ (U : X.Opens) (e : Γ(L, U)), IsTrivializingGenerator L U e →
    ∀ r : Γ(X, U), L.presheaf.map (homOfLE le_top).op s = r • e →
      ∀ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x)

/-- For a regular section `s` of a line bundle `L`, `D = div(s)` is the effective divisor with
local equations `s/e_U` on the trivializing opens `U`. -/
@[mmp "def_p01a_divisor_of_section"]
def IsDivisorOfSection (L : X.Modules) (s : Γ(L, ⊤)) (D : X.CartierDivisor) : Prop :=
  IsRegularSection L s ∧ IsEffective D ∧
    ∀ (U : X.Opens) (e : Γ(L, U)), IsTrivializingGenerator L U e →
      ∀ r : Γ(X, U), L.presheaf.map (homOfLE le_top).op s = r • e →
        ∃ h : IsUnit (toTotalQuotient U r), IsLocalEquationOn D U h.unit

/-! ### The Picard group and canonical divisors -/

/-- `K` is a *canonical divisor* on the `K₀`-scheme `X` (Lazarsfeld Not. 1.1.7):
`𝒪_X(K) ≅ ω_X = Ω^n_{X/K₀}`, where `n = dim X`. -/
@[mmp "not_p01a_canonical_bundle"]
def IsCanonicalDivisor (K₀ : Type u) [Field K₀] (X : Scheme.{u}) [X.Over (Spec (.of K₀))]
    (K : X.CartierDivisor) : Prop :=
  ∃ n : ℕ, Scheme.dimension X = n ∧
    Nonempty (MMP.CartierDivisor.sheaf K ≅
      Scheme.Hom.relativeDifferentialForms (X ↘ Spec (.of K₀)) n)

end MMP.Intersection
