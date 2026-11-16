module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# Multiplicities and degrees on curves (Kollár, *Resolution of singularities*, 1.20)

Let `k` be a field. A commutative `k`-algebra `R` has *finite colength* if `R / rR` is a
finite-dimensional `k`-vector space for every non-zero-divisor `r` of `R`. For such an `r` the
*multiplicity* is `e_R(r) = dim_k R / rR`, and for an element `f = r₁ / r₂` of the total ring of
fractions with `r₁, r₂` non-zero-divisors it is `e_R(f) = e_R(r₁) - e_R(r₂)`.

On an integral curve `C` over `k` the *semi-local ring* `𝒪_{P,C} ⊆ k(C)` of a finite set `P` of
closed points is the intersection of the local rings `𝒪_{p,C}`, and `e_P(f) = e_{𝒪_{P,C}}(f)` for a
rational function `f`. The *degree* of a line bundle `L` with respect to a non-zero rational
section `s ∈ L_η` is `deg_C(L, s) = ∑_p e_p(s)`, where `s = φ_p σ_p` for a generator `σ_p` of
`L_p`; the *degree* `deg_C L` is `deg_C(L, s_L)` for a chosen non-zero rational section `s_L`.

The notion of a *nonsingular* (regular) point of a curve, Kollár 1.19, is Mathlib's
`IsRegularLocalRing` applied to the local ring `𝒪_{p,C}` and is not restated here.

## Main definitions

* `MMP.Resolution.IsFiniteColength`: `k`-algebras of finite colength.
* `MMP.Resolution.eMult`: the multiplicity `e_R(r) = dim_k R / rR`.
* `MMP.Resolution.eMultFrac`: the multiplicity `e_R(f) = e_R(r₁) - e_R(r₂)` of `f = r₁ / r₂`.
* `MMP.Resolution.semilocalRing`: the semi-local ring `𝒪_{P,C} = ⋂_{p ∈ P} 𝒪_{p,C}` in `k(C)`.
* `MMP.Resolution.eMultAt`: the multiplicity `e_P(f)` of a rational function at `P`.
* `MMP.Resolution.sectionMult`: the local multiplicity `e_p(s)` of a rational section of `L`.
* `MMP.Resolution.degreeWRT`: the degree `deg_C(L, s)` of `L` with respect to `s`.
* `MMP.Resolution.degree`: the degree `deg_C L` of `L`.

## Implementation notes

The definitions are total. `eMult` is `Module.finrank`, so it is `0` when `R / rR` is
infinite-dimensional; `eMultFrac` is stated for an arbitrary `R`-algebra `K` (the total ring of
fractions `FractionRing R` is the case of the source, the function field `k(C)` with
`R = 𝒪_{P,C}` the case of curves) and is `0` when `f` has no presentation `r₁ / r₂`. The choices
the source makes (of the presentation, of the generator `σ_p`, of the section `s_L`) are made
with `Classical.choose`. The stalks of `L` are Mathlib's `L.presheaf.stalk`, a module over
`𝒪_{C,p}` by `Stacks.ModuleStalkSpecialization.stalkModule`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u v w

namespace MMP.Resolution

/-! ### Algebras of finite colength -/

section Algebra

variable (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]

/-- A commutative `k`-algebra `R` has *finite colength* if `R / rR` is a finite-dimensional
`k`-vector space for every non-zero-divisor `r ∈ R`. -/
@[mmp "def_kr1a_finite_colength_algebra"]
def IsFiniteColength : Prop :=
  ∀ r ∈ nonZeroDivisors R, Module.Finite k (R ⧸ Ideal.span {r})

variable {R}

/-- The *multiplicity* `e_R(r) = dim_k R / rR` of an element `r` of a `k`-algebra `R`. It is
meaningful for a non-zero-divisor `r` with `R / rR` finite-dimensional, and is `0` when
`R / rR` is infinite-dimensional. -/
@[mmp "def_kr1a_multiplicity_of_element"]
noncomputable def eMult (r : R) : ℕ :=
  Module.finrank k (R ⧸ Ideal.span {r})

variable (K : Type w) [CommRing K] [Algebra R K]

open Classical in
/-- The *multiplicity* of an element `f` of an `R`-algebra `K`: if `f = r₁ / r₂` for
non-zero-divisors `r₁, r₂ ∈ R`, that is `r₁ = f r₂` in `K`, choose such a pair and put
`e_R(f) = e_R(r₁) - e_R(r₂)`; otherwise `e_R(f) = 0`. For `K` the total ring of fractions of a
`k`-algebra `R` of finite colength this is Kollár's (1.20.1). -/
@[mmp "def_kr1a_multiplicity_of_rational_function"]
noncomputable def eMultFrac (f : K) : ℤ :=
  if h : ∃ p : nonZeroDivisors R × nonZeroDivisors R,
      algebraMap R K p.1 = f * algebraMap R K p.2 then
    (eMult k (h.choose.1 : R) : ℤ) - eMult k (h.choose.2 : R)
  else 0

end Algebra

/-! ### The semi-local ring of finitely many points of a curve -/

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]

/-- The *semi-local ring* `𝒪_{P,C} = ⋂_{p ∈ P} 𝒪_{p,C}` of a finite set `P` of points of an
integral scheme `C`: the rational functions regular at every point of `P`, a subring of the
function field `k(C)`. For `P = {p}` it is (the image of) the local ring `𝒪_{p,C}`. -/
@[mmp "def_kr1a_semilocal_ring_of_points"]
noncomputable def semilocalRing (P : Finset C) : Subring C.functionField :=
  ⨅ p ∈ P, (algebraMap (C.presheaf.stalk p) C.functionField).range

variable (sC : C ⟶ Spec (.of k))

/-- For a scheme `C` over `k`, every scalar `a ∈ k` lies in the semi-local ring `𝒪_{P,C}` of
any finite set `P` of points. -/
theorem algebraMap_mem_semilocalRing (P : Finset C) (a : k) :
    letI := MMP.Mori.functionFieldAlgebra sC
    algebraMap k C.functionField a ∈ semilocalRing P := by
  let := MMP.Mori.functionFieldAlgebra sC
  unfold semilocalRing
  rw [Subring.mem_iInf]
  intro p
  rw [Subring.mem_iInf]
  intro _
  let := MMP.Mori.stalkAlgebra sC p
  have := MMP.Mori.isScalarTower_stalk_functionField sC p
  rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk p) C.functionField]
  exact ⟨_, rfl⟩

/-- The `k`-algebra structure of the semi-local ring `𝒪_{P,C}` of a curve over `k`, restricted
from that of `k(C)`. -/
@[instance_reducible]
noncomputable def semilocalRingAlgebra (P : Finset C) : Algebra k (semilocalRing P) :=
  letI := MMP.Mori.functionFieldAlgebra sC
  ((algebraMap k C.functionField).codRestrict (semilocalRing P)
    (algebraMap_mem_semilocalRing sC P)).toAlgebra

/-- The *multiplicity* `e_P(f) = e_{𝒪_{P,C}}(f)` at a finite set `P` of points of an integral
curve `C` over `k` of a rational function `f ∈ k(C)` (Kollár (1.20.1)); `e_p = e_{{p}}`. -/
@[mmp "def_kr1a_multiplicity_of_rational_function"]
noncomputable def eMultAt (P : Finset C) (f : C.functionField) : ℤ :=
  letI := semilocalRingAlgebra sC P
  eMultFrac k C.functionField f (R := semilocalRing P)

/-! ### The degree of a line bundle on a curve -/

variable (L : C.Modules)

/-- The `𝒪_{C,p}`-module structure of the stalk `L_p`. -/
@[instance_reducible]
noncomputable def stalkModule (p : C) : Module (C.presheaf.stalk p) (L.presheaf.stalk p) :=
  Stacks.ModuleStalkSpecialization.stalkModule L p

/-- The `k(C)`-module structure of the generic stalk `L_η`. -/
@[instance_reducible]
noncomputable def genericStalkModule : Module C.functionField (L.presheaf.stalk (genericPoint C)) :=
  Stacks.ModuleStalkSpecialization.stalkModule L (genericPoint C)

/-- The comparison map `L_p → L_η` from the stalk at `p` to the generic stalk. -/
noncomputable def toGenericStalk (p : C) : L.presheaf.stalk p → L.presheaf.stalk (genericPoint C) :=
  fun σ => TopCat.Presheaf.stalkSpecializes L.val.presheaf
    ((genericPoint_spec C).specializes (Set.mem_univ p)) σ

/-- `σ` generates the stalk `L_p` as an `𝒪_{C,p}`-module. -/
def IsStalkGenerator (p : C) (σ : L.presheaf.stalk p) : Prop :=
  letI := stalkModule L p
  Submodule.span (C.presheaf.stalk p) {σ} = ⊤

open Classical in
/-- The rational function `φ_p ∈ k(C)` with `s = φ_p σ_p` in `L_η`, for a chosen generator `σ_p`
of `L_p`; it is `1` when `L_p` has no generator or no such `φ_p` exists. -/
noncomputable def sectionRatio (s : L.presheaf.stalk (genericPoint C)) (p : C) :
    C.functionField :=
  letI := genericStalkModule L
  if hσ : ∃ σ, IsStalkGenerator L p σ then
    if hφ : ∃ φ : C.functionField, s = φ • toGenericStalk L p hσ.choose then hφ.choose else 1
  else 1

/-- The *local multiplicity* `e_p(s) = e_p(φ_p)` at a point `p` of a rational section
`s ∈ L_η` of `L`, where `s = φ_p σ_p` for a chosen generator `σ_p` of `L_p`
(Kollár (1.20.6)). -/
@[mmp "def_kr1a_degree_of_line_bundle_wrt_section"]
noncomputable def sectionMult (s : L.presheaf.stalk (genericPoint C)) (p : C) : ℤ :=
  eMultAt sC {p} (sectionRatio L s p)

open Classical in
/-- The *degree* `deg_C(L, s) = ∑_p e_p(s)` of `L` with respect to a rational section `s ∈ L_η`,
the sum over the closed points `p` with `e_p(s) ≠ 0` if there are finitely many, and `0`
otherwise (Kollár (1.20.6)). -/
@[mmp "def_kr1a_degree_of_line_bundle_wrt_section"]
noncomputable def degreeWRT (s : L.presheaf.stalk (genericPoint C)) : ℤ :=
  if h : {p : C | IsClosed ({p} : Set C) ∧ sectionMult sC L s p ≠ 0}.Finite then
    ∑ p ∈ h.toFinset, sectionMult sC L s p
  else 0

open Classical in
/-- The *degree* `deg_C L = deg_C(L, s_L)` of `L` for a chosen non-zero rational section
`s_L ∈ L_η` (Kollár (1.20.6)); it is `0` when `L_η = 0`. -/
@[mmp "def_kr1a_degree_of_line_bundle"]
noncomputable def degree : ℤ :=
  if h : ∃ s : L.presheaf.stalk (genericPoint C), s ≠ 0 then degreeWRT sC L h.choose else 0

end Curve

end MMP.Resolution
