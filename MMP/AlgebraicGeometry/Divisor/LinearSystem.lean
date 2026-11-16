module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowersRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenModel
public import StacksFrontier.AlgebraicGeometry.Modules.CokernelSupportNonvanishing
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic

/-!
# Linear systems, base loci, big and ample divisors

Let `X` be a normal variety over a field `k` and `M` a divisor on `X`. The global sections
`H⁰(X, M) = H⁰(X, 𝒪_X(M))` are the rational functions `φ ∈ K(X)` with `div φ + M ≥ 0`, and a
nonzero section `σ`, read as such a `φ`, has the *divisor of zeros* `(σ)₀ = div φ + M`. The
*base locus* `Bs|M|` is the intersection of the supports of the `(σ)₀`. A Cartier divisor `D` on a
proper variety of dimension `n` is *big* if `h⁰(X, 𝒪_X(mD)) > c mⁿ` for some `c > 0` and all
large `m`, and a `ℚ`-divisor is big or ample when some positive multiple is a big, respectively
ample, Cartier divisor.

An invertible sheaf `ℒ` with a basis `s₀, …, s_N` of `H⁰(X, ℒ)` defines a morphism
`φ_{|ℒ|} : U → ℙᴺ` on the open `U` where some `sᵢ` generates `ℒ`, with `φ^*𝒪(1) = ℒ|_U` and
`φ^*xᵢ = sᵢ`; its image `Y_ℒ` is the reduced closure of `φ(U)`.

## Main definitions

* `MMP.Mori.Divisor.h0`: `h⁰(X, 𝒪_X(D)) = dim_k H⁰(X, 𝒪_X(D))`.
* `MMP.Mori.Divisor.IsBig`, `MMP.Mori.QDivisor.IsBig`: big Cartier divisors and big
  `ℚ`-Cartier `ℚ`-divisors.
* `MMP.Mori.Divisor.IsAmple`, `MMP.Mori.QDivisor.IsAmple`: ample Cartier divisors and ample
  `ℚ`-Cartier `ℚ`-divisors.
* `MMP.Mori.Divisor.zeroDivisor`: the divisor of zeros `(σ)₀` of a nonzero section.
* `MMP.Mori.Divisor.baseLocus`, `MMP.Mori.Divisor.IsBasepointFree`: `Bs|M|` and freeness of `|M|`.
* `MMP.Mori.Divisor.baseLocusOfMultiple`, `MMP.Mori.Divisor.stableBaseLocusOfPowers`:
  `B(s) = Bs|sD|` and `B_s = ⋂_{u ≥ 1} B(sᵘ)`.
* `MMP.Mori.linearSystemLocus`, `MMP.Mori.linearSystemMap`: the open `U` and the morphism
  `φ_{|ℒ|} : U → ℙᴺ`.
* `MMP.Mori.linearSystemImage`, `MMP.Mori.linearSystemMapToImage`,
  `MMP.Mori.IsBirationalOntoImage`: the image `Y_ℒ` and birationality of `φ_{|ℒ|}` onto it.
* `MMP.Mori.locallyFreeLocus`: the largest open on which a sheaf is locally free.
* `MMP.Mori.reflexivePow`: the reflexive powers `L^{[i]}`, `i ∈ ℤ`.
* `MMP.Mori.Divisor.divisorialAlgebra`: the divisorial algebra `R(Y, B) = ⊕_{m ≥ 0} 𝒪_Y(mB)`.
* `MMP.Mori.Divisor.canonicalRing`: the canonical ring `R(X, K_X + Δ) = ⊕_m H⁰(mK_X + ⌊mΔ⌋) tᵐ`.
* `MMP.Mori.Divisor.eulerPolynomial`: `P(u) = χ(Y, 𝒪_Y(∑ uᵢ Dᵢ + ⌈A⌉))`.

## Main results

* `MMP.Mori.Divisor.zeroDivisor_nonneg`: the divisor of zeros is effective.
* `MMP.Mori.linearSystemMapTwistIso`, `MMP.Mori.linearSystemMapTwistIso_pullbackSectionOne`:
  `φ^*𝒪(1) ≅ ℒ|_U`, carrying `φ^*xᵢ` to `sᵢ`.
* `MMP.Mori.linearSystemLocus_map_iso`, `MMP.Mori.linearSystemLocus_pullback`: the open `U` is
  unchanged by an isomorphism `ℒ ≅ ℒ'` carrying the basis along, and is the preimage `p⁻¹(U)`
  for the pulled back basis of `p^*ℒ`.

## Implementation notes

Divisors are Weil divisors on a locally Noetherian normal scheme, and a Cartier divisor is a Weil
divisor which is locally principal (`MMP.Mori.Divisor.IsCartier`); `𝒪_X(D)` is the divisorial
sheaf. The growth condition defining bigness, the base locus and the divisor of zeros make sense
for every Weil divisor and are defined for all of them; for a Cartier divisor they are the
source's notions.

The `k`-vector space structure on `H⁰(X, 𝒪_X(D))` is restriction of scalars along
`k ≅ Γ(Spec k, 𝒪) → Γ(X, 𝒪_X)`. The dimension `h⁰` is `Module.finrank`, which is the dimension
for a proper `X`, where `H⁰` is finite-dimensional.

A section `σ ∈ H⁰(X, M) ⊆ K(X)` is a unit of `K(X)` as soon as it is nonzero, because `K(X)` is
a field for integral `X`; this is how `σ` is "viewed as `φ ∈ K(X)`".

`ℙᴺ` is `AlgebraicGeometry.projectiveSpaceOfModule k (ι →₀ k) = Proj (Sym_k (k^ι))`, for a basis
of `H⁰(X, ℒ)` indexed by `ι` (`ι = Fin (N + 1)`), whose degree-one coordinates `xᵢ` are the
standard basis vectors, and `φ_{|ℒ|}` is the morphism of Stacks Tag 0FCY attached to the
restriction of the linear system to `U`. The image `Y_ℒ` is the closed subscheme of `ℙᴺ` cut out
by the vanishing ideal of `closure φ(U)`, which is its reduced induced structure; for reduced `X`
the morphism `φ_{|ℒ|}` factors through it.

The locally free locus is defined for any `𝒪_X`-module, and the reflexive powers for any
`𝒪_X`-module; the source states both for a torsion-free coherent sheaf of rank one on a normal
variety.

The Euler characteristic function is written as the alternating sum of the `k`-dimensions of the
cohomology groups, which needs no coherence instance; it is
`AlgebraicGeometry.eulerCharacteristic` by definition when the sheaf is coherent
(`MMP.Mori.Divisor.eulerPolynomial_eq_eulerCharacteristic`).
The canonical ring is the graded `Γ(X, 𝒪_X)`-submodule of `𝒦_X(X)[t] = K(X)[t]`, and is defined
for a divisor carrying the hypothesis that it is canonical.

The divisorial algebra is given by its sections: over an open `U` it is the graded
`Γ(X, U)`-subalgebra of `𝒦_X(U)[t]` of the polynomials whose coefficient of `tᵐ` is a section of
`𝒪_X(mB)` over `U`, with the restriction maps of `𝒦_X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.52, 2.59,
  2.60, 3.2, 3.9, 6.2
* [R. Hartshorne, *Algebraic geometry*][Har77], II.7.1
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Mori

/-! ### Global sections as a `k`-vector space -/

section Scalars

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The ring map `k ≅ Γ(Spec k, 𝒪) → Γ(X, 𝒪_X)` given by a morphism `f : X ⟶ Spec k`. -/
def scalarsToGlobalSections : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

end Scalars

/-! ### Big Cartier divisors on an arbitrary scheme -/

section BigCartier

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `h⁰(X, 𝒪_X(D))` for a Cartier divisor `D ∈ Div(X) = Γ(X, 𝒦_X^*/𝒪_X^*)` on an arbitrary scheme:
the dimension over `k` of the global sections of the invertible sheaf
`𝒪_X(D) = MMP.CartierDivisor.sheaf D`, a `k`-vector space through
`f : X ⟶ Spec k`. -/
@[mmp "def_km2c_big"]
def cartierH0 (D : X.CartierDivisor) : ℕ :=
  letI : Module k Γ(MMP.CartierDivisor.sheaf D, ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k f)
  Module.finrank k Γ(MMP.CartierDivisor.sheaf D, ⊤)

/-- A Cartier divisor `D` on a variety `X` of dimension `n` (no normality assumed) is *big* if
there are `c > 0` and `k₀` such that `h⁰(X, 𝒪_X(mD)) > c mⁿ` for every integer `m ≥ k₀`. -/
@[mmp "def_km2c_big"]
def IsBigCartier (D : X.CartierDivisor) : Prop :=
  ∃ n : ℕ, topologicalKrullDim X = n ∧ ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ m : ℤ, k₀ ≤ m →
    c * (m : ℝ) ^ n < (cartierH0 k f (m • D) : ℝ)

end BigCartier

/-! ### Big divisors -/

section Big

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- `h⁰(X, 𝒪_X(D))`: the dimension over `k` of the global sections of `𝒪_X(D)`, a `k`-vector
space through `f : X ⟶ Spec k`. -/
@[mmp "def_km2c_big"]
def h0 (D : Divisor X) : ℕ :=
  letI : Module k (D.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k f)
  Module.finrank k (D.divisorialSubmodule ⊤)

/-- A divisor `D` on a variety `X` of dimension `n` is *big* if there are `c > 0` and `k₀` such
that `h⁰(X, 𝒪_X(mD)) > c mⁿ` for every integer `m ≥ k₀`. -/
@[mmp "def_km2c_big"]
def IsBig (D : Divisor X) : Prop :=
  ∃ n : ℕ, topologicalKrullDim X = n ∧ ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ m : ℤ, k₀ ≤ m →
    c * (m : ℝ) ^ n < (h0 k f (m • D) : ℝ)

/-- A divisor `D` is big if and only if the defining growth condition on `h⁰(X, 𝒪_X(mD))` holds. -/
theorem isBig_iff (D : Divisor X) :
    D.IsBig k f ↔ ∃ n : ℕ, topologicalKrullDim X = n ∧ ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ,
      ∀ m : ℤ, k₀ ≤ m → c * (m : ℝ) ^ n < (h0 k f (m • D) : ℝ) :=
  Iff.rfl

end Divisor

namespace QDivisor

/-- A `ℚ`-divisor `M` is *big* if some positive multiple `mM` is a Cartier divisor which is
big. -/
@[mmp "def_km2c_big_qdivisor"]
def IsBig (M : QDivisor X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (m : ℚ) • M ∧ D.IsCartier ∧
    D.IsBig k f

/-- A `ℚ`-divisor `M` is big if and only if some positive multiple `mM` is a big Cartier
divisor. -/
theorem isBig_iff (M : QDivisor X) :
    M.IsBig k f ↔ ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (m : ℚ) • M ∧
      D.IsCartier ∧ D.IsBig k f :=
  Iff.rfl

end QDivisor

end Big

/-! ### Ample divisors -/

section Ample

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]

namespace Divisor

/-- A Cartier divisor `D` is *ample* if its invertible sheaf `𝒪_X(D)` is ample. -/
@[mmp "def_km2c_ample_qdivisor"]
def IsAmple (D : Divisor X) (hD : D.IsCartier) : Prop :=
  haveI := hD.isInvertibleModule_divisorialSheaf
  Stacks.Ample.IsAmple X D.divisorialSheaf

end Divisor

namespace QDivisor

/-- A `ℚ`-divisor `A` is *ample* if some positive multiple `mA` is a Cartier divisor whose
invertible sheaf `𝒪_X(mA)` is ample. -/
@[mmp "def_km2c_ample_qdivisor"]
def IsAmple (A : QDivisor X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (m : ℚ) • A ∧
    ∃ hD : D.IsCartier, D.IsAmple hD

/-- A `ℚ`-divisor `A` is ample if and only if some positive multiple `mA` is an ample Cartier
divisor. -/
theorem isAmple_iff (A : QDivisor X) :
    A.IsAmple ↔ ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (m : ℚ) • A ∧
      ∃ hD : D.IsCartier, D.IsAmple hD :=
  Iff.rfl

end QDivisor

end Ample

/-! ### The divisor of zeros of a section and the base locus -/

section BaseLocus

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- A global section `σ ∈ H⁰(X, 𝒪_X(M)) ⊆ 𝒦_X(X)`, read as a rational function in `K(X)`. -/
def sectionToRationalFunctions {M : Divisor X} (σ : M.divisorialSubmodule ⊤) :
    RationalFunctions X :=
  rationalFunctionsPresheafTopEquiv X σ.1

/-- The rational function of a global section `σ` has component `σ` at each irreducible
component. -/
theorem sectionToRationalFunctions_apply {M : Divisor X} (σ : M.divisorialSubmodule ⊤)
    (Z : irreducibleComponents X) :
    sectionToRationalFunctions σ Z = σ.1 ⟨Z, trivial⟩ := rfl

/-- Reading global sections of `𝒪_X(M)` as rational functions is injective. -/
theorem sectionToRationalFunctions_injective {M : Divisor X} :
    Function.Injective (sectionToRationalFunctions (M := M)) := fun _ _ h =>
  Subtype.ext ((rationalFunctionsPresheafTopEquiv X).injective h)

/-- A nonzero global section of `𝒪_X(M)` is a nonzero rational function. -/
theorem sectionToRationalFunctions_ne_zero {M : Divisor X} {σ : M.divisorialSubmodule ⊤}
    (hσ : σ ≠ 0) : sectionToRationalFunctions σ ≠ 0 := fun h =>
  hσ (sectionToRationalFunctions_injective (h.trans (map_zero _).symm))

/-- On an integral scheme, a nonzero global section of `𝒪_X(M)` is a unit of `K(X)`. -/
theorem isUnit_sectionToRationalFunctions [IsIntegral X] {M : Divisor X}
    {σ : M.divisorialSubmodule ⊤} (hσ : σ ≠ 0) : IsUnit (sectionToRationalFunctions σ) := by
  have e := rationalFunctionsEquivFunctionField X
  have h : e (sectionToRationalFunctions σ) ≠ 0 :=
    (map_ne_zero_iff e e.injective).mpr (sectionToRationalFunctions_ne_zero hσ)
  simpa using (isUnit_iff_ne_zero.mpr h).map e.symm

variable [CompactSpace X] [IsIntegral X]

/-- The *divisor of zeros* `(σ)₀ = div φ + M` of a nonzero global section `σ` of `𝒪_X(M)` on a
Noetherian normal integral scheme, where `φ ∈ K(X)` is `σ` read as a rational function, so that
`div φ + M ≥ 0`. -/
@[mmp "def_km3a_zero_divisor_of_section"]
def zeroDivisor (M : Divisor X) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) : Divisor X :=
  principalDivisor (isUnit_sectionToRationalFunctions hσ).unit + M

/-- The divisor of zeros of `σ` is `div φ + M`, where `φ` is `σ` read as a rational function. -/
theorem zeroDivisor_eq (M : Divisor X) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    M.zeroDivisor σ hσ = principalDivisor (isUnit_sectionToRationalFunctions hσ).unit + M := rfl

/-- The divisor of zeros of a nonzero section is effective. -/
theorem zeroDivisor_nonneg (M : Divisor X) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    0 ≤ M.zeroDivisor σ hσ := by
  intro E
  set φ := (isUnit_sectionToRationalFunctions hσ).unit
  have hne : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hE : (E.support ∩ (⊤ : X.Opens)).Nonempty := ⟨_, hne, trivial⟩
  have key := σ.2 E hE
  have hφ : (φ : RationalFunctions X) E.component = σ.1 ⟨E.component, trivial⟩ := rfl
  have hunit : IsUnit ((φ : RationalFunctions X) E.component) :=
    (Pi.isUnit_iff.mp φ.isUnit) E.component
  change 0 ≤ (principalDivisor φ).coeff E + M.coeff E
  rw [coeff_principalDivisor]
  rcases key with h0 | h
  · exact absurd (hφ.trans h0) hunit.ne_zero
  · rw [← hφ, E.valuation_component, WithZero.exp_le_exp] at h
    change -M E ≤ E.ord φ at h
    change 0 ≤ E.ord φ + M E
    omega

/-- The *base locus* `Bs|M| = ⋂_{0 ≠ σ ∈ H⁰(X, M)} Supp (σ)₀` of the linear system `|M|`, a closed
subset of `X`; it is all of `X` when `H⁰(X, M) = 0`. -/
@[mmp "def_km3a_base_locus"]
def baseLocus (M : Divisor X) : Closeds X :=
  ⨅ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), (M.zeroDivisor σ hσ).supp

/-- The linear system `|M|` is *basepoint free* if its base locus is empty. -/
@[mmp "def_km3a_base_locus"]
def IsBasepointFree (M : Divisor X) : Prop :=
  M.baseLocus = ⊥

/-- The base locus of `|M|` is contained in the support of the divisor of zeros of every nonzero
section. -/
theorem baseLocus_le_supp (M : Divisor X) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    M.baseLocus ≤ (M.zeroDivisor σ hσ).supp :=
  iInf₂_le σ hσ

/-- A point lies in the base locus of `|M|` if and only if it lies in the support of the divisor of
zeros of every nonzero section. -/
theorem mem_baseLocus_iff (M : Divisor X) (x : X) :
    x ∈ (M.baseLocus : Set X) ↔
      ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), x ∈ ((M.zeroDivisor σ hσ).supp : Set X) := by
  simp [baseLocus]

/-- If `H⁰(X, M) = 0`, the base locus of `|M|` is all of `X`. -/
theorem baseLocus_eq_top_of_subsingleton (M : Divisor X)
    [Subsingleton (M.divisorialSubmodule ⊤)] : M.baseLocus = ⊤ := by
  refine eq_top_iff.mpr fun x _ => (mem_baseLocus_iff M x).mpr fun σ hσ => ?_
  exact absurd (Subsingleton.elim σ 0) hσ

/-- `B(s) = Bs|sD|`, the base locus of the `s`-th multiple of `D`. -/
@[mmp "def_km3a_base_locus_of_multiples"]
def baseLocusOfMultiple (D : Divisor X) (s : ℕ) : Closeds X := (s • D).baseLocus

/-- `B_s = ⋂_{u ≥ 1} B(sᵘ)`, the intersection of the base loci of the multiples of `D` by the
positive powers of `s`. -/
@[mmp "def_km3a_stable_base_locus_of_powers"]
def stableBaseLocusOfPowers (D : Divisor X) (s : ℕ) : Closeds X :=
  ⨅ (u : ℕ) (_ : 1 ≤ u), D.baseLocusOfMultiple (s ^ u)

/-- The stable base locus `B_s` is contained in `B(sᵘ)` for every `u ≥ 1`. -/
theorem stableBaseLocusOfPowers_le (D : Divisor X) (s : ℕ) {u : ℕ} (hu : 1 ≤ u) :
    D.stableBaseLocusOfPowers s ≤ D.baseLocusOfMultiple (s ^ u) :=
  iInf₂_le u hu

end Divisor

end BaseLocus

/-! ### The morphism of a linear system and its image -/

section LinearSystemMap

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections twistIsoOfGeneratingSections twistIso_pullbackSectionOne
  degreeOneElement grading)
open Stacks.AlgebraicGeometry.GeneratingSectionsRestrict (pullbackSectionsₗ
  iSup_nonvanishingOpen_pullbackGlobalSections_eq_top nonvanishingOpen_pullbackGlobalSections)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L] {ι : Type u} (b : Module.Basis ι k Γ(L, ⊤))

/-- For a basis `(sᵢ)` of `H⁰(X, ℒ)`, the open `U ⊆ X` of the points at which some `sᵢ`
generates `ℒ`. -/
@[mmp "def_km2c_linear_system_map"]
def linearSystemLocus : X.Opens := ⨆ i, nonvanishingOpen X L (b i)

/-- A point lies in `U` if and only if some basis section `sᵢ` generates `ℒ` at it. -/
theorem mem_linearSystemLocus_iff (x : X) :
    x ∈ linearSystemLocus k L b ↔ ∃ i, x ∈ nonvanishingOpen X L (b i) :=
  Opens.mem_iSup

/-- The `k`-linear isomorphism `H⁰(X, ℒ) ≃ H⁰(X, ℒ')` induced by an isomorphism `ℒ ≅ ℒ'`. -/
def globalSectionsLinearEquiv {L L' : X.Modules} (e : L ≅ L') : Γ(L, ⊤) ≃ₗ[k] Γ(L', ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  map_add' := map_add _
  map_smul' _ s := Scheme.Modules.Hom.app_smul e.hom _ s
  left_inv s := by
    change ((e.hom ≫ e.inv).app ⊤) s = s
    rw [Iso.hom_inv_id]
    rfl
  right_inv s := by
    change ((e.inv ≫ e.hom).app ⊤) s = s
    rw [Iso.inv_hom_id]
    rfl

/-- The isomorphism `H⁰(X, ℒ) ≃ H⁰(X, ℒ')` is given by `e` on global sections. -/
@[simp]
theorem globalSectionsLinearEquiv_apply {L L' : X.Modules} (e : L ≅ L') (s : Γ(L, ⊤)) :
    globalSectionsLinearEquiv k e s = e.hom.app ⊤ s := rfl

/-- The inverse of `H⁰(X, ℒ) ≃ H⁰(X, ℒ')` is given by `e⁻¹` on global sections. -/
@[simp]
theorem globalSectionsLinearEquiv_symm_apply {L L' : X.Modules} (e : L ≅ L') (s : Γ(L', ⊤)) :
    (globalSectionsLinearEquiv k e).symm s = e.inv.app ⊤ s := rfl

/-- An isomorphism `e : ℒ ≅ ℒ'` of invertible sheaves does not move the open `U`: the basis
`(e sᵢ)` of `H⁰(X, ℒ')` generates `ℒ'` exactly where `(sᵢ)` generates `ℒ`. -/
theorem linearSystemLocus_map_iso {L' : X.Modules} [Stacks.Ample.IsInvertibleModule X L']
    (e : L ≅ L') :
    linearSystemLocus k L' (b.map (globalSectionsLinearEquiv k e)) = linearSystemLocus k L b :=
  iSup_congr fun i => Opens.ext (Stacks.CokernelSupport.nonvanishingLocus_iso_app e (b i))

/-- For `p : X ⟶ Y` and a basis `(tᵢ)` of `H⁰(X, p^*ℒ)` with `tᵢ = p^*sᵢ`, the open of the
linear system of `p^*ℒ` is the preimage `p⁻¹(U)` of that of `ℒ` (Stacks Tag 0H78). -/
theorem linearSystemLocus_pullback {Y : Scheme.{u}} [Y.Over (Spec (.of k))] (p : X ⟶ Y)
    (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback p).obj M)]
    (b : Module.Basis ι k Γ(M, ⊤))
    (b' : Module.Basis ι k Γ((Scheme.Modules.pullback p).obj M, ⊤))
    (hb : ∀ i, b' i = pullbackGlobalSections p M (b i)) :
    linearSystemLocus k ((Scheme.Modules.pullback p).obj M) b' =
      p ⁻¹ᵁ linearSystemLocus k M b := by
  simp only [linearSystemLocus, hb, nonvanishingOpen_pullbackGlobalSections,
    Scheme.Hom.preimage_iSup]

/-- The open `U` is a scheme over `k` through the inclusion into `X`. -/
instance over_linearSystemLocus : (linearSystemLocus k L b).toScheme.Over (Spec (.of k)) :=
  ⟨(linearSystemLocus k L b).ι ≫ (X ↘ Spec (.of k))⟩

/-- The linear system restricted to `U`: `ι →₀ k ≅ H⁰(X, ℒ) → H⁰(U, ℒ|_U)`, sending the `i`-th
standard basis vector to `sᵢ|_U`. -/
def linearSystemRestrict :
    (ι →₀ k) →ₗ[k] Γ((Scheme.Modules.pullback (linearSystemLocus k L b).ι).obj L, ⊤) :=
  (pullbackSectionsₗ k (linearSystemLocus k L b).ι L rfl).comp b.repr.symm.toLinearMap

/-- The restrictions `sᵢ|_U` generate `ℒ|_U` at every point of `U`. -/
theorem iSup_nonvanishingOpen_linearSystemRestrict :
    (⨆ v : ι →₀ k, nonvanishingOpen (linearSystemLocus k L b).toScheme
      ((Scheme.Modules.pullback (linearSystemLocus k L b).ι).obj L)
      (linearSystemRestrict k L b v)) = ⊤ := by
  refine iSup_nonvanishingOpen_pullbackGlobalSections_eq_top L
    (fun v : ι →₀ k => b.repr.symm v) ?_
  refine iSup_le fun i => ?_
  refine le_trans ?_ (le_iSup _ (Finsupp.single i 1))
  rw [Module.Basis.repr_symm_single_one]

/-- The morphism `φ_{|ℒ|} : U → ℙᴺ = Proj (Sym_k (k^ι))` of the linear system of an invertible
sheaf `ℒ` with basis `(sᵢ)_{i ∈ ι}` of `H⁰(X, ℒ)`: the morphism with `φ^*𝒪(1) ≅ ℒ|_U` and
`φ^*xᵢ = sᵢ` (`MMP.Mori.linearSystemMapTwistIso_pullbackSectionOne`), where `U` is the open of
the points at which some `sᵢ` generates `ℒ`. -/
@[mmp "def_km2c_linear_system_map"]
def linearSystemMap :
    (linearSystemLocus k L b).toScheme ⟶ projectiveSpaceOfModule k (ι →₀ k) :=
  morphismOfGeneratingSections k (ι →₀ k)
    ((Scheme.Modules.pullback (linearSystemLocus k L b).ι).obj L)
    (linearSystemRestrict k L b) (iSup_nonvanishingOpen_linearSystemRestrict k L b)

/-- The isomorphism `φ_{|ℒ|}^*𝒪(1) ≅ ℒ|_U`. -/
def linearSystemMapTwistIso :
    Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.pullbackTwistOne (grading k (ι →₀ k))
      (linearSystemMap k L b) ≅ (Scheme.Modules.pullback (linearSystemLocus k L b).ι).obj L :=
  twistIsoOfGeneratingSections k (ι →₀ k) _ (linearSystemRestrict k L b)
    (iSup_nonvanishingOpen_linearSystemRestrict k L b)

/-- `φ_{|ℒ|}^*xᵢ = sᵢ|_U`: the isomorphism `φ^*𝒪(1) ≅ ℒ|_U` carries the pullback of the `i`-th
coordinate to the restriction of the `i`-th basis vector. -/
theorem linearSystemMapTwistIso_pullbackSectionOne (i : ι) :
    (linearSystemMapTwistIso k L b).hom.app ⊤
        (Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.pullbackSectionOne
          (grading k (ι →₀ k)) (linearSystemMap k L b)
          (degreeOneElement k (ι →₀ k) (Finsupp.single i 1))) =
      pullbackGlobalSections (linearSystemLocus k L b).ι L (b i) := by
  refine (twistIso_pullbackSectionOne k (ι →₀ k) _ (linearSystemRestrict k L b)
    (iSup_nonvanishingOpen_linearSystemRestrict k L b) (Finsupp.single i 1)).trans ?_
  rw [linearSystemRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_symm_single_one]
  rfl

/-- The ideal of the reduced closed subscheme of `ℙᴺ` supported on the closure of the image of
`φ_{|ℒ|}`. -/
def linearSystemImageIdeal : (projectiveSpaceOfModule k (ι →₀ k)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range (linearSystemMap k L b).base))

/-- The image `Y_ℒ ⊆ ℙᴺ` of `φ_{|ℒ|}`: the closure of `φ_{|ℒ|}(U)` with its reduced structure. -/
@[mmp "def_km2c_linear_system_image"]
abbrev linearSystemImage : Scheme.{u} := (linearSystemImageIdeal k L b).subscheme

/-- For reduced `X`, the kernel of `φ_{|ℒ|}` is the ideal of its image `Y_ℒ`. -/
theorem ker_linearSystemMap [IsReduced X] :
    (linearSystemMap k L b).ker = linearSystemImageIdeal k L b := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  rw [linearSystemImageIdeal, Closeds.coe_top, Set.image_univ]

/-- For reduced `X`, the morphism `φ_{|ℒ|} : U → Y_ℒ` onto its image. -/
@[mmp "def_km2c_linear_system_image"]
def linearSystemMapToImage [IsReduced X] :
    (linearSystemLocus k L b).toScheme ⟶ linearSystemImage k L b :=
  IsClosedImmersion.lift (linearSystemImageIdeal k L b).subschemeι (linearSystemMap k L b)
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_linearSystemMap])

/-- The morphism `φ_{|ℒ|} : U → Y_ℒ` composed with the inclusion `Y_ℒ → ℙᴺ` is `φ_{|ℒ|}`. -/
@[reassoc (attr := simp)]
theorem linearSystemMapToImage_subschemeι [IsReduced X] :
    linearSystemMapToImage k L b ≫ (linearSystemImageIdeal k L b).subschemeι =
      linearSystemMap k L b :=
  IsClosedImmersion.lift_fac _ _ _

/-- `φ_{|ℒ|}` is *birational onto its image* if `φ_{|ℒ|} : U → Y_ℒ` is a birational morphism. -/
@[mmp "def_km2c_linear_system_image"]
def IsBirationalOntoImage [IsReduced X] : Prop :=
  IsBirationalMorphism (linearSystemMapToImage k L b)

end LinearSystemMap

/-! ### The locally free locus and reflexive powers -/

section Reflexive

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf reflexiveHull)

variable {X : Scheme.{u}}

/-- The *locally free locus* `X⁰ ⊆ X` of an `𝒪_X`-module `L`: the union of all opens `U` such that
`L|_U` is locally free. -/
@[mmp "def_km2c_locally_free_locus"]
def locallyFreeLocus (L : X.Modules) : X.Opens :=
  sSup {U : X.Opens | ((Scheme.Modules.restrictFunctor U.ι).obj L).IsLocallyFree}

/-- A point lies in the locally free locus of `L` if and only if it has an open neighbourhood `U`
such that `L|_U` is locally free. -/
theorem mem_locallyFreeLocus_iff (L : X.Modules) (x : X) :
    x ∈ locallyFreeLocus L ↔
      ∃ U : X.Opens, x ∈ U ∧ ((Scheme.Modules.restrictFunctor U.ι).obj L).IsLocallyFree := by
  rw [locallyFreeLocus, Opens.mem_sSup]
  exact ⟨fun ⟨U, hU, hx⟩ => ⟨U, hx, hU⟩, fun ⟨U, hx, hU⟩ => ⟨U, hU, hx⟩⟩

/-- Every open `U` on which `L|_U` is locally free is contained in the locally free locus. -/
theorem le_locallyFreeLocus (L : X.Modules) {U : X.Opens}
    (hU : ((Scheme.Modules.restrictFunctor U.ι).obj L).IsLocallyFree) :
    U ≤ locallyFreeLocus L :=
  le_sSup hU

/-- The *reflexive powers* of an `𝒪_X`-module `L`: `L^{[i]} = (L^{⊗ i})^{**}` for `i ≥ 0` and
`L^{[i]} = 𝓗om(L^{[-i]}, 𝒪_X)` for `i < 0`, where `𝒢^* = 𝓗om(𝒢, 𝒪_X)`. -/
@[mmp "def_km2c_reflexive_power"]
def reflexivePow (L : X.Modules) : ℤ → X.Modules
  | (n : ℕ) => reflexiveHull (Stacks.AlgebraicGeometry.ReflexivePowers.tensorPower L n)
  | Int.negSucc n =>
      dualSheaf (reflexiveHull (Stacks.AlgebraicGeometry.ReflexivePowers.tensorPower L (n + 1)))

/-- For `n ≥ 0`, the reflexive power `L^{[n]}` is `(L^{⊗ n})^{**}`. -/
theorem reflexivePow_natCast (L : X.Modules) (n : ℕ) :
    reflexivePow L n = reflexiveHull (Stacks.AlgebraicGeometry.ReflexivePowers.tensorPower L n) :=
  rfl

/-- For `n > 0`, the reflexive power `L^{[-n]}` is the dual `𝓗om(L^{[n]}, 𝒪_X)`. -/
theorem reflexivePow_neg_natCast (L : X.Modules) {n : ℕ} (hn : 0 < n) :
    reflexivePow L (-n) = dualSheaf (reflexivePow L n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rfl

end Reflexive

/-! ### The divisorial algebra -/

section DivisorialAlgebra

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- Products of sections: `𝒪_X(D)(U) · 𝒪_X(D')(U) ⊆ 𝒪_X(D + D')(U)`. -/
theorem IsDivisorialSection.mul {D D' : Divisor X} {U : X.Opens}
    {φ ψ : ToType ((rationalFunctionsPresheaf X).obj (op U))} (hφ : D.IsDivisorialSection U φ)
    (hψ : D'.IsDivisorialSection U ψ) : (D + D').IsDivisorialSection U (φ * ψ) := by
  intro E h
  have := (hφ E h).mul (hψ E h)
  rwa [DivisorWithCoeffs.coeff_add, neg_add]

/-- The sections over `U` of the divisorial algebra `R(X, B) = ⊕_{m ≥ 0} 𝒪_X(mB)`: the graded
`Γ(X, U)`-subalgebra of `𝒦_X(U)[t]` of the polynomials `∑ φₘ tᵐ` with `φₘ ∈ 𝒪_X(mB)(U)`. -/
@[mmp "def_km3c_divisorial_algebra"]
def divisorialAlgebraSections (B : Divisor X) (U : X.Opens) :
    Subalgebra Γ(X, U) (Polynomial ((rationalFunctionsPresheaf X).obj (op U))) where
  carrier := {p | ∀ m : ℕ, p.coeff m ∈ (m • B).divisorialSubmodule U}
  mul_mem' {p q} hp hq m := by
    rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have := IsDivisorialSection.mul (hp ij.1) (hq ij.2)
    rwa [← add_nsmul, hij] at this
  add_mem' {p q} hp hq m := by
    rw [Polynomial.coeff_add]
    exact Submodule.add_mem _ (hp m) (hq m)
  algebraMap_mem' r m := by
    rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
    split_ifs with hm
    · subst hm
      rw [zero_nsmul]
      exact isDivisorialSection_algebraMap le_rfl r
    · exact Submodule.zero_mem _

/-- A polynomial `∑ φₘ tᵐ` is a section of `R(X, B)` over `U` if and only if `φₘ ∈ 𝒪_X(mB)(U)` for
every `m`. -/
@[simp]
theorem mem_divisorialAlgebraSections {B : Divisor X} {U : X.Opens}
    {p : Polynomial ((rationalFunctionsPresheaf X).obj (op U))} :
    p ∈ B.divisorialAlgebraSections U ↔ ∀ m : ℕ, p.coeff m ∈ (m • B).divisorialSubmodule U :=
  Iff.rfl

/-- Restricting the coefficients of a section of `R(X, B)` over `U` to `V ⊆ U` gives a section of
`R(X, B)` over `V`. -/
theorem map_mem_divisorialAlgebraSections (B : Divisor X) {U V : X.Opens} (i : V ⟶ U)
    {p : Polynomial ((rationalFunctionsPresheaf X).obj (op U))}
    (hp : p ∈ B.divisorialAlgebraSections U) :
    p.map ((rationalFunctionsPresheaf X).map i.op).hom ∈ B.divisorialAlgebraSections V :=
  fun m => by
    rw [Polynomial.coeff_map]
    exact (hp m).map i

/-- The *divisorial algebra* `R(X, B) = ⊕_{m ≥ 0} 𝒪_X(mB)` of a divisor `B`, as a presheaf of
commutative rings: the graded subalgebra of `𝒦_X[t] = ⊕_m 𝒦_X tᵐ` whose sections over `U` are
the polynomials `∑ φₘ tᵐ` with `φₘ ∈ 𝒪_X(mB)(U)`, multiplication being induced by the product of
rational functions. Its sections over `U` are a `Γ(X, U)`-algebra
(`MMP.Mori.Divisor.divisorialAlgebraSections`). -/
@[mmp "def_km3c_divisorial_algebra"]
def divisorialAlgebra (B : Divisor X) : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (B.divisorialAlgebraSections U.unop)
  map {U V} i := CommRingCat.ofHom
    { toFun := fun p => ⟨p.1.map ((rationalFunctionsPresheaf X).map i).hom,
        B.map_mem_divisorialAlgebraSections i.unop p.2⟩
      map_one' := Subtype.ext (Polynomial.map_one _)
      map_mul' := fun p q => Subtype.ext (Polynomial.map_mul _)
      map_zero' := Subtype.ext (Polynomial.map_zero _)
      map_add' := fun p q => Subtype.ext (Polynomial.map_add _) }
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => Subtype.ext ?_)
    change p.1.map ((rationalFunctionsPresheaf X).map (𝟙 U)).hom = p.1
    rw [CategoryTheory.Functor.map_id]
    exact Polynomial.map_id
  map_comp {U V W} i j := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => Subtype.ext ?_)
    change p.1.map ((rationalFunctionsPresheaf X).map (i ≫ j)).hom =
      (p.1.map ((rationalFunctionsPresheaf X).map i).hom).map
        ((rationalFunctionsPresheaf X).map j).hom
    rw [Polynomial.map_map, CategoryTheory.Functor.map_comp]
    rfl

end Divisor

end DivisorialAlgebra

/-! ### The canonical ring and the Euler characteristic function -/

section CanonicalRing

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- The degree-`m` piece `R_m = H⁰(X, mK_X + ⌊mΔ⌋) ⊆ K(X)` of the canonical ring of `(X, Δ)`, for
a canonical divisor `K` of `X`. -/
@[mmp "def_km3a_canonical_ring"]
def canonicalRingPiece {n : ℕ} (K : Divisor X) (_hK : K.IsCanonicalDivisor f n) (Δ : QDivisor X)
    (m : ℕ) : Submodule Γ(X, ⊤) ((rationalFunctionsPresheaf X).obj (op ⊤)) :=
  (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Δ)).divisorialSubmodule ⊤

/-- The *canonical ring* `R(X, K_X + Δ) = ⊕_{m ≥ 0} R_m tᵐ` of `(X, Δ)`, for a canonical divisor
`K` of `X` and `R_m = H⁰(X, mK_X + ⌊mΔ⌋)`: the graded subspace of the polynomial ring
`K(X)[t]` of the polynomials whose coefficient of `tᵐ` lies in `R_m`. It is a
`Γ(X, 𝒪_X)`-submodule, hence a `k`-subspace through `f`. -/
@[mmp "def_km3a_canonical_ring"]
def canonicalRing {n : ℕ} (K : Divisor X) (hK : K.IsCanonicalDivisor f n) (Δ : QDivisor X) :
    Submodule Γ(X, ⊤) (Polynomial ((rationalFunctionsPresheaf X).obj (op ⊤))) where
  carrier := {p | ∀ m : ℕ, p.coeff m ∈ K.canonicalRingPiece f hK Δ m}
  zero_mem' m := by
    rw [Polynomial.coeff_zero]
    exact Submodule.zero_mem _
  add_mem' {p q} hp hq m := by
    rw [Polynomial.coeff_add]
    exact Submodule.add_mem _ (hp m) (hq m)
  smul_mem' r p hp m := by
    rw [Polynomial.coeff_smul]
    exact Submodule.smul_mem _ r (hp m)

/-- A polynomial lies in the canonical ring if and only if its coefficient of `tᵐ` lies in `R_m`
for every `m`. -/
@[simp]
theorem mem_canonicalRing {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor f n)
    {Δ : QDivisor X} {p : Polynomial ((rationalFunctionsPresheaf X).obj (op ⊤))} :
    p ∈ K.canonicalRing f hK Δ ↔ ∀ m : ℕ, p.coeff m ∈ K.canonicalRingPiece f hK Δ m :=
  Iff.rfl

/-- For `φ ∈ R_m`, the monomial `φ tᵐ` lies in the canonical ring. -/
theorem monomial_mem_canonicalRing {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor f n)
    {Δ : QDivisor X} {m : ℕ} {φ : (rationalFunctionsPresheaf X).obj (op ⊤)}
    (hφ : φ ∈ K.canonicalRingPiece f hK Δ m) :
    Polynomial.monomial m φ ∈ K.canonicalRing f hK Δ := fun j => by
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact h ▸ hφ
  · exact Submodule.zero_mem _

end Divisor

end CanonicalRing

section EulerPolynomial

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X]

namespace Divisor

/-- The *Euler characteristic function* `P : ℤᵏ → ℤ` of `(Y; D₁, …, D_k; A)`, for divisors
`Dᵢ` and a `ℚ`-divisor `A` on a scheme `Y` over `k`:
`P(u₁, …, u_k) = χ(Y, 𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉)) = ∑ⱼ (-1)ʲ dim_k Hʲ(Y, 𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉))`. -/
@[mmp "def_km3b_multidivisor_euler_polynomial"]
def eulerPolynomial {ι : Type*} [Fintype ι] (D : ι → Divisor X) (A : QDivisor X) (u : ι → ℤ) :
    ℤ :=
  ∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f
    (∑ i, u i • D i + DivisorWithCoeffs.roundUp A).divisorialSheaf j) : ℤ)

/-- On a proper scheme, the Euler characteristic function is the Euler characteristic of
`𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉)`, whenever that sheaf is coherent. -/
theorem eulerPolynomial_eq_eulerCharacteristic [IsProper f] {ι : Type*} [Fintype ι]
    (D : ι → Divisor X) (A : QDivisor X) (u : ι → ℤ)
    [(∑ i, u i • D i + DivisorWithCoeffs.roundUp A).divisorialSheaf.IsCoherent] :
    eulerPolynomial k f D A u =
      eulerCharacteristic k f (∑ i, u i • D i + DivisorWithCoeffs.roundUp A).divisorialSheaf :=
  rfl

end Divisor

end EulerPolynomial

end MMP.Mori
