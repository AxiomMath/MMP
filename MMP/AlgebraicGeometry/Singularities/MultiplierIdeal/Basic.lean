module

public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation

/-!
# The Jacobian section, the relative canonical divisor and multiplier ideals (Lazarsfeld §9.1–9.2)

Let `μ : X' ⟶ X` be a morphism of non-singular varieties of dimension `n` over `k`. Pull-back of
`n`-forms is a homomorphism of line bundles `j_μ : μ^*Ω^n_X ⟶ Ω^n_{X'}`; the corresponding section
of `ω_{X'} ⊗ μ^*ω_X^{-1}` is the *Jacobian section*. For `μ` proper birational, the *relative
canonical divisor* `K_{X'/X}` is the divisor of `j_μ` (and `0` if `j_μ` is not regular, a
convention that never applies). For a log resolution `μ` of an `ℝ`-divisor `D`
the *multiplier ideal computed on `μ`* is `𝒥_μ(X, D) = μ_*𝒪_{X'}(K_{X'/X} - ⌊μ^*D⌋) ⊆ K(X)`, and
a *multiplier ideal* of `D` is `𝒥_μ(X, D)` for some log resolution `μ`.

## Main definitions

* `MMP.Intersection.jacobianSection`: `j_μ`, as the homomorphism `μ^*Ω^n_{X/k} ⟶ Ω^n_{X'/k}`.
* `MMP.Intersection.IsRegularHom`, `MMP.Intersection.IsDivisorOfHom`: regularity and divisor of a
  homomorphism of line bundles, i.e. of the corresponding section of `M ⊗ L⁻¹`.
* `MMP.Intersection.IsRelativeCanonicalDivisor`: `K = K_{X'/X}`.
* `MMP.Intersection.multiplierIdealSections`: the sections of `μ_*𝒪_{X'}(G)` as subsets of `K(X)`.
* `MMP.Intersection.IsMultiplierIdealOn`, `MMP.Intersection.IsMultiplierIdeal`.

## Implementation notes

* **The Jacobian section.** The section `j_μ ∈ H⁰(X', ω_{X'} ⊗ μ^*ω_X^{-1})` "corresponding to"
  the homomorphism `μ^*Ω^n_X ⟶ Ω^n_{X'}` is represented by that homomorphism itself,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` of the square
  `μ ≫ s_X = (μ ≫ s_X) ≫ 𝟙` (the canonical map `μ^*Ω^n_{X/k} ⟶ Ω^n_{X'/k}`, the `n`-th
  exterior power of `μ^*Ω_{X/k} ⟶ Ω_{X'/k}`), under the canonical identification
  `Hom(L, M) = H⁰(M ⊗ L⁻¹)` for a line bundle `L`. Accordingly regularity and the divisor are
  stated for the homomorphism: on an open `U` trivializing `L` by `e` and `M` by `e'`, the local
  function of the section is the `r` with `φ(e) = r e'`, which is the function `s / e_U` of
  `MMP.Intersection.IsRegularSection` for the generator `e_U = e' ⊗ e^∨` of `M ⊗ L⁻¹`.
* **`K_{X'/X}`** is a predicate on a Cartier divisor `K`, with `n = dim X'`; the divisor of a
  regular `j_μ` is determined by its local equations.
* **The multiplier ideal.** `𝒪_{X'}(G)` for a Weil divisor `G` on the normal integral scheme `X'`
  has sections over `V` the rational functions `h` with `ord_P(h) + coeff_P(G) ≥ 0` for every
  prime divisor `P` meeting `V` (`h = 0` allowed), and `0` over `V = ∅`; through the isomorphism
  `μ^* : K(X) ≅ K(X')` the sections of `μ_*𝒪_{X'}(G)` over `U ⊆ X` are the `g ∈ K(X)` with
  `μ^*g ∈ 𝒪_{X'}(G)(μ⁻¹U)`. This is the `𝒪_X`-submodule of `K(X) = K(X')` of the source. The
  order is read with `MMP.Mori.PrimeDivisor.valuationOver` (`v_P(μ^* g) = exp(-ord_P(μ^*g))`),
  so the condition is `v_P(μ^*g) ≤ exp(coeff_P G)`.
* `G = K_{X'/X} - ⌊μ^*D⌋` is formed from the Weil divisor of `K_{X'/X}` and the round-down
  `MMP.Intersection.WeilRDivisor.roundDown` of the Weil divisor of `μ^*D`; on the non-singular
  `X'` Weil and Cartier divisors agree, and `𝒪_{X'}(G)` is the line bundle of the Cartier
  divisor of the source.
* The scheme-theoretic properties of `X'` used to state these (integral, locally Noetherian,
  normal) and dominance of `μ` follow from `μ` being a log resolution; they are bound
  existentially inside `IsMultiplierIdealOn`, so they add no hypothesis.
* **`𝒥(X, D)`** is defined exactly as the source does: `𝒥` is *a* multiplier ideal of `D` if
  `𝒥 = 𝒥_μ(X, D)` for *some* log resolution `μ`. Independence of the log resolution
  (Lazarsfeld Thm. 9.2.18) is a theorem and is not assumed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori (Divisor RDivisor DivisorWithCoeffs)

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-! ### Regular homomorphisms of line bundles and their divisors -/

/-- A homomorphism `φ : L ⟶ M` of line bundles is *regular* (the corresponding section of
`M ⊗ L⁻¹` is regular): on every open `U` trivializing `L` by `e` and `M` by `e'`, the function
`r` with `φ(e) = r e'` is a non-zero-divisor at every point of `U`. -/
@[mmp "def_p09a_relative_canonical_divisor"]
def IsRegularHom {L M : X.Modules} (φ : L ⟶ M) : Prop :=
  ∀ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)), IsTrivializingGenerator L U e →
    IsTrivializingGenerator M U e' → ∀ r : Γ(X, U), φ.app U e = r • e' →
      ∀ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x)

/-- `D = div(φ)` for a regular homomorphism `φ : L ⟶ M` of line bundles (the divisor of the
corresponding section of `M ⊗ L⁻¹`): the effective divisor with local equation `r` on every open
`U` trivializing `L` by `e` and `M` by `e'`, where `φ(e) = r e'`. -/
@[mmp "def_p09a_relative_canonical_divisor"]
def IsDivisorOfHom {L M : X.Modules} (φ : L ⟶ M) (D : X.CartierDivisor) : Prop :=
  IsRegularHom φ ∧ IsEffective D ∧
    ∀ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)), IsTrivializingGenerator L U e →
      IsTrivializingGenerator M U e' → ∀ r : Γ(X, U), φ.app U e = r • e' →
        ∃ h : IsUnit (toTotalQuotient U r), IsLocalEquationOn D U h.unit

/-! ### The Jacobian section and the relative canonical divisor -/

variable (sX : X ⟶ Spec (.of k))

/-- **The Jacobian section** `j_μ` of a morphism `μ : X' ⟶ X` of varieties of dimension `n` over
`k` (Lazarsfeld §9.1.B): the homomorphism `μ^*Ω^n_{X/k} ⟶ Ω^n_{X'/k}` given by pull-back of
`n`-forms, the `n`-th exterior power of `μ^*Ω_{X/k} ⟶ Ω_{X'/k}`; it corresponds to a section of
`ω_{X'} ⊗ μ^*ω_X^{-1}`. -/
@[mmp "def_p09a_jacobian_section"]
def jacobianSection (μ : X' ⟶ X) (n : ℕ) :
    (Scheme.Modules.pullback μ).obj (Scheme.Hom.relativeDifferentialForms sX n) ⟶
      Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n :=
  Scheme.Hom.relativeDifferentialFormsMap μ sX (μ ≫ sX) (𝟙 _) (by simp) n

/-- **The relative canonical divisor** `K_{X'/X}` of `μ : X' ⟶ X` (Lazarsfeld §9.1.B, (9.1)), for
`X'` of dimension `n`: `K` is the divisor of the Jacobian section `j_μ` if `j_μ` is regular, and
`K = 0` otherwise. -/
@[mmp "def_p09a_relative_canonical_divisor"]
def IsRelativeCanonicalDivisor (μ : X' ⟶ X) (K : X'.CartierDivisor) : Prop :=
  ∃ n : ℕ, topologicalKrullDim X' = n ∧
    ((IsRegularHom (jacobianSection sX μ n) ∧ IsDivisorOfHom (jacobianSection sX μ n) K) ∨
      (¬ IsRegularHom (jacobianSection sX μ n) ∧ K = 0))

/-! ### Multiplier ideals -/

section Multiplier

variable [IsIntegral X]

/-- The sections over `U ⊆ X` of `μ_*𝒪_{X'}(G)` for a Weil divisor `G` on the normal integral
scheme `X'`, as a subset of `K(X)` through `μ^* : K(X) → K(X')`: the `g` with
`ord_P(μ^*g) + coeff_P(G) ≥ 0` for every prime divisor `P` of `X'` meeting `μ⁻¹(U)`, and only
`g = 0` when `μ⁻¹(U) = ∅`. -/
@[mmp "def_p09a_multiplier_ideal_resolution"]
def multiplierIdealSections [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] (μ : X' ⟶ X)
    [IsDominant μ] (G : Divisor X') (U : X.Opens) : Set X.functionField :=
  {g | (μ ⁻¹ᵁ U = ⊥ → g = 0) ∧ ∀ P : MMP.Mori.PrimeDivisor X', (P.support ∩ μ ⁻¹ᵁ U).Nonempty →
    P.valuationOver μ g ≤ WithZero.exp (G.coeff P)}

/-- **The multiplier ideal computed on a log resolution** (Lazarsfeld Def. 9.2.1, (9.7)): for a
log resolution `μ : X' ⟶ X` of the `ℝ`-divisor `D`, `𝒥` (given by its sections over the opens of
`X`, as subsets of `K(X) = K(X')`) is `𝒥_μ(X, D) = μ_*𝒪_{X'}(K_{X'/X} - ⌊μ^*D⌋)`. -/
@[mmp "def_p09a_multiplier_ideal_resolution"]
def IsMultiplierIdealOn (D : RCartierDivisor X) (μ : X' ⟶ X) (J : X.Opens → Set X.functionField) :
    Prop :=
  IsLogResolution sX D μ ∧
    ∃ (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (_ : IsNormal X') (_ : IsDominant μ)
      (K : X'.CartierDivisor) (wK : Divisor X') (F : RDivisor X'),
      IsRelativeCanonicalDivisor sX μ K ∧ IsWeilDivisorOfCartier K wK ∧ IsWeilPullback μ D F ∧
        J = multiplierIdealSections μ (wK - WeilRDivisor.roundDown F)

/-- **A multiplier ideal** `𝒥(X, D)` of an `ℝ`-divisor `D` (Lazarsfeld Def. 9.2.1): `𝒥 ⊆ K(X)` is
`𝒥_μ(X, D)` for some log resolution `μ` of `D`. -/
@[mmp "def_p09a_multiplier_ideal"]
def IsMultiplierIdeal (D : RCartierDivisor X) (J : X.Opens → Set X.functionField) : Prop :=
  ∃ (X' : Scheme.{u}) (μ : X' ⟶ X), IsMultiplierIdealOn sX D μ J

end Multiplier

end MMP.Intersection
