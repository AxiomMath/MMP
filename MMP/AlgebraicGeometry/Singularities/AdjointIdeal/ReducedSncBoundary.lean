module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic

/-!
# Adjoint ideals with a reduced simple normal crossing boundary

Let `X` be a smooth variety, `Δ` a reduced snc divisor on `X` and `D` an effective `ℚ`-divisor
containing no stratum of `Δ`. For a projective log resolution `μ : Y → X` of `Δ + D`, let `Γ` be
the reduced sum of the prime divisors of `Y` of log discrepancy zero for `(X, Δ)`, and write
`K_Y + Γ = μ^*(K_X + Δ) + E`. The *reduced-boundary adjoint ideal* is
`𝒥_{Δ,D} = μ_*𝒪_Y(E - ⌊μ^*D⌋)`. For a linear series `V` whose base locus contains no stratum of
`Δ`, and a rational `c ≥ 0`, `𝒥_{Δ,cV}` is defined in the same way with `μ^*D` replaced by `cF`,
for `F` the fixed divisor of the series pulled back to a log resolution of `Δ` and of `V`.

For a projective morphism `X → Z` to an affine scheme and a graded linear series `V_•` of an
integral Cartier divisor `D`, one nonzero `V_b` of which has base locus containing no stratum of
`Δ`, the *asymptotic adjoint ideal* is `𝒥_{Δ,cV_•} = ⋃_{p ∈ bℤ_{>0}} 𝒥_{Δ,(c/p)V_p}`; for the
complete series it is written `𝒥_{Δ,‖cD‖}`.

## Main definitions

* `MMP.Fourfold.IsZeroLogDiscrepancyDivisor`: `Γ`, the reduced sum of the log discrepancy zero
  prime divisors of `(X, Δ)` on `Y`.
* `MMP.Fourfold.IsAdjointDiscrepancyDivisor`: `E` with `K_Y + Γ = μ^*(K_X + Δ) + E`.
* `MMP.Fourfold.IsReducedAdjointIdealOn`: `𝒥_{Δ,D}` computed on a log resolution `μ`.
* `MMP.Fourfold.sectionsIn`, `MMP.Fourfold.baseLocusIn`: `H⁰(X, 𝒪_X(D)) ⊆ K(X)` and the base
  locus of a set of its sections.
* `MMP.Fourfold.IsFixedDivisorOfPullback`, `MMP.Fourfold.IsFreeModuloFixedDivisor`,
  `MMP.Fourfold.IsSeriesLogResolution`: the fixed divisor of a series pulled back to `Y`, and log
  resolutions of a series.
* `MMP.Fourfold.IsSeriesAdjointIdealOn`, `MMP.Fourfold.IsSeriesAdjointIdeal`: `𝒥_{Δ,cV}`.
* `MMP.Fourfold.IsGradedLinearSeries`, `MMP.Fourfold.completeSeries`: graded linear series over
  `Z` and the complete graded series of `D`.
* `MMP.Fourfold.IsAsymptoticAdjointIdeal`, `MMP.Fourfold.IsAsymptoticAdjointIdealOfDivisor`:
  `𝒥_{Δ,cV_•}` and `𝒥_{Δ,‖cD‖}`.
* `MMP.Fourfold.imageSeries`, `MMP.Fourfold.IsRestrictedAsymptoticAdjointIdeal`: the image
  series of `D` on a prime divisor `S` and `𝒥_{Θ,‖cD‖_S}`, `Θ = (Δ - S)|_S`.

## Implementation notes

* **Ideals as subsets of `K(X)`.** As for multiplier ideals
  (`MMP.Intersection.multiplierIdealSections`), `μ_*𝒪_Y(G)` is given by its sections over each
  open `U ⊆ X`, as the subset of `K(X) = K(Y)` of the `g` with `μ^*g ∈ 𝒪_Y(G)(μ⁻¹U)`.
* **`Γ` and `E`.** The canonical divisors in `K_Y + Γ = μ^*(K_X + Δ) + E` are chosen compatibly
  (`μ_*K_Y = K_X`), so the coefficient of a prime divisor `P` of `Y` in
  `K_Y - μ^*(K_X + Δ)` is `a(P, X, Δ) - 1`, with `a` the log discrepancy
  `MMP.Intersection.IsLogDiscrepancy`. Hence `Γ` has coefficient one exactly at the `P` with
  `a(P, X, Δ) = 0` and zero elsewhere, and `coeff_P(E) = a(P, X, Δ) - 1 + coeff_P(Γ)`. `E` is an
  integral divisor, as `𝒪_Y(E - ⌊μ^*D⌋)` requires; for `(X, Δ)` log smooth with `Δ` reduced the
  log discrepancies are integers, so this is no restriction.
* **The log resolution is given.** `𝒥_{Δ,D}` is stated for a given projective log resolution
  `μ` (`MMP.Fourfold.IsLogResolution` of `Δ + D`). Independence of `μ` is a theorem, not used.
  The scheme-theoretic properties of `Y` needed to state the definition (integral, locally
  Noetherian, normal, a normal variety, `μ` dominant and birational) follow from `μ` being a log
  resolution and are bound existentially, so they add no hypothesis.
* **Linear series.** A linear series of a divisor `D` is a set of rational functions contained in
  `H⁰(X, 𝒪_X(D)) = {g | div g + D ≥ 0} ⊆ K(X)` (`MMP.Fourfold.sectionsIn`); `𝒥_{Δ,cV}` depends
  only on that set, so it is stated for any subgroup of `H⁰(X, 𝒪_X(D))`. Its base locus is the
  set of points at which every nonzero `g ∈ V` vanishes as a section of `𝒪_X(D)`, that is, lies
  on a component of the effective divisor `div g + D`; on a smooth (locally factorial) variety
  this is the zero locus of the base ideal.
* **The resolved series.** A log resolution of `Δ` and of `V` is a projective log resolution `μ`
  of `Δ` such that `μ^*V = |M| + F` with `M` free and `Ex(μ) ∪ μ⁻¹(Supp Δ) ∪ Supp F` snc; here
  `F_P = min_{0 ≠ g ∈ V} coeff_P(div(μ^*g) + μ^*D)` is the fixed divisor of `μ^*V`, and
  freeness of the moving part says that at every point `y ∈ Y` some `g ∈ V` has
  `div(μ^*g) + μ^*D - F` passing through no prime divisor containing `y`.
* **The asymptotic ideal.** For each `p ∈ bℤ_{>0}`, `𝒥_{Δ,(c/p)V_p}` is the ideal computed on
  some log resolution of `Δ` and `V_p`. The union of the increasing family of subsheaves is the
  subsheaf whose sections over `U` are the `g` lying, near every point of `U`, in some
  `𝒥_{Δ,(c/p)V_p}`; this is the union in the category of sheaves (over a quasi-compact `U` it is
  the union of the sections, the family being directed for divisibility).
* **Graded linear series over `Z`.** For `X → Z` with `Z = Spec A` affine, a graded linear
  series of `D` is a family `V_m ⊆ H⁰(X, 𝒪_X(mD))` of `A`-submodules (through
  `A = Γ(Z, 𝒪_Z) → Γ(X, 𝒪_X) → K(X)`) with `1 ∈ V_0` and `V_m V_n ⊆ V_{m+n}`.
* **The image series.** For a prime divisor `S` of `X` (an integral closed subscheme), a section
  of `𝒪_X(mD)` restricts to `S` once `S` is not a component of `D`: it lies in `𝒪_{X,η_S}` and
  maps to `K(S)`. For general `D` the series is formed from a linearly equivalent `D + div(φ)`
  of which `S` is not a component, and `D|_S` is the restriction of that divisor; this choice is
  bound existentially.
* The base field of the source is `ℂ`; the definitions are stated over any field `k`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-! ### Strata and the reduced snc boundary -/

/-- A subset `T ⊆ X` *contains no stratum* of the divisor `Δ`: no stratum of `Δ`
(`MMP.Fourfold.IsSNCStratum`) is contained in `T`. -/
def ContainsNoStratum (Δ : Divisor X) (T : Set X) : Prop :=
  ∀ S : Set X, IsSNCStratum Δ S → ¬ S ⊆ T

/-- `Δ` is a *reduced snc divisor* on `X` (over `k`): every coefficient is `0` or `1`, and `Δ` is
simple normal crossing. -/
def IsReducedSNC (Δ : Divisor X) : Prop :=
  MMP.Intersection.IsReducedEffective Δ ∧ DivisorWithCoeffs.IsSNC sX Δ

section Discrepancy

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{u}} (μ : Y ⟶ X)
  (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)

/-! ### The zero log discrepancy divisor and the adjoint discrepancy divisor -/

/-- `Γ` is the *reduced sum of the prime divisors of `Y` of log discrepancy zero* for `(X, Δ)`:
every coefficient of `Γ` is `0` or `1`, and it is `1` exactly at the prime divisors `P` of `Y`
with `a(P, X, Δ) = 0`. -/
def IsZeroLogDiscrepancyDivisor (Δ : Divisor X) (Γ : Divisor Y) : Prop :=
  MMP.Intersection.IsReducedEffective Γ ∧ ∀ P : MMP.Mori.PrimeDivisor Y,
    Γ.coeff P = 1 ↔ ∃ n : ℕ,
      MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ 0

/-- `E` is the divisor with `K_Y + Γ = μ^*(K_X + Δ) + E`, for compatible canonical divisors
(`μ_*K_Y = K_X`): at every prime divisor `P` of `Y`, `coeff_P(E) = a(P, X, Δ) - 1 + coeff_P(Γ)`,
where `a(P, X, Δ) = 1 + coeff_P(K_Y - μ^*(K_X + Δ))` is the log discrepancy. -/
def IsAdjointDiscrepancyDivisor (Δ : Divisor X) (Γ E : Divisor Y) : Prop :=
  ∀ P : MMP.Mori.PrimeDivisor Y, ∃ (n : ℕ) (a : ℝ),
    MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩ a ∧
      (E.coeff P : ℝ) = a - 1 + Γ.coeff P

end Discrepancy

/-! ### The adjoint ideal of a `ℚ`-divisor -/

section Divisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The reduced-boundary adjoint ideal computed on a log resolution.** Let `X` be a smooth
variety, `Δ` a reduced snc divisor, `D` an effective `ℚ`-divisor whose support contains no stratum
of `Δ`, and `μ : Y ⟶ X` a projective log resolution of `Δ + D`. With `Γ` the reduced sum of the
prime divisors of `Y` of log discrepancy zero for `(X, Δ)` and `K_Y + Γ = μ^*(K_X + Δ) + E`,
`J` (given by its sections over the opens of `X`, as subsets of `K(X) = K(Y)`) is
`𝒥_{Δ,D} = μ_*𝒪_Y(E - ⌊μ^*D⌋)`. -/
@[mmp "def_fourfold_reduced_adjoint_ideal"]
def IsReducedAdjointIdealOn (Δ : Divisor X) (D : QDivisor X) {Y : Scheme.{u}} (μ : Y ⟶ X)
    (J : X.Opens → Set X.functionField) : Prop :=
  IsNormalVariety k sX ∧ IsSmoothScheme sX ∧ IsReducedSNC sX Δ ∧ (∀ P, 0 ≤ D.coeff P) ∧
    ContainsNoStratum Δ D.supp ∧ IsLogResolution sX (Divisor.toQDivisor Δ + D) μ ∧
    ∃ (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y) (_ : IsDominant μ)
      (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
      (hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp)
      (Γ E : Divisor Y) (F : QDivisor Y),
      IsZeroLogDiscrepancyDivisor sX μ hY hμ Δ Γ ∧ IsAdjointDiscrepancyDivisor sX μ hY hμ Δ Γ E ∧
        D.IsPullback μ hD F ∧
        J = MMP.Intersection.multiplierIdealSections μ
          (E - MMP.Intersection.WeilRDivisor.roundDown (QDivisor.toRDivisor F))

end Divisor

/-! ### Sections, base loci and fixed divisors of linear series -/

section Series

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- `H⁰(X, 𝒪_X(D))` as a subset of `K(X)`: the rational functions `g` with `div g + D ≥ 0`, that
is, `v_P(g) ≤ exp(coeff_P D)` (`ord_P(g) + coeff_P(D) ≥ 0`) at every prime divisor `P`
(`g = 0` included). -/
def sectionsIn (D : Divisor X) : Set X.functionField :=
  {g | ∀ P : MMP.Mori.PrimeDivisor X, P.divisorialValuation g ≤ WithZero.exp (D.coeff P)}

/-- `H⁰(X, 𝒪_X(D))` as an additive subgroup of `K(X)`. -/
def sectionsSubgroup (D : Divisor X) : AddSubgroup X.functionField where
  carrier := sectionsIn D
  zero_mem' := fun P => by simp
  add_mem' := fun {g h} hg hh P =>
    ((P.divisorialValuation).map_add g h).trans (max_le (hg P) (hh P))
  neg_mem' := fun {g} hg P => by
    simpa only [Valuation.map_neg] using hg P

/-- The *base locus* of a set `V ⊆ H⁰(X, 𝒪_X(D))` of sections: the points `x` at which every
nonzero `g ∈ V` vanishes as a section of `𝒪_X(D)`, that is, `x` lies on a prime divisor `P` with
positive coefficient `ord_P(g) + coeff_P(D) > 0` in `div g + D`. -/
def baseLocusIn (V : Set X.functionField) (D : Divisor X) : Set X :=
  {x | ∀ g ∈ V, g ≠ 0 → ∃ P : MMP.Mori.PrimeDivisor X, x ∈ P.support ∧
    P.divisorialValuation g < WithZero.exp (D.coeff P)}

variable {Y : Scheme.{u}} (μ : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsDominant μ]

/-- `F` is the *fixed divisor of the pulled-back series* `μ^*V`, for `V ⊆ H⁰(X, 𝒪_X(D))` and
`Dμ = μ^*D`: at every prime divisor `P` of `Y`,
`coeff_P(F) = min_{0 ≠ g ∈ V} coeff_P(div(μ^*g) + Dμ)`, that is, every `g ∈ V` has
`v_P(μ^*g) ≤ exp(coeff_P(Dμ) - coeff_P(F))`, with equality for some nonzero `g ∈ V`. -/
def IsFixedDivisorOfPullback (V : Set X.functionField) (Dμ F : Divisor Y) : Prop :=
  ∀ P : MMP.Mori.PrimeDivisor Y,
    (∀ g ∈ V, P.valuationOver μ g ≤ WithZero.exp (Dμ.coeff P - F.coeff P)) ∧
      ∃ g ∈ V, g ≠ 0 ∧ P.valuationOver μ g = WithZero.exp (Dμ.coeff P - F.coeff P)

/-- The *moving part* `μ^*V - F` of the pulled-back series is *free*: at every point `y ∈ Y` some
nonzero `g ∈ V` has `div(μ^*g) + Dμ - F` passing through no prime divisor containing `y`, i.e.
`coeff_P(div(μ^*g) + Dμ) = coeff_P(F)` for every prime divisor `P ∋ y`. -/
def IsFreeModuloFixedDivisor (V : Set X.functionField) (Dμ F : Divisor Y) : Prop :=
  ∀ y : Y, ∃ g ∈ V, g ≠ 0 ∧ ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support →
    P.valuationOver μ g = WithZero.exp (Dμ.coeff P - F.coeff P)

/-- `μ` is a *log resolution of `Δ` and of the series `V`* (with `Dμ = μ^*D`) with fixed divisor
`F`: `μ` is a projective log resolution of `Δ`, `μ^*V = |M| + F` with `F` the fixed divisor of
`μ^*V` and `M` free, and `Ex(μ) ∪ μ⁻¹(Supp Δ) ∪ Supp F` is an snc divisor. -/
def IsSeriesLogResolution (Δ : Divisor X) (V : Set X.functionField) (Dμ F : Divisor Y) : Prop :=
  IsLogResolution sX (Divisor.toQDivisor Δ) μ ∧ IsFixedDivisorOfPullback μ V Dμ F ∧
    IsFreeModuloFixedDivisor μ V Dμ F ∧
    IsSNCSubset (μ ≫ sX) (exceptionalSet μ ⊔ Δ.supp.preimage μ.continuous ⊔ F.supp)

end Series

/-! ### The adjoint ideal of a linear series -/

section SeriesIdeal

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The reduced-boundary adjoint ideal of a linear series, computed on a log resolution.** Let
`X` be a smooth variety, `Δ` a reduced snc divisor, `D` an integral Cartier divisor, `V` a linear
series of `D` (an additive subgroup of `H⁰(X, 𝒪_X(D)) ⊆ K(X)`) whose base locus contains no
stratum of `Δ`, and `c ≥ 0` rational. For a log resolution `μ : Y ⟶ X` of `Δ` and `V`, with `F`
the fixed divisor of the resolved series `μ^*V`, `Γ` the reduced sum of the prime divisors of `Y`
of log discrepancy zero for `(X, Δ)` and `K_Y + Γ = μ^*(K_X + Δ) + E`, `J` is
`𝒥_{Δ,cV} = μ_*𝒪_Y(E - ⌊cF⌋)`. -/
@[mmp "def_fourfold_reduced_adjoint_ideal"]
def IsSeriesAdjointIdealOn (Δ D : Divisor X) (V : AddSubgroup X.functionField) (c : ℚ)
    {Y : Scheme.{u}} (μ : Y ⟶ X) (J : X.Opens → Set X.functionField) : Prop :=
  IsNormalVariety k sX ∧ IsSmoothScheme sX ∧ IsReducedSNC sX Δ ∧ D.IsCartier ∧
    (V : Set X.functionField) ⊆ sectionsIn D ∧ ContainsNoStratum Δ (baseLocusIn V D) ∧ 0 ≤ c ∧
    ∃ (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y) (_ : IsDominant μ)
      (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
      (hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp)
      (Dμ F Γ E : Divisor Y),
      D.IsPullback μ hD Dμ ∧ IsSeriesLogResolution sX μ Δ V Dμ F ∧
        IsZeroLogDiscrepancyDivisor sX μ hY hμ Δ Γ ∧ IsAdjointDiscrepancyDivisor sX μ hY hμ Δ Γ E ∧
        J = MMP.Intersection.multiplierIdealSections μ
          (E - MMP.Intersection.WeilRDivisor.roundDown ((c : ℝ) • Divisor.toRDivisor F))

/-- `J = 𝒥_{Δ,cV}`: the reduced-boundary adjoint ideal of the linear series `V`, computed on some
log resolution of `Δ` and `V`. -/
@[mmp "def_fourfold_reduced_adjoint_ideal"]
def IsSeriesAdjointIdeal (Δ D : Divisor X) (V : AddSubgroup X.functionField) (c : ℚ)
    (J : X.Opens → Set X.functionField) : Prop :=
  ∃ (Y : Scheme.{u}) (μ : Y ⟶ X), IsSeriesAdjointIdealOn sX Δ D V c μ J

end SeriesIdeal

/-! ### Graded linear series and the asymptotic adjoint ideal -/

section Asymptotic

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {Z : Scheme.{u}} (f : X ⟶ Z)

/-- The image in `K(X)` of a regular function `a ∈ Γ(Z, 𝒪_Z)` under `f : X ⟶ Z`. -/
def baseFunction (a : Γ(Z, ⊤)) : X.functionField :=
  X.presheaf.germ ⊤ (genericPoint X) trivial (f.appTop a)

/-- `V_•` is a *graded linear series* of the divisor `D` over `Z` (for `f : X ⟶ Z`, `Z = Spec A`
affine): each `V_m ⊆ H⁰(X, 𝒪_X(mD))` is an `A`-submodule (stable under multiplication by the
images of `A = Γ(Z, 𝒪_Z)` in `K(X)`), `1 ∈ V_0`, and `V_m · V_n ⊆ V_{m+n}`. -/
def IsGradedLinearSeries (D : Divisor X) (V : ℕ → AddSubgroup X.functionField) : Prop :=
  (∀ m : ℕ, (V m : Set X.functionField) ⊆ sectionsIn ((m : ℤ) • D)) ∧
    (∀ (m : ℕ) (a : Γ(Z, ⊤)) (g : X.functionField), g ∈ V m → baseFunction f a * g ∈ V m) ∧
    (1 : X.functionField) ∈ V 0 ∧
    ∀ (m n : ℕ) (g h : X.functionField), g ∈ V m → h ∈ V n → g * h ∈ V (m + n)

/-- **The asymptotic reduced-boundary adjoint ideal.** Let `f : X ⟶ Z` be projective with `X`
smooth and `Z` affine, `Δ` a reduced snc divisor, and `V_•` a graded linear series of an integral
Cartier divisor `D`, with `V_b ≠ 0` (`b > 0`) whose base locus contains no stratum of `Δ`. For
rational `c > 0`, `J = 𝒥_{Δ,cV_•} = ⋃_{p ∈ bℤ_{>0}} 𝒥_{Δ,(c/p)V_p}`: there are ideals
`J_p = 𝒥_{Δ,(c/p)V_p}`, and the sections of `J` over `U` are the `g ∈ K(X)` lying, near every
point of `U`, in some `J_p` (and only `0` over `U = ∅`), the union of the subsheaves `J_p`. -/
@[mmp "def_fourfold_asymptotic_adjoint_ideal"]
def IsAsymptoticAdjointIdeal (Δ D : Divisor X) (V : ℕ → AddSubgroup X.functionField) (b : ℕ)
    (c : ℚ) (J : X.Opens → Set X.functionField) : Prop :=
  IsProjectiveMorphism f ∧ IsAffine Z ∧ IsNormalVariety k sX ∧ IsSmoothScheme sX ∧
    IsReducedSNC sX Δ ∧ D.IsCartier ∧ IsGradedLinearSeries f D V ∧ 0 < b ∧ V b ≠ ⊥ ∧
    ContainsNoStratum Δ (baseLocusIn (V b) ((b : ℤ) • D)) ∧ 0 < c ∧
    ∃ Jp : ℕ → X.Opens → Set X.functionField,
      (∀ p : ℕ, 0 < p → b ∣ p → IsSeriesAdjointIdeal sX Δ ((p : ℤ) • D) (V p) (c / p) (Jp p)) ∧
      ∀ (U : X.Opens) (g : X.functionField), g ∈ J U ↔ (U = ⊥ → g = 0) ∧
        ∀ x ∈ U, ∃ W : X.Opens, x ∈ W ∧ W ≤ U ∧ ∃ p : ℕ, 0 < p ∧ b ∣ p ∧ g ∈ Jp p W

/-- The *complete graded linear series* of `D`: `V_m = H⁰(X, 𝒪_X(mD))`. -/
def completeSeries (D : Divisor X) (m : ℕ) : AddSubgroup X.functionField :=
  sectionsSubgroup ((m : ℤ) • D)

/-- **The asymptotic adjoint ideal of a divisor**, `𝒥_{Δ,‖cD‖}`: the asymptotic reduced-boundary
adjoint ideal `MMP.Fourfold.IsAsymptoticAdjointIdeal` of the complete graded linear series
`V_m = H⁰(X, 𝒪_X(mD))`. -/
@[mmp "def_fourfold_asymptotic_adjoint_ideal"]
def IsAsymptoticAdjointIdealOfDivisor (Δ D : Divisor X) (b : ℕ) (c : ℚ)
    (J : X.Opens → Set X.functionField) : Prop :=
  IsAsymptoticAdjointIdeal sX f Δ D (completeSeries D) b c J

end Asymptotic

/-! ### The image series on a prime divisor -/

section Image

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {Z : Scheme.{u}} (f : X ⟶ Z)

/-- `h ∈ K(S)` is the *restriction* to the prime divisor `S` (as the integral closed subscheme
`ι : S ⟶ X`) of `g ∈ K(X)`: `g` is the image of an element `a` of the local ring `𝒪_{X,η_S}`,
and `h` is the image of `a` under `ι^# : 𝒪_{X,η_S} ⟶ 𝒪_{S,η_S} = K(S)`. -/
def IsRestrictionAlong (S : MMP.Mori.PrimeDivisor X) (g : X.functionField)
    (h : haveI := S.integral; S.idealSheaf.subscheme.functionField) : Prop :=
  haveI := S.integral
  ∃ a : X.presheaf.stalk (S.idealSheaf.subschemeι (genericPoint S.idealSheaf.subscheme)),
    X.presheaf.stalkSpecializes (genericPoint_specializes _) a = g ∧
      S.idealSheaf.subschemeι.stalkMap (genericPoint S.idealSheaf.subscheme) a = h

/-- The *image series* of `D` on the prime divisor `S`: in degree `m`, the restrictions to `S` of
the sections of `𝒪_X(mD)`, that is, the image of `H⁰(X, 𝒪_X(mD)) → H⁰(S, 𝒪_S(mD|_S))`; it is
used for a divisor `D` of which `S` is not a component, so that every section of `𝒪_X(mD)` is
regular at the generic point of `S`. -/
def imageSeries (D : Divisor X) (S : MMP.Mori.PrimeDivisor X) (m : ℕ) :
    haveI := S.integral; AddSubgroup S.idealSheaf.subscheme.functionField :=
  haveI := S.integral
  AddSubgroup.closure
    {h | ∃ g ∈ sectionsIn ((m : ℤ) • D), IsRestrictionAlong S g h}

/-- **The asymptotic adjoint ideal of the image series on a divisor**, `𝒥_{Θ,‖cD‖_S}`, for a
prime divisor `S` of `X` (smooth, as the definition requires of the ambient variety), with
`Θ = (Δ - S)|_S`: the asymptotic reduced-boundary adjoint ideal on `S`, for `S ⟶ X ⟶ Z`, of
the image series of `D` on `S`. The sections of `𝒪_X(mD)` restrict to `S` after replacing `D`
by a linearly equivalent divisor `D + div(φ)` of which `S` is not a component; `D|_S` is then
`(D + div φ)|_S`. -/
@[mmp "def_fourfold_asymptotic_adjoint_ideal"]
def IsRestrictedAsymptoticAdjointIdeal (Δ D : Divisor X) (S : MMP.Mori.PrimeDivisor X) (b : ℕ)
    (c : ℚ) (J : haveI := S.integral;
      S.idealSheaf.subscheme.Opens → Set S.idealSheaf.subscheme.functionField) : Prop :=
  haveI := S.integral
  ∃ (_ : CompactSpace X) (_ : IsLocallyNoetherian S.idealSheaf.subscheme)
    (_ : IsNormal S.idealSheaf.subscheme) (φ : (RationalFunctions X)ˣ),
    (D + principalDivisor φ).coeff S = 0 ∧
      IsAsymptoticAdjointIdeal (S.idealSheaf.subschemeι ≫ sX) (S.idealSheaf.subschemeι ≫ f)
        ((Δ - Finsupp.single S 1).restrictPrimeDivisor S)
        ((D + principalDivisor φ).restrictPrimeDivisor S)
        (imageSeries (D + principalDivisor φ) S) b c J

end Image

end MMP.Fourfold
