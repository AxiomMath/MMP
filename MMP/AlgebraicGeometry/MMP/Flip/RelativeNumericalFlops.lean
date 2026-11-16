/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Basic
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-!
# Miscellaneous definitions of *Flips and abundance*

Relative numerical classes of `ℝ`-Cartier divisors (used in FA 6.1–6.5) and `H`-flops (FA 6.8);
the numerical dimension of a nef divisor (FA 11.1.2); the Weil pull-back of a Weil divisorial
subsheaf along a finite morphism (FA 16.3.5) and the cyclic quotient models (FA 16.6.1.2,
16.6.3); relative bigness via the generic fibre (FA 17.4.2); `f`-negative divisors (FA 18.5.2,
18.5.3, 18.6.2), `ℚ`-factorial lt pairs, procedure data and the class `𝒮₁(H')` of the first
MMP of the flipping procedure (FA 18.12.1, 18.12.3).

## Main definitions

* `MMP.Flips.relativeNumericalDivisorClass`: the class `[L] ∈ N¹(X/S)`; the numerically
  `π`-trivial divisors and `N¹(X/S)` are `MMP.Flips.relativeNumericallyTrivialDivisors`
  and `MMP.Flips.RelativeNumericalDivisorClasses`, registered here.
* `MMP.Flips.IsHFlop`: `H`-flops with respect to `K + B`.
* `MMP.Flips.numericalDimension`: `ν(X, D)`.
* `MMP.Flips.weilPullback`: `p^w(𝓛) = sat(𝓛𝒪_{X'})`.
* `MMP.Flips.cyclicQuotientModel`, `MMP.Flips.cyclicQuotientCurveTwo`,
  `MMP.Flips.cyclicQuotientCurveOne`: `T_{m,q} = Spec K[[x, y]]^{μ_m}`, `C^{(2)}_{m,q}`,
  `C^{(1)}_{m,q}`.
* `MMP.Flips.IsRelativelyBigOnGenericFiber`: `h`-big `ℚ`-Cartier `ℚ`-divisors (FA 17.4.2).
* `MMP.Flips.IsRelativelyNegative`: `f`-negative `ℝ`-Cartier divisors.
* `MMP.Flips.IsQFactorialLogTerminalPair`, `MMP.Flips.ProcedureDatum`,
  `MMP.Flips.IsInFirstProcedureClass`.

## Implementation notes

* `ℚ`-factoriality (`def_mmp_q_factorial`) is inlined as in `MMP.Flips.SequenceOfLogFlips`:
  every Weil divisor has a positive multiple which is Cartier.
* The singular locus `Sing Z` of FA 18.12.1.2 (over `ℂ`) is the non-regular locus: the points
  whose local ring is not regular; `Sing(Supp f_*D)` is that of the reduced closed subscheme
  `Supp f_*D`, whose local ring at `z` is `𝒪_{Z,z}` modulo the stalk of its ideal sheaf.
* The span condition of FA 18.12.1 on `F_1, …, F_r` (their classes span `N¹(Z'/Z)`) is stated
  as: every `ℝ`-Cartier divisor on `Z'` is numerically `π`-equivalent to a real combination of the
  `F_j` (`MMP.Flips.IsNumericallyEquivalentOver`). The strict transform of a prime divisor `Q` of
  `Z` is its birational transform under the inverse `π⁻¹ : Z ⤏ Z'`.
* The set `T` of FA 18.12.1.1 is the image `f(Ex(f))` of the exceptional set of the flipping
  contraction `f : X ⟶ Z`.
* Relative bigness (FA 17.4.2) is measured on the generic fibre `X_η = X ×_Z Spec κ(η)`
  (`AlgebraicGeometry.Scheme.Hom.fiber`), with `𝒪_{X_η}(k m₀ M)` the pull-back of the invertible
  sheaf `𝒪_X(k m₀ M)` along `X_η ⟶ X`. Kollár–Mori's `MMP.Mori.QDivisor.IsRelativelyBig`
  (`def_km3b_relatively_big`) instead uses the rank of `h_* 𝒪_X(kD)` at `η` and a strict bound,
  so it is not registered for FA 17.4.2.
* In `ν(X, D)` a closed subvariety `V` of dimension `k` is the reduced closed subscheme on the
  closure of its generic point (`MMP.Mori.curveSubschemeAt`), and `(D^k · V) ≠ 0` is tested on a
  Cartier multiple `mD` (`(D^k · V) = m^{-k} ((mD)^k · V)`).
* The action of `μ_m ⊆ Kˣ` on `K[[x, y]]` is `f(x, y) ↦ f(ζx, ζ^q y)`
  (`MvPowerSeries.rescale`), and `K[[x, y]]^{μ_m}` is `FixedPoints.subring`. The reduced image
  of a curve `(g = 0)` is the reduced induced closed subscheme on the closure of the image of
  `V(g)` under `Spec K[[x, y]] ⟶ T_{m,q}`.
* The ring map `p^{-1}K(X) → K(X')` of FA 16.3.5 is given on sections: a section `s` of `K(X)`
  over `V` goes, over `U' ⊆ p⁻¹(V)`, to the family of images of its components under the stalk
  maps `𝒪_{X, p(η')} → 𝒪_{X', η'}` at the generic points `η'` of `X'` in `U'`
  (`MMP.Flips.rationalFunctionsPullbackHom`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.1–6.5, 6.8,
  11.1.2, 16.3.5, 16.6.1.2, 16.6.3, 17.4.2, 18.5.2, 18.5.3, 18.6.2, 18.12.1, 18.12.3
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

/-! ### Relative numerical classes -/

attribute [mmp "def_fa6_relative_numerical_classes"] relativeNumericallyTrivialDivisors
  mem_relativeNumericallyTrivialDivisors RelativeNumericalDivisorClasses
  IsNumericallyTrivialOver

section RelativeNumericalClasses

variable {k : Type u} [Field k] {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (π : X ⟶ S)

/-- For a proper morphism `π : X ⟶ S` from a normal variety and an `ℝ`-Cartier divisor `L` on `X`
(an `ℝ`-linear combination of Cartier divisors), the class `[L] ∈ N¹(X/S)` of `L` modulo the
numerically `π`-trivial `ℝ`-Cartier divisors (`L ≡_π 0`: `L · C = 0` for every proper irreducible
curve `C ⊆ X` with `π(C)` a point). -/
@[mmp "def_fa6_relative_numerical_classes"]
def relativeNumericalDivisorClass (L : KCartierDivisor ℝ X) :
    RelativeNumericalDivisorClasses sX π :=
  Submodule.Quotient.mk L

/-- `[L] = 0` in `N¹(X/S)` exactly when `L ≡_π 0`. -/
@[mmp "def_fa6_relative_numerical_classes"]
theorem relativeNumericalDivisorClass_eq_zero_iff (L : KCartierDivisor ℝ X) :
    relativeNumericalDivisorClass sX π L = 0 ↔
      ∀ C : ProperCurve sX, C.IsContractedBy π → (C.cycle ℝ).intersectionNumber L = 0 := by
  rw [relativeNumericalDivisorClass, Submodule.Quotient.mk_eq_zero,
    mem_relativeNumericallyTrivialDivisors]

end RelativeNumericalClasses

/-! ### `H`-flops -/

section HFlop

variable (k : Type u) [Field k] {X Z X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sZ : Z ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX]
  [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']

/-- Let `(X, B)` be an lc pair (with canonical divisor `K` of dimension `n`) and `H` a
`ℚ`-Cartier divisor on `X`. Let `f : X ⟶ Z` be a small contraction such that `K_X + B` is
numerically `f`-trivial and `-H` is `f`-ample. A flip `f⁺ : X⁺ ⟶ Z` (with birational map
`g : X ⤏ X⁺`) of `f` with respect to `H` is an *`H`-flop with respect to `K + B`*, or simply an
*`H`-flop*. -/
@[mmp "def_fa6_h_flop_of_pair"]
def IsHFlop (n : ℕ) (K : Divisor X) (B : RDivisor X) (H : QDivisor X) (f : X ⟶ Z)
    (fp : X' ⟶ Z) (g : X.RationalMap X') : Prop :=
  IsLogCanonical sX n K B ∧ H.IsQCartier ∧ IsSmall k sZ sX f ∧
    IsNumericallyTrivialOver k sX f (logCanonicalDivisor K B) ∧
    IsRelativelyAntiAmple f (QDivisor.toRDivisor H) ∧
    IsFlip k sX sZ sX' (QDivisor.toRDivisor H) f fp g

end HFlop

/-! ### Numerical dimension -/

section NumericalDimension

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The integers `k ∈ {0, 1, …, dim X}` admissible in `ν(X, D)`: `k = 0` (by the convention
`(D⁰ · V) = 1` for a point `V`), or `(D^k · V) ≠ 0` for some closed subvariety `V ⊆ X` of
dimension `k`, computed as `((mD)^k · V) ≠ 0` for a Cartier multiple `mD`, `m > 0`. The
subvariety `V` is the reduced closed subscheme on the closure of a point `x` of `X`. -/
@[mmp "def_fa11_numerical_dimension"]
def numericalDimensionSet (D : QDivisor X) : Set ℕ :=
  {d | d = 0 ∨ (d : WithBot ℕ∞) ≤ topologicalKrullDim X ∧
    ∃ (x : X) (hV : topologicalKrullDim (curveSubschemeAt x) = d) (m : ℕ)
      (E : Divisor X) (hE : E.IsCartier), 0 < m ∧ Divisor.toQDivisor E = (m : ℚ) • D ∧
      Divisor.intersectionNumberOn k sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι d
        hV.le (fun _ => E) (fun _ => hE) ≠ 0}

/-- `k = 0` is always admissible in `ν(X, D)`. -/
@[mmp "def_fa11_numerical_dimension"]
theorem zero_mem_numericalDimensionSet (D : QDivisor X) :
    0 ∈ numericalDimensionSet k sX D :=
  Or.inl rfl

/-- Let `X` be a proper variety and `D` a nef `ℚ`-Cartier divisor on `X`. The *numerical
dimension* of `D` is
`ν(X, D) = max {k ∈ {0, 1, …, dim X} | (D^k · V) ≠ 0 for some closed subvariety V ⊆ X with
dim V = k}`, with the convention `(D⁰ · V) = 1` for a point `V` (so `k = 0` is always admissible).
Also written `ν(D)`. -/
@[mmp "def_fa11_numerical_dimension"]
def numericalDimension (_hX : Mori.IsProperVariety k sX) (D : QDivisor X)
    (_hD : D.IsNef k sX) : ℕ :=
  sSup (numericalDimensionSet k sX D)

end NumericalDimension

/-! ### Weil pull-back along a finite morphism -/

section WeilPullback

variable {X X' : Scheme.{u}} (p : X' ⟶ X)

/-- A morphism `p : X' ⟶ X` maps every generic point of `X'` (of an irreducible component) to a
generic point of `X`. -/
@[mmp "def_fa16a_weil_pullback_finite"]
def MapsGenericPointsToGenericPoints : Prop :=
  ∀ Z' : irreducibleComponents X', ∃ Z : irreducibleComponents X,
    p.base (componentGenericPoint X' Z') = componentGenericPoint X Z

variable {p} (hp : MapsGenericPointsToGenericPoints p)

/-- The ring map `p^{-1}K(X) → K(X')` on sections: for `U' ⊆ p⁻¹(V)`, a section `s` of `K(X)` over
`V` goes to the section of `K(X')` over `U'` whose component at a generic point `η' ∈ U'` of `X'`
is the image of the component of `s` at the generic point `p(η')` of `X` under the stalk map
`𝒪_{X, p(η')} → 𝒪_{X', η'}` (the field extension `k(p(η')) ⊆ k(η')` when `X`, `X'` are
reduced). -/
@[mmp "def_fa16a_weil_pullback_finite"]
def rationalFunctionsPullbackHom {V : X.Opens} {U' : X'.Opens} (hUV : U' ≤ p ⁻¹ᵁ V) :
    (∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V},
        X.presheaf.stalk (componentGenericPoint X Z.1)) →+*
      ∀ Z' : {Z' : irreducibleComponents X' // componentGenericPoint X' Z' ∈ U'},
        X'.presheaf.stalk (componentGenericPoint X' Z'.1) :=
  RingHom.pi fun Z' => (p.stalkMap (componentGenericPoint X' Z'.1)).hom.comp
    ((X.presheaf.stalkSpecializes (specializes_of_eq (hp Z'.1).choose_spec)).hom.comp
      (Pi.evalRingHom (fun Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V} =>
          X.presheaf.stalk (componentGenericPoint X Z.1))
        ⟨(hp Z'.1).choose, (hp Z'.1).choose_spec ▸ hUV Z'.2⟩))

/-- Restricting the image of a section to a smaller open is taking the image there. -/
@[simp]
theorem map_rationalFunctionsPullbackHom {V : X.Opens} {U' W' : X'.Opens} (i : W' ⟶ U')
    (hUV : U' ≤ p ⁻¹ᵁ V) (s : ToType ((rationalFunctionsPresheaf X).obj (op V))) :
    (rationalFunctionsPresheaf X').map i.op (rationalFunctionsPullbackHom hp hUV s) =
      rationalFunctionsPullbackHom hp (i.le.trans hUV) s :=
  rfl

/-- The `Γ(X', U')`-submodule of `K(X')(U')` generated by the images of the sections of `𝓛` over
the opens `V` with `U' ⊆ p⁻¹(V)`, that is, by the image of the sections of `p^{-1}𝓛` over `U'`. -/
@[mmp "def_fa16a_weil_pullback_finite"]
def weilPullbackGenerators (L : RationalFunctionsSubmodule X) (U' : X'.Opens) :
    Submodule Γ(X', U') ((rationalFunctionsPresheaf X').obj (op U')) :=
  Submodule.span Γ(X', U')
    {t | ∃ (V : X.Opens) (hUV : U' ≤ p ⁻¹ᵁ V)
      (s : ToType ((rationalFunctionsPresheaf X).obj (op V))),
      s ∈ L.sections V ∧ rationalFunctionsPullbackHom hp hUV s = t}

/-- Restricting a section of `weilPullbackGenerators hp L U'` to a smaller open `W'` gives a
section of `weilPullbackGenerators hp L W'`. -/
theorem map_mem_weilPullbackGenerators (L : RationalFunctionsSubmodule X) {U' W' : X'.Opens}
    (i : W' ⟶ U') {t : ToType ((rationalFunctionsPresheaf X').obj (op U'))}
    (ht : t ∈ weilPullbackGenerators hp L U') :
    (rationalFunctionsPresheaf X').map i.op t ∈ weilPullbackGenerators hp L W' := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨V, hUV, s, hs, rfl⟩ := ht
    exact Submodule.subset_span ⟨V, i.le.trans hUV, s, hs, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha => rw [rationalFunctionsPresheaf_map_smul]; exact Submodule.smul_mem _ _ ha

/-- The `𝒪_{X'}`-submodule `𝓛𝒪_{X'} ⊆ K(X')` generated by the image of `p^{-1}𝓛`: the subsheaf
of `K(X')` generated by `MMP.Flips.weilPullbackGenerators`. -/
@[mmp "def_fa16a_weil_pullback_finite"]
def weilPullbackImage (L : RationalFunctionsSubmodule X) : RationalFunctionsSubmodule X' :=
  RationalFunctionsSubmodule.localClosure (weilPullbackGenerators hp L)
    fun i _ hs => map_mem_weilPullbackGenerators hp L i hs

end WeilPullback

section WeilPullbackSetting

variable (k : Type u) [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sX' : X' ⟶ Spec (.of k)) (p : X' ⟶ X)

/-- The setting of FA 16.3.5: `p : X' ⟶ X` is a finite morphism of reduced pure-dimensional
schemes of finite type over `k` that maps every generic point of `X'` to a generic point of
`X`. -/
@[mmp "def_fa16a_weil_pullback_finite"]
structure IsWeilPullbackSetting : Prop where
  /-- `X` is reduced. -/
  isReduced : IsReduced X
  /-- `X'` is reduced. -/
  isReduced_source : IsReduced X'
  /-- `X` is locally of finite type over `k`. -/
  locallyOfFiniteType : LocallyOfFiniteType sX
  /-- `X` is quasi-compact over `k`. -/
  quasiCompact : QuasiCompact sX
  /-- `X'` is locally of finite type over `k`. -/
  locallyOfFiniteType_source : LocallyOfFiniteType sX'
  /-- `X'` is quasi-compact over `k`. -/
  quasiCompact_source : QuasiCompact sX'
  /-- `X` is pure-dimensional. -/
  pureDim : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = topologicalKrullDim X
  /-- `X'` is pure-dimensional. -/
  pureDim_source : ∀ Z ∈ irreducibleComponents X',
    topologicalKrullDim Z = topologicalKrullDim X'
  /-- `p` is a morphism of `k`-schemes. -/
  comp_eq : p ≫ sX = sX'
  /-- `p` is finite. -/
  isFinite : IsFinite p
  /-- `p` maps every generic point of `X'` to a generic point of `X`. -/
  mapsGenericPoints : MapsGenericPointsToGenericPoints p

variable {k sX sX' p}

/-- In the setting of FA 16.3.5 (`MMP.Flips.IsWeilPullbackSetting`), for a Weil divisorial
subsheaf `𝓛 ∈ WSh(X)`, `p^w(𝓛) = sat(𝓛𝒪_{X'}) ⊆ K(X')`, the saturation of the
`𝒪_{X'}`-submodule of `K(X')` generated by the image of `p^{-1}𝓛`. -/
@[mmp "def_fa16a_weil_pullback_finite"]
def weilPullback (h : IsWeilPullbackSetting k sX sX' p) (L : WeilDivisorialSubsheaf X) :
    RationalFunctionsSubmodule X' :=
  (weilPullbackImage h.mapsGenericPoints L.toRationalFunctionsSubmodule).saturation

variable (k sX) in
/-- **A finite dominant morphism maps generic points to generic points** (the aside of FA 16.3.5):
for `p : X' ⟶ X` finite and dominant, `X`, `X'` pure-dimensional and `X` of finite type over `k`,
`closure {p(η')}` has dimension `dim X' = dim X` for every generic point `η'` of `X'`, so it is an
irreducible component of `X`. -/
@[mmp "def_fa16a_weil_pullback_finite"]
theorem mapsGenericPointsToGenericPoints_of_isFinite_of_isDominant [LocallyOfFiniteType sX]
    [IsFinite p] [IsDominant p]
    (hX : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = topologicalKrullDim X)
    (hX' : ∀ Z ∈ irreducibleComponents X', topologicalKrullDim Z = topologicalKrullDim X') :
    MapsGenericPointsToGenericPoints p :=
  exists_map_componentGenericPoint_eq_of_isFinite_of_isDominant k sX p hX hX'

/-- The setting of FA 16.3.5 for a finite *dominant* morphism: the condition on generic points
holds automatically (`MMP.Flips.mapsGenericPointsToGenericPoints_of_isFinite_of_isDominant`). -/
@[mmp "def_fa16a_weil_pullback_finite"]
theorem IsWeilPullbackSetting.of_isDominant [IsFinite p] [IsDominant p] (hred : IsReduced X)
    (hred' : IsReduced X') (hft : LocallyOfFiniteType sX) (hqc : QuasiCompact sX)
    (hft' : LocallyOfFiniteType sX') (hqc' : QuasiCompact sX')
    (hX : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = topologicalKrullDim X)
    (hX' : ∀ Z ∈ irreducibleComponents X', topologicalKrullDim Z = topologicalKrullDim X')
    (hc : p ≫ sX = sX') :
    IsWeilPullbackSetting k sX sX' p :=
  ⟨hred, hred', hft, hqc, hft', hqc', hX, hX', hc, ‹_›,
    mapsGenericPointsToGenericPoints_of_isFinite_of_isDominant k sX hX hX'⟩

end WeilPullbackSetting

/-! ### Cyclic quotient models -/

section CyclicQuotient

variable (K : Type u) [Field K] (m : ℕ) (q : ℤ)

/-- The setting of FA 16.6.1.2: `K` is an algebraically closed field of characteristic `0`,
`m ≥ 1` and `gcd(q, m) = 1`. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
structure IsCyclicQuotientSetting : Prop where
  /-- `K` is algebraically closed. -/
  isAlgClosed : IsAlgClosed K
  /-- `K` has characteristic `0`. -/
  charZero : CharZero K
  /-- `m ≥ 1`. -/
  one_le : 1 ≤ m
  /-- `gcd(q, m) = 1`. -/
  gcd_eq_one : Int.gcd q m = 1

/-- The weights `ζ ↦ (ζ, ζ^q)` of the action of `μ_m` on the coordinates `x, y`. -/
def cyclicWeights : rootsOfUnity m K →* (Fin 2 → K) where
  toFun ζ := ![((ζ : Kˣ) : K), (((ζ : Kˣ) ^ q : Kˣ) : K)]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' ζ ξ := by
    funext i
    fin_cases i <;> simp [mul_zpow]

/-- The action of `μ_m` on `K[[x, y]]` by `ζ · (x, y) = (ζx, ζ^q y)`: `ζ` sends a power series
`f(x, y)` to `f(ζx, ζ^q y)`. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
abbrev cyclicAction : MulSemiringAction (rootsOfUnity m K) (MvPowerSeries (Fin 2) K) where
  smul ζ f := MvPowerSeries.rescale (cyclicWeights K m q ζ) f
  one_smul f := by
    change MvPowerSeries.rescale (cyclicWeights K m q 1) f = f
    rw [map_one, MvPowerSeries.rescale_one, RingHom.id_apply]
  mul_smul ζ ξ f := by
    change MvPowerSeries.rescale (cyclicWeights K m q (ζ * ξ)) f =
      MvPowerSeries.rescale (cyclicWeights K m q ζ)
        (MvPowerSeries.rescale (cyclicWeights K m q ξ) f)
    rw [MvPowerSeries.rescale_rescale, map_mul, mul_comm]
  smul_zero ζ := map_zero _
  smul_add ζ := map_add _
  smul_one ζ := map_one _
  smul_mul ζ := map_mul _

/-- The ring of invariants `K[[x, y]]^{μ_m}`, the fixed subring of the action of `μ_m`. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
def cyclicInvariants : Subring (MvPowerSeries (Fin 2) K) :=
  letI := cyclicAction K m q
  FixedPoints.subring (MvPowerSeries (Fin 2) K) (rootsOfUnity m K)

/-- A power series lies in `cyclicInvariants K m q` if and only if it is fixed by the rescaling
`cyclicWeights K m q ζ` for every `ζ ∈ μ_m`. -/
@[simp]
theorem mem_cyclicInvariants_iff (f : MvPowerSeries (Fin 2) K) :
    f ∈ cyclicInvariants K m q ↔
      ∀ ζ : rootsOfUnity m K, MvPowerSeries.rescale (cyclicWeights K m q ζ) f = f :=
  Iff.rfl

/-- In the setting of FA 16.6.1.2, the *cyclic quotient model* `T_{m,q} = Spec K[[x, y]]^{μ_m}`. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
abbrev cyclicQuotientModel (_h : IsCyclicQuotientSetting K m q) : Scheme.{u} :=
  Spec (CommRingCat.of (cyclicInvariants K m q))

variable {K m q} (h : IsCyclicQuotientSetting K m q)

/-- The quotient morphism `Spec K[[x, y]] ⟶ T_{m,q}`, induced by `K[[x, y]]^{μ_m} ⊆ K[[x, y]]`. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
def cyclicQuotientMap :
    Spec (CommRingCat.of (MvPowerSeries (Fin 2) K)) ⟶ cyclicQuotientModel K m q h :=
  Spec.map (CommRingCat.ofHom (cyclicInvariants K m q).subtype)

/-- The closure of the image in `T_{m,q}` of the curve `(g = 0) ⊆ Spec K[[x, y]]`, the
underlying closed set of its reduced image. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
def cyclicQuotientImage (g : MvPowerSeries (Fin 2) K) : Closeds (cyclicQuotientModel K m q h) :=
  ⟨closure ((cyclicQuotientMap h).base ''
    (PrimeSpectrum.zeroLocus {g} : Set (PrimeSpectrum (MvPowerSeries (Fin 2) K)))),
    isClosed_closure⟩

/-- `C^{(2)}_{m,q} ⊆ T_{m,q}`: the reduced image of `(xy = 0)`. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
abbrev cyclicQuotientCurveTwo : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    (cyclicQuotientImage h (MvPowerSeries.X 0 * MvPowerSeries.X 1))).subscheme

/-- `C^{(1)}_{m,q} ⊆ T_{m,q}`: the reduced image of `(x = 0)`. -/
@[mmp "def_fa16a_cyclic_quotient_model"]
abbrev cyclicQuotientCurveOne : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h (MvPowerSeries.X 0))).subscheme

end CyclicQuotient

/-! ### Relative bigness via the generic fibre -/

section RelativelyBig

variable {X Z : Scheme.{u}} (h : X ⟶ Z)

/-- For a morphism `h : X ⟶ Z` from an irreducible scheme, with `η = h(ξ_X)` the generic point of
`h(X)` and `X_η` the generic fibre, `dim_{κ(η)} H⁰(X_η, F|_{X_η})` for a sheaf of modules `F` on
`X`, `F|_{X_η}` being its pull-back along `X_η ⟶ X`. -/
@[mmp "def_fa17_relatively_big"]
def genericFiberH0 [IrreducibleSpace X] (F : X.Modules) : ℕ :=
  letI : Module (Z.residueField (h.base (genericPoint X)))
      Γ((Scheme.Modules.pullback (h.fiberι (h.base (genericPoint X)))).obj F, ⊤) :=
    Module.compHom _ (scalarsToGlobalSections (Z.residueField (h.base (genericPoint X)))
      (h.fiberToSpecResidueField (h.base (genericPoint X))))
  Module.finrank (Z.residueField (h.base (genericPoint X)))
    Γ((Scheme.Modules.pullback (h.fiberι (h.base (genericPoint X)))).obj F, ⊤)

variable (k : Type u) [Field k] (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
  [IrreducibleSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- Let `h : X ⟶ Z` be a proper morphism of varieties, `X` normal, `η` the generic point of
`h(X)`, `X_η` the generic fibre, `d = dim X - dim h(X)`, and `M` a `ℚ`-Cartier `ℚ`-divisor on
`X`. `M` is *`h`-big* if there are an integer `m₀ > 0` and a real `c > 0` such that `m₀M` is
Cartier and `dim_{κ(η)} H⁰(X_η, 𝒪_{X_η}(j m₀ M)) ≥ c j^d` for all integers `j ≫ 0`. -/
@[mmp "def_fa17_relatively_big"]
def IsRelativelyBigOnGenericFiber (M : QDivisor X) : Prop :=
  Mori.IsVariety k sX ∧ Mori.IsVariety k sZ ∧ h ≫ sZ = sX ∧ IsProper h ∧
    ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range h.base)) = b ∧
      ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (m₀ : ℚ) • M ∧ D.IsCartier ∧
        ∃ c : ℝ, 0 < c ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
          c * (j : ℝ) ^ (a - b) ≤ (genericFiberH0 h ((j : ℤ) • D).divisorialSheaf : ℝ)

variable {k sX sZ}

omit [IsLocallyNoetherian X] in
/-- **The generic fibre is a normal variety of dimension `dim X - dim h(X)`** (the aside of
FA 17.4.2): for a morphism `h : X ⟶ Z` of varieties over `k` with `X` normal, `η = h(ξ_X)` the
generic point of `h(X)`, the generic fibre `X_η` is a normal variety over `κ(η)`, and if
`dim X = a` and `dim (closure h(X)) = b` then `dim X_η = a - b`. -/
@[mmp "def_fa17_relatively_big"]
theorem isNormalVariety_genericFiber_and_topologicalKrullDim (hX : Mori.IsVariety k sX)
    (hZ : Mori.IsVariety k sZ) (hc : h ≫ sZ = sX) {a b : ℕ} (ha : topologicalKrullDim X = a)
    (hb : topologicalKrullDim (closure (Set.range h.base)) = b) :
    Mori.IsNormalVariety (Z.residueField (h.base (genericPoint X)))
        (h.fiberToSpecResidueField (h.base (genericPoint X))) ∧
      topologicalKrullDim (h.fiber (h.base (genericPoint X))) = ((a - b : ℕ) : WithBot ℕ∞) := by
  have := hX.toLocallyOfFiniteType
  have := hZ.toLocallyOfFiniteType
  exact ⟨isNormalVariety_fiber_genericPoint h k sX sZ hX hZ hc,
    topologicalKrullDim_fiber_genericPoint_eq_sub h k sX sZ hc ha hb⟩

end RelativelyBig

/-! ### Relatively negative divisors -/

section Negative

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Let `f : X ⟶ Z` be a proper morphism and `D` an `ℝ`-Cartier divisor on `X`. `D` is
*`f`-negative* if `D · Γ < 0` for every irreducible curve `Γ ⊆ X` with `f(Γ)` a point: the
intersection number `D · Γ` is defined (computed with some presentation `D = ∑ r_j L_j`), and
every value of it, for every presentation, is negative. -/
@[mmp "def_fa18_f_negative_divisor"]
def IsRelativelyNegative (f : X ⟶ Z) (D : RDivisor X) : Prop :=
  IsProper f ∧ IsCartierCombination D ∧
    ∀ C : ProperCurve sX, C.IsContractedBy f →
      (∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX D r L C x) ∧
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX D r L C x → x < 0

end Negative

/-! ### `ℚ`-factorial lt pairs -/

section QFactorialPair

variable (k : Type u) [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
  (sZ : Z ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  [LocallyOfFiniteType sY]

/-- A *`ℚ`-factorial lt pair* `(Y, Θ)` (with canonical divisor `K` of dimension `n`): a normal
`ℚ`-factorial variety `Y` (every Weil divisor has a positive multiple which is Cartier,
`def_mmp_q_factorial`) with a boundary `Θ` such that `K_Y + Θ` is log terminal. -/
@[mmp "def_fa18_qfactorial_lt_pair"]
structure IsQFactorialLogTerminalPair (n : ℕ) (K : Divisor Y) (Θ : RDivisor Y) : Prop where
  /-- `Y` is a normal variety. -/
  isNormalVariety : IsNormalVariety k sY
  /-- `Y` is `ℚ`-factorial. -/
  isQFactorial : ∀ D : Divisor Y, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier
  /-- `Θ` is a boundary. -/
  isBoundary : IsBoundary Θ
  /-- `K_Y + Θ` is log terminal. -/
  isLogTerminal : IsLogTerminal sY n K Θ

/-- The class `𝒮₁(H')` of FA 18.12.3, for a reduced divisor `H'` on `Z` (the divisor of a
procedure datum, `MMP.Flips.ProcedureDatum.IsInFirstClass`): `(Y', Θ', h')` belongs to it if
`(Y', Θ')` is an `n`-dimensional `ℚ`-factorial lt pair (with canonical divisor `K`),
`h' : Y' ⟶ Z` is projective, birational and an isomorphism over `Z ∖ Supp H'`, and every prime
divisor of `Y'` contained in `h'⁻¹(Supp H')` has coefficient `1` in `Θ'`. -/
@[mmp "def_fa18_procedure_first_class"]
structure IsInFirstProcedureClass (n : ℕ) (H' : Divisor Z) (K : Divisor Y) (Θ : RDivisor Y)
    (h : Y ⟶ Z) : Prop where
  /-- `(Y', Θ')` is a `ℚ`-factorial lt pair. -/
  isQFactorialLogTerminalPair : IsQFactorialLogTerminalPair k sY n K Θ
  /-- `dim Y' = n`. -/
  dim_eq : topologicalKrullDim Y = n
  /-- `h'` is a morphism of `k`-schemes. -/
  comp_eq : h ≫ sZ = sY
  /-- `h'` is projective. -/
  isProjectiveMorphism : IsProjectiveMorphism h
  /-- `h'` is birational. -/
  isBirationalMorphism : IsBirationalMorphism h
  /-- `h'` is an isomorphism over `Z ∖ Supp H'`. -/
  isIso_restrict : IsIso (h ∣_ H'.supp.compl)
  /-- Every prime divisor of `Y'` contained in `h'⁻¹(Supp H')` has coefficient `1` in `Θ'`. -/
  coeff_eq_one : ∀ P : Mori.PrimeDivisor Y,
    (P.support : Set Y) ⊆ h.base ⁻¹' (H'.supp : Set Z) → Θ.coeff P = 1

end QFactorialPair

/-! ### Procedure data -/

section ProcedureDatum

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
  [IsLocallyNoetherian Z] [IsNormal Z]

/-- The push-forward `f_*D` of an `ℝ`-divisor along a morphism `f : X ⟶ Z`: its birational
transform under `f` (`def_fa2_divisor_pushforward`). -/
abbrev divisorPushforward (f : X ⟶ Z) (D : RDivisor X) : RDivisor Z :=
  Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D

/-- A *procedure datum* for `(X, D, f)`, `f : X ⟶ Z` the flipping contraction and
`T = f(Ex(f))`, is a triple `(π, (F_j)_{j=1}^r, H')` where `π : Z' ⟶ Z` is a projective resolution
of singularities; `F_1, …, F_r` are effective Cartier divisors on `Z'` whose classes span
`N¹(Z'/Z)` and none of whose irreducible components is the strict transform of a component of
`f_*D`; and `H'` is a reduced effective Cartier divisor on `Z` such that
(18.12.1.1) `T ⊆ Supp H'`;
(18.12.1.2) `Sing Z ∪ Sing(Supp f_*D) ⊆ Supp H'`;
(18.12.1.3) `π(F) ⊆ Supp H'` for every irreducible component `F` of every `F_j`;
(18.12.1.5) `f(⌊D⌋) ⊆ Supp H'`; and
(18.12.1.6) no component of `H'` is the image of a component of `D` with coefficient `< 1`. -/
@[mmp "def_fa18_flipping_procedure_divisor"]
structure ProcedureDatum (D : RDivisor X) (f : X ⟶ Z) where
  /-- The resolution `Z'`. -/
  resolution : Scheme.{u}
  /-- The resolution morphism `π : Z' ⟶ Z`. -/
  π : resolution ⟶ Z
  /-- `Z'` is locally Noetherian. -/
  isLocallyNoetherian_resolution : IsLocallyNoetherian resolution
  /-- `Z'` is normal. -/
  isNormal_resolution : IsNormal resolution
  /-- The composite `Z' ⟶ Z ⟶ Spec k` is quasi-compact. -/
  quasiCompact_resolution : QuasiCompact (π ≫ sZ)
  /-- `Z'` is a variety. -/
  isVariety_resolution : Mori.IsVariety k (π ≫ sZ)
  /-- `Z'` is smooth. -/
  isSmoothScheme_resolution : IsSmoothScheme (π ≫ sZ)
  /-- `π` is projective. -/
  isProjectiveMorphism : IsProjectiveMorphism π
  /-- `π` is birational. -/
  isBirationalMorphism : IsBirationalMorphism π
  /-- The number `r` of the divisors `F_j`. -/
  r : ℕ
  /-- The divisors `F_1, …, F_r` on `Z'`. -/
  F : Fin r → Divisor resolution
  /-- Each `F_j` is Cartier. -/
  isCartier_F : ∀ j,
    haveI := isLocallyNoetherian_resolution
    haveI := isNormal_resolution
    (F j).IsCartier
  /-- Each `F_j` is effective. -/
  isEffective_F : ∀ j, (F j).IsEffective
  /-- The classes of the `F_j` span `N¹(Z'/Z)`: every `ℝ`-Cartier divisor on `Z'` is numerically
  `π`-equivalent to a real combination of the `F_j`. -/
  span_F : ∀ L : RDivisor resolution,
    haveI := isLocallyNoetherian_resolution
    haveI := isNormal_resolution
    haveI := quasiCompact_resolution
    IsCartierCombination L → ∃ c : Fin r → ℝ,
      IsNumericallyEquivalentOver k (π ≫ sZ) π L (∑ j, c j • Divisor.toRDivisor (F j))
  /-- No irreducible component of an `F_j` is the strict transform of a component of `f_*D`. -/
  not_strictTransform : ∀ j (P : Mori.PrimeDivisor resolution), (F j).coeff P ≠ 0 →
    ∀ Q : Mori.PrimeDivisor Z, (divisorPushforward f D).coeff Q ≠ 0 →
      (Mori.RationalMap.IsBirational.inverse isBirationalMorphism).transformPrimeDivisor Q ≠
        some P
  /-- The divisor `H'` on `Z`. -/
  H' : Divisor Z
  /-- `H'` is Cartier. -/
  isCartier_H' : H'.IsCartier
  /-- `H'` is reduced and effective. -/
  isReduced_H' : ∀ P, H'.coeff P = 0 ∨ H'.coeff P = 1
  /-- (18.12.1.1) `T = f(Ex(f)) ⊆ Supp H'`. -/
  image_exceptionalSet_subset : f.base '' exceptionalSet f ⊆ H'.supp
  /-- (18.12.1.2) `Sing Z ⊆ Supp H'`. -/
  nonregular_subset : ∀ z : Z, ¬ IsRegularLocalRing (Z.presheaf.stalk z) → z ∈ H'.supp
  /-- (18.12.1.2) `Sing(Supp f_*D) ⊆ Supp H'`. -/
  nonregular_supp_subset : ∀ z ∈ (divisorPushforward f D).supp,
    ¬ IsRegularLocalRing
      (Z.presheaf.stalk z ⧸ IdealSheafData.stalk (divisorPushforward f D).suppIdeal z) →
    z ∈ H'.supp
  /-- (18.12.1.3) `π(F) ⊆ Supp H'` for every irreducible component `F` of every `F_j`. -/
  image_component_subset : ∀ j (P : Mori.PrimeDivisor resolution), (F j).coeff P ≠ 0 →
    π.base '' P.support ⊆ H'.supp
  /-- (18.12.1.5) `f(⌊D⌋) ⊆ Supp H'`. -/
  image_roundDown_subset : f.base '' (reducedPart D).supp ⊆ H'.supp
  /-- (18.12.1.6) No component of `H'` is the image of a component of `D` with coefficient
  `< 1`. -/
  image_ne_component : ∀ P : Mori.PrimeDivisor Z, H'.coeff P ≠ 0 →
    ∀ Q : Mori.PrimeDivisor X, D.coeff Q ≠ 0 → D.coeff Q < 1 → f.base '' Q.support ≠ P.support

variable {k sZ}

/-- (18.12.1.1) The exceptional set of `f` lies over `Supp H'`: `Ex(f) ⊆ f⁻¹(Supp H')`. -/
@[mmp "def_fa18_flipping_procedure_divisor"]
theorem ProcedureDatum.exceptionalSet_subset {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) : exceptionalSet f ⊆ f.base ⁻¹' (P.H'.supp : Set Z) :=
  fun x hx => P.image_exceptionalSet_subset ⟨x, hx, rfl⟩

/-- (18.12.1.1) For the pull-back `H = f^*H'` of the divisor `H'` of a procedure datum,
`Ex(f) ⊆ Supp H`. -/
@[mmp "def_fa18_flipping_procedure_divisor"]
theorem ProcedureDatum.exceptionalSet_subset_supp_of_isPullback [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} {f : X ⟶ Z} (P : ProcedureDatum k sZ D f)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ P.H'.supp}
    {H : Divisor X} (hH : P.H'.IsPullback f hB H) : exceptionalSet f ⊆ (H.supp : Set X) := by
  have hHe : DivisorWithCoeffs.IsEffective P.H' := fun E => by
    rcases P.isReduced_H' E with h | h <;> simp [h]
  rw [supp_eq_preimage_supp_of_isPullback P.isCartier_H' hHe hH]
  exact P.exceptionalSet_subset

variable {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]

/-- For a procedure datum with divisor `H'`, `(Y', Θ', h')` belongs to the class `𝒮₁(H')` of the
first MMP (FA 18.12.3, `MMP.Flips.IsInFirstProcedureClass`). -/
@[mmp "def_fa18_procedure_first_class"]
abbrev ProcedureDatum.IsInFirstClass {D : RDivisor X} {f : X ⟶ Z} (P : ProcedureDatum k sZ D f)
    (n : ℕ) (K : Divisor Y) (Θ : RDivisor Y) (h : Y ⟶ Z) : Prop :=
  IsInFirstProcedureClass k sY sZ n P.H' K Θ h

end ProcedureDatum

end MMP.Flips
