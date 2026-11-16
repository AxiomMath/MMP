/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.WeilDivisor
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints

/-!
# Non-normal schemes in *Flips and abundance*: double normal crossings, pinch points, and the
# normalization of a pair

The definitions of FA 12.2.1(1), (2), (6), FA p. 140, FA Notation 12.2.2 and FA Remark 2.6.1,
2.6.2 about non-normal schemes: double normal crossing points and pinch points, semismooth
`n`-folds, `n`-folds with at worst double normal crossings in codimension one, boundaries on
reduced `S₂` schemes, the double intersection locus `D`, the boundary `Θ` of the normalization,
the condition (2.6.1) and morphisms birational in the sense of (2.6.2).

## Conventions

FA works over `ℂ`; the definitions here are stated over a field `k` (the structure morphism
`sX : X ⟶ Spec k`), and specialize to FA's for `k = ℂ`. As in the conventions of FA Chapter 12,
a *scheme* is a separated scheme of finite type over `k` (`IsFiniteTypeSeparated`), and an
*`n`-fold* is such a scheme which is reduced and of pure dimension `n` (`IsNFold`).

The codimension of a point `η` is its coheight `Order.coheight η` in the specialization order
(as in `MMP.Foundations.Flips.WeilSubsheaf`); the codimension of a closed subset is
`MMP.Mori.closedsCodimension`. A *regular point* is a point whose local ring is a regular local
ring (`IsRegularLocalRing`); a *smooth point* is a point of the smooth locus
`MMP.Mori.smoothLocus sX`.

## Local analytic descriptions

FA describes the singularities analytically ("analytically isomorphic to `xy = 0`"). This is
read as an isomorphism of completed local rings,
the algebraic form of the analytic statement: the completion of `𝒪_{X,x}` is
`CompletedLocalRing x`, Mathlib's `AdicCompletion` of `𝒪_{X,x}` at its maximal ideal, and the
model rings are quotients `k[[x₀, …, xₙ]]/(h)` of Mathlib's `MvPowerSeries (Fin (n + 1)) k` by
the principal ideal `(h)`. At a closed point the isomorphism is one of `k`-algebras, `𝒪_{X,x}`
being a `k`-algebra through `sX` (`stalkStructureMap`); at a codimension-one point `P` (2.6.1)
the model is `κ(P)[[u, v]]/(uv)`, and since the completion is not canonically a
`κ(P)`-algebra the isomorphism is one of rings.

## Main definitions

* `MMP.Flips.IsDoubleNormalCrossingPoint`, `MMP.Flips.IsPinchPoint`: FA 12.2.1(1).
* `MMP.Flips.IsSemismooth`: FA 12.2.1(2).
* `MMP.Flips.IsNcInCodimOne`: at worst double normal crossings in codimension one (FA p. 140).
* `MMP.Flips.QWeilDivisor.IsBoundary`: boundaries on reduced `S₂` schemes (FA 12.2.1(6)).
* `MMP.Flips.doubleIntersectionLocus`, `MMP.Flips.doubleIntersectionLocusScheme`: the double
  intersection locus `D ⊆ X` (FA 12.2.2).
* `MMP.Flips.IsBoundaryOfNormalization`: `Θ = μ⁻¹_*Δ + D_μ` (FA 12.2.2).
* `MMP.Flips.SatisfiesFA261`: the condition (2.6.1) (FA 2.6.1).
* `MMP.Flips.IsBirationalFA262`: morphisms birational in the sense of (2.6.2) (FA 2.6.2).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.6.1, 2.6.2,
  12.2.1, 12.2.2
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

namespace MMP.Flips

open MMP.Mori

/-! ### Schemes, `n`-folds and completed local rings -/

section Local

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *scheme* in the sense of FA Chapter 12: `sX : X ⟶ Spec k` is separated and of finite type
(locally of finite type and quasi-compact). -/
def IsFiniteTypeSeparated : Prop :=
  IsSeparated sX ∧ LocallyOfFiniteType sX ∧ QuasiCompact sX

/-- An *`n`-fold* (FA Chapter 12 conventions): a reduced separated scheme of finite type over `k`
of pure dimension `n`, that is, every irreducible component of `X` has dimension `n`. -/
def IsNFold (n : ℕ) : Prop :=
  IsFiniteTypeSeparated sX ∧ IsReduced X ∧
    ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = n

/-- The structure map `k → 𝒪_{X,x}` making the local ring at `x` a `k`-algebra: the composite
`k ≅ Γ(Spec k, ⊤) → Γ(X, ⊤) → 𝒪_{X,x}` of `sX` on global sections and the germ at `x`. -/
def stalkStructureMap (x : X) : k →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x trivial).hom

variable (X) in
/-- The completed local ring `𝒪̂_{X,x}`: the adic completion of `𝒪_{X,x}` at its maximal
ideal. -/
abbrev CompletedLocalRing (x : X) : Type u :=
  AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- `𝒪̂_{X,x} ≅ k[[x_i : i ∈ σ]]/(h)` as `k`-algebras, the `k`-algebra structure on `𝒪_{X,x}`
(hence on its completion) being `stalkStructureMap sX x`. -/
def HasCompletedLocalModel (x : X) {σ : Type*} (h : MvPowerSeries σ k) : Prop :=
  letI := (stalkStructureMap sX x).toAlgebra
  Nonempty (CompletedLocalRing X x ≃ₐ[k] MvPowerSeries σ k ⧸ Ideal.span {h})

/-! ### Double normal crossing points and pinch points -/

/-- **Double normal crossing point** (FA 12.2.1(1)). Let `X` be an `n`-fold and `x ∈ X` a closed
point. `x` is a *double normal crossing point* of `X` if
`𝒪̂_{X,x} ≅ k[[x₀, …, xₙ]]/(x₀x₁)` as `k`-algebras.

The hypotheses that `X` is an `n`-fold and that `x` is closed are part of the predicate. -/
@[mmp "def_fa12a_double_normal_crossing_point"]
def IsDoubleNormalCrossingPoint (n : ℕ) (x : X) : Prop :=
  IsNFold sX n ∧ IsClosed ({x} : Set X) ∧
    HasCompletedLocalModel sX x
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (n + 1)) k)

/-- **Pinch point** (FA 12.2.1(1)). Let `X` be an `n`-fold, `n ≥ 2`, and `x ∈ X` a closed point.
`x` is a *pinch point* of `X` if `𝒪̂_{X,x} ≅ k[[x₀, …, xₙ]]/(x₀² - x₁x₂²)` as `k`-algebras.

The hypotheses `n ≥ 2`, that `X` is an `n`-fold and that `x` is closed are part of the
predicate. -/
@[mmp "def_fa12a_pinch_point"]
def IsPinchPoint (n : ℕ) (x : X) : Prop :=
  2 ≤ n ∧ IsNFold sX n ∧ IsClosed ({x} : Set X) ∧
    HasCompletedLocalModel sX x
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (n + 1)) k)

/-- **Semismooth** (FA 12.2.1(2)). An `n`-fold `X` is *semismooth* if every closed point of `X`
is a smooth point, a double normal crossing point or a pinch point of `X`. -/
@[mmp "def_fa12a_semismooth"]
def IsSemismooth (n : ℕ) : Prop :=
  IsNFold sX n ∧ ∀ x : X, IsClosed ({x} : Set X) →
    x ∈ smoothLocus sX ∨ IsDoubleNormalCrossingPoint sX n x ∨ IsPinchPoint sX n x

/-- **At worst double normal crossings in codimension one** (FA p. 140). An `n`-fold `X` is
*nc in codimension one* if there is a closed subset `Z ⊆ X` with `codim_X Z ≥ 2` such that every
closed point of `X ∖ Z` is a smooth point of `X` or a double normal crossing point of `X`. -/
@[mmp "def_fa12a_nc_in_codim_one"]
def IsNcInCodimOne (n : ℕ) : Prop :=
  IsNFold sX n ∧ ∃ Z : Closeds X, 2 ≤ closedsCodimension Z ∧
    ∀ x : X, IsClosed ({x} : Set X) → x ∉ Z →
      x ∈ smoothLocus sX ∨ IsDoubleNormalCrossingPoint sX n x

end Local

/-! ### Serre's condition `S₂` and boundaries -/

section Boundary

variable (X : Scheme.{u})

/-- `X` satisfies *Serre's condition `S₂`*: for every point `x`, the local ring `𝒪_{X,x}` has
depth `≥ min(2, dim 𝒪_{X,x})`, that is, its maximal ideal contains an `𝒪_{X,x}`-regular sequence
of length `≥ min(2, dim 𝒪_{X,x})`. -/
def SatisfiesS2 : Prop :=
  ∀ x : X, ∃ s : List (X.presheaf.stalk x),
    (∀ a ∈ s, a ∈ maximalIdeal (X.presheaf.stalk x)) ∧
      RingTheory.Sequence.IsRegular (X.presheaf.stalk x) s ∧
      min 2 (ringKrullDim (X.presheaf.stalk x)) ≤ (s.length : WithBot ℕ∞)

variable {X} {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))

/-- **Boundary** (FA 12.2.1(6)). Let `X` be a reduced (separated, finite type) scheme satisfying
`S₂`. A *boundary* on `X` is a `ℚ`-Weil divisor `Δ = ∑ dᵢ Δᵢ` on `X` (FA 16.2.1; the `Δᵢ` distinct
prime Weil divisors) with `0 ≤ dᵢ ≤ 1` for all `i`.

The hypotheses on `X` are part of the predicate. -/
@[mmp "def_fa12a_boundary"]
def QWeilDivisor.IsBoundary (Δ : QWeilDivisor X) : Prop :=
  IsFiniteTypeSeparated sX ∧ IsReduced X ∧ SatisfiesS2 X ∧
    ∀ Γ : WeilDivisorPrime X, 0 ≤ Δ Γ ∧ Δ Γ ≤ 1

end Boundary

/-! ### The double intersection locus and the boundary of the normalization -/

section Normalization

variable (X : Scheme.{u})

/-- The *double intersection locus* `D ⊆ X` (FA 12.2.2), as a closed subset: the closure of the
set of points `η` of codimension one of `X` at which `𝒪_{X,η}` is not regular. -/
@[mmp "def_fa12a_double_intersection_locus"]
def doubleIntersectionLocus : Closeds X :=
  ⟨closure {η : X | Order.coheight η = 1 ∧ ¬ IsRegularLocalRing (X.presheaf.stalk η)},
    isClosed_closure⟩

/-- The underlying set of the double intersection locus. -/
theorem coe_doubleIntersectionLocus :
    (doubleIntersectionLocus X : Set X) =
      closure {η : X | Order.coheight η = 1 ∧ ¬ IsRegularLocalRing (X.presheaf.stalk η)} :=
  rfl

/-- The ideal sheaf of the reduced structure on the double intersection locus `D`. -/
@[mmp "def_fa12a_double_intersection_locus"]
def doubleIntersectionLocusIdeal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (doubleIntersectionLocus X)

/-- The *double intersection locus* `D ⊆ X` (FA 12.2.2): the closure of the set of points of
codimension one of `X` at which `𝒪_{X,η}` is not regular, with its reduced structure. -/
@[mmp "def_fa12a_double_intersection_locus"]
abbrev doubleIntersectionLocusScheme : Scheme.{u} :=
  (doubleIntersectionLocusIdeal X).subscheme

/-- A point `ξ` of a topological space is the generic point of an *irreducible component* of a
subset `S` if `closure {ξ}` is a maximal irreducible subset of `S`. -/
def IsComponentGenericPoint {T : Type*} [TopologicalSpace T] (S : Set T) (ξ : T) : Prop :=
  Maximal (fun W : Set T => W ⊆ S ∧ IsIrreducible W) (closure {ξ})

variable {X}

/-- The preimage `μ⁻¹(S)` of a subset `S ⊆ X` under a morphism of schemes. -/
abbrev preimageSet {Y : Scheme.{u}} (μ : Y ⟶ X) (S : Set X) : Set Y := μ.base ⁻¹' S

/-- `ξ` is the generic point of an irreducible component of `μ⁻¹(D)` for the normalization
`μ : X^μ ⟶ X` (FA 12.2.2, the notation `D_μ = μ⁻¹(D)_red`): the support of the reduced divisor
`D_μ` is the closed set `μ⁻¹(D)`, and `D_μ` is the sum of its irreducible components, each with
coefficient one. This is an unregistered helper for the notation node
`not_fa12a_conductor_divisor`. -/
def IsConductorComponent {Y : Scheme.{u}} (μ : Y ⟶ X) (ξ : Y) : Prop :=
  IsComponentGenericPoint (preimageSet μ (doubleIntersectionLocus X)) ξ

variable {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))

open scoped Classical in
/-- **The boundary of the normalization** (FA 12.2.2). Let `X` be an `n`-fold which satisfies
`S₂` and is nc in codimension one, `μ : X^μ ⟶ X` its normalization and `Δ = ∑ dᵢ Δᵢ` a
`ℚ`-Weil divisor on `X`. Then `Θ := μ⁻¹_*Δ + D_μ`, a `ℚ`-divisor on `X^μ`, where
`μ⁻¹_*Δ = ∑ dᵢ (closure of μ⁻¹(Δᵢ ∖ D))` (the book prints `μ⁻¹Δ`) and `D_μ = μ⁻¹(D)_red`.
`Θ` is called the *boundary of the normalization*.

The normalization is `Stacks.AlgebraicGeometry.Normalization.normalization X hX`, the relative
normalization of `X` in `⨿_η Spec κ(η)` over the generic points `η` (Stacks 035M, 035N), which
needs that quasi-compact opens of `X` have finitely many irreducible components (`hX`, true for
the Noetherian `X` here). The reduced closed sets `closure(μ⁻¹(Δᵢ ∖ D))` and `μ⁻¹(D)` are read as
divisors with coefficient one on each irreducible component, so `Θ` is characterized by its
coefficients: the coefficient of a prime Weil divisor `Γ'` of `X^μ` is
`∑ {dᵢ | Γ' is a component of closure(μ⁻¹(Δᵢ ∖ D))} + (1 if Γ' is a component of μ⁻¹(D))`.
The `Δᵢ` are the prime Weil divisors in the support of `Δ`, and `Δᵢ` is the closure of its
generic point. The setting hypotheses are part of the predicate. -/
@[mmp "def_fa12a_slc_normalization_data"]
def IsBoundaryOfNormalization (n : ℕ)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (Δ : QWeilDivisor X)
    (Θ : QWeilDivisor (Stacks.AlgebraicGeometry.Normalization.normalizationScheme X hX)) :
    Prop :=
  IsNFold sX n ∧ SatisfiesS2 X ∧ IsNcInCodimOne sX n ∧
    ∀ Γ' : WeilDivisorPrime (Stacks.AlgebraicGeometry.Normalization.normalizationScheme X hX),
      Θ Γ' =
        (∑ Γ ∈ Δ.support,
          if IsComponentGenericPoint
              (closure (preimageSet (Stacks.AlgebraicGeometry.Normalization.normalization X hX)
                (closure {Γ.1.genericPoint} \ (doubleIntersectionLocus X : Set X))))
              Γ'.1.genericPoint
          then Δ Γ else 0) +
        if IsConductorComponent (Stacks.AlgebraicGeometry.Normalization.normalization X hX)
            Γ'.1.genericPoint
        then 1 else 0

end Normalization

/-! ### The conditions (2.6.1) and (2.6.2) -/

section Chapter2

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k))

/-- **The condition (2.6.1)** (FA Remark 2.6.1). A scheme `X` of finite type over `k`
*satisfies (2.6.1)* if `X` is reduced and equidimensional and every codimension-one point
`P ∈ X` is either a regular point of `X` or a point where `X` has two regular branches meeting
transversally, i.e. `𝒪̂_{X,P} ≅ κ(P)[[u, v]]/(uv)`.

Equidimensional: all irreducible components have the same dimension `d`. The isomorphism
`𝒪̂_{X,P} ≅ κ(P)[[u, v]]/(uv)` is one of rings, the completion not being canonically a
`κ(P)`-algebra. -/
@[mmp "def_fa2_seminormal_crossing_codim_one"]
def SatisfiesFA261 : Prop :=
  LocallyOfFiniteType sX ∧ QuasiCompact sX ∧ IsReduced X ∧
    (∃ d : ℕ, ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) ∧
    ∀ P : X, Order.coheight P = 1 →
      IsRegularLocalRing (X.presheaf.stalk P) ∨
        Nonempty (CompletedLocalRing X P ≃+*
          MvPowerSeries (Fin 2) (X.residueField P) ⧸
            Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
              MvPowerSeries (Fin 2) (X.residueField P))})

/-- A point `x` is a *generic point or a codimension-one singular point* of `X`: either the
closure of `x` is an irreducible component of `X`, or `x` has codimension one and `𝒪_{X,x}` is
not regular. -/
def IsGenericOrCodimOneSingular (x : X) : Prop :=
  closure {x} ∈ irreducibleComponents X ∨
    (Order.coheight x = 1 ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x))

/-- **Birational in the sense of (2.6.2)** (FA Remark 2.6.2). Let `X`, `Y` satisfy (2.6.1). A
morphism `f : Y ⟶ X` is *birational in the sense of (2.6.2)* if there are open subsets
`V ⊆ Y`, `U ⊆ X` containing all generic points of `Y`, resp. `X`, and all codimension-one
singular points of `Y`, resp. `X`, such that `f` restricts to an isomorphism `V → U` and
`f⁻¹(U) = V`.

Since `V = f⁻¹(U)`, this is stated with `V := f⁻¹ᵁ U`: the restriction `f ∣_ U : f⁻¹(U) ⟶ U` is
an isomorphism. The hypotheses that `X` and `Y` satisfy (2.6.1) are part of the predicate. -/
@[mmp "def_fa2_birational_nonnormal"]
def IsBirationalFA262 (f : Y ⟶ X) : Prop :=
  SatisfiesFA261 sX ∧ SatisfiesFA261 sY ∧
    ∃ U : X.Opens, (∀ x : X, IsGenericOrCodimOneSingular x → x ∈ U) ∧
      (∀ y : Y, IsGenericOrCodimOneSingular y → y ∈ f ⁻¹ᵁ U) ∧ IsIso (f ∣_ U)

end Chapter2

end MMP.Flips
