/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Basic
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.Pullback

/-!
# Birational transforms, pull-backs and discrepancies in *Flips and abundance*

The definitions of FA 2.4, 2.5 (with the pull-back of `ℝ`-Cartier divisors it uses), 2.7 and 2.9:
push-forward and birational transform of `ℝ`-divisors under maps that are morphisms in
codimension one, the pull-back of `ℝ`-Cartier divisors, discrepancies of divisors over a normal
variety with respect to an `ℝ`-divisor, `φ⁻¹`-exceptional divisors and log resolutions.

FA's push-forward `f_*(D)` of a prime divisor is the closure of `f(D ∩ U)` when this is a prime
divisor, and `0` otherwise, for a map `f` whose domain of definition `U` has complement of
codimension `≥ 2`. It is Kollár–Mori's birational transform of divisors,
`MMP.Mori.RationalMap.transformDivisor`, which is defined for every rational map; FA's condition
is `MMP.Flips.RationalMap.IsMorphismInCodimOne`.

## Main definitions

* `MMP.Flips.RationalMap.IsMorphismInCodimOne`: the complement of the domain of definition has
  codimension `≥ 2`.
* `MMP.Flips.birationalInverseTransform`: `g⁻¹_*(D)` for a birational morphism `g`.
* `MMP.Flips.IsRCartierPullback`: `G` is a pull-back `∑ r_j f^*L_j` of `D = ∑ r_j L_j`.
* `MMP.Flips.IsDiscrepancyWith`: `a = a_ω(E, D_X)`, computed with a form `ω` and a presentation
  of `div_X(ω) + D_X` as an `ℝ`-combination of Cartier divisors.
* `MMP.Flips.IsDiscrepancy`: `a = a(F, D_X)` for a divisor `F` of `k(X)` with nonempty center.
* `MMP.Flips.RationalMap.IsInverseExceptional`: `φ⁻¹`-exceptional prime divisors.
* `MMP.Flips.IsLogResolution`: log resolutions of a log variety.

## Implementation notes

FA chooses a rational top form `ω` with `div_X(ω) = K_X` and a presentation
`div_X(ω) + D_X = ∑ r_j L_j`, and defines the discrepancy with these choices; "`a` is the
discrepancy computed with these choices" is the predicate `MMP.Flips.IsDiscrepancyWith`. The
general discrepancy `MMP.Flips.IsDiscrepancy` existentially quantifies over the choices (FA 2.5.2
shows that the value does not depend on them).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.4.1, 2.5.1,
  2.5.2, 2.5.4, 2.7, 2.9
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

/-! ### Push-forward and birational transforms -/

namespace RationalMap

variable {X Y : Scheme.{u}}

/-- A map `f : X ⤏ Y` is a *morphism in codimension one* if its domain of definition `U`
satisfies `codim_X (X ∖ U) ≥ 2`. -/
@[mmp "def_fa2_divisor_pushforward"]
def IsMorphismInCodimOne (f : X.RationalMap Y) : Prop :=
  2 ≤ closedsCodimension (Mori.RationalMap.dom f).compl

end RationalMap

attribute [mmp "def_fa2_divisor_pushforward", mmp "def_fa2_birational_transform"]
  MMP.Mori.RationalMap.transformDivisor

/-- For a birational morphism `g : Y ⟶ X` of normal varieties whose inverse `g⁻¹` is a morphism in
codimension one, `g⁻¹_*(D) = (g⁻¹)_*(D)`, the birational transform of `D` under the inverse map
`g⁻¹ : X ⤏ Y`. -/
@[mmp "def_fa2_birational_transform"]
def birationalInverseTransform {X Y : Scheme.{u}} {R : Type*} [AddCommMonoid R] (g : Y ⟶ X)
    (hg : IsBirationalMorphism g) : DivisorWithCoeffs R X →+ DivisorWithCoeffs R Y :=
  Mori.RationalMap.transformDivisor (RationalMap.IsBirational.inverse hg)

/-! ### Pull-backs of `ℝ`-Cartier divisors -/

section Pullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- Let `f : Y ⟶ X` be a dominant morphism of normal varieties and `D` an `ℝ`-Cartier divisor on
`X`. An `ℝ`-divisor `G` on `Y` is a *pull-back of `D`* if there are Cartier divisors
`L₁, …, L_m` on `X` and `r_j ∈ ℝ` with `D = ∑ r_j L_j` and `G = ∑ r_j f^*L_j`, where `f^*L_j` is
the (Weil divisor of the) pull-back of `L_j` (`MMP.Mori.Divisor.IsPullback`, defined since the
generic points of `Y` map outside `Supp L_j`). -/
@[mmp "def_fa2_r_cartier_pullback"]
def IsRCartierPullback (f : Y ⟶ X) (D : RDivisor X) (G : RDivisor Y) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (L' : Fin m → Divisor Y),
    (∀ j, (L j).IsCartier) ∧ D = ∑ j, r j • Divisor.toRDivisor (L j) ∧
    (∀ j, ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (L j).supp,
      (L j).IsPullback f hB (L' j)) ∧
    G = ∑ j, r j • Divisor.toRDivisor (L' j)

end Pullback

/-! ### Discrepancies -/

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **The discrepancy, computed with choices.** Let `X` be a normal variety of dimension `n`,
`D_X` an `ℝ`-divisor on `X`, `ω ≠ 0` a rational `n`-form on `X`, and `(Y, f, E)` a divisor over
`X`. Given a presentation `div_X(ω) + D_X = ∑_{j=1}^m r_j L_j` with `L_j` Cartier and `r_j ∈ ℝ`,
the real number `a` is the *discrepancy* `a_ω(E, D_X)` computed with these choices if it is the
coefficient of `E` in the `ℝ`-divisor `div_Y(f^*ω) - ∑ r_j f^*L_j` on `Y`: for the pull-backs
`f^*L_j` (`MMP.Mori.Divisor.IsPullback`), `a = ord_E(f^*ω) - ∑ r_j coeff_E(f^*L_j)`. -/
@[mmp "def_fa2_discrepancy"]
def IsDiscrepancyWith (n : ℕ) (D_X : RDivisor X) (ω : RationalPluriForms sX n 1)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (E : ProperDivisorOver k sX) (a : ℝ) :
    Prop :=
  IsNormalVariety k sX ∧ topologicalKrullDim X = n ∧ ω ≠ 0 ∧ (∀ j, (L j).IsCartier) ∧
    Divisor.toRDivisor (divisorOfForm ω) + D_X = ∑ j, r j • Divisor.toRDivisor (L j) ∧
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    ∃ L' : Fin m → Divisor E.Y,
      (∀ j, ∃ hB : ∀ Z : irreducibleComponents E.Y,
          E.f (componentGenericPoint E.Y Z) ∉ (L j).supp,
        (L j).IsPullback E.f hB (L' j)) ∧
      a = (E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * (L' j).coeff E.E

/-- **The discrepancy of a divisor of `k(X)`.** Let `X` be a normal variety of dimension `n`,
`D_X` an `ℝ`-divisor on `X` and `K_X` a canonical divisor with `K_X + D_X` `ℝ`-Cartier, and let
`F` be a divisor of `k(X)` with nonempty center on `X`. The real number `a` is the *discrepancy*
`a(F, D_X)` if `a = a_ω(E, D_X)` for a divisor `(Y, f, E)` over `X` with `ord_E = F`, a rational
`n`-form `ω` with `div_X(ω) = K_X` and a presentation of `div_X(ω) + D_X` as an `ℝ`-combination of
Cartier divisors. -/
@[mmp "def_fa2_discrepancy_general"]
def IsDiscrepancy (n : ℕ) (K : Divisor X) (D_X : RDivisor X) (F : Valuation X.functionField ℤᵐ⁰)
    (a : ℝ) : Prop :=
  K.IsCanonicalDivisor sX n ∧ IsCartierCombination (Divisor.toRDivisor K + D_X) ∧
    HasNonemptyCenter k sX F ∧
    ∃ (E : ProperDivisorOver k sX) (ω : RationalPluriForms sX n 1) (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X),
      E.valuation = F ∧ divisorOfForm ω = K ∧ IsDiscrepancyWith sX n D_X ω r L E a

end Discrepancy

/-! ### `φ⁻¹`-exceptional divisors -/

namespace RationalMap

variable {X Y : Scheme.{u}}

/-- Let `φ : X ⤏ Y` be a modification of normal varieties which is a morphism in codimension one.
A prime divisor `F` of `Y` is *`φ⁻¹`-exceptional* if `F ≠ φ_*(P)` for every prime divisor `P` of
`X`. -/
@[mmp "def_fa2_inverse_exceptional_divisor"]
def IsInverseExceptional (φ : X.RationalMap Y) (F : Mori.PrimeDivisor Y) : Prop :=
  ∀ P : Mori.PrimeDivisor X, Mori.RationalMap.transformPrimeDivisor φ P ≠ some F

end RationalMap

/-! ### Log resolutions -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A prime divisor `E` of `Y` is *exceptional over `X`* for a proper birational morphism
`f : Y ⟶ X` from a normal variety: the divisor `(Y, f, E)` over `X` is exceptional,
`dim f(E) ≤ dim X - 2`. -/
def IsExceptionalPrimeDivisor {Y : Scheme.{u}} (f : Y ⟶ X) (E : Mori.PrimeDivisor Y) : Prop :=
  ∃ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (hp : IsProper f),
    (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ hp).IsExceptional

/-- A *log resolution* of a log variety `(X, D)` is a proper birational morphism `f : Y ⟶ X` from a
smooth variety `Y` such that, with `E₁, …, E_k` the prime divisors of `Y` exceptional over `X`,
the reduced divisor with support `Supp(f⁻¹_*(D) + ∑ E_i)` is an snc divisor. -/
@[mmp "def_fa2_log_resolution"]
def IsLogResolution (D : RDivisor X) {Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsLogVariety k sX D ∧ Mori.IsVariety k (f ≫ sX) ∧ IsSmoothScheme (f ≫ sX) ∧ IsProper f ∧
    ∃ hf : IsBirationalMorphism f, ∃ G : Divisor Y,
      (∀ P, G.coeff P = 0 ∨ G.coeff P = 1) ∧
      (∀ P, G.coeff P = 1 ↔
        (birationalInverseTransform f hf D).coeff P ≠ 0 ∨ IsExceptionalPrimeDivisor sX f P) ∧
      IsSNCDivisor (f ≫ sX) G

/-! ### `𝓕`-birational transforms -/

section FBirationalTransform

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- Let `φ : X ⤏ Y` be a birational map of normal varieties and `F` a prime divisor of `Y`, so
that `ord_F` is a divisor of `k(Y) = k(X)`. A divisor `(W, h, E)` over `X` *realizes* `F` through
`φ` if there is a birational morphism `p : W ⟶ Y` agreeing with `φ ∘ h` (on `h⁻¹` of the domain of
a representative `φ_U : U ⟶ Y` of `φ`, `p = φ_U ∘ h`), such that `ord_E = ord_F` through
`p^* : k(Y) ≅ k(W)`. Then `ord_E = ord_F` as divisors of `k(X)`, so `F` has nonempty center on `X`
exactly when it is realized by some divisor over `X`. -/
def IsRealizedOver (φ : X.RationalMap Y) (F : Mori.PrimeDivisor Y)
    (E : ProperDivisorOver k sX) : Prop :=
  ∃ (g : X.PartialMap Y) (p : E.Y ⟶ Y) (hp : IsBirationalMorphism p),
    g.toRationalMap = φ ∧ (E.f ⁻¹ᵁ g.domain).ι ≫ p = (E.f ∣_ g.domain) ≫ g.hom ∧
    haveI := E.isIntegral
    haveI := E.isNormal
    haveI := E.isLocallyNoetherian
    haveI := hp.isDominant
    E.E.divisorialValuation.comap (functionFieldMap p) = F.divisorialValuation

/-- **The `𝓕`-birational transform.** Let `φ : X ⤏ Y` be a modification of normal varieties which
is a morphism in codimension one, `K_X` a canonical divisor of dimension `n` and `D_X` an
`ℝ`-divisor on `X` with `K_X + D_X` `ℝ`-Cartier, and suppose that the `φ⁻¹`-exceptional prime
divisors are finitely many, `F₁, …, F_k`, each with nonempty center on `X` (realized by a divisor
over `X`, `MMP.Flips.IsRealizedOver`). Let `𝓕 = (c₁, …, c_k)` be real numbers with
`1 ≥ c_i ≥ min {1, -a(F_i, D_X)}`. The `ℝ`-divisor `G` is the *`𝓕`-birational transform*
`D_{𝓕,Y} = φ_*(D_X) + ∑ c_i F_i` of `D_X`. Here `c` assigns `c_i` to `F_i`. -/
@[mmp "def_fa2_f_birational_transform"]
def IsFBirationalTransform (sY : Y ⟶ Spec (.of k)) (n : ℕ) (K : Divisor X) (D_X : RDivisor X)
    (φ : X.RationalMap Y) (c : Mori.PrimeDivisor Y → ℝ) (G : RDivisor Y) : Prop :=
  IsNormalVariety k sX ∧ IsNormalVariety k sY ∧ Mori.RationalMap.IsBirational φ ∧
    RationalMap.IsMorphismInCodimOne φ ∧ K.IsCanonicalDivisor sX n ∧
    IsCartierCombination (Divisor.toRDivisor K + D_X) ∧
    ∃ Fs : Finset (Mori.PrimeDivisor Y),
      (∀ F, F ∈ Fs ↔ RationalMap.IsInverseExceptional φ F) ∧
      (∀ F ∈ Fs, ∃ E : ProperDivisorOver k sX, IsRealizedOver sX φ F E) ∧
      (∀ F ∈ Fs, c F ≤ 1 ∧ ∀ (E : ProperDivisorOver k sX) (a : ℝ), IsRealizedOver sX φ F E →
        IsDiscrepancy sX n K D_X E.valuation a → min 1 (-a) ≤ c F) ∧
      G = Mori.RationalMap.transformDivisor φ D_X + ∑ F ∈ Fs, Finsupp.single F (c F)

end FBirationalTransform

end MMP.Flips
