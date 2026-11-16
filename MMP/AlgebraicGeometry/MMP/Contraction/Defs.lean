/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs

/-!
# Contractions, small morphisms and round-downs in *Flips and abundance*

The definitions of FA 2.1.3–2.1.6, 2.2.5–2.2.6 and 2.5.3: contractions, birational contractions,
small birational contractions, modifications of a morphism, the exceptional set of a morphism,
the round down of an `ℝ`-divisor and its reduced part, `ℚ`-Cartier divisors (FA 1.6.1), log
discrepancies, and the multiplicity of an `ℝ`-Cartier divisor along a divisor over `X`.

The round down `⌊r⌋` of a real number (FA 2.2.5) is Mathlib's `Int.floor`, and the round down
`⌊D⌋ = ∑ ⌊dᵢ⌋ Dᵢ` of an `ℝ`-divisor is `MMP.Mori.DivisorWithCoeffs.roundDown`. A `ℚ`-divisor is
`ℚ`-Cartier (FA 1.6.1) when `MMP.Mori.QDivisor.IsQCartier`: some nonzero multiple `mD` is an
integral Cartier divisor (a positive one, `MMP.Mori.QDivisor.IsQCartier.exists_pos`).

## Main definitions

* `MMP.Flips.exceptionalSet`: `Ex(f)`, the points with no neighbourhood on which `f` is an open
  immersion.
* `MMP.Flips.IsContraction`, `MMP.Flips.IsBirationalContraction`, `MMP.Flips.IsSmall`.
* `MMP.Flips.IsModificationOf`: a modification of `f` into `g`.
* `MMP.Flips.reducedPart`: the reduced part `⌊D⌋` of a boundary.
* `MMP.Flips.IsLogDiscrepancy`: `a_ℓ(F, D_X) = 1 + a(F, D_X)`.
* `MMP.Flips.IsMultiplicityAlong`: `mult_F(G) = ∑ r_j coeff_E(f^*L_j)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (1.6.1),
  2.1.3–2.1.6, 2.2.5, 2.2.6, 2.5.3, 2.5.4
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

attribute [mmp "def_fa1a_q_cartier"] MMP.Mori.QDivisor.IsQCartier
attribute [mmp "def_fa2_round_down_divisor"] MMP.Mori.DivisorWithCoeffs.roundDown

/-- The *reduced part* `⌊D⌋` of a boundary `D` (`MMP.Flips.IsBoundary`): its round down. -/
@[mmp "def_fa2_round_down_divisor"]
abbrev reducedPart {X : Scheme.{u}} (D : RDivisor X) : Divisor X :=
  DivisorWithCoeffs.roundDown D

/-! ### The exceptional set -/

section Morphisms

variable {X Y : Scheme.{u}}

/-- The *exceptional set* `Ex(f) ⊆ Y` of a morphism `f : Y ⟶ X` of varieties: the set of points
`y ∈ Y` having no open neighbourhood `V ∋ y` such that `f|_V : V ⟶ X` is an open immersion. -/
@[mmp "def_fa2_exceptional_set"]
def exceptionalSet (f : Y ⟶ X) : Set Y :=
  {y | ¬ ∃ V : Y.Opens, y ∈ V ∧ IsOpenImmersion (V.ι ≫ f)}

/-! ### Contractions -/

variable (k : Type u) [Field k] (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))

/-- A proper morphism `f : Y ⟶ X` of varieties is a *contraction* if the natural map
`𝒪_X ⟶ f_* 𝒪_Y` is an isomorphism: `𝒪_X(U) ⟶ 𝒪_Y(f⁻¹ U)` is bijective for every open `U`. -/
@[mmp "def_fa2_contraction"]
structure IsContraction (f : Y ⟶ X) : Prop where
  /-- `X` is a variety. -/
  isVariety_target : Mori.IsVariety k sX
  /-- `Y` is a variety. -/
  isVariety_source : Mori.IsVariety k sY
  /-- `f` is a morphism of `k`-schemes. -/
  comp_eq : f ≫ sX = sY
  /-- `f` is proper. -/
  isProper : IsProper f
  /-- `𝒪_X ⟶ f_* 𝒪_Y` is an isomorphism. -/
  isIso_app : ∀ U : X.Opens, IsIso (f.app U)

/-- A contraction `f : Y ⟶ X` with `dim Y = dim X` is a *birational contraction* (a *blow down*;
viewed from `X`, an *extraction* or *blow up*). -/
@[mmp "def_fa2_birational_contraction"]
structure IsBirationalContraction (f : Y ⟶ X) : Prop extends IsContraction k sX sY f where
  /-- `dim Y = dim X`. -/
  dim_eq : topologicalKrullDim Y = topologicalKrullDim X

/-- A birational contraction `f : Y ⟶ X` is *small* if it is an isomorphism in codimension one:
there are closed subsets `V ⊆ Y` and `W ⊆ X` of codimension `≥ 2` such that `f` restricts to an
isomorphism `Y ∖ V ⟶ X ∖ W`. -/
@[mmp "def_fa2_small"]
structure IsSmall (f : Y ⟶ X) : Prop extends IsBirationalContraction k sX sY f where
  /-- `f` is an isomorphism outside closed subsets of codimension `≥ 2`. -/
  exists_isIso : ∃ (V : Closeds Y) (W : Closeds X), 2 ≤ closedsCodimension V ∧
    2 ≤ closedsCodimension W ∧ ∃ h : V.compl ≤ f ⁻¹ᵁ W.compl, IsIso (f.resLE W.compl V.compl h)

end Morphisms

/-- For proper morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` of varieties, a *modification of `f` into
`g`* is a modification `φ : X ⤏ Y` (a birational map) with `g ∘ φ = f` as maps. -/
@[mmp "def_fa2_modification_of_morphism"]
def IsModificationOf {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (φ : X.RationalMap Y) :
    Prop :=
  Mori.RationalMap.IsBirational φ ∧ RationalMap.IsOver f g φ

/-! ### Log discrepancies and multiplicities -/

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- In the situation of `MMP.Flips.IsDiscrepancy`, the real number `b` is the *log discrepancy*
`a_ℓ(F, D_X) = 1 + a(F, D_X)` of `F`. -/
@[mmp "def_fa2_log_discrepancy"]
def IsLogDiscrepancy (n : ℕ) (K : Divisor X) (D_X : RDivisor X)
    (F : Valuation X.functionField ℤᵐ⁰) (b : ℝ) : Prop :=
  ∃ a : ℝ, IsDiscrepancy sX n K D_X F a ∧ b = 1 + a

/-- Let `G` be an `ℝ`-Cartier divisor on a normal variety `X` with a chosen presentation
`G = ∑ r_j L_j` (`L_j` Cartier), and `F` a divisor of `k(X)` with nonempty center on `X`, realized
by a chosen divisor `(Y, f, E)` over `X` (`F = ord_E`). The real number `μ` is the *multiplicity*
`mult_F(G) = ∑ r_j · coeff_E(f^*L_j)` of `G` along `F`. -/
@[mmp "def_fa2_multiplicity_along_divisor"]
def IsMultiplicityAlong (G : RDivisor X) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (F : Valuation X.functionField ℤᵐ⁰) (E : ProperDivisorOver k sX) (μ : ℝ) : Prop :=
  IsNormalVariety k sX ∧ HasNonemptyCenter k sX F ∧ E.valuation = F ∧
    (∀ j, (L j).IsCartier) ∧ G = ∑ j, r j • Divisor.toRDivisor (L j) ∧
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    ∃ L' : Fin m → Divisor E.Y,
      (∀ j, ∃ hB : ∀ Z : irreducibleComponents E.Y,
          E.f (componentGenericPoint E.Y Z) ∉ (L j).supp,
        (L j).IsPullback E.f hB (L' j)) ∧
      μ = ∑ j, r j * (L' j).coeff E.E

end Discrepancy

end MMP.Flips
