module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Singularities.Adjunction.DifferentDefs
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Iterated adjunction to a stratum and its difficulty

Let `(X, B)` be a rational pair and `X = S₀ ⊃ S₁ ⊃ ⋯ ⊃ S_k = S` a flag in which each `S_j` is a
normal prime component of the reduced boundary of `B_{j-1}` on `S_{j-1}`, where `B₀ = B` and
`B_j = Diff_{S_j}(B_{j-1} - S_j)` is the residue different of Kollár [SMMP, Def. 4.2]: the
`ℚ`-divisor on `S_j` with `K_{S_j} + B_j = (K_{S_{j-1}} + S_j + (B_{j-1} - S_j))|_{S_j}`, the
canonical divisors being those of a rational top form with a simple pole along `S_j` and of its
Poincaré residue. The sequence of pairs `(S_j, B_j)` is the *iterated adjunction data* of the
flag; it exists only when each `K_{S_{j-1}} + B_{j-1}` is `ℚ`-Cartier, so that its restriction is
defined. The pair `(S, B_k)` is the *adjunction pair* on the final stratum of the flag.

For an adjunction pair `(S, B_S)` and the hyperstandard set `D(I)` of a finite set `I`, the
*difficulty* of `(S, B_S)` is `∑_{α ∈ D(I)} #{E : a(E, S, B_S) < -α, c_S(E) ⊄ ⌊B_S⌋}`, the
count running over the divisorial valuations `E` of `k(S)`; it is an element of `ℕ∞`.

## Main definitions

* `MMP.Fourfold.QDivisor.toQWeilDivisor`: a `ℚ`-divisor as a `ℚ`-Weil divisor of FA 16.2.1.
* `MMP.Fourfold.IsPoincareResidue`: the Poincaré residue of an `m`-fold form along a divisor.
* `MMP.Fourfold.IsAdjunctionStep`: `(T, B_T)` is obtained from `(Y, B_Y)` by one adjunction step
  to a normal prime component `T` of the reduced boundary of `B_Y`.
* `MMP.Fourfold.StratumAdjunctionData`: the iterated adjunction data of a flag of strata.
* `MMP.Fourfold.IsStratumAdjunctionPair`: `(S, B_S)` is the adjunction pair on the final
  stratum of some flag.
* `MMP.Fourfold.adjunctionPairDifficulty`, `MMP.Fourfold.StratumAdjunctionData.difficulty`: the
  difficulty of an adjunction pair.

## Implementation notes

The boundary `B` need not be effective: a rational pair is `MMP.Mori.IsPair`, so that iterated
adjunction applies to subboundaries, whose coefficients are at most one but may be negative, such
as the crepant pull-backs `K_Y + C = h^*(K_X + B)`. Accordingly the reduced boundary of `B_Y` is
taken to consist of the prime divisors with coefficient at least one; for an effective divisor
these are the components of `⌊B_Y⌋`, and for a subboundary those with coefficient exactly one.
For an effective `B` the pair `(X, B)` is a pair in the sense of `MMP.Fourfold.IsPair`
(`MMP.Fourfold.StratumAdjunctionData.isPair`).

The different of one step to a prime divisor `P ⊂ Y`, with inclusion
`j : T ⟶ Y` is the residue different (Kollár [SMMP, Def. 4.2]): for a rational top form `τ` on
`Y` with a simple pole along `P` and its Poincaré residue `ρ = Res_T τ`, `K_Y = div τ` and
`K_T = div ρ` are canonical divisors with `(K_Y + P)|_T = K_T` in codimension one along `T`, and
`B_T` is defined by `(div τ + B_Y)|_T = div ρ + B_T`, the restriction being the pull-back of the
`ℚ`-Cartier divisor `div τ + B_Y` (`MMP.Mori.QDivisor.IsPullback`). The support condition of that
pull-back forces `coeff_P B_Y = 1`. The definition asks for one such `τ`; it does not depend on
the choice: another form is `f τ` with `f` a unit along `P`, its residue is `f|_T ρ`, and
`div(f τ) + B_Y = div f + (div τ + B_Y)` restricts to `div(f|_T) + (div ρ + B_T)`, the pull-back of
the principal divisor `div f` being `div(f|_T)`
(`MMP.Fourfold.IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue`). Since
pull-backs of `ℚ`-Cartier divisors are unique, `B_T` is determined by `(Y, B_Y)` and `j`.

Where the different `Diff_T(B_Y - T)` of FA 16.6 is defined, through the embedded dualizing sheaf
and the restriction of Weil divisorial subsheaves (`MMP.Flips.IsDifferentDivisor`), it is the
residue different (`MMP.Fourfold.isAdjunctionStep_of_isDifferentDivisor`). This is the case along
the strata of a dlt pair: there the codimension-two germs of `Y` along `T` are cyclic quotient
singularities, hence `ℚ`-factorial.

The flag is recorded together with the divisors `B_j`, since the condition on `S_j` (a component
of `⌊B_{j-1}⌋`) involves `B_{j-1}`: a term of `StratumAdjunctionData sX B ι B_S` is a flag
`X = S₀ ⊃ ⋯ ⊃ S_k = S`, with composite closed immersion `ι : S ⟶ X`, together with the divisors
`B_j` and the facts that each `B_j` is the residue different. The final stratum carries the
structure morphism `ι ≫ s_X`.

A divisorial valuation of `k(S)` is the valuation of some divisor `(Y, f, E)` over `S`
(`MMP.Mori.DivisorOver.valuation`), and the discrepancy `a(E, S, B_S)` is
`MMP.Mori.IsDiscrepancy` for some canonical divisor of `S`; the count in the difficulty is the
cardinality of a set of valuations, so divisors over `S` with the same valuation are counted once.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Definition 4.2
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### `ℚ`-divisors as `ℚ`-Weil divisors -/

section QWeil

variable {X : Scheme.{u}}

/-- A `ℚ`-divisor `B = ∑ b_Γ Γ` regarded as the `ℚ`-Weil divisor `∑ b_Γ Γ` of FA 16.2.1, the sum
running over the prime divisors `Γ` along which `𝒪_{X,Γ}` is a discrete valuation ring. -/
def QDivisor.toQWeilDivisor (B : QDivisor X) : MMP.Flips.QWeilDivisor X :=
  Finsupp.subtypeDomain
    (fun Γ : MMP.Mori.PrimeDivisor X =>
      ∃ _ : IsDomain Γ.localRing, IsDiscreteValuationRing Γ.localRing) B

/-- The coefficient of `QDivisor.toQWeilDivisor B` at a prime divisor `Γ` is the coefficient of
`B` at `Γ`. -/
@[simp]
theorem QDivisor.toQWeilDivisor_apply (B : QDivisor X) (Γ : MMP.Flips.WeilDivisorPrime X) :
    QDivisor.toQWeilDivisor B Γ = B.coeff Γ.1 :=
  rfl

/-- `QDivisor.toQWeilDivisor` commutes with subtraction. -/
@[simp]
theorem QDivisor.toQWeilDivisor_sub (B B' : QDivisor X) :
    QDivisor.toQWeilDivisor (B - B') =
      QDivisor.toQWeilDivisor B - QDivisor.toQWeilDivisor B' :=
  Finsupp.subtypeDomain_sub

/-- On a locally Noetherian normal integral scheme every prime divisor is a prime divisor of
FA 16.2.1, so a `ℚ`-divisor is determined by its `ℚ`-Weil divisor. -/
theorem QDivisor.toQWeilDivisor_injective [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] :
    Function.Injective (QDivisor.toQWeilDivisor (X := X)) := by
  intro B B' h
  ext Γ
  exact congrArg (fun D : MMP.Flips.QWeilDivisor X =>
    D ⟨Γ, inferInstance, Γ.isDiscreteValuationRing_localRing⟩) h

end QWeil

/-! ### Poincaré residues -/

section Residue

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsIntegral T] (j : T ⟶ Y)

/-- **The Poincaré residue of an `m`-fold form along a divisor.** Let `j : T ⟶ Y` be an integral
closed subscheme of an integral scheme `Y` over `k`, with generic point `y = j(η_T)` of
codimension one, and `τ` a rational `m`-canonical form of degree `n + 1` on `Y`. A rational
`m`-canonical form `ρ` of degree `n` on `T` is *the residue* `Res_T τ` if there are
`t, g, x₁, …, x_n ∈ 𝒪_{Y,y}`, with `t` a uniformizer (`ord_y t = 1`), such that
`τ = g · (dt/t ∧ dx₁ ∧ ⋯ ∧ dx_n)^{⊗m}` and `ρ = ḡ · (dx̄₁ ∧ ⋯ ∧ dx̄_n)^{⊗m}`, where `f ↦ f̄` is
the restriction `𝒪_{Y,y} → 𝒪_{T,η_T} = k(T)`. The factor `dt/t` is placed first; reordering
it changes `ρ` by `(-1)^{nm}`, so for even `m` the choice is immaterial. -/
@[mmp "def_fourfold_stratified_admissible_sections"]
def IsPoincareResidue (n m : ℕ) (τ : RationalPluriForms sY (n + 1) m)
    (ρ : RationalPluriForms (j ≫ sY) n m) : Prop :=
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  ∃ (t g : Y.presheaf.stalk (j (genericPoint T)))
    (x : Fin n → Y.presheaf.stalk (j (genericPoint T))),
    Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 ∧
    τ = (algebraMap _ Y.functionField g • PiTensorProduct.tprod Y.functionField
        (fun _ : Fin m => (algebraMap _ Y.functionField t)⁻¹ •
          exteriorPower.ιMulti Y.functionField (n + 1)
            (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
              fun i => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (x i)))) :
        TensorPower Y.functionField m (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k])) ∧
    ρ = ((j.stalkMap (genericPoint T)).hom g • PiTensorProduct.tprod T.functionField
        (fun _ : Fin m => exteriorPower.ιMulti T.functionField n
          fun i => KaehlerDifferential.D k T.functionField
            ((j.stalkMap (genericPoint T)).hom (x i))) :
        TensorPower T.functionField m (⋀[T.functionField]^n Ω[T.functionField⁄k]))

end Residue

/-! ### One adjunction step -/

variable {k : Type u} [Field k]

/-- `(T, B_T)` is obtained from `(Y, B_Y)` by *one adjunction step*, for `j : T ⟶ Y`: `T`, with
structure morphism `j ≫ s_Y`, is a normal variety; `j` is a closed immersion onto a prime divisor
`P` of `Y` which is a component of the reduced boundary of `B_Y` (that is, `1 ≤ coeff_P B_Y`; for
effective `B_Y` these are the components of `⌊B_Y⌋`); and `B_T` is the residue different of
Kollár [SMMP, Def. 4.2]: `Y` is a normal variety of dimension `n + 1`, and for some rational top
form `τ ≠ 0` on `Y` with a simple pole along `P` and its Poincaré residue `ρ = Res_T τ`
(`MMP.Fourfold.IsPoincareResidue`), the divisor `K_Y + B_Y = div τ + B_Y` is `ℚ`-Cartier and its
restriction to `T` is `K_T + B_T = div ρ + B_T` (`MMP.Mori.QDivisor.IsPullback`, whose support
condition is part of the statement). Writing `div τ + B_Y = (div τ + P) + (B_Y - P)`, this says
`K_T + B_T = (K_Y + T + (B_Y - T))|_T` with `K_T = div Res_T τ`. The divisor `B_T` does not depend
on `τ` (`MMP.Fourfold.IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue`). -/
@[mmp "def_mmp_stratum_adjunction_data"]
def IsAdjunctionStep {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (BY : QDivisor Y) (j : T ⟶ Y)
    (BT : QDivisor T) : Prop :=
  IsNormalVariety k (j ≫ sY) ∧
    ∃ P : MMP.Mori.PrimeDivisor Y, 1 ≤ BY.coeff P ∧ Set.range j.base = (P.support : Set Y) ∧
      ∃ (_ : IsClosedImmersion j) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
        (_ : CompactSpace Y) (_ : LocallyOfFiniteType sY) (_ : IsIntegral T)
        (_ : IsLocallyNoetherian T) (_ : IsNormal T) (_ : CompactSpace T)
        (_ : LocallyOfFiniteType (j ≫ sY)) (n : ℕ),
        IsNormalVariety k sY ∧ topologicalKrullDim Y = n + 1 ∧
        ∃ τ : RationalPluriForms sY (n + 1) 1, τ ≠ 0 ∧ P.ordForm τ = -1 ∧
          (Divisor.toQDivisor (divisorOfForm τ) + BY).IsQCartier ∧
          ∃ ρ : RationalPluriForms (j ≫ sY) n 1, IsPoincareResidue sY j n 1 τ ρ ∧
            ∃ hgen : ∀ Z : irreducibleComponents T,
                j (componentGenericPoint T Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + BY).supp,
              (Divisor.toQDivisor (divisorOfForm τ) + BY).IsPullback j hgen
                (Divisor.toQDivisor (divisorOfForm ρ) + BT)

/-! ### Iterated adjunction data -/

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]

/-- **Iterated adjunction data on a stratum.** For a rational pair `(X, B)`
(`MMP.Mori.IsPair`; `B` need not be effective), a term of `StratumAdjunctionData sX B ι B_S` is
a flag `X = S₀ ⊃ S₁ ⊃ ⋯ ⊃ S_k = S`, with `ι : S ⟶ X` the composite of the inclusions, together
with the sequence of pairs `(S_j, B_j)` with `B₀ = B` and `B_j = Diff_{S_j}(B_{j-1} - S_j)` the
residue different (Kollár [SMMP, Def. 4.2]), each `S_j` being a normal prime component of the
reduced boundary of `B_{j-1}` on `S_{j-1}` (`MMP.Fourfold.IsAdjunctionStep`, for the structure
morphism of `S_{j-1}` induced from `X`). Such data exist only when every one of these differents
is defined. The pair `(S, B_S) = (S, B_k)` is the adjunction pair on the final stratum of the
flag. -/
@[mmp "def_mmp_stratum_adjunction_data"]
inductive StratumAdjunctionData (B : QDivisor X) : {S : Scheme.{u}} → (S ⟶ X) → QDivisor S →
    Type (u + 1)
  /-- The flag of length zero `X = S₀`, with `B₀ = B`. -/
  | refl (h : MMP.Mori.IsPair sX B) : StratumAdjunctionData B (𝟙 X) B
  /-- Extension of a flag ending at `(S, B_S)` by one adjunction step `T ⊂ S`. -/
  | step {S T : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S}
      (F : StratumAdjunctionData B ι BS) (j : T ⟶ S) (BT : QDivisor T)
      (h : IsAdjunctionStep (ι ≫ sX) BS j BT) : StratumAdjunctionData B (j ≫ ι) BT

/-- `(S, B_S)`, with `ι : S ⟶ X`, is *the adjunction pair on the final stratum* of a flag of
iterated adjunction data of the rational pair `(X, B)`. -/
@[mmp "def_mmp_stratum_adjunction_data"]
def IsStratumAdjunctionPair (B : QDivisor X) {S : Scheme.{u}} (ι : S ⟶ X) (BS : QDivisor S) :
    Prop :=
  Nonempty (StratumAdjunctionData sX B ι BS)

namespace StratumAdjunctionData

variable {sX} {B : QDivisor X}

/-- The length `k` of the flag `X = S₀ ⊃ ⋯ ⊃ S_k`. -/
def length {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} :
    StratumAdjunctionData sX B ι BS → ℕ
  | refl _ => 0
  | step F _ _ _ => F.length + 1

@[simp]
theorem length_refl (h : MMP.Mori.IsPair sX B) :
    (refl h : StratumAdjunctionData sX B (𝟙 X) B).length = 0 :=
  rfl

@[simp]
theorem length_step {S T : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) (j : T ⟶ S) (BT : QDivisor T)
    (h : IsAdjunctionStep (ι ≫ sX) BS j BT) : (F.step j BT h).length = F.length + 1 :=
  rfl

/-- The pair `(X, B)` carrying iterated adjunction data is a rational pair (`MMP.Mori.IsPair`). -/
theorem isRationalPair {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} :
    StratumAdjunctionData sX B ι BS → MMP.Mori.IsPair sX B
  | refl h => h
  | step F _ _ _ => F.isRationalPair

/-- Over an algebraically closed field of characteristic zero, `(X, B)` is a pair
(`MMP.Fourfold.IsPair`) when `B` is effective. -/
theorem isPair [IsAlgClosed k] [CharZero k] {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) (hB : ∀ P, 0 ≤ B.coeff P) : IsPair sX B :=
  ⟨inferInstance, inferInstance, F.isRationalPair, hB⟩

/-- The final stratum, with the structure morphism `ι ≫ s_X`, is a normal variety. -/
theorem isNormalVariety {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} :
    StratumAdjunctionData sX B ι BS → IsNormalVariety k (ι ≫ sX)
  | refl h => by rw [Category.id_comp]; exact h.1
  | step _ _ _ h => by rw [Category.assoc]; exact h.1

/-- The inclusion `ι : S ⟶ X` of the final stratum is a closed immersion. -/
theorem isClosedImmersion {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} :
    StratumAdjunctionData sX B ι BS → IsClosedImmersion ι
  | refl _ => inferInstance
  | step F _ _ h => by
      have := F.isClosedImmersion
      obtain ⟨-, -, -, -, hj, -⟩ := h
      infer_instance

end StratumAdjunctionData

/-- A flag of length zero: `(X, B)` is the adjunction pair of the trivial flag. -/
theorem isStratumAdjunctionPair_refl {B : QDivisor X} (h : MMP.Mori.IsPair sX B) :
    IsStratumAdjunctionPair sX B (𝟙 X) B :=
  ⟨.refl h⟩

/-- One more adjunction step from an adjunction pair is an adjunction pair. -/
theorem IsStratumAdjunctionPair.step {B : QDivisor X} {S T : Scheme.{u}} {ι : S ⟶ X}
    {BS : QDivisor S} (hS : IsStratumAdjunctionPair sX B ι BS) (j : T ⟶ S) {BT : QDivisor T}
    (h : IsAdjunctionStep (ι ≫ sX) BS j BT) : IsStratumAdjunctionPair sX B (j ≫ ι) BT :=
  ⟨.step hS.some j BT h⟩

end MMP.Fourfold

/-! ### The difficulty -/

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
  [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]

/-- For a pair `(S, B_S)` and a number `α`, the set of divisorial valuations `E` of `k(S)` with
discrepancy `a(E, S, B_S) < -α` whose centre on `S` is not contained in `⌊B_S⌋`. A divisorial
valuation is the valuation of a divisor `(Y, f, E)` over `S`; the discrepancy is
`MMP.Mori.IsDiscrepancy` for some canonical divisor `K` of `S` of dimension `n`. -/
def difficultValuations (BS : QDivisor S) (α : ℝ) : Set (Valuation S.functionField ℤᵐ⁰) :=
  {v | ∃ E : DivisorOver k sS, E.valuation = v ∧
    (∃ (n : ℕ) (K : Divisor S) (a : ℚ), IsDiscrepancy sS n K BS E a ∧ (a : ℝ) < -α) ∧
      ¬ (E.center : Set S) ⊆ ((DivisorWithCoeffs.roundDown BS).supp : Set S)}

/-- **The difficulty of an adjunction pair** `(S, B_S)` for the hyperstandard set
`D(I) = MMP.Fourfold.hyperstandardSet I`: the sum over `α ∈ D(I)` of the number of divisorial
valuations `E` of `k(S)` with `a(E, S, B_S) < -α` and centre not contained in `⌊B_S⌋`
(`MMP.Fourfold.difficultValuations`), an element of `ℕ∞`. -/
@[mmp "def_mmp_stratum_difficulty"]
def adjunctionPairDifficulty (I : Finset ℚ) (BS : QDivisor S) : ℕ∞ :=
  ∑' α : hyperstandardSet I, (difficultValuations sS BS α).encard

/-- The difficulty is the sum of the counts in `ℕ∞`, where every family is summable: it is the
supremum of the finite partial sums over `D(I)`. -/
theorem hasSum_adjunctionPairDifficulty (I : Finset ℚ) (BS : QDivisor S) :
    HasSum (fun α : hyperstandardSet I => (difficultValuations sS BS α).encard)
      (adjunctionPairDifficulty sS I BS) :=
  (hasSum_of_isLUB _ (isLUB_sSup _)).summable.hasSum

end MMP.Fourfold

namespace MMP.Fourfold.StratumAdjunctionData

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}

/-- **The difficulty of an adjunction stratum.** For iterated adjunction data with final pair
`(S, B_S)`, the difficulty of `(S, B_S)` for the hyperstandard set `D(I)`
(`MMP.Fourfold.adjunctionPairDifficulty`), `S` carrying the structure morphism `ι ≫ s_X`. -/
@[mmp "def_mmp_stratum_difficulty"]
def difficulty {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) (I : Finset ℚ) : ℕ∞ :=
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  haveI : IsNormal S := F.isNormalVariety.2
  haveI : IsLocallyNoetherian S := by
    have := F.isNormalVariety.1
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
  adjunctionPairDifficulty (ι ≫ sX) I BS

end MMP.Fourfold.StratumAdjunctionData

