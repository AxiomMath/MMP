module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicGeometry.CycleMap.Stacks.ComplexSchemeProduct
public import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Japanese
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeSubscheme
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Finite
public import MMP.AlgebraicTopology.ThomClass.OfRank
public import MMP.AlgebraicGeometry.Variety.SmoothVarietyConstructions

/-!
# The boxed divisor cycle rank of a surface and the difficulty of a model of a prepared chain

For a normal projective complex surface `S`, the *boxed divisor cycle rank* is
`ρ^□(S) = ρ_2(S × ℙ¹)`, the cycle rank of the complex variety `S × ℙ¹`
(`MMP.Analytic.cycleRank`). When `S × ℙ¹` is a normal projective threefold this is its divisor
cycle rank `ρ_*(S × ℙ¹)` (`MMP.Analytic.divisorCycleRank`), which is defined as `ρ_2`.

For a model `(Y, Θ)` of a prepared chain, with labels `S_h`, the *difficulty* is
`𝒟(Y, Θ) = ∑_{c_Y(v) a closed point} w_v + ∑_{C ⊆ Y} β_C(Y, Θ) + ∑_h d_h ρ^□(S_h^ν)`:
the first sum runs over the normalized divisorial valuations `v` of `ℂ(Y)` whose centre on `Y`
is a closed point, with weights `w_v`; the second over the irreducible closed curves `C` of `Y`,
with brackets `β_C = ∑_{c_Y(v) = C} w_v - ∑_h r_{C,h} d_h`; both are finitely supported sums,
`0` by convention if the support were infinite. In the third, `d_h` is the default of the label
`S_h` and `ρ^□(S_h^ν)` the boxed divisor cycle rank of the normalization `S_h^ν` of the label
on `Y`.

## Main definitions

* `MMP.Fourfold.boxedSurfaceRank`: `ρ^□(S) = ρ_2(S × ℙ¹)`.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBoxedRank`: `ρ = ρ^□(S_h^ν)` for a label
  `S_h` of a model of a terminal chain.
* `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`: `D = 𝒟(Y, Θ)` on a model of a
  prepared chain.

## Main results

* `MMP.Fourfold.isComplexScheme_of_isProjectiveVariety`: a projective variety over `ℂ` is a
  complex scheme in Fulton's sense; so is `ℙⁿ_ℂ` (`MMP.Fourfold.isComplexScheme_projectiveSpace`),
  and hence `S × ℙ¹` for projective `S`.
* `MMP.Fourfold.boxedSurfaceRank_eq_divisorCycleRank`: `ρ^□(S) = ρ_*(S × ℙ¹)`.
* `MMP.Fourfold.isComplexScheme_primeDivisorNormalizationScheme`: the normalization of a prime
  divisor of a projective complex variety is a complex scheme.

## Implementation notes

* `ℙⁿ_ℂ` is `AlgebraicGeometry.Proj (ProjPolyChart.polyGrading ℂ n)`, over `ℂ` through
  `ProjPolyChart.projToSpecCoeff ℂ n`. `S × ℙ¹` is the fibre product
  `CategoryTheory.Limits.pullback (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)` over `Spec ℂ`, over `ℂ`
  through `pullback.snd _ _ ≫ projToSpecCoeff ℂ 1`. The cycle rank is defined for
  complex schemes (`MMP.IsComplexScheme`), so `ρ^□(S)` is defined for every
  complex scheme `S` over `ℂ`; the product of two complex schemes is one
  (`MMP.Chow.isComplexScheme_pullback`). This hypothesis holds for every projective `S`
  (`MMP.Fourfold.isComplexScheme_of_isProjectiveVariety`), in particular for the normal
  projective surfaces of the source, so it excludes none of them; normality and dimension two
  are not needed to define the number.
* The normalization `S_h^ν` of a label is the normalization
  `MMP.Fourfold.primeDivisorNormalizationScheme` of its centre on the model, a prime divisor
  (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCentre`), over `ℂ` through the
  normalization morphism to the model. It is a complex scheme, so `ρ^□(S_h^ν)` is defined: every
  model is a projective variety
  (`MMP.Fourfold.StabilizedTail.TerminalChain.isProjectiveVariety_modelStructure`), the centre is
  a closed subscheme of it, and the normalization of an integral scheme of finite type over `ℂ`
  is finite over it (`MMP.Fourfold.isComplexScheme_primeDivisorNormalizationScheme`).
* As for weights and brackets, the difficulty is a predicate on its value. The first sum is the
  finitely supported sum `∑ᶠ` of chosen weights `w_v` over the valuations whose centre is
  (the closure of) a closed point; these are normalized divisorial valuations by the definition
  of the centre (`MMP.Intersection.IsCentre`). The second is `∑ᶠ` over the proper curves
  `MMP.Mori.ProperCurve` of the model, recorded by their generic points, of chosen brackets; the
  third is over the finitely many labels. Each bracket is taken at its curve before summing.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open MMP (IsComplexScheme)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Projective complex schemes -/

/-- A projective variety over `ℂ` is a complex scheme in Fulton's sense: its structure morphism
is projective, so it imbeds in projective space, a non-singular variety
(`MMP.Analytic.isComplexScheme_of_isProjective`). -/
theorem isComplexScheme_of_isProjectiveVariety (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    (h : AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))) : IsComplexScheme X :=
  MMP.Analytic.isComplexScheme_of_isProjective X h.isProjective.isProjective

/-- Projective space `ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]`, over `ℂ` through `projToSpecCoeff ℂ n`, is a
complex scheme: it is itself a non-singular variety. -/
theorem isComplexScheme_projectiveSpace (n : ℕ)
    [(AlgebraicGeometry.Proj (polyGrading ℂ n)).Over (Spec (.of ℂ))]
    (hP : AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ) = projToSpecCoeff ℂ n) :
    IsComplexScheme (AlgebraicGeometry.Proj (polyGrading ℂ n)) :=
  haveI : IsSmoothVariety ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) := by
    rw [hP]; infer_instance
  IsComplexScheme.of_isSmoothVariety _

/-! ### The boxed divisor cycle rank -/

section BoxedRank

variable (S : Scheme.{0}) [S.Over (Spec (.of ℂ))] [IsComplexScheme S]

/-- The *boxed divisor cycle rank* `ρ^□(S) = ρ_2(S × ℙ¹)` of a complex scheme `S` (in the source,
a normal projective complex surface): the cycle rank `ρ_2` (`MMP.Analytic.cycleRank`) of the
complex scheme `S × ℙ¹ = S ×_{Spec ℂ} ℙ¹_ℂ`, over `ℂ` through `ℙ¹_ℂ = Proj ℂ[x₀, x₁]`. -/
@[mmp "def_mmp_indexd_surface_rank"]
def boxedSurfaceRank : ℕ :=
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ 1⟩
  haveI := isComplexScheme_projectiveSpace 1 rfl
  haveI : IsComplexScheme
      (CategoryTheory.Limits.pullback (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)) :=
    MMP.Chow.isComplexScheme_pullback S (AlgebraicGeometry.Proj (polyGrading ℂ 1))
  MMP.Analytic.cycleRank (CategoryTheory.Limits.pullback (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)) 2

/-- `ρ^□(S)` is the divisor cycle rank `ρ_*(S × ℙ¹)`, which is defined as `ρ_2`. -/
theorem boxedSurfaceRank_eq_divisorCycleRank :
    letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ 1⟩
    haveI := isComplexScheme_projectiveSpace 1 rfl
    haveI : IsComplexScheme
        (CategoryTheory.Limits.pullback (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)) :=
      MMP.Chow.isComplexScheme_pullback S (AlgebraicGeometry.Proj (polyGrading ℂ 1))
    boxedSurfaceRank S = MMP.Analytic.divisorCycleRank
      (CategoryTheory.Limits.pullback (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)) :=
  rfl

end BoxedRank

/-! ### Normalizations of prime divisors of projective varieties -/

section Normalization

variable {Y : Scheme.{0}}

/-- The normalization of an integral scheme locally of finite type over a field is finite: the
scheme is Nagata, hence Japanese. -/
theorem isFinite_normalization_of_locallyOfFiniteType {k : Type} [Field k] (X : Scheme.{0})
    [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents (U : Set X)).Finite) :
    IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization X hX) :=
  normalization_isFinite X (isJapaneseScheme_of_isNagataScheme X
    (isNagataScheme_of_locallyOfFiniteType_over_field k f))

/-- The normalization `P^ν` of a prime divisor `P` of a scheme `Y` over `ℂ` (through `s`) is a
scheme over `ℂ` through `P^ν ⟶ Y`. -/
abbrev primeDivisorNormalizationOver (s : Y ⟶ Spec (.of ℂ)) (P : MMP.Mori.PrimeDivisor Y) :
    (primeDivisorNormalizationScheme P).Over (Spec (.of ℂ)) :=
  ⟨primeDivisorNormalization P ≫ s⟩

/-- The normalization `P^ν` of a prime divisor `P` of a projective variety over `ℂ` is a complex
scheme: `P` is a closed subscheme of the complex scheme `Y`, and `P^ν ⟶ P` is finite. -/
theorem isComplexScheme_primeDivisorNormalizationScheme (s : Y ⟶ Spec (.of ℂ))
    (hs : AlgebraicGeometry.IsProjectiveVariety ℂ s) (P : MMP.Mori.PrimeDivisor Y) :
    letI := primeDivisorNormalizationOver s P
    IsComplexScheme (primeDivisorNormalizationScheme P) := by
  let : Y.Over (Spec (.of ℂ)) := ⟨s⟩
  have : IsComplexScheme Y := isComplexScheme_of_isProjectiveVariety Y hs
  have := P.integral
  have : LocallyOfFiniteType s := hs.toLocallyOfFiniteType
  have : LocallyOfFiniteType (P.idealSheaf.subschemeι ≫ s) := inferInstance
  have hfin := isFinite_normalization_of_locallyOfFiniteType P.idealSheaf.subscheme
    (P.idealSheaf.subschemeι ≫ s)
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  let := primeDivisorNormalizationOver s P
  let : P.idealSheaf.subscheme.Over (Spec (.of ℂ)) := ⟨P.idealSheaf.subschemeι ≫ s⟩
  have : IsComplexScheme P.idealSheaf.subscheme :=
    MMP.isComplexScheme_subscheme P.idealSheaf
  have : (Stacks.AlgebraicGeometry.Normalization.normalization P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)).IsOver
      (Spec (.of ℂ)) := ⟨(Category.assoc _ _ _).symm⟩
  exact MMP.IsComplexScheme.of_isFinite
    (Stacks.AlgebraicGeometry.Normalization.normalization P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U))

end Normalization

namespace StabilizedTail

namespace TerminalChain

variable {T : StabilizedTail} (C : TerminalChain T)

/-- Every model of a terminal chain is a projective variety over `ℂ`: a junction `Y_i` by
definition, and a later model of a bridge as the target of a flip. -/
theorem isProjectiveVariety_modelStructure :
    ∀ x : C.ModelIndex, MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x)
  | ⟨i, none⟩ => (C.junction i).isProjectiveVariety
  | ⟨i, some ⟨0, _⟩⟩ => (C.junction i).isProjectiveVariety
  | ⟨i, some ⟨k + 1, hk⟩⟩ =>
    ((C.bridge i).P.isThreefoldStepDiagram k (by omega)).isProjectiveVariety_plus

/-- The normalization `S_h^ν` of the centre `P` of a label on a model of a terminal chain is a
complex scheme, over `ℂ` through `P^ν ⟶ Y`. -/
instance isComplexScheme_primeDivisorNormalizationScheme_model (x : C.ModelIndex)
    (P : MMP.Mori.PrimeDivisor (C.model x)) :
    letI := primeDivisorNormalizationOver (C.modelStructure x) P
    IsComplexScheme (primeDivisorNormalizationScheme P) :=
  isComplexScheme_primeDivisorNormalizationScheme _ (C.isProjectiveVariety_modelStructure x) P

/-- `ρ` is the boxed divisor cycle rank `ρ^□(S_h^ν)` of the normalization of a label `S_h` on the
model `M` indexed by `x`: the centre `S_h^M` is a prime divisor `P` of `M`, and `ρ = ρ^□(P^ν)`
(`MMP.Fourfold.boxedSurfaceRank`) for its normalization `P^ν`
(`MMP.Fourfold.primeDivisorNormalizationScheme`), over `ℂ` through `P^ν ⟶ M`, a complex scheme by
`MMP.Fourfold.StabilizedTail.TerminalChain.isComplexScheme_primeDivisorNormalizationScheme_model`.
-/
def IsLabelBoxedRank (S : C.Label) (x : C.ModelIndex) (ρ : ℕ) : Prop :=
  ∃ P : MMP.Mori.PrimeDivisor (C.model x), C.IsLabelCentre S x P ∧
    letI := primeDivisorNormalizationOver (C.modelStructure x) P
    haveI := C.isComplexScheme_primeDivisorNormalizationScheme_model x P
    ρ = boxedSurfaceRank (primeDivisorNormalizationScheme P)

end TerminalChain

namespace PreparedChain

variable {T : StabilizedTail} (Q : PreparedChain T)

/-- `D` is the *difficulty* `𝒟(Y, Θ)` of the model `(Y, Θ)` of the prepared chain indexed by `x`:
`D = ∑_{c_Y(v) a closed point} w_v + ∑_C β_C(Y, Θ) + ∑_h d_h ρ^□(S_h^ν)`. The first sum, over
the normalized divisorial valuations `v` of `ℂ(Y)` whose centre on `Y` is a closed point, is the
finitely supported sum (`0` if the support were infinite) of their weights `w_v`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`) at the fixed admissible scale; the
second, over the irreducible closed curves `C` of `Y`, is the finitely supported sum of the
brackets `β_C(Y, Θ)` (`MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`); the third runs
over the finitely many labels `S_h`, with defaults `d_h`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelDefault`) and boxed divisor cycle ranks
`ρ^□(S_h^ν)` of their normalizations
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBoxedRank`). -/
@[mmp "def_mmp_indexd_difficulty"]
def IsDifficulty (x : Q.ModelIndex) (D : ℤ) : Prop :=
  ∃ (w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (β : ProperCurve (Q.chain.modelStructure x.1) → ℤ) (d ρ : Q.chain.Label → ℕ),
    (∀ v, (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
          ∃ y : Q.chain.model x.1, IsClosed ({y} : Set (Q.chain.model x.1)) ∧
            (Z : Set (Q.chain.model x.1)) = {y}) →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v)) ∧
    (∀ γ, Q.IsCurveBracket x γ (β γ)) ∧
    (∀ S, Q.chain.IsLabelDefault Q.scale S x.1 (d S)) ∧
    (∀ S, Q.chain.IsLabelBoxedRank S x.1 (ρ S)) ∧
    D = ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
          ∃ y : Q.chain.model x.1, IsClosed ({y} : Set (Q.chain.model x.1)) ∧
            (Z : Set (Q.chain.model x.1)) = {y}), w v : ℕ) : ℤ) +
      ∑ᶠ γ, β γ + ((∑ᶠ S, d S * ρ S : ℕ) : ℤ)

end PreparedChain

end StabilizedTail

end MMP.Fourfold
