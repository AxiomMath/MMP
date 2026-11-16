module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import StacksFrontier.AlgebraicGeometry.Properties.NormalCodimensionOne
import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.ConductorDescent
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.Surface.DiscrepancyMultiplicity
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
import MMP.AlgebraicGeometry.Singularities.Surface.MldDenominatorBound
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.SNCWeight.PrimitiveWeightModification
import MMP.AlgebraicGeometry.MMP.Abundance.SubkltSurfacePluriformFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.CrepantDifferentMatch
import MMP.AlgebraicGeometry.MMP.Abundance.NormalizedSectionDegreeZero
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelProperties
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStep
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentExistence
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumDiscrepancyMonotone
import MMP.AlgebraicGeometry.Singularities.Adjunction.EffectiveResidueAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.SmoothDivisorResidueRestriction
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryPushforward
import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import StacksFrontier.AlgebraicGeometry.Properties.Dimension
import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Curves.RationalFunctionDegree
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.LogCanonicalOneResolution
import MMP.AlgebraicGeometry.Singularities.SncStrata.ZeroPlaceExtraction
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
public import MMP.AlgebraicGeometry.Singularities.Adjunction.MonomialValuationResidue

/-!
# Residues of crepant pull-backs along floor curves sent to exceptional divisors

Let `(X_i, B_i)` be one of a finite collection of rational dlt surface pairs carrying a
preadmissible section system `s`, and `σ : (X_i, B_i) ⇢ (X_j, B_j)` a crepant birational map
carrying the valuation of a floor curve `P ⊆ X_i` to a divisor `D` exceptional over `X_j`. Then
the residue of `σ^* s_j` along `P` is the residue of `s_i` along `P`.

The divisor `D` has log discrepancy zero over the dlt pair `(X_j, B_j)`, so its centre is a
zero-dimensional stratum `p` of `X_j`, a crossing of two floor curves. The normal curve `T` over
`P` is then a rational curve with `K_T + B_T ∼ 0`, `B_T` being two points: the residues along `P`
of all sections of `m(K_{X_i} + B_i)` lie on one line of `m`-canonical forms on `T`, spanned by a
form with a pole of order `m` at a zero-dimensional stratum `q ∈ T`, so a residue along `P` is
determined by its residue at `q`. At `q` the iterated residue of `σ^* s_j` is the iterated
residue of `s_j` at `p`, which by preadmissibility (between points, every isomorphism of
function fields is crepant) is the iterated residue of `s_i` at `q`.

## Main results

* `MMP.Fourfold.toFun_step_refl_eq_of_isExceptional_of_isCrepantBirationalMap`

## References

* [Kollár, *Singularities of the minimal model program*][kollar2013singularities]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

variable {k : Type} [Field k] {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {m : ℕ}

/-! ### The remaining geometric inputs -/

/-- **The floor curve sent to an exceptional divisor is an lc place of `(X_j, B_j)`.** If `σ`
carries the valuation of the floor curve `P` (the image of an adjunction step) to a divisor `D`
over `X_j`, then `D` has log discrepancy `0` with respect to `(X_j, B_j)`. -/
theorem hasLogDiscrepancy_valuation_eq_zero_of_isCrepantBirationalMap
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) :
    HasLogDiscrepancy (sX j) (B j) D.valuation 0 := by
  have hPi := R.setting.isPair i
  haveI := hPi.isAlgClosed
  have hX := hPi.isPair.isNormalVariety
  -- `ι` is supported on `P`
  have hrange : Set.range ι.base = (P.support : Set (X i)) := by
    obtain ⟨-, P₀, -, hrange₀, -⟩ := id hι
    have h1 : closure ({ι (genericPoint T)} : Set (X i)) = Set.range ι.base := by
      apply le_antisymm
      · rw [hrange₀]
        exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure P₀ ▸
          isClosed_closure).closure_subset_iff.mpr
          (Set.singleton_subset_iff.mpr (hrange₀ ▸ Set.mem_range_self _))
      · rintro _ ⟨z, rfl⟩
        have hz : genericPoint T ⤳ z := (genericPoint_spec T).specializes trivial
        exact specializes_iff_mem_closure.mp (hz.map ι.continuous)
    rw [← h1, hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hc1 : (B i).coeff P = 1 := hι.coeff_eq_one hrange
  obtain ⟨n, hn⟩ := isLogDiscrepancy_ofPrimeDivisor hX h P
  rw [hc1, Rat.cast_one, sub_self] at hn
  have hv := (hσ _ 0).mp ⟨n, _, rfl, hn⟩
  convert hv using 1
  ext g
  rw [hDv]
  change _ = P.divisorialValuation (functionFieldMap (𝟙 (X i)) _)
  rw [functionFieldMap_id_apply]
  rfl

open TopologicalSpace in
/-- **The centre of the lc place lies in the snc locus.** In the situation of
`hasLogDiscrepancy_valuation_eq_zero_of_isCrepantBirationalMap`, the centre of `D` on `X_j` lies
off the closed set `Z` of a dlt witness of `(X_j, B_j)`: on `X_j \ Z` the variety is smooth and
`B_j` is snc, while divisors with centre in `Z` have positive log discrepancy. -/
theorem exists_dltWitness_center_notMem_of_isCrepantBirationalMap
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) :
    ∃ Z : Closeds (X j),
      MMP.Mori.IsSmoothScheme (Scheme.Opens.ι (Z.compl : (X j).Opens) ≫ sX j) ∧
      DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : (X j).Opens) ≫ sX j)
        (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : (X j).Opens)) (B j)) ∧
      D.f D.E.genericPoint ∉ (Z : Set (X j)) := by
  obtain ⟨n, D', hv', hn⟩ :=
    hasLogDiscrepancy_valuation_eq_zero_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv
  have hXj := (R.setting.isPair j).isPair.isNormalVariety
  obtain ⟨-, -, Z, hs, hsnc, hlc⟩ := R.setting.isDltPair j
  refine ⟨Z, hs, hsnc, fun hz => ?_⟩
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXj hv'
  have hsub : (D'.center : Set (X j)) ⊆ Z := by
    rw [D'.center_eq_closure_genericPoint, hc]
    exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz)
  exact lt_irrefl _ (hlc n D' hsub 0 hn)

/-- **The centre of the lc place is a crossing of two floor curves.** In the situation of
`hasLogDiscrepancy_valuation_eq_zero_of_isCrepantBirationalMap`, if `D` is exceptional over `X_j`,
its centre lies on two distinct prime divisors of `X_j` along which `B_j` has coefficient one, and
on no other component of `B_j`. -/
theorem exists_ne_coeff_eq_one_of_isExceptional_of_isCrepantBirationalMap
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    ∃ Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j), Q₁ ≠ Q₂ ∧ (B j).coeff Q₁ = 1 ∧ (B j).coeff Q₂ = 1 ∧
      D.f D.E.genericPoint ∈ Q₁.support ∧ D.f D.E.genericPoint ∈ Q₂.support ∧
      ∀ Q : MMP.Mori.PrimeDivisor (X j), (B j).coeff Q ≠ 0 → D.f D.E.genericPoint ∈ Q.support →
        Q = Q₁ ∨ Q = Q₂ := by
  have hPj := R.setting.isPair j
  haveI := hPj.isAlgClosed
  have hXj := hPj.isPair.isNormalVariety
  obtain ⟨n, D', hv', hn⟩ :=
    hasLogDiscrepancy_valuation_eq_zero_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv
  have hpt := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXj hv'
  obtain ⟨Z, hs, hsnc, hZ⟩ :=
    exists_dltWitness_center_notMem_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv
  obtain ⟨-, hB1, -⟩ := R.setting.isDltPair j
  have hcoh := DivisorOver.coheight_eq_two_of_isExceptional hXj
    (by exact_mod_cast R.setting.topologicalKrullDim_eq j) D hD
  rw [← hpt] at hZ hcoh ⊢
  exact exists_ne_coeff_eq_one_of_isLogDiscrepancy_eq_zero hPj.isPair hB1 Z hs hsnc D' hn hZ hcoh

/-- **The centre of the lc place is a zero-dimensional stratum.** In the situation of
`exists_ne_coeff_eq_one_of_isExceptional_of_isCrepantBirationalMap`, iterated adjunction on
`(X_j, B_j)` is defined along a flag ending at the centre `p` of `D`. -/
theorem exists_stratumAdjunctionData_range_eq_center_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    ∃ (S' : Scheme.{0}) (ι' : S' ⟶ X j) (BS' : QDivisor S')
      (F' : StratumAdjunctionData (sX j) (B j) ι' BS'),
      Set.range ι'.base = {D.f D.E.genericPoint} ∧ topologicalKrullDim S' = (0 : ℕ) ∧
        F'.length = 2 := by
  have hPj := R.setting.isPair j
  haveI := hPj.isAlgClosed
  haveI := hPj.charZero
  have hXj := hPj.isPair.isNormalVariety
  have hd : topologicalKrullDim (X j) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq j
  obtain ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, -⟩ :=
    exists_ne_coeff_eq_one_of_isExceptional_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv hD
  have hS := isDltStratum_singleton_of_coeff_eq_one (R.setting.isDltPair j)
    (DivisorOver.isClosed_singleton_of_isExceptional hXj hd D hD)
    (DivisorOver.coheight_eq_two_of_isExceptional hXj hd D hD) hne h₁ h₂ hp₁ hp₂
  obtain ⟨⟨⟨S', ι', BS', hr, ⟨F'⟩⟩, -⟩, -⟩ :=
    IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hS
  -- `S'` is a single point
  haveI := F'.isIntegral_stratum
  haveI := F'.isClosedImmersion
  haveI : Subsingleton S' := ⟨fun a b => ι'.isClosedEmbedding.injective <| by
    have ha : ι' a ∈ Set.range ι'.base := ⟨a, rfl⟩
    have hb : ι' b ∈ Set.range ι'.base := ⟨b, rfl⟩
    rw [hr] at ha hb
    exact ha.trans hb.symm⟩
  have hdim : topologicalKrullDim S' = (0 : ℕ) := by
    haveI : Nonempty (TopologicalSpace.IrreducibleCloseds S') :=
      ⟨(irreducibleSetEquivPoints (α := S')).symm (genericPoint S')⟩
    exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology S') Order.krullDim_nonneg
  have hlen :=
    StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq j) F' hdim
  exact ⟨S', ι', BS', F', hr, hdim, by omega⟩

open exteriorPower in
/-- **Log pluricanonical sections at the centre of the lc place.** In the situation of
`exists_ne_coeff_eq_one_of_isExceptional_of_isCrepantBirationalMap`, the local ring of `X_j` at
the centre `p` of `D` has a regular system of parameters `x, y`, local equations of the two
coefficient-one curves `Q₁, Q₂` through `p`, such that `dx ∧ dy` generates `Ω²_{𝒪_{X_j,p}/k}`
and every section of `m(K_{X_j} + B_j)` is `g (dx/x ∧ dy/y)^{⊗m}` with `g ∈ 𝒪_{X_j,p}`. -/
theorem exists_stalk_eq_smul_formPow_dlog_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
    letI := functionFieldAlgebra (sX j)
    haveI := isScalarTower_stalk_functionField (sX j) (D.f D.E.genericPoint)
    ∃ Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j), Q₁ ≠ Q₂ ∧ (B j).coeff Q₁ = 1 ∧ (B j).coeff Q₂ = 1 ∧
      D.f D.E.genericPoint ∈ Q₁.support ∧ D.f D.E.genericPoint ∈ Q₂.support ∧
      ∃ x y : (X j).presheaf.stalk (D.f D.E.genericPoint),
        MMP.Mori.IsRegularSystemOfParameters ![x, y] ∧
        IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x} ∧
        IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y} ∧
        Submodule.span ((X j).presheaf.stalk (D.f D.E.genericPoint))
          {ιMulti ((X j).presheaf.stalk (D.f D.E.genericPoint)) 2
            ![KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) x,
              KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) y]} = ⊤ ∧
        topFormsMap k ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField 2
          (ιMulti ((X j).presheaf.stalk (D.f D.E.genericPoint)) 2
            ![KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) x,
              KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) y]) ≠ 0 ∧
        ∀ m' : ℕ, ∀ τ ∈ logPluricanonicalSections (sX j) 2 m' (B j),
          ∃ g : (X j).presheaf.stalk (D.f D.E.genericPoint),
            τ = algebraMap _ (X j).functionField g •
              (formPow (ιMulti (X j).functionField 2
                ![(algebraMap _ (X j).functionField x)⁻¹ •
                    KaehlerDifferential.D k (X j).functionField
                      (algebraMap _ (X j).functionField x),
                  (algebraMap _ (X j).functionField y)⁻¹ •
                    KaehlerDifferential.D k (X j).functionField
                      (algebraMap _ (X j).functionField y)]) m' :
                RationalPluriForms (sX j) 2 m') := by
  have hPj := R.setting.isPair j
  haveI := hPj.charZero
  have hXj := hPj.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim (X j) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq j
  obtain ⟨Z, -, hsnc, hZ⟩ :=
    exists_dltWitness_center_notMem_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv
  obtain ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, hQ⟩ :=
    exists_ne_coeff_eq_one_of_isExceptional_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv hD
  have hcoh := DivisorOver.coheight_eq_two_of_isExceptional hXj hd D hD
  exact ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, exists_stalk_eq_smul_formPow_dlog_of_isSNC_restrict hd
    (Z.compl : (X j).Opens) hsnc ⟨D.f D.E.genericPoint, hZ⟩ hcoh hne h₁ h₂ hp₁ hp₂ hQ⟩

open Classical TopologicalSpace in
/-- **Lc places over an snc crossing have coprime orders.** Let `W` be a smooth surface over an
algebraically closed field of characteristic zero, `T` a reduced snc divisor on `W`, and `D` a
divisor over `W` with log discrepancy `0` with respect to `(W, T)` whose centre is a closed point
`p` lying on two components `Q₁ ≠ Q₂` of `T`, with local equations `x, y` at `p`. Then the orders
`a = v_D(x)`, `b = v_D(y)` are coprime: `ac + bd = 1` for some integers `c, d`. Indeed `D` is
then the divisor of the monomial valuation of the primitive weight `(a, b) / gcd(a, b)`, read on
the snc modification adapted to that weight. Moreover `v_D` is
monomial of weights `(a, b)` in `x, y`: an element of `𝒪_p` of valuation `exp(-M)` lies in
the weighted monomial ideal of degree `M`. -/
theorem exists_coprime_mem_weightedMonomialIdeal_of_isLogDiscrepancy_eq_zero {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hW : MMP.Mori.IsVariety k sW)
    (hWs : MMP.Mori.IsSmoothScheme sW) {T : Divisor W}
    (hT : MMP.Intersection.IsReducedEffective T) (hTs : T.IsSNC sW)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor W} (hne : Q₁ ≠ Q₂) (h₁ : Q₁ ∈ T.support)
    (h₂ : Q₂ ∈ T.support) {n : ℕ} (D : DivisorOver k sW) (hDp : IsProper D.f)
    {B : QDivisor W} (hB₁ : B.coeff Q₁ = 1) (hB₂ : B.coeff Q₂ = 1)
    (hBT : ∀ P, B.coeff P ≠ 0 → P ∈ T.support)
    (hD : MMP.Intersection.IsLogDiscrepancy sW n (QDivisor.toRDivisor B) D 0)
    (hcl : IsClosed ({D.f D.E.genericPoint} : Set W))
    (hcoh : Order.coheight (D.f D.E.genericPoint) = 2) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support) {x y : W.presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      D.valuation (algebraMap _ W.functionField x) = WithZero.exp (-(a : ℤ)) ∧
      D.valuation (algebraMap _ W.functionField y) = WithZero.exp (-(b : ℤ)) ∧
      ∀ f : W.presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∀ M : ℕ,
        D.valuation (algebraMap _ W.functionField f) = WithZero.exp (-(M : ℤ)) →
        f ∈ weightedMonomialIdeal ![x, y] ![a, b] M := by
  -- the orders `a, b ≥ 1`
  have hval : ∀ (Q : MMP.Mori.PrimeDivisor W) (z : W.presheaf.stalk (D.f D.E.genericPoint)),
      (D.f D.E.genericPoint) ∈ Q.support →
      IdealSheafData.stalk Q.idealSheaf (D.f D.E.genericPoint) = Ideal.span {z} →
      ∃ a : ℕ, 0 < a ∧ D.valuation (algebraMap _ W.functionField z) = WithZero.exp (-(a : ℤ)) := by
    intro Q z hpQ hz
    have hz0 := SNCWeight.LocalEquation.localEq_ne_zero Q hpQ hz
    obtain ⟨q, -, hq, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Q hpQ
    have hzm : z ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk (D.f D.E.genericPoint)) := by
      have hzq : z ∈ q.asIdeal := by rw [← hq, hz]; exact Ideal.mem_span_singleton_self z
      exact IsLocalRing.le_maximalIdeal q.2.ne_top hzq
    have hlt := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one
      D (D.f D.E.genericPoint) rfl z hzm
    have hne0 : D.valuation (algebraMap _ W.functionField z) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hz0
    refine ⟨(-WithZero.log (D.valuation (algebraMap _ W.functionField z))).toNat, ?_, ?_⟩
    · have : WithZero.log (D.valuation (algebraMap _ W.functionField z)) < 0 := by
        rw [← WithZero.exp_lt_exp, WithZero.exp_log hne0, WithZero.exp_zero]; exact hlt
      omega
    · have : WithZero.log (D.valuation (algebraMap _ W.functionField z)) < 0 := by
        rw [← WithZero.exp_lt_exp, WithZero.exp_log hne0, WithZero.exp_zero]; exact hlt
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne0]
  obtain ⟨a, ha0, hva⟩ := hval Q₁ x hp₁ hx
  obtain ⟨b, hb0, hvb⟩ := hval Q₂ y hp₂ hy
  -- the primitive weight `α = (a, b) / g`
  set g := Nat.gcd a b with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ ha0
  have hcop : Nat.Coprime (a / g) (b / g) := Nat.coprime_div_gcd_div_gcd hg0
  have haa : a = g * (a / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hbb : b = g * (b / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have ha'0 : 0 < a / g := Nat.div_pos (Nat.gcd_le_left _ ha0) hg0
  have hb'0 : 0 < b / g := Nat.div_pos (Nat.gcd_le_right _ hb0) hg0
  set J : Finset (MMP.Mori.PrimeDivisor W) := {Q₁, Q₂} with hJ
  have hmemJ : ∀ j : J, j.1 = Q₁ ∨ j.1 = Q₂ := fun ⟨P, hP⟩ => by
    simpa only [hJ, Finset.mem_insert, Finset.mem_singleton] using hP
  let α : J → ℕ := fun j => if j.1 = Q₁ then a / g else b / g
  have hα : ∀ j, 0 < α j := fun j => by simp only [α]; split_ifs <;> assumption
  have hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1 := fun d hd => by
    have h1 := hd ⟨Q₁, by simp [J]⟩
    have h2 := hd ⟨Q₂, by simp [J]⟩
    simp only [α, if_pos rfl, if_neg (Ne.symm hne)] at h1 h2
    exact (Nat.coprime_self _).mp
      (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h2 hcop))
  -- the centre `Z = {p}` is a component of `Q₁ ∩ Q₂`
  have hZset : (D.center : Set W) = {D.f D.E.genericPoint} := by
    rw [D.center_eq_closure_genericPoint, hcl.closure_eq]
  have hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support)
      (D.center : Set W) := by
    rw [hZset]
    exact maximal_singleton_of_coheight_eq_two hcl hcoh hne hp₁ hp₂
  have hJT : J ⊆ T.support := fun P hP => by
    rcases (by simpa [J] using hP : P = Q₁ ∨ P = Q₂) with rfl | rfl
    exacts [h₁, h₂]
  have hη : D.center.isIrreducible.genericPoint = D.f D.E.genericPoint := by
    have h1 : closure ({D.center.isIrreducible.genericPoint} : Set W) =
        closure {D.f D.E.genericPoint} :=
      D.center.isIrreducible.isGenericPoint_genericPoint_closure.def.trans (by rw [hZset])
    exact (inseparable_iff_closure_eq.2 h1).eq
  obtain ⟨x', y', hxy', hx', hy', hvx', hvy', hback⟩ : ∃ x' y' :
      W.presheaf.stalk D.center.isIrreducible.genericPoint,
      MMP.Mori.IsRegularSystemOfParameters ![x', y'] ∧
      IdealSheafData.stalk Q₁.idealSheaf D.center.isIrreducible.genericPoint = Ideal.span {x'} ∧
      IdealSheafData.stalk Q₂.idealSheaf D.center.isIrreducible.genericPoint = Ideal.span {y'} ∧
      D.valuation (algebraMap _ W.functionField x') = WithZero.exp (-(a : ℤ)) ∧
      D.valuation (algebraMap _ W.functionField y') = WithZero.exp (-(b : ℤ)) ∧
      ((∀ f : W.presheaf.stalk D.center.isIrreducible.genericPoint, f ≠ 0 → ∀ M : ℕ,
          D.valuation (algebraMap _ W.functionField f) = WithZero.exp (-(M : ℤ)) →
          f ∈ weightedMonomialIdeal ![x', y'] ![a, b] M) →
        ∀ f : W.presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∀ M : ℕ,
          D.valuation (algebraMap _ W.functionField f) = WithZero.exp (-(M : ℤ)) →
          f ∈ weightedMonomialIdeal ![x, y] ![a, b] M) := by
    rw [hη]
    exact ⟨x, y, hxy, hx, hy, hva, hvb, fun h => h⟩
  let z : J → W.presheaf.stalk D.center.isIrreducible.genericPoint :=
    fun j => if j.1 = Q₁ then x' else y'
  have hz : ∀ j : J, IdealSheafData.stalk j.1.idealSheaf D.center.isIrreducible.genericPoint =
      Ideal.span {z j} := fun j => by
    rcases hmemJ j with h | h
    · simp only [z, if_pos h]; rw [h]; exact hx'
    · have h' : j.1 ≠ Q₁ := fun h'' => hne (h''.symm.trans h)
      simp only [z, if_neg h']; rw [h]; exact hy'
  -- the snc modification adapted to `α`
  obtain ⟨U, hηU, -, hUJ, hmod⟩ := exists_snc_modification_primitive_weight sW hW hWs T hT hTs J
    ⟨Q₁, by simp [J]⟩ hJT D.center hZ α hα hαp
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  obtain ⟨W', hW'i, hW'l, hW'n, g', hg', hdom, hW', T', hproj, -, hsm', hred', hsnc', -, -,
    ⟨n', K, hK, hcrep⟩, E, hE, hmono, hcent⟩ := hmod
  haveI := hW'i
  haveI := hW'l
  haveI := hW'n
  have hz0 : ∀ j, ¬ (z j = 0) := fun j h0 => by
    have := SNCWeight.LocalEquation.localEq_ne_zero j.1 (hη ▸ (by
      rcases hmemJ j with h | h <;> rw [h] <;> assumption)) (hz j)
    rw [h0, map_zero] at this
    exact this rfl
  -- the valuation of `D` has orders `g α` on the local equations
  have hvz : ∀ j, D.valuation (algebraMap _ W.functionField (z j)) =
      WithZero.exp (-((g * α j : ℕ) : ℤ)) := fun j => by
    rcases hmemJ j with h | h
    · simp only [z, α, if_pos h]; rw [hvx', ← haa]
    · have h' : j.1 ≠ Q₁ := fun h'' => hne (h''.symm.trans h)
      simp only [z, α, if_neg h']; rw [hvy', ← hbb]
  obtain ⟨ξ', C', hcm, ⟨D'', hD''p, rfl, rfl⟩, hCE, hCF⟩ :=
    hcent D.valuation g z hz ⟨D, hDp, rfl, rfl⟩ hg0 hvz
  -- instances on `W` and `W'`
  haveI := hdom
  haveI : AlgebraicGeometry.IsVariety k sW := hW
  haveI : Smooth sW := MMP.Mori.IsSmoothScheme.smooth hWs
  haveI : IsSmoothVariety k sW := ⟨⟩
  haveI hWv : AlgebraicGeometry.IsVariety k (g' ≫ U.ι ≫ sW) := hW'.1
  haveI : LocallyOfFiniteType (g' ≫ U.ι ≫ sW) := hWv.toLocallyOfFiniteType
  haveI : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (g' ≫ U.ι ≫ sW)
  haveI : Smooth (g' ≫ U.ι ≫ sW) := MMP.Mori.IsSmoothScheme.smooth hsm'
  haveI : IsSmoothVariety k (g' ≫ U.ι ≫ sW) := ⟨⟩
  haveI : PerfectField k := PerfectField.ofCharZero
  have hcartW := (Divisor.cartier_weil_dictionary_of_isSmoothVariety k sW).1
  have hcartW' := (Divisor.cartier_weil_dictionary_of_isSmoothVariety k (g' ≫ U.ι ≫ sW)).1
  -- the pair `(W, T)`
  have hn : topologicalKrullDim W = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD
  obtain ⟨hWN, -, -, -, ⟨K₀, hK₀, -⟩, -⟩ := id hD
  obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor B
  have hpair : MMP.Mori.IsPair sW B := ⟨hWN, n, K₀, hK₀, N, by exact_mod_cast hN.ne', by
    rw [smul_add, ← hG, ← map_zsmul, ← map_add]
    exact MMP.Mori.QDivisor.isCartierDivisor_toQDivisor.mpr (hcartW _)⟩
  -- restriction to `U`, through the divisor `D''` over `W'`
  haveI : IsDominant g' := hg'.isDominant
  haveI := D''.isIntegral
  haveI := D''.isNormal
  haveI := D''.isLocallyNoetherian
  haveI := D''.isDominant
  let D_U : DivisorOver k (U.ι ≫ sW) :=
    { Y := D''.Y
      f := D''.f ≫ g'
      isNormalVariety := by rw [Category.assoc]; exact D''.isNormalVariety
      isBirationalMorphism :=
        MMP.Mori.IsPair.isBirationalMorphism_comp D''.isBirationalMorphism hg'
      E := D''.E }
  haveI : IsDominant (D''.f ≫ g') := inferInstance
  have hvU' : D_U.valuation = D''.valuation.comap (functionFieldMap g') := by
    ext t
    change D''.E.divisorialValuation (functionFieldMap (D''.f ≫ g') t) =
      D''.E.divisorialValuation (functionFieldMap D''.f (functionFieldMap g' t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hvU : D.valuation = D_U.valuation.comap (functionFieldMap U.ι) := by
    rw [hvU', ← hcm]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hηmem : D.f D.E.genericPoint ∈ U := hη ▸ hηU
  haveI : IsProper g' := AlgebraicGeometry.isProper_of_isProjectiveMorphism g' hproj
  haveI := hD''p
  have hDUp : IsProper D_U.f := (inferInstance : IsProper (D''.f ≫ g'))
  have hlogU := (MMP.isLogDiscrepancy_open_iff sW hpair hn U D hDp hηmem D_U hDUp hvU 0).mp hD
  have hΔ : MMP.Mori.inverseTransformDivisor U.ι B =
      Divisor.toQDivisor (MMP.Mori.inverseTransformDivisor U.ι T) := by
    rw [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen,
      MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen]
    refine DivisorWithCoeffs.ext' fun P => ?_
    change B.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) =
      ((T.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) : ℤ) : ℚ)
    set Q := OpenWeilRestriction.primeDivisorMap U.ι P
    have hQU : (Q.support ∩ (U : Set W)).Nonempty := by
      refine ⟨U.ι P.genericPoint, ?_, SNCWeight.Restriction.ι_mem U _⟩
      rw [← OpenWeilRestriction.genericPoint_primeDivisorMap,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hJ1 : ∀ R ∈ J, B.coeff R = 1 ∧ T.coeff R = 1 := fun R hR => by
      rcases (by simpa [J] using hR : R = Q₁ ∨ R = Q₂) with rfl | rfl
      · exact ⟨hB₁, (hT R).resolve_left (Finsupp.mem_support_iff.mp h₁)⟩
      · exact ⟨hB₂, (hT R).resolve_left (Finsupp.mem_support_iff.mp h₂)⟩
    by_cases hB0 : B.coeff Q = 0
    · rw [hB0]
      by_contra hT0
      have hQT : Q ∈ T.support := Finsupp.mem_support_iff.mpr fun h => hT0 (by
        change (0 : ℚ) = ((T Q : ℤ) : ℚ); rw [h]; simp)
      rw [(hJ1 Q (hUJ Q hQT hQU)).1] at hB0
      exact one_ne_zero hB0
    · have hQJ := hUJ Q (hBT Q hB0) hQU
      rw [(hJ1 Q hQJ).1, (hJ1 Q hQJ).2]
      simp
  rw [hΔ] at hlogU
  have hnn : n = n' := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hlogU).symm.trans
      hK.topologicalKrullDim_eq
  subst hnn
  have hpairU := (hcrep E).isPair
  haveI : AlgebraicGeometry.IsVariety k (U.ι ≫ sW) := hpairU.1.1
  have hdimW' : topologicalKrullDim W' = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (U.ι ≫ sW)
      (g' ≫ U.ι ≫ sW) hg').symm.trans hK.topologicalKrullDim_eq
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (g' ≫ U.ι ≫ sW) hsm'
    hdimW'
  have hCY : ∀ m : ℕ, 0 < m →
      ((m : ℤ) • (Divisor.toQDivisor K + Divisor.toQDivisor
        (MMP.Mori.inverseTransformDivisor U.ι T))).IsCartierDivisor →
      ((m : ℤ) • (Divisor.toQDivisor KY + Divisor.toQDivisor T')).IsCartierDivisor :=
    fun m _ _ => by
      rw [← map_add, ← map_zsmul]
      exact MMP.Mori.QDivisor.isCartierDivisor_toQDivisor.mpr (hcartW' _)
  have hlogW' := isLogDiscrepancy_of_isCrepantBoundary hpairU hK g' hW' hg' hcrep hKY hCY D_U D''
    hD''p hvU'.symm hlogU
  -- the centre of `D''` on `W'` is the divisor `E`
  obtain ⟨K'', -, hFl⟩ := exists_flipsIsLogDiscrepancy_of_isLogDiscrepancy hlogW'
  let ν : MMP.Flips.ProperDivisorOver k (g' ≫ U.ι ≫ sW) := ⟨D'', hD''p⟩
  have hSsnc : MMP.Flips.IsSNCDivisor (g' ≫ U.ι ≫ sW) T' := ⟨hred', hsnc'.1, fun q _ => hsnc'.2 q⟩
  have hBS : ∀ P, (QDivisor.toRDivisor (Divisor.toQDivisor T')).coeff P ≠ 0 → P ∈ T'.support :=
    fun P hP => Finsupp.mem_support_iff.mpr fun h0 => hP (by
      rw [QDivisor.coeff_toRDivisor]
      change ((((Divisor.toQDivisor T').coeff P : ℚ)) : ℝ) = 0
      rw [show (Divisor.toQDivisor T').coeff P = ((T'.coeff P : ℤ) : ℚ) from rfl]
      rw [show T'.coeff P = 0 from h0]
      simp)
  have hB1 : ∀ P ∈ T'.support, (QDivisor.toRDivisor (Divisor.toQDivisor T')).coeff P ≤ 1 :=
    fun P _ => by
      rw [QDivisor.coeff_toRDivisor]
      rw [show (Divisor.toQDivisor T').coeff P = ((T'.coeff P : ℤ) : ℚ) from rfl]
      rcases hred' P with h | h <;> rw [h] <;> norm_num
  have hcod := codimension_center_le_card_of_isLogDiscrepancy_eq_zero (g' ≫ U.ι ≫ sW) hWv hsm'
    hSsnc hBS hB1 ν hFl
  have hcen : ν.center = D''.center := IrreducibleCloseds.ext <| by
    change _ = closure _
    exact ν.isClosed_image_support.closure_eq.symm
  have hc1 : Order.coheight (D''.f D''.E.genericPoint) ≤ 1 := by
    have h := hcod.trans (show _ ≤ ((1 : ℕ) : ℕ∞) from Nat.cast_le.mpr
      (Finset.card_le_one.mpr fun P hP Q hQ => by
        rw [Finset.mem_filter, hcen] at hP hQ
        have hPE : P = E := by_contra fun h => hCF P hP.1 h hP.2.1
        have hQE : Q = E := by_contra fun h => hCF Q hQ.1 h hQ.2.1
        rw [hPE, hQE]))
    rwa [hcen, MMP.Positivity.DivisorOver.codimension_center] at h
  have hcE : D''.f D''.E.genericPoint ∈ E.support := hCE (by
    rw [D''.center_eq_closure_genericPoint]; exact subset_closure rfl)
  have hc : D''.f D''.E.genericPoint = E.genericPoint := by
    have hs : E.genericPoint ⤳ D''.f D''.E.genericPoint := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hcE
      exact specializes_iff_mem_closure.mpr hcE
    by_contra hne'
    have h2 := Order.coheight_add_one_le ((Scheme.le_iff_specializes.mpr hs).lt_of_not_ge fun h =>
      hne' ((Scheme.le_iff_specializes.mp h).antisymm hs).eq)
    rw [E.coheight_genericPoint] at h2
    have := h2.trans hc1
    exact absurd this (by decide)
  have hvE : D''.valuation = E.divisorialValuation := by
    rw [MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hW' D'' E hc]
    ext t
    change E.divisorialValuation (functionFieldMap (𝟙 W') t) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  -- `ord_E` is monomial of weight `α`, so `g = 1`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmval⟩ := hmono z hz
  rw [← hvE, hcm] at hmval
  have hspan : Ideal.span (Set.range z) =
      IsLocalRing.maximalIdeal (W.presheaf.stalk D.center.isIrreducible.genericPoint) := by
    rw [← hxy'.1]
    congr 1
    ext t
    constructor
    · rintro ⟨j, rfl⟩
      rcases hmemJ j with h | h
      · exact ⟨0, by simp [z, h]⟩
      · exact ⟨1, by simp [z, h, Ne.symm hne]⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨⟨Q₁, by simp [J]⟩, by simp [z]⟩
      · exact ⟨⟨Q₂, by simp [J]⟩, by simp [z, Ne.symm hne]⟩
  have hdim : ringKrullDim (W.presheaf.stalk D.center.isIrreducible.genericPoint) =
      Fintype.card J := by
    rw [hxy'.2, Fintype.card_coe, Finset.card_pair hne]
  have hj₁ : (⟨Q₁, by simp [J]⟩ : J) ∈ (Finset.univ : Finset J) := Finset.mem_univ _
  set j₁ : J := ⟨Q₁, by simp [J]⟩ with hj₁def
  obtain ⟨M, hM, hMv⟩ := hmval (z j₁) (hz0 j₁)
  have hMα : M = α j₁ := by
    refine le_antisymm ?_ (hM.2 (SNCWeight.WeightedOrder.mem_weightedMonomialIdeal_self z α j₁))
    by_contra hlt
    exact SNCWeight.WeightedOrder.notMem_weightedMonomialIdeal_succ z α hα hspan hdim j₁
      (weightedMonomialIdeal_antitone z α (by omega) hM.1)
  have hg1 : g = 1 := by
    have h := (hvz j₁).symm.trans hMv
    rw [hMα] at h
    have h' := WithZero.exp_injective h
    have : g * α j₁ = α j₁ := by exact_mod_cast neg_injective h'
    exact (Nat.mul_eq_right (hα j₁).ne').mp this
  -- conclusion
  have hcop' : Nat.Coprime a b := by
    rwa [hg1, Nat.div_one, Nat.div_one] at hcop
  set j₂ : J := ⟨Q₂, by simp [J]⟩ with hj₂def
  have hinj : Function.Injective (![j₁, j₂] : Fin 2 → J) := by
    intro i i' hii'
    fin_cases i <;> fin_cases i'
    · rfl
    · have := congrArg Subtype.val hii'
      simp [hj₁def, hj₂def] at this
      exact absurd this hne
    · have := congrArg Subtype.val hii'
      simp [hj₁def, hj₂def] at this
      exact absurd this.symm hne
    · rfl
  have hsurj : Function.Surjective (![j₁, j₂] : Fin 2 → J) := by
    intro j
    rcases hmemJ j with h | h
    · exact ⟨0, Subtype.ext (by simp [hj₁def, h])⟩
    · exact ⟨1, Subtype.ext (by simp [hj₂def, h])⟩
  set eJ := Equiv.ofBijective _ ⟨hinj, hsurj⟩ with heJ
  have hz2 : z ∘ eJ = ![x', y'] := by
    funext i
    fin_cases i
    · simp [heJ, z, hj₁def]
    · simp [heJ, z, hj₂def, Ne.symm hne]
  have hα2 : α ∘ eJ = ![a, b] := by
    funext i
    fin_cases i
    · simp [heJ, α, hj₁def, hg1]
    · simp [heJ, α, hj₂def, Ne.symm hne, hg1]
  refine ⟨a, b, ha0, hb0, hcop', hva, hvb, hback ?_⟩
  intro f hf M hfM
  obtain ⟨M', hM', hM'v⟩ := hmval f hf
  have hMM : M' = M := by
    have := hM'v.symm.trans hfM
    exact_mod_cast neg_injective (WithZero.exp_injective this)
  subst hMM
  rw [← hz2, ← hα2, weightedMonomialIdeal_comp_equiv]
  exact hM'.1

open Classical TopologicalSpace in
/-- **Lc places centred at an snc crossing of a pair have coprime orders.** Let `(X, B)` be a
normal surface pair over an algebraically closed field of characteristic zero, smooth with `B`
snc off a closed set `Z`, and `D` a divisor over `X` with log discrepancy `0` whose centre is a
closed point `p ∉ Z` of codimension two on two coefficient-one curves `Q₁ ≠ Q₂`, with local
equations `x, y` at `p`. Then `v_D(x)` and `v_D(y)` are coprime. Moreover `v_D` is
monomial of weights `(a, b)` in `x, y`: an element of `𝒪_p` of valuation `exp(-M)` lies in
the weighted monomial ideal of degree `M`. -/
theorem exists_coprime_mem_weightedMonomialIdeal_of_isSNC_restrict {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} (hB : MMP.Mori.IsPair sX B)
    (Z : Closeds X)
    (hsm : MMP.Mori.IsSmoothScheme (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX))
    (hsnc : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : X.Opens)) B))
    {n : ℕ} (D : DivisorOver k sX)
    (hD : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D 0)
    (hDZ : D.f D.E.genericPoint ∉ (Z : Set X)) (hcl : IsClosed ({D.f D.E.genericPoint} : Set X))
    (hcoh : Order.coheight (D.f D.E.genericPoint) = 2) {Q₁ Q₂ : MMP.Mori.PrimeDivisor X}
    (hne : Q₁ ≠ Q₂) (h₁ : B.coeff Q₁ = 1) (h₂ : B.coeff Q₂ = 1)
    (hp₁ : D.f D.E.genericPoint ∈ Q₁.support) (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : X.presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      D.valuation (algebraMap _ X.functionField x) = WithZero.exp (-(a : ℤ)) ∧
      D.valuation (algebraMap _ X.functionField y) = WithZero.exp (-(b : ℤ)) ∧
      ∀ f : X.presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∀ M : ℕ,
        D.valuation (algebraMap _ X.functionField f) = WithZero.exp (-(M : ℤ)) →
        f ∈ weightedMonomialIdeal ![x, y] ![a, b] M := by
  set U : X.Opens := Z.compl with hU
  have hpU : D.f D.E.genericPoint ∈ U := hDZ
  haveI : Nonempty U := ⟨⟨_, hpU⟩⟩
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, hpU⟩)
  have hXv := hB.1
  haveI : AlgebraicGeometry.IsVariety k sX := hXv.1
  haveI : AlgebraicGeometry.IsVariety k (U.ι ≫ sX) := ⟨⟩
  haveI : PerfectField k := PerfectField.ofCharZero
  obtain ⟨-, n0, K, hK, hQ⟩ := id hB
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hpU⟩
  obtain ⟨hY, hf, E', hE', hval, -⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff ⟨hXv, hK, hQ⟩ D U hcen
  set D_U : DivisorOver k (U.ι ≫ sX) := ⟨_, D.f ∣_ U, hY, hf, E'⟩ with hD_U
  have hDp : IsProper D.f := hD.2.1
  haveI : IsProper (D.f ∣_ U) := by haveI := hDp; infer_instance
  have hn : topologicalKrullDim X = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD
  have hlogU := (MMP.isLogDiscrepancy_open_iff sX hB hn U D hDp hpU D_U inferInstance hval 0).mp hD
  -- the centre of `D_U`
  set p' : U.toScheme := ⟨D.f D.E.genericPoint, hpU⟩
  have hc : D_U.f D_U.E.genericPoint = p' := U.ι.isOpenEmbedding.injective <| by
    change U.ι ((D.f ∣_ U) E'.genericPoint) = D.f D.E.genericPoint
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE',
      ← OpenWeilRestriction.genericPoint_primeDivisorMap]
  -- the boundary on `U`
  set BU := MMP.Mori.inverseTransformDivisor U.ι B with hBUdef
  have hBU : ∀ W, BU.coeff W = B.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := fun W => by
    rw [hBUdef, MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen (U := U)]
    rfl
  let T : Divisor U := MMP.Intersection.reducedDivisorOf BU.support
  have hTsupp : T.support = BU.support := MMP.Intersection.support_reducedDivisorOf _
  have hTred : MMP.Intersection.IsReducedEffective T := fun P => by
    change (MMP.Intersection.reducedDivisorOf BU.support).coeff P = 0 ∨ _
    rw [MMP.Intersection.coeff_reducedDivisorOf]
    split_ifs <;> simp
  have hTs : T.IsSNC (U.ι ≫ sX) := hsnc.of_support_subset hTsupp.le
  have hBT : ∀ P, BU.coeff P ≠ 0 → P ∈ T.support := fun P hP => by
    rw [hTsupp]; exact Finsupp.mem_support_iff.mpr (by rwa [DivisorWithCoeffs.coeff_apply] at hP)
  obtain ⟨W₁, rfl⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι Q₁ p' hp₁
  obtain ⟨W₂, rfl⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι Q₂ p' hp₂
  have hp₁' := (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι W₁ p').mp hp₁
  have hp₂' := (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι W₂ p').mp hp₂
  have hcoh' : Order.coheight p' = 2 := by rwa [← coheight_eq_of_isOpenImmersion U.ι]
  have hcl' : IsClosed ({p'} : Set U.toScheme) := by
    have := hcl.preimage U.ι.continuous
    convert this using 1
    ext q
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => U.ι.isOpenEmbedding.injective h⟩
  -- local equations on `U`
  let e : X.presheaf.stalk (U.ι p') ≃+* U.toScheme.presheaf.stalk p' :=
    (asIso (U.ι.stalkMap p')).commRingCatIsoToRingEquiv
  have hee : (e : X.presheaf.stalk (U.ι p') →+* U.toScheme.presheaf.stalk p') =
      (U.ι.stalkMap p').hom := rfl
  have hloc : ∀ (W : MMP.Mori.PrimeDivisor U) (z : X.presheaf.stalk (U.ι p')),
      IdealSheafData.stalk (OpenWeilRestriction.primeDivisorMap U.ι W).idealSheaf (U.ι p') =
        Ideal.span {z} → IdealSheafData.stalk W.idealSheaf p' = Ideal.span {e z} := fun W z hz => by
    rw [SNCWeight.Restriction.stalk_primeDivisorMap_comap U W p', hz, Ideal.map_span,
      Set.image_singleton]
    rfl
  have hvalz : ∀ z : X.presheaf.stalk (U.ι p'), D.valuation (algebraMap _ X.functionField z) =
      D_U.valuation (algebraMap _ U.toScheme.functionField (e z)) := fun z => by
    rw [hval, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk U.ι p' z]
    rfl
  obtain ⟨xU, yU, hxyU, hxU, hyU, hvx, hvy, hback⟩ : ∃ xU yU :
      U.toScheme.presheaf.stalk (D_U.f D_U.E.genericPoint),
      MMP.Mori.IsRegularSystemOfParameters ![xU, yU] ∧
      IdealSheafData.stalk W₁.idealSheaf (D_U.f D_U.E.genericPoint) = Ideal.span {xU} ∧
      IdealSheafData.stalk W₂.idealSheaf (D_U.f D_U.E.genericPoint) = Ideal.span {yU} ∧
      D.valuation (algebraMap _ X.functionField x) =
        D_U.valuation (algebraMap _ U.toScheme.functionField xU) ∧
      D.valuation (algebraMap _ X.functionField y) =
        D_U.valuation (algebraMap _ U.toScheme.functionField yU) ∧
      (∀ α : Fin 2 → ℕ, ∀ M : ℕ,
        (∀ f' : U.toScheme.presheaf.stalk (D_U.f D_U.E.genericPoint), f' ≠ 0 →
          D_U.valuation (algebraMap _ U.toScheme.functionField f') = WithZero.exp (-(M : ℤ)) →
          f' ∈ weightedMonomialIdeal ![xU, yU] α M) →
        ∀ f : X.presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 →
          D.valuation (algebraMap _ X.functionField f) = WithZero.exp (-(M : ℤ)) →
          f ∈ weightedMonomialIdeal ![x, y] α M) := by
    rw [hc]
    refine ⟨e x, e y, ?_, hloc W₁ x hx, hloc W₂ y hy, hvalz x, hvalz y, ?_⟩
    · have := MMP.Resolution.isRegularSystemOfParameters_map_ringEquiv e hxy
      convert this using 1
      ext i
      fin_cases i <;> rfl
    · intro α M hU f hf hfM
      have hef : e f ≠ 0 := fun h0 => hf (e.injective (h0.trans (map_zero e).symm))
      have hmem := hU (e f) hef ((hvalz f).symm.trans hfM)
      have hmap : Ideal.map e (weightedMonomialIdeal ![x, y] α M) =
          weightedMonomialIdeal ![e x, e y] α M :=
        (weightedMonomialIdeal_map e ![x, y] α M).trans (by
          congr 1
          funext i
          fin_cases i <;> rfl)
      rw [← hmap] at hmem
      obtain ⟨f', hf', hef'⟩ := (Ideal.mem_map_of_equiv e (e f)).mp hmem
      rwa [e.injective hef'] at hf'
  have hW₁T : W₁ ∈ T.support := hBT W₁ (by rw [hBU, h₁]; exact one_ne_zero)
  have hW₂T : W₂ ∈ T.support := hBT W₂ (by rw [hBU, h₂]; exact one_ne_zero)
  obtain ⟨a, b, ha0, hb0, hcop, ha, hb, hmon⟩ :=
    exists_coprime_mem_weightedMonomialIdeal_of_isLogDiscrepancy_eq_zero
    (sW := U.ι ≫ sX) inferInstance hsm hTred hTs (fun h => hne (by rw [h])) hW₁T hW₂T D_U
    inferInstance (by rw [hBU]; exact h₁) (by rw [hBU]; exact h₂) hBT hlogU (hc ▸ hcl')
    (hc ▸ hcoh') (hc ▸ hp₁') (hc ▸ hp₂') hxyU hxU hyU
  exact ⟨a, b, ha0, hb0, hcop, hvx.trans ha, hvy.trans hb,
    fun f hf M hfM => hback ![a, b] M (fun f' hf' hf'M => hmon f' hf' M hf'M) f hf hfM⟩

/-- **The orders of the lc place at the crossing are coprime.** In the situation of
`exists_stalk_eq_smul_formPow_dlog_of_isExceptional`, for local equations `x, y` of the two
coefficient-one curves through the centre `p` of `D`, `v_D(x)` and `v_D(y)` are coprime. Moreover
`v_D` is monomial of weights `(a, b)` in `x, y`: an element of `𝒪_p` of valuation `exp(-M)` lies in
the weighted monomial ideal of degree `M`. -/
theorem exists_coprime_mem_weightedMonomialIdeal_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      D.valuation (algebraMap _ (X j).functionField x) = WithZero.exp (-(a : ℤ)) ∧
      D.valuation (algebraMap _ (X j).functionField y) = WithZero.exp (-(b : ℤ)) ∧
      ∀ f : (X j).presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∀ M : ℕ,
        D.valuation (algebraMap _ (X j).functionField f) = WithZero.exp (-(M : ℤ)) →
        f ∈ weightedMonomialIdeal ![x, y] ![a, b] M := by
  have hPj := R.setting.isPair j
  haveI := hPj.isAlgClosed
  haveI := hPj.charZero
  have hXj := hPj.isPair.isNormalVariety
  have hd : topologicalKrullDim (X j) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq j
  obtain ⟨Z, hs, hsnc, hZ⟩ :=
    exists_dltWitness_center_notMem_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv
  obtain ⟨n, D', hv', hn⟩ :=
    hasLogDiscrepancy_valuation_eq_zero_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv
  have hpt := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXj hv'
  have hcl := DivisorOver.isClosed_singleton_of_isExceptional hXj hd D hD
  have hcoh := DivisorOver.coheight_eq_two_of_isExceptional hXj hd D hD
  rw [← hpt] at hZ hcl hcoh hp₁ hp₂
  obtain ⟨x', y', hxy', hx', hy', hxx, hyy, hback⟩ : ∃ x' y' :
      (X j).presheaf.stalk (D'.f D'.E.genericPoint),
      MMP.Mori.IsRegularSystemOfParameters ![x', y'] ∧
      IdealSheafData.stalk Q₁.idealSheaf (D'.f D'.E.genericPoint) = Ideal.span {x'} ∧
      IdealSheafData.stalk Q₂.idealSheaf (D'.f D'.E.genericPoint) = Ideal.span {y'} ∧
      D.valuation (algebraMap _ (X j).functionField x') =
        D.valuation (algebraMap _ (X j).functionField x) ∧
      D.valuation (algebraMap _ (X j).functionField y') =
        D.valuation (algebraMap _ (X j).functionField y) ∧
      (∀ α : Fin 2 → ℕ, (∀ f' : (X j).presheaf.stalk (D'.f D'.E.genericPoint), f' ≠ 0 →
          ∀ M : ℕ, D'.valuation (algebraMap _ (X j).functionField f') = WithZero.exp (-(M : ℤ)) →
          f' ∈ weightedMonomialIdeal ![x', y'] α M) →
        ∀ f : (X j).presheaf.stalk (D.f D.E.genericPoint), f ≠ 0 → ∀ M : ℕ,
          D.valuation (algebraMap _ (X j).functionField f) = WithZero.exp (-(M : ℤ)) →
          f ∈ weightedMonomialIdeal ![x, y] α M) := by
    rw [hpt]
    exact ⟨x, y, hxy, hx, hy, rfl, rfl, fun α h f hf M hfM => h f hf M (by rw [hv']; exact hfM)⟩
  obtain ⟨a, b, ha0, hb0, hcop, ha, hb, hmon⟩ :=
    exists_coprime_mem_weightedMonomialIdeal_of_isSNC_restrict hPj.isPair Z
    hs hsnc D' hn hZ hcl hcoh hne h₁ h₂ hp₁ hp₂ hxy' hx' hy'
  rw [hv'] at ha hb
  exact ⟨a, b, ha0, hb0, hcop, hxx.symm.trans ha, hyy.symm.trans hb, hback ![a, b] hmon⟩

/-- **The orders of the lc place at the crossing are coprime.** In the situation of
`exists_stalk_eq_smul_formPow_dlog_of_isExceptional`, for local equations `x, y` of the two
coefficient-one curves through the centre `p` of `D`, `v_D(x)` and `v_D(y)` are coprime. -/
theorem exists_mul_add_mul_eq_one_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) :
    ∃ a b c d : ℤ, D.valuation (algebraMap _ (X j).functionField x) = WithZero.exp (-a) ∧
      D.valuation (algebraMap _ (X j).functionField y) = WithZero.exp (-b) ∧
        a * c + b * d = 1 := by
  obtain ⟨a, b, -, -, hcop, ha, hb, -⟩ :=
    exists_coprime_mem_weightedMonomialIdeal_of_isExceptional R σ hσ h hι P hP D hDv hD hne h₁ h₂
      hp₁ hp₂ hxy hx hy
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  exact ⟨a, b, u, v, ha, hb, by linarith⟩

open exteriorPower in
/-- **The line of residues along an exceptional floor curve.** In the situation of
`exists_stalk_eq_smul_formPow_dlog_of_isExceptional`, let `x, y` be local equations at the
centre `p` of `D` of the two coefficient-one curves through `p`, with `a = ord_P(σ x)`,
`b = ord_P(σ y)`. Then `z = σ(y)^a σ(x)^{-b}` is a unit along `P`, and the residue along `P` of
every section of `m(K_{X_i} + B_i)` is a constant multiple of `(dz̄/z̄)^{⊗m}`: the section is
`σ^*` of a section of `m(K_{X_j} + B_j)`, which is `g (dx/x ∧ dy/y)^{⊗m}` near `p`. -/
theorem exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    letI := functionFieldAlgebra (sX j)
    letI := functionFieldAlgebra (sX i)
    letI := functionFieldAlgebra (ι ≫ sX i)
    ∃ Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j), Q₁ ≠ Q₂ ∧ (B j).coeff Q₁ = 1 ∧ (B j).coeff Q₂ = 1 ∧
      D.f D.E.genericPoint ∈ Q₁.support ∧ D.f D.E.genericPoint ∈ Q₂.support ∧
      ∃ x y : (X j).presheaf.stalk (D.f D.E.genericPoint),
        MMP.Mori.IsRegularSystemOfParameters ![x, y] ∧
        IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x} ∧
        IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y} ∧
      ∃ a b : ℤ,
      (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField x)) (ι (genericPoint T)) = a ∧
      (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField y)) (ι (genericPoint T)) = b ∧
      (∃ c d : ℤ, a * c + b * d = 1) ∧
      ∃ z : (X i).presheaf.stalk (ι (genericPoint T)), IsUnit z ∧
        algebraMap _ (X i).functionField z =
          (σ.toHom) (algebraMap _ (X j).functionField y) ^ a *
            (σ.toHom) (algebraMap _ (X j).functionField x) ^ (-b) ∧
        ∀ w ∈ logPluricanonicalSections (sX i) 2 m (B i), ∃ e : k,
          IsPoincareResidue (sX i) ι 1 m w
            (e • (show RationalPluriForms (ι ≫ sX i) 1 m from formPow (ιMulti T.functionField 1
              ![((ι.stalkMap (genericPoint T)).hom z)⁻¹ •
                KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom z)])
              m)) := by
  have hPj := R.setting.isPair j
  have hPi := R.setting.isPair i
  haveI := hPj.isAlgClosed
  haveI := hPj.charZero
  have hXj := hPj.isPair.isNormalVariety
  have hXi := hPi.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX i) := hXi.1.toLocallyOfFiniteType
  have hdj : topologicalKrullDim (X j) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq j
  have hdi : topologicalKrullDim (X i) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq i
  obtain ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, x, y, hxy, hx, hy, -, h0, hsec⟩ :=
    exists_stalk_eq_smul_formPow_dlog_of_isExceptional R σ hσ h hι P hP D hDv hD
  obtain ⟨a, b, c, d, ha, hb, habcd⟩ := exists_mul_add_mul_eq_one_of_isExceptional R σ hσ h hι P
    hP D hDv hD hne h₁ h₂ hp₁ hp₂ hxy hx hy
  letI := functionFieldAlgebra (sX j)
  letI := functionFieldAlgebra (sX i)
  obtain ⟨hx0, hy0, h0'⟩ := ne_zero_and_ιMulti_dlog_ne_zero_of_topFormsMap_ne_zero _ h0
  have hord : ∀ {f : (X j).functionField} {a : ℤ}, f ≠ 0 → D.valuation f = WithZero.exp (-a) →
      (X i).ord ((σ.toHom) f) (ι (genericPoint T)) = a := by
    intro f a hf hfa
    have hσf : (σ.toHom) f ≠ 0 := (map_ne_zero _).mpr hf
    rw [hDv, P.divisorialValuation_eq_exp_neg_ord hσf, WithZero.exp_inj, neg_inj] at hfa
    rw [hP]
    exact hfa
  have hc := DivisorOver.isClosed_singleton_of_isExceptional hXj hdj D hD
  obtain ⟨z, hz, hzv, hres⟩ := isPoincareResidue_pluriformPullback_smul_formPow_dlog hdi hdj P hP
    σ D hDv hc h0' hx0 hy0 (hord hx0 ha) (hord hy0 hb) habcd m
  refine ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, x, y, hxy, hx, hy, a, b, hord hx0 ha, hord hy0 hb,
    ⟨c, d, habcd⟩, z, hz, hzv, fun w hw => ?_⟩
  obtain ⟨d', K, hK, hmK⟩ := R.setting.isCartierDivisor i (.refl h)
  rw [Category.id_comp] at hK
  have hd' : d' = 2 := by
    have := hK.topologicalKrullDim_eq.symm.trans hdi
    exact_mod_cast this
  subst hd'
  have hτ := pluriformPullback_mem_logPluricanonicalSections_of_isCrepantBirationalMap hPj.isPair
    hdj hXi hK R.setting.pos hmK hσ.symm hw
  obtain ⟨g, hg⟩ := hsec m _ hτ
  obtain ⟨e, he⟩ := hres g
  refine ⟨e, ?_⟩
  have hcomp : (σ.toHom).comp (FunctionFieldEquiv.toHom (sX j) (sX i) σ.symm) =
      (1 : FunctionFieldEquiv (sX i) (sX i)).toHom :=
    AlgHom.ext σ.apply_symm_apply
  rwa [← hg, pluriformPullback_comp hdi hdj hdi, hcomp, pluriformPullback_one hdi] at he

/-- **Adjunction to a curve contracted where `K + B` is trivial.** Let `W` be a smooth variety of
dimension `n + 1`, `Y ⊆ W` a smooth prime divisor `P_t`, and `q : W ⟶ X'` a morphism to a normal
scheme carrying `Y` off the support of a `ℚ`-Cartier divisor `M`. If `q^*M = div σ + Θ` with
`Θ(P_t) = 1`, then `σ` has a simple pole along `P_t`, its residue `η` on `Y` is nonzero, and
`(Θ - P_t)|_Y = -div η`: the restriction of `q^*M` to `Y` vanishes. -/
theorem coeff_eq_neg_ordForm_of_isPullback_of_map_notMem_supp {k : Type} [Field k]
    {W Y X' : Scheme.{0}} (sW : W ⟶ Spec (.of k)) [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] [LocallyOfFiniteType sW] (hW : AlgebraicGeometry.IsVariety k sW)
    (hsmW : IsSmoothScheme sW) {n : ℕ} (hdim : topologicalKrullDim W = n + 1) (jW : Y ⟶ W)
    [IsClosedImmersion jW] [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    [LocallyOfFiniteType (jW ≫ sW)] (hYsm : IsSmoothScheme (jW ≫ sW))
    (Pt : MMP.Mori.PrimeDivisor W) (hjWP : jW (genericPoint Y) = Pt.genericPoint)
    (hPtr : Set.range jW.base = (Pt.support : Set W)) [IsLocallyNoetherian X'] [IsNormal X']
    (q : W ⟶ X') {M : QDivisor X'} (hMq : M.IsQCartier) (hYM : ∀ y : Y, q (jW y) ∉ M.supp)
    (σW : RationalPluriForms sW (n + 1) 1) {Θ : QDivisor W} (hΘ : Θ.coeff Pt = 1)
    {hB : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ M.supp}
    (hN : M.IsPullback q hB (Divisor.toQDivisor (divisorOfForm σW) + Θ)) {Rd : QDivisor Y}
    {hg : ∀ Z : irreducibleComponents Y,
      jW (componentGenericPoint Y Z) ∉ (Θ - Finsupp.single Pt 1).supp}
    (hRd : (Θ - Finsupp.single Pt 1).IsPullback jW hg Rd) :
    Pt.ordForm σW = -1 ∧ ∃ η : RationalPluriForms (jW ≫ sW) n 1,
      (∀ η', IsPoincareResidue sW jW n 1 σW η' ↔ η' = η) ∧ η ≠ 0 ∧
        ∀ Qt : MMP.Mori.PrimeDivisor Y, Rd.coeff Qt = -(Qt.ordForm η : ℚ) := by
  haveI : LocallyOfFinitePresentation sW :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sW)).mpr inferInstance
  haveI : Smooth sW := (isSmoothScheme_iff _).mp hsmW
  haveI : LocallyOfFinitePresentation (jW ≫ sW) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := jW ≫ sW)).mpr inferInstance
  haveI : Smooth (jW ≫ sW) := (isSmoothScheme_iff _).mp hYsm
  set N := Divisor.toQDivisor (divisorOfForm σW) + Θ with hNdef
  have hNPt : N.coeff Pt = 0 :=
    qdivisor_coeff_eq_zero_of_isPullback hMq hN Pt (by rw [← hjWP]; exact hYM _)
  have hσWP : Pt.ordForm σW = -1 := by
    have h1 := hNPt
    rw [hNdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      hΘ] at h1
    have h2 : ((Pt.ordForm σW : ℤ) : ℚ) = ((-1 : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h2
  have hσW0 : σW ≠ 0 := fun h => by
    rw [h, MMP.Mori.PrimeDivisor.ordForm_zero] at hσWP
    exact absurd hσWP (by decide)
  obtain ⟨η, hηiff, hη0, -, -⟩ := MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one
    sW hdim jW Pt hjWP σW hσW0 hσWP
  have hη := (hηiff η).mpr rfl
  obtain ⟨-, -, hadj⟩ := MMP.Fourfold.isPullback_divisorOfForm_add_of_isPoincareResidue
    sW hW hdim jW Pt hPtr σW hσW0 hσWP η hη
  have hNgen : ∀ Z' : irreducibleComponents Y, jW (componentGenericPoint _ Z') ∉ N.supp := by
    intro Z'
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjWP]
    exact MMP.CyclicChartDifferent.genericPoint_notMem_supp_of_coeff_eq_zero hNPt
  obtain ⟨R', ⟨hgR', hR'⟩, hNR'⟩ :=
    hadj N Θ (MMP.Fourfold.isQCartier_of_isSmoothScheme hsmW N) hNgen rfl
  have hRR : R' = Rd :=
    ((MMP.Fourfold.isQCartier_of_isSmoothScheme hsmW _).existsUnique_isPullback hg).unique hR' hRd
  subst hRR
  have hcomp := MMP.Mori.QDivisor.IsPullback.comp hN hNR' (fun Z' => by
    rw [Scheme.Hom.comp_apply]; exact hYM _)
  refine ⟨hσWP, η, hηiff, hη0, fun Qt => ?_⟩
  have h0 := qdivisor_coeff_eq_zero_of_isPullback hMq hcomp Qt (by
    rw [Scheme.Hom.comp_apply]; exact hYM _)
  rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm] at h0
  linarith

open MMP.Fold06.LemMmpStratumDiscrepancyNondecreasing exteriorPower in
/-- **Floor points of a curve pair read on a smooth model.** Let `(T, B_T)` be a pair on a proper
normal curve, `p_V : Y ⟶ T` a proper birational morphism from a smooth proper curve, and `R` the
crepant boundary of `(T, B_T)` on `Y`. If `R = -div(dζ/ζ)` for the pull-back `ζ = p_V^* z` of a
rational function `z` on `T`, and `dζ/ζ ≠ 0`, then `B_T(q) = 1` at every zero or pole `q` of `z`,
`B_T(q) ≤ 0` at every other point, and `z` has a zero or a pole. -/
theorem coeff_eq_one_of_ord_ne_zero_of_coeff_eq_neg_ordForm_dlog {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {T Y : Scheme.{0}} {sT : T ⟶ Spec (.of k)} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    [UniversallyClosed sT] (hTv : IsNormalVariety k sT) (hdT : topologicalKrullDim T = 1)
    {BT : QDivisor T} (hTp : MMP.Mori.IsPair sT BT) (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hYv : IsNormalVariety k sY)
    (hYsm : IsSmoothScheme sY) (hYp : IsProper sY) (hdY : topologicalKrullDim Y = 1)
    (pV : Y ⟶ T) [IsProper pV] [IsDominant pV] [LocallyOfFiniteType (pV ≫ sT)]
    (hYv' : IsNormalVariety k (pV ≫ sT)) (hpV : IsBirationalMorphism pV) {Rd : QDivisor Y}
    (hcrR : ∀ (d : ℕ) (K : Divisor T), K.IsCanonicalDivisor sT d →
      IsCrepantBoundary sT d K BT pV hYv' hpV Rd)
    {z : T.functionField} (hz0 : z ≠ 0) {ζ : Y.functionField} (hζ : functionFieldMap pV z = ζ)
    (hRd : letI := functionFieldAlgebra sY
      ∀ Qt : MMP.Mori.PrimeDivisor Y, Rd.coeff Qt = -(Qt.ordForm
        (show RationalPluriForms sY 1 (1 : ℕ) from formPow (ιMulti Y.functionField 1
          ![ζ⁻¹ • KaehlerDifferential.D k Y.functionField ζ]) 1) : ℚ))
    (hη0 : letI := functionFieldAlgebra sY
      (show RationalPluriForms sY 1 (1 : ℕ) from formPow (ιMulti Y.functionField 1
          ![ζ⁻¹ • KaehlerDifferential.D k Y.functionField ζ]) 1) ≠ 0) :
    (∀ Q : MMP.Mori.PrimeDivisor T, (T.ord z Q.genericPoint ≠ 0 → BT.coeff Q = 1) ∧
      (T.ord z Q.genericPoint = 0 → BT.coeff Q ≤ 0)) ∧
      ∃ Q : MMP.Mori.PrimeDivisor T, T.ord z Q.genericPoint ≠ 0 := by
  classical
  letI := functionFieldAlgebra sY
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : PerfectField k := PerfectField.ofCharZero
  have hd1 : topologicalKrullDim Y = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdY
  have hζ0 : ζ ≠ 0 := by rw [← hζ]; exact (map_ne_zero _).mpr hz0
  -- every point of `T` is matched with a point of `Y`
  have hQt : ∀ Q : MMP.Mori.PrimeDivisor T, ∃ Qt : MMP.Mori.PrimeDivisor Y,
      Rd.coeff Qt = BT.coeff Q ∧ Y.ord ζ Qt.genericPoint = T.ord z Q.genericPoint := by
    intro Q
    obtain ⟨y₁, hy₁, hQb, hcoh₁⟩ := exists_map_eq_genericPoint_of_isBirationalMorphism pV hpV Q
    set Qt : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y₁ hcoh₁
    have hQtg : Qt.genericPoint = y₁ :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y₁ hcoh₁
    have hQtQ : pV Qt.genericPoint = Q.genericPoint := by rw [hQtg, hy₁]
    haveI : IsIso (pV.stalkMap Qt.genericPoint) :=
      MMP.isIso_stalkMap_of_mem_biregularLocus pV (by rw [hQtQ]; exact hQb)
    refine ⟨Qt, coeff_eq_coeff_of_isCrepantBoundary hTp pV hYv' hpV hcrR Qt Q hQtQ, ?_⟩
    have h1 := valuation_eq_ofPrimeDivisor_of_mem_biregularLocus hTv ⟨Y, pV, hYv', hpV, Qt⟩ Q
      hQtQ hQb
    have h2 := congrArg
      (fun v : Valuation T.functionField (WithZero (Multiplicative ℤ)) => v z) h1
    change Qt.divisorialValuation (functionFieldMap pV z) =
      Q.divisorialValuation (functionFieldMap (𝟙 T) z) at h2
    rw [functionFieldMap_id_apply, hζ, Qt.divisorialValuation_eq_exp_neg_ord hζ0,
      Q.divisorialValuation_eq_exp_neg_ord hz0, WithZero.exp_inj, neg_inj] at h2
    exact h2
  -- `dζ/ζ = ζ⁻¹ dζ`
  set ω : RationalPluriForms sY 1 (1 : ℕ) := PiTensorProduct.tprod Y.functionField
    fun _ : Fin 1 => ιMulti Y.functionField 1 fun _ => KaehlerDifferential.D k Y.functionField ζ
    with hωdef
  have hdl : (show RationalPluriForms sY 1 (1 : ℕ) from formPow (ιMulti Y.functionField 1
      ![ζ⁻¹ • KaehlerDifferential.D k Y.functionField ζ]) 1) = ζ⁻¹ • ω := by
    change formPow _ 1 = _
    rw [ιMulti_one_smul, formPow_smul, pow_one]
    congr 1
  have hω0 : ω ≠ 0 := by
    intro h0
    apply hη0
    rw [hdl, h0, smul_zero]
  have hcoef : ∀ (Q : MMP.Mori.PrimeDivisor T) (Qt : MMP.Mori.PrimeDivisor Y),
      Rd.coeff Qt = BT.coeff Q → Y.ord ζ Qt.genericPoint = T.ord z Q.genericPoint →
      (T.ord z Q.genericPoint ≠ 0 → BT.coeff Q = 1) ∧
        (T.ord z Q.genericPoint = 0 → BT.coeff Q ≤ 0) := by
    intro Q Qt hc ho
    refine ⟨fun hne => ?_, fun he => ?_⟩
    · have h1 := ordForm_formPow_dlog_eq_neg_one_of_ord_ne_zero hYv hdY Qt hζ0
        (by rw [ho]; exact hne)
      rw [← hc, hRd Qt, h1]
      norm_num
    · have h1 : 0 ≤ Qt.ordForm ω :=
        Flips.zero_le_ordForm_d hYv hdY Qt ζ (by rw [ho, he]) ω rfl hω0
      have h2 := hRd Qt
      rw [hdl, Qt.ordForm_smul_of_topologicalKrullDim_eq hd1 (inv_ne_zero hζ0) hω0,
        ← zpow_neg_one, ord_zpow _ hζ0, ho, he] at h2
      rw [← hc, h2]
      have h3 : (0 : ℚ) ≤ (Qt.ordForm ω : ℚ) := by exact_mod_cast h1
      push_cast
      linarith
  refine ⟨fun Q => ?_, ?_⟩
  · obtain ⟨Qt, hc, ho⟩ := hQt Q
    exact hcoef Q Qt hc ho
  -- `ζ` is not constant, so it has a zero or a pole on `Y`
  have hk : ∀ c : k, ζ ≠ algebraMap k Y.functionField c := by
    intro c hc
    apply hω0
    rw [hωdef, hc, Derivation.map_algebraMap]
    exact (PiTensorProduct.tprod _).map_coord_zero (0 : Fin 1)
      ((ιMulti Y.functionField 1).map_coord_zero 0 rfl)
  obtain ⟨Qt₀, hQt₀⟩ := exists_ord_ne_zero_of_forall_ne_algebraMap hYv hYsm hYp hdY hζ0 hk
  letI := functionFieldAlgebra sT
  letI := functionFieldAlgebra (pV ≫ sT)
  letI := functionFieldMapAlgebra pV
  haveI := isScalarTower_functionFieldMap sT pV
  let e : FunctionFieldEquiv (pV ≫ sT) sT := AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom k T.functionField Y.functionField) hpV.functionFieldMap_bijective
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_ord_eq_of_curve hdT e Qt₀
  refine ⟨Q, ?_⟩
  have he : (e.toHom) z = ζ := hζ
  rwa [← hQ z hz0, he]

open MMP.Fold06.LemMmpStratumDiscrepancyNondecreasing exteriorPower TopologicalSpace in
/-- **The different along an exceptional floor curve.** In the situation of
`exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional`, `(T, B_T)` is a pair, a
point `q ∈ T` has coefficient one in `B_T` exactly when `z̄` has a zero or a pole at `q` (and
coefficient at most zero otherwise), and such points exist. On a common log
resolution `p : W ⟶ X_i`, `q : W ⟶ X_j` of `σ`, the strict transform `Y` of `P` is contracted by
`q` to the centre `x_j` of `D`; the pull-back of `K_{X_j} + B_j = div(dx/x ∧ dy/y) + B_j`, which
vanishes near `x_j`, restricts to zero on `Y`, so adjunction along `Y` makes the crepant boundary
of `(T, B_T)` on `Y` the divisor `-div(dz̄/z̄)` of the residue. So the points of coefficient one
in `B_T` are exactly the zeros and poles of `z̄`, and the others have coefficient at most zero;
`z̄` is not constant (its logarithmic differential, the residue of a form with a simple pole along
the smooth curve `Y`, is nonzero), so it has a zero or a pole on the smooth proper curve `Y`. -/
theorem coeff_eq_one_iff_ord_ne_zero_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I}
    (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) {a b : ℤ}
    (ha : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField x)) (ι (genericPoint T)) = a)
    (hb : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField y)) (ι (genericPoint T)) = b)
    {z : (X i).presheaf.stalk (ι (genericPoint T))} (hz : IsUnit z)
    (hzv : algebraMap _ (X i).functionField z =
      (σ.toHom) (algebraMap _ (X j).functionField y) ^ a *
        (σ.toHom) (algebraMap _ (X j).functionField x) ^ (-b)) :
    haveI : IsLocallyNoetherian T :=
      (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    haveI : IsNormal T := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
    MMP.Mori.IsPair (ι ≫ sX i) BT ∧
      (∀ Q : MMP.Mori.PrimeDivisor T,
        (T.ord ((ι.stalkMap (genericPoint T)).hom z) Q.genericPoint ≠ 0 → BT.coeff Q = 1) ∧
        (T.ord ((ι.stalkMap (genericPoint T)).hom z) Q.genericPoint = 0 → BT.coeff Q ≤ 0)) ∧
      ∃ Q : MMP.Mori.PrimeDivisor T,
        T.ord ((ι.stalkMap (genericPoint T)).hom z) Q.genericPoint ≠ 0 := by
  set F1 := StratumAdjunctionData.step (.refl h) ι BT hι
  haveI := F1.isLocallyNoetherian_stratum
  haveI := F1.isNormal_stratum
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  haveI : PerfectField k := PerfectField.ofCharZero
  have hXi : IsNormalVariety k (sX i) := hPi.isPair.isNormalVariety
  have hXj : IsNormalVariety k (sX j) := hPj.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX i) := hXi.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  have hXip := (R.setting.isProjectiveVariety i).isProjective
  have hXjp := (R.setting.isProjectiveVariety j).isProjective
  haveI : IsProper (sX i) := isProper_of_isProjectiveMorphism (sX i) hXip
  haveI : IsProper (sX j) := isProper_of_isProjectiveMorphism (sX j) hXjp
  haveI : CompactSpace (X i) := QuasiCompact.compactSpace_of_compactSpace (sX i)
  haveI : CompactSpace (X j) := QuasiCompact.compactSpace_of_compactSpace (sX j)
  have hι0 := hι
  rw [Category.id_comp] at hι0
  obtain ⟨hTv, P₀, hP₀1, hP₀r, hιci, -, -, -, -, -, -, -, -, hTc, hTlft, -⟩ := id hι0
  haveI := hιci
  haveI := hTc
  haveI := hTlft
  obtain rfl : P = P₀ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hP.symm.trans (MMP.CyclicChartDifferent.Aux.map_genericPoint_eq ι P₀ hP₀r))
  have hdi : topologicalKrullDim (X i) = ((1 : ℕ) : WithBot ℕ∞) + 1 := by
    rw [R.setting.topologicalKrullDim_eq i]; norm_num
  have hdj : topologicalKrullDim (X j) = ((1 : ℕ) : WithBot ℕ∞) + 1 := by
    rw [R.setting.topologicalKrullDim_eq j]; norm_num
  have hdj2 : topologicalKrullDim (X j) = 2 := by
    exact_mod_cast R.setting.topologicalKrullDim_eq j
  have hBi : MMP.Flips.IsBoundary (MMP.Mori.QDivisor.toRDivisor (B i)) := fun E => by
    rw [MMP.Mori.QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast hPi.nonneg E, by exact_mod_cast (R.setting.isDltPair i).2.1 E⟩
  have hBj : MMP.Flips.IsBoundary (MMP.Mori.QDivisor.toRDivisor (B j)) := fun E => by
    rw [MMP.Mori.QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast hPj.nonneg E, by exact_mod_cast (R.setting.isDltPair j).2.1 E⟩
  /- Step 1: the birational map `X_i ⇢ X_j` with pull-back `σ`, and a common log resolution. -/
  obtain ⟨U, _, j₁, j₂, _, _, _, _, hj₁₂, hσj⟩ :=
    exists_isOpenImmersion_functionFieldMap_eq_of_functionFieldEquiv σ
  let φ : (X i).PartialIso (X j) :=
    { source := j₁.opensRange
      dense_source := j₁.opensRange.isOpen.dense ⟨_, ⟨genericPoint U, rfl⟩⟩
      target := j₂.opensRange
      dense_target := j₂.opensRange.isOpen.dense ⟨_, ⟨genericPoint U, rfl⟩⟩
      iso := j₁.isoOpensRange.symm ≪≫ j₂.isoOpensRange }
  have hφι : φ.iso.hom ≫ φ.target.ι = j₁.isoOpensRange.inv ≫ j₂ := by
    change (j₁.isoOpensRange.inv ≫ j₂.isoOpensRange.hom) ≫ j₂.opensRange.ι = _
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have hsrc : j₁.isoOpensRange.inv ≫ j₁ = φ.source.ι :=
    (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι j₁).symm
  have hφ : φ.IsOver (sX i) (sX j) := by
    change φ.iso.hom ≫ φ.target.ι ≫ sX j = φ.source.ι ≫ sX i
    rw [← Category.assoc, hφι, Category.assoc, hj₁₂, ← Category.assoc, hsrc]
  have hbot : ∀ (Z : Scheme.{0}), IsEmpty (⊥ : Z.Opens).toScheme :=
    fun Z => ⟨fun x => by simpa using x.2⟩
  have hsm0 : ∀ (Z : Scheme.{0}) (s : Z ⟶ Spec (.of k)), IsSmoothScheme ((⊥ : Z.Opens).ι ≫ s) := by
    intro Z s
    haveI := hbot Z
    change smoothLocus _ = ⊤
    ext x
    exact isEmptyElim x
  have hsnc0 : ∀ (Z : Scheme.{0}) (s : Z ⟶ Spec (.of k)) (S : Closeds (⊥ : Z.Opens).toScheme),
      IsSNCSubset ((⊥ : Z.Opens).ι ≫ s) S := by
    intro Z s S
    haveI := hbot Z
    exact Or.inl (Closeds.ext (Set.ext isEmptyElim))
  obtain ⟨W, p, q, hpres, -, hqres, -, hcompat, -, -⟩ :=
    MMP.Flips.exists_isLogResolution_isIso_restrict_of_partialIso (sX i) (sX j) hXi hXj hXip hXjp
      (B i) (B j) hBi hBj φ hφ ⊥ ⊥ bot_le bot_le (by simp) (hsm0 _ _) (hsnc0 _ _ _)
      (hsnc0 _ _ _) (hsnc0 _ _ _)
  obtain ⟨-, hvarW, hsmW, hpP, hp, G, -, hGiff, hGsnc⟩ := hpres
  obtain ⟨-, hvarW', hsmW', hqP, hq, -⟩ := hqres
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hvarW.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX i) := hvarW.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX j) := hvarW'.toLocallyOfFiniteType
  obtain ⟨hWln, hWn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsmW
  haveI := hWln
  haveI := hWn
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX i)
  have hWv : IsNormalVariety k (p ≫ sX i) := ⟨hvarW, hWn⟩
  have hWv' : IsNormalVariety k (q ≫ sX j) := ⟨hvarW', hWn⟩
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  /- Step 2: `q^* = p^* ∘ σ` on function fields, and `p ≫ s_{X_i} = q ≫ s_{X_j}`. -/
  set A := p ⁻¹ᵁ φ.source with hAdef
  have hηA : genericPoint W ∈ A := by
    change p (genericPoint W) ∈ φ.source
    rw [MMP.Positivity.map_genericPoint_eq_of_isDominant p]
    obtain ⟨x, hx⟩ := φ.dense_source.nonempty
    exact ((genericPoint_spec (X i)).mem_open_set_iff φ.source.isOpen).mpr
      ⟨x, Set.mem_univ _, hx⟩
  haveI : Nonempty A := ⟨⟨_, hηA⟩⟩
  haveI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  haveI : IsDominant A.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion A.ι
  set bA := (p ∣_ φ.source) ≫ j₁.isoOpensRange.inv with hbA
  have hb₁ : bA ≫ j₁ = A.ι ≫ p := by
    rw [hbA, Category.assoc, hsrc, morphismRestrict_ι]
  have hb₂ : bA ≫ j₂ = A.ι ≫ q := by
    rw [hbA, Category.assoc, ← hφι, ← hcompat]
  haveI : IsDominant (bA ≫ j₁) := by rw [hb₁]; infer_instance
  haveI : IsDominant bA := IsDominant.of_comp_of_isOpenImmersion bA j₁
  have hfq : ∀ g, functionFieldMap q g = functionFieldMap p ((σ.toHom) g) := by
    intro g
    apply (functionFieldMap A.ι).injective
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      ← MMP.Positivity.DivisorOver.functionFieldMap_congr hb₂,
      ← MMP.Positivity.DivisorOver.functionFieldMap_congr hb₁,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply bA j₂,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply bA j₁, hσj]
  have hpq : p ≫ sX i = q ≫ sX j := by
    refine ext_of_isDominant A.ι ?_
    calc A.ι ≫ p ≫ sX i = (bA ≫ j₁) ≫ sX i := by rw [hb₁, Category.assoc]
      _ = (bA ≫ j₂) ≫ sX j := by simp only [Category.assoc, hj₁₂]
      _ = A.ι ≫ q ≫ sX j := by rw [hb₂, Category.assoc]
  /- Step 3: the crepant boundaries of `(X_i, B_i)` and `(X_j, B_j)` on `W` coincide. -/
  obtain ⟨-, n, K₀, hK₀, -⟩ := id hPi.isPair
  obtain ⟨-, n', K₀', hK₀', -⟩ := id hPj.isPair
  obtain ⟨⟨Θ, hΘ, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPi.isPair hK₀ p hWv hp
  obtain ⟨⟨Θ', hΘ', -⟩, -⟩ :=
    MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPj.isPair hK₀' q hWv' hq
  have hcr : ∀ (d : ℕ) (K : Divisor (X i)), K.IsCanonicalDivisor (sX i) d →
      IsCrepantBoundary (sX i) d K (B i) p hWv hp Θ := by
    intro d K hK
    obtain rfl : d = n := by
      have h1 := hK.topologicalKrullDim_eq
      rw [hK₀.topologicalKrullDim_eq] at h1
      exact_mod_cast h1.symm
    exact fun F => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hΘ F)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sX i) hXi hK hK₀)
  have hcr' : ∀ (d : ℕ) (K : Divisor (X j)), K.IsCanonicalDivisor (sX j) d →
      IsCrepantBoundary (sX j) d K (B j) q hWv' hq Θ' := by
    intro d K hK
    obtain rfl : d = n' := by
      have h1 := hK.topologicalKrullDim_eq
      rw [hK₀'.topologicalKrullDim_eq] at h1
      exact_mod_cast h1.symm
    exact fun F => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hΘ' F)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sX j) hXj hK hK₀')
  have hΘΘ' : Θ = Θ' := by
    ext F
    have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΘ F)
      (show IsProper (⟨W, p, hWv, hp, F⟩ : DivisorOver k (sX i)).f from hpP)
    have h2 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΘ' F)
      (show IsProper (⟨W, q, hWv', hq, F⟩ : DivisorOver k (sX j)).f from hqP)
    obtain ⟨n'', D'', hD'', h3⟩ := (hσ _ _).mp ⟨n, _, rfl, h1⟩
    have hv : D''.valuation = (⟨W, q, hWv', hq, F⟩ : DivisorOver k (sX j)).valuation := by
      rw [hD'']
      ext g
      change F.divisorialValuation (functionFieldMap p ((σ.toHom) g)) =
        F.divisorialValuation (functionFieldMap q g)
      rw [hfq]
    have h4 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h3 h2 hv
    have h5 : ((Θ.coeff F : ℚ) : ℝ) = ((Θ'.coeff F : ℚ) : ℝ) := by
      push_cast at h4
      linarith
    have h6 : Θ.coeff F = Θ'.coeff F := by exact_mod_cast h5
    exact h6
  rw [← hΘΘ'] at hcr'
  /- Step 4: the strict transform `Pt` of `P` on `W` is contracted by `q` to the centre of `D`. -/
  obtain ⟨t, hpt, hPb, hcoh⟩ := exists_map_eq_genericPoint_of_isBirationalMorphism p hp P
  set Pt : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh
    with hPtdef
  have hPtg : Pt.genericPoint = t :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne t hcoh
  have hPtP : p Pt.genericPoint = P.genericPoint := by rw [hPtg, hpt]
  haveI : IsIso (p.stalkMap Pt.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus p (by rw [hPtP]; exact hPb)
  have hvq : (⟨W, q, hWv', hq, Pt⟩ : DivisorOver k (sX j)).valuation = D.valuation := by
    have h1 := valuation_eq_ofPrimeDivisor_of_mem_biregularLocus hXi ⟨W, p, hWv, hp, Pt⟩ P hPtP hPb
    ext g
    have h2 := congrArg
      (fun v : Valuation (X i).functionField (WithZero (Multiplicative ℤ)) => v ((σ.toHom) g)) h1
    change Pt.divisorialValuation (functionFieldMap p _) =
      P.divisorialValuation (functionFieldMap (𝟙 (X i)) _) at h2
    change Pt.divisorialValuation (functionFieldMap q g) = D.valuation g
    rw [functionFieldMap_id_apply] at h2
    rw [hfq, h2, hDv]
  have hqPt : q Pt.genericPoint = D.f D.E.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXj hvq
  /- Step 5: `Pt` is a component of the snc divisor of the log resolution, hence smooth. -/
  have hnotexc : Pt.genericPoint ∉ (MMP.Mori.exceptionalSet p : Set W) := fun hex =>
    (MMP.Mori.mem_exceptionalSet.mp hex) (by rw [hPtP]; exact hPb)
  have hGPt : G.coeff Pt = 1 := by
    refine (hGiff Pt).mpr (Or.inl ?_)
    refine (MMP.Flips.coeff_birationalInverseTransform_ne_zero_iff hXi _ hWv hp Pt hnotexc).mpr ?_
    rw [hPtP]
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, ?_, ?_⟩
    · rw [MMP.Mori.QDivisor.coeff_toRDivisor]
      have h0 : (B i).coeff P ≠ 0 := (by linarith : (0 : ℚ) < (B i).coeff P).ne'
      exact_mod_cast h0
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  have hGsnc' := MMP.Flips.IsSNCDivisor.isSNC hvarW hsmW hGsnc
  have hsnc1 : DivisorWithCoeffs.IsSNC (p ≫ sX i)
      (∑ G' ∈ ({Pt} : Finset (MMP.Mori.PrimeDivisor W)), Finsupp.single G' (1 : ℤ)) := by
    refine hGsnc'.of_support_subset fun G' hG' => ?_
    rw [Finset.sum_singleton, Finsupp.support_single_ne_zero _ one_ne_zero,
      Finset.mem_singleton] at hG'
    subst hG'
    rw [Finsupp.mem_support_iff]
    change G.coeff Pt ≠ 0
    rw [hGPt]
    exact one_ne_zero
  obtain ⟨-, hYsm, -⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC (p ≫ sX i) hsnc1
    (y := t) (fun G' hG' => by
      rw [Finset.mem_singleton.mp hG', ← hPtg, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
    (by rw [hcoh, Finset.card_singleton, Nat.cast_one])
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure t
  set Y := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subscheme with hYdef
  set jW := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subschemeι with hjWdef
  obtain ⟨hYln, hYn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYsm
  haveI := hYln
  haveI := hYn
  haveI : CompactSpace Y := jW.isClosedEmbedding.compactSpace
  have hYsm' : IsSmoothScheme (jW ≫ q ≫ sX j) := by rw [← hpq]; exact hYsm
  have hjg : jW (genericPoint Y) = t :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure t
  have hjWP : jW (genericPoint Y) = Pt.genericPoint := hjg.trans hPtg.symm
  have hPtr : Set.range jW = (Pt.support : Set W) := by
    rw [hjWdef, range_subschemeι_vanishingIdeal_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun x => closure {x}) hPtg.symm
  /- Step 6: the strict transform `Y ⟶ T`, and adjunction along `Y`. -/
  obtain ⟨pV, hsqV, hpVP, hpV⟩ := exists_strictTransform_of_isIso_stalkMap t p ι P hP₀r hpt
    (MMP.Positivity.DivisorOver.isIso_stalkMap_of_eq p hPtg.symm)
  haveI := hpVP
  haveI : IsDominant pV := hpV.isDominant
  have hsW : pV ≫ ι ≫ sX i = jW ≫ p ≫ sX i := by
    rw [← Category.assoc, hsqV, Category.assoc]
  haveI := hvarW
  have hYv : IsNormalVariety k (pV ≫ ι ≫ sX i) := ⟨by rw [hsW]; exact ⟨⟩, hYn⟩
  haveI : LocallyOfFiniteType (pV ≫ ι ≫ sX i) := hYv.1.toLocallyOfFiniteType
  obtain ⟨hTp, hΘPt, hg, Rd, hRd, hcrR⟩ :=
    isCrepantBoundary_sub_single_of_isAdjunctionStep hPi.isPair p hWv hp hsmW hcr ι hι0 P hP₀r
      hdi hT Nat.one_pos Pt hPtP jW hjWP hPtr hYsm pV hsqV hYv hpV
  /- Step 7: `ω = dx/x ∧ dy/y` on `X_j`; `K_{X_j} + B_j = div ω + B_j` vanishes near the
  centre `x_j` of `D`. -/
  letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
  letI := functionFieldAlgebra (sX j)
  haveI := isScalarTower_stalk_functionField (sX j) (D.f D.E.genericPoint)
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hxy
  obtain ⟨r, w, hr, -, hspan, h0⟩ := exists_stalk_topForms_generator (sX j) (n := 2)
    (by exact_mod_cast hdj2) (D.f D.E.genericPoint) hxy
  obtain rfl : r = 0 := by omega
  have hw : w = ![] := Subsingleton.elim _ _
  subst hw
  obtain ⟨hx0, hy0, h0'⟩ := ne_zero_and_ιMulti_dlog_ne_zero_of_topFormsMap_ne_zero _ h0
  have hdj2' : topologicalKrullDim (X j) = ((2 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdj2
  have hKω := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hXj hdj2' h0'
  obtain ⟨-, nj, Kj, hKj, hKjq⟩ := id hPj.isPair
  have hMq := hKjq.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sX j) hXj hKj hKω)
  obtain ⟨Q₁', Q₂', -, -, -, -, -, hQ'⟩ :=
    exists_ne_coeff_eq_one_of_isExceptional_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv hD
  have hQ : ∀ Γ : MMP.Mori.PrimeDivisor (X j), (B j).coeff Γ ≠ 0 →
      D.f D.E.genericPoint ∈ Γ.support → Γ = Q₁ ∨ Γ = Q₂ := by
    intro Γ hΓ hΓp
    have e1 := hQ' Q₁ (by rw [h₁]; exact one_ne_zero) hp₁
    have e2 := hQ' Q₂ (by rw [h₂]; exact one_ne_zero) hp₂
    rcases hQ' Γ hΓ hΓp with h3 | h3 <;> rcases e1 with h1' | h1' <;> rcases e2 with h2' | h2'
    all_goals first
      | exact absurd (h1'.trans h2'.symm) hne
      | exact Or.inl (h3.trans h1'.symm)
      | exact Or.inr (h3.trans h2'.symm)
  have hMp := notMem_supp_topFormDivisor_dlog_add (sX := sX j) _ hne h₁ h₂ hp₁ hp₂ hQ hx hy
    hspan h0
  have h0c := h0'
  generalize hωt : (ιMulti (X j).functionField 2
    ![(algebraMap _ (X j).functionField x)⁻¹ •
        KaehlerDifferential.D k (X j).functionField (algebraMap _ (X j).functionField x),
      (algebraMap _ (X j).functionField y)⁻¹ •
        KaehlerDifferential.D k (X j).functionField (algebraMap _ (X j).functionField y)] :
      RationalTopForms (sX j) 2) = ωt at h0' hKω hMq hMp
  /- Step 8: `q^*(K_{X_j} + B_j) = div(q^*ω) + Θ` restricts to zero on `Y`. -/
  have hNpb := (MMP.Mori.isCrepantBoundary_iff_isPullback_topFormDivisor_add (sX j) hPj.isPair
      hdj2' ωt h0' q hWv' hq Θ).mp (hcr' 2 _ hKω) (fun Z => by
        rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
          MMP.Positivity.map_genericPoint_eq_of_isDominant]
        exact MMP.Fourfold.genericPoint_notMem_supp _)
  have hc := DivisorOver.isClosed_singleton_of_isExceptional hXj hdj2 D hD
  have hYp : ∀ y : Y, q (jW y) = D.f D.E.genericPoint := by
    intro y
    have hy1 : jW y ∈ closure ({t} : Set W) := by
      rw [← range_subschemeι_vanishingIdeal_closure]; exact ⟨y, rfl⟩
    have h2 := (specializes_iff_mem_closure.mpr hy1).map q.base.hom.continuous
    have h3 : q t = D.f D.E.genericPoint := by rw [← hPtg]; exact hqPt
    rw [h3] at h2
    exact h2.mem_closed hc rfl
  have hdW : topologicalKrullDim W = ((1 : ℕ) : WithBot ℕ∞) + 1 := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (q ≫ sX j),
      ← MMP.Mori.trdeg_functionField_eq_of_bijective (sX j) q hq.functionFieldMap_bijective,
      MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX j) hdj2']
    norm_cast
  obtain ⟨-, η, hηiff, hη0, hRdη⟩ := coeff_eq_neg_ordForm_of_isPullback_of_map_notMem_supp
    (q ≫ sX j) hvarW' hsmW' hdW jW hYsm' Pt hjWP hPtr q hMq (fun y => by rw [hYp]; exact hMp)
    _ hΘPt hNpb hRd
  /- Step 9: the residue `η` is `dζ/ζ`, `ζ` the restriction of `q^*(y^a x^{-b})` to `Y`. -/
  obtain ⟨a', b', c, d, ha', hb', habcd⟩ := exists_mul_add_mul_eq_one_of_isExceptional R σ hσ h hι
    P hP D hDv hD hne h₁ h₂ hp₁ hp₂ hxy hx hy
  have hordD : ∀ {f : (X j).functionField} {e : ℤ}, f ≠ 0 → D.valuation f = WithZero.exp (-e) →
      (X i).ord ((σ.toHom) f) (ι (genericPoint T)) = e ∧
        W.ord (functionFieldMap q f) (jW (genericPoint Y)) = e := by
    intro f e hf hfe
    have hσf : (σ.toHom) f ≠ 0 := (map_ne_zero _).mpr hf
    have hqf : functionFieldMap q f ≠ 0 := (map_ne_zero _).mpr hf
    have h1 : Pt.divisorialValuation (functionFieldMap q f) = D.valuation f :=
      congrArg (fun v : Valuation (X j).functionField (WithZero (Multiplicative ℤ)) => v f) hvq
    refine ⟨?_, ?_⟩
    · rw [hDv, P.divisorialValuation_eq_exp_neg_ord hσf, WithZero.exp_inj, neg_inj] at hfe
      rw [hP]
      exact hfe
    · rw [hfe, Pt.divisorialValuation_eq_exp_neg_ord hqf, WithZero.exp_inj, neg_inj] at h1
      rw [hjWP]
      exact h1
  obtain ⟨hia, hWa⟩ := hordD hx0 ha'
  obtain ⟨hib, hWb⟩ := hordD hy0 hb'
  obtain rfl : a' = a := hia.symm.trans ha
  obtain rfl : b' = b := hib.symm.trans hb
  letI := functionFieldAlgebra (q ≫ sX j)
  letI := functionFieldMapAlgebra q
  haveI := isScalarTower_functionFieldMap (sX j) q
  let φq : FunctionFieldHom (q ≫ sX j) (sX j) :=
    IsScalarTower.toAlgHom k (X j).functionField W.functionField
  have hcohY : Order.coheight (jW (genericPoint Y)) = 1 := by
    rw [hjWP]; exact Pt.coheight_genericPoint
  obtain ⟨ζW, -, hζWv, hres⟩ := isPoincareResidue_pluriformPullback_formPow_dlog
    (sY := q ≫ sX j) (sX' := sX j) (by rw [hdW]; norm_num) hdj2 jW hcohY φq h0c hx0 hy0 hWa hWb
    habcd 1
  have hσeq : pluriformPullback (q ≫ sX j) (sX j) φq 2 1 (formPow (ιMulti (X j).functionField 2
      ![(algebraMap _ (X j).functionField x)⁻¹ •
          KaehlerDifferential.D k (X j).functionField (algebraMap _ (X j).functionField x),
        (algebraMap _ (X j).functionField y)⁻¹ •
          KaehlerDifferential.D k (X j).functionField (algebraMap _ (X j).functionField y)]) 1) =
      pullbackRationalPluriForms (sX j) q (RationalTopForms.toPluriForms (sX j) ωt) := by
    rw [← hωt]
    rfl
  letI := functionFieldAlgebra (jW ≫ q ≫ sX j)
  have hres' : IsPoincareResidue (q ≫ sX j) jW 1 1
      (pullbackRationalPluriForms (sX j) q (RationalTopForms.toPluriForms (sX j) ωt))
      (formPow (ιMulti Y.functionField 1
        ![((jW.stalkMap (genericPoint Y)).hom ζW)⁻¹ •
          KaehlerDifferential.D k Y.functionField ((jW.stalkMap (genericPoint Y)).hom ζW)]) 1) := by
    rw [← hσeq]
    exact hres
  have hηe := (hηiff _).mp hres'
  /- Step 10: `ζ` is the pull-back of `z̄` along `Y ⟶ T`. -/
  have hpVg : pV (genericPoint Y) = genericPoint T :=
    MMP.Positivity.map_genericPoint_eq_of_isDominant pV
  have hzw : ι (genericPoint T) = p (jW (genericPoint Y)) := by rw [hjg, hpt, hP]
  have h1 := functionFieldMap_algebraMap_stalkMap_of_comp_eq pV ι jW p hsqV (genericPoint Y)
    hpVg hzw z
  rw [MMP.Resolution.algebraMap_stalk_genericPoint_apply,
    MMP.Resolution.algebraMap_stalk_genericPoint_apply] at h1
  have hw : (p.stalkMap (jW (genericPoint Y))).hom
      (((X i).presheaf.stalkCongr (.of_eq hzw)).hom.hom z) = ζW := by
    apply IsFractionRing.injective (W.presheaf.stalk (jW (genericPoint Y))) W.functionField
    rw [← functionFieldMap_algebraMap_stalk p, algebraMap_stalkCongr_hom hzw, hzv, hζWv,
      map_mul, map_zpow₀, map_zpow₀, ← hfq, ← hfq]
    rfl
  rw [hw] at h1
  /- Step 11: read `B_T` on `Y`. -/
  have hsYeq : pV ≫ ι ≫ sX i = jW ≫ q ≫ sX j := by rw [hsW, hpq]
  have hYvj : IsNormalVariety k (jW ≫ q ≫ sX j) := hsYeq ▸ hYv
  have hdY : topologicalKrullDim Y = (1 : ℕ) :=
    MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support (q ≫ sX j) (by rw [hdW])
      jW Pt hPtr
  obtain ⟨hall, hex⟩ := coeff_eq_one_of_ord_ne_zero_of_coeff_eq_neg_ordForm_dlog hTv
    (by exact_mod_cast hT) hTp (jW ≫ q ≫ sX j) hYvj hYsm' inferInstance
    (by exact_mod_cast hdY) pV hYv hpV hcrR ((hz.map _).ne_zero) h1
    (fun Qt => by rw [hRdη Qt, ← hηe]) (by rw [← hηe] at hη0; exact hη0)
  exact ⟨hTp, hall, hex⟩

/-- **`z̄` has a zero or a pole at every floor point.** In the situation of
`exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional`, every zero-dimensional
stratum `q` of `(T, B_T)` reached by an adjunction step `S ⟶ T` is a zero or a pole of `z̄`: the
points of coefficient one in `B_T` are the zeros and poles of `z̄`
(`MMP.Fourfold.coeff_eq_one_iff_ord_ne_zero_of_isExceptional`). -/
theorem ord_ne_zero_of_isExceptional_of_isAdjunctionStep
    (R : ResidueRestriction sX B 2 m) {i j : I}
    (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) {a b : ℤ}
    (ha : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField x)) (ι (genericPoint T)) = a)
    (hb : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField y)) (ι (genericPoint T)) = b)
    {z : (X i).presheaf.stalk (ι (genericPoint T))} (hz : IsUnit z)
    (hzv : algebraMap _ (X i).functionField z =
      (σ.toHom) (algebraMap _ (X j).functionField y) ^ a *
        (σ.toHom) (algebraMap _ (X j).functionField x) ^ (-b))
    {S : Scheme.{0}} {jq : S ⟶ T} {Bq : QDivisor S}
    (hq : IsAdjunctionStep (ι ≫ sX i) BT jq Bq) :
    haveI : IsLocallyNoetherian T :=
      (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    haveI : IsIntegral S := hq.1.1.toIsIntegral
    T.ord ((ι.stalkMap (genericPoint T)).hom z) (jq (genericPoint S)) ≠ 0 := by
  haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
  haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
  haveI : IsIntegral S := hq.1.1.toIsIntegral
  obtain ⟨-, hall, -⟩ := coeff_eq_one_iff_ord_ne_zero_of_isExceptional R σ hσ h hι hT P hP D hDv
    hD hne h₁ h₂ hp₁ hp₂ hxy hx hy ha hb hz hzv
  obtain ⟨-, Q, hQ1, hQr, hci, -⟩ := hq
  haveI := hci
  rw [MMP.CyclicChartDifferent.Aux.map_genericPoint_eq jq Q hQr]
  intro h0
  have := (hall Q).2 h0
  linarith

/-- **A floor point where `z̄` has a zero or a pole.** In the situation of
`exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional`, some zero-dimensional
stratum `q` of `(T, B_T)` reached by an adjunction step has `ord_q z̄ ≠ 0`. -/
private theorem exists_isAdjunctionStep_ord_ne_zero_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) {a b : ℤ}
    (ha : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField x)) (ι (genericPoint T)) = a)
    (hb : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField y)) (ι (genericPoint T)) = b)
    {z : (X i).presheaf.stalk (ι (genericPoint T))} (hz : IsUnit z)
    (hzv : algebraMap _ (X i).functionField z =
      (σ.toHom) (algebraMap _ (X j).functionField y) ^ a *
        (σ.toHom) (algebraMap _ (X j).functionField x) ^ (-b)) :
    letI := functionFieldAlgebra (ι ≫ sX i)
    haveI : IsLocallyNoetherian T :=
      (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    ∃ (S : Scheme.{0}) (jq : S ⟶ T) (Bq : QDivisor S)
      (_ : IsAdjunctionStep (ι ≫ sX i) BT jq Bq) (_ : IsIntegral S),
      topologicalKrullDim S = (0 : ℕ) ∧
        T.ord ((ι.stalkMap (genericPoint T)).hom z) (jq (genericPoint S)) ≠ 0 := by
  have hPi := R.setting.isPair i
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
  haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
  obtain ⟨hTp, hall, Q, hQz⟩ := coeff_eq_one_iff_ord_ne_zero_of_isExceptional R σ hσ
    h hι hT P hP D hDv hD hne h₁ h₂ hp₁ hp₂ hxy hx hy ha hb hz hzv
  have hQ1 := (hall Q).1 hQz
  obtain ⟨S, jq, Bq, hq, hSi, hS, hjq⟩ :=
    exists_isAdjunctionStep_of_coeff_eq_one_of_topologicalKrullDim_eq_one hTp
      (by exact_mod_cast hT) Q hQ1
  exact ⟨S, jq, Bq, hq, hSi, hS, by rw [hjq]; exact hQz⟩

open exteriorPower in
/-- **A floor point of the exceptional floor curve.** In the situation of
`exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional`, the form `(dz̄/z̄)^{⊗m}`
on `T` has a nonzero residue at a zero-dimensional stratum `q ∈ T`: a point where `z̄` has a zero
or a pole is a floor point of `(T, B_T)`. -/
private theorem exists_isAdjunctionStep_isPoincareResidue_formPow_dlog_ne_zero_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) {a b : ℤ}
    (ha : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField x)) (ι (genericPoint T)) = a)
    (hb : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField y)) (ι (genericPoint T)) = b)
    {z : (X i).presheaf.stalk (ι (genericPoint T))} (hz : IsUnit z)
    (hzv : algebraMap _ (X i).functionField z =
      (σ.toHom) (algebraMap _ (X j).functionField y) ^ a *
        (σ.toHom) (algebraMap _ (X j).functionField x) ^ (-b)) :
    letI := functionFieldAlgebra (ι ≫ sX i)
    haveI : IsLocallyNoetherian T :=
      (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    ∃ (S : Scheme.{0}) (jq : S ⟶ T) (Bq : QDivisor S)
      (_ : IsAdjunctionStep (ι ≫ sX i) BT jq Bq) (_ : IsIntegral S),
      topologicalKrullDim S = (0 : ℕ) ∧
        ∃ r : RationalPluriForms (jq ≫ ι ≫ sX i) 0 m, r ≠ 0 ∧
          IsPoincareResidue (ι ≫ sX i) jq 0 m
            (show RationalPluriForms (ι ≫ sX i) 1 m from formPow (ιMulti T.functionField 1
              ![((ι.stalkMap (genericPoint T)).hom z)⁻¹ •
                KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom z)]) m)
            r := by
  letI := functionFieldAlgebra (ι ≫ sX i)
  have hPi := R.setting.isPair i
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
  haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
  obtain ⟨S, jq, Bq, hq, hSi, hS, hord⟩ :=
    exists_isAdjunctionStep_ord_ne_zero_of_isExceptional R σ hσ h hι hT P hP D hDv hD hne h₁
      h₂ hp₁ hp₂ hxy hx hy ha hb hz hzv
  have hz0 : (ι.stalkMap (genericPoint T)).hom z ≠ 0 := (hz.map _).ne_zero
  have hTn : IsNormalVariety k (ι ≫ sX i) := by
    have := hι.1
    rwa [Category.id_comp] at this
  obtain ⟨r, hr0, hr⟩ := exists_isPoincareResidue_formPow_dlog_ne_zero hTn
    (by exact_mod_cast hT) hq hS hz0 hord m
  exact ⟨S, jq, Bq, hq, hSi, hS, r, hr0, hr⟩

open exteriorPower in
/-- **The degree-zero line of residues along an exceptional floor curve.** In the situation of
`toFun_step_refl_eq_of_isExceptional_of_isCrepantBirationalMap`, the residues along `P` of all
sections of `m(K_{X_i} + B_i)` are multiples `c • ρ`, `c ∈ k`, of one form `ρ` on `T`, and `ρ`
has a nonzero residue at a zero-dimensional stratum `q ∈ T` reached by one more adjunction
step. -/
private theorem exists_line_and_point_of_isExceptional (R : ResidueRestriction sX B 2 m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    haveI : IsLocallyNoetherian T :=
      (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    ∃ ρ : RationalPluriForms ((ι ≫ 𝟙 (X i)) ≫ sX i) 1 m,
      (∀ w : logPluricanonicalSections (sX i) 2 m (B i), ∃ c : k,
        R.toFun i (.step (.refl h) ι BT hι) 1 w = c • ρ) ∧
      ∃ (S : Scheme.{0}) (jq : S ⟶ T) (Bq : QDivisor S)
        (hq : IsAdjunctionStep ((ι ≫ 𝟙 (X i)) ≫ sX i) BT jq Bq) (_ : IsIntegral S),
        topologicalKrullDim S = (0 : ℕ) ∧
        ∃ r : RationalPluriForms (jq ≫ (ι ≫ 𝟙 (X i)) ≫ sX i) 0 m, r ≠ 0 ∧
          IsPoincareResidue ((ι ≫ 𝟙 (X i)) ≫ sX i) jq 0 m ρ r := by
  have hPi := R.setting.isPair i
  haveI := hPi.charZero
  haveI := hPi.isAlgClosed
  haveI : PerfectField k := PerfectField.ofCharZero
  have hXi := hPi.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX i) := hXi.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (𝟙 (X i) ≫ sX i) := by rw [Category.id_comp]; infer_instance
  set F1 := StratumAdjunctionData.step (.refl h) ι BT hι with hF1
  haveI := F1.isLocallyNoetherian_stratum
  obtain ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, x, y, hxy, hx, hy, a, b, ha, hb, -, z, hz, hzv, hres⟩ :=
    exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional R σ hσ h hι P hP D hDv hD
  obtain ⟨S, jq, Bq, hq, hSi, hS, r, hr0, hr⟩ :=
    exists_isAdjunctionStep_isPoincareResidue_formPow_dlog_ne_zero_of_isExceptional R σ hσ h hι
      hT P hP D hDv hD hne h₁ h₂ hp₁ hp₂ hxy hx hy ha hb hz hzv
  letI := functionFieldAlgebra (ι ≫ sX i)
  generalize (show RationalPluriForms (ι ≫ sX i) 1 m from formPow (ιMulti T.functionField 1
      ![((ι.stalkMap (genericPoint T)).hom z)⁻¹ •
        KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom z)]) m) = ρT
    at hres hr
  have e₁ : ι ≫ sX i = (ι ≫ 𝟙 (X i)) ≫ sX i := by rw [Category.comp_id]
  have e₂ : jq ≫ ι ≫ sX i = jq ≫ (ι ≫ 𝟙 (X i)) ≫ sX i := by rw [Category.comp_id]
  refine ⟨cast (congrArg (fun s : T ⟶ Spec (.of k) => RationalPluriForms s 1 (m : ℤ)) e₁) ρT,
    fun w => ?_, S, jq, Bq, e₁ ▸ hq, hSi, hS,
    cast (congrArg (fun s : S ⟶ Spec (.of k) => RationalPluriForms s 0 (m : ℤ)) e₂) r, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hres w w.2
    obtain ⟨ρ₀, ⟨-, hρ₀⟩, ρ', hr', hρ'⟩ := (R.isIteratedResidue i F1 1 w hT).rec'
    have e₀ : sX i = 𝟙 (X i) ≫ sX i := (Category.id_comp _).symm
    have e₃ : ι ≫ sX i = ι ≫ 𝟙 (X i) ≫ sX i := by rw [Category.id_comp]
    have he' := IsPoincareResidue.of_heq ι e₀ (τ' := ρ₀)
      (ρ' := cast (congrArg (fun s : T ⟶ Spec (.of k) => RationalPluriForms s 1 (m : ℤ)) e₃)
        (e • ρT)) hρ₀.symm (cast_heq _ _).symm he
    have hu := IsPoincareResidue.unique hι hr' he'
    refine ⟨e, eq_of_heq (hρ'.trans ?_)⟩
    rw [hu]
    exact (cast_heq _ _).trans (RationalPluriForms.smul_heq e₁ (cast_heq _ _).symm e)
  · intro h0
    exact hr0 (RationalPluriForms.eq_zero_of_heq e₂.symm (cast_heq _ _) h0)
  · exact IsPoincareResidue.of_heq jq e₁ (τ := ρT) (ρ := r) (cast_heq _ _).symm
      (cast_heq _ _).symm hr

open exteriorPower in
/-- `MMP.Fourfold.exists_stalk_eq_smul_formPow_dlog_of_isExceptional`, recording also that `Q₁`
and `Q₂` are the only components of `B_j` through the centre `p` of `D`. -/
theorem exists_stalk_eq_smul_formPow_dlog_of_isExceptional'
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
    letI := functionFieldAlgebra (sX j)
    haveI := isScalarTower_stalk_functionField (sX j) (D.f D.E.genericPoint)
    ∃ Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j), Q₁ ≠ Q₂ ∧ (B j).coeff Q₁ = 1 ∧ (B j).coeff Q₂ = 1 ∧
      D.f D.E.genericPoint ∈ Q₁.support ∧ D.f D.E.genericPoint ∈ Q₂.support ∧
      (∀ Q : MMP.Mori.PrimeDivisor (X j), (B j).coeff Q ≠ 0 → D.f D.E.genericPoint ∈ Q.support →
        Q = Q₁ ∨ Q = Q₂) ∧
      ∃ x y : (X j).presheaf.stalk (D.f D.E.genericPoint),
        MMP.Mori.IsRegularSystemOfParameters ![x, y] ∧
        IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x} ∧
        IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y} ∧
        Submodule.span ((X j).presheaf.stalk (D.f D.E.genericPoint))
          {ιMulti ((X j).presheaf.stalk (D.f D.E.genericPoint)) 2
            ![KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) x,
              KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) y]} = ⊤ ∧
        topFormsMap k ((X j).presheaf.stalk (D.f D.E.genericPoint)) (X j).functionField 2
          (ιMulti ((X j).presheaf.stalk (D.f D.E.genericPoint)) 2
            ![KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) x,
              KaehlerDifferential.D k ((X j).presheaf.stalk (D.f D.E.genericPoint)) y]) ≠ 0 ∧
        ∀ m' : ℕ, ∀ τ ∈ logPluricanonicalSections (sX j) 2 m' (B j),
          ∃ g : (X j).presheaf.stalk (D.f D.E.genericPoint),
            τ = algebraMap _ (X j).functionField g •
              (formPow (ιMulti (X j).functionField 2
                ![(algebraMap _ (X j).functionField x)⁻¹ •
                    KaehlerDifferential.D k (X j).functionField
                      (algebraMap _ (X j).functionField x),
                  (algebraMap _ (X j).functionField y)⁻¹ •
                    KaehlerDifferential.D k (X j).functionField
                      (algebraMap _ (X j).functionField y)]) m' :
                RationalPluriForms (sX j) 2 m') := by
  have hPj := R.setting.isPair j
  haveI := hPj.charZero
  have hXj := hPj.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim (X j) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq j
  obtain ⟨Z, -, hsnc, hZ⟩ :=
    exists_dltWitness_center_notMem_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv
  obtain ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, hQ⟩ :=
    exists_ne_coeff_eq_one_of_isExceptional_of_isCrepantBirationalMap R σ hσ h hι P hP D hDv hD
  have hcoh := DivisorOver.coheight_eq_two_of_isExceptional hXj hd D hD
  exact ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, hQ, exists_stalk_eq_smul_formPow_dlog_of_isSNC_restrict hd
    (Z.compl : (X j).Opens) hsnc ⟨D.f D.E.genericPoint, hZ⟩ hcoh hne h₁ h₂ hp₁ hp₂ hQ⟩

/-- **The function field of an exceptional floor curve.** In the situation of
`exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional`, `k(T) = k(z̄)`: the residue
field of the monomial valuation `v_D` of weight `(a, b)` (`gcd(a, b) = 1`) at the crossing `p` is
generated by the class of `y^a x^{-b}`. -/
private theorem adjoin_eq_top_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) {a b : ℤ}
    (ha : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField x)) (ι (genericPoint T)) = a)
    (hb : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField y)) (ι (genericPoint T)) = b)
    {z : (X i).presheaf.stalk (ι (genericPoint T))} (hz : IsUnit z)
    (hzv : algebraMap _ (X i).functionField z =
      (σ.toHom) (algebraMap _ (X j).functionField y) ^ a *
        (σ.toHom) (algebraMap _ (X j).functionField x) ^ (-b)) :
    letI := functionFieldAlgebra (ι ≫ sX i)
    IntermediateField.adjoin k {(ι.stalkMap (genericPoint T)).hom z} = ⊤ := by
  classical
  letI := functionFieldAlgebra (ι ≫ sX i)
  have hPj := R.setting.isPair j
  have hPi := R.setting.isPair i
  haveI := hPj.isAlgClosed
  haveI := hPj.charZero
  haveI : PerfectField k := PerfectField.ofCharZero
  have hXj := hPj.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  have hdj : topologicalKrullDim (X j) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq j
  have hc := DivisorOver.isClosed_singleton_of_isExceptional hXj hdj D hD
  letI := functionFieldAlgebra (sX j)
  letI := functionFieldAlgebra (sX i)
  letI := stalkAlgebra (sX j) (D.f D.E.genericPoint)
  haveI := isScalarTower_stalk_functionField (sX j) (D.f D.E.genericPoint)
  letI := stalkAlgebra (sX i) (ι (genericPoint T))
  haveI := isScalarTower_stalk_functionField (sX i) (ι (genericPoint T))
  obtain ⟨a', b', ha0, hb0, hcop, hva, hvb, hmon⟩ :=
    exists_coprime_mem_weightedMonomialIdeal_of_isExceptional R σ hσ h hι P hP D hDv hD hne h₁ h₂
      hp₁ hp₂ hxy hx hy
  -- the orders `a, b` are those of `v_D`
  have hord : ∀ {f : (X j).functionField} {e : ℕ}, f ≠ 0 →
      D.valuation f = WithZero.exp (-(e : ℤ)) →
      (X i).ord ((σ.toHom) f) (ι (genericPoint T)) = e := by
    intro f e hf hfe
    have hσf : (σ.toHom) f ≠ 0 := (map_ne_zero _).mpr hf
    rw [hDv, P.divisorialValuation_eq_exp_neg_ord hσf, WithZero.exp_inj, neg_inj] at hfe
    rwa [hP]
  have hx0 : algebraMap _ (X j).functionField x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hva; exact WithZero.exp_ne_zero hva.symm
  have hy0 : algebraMap _ (X j).functionField y ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvb; exact WithZero.exp_ne_zero hvb.symm
  obtain rfl : a = a' := ha.symm.trans (hord hx0 hva)
  obtain rfl : b = b' := hb.symm.trans (hord hy0 hvb)
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℤ, (a' : ℤ) * c + b' * d = 1 := by
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨u, v, by linarith⟩
  -- the data of `v_D` on `𝒪_{X_j,p}`
  have hvR : ∀ r : (X j).presheaf.stalk (D.f D.E.genericPoint),
      D.valuation (algebraMap _ (X j).functionField r) ≤ 1 :=
    MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl
  have hres := exists_sub_mem_maximalIdeal_of_isClosed (sX j) _ hc
  have hmax : IsLocalRing.maximalIdeal ((X j).presheaf.stalk (D.f D.E.genericPoint)) ≤
      Ideal.span {x, y} := by
    rw [← hxy.1]
    refine le_of_eq (congrArg Ideal.span ?_)
    ext t
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_congr eq_comm eq_comm
  -- residues along `P`
  set zbar := (ι.stalkMap (genericPoint T)).hom z with hzbar
  have hcohP : Order.coheight (ι (genericPoint T)) = 1 := hP ▸ P.coheight_genericPoint
  have hvP : ∀ ψ : (X i).presheaf.stalk (ι (genericPoint T)),
      algebraMap _ (X i).functionField ψ ≠ 0 →
      P.divisorialValuation (algebraMap _ (X i).functionField ψ) =
        WithZero.exp (-(X i).ord (algebraMap _ (X i).functionField ψ) (ι (genericPoint T))) :=
    fun ψ hψ => by rw [P.divisorialValuation_eq_exp_neg_ord hψ, ← hP]
  have hmem_of_lt : ∀ ψ : (X i).presheaf.stalk (ι (genericPoint T)),
      P.divisorialValuation (algebraMap _ (X i).functionField ψ) < 1 →
      ψ ∈ IsLocalRing.maximalIdeal ((X i).presheaf.stalk (ι (genericPoint T))) := by
    intro ψ hψ
    by_cases h0 : algebraMap _ (X i).functionField ψ = 0
    · rw [(map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h0]; exact zero_mem _
    refine mem_maximalIdeal_of_ord_pos hcohP ψ ?_
    rw [hvP ψ h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hψ
    omega
  have hunit_of_eq : ∀ ψ : (X i).presheaf.stalk (ι (genericPoint T)),
      P.divisorialValuation (algebraMap _ (X i).functionField ψ) = 1 → IsUnit ψ := by
    intro ψ hψ
    have h0 : algebraMap _ (X i).functionField ψ ≠ 0 := by
      intro h0; rw [h0, map_zero] at hψ; exact zero_ne_one hψ
    have ho : (X i).ord (algebraMap _ (X i).functionField ψ) (ι (genericPoint T)) = 0 := by
      rw [hvP ψ h0, ← WithZero.exp_zero, WithZero.exp_inj] at hψ
      omega
    have hinv : (algebraMap _ (X i).functionField ψ)⁻¹ ∈
        (algebraMap ((X i).presheaf.stalk (ι (genericPoint T))) (X i).functionField).range := by
      refine (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hcohP (inv_ne_zero h0)).mpr ?_
      have := MMP.Mori.ord_zpow (ι (genericPoint T)) h0 (-1)
      rw [zpow_neg, zpow_one] at this
      rw [this, ho]; norm_num
    obtain ⟨w, hw⟩ := hinv
    refine isUnit_iff_exists_inv.mpr ⟨w, IsFractionRing.injective _ (X i).functionField ?_⟩
    rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]
  obtain ⟨-, -, hci⟩ := hι.exists_primeDivisor
  haveI := hci
  have hsurj : Function.Surjective (ι.stalkMap (genericPoint T)).hom :=
    ι.stalkMap_surjective (genericPoint T)
  letI : Field (T.presheaf.stalk (genericPoint T)) := inferInstanceAs (Field T.functionField)
  have hker : RingHom.ker (ι.stalkMap (genericPoint T)).hom =
      IsLocalRing.maximalIdeal ((X i).presheaf.stalk (ι (genericPoint T))) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  -- Laurent polynomials in `y^a x^{-b}` restrict into `k(z̄)`
  set zf := algebraMap _ (X j).functionField y ^ (a' : ℤ) *
    algebraMap _ (X j).functionField x ^ (-(b' : ℤ)) with hzf
  have hσzf : σ zf = algebraMap _ (X i).functionField z := by
    rw [hzv, hzf, map_mul, map_zpow₀, map_zpow₀]; rfl
  have hkT : ∀ c : k, (ι.stalkMap (genericPoint T)).hom (algebraMap k _ c) =
      algebraMap k T.functionField c :=
    fun c => MMP.Threefold.Resolution.stalkMap_algebraMap (sX := sX i) ι (genericPoint T) c
  let S : Subalgebra k (X j).functionField :=
    { carrier := {L | ∃ ℓ : (X i).presheaf.stalk (ι (genericPoint T)),
        algebraMap _ (X i).functionField ℓ = σ L ∧
          (ι.stalkMap (genericPoint T)).hom ℓ ∈ IntermediateField.adjoin k {zbar}}
      mul_mem' := by
        rintro L L' ⟨ℓ, h1, h2⟩ ⟨ℓ', h1', h2'⟩
        exact ⟨ℓ * ℓ', by rw [map_mul, map_mul, h1, h1'], by rw [map_mul]; exact mul_mem h2 h2'⟩
      one_mem' := ⟨1, by rw [map_one, map_one], by rw [map_one]; exact one_mem _⟩
      add_mem' := by
        rintro L L' ⟨ℓ, h1, h2⟩ ⟨ℓ', h1', h2'⟩
        exact ⟨ℓ + ℓ', by rw [map_add, map_add, h1, h1'], by rw [map_add]; exact add_mem h2 h2'⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; exact zero_mem _⟩
      algebraMap_mem' := fun c => ⟨algebraMap k _ c,
        by rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes],
        by rw [hkT]; exact IntermediateField.algebraMap_mem _ c⟩ }
  have hAS : Algebra.adjoin k {zf, zf⁻¹} ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro L (rfl | hL)
    · exact ⟨z, hσzf.symm, IntermediateField.mem_adjoin_simple_self k zbar⟩
    · rw [Set.mem_singleton_iff] at hL
      subst hL
      obtain ⟨w, hzw⟩ := hz.exists_right_inv
      refine ⟨w, ?_, ?_⟩
      · rw [map_inv₀, hσzf]
        exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, hzw, map_one])
      · have : (ι.stalkMap (genericPoint T)).hom w = zbar⁻¹ :=
          eq_inv_of_mul_eq_one_right (by rw [hzbar, ← map_mul, hzw, map_one])
        rw [this]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self k zbar)
  -- every element of `k(T)` is a residue
  rw [eq_top_iff]
  intro fbar _
  obtain ⟨φ, rfl⟩ := hsurj fbar
  have hφle : P.divisorialValuation (algebraMap _ (X i).functionField φ) ≤ 1 := by
    by_cases h0 : algebraMap _ (X i).functionField φ = 0
    · rw [h0, map_zero]; exact zero_le'
    rw [hvP φ h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    have := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hcohP h0).mp ⟨φ, rfl⟩
    omega
  rcases hφle.lt_or_eq with hlt | heq
  · have : (ι.stalkMap (genericPoint T)).hom φ = 0 := by
      rw [← RingHom.mem_ker, hker]; exact hmem_of_lt φ hlt
    rw [this]; exact zero_mem _
  set F := σ.symm (algebraMap _ (X i).functionField φ) with hF
  have hσF : σ F = algebraMap _ (X i).functionField φ := σ.apply_symm_apply _
  have hvF : D.valuation F = 1 := by
    rw [hDv]; change P.divisorialValuation (σ F) = 1; rw [hσF, heq]
  obtain ⟨L₁, hL₁, L₂, hL₂, hvL₂, hlt⟩ := exists_mem_adjoin_valuation_mul_sub_lt_one
    (k := k) D.valuation hvR hcd ha0 hb0 hva hvb hres hmax
    (fun f hf M hfM => hmon f hf M hfM) F hvF
  obtain ⟨ℓ₁, h1₁, h2₁⟩ := hAS hL₁
  obtain ⟨ℓ₂, h1₂, h2₂⟩ := hAS hL₂
  have hdiff : φ * ℓ₂ - ℓ₁ ∈ IsLocalRing.maximalIdeal _ := by
    refine hmem_of_lt _ ?_
    have he : algebraMap _ (X i).functionField (φ * ℓ₂ - ℓ₁) = σ (F * L₂ - L₁) := by
      rw [map_sub, map_mul, map_sub, map_mul, hσF, h1₂, h1₁]
    rw [he]
    have := hDv (F * L₂ - L₁)
    change D.valuation _ = P.divisorialValuation (σ _) at this
    rw [← this]; exact hlt
  rw [← hker, RingHom.mem_ker, map_sub, map_mul, sub_eq_zero] at hdiff
  have hℓ₂ : (ι.stalkMap (genericPoint T)).hom ℓ₂ ≠ 0 := by
    have hu : IsUnit ℓ₂ := hunit_of_eq ℓ₂ (by
      rw [h1₂]
      have := hDv L₂
      change D.valuation _ = P.divisorialValuation (σ _) at this
      rw [← this, hvL₂])
    exact (hu.map _).ne_zero
  rw [(eq_div_iff hℓ₂).mpr hdiff]
  exact div_mem h2₁ h2₂

/-- **Orders of `z̄` at the floor points of an exceptional floor curve.** In the situation of
`exists_forall_isPoincareResidue_smul_formPow_dlog_of_isExceptional`, at every
zero-dimensional stratum `q` of `(T, B_T)` reached by an adjunction step, `ord_q z̄ = ±1`. -/
private theorem ord_eq_one_or_eq_neg_one_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor (X j)} (hne : Q₁ ≠ Q₂) (h₁ : (B j).coeff Q₁ = 1)
    (h₂ : (B j).coeff Q₂ = 1) (hp₁ : D.f D.E.genericPoint ∈ Q₁.support)
    (hp₂ : D.f D.E.genericPoint ∈ Q₂.support)
    {x y : (X j).presheaf.stalk (D.f D.E.genericPoint)}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (hx : IdealSheafData.stalk Q₁.idealSheaf (D.f D.E.genericPoint) = Ideal.span {x})
    (hy : IdealSheafData.stalk Q₂.idealSheaf (D.f D.E.genericPoint) = Ideal.span {y}) {a b : ℤ}
    (ha : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField x)) (ι (genericPoint T)) = a)
    (hb : (X i).ord ((σ.toHom) (algebraMap _ (X j).functionField y)) (ι (genericPoint T)) = b)
    {z : (X i).presheaf.stalk (ι (genericPoint T))} (hz : IsUnit z)
    (hzv : algebraMap _ (X i).functionField z =
      (σ.toHom) (algebraMap _ (X j).functionField y) ^ a *
        (σ.toHom) (algebraMap _ (X j).functionField x) ^ (-b))
    {S : Scheme.{0}} {jq : S ⟶ T} {Bq : QDivisor S} [IsIntegral S]
    (hq : IsAdjunctionStep (ι ≫ sX i) BT jq Bq) (hS : topologicalKrullDim S = (0 : ℕ)) :
    haveI : IsLocallyNoetherian T :=
      (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    T.ord ((ι.stalkMap (genericPoint T)).hom z) (jq (genericPoint S)) = 1 ∨
      T.ord ((ι.stalkMap (genericPoint T)).hom z) (jq (genericPoint S)) = -1 := by
  letI := functionFieldAlgebra (ι ≫ sX i)
  haveI : IsLocallyNoetherian T :=
    (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
  haveI : IsNormal T := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
  have hgen := adjoin_eq_top_of_isExceptional R σ hσ h hι hT P hP D hDv hD hne h₁ h₂ hp₁ hp₂
    hxy hx hy ha hb hz hzv
  have hne0 := ord_ne_zero_of_isExceptional_of_isAdjunctionStep R σ hσ h hι hT P hP D hDv hD hne
    h₁ h₂ hp₁ hp₂ hxy hx hy ha hb hz hzv hq
  obtain ⟨Q, hQ, -⟩ := hq.exists_primeDivisor
  rw [hQ] at hne0 ⊢
  have hw0 : (ι.stalkMap (genericPoint T)).hom z ≠ 0 := (hz.map _).ne_zero
  rcases lt_or_gt_of_ne hne0 with hneg | hpos
  · right
    have hinv : T.ord ((ι.stalkMap (genericPoint T)).hom z)⁻¹ Q.genericPoint =
        -T.ord ((ι.stalkMap (genericPoint T)).hom z) Q.genericPoint := by
      have := MMP.Mori.ord_zpow Q.genericPoint hw0 (-1)
      rw [zpow_neg, zpow_one] at this
      rw [this]; ring
    have hgen' : IntermediateField.adjoin k {((ι.stalkMap (genericPoint T)).hom z)⁻¹} = ⊤ := by
      refine top_le_iff.mp (hgen ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
      have := IntermediateField.inv_mem _
        (IntermediateField.mem_adjoin_simple_self k ((ι.stalkMap (genericPoint T)).hom z)⁻¹)
      rwa [inv_inv] at this
    have h1 := eq_one_of_adjoin_eq_top_of_ord_pos (ι ≫ sX i) Q hgen' (by rw [hinv]; omega)
    rw [hinv] at h1
    omega
  · exact Or.inl (eq_one_of_adjoin_eq_top_of_ord_pos (ι ≫ sX i) Q hgen hpos)

open exteriorPower in
/-- **Residues at points of an exceptional floor curve.** In the situation of
`toFun_step_refl_eq_of_isExceptional_of_isCrepantBirationalMap`, at every zero-dimensional
stratum `q` of `X_i` on `P`, the iterated residue of `u = σ^* s_j` along `(P, q)` is the pull-back
of the iterated residue of `s_j` at a zero-dimensional stratum of `X_j` (the centre of `D`). -/
private theorem exists_toFun_eq_pluriformPullback_of_isExceptional
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)}
    (u : logPluricanonicalSections (sX i) 2 m (B i))
    (hu : (u : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {S : Scheme.{0}} {jq : S ⟶ T} {Bq : QDivisor S}
    (hq : IsAdjunctionStep ((ι ≫ 𝟙 (X i)) ≫ sX i) BT jq Bq)
    (hS : topologicalKrullDim S = (0 : ℕ)) :
    ∃ (S' : Scheme.{0}) (ι' : S' ⟶ X j) (BS' : QDivisor S')
      (F' : StratumAdjunctionData (sX j) (B j) ι' BS'),
      1 ≤ F'.length ∧ topologicalKrullDim S' = (0 : ℕ) ∧
      haveI := F'.isIntegral_stratum
      haveI : IsIntegral S := hq.1.1.toIsIntegral
      ∃ σ₀ : FunctionFieldEquiv ((jq ≫ ι ≫ 𝟙 (X i)) ≫ sX i) (ι' ≫ sX j),
        pluriformPullback ((jq ≫ ι ≫ 𝟙 (X i)) ≫ sX i) (ι' ≫ sX j) σ₀.toHom 0 m
            (R.toFun j F' 0 (s j)) =
          R.toFun i (.step (.step (.refl h) ι BT hι) jq Bq hq) 0 u := by
  classical
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  haveI := hPj.isAlgClosed
  haveI := hPj.charZero
  haveI : PerfectField k := PerfectField.ofCharZero
  have hXj := hPj.isPair.isNormalVariety
  have hXi := hPi.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX i) := hXi.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (𝟙 (X i) ≫ sX i) := by rw [Category.id_comp]; infer_instance
  haveI : LocallyOfFiniteType (𝟙 (X j) ≫ sX j) := by rw [Category.id_comp]; infer_instance
  have hdj : topologicalKrullDim (X j) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq j
  have hdi : topologicalKrullDim (X i) = 2 := by exact_mod_cast R.setting.topologicalKrullDim_eq i
  have hm : Even m := R.setting.even
  set F1 := StratumAdjunctionData.step (.refl h) ι BT hι with hF1
  haveI := F1.isLocallyNoetherian_stratum
  haveI := F1.isNormal_stratum
  haveI : IsIntegral S := hq.1.1.toIsIntegral
  haveI : LocallyOfFiniteType ((ι ≫ 𝟙 (X i)) ≫ sX i) :=
    F1.isNormalVariety.1.toLocallyOfFiniteType
  have e₁ : ι ≫ sX i = (ι ≫ 𝟙 (X i)) ≫ sX i := by rw [Category.comp_id]
  haveI : LocallyOfFiniteType (ι ≫ sX i) := by rw [e₁]; infer_instance
  have hT : topologicalKrullDim T = (1 : ℕ) := by
    have hT0 := topologicalKrullDim_eq_toNat_trdeg ((ι ≫ 𝟙 (X i)) ≫ sX i)
    have hdl := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq i) F1 hT0
    simp only [hF1, StratumAdjunctionData.length] at hdl
    rw [hT0]
    exact_mod_cast (by omega : _ = 1)
  -- local data at the centre `p` of `D`
  obtain ⟨Q₁, Q₂, hne, h₁, h₂, hp₁, hp₂, hQ, x, y, hxy, hx, hy, -, h0, hsec⟩ :=
    exists_stalk_eq_smul_formPow_dlog_of_isExceptional' R σ hσ h hι P hP D hDv hD
  obtain ⟨a', b', c, d, ha, hb, habcd⟩ := exists_mul_add_mul_eq_one_of_isExceptional R σ hσ h hι P
    hP D hDv hD hne h₁ h₂ hp₁ hp₂ hxy hx hy
  letI := functionFieldAlgebra (sX j)
  letI := functionFieldAlgebra (sX i)
  letI := functionFieldAlgebra (ι ≫ sX i)
  obtain ⟨hx0, hy0, h0'⟩ := ne_zero_and_ιMulti_dlog_ne_zero_of_topFormsMap_ne_zero _ h0
  have hord : ∀ {f : (X j).functionField} {a : ℤ}, f ≠ 0 → D.valuation f = WithZero.exp (-a) →
      (X i).ord ((σ.toHom) f) (ι (genericPoint T)) = a := by
    intro f a hf hfa
    have hσf : (σ.toHom) f ≠ 0 := (map_ne_zero _).mpr hf
    rw [hDv, P.divisorialValuation_eq_exp_neg_ord hσf, WithZero.exp_inj, neg_inj] at hfa
    rw [hP]
    exact hfa
  have hc := DivisorOver.isClosed_singleton_of_isExceptional hXj hdj D hD
  have hcoh : Order.coheight (ι (genericPoint T)) = 1 := hP ▸ P.coheight_genericPoint
  obtain ⟨z, hz, hzv, hres⟩ := isPoincareResidue_pluriformPullback_formPow_dlog hdi hdj ι hcoh
    σ.toHom h0' hx0 hy0 (hord hx0 ha) (hord hy0 hb) habcd m
  obtain ⟨g, hg⟩ := hsec m _ (s j).2
  obtain ⟨e, he⟩ := exists_sub_mem_maximalIdeal_of_isClosed (sX j) _ hc g
  set ρz : RationalPluriForms (ι ≫ sX i) 1 m := formPow (ιMulti T.functionField 1
    ![((ι.stalkMap (genericPoint T)).hom z)⁻¹ •
      KaehlerDifferential.D k T.functionField ((ι.stalkMap (genericPoint T)).hom z)]) m with hρz
  -- the residue of `u` along `P`
  have hresu : IsPoincareResidue (sX i) ι 1 m (u : RationalPluriForms (sX i) 2 m) (e • ρz) := by
    rw [hu, hg]
    exact hres.pluriformPullback_smul_of_sub_mem_maximalIdeal P hP σ D hDv g e he
  -- the residue at `q`
  have hq' : IsAdjunctionStep (ι ≫ sX i) BT jq Bq := by rw [e₁]; exact hq
  have hordz := ord_eq_one_or_eq_neg_one_of_isExceptional R σ hσ h hι hT P hP D hDv hD hne h₁
    h₂ hp₁ hp₂ hxy hx hy (hord hx0 ha) (hord hy0 hb) hz hzv hq' hS
  obtain ⟨-, -, -, -, hcohq, -⟩ := hq'.stalk_facts
  have hz0 : (ι.stalkMap (genericPoint T)).hom z ≠ 0 := (hz.map _).ne_zero
  have hptq := (isPoincareResidue_formPow_dlog_pointUnitForm (ι ≫ sX i) jq hcohq hm hz0
    hordz).const_smul (ι ≫ sX i) jq e
  -- the iterated residue of `u` along `(P, q)`
  have hXi_side : R.toFun i (.step F1 jq Bq hq) 0 u =
      e • pointUnitForm ((jq ≫ ι ≫ 𝟙 (X i)) ≫ sX i) m := by
    obtain ⟨ρ₀, h₀, ρ', hr', hρ'⟩ := (R.isIteratedResidue i (.step F1 jq Bq hq) 0 u hS).rec'
    obtain ⟨ρ₁, ⟨-, hρ₁⟩, ρ₁', hr₁, hρ₁'⟩ := (R.isIteratedResidue i F1 1 u hT).rec'
    have e₀ : ρ₀ = R.toFun i F1 1 u :=
      IsIteratedResidueRec.unique F1 h₀ (R.isIteratedResidue i F1 1 u hT).rec'
    have es : sX i = 𝟙 (X i) ≫ sX i := (Category.id_comp _).symm
    have e₃ : ι ≫ sX i = ι ≫ 𝟙 (X i) ≫ sX i := by rw [Category.id_comp]
    have he' := IsPoincareResidue.of_heq ι es (τ' := ρ₁)
      (ρ' := cast (congrArg (fun s : T ⟶ Spec (.of k) => RationalPluriForms s 1 (m : ℤ)) e₃)
        (e • ρz)) hρ₁.symm (cast_heq _ _).symm hresu
    have hu1 := IsPoincareResidue.unique hι hr₁ he'
    have hρ₀ : HEq ρ₀ (e • ρz) := by
      rw [e₀]
      exact hρ₁'.trans (by rw [hu1]; exact cast_heq _ _)
    have hr2 := IsPoincareResidue.of_heq jq e₁ (τ := e • ρz) (τ' := ρ₀)
      (ρ := e • pointUnitForm (jq ≫ ι ≫ sX i) m)
      (ρ' := e • pointUnitForm (jq ≫ (ι ≫ 𝟙 (X i)) ≫ sX i) m) hρ₀.symm
      (pointUnitForm_smul_heq (by simp) e m) hptq
    have hu2 := IsPoincareResidue.unique hq hr' hr2
    exact eq_of_heq (hρ'.trans (by rw [hu2]; exact pointUnitForm_smul_heq (by simp) e m))
  -- a flag of `X_j` ending at the centre of `D`
  obtain ⟨S', ι', BS', F', hr', hS', hlen⟩ :=
    exists_stratumAdjunctionData_range_eq_center_of_isExceptional R σ hσ h hι P hP D hDv hD
  cases F' with
  | refl h₀ => simp [StratumAdjunctionData.length] at hlen
  | @step S₁ _ ιx B₁ F'' jp _ hp =>
  cases F'' with
  | refl h₀ => simp [StratumAdjunctionData.length] at hlen
  | @step _ _ _ _ F₃ ι₁ _ h1 =>
  cases F₃ with
  | step => simp [StratumAdjunctionData.length] at hlen
  | refl h' =>
  set F1j := StratumAdjunctionData.step (.refl h') ι₁ B₁ h1 with hF1j
  set F' := StratumAdjunctionData.step F1j jp BS' hp with hF'
  haveI := F1j.isIntegral_stratum
  haveI := F1j.isNormal_stratum
  haveI := F1j.isLocallyNoetherian_stratum
  haveI := F'.isIntegral_stratum
  have h1c := h1
  obtain ⟨-, Q, hQc, hQr, hci, -⟩ := h1c
  haveI := hci
  haveI : LocallyOfFiniteType ((ι₁ ≫ 𝟙 (X j)) ≫ sX j) :=
    F1j.isNormalVariety.1.toLocallyOfFiniteType
  have e₂ : (ι₁ ≫ 𝟙 (X j)) ≫ sX j = ι₁ ≫ sX j := by rw [Category.comp_id]
  haveI : LocallyOfFiniteType (ι₁ ≫ sX j) := by rw [← e₂]; infer_instance
  have hp' : IsAdjunctionStep (ι₁ ≫ sX j) B₁ jp BS' := by rw [← e₂]; exact hp
  have hpp : ι₁ (jp (genericPoint S')) = D.f D.E.genericPoint := by
    have hmem : (jp ≫ ι₁ ≫ 𝟙 (X j)).base (genericPoint S') ∈
        Set.range (jp ≫ ι₁ ≫ 𝟙 (X j)).base := ⟨_, rfl⟩
    rw [hr'] at hmem
    simpa using hmem
  have hpQ : D.f D.E.genericPoint ∈ Q.support := by
    have : ι₁ (jp (genericPoint S')) ∈ (Q.support : Set (X j)) := hQr ▸ ⟨_, rfl⟩
    rw [hpp] at this
    exact this
  have hQ12 := hQ Q (by linarith) hpQ
  -- the iterated residue of `s_j` along the flag
  have key2 : ∃ ρ₁ : RationalPluriForms (ι₁ ≫ sX j) 1 m,
      IsPoincareResidue (sX j) ι₁ 1 m (s j : RationalPluriForms (sX j) 2 m) ρ₁ ∧
      IsPoincareResidue (ι₁ ≫ sX j) jp 0 m ρ₁ (e • pointUnitForm (jp ≫ ι₁ ≫ sX j) m) := by
    rw [hg]
    rcases hQ12 with rfl | rfl
    · exact isPoincareResidue_smul_formPow_dlog_two_step hp' hne hQr hpp hp₂ hxy hx hy g e he hm
    · have hyx : MMP.Mori.IsRegularSystemOfParameters ![y, x] := by
        refine ⟨?_, hxy.2⟩
        have hr : Set.range ![y, x] = Set.range ![x, y] := by
          ext t; simp [Fin.exists_fin_two, or_comm]
        rw [hr]; exact hxy.1
      obtain ⟨ρ₁, hr1, hr2⟩ := isPoincareResidue_smul_formPow_dlog_two_step hp' hne.symm hQr hpp
        hp₁ hyx hy hx g e he hm
      refine ⟨ρ₁, ?_, hr2⟩
      rwa [formPow_ιMulti_two_swap _ _ hm] at hr1
  obtain ⟨ρ₁, hres1, hres2⟩ := key2
  have hXj_side : R.toFun j F' 0 (s j) = e • pointUnitForm ((jp ≫ ι₁ ≫ 𝟙 (X j)) ≫ sX j) m := by
    obtain ⟨ρ₀, ⟨ρa, ⟨-, hρa⟩, ρb, hrb, hρb⟩, ρ', hr'', hρ'⟩ :=
      (R.isIteratedResidue j F' 0 (s j) hS').rec'
    have es : sX j = 𝟙 (X j) ≫ sX j := (Category.id_comp _).symm
    have e₃ : ι₁ ≫ sX j = ι₁ ≫ 𝟙 (X j) ≫ sX j := by rw [Category.id_comp]
    have he1 := IsPoincareResidue.of_heq ι₁ es (τ' := ρa)
      (ρ' := cast (congrArg (fun s : S₁ ⟶ Spec (.of k) => RationalPluriForms s 1 (m : ℤ)) e₃) ρ₁)
      hρa.symm (cast_heq _ _).symm hres1
    have hu1 := IsPoincareResidue.unique h1 hrb he1
    have hρ₀ : HEq ρ₀ ρ₁ := hρb.trans (by rw [hu1]; exact cast_heq _ _)
    have hr2 := IsPoincareResidue.of_heq jp e₂.symm (τ' := ρ₀)
      (ρ' := e • pointUnitForm (jp ≫ (ι₁ ≫ 𝟙 (X j)) ≫ sX j) m) hρ₀.symm
      (pointUnitForm_smul_heq (by simp) e m) hres2
    have hu2 := IsPoincareResidue.unique hp hr'' hr2
    exact eq_of_heq (hρ'.trans (by rw [hu2]; exact pointUnitForm_smul_heq (by simp) e m))
  haveI : LocallyOfFiniteType ((jq ≫ ι ≫ 𝟙 (X i)) ≫ sX i) :=
    (StratumAdjunctionData.step F1 jq Bq hq).isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType ((jp ≫ ι₁ ≫ 𝟙 (X j)) ≫ sX j) :=
    F'.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨σ₀⟩ := nonempty_functionFieldEquiv_of_topologicalKrullDim_eq_zero
    ((jq ≫ ι ≫ 𝟙 (X i)) ≫ sX i) ((jp ≫ ι₁ ≫ 𝟙 (X j)) ≫ sX j) (by exact_mod_cast hS)
    (by exact_mod_cast hS')
  refine ⟨S', jp ≫ ι₁ ≫ 𝟙 (X j), BS', F', by simp [hF', StratumAdjunctionData.length], hS', σ₀, ?_⟩
  rw [hXj_side, hXi_side, map_smul, pluriformPullback_pointUnitForm (by exact_mod_cast hS)
    (by exact_mod_cast hS')]

/-! ### Assembly -/

/-- **Residues at points of an exceptional floor curve agree.** At every zero-dimensional stratum
`q` of `X_i` on `P`, the iterated residues of `u = σ^* s_j` and of `s_i` along `(P, q)` agree. -/
private theorem toFun_step_step_eq_of_isExceptional (R : ResidueRestriction sX B 2 m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) 2 m (B i))
    (hu : (u : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional)
    {S : Scheme.{0}} {jq : S ⟶ T} {Bq : QDivisor S}
    (hq : IsAdjunctionStep ((ι ≫ 𝟙 (X i)) ≫ sX i) BT jq Bq)
    (hS : topologicalKrullDim S = (0 : ℕ)) :
    R.toFun i (.step (.step (.refl h) ι BT hι) jq Bq hq) 0 u =
      R.toFun i (.step (.step (.refl h) ι BT hι) jq Bq hq) 0 (s i) := by
  obtain ⟨S', ι', BS', F', hlen', hS', σ₀, hσ₀⟩ :=
    exists_toFun_eq_pluriformPullback_of_isExceptional R σ hσ u hu h hι P hP D hDv hD hq hS
  set F := StratumAdjunctionData.step (.step (.refl h) ι BT hι) jq Bq hq
  haveI := F.isIntegral_stratum
  haveI := F.isNormal_stratum
  haveI := F.isLocallyNoetherian_stratum
  haveI := F'.isIntegral_stratum
  haveI := F'.isNormal_stratum
  haveI := F'.isLocallyNoetherian_stratum
  have hcrep := isCrepantBirationalMap_of_topologicalKrullDim_eq_zero (by exact_mod_cast hS)
    (by exact_mod_cast hS') Bq BS' σ₀
  rw [← hσ₀]
  exact hs i j F F' 0 (by simp [F, StratumAdjunctionData.length]) hlen' hS hS' σ₀ hcrep

/-- **Residues along an exceptional floor curve are determined at a point.** In the situation of
`toFun_step_refl_eq_of_isExceptional_of_isCrepantBirationalMap`, there is a zero-dimensional
stratum `q` on `P` such that a section of `m(K_{X_i} + B_i)` whose iterated residue along
`(P, q)` vanishes has residue zero along `P`. -/
private theorem exists_point_toFun_eq_zero_imp_of_isExceptional (R : ResidueRestriction sX B 2 m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) [IsIntegral T]
    (hT : topologicalKrullDim T = (1 : ℕ)) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    ∃ (S : Scheme.{0}) (jq : S ⟶ T) (Bq : QDivisor S)
      (hq : IsAdjunctionStep ((ι ≫ 𝟙 (X i)) ≫ sX i) BT jq Bq),
      topologicalKrullDim S = (0 : ℕ) ∧ ∀ w : logPluricanonicalSections (sX i) 2 m (B i),
        R.toFun i (.step (.step (.refl h) ι BT hι) jq Bq hq) 0 w = 0 →
          R.toFun i (.step (.refl h) ι BT hι) 1 w = 0 := by
  have hPi := R.setting.isPair i
  haveI := hPi.charZero
  set F1 := StratumAdjunctionData.step (.refl h) ι BT hι with hF1
  haveI := F1.isLocallyNoetherian_stratum
  haveI := F1.isNormal_stratum
  obtain ⟨ρ, hline, S, jq, Bq, hq, _, hS, r, hr0, hr⟩ :=
    exists_line_and_point_of_isExceptional R σ hσ h hι hT P hP D hDv hD
  refine ⟨S, jq, Bq, hq, hS, fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := hline w
  haveI : LocallyOfFiniteType ((ι ≫ 𝟙 (X i)) ≫ sX i) := F1.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨ρ₀, h₀, ρ', hr', hρ'⟩ :=
    (R.isIteratedResidue i (.step F1 jq Bq hq) 0 w hS).rec'
  have e₀ : ρ₀ = R.toFun i F1 1 w :=
    IsIteratedResidueRec.unique F1 h₀ (R.isIteratedResidue i F1 1 w hT).rec'
  rw [e₀, hc] at hr'
  have e' : ρ' = c • r := IsPoincareResidue.unique hq hr' (hr.const_smul _ _ c)
  have hz : ρ' = 0 := RationalPluriForms.eq_zero_of_heq (Category.assoc _ _ _) hρ' hw
  rw [hz, RationalPluriForms.smul_def] at e'
  have hc0 : c = 0 := by
    letI := functionFieldAlgebra (jq ≫ (ι ≫ 𝟙 (X i)) ≫ sX i)
    rcases smul_eq_zero.mp e'.symm with h0 | h0
    · exact (map_eq_zero_iff _ (algebraMap k _).injective).mp h0
    · exact absurd h0 hr0
  rw [hc, hc0, zero_smul]

/-- **Floor curves exceptional for a crepant map.** If `σ` carries the valuation of the floor
curve `P ⊆ X_i` to a divisor `D` exceptional over `X_j`, the residue restrictions of
`u = σ^* s_j` and of `s_i` to `P` agree. -/
theorem toFun_step_refl_eq_of_isExceptional_of_isCrepantBirationalMap
    (R : ResidueRestriction sX B 2 m) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) 2 m (B i))
    (hu : (u : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) [IsIntegral T] (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (D : DivisorOver k (sX j))
    (hDv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g)) (hD : D.IsExceptional) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  have hPi := R.setting.isPair i
  haveI := hPi.charZero
  have he1 : e = 1 := by
    have := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq i)
      (StratumAdjunctionData.step (.refl h) ι BT hι) he
    simp only [StratumAdjunctionData.length] at this
    omega
  subst he1
  obtain ⟨S, jq, Bq, hq, hS, hinj⟩ :=
    exists_point_toFun_eq_zero_imp_of_isExceptional R σ hσ h hι he P hP D hDv hD
  have hpt := toFun_step_step_eq_of_isExceptional R σ hσ hs u hu h hι P hP D hDv hD hq hS
  have := hinj (u - s i) (by rw [map_sub, hpt, sub_self])
  rwa [map_sub, sub_eq_zero] at this

end MMP.Fourfold
