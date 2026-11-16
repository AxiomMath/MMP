module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.MMP.Fourfold.Scaling.BirationalTermination
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
public import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
public import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Positivity.RelativeEffectiveAdjoint
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Specified extraction on a quasi-projective klt fourfold

Let `(S, C)` be an effective rational klt pair on a normal quasi-projective complex fourfold `S`,
and let `I` be a finite set of normalized divisorial valuations of `k(S)`, exceptional over `S`,
with log discrepancy `a(s; S, C) ≤ 1` for `s ∈ I` (that is, `I ⊆ I(S, C)`). Then there is a
projective birational morphism `q : V ⟶ S` from a `ℚ`-factorial normal variety `V` whose
exceptional prime divisors are exactly the centres `E_s = c_V(s)`, `s ∈ I`; the effective rational
boundary `C_V = q⁻¹_* C + ∑_{s ∈ I} (1 - a(s; S, C)) E_s` makes `(V, C_V)` klt, and
`K_V + C_V = q^*(K_S + C)`. For `I = ∅` the morphism `q` has no exceptional divisor: it is a small
projective `ℚ`-factorialization.

## Main results

* `MMP.Fourfold.exists_specifiedExtraction_of_isQuasiProjectiveVariety`: the extraction.

## Implementation notes

* As in `MMP.Fourfold.FourfoldCrepantJunction`, the variety `V` lives over `ℂ` through
  `q ≫ s_S`, and `E_s = c_V(s)` is stated as `ord_{E_s} = s` for the divisor `(V, q, E_s)` over
  `S`; the bijection of `I` onto the `q`-exceptional prime divisors is injectivity of `s ↦ E_s`
  together with `MMP.Mori.RationalMap.IsExceptional` holding exactly on its range.
* The log discrepancies `a(s; S, C)` enter through `MMP.Fourfold.IsValuationLogDiscrepancy`.
* `K_V + C_V = q^*(K_S + C)`, with `K_V` the canonical divisor of `V` matching `K_S`, says that
  `C_V` is the crepant boundary of `(S, C)` on `V` (`MMP.Mori.IsCrepantBoundary`); it is stated for
  every canonical divisor `K` of `S`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_thm_fourfold_quasiprojective_specified_extraction_4

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-- A scheme separated over `Spec ℂ` is separated over the terminal scheme. -/
private theorem isSeparated_terminal {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from _ from Subsingleton.elim _ _]
  infer_instance

/-- A morphism inducing a surjection of function fields makes `v ↦ v ∘ f^*` injective. -/
private theorem eq_of_comap_functionFieldMap_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] ⦃v₁ v₂ : Valuation X.functionField Γ₀⦄
    (h : v₁.comap (functionFieldMap f) = v₂.comap (functionFieldMap f)) : v₁ = v₂ := by
  ext t
  obtain ⟨u, rfl⟩ := hf t
  exact congrArg (fun v => v u) h

/-! ### The boundary of an extraction -/

section Boundary

variable {X Y : Scheme.{0}} {R : Type*} [AddCommMonoid R] {g : Y ⟶ X}

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`. -/
private theorem coeff_inverseTransformDivisor_of_eq_some {D : MMP.Mori.PrimeDivisor X}
    {F : MMP.Mori.PrimeDivisor Y} (hD : inverseTransformPrimeDivisor g D = some F)
    (B : DivisorWithCoeffs R X) : (inverseTransformDivisor g B).coeff F = B.coeff D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

/-- A prime divisor of `Y` which is the inverse transform of no prime divisor of `X` has
coefficient zero in every inverse transform `g⁻¹_* B`. -/
private theorem coeff_inverseTransformDivisor_eq_zero {F : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P, inverseTransformPrimeDivisor g P ≠ some F) (B : DivisorWithCoeffs R X) :
    (inverseTransformDivisor g B).coeff F = 0 := by
  classical
  induction B using Finsupp.induction_linear with
  | zero => simp [DivisorWithCoeffs.coeff]
  | add B B' hB hB' =>
    rw [map_add, DivisorWithCoeffs.coeff, Finsupp.add_apply, ← DivisorWithCoeffs.coeff,
      ← DivisorWithCoeffs.coeff, hB, hB', add_zero]
  | single P r =>
    rw [inverseTransformDivisor_single]
    rcases hP : inverseTransformPrimeDivisor g P with _ | E
    · rfl
    · exact Finsupp.single_eq_of_ne fun hEF => h P (hEF ▸ hP)

/-- The inverse transform of an effective divisor is effective. -/
private theorem inverseTransformDivisor_nonneg (g : Y ⟶ X) {D : QDivisor X}
    (hD : ∀ P, 0 ≤ D.coeff P) (P : MMP.Mori.PrimeDivisor Y) :
    0 ≤ (inverseTransformDivisor g D).coeff P := by
  classical
  by_cases h : ∃ Q, inverseTransformPrimeDivisor g Q = some P
  · obtain ⟨Q, hQ⟩ := h
    rw [coeff_inverseTransformDivisor_of_eq_some hQ]
    exact hD Q
  · simp only [not_exists] at h
    rw [coeff_inverseTransformDivisor_eq_zero h]

end Boundary

section Extraction

variable {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  {sS : S ⟶ Spec (.of ℂ)}
  {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]

/-- The log discrepancy of a valuation is unique. -/
private theorem IsValuationLogDiscrepancy.eq {B : QDivisor S}
    {ξ : Valuation S.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : IsValuationLogDiscrepancy sS B ξ a)
    (h' : IsValuationLogDiscrepancy sS B ξ a') : a = a' := by
  obtain ⟨n, D, -, hv, h⟩ := h
  obtain ⟨n', D', -, hv', h'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hv.trans hv'.symm)

/-- The composite `(W, g ≫ q, F)` over `S` of a proper divisor `(W, g, F)` over `V`, a proper
divisor whose valuation restricts that of `(W, g, F)` along `q^*`. -/
private theorem exists_comp_divisorOver (q : V ⟶ S) (hq : IsBirationalMorphism q) [IsProper q]
    (D : DivisorOver ℂ (q ≫ sS)) (hD : IsProper D.f) :
    haveI := hq.isDominant
    ∃ E : DivisorOver ℂ sS, IsProper E.f ∧
      E.valuation = D.valuation.comap (functionFieldMap q) := by
  haveI := hq.isDominant
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := hD
  have hb : IsBirationalMorphism (D.f ≫ q) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational q D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hq)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  have hY : IsNormalVariety ℂ ((D.f ≫ q) ≫ sS) := by
    rw [Category.assoc]; exact D.isNormalVariety
  refine ⟨⟨D.Y, D.f ≫ q, hY, hb, D.E⟩, (inferInstance : IsProper (D.f ≫ q)), ?_⟩
  haveI : IsDominant (D.f ≫ q) := hb.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ q) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap q t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

end Extraction

/-- Given a projective birational extraction `q : V ⟶ S` from a `ℚ`-factorial variety whose
exceptional primes are exactly the centres `E_s` of the valuations `s ∈ I`, the boundary
`C_V = q⁻¹_* C + ∑ (1 - a_s) E_s` is the crepant boundary of `(S, C)`, effective and klt. -/
private theorem boundary_of_extraction
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P)
    (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {n : ℕ} {K : Divisor S} (hK : K.IsCanonicalDivisor sS n)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (q : V ⟶ S) (E : I → MMP.Mori.PrimeDivisor V)
    (hV : IsQFactorial (q ≫ sS)) (hq : IsBirationalMorphism q) (hqp : IsProjectiveMorphism q)
    (hval : ∀ s : I, (⟨V, q, hV.1, hq, E s⟩ : DivisorOver ℂ sS).valuation = s)
    (hinj : Function.Injective E)
    (hexc : ∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) q.toRationalMap P ↔ P ∈ Set.range E) :
    ∃ (a : I → ℚ) (CV : QDivisor V),
      (∀ s : I, IsValuationLogDiscrepancy sS C s (a s)) ∧
      CV = inverseTransformDivisor q C + ∑ s : I, Finsupp.single (E s) (1 - a s) ∧
      (∀ P, 0 ≤ CV.coeff P) ∧
      IsKltPair (q ≫ sS) CV ∧
      IsCrepantBoundary sS n K C q hV.1 hq CV := by
  classical
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hqp
  have hP : MMP.Mori.IsPair sS C := hklt.1.isPair
  have hSn : IsNormalVariety ℂ sS := hP.1
  -- the divisors `(V, q, E_s)` over `S` and their discrepancies
  let D : I → DivisorOver ℂ sS := fun s => ⟨V, q, hV.1, hq, E s⟩
  choose c hc using fun s => MMP.Positivity.IsPair.exists_isDiscrepancy hP hK (D s)
  have hla : ∀ s : I, IsValuationLogDiscrepancy sS C s ((1 + c s : ℚ) : ℝ) := fun s =>
    ⟨n, D s, inferInstanceAs (IsProper q), hval s, by
      push_cast
      exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hc s)
        (inferInstanceAs (IsProper q))⟩
  have hale : ∀ s : I, 1 + c s ≤ 1 := fun s => by
    obtain ⟨-, a', ha', ha'1⟩ := hI s.2
    have := IsValuationLogDiscrepancy.eq (hla s) ha'
    exact_mod_cast this ▸ ha'1
  -- the crepant boundary
  obtain ⟨⟨CV, hCV, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP hK q hV.1 hq
  have hCVE : ∀ s : I, CV.coeff (E s) = 1 - (1 + c s) := fun s => by
    have := (hCV (E s)).eq (hc s)
    linarith
  obtain ⟨hCVeq, -⟩ := IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional hP hCV
  have hfilter : Finsupp.filter (fun P => RationalMap.IsExceptional (X := V) q.toRationalMap P) CV =
      ∑ s : I, Finsupp.single (E s) (1 - (1 + c s)) := by
    refine Finsupp.ext fun P => ?_
    rw [Finsupp.filter_apply, Finsupp.finset_sum_apply]
    by_cases hPE : P ∈ Set.range E
    · obtain ⟨t, rfl⟩ := hPE
      rw [if_pos ((hexc _).mpr ⟨t, rfl⟩), Finset.sum_eq_single t
        (fun u _ hut => Finsupp.single_eq_of_ne (hinj.ne hut).symm) (by simp),
        Finsupp.single_eq_same]
      exact hCVE t
    · rw [if_neg (fun h => hPE ((hexc P).mp h))]
      exact (Finset.sum_eq_zero fun u _ =>
        Finsupp.single_eq_of_ne (fun h => hPE ⟨u, h.symm⟩)).symm
  have hCVf : CV = inverseTransformDivisor q C + ∑ s : I, Finsupp.single (E s) (1 - (1 + c s)) := by
    rw [← hfilter]; exact hCVeq
  have hCV0 : ∀ P, 0 ≤ CV.coeff P := by
    intro P
    rw [hCVf]
    change 0 ≤ (inverseTransformDivisor q C).coeff P +
      (∑ s : I, Finsupp.single (E s) (1 - (1 + c s)) : QDivisor V) P
    rw [Finsupp.finset_sum_apply]
    refine add_nonneg (inverseTransformDivisor_nonneg q hC P) (Finset.sum_nonneg fun s _ => ?_)
    rw [Finsupp.single_apply]
    split_ifs
    · linarith [hale s]
    · exact le_rfl
  refine ⟨fun s => 1 + c s, CV, hla, hCVf, hCV0, ?_, hCV⟩
  · -- `(V, C_V)` is crepant over `(S, C)`, so its log discrepancies are those of `(S, C)`
    haveI : CompactSpace S := by
      haveI := hSn.1.toQuasiCompact
      exact QuasiCompact.compactSpace_of_compactSpace sS
    haveI : CompactSpace V := by
      haveI := hV.1.1.toQuasiCompact
      exact QuasiCompact.compactSpace_of_compactSpace (q ≫ sS)
    have hdimV : topologicalKrullDim V = n := by
      rw [← hK.topologicalKrullDim_eq]
      haveI := hSn.1
      haveI := hV.1.1
      exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (q ≫ sS) hq).symm
    obtain ⟨KV, hKV⟩ := MMP.Mori.exists_isCanonicalDivisor (q ≫ sS) hV.1 hdimV
    obtain ⟨hPV, hinv⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP q hV.1 hq hK hKV
      (Or.inl hCV)
    refine ⟨⟨hklt.1.isAlgClosed, hklt.1.charZero, hPV, hCV0⟩, fun n' D' a hD' => ?_⟩
    have hn' : n' = n := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD').symm.trans
        hdimV
      exact_mod_cast this
    subst hn'
    obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPV hKV D'
    obtain ⟨hD'p, rfl⟩ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc' a).mp
      hD'
    obtain ⟨E', hE'p, hE'v⟩ := exists_comp_divisorOver q hq D' hD'p
    exact hklt.2 n' E' _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
      ((hinv D' E' hE'v c').mp hc') hE'p)

/-! ### Compactification -/

/-- A normal quasi-projective complex variety is a dense open subscheme of a normal projective
complex variety. -/
private theorem exists_normal_projective_compactification {U : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} (hUn : IsNormalVariety ℂ sU)
    (hUq : IsQuasiProjectiveVariety ℂ sU) :
    ∃ (Ub : Scheme.{0}) (_ : IsIntegral Ub) (_ : IsLocallyNoetherian Ub) (_ : IsNormal Ub)
      (_ : CompactSpace Ub) (sUb : Ub ⟶ Spec (.of ℂ)) (ι : U ⟶ Ub),
      IsOpenImmersion ι ∧ ι ≫ sUb = sU ∧ MMP.Mori.IsProjectiveVariety ℂ sUb ∧
        IsNormalVariety ℂ sUb := by
  obtain ⟨hUv, -⟩ := hUn
  have hqp : IsQuasiProjective sU := ((isQuasiProjectiveVariety_iff ℂ sU).mp hUq).2
  obtain ⟨n, i, hi, hiqc, hip⟩ := isHQuasiProjective_of_isQuasiProjective sU
    (Stacks.Ample.unitModule (Spec (.of ℂ)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))) hqp
  have : IsImmersion i := hi
  have : QuasiCompact i := hiqc
  set π := projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ) with hπ
  have hπp : IsProjectiveMorphism π := ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  have : IsProper π := isProper_of_isProjectiveMorphism π hπp
  have hNagata : IsNagataScheme (projectiveSpaceOver n (Spec (.of ℂ))) :=
    isNagataScheme_of_locallyOfFiniteType_over_field ℂ π
  have hfin : IsFinite i.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType i hNagata
  have hcomp : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite :=
    fun V hV => by
      have : IsNoetherian V :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp hV }
      exact finite_irreducibleComponents_of_isNoetherian
  have hproj : IsProjective (i.fromNormalization ≫ π) :=
    (Stacks.FiniteMorphismProjective.isProjective_of_isFinite i.fromNormalization).comp
      hπp.isProjective
  have h2 : IsProjectiveMorphism (i.fromNormalization ≫ π) :=
    isProjectiveMorphism_of_isProjective _ (Stacks.Ample.unitModule (Spec (.of ℂ)))
      (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))) hproj
  have hnorm : IsNormal i.normalization := isNormal_normalization i hcomp
  have : IsProper (i.fromNormalization ≫ π) := isProper_of_isProjectiveMorphism _ h2
  have hv : AlgebraicGeometry.IsVariety ℂ (i.fromNormalization ≫ π) := { }
  have : IsIntegral i.normalization := inferInstance
  have : IsLocallyNoetherian i.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (i.fromNormalization ≫ π)
  have : CompactSpace i.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (i.fromNormalization ≫ π)
  refine ⟨i.normalization, inferInstance, inferInstance, hnorm, inferInstance,
    i.fromNormalization ≫ π, i.toNormalization, inferInstance, ?_,
    (MMP.Mori.isProjectiveVariety_iff _ _).mpr ⟨hv, h2⟩, ⟨hv, hnorm⟩⟩
  rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hip]

/-! ### The compactification -/

/-- The dimension of a variety is that of a dense open subscheme. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {S Sb : Scheme.{0}}
    [IsIntegral Sb] {sSb : Sb ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sSb] [Nonempty S]
    (ι : S ⟶ Sb) [IsOpenImmersion ι] : topologicalKrullDim S = topologicalKrullDim Sb := by
  rw [topologicalKrullDim_eq_of_isOpen ℂ Sb sSb _ ι.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _)]
  exact ι.isOpenEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- An open immersion of a nonempty scheme into an irreducible scheme is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion' {X Y : Scheme.{0}} [IrreducibleSpace Y]
    [Nonempty X] (f : X ⟶ Y) [IsOpenImmersion f] : IsBirationalMorphism f := by
  haveI : IsDominant f := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion f
  haveI : IsOpenImmersion ((⊤ : X.Opens).ι ≫ f) := inferInstance
  exact isBirationalMorphism_of_isOpenImmersion f ⊤ (by simp)

/-- The composite `(Y, g ≫ ι, F)` of a divisor `(Y, g, F)` over `S` with a birational morphism
`ι : S ⟶ S̄`, a divisor over `S̄` whose valuation restricts that of `(Y, g, F)` along `ι^*`. -/
private noncomputable def compDivisorOver {S Sb : Scheme.{0}} [IsIntegral S] [IsIntegral Sb]
    [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian Sb] [IsNormal Sb]
    {sS : S ⟶ Spec (.of ℂ)} {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι) (D : DivisorOver ℂ sS) : DivisorOver ℂ sSb :=
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  { Y := D.Y
    f := D.f ≫ ι
    isNormalVariety := by rw [Category.assoc, hιs]; exact D.isNormalVariety
    isBirationalMorphism := MMP.Mori.isBirationalMorphism_comp D.isBirationalMorphism hι
    E := D.E }

private theorem valuation_compDivisorOver {S Sb : Scheme.{0}} [IsIntegral S] [IsIntegral Sb]
    [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian Sb] [IsNormal Sb]
    {sS : S ⟶ Spec (.of ℂ)} {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι) (D : DivisorOver ℂ sS) :
    haveI := hι.isDominant
    (compDivisorOver ι hιs hι D).valuation = D.valuation.comap (functionFieldMap ι) := by
  haveI := hι.isDominant
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : IsDominant (D.f ≫ ι) := (compDivisorOver ι hιs hι D).isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ ι) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap ι t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- A valuation of `k(S)` with a log discrepancy over `(S, C)` is the valuation of a divisor over
`S`; transported to `k(S̄)`, it has a nonempty centre on `S̄`. -/
private theorem hasNonemptyCenter_comap {S Sb : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (hSbn : IsNormalVariety ℂ sSb) (ι : S ⟶ Sb) (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι) {C : QDivisor S}
    {ξ : Valuation S.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (h : IsValuationLogDiscrepancy sS C ξ a) :
    haveI := hι.isDominant
    MMP.Flips.HasNonemptyCenter ℂ sSb (ξ.comap (functionFieldMap ι)) := by
  haveI := hι.isDominant
  obtain ⟨n, D, -, rfl, -⟩ := h
  set D' := compDivisorOver ι hιs hι D
  have hv := valuation_compDivisorOver ι hιs hι D
  rw [← hv]
  haveI := D'.isIntegral
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  haveI := D'.isDominant
  refine ⟨MMP.Fourfold.SNCWeight.Restriction.isDivisorOfFunctionField_comap_primeDivisor sSb D'.f D'.isNormalVariety
    D'.isBirationalMorphism.functionFieldMap_bijective D'.E, ?_⟩
  haveI : LocallyOfFiniteType sSb := hSbn.1.toLocallyOfFiniteType
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hSbn D'
  exact ⟨E, hE⟩

/-! ### Restriction to an open subscheme -/

section RestrictOpen

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

private theorem primeDivisorMap_support_inter_nonempty (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] {V : X.Opens} (W : MMP.Mori.PrimeDivisor U.toScheme)
    (hW : (W.support ∩ U.ι ⁻¹ᵁ V).Nonempty) :
    ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ V).Nonempty := by
  rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff]
  exact (congrArg (· ∈ V) (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W)).mpr
    ((W.genericPoint_mem_iff _).2 hW)

/-- The restriction of a Cartier divisor to a dense open subscheme is Cartier. -/
private theorem isCartier_restrictOpen {D : Divisor X} (h : D.IsCartier) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : Divisor.IsCartier (D.restrictOpen U) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := h (U.ι x)
  obtain ⟨g, hg, hφg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap U.ι)).2 hg)
  refine ⟨U.ι ⁻¹ᵁ V, hxV, φ', fun W hW => ?_⟩
  have hP := primeDivisorMap_support_inter_nonempty U W hW
  rw [DivisorWithCoeffs.coeff_restrictOpen, hφ _ hP, hφg, hφ',
    MMP.Positivity.ord_functionFieldMap_of_isIso U.ι W _
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- The extension by closure of a divisor of an open subscheme restricts back to it. -/
private theorem restrictOpen_mapDomain {R : Type*} [AddCommMonoid R] (U : X.Opens)
    (D : DivisorWithCoeffs R U.toScheme) :
    DivisorWithCoeffs.restrictOpen U
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap U.ι) D) = D := by
  ext W
  rw [DivisorWithCoeffs.coeff_restrictOpen]
  exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective U.ι) D W

/-- Restriction of divisors to an open subscheme commutes with integer multiples. -/
private theorem restrictOpen_zsmul (U : X.Opens) (m : ℤ) (D : Divisor X) :
    DivisorWithCoeffs.restrictOpen U (m • D) = m • DivisorWithCoeffs.restrictOpen U D :=
  Finsupp.ext fun W => by
    change ((m • D).restrictOpen U).coeff W = (m • D.restrictOpen U).coeff W
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_restrictOpen,
      DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.coeff_smul]

/-- **`ℚ`-factoriality restricts to open subschemes.** -/
private theorem isQFactorial_restrictOpen {sX : X ⟶ Spec (.of ℂ)} (h : IsQFactorial sX)
    (U : X.Opens) [Nonempty U] : IsQFactorial (U.ι ≫ sX) := by
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  refine ⟨h.1.restrictOpen U, fun D => ?_⟩
  obtain ⟨m, hm, hmD⟩ := h.2 (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap U.ι) D)
  refine ⟨m, hm, ?_⟩
  have := isCartier_restrictOpen hmD U
  rwa [restrictOpen_zsmul, restrictOpen_mapDomain] at this

end RestrictOpen

/-! ### Restriction of the log minimal model over `S` -/

/-- The valuation of a prime divisor `P` of `X`, viewed as a divisor over `X`, is `ord_P`. -/
private theorem valuation_ofPrimeDivisor {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor ℂ hX P).valuation = P.divisorialValuation :=
  Valuation.ext fun φ => by
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [functionFieldMap_id_apply]

/-- A prime divisor of a normal variety `Y` is determined by its valuation read in `k(X)` along a
morphism `f : Y ⟶ X` inducing a surjection of function fields. -/
private theorem eq_of_valuationOver_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    ⦃D₁ D₂ : MMP.Mori.PrimeDivisor Y⦄ (h : D₁.valuationOver f = D₂.valuationOver f) :
    D₁ = D₂ := by
  have hdiv : D₁.divisorialValuation = D₂.divisorialValuation := by
    ext t
    obtain ⟨u, rfl⟩ := hf t
    simpa only [MMP.Mori.PrimeDivisor.valuationOver_apply] using congrArg (fun v => v u) h
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1
      (D := DivisorOver.ofPrimeDivisor ℂ hY D₁) (D' := DivisorOver.ofPrimeDivisor ℂ hY D₂)
      (by rw [valuation_ofPrimeDivisor, valuation_ofPrimeDivisor, hdiv]))

/-- An open immersion of integral schemes induces an isomorphism of function fields. -/
private theorem functionFieldMap_bijective_of_isOpenImmersion {W Y : Scheme.{0}} [IsIntegral W]
    [IsIntegral Y] (f : W ⟶ Y) [IsOpenImmersion f] [IsDominant f] :
    Function.Bijective (functionFieldMap f) := by
  rw [functionFieldMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- A representative `g` of a rational map `φ` over `Z` (`q ∘ φ = π`) commutes with the
structure morphisms on its domain: `q ∘ g = π|_{dom g}`. -/
private theorem hom_comp_eq_of_isOver {W Y Z : Scheme.{0}} [IsReduced W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (π : W ⟶ Z) (q : Y ⟶ Z) {φ : W.RationalMap Y}
    (hover : MMP.Flips.RationalMap.IsOver π q φ) (g : W.PartialMap Y)
    (hg : g.toRationalMap = φ) : g.hom ≫ q = g.domain.ι ≫ π := by
  have heq : W.homOfLE (inf_le_left : g.domain ⊓ ⊤ ≤ g.domain) ≫ g.hom ≫ q =
      W.homOfLE inf_le_right ≫ W.topIso.hom ≫ π := by
    have := (Scheme.PartialMap.equiv_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp
        ((Scheme.RationalMap.compHom_toRationalMap g q).trans ((congrArg _ hg).trans hover)))
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.compHom_hom,
      Scheme.Hom.toPartialMap_hom] at this
    exact this
  have h := W.homOfLE (le_inf le_rfl le_top : g.domain ≤ g.domain ⊓ ⊤) ≫= heq
  rwa [Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_rfl, Category.id_comp, Scheme.topIso_hom,
    Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_ι_assoc] at h

/-- **The base of a birational map over a birational morphism is birational.** -/
private theorem isBirationalMorphism_of_isOver {W Y Z : Scheme.{0}} [IsIntegral W] [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (π : W ⟶ Z) (q : Y ⟶ Z) [IsProper q]
    (hπ : IsBirationalMorphism π) {φ : W.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hover : MMP.Flips.RationalMap.IsOver π q φ) :
    IsBirationalMorphism q := by
  have : IsDominant π := hπ.isDominant
  obtain ⟨e, he⟩ := hφ
  set h : e.source.toScheme ⟶ Y := e.iso.hom ≫ e.target.ι
  have hc : h ≫ q = e.source.ι ≫ π := hom_comp_eq_of_isOver π q hover e.toPartialMap he
  haveI : Nonempty e.source := ⟨⟨_, e.dense_source.nonempty.some_mem⟩⟩
  haveI : IsDominant h := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant e.source.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant q := by
    constructor
    have : IsDominant (e.source.ι ≫ π) := inferInstance
    refine Dense.mono ?_ (IsDominant.denseRange (f := e.source.ι ≫ π))
    rintro _ ⟨x, rfl⟩
    exact ⟨h x, by rw [← Scheme.Hom.comp_apply, hc]⟩
  have hbh := functionFieldMap_bijective_of_isOpenImmersion h
  have hbO := functionFieldMap_bijective_of_isOpenImmersion e.source.ι
  have hbq : Function.Bijective (functionFieldMap q) := by
    refine ⟨(functionFieldMap q).injective, fun t => ?_⟩
    obtain ⟨s, hs⟩ := (hbO.comp hπ.functionFieldMap_bijective).surjective (functionFieldMap h t)
    refine ⟨s, hbh.injective ?_⟩
    rwa [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hc,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hqη : q (genericPoint Y) = genericPoint Z := map_genericPoint_of_isDominant q
  have hbir : IsBirational q := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hqη]
      exact Set.bijOn_singleton.mpr rfl
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      have : IsIso ((Z.presheaf.stalkCongr (Inseparable.of_eq hqη.symm)).hom ≫
          q.stalkMap (genericPoint Y)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr hbq
      exact IsIso.of_isIso_comp_left (Z.presheaf.stalkCongr (Inseparable.of_eq hqη.symm)).hom _
  have hbid : IsBirational (𝟙 Y) := by
    refine ⟨?_, fun x _ => inferInstance⟩
    simpa using Set.bijOn_id (genericPoints Y)
  simpa using isBirationalMorphism_comp_of_isBirational q (𝟙 Y) hbir hbid

/-! ### Intersection numbers on an open subscheme -/

section IntersectionRestrict

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (U : X.Opens) [IsIntegral U]
  [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] [IsDominant U.ι]

/-- The restriction to a dense open `U` of a Cartier divisor is its pull-back along `U ⟶ X`. -/
private theorem isPullback_restrictOpen {N : Divisor X} (hN : N.IsCartier) :
    N.IsPullback U.ι (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
      (N.restrictOpen U) := by
  obtain ⟨N', hN'⟩ := hN.exists_isPullback (f := U.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
  have hiso : ∀ P : MMP.Mori.PrimeDivisor U, IsIso (U.ι.stalkMap P.genericPoint) := fun P =>
    inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
  have : N' = N.restrictOpen U := by
    ext P
    change N'.coeff P = (N.restrictOpen U).coeff P
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact MMP.Positivity.coeff_eq_of_isPullback P _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm hN hN'
  exact this ▸ hN'

/-- A proper curve `C` of an open `U ⊆ X`, `X` separated over `k`, is a proper curve `Γ` of `X`,
with the same generic point and isomorphic to `C` over `X`. -/
private theorem exists_properCurve_of_opens [IsSeparated sX] (C : ProperCurve (U.ι ≫ sX)) :
    ∃ (Γ : ProperCurve sX) (e : C.scheme ≅ Γ.scheme),
      Γ.point = U.ι C.point ∧ e.hom ≫ Γ.ι = C.ι ≫ U.ι := by
  have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have : IsProper (C.ι ≫ U.ι) := IsProper.of_comp (C.ι ≫ U.ι) sX
  have hrange : Set.range (C.ι ≫ U.ι) = U.ι '' closure {C.point} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    congr 1
    change Set.range (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set U))).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hcl : closure ({U.ι C.point} : Set X) ⊆ Set.range U.ι := by
    refine (closure_minimal ?_ (C.ι ≫ U.ι).isClosedMap.isClosed_range).trans ?_
    · rw [Set.singleton_subset_iff, hrange]; exact ⟨C.point, subset_closure rfl, rfl⟩
    · rw [hrange]; exact Set.image_subset_range _ _
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι C.point rfl hcl
  refine ⟨⟨U.ι C.point, ⟨?_, ?_⟩⟩, e, rfl, he⟩
  · rw [← IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact C.dim_eq
  · have : curveSubschemeAtι (U.ι C.point) ≫ sX = e.inv ≫ (C.ι ≫ U.ι) ≫ sX := by
      rw [← he, Category.assoc, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance

variable [QuasiCompact sX] [QuasiCompact (U.ι ≫ sX)]

/-- **Intersection numbers can be computed on a dense open.** For a `ℚ`-Cartier `ℚ`-divisor `L`
on `X`, a proper curve `C` of `U` and the proper curve `Γ` of `X` it is, isomorphic to `C` over
`X`, `(L|_U · C) = (L · Γ)`. -/
private theorem intersectionNumber_restrictOpen (L : QDivisor X) (hL : L.IsQCartier)
    (hLU : QDivisor.IsQCartier (L.restrictOpen U)) (C : ProperCurve (U.ι ≫ sX)) (Γ : ProperCurve sX)
    (e : C.scheme ≅ Γ.scheme) (he : e.hom ≫ Γ.ι = C.ι ≫ U.ι) :
    QDivisor.intersectionNumber k (U.ι ≫ sX) C.ι C.dim_le (L.restrictOpen U) hLU =
      L.intersectionNumber k sX Γ.ι Γ.dim_le hL := by
  have hm := QDivisor.cartierIndex_pos hL
  obtain ⟨N, hN, hNc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hL
  have hp := isPullback_restrictOpen U hNc
  have hNUc : Divisor.IsCartier (N.restrictOpen U) := Divisor.IsPullback.isCartier hp hNc
  have hNU : Divisor.toQDivisor (N.restrictOpen U) =
      ((L.cartierIndex hL : ℕ) : ℤ) • L.restrictOpen U := by
    ext P
    exact congrArg (fun G : QDivisor X => G (OpenWeilRestriction.primeDivisorMap U.ι P)) hN
  rw [QDivisor.intersectionNumber_eq_of_smul k (U.ι ≫ sX) C.ι C.dim_le _ hLU hm _ hNUc hNU,
    QDivisor.intersectionNumber_eq_of_smul k sX Γ.ι Γ.dim_le _ hL hm _ hNc hN]
  congr 2
  have := hNc.isInvertibleModule_divisorialSheaf
  have := hNUc.isInvertibleModule_divisorialSheaf
  have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  change MMP.Mori.degreeOn k (U.ι ≫ sX) C.ι C.dim_le (Divisor.divisorialSheaf (N.restrictOpen U)) =
    MMP.Mori.degreeOn k sX Γ.ι Γ.dim_le N.divisorialSheaf
  rw [degreeOn_eq_of_iso k (U.ι ≫ sX) C.ι C.dim_le
      (Divisor.IsPullback.divisorialSheafIso (hBc := hNc) hp),
    degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι C.ι rfl]
  exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX (C.ι ≫ U.ι) Γ.ι C.dim_le
    Γ.dim_le e he N.divisorialSheaf

end IntersectionRestrict

section PullbackDegree

variable {k : Type} [Field k] {V T : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]
  [QuasiCompact sV] [QuasiCompact sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian T] [IsNormal T]

/-- The pull-back of a Cartier divisor has degree zero on a contracted curve. -/
private theorem degreeOn_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy u hu hD hB Γ hΓ

end PullbackDegree

/-- **A compatible canonical divisor upstairs.** For a proper birational morphism `f : Y → X` of
normal varieties of dimension `n` and a canonical divisor `K_X`, there is a canonical divisor
`K_Y` of `Y` with `f_* K_Y = K_X`: if `K_X = div(ω)`, take `K_Y = div(f^*ω)`. -/
private theorem exists_isCanonicalDivisor_transformDivisor_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (hX : IsNormalVariety ℂ sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety ℂ (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) {K₀ : Divisor Y} (hK₀ : K₀.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ KY : Divisor Y, KY.IsCanonicalDivisor (f ≫ sX) n ∧
      RationalMap.transformDivisor (X := Y) f.toRationalMap KY = KX := by
  have hbij := hf.functionFieldMap_bijective
  have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hKX.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hKX
  have hτ0 := MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero f hbij hd hω0
  refine ⟨divisorOfForm (pullbackRationalPluriForms sX f ω), ?_, Finsupp.ext fun P => ?_⟩
  · have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hτ0
    rw [one_zsmul] at h
    exact hK₀.of_linearlyEquivalent h
  · obtain ⟨E, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [htr]
    change E.ordForm (pullbackRationalPluriForms sX f ω) = KX.coeff P
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq ω, hω]

/-- Relative nefness only sees the structure morphism through its value. -/
private theorem isRelativelyNef_congr_structure {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {s₁ s₂ : X ⟶ Spec (.of ℂ)} (h : s₁ = s₂) [QuasiCompact s₁] [QuasiCompact s₂]
    (f : X ⟶ Y) (D : QDivisor X) : D.IsRelativelyNef s₁ f ↔ D.IsRelativelyNef s₂ f := by
  subst h
  rfl

/-! ### Exceptional prime divisors of a morphism -/

section Exceptional

private theorem topologicalKrullDim_closure_singleton_add_coheight
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [LocallyOfFiniteType sY] (x : Y) :
    topologicalKrullDim (closure {x} : Set Y) + Order.coheight x = topologicalKrullDim Y := by
  let _ : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim ℂ
    (MMP.Intersection.Scheme.Subvariety.ofPoint x)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint] at h
  exact h

/-- With `d + c = n`, the dimension `d` is at most `n - 2` iff the codimension `c` is at least
two. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h' : d + c = n := WithBot.coe_injective h
    lift d to ℕ using (by rintro rfl; simp at h')
    lift c to ℕ using (by rintro rfl; simp at h')
    norm_cast at h'
    rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
      show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe, Nat.cast_le,
      Nat.ofNat_le_cast]
    omega

/-- A proper divisor over `X` is exceptional iff its centre has coheight at least two. -/
private theorem properDivisorOver_isExceptional_iff {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : MMP.Flips.ProperDivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- A prime divisor `E` is exceptional for a morphism `f` iff `f(η_E)` has coheight at least
two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (f : X ⟶ Y) (E : MMP.Mori.PrimeDivisor X) :
    RationalMap.IsExceptional (X := X) f.toRationalMap E ↔
      2 ≤ Order.coheight (f E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hmem : f E.genericPoint ∈ closure (f '' (E.idealSheaf.support : Set X)) :=
    subset_closure ⟨_, (by
      change _ ∈ E.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl), rfl⟩
  refine ⟨fun h => h _ hmem, fun h x hx => h.trans (Order.coheight_anti ?_)⟩
  have hsub : closure (f '' (E.idealSheaf.support : Set X)) ⊆ closure {f E.genericPoint} := by
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨y, hy, rfl⟩
    have : y ∈ closure {E.genericPoint} := by
      change y ∈ E.support at hy
      rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
    exact (specializes_iff_mem_closure.mpr this).map f.continuous |>.mem_closure
  exact (show x ≤ f E.genericPoint from specializes_iff_mem_closure.mpr (hsub hx))

end Exceptional

/-! ### Prime divisors on models birational over a base -/

section Correspondence

/-- The valuation `ord_E ∘ (f ≫ g)^*` is `ord_E ∘ f^*` restricted along `g^*`. -/
private theorem valuationOver_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (E : MMP.Mori.PrimeDivisor X) (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    E.valuationOver (f ≫ g) = (E.valuationOver f).comap (functionFieldMap g) := by
  ext t
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- `ord_E ∘ f^*` is integral on the local ring of `X` at `f(η_E)`. -/
private theorem valuationOver_algebraMap_le_one {X Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] (f : Y ⟶ X) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor Y) (a : X.presheaf.stalk (f E.genericPoint)) :
    E.valuationOver f (algebraMap _ X.functionField a) ≤ 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
  exact ⟨_, rfl⟩

/-- `ord_E ∘ f^*` is positive on the maximal ideal of the local ring of `X` at `f(η_E)`. -/
private theorem valuationOver_algebraMap_lt_one {X Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] (f : Y ⟶ X) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor Y) (a : X.presheaf.stalk (f E.genericPoint))
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (f E.genericPoint))) :
    E.valuationOver f (algebraMap _ X.functionField a) < 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
    (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- If a dominant morphism `f : Y ⟶ X` of normal integral schemes inducing a surjection of
function fields maps the generic point of a prime divisor `E` of `Y` to that of a prime divisor
`P` of `X`, then `ord_E`, read in `k(X)`, is `ord_P`. -/
private theorem valuationOver_eq_of_map_genericPoint {X Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    (E : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor X)
    (h : f E.genericPoint = P.genericPoint) :
    E.valuationOver f = P.divisorialValuation := by
  have := P.isDiscreteValuationRing_localRing
  have h1 : ∀ z, f E.genericPoint = z → ∀ a : X.presheaf.stalk z,
      E.valuationOver f (algebraMap _ X.functionField a) ≤ 1 := by
    rintro z rfl a
    exact valuationOver_algebraMap_le_one f E a
  have h2 : ∀ z, f E.genericPoint = z → ∀ a : X.presheaf.stalk z,
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) →
      E.valuationOver f (algebraMap _ X.functionField a) < 1 := by
    rintro z rfl a ha
    exact valuationOver_algebraMap_lt_one f E a ha
  have h3 : ∃ g, E.valuationOver f g = WithZero.exp (-1) := by
    have := E.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
    obtain ⟨g, hg⟩ := hf (algebraMap E.localRing Y.functionField ϖ)
    exact ⟨g, by rw [MMP.Mori.PrimeDivisor.valuationOver_apply, hg,
      MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_of_irreducible _ hϖ]⟩
  have h3' : ∃ g, P.divisorialValuation g = WithZero.exp (-1) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    exact ⟨_, P.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  exact MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := P.localRing)
    (h1 _ h) (h2 _ h) h3 (fun r => (P.divisorialValuation_le_one_iff _).2 ⟨r, rfl⟩)
    (fun r hr => (P.divisorialValuation_algebraMap_lt_one_iff r).2 hr) h3'

/-- A representative of a birational map of irreducible schemes is dominant. -/
private theorem isDominant_hom_of_isBirational {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] {φ : X.RationalMap Y} (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (g : X.PartialMap Y) (hg : g.toRationalMap = φ) : IsDominant g.hom := by
  obtain ⟨e, he⟩ := hφ
  obtain ⟨U, hU, hUl, hUr, hUe⟩ :=
    Scheme.PartialMap.toRationalMap_eq_iff.mp (hg.trans he.symm)
  haveI : Nonempty X := IrreducibleSpace.toNonempty
  haveI : Nonempty U := hU.nonempty.to_subtype
  have hopen : IsOpenImmersion (e.toPartialMap.restrict U hU hUr).hom := by
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom]
    exact inferInstanceAs
      (IsOpenImmersion (X.homOfLE (show U ≤ e.source from hUr) ≫ e.iso.hom ≫ e.target.ι))
  haveI : Nonempty (e.toPartialMap.restrict U hU hUr).domain := ‹Nonempty U›
  constructor
  refine (((e.toPartialMap.restrict U hU hUr).hom).isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty _)).mono ?_
  rw [← hUe]
  rintro _ ⟨u, rfl⟩
  exact ⟨_, rfl⟩

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- **Prime divisors on two models over a base correspond by their valuations.** Let `φ : W ⤏ M`
be a birational map over `Z` (`π_M ∘ φ = p`) with `π_M` proper and birational. A prime divisor
`D` of `W` is sent by `φ` to the prime divisor `P` of `M` if and only if `ord_D = ord_P` as
valuations of `k(Z)`. -/
private theorem transformPrimeDivisor_eq_some_iff_valuationOver_eq {W M Z : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral M] [IsLocallyNoetherian M]
    [IsNormal M] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (M ↘ ⊤_ Scheme)]
    (sM : M ⟶ Spec (.of ℂ)) [IsSeparated sM]
    (p : W ⟶ Z) (πM : M ⟶ Z) [IsProper πM] (hp : IsBirationalMorphism p)
    (hπM : IsBirationalMorphism πM)
    {φ : W.RationalMap M} (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hover : MMP.Flips.RationalMap.IsOver p πM φ) (D : MMP.Mori.PrimeDivisor W)
    (P : MMP.Mori.PrimeDivisor M) :
    haveI := hπM.isDominant
    haveI := hp.isDominant
    MMP.Mori.RationalMap.transformPrimeDivisor φ D = some P ↔
      D.valuationOver p = P.valuationOver πM := by
  haveI := hπM.isDominant
  haveI := hp.isDominant
  have hdom : D.genericPoint ∈ φ.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one p πM φ hover D.coheight_genericPoint.le
  obtain ⟨g, hxg, hg⟩ := Scheme.RationalMap.mem_domain.mp hdom
  haveI : Nonempty g.domain := ⟨⟨_, hxg⟩⟩
  haveI : IsDominant g.domain.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant g.hom := isDominant_hom_of_isBirational hφ g hg
  have hc : g.hom ≫ πM = g.domain.ι ≫ p := hom_comp_eq_of_isOver p πM hover g hg
  obtain ⟨DO, hDO⟩ : ∃ DO : MMP.Mori.PrimeDivisor g.domain.toScheme,
      OpenWeilRestriction.primeDivisorMap g.domain.ι DO = D :=
    (OpenWeilRestriction.mem_range_primeDivisorMap_iff g.domain.ι D).mpr
      (by rw [Scheme.Opens.range_ι]; exact hxg)
  have hηO : g.domain.ι DO.genericPoint = D.genericPoint := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hDO]
  have hxO : (⟨D.genericPoint, hxg⟩ : g.domain) = DO.genericPoint :=
    g.domain.ι.isOpenEmbedding.injective (by rw [hηO]; rfl)
  have hvO : DO.valuationOver g.domain.ι = D.divisorialValuation :=
    valuationOver_eq_of_map_genericPoint g.domain.ι
      (functionFieldMap_bijective_of_isOpenImmersion g.domain.ι).2 DO D hηO
  have hv1 : D.valuationOver p = (DO.valuationOver g.hom).comap (functionFieldMap πM) := by
    ext t
    have h := congrArg (fun v => v (functionFieldMap p t)) hvO
    simp only [MMP.Mori.PrimeDivisor.valuationOver_apply] at h
    rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hc,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, h]
  have hbg : Function.Bijective (functionFieldMap g.hom) := by
    refine ⟨(functionFieldMap g.hom).injective, fun t => ?_⟩
    obtain ⟨s, hs⟩ := ((functionFieldMap_bijective_of_isOpenImmersion g.domain.ι).comp
      hp.functionFieldMap_bijective).2 t
    refine ⟨functionFieldMap πM s, ?_⟩
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hc,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    exact hs
  constructor
  · intro h
    have hgP := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g hg hxg
    have := valuationOver_eq_of_map_genericPoint g.hom hbg.2 DO P (by rw [← hxO, ← hgP])
    rw [hv1, this]
    ext t
    rfl
  · intro h
    have h2 : DO.valuationOver g.hom = P.divisorialValuation := by
      ext t
      obtain ⟨s, rfl⟩ := hπM.functionFieldMap_bijective.2 t
      have := congrArg (fun v => v s) (hv1.symm.trans h)
      simpa only [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply] using this
    have hy : g.hom DO.genericPoint = P.genericPoint := by
      have := P.isDiscreteValuationRing_localRing
      refine MMP.Positivity.DivisorOver.eq_of_dominates sM P.divisorialValuation
        (fun a => h2 ▸ valuationOver_algebraMap_le_one g.hom DO a)
        (fun a ha => h2 ▸ valuationOver_algebraMap_lt_one g.hom DO a ha)
        (fun r => (P.divisorialValuation_le_one_iff _).2 ⟨r, rfl⟩)
        (fun r hr => (P.divisorialValuation_algebraMap_lt_one_iff r).2 hr)
    exact transformPrimeDivisor_eq_some_of_genericPoint_eq g hg hxg (by rw [hxO, hy])

/-- At the generic point, the local ring is the function field. -/
private theorem exists_algebraMap_stalk_eq {X : Scheme.{0}} [IsIntegral X] {z : X}
    (hz : z = genericPoint X) (u : X.functionField) :
    ∃ a : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField a = u := by
  subst hz
  refine ⟨u, ?_⟩
  rw [RingHom.algebraMap_toAlgebra]
  simp [TopCat.Presheaf.stalkSpecializes_refl]

/-- Discrepancies over `X` only see the structure morphism through its value. -/
private theorem isDiscrepancy_congr_structure {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {s₁ s₂ : X ⟶ Spec (.of ℂ)} (h : s₁ = s₂) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (f : Y ⟶ X) (hY₁ : IsNormalVariety ℂ (f ≫ s₁))
    (hY₂ : IsNormalVariety ℂ (f ≫ s₂)) (hb : IsBirationalMorphism f)
    (E : MMP.Mori.PrimeDivisor Y) (a : ℚ) :
    IsDiscrepancy s₁ n K Δ ⟨Y, f, hY₁, hb, E⟩ a ↔ IsDiscrepancy s₂ n K Δ ⟨Y, f, hY₂, hb, E⟩ a := by
  subst h
  rfl

/-- A prime divisor of `W` which is not sent to a prime divisor of `M` by a birational map over a
base is exceptional for it: the image of its generic point has coheight at least two, since
coheight one would give a prime divisor, and coheight zero would make it dominate the base. -/
private theorem isExceptional_of_forall_transformPrimeDivisor_ne {W M Z : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral M] [IsLocallyNoetherian M]
    [IsNormal M] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (M ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    {sZ : Z ⟶ Spec (.of ℂ)} (p : W ⟶ Z) (hW : IsNormalVariety ℂ (p ≫ sZ))
    (hp : IsBirationalMorphism p) (πM : M ⟶ Z) [IsDominant πM]
    {φ : W.RationalMap M} (hover : MMP.Flips.RationalMap.IsOver p πM φ)
    (D : MMP.Mori.PrimeDivisor W)
    (h : ∀ P : MMP.Mori.PrimeDivisor M, MMP.Mori.RationalMap.transformPrimeDivisor φ D ≠ some P) :
    MMP.Mori.RationalMap.IsExceptional φ D := by
  rw [MMP.Mori.RationalMap.isExceptional_iff]
  intro hdef
  obtain ⟨g, hxg, hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hcl := MMP.Flips.coe_transform_eq_closure_singleton g hg D hxg
  suffices hy : 2 ≤ Order.coheight (g.hom ⟨D.genericPoint, hxg⟩) by
    intro x hx
    have hx' : x ∈ closure {g.hom ⟨D.genericPoint, hxg⟩} := hcl ▸ hx
    exact hy.trans (Order.coheight_anti
      (show x ≤ g.hom ⟨D.genericPoint, hxg⟩ from specializes_iff_mem_closure.mpr hx'))
  by_contra hlt
  have key : Order.coheight (g.hom ⟨D.genericPoint, hxg⟩) = 0 ∨
      Order.coheight (g.hom ⟨D.genericPoint, hxg⟩) = 1 := by
    have hlt' : Order.coheight (g.hom ⟨D.genericPoint, hxg⟩) < 2 := lt_of_not_ge hlt
    generalize Order.coheight (g.hom ⟨D.genericPoint, hxg⟩) = c at hlt' ⊢
    induction c using ENat.recTopCoe with
    | top => exact absurd hlt' (by simp)
    | coe c => norm_cast at hlt' ⊢; omega
  rcases key with h0 | h1
  · -- the image is the generic point of `M`, so `D` dominates `Z`
    haveI := hp.isDominant
    have hmax : IsMax (g.hom ⟨D.genericPoint, hxg⟩) := Order.coheight_eq_zero.mp h0
    have hgen : genericPoint M ⤳ g.hom ⟨D.genericPoint, hxg⟩ :=
      (genericPoint_spec M).specializes trivial
    have hy' : g.hom ⟨D.genericPoint, hxg⟩ ⤳ genericPoint M :=
      hmax (show g.hom ⟨D.genericPoint, hxg⟩ ≤ genericPoint M from hgen)
    have hyg : genericPoint M = g.hom ⟨D.genericPoint, hxg⟩ := (hgen.antisymm hy').eq
    have hc : g.hom ≫ πM = g.domain.ι ≫ p := hom_comp_eq_of_isOver p πM hover g hg
    have hpη : p D.genericPoint = genericPoint Z := by
      have := congrArg (fun f => f ⟨D.genericPoint, hxg⟩) (congrArg (·.base) hc)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      change πM (g.hom ⟨D.genericPoint, hxg⟩) = p D.genericPoint at this
      rw [← this, ← hyg, map_genericPoint_of_isDominant]
    let D' : DivisorOver ℂ sZ := ⟨W, p, hW, hp, D⟩
    have hle : ∀ t : W.functionField, D.divisorialValuation t ≤ 1 := by
      intro t
      obtain ⟨u, rfl⟩ := hp.functionFieldMap_bijective.2 t
      obtain ⟨a, ha⟩ := exists_algebraMap_stalk_eq hpη u
      have := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' (p D.genericPoint) rfl a
      rw [ha] at this
      exact this
    have := D.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.localRing
    have h1 := hle (algebraMap D.localRing W.functionField ϖ)⁻¹
    rw [map_inv₀, D.divisorialValuation_algebraMap_of_irreducible hϖ, ← WithZero.exp_neg,
      neg_neg] at h1
    have h2 : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    exact (not_le.mpr h2) h1
  · -- the image is the generic point of a prime divisor
    exact h (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1)
      (transformPrimeDivisor_eq_some_of_genericPoint_eq g hg hxg
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1))

/-- The inverse of a birational map over a base lies over the base. -/
private theorem isOver_symm {W M Z : Scheme.{0}} [IsReduced M] [IsReduced W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (p : W ⟶ Z) (πM : M ⟶ Z) (e : W.PartialIso M)
    (hover : MMP.Flips.RationalMap.IsOver p πM e.toRationalMap) :
    MMP.Flips.RationalMap.IsOver πM p e.symm.toRationalMap := by
  have hc : (e.iso.hom ≫ e.target.ι) ≫ πM = e.source.ι ≫ p :=
    hom_comp_eq_of_isOver p πM hover e.toPartialMap rfl
  unfold MMP.Flips.RationalMap.IsOver
  change (e.symm.toPartialMap.toRationalMap).compHom p = πM.toRationalMap
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ πM
  rw [← hc, Category.assoc, Iso.inv_hom_id_assoc]

/-- The log discrepancy of a prime divisor `P` of `X` with respect to a pair `(X, Δ)` is
`1 - coeff_P Δ`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hΔ : MMP.Mori.IsPairWith sX n K Δ) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ)
      (DivisorOver.ofPrimeDivisor ℂ hΔ.1 P) (1 + ((-Δ.coeff P : ℚ) : ℝ)) := by
  haveI : IsSeparated sX := hΔ.1.1.toIsSeparated
  haveI := isSeparated_terminal sX
  have hne : ¬ (DivisorOver.ofPrimeDivisor ℂ hΔ.1 P).IsExceptional := by
    change ¬ RationalMap.IsExceptional (X := X) (Scheme.Hom.toRationalMap (𝟙 X)) P
    rw [isExceptional_toRationalMap_iff_two_le_coheight]
    change ¬ 2 ≤ Order.coheight P.genericPoint
    rw [P.coheight_genericPoint]
    decide
  obtain ⟨Q, hQc, hQd⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hΔ _ hne
  rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hQc
  have hPQ : P = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (inseparable_iff_closure_eq.mpr hQc).eq
  subst hPQ
  exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hQd
    (inferInstanceAs (IsProper (𝟙 X)))

end Correspondence

/-- **The part over `S` of a model over `S̄`.** Let `π_M : M ⟶ S̄` be projective and birational,
`M` `ℚ`-factorial, and every prime of `M` the strict transform of a prime of `W` with its
coefficient in `Γ`. Then `q : V = π_M⁻¹(S) ⟶ S` is projective birational from a `ℚ`-factorial
variety, and for the crepant boundary `C_V` of `(S, C)` the divisor `F = B_V - C_V` vanishes along
the non-exceptional primes and the primes carrying a valuation of `I`, and is positive along the
other exceptional primes. -/
private theorem model_analysis
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSn : IsNormalVariety ℂ sS)
    (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P) (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) [IsOpenImmersion ι] (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι)
    (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb) (hSbn : IsNormalVariety ℂ sSb)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ Sb) (hW : IsNormalVariety ℂ (p ≫ sSb)) (hpb : IsBirationalMorphism p)
    (hpp : IsProjectiveMorphism p)
    (D : I → MMP.Mori.PrimeDivisor W)
    (hD : ∀ s : I, haveI := hι.isDominant
      (⟨W, p, hW, hpb, D s⟩ : DivisorOver ℂ sSb).valuation =
        (s : Valuation S.functionField _).comap (functionFieldMap ι))
    (Γ : QDivisor W)
    (hΓC : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S),
      p P.genericPoint = ι Q.genericPoint → Γ.coeff P = C.coeff Q)
    (hΓD : ∀ (s : I) (a : ℝ), IsValuationLogDiscrepancy sS C s a → (Γ.coeff (D s) : ℝ) = 1 - a)
    (hΓE : ∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _) (a : ℝ),
      haveI := hι.isDominant
      (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation = ξ.comap (functionFieldMap ι) →
      MMP.Intersection.IsExceptionalValuation ℂ sS ξ → IsValuationLogDiscrepancy sS C ξ a →
      ξ ∉ I → 1 - a < (Γ.coeff P : ℝ))
    {M : Scheme.{0}} [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM] [QuasiCompact sM]
    {πM : M ⟶ Sb} {BM : QDivisor M}
    (hMp : MMP.Mori.IsProjectiveVariety ℂ sM) (hπs : πM ≫ sSb = sM)
    (hπp : IsProjectiveMorphism πM) (hπb : IsBirationalMorphism πM) (hMQ : IsQFactorial sM)
    (hprime : haveI := hpb.isDominant; haveI := hπb.isDominant
      ∀ P : MMP.Mori.PrimeDivisor M, ∃ D₀ : MMP.Mori.PrimeDivisor W,
        D₀.valuationOver p = P.valuationOver πM ∧ BM.coeff P = Γ.coeff D₀) :
    ∃ (_ : IsIntegral (πM ⁻¹ᵁ ι.opensRange).toScheme)
      (q : (πM ⁻¹ᵁ ι.opensRange).toScheme ⟶ S) (_ : (πM ⁻¹ᵁ ι.opensRange).ι ≫ πM = q ≫ ι)
      (hVQ : IsQFactorial (q ≫ sS)) (hqb : IsBirationalMorphism q),
      IsProjectiveMorphism q ∧ q ≫ sS = (πM ⁻¹ᵁ ι.opensRange).ι ≫ sM ∧
      ∀ (n : ℕ) (KS : Divisor S), KS.IsCanonicalDivisor sS n →
        (Divisor.toQDivisor KS + C).IsQCartier →
        ∀ CV : QDivisor (πM ⁻¹ᵁ ι.opensRange).toScheme,
        IsCrepantBoundary sS n KS C q hVQ.1 hqb CV →
        ∀ P : MMP.Mori.PrimeDivisor (πM ⁻¹ᵁ ι.opensRange).toScheme,
          ((¬ RationalMap.IsExceptional (X := (πM ⁻¹ᵁ ι.opensRange).toScheme) q.toRationalMap P ∨
              (⟨_, q, hVQ.1, hqb, P⟩ : DivisorOver ℂ sS).valuation ∈ I) →
            (BM.restrictOpen (πM ⁻¹ᵁ ι.opensRange) - CV).coeff P = 0) ∧
          (RationalMap.IsExceptional (X := (πM ⁻¹ᵁ ι.opensRange).toScheme) q.toRationalMap P →
            (⟨_, q, hVQ.1, hqb, P⟩ : DivisorOver ℂ sS).valuation ∉ I →
            0 < (BM.restrictOpen (πM ⁻¹ᵁ ι.opensRange) - CV).coeff P) := by
  classical
  -- the part `V = π_M⁻¹(S)` of `M` over `S`
  let R : Sb.Opens := ι.opensRange
  let U : M.Opens := πM ⁻¹ᵁ R
  let V := U.toScheme
  let j : V ⟶ M := U.ι
  let q : V ⟶ S := (πM ∣_ R) ≫ ι.isoOpensRange.inv
  have hjq : j ≫ πM = q ≫ ι := by
    simp only [j, q, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι, R]
    rfl
  haveI : LocallyOfFiniteType (p ≫ sSb) := hW.1.toLocallyOfFiniteType
  haveI : IsProper πM := isProper_of_isProjectiveMorphism πM hπp
  haveI : IsDominant πM := hπb.isDominant
  haveI : Nonempty S := inferInstance
  haveI : Nonempty V := by
    obtain ⟨s₀⟩ := ‹Nonempty S›
    have hsurj : Function.Surjective πM := by
      have h := πM.isClosedMap.isClosed_range.closure_eq
      rw [πM.denseRange.closure_range] at h
      intro z
      have hz : z ∈ Set.range πM := h ▸ Set.mem_univ z
      exact hz
    obtain ⟨m, hm⟩ := hsurj (ι s₀)
    exact ⟨⟨m, show πM m ∈ R from ⟨s₀, hm.symm⟩⟩⟩
  haveI : IsDominant j := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion j
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion j
  have hqp : IsProjectiveMorphism q := by
    have hr : Set.range j = Set.range (Limits.pullback.fst πM ι) := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
      rfl
    let e := IsOpenImmersion.isoOfRangeEq j (Limits.pullback.fst πM ι) hr
    have he : e.hom ≫ Limits.pullback.snd πM ι = q := by
      rw [← cancel_mono ι, Category.assoc, ← Limits.pullback.condition,
        ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, hjq]
    obtain ⟨n, i, hi, hci⟩ := hπp.baseChange ι
    exact ⟨n, e.hom ≫ i, inferInstance, by rw [Category.assoc, hci, he]⟩
  have hqb : IsBirationalMorphism q := by
    obtain ⟨U, hUne, hU⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hπb
    let U' : V.Opens := j ⁻¹ᵁ U
    have hU'ne : (U' : Set V).Nonempty := by
      obtain ⟨y, ⟨v, rfl⟩, hy⟩ := nonempty_preirreducible_inter j.isOpenEmbedding.isOpen_range
        U.isOpen (Set.range_nonempty _) hUne
      exact ⟨v, hy⟩
    have hU'd : Dense (U' : Set V) := U'.isOpen.dense hU'ne
    haveI : Nonempty U' := hU'ne.to_subtype
    have h1 : IsOpenImmersion (U'.ι ≫ j ≫ πM) := by
      change IsOpenImmersion ((j ⁻¹ᵁ U).ι ≫ j ≫ πM)
      rw [← Category.assoc, ← morphismRestrict_ι j U, Category.assoc]
      infer_instance
    have h2 : IsOpenImmersion ((U'.ι ≫ q) ≫ ι) := by
      rw [Category.assoc, ← hjq]; exact h1
    haveI : IsOpenImmersion (U'.ι ≫ q) := IsOpenImmersion.of_comp _ ι
    haveI : IsDominant q := by
      constructor
      have hd : Dense (Set.range (U'.ι ≫ q)) :=
        (U'.ι ≫ q).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
      refine hd.mono ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨U'.ι x, rfl⟩
    exact isBirationalMorphism_of_isOpenImmersion q U' hU'd
  have hqs : q ≫ sS = j ≫ sM := by
    rw [← hιs, ← Category.assoc, ← hjq, Category.assoc, hπs]
  have hVQ : IsQFactorial (q ≫ sS) := by
    rw [hqs]; exact isQFactorial_restrictOpen hMQ U
  -- the valuation of a prime divisor of `V`, over `S`
  let val : MMP.Mori.PrimeDivisor V → Valuation S.functionField (WithZero (Multiplicative ℤ)) :=
    fun P => (⟨V, q, hVQ.1, hqb, P⟩ : DivisorOver ℂ sS).valuation
  have hval_inj : Function.Injective val := fun _ _ h =>
    haveI := hqb.isDominant
    eq_of_valuationOver_eq hVQ.1 q hqb.functionFieldMap_bijective.2 h
  -- the crepant boundary `C_V` of `(S, C)` on `V` and the restriction `B_V` of `B_M`
  let BV : QDivisor V := BM.restrictOpen U
  haveI : IsSeparated sSb := hSbn.1.toIsSeparated
  haveI := isSeparated_terminal sSb
  haveI : IsSeparated sM := ((MMP.Mori.isProjectiveVariety_iff ℂ sM).mp hMp).1.toIsSeparated
  haveI := isSeparated_terminal sM
  haveI := hpb.isDominant
  haveI := hι.isDominant
  haveI := hqb.isDominant
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  -- valuations of the primes of `V`, read on `M`
  let pm : MMP.Mori.PrimeDivisor V → MMP.Mori.PrimeDivisor M :=
    fun P => OpenWeilRestriction.primeDivisorMap j P
  haveI : IsSeparated sS := hSn.1.toIsSeparated
  haveI : QuasiCompact sS := hSn.1.toQuasiCompact
  haveI := isSeparated_terminal sS
  have hPval : ∀ P : MMP.Mori.PrimeDivisor V,
      (pm P).valuationOver πM =
        (val P).comap (functionFieldMap ι) := by
    intro P
    have h1 : P.valuationOver j = (pm P).divisorialValuation :=
      valuationOver_eq_of_map_genericPoint j (functionFieldMap_bijective_of_isOpenImmersion j).2 P
        (pm P) (OpenWeilRestriction.genericPoint_primeDivisorMap j P).symm
    ext t
    have h := congrArg (fun v => v (functionFieldMap πM t)) h1
    simp only [MMP.Mori.PrimeDivisor.valuationOver_apply] at h
    rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply, ← h]
    change P.divisorialValuation (functionFieldMap j (functionFieldMap πM t)) =
      P.divisorialValuation (functionFieldMap q (functionFieldMap ι t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hjq,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  -- the primes of `W` are determined by their valuations
  have hWinj := eq_of_valuationOver_eq hW p hpb.functionFieldMap_bijective.2
  -- the coefficient of `B_V`: that of `Γ` along the corresponding prime of `W`
  have hcases : ∀ P : MMP.Mori.PrimeDivisor V,
      ∃ D₀ : MMP.Mori.PrimeDivisor W,
        D₀.valuationOver p = (val P).comap (functionFieldMap ι) ∧ BV.coeff P = Γ.coeff D₀ := by
    intro P
    obtain ⟨D₀, hD₀, hB⟩ := hprime (pm P)
    refine ⟨D₀, hD₀.trans (hPval P), ?_⟩
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact hB
  refine ⟨inferInstance, q, hjq, hVQ, hqb, hqp, hqs, fun n KS hKS hKSC CV hCV => ?_⟩
  -- the log discrepancy of the valuation of a prime of `V`
  have hlog : ∀ P : MMP.Mori.PrimeDivisor V,
      IsValuationLogDiscrepancy sS C (val P) ((1 + -CV.coeff P : ℚ) : ℝ) := fun P =>
    ⟨n, _, inferInstanceAs (IsProper q), rfl, by
      have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hCV P)
        (inferInstanceAs (IsProper q))
      rwa [show ((1 + -CV.coeff P : ℚ) : ℝ) = 1 + ((-CV.coeff P : ℚ) : ℝ) by push_cast; ring]⟩
  -- the coefficients of `F = B_V - C_V`
  have hcoeffF : ∀ P : MMP.Mori.PrimeDivisor V,
      ((¬ RationalMap.IsExceptional (X := V) q.toRationalMap P ∨ val P ∈ I) →
        (BV - CV).coeff P = 0) ∧
      (RationalMap.IsExceptional (X := V) q.toRationalMap P → val P ∉ I →
        0 < (BV - CV).coeff P) := by
    intro P
    have hF : (BV - CV).coeff P = BV.coeff P - CV.coeff P := by
      simp [DivisorWithCoeffs.coeff]
    by_cases hPe : RationalMap.IsExceptional (X := V) q.toRationalMap P
    · -- an exceptional prime
      have hexcv : MMP.Intersection.IsExceptionalValuation ℂ sS (val P) := by
        refine ⟨⟨V, q, hVQ.1, hqb, P⟩, inferInstanceAs (IsProper q), rfl, ?_⟩
        rw [MMP.Positivity.DivisorOver.codimension_center]
        exact (isExceptional_toRationalMap_iff_two_le_coheight q P).mp hPe
      obtain ⟨D₀, hD₀, hB⟩ := hcases P
      · by_cases hPI : val P ∈ I
        · have hD₀s : D₀ = D ⟨val P, hPI⟩ := hWinj (hD₀.trans (hD ⟨val P, hPI⟩).symm)
          have h1 := hΓD ⟨val P, hPI⟩ _ (hlog P)
          rw [← hD₀s] at h1
          refine ⟨fun _ => ?_, fun _ h => absurd hPI h⟩
          rw [hF, hB]
          have : (Γ.coeff D₀ : ℝ) = CV.coeff P := by rw [h1]; push_cast; ring
          exact_mod_cast sub_eq_zero.mpr (by exact_mod_cast this)
        · have h1 := hΓE D₀ (val P) _ hD₀ hexcv (hlog P) hPI
          refine ⟨fun h => absurd (h.resolve_left (not_not.mpr hPe)) hPI, fun _ _ => ?_⟩
          rw [hF, hB]
          have : (CV.coeff P : ℝ) < Γ.coeff D₀ := by push_cast at h1; linarith
          exact sub_pos.mpr (by exact_mod_cast this)
    · -- a non-exceptional prime: `q(η_P)` is the generic point of a prime `Q` of `S`
      have hPC' : MMP.Mori.IsPairWith sS n KS C := ⟨hSn, hKS, hKSC⟩
      obtain ⟨Q, hQc, hQd⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPC'
        (⟨V, q, hVQ.1, hqb, P⟩ : DivisorOver ℂ sS) hPe
      have hCVQ : CV.coeff P = C.coeff Q := by
        have := (hCV P).eq hQd
        linarith
      rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hQc
      have hqη : q P.genericPoint = Q.genericPoint := (inseparable_iff_closure_eq.mpr hQc).eq
      set Qb : MMP.Mori.PrimeDivisor Sb := OpenWeilRestriction.primeDivisorMap ι Q
      have hQb : Qb.genericPoint = ι Q.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap ι Q
      have hqιb : IsBirationalMorphism (q ≫ ι) := MMP.Mori.isBirationalMorphism_comp hqb hι
      haveI : IsDominant (q ≫ ι) := hqιb.isDominant
      have hvalPQ : (val P).comap (functionFieldMap ι) = Qb.divisorialValuation := by
        rw [← valuationOver_eq_of_map_genericPoint (q ≫ ι) hqιb.functionFieldMap_bijective.2 P Qb
          (by rw [Scheme.Hom.comp_apply, hqη, hQb]), valuationOver_comp]
        rfl
      refine ⟨fun _ => ?_, fun h => absurd h hPe⟩
      obtain ⟨D₀, hD₀, hB⟩ := hcases P
      · have hpη : p D₀.genericPoint = Qb.genericPoint :=
          MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hSbn.1
            (D := (⟨W, p, hW, hpb, D₀⟩ : DivisorOver ℂ sSb))
            (D' := DivisorOver.ofPrimeDivisor ℂ hSbn Qb)
            (by rw [valuation_ofPrimeDivisor]; exact hD₀.trans hvalPQ)
        have hΓQ := hΓC D₀ Q (hpη.trans hQb)
        rw [hF, hB, hΓQ, hCVQ, sub_self]
  exact hcoeffF

/-- **The extraction from a log minimal model.** Let `p : W ⟶ S̄` be a projective birational
morphism from a normal variety, `Γ` a boundary on `W` whose coefficients are those of `C` along
the strict transforms of the primes of `S`, equal to `1 - a(s; S, C)` along prime divisors `D_s`
realizing the valuations `s ∈ I`, and greater than `1 - a(E; S, C)` along every other exceptional
prime `E` over `S`, and let `(M/S̄, B_M)` be a log minimal model of `(W/S̄, Γ)`. Then the part
`q : V ⟶ S` of `M` over `S` is the extraction of `I`. -/
private theorem exists_extraction_of_logMinimalModel
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSn : IsNormalVariety ℂ sS)
    (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P) (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) [IsOpenImmersion ι] (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι)
    (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb) (hSbn : IsNormalVariety ℂ sSb)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ Sb) (hW : IsNormalVariety ℂ (p ≫ sSb)) (hpb : IsBirationalMorphism p)
    (hpp : IsProjectiveMorphism p)
    (D : I → MMP.Mori.PrimeDivisor W)
    (hD : ∀ s : I, haveI := hι.isDominant
      (⟨W, p, hW, hpb, D s⟩ : DivisorOver ℂ sSb).valuation =
        (s : Valuation S.functionField _).comap (functionFieldMap ι))
    (Γ : QDivisor W)
    (hΓC : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S),
      p P.genericPoint = ι Q.genericPoint → Γ.coeff P = C.coeff Q)
    (hΓD : ∀ (s : I) (a : ℝ), IsValuationLogDiscrepancy sS C s a → (Γ.coeff (D s) : ℝ) = 1 - a)
    (hΓE : ∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _) (a : ℝ),
      haveI := hι.isDominant
      (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation = ξ.comap (functionFieldMap ι) →
      MMP.Intersection.IsExceptionalValuation ℂ sS ξ → IsValuationLogDiscrepancy sS C ξ a →
      ξ ∉ I → 1 - a < (Γ.coeff P : ℝ))
    {M : Scheme.{0}} [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM] [QuasiCompact sM]
    {πM : M ⟶ Sb} {KM : Divisor M} {BM : QDivisor M}
    (hMp : MMP.Mori.IsProjectiveVariety ℂ sM) (hπs : πM ≫ sSb = sM)
    (hπp : IsProjectiveMorphism πM) (hπb : IsBirationalMorphism πM) (hMQ : IsQFactorial sM)
    (hKM : ∃ n : ℕ, KM.IsCanonicalDivisor sM n)
    (hnefM : QDivisor.IsRelativelyNef sM πM (Divisor.toQDivisor KM + BM))
    (hprime : haveI := hpb.isDominant; haveI := hπb.isDominant
      ∀ P : MMP.Mori.PrimeDivisor M, ∃ D₀ : MMP.Mori.PrimeDivisor W,
        D₀.valuationOver p = P.valuationOver πM ∧ BM.coeff P = Γ.coeff D₀)
    (hsurvive : haveI := hpb.isDominant; haveI := hπb.isDominant
      ∀ s : I, ∃ P : MMP.Mori.PrimeDivisor M, P.valuationOver πM = (D s).valuationOver p) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (q : V ⟶ S) (E : I → MMP.Mori.PrimeDivisor V)
      (hV : IsQFactorial (q ≫ sS)) (hq : IsBirationalMorphism q),
      IsProjectiveMorphism q ∧
      (∀ s : I, (⟨V, q, hV.1, hq, E s⟩ : DivisorOver ℂ sS).valuation = s) ∧
      Function.Injective E ∧
      (∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) q.toRationalMap P ↔ P ∈ Set.range E) := by
  classical
  -- the part `V = π_M⁻¹(S)` of `M` over `S`
  let R : Sb.Opens := ι.opensRange
  let U : M.Opens := πM ⁻¹ᵁ R
  let V := U.toScheme
  let j : V ⟶ M := U.ι
  haveI : LocallyOfFiniteType (p ≫ sSb) := hW.1.toLocallyOfFiniteType
  obtain ⟨_, q, hjq, hVQ, hqb, hqp, hqs, hF⟩ := model_analysis sS hSn C hC hklt I hI ι hιs hι
    hSbp hSbn p hW hpb hpp D hD Γ hΓC hΓD hΓE hMp hπs hπp hπb hMQ hprime
  haveI : IsProper πM := isProper_of_isProjectiveMorphism πM hπp
  haveI : IsDominant πM := hπb.isDominant
  -- the valuation of a prime divisor of `V`, over `S`
  let val : MMP.Mori.PrimeDivisor V → Valuation S.functionField (WithZero (Multiplicative ℤ)) :=
    fun P => (⟨V, q, hVQ.1, hqb, P⟩ : DivisorOver ℂ sS).valuation
  have hval_inj : Function.Injective val := fun _ _ h =>
    haveI := hqb.isDominant
    eq_of_valuationOver_eq hVQ.1 q hqb.functionFieldMap_bijective.2 h
  -- the crepant boundary `C_V` of `(S, C)` on `V` and the restriction `B_V` of `B_M`
  have hPC : MMP.Mori.IsPair sS C := hklt.1.isPair
  obtain ⟨-, n, KS, hKS, hKSC⟩ := id hPC
  obtain ⟨⟨CV, hCV, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPC hKS q hVQ.1 hqb
  let BV : QDivisor V := BM.restrictOpen U
  haveI : IsSeparated sSb := hSbn.1.toIsSeparated
  haveI := isSeparated_terminal sSb
  haveI : IsSeparated sM := ((MMP.Mori.isProjectiveVariety_iff ℂ sM).mp hMp).1.toIsSeparated
  haveI := isSeparated_terminal sM
  haveI := hpb.isDominant
  haveI := hι.isDominant
  haveI := hqb.isDominant
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  -- valuations of the primes of `V`, read on `M`
  let pm : MMP.Mori.PrimeDivisor V → MMP.Mori.PrimeDivisor M :=
    fun P => OpenWeilRestriction.primeDivisorMap j P
  haveI : IsSeparated sS := hSn.1.toIsSeparated
  haveI : QuasiCompact sS := hSn.1.toQuasiCompact
  haveI := isSeparated_terminal sS
  have hPval : ∀ P : MMP.Mori.PrimeDivisor V,
      (pm P).valuationOver πM =
        (val P).comap (functionFieldMap ι) := by
    intro P
    have h1 : P.valuationOver j = (pm P).divisorialValuation :=
      valuationOver_eq_of_map_genericPoint j (functionFieldMap_bijective_of_isOpenImmersion j).2 P
        (pm P) (OpenWeilRestriction.genericPoint_primeDivisorMap j P).symm
    ext t
    have h := congrArg (fun v => v (functionFieldMap πM t)) h1
    simp only [MMP.Mori.PrimeDivisor.valuationOver_apply] at h
    rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply, ← h]
    change P.divisorialValuation (functionFieldMap j (functionFieldMap πM t)) =
      P.divisorialValuation (functionFieldMap q (functionFieldMap ι t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hjq,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  -- the primes of `W` are determined by their valuations
  have hWinj := eq_of_valuationOver_eq hW p hpb.functionFieldMap_bijective.2
  have hcoeffF := hF n KS hKS hKSC CV hCV
  -- `F` is nef over `S`
  have hnef : (BV - CV).IsRelativelyNef (q ≫ sS) q := by
    haveI : QuasiCompact (j ≫ sM) := by rw [← hqs]; infer_instance
    haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (q ≫ sS)
    haveI : LocallyOfFiniteType sS := hSn.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (q ≫ sS) := hVQ.1.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V := inferInstance
    have hVQ' : IsQFactorial (j ≫ sM) := hqs ▸ hVQ
    have hFQ := MMP.Fourfold.isQCartier_of_isQFactorial _ hVQ (BV - CV)
    -- a canonical divisor `K_V` with `q_* K_V = K_S`, so `K_V + C_V = q^*(K_S + C)`
    have hdimV : topologicalKrullDim V = n := by
      rw [← hKS.topologicalKrullDim_eq]
      haveI := hSn.1
      haveI := hVQ.1.1
      exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (q ≫ sS) hqb).symm
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (q ≫ sS) hVQ.1 hdimV
    obtain ⟨KV, hKV, htr⟩ := exists_isCanonicalDivisor_transformDivisor_eq hSn hVQ.1 hqb hKS hK₀
    obtain ⟨hpbk, -, -⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hPC q hVQ.1 hqb hKS hKV
      (Or.inr ⟨inferInstance, htr⟩) hCV
    obtain ⟨N, hN, hNc⟩ := MMP.Mori.QDivisor.isCartierDivisor_cartierIndex_smul hKSC
    obtain ⟨NV, hNV, hNVc, hB, hpbN⟩ := hpbk _ (MMP.Mori.QDivisor.cartierIndex_pos hKSC) N hN hNc
    -- `K_M + B_M` and the comparison of `K_M|_V` with `K_V`
    obtain ⟨nK, hKM⟩ := hKM
    have hMn'' : IsNormalVariety ℂ sM :=
      ⟨((MMP.Mori.isProjectiveVariety_iff ℂ sM).mp hMp).1, inferInstance⟩
    have hKMU : Divisor.IsCanonicalDivisor (q ≫ sS) nK (KM.restrictOpen U) := by
      rw [hqs]; exact hKM.restrictOpen hMn'' U
    have hlin : Divisor.LinearlyEquivalent (KM.restrictOpen U) KV :=
      MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (q ≫ sS) hVQ.1 hKMU hKV
    have h0 : Divisor.LinearlyEquivalent (KM.restrictOpen U - KV) 0 := by
      obtain ⟨φ, hφ⟩ := hlin
      exact ⟨φ, by rw [sub_zero]; exact hφ⟩
    have hPc : Divisor.IsCartier (KM.restrictOpen U - KV) :=
      Divisor.IsCartier.of_linearlyEquivalent h0 Divisor.isCartier_zero
    have hAMq := MMP.Fourfold.isQCartier_of_isQFactorial _ hMQ
      (Divisor.toQDivisor KM + BM)
    rw [isRelativelyNef_congr_structure hqs]
    refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (j ≫ sM) hFQ
      fun C hC => ?_
    -- `(K_V + C_V) · C = 0`
    have hBq := MMP.Fourfold.isQCartier_of_isQFactorial _ hVQ' (Divisor.toQDivisor KV + CV)
    have hB0 : (Divisor.toQDivisor KV + CV).intersectionNumber ℂ (j ≫ sM) C.ι C.dim_le hBq = 0 := by
      rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ (j ≫ sM) C.ι C.dim_le _ hBq
        (MMP.Mori.QDivisor.cartierIndex_pos hKSC) NV hNVc hNV,
        degreeOn_isPullback_eq_zero (sV := j ≫ sM) (sT := sS) q hqs hNc hpbN C hC]
      simp
    -- `(K_M|_V - K_V) · C = 0`
    have hPq := MMP.Fourfold.isQCartier_of_isQFactorial _ hVQ'
      (Divisor.toQDivisor (KM.restrictOpen U - KV))
    have hP0 : (Divisor.toQDivisor (KM.restrictOpen U - KV)).intersectionNumber ℂ (j ≫ sM) C.ι
        C.dim_le hPq = 0 := by
      rw [MMP.Mori.QDivisor.intersectionNumber_toQDivisor ℂ (j ≫ sM) C.ι C.dim_le _ hPc hPq,
        MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent (k := ℂ) (sX := j ≫ sM) C.ι
          C.dim_le hPc h0]
      simp
    -- `(K_M + B_M)|_V · C = (K_M + B_M) · Γ ≥ 0`
    obtain ⟨Γ, e, hΓpt, he⟩ := exists_properCurve_of_opens sM U C
    have hΓc : Γ.IsContractedBy πM := by
      intro y hy
      rw [← Γ.range_ι] at hy
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨c', rfl⟩ : ∃ c', e.hom c' = c := ⟨e.inv c, by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
      have h1 : Γ.ι (e.hom c') = U.ι (C.ι c') := by
        rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
      have hz : C.ι c' ∈ closure {C.point} := C.range_ι ▸ ⟨c', rfl⟩
      rw [h1, hΓpt]
      change (j ≫ πM) (C.ι c') = (j ≫ πM) C.point
      rw [hjq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact congrArg ι (hC _ hz)
    have hAU := MMP.Fourfold.isQCartier_of_isQFactorial _ hVQ'
      ((Divisor.toQDivisor KM + BM).restrictOpen U)
    have hA := intersectionNumber_restrictOpen sM U _ hAMq hAU C Γ e he
    have hAnn := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sM
      hnefM hAMq Γ hΓc
    -- the decomposition `(K_M + B_M)|_V = F + (K_V + C_V) + (K_M|_V - K_V)`
    have hdec : (Divisor.toQDivisor KM + BM).restrictOpen U =
        (BV - CV) + ((Divisor.toQDivisor KV + CV) +
          Divisor.toQDivisor (KM.restrictOpen U - KV)) := by
      refine Finsupp.ext fun W => ?_
      change ((Divisor.toQDivisor KM + BM).restrictOpen U).coeff W =
        ((BV - CV) + ((Divisor.toQDivisor KV + CV) +
          Divisor.toQDivisor (KM.restrictOpen U - KV))).coeff W
      simp only [DivisorWithCoeffs.coeff_restrictOpen, BV, map_sub, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
      ring
    have hBP := hBq.add hPq
    have hFBP := hFQ.add hBP
    have hsum := MMP.Fourfold.intersectionNumber_congr (k := ℂ) (sX := j ≫ sM) C.ι C.dim_le
      hAU hFBP hdec
    rw [MMP.Mori.QDivisor.intersectionNumber_add' ℂ (j ≫ sM) C.ι C.dim_le _ _ hFQ hBP hFBP,
      MMP.Mori.QDivisor.intersectionNumber_add' ℂ (j ≫ sM) C.ι C.dim_le _ _ hBq hPq hBP, hB0,
      hP0, hA] at hsum
    linarith
  -- negativity: `F = 0`
  have hF0 : BV - CV = 0 := by
    haveI : QuasiCompact (q ≫ sS) := inferInstance
    haveI : LocallyOfFiniteType sS := hSn.1.toLocallyOfFiniteType
    have hdimS : topologicalKrullDim S = n := hKS.topologicalKrullDim_eq
    refine MMP.Mori.QDivisor.eq_zero_of_isEffective_of_isRelativelyNef ℂ sS (q ≫ sS) hSn hVQ.1 q
      rfl hqb (MMP.Fourfold.isQCartier_of_isQFactorial _ hVQ _)
      (fun P hP => (hcoeffF P).1 (Or.inl fun hPe => hP ⟨hVQ.1, hqb, inferInstance, ?_⟩))
      (fun P => ?_) hnef
    · exact (properDivisorOver_isExceptional_iff hdimS _).mpr
        ((isExceptional_toRationalMap_iff_two_le_coheight q P).mp hPe)
    · by_cases hPe : RationalMap.IsExceptional (X := V) q.toRationalMap P
      · by_cases hPI : val P ∈ I
        · exact ((hcoeffF P).1 (Or.inr hPI)).ge
        · exact ((hcoeffF P).2 hPe hPI).le
      · exact ((hcoeffF P).1 (Or.inl hPe)).ge
  -- negativity: every exceptional prime of `V` is the centre of a valuation of `I`
  have hexc : ∀ P : MMP.Mori.PrimeDivisor V,
      RationalMap.IsExceptional (X := V) q.toRationalMap P → val P ∈ I := by
    intro P hPe
    by_contra hPI
    have := (hcoeffF P).2 hPe hPI
    rw [hF0] at this
    simp [DivisorWithCoeffs.coeff] at this
  -- every valuation of `I` survives on `V`
  have hMn' : IsNormalVariety ℂ sM := ⟨((MMP.Mori.isProjectiveVariety_iff ℂ sM).mp hMp).1, inferInstance⟩
  have hMn : IsNormalVariety ℂ (πM ≫ sSb) := by rw [hπs]; exact hMn'
  have hcomap_inj := eq_of_comap_functionFieldMap_eq (Γ₀ := WithZero (Multiplicative ℤ)) ι
    hι.functionFieldMap_bijective.2
  have hsurv : ∀ s : I, ∃ P : MMP.Mori.PrimeDivisor V, val P = s := by
    intro s
    -- a proper divisor `D_s'` over `S` with valuation `s`
    obtain ⟨-, a₀, ⟨n₀, Ds, hDsp, hDsv, -⟩, -⟩ := hI s.2
    have hcomap : (compDivisorOver ι hιs hι Ds).valuation =
        (s : Valuation S.functionField _).comap (functionFieldMap ι) := by
      rw [valuation_compDivisorOver, hDsv]
    -- the centre on `S̄` of a divisor with valuation `s` lies in `ι(S)`
    have hcen : ∀ E' : DivisorOver ℂ sSb,
        E'.valuation = (s : Valuation S.functionField _).comap (functionFieldMap ι) →
        E'.f E'.E.genericPoint ∈ Set.range ι := fun E' hE' => by
      have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hSbn.1
        (hE'.trans hcomap.symm)
      exact ⟨Ds.f Ds.E.genericPoint, h.symm⟩
    obtain ⟨P', hv'⟩ := hsurvive s
    have hv' : P'.valuationOver πM = (s : Valuation S.functionField _).comap (functionFieldMap ι) :=
      hv'.trans (hD s)
    have hπη : πM P'.genericPoint ∈ Set.range ι := hcen ⟨M, πM, hMn, hπb, P'⟩ hv'
    obtain ⟨P, hP⟩ : ∃ P : MMP.Mori.PrimeDivisor V, OpenWeilRestriction.primeDivisorMap j P = P' :=
      (OpenWeilRestriction.mem_range_primeDivisorMap_iff j P').mpr
        (by rw [Scheme.Opens.range_ι]; exact hπη)
    refine ⟨P, hcomap_inj ?_⟩
    rw [← hPval P]
    change (pm P).valuationOver πM = _
    rw [show pm P = P' from hP, hv']
  -- the valuations of `I` are exceptional
  have hexcI : ∀ P : MMP.Mori.PrimeDivisor V, val P ∈ I →
      RationalMap.IsExceptional (X := V) q.toRationalMap P := by
    intro P hP
    obtain ⟨⟨D', hD'p, hD'v, hD'c⟩, -⟩ := hI hP
    by_contra hne
    obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hSn
      (⟨V, q, hVQ.1, hqb, P⟩ : DivisorOver ℂ sS) hne
    exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hSn D').mp hD'c Q
      (hD'v.symm.trans hQ)
  choose E hE using hsurv
  refine ⟨V, inferInstance, inferInstance, inferInstance, q, E, hVQ, hqb, hqp, hE, ?_, ?_⟩
  · intro s t hst
    exact Subtype.ext ((hE s).symm.trans ((congrArg val hst).trans (hE t)))
  · intro P
    refine ⟨fun hP => ?_, ?_⟩
    · exact ⟨⟨val P, hexc P hP⟩, hval_inj (hE _)⟩
    · rintro ⟨s, rfl⟩
      exact hexcI _ ((hE s).symm ▸ s.2)

/-! ### A log resolution carrying the valuations -/

/-- The components of the snc divisor `Ex(f) ∪ f⁻¹(Supp D)` of a log resolution: a finite set of
prime divisors, which are exactly those with generic point in that set, whose reduced sum is
snc. -/
private theorem exists_finset_isSNC_of_isLogResolution {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {D : RDivisor X} {Y : Scheme.{0}} {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hf : MMP.Mori.IsLogResolution sX D f) :
    ∃ t : Finset (MMP.Mori.PrimeDivisor Y),
      (∀ P : MMP.Mori.PrimeDivisor Y,
        P.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set Y) ∨ f P.genericPoint ∈ D.supp ↔
          P ∈ t) ∧
      DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ P ∈ t, Finsupp.single P (1 : ℤ)) := by
  rcases hf.isSNCSubset with h | ⟨t, ht, htsnc⟩
  · refine ⟨∅, fun P => ?_, ?_⟩
    · simp only [Finset.notMem_empty, iff_false]
      intro hP
      have : P.genericPoint ∈
          ((MMP.Mori.exceptionalSet f ⊔ D.supp.preimage f.continuous : TopologicalSpace.Closeds Y) : Set Y) := hP
      rw [h] at this
      exact this
    · rw [Finset.sum_empty]
      haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' (f ≫ sX) hf.isSmoothScheme
      exact DivisorWithCoeffs.isSNC_zero _
  · refine ⟨t, fun P => ⟨fun hP => ?_, fun hP => ?_⟩, htsnc⟩
    · have : P.genericPoint ∈
          ((MMP.Mori.exceptionalSet f ⊔ D.supp.preimage f.continuous : TopologicalSpace.Closeds Y) : Set Y) := hP
      rw [← ht] at this
      obtain ⟨P', hP', hPP'⟩ := Set.mem_iUnion₂.1 this
      rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPP'] at hP'
    · have : P.genericPoint ∈ ⋃ E ∈ t, (E.support : Set Y) :=
        Set.mem_iUnion₂.2 ⟨P, hP, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
      rw [ht] at this
      exact this

/-- **A log resolution carrying finitely many valuations.** Over a normal projective variety `S̄`,
with a finite family `v` of valuations with nonempty centres and a finite set `T` of prime
divisors, there is a projective birational morphism `p : W ⟶ S̄` from a smooth projective variety
carrying a prime divisor of valuation `v j` for each `j`, and a reduced snc divisor `G` on `W`
containing every `p`-exceptional prime and the strict transforms of the primes of `T`. -/
private theorem exists_resolution {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb]
    [IsNormal Sb] [CompactSpace Sb] {sSb : Sb ⟶ Spec (.of ℂ)}
    (hSbn : IsNormalVariety ℂ sSb) (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb)
    {n : ℕ} (hn : topologicalKrullDim Sb = n)
    {κ : Type} [Finite κ] (v : κ → Valuation Sb.functionField (WithZero (Multiplicative ℤ)))
    (hv : ∀ j, MMP.Flips.HasNonemptyCenter ℂ sSb (v j))
    (T : Finset (MMP.Mori.PrimeDivisor Sb)) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (p : W ⟶ Sb) (hW : IsNormalVariety ℂ (p ≫ sSb))
      (hpb : IsBirationalMorphism p),
      IsProjectiveMorphism p ∧ IsSmoothScheme (p ≫ sSb) ∧
      MMP.Mori.IsProjectiveVariety ℂ (p ≫ sSb) ∧
      (∀ j, ∃ E : MMP.Mori.PrimeDivisor W,
        (⟨W, p, hW, hpb, E⟩ : DivisorOver ℂ sSb).valuation = v j) ∧
      ∃ G : QDivisor W, G.IsSNC (p ≫ sSb) ∧
        (∀ P, MMP.Flips.IsExceptionalPrimeDivisor sSb p P → G.coeff P ≠ 0) ∧
        (∀ P (Q : MMP.Mori.PrimeDivisor Sb), Q ∈ T →
          inverseTransformPrimeDivisor p Q = some P → G.coeff P ≠ 0) := by
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sSb := hSbn.1
  haveI : LocallyOfFiniteType sSb := hSbn.1.toLocallyOfFiniteType
  haveI : IsSeparated sSb := hSbn.1.toIsSeparated
  haveI := isSeparated_terminal sSb
  -- a smooth projective model carrying the valuations
  obtain ⟨W₀, w₀, hW₀, hw₀b, -, hsm₀, hw₀p, -, hval₀, hproj₀⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (k := ℂ) sSb
      (ι := Empty) (X := fun _ => Sb) (fun _ => 𝟙 Sb) (fun e => e.elim) (fun e => e.elim) v hv
  haveI : IsIntegral W₀ := hW₀.1.toIsIntegral
  haveI : IsNormal W₀ := hW₀.2
  haveI : LocallyOfFiniteType (w₀ ≫ sSb) := hW₀.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian (w₀ ≫ sSb)
  haveI : IsProper w₀ := isProper_of_isProjectiveMorphism w₀ hw₀p
  haveI := hw₀b.isDominant
  -- the exceptional primes of `w₀` and the strict transforms of `T` form a finite set
  obtain ⟨hfinS₀, hiffS₀⟩ := MMP.Flips.RationalMap.finite_setOf_isInverseExceptional hSbn hW₀
    (MMP.Mori.RationalMap.IsBirational.inverse hw₀b) hw₀b.isBirational_inverse
    (MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hSbn w₀ hW₀.1 hw₀b)
  have hS₀ : ∀ P, MMP.Flips.IsExceptionalPrimeDivisor sSb w₀ P ↔
      MMP.Flips.RationalMap.IsInverseExceptional (MMP.Mori.RationalMap.IsBirational.inverse hw₀b)
        P := fun P => (hiffS₀ w₀ inferInstance rfl hw₀b.isInverse_inverse P).symm
  have hfinT : {P : MMP.Mori.PrimeDivisor W₀ | ∃ Q ∈ T,
      inverseTransformPrimeDivisor w₀ Q = some P}.Finite := by
    refine ((T.finite_toSet.image fun Q => inverseTransformPrimeDivisor w₀ Q).preimage
      (Option.some_injective _).injOn).subset ?_
    rintro P ⟨Q, hQ, hQP⟩
    exact ⟨Q, hQ, hQP⟩
  set F := (hfinS₀.union hfinT).toFinset
  let R : RDivisor W₀ := ∑ P ∈ F, Finsupp.single P (1 : ℝ)
  have hR : ∀ P, R.coeff P = if P ∈ F then 1 else 0 := by
    intro P
    change (∑ P' ∈ F, Finsupp.single P' (1 : ℝ)) P = _
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  -- a projective log resolution of `(W₀, R)`
  obtain ⟨W, f, hf, hfp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism (k := ℂ)
    (w₀ ≫ sSb) hW₀ R
  have hfsm : MMP.Mori.IsSmoothScheme (f ≫ w₀ ≫ sSb) := hf.isSmoothScheme
  obtain ⟨hWn', -, -⟩ := MMP.Mori.IsSmoothResolution.isNormalVariety hW₀ hf.toIsSmoothResolution
  have hfv : MMP.Mori.IsVariety ℂ (f ≫ w₀ ≫ sSb) := hWn'.1
  haveI : IsIntegral W := hfv.toIsIntegral
  haveI : IsNormal W := hWn'.2
  haveI : LocallyOfFiniteType (f ≫ w₀ ≫ sSb) := hfv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (f ≫ w₀ ≫ sSb)
  haveI : CompactSpace W := by
    haveI := hfv.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (f ≫ w₀ ≫ sSb)
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hfp
  have hfb : IsBirationalMorphism f := hf.isBirationalMorphism
  haveI := hfb.isDominant
  have hWn : IsNormalVariety ℂ ((f ≫ w₀) ≫ sSb) := by
    rw [Category.assoc]; exact ⟨hfv, inferInstance⟩
  have hpb : IsBirationalMorphism (f ≫ w₀) := MMP.Mori.isBirationalMorphism_comp hfb hw₀b
  haveI := hpb.isDominant
  have hpp : IsProjectiveMorphism (f ≫ w₀) := IsProjectiveMorphism.comp hfp hw₀p
  haveI : IsProper (f ≫ w₀) := isProper_of_isProjectiveMorphism _ hpp
  -- the snc divisor `Ex(f) ∪ f⁻¹(Supp R)`
  obtain ⟨t₀, ht₀, ht₀snc⟩ := exists_finset_isSNC_of_isLogResolution hf
  let G : QDivisor W := ∑ P ∈ t₀, Finsupp.single P (1 : ℚ)
  have hG : ∀ P, G.coeff P ≠ 0 ↔ P ∈ t₀ := by
    intro P
    change (∑ P' ∈ t₀, Finsupp.single P' (1 : ℚ)) P ≠ 0 ↔ _
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with hP <;> simp [hP]
  have hGsnc : G.IsSNC ((f ≫ w₀) ≫ sSb) := by
    rw [Category.assoc]
    refine ht₀snc.of_support_subset fun P hP => ?_
    rw [Finsupp.mem_support_iff] at hP ⊢
    change (∑ P' ∈ t₀, Finsupp.single P' (1 : ℤ)) P ≠ 0
    have hP' := (hG P).mp hP
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq', if_pos hP']
    exact one_ne_zero
  -- a prime of `W` not exceptional for `f` lies over a prime of `W₀`
  have hover : ∀ P : MMP.Mori.PrimeDivisor W,
      P.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set W) →
        ∃ P₀ : MMP.Mori.PrimeDivisor W₀, f P.genericPoint = P₀.genericPoint := by
    intro P hP
    have hb : f P.genericPoint ∈ MMP.Mori.biregularLocus f := not_not.mp hP
    have hco : Order.coheight (f P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩
  have hsupp : ∀ (P : MMP.Mori.PrimeDivisor W) (P₀ : MMP.Mori.PrimeDivisor W₀),
      f P.genericPoint = P₀.genericPoint → P₀ ∈ F → P ∈ t₀ := by
    intro P P₀ hP hP₀
    refine (ht₀ P).mp (Or.inr ?_)
    rw [hP]
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P₀, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P₀⟩
    rw [hR, if_pos hP₀]
    exact one_ne_zero
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, f ≫ w₀, hWn, hpb, hpp,
    by rw [Category.assoc]; exact hfsm, ?_, fun j => ?_, G, hGsnc, fun P hP => ?_,
    fun P Q hQ hPQ => ?_⟩
  · -- `W` is projective
    rw [MMP.Mori.isProjectiveVariety_iff] at hSbp ⊢
    exact ⟨hWn.1, IsProjectiveMorphism.comp hpp hSbp.2⟩
  · -- the valuations survive on `W`
    obtain ⟨E₀, hE₀⟩ := hval₀ j
    obtain ⟨E, hE, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hW₀ hWn' hfb E₀
    refine ⟨E, ?_⟩
    rw [← hE₀]
    change E.valuationOver (f ≫ w₀) = E₀.valuationOver w₀
    rw [valuationOver_comp, valuationOver_eq_of_map_genericPoint f hfb.functionFieldMap_bijective.2
      E E₀ hE]
    rfl
  · -- the exceptional primes of `p = w₀ ∘ f` lie in `G`
    rw [hG]
    by_cases hPf : P.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set W)
    · exact (ht₀ P).mp (Or.inl hPf)
    obtain ⟨P₀, hP₀⟩ := hover P hPf
    refine hsupp P P₀ hP₀ ?_
    rw [Set.Finite.mem_toFinset]
    left
    rw [Set.mem_setOf_eq, ← hS₀]
    refine ⟨hW₀, hw₀b, inferInstance, ?_⟩
    obtain ⟨hY', hf', hp', hPe⟩ := hP
    rw [properDivisorOver_isExceptional_iff hn] at hPe ⊢
    change 2 ≤ Order.coheight ((f ≫ w₀) P.genericPoint) at hPe
    change 2 ≤ Order.coheight (w₀ P₀.genericPoint)
    rwa [Scheme.Hom.comp_apply, hP₀] at hPe
  · -- the strict transforms of the primes of `T` lie in `G`
    rw [hG]
    have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hPQ).1
    by_cases hPf : P.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set W)
    · exact (ht₀ P).mp (Or.inl hPf)
    obtain ⟨P₀, hP₀⟩ := hover P hPf
    refine hsupp P P₀ hP₀ ?_
    rw [Set.Finite.mem_toFinset]
    right
    have hw₀η : w₀ P₀.genericPoint = Q.genericPoint := by
      rw [← hP₀, ← Scheme.Hom.comp_apply]; exact hη
    have hbir : Q.genericPoint ∈ MMP.Mori.biregularLocus w₀ := by
      refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hSbn w₀ hW₀.1 hw₀b ?_
      rw [ringKrullDim_stalk_eq_coheight, Q.coheight_genericPoint]
      simp
    exact ⟨Q, hQ, MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      hw₀η (hw₀η ▸ hbir)⟩

/-! ### The boundary on the resolution -/

/-- **The boundary on the resolution.** On a resolution `p : W ⟶ S̄` whose snc divisor `G`
contains the exceptional primes and the strict transforms of the components of `C`, there is a
boundary `Γ`, supported in `G`, with coefficients in `[0, 1)`: the coefficient of `C` along the
strict transform of a prime of `S`, `1 - a(s; S, C)` along a prime realizing `s ∈ I`, and a
coefficient `> 1 - a(ξ; S, C)` along every other prime with exceptional valuation `ξ` over `S`. -/
private theorem exists_boundary
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSn : IsNormalVariety ℂ sS)
    (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P) (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (hSbn : IsNormalVariety ℂ sSb) (ι : S ⟶ Sb) [IsOpenImmersion ι]
    (hιs : ι ≫ sSb = sS) (hι : IsBirationalMorphism ι)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (p : W ⟶ Sb) [IsProper p] (hW : IsNormalVariety ℂ (p ≫ sSb)) (hpb : IsBirationalMorphism p)
    (G : QDivisor W)
    (hGexc : ∀ P, MMP.Flips.IsExceptionalPrimeDivisor sSb p P → G.coeff P ≠ 0)
    (hGC : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S), C.coeff Q ≠ 0 →
      inverseTransformPrimeDivisor p (OpenWeilRestriction.primeDivisorMap ι Q) = some P →
        G.coeff P ≠ 0) :
    ∃ Γ : QDivisor W, (∀ P, 0 ≤ Γ.coeff P ∧ Γ.coeff P < 1) ∧ Γ.support ⊆ G.support ∧
      (∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S),
        p P.genericPoint = ι Q.genericPoint → Γ.coeff P = C.coeff Q) ∧
      (∀ (s : I) (P : MMP.Mori.PrimeDivisor W) (a : ℝ), haveI := hι.isDominant
        (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation =
          (s : Valuation S.functionField _).comap (functionFieldMap ι) →
        IsValuationLogDiscrepancy sS C s a → (Γ.coeff P : ℝ) = 1 - a) ∧
      (∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _) (a : ℝ),
        haveI := hι.isDominant
        (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation = ξ.comap (functionFieldMap ι) →
        MMP.Intersection.IsExceptionalValuation ℂ sS ξ → IsValuationLogDiscrepancy sS C ξ a →
        ξ ∉ I → 1 - a < (Γ.coeff P : ℝ)) := by
  classical
  haveI := hι.isDominant
  haveI := hpb.isDominant
  have hPC : MMP.Mori.IsPair sS C := hklt.1.isPair
  obtain ⟨-, n, KS, hKS, hKSC⟩ := id hPC
  let val : MMP.Mori.PrimeDivisor W → Valuation Sb.functionField (WithZero (Multiplicative ℤ)) :=
    fun P => (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation
  have hcomap_inj := eq_of_comap_functionFieldMap_eq (Γ₀ := WithZero (Multiplicative ℤ)) ι
    hι.functionFieldMap_bijective.2
  -- the valuation of the strict transform of a prime `Q` of `S`
  have hvalQ : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S),
      p P.genericPoint = ι Q.genericPoint →
        val P = Q.divisorialValuation.comap (functionFieldMap ι) := by
    intro P Q h
    set Qb : MMP.Mori.PrimeDivisor Sb := OpenWeilRestriction.primeDivisorMap ι Q
    have hQb : Qb.genericPoint = ι Q.genericPoint :=
      OpenWeilRestriction.genericPoint_primeDivisorMap ι Q
    have h1 : val P = Qb.divisorialValuation :=
      valuationOver_eq_of_map_genericPoint p hpb.functionFieldMap_bijective.2 P Qb (h.trans hQb.symm)
    have h2 : Q.valuationOver ι = Qb.divisorialValuation :=
      valuationOver_eq_of_map_genericPoint ι hι.functionFieldMap_bijective.2 Q Qb hQb.symm
    rw [h1, ← h2]
    rfl
  -- an exceptional valuation is not the valuation of a prime divisor
  have hexcne : ∀ (ξ : Valuation S.functionField (WithZero (Multiplicative ℤ)))
      (Q : MMP.Mori.PrimeDivisor S), MMP.Intersection.IsExceptionalValuation ℂ sS ξ →
        ξ ≠ Q.divisorialValuation := by
    rintro ξ Q ⟨D', -, rfl, hD'c⟩ hQ
    exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hSn D').mp hD'c Q
      (hQ.trans (valuation_ofPrimeDivisor hSn Q).symm)
  -- a prime with an exceptional valuation over `S` is exceptional over `S̄`
  haveI : LocallyOfFiniteType sSb := hSbn.1.toLocallyOfFiniteType
  have hdSb : topologicalKrullDim Sb = n :=
    (topologicalKrullDim_eq_of_isOpenImmersion (sSb := sSb) ι).symm.trans hKS.topologicalKrullDim_eq
  have hcenS : ∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _),
      val P = ξ.comap (functionFieldMap ι) → MMP.Intersection.IsExceptionalValuation ℂ sS ξ →
        p P.genericPoint ∈ Set.range ι := by
    rintro P ξ hP ⟨D', -, rfl, -⟩
    have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hSbn.1
      (D := (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb)) (D' := compDivisorOver ι hιs hι D')
      (by rw [valuation_compDivisorOver]; exact hP)
    exact ⟨D'.f D'.E.genericPoint, h.symm⟩
  have hexcW : ∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _),
      val P = ξ.comap (functionFieldMap ι) → MMP.Intersection.IsExceptionalValuation ℂ sS ξ →
        MMP.Flips.IsExceptionalPrimeDivisor sSb p P := by
    intro P ξ hP hξ
    refine ⟨hW, hpb, inferInstance, ?_⟩
    rw [properDivisorOver_isExceptional_iff hdSb]
    change 2 ≤ Order.coheight (p P.genericPoint)
    rw [← MMP.Positivity.DivisorOver.codimension_center (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb),
      MMP.Positivity.DivisorOver.two_le_codimension_center_iff hSbn]
    intro Q' hQ'
    rw [valuation_ofPrimeDivisor] at hQ'
    have hη : p P.genericPoint = Q'.genericPoint := by
      have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hSbn.1
        (D := (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb)) (D' := DivisorOver.ofPrimeDivisor ℂ hSbn Q')
        (by rw [valuation_ofPrimeDivisor]; exact hQ')
      exact this
    obtain ⟨Q, hQ⟩ : ∃ Q : MMP.Mori.PrimeDivisor S, OpenWeilRestriction.primeDivisorMap ι Q = Q' :=
      (OpenWeilRestriction.mem_range_primeDivisorMap_iff ι Q').mpr
        (by
          have h1 := hcenS P ξ hP hξ
          rw [hη] at h1
          exact h1)
    have hηQ : p P.genericPoint = ι Q.genericPoint := by
      rw [hη, ← hQ]
      exact OpenWeilRestriction.genericPoint_primeDivisorMap ι Q
    exact hexcne ξ Q hξ (hcomap_inj (hP.symm.trans (hvalQ P Q hηQ)))
  -- log discrepancies of exceptional valuations are rational
  have hrat : ∀ (ξ : Valuation S.functionField _) (a : ℝ), IsValuationLogDiscrepancy sS C ξ a →
      ∃ d : ℚ, a = 1 + d := by
    rintro ξ a ⟨n', Dξ, -, -, hl⟩
    have hn' : n' = n := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hl).symm.trans
        hKS.topologicalKrullDim_eq
      exact_mod_cast this
    subst hn'
    obtain ⟨d, hd⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPC hKS Dξ
    exact ⟨d, ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hd a).mp hl).2⟩
  -- klt: log discrepancies are positive
  have hpos : ∀ (ξ : Valuation S.functionField _) (a : ℝ), IsValuationLogDiscrepancy sS C ξ a →
      0 < a := by
    rintro ξ a ⟨n', Dξ, -, -, hl⟩
    exact hklt.2 n' Dξ a hl
  -- the coefficient along a prime of `W`
  let Good : MMP.Mori.PrimeDivisor W → ℚ → Prop := fun P r =>
    (0 ≤ r ∧ r < 1) ∧ (P ∉ G.support → r = 0) ∧
    (∀ Q : MMP.Mori.PrimeDivisor S, p P.genericPoint = ι Q.genericPoint → r = C.coeff Q) ∧
    (∀ (s : I) (a : ℝ), val P = (s : Valuation S.functionField _).comap (functionFieldMap ι) →
      IsValuationLogDiscrepancy sS C s a → (r : ℝ) = 1 - a) ∧
    (∀ (ξ : Valuation S.functionField _) (a : ℝ), val P = ξ.comap (functionFieldMap ι) →
      MMP.Intersection.IsExceptionalValuation ℂ sS ξ → IsValuationLogDiscrepancy sS C ξ a →
      ξ ∉ I → 1 - a < (r : ℝ))
  have hgood : ∀ P, ∃ r, Good P r := by
    intro P
    by_cases hA : ∃ Q : MMP.Mori.PrimeDivisor S, p P.genericPoint = ι Q.genericPoint
    · -- the strict transform of a prime `Q` of `S`
      obtain ⟨Q, hQ⟩ := hA
      have hvP := hvalQ P Q hQ
      refine ⟨C.coeff Q, ⟨hC Q, ?_⟩, fun hPG => ?_, fun Q' hQ' => ?_, fun s a hs _ => ?_,
        fun ξ a hξ hξe _ _ => ?_⟩
      · have h1 := isLogDiscrepancy_ofPrimeDivisor ⟨hSn, hKS, hKSC⟩ Q
        have h2 := hklt.2 n _ _ h1
        push_cast at h2
        exact_mod_cast (by linarith : (C.coeff Q : ℝ) < 1)
      · by_contra hCQ
        refine hPG (Finsupp.mem_support_iff.mpr (hGC P Q hCQ ?_))
        set Qb : MMP.Mori.PrimeDivisor Sb := OpenWeilRestriction.primeDivisorMap ι Q
        have hQb : p P.genericPoint = Qb.genericPoint :=
          hQ.trans (OpenWeilRestriction.genericPoint_primeDivisorMap ι Q).symm
        have hbir : Qb.genericPoint ∈ biregularLocus p := by
          refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hSbn p hW.1 hpb ?_
          rw [ringKrullDim_stalk_eq_coheight, Qb.coheight_genericPoint]
          simp
        exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQb
          (hQb ▸ hbir)
      · have : Q' = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (ι.isOpenEmbedding.injective (hQ'.symm.trans hQ))
        rw [this]
      · exact absurd (hcomap_inj (hs.symm.trans hvP))
          (hexcne _ Q (hI s.2).1)
      · exact absurd (hcomap_inj (hξ.symm.trans hvP)) (hexcne ξ Q hξe)
    by_cases hB : ∃ (ξ : Valuation S.functionField _) (a : ℝ),
        val P = ξ.comap (functionFieldMap ι) ∧ MMP.Intersection.IsExceptionalValuation ℂ sS ξ ∧
          IsValuationLogDiscrepancy sS C ξ a
    · obtain ⟨ξ, a, hξ, hξe, hξa⟩ := hB
      obtain ⟨d, rfl⟩ := hrat ξ a hξa
      have hPG : P ∈ G.support := Finsupp.mem_support_iff.mpr (hGexc P (hexcW P ξ hξ hξe))
      have ha0 := hpos ξ _ hξa
      by_cases hξI : ξ ∈ I
      · -- a valuation of `I`: coefficient `1 - a`
        obtain ⟨-, a', ha', ha'1⟩ := hI hξI
        have haa' := IsValuationLogDiscrepancy.eq hξa ha'
        refine ⟨-d, ⟨?_, ?_⟩, fun h => absurd hPG h, fun Q hQ => absurd ⟨Q, hQ⟩ hA,
          fun s a₁ hs hs₁ => ?_, fun ξ' a₁ hξ' _ _ hξ'I => ?_⟩
        · have : (d : ℝ) ≤ 0 := by linarith
          exact_mod_cast (neg_nonneg.mpr (by exact_mod_cast this))
        · have : (-d : ℝ) < 1 := by linarith
          exact_mod_cast this
        · have hsξ : (s : Valuation S.functionField _) = ξ := hcomap_inj (hs.symm.trans hξ)
          rw [hsξ] at hs₁
          have := IsValuationLogDiscrepancy.eq hs₁ hξa
          push_cast
          linarith
        · exact absurd ((hcomap_inj (hξ'.symm.trans hξ)) ▸ hξI) hξ'I
      · -- another exceptional valuation: coefficient `1 - min(a, 1)/2`
        refine ⟨1 - min (1 + d) 1 / 2, ⟨?_, ?_⟩, fun h => absurd hPG h,
          fun Q hQ => absurd ⟨Q, hQ⟩ hA, fun s a₁ hs _ => ?_, fun ξ' a₁ hξ' _ hξ'a _ => ?_⟩
        · have : min (1 + d) 1 ≤ 1 := min_le_right _ _
          linarith
        · have h0 : (0 : ℚ) < 1 + d := by exact_mod_cast (by push_cast at ha0; linarith : (0 : ℝ) < 1 + d)
          have : 0 < min (1 + d) 1 := lt_min h0 one_pos
          linarith
        · exact absurd ((hcomap_inj (hs.symm.trans hξ)) ▸ s.2) hξI
        · have hξ'ξ : ξ' = ξ := hcomap_inj (hξ'.symm.trans hξ)
          rw [hξ'ξ] at hξ'a
          have h1 := IsValuationLogDiscrepancy.eq hξ'a hξa
          have h0 : (0 : ℚ) < 1 + d := by exact_mod_cast (by push_cast at ha0; linarith : (0 : ℝ) < 1 + d)
          have h2 : min (1 + d) 1 / 2 < 1 + d := by
            have := min_le_left (1 + d) 1
            linarith
          have h3 : ((min (1 + d) 1 / 2 : ℚ) : ℝ) < 1 + (d : ℝ) := by exact_mod_cast h2
          push_cast at h3 ⊢
          linarith
    · -- any other prime of the snc divisor
      refine ⟨if P ∈ G.support then 1 / 2 else 0, ⟨by split_ifs <;> norm_num,
        by split_ifs <;> norm_num⟩, fun h => if_neg h, fun Q hQ => absurd ⟨Q, hQ⟩ hA,
        fun s a hs hsa => absurd ⟨s, a, hs, (hI s.2).1, hsa⟩ hB,
        fun ξ a hξ hξe hξa _ => absurd ⟨ξ, a, hξ, hξe, hξa⟩ hB⟩
  choose γ hγ using hgood
  let Γ : QDivisor W := Finsupp.onFinset G.support γ fun P hP => by
    by_contra h
    exact hP ((hγ P).2.1 h)
  have hΓ : ∀ P, Γ.coeff P = γ P := fun P => Finsupp.onFinset_apply
  refine ⟨Γ, fun P => by rw [hΓ]; exact (hγ P).1, Finsupp.support_onFinset_subset,
    fun P Q h => by rw [hΓ]; exact (hγ P).2.2.1 Q h, fun s P a h ha => by
      rw [hΓ]; exact (hγ P).2.2.2.1 s a h ha, fun P ξ a h hξ ha hξI => by
      rw [hΓ]; exact (hγ P).2.2.2.2 ξ a h hξ ha hξI⟩

/-! ### The steps of the program with scaling -/

section Steps

/-- Composing a rational map with two morphisms in turn. -/
private theorem compHom_compHom' {A B C D : Scheme.{0}} (ψ : A.RationalMap B) (b : B ⟶ C)
    (c : C ⟶ D) : (ψ.compHom b).compHom c = ψ.compHom (b ≫ c) := by
  obtain ⟨ψ', rfl⟩ := Scheme.PartialMap.toRationalMap_surjective ψ
  simp only [← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- A rational map over `T` lies over every base below `T`. -/
private theorem isOver_comp {A B T Z : Scheme.{0}} {f : A ⟶ T} {fp : B ⟶ T} (g : T ⟶ Z)
    {φ : A.RationalMap B} (h : MMP.Flips.RationalMap.IsOver f fp φ) :
    MMP.Flips.RationalMap.IsOver (f ≫ g) (fp ≫ g) φ := by
  unfold MMP.Flips.RationalMap.IsOver at h ⊢
  rw [← compHom_compHom', h, Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

/-- Two prime divisors one of whose generic points lies on the other coincide. -/
private theorem eq_of_genericPoint_mem_support {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {P E : MMP.Mori.PrimeDivisor X} (h : P.genericPoint ∈ E.support) :
    P = E := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hle : P.genericPoint ≤ E.genericPoint := specializes_iff_mem_closure.mpr h
  by_cases hge : E.genericPoint ≤ P.genericPoint
  · exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (Specializes.antisymm hge hle).eq
  have := Order.coheight_strictAnti (lt_of_le_not_ge hle hge)
  rw [P.coheight_genericPoint, E.coheight_genericPoint] at this
  exact absurd (this (by decide)) (lt_irrefl _)

/-- A morphism which is an open immersion near the generic point of a prime divisor `P` sends it
to the generic point of a prime divisor. -/
private theorem exists_genericPoint_eq_of_isOpenImmersion {X T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral T] [IsLocallyNoetherian T] (f : X ⟶ T)
    (P : MMP.Mori.PrimeDivisor X) (V : X.Opens) (hPV : P.genericPoint ∈ V)
    (hV : IsOpenImmersion (V.ι ≫ f)) :
    ∃ R : MMP.Mori.PrimeDivisor T, f P.genericPoint = R.genericPoint := by
  have h : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet (fun h => h ⟨V, hPV, hV⟩),
      P.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h).symm⟩

/-- A small contraction is an open immersion near the generic point of every prime divisor. -/
private theorem exists_isOpenImmersion_of_isSmall {X T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {f : X ⟶ T} (hf : MMP.Flips.IsSmall ℂ sT sX f)
    [IsLocallyNoetherian X] (P : MMP.Mori.PrimeDivisor X) :
    ∃ V : X.Opens, P.genericPoint ∈ V ∧ IsOpenImmersion (V.ι ≫ f) := by
  obtain ⟨-, V, W, hV, -, h, hiso⟩ := hf
  refine ⟨V.compl, ?_, ?_⟩
  · intro hP
    have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) _ hP
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)
  · rw [← Scheme.Hom.resLE_comp_ι f h]
    infer_instance

/-- **A prime divisor upstairs of a prime divisor of the target.** Let `f : X ⟶ T`,
`f⁺ : X' ⟶ T` be proper birational morphisms of normal varieties and `φ : X ⤏ X'` birational
with `f⁺ ∘ φ = f`. If `f⁺` sends the generic point of a prime `P'` of `X'` to that of a prime `R`
of `T`, there is a prime `P` of `X` over `R`, with the valuation of `P'` over `T`, sent to `P'` by
`φ`, and the coefficient of `P'` in `φ_* B` is that of `P` in `B`. -/
private theorem exists_transformPrimeDivisor_eq_some {X X' T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    (hT : IsNormalVariety ℂ sT) (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX')
    (f : X ⟶ T) (fp : X' ⟶ T) [IsProper f] [IsProper fp] (hfs : f ≫ sT = sX)
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) {φ : X.RationalMap X'}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hover : MMP.Flips.RationalMap.IsOver f fp φ)
    (P' : MMP.Mori.PrimeDivisor X') (R : MMP.Mori.PrimeDivisor T)
    (hR : fp P'.genericPoint = R.genericPoint) :
    haveI := hf.isDominant
    haveI := hfp.isDominant
    ∃ P : MMP.Mori.PrimeDivisor X, f P.genericPoint = R.genericPoint ∧
      P.valuationOver f = P'.valuationOver fp ∧
      MMP.Mori.RationalMap.transformPrimeDivisor φ P = some P' ∧
      ∀ B : RDivisor X, (MMP.Mori.RationalMap.transformDivisor φ B).coeff P' = B.coeff P := by
  haveI := hf.isDominant
  haveI := hfp.isDominant
  haveI : IsSeparated sT := hT.1.toIsSeparated
  haveI := isSeparated_terminal sT
  haveI : IsSeparated sX' := hX'.1.toIsSeparated
  haveI := isSeparated_terminal sX'
  obtain ⟨P, hPR, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hT
    (by rw [hfs]; exact hX) hf R
  have hv : P.valuationOver f = P'.valuationOver fp := by
    rw [valuationOver_eq_of_map_genericPoint f hf.functionFieldMap_bijective.2 P R hPR,
      valuationOver_eq_of_map_genericPoint fp hfp.functionFieldMap_bijective.2 P' R hR]
  have hcorr := transformPrimeDivisor_eq_some_iff_valuationOver_eq sX' f fp hf hfp hφ hover
  have hT' := (hcorr P P').mpr hv
  refine ⟨P, hPR, hv, hT', fun B => ?_⟩
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hT' (fun D₁ hD₁ =>
    eq_of_valuationOver_eq hX f hf.functionFieldMap_bijective.2
      (((hcorr D₁ P').mp hD₁).trans hv.symm)) B

/-- The discrepancy of a prime divisor of `X` over `(X, Δ)` is minus its coefficient. -/
private theorem isDiscrepancy_ofPrimeDivisor {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hΔ : MMP.Mori.IsPairWith sX n K Δ) (P : MMP.Mori.PrimeDivisor X) :
    IsDiscrepancy sX n K Δ (DivisorOver.ofPrimeDivisor ℂ hΔ.1 P) (-Δ.coeff P) := by
  haveI : IsSeparated sX := hΔ.1.1.toIsSeparated
  haveI := isSeparated_terminal sX
  have hne : ¬ (DivisorOver.ofPrimeDivisor ℂ hΔ.1 P).IsExceptional := by
    change ¬ RationalMap.IsExceptional (X := X) (Scheme.Hom.toRationalMap (𝟙 X)) P
    rw [isExceptional_toRationalMap_iff_two_le_coheight]
    change ¬ 2 ≤ Order.coheight P.genericPoint
    rw [P.coheight_genericPoint]
    decide
  obtain ⟨Q, hQc, hQd⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hΔ _ hne
  rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hQc
  have hPQ : P = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (inseparable_iff_closure_eq.mpr hQc).eq
  subst hPQ
  exact hQd

/-- No proper curve is contracted by an injective morphism. -/
private theorem false_of_isContractedBy_of_injective {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) {f : X ⟶ Y} (hf : Function.Injective f) (hC : C.IsContractedBy f) :
    False := by
  have hcl : ∀ x ∈ closure ({C.point} : Set X), x = C.point := fun x hx => hf (hC x hx)
  have hrange : ∀ a : C.scheme, C.ι a ∈ closure ({C.point} : Set X) := by
    intro a
    have : C.ι a ∈ Set.range C.ι := ⟨a, rfl⟩
    simpa [ProperCurve.ι, curveSubschemeAtι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] using this
  have : Subsingleton C.scheme := ⟨fun a b => C.ι.isClosedEmbedding.injective
    ((hcl _ (hrange a)).trans (hcl _ (hrange b)).symm)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- The centre on `S̄` of a divisor whose valuation comes from a divisor over `S` lies in `S`. -/
private theorem mem_range_of_valuation_eq {S Sb : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb]
    {sS : S ⟶ Spec (.of ℂ)} {sSb : Sb ⟶ Spec (.of ℂ)} (hSbn : IsNormalVariety ℂ sSb)
    (ι : S ⟶ Sb) (hιs : ι ≫ sSb = sS) (hι : IsBirationalMorphism ι) (Ds : DivisorOver ℂ sS)
    (E' : DivisorOver ℂ sSb)
    (hE' : haveI := hι.isDominant; E'.valuation = Ds.valuation.comap (functionFieldMap ι)) :
    E'.f E'.E.genericPoint ∈ Set.range ι := by
  have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hSbn.1
    (hE'.trans (valuation_compDivisorOver ι hιs hι Ds).symm)
  exact ⟨Ds.f Ds.E.genericPoint, h.symm⟩

/-- **No divisorial step contracts a desired prime.** In a divisorial step `f : X ⟶ T` of the
program, with `f⁺ : X' ⟶ T` an isomorphism, the contracted prime `E` cannot carry a valuation
`s ∈ I`. Over `S`, compare `(X, B)` with `(X', B')` over `T`: since `-(K + B)` is `f`-ample and `f`
is not an isomorphism at the centre of `E`, `a(E; X', B') > a(E; X, B) = -Γ(D_s)`. On the other
hand `B'|_V ≥ C_V` on `V = π'⁻¹(S)`, so `a(E; X', B') ≤ a(E; V, C_V) = a(s; S, C) - 1 = -Γ(D_s)`.
-/
private theorem false_of_isExceptional_step
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSn : IsNormalVariety ℂ sS)
    (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P) (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) [IsOpenImmersion ι] (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι)
    (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb) (hSbn : IsNormalVariety ℂ sSb)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ Sb) (hW : IsNormalVariety ℂ (p ≫ sSb)) (hpb : IsBirationalMorphism p)
    (hpp : IsProjectiveMorphism p)
    (D : I → MMP.Mori.PrimeDivisor W)
    (hD : ∀ s : I, haveI := hι.isDominant
      (⟨W, p, hW, hpb, D s⟩ : DivisorOver ℂ sSb).valuation =
        (s : Valuation S.functionField _).comap (functionFieldMap ι))
    (Γ : QDivisor W)
    (hΓC : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S),
      p P.genericPoint = ι Q.genericPoint → Γ.coeff P = C.coeff Q)
    (hΓD : ∀ (s : I) (a : ℝ), IsValuationLogDiscrepancy sS C s a → (Γ.coeff (D s) : ℝ) = 1 - a)
    (hΓE : ∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _) (a : ℝ),
      haveI := hι.isDominant
      (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation = ξ.comap (functionFieldMap ι) →
      MMP.Intersection.IsExceptionalValuation ℂ sS ξ → IsValuationLogDiscrepancy sS C ξ a →
      ξ ∉ I → 1 - a < (Γ.coeff P : ℝ))
    {X X' T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX']
    [QuasiCompact sX'] [QuasiCompact sX] {sT : T ⟶ Spec (.of ℂ)}
    {πX : X ⟶ Sb} {πX' : X' ⟶ Sb} (hπs : πX ≫ sSb = sX) (hπb : IsBirationalMorphism πX)
    (hX'p : MMP.Mori.IsProjectiveVariety ℂ sX') (hπs' : πX' ≫ sSb = sX')
    (hπp' : IsProjectiveMorphism πX') (hπb' : IsBirationalMorphism πX')
    (hXQ : IsQFactorial sX) (hX'Q : IsQFactorial sX')
    {f : X ⟶ T} {g : T ⟶ Sb} {fp : X' ⟶ T} [IsIso fp] (hfg : f ≫ g = πX) (hfpg : fp ≫ g = πX')
    (hfb : IsBirationalMorphism f) (hfps : fp ≫ sT = sX')
    {n : ℕ} {KS : Divisor S} (hKS : KS.IsCanonicalDivisor sS n)
    (hKSC : (Divisor.toQDivisor KS + C).IsQCartier)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {K' : Divisor X'}
    (hK' : K'.IsCanonicalDivisor sX' n) {BQ : QDivisor X} {BQ' : QDivisor X'}
    (hneg : MMP.Flips.IsNegativeExtremalContraction ℂ sX sT
      (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor BQ)) f)
    (E : MMP.Mori.PrimeDivisor X) (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support)
    (hcoef : haveI := hfb.isDominant
      ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
        P.valuationOver f = P'.valuationOver fp → BQ'.coeff P' = BQ.coeff P)
    (hprime' : haveI := hpb.isDominant; haveI := hπb'.isDominant
      ∀ P : MMP.Mori.PrimeDivisor X', ∃ D₀ : MMP.Mori.PrimeDivisor W,
        D₀.valuationOver p = P.valuationOver πX' ∧ BQ'.coeff P = Γ.coeff D₀)
    (s : I) (hEs : haveI := hpb.isDominant; haveI := hπb.isDominant
      E.valuationOver πX = (D s).valuationOver p)
    (hBE : BQ.coeff E = Γ.coeff (D s)) : False := by
  classical
  haveI := hpb.isDominant
  haveI := hπb.isDominant
  haveI := hπb'.isDominant
  haveI := hfb.isDominant
  haveI := hι.isDominant
  have hXn : IsNormalVariety ℂ sX := hneg.isNormalVariety_source
  have hX'n : IsNormalVariety ℂ sX' := hX'Q.1
  have hfs : f ≫ sT = sX := hneg.isContraction.comp_eq
  haveI : IsProper f := hneg.isContraction.isProper
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sX' := hX'n.1.toIsSeparated
  haveI := isSeparated_terminal sX'
  haveI : IsSeparated sS := hSn.1.toIsSeparated
  haveI : QuasiCompact sS := hSn.1.toQuasiCompact
  -- `h = f⁺⁻¹ ∘ f : X ⟶ X'`
  set h : X ⟶ X' := f ≫ inv fp with hh
  have hhπ : h ≫ πX' = πX := by rw [hh, Category.assoc, ← hfpg, IsIso.inv_hom_id_assoc, hfg]
  have hhs : h ≫ sX' = sX := by rw [← hπs', ← Category.assoc, hhπ, hπs]
  have hhb : IsBirationalMorphism h :=
    MMP.Mori.isBirationalMorphism_comp hfb (isBirationalMorphism_of_isIso (inv fp))
  haveI := hhb.isDominant
  have hfh : f = h ≫ fp := by rw [hh, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  -- `E` is exceptional over `T`
  have hEη : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
    rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hEexc : 2 ≤ Order.coheight (f E.genericPoint) := by
    by_contra hlt
    have h1 : Order.coheight (f E.genericPoint) ≤ 1 := by
      rw [← not_lt]; intro h2; exact hlt (Order.add_one_le_of_lt h2)
    exact hEη (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb h1)
  -- the part `V = π'⁻¹(S)` of `X'` over `S`
  obtain ⟨_, q, hjq, hVQ, hqb, hqp, hqs, hF⟩ := model_analysis sS hSn C hC hklt I hI ι hιs hι
    hSbp hSbn p hW hpb hpp D hD Γ hΓC hΓD hΓE hX'p hπs' hπp' hπb' hX'Q hprime'
  haveI := hqb.isDominant
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  -- `E` lies over `S`
  obtain ⟨-, a₀, ⟨n₀, Ds, hDsp, hDsv, -⟩, -⟩ := hI s.2
  have hEU : πX E.genericPoint ∈ Set.range ι := by
    refine mem_range_of_valuation_eq hSbn ι hιs hι Ds
      ⟨X, πX, by rw [hπs]; exact hXn, hπb, E⟩ ?_
    rw [hDsv]
    exact hEs.trans (hD s)
  have hEU' : h E.genericPoint ∈ (πX' ⁻¹ᵁ ι.opensRange) := by
    change πX' (h E.genericPoint) ∈ Set.range ι
    rw [← Scheme.Hom.comp_apply, hhπ]
    exact hEU
  -- the part `X_V = h⁻¹(V)` of `X` and `E` on it
  set XV := h ⁻¹ᵁ (πX' ⁻¹ᵁ ι.opensRange) with hXV
  haveI : Nonempty XV := ⟨⟨E.genericPoint, hEU'⟩⟩
  haveI : IsDominant XV.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion XV.ι
  haveI : IsIntegral XV := isIntegral_of_isOpenImmersion XV.ι
  set h' : XV.toScheme ⟶ (πX' ⁻¹ᵁ ι.opensRange).toScheme := h ∣_ (πX' ⁻¹ᵁ ι.opensRange) with hh'
  have hh'ι : h' ≫ (πX' ⁻¹ᵁ ι.opensRange).ι = XV.ι ≫ h := morphismRestrict_ι h (πX' ⁻¹ᵁ ι.opensRange)
  have hh'b : IsBirationalMorphism h' := MMP.Mori.isBirationalMorphism_morphismRestrict hhb (πX' ⁻¹ᵁ ι.opensRange)
  haveI := hh'b.isDominant
  haveI : IsProper h' := by rw [hh']; infer_instance
  obtain ⟨EV, hEV⟩ : ∃ EV : MMP.Mori.PrimeDivisor XV,
      OpenWeilRestriction.primeDivisorMap XV.ι EV = E :=
    (OpenWeilRestriction.mem_range_primeDivisorMap_iff XV.ι E).mpr
      (by rw [Scheme.Opens.range_ι]; exact hEU')
  have hηEV : XV.ι EV.genericPoint = E.genericPoint := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hEV]
  -- structure morphisms
  have hXVn : IsNormalVariety ℂ (XV.ι ≫ sX) := hXn.restrictOpen XV
  have hU'n : IsNormalVariety ℂ ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX') := hX'n.restrictOpen (πX' ⁻¹ᵁ ι.opensRange)
  have hh's : h' ≫ (πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX' = XV.ι ≫ sX := by
    rw [← Category.assoc, hh'ι, Category.assoc, hhs]
  haveI : QuasiCompact ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX') := by rw [← hqs]; infer_instance
  haveI : QuasiCompact (XV.ι ≫ sX) := by rw [← hh's]; infer_instance
  haveI : CompactSpace XV := QuasiCompact.compactSpace_of_compactSpace (XV.ι ≫ sX)
  haveI : CompactSpace (πX' ⁻¹ᵁ ι.opensRange) := QuasiCompact.compactSpace_of_compactSpace ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX')
  haveI : IsSeparated ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX') := hU'n.1.toIsSeparated
  haveI := isSeparated_terminal ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX')
  -- canonical divisors and boundaries on the opens
  have hKV := hK.restrictOpen hXn XV
  have hKV' := hK'.restrictOpen hX'n (πX' ⁻¹ᵁ ι.opensRange)
  have hXVQ : IsQFactorial (XV.ι ≫ sX) := isQFactorial_restrictOpen hXQ XV
  have hU'Q : IsQFactorial ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX') := isQFactorial_restrictOpen hX'Q (πX' ⁻¹ᵁ ι.opensRange)
  set BV := BQ.restrictOpen XV with hBV
  set BV' := BQ'.restrictOpen (πX' ⁻¹ᵁ ι.opensRange) with hBV'
  -- the divisors `E` over `X_V` and over `V`
  have hPV : MMP.Mori.IsPairWith (XV.ι ≫ sX) n (K.restrictOpen XV) BV :=
    ⟨hXVn, hKV, MMP.Fourfold.isQCartier_of_isQFactorial _ hXVQ _⟩
  have hY' : IsNormalVariety ℂ (h' ≫ (πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX') := by rw [hh's]; exact hXVn
  let D₁ : DivisorOver ℂ (XV.ι ≫ sX) := DivisorOver.ofPrimeDivisor ℂ hPV.1 EV
  let D₂ : DivisorOver ℂ ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX') := ⟨XV, h', hY', hh'b, EV⟩
  have ha := isDiscrepancy_ofPrimeDivisor hPV EV
  have hPV' : MMP.Mori.IsPair ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX') BV' :=
    ⟨hU'n, n, _, hKV', MMP.Fourfold.isQCartier_of_isQFactorial _ hU'Q _⟩
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPV' hKV' D₂
  -- the strict comparison over `V`
  have hlt : -BV.coeff EV < a' := by
    -- `-(K + B)` is `f`-ample, so it is positive on the curves contracted by `f`
    have hKQ : QDivisor.toRDivisor (-(Divisor.toQDivisor K + BQ)) =
        -MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor BQ) := by
      rw [map_neg, map_add, QDivisor.toRDivisor_toQDivisor]; rfl
    have hamp : MMP.Flips.IsRelativelyAmple f
        (QDivisor.toRDivisor (-(Divisor.toQDivisor K + BQ))) := by
      rw [hKQ]; exact hneg.isRelativelyAntiAmple
    have hQ := MMP.Fourfold.isQCartier_of_isQFactorial _ hXQ (-(Divisor.toQDivisor K + BQ))
    have hpos : ∀ Γ' : ProperCurve sX, Γ'.IsContractedBy f →
        0 < (-(Divisor.toQDivisor K + BQ)).intersectionNumber ℂ sX Γ'.ι Γ'.dim_le hQ :=
      fun Γ' hΓ' => MMP.Flips.intersectionNumber_pos_of_isRelativelyAmple f hQ hamp Γ' hΓ'
    -- and on `X_V`, on the curves contracted by `h'`
    have hres : (-(Divisor.toQDivisor K + BQ)).restrictOpen XV =
        -(Divisor.toQDivisor (K.restrictOpen XV) + BV) := by
      refine Finsupp.ext fun P => ?_
      change ((-(Divisor.toQDivisor K + BQ)).restrictOpen XV).coeff P =
        (-(Divisor.toQDivisor (K.restrictOpen XV) + BV)).coeff P
      simp only [DivisorWithCoeffs.coeff_restrictOpen, hBV, DivisorWithCoeffs.coeff_neg,
        DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    have key : ∀ z, h (XV.ι z) = (πX' ⁻¹ᵁ ι.opensRange).ι (h' z) := fun z => by
      rw [← Scheme.Hom.comp_apply, ← hh'ι, Scheme.Hom.comp_apply]
    have hposV : ∀ C' : ProperCurve (XV.ι ≫ sX), C'.IsContractedBy h' →
        ∀ hQV : (-(Divisor.toQDivisor (K.restrictOpen XV) + BV)).IsQCartier,
        0 < (-(Divisor.toQDivisor (K.restrictOpen XV) + BV)).intersectionNumber ℂ (XV.ι ≫ sX)
          C'.ι C'.dim_le hQV := by
      intro C' hC' hQV
      obtain ⟨Γ', e, hΓpt, he⟩ := exists_properCurve_of_opens sX XV C'
      have hΓc : Γ'.IsContractedBy f := by
        intro y hy
        rw [← Γ'.range_ι] at hy
        obtain ⟨c', rfl⟩ := hy
        obtain ⟨c'', rfl⟩ : ∃ c'', e.hom c'' = c' := ⟨e.inv c', by
          rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
        have h1 : Γ'.ι (e.hom c'') = XV.ι (C'.ι c'') := by
          rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
        have hz : C'.ι c'' ∈ closure {C'.point} := C'.range_ι ▸ ⟨c'', rfl⟩
        rw [h1, hΓpt, hfh]
        change fp (h (XV.ι (C'.ι c''))) = fp (h (XV.ι C'.point))
        rw [key, key, hC' _ hz]
      have hAU : QDivisor.IsQCartier ((-(Divisor.toQDivisor K + BQ)).restrictOpen XV) :=
        hres ▸ hQV
      have h1 := intersectionNumber_restrictOpen sX XV _ hQ hAU C' Γ' e he
      have hcongr := MMP.Fourfold.intersectionNumber_congr (k := ℂ) (sX := XV.ι ≫ sX) C'.ι
        C'.dim_le hAU hQV hres
      rw [← hcongr, h1]
      exact hpos Γ' hΓc
    have hQV0 := MMP.Fourfold.isQCartier_of_isQFactorial _ hXVQ
      (-(Divisor.toQDivisor (K.restrictOpen XV) + BV))
    have hN : QDivisor.IsRelativelyNef (XV.ι ≫ sX) h'
        (-(Divisor.toQDivisor (K.restrictOpen XV) + BV)) :=
      MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (XV.ι ≫ sX) hQV0
        fun C' hC' => (hposV C' hC' hQV0).le
    have hnegV : ∀ C' : ProperCurve (XV.ι ≫ sX), C'.IsContractedBy h' →
        ∀ hQ' : (Divisor.toQDivisor (K.restrictOpen XV) + BV).IsQCartier,
        (Divisor.toQDivisor (K.restrictOpen XV) + BV).intersectionNumber ℂ (XV.ι ≫ sX) C'.ι
          C'.dim_le hQ' < 0 := by
      intro C' hC' hQ'
      have h1 := hposV C' hC' hQ'.neg
      rw [QDivisor.intersectionNumber_neg ℂ (XV.ι ≫ sX) C'.ι C'.dim_le hQ' hQ'.neg] at h1
      linarith
    have hN' : QDivisor.IsRelativelyNef ((πX' ⁻¹ᵁ ι.opensRange).ι ≫ sX')
        (𝟙 (πX' ⁻¹ᵁ ι.opensRange).toScheme)
        (Divisor.toQDivisor (K'.restrictOpen (πX' ⁻¹ᵁ ι.opensRange)) + BV') :=
      ⟨MMP.Fourfold.isQCartier_of_isQFactorial _ hU'Q _, fun C' hC' =>
        (false_of_isContractedBy_of_injective C' (fun a b hab => by simpa using hab) hC').elim⟩
    -- the boundaries have the same push-forward to `V`
    have hΔ : RationalMap.transformDivisor (X := XV.toScheme) h'.toRationalMap BV =
        RationalMap.transformDivisor (X := (πX' ⁻¹ᵁ ι.opensRange).toScheme)
          (Scheme.Hom.toRationalMap (𝟙 (πX' ⁻¹ᵁ ι.opensRange).toScheme)) BV' := by
      refine Finsupp.ext fun R => ?_
      obtain ⟨P₁, hP₁, -, hP₁t⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hU'n
          (by rw [hh's]; exact hXVn) hh'b R
      obtain ⟨P₂, hP₂, -, hP₂t⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hU'n
          (by rw [Category.id_comp]; exact hU'n) (isBirationalMorphism_of_isIso (𝟙 _)) R
      rw [hP₁t, hP₂t]
      have hP₂R : P₂ = R := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by simpa using hP₂)
      subst hP₂R
      change BV.coeff P₁ = BV'.coeff P₂
      rw [hBV, hBV', DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.coeff_restrictOpen]
      symm
      apply hcoef
      have hηP : h (OpenWeilRestriction.primeDivisorMap XV.ι P₁).genericPoint =
          (OpenWeilRestriction.primeDivisorMap (πX' ⁻¹ᵁ ι.opensRange).ι P₂).genericPoint := by
        rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
          OpenWeilRestriction.genericPoint_primeDivisorMap, key, hP₁]
      have hv1 := valuationOver_eq_of_map_genericPoint h hhb.functionFieldMap_bijective.2 _ _ hηP
      ext t
      have h2 := congrArg (fun v => v (functionFieldMap fp t)) hv1
      simp only [MMP.Mori.PrimeDivisor.valuationOver_apply] at h2 ⊢
      rw [← h2, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply h fp,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hfh]
    -- the two divisors induce the same valuation of `k(V)`
    have hv : D₁.valuation.comap (functionFieldMap h') =
        D₂.valuation.comap (functionFieldMap (𝟙 (πX' ⁻¹ᵁ ι.opensRange).toScheme)) := by
      ext t
      simp only [Valuation.comap_apply]
      change EV.divisorialValuation (functionFieldMap (𝟙 XV.toScheme) (functionFieldMap h' t)) =
        EV.divisorialValuation (functionFieldMap h'
          (functionFieldMap (𝟙 (πX' ⁻¹ᵁ ι.opensRange).toScheme) t))
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr (Category.id_comp h'),
        MMP.Positivity.DivisorOver.functionFieldMap_congr (Category.comp_id h')]
    -- `E` is exceptional over `V`, and `h'` is not an isomorphism at its centre
    have hcoh : 2 ≤ Order.coheight (h' EV.genericPoint) := by
      have e1 := AlgebraicGeometry.coheight_eq_of_isOpenImmersion (x := h' EV.genericPoint)
        (πX' ⁻¹ᵁ ι.opensRange).ι
      have e2 := AlgebraicGeometry.coheight_eq_of_isOpenImmersion (x := f E.genericPoint) (inv fp)
      rw [← e1, ← key, hηEV, hh, Scheme.Hom.comp_apply, e2]
      exact hEexc
    have hEx : RationalMap.IsExceptional (X := XV.toScheme)
        ((𝟙 XV.toScheme) ≫ h').toRationalMap EV := by
      rw [Category.id_comp, isExceptional_toRationalMap_iff_two_le_coheight]
      exact hcoh
    have hWb : h' ((𝟙 XV.toScheme) EV.genericPoint) ∉ MMP.Mori.biregularLocus h' := by
      intro hmem
      have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus h' hmem
      change Order.coheight (h' EV.genericPoint) = Order.coheight EV.genericPoint at h1
      rw [h1, EV.coheight_genericPoint] at hcoh
      exact absurd hcoh (by decide)
    exact MMP.Mori.isDiscrepancy_lt_of_forall_intersectionNumber_neg hXVn hU'n hU'n (f := h')
      (f' := 𝟙 _) hh's (Category.id_comp _) hh'b (isBirationalMorphism_of_isIso _) hKV hKV' hΔ
      hN hN' hnegV D₁ D₂ hv hEx hWb ha ha'
  -- the upper bound through `(S, C)`
  have hPC : MMP.Mori.IsPair sS C := hklt.1.isPair
  obtain ⟨⟨CV, hCV, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPC hKS q hVQ.1 hqb
  have hFc := hF n KS hKS hKSC CV hCV
  have hFe : (BV' - CV).IsEffective := fun P => by
    by_cases hPe : RationalMap.IsExceptional (X := (πX' ⁻¹ᵁ ι.opensRange).toScheme) q.toRationalMap P
    · by_cases hPI : (⟨_, q, hVQ.1, hqb, P⟩ : DivisorOver ℂ sS).valuation ∈ I
      · exact ((hFc P).1 (Or.inr hPI)).ge
      · exact ((hFc P).2 hPe hPI).le
    · exact ((hFc P).1 (Or.inl hPe)).ge
  have hKVq : Divisor.IsCanonicalDivisor (q ≫ sS) n (K'.restrictOpen (πX' ⁻¹ᵁ ι.opensRange)) := by
    rw [hqs]; exact hKV'
  obtain ⟨hPVC, hinv⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hPC q hVQ.1 hqb hKS hKVq
    (Or.inl hCV)
  have hY₃ : IsNormalVariety ℂ (h' ≫ q ≫ sS) := by rw [hqs]; exact hY'
  let D₃ : DivisorOver ℂ (q ≫ sS) := ⟨XV, h', hY₃, hh'b, EV⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPVC hKVq D₃
  have ha'' : IsDiscrepancy (q ≫ sS) n (K'.restrictOpen (πX' ⁻¹ᵁ ι.opensRange)) (CV + (BV' - CV)) D₃ a' := by
    rw [add_sub_cancel]
    exact (isDiscrepancy_congr_structure hqs h' hY₃ hY' hh'b EV a').mpr ha'
  have hle : a' ≤ c := MMP.Threefold.Mori.Helpers.isDiscrepancy_le_of_effective hFe hc ha''
  -- `c = a(s; S, C) - 1`
  have hcomap_inj := eq_of_comap_functionFieldMap_eq (Γ₀ := WithZero (Multiplicative ℤ)) ι
    hι.functionFieldMap_bijective.2
  have hcomp : h' ≫ q ≫ ι = XV.ι ≫ πX := by
    rw [← hjq, ← Category.assoc, hh'ι, Category.assoc, hhπ]
  have hvE : Ds.valuation = D₃.valuation.comap (functionFieldMap q) := by
    rw [hDsv]
    refine hcomap_inj ?_
    rw [← hD s]
    change (D s).valuationOver p = _
    rw [← hEs]
    have h1 : EV.valuationOver XV.ι = E.divisorialValuation :=
      valuationOver_eq_of_map_genericPoint XV.ι
        (functionFieldMap_bijective_of_isOpenImmersion XV.ι).2 EV E hηEV
    ext t
    have h2 := congrArg (fun v => v (functionFieldMap πX t)) h1
    simp only [MMP.Mori.PrimeDivisor.valuationOver_apply] at h2
    rw [Valuation.comap_apply, Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
      ← h2]
    change EV.divisorialValuation (functionFieldMap XV.ι (functionFieldMap πX t)) =
      EV.divisorialValuation (functionFieldMap h' (functionFieldMap q (functionFieldMap ι t)))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply XV.ι πX,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply q ι,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply h' (q ≫ ι),
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomp]
  have hDsd := (hinv D₃ Ds hvE c).mp hc
  have hlog' : IsValuationLogDiscrepancy sS C s ((1 + c : ℚ) : ℝ) :=
    ⟨n, Ds, hDsp, hDsv, by
      have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hDsd hDsp
      rwa [show ((1 + c : ℚ) : ℝ) = 1 + (c : ℝ) by push_cast; ring]⟩
  have hΓs := hΓD s _ hlog'
  have hBVE : BV.coeff EV = BQ.coeff E := by
    rw [hBV, DivisorWithCoeffs.coeff_restrictOpen, hEV]
  rw [hBVE, hBE] at hlt
  have hΓs' : (Γ.coeff (D s) : ℚ) = -c := by
    have : ((Γ.coeff (D s) : ℚ) : ℝ) = ((-c : ℚ) : ℝ) := by rw [hΓs]; push_cast; ring
    exact_mod_cast this
  linarith

/-- An `ℝ`-divisor with rational coefficients is a `ℚ`-divisor. -/
private theorem exists_qDivisor_eq {X : Scheme.{0}} (B : RDivisor X)
    (h : ∀ P, ∃ c : ℚ, B.coeff P = c) : ∃ BQ : QDivisor X, QDivisor.toRDivisor BQ = B := by
  classical
  choose c hc using h
  refine ⟨Finsupp.onFinset B.support c (fun P hP => Finsupp.mem_support_iff.mpr fun h0 => hP ?_),
    Finsupp.ext fun P => ?_⟩
  · have := hc P
    rw [DivisorWithCoeffs.coeff_apply, h0] at this
    exact_mod_cast this.symm
  · change (QDivisor.toRDivisor _).coeff P = B.coeff P
    rw [QDivisor.coeff_toRDivisor, hc P, DivisorWithCoeffs.coeff_apply, Finsupp.onFinset_apply]

/-- **One step of the program.** Let `f : X ⟶ T` be a `(K + B)`-negative extremal contraction over
`S̄` (by `g`), followed either by an isomorphism `f⁺` (a divisorial contraction) or by the flip
`f⁺ : X' ⟶ T`, with `B' = φ_* B`. If `X` is birational over `S̄`, every prime of `X` is the strict
transform of a prime of `W` with its coefficient in `Γ`, and every `D_s` survives on `X`, then the
same holds on `X'`. -/
private theorem step_invariant
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSn : IsNormalVariety ℂ sS)
    (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P) (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) [IsOpenImmersion ι] (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι)
    (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb) (hSbn : IsNormalVariety ℂ sSb)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ Sb) (hW : IsNormalVariety ℂ (p ≫ sSb)) (hpb : IsBirationalMorphism p)
    (hpp : IsProjectiveMorphism p)
    (D : I → MMP.Mori.PrimeDivisor W)
    (hD : ∀ s : I, haveI := hι.isDominant
      (⟨W, p, hW, hpb, D s⟩ : DivisorOver ℂ sSb).valuation =
        (s : Valuation S.functionField _).comap (functionFieldMap ι))
    (Γ : QDivisor W)
    (hΓC : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S),
      p P.genericPoint = ι Q.genericPoint → Γ.coeff P = C.coeff Q)
    (hΓD : ∀ (s : I) (a : ℝ), IsValuationLogDiscrepancy sS C s a → (Γ.coeff (D s) : ℝ) = 1 - a)
    (hΓE : ∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _) (a : ℝ),
      haveI := hι.isDominant
      (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation = ξ.comap (functionFieldMap ι) →
      MMP.Intersection.IsExceptionalValuation ℂ sS ξ → IsValuationLogDiscrepancy sS C ξ a →
      ξ ∉ I → 1 - a < (Γ.coeff P : ℝ))
    {X X' T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX']
    [QuasiCompact sX'] [QuasiCompact sX] {sT : T ⟶ Spec (.of ℂ)}
    {πX : X ⟶ Sb} {πX' : X' ⟶ Sb} (hπs : πX ≫ sSb = sX) (hπb : IsBirationalMorphism πX)
    (hX'p : MMP.Mori.IsProjectiveVariety ℂ sX') (hπs' : πX' ≫ sSb = sX')
    (hXQ : IsQFactorial sX) (hX'Q : IsQFactorial sX')
    {f : X ⟶ T} {g : T ⟶ Sb} {fp : X' ⟶ T} {φ : X.RationalMap X'}
    (hfg : f ≫ g = πX) (hfpg : fp ≫ g = πX')
    {n : ℕ} {KS : Divisor S} (hKS : KS.IsCanonicalDivisor sS n)
    (hKSC : (Divisor.toQDivisor KS + C).IsQCartier)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {K' : Divisor X'}
    (hK' : IsBirationalMorphism πX' → K'.IsCanonicalDivisor sX' n) {B : RDivisor X}
    {B' : RDivisor X'}
    (hneg : MMP.Flips.IsNegativeExtremalContraction ℂ sX sT (MMP.Flips.logCanonicalDivisor K B) f)
    (hcase : (IsBirationalMorphism f ∧
        (∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
        IsIso fp ∧ MMP.Flips.IsModificationOf f fp φ) ∨
      MMP.Flips.IsFlip ℂ sX sT sX' (MMP.Flips.logCanonicalDivisor K B) f fp φ)
    (hB' : B' = MMP.Mori.RationalMap.transformDivisor φ B)
    (hprime : haveI := hpb.isDominant; haveI := hπb.isDominant
      ∀ P : MMP.Mori.PrimeDivisor X, ∃ D₀ : MMP.Mori.PrimeDivisor W,
        D₀.valuationOver p = P.valuationOver πX ∧ B.coeff P = ((Γ.coeff D₀ : ℚ) : ℝ))
    (hsurv : haveI := hpb.isDominant; haveI := hπb.isDominant
      ∀ s : I, ∃ P : MMP.Mori.PrimeDivisor X, P.valuationOver πX = (D s).valuationOver p) :
    ∃ hπb' : IsBirationalMorphism πX',
      (haveI := hpb.isDominant; haveI := hπb'.isDominant
        ∀ P : MMP.Mori.PrimeDivisor X', ∃ D₀ : MMP.Mori.PrimeDivisor W,
          D₀.valuationOver p = P.valuationOver πX' ∧ B'.coeff P = ((Γ.coeff D₀ : ℚ) : ℝ)) ∧
      (haveI := hpb.isDominant; haveI := hπb'.isDominant
        ∀ s : I, ∃ P : MMP.Mori.PrimeDivisor X', P.valuationOver πX' = (D s).valuationOver p) := by
  classical
  subst hfg hfpg
  haveI := hpb.isDominant
  haveI := hπb.isDominant
  have hXn : IsNormalVariety ℂ sX := hneg.isNormalVariety_source
  have hX'n : IsNormalVariety ℂ sX' := hX'Q.1
  have hTn : IsNormalVariety ℂ sT := hneg.isNormalVariety_target
  have hfs : f ≫ sT = sX := hneg.isContraction.comp_eq
  haveI : IsProper f := hneg.isContraction.isProper
  haveI : IsIntegral T := hTn.1.toIsIntegral
  haveI : IsNormal T := hTn.2
  haveI : LocallyOfFiniteType sT := hTn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI : IsSeparated sSb := hSbn.1.toIsSeparated
  haveI := isSeparated_terminal sSb
  -- the data common to both kinds of step
  have hfb : IsBirationalMorphism f :=
    hcase.elim (fun h => h.1) fun hfl => hfl.isSmall_source.isBirationalMorphism
  haveI := hfb.isDominant
  haveI : IsDominant g := IsDominant.of_comp f g
  have hmod : MMP.Flips.IsModificationOf f fp φ :=
    hcase.elim (fun h => h.2.2.2) fun hfl => hfl.isModificationOf
  haveI : IsProper fp :=
    hcase.elim (fun h => haveI := h.2.2.1; inferInstance) fun hfl => hfl.isProper
  have hfpb : IsBirationalMorphism fp :=
    hcase.elim (fun h => haveI := h.2.2.1; isBirationalMorphism_of_isIso fp)
      fun hfl => hfl.isSmall.isBirationalMorphism
  haveI := hfpb.isDominant
  have hgs : g ≫ sSb = sT := ext_of_isDominant f (by rw [← Category.assoc, hπs, hfs])
  have hfps : fp ≫ sT = sX' := by rw [← hgs, ← Category.assoc, hπs']
  -- `π' = f⁺ ≫ g` is birational
  haveI : IsSeparated sX' := hX'n.1.toIsSeparated
  haveI : IsProper (fp ≫ g) := by
    haveI : IsProper ((fp ≫ g) ≫ sSb) := by
      rw [hπs']; exact isProper_of_isProjectiveMorphism _ hX'p.isProjective
    exact IsProper.of_comp (fp ≫ g) sSb
  have hπb' : IsBirationalMorphism (fp ≫ g) :=
    isBirationalMorphism_of_isOver (f ≫ g) (fp ≫ g) hπb hmod.1 (isOver_comp g hmod.2)
  haveI := hπb'.isDominant
  -- every prime of `X'` comes from a prime of `X`
  have hnbhd : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ V : X'.Opens,
      P'.genericPoint ∈ V ∧ IsOpenImmersion (V.ι ≫ fp) :=
    hcase.elim (fun h => haveI := h.2.2.1; fun P' => ⟨⊤, trivial, inferInstance⟩)
      fun hfl => exists_isOpenImmersion_of_isSmall hfl.isSmall
  have hcorr : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
      P.valuationOver f = P'.valuationOver fp ∧
      ∀ B₀ : RDivisor X, (MMP.Mori.RationalMap.transformDivisor φ B₀).coeff P' = B₀.coeff P := by
    intro P'
    obtain ⟨V, hV, hVo⟩ := hnbhd P'
    obtain ⟨R, hR⟩ := exists_genericPoint_eq_of_isOpenImmersion fp P' V hV hVo
    obtain ⟨P, -, hv, -, hc⟩ := exists_transformPrimeDivisor_eq_some hTn hXn hX'n f fp hfs hfb
      hfpb hmod.1 hmod.2 P' R hR
    exact ⟨P, hv, hc⟩
  have hprime' : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ D₀ : MMP.Mori.PrimeDivisor W,
      D₀.valuationOver p = P'.valuationOver (fp ≫ g) ∧ B'.coeff P' = ((Γ.coeff D₀ : ℚ) : ℝ) := by
    intro P'
    obtain ⟨P, hv, hc⟩ := hcorr P'
    obtain ⟨D₀, hD₀, hB⟩ := hprime P
    refine ⟨D₀, ?_, by rw [hB', hc, hB]⟩
    rw [hD₀, valuationOver_comp, valuationOver_comp, hv]
  refine ⟨hπb', hprime', fun s => ?_⟩
  obtain ⟨P, hP⟩ := hsurv s
  -- the image of the generic point of `P` on `T` is that of a prime divisor
  obtain ⟨R, hR⟩ : ∃ R : MMP.Mori.PrimeDivisor T, f P.genericPoint = R.genericPoint := by
    rcases hcase with ⟨-, ⟨E, hE⟩, hiso, -⟩ | hfl
    · by_cases hPE : P = E
      · -- the contracted prime cannot carry a valuation of `I`
        exfalso
        subst hPE
        obtain ⟨BQ, hBQ⟩ := exists_qDivisor_eq B fun P₁ => by
          obtain ⟨D₀, -, hB⟩ := hprime P₁
          exact ⟨_, hB⟩
        obtain ⟨BQ', hBQ'⟩ := exists_qDivisor_eq B' fun P₁ => by
          obtain ⟨D₀, -, hB⟩ := hprime' P₁
          exact ⟨_, hB⟩
        subst hBQ hBQ'
        obtain ⟨D₀, hD₀, hB⟩ := hprime P
        have hD₀s : D₀ = D s := eq_of_valuationOver_eq hW p hpb.functionFieldMap_bijective.2
          (hD₀.trans hP)
        subst hD₀s
        haveI := hiso
        haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
        refine false_of_isExceptional_step (BQ' := BQ') sS hSn C hC hklt I hI ι hιs hι hSbp hSbn p hW hpb hpp
          D hD Γ hΓC hΓD hΓE hπs hπb hX'p hπs' (IsProjectiveMorphism.of_comp (fp ≫ g) sSb
            (hπs' ▸ hX'p.isProjective)) hπb' hXQ hX'Q rfl rfl hfb hfps hKS hKSC hK (hK' hπb') hneg P hE
          (fun P₁ P' hv => ?_) (fun P' => ?_) s hP
          (by rw [QDivisor.coeff_toRDivisor] at hB; exact_mod_cast hB)
        · obtain ⟨P₂, hv₂, hc₂⟩ := hcorr P'
          have hP₂ : P₂ = P₁ := eq_of_valuationOver_eq hXn f hfb.functionFieldMap_bijective.2
            (hv₂.trans hv.symm)
          subst hP₂
          have := hc₂ (QDivisor.toRDivisor BQ)
          rw [← hB'] at this
          simp only [QDivisor.coeff_toRDivisor] at this
          exact_mod_cast this
        · obtain ⟨D₁, hD₁, hB₁⟩ := hprime' P'
          refine ⟨D₁, hD₁, ?_⟩
          rw [QDivisor.coeff_toRDivisor] at hB₁
          exact_mod_cast hB₁
      · have hPη : P.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set X) := by
          rw [hE]; exact fun h => hPE (eq_of_genericPoint_mem_support h)
        have hmem : f P.genericPoint ∈ MMP.Mori.biregularLocus f := by
          by_contra h; exact hPη h
        have h1 : Order.coheight (f P.genericPoint) = 1 := by
          rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hmem, P.coheight_genericPoint]
        exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1,
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm⟩
    · obtain ⟨V, hV, hVo⟩ := exists_isOpenImmersion_of_isSmall hfl.isSmall_source P
      exact exists_genericPoint_eq_of_isOpenImmersion f P V hV hVo
  -- the prime of `X'` over `R`
  obtain ⟨P', hP'R, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hTn
      (by rw [hfps]; exact hX'n) hfpb R
  refine ⟨P', ?_⟩
  rw [← hP, valuationOver_comp, valuationOver_comp,
    valuationOver_eq_of_map_genericPoint f hfb.functionFieldMap_bijective.2 P R hR,
    valuationOver_eq_of_map_genericPoint fp hfpb.functionFieldMap_bijective.2 P' R hP'R]

end Steps

/-! ### A scaling divisor on the resolution -/

section Scaling

/-- Every `ℝ`-divisor is the sum of its coefficients times its prime components. -/
private theorem exists_eq_sum_single {X : Scheme.{0}} (B : RDivisor X) :
    ∃ (m : ℕ) (P : Fin m → MMP.Mori.PrimeDivisor X),
      B = ∑ j, B.coeff (P j) • Divisor.toRDivisor (Finsupp.single (P j) 1) := by
  classical
  refine ⟨B.support.card, fun j => B.support.equivFin.symm j, Finsupp.ext fun Q => ?_⟩
  rw [Finsupp.finset_sum_apply]
  have h1 : ∀ P : MMP.Mori.PrimeDivisor X,
      (B.coeff P • Divisor.toRDivisor (Finsupp.single P (1 : ℤ))) Q = if P = Q then B Q else 0 := by
    intro P
    change B.coeff P * (Divisor.toRDivisor (Finsupp.single P (1 : ℤ))).coeff Q = _
    rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; simp
    · simp
  simp only [h1]
  rw [Fintype.sum_equiv B.support.equivFin.symm _ (fun x : B.support => if (x : _) = Q then B Q else 0)
    (fun _ => rfl), Finset.sum_coe_sort B.support (fun x => if x = Q then B Q else 0),
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact Finsupp.notMem_support_iff.mp h

/-- When every Weil divisor is Cartier, every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_forall_isCartier {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (hcart : ∀ D : Divisor X, D.IsCartier) (B : RDivisor X) :
    MMP.Flips.IsCartierCombination B := by
  obtain ⟨m, P, hB⟩ := exists_eq_sum_single B
  exact ⟨m, fun j => B.coeff (P j), fun j => Finsupp.single (P j) 1, fun j => hcart _, hB⟩

/-- When every Weil divisor is Cartier, every `ℝ`-divisor is `ℝ`-Cartier (coefficient form). -/
private theorem isRCartier_of_forall_isCartier {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (hcart : ∀ D : Divisor X, D.IsCartier) (B : RDivisor X) :
    RDivisor.IsRCartier B := by
  obtain ⟨m, P, hB⟩ := exists_eq_sum_single B
  refine ⟨m, fun j => B.coeff (P j), fun j => Finsupp.single (P j) 1, fun j => hcart _,
    fun Q => ?_⟩
  conv_lhs => rw [hB]
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  rfl

/-- A klt pair, in the sense of discrepancies, on a variety all of whose Weil divisors are Cartier,
is a real klt pair. -/
private theorem isRealKltPair_of_isKltPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hcart : ∀ D : Divisor X, D.IsCartier) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : MMP.Mori.IsKltPair sX n K Δ) : IsRealKltPair sX (QDivisor.toRDivisor Δ) := by
  refine ⟨h.1.1, fun P => ?_, ⟨n, K, h.1.2.1, isRCartier_of_forall_isCartier hcart _⟩,
    fun n' D a ha => ?_⟩
  · rw [QDivisor.coeff_toRDivisor]
    exact_mod_cast MMP.Mori.roundDown_nonpos_iff.mp h.2.2 P
  have hn' : n' = n := by
    have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      h.1.2.1.topologicalKrullDim_eq
    exact_mod_cast this
  subst hn'
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1 D
  obtain ⟨-, rfl⟩ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp ha
  by_cases hD : D.IsExceptional
  · have h1 := MMP.Mori.discrep_le hD hc
    have h2 : ((-1 : ℝ) : EReal) < ((c : ℝ) : EReal) := by
      have := lt_of_lt_of_le h.2.1 h1
      simpa using this
    have h3 : (-1 : ℝ) < c := EReal.coe_lt_coe_iff.mp h2
    linarith
  · obtain ⟨Q, -, hQd⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff h.1 D hD
    have hcQ := hc.eq hQd
    have hQ1 : Δ.coeff Q < 1 := MMP.Mori.roundDown_nonpos_iff.mp h.2.2 Q
    have : (-1 : ℚ) < c := by linarith
    have : (-1 : ℝ) < c := by exact_mod_cast this
    linarith

/-- Ampleness over the base field is ampleness. -/
private theorem isRelativelyAmpleCartier_iff_isAmple' {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] {L : Divisor X} (hL : L.IsCartier) :
    MMP.Flips.IsRelativelyAmpleCartier sX L ↔ L.IsAmple hL := by
  have := hL.isInvertibleModule_divisorialSheaf
  have h := (Stacks.AmpleRelativeFiniteType.tfae_six sX L.divisorialSheaf).out 1 2
  constructor
  · rintro ⟨hL', hU⟩
    exact h.2 ⟨inferInstance, hU⟩
  · intro hA
    exact ⟨hL, (h.1 hA).2⟩

end Scaling

/-- **A scaling divisor on `W`.** On the smooth projective `W` with the snc klt boundary `Γ`, there
is an effective `ℝ`-Cartier `C` with `(W, Γ + C)` klt and `K_W + Γ + C` nef over `S̄`. -/
private theorem exists_scaling_divisor
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb)
    (hSbn : IsNormalVariety ℂ sSb)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ Sb) (hW : IsNormalVariety ℂ (p ≫ sSb)) (hpb : IsBirationalMorphism p)
    (hpp : IsProjectiveMorphism p) (hsm : IsSmoothScheme (p ≫ sSb))
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sSb))
    (Γ : QDivisor W) (hΓ01 : ∀ P, 0 ≤ Γ.coeff P ∧ Γ.coeff P < 1)
    (G : QDivisor W) (hGsnc : G.IsSNC (p ≫ sSb)) (hΓG : Γ.support ⊆ G.support)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (p ≫ sSb) 4)
    (hkltW : MMP.Mori.IsKltPair (p ≫ sSb) 4 KW Γ) :
    IsQFactorial (p ≫ sSb) ∧ MMP.Flips.IsCartierCombination (QDivisor.toRDivisor Γ) ∧
    ∃ Cs : RDivisor W, (∀ P, 0 ≤ Cs.coeff P) ∧ MMP.Flips.IsCartierCombination Cs ∧
      IsRealKltPair (p ≫ sSb) (QDivisor.toRDivisor Γ + Cs) ∧
      MMP.Flips.IsRelativelyNef ℂ (p ≫ sSb) p
        (MMP.Flips.logCanonicalDivisor KW (QDivisor.toRDivisor Γ + Cs)) := by
  classical
  haveI := hpb.isDominant
  haveI : LocallyOfFiniteType (p ≫ sSb) := hW.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sSb) := hW.1.toQuasiCompact
  haveI : IsSeparated sSb := hSbn.1.toIsSeparated
  have hcart : ∀ D : Divisor W, D.IsCartier := fun D =>
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D
  have hXq : IsQFactorial (p ≫ sSb) := ⟨hW, fun D => ⟨1, one_pos, hcart _⟩⟩
  have hΓR : IsRealKltPair (p ≫ sSb) (QDivisor.toRDivisor Γ) := isRealKltPair_of_isKltPair hcart hkltW
  have hΓe : (QDivisor.toRDivisor Γ).IsEffective := fun P => by
    rw [QDivisor.coeff_toRDivisor]; exact_mod_cast (hΓ01 P).1
  -- an ample Cartier divisor `D_A` on `W`
  obtain ⟨-, -, ⟨-, A, -, -, -, -, -, -, -, -, -, hAa, -⟩, -⟩ :=
    exists_isRealKltPair_add_pullback_isAmple_le_of_isBirationalMorphism (p ≫ sSb) sSb hWp hXq
      hSbp hSbn p rfl hpp hpb KW hKW (QDivisor.toRDivisor Γ) hΓe hΓR
  obtain ⟨mA, -, DA, -, hDAc, hDAa⟩ := hAa
  have hDAr : MMP.Flips.IsRelativelyAmpleCartier (p ≫ sSb) DA :=
    (isRelativelyAmpleCartier_iff_isAmple' (p ≫ sSb) hDAc).2 hDAa
  -- an integral multiple `N = c (K_W + Γ)`
  obtain ⟨c, hc, Nd, hNd⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor (Divisor.toQDivisor KW + Γ)
  -- `m D_A + N` and `2m D_A` are ample
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (MMP.Flips.Internal.RelativeRealAmplePerturbation.eventually_isRelativelyAmpleCartier_nsmul_add
      (p ≫ sSb) hDAr (hcart Nd))
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp
    (MMP.Flips.Internal.RelativeRealAmplePerturbation.eventually_isRelativelyAmpleCartier_nsmul_add
      (p ≫ sSb) hDAr (hcart 0))
  have hL : MMP.Flips.IsRelativelyAmpleCartier (p ≫ sSb) ((m₀ + m₁ + 1) • DA + Nd) :=
    hm₀ _ (by omega)
  have h2m : ((2 * (m₀ + m₁ + 1)) • DA).IsAmple (hcart _) := by
    have := hm₁ (2 * (m₀ + m₁ + 1)) (by omega)
    rw [add_zero] at this
    exact (isRelativelyAmpleCartier_iff_isAmple' (p ≫ sSb) (hcart _)).1 this
  set m : ℕ := m₀ + m₁ + 1 with hm
  have hc0 : (0 : ℚ) < c := by exact_mod_cast hc
  -- the ample `ℚ`-divisor `H = (2m / c) D_A`
  set H : QDivisor W := ((2 * m : ℚ) / c) • Divisor.toQDivisor DA with hH
  have hHa : H.IsAmple := by
    refine ⟨c, hc, (2 * m) • DA, Finsupp.ext fun P => ?_, hcart _, h2m⟩
    change (Divisor.toQDivisor ((2 * m) • DA)).coeff P = ((c : ℚ) • H).coeff P
    simp only [hH, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, nsmul_eq_mul]
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    have hc0' : (c : ℚ) ≠ 0 := hc0.ne'
    push_cast
    field_simp
  -- `𝟙 : W ⟶ W` is a log resolution of `(W, Γ)`
  have hbir : MMP.Mori.IsBiregular (𝟙 W) ⊤ := inferInstanceAs (IsIso (𝟙 W ∣_ ⊤))
  have hexc : ∀ x : W, x ∉ (MMP.Mori.exceptionalSet (𝟙 W) : Set W) := fun x hx =>
    hx (MMP.Mori.le_biregularLocus hbir (show x ∈ (⊤ : W.Opens) from trivial))
  have hlr : MMP.Mori.IsLogResolution (p ≫ sSb) (QDivisor.toRDivisor Γ) (𝟙 W) := by
    refine ⟨⟨inferInstance, isBirationalMorphism_of_isIso _, by rw [Category.id_comp]; exact hsm⟩,
      fun W' hW' => ?_, Or.inr ⟨(QDivisor.toRDivisor Γ).support, ?_, ?_⟩⟩
    · obtain ⟨x, hx⟩ := W'.isIrreducible.nonempty
      exact absurd (hW'.1 hx) (hexc x)
    · ext x
      rw [← DivisorWithCoeffs.coe_supp, TopologicalSpace.Closeds.coe_sup, Set.mem_union]
      exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd h' (hexc x)) id⟩
    · rw [Category.id_comp]
      refine hGsnc.of_support_subset (Finsupp.support_finsetSum.trans
        (Finset.biUnion_subset.mpr fun E hE => Finsupp.support_single_subset.trans
          (Finset.singleton_subset_iff.mpr (hΓG ?_))))
      rw [Finsupp.mem_support_iff] at hE ⊢
      intro h0
      apply hE
      change (QDivisor.toRDivisor Γ).coeff E = 0
      rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, h0, Rat.cast_zero]
  -- a general member `H' ∼_ℚ H`, and `C = H' / 2`
  obtain ⟨H', hH'e, -, hH'lin, hH'R, hH'lr, N', Z, hN', -, hZ1, hH'Z⟩ :=
    hlr.exists_isAmple_qLinearlyEquivalent_add hW.1 hHa
  set C₀ : QDivisor W := (1 / 2 : ℚ) • H' with hC₀
  have hH'1 : ∀ P, H'.coeff P ≤ 1 := fun P => by
    have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hH'Z
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul] at this
    rw [this]
    have hN'1 : (1 : ℚ) ≤ N' := by exact_mod_cast hN'
    have hZP : ((Z.coeff P : ℤ) : ℚ) ≤ 1 := by exact_mod_cast hZ1 P
    calc (N' : ℚ)⁻¹ * (Z.coeff P : ℚ) ≤ 1 * 1 := by
          rcases le_or_gt ((Z.coeff P : ℤ) : ℚ) 0 with h | h
          · nlinarith [inv_pos.mpr (show (0 : ℚ) < N' by linarith)]
          · exact mul_le_mul (inv_le_one_of_one_le₀ hN'1) hZP h.le zero_le_one
      _ = 1 := one_mul 1
  have hC₀P : ∀ P, C₀.coeff P = H'.coeff P / 2 := fun P => by
    simp only [hC₀, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; ring
  refine ⟨hXq, isCartierCombination_of_forall_isCartier hcart _, QDivisor.toRDivisor C₀,
    fun P => ?_, isCartierCombination_of_forall_isCartier hcart _, ?_, ?_⟩
  · rw [QDivisor.coeff_toRDivisor, hC₀P]
    have := hH'e P
    have : (0 : ℚ) ≤ H'.coeff P / 2 := by linarith
    exact_mod_cast this
  · -- `(W, Γ + C)` is klt: its support is snc and its coefficients are `< 1`
    have hmemS : ∀ P, (Γ + C₀).coeff P ≠ 0 → P.genericPoint ∈
        ((MMP.Mori.exceptionalSet (𝟙 W) ⊔ (QDivisor.toRDivisor Γ +
          QDivisor.toRDivisor H').supp.preimage (Scheme.Hom.continuous (𝟙 W)) :
            TopologicalSpace.Closeds W) : Set W) := by
      intro P hP
      rw [TopologicalSpace.Closeds.coe_sup]
      refine Or.inr (DivisorWithCoeffs.support_subset_supp ?_
        (MMP.Flips.primeDivisor_genericPoint_mem_support P))
      rw [DivisorWithCoeffs.coeff_add, hC₀P] at hP
      rw [DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
      intro h0
      have h0' : Γ.coeff P + H'.coeff P = 0 := by exact_mod_cast h0
      have := (hΓ01 P).1
      have := hH'e P
      apply hP
      linarith
    have hsnc : (Γ + C₀).IsSNC (p ≫ sSb) := by
      rcases hH'lr.isSNCSubset with hbot | ⟨s, hs, hsncs⟩
      · refine hGsnc.of_support_subset fun P hP => ?_
        exfalso
        have := hmemS P (Finsupp.mem_support_iff.mp hP)
        rw [hbot] at this
        exact this
      · rw [Category.id_comp] at hsncs
        refine hsncs.of_support_subset fun P hP => ?_
        have h1 := hmemS P (Finsupp.mem_support_iff.mp hP)
        rw [← hs] at h1
        obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp h1
        obtain rfl := eq_of_genericPoint_mem_support hPE
        rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
        simp [Finsupp.single_apply, hE]
    have hcoef : ∀ P, (Γ + C₀).coeff P < 1 := fun P => by
      rw [DivisorWithCoeffs.coeff_add, hC₀P]
      by_cases hH0 : H'.coeff P = 0
      · rw [hH0]; linarith [(hΓ01 P).2]
      · have hΓ0 := hH'R P hH0
        rw [QDivisor.coeff_toRDivisor] at hΓ0
        have hΓ0' : Γ.coeff P = 0 := by exact_mod_cast hΓ0
        rw [hΓ0']
        linarith [hH'1 P]
    have := isRealKltPair_of_isKltPair hcart
      (MMP.Mori.isKltPair_of_isSNC (p ≫ sSb) hW hsm hKW hsnc hcoef)
    rwa [map_add] at this
  · -- `K_W + Γ + C = c⁻¹ (m D_A + N) + (2k)⁻¹ div ψ` is positive on curves
    obtain ⟨k, hk, ψ, hψ⟩ := hH'lin
    have hpres : MMP.Flips.logCanonicalDivisor KW (QDivisor.toRDivisor Γ + QDivisor.toRDivisor C₀) =
        ∑ j, (![(c : ℝ)⁻¹, ((2 * k : ℕ) : ℝ)⁻¹] : Fin 2 → ℝ) j •
          Divisor.toRDivisor ((![m • DA + Nd, principalDivisor ψ] : Fin 2 → Divisor W) j) := by
      refine Finsupp.ext fun P => ?_
      have e1 := congrArg (fun D => DivisorWithCoeffs.coeff D P) hNd
      have e2 := congrArg (fun D => DivisorWithCoeffs.coeff D P) hψ
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_sub, zsmul_eq_mul, smul_eq_mul, hH] at e1 e2
      change (MMP.Flips.logCanonicalDivisor KW
        (QDivisor.toRDivisor Γ + QDivisor.toRDivisor C₀)).coeff P = _
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Fin.sum_univ_two]
      simp only [MMP.Flips.logCanonicalDivisor, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply]
      rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
        ← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
        ← DivisorWithCoeffs.coeff_apply]
      rw [Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, hC₀P,
        Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_smul]
      have e1' : ((Nd.coeff P : ℤ) : ℝ) = (c : ℝ) * ((KW.coeff P : ℤ) + (Γ.coeff P : ℝ)) := by
        have : ((Nd.coeff P : ℤ) : ℚ) = (c : ℚ) * ((KW.coeff P : ℤ) + Γ.coeff P) := e1
        exact_mod_cast this
      have e2' : ((principalDivisor ψ).coeff P : ℝ) =
          (k : ℝ) * ((H'.coeff P : ℝ) - 2 * m / c * (DA.coeff P : ℤ)) := by
        have := congrArg (Rat.cast : ℚ → ℝ) e2.symm
        push_cast at this ⊢
        linarith
      push_cast [nsmul_eq_mul]
      rw [e1', e2']
      have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      push_cast
      field_simp
      ring
    refine ⟨2, _, _, fun j => hcart _, hpres, fun C hC x hx => ?_⟩
    rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ (p ≫ sSb) C _ _ (fun j => hcart _)
      hpres hx, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hd1 := MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier (p ≫ sSb) hL (hcart _) C
      (fun y _ => Subsingleton.elim _ _)
    have hd2 := MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent (k := ℂ) (sX := p ≫ sSb)
      C.ι C.dim_le (hcart (principalDivisor ψ)) ⟨ψ, sub_zero _⟩
    have hd1' : (0 : ℝ) < ((m • DA + Nd).degreeOn ℂ (p ≫ sSb) C.ι C.dim_le (hcart _) : ℤ) := by
      exact_mod_cast hd1
    rw [hd2]
    have := mul_pos (inv_pos.mpr (show (0 : ℝ) < c by exact_mod_cast hc)) hd1'
    simp only [Int.cast_zero, mul_zero, add_zero]
    exact this.le

/-- **The program with scaling over `S̄`.** The `(K_W + Γ)`-program over `S̄` with scaling of an
ample divisor ends at a model `M` projective and birational over `S̄`, `ℚ`-factorial, with
`K_M + B_M` nef over `S̄`; every prime of `M` is the strict transform of a prime of `W`, with the
coefficient of `Γ`, and every `D_s` survives on `M`. -/
private theorem exists_model_of_program
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSn : IsNormalVariety ℂ sS)
    (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P) (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) [IsOpenImmersion ι] (hιs : ι ≫ sSb = sS)
    (hι : IsBirationalMorphism ι)
    (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb) (hSbn : IsNormalVariety ℂ sSb)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ Sb) (hW : IsNormalVariety ℂ (p ≫ sSb)) (hpb : IsBirationalMorphism p)
    (hpp : IsProjectiveMorphism p) (hsm : IsSmoothScheme (p ≫ sSb))
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sSb)) (hdimW : topologicalKrullDim W = 4)
    (D : I → MMP.Mori.PrimeDivisor W)
    (hD : ∀ s : I, haveI := hι.isDominant
      (⟨W, p, hW, hpb, D s⟩ : DivisorOver ℂ sSb).valuation =
        (s : Valuation S.functionField _).comap (functionFieldMap ι))
    (Γ : QDivisor W) (hΓ01 : ∀ P, 0 ≤ Γ.coeff P ∧ Γ.coeff P < 1)
    (G : QDivisor W) (hGsnc : G.IsSNC (p ≫ sSb)) (hΓG : Γ.support ⊆ G.support)
    (hΓC : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor S),
      p P.genericPoint = ι Q.genericPoint → Γ.coeff P = C.coeff Q)
    (hΓD : ∀ (s : I) (a : ℝ), IsValuationLogDiscrepancy sS C s a → (Γ.coeff (D s) : ℝ) = 1 - a)
    (hΓE : ∀ (P : MMP.Mori.PrimeDivisor W) (ξ : Valuation S.functionField _) (a : ℝ),
      haveI := hι.isDominant
      (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sSb).valuation = ξ.comap (functionFieldMap ι) →
      MMP.Intersection.IsExceptionalValuation ℂ sS ξ → IsValuationLogDiscrepancy sS C ξ a →
      ξ ∉ I → 1 - a < (Γ.coeff P : ℝ))
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (p ≫ sSb) 4)
    (hkltW : MMP.Mori.IsKltPair (p ≫ sSb) 4 KW Γ) :
    ∃ (M : Scheme.{0}) (_ : IsIntegral M) (_ : CompactSpace M) (_ : IsLocallyNoetherian M)
      (_ : IsNormal M) (sM : M ⟶ Spec (.of ℂ)) (_ : LocallyOfFiniteType sM)
      (_ : QuasiCompact sM) (πM : M ⟶ Sb) (KM : Divisor M) (BM : QDivisor M),
      MMP.Mori.IsProjectiveVariety ℂ sM ∧ πM ≫ sSb = sM ∧ IsProjectiveMorphism πM ∧
      ∃ hπb : IsBirationalMorphism πM, IsQFactorial sM ∧ (∃ n : ℕ, KM.IsCanonicalDivisor sM n) ∧
      QDivisor.IsRelativelyNef sM πM (Divisor.toQDivisor KM + BM) ∧
      (haveI := hpb.isDominant; haveI := hπb.isDominant
        ∀ P : MMP.Mori.PrimeDivisor M, ∃ D₀ : MMP.Mori.PrimeDivisor W,
          D₀.valuationOver p = P.valuationOver πM ∧ BM.coeff P = Γ.coeff D₀) ∧
      (haveI := hpb.isDominant; haveI := hπb.isDominant
        ∀ s : I, ∃ P : MMP.Mori.PrimeDivisor M, P.valuationOver πM = (D s).valuationOver p) := by
  classical
  haveI := hpb.isDominant
  haveI : LocallyOfFiniteType (p ≫ sSb) := hW.1.toLocallyOfFiniteType
  -- the scaling divisor and the program with scaling
  obtain ⟨hXq, hBc, Cs, hCs0, hCsc, hkltBC, hnefBC⟩ :=
    exists_scaling_divisor hSbp hSbn p hW hpb hpp hsm hWp Γ hΓ01 G hGsnc hΓG hKW hkltW
  obtain ⟨⟨N, Y, sY, _, _, _, _, πY, KY, BY, CY, lam, T, sT, f, g, fp, φ, hmod, hstep, hnefN⟩, -⟩ :=
    exists_scalingProgram_and_finite_of_isBirationalMorphism (p ≫ sSb) sSb p rfl hWp hSbp hSbn
      hpp hpb hXq KW hKW (QDivisor.toRDivisor Γ) Cs
      (fun P => by rw [QDivisor.coeff_toRDivisor]; exact_mod_cast (hΓ01 P).1) hCs0 hBc hCsc
      hkltBC hnefBC
  -- dimensions
  have hdSb : topologicalKrullDim Sb = 4 := by
    haveI := hSbn.1
    haveI := hW.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sSb (p ≫ sSb) hpb, hdimW]
  obtain ⟨-, nS, KS, hKS, hKSC⟩ := id hklt.1.isPair
  have hnS : nS = 4 := by
    have h1 := hKS.topologicalKrullDim_eq
    rw [topologicalKrullDim_eq_of_isOpenImmersion (sSb := sSb) ι, hdSb] at h1
    exact_mod_cast h1.symm
  subst hnS
  have hcan : ∀ i ≤ N, IsBirationalMorphism (modelMap p πY i) →
      Divisor.IsCanonicalDivisor (modelStr (p ≫ sSb) sY i) 4 (divisorSeq KW KY i) := by
    intro i hi hb
    obtain ⟨-, -, hQ, ⟨m, hm⟩, -⟩ := hmod i hi
    haveI := hSbn.1
    haveI := hQ.1.1
    have h1 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sSb
      (modelStr (p ≫ sSb) sY i) hb
    have h2 := hm.topologicalKrullDim_eq
    have hm4 : m = 4 := by
      have := h2.symm.trans (h1.symm.trans hdSb)
      exact_mod_cast this
    subst hm4
    exact hm
  -- the invariants along the program
  have key : ∀ i, i ≤ N → ∃ hb : IsBirationalMorphism (modelMap p πY i),
      (haveI := hb.isDominant
        ∀ P : MMP.Mori.PrimeDivisor (modelSeq W Y i), ∃ D₀ : MMP.Mori.PrimeDivisor W,
          D₀.valuationOver p = P.valuationOver (modelMap p πY i) ∧
          (divisorSeq (QDivisor.toRDivisor Γ) BY i).coeff P = ((Γ.coeff D₀ : ℚ) : ℝ)) ∧
      (haveI := hb.isDominant
        ∀ s : I, ∃ P : MMP.Mori.PrimeDivisor (modelSeq W Y i),
          P.valuationOver (modelMap p πY i) = (D s).valuationOver p) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨hpb, fun P => ⟨P, rfl, QDivisor.coeff_toRDivisor _ _⟩, fun s => ⟨D s, rfl⟩⟩
    | succ i ih =>
      intro hi
      obtain ⟨hb, hpr, hsv⟩ := ih (by omega)
      obtain ⟨-, -, hfg, hfpg, hneg, -, hcase, hBY, -⟩ := hstep i (by omega)
      obtain ⟨hms, hproj, hQ, -, -⟩ := hmod i (by omega)
      obtain ⟨hms', hproj', hQ', -, -⟩ := hmod (i + 1) hi
      haveI : LocallyOfFiniteType (modelStr (p ≫ sSb) sY i) := hQ.1.1.toLocallyOfFiniteType
      haveI : QuasiCompact (modelStr (p ≫ sSb) sY i) := hQ.1.1.toQuasiCompact
      haveI : LocallyOfFiniteType (sY i) := hQ'.1.1.toLocallyOfFiniteType
      haveI : QuasiCompact (sY i) := hQ'.1.1.toQuasiCompact
      exact step_invariant sS hSn C hC hklt I hI ι hιs hι hSbp hSbn p hW hpb hpp D hD Γ hΓC hΓD hΓE
        hms hb hproj' hms' hQ hQ' hfg hfpg hKS hKSC (hcan i (by omega) hb)
        (fun hb' => hcan (i + 1) hi hb') hneg hcase hBY hpr hsv
  -- the end of the program
  obtain ⟨hbN, hprN, hsvN⟩ := key N le_rfl
  obtain ⟨hmsN, hprojN, hQN, -, -⟩ := hmod N le_rfl
  haveI := hbN.isDominant
  obtain ⟨BQN, hBQN⟩ := exists_qDivisor_eq (divisorSeq (QDivisor.toRDivisor Γ) BY N) fun P => by
    obtain ⟨D₀, -, h⟩ := hprN P
    exact ⟨_, h⟩
  haveI : LocallyOfFiniteType (modelStr (p ≫ sSb) sY N) := hQN.1.1.toLocallyOfFiniteType
  haveI : QuasiCompact (modelStr (p ≫ sSb) sY N) := hQN.1.1.toQuasiCompact
  haveI : IsSeparated sSb := hSbn.1.toIsSeparated
  refine ⟨modelSeq W Y N, inferInstance, inferInstance, inferInstance, inferInstance,
    modelStr (p ≫ sSb) sY N, inferInstance, inferInstance, modelMap p πY N, divisorSeq KW KY N,
    BQN, hprojN, hmsN, IsProjectiveMorphism.of_comp _ sSb (hmsN ▸ hprojN.isProjective), hbN, hQN,
    ⟨4, hcan N le_rfl hbN⟩, ?_, fun P => ?_, hsvN⟩
  · refine MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor
      (MMP.Fourfold.isQCartier_of_isQFactorial _ hQN _) ?_
    rw [map_add, QDivisor.toRDivisor_toQDivisor, hBQN]
    exact hnefN
  · obtain ⟨D₀, h1, h2⟩ := hprN P
    refine ⟨D₀, h1, ?_⟩
    rw [← hBQN, QDivisor.coeff_toRDivisor] at h2
    exact_mod_cast h2

/-- **The extraction over a compactification.** The extraction of `I`, given an open immersion
`ι : S ⟶ S̄` into a normal projective variety. -/
private theorem exists_extraction_of_compactification
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSn : IsNormalVariety ℂ sS)
    (hdim : topologicalKrullDim S = 4) (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P)
    (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {Sb : Scheme.{0}} [IsIntegral Sb] [IsLocallyNoetherian Sb] [IsNormal Sb] [CompactSpace Sb]
    {sSb : Sb ⟶ Spec (.of ℂ)} (ι : S ⟶ Sb) [IsOpenImmersion ι] (hιs : ι ≫ sSb = sS)
    (hSbp : MMP.Mori.IsProjectiveVariety ℂ sSb) (hSbn : IsNormalVariety ℂ sSb) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (q : V ⟶ S) (E : I → MMP.Mori.PrimeDivisor V)
      (hV : IsQFactorial (q ≫ sS)) (hq : IsBirationalMorphism q),
      IsProjectiveMorphism q ∧
      (∀ s : I, (⟨V, q, hV.1, hq, E s⟩ : DivisorOver ℂ sS).valuation = s) ∧
      Function.Injective E ∧
      (∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) q.toRationalMap P ↔ P ∈ Set.range E) := by
  classical
  haveI : Nonempty S := inferInstance
  have hι : IsBirationalMorphism ι := isBirationalMorphism_of_isOpenImmersion' ι
  haveI := hι.isDominant
  -- the valuations of `I` have centres on `S̄`
  have hv : ∀ s : I, MMP.Flips.HasNonemptyCenter ℂ sSb
      ((s : Valuation S.functionField _).comap (functionFieldMap ι)) := fun s => by
    obtain ⟨-, a, ha, -⟩ := hI s.2
    exact hasNonemptyCenter_comap hSbn ι hιs hι ha
  -- a resolution carrying the valuations, with an snc divisor `G`
  let T : Finset (MMP.Mori.PrimeDivisor Sb) :=
    C.support.image fun Q => OpenWeilRestriction.primeDivisorMap ι Q
  obtain ⟨W, _, _, _, _, p, hW, hpb, hpp, hsm, hWp, hval, G, hGsnc, hGexc, hGT⟩ :=
    exists_resolution hSbn hSbp
      ((topologicalKrullDim_eq_of_isOpenImmersion (sSb := sSb) ι).symm.trans hdim) (κ := I)
      (fun s => (s : Valuation S.functionField _).comap (functionFieldMap ι)) hv T
  choose D hD using hval
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  -- the boundary `Γ`
  obtain ⟨Γ, hΓ01, hΓG, hΓC, hΓD, hΓE⟩ := exists_boundary sS hSn C hC hklt I hI hSbn ι hιs hι
    p hW hpb G hGexc (fun P Q hQ hPQ => hGT P _
      (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hQ)) hPQ)
  -- `(W, Γ)` is lc
  haveI : LocallyOfFiniteType sSb := hSbn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ sSb) := hW.1.toLocallyOfFiniteType
  have hdimW : topologicalKrullDim W = 4 := by
    rw [← hdim, topologicalKrullDim_eq_of_isOpenImmersion (sSb := sSb) ι]
    haveI := hSbn.1
    haveI := hW.1
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sSb (p ≫ sSb) hpb).symm
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor (p ≫ sSb) hW (n := 4) hdimW
  have hkltW := MMP.Mori.isKltPair_of_isSNC (p ≫ sSb) hW hsm hKW (hGsnc.of_support_subset hΓG)
    (fun P => (hΓ01 P).2)
  -- the end of the program with scaling over `S̄`
  obtain ⟨M, _, _, _, _, sM, _, _, πM, KM, BM, hMp, hπs, hπp, hπb, hMQ, hKM, hnefM, hprime,
      hsurvive⟩ :=
    exists_model_of_program sS hSn C hC hklt I hI ι hιs hι hSbp hSbn p hW hpb hpp hsm hWp hdimW
      D hD Γ hΓ01 G hGsnc hΓG hΓC (fun s a ha => hΓD s (D s) a (hD s) ha) hΓE hKW hkltW
  exact exists_extraction_of_logMinimalModel sS hSn C hC hklt I hI ι hιs hι hSbp hSbn p hW hpb hpp
    D hD Γ hΓC (fun s a ha => hΓD s (D s) a (hD s) ha) hΓE hMp hπs hπp hπb hMQ hKM hnefM hprime
    hsurvive

/-! ### The extraction -/

/-- **The extraction.** There is a projective birational morphism `q : V ⟶ S` from a
`ℚ`-factorial variety and prime divisors `E_s` of `V` with `ord_{E_s} = s`, `s ∈ I`, such that
`s ↦ E_s` is a bijection onto the `q`-exceptional prime divisors. -/
private theorem exists_extraction
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sS)
    (hdim : topologicalKrullDim S = 4) (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P)
    (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (q : V ⟶ S) (E : I → MMP.Mori.PrimeDivisor V)
      (hV : IsQFactorial (q ≫ sS)) (hq : IsBirationalMorphism q),
      IsProjectiveMorphism q ∧
      (∀ s : I, (⟨V, q, hV.1, hq, E s⟩ : DivisorOver ℂ sS).valuation = s) ∧
      Function.Injective E ∧
      (∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) q.toRationalMap P ↔ P ∈ Set.range E) := by
  have hSn : IsNormalVariety ℂ sS := ⟨hS.toIsVariety, inferInstance⟩
  obtain ⟨Sb, _, _, _, _, sSb, ι, hι, hιs, hSbp, hSbn⟩ :=
    exists_normal_projective_compactification hSn hS
  exact exists_extraction_of_compactification sS hSn hdim C hC hklt I hI ι hιs hSbp hSbn

private theorem solution
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sS)
    (hdim : topologicalKrullDim S = 4) (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P)
    (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {n : ℕ} {K : Divisor S} (hK : K.IsCanonicalDivisor sS n) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (q : V ⟶ S) (E : I → MMP.Mori.PrimeDivisor V) (a : I → ℚ) (CV : QDivisor V)
      (hV : IsQFactorial (q ≫ sS)) (hq : IsBirationalMorphism q),
      IsProjectiveMorphism q ∧
      (∀ s : I, (⟨V, q, hV.1, hq, E s⟩ : DivisorOver ℂ sS).valuation = s) ∧
      Function.Injective E ∧
      (∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) q.toRationalMap P ↔ P ∈ Set.range E) ∧
      (∀ s : I, IsValuationLogDiscrepancy sS C s (a s)) ∧
      CV = inverseTransformDivisor q C + ∑ s : I, Finsupp.single (E s) (1 - a s) ∧
      (∀ P, 0 ≤ CV.coeff P) ∧
      IsKltPair (q ≫ sS) CV ∧
      IsCrepantBoundary sS n K C q hV.1 hq CV := by
  obtain ⟨V, _, _, _, q, E, hV, hq, hqp, hval, hinj, hexc⟩ :=
    exists_extraction sS hS hdim C hC hklt I hI
  obtain ⟨a, CV, ha, hCV, hCV0, hCVk, hCVc⟩ :=
    boundary_of_extraction sS C hC hklt I hI hK q E hV hq hqp hval hinj hexc
  exact ⟨V, inferInstance, inferInstance, inferInstance, q, E, a, CV, hV, hq, hqp, hval, hinj,
    hexc, ha, hCV, hCV0, hCVk, hCVc⟩

end Proof_thm_fourfold_quasiprojective_specified_extraction_4

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Specified extraction on a quasi-projective klt fourfold.** Let `(S, C)` be an effective klt
pair on a normal quasi-projective complex fourfold and `I` a finite set of valuations of `k(S)` in
the low-discrepancy set `I(S, C)` (exceptional over `S`, with `a(s; S, C) ≤ 1`). There is a
projective birational morphism `q : V ⟶ S` from a `ℚ`-factorial variety `V`, with prime divisors
`E_s` of `V` (`s ∈ I`) such that `ord_{E_s} = s`, `s ↦ E_s` is a bijection onto the `q`-exceptional
prime divisors, and, writing `a_s = a(s; S, C)`, the effective boundary
`C_V = q⁻¹_* C + ∑_{s ∈ I} (1 - a_s) E_s` makes `(V, C_V)` klt and is the crepant boundary of
`(S, C)` on `V`, i.e. `K_V + C_V = q^*(K_S + C)`. -/
@[mmp "thm_fourfold_quasiprojective_specified_extraction_4"]
public theorem exists_specifiedExtraction_of_isQuasiProjectiveVariety
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sS)
    (hdim : topologicalKrullDim S = 4) (C : QDivisor S) (hC : ∀ P, 0 ≤ C.coeff P)
    (hklt : IsKltPair sS C)
    (I : Finset (Valuation S.functionField (WithZero (Multiplicative ℤ))))
    (hI : (I : Set _) ⊆ lowDiscrepancySet sS C)
    {n : ℕ} {K : Divisor S} (hK : K.IsCanonicalDivisor sS n) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (q : V ⟶ S) (E : I → MMP.Mori.PrimeDivisor V) (a : I → ℚ) (CV : QDivisor V)
      (hV : IsQFactorial (q ≫ sS)) (hq : IsBirationalMorphism q),
      IsProjectiveMorphism q ∧
      (∀ s : I, (⟨V, q, hV.1, hq, E s⟩ : DivisorOver ℂ sS).valuation = s) ∧
      Function.Injective E ∧
      (∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) q.toRationalMap P ↔ P ∈ Set.range E) ∧
      (∀ s : I, IsValuationLogDiscrepancy sS C s (a s)) ∧
      CV = inverseTransformDivisor q C + ∑ s : I, Finsupp.single (E s) (1 - a s) ∧
      (∀ P, 0 ≤ CV.coeff P) ∧
      IsKltPair (q ≫ sS) CV ∧
      IsCrepantBoundary sS n K C q hV.1 hq CV :=
        by revert S sS hS hdim C hC hklt I hI n K hK; first | exact Proof_thm_fourfold_quasiprojective_specified_extraction_4.solution | exact Proof_thm_fourfold_quasiprojective_specified_extraction_4.solution _ | exact Proof_thm_fourfold_quasiprojective_specified_extraction_4.solution _ _ | exact Proof_thm_fourfold_quasiprojective_specified_extraction_4.solution _ _ _ | exact Proof_thm_fourfold_quasiprojective_specified_extraction_4.solution _ _ _ _

end MMP.Fourfold

