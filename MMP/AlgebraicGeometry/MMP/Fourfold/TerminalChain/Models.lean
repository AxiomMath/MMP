module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.BridgeLabels
import MMP.AlgebraicGeometry.MMP.Threefold.StepDiagram.BadLociTerminalChain
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
import MMP.RingTheory.SerreCondition.ExtSupportCriterion
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.Analysis.Complex.CauchyTransformRungeMontel

/-!
# The models of a terminal chain

Let `C = (p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`, with labels `S_h`. Its models are the junctions
`(Y_i, Θ_i)` and the models `(V_k, Θ_k)`, `k ≤ m_i`, of the programmes of its bridges,
`(V_0, Θ_0) = (Y_i, Θ_i')` being the decreased pair.

Every model `(Y, Θ)` is an effective terminal pair on a normal projective `ℚ`-factorial threefold:
a junction because it is crepant over `(X_i, B_i)` and extracts all of `I(X_i, B_i)`, a bridge
model because no divisor is lost in a bridge programme. Every label persists as a prime divisor
`S_h^Y` of every model, distinct labels giving distinct prime divisors, and `Θ = ∑_h b_h S_h^Y`
with `b_h = b_h^Y ∈ [0, 1)`.

Along the models, in their order, the log discrepancy `a(v; -)` of every normalized divisorial
valuation `v` is nondecreasing: at a coefficient decrease the boundary only drops along the
`E_{i,s}`; along a flip of a bridge `a⁻ ≤ a⁺` (strict over the bad locus, an equality off it);
and the end `V_{m_i}` of a bridge is identified with the next junction `Y_{i+1}` by a crepant
isomorphism. Since a label coefficient is `b_h^Y = 1 - a(ord_{S_h^Y}; Y, Θ)`, every label
coefficient is nonincreasing along the models.

Consequently a varying label, one whose junction coefficients `b_h^{(i)}` are not eventually
constant, has `b_h^{(i)} > 0` for every `i`: a zero coefficient would stay zero, and the label
would be fixed.

## Main results

* `MMP.Fourfold.StabilizedTail.TerminalChain.isKltTerminalPair_and_antitone_and_monotone`: the
  models of a terminal chain are terminal pairs whose boundaries are supported on the labels with
  coefficients in `[0, 1)`; label coefficients are nonincreasing and log discrepancies
  nondecreasing along the chain.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsVaryingLabel.pos_of_isJunctionLabelCoefficient`:
  the coefficient of a varying label at every junction is positive.

## Implementation notes

* The models are listed in the lexicographic order of their indices
  `MMP.Fourfold.StabilizedTail.TerminalChain.ModelIndex`, the junction `(i, none)` coming before
  the bridge models `(i, some k)`; it is expressed through the rank `(i, 0)`, resp. `(i, k + 1)`,
  in `ℕ ×ₗ ℕ`.
* "`Θ = ∑_h b_h S_h^Y`" reads: every prime divisor in the support of `Θ` is the centre of a label,
  and the coefficient of `Θ` at the centre of a label `S_h` is the label coefficient `b_h^Y`
  (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCoefficient`).
* A normalized divisorial valuation `v` is given as a valuation `ν` of `k(X_0)`; on the junction
  `Y_i` it is the valuation whose image in `k(X_i)` through `p_i` is `ν` carried to `k(X_i)`
  (`MMP.Fourfold.StabilizedTail.IsTransportedValuationFrom`), and on the model `V_k` of the
  `i`-th bridge the valuation whose image in `k(Z_i)` through `π_k : V_k ⟶ Z_i` is the image of
  that valuation through `f_i`, as for the centres of labels
  (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCentre`). Log discrepancies are values of
  `MMP.Fourfold.IsValuationLogDiscrepancy`, which holds only for normalized divisorial
  valuations.
* The coefficient of a label at a junction is the predicate
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsJunctionLabelCoefficient`, so positivity reads:
  every `b` that is the coefficient `b_h^{(i)}` is positive.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

namespace StabilizedTail

namespace TerminalChain

/-! ### Log discrepancies along a threefold step -/

/-- Two birational morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y` to a separated scheme give a
birational map `φ : X ⤏ X'` with `φ ≫ f' = f`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} [IsReduced X]
    [IsReduced X'] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', MMP.Mori.RationalMap.IsBirational φ ∧
      φ.compHom f' = f.toRationalMap := by
  obtain ⟨em, hem⟩ := hf
  obtain ⟨ep, hep⟩ := hf'
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 Y) hem
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep f' (𝟙 Y) hep
  set e := em.trans ep.symm with he
  have H : e.IsOver (f ≫ 𝟙 Y) (f' ≫ 𝟙 Y) := h1.trans h2.symm
  have H' : e.iso.hom ≫ e.target.ι ≫ f' = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using H
  refine ⟨e.toRationalMap, MMP.Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H']
  simp

section OffBadLocus

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- Pulling valuations back along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {g : R →+* S} (hg : Function.Surjective g)
    {v w : Valuation S (WithZero (Multiplicative ℤ))} (h : v.comap g = w.comap g) : v = w := by
  ext t
  obtain ⟨s, rfl⟩ := hg t
  exact congrArg (fun u : Valuation R (WithZero (Multiplicative ℤ)) => u s) h

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme is that of its closure,
through the identification of function fields. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- The valuation of a prime divisor of `X`, regarded as a divisor over `X`. -/
private theorem valuation_ofPrimeDivisor {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation := by
  ext t
  change P.divisorialValuation (functionFieldMap (𝟙 X) t) = _
  rw [functionFieldMap_id_apply]

/-- An open immersion of nonempty irreducible schemes is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {W Y : Scheme.{0}} [IrreducibleSpace W]
    [IrreducibleSpace Y] [Nonempty W] (j : W ⟶ Y) [IsOpenImmersion j] :
    IsBirationalMorphism j := by
  let U : W.Opens := ⊤
  let V' : Y.Opens := (U.ι ≫ j).opensRange
  have hle : U ≤ j ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE j U V' ⟨w, trivial⟩
    ⟨_, ⟨⟨w, trivial⟩, rfl⟩⟩ hle ?_
  have e : j.resLE V' U hle = (U.ι ≫ j).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- A divisor over `X` with the valuation of a prime divisor `P` of `X` has discrepancy
`-B.coeff P`. -/
private theorem isDiscrepancy_neg_coeff_of_valuation_eq {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hP : MMP.Mori.IsPair sX B) (hK : K.IsCanonicalDivisor sX n)
    (hX : IsNormalVariety ℂ sX) (P : MMP.Mori.PrimeDivisor X) (D : DivisorOver ℂ sX)
    (hvD : D.valuation = (DivisorOver.ofPrimeDivisor ℂ hX P).valuation) :
    IsDiscrepancy sX n K B D (-B.coeff P) := by
  obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  obtain ⟨cD, hcD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  have e := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hvD
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hvD) hcD hc₀
  rw [← hc₀.eq_neg_coeff_of_ofPrimeDivisor hX, ← e]
  exact hcD

/-- **Crepant invariance**, with the structure morphism of the source given up to equality: if
`ΔY` is the crepant boundary of `(X, Δ)` along a birational `φ : Y ⟶ X`, divisors over `Y` and
over `X` with corresponding valuations have the same discrepancies. -/
private theorem isDiscrepancy_iff_of_crepant {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {KX : Divisor X} {Δ : QDivisor X}
    {KY : Divisor Y} {ΔY : QDivisor Y} (hP : MMP.Mori.IsPair sX Δ)
    (hKX : KX.IsCanonicalDivisor sX n) (φ : Y ⟶ X) [IsDominant φ] (hs : φ ≫ sX = sY)
    (hY : IsNormalVariety ℂ sY) (hφ : IsBirationalMorphism φ) (hKY : KY.IsCanonicalDivisor sY n)
    (hcb : ∀ (F : MMP.Mori.PrimeDivisor Y) (D : DivisorOver ℂ sX), D.valuation = F.valuationOver φ →
      IsDiscrepancy sX n KX Δ D (-ΔY.coeff F))
    (E : DivisorOver ℂ sY) (E' : DivisorOver ℂ sX)
    (hv : E'.valuation = E.valuation.comap (functionFieldMap φ)) (a : ℚ) :
    IsDiscrepancy sY n KY ΔY E a ↔ IsDiscrepancy sX n KX Δ E' a := by
  subst hs
  have hcb' : IsCrepantBoundary sX n KX Δ φ hY hφ ΔY := fun F => hcb F _ rfl
  exact (IsPair.isDiscrepancy_iff_of_crepant hP φ hY hφ hKX hKY (Or.inl hcb')).2 E E' hv a

omit [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
  [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] in
/-- The biregular locus of `f⁺` maps to `X⁻` by an open immersion over `Z`. -/
private theorem exists_isOpenImmersion_comp_eq (fm : Xm ⟶ Z) (fp : Xp ⟶ Z) :
    ∃ φ : (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme ⟶ Xm, IsOpenImmersion φ ∧
      φ ≫ fm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp := by
  have : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  have : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  refine ⟨(fp ∣_ commonBiregularLocus fm fp) ≫ inv (fm ∣_ commonBiregularLocus fm fp) ≫
      (fm ⁻¹ᵁ commonBiregularLocus fm fp).ι, inferInstance, ?_⟩
  simp only [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]

/-- If the center of `Dp` meets the common biregular locus, the discrepancies of corresponding
divisors agree. -/
private theorem discrepancy_eq_of_nonempty_inter
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (hU : ((Dp.center : Set Xp) ∩ (fp ⁻¹ᵁ commonBiregularLocus fm fp : Set Xp)).Nonempty)
    {mm : ℕ} (hKm : Divisor.IsCanonicalDivisor sXm mm K)
    (hPp : IsPairWith sXp mm (flipTransform fm fp K) (flipTransform fm fp B))
    {cp cm : ℚ} (hcp : IsDiscrepancy sXp mm (flipTransform fm fp K) (flipTransform fm fp B) Dp cp)
    (hcm : IsDiscrepancy sXm mm K B Dm cm) :
    cm = cp := by
  have : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  have := h.isBirationalMorphism_minus.isDominant
  have := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPp Dp _ hU
  have hcE := (hiff cp).mp hcp
  have : Nonempty (fp ⁻¹ᵁ commonBiregularLocus fm fp) := ⟨⟨hU.choose, hU.choose_spec.2⟩⟩
  obtain ⟨φ, hφo, hφ⟩ := exists_isOpenImmersion_comp_eq fm fp
  have hs : φ ≫ sXm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp := by
    rw [← h.comp_eq_minus, ← h.comp_eq_plus, ← Category.assoc, hφ, Category.assoc]
  have hφb : IsBirationalMorphism φ := isBirationalMorphism_of_isOpenImmersion φ
  have : IsDominant φ := hφb.isDominant
  have : IsDominant (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι :=
    Opens.isDominant_ι ((fp ⁻¹ᵁ commonBiregularLocus fm fp).isOpen.dense
      ⟨hU.choose, hU.choose_spec.2⟩)
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective.2
  have hvF : ∀ F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme,
      (F.valuationOver φ).comap (functionFieldMap fm) =
        MMP.Mori.PrimeDivisor.valuationOver
          (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F) fp := by
    intro F
    ext t
    simp only [MMP.Mori.PrimeDivisor.valuationOver, Valuation.comap_apply]
    rw [divisorialValuation_primeDivisorMap, Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hφ]
  have hvE : Dm.valuation = (DivisorOver.valuation (⟨_, Dp.f ∣_ _, hY, hf, E'⟩ :
      DivisorOver ℂ ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp))).comap
        (functionFieldMap φ) := by
    apply comap_injective_of_surjective hfm
    rw [← hv, hval]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hφ]
  have hcb : ∀ (F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme)
      (D : DivisorOver ℂ sXm), D.valuation = F.valuationOver φ →
      IsDiscrepancy sXm mm K B D
        (-((flipTransform fm fp B).restrictOpen (fp ⁻¹ᵁ commonBiregularLocus fm fp)).coeff F) := by
    intro F D hD
    obtain ⟨Pm, -, hPm, -, -, -, hcoef, -⟩ := h.exists_primeDivisor_valuationOver_eq
      (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F)
    rw [DivisorWithCoeffs.coeff_restrictOpen, hcoef]
    refine isDiscrepancy_neg_coeff_of_valuation_eq hB.isPair hKm h.isNormalVariety_minus Pm D ?_
    rw [valuation_ofPrimeDivisor, hD]
    apply comap_injective_of_surjective hfm
    rw [hvF, ← hPm]
    rfl
  exact hcm.eq ((isDiscrepancy_iff_of_crepant hB.isPair hKm φ hs hcE.1 hφb hcE.2.1 hcb
    ⟨_, Dp.f ∣_ _, hY, hf, E'⟩ Dm hvE cp).mp hcE)

/-- Off the bad locus the log discrepancies of corresponding divisors agree. -/
private theorem eq_of_not_subset_badLocusPlus (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (hc : ¬ (Dp.center : Set Xp) ⊆ badLocusPlus fm fp)
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am = ap := by
  have : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  have := h.isBirationalMorphism_minus.isDominant
  have := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hU : ((Dp.center : Set Xp) ∩ (fp ⁻¹ᵁ commonBiregularLocus fm fp : Set Xp)).Nonempty := by
    rw [Set.not_subset] at hc
    obtain ⟨x, hx, hxW⟩ := hc
    refine ⟨x, hx, ?_⟩
    rw [coe_badLocusPlus, coe_badLocusBase] at hxW
    simpa using hxW
  obtain ⟨mp, hKp⟩ := h.isCanonicalDivisor_plus
  obtain ⟨mm, hKm⟩ := h.isCanonicalDivisor
  obtain rfl : mp = n := by
    exact_mod_cast hKp.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hap)
  obtain rfl : mm = n' := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ham)
  obtain rfl : mm = mp := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (h.dim_minus.trans (h.dim_plus.symm.trans hKp.topologicalKrullDim_eq))
  have hPp : IsPairWith sXp mm (flipTransform fm fp K) (flipTransform fm fp B) :=
    ⟨h.isNormalVariety_plus, hKp, h.isQCartier_plus⟩
  obtain ⟨cp, hcp⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPp.isPair hKp Dp
  obtain ⟨cm, hcm⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm Dm
  rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcp ap).mp hap).2,
    ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcm am).mp ham).2]
  rw [discrepancy_eq_of_nonempty_inter h hB Dp Dm hv hU hKm hPp hcp hcm]

/-- **The comparison** `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`. -/
private theorem le_of_isLogDiscrepancy (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm) (hDm : IsProper Dm.f)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am ≤ ap := by
  by_cases hc : (Dp.center : Set Xp) ⊆ badLocusPlus fm fp
  · have ham' : IsValuationLogDiscrepancy sXm B Dm.valuation am := ⟨n', Dm, hDm, rfl, ham⟩
    have hap' : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) Dp.valuation ap :=
      ⟨n, Dp, hap.2.1, rfl, hap⟩
    have hCm : MMP.Intersection.IsCentre ℂ sXm Dm.valuation Dm.center := ⟨Dm, hDm, rfl, rfl⟩
    have hCp : MMP.Intersection.IsCentre ℂ sXp Dp.valuation Dp.center :=
      ⟨Dp, hap.2.1, rfl, rfl⟩
    have hT := IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus h hv
      ham' hap' hCm hCp
    exact (show am < ap from (hT.out 3 1).mp hc).le
  · exact (eq_of_not_subset_badLocusPlus h hB Dp Dm hv hc hap ham).le

omit [CompactSpace Xm] in
/-- The log discrepancy of a proper divisor over a pair exists. -/
private theorem exists_isLogDiscrepancy (hB : MMP.Fourfold.IsPair sXm B) (Dm : DivisorOver ℂ sXm)
    (hDm : IsProper Dm.f) :
    ∃ (n : ℕ) (am : ℝ), MMP.Intersection.IsLogDiscrepancy sXm n (QDivisor.toRDivisor B) Dm am := by
  obtain ⟨-, n, K', hK', -⟩ := hB.isPair
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hK' Dm
  exact ⟨n, _, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDm⟩

/-- Every divisor `D⁺` over `X⁺` has a counterpart `D⁻` over `X⁻`, proper, whose valuation
agrees with that of `D⁺` on `k(Z)`. -/
private theorem exists_properDivisorOver_minus (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (D : DivisorOver ℂ sXp) :
    haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ D' : DivisorOver ℂ sXm, IsProper D'.f ∧
      D.valuation.comap (functionFieldMap fp) = D'.valuation.comap (functionFieldMap fm) := by
  have : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  have := h.isBirationalMorphism_minus.isDominant
  have := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have : IsSeparated sZ := h.isProjectiveVariety_target.1.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := by
    have e : (Z ↘ ⊤_ Scheme) = sZ ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
    rw [e]
    infer_instance
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq
    h.isSmallMorphism_plus.isBirationalMorphism h.isBirationalMorphism_minus
  have : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have : IsProper fp := h.isSmallMorphism_plus.isProper
  obtain ⟨W, g, g', hW, hg, -, hg'p, hg', -, hcomm, P, hP⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq
      h.isNormalVariety_plus h.isNormalVariety_minus fp fm φ hφ hφS D
  have hW' : IsNormalVariety ℂ (g' ≫ sXm) := by
    rwa [← h.comp_eq_minus, ← Category.assoc, ← hcomm, Category.assoc, h.comp_eq_plus]
  have : IsIntegral W := hW.1.toIsIntegral
  have : IsNormal W := hW.2
  have : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ sXp)
  have := hg.isDominant
  have := hg'.isDominant
  refine ⟨⟨W, g', hW', hg', P⟩, hg'p, ?_⟩
  rw [← hP]
  ext t
  change P.divisorialValuation (functionFieldMap g (functionFieldMap fp t)) =
    P.divisorialValuation (functionFieldMap g' (functionFieldMap fm t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  simp only [hcomm]

end OffBadLocus

/-! ### Junctions are terminal -/

/-- The centre of a divisor exceptional over a normal variety has codimension at least two. -/
private theorem two_le_codimension_center_of_isExceptional {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (D : DivisorOver ℂ sY) (hE : D.IsExceptional) : 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sY := hY.1.toIsSeparated
  have hsep : IsSeparated (Y ↘ ⊤_ Scheme) := by
    have : (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional at hE
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hE
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set Y), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc] at hE
  change 2 ≤ closedsCodimension (T := Y) ⟨(D.center : Set Y), D.center.isClosed⟩ at hE
  rwa [closedsCodimension_coe] at hE

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- The divisor `(Y, p, Q)` over `X` of a prime divisor `Q` of the source of a junction. -/
private abbrev divisorOver (J : CrepantJunction sX B I) (Q : MMP.Mori.PrimeDivisor J.Y) :
    DivisorOver ℂ sX :=
  ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, Q⟩

/-- **Strict transforms.** Every prime divisor `P` of `X` has a strict transform `Q` on `Y`, with
`ord_Q = ord_P` as valuations of `k(X)`. -/
private theorem exists_valuation_divisorOver_eq (J : CrepantJunction sX B I)
    (hX : IsNormalVariety ℂ sX) (P : MMP.Mori.PrimeDivisor X) :
    ∃ Q : MMP.Mori.PrimeDivisor J.Y,
      (divisorOver J Q).valuation = (DivisorOver.ofPrimeDivisor ℂ hX P).valuation := by
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have := J.isBirationalMorphism.isDominant
  obtain ⟨y, hy, hcoh, -, -⟩ := MMP.Intersection.exists_preimage_of_coheight_eq_one J.p
    (IsBirationalMorphism.functionFieldMap_bijective J.isBirationalMorphism)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_⟩
  refine MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX _ P ?_
  change J.p (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh).genericPoint = _
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hy]

/-- The valuation of a divisor exceptional over the source `Y` of a junction, restricted to
`k(X)`, is not the valuation `ord_Q` of a prime divisor `Q` of `Y`. -/
private theorem comap_valuation_ne (J : CrepantJunction sX B I)
    {D : DivisorOver ℂ (J.p ≫ sX)} (hE : D.IsExceptional) (Q : MMP.Mori.PrimeDivisor J.Y) :
    haveI := J.isBirationalMorphism.isDominant
    D.valuation.comap (functionFieldMap J.p) ≠ (divisorOver J Q).valuation := by
  have := J.isBirationalMorphism.isDominant
  intro hv
  have hY : IsNormalVariety ℂ (J.p ≫ sX) := J.isQFactorial.1
  have hvY : D.valuation = (DivisorOver.ofPrimeDivisor ℂ hY Q).valuation := by
    refine comap_injective_of_surjective J.isBirationalMorphism.functionFieldMap_bijective.2
      (hv.trans ?_)
    ext g
    change Q.divisorialValuation (functionFieldMap J.p g) =
      Q.divisorialValuation (functionFieldMap (𝟙 J.Y) (functionFieldMap J.p g))
    rw [MMP.Mori.functionFieldMap_id_apply]
  exact ((MMP.Positivity.DivisorOver.two_le_codimension_center_iff hY D).mp
    (two_le_codimension_center_of_isExceptional hY D hE)) Q hvY

/-- A divisor exceptional over the source `Y` of a junction has, restricted to `k(X)`, a
valuation exceptional over `X`. -/
private theorem isExceptionalValuation_comap (J : CrepantJunction sX B I)
    (hX : IsNormalVariety ℂ sX) {D : DivisorOver ℂ (J.p ≫ sX)} (hE : D.IsExceptional)
    {D' : DivisorOver ℂ sX} (hD' : IsProper D'.f)
    (hv : haveI := J.isBirationalMorphism.isDominant
      D'.valuation = D.valuation.comap (functionFieldMap J.p)) :
    MMP.Intersection.IsExceptionalValuation ℂ sX D'.valuation := by
  refine ⟨D', hD', rfl, ?_⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX]
  intro P hP
  obtain ⟨Q, hQ⟩ := exists_valuation_divisorOver_eq J hX P
  exact comap_valuation_ne J hE Q (hv.symm.trans (hP.trans hQ.symm))

/-- **Terminality over a junction extracting `I(X, B)`.** If the junction extracts exactly the
low-discrepancy set `I(X, B)`, then a divisor exceptional over its source `Y` has log
discrepancy `> 1` over `(X, B)`: its valuation is exceptional over `X` and differs from every
extracted valuation, whose centres on `Y` are divisors. -/
private theorem one_lt_of_isExceptional (J : CrepantJunction sX B I)
    (hI : (I : Set _) = lowDiscrepancySet sX B) (hX : IsNormalVariety ℂ sX)
    {D : DivisorOver ℂ (J.p ≫ sX)} (hE : D.IsExceptional) {b : ℝ}
    (hb : haveI := J.isBirationalMorphism.isDominant
      IsValuationLogDiscrepancy sX B (D.valuation.comap (functionFieldMap J.p)) b) : 1 < b := by
  have := J.isBirationalMorphism.isDominant
  by_contra! h1
  obtain ⟨-, D', hD'p, hv, -⟩ := id hb
  have hmem : D.valuation.comap (functionFieldMap J.p) ∈ (I : Set _) := by
    rw [hI]
    exact ⟨hv ▸ isExceptionalValuation_comap J hX hE hD'p hv, b, hb, h1⟩
  exact comap_valuation_ne J hE (J.E ⟨_, hmem⟩) (J.valuation_eq ⟨_, hmem⟩).symm

end Junction

/-! ### Birational morphisms and function fields -/

/-- A proper divisor over `Y` is carried along an isomorphism `e : V ≅ Y` to a proper divisor
over `V`, with valuation pulled back along `e`. -/
private theorem exists_divisorOver_of_iso {V Y : Scheme.{0}} [IsIntegral V] [IsIntegral Y]
    {sV : V ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (e : V ≅ Y)
    (hs : e.hom ≫ sY = sV) (D : DivisorOver ℂ sY) [IsProper D.f] :
    ∃ E : DivisorOver ℂ sV, IsProper E.f ∧
      D.valuation = E.valuation.comap (functionFieldMap e.hom) := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hb : IsBirationalMorphism (D.f ≫ e.inv) :=
    MMP.Mori.IsPair.isBirationalMorphism_comp D.isBirationalMorphism
      (isBirationalMorphism_of_isIso _)
  have hnv : IsNormalVariety ℂ ((D.f ≫ e.inv) ≫ sV) := by
    rw [← hs, show (D.f ≫ e.inv) ≫ e.hom ≫ sY = D.f ≫ sY by simp]
    exact D.isNormalVariety
  have : IsDominant (D.f ≫ e.inv) := hb.isDominant
  refine ⟨⟨D.Y, D.f ≫ e.inv, hnv, hb, D.E⟩, inferInstanceAs (IsProper (D.f ≫ e.inv)), ?_⟩
  ext t
  change D.E.divisorialValuation (functionFieldMap D.f t) =
    D.E.divisorialValuation (functionFieldMap (D.f ≫ e.inv) (functionFieldMap e.hom t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr
      (a := (D.f ≫ e.inv) ≫ e.hom) (b := D.f) (by simp)]

/-- The extension of function fields of a composite of dominant morphisms is the composite. -/
private theorem functionFieldMap_comp' {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsDominant a] [IsDominant b]
    [IsDominant (a ≫ b)] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  ext t
  exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b t).symm

/-- Restricting a valuation along a composite of dominant morphisms. -/
private theorem comap_functionFieldMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (a : X ⟶ Y) (b : Y ⟶ Z) [ia : IsDominant a] [ib : IsDominant b]
    [iab : IsDominant (a ≫ b)]
    (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    v.comap (functionFieldMap (a ≫ b)) =
      (v.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  rw [functionFieldMap_comp' a b, Valuation.comap_comp]

/-- Restricting a valuation along a morphism only depends on the morphism. -/
private theorem comap_functionFieldMap_congr {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {a b : X ⟶ Y} (h : a = b) [ia : IsDominant a] [ib : IsDominant b]
    (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    v.comap (functionFieldMap a) = v.comap (functionFieldMap b) := by
  subst h
  rfl

/-- If the extension of function fields of `a ≫ b` is onto, so is that of `b`. -/
private theorem functionFieldMap_surjective_of_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] (a : X ⟶ Y) (b : Y ⟶ Z) [ia : IsDominant a] [ib : IsDominant b]
    [iab : IsDominant (a ≫ b)] (h : Function.Surjective (functionFieldMap (a ≫ b))) :
    Function.Surjective (functionFieldMap b) := by
  intro t
  obtain ⟨z, hz⟩ := h (functionFieldMap a t)
  rw [functionFieldMap_comp' a b, RingHom.comp_apply] at hz
  exact ⟨z, (functionFieldMap a).injective hz⟩

/-- If the extensions of function fields of `a` and `b` are onto, so is that of `a ≫ b`. -/
private theorem functionFieldMap_comp_surjective {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] (a : X ⟶ Y) (b : Y ⟶ Z) [ia : IsDominant a] [ib : IsDominant b]
    [iab : IsDominant (a ≫ b)] (ha : Function.Surjective (functionFieldMap a))
    (hb : Function.Surjective (functionFieldMap b)) :
    Function.Surjective (functionFieldMap (a ≫ b)) := by
  rw [functionFieldMap_comp' a b, RingHom.coe_comp]
  exact ha.comp hb

/-- Surjectivity of the extension of function fields only depends on the morphism. -/
private theorem functionFieldMap_surjective_congr {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {a b : X ⟶ Y} (h : a = b) [IsDominant a] [ib : IsDominant b]
    (ha : Function.Surjective (functionFieldMap a)) :
    Function.Surjective (functionFieldMap b) := by
  subst h
  exact ha

/-- Prime divisors of a normal variety with the same valuation are equal. -/
private theorem eq_of_divisorialValuation_eq {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {P P' : MMP.Mori.PrimeDivisor X} (h : P.divisorialValuation = P'.divisorialValuation) :
    P = P' :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1
      (D := DivisorOver.ofPrimeDivisor ℂ hX P) (D' := DivisorOver.ofPrimeDivisor ℂ hX P')
      (by rw [valuation_ofPrimeDivisor, valuation_ofPrimeDivisor, h]))

/-- **The log discrepancy of a prime divisor.** On a pair `(Y, Θ)`, `a(ord_Γ; Y, Θ) = 1 - Θ_Γ`
for every prime divisor `Γ` of `Y`. -/
private theorem isValuationLogDiscrepancy_divisorialValuation {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    {Θ : QDivisor Y} (hP : MMP.Fourfold.IsPair sY Θ) (Γ : MMP.Mori.PrimeDivisor Y) :
    IsValuationLogDiscrepancy sY Θ Γ.divisorialValuation (1 - (Θ.coeff Γ : ℝ)) := by
  obtain ⟨-, nY, _, hKY, -⟩ := hP.isPair
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hKY
    (DivisorOver.ofPrimeDivisor ℂ hY Γ)
  have hprop : IsProper (DivisorOver.ofPrimeDivisor ℂ hY Γ).f := by
    change IsProper (𝟙 Y)
    infer_instance
  have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hprop
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hY hc] at h
  refine ⟨nY, _, hprop, valuation_ofPrimeDivisor hY Γ, ?_⟩
  convert h using 1
  push_cast
  ring

/-! ### Prime divisors along an isomorphism -/

/-- The image of a prime divisor under an isomorphism. -/
private def mapOfIso {V W : Scheme.{0}} (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor W :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e.hom Q.genericPoint) (by
    rw [coheight_eq_of_isOpenImmersion e.hom]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)

private theorem genericPoint_mapOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) : (mapOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- Transport along an isomorphism preserves the divisorial valuation. -/
private theorem divisorialValuation_mapOfIso {V W : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) :
    Q.divisorialValuation.comap (functionFieldMap e.hom) =
      (mapOfIso e Q).divisorialValuation := by
  ext g
  rw [Valuation.comap_apply]
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap e.hom g ≠ 0 := (map_ne_zero _).mpr hg
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso e.hom Q (mapOfIso e Q)
      (genericPoint_mapOfIso e Q).symm]

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`. -/
private theorem coeff_inverseTransformDivisor_of_eq_some {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {D : MMP.Mori.PrimeDivisor X}
    {F : MMP.Mori.PrimeDivisor Y} (hD : inverseTransformPrimeDivisor g D = some F)
    (B : DivisorWithCoeffs R X) : (inverseTransformDivisor g B).coeff F = B.coeff D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

/-- A prime divisor of `Y` which is the inverse transform of no prime divisor of `X` has
coefficient zero in every inverse transform `g⁻¹_* B`. -/
private theorem coeff_inverseTransformDivisor_eq_zero {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {F : MMP.Mori.PrimeDivisor Y}
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

/-- Under an isomorphism `e : V ≅ W`, the coefficient of `e⁻¹_* B` at `Q` is that of `B` at the
image of `Q`. -/
private theorem coeff_inverseTransformDivisor_iso {V W : Scheme.{0}} (e : V ≅ W) {R : Type*}
    [AddCommMonoid R] (B : DivisorWithCoeffs R W) (Q : MMP.Mori.PrimeDivisor V) :
    (inverseTransformDivisor e.hom B).coeff Q = B.coeff (mapOfIso e Q) := by
  refine coeff_inverseTransformDivisor_of_eq_some ?_ B
  refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
    (genericPoint_mapOfIso e Q).symm ?_
  rw [top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff e.hom).mpr inferInstance))]
  trivial

/-! ### Valuations on the models of a terminal chain -/

section Chain

variable {T : StabilizedTail}

/-- The transport of a valuation of `k(X_0)` to `k(X_i)` is unique. -/
private theorem isTransportedValuationFrom_unique
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))} :
    ∀ {i : ℕ} {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
      T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, ⟨u, hu, huw⟩, ⟨u', hu', huw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique hu hu'
    have := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    have := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    have := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    unfold StabilizedTail.IsTransportedValuation at huw huw'
    exact comap_injective_of_surjective
      ((T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
        |>.functionFieldMap_bijective.2)
      (huw.trans huw'.symm)

variable (C : TerminalChain T) (ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)))

/-- The valuation `u` of `k(Y_i)` is the valuation `ν` of `k(X_0)`, carried to the junction
`Y_i`. -/
private def JMatch (i : ℕ)
    (u : Valuation (C.junction i).Y.functionField (WithZero (Multiplicative ℤ))) :
    Prop :=
  haveI := (C.junction i).isBirationalMorphism.isDominant
  ∃ w, T.IsTransportedValuationFrom i ν w ∧ u.comap (functionFieldMap (C.junction i).p) = w

/-- The valuation `u` of `k(V_k)` is the valuation `ν` of `k(X_0)`, carried to the model `V_k`
of the `i`-th bridge. -/
private def BMatch (i k : ℕ)
    (u : Valuation (modelSeq (C.junction i).Y (C.bridge i).P.Y k).functionField
      (WithZero (Multiplicative ℤ))) : Prop :=
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  ∃ w, T.IsTransportedValuationFrom i ν w ∧
    ∃ _ : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k),
      u.comap (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) =
        w.comap (functionFieldMap (T.f i))

/-- The morphisms `π_k : V_k ⟶ Z_i` of the programme of a bridge induce surjections of function
fields. -/
private theorem functionFieldMap_modelMap_surjective (i : ℕ) [IsIntegral (T.Z i)] :
    ∀ k ≤ (C.bridge i).P.m,
    ∀ [IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)],
      Function.Surjective
        (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) := by
  have := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  have := (C.junction i).isBirationalMorphism.isDominant
  intro k hk
  induction k with
  | zero =>
    intro hd
    exact functionFieldMap_comp_surjective (C.junction i).p (T.f i)
      (C.junction i).isBirationalMorphism.functionFieldMap_bijective.2
      (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective.2
  | succ k ih =>
    intro hd
    have hk' : k < (C.bridge i).P.m := hk
    have hD := (C.bridge i).P.isThreefoldStepDiagram k hk'
    have := hD.isNormalVariety_target.1.toIsIntegral
    have := hD.isBirationalMorphism_minus.isDominant
    have hgp : IsDominant ((C.bridge i).P.gp k) :=
      hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have h1 := (C.bridge i).P.modelMap_eq k hk'
    have h2 := (C.bridge i).P.modelMap_succ_eq hk'
    have hgh' : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := h2 ▸ hd
    haveI := IsDominant.of_comp ((C.bridge i).P.gp k) ((C.bridge i).P.h k)
    haveI hd' : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) :=
      h1 ▸ (inferInstance : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k))
    have hs := functionFieldMap_surjective_congr h1 (ih hk'.le)
    have hh := functionFieldMap_surjective_of_comp _ _ hs
    exact functionFieldMap_surjective_congr (ib := hd) h2.symm (functionFieldMap_comp_surjective _ _
      hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2 hh)

variable {C ν}

private theorem JMatch.unique {i : ℕ} {u u' : Valuation (C.junction i).Y.functionField
    (WithZero (Multiplicative ℤ))} (h : JMatch C ν i u) (h' : JMatch C ν i u') : u = u' := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hu⟩ := h
  obtain ⟨w', hw', hu'⟩ := h'
  obtain rfl := isTransportedValuationFrom_unique hw hw'
  exact comap_injective_of_surjective
    (C.junction i).isBirationalMorphism.functionFieldMap_bijective.2
    (hu.trans hu'.symm)

private theorem BMatch.unique {i k : ℕ} (hk : k ≤ (C.bridge i).P.m)
    {u u' : Valuation (modelSeq (C.junction i).Y (C.bridge i).P.Y k).functionField
      (WithZero (Multiplicative ℤ))} (h : BMatch C ν i k u) (h' : BMatch C ν i k u') : u = u' := by
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  obtain ⟨w, hw, hd, hu⟩ := h
  obtain ⟨w', hw', _, hu'⟩ := h'
  obtain rfl := isTransportedValuationFrom_unique hw hw'
  exact comap_injective_of_surjective (functionFieldMap_modelMap_surjective C i k hk)
    (hu.trans hu'.symm)

end Chain

/-! ### Descending along the models -/

/-- Every valuation `v'` with log discrepancy `a'` on `(Y, Θ_Y)` subject to `M_Y` comes from a
valuation `v` subject to `M_X` with log discrepancy `a ≤ a'` on `(X, Θ_X)`. -/
private def Desc {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (ΘX : QDivisor X)
    (MX : Valuation X.functionField (WithZero (Multiplicative ℤ)) → Prop)
    (sY : Y ⟶ Spec (.of ℂ)) (ΘY : QDivisor Y)
    (MY : Valuation Y.functionField (WithZero (Multiplicative ℤ)) → Prop) : Prop :=
  ∀ v' a', MY v' → IsValuationLogDiscrepancy sY ΘY v' a' →
    ∃ v a, MX v ∧ IsValuationLogDiscrepancy sX ΘX v a ∧ a ≤ a'

private theorem Desc.refl {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {ΘX : QDivisor X}
    {MX : Valuation X.functionField (WithZero (Multiplicative ℤ)) → Prop} :
    Desc sX ΘX MX sX ΘX MX :=
  fun v' a' h h' => ⟨v', a', h, h', le_rfl⟩

private theorem Desc.trans {X Y W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {ΘX : QDivisor X}
    {MX : Valuation X.functionField (WithZero (Multiplicative ℤ)) → Prop}
    {sY : Y ⟶ Spec (.of ℂ)} {ΘY : QDivisor Y}
    {MY : Valuation Y.functionField (WithZero (Multiplicative ℤ)) → Prop}
    {sW : W ⟶ Spec (.of ℂ)} {ΘW : QDivisor W}
    {MW : Valuation W.functionField (WithZero (Multiplicative ℤ)) → Prop}
    (h₁ : Desc sX ΘX MX sY ΘY MY) (h₂ : Desc sY ΘY MY sW ΘW MW) : Desc sX ΘX MX sW ΘW MW := by
  intro v' a' h h'
  obtain ⟨v₁, a₁, hv₁, ha₁, hle₁⟩ := h₂ v' a' h h'
  obtain ⟨v₂, a₂, hv₂, ha₂, hle₂⟩ := h₁ v₁ a₁ hv₁ ha₁
  exact ⟨v₂, a₂, hv₂, ha₂, hle₂.trans hle₁⟩

section Steps

variable {T : StabilizedTail} (C : TerminalChain T)
  (ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)))

/-- The models `(V_k, Θ_k)`, `k ≤ m_i`, of the `i`-th bridge are terminal pairs on projective
`ℚ`-factorial threefolds. -/
private theorem bridgeModel_spec (i k : ℕ) (hk : k ≤ (C.bridge i).P.m) :
    MMP.Mori.IsProjectiveVariety ℂ (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k) ∧
    topologicalKrullDim (modelSeq (C.junction i).Y (C.bridge i).P.Y k) = 3 ∧
    IsQFactorial (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k) ∧
    IsKltTerminalPair (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k)
      ((C.bridge i).P.boundary k) :=
  (IsDecreasedBoundary.isSmallMorphism_relativeThreefoldProgram (C.coe_I i)
    (C.bridge i).isDecreasedBoundary (C.bridge i).P).2.choose_spec.2.2.2 k hk

/-- `π_k ≫ (Z_i → Spec ℂ)` is the structure morphism of `V_k`. -/
private theorem modelMap_comp_sZ (i k : ℕ) (hk : k ≤ (C.bridge i).P.m) :
    modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k ≫ T.sZ i =
      modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k := by
  cases k with
  | zero => exact (C.bridge i).P.comp_eq
  | succ k =>
    change (C.bridge i).P.πY k ≫ T.sZ i = (C.bridge i).P.sY k
    rw [(C.bridge i).P.πY_eq k hk, Category.assoc, (C.bridge i).P.comp_eq_base k hk,
      ((C.bridge i).P.isThreefoldStepDiagram k hk).comp_eq_plus]

/-- **A coefficient decrease.** `a(v; Y_i, Θ_i) ≤ a(v; Y_i, Θ_i')`. -/
private theorem desc_decrease (i : ℕ) :
    Desc ((C.junction i).p ≫ T.sX i) (C.junction i).Θ (JMatch C ν i)
      (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY 0) ((C.bridge i).P.boundary 0)
      (BMatch C ν i 0) := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  rintro v' a' ⟨w, hw, hd, hv'⟩ ha'
  obtain ⟨n, D, hDp, hDv, -⟩ := id ha'
  obtain ⟨n₀, a, ha⟩ := exists_isLogDiscrepancy (C.junction i).isCrepant.1 D hDp
  have hb : IsValuationLogDiscrepancy ((C.junction i).p ≫ T.sX i) (C.junction i).Θ v' a :=
    ⟨n₀, D, hDp, hDv, ha⟩
  refine ⟨v', a, ⟨w, hw, ?_⟩, hb, (IsDecreasedBoundary.sub_eq_sum_and_le (C.coe_I i)
    (C.bridge i).isDecreasedBoundary).2.2 v' a a' hb ha'⟩
  refine comap_injective_of_surjective
    (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective.2 ?_
  exact (comap_functionFieldMap_comp (C.junction i).p (T.f i) (iab := hd) v').symm.trans hv'

/-- **A flip of a bridge.** `a(v; V_k, Θ_k) ≤ a(v; V_{k+1}, Θ_{k+1})`. -/
private theorem desc_flip (i k : ℕ) (hk : k < (C.bridge i).P.m) :
    Desc (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k) ((C.bridge i).P.boundary k)
      (BMatch C ν i k)
      (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY (k + 1))
      ((C.bridge i).P.boundary (k + 1)) (BMatch C ν i (k + 1)) := by
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  have hD := (C.bridge i).P.isThreefoldStepDiagram k hk
  haveI := hD.isNormalVariety_target.1.toIsIntegral
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI hgp : IsDominant ((C.bridge i).P.gp k) :=
    hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hB := (bridgeModel_spec C i k hk.le).2.2.2.1.1
  rintro v' a' ⟨w, hw, hd, hv'⟩ ⟨n, Dp, -, rfl, hap⟩
  rw [RelativeThreefoldProgram.boundary_succ_eq_flipTransform _ hk] at hap
  obtain ⟨Dm, hDm, hv⟩ := exists_properDivisorOver_minus hD Dp
  obtain ⟨n', am, ham⟩ := exists_isLogDiscrepancy hB Dm hDm
  refine ⟨Dm.valuation, am, ⟨w, hw, ?_⟩, ⟨n', Dm, hDm, rfl, ham⟩,
    le_of_isLogDiscrepancy hD hB Dp Dm hDm hv hap ham⟩
  have h1 := (C.bridge i).P.modelMap_eq k hk
  have h2 := (C.bridge i).P.modelMap_succ_eq hk
  haveI hgh' : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := h2 ▸ hd
  haveI := IsDominant.of_comp ((C.bridge i).P.gp k) ((C.bridge i).P.h k)
  haveI hd' : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) :=
    h1 ▸ (inferInstance : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k))
  refine ⟨hd', ?_⟩
  rw [comap_functionFieldMap_congr h1, comap_functionFieldMap_comp, ← hv,
    ← comap_functionFieldMap_comp]
  exact (comap_functionFieldMap_congr (ia := hd) (ib := hgh') h2 _).symm.trans hv'

/-- **The end of a bridge.** The isomorphism `e : V_{m_i} ≅ Y_{i+1}` carries `Θ_{m_i}` to
`Θ_{i+1}`, so it is crepant: `a(v; V_{m_i}, Θ_{m_i}) = a(v; Y_{i+1}, Θ_{i+1})`. -/
private theorem desc_end (i : ℕ) :
    Desc (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY (C.bridge i).P.m)
      ((C.bridge i).P.boundary (C.bridge i).P.m) (BMatch C ν i (C.bridge i).P.m)
      ((C.junction (i + 1)).p ≫ T.sX (i + 1)) (C.junction (i + 1)).Θ (JMatch C ν (i + 1)) := by
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  obtain ⟨-, hdim, hQ, hterm⟩ := bridgeModel_spec C i _ le_rfl
  have hV : IsNormalVariety ℂ
      (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY (C.bridge i).P.m) := hQ.1
  have hY' : IsNormalVariety ℂ ((C.junction (i + 1)).p ≫ T.sX (i + 1)) :=
    (C.junction (i + 1)).isQFactorial.1
  have hs : (C.bridge i).e.hom ≫ (C.junction (i + 1)).p ≫ T.sX (i + 1) =
      modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY (C.bridge i).P.m := by
    rw [← modelMap_comp_sZ C i _ le_rfl, (C.bridge i).modelMap_eq, Category.assoc,
      Category.assoc, (T.isThreefoldStepDiagram i).comp_eq_plus]
  have hPY := (C.junction (i + 1)).isCrepant.1
  obtain ⟨-, n₁, K', hK', -⟩ := hPY.isPair
  obtain ⟨-, n₂, KV, hKV, -⟩ := hterm.1.1.isPair
  obtain rfl : n₂ = n₁ := by
    exact_mod_cast hKV.topologicalKrullDim_eq.symm.trans
      (hdim.trans ((C.junction (i + 1)).dim_eq.symm.trans hK'.topologicalKrullDim_eq))
  have hcb : ∀ (F : MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y
      (C.bridge i).P.m)) (D : DivisorOver ℂ ((C.junction (i + 1)).p ≫ T.sX (i + 1))),
      D.valuation = F.valuationOver (C.bridge i).e.hom →
      IsDiscrepancy ((C.junction (i + 1)).p ≫ T.sX (i + 1)) n₂ K' (C.junction (i + 1)).Θ D
        (-((C.bridge i).P.boundary (C.bridge i).P.m).coeff F) := by
    intro F D hD
    rw [(C.bridge i).boundary_eq, coeff_inverseTransformDivisor_iso]
    refine isDiscrepancy_neg_coeff_of_valuation_eq hPY.isPair hK' hY' _ D ?_
    rw [valuation_ofPrimeDivisor, hD, ← divisorialValuation_mapOfIso]
    rfl
  rintro v' a' ⟨w', ⟨u, hu, htr⟩, hv'⟩ ⟨n, D', hD'p, rfl, hD'a⟩
  obtain rfl : n = n₂ := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD'a).symm.trans
      hK'.topologicalKrullDim_eq
  haveI := hD'p
  obtain ⟨E, hEp, hEv⟩ := exists_divisorOver_of_iso (C.bridge i).e hs D'
  have hcrep := isDiscrepancy_iff_of_crepant hPY.isPair hK' (C.bridge i).e.hom hs hV
    (isBirationalMorphism_of_isIso _) hKV hcb E D' hEv
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY.isPair hK' D'
  obtain ⟨-, rfl⟩ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc _).mp hD'a
  refine ⟨E.valuation, 1 + c, ⟨u, hu, ?_⟩, ⟨_, E, hEp,
    rfl, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ((hcrep c).mpr hc)
      hEp⟩, le_rfl⟩
  have hm := (C.bridge i).modelMap_eq
  haveI hdm : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY
      (C.bridge i).P.m) := hm ▸ (inferInstance : IsDominant
        ((C.bridge i).e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i))
  refine ⟨hdm, ?_⟩
  rw [comap_functionFieldMap_congr hm, comap_functionFieldMap_comp, ← hEv,
    comap_functionFieldMap_comp, hv']
  unfold StabilizedTail.IsTransportedValuation at htr
  exact htr

/-- Along the models of a bridge, log discrepancies do not decrease. -/
private theorem desc_bridge (i : ℕ) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ (C.bridge i).P.m) :
    Desc (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY j) ((C.bridge i).P.boundary j)
      (BMatch C ν i j)
      (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k) ((C.bridge i).P.boundary k)
      (BMatch C ν i k) := by
  induction k, hjk using Nat.le_induction with
  | base => exact Desc.refl
  | succ k hjk ih => exact (ih (Nat.le_of_succ_le hk)).trans (desc_flip C ν i k hk)

/-- Along the junctions, log discrepancies do not decrease. -/
private theorem desc_junction {i j : ℕ} (hij : i ≤ j) :
    Desc ((C.junction i).p ≫ T.sX i) (C.junction i).Θ (JMatch C ν i)
      ((C.junction j).p ≫ T.sX j) (C.junction j).Θ (JMatch C ν j) := by
  induction j, hij using Nat.le_induction with
  | base => exact Desc.refl
  | succ j hij ih =>
    exact ih.trans ((desc_decrease C ν j).trans
      ((desc_bridge C ν j (Nat.zero_le _) le_rfl).trans (desc_end C ν j)))

end Steps

/-! ### The models of a terminal chain -/

section Models

variable {T : StabilizedTail} (C : TerminalChain T)
  (ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ)))

/-- The valuation `v` of the function field of the model indexed by `x` is the valuation `ν` of
`k(X_0)`, carried to that model. -/
private def IsMatch : ∀ x : C.ModelIndex,
    Valuation (C.model x).functionField (WithZero (Multiplicative ℤ)) → Prop
  | ⟨i, none⟩ => JMatch C ν i
  | ⟨i, some k⟩ => BMatch C ν i k

variable {C ν} in
private theorem IsMatch.unique {x : C.ModelIndex}
    {v v' : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))}
    (h : IsMatch C ν x v) (h' : IsMatch C ν x v') : v = v' := by
  obtain ⟨i, _ | k⟩ := x
  · exact JMatch.unique h h'
  · exact BMatch.unique k.2.le h h'

/-- Log discrepancies descend along the models, in their order. -/
private theorem desc_of_le {x y : C.ModelIndex}
    (hxy : toLex (x.1, x.2.elim 0 fun k => k.1 + 1) ≤ toLex (y.1, y.2.elim 0 fun k => k.1 + 1)) :
    Desc (C.modelStructure x) (C.modelBoundary x) (IsMatch C ν x)
      (C.modelStructure y) (C.modelBoundary y) (IsMatch C ν y) := by
  obtain ⟨i, _ | k⟩ := x <;> obtain ⟨j, _ | l⟩ := y <;>
    simp only [Prod.Lex.toLex_le_toLex, Option.elim] at hxy
  · exact desc_junction C ν (by omega)
  · exact (desc_junction C ν (i := i) (j := j) (by omega)).trans
      ((desc_decrease C ν j).trans (desc_bridge C ν j (Nat.zero_le _) l.2.le))
  · have hij : i < j := by omega
    exact (desc_bridge C ν i k.2.le le_rfl).trans ((desc_end C ν i).trans (desc_junction C ν hij))
  · rcases hxy with hij | ⟨rfl, hkl⟩
    · exact (desc_bridge C ν i k.2.le le_rfl).trans ((desc_end C ν i).trans
        ((desc_junction C ν hij).trans ((desc_decrease C ν j).trans
          (desc_bridge C ν j (Nat.zero_le _) l.2.le))))
    · exact desc_bridge C ν i (by omega) l.2.le

/-- **Log discrepancies do not decrease along the models.** -/
private theorem le_of_isMatch {x y : C.ModelIndex}
    (hxy : toLex (x.1, x.2.elim 0 fun k => k.1 + 1) ≤ toLex (y.1, y.2.elim 0 fun k => k.1 + 1))
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation (C.model y).functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (hv : IsMatch C ν x v) (hv' : IsMatch C ν y v')
    (ha : IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a)
    (ha' : IsValuationLogDiscrepancy (C.modelStructure y) (C.modelBoundary y) v' a') :
    a ≤ a' := by
  obtain ⟨v₀, a₀, h₀, ha₀, hle⟩ := desc_of_le C ν hxy v' a' hv' ha'
  obtain rfl := hv.unique h₀
  obtain ⟨_, D, -, hD, ha⟩ := ha
  obtain ⟨_, D', -, hD', ha₀⟩ := ha₀
  exact (MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha₀
    (hD.trans hD'.symm)).trans_le hle

/-- **Junctions are terminal.** -/
private theorem isKltTerminalPair_junction (i : ℕ) :
    IsKltTerminalPair ((C.junction i).p ≫ T.sX i) (C.junction i).Θ := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨hPΘ, -, hcrep⟩ := (C.junction i).isCrepant
  have hklt : IsKltPair ((C.junction i).p ≫ T.sX i) (C.junction i).Θ := ⟨hPΘ, fun n D a ha => by
    obtain ⟨n', D', -, -, hD'⟩ := (hcrep _ _).mp ⟨n, D, ha.2.1, rfl, ha⟩
    exact (T.isKltPair i).2 n' D' a hD'⟩
  exact ⟨hklt, fun n D a hE ha => one_lt_of_isExceptional (C.junction i) (C.coe_I i)
    (T.isKltPair i).1.isPair.1 hE ((hcrep _ _).mp ⟨n, D, ha.2.1, rfl, ha⟩)⟩

/-- Every model is a terminal pair on a projective `ℚ`-factorial threefold. -/
private theorem model_spec (x : C.ModelIndex) :
    MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x) ∧ IsQFactorial (C.modelStructure x) ∧
      topologicalKrullDim (C.model x) = 3 ∧
      IsKltTerminalPair (C.modelStructure x) (C.modelBoundary x) := by
  obtain ⟨i, _ | k⟩ := x
  · exact ⟨(C.junction i).isProjectiveVariety, (C.junction i).isQFactorial,
      (C.junction i).dim_eq, isKltTerminalPair_junction C i⟩
  · obtain ⟨h1, h2, h3, h4⟩ := bridgeModel_spec C i k k.2.le
    exact ⟨h1, h3, h2, h4⟩

/-- `a(ord_P; Y, Θ) = 1 - Θ_P` on every model `(Y, Θ)`. -/
private theorem isValuationLogDiscrepancy_model (x : C.ModelIndex)
    (P : MMP.Mori.PrimeDivisor (C.model x)) :
    IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) P.divisorialValuation
      (1 - ((C.modelBoundary x).coeff P : ℝ)) :=
  isValuationLogDiscrepancy_divisorialValuation (model_spec C x).2.1.1
    (model_spec C x).2.2.2.1.1 P

/-- The boundary of every model has coefficients in `[0, 1)`. -/
private theorem zero_le_coeff_and_coeff_lt_one (x : C.ModelIndex) (P : MMP.Mori.PrimeDivisor (C.model x)) :
    0 ≤ (C.modelBoundary x).coeff P ∧ (C.modelBoundary x).coeff P < 1 := by
  have hklt := (model_spec C x).2.2.2.1
  refine ⟨hklt.1.nonneg P, ?_⟩
  obtain ⟨n, D, -, -, hD⟩ := isValuationLogDiscrepancy_model C x P
  have := hklt.2 n D _ hD
  exact_mod_cast (by linarith : ((C.modelBoundary x).coeff P : ℝ) < 1)

/-- The prime divisors of every model correspond to those of `Y_0`, compatibly with valuations. -/
private theorem exists_equiv_isMatch (x : C.ModelIndex) :
    haveI := (C.junction 0).isBirationalMorphism.isDominant
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x),
      ∀ Q, IsMatch C (Q.valuationOver (C.junction 0).p) x (e Q).divisorialValuation := by
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  obtain ⟨hJ, hB, -⟩ := exists_equiv_primeDivisor C
  obtain ⟨i, _ | k⟩ := x
  · obtain ⟨e, he⟩ := hJ i
    exact ⟨e, he⟩
  · obtain ⟨e, he, -⟩ := hB i
    exact ⟨e k k.2.le, he k k.2.le⟩

/-- **Coefficients do not increase along the models.** If prime divisors `P` of the model `x`
and `P'` of a later model `y` both carry the valuation `ν` of `k(X_0)`, then
`Θ_y(P') ≤ Θ_x(P)`: the coefficients are `1 - a(ν; ·)`, and log discrepancies do not decrease
along the models. -/
private theorem coeff_le_of_isMatch {x y : C.ModelIndex}
    (hxy : toLex (x.1, x.2.elim 0 fun k => k.1 + 1) ≤ toLex (y.1, y.2.elim 0 fun k => k.1 + 1))
    {P : MMP.Mori.PrimeDivisor (C.model x)} {P' : MMP.Mori.PrimeDivisor (C.model y)}
    (hP : IsMatch C ν x P.divisorialValuation) (hP' : IsMatch C ν y P'.divisorialValuation) :
    (C.modelBoundary y).coeff P' ≤ (C.modelBoundary x).coeff P := by
  have := le_of_isMatch C ν hxy hP hP' (isValuationLogDiscrepancy_model C x P)
    (isValuationLogDiscrepancy_model C y P')
  exact_mod_cast (by linarith : ((C.modelBoundary y).coeff P' : ℝ) ≤ (C.modelBoundary x).coeff P)

private theorem isLabelCentre_iff (S : C.Label) (x : C.ModelIndex)
    (P : MMP.Mori.PrimeDivisor (C.model x)) :
    C.IsLabelCentre S x P ↔ IsMatch C (labelValuation S) x P.divisorialValuation := by
  obtain ⟨i, _ | k⟩ := x <;> exact Iff.rfl

/-- A prime divisor of `Y_0` with nonzero coefficient in `Θ_0` is a label. -/
private theorem isLabel_of_coeff_ne_zero (Q : MMP.Mori.PrimeDivisor (C.junction 0).Y)
    (hQ : (C.junction 0).Θ.coeff Q ≠ 0) : C.IsLabel Q := by
  classical
  obtain ⟨a, -, hΘ⟩ := (C.junction 0).Θ_eq
  by_cases hE : Q ∈ Set.range (C.junction 0).E
  · exact Or.inr hE
  left
  have h1 : (C.junction 0).Θ.coeff Q =
      (inverseTransformDivisor (C.junction 0).p (T.B 0)).coeff Q := by
    rw [hΘ, DivisorWithCoeffs.coeff, Finsupp.add_apply, Finsupp.finset_sum_apply,
      Finset.sum_eq_zero fun s _ => by rw [Finsupp.single_apply, if_neg fun h => hE ⟨s, h⟩],
      add_zero]
    rfl
  rw [h1] at hQ
  by_cases hΓ : ∃ Γ, inverseTransformPrimeDivisor (C.junction 0).p Γ = some Q
  · obtain ⟨Γ, hΓ⟩ := hΓ
    rw [coeff_inverseTransformDivisor_of_eq_some hΓ] at hQ
    exact ⟨Γ, hQ, hΓ⟩
  · exact absurd (coeff_inverseTransformDivisor_eq_zero (not_exists.mp hΓ) _) hQ

end Models

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **The models of a terminal chain.** Let `C` be a terminal chain over a stabilized tail `T`.
1. Every model `(Y, Θ)` of `C` is a projective `ℚ`-factorial (in particular normal) threefold and
  `(Y, Θ)` is a terminal pair (in particular `Θ ≥ 0`); every label `S_h` has a unique centre
  `S_h^Y` on `Y` which is a prime divisor, distinct labels have distinct centres, every prime
  divisor in the support of `Θ` is the centre of a label, and every label coefficient `b_h^Y`
  lies in `[0, 1)`.
2. Along the models, in their order, every label coefficient is nonincreasing.
3. Along the models, in their order, the log discrepancy of every normalized divisorial valuation
  is nondecreasing. -/
@[mmp "prop_mmp_indexc_chain_models"]
public theorem isKltTerminalPair_and_antitone_and_monotone {T : StabilizedTail}
    (C : TerminalChain T) :
    (∀ x : C.ModelIndex,
      MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x) ∧ IsQFactorial (C.modelStructure x) ∧
        topologicalKrullDim (C.model x) = 3 ∧
        IsKltTerminalPair (C.modelStructure x) (C.modelBoundary x) ∧
        (∀ S : C.Label, ∃! P : MMP.Mori.PrimeDivisor (C.model x), C.IsLabelCentre S x P) ∧
        (∀ (S S' : C.Label) (P : MMP.Mori.PrimeDivisor (C.model x)),
          C.IsLabelCentre S x P → C.IsLabelCentre S' x P → S = S') ∧
        (∀ P : MMP.Mori.PrimeDivisor (C.model x),
          (C.modelBoundary x).coeff P ≠ 0 → ∃ S : C.Label, C.IsLabelCentre S x P) ∧
        (∀ (S : C.Label) (b : ℚ), C.IsLabelCoefficient S x b → 0 ≤ b ∧ b < 1)) ∧
    (∀ (S : C.Label) (x y : C.ModelIndex) (b b' : ℚ),
      toLex (x.1, x.2.elim 0 fun k => k.1 + 1) ≤ toLex (y.1, y.2.elim 0 fun k => k.1 + 1) →
      C.IsLabelCoefficient S x b → C.IsLabelCoefficient S y b' → b' ≤ b) ∧
    (∀ (ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))) (x y : C.ModelIndex),
      toLex (x.1, x.2.elim 0 fun k => k.1 + 1) ≤ toLex (y.1, y.2.elim 0 fun k => k.1 + 1) →
      ∀ (v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ)))
        (v' : Valuation (C.model y).functionField (WithZero (Multiplicative ℤ))) (a a' : ℝ),
      (match x, v with
        | ⟨i, none⟩, u =>
          haveI := (C.junction i).isBirationalMorphism.isDominant
          ∃ w, T.IsTransportedValuationFrom i ν w ∧
            u.comap (functionFieldMap (C.junction i).p) = w
        | ⟨i, some k⟩, u =>
          haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
          haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
          ∃ w, T.IsTransportedValuationFrom i ν w ∧
            ∃ _ : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k),
              u.comap (functionFieldMap
                  (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) =
                w.comap (functionFieldMap (T.f i))) →
      (match y, v' with
        | ⟨i, none⟩, u =>
          haveI := (C.junction i).isBirationalMorphism.isDominant
          ∃ w, T.IsTransportedValuationFrom i ν w ∧
            u.comap (functionFieldMap (C.junction i).p) = w
        | ⟨i, some k⟩, u =>
          haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
          haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
          ∃ w, T.IsTransportedValuationFrom i ν w ∧
            ∃ _ : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k),
              u.comap (functionFieldMap
                  (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) =
                w.comap (functionFieldMap (T.f i))) →
      IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a →
      IsValuationLogDiscrepancy (C.modelStructure y) (C.modelBoundary y) v' a' → a ≤ a') := by
  refine ⟨fun x => ?_, fun S x y b b' hxy hx hy => ?_,
    fun ν x y hxy v v' a a' hv hv' ha ha' => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := model_spec C x
    obtain ⟨e, he⟩ := exists_equiv_isMatch C x
    have hcentre : ∀ S : C.Label, C.IsLabelCentre S x (e S.1) :=
      fun S => (isLabelCentre_iff C S x _).mpr (he S.1)
    have huniq : ∀ (S : C.Label) (P : MMP.Mori.PrimeDivisor (C.model x)),
        C.IsLabelCentre S x P → P = e S.1 := fun S P hP =>
      eq_of_divisorialValuation_eq h2.1 (((isLabelCentre_iff C S x P).mp hP).unique (he S.1))
    refine ⟨h1, h2, h3, h4, fun S => ⟨e S.1, hcentre S, fun P hP => huniq S P hP⟩,
      fun S S' P hS hS' => Subtype.ext (e.injective ((huniq S P hS).symm.trans (huniq S' P hS'))),
      fun P hP => ?_, fun S b ⟨P, _, hb⟩ => hb ▸ zero_le_coeff_and_coeff_lt_one C x P⟩
    have hPm := he (e.symm P)
    rw [e.apply_symm_apply] at hPm
    have hle := coeff_le_of_isMatch C _ (x := ⟨0, none⟩)
      (Prod.Lex.toLex_le_toLex.mpr (by dsimp only [Option.elim]; omega)) ⟨_, rfl, rfl⟩ hPm
    exact ⟨⟨e.symm P, isLabel_of_coeff_ne_zero C _
      (((zero_le_coeff_and_coeff_lt_one C x P).1.lt_of_ne' hP).trans_le hle).ne'⟩,
      (isLabelCentre_iff C _ x P).mpr hPm⟩
  · obtain ⟨P, hP, rfl⟩ := hx
    obtain ⟨P', hP', rfl⟩ := hy
    exact coeff_le_of_isMatch C _ hxy ((isLabelCentre_iff C S x P).mp hP)
      ((isLabelCentre_iff C S y P').mp hP')
  · exact le_of_isMatch C ν hxy (by rcases x with ⟨i, _ | k⟩ <;> exact hv)
      (by rcases y with ⟨j, _ | l⟩ <;> exact hv') ha ha'

/-- Label coefficients are nonnegative. -/
private theorem isLabelCoefficient_nonneg {T : StabilizedTail} {C : TerminalChain T} {S : C.Label}
    {x : C.ModelIndex} {b : ℚ} (hb : C.IsLabelCoefficient S x b) : 0 ≤ b :=
  ((C.isKltTerminalPair_and_antitone_and_monotone.1 x).2.2.2.2.2.2.2 S b hb).1

/-- A label whose coefficient vanishes at some junction is fixed, with coefficient `0`. -/
private theorem isFixedLabel_of_isJunctionLabelCoefficient_zero {T : StabilizedTail}
    {C : TerminalChain T} {S : C.Label} {i : ℕ} (h0 : C.IsJunctionLabelCoefficient S i 0) :
    C.IsFixedLabel S := by
  refine ⟨0, i, fun j hj => ?_⟩
  obtain ⟨h1, h2, -⟩ := C.isKltTerminalPair_and_antitone_and_monotone
  obtain ⟨P, hP, -⟩ := (h1 ⟨j, none⟩).2.2.2.2.1 S
  have hP' : C.IsLabelCoefficient S ⟨j, none⟩ _ := ⟨P, hP, rfl⟩
  exact ⟨P, hP, le_antisymm
    (h2 S ⟨i, none⟩ ⟨j, none⟩ 0 _ (Prod.Lex.toLex_mono ⟨hj, le_rfl⟩) h0 hP')
    (isLabelCoefficient_nonneg hP')⟩

/-- **Varying coefficients stay positive.** If `S` is a varying label of a terminal chain `C`,
then its coefficient `b_h^{(i)}` at the `i`-th junction is positive for every `i`. -/
@[mmp "lem_mmp_indexc_varying_positive"]
public theorem IsVaryingLabel.pos_of_isJunctionLabelCoefficient {T : StabilizedTail}
    {C : TerminalChain T} {S : C.Label} (hS : C.IsVaryingLabel S) {i : ℕ} {b : ℚ}
    (hb : C.IsJunctionLabelCoefficient S i b) : 0 < b :=
  (isLabelCoefficient_nonneg hb).lt_of_ne fun h =>
    hS (isFixedLabel_of_isJunctionLabelCoefficient_zero (h ▸ hb))

end TerminalChain

end StabilizedTail

end MMP.Fourfold
