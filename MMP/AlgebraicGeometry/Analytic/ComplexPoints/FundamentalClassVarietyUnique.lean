module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVariety
public import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Uniqueness
public import MMP.AlgebraicTopology.PoincareDuality.Alexander
public import MMP.AlgebraicTopology.FundamentalClass.Exists
/-!
# Uniqueness of the fundamental class of a complex variety (Fulton, Lemma 19.1.1)

Let `V` be a complex variety of dimension `n` (a variety over `ℂ` which is a complex scheme,
Fulton's standing convention in §19.1). The singular locus `V_sing` is Zariski closed of
dimension `< n`, so the restriction `H_{2n} V → H_{2n} V_reg` is an isomorphism
(`isIso_restrict_regularOpens`); `V_reg(ℂ)` is a connected complex manifold
(`connectedSpace_regularOpens`), so a fundamental class of `V_reg` freely generates
`H_{2n} V_reg` and is unique (`IsFundamentalClass.eq_of_connectedSpace'`). Hence:

* a fundamental class `c` of `V` freely generates `H_{2n} V`
  (`IsVarietyFundamentalClass.bijective_smul`);
* two fundamental classes of `V` agree (`IsVarietyFundamentalClass.eq`);
* `V` has a fundamental class as soon as `V_reg(ℂ)` has one
  (`exists_isVarietyFundamentalClass_of_exists`); it has one, since the complex manifold
  `V_reg(ℂ)` has an oriented atlas and hence a fundamental class
  (`existsUnique_isVarietyFundamentalClass`, Fulton, Lemma 19.1.1);
* for every fundamental class `c` of `V` and every open `W ⊆ V(ℂ)`, the restriction of `c` to the
  open subset `W ∩ V_reg` of `V_reg` is a fundamental class of `W ∩ V_reg`
  (`IsVarietyFundamentalClass.isFundamentalClass_restrict`, Fulton §19.1).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP.UnderlyingSpace MMP.FundamentalClass

namespace MMP

section Zero

open Set SingularCochain ThomClass

universe u

variable {R : Type u} [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ChartedSpace H Y]

/-- **Uniqueness of the fundamental class in dimension `0`**: a connected Hausdorff second
countable `0`-manifold is a point, and the cocycle `1` of `(Y, Y - y)` detects the coefficient. -/
theorem IsFundamentalClass.eq_of_connectedSpace_zero [SecondCountableTopology Y]
    [ConnectedSpace Y] {b : Module.Basis (Fin 0) ℝ H}
    {μ μ' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) (0 : ℕ)}
    (hμ : IsFundamentalClass R b μ) (hμ' : IsFundamentalClass R b μ') : μ' = μ := by
  obtain ⟨r, hr⟩ := (PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold
    (R := R) (Y := Y) b μ hμ).2 μ'
  simp only at hr
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  set e := chartAt H y
  have hy : y ∈ e.source := mem_chart_source H y
  haveI : Subsingleton H := b.repr.toEquiv.subsingleton
  have hsrc : e.source = {y} := by
    refine Set.Subset.antisymm (fun z hz ↦ ?_) (Set.singleton_subset_iff.2 hy)
    exact e.injOn hz hy (Subsingleton.elim _ _)
  have hcl : IsClopen ({y} : Set Y) := ⟨isClosed_singleton, hsrc ▸ e.open_source⟩
  have huniv : ({y} : Set Y) = univ := hcl.eq_univ ⟨y, rfl⟩
  have hall : ∀ z : Y, z = y := fun z ↦ by
    have : z ∈ ({y} : Set Y) := huniv ▸ mem_univ z
    exact this
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e y)
    (e.open_target.mem_nhds (e.map_source hy))
  have h1 := IsLocallyClassOf.of_restrict (chartOpens e)
    (hμ e (chart_mem_atlas H y) ⟨y, hy⟩ v hv hvt)
  have h2 := IsLocallyClassOf.of_restrict (chartOpens e)
    (hμ' e (chart_mem_atlas H y) ⟨y, hy⟩ v hv hvt)
  rw [← hr] at h2
  have hφ : (fun _ ↦ (1 : R) : SingularChain.Simplex (TopCat.of Y) 0 → R) ∈
      relCocycles R ({y}ᶜ : Set (TopCat.of Y)) 0 := by
    rw [mem_relCocycles_iff]
    refine ⟨fun σ hσ ↦ ?_, ?_⟩
    · obtain ⟨p⟩ : Nonempty (stdSimplex ℝ (Fin 1)) := inferInstance
      exact absurd (hall (σ p)) (hσ ⟨p, rfl⟩)
    · ext σ
      simp [coboundary, Fin.sum_univ_two]
  rw [← hr, h1.eq_one_of_smul h2 hφ rfl, one_smul]

/-- **Uniqueness of the fundamental class of a connected manifold**, in every dimension. -/
theorem IsFundamentalClass.eq_of_connectedSpace' [SecondCountableTopology Y]
    [ConnectedSpace Y] {n : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {μ μ' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) n}
    (hμ : IsFundamentalClass R b μ) (hμ' : IsFundamentalClass R b μ') : μ' = μ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hμ.eq_of_connectedSpace_zero hμ'
  · exact hμ.eq_of_connectedSpace_of_pos hn hμ'

end Zero

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]

variable (V) in
/-- The singular locus of a complex variety, as a Zariski closed subset. -/
def singularLocusCloseds : Closeds V :=
  ⟨singularLocus V, isClosed_singularLocus_of_isAlgebraicScheme ℂ V⟩

/-- The reduced singular locus of `V` lies over `ℂ` through its inclusion. -/
@[reducible] noncomputable def singularLocusOver :
    (Scheme.IdealSheafData.vanishingIdeal (singularLocusCloseds V)).subscheme.Over (Spec (.of ℂ)) :=
  ⟨(Scheme.IdealSheafData.vanishingIdeal (singularLocusCloseds V)).subschemeι ≫ V ↘ Spec (.of ℂ)⟩

attribute [local instance] singularLocusOver

/-- The inclusion of the reduced singular locus of `V` is a morphism over `ℂ`. -/
instance isOver_singularLocus_subschemeι :
    (Scheme.IdealSheafData.vanishingIdeal (singularLocusCloseds V)).subschemeι.IsOver
      (Spec (.of ℂ)) :=
  ⟨rfl⟩

/-- The complement in `V(ℂ)` of the (reduced) singular locus is the regular part `V_reg(ℂ)`. -/
lemma complOpens_singularLocus_eq_regularOpens :
    borelMooreHomology.complOpens (Y := TopCat.of (UnderlyingSpace ℂ V))
      (isClosed_range_map_of_isClosedImmersion
        (Scheme.IdealSheafData.vanishingIdeal (singularLocusCloseds V)).subschemeι) =
      regularOpens ℂ V := by
  ext p
  change p ∉ Set.range (mapFun (K := ℂ) _) ↔ p ∈ regularPart ℂ V
  rw [range_mapFun_of_isClosedImmersion, mem_regularPart_iff]
  change ¬ (_ ∈ Set.range (Scheme.IdealSheafData.subschemeι _).base) ↔ _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change ¬ ¬ _ ↔ _
  exact not_not

variable (R : Type) [CommRing R]

/-- **Restriction to the regular part is an isomorphism in top degree** (Fulton, Lemma 19.1.1):
for a complex variety `V` of dimension `n`, `H_{2n} V → H_{2n} V_reg` is an isomorphism. -/
theorem isIso_restrict_regularOpens {n : ℕ} (hn : (n : WithBot ℕ∞) = topologicalKrullDim V) :
    IsIso (borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ V))
      (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) (2 * n : ℕ)) := by
  have h := IsComplexScheme.isIso_restrict_compl_of_setDimension_lt R V (singularLocusCloseds V)
    (n := n) (hn ▸ setDimension_singularLocus_lt_dimension ℂ V)
  rw [complOpens_singularLocus_eq_regularOpens] at h
  have e : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  rw [e]
  exact h

/-- For a complex variety `V` of dimension `n`, the restriction `H_{2n} V → H_{2n} V_reg` is
bijective. -/
lemma bijective_restrict_regularOpens {n : ℕ} (hn : (n : WithBot ℕ∞) = topologicalKrullDim V) :
    Function.Bijective (borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ V))
      (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) (2 * n : ℕ)) :=
  haveI := isIso_restrict_regularOpens R hn
  (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- The regular part of a complex variety is connected. -/
lemma connectedSpace_regularOpens : ConnectedSpace (regularOpens ℂ V) := by
  obtain ⟨p⟩ : Nonempty V := inferInstance
  have h := isConnected_regularPart_diff (X := V) isClosed_empty
    (fun h ↦ (Set.eq_empty_iff_forall_notMem.1 h.symm) p trivial)
  simp only [Set.mem_empty_iff_false, Set.setOf_false, Set.diff_empty] at h
  exact isConnected_iff_connectedSpace.1 h

variable {R}

/-- **A fundamental class of a complex variety freely generates its top homology** (Fulton,
Lemma 19.1.1): if `c` is a fundamental class of `V`, `r ↦ r • c`, `R → H_{2n} V`, is bijective. -/
theorem IsVarietyFundamentalClass.bijective_smul {n : ℕ} {hn : (n : WithBot ℕ∞) = topologicalKrullDim V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)}
    (hc : IsVarietyFundamentalClass R hn c) : Function.Bijective fun r : R ↦ r • c := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  haveI := connectedSpace_regularOpens (V := V)
  have hf := bijective_restrict_regularOpens R hn
  have hμ := (borelMooreHomology.topHomologyFreeOnFundamentalClass_and_bijective_dualityMap
    (R := R) (M := regularOpens ℂ V) (euclideanComplexOrientationBasis n)).1 _ hc
  refine (Function.Bijective.of_comp_iff' hf _).1 ?_
  convert hμ using 1
  funext r
  simp [map_smul]

/-- **Uniqueness of the fundamental class of a complex variety** (Fulton,
Lemma 19.1.1). -/
theorem IsVarietyFundamentalClass.eq {n : ℕ}
    {hn : (n : WithBot ℕ∞) = topologicalKrullDim V}
    {c c' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)}
    (hc : IsVarietyFundamentalClass R hn c) (hc' : IsVarietyFundamentalClass R hn c') :
    c = c' := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  haveI := connectedSpace_regularOpens (V := V)
  exact (bijective_restrict_regularOpens R hn).1
    (IsFundamentalClass.eq_of_connectedSpace' hc' hc)

/-- A complex variety has a fundamental class as soon as its regular part has one. -/
theorem exists_isVarietyFundamentalClass_of_exists {n : ℕ} (hn : (n : WithBot ℕ∞) = topologicalKrullDim V)
    (h : letI := regularChartedSpace (𝕜 := ℂ) hn
      ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (regularOpens ℂ V)) (2 * n : ℕ),
        IsFundamentalClass R (euclideanComplexOrientationBasis n) μ) :
    ∃ c, IsVarietyFundamentalClass R hn c := by
  obtain ⟨μ, hμ⟩ := h
  obtain ⟨c, rfl⟩ := (bijective_restrict_regularOpens R hn).2 μ
  exact ⟨c, hμ⟩

/-- **The fundamental class of a variety restricts to fundamental classes** (Fulton, §19.1: "it
restricts to the fundamental class `μ_{U_i}` for any connected open subset `U_i` of the
non-singular locus"). Let `c = cl(V)` be a fundamental class of the complex variety `V` and
`W ⊆ V(ℂ)` open. Then `c|_W = μ_W`, the restriction being taken to the open subset `W ∩ V_reg` of
the complex manifold `V_reg(ℂ)` (which is `W` when `W ⊆ V_reg`), through `V_reg`. -/
theorem IsVarietyFundamentalClass.isFundamentalClass_restrict {n : ℕ}
    {hn : (n : WithBot ℕ∞) = topologicalKrullDim V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)}
    (hc : IsVarietyFundamentalClass R hn c) (W : Opens (UnderlyingSpace ℂ V)) :
    letI := regularChartedSpace (𝕜 := ℂ) hn
    IsFundamentalClass R (euclideanComplexOrientationBasis n)
      (borelMooreHomology.restrict R (ModuleCat.of R R)
        (Y := TopCat.of (regularOpens ℂ V)) (regularOpensInter W) (2 * n : ℕ)
        (borelMooreHomology.restrict R (ModuleCat.of R R)
          (Y := TopCat.of (UnderlyingSpace ℂ V))
          (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) (2 * n : ℕ) c)) :=
  letI := regularChartedSpace (𝕜 := ℂ) hn
  IsFundamentalClass.restrict (M := regularOpens ℂ V) (b := euclideanComplexOrientationBasis n)
    (μ := borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
      (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) (2 * n : ℕ) c) hc
    (regularOpensInter W)

end MMP

namespace MMP

section variety

open AlgebraicGeometry UnderlyingSpace Manifold

variable (R : Type) [CommRing R] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V]
  [IsIntegral V]

/-- The fundamental class of the regular part of a complex variety exists. -/
theorem exists_isFundamentalClass_regularOpens {n : ℕ} (hn : (n : WithBot ℕ∞) = topologicalKrullDim V) :
    letI := regularChartedSpace (𝕜 := ℂ) hn
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (regularOpens ℂ V)) (2 * n : ℕ),
      IsFundamentalClass R (euclideanComplexOrientationBasis n) μ := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  haveI := isManifold_regularOpens (𝕜 := ℂ) (X := V) hn
  haveI : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 1 (regularOpens ℂ V) :=
    IsManifold.of_le le_top
  exact exists_isFundamentalClass (isOrientedAtlas_of_isManifold_complex _)
    (euclideanComplexOrientationBasis n)

/-- **The fundamental class of a complex variety** (Fulton, Lemma 19.1.1): a complex variety `V`
of dimension `n` has exactly one fundamental class `cl(V)`, and `H_{2n} V` is free of rank one
with generator `cl(V)`. -/
theorem existsUnique_isVarietyFundamentalClass {n : ℕ} (hn : (n : WithBot ℕ∞) = topologicalKrullDim V) :
    ∃ c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ),
      IsVarietyFundamentalClass R hn c ∧ (∀ c', IsVarietyFundamentalClass R hn c' → c' = c) ∧
        Function.Bijective fun r : R ↦ r • c := by
  obtain ⟨c, hc⟩ := exists_isVarietyFundamentalClass_of_exists hn
    (exists_isFundamentalClass_regularOpens R hn)
  exact ⟨c, hc, fun c' hc' ↦ hc'.eq hc, hc.bijective_smul⟩

end variety

end MMP
