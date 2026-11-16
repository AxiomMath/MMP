module
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Analytic.PluriformDensity
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.StalkValuationRing

/-!
# The invariant integrable gauge on subklt pluriforms

Let `X` be a smooth projective complex variety of dimension `n`, `B` an snc `ℚ`-divisor all of
whose coefficients are less than one, and `m > 0` with `mB` integral. A section
`s ∈ V = H⁰(X, m(K_X + B))` is an `m`-fold top form, locally `s = φ (dz₁ ∧ ⋯ ∧ dzₙ)^{⊗m}`, and
`|s|^{2/m} = |φ|^{2/m} |dz₁ ∧ d z̄₁ ∧ ⋯|` is an intrinsic density on `X(ℂ)`. Its integral
`p(s) = ∫_X |s|^{2/m}` is finite because every coefficient of `B` is less than one, and it is a
continuous function on `V`, positive off zero, with `p(cs) = |c|^{2/m} p(s)`. A birational
self-map whose pluriform pull-back preserves `V` preserves `p`.

## Main results

* `MMP.Fourfold.exists_gauge_logPluricanonicalSections`.
* `MMP.Fourfold.finite_logPluricanonicalSections`: `V` is finite-dimensional.
* `MMP.Fourfold.finiteDimensional_sections`: `H⁰(Y, 𝒪_Y(E))` is finite-dimensional for a Cartier
  divisor `E` on `Y` proper over a field.

## Implementation notes

* The density `|s|^{2/m}` is given on each étale chart `W` of `X^an` by
  `MMP.Analytic.ComplexPoints.pluriformChartMeasure`, the measure `|φ|^{2/m} dλ` with `λ`
  Lebesgue measure on `ℂⁿ` transported by the coordinates; these chart measures glue to a unique
  measure `μ_s` on `X^an` (`MMP.Analytic.ComplexPoints.pluriformChartMeasure_intrinsic`), and
  `p(s)` is its total mass `μ_s(X^an)`. The gauge is characterised by
  `ENNReal.ofReal (p s) = μ Set.univ` for every measure `μ` on `X^an` (with its Borel structure)
  whose restriction to every chart is the chart measure of `s`.
* `V` carries its module topology, the unique Hausdorff vector space topology of a
  finite-dimensional complex space.
* A birational self-map is recorded by its pull-back, a `ℂ`-automorphism of `ℂ(X)`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MMP.Analytic MMP.Analytic.ComplexPoints MeasureTheory Topology
  Filter TopologicalSpace Opposite Order MMP.Mori
open scoped ENNReal TensorProduct

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-! ### The setting: a smooth projective variety and its Borel structure -/

section Setting

variable {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {m : ℕ}

/-- The Borel structure of the analytic topology on `X^an`. -/
private noncomputable abbrev complexBorel : MeasurableSpace (ComplexPoints sX) := borel _

attribute [local instance] complexBorel

private lemma borelSpace_complexPoints : BorelSpace (ComplexPoints sX) := ⟨rfl⟩

attribute [local instance] borelSpace_complexPoints

/-- `μ` is the measure `μ_s`: its restriction to every étale chart is the chart measure of `s`. -/
private abbrev IsGlued [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    (hm : 0 < m)
    (s : RationalPluriForms sX n m) (μ : Measure (ComplexPoints sX)) : Prop :=
  ∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ ComplexPoints.chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩)),
    μ.restrict W = ComplexPoints.pluriformChartMeasure sX hm s U z hz W hW hWo hWz

/-- The measure `μ_s` on `X^an` glued from the chart measures of `s`. -/
private noncomputable def gluedMeasure [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) (s : RationalPluriForms sX n m) :
    Measure (ComplexPoints sX) :=
  (ComplexPoints.pluriformChartMeasure_intrinsic sX hm s).2.1.exists.choose

private lemma isGlued_gluedMeasure [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) (s : RationalPluriForms sX n m) :
    IsGlued hm s (gluedMeasure hm s) :=
  fun U _ z hz W hW hWo hWz ↦
    (ComplexPoints.pluriformChartMeasure_intrinsic sX hm s).2.1.exists.choose_spec U z hz W hW
      hWo hWz

/-- `μ_{cs} = |c|^{2/m} μ_s`. -/
private lemma gluedMeasure_smul [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) (c : ℂ) (s : RationalPluriForms sX n m) :
    gluedMeasure hm (c • s) = ENNReal.ofReal (‖c‖ ^ (2 / m : ℝ)) • gluedMeasure hm s :=
  (ComplexPoints.pluriformChartMeasure_intrinsic sX hm s).2.2.1 c _ _
    (isGlued_gluedMeasure hm s) (isGlued_gluedMeasure hm (c • s))

/-- `μ_s` charges every nonempty open set when `s ≠ 0`. -/
private lemma gluedMeasure_pos [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) (s : RationalPluriForms sX n m) (hs : s ≠ 0)
    {W : Set (ComplexPoints sX)} (hWo : IsOpen W) (hW : W.Nonempty) :
    0 < gluedMeasure hm s W :=
  ((ComplexPoints.measure_proper_closed_null_and_pos_of_isGlued sX hm s).2 _
    (isGlued_gluedMeasure hm s)).2 hs W hWo hW

/-- The complex realization of a projective variety is compact. -/
private lemma compactSpace_complexPoints [AlgebraicGeometry.IsVariety ℂ sX]
    (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX) : CompactSpace (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  have : IsProper sX := inferInstance
  have : sX.IsOver (Spec (.of ℂ)) := ⟨Category.comp_id sX⟩
  have : LocallyOfFiniteType (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (𝟙 _) from inferInstance
  have hp := MMP.UnderlyingSpace.isProperMap_map (K := ℂ) sX
  have : Subsingleton (MMP.UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    ⟨fun p q ↦ MMP.UnderlyingSpace.ext
      (((Category.comp_id _).symm.trans p.toHom_comp_over).trans
        ((Category.comp_id _).symm.trans q.toHom_comp_over).symm)⟩
  have hc : CompactSpace (MMP.UnderlyingSpace ℂ X) :=
    ⟨by simpa using hp.isCompact_preimage (Set.subsingleton_univ.isCompact)⟩
  exact (ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm.compactSpace

/-- A complex variety has a complex point (a closed point, by the Nullstellensatz). -/
private lemma nonempty_complexPoints [AlgebraicGeometry.IsVariety ℂ sX] :
    Nonempty (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have : CompactSpace X :=
    ⟨QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X) isClosed_univ Set.univ_nonempty
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := show LocallyOfFiniteType sX from inferInstance
  obtain ⟨p⟩ : Nonempty (MMP.UnderlyingSpace ℂ X) :=
    ⟨(MMP.UnderlyingSpace.equivClosedPoints X).symm ⟨x, hx⟩⟩
  exact ⟨(ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm p⟩

/-- `μ_s(X^an)` is finite for `s` with poles bounded by `mB`, `B` snc with coefficients `< 1`:
finitely many étale charts cover the compact space `X^an`, and each chart measure is finite. -/
private lemma gluedMeasure_univ_lt_top [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [IsLocallyNoetherian X]
    (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX) (B : DivisorWithCoeffs ℚ X)
    (hB : B.IsSNC sX) (hb : ∀ E, B.coeff E < 1) (hm : 0 < m) (s : RationalPluriForms sX n m)
    (hs : ∀ E : MMP.Mori.PrimeDivisor X, 0 ≤ (E.ordForm s : ℚ) + m * B.coeff E) :
    gluedMeasure hm s Set.univ < ⊤ := by
  haveI := compactSpace_complexPoints hX
  have hfin :=
    (ComplexPoints.isFiniteMeasure_pluriformChartMeasure_of_isSNC sX hX B hB hb hm s hs).1
  have hchart : ∀ x : ComplexPoints sX, ∃ W : Set (ComplexPoints sX),
      IsOpen W ∧ x ∈ W ∧ gluedMeasure hm s W < ⊤ := by
    intro x
    obtain ⟨U, z, hz, hx⟩ := (ComplexPoints.etaleCoordinate_atlas sX (n := n)).1 x
    obtain ⟨W, hW, hWo, hxW, hWz⟩ :=
      (ComplexPoints.etaleCoordinate_atlas sX (n := n)).2.1 U z hz x hx
    haveI : Nonempty U := by
      have h : x.hom ⁻¹ᵁ U = ⊤ := hx
      have hmem : (IsLocalRing.closedPoint ℂ : Spec (.of ℂ)) ∈ x.hom ⁻¹ᵁ U := by
        rw [h]
        trivial
      exact ⟨⟨_, hmem⟩⟩
    refine ⟨W, hWo, hxW, ?_⟩
    haveI := hfin U z hz W hW hWo hWz
    rw [← Measure.restrict_apply_self, isGlued_gluedMeasure hm s U z hz W hW hWo hWz]
    exact measure_lt_top _ _
  choose W hWo hxW hW using hchart
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxW x⟩)
  calc gluedMeasure hm s Set.univ ≤ gluedMeasure hm s (⋃ x ∈ t, W x) := measure_mono ht
    _ ≤ ∑ x ∈ t, gluedMeasure hm s (W x) := measure_biUnion_finset_le _ _
    _ < ⊤ := ENNReal.sum_lt_top.2 fun x _ ↦ hW x

/-- `μ_0 = 0`. -/
private lemma gluedMeasure_zero [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) :
    gluedMeasure hm (0 : RationalPluriForms sX n m) = 0 := by
  have h := gluedMeasure_smul hm 0 (0 : RationalPluriForms sX n m)
  rw [zero_smul] at h
  rw [h, norm_zero, Real.zero_rpow (by positivity), ENNReal.ofReal_zero, zero_smul]

end Setting

/-! ### Finite-dimensionality of the sections -/

section Finiteness

/-- On a one-point space, the germ at the point of a section over `⊤` is a bijection. -/
private lemma bijective_germ_top_of_subsingleton {X : TopCat.{u}} [Subsingleton X] {C : Type*}
    [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{u} C FC] [Limits.HasColimits.{u} C]
    [Limits.PreservesFilteredColimits (forget C)]
    (F : X.Presheaf C) (x : X) : Function.Bijective (F.germ ⊤ x trivial) := by
  have hU : ∀ U : Opens X, x ∈ U → U = ⊤ := fun U hU => by
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    rwa [Subsingleton.elim y x]
  refine ⟨fun a b h => ?_, fun t => ?_⟩
  · obtain ⟨W, hW, iU, iV, he⟩ := F.germ_eq (U := ⊤) (V := ⊤) x trivial trivial a b h
    obtain rfl := hU W hW
    obtain rfl : iU = 𝟙 _ := Subsingleton.elim _ _
    obtain rfl : iV = 𝟙 _ := Subsingleton.elim _ _
    simpa using he
  · obtain ⟨W, hW, a, rfl⟩ := F.exists_germ_eq t
    obtain rfl := hU W hW
    exact ⟨a, rfl⟩

/-- The `k`-rank of `H⁰(Y, 𝒪_Y(E))` is the rank of the stalk of `π_* 𝒪_Y(E)` at the point of
`Spec k`. -/
private theorem rank_sections_eq_rank_stalk {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (s : Y ⟶ Spec (.of k)) (E : Divisor Y) :
    letI G := (Scheme.Modules.pushforward s).obj E.divisorialSheaf
    letI : Module ((Spec (.of k)).presheaf.stalk (genericPoint (Spec (.of k))))
        (G.presheaf.stalk (genericPoint (Spec (.of k)))) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec (.of k)).presheaf) G.val (genericPoint (Spec (.of k)))
    letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
    Module.rank k (E.divisorialSubmodule ⊤) =
      Module.rank ((Spec (.of k)).presheaf.stalk (genericPoint (Spec (.of k))))
        (G.presheaf.stalk (genericPoint (Spec (.of k)))) := by
  haveI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  set G := (Scheme.Modules.pushforward s).obj E.divisorialSheaf
  set η := genericPoint (Spec (.of k))
  have hR := bijective_germ_top_of_subsingleton (Spec (.of k)).presheaf η
  have hM := bijective_germ_top_of_subsingleton G.presheaf η
  letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
  let j : E.divisorialSubmodule ⊤ ≃+ G.presheaf.stalk η :=
    AddEquiv.ofBijective (G.presheaf.germ ⊤ η trivial).hom hM
  exact rank_eq_of_equiv_equiv (R := k) (R' := (Spec (.of k)).presheaf.stalk η)
    (fun c => (Spec (.of k)).presheaf.germ ⊤ η trivial ((Scheme.ΓSpecIso (.of k)).inv c)) j
    (hR.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)) (fun c m =>
      (PresheafOfModules.germ_smul (R := (Spec (.of k)).presheaf) G.val η ⊤ trivial _ m))

/-- `H⁰(Y, 𝒪_Y(E))` is finite-dimensional over `k` for a Cartier divisor `E` on `Y` proper over
`k`: the direct image of the coherent `𝒪_Y(E)` is coherent ([Stacks, Tag 02O5]). -/
theorem finiteDimensional_sections {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (s : Y ⟶ Spec (.of k)) [IsProper s]
    (E : Divisor Y) (hE : E.IsCartier) :
    letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
    FiniteDimensional k (E.divisorialSubmodule ⊤) := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have hinv := hE.isInvertibleModule_divisorialSheaf
  have : (E.divisorialSheaf).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y _ _ hinv
  have : ((Scheme.Modules.pushforward s).obj E.divisorialSheaf).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward s E.divisorialSheaf
  have hfin := Scheme.Modules.finite_stalk_of_isCoherent
    ((Scheme.Modules.pushforward s).obj E.divisorialSheaf) (genericPoint (Spec (.of k)))
  letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
  have hlt : Module.rank k (E.divisorialSubmodule ⊤) < Cardinal.aleph0 := by
    rw [rank_sections_eq_rank_stalk s E]
    exact Module.rank_lt_aleph0 _ _
  exact Module.rank_lt_aleph0_iff.mp hlt

private theorem germ_eq_rationalFunctionsEquivFunctionField_symm {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) (s : Γ(X, U))
    (h : genericPoint X ∈ U) (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U) :
    (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s) Z =
      X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hd : Dense (U : Set X) := U.isOpen.dense ⟨_, h⟩
  let D : Stacks.Chow.DenseOpen X := ⟨U, hd⟩
  have key : (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s)
      = (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X D s) := by
    rw [RingEquiv.symm_apply_eq, ← (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 D s h]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm _)
    rw [RingEquiv.symm_apply_apply]
  rw [key]
  exact (Stacks.Chow.rationalFunctionsEquivStalks X).2 D s Z hZ

private theorem componentGenericPoint_eq {X : Scheme.{u}} [IsIntegral X]
    (Z : irreducibleComponents X) :
    componentGenericPoint X Z = genericPoint X := by
  have hZ : Z.1 = Set.univ := by
    simpa [irreducibleComponents_eq_singleton] using Z.2
  have h1 := isGenericPoint_componentGenericPoint X Z
  rw [hZ] at h1
  exact h1.eq (genericPoint_spec X)

private theorem stalkSpecializes_rationalFunctionsEquivFunctionField_symm {X : Scheme.{u}}
    [IsIntegral X] (Z : irreducibleComponents X) (φ : X.functionField) :
    (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
        (Set.mem_univ (componentGenericPoint X Z)))).hom
      ((rationalFunctionsEquivFunctionField X).symm φ Z) = φ := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) φ
  have hZ : componentGenericPoint X Z ∈ U := (componentGenericPoint_eq Z) ▸ hx
  rw [germ_eq_rationalFunctionsEquivFunctionField_symm U s hx Z hZ,
    TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem valuation_rationalFunctionsEquivFunctionField_symm {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X)
    (φ : X.functionField) :
    E.valuation ((rationalFunctionsEquivFunctionField X).symm φ E.component) =
      X.ordHom E.genericPoint E.coheight_genericPoint φ := by
  set a := (rationalFunctionsEquivFunctionField X).symm φ E.component
  let ψ := (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
        (Set.mem_univ (componentGenericPoint X E.component)))).hom
  have hψ : ψ a = φ := stalkSpecializes_rationalFunctionsEquivFunctionField_symm _ φ
  letI := E.toComponent.hom.toAlgebra
  haveI := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  haveI : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  let alg1 := IsLocalization.algEquiv (nonZeroDivisors E.localRing)
    (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
  let Eq := (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
    X.functionField).toRingEquiv
  have hEq : ∀ r : E.localRing, Eq (algebraMap E.localRing (FractionRing E.localRing) r) =
      algebraMap E.localRing X.functionField (RingEquiv.refl E.localRing r) := fun r =>
    (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
      X.functionField).commutes r
  have hcomp : Eq (alg1 a) = φ := by
    rw [← hψ]
    have : (Eq.toRingHom.comp alg1.toRingEquiv.toRingHom) = ψ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors E.localRing) ?_
      ext r
      simp only [RingHom.comp_apply]
      change Eq (alg1 (algebraMap _ _ r)) = _
      rw [AlgEquiv.commutes, hEq]
      change _ = ψ ((X.presheaf.stalkSpecializes E.specializes_genericPoint).hom r)
      simp only [ψ]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    exact congrArg (fun f => f a) this
  change Ring.ordFrac E.localRing (alg1 a) = Ring.ordFrac E.localRing φ
  rw [← hcomp]
  exact (Stacks.Chow.ordFrac_congr (RingEquiv.refl E.localRing) Eq hEq (alg1 a)).symm

private theorem ordGE_iff {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (E : MMP.Mori.PrimeDivisor X) (n : ℤ) (φ : X.functionField) :
    E.OrdGE n ((rationalFunctionsEquivFunctionField X).symm φ E.component) ↔
      φ = 0 ∨ n ≤ X.ord φ E.genericPoint := by
  unfold MMP.Mori.PrimeDivisor.OrdGE
  rw [valuation_rationalFunctionsEquivFunctionField_symm]
  have h0 : (rationalFunctionsEquivFunctionField X).symm φ E.component = 0 ↔ φ = 0 := by
    constructor
    · intro h
      rw [← stalkSpecializes_rationalFunctionsEquivFunctionField_symm E.component φ, h, map_zero]
    · rintro rfl
      rw [map_zero]
      rfl
  rw [h0]
  by_cases hφ : φ = 0
  · simp [hφ]
  · simp only [hφ, false_or]
    rw [(Scheme.ord_eq_iff E.coheight_genericPoint hφ).mp rfl]
    exact WithZero.exp_le_exp

end Finiteness

/-! ### Continuity of the total mass along a finite family -/

section Continuity

section Evaluation

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

private lemma eval_mul (V : X.Opens) (f g : Γ(X, V)) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (f * g) y = ComplexPoints.eval V f y * ComplexPoints.eval V g y := by
  simp [ComplexPoints.eval]

private lemma eval_add (V : X.Opens) (f g : Γ(X, V)) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (f + g) y = ComplexPoints.eval V f y + ComplexPoints.eval V g y := by
  simp [ComplexPoints.eval]

private lemma eval_zero (V : X.Opens) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (0 : Γ(X, V)) y = 0 := by
  simp [ComplexPoints.eval]

private lemma eval_one (V : X.Opens) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (1 : Γ(X, V)) y = 1 := by
  simp [ComplexPoints.eval]

private lemma eval_appLE (V : X.Opens) (e : V ≤ sX ⁻¹ᵁ ⊤) (a : Γ(Spec (.of ℂ), ⊤))
    (y : chart (sX := sX) V) :
    ComplexPoints.eval V (sX.appLE ⊤ V e a) y = (Scheme.ΓSpecIso (.of ℂ)).hom a := by
  have h2 : y.1.hom ≫ sX = 𝟙 _ := y.1.2
  have key : sX.appLE ⊤ V e ≫ y.1.hom.appLE V ⊤ y.2.ge = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have aux : ∀ (f : Spec (.of ℂ) ⟶ Spec (.of ℂ)), f = 𝟙 _ → ∀ e, f.appLE ⊤ ⊤ e = 𝟙 _ := by
      rintro _ rfl e
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact (Spec (.of ℂ)).presheaf.map_id _
    exact aux _ h2 _
  have := congrArg (fun φ => (Scheme.ΓSpecIso (.of ℂ)).hom.hom (φ.hom a)) key
  exact this

private lemma mem_chart_of_mem {U : X.Opens} {y : ComplexPoints sX} (q : Spec (.of ℂ))
    (hq : y.hom.base q ∈ U) : y ∈ chart U := by
  change y.hom ⁻¹ᵁ U = ⊤
  ext q'
  rw [Subsingleton.elim q' q]
  simpa using hq

private lemma mem_of_mem_chart {U : X.Opens} {y : ComplexPoints sX} (hy : y ∈ chart U)
    (q : Spec (.of ℂ)) : y.hom.base q ∈ U := by
  have : q ∈ y.hom ⁻¹ᵁ U := by
    change y.hom ⁻¹ᵁ U = ⊤ at hy
    rw [hy]
    trivial
  exact this

private lemma mem_chart_top (y : ComplexPoints sX) : y ∈ chart (⊤ : X.Opens) :=
  mem_chart_of_mem sX (Classical.arbitrary _) trivial

private lemma eval_res {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : ComplexPoints sX)
    (hy : y ∈ chart V) :
    ComplexPoints.eval V (X.presheaf.map (homOfLE h).op f) ⟨y, hy⟩ =
      ComplexPoints.eval U f ⟨y, ComplexPoints.chart_mono h hy⟩ := by
  simp only [ComplexPoints.eval]
  congr 1
  change (X.presheaf.map (homOfLE h).op ≫ y.hom.appLE V ⊤ _) f = _
  rw [Scheme.Hom.map_appLE]

private lemma mem_chart_inf {V V' : X.Opens} {y : ComplexPoints sX} (hy : y ∈ chart V)
    (hy' : y ∈ chart V') : y ∈ chart (V ⊓ V') := by
  change y.hom ⁻¹ᵁ (V ⊓ V') = ⊤
  have h1 : y.hom ⁻¹ᵁ V = ⊤ := hy
  have h2 : y.hom ⁻¹ᵁ V' = ⊤ := hy'
  rw [Scheme.Hom.preimage_inf, h1, h2, top_inf_eq]

/-- The constant section `c` of `𝒪_X` over `V`. -/
private noncomputable def constSec (V : X.Opens) (c : ℂ) : Γ(X, V) :=
  X.presheaf.map (homOfLE le_top).op (sX.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c))

private lemma eval_constSec (V : X.Opens) (c : ℂ) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (constSec sX V c) y = c :=
  (eval_appLE sX V le_top _ y).trans (by simp)

private lemma germ_constSec_mul [IsIntegral X] (V : X.Opens) (c : ℂ) (g : Γ(X, V))
    (hg : genericPoint X ∈ V) :
    X.presheaf.germ V (genericPoint X) hg (constSec sX V c * g) =
      @algebraMap ℂ X.functionField _ _ (MMP.Mori.functionFieldAlgebra sX) c *
        X.presheaf.germ V (genericPoint X) hg g := by
  rw [map_mul]
  congr 1
  unfold constSec
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

variable [IsIntegral X]

/-- The density at a point where the rational function has a regular representative. -/
private lemma pluriformDensity_eq (m : ℕ) (φ : X.functionField) (y : ComplexPoints sX)
    (V : X.Opens) (g : Γ(X, V)) (hy : y ∈ chart V) (hg : genericPoint X ∈ V)
    (hgφ : X.presheaf.germ V (genericPoint X) hg g = φ) :
    pluriformDensity sX m φ y =
      ENNReal.ofReal (‖ComplexPoints.eval V g ⟨y, hy⟩‖ ^ (2 / m : ℝ)) := by
  refine le_antisymm ?_ (le_iSup_of_le V <| le_iSup_of_le g <| le_iSup_of_le hy <|
    le_iSup_of_le hg <| le_iSup_of_le hgφ le_rfl)
  refine iSup_le fun V₂ ↦ iSup_le fun g₂ ↦ iSup_le fun hy₂ ↦ iSup_le fun hg₂ ↦
    iSup_le fun hgφ₂ ↦ ?_
  have hη : genericPoint X ∈ V ⊓ V₂ := ⟨hg, hg₂⟩
  haveI : Nonempty (V ⊓ V₂ : X.Opens) := ⟨⟨_, hη⟩⟩
  have hres : X.presheaf.map (homOfLE (inf_le_left : V ⊓ V₂ ≤ V)).op g =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ V₂ ≤ V₂)).op g₂ := by
    apply germ_injective_of_isIntegral X _ hη
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hgφ, hgφ₂]
  have hyy := mem_chart_inf sX hy hy₂
  have e1 := eval_res sX (inf_le_left : V ⊓ V₂ ≤ V) g y hyy
  have e2 := eval_res sX (inf_le_right : V ⊓ V₂ ≤ V₂) g₂ y hyy
  rw [hres] at e1
  rw [← e2, e1]

/-- `y ↦ |g(y)|^{2/m}` on `V(ℂ)`, and `0` off it, is lower semicontinuous on `X^an`. -/
private theorem lowerSemicontinuous_iSup_mem_chart (p : ℝ) (hp : 0 ≤ p) (V : X.Opens)
    (g : Γ(X, V)) :
    LowerSemicontinuous fun y : ComplexPoints sX ↦
      ⨆ hy : y ∈ chart V, ENNReal.ofReal (‖eval V g ⟨y, hy⟩‖ ^ p) := by
  classical
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have hS : IsOpen (chart (sX := sX) V) := MMP.Analytic.InvertibleModule.isOpen_chart V
  let e : ComplexPoints sX → ℂ := fun y ↦ if hy : y ∈ chart V then eval V g ⟨y, hy⟩ else 0
  have hev : ContinuousOn e (chart (sX := sX) V) :=
    MMP.Analytic.InvertibleModule.continuousOn_evalExt V g
  have hK : ContinuousOn (fun y ↦ ENNReal.ofReal (‖e y‖ ^ p)) (chart (sX := sX) V) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((continuous_norm.comp_continuousOn hev).rpow_const fun _ _ ↦ Or.inr hp)
  intro y c hc
  simp only at hc ⊢
  by_cases hy : y ∈ chart (sX := sX) V
  · rw [iSup_pos hy] at hc
    have hc' : c < ENNReal.ofReal (‖e y‖ ^ p) := by simpa [e, dif_pos hy] using hc
    filter_upwards [(hK.continuousAt (hS.mem_nhds hy)).eventually (lt_mem_nhds hc'),
      hS.mem_nhds hy] with y' h1 h2
    rw [iSup_pos h2]
    simpa [e, dif_pos h2] using h1
  · simp [hy] at hc

/-- The density `|φ|^{2/m}` is lower semicontinuous on `X^an`. -/
private theorem lowerSemicontinuous_pluriformDensity (m : ℕ) (φ : X.functionField) :
    LowerSemicontinuous (pluriformDensity sX m φ) := by
  unfold pluriformDensity
  refine lowerSemicontinuous_iSup fun V ↦ lowerSemicontinuous_iSup fun g ↦ ?_
  have : (fun y : ComplexPoints sX ↦ ⨆ (hy : y ∈ chart V) (hg : genericPoint X ∈ V)
      (_ : X.presheaf.germ V (genericPoint X) hg g = φ),
        ENNReal.ofReal (‖eval V g ⟨y, hy⟩‖ ^ (2 / m : ℝ))) =
      fun y ↦ ⨆ (hg : genericPoint X ∈ V) (_ : X.presheaf.germ V (genericPoint X) hg g = φ)
        (hy : y ∈ chart V), ENNReal.ofReal (‖eval V g ⟨y, hy⟩‖ ^ (2 / m : ℝ)) := by
    funext y
    rw [iSup_comm]
    exact iSup_congr fun _ ↦ iSup_comm
  rw [this]
  exact lowerSemicontinuous_iSup fun _ ↦ lowerSemicontinuous_iSup fun _ ↦
    lowerSemicontinuous_iSup_mem_chart sX _ (by positivity) V g

/-- A representative of `∑ⱼ aⱼ φⱼ` from representatives of the `φⱼ` at a point `y`, with value
`∑ⱼ aⱼ φⱼ(y)`. -/
private lemma exists_germ_sum (y : ComplexPoints sX) {ι : Type*} (S : Finset ι)
    (c : ι → X.functionField) (a : ι → ℂ) (V : ι → X.Opens) (g : ∀ j, Γ(X, V j))
    (hy : ∀ j, y ∈ chart (V j)) (hg : ∀ j, genericPoint X ∈ V j)
    (hgc : ∀ j, X.presheaf.germ (V j) _ (hg j) (g j) = c j) :
    ∃ (V' : X.Opens) (g' : Γ(X, V')) (hy' : y ∈ chart V') (hg' : genericPoint X ∈ V'),
      X.presheaf.germ V' _ hg' g' =
        ∑ j ∈ S, @algebraMap ℂ X.functionField _ _ (MMP.Mori.functionFieldAlgebra sX) (a j) *
          c j ∧
      ComplexPoints.eval V' g' ⟨y, hy'⟩ =
        ∑ j ∈ S, a j * ComplexPoints.eval (V j) (g j) ⟨y, hy j⟩ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⊤, 0, mem_chart_top sX y, trivial, by simp, by simp [eval_zero]⟩
  | insert j S hj ih =>
    obtain ⟨V', g', hy', hg', h1, h2⟩ := ih
    refine ⟨V j ⊓ V', X.presheaf.map (homOfLE inf_le_left).op (constSec sX (V j) (a j) * g j) +
      X.presheaf.map (homOfLE inf_le_right).op g', mem_chart_inf sX (hy j) hy',
      (show genericPoint X ∈ V j ⊓ V' from ⟨hg j, hg'⟩),
      ?_, ?_⟩
    · rw [Finset.sum_insert hj, map_add, TopCat.Presheaf.germ_res_apply,
        TopCat.Presheaf.germ_res_apply, germ_constSec_mul, hgc, h1]
    · rw [Finset.sum_insert hj, eval_add, eval_res, eval_res, eval_mul, eval_constSec, h2]

/-- The density of `∑ⱼ aⱼ φⱼ` at a point where every `φⱼ` is regular. -/
private lemma pluriformDensity_sum (m : ℕ) (y : ComplexPoints sX) {k : ℕ}
    (c : Fin k → X.functionField) (a : Fin k → ℂ) (V : Fin k → X.Opens) (g : ∀ j, Γ(X, V j))
    (hy : ∀ j, y ∈ chart (V j)) (hg : ∀ j, genericPoint X ∈ V j)
    (hgc : ∀ j, X.presheaf.germ (V j) _ (hg j) (g j) = c j) :
    pluriformDensity sX m
        (∑ j, @algebraMap ℂ X.functionField _ _ (MMP.Mori.functionFieldAlgebra sX) (a j) * c j)
        y =
      ENNReal.ofReal (‖∑ j, a j * ComplexPoints.eval (V j) (g j) ⟨y, hy j⟩‖ ^ (2 / m : ℝ)) := by
  obtain ⟨V', g', hy', hg', h1, h2⟩ := exists_germ_sum sX y Finset.univ c a V g hy hg hgc
  rw [pluriformDensity_eq sX m _ y V' g' hy' hg' h1, h2]

/-- The density of the rational function `1` is `1` on `U(ℂ)`. -/
private lemma pluriformDensity_one (m : ℕ) (U : X.Opens) [Nonempty U] (y : ComplexPoints sX)
    (hy : y ∈ chart U) : pluriformDensity sX m 1 y = 1 := by
  have hη : genericPoint X ∈ U := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact (genericPoint_spec X).mem_open_set_iff U.isOpen |>.2 ⟨x.1, trivial, x.2⟩
  rw [pluriformDensity_eq sX m 1 y U 1 hy hη (map_one _), eval_one]
  simp

end Evaluation

section Coefficient

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] {n m : ℕ}

/-- The coefficient `s ↦ φ` of `s = φ (dz)^{⊗m}` is `ℂ(X)`-linear, and it is either onto (some form
has coefficient `1`) or zero. -/
private lemma exists_linearMap_pluriformCoeff (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U)) :
    ∃ L : MMP.Mori.RationalPluriForms sX n m →ₗ[X.functionField] X.functionField,
      (∀ s, pluriformCoeff sX s U z = L s) ∧ ((∃ s₀, L s₀ = 1) ∨ L = 0) := by
  classical
  letI := MMP.Mori.functionFieldAlgebra sX
  set dz : ⋀[X.functionField]^n Ω[X.functionField⁄ℂ] :=
    exteriorPower.ιMulti X.functionField n
      (fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField U (z i))) with hdz
  by_cases h : Submodule.span X.functionField {dz} = ⊤ ∧ dz ≠ 0
  · let b : Module.Basis Unit X.functionField (MMP.Mori.RationalPluriForms sX n m) :=
      MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton h.1 h.2) (m : ℤ)
    refine ⟨(Finsupp.lapply ()) ∘ₗ b.repr.toLinearMap, fun s => ?_, Or.inl ⟨b (), by simp⟩⟩
    unfold pluriformCoeff
    simp only [← hdz, dif_pos h]
    rfl
  · refine ⟨0, fun s => ?_, Or.inr rfl⟩
    unfold pluriformCoeff
    simp only [← hdz, dif_neg h]
    rfl

end Coefficient

section Charts

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (n : ℕ)

/-- An étale chart of `X^an`: étale coordinates `z` on a Zariski open `U` together with an open
`W ⊆ U(ℂ)` on which `z` is an open embedding into `ℂⁿ`. -/
private structure EtaleChart where
  U : X.Opens
  ne : Nonempty U
  z : Fin n → Γ(X, U)
  hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
    (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))
  W : Set (ComplexPoints sX)
  hW : W ⊆ chart U
  hWo : IsOpen W
  hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)

variable {sX n}

private instance (c : EtaleChart sX n) : Nonempty c.U := c.ne

/-- The measure `z^* λ` on the chart `W`, pushed forward to `X^an`. -/
private noncomputable def EtaleChart.baseMeasure [MeasurableSpace (ComplexPoints sX)]
    (c : EtaleChart sX n) : Measure (ComplexPoints sX) :=
  (Measure.comap (fun y : c.W ↦ fun i ↦ eval c.U (c.z i) ⟨y.1, c.hW y.2⟩)
      (volume : Measure (Fin n → ℂ))).map Subtype.val

variable [IsIntegral X] [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]

attribute [local instance] complexBorel borelSpace_complexPoints

private lemma EtaleChart.pluriformChartMeasure_eq {m : ℕ} (hm : 0 < m) (c : EtaleChart sX n)
    (s : RationalPluriForms sX n m) :
    haveI := c.ne
    pluriformChartMeasure sX hm s c.U c.z c.hz c.W c.hW c.hWo c.hWz =
      c.baseMeasure.withDensity (pluriformDensity sX m (pluriformCoeff sX s c.U c.z)) := rfl

/-- The base measure of a chart is carried by `W`. -/
private lemma EtaleChart.baseMeasure_compl (c : EtaleChart sX n) : c.baseMeasure c.Wᶜ = 0 := by
  unfold EtaleChart.baseMeasure
  rw [Measure.map_apply measurable_subtype_coe c.hWo.measurableSet.compl]
  have : (Subtype.val ⁻¹' c.Wᶜ : Set c.W) = ∅ := by
    ext y
    simp [y.2]
  rw [this, measure_empty]

/-- Almost every point of a chart, for its base measure, is a point where the coefficient of `s`
on the chart is regular: the base measure is the chart measure of a form of coefficient `1`, which
does not charge `Z^an` for a proper Zariski closed `Z`. -/
private lemma EtaleChart.ae_regular {m : ℕ} (hm : 0 < m) (c : EtaleChart sX n)
    (s : RationalPluriForms sX n m) :
    ∀ᵐ y ∂c.baseMeasure, ∃ (V : X.Opens) (g : Γ(X, V)) (_ : y ∈ chart V)
      (hg : genericPoint X ∈ V), X.presheaf.germ V _ hg g = pluriformCoeff sX s c.U c.z := by
  haveI := c.ne
  obtain ⟨L, hL, hL1 | hL0⟩ := exists_linearMap_pluriformCoeff (m := m) sX c.U c.z
  · obtain ⟨s₀, hs₀⟩ := hL1
    obtain ⟨V, hη, g, hg⟩ := X.presheaf.germ_exist (x := genericPoint X)
      (pluriformCoeff sX s c.U c.z)
    -- the chart measure of `s₀` is the base measure
    have hρ : pluriformDensity sX m (pluriformCoeff sX s₀ c.U c.z) =ᵐ[c.baseMeasure] 1 := by
      have hW : ∀ᵐ y ∂c.baseMeasure, y ∈ c.W := measure_eq_zero_iff_ae_notMem.1
        c.baseMeasure_compl |>.mono fun y hy => by simpa using hy
      filter_upwards [hW] with y hy
      rw [hL, hs₀]
      exact pluriformDensity_one sX m c.U y (c.hW hy)
    have heq : pluriformChartMeasure sX hm s₀ c.U c.z c.hz c.W c.hW c.hWo c.hWz =
        c.baseMeasure := by
      rw [c.pluriformChartMeasure_eq hm s₀, withDensity_congr_ae hρ, withDensity_one]
    have hZ : IsClosed (V : Set X)ᶜ := V.isOpen.isClosed_compl
    have hZne : (V : Set X)ᶜ ≠ Set.univ := fun h =>
      (Set.eq_univ_iff_forall.1 h (genericPoint X)) hη
    have hnull := ((pluriformChartMeasure_proper_closed_null sX hm s₀ c.U c.z c.hz c.W c.hW c.hWo
      c.hWz).1 _ hZ hZne)
    rw [heq] at hnull
    refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
    simp only [Set.mem_setOf_eq] at hy ⊢
    rintro _ ⟨q, rfl⟩ hq
    exact hy ⟨V, g, mem_chart_of_mem sX q hq, hη, hg⟩
  · refine Eventually.of_forall fun y => ⟨⊤, 0, mem_chart_top sX y, trivial, ?_⟩
    rw [hL, hL0, map_zero, LinearMap.zero_apply]

end Charts

section Measure

/-! The analytic core: dominated convergence. -/

/-- `‖∑ aⱼ wⱼ‖^p ≤ (k ‖a‖)^p ∑ⱼ ‖wⱼ‖^p`. -/
private theorem norm_sum_mul_rpow_le {k : ℕ} {p : ℝ} (hp : 0 < p) (a w : Fin k → ℂ) :
    ‖∑ j, a j * w j‖ ^ p ≤ (k * ‖a‖) ^ p * ∑ j, ‖w j‖ ^ p := by
  have h1 : ‖∑ j, a j * w j‖ ≤ k * ‖a‖ * ‖w‖ := by
    calc ‖∑ j, a j * w j‖ ≤ ∑ j, ‖a j * w j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin k, ‖a‖ * ‖w‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm a j) (norm_le_pi_norm w j) (norm_nonneg _)
            (norm_nonneg _)
      _ = k * ‖a‖ * ‖w‖ := by simp [mul_assoc]
  have h2 : ‖w‖ ^ p ≤ ∑ j, ‖w j‖ ^ p := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Subsingleton.elim w 0, norm_zero, Real.zero_rpow hp.ne']
      simp
    · haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      obtain ⟨j, hj⟩ := Finite.exists_max fun j => ‖w j‖
      have : ‖w‖ = ‖w j‖ := le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hj)
        (norm_le_pi_norm w j)
      rw [this]
      exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ p)
        (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
  calc ‖∑ j, a j * w j‖ ^ p ≤ (k * ‖a‖ * ‖w‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hp.le
    _ = (k * ‖a‖) ^ p * ‖w‖ ^ p := Real.mul_rpow (by positivity) (norm_nonneg _)
    _ ≤ (k * ‖a‖) ^ p * ∑ j, ‖w j‖ ^ p :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Dominated convergence along a finite family.** If, almost everywhere, `ρ a = |∑ⱼ aⱼ wⱼ|^p`
for all `a`, and each `ρ (eⱼ)` is integrable, then `a ↦ ∫ ρ a` is continuous. -/
private theorem continuous_toReal_lintegral_of_ae_eq {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {k : ℕ} {p : ℝ} (hp : 0 < p) (ρ : (Fin k → ℂ) → Y → ℝ≥0∞) (hρm : ∀ a, Measurable (ρ a))
    (w : Y → Fin k → ℂ)
    (hρ : ∀ᵐ y ∂ν, ∀ a, ρ a y = ENNReal.ofReal (‖∑ j, a j * w y j‖ ^ p))
    (hfin : ∀ j, ∫⁻ y, ρ (Pi.single j 1) y ∂ν < ⊤) :
    Continuous fun a => (∫⁻ y, ρ a y ∂ν).toReal := by
  have hw : ∀ᵐ y ∂ν, ∀ j, ρ (Pi.single j 1) y = ENNReal.ofReal (‖w y j‖ ^ p) := by
    filter_upwards [hρ] with y hy j
    rw [hy]
    congr 3
    simp [Pi.single_apply]
  have heq : ∀ a, (∫⁻ y, ρ a y ∂ν).toReal = ∫ y, (ρ a y).toReal ∂ν := by
    intro a
    rw [integral_toReal (hρm a).aemeasurable]
    filter_upwards [hρ] with y hy
    rw [hy]
    exact ENNReal.ofReal_lt_top
  simp_rw [heq]
  rw [continuous_iff_continuousAt]
  intro a₀
  set R : ℝ := ‖a₀‖ + 1
  let bound : Y → ℝ := fun y => (k * R) ^ p * ∑ j, (ρ (Pi.single j 1) y).toReal
  refine continuousAt_of_dominated (bound := bound) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun a =>
      ((hρm a).ennreal_toReal).aestronglyMeasurable
  · have hball : ∀ᶠ a in 𝓝 a₀, ‖a‖ ≤ R := by
      filter_upwards [Metric.ball_mem_nhds a₀ one_pos] with a ha
      have := norm_le_norm_add_norm_sub' a a₀
      rw [Metric.mem_ball, dist_eq_norm] at ha
      simp only [R]
      linarith [norm_sub_rev a a₀]
    filter_upwards [hball] with a ha
    filter_upwards [hρ, hw] with y hy hy'
    rw [hy, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
    simp only [bound, hy', ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
    refine (norm_sum_mul_rpow_le hp a (w y)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _)
    exact Real.rpow_le_rpow (by positivity) (by gcongr) hp.le
  · refine Integrable.const_mul (integrable_finset_sum _ fun j _ => ?_) _
    exact integrable_toReal_of_lintegral_ne_top (hρm _).aemeasurable (hfin j).ne
  · filter_upwards [hρ] with y hy
    simp_rw [hy, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
    refine Continuous.continuousAt ?_
    refine Continuous.rpow_const (continuous_norm.comp ?_) fun _ => Or.inr hp.le
    exact continuous_finset_sum _ fun j _ => (continuous_apply j).mul continuous_const

end Measure

section Decomposition

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} [IsIntegral X]
  [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]

attribute [local instance] complexBorel borelSpace_complexPoints

/-- A finite measurable partition of the compact `X^an` subordinate to étale charts. -/
private lemma exists_chart_partition (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX) :
    ∃ (r : ℕ) (c : Fin r → EtaleChart sX n) (P : Fin r → Set (ComplexPoints sX)),
      (∀ i, MeasurableSet (P i)) ∧ (∀ i, P i ⊆ (c i).W) ∧ Pairwise (Function.onFun Disjoint P) ∧
        ⋃ i, P i = Set.univ := by
  haveI := compactSpace_complexPoints hX
  have hch : ∀ x : ComplexPoints sX, ∃ c : EtaleChart sX n, x ∈ c.W := by
    intro x
    obtain ⟨U, z, hz, hx⟩ := (etaleCoordinate_atlas sX (n := n)).1 x
    obtain ⟨W, hW, hWo, hxW, hWz⟩ := (etaleCoordinate_atlas sX (n := n)).2.1 U z hz x hx
    have hU : Nonempty U := ⟨⟨_, mem_of_mem_chart sX hx (Classical.arbitrary _)⟩⟩
    exact ⟨⟨U, hU, z, hz, W, hW, hWo, hWz⟩, hxW⟩
  choose ch hxch using hch
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (ch x).W) (fun x => (ch x).hWo)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxch x⟩)
  let e : Fin t.card ≃ t := t.equivFin.symm
  let c : Fin t.card → EtaleChart sX n := fun i => ch (e i)
  refine ⟨t.card, c, disjointed fun i : Fin t.card => (c i).W,
    fun i => by
      rw [disjointed_eq_inter_compl]
      exact (c i).hWo.measurableSet.inter (MeasurableSet.iInter fun j =>
        MeasurableSet.iInter fun _ => (c j).hWo.measurableSet.compl), disjointed_subset _,
    disjoint_disjointed _, ?_⟩
  rw [iUnion_disjointed]
  refine Set.eq_univ_of_univ_subset (ht.trans fun y hy => ?_)
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
  exact Set.mem_iUnion.2 ⟨e.symm ⟨x, hx⟩, by simp [c, hyx]⟩

/-- The total mass of `μ_s` as a finite sum of chart integrals over a partition. -/
private lemma gluedMeasure_univ_eq_sum {m : ℕ} (hm : 0 < m) {r : ℕ} (c : Fin r → EtaleChart sX n)
    (P : Fin r → Set (ComplexPoints sX)) (hPm : ∀ i, MeasurableSet (P i))
    (hPW : ∀ i, P i ⊆ (c i).W) (hPd : Pairwise (Function.onFun Disjoint P))
    (hPu : ⋃ i, P i = Set.univ) (s : RationalPluriForms sX n m) :
    gluedMeasure hm s Set.univ = ∑ i, ∫⁻ y in P i,
      pluriformDensity sX m (pluriformCoeff sX s (c i).U (c i).z) y ∂(c i).baseMeasure := by
  rw [← hPu, measure_iUnion hPd hPm, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Measure.restrict_apply_self, ← Measure.restrict_restrict_of_subset (hPW i),
    isGlued_gluedMeasure hm s (c i).U (c i).z (c i).hz (c i).W (c i).hW (c i).hWo (c i).hWz,
    (c i).pluriformChartMeasure_eq hm s, Measure.restrict_apply_self,
    withDensity_apply _ (hPm i)]

/-- **Continuity of the total mass along a finite family.** `a ↦ μ_{∑ aⱼ tⱼ}(X^an)` is continuous
when all these masses are finite. -/
private theorem continuous_gluedMeasure_univ_sum (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX)
    {m : ℕ} (hm : 0 < m) {k : ℕ} (t : Fin k → RationalPluriForms sX n m)
    (hfin : ∀ a : Fin k → ℂ, gluedMeasure hm (∑ j, a j • t j) Set.univ < ⊤) :
    Continuous fun a : Fin k → ℂ => (gluedMeasure hm (∑ j, a j • t j) Set.univ).toReal := by
  classical
  letI := MMP.Mori.functionFieldAlgebra sX
  obtain ⟨r, c, P, hPm, hPW, hPd, hPu⟩ := exists_chart_partition (n := n) hX
  have hdec := gluedMeasure_univ_eq_sum hm c P hPm hPW hPd hPu
  have hle : ∀ (s : RationalPluriForms sX n m) i, ∫⁻ y in P i,
      pluriformDensity sX m (pluriformCoeff sX s (c i).U (c i).z) y ∂(c i).baseMeasure ≤
        gluedMeasure hm s Set.univ := fun s i => by
    rw [hdec s]
    exact Finset.single_le_sum (f := fun i => ∫⁻ y in P i,
      pluriformDensity sX m (pluriformCoeff sX s (c i).U (c i).z) y ∂(c i).baseMeasure)
      (fun _ _ => zero_le) (Finset.mem_univ i)
  have hsum : (fun a : Fin k → ℂ => (gluedMeasure hm (∑ j, a j • t j) Set.univ).toReal) =
      fun a => ∑ i, (∫⁻ y in P i, pluriformDensity sX m
        (pluriformCoeff sX (∑ j, a j • t j) (c i).U (c i).z) y ∂(c i).baseMeasure).toReal := by
    funext a
    rw [hdec, ENNReal.toReal_sum fun i _ => ((hle _ i).trans_lt (hfin a)).ne]
  rw [hsum]
  refine continuous_finset_sum _ fun i _ => ?_
  -- the coefficients of the `tⱼ` on the chart `c i`, and their values
  let φ : Fin k → X.functionField := fun j => pluriformCoeff sX (t j) (c i).U (c i).z
  let w : ComplexPoints sX → Fin k → ℂ := fun y j =>
    if h : ∃ (V : X.Opens) (g : Γ(X, V)) (_ : y ∈ chart V) (hg : genericPoint X ∈ V),
        X.presheaf.germ V _ hg g = φ j then
      eval h.choose h.choose_spec.choose ⟨y, h.choose_spec.choose_spec.choose⟩
    else 0
  obtain ⟨L, hL, -⟩ := exists_linearMap_pluriformCoeff (m := m) sX (c i).U (c i).z
  have hcoeff : ∀ a : Fin k → ℂ, pluriformCoeff sX (∑ j, a j • t j) (c i).U (c i).z =
      ∑ j, algebraMap ℂ X.functionField (a j) * φ j := by
    intro a
    rw [hL, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RationalPluriForms.smul_def, map_smul, smul_eq_mul]
    exact congrArg _ (hL (t j)).symm
  refine continuous_toReal_lintegral_of_ae_eq _ (p := 2 / m) (by positivity)
    (fun a => pluriformDensity sX m (pluriformCoeff sX (∑ j, a j • t j) (c i).U (c i).z))
    (fun a => (lowerSemicontinuous_pluriformDensity sX m _).measurable) w ?_
    (fun j => ((hle _ i).trans_lt (hfin _)))
  refine ae_restrict_of_ae ?_
  have hreg := ae_all_iff.2 fun j => (c i).ae_regular hm (t j)
  filter_upwards [hreg] with y hy a
  rw [hcoeff a, pluriformDensity_sum sX m y φ a (fun j => (hy j).choose)
    (fun j => (hy j).choose_spec.choose) (fun j => (hy j).choose_spec.choose_spec.choose)
    (fun j => (hy j).choose_spec.choose_spec.choose_spec.choose)
    (fun j => (hy j).choose_spec.choose_spec.choose_spec.choose_spec)]
  congr 4
  funext j
  simp only [w, φ, dif_pos (hy j)]

end Decomposition

end Continuity

/-! ### Birational invariance of the total mass -/

section Pullback

attribute [local instance] complexBorel borelSpace_complexPoints

variable {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {n m : ℕ}

/-- A complex point landing in the image of an open immersion `j` is realized from the source. -/
private lemma mem_range_realize_of_mem {U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (x : ComplexPoints sX) (q : Spec (.of ℂ)) (hq : x.hom.base q ∈ Set.range j.base) :
    x ∈ Set.range (realize (sX := j ≫ sX) j rfl) := by
  have H : Set.range x.hom.base ⊆ Set.range j.base := by
    rintro _ ⟨q', rfl⟩
    rwa [Subsingleton.elim q' q]
  refine ⟨⟨IsOpenImmersion.lift j x.hom H, ?_⟩, ComplexPoints.ext ?_⟩
  · rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact x.2
  · exact IsOpenImmersion.lift_fac j x.hom H

/-- The complex points outside the image of an open immersion from a nonempty scheme are
`μ_s`-null, so the image carries the total mass. -/
private lemma gluedMeasure_range_realize [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) (s : RationalPluriForms sX n m)
    {U : Scheme.{0}} [Nonempty U] (j : U ⟶ X) [IsOpenImmersion j] :
    gluedMeasure hm s (Set.range (realize (sX := j ≫ sX) j rfl)) = gluedMeasure hm s Set.univ := by
  set R := Set.range (realize (sX := j ≫ sX) j rfl)
  have hZ : IsClosed (Set.range j.base)ᶜ := j.isOpenEmbedding.isOpen_range.isClosed_compl
  have hZne : (Set.range j.base)ᶜ ≠ Set.univ := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    exact fun h => (Set.eq_univ_iff_forall.1 h (j.base u)) ⟨u, rfl⟩
  have hnull := ((ComplexPoints.measure_proper_closed_null_and_pos_of_isGlued sX hm s).2 _
    (isGlued_gluedMeasure hm s)).1 _ hZ hZne
  have hc : gluedMeasure hm s Rᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) hnull
    rintro _ ⟨q, rfl⟩ hq
    exact hx (mem_range_realize_of_mem j x q hq)
  exact measure_congr (ae_eq_univ.mpr hc)

/-- **The total mass is preserved under pull-back along a dominant open immersion.** -/
private lemma gluedMeasure_univ_pullback_of_isOpenImmersion [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) (s : RationalPluriForms sX n m)
    {U : Scheme.{0}} [IsIntegral U] (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [AlgebraicGeometry.IsVariety ℂ (j ≫ sX)] [SmoothOfRelativeDimension n (j ≫ sX)] :
    gluedMeasure hm (pullbackRationalPluriForms sX j s) Set.univ = gluedMeasure hm s Set.univ := by
  have h := ComplexPoints.map_realize_eq_restrict_of_isOpenImmersion sX hm s j _ _
    (isGlued_gluedMeasure hm s) (isGlued_gluedMeasure hm (pullbackRationalPluriForms sX j s))
  have h1 := congrArg (fun μ : Measure (ComplexPoints sX) => μ Set.univ) h
  rw [Measure.map_apply (continuous_realize j rfl).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h1
  rw [h1, gluedMeasure_range_realize hm s j]

/-- The total mass depends on the structure morphism only through its value. -/
private lemma gluedMeasure_univ_congr {Y : Scheme.{0}} [IsIntegral Y] {t₁ t₂ : Y ⟶ Spec (.of ℂ)}
    (e : t₁ = t₂) [AlgebraicGeometry.IsVariety ℂ t₁] [SmoothOfRelativeDimension n t₁]
    [AlgebraicGeometry.IsVariety ℂ t₂] [SmoothOfRelativeDimension n t₂] (hm : 0 < m)
    (τ₁ : RationalPluriForms t₁ n m) (τ₂ : RationalPluriForms t₂ n m)
    (h : cast (congrArg (fun t => RationalPluriForms t n m) e) τ₁ = τ₂) :
    gluedMeasure hm τ₁ Set.univ = gluedMeasure hm τ₂ Set.univ := by
  subst e
  subst h
  rfl

/-- `Spec ℂ(X) ⟶ X ⟶ Spec ℂ` is `Spec` of the `ℂ`-algebra structure of `ℂ(X)`. -/
private lemma fromSpecStalk_genericPoint_comp :
    X.fromSpecStalk (genericPoint X) ≫ sX =
      Spec.map (CommRingCat.ofHom
        (@algebraMap ℂ X.functionField _ _ (functionFieldAlgebra sX))) := by
  rw [MMP.fromSpecStalk_comp_eq]
  rfl

/-- An open immersion of integral schemes induces an isomorphism of function fields. -/
private lemma bijective_functionFieldMap_of_isOpenImmersion {V Y : Scheme.{0}} [IsIntegral V]
    [IsIntegral Y] (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] :
    Function.Bijective (functionFieldMap j) :=
  ConcreteCategory.bijective_of_isIso
    ((Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant j).symm)).hom ≫
      j.stalkMap (genericPoint V))

/-- Pull-back of rational pluriforms along a dominant morphism `j` is the pluriform pull-back
along any `ℂ`-homomorphism of function fields agreeing with `j^*`. -/
private lemma cast_pullbackRationalPluriForms_eq {U : Scheme.{0}} [IsIntegral U]
    (t : U ⟶ Spec (.of ℂ)) (j : U ⟶ X) [IsDominant j] (e : j ≫ sX = t)
    (φ : FunctionFieldHom t sX) (hφ : ∀ a, φ a = functionFieldMap j a)
    (s : RationalPluriForms sX n m) :
    cast (congrArg (fun t => RationalPluriForms t n m) e) (pullbackRationalPluriForms sX j s) =
      pluriformPullback t sX φ n m s := by
  subst e
  obtain ⟨r, hc⟩ := φ
  have hr : r = functionFieldMap j := RingHom.ext hφ
  subst hr
  rfl

/-- A dominant morphism of finite type between integral schemes inducing an isomorphism of
function fields is an open immersion on a nonempty open of the source. -/
private lemma exists_isOpenImmersion_of_bijective_functionFieldMap {V Y : Scheme.{0}}
    [IsIntegral V] [IsIntegral Y] (f : V ⟶ Y) [IsDominant f] [LocallyOfFiniteType f]
    (hbij : Function.Bijective (functionFieldMap f)) :
    ∃ U : V.Opens, Nonempty U ∧ IsOpenImmersion (U.ι ≫ f) := by
  let e := Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)
  haveI : IsIso (e.hom ≫ f.stalkMap (genericPoint V)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (f.stalkMap (genericPoint V)) := IsIso.of_isIso_comp_left e.hom _
  have hbir : AlgebraicGeometry.IsBirational f := by
    rw [isBirational_iff]
    simp only [genericPoints_eq_singleton, Set.bijOn_singleton, Set.mem_singleton_iff, forall_eq]
    exact ⟨map_genericPoint_of_isDominant f, inferInstance⟩
  haveI : Finite (irreducibleComponents V) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, W, hUW, hU, -, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational f hbir
    (Or.inl ⟨inferInstance, inferInstance⟩)
  refine ⟨U, hU.nonempty.to_subtype, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hUW]
  infer_instance

/-- **A birational self-map is an isomorphism between dense opens.** For a `ℂ`-automorphism `σ`
of `ℂ(X)` there are an integral `U` and dominant open immersions `j₁ j₂ : U ⟶ X` over `ℂ` with
`j₂^* = j₁^* ∘ σ` on function fields: `Spec σ : Spec ℂ(X) ⟶ X` spreads out to a morphism on an
open `D ∋ η`, which is birational and hence an isomorphism between dense opens. -/
private theorem exists_isOpenImmersion_functionFieldMap_eq [AlgebraicGeometry.IsVariety ℂ sX]
    (σ : FunctionFieldEquiv sX sX) :
    letI := functionFieldAlgebra sX
    ∃ (U : Scheme.{0}) (_ : IsIntegral U) (j₁ j₂ : U ⟶ X) (_ : IsOpenImmersion j₁)
      (_ : IsOpenImmersion j₂) (_ : IsDominant j₁) (_ : IsDominant j₂),
      j₂ ≫ sX = j₁ ≫ sX ∧
        functionFieldMap j₂ = (functionFieldMap j₁).comp σ.toRingEquiv.toRingHom := by
  letI := functionFieldAlgebra sX
  have hα : (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      X.fromSpecStalk (genericPoint X)) ≫ sX = X.fromSpecStalk (genericPoint X) ≫ sX := by
    rw [Category.assoc, fromSpecStalk_genericPoint_comp, ← Spec.map_comp]
    congr 1
    ext c
    exact σ.commutes c
  let P := Scheme.PartialMap.ofFromSpecStalk sX sX _ hα
  have hη : genericPoint X ∈ P.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sX _ hα
  have hP : P.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ P.hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ X.fromSpecStalk (genericPoint X) :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sX _ hα
  have hPs : P.hom ≫ sX = P.domain.ι ≫ sX := Scheme.PartialMap.ofFromSpecStalk_comp sX sX _ hα
  haveI : Nonempty P.domain := ⟨⟨_, hη⟩⟩
  haveI : IsIntegral P.domain.toScheme := isIntegral_of_isOpenImmersion P.domain.ι
  haveI : IsDominant P.domain.ι :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion P.domain.ι
  have hpt : P.domain.fromSpecStalkOfMem (genericPoint X) hη (IsLocalRing.closedPoint _) =
      ⟨genericPoint X, hη⟩ := by
    apply Subtype.ext
    change (P.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ P.domain.ι)
      (IsLocalRing.closedPoint _) = _
    rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
  have hgen : P.hom ⟨genericPoint X, hη⟩ = genericPoint X := by
    have e := congr($hP (IsLocalRing.closedPoint X.functionField))
    change P.hom (P.domain.fromSpecStalkOfMem (genericPoint X) hη
        (IsLocalRing.closedPoint _)) = X.fromSpecStalk (genericPoint X)
        (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)
          (IsLocalRing.closedPoint X.functionField)) at e
    haveI : Subsingleton (Spec X.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
    rwa [hpt, Subsingleton.elim (Spec.map _ (IsLocalRing.closedPoint X.functionField))
        (IsLocalRing.closedPoint X.functionField), Scheme.fromSpecStalk_closedPoint] at e
  haveI : IsDominant P.hom := ⟨Dense.mono
    (Set.singleton_subset_iff.mpr (Set.mem_range.mpr ⟨_, hgen⟩))
    (by
      rw [dense_iff_closure_eq]
      exact (genericPoint_spec X).def)⟩
  have key : ∀ (V : Scheme.{0}) [IsIntegral V] (a : V ⟶ P.domain.toScheme) (g₁ g₂ : V ⟶ X)
      [IsDominant g₁] [IsDominant g₂], a ≫ P.domain.ι = g₁ → a ≫ P.hom = g₂ →
      functionFieldMap g₂ = (functionFieldMap g₁).comp σ.toRingEquiv.toRingHom := by
    intro V _ a g₁ g₂ _ _ h₁ h₂
    have ha : V.fromSpecStalk (genericPoint V) ≫ a =
        Spec.map (CommRingCat.ofHom (functionFieldMap g₁)) ≫
          P.domain.fromSpecStalkOfMem (genericPoint X) hη := by
      rw [← cancel_mono P.domain.ι, Category.assoc, h₁, Category.assoc,
        Scheme.Opens.fromSpecStalkOfMem_ι, functionFieldMap_fromSpecStalk]
    have h : Spec.map (CommRingCat.ofHom (functionFieldMap g₂)) ≫
          X.fromSpecStalk (genericPoint X) =
        Spec.map (CommRingCat.ofHom ((functionFieldMap g₁).comp σ.toRingEquiv.toRingHom)) ≫
          X.fromSpecStalk (genericPoint X) := by
      rw [functionFieldMap_fromSpecStalk, ← h₂, ← Category.assoc, ha, CommRingCat.ofHom_comp,
        Spec.map_comp, Category.assoc, Category.assoc, hP]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp h))
  have hbij : Function.Bijective (functionFieldMap P.hom) := by
    rw [key P.domain (𝟙 _) P.domain.ι P.hom (Category.id_comp _) (Category.id_comp _)]
    exact (bijective_functionFieldMap_of_isOpenImmersion P.domain.ι).comp σ.bijective
  haveI : LocallyOfFiniteType (P.hom ≫ sX) := hPs ▸ inferInstance
  haveI : LocallyOfFiniteType P.hom := LocallyOfFiniteType.of_comp (g := sX) ‹_›
  obtain ⟨U, _, _⟩ := exists_isOpenImmersion_of_bijective_functionFieldMap P.hom hbij
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  haveI : IsDominant (U.ι ≫ P.domain.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant (U.ι ≫ P.hom) := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  refine ⟨U, inferInstance, U.ι ≫ P.domain.ι, U.ι ≫ P.hom, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [Category.assoc, hPs, Category.assoc], ?_⟩
  exact key U U.ι _ _ rfl rfl

/-- **Birational invariance of the total mass.** A birational self-map `σ` of `X` is an
isomorphism between dense opens, whose complements are `μ`-null, so `μ_{σ^* s}(X^an) =
μ_s(X^an)`. -/
private theorem measure_univ_pullback [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hm : 0 < m) (σ : FunctionFieldEquiv sX sX)
    (s : RationalPluriForms sX n m) :
    gluedMeasure hm (pluriformPullback sX sX σ.toHom n m s) Set.univ =
      gluedMeasure hm s Set.univ := by
  obtain ⟨U, hU, j₁, j₂, h₁, h₂, hd₁, hd₂, e, hff⟩ := exists_isOpenImmersion_functionFieldMap_eq σ
  haveI : AlgebraicGeometry.IsVariety ℂ (j₁ ≫ sX) := by
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : CompactSpace X := by
      rw [← isCompact_univ_iff, ← Set.preimage_univ (f := sX.base)]
      exact QuasiCompact.isCompact_preimage _ isOpen_univ isCompact_univ
    haveI : IsNoetherian X := ⟨⟩
    exact { }
  haveI : SmoothOfRelativeDimension n (j₁ ≫ sX) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := n) j₁ sX
    rwa [zero_add] at this
  haveI : AlgebraicGeometry.IsVariety ℂ (j₂ ≫ sX) := e ▸ inferInstance
  haveI : SmoothOfRelativeDimension n (j₂ ≫ sX) := e ▸ inferInstance
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n sX
  have hUd := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n (j₁ ≫ sX)
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (j₁ ≫ sX)
  let φ₁ : FunctionFieldHom (j₁ ≫ sX) sX :=
    { functionFieldMap j₁ with
      commutes' := fun c => by
        letI := functionFieldMapAlgebra j₁
        haveI := isScalarTower_functionFieldMap sX j₁
        exact (IsScalarTower.algebraMap_apply ℂ X.functionField U.functionField c).symm }
  have h : cast (congrArg (fun t => RationalPluriForms t n m) e)
      (pullbackRationalPluriForms sX j₂ s) =
        pullbackRationalPluriForms sX j₁ (pluriformPullback sX sX σ.toHom n m s) := by
    rw [cast_pullbackRationalPluriForms_eq (j₁ ≫ sX) j₂ e (φ₁.comp σ.toHom)
      (fun a => by rw [hff]; rfl) s]
    have h1 := cast_pullbackRationalPluriForms_eq (j₁ ≫ sX) j₁ rfl φ₁ (fun _ => rfl)
      (pluriformPullback sX sX σ.toHom n m s)
    rw [cast_eq] at h1
    rw [h1, pluriformPullback_comp hUd hX hX]
  rw [← gluedMeasure_univ_pullback_of_isOpenImmersion hm s j₂,
    ← gluedMeasure_univ_pullback_of_isOpenImmersion hm (pluriformPullback sX sX σ.toHom n m s) j₁]
  exact (gluedMeasure_univ_congr e hm _ _ h).symm

end Pullback

/-! ### The gauge -/

section Gauge

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {B : QDivisor X} {m : ℕ}

attribute [local instance] complexBorel borelSpace_complexPoints

private lemma smoothOfRelativeDimension_of_isSNCSubboundaryPair (hn : topologicalKrullDim X = n)
    (hXB : IsSNCSubboundaryPair sX B) : SmoothOfRelativeDimension n sX := by
  haveI := hXB.isProjectiveVariety.toIsVariety
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hXB.isSmoothScheme
  exact MMP.Intersection.smoothOfRelativeDimension_of_isVariety sX n hn

/-- The gauge `p(s) = μ_s(X^an) = ∫_X |s|^{2/m}`. -/
private noncomputable def gauge (hn : topologicalKrullDim X = n) (hXB : IsSNCSubboundaryPair sX B)
    (hm : 0 < m) (s : logPluricanonicalSections sX n m B) : ℝ :=
  haveI := hXB.isProjectiveVariety.toIsVariety
  haveI := smoothOfRelativeDimension_of_isSNCSubboundaryPair hn hXB
  (gluedMeasure hm (s : RationalPluriForms sX n m) Set.univ).toReal

/-- A section of `m(K_X + B)` has poles bounded by `mB`. -/
private lemma ordForm_add_nonneg (s : logPluricanonicalSections sX n m B)
    (hs : (s : RationalPluriForms sX n m) ≠ 0) (E : MMP.Mori.PrimeDivisor X) :
    0 ≤ (E.ordForm (s : RationalPluriForms sX n m) : ℚ) + m * B.coeff E := by
  have hE : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have h := s.2.2 E ⟨E.genericPoint, hE, trivial⟩ hs
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h
  have h2 : ((⌊((m : ℤ) • B.coeff E : ℚ)⌋ : ℤ) : ℚ) ≤ m * B.coeff E := by
    simpa [zsmul_eq_mul] using Int.floor_le ((m : ℤ) • B.coeff E : ℚ)
  have h3 : (0 : ℚ) ≤ (E.ordForm (s : RationalPluriForms sX n m) : ℚ) +
      ((⌊((m : ℤ) • B.coeff E : ℚ)⌋ : ℤ) : ℚ) := by exact_mod_cast h
  linarith

private lemma gluedMeasure_univ_lt_top_of_mem [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1)
    (hm : 0 < m) (s : logPluricanonicalSections sX n m B) :
    gluedMeasure hm (s : RationalPluriForms sX n m) Set.univ < ⊤ := by
  by_cases hs : (s : RationalPluriForms sX n m) = 0
  · rw [hs, gluedMeasure_zero]
    simp
  · exact gluedMeasure_univ_lt_top hXB.isProjectiveVariety B hXB.isSNC hB hm _
      (ordForm_add_nonneg s hs)

variable (hn : topologicalKrullDim X = n) (hXB : IsSNCSubboundaryPair sX B)
  (hB : ∀ P, B.coeff P < 1) (hm : 0 < m)

include hn hXB in
/-- `V = H⁰(X, m(K_X + B))` is finite-dimensional: it is `H⁰` of the coherent sheaf
`𝒪_X(mK_X + ⌊mB⌋)` on the proper variety `X`. -/
theorem finite_logPluricanonicalSections :
    Module.Finite ℂ (logPluricanonicalSections sX n m B) := by
  letI := functionFieldAlgebra sX
  haveI := hXB.isProjectiveVariety.toIsVariety
  have hX := hXB.isProjectiveVariety
  haveI : IsProper sX := inferInstance
  haveI : LocallyOfFiniteType sX := inferInstance
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨bT⟩ := exists_basis_topForms (sX := sX) hn
  let bb : Module.Basis Unit X.functionField (RationalPluriForms sX n m) :=
    ZTensorPower.basis bT (m : ℤ)
  set ω₀ : RationalPluriForms sX n m := bb ()
  have hω₀0 : ω₀ ≠ 0 := bb.ne_zero ()
  let coord : RationalPluriForms sX n m →ₗ[X.functionField] X.functionField :=
    (Finsupp.lapply ()) ∘ₗ bb.repr.toLinearMap
  have hcoord : ∀ τ, τ = coord τ • ω₀ := fun τ => (basis_unit_repr_smul bb τ).symm
  set D : Divisor X := divisorOfForm ω₀ + DivisorWithCoeffs.roundDown ((m : ℤ) • B) with hD
  have hDc : D.IsCartier := isCartier_of_isSmoothScheme hXB.isSmoothScheme D
  letI : Module ℂ (D.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections ℂ sX)
  haveI := finiteDimensional_sections sX D hDc
  let e := rationalFunctionsEquivFunctionField X
  let toRF : X.functionField → ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤)) :=
    fun f => (rationalFunctionsPresheafTopEquiv X).symm (e.symm f)
  have hmem : ∀ τ ∈ logPluricanonicalSections sX n m B,
      toRF (coord τ) ∈ D.divisorialSubmodule ⊤ := by
    intro τ hτ E _
    change E.OrdGE (-D.coeff E) (e.symm (coord τ) E.component)
    rw [ordGE_iff]
    by_cases hf : coord τ = 0
    · exact Or.inl hf
    right
    have hτ0 : τ ≠ 0 := fun h => hf (by rw [h, map_zero])
    have hE : (E.support ∩ (⊤ : X.Opens)).Nonempty :=
      ⟨E.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl, trivial⟩
    have h1 := hτ.2 E hE hτ0
    have h2 : E.ordForm τ = X.ord (coord τ) E.genericPoint + E.ordForm ω₀ := by
      conv_lhs => rw [hcoord τ]
      exact E.ordForm_smul_of_topologicalKrullDim_eq hn hf hω₀0
    have h3 : D.coeff E = E.ordForm ω₀ +
        (DivisorWithCoeffs.roundDown ((m : ℤ) • B)).coeff E := by
      rw [hD]
      simp [DivisorWithCoeffs.coeff_apply]
      rfl
    omega
  let L : logPluricanonicalSections sX n m B →ₗ[ℂ] D.divisorialSubmodule ⊤ :=
    { toFun := fun τ => ⟨toRF (coord τ), hmem τ τ.2⟩
      map_add' := fun a b => Subtype.ext (by
        simp only [Submodule.coe_add, map_add, toRF])
      map_smul' := fun c a => Subtype.ext (by
        change toRF (coord (algebraMap ℂ X.functionField c • (a : RationalPluriForms sX n m))) =
          scalarsToGlobalSections ℂ sX c • toRF (coord a)
        rw [map_smul, smul_eq_mul]
        funext Z
        rw [rationalFunctions_smul_apply]
        change e.symm (algebraMap ℂ X.functionField c * coord a) Z.1 = _ * e.symm (coord a) Z.1
        rw [map_mul]
        change e.symm (algebraMap ℂ X.functionField c) Z.1 * _ = _
        congr 1
        exact germ_eq_rationalFunctionsEquivFunctionField_symm ⊤
          (scalarsToGlobalSections ℂ sX c) trivial Z.1 Z.2) }
  have hL : Function.Injective L := by
    intro a b hab
    have h1 : toRF (coord a) = toRF (coord b) := congrArg Subtype.val hab
    have h2 : coord a = coord b := e.symm.injective
      ((rationalFunctionsPresheafTopEquiv X).symm.injective h1)
    exact Subtype.ext (by rw [hcoord (a : RationalPluriForms sX n m),
      hcoord (b : RationalPluriForms sX n m), h2])
  exact Module.Finite.of_injective L hL

include hB in
/-- The gauge is continuous along every finite family: `a ↦ p(∑ aⱼ sⱼ)` is continuous on `ℂᵏ`
(the densities of `∑ aⱼ sⱼ` are dominated by a constant times `∑ |sⱼ|^{2/m}`, each integrable,
and dominated convergence applies). -/
private theorem continuous_gauge_sum {k : ℕ} (t : Fin k → logPluricanonicalSections sX n m B) :
    Continuous fun a : Fin k → ℂ ↦ gauge hn hXB hm (∑ j, a j • t j) := by
  haveI := hXB.isProjectiveVariety.toIsVariety
  haveI := smoothOfRelativeDimension_of_isSNCSubboundaryPair hn hXB
  have hcoe : ∀ a : Fin k → ℂ, ((∑ j, a j • t j : logPluricanonicalSections sX n m B) :
      RationalPluriForms sX n m) = ∑ j, a j • (t j : RationalPluriForms sX n m) := fun a => by
    rw [Submodule.coe_sum]
    rfl
  have h := continuous_gluedMeasure_univ_sum hXB.isProjectiveVariety hm
    (fun j => (t j : RationalPluriForms sX n m)) fun a => by
      rw [← hcoe]
      exact gluedMeasure_univ_lt_top_of_mem hXB hB hm _
  convert h using 2 with a
  simp only [gauge, hcoe]

include hB in
/-- Continuity: `V` is finite-dimensional, so its module topology is that of `ℂᵏ` through a
basis, along which the gauge is continuous. -/
private theorem continuous_gauge :
    letI := functionFieldAlgebra sX
    @Continuous _ _ (moduleTopology ℂ _) _ (gauge hn hXB hm) := by
  letI := functionFieldAlgebra sX
  letI : TopologicalSpace (logPluricanonicalSections sX n m B) := moduleTopology ℂ _
  haveI : IsModuleTopology ℂ (logPluricanonicalSections sX n m B) := ⟨rfl⟩
  haveI := finite_logPluricanonicalSections (sX := sX) (B := B) (m := m) hn hXB
  let b := Module.finBasis ℂ (logPluricanonicalSections sX n m B)
  have hc : Continuous (b.equivFun : logPluricanonicalSections sX n m B → _) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap)
  have h := (continuous_gauge_sum hn hXB hB hm b).comp hc
  convert h using 1
  funext s
  simp only [Function.comp_apply, Module.Basis.equivFun_apply]
  rw [Module.Basis.sum_repr]

include hB in
/-- A nonzero section has a glued measure charging the nonempty space `X^an`. -/
private theorem gauge_pos (s : logPluricanonicalSections sX n m B) (hs : s ≠ 0) :
    0 < gauge hn hXB hm s := by
  haveI := hXB.isProjectiveVariety.toIsVariety
  haveI := smoothOfRelativeDimension_of_isSNCSubboundaryPair hn hXB
  haveI := nonempty_complexPoints (sX := sX)
  have hs' : (s : RationalPluriForms sX n m) ≠ 0 := fun h ↦ hs (Subtype.ext h)
  exact ENNReal.toReal_pos
    (gluedMeasure_pos hm _ hs' isOpen_univ Set.univ_nonempty).ne'
    (gluedMeasure_univ_lt_top_of_mem hXB hB hm s).ne

/-- Scalar homogeneity: `μ_{cs} = |c|^{2/m} μ_s`. -/
private theorem gauge_smul (c : ℂ) (s : logPluricanonicalSections sX n m B) :
    letI := functionFieldAlgebra sX
    gauge hn hXB hm (c • s) = ‖c‖ ^ (2 / m : ℝ) * gauge hn hXB hm s := by
  haveI := hXB.isProjectiveVariety.toIsVariety
  haveI := smoothOfRelativeDimension_of_isSNCSubboundaryPair hn hXB
  simp only [gauge]
  rw [Submodule.coe_smul, gluedMeasure_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- Invariance under a birational self-map. -/
private theorem gauge_pullback :
    letI := functionFieldAlgebra sX
    ∀ σ : FunctionFieldEquiv sX sX,
      ∀ hσ : ∀ s ∈ logPluricanonicalSections sX n m B,
        pluriformPullback sX sX σ.toHom n m s ∈ logPluricanonicalSections sX n m B,
      ∀ s : logPluricanonicalSections sX n m B,
        gauge hn hXB hm ⟨_, hσ s s.2⟩ = gauge hn hXB hm s := by
  intro σ hσ s
  haveI := hXB.isProjectiveVariety.toIsVariety
  haveI := smoothOfRelativeDimension_of_isSNCSubboundaryPair hn hXB
  simp only [gauge]
  rw [measure_univ_pullback hm σ]

omit hn hXB hB hm in

/-- **The invariant integrable gauge on subklt pluriforms.** Let `X` be a smooth projective complex
variety of dimension `n`, `B` an snc `ℚ`-divisor with every coefficient less than one, and
`m > 0` with `mB` integral. On `V = H⁰(X, m(K_X + B))` (`MMP.Fourfold.logPluricanonicalSections`)
there is a function `p`, the integral `p(s) = ∫_X |s|^{2/m}`, which is finite, continuous,
positive off zero, satisfies `p(cs) = |c|^{2/m} p(s)`, and is preserved by every birational
self-map whose pluriform pull-back preserves `V`. Here `p(s)` is the total mass `μ_s(X^an)` of the
measure `μ_s` on `X^an` glued from the chart measures of `s`
(`MMP.Analytic.ComplexPoints.pluriformChartMeasure`): `ENNReal.ofReal (p s) = μ Set.univ` for
every measure `μ` whose restriction to every étale chart is the chart measure of `s` there. -/
@[mmp "lem_fourfold_subklt_pluriform_integrable_gauge"]
public theorem exists_gauge_logPluricanonicalSections
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} (hn : topologicalKrullDim X = n) {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1)
    {m : ℕ} (hm : 0 < m) (hmB : ∀ P, ∃ a : ℤ, (m : ℚ) * B.coeff P = a) :
    letI := functionFieldAlgebra sX
    ∃ p : logPluricanonicalSections sX n m B → ℝ,
      @Continuous _ _ (moduleTopology ℂ _) _ p ∧
      (∀ s, s ≠ 0 → 0 < p s) ∧
      (∀ (c : ℂ) s, p (c • s) = ‖c‖ ^ (2 / m : ℝ) * p s) ∧
      (∀ σ : FunctionFieldEquiv sX sX,
        ∀ hσ : ∀ s ∈ logPluricanonicalSections sX n m B,
          pluriformPullback sX sX σ.toHom n m s ∈ logPluricanonicalSections sX n m B,
        ∀ s : logPluricanonicalSections sX n m B, p ⟨_, hσ s s.2⟩ = p s) ∧
      ∀ s : logPluricanonicalSections sX n m B,
        haveI : AlgebraicGeometry.IsVariety ℂ sX := hXB.isProjectiveVariety.toIsVariety
        haveI : SmoothOfRelativeDimension n sX :=
          haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hXB.isSmoothScheme
          MMP.Intersection.smoothOfRelativeDimension_of_isVariety sX n hn
        letI : MeasurableSpace (ComplexPoints sX) := borel _
        ∀ μ : MeasureTheory.Measure (ComplexPoints sX),
          (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
            (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
              (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
            (W : Set (ComplexPoints sX)) (hW : W ⊆ ComplexPoints.chart U) (hWo : IsOpen W)
            (hWz : Topology.IsOpenEmbedding
              (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩)),
            μ.restrict W = ComplexPoints.pluriformChartMeasure sX hm
              (s : RationalPluriForms sX n m) U z hz W hW hWo hWz) →
          ENNReal.ofReal (p s) = μ Set.univ := by
  letI := functionFieldAlgebra sX
  refine ⟨gauge hn hXB hm, continuous_gauge hn hXB hB hm,
    gauge_pos hn hXB hB hm, gauge_smul hn hXB hm, gauge_pullback hn hXB hm, fun s μ hμ => ?_⟩
  haveI := hXB.isProjectiveVariety.toIsVariety
  haveI := smoothOfRelativeDimension_of_isSNCSubboundaryPair hn hXB
  rw [gauge, ENNReal.ofReal_toReal (gluedMeasure_univ_lt_top_of_mem hXB hB hm s).ne]
  congr 1
  exact (ComplexPoints.pluriformChartMeasure_intrinsic sX hm _).2.1.unique
    (isGlued_gluedMeasure hm _) hμ

end Gauge

end MMP.Fourfold

end
