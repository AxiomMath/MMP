module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalization
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.HomotopyPointGeneric
public import MMP.AlgebraicTopology.BorelMoore.Suspension
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AgreesSubmanifoldRank
public import MMP.AlgebraicGeometry.Analytic.DivisorOrientationDatum
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.CupCompositeGeneric
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionNormalize
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksAgreesSubmanifoldStalk
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyInfra

/-!
# A section of a rank-one bundle cutting out a point of a smooth curve

Let `T` be a smooth complex curve, `t ∈ T(ℂ)` and `σ` a section of a rank-one bundle `𝐕(ℰ) ⟶ T`
whose zero scheme is the reduced point `t`. Then `σ⁻¹(0) = {t}` on `ℂ`-points, `σ` has a simple
zero at `t`, and `σ^*(u_ℰ)` is the local orientation class of the complex curve `T(ℂ)` at `t`
(Fulton, proof of Lemma 19.1.3).

## Main results

* `MMP.Modules.preimage_mapFun_range_zeroSection_eq_singleton`: `σ⁻¹(0(T(ℂ))) = {t}`.
* `MMP.Modules.injective_chartDeriv_chartLocalCoord`: a section cutting out a point of a curve has
  a simple zero.
* `MMP.Modules.isLocalOrientationClass_forget_pullback_thomClass`: `σ^*(u_ℰ)` is the local
  orientation class of the curve at the point `σ` cuts out.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open MMP.UnderlyingSpace

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace MMP.Modules

open MMP AlgebraicGeometry.SheafOfModules

section Point

open Finsupp MMP.SingularChain MMP.SingularCochain MMP.FundamentalClass MMP.ThomClass

variable {T : Scheme.{0}} [T.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))]
  {E : T.Modules} [E.IsQuasicoherent] (σ : T ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]
  (t : UnderlyingSpace ℂ T)

/-- **`σ⁻¹(0(T(ℂ))) = {t}`** for a section `σ` whose zero scheme is the point `t`. -/
theorem preimage_mapFun_range_zeroSection_eq_singleton (hz : zeroLocus E σ = t.toHom.ker) :
    mapFun σ ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) = {t} := by
  rw [preimage_mapFun_range_zeroSection, hz, Scheme.Hom.support_ker,
    t.toHom.isClosedEmbedding.isClosed_range.closure_eq, ← range_map_of_isClosedImmersion,
    range_map_toHom]

/-- `σ⁻¹(0(T(ℂ))) ⊆ {t}`, as subsets of the topological space `T(ℂ)`. -/
theorem preimage_ofHom_range_zeroSection_subset_singleton (hz : zeroLocus E σ = t.toHom.ker) :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) ⊆
      ({t} : Set (UnderlyingSpace ℂ T)) := fun _ hp ↦
  (preimage_mapFun_range_zeroSection_eq_singleton σ t hz).subset hp

variable [IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1] {σ}

omit [IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1] in
/-- The local coordinate of `σ` in a chart around `t` vanishes at `t`, for a section `σ` whose zero
scheme is the point `t`. -/
lemma evalExt_chartLocalCoord_eq_zero (hσ : σ ≫ proj E = 𝟙 T) (hz : zeroLocus E σ = t.toHom.ker)
    (c : Chart E 1) (hc : t ∈ chartBase c) :
    evalExt c.1.1 (chartLocalCoord σ hσ c) t = 0 := by
  rw [show evalExt c.1.1 (chartLocalCoord σ hσ c) t = coord c (mapFun σ t) 0 from
    (evalExt_of_le _ hc).trans (eval_sectionCoord σ c _ t hc 0)]
  have hmem : mapFun σ t ∈ range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) :=
    (preimage_mapFun_range_zeroSection_eq_singleton σ t hz).ge rfl
  have hp : mapFun σ t ∈ chartTotalOpens c := by
    change mapFun (proj E) (mapFun σ t) ∈ chartBase c
    rw [mapFun_proj_mapFun_of_comp_eq_id σ hσ]
    exact hc
  exact congrFun ((mem_range_zeroSection_iff_coord_eq_zero c _ hp).1 hmem) 0

/-- **A section cutting out a point of a curve has a simple zero**: if the zero scheme of a section
`σ` of a rank-one bundle `𝐕(ℰ)` on a smooth curve `T` is the point `t`, then in every algebraic
chart `e` at `t` the differential at `t` of the local coordinate `σ^♯b` of `σ` is injective. -/
theorem injective_chartDeriv_chartLocalCoord (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ)))
    (hσ : σ ≫ proj E = 𝟙 T) (hz : zeroLocus E σ = t.toHom.ker)
    {e : OpenPartialHomeomorph (UnderlyingSpace ℂ T) (EuclideanSpace ℂ (Fin 1))}
    (he : IsAlgebraicChart e) (ht : t ∈ e.source) (c : Chart E 1) (hc : t ∈ chartBase c) :
    Function.Injective (chartDeriv e c.1.1 t (chartLocalCoord σ hσ c)) := by
  set a := chartLocalCoord σ hσ c
  have ha0 := evalExt_chartLocalCoord_eq_zero t hσ hz c hc
  obtain ⟨x, hx⟩ : t ∈ range (UnderlyingSpace.map (K := ℂ) t.toHom) := by
    rw [range_map_toHom]
    rfl
  change mapFun t.toHom x = t at hx
  rw [← hx] at ht hc ha0 ⊢
  have hns := isNonsingularPair_toHom (n := 1) t
  have := (hns.regular_Y (mapFun t.toHom x)).1
  have := hns.regular_X x
  have hdim : ringKrullDim (T.presheaf.stalk ((mapFun t.toHom x).toHom
      (IsLocalRing.closedPoint ℂ))) = (1 : ℕ) := by
    rw [(hns.regular_Y (mapFun t.toHom x)).2, finrank_euclideanSpace, Fintype.card_fin]
  have hpx := (top_le_preimage_iff (mapFun t.toHom x) c.1.1).1 hc
  have hx' : x.toHom (IsLocalRing.closedPoint ℂ) ∈ t.toHom ⁻¹ᵁ c.1.1 := hpx
  set y := x.toHom (IsLocalRing.closedPoint ℂ)
  have hpy : t.toHom y ∈ c.1.1 := hpx
  have hK : RingHom.ker (t.toHom.stalkMap y).hom =
      Ideal.span (Set.range fun _ : Fin 1 ↦ T.presheaf.germ c.1.1 (t.toHom y) hpy a) := by
    rw [Stacks.Flatness.ker_stalkMap_eq_map_germ t.toHom c.1.2 (c.1.2.preimage t.toHom) le_rfl
        hx' hpy (by rw [← Scheme.Hom.app_eq_appLE]; exact t.toHom.app_surjective c.1.1 c.1.2),
      ← Scheme.Hom.app_eq_appLE, ← Scheme.Hom.ker_apply, ← hz, ideal_zeroLocus_chart σ hσ c,
      Ideal.map_span, Set.image_singleton, Set.range_const]
  have hreg : IsRegularLocalRing (T.presheaf.stalk ((mapFun t.toHom x).toHom
      (IsLocalRing.closedPoint ℂ)) ⧸
        Ideal.span (Set.range fun _ : Fin 1 ↦ T.presheaf.germ c.1.1 _ hpx a)) :=
    IsRegularLocalRing.of_ringEquiv ((Ideal.quotEquivOfEq hK.symm).trans
      (RingHom.quotientKerEquivOfSurjective (t.toHom.stalkMap_surjective y))).symm
  have hdimq : ringKrullDim (T.presheaf.stalk ((mapFun t.toHom x).toHom
      (IsLocalRing.closedPoint ℂ)) ⧸
        Ideal.span (Set.range fun _ : Fin 1 ↦ T.presheaf.germ c.1.1 _ hpx a)) + (1 : ℕ) =
      (1 : ℕ) := by
    obtain ⟨rs, hlen, hrs, hker⟩ := exists_isRegular_ofList_eq_ker_stalkMap
      (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT t) y
    have : IsNoetherianRing (T.presheaf.stalk (t.toHom y)) :=
      (hns.regular_Y (mapFun t.toHom x)).1.toIsNoetherian
    have key := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hrs
    rw [hker, hK, hlen] at key
    exact key.trans hdim
  have h := finrank_iInf_ker_chartDeriv_add_le (d := 1)
    (by rw [finrank_euclideanSpace, Fintype.card_fin]) he ht c.1.2 hc hdim (fun _ : Fin 1 ↦ a)
    (fun _ ↦ ha0) hreg hdimq
  rw [iInf_const] at h
  exact LinearMap.ker_eq_bot.1 (Submodule.finrank_eq_zero.1 (by omega))

omit [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))] in
/-- On an open `O` where `h` is the local coordinate of `σ`, the class `σ^*(u_ℰ)` is represented,
up to a relative coboundary, by `h^* α₀` for a chart-oriented cocycle `α₀` of `(ℂ, ℂ - 0)`. -/
theorem exists_cochainPullback_sub_mem_relCoboundaries (R : Type) [CommRing R]
    (hσ : σ ≫ proj E = 𝟙 T) (c : Chart E 1)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T)))
    (hO : (O : Set _) ⊆ chartBase c) (h : TopCat.of O ⟶ TopCat.of ℂ)
    (hh : ∀ p : O, h p = coord c (mapFun σ p.1) 0)
    {α : Simplex (TopCat.of (UnderlyingSpace ℂ T)) (2 * 1) → R}
    (hα : α ∈ relCocycles R ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ (2 * 1))
    (hrep : Submodule.Quotient.mk ⟨α, hα⟩ = relativeSingularCohomologyEquiv R
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ (2 * 1)
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
          (thomClass R E 1))) :
    ∃ α₀ : Simplex (TopCat.of ℂ) 2 → R,
      IsChartOrientedCocycle R Complex.basisOneI (0 : TopCat.of ℂ) α₀ ∧
      cochainPullback R (borelMooreHomology.inclHom O) (2 * 1) α - cochainPullback R h 2 α₀ ∈
        relCoboundaries R ((borelMooreHomology.inclHom O).hom ⁻¹'
          ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
            range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))ᶜ (2 * 1) := by
  set S := (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
    range (UnderlyingSpace.map (K := ℂ) (zeroSection E))
  set u := (cohomologyWithSupports.pullback R (ModuleCat.of R R)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom (thomClass R E 1)
  set SO := (borelMooreHomology.inclHom O).hom ⁻¹' S
  obtain ⟨u₀, hu₀⟩ := exists_isLocalOrientationClass (R := R) (T := TopCat.of ℂ)
    (isOrientedAtlas_self ℂ) (n := 2) two_pos Complex.basisOneI (0 : ℂ)
  have key : (relativeSingularCohomology.map R (ModuleCat.of R R) (borelMooreHomology.inclHom O)
      (A' := SOᶜ) (A := Sᶜ) (fun _ hx ↦ hx) (2 * 1 : ℕ)).hom u =
      (relativeSingularCohomology.map R (ModuleCat.of R R) h
        (compl_preimage_inclHom_preimage_subset σ hσ c O hO h hh) (2 : ℕ)).hom
        u₀ := pullback_inclHom_pullback_thomClass R σ hσ c O hO h hh hu₀
  obtain ⟨α₀, hα₀, hc₀, hrep₀⟩ := hu₀
  refine ⟨α₀, hc₀, ?_⟩
  have e1 := relativeSingularCohomologyEquiv_map (g := borelMooreHomology.inclHom O)
    (A' := SOᶜ) (A := Sᶜ) (fun _ hx ↦ hx) (2 * 1) u
  have e2 := relativeSingularCohomologyEquiv_map (g := h) (A' := SOᶜ)
    (A := ({0}ᶜ : Set (TopCat.of ℂ)))
    (compl_preimage_inclHom_preimage_subset σ hσ c O hO h hh) 2 u₀
  have hdiff := congrArg (relativeSingularCohomologyEquiv R SOᶜ (2 * 1)) key
  rw [e1] at hdiff
  erw [e2] at hdiff
  rw [← hrep, hrep₀] at hdiff
  erw [relCohomologyMap_mk, relCohomologyMap_mk, Submodule.Quotient.eq] at hdiff
  exact hdiff

/-- Near the point `t` cut out by `σ`, the pull-back along the local coordinate `h` of `σ` of a
chart-oriented cocycle of `(ℂ, ℂ - 0)` takes the value `1` on small chart simplices around `t`. -/
theorem exists_eval_comp_chartSimplex_eq_one (R : Type) [CommRing R]
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (hσ : σ ≫ proj E = 𝟙 T)
    (hz : zeroLocus E σ = t.toHom.ker)
    {e : OpenPartialHomeomorph (UnderlyingSpace ℂ T) (EuclideanSpace ℂ (Fin 1))}
    (he : IsAlgebraicChart e) (ht : t ∈ e.source) (c : Chart E 1) (hc : t ∈ chartBase c)
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T))) (htO : t ∈ O)
    (h : TopCat.of O ⟶ TopCat.of ℂ)
    (hh : ∀ p : O, h.hom p = evalExt c.1.1 (chartLocalCoord σ hσ c) p.1)
    {α₀ : Simplex (TopCat.of ℂ) 2 → R}
    (hα₀ : IsChartOrientedCocycle R Complex.basisOneI (0 : TopCat.of ℂ) α₀) :
    ∃ v : Fin (2 * 1 + 1) → EuclideanSpace ℂ (Fin 1),
      IsOrientedSimplexAroundZero curveOrientationBasis (fun k ↦ v k - e t) ∧
      range (affineSimplex v) ⊆ e.target ∧ (∀ z, e.symm (affineSimplex v z) ∈ O) ∧
      ∀ σ' : Simplex (TopCat.of O) (2 * 1), (∀ z, (σ' z).1 = e.symm (affineSimplex v z)) →
        SingularCochain.eval α₀ (single (h.hom.comp σ') 1) = 1 := by
  set M := EuclideanSpace ℂ (Fin 1)
  set a := chartLocalCoord σ hσ c
  set F : M → ℂ := fun k ↦ evalExt c.1.1 a (e.symm k)
  set D := chartDeriv e c.1.1 t a
  have hDF : HasFDerivAt F D (e t) := (differentiableAt_evalExt he ht hc a).hasFDerivAt
  have hdet :=
    curveOrientationBasis_det_pos (injective_chartDeriv_chartLocalCoord t hT hσ hz he ht c hc)
  have hF0 : F (e t) = 0 := (congrArg (evalExt c.1.1 a) (e.left_inv ht)).trans
    (evalExt_chartLocalCoord_eq_zero t hσ hz c hc)
  have hWc : e.target ∩ e.symm ⁻¹' chartBase c ∈ nhds (e t) :=
    (e.isOpen_inter_preimage_symm (isOpen_chartBase c)).mem_nhds
      ⟨e.map_source ht, by simpa [e.left_inv ht] using hc⟩
  have hFc : ContinuousOn F (e.target ∩ e.symm ⁻¹' chartBase c) :=
    (continuousOn_evalExt c.1.1 a).comp (e.continuousOn_symm.mono inter_subset_left)
      fun k hk ↦ hk.2
  obtain ⟨δ, hδ, hloc⟩ := isLocallyHomologous_of_hasFDerivAt (X := TopCat.of ℂ)
    curveOrientationBasis Complex.basisOneI isOpen_univ (g := id) continuousOn_id
    (injOn_id _) hWc hFc hF0 (mem_univ _) (hDF.restrictScalars ℝ) hdet
  have hWs : e.target ∩ e.symm ⁻¹' (O : Set (TopCat.of (UnderlyingSpace ℂ T))) ∈ nhds (e t) :=
    (e.isOpen_inter_preimage_symm O.2).mem_nhds
      ⟨e.map_source ht, by rw [mem_preimage, e.left_inv ht]; exact htO⟩
  obtain ⟨v, hv, hvs⟩ := exists_isOrientedSimplexAroundZero_subset curveOrientationBasis
    (e t) (Filter.inter_mem (Metric.ball_mem_nhds _ hδ) hWs)
  obtain ⟨-, hA⟩ := hloc v hv fun z hz ↦ (hvs hz).1
  refine ⟨v, hv, fun z hz ↦ (hvs hz).2.1, fun z ↦ (hvs ⟨z, rfl⟩).2.2, fun σ' hσ' ↦ ?_⟩
  set w : Fin (2 * 1 + 1) → ℂ := fun k ↦ 0 + D (v k - e t)
  have hw : range (affineSimplex w) ⊆ (_root_.chartAt ℂ (0 : TopCat.of ℂ)).target := by
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_target]
    exact subset_univ _
  have hw' : IsOrientedSimplexAroundZero Complex.basisOneI
      (fun k ↦ w k - _root_.chartAt ℂ (0 : TopCat.of ℂ) (0 : TopCat.of ℂ)) := by
    simpa [w, chartAt_self_eq, Function.comp_def] using
      hv.map_linearMap ((D.restrictScalars ℝ : M →L[ℝ] ℂ) : M →ₗ[ℝ] ℂ) hdet
  have hlh := hA (h.hom.comp σ') (chartSimplexOf (_root_.chartAt ℂ (0 : TopCat.of ℂ)) w hw)
    (fun z ↦ (hh (σ' z)).trans (congrArg (evalExt c.1.1 a) (hσ' z))) (fun z ↦ by
      rw [chartSimplexOf_apply, chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
      rfl)
  exact (eval_eq_of_isLocallyHomologous hα₀.1 hlh).trans
    (hα₀.2 _ (chart_mem_atlas _ _) (mem_chart_source _ _) w hw' hw)

omit [IsFiniteLocallyFreeOfRank E 1] in
/-- A cochain of `T(ℂ)` that agrees near `t`, up to a relative coboundary of `(O, O - t)`, with the
pull-back `h^* α₀` of a cochain taking the value `1` on the chart simplex `v` around `t`, takes the
value `1` on that chart simplex too. -/
theorem eval_chartSimplexOf_eq_one_of_sub_mem_relCoboundaries (R : Type) [CommRing R]
    (hz : zeroLocus E σ = t.toHom.ker)
    {e : OpenPartialHomeomorph (TopCat.of (UnderlyingSpace ℂ T)) (EuclideanSpace ℂ (Fin 1))}
    (O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T)))
    (h : TopCat.of O ⟶ TopCat.of ℂ) {v : Fin (2 * 1 + 1) → EuclideanSpace ℂ (Fin 1)}
    (hv : IsOrientedSimplexAroundZero curveOrientationBasis fun k ↦ v k - e t)
    (hvt : range (affineSimplex v) ⊆ e.target) (hvO : ∀ z, e.symm (affineSimplex v z) ∈ O)
    {α : Simplex (TopCat.of (UnderlyingSpace ℂ T)) (2 * 1) → R}
    {α₀ : Simplex (TopCat.of ℂ) 2 → R}
    (hα : cochainPullback R (borelMooreHomology.inclHom O) (2 * 1) α - cochainPullback R h 2 α₀ ∈
      relCoboundaries R ((borelMooreHomology.inclHom O).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))ᶜ (2 * 1))
    (hα₀ : ∀ σ' : Simplex (TopCat.of O) (2 * 1), (∀ z, (σ' z).1 = e.symm (affineSimplex v z)) →
      SingularCochain.eval α₀ (single (h.hom.comp σ') 1) = 1) :
    SingularCochain.eval α (single (chartSimplexOf e v hvt) 1) = 1 := by
  let σO : Simplex (TopCat.of O) (2 * 1) :=
    ⟨fun z ↦ ⟨e.symm (affineSimplex v z), hvO z⟩,
      (e.continuousOn_symm.comp_continuous (affineSimplex v).continuous
        fun z ↦ hvt ⟨z, rfl⟩).subtype_mk _⟩
  have hbd : ∀ z : stdSimplex ℝ (Fin (2 * 1 + 1)), (∃ k, z k = 0) →
      σO z ∈ ((borelMooreHomology.inclHom O).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))))ᶜ := by
    intro z hz' hmem
    have ht : e.symm (affineSimplex v z) = t :=
      (preimage_mapFun_range_zeroSection_eq_singleton σ t hz).subset hmem
    have h₁ : affineSimplex v z = e t := by rw [← ht, e.right_inv (hvt ⟨z, rfl⟩)]
    apply hv.affineSimplex_ne_zero z hz'
    rw [affineSimplex_sub, h₁, sub_self]
  have hzero := eval_single_eq_zero_of_mem_relCoboundaries σO hbd _ hα
  have h₀ := hα₀ σO fun _ ↦ rfl
  have hcomp : (borelMooreHomology.inclHom O).hom.comp σO = chartSimplexOf e v hvt :=
    ContinuousMap.ext fun _ ↦ rfl
  simp only [SingularCochain.eval, linearCombination_single, Pi.sub_apply, smul_eq_mul,
    one_mul] at hzero h₀ ⊢
  rw [← hcomp]
  exact (sub_eq_zero.1 hzero).trans h₀

/-- **The pull-back of the Thom class by a section cutting out a point is the local orientation
class** (Fulton, proof of Lemma 19.1.3). Let `T` be a smooth complex curve, `t ∈ T(ℂ)`, and `σ` a
section of the rank-one bundle `𝐕(ℰ) ⟶ T` whose zero scheme is the point `t`. Then `σ^*(u_ℰ)`,
viewed in `H²(T, T - t)` (`σ⁻¹(0) = {t}`), is the local orientation class of the complex
manifold `T(ℂ)` at `t` for its complex orientation. -/
theorem isLocalOrientationClass_forget_pullback_thomClass (R : Type) [CommRing R]
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (hσ : σ ≫ proj E = 𝟙 T)
    (hz : zeroLocus E σ = t.toHom.ker) :
    IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ T)) R curveOrientationBasis t
      ((cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
        (preimage_ofHom_range_zeroSection_subset_singleton σ t hz) (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
            (thomClass R E 1))) := by
  set M := EuclideanSpace ℂ (Fin 1)
  set S := (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
    range (UnderlyingSpace.map (K := ℂ) (zeroSection E))
  have hS : S = {t} := preimage_mapFun_range_zeroSection_eq_singleton σ t hz
  set u := (cohomologyWithSupports.pullback R (ModuleCat.of R R)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom (thomClass R E 1)
  have hTo : IsOrientedAtlas M (TopCat.of (UnderlyingSpace ℂ T)) :=
    isOrientedAtlas_of_isManifold_complex _
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R (Sᶜ : Set (TopCat.of (UnderlyingSpace ℂ T))) (2 * 1) u)
  have hα' : α ∈ relCocycles R ({t}ᶜ : Set (TopCat.of (UnderlyingSpace ℂ T))) (2 * 1) :=
    hS ▸ hα
  set e := ChartedSpace.chartAt (H := M) t
  have he : e ∈ atlas M (TopCat.of (UnderlyingSpace ℂ T)) := chart_mem_atlas M t
  have ht : t ∈ e.source := mem_chart_source M t
  obtain ⟨c, hi⟩ := exists_mem_chartBase E 1 t
  let O : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T)) :=
    ⟨e.source ∩ chartBase c, e.open_source.inter (isOpen_chartBase c)⟩
  have hO : (O : Set (TopCat.of (UnderlyingSpace ℂ T))) ⊆ chartBase c := inter_subset_right
  set a := chartLocalCoord σ hσ c
  have hcont : Continuous fun p : O ↦ evalExt (K := ℂ) c.1.1 a p.1 :=
    (continuousOn_evalExt c.1.1 a).comp_continuous continuous_subtype_val fun p ↦ hO p.2
  let h : TopCat.of O ⟶ TopCat.of ℂ := TopCat.ofHom ⟨fun p ↦ evalExt c.1.1 a p.1, hcont⟩
  obtain ⟨α₀, hα₀, hdiff⟩ := exists_cochainPullback_sub_mem_relCoboundaries R hσ c O hO h
    (fun p ↦ (evalExt_of_le a (hO p.2)).trans (eval_sectionCoord σ c _ p.1 (hO p.2) 0)) hα hrep
  obtain ⟨v, hv, hvt, hvO, h₀⟩ := exists_eval_comp_chartSimplex_eq_one t R hT hσ hz
    (isAlgebraicChart_of_mem_atlas he) ht c hi O ⟨ht, hi⟩ h (fun _ ↦ rfl) hα₀
  refine ⟨α, hα', isChartOrientedCocycle_of_eval hTo _ hα' he ht hv hvt
    (eval_chartSimplexOf_eq_one_of_sub_mem_relCoboundaries t R hz O h hv hvt hvO hdiff h₀), ?_⟩
  simp only [cohomologyWithSupports.forget]
  erw [relativeSingularCohomologyEquiv_map]
  rw [← hrep]
  rfl

end Point

end MMP.Modules
