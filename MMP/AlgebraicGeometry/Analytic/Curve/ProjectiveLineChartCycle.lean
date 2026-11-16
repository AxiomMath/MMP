module

public import MMP.AlgebraicGeometry.Analytic.Curve.RiemannSphereConeCycle
public import MMP.AlgebraicGeometry.Analytic.GAGA.TwistsLaurentModel
public import MMP.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinateCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import MMP.AlgebraicGeometry.Variety.SmoothVarietyConstructions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedProjectiveSpace

/-!
# A fine fundamental cycle of flat chart cones on the projective line

The two standard affine coordinates `x₁ / x₀` on `D₊(x₀)` and `x₀ / x₁` on `D₊(x₁)` are étale
coordinate charts of `ℙ¹(ℂ)`, onto `ℂ`, related by `x₀ / x₁ = 1 / (x₁ / x₀)` on `D₊(x₀ x₁)`, so
they make `ℙ¹(ℂ)` a sphere (`stdSphereCharts`). The flat cone cycle of the sphere
(`MMP.Analytic.ChartConeCellulation.exists_cone_cycle_of_sphereCharts`) is then a fine fundamental
cycle of `ℙ¹(ℂ)`, with prescribed apices.

## Main definitions

* `MMP.Analytic.ChartConeCellulation.stdEtaleChart`: the standard étale charts of `ℙ¹(ℂ)`.
* `MMP.Analytic.ChartConeCellulation.stdSphereCharts`: the sphere charts of `ℙ¹(ℂ)`.

## Main results

* `MMP.Analytic.ChartConeCellulation.exists_cone_cycle_projectiveLine`: the fine fundamental
  cycle of flat chart cones on `ℙ¹(ℂ)`.
-/

@[expose] public noncomputable section

open Set Finsupp MMP.SingularChain
open MMP.Analytic MMP.Analytic.CurveCupPositivity

namespace MMP.Analytic.ChartConeCellulation

section ProjectiveLine

open CategoryTheory AlgebraicGeometry MMP MMP.FundamentalClass
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

/-- `ℙ¹_ℂ = Proj ℂ[x₀, x₁]`, over `ℂ` through `projToSpecCoeff ℂ 1`, is a projective variety. -/
theorem isProjectiveVariety_projectiveLine :
    AlgebraicGeometry.IsProjectiveVariety ℂ (projToSpecCoeff ℂ 1) :=
  (AlgebraicGeometry.isProjectiveVariety_iff_isProjective' ℂ _).2
    ⟨inferInstance, Stacks.WeilDeRham.isProjective_projToSpecCoeff ℂ 1⟩

/-- `ℙ¹_ℂ = Proj ℂ[x₀, x₁]` over `ℂ` through `projToSpecCoeff ℂ 1`. -/
@[reducible] private noncomputable def projectiveLineOver :
    (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
  ⟨projToSpecCoeff ℂ 1⟩

attribute [local instance high] projectiveLineOver

attribute [local instance] isProjectiveVariety_projectiveLine
  Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff
  MMP.Analytic.ProjectiveTwists.locallyOfFiniteType_sP

/-! ### The standard étale charts of `ℙ¹` -/

open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints in
/-- The coordinate `x_{j.succAbove 0} / x_j` of the standard chart `D₊(x_j)` of `ℙ¹_ℂ` is an étale
coordinate: `Γ(D₊(x_j)) ≅ ℂ[t]`, so the map `D₊(x_j) → 𝔸¹` is étale. -/
theorem etale_stdChart (j : Fin 2) :
    Etale (AffineSpace.homOfVector
      ((UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j).ι ≫ (sP 1))
      (fun i : ULift.{0} (Fin 1) ↦
        (UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j).topIso.inv (stdGen 1 j i.down))) := by
  let e := (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv
  let P : MvPolynomial (Fin 1) ℂ →+*
      Γ(AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1),
        UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j) :=
    MvPolynomial.eval₂Hom (baseRingHom (sP 1) (UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j))
      (stdGen 1 j)
  let φ : MvPolynomial (ULift.{0} (Fin 1)) Γ(Spec (.of ℂ), ⊤) →+*
      Γ(AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1),
        UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j) :=
    P.comp ((MvPolynomial.rename ULift.down).toRingHom.comp (MvPolynomial.map e.toRingHom))
  have hφ : Function.Bijective φ :=
    (bijective_pres 1 j).comp ((MvPolynomial.renameEquiv ℂ Equiv.ulift).bijective.comp
      (MvPolynomial.mapEquiv _ e).bijective)
  have hU : IsAffineOpen (UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j) :=
    Proj.isAffineOpen_basicOpen (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1)
      (MvPolynomial.X j) (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one ℂ 1 j) one_pos
  have key := MMP.Flips.ResolutionInputs.etale_homOfVector_of_etale
    (sP 1) (UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j) hU
    (fun i ↦ stdGen 1 j i.down) φ (by
      refine RingHom.ext fun a ↦ ?_
      have h1 : φ (MvPolynomial.C a) = baseRingHom (sP 1)
          (UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j) (e a) := by
        simp only [φ, P, RingHom.comp_apply, MvPolynomial.map_C, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, MvPolynomial.rename_C, MvPolynomial.eval₂Hom_C]
        rfl
      rw [RingHom.comp_apply, h1, baseRingHom, RingHom.comp_apply, RingHom.comp_apply]
      have h2 : (Scheme.ΓSpecIso (.of ℂ)).inv.hom (e a) = a := by
        change ((Scheme.ΓSpecIso (.of ℂ)).hom ≫ (Scheme.ΓSpecIso (.of ℂ)).inv).hom a = a
        rw [Iso.hom_inv_id]; rfl
      rw [h2]
      change ((sP 1).appTop ≫ (AlgebraicGeometry.Proj
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1)).presheaf.map
        (homOfLE (le_top : UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j ≤ ⊤)).op).hom a = _
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      erw [Scheme.Hom.appLE_map]) (fun i ↦ by
        show P ((MvPolynomial.rename ULift.down) (MvPolynomial.map e.toRingHom
          (MvPolynomial.X i))) = stdGen 1 j i.down
        rw [MvPolynomial.map_X, MvPolynomial.rename_X]
        exact MvPolynomial.eval₂Hom_X' _ _ _) (RingHom.Etale.of_bijective hφ)
  exact key

open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints in
/-- The standard étale chart `D₊(x_j)(ℂ) → ℂ` of `ℙ¹(ℂ)`, `y ↦ (x_{j.succAbove 0} / x_j)(y)`. -/
def stdEtaleChart (j : Fin 2) :
    ComplexPoints.EtaleCoordinateChart (sP 1) 1 where
  U := UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j
  z := stdGen 1 j
  etale := etale_stdChart j
  W := ComplexPoints.chart (UnderlyingSpace.projectiveSpaceStdChart ℂ 1 j)
  subset := subset_rfl
  isOpen := (Chart.isOpen_chart_and_isEmbedding_coords (stdChart 1 j)).1
  nonempty := by
    obtain ⟨y, -⟩ := (range_coords_stdChart 1 j).symm ▸ mem_univ (0 : Fin 1 → ℂ)
    exact ⟨y.1, y.2⟩
  isOpenEmbedding :=
    ⟨(Chart.isOpen_chart_and_isEmbedding_coords (stdChart 1 j)).2.2.1, by
      have := range_coords_stdChart 1 j
      exact this ▸ isOpen_univ⟩

open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints in
/-- On its domain, the chart `stdEtaleChart j` sends `y` to the homogeneous coordinate ratio
`hcoord 1 j y (j.succAbove 0)`. -/
theorem stdEtaleChart_apply (j : Fin 2) {y : ComplexPoints (sP 1)}
    (hy : y ∈ (stdEtaleChart j).W) :
    (stdEtaleChart j).toOpenPartialHomeomorph y 0 = hcoord 1 j ⟨y, hy⟩ (j.succAbove 0) :=
  (stdEtaleChart j).toOpenPartialHomeomorph_apply hy 0

open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints in
/-- The target of the chart `stdEtaleChart j` is all of `Fin 1 → ℂ`. -/
theorem target_stdEtaleChart (j : Fin 2) :
    (stdEtaleChart j).toOpenPartialHomeomorph.target = univ := by
  refine eq_univ_of_forall fun v ↦ ?_
  obtain ⟨y, hy⟩ := (range_coords_stdChart 1 j).symm ▸ mem_univ v
  have hs : y.1 ∈ (stdEtaleChart j).toOpenPartialHomeomorph.source := by
    rw [ComplexPoints.EtaleCoordinateChart.source_toOpenPartialHomeomorph]; exact y.2
  have h := (stdEtaleChart j).toOpenPartialHomeomorph.map_source hs
  have he : (stdEtaleChart j).toOpenPartialHomeomorph y.1 = v := by
    rw [← hy]
    funext i
    rw [Subsingleton.elim i 0, (stdEtaleChart j).toOpenPartialHomeomorph_apply y.2 0]
    rfl
  rwa [he] at h

open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints in
/-- The inverse of the chart `stdEtaleChart j` takes values in its domain `W`. -/
theorem symm_mem_W_stdEtaleChart (j : Fin 2) (v : Fin 1 → ℂ) :
    (stdEtaleChart j).toOpenPartialHomeomorph.symm v ∈ (stdEtaleChart j).W :=
  (stdEtaleChart j).toOpenPartialHomeomorph_symm_mem
    (by rw [target_stdEtaleChart]; exact mem_univ _)

open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints in
/-- The coordinate `hcoord 1 j` of the inverse chart image of `v` is `v 0`. -/
theorem hcoord_symm_stdEtaleChart (j : Fin 2) (v : Fin 1 → ℂ) :
    hcoord 1 j ⟨_, symm_mem_W_stdEtaleChart j v⟩ (j.succAbove 0) = v 0 := by
  rw [← stdEtaleChart_apply j]
  exact congrFun ((stdEtaleChart j).toOpenPartialHomeomorph.right_inv
    (by rw [target_stdEtaleChart]; exact mem_univ _)) 0

open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints in
/-- The two standard charts of `ℙ¹(ℂ)` make it a sphere. -/
def stdSphereCharts : SphereCharts (ComplexPoints (sP 1)) where
  chart k := (stdEtaleChart k).toOpenPartialHomeomorph
  target_eq k := target_stdEtaleChart k
  source_union := by
    refine eq_univ_of_forall fun x ↦ ?_
    have hx : x.toScheme ∈ ⨆ i, UnderlyingSpace.projectiveSpaceStdChart ℂ 1 i := by
      rw [Stacks.AlgebraicGeometry.ProjPolyChart.iSup_basicOpen_X_eq_top ℂ 1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    simp only [ComplexPoints.EtaleCoordinateChart.source_toOpenPartialHomeomorph, mem_union]
    fin_cases i
    · exact Or.inl (mem_chart_iff.2 hi)
    · exact Or.inr (mem_chart_iff.2 hi)
  symm_mem_source_one v hv := by
    have hy := symm_mem_W_stdEtaleChart 0 v
    have hval := hcoord_symm_stdEtaleChart 0 v
    rw [ComplexPoints.EtaleCoordinateChart.source_toOpenPartialHomeomorph]
    exact mem_chart_iff.2 ((toScheme_mem_X_iff 0 ⟨_, hy⟩ 1).2 (by
      rw [show (1 : Fin 2) = (0 : Fin 2).succAbove 0 from rfl, hval]; exact hv))
  chart_one_symm v hv := by
    have hy := symm_mem_W_stdEtaleChart 0 v
    have hval := hcoord_symm_stdEtaleChart 0 v
    have hy1 : (stdEtaleChart 0).toOpenPartialHomeomorph.symm v ∈ (stdEtaleChart 1).W :=
      mem_chart_iff.2 ((toScheme_mem_X_iff 0 ⟨_, hy⟩ 1).2 (by
        rw [show (1 : Fin 2) = (0 : Fin 2).succAbove 0 from rfl, hval]; exact hv))
    funext i
    rw [Subsingleton.elim i 0, stdEtaleChart_apply 1 hy1]
    have hc := hcoord_change 0 1 _ hy hy1 1
    rw [hcoord_self] at hc
    rw [show (0 : Fin 2).succAbove 0 = 1 from rfl] at hval
    rw [show (1 : Fin 2).succAbove 0 = 0 from rfl, ← hval]
    exact eq_inv_of_mul_eq_one_left hc.symm
  symm_zero_notMem := by
    have hy := symm_mem_W_stdEtaleChart 1 0
    have hval := hcoord_symm_stdEtaleChart 1 0
    rw [show (1 : Fin 2).succAbove 0 = 0 from rfl] at hval
    intro hy0
    rw [ComplexPoints.EtaleCoordinateChart.source_toOpenPartialHomeomorph] at hy0
    have hc := hcoord_change 1 0 _ hy hy0 0
    rw [hcoord_self, hval] at hc
    simp at hc

/-- **The two standard charts of `ℙ¹(ℂ)` are étale coordinate charts making it a sphere.** The
coordinate `x₁ / x₀` on `D₊(x₀)` and the coordinate `x₀ / x₁` on `D₊(x₁)` are étale coordinates
(each is an isomorphism `D₊(xᵢ) ≅ 𝔸¹`), their domains are all of `D₊(xᵢ)(ℂ)`, their images all of
`ℂ`, and `x₀ / x₁ = 1 / (x₁ / x₀)` on `D₊(x₀ x₁)`. -/
theorem exists_sphereCharts_projectiveLine :
    ∃ (c : Fin 2 → ComplexPoints.EtaleCoordinateChart (projToSpecCoeff ℂ 1) 1)
      (E : SphereCharts (ComplexPoints (projToSpecCoeff ℂ 1))),
      ∀ k, E.chart k = (c k).toOpenPartialHomeomorph :=
  ⟨stdEtaleChart, stdSphereCharts, fun _ ↦ rfl⟩

/-- **A fine fundamental cycle of flat chart cones on `ℙ¹(ℂ)` with prescribed apices.** For every
finite set `S ⊆ ℙ¹(ℂ)` and open neighbourhoods `B y` of the points `y` of `ℙ¹(ℂ)`, there is a
finite `2`-cycle `w = ∑ r_σ σ` of `ℙ¹(ℂ)` with real coefficients, whose triangles lie in some
`B y` and are read in the two standard étale charts as `C²` maps with `r_σ` times the Jacobian
nonnegative on an open neighbourhood of the square, meeting every nonempty open set at a point of
positive Jacobian, with every point of `S` the apex of the flat cones through it and of no other
triangle, and representing the fundamental class of `ℙ¹`. -/
theorem exists_cone_cycle_projectiveLine
    (S : Set (ComplexPoints (projToSpecCoeff ℂ 1))) (hS : S.Finite)
    (B : ComplexPoints (projToSpecCoeff ℂ 1) →
      Set (ComplexPoints (projToSpecCoeff ℂ 1)))
    (hBo : ∀ y, IsOpen (B y)) (hmem : ∀ y, y ∈ B y) :
    ∃ (w : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1) →₀ ℂ)
      (r : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1) → ℝ)
      (Y' : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1) →
        ComplexPoints (projToSpecCoeff ℂ 1))
      (c : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1) →
        ComplexPoints.EtaleCoordinateChart (projToSpecCoeff ℂ 1) 1)
      (g : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1) →
        ℝ × ℝ → (Fin 1 → ℂ))
      (U : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1) →
        Set (ℝ × ℝ)),
      ∃ hw : bd ℂ 1 w = 0,
      (∀ σ ∈ w.support, w σ = r σ ∧ range σ ⊆ B (Y' σ) ∧ IsOpen (U σ) ∧ unitSquare ⊆ U σ ∧
        ContDiffOn ℝ 2 (g σ) (U σ) ∧ MapsTo (g σ) (U σ) (c σ).toOpenPartialHomeomorph.target ∧
        (∀ p ∈ unitSquare, σ (squareCollapse p) = (c σ).toOpenPartialHomeomorph.symm (g σ p)) ∧
        ∀ p ∈ U σ, ∀ i : Fin 1, 0 ≤ r σ * FundamentalChartCycle.chartJacobian (g σ) p i) ∧
      (∀ W : Set (ComplexPoints (projToSpecCoeff ℂ 1)), IsOpen W → W.Nonempty →
        ∃ σ ∈ w.support, ∃ p ∈ unitSquare, σ (squareCollapse p) ∈ W ∧ ∀ i : Fin 1,
          0 < r σ * FundamentalChartCycle.chartJacobian (g σ) p i) ∧
      (∃ σ₀ ∈ w.support, ∃ p₀ ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, w σ₀ = 1 ∧
        (∀ i : Fin 1, 0 < FundamentalChartCycle.chartJacobian (g σ₀) p₀ i) ∧
        (∀ t, σ₀ t = σ₀ (squareCollapse p₀) → t = squareCollapse p₀) ∧
        ∀ σ ∈ w.support, σ ≠ σ₀ → σ₀ (squareCollapse p₀) ∉ range σ) ∧
      (∀ s ∈ S, (∃ σ ∈ w.support, σ (squareCollapse (0, 0)) = s) ∧
        ∀ σ ∈ w.support, s ∈ range σ →
          s ∈ (c σ).toOpenPartialHomeomorph.source ∧
          (∃ γ : ℝ → Fin 1 → ℂ, ContDiff ℝ 2 γ ∧
            g σ = CurveCupPositivity.coneMap coneProfile ((c σ).toOpenPartialHomeomorph s) γ) ∧
          ∀ t, σ t = s ↔ t = squareCollapse (0, 0)) ∧
      (letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
        ⟨projToSpecCoeff ℂ 1⟩
      haveI : IsSmoothVariety ℂ (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
        MMP.isSmoothVariety_projToSpecCoeff ℂ 1
      haveI : IsProjectiveVariety ℂ (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
        isProjectiveVariety_projectiveLine
      haveI : SmoothOfRelativeDimension 1
          (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
        Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff ℂ 1
      IsVarietyFundamentalClass ℂ (PolarizationPositivity.natCast_one_eq_dimension
          (PolarizationPositivity.topologicalKrullDim_eq_one
            (X := AlgebraicGeometry.Proj (polyGrading ℂ 1))))
        (PolarizationPositivity.finiteCycleClass
          (Y := TopCat.of (UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ 1))))
          (postcomp ℂ ⟨_, (ComplexPoints.homeomorphUnderlyingSpace
            (X := AlgebraicGeometry.Proj (polyGrading ℂ 1))).continuous⟩ (1 + 1) w)
          (PolarizationPositivity.bd_postcomp_homeomorphUnderlyingSpace_eq_zero hw))) := by
  classical
  haveI : IsSmoothVariety ℂ (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    MMP.isSmoothVariety_projToSpecCoeff ℂ 1
  haveI : IsProjectiveVariety ℂ (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    isProjectiveVariety_projectiveLine
  haveI : SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff ℂ 1
  obtain ⟨c, E, hE⟩ := exists_sphereCharts_projectiveLine
  obtain ⟨w, r, k, g, U, hw, hgood, hdense, ⟨σ₀, hσ₀, p₀, hp₀, hw₀, hJ, hinj, hsimple⟩, hSc⟩ :=
    exists_cone_cycle_of_sphereCharts E S hS B hBo hmem
  have htarget : ∀ j, (c j).toOpenPartialHomeomorph.target = univ := fun j ↦ by
    rw [← hE]; exact E.target_eq j
  let Y' : Simplex (Analytification.space (projToSpecCoeff ℂ 1)) (1 + 1) →
      ComplexPoints (projToSpecCoeff ℂ 1) := fun σ ↦
    if h : ∃ y, range σ ⊆ B y then h.choose else σ (squareCollapse (0, 0))
  have hgood' : ∀ σ ∈ w.support, w σ = r σ ∧ range σ ⊆ B (Y' σ) ∧ IsOpen (U σ) ∧
      unitSquare ⊆ U σ ∧ ContDiffOn ℝ 2 (g σ) (U σ) ∧
      MapsTo (g σ) (U σ) (c (k σ)).toOpenPartialHomeomorph.target ∧
      (∀ p ∈ unitSquare,
        σ (squareCollapse p) = (c (k σ)).toOpenPartialHomeomorph.symm (g σ p)) ∧
      ∀ p ∈ U σ, ∀ i : Fin 1, 0 ≤ r σ * FundamentalChartCycle.chartJacobian (g σ) p i := by
    intro σ hσ
    obtain ⟨h1, hy, h2, h3, h4, h5, h6⟩ := hgood σ hσ
    have hY : range σ ⊆ B (Y' σ) := by
      simp only [Y', dif_pos hy]; exact hy.choose_spec
    refine ⟨h1, hY, h2, h3, h4, fun p _ ↦ by rw [htarget]; exact mem_univ _, fun p hp ↦ ?_, h6⟩
    rw [h5 p hp, hE]
  refine ⟨w, r, Y', fun σ ↦ c (k σ), g, U, hw, hgood', hdense,
    ⟨σ₀, hσ₀, p₀, hp₀, hw₀, hJ, hinj, hsimple⟩, fun s hs ↦ ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hSc s hs
    refine ⟨h1, fun σ hσ hsσ ↦ ?_⟩
    obtain ⟨h3, h4, h5⟩ := h2 σ hσ hsσ
    exact ⟨by rw [← hE]; exact h3, by rw [← hE]; exact h4, h5⟩
  · obtain ⟨-, -, hUo, hsq, hg, hgT, hσ, -⟩ := hgood' σ₀ hσ₀
    exact isVarietyFundamentalClass_of_simplePoint w hw hσ₀ (c (k σ₀)) (g σ₀) (U σ₀) hUo hsq hg
      hgT hσ hp₀ hw₀ hJ hinj hsimple

end ProjectiveLine

end MMP.Analytic.ChartConeCellulation
