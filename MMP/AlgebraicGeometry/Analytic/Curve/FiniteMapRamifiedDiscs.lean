module

public import MMP.AlgebraicGeometry.Analytic.Curve.RamifiedConeLift

/-!
# Ramified discs of a finite map from a smooth projective curve to `ℙ¹`

Let `X` be a smooth projective complex curve and `f : X ⟶ ℙ¹` a finite morphism over `ℂ`. Its
realization `f^an : X(ℂ) → ℙ¹(ℂ)` is a closed map (`f` is proper), `X(ℂ)` is Hausdorff (`X` is
separated), the fibres of `f^an` are finite (`f` is quasi-finite and the `ℂ`-points are closed
points) and `f^an` is not locally constant anywhere (`X(ℂ)` has no isolated points, being locally
homeomorphic to `ℂ`). So over a small disc around every point of `ℙ¹(ℂ)`, `f^an` is a finite
disjoint union of branched discs `w ↦ s + w ^ e` in étale charts
(`exists_ramifiedDisc_realize_projectiveLine`).

## Main results

* `MMP.Analytic.ChartConeCellulation.isClosedMap_realize_of_isProper`: a proper morphism
  realizes to a closed map.
* `MMP.Analytic.ChartConeCellulation.t2Space_complexPoints`: `X(ℂ)` is Hausdorff for `X`
  separated.
* `MMP.Analytic.ChartConeCellulation.finite_realize_preimage_singleton`: the fibres of the
  realization of a quasi-finite quasi-compact morphism are finite.
* `MMP.Analytic.ChartConeCellulation.not_eventually_realize_eq`: a realization with finite fibres
  of a smooth curve is not locally constant.
* `MMP.Analytic.ChartConeCellulation.exists_ramifiedDisc_realize_projectiveLine`: the ramified
  discs of a finite map of a smooth projective curve to `ℙ¹`.
-/

@[expose] public noncomputable section

open Set CategoryTheory AlgebraicGeometry MMP MMP.Analytic.ComplexPoints
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

namespace MMP.Analytic.ChartConeCellulation

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

/-- The realization of a morphism over `ℂ` is the induced map of underlying spaces, read through
`homeomorphUnderlyingSpace`. -/
theorem realize_eq_homeomorphUnderlyingSpace (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] :
    realize f (comp_over f (Spec (.of ℂ))) =
      homeomorphUnderlyingSpace.symm ∘ UnderlyingSpace.mapFun (K := ℂ) f ∘
        homeomorphUnderlyingSpace := by
  funext x
  rfl

/-- **A proper morphism realizes to a closed map.** -/
theorem isClosedMap_realize_of_isProper (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] :
    IsClosedMap (realize f (comp_over f (Spec (.of ℂ)))) := by
  rw [realize_eq_homeomorphUnderlyingSpace]
  exact homeomorphUnderlyingSpace.symm.isClosedMap.comp
    ((UnderlyingSpace.isProperMap_map (K := ℂ) f).isClosedMap.comp
      homeomorphUnderlyingSpace.isClosedMap)

/-- `X(ℂ)` is Hausdorff for `X` separated over `ℂ`. -/
theorem t2Space_complexPoints [IsSeparated (X ↘ Spec (.of ℂ))] :
    T2Space (ComplexPoints (X ↘ Spec (.of ℂ))) := by
  have := UnderlyingSpace.t2Space_of_isSeparated (K := ℂ) X
  exact homeomorphUnderlyingSpace.isEmbedding.t2Space

/-- **The fibres of the realization of a quasi-finite quasi-compact morphism are finite.** -/
theorem finite_realize_preimage_singleton (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [LocallyQuasiFinite f] [QuasiCompact f]
    (s : ComplexPoints (Y ↘ Spec (.of ℂ))) :
    (realize f (comp_over f (Spec (.of ℂ))) ⁻¹' {s}).Finite := by
  set pt := IsLocalRing.closedPoint ℂ
  have hinj : InjOn (fun x : ComplexPoints (X ↘ Spec (.of ℂ)) ↦ x.hom pt)
      (realize f (comp_over f (Spec (.of ℂ))) ⁻¹' {s}) := fun x _ y _ h ↦ by
    have := (UnderlyingSpace.equivClosedPoints (K := ℂ) X).injective
      (a₁ := homeomorphUnderlyingSpace x) (a₂ := homeomorphUnderlyingSpace y)
      (Subtype.ext h)
    exact homeomorphUnderlyingSpace.injective this
  refine Set.Finite.of_finite_image ?_ hinj
  refine (f.finite_preimage_singleton (s.hom pt)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x.hom ≫ f = s.hom := congrArg ComplexPoints.hom hx
  change f (x.hom pt) = s.hom pt
  rw [← hx']
  rfl

/-- A point of a scheme smooth of relative dimension one over `ℂ` is not isolated in `X(ℂ)`. -/
theorem not_isOpen_singleton_complexPoints [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (q : ComplexPoints (X ↘ Spec (.of ℂ))) : ¬ IsOpen ({q} : Set _) := by
  intro hq
  obtain ⟨c, hc⟩ := EtaleCoordinateChart.exists_mem_W (n := 1) q
  have hcs : q ∈ c.toOpenPartialHomeomorph.source := by
    rwa [c.source_toOpenPartialHomeomorph]
  have himg := c.toOpenPartialHomeomorph.isOpen_image_of_subset_source hq
    (singleton_subset_iff.2 hcs)
  rw [image_singleton] at himg
  exact not_isOpen_singleton _ himg

omit [Y.Over (Spec (.of ℂ))] in
/-- **A realization with finite fibres of a smooth curve is not locally constant.** -/
theorem not_eventually_realize_eq [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    [T1Space (ComplexPoints (X ↘ Spec (.of ℂ)))] {sY : Y ⟶ Spec (.of ℂ)} (f : X ⟶ Y)
    (hf : f ≫ sY = X ↘ Spec (.of ℂ)) (hfin : ∀ s, (realize f hf ⁻¹' {s}).Finite)
    (q : ComplexPoints (X ↘ Spec (.of ℂ))) :
    ¬ ∀ᶠ y in nhds q, realize f hf y = realize f hf q := fun hev ↦
  not_isOpen_singleton_complexPoints q (isOpen_singleton_of_finite_mem_nhds q hev (hfin _))

variable [AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The ramified discs of a finite map of a smooth projective curve to `ℙ¹`.** For a finite
morphism `f : X ⟶ ℙ¹` over `ℂ`, an étale chart `c'` of `ℙ¹` at `s`, read in `ℂ`, neighbourhoods
`N q` of the points of `X(ℂ)` and `ε > 0`, the realization of `f` is a ramified disc over a disc
of radius at most `ε` around the reading of `s`, each of whose coordinates has source in
`c.W ∩ N q` for some point `q` over `s` and some étale chart `c`, with `c ∘ (d.coord i).symm`
analytic on the target of `d.coord i`. -/
theorem exists_ramifiedDisc_realize_projectiveLine
    (f : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ 1))
    (hf : f ≫ projToSpecCoeff ℂ 1 = X ↘ Spec (.of ℂ)) [IsFinite f]
    (c' : EtaleCoordinateChart (projToSpecCoeff ℂ 1) 1) {s : ComplexPoints (projToSpecCoeff ℂ 1)}
    (hs : s ∈ c'.W)
    (N : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))))
    (hN : ∀ q, N q ∈ nhds q) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : RamifiedDisc.{0, 0, 0} (realize f hf),
      d.chart = c'.toOpenPartialHomeomorph.transHomeomorph
        (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph ∧
      d.centre = c'.toOpenPartialHomeomorph.transHomeomorph
        (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).toHomeomorph s ∧
      0 < d.radius ∧ d.radius ≤ ε ∧
      ∀ i, ∃ q ∈ realize f hf ⁻¹' {s},
        ∃ c : EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1,
        (d.coord i).source ⊆ c.W ∩ N q ∧
        ∀ w ∈ (d.coord i).target,
          AnalyticAt ℂ (fun w ↦ c.toOpenPartialHomeomorph ((d.coord i).symm w)) w := by
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ 1⟩
  haveI : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ 1
  haveI : LocallyOfFiniteType (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (projToSpecCoeff ℂ 1))
  have := t2Space_complexPoints (X := X)
  have hfin := finite_realize_preimage_singleton f
  exact exists_ramifiedDisc_realize f _ (isClosedMap_realize_of_isProper f) c' hs (hfin s)
    (fun q _ ↦ not_eventually_realize_eq f _ hfin q) N hN hε

end MMP.Analytic.ChartConeCellulation
