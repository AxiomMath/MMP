module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocalNormalForm
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering

/-!
# A product chart of balls in a holomorphic chart of `X_reg(ℂ)`

Let `X` be a complex variety of dimension `k + 1`, `e` an algebraic chart of `X(ℂ)` with values
in `ℂ^{k+1}` and `ψ` a biholomorphism from an open subset of `ℂ^{k+1}` onto an open subset of
`ℂ × ℂ^k`, such that `U = e.source ∩ e⁻¹(ψ.source)` lies in `X_reg(ℂ)`. The composite `ψ ∘ e`
is a partial homeomorphism of `X(ℂ)` with source `U` and open target; around a point `y₀ ∈ U`
whose image `ψ (e y₀) = (0, b₀)` lies on the hyperplane `{0} × ℂ^k`, the target contains a
product of balls `B_ε(0) × B_δ(b₀)`, and its preimage `O ⊆ U` is an open neighbourhood of `y₀`
mapped homeomorphically onto `B_ε(0) × B_δ(b₀)`. In the algebraic charts `e₁` of `X_reg(ℂ)` this
homeomorphism reads as `ψ ∘ e ∘ e₁⁻¹`, which is holomorphic with injective derivative: the
transitions `e ∘ e₁⁻¹` between algebraic charts are holomorphic
(`MMP.UnderlyingSpace.IsAlgebraicChart.contDiffOn_symm_trans`), and
`e₁ ∘ e⁻¹ ∘ ψ⁻¹` is a differentiable left inverse.

This is the local chart used in the proof of Lemma 19.1.3 of Fulton, where the localized first
Chern class of a function is computed near a general point of a component of its zeros, in the
coordinates given by the local normal form
(`MMP.UnderlyingSpace.exists_localNormalForm`).

## Main results

* `MMP.UnderlyingSpace.IsAlgebraicChart.exists_injective_hasFDerivAt_comp_symm`:
  `ψ ∘ e ∘ e₁⁻¹` has an injective derivative, for algebraic charts `e`, `e₁` and a map `ψ`
  differentiable with a differentiable local inverse.
* `MMP.UnderlyingSpace.exists_ballProductChart`: the ball product chart.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set Metric
open scoped ContDiff

namespace MMP

open MMP

namespace UnderlyingSpace

open MMP.UnderlyingSpace

namespace IsAlgebraicChart

open MMP.UnderlyingSpace.IsAlgebraicChart

universe u

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {e e₁ : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) E}

/-- **A holomorphic map read in algebraic charts.** For algebraic charts `e`, `e₁` of `X(𝕜)` and a
partial homeomorphism `ψ` of `E` differentiable at `e p` whose inverse is differentiable at
`ψ (e p)`, the map `ψ ∘ e ∘ e₁⁻¹` has an injective derivative at `e₁ p`. -/
theorem exists_injective_hasFDerivAt_comp_symm (he : IsAlgebraicChart e)
    (he₁ : IsAlgebraicChart e₁) {ψ : OpenPartialHomeomorph E F} {p : UnderlyingSpace 𝕜 X}
    (hp₁ : p ∈ e₁.source) (hp : p ∈ e.source) (hpψ : e p ∈ ψ.source)
    (hψ : DifferentiableAt 𝕜 ψ (e p)) (hψs : DifferentiableAt 𝕜 ψ.symm (ψ (e p))) :
    ∃ L : E →L[𝕜] F, Function.Injective L ∧ HasFDerivAt (fun y ↦ ψ (e (e₁.symm y))) L (e₁ p) := by
  set f := e₁.symm.trans e
  set g := e.symm.trans e₁
  have hpf : e₁ p ∈ f.source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨e₁.map_source hp₁, by rwa [mem_preimage, e₁.left_inv hp₁]⟩
  have hpg : e p ∈ g.source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨e.map_source hp, by rwa [mem_preimage, e.left_inv hp]⟩
  have hfd : DifferentiableAt 𝕜 f (e₁ p) :=
    ((he₁.contDiffOn_symm_trans he).contDiffAt (f.open_source.mem_nhds hpf)).differentiableAt
      (by simp)
  have hgd : DifferentiableAt 𝕜 g (e p) :=
    ((he.contDiffOn_symm_trans he₁).contDiffAt (g.open_source.mem_nhds hpg)).differentiableAt
      (by simp)
  have hfp : f (e₁ p) = e p := by
    simp only [f, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.coe_trans_symm, e₁.left_inv hp₁]
  have hψ' : HasFDerivAt ψ (fderiv 𝕜 ψ (e p)) (f (e₁ p)) := hfp ▸ hψ.hasFDerivAt
  have hF : HasFDerivAt (fun y ↦ ψ (f y)) ((fderiv 𝕜 ψ (e p)).comp (fderiv 𝕜 f (e₁ p)))
      (e₁ p) := hψ'.comp (e₁ p) hfd.hasFDerivAt
  have hGd : HasFDerivAt (fun z ↦ g (ψ.symm z))
      ((fderiv 𝕜 g (e p)).comp (fderiv 𝕜 ψ.symm (ψ (e p)))) (ψ (f (e₁ p))) := by
    rw [hfp]
    have hg' : HasFDerivAt g (fderiv 𝕜 g (e p)) (ψ.symm (ψ (e p))) := by
      rw [ψ.left_inv hpψ]
      exact hgd.hasFDerivAt
    exact hg'.comp _ hψs.hasFDerivAt
  have hN : f.source ∩ f ⁻¹' ψ.source ∈ 𝓝 (e₁ p) :=
    (f.isOpen_inter_preimage ψ.open_source).mem_nhds ⟨hpf, by rwa [mem_preimage, hfp]⟩
  have hid : (fun y ↦ g (ψ.symm (ψ (f y)))) =ᶠ[𝓝 (e₁ p)] id := by
    filter_upwards [hN] with y ⟨hy₁, hy₂⟩
    rw [ψ.left_inv hy₂]
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy₁
    simp only [f, g, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.coe_trans_symm, id, e.left_inv hy₁.2, e₁.right_inv hy₁.1]
  have huniq : ((fderiv 𝕜 g (e p)).comp (fderiv 𝕜 ψ.symm (ψ (e p)))).comp
      ((fderiv 𝕜 ψ (e p)).comp (fderiv 𝕜 f (e₁ p))) = ContinuousLinearMap.id 𝕜 E :=
    (hGd.comp (e₁ p) hF).unique ((hasFDerivAt_id (e₁ p)).congr_of_eventuallyEq hid)
  refine ⟨(fderiv 𝕜 ψ (e p)).comp (fderiv 𝕜 f (e₁ p)),
    Function.LeftInverse.injective (g := (fderiv 𝕜 g (e p)).comp (fderiv 𝕜 ψ.symm (ψ (e p))))
      (DFunLike.congr_fun huniq ·), hF⟩

end IsAlgebraicChart

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]

/-- A chart of the atlas of `O ∩ X_reg(ℂ)` is read, near each point of its source, in an algebraic
chart `e₁` of `X(ℂ)`: it agrees with `e₁` there, and its inverse agrees with `e₁⁻¹` on its
target. -/
theorem exists_isAlgebraicChart_eqOn_of_mem_atlas_regularOpensInter {n : ℕ}
    (hn : (n : WithBot ℕ∞) = MMP.Intersection.Scheme.dimension X)
    {O : Opens (UnderlyingSpace ℂ X)}
    {c : OpenPartialHomeomorph (regularOpensInter (𝕜 := ℂ) O) (EuclideanSpace ℂ (Fin n))}
    (hc : letI := regularChartedSpace (𝕜 := ℂ) hn
      c ∈ atlas (EuclideanSpace ℂ (Fin n)) (regularOpensInter (𝕜 := ℂ) O))
    {x : regularOpensInter (𝕜 := ℂ) O} (hx : x ∈ c.source) :
    ∃ e₁ : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)),
      IsAlgebraicChart e₁ ∧ x.1.1 ∈ e₁.source ∧ c x = e₁ x.1.1 ∧
      ∀ y ∈ c.target, (c.symm y).1.1 = e₁.symm y := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  obtain ⟨q, hq⟩ := mem_iUnion.1 hc
  obtain rfl := mem_singleton_iff.1 hq
  obtain ⟨e₁, h, he₁, hc₀⟩ := chart_mem_atlas (EuclideanSpace ℂ (Fin n)) q.1
  set c₀ := chartAt (EuclideanSpace ℂ (Fin n)) q.1
  have hxc₀ : x.1 ∈ c₀.source := by rwa [OpenPartialHomeomorph.subtypeRestr_source] at hx
  refine ⟨e₁, he₁, by rwa [hc₀, OpenPartialHomeomorph.subtypeRestr_source] at hxc₀, ?_,
    fun y hy ↦ ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_coe, Set.restrict_apply, hc₀,
      OpenPartialHomeomorph.subtypeRestr_coe, Set.restrict_apply]
  · have h1 := (c₀.subtypeRestr_symm_eqOn ⟨q⟩ hy).symm
    have hy' := c₀.subtypeRestr_target_subset ⟨q⟩ hy
    simp only [Function.comp_apply] at h1
    rw [h1]
    rw [hc₀] at hy' ⊢
    exact ((e₁.subtypeRestr_symm_eqOn h hy').symm :)

/-- **A ball product chart.** Let `e` be an algebraic chart of `X(ℂ)` (`dim X = k + 1`) and
`ψ` a biholomorphism from an open subset of `ℂ^{k+1}` onto an open subset of `ℂ × ℂ^k`, with
`U = e.source ∩ e⁻¹(ψ.source) ⊆ X_reg(ℂ)`. For `y₀ ∈ U` with `(ψ (e y₀)).1 = 0` there are an open
`O ∋ y₀` of `X(ℂ)` inside `U` and balls `B_ε(0) ⊆ ℂ`, `B = B_δ(b₀) ⊆ ℂ^k` such that `ψ ∘ e` maps
`O` homeomorphically onto `B_ε(0) × B`; read in the algebraic charts of `X_reg(ℂ)` it is
holomorphic with injective derivative. -/
theorem exists_ballProductChart {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = MMP.Intersection.Scheme.dimension X)
    {e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin (k + 1)))}
    (he : IsAlgebraicChart e)
    {ψ : OpenPartialHomeomorph (EuclideanSpace ℂ (Fin (k + 1))) (ℂ × EuclideanSpace ℂ (Fin k))}
    (hψ : ContDiffOn ℂ ω ψ ψ.source) (hψs : ContDiffOn ℂ ω ψ.symm ψ.target)
    (hU : e.source ∩ e ⁻¹' ψ.source ⊆ regularPart ℂ X)
    {y₀ : UnderlyingSpace ℂ X} (hy₀ : y₀ ∈ e.source ∩ e ⁻¹' ψ.source) (hy₀0 : (ψ (e y₀)).1 = 0) :
    ∃ (O : Opens (UnderlyingSpace ℂ X)) (hO : O ≤ regularOpens ℂ X) (ε δ : ℝ) (_ : 0 < ε)
      (_ : 0 < δ),
      y₀ ∈ O ∧ (O : Set (UnderlyingSpace ℂ X)) ⊆ e.source ∩ e ⁻¹' ψ.source ∧
      ∃ Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ
          ball (0 : ℂ) ε × (⟨ball (ψ (e y₀)).2 δ, isOpen_ball⟩ : Opens (EuclideanSpace ℂ (Fin k))),
        (∀ p, ((Φ p).1 : ℂ) = (ψ (e p.1.1)).1) ∧
        (∀ p, ((Φ p).2 : EuclideanSpace ℂ (Fin k)) = (ψ (e p.1.1)).2) ∧
        letI := regularChartedSpace (𝕜 := ℂ) hn
        ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (k + 1))) (regularOpensInter (𝕜 := ℂ) O),
          ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin k))
            (⟨ball (ψ (e y₀)).2 δ, isOpen_ball⟩ : Opens (EuclideanSpace ℂ (Fin k))),
          ∀ x ∈ c.source, (Φ x).2 ∈ c'.source →
            ∃ L : EuclideanSpace ℂ (Fin (k + 1)) →L[ℂ] ℂ × EuclideanSpace ℂ (Fin k),
              Function.Injective L ∧
              HasFDerivAt (fun y ↦ (((Φ (c.symm y)).1 : ℂ), c' (Φ (c.symm y)).2)) L (c x) := by
  set F := e.trans ψ
  have hFy₀ : F y₀ = (0, (ψ (e y₀)).2) := Prod.ext hy₀0 rfl
  obtain ⟨r, hr, hrF⟩ := Metric.isOpen_iff.1 F.open_target _ (F.map_source hy₀)
  rw [hFy₀, ← ball_prod_same] at hrF
  set b₀ := (ψ (e y₀)).2
  let O : Opens (UnderlyingSpace ℂ X) :=
    ⟨F.source ∩ F ⁻¹' (ball (0 : ℂ) r ×ˢ ball b₀ r),
      F.isOpen_inter_preimage (isOpen_ball.prod isOpen_ball)⟩
  have hOU : (O : Set (UnderlyingSpace ℂ X)) ⊆ e.source ∩ e ⁻¹' ψ.source := fun p hp ↦ hp.1
  have hOreg : O ≤ regularOpens ℂ X := fun p hp ↦ hU (hOU hp)
  have hy₀O : y₀ ∈ O :=
    ⟨hy₀, by rw [mem_preimage, hFy₀]; exact ⟨mem_ball_self hr, mem_ball_self hr⟩⟩
  have hmemO : ∀ w : ℂ × EuclideanSpace ℂ (Fin k), w ∈ ball (0 : ℂ) r ×ˢ ball b₀ r →
      F.symm w ∈ O := fun w hw ↦
    ⟨F.map_target (hrF hw), by rwa [mem_preimage, F.right_inv (hrF hw)]⟩
  have hcont : Continuous fun p : regularOpensInter (𝕜 := ℂ) O ↦ F p.1.1 :=
    F.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      fun p ↦ p.2.1
  let Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ
      ball (0 : ℂ) r × (⟨ball b₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℂ (Fin k))) :=
    { toFun := fun p ↦ (⟨(F p.1.1).1, p.2.2.1⟩, ⟨(F p.1.1).2, p.2.2.2⟩)
      invFun := fun w ↦ ⟨⟨F.symm (w.1.1, w.2.1), hOreg (hmemO _ ⟨w.1.2, w.2.2⟩)⟩,
        hmemO _ ⟨w.1.2, w.2.2⟩⟩
      left_inv := fun p ↦ Subtype.ext (Subtype.ext (F.left_inv p.2.1))
      right_inv := fun w ↦ by
        have h := F.right_inv (hrF (show (w.1.1, w.2.1) ∈ _ from ⟨w.1.2, w.2.2⟩))
        exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
      continuous_toFun :=
        ((continuous_fst.comp hcont).subtype_mk _).prodMk ((continuous_snd.comp hcont).subtype_mk _)
      continuous_invFun :=
        ((F.continuousOn_symm.comp_continuous
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd))
          fun w ↦ hrF ⟨w.1.2, w.2.2⟩).subtype_mk _).subtype_mk _ }
  refine ⟨O, hOreg, r, r, hr, hr, hy₀O, hOU, Φ, fun p ↦ rfl, fun p ↦ rfl, ?_⟩
  letI := regularChartedSpace (𝕜 := ℂ) hn
  intro c hc c' hc' x hx _
  obtain ⟨e₁, he₁, hx₁, hcx, hsymm⟩ :=
    exists_isAlgebraicChart_eqOn_of_mem_atlas_regularOpensInter hn hc hx
  obtain ⟨q', rfl⟩ := mem_iUnion.1 hc'
  have hxF := hOU x.2
  obtain ⟨L, hL, hLd⟩ := he.exists_injective_hasFDerivAt_comp_symm he₁ hx₁ hxF.1 hxF.2
    ((hψ.differentiableOn (by simp)).differentiableAt (ψ.open_source.mem_nhds hxF.2))
    ((hψs.differentiableOn (by simp)).differentiableAt
      (ψ.open_target.mem_nhds (ψ.map_source hxF.2)))
  rw [← hcx] at hLd
  refine ⟨L, hL, hLd.congr_of_eventuallyEq ?_⟩
  filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with y hy
  rw [← hsymm y hy]
  rfl

end UnderlyingSpace

end MMP
