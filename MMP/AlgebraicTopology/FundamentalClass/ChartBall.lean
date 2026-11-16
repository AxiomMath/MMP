module

public import MMP.AlgebraicTopology.FundamentalClass.Euclidean
public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import MMP.AlgebraicTopology.SingularHomology.ChartSimplexLocalHomology

/-!
# The fundamental class of a chart ball (Fulton, §19.1)

A space `Y` with one *global chart* `g : Y → V` (a homeomorphism onto an open subset of a
finite-dimensional real normed space `V`, with `g.source = univ`) and an atlas all of whose charts
agree with `g` on their domains (for instance the single chart `g`, or restrictions of it) has a
fundamental class for the orientation of any basis `b` of `V`: the restriction of `μ_{ℝ^N}` to the
open set `L⁻¹ (g Y)`, pushed forward along `y ↦ g⁻¹ (L y)` (`L : ℝ^N ≅ V` carrying the standard
basis to `b`). This gives the fundamental class `μ_U` of a chart ball `U ⊆ M` charted by the
single chart `e'|_U` (step (B1) of `lem_ext_c19_orientation_class_cap_fundamental`).

## Main results

* `MMP.FundamentalClass.isOrientationPreserving_of_eqOn`: a homeomorphism which
  in the charts of the source and a global chart `g` of the target is a linear isomorphism `L`
  is orientation preserving from `b` to `L b`.
* `MMP.FundamentalClass.exists_isFundamentalClass_of_globalChart`: a space with a
  global chart has a fundamental class.
-/

@[expose] public noncomputable section

open Set Topology

universe u

namespace MMP

open ThomClass

namespace FundamentalClass

/-- The inverse of the restriction of a chart to an open set is the inverse of the chart. -/
lemma coe_subtypeRestr_symm_apply {X H : Type*} [TopologicalSpace X] [TopologicalSpace H]
    (e : OpenPartialHomeomorph X H) {U : TopologicalSpace.Opens X} (hU : Nonempty U) {y : H}
    (hy : y ∈ (e.subtypeRestr hU).target) : ((e.subtypeRestr hU).symm y : X) = e.symm y := by
  have h := (e.subtypeRestr hU).right_inv hy
  have hs := (e.subtypeRestr hU).map_target hy
  rw [OpenPartialHomeomorph.subtypeRestr_coe] at h
  rw [OpenPartialHomeomorph.subtypeRestr_source] at hs
  generalize (e.subtypeRestr hU).symm y = z at h hs ⊢
  rw [← h]
  exact (e.left_inv hs).symm

section Orientation

variable {H H' : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] [AddCommGroup H'] [Module ℝ H'] [TopologicalSpace H'] [ContinuousAdd H']
  [ContinuousSMul ℝ H'] {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace H M] [ChartedSpace H' M']

/-- A homeomorphism `φ : M ≃ₜ M'` which in every chart `e` of `M` and a chart `g` of `M'`
containing the domains of all charts of `M'`, and agreeing with them there, is a linear
isomorphism `L` (`g ∘ φ ∘ e⁻¹ = L` on the image of `e`) is orientation preserving from the
orientation of a basis `b` to that of `L b`. -/
theorem isOrientationPreserving_of_eqOn {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (L : H ≃ₗ[ℝ] H') (φ : M ≃ₜ M') (g : OpenPartialHomeomorph M' H')
    (hφ : ∀ e ∈ atlas H M, ∀ y ∈ e.target, φ (e.symm y) ∈ g.source ∧ g (φ (e.symm y)) = L y)
    (hg : ∀ e' ∈ atlas H' M', e'.source ⊆ g.source ∧ EqOn e' g e'.source) :
    IsOrientationPreserving b (b.map L) φ := by
  intro e he e' he' x hx hx' v hv hvt v' hv' hvt'
  have hφx : g (φ x) = L (e x) := by
    rw [← (hφ e he (e x) (e.map_source hx)).2, e.left_inv hx]
  have hge' : e' (φ x) = g (φ x) := (hg e' he').2 hx'
  have hA : ∀ t, affineSimplex (L ∘ v) t = L (affineSimplex v t) := fun t ↦ by
    simp only [affineSimplex_apply, map_sum, map_smul, Function.comp_apply]
  have hsymm : ∀ y ∈ e'.target, e'.symm y ∈ g.source ∧ g (e'.symm y) = y := fun y hy ↦ by
    have hs := e'.map_target hy
    exact ⟨(hg e' he').1 hs, by rw [← (hg e' he').2 hs, e'.right_inv hy]⟩
  refine isLocallyHomologous_of_isOrientedSimplexAroundZero g (x := φ x)
    ((hg e' he').1 hx') (b := b.map L) (v := L ∘ v) (w := v') ?_ ?_ (hge' ▸ hv') ?_
    (fun t ↦ ?_) (fun t ↦ ?_)
  · convert hv.map L using 1
    funext k
    simp [hφx]
  · rintro _ ⟨t, rfl⟩
    rw [hA, ← (hφ e he _ (hvt ⟨t, rfl⟩)).2]
    exact g.map_source (hφ e he _ (hvt ⟨t, rfl⟩)).1
  · rintro _ ⟨t, rfl⟩
    rw [← (hsymm _ (hvt' ⟨t, rfl⟩)).2]
    exact g.map_source (hsymm _ (hvt' ⟨t, rfl⟩)).1
  · change φ (e.symm (affineSimplex v t)) = g.symm (affineSimplex (L ∘ v) t)
    rw [hA, ← (hφ e he _ (hvt ⟨t, rfl⟩)).2, g.left_inv (hφ e he _ (hvt ⟨t, rfl⟩)).1]
  · change e'.symm (affineSimplex v' t) = g.symm (affineSimplex v' t)
    rw [← (hsymm _ (hvt' ⟨t, rfl⟩)).2, g.left_inv (hsymm _ (hvt' ⟨t, rfl⟩)).1,
      (hsymm _ (hvt' ⟨t, rfl⟩)).2]

end Orientation

section GlobalChart

variable (R : Type u) [CommRing R] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ChartedSpace V Y]

/-- The open set `L⁻¹ (g Y)` of `W`, for a chart `g` of `Y` and a homeomorphism `L : W ≃ₜ V`. -/
def globalChartOpens {W : Type u} [TopologicalSpace W] (L : W ≃ₜ V)
    (g : OpenPartialHomeomorph Y V) : TopologicalSpace.Opens W :=
  ⟨L ⁻¹' g.target, g.open_target.preimage L.continuous⟩

/-- The bijection `L⁻¹ (g Y) ≃ Y`, `y ↦ g⁻¹ (L y)`, for a global chart `g` of `Y` (defined at
every point) and a homeomorphism `L`. -/
def globalChartEquiv {W : Type u} [TopologicalSpace W] (L : W ≃ₜ V)
    (g : OpenPartialHomeomorph Y V) (hg : ∀ x, x ∈ g.source) :
    globalChartOpens L g ≃ Y where
  toFun y := g.symm (L y.1)
  invFun x := ⟨L.symm (g x), show L (L.symm (g x)) ∈ g.target by
    rw [L.apply_symm_apply]
    exact g.map_source (hg x)⟩
  left_inv y := by
    apply Subtype.ext
    change L.symm (g (g.symm (L y.1))) = y.1
    rw [g.right_inv y.2, L.symm_apply_apply]
  right_inv x := by
    change g.symm (L (L.symm (g x))) = x
    rw [L.apply_symm_apply, g.left_inv (hg x)]

/-- The homeomorphism `L⁻¹ (g Y) ≃ₜ Y`, `y ↦ g⁻¹ (L y)`, for a global chart `g` of `Y` (defined
at every point) and a homeomorphism `L`. -/
def globalChartHomeomorph {W : Type u} [TopologicalSpace W] (L : W ≃ₜ V)
    (g : OpenPartialHomeomorph Y V) (hg : ∀ x, x ∈ g.source) :
    globalChartOpens L g ≃ₜ Y where
  toEquiv := globalChartEquiv L g hg
  continuous_toFun := g.continuousOn_symm.comp_continuous
    (L.continuous.comp continuous_subtype_val) fun y ↦ y.2
  continuous_invFun :=
    (L.symm.continuous.comp (g.continuousOn.comp_continuous continuous_id hg)).subtype_mk _

/-- **The fundamental class of a chart ball.** A space `Y` with a global chart `g` (defined on all
of `Y`) such that every chart of `Y` agrees with `g` on its domain — e.g. a chart ball of a
manifold charted by the single chart `e'|_U` — has a fundamental class for the orientation of
every basis `b` of the model space. -/
theorem exists_isFundamentalClass_of_globalChart {N : ℕ} (b : Module.Basis (Fin N) ℝ V)
    (g : OpenPartialHomeomorph Y V) (hg : g.source = univ)
    (hatlas : ∀ e ∈ atlas V Y, EqOn e g e.source) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) N, IsFundamentalClass R b μ := by
  set L : (Fin N → ULift.{u} ℝ) ≃ₗ[ℝ] V := (liftEuclideanBasis N).equiv b (Equiv.refl _)
  let Lh : (Fin N → ULift.{u} ℝ) ≃ₜ V := L.toContinuousLinearEquiv.toHomeomorph
  have hL : (liftEuclideanBasis N).map L = b := by
    refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
    rw [Module.Basis.map_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hg' : ∀ x, x ∈ g.source := fun x ↦ hg ▸ mem_univ x
  set T := globalChartOpens Lh g
  have hT := (isFundamentalClass_euclideanClass R N).restrict T
  set φ := globalChartHomeomorph Lh g hg'
  have hφ := hT.pushforward_homeomorph R φ
    (isOrientationPreserving_of_eqOn _ L φ g ?_ fun e he ↦ ⟨hg ▸ subset_univ _, hatlas e he⟩)
  · exact ⟨_, hL ▸ hφ⟩
  · rintro e ⟨_, ⟨x, rfl⟩, rfl⟩ y hy
    refine ⟨hg' _, ?_⟩
    change g (g.symm (Lh (((chartAt _ x.1).subtypeRestr ⟨x⟩).symm y).1)) = L y
    refine (g.right_inv (((chartAt _ x.1).subtypeRestr ⟨x⟩).symm y).2).trans ?_
    rw [coe_subtypeRestr_symm_apply _ _ hy]
    rfl

end GlobalChart

end FundamentalClass

end MMP
