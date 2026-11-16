module

public import MMP.AlgebraicTopology.BorelMoore.MayerVietorisGlue
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderMayerVietoris
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderInduction
public import MMP.AlgebraicTopology.FundamentalClass.ChartBall
public import MMP.AlgebraicTopology.OrientationClass.Point
public import MMP.AlgebraicTopology.PoincareDuality.Alexander

/-!
# Existence of the fundamental class of an oriented manifold (Iversen, IX.4.7)

Let `M` be a Hausdorff, second countable real `n`-manifold, modelled on a finite-dimensional real
normed space `H`, with an oriented atlas (`IsOrientedAtlas`: the transition maps have positive
Jacobian determinant), oriented in its charts by a basis `b` of `H`. Then `M` has a fundamental
class `μ_M ∈ H_n M`, and it is unique.

The fundamental class is a local notion: a class is fundamental as soon as, at every point `x`,
it is locally the class of one positively oriented simplex of the chart at `x`
(`isFundamentalClass_of_forall_exists`), the charts of an oriented atlas inducing the same local
orientations (`isLocallyHomologous_chartSimplexOf_of_det_pos`). Hence

* **uniqueness**: two fundamental classes differ by a top-degree cycle which is a relative
  boundary at every point, hence a boundary (Hatcher, Lemma 3.27(b) and the `lim¹` argument,
  `PoincareDuality.exists_d_eq_of_forall_isRelBoundary`); no connectedness is needed
  (`IsFundamentalClass.eq_of_isFundamentalClass_succ`);
* **existence**: by Bredon's induction on the open subsets of `M`
  (`isOpen_induction_chartedSpace`). An open subset of a chart domain has a global chart, hence a
  fundamental class; if the open sets `A` and `B` have fundamental classes `μ_A`, `μ_B`, their
  restrictions to `A ∩ B` agree by uniqueness, and the gluing step of the Borel–Moore
  Mayer–Vietoris sequence (`borelMooreHomology.exists_glue`) gives a class on `A ∪ B`
  restricting to both, which is fundamental by locality; a disjoint union of open sets with
  fundamental classes has one (`PoincareAlexander.glueChain`). In dimension `0` the manifold is
  discrete and the union step reduces to the disjoint-union step.

## Main results

* `MMP.FundamentalClass.isLocallyHomologous_chartSimplexOf_of_det_pos`.
* `MMP.isOrientedAtlas_opens`: an open subset of a manifold with an oriented atlas
  has an oriented atlas.
* `MMP.isFundamentalClass_of_forall_exists`: locality of fundamental classes.
* `MMP.IsFundamentalClass.eq_of_isFundamentalClass_succ`: uniqueness in positive
  dimension, without connectedness.
* `MMP.exists_isFundamentalClass_of_union`,
  `MMP.exists_isFundamentalClass_of_disjoint`: the Mayer–Vietoris and the
  disjoint-union steps.
* `MMP.exists_isFundamentalClass`: **existence of the fundamental class**.

## References

* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.7.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27, Theorem 3.26.
* [G. Bredon, *Topology and Geometry*][bredon1993], VI.7.9.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial Finsupp Manifold
open MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass MMP.FundamentalClass

universe u

namespace MMP

open MMP

namespace FundamentalClass

section orientation

variable {T : Type*} [TopologicalSpace T] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] {n : ℕ}

/-- **Charts with orientation-preserving transition induce the same local orientation**: if the
transition map `e⁻¹ ≫ e'` is differentiable at `e y` with positive Jacobian determinant, affine
simplices around `e y` and `e' y` positively oriented for `b` give locally homologous chart
simplices at `y`. -/
theorem isLocallyHomologous_chartSimplexOf_of_det_pos (b : Module.Basis (Fin n) ℝ H)
    {e e' : OpenPartialHomeomorph T H} {y : T} (hy : y ∈ e.source) (hy' : y ∈ e'.source)
    (hdiff : DifferentiableAt ℝ (e.symm ≫ₕ e') (e y))
    (hdet : 0 < LinearMap.det (fderiv ℝ (e.symm ≫ₕ e') (e y) : H →ₗ[ℝ] H))
    {v v' : Fin (n + 1) → H} (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e y)
    (hvt : range (affineSimplex v) ⊆ e.target)
    (hv' : IsOrientedSimplexAroundZero b fun k ↦ v' k - e' y)
    (hvt' : range (affineSimplex v') ⊆ e'.target) :
    IsLocallyHomologous y (chartSimplexOf e v hvt) (chartSimplexOf e' v' hvt') := by
  set f := e.symm ≫ₕ e'
  have hx : e y ∈ f.source := by
    simp only [f, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage, e.left_inv hy]
    exact ⟨e.map_source hy, hy'⟩
  have hfx : f (e y) = e' y := by
    simp [f, e.left_inv hy]
  obtain ⟨δ, hδ, hloc⟩ := isLocallyHomologous_of_hasFDerivAt (X := T) b b e'.open_target
    e'.continuousOn_symm e'.symm.injOn (f.open_source.mem_nhds hx) f.continuousOn hfx
    (e'.map_source hy') hdiff.hasFDerivAt
    (lt_of_lt_of_eq hdet (basis_det_comp_self b _).symm)
  obtain ⟨w, hw, hwW⟩ := exists_isOrientedSimplexAroundZero_subset b (e y)
    (Filter.inter_mem (Metric.ball_mem_nhds _ hδ) (f.open_source.mem_nhds hx))
  obtain ⟨hAO, hA⟩ := hloc w hw (hwW.trans inter_subset_left)
  have hwt : range (affineSimplex w) ⊆ e.target := fun z hz ↦ by
    have := (hwW hz).2
    simp only [f, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at this
    exact this.1
  set L := fderiv ℝ f (e y)
  set w' : Fin (n + 1) → H := fun k ↦ e' y + L (w k - e y)
  have hw'O : range (affineSimplex w') ⊆ e'.target := by
    rintro _ ⟨t, rfl⟩
    exact hAO t
  have hw' : IsOrientedSimplexAroundZero b fun k ↦ w' k - e' y := by
    have := hw.map_linearMap (L : H →ₗ[ℝ] H) (bH := b)
      (lt_of_lt_of_eq hdet (basis_det_comp_self b _).symm)
    convert this using 1
    funext k
    simp [w']
  have h1 : IsLocallyHomologous y (chartSimplexOf e w hwt) (chartSimplexOf e' w' hw'O) := by
    have := hA (chartSimplexOf e w hwt) (chartSimplexOf e' w' hw'O) (fun t ↦ ?_) (fun t ↦ rfl)
    · rwa [e'.left_inv hy'] at this
    · have hmem := (hwW ⟨t, rfl⟩).2
      simp only [f, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        mem_inter_iff, mem_preimage] at hmem
      simp only [chartSimplexOf_apply, f, OpenPartialHomeomorph.coe_trans,
        Function.comp_apply, e'.left_inv hmem.2]
  refine ((isLocallyHomologous_of_isOrientedSimplexAroundZero e hy hv hvt hw hwt
    (fun _ ↦ rfl) (fun _ ↦ rfl)).trans h1).trans ?_
  exact isLocallyHomologous_of_isOrientedSimplexAroundZero e' hy' hw' hw'O hv' hvt'
    (fun _ ↦ rfl) (fun _ ↦ rfl)

end orientation

end FundamentalClass

section opens

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {N : Type*} [TopologicalSpace N]
  [ChartedSpace H N]

/-- The transition map between the restrictions to an open set `U` of two charts of an oriented
atlas is differentiable with positive Jacobian determinant. -/
lemma differentiableAt_det_pos_subtypeRestr (hN : IsOrientedAtlas H N)
    {e e' : OpenPartialHomeomorph N H} (he : e ∈ atlas H N) (he' : e' ∈ atlas H N)
    {U : TopologicalSpace.Opens N} (hU : Nonempty U) {p : H}
    (hp : p ∈ ((e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU).source) :
    DifferentiableAt ℝ ((e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU) p ∧
      0 < LinearMap.det (fderiv ℝ ((e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU) p :
        H →ₗ[ℝ] H) := by
  have h := OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr hU e e'
  have hp' : p ∈ ((e.symm ≫ₕ e').restr (e.target ∩ e.symm ⁻¹' U)).source := by
    rwa [← h.source_eq]
  have hev : ((e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU : H → H) =ᶠ[𝓝 p]
      (e.symm ≫ₕ e' : H → H) :=
    Filter.eventuallyEq_of_mem
      (((e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU).open_source.mem_nhds hp)
      fun q hq ↦ h.eqOn hq
  obtain ⟨hdiff, hdet⟩ := hN e he e' he' p hp'.1
  exact ⟨hdiff.congr_of_eventuallyEq hev, by rwa [hev.fderiv_eq]⟩

/-- **An open subset of a manifold with an oriented atlas has an oriented atlas.** -/
theorem isOrientedAtlas_opens (hN : IsOrientedAtlas H N) (U : TopologicalSpace.Opens N) :
    IsOrientedAtlas H U := by
  rintro e ⟨_, ⟨x, rfl⟩, he⟩ e' ⟨_, ⟨x', rfl⟩, he'⟩ p hp
  rw [mem_singleton_iff] at he he'
  subst he he'
  exact differentiableAt_det_pos_subtypeRestr hN (chart_mem_atlas H x.1)
    (chart_mem_atlas H x'.1) ⟨x⟩ hp

end opens

section locality

variable {R : Type u} [CommRing R] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ChartedSpace H Z]
  {n : ℕ} {b : Module.Basis (Fin n) ℝ H}

/-- A fundamental class is locally the class of every oriented chart simplex. -/
lemma IsFundamentalClass.isLocallyClassOf
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) n} (hμ : IsFundamentalClass R b μ)
    {e : OpenPartialHomeomorph Z H} (he : e ∈ atlas H Z) {x : Z} (hx : x ∈ e.source)
    {v : Fin (n + 1) → H} (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e x)
    (hvt : range (affineSimplex v) ⊆ e.target) :
    IsLocallyClassOf R μ x (chartSimplexOf e v hvt) :=
  IsLocallyClassOf.of_restrict (chartOpens e) (x := ⟨x, hx⟩) (hμ e he ⟨x, hx⟩ v hv hvt)

/-- **Locality of the fundamental class.** On a manifold with an oriented atlas, a class which
at every point `x` is locally the class of one positively oriented simplex of the chart at `x`
is a fundamental class. -/
theorem isFundamentalClass_of_forall_exists (hZ : IsOrientedAtlas H Z)
    {ν : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) n}
    (h : ∀ x : Z, ∃ (v : Fin (n + 1) → H)
      (_ : IsOrientedSimplexAroundZero b fun k ↦ v k - chartAt H x x)
      (hvt : range (affineSimplex v) ⊆ (chartAt H x).target),
      IsLocallyClassOf R ν x (chartSimplexOf (chartAt H x) v hvt)) :
    IsFundamentalClass R b ν := by
  intro e he x v hv hvt
  obtain ⟨w, hw, hwt, hloc⟩ := h x.1
  have hh := isLocallyHomologous_chartSimplexOf hZ b (chart_mem_atlas H x.1) he
    (mem_chart_source H x.1) x.2 hw hwt hv hvt
  exact IsLocallyClassOf.restrict (chartOpens e) (hloc.of_isLocallyHomologous hh)

end locality

section uniqueness

open borelMooreHomology PoincareDuality

variable {R : Type u} [CommRing R] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ChartedSpace H Z]
  [SecondCountableTopology Z]

/-- **Uniqueness of the fundamental class in positive dimension**, with no connectedness
assumption: two fundamental classes differ by a cycle which is a relative boundary at every
point, hence a boundary. -/
theorem IsFundamentalClass.eq_of_isFundamentalClass_succ {m : ℕ}
    {b : Module.Basis (Fin (m + 1)) ℝ H}
    {μ μ' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) (m + 1 : ℕ)}
    (hμ : IsFundamentalClass R b μ) (hμ' : IsFundamentalClass R b μ') : μ' = μ := by
  set C := borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of Z)
  set ι := borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of Z) (m + 1)
  have hsurjπ := (ModuleCat.epi_iff_surjective (C.homologyπ (m + 1))).1 inferInstance
  obtain ⟨z, hz⟩ := hsurjπ (ι.hom μ)
  obtain ⟨z', hz'⟩ := hsurjπ (ι.hom μ')
  set ζ : C.X (m + 1) := C.iCycles (m + 1) (z' - z)
  have hζ : (C.d (m + 1) m).hom ζ = 0 :=
    congrArg (fun f ↦ ModuleCat.Hom.hom f (z' - z)) (C.iCycles_d (m + 1) m)
  have hS : ∀ x : Z, IsRelBoundary R (m + 1) {x}
      (truncFin (isCompact_singleton (x := (x : TopCat.of Z))) ζ) := by
    intro x
    set e₀ := chartAt H x
    have hx₀ : x ∈ e₀.source := mem_chart_source H x
    obtain ⟨v₀, hv₀, hvt₀⟩ := exists_isOrientedSimplexAroundZero_subset b (e₀ x)
      (e₀.open_target.mem_nhds (mem_chart_target H x))
    obtain ⟨hgen₀, -, φ₀, hφ₀, hφ₀Δ⟩ := localPackage (R := R) (Y := Z) b e₀ x hx₀ v₀ hv₀ hvt₀
    have h1 := hμ.isLocallyClassOf (chart_mem_atlas H x) hx₀ hv₀ hvt₀ z hz φ₀ hφ₀
    have h2 := hμ'.isLocallyClassOf (chart_mem_atlas H x) hx₀ hv₀ hvt₀ z' hz' φ₀ hφ₀
    have hpair : localPairing ((ζ.1 : _ → R)) φ₀ = 0 := by
      have := map_sub (chainPairing (X := TopCat.of Z) (x := x) hφ₀.1) (C.iCycles (m + 1) z')
        (C.iCycles (m + 1) z)
      rw [chainPairing_apply, chainPairing_apply, chainPairing_apply, h1, h2, sub_self] at this
      simpa [ζ, map_sub] using this
    obtain ⟨t, w, htw⟩ := hgen₀ _ (bd_truncFin_mem_inside isCompact_singleton hζ)
    have he := eval_eq_zero_of_mem_vanishing hφ₀.1 htw
    have hcob : coboundary R (m + 1) φ₀ = 0 := hφ₀.2
    rw [map_sub, map_sub, map_smul, hφ₀Δ, ← eval_coboundary, hcob] at he
    have heval := eval_truncFin (isCompact_singleton (x := (x : TopCat.of Z))) ζ
      (mem_singleton _) hφ₀.1
    erw [heval] at he
    obtain rfl : t = 0 := by simpa [hpair] using he
    rw [zero_smul, sub_zero] at htw
    exact ⟨w, htw⟩
  obtain ⟨W, hW⟩ := exists_d_eq_of_forall_isRelBoundary b hζ hS
  have hcyc : z' - z = C.toCycles (m + 2) (m + 1) W := by
    apply (ModuleCat.mono_iff_injective (C.iCycles (m + 1))).1 inferInstance
    have := ConcreteCategory.congr_hom (C.toCycles_i (m + 2) (m + 1)) W
    rw [ConcreteCategory.comp_apply] at this
    rw [this]
    exact hW.symm
  have h0 : C.homologyπ (m + 1) (z' - z) = 0 := by
    rw [hcyc]
    have := ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ (m + 2) (m + 1)) W
    rw [ConcreteCategory.comp_apply] at this
    exact this.trans (by rfl)
  rw [map_sub, sub_eq_zero, hz, hz'] at h0
  simpa using congrArg ι.inv h0

end uniqueness

section transport

open borelMooreHomology PoincareAlexander BorelMooreCross

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Z : Type u} [TopologicalSpace Z]

/-- A point lies in the target of the restriction of `e` to an open set `U` if and only if it lies
in the target of `e` and its preimage under `e` lies in `U`. -/
lemma mem_subtypeRestr_target_iff (e : OpenPartialHomeomorph Z H) {U : TopologicalSpace.Opens Z}
    (hU : Nonempty U) {y : H} :
    y ∈ (e.subtypeRestr hU).target ↔ y ∈ e.target ∧ e.symm y ∈ U := by
  simp [OpenPartialHomeomorph.subtypeRestr_def]

/-- The chart simplex of the restriction of a chart `e` to an open set `U`, read in the ambient
space, is the chart simplex of `e`. -/
lemma inclChainSimplex_chartSimplexOf_subtypeRestr {n : ℕ} (e : OpenPartialHomeomorph Z H)
    {U : TopologicalSpace.Opens Z} (hU : Nonempty U) {v : Fin (n + 1) → H}
    (hvt : range (affineSimplex v) ⊆ (e.subtypeRestr hU).target) :
    inclChainSimplex (Y := TopCat.of Z) U (chartSimplexOf (e.subtypeRestr hU) v hvt) =
      chartSimplexOf e v fun _ hy ↦ ((mem_subtypeRestr_target_iff e hU).1 (hvt hy)).1 := by
  ext t
  exact coe_subtypeRestr_symm_apply e hU (hvt ⟨t, rfl⟩)

variable {R : Type u} [CommRing R] [T2Space Z]

/-- If the cycle `x` represents `ν`, then `x|_{U'}`, read in `U'`, represents the push-forward to
`U'` of the restriction of `ν` to the preimage of `U'`. -/
lemma homologyEquiv_pushforward_restrict_subOpens (A : TopologicalSpace.Opens Z)
    {I : TopologicalSpace.Opens Z} (h : I ≤ A) {n : ℕ}
    (ν : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) n) (x : Cyc (R := R) (TopCat.of A) n)
    (hx : homologyEquiv R (TopCat.of A) n ν = Submodule.Quotient.mk x) :
    homologyEquiv R (TopCat.of I) n
      ((borelMooreHomology.pushforward R (ModuleCat.of R R) (subOpensInv (Y := TopCat.of Z) A h)
        (isProperMap_subOpensInv (Y := TopCat.of Z) A h) n).hom
          ((borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of A)
          (subOpens (Y := TopCat.of Z) A I) n).hom ν)) =
      Submodule.Quotient.mk (subRestrictCyc R (Y := TopCat.of Z) A h x) := by
  have h1 := homologyEquiv_restrict (Y := TopCat.of A) (subOpens (Y := TopCat.of Z) A I) ν x hx
  have h2 := (LinearEquiv.eq_symm_apply _).2 h1
  rw [h2, pushforward_eq_homologyMap]
  exact (congrArg (homologyEquiv R (TopCat.of I) n)
    (homologyMap_homologyEquiv_symm_mk R _ n _)).trans (LinearEquiv.apply_symm_apply _ _)

variable [ChartedSpace H Z] [FiniteDimensional ℝ H]

/-- **The fundamental class of `A` restricts to that of `I ≤ A`**, read in `I` through the
homeomorphism of `I` with its preimage in `A`. -/
theorem IsFundamentalClass.pushforward_subOpensInv (hZ : IsOrientedAtlas H Z) {n : ℕ}
    {b : Module.Basis (Fin n) ℝ H} (A : TopologicalSpace.Opens Z) {I : TopologicalSpace.Opens Z}
    (h : I ≤ A) {ν : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) n}
    (hν : IsFundamentalClass R b ν) :
    IsFundamentalClass R b ((borelMooreHomology.pushforward R (ModuleCat.of R R)
      (subOpensInv (Y := TopCat.of Z) A h) (isProperMap_subOpensInv (Y := TopCat.of Z) A h) n).hom
        ((borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of A)
          (subOpens (Y := TopCat.of Z) A I) n).hom ν)) := by
  refine isFundamentalClass_of_forall_exists (isOrientedAtlas_opens hZ I) fun x ↦ ?_
  let e := chartAt H x.1
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (chartAt H x x)
    ((chartAt H x).open_target.mem_nhds (mem_chart_target H x))
  refine ⟨v, hv, hvt, ?_⟩
  let xA : A := ⟨x.1, h x.2⟩
  have hvtA : range (affineSimplex v) ⊆ (chartAt H xA).target := fun y hy ↦ by
    have := (mem_subtypeRestr_target_iff e ⟨x⟩).1 (hvt hy)
    exact (mem_subtypeRestr_target_iff e ⟨xA⟩).2 ⟨this.1, h this.2⟩
  have h1 := hν.isLocallyClassOf (chart_mem_atlas H xA) (mem_chart_source H xA) hv hvtA
  let Δ' : Simplex (TopCat.of (subOpens (Y := TopCat.of Z) A I)) n :=
    (subOpensMap (Y := TopCat.of Z) A h).hom.comp (chartSimplexOf (chartAt H x) v hvt)
  have hΔ' : inclChainSimplex (subOpens (Y := TopCat.of Z) A I) Δ' =
      chartSimplexOf (chartAt H xA) v hvtA := by
    ext t
    change ((chartAt H x).symm (affineSimplex v t)).1 =
      ((chartAt H xA).symm (affineSimplex v t)).1
    exact (coe_subtypeRestr_symm_apply e ⟨x⟩ (hvt ⟨t, rfl⟩)).trans
      (coe_subtypeRestr_symm_apply e ⟨xA⟩ (hvtA ⟨t, rfl⟩)).symm
  have h2 := IsLocallyClassOf.restrict (subOpens (Y := TopCat.of Z) A I)
    (x := subOpensMap (Y := TopCat.of Z) A h x) (Δ := Δ') (by rwa [hΔ'])
  have h3 := IsLocallyClassOf.pushforward (subOpensInv (Y := TopCat.of Z) A h)
    (isProperMap_subOpensInv (Y := TopCat.of Z) A h)
    (fun y hy ↦ (subOpensHomeo (Y := TopCat.of Z) A h).symm.injective hy) h2
  have heq2 : (subOpensInv (Y := TopCat.of Z) A h).hom.comp Δ' =
      chartSimplexOf (chartAt H x) v hvt := by
    ext t
    rfl
  rwa [heq2] at h3

/-- A class whose restrictions to the members of an open cover are fundamental classes is a
fundamental class. -/
theorem isFundamentalClass_of_forall_restrict (hZ : IsOrientedAtlas H Z) {n : ℕ}
    {b : Module.Basis (Fin n) ℝ H} {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) n}
    (h : ∀ p : Z, ∃ U : TopologicalSpace.Opens Z, p ∈ U ∧
      IsFundamentalClass R b
        ((borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of Z) U n).hom μ)) :
    IsFundamentalClass R b μ := by
  refine isFundamentalClass_of_forall_exists hZ fun p ↦ ?_
  obtain ⟨U, hpU, hU⟩ := h p
  let pU : U := ⟨p, hpU⟩
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (chartAt H pU pU)
    ((chartAt H pU).open_target.mem_nhds (mem_chart_target H pU))
  have h0 := hU.isLocallyClassOf (chart_mem_atlas H pU) (mem_chart_source H pU) hv hvt
  have h1 := IsLocallyClassOf.of_restrict (Y := TopCat.of Z) U (x := pU) h0
  have hvt' : range (affineSimplex v) ⊆ (chartAt H p).target := fun y hy ↦
    ((mem_subtypeRestr_target_iff (chartAt H p) (U := U) ⟨pU⟩).1 (hvt hy)).1
  have hv' : IsOrientedSimplexAroundZero b fun k ↦ v k - chartAt H p p := hv
  refine ⟨v, hv', hvt', ?_⟩
  rwa [← inclChainSimplex_chartSimplexOf_subtypeRestr (chartAt H p) (U := U) ⟨pU⟩ hvt]

end transport

section mayerVietoris

open borelMooreHomology PoincareAlexander BorelMooreCross

variable {R : Type u} [CommRing R] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ChartedSpace H Z]
  [SecondCountableTopology Z]

/-- **The Mayer–Vietoris step**: if the open sets `A`, `B` covering a manifold with an oriented
atlas have fundamental classes, so does the manifold. -/
theorem exists_isFundamentalClass_of_union (hZ : IsOrientedAtlas H Z) {m : ℕ}
    {b : Module.Basis (Fin (m + 1)) ℝ H} (A B : TopologicalSpace.Opens Z)
    (hAB : (A : Set Z) ∪ B = univ)
    (hA : ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) (m + 1 : ℕ),
      IsFundamentalClass R b μ)
    (hB : ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (m + 1 : ℕ),
      IsFundamentalClass R b μ) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) (m + 1 : ℕ),
      IsFundamentalClass R b μ := by
  have : LocallyCompactSpace Z := ChartedSpace.locallyCompactSpace H Z
  obtain ⟨μA, hμA⟩ := hA
  obtain ⟨μB, hμB⟩ := hB
  obtain ⟨x, hx⟩ : ∃ x : Cyc (R := R) (TopCat.of A) (m + 1),
      Submodule.Quotient.mk x = homologyEquiv R (TopCat.of A) (m + 1) μA :=
    Submodule.Quotient.mk_surjective _ _
  obtain ⟨y, hy⟩ : ∃ y : Cyc (R := R) (TopCat.of B) (m + 1),
      Submodule.Quotient.mk y = homologyEquiv R (TopCat.of B) (m + 1) μB :=
    Submodule.Quotient.mk_surjective _ _
  have h1 := hμA.pushforward_subOpensInv hZ A (inf_le_left : A ⊓ B ≤ A)
  have h2 := hμB.pushforward_subOpensInv hZ B (inf_le_right : A ⊓ B ≤ B)
  have heq := h1.eq_of_isFundamentalClass_succ h2
  have hx' :=
    homologyEquiv_pushforward_restrict_subOpens A (inf_le_left : A ⊓ B ≤ A) μA x hx.symm
  have hy' :=
    homologyEquiv_pushforward_restrict_subOpens B (inf_le_right : A ⊓ B ≤ B) μB y hy.symm
  have hmk : (Submodule.Quotient.mk (subRestrictCyc R (Y := TopCat.of Z) A inf_le_left x) :
      HomQ (R := R) (TopCat.of ↥(A ⊓ B)) (m + 1)) =
      Submodule.Quotient.mk (subRestrictCyc R (Y := TopCat.of Z) B inf_le_right y) :=
    hx'.symm.trans ((congrArg (homologyEquiv R (TopCat.of ↥(A ⊓ B)) (m + 1)) heq).symm.trans hy')
  obtain ⟨w, hw⟩ := (mk_eq_mk_iff_exists _ _).1 hmk
  obtain ⟨S, T, hS, hT, hST, hBS, hAT⟩ := exists_mvSeparation A.isOpen B.isOpen hAB
  obtain ⟨z, hz, ⟨a, ha⟩, ⟨b', hb'⟩⟩ := exists_glue (Y := TopCat.of Z) (A := A) (B := B)
    (M := ModuleCat.of R R) hS hT hST hBS hAT (x := x.1) ((mem_cyc_iff _).1 x.2) (y := y.1)
    ((mem_cyc_iff _).1 y.2) (w := w) hw.symm
  set zc : Cyc (R := R) (TopCat.of Z) (m + 1) := ⟨z, (mem_cyc_iff _).2 hz⟩
  set μ := (homologyEquiv R (TopCat.of Z) (m + 1)).symm (Submodule.Quotient.mk zc)
  have hres : ∀ (U : TopologicalSpace.Opens Z) (xU : Cyc (R := R) (TopCat.of U) (m + 1))
      (μU : borelMooreHomology R (ModuleCat.of R R) (TopCat.of U) (m + 1 : ℕ))
      (_ : Submodule.Quotient.mk xU = homologyEquiv R (TopCat.of U) (m + 1) μU)
      (c : (BM R (TopCat.of U)).X (m + 1 + 1)),
      ((restrictChainMap R (ModuleCat.of R R) U).f (m + 1)).hom z = xU.1 +
        ((BM R (TopCat.of U)).d (m + 1 + 1) (m + 1)).hom c →
      (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of Z) U (m + 1 : ℕ)).hom μ =
        μU := by
    intro U xU μU hxU c hc
    apply (homologyEquiv R (TopCat.of U) (m + 1)).injective
    rw [homologyEquiv_restrict U μ zc (LinearEquiv.apply_symm_apply _ _), ← hxU]
    refine (mk_eq_mk_iff_exists _ _).2 ⟨c, ?_⟩
    rw [resCycOpen_coe]
    change _ = ((restrictChainMap R (ModuleCat.of R R) U).f (m + 1)).hom z - xU.1
    rw [hc]
    abel
  refine ⟨μ, isFundamentalClass_of_forall_restrict hZ fun p ↦ ?_⟩
  have hp : p ∈ (A : Set Z) ∪ B := hAB ▸ mem_univ p
  rcases hp with hpA | hpB
  · exact ⟨A, hpA, by rwa [hres A x μA hx a ha]⟩
  · exact ⟨B, hpB, by rwa [hres B y μB hy b' hb']⟩

end mayerVietoris

section disjoint

open borelMooreHomology PoincareAlexander BorelMooreCross Function

variable {R : Type u} [CommRing R] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ChartedSpace H Z]

/-- **The disjoint-union step**: if a manifold with an oriented atlas is the union of pairwise
disjoint open sets with fundamental classes, it has a fundamental class. -/
theorem exists_isFundamentalClass_of_disjoint (hZ : IsOrientedAtlas H Z) {n : ℕ}
    {b : Module.Basis (Fin n) ℝ H} {ι : Type*} (V : ι → TopologicalSpace.Opens Z)
    (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Z))) (hcov : ∀ y, ∃ l, y ∈ V l)
    (h : ∀ l, ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (V l)) n,
      IsFundamentalClass R b μ) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) n, IsFundamentalClass R b μ := by
  choose μV hμV using h
  have hc : ∀ l, ∃ c : Cyc (R := R) (TopCat.of (V l)) n,
      Submodule.Quotient.mk c = homologyEquiv R (TopCat.of (V l)) n (μV l) := fun l ↦
    Submodule.Quotient.mk_surjective _ _
  choose c hcμ using hc
  set g := glueChain (R := R) (Y := TopCat.of Z) V hdisj hcov fun l ↦ (c l).1
  have hg : g ∈ Cyc (R := R) (TopCat.of Z) n := by
    rcases n with _ | k
    · exact mem_cyc_zero g
    · rw [mem_cyc_iff]
      change ((BM R (TopCat.of Z)).d (k + 1) k).hom g = 0
      rw [d_glueChain]
      refine chain_ext hdisj hcov fun l ↦ ?_
      rw [res_glueChain, map_zero]
      exact (mem_cyc_iff _).1 (c l).2
  set μ := (homologyEquiv R (TopCat.of Z) n).symm (Submodule.Quotient.mk ⟨g, hg⟩)
  refine ⟨μ, isFundamentalClass_of_forall_restrict hZ fun p ↦ ?_⟩
  obtain ⟨l, hl⟩ := hcov p
  refine ⟨V l, hl, ?_⟩
  have : (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of Z) (V l) n).hom μ =
      μV l := by
    apply (homologyEquiv R (TopCat.of (V l)) n).injective
    rw [homologyEquiv_restrict (V l) μ ⟨g, hg⟩ (LinearEquiv.apply_symm_apply _ _), ← hcμ l]
    congr 1
    exact Subtype.ext (res_glueChain hdisj hcov _ l)
  exact this ▸ hμV l

end disjoint

section run

open borelMooreHomology PoincareAlexander BorelMooreCross

variable {R : Type u} [CommRing R] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]

/-- **The fundamental class of `S ≤ W` read in the preimage of `S` in `W`.** -/
theorem IsFundamentalClass.pushforward_subOpensMap (hM : IsOrientedAtlas H M) {n : ℕ}
    {b : Module.Basis (Fin n) ℝ H} (W : TopologicalSpace.Opens M) {S : TopologicalSpace.Opens M}
    (h : S ≤ W) {ν : borelMooreHomology R (ModuleCat.of R R) (TopCat.of S) n}
    (hν : IsFundamentalClass R b ν) :
    IsFundamentalClass R b ((borelMooreHomology.pushforward R (ModuleCat.of R R)
      (subOpensMap (Y := TopCat.of M) W h) (isProperMap_subOpensMap (Y := TopCat.of M) W h)
        n).hom ν) := by
  refine isFundamentalClass_of_forall_exists
    (isOrientedAtlas_opens (isOrientedAtlas_opens hM W) (subOpens (Y := TopCat.of M) W S))
    fun x ↦ ?_
  let e := chartAt H x.1.1
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (chartAt H x x)
    ((chartAt H x).open_target.mem_nhds (mem_chart_target H x))
  refine ⟨v, hv, hvt, ?_⟩
  let y : S := ⟨x.1.1, x.2⟩
  have hvtS : range (affineSimplex v) ⊆ (chartAt H y).target := fun z hz ↦ by
    have h1 := (mem_subtypeRestr_target_iff (chartAt H x.1) ⟨x⟩).1 (hvt hz)
    have h2 := (mem_subtypeRestr_target_iff e ⟨x.1⟩).1 h1.1
    refine (mem_subtypeRestr_target_iff e ⟨y⟩).2 ⟨h2.1, ?_⟩
    have h3 := h1.2
    rw [mem_subOpens] at h3
    rwa [← coe_subtypeRestr_symm_apply e ⟨x.1⟩ h1.1]
  have h1 := hν.isLocallyClassOf (chart_mem_atlas H y) (mem_chart_source H y) hv hvtS
  have h2 := IsLocallyClassOf.pushforward (subOpensMap (Y := TopCat.of M) W h)
    (isProperMap_subOpensMap (Y := TopCat.of M) W h)
    (fun z hz ↦ (subOpensHomeo (Y := TopCat.of M) W h).injective hz) h1
  have heq : (subOpensMap (Y := TopCat.of M) W h).hom.comp (chartSimplexOf (chartAt H y) v hvtS) =
      chartSimplexOf (chartAt H x) v hvt := by
    ext t
    have h1 := (mem_subtypeRestr_target_iff (chartAt H x.1) ⟨x⟩).1 (hvt ⟨t, rfl⟩)
    change ((chartAt H y).symm (affineSimplex v t)).1 =
      (((chartAt H x).symm (affineSimplex v t)).1).1
    exact (coe_subtypeRestr_symm_apply e ⟨y⟩ (hvtS ⟨t, rfl⟩)).trans
      ((coe_subtypeRestr_symm_apply e ⟨x.1⟩ h1.1).symm.trans (congrArg Subtype.val
        (coe_subtypeRestr_symm_apply (chartAt H x.1) ⟨x⟩ (hvt ⟨t, rfl⟩)).symm))
  rwa [heq] at h2

variable [SecondCountableTopology M]

/-- The union step of Bredon's induction on a manifold, in positive dimension. -/
lemma exists_isFundamentalClass_sup (hM : IsOrientedAtlas H M) {m : ℕ}
    {b : Module.Basis (Fin (m + 1)) ℝ H}
    {S T : TopologicalSpace.Opens M} (hS : ∃ μ : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of S) (m + 1 : ℕ), IsFundamentalClass R b μ)
    (hT : ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of T) (m + 1 : ℕ),
      IsFundamentalClass R b μ) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of ↥(S ⊔ T)) (m + 1 : ℕ),
      IsFundamentalClass R b μ := by
  obtain ⟨μS, hμS⟩ := hS
  obtain ⟨μT, hμT⟩ := hT
  refine exists_isFundamentalClass_of_union (isOrientedAtlas_opens hM (S ⊔ T))
    (subOpens (Y := TopCat.of M) (S ⊔ T) S) (subOpens (Y := TopCat.of M) (S ⊔ T) T) ?_
    ⟨_, hμS.pushforward_subOpensMap hM (S ⊔ T) le_sup_left⟩
    ⟨_, hμT.pushforward_subOpensMap hM (S ⊔ T) le_sup_right⟩
  ext p
  simp only [mem_union, mem_univ, iff_true, SetLike.mem_coe]
  exact p.2

end run

section chart

open borelMooreHomology

variable {R : Type u} [CommRing R] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- A space with a global chart `g` has a class which at every point is locally the class of
every positively oriented simplex of `g`. -/
lemma exists_forall_isLocallyClassOf_of_globalChart {Y : Type u} [TopologicalSpace Y]
    [T2Space Y] {n : ℕ} (b : Module.Basis (Fin n) ℝ H) (g : OpenPartialHomeomorph Y H)
    (hg : g.source = univ) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) n,
      ∀ (x : Y) (v : Fin (n + 1) → H) (_ : IsOrientedSimplexAroundZero b fun k ↦ v k - g x)
        (hvt : range (affineSimplex v) ⊆ g.target),
        IsLocallyClassOf R μ x (chartSimplexOf g v hvt) := by
  let : ChartedSpace H Y := g.singletonChartedSpace hg
  obtain ⟨μ, hμ⟩ := exists_isFundamentalClass_of_globalChart R b g hg fun e' he' ↦ by
    rw [show e' = g from he']
    exact Set.eqOn_refl _ _
  exact ⟨μ, fun x v hv hvt ↦ hμ.isLocallyClassOf (show g ∈ ({g} : Set _) from rfl)
    (hg ▸ mem_univ x) hv hvt⟩

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]

/-- The empty open set has a fundamental class. -/
lemma exists_isFundamentalClass_of_isEmpty (hM : IsOrientedAtlas H M) {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H) (S : TopologicalSpace.Opens M) (hS : ¬ Nonempty S) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of S) n, IsFundamentalClass R b μ :=
  ⟨0, isFundamentalClass_of_forall_exists (isOrientedAtlas_opens hM S) fun x ↦ (hS ⟨x⟩).elim⟩

/-- **The chart pieces of Bredon's induction**: an open subset of the domain of a chart has a
fundamental class. -/
theorem exists_isFundamentalClass_of_subset_source (hM : IsOrientedAtlas H M) {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H) {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (S : TopologicalSpace.Opens M) (hS : (S : Set M) ⊆ e.source) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of S) n, IsFundamentalClass R b μ := by
  by_cases hne : Nonempty S
  swap
  · exact exists_isFundamentalClass_of_isEmpty hM b S hne
  set g := e.subtypeRestr hne
  have hg : g.source = univ := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact eq_univ_of_forall fun x ↦ hS x.2
  obtain ⟨μ, hμ⟩ := exists_forall_isLocallyClassOf_of_globalChart (R := R) b g hg
  refine ⟨μ, isFundamentalClass_of_forall_exists (isOrientedAtlas_opens hM S) fun x ↦ ?_⟩
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (chartAt H x x)
    ((chartAt H x).open_target.mem_nhds (mem_chart_target H x))
  have hx : x ∈ g.source := hg ▸ mem_univ x
  obtain ⟨w, hw, hwt⟩ := exists_isOrientedSimplexAroundZero_subset b (g x)
    (g.open_target.mem_nhds (g.map_source hx))
  have hp : g x ∈ (g.symm ≫ₕ chartAt H x).source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨g.map_source hx, by rw [g.left_inv hx]; exact mem_chart_source H x⟩
  obtain ⟨hdiff, hdet⟩ := differentiableAt_det_pos_subtypeRestr hM he (chart_mem_atlas H x.1)
    hne hp
  have hh := isLocallyHomologous_chartSimplexOf_of_det_pos b hx (mem_chart_source H x) hdiff hdet
    hw hwt hv hvt
  exact ⟨v, hv, hvt, (hμ x w hw hwt).of_isLocallyHomologous hh⟩

end chart

section main

open borelMooreHomology Function

variable {R : Type u} [CommRing R] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]

/-- The disjoint-union step of Bredon's induction on a manifold. -/
lemma exists_isFundamentalClass_iSup (hM : IsOrientedAtlas H M) {n : ℕ}
    {b : Module.Basis (Fin n) ℝ H} {ι : Type*} (S : ι → TopologicalSpace.Opens M)
    (hdisj : Pairwise (Disjoint on fun l ↦ (S l : Set M)))
    (h : ∀ l, ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (S l)) n,
      IsFundamentalClass R b μ) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of ↥(⨆ l, S l)) n,
      IsFundamentalClass R b μ := by
  set W := ⨆ l, S l
  refine exists_isFundamentalClass_of_disjoint (isOrientedAtlas_opens hM W)
    (fun l ↦ subOpens (Y := TopCat.of M) W (S l)) ?_ ?_ fun l ↦ ?_
  · intro l l' hll'
    refine Set.disjoint_left.2 fun p hp hp' ↦ ?_
    have h1 : p.1 ∈ (S l : Set M) := (mem_subOpens (Y := TopCat.of M) W).1 hp
    have h2 : p.1 ∈ (S l' : Set M) := (mem_subOpens (Y := TopCat.of M) W).1 hp'
    exact Set.disjoint_left.1 (hdisj hll') h1 h2
  · intro p
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 p.2
    exact ⟨l, (mem_subOpens (Y := TopCat.of M) W (U' := S l) (x := p)).2 hl⟩
  · obtain ⟨μ, hμ⟩ := h l
    exact ⟨_, hμ.pushforward_subOpensMap hM W (le_iSup S l)⟩

omit [FiniteDimensional ℝ H] in
/-- A manifold of dimension `0` is discrete. -/
lemma isOpen_of_basis_zero (b : Module.Basis (Fin 0) ℝ H) (s : Set M) : IsOpen s := by
  have : Subsingleton H := b.repr.toEquiv.subsingleton
  have h1 : ∀ x : M, IsOpen ({x} : Set M) := fun x ↦ by
    have : (chartAt H x).source = {x} := Set.eq_singleton_iff_unique_mem.2
      ⟨mem_chart_source H x, fun y hy ↦
        (chartAt H x).injOn hy (mem_chart_source H x) (Subsingleton.elim _ _)⟩
    rw [← this]
    exact (chartAt H x).open_source
  rw [← biUnion_of_singleton s]
  exact isOpen_biUnion fun x _ ↦ h1 x

/-- The union step of Bredon's induction on a manifold of dimension `0`. -/
lemma exists_isFundamentalClass_sup_zero (hM : IsOrientedAtlas H M)
    {b : Module.Basis (Fin 0) ℝ H} {S T : TopologicalSpace.Opens M}
    (hS : ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of S) (0 : ℕ),
      IsFundamentalClass R b μ)
    (hT : ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of T) (0 : ℕ),
      IsFundamentalClass R b μ) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of ↥(S ⊔ T)) (0 : ℕ),
      IsFundamentalClass R b μ := by
  set T' : TopologicalSpace.Opens M := ⟨(T : Set M) \ S, isOpen_of_basis_zero b _⟩
  have hT'T : T' ≤ T := fun p hp ↦ hp.1
  obtain ⟨μT, hμT⟩ := hT
  have hT' : ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of T') (0 : ℕ),
      IsFundamentalClass R b μ := ⟨_, hμT.pushforward_subOpensInv hM T hT'T⟩
  let F : Bool → TopologicalSpace.Opens M := fun l ↦ bif l then S else T'
  have hF : (⨆ l, F l) = S ⊔ T := by
    apply le_antisymm
    · exact iSup_le <| Bool.forall_bool.2 ⟨hT'T.trans le_sup_right, le_sup_left⟩
    · refine sup_le (le_iSup F true) fun p hp ↦ ?_
      by_cases hpS : p ∈ S
      · exact le_iSup F true hpS
      · exact le_iSup F false ⟨hp, hpS⟩
  have := exists_isFundamentalClass_iSup (R := R) (b := b) hM F (by
    intro l l' hll'
    cases l <;> cases l'
    · exact absurd rfl hll'
    · exact Set.disjoint_left.2 fun p hp hp' ↦ hp.2 hp'
    · exact Set.disjoint_left.2 fun p hp hp' ↦ hp'.2 hp
    · exact absurd rfl hll') (Bool.forall_bool.2 ⟨hT', hS⟩)
  rwa [hF] at this

variable [SecondCountableTopology M]

/-- **Existence of the fundamental class of an oriented manifold** (Iversen, IX.4.7; Hatcher,
Lemma 3.27(a) with the `lim¹` argument): a Hausdorff, second countable manifold modelled on a
finite-dimensional real normed space `H`, with an oriented atlas, has a fundamental class for the
orientation of every basis `b` of `H`. -/
theorem exists_isFundamentalClass (hM : IsOrientedAtlas H M) {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n, IsFundamentalClass R b μ := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let P : Set M → Prop := fun s ↦ ∀ hs : IsOpen s,
    ∃ μ : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (⟨s, hs⟩ : TopologicalSpace.Opens M)) n, IsFundamentalClass R b μ
  have key : P univ := by
    refine isOpen_induction_chartedSpace (H := H) (P := P) ?_ ?_ ?_ ?_ isOpen_univ
    · intro e he s _ hse _ _ hs'
      exact exists_isFundamentalClass_of_subset_source hM b he ⟨s, hs'⟩ hse
    · intro hs
      exact exists_isFundamentalClass_of_isEmpty hM b ⟨∅, hs⟩ fun ⟨x⟩ ↦ x.2
    · intro s t hs ht hPs hPt _ hst
      have heq : (⟨s ∪ t, hst⟩ : TopologicalSpace.Opens M) = ⟨s, hs⟩ ⊔ ⟨t, ht⟩ := rfl
      rw [heq]
      rcases n with _ | m
      · exact exists_isFundamentalClass_sup_zero hM (hPs hs) (hPt ht)
      · exact exists_isFundamentalClass_sup hM (hPs hs) (hPt ht)
    · intro s hs hdisj hP hs'
      have heq : (⟨⋃ i, s i, hs'⟩ : TopologicalSpace.Opens M) =
          ⨆ i, (⟨s i, hs i⟩ : TopologicalSpace.Opens M) := by
        ext x
        simp
      rw [heq]
      exact exists_isFundamentalClass_iSup hM (fun i ↦ ⟨s i, hs i⟩) hdisj fun i ↦ hP i (hs i)
  obtain ⟨μU, hμU⟩ := key isOpen_univ
  let U : TopologicalSpace.Opens M := ⟨univ, isOpen_univ⟩
  let f : TopCat.of U ⟶ TopCat.of M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hf : IsProperMap f :=
    (show IsClosed (U : Set M) from isClosed_univ).isClosedEmbedding_subtypeVal.isProperMap
  refine ⟨(borelMooreHomology.pushforward R (ModuleCat.of R R) f hf n).hom μU,
    isFundamentalClass_of_forall_exists hM fun x ↦ ?_⟩
  let xU : U := ⟨x, trivial⟩
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (chartAt H xU xU)
    ((chartAt H xU).open_target.mem_nhds (mem_chart_target H xU))
  have h1 := IsLocallyClassOf.pushforward f hf (fun y hy ↦ Subtype.val_injective hy)
    (hμU.isLocallyClassOf (chart_mem_atlas H xU) (mem_chart_source H xU) hv hvt)
  have hvt' : range (affineSimplex v) ⊆ (chartAt H x).target := fun y hy ↦
    ((mem_subtypeRestr_target_iff (chartAt H x) (U := U) ⟨xU⟩).1 (hvt hy)).1
  have hv' : IsOrientedSimplexAroundZero b fun k ↦ v k - chartAt H x x := hv
  have heq : f.hom.comp (chartSimplexOf (chartAt H xU) v hvt) =
      chartSimplexOf (chartAt H x) v hvt' := by
    ext t
    exact coe_subtypeRestr_symm_apply (chartAt H x) (U := U) ⟨xU⟩ (hvt ⟨t, rfl⟩)
  rw [heq] at h1
  exact ⟨v, hv', hvt', h1⟩

end main

end MMP
