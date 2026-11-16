module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AnalyticSubsetComplement
public import MMP.AlgebraicGeometry.AnalytificationChartTransition
public import MMP.Analysis.Complex.Coherent.OkaWeierstrassReduction

/-!
# Rational subspaces of a complex torus

Let `E` be a finite-dimensional real vector space and `Λ ⊆ E` a full lattice, so that `E / Λ`
is a compact torus. A real subspace `W ⊆ E` is *rational* when it is spanned by the lattice
points it contains, `span_ℝ (W ∩ Λ) = W`; equivalently the image of `W` in `E / Λ` is a closed
subtorus. This file proves the topological half of the rationality theorem for the image `V` of
`H¹(S, 𝒪_S)` in the Jacobian of an ample curve `C` on a smooth projective surface `S`:

* if `W` is locally, near `0`, the whole of the subgroup `W + Λ` (that is, `‖w + μ‖ < ε` with
  `w ∈ W`, `μ ∈ Λ` forces `w + μ ∈ W`), then `W` is rational: every point of `W` is uniformly
  close to a lattice point of `W`, and scaling down makes `W` the closure of the span of these;
* if `W + Λ` is closed, then `W` is rational: by Baire's theorem on the closed set `W + Λ`, one of
  the countably many translates `W + μ` has interior in it, which is the local condition above;
* a countable family of closed analytic subsets covering a connected Baire space contains the
  whole space (Baire's theorem and the identity theorem);
* the inverse image of a Zariski-closed subset of a scheme `X` of finite type over `ℂ` under a
  map `N → X(ℂ)` holomorphic in charts is analytic, since on an affine chart the closed set is
  cut out by polynomials in the coordinates. So if such a map from a complex vector space has
  image in countably many Zariski-closed sets, its image lies in one of them. Applied to the
  uniformisation of the Jacobian on `V` and the image closures of the countably many algebraic
  families of line bundles, this puts `exp(V)` inside one algebraic image closure.

## Main results

* `MMP.Analytic.SurfaceHodge.exists_norm_sub_le_of_isZLattice`: points of `E` are uniformly
  close to the lattice.
* `MMP.Analytic.SurfaceHodge.span_inter_eq_of_forall_norm_lt`: the local criterion for
  rationality.
* `MMP.Analytic.SurfaceHodge.span_inter_eq_of_addSubgroup`: a subspace is rational when some
  subgroup containing it and the lattice coincides with it near `0`.
* `MMP.Analytic.SurfaceHodge.span_inter_eq_of_isClosed_add`: a subspace whose sum with the
  lattice is closed is rational.
* `MMP.Analytic.SurfaceHodge.isClosed_of_isLocallyAnalytic`: a locally analytic subset is closed.
* `MMP.Analytic.SurfaceHodge.exists_eq_univ_of_iUnion_eq_univ`,
  `MMP.Analytic.SurfaceHodge.exists_subset_of_subset_iUnion`: one member of a countable cover of
  a connected Baire space (a complex vector space) by locally analytic subsets is everything.
* `MMP.Analytic.SurfaceHodge.isLocallyAnalytic_preimage_toScheme`: the inverse image of a
  Zariski-closed set under a map to `X(ℂ)` holomorphic in charts is locally analytic.
* `MMP.Analytic.SurfaceHodge.exists_forall_mem_of_forall_mem_iUnion`: a holomorphic image of a
  complex vector space covered by countably many Zariski-closed sets lies in one of them.

## Implementation notes

Rationality is stated as `Submodule.span ℝ ((W : Set E) ∩ Λ) = W` for `W : Submodule ℝ E` and
`Λ : Submodule ℤ E` with `DiscreteTopology Λ` and `IsZLattice ℝ Λ`, the form in which the
logarithmic coordinates `MMP.Conductor.exists_isZLattice_exponential_of_isProjective` give the
period lattice of a curve. A complex subspace `V` enters as `V.restrictScalars ℝ`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
* [D. Mumford, *Abelian varieties*], §1.
-/

@[expose] public section

open Module Pointwise Metric Set

namespace MMP.Analytic.SurfaceHodge

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- Every point of `E` lies within a fixed distance of the full lattice `Λ`. -/
theorem exists_norm_sub_le_of_isZLattice :
    ∃ R : ℝ, ∀ x : E, ∃ μ ∈ Λ, ‖x - μ‖ ≤ R := by
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  refine ⟨∑ i, ‖b i‖, fun x => ⟨ZSpan.floor b x, ?_, ?_⟩⟩
  · exact (Basis.ofZLatticeBasis_span ℝ Λ (Module.Free.chooseBasis ℤ Λ)).le
      (ZSpan.floor b x).2
  · rw [← ZSpan.fract_apply]
    exact ZSpan.norm_fract_le b x

variable {Λ}

omit [FiniteDimensional ℝ E] [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
/-- If near `0` the subgroup `W + Λ` is contained in `W`, then near each centre `y` the points of
`W + Λ` lie in a single translate `W + ν`. -/
theorem exists_forall_sub_mem_of_forall_norm_lt {W : Submodule ℝ E} {ε : ℝ}
    (h : ∀ w ∈ W, ∀ μ ∈ Λ, ‖w + μ‖ < ε → w + μ ∈ W) (y : E) :
    ∃ ν ∈ Λ, ∀ w ∈ W, ∀ μ ∈ Λ, w + μ ∈ ball y (ε / 2) → μ - ν ∈ W := by
  by_cases hy : ∃ w ∈ W, ∃ μ ∈ Λ, w + μ ∈ ball y (ε / 2)
  · obtain ⟨w₀, hw₀, ν, hν, hb⟩ := hy
    refine ⟨ν, hν, fun w hw μ hμ hb' => ?_⟩
    have hlt : ‖(w - w₀) + (μ - ν)‖ < ε := by
      rw [show (w - w₀) + (μ - ν) = (w + μ - y) - (w₀ + ν - y) by abel]
      calc ‖(w + μ - y) - (w₀ + ν - y)‖ ≤ ‖w + μ - y‖ + ‖w₀ + ν - y‖ := norm_sub_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add (mem_ball_iff_norm.1 hb') (mem_ball_iff_norm.1 hb)
        _ = ε := add_halves ε
    simpa using W.sub_mem (h _ (W.sub_mem hw hw₀) _ (Λ.sub_mem hμ hν) hlt) (W.sub_mem hw hw₀)
  · exact ⟨0, Λ.zero_mem, fun w hw μ hμ hb => (hy ⟨w, hw, μ, hμ, hb⟩).elim⟩

/-- **The local criterion for rationality.** If near `0` the subgroup `W + Λ` is contained in the
real subspace `W`, then `W` is spanned by the lattice points it contains. -/
theorem span_inter_eq_of_forall_norm_lt {W : Submodule ℝ E} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ w ∈ W, ∀ μ ∈ Λ, ‖w + μ‖ < ε → w + μ ∈ W) :
    Submodule.span ℝ ((W : Set E) ∩ Λ) = W := by
  obtain ⟨R, hR⟩ := exists_norm_sub_le_of_isZLattice Λ
  obtain ⟨t, -, htf, ht⟩ := (isCompact_closedBall (0 : E) R).finite_cover_balls (half_pos hε)
  choose ν hνΛ hν using exists_forall_sub_mem_of_forall_norm_lt h
  obtain ⟨M, hM⟩ := (htf.image fun y => ‖ν y‖).bddAbove
  -- every point of `W` is uniformly close to a lattice point of `W`
  have hclose : ∀ w ∈ W, ∃ u ∈ (W : Set E) ∩ Λ, ‖w - u‖ ≤ R + M := by
    intro w hw
    obtain ⟨μ, hμ, hwμ⟩ := hR w
    have hd : w + -μ ∈ closedBall (0 : E) R := by
      rwa [mem_closedBall_zero_iff, ← sub_eq_add_neg]
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (ht hd)
    refine ⟨μ + ν y, ⟨?_, Λ.add_mem hμ (hνΛ y)⟩, ?_⟩
    · rw [show μ + ν y = w - (w + (-μ - ν y)) by abel]
      exact W.sub_mem hw (W.add_mem hw (hν y w hw (-μ) (Λ.neg_mem hμ) hy))
    · rw [show w - (μ + ν y) = (w - μ) - ν y by abel]
      exact (norm_sub_le _ _).trans (add_le_add hwμ (hM ⟨y, hyt, rfl⟩))
  obtain ⟨u₀, -, hu₀⟩ := hclose 0 W.zero_mem
  have hRM : 0 ≤ R + M := (norm_nonneg _).trans hu₀
  -- scaling down: `W` lies in the closure of the span of `W ∩ Λ`
  refine le_antisymm (Submodule.span_le.2 Set.inter_subset_left) fun w hw => ?_
  set W₀ := Submodule.span ℝ ((W : Set E) ∩ Λ)
  rw [← SetLike.mem_coe, ← W₀.closed_of_finiteDimensional.closure_eq, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + M) / δ)
  have hNpos : (0 : ℝ) < N := (div_nonneg hRM hδ.le).trans_lt hN
  obtain ⟨u, hu, hwu⟩ := hclose ((N : ℝ) • w) (W.smul_mem _ hw)
  refine ⟨(N : ℝ)⁻¹ • u, W₀.smul_mem _ (Submodule.subset_span hu), ?_⟩
  rw [dist_eq_norm, show w - (N : ℝ)⁻¹ • u = (N : ℝ)⁻¹ • ((N : ℝ) • w - u) by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hNpos.ne', one_smul],
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hNpos)]
  calc (N : ℝ)⁻¹ * ‖(N : ℝ) • w - u‖ ≤ (N : ℝ)⁻¹ * (R + M) :=
        mul_le_mul_of_nonneg_left hwu (inv_nonneg.2 hNpos.le)
    _ < δ := by
      rw [inv_mul_lt_iff₀ hNpos]
      rwa [div_lt_iff₀ hδ] at hN

/-- **Rationality from a subgroup with tangent space `W`.** If an additive subgroup `G ⊆ E`
contains the real subspace `W` and the lattice `Λ`, and near `0` every point of `G` lies in `W`,
then `W` is spanned by the lattice points it contains. -/
theorem span_inter_eq_of_addSubgroup {W : Submodule ℝ E} (G : AddSubgroup E)
    (hW : (W : Set E) ⊆ G) (hΛ : (Λ : Set E) ⊆ G) {ε : ℝ} (hε : 0 < ε)
    (hG : ∀ x ∈ G, ‖x‖ < ε → x ∈ W) :
    Submodule.span ℝ ((W : Set E) ∩ Λ) = W :=
  span_inter_eq_of_forall_norm_lt hε fun _ hw _ hμ hlt =>
    hG _ (G.add_mem (hW hw) (hΛ hμ)) hlt

/-- **Rationality from closedness.** If `W + Λ` is closed, then the real subspace `W` is spanned
by the lattice points it contains. -/
theorem span_inter_eq_of_isClosed_add {W : Submodule ℝ E}
    (hS : IsClosed ((W : Set E) + (Λ : Set E))) :
    Submodule.span ℝ ((W : Set E) ∩ Λ) = W := by
  set S := (W : Set E) + (Λ : Set E)
  have : CompleteSpace S := hS.completeSpace_coe
  have : Nonempty S := ⟨⟨0, Set.mem_add.2 ⟨0, W.zero_mem, 0, Λ.zero_mem, add_zero 0⟩⟩⟩
  let A : Λ → Set S := fun μ => {s | (s : E) - μ ∈ W}
  have hA : ∀ μ, IsClosed (A μ) := fun μ =>
    W.closed_of_finiteDimensional.preimage (continuous_subtype_val.sub continuous_const)
  have hcov : ⋃ μ, A μ = univ := by
    refine eq_univ_of_forall fun s => ?_
    obtain ⟨w, hw, μ, hμ, hs⟩ := Set.mem_add.1 s.2
    exact Set.mem_iUnion.2 ⟨⟨μ, hμ⟩, show (s : E) - μ ∈ W by rw [← hs]; simpa using hw⟩
  -- Baire: one translate `W + μ` has interior in `S`
  obtain ⟨μ, s₀, hs₀⟩ := nonempty_interior_of_iUnion_of_closed hA hcov
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hs₀)
  refine span_inter_eq_of_forall_norm_lt hε fun w hw ν hν hlt => ?_
  obtain ⟨w₀, hw₀, μ₀, hμ₀, hs⟩ := Set.mem_add.1 s₀.2
  have hx : w + ν + s₀ ∈ S := Set.mem_add.2
    ⟨w + w₀, W.add_mem hw hw₀, ν + μ₀, Λ.add_mem hν hμ₀, by rw [← hs]; abel⟩
  have hmem : (⟨w + ν + s₀, hx⟩ : S) ∈ ball s₀ ε := by
    rw [mem_ball, Subtype.dist_eq, dist_eq_norm]
    simpa using hlt
  rw [show w + ν = (w + ν + s₀ - μ) - ((s₀ : E) - μ) by abel]
  exact W.sub_mem (hball hmem) (interior_subset (s := A μ) hs₀)

end Lattice

section Analytic

open MMP.SmoothLocusConnected

variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {M : Type*} [TopologicalSpace M]

/-- A locally analytic subset is closed. -/
theorem isClosed_of_isLocallyAnalytic {S : Set M} (hS : IsLocallyAnalytic H F S) :
    IsClosed S := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun p hp => ?_)
  obtain ⟨e, ι, g, hpe, hg, hSe⟩ := hS p
  obtain ⟨i, hi⟩ : ∃ i, g i (e p) ≠ 0 := by
    by_contra! h
    exact hp ((hSe p hpe).2 h)
  have hO : IsOpen (e.target ∩ g i ⁻¹' {0}ᶜ) :=
    (hg i).continuousOn.isOpen_inter_preimage e.open_target isOpen_compl_singleton
  refine ⟨e.source ∩ e ⁻¹' (e.target ∩ g i ⁻¹' {0}ᶜ), fun q hq hqS => ?_,
    e.continuousOn.isOpen_inter_preimage e.open_source hO, hpe, e.map_source hpe, hi⟩
  exact hq.2.2 ((hSe q hq.1).1 hqS i)

/-- **Baire and the identity theorem.** If countably many locally analytic subsets cover a
nonempty preconnected Baire space, one of them is the whole space. -/
theorem exists_eq_univ_of_iUnion_eq_univ [PreconnectedSpace M] [BaireSpace M] [Nonempty M]
    {ι : Type*} [Countable ι] {S : ι → Set M} (hS : ∀ i, IsLocallyAnalytic H F (S i))
    (hU : ⋃ i, S i = univ) : ∃ i, S i = univ := by
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed
    (fun i => isClosed_of_isLocallyAnalytic (hS i)) hU
  by_contra! h
  exact hi.ne_empty
    (interior_eq_empty_iff_dense_compl.2 (dense_compl_of_isLocallyAnalytic (hS i) (h i)))

/-- **Baire and the identity theorem on a complex subspace.** Let `V` be a subspace of a
finite-dimensional complex normed space `E`, and let countably many sets `Zᵢ ⊆ E` cover `V`, each
meeting `V` in a locally analytic subset of `V`. Then one `Zᵢ` contains `V`. -/
theorem exists_subset_of_subset_iUnion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (V : Submodule ℂ E) {ι : Type*} [Countable ι] {Z : ι → Set E}
    (hZ : ∀ i, IsLocallyAnalytic V F (((↑) : V → E) ⁻¹' Z i)) (hV : (V : Set E) ⊆ ⋃ i, Z i) :
    ∃ i, (V : Set E) ⊆ Z i := by
  have hU : ⋃ i, ((↑) : V → E) ⁻¹' Z i = univ := by
    rw [← Set.preimage_iUnion]
    exact eq_univ_of_forall fun v => hV v.2
  obtain ⟨i, hi⟩ := exists_eq_univ_of_iUnion_eq_univ hZ hU
  exact ⟨i, fun x hx => (Set.eq_univ_iff_forall.1 hi ⟨x, hx⟩ :)⟩

end Analytic

section Algebraic

open CategoryTheory AlgebraicGeometry Topology Filter MMP.SmoothLocusConnected
open MMP.Analytic.ComplexPoints

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
  {N : Type} [NormedAddCommGroup N] [NormedSpace ℂ N] [FiniteDimensional ℂ N]

/-- **The inverse image of a Zariski-closed set under a holomorphic map is locally analytic.** Let
`Ψ : N → X(ℂ)` be a continuous map from a finite-dimensional complex normed space which is
holomorphic in charts: near every point, its coordinates in every affine chart are those of a
holomorphic map. Then for a closed subset `T` of the scheme `X`, the set of `v` with
`Ψ(v) ∈ T` is locally analytic. -/
theorem isLocallyAnalytic_preimage_toScheme {Ψ : N → ComplexPoints sX} (hΨ : Continuous Ψ)
    (hhol : ∀ (v : N) (c : Chart sX) (_ : Ψ v ∈ chart c.U), ∃ F : N → (Fin c.n → ℂ),
      DifferentiableAt ℂ F v ∧ ∀ᶠ v' in 𝓝 v, ∃ h' : Ψ v' ∈ chart c.U, c.coords ⟨Ψ v', h'⟩ = F v')
    {T : Set X} (hT : IsClosed T) :
    IsLocallyAnalytic N ℂ (Ψ ⁻¹' (toScheme ⁻¹' T)) := by
  classical
  intro p
  obtain ⟨U, hU, hpU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (Ψ p).toScheme) (U := ⊤) trivial
  obtain ⟨c, rfl⟩ := Chart.exists_eq (sX := sX) hU
  have hO : IsOpen (Ψ ⁻¹' chart c.U) := by
    rw [show chart (sX := sX) c.U = toScheme ⁻¹' (c.U : Set X) from
      Set.ext fun _ => mem_chart_iff]
    exact (c.U.2.preimage continuous_toScheme).preimage hΨ
  let ι : Type := {f : Γ(X, c.U) // ∀ x ∈ T, x ∉ X.basicOpen f}
  let g : ι → N → ℂ := fun f z =>
    if h : Ψ z ∈ chart c.U then evalHom c.U ⟨Ψ z, h⟩ f.1 else 0
  refine ⟨OpenPartialHomeomorph.ofSet _ hO, ι, g, mem_chart_iff.2 hpU, fun f => ?_, ?_⟩
  · refine OkaCoherence.analyticOnNhd_of_differentiableOn' hO fun z hz => ?_
    obtain ⟨q, hq⟩ := c.surjective f.1
    obtain ⟨F, hF, hev⟩ := hhol z c hz
    have hd : DifferentiableAt ℂ (fun z' => MvPolynomial.eval (F z') q) z :=
      (differentiable_eval_mvPolynomial q).differentiableAt.comp z hF
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hev] with z' ⟨h', hc⟩
    simp only [g, h', ↓reduceDIte, ← hc]
    rw [← hq]
    exact c.evalHom_pres ⟨Ψ z', h'⟩ q
  · intro q hq
    change Ψ q ∈ chart c.U at hq
    have hg : ∀ f : ι, g f q = evalHom c.U ⟨Ψ q, hq⟩ f.1 := fun f => by
      simp only [g, hq, ↓reduceDIte]
    simp only [OpenPartialHomeomorph.ofSet_apply, id_eq, hg]
    refine ⟨fun hqT f => Classical.byContradiction fun h0 =>
      f.2 _ hqT ((toScheme_mem_basicOpen_iff ⟨Ψ q, hq⟩ f.1).2 h0), fun h0 => ?_⟩
    by_contra hqT
    obtain ⟨f, hfV, hqf⟩ := c.isAffineOpen.exists_basicOpen_le
      (V := ⟨Tᶜ, hT.isOpen_compl⟩) ⟨(Ψ q).toScheme, hqT⟩ (mem_chart_iff.1 hq)
    exact (toScheme_mem_basicOpen_iff ⟨Ψ q, hq⟩ f).1 hqf
      (h0 ⟨f, fun x hx hxf => hfV hxf hx⟩)

/-- **Baire and the identity theorem for a holomorphic map to `X(ℂ)`.** If the image of a
continuous map `Ψ : N → X(ℂ)`, holomorphic in charts, lies in the union of countably many closed
subsets `Tᵢ` of the scheme `X`, then it lies in one of them. -/
theorem exists_forall_mem_of_forall_mem_iUnion {Ψ : N → ComplexPoints sX} (hΨ : Continuous Ψ)
    (hhol : ∀ (v : N) (c : Chart sX) (_ : Ψ v ∈ chart c.U), ∃ F : N → (Fin c.n → ℂ),
      DifferentiableAt ℂ F v ∧ ∀ᶠ v' in 𝓝 v, ∃ h' : Ψ v' ∈ chart c.U, c.coords ⟨Ψ v', h'⟩ = F v')
    {ι : Type*} [Countable ι] {T : ι → Set X} (hT : ∀ i, IsClosed (T i))
    (hcov : ∀ v, (Ψ v).toScheme ∈ ⋃ i, T i) : ∃ i, ∀ v, (Ψ v).toScheme ∈ T i := by
  have hU : ⋃ i, Ψ ⁻¹' (toScheme ⁻¹' T i) = Set.univ :=
    Set.eq_univ_of_forall fun v => by simpa using hcov v
  obtain ⟨i, hi⟩ := exists_eq_univ_of_iUnion_eq_univ
    (fun i => isLocallyAnalytic_preimage_toScheme hΨ hhol (hT i)) hU
  exact ⟨i, fun v => (Set.eq_univ_iff_forall.1 hi v :)⟩

end Algebraic

end MMP.Analytic.SurfaceHodge
