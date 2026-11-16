module

public import MMP.Analysis.Complex.StratifiedFlows
public import MMP.AlgebraicTopology.ComplexProjectiveSpace.Cohomology
public import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
public import MMP.AlgebraicGeometry.Analytic.QuasiProjectiveFiniteHomotopy
public import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
public import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
public import MMP.AlgebraicGeometry.Analytic.SchemeManifold
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
public import MMP.Attr

/-!
# Bounded second Betti numbers of chosen resolutions in a family of surfaces

Let `h : 𝒵 ⟶ T` be projective over `ℂ`, with `T` reduced and quasi-projective, all of whose
closed fibres are reduced surfaces of pure dimension two. Then the closed fibres admit
resolutions `Y_t` by smooth projective surfaces with uniformly bounded `dim_ℚ H²(Y_t^an; ℚ)`.

`T` is stratified, by noetherian induction, into finitely many smooth quasi-projective pieces
`S`, each carrying a smooth projective family of surfaces `𝒴 ⟶ S` whose closed fibres map over
`ℂ` to the closed fibres of `h`, isomorphically over a dense open with dense preimage. Over an
irreducible closed `Z₁ ⊆ T` with reduced structure `W`, the family is the disjoint union, over
a dense open `W₀ ⊆ W`, of strong resolutions `R_C` of the components `C` of `(𝒵 ×_T W)_red`
dominating `W`: by generic smoothness `R_C ⟶ W` is smooth over `W₀`, and the dimension of the
fibres of `C` and of the proper closed subsets where the resolution is not an isomorphism are
read off from generic fibre dimension. A dimension count in each closed fibre shows that the
fibres of `C` are surfaces, so that `R_C ⟶ W₀` has relative dimension two, and that the loci
where the resolution is an isomorphism are dense in the fibres.

On each piece the second Betti number of the fibres is locally constant: the complex
realization of a smooth proper morphism is a proper holomorphic submersion, and flowing along
lifts of constant vector fields of a chart of the base (Ehresmann) identifies nearby fibres. A
smooth quasi-projective complex scheme has finitely many analytic connected components, so the
Betti number takes finitely many values on each piece.

## Main results

* `MMP.Fourfold.exists_forall_finrank_singularCohomology_two_le_of_resolution`: the uniform
  bound `b` on the second Betti numbers of chosen resolutions of the closed fibres.

## Implementation notes

* A *resolved stratum* (`Stratum`) bundles the base `S`, smooth of pure relative dimension and
  quasi-projective over `ℂ`, and a smooth projective family of surfaces over it; it *resolves*
  the fibre of `h` over a `ℂ`-point `t` (`Stratum.Resolves`) when some closed fibre of the family
  maps to the fibre of `h` over `t` as required by the statement.
* Ehresmann's lemma is proved for maps of real manifolds into a manifold of any dimension, from
  a lift of a basis of the base by a partition of unity; the complex realization of a smooth
  morphism is made a submersion by étale charts in which the pull-backs of étale coordinates of
  the base are coordinates.
* Dimensions of subsets of a closed fibre are Krull dimensions of subspaces, and their
  irreducible components are the maximal irreducible subsets (`IsMaxIrreducible`).

## References

* [J. Kollár, *Lectures on resolution of singularities*]
* [R. Lazarsfeld, *Positivity in algebraic geometry I*]
* [J. M. Lee, *Introduction to smooth manifolds*][lee2012], Chapter 9
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MMP.Analytic.ComplexPoints MMP

namespace MMP.Proof_lem_fourfold_surface_family_resolution_betti_bound

/-- A *resolved stratum*: a smooth quasi-projective `S` over `ℂ` of pure relative dimension,
with a smooth projective family of surfaces `q : Y ⟶ S`. -/
structure Stratum where
  /-- The base scheme of the stratum. -/
  S : Scheme.{0}
  /-- The structure morphism of the base to `Spec ℂ`. -/
  sS : S ⟶ Spec (.of ℂ)
  /-- The total space of the family of surfaces. -/
  Y : Scheme.{0}
  /-- The family of surfaces over the base. -/
  q : Y ⟶ S
  /-- The relative dimension of the base over `ℂ`. -/
  relDim : ℕ
  /-- The base is smooth over `ℂ` of relative dimension `relDim`. -/
  smoothRel : SmoothOfRelativeDimension relDim sS
  /-- The base is separated over `ℂ`. -/
  separated : IsSeparated sS
  /-- The base is quasi-projective over `ℂ`. -/
  quasiProjective : Stacks.HProjective.IsQuasiProjective sS
  /-- The family `q` is projective. -/
  projective : IsProjectiveMorphism q
  /-- The family `q` is smooth of relative dimension `2`. -/
  smoothTwo : SmoothOfRelativeDimension 2 q

/-- The stratum `σ` resolves the fibre of `h` over the `ℂ`-point `t` of its base: some closed
fibre of `σ` maps over `ℂ` to the fibre of `h` over `t`, isomorphically over a dense open whose
preimage is dense. -/
def Stratum.Resolves (σ : Stratum) {𝒵 T : Scheme.{0}} (h : 𝒵 ⟶ T) (t : Spec (.of ℂ) ⟶ T) :
    Prop :=
  ∃ s : Spec (.of ℂ) ⟶ σ.S, s ≫ σ.sS = 𝟙 _ ∧ ∃ p : pullback σ.q s ⟶ pullback h t,
    p ≫ pullback.snd h t = pullback.snd σ.q s ∧ ∃ U : (pullback h t).Opens,
      Dense (U : Set (pullback h t : Scheme.{0})) ∧
      Dense ((p ⁻¹ᵁ U : (pullback σ.q s).Opens) : Set (pullback σ.q s : Scheme.{0})) ∧
      IsIso (p ∣_ U)

/-! ### Ehresmann's lemma for proper submersions -/

section Ehresmann

open Set Filter _root_.Topology Metric
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Local lifts.** Near a point where `g` is smooth with surjective differential, a vector
`ξ` of the target lifts to a local `C¹` vector field `V` with `dg(V) = ξ`. -/
private theorem exists_local_lift_of_surjective {g : M → F} {O : Set M} (hO : IsOpen O)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g O) {x₀ : M} (hx₀ : x₀ ∈ O)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x₀)) (ξ : F) :
    ∃ U ∈ 𝓝 x₀, ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧
      ∀ y ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g y (V y) = ξ := by
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  set φ := chartAt E x₀ with hφdef
  have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x₀
  have hφ1 := IsManifold.maximalAtlas_subset_of_le h1 hφ
  have hx₀s : x₀ ∈ φ.source := mem_chart_source E x₀
  set h : E → F := g ∘ φ.symm with hhdef
  set O' : Set E := φ.target ∩ φ.symm ⁻¹' O with hO'def
  have hO' : IsOpen O' := φ.isOpen_inter_preimage_symm hO
  have hh : ContDiffOn ℝ ∞ h O' := by
    have : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h O' :=
      hg.comp ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono inter_subset_left)
        (fun z hz => hz.2)
    exact contMDiffOn_iff_contDiffOn.1 this
  have hgd : ∀ y ∈ O, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g y := fun y hy =>
    ((hg y hy).contMDiffAt (hO.mem_nhds hy)).mdifferentiableAt (by simp)
  have hhd : ∀ z ∈ O', DifferentiableAt ℝ h z := fun z hz =>
    ((hh z hz).contDiffAt (hO'.mem_nhds hz)).differentiableAt (by simp)
  set D : E → E →L[ℝ] F := fun z => fderiv ℝ h z with hDdef
  have hD : ContDiffOn ℝ ∞ D O' := hh.fderiv_of_isOpen hO' (by simp)
  -- the derivative at `x₀` in the chart is surjective
  have hx₀O' : φ x₀ ∈ O' := ⟨φ.map_source hx₀s, by
    show φ.symm (φ x₀) ∈ O
    rw [φ.left_inv hx₀s]
    exact hx₀⟩
  have hD₀ : Function.Surjective (D (φ x₀)) := by
    have heq : g =ᶠ[𝓝 x₀] h ∘ φ := by
      filter_upwards [φ.open_source.mem_nhds hx₀s] with y hy
      simp [hhdef, φ.left_inv hy]
    have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x₀ =
        (fderiv ℝ h (φ x₀)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x₀) := by
      rw [heq.mfderiv_eq, mfderiv_comp x₀ (hhd _ hx₀O').mdifferentiableAt
        (mdifferentiableAt_of_mem_maximalAtlas hφ1 hx₀s), mfderiv_eq_fderiv]
      rfl
    rw [hc] at hsurj
    exact Function.Surjective.of_comp hsurj
  obtain ⟨A₀, hA₀⟩ := (D (φ x₀)).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hD₀)
  set A : F →L[ℝ] E := LinearMap.toContinuousLinearMap A₀ with hAdef
  have hA : (D (φ x₀)).comp A = ContinuousLinearMap.id ℝ F := by
    ext v
    exact LinearMap.congr_fun hA₀ v
  set N : E → F →L[ℝ] F := fun z => (D z).comp A with hNdef
  have hN : ContDiffOn ℝ ∞ N O' := hD.clm_comp contDiffOn_const
  set O'' : Set E := O' ∩ N ⁻¹' {u | IsUnit u} with hO''def
  have hO'' : IsOpen O'' := hN.continuousOn.isOpen_inter_preimage hO' Units.isOpen
  have hx₀O'' : φ x₀ ∈ O'' := ⟨hx₀O', by
    change IsUnit ((D (φ x₀)).comp A)
    rw [hA]
    exact isUnit_one⟩
  set Uf : E → E := fun z => A (Ring.inverse (N z) ξ) with hUfdef
  have hUf : ContDiffOn ℝ 1 Uf O'' := by
    intro z hz
    obtain ⟨u, hu⟩ := hz.2
    have hinv : ContDiffAt ℝ 1 (fun z => Ring.inverse (N z)) z := by
      have := contDiffAt_ringInverse ℝ (n := 1) u
      rw [hu] at this
      exact this.comp z (((hN z hz.1).contDiffAt (hO'.mem_nhds hz.1)).of_le (by simp))
    have : ContDiffAt ℝ 1 Uf z :=
      A.contDiff.contDiffAt.comp z (hinv.clm_apply contDiffAt_const)
    exact this.contDiffWithinAt
  have hUfξ : ∀ z ∈ O'', D z (Uf z) = ξ := by
    intro z hz
    obtain ⟨u, hu⟩ := hz.2
    change N z (Ring.inverse (N z) ξ) = ξ
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ ⟨u, hu⟩]
    rfl
  set U : Set M := φ.source ∩ φ ⁻¹' O'' with hUdef
  have hUo : IsOpen U := φ.isOpen_inter_preimage hO''
  have hx₀U : x₀ ∈ U := ⟨hx₀s, hx₀O''⟩
  have hUsrc : U ⊆ φ.source := fun y hy => hy.1
  have himg : φ '' U ⊆ O'' := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  refine ⟨U, hUo.mem_nhds hx₀U,
    fun y => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm (φ y) (Uf (φ y)),
    MMP.Analytic.StratifiedFlows.contMDiffOn_section_of_chart hφ hUsrc (hUf.mono himg),
    fun y hy => ?_⟩
  have hys := hUsrc hy
  have hz : φ y ∈ O'' := himg ⟨y, hy, rfl⟩
  have hyO : y ∈ O := by simpa [φ.left_inv hys] using hz.1.2
  have hsymm := mdifferentiableAt_symm_of_mem_maximalAtlas hφ1 (φ.map_source hys)
  erw [← mfderiv_comp_apply_of_eq _ (hgd y hyO) hsymm
    (φ.left_inv hys), mfderiv_eq_fderiv]
  exact hUfξ _ hz

/-- **Lifts over a closed set.** If `g` is a submersion on an open `O ⊇ C` with `C` closed, a
vector `ξ` lifts to a global `C¹` vector field `V` with `dg(V) = ξ` on `C`. -/
private theorem exists_lift_field [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {g : M → F} {O : Set M} (hO : IsOpen O) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g O)
    (hsub : ∀ x ∈ O, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x))
    {C : Set M} (hC : IsClosed C) (hCO : C ⊆ O) (ξ : F) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∀ x ∈ C, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (V x) = ξ := by
  set t : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w | x ∈ C → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x w = ξ} with ht
  have hconv : ∀ x, Convex ℝ (t x) := by
    intro x w₁ hw₁ w₂ hw₂ a b ha hb hab hx
    have : a • ξ + b • ξ = ξ := by rw [← add_smul, hab, one_smul]
    rw [map_add, map_smul, map_smul, hw₁ hx, hw₂ hx]
    exact this
  have hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧ ∀ y ∈ U, V y ∈ t y := by
    intro x₀
    by_cases hx₀ : x₀ ∈ C
    · obtain ⟨U, hU, V, hV, hVξ⟩ :=
        exists_local_lift_of_surjective hO hg (hCO hx₀) (hsub _ (hCO hx₀)) ξ
      exact ⟨U, hU, V, hV, fun y hy _ => hVξ y hy⟩
    · refine ⟨Cᶜ, hC.isOpen_compl.mem_nhds hx₀, fun _ => 0, ?_, fun y hy h => absurd h hy⟩
      exact (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E))).contMDiffOn
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    𝓘(ℝ, E) (TangentSpace 𝓘(ℝ, E)) t hconv hloc
  exact ⟨σ, σ.contMDiff, hσ⟩

/-- **Continuation.** A continuous curve `γ` along which `g` moves with constant velocity `ζ`
while it stays in an open `Ω`, starting in the closed set `L ⊆ Ω` of points of `O` over the ball
`closedBall c R`, keeps moving with velocity `ζ`, inside `L`, as long as `g` stays in the ball. -/
private theorem mem_and_eq_add_smul_of_hasDerivAt {g : M → F} {O L Ω : Set M} (hgO : ContinuousOn g O)
    (hL : IsClosed L) (hLΩ : L ⊆ Ω) (hΩ : IsOpen Ω) (hΩO : Ω ⊆ O) {c : F} {R : ℝ}
    (hLdef : ∀ x ∈ O, g x ∈ closedBall c R → x ∈ L)
    {γ : ℝ → M} (hγ : Continuous γ) {ζ : F}
    (hder : ∀ u, γ u ∈ Ω → HasDerivAt (fun u => g (γ u)) ζ u)
    (h0 : γ 0 ∈ L) {s : ℝ} (hs : 0 ≤ s) (hR : ‖g (γ 0) - c‖ + s * ‖ζ‖ < R) :
    γ s ∈ L ∧ g (γ s) = g (γ 0) + s • ζ := by
  set a := g (γ 0) with ha
  set G : Set ℝ := {u | γ u ∈ L ∧ g (γ u) = a + u • ζ} with hG
  have hGc : IsClosed (G ∩ Icc 0 s) := by
    have hc : ContinuousOn (fun u => (g (γ u), a + u • ζ)) (γ ⁻¹' L) := by
      refine ContinuousOn.prodMk ?_
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      exact hgO.comp hγ.continuousOn (fun u hu => hΩO (hLΩ hu))
    have := (hc.preimage_isClosed_of_isClosed (hL.preimage hγ) isClosed_diagonal).inter
      (isClosed_Icc (a := (0 : ℝ)) (b := s))
    convert this using 1
    ext u
    simp only [hG, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_diagonal_iff]
  have hG0 : (0 : ℝ) ∈ G := ⟨h0, by simp [ha]⟩
  have hstep : ∀ u ∈ G ∩ Ico 0 s, G ∈ 𝓝[>] u := by
    rintro u ⟨⟨huL, hua⟩, hu0, hus⟩
    have hΩu : γ u ∈ Ω := hLΩ huL
    obtain ⟨δ, hδ, hδΩ⟩ := Metric.mem_nhds_iff.mp
      (hγ.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hΩu))
    rw [Real.ball_eq_Ioo] at hδΩ
    have hd : ∀ w ∈ Ioo (u - δ) (u + δ), HasDerivAt (fun u => g (γ u)) ζ w :=
      fun w hw => hder w (hδΩ hw)
    refine Filter.mem_of_superset (Ioo_mem_nhdsGT (lt_min (by linarith : u < u + δ) hus))
      fun w hw => ?_
    have hw1 : w < u + δ := lt_of_lt_of_le hw.2 (min_le_left _ _)
    have hw2 : w < s := lt_of_lt_of_le hw.2 (min_le_right _ _)
    have hwI : w ∈ Ioo (u - δ) (u + δ) := ⟨by linarith [hw.1], hw1⟩
    have hlin := MMP.Analytic.StratifiedFlows.eq_add_smul_of_hasDerivAt hd
      (show u ∈ Ioo (u - δ) (u + δ) from ⟨by linarith, by linarith⟩) hwI
    have hgw : g (γ w) = a + w • ζ := by
      rw [hlin, hua, add_assoc, ← add_smul]
      congr 2
      ring
    refine ⟨hLdef _ (hΩO (hδΩ hwI)) ?_, hgw⟩
    rw [mem_closedBall, dist_eq_norm, hgw]
    calc ‖a + w • ζ - c‖ = ‖(a - c) + w • ζ‖ := by congr 1; abel
      _ ≤ ‖a - c‖ + w * ‖ζ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hw.1])]
      _ ≤ ‖a - c‖ + s * ‖ζ‖ := by gcongr
      _ ≤ R := hR.le
  exact (hGc.Icc_subset_of_forall_mem_nhdsWithin hG0 hstep) ⟨hs, le_rfl⟩

/-- **Ehresmann's lemma, over a ball.** Let `g : M → F` be smooth with surjective differential on
an open set `O`, and suppose the points of `O` over `closedBall c R` form a compact set. Then over
every point `y` of the ball of radius `R / 2` the fibre of `g` in `O` is homeomorphic to the
fibre over `c`: flowing for unit time along a lift of the constant field `y - c` carries one to
the other, and flowing back undoes it. -/
private theorem nonempty_homeomorph_fibre [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {g : M → F} {O : Set M} (hO : IsOpen O) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g O)
    (hsub : ∀ x ∈ O, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x))
    {c : F} {R : ℝ} (hL : IsCompact (O ∩ g ⁻¹' closedBall c R)) {y : F}
    (hy : y ∈ ball c (R / 2)) :
    Nonempty ({x | x ∈ O ∧ g x = c} ≃ₜ {x | x ∈ O ∧ g x = y}) := by
  classical
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  set L := O ∩ g ⁻¹' closedBall c R with hLdef
  have hLc : IsClosed L := hL.isClosed
  obtain ⟨K₁, hK₁c, hLK₁, hK₁O⟩ := exists_compact_between hL hO inter_subset_left
  obtain ⟨K₂, hK₂c, hLK₂, hK₂K₁⟩ := exists_compact_between hL isOpen_interior hLK₁
  set b := Module.finBasis ℝ F
  have hfield := fun j => exists_lift_field hO hg hsub hK₁c.isClosed hK₁O (b j)
  choose V hVs hVξ using hfield
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, E) (n := 1)
    isOpen_interior.isClosed_compl hK₂c.isClosed (disjoint_compl_left_iff_subset.mpr hK₂K₁)
  set ξ := y - c with hξ
  set W : (x : M) → TangentSpace 𝓘(ℝ, E) x :=
    fun x => χ x • ∑ j, b.repr ξ j • V j x with hWdef
  have hWs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    χ.contMDiff.smul_section (ContMDiff.sum_section fun j _ => (hVs j).const_smul_section)
  have hWK : ∀ x ∉ K₁, W x = 0 := by
    intro x hx
    have : χ x = 0 := hχ0 (fun h => hx (interior_subset h))
    simp [hWdef, this]
  obtain ⟨Φ, hΦ0, hΦint, hΦgrp, hΦcont, -⟩ :=
    MMP.Analytic.StratifiedFlows.exists_global_flow hWs hK₁c hWK
  set Ω : Set M := interior K₂ with hΩdef
  have hΩO : Ω ⊆ O := fun x hx => hK₁O (interior_subset (hK₂K₁ (interior_subset hx)))
  have hgd : ∀ x ∈ O, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g x := fun x hx =>
    ((hg x hx).contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp)
  have hWξ : ∀ x ∈ Ω, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (W x) = ξ := by
    intro x hx
    have hχx : χ x = 1 := hχ1 (interior_subset hx)
    have hxK : x ∈ K₁ := interior_subset (hK₂K₁ (interior_subset hx))
    simp only [hWdef, hχx, one_smul, map_sum, map_smul, hVξ _ x hxK]
    exact b.sum_repr ξ
  have hder : ∀ x u, Φ u x ∈ Ω → HasDerivAt (fun u => g (Φ u x)) ξ u := by
    intro x u hu
    have h := MMP.Analytic.StratifiedFlows.hasDerivAt_comp_of_hasMFDerivAt (hΦint x u)
      (hgd _ (hΩO hu))
    rwa [hWξ _ hu] at h
  have hcurve : ∀ x, Continuous fun u => Φ u x := fun x =>
    hΦcont.comp (continuous_id.prodMk continuous_const)
  have hgO : ContinuousOn g O := hg.continuousOn
  have hLmem : ∀ x ∈ O, g x ∈ closedBall c R → x ∈ L := fun x hx h => ⟨hx, h⟩
  have hyc : ‖ξ‖ < R / 2 := by rwa [mem_ball, dist_eq_norm] at hy
  have hR : 0 < R := by linarith [norm_nonneg ξ]
  -- forward
  have hfwd : ∀ x ∈ O, g x = c → Φ 1 x ∈ O ∧ g (Φ 1 x) = y := by
    intro x hxO hxc
    have h0 : Φ 0 x ∈ L := by
      rw [hΦ0]
      exact ⟨hxO, by rw [mem_preimage, hxc]; exact mem_closedBall_self hR.le⟩
    obtain ⟨h1, h2⟩ := mem_and_eq_add_smul_of_hasDerivAt hgO hLc hLK₂ isOpen_interior hΩO
      hLmem (hcurve x) (hder x) h0 zero_le_one (by rw [hΦ0, hxc, sub_self, norm_zero]; linarith)
    refine ⟨h1.1, ?_⟩
    rw [h2, hΦ0, hxc, one_smul, hξ]
    abel
  -- backward
  have hbwd : ∀ x ∈ O, g x = y → Φ (-1) x ∈ O ∧ g (Φ (-1) x) = c := by
    intro x hxO hxy
    have hder' : ∀ u, Φ (-u) x ∈ Ω → HasDerivAt (fun u => g (Φ (-u) x)) (-ξ) u := by
      intro u hu
      have h' := (hder x (-u) hu).scomp u (hasDerivAt_neg u)
      rwa [neg_one_smul] at h'
    have hγ0 : Φ (-0) x = x := by rw [neg_zero, hΦ0]
    have h0 : Φ (-0) x ∈ L := by
      rw [hγ0]
      refine ⟨hxO, ?_⟩
      rw [mem_preimage, hxy, mem_closedBall, dist_eq_norm]
      linarith
    obtain ⟨h1, h2⟩ := mem_and_eq_add_smul_of_hasDerivAt (γ := fun u => Φ (-u) x) hgO hLc
      hLK₂ isOpen_interior hΩO hLmem ((hcurve x).comp continuous_neg) hder' h0 zero_le_one
      (by
        rw [hγ0, hxy, norm_neg, one_mul]
        change ‖ξ‖ + ‖ξ‖ < R
        linarith)
    refine ⟨h1.1, ?_⟩
    rw [h2, hγ0, hxy, one_smul, hξ]
    abel
  refine ⟨{
    toFun := fun x => ⟨Φ 1 x, hfwd x.1 x.2.1 x.2.2⟩
    invFun := fun x => ⟨Φ (-1) x, hbwd x.1 x.2.1 x.2.2⟩
    left_inv := fun x => Subtype.ext (by
      change Φ (-1) (Φ 1 x) = x
      rw [hΦgrp, neg_add_cancel, hΦ0])
    right_inv := fun x => Subtype.ext (by
      change Φ 1 (Φ (-1) x) = x
      rw [hΦgrp, add_neg_cancel, hΦ0])
    continuous_toFun := ((hΦcont.comp (continuous_const.prodMk continuous_id)).comp
      continuous_subtype_val).subtype_mk _
    continuous_invFun := ((hΦcont.comp (continuous_const.prodMk continuous_id)).comp
      continuous_subtype_val).subtype_mk _ }⟩

/-- **Ehresmann's lemma.** The fibres of a proper smooth submersion `G : M → B` of manifolds over
the points of a neighbourhood of `b₀` are homeomorphic to the fibre over `b₀`. -/
private theorem eventually_nonempty_homeomorph_fibre [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {B : Type*} [TopologicalSpace B] [ChartedSpace E' B]
    [IsManifold 𝓘(ℝ, E') ∞ B] {G : M → B} (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ G)
    (hGp : IsProperMap G) (hsub : ∀ x, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') G x))
    (b₀ : B) : ∀ᶠ b in 𝓝 b₀, Nonempty (G ⁻¹' {b} ≃ₜ G ⁻¹' {b₀}) := by
  set ψ := chartAt E' b₀ with hψdef
  have hb₀ : b₀ ∈ ψ.source := mem_chart_source E' b₀
  set O : Set M := G ⁻¹' ψ.source with hOdef
  have hO : IsOpen O := ψ.open_source.preimage hG.continuous
  set g : M → E' := ψ ∘ G with hgdef
  have hψs : ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E') ∞ ψ ψ.source := contMDiffOn_chart
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ g O :=
    hψs.comp hG.contMDiffOn (fun x hx => hx)
  have hgsub : ∀ x ∈ O, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') g x) := by
    intro x hx
    have hψd : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E') ψ (G x) :=
      ((hψs _ hx).contMDiffAt (ψ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
    have hGd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') G x :=
      (hG x).mdifferentiableAt (by simp)
    have hinv : (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ (G x)).IsInvertible := by
      have := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E')) (x := b₀) (y := G x)
        (by rwa [extChartAt_source])
      have he : (extChartAt 𝓘(ℝ, E') b₀ : B → E') = ψ := by
        rw [extChartAt_coe]
        rfl
      rwa [he] at this
    rw [hgdef, mfderiv_comp x hψd hGd]
    obtain ⟨e, he⟩ := hinv
    intro v
    obtain ⟨w, hw⟩ := hsub x (e.symm v)
    refine ⟨w, ?_⟩
    rw [ContinuousLinearMap.comp_apply, hw, ← he]
    exact e.apply_symm_apply v
  set c := ψ b₀ with hcdef
  obtain ⟨R, hR, hRt⟩ : ∃ R > 0, closedBall c R ⊆ ψ.target := by
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp
      (ψ.open_target.mem_nhds (ψ.map_source hb₀))
    exact ⟨r / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hrt⟩
  have hK : IsCompact (ψ.symm '' closedBall c R) :=
    (isCompact_closedBall c R).image_of_continuousOn (ψ.continuousOn_symm.mono hRt)
  have hLeq : O ∩ g ⁻¹' closedBall c R = G ⁻¹' (ψ.symm '' closedBall c R) := by
    ext x
    constructor
    · rintro ⟨hxO, hxR⟩
      exact ⟨ψ (G x), hxR, ψ.left_inv hxO⟩
    · rintro ⟨z, hz, hzx⟩
      have hzt := hRt hz
      have hGx : G x = ψ.symm z := hzx.symm
      refine ⟨?_, ?_⟩
      · change G x ∈ ψ.source
        exact hGx ▸ ψ.map_target hzt
      · change ψ (G x) ∈ closedBall c R
        rwa [hGx, ψ.right_inv hzt]
  have hL : IsCompact (O ∩ g ⁻¹' closedBall c R) := hLeq ▸ hGp.isCompact_preimage hK
  have hfib : ∀ b ∈ ψ.source, {x | x ∈ O ∧ g x = ψ b} = G ⁻¹' {b} := by
    intro b hb
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, hgdef, Function.comp_apply, hOdef]
    constructor
    · rintro ⟨hxO, hxb⟩
      exact ψ.injOn hxO hb hxb
    · rintro rfl
      exact ⟨hb, rfl⟩
  filter_upwards [ψ.open_source.mem_nhds hb₀,
    (ψ.continuousAt hb₀).preimage_mem_nhds (ball_mem_nhds c (half_pos hR))] with b hb hbR
  obtain ⟨e⟩ := nonempty_homeomorph_fibre hO hg hgsub hL hbR
  rw [hfib b hb, hfib b₀ hb₀] at e
  exact ⟨e.symm⟩

end Ehresmann

/-! ### Smooth morphisms realize to submersions -/

section Submersion

open IsLocalRing TensorProduct KaehlerDifferential _root_.Topology Filter
open scoped Manifold ContDiff

/-- A linearly independent finite family in a vector space has a dual family of functionals. -/
private theorem exists_forall_apply_eq_ite_of_linearIndependent {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {k : ℕ} {v : Fin k → V} (hv : LinearIndependent K v) :
    ∃ μ : Fin k → V →ₗ[K] K, ∀ i j, μ j (v i) = if i = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K v).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hv.fintypeLinearCombination_injective)
  refine ⟨fun j => LinearMap.proj j ∘ₗ g, fun i j => ?_⟩
  have := LinearMap.congr_fun hg (Pi.single i 1)
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul,
    LinearMap.id_apply] at this
  simp only [LinearMap.comp_apply, this, LinearMap.proj_apply, Pi.single_apply, eq_comm]

/-- **Differentials stay independent along a smooth map.** Let `R → S → T` with `S → T` a
formally smooth local homomorphism of local rings and `Ω[S⁄R]` free. If the `ds_i ⊗ 1` are
linearly independent in `κ(S) ⊗ Ω[S⁄R]`, the `d(s_i|_T) ⊗ 1` are linearly independent in
`κ(T) ⊗ Ω[T⁄R]`. -/
private theorem linearIndependent_tmul_D_algebraMap {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [IsLocalRing S] [IsLocalRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] [IsLocalHom (algebraMap S T)]
    [Module.Free S Ω[S⁄R]] {k : ℕ} (s : Fin k → S)
    (hs : LinearIndependent (ResidueField S)
      fun i => (1 : ResidueField S) ⊗ₜ[S] D R S (s i)) :
    LinearIndependent (ResidueField T)
      fun i => (1 : ResidueField T) ⊗ₜ[T] D R T (algebraMap S T (s i)) := by
  classical
  obtain ⟨μ, hμ⟩ := exists_forall_apply_eq_ite_of_linearIndependent hs
  let β := Module.Free.chooseBasis S Ω[S⁄R]
  have hlift : ∀ j, ∃ ν : Ω[S⁄R] →ₗ[S] S,
      ∀ x, residue S (ν x) = μ j ((1 : ResidueField S) ⊗ₜ[S] x) := by
    intro j
    choose r hr using fun l => residue_surjective (μ j ((1 : ResidueField S) ⊗ₜ[S] β l))
    refine ⟨β.constr S r, fun x => ?_⟩
    have key : (Algebra.linearMap S (ResidueField S)) ∘ₗ β.constr S r =
        ((μ j).restrictScalars S) ∘ₗ (TensorProduct.mk S (ResidueField S) Ω[S⁄R] 1) := by
      refine β.ext fun l => ?_
      simp only [LinearMap.comp_apply, Module.Basis.constr_basis, Algebra.linearMap_apply,
        LinearMap.coe_restrictScalars, TensorProduct.mk_apply]
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact hr l
    exact LinearMap.congr_fun key x
  choose ν hν using hlift
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hinj : Function.Injective (mapBaseChange R S T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    have : Subsingleton (Algebra.H1Cotangent S T) := ((Algebra.formallySmooth_iff S T).1 ‹_›).2
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (map R S T T) := map_surjective R S T
  obtain ⟨l₀, hl₀⟩ := Module.projective_lifting_property (map R S T T) LinearMap.id hsurj
  have htf := (hex.split_tfae hinj hsurj).out 1 2
  obtain ⟨l, hl⟩ := htf.1 ⟨l₀, hl₀⟩
  let Φ : Fin k → Ω[T⁄R] →ₗ[T] T := fun j =>
    ((Algebra.linearMap S T) ∘ₗ ν j).liftBaseChange T ∘ₗ l
  have hΦ : ∀ i j, Φ j (D R T (algebraMap S T (s i))) = algebraMap S T (ν j (D R S (s i))) := by
    intro i j
    have : D R T (algebraMap S T (s i)) = mapBaseChange R S T (1 ⊗ₜ D R S (s i)) := by
      rw [mapBaseChange_tmul, one_smul, map_D]
    simp only [Φ, LinearMap.comp_apply, this]
    rw [← LinearMap.comp_apply l, hl, LinearMap.id_apply, LinearMap.liftBaseChange_tmul,
      one_smul]
    rfl
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun j => ((Algebra.linearMap T (ResidueField T)) ∘ₗ Φ j).liftBaseChange (ResidueField T))
    (fun j i hji => ?_) (fun i => ?_) <;> (try dsimp only) <;>
  rw [LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply, hΦ,
    Algebra.linearMap_apply, IsLocalRing.ResidueField.algebraMap_eq,
    ← IsLocalRing.ResidueField.map_residue, hν, hμ]
  · simp [Ne.symm hji]
  · simp

/-- **Pull-backs along a smooth morphism keep independent differentials.** Let `g : X ⟶ B` be a
morphism over `ℂ`, smooth at `p`, with `B` smooth over `ℂ`. If sections `w_i` of `𝒪_B` near
`g(p)` have linearly independent differentials in `κ(g p) ⊗ Ω_{B/ℂ, g p}`, then the `g^* w_i`
have linearly independent differentials in `κ(p) ⊗ Ω_{X/ℂ, p}`. -/
private theorem linearIndependent_tmul_D_germ_app {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sB : B ⟶ Spec (.of ℂ)} [Smooth sB] (g : X ⟶ B) (hg : g ≫ sB = sX) (p : X)
    (hgp : (g.stalkMap p).hom.FormallySmooth) (V : B.Opens) (hpV : g p ∈ V) {k : ℕ}
    (w : Fin k → Γ(B, V))
    (hw : letI := (sB.stalkMap (g p)).hom.toAlgebra
      LinearIndependent (ResidueField (B.presheaf.stalk (g p))) fun i =>
        (1 : ResidueField (B.presheaf.stalk (g p))) ⊗ₜ[B.presheaf.stalk (g p)]
          D ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (B.presheaf.stalk (g p))
            (B.presheaf.germ V (g p) hpV (w i))) :
    letI := (sX.stalkMap p).hom.toAlgebra
    LinearIndependent (ResidueField (X.presheaf.stalk p)) fun i =>
      (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ (g ⁻¹ᵁ V) p hpV (g.app V (w i))) := by
  subst hg
  letI : Algebra ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (B.presheaf.stalk (g p)) :=
    (sB.stalkMap (g p)).hom.toAlgebra
  letI : Algebra (B.presheaf.stalk (g p)) (X.presheaf.stalk p) := (g.stalkMap p).hom.toAlgebra
  letI : Algebra ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (X.presheaf.stalk p) :=
    ((g ≫ sB).stalkMap p).hom.toAlgebra
  have : IsScalarTower ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (B.presheaf.stalk (g p))
      (X.presheaf.stalk p) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((g ≫ sB).stalkMap p).hom = _
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have : Algebra.FormallySmooth (B.presheaf.stalk (g p)) (X.presheaf.stalk p) := hgp
  have : IsLocalHom (algebraMap (B.presheaf.stalk (g p)) (X.presheaf.stalk p)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap p).hom)
  obtain ⟨hfree, -⟩ := MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk sB (g p)
  have := linearIndependent_tmul_D_algebraMap (R := (Spec (.of ℂ)).presheaf.stalk (sB (g p)))
    (T := X.presheaf.stalk p) (fun i => B.presheaf.germ V (g p) hpV (w i)) hw
  have heq : ∀ i, algebraMap (B.presheaf.stalk (g p)) (X.presheaf.stalk p)
      (B.presheaf.germ V (g p) hpV (w i)) = X.presheaf.germ (g ⁻¹ᵁ V) p hpV (g.app V (w i)) :=
    fun i => Scheme.Hom.germ_stalkMap_apply g V p hpV (w i)
  simp only [heq] at this
  exact this

/-- The differentials `dr ⊗ 1` span `κ(T) ⊗ Ω[T⁄R]`. -/
private theorem span_tmul_D_residueField {R T : Type*} [CommRing R] [CommRing T] [IsLocalRing T]
    [Algebra R T] :
    ⊤ ≤ Submodule.span (ResidueField T)
      (Set.range fun r : T ↦ (1 : ResidueField T) ⊗ₜ[T] D R T r) := by
  have key : ∀ v : ResidueField T ⊗[T] Ω[T⁄R], v ∈ Submodule.span (ResidueField T)
      (Set.range fun r : T ↦ (1 : ResidueField T) ⊗ₜ[T] D R T r) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul c x =>
      have hx : x ∈ Submodule.span T (Set.range (D R T)) := by
        rw [span_range_derivation]; trivial
      have h1 : (1 : ResidueField T) ⊗ₜ[T] x ∈ Submodule.span (ResidueField T)
          (Set.range fun r : T ↦ (1 : ResidueField T) ⊗ₜ[T] D R T r) := by
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨r, rfl⟩ := hy
          exact Submodule.subset_span ⟨r, rfl⟩
        | zero => simp
        | add y y' _ _ hy hy' => rw [tmul_add]; exact add_mem hy hy'
        | smul a y _ hy =>
          rw [tmul_smul, ← algebraMap_smul (ResidueField T) a]
          exact Submodule.smul_mem _ _ hy
      rw [show c ⊗ₜ[T] x = c • ((1 : ResidueField T) ⊗ₜ[T] x) by
        rw [smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ h1
    | add x y hx hy => exact add_mem hx hy
  exact fun v _ ↦ key v

open MMP.Analytic.ComplexPoints in
/-- **Étale coordinates with independent differentials.** On a scheme `X` smooth of relative
dimension `n` over `ℂ`, every point `p` has étale coordinates `z_1, …, z_n` on a Zariski open
`U ∋ p` whose differentials are linearly independent in `κ(p) ⊗ Ω_{X/ℂ,p}`. -/
private theorem exists_etale_coordinates_linearIndependent {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {n : ℕ} [SmoothOfRelativeDimension n sX] (p : X) :
    ∃ (U : X.Opens) (hpU : p ∈ U) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧
      letI := (sX.stalkMap p).hom.toAlgebra
      LinearIndependent (ResidueField (X.presheaf.stalk p)) fun i ↦
        (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
          D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
            (X.presheaf.germ U p hpU (z i)) := by
  classical
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  letI := (sX.stalkMap p).hom.toAlgebra
  obtain ⟨hfree, hfin⟩ := MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk sX p
  have : SmoothOfRelativeDimension n ((⊤ : X.Opens).ι ≫ sX) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := n) (⊤ : X.Opens).ι sX
    rwa [zero_add] at this
  have hdim : Module.finrank (ResidueField (X.presheaf.stalk p))
      (ResidueField (X.presheaf.stalk p) ⊗[X.presheaf.stalk p]
        Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)]) = n := by
    rw [Module.finrank_baseChange]
    exact finrank_kaehlerDifferential_stalk_of_mem ⊤ p trivial
  obtain ⟨e, v, hvS, hli, hsp⟩ := MMP.Flips.ResolutionInputs.exists_sumElim_basis
    (Fin.elim0 : Fin 0 → ResidueField (X.presheaf.stalk p) ⊗[X.presheaf.stalk p]
      Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)])
    linearIndependent_empty_type _ span_tmul_D_residueField
  have hcard : e = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [hdim, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, zero_add] at this
    exact this.symm
  subst hcard
  choose r hr using hvS
  obtain ⟨W, -, hpW, b, hb⟩ := MMP.Flips.ResolutionInputs.exists_affineOpen_germ_eq p r
  have hbli : LinearIndependent (ResidueField (X.presheaf.stalk p)) fun j ↦
      (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ W p hpW (b j)) := by
    have := hli.comp Sum.inr Sum.inr_injective
    have heq : (fun j ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ W p hpW (b j))) = Sum.elim Fin.elim0 v ∘ Sum.inr := by
      funext j
      simp only [Function.comp_apply, Sum.elim_inr]
      rw [hb j]
      exact hr j
    rw [heq]
    exact this
  obtain ⟨U, hpU, hUW, z, c, hz, hzc⟩ := exists_etale_coordinates_extending (n := e) p W hpW b hbli
  refine ⟨U, hpU, z, hz, ?_⟩
  have hc : Function.Bijective c := (Fintype.bijective_iff_injective_and_card c).2
    ⟨c.injective, rfl⟩
  rw [← linearIndependent_equiv (Equiv.ofBijective c hc)]
  convert hbli using 1
  funext j
  simp only [Function.comp_apply, Equiv.ofBijective_apply, hzc j]
  rw [X.presheaf.germ_res_apply]

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- Étale coordinate charts at every point whose coordinates have linearly independent
differentials there, recorded with the coordinates. -/
private theorem exists_etaleCoordinateChart_linearIndependent {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n sX] (x : ComplexPoints sX) :
    ∃ (U : X.Opens) (hxU : toScheme x ∈ U) (z : Fin n → Γ(X, U))
      (c : EtaleCoordinateChart sX n), x ∈ c.W ∧ ∃ hcU : c.W ⊆ chart U,
      (∀ (y : ComplexPoints sX) (hy : y ∈ c.W) (j : Fin n),
        c.toOpenPartialHomeomorph y j = eval U (z j) ⟨y, hcU hy⟩) ∧
      letI := (sX.stalkMap (toScheme x)).hom.toAlgebra
      LinearIndependent (ResidueField (X.presheaf.stalk (toScheme x))) fun i ↦
        (1 : ResidueField (X.presheaf.stalk (toScheme x))) ⊗ₜ[X.presheaf.stalk (toScheme x)]
          D ((Spec (.of ℂ)).presheaf.stalk (sX (toScheme x))) (X.presheaf.stalk (toScheme x))
            (X.presheaf.germ U (toScheme x) hxU (z i)) := by
  obtain ⟨U, hpU, z, hz, hli⟩ := exists_etale_coordinates_linearIndependent (sX := sX)
    (n := n) (toScheme x)
  obtain ⟨c, hxc, -, hcU, hcz⟩ := EtaleCoordinateChart.exists_of_etale U z hz
    (mem_chart_iff.2 hpU) isOpen_univ (Set.mem_univ x)
  exact ⟨U, hpU, z, c, hxc, hcU, fun y hy j => hcz y hy (hcU hy) j, hli⟩

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- **Charts adapted to a smooth morphism.** Let `g : X ⟶ B` be a smooth morphism of smooth
complex schemes and `c_B` an étale chart around `g(x)` given by étale coordinates `w` with
independent differentials at `g(x)`. Then there is an étale chart `c` of `X^an` around `x`,
mapping into `c_B`, among whose coordinates are the pull-backs `g^* w_j`. -/
private theorem exists_etaleCoordinateChart_adapted {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sB : B ⟶ Spec (.of ℂ)} {n m : ℕ} [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension m sB] (g : X ⟶ B) (hg : g ≫ sB = sX) [Smooth g]
    (x : ComplexPoints sX) (UB : B.Opens) (hxB' : toScheme (realize g hg x) ∈ UB)
    (w : Fin m → Γ(B, UB)) (cB : EtaleCoordinateChart sB m) (hxB : realize g hg x ∈ cB.W)
    (hcBU : cB.W ⊆ chart UB)
    (hcBw : ∀ (y : ComplexPoints sB) (hy : y ∈ cB.W) (j : Fin m),
      cB.toOpenPartialHomeomorph y j = eval UB (w j) ⟨y, hcBU hy⟩)
    (hli : letI := (sB.stalkMap (toScheme (realize g hg x))).hom.toAlgebra
      LinearIndependent (ResidueField (B.presheaf.stalk (toScheme (realize g hg x)))) fun i ↦
        (1 : ResidueField (B.presheaf.stalk (toScheme (realize g hg x)))) ⊗ₜ[B.presheaf.stalk
          (toScheme (realize g hg x))]
          D ((Spec (.of ℂ)).presheaf.stalk (sB (toScheme (realize g hg x))))
            (B.presheaf.stalk (toScheme (realize g hg x)))
            (B.presheaf.germ UB (toScheme (realize g hg x)) hxB' (w i))) :
    ∃ (c : EtaleCoordinateChart sX n) (ι : Fin m ↪ Fin n), x ∈ c.W ∧
      c.W ⊆ realize g hg ⁻¹' cB.W ∧
      ∀ y ∈ c.W, ∀ j, cB.toOpenPartialHomeomorph (realize g hg y) j =
        c.toOpenPartialHomeomorph y (ι j) := by
  have : Smooth sB := SmoothOfRelativeDimension.smooth m sB
  set p := toScheme x with hpdef
  have hpV : g p ∈ UB := hxB'
  have hgp : (g.stalkMap p).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.1 (by rw [g.smoothLocus_eq_top]; trivial)
  have hind := linearIndependent_tmul_D_germ_app g hg p hgp UB hpV w hli
  obtain ⟨U, hpU, hUV, z, ι, hz, hzι⟩ := exists_etale_coordinates_extending (n := n) p
    (g ⁻¹ᵁ UB) hpV (fun j => g.app UB (w j)) hind
  obtain ⟨c, hxc, hcO, hcU, hcz⟩ := EtaleCoordinateChart.exists_of_etale U z hz
    (mem_chart_iff.2 hpU) (cB.isOpen.preimage (continuous_realize g hg)) hxB
  refine ⟨c, ι, hxc, hcO, fun y hy j => ?_⟩
  have hyB : realize g hg y ∈ cB.W := hcO hy
  have hyU : y ∈ chart U := hcU hy
  rw [hcBw _ hyB j, hcz y hy hyU (ι j), hzι j]
  have h2 : eval (g ⁻¹ᵁ UB) (g.app UB (w j)) ⟨y, chart_mono hUV hyU⟩ =
      eval UB (w j) ⟨realize g hg y, hcBU hyB⟩ := by
    simp only [ComplexPoints.eval]
    congr 1
  rw [← h2]
  exact evalHom_res hUV ⟨y, hyU⟩ (g.app UB (w j))

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- **Adapted charts give a submersion.** If the preferred chart of `X^an` at `x` maps into the
preferred chart of `B^an` at `g(x)`, and the coordinates of the latter pull back to coordinates
`ι j` of the former, then the differential of `g^an` at `x` is surjective. -/
private theorem surjective_mfderiv_realize_of_adapted {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sB : B ⟶ Spec (.of ℂ)} {n m : ℕ} [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension m sB]
    (pickX : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (pickB : ∀ b : ComplexPoints sB, {c : EtaleCoordinateChart sB m // b ∈ c.W})
    (g : X ⟶ B) (hg : g ≫ sB = sX) (x : ComplexPoints sX) (ι : Fin m ↪ Fin n)
    (hsub : (pickX x).1.W ⊆ realize g hg ⁻¹' (pickB (realize g hg x)).1.W)
    (hadapt : ∀ y ∈ (pickX x).1.W, ∀ j,
      (pickB (realize g hg x)).1.toOpenPartialHomeomorph (realize g hg y) j =
        (pickX x).1.toOpenPartialHomeomorph y (ι j)) :
    letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pickX
    letI := etaleChartedSpaceOf sB m (EuclideanSpace.equiv (Fin m) ℂ).symm pickB
    Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
      𝓘(ℂ, EuclideanSpace ℂ (Fin m)) (realize g hg) x) := by
  letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pickX
  letI := etaleChartedSpaceOf sB m (EuclideanSpace.equiv (Fin m) ℂ).symm pickB
  set LX := (EuclideanSpace.equiv (Fin n) ℂ).symm with hLX
  set LB := (EuclideanSpace.equiv (Fin m) ℂ).symm with hLB
  set π : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (ι j) with hπ
  set P : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (LB : (Fin m → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m)).comp
      (π.comp (LX.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))) with hP
  set c := (pickX x).1 with hc
  set cB := (pickB (realize g hg x)).1 with hcB
  set e := c.toChart LX with he
  have hechart : chartAt (EuclideanSpace ℂ (Fin n)) x = e := rfl
  have heB : chartAt (EuclideanSpace ℂ (Fin m)) (realize g hg x) = cB.toChart LB := rfl
  have hxs : x ∈ e.source := by rw [he, EtaleCoordinateChart.source_toChart]; exact (pickX x).2
  have hder : HasMFDerivAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin m))
      (realize g hg) x P := by
    refine ⟨(continuous_realize g hg).continuousAt, ?_⟩
    have hev : writtenInExtChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
        𝓘(ℂ, EuclideanSpace ℂ (Fin m)) x (realize g hg) =ᶠ[𝓝 (e x)] P := by
      filter_upwards [e.open_target.mem_nhds (e.map_source hxs)] with v hv
      have hW : e.symm v ∈ c.W := by
        have := e.map_target hv
        rwa [he, EtaleCoordinateChart.source_toChart] at this
      have h1 : c.toOpenPartialHomeomorph (e.symm v) = LX.symm v := by
        have := e.right_inv hv
        rw [he, EtaleCoordinateChart.toChart_apply] at this
        exact LX.eq_symm_apply.2 this
      simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, hechart, heB,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
      rw [EtaleCoordinateChart.toChart_apply, hP]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      congr 1
      funext j
      rw [hadapt _ hW j, h1]
      rfl
    have hd := P.hasFDerivAt.congr_of_eventuallyEq hev
    simp only [extChartAt_coe, hechart, modelWithCornersSelf_coe, Function.comp_apply, id_eq,
      Set.range_id]
    exact hd.hasFDerivWithinAt
  rw [hder.mfderiv]
  intro u
  refine ⟨LX (Function.extend ι (LB.symm u) 0), ?_⟩
  have : π (Function.extend ι (LB.symm u) 0) = LB.symm u := by
    funext j
    simp only [hπ, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    exact ι.injective.extend_apply _ _ j
  show (LB : (Fin m → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m))
    (π ((LX.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))
      (LX (Function.extend ι (LB.symm u) 0)))) = u
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, this]
  exact LB.apply_symm_apply u

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- **Smooth morphisms are submersions.** For a smooth morphism `g : X ⟶ B` of smooth complex
schemes of relative dimensions `n` and `m`, there are choices of preferred étale charts of `X^an`
and of `B^an` in which `g^an` has surjective differential everywhere. -/
private theorem exists_picks_surjective_mfderiv_realize_of_smooth {X B : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)} {n m : ℕ}
    [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension m sB]
    (g : X ⟶ B) (hg : g ≫ sB = sX) [Smooth g] :
    ∃ (pickX : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
      (pickB : ∀ b : ComplexPoints sB, {c : EtaleCoordinateChart sB m // b ∈ c.W}),
      letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pickX
      letI := etaleChartedSpaceOf sB m (EuclideanSpace.equiv (Fin m) ℂ).symm pickB
      ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
        𝓘(ℂ, EuclideanSpace ℂ (Fin m)) (realize g hg) x) := by
  choose UB hbU wB cB hbc hcBU hcBw hliB using fun b : ComplexPoints sB =>
    exists_etaleCoordinateChart_linearIndependent (sX := sB) (n := m) b
  let pickB : ∀ b : ComplexPoints sB, {c : EtaleCoordinateChart sB m // b ∈ c.W} :=
    fun b => ⟨cB b, hbc b⟩
  choose cX ιX hxc hcsub hcad using fun x : ComplexPoints sX =>
    exists_etaleCoordinateChart_adapted (n := n) g hg x (UB _) (hbU _) (wB _) (cB _) (hbc _)
      (hcBU _) (hcBw _) (hliB _)
  let pickX : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W} :=
    fun x => ⟨cX x, hxc x⟩
  exact ⟨pickX, pickB, fun x =>
    surjective_mfderiv_realize_of_adapted pickX pickB g hg x (ιX x) (hcsub x) (hcad x)⟩

end Submersion

/-! ### The second Betti number in a smooth projective family -/

section Betti

open MMP.Analytic MMP.Analytic.ComplexPoints _root_.Topology Filter
open scoped Manifold ContDiff

/-- Equal structure morphisms give the same complex realization. -/
private noncomputable def complexPointsHomeomorphOfEq {X : Scheme.{0}} {s₁ s₂ : X ⟶ Spec (.of ℂ)}
    (h : s₁ = s₂) : ComplexPoints s₁ ≃ₜ ComplexPoints s₂ where
  toFun := realize (𝟙 X) (by rw [Category.id_comp, h])
  invFun := realize (𝟙 X) (by rw [Category.id_comp, h])
  left_inv x := by ext1; simp
  right_inv x := by ext1; simp
  continuous_toFun := continuous_realize _ _
  continuous_invFun := continuous_realize _ _

/-- The complex realization of the fibre of `q` over a `ℂ`-point `s` is the fibre of `q^an`
over `s`. -/
private theorem nonempty_homeomorph_complexPoints_pullback {S Y : Scheme.{0}} {sS : S ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sS] [QuasiCompact sS] (q : Y ⟶ S) [LocallyOfFiniteType q]
    [QuasiCompact q] (s : ComplexPoints sS) :
    Nonempty (ComplexPoints (pullback.snd q s.hom) ≃ₜ
      (realize (sX := q ≫ sS) q rfl) ⁻¹' {s}) := by
  obtain ⟨hemb, hrange⟩ := isEmbedding_realize_pullback (sX := q ≫ sS)
    (sY := 𝟙 (Spec (.of ℂ))) (sS := sS) q s.hom rfl s.2
  have hpt1 : ∀ p : ComplexPoints (𝟙 (Spec (.of ℂ))), p.hom = 𝟙 _ := fun p => by
    simpa using p.2
  have hpt : ∀ p : ComplexPoints (𝟙 (Spec (.of ℂ))), realize (sY := sS) s.hom s.2 p = s := by
    intro p
    ext1
    simp [hpt1 p]
  let pt : ComplexPoints (𝟙 (Spec (.of ℂ))) := ⟨𝟙 _, by simp⟩
  have hstr : pullback.fst q s.hom ≫ q ≫ sS = pullback.snd q s.hom := by
    rw [← Category.assoc, pullback.condition, Category.assoc, s.2, Category.comp_id]
  have h1 : ∀ p : {p : ComplexPoints (q ≫ sS) × ComplexPoints (𝟙 (Spec (.of ℂ))) |
      realize q rfl p.1 = realize (sY := sS) s.hom s.2 p.2},
      p.1.1 ∈ (realize (sX := q ≫ sS) q rfl) ⁻¹' {s} := by
    intro p
    have := p.2
    simp only [Set.mem_setOf_eq, hpt] at this
    exact this
  have h2 : ∀ y : (realize (sX := q ≫ sS) q rfl) ⁻¹' {s},
      (y.1, pt) ∈ {p : ComplexPoints (q ≫ sS) × ComplexPoints (𝟙 (Spec (.of ℂ))) |
        realize q rfl p.1 = realize (sY := sS) s.hom s.2 p.2} := by
    intro y
    simp only [Set.mem_setOf_eq, hpt]
    exact y.2
  let e₄ : {p : ComplexPoints (q ≫ sS) × ComplexPoints (𝟙 (Spec (.of ℂ))) |
      realize q rfl p.1 = realize (sY := sS) s.hom s.2 p.2} ≃ₜ
      (realize (sX := q ≫ sS) q rfl) ⁻¹' {s} :=
    { toFun := fun p => ⟨p.1.1, h1 p⟩
      invFun := fun y => ⟨(y.1, pt), h2 y⟩
      left_inv := fun p => by
        refine Subtype.ext (Prod.ext rfl ?_)
        ext1
        exact (hpt1 _).trans (hpt1 _).symm
      right_inv := fun y => rfl
      continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk h1
      continuous_invFun :=
        ((continuous_subtype_val.prodMk continuous_const).subtype_mk h2) }
  exact ⟨(complexPointsHomeomorphOfEq hstr.symm).trans
    (hemb.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans e₄))⟩

/-- Rational singular cohomology is invariant under homeomorphisms. -/
private theorem finrank_relativeSingularCohomology_eq_of_homeomorph {X X' : TopCat.{0}} (e : X ≃ₜ X')
    (j : ℤ) :
    Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) X ∅ j) =
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) X' ∅ j) :=
  ((MMP.Topology.relativeSingularCohomologyIsoOfIso ℚ (TopCat.isoOfHomeo e) ∅ j).toLinearEquiv
    |>.finrank_eq).symm

/-- Holomorphic maps between complex manifolds are real smooth. -/
private theorem contMDiff_real_of_complex {n m : ℕ} {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℂ (Fin m)) N] {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin m)) ∞ f) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin m)) ∞ f := by
  intro x
  have h := hf x
  rw [contMDiffAt_iff] at h ⊢
  exact ⟨h.1, h.2.restrict_scalars ℝ⟩

/-- The real differential of a holomorphic map is its complex differential. -/
private theorem mfderiv_real_eq_complex {n m : ℕ} {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℂ (Fin m)) N] {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin m)) f x) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin m)) f x :
      EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin m)) =
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin m)) f x := by
  have h : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin m)) f x
      ((mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin m)) f x).restrictScalars
        ℝ) := ⟨hf.hasMFDerivAt.1, hf.hasMFDerivAt.2.restrictScalars ℝ⟩
  rw [h.mfderiv]
  rfl

/-- **Ehresmann's lemma for a smooth projective family.** The fibres of the complex realization
of a smooth proper morphism `q : Y ⟶ S` onto a smooth complex scheme near `s₀` are homeomorphic
to the fibre over `s₀`. -/
private theorem eventually_nonempty_homeomorph_realize_fibre {S Y : Scheme.{0}}
    {sS : S ⟶ Spec (.of ℂ)} {d : ℕ} [SmoothOfRelativeDimension d sS] [IsSeparated sS]
    [QuasiCompact sS] (q : Y ⟶ S) [IsProper q] [SmoothOfRelativeDimension 2 q]
    (s₀ : ComplexPoints sS) :
    ∀ᶠ s in 𝓝 s₀, Nonempty ((realize (sX := q ≫ sS) q rfl) ⁻¹' {s} ≃ₜ
      (realize (sX := q ≫ sS) q rfl) ⁻¹' {s₀}) := by
  have : Smooth q := SmoothOfRelativeDimension.smooth 2 q
  have : Smooth sS := SmoothOfRelativeDimension.smooth d sS
  have : SmoothOfRelativeDimension (2 + d) (q ≫ sS) := inferInstance
  obtain ⟨pick, pickB, hsurj⟩ := exists_picks_surjective_mfderiv_realize_of_smooth
    (n := 2 + d) (m := d) q (rfl : q ≫ sS = q ≫ sS)
  letI := etaleChartedSpaceOf (q ≫ sS) (2 + d) (EuclideanSpace.equiv (Fin (2 + d)) ℂ).symm pick
  haveI := isManifold_etaleChartedSpaceOf (q ≫ sS) (2 + d)
    (EuclideanSpace.equiv (Fin (2 + d)) ℂ).symm pick ∞
  letI := etaleChartedSpaceOf sS d (EuclideanSpace.equiv (Fin d) ℂ).symm pickB
  haveI := isManifold_etaleChartedSpaceOf sS d (EuclideanSpace.equiv (Fin d) ℂ).symm pickB ∞
  haveI : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin (2 + d))) ∞ (ComplexPoints (q ≫ sS)) :=
    MMP.Analytic.StratifiedFlows.isManifold_real_of_complex
  haveI : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin d)) ∞ (ComplexPoints sS) :=
    MMP.Analytic.StratifiedFlows.isManifold_real_of_complex
  haveI : SecondCountableTopology (ComplexPoints (q ≫ sS)) :=
    secondCountableTopology (2 + d)
  haveI : LocallyCompactSpace (ComplexPoints (q ≫ sS)) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℂ (Fin (2 + d))) _
  have hhol : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin (2 + d))) 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) ∞
      (realize (sX := q ≫ sS) q rfl) :=
    contMDiff_realize_etaleChartedSpaceOf _ _ pick pickB ∞ q rfl
  have hp := (isSeparatedMap_and_isProperMap_realize (sX := q ≫ sS) (sS := sS) q rfl).2
  refine eventually_nonempty_homeomorph_fibre (contMDiff_real_of_complex hhol) hp
    (fun x => ?_) s₀
  intro v
  obtain ⟨w, hw⟩ := hsurj x v
  exact ⟨w, (congrFun (mfderiv_real_eq_complex ((hhol x).mdifferentiableAt (by simp))) w).trans
    hw⟩

/-- **Bounded Betti numbers in a smooth projective family.** For a smooth projective family of
surfaces over a smooth quasi-projective complex scheme, the second Betti numbers of the closed
fibres are bounded. -/
private theorem exists_betti_bound {S Y : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ)) {d : ℕ}
    [SmoothOfRelativeDimension d sS] [IsSeparated sS]
    (hS : Stacks.HProjective.IsQuasiProjective sS) (q : Y ⟶ S) (hq : IsProjectiveMorphism q)
    [SmoothOfRelativeDimension 2 q] :
    ∃ b : ℕ, ∀ s : Spec (.of ℂ) ⟶ S, s ≫ sS = 𝟙 _ →
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
        (analyticSpace (pullback.snd q s)) ∅ 2) ≤ b := by
  have : Smooth sS := SmoothOfRelativeDimension.smooth d sS
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have : LocallyOfFiniteType q := IsProper.toLocallyOfFiniteType
  have : QuasiCompact sS := hS.quasiCompact
  have : LocallyOfFiniteType sS := hS.locallyOfFiniteType
  set F : ComplexPoints sS → ℕ := fun s => Module.finrank ℚ (relativeSingularCohomology ℚ
    (.of ℚ ℚ) (analyticSpace (pullback.snd q s.hom)) ∅ 2) with hFdef
  have hloc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s₀
    filter_upwards [eventually_nonempty_homeomorph_realize_fibre (d := d) q s₀] with s ⟨e⟩
    obtain ⟨e₁⟩ := nonempty_homeomorph_complexPoints_pullback q s
    obtain ⟨e₀⟩ := nonempty_homeomorph_complexPoints_pullback q s₀
    exact finrank_relativeSingularCohomology_eq_of_homeomorph
      (X := analyticSpace (pullback.snd q s.hom)) (X' := analyticSpace (pullback.snd q s₀.hom))
      (e₁.trans (e.trans e₀.symm)) 2
  have hfin : Finite (ConnectedComponents (analyticSpace sS)) :=
    (MMP.Analytic.exists_homotopyEquiv_finite_simplicialComplex_of_smooth_of_isQuasiProjective
      sS hS).2
  have hcont : Continuous F := hloc.continuous
  have hrange : (Set.range F).Finite := by
    have : Set.range F ⊆ Set.range hcont.connectedComponentsLift := by
      rintro _ ⟨s, rfl⟩
      exact ⟨ConnectedComponents.mk s, rfl⟩
    exact (Set.finite_range _).subset this
  obtain ⟨b, hb⟩ := hrange.bddAbove
  exact ⟨b, fun s hs => hb ⟨⟨s, hs⟩, rfl⟩⟩

end Betti

/-! ### Dimension counts in a closed fibre -/

section FibreTopology

open Set _root_.Topology

variable {Y : Type*} [TopologicalSpace Y]

/-- `Λ` is a maximal irreducible subset of `A`. -/
private def IsMaxIrreducible (A Λ : Set Y) : Prop :=
  Λ ⊆ A ∧ IsIrreducible Λ ∧ ∀ Λ' ⊆ A, IsIrreducible Λ' → Λ ⊆ Λ' → Λ' ⊆ Λ

private theorem topologicalKrullDim_mono {Γ Γ' : Set Y} (h : Γ ⊆ Γ') :
    topologicalKrullDim Γ ≤ topologicalKrullDim Γ' :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- An irreducible subset of a finite union of closed sets lies in one of them. -/
private theorem exists_subset_of_isIrreducible_of_subset_iUnion {ι : Type*} [Finite ι]
    {C : ι → Set Y} (hC : ∀ k, IsClosed (C k)) {Γ : Set Y} (hΓ : IsIrreducible Γ)
    (hsub : Γ ⊆ ⋃ k, C k) : ∃ k, Γ ⊆ C k := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨z, hz, hΓz⟩ := isIrreducible_iff_sUnion_isClosed.1 hΓ (Finset.univ.image C)
    (fun z hz => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
      exact hC k)
    (by
      intro y hy
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hsub hy)
      exact ⟨C k, by simp, hk⟩)
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
  exact ⟨k, hΓz⟩

/-- In a set all of whose maximal irreducible subsets through a point have dimension `δ`, a
closed set all of whose irreducible subsets have dimension `< δ` is nowhere dense. -/
private theorem subset_closure_diff_of_lt {A E : Set Y} {δ : WithBot ℕ∞}
    (hA : ∀ y ∈ A, ∃ Λ, IsMaxIrreducible A Λ ∧ y ∈ Λ ∧ topologicalKrullDim Λ = δ)
    (hEc : IsClosed E) (hE : ∀ Γ ⊆ A ∩ E, IsIrreducible Γ → topologicalKrullDim Γ < δ) :
    A ⊆ closure (A \ E) := by
  intro y hy
  obtain ⟨Λ, ⟨hΛA, hΛi, -⟩, hyΛ, hΛd⟩ := hA y hy
  have hne : (Λ ∩ Eᶜ).Nonempty := by
    refine inter_compl_nonempty_iff.2 fun hΛE => ?_
    have hsub : Λ ⊆ A ∩ E := fun z hz => ⟨hΛA hz, hΛE hz⟩
    exact absurd (hE Λ hsub hΛi) (by rw [hΛd]; exact lt_irrefl δ)
  have := subset_closure_inter_of_isPreirreducible_of_isOpen hΛi.2 hEc.isOpen_compl hne
  exact closure_mono (s := Λ ∩ Eᶜ) (t := A \ E) (fun z hz => ⟨hΛA hz.1, hz.2⟩) (this hyΛ)

/-- **The dimension count in a closed fibre.** Let `Φ` be a set all of whose maximal irreducible
subsets have dimension `2`, covered by the traces `C k ∩ Φ` of finitely many closed sets, all
of whose maximal irreducible subsets have dimension `δ k`. Let `E k` be closed sets whose traces
on `C k ∩ Φ` have only irreducible subsets of dimension `< δ k`, and suppose that the good part
`(C k ∩ Φ) \ E k` lies in an open set `O k` meeting `Φ` only inside `C k`. Then every `δ k` with
`C k ∩ Φ` nonempty is `2`, and the good parts are dense in `Φ`. -/
private theorem eq_two_and_subset_closure_iUnion {ι : Type*} [Finite ι] {Φ : Set Y}
    {C E O : ι → Set Y} {δ : ι → WithBot ℕ∞}
    (hCc : ∀ k, IsClosed (C k)) (hEc : ∀ k, IsClosed (E k)) (hOo : ∀ k, IsOpen (O k))
    (hcov : Φ ⊆ ⋃ k, C k) (hOC : ∀ k, O k ∩ Φ ⊆ C k) (hG : ∀ k, (C k ∩ Φ) \ E k ⊆ O k)
    (hΦex : ∀ Γ ⊆ Φ, IsIrreducible Γ → ∃ Γ', IsMaxIrreducible Φ Γ' ∧ Γ ⊆ Γ')
    (hΦdim : ∀ Γ', IsMaxIrreducible Φ Γ' → topologicalKrullDim Γ' = 2)
    (hAex : ∀ k, ∀ Γ ⊆ C k ∩ Φ, IsIrreducible Γ →
      ∃ Λ, IsMaxIrreducible (C k ∩ Φ) Λ ∧ Γ ⊆ Λ)
    (hAdim : ∀ k Λ, IsMaxIrreducible (C k ∩ Φ) Λ → topologicalKrullDim Λ = δ k)
    (hE : ∀ k, ∀ Γ ⊆ C k ∩ Φ ∩ E k, IsIrreducible Γ → topologicalKrullDim Γ < δ k) :
    (∀ k, (C k ∩ Φ).Nonempty → δ k = 2) ∧ Φ ⊆ closure (⋃ k, (C k ∩ Φ) \ E k) := by
  have hle : ∀ k Λ, IsMaxIrreducible (C k ∩ Φ) Λ → δ k ≤ 2 := by
    intro k Λ hΛ
    obtain ⟨Γ', hΓ', hΛΓ'⟩ := hΦex Λ (fun z hz => (hΛ.1 hz).2) hΛ.2.1
    rw [← hAdim k Λ hΛ, ← hΦdim Γ' hΓ']
    exact topologicalKrullDim_mono hΛΓ'
  refine ⟨fun k ⟨y, hy⟩ => ?_, fun y hy => ?_⟩
  · obtain ⟨Λ, hΛ, hyΛ⟩ := hAex k {y} (singleton_subset_iff.2 hy) isIrreducible_singleton
    have hΛd := hAdim k Λ hΛ
    have hne : (Λ ∩ (E k)ᶜ).Nonempty := by
      refine inter_compl_nonempty_iff.2 fun hE' => ?_
      have hsub : Λ ⊆ C k ∩ Φ ∩ E k := fun z hz => ⟨hΛ.1 hz, hE' hz⟩
      exact absurd (hE k Λ hsub hΛ.2.1) (by rw [hΛd]; exact lt_irrefl _)
    obtain ⟨z, hzΛ, hzE⟩ := hne
    have hzO : z ∈ O k := hG k ⟨hΛ.1 hzΛ, hzE⟩
    obtain ⟨Γ', hΓ', hΛΓ'⟩ := hΦex Λ (fun z hz => (hΛ.1 hz).2) hΛ.2.1
    have hΓ'C : Γ' ⊆ C k := by
      have := subset_closure_inter_of_isPreirreducible_of_isOpen hΓ'.2.1.2 (hOo k)
        ⟨z, hΛΓ' hzΛ, hzO⟩
      refine this.trans ((closure_mono fun w hw => hOC k ⟨hw.2, hΓ'.1 hw.1⟩).trans ?_)
      exact (hCc k).closure_eq.le
    have hΓ'Λ : Γ' ⊆ Λ := hΛ.2.2 Γ' (fun w hw => ⟨hΓ'C hw, hΓ'.1 hw⟩) hΓ'.2.1 hΛΓ'
    rw [← hΛd, ← hΦdim Γ' hΓ', Set.Subset.antisymm hΛΓ' hΓ'Λ]
  · obtain ⟨Γ', hΓ', hyΓ'⟩ := hΦex {y} (singleton_subset_iff.2 hy) isIrreducible_singleton
    obtain ⟨k, hk⟩ := exists_subset_of_isIrreducible_of_subset_iUnion hCc hΓ'.2.1
      (hΓ'.1.trans hcov)
    have hΓ'A : Γ' ⊆ C k ∩ Φ := fun w hw => ⟨hk hw, hΓ'.1 hw⟩
    have hne : (Γ' ∩ (E k)ᶜ).Nonempty := by
      refine inter_compl_nonempty_iff.2 fun hE' => ?_
      have hsub : Γ' ⊆ C k ∩ Φ ∩ E k := fun z hz => ⟨hΓ'A hz, hE' hz⟩
      have h1 := hE k Γ' hsub hΓ'.2.1
      obtain ⟨Λ, hΛ, -⟩ := hAex k Γ' hΓ'A hΓ'.2.1
      have h2 := hle k Λ hΛ
      rw [hΦdim Γ' hΓ'] at h1
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hΓ'.2.1.2 (hEc k).isOpen_compl hne
    exact closure_mono (s := Γ' ∩ (E k)ᶜ) (t := ⋃ k, (C k ∩ Φ) \ E k)
      (fun w hw => mem_iUnion.2 ⟨k, hΓ'A hw.1, hw.2⟩) (this (hyΓ' rfl))

/-- For `Γ ⊆ A`, the trace of `Γ` in the subspace `A` is irreducible iff `Γ` is. -/
private theorem isIrreducible_preimage_val_iff {A Γ : Set Y} (hΓA : Γ ⊆ A) :
    IsIrreducible ((Subtype.val : A → Y) ⁻¹' Γ) ↔ IsIrreducible Γ := by
  have himg : (Subtype.val : A → Y) '' ((Subtype.val : A → Y) ⁻¹' Γ) = Γ := by
    rw [Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left.2 hΓA]
  refine ⟨fun h => himg ▸ h.image _ continuous_subtype_val.continuousOn, fun h => ?_⟩
  refine ⟨?_, fun u v hu hv hΓu hΓv => ?_⟩
  · obtain ⟨y, hy⟩ := h.nonempty
    exact ⟨⟨y, hΓA hy⟩, hy⟩
  · obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.1 hv
    obtain ⟨⟨a, ha⟩, ha1, ha2⟩ := hΓu
    obtain ⟨⟨b, hb⟩, hb1, hb2⟩ := hΓv
    obtain ⟨c, hcΓ, hcu, hcv⟩ := h.2 u' v' hu' hv' ⟨a, ha1, ha2⟩ ⟨b, hb1, hb2⟩
    exact ⟨⟨c, hΓA hcΓ⟩, hcΓ, hcu, hcv⟩

/-- A subset of `A` and its trace in the subspace `A` have the same dimension. -/
private theorem topologicalKrullDim_preimage_val {A Γ : Set Y} (hΓA : Γ ⊆ A) :
    topologicalKrullDim ((Subtype.val : A → Y) ⁻¹' Γ) = topologicalKrullDim Γ := by
  refine IsHomeomorph.topologicalKrullDim_eq
    (fun x : ((Subtype.val : A → Y) ⁻¹' Γ) => (⟨x.1.1, x.2⟩ : Γ)) ?_
  refine isHomeomorph_iff_isEmbedding_surjective.2 ⟨?_, fun y => ⟨⟨⟨y.1, hΓA y.2⟩, y.2⟩, rfl⟩⟩
  refine IsEmbedding.of_comp (g := (Subtype.val : Γ → Y))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) continuous_subtype_val ?_
  exact (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal :
    IsEmbedding (fun x : ((Subtype.val : A → Y) ⁻¹' Γ) => (x.1.1 : Y)))

/-- Maximal irreducible subsets of `A` are the irreducible components of the subspace `A`. -/
private theorem isMaxIrreducible_iff {A Λ : Set Y} (hΛA : Λ ⊆ A) :
    IsMaxIrreducible A Λ ↔ ((Subtype.val : A → Y) ⁻¹' Λ) ∈ irreducibleComponents A := by
  constructor
  · rintro ⟨-, hΛ, hmax⟩
    refine ⟨(isIrreducible_preimage_val_iff hΛA).2 hΛ, fun Λ' hΛ' hsub => ?_⟩
    have hΛ'A : (Subtype.val : A → Y) '' Λ' ⊆ A := Subtype.coe_image_subset A Λ'
    have h2 := hmax _ hΛ'A (hΛ'.image _ continuous_subtype_val.continuousOn)
      fun y hy => ⟨⟨y, hΛA hy⟩, hsub hy, rfl⟩
    exact fun x hx => h2 ⟨x, hx, rfl⟩
  · intro h
    refine ⟨hΛA, (isIrreducible_preimage_val_iff hΛA).1 h.1, fun Λ' hΛ'A hΛ' hsub => ?_⟩
    have h1 := h.2 ((isIrreducible_preimage_val_iff hΛ'A).2 hΛ')
      (Set.preimage_mono hsub)
    intro y hy
    exact h1 (show (⟨y, hΛ'A hy⟩ : A) ∈ (Subtype.val : A → Y) ⁻¹' Λ' from hy)

/-- Every irreducible subset of `A` lies in a maximal irreducible subset of `A`. -/
private theorem exists_isMaxIrreducible {A Γ : Set Y} (hΓA : Γ ⊆ A) (hΓ : IsIrreducible Γ) :
    ∃ Λ, IsMaxIrreducible A Λ ∧ Γ ⊆ Λ := by
  obtain ⟨Λ', hΛ', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    ((isIrreducible_preimage_val_iff hΓA).2 hΓ)
  have hΛA : (Subtype.val : A → Y) '' Λ' ⊆ A := Subtype.coe_image_subset A Λ'
  refine ⟨(Subtype.val : A → Y) '' Λ', (isMaxIrreducible_iff hΛA).2 ?_, fun y hy => ?_⟩
  · rwa [Set.preimage_image_eq _ Subtype.val_injective]
  · exact ⟨⟨y, hΓA hy⟩, hsub hy, rfl⟩

/-- A property of the dimensions of all irreducible components transfers along a
homeomorphism. -/
private theorem forall_irreducibleComponents_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (P : WithBot ℕ∞ → Prop)
    (h : ∀ C ∈ irreducibleComponents Y, P (topologicalKrullDim C)) :
    ∀ C ∈ irreducibleComponents X, P (topologicalKrullDim C) := by
  intro C hC
  have hC' : e '' C ∈ irreducibleComponents Y := by
    rw [← e.preimage_symm]
    exact preimage_mem_irreducibleComponents hC e.symm.isOpenEmbedding
      (by
        obtain ⟨c, hc⟩ := hC.1.nonempty
        exact ⟨c, hc, e.symm.surjective c⟩)
  have := h _ hC'
  rwa [← IsHomeomorph.topologicalKrullDim_eq _ (e.image C).isHomeomorph] at this

/-- If the dimensions of all irreducible components of a space homeomorphic to the subspace `A`
satisfy `P`, so does the dimension of every maximal irreducible subset of `A`. -/
private theorem topologicalKrullDim_of_isMaxIrreducible {Z : Type*} [TopologicalSpace Z] {A : Set Y}
    (e : Z ≃ₜ A) (P : WithBot ℕ∞ → Prop)
    (h : ∀ C ∈ irreducibleComponents Z, P (topologicalKrullDim C)) {Λ : Set Y}
    (hΛ : IsMaxIrreducible A Λ) : P (topologicalKrullDim Λ) := by
  rw [← topologicalKrullDim_preimage_val hΛ.1]
  exact forall_irreducibleComponents_of_homeomorph e.symm P h _ ((isMaxIrreducible_iff hΛ.1).1 hΛ)

/-- In an irreducible space, finitely many nonempty open sets meet. -/
private theorem nonempty_iInter_of_isOpen {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    {ι : Type*} [Finite ι] {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty) :
    (⋂ i, U i).Nonempty := by
  classical
  have := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, (⋂ i ∈ s, U i).Nonempty by simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact nonempty_preirreducible_inter (hU i) (isOpen_biInter_finset fun j _ => hU j) (hne i) ih

end FibreTopology

/-! ### Reduced closed subschemes -/

section ReducedSubschemes

open TopologicalSpace

/-- The reduced closed subscheme on a closed set `Z` has underlying set `Z`. -/
private theorem range_subschemeι_vanishingIdeal {X : Scheme.{0}} (Z : Closeds X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The reduced closed subscheme on an irreducible closed set is integral. -/
private theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{0}} {Z : Closeds X}
    (hZ : IsIrreducible (Z : Set X)) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  have := MMP.Intersection.Scheme.IdealSheafData.irreducibleSpace_subscheme_vanishingIdeal hZ
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The reduced closed subscheme on a closed set `Z` has the dimension of `Z`. -/
private theorem topologicalKrullDim_subscheme_vanishingIdeal {X : Scheme.{0}} (Z : Closeds X) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme =
      topologicalKrullDim (Z : Set X) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (MMP.Intersection.Scheme.IdealSheafData.subschemeHomeomorphSupport _).isHomeomorph,
    TopologicalSpace.Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)]
  rfl

end ReducedSubschemes

/-! ### Generic fibre dimension -/

section GenericFibres

open _root_.Topology TopologicalSpace

/-- The fibres of a morphism over a point, restricted to the image of a closed embedding. -/
private noncomputable def homeomorphFibreOfIsClosedEmbedding {Z X W : Type*} [TopologicalSpace Z]
    [TopologicalSpace X] (ι : Z → X) (hι : IsClosedEmbedding ι) (f : X → W) (x : W) :
    ((f ∘ ι) ⁻¹' {x} : Set Z) ≃ₜ (Set.range ι ∩ f ⁻¹' {x} : Set X) :=
  (hι.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext y
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩
        exact ⟨⟨z, rfl⟩, hz⟩
      · rintro ⟨⟨z, rfl⟩, hz⟩
        exact ⟨⟨z, hz⟩, rfl⟩))

/-- **Generic fibre dimension of an irreducible closed subset.** For a morphism `f : X ⟶ W` of
finite type separated schemes over `ℂ` with `W` integral and an irreducible closed `E ⊆ X`, over
a nonempty open of `W` every maximal irreducible subset `Λ` of a fibre of `E` satisfies
`dim Λ + dim W = dim E`. -/
private theorem exists_isOpen_forall_isMaxIrreducible {X W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ))
    [IsIntegral W] [LocallyOfFiniteType sW] [QuasiCompact sW] [IsSeparated sW] (f : X ⟶ W)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] {E : Set X} (hEc : IsClosed E)
    (hE : IsIrreducible E) :
    ∃ U : Set W, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, ∀ Λ, IsMaxIrreducible (E ∩ f ⁻¹' {x}) Λ →
      topologicalKrullDim Λ + topologicalKrullDim W = topologicalKrullDim E := by
  classical
  by_cases hd : closure (f '' E) = Set.univ
  · set I := Scheme.IdealSheafData.vanishingIdeal (⟨E, hEc⟩ : Closeds X) with hI
    set ι := I.subschemeι with hιdef
    have hιr : Set.range ι = E := range_subschemeι_vanishingIdeal _
    haveI : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal (Z := ⟨E, hEc⟩) hE
    haveI hWv : IsVariety ℂ sW := ⟨⟩
    haveI hEv : IsVariety ℂ ((ι ≫ f) ≫ sW) := ⟨⟩
    haveI : IsDominant (ι ≫ f) := ⟨by
      rw [DenseRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hιr,
        dense_iff_closure_eq]
      exact hd⟩
    obtain ⟨U, hUo, hUd, -, hU⟩ :=
      MMP.Foundations.exists_dense_isOpen_forall_irreducibleComponents_fiber_dim
        ((ι ≫ f) ≫ sW) sW hEv hWv (ι ≫ f) rfl
    have hdimE : topologicalKrullDim I.subscheme = topologicalKrullDim E :=
      topologicalKrullDim_subscheme_vanishingIdeal _
    refine ⟨U, hUo, hUd.nonempty, fun x hx Λ hΛ => ?_⟩
    have e := homeomorphFibreOfIsClosedEmbedding ι ι.isClosedEmbedding f x
    rw [hιr] at e
    rw [← hdimE]
    exact topologicalKrullDim_of_isMaxIrreducible e
      (fun d => d + topologicalKrullDim W = topologicalKrullDim I.subscheme) (hU x hx) hΛ
  · refine ⟨(closure (f '' E))ᶜ, isClosed_closure.isOpen_compl, Set.nonempty_compl.2 hd,
      fun x hx Λ hΛ => ?_⟩
    exfalso
    obtain ⟨y, hy⟩ := hΛ.2.1.nonempty
    have hyE := hΛ.1 hy
    exact hx (subset_closure ⟨y, hyE.1, hyE.2⟩)

/-- A proper closed subset of an irreducible closed subset of a scheme of finite type over `ℂ`
has smaller dimension. -/
private theorem topologicalKrullDim_lt_of_ssubset {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] [QuasiCompact sX] {C E : Set X} (hCc : IsClosed C)
    (hC : IsIrreducible C) (hEc : IsClosed E) (hEC : E ⊆ C) (hne : E ≠ C) :
    topologicalKrullDim E < topologicalKrullDim C := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  haveI : Nonempty C := hC.nonempty.to_subtype
  have hfin : topologicalKrullDim C ≠ ⊤ := by
    have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType ℂ sX
    exact ne_top_of_le_ne_top h1 (topologicalKrullDim_subspace_le X C)
  have hnd : IsNowhereDense ((Subtype.val : C → X) ⁻¹' E) := by
    rw [IsNowhereDense, (hEc.preimage continuous_subtype_val).closure_eq]
    by_contra h
    obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 h
    haveI : IrreducibleSpace C := isIrreducible_iff_irreducibleSpace.1 hC
    have hdense := isOpen_interior.dense ⟨u, hu⟩
    have hall : ((Subtype.val : C → X) ⁻¹' E) = Set.univ := by
      have := hdense.closure_eq
      rw [← Set.univ_subset_iff, ← this]
      exact closure_minimal interior_subset (hEc.preimage continuous_subtype_val)
    apply hne
    refine Set.Subset.antisymm hEC fun y hy => ?_
    have : (⟨y, hy⟩ : C) ∈ (Subtype.val : C → X) ⁻¹' E := by rw [hall]; trivial
    exact this
  have := IsNowhereDense.topologicalKrullDim_lt hnd (hEc.preimage continuous_subtype_val)
    inferInstance hfin
  rwa [topologicalKrullDim_preimage_val hEC] at this

/-- **The resolution of a component.** For an irreducible component `C` of a reduced scheme `F`
of finite type and separated over `ℂ`, there is a smooth integral `R` with a morphism `g : R ⟶ F`
onto `C`, projective after composing with any projective `π : F ⟶ W`, which is an isomorphism
over a nonempty open `G ⊆ C` missing every other component; and `dim R = dim C`. -/
private theorem exists_resolution_of_mem_irreducibleComponents {F : Scheme.{0}} (sF : F ⟶ Spec (.of ℂ))
    [IsReduced F] [LocallyOfFiniteType sF] [QuasiCompact sF] [IsSeparated sF] {C : Set F}
    (hC : C ∈ irreducibleComponents F) :
    ∃ (R : Scheme.{0}) (g : R ⟶ F) (G : F.Opens), IsIntegral R ∧ Smooth (g ≫ sF) ∧
      (∀ {W : Scheme.{0}} (π : F ⟶ W), IsProjectiveMorphism π → CompactSpace W →
        QuasiSeparatedSpace W → IsProjective (g ≫ π)) ∧
      Set.range g = C ∧ (G : Set F).Nonempty ∧ (G : Set F) ⊆ C ∧
      (∀ C' ∈ irreducibleComponents F, C' ≠ C → Disjoint (G : Set F) C') ∧
      IsIso (g ∣_ G) ∧ topologicalKrullDim R = topologicalKrullDim C := by
  classical
  have : CompactSpace F := QuasiCompact.compactSpace_of_compactSpace sF
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian sF
  have : IsNoetherian F := ⟨⟩
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨C, hCc⟩ : Closeds F) with hI
  set ι := I.subschemeι with hιdef
  have hιr : Set.range ι = C := range_subschemeι_vanishingIdeal _
  haveI : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal (Z := ⟨C, hCc⟩) hC.1
  haveI hXv : IsVariety ℂ (ι ≫ sF) := ⟨⟩
  obtain ⟨R, g₀, hRv, hproj, hbir, hsm, hiso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution (ι ≫ sF) hXv
  haveI := hRv
  have : IsProper g₀ := hproj.isProper
  set g := g₀ ≫ ι with hgdef
  -- the other components and the good open
  set O : Set F := (⋃₀ (irreducibleComponents F \ {C}))ᶜ with hOdef
  have hfinc := NoetherianSpace.finite_irreducibleComponents (α := F)
  have hOo : IsOpen O := by
    rw [hOdef, isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hfinc.diff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have hOC : O ⊆ C := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ : ∃ W ∈ irreducibleComponents F, x ∈ W := by
      have := (isIrreducible_singleton (x := x))
      obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ this
      exact ⟨W, hW, hxW rfl⟩
    by_contra hxC
    exact hx ⟨W, ⟨hW, fun h => hxC (h ▸ hxW)⟩, hxW⟩
  have hOne : O.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, hOdef, Set.compl_empty_iff] at h
    have hsub : C ⊆ ⋃₀ (irreducibleComponents F \ {C}) := by rw [h]; exact Set.subset_univ _
    obtain ⟨W, hW, hCW⟩ := isIrreducible_iff_sUnion_isClosed.1 hC.1 hfinc.diff.toFinset
      (by
        intro W hW
        rw [Set.Finite.mem_toFinset] at hW
        exact isClosed_of_mem_irreducibleComponents W hW.1)
      (by simpa using hsub)
    rw [Set.Finite.mem_toFinset] at hW
    exact hW.2 (Set.Subset.antisymm (hC.2 hW.1.1 hCW) hCW)
  obtain ⟨V', hV'o, hV'⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.1
    (MMP.Mori.smoothLocus (ι ≫ sF)).isOpen
  set G : F.Opens := ⟨O ∩ V', hOo.inter hV'o⟩ with hGdef
  have hGC : (G : Set F) ⊆ C := fun x hx => hOC hx.1
  have hGsm : ι ⁻¹ᵁ G ≤ MMP.Mori.smoothLocus (ι ≫ sF) := by
    intro x hx
    change x ∈ ((MMP.Mori.smoothLocus (ι ≫ sF) : I.subscheme.Opens) : Set I.subscheme)
    rw [← hV']
    exact hx.2
  refine ⟨R, g, G, inferInstance, ?_, ?_, ?_, ?_, hGC, ?_, ?_, ?_⟩
  · have := (MMP.Mori.isSmoothScheme_iff (g₀ ≫ ι ≫ sF)).1 hsm
    rw [hgdef, Category.assoc]
    exact this
  · intro W π hπ _ _
    obtain ⟨n, i, hi, hif⟩ := hπ
    haveI := hi
    have hιπ : IsProjectiveMorphism (ι ≫ π) := ⟨n, ι ≫ i, inferInstance, by rw [Category.assoc, hif]⟩
    have := hproj.comp hιπ.isProjective
    rw [hgdef, Category.assoc]
    exact this
  · -- `g₀` is surjective
    have hdom := hbir.isDominant
    have hcl : IsClosed (Set.range g₀) := g₀.isClosedMap.isClosed_range
    have hsurj : Set.range g₀ = Set.univ := by
      rw [← hcl.closure_eq]
      exact hdom.denseRange.closure_range
    rw [hgdef, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj, Set.image_univ, hιr]
  · -- `G` is nonempty
    obtain ⟨x, hxO⟩ := hOne
    have h1 : (ι ⁻¹' O).Nonempty := by
      obtain ⟨y, rfl⟩ : x ∈ Set.range ι := hιr ▸ hOC hxO
      exact ⟨y, hxO⟩
    have h2 : ((MMP.Mori.smoothLocus (ι ≫ sF) : I.subscheme.Opens) : Set I.subscheme).Nonempty := by
      refine ⟨genericPoint I.subscheme, ?_⟩
      rw [MMP.Mori.smoothLocus_eq_smoothLocus]
      exact (ι ≫ sF).genericPoint_mem_smoothLocus_of_perfectField
    obtain ⟨y, hy1, hy2⟩ := nonempty_preirreducible_inter (hOo.preimage ι.continuous)
      (MMP.Mori.smoothLocus (ι ≫ sF)).isOpen h1 h2
    refine ⟨ι y, hy1, ?_⟩
    exact show y ∈ ι ⁻¹' V' by rwa [hV']
  · intro C' hC' hne
    rw [Set.disjoint_left]
    intro x hx hxC'
    exact hx.1 ⟨C', ⟨hC', hne⟩, hxC'⟩
  · -- the isomorphism over `G`
    rw [hgdef, morphismRestrict_comp]
    have h1 : IsIso (g₀ ∣_ ι ⁻¹ᵁ G) :=
      haveI := hiso; MMP.Resolution.Kollar.isIso_morphismRestrict_of_le g₀ hGsm
    haveI : IsClosedImmersion (ι ∣_ G) := inferInstance
    haveI : Surjective (ι ∣_ G) := by
      refine ⟨fun ⟨z, hz⟩ => ?_⟩
      obtain ⟨y, hy⟩ : z ∈ Set.range ι := hιr ▸ hGC hz
      refine ⟨⟨y, show ι y ∈ G by rw [hy]; exact hz⟩, Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe ι G _).trans hy
    have h2 : IsIso (ι ∣_ G) := isIso_of_isClosedImmersion_of_surjective _
    exact IsIso.comp_isIso' h1 h2
  · -- dimensions
    rw [← show topologicalKrullDim I.subscheme = topologicalKrullDim C from
      topologicalKrullDim_subscheme_vanishingIdeal _]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) (ι ≫ sF)
      (g₀ ≫ ι ≫ sF)
      hbir).symm

/-- A nonempty open of a quasi-compact scheme locally of finite type over `ℂ` contains a
`ℂ`-point. -/
public theorem _root_.MMP.Fourfold.exists_complexPoint_mem {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [QuasiCompact sX] {V : X.Opens}
    (hV : (V : Set X).Nonempty) :
    ∃ x : Spec (.of ℂ) ⟶ X, x ≫ sX = 𝟙 _ ∧ x (default : Spec (.of ℂ)) ∈ V := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ sX⟩
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (V.ι ≫ sX) from inferInstance
  haveI : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.1 (NoetherianSpace.isCompact (V : Set X))
  haveI : Nonempty V.toScheme := hV.to_subtype
  obtain ⟨v, -, hv⟩ := IsClosed.exists_closed_singleton (X := V.toScheme) isClosed_univ
    Set.univ_nonempty
  obtain p := (MMP.UnderlyingSpace.equivClosedPoints (K := ℂ) V.toScheme).symm
    ⟨v, hv⟩
  refine ⟨p.toHom ≫ V.ι, ?_, ?_⟩
  · rw [Category.assoc]
    exact MMP.UnderlyingSpace.toHom_comp_over p
  · rw [Scheme.Hom.comp_apply]
    exact (p.toHom default).2

/-- A smooth irreducible open of a scheme over `ℂ` has constant relative dimension. -/
private theorem exists_smoothOfRelativeDimension_of_irreducibleSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IrreducibleSpace X] (V : X.Opens) (hV : (V : Set X).Nonempty)
    [Smooth (V.ι ≫ sX)] : ∃ d, SmoothOfRelativeDimension d (V.ι ≫ sX) := by
  obtain ⟨x₀, hx₀⟩ := hV
  let p₀ : V.toScheme := ⟨x₀, hx₀⟩
  haveI : Nonempty V.toScheme := ⟨p₀⟩
  haveI : Nonempty {x // x ∈ (V : Set X)} := ⟨⟨x₀, hx₀⟩⟩
  haveI : IrreducibleSpace V.toScheme :=
    (IsOpen.isOpenEmbedding_subtypeVal V.isOpen).irreducibleSpace
  obtain ⟨d, hd⟩ := MMP.Analytic.ComplexPoints.exists_mem_relativeDimensionLocus
    (sX := V.ι ≫ sX) p₀
  set L := MMP.Analytic.ComplexPoints.relativeDimensionLocus (V.ι ≫ sX) d with hL
  have hLc : IsClosed (L : Set V.toScheme) :=
    MMP.Analytic.ComplexPoints.isClosed_relativeDimensionLocus d
  have hLtop : L = ⊤ := by
    have := (isClopen_iff.1 ⟨hLc, L.isOpen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨p₀, hd⟩)
    exact SetLike.coe_injective (by simpa using this)
  refine ⟨d, ?_⟩
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} d)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun _ : Unit => L) (by simp [hLtop]) fun _ => ?_
  exact MMP.Analytic.ComplexPoints.smoothOfRelativeDimension_relativeDimensionLocus d

/-- The fibre of a restriction over a point is homeomorphic to the fibre of the morphism. -/
private noncomputable def homeomorphFiberRestrict {X Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens)
    (y : V.toScheme) : (f ∣_ V).fiber y ≃ₜ f.fiber y.1 :=
  ((f ∣_ V).fiberHomeo y).trans <| (Homeomorph.trans
    ((isHomeomorph_iff_isEmbedding_surjective
      (f := fun p : ((f ∣_ V) ⁻¹' {y} : Set (f ⁻¹ᵁ V).toScheme) ↦
        (⟨p.1.1, by
          have h := congrArg Subtype.val (show (f ∣_ V) p.1 = y from p.2)
          rw [morphismRestrict_base_coe] at h
          exact h⟩ : (f ⁻¹' {y.1} : Set X)))).mpr
      ⟨(IsEmbedding.of_comp_iff (g := ((↑) : (f ⁻¹' {y.1} : Set X) → X))
          IsEmbedding.subtypeVal).mp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal :
            IsEmbedding fun p : ((f ∣_ V) ⁻¹' {y} : Set (f ⁻¹ᵁ V).toScheme) ↦ (p.1.1 : X)),
        fun ⟨x, hx⟩ ↦ ⟨⟨⟨x, show f x ∈ V by
          rw [show f x = y.1 from hx]; exact y.2⟩,
            Subtype.ext ((morphismRestrict_base_coe f V _).trans hx)⟩, rfl⟩⟩).homeomorph
    (f.fiberHomeo y.1).symm)

/-- A restriction of a smooth restriction is smooth. -/
private theorem smooth_morphismRestrict_of_le {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {U V : Y.Opens}
    (hU : Smooth (f ∣_ U)) (hVU : V ≤ U) : Smooth (f ∣_ V) := by
  haveI := hU
  have key : ∀ x : X, f x ∈ U → (f.stalkMap x).hom.FormallySmooth := by
    intro x hx
    let xU : (f ⁻¹ᵁ U).toScheme := ⟨x, show x ∈ f ⁻¹ᵁ U from hx⟩
    have h1 : xU ∈ (f ∣_ U).smoothLocus := by
      rw [(f ∣_ U).smoothLocus_eq_top]
      trivial
    exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U xU)).mp (Scheme.Hom.mem_smoothLocus.1 h1)
  refine Scheme.Hom.smoothLocus_eq_top_iff.mp (top_unique fun x _ => ?_)
  rw [Scheme.Hom.mem_smoothLocus]
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap f V x)).mpr (key x.1 (hVU x.2))

set_option backward.isDefEq.respectTransparency.types false in
/-- **Relative dimension of a restricted smooth family.** If `p` is smooth over an open `U` and
all irreducible components of its fibres over `U` have dimension `n`, then `p` is smooth of
relative dimension `n` over every open `V ⊆ U`. -/
private theorem smoothOfRelativeDimension_restrict {X W : Scheme.{0}} (p : X ⟶ W)
    [LocallyOfFinitePresentation p] (U : W.Opens) (hU : Smooth (p ∣_ U)) {n : ℕ}
    (hdim : ∀ t ∈ U, ∀ Z ∈ irreducibleComponents (p.fiber t), topologicalKrullDim Z = n)
    (V : W.Opens) (hVU : V ≤ U) : SmoothOfRelativeDimension n (p ∣_ V) := by
  have hsm : Smooth (p ∣_ V) := smooth_morphismRestrict_of_le p hU hVU
  haveI : LocallyOfFiniteType (p ∣_ V) := inferInstance
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq (p ∣_ V) n fun x => ?_
  set y := (p ∣_ V) x
  have : LocallyOfFiniteType ((p ∣_ V).fiberToSpecResidueField y) := by
    change LocallyOfFiniteType (pullback.snd (p ∣_ V) (V.toScheme.fromSpecResidueField y))
    infer_instance
  have hcomp : ∀ Z ∈ irreducibleComponents ((p ∣_ V).fiber y), topologicalKrullDim Z = n :=
    forall_irreducibleComponents_of_homeomorph (homeomorphFiberRestrict p V y) (· = n)
      (hdim y.1 (hVU y.2))
  rw [@topologicalKrullDimAt_eq_iSup_irreducibleComponents _ _ _
    ((p ∣_ V).fiberToSpecResidueField y) this]
  obtain ⟨Z₀, hZ₀, hxZ₀⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := (p ∣_ V).asFiber x))
  refine le_antisymm (iSup₂_le fun Z hZ => (hcomp Z hZ.1).le) ?_
  exact le_iSup₂_of_le (f := fun Z (_ : Z ∈ {Z ∈ irreducibleComponents ((p ∣_ V).fiber y) |
    (p ∣_ V).asFiber x ∈ Z}) => topologicalKrullDim Z) Z₀ ⟨hZ₀, hxZ₀ rfl⟩ (hcomp Z₀ hZ₀).ge

end GenericFibres

/-! ### Closed fibres and resolved strata -/

section Fibres

open _root_.Topology

/-- The fibre of `f` over a `ℂ`-point `b` embeds into the source, onto the preimage of the point
underlying `b`. -/
private theorem isEmbedding_and_range_pullback_fst {X B : Scheme.{0}} {sB : B ⟶ Spec (.of ℂ)}
    (f : X ⟶ B) (b : Spec (.of ℂ) ⟶ B) (hb : b ≫ sB = 𝟙 _) :
    IsEmbedding (pullback.fst f b) ∧
      Set.range (pullback.fst f b) = f ⁻¹' {b (default : Spec (.of ℂ))} := by
  have : IsClosedImmersion b := isClosedImmersion_of_comp_eq_id sB b hb
  refine ⟨(pullback.fst f b).isClosedEmbedding.isEmbedding, ?_⟩
  rw [Scheme.Pullback.range_fst]
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    rfl
  · rintro rfl
    exact ⟨default, rfl⟩

/-- Density in a closed fibre, read in the source. -/
private theorem dense_preimage_pullback_fst {X B : Scheme.{0}} {sB : B ⟶ Spec (.of ℂ)}
    (f : X ⟶ B) (b : Spec (.of ℂ) ⟶ B) (hb : b ≫ sB = 𝟙 _) (V : Set X)
    (hV : f ⁻¹' {b (default : Spec (.of ℂ))} ⊆
      closure (V ∩ f ⁻¹' {b (default : Spec (.of ℂ))})) :
    Dense (pullback.fst f b ⁻¹' V) := by
  obtain ⟨hemb, hrange⟩ := isEmbedding_and_range_pullback_fst f b hb
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hz : pullback.fst f b z ∈ closure (V ∩ Set.range (pullback.fst f b)) := by
    rw [hrange]
    exact hV (hrange ▸ ⟨z, rfl⟩)
  rw [hemb.closure_eq_preimage_closure_image]
  have : (pullback.fst f b) '' (pullback.fst f b ⁻¹' V) = V ∩ Set.range (pullback.fst f b) :=
    Set.image_preimage_eq_inter_range
  rw [Set.mem_preimage, this]
  exact hz

/-- Transport of a resolved fibre along an isomorphism of fibres over `ℂ`. -/
private theorem Stratum.Resolves.of_iso {σ : Stratum} {𝒵 𝒵' T T' : Scheme.{0}} {h : 𝒵 ⟶ T}
    {h' : 𝒵' ⟶ T'} {t : Spec (.of ℂ) ⟶ T} {t' : Spec (.of ℂ) ⟶ T'} (hres : σ.Resolves h t)
    (e : pullback h t ≅ pullback h' t')
    (he : e.hom ≫ pullback.snd h' t' = pullback.snd h t) : σ.Resolves h' t' := by
  obtain ⟨s, hs, p, hp, U, hU, hpU, hiso⟩ := hres
  have hU' : e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, Iso.hom_inv_id, Scheme.Hom.id_preimage]
  refine ⟨s, hs, p ≫ e.hom, by rw [Category.assoc, he, hp], e.inv ⁻¹ᵁ U, ?_, ?_, ?_⟩
  · exact (Scheme.homeoOfIso e.symm).dense_preimage hU
  · rw [Scheme.Hom.comp_preimage, hU']
    exact hpU
  · rw [morphismRestrict_comp]
    have h1 : IsIso (p ∣_ e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U)) := by rwa [hU']
    have h2 : IsIso (e.hom ∣_ e.inv ⁻¹ᵁ U) :=
      (isPullback_morphismRestrict e.hom (e.inv ⁻¹ᵁ U)).isIso_fst_of_isIso
    exact IsIso.comp_isIso' h1 h2

/-- **A global isomorphism over an open resolves a fibre.** Let `P : Y ⟶ F` be a morphism over
`ι : S ⟶ W` with `ι` a monomorphism, an isomorphism over an open `G ⊆ F`. If over a `ℂ`-point
`s` of `S` the trace of `G` is dense in the fibre of `F` and the trace of `P⁻¹ G` is dense in
the fibre of `Y`, then the stratum resolves the fibre of `F` over `s ≫ ι`. -/
private theorem Stratum.resolves_of_isIso_restrict (σ : Stratum) {W F : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} (ι : σ.S ⟶ W) [Mono ι] (hι : ι ≫ sW = σ.sS) (π : F ⟶ W)
    (P : σ.Y ⟶ F) (hP : P ≫ π = σ.q ≫ ι) (G : F.Opens) (hG : IsIso (P ∣_ G))
    (s : Spec (.of ℂ) ⟶ σ.S) (hs : s ≫ σ.sS = 𝟙 _)
    (hd1 : π ⁻¹' {(s ≫ ι) (default : Spec (.of ℂ))} ⊆
      closure ((G : Set F) ∩ π ⁻¹' {(s ≫ ι) (default : Spec (.of ℂ))}))
    (hd2 : σ.q ⁻¹' {s (default : Spec (.of ℂ))} ⊆
      closure (P ⁻¹' (G : Set F) ∩ σ.q ⁻¹' {s (default : Spec (.of ℂ))})) :
    σ.Resolves π (s ≫ ι) := by
  have hw : (s ≫ ι) ≫ sW = 𝟙 _ := by rw [Category.assoc, hι, hs]
  set p₀ : pullback σ.q s ⟶ pullback π (s ≫ ι) :=
    pullback.lift (pullback.fst σ.q s ≫ P) (pullback.snd σ.q s) (by
      rw [Category.assoc, hP, ← Category.assoc, pullback.condition, Category.assoc]) with hp₀def
  have hp₀ : p₀ ≫ pullback.snd π (s ≫ ι) = pullback.snd σ.q s := pullback.lift_snd _ _ _
  have hp₀f : p₀ ≫ pullback.fst π (s ≫ ι) = pullback.fst σ.q s ≫ P := pullback.lift_fst _ _ _
  -- the fibre of `Y` is the base change of `P` along the fibre of `F`
  have hsq : IsPullback (pullback.fst σ.q s) p₀ P (pullback.fst π (s ≫ ι)) := by
    have h1 : IsPullback (pullback.snd σ.q s ≫ 𝟙 _) (pullback.fst σ.q s) (s ≫ ι)
        (σ.q ≫ ι) :=
      (IsPullback.of_hasPullback σ.q s).flip.paste_horiz
        (by simpa using (IsPullback.id_horiz s).paste_vert (IsKernelPair.id_of_mono ι))
    rw [Category.comp_id, ← hp₀, ← hP] at h1
    exact (IsPullback.of_right h1 hp₀f (IsPullback.of_hasPullback π (s ≫ ι)).flip).flip
  -- the isomorphism over `G` base changes
  set UT : (pullback π (s ≫ ι)).Opens := pullback.fst π (s ≫ ι) ⁻¹ᵁ G with hUT
  have hUY : p₀ ⁻¹ᵁ UT = pullback.fst σ.q s ⁻¹ᵁ (P ⁻¹ᵁ G) ⊓ p₀ ⁻¹ᵁ UT := by
    rw [hUT, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hp₀f, inf_idem]
  have hres := Scheme.Hom.isPullback_resLE hsq (US := G) (UT := UT) (UX := P ⁻¹ᵁ G)
    le_rfl le_rfl hUY
  have : IsIso (P.resLE G (P ⁻¹ᵁ G) le_rfl) := by
    rwa [Scheme.Hom.resLE_eq_morphismRestrict]
  have hiso : IsIso (p₀ ∣_ UT) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    exact hres.isIso_snd_of_isIso
  refine ⟨s, hs, p₀, hp₀, UT, ?_, ?_, hiso⟩
  · exact dense_preimage_pullback_fst (sB := sW) π (s ≫ ι) hw G hd1
  · have : ((p₀ ⁻¹ᵁ UT : (pullback σ.q s).Opens) : Set (pullback σ.q s : Scheme.{0})) =
        pullback.fst σ.q s ⁻¹' (P ⁻¹' (G : Set F)) := by
      rw [hUT, ← Scheme.Hom.comp_preimage, hp₀f]
      rfl
    rw [this]
    exact dense_preimage_pullback_fst (sB := σ.sS) σ.q s hs _ hd2

end Fibres

/-! ### Stratification -/

section Stratification

open _root_.Topology TopologicalSpace

/-- **Noetherian induction.** If over every irreducible closed subset `Z₁` of a noetherian space
some member of a family covers a nonempty relatively open part of `Z₁`, then finitely many
members cover every closed set. -/
private theorem exists_list_forall_of_isIrreducible {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    {ι : Type*} (R : ι → X → Prop)
    (hgen : ∀ Z₁ : Set X, IsClosed Z₁ → IsIrreducible Z₁ →
      ∃ V : Set X, IsOpen V ∧ (V ∩ Z₁).Nonempty ∧ ∃ i, ∀ x ∈ V ∩ Z₁, R i x) :
    ∀ Z : Closeds X, ∃ L : List ι, ∀ x ∈ Z, ∃ i ∈ L, R i x := by
  intro Z
  induction Z using WellFoundedLT.induction with
  | ind Z IH =>
  by_cases hZ : (Z : Set X) = ∅
  · refine ⟨[], fun x hx => ?_⟩
    have : x ∈ (Z : Set X) := hx
    rw [hZ] at this
    exact absurd this (Set.notMem_empty x)
  obtain ⟨S, hSf, hSc, hSi, hSU'⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible Z.2
  have hSU : (Z : Set X) = ⋃₀ S := hSU'
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.sUnion_empty] at hSU
    exact hZ hSU
  obtain ⟨Z₁, hZ₁S, hmax⟩ := hSf.exists_maximal hSne
  set O := ⋃₀ (S \ {Z₁}) with hOdef
  have hOc : IsClosed O := (hSf.diff).isClosed_sUnion fun t ht => hSc t ht.1
  have hZ₁O : ¬ Z₁ ⊆ O := by
    intro hsub
    obtain ⟨t, htS, ht⟩ := isIrreducible_iff_sUnion_isClosed.1 (hSi Z₁ hZ₁S) ((hSf.diff).toFinset)
      (by simpa using fun t ht _ => hSc t ht) (by simpa [hOdef] using hsub)
    simp only [Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff] at htS
    exact htS.2 (Set.Subset.antisymm (hmax htS.1 ht) ht)
  obtain ⟨V, hV, hVne, i, hi⟩ := hgen Z₁ (hSc Z₁ hZ₁S) (hSi Z₁ hZ₁S)
  set V' := V ∩ Oᶜ with hV'def
  have hV'ne : (V' ∩ Z₁).Nonempty := by
    have h2 : (Z₁ ∩ Oᶜ).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      exact hZ₁O fun x hx => by
        by_contra hxO
        exact (Set.eq_empty_iff_forall_notMem.1 h) x ⟨hx, hxO⟩
    obtain ⟨x, hx⟩ := (hSi Z₁ hZ₁S).2 V Oᶜ hV hOc.isOpen_compl
      (by rwa [Set.inter_comm] at hVne) h2
    exact ⟨x, ⟨hx.2.1, hx.2.2⟩, hx.1⟩
  have hsub : ∀ x ∈ (Z : Set X), x ∈ V' → x ∈ Z₁ := by
    intro x hxZ hxV
    rw [hSU] at hxZ
    obtain ⟨t, htS, hxt⟩ := hxZ
    by_contra hx
    have htZ : t ≠ Z₁ := fun h => hx (h ▸ hxt)
    exact hxV.2 ⟨t, ⟨htS, htZ⟩, hxt⟩
  set Z' : Closeds X := Z ⊓ ⟨V'ᶜ, (hV.inter hOc.isOpen_compl).isClosed_compl⟩ with hZ'def
  have hZ'lt : Z' < Z := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    obtain ⟨x, hxV, hxZ₁⟩ := hV'ne
    have hxZ : x ∈ (Z : Set X) := by rw [hSU]; exact ⟨Z₁, hZ₁S, hxZ₁⟩
    rw [← heq] at hxZ
    exact hxZ.2 hxV
  obtain ⟨L', hL'⟩ := IH Z' hZ'lt
  refine ⟨i :: L', fun x hx => ?_⟩
  by_cases hxV : x ∈ V'
  · exact ⟨i, List.mem_cons_self, hi x ⟨hxV.1, hsub x hx hxV⟩⟩
  · obtain ⟨j, hj, hjx⟩ := hL' x ⟨hx, hxV⟩
    exact ⟨j, List.mem_cons_of_mem _ hj, hjx⟩

/-- A `ℂ`-point lying on a closed subscheme factors through it. -/
private theorem exists_comp_eq_of_isClosedImmersion {Z X : Scheme.{0}} (i : Z ⟶ X)
    [IsClosedImmersion i] (p : Spec (.of ℂ) ⟶ X) (hp : p (default : Spec (.of ℂ)) ∈ Set.range i) :
    ∃ q : Spec (.of ℂ) ⟶ Z, q ≫ i = p := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := i) default z hz.symm
  have : Surjective (pullback.fst p i) := ⟨fun x ↦ ⟨w, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.fst p i)
  exact ⟨inv (pullback.fst p i) ≫ pullback.snd p i, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- A quasi-projective scheme over `ℂ` is separated. -/
private theorem isSeparated_of_isQuasiProjective {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : Stacks.HProjective.IsQuasiProjective sX) : IsSeparated sX := by
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of ℂ))
  have hM := Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))
  obtain ⟨n, i, hi, -, hif⟩ := isHQuasiProjective_of_isQuasiProjective sX _ hM hX
  haveI := hi
  rw [← hif]
  infer_instance

/-- **The stratum of a family of resolved components.** Let `g C : R C ⟶ F` be finitely many
morphisms over `π : F ⟶ W`, isomorphisms over pairwise disjoint opens `G C`, with `g C ≫ π`
projective and smooth of relative dimension two over an open `W₀` of `W` smooth of relative
dimension `d`. If over every `ℂ`-point of `W₀` the opens `G C` are dense in the fibre of `F`
and their preimages are dense in the fibres of the `R C`, then the disjoint union of the `R C`
over `W₀` is a resolved stratum resolving the fibres of `π` over the `ℂ`-points of `W₀`. -/
private theorem exists_stratum_of_family {W F : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ)) [IsSeparated sW]
    (hWq : Stacks.HProjective.IsQuasiProjective sW) (π : F ⟶ W) (W₀ : W.Opens) {d : ℕ}
    (hd : SmoothOfRelativeDimension d (W₀.ι ≫ sW)) {D : Type} [Finite D] (R : D → Scheme.{0})
    (g : ∀ C, R C ⟶ F) (hsm : ∀ C, SmoothOfRelativeDimension 2 ((g C ≫ π) ∣_ W₀))
    (hpr : ∀ C, IsProjective (g C ≫ π)) (G : D → F.Opens) (hiso : ∀ C, IsIso (g C ∣_ G C))
    (hdisj : ∀ C C', C ≠ C' → Disjoint (Set.range (g C')) (G C : Set F))
    (hd1 : ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ → w (default : Spec (.of ℂ)) ∈ W₀ →
      π ⁻¹' {w default} ⊆ closure ((⋃ C, (G C : Set F)) ∩ π ⁻¹' {w default}))
    (hd2 : ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ → w (default : Spec (.of ℂ)) ∈ W₀ → ∀ C,
      (g C ≫ π) ⁻¹' {w default} ⊆
        closure (g C ⁻¹' (G C : Set F) ∩ (g C ≫ π) ⁻¹' {w default})) :
    ∃ σ : Stratum, ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ → w (default : Spec (.of ℂ)) ∈ W₀ →
      σ.Resolves π w := by
  classical
  have : QuasiCompact sW := hWq.quasiCompact
  have : LocallyOfFiniteType sW := hWq.locallyOfFiniteType
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : IsNoetherian W := ⟨⟩
  set Rₒ : D → Scheme.{0} := fun C => ((g C ≫ π) ⁻¹ᵁ W₀).toScheme with hRₒ
  set q : ∐ Rₒ ⟶ W₀.toScheme := Sigma.desc fun C => (g C ≫ π) ∣_ W₀ with hq
  set P : ∐ Rₒ ⟶ F := Sigma.desc fun C => ((g C ≫ π) ⁻¹ᵁ W₀).ι ≫ g C with hPdef
  have hP : P ≫ π = q ≫ W₀.ι := by
    refine Sigma.hom_ext _ _ fun C => ?_
    simp only [hPdef, hq, Sigma.ι_desc_assoc, Category.assoc, morphismRestrict_ι]
  have hsS : Stacks.HProjective.IsQuasiProjective (W₀.ι ≫ sW) :=
    IsQuasiProjective.comp W₀.ι sW (isQuasiProjective_of_isImmersion W₀.ι) hWq
  have hqproj : IsProjectiveMorphism q := by
    haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of ℂ))
    have hMℂ := Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))
    obtain ⟨M, hMi, hM⟩ := exists_isAmple_of_isQuasiProjective (W₀.ι ≫ sW) _ hMℂ hsS
    haveI := hMi
    have hpiece : ∀ C, IsProjective ((g C ≫ π) ∣_ W₀) := fun C =>
      IsProjective.of_isPullback (isPullback_morphismRestrict (g C ≫ π) W₀) (hpr C)
    haveI : ∀ C, IsProper ((g C ≫ π) ∣_ W₀) := fun C => (hpiece C).isProper
    haveI : IsProper q := isProper_sigmaDesc _
    have hqp : IsQuasiProjective q :=
      isQuasiProjective_sigmaDesc _ ⟨M, hMi, hM⟩ (fun C => (hpiece C).isQuasiProjective)
    have hqP : IsProjective q :=
      (isProjective_iff_isQuasiProjective_and_isProper q).2 ⟨hqp, inferInstance⟩
    exact isProjectiveMorphism_of_isProjective q M hM hqP
  have hqsm : SmoothOfRelativeDimension 2 q := by
    let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 2) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} 2)
    exact IsZariskiLocalAtSource.sigmaDesc hsm
  let σ : Stratum := ⟨W₀, W₀.ι ≫ sW, ∐ Rₒ, q, d, hd, inferInstance, hsS, hqproj, hqsm⟩
  set G' : F.Opens := (⨆ C, G C) ⊓ π ⁻¹ᵁ W₀ with hG'def
  have hPι : ∀ C (r : Rₒ C), P (Sigma.ι Rₒ C r) = g C r.1 := by
    intro C r
    rw [← Scheme.Hom.comp_apply, hPdef, Sigma.ι_desc]
    rfl
  have hιP : ∀ C, Sigma.ι Rₒ C ≫ P = ((g C ≫ π) ⁻¹ᵁ W₀).ι ≫ g C := fun C => by
    simp only [hPdef, Sigma.ι_desc]
  have hGsurj : ∀ C, (G C : Set F) ⊆ Set.range (g C) := fun C z hz => by
    haveI := hiso C
    obtain ⟨r, hr⟩ := (Scheme.homeoOfIso (asIso (g C ∣_ G C))).surjective ⟨z, hz⟩
    exact ⟨r.1, (morphismRestrict_base_coe (g C) (G C) r).symm.trans
      (congrArg Subtype.val hr)⟩
  set G'' : D → F.Opens := fun C => G C ⊓ π ⁻¹ᵁ W₀ with hG''def
  have hpieceiso : ∀ C, IsIso (P ∣_ G'' C) := by
    intro C
    have hmemC : ∀ y : (∐ Rₒ : Scheme.{0}), P y ∈ (G C : Set F) →
        y ∈ Set.range (Sigma.ι Rₒ C) := by
      intro y hy
      obtain ⟨⟨C', r⟩, rfl⟩ := (sigmaMk Rₒ).surjective y
      rw [sigmaMk_mk] at hy ⊢
      by_cases hC : C' = C
      · subst hC
        exact ⟨r, rfl⟩
      · exfalso
        rw [hPι] at hy
        exact Set.disjoint_left.1 (hdisj C C' (Ne.symm hC)) ⟨r.1, rfl⟩ hy
    have hsum : Set.range (P ⁻¹ᵁ G'' C).ι ⊆ Set.range (Sigma.ι Rₒ C) := by
      rw [Scheme.Opens.range_ι]
      exact fun y hy => hmemC y hy.1
    set k := IsOpenImmersion.lift (Sigma.ι Rₒ C) (P ⁻¹ᵁ G'' C).ι hsum with hkdef
    have hk : k ≫ Sigma.ι Rₒ C = (P ⁻¹ᵁ G'' C).ι := IsOpenImmersion.lift_fac _ _ _
    have hsub2 : Set.range (k ≫ ((g C ≫ π) ⁻¹ᵁ W₀).ι) ⊆ Set.range (g C ⁻¹ᵁ G C).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h1 : Sigma.ι Rₒ C (k y) = (P ⁻¹ᵁ G'' C).ι y := by rw [← hk]; rfl
      have h2 : P (Sigma.ι Rₒ C (k y)) ∈ (G'' C : Set F) := by rw [h1]; exact y.2
      rw [hPι] at h2
      exact h2.1
    set m := IsOpenImmersion.lift (g C ⁻¹ᵁ G C).ι (k ≫ ((g C ≫ π) ⁻¹ᵁ W₀).ι) hsub2 with hmdef
    have hm : m ≫ (g C ⁻¹ᵁ G C).ι = k ≫ ((g C ≫ π) ⁻¹ᵁ W₀).ι := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion (m ≫ (g C ⁻¹ᵁ G C).ι) := by rw [hm]; infer_instance
    haveI : IsOpenImmersion m := IsOpenImmersion.of_comp m (g C ⁻¹ᵁ G C).ι
    haveI := hiso C
    have hcomp : (P ∣_ G'' C) ≫ (G'' C).ι = m ≫ (g C ∣_ G C) ≫ (G C).ι := by
      rw [morphismRestrict_ι, ← hk, Category.assoc, hιP, ← Category.assoc, ← hm,
        Category.assoc, morphismRestrict_ι]
    haveI : IsOpenImmersion ((P ∣_ G'' C) ≫ (G'' C).ι) := by rw [hcomp]; infer_instance
    haveI : IsOpenImmersion (P ∣_ G'' C) := IsOpenImmersion.of_comp _ (G'' C).ι
    haveI : Surjective (P ∣_ G'' C) := by
      refine ⟨fun ⟨z, hz⟩ => ?_⟩
      obtain ⟨r, hr⟩ := hGsurj C hz.1
      have hrW : r ∈ ((g C ≫ π) ⁻¹ᵁ W₀ : Set (R C)) := by
        change π (g C r) ∈ W₀
        rw [hr]
        exact hz.2
      let r' : Rₒ C := ⟨r, hrW⟩
      have hy : P (Sigma.ι Rₒ C r') ∈ (G'' C : Set F) := by
        rw [hPι]
        change g C r ∈ (G'' C : Set F)
        rw [hr]
        exact hz
      refine ⟨⟨Sigma.ι Rₒ C r', hy⟩, Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe P (G'' C) _).trans ((hPι C r').trans hr)
    exact (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩
  have hGiso : IsIso (P ∣_ G') := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (f := P ∣_ G') (fun C => G'.ι ⁻¹ᵁ G'' C) ?_ fun C => ?_
    · refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨z, hz1, hz2⟩ := z
      obtain ⟨C, hzC⟩ := (TopologicalSpace.Opens.mem_iSup).1 hz1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, ⟨hzC, hz2⟩⟩
    · have hle : G'' C ≤ G' := inf_le_inf_right _ (le_iSup G C)
      have heq : G'.ι ''ᵁ (G'.ι ⁻¹ᵁ G'' C) = G'' C := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.2 hle]
      have h2 := (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
        (morphismRestrictRestrict P G' (G'.ι ⁻¹ᵁ G'' C))
      refine h2.2 ?_
      change IsIso (P ∣_ G'.ι ''ᵁ (G'.ι ⁻¹ᵁ G'' C))
      rw [heq]
      exact hpieceiso C
  refine ⟨σ, fun w hw hwW => ?_⟩
  have hrange : Set.range w ⊆ Set.range W₀.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Subsingleton.elim u default, Scheme.Opens.range_ι]
    exact hwW
  set s := IsOpenImmersion.lift W₀.ι w hrange with hsdef
  have hsι : s ≫ W₀.ι = w := IsOpenImmersion.lift_fac _ _ _
  have hs : s ≫ σ.sS = 𝟙 _ := by
    change s ≫ W₀.ι ≫ sW = 𝟙 _
    rw [← Category.assoc, hsι, hw]
  have hres := Stratum.resolves_of_isIso_restrict σ (sW := sW) W₀.ι rfl π P hP G' hGiso s hs ?_ ?_
  · rwa [hsι] at hres
  · rw [hsι]
    refine (hd1 w hw hwW).trans (closure_mono fun z hz => ⟨⟨?_, ?_⟩, hz.2⟩)
    · obtain ⟨C, hC⟩ := Set.mem_iUnion.1 hz.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hC⟩
    · change π z ∈ W₀
      rw [show π z = w default from hz.2]
      exact hwW
  · intro y hy
    obtain ⟨⟨C, r⟩, rfl⟩ := (sigmaMk Rₒ).surjective y
    rw [sigmaMk_mk] at hy ⊢
    have hqι : ∀ r' : Rₒ C, W₀.ι (q (Sigma.ι Rₒ C r')) = π (g C r'.1) := by
      intro r'
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Sigma.ι_desc_assoc,
        morphismRestrict_ι]
      rfl
    have hrx : (g C ≫ π) r.1 = w default := by
      have h1 := hqι r
      rw [show q (Sigma.ι Rₒ C r) = s default from hy, ← Scheme.Hom.comp_apply, hsι] at h1
      exact h1.symm
    set A : Set (R C) := g C ⁻¹' (G C : Set F) ∩ (g C ≫ π) ⁻¹' {w default} with hA
    have hr : r.1 ∈ closure A := hd2 w hw hwW C hrx
    set j := ((g C ≫ π) ⁻¹ᵁ W₀).ι with hj
    have hr' : r ∈ closure (j ⁻¹' A) := by
      rw [← j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous]
      exact hr
    have hsub : Sigma.ι Rₒ C '' (j ⁻¹' A) ⊆
        P ⁻¹' (G' : Set F) ∩ σ.q ⁻¹' {s (default : Spec (.of ℂ))} := by
      rintro _ ⟨r', hr'A, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hPι]
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hr'A.1⟩
      · change π (P (Sigma.ι Rₒ C r')) ∈ W₀
        rw [hPι, ← Scheme.Hom.comp_apply, show (g C ≫ π) r'.1 = w default from hr'A.2]
        exact hwW
      · change q (Sigma.ι Rₒ C r') = s default
        apply W₀.ι.isOpenEmbedding.injective
        rw [hqι, show W₀.ι (s default) = w default by rw [← Scheme.Hom.comp_apply, hsι]]
        exact (Scheme.Hom.comp_apply (g C) π (j r')).symm.trans hr'A.2
    exact closure_mono hsub (image_closure_subset_closure_image (Sigma.ι Rₒ C).continuous ⟨r, hr', rfl⟩)

/-- A nonempty quasi-compact scheme locally of finite type over `ℂ` has natural-number
dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sW] [CompactSpace W] [Nonempty W] :
    ∃ n : ℕ, topologicalKrullDim W = n := by
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType ℂ sW
  have hbot : topologicalKrullDim W ≠ ⊥ := fun h =>
    (not_isEmpty_iff.mpr (inferInstance : Nonempty W))
      ((topologicalKrullDim_eq_bot_iff_isEmpty W).mp h)
  induction h : topologicalKrullDim W using WithBot.recBotCoe with
  | bot => exact absurd h hbot
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h htop
    | coe n => exact ⟨n, rfl⟩

/-- **Generic smoothness of a dominant family.** A dominant morphism `p : R ⟶ W` of integral
schemes of finite type over `ℂ` with `R` smooth is smooth over a nonempty open of `W`, where its
fibre components have dimension `dim R - dim W`. -/
private theorem exists_smooth_restrict_of_isDominant {R W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ))
    [IsIntegral R] [IsIntegral W] [LocallyOfFiniteType sW] [QuasiCompact sW] (p : R ⟶ W)
    [LocallyOfFiniteType p] [QuasiCompact p] (hsm : Smooth (p ≫ sW)) (hdom : IsDominant p) :
    ∃ U : W.Opens, (U : Set W).Nonempty ∧ Smooth (p ∣_ U) ∧
      ∀ t ∈ U, ∀ Z ∈ irreducibleComponents (p.fiber t),
        topologicalKrullDim Z + topologicalKrullDim W = topologicalKrullDim R := by
  letI : R.Over (Spec (.of ℂ)) := ⟨p ≫ sW⟩
  letI : W.Over (Spec (.of ℂ)) := ⟨sW⟩
  haveI : p.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : LocallyOfFiniteType (R ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (p ≫ sW) from inferInstance
  have : QuasiCompact (R ↘ Spec (.of ℂ)) := show QuasiCompact (p ≫ sW) from inferInstance
  have : LocallyOfFiniteType (W ↘ Spec (.of ℂ)) := show LocallyOfFiniteType sW from inferInstance
  have : QuasiCompact (W ↘ Spec (.of ℂ)) := show QuasiCompact sW from inferInstance
  have : Smooth (R ↘ Spec (.of ℂ)) := hsm
  obtain ⟨U, hU, -, hUsm, hfib⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) p
  exact ⟨U, hU.nonempty, hUsm, fun t ht => (hfib hdom t ht).2⟩

/-- **The generic stratum over an integral base.** Let `π : F ⟶ W` be a projective morphism from
a reduced scheme to an integral quasi-projective complex scheme, all of whose closed fibres have
pure dimension two. Over a nonempty open of `W` a single resolved stratum resolves the closed
fibres of `π`. -/
private theorem exists_stratum_of_isIntegral {W F : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ)) [IsIntegral W]
    [IsSeparated sW] (hWq : Stacks.HProjective.IsQuasiProjective sW) [IsReduced F] (π : F ⟶ W)
    (hπ : IsProjectiveMorphism π)
    (hfib : ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ →
      ∀ Γ ∈ irreducibleComponents (pullback π w : Scheme.{0}), topologicalKrullDim Γ = 2) :
    ∃ W' : Set W, IsOpen W' ∧ W'.Nonempty ∧ ∃ σ : Stratum, ∀ w : Spec (.of ℂ) ⟶ W,
      w ≫ sW = 𝟙 _ → w (default : Spec (.of ℂ)) ∈ W' → σ.Resolves π w := by
  classical
  have : QuasiCompact sW := hWq.quasiCompact
  have : LocallyOfFiniteType sW := hWq.locallyOfFiniteType
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : IsNoetherian W := ⟨⟩
  have : LocallyOfFinitePresentation sW :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hπp : IsProper π := isProper_of_isProjectiveMorphism π hπ
  set sF := π ≫ sW with hsF
  have : CompactSpace F := QuasiCompact.compactSpace_of_compactSpace sF
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian sF
  have : IsNoetherian F := ⟨⟩
  obtain ⟨dW, hdW⟩ := exists_topologicalKrullDim_eq_natCast sW
  have hfinc := NoetherianSpace.finite_irreducibleComponents (α := F)
  -- the dominant components and their resolutions
  set Dset : Set (Set F) := {C | C ∈ irreducibleComponents F ∧ π '' C = Set.univ} with hDset
  haveI : Finite Dset := (hfinc.subset fun C hC => hC.1).to_subtype
  choose R g G hRint hRsm hproj hrange hGne hGC hGdisj hiso hdimR using
    fun C : Dset => exists_resolution_of_mem_irreducibleComponents sF C.2.1
  -- the non-dominant components lie over a proper closed subset
  set Nset : Set (Set F) := {C | C ∈ irreducibleComponents F ∧ π '' C ≠ Set.univ} with hNset
  haveI : Finite Nset := (hfinc.subset fun C hC => hC.1).to_subtype
  set N : Set W := ⋃ C : Nset, π '' C.1 with hNdef
  have hNc : IsClosed N := isClosed_iUnion_of_finite fun C =>
    π.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ C.2.1)
  have hW₁ : (Nᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    obtain ⟨C, hC⟩ := exists_subset_of_isIrreducible_of_subset_iUnion
      (C := fun C : Nset => π '' C.1)
      (fun C => π.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ C.2.1))
      (IrreducibleSpace.isIrreducible_univ W) (by rw [← hNdef, h])
    exact C.2.2 (Set.eq_univ_of_univ_subset hC)
  -- basic facts on each resolved component
  have hRcl : ∀ C : Dset, IsClosed C.1 := fun C => isClosed_of_mem_irreducibleComponents _ C.2.1
  have hRirr : ∀ C : Dset, IsIrreducible C.1 := fun C => C.2.1.1
  have hpproj : ∀ C : Dset, IsProjective (g C ≫ π) := fun C => hproj C π hπ inferInstance inferInstance
  have hpprop : ∀ C : Dset, IsProper (g C ≫ π) := fun C => (hpproj C).isProper
  haveI := hRint
  have hpLFP : ∀ C : Dset, LocallyOfFinitePresentation (g C ≫ π) := fun C =>
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  -- generic smoothness of each resolved component
  have hgs : ∀ C : Dset, ∃ U : W.Opens, (U : Set W).Nonempty ∧ Smooth ((g C ≫ π) ∣_ U) ∧
      ∀ t ∈ U, ∀ Z ∈ irreducibleComponents ((g C ≫ π).fiber t),
        topologicalKrullDim Z + topologicalKrullDim W = topologicalKrullDim (R C) := by
    intro C
    refine exists_smooth_restrict_of_isDominant sW (g C ≫ π) ?_ ⟨?_⟩
    · rw [Category.assoc]
      exact hRsm C
    · rw [DenseRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange C, C.2.2]
      exact dense_univ
  choose Ugs hUgsne hUgssm hUgsdim using hgs
  -- generic fibre dimensions of the components
  have hgfC := fun C : Dset => exists_isOpen_forall_isMaxIrreducible sW π (hRcl C) (hRirr C)
  choose U' hU'o hU'ne hU' using hgfC
  -- the bad parts of the components, and their irreducible pieces
  have hEc : ∀ C : Dset, IsClosed (C.1 \ (G C : Set F)) := fun C =>
    (hRcl C).sdiff (G C).isOpen
  have hEdec := fun C : Dset => NoetherianSpace.exists_finite_set_isClosed_irreducible (hEc C)
  choose 𝓔 h𝓔f h𝓔c h𝓔i h𝓔U using hEdec
  have h𝓔lt : ∀ C : Dset, ∀ E' ∈ 𝓔 C, topologicalKrullDim E' < topologicalKrullDim C.1 := by
    intro C E' hE'
    have hE'E : E' ⊆ C.1 \ (G C : Set F) := (h𝓔U C).symm ▸ Set.subset_sUnion_of_mem hE'
    refine topologicalKrullDim_lt_of_ssubset sF (hRcl C) (hRirr C) (h𝓔c C E' hE')
      (fun x hx => (hE'E hx).1) fun heq => ?_
    obtain ⟨z, hz⟩ := hGne C
    exact (hE'E (heq ▸ hGC C hz)).2 hz
  have hgfE := fun (C : Dset) (E' : 𝓔 C) =>
    exists_isOpen_forall_isMaxIrreducible sW π (h𝓔c C E'.1 E'.2) (h𝓔i C E'.1 E'.2)
  choose UE hUEo hUEne hUE using hgfE
  have hBc : ∀ C : Dset, IsClosed ((g C) ⁻¹' (G C : Set F)ᶜ) := fun C =>
    (G C).isOpen.isClosed_compl.preimage (g C).continuous
  have hRnoeth : ∀ C : Dset, IsNoetherian (R C) := fun C => by
    have := LocallyOfFiniteType.isLocallyNoetherian ((g C ≫ π) ≫ sW)
    have : CompactSpace (R C) := QuasiCompact.compactSpace_of_compactSpace ((g C ≫ π) ≫ sW)
    exact ⟨⟩
  have hBdec := fun C : Dset => by
    haveI := hRnoeth C
    exact NoetherianSpace.exists_finite_set_isClosed_irreducible (hBc C)
  choose 𝓑 h𝓑f h𝓑c h𝓑i h𝓑U using hBdec
  have h𝓑lt : ∀ C : Dset, ∀ B' ∈ 𝓑 C, topologicalKrullDim B' < topologicalKrullDim (R C) := by
    intro C B' hB'
    have hB'B : B' ⊆ (g C) ⁻¹' (G C : Set F)ᶜ := (h𝓑U C).symm ▸ Set.subset_sUnion_of_mem hB'
    have hlt := topologicalKrullDim_lt_of_ssubset ((g C ≫ π) ≫ sW) isClosed_univ
      (IrreducibleSpace.isIrreducible_univ (R C)) (h𝓑c C B' hB') (Set.subset_univ _)
      (fun heq => by
        obtain ⟨z, hz⟩ := hGne C
        obtain ⟨r, hr⟩ : z ∈ Set.range (g C) := (hrange C).symm ▸ hGC C hz
        exact hB'B (heq ▸ Set.mem_univ r) (hr ▸ hz))
    rwa [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ (R C)).isHomeomorph] at hlt
  have hgfB := fun (C : Dset) (B' : 𝓑 C) =>
    exists_isOpen_forall_isMaxIrreducible sW (g C ≫ π) (h𝓑c C B'.1 B'.2) (h𝓑i C B'.1 B'.2)
  choose UB hUBo hUBne hUB using hgfB
  haveI : ∀ C, Finite (𝓔 C) := fun C => (h𝓔f C).to_subtype
  haveI : ∀ C, Finite (𝓑 C) := fun C => (h𝓑f C).to_subtype
  -- the good open of the base
  have hSmne : (sW.smoothLocus : Set W).Nonempty :=
    ⟨genericPoint W, sW.genericPoint_mem_smoothLocus_of_perfectField⟩
  set V : Dset → Set W := fun C => (Ugs C : Set W) ∩ U' C ∩ (⋂ E' : 𝓔 C, UE C E') ∩
    (⋂ B' : 𝓑 C, UB C B') with hVdef
  have hVo : ∀ C, IsOpen (V C) := fun C =>
    (((Ugs C).isOpen.inter (hU'o C)).inter (isOpen_iInter_of_finite fun E' => hUEo C E')).inter
      (isOpen_iInter_of_finite fun B' => hUBo C B')
  have hVne : ∀ C, (V C).Nonempty := fun C => by
    have h1 := nonempty_iInter_of_isOpen (fun E' => hUEo C E') (fun E' => hUEne C E')
    have h2 := nonempty_iInter_of_isOpen (fun B' => hUBo C B') (fun B' => hUBne C B')
    have n1 := nonempty_preirreducible_inter (Ugs C).isOpen (hU'o C) (hUgsne C) (hU'ne C)
    have n2 := nonempty_preirreducible_inter ((Ugs C).isOpen.inter (hU'o C))
      (isOpen_iInter_of_finite fun E' => hUEo C E') n1 h1
    exact nonempty_preirreducible_inter (((Ugs C).isOpen.inter (hU'o C)).inter
      (isOpen_iInter_of_finite fun E' => hUEo C E')) (isOpen_iInter_of_finite fun B' => hUBo C B')
      n2 h2
  set W₀set : Set W := Nᶜ ∩ (sW.smoothLocus : Set W) ∩ ⋂ C, V C with hW₀def
  have hW₀o : IsOpen W₀set := (hNc.isOpen_compl.inter sW.smoothLocus.isOpen).inter
    (isOpen_iInter_of_finite hVo)
  have hW₀ne : W₀set.Nonempty := by
    have n1 := nonempty_preirreducible_inter hNc.isOpen_compl sW.smoothLocus.isOpen hW₁ hSmne
    exact nonempty_preirreducible_inter (hNc.isOpen_compl.inter sW.smoothLocus.isOpen)
      (isOpen_iInter_of_finite hVo) n1 (nonempty_iInter_of_isOpen hVo hVne)
  set W₀ : W.Opens := ⟨W₀set, hW₀o⟩ with hW₀
  have hW₀sm : Smooth (W₀.ι ≫ sW) := by
    refine Scheme.Hom.smoothLocus_eq_top_iff.mp (top_unique fun x _ => ?_)
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact x.2.1.2
  obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension_of_irreducibleSpace sW W₀ hW₀ne
  have hW₀V : ∀ C, ∀ x ∈ W₀set, x ∈ V C := fun C x hx => Set.mem_iInter.1 hx.2 C
  -- the relative dimension of the components
  set δ : Dset → WithBot ℕ∞ := fun C =>
    if h : ∃ v : WithBot ℕ∞, v + dW = topologicalKrullDim C.1 then h.choose else ⊥ with hδdef
  have hδ : ∀ C, ∀ x ∈ U' C, ∀ Λ, IsMaxIrreducible (C.1 ∩ π ⁻¹' {x}) Λ →
      topologicalKrullDim Λ = δ C ∧ δ C + dW = topologicalKrullDim C.1 := by
    intro C x hx Λ hΛ
    have h1 := hU' C x hx Λ hΛ
    rw [hdW] at h1
    have hex : ∃ v : WithBot ℕ∞, v + dW = topologicalKrullDim C.1 := ⟨_, h1⟩
    have hδC : δ C = hex.choose := by simp only [hδdef, dif_pos hex]
    rw [hδC]
    exact ⟨ENat.WithBot.add_natCast_cancel.mp (h1.trans hex.choose_spec.symm), hex.choose_spec⟩
  have hΦmax : ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ → ∀ Γ',
      IsMaxIrreducible (π ⁻¹' {w (default : Spec (.of ℂ))}) Γ' → topologicalKrullDim Γ' = 2 := by
    intro w hw Γ' hΓ'
    obtain ⟨hemb, hrng⟩ := isEmbedding_and_range_pullback_fst (sB := sW) π w hw
    exact topologicalKrullDim_of_isMaxIrreducible
      (hemb.toHomeomorph.trans (Homeomorph.setCongr hrng)) (· = 2) (hfib w hw) hΓ'
  set O : Dset → Set F := fun C => (⋃₀ (irreducibleComponents F \ {C.1}))ᶜ with hOdef
  have hOo : ∀ C, IsOpen (O C) := fun C => by
    rw [hOdef, isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hfinc.diff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have hcomp : ∀ z : F, ∃ C₀ ∈ irreducibleComponents F, z ∈ C₀ := fun z => by
    obtain ⟨C₀, hC₀, hz⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (isIrreducible_singleton (x := z))
    exact ⟨C₀, hC₀, hz rfl⟩
  have htop : ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ → w (default : Spec (.of ℂ)) ∈ W₀set →
      (∀ C : Dset, (C.1 ∩ π ⁻¹' {w default}).Nonempty → δ C = 2) ∧
        π ⁻¹' {w default} ⊆
          closure (⋃ C : Dset, (C.1 ∩ π ⁻¹' {w default}) \ (C.1 \ (G C : Set F))) := by
    intro w hw hwW
    have hxN : w default ∉ N := hwW.1.1
    refine eq_two_and_subset_closure_iUnion (C := fun C : Dset => C.1)
      (E := fun C => C.1 \ (G C : Set F)) (O := O) (δ := δ) hRcl hEc hOo ?_ ?_ ?_
      (fun Γ hΓ hi => exists_isMaxIrreducible hΓ hi) (hΦmax w hw)
      (fun C Γ hΓ hi => exists_isMaxIrreducible hΓ hi)
      (fun C Λ hΛ => (hδ C _ (hW₀V C _ hwW).1.1.2 Λ hΛ).1) ?_
    · intro z hz
      obtain ⟨C₀, hC₀, hzC₀⟩ := hcomp z
      by_cases hdom : π '' C₀ = Set.univ
      · exact Set.mem_iUnion.2 ⟨⟨C₀, hC₀, hdom⟩, hzC₀⟩
      · exfalso
        exact hxN (Set.mem_iUnion.2 ⟨⟨C₀, hC₀, hdom⟩, z, hzC₀, hz⟩)
    · intro C z hz
      obtain ⟨C₀, hC₀, hzC₀⟩ := hcomp z
      by_contra hzC
      exact hz.1 ⟨C₀, ⟨hC₀, fun h => hzC (h ▸ hzC₀)⟩, hzC₀⟩
    · intro C z hz hzO
      have hzG : z ∈ (G C : Set F) := by
        by_contra h
        exact hz.2 ⟨hz.1.1, h⟩
      obtain ⟨C₀, ⟨hC₀, hne⟩, hzC₀⟩ := hzO
      exact Set.disjoint_left.1 (hGdisj C C₀ hC₀ hne) hzG hzC₀
    · intro C Γ hΓ hi
      have hΓE : Γ ⊆ ⋃ E' : 𝓔 C, E'.1 := by
        rw [← Set.sUnion_eq_iUnion, ← h𝓔U C]
        exact fun z hz => (hΓ hz).2
      obtain ⟨E', hE'⟩ := exists_subset_of_isIrreducible_of_subset_iUnion
        (fun E' : 𝓔 C => h𝓔c C E'.1 E'.2) hi hΓE
      obtain ⟨Λ, hΛ, hΓΛ⟩ := exists_isMaxIrreducible (A := E'.1 ∩ π ⁻¹' {w default})
        (fun z hz => ⟨hE' hz, (hΓ hz).1.2⟩) hi
      obtain ⟨ΛC, hΛC, hΓΛC⟩ := exists_isMaxIrreducible (A := C.1 ∩ π ⁻¹' {w default})
        (fun z hz => (hΓ hz).1) hi
      have hxV := hW₀V C _ hwW
      have h1 := hUE C E' _ (Set.mem_iInter.1 hxV.1.2 E') Λ hΛ
      rw [hdW] at h1
      refine (topologicalKrullDim_mono hΓΛ).trans_lt
        (lt_of_add_lt_add_right (a := (dW : WithBot ℕ∞)) ?_)
      rw [h1, (hδ C _ hxV.1.1.2 ΛC hΛC).2]
      exact h𝓔lt C E'.1 E'.2
  -- the dimension of every component is `2 + dim W`
  obtain ⟨w₀, hw₀, hw₀W⟩ := MMP.Fourfold.exists_complexPoint_mem sW (V := W₀) hW₀ne
  have hδ2 : ∀ C : Dset, δ C = 2 ∧ topologicalKrullDim C.1 = 2 + dW := by
    intro C
    obtain ⟨z, hzC, hz⟩ : w₀ default ∈ π '' C.1 := C.2.2 ▸ Set.mem_univ _
    have h2 := (htop w₀ hw₀ hw₀W).1 C ⟨z, hzC, hz⟩
    obtain ⟨Λ, hΛ, -⟩ := exists_isMaxIrreducible (A := C.1 ∩ π ⁻¹' {w₀ default})
      (Set.singleton_subset_iff.2 ⟨hzC, hz⟩) isIrreducible_singleton
    have h3 := (hδ C _ (hW₀V C _ hw₀W).1.1.2 Λ hΛ).2
    rw [h2] at h3
    exact ⟨h2, h3.symm⟩
  -- the families over `W₀` are smooth of relative dimension two
  have hfibdim : ∀ C : Dset, ∀ t ∈ Ugs C, ∀ Z ∈ irreducibleComponents ((g C ≫ π).fiber t),
      topologicalKrullDim Z = 2 := by
    intro C t ht Z hZ
    have h1 := hUgsdim C t ht Z hZ
    rw [hdimR C, (hδ2 C).2, hdW] at h1
    exact ENat.WithBot.add_natCast_cancel.mp h1
  have hsm' : ∀ C : Dset, SmoothOfRelativeDimension 2 ((g C ≫ π) ∣_ W₀) := fun C =>
    smoothOfRelativeDimension_restrict (g C ≫ π) (Ugs C) (hUgssm C) (hfibdim C) W₀
      fun x hx => (hW₀V C x hx).1.1.1
  have hdisj : ∀ C C' : Dset, C ≠ C' → Disjoint (Set.range (g C')) (G C : Set F) := by
    intro C C' hne
    rw [hrange C']
    exact (hGdisj C C'.1 C'.2.1 fun h => hne (Subtype.ext h.symm)).symm
  have hd1 : ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ → w (default : Spec (.of ℂ)) ∈ W₀ →
      π ⁻¹' {w default} ⊆ closure ((⋃ C, (G C : Set F)) ∩ π ⁻¹' {w default}) := by
    intro w hw hwW
    refine ((htop w hw hwW).2.trans (closure_mono ?_))
    intro z hz
    obtain ⟨C, hC⟩ := Set.mem_iUnion.1 hz
    have hzG : z ∈ (G C : Set F) := by
      by_contra h
      exact hC.2 ⟨hC.1.1, h⟩
    exact ⟨Set.mem_iUnion.2 ⟨C, hzG⟩, hC.1.2⟩
  have hd2 : ∀ w : Spec (.of ℂ) ⟶ W, w ≫ sW = 𝟙 _ → w (default : Spec (.of ℂ)) ∈ W₀ → ∀ C,
      (g C ≫ π) ⁻¹' {w default} ⊆
        closure (g C ⁻¹' (G C : Set F) ∩ (g C ≫ π) ⁻¹' {w default}) := by
    intro w hw hwW C
    have hxV := hW₀V C _ hwW
    have hA : ∀ y ∈ (g C ≫ π) ⁻¹' {w default}, ∃ Λ,
        IsMaxIrreducible ((g C ≫ π) ⁻¹' {w default}) Λ ∧ y ∈ Λ ∧ topologicalKrullDim Λ = 2 := by
      intro y hy
      obtain ⟨Λ, hΛ, hyΛ⟩ := exists_isMaxIrreducible (Set.singleton_subset_iff.2 hy)
        isIrreducible_singleton
      refine ⟨Λ, hΛ, hyΛ rfl, ?_⟩
      exact topologicalKrullDim_of_isMaxIrreducible ((g C ≫ π).fiberHomeo (w default)) (· = 2)
        (hfibdim C _ hxV.1.1.1) hΛ
    have hE : ∀ Γ ⊆ (g C ≫ π) ⁻¹' {w default} ∩ (g C) ⁻¹' (G C : Set F)ᶜ, IsIrreducible Γ →
        topologicalKrullDim Γ < 2 := by
      intro Γ hΓ hi
      have hΓB : Γ ⊆ ⋃ B' : 𝓑 C, B'.1 := by
        rw [← Set.sUnion_eq_iUnion, ← h𝓑U C]
        exact fun z hz => (hΓ hz).2
      haveI := hRnoeth C
      obtain ⟨B', hB'⟩ := exists_subset_of_isIrreducible_of_subset_iUnion
        (fun B' : 𝓑 C => h𝓑c C B'.1 B'.2) hi hΓB
      obtain ⟨Λ, hΛ, hΓΛ⟩ := exists_isMaxIrreducible (A := B'.1 ∩ (g C ≫ π) ⁻¹' {w default})
        (fun z hz => ⟨hB' hz, (hΓ hz).1⟩) hi
      have h1 := hUB C B' _ (Set.mem_iInter.1 hxV.2 B') Λ hΛ
      have h3 := h𝓑lt C B'.1 B'.2
      rw [← h1, hdW, hdimR C, (hδ2 C).2] at h3
      exact (topologicalKrullDim_mono hΓΛ).trans_lt (lt_of_add_lt_add_right h3)
    refine (subset_closure_diff_of_lt hA (hBc C) hE).trans (closure_mono ?_)
    intro z hz
    exact ⟨not_not.1 hz.2, hz.1⟩
  obtain ⟨σ, hσ⟩ := exists_stratum_of_family sW hWq π W₀ hd R g hsm' hpproj G hiso hdisj hd1 hd2
  exact ⟨W₀set, hW₀o, hW₀ne, σ, hσ⟩

/-- **The generic stratum.** Over a nonempty relatively open part of every irreducible closed
subset `Z₁` of `T`, a single resolved stratum resolves the closed fibres of `h`. -/
private theorem exists_stratum_of_isIrreducible {𝒵 T : Scheme.{0}} (h : 𝒵 ⟶ T) (sT : T ⟶ Spec (.of ℂ))
    [IsReduced T]
    (hTq : Stacks.HProjective.IsQuasiProjective sT) (hh : IsProjectiveMorphism h)
    (hfib : ∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ →
      IsReduced (pullback h t) ∧
        ∀ C ∈ irreducibleComponents (pullback h t : Scheme.{0}),
          topologicalKrullDim C = 2)
    (Z₁ : Set T) (hZ₁c : IsClosed Z₁) (hZ₁ : IsIrreducible Z₁) :
    ∃ V : Set T, IsOpen V ∧ (V ∩ Z₁).Nonempty ∧ ∃ σ : Stratum, ∀ x ∈ V ∩ Z₁,
      ∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ → t (default : Spec (.of ℂ)) = x →
        σ.Resolves h t := by
  classical
  have : IsSeparated sT := isSeparated_of_isQuasiProjective sT hTq
  -- the reduced closed subscheme on `Z₁`
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨Z₁, hZ₁c⟩ : Closeds T) with hI
  set j := I.subschemeι with hj
  have hjr : Set.range j = Z₁ := range_subschemeι_vanishingIdeal _
  haveI : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal (Z := ⟨Z₁, hZ₁c⟩) hZ₁
  set sW := j ≫ sT with hsW
  have hWq : Stacks.HProjective.IsQuasiProjective sW :=
    IsQuasiProjective.comp j sT (isQuasiProjective_of_isImmersion j) hTq
  -- the reduction of `𝒵 ×_T W`
  set π₀ := pullback.snd h j with hπ₀
  set J := Scheme.IdealSheafData.vanishingIdeal (X := pullback h j) ⊤ with hJ
  set ιF := J.subschemeι with hιF
  haveI : Surjective ιF := by
    refine ⟨fun y => ?_⟩
    have : y ∈ Set.range ιF := by
      rw [hιF, J.range_subschemeι, hJ, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      trivial
    exact this
  set π := ιF ≫ π₀ with hπdef
  have hπ : IsProjectiveMorphism π := by
    obtain ⟨n, i, hi, hif⟩ := hh.baseChange j
    haveI := hi
    exact ⟨n, ιF ≫ i, inferInstance, by rw [Category.assoc, hif]⟩
  -- the closed fibres of the reduction are those of `h`
  have hiso : ∀ w : Spec (.of ℂ) ⟶ I.subscheme, w ≫ sW = 𝟙 _ →
      ∃ e : pullback π w ≅ pullback h (w ≫ j),
        e.hom ≫ pullback.snd h (w ≫ j) = pullback.snd π w := by
    intro w hw
    have ht : (w ≫ j) ≫ sT = 𝟙 _ := by rwa [Category.assoc]
    set m : pullback π w ⟶ pullback π₀ w :=
      (pullbackRightPullbackFstIso π₀ w ιF).inv ≫ pullback.snd ιF (pullback.fst π₀ w) with hm
    haveI : IsReduced (pullback h (w ≫ j)) := (hfib _ ht).1
    haveI : IsReduced (pullback π₀ w) :=
      isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso h j w).hom
    haveI : IsClosedImmersion m := by rw [hm]; infer_instance
    haveI : Surjective m := by rw [hm]; infer_instance
    haveI : IsIso m := isIso_of_isClosedImmersion_of_surjective m
    refine ⟨asIso m ≪≫ pullbackLeftPullbackSndIso h j w, ?_⟩
    rw [Iso.trans_hom, asIso_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, hm,
      Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
  have hfibπ : ∀ w : Spec (.of ℂ) ⟶ I.subscheme, w ≫ sW = 𝟙 _ →
      ∀ Γ ∈ irreducibleComponents (pullback π w : Scheme.{0}), topologicalKrullDim Γ = 2 := by
    intro w hw
    obtain ⟨e, -⟩ := hiso w hw
    exact forall_irreducibleComponents_of_homeomorph (Scheme.homeoOfIso e) (· = 2)
      (hfib _ (by rwa [Category.assoc])).2
  obtain ⟨W', hW'o, hW'ne, σ, hσ⟩ := exists_stratum_of_isIntegral sW hWq π hπ hfibπ
  obtain ⟨V, hVo, hVW'⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.1 hW'o
  refine ⟨V, hVo, ?_, σ, fun x hx t ht htx => ?_⟩
  · obtain ⟨y, hy⟩ := hW'ne
    refine ⟨j y, ?_, hjr ▸ ⟨y, rfl⟩⟩
    rwa [← hVW'] at hy
  · obtain ⟨w, hw⟩ := exists_comp_eq_of_isClosedImmersion j t (by rw [hjr, htx]; exact hx.2)
    subst hw
    have hws : w ≫ sW = 𝟙 _ := by rwa [hsW, ← Category.assoc]
    have hwW' : w (default : Spec (.of ℂ)) ∈ W' := by
      rw [← hVW']
      change j (w default) ∈ V
      rw [← Scheme.Hom.comp_apply, htx]
      exact hx.1
    obtain ⟨e, he⟩ := hiso w hws
    exact Stratum.Resolves.of_iso (hσ w hws hwW') e he

/-- **Stratification.** Finitely many resolved strata resolve every closed fibre of `h`. -/
private theorem exists_strata {𝒵 T : Scheme.{0}} (h : 𝒵 ⟶ T) (sT : T ⟶ Spec (.of ℂ))
    [IsReduced T]
    (hTq : Stacks.HProjective.IsQuasiProjective sT) (hh : IsProjectiveMorphism h)
    (hfib : ∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ →
      IsReduced (pullback h t) ∧
        ∀ C ∈ irreducibleComponents (pullback h t : Scheme.{0}),
          topologicalKrullDim C = 2) :
    ∃ L : List Stratum, ∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ →
      ∃ σ ∈ L, σ.Resolves h t := by
  have : QuasiCompact sT := hTq.quasiCompact
  have : LocallyOfFiniteType sT := hTq.locallyOfFiniteType
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : IsNoetherian T := ⟨⟩
  obtain ⟨L, hL⟩ := exists_list_forall_of_isIrreducible
    (fun (σ : Stratum) (x : T) => ∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ →
      t (default : Spec (.of ℂ)) = x → σ.Resolves h t)
    (exists_stratum_of_isIrreducible h sT hTq hh hfib) ⊤
  exact ⟨L, fun t ht => by
    obtain ⟨σ, hσ, hσt⟩ := hL (t (default : Spec (.of ℂ))) trivial
    exact ⟨σ, hσ, hσt t ht rfl⟩⟩

end Stratification

end MMP.Proof_lem_fourfold_surface_family_resolution_betti_bound

namespace MMP.Fourfold

open MMP.Proof_lem_fourfold_surface_family_resolution_betti_bound

/-- **Bounded second Betti numbers of resolutions in a family of surfaces.** Let `h : 𝒵 ⟶ T` be
a projective morphism of schemes over `ℂ`, with `T` reduced and quasi-projective over `ℂ`, and
suppose that for every `ℂ`-point `t` of `T` the fibre `𝒵_t` is reduced and each of its
irreducible components has dimension `2`. Then there is `b : ℕ` such that every fibre `𝒵_t`
admits a smooth projective surface `Y` over `ℂ` with a morphism `p : Y ⟶ 𝒵_t` over `ℂ` which is
an isomorphism over a dense open `U` of `𝒵_t` with `p⁻¹(U)` dense in `Y`, and with
`dim_ℚ H²(Y^an; ℚ) ≤ b`. -/
@[mmp "lem_fourfold_surface_family_resolution_betti_bound"]
public theorem exists_forall_finrank_singularCohomology_two_le_of_resolution
    {𝒵 T : Scheme.{0}} (h : 𝒵 ⟶ T) (sZ : 𝒵 ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ))
    (hsZ : h ≫ sT = sZ) [IsReduced T] (hTq : IsQuasiProjective sT)
    (hh : IsProjectiveMorphism h)
    (hfib : ∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ →
      IsReduced (pullback h t) ∧
        ∀ C ∈ irreducibleComponents (pullback h t : Scheme.{0}),
          topologicalKrullDim C = 2) :
    ∃ b : ℕ, ∀ t : Spec (.of ℂ) ⟶ T, t ≫ sT = 𝟙 _ →
      ∃ (Y : Scheme.{0}) (p : Y ⟶ pullback h t),
        IsProjectiveMorphism (p ≫ pullback.snd h t) ∧
        SmoothOfRelativeDimension 2 (p ≫ pullback.snd h t) ∧
        (∃ U : (pullback h t).Opens, Dense (U : Set (pullback h t : Scheme.{0})) ∧
          Dense ((p ⁻¹ᵁ U : Y.Opens) : Set Y) ∧ IsIso (p ∣_ U)) ∧
        Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
          (analyticSpace (p ≫ pullback.snd h t)) ∅ 2) ≤ b := by
  obtain ⟨L, hL⟩ := exists_strata h sT hTq hh hfib
  have hb : ∀ σ : Stratum, ∃ b : ℕ, ∀ s : Spec (.of ℂ) ⟶ σ.S, s ≫ σ.sS = 𝟙 _ →
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
        (analyticSpace (pullback.snd σ.q s)) ∅ 2) ≤ b := fun σ =>
    have := σ.smoothRel
    have := σ.separated
    have := σ.smoothTwo
    exists_betti_bound (d := σ.relDim) σ.sS σ.quasiProjective σ.q σ.projective
  choose B hB using hb
  refine ⟨(L.map B).sum, fun t ht => ?_⟩
  obtain ⟨σ, hσL, s, hss, p, hp, U, hU, hpU, hiso⟩ := hL t ht
  refine ⟨_, p, ?_, ?_, ⟨U, hU, hpU, hiso⟩, ?_⟩
  · rw [hp]
    exact σ.projective.baseChange s
  · rw [hp]
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 2)).of_isPullback
      (IsPullback.of_hasPullback σ.q s) σ.smoothTwo
  · rw [hp]
    exact (hB σ s hss).trans (List.le_sum_of_mem (List.mem_map_of_mem hσL))

end MMP.Fourfold
