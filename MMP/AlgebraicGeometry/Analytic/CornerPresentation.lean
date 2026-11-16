module
public import MMP.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import MMP.Geometry.Manifold.Corners.EuclideanQuadrant

/-!
# A compact corner presentation of a projective complex variety

Let `X` be a reduced projective scheme over `ℂ` and `S ⊆ X` a closed subset containing the
singular locus of `X` and no irreducible component of `X`. Resolving `X` and principalizing the
ideal of `S` gives a disjoint union of smooth projective varieties `Y → X`, an isomorphism
outside `S`, whose reduced inverse image `E` of `S` is a simple normal crossings divisor. Passing
to polar coordinates `z_j = r_j e^{iθ_j}` normal to the components of `E` (the real oriented
blow-up of `Y` along `E`) produces a finite disjoint union `M` of compact smooth manifolds with
corners whose boundary hypersurfaces are embedded, with interior `Y ∖ E ≅ X ∖ S` and boundary the
inverse image of `E`. The resulting map `M → X^an` exhibits `X^an` as the pushout
`M ∪_{∂M} S^an` of the boundary inclusion `∂M ⟶ M` along a continuous map `∂M → S^an`.

The proof resolves every component `Z` of `X` and principalizes the ideal of `S ∩ Z`. Holomorphic
coordinates in which the components of `E` are coordinate hyperplanes are passed to polar
coordinates. The real oriented blow-up `M → Y` is realized as the closure of the graph of
`y ↦ (ψ_a(y) z_{a,j}(y) / |z_{a,j}(y)|)_{a,j}` over `Y ∖ E`, for a finite atlas `(a)` with
cut-offs `ψ_a`. The map from the pushout `M ∪_{∂M} S` to `X` is a continuous bijection from a
quotient of a compact space to a Hausdorff space, hence a homeomorphism.

## Main results

* `MMP.Analytic.exists_isPushout_manifoldWithCorners_boundary`: the corner presentation
  `X^an ≅ M ∪_{∂M} S^an`, with `M ∖ ∂M ≅ X^an ∖ S^an`.

## Implementation notes

* `M` is `Σ i, M i` over a finite index type, `M i` a compact Hausdorff `C^∞` manifold modelled
  on the quadrant `[0, ∞)^(n i)`; the dimensions `n i` may differ. Its boundary `∂M` is the set
  of points of positive depth, corners included.
* The boundary hypersurfaces of `M i` are *embedded*: there is a finite family of closed subsets
  `F j` (the faces) such that every point `x` has a chart of the atlas in which the faces through
  `x` correspond bijectively to the coordinates vanishing at `x`, each face being cut out on the
  chart domain by its coordinate, and the faces not through `x` missing the chart domain.
* `X^an` is `MMP.Analytic.ComplexPoints sX` with its analytic topology, and `S^an` is the inverse
  image of `S` under `MMP.Analytic.ComplexPoints.toScheme`. The isomorphism
  `X^an ≅ M ∪_{∂M} S^an` is stated as a pushout square in `TopCat` whose other two sides are a
  continuous map `κ : M → X^an` and the inclusion `S^an ⟶ X^an`; the identification
  `M ∖ ∂M ≅ X^an ∖ S^an` is the restriction of `κ`.
* Changes of polar coordinates are smooth because a holomorphic coordinate change `z'` which
  vanishes exactly on the hyperplane `z_k = 0` is `z_k` times a nowhere vanishing holomorphic
  unit (Hadamard division, with the non-vanishing on the hyperplane read off the derivative).
* An angle is parametrised near `ω₀` by its height `t - 1` over `ω₀`: the circle point
  `ω₀ (√(1 - (t - 1)²) + i (t - 1))`. All coordinates are shifted to be positive away from the
  faces, as the model is the quadrant `[0, ∞)^{2d}`.
* The auxiliary lemmas of the proof live in the namespace
  `MMP.Proof_lem_mmp_projective_corner_presentation`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace Filter Set
  MMP.Analytic
open scoped Manifold ContDiff

namespace MMP.Proof_lem_mmp_projective_corner_presentation

section Gluing

variable {M X : Type} [TopologicalSpace M] [TopologicalSpace X]
  {B : Set M} {S : Set X} (κ : C(M, X)) (hpre : κ ⁻¹' S = B)

private def restrictBoundary : C(B, S) :=
  ⟨fun p ↦ ⟨κ p, by have h : (p : M) ∈ κ ⁻¹' S := hpre ▸ p.2; exact h⟩, by fun_prop⟩

private theorem isPushout_types (hinj : Set.InjOn κ Bᶜ)
    (hsurj : Sᶜ ⊆ Set.range κ) :
    IsPushout ((forget TopCat).map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of B ⟶ TopCat.of M))
      ((forget TopCat).map (TopCat.ofHom (restrictBoundary κ hpre)))
      ((forget TopCat).map (TopCat.ofHom κ))
      ((forget TopCat).map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of S ⟶ TopCat.of X)) := by
  refine IsPushout.flip ?_
  have : Mono ((forget TopCat).map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of S ⟶ TopCat.of X)) :=
    (mono_iff_injective _).2 Subtype.val_injective
  refine Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_
  · rw [Types.isPullback_iff]
    refine ⟨rfl, ?_, ?_⟩
    · rintro x y ⟨-, h⟩; exact Subtype.ext h
    · intro s m h
      have hm : m ∈ B := by
        rw [← hpre]; change κ m ∈ S
        have : (s : X) = κ m := h
        rw [← this]; exact s.2
      exact ⟨⟨m, hm⟩, Subtype.ext h.symm, rfl⟩
  · ext x
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    by_cases hx : x ∈ S
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · obtain ⟨m, rfl⟩ := hsurj hx
      exact Or.inr ⟨m, rfl⟩
  · intro x y hx hy hxy
    exact hinj (fun h ↦ hx ⟨⟨x, h⟩, rfl⟩) (fun h ↦ hy ⟨⟨y, h⟩, rfl⟩) hxy

private theorem isPushout_restrictBoundary [CompactSpace M] [T2Space X] (hS : IsClosed S)
    (hinj : Set.InjOn κ Bᶜ) (hsurj : Sᶜ ⊆ Set.range κ) :
    IsPushout (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of B ⟶ TopCat.of M)
      (TopCat.ofHom (restrictBoundary κ hpre)) (TopCat.ofHom κ)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of S ⟶ TopCat.of X) := by
  have hT := isPushout_types κ hpre hinj hsurj
  have w : (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of B ⟶ TopCat.of M) ≫
      TopCat.ofHom κ = TopCat.ofHom (restrictBoundary κ hpre) ≫
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of S ⟶ TopCat.of X) := rfl
  refine ⟨⟨w⟩, ⟨?_⟩⟩
  have hc := (isColimitMapCoconePushoutCoconeEquiv (forget TopCat) w).symm hT.isColimit
  refine Classical.choice (((TopCat.nonempty_isColimit_iff_eq_coinduced _ hc)).2 ?_)
  refine le_antisymm ?_ (iSup_le fun j ↦ ((PushoutCocone.mk _ _ w).ι.app j).hom.continuous.coinduced_le)
  intro U hU
  rw [isOpen_iSup_iff] at hU
  have hl : IsOpen (κ ⁻¹' U) := isOpen_coinduced.1 (hU WalkingSpan.left)
  have hr : IsOpen ((Subtype.val : S → X) ⁻¹' U) := isOpen_coinduced.1 (hU WalkingSpan.right)
  rw [← isClosed_compl_iff]
  have hC : Uᶜ = κ '' (κ ⁻¹' Uᶜ) ∪ (Uᶜ ∩ S) := by
    ext x
    constructor
    · intro hx
      by_cases hxS : x ∈ S
      · exact Or.inr ⟨hx, hxS⟩
      · obtain ⟨m, rfl⟩ := hsurj hxS
        exact Or.inl ⟨m, hx, rfl⟩
    · rintro (⟨m, hm, rfl⟩ | ⟨hx, -⟩) <;> assumption
  rw [hC]
  refine IsClosed.union ((hl.isClosed_compl.isCompact.image κ.continuous).isClosed) ?_
  have : IsClosed ((Subtype.val : S → X) ⁻¹' Uᶜ) := hr.isClosed_compl
  rw [hS.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed, Subtype.image_preimage_coe] at this
  rwa [Set.inter_comm]

include hpre in
private theorem isOpenEmbedding_restrict [CompactSpace M] [T2Space X] (hS : IsClosed S)
    (hinj : Set.InjOn κ Bᶜ) (hsurj : Sᶜ ⊆ Set.range κ) :
    IsOpenEmbedding (fun p : (Bᶜ : Set M) ↦ κ p) := by
  refine .of_continuous_injective_isOpenMap (by fun_prop)
    (fun p q h ↦ Subtype.ext (hinj p.2 q.2 h)) ?_
  intro U hU
  obtain ⟨V, hV, rfl⟩ := hU
  have hBc : ∀ m, m ∉ B ↔ κ m ∉ S := fun m ↦ by rw [← hpre]; rfl
  have : (fun p : (Bᶜ : Set M) ↦ κ p) '' (Subtype.val ⁻¹' V) =
      Sᶜ ∩ (κ '' (V ∩ Bᶜ)ᶜ)ᶜ := by
    ext y
    constructor
    · rintro ⟨⟨m, hmB⟩, hmV, rfl⟩
      refine ⟨(hBc m).1 hmB, ?_⟩
      rintro ⟨m', hm', hm'B⟩
      have hm'B' : m' ∉ B := (hBc m').2 (hm'B ▸ (hBc m).1 hmB)
      obtain rfl := hinj hm'B' hmB hm'B
      exact hm' ⟨hmV, hmB⟩
    · rintro ⟨hyS, hy⟩
      obtain ⟨m, rfl⟩ := hsurj hyS
      have hmB : m ∉ B := (hBc m).2 hyS
      refine ⟨⟨m, hmB⟩, ?_, rfl⟩
      exact by_contra fun hmV ↦ hy ⟨m, fun h ↦ hmV h.1, rfl⟩
  rw [this]
  have hBcl : IsClosed B := hpre ▸ hS.preimage κ.continuous
  have hcl : IsClosed (V ∩ Bᶜ)ᶜ := by
    rw [Set.compl_inter, compl_compl]
    exact hV.isClosed_compl.union hBcl
  exact hS.isOpen_compl.inter (hcl.isCompact.image κ.continuous).isClosed.isOpen_compl

end Gluing

/-! ### Holomorphic division by a coordinate -/

/-- **Local Hadamard division.** A function holomorphic near a point `b` of the hyperplane
`w_k = 0` and vanishing on that hyperplane near `b` is, near `b`, `w_k` times a holomorphic
function. -/
private lemma exists_eventually_eq_coord_mul {d : ℕ} {F : (Fin d → ℂ) → ℂ} {b : Fin d → ℂ}
    {k : Fin d} (hbk : b k = 0) (hF : ∀ᶠ y in 𝓝 b, DifferentiableAt ℂ F y)
    (hzero : ∀ᶠ y in 𝓝 b, y k = 0 → F y = 0) :
    ∃ V : (Fin d → ℂ) → ℂ, ∀ᶠ y in 𝓝 b, DifferentiableAt ℂ V y ∧ F y = y k * V y := by
  obtain ⟨⟨H, hHd, hHe⟩, -⟩ :=
    MMP.Analytic.exists_sub_eq_sum_sub_mul_and_comp_sub_comp_mem (E := ℂ) hF
  -- `π` projects onto the hyperplane
  set π : (Fin d → ℂ) → (Fin d → ℂ) := fun y ↦ y - y k • Pi.single k 1
  have hπd : Differentiable ℂ π := fun y ↦
    differentiableAt_id.sub ((differentiableAt_apply k y).smul_const _)
  have hπb : π b = b := by simp [π, hbk]
  have hπt : Tendsto π (𝓝 b) (𝓝 b) := by simpa [hπb] using hπd.continuous.tendsto b
  have hψ : Tendsto (fun y ↦ (y, π y)) (𝓝 b) (𝓝 (b, b)) := tendsto_id.prodMk_nhds hπt
  refine ⟨fun y ↦ H k (y, π y), ?_⟩
  filter_upwards [hψ.eventually (hHd k), hψ.eventually hHe, hπt.eventually hzero] with y hd he hz
  refine ⟨hd.comp y (differentiableAt_id.prodMk (hπd y)), ?_⟩
  rw [hz (by simp [π]), sub_zero] at he
  rw [he]
  simp [π, Pi.single_apply]

/-- On the hyperplane `w_k = 0`, the derivative of `w ↦ w_k V(w)` is `v ↦ v_k V(w)`. -/
private lemma fderiv_apply_eq_of_eventuallyEq_coord_mul {d : ℕ} {F V : (Fin d → ℂ) → ℂ}
    {y : Fin d → ℂ} {k : Fin d} (hyk : y k = 0) (hV : DifferentiableAt ℂ V y)
    (hF : F =ᶠ[𝓝 y] fun w ↦ w k * V w) (v : Fin d → ℂ) : fderiv ℂ F y v = v k * V y := by
  rw [hF.fderiv_eq, ((hasFDerivAt_apply k y).fun_mul hV.hasFDerivAt).fderiv]
  simp [hyk, mul_comm]

/-- A coordinate of a map with a differentiable left inverse near `z` has nonzero derivative
at `z`. -/
private lemma fderiv_apply_ne_zero_of_leftInverse {d : ℕ} {τ τ' : (Fin d → ℂ) → (Fin d → ℂ)}
    {z : Fin d → ℂ} (hτ : DifferentiableAt ℂ τ z) (hτ' : DifferentiableAt ℂ τ' (τ z))
    (hinv : ∀ᶠ y in 𝓝 z, τ' (τ y) = y) (k' : Fin d) : fderiv ℂ (fun w ↦ τ w k') z ≠ 0 := by
  have hcomp : (fderiv ℂ τ' (τ z)).comp (fderiv ℂ τ z) = ContinuousLinearMap.id ℂ _ :=
    (hτ'.hasFDerivAt.comp z hτ.hasFDerivAt).unique ((hasFDerivAt_id z).congr_of_eventuallyEq hinv)
  have hinj : Function.Injective (fderiv ℂ τ z) := fun v w hvw ↦ by
    simpa [← ContinuousLinearMap.comp_apply, hcomp] using congrArg (fderiv ℂ τ' (τ z)) hvw
  have hsurj : Function.Surjective (fderiv ℂ τ z : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :=
    LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨v, hv⟩ := hsurj (Pi.single k' 1)
  change fderiv ℂ τ z v = _ at hv
  intro h0
  have h1 : fderiv ℂ (fun w ↦ τ w k') z v = fderiv ℂ τ z v k' := by
    change fderiv ℂ ((fun f : Fin d → ℂ ↦ f k') ∘ τ) z v = _
    rw [((hasFDerivAt_apply k' (τ z)).comp z hτ.hasFDerivAt).fderiv]; rfl
  rw [h0, hv] at h1
  simp at h1

/-- A function holomorphic on an open set `D ⊆ ℂᵈ` vanishing on the hyperplane `z_k = 0`, where it
is a coordinate of a biholomorphism, is `z_k` times a nowhere vanishing holomorphic function. -/
private theorem exists_eq_mul_of_eq_zero_iff {d : ℕ} {τ τ' : (Fin d → ℂ) → (Fin d → ℂ)}
    {D D' : Set (Fin d → ℂ)} (hD : IsOpen D) (hD' : IsOpen D') (hτ : DifferentiableOn ℂ τ D)
    (hτ' : DifferentiableOn ℂ τ' D') (hmaps : ∀ z ∈ D, τ z ∈ D') (hinv : ∀ z ∈ D, τ' (τ z) = z)
    (k k' : Fin d) (hzero : ∀ z ∈ D, τ z k' = 0 ↔ z k = 0) :
    ∃ U : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ U D ∧ (∀ z ∈ D, U z ≠ 0) ∧
      ∀ z ∈ D, τ z k' = z k * U z := by
  classical
  set F : (Fin d → ℂ) → ℂ := fun z ↦ τ z k'
  have hFat : ∀ z ∈ D, DifferentiableAt ℂ F z := fun z hz ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k').differentiable
      |>.comp_differentiableOn hτ).differentiableAt (hD.mem_nhds hz)
  let U : (Fin d → ℂ) → ℂ := fun z ↦ if z k = 0 then fderiv ℂ F z (Pi.single k 1) else F z / z k
  have heq : ∀ z ∈ D, F z = z k * U z := fun z hz ↦ by
    by_cases hzk : z k = 0
    · rw [hzk, zero_mul]; exact (hzero z hz).2 hzk
    · simp only [U, hzk, ↓reduceIte]; field_simp
  -- near a point of the hyperplane, `U` is the local Hadamard quotient
  have hloc : ∀ z ∈ D, z k = 0 → ∃ V : (Fin d → ℂ) → ℂ, DifferentiableAt ℂ V z ∧
      U =ᶠ[𝓝 z] V ∧ ∀ v, fderiv ℂ F z v = v k * V z := by
    intro z hz hzk
    obtain ⟨V, hV⟩ := exists_eventually_eq_coord_mul hzk
      (eventually_of_mem (hD.mem_nhds hz) hFat)
      (eventually_of_mem (hD.mem_nhds hz) fun y hy ↦ (hzero y hy).2)
    refine ⟨V, hV.self_of_nhds.1, ?_, fderiv_apply_eq_of_eventuallyEq_coord_mul hzk
      hV.self_of_nhds.1 (hV.mono fun _ h ↦ h.2)⟩
    filter_upwards [hV.eventually_nhds] with y hy
    by_cases hyk : y k = 0
    · simp only [U, hyk, ↓reduceIte]
      rw [fderiv_apply_eq_of_eventuallyEq_coord_mul hyk hy.self_of_nhds.1 (hy.mono fun _ h ↦ h.2)]
      simp
    · simp only [U, hyk, ↓reduceIte]
      rw [hy.self_of_nhds.2]
      field_simp
  refine ⟨U, fun z hz ↦ ?_, fun z hz hU0 ↦ ?_, heq⟩
  · by_cases hzk : z k = 0
    · obtain ⟨V, hVd, hUV, -⟩ := hloc z hz hzk
      exact (hVd.congr_of_eventuallyEq hUV).differentiableWithinAt
    · refine (((hFat z hz).mul ((differentiableAt_apply (𝕜 := ℂ) k z).inv hzk))
        |>.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [((continuous_apply k).continuousAt (x := z)).eventually_ne hzk] with y hy
      simp [U, hy, div_eq_mul_inv]
  · by_cases hzk : z k = 0
    · obtain ⟨V, -, hUV, hFV⟩ := hloc z hz hzk
      refine fderiv_apply_ne_zero_of_leftInverse (hτ.differentiableAt (hD.mem_nhds hz))
        (hτ'.differentiableAt (hD'.mem_nhds (hmaps z hz)))
        (eventually_of_mem (hD.mem_nhds hz) hinv) k' (ContinuousLinearMap.ext fun v ↦ ?_)
      change fderiv ℂ F z v = 0
      simp [hFV, ← hUV.self_of_nhds, hU0]
    · exact hzk ((hzero z hz).1 ((heq z hz).trans (by rw [hU0, mul_zero])))

/-- A function holomorphic on an open subset of `ℂᵈ` is real smooth there (Osgood's lemma). -/
private lemma contDiffAt_of_differentiableOn {d : ℕ} {f : (Fin d → ℂ) → ℂ}
    {s : Set (Fin d → ℂ)} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) {z : Fin d → ℂ}
    (hz : z ∈ s) : ContDiffAt ℝ ∞ f z := by
  have hosg := ((MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.1 d s f hs
    hf.continuousOn (fun ζ hζ j ↦ by
      have h1 : DifferentiableAt ℂ f (Function.update ζ j (ζ j)) := by
        rw [Function.update_eq_self]; exact hf.differentiableAt (hs.mem_nhds hζ)
      have hu : DifferentiableAt ℂ (fun w : ℂ ↦ Function.update ζ j w) (ζ j) := by
        rw [differentiableAt_pi]
        intro i
        by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      exact h1.comp (ζ j) hu)).2.1
  exact (hosg z hz).contDiffAt.restrict_scalars ℝ

/-! ### Unit directions -/

/-- The direction `z / |z|` of a complex number (`0` at `0`). -/
private noncomputable def unitDir (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

private lemma unitDir_mul (z w : ℂ) : unitDir (z * w) = unitDir z * unitDir w := by
  simp only [unitDir, norm_mul, Complex.ofReal_mul]
  exact mul_div_mul_comm z w _ _

private lemma norm_unitDir {z : ℂ} (hz : z ≠ 0) : ‖unitDir z‖ = 1 := by
  have : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  simp [unitDir, norm_div, this]

private lemma norm_unitDir_le (z : ℂ) : ‖unitDir z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [unitDir, hz]
  · rw [norm_unitDir hz]

private lemma norm_mul_unitDir (z : ℂ) : (‖z‖ : ℂ) * unitDir z = z := by
  by_cases hz : z = 0
  · simp [unitDir, hz]
  · have : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
    simp only [unitDir]
    field_simp

private lemma unitDir_one : unitDir 1 = 1 := by simp [unitDir]

private lemma unitDir_ofReal_mul {r : ℝ} (hr : 0 < r) (z : ℂ) : unitDir (r * z) = unitDir z := by
  rw [unitDir_mul]
  have : unitDir (r : ℂ) = 1 := by
    simp [unitDir, Complex.norm_real, abs_of_pos hr, (Complex.ofReal_ne_zero.2 hr.ne')]
  rw [this, one_mul]

private lemma unitDir_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : unitDir z = z := by
  simp [unitDir, hz]

private lemma continuousAt_unitDir {z : ℂ} (hz : z ≠ 0) : ContinuousAt unitDir z := by
  have : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  exact continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt this

private lemma contDiffAt_unitDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℂ} {x : E} (hF : ContDiffAt ℝ ∞ F x) (h0 : F x ≠ 0) :
    ContDiffAt ℝ ∞ (fun x ↦ unitDir (F x)) x := by
  have : (fun x ↦ unitDir (F x)) = fun x ↦ F x * ((‖F x‖⁻¹ : ℝ) : ℂ) := by
    funext x; simp [unitDir, div_eq_mul_inv]
  rw [this]
  exact hF.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((hF.norm ℝ h0).inv (norm_ne_zero_iff.2 h0)))

private lemma continuousOn_unitDir {X : Type*} [TopologicalSpace X] {g : X → ℂ} {s : Set X}
    (hg : ContinuousOn g s) (h0 : ∀ x ∈ s, g x ≠ 0) : ContinuousOn (fun x ↦ unitDir (g x)) s :=
  fun x hx ↦ (continuousAt_unitDir (h0 x hx)).comp_continuousWithinAt (hg x hx)

/-- A condition imposed, for finitely many indices `k`, on the face `o k` named by `k` (if any)
is open when each of its instances is. -/
private lemma isOpen_setOf_forall_eq_some {X ι J : Type*} [TopologicalSpace X] [Finite ι]
    (o : ι → Option J) {P : ι → J → X → Prop} (hP : ∀ k j, o k = some j → IsOpen {x | P k j x}) :
    IsOpen {x | ∀ k j, o k = some j → P k j x} := by
  simp only [setOf_forall]
  refine isOpen_iInter_of_finite fun k ↦ ?_
  cases h : o k with
  | none => simp
  | some j => simpa using hP k j h

/-! ### Topological facts -/

/-- Functions continuous near a point of the closure of `G` and equal on `G` agree there. -/
private lemma eq_of_mem_closure {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [T2Space Z] {G : Set X} {m : X} (hm : m ∈ closure G) {g h : X → Z} (hg : ContinuousAt g m)
    (hh : ContinuousAt h m) (hgh : ∀ᶠ p in 𝓝 m, p ∈ G → g p = h p) : g m = h m := by
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hm
  have h1 : Tendsto g (𝓝[G] m) (𝓝 (g m)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[G] m) (𝓝 (h m)) := by
    refine (hh.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have : ∀ᶠ p in 𝓝[G] m, p ∈ G := self_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds hgh, this] with p hp hpG
    exact (hp hpG).symm
  exact tendsto_nhds_unique h1 h2

/-- A function continuous on `S ∩ U`, multiplied by a function vanishing off a closed `K ⊆ S`,
is continuous on the open set `U`. -/
private lemma continuousOn_ofReal_mul {X : Type*} [TopologicalSpace X] {g : X → ℂ} {φ : X → ℝ}
    (hφ : Continuous φ) {S K U : Set X} (hS : IsOpen S) (hK : IsClosed K) (hKS : K ⊆ S)
    (hz : ∀ y ∉ K, φ y = 0) (hU : IsOpen U) (hg : ContinuousOn g (S ∩ U)) :
    ContinuousOn (fun y ↦ (φ y : ℂ) * g y) U := by
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hyS : y ∈ S
  · exact (Complex.continuous_ofReal.comp hφ).continuousAt.mul
      (hg.continuousAt ((hS.inter hU).mem_nhds ⟨hyS, hy⟩))
  · have hyK : y ∉ K := fun h ↦ hyS (hKS h)
    have hev : (fun y ↦ (φ y : ℂ) * g y) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hyK] with y' hy'
      simp [hz y' hy']
    exact (continuousAt_const (y := (0 : ℂ))).congr hev.symm

/-! ### Data of the blow-up -/

/-- Finite atlas data for the real oriented blow-up: faces `E j`, charts `e a` with the
coordinate `c a j` of `E j` (if it meets the chart), open sets `W a` covering, closed `K a`
inside the chart domains, and cut-offs `ψ a` equal to `1` on `W a` and `0` off `K a`. -/
private structure BlowupData (Y : Type) [TopologicalSpace Y] (d : ℕ) (J A : Type) where
  E : J → Set Y
  e : A → OpenPartialHomeomorph Y (Fin d → ℂ)
  c : A → J → Option (Fin d)
  W : A → Set Y
  K : A → Set Y
  ψ : A → Y → ℝ

namespace BlowupData

variable {Y : Type} [TopologicalSpace Y] {d : ℕ} {J A : Type} (B : BlowupData Y d J A)

/-- The domain of the transition map from chart `a` to chart `b`. -/
private def dom (a b : A) : Set (Fin d → ℂ) := (B.e a).target ∩ (B.e a).symm ⁻¹' (B.e b).source

/-- The axioms of the data. -/
private structure IsGood : Prop where
  isClosed_E : ∀ j, IsClosed (B.E j)
  differentiableOn : ∀ a b, DifferentiableOn ℂ (B.e b ∘ (B.e a).symm) (B.dom a b)
  c_inj : ∀ a j j' k, B.c a j = some k → B.c a j' = some k → j = j'
  c_none : ∀ a j, B.c a j = none → B.E j ∩ (B.e a).source = ∅
  c_some : ∀ a j k, B.c a j = some k → ∀ y ∈ (B.e a).source, y ∈ B.E j ↔ B.e a y k = 0
  isOpen_W : ∀ a, IsOpen (B.W a)
  cover : ∀ y, ∃ a, y ∈ B.W a
  isClosed_K : ∀ a, IsClosed (B.K a)
  K_sub : ∀ a, B.K a ⊆ (B.e a).source
  continuous_ψ : ∀ a, Continuous (B.ψ a)
  ψ_eq_one : ∀ a, ∀ y ∈ B.W a, B.ψ a y = 1
  ψ_eq_zero : ∀ a y, y ∉ B.K a → B.ψ a y = 0
  ψ_nonneg : ∀ a y, 0 ≤ B.ψ a y
  ψ_le_one : ∀ a y, B.ψ a y ≤ 1

variable {B}

variable (B) in
private lemma isOpen_dom (a b : A) : IsOpen (B.dom a b) :=
  (B.e a).isOpen_inter_preimage_symm (B.e b).open_source

private lemma IsGood.W_sub (hB : B.IsGood) (a : A) : B.W a ⊆ (B.e a).source := by
  intro y hy
  refine hB.K_sub a (by_contra fun h ↦ ?_)
  have := hB.ψ_eq_zero a y h
  rw [hB.ψ_eq_one a y hy] at this
  exact one_ne_zero this

variable (B)

/-- The local equation of `E j` in chart `a` (`1` if `E j` misses the chart). -/
private noncomputable def f (a : A) (j : J) (y : Y) : ℂ :=
  match B.c a j with
  | some k => B.e a y k
  | none => 1

/-- The union of the faces. -/
private def Eall : Set Y := ⋃ j, B.E j

/-- The angular part of the blow-up map over `Y ∖ E`. -/
private noncomputable def Φ (y : Y) : A × J → ℂ := fun p ↦ (B.ψ p.1 y : ℂ) * unitDir (B.f p.1 p.2 y)

/-- The graph of `Φ` over `Y ∖ E`. -/
private def graph : Set (Y × (A × J → ℂ)) := {p | p.1 ∉ B.Eall ∧ p.2 = B.Φ p.1}

/-- The real oriented blow-up, as the closure of the graph. -/
private def Mset : Set (Y × (A × J → ℂ)) := closure B.graph

private lemma continuousOn_f (a : A) (j : J) : ContinuousOn (B.f a j) (B.e a).source := by
  unfold f
  cases B.c a j with
  | none => exact continuousOn_const
  | some k => exact (continuous_apply k).comp_continuousOn (B.e a).continuousOn

variable {B}

private lemma IsGood.f_ne_zero (hB : B.IsGood) {a : A} {j : J} {y : Y} (hy : y ∈ (B.e a).source)
    (hyE : y ∉ B.E j) : B.f a j y ≠ 0 := by
  unfold f
  cases h : B.c a j with
  | none => exact one_ne_zero
  | some k => exact fun h0 ↦ hyE ((hB.c_some a j k h y hy).2 h0)

private lemma IsGood.continuousOn_Φ_apply (hB : B.IsGood) (a : A) (j : J) :
    ContinuousOn (fun y ↦ B.Φ y (a, j)) (B.E j)ᶜ :=
  continuousOn_ofReal_mul (hB.continuous_ψ a) (B.e a).open_source (hB.isClosed_K a)
    (hB.K_sub a) (hB.ψ_eq_zero a) (hB.isClosed_E j).isOpen_compl
    (continuousOn_unitDir ((B.continuousOn_f a j).mono inter_subset_left)
      fun y hy ↦ hB.f_ne_zero hy.1 hy.2)

/-- **Closed relations.** A relation between continuous functions of the points over an open
`O ⊆ Y`, valid on the graph, holds on the blow-up. -/
private lemma eq_of_mem_Mset {Z : Type*} [TopologicalSpace Z] [T2Space Z] {O : Set Y}
    (hO : IsOpen O) {g h : Y × (A × J → ℂ) → Z} (hg : ContinuousOn g {p | p.1 ∈ O})
    (hh : ContinuousOn h {p | p.1 ∈ O}) (hgh : ∀ p ∈ B.graph, p.1 ∈ O → g p = h p)
    {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset) (hmO : m.1 ∈ O) : g m = h m := by
  have hOp : IsOpen {p : Y × (A × J → ℂ) | p.1 ∈ O} := hO.preimage continuous_fst
  refine eq_of_mem_closure hm (hg.continuousAt (hOp.mem_nhds hmO))
    (hh.continuousAt (hOp.mem_nhds hmO)) ?_
  filter_upwards [hOp.mem_nhds hmO] with p hp hpG
  exact hgh p hpG hp

private lemma IsGood.Mset_apply_eq_zero (hB : B.IsGood) {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset)
    {a : A} (hma : m.1 ∉ B.K a) (j : J) : m.2 (a, j) = 0 := by
  refine eq_of_mem_Mset (g := fun p ↦ p.2 (a, j)) (h := fun _ ↦ (0 : ℂ))
    (hB.isClosed_K a).isOpen_compl ((continuous_apply (a, j)).comp continuous_snd).continuousOn
    continuousOn_const ?_ hm hma
  rintro p ⟨-, hp⟩ hpa
  simp [hp, Φ, hB.ψ_eq_zero a p.1 hpa]

private lemma IsGood.norm_Mset_apply_le (hB : B.IsGood) {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset)
    (a : A) (j : J) : ‖m.2 (a, j)‖ ≤ 1 := by
  have hcl : IsClosed {p : Y × (A × J → ℂ) | ‖p.2 (a, j)‖ ≤ 1} :=
    isClosed_le ((continuous_apply (a, j)).comp continuous_snd).norm continuous_const
  refine closure_minimal (fun p hp ↦ ?_) hcl hm
  obtain ⟨-, hp⟩ := hp
  simp only [mem_setOf_eq, hp, Φ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hB.ψ_nonneg a p.1)]
  exact mul_le_one₀ (hB.ψ_le_one a p.1) (norm_nonneg _) (norm_unitDir_le _)

private lemma IsGood.Mset_ψ_mul (hB : B.IsGood) {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset) {a : A}
    {j : J} {k : Fin d} (hk : B.c a j = some k) (hma : m.1 ∈ (B.e a).source) :
    (B.ψ a m.1 : ℂ) * B.e a m.1 k = ‖B.e a m.1 k‖ * m.2 (a, j) := by
  have hc : ContinuousOn (fun p : Y × (A × J → ℂ) ↦ B.e a p.1 k) {p | p.1 ∈ (B.e a).source} :=
    (continuous_apply k).comp_continuousOn
      ((B.e a).continuousOn.comp continuous_fst.continuousOn fun _ h ↦ h)
  refine eq_of_mem_Mset (g := fun p ↦ (B.ψ a p.1 : ℂ) * B.e a p.1 k)
    (h := fun p ↦ ‖B.e a p.1 k‖ * p.2 (a, j)) (B.e a).open_source
    (((Complex.continuous_ofReal.comp ((hB.continuous_ψ a).comp continuous_fst))).continuousOn.mul
      hc) ((Complex.continuous_ofReal.continuousOn.comp hc.norm fun _ _ ↦ mem_univ _).mul
        ((continuous_apply (a, j)).comp continuous_snd).continuousOn) ?_ hm hma
  rintro p ⟨-, hp⟩ -
  simp only [hp, Φ, f, hk]
  rw [mul_left_comm, norm_mul_unitDir]

private lemma IsGood.norm_Mset_apply (hB : B.IsGood) {m : Y × (A × J → ℂ)}
    (hm : m ∈ B.Mset) {a : A} (j : J) (hma : m.1 ∈ (B.e a).source) :
    ‖m.2 (a, j)‖ = B.ψ a m.1 := by
  refine eq_of_mem_Mset (g := fun p ↦ ‖p.2 (a, j)‖) (h := fun p ↦ B.ψ a p.1) (B.e a).open_source
    ((continuous_apply (a, j)).comp continuous_snd).norm.continuousOn
    ((hB.continuous_ψ a).comp continuous_fst).continuousOn ?_ hm hma
  rintro p ⟨hpE, hp⟩ hpa
  have hpj : p.1 ∉ B.E j := fun h ↦ hpE (mem_iUnion.2 ⟨j, h⟩)
  simp only [hp, Φ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hB.ψ_nonneg a p.1), norm_unitDir (hB.f_ne_zero hpa hpj), mul_one]

private lemma IsGood.Mset_apply_of_notMem (hB : B.IsGood) {m : Y × (A × J → ℂ)}
    (hm : m ∈ B.Mset) {a : A} {j : J} (hma : m.1 ∈ (B.e a).source) (hmj : m.1 ∉ B.E j) :
    m.2 (a, j) = B.Φ m.1 (a, j) := by
  refine eq_of_mem_Mset (g := fun p ↦ p.2 (a, j)) (h := fun p ↦ B.Φ p.1 (a, j))
    (hB.isClosed_E j).isOpen_compl ((continuous_apply (a, j)).comp continuous_snd).continuousOn
    ((hB.continuousOn_Φ_apply a j).comp continuous_fst.continuousOn fun _ h ↦ h) ?_ hm hmj
  rintro p ⟨-, hp⟩ -
  rw [hp]

private lemma IsGood.Mset_eq_Φ (hB : B.IsGood) {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset)
    (hmE : m.1 ∉ B.Eall) : m.2 = B.Φ m.1 := by
  funext ⟨a, j⟩
  have hmj : m.1 ∉ B.E j := fun h ↦ hmE (mem_iUnion.2 ⟨j, h⟩)
  by_cases hma : m.1 ∈ (B.e a).source
  · exact hB.Mset_apply_of_notMem hm hma hmj
  · have hK : m.1 ∉ B.K a := fun h ↦ hma (hB.K_sub a h)
    rw [hB.Mset_apply_eq_zero hm hK]
    simp [Φ, hB.ψ_eq_zero a _ hK]

private lemma IsGood.isCompact_Mset [CompactSpace Y] (hB : B.IsGood) : IsCompact B.Mset := by
  refine (isCompact_univ.prod (isCompact_univ_pi fun _ ↦ isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
    isClosed_closure fun m hm ↦ ⟨mem_univ _, fun p ↦ ?_⟩
  simpa using hB.norm_Mset_apply_le hm p.1 p.2

/-! ### Transition units -/

variable (B) in
/-- The unit relating the local equations of a face in two charts, read in the first chart. -/
private noncomputable def Ufun (a b : A) (k k' : Fin d) : (Fin d → ℂ) → ℂ :=
  open Classical in
  if h : ∃ U : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ U (B.dom a b) ∧ (∀ z ∈ B.dom a b, U z ≠ 0) ∧
      ∀ z ∈ B.dom a b, (B.e b ∘ (B.e a).symm) z k' = z k * U z then h.choose else fun _ ↦ 1

variable (B) in
private lemma mem_dom {a b : A} {y : Y} (hya : y ∈ (B.e a).source)
    (hyb : y ∈ (B.e b).source) : B.e a y ∈ B.dom a b :=
  ⟨(B.e a).map_source hya, by simp only [mem_preimage, (B.e a).left_inv hya]; exact hyb⟩

private lemma IsGood.Ufun_spec (hB : B.IsGood) {a b : A} {j : J} {k k' : Fin d}
    (hk : B.c a j = some k) (hk' : B.c b j = some k') :
    DifferentiableOn ℂ (B.Ufun a b k k') (B.dom a b) ∧ (∀ z ∈ B.dom a b, B.Ufun a b k k' z ≠ 0) ∧
      ∀ z ∈ B.dom a b, (B.e b ∘ (B.e a).symm) z k' = z k * B.Ufun a b k k' z := by
  have hex : ∃ U : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ U (B.dom a b) ∧
      (∀ z ∈ B.dom a b, U z ≠ 0) ∧
      ∀ z ∈ B.dom a b, (B.e b ∘ (B.e a).symm) z k' = z k * U z := by
    refine exists_eq_mul_of_eq_zero_iff (B.isOpen_dom a b) (B.isOpen_dom b a)
      (hB.differentiableOn a b) (hB.differentiableOn b a) (fun z hz ↦ ?_) (fun z hz ↦ ?_) k k'
      fun z hz ↦ ?_
    · refine ⟨(B.e b).map_source hz.2, ?_⟩
      simp only [mem_preimage, Function.comp_apply, (B.e b).left_inv hz.2]
      exact (B.e a).map_target hz.1
    · simp [(B.e b).left_inv hz.2, (B.e a).right_inv hz.1]
    · have h1 := hB.c_some b j k' hk' _ hz.2
      have h2 := hB.c_some a j k hk _ ((B.e a).map_target hz.1)
      rw [(B.e a).right_inv hz.1] at h2
      exact h1.symm.trans h2
  unfold Ufun
  rw [dif_pos hex]
  exact hex.choose_spec

private lemma IsGood.Ufun_self (hB : B.IsGood) {a : A} {j : J} {k : Fin d}
    (hk : B.c a j = some k) {z : Fin d → ℂ} (hz : z ∈ B.dom a a) : B.Ufun a a k k z = 1 := by
  obtain ⟨hd, -, heq⟩ := hB.Ufun_spec hk hk
  have hone : ∀ z' ∈ B.dom a a, z' k ≠ 0 → B.Ufun a a k k z' = 1 := by
    intro z' hz' hk0
    have := heq z' hz'
    simp only [Function.comp_apply, (B.e a).right_inv hz'.1] at this
    exact (mul_eq_left₀ hk0).1 this.symm
  by_cases hzk : z k = 0
  · set ek : Fin d → ℂ := Pi.single k 1
    have hcont : ContinuousAt (B.Ufun a a k k) z :=
      (hd.differentiableAt ((B.isOpen_dom a a).mem_nhds hz)).continuousAt
    have hline : Tendsto (fun t : ℂ ↦ z + t • ek) (𝓝[≠] 0) (𝓝 z) := by
      have : Continuous (fun t : ℂ ↦ z + t • ek) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun t : ℂ ↦ B.Ufun a a k k (z + t • ek)) (𝓝[≠] 0)
        (𝓝 (B.Ufun a a k k z)) := hcont.tendsto.comp hline
    have h2 : Tendsto (fun t : ℂ ↦ B.Ufun a a k k (z + t • ek)) (𝓝[≠] 0) (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hline ((B.isOpen_dom a a).mem_nhds hz), self_mem_nhdsWithin] with t ht ht0
      refine (hone _ ht ?_).symm
      simpa [ek, hzk] using ht0
    exact tendsto_nhds_unique h1 h2
  · exact hone z hz hzk

variable (B) in
/-- The unit `u` with `f_b = u f_a` on the overlap of the charts `a`, `b`, for the face `j`. -/
private noncomputable def u (a b : A) (j : J) (y : Y) : ℂ :=
  match B.c a j, B.c b j with
  | none, _ => B.f b j y
  | some k, none => (B.e a y k)⁻¹
  | some k, some k' => B.Ufun a b k k' (B.e a y)

private lemma IsGood.u_spec (hB : B.IsGood) {a b : A} (j : J) {y : Y}
    (hya : y ∈ (B.e a).source) (hyb : y ∈ (B.e b).source) :
    B.f b j y = B.u a b j y * B.f a j y ∧ B.u a b j y ≠ 0 := by
  unfold u
  cases ha : B.c a j with
  | none =>
    have hyE : y ∉ B.E j := fun h ↦ (hB.c_none a j ha).subset ⟨h, hya⟩
    simp only [f, ha, mul_one]
    exact ⟨trivial, by simpa [f] using hB.f_ne_zero hyb hyE⟩
  | some k =>
    cases hb : B.c b j with
    | none =>
      have hyE : y ∉ B.E j := fun h ↦ (hB.c_none b j hb).subset ⟨h, hyb⟩
      have h0 : B.e a y k ≠ 0 := fun h0 ↦ hyE ((hB.c_some a j k ha y hya).2 h0)
      simp only [f, ha, hb]
      exact ⟨(inv_mul_cancel₀ h0).symm, inv_ne_zero h0⟩
    | some k' =>
      obtain ⟨-, hne, heq⟩ := hB.Ufun_spec ha hb
      have hz := B.mem_dom hya hyb
      simp only [f, ha, hb]
      refine ⟨?_, hne _ hz⟩
      have := heq _ hz
      simp only [Function.comp_apply, (B.e a).left_inv hya] at this
      rw [this, mul_comm]

private lemma IsGood.continuousOn_u (hB : B.IsGood) (a b : A) (j : J) :
    ContinuousOn (B.u a b j) ((B.e a).source ∩ (B.e b).source) := by
  unfold u
  cases ha : B.c a j with
  | none => exact (B.continuousOn_f b j).mono inter_subset_right
  | some k =>
    cases hb : B.c b j with
    | none =>
      refine ContinuousOn.inv₀ ((continuous_apply k).comp_continuousOn
        ((B.e a).continuousOn.mono inter_subset_left)) fun y hy h0 ↦ ?_
      have hyE : y ∉ B.E j := fun h ↦ (hB.c_none b j hb).subset ⟨h, hy.2⟩
      exact hyE ((hB.c_some a j k ha y hy.1).2 h0)
    | some k' =>
      obtain ⟨hd, -, -⟩ := hB.Ufun_spec ha hb
      exact hd.continuousOn.comp ((B.e a).continuousOn.mono inter_subset_left)
        fun y hy ↦ B.mem_dom hy.1 hy.2

private lemma IsGood.u_self (hB : B.IsGood) {a : A} (j : J) {y : Y} (hy : y ∈ (B.e a).source) :
    B.u a a j y = 1 := by
  unfold u
  cases ha : B.c a j with
  | none => simp [f, ha]
  | some k => exact hB.Ufun_self ha (B.mem_dom hy hy)

private lemma IsGood.Mset_apply_mul (hB : B.IsGood) {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset)
    {a b : A} (j : J) (hma : m.1 ∈ (B.e a).source) (hmb : m.1 ∈ (B.e b).source) :
    m.2 (b, j) * B.ψ a m.1 = B.ψ b m.1 * unitDir (B.u a b j m.1) * m.2 (a, j) := by
  have hO : IsOpen ((B.e a).source ∩ (B.e b).source) := (B.e a).open_source.inter (B.e b).open_source
  have hcu : ContinuousOn (fun p : Y × (A × J → ℂ) ↦ unitDir (B.u a b j p.1))
      {p | p.1 ∈ (B.e a).source ∩ (B.e b).source} :=
    continuousOn_unitDir ((hB.continuousOn_u a b j).comp continuous_fst.continuousOn
      fun _ h ↦ h) fun p hp ↦ (hB.u_spec j hp.1 hp.2).2
  refine eq_of_mem_Mset (g := fun p ↦ p.2 (b, j) * B.ψ a p.1)
    (h := fun p ↦ B.ψ b p.1 * unitDir (B.u a b j p.1) * p.2 (a, j)) hO
    (((continuous_apply (b, j)).comp continuous_snd).continuousOn.mul
      (Complex.continuous_ofReal.comp ((hB.continuous_ψ a).comp continuous_fst)).continuousOn)
    (((Complex.continuous_ofReal.comp ((hB.continuous_ψ b).comp
      continuous_fst)).continuousOn.mul hcu).mul
        ((continuous_apply (a, j)).comp continuous_snd).continuousOn) ?_ hm ⟨hma, hmb⟩
  rintro p ⟨-, hp⟩ hpO
  simp only [hp, Φ]
  rw [(hB.u_spec j hpO.1 hpO.2).1, unitDir_mul]
  ring

end BlowupData

/-! ### Points of the circle -/

/-- The point of the unit circle at height `t - 1` over the direction `η`. -/
private noncomputable def circ (η : ℂ) (t : ℝ) : ℂ :=
  η * ((√(1 - (t - 1) ^ 2) : ℝ) + ((t - 1 : ℝ) : ℂ) * Complex.I)

private lemma continuous_circ (η : ℂ) : Continuous (circ η) := by
  unfold circ; fun_prop

private lemma norm_circ {η : ℂ} (hη : ‖η‖ = 1) {t : ℝ} (ht : |t - 1| ≤ 1) : ‖circ η t‖ = 1 := by
  have h0 : 0 ≤ 1 - (t - 1) ^ 2 := by
    have := (sq_le_one_iff_abs_le_one (t - 1)).2 ht; linarith
  rw [circ, norm_mul, hη, one_mul]
  have : ‖((√(1 - (t - 1) ^ 2) : ℝ) : ℂ) + ((t - 1 : ℝ) : ℂ) * Complex.I‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I, Real.sq_sqrt h0]; ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

private lemma contDiffAt_circ (η : ℂ) {t : ℝ} (ht : |t - 1| < 1) :
    ContDiffAt ℝ ∞ (circ η) t := by
  have hpos : 1 - (t - 1) ^ 2 ≠ 0 := by
    have := (sq_lt_one_iff_abs_lt_one (t - 1)).2 ht; linarith
  unfold circ
  refine contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp t
    ((contDiffAt_const.sub ((contDiffAt_id.sub contDiffAt_const).pow 2)).sqrt hpos)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp t (contDiffAt_id.sub contDiffAt_const)).mul
        contDiffAt_const))

private lemma conj_mul_self_of_norm_eq_one {η : ℂ} (hη : ‖η‖ = 1) :
    starRingEnd ℂ η * η = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]; simp

private lemma im_conj_mul_circ {η : ℂ} (hη : ‖η‖ = 1) (t : ℝ) :
    (starRingEnd ℂ η * circ η t).im = t - 1 := by
  rw [circ, ← mul_assoc, conj_mul_self_of_norm_eq_one hη, one_mul]
  simp

private lemma circ_conj_mul {η w : ℂ} (hη : ‖η‖ = 1) (hw : ‖w‖ = 1)
    (hre : 0 < (starRingEnd ℂ η * w).re) : circ η (1 + (starRingEnd ℂ η * w).im) = w := by
  set v := starRingEnd ℂ η * w with hv
  have hvn : ‖v‖ = 1 := by simp [hv, hη, hw]
  have hre2 : v.re ^ 2 = 1 - v.im ^ 2 := by
    have := Complex.sq_norm_sub_sq_im v; rw [hvn] at this; linarith
  have hsq : √(1 - (1 + v.im - 1) ^ 2) = v.re := by
    rw [show 1 + v.im - 1 = v.im by ring, ← hre2, Real.sqrt_sq hre.le]
  rw [circ, hsq, show (1 + v.im - 1 : ℝ) = v.im by ring, Complex.re_add_im, hv, ← mul_assoc,
    mul_comm η, conj_mul_self_of_norm_eq_one hη, one_mul]

namespace BlowupData

variable {Y : Type} [TopologicalSpace Y] {d : ℕ} {J A : Type} {B : BlowupData Y d J A}

/-! ### Charts of the blow-up -/

variable (B) in
/-- The data of a polar chart of the blow-up: a chart `a` of `Y`, the face `jOf k` whose
equation is the coordinate `k` (for the normal coordinates), base values `z0` of the other
coordinates and `ω0` of the angles, an open set `O` of `Y`, and a base point. -/
private structure ChartData where
  a : A
  jOf : Fin d → Option J
  z0 : Fin d → ℂ
  ω0 : Fin d → ℂ
  O : Set Y
  base : B.Mset

namespace ChartData

/-- The axioms of the data of a polar chart. -/
private structure IsGood (D : B.ChartData) : Prop where
  isOpen_O : IsOpen D.O
  O_sub : D.O ⊆ B.W D.a
  jOf_c : ∀ k j, D.jOf k = some j → B.c D.a j = some k
  norm_ω0 : ∀ k j, D.jOf k = some j → ‖D.ω0 k‖ = 1
  O_E : ∀ j, (∀ k, D.jOf k ≠ some j) → ∀ y ∈ D.O, y ∉ B.E j
  O_tan : ∀ k, D.jOf k = none → ∀ y ∈ D.O, ‖B.e D.a y k - D.z0 k‖ < 1

variable (D : B.ChartData)

/-- The real coordinates of a point. -/
private noncomputable def coord (p : Y × (A × J → ℂ)) (k : Fin d) (s : Fin 2) : ℝ :=
  match D.jOf k with
  | some j => if s = 0 then ‖B.e D.a p.1 k‖ else 1 + (starRingEnd ℂ (D.ω0 k) * p.2 (D.a, j)).im
  | none => if s = 0 then 1 + (B.e D.a p.1 k - D.z0 k).re else 1 + (B.e D.a p.1 k - D.z0 k).im

/-- The coordinate vector of a point. -/
private noncomputable def raw (p : Y × (A × J → ℂ)) : EuclideanSpace ℝ (Fin (d * 2)) :=
  WithLp.toLp 2 fun i ↦ D.coord p (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

private lemma raw_apply (p : Y × (A × J → ℂ)) (k : Fin d) (s : Fin 2) :
    D.raw p (finProdFinEquiv (k, s)) = D.coord p k s := by
  unfold raw
  rw [PiLp.toLp_apply, Equiv.symm_apply_apply]

/-- The complex coordinates of the point of `Y` with real coordinates `v`. -/
private noncomputable def zD (v : EuclideanSpace ℝ (Fin (d * 2))) : Fin d → ℂ := fun k ↦
  match D.jOf k with
  | some _ => (v (finProdFinEquiv (k, 0)) : ℂ) * circ (D.ω0 k) (v (finProdFinEquiv (k, 1)))
  | none => D.z0 k + (((v (finProdFinEquiv (k, 0)) - 1 : ℝ) : ℂ) +
      ((v (finProdFinEquiv (k, 1)) - 1 : ℝ) : ℂ) * Complex.I)

/-- The point of `Y` with real coordinates `v`. -/
private noncomputable def yD (v : EuclideanSpace ℝ (Fin (d * 2))) : Y := (B.e D.a).symm (D.zD v)

open Classical in
/-- The angle of the face `j` at the point with real coordinates `v`, in chart `a`. -/
private noncomputable def Wfun (v : EuclideanSpace ℝ (Fin (d * 2))) (j : J) : ℂ :=
  if h : ∃ k, D.jOf k = some j then circ (D.ω0 h.choose) (v (finProdFinEquiv (h.choose, 1)))
  else unitDir (B.f D.a j (D.yD v))

open Classical in
/-- The factor carrying the angle in chart `a` to the angle in chart `b`. -/
private noncomputable def gfun (b : A) (j : J) (y : Y) : ℂ :=
  if y ∈ (B.e b).source then (B.ψ b y : ℂ) * unitDir (B.u D.a b j y) else 0

/-- The point of the blow-up with real coordinates `v`. -/
private noncomputable def Praw (v : EuclideanSpace ℝ (Fin (d * 2))) : Y × (A × J → ℂ) :=
  (D.yD v, fun q ↦ D.gfun q.1 q.2 (D.yD v) * D.Wfun v q.2)

/-- The coordinate vectors of the chart. -/
private def targetRaw : Set (EuclideanSpace ℝ (Fin (d * 2))) :=
  {v | (∀ k j, D.jOf k = some j → |v (finProdFinEquiv (k, 1)) - 1| < 1) ∧
    D.zD v ∈ (B.e D.a).target ∧ D.yD v ∈ D.O}

/-- The domain of the chart. -/
private def sourceSet : Set B.Mset :=
  {m | m.1.1 ∈ D.O ∧ ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.1.2 (D.a, j)).re}

variable {D}

private lemma IsGood.jOf_unique (hD : D.IsGood) {k k' : Fin d} {j : J} (hk : D.jOf k = some j)
    (hk' : D.jOf k' = some j) : k = k' :=
  Option.some_injective _ ((hD.jOf_c k j hk).symm.trans (hD.jOf_c k' j hk'))

private lemma IsGood.Wfun_of_jOf (hD : D.IsGood) {k : Fin d} {j : J} (hk : D.jOf k = some j)
    (v : EuclideanSpace ℝ (Fin (d * 2))) :
    D.Wfun v j = circ (D.ω0 k) (v (finProdFinEquiv (k, 1))) := by
  have h : ∃ k, D.jOf k = some j := ⟨k, hk⟩
  rw [Wfun, dif_pos h, hD.jOf_unique h.choose_spec hk]

private lemma Wfun_of_forall_ne {j : J} (hj : ∀ k, D.jOf k ≠ some j)
    (v : EuclideanSpace ℝ (Fin (d * 2))) : D.Wfun v j = unitDir (B.f D.a j (D.yD v)) := by
  have h : ¬ ∃ k, D.jOf k = some j := fun ⟨k, hk⟩ ↦ hj k hk
  rw [Wfun, dif_neg h]

private lemma continuous_zD : Continuous D.zD := by
  refine continuous_pi fun k ↦ ?_
  unfold zD
  cases D.jOf k with
  | some _ =>
    exact (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ _)).mul
      ((continuous_circ _).comp (PiLp.continuous_apply 2 _ _))
  | none =>
    exact continuous_const.add ((Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 _ _).sub continuous_const)).add
        ((Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ _).sub
          continuous_const)).mul continuous_const))

private lemma IsGood.isOpen_targetRaw (hD : D.IsGood) : IsOpen D.targetRaw :=
  (isOpen_setOf_forall_eq_some D.jOf
    (P := fun k _ (v : EuclideanSpace ℝ (Fin (d * 2))) ↦ |v (finProdFinEquiv (k, 1)) - 1| < 1)
    fun _ _ _ ↦ isOpen_lt
    ((PiLp.continuous_apply 2 _ _).sub continuous_const).abs continuous_const).inter
    ((B.e D.a).isOpen_inter_preimage_symm hD.isOpen_O |>.preimage continuous_zD)

private lemma coord_of_some {k : Fin d} {j : J} (h : D.jOf k = some j) (p : Y × (A × J → ℂ)) :
    D.coord p k 0 = ‖B.e D.a p.1 k‖ ∧
      D.coord p k 1 = 1 + (starRingEnd ℂ (D.ω0 k) * p.2 (D.a, j)).im := by
  simp [coord, h]

private lemma coord_of_none {k : Fin d} (h : D.jOf k = none) (p : Y × (A × J → ℂ)) :
    D.coord p k 0 = 1 + (B.e D.a p.1 k - D.z0 k).re ∧
      D.coord p k 1 = 1 + (B.e D.a p.1 k - D.z0 k).im := by
  simp [coord, h]

private lemma zD_of_some {k : Fin d} {j : J} (h : D.jOf k = some j)
    (v : EuclideanSpace ℝ (Fin (d * 2))) :
    D.zD v k = (v (finProdFinEquiv (k, 0)) : ℂ) * circ (D.ω0 k) (v (finProdFinEquiv (k, 1))) := by
  simp [zD, h]

private lemma zD_of_none {k : Fin d} (h : D.jOf k = none) (v : EuclideanSpace ℝ (Fin (d * 2))) :
    D.zD v k = D.z0 k + (((v (finProdFinEquiv (k, 0)) - 1 : ℝ) : ℂ) +
      ((v (finProdFinEquiv (k, 1)) - 1 : ℝ) : ℂ) * Complex.I) := by
  simp [zD, h]

private lemma IsGood.mem_source (hB : B.IsGood) (hD : D.IsGood) {y : Y} (hy : y ∈ D.O) :
    y ∈ (B.e D.a).source :=
  hB.W_sub D.a (hD.O_sub hy)

private lemma IsGood.ψ_eq_one' (hB : B.IsGood) (hD : D.IsGood) {y : Y} (hy : y ∈ D.O) :
    B.ψ D.a y = 1 :=
  hB.ψ_eq_one D.a y (hD.O_sub hy)

/-- On the chart domain, the angle in chart `a` is the circle point of the coordinates. -/
private lemma IsGood.circ_coord (hB : B.IsGood) (hD : D.IsGood)
    {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset) (hO : m.1 ∈ D.O)
    (hre : ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.2 (D.a, j)).re)
    {k : Fin d} {j : J} (h : D.jOf k = some j) :
    circ (D.ω0 k) (D.coord m k 1) = m.2 (D.a, j) := by
  rw [(coord_of_some h m).2]
  refine circ_conj_mul (hD.norm_ω0 k j h) ?_ (hre k j h)
  rw [hB.norm_Mset_apply hm j (hD.mem_source hB hO), hD.ψ_eq_one' hB hO]

private lemma IsGood.zD_raw (hB : B.IsGood) (hD : D.IsGood) {m : Y × (A × J → ℂ)}
    (hm : m ∈ B.Mset) (hO : m.1 ∈ D.O)
    (hre : ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.2 (D.a, j)).re) :
    D.zD (D.raw m) = B.e D.a m.1 := by
  funext k
  cases h : D.jOf k with
  | some j =>
    rw [zD_of_some h, raw_apply, raw_apply, hD.circ_coord hB hm hO hre h, (coord_of_some h m).1]
    have := hB.Mset_ψ_mul hm (hD.jOf_c k j h) (hD.mem_source hB hO)
    rw [hD.ψ_eq_one' hB hO, Complex.ofReal_one, one_mul] at this
    exact this.symm
  | none =>
    rw [zD_of_none h, raw_apply, raw_apply, (coord_of_none h m).1, (coord_of_none h m).2]
    have := Complex.re_add_im (B.e D.a m.1 k - D.z0 k)
    push_cast
    linear_combination this

private lemma continuousOn_gfun (hB : B.IsGood) (b : A) (j : J) :
    ContinuousOn (D.gfun b j) (B.e D.a).source := by
  classical
  have h1 : D.gfun b j = fun y ↦ (B.ψ b y : ℂ) *
      (if y ∈ (B.e b).source then unitDir (B.u D.a b j y) else 0) := by
    funext y
    unfold gfun
    split_ifs <;> simp
  rw [h1]
  refine continuousOn_ofReal_mul (hB.continuous_ψ b) (B.e b).open_source (hB.isClosed_K b)
    (hB.K_sub b) (hB.ψ_eq_zero b) (B.e D.a).open_source ?_
  have h2 : ContinuousOn (fun y ↦ unitDir (B.u D.a b j y)) ((B.e b).source ∩ (B.e D.a).source) :=
    continuousOn_unitDir ((hB.continuousOn_u D.a b j).mono fun y hy ↦ ⟨hy.2, hy.1⟩)
      fun y hy ↦ (hB.u_spec j hy.2 hy.1).2
  exact h2.congr fun y hy ↦ by simp [hy.1]

private lemma IsGood.gfun_self (hB : B.IsGood) (hD : D.IsGood) (j : J) {y : Y} (hy : y ∈ D.O) :
    D.gfun D.a j y = 1 := by
  have hs := hD.mem_source hB hy
  simp [gfun, hs, hD.ψ_eq_one' hB hy, hB.u_self j hs, unitDir_one]

private lemma IsGood.yD_mem_source (hB : B.IsGood) (hD : D.IsGood) {v : EuclideanSpace ℝ (Fin (d * 2))}
    (hv : v ∈ D.targetRaw) : D.yD v ∈ (B.e D.a).source :=
  hD.mem_source hB hv.2.2

private lemma e_yD {v : EuclideanSpace ℝ (Fin (d * 2))} (hv : v ∈ D.targetRaw) :
    B.e D.a (D.yD v) = D.zD v :=
  (B.e D.a).right_inv hv.2.1

private lemma IsGood.raw_Praw (hB : B.IsGood) (hD : D.IsGood) {v : EuclideanSpace ℝ (Fin (d * 2))}
    (hv : v ∈ D.targetRaw) (hq : ∀ i, 0 ≤ v i) : D.raw (D.Praw v) = v := by
  ext i
  obtain ⟨⟨k, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [raw_apply]
  cases h : D.jOf k with
  | some j =>
    fin_cases s
    · simp only [Fin.zero_eta]
      rw [(coord_of_some h _).1]
      change ‖B.e D.a (D.yD v) k‖ = _
      rw [e_yD hv, zD_of_some h, norm_mul, norm_circ (hD.norm_ω0 k j h) (hv.1 k j h).le,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq _)]
    · simp only [Fin.mk_one]
      rw [(coord_of_some h _).2]
      change 1 + (starRingEnd ℂ (D.ω0 k) * (D.gfun D.a j (D.yD v) * D.Wfun v j)).im = _
      rw [hD.gfun_self hB j hv.2.2, one_mul, hD.Wfun_of_jOf h, im_conj_mul_circ (hD.norm_ω0 k j h)]
      ring
  | none =>
    fin_cases s
    · simp only [Fin.zero_eta]
      rw [(coord_of_none h _).1]
      change 1 + (B.e D.a (D.yD v) k - D.z0 k).re = _
      rw [e_yD hv, zD_of_none h]
      simp
    · simp only [Fin.mk_one]
      rw [(coord_of_none h _).2]
      change 1 + (B.e D.a (D.yD v) k - D.z0 k).im = _
      rw [e_yD hv, zD_of_none h]
      simp

private lemma IsGood.Wfun_raw (hB : B.IsGood) (hD : D.IsGood) {m : Y × (A × J → ℂ)}
    (hm : m ∈ B.Mset) (hO : m.1 ∈ D.O)
    (hre : ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.2 (D.a, j)).re) (j : J) :
    D.Wfun (D.raw m) j = m.2 (D.a, j) := by
  by_cases hj : ∃ k, D.jOf k = some j
  · obtain ⟨k, hk⟩ := hj
    rw [hD.Wfun_of_jOf hk, raw_apply, hD.circ_coord hB hm hO hre hk]
  · push Not at hj
    have hyD : D.yD (D.raw m) = m.1 := by
      rw [yD, hD.zD_raw hB hm hO hre, (B.e D.a).left_inv (hD.mem_source hB hO)]
    rw [Wfun_of_forall_ne hj, hyD, hB.Mset_apply_of_notMem hm (hD.mem_source hB hO)
      (hD.O_E j hj _ hO)]
    simp [Φ, hD.ψ_eq_one' hB hO]

private lemma IsGood.Praw_raw (hB : B.IsGood) (hD : D.IsGood) {m : Y × (A × J → ℂ)}
    (hm : m ∈ B.Mset) (hO : m.1 ∈ D.O)
    (hre : ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.2 (D.a, j)).re) :
    D.Praw (D.raw m) = m := by
  have hyD : D.yD (D.raw m) = m.1 := by
    rw [yD, hD.zD_raw hB hm hO hre, (B.e D.a).left_inv (hD.mem_source hB hO)]
  have hsa := hD.mem_source hB hO
  refine Prod.ext hyD (funext fun q ↦ ?_)
  obtain ⟨b, j⟩ := q
  change D.gfun b j (D.yD (D.raw m)) * D.Wfun (D.raw m) j = m.2 (b, j)
  rw [hyD, hD.Wfun_raw hB hm hO hre j]
  by_cases hsb : m.1 ∈ (B.e b).source
  · have := hB.Mset_apply_mul hm j hsa hsb
    rw [hD.ψ_eq_one' hB hO, Complex.ofReal_one, mul_one] at this
    rw [this]
    simp [gfun, hsb]
  · have hK : m.1 ∉ B.K b := fun h ↦ hsb (hB.K_sub b h)
    rw [hB.Mset_apply_eq_zero hm hK]
    simp [gfun, hsb]

private lemma f_eq_of_some {a : A} {j : J} {k : Fin d} (h : B.c a j = some k) (y : Y) :
    B.f a j y = B.e a y k := by
  simp [BlowupData.f, h]

private lemma IsGood.continuousOn_yD (hD : D.IsGood) : ContinuousOn D.yD D.targetRaw :=
  (B.e D.a).continuousOn_symm.comp continuous_zD.continuousOn fun _ hv ↦ hv.2.1

private lemma IsGood.continuousOn_Wfun (hD : D.IsGood) (hB : B.IsGood) (j : J) :
    ContinuousOn (fun v ↦ D.Wfun v j) D.targetRaw := by
  by_cases hj : ∃ k, D.jOf k = some j
  · obtain ⟨k, hk⟩ := hj
    have : (fun v ↦ D.Wfun v j) = fun v ↦ circ (D.ω0 k) (v (finProdFinEquiv (k, 1))) :=
      funext fun v ↦ hD.Wfun_of_jOf hk v
    rw [this]
    exact ((continuous_circ _).comp (PiLp.continuous_apply 2 _ _)).continuousOn
  · push Not at hj
    have : (fun v ↦ D.Wfun v j) = fun v ↦ unitDir (B.f D.a j (D.yD v)) :=
      funext fun v ↦ Wfun_of_forall_ne hj v
    rw [this]
    exact continuousOn_unitDir ((B.continuousOn_f D.a j).comp hD.continuousOn_yD
      fun v hv ↦ hD.yD_mem_source hB hv) fun v hv ↦
        hB.f_ne_zero (hD.yD_mem_source hB hv) (hD.O_E j hj _ hv.2.2)

private lemma IsGood.continuousOn_Praw (hD : D.IsGood) (hB : B.IsGood) :
    ContinuousOn D.Praw D.targetRaw := by
  refine hD.continuousOn_yD.prodMk (continuousOn_pi.2 fun q ↦ ?_)
  exact ((continuousOn_gfun hB q.1 q.2).comp hD.continuousOn_yD
    fun v hv ↦ hD.yD_mem_source hB hv).mul (hD.continuousOn_Wfun hB q.2)

private lemma IsGood.Praw_mem_graph (hD : D.IsGood) (hB : B.IsGood)
    {v : EuclideanSpace ℝ (Fin (d * 2))} (hv : v ∈ D.targetRaw)
    (hpos : ∀ k j, D.jOf k = some j → 0 < v (finProdFinEquiv (k, 0))) : D.Praw v ∈ B.graph := by
  have hya := hD.yD_mem_source hB hv
  have hW : ∀ j, D.Wfun v j = unitDir (B.f D.a j (D.yD v)) := by
    intro j
    by_cases hj : ∃ k, D.jOf k = some j
    · obtain ⟨k, hk⟩ := hj
      rw [hD.Wfun_of_jOf hk, f_eq_of_some (hD.jOf_c k j hk), e_yD hv, zD_of_some hk,
        unitDir_ofReal_mul (hpos k j hk),
        unitDir_of_norm_eq_one (norm_circ (hD.norm_ω0 k j hk) (hv.1 k j hk).le)]
    · push Not at hj; exact Wfun_of_forall_ne hj v
  refine ⟨?_, funext fun q ↦ ?_⟩
  · simp only [Eall, mem_iUnion, not_exists]
    intro j hj
    by_cases hj' : ∃ k, D.jOf k = some j
    · obtain ⟨k, hk⟩ := hj'
      have h0 := (hB.c_some D.a j k (hD.jOf_c k j hk) _ hya).1 hj
      rw [e_yD hv, zD_of_some hk] at h0
      have hn := norm_circ (hD.norm_ω0 k j hk) (hv.1 k j hk).le
      rcases mul_eq_zero.1 h0 with h | h
      · exact (hpos k j hk).ne' (by exact_mod_cast h)
      · rw [h, norm_zero] at hn; exact zero_ne_one hn
    · push Not at hj'; exact hD.O_E j hj' _ hv.2.2 hj
  · obtain ⟨b, j⟩ := q
    change D.gfun b j (D.yD v) * D.Wfun v j = B.Φ (D.yD v) (b, j)
    rw [hW j]
    simp only [Φ, gfun]
    split_ifs with hb
    · rw [(hB.u_spec j hya hb).1, unitDir_mul]; ring
    · have hK : D.yD v ∉ B.K b := fun h ↦ hb (hB.K_sub b h)
      simp [hB.ψ_eq_zero b _ hK]

private lemma IsGood.Praw_mem (hD : D.IsGood) (hB : B.IsGood)
    {v : EuclideanSpace ℝ (Fin (d * 2))} (hv : v ∈ D.targetRaw) (hq : ∀ i, 0 ≤ v i) :
    D.Praw v ∈ B.Mset := by
  set δ : EuclideanSpace ℝ (Fin (d * 2)) :=
    WithLp.toLp 2 fun i ↦ if (finProdFinEquiv.symm i).2 = 0 then 1 else 0 with hδ
  have hc : Continuous fun t : ℝ ↦ v + t • δ := by fun_prop
  have hlim : Tendsto (fun t : ℝ ↦ v + t • δ) (𝓝[>] 0) (𝓝 v) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun t : ℝ ↦ D.Praw (v + t • δ)) (𝓝[>] 0) (𝓝 (D.Praw v)) :=
    ((hD.continuousOn_Praw hB).continuousAt (hD.isOpen_targetRaw.mem_nhds hv)).tendsto.comp hlim
  refine mem_closure_of_tendsto hP ?_
  filter_upwards [hlim (hD.isOpen_targetRaw.mem_nhds hv), self_mem_nhdsWithin] with t ht htpos
  refine hD.Praw_mem_graph hB ht fun k j hk ↦ ?_
  have : (v + t • δ) (finProdFinEquiv (k, 0)) = v (finProdFinEquiv (k, 0)) + t := by
    simp only [PiLp.add_apply, PiLp.smul_apply, hδ, PiLp.toLp_apply, Equiv.symm_apply_apply,
      smul_eq_mul]
    simp
  rw [this]
  have := hq (finProdFinEquiv (k, 0))
  have ht0 : 0 < t := htpos
  linarith

private lemma abs_im_conj_mul_lt {η w : ℂ} (hη : ‖η‖ = 1) (hw : ‖w‖ = 1)
    (hre : 0 < (starRingEnd ℂ η * w).re) : |(starRingEnd ℂ η * w).im| < 1 := by
  set v := starRingEnd ℂ η * w with hv
  have hvn : ‖v‖ = 1 := by simp [hv, hη, hw]
  have h := Complex.sq_norm_sub_sq_re v
  rw [hvn] at h
  have : v.im ^ 2 < 1 := by nlinarith
  exact (sq_lt_one_iff_abs_lt_one _).1 this

private lemma re_conj_mul_circ {η : ℂ} (hη : ‖η‖ = 1) (t : ℝ) :
    (starRingEnd ℂ η * circ η t).re = √(1 - (t - 1) ^ 2) := by
  rw [circ, ← mul_assoc, conj_mul_self_of_norm_eq_one hη, one_mul]
  simp

private lemma IsGood.abs_coord_lt (hD : D.IsGood) (hB : B.IsGood)
    {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset) (hO : m.1 ∈ D.O)
    (hre : ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.2 (D.a, j)).re)
    {k : Fin d} {j : J} (h : D.jOf k = some j) : |D.coord m k 1 - 1| < 1 := by
  rw [(coord_of_some h m).2, add_sub_cancel_left]
  refine abs_im_conj_mul_lt (hD.norm_ω0 k j h) ?_ (hre k j h)
  rw [hB.norm_Mset_apply hm j (hD.mem_source hB hO), hD.ψ_eq_one' hB hO]

private lemma IsGood.raw_nonneg (hD : D.IsGood) (hB : B.IsGood)
    {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset) (hO : m.1 ∈ D.O)
    (hre : ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.2 (D.a, j)).re) (i) :
    0 ≤ D.raw m i := by
  obtain ⟨⟨k, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [raw_apply]
  cases h : D.jOf k with
  | some j =>
    fin_cases s
    · simp only [Fin.zero_eta]; rw [(coord_of_some h m).1]; exact norm_nonneg _
    · simp only [Fin.mk_one]
      have := abs_lt.1 (hD.abs_coord_lt hB hm hO hre h)
      linarith
  | none =>
    have ht := hD.O_tan k h _ hO
    fin_cases s
    · simp only [Fin.zero_eta]; rw [(coord_of_none h m).1]
      have := Complex.abs_re_le_norm (B.e D.a m.1 k - D.z0 k)
      have := (abs_le.1 this).1
      linarith
    · simp only [Fin.mk_one]; rw [(coord_of_none h m).2]
      have := Complex.abs_im_le_norm (B.e D.a m.1 k - D.z0 k)
      have := (abs_le.1 this).1
      linarith

private lemma IsGood.raw_mem_targetRaw (hD : D.IsGood) (hB : B.IsGood)
    {m : Y × (A × J → ℂ)} (hm : m ∈ B.Mset) (hO : m.1 ∈ D.O)
    (hre : ∀ k j, D.jOf k = some j → 0 < (starRingEnd ℂ (D.ω0 k) * m.2 (D.a, j)).re) :
    D.raw m ∈ D.targetRaw := by
  have hz := hD.zD_raw hB hm hO hre
  refine ⟨fun k j h ↦ ?_, ?_, ?_⟩
  · rw [raw_apply]; exact hD.abs_coord_lt hB hm hO hre h
  · rw [hz]; exact (B.e D.a).map_source (hD.mem_source hB hO)
  · rw [yD, hz, (B.e D.a).left_inv (hD.mem_source hB hO)]; exact hO

private lemma IsGood.Praw_mem_sourceSet (hD : D.IsGood) (hB : B.IsGood)
    {v : EuclideanSpace ℝ (Fin (d * 2))} (hv : v ∈ D.targetRaw) :
    (D.Praw v).1 ∈ D.O ∧ ∀ k j, D.jOf k = some j →
      0 < (starRingEnd ℂ (D.ω0 k) * (D.Praw v).2 (D.a, j)).re := by
  refine ⟨hv.2.2, fun k j h ↦ ?_⟩
  change 0 < (starRingEnd ℂ (D.ω0 k) * (D.gfun D.a j (D.yD v) * D.Wfun v j)).re
  rw [hD.gfun_self hB j hv.2.2, one_mul, hD.Wfun_of_jOf h, re_conj_mul_circ (hD.norm_ω0 k j h)]
  have h1 := hv.1 k j h
  have : (v (finProdFinEquiv (k, 1)) - 1) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).2 h1
  exact Real.sqrt_pos.2 (by linarith)

private lemma continuousOn_coord (k : Fin d) (s : Fin 2) :
    ContinuousOn (fun p : Y × (A × J → ℂ) ↦ D.coord p k s) {p | p.1 ∈ (B.e D.a).source} := by
  have he : ContinuousOn (fun p : Y × (A × J → ℂ) ↦ B.e D.a p.1 k) {p | p.1 ∈ (B.e D.a).source} :=
    (continuous_apply k).comp_continuousOn
      ((B.e D.a).continuousOn.comp continuous_fst.continuousOn fun _ h ↦ h)
  unfold coord
  cases D.jOf k with
  | some j =>
    split_ifs
    · exact he.norm
    · exact continuousOn_const.add (Complex.continuous_im.comp_continuousOn
        (continuousOn_const.mul ((continuous_apply _).comp continuous_snd).continuousOn))
  | none =>
    split_ifs
    · exact continuousOn_const.add (Complex.continuous_re.comp_continuousOn (he.sub continuousOn_const))
    · exact continuousOn_const.add (Complex.continuous_im.comp_continuousOn (he.sub continuousOn_const))

private lemma IsGood.isOpen_sourceSet (hD : D.IsGood) : IsOpen D.sourceSet :=
  ((hD.isOpen_O.preimage continuous_fst).inter (isOpen_setOf_forall_eq_some D.jOf
    (P := fun k j (p : Y × (A × J → ℂ)) ↦ 0 < (starRingEnd ℂ (D.ω0 k) * p.2 (D.a, j)).re)
    fun _ _ _ ↦ isOpen_lt continuous_const (by fun_prop))).preimage continuous_subtype_val

/-- The polar chart of the blow-up defined by good chart data. -/
private noncomputable def IsGood.chart (hD : D.IsGood) (hB : B.IsGood) :
    OpenPartialHomeomorph B.Mset (EuclideanQuadrant (d * 2)) where
  toFun m := (modelWithCornersEuclideanQuadrant (d * 2)).symm (D.raw m.1)
  invFun x := open Classical in if h : D.Praw x.1 ∈ B.Mset then ⟨D.Praw x.1, h⟩ else D.base
  source := D.sourceSet
  target := {x | x.1 ∈ D.targetRaw}
  map_source' := by
    intro m hm
    change (modelWithCornersEuclideanQuadrant (d * 2)).symm (D.raw m.1) ∈ {x | x.1 ∈ D.targetRaw}
    rw [modelWithCornersEuclideanQuadrant_symm_apply_of_le (hD.raw_nonneg hB m.2 hm.1 hm.2)]
    exact hD.raw_mem_targetRaw hB m.2 hm.1 hm.2
  map_target' := by
    intro x hx
    have hmem := hD.Praw_mem hB hx x.2
    simp only [dif_pos hmem]
    exact hD.Praw_mem_sourceSet hB hx
  left_inv' := by
    intro m hm
    have hm' : m.1.1 ∈ D.O ∧ ∀ k j, D.jOf k = some j →
        0 < (starRingEnd ℂ (D.ω0 k) * m.1.2 (D.a, j)).re := hm
    have hr : (modelWithCornersEuclideanQuadrant (d * 2)).symm (D.raw m.1) =
        ⟨D.raw m.1, hD.raw_nonneg hB m.2 hm'.1 hm'.2⟩ :=
      modelWithCornersEuclideanQuadrant_symm_apply_of_le _
    have h := hD.Praw_raw hB m.2 hm'.1 hm'.2
    split_ifs with h1
    · apply Subtype.ext
      change D.Praw ((modelWithCornersEuclideanQuadrant (d * 2)).symm (D.raw m.1)).1 = m.1
      rw [hr]
      exact h
    · exfalso
      apply h1
      rw [hr]
      change D.Praw (D.raw m.1) ∈ B.Mset
      rw [h]
      exact m.2
  right_inv' := by
    intro x hx
    have hmem := hD.Praw_mem hB hx x.2
    simp only [dif_pos hmem]
    rw [hD.raw_Praw hB hx x.2]
    exact (modelWithCornersEuclideanQuadrant (d * 2)).left_inv x
  open_source := hD.isOpen_sourceSet
  open_target := hD.isOpen_targetRaw.preimage continuous_subtype_val
  continuousOn_toFun := by
    refine (modelWithCornersEuclideanQuadrant (d * 2)).continuous_symm.comp_continuousOn ?_
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i ↦ ?_)
    exact (D.continuousOn_coord _ _).comp continuous_subtype_val.continuousOn
      fun m hm ↦ hD.mem_source hB hm.1
  continuousOn_invFun := by
    classical
    rw [continuousOn_iff_continuous_restrict]
    refine Continuous.congr (f := fun x : {x : EuclideanQuadrant (d * 2) // x.1 ∈ D.targetRaw} ↦
      (⟨D.Praw x.1.1, hD.Praw_mem hB x.2 x.1.2⟩ : B.Mset)) ?_ ?_
    · refine Continuous.subtype_mk ?_ _
      exact (hD.continuousOn_Praw hB).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) fun x ↦ x.2
    · intro x
      change _ = (if h : D.Praw x.1.1 ∈ B.Mset then (⟨D.Praw x.1.1, h⟩ : B.Mset) else D.base)
      rw [dif_pos (hD.Praw_mem hB x.2 x.1.2)]

private lemma IsGood.chart_apply (hD : D.IsGood) (hB : B.IsGood) {m : B.Mset}
    (hm : m ∈ D.sourceSet) : ((hD.chart hB) m).1 = D.raw m.1 := by
  have hm' : m.1.1 ∈ D.O ∧ ∀ k j, D.jOf k = some j →
      0 < (starRingEnd ℂ (D.ω0 k) * m.1.2 (D.a, j)).re := hm
  change ((modelWithCornersEuclideanQuadrant (d * 2)).symm (D.raw m.1)).1 = _
  rw [modelWithCornersEuclideanQuadrant_symm_apply_of_le (hD.raw_nonneg hB m.2 hm'.1 hm'.2)]

private lemma IsGood.chart_symm_apply (hD : D.IsGood) (hB : B.IsGood)
    {x : EuclideanQuadrant (d * 2)} (hx : x.1 ∈ D.targetRaw) :
    ((hD.chart hB).symm x).1 = D.Praw x.1 := by
  classical
  change ((if h : D.Praw x.1 ∈ B.Mset then (⟨D.Praw x.1, h⟩ : B.Mset) else D.base) : B.Mset).1 = _
  rw [dif_pos (hD.Praw_mem hB hx x.2)]

variable (D) in
private lemma contDiffAt_zD {x : EuclideanSpace ℝ (Fin (d * 2))}
    (hx : ∀ k j, D.jOf k = some j → |x (finProdFinEquiv (k, 1)) - 1| < 1) :
    ContDiffAt ℝ ∞ D.zD x := by
  rw [contDiffAt_pi]
  intro k
  cases h : D.jOf k with
  | some j =>
    have : (fun x ↦ D.zD x k) = fun x : EuclideanSpace ℝ (Fin (d * 2)) ↦
        (x (finProdFinEquiv (k, 0)) : ℂ) * circ (D.ω0 k) (x (finProdFinEquiv (k, 1))) :=
      funext fun x ↦ zD_of_some h x
    rw [this]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_piLp_apply 2)).mul
      (ContDiffAt.comp (g := circ (D.ω0 k)) x (contDiffAt_circ _ (hx k j h))
              (contDiffAt_piLp_apply 2))
  | none =>
    have : (fun x ↦ D.zD x k) = fun x : EuclideanSpace ℝ (Fin (d * 2)) ↦
        D.z0 k + (((x (finProdFinEquiv (k, 0)) - 1 : ℝ) : ℂ) +
          ((x (finProdFinEquiv (k, 1)) - 1 : ℝ) : ℂ) * Complex.I) :=
      funext fun x ↦ zD_of_none h x
    rw [this]
    exact contDiffAt_const.add ((Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((contDiffAt_piLp_apply 2).sub contDiffAt_const)).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp x
          ((contDiffAt_piLp_apply 2).sub contDiffAt_const)).mul contDiffAt_const))

/-! ### Transition maps -/

/-- The coordinates of chart `D'`, as functions of the coordinates of chart `D`. -/
private noncomputable def tz (D D' : B.ChartData) (x : EuclideanSpace ℝ (Fin (d * 2))) :
    Fin d → ℂ :=
  B.e D'.a ((B.e D.a).symm (D.zD x))

open Classical in
/-- The transition map from chart `D` to chart `D'`, in coordinates. -/
private noncomputable def gcoord (D D' : B.ChartData) (x : EuclideanSpace ℝ (Fin (d * 2)))
    (k' : Fin d) (s : Fin 2) : ℝ :=
  match D'.jOf k' with
  | some j =>
    if h : ∃ k, D.jOf k = some j then
      if s = 0 then x (finProdFinEquiv (h.choose, 0)) * ‖B.Ufun D.a D'.a h.choose k' (D.zD x)‖
      else 1 + (starRingEnd ℂ (D'.ω0 k') * (unitDir (B.Ufun D.a D'.a h.choose k' (D.zD x)) *
        circ (D.ω0 h.choose) (x (finProdFinEquiv (h.choose, 1))))).im
    else
      if s = 0 then ‖tz D D' x k'‖
      else 1 + (starRingEnd ℂ (D'.ω0 k') * unitDir (tz D D' x k')).im
  | none =>
    if s = 0 then 1 + (tz D D' x k' - D'.z0 k').re else 1 + (tz D D' x k' - D'.z0 k').im

private lemma IsGood.gcoord_of_some_some (hD : D.IsGood) (D' : B.ChartData) {k k' : Fin d}
    {j : J} (h' : D'.jOf k' = some j) (hk : D.jOf k = some j) (x : EuclideanSpace ℝ (Fin (d * 2))) :
    gcoord D D' x k' 0 = x (finProdFinEquiv (k, 0)) * ‖B.Ufun D.a D'.a k k' (D.zD x)‖ ∧
    gcoord D D' x k' 1 = 1 + (starRingEnd ℂ (D'.ω0 k') * (unitDir (B.Ufun D.a D'.a k k' (D.zD x)) *
        circ (D.ω0 k) (x (finProdFinEquiv (k, 1))))).im := by
  have h : ∃ k, D.jOf k = some j := ⟨k, hk⟩
  have hck : h.choose = k := hD.jOf_unique h.choose_spec hk
  simp only [gcoord, h', dif_pos h, hck]
  simp

private lemma gcoord_of_some_none (D' : B.ChartData) {k' : Fin d} {j : J}
    (h' : D'.jOf k' = some j) (hk : ∀ k, D.jOf k ≠ some j) (x : EuclideanSpace ℝ (Fin (d * 2))) :
    gcoord D D' x k' 0 = ‖tz D D' x k'‖ ∧
    gcoord D D' x k' 1 = 1 + (starRingEnd ℂ (D'.ω0 k') * unitDir (tz D D' x k')).im := by
  have h : ¬ ∃ k, D.jOf k = some j := fun ⟨k, hk'⟩ ↦ hk k hk'
  simp only [gcoord, h', dif_neg h]
  simp

private lemma gcoord_of_none (D' : B.ChartData) {k' : Fin d} (h' : D'.jOf k' = none)
    (x : EuclideanSpace ℝ (Fin (d * 2))) :
    gcoord D D' x k' 0 = 1 + (tz D D' x k' - D'.z0 k').re ∧
    gcoord D D' x k' 1 = 1 + (tz D D' x k' - D'.z0 k').im := by
  simp [gcoord, h']

private lemma IsGood.coord_Praw (hD : D.IsGood) (hB : B.IsGood) {D' : B.ChartData}
    (hD' : D'.IsGood) {x : EuclideanSpace ℝ (Fin (d * 2))} (hx : x ∈ D.targetRaw)
    (hq : ∀ i, 0 ≤ x i) (hy' : D.yD x ∈ D'.O) (k' : Fin d) (s : Fin 2) :
    D'.coord (D.Praw x) k' s = gcoord D D' x k' s := by
  have hya := hD.yD_mem_source hB hx
  have hya' := hD'.mem_source hB hy'
  have hψ' := hD'.ψ_eq_one' hB hy'
  have htz : tz D D' x = B.e D'.a (D.yD x) := rfl
  cases h' : D'.jOf k' with
  | some j =>
    have hc' := hD'.jOf_c k' j h'
    have hw : (D.Praw x).2 (D'.a, j) = unitDir (B.u D.a D'.a j (D.yD x)) * D.Wfun x j := by
      change D.gfun D'.a j (D.yD x) * D.Wfun x j = _
      simp [gfun, hya', hψ']
    by_cases h : ∃ k, D.jOf k = some j
    · obtain ⟨k, hk⟩ := h
      have hc := hD.jOf_c k j hk
      have hu : B.u D.a D'.a j (D.yD x) = B.Ufun D.a D'.a k k' (D.zD x) := by
        simp [u, hc, hc', e_yD hx]
      have hg := hD.gcoord_of_some_some D' h' hk x
      fin_cases s
      · simp only [Fin.zero_eta]
        rw [(coord_of_some h' _).1, hg.1]
        change ‖B.e D'.a (D.yD x) k'‖ = _
        obtain ⟨-, -, heq⟩ := hB.Ufun_spec hc hc'
        have := heq (D.zD x) ⟨hx.2.1, hya'⟩
        rw [show B.e D'.a (D.yD x) k' = (B.e D'.a ∘ (B.e D.a).symm) (D.zD x) k' from rfl, this,
          norm_mul, zD_of_some hk, norm_mul, norm_circ (hD.norm_ω0 k j hk) (hx.1 k j hk).le,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq _)]
      · simp only [Fin.mk_one]
        rw [(coord_of_some h' _).2, hg.2, hw, hu, hD.Wfun_of_jOf hk]
    · push Not at h
      have hg := gcoord_of_some_none D' h' h x
      fin_cases s
      · simp only [Fin.zero_eta]
        rw [(coord_of_some h' _).1, hg.1, htz]
        rfl
      · simp only [Fin.mk_one]
        rw [(coord_of_some h' _).2, hg.2, hw, Wfun_of_forall_ne h, ← unitDir_mul,
          ← (hB.u_spec j hya hya').1, f_eq_of_some hc', htz]
  | none =>
    have hg := gcoord_of_none (D := D) D' h' x
    fin_cases s
    · simp only [Fin.zero_eta]; rw [(coord_of_none h' _).1, hg.1, htz]; rfl
    · simp only [Fin.mk_one]; rw [(coord_of_none h' _).2, hg.2, htz]; rfl

private lemma IsGood.contDiffAt_gcoord (hD : D.IsGood) (hB : B.IsGood) {D' : B.ChartData}
    (hD' : D'.IsGood) {x : EuclideanSpace ℝ (Fin (d * 2))} (hx : x ∈ D.targetRaw)
    (hy' : D.yD x ∈ D'.O) (k' : Fin d) (s : Fin 2) :
    ContDiffAt ℝ ∞ (fun x ↦ gcoord D D' x k' s) x := by
  have hya' := hD'.mem_source hB hy'
  have hz : D.zD x ∈ B.dom D.a D'.a := ⟨hx.2.1, hya'⟩
  have hzD := D.contDiffAt_zD hx.1
  have hτ : ∀ k', ContDiffAt ℝ ∞ (fun x ↦ tz D D' x k') x := by
    intro k'
    have hd : DifferentiableOn ℂ (fun z ↦ (B.e D'.a ∘ (B.e D.a).symm) z k') (B.dom D.a D'.a) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k').differentiable.comp_differentiableOn
        (hB.differentiableOn D.a D'.a)
    exact (contDiffAt_of_differentiableOn hd (B.isOpen_dom _ _) hz).comp x hzD
  cases h' : D'.jOf k' with
  | some j =>
    have hc' := hD'.jOf_c k' j h'
    by_cases h : ∃ k, D.jOf k = some j
    · obtain ⟨k, hk⟩ := h
      have hc := hD.jOf_c k j hk
      obtain ⟨hUd, hU0, -⟩ := hB.Ufun_spec hc hc'
      have hU : ContDiffAt ℝ ∞ (fun x ↦ B.Ufun D.a D'.a k k' (D.zD x)) x :=
        (contDiffAt_of_differentiableOn hUd (B.isOpen_dom _ _) hz).comp x hzD
      have hg := hD.gcoord_of_some_some D' h' hk
      fin_cases s
      · simp only [Fin.zero_eta]
        rw [show (fun x ↦ gcoord D D' x k' 0) = fun x ↦ x (finProdFinEquiv (k, 0)) *
          ‖B.Ufun D.a D'.a k k' (D.zD x)‖ from funext fun x ↦ (hg x).1]
        exact (contDiffAt_piLp_apply 2).mul (hU.norm ℝ (hU0 _ hz))
      · simp only [Fin.mk_one]
        rw [show (fun x ↦ gcoord D D' x k' 1) = fun x ↦ 1 + (starRingEnd ℂ (D'.ω0 k') *
          (unitDir (B.Ufun D.a D'.a k k' (D.zD x)) *
            circ (D.ω0 k) (x (finProdFinEquiv (k, 1))))).im from funext fun x ↦ (hg x).2]
        exact contDiffAt_const.add (Complex.imCLM.contDiff.contDiffAt.comp x
          (contDiffAt_const.mul ((contDiffAt_unitDir hU (hU0 _ hz)).mul
            (ContDiffAt.comp (g := circ (D.ω0 k)) x (contDiffAt_circ _ (hx.1 k j hk))
              (contDiffAt_piLp_apply 2)))))
    · push Not at h
      have hne : tz D D' x k' ≠ 0 := by
        intro h0
        have hyE : D.yD x ∈ B.E j := (hB.c_some D'.a j k' hc' _ hya').2 h0
        exact hD.O_E j h _ hx.2.2 hyE
      have hg := gcoord_of_some_none D' h' h
      fin_cases s
      · simp only [Fin.zero_eta]
        rw [show (fun x ↦ gcoord D D' x k' 0) = fun x ↦ ‖tz D D' x k'‖ from
          funext fun x ↦ (hg x).1]
        exact (hτ k').norm ℝ hne
      · simp only [Fin.mk_one]
        rw [show (fun x ↦ gcoord D D' x k' 1) = fun x ↦
          1 + (starRingEnd ℂ (D'.ω0 k') * unitDir (tz D D' x k')).im from
          funext fun x ↦ (hg x).2]
        exact contDiffAt_const.add (Complex.imCLM.contDiff.contDiffAt.comp x
          (contDiffAt_const.mul (contDiffAt_unitDir (hτ k') hne)))
  | none =>
    have hg := gcoord_of_none (D := D) D' h'
    fin_cases s
    · simp only [Fin.zero_eta]
      rw [show (fun x ↦ gcoord D D' x k' 0) = fun x ↦ 1 + (tz D D' x k' - D'.z0 k').re from
        funext fun x ↦ (hg x).1]
      exact contDiffAt_const.add (Complex.reCLM.contDiff.contDiffAt.comp x
        ((hτ k').sub contDiffAt_const))
    · simp only [Fin.mk_one]
      rw [show (fun x ↦ gcoord D D' x k' 1) = fun x ↦ 1 + (tz D D' x k' - D'.z0 k').im from
        funext fun x ↦ (hg x).2]
      exact contDiffAt_const.add (Complex.imCLM.contDiff.contDiffAt.comp x
        ((hτ k').sub contDiffAt_const))

/-- **Smooth transitions.** The transition maps between polar charts are smooth. -/
private lemma IsGood.contDiffOn_transition (hD : D.IsGood) (hB : B.IsGood)
    {D' : B.ChartData} (hD' : D'.IsGood) :
    ContDiffOn ℝ ∞ (modelWithCornersEuclideanQuadrant (d * 2) ∘
      ((hD.chart hB).symm ≫ₕ hD'.chart hB) ∘ (modelWithCornersEuclideanQuadrant (d * 2)).symm)
      ((modelWithCornersEuclideanQuadrant (d * 2)).symm ⁻¹'
        ((hD.chart hB).symm ≫ₕ hD'.chart hB).source ∩
        range (modelWithCornersEuclideanQuadrant (d * 2))) := by
  set I := modelWithCornersEuclideanQuadrant (d * 2)
  set G : EuclideanSpace ℝ (Fin (d * 2)) → EuclideanSpace ℝ (Fin (d * 2)) := fun x ↦
    WithLp.toLp 2 fun i ↦ gcoord D D' x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  -- unpacking a point of the domain
  have hpt : ∀ x ∈ I.symm ⁻¹' ((hD.chart hB).symm ≫ₕ hD'.chart hB).source ∩ range I,
      x ∈ D.targetRaw ∧ (∀ i, 0 ≤ x i) ∧ D.yD x ∈ D'.O ∧ (I.symm x).1 = x ∧
      ((hD.chart hB).symm (I.symm x)) ∈ D'.sourceSet := by
    rintro x ⟨hx1, ⟨q, rfl⟩⟩
    rw [mem_preimage, OpenPartialHomeomorph.trans_source] at hx1
    have hIq : I.symm (I q) = q := I.left_inv q
    rw [hIq] at hx1 ⊢
    have hqt : q.1 ∈ D.targetRaw := hx1.1
    have hsrc : (hD.chart hB).symm q ∈ D'.sourceSet := hx1.2
    have hval := hD.chart_symm_apply hB hqt
    have hO : ((hD.chart hB).symm q).1.1 ∈ D'.O := hsrc.1
    rw [hval] at hO
    exact ⟨hqt, q.2, hO, rfl, hsrc⟩
  refine ContDiffOn.congr (f := G) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨hxt, -, hy', -, -⟩ := hpt x hx
    refine ContDiffAt.contDiffWithinAt ?_
    refine contDiffAt_piLp' 2 fun i ↦ ?_
    exact hD.contDiffAt_gcoord hB hD' hxt hy' _ _
  · obtain ⟨hxt, hq, hy', hIx, hsrc⟩ := hpt x hx
    change ((hD'.chart hB) ((hD.chart hB).symm (I.symm x))).1 = G x
    rw [hD'.chart_apply hB hsrc, hD.chart_symm_apply hB (by rw [hIx]; exact hxt), hIx]
    ext i
    obtain ⟨⟨k', s⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [raw_apply, hD.coord_Praw hB hD' hxt hq hy']
    simp only [G, PiLp.toLp_apply, Equiv.symm_apply_apply]

end ChartData

/-! ### The charts centred at the points of the blow-up -/

section PointCharts

variable [Finite J]

/-- The chart of `Y` used at a point of the blow-up. -/
private noncomputable def IsGood.pa (hB : B.IsGood) (m : B.Mset) : A := (hB.cover m.1.1).choose

open Classical in
/-- The faces through a point of the blow-up, indexed by their coordinates. -/
private noncomputable def IsGood.pjOf (hB : B.IsGood) (m : B.Mset) (k : Fin d) : Option J :=
  if h : ∃ j, m.1.1 ∈ B.E j ∧ B.c (hB.pa m) j = some k then some h.choose else none

private lemma IsGood.pjOf_eq_some_iff (hB : B.IsGood) (m : B.Mset) (k : Fin d) (j : J) :
    hB.pjOf m k = some j ↔ m.1.1 ∈ B.E j ∧ B.c (hB.pa m) j = some k := by
  classical
  unfold pjOf
  constructor
  · intro h
    split_ifs at h with h'
    · cases h
      exact h'.choose_spec
  · intro h
    have h' : ∃ j, m.1.1 ∈ B.E j ∧ B.c (hB.pa m) j = some k := ⟨j, h⟩
    rw [dif_pos h', hB.c_inj _ _ _ _ h'.choose_spec.2 h.2]

private lemma IsGood.mem_W_pa (hB : B.IsGood) (m : B.Mset) : m.1.1 ∈ B.W (hB.pa m) :=
  (hB.cover m.1.1).choose_spec

/-- The polar chart data centred at a point of the blow-up. -/
private noncomputable def IsGood.pointData (hB : B.IsGood) (m : B.Mset) : B.ChartData where
  a := hB.pa m
  jOf := hB.pjOf m
  z0 := B.e (hB.pa m) m.1.1
  ω0 := fun k ↦ match hB.pjOf m k with
    | some j => m.1.2 (hB.pa m, j)
    | none => 1
  O := B.W (hB.pa m) ∩ {y' | ∀ j, m.1.1 ∉ B.E j → y' ∉ B.E j} ∩
    ((B.e (hB.pa m)).source ∩ B.e (hB.pa m) ⁻¹'
      {z | ∀ k, hB.pjOf m k = none → ‖z k - B.e (hB.pa m) m.1.1 k‖ < 1})
  base := m

private lemma IsGood.pointData_ω0 (hB : B.IsGood) (m : B.Mset) {k : Fin d} {j : J}
    (h : hB.pjOf m k = some j) : (hB.pointData m).ω0 k = m.1.2 (hB.pa m, j) := by
  simp [pointData, h]

private lemma IsGood.pointData_isGood (hB : B.IsGood) (m : B.Mset) : (hB.pointData m).IsGood where
  isOpen_O := by
    refine ((hB.isOpen_W _).inter ?_).inter ?_
    · have : {y' | ∀ j, m.1.1 ∉ B.E j → y' ∉ B.E j} = ⋂ j, {y' | m.1.1 ∉ B.E j → y' ∉ B.E j} := by
        ext; simp
      rw [this]
      refine isOpen_iInter_of_finite fun j ↦ ?_
      by_cases hy : m.1.1 ∈ B.E j
      · simp [hy]
      · simp only [hy, not_false_eq_true, forall_const]
        exact (hB.isClosed_E j).isOpen_compl
    · refine (B.e (hB.pa m)).isOpen_inter_preimage ?_
      have : {z : Fin d → ℂ | ∀ k, hB.pjOf m k = none → ‖z k - B.e (hB.pa m) m.1.1 k‖ < 1} =
          ⋂ k, {z | hB.pjOf m k = none → ‖z k - B.e (hB.pa m) m.1.1 k‖ < 1} := by
        ext; simp
      rw [this]
      refine isOpen_iInter_of_finite fun k ↦ ?_
      by_cases hk : hB.pjOf m k = none
      · simp only [hk, forall_const]
        exact isOpen_lt (((continuous_apply k).sub continuous_const).norm) continuous_const
      · simp [hk]
  O_sub := fun _ hy ↦ hy.1.1
  jOf_c := fun k j h ↦ ((hB.pjOf_eq_some_iff m k j).1 h).2
  norm_ω0 := fun k j h ↦ by
    change ‖(hB.pointData m).ω0 k‖ = 1
    rw [hB.pointData_ω0 m h, hB.norm_Mset_apply m.2 j (hB.W_sub _ (hB.mem_W_pa m)),
      hB.ψ_eq_one _ _ (hB.mem_W_pa m)]
  O_E := fun j hj y' hy' ↦ by
    refine hy'.1.2 j fun hyE ↦ ?_
    have hsrc := hB.W_sub _ (hB.mem_W_pa m)
    cases hc : B.c (hB.pa m) j with
    | none => exact (hB.c_none _ j hc).subset ⟨hyE, hsrc⟩
    | some k => exact hj k ((hB.pjOf_eq_some_iff m k j).2 ⟨hyE, hc⟩)
  O_tan := fun k hk y' hy' ↦ hy'.2.2 k hk

private lemma IsGood.mem_pointData_sourceSet (hB : B.IsGood) (m : B.Mset) :
    m ∈ (hB.pointData m).sourceSet := by
  refine ⟨⟨⟨hB.mem_W_pa m, fun _ h ↦ h⟩, hB.W_sub _ (hB.mem_W_pa m), fun k _ ↦ by simp⟩,
    fun k j h ↦ ?_⟩
  change 0 < (starRingEnd ℂ ((hB.pointData m).ω0 k) * m.1.2 (hB.pa m, j)).re
  rw [hB.pointData_ω0 m h, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, hB.norm_Mset_apply m.2 j (hB.W_sub _ (hB.mem_W_pa m)),
    hB.ψ_eq_one _ _ (hB.mem_W_pa m)]
  norm_num

/-- The coordinates of a point in its own chart vanish exactly at the radii of the faces through
it. -/
private lemma IsGood.pointData_raw_eq_zero_iff (hB : B.IsGood) (m : B.Mset) (k : Fin d)
    (s : Fin 2) : (hB.pointData m).raw m.1 (finProdFinEquiv (k, s)) = 0 ↔
      s = 0 ∧ ∃ j, hB.pjOf m k = some j := by
  rw [ChartData.raw_apply]
  have hsrc := hB.W_sub _ (hB.mem_W_pa m)
  cases h : hB.pjOf m k with
  | some j =>
    have h' : (hB.pointData m).jOf k = some j := h
    obtain ⟨hyE, hc⟩ := (hB.pjOf_eq_some_iff m k j).1 h
    fin_cases s
    · simp only [Fin.zero_eta, true_and]
      rw [(ChartData.coord_of_some h' _).1]
      change ‖B.e (hB.pa m) m.1.1 k‖ = 0 ↔ _
      rw [(hB.c_some _ j k hc _ hsrc).1 hyE, norm_zero]
      simp
    · simp only [Fin.mk_one]
      rw [(ChartData.coord_of_some h' _).2]
      change 1 + (starRingEnd ℂ ((hB.pointData m).ω0 k) * m.1.2 (hB.pa m, j)).im = 0 ↔ _
      rw [hB.pointData_ω0 m h, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
      simp
  | none =>
    have h' : (hB.pointData m).jOf k = none := h
    fin_cases s
    · simp only [Fin.zero_eta]
      rw [(ChartData.coord_of_none h' _).1]
      change 1 + (B.e (hB.pa m) m.1.1 k - B.e (hB.pa m) m.1.1 k).re = 0 ↔ _
      simp
    · simp only [Fin.mk_one]
      rw [(ChartData.coord_of_none h' _).2]
      change 1 + (B.e (hB.pa m) m.1.1 k - B.e (hB.pa m) m.1.1 k).im = 0 ↔ _
      simp

/-- The charted space structure of the blow-up. -/
@[instance_reducible]
private noncomputable def IsGood.chartedSpace (hB : B.IsGood) :
    ChartedSpace (EuclideanQuadrant (d * 2)) B.Mset where
  atlas := range fun m ↦ (hB.pointData_isGood m).chart hB
  chartAt m := (hB.pointData_isGood m).chart hB
  mem_chart_source m := hB.mem_pointData_sourceSet m
  chart_mem_atlas m := ⟨m, rfl⟩

private lemma IsGood.isManifold (hB : B.IsGood) :
    @IsManifold ℝ _ _ _ _ _ _ (modelWithCornersEuclideanQuadrant (d * 2)) ∞ B.Mset _
      hB.chartedSpace := by
  letI := hB.chartedSpace
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
  obtain ⟨m, rfl⟩ := he
  obtain ⟨m', rfl⟩ := he'
  exact (hB.pointData_isGood m).contDiffOn_transition hB (hB.pointData_isGood m')

private lemma IsGood.mem_boundary_iff (hB : B.IsGood) (m : B.Mset) :
    m ∈ @ModelWithCorners.boundary ℝ _ _ _ _ _ _ (modelWithCornersEuclideanQuadrant (d * 2))
      B.Mset _ hB.chartedSpace ↔ m.1.1 ∈ B.Eall := by
  letI := hB.chartedSpace
  change (modelWithCornersEuclideanQuadrant (d * 2)).IsBoundaryPoint m ↔ _
  rw [MMP.Topology.isBoundaryPoint_iff_exists_extChartAt_eq_zero]
  have hx : extChartAt (modelWithCornersEuclideanQuadrant (d * 2)) m m =
      (hB.pointData m).raw m.1 := by
    rw [extChartAt_coe]
    change ((hB.pointData_isGood m).chart hB m).1 = _
    exact (hB.pointData_isGood m).chart_apply hB (hB.mem_pointData_sourceSet m)
  rw [hx]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨⟨k, s⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨-, j, hj⟩ := (hB.pointData_raw_eq_zero_iff m k s).1 hi
    exact mem_iUnion.2 ⟨j, ((hB.pjOf_eq_some_iff m k j).1 hj).1⟩
  · intro hm
    obtain ⟨j, hj⟩ := mem_iUnion.1 hm
    have hsrc := hB.W_sub _ (hB.mem_W_pa m)
    cases hc : B.c (hB.pa m) j with
    | none => exact ((hB.c_none _ j hc).subset ⟨hj, hsrc⟩).elim
    | some k =>
      exact ⟨finProdFinEquiv (k, 0), (hB.pointData_raw_eq_zero_iff m k 0).2
        ⟨rfl, j, (hB.pjOf_eq_some_iff m k j).2 ⟨hj, hc⟩⟩⟩

private lemma IsGood.exists_c (hB : B.IsGood) (m : B.Mset) {j : J} (hj : m.1.1 ∈ B.E j) :
    ∃ k, B.c (hB.pa m) j = some k := by
  cases hc : B.c (hB.pa m) j with
  | none => exact ((hB.c_none _ j hc).subset ⟨hj, hB.W_sub _ (hB.mem_W_pa m)⟩).elim
  | some k => exact ⟨k, rfl⟩

/-- Every point of the blow-up has an atlas chart in which the faces through it are cut out
by distinct coordinates vanishing at it. -/
private lemma IsGood.exists_chart_faces (hB : B.IsGood) (x : B.Mset) :
    ∃ e ∈ @atlas (EuclideanQuadrant (d * 2)) _ B.Mset _ hB.chartedSpace, x ∈ e.source ∧
      ∃ σ : {j // x ∈ {m : B.Mset | m.1.1 ∈ B.E j}} ≃ {k : Fin (d * 2) // (e x).1 k = 0},
        ∀ j, {m : B.Mset | m.1.1 ∈ B.E j} ∩ e.source = {z | z ∈ e.source ∧
          ∃ hj : x ∈ {m : B.Mset | m.1.1 ∈ B.E j}, (e z).1 (σ ⟨j, hj⟩) = 0} := by
  classical
  letI := hB.chartedSpace
  set D := hB.pointData x
  have hD := hB.pointData_isGood x
  have hxs := hB.mem_pointData_sourceSet x
  have hex : ∀ z : B.Mset, z ∈ D.sourceSet → ((hD.chart hB) z).1 = D.raw z.1 :=
    fun z hz ↦ hD.chart_apply hB hz
  -- the coordinate of a face through `x`
  let kOf : {j // x.1.1 ∈ B.E j} → Fin d := fun j ↦ (hB.exists_c x j.2).choose
  have hkOf : ∀ j, B.c (hB.pa x) j.1 = some (kOf j) := fun j ↦ (hB.exists_c x j.2).choose_spec
  have hjOf : ∀ j, D.jOf (kOf j) = some j.1 :=
    fun j ↦ (hB.pjOf_eq_some_iff x _ _).2 ⟨j.2, hkOf j⟩
  have hzero : ∀ j, ((hD.chart hB) x).1 (finProdFinEquiv (kOf j, 0)) = 0 := by
    intro j
    rw [hex x hxs]
    exact (hB.pointData_raw_eq_zero_iff x _ 0).2 ⟨rfl, j.1, hjOf j⟩
  let σf : {j // x.1.1 ∈ B.E j} → {i : Fin (d * 2) // ((hD.chart hB) x).1 i = 0} :=
    fun j ↦ ⟨finProdFinEquiv (kOf j, 0), hzero j⟩
  have hσ : Function.Bijective σf := by
    constructor
    · intro j₁ j₂ h
      have h1 : kOf j₁ = kOf j₂ := by
        have := congrArg (fun i : {i : Fin (d * 2) // ((hD.chart hB) x).1 i = 0} ↦
          (finProdFinEquiv.symm i.1).1) h
        simpa [σf] using this
      exact Subtype.ext (hB.c_inj _ _ _ _ (hkOf j₁) (h1 ▸ hkOf j₂))
    · rintro ⟨i, hi⟩
      obtain ⟨⟨k, s⟩, rfl⟩ := finProdFinEquiv.surjective i
      rw [hex x hxs] at hi
      obtain ⟨rfl, j, hj⟩ := (hB.pointData_raw_eq_zero_iff x k s).1 hi
      obtain ⟨hjE, hc⟩ := (hB.pjOf_eq_some_iff x k j).1 hj
      refine ⟨⟨j, hjE⟩, Subtype.ext ?_⟩
      have : kOf ⟨j, hjE⟩ = k := Option.some_injective _ ((hkOf ⟨j, hjE⟩).symm.trans hc)
      simp [σf, this]
  refine ⟨(hD.chart hB), ⟨x, rfl⟩, hxs, Equiv.ofBijective σf hσ, fun j ↦ ?_⟩
  ext z
  simp only [mem_inter_iff, mem_setOf_eq, Equiv.ofBijective_apply]
  constructor
  · rintro ⟨hzE, hzs⟩
    have hzs' : z ∈ D.sourceSet := hzs
    have hxE : x.1.1 ∈ B.E j := by_contra fun hxE ↦ hzs'.1.1.2 j hxE hzE
    refine ⟨hzs, hxE, ?_⟩
    rw [hex z hzs']
    simp only [σf, ChartData.raw_apply]
    rw [(ChartData.coord_of_some (hjOf ⟨j, hxE⟩) _).1]
    have hsrc : z.1.1 ∈ (B.e (hB.pa x)).source := hD.mem_source hB hzs'.1
    change ‖B.e (hB.pa x) z.1.1 (kOf ⟨j, hxE⟩)‖ = 0
    rw [(hB.c_some _ j _ (hkOf ⟨j, hxE⟩) _ hsrc).1 hzE, norm_zero]
  · rintro ⟨hzs, hxE, h0⟩
    have hzs' : z ∈ D.sourceSet := hzs
    refine ⟨?_, hzs⟩
    rw [hex z hzs'] at h0
    simp only [σf, ChartData.raw_apply] at h0
    rw [(ChartData.coord_of_some (hjOf ⟨j, hxE⟩) _).1, norm_eq_zero] at h0
    have h0' : B.e (hB.pa x) z.1.1 (kOf ⟨j, hxE⟩) = 0 := h0
    exact (hB.c_some _ j _ (hkOf ⟨j, hxE⟩) _ (hD.mem_source hB hzs'.1)).2 h0'

/-- **The real oriented blow-up.** Good blow-up data give a compact Hausdorff smooth manifold
with corners, with embedded boundary hypersurfaces, and a map to `Y` which is a bijection of the
interior onto `Y ∖ E` and whose boundary is the inverse image of `E`. -/
private theorem IsGood.exists_manifold [CompactSpace Y] [T2Space Y] (hB : B.IsGood) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanQuadrant (d * 2)) M)
      (_ : IsManifold (modelWithCornersEuclideanQuadrant (d * 2)) ∞ M)
      (_ : CompactSpace M) (_ : T2Space M),
      (∃ (J' : Type) (_ : Finite J') (F : J' → Set M), (∀ j, IsClosed (F j)) ∧
        ∀ x : M, ∃ e ∈ atlas (EuclideanQuadrant (d * 2)) M, x ∈ e.source ∧
          ∃ σ : {j // x ∈ F j} ≃ {k : Fin (d * 2) // (e x).1 k = 0},
            ∀ j, F j ∩ e.source = {z | z ∈ e.source ∧ ∃ hj : x ∈ F j, (e z).1 (σ ⟨j, hj⟩) = 0}) ∧
      ∃ β : C(M, Y), β ⁻¹' B.Eall = (modelWithCornersEuclideanQuadrant (d * 2)).boundary M ∧
        Set.InjOn β ((modelWithCornersEuclideanQuadrant (d * 2)).boundary M)ᶜ ∧
        B.Eallᶜ ⊆ β '' ((modelWithCornersEuclideanQuadrant (d * 2)).boundary M)ᶜ := by
  classical
  letI := hB.chartedSpace
  haveI : CompactSpace B.Mset := isCompact_iff_compactSpace.1 hB.isCompact_Mset
  have hβ : Continuous fun m : B.Mset ↦ m.1.1 := continuous_fst.comp continuous_subtype_val
  refine ⟨B.Mset, inferInstance, hB.chartedSpace, hB.isManifold, inferInstance, inferInstance,
    ⟨J, inferInstance, fun j ↦ {m : B.Mset | m.1.1 ∈ B.E j},
      fun j ↦ (hB.isClosed_E j).preimage hβ, hB.exists_chart_faces⟩,
    ⟨⟨fun m ↦ m.1.1, hβ⟩, ?_, ?_, ?_⟩⟩
  · ext m
    exact (hB.mem_boundary_iff m).symm
  · intro m hm m' hm' h
    have h1 : m.1.1 ∉ B.Eall := fun h' ↦ hm ((hB.mem_boundary_iff m).2 h')
    have h2 : m'.1.1 ∉ B.Eall := fun h' ↦ hm' ((hB.mem_boundary_iff m').2 h')
    have h : m.1.1 = m'.1.1 := h
    refine Subtype.ext (Prod.ext h ?_)
    rw [hB.Mset_eq_Φ m.2 h1, hB.Mset_eq_Φ m'.2 h2, h]
  · intro y hy
    refine ⟨⟨(y, B.Φ y), subset_closure ⟨hy, rfl⟩⟩, fun hb ↦ hy ((hB.mem_boundary_iff _).1 hb), rfl⟩

end PointCharts

end BlowupData

/-- **The real oriented blow-up along a simple normal crossings divisor.** Let `Y` be a compact
Hausdorff space with a holomorphic atlas of dimension `d` (holomorphic transition maps) adapted
to closed subsets `E j`: in every chart each `E j` is either disjoint from the domain or the zero
locus of one coordinate, distinct `E j` using distinct coordinates. Passing to polar coordinates
`z_k = r_k e^{iθ_k}` in the coordinates cutting out the `E j` gives a compact Hausdorff smooth
manifold with corners `M`, modelled on `[0, ∞)^{2d}`, with embedded boundary hypersurfaces, and
a continuous `β : M → Y` such that `β⁻¹(⋃ E j) = ∂M` and `β` maps `M ∖ ∂M` bijectively onto
`Y ∖ ⋃ E j`. -/
private theorem exists_realOrientedBlowup_of_atlas {Y : Type} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] (d : ℕ) {J : Type} [Finite J] (E : J → Set Y)
    (hE : ∀ j, IsClosed (E j)) (Ach : Set (OpenPartialHomeomorph Y (Fin d → ℂ)))
    (hcov : ∀ y, ∃ e ∈ Ach, y ∈ e.source)
    (hdiff : ∀ e ∈ Ach, ∀ e' ∈ Ach,
      DifferentiableOn ℂ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source))
    (hadapt : ∀ e ∈ Ach, ∃ c : J → Option (Fin d),
      (∀ j j' k, c j = some k → c j' = some k → j = j') ∧
      (∀ j, c j = none → E j ∩ e.source = ∅) ∧
      ∀ j k, c j = some k → ∀ y ∈ e.source, y ∈ E j ↔ e y k = 0) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanQuadrant (d * 2)) M)
      (_ : IsManifold (modelWithCornersEuclideanQuadrant (d * 2)) ∞ M)
      (_ : CompactSpace M) (_ : T2Space M),
      (∃ (J' : Type) (_ : Finite J') (F : J' → Set M), (∀ j, IsClosed (F j)) ∧
        ∀ x : M, ∃ e ∈ atlas (EuclideanQuadrant (d * 2)) M, x ∈ e.source ∧
          ∃ σ : {j // x ∈ F j} ≃ {k : Fin (d * 2) // (e x).1 k = 0},
            ∀ j, F j ∩ e.source = {z | z ∈ e.source ∧ ∃ hj : x ∈ F j, (e z).1 (σ ⟨j, hj⟩) = 0}) ∧
      ∃ β : C(M, Y), β ⁻¹' (⋃ j, E j) = (modelWithCornersEuclideanQuadrant (d * 2)).boundary M ∧
        Set.InjOn β ((modelWithCornersEuclideanQuadrant (d * 2)).boundary M)ᶜ ∧
        (⋃ j, E j)ᶜ ⊆ β '' ((modelWithCornersEuclideanQuadrant (d * 2)).boundary M)ᶜ := by
  classical
  choose ey hey hyey using hcov
  choose cy hcy using fun y ↦ hadapt (ey y) (hey y)
  -- nested neighbourhoods `y ∈ W y ⊆ closure (W y) ⊆ V y ⊆ closure (V y) ⊆ (ey y).source`
  have hV : ∀ y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ closure V ⊆ (ey y).source := fun y ↦ by
    obtain ⟨V, hVo, hyV, hVc⟩ := normal_exists_closure_subset isClosed_singleton
      (ey y).open_source (singleton_subset_iff.2 (hyey y))
    exact ⟨V, hVo, hyV rfl, hVc⟩
  choose V hVo hyV hVc using hV
  have hW : ∀ y, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ closure W ⊆ V y := fun y ↦ by
    obtain ⟨W, hWo, hyW, hWc⟩ := normal_exists_closure_subset isClosed_singleton
      (hVo y) (singleton_subset_iff.2 (hyV y))
    exact ⟨W, hWo, hyW rfl, hWc⟩
  choose W hWo hyW hWc using hW
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ ↦ mem_iUnion.2 ⟨y, hyW y⟩
  -- cut-offs
  have hψ : ∀ y, ∃ ψ : C(Y, ℝ), EqOn ψ 0 (V y)ᶜ ∧ EqOn ψ 1 (closure (W y)) ∧
      ∀ x, ψ x ∈ Icc (0 : ℝ) 1 := fun y ↦
    exists_continuous_zero_one_of_isClosed (hVo y).isClosed_compl isClosed_closure
      (disjoint_compl_left_iff_subset.2 (hWc y))
  choose ψ hψ0 hψ1 hψI using hψ
  let B : BlowupData Y d J t :=
    { E := E
      e := fun a ↦ ey a.1
      c := fun a ↦ cy a.1
      W := fun a ↦ W a.1
      K := fun a ↦ closure (V a.1)
      ψ := fun a ↦ ψ a.1 }
  have hB : B.IsGood :=
    { isClosed_E := hE
      differentiableOn := fun a b ↦ hdiff _ (hey a.1) _ (hey b.1)
      c_inj := fun a ↦ (hcy a.1).1
      c_none := fun a ↦ (hcy a.1).2.1
      c_some := fun a ↦ (hcy a.1).2.2
      isOpen_W := fun a ↦ hWo a.1
      cover := fun y ↦ by
        obtain ⟨a, ha, hya⟩ := mem_iUnion₂.1 (ht (mem_univ y))
        exact ⟨⟨a, ha⟩, hya⟩
      isClosed_K := fun _ ↦ isClosed_closure
      K_sub := fun a ↦ hVc a.1
      continuous_ψ := fun a ↦ (ψ a.1).continuous
      ψ_eq_one := fun a y hy ↦ hψ1 a.1 (subset_closure hy)
      ψ_eq_zero := fun a y hy ↦ hψ0 a.1 fun h ↦ hy (subset_closure h)
      ψ_nonneg := fun a y ↦ (hψI a.1 y).1
      ψ_le_one := fun a y ↦ (hψI a.1 y).2 }
  exact hB.exists_manifold

section AlgebraicInput

open MMP.Analytic.ComplexPoints

section SNCCharts

open IsLocalRing TensorProduct KaehlerDifferential

/-- The point of `X` under a `ℂ`-point is closed: a section of `X → Spec ℂ` is a closed
immersion. -/
private theorem isClosed_singleton_toScheme {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (x : ComplexPoints sX) : IsClosed ({x.toScheme} : Set X) := by
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id sX x.hom x.2
  convert x.hom.isClosedEmbedding.isClosed_range using 1
  ext y
  constructor
  · rintro rfl; exact ⟨default, rfl⟩
  · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q default]; rfl

/-- Over a base change `R → R₀` with bijective structure map, differentials forming a basis of
`κ(B) ⊗ Ω[B⁄R]` also form a basis of `κ(B) ⊗ Ω[B⁄R₀]`. -/
private theorem isBasis_D_of_bijective_algebraMap {R R₀ B : Type*} [CommRing R] [CommRing R₀]
    [CommRing B] [IsLocalRing B] [Algebra R R₀] [Algebra R₀ B] [Algebra R B]
    [IsScalarTower R R₀ B] (hR : Function.Bijective (algebraMap R R₀)) {ι : Type*} (b : ι → B)
    (hli : LinearIndependent (ResidueField B)
      (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i)))
    (hsp : Submodule.span (ResidueField B)
      (Set.range (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i))) = ⊤) :
    LinearIndependent (ResidueField B)
      (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i)) ∧
    Submodule.span (ResidueField B)
      (Set.range (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i))) = ⊤ := by
  have : Algebra.FormallyEtale R R₀ :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R R₀) hR)
  have : Subsingleton Ω[R₀⁄R] := (Algebra.formallyUnramified_iff R R₀).mp inferInstance
  have hbij : Function.Bijective (KaehlerDifferential.map R R₀ B B) := by
    refine ⟨?_, KaehlerDifferential.map_surjective R R₀ B⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R₀ B x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  let e : Ω[B⁄R] ≃ₗ[B] Ω[B⁄R₀] := LinearEquiv.ofBijective (KaehlerDifferential.map R R₀ B B) hbij
  let e' := e.baseChange B (ResidueField B)
  have hcomp : (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i)) =
      e' ∘ (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i)) := by
    funext i
    change _ = (1 : ResidueField B) ⊗ₜ[B]
      KaehlerDifferential.map R R₀ B B (KaehlerDifferential.D R B (b i))
    rw [KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hcomp]
  refine ⟨hli.map' e'.toLinearMap (LinearEquiv.ker e'), ?_⟩
  rw [Set.range_comp, ← LinearEquiv.coe_coe, ← Submodule.map_span, hsp, Submodule.map_top,
    LinearEquiv.range]

/-- At a closed point of a smooth complex scheme, the differentials of a regular system of
parameters form a basis of the fibre `κ(p) ⊗ Ω_{𝒪_{X,p}/ℂ}`. -/
private theorem isBasis_D_stalk_of_isRegularSystemOfParameters {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [Smooth sX] (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ}
    (t : Fin n → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    let := MMP.Mori.stalkAlgebra sX p
    LinearIndependent (ResidueField (X.presheaf.stalk p))
      (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i)) ∧
    Submodule.span (ResidueField (X.presheaf.stalk p))
      (Set.range (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i))) = ⊤ := by
  classical
  let := MMP.Mori.stalkAlgebra sX p
  obtain ⟨_, _, _⟩ := MMP.Flips.ResolutionInputs.stalk_facts sX p
  have : Module.Finite ℂ (ResidueField (X.presheaf.stalk p)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX p hp
  have : Algebra.FormallyUnramified ℂ (ResidueField (X.presheaf.stalk p)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular t ht.1 ht.2
  exact ⟨MMP.Flips.ResolutionInputs.linearIndependent_tmul_D ℂ t ht0 hli,
    top_le_iff.mp (MMP.Flips.ResolutionInputs.span_tmul_D ℂ t ht.1)⟩

/-- The structure map from `ℂ` to the stalk of `Spec ℂ` at its point is bijective. -/
private theorem bijective_germ_comp_ΓSpecIso_inv (q : Spec (.of ℂ)) :
    Function.Bijective ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec (.of ℂ)).presheaf.germ ⊤ q trivial).hom := by
  refine ⟨RingHom.injective _, ?_⟩
  have hloc := (isAffineOpen_top (Spec (.of ℂ))).isLocalization_stalk ⟨q, trivial⟩
  have hu : ∀ y : ((isAffineOpen_top (Spec (.of ℂ))).primeIdealOf ⟨q, trivial⟩).asIdeal.primeCompl,
      IsUnit (y : Γ(Spec (.of ℂ), ⊤)) := by
    intro y
    have hy0 : (y : Γ(Spec (.of ℂ), ⊤)) ≠ 0 := fun h0 ↦ y.2 (h0 ▸ Ideal.zero_mem _)
    have : (Scheme.ΓSpecIso (.of ℂ)).hom (y : Γ(Spec (.of ℂ), ⊤)) ≠ 0 := by
      intro h; apply hy0
      rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of ℂ)) (y : Γ(Spec (.of ℂ), ⊤)), h, map_zero]
    have hU := (IsUnit.mk0 _ this).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
    rwa [Iso.hom_inv_id_apply] at hU
  let := TopCat.Presheaf.algebra_section_stalk (Spec (.of ℂ)).presheaf (U := ⊤) ⟨q, trivial⟩
  have hs := (IsLocalization.atUnits Γ(Spec (.of ℂ), ⊤) _ (S := (Spec (.of ℂ)).presheaf.stalk q)
    (fun y hy ↦ hu ⟨y, hy⟩)).surjective
  intro r
  obtain ⟨a, ha⟩ := hs r
  refine ⟨(Scheme.ΓSpecIso (.of ℂ)).hom a, ?_⟩
  rw [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply]
  exact ha

/-- At a closed point `p` of a smooth complex scheme, the differentials of a regular system of
parameters form a basis of `κ(p) ⊗ Ω[𝒪_{X,p} ⁄ 𝒪_{Spec ℂ, sX p}]`. -/
private theorem isBasis_D_stalk_base_of_isRegularSystemOfParameters {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [Smooth sX] (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ}
    (t : Fin n → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    let := (sX.stalkMap p).hom.toAlgebra
    LinearIndependent (ResidueField (X.presheaf.stalk p))
      (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (t i)) ∧
    Submodule.span (ResidueField (X.presheaf.stalk p))
      (Set.range (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (t i))) = ⊤ := by
  let := MMP.Mori.stalkAlgebra sX p
  let := (sX.stalkMap p).hom.toAlgebra
  let : Algebra ℂ ((Spec (.of ℂ)).presheaf.stalk (sX p)) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).presheaf.germ ⊤ (sX p) trivial).hom.toAlgebra
  have : IsScalarTower ℂ ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom =
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).presheaf.germ ⊤ (sX p)
        (TopologicalSpace.Opens.mem_top _) ≫ sX.stalkMap p).hom
    rw [Scheme.Hom.germ_stalkMap]
    rfl
  obtain ⟨hli, hsp⟩ := isBasis_D_stalk_of_isRegularSystemOfParameters sX p hp t ht
  exact isBasis_D_of_bijective_algebraMap (bijective_germ_comp_ΓSpecIso_inv (sX p)) t hli hsp

/-- **Étale coordinates adapted to a simple normal crossing divisor.** Let `X` be smooth of
relative dimension `n` over `ℂ` and `E = ∑_{E_i ∈ s} E_i` a simple normal crossing divisor on
`X`. Around every `x ∈ X(ℂ)` there are étale coordinates `z` on a Zariski open `U` such that the
components through `x` are the zero loci on `U(ℂ)` of distinct coordinates `z_{c i}`, and the
other components miss `U(ℂ)`. -/
private theorem exists_etale_coordinates_adapted_of_isSNC {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n sX]
    (s : Finset (MMP.Mori.PrimeDivisor X))
    (hs : MMP.Mori.DivisorWithCoeffs.IsSNC sX (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (x : ComplexPoints sX) :
    ∃ (U : X.Opens) (z : Fin n → Γ(X, U))
      (_ : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (_ : x ∈ chart U) (s' : Finset s) (c : s' ↪ Fin n),
        (∀ i ∉ s', {y : ComplexPoints sX | toScheme y ∈ i.1.support} ∩ chart U = ∅) ∧
        ∀ (i : s') (y : ComplexPoints sX) (hy : y ∈ chart U),
          toScheme y ∈ i.1.1.support ↔ eval U (z (c i)) ⟨y, hy⟩ = 0 := by
  classical
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : ∀ m, IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} m) := fun m ↦
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} m)
  have : SmoothOfRelativeDimension n ((⊤ : X.Opens).ι ≫ sX) := IsZariskiLocalAtSource.comp ‹_› _
  set p := toScheme x with hp
  have hsupp : ∀ E, E ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support ↔ E ∈ s := by
    intro E
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    by_cases hE : E ∈ s
    · rw [Finset.sum_eq_single E (fun b _ hb ↦ by rw [Finsupp.single_apply, if_neg hb])
        (fun h ↦ (h hE).elim), Finsupp.single_eq_same]
      exact ⟨fun _ ↦ hE, fun _ ↦ one_ne_zero⟩
    · rw [Finset.sum_eq_zero fun b hb ↦ by
        rw [Finsupp.single_apply, if_neg (fun h : b = E ↦ hE (h ▸ hb))]]
      exact ⟨fun h ↦ (h rfl).elim, fun h ↦ (hE h).elim⟩
  obtain ⟨m, t, j, ht, hj, hI⟩ := hs.2 p
  -- the components through `p`
  let s' : Finset s := s.attach.filter fun E ↦ p ∈ E.1.support
  have hs' : ∀ E : s, E ∈ s' ↔ p ∈ E.1.support := fun E ↦ by simp [s']
  let k := s'.card
  obtain ⟨e⟩ : Nonempty (Fin k ≃ s') := ⟨s'.equivFin.symm⟩
  let jE : s' → Fin m := fun E ↦ j ⟨E.1.1, (hsupp _).2 E.1.2, (hs' _).1 E.2⟩
  have hjE : Function.Injective jE := fun E E' h ↦
    Subtype.ext (Subtype.ext (by simpa only [Subtype.mk.injEq] using hj h))
  have hI' : ∀ E : s', IdealSheafData.stalk E.1.1.idealSheaf p = Ideal.span {t (jE E)} :=
    fun E ↦ hI ⟨E.1.1, (hsupp _).2 E.1.2, (hs' _).1 E.2⟩
  choose V hpV τ hτ hτV using fun l : Fin k ↦
    exists_mem_support_iff_notMem_basicOpen (e l).1.1.idealSheaf p (t (jE (e l))) (hI' (e l))
  -- a common neighbourhood
  have hev : ∀ᶠ q in 𝓝 p, (∀ l, q ∈ V l) ∧ (∀ E ∈ s, p ∉ E.support → q ∉ E.support) := by
    refine (Filter.eventually_all.2 fun l ↦ (V l).isOpen.mem_nhds (hpV l)).and ?_
    refine (Filter.eventually_all_finset s).2 fun E _ ↦ ?_
    by_cases hE : p ∈ E.support
    · exact Filter.Eventually.of_forall fun q h ↦ (h hE).elim
    · filter_upwards [E.idealSheaf.support.isClosed.isOpen_compl.mem_nhds hE] with q hq _
      exact hq
  obtain ⟨O, hOsub, hOo, hpO⟩ := mem_nhds_iff.1 hev
  let V₀ : X.Opens := ⟨O, hOo⟩
  have hV₀l : ∀ l, V₀ ≤ V l := fun l q hq ↦ (hOsub hq).1 l
  have hpV₀ : p ∈ V₀ := hpO
  let a : Fin k → Γ(X, V₀) := fun l ↦ X.presheaf.map (homOfLE (hV₀l l)).op (τ l)
  letI := (sX.stalkMap p).hom.toAlgebra
  have hgerm : (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
      D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
        (X.presheaf.germ V₀ p hpV₀ (a i))) =
      fun l ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
          D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p) (t (jE (e l))) := by
    funext l
    simp only [a]
    rw [X.presheaf.germ_res_apply, hτ l]
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk p)) fun i ↦
      (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ V₀ p hpV₀ (a i)) := by
    rw [hgerm]
    exact (isBasis_D_stalk_base_of_isRegularSystemOfParameters sX p
      (isClosed_singleton_toScheme x) t ht).1.comp _ (hjE.comp e.injective)
  obtain ⟨U, hpU, hUV, z, cc, hz, hzc⟩ :=
    exists_etale_coordinates_extending_of_mem (sX := sX) (n := n) ⊤ p trivial V₀ hpV₀ a hli
  refine ⟨U, z, hz, mem_chart_iff.2 hpU, s',
    ⟨fun E ↦ cc (e.symm E), fun E E' h ↦ e.symm.injective (cc.injective h)⟩,
    fun E hE ↦ ?_, fun E y hy ↦ ?_⟩
  · refine Set.eq_empty_of_forall_notMem fun y hy ↦ ?_
    have hyO : toScheme y ∈ O := hUV (mem_chart_iff.1 hy.2)
    exact (hOsub hyO).2 E.1 E.2 (fun h ↦ hE ((hs' E).2 h)) hy.1
  · change toScheme y ∈ (E : s).1.support ↔ _
    have hyU : toScheme y ∈ U := mem_chart_iff.1 hy
    have hkey := toScheme_mem_basicOpen_iff (sX := sX) ⟨y, hy⟩ (z (cc (e.symm E)))
    rw [evalHom_apply] at hkey
    change _ ↔ eval U (z (cc (e.symm E))) ⟨y, hy⟩ = 0
    rw [← not_iff_not, ← ne_eq, ← hkey, hzc, Scheme.basicOpen_res]
    simp only [a]
    rw [Scheme.basicOpen_res]
    have h1 := hτV (e.symm E) (toScheme y) (hV₀l _ (hUV hyU))
    rw [e.apply_symm_apply] at h1
    rw [show toScheme y ∈ U ⊓ (V₀ ⊓ X.basicOpen (τ (e.symm E))) ↔
        toScheme y ∈ X.basicOpen (τ (e.symm E)) from
          ⟨fun h ↦ h.2.2, fun h ↦ ⟨hyU, hUV hyU, h⟩⟩]
    exact ⟨fun h ↦ by_contra fun hb ↦ h (h1.2 hb), fun hb ha ↦ h1.1 ha hb⟩

/-- **A holomorphic atlas adapted to a simple normal crossing divisor.** On a scheme smooth of
relative dimension `n` over `ℂ`, the étale coordinate charts in which every component of a simple
normal crossing divisor either misses the chart or is the zero locus of a coordinate (distinct
components, distinct coordinates) cover `X^an` and have holomorphic transition maps. -/
private theorem exists_sncAtlas {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ}
    [SmoothOfRelativeDimension n sY] (s : Finset (MMP.Mori.PrimeDivisor Y))
    (hs : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ E ∈ s, Finsupp.single E (1 : ℤ))) :
    ∃ Ach : Set (OpenPartialHomeomorph (ComplexPoints sY) (Fin n → ℂ)),
      (∀ y, ∃ e ∈ Ach, y ∈ e.source) ∧
      (∀ e ∈ Ach, ∀ e' ∈ Ach,
        DifferentiableOn ℂ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source)) ∧
      ∀ e ∈ Ach, ∃ c : s → Option (Fin n),
        (∀ j j' k, c j = some k → c j' = some k → j = j') ∧
        (∀ j, c j = none → {y : ComplexPoints sY | toScheme y ∈ j.1.support} ∩ e.source = ∅) ∧
        ∀ j k, c j = some k → ∀ y ∈ e.source,
          y ∈ {y : ComplexPoints sY | toScheme y ∈ j.1.support} ↔ e y k = 0 := by
  classical
  let Good : OpenPartialHomeomorph (ComplexPoints sY) (Fin n → ℂ) → Prop := fun e ↦
    ∃ c : s → Option (Fin n),
      (∀ j j' k, c j = some k → c j' = some k → j = j') ∧
      (∀ j, c j = none → {y : ComplexPoints sY | toScheme y ∈ j.1.support} ∩ e.source = ∅) ∧
      ∀ j k, c j = some k → ∀ y ∈ e.source,
        y ∈ {y : ComplexPoints sY | toScheme y ∈ j.1.support} ↔ e y k = 0
  refine ⟨{e | (∃ c : EtaleCoordinateChart sY n, e = c.toOpenPartialHomeomorph) ∧ Good e},
    fun y ↦ ?_, ?_, fun e he ↦ he.2⟩
  · obtain ⟨U, z, hz, hy, s', cc, hnone, hsome⟩ := exists_etale_coordinates_adapted_of_isSNC (n := n) s hs y
    obtain ⟨W, hW, hWo, hyW, hemb⟩ := (etaleCoordinate_atlas_of_smooth sY (n := n)).2.1 U z hz y hy
    let c : EtaleCoordinateChart sY n := ⟨U, z, hz, W, hW, hWo, ⟨y, hyW⟩, hemb⟩
    refine ⟨c.toOpenPartialHomeomorph, ⟨⟨c, rfl⟩, fun j ↦ if h : j ∈ s' then some (cc ⟨j, h⟩)
      else none, ?_, ?_, ?_⟩, by rw [c.source_toOpenPartialHomeomorph]; exact hyW⟩
    · intro j j' k hj hj'
      by_cases h : j ∈ s'
      · by_cases h' : j' ∈ s'
        · simp only [h, h', dite_true, Option.some.injEq] at hj hj'
          exact congrArg Subtype.val (cc.injective (hj.trans hj'.symm))
        · simp [h'] at hj'
      · simp [h] at hj
    · intro j hj
      have h : j ∉ s' := fun h ↦ by simp [h] at hj
      rw [c.source_toOpenPartialHomeomorph]
      exact Set.eq_empty_of_forall_notMem fun y' hy' ↦
        (Set.eq_empty_iff_forall_notMem.1 (hnone j h)) y' ⟨hy'.1, hW hy'.2⟩
    · intro j k hj y' hy'
      have h : j ∈ s' := by by_contra h; simp [h] at hj
      simp only [h, dite_true, Option.some.injEq] at hj
      rw [c.source_toOpenPartialHomeomorph] at hy'
      rw [c.toOpenPartialHomeomorph_apply hy', ← hj]
      exact hsome ⟨j, h⟩ y' (hW hy')
  · rintro e ⟨⟨c, rfl⟩, -⟩ e' ⟨⟨c', rfl⟩, -⟩
    have h := (EtaleCoordinateChart.analyticOnNhd_transition c c').differentiableOn
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans] at h

end SNCCharts

/-! ### The components of `X` -/

section Components

/-- In a scheme whose stalk at `q` is a domain, `q` lies on only one irreducible component. -/
private theorem eq_of_mem_irreducibleComponents_of_isDomain {X : Scheme.{0}} {q : X}
    (hq : IsDomain (X.presheaf.stalk q)) {Z Z' : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hZ' : Z' ∈ irreducibleComponents X) (hqZ : q ∈ Z) (hqZ' : q ∈ Z') : Z = Z' := by
  let g : X := X.fromSpecStalk q (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk q))
  have key : ∀ W ∈ irreducibleComponents X, q ∈ W → W = closure {g} := by
    intro W hW hqW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hη : IsGenericPoint hW.1.genericPoint W := by
      have := hW.1.isGenericPoint_genericPoint_closure
      rwa [hWc.closure_eq] at this
    have h1 : hW.1.genericPoint ⤳ q := hη.specializes hqW
    obtain ⟨P, hP⟩ : hW.1.genericPoint ∈ Set.range (X.fromSpecStalk q) := by
      rwa [Scheme.range_fromSpecStalk]
    have h2 : g ⤳ hW.1.genericPoint := by
      rw [← hP]
      exact ((PrimeSpectrum.le_iff_specializes
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk q)) P).1 bot_le).map
          (X.fromSpecStalk q).continuous
    have hsub : W ⊆ closure {g} := by
      rw [← hη.def]
      exact closure_minimal (singleton_subset_iff.2 (specializes_iff_mem_closure.1 h2))
        isClosed_closure
    exact le_antisymm hsub (hW.2 isIrreducible_singleton.closure hsub)
  rw [key Z hZ hqZ, key Z' hZ' hqZ']

/-- The stalks of a scheme at its smooth points over `ℂ` are domains. -/
private theorem isDomain_stalk_of_mem_smoothLocus {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {q : X} (hq : q ∈ MMP.Mori.smoothLocus sX) : IsDomain (X.presheaf.stalk q) := by
  obtain ⟨U, hqU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.1 hq
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sX) ⟨q, hqU⟩
  have : IsDomain (U.toScheme.presheaf.stalk ⟨q, hqU⟩) := IsRegularLocalRing.isDomain _
  haveI := IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι ⟨q, hqU⟩
  exact Function.Injective.isDomain (U.ι.stalkMap ⟨q, hqU⟩).hom
    (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap ⟨q, hqU⟩)).1

/-- A point outside a closed set containing the singular locus lies on only one irreducible
component. -/
private theorem eq_of_mem_irreducibleComponents_of_notMem {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {S : Closeds X} (hSing : MMP.Mori.singularLocus sX ≤ S) {q : X}
    (hq : q ∉ S) {Z Z' : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hZ' : Z' ∈ irreducibleComponents X) (hqZ : q ∈ Z) (hqZ' : q ∈ Z') : Z = Z' :=
  eq_of_mem_irreducibleComponents_of_isDomain
    (isDomain_stalk_of_mem_smoothLocus (sX := sX) (by_contra fun h ↦ hq (hSing h))) hZ hZ' hqZ hqZ'

/-- Off a closed set containing the singular locus, an irreducible component is smooth. -/
private theorem mem_smoothLocus_of_mem_irreducibleComponents {X W : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    [IsReduced X] (S : Closeds X)
    (hSing : MMP.Mori.singularLocus sX ≤ S) (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (ι : W ⟶ X) [IsClosedImmersion ι] (hrange : Set.range ι = Z) (w : W) (hwS : ι w ∉ S) :
    w ∈ MMP.Mori.smoothLocus (ι ≫ sX) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  haveI : IsNoetherian X := ⟨⟩
  have hfin : (irreducibleComponents X).Finite := finite_irreducibleComponents_of_isNoetherian
  set others : Set X := ⋃ Z' ∈ {Z' | Z' ∈ irreducibleComponents X ∧ Z' ≠ Z}, Z'
  have hothers : IsClosed others :=
    (hfin.subset fun Z' h ↦ h.1).isClosed_biUnion fun Z' h ↦
      isClosed_of_mem_irreducibleComponents Z' h.1
  let V : X.Opens := ⟨((S : Set X) ∪ others)ᶜ, (S.isClosed.union hothers).isOpen_compl⟩
  have hwZ : ι w ∈ Z := hrange ▸ ⟨w, rfl⟩
  have hqV : ι w ∈ V := by
    change ι w ∉ (S : Set X) ∪ others
    rintro (h | h)
    · exact hwS h
    · obtain ⟨Z', ⟨hZ', hne⟩, hw'⟩ := mem_iUnion₂.1 h
      exact hne (eq_of_mem_irreducibleComponents_of_notMem hSing hwS hZ' hZ hw' hwZ)
  have hVZ : (V : Set X) ⊆ Z := by
    intro v hv
    by_cases h : irreducibleComponent v = Z
    · exact h ▸ mem_irreducibleComponent
    · exact absurd (Or.inr (mem_iUnion₂.2 ⟨irreducibleComponent v,
        ⟨irreducibleComponent_mem_irreducibleComponents v, h⟩, mem_irreducibleComponent⟩)) hv
  have hsmX : ι w ∈ MMP.Mori.smoothLocus sX := by_contra fun h ↦ hwS (hSing h)
  obtain ⟨U, hqU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.1 hsmX
  set V' : X.Opens := V ⊓ U
  have hV'sm : Smooth (V'.ι ≫ sX) := by
    rw [← X.homOfLE_ι (inf_le_right : V' ≤ U), Category.assoc]; infer_instance
  have hV'Z : (V' : Set X) ⊆ Set.range ι := fun v hv ↦ hrange ▸ hVZ hv.1
  haveI : Surjective (ι ∣_ V') := ⟨fun v ↦ by
    obtain ⟨u, hu⟩ := hV'Z v.2
    refine ⟨⟨u, show ι u ∈ V' from hu ▸ v.2⟩, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe ι V' _).trans hu⟩
  haveI : IsIso (ι ∣_ V') := isIso_of_isClosedImmersion_of_surjective _
  refine MMP.Mori.mem_smoothLocus_iff.2 ⟨ι ⁻¹ᵁ V', show ι w ∈ V' from ⟨hqV, hqU⟩, ?_⟩
  have : (ι ⁻¹ᵁ V').ι ≫ ι ≫ sX = (ι ∣_ V') ≫ V'.ι ≫ sX := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rw [this]
  infer_instance

/-- A morphism that is an isomorphism over `U` lifts every `ℂ`-point of `U`. -/
private theorem exists_comp_eq_of_isIso_morphismRestrict {Y W : Scheme.{0}} (f : Y ⟶ W)
    (U : W.Opens) [IsIso (f ∣_ U)] (x : Spec (.of ℂ) ⟶ W) (hx : Set.range x ⊆ Set.range U.ι) :
    ∃ y : Spec (.of ℂ) ⟶ Y, y ≫ f = x :=
  ⟨IsOpenImmersion.lift U.ι x hx ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι, by
    simp only [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      IsOpenImmersion.lift_fac]⟩

/-- A morphism that is an isomorphism over `U` is injective on `ℂ`-points over `U`. -/
private theorem eq_of_comp_eq_of_isIso_morphismRestrict {Y W : Scheme.{0}} (f : Y ⟶ W)
    (U : W.Opens) [IsIso (f ∣_ U)] {a b : Spec (.of ℂ) ⟶ Y} (hab : a ≫ f = b ≫ f)
    (ha : f (a default) ∈ U) : a = b := by
  have hmem : ∀ c : Spec (.of ℂ) ⟶ Y, f (c default) ∈ U →
      Set.range c ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro c h _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim u default]
    exact h
  have hb : f (b default) ∈ U := by
    rwa [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply]
  have h3 : IsOpenImmersion.lift (f ⁻¹ᵁ U).ι a (hmem a ha) ≫ (f ∣_ U) =
      IsOpenImmersion.lift (f ⁻¹ᵁ U).ι b (hmem b hb) ≫ (f ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, hab]
  rw [← IsOpenImmersion.lift_fac (f ⁻¹ᵁ U).ι a (hmem a ha),
    ← IsOpenImmersion.lift_fac (f ⁻¹ᵁ U).ι b (hmem b hb), (cancel_mono (f ∣_ U)).1 h3]

/-- A `ℂ`-point of `X` lying in a closed set `F` factors through the reduced subscheme on `F`. -/
private theorem exists_comp_vanishingIdeal_subschemeι_eq {X : Scheme.{0}} (F : Closeds X)
    (x : Spec (.of ℂ) ⟶ X) (hx : x default ∈ (F : Set X)) :
    ∃ x1 : Spec (.of ℂ) ⟶ (Scheme.IdealSheafData.vanishingIdeal F).subscheme,
      x1 ≫ (Scheme.IdealSheafData.vanishingIdeal F).subschemeι = x := by
  have hr : Set.range x ⊆ (F : Set X) := by
    rintro _ ⟨u, rfl⟩
    rw [Subsingleton.elim u default]
    exact hx
  have hker : Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal F).subschemeι ≤
      Scheme.Hom.ker x := by
    rw [Scheme.IdealSheafData.ker_subschemeι, x.ker_eq_vanishingIdeal_closure_range]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.closure_le.mpr hr)
  exact ⟨IsClosedImmersion.lift _ x hker, IsClosedImmersion.lift_fac _ _ _⟩

/-- If `f` is an isomorphism over an open `U` containing every point of `W` off `ι⁻¹ S`, then
every complex point of `X` off `S` that lifts along `ι` lifts along `f ≫ ι`. -/
private theorem exists_realize_eq_of_isIso_morphismRestrict {X W Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (f : Y ⟶ W) (ι : W ⟶ X)
    (hg : (f ≫ ι) ≫ sX = sY) (U : W.Opens) [IsIso (f ∣_ U)] (S : Set X)
    (hU : ∀ w, ι w ∉ S → w ∈ (U : Set W)) (x : ComplexPoints sX) (hxS : toScheme x ∉ S)
    (x1 : Spec (.of ℂ) ⟶ W) (hx1 : x1 ≫ ι = x.hom) :
    ∃ y : ComplexPoints sY, realize (f ≫ ι) hg y = x := by
  have hx1U : Set.range x1 ⊆ Set.range U.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim u default]
    refine hU _ fun h ↦ hxS ?_
    have : ι (x1 default) = toScheme x := by
      rw [← Scheme.Hom.comp_apply, hx1]
      rfl
    rwa [← this]
  obtain ⟨y0, hy0⟩ := exists_comp_eq_of_isIso_morphismRestrict f U x1 hx1U
  have hy0' : y0 ≫ (f ≫ ι) = x.hom := by rw [← Category.assoc, hy0, hx1]
  refine ⟨⟨y0, ?_⟩, ?_⟩
  · rw [← hg, ← Category.assoc, hy0']
    exact x.2
  · apply ComplexPoints.ext
    change y0 ≫ (f ≫ ι) = x.hom
    exact hy0'

/-- **Resolution of one component.** Let `Z` be an irreducible component of a reduced projective
complex scheme `X`, not contained in a closed set `S ⊇ Sing X`. Resolving `Z` and principalizing
the ideal of `S ∩ Z` gives a smooth projective `Y` with a map `g : Y → X` onto `Z` such that
`g⁻¹(S)` is the support of a simple normal crossing divisor and `g` is bijective on complex
points over `Z ∖ S`. -/
private theorem exists_componentResolution {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsReduced X] (hX : IsProjective sX) (S : Closeds X)
    (hSing : MMP.Mori.singularLocus sX ≤ S) (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (hZS : ¬ Z ⊆ S) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ X) (hg : g ≫ sX = sY) (n : ℕ)
      (_ : SmoothOfRelativeDimension n sY) (_ : IsProper sY)
      (s : Finset (MMP.Mori.PrimeDivisor Y)),
      MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ E ∈ s, Finsupp.single E (1 : ℤ)) ∧
      (⋃ E ∈ s, (E.support : Set Y)) = g ⁻¹' S ∧ Set.range g ⊆ Z ∧
      (∀ x : ComplexPoints sX, toScheme x ∈ Z → toScheme x ∉ S →
        ∃ y : ComplexPoints sY, realize g hg y = x) ∧
      (∀ y y' : ComplexPoints sY, g (toScheme y) ∉ S → realize g hg y = realize g hg y' →
        y = y') := by
  classical
  haveI : IsProper sX := hX.isProper
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  set F : Closeds X := ⟨Z, hZc⟩ with hF
  set I := Scheme.IdealSheafData.vanishingIdeal F with hI
  set ι := I.subschemeι with hι
  set sZ := ι ≫ sX
  haveI : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal F
  have hrange : Set.range ι = Z := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  haveI : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by rw [← hι, hrange]; exact hZ.1)
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI hZv : AlgebraicGeometry.IsVariety ℂ sZ := { toIsIntegral := inferInstance }
  -- the ideal of `S ∩ Z` in `Z`
  set T : Closeds I.subscheme := S.preimage ι.continuous with hT
  set J := Scheme.IdealSheafData.vanishingIdeal T with hJdef
  have hJsupp : (J.support : Set I.subscheme) = ι ⁻¹' S := by
    rw [hJdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hJ : J ≠ ⊥ := by
    intro h
    apply hZS
    have h1 : (J.support : Set I.subscheme) = univ := by
      rw [h, Scheme.IdealSheafData.support_bot]; rfl
    rw [hJsupp] at h1
    rw [← hrange]
    rintro _ ⟨w, rfl⟩
    exact (h1 ▸ mem_univ w : w ∈ ι ⁻¹' S)
  obtain ⟨Y, f, hYv, hfp, -, hYs, hiso, -, hsnc, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap sZ hZv J hJ
  -- `Z ∖ S` lies in the smooth locus of `Z`
  have hsm : J.support.compl ≤ MMP.Mori.smoothLocus sZ := by
    intro w hw
    refine mem_smoothLocus_of_mem_irreducibleComponents sX S hSing Z hZ ι hrange w fun h ↦ ?_
    apply hw
    change w ∈ (J.support : Set _)
    rw [hJsupp]
    exact h
  have hiso' : IsIso (f ∣_ J.support.compl) := by rwa [inf_eq_right.2 hsm] at hiso
  have hexc : MMP.Mori.exceptionalSet f ≤ (J.comap f).support := by
    intro y hy
    rw [Scheme.IdealSheafData.support_comap]
    by_contra h2
    exact hy (MMP.Mori.le_biregularLocus hiso' h2)
  rw [sup_eq_right.2 hexc] at hsnc
  set sY := f ≫ sZ
  haveI : Smooth sY := by
    haveI : LocallyOfFinitePresentation sY := inferInstance
    exact (MMP.Mori.isSmoothScheme_iff sY).1 hYs
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety ℂ sY
  haveI : SmoothOfRelativeDimension n sY := MMP.Intersection.smoothOfRelativeDimension_of_isVariety sY n hn
  haveI : IsProper f := hfp.isProper
  have hg : (f ≫ ι) ≫ sX = sY := Category.assoc _ _ _
  have hU : ∀ w, ι w ∉ (S : Set X) → w ∈ (J.support.compl : Set I.subscheme) := fun w hw ↦ by
    change w ∉ (J.support : Set I.subscheme)
    rw [hJsupp]
    exact hw
  have hpre : (J.comap f).support = (S.preimage (f ≫ ι).continuous) := by
    ext1
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hJsupp]
    rfl
  obtain ⟨s, hs1, hs2⟩ : ∃ s : Finset (MMP.Mori.PrimeDivisor Y),
      (⋃ E ∈ s, (E.support : Set Y)) = (f ≫ ι) ⁻¹' S ∧
      MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ E ∈ s, Finsupp.single E (1 : ℤ)) := by
    rcases hsnc with h | ⟨s, hs1, hs2⟩
    · refine ⟨∅, ?_, by simpa using MMP.Mori.DivisorWithCoeffs.isSNC_zero (R := ℤ) sY⟩
      have : ((J.comap f).support : Set Y) = ∅ := by rw [h]; rfl
      rw [hpre] at this
      simpa using this.symm
    · refine ⟨s, ?_, hs2⟩
      rw [hs1, hpre]; rfl
  refine ⟨Y, sY, f ≫ ι, hg, n, inferInstance, inferInstance, s, hs2, hs1, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    rw [← hrange]
    exact ⟨f y, rfl⟩
  · intro x hxZ hxS
    obtain ⟨x1, hx1⟩ : ∃ x1, x1 ≫ ι = x.hom :=
      exists_comp_vanishingIdeal_subschemeι_eq F x.hom hxZ
    exact exists_realize_eq_of_isIso_morphismRestrict f ι hg J.support.compl (S : Set X) hU x
      hxS x1 hx1
  · intro y y' hyS hyy'
    have h2 : y.hom ≫ f = y'.hom ≫ f := by
      rw [← cancel_mono ι]
      simpa only [Category.assoc, realize_hom] using congrArg ComplexPoints.hom hyy'
    ext1
    exact eq_of_comp_eq_of_isIso_morphismRestrict f J.support.compl h2 (hU (f (toScheme y)) hyS)

end Components

/-! ### The complex points of the resolutions -/

section Realized

/-- The complex realization of a scheme proper over `ℂ` is compact. -/
public theorem compactSpace_complexPoints {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [IsProper sZ] : CompactSpace (ComplexPoints sZ) := by
  letI : Z.Over (Spec (.of ℂ)) := ⟨sZ⟩
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  have : sZ.IsOver (Spec (.of ℂ)) := ⟨Category.comp_id sZ⟩
  have : LocallyOfFiniteType (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (𝟙 _) from inferInstance
  have hp := MMP.UnderlyingSpace.isProperMap_map (K := ℂ) sZ
  have : Subsingleton (MMP.UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    ⟨fun p q ↦ MMP.UnderlyingSpace.ext
      (((Category.comp_id _).symm.trans p.toHom_comp_over).trans
        ((Category.comp_id _).symm.trans q.toHom_comp_over).symm)⟩
  have hc : CompactSpace (MMP.UnderlyingSpace ℂ Z) :=
    ⟨by simpa using hp.isCompact_preimage (Set.subsingleton_univ.isCompact)⟩
  exact (homeomorphUnderlyingSpace (X := Z)).symm.compactSpace

private lemma toScheme_realize {Y X : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {sX : X ⟶ Spec (.of ℂ)} (g : Y ⟶ X) (hg : g ≫ sX = sY) (y : ComplexPoints sY) :
    toScheme (realize g hg y) = g (toScheme y) := by
  rfl

/-- **Resolution with principalization, realized.** For a reduced projective complex scheme `X`
and a closed `S ⊇ Sing X` containing no component, the analytic spaces of the resolutions of the
components of `X`, principalizing the ideal of `S`, are compact Hausdorff spaces with holomorphic
atlases adapted to the simple normal crossing divisors `E` over `S`, mapping continuously to
`X^an`, jointly injectively off `E` and onto `X^an ∖ S^an`. -/
private theorem exists_sncResolution_complexPoints {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsReduced X] (hX : IsProjective sX) (S : Closeds X) (hSing : MMP.Mori.singularLocus sX ≤ S)
    (hcomp : ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ (S : Set X)) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (Y : ι → Type) (_ : ∀ i, TopologicalSpace (Y i))
      (_ : ∀ i, CompactSpace (Y i)) (_ : ∀ i, T2Space (Y i)) (J : ι → Type)
      (_ : ∀ i, Finite (J i)) (E : ∀ i, J i → Set (Y i)) (_ : ∀ i j, IsClosed (E i j))
      (Ach : ∀ i, Set (OpenPartialHomeomorph (Y i) (Fin (d i) → ℂ))),
      (∀ i, (∀ y, ∃ e ∈ Ach i, y ∈ e.source) ∧
        (∀ e ∈ Ach i, ∀ e' ∈ Ach i,
          DifferentiableOn ℂ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source)) ∧
        ∀ e ∈ Ach i, ∃ c : J i → Option (Fin (d i)),
          (∀ j j' k, c j = some k → c j' = some k → j = j') ∧
          (∀ j, c j = none → E i j ∩ e.source = ∅) ∧
          ∀ j k, c j = some k → ∀ y ∈ e.source, y ∈ E i j ↔ e y k = 0) ∧
      ∃ p : ∀ i, C(Y i, ComplexPoints sX),
        (∀ i, p i ⁻¹' (toScheme ⁻¹' (S : Set X)) = ⋃ j, E i j) ∧
        (∀ i i' (y : Y i) (y' : Y i'), y ∉ ⋃ j, E i j → y' ∉ ⋃ j, E i' j →
          p i y = p i' y' → (⟨i, y⟩ : Σ i, Y i) = ⟨i', y'⟩) ∧
        (toScheme ⁻¹' (S : Set X))ᶜ ⊆ ⋃ i, Set.range (p i) := by
  classical
  haveI : IsProper sX := hX.isProper
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  haveI : IsNoetherian X := ⟨⟩
  have hfin : (irreducibleComponents X).Finite := finite_irreducibleComponents_of_isNoetherian
  letI : Fintype (irreducibleComponents X) := hfin.fintype
  choose Y sY g hg n hsm hpr s hsnc hpre hrg hsurj hinj using fun Z : irreducibleComponents X ↦
    exists_componentResolution sX hX S hSing Z.1 Z.2 (hcomp Z.1 Z.2)
  have hE : ∀ i (j : s i), IsClosed {y : ComplexPoints (sY i) | toScheme y ∈ j.1.support} :=
    fun i j ↦ j.1.idealSheaf.support.isClosed.preimage continuous_toScheme
  choose Ach hcov hdiff hadapt using fun i ↦ exists_sncAtlas (sY := sY i) (n := n i) (s i) (hsnc i)
  haveI : ∀ i, CompactSpace (ComplexPoints (sY i)) := fun i ↦ compactSpace_complexPoints (sY i)
  have hE' : ∀ i (y : ComplexPoints (sY i)),
      y ∈ ⋃ j : s i, {y : ComplexPoints (sY i) | toScheme y ∈ j.1.support} ↔
        g i (toScheme y) ∈ (S : Set X) := by
    intro i y
    rw [mem_iUnion]
    have := congrArg (fun T : Set (Y i) ↦ toScheme y ∈ T) (hpre i)
    simp only [mem_iUnion, mem_preimage, exists_prop] at this
    rw [← this]
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨j.1, j.2, hj⟩, fun ⟨j, hj, hj'⟩ ↦ ⟨⟨j, hj⟩, hj'⟩⟩
  refine ⟨irreducibleComponents X, inferInstance, n, fun i ↦ ComplexPoints (sY i),
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun i ↦ s i,
    fun _ ↦ inferInstance, fun i j ↦ {y | toScheme y ∈ j.1.support}, hE, Ach,
    fun i ↦ ⟨hcov i, hdiff i, hadapt i⟩,
    fun i ↦ ⟨realize (g i) (hg i), continuous_realize (g i) (hg i)⟩, ?_, ?_, ?_⟩
  · intro i
    ext y
    rw [hE' i y]
    change toScheme (realize (g i) (hg i) y) ∈ (S : Set X) ↔ _
    rw [toScheme_realize]
  · intro i i' y y' hy hy' h
    have hy1 : g i (toScheme y) ∉ (S : Set X) := fun h' ↦ hy ((hE' i y).2 h')
    have hy1' : g i' (toScheme y') ∉ (S : Set X) := fun h' ↦ hy' ((hE' i' y').2 h')
    have hq : toScheme (realize (g i) (hg i) y) = toScheme (realize (g i') (hg i') y') :=
      congrArg toScheme h
    rw [toScheme_realize, toScheme_realize] at hq
    have hii : i = i' := Subtype.ext (eq_of_mem_irreducibleComponents_of_notMem hSing hy1 i.2 i'.2
      (hrg i ⟨_, rfl⟩) (hq ▸ hrg i' ⟨_, rfl⟩))
    subst hii
    rw [hinj i y y' hy1 h]
  · intro x hx
    have hxS : toScheme x ∉ (S : Set X) := hx
    obtain ⟨y, hy⟩ := hsurj ⟨irreducibleComponent (toScheme x),
      irreducibleComponent_mem_irreducibleComponents _⟩ x mem_irreducibleComponent hxS
    exact mem_iUnion.2 ⟨_, y, hy⟩

end Realized

end AlgebraicInput

/-- The real oriented blow-up of the resolutions of the components of `X` along the divisor over
`S`: a finite disjoint union of compact smooth manifolds with corners with embedded boundary
hypersurfaces, mapping continuously to `X^an`, with boundary exactly the preimage of `S^an`,
injective on the interior, and reaching every point outside `S^an`. -/
private theorem exists_realOrientedBlowup
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsReduced X] (hX : IsProjective sX)
    (S : Closeds X) (hSing : MMP.Mori.singularLocus sX ≤ S)
    (hcomp : ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ (S : Set X)) :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (M : ι → Type)
      (_ : ∀ i, TopologicalSpace (M i)) (_ : ∀ i, ChartedSpace (EuclideanQuadrant (n i)) (M i))
      (_ : ∀ i, IsManifold (modelWithCornersEuclideanQuadrant (n i)) ∞ (M i))
      (_ : ∀ i, CompactSpace (M i)) (_ : ∀ i, T2Space (M i)),
      (∀ i, ∃ (J : Type) (_ : Finite J) (F : J → Set (M i)), (∀ j, IsClosed (F j)) ∧
        ∀ x : M i, ∃ e ∈ atlas (EuclideanQuadrant (n i)) (M i), x ∈ e.source ∧
          ∃ σ : {j // x ∈ F j} ≃ {k : Fin (n i) // (e x).1 k = 0},
            ∀ j, F j ∩ e.source = {z | z ∈ e.source ∧ ∃ hj : x ∈ F j, (e z).1 (σ ⟨j, hj⟩) = 0}) ∧
      ∃ κ : C(Σ i, M i, ComplexPoints sX),
        κ ⁻¹' (ComplexPoints.toScheme ⁻¹' (S : Set X)) =
          {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} ∧
        Set.InjOn κ {p : Σ i, M i |
          p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)}ᶜ ∧
        (ComplexPoints.toScheme ⁻¹' (S : Set X))ᶜ ⊆ Set.range κ := by
  obtain ⟨ι, hι, d, Y, hYt, hYc, hYt2, J, hJ, E, hEc, Ach, hAch, p, hp1, hp2, hp3⟩ :=
    exists_sncResolution_complexPoints sX hX S hSing hcomp
  choose M hMt hMc hMm hMcpt hMt2 hface β hβ1 hβ2 hβ3 using fun i ↦
    exists_realOrientedBlowup_of_atlas (d i) (E i) (hEc i) (Ach i) (hAch i).1 (hAch i).2.1
      (hAch i).2.2
  refine ⟨ι, hι, fun i ↦ d i * 2, M, hMt, hMc, hMm, hMcpt, hMt2, hface,
    ⟨fun q ↦ p q.1 (β q.1 q.2), continuous_sigma fun i ↦ (p i).continuous.comp (β i).continuous⟩,
    ?_, ?_, ?_⟩
  · ext ⟨i, x⟩
    change p i (β i x) ∈ ComplexPoints.toScheme ⁻¹' (S : Set X) ↔
      x ∈ (modelWithCornersEuclideanQuadrant (d i * 2)).boundary (M i)
    rw [← hβ1 i, ← hp1 i]
    rfl
  · rintro ⟨i, x⟩ hx ⟨i', x'⟩ hx' h
    have h1 : β i x ∉ ⋃ j, E i j := fun h' ↦ hx (by
      change x ∈ (modelWithCornersEuclideanQuadrant (d i * 2)).boundary (M i)
      rw [← hβ1 i]; exact h')
    have h2 : β i' x' ∉ ⋃ j, E i' j := fun h' ↦ hx' (by
      change x' ∈ (modelWithCornersEuclideanQuadrant (d i' * 2)).boundary (M i')
      rw [← hβ1 i']; exact h')
    have h3 := hp2 i i' (β i x) (β i' x') h1 h2 h
    obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.1 h3
    have h4 : β i x = β i x' := eq_of_heq h4
    have h5 : x = x' := hβ2 i hx hx' h4
    rw [h5]
  · intro x hx
    obtain ⟨i, y, rfl⟩ := mem_iUnion.1 (hp3 hx)
    have hy : y ∉ ⋃ j, E i j := by
      rw [← hp1 i]; exact hx
    obtain ⟨x', hx', rfl⟩ := hβ3 i hy
    exact ⟨⟨i, x'⟩, rfl⟩

end MMP.Proof_lem_mmp_projective_corner_presentation

@[expose] public section

namespace MMP.Analytic

open MMP.Proof_lem_mmp_projective_corner_presentation

/-- **Compact corner presentation of a projective complex variety.** Let `X` be a reduced
projective scheme over `ℂ` and `S ⊆ X` a closed subset containing the singular locus and no
irreducible component of `X`. There are a finite disjoint union `M = Σ i, M i` of compact
Hausdorff smooth manifolds with corners with embedded boundary hypersurfaces, a continuous map
`φ : ∂M → S^an` and a continuous map `κ : M → X^an` such that the square
`∂M ⟶ M`, `φ`, `κ`, `S^an ⟶ X^an` is a pushout in `TopCat` (so `X^an ≅ M ∪_{∂M} S^an`), and
`κ` restricts to a homeomorphism of `M ∖ ∂M` onto the open set `X^an ∖ S^an`. -/
@[mmp "lem_mmp_projective_corner_presentation"]
public theorem exists_isPushout_manifoldWithCorners_boundary
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsReduced X] (hX : IsProjective sX)
    (S : Closeds X) (hSing : MMP.Mori.singularLocus sX ≤ S)
    (hcomp : ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ (S : Set X)) :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (M : ι → Type)
      (_ : ∀ i, TopologicalSpace (M i)) (_ : ∀ i, ChartedSpace (EuclideanQuadrant (n i)) (M i))
      (_ : ∀ i, IsManifold (modelWithCornersEuclideanQuadrant (n i)) ∞ (M i))
      (_ : ∀ i, CompactSpace (M i)) (_ : ∀ i, T2Space (M i)),
      -- the boundary hypersurfaces of each `M i` are embedded
      (∀ i, ∃ (J : Type) (_ : Finite J) (F : J → Set (M i)), (∀ j, IsClosed (F j)) ∧
        ∀ x : M i, ∃ e ∈ atlas (EuclideanQuadrant (n i)) (M i), x ∈ e.source ∧
          ∃ σ : {j // x ∈ F j} ≃ {k : Fin (n i) // (e x).1 k = 0},
            ∀ j, F j ∩ e.source = {z | z ∈ e.source ∧ ∃ hj : x ∈ F j, (e z).1 (σ ⟨j, hj⟩) = 0}) ∧
      ∃ (φ : C({p : Σ i, M i |
            p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)},
            ((ComplexPoints.toScheme ⁻¹' (S : Set X) : Set (ComplexPoints sX)))))
        (κ : C(Σ i, M i, ComplexPoints sX)),
        IsPushout
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of {p : Σ i, M i |
              p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} ⟶
              TopCat.of (Σ i, M i))
          (TopCat.ofHom φ) (TopCat.ofHom κ)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of ((ComplexPoints.toScheme ⁻¹' (S : Set X) : Set (ComplexPoints sX))) ⟶
              TopCat.of (ComplexPoints sX)) ∧
        IsOpenEmbedding (fun p : {p : Σ i, M i |
            p.2 ∉ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} ↦ κ p) ∧
        Set.range (fun p : {p : Σ i, M i |
            p.2 ∉ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} ↦ κ p) =
          (ComplexPoints.toScheme ⁻¹' (S : Set X))ᶜ := by
  haveI : IsProper sX := hX.isProper
  obtain ⟨ι, hι, n, M, hM, hc, hmf, hcpt, ht2, hface, κ, hpre, hinj, hsurj⟩ :=
    exists_realOrientedBlowup sX hX S hSing hcomp
  have hS : IsClosed (ComplexPoints.toScheme ⁻¹' (S : Set X) : Set (ComplexPoints sX)) :=
    S.isClosed.preimage ComplexPoints.continuous_toScheme
  refine ⟨ι, hι, n, M, hM, hc, hmf, hcpt, ht2, hface, restrictBoundary κ hpre, κ,
    isPushout_restrictBoundary κ hpre hS hinj hsurj,
    isOpenEmbedding_restrict κ hpre hS hinj hsurj, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨⟨p, hp⟩, rfl⟩ h
    exact hp ((Set.ext_iff.1 hpre p).1 h)
  · intro x hx
    obtain ⟨p, rfl⟩ := hsurj hx
    exact ⟨⟨p, fun h ↦ hx ((Set.ext_iff.1 hpre p).2 h)⟩, rfl⟩

end MMP.Analytic
