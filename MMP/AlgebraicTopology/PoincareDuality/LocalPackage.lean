module

public import MMP.AlgebraicTopology.PoincareDuality.LocalGenerator
public import MMP.AlgebraicTopology.PoincareDuality.DetectingCocycle
public import MMP.AlgebraicTopology.PoincareDuality.LocalInjectiveManifold
public import MMP.AlgebraicTopology.SingularHomology.ChartSimplexLocalHomology
public import MMP.AlgebraicTopology.FundamentalClass.Euclidean

/-!
# The local homology of a manifold in the top degree, at a point

Let `Y` be a T1 space, `e : Y → H` an open partial homeomorphism into a real vector space
`H` with a basis `b` of `n = m + 1` vectors, and `y` a point of the domain of `e`. For an affine
simplex `Δ` of the image of `e`, around `e y` and positively oriented for `b`, the simplex
`e⁻¹ ∘ Δ` of `Y` freely generates the local homology `H_n(Y, Y - y; R)`, and some relative
cocycle `φ ∈ Z^n(Y, Y - y; R)` takes the value `1` on it.

The statement on `ℝⁿ` at `0`, for the explicit simplex `Δₙ`
(`MMP.SingularChain.localGenerator`), is transported:

* along the homeomorphism `ℝⁿ ≅ H`, `u ↦ ∑ uᵢ bᵢ + e y`, which sends `Δₙ` to an affine simplex
  around `e y` oriented for `b`;
* to the given simplex `Δ`, which is locally homologous to it
  (`MMP.FundamentalClass.isLocallyHomologous_of_isOrientedSimplexAroundZero`);
* to the open subset `e(Y)` of `H` (converse excision), along `e⁻¹ : e(Y) ≅ dom e`, and from the
  open subset `dom e` to `Y` (excision).

The same transports carry the vanishing of `H_k(ℝⁿ, ℝⁿ - 0)` for `k < n` to `(Y, Y - y)`, and the
detecting cocycle comes from
`MMP.SingularCochain.exists_mem_relCocycles_eval_eq_one`.

## Main results

* `MMP.SingularChain.exists_sub_smul_chartSimplexIn_mem`: generation.
* `MMP.SingularChain.eq_zero_of_smul_chartSimplexIn_mem`: freeness.
* `MMP.SingularChain.exists_mem_relCocycles_eval_chartSimplexIn`: the detecting
  relative cocycle.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27 and Theorem 3.26.
-/

@[expose] public noncomputable section

open Finsupp Set Topology
open MMP.ThomClass MMP.FundamentalClass

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

section transport

variable (R) in
/-- The relative cycle `z` freely generates `H_{m+1}(X, X - x; R)`: its boundary lies in
`X - x`, every relative cycle is a multiple of `z` modulo relative boundaries, and `r z` is a
relative boundary only for `r = 0`. -/
def IsFreeLocalGenerator (m : ℕ) (x : X) (z : Chain R X (m + 1)) : Prop :=
  bd R m z ∈ inside R m ({x}ᶜ : Set X) ∧
    (∀ c : Chain R X (m + 1), bd R m c ∈ inside R m ({x}ᶜ : Set X) →
      ∃ r : R, IsRelBoundary R (m + 1) {x} (c - r • z)) ∧
    ∀ r : R, IsRelBoundary R (m + 1) {x} (r • z) → r = 0

variable (R) in
/-- `H_0(X, X - x; R) = 0`. -/
def ZeroLocalVanishing (x : X) : Prop :=
  ∀ c : Chain R X 0, IsRelBoundary R 0 {x} c

/-- The boundary of a relative boundary of `(X, K)` is a chain of `X - K`. -/
lemma bd_mem_inside_of_isRelBoundary {m : ℕ} {K : Set X} {c : Chain R X (m + 1)}
    (hc : IsRelBoundary R (m + 1) K c) : bd R m c ∈ inside R m Kᶜ := by
  obtain ⟨w, hw⟩ := hc
  have := bd_mem_inside hw
  rwa [map_sub, bd_bd, sub_zero] at this

/-- Replacing the generator by a homologous relative cycle. -/
lemma IsFreeLocalGenerator.of_isRelBoundary_sub {m : ℕ} {x : X} {z z' : Chain R X (m + 1)}
    (h : IsFreeLocalGenerator R m x z) (hzz : IsRelBoundary R (m + 1) {x} (z - z')) :
    IsFreeLocalGenerator R m x z' := by
  obtain ⟨hz, hgen, hfree⟩ := h
  refine ⟨?_, fun c hc ↦ ?_, fun r hr ↦ hfree r ?_⟩
  · have h1 := bd_mem_inside_of_isRelBoundary hzz
    rw [map_sub] at h1
    have := Submodule.sub_mem _ hz h1
    rwa [sub_sub_cancel] at this
  · obtain ⟨r, hr⟩ := hgen c hc
    refine ⟨r, ?_⟩
    have := hr.add (hzz.smul r)
    rwa [smul_sub, sub_add_sub_cancel] at this
  · have := hr.add (hzz.smul r)
    rwa [smul_sub, add_sub_cancel] at this

/-- Pushing a chain forward along `φ` and then along `φ⁻¹` returns it. -/
lemma postcomp_symm_postcomp (φ : X ≃ₜ X') {n : ℕ} (c : Chain R X n) :
    postcomp R (φ.symm : C(X', X)) n (postcomp R (φ : C(X, X')) n c) = c := by
  rw [postcomp_comp, φ.symm_comp_toContinuousMap, postcomp_id]

/-- Pushing a chain forward along `φ⁻¹` and then along `φ` returns it. -/
lemma postcomp_postcomp_symm (φ : X ≃ₜ X') {n : ℕ} (c : Chain R X' n) :
    postcomp R (φ : C(X, X')) n (postcomp R (φ.symm : C(X', X)) n c) = c := by
  simpa using postcomp_symm_postcomp φ.symm c

/-- Transport of a free generator along a homeomorphism. -/
lemma IsFreeLocalGenerator.postcomp_homeomorph {m : ℕ} (φ : X ≃ₜ X') {x : X}
    {z : Chain R X (m + 1)} (h : IsFreeLocalGenerator R m x z) :
    IsFreeLocalGenerator R m (φ x) (postcomp R (φ : C(X, X')) (m + 1) z) := by
  obtain ⟨hz, hgen, hfree⟩ := h
  refine ⟨?_, fun c hc ↦ ?_, fun r hr ↦ hfree r ?_⟩
  · rw [← postcomp_bd]
    exact postcomp_mem_inside _ (U := {x}ᶜ) (V := {φ x}ᶜ)
      (fun u hu h ↦ hu (φ.injective h)) hz
  · have hc' : bd R m (postcomp R (φ.symm : C(X', X)) (m + 1) c) ∈ inside R m ({x}ᶜ : Set X) := by
      rw [← postcomp_bd]
      exact postcomp_mem_inside _ (U := {φ x}ᶜ) (V := {x}ᶜ)
        (fun u hu h ↦ hu (φ.symm_apply_eq.1 h)) hc
    obtain ⟨r, hr⟩ := hgen _ hc'
    refine ⟨r, ?_⟩
    have := isRelBoundary_postcomp (φ : C(X, X')) (L := {φ x})
      (fun u (hu : φ u = φ x) ↦ (φ.injective hu : u = x)) hr
    rwa [map_sub, map_smul, postcomp_postcomp_symm] at this
  · have := isRelBoundary_postcomp (φ.symm : C(X', X)) (L := {x})
      (fun u (hu : φ.symm u = x) ↦ φ.symm_apply_eq.1 hu) hr
    rwa [map_smul, postcomp_symm_postcomp] at this

/-- If `H_0(X, X - x; R) = 0` and `φ : X ≃ₜ X'`, then `H_0(X', X' - φ x; R) = 0`. -/
lemma ZeroLocalVanishing.postcomp_homeomorph (φ : X ≃ₜ X') {x : X}
    (h : ZeroLocalVanishing R x) : ZeroLocalVanishing R (φ x) := fun c ↦ by
  have := isRelBoundary_postcomp (φ : C(X, X')) (L := {φ x})
    (fun u (hu : φ u = φ x) ↦ (φ.injective hu : u = x)) (h (postcomp R (φ.symm : C(X', X)) 0 c))
  rwa [postcomp_postcomp_symm] at this

/-- The preimage of `{x}` under the inclusion of a subset `U ∋ x` is `{x}`. -/
lemma preimage_subtypeVal_singleton {U : Set X} (x : U) :
    ((↑) : U → X) ⁻¹' {(x : X)} = {x} := by
  ext u
  simp [Subtype.ext_iff]

/-- If `H_0(U, U - x; R) = 0` for a subset `U ∋ x`, then `H_0(X, X - x; R) = 0`. -/
lemma ZeroLocalVanishing.postcomp_subtypeVal {U : Set X} {x : U}
    (h : ZeroLocalVanishing R x) : ZeroLocalVanishing R (x : X) := fun c ↦ by
  induction c using Finsupp.induction_linear with
  | zero => exact isRelBoundary_zero 0 _
  | add c d hc hd => exact hc.add hd
  | single σ a =>
    by_cases hσ : range σ ⊆ U
    · obtain ⟨c', hc'⟩ := exists_postcomp_subtypeVal_eq (R := R) (single_mem_supported R a hσ)
      rw [← hc']
      exact isRelBoundary_postcomp_subtypeVal
        (by simpa only [preimage_subtypeVal_singleton] using h c')
    · refine isRelBoundary_of_mem_inside (single_mem_supported R a ?_)
      rw [simplex_zero_eq_const σ] at hσ ⊢
      rintro _ ⟨t, rfl⟩ (hx : _ = (x : X))
      exact hσ (by rintro _ ⟨s, rfl⟩; exact (hx ▸ x.2 : _))

variable [T1Space X]

/-- Converse excision of a free generator: from `X` to an open subset `U`. -/
lemma IsFreeLocalGenerator.of_postcomp_subtypeVal {m : ℕ} {U : Set X} (hU : IsOpen U) {x : U}
    {z : Chain R U (m + 1)}
    (h : IsFreeLocalGenerator R m (x : X) (postcomp R (ContinuousMap.subtypeVal U) (m + 1) z)) :
    IsFreeLocalGenerator R m x z := by
  obtain ⟨hz, hgen, hfree⟩ := h
  have hpre := preimage_subtypeVal_singleton x
  have hpre' : (ContinuousMap.subtypeVal U : U → X) ⁻¹' {(x : X)} = {x} := hpre
  refine ⟨?_, fun c hc ↦ ?_, fun r hr ↦ hfree r ?_⟩
  · rw [← postcomp_bd] at hz
    have := mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective hz
    rwa [preimage_compl, hpre'] at this
  · have hc' : bd R m (postcomp R (ContinuousMap.subtypeVal U) (m + 1) c) ∈
        inside R m ({(x : X)}ᶜ : Set X) := by
      rw [← postcomp_bd]
      exact postcomp_mem_inside _ (U := {x}ᶜ) (V := {(x : X)}ᶜ)
        (fun u hu h ↦ hu (Subtype.ext h)) hc
    obtain ⟨r, hr⟩ := hgen _ hc'
    refine ⟨r, ?_⟩
    rw [← map_smul, ← map_sub] at hr
    have := IsRelBoundary.of_postcomp_subtypeVal hU isClosed_singleton
      (singleton_subset_iff.2 x.2) hr
    rwa [hpre] at this
  · rw [← map_smul]
    exact isRelBoundary_postcomp_subtypeVal (by rwa [hpre])

/-- Excision of a free generator: from an open subset `U` to `X`. -/
lemma IsFreeLocalGenerator.postcomp_subtypeVal {m : ℕ} {U : Set X} (hU : IsOpen U) {x : U}
    {z : Chain R U (m + 1)} (h : IsFreeLocalGenerator R m x z) :
    IsFreeLocalGenerator R m (x : X) (postcomp R (ContinuousMap.subtypeVal U) (m + 1) z) := by
  obtain ⟨hz, hgen, hfree⟩ := h
  have hpre := preimage_subtypeVal_singleton x
  refine ⟨?_, fun c hc ↦ ?_, fun r hr ↦ hfree r ?_⟩
  · rw [← postcomp_bd]
    exact postcomp_mem_inside _ (U := {x}ᶜ) (V := {(x : X)}ᶜ)
        (fun u hu h ↦ hu (Subtype.ext h)) hz
  · obtain ⟨c', hc', hbd⟩ := exists_isRelBoundary_sub_postcomp_subtypeVal hU isClosed_singleton
      (singleton_subset_iff.2 x.2) hc
    rw [hpre] at hbd
    obtain ⟨r, hr⟩ := hgen c' hbd
    refine ⟨r, ?_⟩
    have h2 := isRelBoundary_postcomp_subtypeVal (K := {(x : X)}) (by rwa [hpre])
    rw [map_sub, map_smul] at h2
    have := hc'.add h2
    rwa [sub_add_sub_cancel] at this
  · rw [← map_smul] at hr
    have := IsRelBoundary.of_postcomp_subtypeVal hU isClosed_singleton
      (singleton_subset_iff.2 x.2) hr
    rwa [hpre] at this

/-- If `H_0(X, X - x; R) = 0` and `U ∋ x` is open, then `H_0(U, U - x; R) = 0`. -/
lemma ZeroLocalVanishing.of_subtypeVal {U : Set X} (hU : IsOpen U) {x : U}
    (h : ZeroLocalVanishing R (x : X)) : ZeroLocalVanishing R x := fun c ↦ by
  have := IsRelBoundary.of_postcomp_subtypeVal hU isClosed_singleton
    (singleton_subset_iff.2 x.2) (h (postcomp R (ContinuousMap.subtypeVal U) 0 c))
  rwa [preimage_subtypeVal_singleton] at this

end transport

section chart

/-- Two locally homologous simplices (over `ℤ`) differ by a relative boundary with coefficients
in `R`. -/
lemma isRelBoundary_of_isLocallyHomologous {x : X} {n : ℕ} {σ₁ σ₂ : Simplex X n}
    (h : IsLocallyHomologous x σ₁ σ₂) :
    IsRelBoundary R n {x} (single σ₁ 1 - single σ₂ 1) := by
  obtain ⟨c, d, hd, h⟩ := h
  refine ⟨castChain R (n + 1) c, ?_⟩
  have := congrArg (castChain R n) h
  rw [map_sub, map_add, castChain_single, castChain_single, Int.cast_one, ← bd_castChain] at this
  rw [this, add_sub_cancel_left]
  exact castChain_mem_inside hd

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] [T2Space H] {Y : Type*} [TopologicalSpace Y]

/-- The singular simplex `e⁻¹ ∘ Δ` of `Y`, for the affine simplex `Δ` with vertices `v` in the
image of `e`: the chart simplex of the coordinate ball of `e`, pushed to `Y`. -/
def chartSimplexIn {m : ℕ} (e : OpenPartialHomeomorph Y H) (v : Fin (m + 2) → H)
    (hvt : range (affineSimplex v) ⊆ e.target) : Simplex Y (m + 1) :=
  (ContinuousMap.subtypeVal _).comp (chartSimplex e v hvt)

/-- The homeomorphism `ℝⁿ ≅ H`, `u ↦ ∑ uᵢ bᵢ + p`. -/
def basisTranslateHomeomorph {n : ℕ} (b : Module.Basis (Fin n) ℝ H) (p : H) :
    (Fin n → ℝ) ≃ₜ H :=
  (basisHomeomorph b).symm.trans (Homeomorph.addRight p)

/-- `basisTranslateHomeomorph b p u = ∑ uᵢ bᵢ + p`. -/
lemma basisTranslateHomeomorph_apply {n : ℕ} (b : Module.Basis (Fin n) ℝ H) (p : H)
    (u : Fin n → ℝ) : basisTranslateHomeomorph b p u = b.equivFun.symm u + p :=
  rfl

/-- `basisTranslateHomeomorph b p` sends `0` to `p`. -/
lemma basisTranslateHomeomorph_zero {n : ℕ} (b : Module.Basis (Fin n) ℝ H) (p : H) :
    basisTranslateHomeomorph b p 0 = p := by
  rw [basisTranslateHomeomorph_apply, map_zero, zero_add]

/-- **An oriented affine simplex around `p` freely generates `H_n(H, H - p; R)`.** -/
theorem isFreeLocalGenerator_affineSimplex {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    {p : H} {v : Fin (m + 2) → H} (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - p) :
    IsFreeLocalGenerator R m p (single (affineSimplex v) 1) := by
  have h0 : IsFreeLocalGenerator R m (0 : Fin (m + 1) → ℝ) (single (localGenerator (m + 1)) 1) :=
    ⟨bd_localGenerator_mem m, exists_sub_smul_localGenerator_mem m,
      eq_zero_of_smul_localGenerator_mem m⟩
  set ψ := basisTranslateHomeomorph b p
  set v' : Fin (m + 2) → H := fun k ↦ b.equivFun.symm (localGeneratorVertices (m + 1) k) + p
  have hcomp : (ψ : C(Fin (m + 1) → ℝ, H)).comp (localGenerator (m + 1)) = affineSimplex v' := by
    ext t
    have hsum : ∑ k, (t : Fin (m + 2) → ℝ) k = 1 := t.2.2
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, localGenerator, affineSimplex_apply,
      ψ, basisTranslateHomeomorph_apply, v', smul_add, Finset.sum_add_distrib, ← Finset.sum_smul,
      hsum, one_smul, map_sum, map_smul]
  have h1 := h0.postcomp_homeomorph ψ
  rw [postcomp_single, hcomp, basisTranslateHomeomorph_zero] at h1
  have hv' : IsOrientedSimplexAroundZero b fun k ↦ v' k - p := by
    have := (isOrientedSimplexAroundZero_localGeneratorVertices (m + 1)).map b.equivFun.symm
    have hb : (Pi.basisFun ℝ (Fin (m + 1))).map b.equivFun.symm = b :=
      Module.Basis.eq_of_apply_eq fun i ↦ by simp
    rw [hb] at this
    convert this using 1
    funext k
    simp [v']
  refine h1.of_isRelBoundary_sub ?_
  exact isRelBoundary_of_isLocallyHomologous
    (isLocallyHomologous_of_isOrientedSimplexAroundZero (OpenPartialHomeomorph.refl H)
      (mem_univ p) hv' (subset_univ _) hv (subset_univ _) (fun _ ↦ rfl) (fun _ ↦ rfl))

/-- The inverse of `e : e.source ≃ₜ e.target` sends `e y` to `y`. -/
lemma toHomeomorphSourceTarget_symm_mk (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) :
    e.toHomeomorphSourceTarget.symm ⟨e y, e.map_source hy⟩ = ⟨y, hy⟩ :=
  Subtype.ext (e.left_inv hy)

variable [T1Space Y]

/-- **The chart simplex `e⁻¹ ∘ Δ` freely generates `H_n(Y, Y - y; R)`**, for `Δ` an affine
simplex of the image of `e` around `e y`, positively oriented for `b`. -/
theorem isFreeLocalGenerator_chartSimplexIn {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) {v : Fin (m + 2) → H}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e y)
    (hvt : range (affineSimplex v) ⊆ e.target) :
    IsFreeLocalGenerator R m y (single (chartSimplexIn e v hvt) 1) := by
  have hH := isFreeLocalGenerator_affineSimplex (R := R) b hv
  let ΔT : Simplex e.target (m + 1) :=
    ⟨fun t ↦ ⟨affineSimplex v t, hvt ⟨t, rfl⟩⟩, (affineSimplex v).continuous.subtype_mk _⟩
  have hΔT : (ContinuousMap.subtypeVal e.target).comp ΔT = affineSimplex v := rfl
  have hT : IsFreeLocalGenerator R m (⟨e y, e.map_source hy⟩ : e.target) (single ΔT 1) :=
    .of_postcomp_subtypeVal (x := ⟨e y, e.map_source hy⟩) e.open_target
      (by rwa [postcomp_single, hΔT])
  have hS := hT.postcomp_homeomorph e.toHomeomorphSourceTarget.symm
  rw [postcomp_single, toHomeomorphSourceTarget_symm_mk e hy] at hS
  have hY := hS.postcomp_subtypeVal e.open_source
  rw [postcomp_single] at hY
  convert hY using 2
  ext t
  rfl

/-- `H_0(Y, Y - y; R) = 0` at a point `y` of the domain of `e`. -/
theorem zeroLocalVanishing_of_mem_source {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) : ZeroLocalVanishing R y := by
  have h0 : ZeroLocalVanishing R (0 : Fin (m + 1) → ℝ) :=
    isRelBoundary_singleton_zero_zero (by omega)
  have h1 := h0.postcomp_homeomorph (basisTranslateHomeomorph b (e y))
  rw [basisTranslateHomeomorph_zero] at h1
  have hT := ZeroLocalVanishing.of_subtypeVal (x := ⟨e y, e.map_source hy⟩) e.open_target h1
  have hS := hT.postcomp_homeomorph e.toHomeomorphSourceTarget.symm
  rw [toHomeomorphSourceTarget_symm_mk e hy] at hS
  exact hS.postcomp_subtypeVal

/-- `H_{k+1}(Y, Y - y; R) = 0` for `k + 1 < n` at a point `y` of the domain of `e`. -/
theorem relVanishing_singleton_of_mem_source {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) {k : ℕ} (hk : k + 1 < m + 1) :
    RelVanishing R Y k {y} := by
  have h1 := RelVanishing.of_homeomorph (basisTranslateHomeomorph b (e y))
    (relVanishing_singleton_zero_low (R := R) (m + 1) k hk)
  rw [image_singleton, basisTranslateHomeomorph_zero] at h1
  refine RelVanishing.of_openPartialHomeomorph e isClosed_singleton (singleton_subset_iff.2 hy) ?_
  rw [image_singleton]
  exact RelVanishing.subtype e.open_target isClosed_singleton
    (singleton_subset_iff.2 (e.map_source hy)) h1

/-- **Generation of `H_n(Y, Y - y; R)`** by the chart simplex `e⁻¹ ∘ Δ`. -/
theorem exists_sub_smul_chartSimplexIn_mem {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) {v : Fin (m + 2) → H}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e y)
    (hvt : range (affineSimplex v) ⊆ e.target) :
    ∀ c : Chain R Y (m + 1), bd R m c ∈ inside R m ({y}ᶜ : Set Y) →
      ∃ r : R, ∃ w, c - r • single (chartSimplexIn e v hvt) 1 - bd R (m + 1) w ∈
        inside R (m + 1) ({y}ᶜ : Set Y) :=
  (isFreeLocalGenerator_chartSimplexIn b e hy hv hvt).2.1

/-- **Freeness of `H_n(Y, Y - y; R)`** on the chart simplex `e⁻¹ ∘ Δ`. -/
theorem eq_zero_of_smul_chartSimplexIn_mem {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) {v : Fin (m + 2) → H}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e y)
    (hvt : range (affineSimplex v) ⊆ e.target) :
    ∀ r : R, (∃ w, r • single (chartSimplexIn e v hvt) 1 - bd R (m + 1) w ∈
      inside R (m + 1) ({y}ᶜ : Set Y)) → r = 0 :=
  (isFreeLocalGenerator_chartSimplexIn b e hy hv hvt).2.2

/-- **A relative cocycle of `(Y, Y - y)` detecting the chart simplex**: some
`φ ∈ Z^n(Y, Y - y; R)` has `⟨φ, e⁻¹ ∘ Δ⟩ = 1`. -/
theorem exists_mem_relCocycles_eval_chartSimplexIn {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    (e : OpenPartialHomeomorph Y H) {y : Y} (hy : y ∈ e.source) {v : Fin (m + 2) → H}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e y)
    (hvt : range (affineSimplex v) ⊆ e.target) :
    ∃ φ ∈ SingularCochain.relCocycles R ({y}ᶜ : Set Y) (m + 1),
      SingularCochain.eval φ (single (chartSimplexIn e v hvt) 1) = 1 :=
  have h := isFreeLocalGenerator_chartSimplexIn (R := R) b e hy hv hvt
  SingularCochain.exists_mem_relCocycles_eval_eq_one _ m (zeroLocalVanishing_of_mem_source b e hy)
    (fun _ hk ↦ relVanishing_singleton_of_mem_source b e hy hk) _ h.1 h.2.1 h.2.2

end chart

end SingularChain

end MMP
