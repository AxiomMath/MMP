module

public import Mathlib
public import MMP.Analysis.Complex.Submanifold
import MMP.Analysis.Complex.CauchyOsgoodLaurent

/-!
# Holomorphic functions on open subsets of `ℂⁿ` and compact convergence

For an open set `D ⊆ ℂⁿ` and an open `W ⊆ D`, the sections of the sheaf of holomorphic functions
`𝒪_D` over `W` are the holomorphic functions on `W`. We give them the uniform structure of uniform
convergence on compact subsets of `W`. It makes `𝒪_D(W)` a complete, Hausdorff, first countable
uniform additive group (indeed a topological ring), and the restriction maps `𝒪_D(W) → 𝒪_D(W')`,
`W' ⊆ W`, are uniformly continuous.

Completeness is the theorem of Weierstrass: a locally uniform limit of holomorphic functions of
several variables is holomorphic. A function on `W` is holomorphic, as a section of `𝒪_D`, exactly
when it is complex differentiable on the image of `W` in `ℂⁿ`, by Osgood's lemma.

## Main definitions

* `MMP.Analytic.holomorphicCompactConvergence`: the uniform structure of compact convergence on
  `𝒪_D(W)`.
* `MMP.Analytic.holomorphicToContinuousMap`: the map `𝒪_D(W) → C(W, ℂ)` inducing it.

## Main results

* `MMP.Analytic.contMDiff_iff_differentiableOn_extend`: a function on `W` is holomorphic exactly
  when its extension by zero is complex differentiable on the image of `W` in `ℂⁿ`.
* `MMP.Analytic.analyticOnNhd_of_differentiableOn`: complex differentiable functions on open
  subsets of `ℂⁿ` are analytic.
* `MMP.Analytic.differentiableOn_of_tendstoLocallyUniformlyOn`: locally uniform limits of complex
  differentiable functions on open subsets of `ℂⁿ` are complex differentiable.
* `MMP.Analytic.completeSpace_holomorphicCompactConvergence`,
  `MMP.Analytic.t2Space_holomorphicCompactConvergence`,
  `MMP.Analytic.firstCountableTopology_holomorphicCompactConvergence`,
  `MMP.Analytic.isUniformAddGroup_holomorphicCompactConvergence`,
  `MMP.Analytic.isTopologicalRing_holomorphicCompactConvergence`,
  `MMP.Analytic.uniformContinuous_holomorphic_restrict`: the properties of the uniform structure.

## References

* [Grauert–Remmert, *Coherent analytic sheaves*]
* [Gunning–Rossi, *Analytic functions of several complex variables*]
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Filter Topology Set
open scoped Manifold ContDiff

namespace MMP.Analytic

/-! ### Complex differentiable functions on open subsets of `ℂⁿ` -/

section Euclidean

variable {n : ℕ}

/-- A complex differentiable function on an open subset of `ℂⁿ` is analytic there
(Osgood's lemma). -/
theorem analyticOnNhd_of_differentiableOn {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsOpen S)
    {G : EuclideanSpace ℂ (Fin n) → ℂ} (hG : DifferentiableOn ℂ G S) :
    AnalyticOnNhd ℂ G S := by
  classical
  set e := EuclideanSpace.equiv (Fin n) ℂ
  have hΩ : IsOpen (e.symm ⁻¹' S) := hS.preimage e.symm.continuous
  have hd : DifferentiableOn ℂ (G ∘ e.symm) (e.symm ⁻¹' S) :=
    hG.comp e.symm.differentiableOn (fun _ h => h)
  have h3 := (MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.1 n (e.symm ⁻¹' S)
    (G ∘ e.symm) hΩ hd.continuousOn (fun ζ hζ j => by
      have hu : DifferentiableAt ℂ (fun w : ℂ => Function.update ζ j w) (ζ j) :=
        (hasFDerivAt_update ζ (ζ j)).differentiableAt
      have hG' : DifferentiableAt ℂ (G ∘ e.symm) (Function.update ζ j (ζ j)) := by
        rw [Function.update_eq_self]
        exact hd.differentiableAt (hΩ.mem_nhds hζ)
      exact hG'.comp (ζ j) hu)
  intro z hz
  have : AnalyticAt ℂ (G ∘ e.symm) (e z) := h3.2.1 (e z) (by simpa using hz)
  convert this.comp ((e : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)).analyticAt z) using 1
  ext w
  simp

/-- A locally uniform limit of complex differentiable functions on an open subset of `ℂⁿ` is
complex differentiable. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsOpen S) {F : ι → EuclideanSpace ℂ (Fin n) → ℂ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) S)
    (hlim : TendstoLocallyUniformlyOn F f l S) : DifferentiableOn ℂ f S := by
  set e := EuclideanSpace.equiv (Fin n) ℂ
  have hΩ : IsOpen (e.symm ⁻¹' S) := hS.preimage e.symm.continuous
  have h6 := (MMP.SeveralComplex.cauchy_osgood_laurent.{0, _} ℂ).2.2.2.2.2 n l (e.symm ⁻¹' S)
    (fun i => F i ∘ e.symm) (f ∘ e.symm) hΩ
    (hF.mono fun i hi => hi.comp e.symm.differentiableOn (fun _ h => h))
    (hlim.comp e.symm (fun _ h => h) e.symm.continuous.continuousOn)
  have h2 := h6.comp e.differentiableOn (fun z hz => by simpa using hz)
  have he : (f ∘ e.symm) ∘ e = f := funext fun w => by simp
  rwa [he] at h2

end Euclidean

/-! ### Holomorphic functions on open subsets of an open set of `ℂⁿ` -/

section OpenSubset

variable {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}

/-- The inclusion into `ℂⁿ` of an open subset `W` of an open set `D ⊆ ℂⁿ`. -/
abbrev openInclusion (W : Opens (TopCat.of D)) : W → EuclideanSpace ℂ (Fin n) :=
  fun w => ((w : D) : EuclideanSpace ℂ (Fin n))

/-- The inclusion `W → ℂⁿ` is an open embedding. -/
theorem isOpenEmbedding_openInclusion (W : Opens (TopCat.of D)) :
    IsOpenEmbedding (openInclusion W) :=
  D.isOpen.isOpenEmbedding_subtypeVal.comp W.isOpen.isOpenEmbedding_subtypeVal

/-- An open subset `W` of an open set `D ⊆ ℂⁿ` is locally compact. -/
instance (W : Opens (TopCat.of D)) : LocallyCompactSpace W :=
  (isOpenEmbedding_openInclusion W).locallyCompactSpace

/-- A function on `W` is holomorphic at `w` exactly when its extension by zero to `ℂⁿ` is complex
smooth at the image of `w`. -/
theorem contMDiffAt_iff_contDiffAt_extend (W : Opens (TopCat.of D)) (g : W → ℂ) (w : W) :
    ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g w ↔
      ContDiffAt ℂ ∞ (Function.extend (openInclusion W) g 0) (openInclusion W w) := by
  set G := Function.extend (openInclusion W) g 0
  have hg : g = fun w : W => (fun d : D => G d) w := funext fun w =>
    ((isOpenEmbedding_openInclusion W).injective.extend_apply g 0 w).symm
  rw [hg]
  exact contMDiffAt_subtype_iff.trans (contMDiffAt_subtype_iff.trans contMDiffAt_iff_contDiffAt)

/-- A function on `W` is holomorphic exactly when its extension by zero to `ℂⁿ` is complex
differentiable on the image of `W`. -/
theorem contMDiff_iff_differentiableOn_extend (W : Opens (TopCat.of D)) (g : W → ℂ) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g ↔
      DifferentiableOn ℂ (Function.extend (openInclusion W) g 0) (range (openInclusion W)) := by
  constructor
  · rintro hg _ ⟨w, rfl⟩
    exact (((contMDiffAt_iff_contDiffAt_extend W g w).1 (hg w)).differentiableAt
      (by simp)).differentiableWithinAt
  · intro hg w
    rw [contMDiffAt_iff_contDiffAt_extend]
    exact (analyticOnNhd_of_differentiableOn (isOpenEmbedding_openInclusion W).isOpen_range hg
      _ ⟨w, rfl⟩).contDiffAt

/-- The additive map viewing a holomorphic function on `W` as an element of
`UniformOnFun W ℂ {K | IsCompact K}` (uniform convergence on compact subsets). -/
def holomorphicToUniformOnFun (W : Opens (TopCat.of D)) :
    𝒪[n, D].presheaf.obj (op W) →+ UniformOnFun W ℂ {K | IsCompact K} where
  toFun f := UniformOnFun.ofFun _ (f : W → ℂ)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation of `holomorphicToUniformOnFun`. -/
@[simp]
theorem holomorphicToUniformOnFun_apply (W : Opens (TopCat.of D))
    (f : 𝒪[n, D].presheaf.obj (op W)) :
    holomorphicToUniformOnFun W f = UniformOnFun.ofFun _ (f : W → ℂ) :=
  rfl

/-- The **uniform structure of compact convergence** on the holomorphic functions `𝒪_D(W)`. -/
@[instance_reducible]
def holomorphicCompactConvergence (W : Opens (TopCat.of D)) :
    UniformSpace (𝒪[n, D].presheaf.obj (op W)) :=
  UniformSpace.comap (holomorphicToUniformOnFun W) inferInstance

/-- A holomorphic function on `W` as a continuous function. -/
def holomorphicToContinuousMap (W : Opens (TopCat.of D)) (f : 𝒪[n, D].presheaf.obj (op W)) :
    C(W, ℂ) :=
  ⟨f, (show ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (f : W → ℂ) from f.2).continuous⟩

/-- Evaluation of `holomorphicToContinuousMap`. -/
@[simp]
theorem holomorphicToContinuousMap_apply (W : Opens (TopCat.of D))
    (f : 𝒪[n, D].presheaf.obj (op W)) (w : W) :
    holomorphicToContinuousMap W f w = (f : W → ℂ) w :=
  rfl

/-- A holomorphic function on `W` is determined by its underlying continuous function. -/
theorem holomorphicToContinuousMap_injective (W : Opens (TopCat.of D)) :
    Function.Injective (holomorphicToContinuousMap W) := fun f g h =>
  ContMDiffMap.ext fun x => DFunLike.congr_fun h x

/-- The uniform structure of compact convergence on `𝒪_D(W)` is induced by the map to `C(W, ℂ)`
with the compact-open uniform structure. -/
theorem isUniformInducing_holomorphicToContinuousMap (W : Opens (TopCat.of D)) :
    @IsUniformInducing _ _ (holomorphicCompactConvergence W) _ (holomorphicToContinuousMap W) := by
  letI := holomorphicCompactConvergence W
  exact (IsUniformInducing.of_comp_iff
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing).1
    (isUniformInducing_iff_uniformSpace.2 rfl)

/-- With compact convergence, the holomorphic functions on `W` form a uniform additive group. -/
theorem isUniformAddGroup_holomorphicCompactConvergence (W : Opens (TopCat.of D)) :
    @IsUniformAddGroup _ (holomorphicCompactConvergence W) _ :=
  IsUniformAddGroup.comap (holomorphicToUniformOnFun W)

/-- The topology of compact convergence on the holomorphic functions on `W` is Hausdorff. -/
theorem t2Space_holomorphicCompactConvergence (W : Opens (TopCat.of D)) :
    @T2Space _ (holomorphicCompactConvergence W).toTopologicalSpace := by
  letI := holomorphicCompactConvergence W
  exact (IsEmbedding.mk (isUniformInducing_holomorphicToContinuousMap W).isInducing
    (holomorphicToContinuousMap_injective W)).t2Space

/-- The topology of compact convergence on the holomorphic functions on `W` is first countable. -/
theorem firstCountableTopology_holomorphicCompactConvergence (W : Opens (TopCat.of D)) :
    @FirstCountableTopology _ (holomorphicCompactConvergence W).toTopologicalSpace := by
  letI := holomorphicCompactConvergence W
  exact (isUniformInducing_holomorphicToContinuousMap W).isInducing.firstCountableTopology

/-- With compact convergence, the holomorphic functions on `W` form a topological ring. -/
theorem isTopologicalRing_holomorphicCompactConvergence (W : Opens (TopCat.of D)) :
    @IsTopologicalRing _ (holomorphicCompactConvergence W).toTopologicalSpace _ := by
  letI := holomorphicCompactConvergence W
  haveI := isUniformAddGroup_holomorphicCompactConvergence W
  have h := (isUniformInducing_holomorphicToContinuousMap W).isInducing
  haveI : ContinuousMul (𝒪[n, D].presheaf.obj (op W)) :=
    ⟨h.continuous_iff.2 ((continuous_mul.comp (h.continuous.prodMap h.continuous) : Continuous
      fun p : 𝒪[n, D].presheaf.obj (op W) × 𝒪[n, D].presheaf.obj (op W) =>
        holomorphicToContinuousMap W p.1 * holomorphicToContinuousMap W p.2))⟩
  exact {}

/-- The extension by zero to `ℂⁿ` of functions on `W` turns uniform convergence on compact subsets
of `W` into locally uniform convergence on the image of `W`. -/
theorem tendstoLocallyUniformlyOn_extend (W : Opens (TopCat.of D)) {ι : Type*} {l : Filter ι}
    {F : ι → W → ℂ} {f : W → ℂ}
    (h : ∀ K : Set W, IsCompact K → TendstoUniformlyOn F f l K) :
    TendstoLocallyUniformlyOn (fun i => Function.extend (openInclusion W) (F i) 0)
      (Function.extend (openInclusion W) f 0) l (range (openInclusion W)) := by
  have hemb := isOpenEmbedding_openInclusion W
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hemb.isOpen_range).2 fun K hKs hK => ?_
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    (h _ ((hemb.isInducing.isCompact_preimage_iff hKs).2 hK)) ε hε] with i hi z hz
  obtain ⟨w, rfl⟩ := hKs hz
  rw [hemb.injective.extend_apply, hemb.injective.extend_apply]
  exact hi w hz

/-- With compact convergence, the holomorphic functions on `W` form a complete uniform space
(Weierstrass). -/
theorem completeSpace_holomorphicCompactConvergence (W : Opens (TopCat.of D)) :
    @CompleteSpace _ (holomorphicCompactConvergence W) := by
  letI := holomorphicCompactConvergence W
  rw [completeSpace_iff_isComplete_range (isUniformInducing_holomorphicToContinuousMap W)]
  refine IsClosed.isComplete (closure_subset_iff_isClosed.1 fun φ hφ => ?_)
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hφ
  choose s hs using hx
  have hloc := tendstoLocallyUniformlyOn_extend W (F := fun k => (x k : W → ℂ)) (f := φ)
    (l := atTop) fun K hK =>
      ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hlim K hK
  have hd : DifferentiableOn ℂ (Function.extend (openInclusion W) φ 0)
      (range (openInclusion W)) :=
    differentiableOn_of_tendstoLocallyUniformlyOn (isOpenEmbedding_openInclusion W).isOpen_range
      (Eventually.of_forall fun k => by
        rw [← hs k]
        exact (contMDiff_iff_differentiableOn_extend W _).1 (s k).2) hloc
  exact ⟨⟨φ, (contMDiff_iff_differentiableOn_extend W φ).2 hd⟩, rfl⟩

/-- Restriction of holomorphic functions to a smaller open set is uniformly continuous. -/
theorem uniformContinuous_holomorphic_restrict {W W' : Opens (TopCat.of D)} (h : W' ≤ W) :
    @UniformContinuous _ _ (holomorphicCompactConvergence W) (holomorphicCompactConvergence W')
      (𝒪[n, D].presheaf.map (homOfLE h).op).hom := by
  letI := holomorphicCompactConvergence W
  letI := holomorphicCompactConvergence W'
  exact uniformContinuous_comap' ((UniformOnFun.precomp_uniformContinuous
    (𝔖 := {K : Set W | IsCompact K}) (𝔗 := {K : Set W' | IsCompact K}) (β := ℂ)
    (f := inclusion h) (fun K hK => hK.image (continuous_inclusion h))).comp
    uniformContinuous_comap)

end OpenSubset

end MMP.Analytic
