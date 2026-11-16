module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Analysis.RCLike.Basic

/-!
# A vector bundle with a finite trivializing cover is a sub-bundle of a trivial bundle

Let `E` be a topological vector bundle on `B` with fibre `F` over `𝕜` (`ℝ` or `ℂ`), `(eₗ)` a
family of linear trivializations whose base sets cover `B`, and `(ρₗ)` a partition of unity on
`B` subordinate to the base sets. Then `p ↦ (ρₗ(π p) • eₗ(p))ₗ` is a continuous map
`E → (ι → F)`, linear and injective on every fibre.

## Main definitions

* `MMP.bundleEmbedding`: the map `E → (ι → F)`.
* `MMP.bundleEmbeddingL`: its restriction to the fibre at `b`, a linear map.

## Main results

* `MMP.continuous_bundleEmbedding`: the map `E → (ι → F)` is continuous.
* `MMP.bundleEmbedding_mk`: on the fibre at `b` it is `bundleEmbeddingL b`.
* `MMP.injective_bundleEmbeddingL`: its restriction to each fibre is injective.
-/

@[expose] public noncomputable section

open Bundle Set Topology Filter

namespace MMP

variable {𝕜 B F : Type*} [RCLike 𝕜] [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {ι : Type*} (e : ι → Trivialization F (π F E)) [∀ l, (e l).IsLinear 𝕜]
  (ρ : PartitionOfUnity ι B univ)

/-- The map `E → (ι → F)`, `p ↦ (ρₗ(π p) • eₗ(p))ₗ`. -/
def bundleEmbedding (p : TotalSpace F E) : ι → F :=
  fun l ↦ ((ρ l p.proj : ℝ) : 𝕜) • (e l p).2

/-- The map `E_b → (ι → F)`, `v ↦ (ρₗ(b) • eₗ(v))ₗ`. -/
def bundleEmbeddingL (b : B) : E b →ₗ[𝕜] (ι → F) :=
  LinearMap.pi fun l ↦ ((ρ l b : ℝ) : 𝕜) • (e l).linearMapAt 𝕜 b

variable {e ρ}

/-- If `ρ` is subordinate to the base sets of `e` and `b ∉ (e l).baseSet`, then `ρ l b = 0`. -/
lemma eq_zero_of_notMem_baseSet (hρ : ρ.IsSubordinate fun l ↦ (e l).baseSet) {l : ι} {b : B}
    (hb : b ∉ (e l).baseSet) : ρ l b = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hb (hρ l h)

/-- On the fibre at `b`, `bundleEmbedding e ρ` is the linear map `bundleEmbeddingL e ρ b`. -/
lemma bundleEmbedding_mk (hρ : ρ.IsSubordinate fun l ↦ (e l).baseSet) (b : B) (v : E b) :
    bundleEmbedding (𝕜 := 𝕜) e ρ ⟨b, v⟩ = bundleEmbeddingL (𝕜 := 𝕜) e ρ b v := by
  funext l
  simp only [bundleEmbedding, bundleEmbeddingL, LinearMap.pi_apply, LinearMap.smul_apply,
    Trivialization.linearMapAt_apply]
  split_ifs with hb
  · rfl
  · rw [eq_zero_of_notMem_baseSet hρ hb, RCLike.ofReal_zero, zero_smul, zero_smul]

/-- If `ρ` is subordinate to the base sets of `e`, then `bundleEmbedding e ρ` is continuous. -/
theorem continuous_bundleEmbedding (hρ : ρ.IsSubordinate fun l ↦ (e l).baseSet) :
    Continuous (bundleEmbedding (𝕜 := 𝕜) e ρ) := by
  refine continuous_pi fun l ↦ continuous_iff_continuousAt.2 fun p ↦ ?_
  by_cases hp : p.proj ∈ (e l).baseSet
  · have hsrc : (e l).source ∈ 𝓝 p := (e l).open_source.mem_nhds ((e l).mem_source.2 hp)
    exact ((RCLike.continuous_ofReal.comp ((ρ l).continuous.comp
      (FiberBundle.continuous_proj F E))).continuousAt).smul
      ((e l).continuousOn.continuousAt hsrc).snd
  · have hnot : p.proj ∉ tsupport (ρ l) := fun h ↦ hp (hρ l h)
    have hev : ∀ᶠ q in 𝓝 p, q.proj ∈ (tsupport (ρ l))ᶜ :=
      (FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport _).isOpen_compl.mem_nhds hnot)
    refine (continuousAt_const (y := (0 : F))).congr (hev.mono fun q hq ↦ ?_)
    change (0 : F) = ((ρ l q.proj : ℝ) : 𝕜) • (e l q).2
    rw [image_eq_zero_of_notMem_tsupport hq, RCLike.ofReal_zero, zero_smul]

/-- If `ρ` is subordinate to the base sets of `e`, then `bundleEmbeddingL e ρ b` is injective. -/
theorem injective_bundleEmbeddingL (hρ : ρ.IsSubordinate fun l ↦ (e l).baseSet) (b : B) :
    Function.Injective (bundleEmbeddingL (𝕜 := 𝕜) e ρ b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨l, hl⟩ : ∃ l, ρ l b ≠ 0 := by
    by_contra! h
    have := ρ.sum_eq_one (mem_univ b)
    simp only [h, finsum_zero] at this
    exact zero_ne_one this
  have hb : b ∈ (e l).baseSet := by
    by_contra hb
    exact hl (eq_zero_of_notMem_baseSet hρ hb)
  have h1 := congrFun hv l
  simp only [bundleEmbeddingL, LinearMap.pi_apply, LinearMap.smul_apply, Pi.zero_apply] at h1
  rw [smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (RCLike.ofReal_eq_zero.1 h1) hl
  · rw [← (e l).symmₗ_linearMapAt (R := 𝕜) hb v, h1, map_zero]

end MMP
