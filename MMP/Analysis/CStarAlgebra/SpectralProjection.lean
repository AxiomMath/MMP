module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# The spectral projection of a nearly idempotent normal element

Let `a` be a normal element of a C⋆-algebra with `‖a * a - a‖ ≤ 1/8`. Its spectrum lies in the
compact set `{z | ‖z * z - z‖ ≤ 1/8}`, which misses the line `re z = 1/2`; so the function equal
to `1` for `re z > 1/2` and to `0` otherwise is continuous on the spectrum, and applying it to `a`
gives an idempotent, the *spectral projection* of `a` onto the part of its spectrum near `1`.
It equals `a` when `a` is idempotent, lies in `a * 𝒜`, and depends continuously on `a`.

This turns a continuous family of normal operators that are idempotent on a subset `X` into a
continuous family of idempotents on a neighbourhood of `X`, agreeing with the given one on `X`.

## Main definitions

* `MMP.spectralProj`: the spectral projection.

## Main results

* `MMP.isIdempotentElem_spectralProj`: the spectral projection is idempotent.
* `MMP.spectralProj_eq_self`: the spectral projection of an idempotent is itself.
* `MMP.spectralProj_eq_mul`: `spectralProj a = a * c` for some `c`.
* `MMP.continuousOn_spectralProj`: continuity on `{x | ‖a x * a x - a x‖ ≤ 1/8}`.
-/

@[expose] public noncomputable section

open Set Topology Filter

namespace MMP

/-- The compact set `{z | ‖z * z - z‖ ≤ 1/8}` around `0` and `1`. -/
def nearIdempotentSet : Set ℂ := {z | ‖z * z - z‖ ≤ 1 / 8}

/-- `1` right of the line `re z = 1/2`, `0` left of it. -/
def halfPlaneIndicator (z : ℂ) : ℂ := if 1 / 2 < z.re then 1 else 0

/-- `z⁻¹` right of the line `re z = 1/2`, `0` left of it. -/
def halfPlaneInv (z : ℂ) : ℂ := if 1 / 2 < z.re then z⁻¹ else 0

/-- A point of `nearIdempotentSet` does not lie on the line `re z = 1/2`. -/
lemma re_ne_half_of_mem_nearIdempotentSet {z : ℂ} (hz : z ∈ nearIdempotentSet) :
    z.re ≠ 1 / 2 := by
  intro h
  have h1 := (Complex.abs_re_le_norm (z * z - z)).trans hz
  simp only [Complex.sub_re, Complex.mul_re, h] at h1
  rw [abs_le] at h1
  nlinarith [sq_nonneg z.im]

/-- The set `nearIdempotentSet` is compact. -/
lemma isCompact_nearIdempotentSet : IsCompact nearIdempotentSet := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (by fun_prop) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  have h1 := norm_sub_norm_le (z * z) z
  rw [norm_mul] at h1
  have : ‖z * z - z‖ ≤ 1 / 8 := hz
  nlinarith

/-- `halfPlaneIndicator` is continuous on `nearIdempotentSet`. -/
lemma continuousOn_halfPlaneIndicator : ContinuousOn halfPlaneIndicator nearIdempotentSet := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  rcases (re_ne_half_of_mem_nearIdempotentSet hz).lt_or_gt with h | h
  · have : ∀ᶠ w in 𝓝 z, w.re < 1 / 2 :=
      Complex.continuous_re.continuousAt.eventually (gt_mem_nhds h)
    refine (continuousAt_const (y := (0 : ℂ))).congr (this.mono fun w hw ↦ ?_)
    simp only [halfPlaneIndicator, hw.not_gt, ↓reduceIte]
  · have : ∀ᶠ w in 𝓝 z, 1 / 2 < w.re :=
      Complex.continuous_re.continuousAt.eventually (lt_mem_nhds h)
    refine (continuousAt_const (y := (1 : ℂ))).congr (this.mono fun w hw ↦ ?_)
    simp only [halfPlaneIndicator, hw, ↓reduceIte]

/-- `halfPlaneInv` is continuous on `nearIdempotentSet`. -/
lemma continuousOn_halfPlaneInv : ContinuousOn halfPlaneInv nearIdempotentSet := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  rcases (re_ne_half_of_mem_nearIdempotentSet hz).lt_or_gt with h | h
  · have : ∀ᶠ w in 𝓝 z, w.re < 1 / 2 :=
      Complex.continuous_re.continuousAt.eventually (gt_mem_nhds h)
    refine (continuousAt_const (y := (0 : ℂ))).congr (this.mono fun w hw ↦ ?_)
    simp only [halfPlaneInv, hw.not_gt, ↓reduceIte]
  · have : ∀ᶠ w in 𝓝 z, 1 / 2 < w.re :=
      Complex.continuous_re.continuousAt.eventually (lt_mem_nhds h)
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at h
    refine (continuousAt_inv₀ hz0).congr (this.mono fun w hw ↦ ?_)
    simp only [halfPlaneInv, hw, ↓reduceIte]

/-- `halfPlaneIndicator` is idempotent pointwise. -/
lemma halfPlaneIndicator_mul_self (z : ℂ) :
    halfPlaneIndicator z * halfPlaneIndicator z = halfPlaneIndicator z := by
  unfold halfPlaneIndicator
  split_ifs <;> simp

/-- `halfPlaneIndicator z = z * halfPlaneInv z`. -/
lemma halfPlaneIndicator_eq_mul (z : ℂ) : halfPlaneIndicator z = z * halfPlaneInv z := by
  unfold halfPlaneIndicator halfPlaneInv
  split_ifs with h
  · have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at h
    rw [mul_inv_cancel₀ hz0]
  · simp

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- If `‖a * a - a‖ ≤ 1/8`, then the spectrum of `a` is contained in `nearIdempotentSet`. -/
lemma spectrum_subset_nearIdempotentSet {a : 𝒜} (h : ‖a * a - a‖ ≤ 1 / 8) :
    spectrum ℂ a ⊆ nearIdempotentSet := by
  rcases subsingleton_or_nontrivial 𝒜 with h𝒜 | h𝒜
  · simp [spectrum.of_subsingleton]
  intro z hz
  have hmem := spectrum.subset_polynomial_aeval a (Polynomial.X * Polynomial.X - Polynomial.X)
    ⟨z, hz, rfl⟩
  simp only [map_sub, map_mul, Polynomial.aeval_X, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X] at hmem
  exact (spectrum.norm_le_norm_of_mem hmem).trans h

/-- The **spectral projection** of `a`: the continuous functional calculus applied to the
function equal to `1` for `re z > 1/2` and to `0` otherwise. -/
def spectralProj (a : 𝒜) : 𝒜 := cfc halfPlaneIndicator a

/-- The spectral projection of a normal element `a` with `‖a * a - a‖ ≤ 1/8` is idempotent. -/
lemma isIdempotentElem_spectralProj {a : 𝒜} (ha : IsStarNormal a) (h : ‖a * a - a‖ ≤ 1 / 8) :
    IsIdempotentElem (spectralProj a) := by
  have hc := continuousOn_halfPlaneIndicator.mono (spectrum_subset_nearIdempotentSet h)
  rw [IsIdempotentElem, spectralProj, ← cfc_mul halfPlaneIndicator halfPlaneIndicator a hc hc]
  exact cfc_congr fun z _ ↦ halfPlaneIndicator_mul_self z

/-- The spectral projection of an idempotent normal element is the element itself. -/
lemma spectralProj_eq_self {a : 𝒜} (ha : IsStarNormal a) (h : IsIdempotentElem a) :
    spectralProj a = a := by
  unfold spectralProj
  conv_rhs => rw [← cfc_id' ℂ a]
  refine cfc_congr fun z hz ↦ ?_
  rcases h.spectrum_subset ℂ hz with rfl | rfl <;> norm_num [halfPlaneIndicator]

/-- The spectral projection of `a` is a multiple `a * c`. -/
lemma spectralProj_eq_mul {a : 𝒜} (ha : IsStarNormal a) (h : ‖a * a - a‖ ≤ 1 / 8) :
    spectralProj a = a * cfc halfPlaneInv a := by
  calc spectralProj a = cfc (fun z ↦ z * halfPlaneInv z) a :=
        cfc_congr fun z _ ↦ halfPlaneIndicator_eq_mul z
    _ = cfc (fun z ↦ z) a * cfc halfPlaneInv a :=
        cfc_mul (fun z ↦ z) halfPlaneInv a (continuousOn_id' _)
          (continuousOn_halfPlaneInv.mono (spectrum_subset_nearIdempotentSet h))
    _ = a * cfc halfPlaneInv a := by rw [cfc_id' ℂ a]

/-- The spectral projection depends continuously on a normal element `a` with
`‖a * a - a‖ ≤ 1/8`. -/
theorem continuousOn_spectralProj {X : Type*} [TopologicalSpace X] {a : X → 𝒜}
    {t : Set X} (hcont : ContinuousOn a t) (hnormal : ∀ x ∈ t, IsStarNormal (a x))
    (h : ∀ x ∈ t, ‖a x * a x - a x‖ ≤ 1 / 8) :
    ContinuousOn (fun x ↦ MMP.spectralProj (a x)) t :=
  ContinuousOn.cfc' isCompact_nearIdempotentSet halfPlaneIndicator hcont
    (fun x hx ↦ spectrum_subset_nearIdempotentSet (h x hx)) hnormal
    continuousOn_halfPlaneIndicator

end MMP
