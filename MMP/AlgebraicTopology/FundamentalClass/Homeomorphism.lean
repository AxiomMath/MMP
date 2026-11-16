module

public import MMP.AlgebraicTopology.FundamentalClass.Locality
/-!
# Fundamental classes under orientation-preserving homeomorphisms (Fulton, §19.1)

Let `φ : M → M'` be an orientation-preserving homeomorphism of oriented real `n`-manifolds (for
example a biholomorphic map of complex manifolds). Then `φ_* μ_M = μ_{M'}`.

A homeomorphism is *orientation preserving* when it carries the local orientation of `M` at
every point `x` to that of `M'` at `φ x`. The local orientation of `M` at `x` is the class in
`H_n(M, M - x; ℤ)` of `e⁻¹ ∘ Δ`, for a chart `e` at `x` and an affine simplex `Δ` around `e x`
positively oriented for the orientation of the model space; so `φ` preserves orientations when
`φ ∘ e⁻¹ ∘ Δ` and `e'⁻¹ ∘ Δ'` have the same class in `H_n(M', M' - φ x; ℤ)` for all such
charts and simplices at `x` and at `φ x`.

The proof is local. At `x' = φ x`, `μ_M` restricted to a coordinate ball at `x` is locally the
class of an oriented simplex `e⁻¹ ∘ Δ` small enough to lie in that ball; by excision
(`IsLocallyClassOf.of_restrict`) so is `μ_M`; push-forward along the injective proper map `φ`
makes `φ_* μ_M` locally the class of `φ ∘ e⁻¹ ∘ Δ` at `x'`, hence of `e'⁻¹ ∘ Δ'`; and
restriction to the coordinate ball of `e'` gives the defining property of `μ_{M'}`.

## Main definitions

* `MMP.FundamentalClass.IsLocallyHomologous`: two singular simplices have the
  same class in the local homology `H_n(X, X - x; ℤ)`.
* `MMP.IsOrientationPreserving`: orientation-preserving homeomorphisms of oriented
  manifolds.

## Main results

* `MMP.ThomClass.exists_isOrientedSimplexAroundZero_subset`: arbitrarily small
  oriented simplices around a point.
* `MMP.FundamentalClass.IsLocallyClassOf.of_isLocallyHomologous`: local classes
  depend only on the local homology class of the simplex.
* `MMP.IsFundamentalClass.pushforward_homeomorph`: `φ_* μ_M = μ_{M'}`.

## Implementation notes

As for `IsFundamentalClass`, the orientations of `M` and `M'` are given by bases `b`, `b'` of the
model spaces together with the atlases. The local homology relation is stated with integer
coefficients at the level of chains: `σ₁ - σ₂ = ∂ c + d` with `d` a chain of `M' - φ x`; it then
holds for every coefficient ring. Fulton's `μ_{M'}` is the class with the defining property of
`IsFundamentalClass`, so the statement is that `φ_* μ_M` has that property.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Filter Finsupp
open MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass

universe u

namespace MMP

namespace ThomClass

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} {b : Module.Basis (Fin n) ℝ V}

/-- A positive multiple of an oriented simplex around `0` is an oriented simplex around `0`. -/
lemma IsOrientedSimplexAroundZero.smul {v : Fin (n + 1) → V}
    (h : IsOrientedSimplexAroundZero b v) {c : ℝ} (hc : 0 < c) :
    IsOrientedSimplexAroundZero b (c • v) := by
  obtain ⟨⟨t, ht0, ht1, htv⟩, hdet⟩ := h
  refine ⟨⟨t, ht0, ht1, ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_comm (t _) c]
    rw [← Finset.smul_sum, htv, smul_zero]
  · have : (fun k : Fin n ↦ (c • v) k.succ - (c • v) 0) = fun k ↦ c • (v k.succ - v 0) := by
      funext k
      simp [smul_sub]
    rw [this, AlternatingMap.map_smul_univ]
    simpa using mul_pos (pow_pos hc n) hdet

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- Every neighbourhood of a point `p` contains an affine simplex around `p`, positively
oriented for the orientation of `b`. -/
lemma exists_isOrientedSimplexAroundZero_subset (b : Module.Basis (Fin n) ℝ V) (p : V)
    {W : Set V} (hW : W ∈ 𝓝 p) :
    ∃ v : Fin (n + 1) → V, IsOrientedSimplexAroundZero b (fun k ↦ v k - p) ∧
      range (affineSimplex v) ⊆ W := by
  obtain ⟨w, hw⟩ := exists_isOrientedSimplexAroundZero b
  have hev : ∀ᶠ c : ℝ in 𝓝 0, ∀ t ∈ stdSimplex ℝ (Fin (n + 1)),
      p + c • ∑ k, t k • w k ∈ W := by
    refine (isCompact_stdSimplex ℝ (Fin (n + 1))).eventually_forall_of_forall_eventually
      fun t _ ↦ ?_
    have hcont : Continuous fun z : ℝ × (Fin (n + 1) → ℝ) ↦ p + z.1 • ∑ k, z.2 k • w k :=
      continuous_const.add (continuous_fst.smul (continuous_finset_sum _ fun k _ ↦
        ((continuous_apply k).comp continuous_snd).smul continuous_const))
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨c, hcW, hc⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  refine ⟨fun k ↦ p + c • w k, ?_, ?_⟩
  · have : (fun k ↦ (p + c • w k) - p) = c • w := by
      funext k
      simp
    rw [this]
    exact hw.smul hc
  · rintro _ ⟨t, rfl⟩
    rw [affineSimplex_apply]
    have hsum : ∑ k, (t : Fin (n + 1) → ℝ) k = 1 := t.2.2
    have : ∑ k, (t : Fin (n + 1) → ℝ) k • (p + c • w k) =
        p + c • ∑ k, (t : Fin (n + 1) → ℝ) k • w k := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul,
        Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ smul_comm _ _ _
    rw [this]
    exact hcW t t.2

end ThomClass

namespace FundamentalClass

section Homologous

variable {X : Type*} [TopologicalSpace X]

/-- Two singular `n`-simplices `σ₁`, `σ₂` of `X` have the same class in the local homology
`H_n(X, X - x; ℤ)`: `σ₁ - σ₂ = ∂ c + d` for an integral chain `c` and an integral chain `d` of
`X - x`. -/
def IsLocallyHomologous (x : X) {n : ℕ} (σ₁ σ₂ : Simplex X n) : Prop :=
  ∃ (c : Chain ℤ X (n + 1)) (d : Chain ℤ X n), d ∈ inside ℤ n ({x}ᶜ : Set X) ∧
    single σ₁ 1 - single σ₂ 1 = bd ℤ n c + d

namespace IsLocallyHomologous

variable {x : X} {n : ℕ} {σ₁ σ₂ σ₃ : Simplex X n}

/-- Every singular simplex is locally homologous to itself. -/
@[refl]
lemma refl (x : X) (σ : Simplex X n) : IsLocallyHomologous x σ σ :=
  ⟨0, 0, zero_mem _, by simp⟩

/-- Local homology of singular simplices at `x` is symmetric. -/
lemma symm (h : IsLocallyHomologous x σ₁ σ₂) : IsLocallyHomologous x σ₂ σ₁ := by
  obtain ⟨c, d, hd, h⟩ := h
  refine ⟨-c, -d, neg_mem hd, ?_⟩
  rw [map_neg, ← neg_add, ← h, neg_sub]

/-- Local homology of singular simplices at `x` is transitive. -/
lemma trans (h₁ : IsLocallyHomologous x σ₁ σ₂) (h₂ : IsLocallyHomologous x σ₂ σ₃) :
    IsLocallyHomologous x σ₁ σ₃ := by
  obtain ⟨c₁, d₁, hd₁, h₁⟩ := h₁
  obtain ⟨c₂, d₂, hd₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, d₁ + d₂, add_mem hd₁ hd₂, ?_⟩
  rw [map_add, ← sub_add_sub_cancel _ (single σ₂ 1), h₁, h₂]
  abel

/-- Locally homologous simplices take the same value on every relative cocycle of
`(X, X - x)`, for any coefficient ring. -/
lemma apply_eq {R : Type*} [CommRing R] (h : IsLocallyHomologous x σ₁ σ₂)
    {φ : Simplex X n → R} (hφ : φ ∈ relCocycles R ({x}ᶜ : Set X) n) : φ σ₁ = φ σ₂ := by
  obtain ⟨c, d, hd, h⟩ := h
  have hδ : coboundary R n φ = 0 := hφ.2
  have := congrArg (linearCombination ℤ φ) h
  rw [map_sub, map_add, linearCombination_single, linearCombination_single, one_smul, one_smul,
    linearCombination_int_bd, hδ, linearCombination_zero, LinearMap.zero_apply, zero_add,
    linearCombination_int_eq_zero_of_mem_inside hφ.1 hd] at this
  exact sub_eq_zero.1 this

end IsLocallyHomologous

end Homologous

variable {R : Type u} [CommRing R]

/-- A class that is locally the class of `σ₁` at `x` is locally the class of every simplex
locally homologous to `σ₁`. -/
lemma IsLocallyClassOf.of_isLocallyHomologous {X : TopCat.{u}} {n : ℕ}
    {ν : borelMooreHomology R (ModuleCat.of R R) X n} {x : X} {σ₁ σ₂ : Simplex X n}
    (h : IsLocallyClassOf R ν x σ₁) (hσ : IsLocallyHomologous x σ₁ σ₂) :
    IsLocallyClassOf R ν x σ₂ := fun z hz φ hφ ↦ (h z hz φ hφ).trans (hσ.apply_eq hφ)

end FundamentalClass

open FundamentalClass

section Manifold

variable {H H' : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] [AddCommGroup H'] [Module ℝ H'] [TopologicalSpace H'] [ContinuousAdd H']
  [ContinuousSMul ℝ H'] {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace H M] [ChartedSpace H' M']

/-- A homeomorphism `φ : M ≃ₜ M'` of real `n`-manifolds, oriented in their charts by the bases
`b` of `H` and `b'` of `H'`, is *orientation preserving* if it carries the local orientation of
`M` at every point `x` to that of `M'` at `φ x`: for charts `e` of `M` at `x` and `e'` of `M'` at
`φ x`, and affine simplices `Δ` around `e x` and `Δ'` around `e' (φ x)` positively oriented for
`b` and `b'`, the simplices `φ ∘ e⁻¹ ∘ Δ` and `e'⁻¹ ∘ Δ'` have the same class in
`H_n(M', M' - φ x; ℤ)`. -/
def IsOrientationPreserving {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (b' : Module.Basis (Fin n) ℝ H') (φ : M ≃ₜ M') : Prop :=
  ∀ e ∈ atlas H M, ∀ e' ∈ atlas H' M', ∀ x ∈ e.source, φ x ∈ e'.source →
    ∀ (v : Fin (n + 1) → H), IsOrientedSimplexAroundZero b (fun k ↦ v k - e x) →
    ∀ (hv : range (affineSimplex v) ⊆ e.target) (v' : Fin (n + 1) → H'),
      IsOrientedSimplexAroundZero b' (fun k ↦ v' k - e' (φ x)) →
    ∀ (hv' : range (affineSimplex v') ⊆ e'.target),
      IsLocallyHomologous (X := M') (φ x)
        ((φ : C(M, M')).comp (inclChainSimplex (chartOpens e) (chartSimplex e v hv)))
        (inclChainSimplex (chartOpens e') (chartSimplex e' v' hv'))

variable [T2Space M] [T2Space M'] (R : Type u) [CommRing R]

/-- **Fundamental classes under orientation-preserving homeomorphisms** (Fulton, §19.1). Let
`φ : M → M'` be an orientation-preserving homeomorphism of oriented real `n`-manifolds. Then
`φ_* μ_M = μ_{M'}`. -/
theorem IsFundamentalClass.pushforward_homeomorph {n : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {b' : Module.Basis (Fin n) ℝ H'}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (hμ : IsFundamentalClass R b μ) (φ : M ≃ₜ M') (hφ : IsOrientationPreserving b b' φ) :
    IsFundamentalClass R b'
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap n μ) := by
  intro e' he' x' v' hv' hvt'
  set y : M := φ.symm x'.1
  have hxy : φ y = x'.1 := φ.apply_symm_apply x'.1
  set e := chartAt H y
  have hy : y ∈ e.source := mem_chart_source H y
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e y)
    (e.open_target.mem_nhds (e.map_source hy))
  have h0 := hμ e (chart_mem_atlas H y) ⟨y, hy⟩ v hv hvt
  have h1 := IsLocallyClassOf.of_restrict (chartOpens e) h0
  have h2 := IsLocallyClassOf.pushforward (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap
    (fun z hz ↦ φ.injective hz) h1
  have hφy : φ y ∈ e'.source := hxy ▸ x'.2
  have hv'' : IsOrientedSimplexAroundZero b' (fun k ↦ v' k - e' (φ y)) := by
    rw [hxy]
    exact hv'
  have h3 := h2.of_isLocallyHomologous
    (hφ e (chart_mem_atlas H y) e' he' y hy hφy v hv hvt v' hv'' hvt')
  have h3' : IsLocallyClassOf R (borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap n μ) x'.1
      (inclChainSimplex (chartOpens e') (chartSimplex e' v' hvt')) := hxy ▸ h3
  exact IsLocallyClassOf.restrict (chartOpens e') h3'

end Manifold

end MMP
