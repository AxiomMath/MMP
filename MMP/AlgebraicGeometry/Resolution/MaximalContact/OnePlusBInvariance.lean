module
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.RingTheory.PowerSeries.CompleteLocalRing
public import MMP.RingTheory.PowerSeries.Derivations
public import MMP.RingTheory.Ideal.KrullIntersectionClosed
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.OnePlusBAutomorphism
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Descent.IdealSheafFpqcDescent

/-!
# Kollár's resolution: chart derivatives, automorphisms of the form `1 + B`, globalization

This file collects results from Kollár's *Lectures on resolution of singularities*, §3.7–3.10.

* The logarithmic derivatives `x_j ∂/∂x_j` in the directions of the centre transform on a
  blow-up chart as `π^*(x_j ∂f/∂x_j) = y_ℓ^m y_j ∂g/∂y_j` (Kollár (3.75.4)).
* The formal inverse function theorem: a substitution `f ↦ f(g₁, …, gₙ)` of `K⟦x₁, …, xₙ⟧` is an
  automorphism iff the linear parts of the `gᵢ` are linearly independent, iff it is bijective on
  `𝔪/𝔪²` (Kollár, Notation 3.93).
* For general `λ`, `xᵢ ↦ xᵢ + λᵢ bᵢ` is an automorphism of the form `1 + B` (Notation 3.93).
* An ideal `I` is invariant under all automorphisms of the form `1 + B` iff `B · D(I) ⊆ I`, iff
  `B^j · D^j(I) ⊆ I` for all `j` (Prop. 3.94).
* Blow-up sequence functors commuting with smooth surjections globalize (Thm. 3.105).

## Main results

* `MMP.Resolution.Kollar.appLE_mul_partialDerivative_eq_pow_mul_mul_partialDerivative_of_ne`
* `MMP.Flips.ResolutionInputs.tfae_bijective_substAlgHom`
* `MMP.Resolution.exists_isAutomorphismOfFormOnePlus_add_smul`
* `MMP.Resolution.Kollar.mul_derivativeIdealOfRing_le_of_image_subst_subset`
* `MMP.Resolution.Kollar.tfae_image_subst_eq_of_isAutomorphismOfFormOnePlus`
* `MMP.Resolution.Kollar.exists_pullback_eq_of_commutes_with_surjections`

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007]
-/

@[expose] public section

/-!
## Logarithmic derivatives of a chart transform in the directions of the centre (Kollár (3.75.4))

Let `X` be a scheme over a field `k`, `Z ⊆ X` a closed subscheme and `π : B_Z X → X` its
blow-up. Let `x_1, …, x_n` be local coordinates on an open `U ⊆ X` whose first `r` generate the
ideal of `Z` on `U`, and on the chart `U_ℓ` (`ℓ ≤ r`) let `y_i = x_i / x_ℓ` (`i ≤ r`, `i ≠ ℓ`)
and `y_i = π^*x_i` (`i = ℓ` or `i > r`) be the chart coordinates. If `f ∈ 𝒪_X(U)` and
`g ∈ 𝒪(U_ℓ)` satisfy `π^*f = y_ℓ^m g`, then for every `j ≤ r`, `j ≠ ℓ`, the logarithmic
derivative `x_j ∂/∂x_j` transforms as
`π^*(x_j ∂f/∂x_j) = y_ℓ^m y_j ∂g/∂y_j` on `U_ℓ`.

### Main results

* `MMP.Resolution.Kollar.appLE_mul_partialDerivative_eq_pow_mul_mul_partialDerivative_of_ne`.

### Implementation notes

The identity is stated on every affine open `W ⊆ U_ℓ` lying over an affine open `W' ⊆ U`, the
derivatives being read there (`MMP.Resolution.partialDerivative`); such `W` cover `U_ℓ`. The
function `g` is any section with `π^*f = y_ℓ^m g`, i.e. any representative of the chart
transform `MMP.Resolution.BlowupChartData.chartTransform`. Unlike (3.75.1), no condition
`m ≥ 1` is needed: since `π^*x_j = y_j y_ℓ` the factor `y_ℓ` produced by the chain rule is
absorbed by `y_j`, and no cancellation takes place.

### References

* [J. Kollár, *Lectures on resolution of singularities*, (3.75.4)]
-/

universe u

namespace MMP.Resolution.Kollar

open CategoryTheory AlgebraicGeometry MMP.Resolution MMP.Flips.ResolutionInputs

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (CommRingCat.of k)}

/-- Pulling back along `π` and restricting to `W ⊆ U_ℓ` is restriction of the chart pullback. -/
private theorem appLE_restrictSection {Z : X.IdealSheafData} (c : BlowupChartData Z)
    (ℓ : Fin c.r) (W' : X.affineOpens) (hW' : W'.1 ≤ c.U) (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ c.chart ℓ) (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1) (s : Γ(X, c.U)) :
    ((blowUpToBase Z).appLE W'.1 W.1 hWW').hom (restrictSection W' hW' s) =
      restrictSection W hW (c.chartPullback ℓ s) := by
  rw [BlowupChartData.chartPullback, restrictSection, restrictSection,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map]

/-- A coordinate `x_l` is a constant for `∂/∂x_j` when `j ≠ l`:
`∂(x_l f)/∂x_j = x_l ∂f/∂x_j`. -/
private theorem partialDerivative_coordinate_mul {U : X.Opens} {n : ℕ} {x : Fin n → Γ(X, U)}
    (hx : IsLocalCoordinatesOn sX U x) (W : X.affineOpens) (hW : W.1 ≤ U) {j l : Fin n}
    (hjl : j ≠ l) (f : Γ(X, U)) :
    partialDerivative hx W hW j (restrictSection W hW (x l * f)) =
      restrictSection W hW (x l) * partialDerivative hx W hW j (restrictSection W hW f) := by
  letI := MMP.Mori.sectionAlgebra sX W.1
  rw [restrictSection, map_mul, ← restrictSection, ← restrictSection,
    ← Bridges.partialDerivation_apply, Derivation.leibniz, Bridges.partialDerivation_apply,
    Bridges.partialDerivation_apply, Bridges.partialDerivative_restrictSection_coordinate,
    if_neg hjl, smul_zero, add_zero, smul_eq_mul]

end

/-- **Kollár (3.75.4).** Let `x_1, …, x_n` be local coordinates on `U` whose first `r` generate
the centre `Z`, and `y = chartCoordinates c x ℓ` the coordinates of the chart `U_ℓ` of the
blow-up `π : B_Z X → X`. If `π^*f = y_ℓ^m g`, then for `j ≤ r`, `j ≠ ℓ`,
`π^*(x_j ∂f/∂x_j) = y_ℓ^m y_j ∂g/∂y_j` on every affine open `W ⊆ U_ℓ` over an affine open
`W' ⊆ U`. -/
@[mmp "lem_kr3d_chart_log_derivative_index_below"]
public theorem appLE_mul_partialDerivative_eq_pow_mul_mul_partialDerivative_of_ne
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Z : X.IdealSheafData}
    (c : BlowupChartData Z) {n : ℕ} {x : Fin n → Γ(X, c.U)} (hx : IsLocalCoordinatesOn sX c.U x)
    (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
    (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
    {f : Γ(X, c.U)} {g : Γ(blowUp Z, c.chart ℓ)} {m : ℕ}
    (hfg : c.chartPullback ℓ f = c.chartPullback ℓ (c.x ℓ) ^ m * g)
    {j : Fin c.r} (hjℓ : j ≠ ℓ)
    (W' : X.affineOpens) (hW' : W'.1 ≤ c.U) (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ c.chart ℓ) (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1) :
    ((blowUpToBase Z).appLE W' W hWW').hom
        (restrictSection W' hW' (x (Fin.castLE hrn j)) *
          partialDerivative hx W' hW' (Fin.castLE hrn j) (restrictSection W' hW' f)) =
      restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) ^ m *
        (restrictSection W hW (chartCoordinates c x ℓ (Fin.castLE hrn j)) *
          partialDerivative hy W hW (Fin.castLE hrn j) (restrictSection W hW g)) := by
  have hfg' : c.chartPullback ℓ (x (Fin.castLE hrn ℓ) * f) =
      c.chartPullback ℓ (c.x ℓ) ^ (m + 1) * g := by
    simp only [BlowupChartData.chartPullback, map_mul] at hfg ⊢
    rw [hfg, hcx ℓ]
    ring
  have key := MMP.Resolution.Kollar.appLE_partialDerivative_eq_pow_mul_partialDerivative_of_ne
    c hx hrn hcx ℓ hy (Nat.succ_pos m) hfg' hjℓ W' hW' W hW hWW'
  rw [partialDerivative_coordinate_mul hx W' hW' (Fin.castLE_injective hrn |>.ne hjℓ), map_mul,
    appLE_restrictSection c ℓ W' hW' W hW, ← hcx ℓ, Nat.succ_sub_one] at key
  rw [map_mul, appLE_restrictSection c ℓ W' hW' W hW, ← hcx j,
    chartPullback_eq_chartFraction_mul c ℓ j,
    ← chartCoordinates_castLE_of_ne c x hrn hjℓ, restrictSection, map_mul, ← restrictSection,
    ← restrictSection]
  linear_combination restrictSection W hW (chartCoordinates c x ℓ (Fin.castLE hrn j)) * key

end MMP.Resolution.Kollar

/-!
## The formal inverse function theorem

Let `K` be a field and `R = K⟦x₁, …, xₙ⟧` with maximal ideal `𝔪`. For `g = (g₁, …, gₙ) ∈ 𝔪ⁿ`, the
substitution `g^* : f ↦ f(g₁, …, gₙ)` is a local `K`-algebra endomorphism of `R`. It is an
automorphism if and only if the linear parts of `g₁, …, gₙ` are `K`-linearly independent, if and
only if the `K`-linear map it induces on the cotangent space `𝔪/𝔪²` is bijective.

### Main results

* `MMP.Flips.ResolutionInputs.tfae_bijective_substAlgHom`: the three conditions above are
  equivalent.

### Implementation notes

The substitution is Mathlib's `MvPowerSeries.substAlgHom`. The linear part of `gᵢ` is the vector
`(coeff (single j 1) gᵢ)ⱼ ∈ Kⁿ`. The map on `𝔪/𝔪²` is `Ideal.mapCotangent`, which is `K`-linear.
No assumption on the characteristic of `K` is needed.

### References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.93]
-/

namespace MMP.Flips.ResolutionInputs

open IsLocalRing MvPowerSeries

section

variable {K : Type*} [Field K] {n : ℕ}

/-- An element of `K⟦x⟧` lies in `𝔪` iff its constant coefficient vanishes. -/
private lemma mem_maximalIdeal_iff_constantCoeff_eq_zero {f : MvPowerSeries (Fin n) K} :
    f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ↔ constantCoeff f = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

/-- Each variable lies in the maximal ideal. -/
private lemma X_mem_maximalIdeal' (i : Fin n) :
    (X i : MvPowerSeries (Fin n) K) ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
  rw [mem_maximalIdeal_iff_constantCoeff_eq_zero]
  simp

/-- The linear parts of the variables form the identity matrix. -/
private lemma coeff_single_X (k i : Fin n) :
    coeff (Finsupp.single k 1) (X i : MvPowerSeries (Fin n) K) =
      (1 : Matrix (Fin n) (Fin n) K) i k := by
  rw [coeff_X, Matrix.one_apply]
  by_cases h : i = k
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h'
    exact h ((Finsupp.single_left_inj one_ne_zero).mp h').symm

/-- An element of `𝔪²` has no linear part. -/
private lemma coeff_single_eq_zero_of_mem_sq {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2) (j : Fin n) :
    coeff (Finsupp.single j 1) f = 0 := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X,
    Stacks.MvPowerSeries.RegularParameters.mem_pow_span_range_X_iff] at hf
  refine hf _ ?_
  simp [Finsupp.single_apply]

/-- Elements congruent modulo `𝔪²` have the same linear parts. -/
private lemma coeff_single_eq_of_sub_mem_sq {u v : MvPowerSeries (Fin n) K}
    (h : u - v ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2) (j : Fin n) :
    coeff (Finsupp.single j 1) u = coeff (Finsupp.single j 1) v := by
  simpa [sub_eq_zero] using coeff_single_eq_zero_of_mem_sq h j

/-- A multi-index of total degree one is a unit vector. -/
private lemma eq_single_of_sum_eq_one {d : Fin n →₀ ℕ} (h : ∑ i, d i = 1) :
    ∃ j, d = Finsupp.single j 1 := by
  have hne : d ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hne (Finsupp.ext h')
  have hle : d j ≤ 1 := h ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) (Finset.mem_univ j)
  have hj1 : d j = 1 := by omega
  have hrest : ∑ i ∈ Finset.univ.erase j, d i = 0 := by
    have := Finset.add_sum_erase Finset.univ d (Finset.mem_univ j)
    omega
  refine ⟨j, Finsupp.ext fun i => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp [hj1]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hij)]
    exact (Finset.sum_eq_zero_iff.mp hrest) i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

/-- An element of `𝔪` with no linear part lies in `𝔪²`. -/
private lemma mem_sq_of_coeff_single_eq_zero {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K))
    (h : ∀ j, coeff (Finsupp.single j 1) f = 0) :
    f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
  rw [mem_maximalIdeal_iff_constantCoeff_eq_zero] at hf
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X,
    Stacks.MvPowerSeries.RegularParameters.mem_pow_span_range_X_iff]
  intro d hd
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
  · obtain rfl : d = 0 := Finsupp.ext fun i => by
      simpa using (Finset.sum_eq_zero_iff.mp (Nat.lt_one_iff.mp hd)) i (Finset.mem_univ i)
    simpa using hf
  · obtain ⟨j, rfl⟩ := eq_single_of_sum_eq_one hd
    exact h j

/-- Two elements of `𝔪` with the same linear parts agree modulo `𝔪²`. -/
private lemma sub_mem_sq {u v : MvPowerSeries (Fin n) K}
    (hu : u ∈ maximalIdeal (MvPowerSeries (Fin n) K))
    (hv : v ∈ maximalIdeal (MvPowerSeries (Fin n) K))
    (h : ∀ j, coeff (Finsupp.single j 1) u = coeff (Finsupp.single j 1) v) :
    u - v ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 :=
  mem_sq_of_coeff_single_eq_zero (sub_mem hu hv) fun j => by rw [map_sub, h, sub_self]

/-- The linear part of `a * b`, `b ∈ 𝔪`, is the constant term of `a` times that of `b`. -/
private lemma coeff_single_mul {a b : MvPowerSeries (Fin n) K}
    (hb : b ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (j : Fin n) :
    coeff (Finsupp.single j 1) (a * b) = constantCoeff a * coeff (Finsupp.single j 1) b := by
  have ha : a - C (constantCoeff a) ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
    rw [mem_maximalIdeal_iff_constantCoeff_eq_zero]; simp
  have hsq : (a - C (constantCoeff a)) * b ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  have := coeff_single_eq_zero_of_mem_sq hsq j
  rw [sub_mul, map_sub, coeff_C_mul, sub_eq_zero] at this
  exact this

/-- A substitution by elements of `𝔪` preserves constant coefficients. -/
private lemma constantCoeff_substAlgHom {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (f : MvPowerSeries (Fin n) K) :
    constantCoeff (substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg) f) = constantCoeff f := by
  set φ := MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)
  have hcomp : (MvPowerSeries.constantCoeff (σ := Fin n) (R := K)).comp φ.toRingHom =
      MvPowerSeries.constantCoeff := by
    refine mvPowerSeries_hom_ext (⊥ : Ideal K) n _ _ (fun r => ?_) (fun i => ?_) (fun i => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, mvPowerSeries_C_eq_algebraMap, AlgHom.commutes]
    · simp [φ, MvPowerSeries.subst_X (hasSubst_of_mem_maximalIdeal hg),
        constantCoeff_eq_zero_of_mem_maximalIdeal (hg i)]
    · simp [φ, MvPowerSeries.subst_X (hasSubst_of_mem_maximalIdeal hg),
        constantCoeff_eq_zero_of_mem_maximalIdeal (hg i)]
  exact congrArg (fun ψ => ψ f) hcomp

/-- **The substitution on linear parts.** For `f ∈ 𝔪`, the linear part of `f(g)` is the linear
part of `f` times the matrix of linear parts of `g`. -/
private lemma coeff_single_substAlgHom {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (j : Fin n) :
    coeff (Finsupp.single j 1) (substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg) f) =
      ∑ i, coeff (Finsupp.single i 1) f * coeff (Finsupp.single j 1) (g i) := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X, Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, rfl⟩ := hf
  simp only [map_sum, map_mul, substAlgHom_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_single_mul (hg i), constantCoeff_substAlgHom hg]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [coeff_single_mul (X_mem_maximalIdeal' i), coeff_single_X, Matrix.one_apply_eq, mul_one]
  · intro k _ hk
    rw [coeff_single_mul (X_mem_maximalIdeal' k), coeff_single_X, Matrix.one_apply_ne hk, mul_zero]
  · simp

/-- A substitution by elements of `𝔪` maps `𝔪` into itself. -/
private lemma substAlgHom_mem_maximalIdeal {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg) f ∈
      maximalIdeal (MvPowerSeries (Fin n) K) := by
  simpa using substAlgHom_mem_pow hg (N := 1) (by simpa using hf)

/-- `K⟦x⟧` is `𝔪`-adically separated. -/
private lemma eq_zero_of_forall_mem_pow {x : MvPowerSeries (Fin n) K}
    (h : ∀ N, x ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ N) : x = 0 :=
  IsHausdorff.haus (inferInstance :
    IsHausdorff (maximalIdeal (MvPowerSeries (Fin n) K)) (MvPowerSeries (Fin n) K)) x fun N => by
    rw [SModEq.sub_mem, sub_zero]; simpa using h N

/-- **Endomorphisms tangent to the identity are automorphisms.** A `K`-algebra endomorphism `σ`
of `K⟦x₁, …, xₙ⟧` with `σ(xᵢ) ≡ xᵢ mod 𝔪²` is bijective. -/
private lemma bijective_of_sub_X_mem_sq (σ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hσ : ∀ i, σ (X i) - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2) :
    Function.Bijective σ := by
  set 𝔪 := maximalIdeal (MvPowerSeries (Fin n) K) with h𝔪
  have hX : ∀ i, σ (X i) ∈ 𝔪 := fun i => (Submodule.sub_mem_iff_left _
    (X_mem_maximalIdeal' i)).mp (Ideal.pow_le_self two_ne_zero (hσ i))
  have hσeq := eq_substAlgHom_of_X hX σ fun _ => rfl
  -- `σ` preserves constant coefficients.
  have S0 : ∀ r, σ r - r ∈ 𝔪 := fun r => by
    rw [h𝔪, mem_maximalIdeal_iff_constantCoeff_eq_zero, map_sub, hσeq, constantCoeff_substAlgHom hX,
      sub_self]
  -- `σ` is the identity on linear parts.
  have S1 : ∀ a ∈ 𝔪, σ a - a ∈ 𝔪 ^ 2 := fun a ha => by
    refine sub_mem_sq ((Submodule.sub_mem_iff_left _ ha).mp (S0 a)) ha fun j => ?_
    rw [hσeq, coeff_single_substAlgHom hX ha]
    simp [coeff_single_eq_of_sub_mem_sq (hσ _), coeff_single_X, Matrix.one_apply]
  have hm : ∀ a ∈ 𝔪, σ a ∈ 𝔪 := fun a ha =>
    (Submodule.sub_mem_iff_left _ ha).mp (Ideal.pow_le_self two_ne_zero (S1 a ha))
  have SN : ∀ N, ∀ f ∈ 𝔪 ^ N, σ f - f ∈ 𝔪 ^ (N + 1) := by
    intro N
    induction N with
    | zero => intro f _; simpa using S0 f
    | succ N ih =>
      intro f hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun x y hx hy => ?_)
      · have : σ (a * b) - a * b = (σ a - a) * σ b + a * (σ b - b) := by rw [map_mul]; ring
        rw [this]
        refine add_mem ?_ ?_
        · rw [pow_succ]; exact Ideal.mul_mem_mul (ih a ha) (hm b hb)
        · rw [show N + 1 + 1 = N + 2 by ring, pow_add]; exact Ideal.mul_mem_mul ha (S1 b hb)
      · have : σ (x + y) - (x + y) = (σ x - x) + (σ y - y) := by rw [map_add]; ring
        rw [this]; exact add_mem hx hy
  have hpow : ∀ N, ∀ f ∈ 𝔪 ^ N, σ f ∈ 𝔪 ^ N := fun N f hf =>
    (Submodule.sub_mem_iff_left _ hf).mp (Ideal.pow_le_pow_right (Nat.le_succ N) (SN N f hf))
  refine ⟨(injective_iff_map_eq_zero σ).mpr fun f hf => ?_, fun h => ?_⟩
  · refine eq_zero_of_forall_mem_pow fun N => ?_
    induction N with
    | zero => simp
    | succ N ih => simpa [hf] using SN N f ih
  · -- successive approximation
    let F : ℕ → MvPowerSeries (Fin n) K := fun l => Nat.rec 0 (fun _ x => x + (h - σ x)) l
    have hF : ∀ l, F (l + 1) = F l + (h - σ (F l)) := fun _ => rfl
    have he : ∀ l, h - σ (F l) ∈ 𝔪 ^ l := by
      intro l
      induction l with
      | zero => simp
      | succ l ih =>
        have : h - σ (F (l + 1)) = -(σ (h - σ (F l)) - (h - σ (F l))) := by
          rw [hF, map_add]; ring
        rw [this]; exact neg_mem (SN l _ ih)
    have hcauchy : ∀ {m l : ℕ}, m ≤ l → F l - F m ∈ 𝔪 ^ m := by
      intro m l hml
      induction l, hml using Nat.le_induction with
      | base => simp
      | succ l hml ih =>
        have : F (l + 1) - F m = (F l - F m) + (h - σ (F l)) := by rw [hF]; ring
        rw [this]
        exact add_mem ih (Ideal.pow_le_pow_right hml (he l))
    have hK : IsAdicComplete (maximalIdeal K) K := by rw [maximalIdeal_eq_bot]; infer_instance
    have hcomp := (MvPowerSeries.isAdicComplete_maximalIdeal n K hK).toIsPrecomplete
    obtain ⟨L, hL⟩ := hcomp.prec (f := F) fun {m l} hml => by
      rw [SModEq.sub_mem]
      have := neg_mem (hcauchy hml)
      simpa using this
    refine ⟨L, (sub_eq_zero.mp (eq_zero_of_forall_mem_pow fun N => ?_)).symm⟩
    have hLN : F N - L ∈ 𝔪 ^ N := by
      have := hL N
      rw [SModEq.sub_mem] at this
      simpa using this
    have : h - σ L = (h - σ (F N)) + σ (F N - L) := by rw [map_sub]; ring
    rw [this]
    exact add_mem (he N) (hpow N _ hLN)

/-- Transport of bijectivity along two surjections with the same fibres. -/
private lemma bijective_of_bijective_of_fibres {X Y Z : Type*} {T : X → Y} {L : X → Z}
    (hT : Function.Surjective T) (hL : Function.Surjective L)
    (hTL : ∀ x y, T x = T y ↔ L x = L y) {F : X → X} {M : Y → Y} {N : Z → Z}
    (hM : ∀ x, M (T x) = T (F x)) (hN : ∀ x, N (L x) = L (F x)) (h : Function.Bijective M) :
    Function.Bijective N := by
  refine ⟨fun z₁ z₂ hz => ?_, fun z => ?_⟩
  · obtain ⟨x₁, rfl⟩ := hL z₁
    obtain ⟨x₂, rfl⟩ := hL z₂
    rw [hN, hN, ← hTL, ← hM, ← hM] at hz
    exact (hTL _ _).mp (h.1 hz)
  · obtain ⟨x, rfl⟩ := hL z
    obtain ⟨y, hy⟩ := h.2 (T x)
    obtain ⟨x', rfl⟩ := hT y
    rw [hM, hTL] at hy
    exact ⟨L x', by rw [hN, hy]⟩

/-- The element `∑ⱼ vⱼ xⱼ` of `𝔪` with linear part `v`. -/
private lemma exists_mem_coeff_single (v : Fin n → K) :
    ∃ f ∈ maximalIdeal (MvPowerSeries (Fin n) K), ∀ k, coeff (Finsupp.single k 1) f = v k := by
  refine ⟨∑ j, C (v j) * X j, Ideal.sum_mem _ fun j _ =>
    Ideal.mul_mem_left _ _ (X_mem_maximalIdeal' j), fun k => ?_⟩
  rw [map_sum, Finset.sum_eq_single k]
  · rw [coeff_C_mul, coeff_single_X, Matrix.one_apply_eq, mul_one]
  · intro j _ hj
    rw [coeff_C_mul, coeff_single_X, Matrix.one_apply_ne hj, mul_zero]
  · simp

end

variable {K : Type*} [Field K] {n : ℕ}

/-- **Formal inverse function theorem.** For `g₁, …, gₙ` in the maximal ideal of `K⟦x₁, …, xₙ⟧`,
the following are equivalent: the substitution `f ↦ f(g₁, …, gₙ)` is bijective; the linear parts of
the `gᵢ` are `K`-linearly independent; the substitution induces a bijection on `𝔪/𝔪²`. -/
@[mmp "lem_kr3d_power_series_substitution_automorphism"]
public theorem tfae_bijective_substAlgHom {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    List.TFAE
      [Function.Bijective (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)),
        LinearIndependent K fun i (j : Fin n) =>
          MvPowerSeries.coeff (Finsupp.single j 1) (g i),
        Function.Bijective
          (Ideal.mapCotangent (maximalIdeal (MvPowerSeries (Fin n) K))
            (maximalIdeal (MvPowerSeries (Fin n) K))
            (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg))
            (haveI : IsLocalHom
                (MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg)).toRingHom :=
              ⟨(isLocalHom_substAlgHom hg).map_nonunit⟩
             (maximalIdeal_comap
              (MvPowerSeries.substAlgHom (R := K)
                (hasSubst_of_mem_maximalIdeal hg)).toRingHom).ge))] := by
  set φ := MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hg) with hφ
  set A : Matrix (Fin n) (Fin n) K := fun i j => coeff (Finsupp.single j 1) (g i) with hA
  have hrows : (LinearIndependent K fun i (j : Fin n) =>
      MvPowerSeries.coeff (Finsupp.single j 1) (g i)) ↔ IsUnit A :=
    Matrix.linearIndependent_rows_iff_isUnit
  have hφm : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) K), φ f ∈ maximalIdeal _ :=
    fun _ => substAlgHom_mem_maximalIdeal hg
  have hlin : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) K), ∀ k,
      coeff (Finsupp.single k 1) (φ f) =
        Matrix.vecMul (fun j => coeff (Finsupp.single j 1) f) A k :=
    fun f hf k => coeff_single_substAlgHom hg hf k
  tfae_have 1 → 2 := by
    intro hb
    let e := AlgEquiv.ofBijective φ hb
    have hφe : ∀ i, φ (e.symm (X i)) = X i := fun i => e.apply_symm_apply (X i)
    have hhm : ∀ i, e.symm (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K) := fun i => by
      by_contra hn
      rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hn
      have := hn.map φ
      rw [hφe] at this
      exact X_mem_maximalIdeal' (K := K) i this
    let H : Matrix (Fin n) (Fin n) K := fun i j => coeff (Finsupp.single j 1) (e.symm (X i))
    have hHA : H * A = 1 := by
      ext i k
      rw [← coeff_single_X, ← hφe i, hlin _ (hhm i)]
      rfl
    exact hrows.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_left_inverse hHA))
  tfae_have 2 → 1 := by
    intro hli
    have hdet := (Matrix.isUnit_iff_isUnit_det A).mp (hrows.mp hli)
    set B := A⁻¹
    have hBA : B * A = 1 := Matrix.nonsing_inv_mul _ hdet
    have hAB : A * B = 1 := Matrix.mul_nonsing_inv _ hdet
    choose ℓ hℓm hℓc using fun i => exists_mem_coeff_single (K := K) (B i)
    set Λ := MvPowerSeries.substAlgHom (R := K) (hasSubst_of_mem_maximalIdeal hℓm)
    have hσ := bijective_of_sub_X_mem_sq (φ.comp Λ) fun i => by
      rw [AlgHom.comp_apply, substAlgHom_X]
      refine sub_mem_sq (hφm _ (hℓm i)) (X_mem_maximalIdeal' i) fun k => ?_
      rw [hlin _ (hℓm i), coeff_single_X, ← hBA]
      simp only [hℓc]
      rfl
    have hτ := bijective_of_sub_X_mem_sq (Λ.comp φ) fun i => by
      rw [AlgHom.comp_apply, substAlgHom_X]
      refine sub_mem_sq (substAlgHom_mem_maximalIdeal hℓm (hg i)) (X_mem_maximalIdeal' i)
        fun k => ?_
      rw [coeff_single_substAlgHom hℓm (hg i), coeff_single_X, ← hAB]
      simp only [hℓc]
      rfl
    refine ⟨fun x y hxy => hτ.1 (congrArg Λ hxy), fun y => ?_⟩
    obtain ⟨x, rfl⟩ := hσ.2 y
    exact ⟨Λ x, rfl⟩
  tfae_have 2 ↔ 3 := by
    let T := (maximalIdeal (MvPowerSeries (Fin n) K)).toCotangent
    let Lf : maximalIdeal (MvPowerSeries (Fin n) K) → Fin n → K :=
      fun x j => coeff (Finsupp.single j 1) (x : MvPowerSeries (Fin n) K)
    let F : maximalIdeal (MvPowerSeries (Fin n) K) → maximalIdeal (MvPowerSeries (Fin n) K) :=
      fun x => ⟨φ x, hφm x x.2⟩
    have hTL : ∀ x y, T x = T y ↔ Lf x = Lf y := fun x y => by
      rw [Ideal.toCotangent_eq]
      exact ⟨fun h => funext (coeff_single_eq_of_sub_mem_sq h),
        fun h => sub_mem_sq x.2 y.2 (congrFun h)⟩
    have hLs : Function.Surjective Lf := fun v => by
      obtain ⟨f, hf, hfv⟩ := exists_mem_coeff_single (K := K) v
      exact ⟨⟨f, hf⟩, funext hfv⟩
    have hN : ∀ x, Matrix.vecMul (Lf x) A = Lf (F x) := fun x => funext fun k =>
      (hlin x x.2 k).symm
    rw [hrows]
    constructor
    · intro hu
      exact bijective_of_bijective_of_fibres (M := fun v => Matrix.vecMul v A) hLs
        (Ideal.toCotangent_surjective _)
        (fun x y => (hTL x y).symm) hN (fun x => Ideal.mapCotangent_toCotangent _ _ _ _ x)
        ⟨Matrix.vecMul_injective_iff_isUnit.mpr hu, Matrix.vecMul_surjective_iff_isUnit.mpr hu⟩
    · intro hb
      exact Matrix.vecMul_injective_iff_isUnit.mp (bijective_of_bijective_of_fibres
        (N := fun v => Matrix.vecMul v A)
        (Ideal.toCotangent_surjective _) hLs hTL
        (fun x => Ideal.mapCotangent_toCotangent _ _ _ _ x) hN hb).1
  tfae_finish

end MMP.Flips.ResolutionInputs

/-!
## Automorphisms `xᵢ ↦ xᵢ + λᵢ bᵢ` for general `λ`

Let `k ⊆ K` be fields, `R = K⟦x₁, …, xₙ⟧` with maximal ideal `𝔪`, `B` an ideal of `R` and
`b₁, …, bₙ ∈ B ∩ 𝔪`. For `λ` in a Zariski open neighbourhood of `0` in `𝔸ⁿ_k`, the substitution
`xᵢ ↦ xᵢ + λᵢ bᵢ` is an automorphism of `R` of the form `1 + B`. The open set is a basic open
`{N ≠ 0}` for a polynomial `N ∈ k[λ₁, …, λₙ]` with `N(0) ≠ 0`; it contains `0`, hence is nonempty.

### Main results

* `MMP.Resolution.exists_isAutomorphismOfFormOnePlus_add_smul`: the statement above.

### Implementation notes

The Zariski open subset `Λ ⊆ 𝔸ⁿ_k` containing `0` is given by a polynomial `N` with
`N(0) ≠ 0`, and membership of `λ ∈ kⁿ` in `Λ` is `N(λ) ≠ 0`; every open neighbourhood of `0`
contains such a basic open one, so this is the same statement. No assumption on the
characteristic of `k` or on the degree of `K/k` is needed.

### References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.93]
-/

namespace MMP.Resolution

section

/-- The matrix of linear parts of a family of power series. -/
private noncomputable abbrev linearParts {K : Type*} [Field K] {n : ℕ}
    (b : Fin n → MvPowerSeries (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (b i)

/-- If `det(1 + diag(c) C) ≠ 0`, where `C` is the matrix of linear parts of the `bᵢ ∈ B ∩ 𝔪`, then
`xᵢ ↦ xᵢ + cᵢ bᵢ` is an automorphism of the form `1 + B`. -/
private lemma isAutomorphismOfFormOnePlus_of_det_ne_zero {k K : Type*} [Field k] [Field K]
    [Algebra k K] {n : ℕ} {B : Ideal (MvPowerSeries (Fin n) K)}
    {b : Fin n → MvPowerSeries (Fin n) K} (hbB : ∀ i, b i ∈ B)
    (hb𝔪 : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) {c : Fin n → k}
    (hdet : (1 + Matrix.diagonal (fun i => algebraMap k K (c i)) * linearParts b).det ≠ 0) :
    IsAutomorphismOfFormOnePlus B (fun i => MvPowerSeries.X i + c i • b i) := by
  have hcc : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X i + c i • b i) = 0 := fun i => by
    simp [hb𝔪 i]
  refine ⟨hcc, ?_, fun i => by simpa using Submodule.smul_of_tower_mem B (c i) (hbB i)⟩
  have hg : ∀ i, MvPowerSeries.X i + c i • b i ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K) := fun i => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      hcc i]
    exact not_isUnit_zero
  have hli : LinearIndependent K fun i (j : Fin n) =>
      MvPowerSeries.coeff (Finsupp.single j 1) (MvPowerSeries.X i + c i • b i) := by
    convert Matrix.linearIndependent_rows_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit) using 1
    ext i j
    rw [Matrix.row, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_mul, map_add,
      MvPowerSeries.coeff_X, LinearMap.map_smul_of_tower, Algebra.smul_def]
    simp only [Finsupp.single_left_inj one_ne_zero, eq_comm]
  have := ((MMP.Flips.ResolutionInputs.tfae_bijective_substAlgHom hg).out 1 2).2 hli
  rwa [MvPowerSeries.coe_substAlgHom] at this

/-- Evaluating `det(1 + diag(X) C)` at `x` gives `det(1 + diag(x) C)`. -/
private lemma eval_det_one_add_diagonal_X_mul {K : Type*} [Field K] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    MvPolynomial.eval x
        (1 + Matrix.diagonal MvPolynomial.X * C.map MvPolynomial.C).det =
      (1 + Matrix.diagonal x * C).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.diagonal_mul]

/-- Applying a `k`-linear form `φ : K → k` to the coefficients of `P ∈ K[X]` gives `N ∈ k[X]` with
`N(c) = φ(P(c))` for every `c ∈ kⁿ`. -/
private lemma exists_eval_eq_dual_eval {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (φ : Module.Dual k K) (P : MvPolynomial σ K) :
    ∃ N : MvPolynomial σ k, ∀ c : σ → k,
      MvPolynomial.eval c N = φ (MvPolynomial.eval (fun i => algebraMap k K (c i)) P) := by
  refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m (φ (P.coeff m)), fun c => ?_⟩
  simp only [map_sum, MvPolynomial.eval_monomial]
  conv_rhs => rw [MvPolynomial.eval_eq, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [← map_pow, ← map_prod, Finsupp.prod]
  rw [mul_comm (P.coeff m), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

end

/-- **Kollár, Notation 3.93.** Let `k ⊆ K` be fields, `B` an ideal of `K⟦x₁, …, xₙ⟧` and
`b₁, …, bₙ ∈ B` without constant term. There is a polynomial `N ∈ k[λ₁, …, λₙ]` with `N(0) ≠ 0`
such that for every `λ ∈ kⁿ` with `N(λ) ≠ 0` the substitution `xᵢ ↦ xᵢ + λᵢ bᵢ` is an
automorphism of the form `1 + B`. -/
@[mmp "lem_kr3d_one_plus_ideal_general_automorphism"]
public theorem exists_isAutomorphismOfFormOnePlus_add_smul {k K : Type*} [Field k] [Field K]
    [Algebra k K] {n : ℕ} (B : Ideal (MvPowerSeries (Fin n) K))
    {b : Fin n → MvPowerSeries (Fin n) K} (hbB : ∀ i, b i ∈ B)
    (hb𝔪 : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    ∃ N : MvPolynomial (Fin n) k, MvPolynomial.eval 0 N ≠ 0 ∧
      ∀ c : Fin n → k, MvPolynomial.eval c N ≠ 0 →
        IsAutomorphismOfFormOnePlus B (fun i => MvPowerSeries.X i + c i • b i) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k K, φ 1 ≠ 0 := by
    by_contra! h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff k (1 : K)).1 h)
  obtain ⟨N, hN⟩ := exists_eval_eq_dual_eval φ
    (1 + Matrix.diagonal MvPolynomial.X * (linearParts b).map MvPolynomial.C).det
  refine ⟨N, ?_, fun c hc => ?_⟩
  · simp only [hN, Pi.zero_apply, map_zero, eval_det_one_add_diagonal_X_mul]
    simpa using hφ
  · refine isAutomorphismOfFormOnePlus_of_det_ne_zero hbB hb𝔪 fun h => hc ?_
    rw [hN, eval_det_one_add_diagonal_X_mul, h, map_zero]

end MMP.Resolution

/-!
## Invariance under automorphisms of the form `1 + B` gives `B · D(I) ⊆ I`

Let `k ⊆ K` be fields, `R = K⟦x₁, …, xₙ⟧` with maximal ideal `𝔪`, viewed as a `k`-algebra, and
`D(J) = D_{R/k}(J)` the ideal generated by the `δ(f)`, `δ ∈ Der_k(R)`, `f ∈ J`. If `B ⊆ 𝔪` and
`I` are ideals of `R` and `g^*(I) ⊆ I` for every automorphism `g^*` of the form `1 + B`, then
`B · D(I) ⊆ I`. This is the implication (1) ⇒ (2) of Kollár's Prop. 3.94.

### Main results

* `MMP.Resolution.Kollar.mul_derivativeIdealOfRing_le_of_image_subst_subset`: the statement above.

### Implementation notes

The hypotheses on `k` and `K` are those the argument uses: `k` is infinite (so that infinitely
many `λ ∈ k` give automorphisms `xᵢ ↦ xᵢ + λ b`) and `K / k` is separable algebraic (so that every
`k`-derivation of `R` is a combination of the partial derivatives `∂/∂xᵢ`). A field of
characteristic `0` is infinite, and a finite extension in characteristic `0` is separable, so the
case of a finite extension of a field of characteristic `0` is included.

### References

* [J. Kollár, *Lectures on resolution of singularities*, Prop. 3.94]
-/

namespace MMP.Resolution.Kollar

open IsLocalRing MvPowerSeries

section

variable {K : Type*} [Field K] {n : ℕ}

/-- First-order Taylor expansion of a polynomial in the direction `b • eᵢ`. -/
private lemma coeff_aeval_add_X_mul (b : MvPowerSeries (Fin n) K) (i : Fin n)
    (P : MvPolynomial (Fin n) K) :
    (MvPolynomial.aeval (fun j => Polynomial.C (X j) +
        Polynomial.C (Pi.single (M := fun _ => MvPowerSeries (Fin n) K) i b j) * Polynomial.X) P :
          Polynomial (MvPowerSeries (Fin n) K)).coeff 0 = (P : MvPowerSeries (Fin n) K) ∧
    (MvPolynomial.aeval (fun j => Polynomial.C (X j) +
        Polynomial.C (Pi.single (M := fun _ => MvPowerSeries (Fin n) K) i b j) * Polynomial.X) P :
          Polynomial (MvPowerSeries (Fin n) K)).coeff 1 =
      b * pderiv (R := K) i (P : MvPowerSeries (Fin n) K) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp [pderiv_coe, MvPowerSeries.algebraMap_apply]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, MvPolynomial.coe_add, hp.1, hp.2, hq.1, hq.2,
      mul_add, and_self]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.coe_mul, MvPolynomial.coe_X,
      Derivation.leibniz, pderiv_X, mul_add, add_mul, Polynomial.coeff_add,
      Polynomial.coeff_mul_C, ← mul_assoc, Polynomial.coeff_mul_X, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · simp [Polynomial.coeff_mul_X_zero, hp.1]
    · rw [hp.1, hp.2]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [Pi.single_apply, hij, Ne.symm hij]; ring

/-- Substituting `xⱼ ↦ xⱼ + λ bⱼ` into a polynomial is evaluating the polynomial in `T` obtained by
substituting `xⱼ ↦ xⱼ + T bⱼ` at `T = λ`. -/
private lemma subst_coe_eq_eval {k : Type*} [Field k] [Algebra k K]
    (b : Fin n → MvPowerSeries (Fin n) K) (c : k) (P : MvPolynomial (Fin n) K) :
    subst (R := K) (fun j => X j + c • b j) (P : MvPowerSeries (Fin n) K) =
      (MvPolynomial.aeval (fun j => Polynomial.C (X j) + Polynomial.C (b j) * Polynomial.X) P :
          Polynomial (MvPowerSeries (Fin n) K)).eval (algebraMap k _ c) := by
  rw [subst_coe, ← Polynomial.coe_aeval_eq_eval]
  have h := congrArg (fun φ => φ P) (MvPolynomial.comp_aeval (R := K)
    (fun j => Polynomial.C (X j) + Polynomial.C (b j) * Polynomial.X)
    ((Polynomial.aeval (R := MvPowerSeries (Fin n) K)
      (algebraMap k (MvPowerSeries (Fin n) K) c)).restrictScalars K))
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  refine congrArg (fun x => MvPolynomial.aeval (R := K) x P) (funext fun j => ?_)
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.smul_def]
  rw [mul_comm]

/-- A polynomial over a `k`-algebra vanishing at infinitely many scalars is zero. -/
private lemma polynomial_eq_zero_of_infinite {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (q : Polynomial A) {S : Set k} (hS : S.Infinite)
    (h : ∀ c ∈ S, q.eval (algebraMap k A c) = 0) : q = 0 := by
  classical
  ext m
  rw [Polynomial.coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k (q.coeff m)).mp fun φ => ?_
  set p : Polynomial k := ∑ e ∈ q.support, Polynomial.monomial e (φ (q.coeff e)) with hp
  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p (hS.mono fun c hc => ?_)
    have := congrArg φ (h c hc)
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum, map_zero] at this
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hp, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial]
    rw [← this]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul,
      smul_eq_mul, mul_comm]
  have := congrArg (fun p => Polynomial.coeff p m) hp0
  simp only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero,
    Finset.sum_ite_eq', Polynomial.mem_support_iff] at this
  by_cases hm : q.coeff m = 0
  · simp [hm]
  · simpa [hm] using this

/-- A partial derivative lowers the `𝔪`-adic order by at most one. -/
private lemma pderiv_mem_pow {i : Fin n} {s : ℕ} {e : MvPowerSeries (Fin n) K}
    (he : e ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1)) :
    pderiv (R := K) i e ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ s := by
  classical
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X,
    Stacks.MvPowerSeries.RegularParameters.mem_pow_span_range_X_iff] at he ⊢
  intro d hd
  rw [coeff_pderiv, he _ ?_, zero_mul]
  simp [Finset.sum_add_distrib, Finsupp.single_apply]
  omega

/-- For `N` with `N(0) ≠ 0`, infinitely many `λ ∈ k` have `N(λ eᵢ) ≠ 0`. -/
private lemma infinite_setOf_eval_single_ne_zero {k : Type*} [Field k] [Infinite k]
    (N : MvPolynomial (Fin n) k) (hN : MvPolynomial.eval 0 N ≠ 0) (i : Fin n) :
    {c : k | MvPolynomial.eval (Pi.single i c) N ≠ 0}.Infinite := by
  classical
  set p : Polynomial k := MvPolynomial.aeval (Pi.single i Polynomial.X) N
  have hp : ∀ c, p.eval c = MvPolynomial.eval (Pi.single i c) N := by
    intro c
    rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hfun : (fun j => Polynomial.aeval c
        (Pi.single (M := fun _ => Polynomial k) i Polynomial.X j)) = Pi.single i c := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    rw [hfun, MvPolynomial.aeval_eq_eval]
  have hp0 : p ≠ 0 := by
    intro h0
    apply hN
    have := hp 0
    rw [h0, Polynomial.eval_zero, Pi.single_zero] at this
    exact this.symm
  have : {c : k | MvPolynomial.eval (Pi.single i c) N ≠ 0} = {c | p.IsRoot c}ᶜ := by
    ext c; simp [hp]
  rw [this]
  exact (Polynomial.finite_setOf_isRoot hp0).infinite_compl

/-- **The first-order condition modulo `𝔪^{s+1}`.** If substituting `xᵢ ↦ xᵢ + λ b` maps `I` into
itself for infinitely many `λ ∈ k`, where `b ∈ 𝔪`, then `b ∂f/∂xᵢ ∈ I + 𝔪^{s+1}` for `f ∈ I`. -/
private lemma mul_pderiv_mem_sup_pow {k : Type*} [Field k] [Algebra k K]
    {I : Ideal (MvPowerSeries (Fin n) K)} {S : Set k} (hS : S.Infinite)
    {b : MvPowerSeries (Fin n) K} (hb : b ∈ maximalIdeal (MvPowerSeries (Fin n) K)) {i : Fin n}
    (hσ : ∀ c ∈ S, MvPowerSeries.subst (R := K) (fun j => X j + c • Pi.single i b j) ''
      (I : Set (MvPowerSeries (Fin n) K)) ⊆ (I : Set (MvPowerSeries (Fin n) K)))
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ I) (s : ℕ) :
    b * pderiv (R := K) i f ∈ I ⊔ maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := by
  classical
  set J := I ⊔ maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1)
  obtain ⟨P, hP⟩ :=
    Stacks.MvPowerSeries.RegularParameters.exists_polynomial_sub_mem_pow_span_range_X (s + 1) f
  rw [← MvPowerSeries.maximalIdeal_eq_span_range_X] at hP
  have hQ0 : (MvPolynomial.aeval (fun j => Polynomial.C (X j) +
      Polynomial.C (Pi.single (M := fun _ => MvPowerSeries (Fin n) K) i b j) * Polynomial.X)
        P).map (Ideal.Quotient.mk J) = 0 := by
    refine polynomial_eq_zero_of_infinite (k := k) _ hS fun c hc => ?_
    rw [Polynomial.eval_map, ← Ideal.Quotient.mk_algebraMap, Polynomial.eval₂_at_apply,
      Ideal.Quotient.eq_zero_iff_mem, ← subst_coe_eq_eval]
    have hg𝔪 : ∀ j, X j + c • Pi.single (M := fun _ => MvPowerSeries (Fin n) K) i b j ∈
        maximalIdeal (MvPowerSeries (Fin n) K) := fun j => by
      refine add_mem (MMP.Flips.ResolutionInputs.mem_maximalIdeal_iff_constantCoeff_eq_zero.mpr
        (constantCoeff_X j)) ?_
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_left _ _ ?_
      rcases eq_or_ne j i with rfl | hj
      · simpa using hb
      · simp [hj]
    have ha := MMP.Flips.ResolutionInputs.hasSubst_of_mem_maximalIdeal hg𝔪
    rw [← MvPowerSeries.coe_substAlgHom ha, show (P : MvPowerSeries (Fin n) K) = f - (f - P) by
      ring, map_sub]
    exact J.sub_mem (le_sup_left (a := I) (hσ c hc ⟨f, hf, by rw [coe_substAlgHom]⟩))
      (le_sup_right (a := I) (MMP.Flips.ResolutionInputs.substAlgHom_mem_pow hg𝔪 hP))
  have h1 : b * pderiv (R := K) i (P : MvPowerSeries (Fin n) K) ∈ J := by
    rw [← (coeff_aeval_add_X_mul b i P).2, ← Ideal.Quotient.eq_zero_iff_mem,
      ← Polynomial.coeff_map, hQ0, Polynomial.coeff_zero]
  have h2 : b * pderiv (R := K) i (f - P) ∈ J :=
    le_sup_right (a := I) (pow_succ' (maximalIdeal (MvPowerSeries (Fin n) K)) s ▸
      Ideal.mul_mem_mul hb (pderiv_mem_pow hP))
  simpa [← mul_add] using J.add_mem h1 h2

/-- **The first-order condition for one partial derivative.** If `I` is stable under every
automorphism of the form `1 + B`, `b ∈ B ∩ 𝔪` and `f ∈ I`, then `b ∂f/∂xᵢ ∈ I`. -/
private lemma mul_pderiv_mem {k : Type*} [Field k] [Infinite k] [Algebra k K]
    {B I : Ideal (MvPowerSeries (Fin n) K)}
    (h : ∀ g : Fin n → MvPowerSeries (Fin n) K, MMP.Resolution.IsAutomorphismOfFormOnePlus B g →
      MvPowerSeries.subst (R := K) g '' (I : Set (MvPowerSeries (Fin n) K)) ⊆ I)
    {b : MvPowerSeries (Fin n) K} (hbB : b ∈ B)
    (hb : b ∈ maximalIdeal (MvPowerSeries (Fin n) K)) {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ I) (i : Fin n) :
    b * pderiv (R := K) i f ∈ I := by
  classical
  obtain ⟨N, hN0, hN⟩ := MMP.Resolution.exists_isAutomorphismOfFormOnePlus_add_smul (k := k) B
    (b := Pi.single i b) (fun j => by rcases eq_or_ne j i with rfl | hj <;> simp [*])
    (fun j => by
      rcases eq_or_ne j i with rfl | hj
      · simpa using MMP.Flips.ResolutionInputs.mem_maximalIdeal_iff_constantCoeff_eq_zero.mp hb
      · simp [hj])
  have hσ : ∀ c ∈ {c : k | MvPolynomial.eval (Pi.single i c) N ≠ 0},
      MvPowerSeries.subst (R := K) (fun j => X j + c • Pi.single i b j) ''
        (I : Set (MvPowerSeries (Fin n) K)) ⊆ (I : Set (MvPowerSeries (Fin n) K)) :=
      fun c hc => by
    refine h _ ?_
    convert hN (Pi.single i c) hc using 2 with j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  exact (MMP.Resolution.Bridges.eq_iInf_sup_maximalIdeal_pow I).ge <| Submodule.mem_iInf _ |>.mpr
    (mul_pderiv_mem_sup_pow (infinite_setOf_eval_single_ne_zero N hN0 i) hb hσ hf)

end

/-- **Kollár Prop. 3.94, (1) ⇒ (2).** Let `k` be an infinite field, `K / k` a separable algebraic
extension, `R = K⟦x₁, …, xₙ⟧` and `B ⊆ 𝔪`, `I` ideals of `R` such that `g^*(I) ⊆ I` for every
automorphism `g^*` of `R` of the form `1 + B` (`MMP.Resolution.IsAutomorphismOfFormOnePlus`).
Then `B · D_{R/k}(I) ⊆ I`. -/
@[mmp "lem_kr3d_first_order_condition_from_invariance"]
public theorem mul_derivativeIdealOfRing_le_of_image_subst_subset {k K : Type*} [Field k]
    [Infinite k] [Field K] [Algebra k K] [Algebra.IsSeparable k K] {n : ℕ}
    {B I : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K))
    (h : ∀ g : Fin n → MvPowerSeries (Fin n) K, IsAutomorphismOfFormOnePlus B g →
      MvPowerSeries.subst (R := K) g '' (I : Set (MvPowerSeries (Fin n) K)) ⊆ I) :
    B * derivativeIdealOfRing k I ≤ I := by
  obtain ⟨e, he⟩ := MMP.Resolution.Kollar.exists_basis_derivation_mvPowerSeries k K n
  refine Ideal.mul_le.mpr fun b hb x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, f, hf, rfl⟩ := hx
    have hδ : δ f = ∑ j, e.repr δ j * pderiv (R := K) j f := by
      conv_lhs => rw [← e.sum_repr δ]
      simp only [he]
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => simp [Finset.sum_insert ha, ih]
    rw [hδ, Finset.mul_sum]
    exact I.sum_mem fun j _ => mul_left_comm (e.repr δ j) b _ ▸
      I.mul_mem_left _ (mul_pderiv_mem (k := k) h hb (hB hb) hf j)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact I.add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact I.mul_mem_left a hx

end MMP.Resolution.Kollar

/-!
## Invariance of an ideal under automorphisms of the form `1 + B`

Let `k ⊆ K` be fields, `R = K⟦x₁, …, xₙ⟧` with maximal ideal `𝔪`, viewed as a `k`-algebra, and
`D^j(J) = D^j_{R/k}(J)` the iterated derivative ideals of an ideal `J`. For ideals `B ⊆ 𝔪` and `I`
of `R` the following are equivalent:

1. `g^*(I) = I` for every automorphism `g^*` of `R` of the form `1 + B`;
2. `B · D(I) ⊆ I`;
3. `B^j · D^j(I) ⊆ I` for every `j`.

### Main results

* `MMP.Resolution.Kollar.tfae_image_subst_eq_of_isAutomorphismOfFormOnePlus`: the equivalence.

### Implementation notes

The source works over a field `k` of characteristic `0` and a finite extension `K / k`. Here `k`
has characteristic `0` and `K / k` is separable algebraic; a finite extension in characteristic
`0` is separable, so the source's setting is included. Condition (3) is stated for every `j`,
the case `j = 0` (`B^0 · D^0(I) = I ⊆ I`) being trivial. The substitution `g^*` is
`MvPowerSeries.subst g`, and `g^*(I) = I` is the equality of the image of `I` with `I`.

### References

* [J. Kollár, *Lectures on resolution of singularities*, Prop. 3.94]
-/

namespace MMP.Resolution.Kollar

open MMP.Resolution

/-- **Kollár Prop. 3.94.** Let `k` be a field of characteristic `0`, `K / k` a separable algebraic
extension, `R = K⟦x₁, …, xₙ⟧` and `B ⊆ 𝔪`, `I` ideals of `R`. The following are equivalent:
`g^*(I) = I` for every automorphism `g^*` of `R` of the form `1 + B`
(`MMP.Resolution.IsAutomorphismOfFormOnePlus`); `B · D_{R/k}(I) ⊆ I`; and
`B^j · D^j_{R/k}(I) ⊆ I` for every `j`. -/
@[mmp "prop_kr3d_one_plus_ideal_invariance_criterion"]
public theorem tfae_image_subst_eq_of_isAutomorphismOfFormOnePlus {k K : Type*} [Field k]
    [CharZero k] [Field K] [Algebra k K] [Algebra.IsSeparable k K] {n : ℕ}
    {B I : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K)) :
    List.TFAE
      [∀ g : Fin n → MvPowerSeries (Fin n) K, IsAutomorphismOfFormOnePlus B g →
          MvPowerSeries.subst (R := K) g '' (I : Set (MvPowerSeries (Fin n) K)) = I,
        B * derivativeIdealOfRing k I ≤ I,
        ∀ j : ℕ, B ^ j * higherDerivativeIdealOfRing k I j ≤ I] := by
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  tfae_have 1 → 2 := fun h =>
    mul_derivativeIdealOfRing_le_of_image_subst_subset hB fun g hg => (h g hg).subset
  tfae_have 2 → 3 := fun h j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [higherDerivativeIdealOfRing_zero]
    · exact pow_mul_higherDerivativeIdealOfRing_le k h j hj
  tfae_have 3 → 1 := fun h g hg =>
    image_subst_eq_of_pow_mul_higherDerivativeIdealOfRing_le (fun j _ => h j) hg
  tfae_finish

end MMP.Resolution.Kollar

/-!
## Globalization of blow-up sequences

Let `𝓜` be a class of smooth morphisms of schemes which contains all open cover maps and is
closed under composition, base change and finite coproducts over a common target, and let
`𝓖𝓣 ⊇ 𝓛𝓣` be two classes of triples `(X, I, E)` of finite type over a field. Suppose that every
triple of `𝓖𝓣` is, locally around each of its points, the pull-back of a triple of `𝓛𝓣` along an
`𝓜`-morphism; that `𝓛𝓣` is closed under finite disjoint unions and under pull-back along
`𝓜`-morphisms; and that `𝓑` is a blow-up sequence functor on `𝓛𝓣` commuting with every
surjective `𝓜`-morphism between members of `𝓛𝓣`. Then every `(X, I, E) ∈ 𝓖𝓣` carries a blow-up
sequence `𝐁` starting with `X` such that `g^*𝐁 = 𝓑(X', g^*I, g⁻¹E)` for every surjective
`𝓜`-morphism `g : X' → X` with `(X', g^*I, g⁻¹E) ∈ 𝓛𝓣`.

The sequence is built from one cover `g : X' = ∐ U_α → X` by descending the centres of `𝓑(X')`
along the faithfully flat quasi-compact `g` (they agree on `X' ×_X X'`) and using that blowing
up commutes with flat base change; the comparison with any other `g` uses that a blow-up
sequence is determined by its pull-back along a flat surjection.

### Main results

* `MMP.Resolution.Kollar.exists_pullback_eq_of_commutes_with_surjections`: the globalization
  theorem (Kollár Thm. 3.105, with the hypothesis that `𝓛𝓣` is closed under pull-back by
  `𝓜`-morphisms added).

### Implementation notes

Triples are `MMP.Resolution.FieldBlowupTriple`s, which carry their ground field and structure
morphism; the pull-back of a triple along `g` is `MMP.Resolution.FieldBlowupTriple.pullback`,
over the same field. A blow-up sequence functor on `𝓛𝓣` is a
`MMP.Resolution.BlowupSequenceFunctor` on `𝓛𝓣`. Open cover maps are
`MMP.Resolution.IsOpenCoverMap`.

"Schemes of finite type over a field" is imposed on the members of `𝓖𝓣` (hence of `𝓛𝓣`), since a
base-change-stable class of morphisms cannot itself be restricted to finite-type schemes.

"`𝓛𝓣` is closed under finite disjoint unions" is phrased intrinsically: a triple whose scheme is
covered by finitely many pairwise disjoint open immersions, along each of which it pulls back
to a member of `𝓛𝓣`, is itself a member of `𝓛𝓣`. "Closed under finite coproducts over a common
target" for `𝓜` says that `Sigma.desc g : ∐ U_i → X` lies in `𝓜` whenever every `g_i` does.

### References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], Thm. 3.105.
-/

namespace MMP.Resolution.Kollar

open CategoryTheory AlgebraicGeometry Limits MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral CategoryTheory.catToReflQuiver

section

/-- Pulling back along two lifts of the same morphism into a blow-up gives the same sequence,
even when the two blown-up ideals are only propositionally equal. -/
private theorem pullback_heq_of_comp_eq {T Y : Scheme.{u}} (k : T ⟶ Y) (Z : Y.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) {W₁ W₂ : T.IdealSheafData} (e₁ : Z.comap k = W₁)
    (e₂ : Z.comap k = W₂) (c₁ : blowUp W₁ ⟶ blowUp Z) (c₂ : blowUp W₂ ⟶ blowUp Z)
    (h₁ : c₁ ≫ blowUpToBase Z = blowUpToBase W₁ ≫ k)
    (h₂ : c₂ ≫ blowUpToBase Z = blowUpToBase W₂ ≫ k) :
    B.pullback c₁ ≍ B.pullback c₂ := by
  subst e₁ e₂
  have hc := isCartierOver_blowUpToBase_comp k Z
  obtain rfl : c₁ = c₂ :=
    (blowUpLift_unique _ _ hc _ h₁).trans (blowUpLift_unique _ _ hc _ h₂).symm
  rfl

/-- Pull-back of blow-up sequences is compatible with composition. -/
private theorem pullback_pullback {X Y T : Scheme.{u}} (B : ClosedBlowupSequence X)
    (a : Y ⟶ X) (b : T ⟶ Y) : (B.pullback a).pullback b = B.pullback (b ≫ a) := by
  induction B generalizing Y T with
  | nil X => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons _ _ = ClosedBlowupSequence.cons _ _
    refine ClosedBlowupSequence.cons_eq_cons_iff.mpr
      ⟨(Scheme.IdealSheafData.comap_comp _ _ _).symm, ?_⟩
    rw [ih]
    refine pullback_heq_of_comp_eq (b ≫ a) Z B (Scheme.IdealSheafData.comap_comp _ _ _) rfl _ _
      ?_ (canonicalLift_comp_blowUpToBase _ _)
    rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
      canonicalLift_comp_blowUpToBase, Category.assoc]

/-- Ideal sheaves descend along a flat surjective morphism locally of finite presentation: an
ideal sheaf on `X'` with equal pull-backs to `X' ×_X X'` is the pull-back of one on `X`. -/
private theorem exists_comap_eq_of_isPullback {X X' P : Scheme.{u}} (g : X' ⟶ X) [Flat g]
    [Surjective g] [LocallyOfFinitePresentation g] {p₁ p₂ : P ⟶ X'} (hP : IsPullback p₁ p₂ g g)
    (Z' : X'.IdealSheafData) (h : Z'.comap p₁ = Z'.comap p₂) :
    ∃ Z : X.IdealSheafData, Z.comap g = Z' := by
  have hcov : Presieve.ofArrows (fun _ : PUnit.{u + 1} => X') (fun _ => g) ∈
      Scheme.fpqcPrecoverage X := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.fppfPrecoverage_le_fpqcPrecoverage _ g.singleton_mem_fppfPrecoverage
  obtain ⟨K, hK⟩ := Scheme.IdealSheafData.exists_comap_eq_of_fpqc _ hcov (fun _ => Z')
    (fun _ _ => by
      rw [← hP.isoPullback_inv_fst, ← hP.isoPullback_inv_snd,
        Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h])
  exact ⟨K, hK ⟨⟩⟩

/-- **Descent of blow-up sequences.** Let `g : X' → X` be flat, surjective and locally of
finite presentation, and `B'` a blow-up sequence starting with `X'` whose two pull-backs to
`X' ×_X X'` agree. Then `B'` is the pull-back along `g` of a blow-up sequence starting with
`X`. -/
private theorem exists_pullback_eq_of_isPullback {X' : Scheme.{u}}
    (B' : ClosedBlowupSequence X') : ∀ {X : Scheme.{u}} (g : X' ⟶ X) [Flat g] [Surjective g]
    [LocallyOfFinitePresentation g] {P : Scheme.{u}} (p₁ p₂ : P ⟶ X'), IsPullback p₁ p₂ g g →
    B'.pullback p₁ = B'.pullback p₂ → ∃ B : ClosedBlowupSequence X, B.pullback g = B' := by
  induction B' with
  | nil X' => exact fun {X} _ _ _ _ _ _ _ _ _ => ⟨.nil X, rfl⟩
  | @cons Y Z' B'' ih =>
    intro X g _ _ _ P p₁ p₂ hP h
    obtain ⟨hZ, hT⟩ := ClosedBlowupSequence.cons_eq_cons_iff.mp h
    obtain ⟨Z, rfl⟩ := exists_comap_eq_of_isPullback g hP Z' hZ
    have hsq := isPullback_canonicalLift_of_flat g Z
    have : Flat (canonicalLift g Z) := flat_canonicalLift g Z
    have : Surjective (canonicalLift g Z) := surjective_canonicalLift g Z
    have : LocallyOfFinitePresentation (canonicalLift g Z) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsq ‹_›
    have : Flat p₁ := MorphismProperty.of_isPullback (P := @Flat) hP.flip ‹_›
    have hcart : ∀ q : P ⟶ Y, q ≫ g = p₁ ≫ g → Stacks.Blowup.IsCartierOver (Z.comap g)
        (Over.mk (blowUpToBase (Z.comap (p₁ ≫ g)) ≫ q)) := by
      intro q hq
      change Stacks.Divisors.IsEffectiveCartierDivisor ((Z.comap g).comap _)
      rw [← Scheme.IdealSheafData.comap_comp]
      change Stacks.Divisors.IsEffectiveCartierDivisor
        (Z.comap ((blowUpToBase (Z.comap (p₁ ≫ g)) ≫ q) ≫ g))
      rw [Category.assoc, hq]
      exact isCartierOver_blowUpToBase_comp (p₁ ≫ g) Z
    set π₁ := blowUpToBase (Z.comap (p₁ ≫ g))
    let c₁ := blowUpLift (Z.comap g) (π₁ ≫ p₁) (hcart p₁ rfl)
    let c₂ := blowUpLift (Z.comap g) (π₁ ≫ p₂) (hcart p₂ hP.w.symm)
    have hc₁ : c₁ ≫ blowUpToBase (Z.comap g) = π₁ ≫ p₁ := blowUpLift_comp _ _ _
    have hc₂ : c₂ ≫ blowUpToBase (Z.comap g) = π₁ ≫ p₂ := blowUpLift_comp _ _ _
    have hlift : ∀ c : blowUp (Z.comap (p₁ ≫ g)) ⟶ blowUp Z,
        c ≫ blowUpToBase Z = π₁ ≫ p₁ ≫ g → c = canonicalLift (p₁ ≫ g) Z :=
      fun c hc => blowUpLift_unique _ _ _ c hc
    have hc₁g : c₁ ≫ canonicalLift g Z = canonicalLift (p₁ ≫ g) Z := hlift _ (by
      rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, hc₁,
        Category.assoc])
    have hc₂g : c₂ ≫ canonicalLift g Z = canonicalLift (p₁ ≫ g) Z := hlift _ (by
      rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, hc₂,
        Category.assoc]; exact congrArg (π₁ ≫ ·) hP.w.symm)
    have S₁ : IsPullback c₁ π₁ (blowUpToBase (Z.comap g)) p₁ := by
      refine IsPullback.of_right ?_ hc₁ hsq.flip
      rw [hc₁g]
      exact (isPullback_canonicalLift_of_flat (p₁ ≫ g) Z).flip
    have S₂ := S₁.paste_vert hP
    have top : IsPullback c₁ c₂ (canonicalLift g Z) (canonicalLift g Z) := by
      refine IsPullback.of_bot ?_ (hc₁g.trans hc₂g.symm) hsq.flip
      rw [hc₂, canonicalLift_comp_blowUpToBase]
      exact S₂
    have a₁ : B''.pullback c₁ ≍ B''.pullback (canonicalLift p₁ (Z.comap g)) :=
      pullback_heq_of_comp_eq p₁ (Z.comap g) B'' (Scheme.IdealSheafData.comap_comp _ _ _).symm
        rfl c₁ _ hc₁ (canonicalLift_comp_blowUpToBase _ _)
    have a₂ : B''.pullback c₂ ≍ B''.pullback (canonicalLift p₂ (Z.comap g)) :=
      pullback_heq_of_comp_eq p₂ (Z.comap g) B''
        (by rw [← Scheme.IdealSheafData.comap_comp, hP.w]) rfl c₂ _ hc₂
        (canonicalLift_comp_blowUpToBase _ _)
    obtain ⟨B₁, hB₁⟩ := ih (canonicalLift g Z) c₁ c₂ top (eq_of_heq (a₁.trans (hT.trans a₂.symm)))
    exact ⟨.cons Z B₁, by
      change ClosedBlowupSequence.cons _ (B₁.pullback (canonicalLift g Z)) = _
      rw [hB₁]⟩

/-- Pull-back of triples is compatible with composition. -/
private theorem fieldBlowupTriple_pullback_pullback (t : FieldBlowupTriple.{u}) {Y T : Scheme.{u}}
    (a : Y ⟶ t.X) (b : T ⟶ Y) : (t.pullback a).pullback b = t.pullback (b ≫ a) := by
  have h₁ : (t.I.comap a).comap b = t.I.comap (b ≫ a) :=
    (Scheme.IdealSheafData.comap_comp _ _ _).symm
  have h₂ : (fun i => ((t.E.E i).comap a).comap b) = fun i => (t.E.E i).comap (b ≫ a) :=
    funext fun _ => (Scheme.IdealSheafData.comap_comp _ _ _).symm
  unfold FieldBlowupTriple.pullback OrderedDivisor.comap
  rw [h₁, h₂, Category.assoc]

/-- A blow-up sequence functor takes equal triples to equal sequences. -/
private theorem blowupSequenceFunctor_heq {LT : Set FieldBlowupTriple.{u}}
    (𝓑 : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple LT) {t t' : FieldBlowupTriple.{u}}
    (e : t = t') (h : t ∈ LT) (h' : t' ∈ LT) : 𝓑 t h ≍ 𝓑 t' h' := by
  subst e
  rfl

/-- A triple of `GT` on a quasi-compact scheme admits a single surjective `M`-morphism from a
finite disjoint union along which it pulls back to a member of `LT`. -/
private theorem exists_surjective_pullback_mem (M : MorphismProperty Scheme.{u})
    (hM : M ≤ @Smooth)
    (hMcoprod : ∀ {X : Scheme.{u}} (n : ℕ) (U : Fin n → Scheme.{u}) (g : ∀ i, U i ⟶ X),
      (∀ i, M (g i)) → M (Sigma.desc g))
    (LT : Set FieldBlowupTriple.{u})
    (hunion : ∀ (t : FieldBlowupTriple.{u}) (n : ℕ) (V : Fin n → Scheme.{u})
      (j : ∀ i, V i ⟶ t.X), (∀ i, IsOpenImmersion (j i)) →
      Pairwise (fun a b => Disjoint (Set.range (j a)) (Set.range (j b))) →
      (⋃ i, Set.range (j i)) = Set.univ → (∀ i, t.pullback (j i) ∈ LT) → t ∈ LT)
    (t : FieldBlowupTriple.{u}) [CompactSpace t.X]
    (hloc : ∀ x : t.X, ∃ (U : Scheme.{u}) (g : U ⟶ t.X),
      M g ∧ x ∈ Set.range g ∧ t.pullback g ∈ LT) :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ t.X), M g ∧ Surjective g ∧ t.pullback g ∈ LT := by
  choose U g hMg hx hLT using hloc
  have hopen : ∀ x, IsOpen (Set.range (g x)) := fun x => by
    have : Smooth (g x) := hM _ (hMg x)
    have : UniversallyOpen (g x) := UniversallyOpen.of_flat (g x)
    exact (g x).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (g x)) hopen
    (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  let e := s.equivFin.symm
  let V : Fin s.card → Scheme.{u} := fun i => U (e i).1
  let G : ∀ i, V i ⟶ t.X := fun i => g (e i).1
  refine ⟨∐ V, Sigma.desc G, hMcoprod _ V G (fun i => hMg _), ⟨fun x => ?_⟩, ?_⟩
  · obtain ⟨i, hi, y, rfl⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    let j := s.equivFin ⟨i, hi⟩
    have hmem : ∀ i', i' = i → g i y ∈ Set.range (g i') := by
      rintro _ rfl
      exact ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := hmem (e j).1 (by simp [e, j])
    refine ⟨Sigma.ι V j y', ?_⟩
    rwa [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  · refine hunion _ _ V (Sigma.ι V)
      (fun i => Scheme.IsLocallyDirected.instIsOpenImmersionι (Discrete.functor V) ⟨i⟩)
      (fun a b hab => ?_) ?_ (fun i => ?_)
    · have := disjoint_opensRange_sigmaι V a b hab
      refine Set.disjoint_left.2 fun x h₁ h₂ => ?_
      have hx : x ∈ (Sigma.ι V a).opensRange ⊓ (Sigma.ι V b).opensRange := ⟨h₁, h₂⟩
      rwa [this.eq_bot] at hx
    · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
      obtain ⟨⟨i⟩, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (Discrete.functor V) x
      exact ⟨i, y, hy⟩
    · rw [fieldBlowupTriple_pullback_pullback, Sigma.ι_desc]
      exact hLT _

/-- If `𝓑` commutes with surjective `M`-morphisms, then two surjective `M`-morphisms
`a₁ : P → X₁`, `a₂ : P → X₂` pulling `t₁, t₂ ∈ LT` back to the same triple pull `𝓑 t₁` and
`𝓑 t₂` back to the same sequence on `P`. -/
private theorem pullback_eq_pullback_of_pullback_eq {M : MorphismProperty Scheme.{u}}
    {LT : Set FieldBlowupTriple.{u}}
    (hpull : ∀ t ∈ LT, ∀ (Y : Scheme.{u}) (h : Y ⟶ t.X), M h → t.pullback h ∈ LT)
    (𝓑 : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple LT)
    (hB : ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ LT) (Y : Scheme.{u}) (h : Y ⟶ t.X),
      M h → Surjective h → ∀ hY : t.pullback h ∈ LT, 𝓑 (t.pullback h) hY = (𝓑 t ht).pullback h)
    {t₁ t₂ : FieldBlowupTriple.{u}} (h₁ : t₁ ∈ LT) (h₂ : t₂ ∈ LT) {P : Scheme.{u}}
    (a₁ : P ⟶ t₁.X) (a₂ : P ⟶ t₂.X) (hM₁ : M a₁) (hM₂ : M a₂) (hs₁ : Surjective a₁)
    (hs₂ : Surjective a₂) (e : t₁.pullback a₁ = t₂.pullback a₂) :
    (𝓑 t₁ h₁).pullback a₁ = (𝓑 t₂ h₂).pullback a₂ := by
  rw [← hB t₁ h₁ P a₁ hM₁ hs₁ (hpull _ h₁ _ _ hM₁), ← hB t₂ h₂ P a₂ hM₂ hs₂ (hpull _ h₂ _ _ hM₂)]
  exact eq_of_heq (blowupSequenceFunctor_heq 𝓑 e _ _)

end

/-- **Globalization of blow-up sequences** (Kollár Thm. 3.105, corrected). Let `M` be a class of
smooth morphisms containing all open cover maps and closed under composition, base change and
finite coproducts over a common target, and `GT ⊇ LT` classes of triples of finite type over
their field such that every member of `GT` is locally (at each point, along an `M`-morphism) a
member of `LT`, and `LT` is closed under finite disjoint unions and under pull-back along
`M`-morphisms. If the blow-up sequence functor `𝓑` on `LT` commutes with every surjective
`M`-morphism between members of `LT`, then each `t ∈ GT` carries a blow-up sequence `𝐁` with
`g^*𝐁 = 𝓑(t.pullback g)` for every surjective `M`-morphism `g` with `t.pullback g ∈ LT`. -/
@[mmp "thm_kr3e_globalization_blowup_sequences"]
public theorem exists_pullback_eq_of_commutes_with_surjections
    (M : MorphismProperty Scheme.{u}) [M.IsStableUnderBaseChange]
    [M.IsStableUnderComposition] (hM : M ≤ @Smooth)
    (hMcover : ∀ {X' X : Scheme.{u}} (g : X' ⟶ X), IsOpenCoverMap g → M g)
    (hMcoprod : ∀ {X : Scheme.{u}} (n : ℕ) (U : Fin n → Scheme.{u}) (g : ∀ i, U i ⟶ X),
      (∀ i, M (g i)) → M (Sigma.desc g))
    (GT LT : Set FieldBlowupTriple.{u}) (hLTGT : LT ⊆ GT)
    (hGT : ∀ t ∈ GT, LocallyOfFiniteType t.sX ∧ QuasiCompact t.sX)
    (hloc : ∀ t ∈ GT, ∀ x : t.X, ∃ (U : Scheme.{u}) (g : U ⟶ t.X),
      M g ∧ x ∈ Set.range g ∧ t.pullback g ∈ LT)
    (hunion : ∀ (t : FieldBlowupTriple.{u}) (n : ℕ) (V : Fin n → Scheme.{u})
      (j : ∀ i, V i ⟶ t.X), (∀ i, IsOpenImmersion (j i)) →
      Pairwise (fun a b => Disjoint (Set.range (j a)) (Set.range (j b))) →
      (⋃ i, Set.range (j i)) = Set.univ → (∀ i, t.pullback (j i) ∈ LT) → t ∈ LT)
    (hpull : ∀ t ∈ LT, ∀ (Y : Scheme.{u}) (h : Y ⟶ t.X), M h → t.pullback h ∈ LT)
    (𝓑 : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple LT)
    (hB : ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ LT) (Y : Scheme.{u}) (h : Y ⟶ t.X),
      M h → Surjective h → ∀ hY : t.pullback h ∈ LT, 𝓑 (t.pullback h) hY = (𝓑 t ht).pullback h)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ GT) :
    ∃ B : ClosedBlowupSequence t.X, ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X), M g → Surjective g →
      ∀ hg : t.pullback g ∈ LT, B.pullback g = 𝓑 (t.pullback g) hg := by
  have : QuasiCompact t.sX := (hGT t ht).2
  have : CompactSpace t.X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := t.sX) Set.univ isOpen_univ isCompact_univ⟩
  obtain ⟨X', g, hMg, hg, hT'⟩ :=
    exists_surjective_pullback_mem M hM hMcoprod LT hunion t (hloc t ht)
  have : Smooth g := hM _ hMg
  have : Flat g := inferInstance
  have : LocallyOfFinitePresentation g := inferInstance
  obtain ⟨B, hBg⟩ := exists_pullback_eq_of_isPullback (X' := X') (𝓑 _ hT') g _ _
    (IsPullback.of_hasPullback g g) (pullback_eq_pullback_of_pullback_eq hpull 𝓑 hB hT' hT'
      (pullback.fst g g) (pullback.snd g g) (M.pullback_fst g g hMg)
      (M.pullback_snd g g hMg)
      (inferInstanceAs (Surjective (pullback.fst g g)))
      (inferInstanceAs (Surjective (pullback.snd g g))) (by
        rw [fieldBlowupTriple_pullback_pullback, fieldBlowupTriple_pullback_pullback,
          pullback.condition]))
  refine ⟨B, fun Y h hMh hh hY => ?_⟩
  have : Smooth h := hM _ hMh
  have : Flat (pullback.fst h g) := inferInstance
  apply eq_of_pullback_eq_of_flat_of_surjective (pullback.fst h g)
  rw [pullback_pullback, pullback.condition, ← pullback_pullback, hBg]
  exact pullback_eq_pullback_of_pullback_eq hpull 𝓑 hB hT' hY
    (pullback.snd h g) (pullback.fst h g) (M.pullback_snd h g hMh) (M.pullback_fst h g hMg)
    (inferInstanceAs (Surjective (pullback.snd h g)))
    (inferInstanceAs (Surjective (pullback.fst h g))) (by
    rw [fieldBlowupTriple_pullback_pullback, fieldBlowupTriple_pullback_pullback,
      pullback.condition])

end MMP.Resolution.Kollar

end
