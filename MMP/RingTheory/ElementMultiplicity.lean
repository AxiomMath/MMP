module

public import MMP.AlgebraicGeometry.Resolution.Surface.CurveMultiplicity
public import MMP.AlgebraicGeometry.Divisor.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Multiplicities of elements and rational functions (Kollár 1.19–1.20)

Properties of the multiplicity `e_R(r) = dim_k R / rR` of a non-zero-divisor of a `k`-algebra
`R` (`MMP.Resolution.eMult`) and of its extension `e_R(r₁ / r₂) = e_R(r₁) - e_R(r₂)` to the total
ring of fractions (`MMP.Resolution.eMultFrac`), and the characterization of nonsingular points of a
curve by principal maximal ideals (Kollár, *Lectures on resolution of singularities*, 1.19–1.20).

## Main statements

* `MMP.Resolution.Kollar.eMult_mul`: for non-zero-divisors `a, b` with `R / aR`, `R / bR`
  finite-dimensional, `ab` is a non-zero-divisor, `R / abR` is finite-dimensional and
  `e_R(ab) = e_R(a) + e_R(b)` (1.20.1).
* `MMP.Resolution.Kollar.eMultFrac_eq_of_eq_mul`: for `R` of finite colength and `f = s₁ / s₂` in
  the total ring of fractions, `f` is a unit and `e_R(f) = e_R(s₁) - e_R(s₂)`: the multiplicity
  of `f` does not depend on the presentation.
* `MMP.Resolution.Kollar.eMultFrac_mul`: `e_R(fg) = e_R(f) + e_R(g)` for units `f, g` (1.20.2).
* `MMP.Resolution.Kollar.isRegularLocalRing_stalk_iff_isPrincipal`: a closed point `p` of a curve
  is nonsingular if and only if `𝔪_p` is principal.

## Implementation notes

The total ring of fractions of `R` is any `R`-algebra `K` with `IsFractionRing R K`, for instance
`FractionRing R`. A presentation `f = s₁ / s₂` is written `s₁ = f s₂` in `K`, as in the definition
of `eMultFrac`.
-/

@[expose] public section

open AlgebraicGeometry

universe u v w

namespace MMP.Resolution.Kollar

section Algebra

variable (k : Type u) [Field k] {R : Type v} [CommRing R] [Algebra k R]

/-- **Kollár (1.20.1).** If `a, b` are non-zero-divisors of a `k`-algebra `R` with `R / aR` and
`R / bR` finite-dimensional, then `ab` is a non-zero-divisor, `R / abR` is finite-dimensional, and
`e_R(ab) = e_R(a) + e_R(b)`. -/
@[mmp "lem_kr1a_colength_multiplicative"]
theorem eMult_mul {a b : R} (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R)
    (ha' : Module.Finite k (R ⧸ Ideal.span {a})) (hb' : Module.Finite k (R ⧸ Ideal.span {b})) :
    a * b ∈ nonZeroDivisors R ∧ Module.Finite k (R ⧸ Ideal.span {a * b}) ∧
      eMult k (a * b) = eMult k a + eMult k b := by
  refine ⟨mul_mem ha hb, ?_⟩
  let φ : R ⧸ Ideal.span {a} →ₗ[R] R ⧸ Ideal.span {a * b} :=
    Submodule.mapQ (Ideal.span {a}) (Ideal.span {a * b}) (LinearMap.mulLeft R b) (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      change b * (c * a) ∈ Ideal.span {a * b}
      exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩)
  let ψ : R ⧸ Ideal.span {a * b} →ₗ[R] R ⧸ Ideal.span {b} :=
    Submodule.mapQ (Ideal.span {a * b}) (Ideal.span {b}) LinearMap.id (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      change c * (a * b) ∈ Ideal.span {b}
      exact Ideal.mem_span_singleton'.2 ⟨c * a, by ring⟩)
  have hinj : Function.Injective (φ.restrictScalars k) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change φ (Submodule.Quotient.mk x) = 0 at hx
    simp only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    have h0 : (c * a - x) * b = 0 := by linear_combination hc
    simpa [sub_eq_zero] using (mem_nonZeroDivisors_iff.1 hb).2 _ h0
  have hsurj : Function.Surjective (ψ.restrictScalars k) := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hex : Function.Exact (φ.restrictScalars k) (ψ.restrictScalars k) := by
    intro y
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change ψ (Submodule.Quotient.mk y) = 0 at h
      simp only [ψ, Submodule.mapQ_apply, LinearMap.id_apply] at h
      rw [Submodule.Quotient.mk_eq_zero] at h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      exact ⟨Submodule.Quotient.mk c, by
        change φ (Submodule.Quotient.mk c) = _
        simp only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
        congr 1
        ring⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change ψ (φ (Submodule.Quotient.mk x)) = 0
      simp only [φ, ψ, Submodule.mapQ_apply, LinearMap.mulLeft_apply, LinearMap.id_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.2 ⟨x, by ring⟩
  have hfin : Module.Finite k (R ⧸ Ideal.span {a * b}) := Module.Finite.of_exact hex hsurj
  refine ⟨hfin, ?_⟩
  have h1 := (ψ.restrictScalars k).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hex.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj hinj] at h1
  unfold eMult
  omega

variable (K : Type w) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- **Kollár 1.20**, "so the notion is well defined". Let `R` be a `k`-algebra of finite colength
with total ring of fractions `K`, and `f = s₁ / s₂` with non-zero-divisors `s₁, s₂ ∈ R`. Then `f`
is a unit of `K` and `e_R(f) = e_R(s₁) - e_R(s₂)`. -/
@[mmp "lem_kr1a_multiplicity_of_rational_function_well_defined"]
theorem eMultFrac_eq_of_eq_mul (hR : IsFiniteColength k R) {f : K} {s₁ s₂ : R}
    (hs₁ : s₁ ∈ nonZeroDivisors R) (hs₂ : s₂ ∈ nonZeroDivisors R)
    (hf : algebraMap R K s₁ = f * algebraMap R K s₂) :
    IsUnit f ∧ eMultFrac k K f (R := R) = (eMult k s₁ : ℤ) - eMult k s₂ := by
  have hu₁ : IsUnit (algebraMap R K s₁) :=
    IsLocalization.map_units K (⟨s₁, hs₁⟩ : nonZeroDivisors R)
  have hu₂ : IsUnit (algebraMap R K s₂) :=
    IsLocalization.map_units K (⟨s₂, hs₂⟩ : nonZeroDivisors R)
  refine ⟨?_, ?_⟩
  · rw [hf] at hu₁
    exact (IsUnit.mul_left_iff hu₂).1 (by rwa [mul_comm])
  · have hex : ∃ p : nonZeroDivisors R × nonZeroDivisors R,
        algebraMap R K p.1 = f * algebraMap R K p.2 := ⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩), hf⟩
    unfold eMultFrac
    simp only [hex, ↓reduceDIte]
    have hp := hex.choose_spec
    generalize hex.choose = q at hp ⊢
    obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := q
    simp only at hp ⊢
    have hmul : r₁ * s₂ = s₁ * r₂ := by
      apply IsFractionRing.injective R K
      rw [map_mul, map_mul, hp, hf]
      ring
    have e1 := (eMult_mul k hr₁ hs₂ (hR _ hr₁) (hR _ hs₂)).2.2
    have e2 := (eMult_mul k hs₁ hr₂ (hR _ hs₁) (hR _ hr₂)).2.2
    rw [hmul] at e1
    omega

/-- A unit of the total ring of fractions is a quotient of two non-zero-divisors. -/
private lemma exists_presentation {f : K} (hf : IsUnit f) :
    ∃ a s : R, a ∈ nonZeroDivisors R ∧ s ∈ nonZeroDivisors R ∧
      algebraMap R K a = f * algebraMap R K s := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) f
  have hspec := IsLocalization.mk'_spec K a s
  change IsLocalization.mk' K a s = f at hs
  rw [hs] at hspec
  refine ⟨a, s, ?_, s.2, hspec.symm⟩
  have hu : IsUnit (algebraMap R K a) := by
    rw [← hspec]
    exact hf.mul (IsLocalization.map_units K s)
  refine mem_nonZeroDivisors_iff_left.2 fun x hx => IsFractionRing.injective R K ?_
  have h := congrArg (algebraMap R K) hx
  rw [map_mul, map_zero] at h
  simpa using hu.mul_right_eq_zero.1 h

/-- **Kollár (1.20.2).** Let `R` be a `k`-algebra of finite colength with total ring of
fractions `K`. For units `f, g` of `K`, `e_R(fg) = e_R(f) + e_R(g)`. -/
@[mmp "lem_kr1a_multiplicity_additive"]
theorem eMultFrac_mul (hR : IsFiniteColength k R) {f g : K} (hf : IsUnit f) (hg : IsUnit g) :
    eMultFrac k K (f * g) (R := R) =
      eMultFrac k K f (R := R) + eMultFrac k K g (R := R) := by
  obtain ⟨a, s, ha, hs, hfa⟩ := exists_presentation (R := R) K hf
  obtain ⟨b, t, hb, ht, hgb⟩ := exists_presentation (R := R) K hg
  have hfg : algebraMap R K (a * b) = f * g * algebraMap R K (s * t) := by
    rw [map_mul, map_mul, hfa, hgb]
    ring
  rw [(eMultFrac_eq_of_eq_mul k K hR (mul_mem ha hb) (mul_mem hs ht) hfg).2,
    (eMultFrac_eq_of_eq_mul k K hR ha hs hfa).2, (eMultFrac_eq_of_eq_mul k K hR hb ht hgb).2,
    (eMult_mul k ha hb (hR _ ha) (hR _ hb)).2.2, (eMult_mul k hs ht (hR _ hs) (hR _ ht)).2.2]
  push_cast
  ring

end Algebra

section Curve

variable (k : Type u) [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))

/-- The local ring of a curve at a closed point has Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_isClosed [MMP.Mori.IsCurve k sC] {p : C}
    (hp : IsClosed ({p} : Set C)) : ringKrullDim (C.presheaf.stalk p) = 1 := by
  have h1 : topologicalKrullDim C = 1 :=
    (inferInstance : MMP.Mori.IsCurve k sC).topologicalKrullDim_eq_one
  rw [ringKrullDim_stalk_eq_coheight]
  have hle : (Order.coheight p : WithBot ℕ∞) ≤ 1 := by
    rw [← h1]
    unfold topologicalKrullDim
    rw [← Order.coheight_orderIso (irreducibleSetEquivPoints (α := C)).symm p]
    exact Order.coheight_le_krullDim _
  have hne : p ≠ genericPoint C := by
    rintro rfl
    have hsub : Subsingleton C := ⟨fun x y => by
      have hx : x ∈ ({genericPoint C} : Set C) := by
        rw [← hp.closure_eq]
        exact (genericPoint_specializes x).mem_closure
      have hy : y ∈ ({genericPoint C} : Set C) := by
        rw [← hp.closure_eq]
        exact (genericPoint_specializes y).mem_closure
      rw [hx, hy]⟩
    have : DiscreteTopology C := inferInstance
    have := topologicalKrullDim_zero_of_discreteTopology C
    rw [h1] at this
    exact absurd this (by norm_num)
  have hlt : p < genericPoint C := by
    refine lt_of_le_not_ge ((genericPoint_specializes p : p ≤ genericPoint C)) fun h => hne ?_
    exact (Specializes.antisymm (h : p ⤳ genericPoint C) (genericPoint_specializes p)).eq
  have : (1 : ℕ∞) ≤ Order.coheight p := le_trans (by simp) (Order.coheight_add_one_le hlt)
  exact le_antisymm hle (by exact_mod_cast this)

/-- **Kollár 1.19–1.20.** A closed point `p` of a curve `C` over a field `k` is nonsingular,
that is `𝒪_{p,C}` is a regular local ring, if and only if the maximal ideal `𝔪_p` of `𝒪_{p,C}`
is principal. -/
@[mmp "lem_kr1a_mult_one_iff_regular"]
theorem isRegularLocalRing_stalk_iff_isPrincipal [MMP.Mori.IsCurve k sC] {p : C}
    (hp : IsClosed ({p} : Set C)) :
    IsRegularLocalRing (C.presheaf.stalk p) ↔
      (IsLocalRing.maximalIdeal (C.presheaf.stalk p)).IsPrincipal := by
  have h : MMP.Mori.IsCurve k sC := inferInstance
  have hN : IsLocallyNoetherian C := by
    have := h.toLocallyOfFiniteType
    exact LocallyOfFiniteType.isLocallyNoetherian sC
  have : IsNoetherianRing (C.presheaf.stalk p) := inferInstance
  have hdim := ringKrullDim_stalk_eq_one_of_isClosed k sC hp
  rw [isRegularLocalRing_iff, hdim]
  have hbot : IsLocalRing.maximalIdeal (C.presheaf.stalk p) ≠ ⊥ := by
    intro hb
    have hf : IsField (C.presheaf.stalk p) := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hb
    let := hf.toField
    have h0 : ringKrullDim (C.presheaf.stalk p) = 0 := ringKrullDim_eq_zero_of_field _
    rw [h0] at hdim
    exact absurd hdim (by norm_num)
  have hc : ((IsLocalRing.maximalIdeal (C.presheaf.stalk p)).spanFinrank : WithBot ℕ∞) = 1 ↔
      (IsLocalRing.maximalIdeal (C.presheaf.stalk p)).spanFinrank = 1 :=
    ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  rw [hc]
  exact ⟨fun h => ((Submodule.spanFinrank_eq_one_iff _).1 h).1,
    fun hpr => (Submodule.spanFinrank_eq_one_iff _).2 ⟨hpr, hbot⟩⟩

end Curve

end MMP.Resolution.Kollar
