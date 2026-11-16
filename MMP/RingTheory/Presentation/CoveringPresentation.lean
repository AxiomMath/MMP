module

public import MMP.RingTheory.Presentation.HypersurfacePresentation

/-!
# Covering presentations of finite extensions of domains

Let `R ⊆ B` be a finite extension of domains in characteristic zero, with fraction fields
`K ⊆ L`. There are `y ∈ B`, a monic `f ∈ R[t]` with `f(y) = 0` whose multiples are exactly the
relations of `y` over `R`, a nonzero *conductor element* `c ∈ R` with `c B ⊆ R[y]`, and a nonzero
`δ ∈ R` lying in the ideal `(f, f')` of `R[t]`; the degree of `f` is `[L : K]`. Geometrically,
over the open set `{c δ ≠ 0}` of `Spec R` the scheme `Spec B` is the hypersurface `f = 0`, and
its fibres are the `deg f` simple roots of `f`.

The element `y` is a primitive element of `L / K` scaled by a common denominator `s` of the
coefficients of its minimal polynomial `m`: the minimal polynomial of `s y` is
`s^{deg m} m(t / s)`, which has coefficients in `R`.

For a ring map `w : R → k` to a field with `w(c) ≠ 0` and a root `t` of `f_w`, there is a unique
ring map `B → k` extending `w` and sending `y` to `t`: its value at `b` is `Q_w(t) / w(c)` for any
`Q ∈ R[t]` with `Q(y) = c b`.

## Main definitions

* `MMP.GenericCovering.CoveringPresentation`: the data `y, f, c, δ`.
* `MMP.GenericCovering.CoveringPresentation.point`: the ring map `B → k` over a
  root of `f_w`.

## Main results

* `MMP.GenericCovering.CoveringPresentation.natDegree_f_eq_finrank`: the degree of
  `f` is the degree `[L : K]` of the fraction fields.
* `MMP.GenericCovering.CoveringPresentation.separable_map`: `f_w` is separable when
  `w(δ) ≠ 0`.
* `MMP.GenericCovering.exists_coveringPresentation`: covering presentations exist
  for finite extensions of domains of characteristic zero.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open Polynomial IntermediateField

namespace MMP.GenericCovering

/-- A *covering presentation* of an `R`-algebra `B`: an element `y` whose relations over `R` are
the multiples of a monic `f`, a conductor element `c ∈ R` with `c B ⊆ R[y]`, and an element
`δ ∈ R` of the ideal `(f, f')` of `R[t]`. -/
structure CoveringPresentation (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] where
  /-- The element generating `B` over `R` up to the conductor. -/
  y : B
  /-- The relation of `y` over `R`. -/
  f : R[X]
  /-- The conductor element. -/
  c : R
  /-- An element of the ideal `(f, f')`. -/
  δ : R
  /-- The polynomial `f` is monic. -/
  monic : f.Monic
  /-- The element `y` is a root of `f`. -/
  aeval_f : aeval y f = 0
  /-- Every polynomial vanishing at `y` is a multiple of `f`. -/
  dvd_of_aeval_eq_zero : ∀ Q : R[X], aeval y Q = 0 → f ∣ Q
  /-- Every `c b` with `b ∈ B` is a polynomial in `y` over `R`. -/
  exists_aeval_eq_mul : ∀ b : B, ∃ Q : R[X], aeval y Q = algebraMap R B c * b
  /-- The element `δ` lies in the ideal `(f, f')` of `R[t]`. -/
  exists_mul_add_mul_derivative : ∃ U V : R[X], U * f + V * derivative f = C δ

namespace CoveringPresentation

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (P : CoveringPresentation R B)

/-- A chosen `Q` with `Q(y) = c b`. -/
noncomputable def numer (b : B) : R[X] := (P.exists_aeval_eq_mul b).choose

/-- The polynomial `numer b` evaluated at `y` is `c b`. -/
lemma aeval_numer (b : B) : aeval P.y (P.numer b) = algebraMap R B P.c * b :=
  (P.exists_aeval_eq_mul b).choose_spec

/-- `f_w` is separable when `w(δ) ≠ 0`. -/
theorem separable_map {k : Type*} [Field k] (w : R →+* k) (hδ : w P.δ ≠ 0) :
    (P.f.map w).Separable := by
  obtain ⟨U, V, hUV⟩ := P.exists_mul_add_mul_derivative
  have h := congrArg (Polynomial.map w) hUV
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map] at h
  refine ⟨C (w P.δ)⁻¹ * U.map w, C (w P.δ)⁻¹ * V.map w, ?_⟩
  have : C (w P.δ)⁻¹ * C (w P.δ) = 1 := by rw [← C_mul, inv_mul_cancel₀ hδ, C_1]
  rw [← this, ← h]
  ring

section Point

variable {k : Type*} [Field k]

/-- The candidate value at `b` of the point over `w` and `t`: `Q_w(t) / w(c)` with `Q(y) = c b`. -/
noncomputable def pointFun (w : R →+* k) (t : k) (b : B) : k :=
  (P.numer b).eval₂ w t / w P.c

variable {P} {w : R →+* k} {t : k}

/-- At a root `t` of `f_w`, two polynomials taking the same value at `y` have the same value at `t`
over `w`. -/
lemma eval₂_eq_of_aeval_eq (ht : (P.f.map w).eval t = 0) {Q Q' : R[X]}
    (h : aeval P.y Q = aeval P.y Q') : Q.eval₂ w t = Q'.eval₂ w t := by
  obtain ⟨S, hS⟩ := P.dvd_of_aeval_eq_zero (Q - Q') (by rw [map_sub, h, sub_self])
  have := congrArg (fun p ↦ p.eval₂ w t) hS
  rw [eval_map] at ht
  simp only [eval₂_sub, eval₂_mul, ht, zero_mul] at this
  exact sub_eq_zero.mp this

/-- At a root `t` of `f_w` with `w(c) ≠ 0`, a polynomial `Q` with `Q(y) = c b` satisfies
`Q_w(t) = w(c) · pointFun w t b`. -/
lemma eval₂_eq_mul_pointFun (ht : (P.f.map w).eval t = 0) (hc : w P.c ≠ 0) {Q : R[X]} {b : B}
    (h : aeval P.y Q = algebraMap R B P.c * b) :
    Q.eval₂ w t = w P.c * P.pointFun w t b := by
  rw [pointFun, mul_div_cancel₀ _ hc]
  exact eval₂_eq_of_aeval_eq ht (h.trans (P.aeval_numer b).symm)

/-- The function `pointFun w t` is `R`-semilinear over `w`: it sends `r b` to `w(r)` times its
value at `b`. -/
lemma pointFun_algebraMap_mul (ht : (P.f.map w).eval t = 0) (hc : w P.c ≠ 0) (r : R) (b : B) :
    P.pointFun w t (algebraMap R B r * b) = w r * P.pointFun w t b := by
  have h := eval₂_eq_mul_pointFun ht hc (Q := C r * P.numer b) (b := algebraMap R B r * b)
    (by rw [map_mul, aeval_C, aeval_numer]; ring)
  rw [eval₂_mul, eval₂_C, eval₂_eq_mul_pointFun ht hc (P.aeval_numer b)] at h
  exact (mul_left_cancel₀ hc (by rw [← h]; ring)).symm

/-- The ring map `B → k` extending `w : R → k` and sending `y` to a root `t` of `f_w`, when
`w(c) ≠ 0`. -/
noncomputable def point (ht : (P.f.map w).eval t = 0) (hc : w P.c ≠ 0) : B →+* k where
  toFun := P.pointFun w t
  map_one' := by
    have h := eval₂_eq_mul_pointFun ht hc (Q := C P.c) (b := 1) (by simp)
    rw [eval₂_C] at h
    exact (mul_eq_left₀ hc).mp h.symm
  map_mul' a b := by
    have h := eval₂_eq_mul_pointFun ht hc (Q := P.numer a * P.numer b)
      (b := algebraMap R B P.c * (a * b))
      (by rw [map_mul, aeval_numer, aeval_numer]; ring)
    rw [eval₂_mul, pointFun_algebraMap_mul ht hc, eval₂_eq_mul_pointFun ht hc (P.aeval_numer a),
      eval₂_eq_mul_pointFun ht hc (P.aeval_numer b)] at h
    have h' : w P.c * (w P.c * P.pointFun w t (a * b)) =
        w P.c * (w P.c * (P.pointFun w t a * P.pointFun w t b)) := by
      rw [← h]
      ring
    exact mul_left_cancel₀ hc (mul_left_cancel₀ hc h')
  map_zero' := by
    have h := eval₂_eq_mul_pointFun ht hc (Q := 0) (b := 0) (by simp)
    rw [eval₂_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  map_add' a b := by
    have h := eval₂_eq_mul_pointFun ht hc (Q := P.numer a + P.numer b) (b := a + b)
      (by rw [map_add, aeval_numer, aeval_numer]; ring)
    rw [eval₂_add, eval₂_eq_mul_pointFun ht hc (P.aeval_numer a),
      eval₂_eq_mul_pointFun ht hc (P.aeval_numer b)] at h
    exact mul_left_cancel₀ hc (by rw [mul_add, h])

/-- The value of `point` at `b` is `pointFun w t b`. -/
lemma point_apply (ht : (P.f.map w).eval t = 0) (hc : w P.c ≠ 0) (b : B) :
    point ht hc b = P.pointFun w t b :=
  rfl

/-- The map `point` sends `r ∈ R` to `w(r)`. -/
@[simp]
lemma point_algebraMap (ht : (P.f.map w).eval t = 0) (hc : w P.c ≠ 0) (r : R) :
    point ht hc (algebraMap R B r) = w r := by
  have h := pointFun_algebraMap_mul ht hc r 1
  rw [mul_one] at h
  rw [point_apply, h, ← point_apply ht hc, map_one, mul_one]

/-- The map `point` restricts to `w` on `R`. -/
@[simp]
lemma point_comp_algebraMap (ht : (P.f.map w).eval t = 0) (hc : w P.c ≠ 0) :
    (point ht hc).comp (algebraMap R B) = w :=
  RingHom.ext (point_algebraMap ht hc)

/-- The map `point` sends `y` to `t`. -/
@[simp]
lemma point_y (ht : (P.f.map w).eval t = 0) (hc : w P.c ≠ 0) : point ht hc P.y = t := by
  have h := eval₂_eq_mul_pointFun ht hc (Q := C P.c * X) (b := P.y) (by simp)
  rw [eval₂_mul, eval₂_C, eval₂_X] at h
  exact (mul_left_cancel₀ hc h).symm

variable (P) in
/-- A ring map `ψ : B → k` evaluates `Q(y)` as `Q` at `ψ(y)` over `ψ|_R`. -/
lemma apply_aeval (ψ : B →+* k) (Q : R[X]) :
    ψ (aeval P.y Q) = Q.eval₂ (ψ.comp (algebraMap R B)) (ψ P.y) := by
  rw [aeval_def, hom_eval₂]

variable (P) in
/-- The value of a ring map `ψ : B → k` at `y` is a root of `f` over `ψ|_R`. -/
lemma eval_map_apply_y (ψ : B →+* k) :
    (P.f.map (ψ.comp (algebraMap R B))).eval (ψ P.y) = 0 := by
  rw [eval_map, ← apply_aeval, P.aeval_f, map_zero]

variable (P) in
/-- A ring map `ψ : B → k` with `ψ(c) ≠ 0` is the point over `ψ|_R` and `ψ(y)`. -/
lemma eq_point (ψ : B →+* k) (hc : ψ (algebraMap R B P.c) ≠ 0) :
    ψ = point (P.eval_map_apply_y ψ) hc := by
  ext b
  have h := eval₂_eq_mul_pointFun (P.eval_map_apply_y ψ) hc (P.aeval_numer b)
  rw [← apply_aeval, aeval_numer, map_mul] at h
  exact mul_left_cancel₀ hc h

variable (P) in
/-- Two ring maps `B → k` agreeing on `R` and at `y`, not vanishing at `c`, are equal. -/
lemma ringHom_ext {ψ ψ' : B →+* k} (hc : ψ (algebraMap R B P.c) ≠ 0)
    (hR : ψ.comp (algebraMap R B) = ψ'.comp (algebraMap R B)) (hy : ψ P.y = ψ' P.y) :
    ψ = ψ' := by
  have hc' : ψ' (algebraMap R B P.c) ≠ 0 := by
    rwa [← RingHom.comp_apply, ← hR]
  rw [P.eq_point ψ hc, P.eq_point ψ' hc']
  ext b
  simp only [point_apply, pointFun, hR, hy, RingHom.comp_apply]

end Point

section Degree

variable [IsDomain R] [IsDomain B] (K L : Type*) [Field K] [Field L] [Algebra R K]
  [IsFractionRing R K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

omit [IsDomain B] in
/-- The minimal polynomial over `K` of the image of `y` in `L` is `f`. -/
theorem minpoly_eq_map :
    minpoly K (algebraMap B L P.y) = P.f.map (algebraMap R K) := by
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hroot : ∀ Q : R[X], aeval (algebraMap B L P.y) (Q.map (algebraMap R K)) =
      algebraMap B L (aeval P.y Q) := fun Q ↦ by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply]
  refine (minpoly.unique K _ (P.monic.map _) (by rw [hroot, P.aeval_f, map_zero])
    fun q hq hqy ↦ ?_).symm
  obtain ⟨b, hb, hqb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
  set q' := IsLocalization.integerNormalization (nonZeroDivisors R) q
  have hq'y : aeval P.y q' = 0 := by
    apply hBL
    rw [map_zero, ← hroot, hqb, Algebra.smul_def, map_mul, hqy, mul_zero]
  have hb0 : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ hRK).mpr (nonZeroDivisors.ne_zero hb)
  have hq'0 : q' ≠ 0 := by
    rintro h
    rw [h, Polynomial.map_zero, Algebra.smul_def, Polynomial.algebraMap_apply] at hqb
    exact (mul_ne_zero (C_ne_zero.mpr hb0) hq.ne_zero) hqb.symm
  have hdeg : q'.degree = q.degree := by
    rw [← degree_map_eq_of_injective hRK, hqb, Algebra.smul_def, Polynomial.algebraMap_apply,
      degree_C_mul hb0]
  rw [degree_map_eq_of_injective hRK, ← hdeg]
  exact degree_le_of_dvd (P.dvd_of_aeval_eq_zero q' hq'y) hq'0

omit [IsDomain B] in
/-- **The degree of a covering presentation.** For a covering presentation of an extension of
domains `R ⊆ B` with nonzero conductor element, the degree of `f` is the degree `[L : K]` of the
extension of fraction fields. -/
theorem natDegree_f_eq_finrank (hc : P.c ≠ 0) : P.f.natDegree = Module.finrank K L := by
  set y' := algebraMap B L P.y
  have hmin := P.minpoly_eq_map K L
  have hint : IsIntegral K y' := by
    by_contra h
    rw [minpoly.eq_zero h] at hmin
    exact (P.monic.map (algebraMap R K)).ne_zero hmin.symm
  have hcL : algebraMap R L P.c ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K L]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hc)
  have hB : ∀ b : B, algebraMap B L b ∈ K⟮y'⟯ := fun b ↦ by
    have h := congrArg (algebraMap B L) (P.aeval_numer b)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← aeval_algebraMap_apply,
      ← aeval_map_algebraMap K] at h
    have hmem : aeval y' ((P.numer b).map (algebraMap R K)) ∈ K⟮y'⟯ :=
      IntermediateField.algebra_adjoin_le_adjoin K {y'}
        (Polynomial.aeval_mem_adjoin_singleton K y')
    have hcK : algebraMap R L P.c ∈ K⟮y'⟯ := by
      rw [IsScalarTower.algebraMap_apply R K L]
      exact IntermediateField.algebraMap_mem _ _
    have : algebraMap B L b = (algebraMap R L P.c)⁻¹ *
        aeval y' ((P.numer b).map (algebraMap R K)) := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ hcL, one_mul]
    rw [this]
    exact mul_mem (inv_mem hcK) hmem
  have htop : K⟮y'⟯ = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨b, b', -, rfl⟩ := IsFractionRing.div_surjective B x
    exact div_mem (hB b) (hB b')
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint, hmin,
    P.monic.natDegree_map]

end Degree

end CoveringPresentation

/-- **Generic separability, clearing denominators.** If `f ∈ R[t]` is separable over the fraction
field `K` of the domain `R`, there are `δ ≠ 0` in `R` and `U, V ∈ R[t]` with `U f + V f' = δ`. -/
theorem exists_mul_add_mul_derivative_eq_C {R : Type*} [CommRing R] [IsDomain R] (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] {f : R[X]}
    (hf : (f.map (algebraMap R K)).Separable) :
    ∃ δ : R, δ ≠ 0 ∧ ∃ U V : R[X], U * f + V * derivative f = C δ := by
  obtain ⟨u, v, huv⟩ := hf
  obtain ⟨b₁, hb₁, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) u
  obtain ⟨b₂, hb₂, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) v
  set u' := IsLocalization.integerNormalization (nonZeroDivisors R) u
  set v' := IsLocalization.integerNormalization (nonZeroDivisors R) v
  have hinj : Function.Injective (Polynomial.map (algebraMap R K)) :=
    map_injective _ (IsFractionRing.injective R K)
  refine ⟨b₁ * b₂, mul_ne_zero (nonZeroDivisors.ne_zero hb₁) (nonZeroDivisors.ne_zero hb₂),
    C b₂ * u', C b₁ * v', ?_⟩
  apply hinj
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hu, hv, ← derivative_map]
  rw [Algebra.smul_def, Algebra.smul_def]
  simp only [Polynomial.algebraMap_apply, map_mul]
  linear_combination (C (algebraMap R K b₁) * C (algebraMap R K b₂)) * huv

/-- A nonzero scalar multiple of a primitive element is a primitive element. -/
theorem adjoin_simple_eq_top_of_eq_algebraMap_mul {K L : Type*} [Field K] [Field L]
    [Algebra K L] {α x : L} {k : K} (hk : k ≠ 0) (hx : x = algebraMap K L k * α)
    (hα : K⟮α⟯ = ⊤) : K⟮x⟯ = ⊤ := by
  refine eq_top_iff.mpr (hα ▸ adjoin_simple_le_iff.mpr ?_)
  rw [show α = (algebraMap K L k)⁻¹ * x by
    rw [hx, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hk),
      one_mul]]
  exact mul_mem (inv_mem (IntermediateField.algebraMap_mem _ _)) (mem_adjoin_simple_self _ _)

/-- **A common conductor element.** If every element of a finite `R`-algebra `B` has a nonzero
`R`-multiple in `R[y]`, then a single nonzero `c ∈ R` satisfies `c B ⊆ R[y]`. -/
theorem exists_ne_zero_forall_aeval_eq_mul {R B : Type*} [CommRing R] [IsDomain R] [CommRing B]
    [Algebra R B] [Module.Finite R B] (y : B)
    (h : ∀ e : B, ∃ Q : R[X], ∃ d : R, d ≠ 0 ∧ aeval y Q = algebraMap R B d * e) :
    ∃ c : R, c ≠ 0 ∧ ∀ e : B, ∃ Q : R[X], aeval y Q = algebraMap R B c * e := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := B)
  choose Q d hd hQ using h
  classical
  refine ⟨∏ e ∈ S, d e, Finset.prod_ne_zero_iff.mpr fun e _ ↦ hd e, fun e' ↦ ?_⟩
  have he' : e' ∈ Submodule.span R (S : Set B) := hS ▸ Submodule.mem_top
  induction he' using Submodule.span_induction with
  | mem e he =>
    refine ⟨C (∏ e' ∈ S.erase e, d e') * Q e, ?_⟩
    rw [map_mul, aeval_C, hQ, ← Finset.mul_prod_erase S d he, map_mul]
    ring
  | zero => exact ⟨0, by simp⟩
  | add u w _ _ hu hw =>
    obtain ⟨Qu, hQu⟩ := hu
    obtain ⟨Qw, hQw⟩ := hw
    exact ⟨Qu + Qw, by rw [map_add, hQu, hQw, mul_add]⟩
  | smul t u _ hu =>
    obtain ⟨Qu, hQu⟩ := hu
    refine ⟨C t * Qu, ?_⟩
    rw [map_mul, aeval_C, hQu, Algebra.smul_def]
    ring

/-- A finite separable extension `L / K` of fraction fields of an integral extension `R ⊆ B` has a
primitive element in `B`. -/
theorem exists_adjoin_simple_algebraMap_eq_top (R B K L : Type*) [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra R L] [IsScalarTower R B L] [IsScalarTower R K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : ∃ y₀ : B, K⟮algebraMap B L y₀⟯ = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective B α
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨r, hr0, b', hbb'⟩ := SmoothLocusConnected.exists_ne_zero_dvd_algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) b) hb0
  refine ⟨a * b', adjoin_simple_eq_top_of_eq_algebraMap_mul
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0) ?_ hα⟩
  have hr : algebraMap K L (algebraMap R K r) = algebraMap B L b * algebraMap B L b' := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R B L, hbb', map_mul]
  rw [hr, ← hab, map_mul, eq_comm, mul_comm, div_mul_eq_mul_div,
    div_eq_iff ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb0)]
  ring

/-- If `y ∈ B` generates `L / K`, every element of `B` has a nonzero `R`-multiple in `R[y]`. -/
theorem exists_aeval_eq_algebraMap_mul_of_adjoin_eq_top (R B K L : Type*) [CommRing R]
    [IsDomain R] [CommRing B] [Algebra R B] [Field K] [Field L] [Algebra R K]
    [IsFractionRing R K] [Algebra B L] [Algebra K L] [Algebra R L] [IsScalarTower R B L]
    [IsScalarTower R K L] [Algebra.IsAlgebraic K L] {y : B}
    (hBL : Function.Injective (algebraMap B L)) (hy : K⟮algebraMap B L y⟯ = ⊤) (e : B) :
    ∃ Q : R[X], ∃ d : R, d ≠ 0 ∧ aeval y Q = algebraMap R B d * e := by
  have he : algebraMap B L e ∈ K⟮algebraMap B L y⟯.toSubalgebra := by
    rw [hy]
    trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨p, hp⟩ := he
  obtain ⟨d, hd, hpd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors R) p, d,
    nonZeroDivisors.ne_zero hd, hBL ?_⟩
  have hp' : aeval (algebraMap B L y) p = algebraMap B L e := hp
  rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap K, hpd, Algebra.smul_def,
    Polynomial.algebraMap_apply, map_mul (aeval (algebraMap B L y)), aeval_C, hp', map_mul,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R B L]

attribute [local instance] FractionRing.liftAlgebra in
/-- **Covering presentations exist.** A finite extension `R ⊆ B` of domains of characteristic
zero has a covering presentation with nonzero conductor element and nonzero `δ`. -/
theorem exists_coveringPresentation (R B : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) :
    ∃ P : CoveringPresentation R B, P.c ≠ 0 ∧ P.δ ≠ 0 := by
  have : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Algebra.IsIntegral R B := inferInstance
  set K := FractionRing R
  set L := FractionRing B
  have : IsScalarTower R B L := inferInstance
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  have : FiniteDimensional K L := inferInstance
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  have : Algebra.IsSeparable K L := inferInstance
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  obtain ⟨y₀, hprim₀⟩ := exists_adjoin_simple_algebraMap_eq_top R B K L
  set m := minpoly K (algebraMap B L y₀)
  have hy₀int : IsIntegral K (algebraMap B L y₀) := Algebra.IsIntegral.isIntegral _
  have hmmon : m.Monic := minpoly.monic hy₀int
  set s : R := (IsLocalization.commonDenom (nonZeroDivisors R) m.support m.coeff : R)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero (IsLocalization.commonDenom _ _ _).2
  set sK := algebraMap R K s
  obtain ⟨F, hFmap, -, hFmon⟩ := lifts_and_natDegree_eq_and_monic
    (IsLocalization.scaleRoots_commonDenom_mem_lifts (nonZeroDivisors R) m
      (hmmon.leadingCoeff ▸ one_mem _)) ((monic_scaleRoots_iff sK).mpr hmmon)
  set y := algebraMap R B s * y₀
  have hyL : algebraMap B L y = algebraMap K L sK * algebraMap B L y₀ := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K L]
  have hprim : K⟮algebraMap B L y⟯ = ⊤ :=
    adjoin_simple_eq_top_of_eq_algebraMap_mul ((map_ne_zero_iff _ hRK).mpr hs0) hyL hprim₀
  have hroot : ∀ Q : R[X], aeval (algebraMap B L y) (Q.map (algebraMap R K)) =
      algebraMap B L (aeval y Q) := fun Q ↦ by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply]
  have hFy : aeval y F = 0 := by
    apply hBL
    rw [← hroot, hFmap, map_zero, hyL]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval K _)
  have hyint : IsIntegral K (algebraMap B L y) := Algebra.IsIntegral.isIntegral _
  have hFmin : F.map (algebraMap R K) = minpoly K (algebraMap B L y) := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hyint) (hFmon.map _)
      (minpoly.dvd K _ (by rw [hroot, hFy, map_zero])) ?_
    rw [hFmap, natDegree_scaleRoots, ← IntermediateField.adjoin.finrank hyint,
      ← IntermediateField.adjoin.finrank hy₀int, hprim, hprim₀]
  have hdvd : ∀ Q : R[X], aeval y Q = 0 → F ∣ Q := fun Q hQ ↦ by
    rw [← map_dvd_map (algebraMap R K) hRK hFmon, hFmin]
    exact minpoly.dvd K _ (by rw [hroot, hQ, map_zero])
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_forall_aeval_eq_mul y
    (exists_aeval_eq_algebraMap_mul_of_adjoin_eq_top R B K L hBL hprim)
  have hsepK : (F.map (algebraMap R K)).Separable := by
    rw [hFmin]
    exact Algebra.IsSeparable.isSeparable K _
  obtain ⟨δ, hδ0, U, V, hUV⟩ := exists_mul_add_mul_derivative_eq_C K hsepK
  exact ⟨⟨y, F, c, δ, hFmon, hFy, hdvd, hc, U, V, hUV⟩, hc0, hδ0⟩

end MMP.GenericCovering
