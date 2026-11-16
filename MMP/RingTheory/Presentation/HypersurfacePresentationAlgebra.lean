module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FiniteCoveringModel

/-!
# Points of an algebra with a hypersurface presentation

Let `A` be a `ℂ`-algebra together with a map `g : ℂ[x₁, …, xₛ] → A`, an element `y ∈ A` and a
monic irreducible `f ∈ ℂ[x][t]` such that the kernel of `Q ↦ Q(y)` on `ℂ[x][t]` is `(f)`, and an
element `c ∈ ℂ[x]` with `c A ⊆ ℂ[x][y]` (a conductor element). This is what Noether normalization
and a primitive element give for a finitely generated domain. Then the `ℂ`-points
`φ : A → ℂ` with `φ(c) ≠ 0` are the points `(x, t) = (φ(x), φ(y))` of the hypersurface
`{c(x) ≠ 0, f(x, t) = 0}`, and each value `φ(a)` is `Q(x, t) / c(x)` for any `Q` with
`Q(y) = c a`. Hence, for `δ ∈ ℂ[x]` divisible by `c` such that `f_x` is separable where
`δ(x) ≠ 0`, the set of points with `φ(δ) ≠ 0` is a continuous image of the connected
`modelHypersurface f δ`, and so is connected (in the topology of pointwise convergence).

## Main definitions

* `MMP.SmoothLocusConnected.HypersurfacePresentation`: the data above.

## Main results

* `MMP.SmoothLocusConnected.HypersurfacePresentation.isPreconnected_image_coe`:
  the points `φ` with `φ(δ) ≠ 0`, viewed as functions `A → ℂ`, form a preconnected set.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open Polynomial Filter Topology Set

namespace MMP.SmoothLocusConnected

/-- A *hypersurface presentation* of a `ℂ`-algebra `A`: a map `g : ℂ[x₁, …, xₛ] → A`, an element
`y` whose relations over `ℂ[x]` are the multiples of a monic irreducible `f`, and a conductor
element `c ∈ ℂ[x]` with `c A ⊆ ℂ[x][y]`. -/
structure HypersurfacePresentation (A : Type*) [CommRing A] [Algebra ℂ A] (s : ℕ) where
  /-- The coordinates `x₁, …, xₛ`. -/
  g : MvPolynomial (Fin s) ℂ →ₐ[ℂ] A
  /-- The element generating `A` over `ℂ[x]` up to the conductor. -/
  y : A
  /-- The relation of `y` over `ℂ[x]`. -/
  f : (MvPolynomial (Fin s) ℂ)[X]
  /-- The conductor element. -/
  c : MvPolynomial (Fin s) ℂ
  /-- The relation `f` is monic. -/
  monic : f.Monic
  /-- The relation `f` is irreducible. -/
  irreducible : Irreducible f
  /-- The element `y` is a root of `f`. -/
  eval₂_f : f.eval₂ g.toRingHom y = 0
  /-- Every polynomial over `ℂ[x]` vanishing at `y` is a multiple of `f`. -/
  dvd_of_eval₂_eq_zero : ∀ Q : (MvPolynomial (Fin s) ℂ)[X], Q.eval₂ g.toRingHom y = 0 → f ∣ Q
  /-- For every `a ∈ A`, the element `c a` lies in `ℂ[x][y]`. -/
  exists_eval₂_eq_mul : ∀ a : A, ∃ Q : (MvPolynomial (Fin s) ℂ)[X], Q.eval₂ g.toRingHom y = g c * a

namespace HypersurfacePresentation

variable {A : Type*} [CommRing A] [Algebra ℂ A] {s : ℕ} (P : HypersurfacePresentation A s)

/-- A chosen `Q` with `Q(y) = c a`. -/
noncomputable def numer (a : A) : (MvPolynomial (Fin s) ℂ)[X] := (P.exists_eval₂_eq_mul a).choose

/-- The polynomial `numer a` evaluates at `y` to `c a`. -/
lemma eval₂_numer (a : A) : (P.numer a).eval₂ P.g.toRingHom P.y = P.g P.c * a :=
  (P.exists_eval₂_eq_mul a).choose_spec

/-- The candidate value at `a` of the point over `u = (x, t)`: `Q(x, t) / c(x)` with
`Q(y) = c a`. -/
noncomputable def pointFun (u : (Fin s → ℂ) × ℂ) (a : A) : ℂ :=
  (P.numer a).eval₂ (MvPolynomial.eval u.1) u.2 / MvPolynomial.eval u.1 P.c

variable {P} {u : (Fin s → ℂ) × ℂ}

/-- At a point `u = (x, t)` with `f(x, t) = 0`, two polynomials `Q, Q'` with `Q(y) = Q'(y)`
take the same value. -/
lemma eval₂_eq_of_eval₂_eq (hu : P.f.eval₂ (MvPolynomial.eval u.1) u.2 = 0)
    {Q Q' : (MvPolynomial (Fin s) ℂ)[X]}
    (h : Q.eval₂ P.g.toRingHom P.y = Q'.eval₂ P.g.toRingHom P.y) :
    Q.eval₂ (MvPolynomial.eval u.1) u.2 = Q'.eval₂ (MvPolynomial.eval u.1) u.2 := by
  obtain ⟨R, hR⟩ := P.dvd_of_eval₂_eq_zero (Q - Q') (by rw [eval₂_sub, h, sub_self])
  have := congrArg (fun p ↦ p.eval₂ (MvPolynomial.eval u.1) u.2) hR
  simp only [eval₂_sub, eval₂_mul, hu, zero_mul] at this
  exact sub_eq_zero.mp this

/-- At a point `u = (x, t)` with `f(x, t) = 0` and `c(x) ≠ 0`, a polynomial `Q` with
`Q(y) = c a` satisfies `Q(x, t) = c(x) · pointFun u a`. -/
lemma eval₂_eq_mul_pointFun (hu : P.f.eval₂ (MvPolynomial.eval u.1) u.2 = 0)
    (hc : MvPolynomial.eval u.1 P.c ≠ 0) {Q : (MvPolynomial (Fin s) ℂ)[X]} {a : A}
    (h : Q.eval₂ P.g.toRingHom P.y = P.g P.c * a) :
    Q.eval₂ (MvPolynomial.eval u.1) u.2 = MvPolynomial.eval u.1 P.c * P.pointFun u a := by
  rw [pointFun, mul_div_cancel₀ _ hc]
  exact eval₂_eq_of_eval₂_eq hu (h.trans (P.eval₂_numer a).symm)

/-- At a point `u = (x, t)` with `f(x, t) = 0` and `c(x) ≠ 0`, `pointFun u (g(b) a)` is
`b(x) · pointFun u a`. -/
lemma pointFun_g_mul (hu : P.f.eval₂ (MvPolynomial.eval u.1) u.2 = 0)
    (hc : MvPolynomial.eval u.1 P.c ≠ 0) (b : MvPolynomial (Fin s) ℂ) (a : A) :
    P.pointFun u (P.g b * a) = MvPolynomial.eval u.1 b * P.pointFun u a := by
  have h := eval₂_eq_mul_pointFun hu hc (Q := C b * P.numer a) (a := P.g b * a)
    (by rw [eval₂_mul, eval₂_C, eval₂_numer]; simp only [AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]; ring)
  rw [eval₂_mul, eval₂_C, ← mul_div_cancel₀ ((P.numer a).eval₂ (MvPolynomial.eval u.1) u.2) hc,
    ← pointFun] at h
  exact (mul_left_cancel₀ hc (by rw [← h]; ring)).symm

/-- The `ℂ`-point of `A` over a point `u` of the hypersurface `{c ≠ 0, f = 0}`. -/
noncomputable def point (hu : P.f.eval₂ (MvPolynomial.eval u.1) u.2 = 0)
    (hc : MvPolynomial.eval u.1 P.c ≠ 0) : A →ₐ[ℂ] ℂ where
  toFun := P.pointFun u
  map_one' := by
    have h := eval₂_eq_mul_pointFun hu hc (Q := C P.c) (a := 1) (by simp)
    rw [eval₂_C] at h
    exact (mul_eq_left₀ hc).mp h.symm
  map_mul' a b := by
    have h := eval₂_eq_mul_pointFun hu hc (Q := P.numer a * P.numer b) (a := P.g P.c * (a * b))
      (by rw [eval₂_mul, eval₂_numer, eval₂_numer]; ring)
    rw [eval₂_mul, pointFun_g_mul hu hc, eval₂_eq_mul_pointFun hu hc (P.eval₂_numer a),
      eval₂_eq_mul_pointFun hu hc (P.eval₂_numer b)] at h
    exact mul_left_cancel₀ hc (mul_left_cancel₀ hc (by rw [← h]; ring))
  map_zero' := by
    have h := eval₂_eq_mul_pointFun hu hc (Q := 0) (a := 0) (by simp)
    rw [eval₂_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  map_add' a b := by
    have h := eval₂_eq_mul_pointFun hu hc (Q := P.numer a + P.numer b) (a := a + b)
      (by rw [eval₂_add, eval₂_numer, eval₂_numer]; ring)
    rw [eval₂_add, eval₂_eq_mul_pointFun hu hc (P.eval₂_numer a),
      eval₂_eq_mul_pointFun hu hc (P.eval₂_numer b)] at h
    exact mul_left_cancel₀ hc (by rw [mul_add, h])
  commutes' r := by
    have h := eval₂_eq_mul_pointFun hu hc (Q := C (P.c * MvPolynomial.C r))
      (a := algebraMap ℂ A r) (by rw [eval₂_C]; simp [Algebra.algebraMap_eq_smul_one])
    rw [eval₂_C, map_mul, MvPolynomial.eval_C] at h
    exact (mul_left_cancel₀ hc h).symm

/-- The point over `u` takes the value `pointFun u a` at `a`. -/
lemma point_apply (hu : P.f.eval₂ (MvPolynomial.eval u.1) u.2 = 0)
    (hc : MvPolynomial.eval u.1 P.c ≠ 0) (a : A) : point hu hc a = P.pointFun u a := rfl

/-- The point over `u = (x, t)` sends `g(b)` to `b(x)`. -/
lemma point_g (hu : P.f.eval₂ (MvPolynomial.eval u.1) u.2 = 0)
    (hc : MvPolynomial.eval u.1 P.c ≠ 0) (b : MvPolynomial (Fin s) ℂ) :
    point hu hc (P.g b) = MvPolynomial.eval u.1 b := by
  have := pointFun_g_mul hu hc b 1
  rw [mul_one] at this
  rw [point_apply, this, ← point_apply hu hc, map_one, mul_one]

/-- A `ℂ`-point `φ` of `A` is determined on `ℂ[x]` by the values `φ(xᵢ)`. -/
lemma apply_g (φ : A →ₐ[ℂ] ℂ) (b : MvPolynomial (Fin s) ℂ) :
    φ (P.g b) = MvPolynomial.eval (fun i ↦ φ (P.g (MvPolynomial.X i))) b := by
  have : φ.comp P.g = MvPolynomial.aeval (fun i ↦ φ (P.g (MvPolynomial.X i))) :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  simpa [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom] using DFunLike.congr_fun this b

/-- A `ℂ`-point `φ` of `A` sends `Q(y)` to `Q` evaluated at `((φ(x₁), …, φ(xₛ)), φ(y))`. -/
lemma apply_eval₂ (φ : A →ₐ[ℂ] ℂ) (Q : (MvPolynomial (Fin s) ℂ)[X]) :
    φ (Q.eval₂ P.g.toRingHom P.y) =
      Q.eval₂ (MvPolynomial.eval fun i ↦ φ (P.g (MvPolynomial.X i))) (φ P.y) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | monomial k a =>
    rw [eval₂_monomial, eval₂_monomial, map_mul, map_pow, ← apply_g]
    rfl

/-- A `ℂ`-point `φ` of `A` with `φ(c) ≠ 0` takes the value `pointFun u a` at `a`, where
`u = ((φ(x₁), …, φ(xₛ)), φ(y))`. -/
lemma pointFun_apply_eq (φ : A →ₐ[ℂ] ℂ) (hc : φ (P.g P.c) ≠ 0) (a : A) :
    P.pointFun (fun i ↦ φ (P.g (MvPolynomial.X i)), φ P.y) a = φ a := by
  rw [pointFun, ← apply_eval₂, eval₂_numer, map_mul, ← apply_g, mul_div_cancel_left₀ _ hc]

variable (P) in
/-- The candidate values `pointFun u` depend continuously on `u` where `c(x) ≠ 0`. -/
lemma continuousOn_pointFun {S : Set ((Fin s → ℂ) × ℂ)}
    (hS : ∀ u ∈ S, MvPolynomial.eval u.1 P.c ≠ 0) :
    ContinuousOn (fun u a ↦ P.pointFun u a) S := by
  refine continuousOn_pi.mpr fun a ↦ ContinuousOn.div ?_ ?_ hS
  · exact (contDiff_eval_map (P.numer a) (m := 0)).continuous.continuousOn.congr
      fun u _ ↦ (eval_map _ _).symm
  · exact ((MvPolynomial.continuous_eval P.c).comp continuous_fst).continuousOn

variable (P) in
/-- **The points off `δ = 0` form a connected set.** For a hypersurface presentation of `A` and a
nonzero `δ ∈ ℂ[x]` divisible by the conductor element, such that `f_x` is separable wherever
`δ(x) ≠ 0`, the `ℂ`-points `φ` of `A` with `φ(δ) ≠ 0`, as functions `A → ℂ`, form a preconnected
set. -/
theorem isPreconnected_image_coe {δ : MvPolynomial (Fin s) ℂ} (hδ : δ ≠ 0) (hcδ : P.c ∣ δ)
    (hsep : ∀ x, MvPolynomial.eval x δ ≠ 0 → (P.f.map (MvPolynomial.eval x)).Separable) :
    IsPreconnected ((fun φ : A →ₐ[ℂ] ℂ ↦ (φ : A → ℂ)) '' {φ | φ (P.g δ) ≠ 0}) := by
  obtain ⟨e, he⟩ := hcδ
  have hcne : ∀ u ∈ modelHypersurface P.f δ, MvPolynomial.eval u.1 P.c ≠ 0 := fun u hu ↦ by
    have := hu.1
    rw [he, map_mul] at this
    exact left_ne_zero_of_mul this
  have himage : (fun φ : A →ₐ[ℂ] ℂ ↦ (φ : A → ℂ)) '' {φ | φ (P.g δ) ≠ 0} =
      (fun u a ↦ P.pointFun u a) '' modelHypersurface P.f δ := by
    ext F
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      set u : (Fin s → ℂ) × ℂ := (fun i ↦ φ (P.g (MvPolynomial.X i)), φ P.y)
      have hu : u ∈ modelHypersurface P.f δ :=
        ⟨by rwa [← apply_g], by rw [eval_map, ← apply_eval₂, P.eval₂_f, map_zero]⟩
      have hc : φ (P.g P.c) ≠ 0 := by rw [apply_g]; exact hcne u hu
      exact ⟨u, hu, funext (pointFun_apply_eq φ hc)⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨point ((eval_map _ _).symm.trans hu.2) (hcne u hu), by simpa [point_g] using hu.1, rfl⟩
  rw [himage]
  exact (isPreconnected_modelHypersurface P.monic P.irreducible hδ hsep).image _
    (P.continuousOn_pointFun hcne)

end HypersurfacePresentation

end MMP.SmoothLocusConnected
