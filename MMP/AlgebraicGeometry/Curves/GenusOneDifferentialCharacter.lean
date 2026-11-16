module
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringModuleComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.AutomorphismSchemeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# The differential character of an automorphism of a genus-one curve

Let `C` be a smooth connected proper curve of genus one over an algebraically closed field `K`
of characteristic zero. The space `H⁰(C, Ω¹_{C/K})` of regular differentials is one-dimensional
over `K`, and every automorphism `σ` of `C` over `K` acts on it, by pullback of differentials, as
multiplication by a scalar `χ` with `χ⁴ = 1` or `χ⁶ = 1`. In particular `σ` acts trivially on
the space `H⁰(C, ω_C^{⊗12})` of `12`-canonical forms.

A closed point of `C` is a `K`-rational section, so `C` is geometrically connected and,
being geometrically normal, has `H⁰(C, 𝒪_C) = K`; then `dim_K H⁰(C, Ω¹_{C/K}) = g = 1`, and
`Ω¹_{C/K}` is trivial, being of degree `2g - 2 = 0` with a nonzero section. A trivialising
differential `ω₀` gives a derivation `D` of `𝒪_C`, `d a = D(a) ω₀`, whose values on an affine open
generate the unit ideal. An automorphism `σ` acting on `H⁰(C, Ω¹)` by the scalar `χ` satisfies
`D (σ^♯ a) = χ σ^♯ (D a)` on every open.

If `σ` fixes a rational point `p`, write `C ∖ {p}` as the affine Weierstrass curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` of a Weierstrass model at `p`. The norm degree on its
coordinate ring is `dim_K A/(a)`, hence invariant under `σ^♯`, so `σ^♯ x = u²x + r` and
`σ^♯ y = u³y + u²sx + t` with `(u, r, s, t) • W = W`; the derivation is a nonzero constant
multiple of `(2y + a₁x + a₃) ∂/∂x - (a₁y - 3x² - 2a₂x - a₄) ∂/∂y`, since its values generate the
unit ideal and the units of `A` are constants; comparing the coefficients of `y` in
`D (σ^♯ x) = χ σ^♯ (D x)` gives `χ = u⁻¹`, and `c₄ = u⁻⁴c₄`, `c₆ = u⁻⁶c₆` with `c₄, c₆` not both
zero give `χ⁴ = 1` or `χ⁶ = 1`.

If `σ` fixes no rational point, identify the rational points with the points of a Weierstrass
model `W` at a base point. Using a nonzero `2`-torsion point and the infinitude of `W(K)`, choose
`P` with `P ≠ 0`, `σ P ≠ 0` and `2 σ P ≠ P`, and put `Q = P - σ P`. On the open `x ≠ x(Q)` the
addition formula `R ↦ R + Q` is a morphism into `C`; it extends to an automorphism `ρ` of the
proper curve `C`, the extension for `-Q` being its inverse because the two agree with the identity
at the closed points of a dense open. The addition formula preserves the invariant derivation, an
identity of rational functions modulo the two Weierstrass equations, so `ρ` acts trivially on
`H⁰(C, Ω¹)`. Then `σ ≫ ρ` fixes `P` and acts by `χ`, and the first case applies.

For the action on `ω^{⊗n}`, a trivialisation `e : Ω¹_{C/K} ≅ 𝒪_C` induces trivialisations
`E n : ω^{⊗n} ≅ 𝒪_C`, with `E (n + 1)` the tensor product of `E n` and `e` followed by the unitor.
The transpose of `ψ (n + 1)` carries a local pure tensor `a ⊗ b` to the tensor of the transposes
of `ψ n` and of the action on differentials applied to `a` and `b`; by induction it carries the
generator `(E n)⁻¹ 1` to an element with coordinate `χⁿ`. Since the transpose is
`σ^♯`-semilinear, `σ^♯` fixes the constants and `H⁰(C, 𝒪_C) = K`, it acts on `H⁰(C, ω^{⊗n})` as
multiplication by `χⁿ`, which is the identity for `n = 12`.

## Main results

* `MMP.finrank_eq_one_and_exists_smul_of_genus_eq_one`

## Implementation notes

The canonical bundle of the smooth curve is the sheaf of relative differentials
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials f`; on a curve it is its own top exterior
power. Its global sections are taken as a `K`-module through the pushforward to `Spec K`
followed by `AlgebraicGeometry.moduleSpecΓFunctor`. The complex numbers are replaced by an
algebraically closed field of characteristic zero.

The action of `σ` on `ω_C^{⊗n}` is the `n`-th tensor power of its action
`φ : σ^* Ω¹ ⟶ Ω¹` on differentials: the morphisms `ψ n : σ^* (Ω¹)^{⊗n} ⟶ (Ω¹)^{⊗n}` with
`ψ 0` the canonical `σ^* 𝒪_C ≅ 𝒪_C` and `ψ (n + 1)` the pullback-tensor comparison
`σ^* (A ⊗ B) ⟶ σ^* A ⊗ σ^* B` followed by `ψ n ⊗ φ`. These conditions determine `ψ`, and the
statement quantifies over every such family.

## References

* [O. Fujino et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][Silverman], III.10
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace MMP

namespace EllipticDifferentialCharacter

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

/-- A connected proper smooth curve over an algebraically closed field has `H⁰(C, 𝒪_C) = K`. -/
private theorem isIso_appTop_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f] [ConnectedSpace C] :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨x, hx⟩ := (inferInstance : Nonempty C).elim fun x =>
    (isClosed_univ (X := C)).exists_closed_singleton ⟨x, trivial⟩ |>.imp fun _ h => h.2
  have hs := pointOfClosedPoint_comp f x hx
  have : GeometricallyConnected f := geometricallyConnected_of_connectedSpace_of_section f _ hs
  exact ((isIso_globalSections_tfae_geometricallyConnected_irreducible_integral K f
    (isGeometricallyNormal_of_smooth f)).out 1 2).mpr this

private theorem finrank_globalSections_relativeDifferentials
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f] [ConnectedSpace C]
    (hg : genus f = 1) :
    Module.finrank K (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward f).obj (Scheme.Hom.relativeDifferentials f))) = 1 := by
  have := isIso_appTop_of_isAlgClosed f
  rw [← hg, ← finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus f,
    (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f _).finrank_eq]
  rfl

namespace EllAlg

open Polynomial

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

local notation "A" => W.toAffine.CoordinateRing
local notation "mkW" => WeierstrassCurve.Affine.CoordinateRing.mk W
local notation "aW" => algebraMap K W.toAffine.CoordinateRing

/-- The norm degree. -/
private noncomputable def ndeg (a : A) : ℕ := (Algebra.norm K[X] a).natDegree

/-- The coordinate `x`. -/
private noncomputable def xA : A := mkW (C X)
/-- The coordinate `y`. -/
private noncomputable def yA : A := mkW X

private theorem finrank_quot_eq (a : A) (ha : a ≠ 0) :
    Module.finrank K (A ⧸ Ideal.span {a}) = ndeg W a :=
  finrank_quotient_span_eq_natDegree_norm (WeierstrassCurve.Affine.CoordinateRing.basis W) ha

private theorem ndeg_map (ψ : A ≃ₐ[K] A) (a : A) (ha : a ≠ 0) : ndeg W (ψ a) = ndeg W a := by
  rw [← finrank_quot_eq W a ha, ← finrank_quot_eq W (ψ a) (by simpa using ha)]
  refine (LinearEquiv.finrank_eq ?_).symm
  refine (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {ψ a}) ψ ?_).toLinearEquiv
  rw [Ideal.map_span]; simp

private theorem mk_C_eq_aeval (p : K[X]) : mkW (C p) = aeval (xA W) p := by
  have : (mkW).comp C = (aeval (xA W)).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]; rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]; rfl
  exact congrArg (fun φ : K[X] →+* A => φ p) this

private theorem repr (a : A) : ∃ p q : K[X], a = aeval (xA W) p + aeval (xA W) q * yA W := by
  obtain ⟨p, q, h⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  refine ⟨p, q, ?_⟩
  rw [← h, WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
    mk_C_eq_aeval, mk_C_eq_aeval, mul_one]
  rfl

private theorem eq_zero_of_repr {p q : K[X]} (h : aeval (xA W) p + aeval (xA W) q * yA W = 0) :
    p = 0 ∧ q = 0 := by
  refine WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := W) ?_
  rwa [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
    mk_C_eq_aeval, mk_C_eq_aeval, mul_one]

private theorem degree_norm_repr (p q : K[X]) :
    (Algebra.norm K[X] (aeval (xA W) p + aeval (xA W) q * yA W)).degree
      = max (2 • p.degree) (2 • q.degree + 3) := by
  have := WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis (W' := W) p q
  rwa [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
    mk_C_eq_aeval, mk_C_eq_aeval, mul_one] at this

private theorem ndeg_repr (p q : K[X]) (hq : q ≠ 0) :
    ndeg W (aeval (xA W) p + aeval (xA W) q * yA W) = max (2 * p.natDegree) (2 * q.natDegree +
        3) := by
  unfold ndeg
  apply natDegree_eq_of_degree_eq_some
  rw [degree_norm_repr, degree_eq_natDegree hq]
  by_cases hp : p = 0
  · subst hp
    simp only [degree_zero, natDegree_zero, mul_zero]
    rw [show (2 • (⊥ : WithBot ℕ)) = ⊥ from rfl, max_eq_right bot_le]
    simp
  · rw [degree_eq_natDegree hp]; norm_cast

private theorem ndeg_repr0 (p : K[X]) (hp : p ≠ 0) : ndeg W (aeval (xA W) p) = 2 * p.natDegree := by
  have := degree_norm_repr W p 0
  simp only [map_zero, zero_mul, add_zero, degree_zero] at this
  unfold ndeg
  apply natDegree_eq_of_degree_eq_some
  rw [this, degree_eq_natDegree hp, show (2 • (⊥ : WithBot ℕ) + 3) = ⊥ from rfl, max_eq_left bot_le]
  norm_cast

private theorem xA_ne_zero : xA W ≠ 0 := fun h =>
  X_ne_zero (eq_zero_of_repr W (p := X) (q := 0) (by simpa using h)).1

private theorem yA_ne_zero : yA W ≠ 0 := fun h =>
  one_ne_zero (eq_zero_of_repr W (p := 0) (q := 1) (by simpa using h)).2

private theorem ndeg_xA : ndeg W (xA W) = 2 := by
  simpa using ndeg_repr0 W X X_ne_zero

private theorem ndeg_yA : ndeg W (yA W) = 3 := by
  simpa using ndeg_repr W 0 1 one_ne_zero

private theorem psi_x (ψ : A ≃ₐ[K] A) : ∃ α β : K, α ≠ 0 ∧ ψ (xA W) = aW α * xA W + aW β := by
  have hd : ndeg W (ψ (xA W)) = 2 := by rw [ndeg_map W ψ _ (xA_ne_zero W), ndeg_xA]
  obtain ⟨p, q, hpq⟩ := repr W (ψ (xA W))
  by_cases hq : q = 0
  · subst hq
    simp only [map_zero, zero_mul, add_zero] at hpq
    have hp : p ≠ 0 := by
      rintro rfl; simp only [map_zero, EmbeddingLike.map_eq_zero_iff] at hpq; exact xA_ne_zero W hpq
    rw [hpq, ndeg_repr0 W p hp] at hd
    have h1 : p.natDegree = 1 := by omega
    obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one h1.le
    refine ⟨a, b, ?_, ?_⟩
    · rintro rfl; simp at h1
    · rw [hpq]; simp [Algebra.smul_def]
  · rw [hpq, ndeg_repr W p q hq] at hd
    omega

private theorem psi_y (ψ : A ≃ₐ[K] A) :
    ∃ γ δ ε : K, γ ≠ 0 ∧ ψ (yA W) = aW γ * yA W + aW δ * xA W + aW ε := by
  have hd : ndeg W (ψ (yA W)) = 3 := by rw [ndeg_map W ψ _ (yA_ne_zero W), ndeg_yA]
  obtain ⟨p, q, hpq⟩ := repr W (ψ (yA W))
  by_cases hq : q = 0
  · subst hq
    simp only [map_zero, zero_mul, add_zero] at hpq
    have hp : p ≠ 0 := by
      rintro rfl; simp only [map_zero, EmbeddingLike.map_eq_zero_iff] at hpq; exact yA_ne_zero W hpq
    rw [hpq, ndeg_repr0 W p hp] at hd
    omega
  · rw [hpq, ndeg_repr W p q hq] at hd
    have hq0 : q.natDegree = 0 := by omega
    have hp1 : p.natDegree ≤ 1 := by omega
    obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hp1
    rw [eq_C_of_natDegree_eq_zero hq0] at hpq hq
    refine ⟨q.coeff 0, a, b, fun h => hq (by rw [h, C_0]), ?_⟩
    rw [hpq]; simp [Algebra.smul_def]; ring

private theorem rel : yA W ^ 2 + aW W.a₁ * xA W * yA W + aW W.a₃ * yA W
    = xA W ^ 3 + aW W.a₂ * xA W ^ 2 + aW W.a₄ * xA W + aW W.a₆ := by
  have h : mkW (Polynomial.X ^ 2 + C (C W.a₁ * Polynomial.X + C W.a₃) * Polynomial.X -
      C (Polynomial.X ^ 3 + C W.a₂ * Polynomial.X ^ 2 + C W.a₄ * Polynomial.X + C W.a₆)) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_mul, map_pow] at h
  change yA W ^ 2 + (aW W.a₁ * xA W + aW W.a₃) * yA W -
    (xA W ^ 3 + aW W.a₂ * xA W ^ 2 + aW W.a₄ * xA W + aW W.a₆) = 0 at h
  linear_combination h

private theorem coeff_zero {c₀ c₁ c₂ c₃ d₀ d₁ : K}
    (h : aW c₃ * xA W ^ 3 + aW c₂ * xA W ^ 2 + aW c₁ * xA W + aW c₀ +
      (aW d₁ * xA W + aW d₀) * yA W = 0) :
    c₃ = 0 ∧ c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 ∧ d₁ = 0 ∧ d₀ = 0 := by
  obtain ⟨hp, hq⟩ := eq_zero_of_repr W (p := C c₃ * Polynomial.X ^ 3 + C c₂ * Polynomial.X ^ 2 +
      C c₁ * Polynomial.X + C c₀)
    (q := C d₁ * Polynomial.X + C d₀) (by simpa using h)
  have h3 := congrArg (fun p => p.coeff 3) hp
  have h2 := congrArg (fun p => p.coeff 2) hp
  have h1 := congrArg (fun p => p.coeff 1) hp
  have h0 := congrArg (fun p => p.coeff 0) hp
  have g1 := congrArg (fun p => p.coeff 1) hq
  have g0 := congrArg (fun p => p.coeff 0) hq
  simp [coeff_X, coeff_C, coeff_X_pow] at h3 h2 h1 h0 g1 g0
  exact ⟨h3, h2, h1, h0, g1, g0⟩

private theorem jacobian : ∃ Bx By : A, aW W.Δ =
    Bx * (aW W.a₁ * yA W - (3 * xA W ^ 2 + 2 * aW W.a₂ * xA W + aW W.a₄)) +
      By * (2 * yA W + aW W.a₁ * xA W + aW W.a₃) := by
  have h := AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.Δ_eq_jacobian_zChart
    (W.map (algebraMap K A)) (xA W) (yA W)
    (by simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]; linear_combination rel W)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, WeierstrassCurve.map_Δ] at h
  exact ⟨_, _, h⟩

private theorem eq_algebraMap_of_isUnit (h : A) (hu : IsUnit h) : ∃ c : K, c ≠ 0 ∧ h = aW c := by
  have hn : (Algebra.norm K[X] h).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit (hu.map (Algebra.norm K[X]))
  have hd : ndeg W h = 0 := hn
  obtain ⟨p, q, hpq⟩ := repr W h
  by_cases hq : q = 0
  · subst hq
    simp only [map_zero, zero_mul, add_zero] at hpq
    have hp : p ≠ 0 := by rintro rfl; simp at hpq; exact hu.ne_zero hpq
    rw [hpq, ndeg_repr0 W p hp] at hd
    rw [eq_C_of_natDegree_eq_zero (by omega : p.natDegree = 0)] at hpq hp
    refine ⟨p.coeff 0, fun h0 => hp (by rw [h0, C_0]), by rw [hpq, aeval_C]⟩
  · rw [hpq, ndeg_repr W p q hq] at hd
    omega

variable [W.IsElliptic]

private theorem deriv_form (D : Derivation K A A) (hD : Ideal.span (Set.range D) = ⊤) :
    ∃ c : K, c ≠ 0 ∧ D (xA W) = aW c * (2 * yA W + aW W.a₁ * xA W + aW W.a₃) ∧
      D (yA W) = aW c * (3 * xA W ^ 2 + 2 * aW W.a₂ * xA W + aW W.a₄ - aW W.a₁ * yA W) := by
  have hrel := congrArg D (rel W)
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    smul_eq_mul, mul_zero, add_zero, zero_add, nsmul_eq_mul, Nat.cast_ofNat] at hrel
  norm_num at hrel
  obtain ⟨Bx, By, hΔ⟩ := jacobian W
  have hΔ0 : W.Δ ≠ 0 := (WeierstrassCurve.IsElliptic.isUnit (W := W)).ne_zero
  obtain ⟨h, hh⟩ : ∃ h : A, h = aW W.Δ⁻¹ * (By * D (xA W) - Bx * D (yA W)) := ⟨_, rfl⟩
  have hinv : aW W.Δ⁻¹ * aW W.Δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hΔ0, map_one]
  have hF : D (xA W) = h * (2 * yA W + aW W.a₁ * xA W + aW W.a₃) := by
    rw [hh]
    linear_combination (-D (xA W)) * hinv + aW W.Δ⁻¹ * D (xA W) * hΔ + aW W.Δ⁻¹ * Bx * hrel
  have hG : D (yA W) = h * (3 * xA W ^ 2 + 2 * aW W.a₂ * xA W + aW W.a₄ - aW W.a₁ * yA W) := by
    rw [hh]
    linear_combination (-D (yA W)) * hinv + aW W.Δ⁻¹ * D (yA W) * hΔ + aW W.Δ⁻¹ * By * hrel
  have hrange : Set.range D ⊆ Ideal.span {h} := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨p, q, rfl⟩ := repr W a
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    refine ⟨aeval (xA W) (derivative p) * (2 * yA W + aW W.a₁ * xA W + aW W.a₃) +
      aeval (xA W) (derivative q) * (2 * yA W + aW W.a₁ * xA W + aW W.a₃) * yA W +
      aeval (xA W) q * (3 * xA W ^ 2 + 2 * aW W.a₂ * xA W + aW W.a₄ - aW W.a₁ * yA W), ?_⟩
    simp only [map_add, Derivation.leibniz, Derivation.map_aeval, smul_eq_mul]
    rw [hF, hG]; ring
  have hunit : IsUnit h := by
    rw [← Ideal.span_singleton_eq_top, eq_top_iff, ← hD]
    exact Ideal.span_le.mpr hrange
  obtain ⟨c, hc, hc'⟩ := eq_algebraMap_of_isUnit W h hunit
  exact ⟨c, hc, by rw [hF, hc'], by rw [hG, hc']⟩

private theorem chi_pow [CharZero K] (D : Derivation K A A) (hD : Ideal.span (Set.range D) = ⊤)
    (ψ : A ≃ₐ[K] A) (χ : K) (hψ : ∀ a, D (ψ a) = χ • ψ (D a)) : χ ^ 4 = 1 ∨ χ ^ 6 = 1 := by
  obtain ⟨c, hc, hDx, hDy⟩ := deriv_form W D hD
  obtain ⟨α, β, hα, hx⟩ := psi_x W ψ
  obtain ⟨γ, δ, ε, hγ, hy⟩ := psi_y W ψ
  have e1 := hψ (xA W)
  rw [hx, hDx] at e1
  simp only [map_add, map_mul, AlgEquiv.commutes, hx, hy, Derivation.leibniz,
    Derivation.map_algebraMap, smul_eq_mul, mul_zero, add_zero, Algebra.smul_def, map_ofNat] at e1
  rw [hDx] at e1
  obtain ⟨-, -, -, -, -, k1⟩ := coeff_zero W (c₃ := 0) (c₂ := 0)
    (c₁ := α * c * W.a₁ - χ * c * (2 * δ + W.a₁ * α))
    (c₀ := α * c * W.a₃ - χ * c * (2 * ε + W.a₁ * β + W.a₃)) (d₁ := 0)
    (d₀ := 2 * α * c - 2 * χ * c * γ)
    (by simp only [map_sub, map_mul, map_add, map_ofNat, map_zero]; linear_combination e1)
  have e2 := congrArg ψ (rel W)
  simp only [map_add, map_mul, map_pow, AlgEquiv.commutes, hx, hy] at e2
  obtain ⟨k3, k2, k1', k0, k11, k01⟩ := coeff_zero W (c₃ := -α ^ 3 + γ ^ 2)
    (c₂ := W.a₁ * α * δ - W.a₂ * α ^ 2 + W.a₂ * γ ^ 2 - 3 * α ^ 2 * β + δ ^ 2)
    (c₁ := W.a₁ * α * ε + W.a₁ * β * δ - 2 * W.a₂ * α * β + W.a₃ * δ - W.a₄ * α + W.a₄ * γ ^ 2
      - 3 * α * β ^ 2 + 2 * δ * ε)
    (c₀ := W.a₁ * β * ε - W.a₂ * β ^ 2 + W.a₃ * ε - W.a₄ * β + W.a₆ * γ ^ 2 - W.a₆ - β ^ 3
      + ε ^ 2)
    (d₁ := γ * (W.a₁ * α - W.a₁ * γ + 2 * δ)) (d₀ := γ * (W.a₁ * β - W.a₃ * γ + W.a₃ + 2 * ε))
    (by simp only [map_sub, map_mul, map_add, map_ofNat, map_pow, map_neg]
        linear_combination e2 - (aW γ) ^ 2 * rel W)
  -- the scalar
  have hαχ : α = χ * γ := sub_eq_zero.mp <|
    eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero two_ne_zero hc) (by linear_combination k1)
  obtain ⟨u, hu⟩ : ∃ u, u = γ / α := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; exact div_ne_zero hγ hα
  have hαu : α = u ^ 2 := by rw [hu]; field_simp; linear_combination -k3
  have hγu : γ = u ^ 3 := by rw [pow_succ, ← hαu, hu]; field_simp
  have hχ : χ * u = 1 := sub_eq_zero.mp <| eq_zero_of_ne_zero_of_mul_left_eq_zero
    (pow_ne_zero 2 hu0) (by linear_combination hαu - hαχ - χ * hγu)
  obtain ⟨s, hs⟩ : ∃ s, s = δ / u ^ 2 := ⟨_, rfl⟩
  have hδ : δ = u ^ 2 * s := by rw [hs]; field_simp
  simp only [hαu, hγu, hδ] at k2 k1' k0 k11 k01
  have q11 : W.a₁ - W.a₁ * u + 2 * s = 0 :=
    eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero 5 hu0) (by linear_combination k11)
  have q2 : W.a₂ - W.a₁ * s - W.a₂ * u ^ 2 + 3 * β - s ^ 2 = 0 :=
    eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero 4 hu0) (by linear_combination -k2)
  have q01 : W.a₁ * β - W.a₃ * u ^ 3 + W.a₃ + 2 * ε = 0 :=
    eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero 3 hu0) (by linear_combination k01)
  have q1 : -W.a₁ * β * s - W.a₁ * ε + 2 * W.a₂ * β - W.a₃ * s - W.a₄ * u ^ 4 + W.a₄ + 3 * β ^ 2
      - 2 * s * ε = 0 :=
    eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero 2 hu0) (by linear_combination -k1')
  let vc : WeierstrassCurve.VariableChange K := ⟨Units.mk0 u hu0, β, s, ε⟩
  have hvc : vc • W = W := by
    ext
    · rw [WeierstrassCurve.variableChange_a₁]
      simp only [vc, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [inv_mul_eq_iff_eq_mul₀ hu0]; linear_combination q11
    · rw [WeierstrassCurve.variableChange_a₂]
      simp only [vc, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow]
      rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hu0)]; linear_combination q2
    · rw [WeierstrassCurve.variableChange_a₃]
      simp only [vc, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow]
      rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 3 hu0)]; linear_combination q01
    · rw [WeierstrassCurve.variableChange_a₄]
      simp only [vc, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow]
      rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 4 hu0)]; linear_combination q1
    · rw [WeierstrassCurve.variableChange_a₆]
      simp only [vc, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow]
      rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 6 hu0)]; linear_combination -k0
  have h4 := WeierstrassCurve.variableChange_c₄ W vc
  have h6 := WeierstrassCurve.variableChange_c₆ W vc
  rw [hvc] at h4 h6
  simp only [vc, Units.val_inv_eq_inv_val, Units.val_mk0] at h4 h6
  have hχu : u⁻¹ = χ := (eq_inv_of_mul_eq_one_left hχ).symm
  rw [hχu] at h4 h6
  have hrel := WeierstrassCurve.c_relation W
  have hΔ0 : W.Δ ≠ 0 := (WeierstrassCurve.IsElliptic.isUnit (W := W)).ne_zero
  by_cases hc4 : W.c₄ = 0
  · right
    have hc6 : W.c₆ ≠ 0 := by
      intro hc6; rw [hc4, hc6] at hrel; norm_num at hrel; exact hΔ0 hrel
    exact sub_eq_zero.mp (eq_zero_of_ne_zero_of_mul_left_eq_zero hc6 (by linear_combination -h6))
  · exact .inl <| sub_eq_zero.mp
      (eq_zero_of_ne_zero_of_mul_left_eq_zero hc4 (by linear_combination -h4))

end EllAlg

namespace EllGeo

variable {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
  (e : Scheme.Hom.relativeDifferentials f ≅ SheafOfModules.unit C.ringCatSheaf)

/-- The vector field dual to the trivialising differential. -/
private noncomputable def vf := (Scheme.Hom.universalRelativeDerivation f).postcomp e.hom.val

/-- The derivation on sections. -/
private noncomputable def Dv (U : C.Opens) (a : Γ(C, U)) : Γ(C, U) := (vf f e).d (X := op U) a

private theorem Dv_mul (U : C.Opens) (a b : Γ(C, U)) : Dv f e U (a * b) = a * Dv f e U b + b *
    Dv f e U a :=
  (vf f e).d_mul (X := op U) a b

private theorem Dv_add (U : C.Opens) (a b : Γ(C, U)) : Dv f e U (a + b) = Dv f e U a + Dv f e U b :=
  map_add _ a b

private theorem Dv_res {U V : C.Opens} (h : V ≤ U) (a : Γ(C, U)) :
    Dv f e V (C.presheaf.map (homOfLE h).op a) = C.presheaf.map (homOfLE h).op (Dv f e U a) :=
  (vf f e).d_map (homOfLE h).op a

/-- The constants, as global sections. -/
private noncomputable def kTop (c : K) : Γ(C, ⊤) := f.appTop ((Scheme.ΓSpecIso (.of K)).inv c)

/-- The constants. -/
private noncomputable def kap (U : C.Opens) (c : K) : Γ(C, U) :=
  C.presheaf.map (homOfLE le_top).op (kTop f c)

private theorem kap_top (c : K) : kap f ⊤ c = kTop f c := by
  simp only [kap, homOfLE_refl, op_id, CategoryTheory.Functor.map_id]; rfl

private theorem kap_res {U V : C.Opens} (h : V ≤ U) (c : K) :
    C.presheaf.map (homOfLE h).op (kap f U c) = kap f V c := by
  simp only [kap]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem kap_one (U : C.Opens) : kap f U 1 = 1 := by
  simp [kap, kTop]

private theorem Dv_app_top (r : Γ(Spec (.of K), ⊤)) : Dv f e (f ⁻¹ᵁ ⊤) ((f.app ⊤).hom r) = 0 := by
  have := Scheme.Hom.universalRelativeDerivation_d_app_eq_zero f ⊤ r
  unfold Dv vf
  erw [PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply, this, map_zero]
  rfl

private theorem Dv_kap (U : C.Opens) (c : K) : Dv f e U (kap f U c) = 0 := by
  unfold kap kTop
  erw [Dv_res f e (U := f ⁻¹ᵁ ⊤) (by simp), Dv_app_top, map_zero]

private theorem appLE_eq_res (k : C ⟶ C) {U V : C.Opens}
    (h : V ≤ k ⁻¹ᵁ U) (b : Γ(C, U)) :
    C.presheaf.map (homOfLE h).op ((k.app U).hom b) = (k.appLE U V h).hom b := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem Dv_appLE (k : C ⟶ C) {U V : C.Opens} (h : V ≤ k ⁻¹ᵁ U) (b : Γ(C, U)) :
    Dv f e V ((k.appLE U V h).hom b) =
      C.presheaf.map (homOfLE h).op (Dv f e (k ⁻¹ᵁ U) ((k.app U).hom b)) := by
  rw [Scheme.Hom.app_eq_appLE, ← Dv_res, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- Restriction of differentials. -/
private noncomputable def resO {U V : C.Opens} (h : V ≤ U) (m : (Scheme.Hom.relativeDifferentials
    f).val.obj (op U)) :
    (Scheme.Hom.relativeDifferentials f).val.obj (op V) :=
  ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE h).op).hom m

/-- The trivialising differential. -/
private noncomputable def om0 : (Scheme.Hom.relativeDifferentials f).val.obj (op ⊤) :=
  e.inv.val.app (op ⊤) (1 : C.ringCatSheaf.obj.obj (op ⊤))

private theorem e_inv_e (U : C.Opens) (m : (Scheme.Hom.relativeDifferentials f).val.obj (op U)) :
    e.inv.val.app (op U) (e.hom.val.app (op U) m) = m :=
  ((PresheafOfModules.evaluation _ (op U)).mapIso
    ((SheafOfModules.forget _).mapIso e)).hom_inv_id_apply m

private theorem e_e_inv (U : C.Opens) (m : (SheafOfModules.unit C.ringCatSheaf).val.obj (op U)) :
    e.hom.val.app (op U) (e.inv.val.app (op U) m) = m :=
  ((PresheafOfModules.evaluation _ (op U)).mapIso
    ((SheafOfModules.forget _).mapIso e)).inv_hom_id_apply m

/-- The coefficient of a differential with respect to the trivialisation. -/
private noncomputable def co (U : C.Opens) (m : (Scheme.Hom.relativeDifferentials f).val.obj (op
    U)) :
    Γ(C, U) :=
  e.hom.val.app (op U) m

/-- Scalar multiplication of differentials by sections. -/
private noncomputable def smulO {U : C.Opens} (b : Γ(C, U))
    (m : (Scheme.Hom.relativeDifferentials f).val.obj (op U)) :
    (Scheme.Hom.relativeDifferentials f).val.obj (op U) :=
  (@id (C.ringCatSheaf.obj.obj (op U)) b) • m

private theorem co_add (U : C.Opens) (m m' : (Scheme.Hom.relativeDifferentials f).val.obj (op U)) :
    co f e U (m + m') = co f e U m + co f e U m' := map_add _ _ _

private theorem co_zero (U : C.Opens) : co f e U 0 = 0 := map_zero _

private theorem co_injective (U : C.Opens) : Function.Injective (co f e U) := by
  intro m m' h
  rw [← e_inv_e f e U m, ← e_inv_e f e U m']
  exact congrArg (e.inv.val.app (op U)).hom h

private theorem co_om0 : co f e ⊤ (om0 f e) = 1 := e_e_inv f e ⊤ _

private theorem co_res {U V : C.Opens} (h : V ≤ U) (m : (Scheme.Hom.relativeDifferentials
    f).val.obj (op U)) :
    co f e V (resO f h m) = C.presheaf.map (homOfLE h).op (co f e U m) :=
  PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op m

private theorem co_smulO (U : C.Opens) (b : Γ(C,
    U)) (m : (Scheme.Hom.relativeDifferentials f).val.obj (op U)) :
    co f e U (smulO f b m) = b * co f e U m :=
  (e.hom.val.app (op U)).hom.map_smul b m

private theorem co_d (U : C.Opens) (a : Γ(C, U)) :
    co f e U ((Scheme.Hom.universalRelativeDerivation f).d (X := op U) a) = Dv f e U a := by
  unfold co Dv vf
  erw [PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply]

private theorem d_eq_smulO (U : C.Opens) (a : Γ(C, U)) :
    (Scheme.Hom.universalRelativeDerivation f).d (X := op U) a =
      smulO f (Dv f e U a) (resO f le_top (om0 f e)) := by
  apply co_injective f e U
  rw [co_d, co_smulO, co_res, co_om0, map_one, mul_one]

private theorem span_Dv_eq_top (U : C.Opens) (hU : IsAffineOpen U) :
    Ideal.span (Set.range (Dv f e U)) = ⊤ := by
  have hle : U ≤ f ⁻¹ᵁ ⊤ := by simp
  let κ := Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections f ⊤ U hle
  have : IsIso κ := Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections f hU
    hle (isAffineOpen_top _)
  obtain ⟨η, hη⟩ := (ConcreteCategory.bijective_of_isIso κ).2 (resO f le_top (om0 f e))
  have key : ∀ η, co f e U (κ.hom η) ∈ Ideal.span (Set.range (Dv f e U)) := by
    intro η
    letI : Algebra Γ(Spec (.of K), ⊤) Γ(C, U) := (f.appLE ⊤ U hle).hom.toAlgebra
    have hη' : η ∈ Submodule.span Γ(C, U)
        (Set.range (KaehlerDifferential.D Γ(Spec (.of K), ⊤) Γ(C, U))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hη' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have := Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d f ⊤ U hle a
      erw [this, co_d]
      exact Ideal.subset_span ⟨a, rfl⟩
    | zero => rw [map_zero, co_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, co_add]; exact add_mem hx hy
    | smul b x _ hx =>
      letI : Module Γ(C, U) ((Scheme.Hom.relativeDifferentials f).val.obj (op U)) :=
        ((Scheme.Hom.relativeDifferentials f).val.obj (op U)).isModule
      have hs : κ.hom (b • x) = smulO f b (κ.hom x) := κ.hom.map_smul b x
      erw [hs, co_smulO f e U b (κ.hom x)]
      exact Ideal.mul_mem_left _ _ hx
  have h1 := key η
  rw [hη, co_res, co_om0, map_one] at h1
  exact (Ideal.eq_top_iff_one _).2 h1

section Equivariance

variable (σ : C ≅ C) (hσ : σ.hom ≫ f = f)

/-- Pull-back of differentials along `σ`, as a map to the push-forward. -/
private noncomputable def th : Scheme.Hom.relativeDifferentials f ⟶
    (Scheme.Modules.pushforward σ.hom).obj (Scheme.Hom.relativeDifferentials f) :=
  (Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _
    (Scheme.Hom.relativeDifferentialsMap σ.hom f f (𝟙 _) (hσ.trans (Category.comp_id f).symm))

/-- The action on global differentials, as in the statement. -/
private noncomputable def Tm := moduleSpecΓFunctor.map
  ((Scheme.Modules.pushforward f).map (th f σ hσ) ≫
    (Scheme.Modules.pushforwardComp σ.hom f).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr hσ).hom.app _)

private theorem th_d (U : C.Opens) (a : Γ(C, U)) :
    (th f σ hσ).val.app (op U) ((Scheme.Hom.universalRelativeDerivation f).d (X := op U) a) =
      (Scheme.Hom.universalRelativeDerivation f).d (X := op (σ.hom ⁻¹ᵁ U)) ((σ.hom.app U).hom a) :=
  Scheme.Hom.relativeDifferentialsMap_app_d (𝟙 _) _ U a

private theorem th_smulO (U : C.Opens) (b : Γ(C, U))
    (m : (Scheme.Hom.relativeDifferentials f).val.obj (op U)) :
    (th f σ hσ).val.app (op U) (smulO f b m) =
      smulO f ((σ.hom.app U).hom b)
        (@id ((Scheme.Hom.relativeDifferentials f).val.obj (op (σ.hom ⁻¹ᵁ U)))
          ((th f σ hσ).val.app (op U) m)) :=
  ((th f σ hσ).val.app (op U)).hom.map_smul b m

private theorem th_res {U V : C.Opens} (h : V ≤ U) (m : (Scheme.Hom.relativeDifferentials
    f).val.obj (op U)) :
    (th f σ hσ).val.app (op V) (resO f h m) =
      resO f (Scheme.Hom.preimage_mono σ.hom h) ((th f σ hσ).val.app (op U) m) :=
  PresheafOfModules.naturality_apply (th f σ hσ).val (homOfLE h).op m

/-- The action on global sections of a morphism `M ⟶ σ_* M`, pushed to `Spec K`, is the morphism
on sections over `C`. -/
private theorem moduleSpecΓFunctor_map_apply (M : C.Modules)
    (θ : M ⟶ (Scheme.Modules.pushforward σ.hom).obj M)
    (ω : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj M)) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward f).map θ ≫
      (Scheme.Modules.pushforwardComp σ.hom f).hom.app _ ≫
        (Scheme.Modules.pushforwardCongr hσ).hom.app _)).hom ω = (θ.val.app (op ⊤)).hom ω := by
  show (((Scheme.Modules.pushforwardCongr hσ).hom.app _).app ⊤).hom
    ((((Scheme.Modules.pushforwardComp σ.hom f).hom.app _).app ⊤).hom
      ((((Scheme.Modules.pushforward f).map θ).app ⊤).hom ω)) = _
  rw [Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_hom_app_app]
  erw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem Tm_apply (ω) : (Tm f σ hσ).hom ω = (th f σ hσ).val.app (op ⊤) ω :=
  moduleSpecΓFunctor_map_apply f σ hσ _ _ ω

private theorem th_top_res {U : C.Opens} (m : (Scheme.Hom.relativeDifferentials f).val.obj (op ⊤)) :
    (th f σ hσ).val.app (op U) (resO f le_top m) =
      @id (((Scheme.Modules.pushforward σ.hom).obj (Scheme.Hom.relativeDifferentials f)).val.obj
          (op U))
        (resO f (le_top : σ.hom ⁻¹ᵁ U ≤ ⊤) (@id ((Scheme.Hom.relativeDifferentials f).val.obj (op
            ⊤))
          ((th f σ hσ).val.app (op ⊤) m))) :=
  th_res f σ hσ le_top m

private theorem smul_top (χ : K)
    (ω : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj
        (Scheme.Hom.relativeDifferentials f))) :
    (@id ((Scheme.Hom.relativeDifferentials f).val.obj (op ⊤)) (χ • ω)) = smulO f (kTop f χ) ω :=
  rfl

/-- On a one-dimensional space of global differentials, `σ` acts by a scalar. -/
private theorem exists_Tm_eq_smul
    (hfr : Module.finrank K (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward f).obj (Scheme.Hom.relativeDifferentials f))) = 1) :
    ∃ χ : K, ∀ ω, (Tm f σ hσ).hom ω = χ • ω := by
  obtain ⟨χ, hχ, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hfr (Tm f σ hσ).hom
  exact ⟨χ, fun ω => by rw [hχ]; rfl⟩

private theorem equivariance (χ : K) (hχ : ∀ ω, (Tm f σ hσ).hom ω = χ • ω) (U : C.Opens) (a : Γ(C,
    U)) :
    Dv f e (σ.hom ⁻¹ᵁ U) ((σ.hom.app U).hom a) =
      kap f _ χ * (σ.hom.app U).hom (Dv f e U a) := by
  have h1 := th_d f σ hσ U a
  rw [d_eq_smulO f e U a, d_eq_smulO f e _ ((σ.hom.app U).hom a), th_smulO, th_top_res] at h1
  have h2 : (@id ((Scheme.Hom.relativeDifferentials f).val.obj (op ⊤))
      ((th f σ hσ).val.app (op ⊤) (om0 f e))) = smulO f (kTop f χ) (om0 f e) :=
    (Tm_apply f σ hσ (om0 f e)).symm.trans ((hχ _).trans (smul_top f χ _))
  rw [h2] at h1
  have h3 := congrArg (co f e (σ.hom ⁻¹ᵁ U)) h1
  rw [co_smulO, co_smulO] at h3
  erw [co_res, co_res] at h3
  rw [co_smulO, co_om0, map_mul, map_one, mul_one, mul_one, ← kap_top, kap_res] at h3
  rw [← h3, mul_comm]

end Equivariance

end EllGeo

namespace EllW

open Stacks.GradedSections (powSections sectionRing)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors (modulesInvertibleSheaf)
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
open AlgebraicGeometry.GenusOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

private theorem exists_weierstrassCurve_iso [IsProper f] [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (hg : genus f = 1)
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ∃ (C : WeierstrassCurve k) (_ : C.IsElliptic) (e : X ≅ projOf C),
      e.hom ≫ projectionOf C = f ∧ p ≫ e.hom = zeroOf C := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  have := isIntegral f h0
  have := isCurve f h0
  have := isDiscreteValuationRing_stalk f h0 p hp
  have hx := isClosed_point f p hp
  have := isEffectiveCartierDivisor_pow f h0 p hp 3
  set L := modulesInvertibleSheaf
    (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, hx⟩ : Closeds X) ^ 3) with hLdef
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hdeg : invertibleCurveDegree k f hdim L = (3 : ℕ) :=
    invertibleCurveDegree_vanishingIdeal_point_pow f h0 hdim p hp 3
  -- the abstract data
  have hfin : ∀ m, FiniteDimensional k (gradingK L k m) := fun m =>
    have : FiniteDimensional k (cohomologyOverField k (X ↘ Spec (.of k)) (natTensorPow L m) 0) :=
      finiteDimensional_cohomologyOverField_natTensorPow f L m 0
    finiteDimensional_gradingK L k m
  have : Nontrivial (sectionRing L) := by
    have := nontrivial_globalSections f h0
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have h1 : (1 : Stacks.AmpleFiniteAvoidance.grading L 0) = 0 := Subtype.ext h
    have h2 := congrArg (Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom L) h1
    rw [map_one, map_zero] at h2
    exact one_ne_zero h2
  have hle : ∀ m, 1 ≤ m → 3 * m ≤ Module.finrank k (gradingK L k m) := fun m _ => by
    rw [finrank_gradingK]
    exact mul_le_finrank_cohomologyOverField_zero_natTensorPow f h0 hg hdim L hdeg m
  have hev : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → Module.finrank k (gradingK L k m) ≤ 3 * m := by
    obtain ⟨m₀, hm₀⟩ := exists_forall_finrank_cohomologyOverField_zero_natTensorPow_le f h0 hg
      hdim L hdeg (by norm_num)
    exact ⟨m₀, fun m hm => by rw [finrank_gradingK]; exact hm₀ m hm⟩
  let D := sectionRingData L (point p) k (exists_sub_Γgerm_mem_maximalIdeal f p hp)
    (bijective_globalSectionsHom f h0).2 (pointSection hx 3)
    (mem_nonvanishingOpen_pointSection hx 3 (by norm_num)) (sectionOrd_pointSection hx 3)
    hfin hle hev
  -- the Weierstrass presentation
  obtain ⟨X', hX', -, hX'o⟩ := (Stacks.GenusOneSectionRing.exists_ord_eq_iff D (by norm_num)
    le_rfl 1).mpr ⟨by norm_num, by norm_num⟩
  obtain ⟨Y', hY', -, hY'o⟩ := (Stacks.GenusOneSectionRing.exists_ord_eq_iff D (by norm_num)
    le_rfl 0).mpr ⟨by norm_num, by norm_num⟩
  obtain ⟨C, l, n, -, -, hsurj, hker⟩ :=
    Stacks.GenusOneSectionRing.exists_weierstrassCurve D hX' hX'o hY' hY'o
  set φ := (MvPolynomial.aeval ![l • X', n • Y', D.Z] :
    MvPolynomial (Fin 3) k →ₐ[k] sectionRing L) with hφ
  have hv : ∀ i, φ (MvPolynomial.X i) ∈ Stacks.AmpleFiniteAvoidance.grading L 1 := by
    intro i
    rw [hφ, MvPolynomial.aeval_X]
    fin_cases i
    · exact (gradingK L k 1).smul_mem l hX'
    · exact (gradingK L k 1).smul_mem n hY'
    · exact D.Z_mem
  -- the isomorphism
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L
      ((isAmple_iff_invertibleCurveDegree_pos k f hdim L).mpr (by rw [hdeg]; norm_num))
  have hUC : UniversallyClosed X.toSpecΓ :=
    Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ f
  have := isIso_weierstrassModelHom L k hL C φ hker hv hsurj hUC
  set e := asIso (weierstrassModelHom L k hL C φ hker hv hsurj) with he
  have hover : e.hom ≫ projectionOf C = f := weierstrassModelHom_projectionOf L k hL C φ hker hv
    hsurj
  refine ⟨C, ?_, e, hover, ?_⟩
  · -- the discriminant is a unit
    have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    have hproj : projectionOf C = e.inv ≫ f := by rw [← hover, Iso.inv_hom_id_assoc]
    have : Smooth (projectionOf C) := by rw [hproj]; infer_instance
    exact isElliptic_of_smooth C
  · -- the point goes to infinity
    refine eq_zeroOf_of_notMem_basicOpenOf C _ (by rw [Category.assoc, hover, hp]) ?_
    intro hmem
    have hpre : point p ∈ e.hom ⁻¹ᵁ basicOpenOf C (coordOf C 2) := hmem
    change point p ∈ Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL ⁻¹ᵁ
      (Proj.map _ (Proj.irrelevant_le_map_of_surjective _
        (bijective_weierstrassRingHom C φ hker hsurj).2) ⁻¹ᵁ
          Proj.basicOpen (gradingOf C) (coordOf C 2)) at hpre
    rw [Proj.map_preimage_basicOpen] at hpre
    have hz : (weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C φ hker
        (algebraMap_mem_grading_zero L k) hv) (coordOf C 2) =
        DirectSum.of (powSections L) 1 (pointSection hx 3) := by
      change φ (MvPolynomial.X 2) = _
      rw [hφ, MvPolynomial.aeval_X]
      rfl
    rw [hz, Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL _
      one_pos] at hpre
    exact notMem_nonvanishingOpen_pointSection hx 3 (by norm_num) hpre

end EllW

namespace EllPF

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass EllGeo

variable {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
  (e : Scheme.Hom.relativeDifferentials f ≅ SheafOfModules.unit C.ringCatSheaf)

/-- A derivation transported along a ring isomorphism compatible with the constants. -/
private noncomputable def transDer {R A : Type*} [CommRing R] [CommRing A] [Algebra K A] (ι : R ≃+*
    A)
    (κ : K → R) (hι : ∀ c, ι (κ c) = algebraMap K A c) (δ : R → R)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = a * δ b + b * δ a)
    (hκ : ∀ c, δ (κ c) = 0) : Derivation K A A :=
  Derivation.mk'
    { toFun := fun a => ι (δ (ι.symm a))
      map_add' := fun a b => by simp [hadd]
      map_smul' := fun c a => by
        have h1 : ι.symm (c • a) = κ c * ι.symm a := by
          rw [Algebra.smul_def, map_mul, ← hι, RingEquiv.symm_apply_apply]
        show ι (δ (ι.symm (c • a))) = (RingHom.id K) c • ι (δ (ι.symm a))
        rw [h1, hmul, hκ, mul_zero, add_zero, map_mul, hι, RingHom.id_apply, Algebra.smul_def] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, hmul, map_add,
        RingEquiv.apply_symm_apply, smul_eq_mul])

private theorem transDer_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra K A] (ι : R ≃+* A)
    (κ : K → R) (hι) (δ : R → R) (hadd hmul hκ) (a : A) :
    transDer (K := K) ι κ hι δ hadd hmul hκ a = ι (δ (ι.symm a)) := rfl

private theorem span_transDer {R A : Type*} [CommRing R] [CommRing A] [Algebra K A]
    (ι : R ≃+* A) (κ : K → R) (hι) (δ : R → R) (hadd hmul hκ)
    (hδ : Ideal.span (Set.range δ) = ⊤) :
    Ideal.span (Set.range (transDer (K := K) ι κ hι δ hadd hmul hκ)) = ⊤ := by
  have hr : Set.range (transDer (K := K) ι κ hι δ hadd hmul hκ) =
      (ι : R →+* A) '' Set.range δ := by
    ext a
    simp only [transDer_apply, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨b, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩; exact ⟨ι b, by simp⟩
  rw [hr, ← Ideal.map_span, hδ, Ideal.map_top]

private theorem appIso_kap {A : CommRingCat.{u}} (j : Spec A ⟶ C) [IsOpenImmersion j]
    (φ : CommRingCat.of K ⟶ A) (hj : j ≫ f = Spec.map φ) (c : K) :
    ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso A).hom (kap f (j ''ᵁ ⊤) c) = φ c := by
  have hjt : j.appLE ⊤ ⊤ (by simp) = j.appTop :=
    Scheme.Hom.appLE_eq_app j
  have key : (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.presheaf.map (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op ≫ (j.appIso ⊤).hom ≫
        (Scheme.ΓSpecIso A).hom = φ := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE_assoc, hjt, ← Category.assoc f.appTop,
      ← Scheme.Hom.comp_appTop, hj, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun g => g.hom c) key

private theorem appLE_eq_of_eq {X Y : Scheme.{u}} {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂) {V : Y.Opens}
    {U : X.Opens} (e₁ : U ≤ k₁ ⁻¹ᵁ V) (e₂ : U ≤ k₂ ⁻¹ᵁ V) : k₁.appLE V U e₁ = k₂.appLE V U e₂ := by
  subst hk; rfl

private theorem appLE_kap (g : C ⟶ C) (hg : g ≫ f = f) {V U : C.Opens} (h : U ≤ g ⁻¹ᵁ V) (c : K) :
    (g.appLE V U h).hom (kap f V c) = kap f U c := by
  simp only [kap, kTop]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply]
  have key : f.appTop ≫ g.appLE ⊤ U (h.trans (by simp)) =
      f.app ⊤ ≫ C.presheaf.map (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op := by
    erw [← Scheme.Hom.comp_appLE g f ⊤ U, appLE_eq_of_eq hg _ (by simp)]
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  erw [key]
  rfl

private theorem chi_pow_of_fixed_point [CharZero K] (W : WeierstrassCurve K) [W.IsElliptic] (eW : C
    ≅ projOf W)
    (hover : eW.hom ≫ projectionOf W = f) (p : Spec (.of K) ⟶ C) (hzero : p ≫ eW.hom = zeroOf W)
    (α : C ≅ C) (hα : α.hom ≫ f = f) (hfix : p ≫ α.hom = p) (c : K)
    (hc : ∀ (U : C.Opens) (a : Γ(C, U)), Dv f e (α.hom ⁻¹ᵁ U) ((α.hom.app U).hom a) =
      kap f _ c * (α.hom.app U).hom (Dv f e U a)) : c ^ 4 = 1 ∨ c ^ 6 = 1 := by
  let A := W.toAffine.CoordinateRing
  let j : Spec (.of A) ⟶ C := chartZ W ≫ eW.inv
  let U : C.Opens := j ''ᵁ ⊤
  have hmemU : ∀ x, x ∈ U ↔ eW.hom x ∈ basicOpenOf W (coordOf W 2) := by
    intro x
    rw [← opensRange_chartZ W]
    simp only [U, Scheme.Hom.image_top_eq_opensRange]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Scheme.Hom.comp_apply, Scheme.inv_hom_apply]⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]; simp⟩
  have hz : zeroOf W ≫ (eW.inv ≫ α.hom ≫ eW.hom) = zeroOf W := by
    rw [← hzero, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hfix]
  have hpre := preimage_basicOpenOf_two (eW.inv ≫ α.hom ≫ eW.hom) hz
  have hUα : α.hom ⁻¹ᵁ U = U := by
    ext x
    show α.hom x ∈ U ↔ x ∈ U
    rw [hmemU, hmemU]
    have h1 : eW.hom (α.hom x) = (eW.inv ≫ α.hom ≫ eW.hom) (eW.hom x) := by
      simp [Scheme.Hom.comp_apply]
    rw [h1]
    exact SetLike.ext_iff.mp hpre (eW.hom x)
  have hUα' : α.inv ⁻¹ᵁ U = U := by
    ext x
    show α.inv x ∈ U ↔ x ∈ U
    have h2 := SetLike.ext_iff.mp hUα (α.inv x)
    rw [← h2]
    show α.hom (α.inv x) ∈ U ↔ x ∈ U
    rw [Scheme.inv_hom_apply]
  have hUaff : IsAffineOpen U := (isAffineOpen_top (Spec (.of A))).image_of_isOpenImmersion j
  let ι : Γ(C, U) ≃+* A := ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  have hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    have h1 : eW.inv ≫ f = projectionOf W := by rw [← hover, Iso.inv_hom_id_assoc]
    simp only [j, Category.assoc, h1]
    exact chartZ_projectionOf W
  have hι : ∀ c, ι (kap f U c) = algebraMap K A c := fun c => appIso_kap f j _ hj c
  let a0 := α.hom.appLE U U hUα.ge
  let a1 := α.inv.appLE U U hUα'.ge
  have hid : ∀ e', (𝟙 C : C ⟶ C).appLE U U e' = 𝟙 _ := fun e' =>
    (Scheme.Hom.appLE_eq_app _).trans (Scheme.Hom.id_app U)
  have h01 : ∀ b, a1.hom (a0.hom b) = b := by
    intro b
    have : a0 ≫ a1 = 𝟙 _ := by
      simp only [a0, a1]
      rw [Scheme.Hom.appLE_comp_appLE,
        appLE_eq_of_eq (V := U) (U := U) α.inv_hom_id _ le_rfl]
      exact hid _
    exact congrArg (fun g => g.hom b) this
  have h10 : ∀ b, a0.hom (a1.hom b) = b := by
    intro b
    have : a1 ≫ a0 = 𝟙 _ := by
      simp only [a0, a1]
      rw [Scheme.Hom.appLE_comp_appLE,
        appLE_eq_of_eq (V := U) (U := U) α.hom_inv_id _ le_rfl]
      exact hid _
    exact congrArg (fun g => g.hom b) this
  let ψ0 : Γ(C, U) ≃+* Γ(C, U) :=
    RingEquiv.ofRingHom a0.hom a1.hom (RingHom.ext h10) (RingHom.ext h01)
  have hψ0 : ∀ b, ψ0 b = a0.hom b := fun _ => rfl
  have hka : ∀ c, a0.hom (kap f U c) = kap f U c := fun c => appLE_kap f α.hom hα hUα.ge c
  let ψ : A ≃ₐ[K] A := AlgEquiv.ofRingEquiv (f := (ι.symm.trans ψ0).trans ι) (fun c => by
    simp only [RingEquiv.trans_apply]
    rw [← hι, RingEquiv.symm_apply_apply, hψ0, hka])
  let D := transDer ι (kap f U) hι (Dv f e U) (Dv_add f e U) (Dv_mul f e U) (Dv_kap f e U)
  have hD : Ideal.span (Set.range D) = ⊤ :=
      span_transDer ι _ hι _ _ _ _ (span_Dv_eq_top f e U hUaff)
  have hψ : ∀ a, D (ψ a) = c • ψ (D a) := by
    intro a
    simp only [D, ψ, transDer_apply, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
      RingEquiv.symm_apply_apply, hψ0]
    rw [← appLE_eq_res, ← appLE_eq_res, Dv_res, hc, map_mul, kap_res, map_mul, hι,
      Algebra.smul_def]
  exact EllAlg.chi_pow W D hD ψ c hψ

end EllPF

namespace EllTr

variable {B : Type*} [CommRing B]

/-- The `x`-coordinate of the translate. -/
private def trX (a1 a2 x0 y0 X Y G : B) : B := ((Y - y0) * G) ^ 2 + a1 * ((Y - y0) * G) - a2 - X -
    x0

/-- The `y`-coordinate of the translate. -/
private def trY (a1 a2 a3 x0 y0 X Y G : B) : B :=
  -(((Y - y0) * G) * (trX a1 a2 x0 y0 X Y G - X) + Y) - a1 * trX a1 a2 x0 y0 X Y G - a3

private theorem tr_eq (a1 a2 a3 a4 a6 x0 y0 X Y G : B)
    (h1 : Y ^ 2 + a1 * X * Y + a3 * Y - (X ^ 3 + a2 * X ^ 2 + a4 * X + a6) = 0)
    (h2 : y0 ^ 2 + a1 * x0 * y0 + a3 * y0 - (x0 ^ 3 + a2 * x0 ^ 2 + a4 * x0 + a6) = 0)
    (h3 : (X - x0) * G - 1 = 0) :
    trY a1 a2 a3 x0 y0 X Y G ^ 2 + a1 * trX a1 a2 x0 y0 X Y G * trY a1 a2 a3 x0 y0 X Y G +
      a3 * trY a1 a2 a3 x0 y0 X Y G - (trX a1 a2 x0 y0 X Y G ^ 3 +
        a2 * trX a1 a2 x0 y0 X Y G ^ 2 + a4 * trX a1 a2 x0 y0 X Y G + a6) = 0 := by
  unfold trY trX
  linear_combination (-G^4*X^4 - G^4*X^3*a2 + G^4*X^3*x0 + G^4*X^2*Y*a1 - G^4*X^2*a1*y0 +
      3*G^4*X^2*a2*x0 + 3*G^4*X^2*x0^2 + G^4*X*Y^2 - 2*G^4*X*Y*a1*x0 - 2*G^4*X*Y*y0 +
      G^4*X*a1*x0*y0 - 2*G^4*X*a2*x0^2 - G^4*X*a3*y0 + G^4*X*a4*x0 + G^4*X*a6 - 4*G^4*X*x0^3 -
      G^4*Y^2*x0 + G^4*Y*a1*x0^2 + 2*G^4*Y*x0*y0 + G^4*a3*x0*y0 - G^4*a4*x0^2 - G^4*a6*x0 +
      G^4*x0^4) * h1 + (G^4*X^4 - 4*G^4*X^3*x0 + G^4*X^2*a1*y0 - 2*G^4*X^2*a2*x0 - G^4*X^2*a4 +
      3*G^4*X^2*x0^2 + G^4*X*Y*a1*x0 + G^4*X*Y*a3 + 2*G^4*X*Y*y0 - 2*G^4*X*a1*x0*y0 +
      3*G^4*X*a2*x0^2 + G^4*X*a4*x0 - G^4*X*a6 + G^4*X*x0^3 - G^4*X*y0^2 - G^4*Y*a1*x0^2 -
      G^4*Y*a3*x0 - 2*G^4*Y*x0*y0 + G^4*a1*x0^2*y0 - G^4*a2*x0^3 + G^4*a6*x0 - G^4*x0^4 +
      G^4*x0*y0^2) * h2 + (-G^3*X^6 - 2*G^3*X^5*a2 + 2*G^3*X^4*Y*a1 - G^3*X^4*a1*y0 -
      G^3*X^4*a2^2 + 2*G^3*X^4*a2*x0 - G^3*X^4*a4 + 3*G^3*X^4*x0^2 + 2*G^3*X^3*Y^2 +
      2*G^3*X^3*Y*a1*a2 - G^3*X^3*Y*a1*x0 + G^3*X^3*Y*a3 - 2*G^3*X^3*Y*y0 - G^3*X^3*a1*a2*y0 -
      G^3*X^3*a1*x0*y0 + 2*G^3*X^3*a2^2*x0 - G^3*X^3*a2*a4 + 4*G^3*X^3*a2*x0^2 - 2*G^3*X^3*a3*y0 +
      2*G^3*X^3*a4*x0 + G^3*X^3*a6 - G^3*X^3*y0^2 - G^3*X^2*Y^2*a1^2 + 2*G^3*X^2*Y^2*a2 +
      G^3*X^2*Y*a1^2*y0 - 3*G^3*X^2*Y*a1*a2*x0 + G^3*X^2*Y*a1*a4 - 3*G^3*X^2*Y*a1*x0^2 +
      G^3*X^2*Y*a2*a3 - 2*G^3*X^2*Y*a2*y0 - G^3*X^2*a1*a4*y0 + 3*G^3*X^2*a1*x0^2*y0 -
      G^3*X^2*a2*a3*y0 + 3*G^3*X^2*a2*a4*x0 - 4*G^3*X^2*a2*x0^3 + 3*G^3*X^2*a3*x0*y0 -
      3*G^3*X^2*a6*x0 - 3*G^3*X^2*x0^4 + 3*G^3*X^2*x0*y0^2 - 2*G^3*X*Y^3*a1 + G^3*X*Y^2*a1^2*x0 -
      G^3*X*Y^2*a1*a3 + 3*G^3*X*Y^2*a1*y0 - 2*G^3*X*Y^2*a2*x0 + G^3*X*Y^2*a4 - 3*G^3*X*Y^2*x0^2 +
      2*G^3*X*Y*a1*a3*y0 - 2*G^3*X*Y*a1*a4*x0 + G^3*X*Y*a1*x0^3 - 2*G^3*X*Y*a2*a3*x0 -
      3*G^3*X*Y*a3*x0^2 - 2*G^3*X*Y*a4*y0 - G^3*X*a1^2*x0*y0^2 + 3*G^3*X*a1*a2*x0^2*y0 -
      G^3*X*a1*a3*y0^2 + 2*G^3*X*a1*a4*x0*y0 + G^3*X*a1*x0^3*y0 - G^3*X*a1*y0^3 -
      2*G^3*X*a2^2*x0^3 + 2*G^3*X*a2*a3*x0*y0 - 3*G^3*X*a2*a4*x0^2 - 2*G^3*X*a2*x0^4 +
      2*G^3*X*a2*x0*y0^2 - 2*G^3*X*a4*x0^3 + G^3*X*a4*y0^2 + 3*G^3*X*a6*x0^2 - 2*G^3*Y^4 +
      G^3*Y^3*a1*x0 - G^3*Y^3*a3 + 6*G^3*Y^3*y0 + G^3*Y^2*a1*a3*x0 + 3*G^3*Y^2*a3*y0 -
      G^3*Y^2*a4*x0 + G^3*Y^2*x0^3 - 6*G^3*Y^2*y0^2 - G^3*Y*a1^2*x0^2*y0 + G^3*Y*a1*a2*x0^3 -
      2*G^3*Y*a1*a3*x0*y0 + G^3*Y*a1*a4*x0^2 + G^3*Y*a1*x0^4 - 3*G^3*Y*a1*x0*y0^2 +
      G^3*Y*a2*a3*x0^2 + 2*G^3*Y*a2*x0^2*y0 + 2*G^3*Y*a3*x0^3 - 3*G^3*Y*a3*y0^2 +
      2*G^3*Y*a4*x0*y0 + 2*G^3*Y*x0^3*y0 + 2*G^3*Y*y0^3 + G^3*a1^2*x0^2*y0^2 -
      2*G^3*a1*a2*x0^3*y0 + G^3*a1*a3*x0*y0^2 - G^3*a1*a4*x0^2*y0 - 2*G^3*a1*x0^4*y0 +
      2*G^3*a1*x0*y0^3 + G^3*a2^2*x0^4 - G^3*a2*a3*x0^2*y0 + G^3*a2*a4*x0^3 + 2*G^3*a2*x0^5 -
      2*G^3*a2*x0^2*y0^2 - G^3*a3*x0^3*y0 + G^3*a3*y0^3 + G^3*a4*x0^4 - G^3*a4*x0*y0^2 -
      G^3*a6*x0^3 + G^3*x0^6 - 2*G^3*x0^3*y0^2 - G^2*X^5 - 2*G^2*X^4*a2 - G^2*X^4*x0 +
      2*G^2*X^3*Y*a1 - G^2*X^3*a1*y0 - G^2*X^3*a2^2 - G^2*X^3*a4 + 2*G^2*X^3*x0^2 + 2*G^2*X^2*Y^2 +
      2*G^2*X^2*Y*a1*a2 + G^2*X^2*Y*a1*x0 + G^2*X^2*Y*a3 - 2*G^2*X^2*Y*y0 - G^2*X^2*a1*a2*y0 -
      2*G^2*X^2*a1*x0*y0 + G^2*X^2*a2^2*x0 - G^2*X^2*a2*a4 + 4*G^2*X^2*a2*x0^2 - 2*G^2*X^2*a3*y0 +
      G^2*X^2*a4*x0 + G^2*X^2*a6 + 2*G^2*X^2*x0^3 - G^2*X^2*y0^2 - G^2*X*Y^2*a1^2 +
      2*G^2*X*Y^2*a2 + 2*G^2*X*Y^2*x0 + G^2*X*Y*a1^2*y0 - G^2*X*Y*a1*a2*x0 + G^2*X*Y*a1*a4 -
      2*G^2*X*Y*a1*x0^2 + G^2*X*Y*a2*a3 - 2*G^2*X*Y*a2*y0 + G^2*X*Y*a3*x0 - 2*G^2*X*Y*x0*y0 -
      G^2*X*a1*a2*x0*y0 - G^2*X*a1*a4*y0 + G^2*X*a1*x0^2*y0 + G^2*X*a2^2*x0^2 - G^2*X*a2*a3*y0 +
      2*G^2*X*a2*a4*x0 + G^2*X*a3*x0*y0 + G^2*X*a4*x0^2 - 2*G^2*X*a6*x0 - G^2*X*x0^4 +
      2*G^2*X*x0*y0^2 - 3*G^2*Y^3*a1 - G^2*Y^2*a1*a3 + 6*G^2*Y^2*a1*y0 + G^2*Y^2*a4 -
      G^2*Y^2*x0^2 + G^2*Y*a1^2*x0*y0 - G^2*Y*a1*a2*x0^2 + 2*G^2*Y*a1*a3*y0 - G^2*Y*a1*a4*x0 -
      G^2*Y*a1*x0^3 - 3*G^2*Y*a1*y0^2 - G^2*Y*a2*a3*x0 - 2*G^2*Y*a2*x0*y0 - 2*G^2*Y*a3*x0^2 -
      2*G^2*Y*a4*y0 - 2*G^2*Y*x0^2*y0 - G^2*a1^2*x0*y0^2 + 2*G^2*a1*a2*x0^2*y0 - G^2*a1*a3*y0^2 +
      G^2*a1*a4*x0*y0 + 2*G^2*a1*x0^3*y0 - G^2*a2^2*x0^3 + G^2*a2*a3*x0*y0 - G^2*a2*a4*x0^2 -
      2*G^2*a2*x0^4 + 2*G^2*a2*x0*y0^2 + G^2*a3*x0^2*y0 - G^2*a4*x0^3 + G^2*a4*y0^2 + G^2*a6*x0^2 -
      G^2*x0^5 + 2*G^2*x0^2*y0^2 - G*X^4 - 2*G*X^3*a2 - 2*G*X^3*x0 + 2*G*X^2*Y*a1 - G*X^2*a1*y0 -
      G*X^2*a2^2 - 2*G*X^2*a2*x0 - G*X^2*a4 + 3*G*X*Y^2 + 2*G*X*Y*a1*a2 + 3*G*X*Y*a1*x0 +
      G*X*Y*a3 - 4*G*X*Y*y0 - G*X*a1*a2*y0 - 3*G*X*a1*x0*y0 - G*X*a2*a4 + 2*G*X*a2*x0^2 -
      2*G*X*a3*y0 + G*X*a6 + 2*G*X*x0^3 - G*Y^2*a1^2 + 2*G*Y^2*a2 + 3*G*Y^2*x0 + G*Y*a1^2*y0 +
      G*Y*a1*a2*x0 + G*Y*a1*a4 + G*Y*a1*x0^2 + G*Y*a2*a3 - 2*G*Y*a2*y0 + 2*G*Y*a3*x0 -
      2*G*Y*x0*y0 - 2*G*a1*a2*x0*y0 - G*a1*a4*y0 - 2*G*a1*x0^2*y0 + G*a2^2*x0^2 - G*a2*a3*y0 +
      G*a2*a4*x0 + 2*G*a2*x0^3 - G*a3*x0*y0 + G*a4*x0^2 - G*a6*x0 + G*x0^4 - X^3 - 2*X^2*a2 -
      3*X^2*x0 + X*Y*a1 - X*a2^2 - 4*X*a2*x0 - X*a4 - 3*X*x0^2 - Y^2 + Y*a1*a2 + Y*a1*x0 - Y*a3 -
      a2^2*x0 - a2*a4 - 2*a2*x0^2 - a4*x0 + a6 - x0^3) * h3

private theorem tr_der {R : Type*} [CommRing R] [Algebra R B] (D : Derivation R B B) (a1 a2 a3 a4
    a6 x0 y0 c X Y G : B)
    (h1 : Y ^ 2 + a1 * X * Y + a3 * Y - (X ^ 3 + a2 * X ^ 2 + a4 * X + a6) = 0)
    (h2 : y0 ^ 2 + a1 * x0 * y0 + a3 * y0 - (x0 ^ 3 + a2 * x0 ^ 2 + a4 * x0 + a6) = 0)
    (h3 : (X - x0) * G - 1 = 0)
    (hk : D a1 = 0 ∧ D a2 = 0 ∧ D a3 = 0 ∧ D a4 = 0 ∧ D a6 = 0 ∧ D x0 = 0 ∧ D y0 = 0 ∧ D c = 0)
    (hX : D X = c * (2 * Y + a1 * X + a3))
    (hY : D Y = -(c * (a1 * Y - 3 * X ^ 2 - 2 * a2 * X - a4))) :
    D (trX a1 a2 x0 y0 X Y G) =
        c * (2 * trY a1 a2 a3 x0 y0 X Y G + a1 * trX a1 a2 x0 y0 X Y G + a3) ∧
      D (trY a1 a2 a3 x0 y0 X Y G) = -(c * (a1 * trY a1 a2 a3 x0 y0 X Y G -
        3 * trX a1 a2 x0 y0 X Y G ^ 2 - 2 * a2 * trX a1 a2 x0 y0 X Y G - a4)) := by
  obtain ⟨k1, k2, k3, k4, k6, kx, ky, kc⟩ := hk
  have hd := congrArg D h3
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, kx,
    sub_zero, map_zero] at hd
  have hG : D G = -(G ^ 2 * (c * (2 * Y + a1 * X + a3))) := by
    rw [← hX]; linear_combination G * hd - D G * h3
  unfold trY trX
  constructor
  · simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      hX, hY, hG, k1, k2, k3, k4, k6, kx, ky, kc, nsmul_eq_mul, Nat.cast_ofNat, mul_zero,
      add_zero, sub_zero, zero_add]
    linear_combination (-G^3*X*a1*c - 2*G^3*Y*c + G^3*a1*c*x0 + 2*G^3*c*y0) * h1 + (G^3*X*a1*c +
        2*G^3*Y*c - G^3*a1*c*x0 - 2*G^3*c*y0) * h2 + (-G^2*X^3*a1*c - 2*G^2*X^2*Y*c -
        G^2*X^2*a1*a2*c + 2*G^2*X^2*c*y0 + G^2*X*Y*a1^2*c - 2*G^2*X*Y*a2*c - 2*G^2*X*Y*c*x0 -
        G^2*X*a1*a4*c + 2*G^2*X*a2*c*y0 + 2*G^2*X*c*x0*y0 + G^2*Y^2*a1*c + G^2*Y*a1*a3*c +
        2*G^2*Y*a1*c*y0 - 2*G^2*Y*a2*c*x0 - 2*G^2*Y*a4*c - 2*G^2*Y*c*x0^2 - G^2*a1^2*c*x0*y0 +
        G^2*a1*a2*c*x0^2 - G^2*a1*a3*c*y0 + G^2*a1*a4*c*x0 + G^2*a1*c*x0^3 - 3*G^2*a1*c*y0^2 +
        2*G^2*a2*c*x0*y0 + 2*G^2*a4*c*y0 + 2*G^2*c*x0^2*y0 - G*X^2*a1*c + 4*G*X*Y*c - G*X*a1*a2*c -
        G*X*a1*c*x0 - 4*G*X*c*y0 + 2*G*Y*a2*c + 2*G*Y*c*x0 + G*a1^2*c*y0 - G*a1*a2*c*x0 -
        G*a1*a4*c - G*a1*c*x0^2 - 2*G*a2*c*y0 - 2*G*c*x0*y0 + 2*X*a1*c + a1*a2*c + a1*c*x0) * h3
  · simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      hX, hY, hG, k1, k2, k3, k4, k6, kx, ky, kc, nsmul_eq_mul, Nat.cast_ofNat, mul_zero,
      add_zero, sub_zero, zero_add]
    linear_combination (G^4*X^2*a1^2*c - G^4*X^2*a2*c - 3*G^4*X^2*c*x0 + 4*G^4*X*Y*a1*c -
        2*G^4*X*a1^2*c*x0 - 4*G^4*X*a1*c*y0 + 2*G^4*X*a2*c*x0 + 6*G^4*X*c*x0^2 + 3*G^4*Y^2*c -
        4*G^4*Y*a1*c*x0 - 6*G^4*Y*c*y0 + G^4*a1^2*c*x0^2 + G^4*a1*c*x0*y0 + 2*G^4*a2*c*x0^2 -
        3*G^4*a3*c*y0 + 3*G^4*a4*c*x0 + 3*G^4*a6*c) * h1 + (-3*G^4*X^3*c - G^4*X^2*a1^2*c -
        2*G^4*X^2*a2*c + 3*G^4*X^2*c*x0 - G^4*X*Y*a1*c + 2*G^4*X*a1^2*c*x0 + 4*G^4*X*a1*c*y0 -
        2*G^4*X*a2*c*x0 - 3*G^4*X*a4*c - 6*G^4*X*c*x0^2 + 4*G^4*Y*a1*c*x0 + 3*G^4*Y*a3*c +
        6*G^4*Y*c*y0 - G^4*a1^2*c*x0^2 - 4*G^4*a1*c*x0*y0 + G^4*a2*c*x0^2 - 3*G^4*a6*c +
        3*G^4*c*x0^3 - 3*G^4*c*y0^2) * h2 + (G^3*X^4*a1^2*c - G^3*X^4*a2*c - 3*G^3*X^4*c*x0 +
        4*G^3*X^3*Y*a1*c + G^3*X^3*a1^2*a2*c - G^3*X^3*a1^2*c*x0 - 4*G^3*X^3*a1*c*y0 -
        G^3*X^3*a2^2*c - 2*G^3*X^3*a2*c*x0 + 3*G^3*X^3*c*x0^2 + 3*G^3*X^2*Y^2*c -
        G^3*X^2*Y*a1^3*c + 5*G^3*X^2*Y*a1*a2*c + 3*G^3*X^2*Y*a1*c*x0 - 6*G^3*X^2*Y*c*y0 -
        G^3*X^2*a1^2*a2*c*x0 + G^3*X^2*a1^2*a4*c - 4*G^3*X^2*a1*a2*c*y0 + G^3*X^2*a2^2*c*x0 -
        G^3*X^2*a2*a4*c + 3*G^3*X^2*a2*c*x0^2 - 3*G^3*X^2*a4*c*x0 + 3*G^3*X^2*c*y0^2 -
        5*G^3*X*Y^2*a1^2*c + 4*G^3*X*Y^2*a2*c + 6*G^3*X*Y^2*c*x0 + G^3*X*Y*a1^3*c*x0 -
        G^3*X*Y*a1^2*a3*c + 4*G^3*X*Y*a1^2*c*y0 - G^3*X*Y*a1*a2*c*x0 + 4*G^3*X*Y*a1*a4*c -
        3*G^3*X*Y*a1*c*x0^2 + G^3*X*Y*a2*a3*c - 6*G^3*X*Y*a2*c*y0 + 3*G^3*X*Y*a3*c*x0 -
        6*G^3*X*Y*c*x0*y0 + G^3*X*a1^3*c*x0*y0 - G^3*X*a1^2*a2*c*x0^2 + G^3*X*a1^2*a3*c*y0 -
        2*G^3*X*a1^2*a4*c*x0 - G^3*X*a1^2*c*x0^3 + G^3*X*a1^2*c*y0^2 - G^3*X*a1*a2*c*x0*y0 -
        4*G^3*X*a1*a4*c*y0 - 3*G^3*X*a1*c*x0^2*y0 + G^3*X*a2^2*c*x0^2 - G^3*X*a2*a3*c*y0 +
        2*G^3*X*a2*a4*c*x0 + 4*G^3*X*a2*c*x0^3 + 2*G^3*X*a2*c*y0^2 - 3*G^3*X*a3*c*x0*y0 +
        6*G^3*X*a4*c*x0^2 + 3*G^3*X*c*x0^4 - 4*G^3*Y^3*a1*c + G^3*Y^2*a1^2*c*x0 -
        4*G^3*Y^2*a1*a3*c + G^3*Y^2*a1*c*y0 + 2*G^3*Y^2*a2*c*x0 + 3*G^3*Y^2*a4*c +
        G^3*Y*a1^2*a3*c*x0 + 4*G^3*Y*a1^2*c*x0*y0 - 4*G^3*Y*a1*a2*c*x0^2 + 8*G^3*Y*a1*a3*c*y0 -
        4*G^3*Y*a1*a4*c*x0 - 4*G^3*Y*a1*c*x0^3 + 10*G^3*Y*a1*c*y0^2 - G^3*Y*a2*a3*c*x0 -
        6*G^3*Y*a2*c*x0*y0 - 3*G^3*Y*a3*c*x0^2 - 6*G^3*Y*a4*c*y0 - 6*G^3*Y*c*x0^2*y0 -
        G^3*a1^3*c*x0^2*y0 + G^3*a1^2*a2*c*x0^3 - G^3*a1^2*a3*c*x0*y0 + G^3*a1^2*a4*c*x0^2 +
        G^3*a1^2*c*x0^4 - 5*G^3*a1^2*c*x0*y0^2 + 5*G^3*a1*a2*c*x0^2*y0 - 4*G^3*a1*a3*c*y0^2 +
        4*G^3*a1*a4*c*x0*y0 + 7*G^3*a1*c*x0^3*y0 - 7*G^3*a1*c*y0^3 - G^3*a2^2*c*x0^3 +
        G^3*a2*a3*c*x0*y0 - G^3*a2*a4*c*x0^2 - 4*G^3*a2*c*x0^4 + 4*G^3*a2*c*x0*y0^2 +
        3*G^3*a3*c*x0^2*y0 - 3*G^3*a4*c*x0^3 + 3*G^3*a4*c*y0^2 - 3*G^3*c*x0^5 + 6*G^3*c*x0^2*y0^2 +
        G^2*X^3*a1^2*c - G^2*X^3*a2*c - 3*G^2*X^3*c*x0 + 4*G^2*X^2*Y*a1*c + G^2*X^2*a1^2*a2*c -
        4*G^2*X^2*a1*c*y0 - G^2*X^2*a2^2*c - 3*G^2*X^2*a2*c*x0 - 6*G^2*X*Y^2*c - G^2*X*Y*a1^3*c +
        5*G^2*X*Y*a1*a2*c + 7*G^2*X*Y*a1*c*x0 + 12*G^2*X*Y*c*y0 + G^2*X*a1^2*a4*c -
        4*G^2*X*a1*a2*c*y0 - 4*G^2*X*a1*c*x0*y0 - G^2*X*a2*a4*c - 3*G^2*X*a4*c*x0 -
        6*G^2*X*c*y0^2 - G^2*Y^2*a1^2*c - 2*G^2*Y^2*a2*c - G^2*Y*a1^2*a3*c - 4*G^2*Y*a1^2*c*y0 +
        4*G^2*Y*a1*a2*c*x0 + 4*G^2*Y*a1*a4*c + 4*G^2*Y*a1*c*x0^2 + G^2*Y*a2*a3*c +
        6*G^2*Y*a2*c*y0 + 3*G^2*Y*a3*c*x0 + 6*G^2*Y*c*x0*y0 + G^2*a1^3*c*x0*y0 -
        G^2*a1^2*a2*c*x0^2 + G^2*a1^2*a3*c*y0 - G^2*a1^2*a4*c*x0 - G^2*a1^2*c*x0^3 +
        5*G^2*a1^2*c*y0^2 - 5*G^2*a1*a2*c*x0*y0 - 4*G^2*a1*a4*c*y0 - 7*G^2*a1*c*x0^2*y0 +
        G^2*a2^2*c*x0^2 - G^2*a2*a3*c*y0 + G^2*a2*a4*c*x0 + 4*G^2*a2*c*x0^3 - 4*G^2*a2*c*y0^2 -
        3*G^2*a3*c*x0*y0 + 3*G^2*a4*c*x0^2 + 3*G^2*c*x0^4 - 6*G^2*c*x0*y0^2 + G*X^2*a1^2*c -
        G*X^2*a2*c - 3*G*X^2*c*x0 - 10*G*X*Y*a1*c + G*X*a1^2*a2*c + G*X*a1^2*c*x0 +
        10*G*X*a1*c*y0 - G*X*a2^2*c - 4*G*X*a2*c*x0 - 3*G*X*c*x0^2 - 4*G*Y^2*c - 4*G*Y*a1*a2*c -
        4*G*Y*a1*c*x0 - 2*G*Y*a3*c + 4*G*Y*c*y0 - G*a1^3*c*y0 + G*a1^2*a2*c*x0 + G*a1^2*a4*c +
        G*a1^2*c*x0^2 + 5*G*a1*a2*c*y0 + 7*G*a1*c*x0*y0 - G*a2^2*c*x0 - G*a2*a4*c - 4*G*a2*c*x0^2 +
        2*G*a3*c*y0 - 3*G*a4*c*x0 - 3*G*c*x0^3 + 6*X^2*c - 2*X*a1^2*c + 6*X*a2*c + 6*X*c*x0 -
        2*Y*a1*c - a1^2*a2*c - a1^2*c*x0 + a2^2*c + 4*a2*c*x0 + 2*a4*c + 3*c*x0^2) * h3

end EllTr

namespace EllPts

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass Polynomial

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- Evaluation at an affine point. -/
private noncomputable def ev (x y : K) (h : W.toAffine.Equation x y) :
    W.toAffine.CoordinateRing →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom x) y (by rw [Polynomial.eval₂_evalRingHom]; exact h)

private theorem ev_x (x y : K) (h) : ev W x y h (EllAlg.xA W) = x := by
  simp [ev, EllAlg.xA, WeierstrassCurve.Affine.CoordinateRing.mk]

private theorem ev_y (x y : K) (h) : ev W x y h (EllAlg.yA W) = y := by
  simp [ev, EllAlg.yA, WeierstrassCurve.Affine.CoordinateRing.mk]

private theorem ev_alg (x y : K) (h) (c : K) :
    ev W x y h (algebraMap K W.toAffine.CoordinateRing c) = c := by
  change ev W x y h (WeierstrassCurve.Affine.CoordinateRing.mk W (C (C c))) = c
  simp [ev, WeierstrassCurve.Affine.CoordinateRing.mk]

/-- Two ring maps out of the coordinate ring which fix the constants agree once they agree on
`x` and `y`. -/
private theorem ringHom_ext {S : Type*} [CommRing S] [Algebra K S] (φ ψ : W.toAffine.CoordinateRing
    →+* S)
    (hφ : ∀ c, φ (algebraMap K _ c) = algebraMap K S c)
    (hψ : ∀ c, ψ (algebraMap K _ c) = algebraMap K S c)
    (hx : φ (EllAlg.xA W) = ψ (EllAlg.xA W)) (hy : φ (EllAlg.yA W) = ψ (EllAlg.yA W)) :
    φ = ψ := by
  let φ' : W.toAffine.CoordinateRing →ₐ[K] S := { φ with commutes' := hφ }
  let ψ' : W.toAffine.CoordinateRing →ₐ[K] S := { ψ with commutes' := hψ }
  refine RingHom.ext fun a => ?_
  obtain ⟨p, q, rfl⟩ := EllAlg.repr W a
  have h1 : ∀ r : K[X], φ (aeval (EllAlg.xA W) r) = ψ (aeval (EllAlg.xA W) r) := by
    intro r
    change φ' (aeval (EllAlg.xA W) r) = ψ' (aeval (EllAlg.xA W) r)
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
    exact congrArg (fun z => aeval z r) hx
  simp only [map_add, map_mul, h1, hy]

section Sections

variable {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) (eW : C ≅ projOf W)

/-- The rational point of `C` with affine Weierstrass coordinates `(x, y)`. -/
private noncomputable def pt (x y : K) (h : W.toAffine.Equation x y) : Spec (.of K) ⟶ C :=
  Spec.map (CommRingCat.ofHom (ev W x y h)) ≫ chartZ W ≫ eW.inv

private theorem algebraMap_comp_ev (x y : K) (h) :
    CommRingCat.ofHom (algebraMap K W.toAffine.CoordinateRing) ≫ CommRingCat.ofHom (ev W x y h) =
      𝟙 _ := by
  ext c; exact ev_alg W x y h c

private theorem pt_comp (hover : eW.hom ≫ projectionOf W = f) (x y : K) (h) :
    pt W eW x y h ≫ f = 𝟙 _ := by
  have h1 : eW.inv ≫ f = projectionOf W := by rw [← hover, Iso.inv_hom_id_assoc]
  rw [pt, Category.assoc, Category.assoc, h1, chartZ_projectionOf, ← Spec.map_comp,
    algebraMap_comp_ev, Spec.map_id]

private theorem pt_inj {x y x' y' : K} {h h'} (he : pt W eW x y h = pt W eW x' y' h') :
    x = x' ∧ y = y' := by
  have h1 : Spec.map (CommRingCat.ofHom (ev W x y h)) =
      Spec.map (CommRingCat.ofHom (ev W x' y' h')) :=
    (cancel_mono (chartZ W ≫ eW.inv)).1 he
  have h3 : ev W x y h = ev W x' y' h' := by
    simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  constructor
  · rw [← ev_x W x y h, ← ev_x W x' y' h', h3]
  · rw [← ev_y W x y h, ← ev_y W x' y' h', h3]

private theorem pt_ne (o : Spec (.of K) ⟶ C) (hzero : o ≫ eW.hom = zeroOf W) (x y : K) (h) :
    pt W eW x y h ≠ o := by
  intro he
  have h1 : Spec.map (CommRingCat.ofHom (ev W x y h)) ≫ chartZ W = zeroOf W := by
    rw [← hzero, ← he, pt, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let z : Spec (.of K) := IsLocalRing.closedPoint K
  have hz1 : (zeroOf W) z ∈ Set.range (zeroOf W) := ⟨z, rfl⟩
  rw [range_zeroOf, ← h1] at hz1
  apply hz1
  rw [Scheme.Hom.comp_apply, ← opensRange_chartZ W]
  exact ⟨_, rfl⟩

private theorem sect_cases (hover : eW.hom ≫ projectionOf W = f) (o : Spec (.of K) ⟶ C)
    (hzero : o ≫ eW.hom = zeroOf W) (p : Spec (.of K) ⟶ C) (hp : p ≫ f = 𝟙 _) :
    p = o ∨ ∃ x y h, p = pt W eW x y h := by
  by_cases hmem : (p ≫ eW.hom) (IsLocalRing.closedPoint K) ∈ basicOpenOf W (coordOf W 2)
  · right
    have hrange : Set.range (p ≫ eW.hom) ⊆ Set.range (chartZ W) := by
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
      rwa [← opensRange_chartZ W] at hmem
    let q := IsOpenImmersion.lift (chartZ W) (p ≫ eW.hom) hrange
    have hq : q ≫ chartZ W = p ≫ eW.hom := IsOpenImmersion.lift_fac _ _ _
    let φ := Spec.preimage q
    have hφ : Spec.map φ = q := Spec.map_preimage q
    have hφK : CommRingCat.ofHom (algebraMap K W.toAffine.CoordinateRing) ≫ φ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, Spec.map_id, ← chartZ_projectionOf, ← Category.assoc, hq,
        Category.assoc, hover, hp]
    have hφc : ∀ c, φ.hom (algebraMap K _ c) = c := fun c =>
      congrArg (fun g => g.hom c) hφK
    have hxy : W.toAffine.Equation (φ.hom (EllAlg.xA W)) (φ.hom (EllAlg.yA W)) := by
      have := congrArg φ.hom (EllAlg.rel W)
      simp only [map_add, map_mul, map_pow, hφc] at this
      rw [WeierstrassCurve.Affine.equation_iff]
      exact this
    refine ⟨_, _, hxy, ?_⟩
    have hev : ev W _ _ hxy = φ.hom :=
      ringHom_ext W _ _ (ev_alg W _ _ hxy) hφc (ev_x W _ _ hxy) (ev_y W _ _ hxy)
    rw [pt, hev, CommRingCat.ofHom_hom, hφ, ← Category.assoc, hq, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · left
    have h1 := GenusOne.eq_zeroOf_of_notMem_basicOpenOf W (p ≫ eW.hom)
      (by rw [Category.assoc, hover, hp]) hmem
    rw [← hzero] at h1
    exact (cancel_mono eW.hom).1 h1

end Sections

end EllPts

namespace EllTrRing

open Polynomial

variable {K : Type u} [Field K] (W : WeierstrassCurve K) (x0 y0 : K)

local notation "A" => W.toAffine.CoordinateRing

/-- The function `x - x₀`. -/
private noncomputable def gx : A := EllAlg.xA W - algebraMap K A x0

/-- The localisation away from `x = x₀`. -/
private abbrev LB := Localization.Away (gx W x0)

/-- The inverse of `x - x₀`. -/
private noncomputable def Gi : LB W x0 := IsLocalization.Away.invSelf (gx W x0)

local notation "κ" => algebraMap K (LB W x0)
local notation "ιA" => algebraMap A (LB W x0)

/-- The `x`-coordinate of the translate by `(x₀, y₀)`. -/
private noncomputable def Xt : LB W x0 :=
  EllTr.trX (κ W.a₁) (κ W.a₂) (κ x0) (κ y0) (ιA (EllAlg.xA W)) (ιA (EllAlg.yA W)) (Gi W x0)

/-- The `y`-coordinate of the translate by `(x₀, y₀)`. -/
private noncomputable def Yt : LB W x0 :=
  EllTr.trY (κ W.a₁) (κ W.a₂) (κ W.a₃) (κ x0) (κ y0) (ιA (EllAlg.xA W)) (ιA (EllAlg.yA W))
    (Gi W x0)

private theorem weierstrass_xy_eq_zero :
    ιA (EllAlg.yA W) ^ 2 + κ W.a₁ * ιA (EllAlg.xA W) * ιA (EllAlg.yA W) +
    κ W.a₃ * ιA (EllAlg.yA W) - (ιA (EllAlg.xA W) ^ 3 + κ W.a₂ * ιA (EllAlg.xA W) ^ 2 +
      κ W.a₄ * ιA (EllAlg.xA W) + κ W.a₆) = 0 := by
  have := congrArg ιA (EllAlg.rel W)
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at this
  rw [this]; ring

private theorem weierstrass_base_eq_zero (h0 : W.toAffine.Equation x0 y0) :
    κ y0 ^ 2 + κ W.a₁ * κ x0 * κ y0 + κ W.a₃ * κ y0 -
    (κ x0 ^ 3 + κ W.a₂ * κ x0 ^ 2 + κ W.a₄ * κ x0 + κ W.a₆) = 0 := by
  have h := (WeierstrassCurve.Affine.equation_iff _ _).1 h0
  have := congrArg κ h
  simp only [map_add, map_mul, map_pow] at this
  rw [this]; ring

private theorem sub_mul_Gi_sub_one : (ιA (EllAlg.xA W) - κ x0) * Gi W x0 - 1 = 0 := by
  have : ιA (EllAlg.xA W) - κ x0 = ιA (gx W x0) := by
    simp [gx, ← IsScalarTower.algebraMap_apply]
  rw [this, Gi, IsLocalization.Away.mul_invSelf, sub_self]

/-- The translation by `(x₀, y₀)` on coordinate rings. -/
private noncomputable def transl (h0 : W.toAffine.Equation x0 y0) : A →+* LB W x0 :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom κ (Xt W x0 y0)) (Yt W x0 y0) (by
    have := EllTr.tr_eq (κ W.a₁) (κ W.a₂) (κ W.a₃) (κ W.a₄) (κ W.a₆) (κ x0) (κ y0)
      (ιA (EllAlg.xA W)) (ιA (EllAlg.yA W)) (Gi W x0) (weierstrass_xy_eq_zero W x0)
      (weierstrass_base_eq_zero W x0 y0 h0) (sub_mul_Gi_sub_one W x0)
    simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_C, coe_eval₂RingHom]
    rw [← this]
    simp only [Xt, Yt]
    ring)

private theorem transl_x (h0 : W.toAffine.Equation x0 y0) :
    transl W x0 y0 h0 (EllAlg.xA W) = Xt W x0 y0 := by
  simp [transl, EllAlg.xA, WeierstrassCurve.Affine.CoordinateRing.mk]

private theorem transl_y (h0 : W.toAffine.Equation x0 y0) :
    transl W x0 y0 h0 (EllAlg.yA W) = Yt W x0 y0 := by
  simp [transl, EllAlg.yA, WeierstrassCurve.Affine.CoordinateRing.mk]

private theorem transl_algebraMap (h0 : W.toAffine.Equation x0 y0) (c : K) :
    transl W x0 y0 h0 (algebraMap K A c) = κ c := by
  change transl W x0 y0 h0 (WeierstrassCurve.Affine.CoordinateRing.mk W (C (C c))) = _
  simp [transl, WeierstrassCurve.Affine.CoordinateRing.mk]

private theorem ev_gx (x y : K) (h : W.toAffine.Equation x y) :
    EllPts.ev W x y h (gx W x0) = x - x0 := by
  simp [gx, EllPts.ev_x, EllPts.ev_alg]

/-- Evaluation at a point off `x = x₀`, on the localisation. -/
private noncomputable def evB (x y : K) (h : W.toAffine.Equation x y) (hx : x ≠ x0) :
    LB W x0 →+* K :=
  IsLocalization.Away.lift (S := LB W x0) (gx W x0) (g := EllPts.ev W x y h)
    (by rw [ev_gx]; exact (sub_ne_zero.2 hx).isUnit)

private theorem evB_ιA (x y : K) (h) (hx : x ≠ x0) (a : A) : evB W x0 x y h hx (ιA a) =
    EllPts.ev W x y h a :=
  IsLocalization.Away.lift_eq _ _ a

private theorem evB_κ (x y : K) (h) (hx : x ≠ x0) (c : K) : evB W x0 x y h hx (κ c) = c := by
  rw [IsScalarTower.algebraMap_apply K A, evB_ιA, EllPts.ev_alg]

private theorem evB_G (x y : K) (h) (hx : x ≠ x0) : evB W x0 x y h hx (Gi W x0) = (x - x0)⁻¹ := by
  have h1 := congrArg (evB W x0 x y h hx) (IsLocalization.Away.mul_invSelf (S := LB W x0) (gx W x0))
  rw [map_mul, map_one, evB_ιA, ev_gx] at h1
  exact (eq_inv_of_mul_eq_one_right h1)

/-- The translated coordinates at a point. -/
private noncomputable def tX (x y : K) : K := EllTr.trX W.a₁ W.a₂ x0 y0 x y (x - x0)⁻¹
private noncomputable def tY (x y : K) : K := EllTr.trY W.a₁ W.a₂ W.a₃ x0 y0 x y (x - x0)⁻¹

private theorem equation_tX_tY (h0 : W.toAffine.Equation x0 y0) (x y : K)
    (h : W.toAffine.Equation x y) (hx : x ≠ x0) :
    W.toAffine.Equation (tX W x0 y0 x y) (tY W x0 y0 x y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h1 := (WeierstrassCurve.Affine.equation_iff _ _).1 h
  have h2 := (WeierstrassCurve.Affine.equation_iff _ _).1 h0
  have := EllTr.tr_eq W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ x0 y0 x y (x - x0)⁻¹ (by rw [h1]; ring)
    (by rw [h2]; ring) (by rw [mul_inv_cancel₀ (sub_ne_zero.2 hx)]; ring)
  simp only [tX, tY]
  linear_combination this

private theorem evB_transl (h0 : W.toAffine.Equation x0 y0) (x y : K) (h : W.toAffine.Equation x y)
    (hx : x ≠ x0) :
    (evB W x0 x y h hx).comp (transl W x0 y0 h0) =
      EllPts.ev W _ _ (equation_tX_tY W x0 y0 h0 x y h hx) := by
  refine EllPts.ringHom_ext W _ _ (fun c => ?_) (EllPts.ev_alg W _ _ _) ?_ ?_
  · rw [RingHom.comp_apply, transl_algebraMap, evB_κ]; rfl
  · rw [RingHom.comp_apply, transl_x, EllPts.ev_x, Xt, tX]
    simp only [EllTr.trX, map_add, map_sub, map_mul, map_pow, evB_κ, evB_ιA, evB_G,
      EllPts.ev_x, EllPts.ev_y]
  · rw [RingHom.comp_apply, transl_y, EllPts.ev_y, Yt, tY]
    simp only [EllTr.trY, EllTr.trX, map_add, map_sub, map_neg, map_mul, map_pow, evB_κ, evB_ιA,
      evB_G, EllPts.ev_x, EllPts.ev_y]

private theorem add_eq [DecidableEq K] [W.IsElliptic] (h0 : W.toAffine.Equation x0 y0) (x y : K)
    (h : W.toAffine.Equation x y) (hx : x ≠ x0) :
    (WeierstrassCurve.Affine.Point.some x y (WeierstrassCurve.Affine.equation_iff_nonsingular.1 h) +
      WeierstrassCurve.Affine.Point.some x0 y0
        (WeierstrassCurve.Affine.equation_iff_nonsingular.1 h0) : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some (tX W x0 y0 x y) (tY W x0 y0 x y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.1
          (equation_tX_tY W x0 y0 h0 x y h hx)) := by
  rw [WeierstrassCurve.Affine.Point.add_some (fun hh => hx hh.1)]
  have hsl := WeierstrassCurve.Affine.slope_of_X_ne (W := W.toAffine) (y₁ := y) (y₂ := y0) hx
  congr 1
  · rw [hsl, tX, EllTr.trX, WeierstrassCurve.Affine.addX]; ring
  · rw [hsl, tY, EllTr.trY, EllTr.trX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.addX]; ring

end EllTrRing

namespace EllTrSch

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass EllTrRing

variable {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) (W : WeierstrassCurve K)
  (eW : C ≅ projOf W) (x0 y0 : K) (h0 : W.toAffine.Equation x0 y0)

/-- The chart `C ∖ {o} ≅ Spec A`. -/
private noncomputable def jC : Spec (.of W.toAffine.CoordinateRing) ⟶ C := chartZ W ≫ eW.inv

/-- The open `x ≠ x₀` of the chart. -/
private noncomputable def ιV : Spec (.of (LB W x0)) ⟶ C :=
  Spec.map (CommRingCat.ofHom (algebraMap W.toAffine.CoordinateRing (LB W x0))) ≫ jC W eW

/-- The translation on the open `x ≠ x₀`. -/
private noncomputable def μ : Spec (.of (LB W x0)) ⟶ C :=
  Spec.map (CommRingCat.ofHom (transl W x0 y0 h0)) ≫ jC W eW

private theorem transl_comp_algebraMap :
    CommRingCat.ofHom (algebraMap K W.toAffine.CoordinateRing) ≫
        CommRingCat.ofHom (transl W x0 y0 h0) =
      CommRingCat.ofHom (algebraMap K (LB W x0)) := by
  ext c; exact transl_algebraMap W x0 y0 h0 c

private theorem jC_f (hover : eW.hom ≫ projectionOf W = f) :
    jC W eW ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K W.toAffine.CoordinateRing)) := by
  have h1 : eW.inv ≫ f = projectionOf W := by rw [← hover, Iso.inv_hom_id_assoc]
  rw [jC, Category.assoc, h1, chartZ_projectionOf]

private theorem μ_f (hover : eW.hom ≫ projectionOf W = f) :
    μ W eW x0 y0 h0 ≫ f = ιV W eW x0 ≫ f := by
  rw [μ, ιV, Category.assoc, Category.assoc, jC_f f W eW hover, ← Spec.map_comp, ← Spec.map_comp,
    transl_comp_algebraMap, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

private theorem isOpenImmersion_jC : IsOpenImmersion (jC W eW) := by unfold jC; infer_instance

private theorem isOpenImmersion_ιV : IsOpenImmersion (ιV W eW x0) := by
  have := isOpenImmersion_jC W eW; unfold ιV; infer_instance

private theorem gx_ne_zero : gx W x0 ≠ 0 := by
  intro h
  have := (EllAlg.eq_zero_of_repr W (p := Polynomial.X - Polynomial.C x0) (q := 0) (by
    have h' : EllAlg.xA W - algebraMap K _ x0 = 0 := h
    simpa [EllAlg.xA] using h')).1
  exact Polynomial.X_sub_C_ne_zero x0 this

private theorem isDomain_LB : IsDomain (LB W x0) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (gx_ne_zero W
      x0))

attribute [local instance] isDomain_LB

private theorem exists_ρ [IsAlgClosed K] [IsCurve K f] [Smooth f] [IsProper f] [IsIntegral C]
    (hover : eW.hom ≫ projectionOf W = f) :
    ∃ ρ : C ⟶ C, ρ ≫ f = f ∧ ιV W eW x0 ≫ ρ = μ W eW x0 y0 h0 := by
  haveI := isOpenImmersion_ιV W eW x0
  letI : C.Over (Spec (.of K)) := ⟨f⟩
  let V := (ιV W eW x0).opensRange
  have hVne : (V : Set C).Nonempty := by
    obtain ⟨z⟩ : Nonempty (Spec (.of (LB W x0))) := inferInstance
    exact ⟨_, z, rfl⟩
  have hVd : Dense (V : Set C) := V.isOpen.dense hVne
  let μP : C.PartialMap C := ⟨V, hVd, (ιV W eW x0).isoOpensRange.inv ≫ μ W eW x0 y0 h0⟩
  have hμP : μP.IsOver (Spec (.of K)) := by
    constructor
    show ((ιV W eW x0).isoOpensRange.inv ≫ μ W eW x0 y0 h0) ≫ f = V.ι ≫ f
    rw [Category.assoc, μ_f f W eW x0 y0 h0 hover, Iso.inv_comp_eq, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι]
  have hPV : IsProperVariety K f := (isProperVariety_iff K f).2 ⟨inferInstance, inferInstance⟩
  haveI hC : IsCurve K (Over.mk f).hom := ‹IsCurve K f›
  haveI : IsProperVariety K (Over.mk f).hom := hPV
  haveI : IsNormal (Spec (.of K)) := isNormal_spec_of_isIntegrallyClosed K
  haveI : IsNormal (Over.mk f).left := isNormal_of_smooth f
  obtain ⟨ρo, hρo⟩ := (toRationalMap_bijective K (Over.mk f) (Over.mk f)).2
    ⟨μP.toRationalMap, inferInstance⟩
  refine ⟨ρo.left, Over.w ρo, ?_⟩
  have h1 : ρo.left.toRationalMap = μP.toRationalMap := congrArg Subtype.val hρo
  have h2 : μP.equiv ρo.left.toPartialMap :=
    Scheme.PartialMap.toRationalMap_eq_iff.1 h1.symm
  haveI : ρo.left.IsOver (Spec (.of K)) := ⟨Over.w ρo⟩
  haveI : IsSeparated (C ↘ Spec (.of K)) := (inferInstance : IsSeparated f)
  rw [Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := Spec (.of K))] at h2
  rw [← (ιV W eW x0).isoOpensRange_hom_ι, Category.assoc]
  change _ ≫ V.ι ≫ ρo.left = _
  rw [← h2]
  exact Iso.hom_inv_id_assoc _ _

private theorem pt_eq_ιV (x y : K) (h : W.toAffine.Equation x y) (hx : x ≠ x0) :
    EllPts.pt W eW x y h =
      Spec.map (CommRingCat.ofHom (evB W x0 x y h hx)) ≫ ιV W eW x0 := by
  have : CommRingCat.ofHom (EllPts.ev W x y h) =
      CommRingCat.ofHom (algebraMap W.toAffine.CoordinateRing (LB W x0)) ≫
        CommRingCat.ofHom (evB W x0 x y h hx) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (RingHom.ext fun a => (evB_ιA W x0 x y h hx a).symm)
  rw [EllPts.pt, ιV, jC, this, Spec.map_comp, Category.assoc]

private theorem pt_ρ (ρ : C ⟶ C) (hρ : ιV W eW x0 ≫ ρ = μ W eW x0 y0 h0) (x y : K)
    (h : W.toAffine.Equation x y) (hx : x ≠ x0) :
    EllPts.pt W eW x y h ≫ ρ =
      EllPts.pt W eW (tX W x0 y0 x y) (tY W x0 y0 x y) (equation_tX_tY W x0 y0 h0 x y h hx) := by
  rw [pt_eq_ιV W eW x0 x y h hx, Category.assoc, hρ, μ, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, evB_transl, EllPts.pt, jC]

private theorem ne_of_mem_V (x y : K) (h : W.toAffine.Equation x y) (z : Spec (.of K))
    (hm : (EllPts.pt W eW x y h) z ∈ Set.range (ιV W eW x0)) :
    x ≠ x0 := by
  haveI := isOpenImmersion_jC W eW
  obtain ⟨w, hw⟩ := hm
  rw [ιV, EllPts.pt, ← jC, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hw
  have hw' := (jC W eW).isOpenEmbedding.injective hw
  rw [Spec.map_apply, Spec.map_apply] at hw'
  have hg : gx W x0 ∉ (PrimeSpectrum.comap (algebraMap W.toAffine.CoordinateRing (LB W x0))
      w).asIdeal := by
    intro hmem
    exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      (IsLocalization.Away.algebraMap_isUnit (gx W x0)))
  rw [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hw'
  rw [hw'] at hg
  intro hx
  apply hg
  change EllPts.ev W x y h (gx W x0) ∈ z.asIdeal
  rw [ev_gx, hx, sub_self]
  exact Ideal.zero_mem _

private theorem ιV_f (hover : eW.hom ≫ projectionOf W = f) :
    ιV W eW x0 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K (LB W x0))) := by
  rw [ιV, Category.assoc, jC_f f W eW hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

private theorem exists_pt_of_mem [IsAlgClosed K] [LocallyOfFiniteType f]
    (hover : eW.hom ≫ projectionOf W = f) (z : C) (hz : IsClosed {z})
    (hzV : z ∈ Set.range (ιV W eW x0)) :
    ∃ a b h, a ≠ x0 ∧ z ∈ Set.range (EllPts.pt W eW a b h) := by
  haveI := isOpenImmersion_ιV W eW x0
  obtain ⟨w, rfl⟩ := hzV
  have hw : IsClosed {w} := by
    have : ({w} : Set _) = (ιV W eW x0) ⁻¹' {(ιV W eW x0) w} :=
      Set.ext fun t => ⟨fun ht => by rw [Set.mem_singleton_iff.1 ht]; rfl,
        fun ht => (ιV W eW x0).isOpenEmbedding.injective ht⟩
    rw [this]; exact hz.preimage (ιV W eW x0).continuous
  let q := pointOfClosedPoint (ιV W eW x0 ≫ f) w hw
  have hq := pointOfClosedPoint_comp (ιV W eW x0 ≫ f) w hw
  let φ := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have hφK : ∀ c, φ.hom (algebraMap K _ c) = c := by
    have : CommRingCat.ofHom (algebraMap K (LB W x0)) ≫ φ = 𝟙 _ := by
      apply Spec.map_injective
      rwa [Spec.map_comp, hφ, Spec.map_id, ← ιV_f f W eW x0 hover]
    exact fun c => congrArg (fun g => g.hom c) this
  have hab : W.toAffine.Equation (φ.hom (algebraMap _ (LB W x0) (EllAlg.xA W)))
      (φ.hom (algebraMap _ (LB W x0) (EllAlg.yA W))) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have := congrArg φ.hom (weierstrass_xy_eq_zero W x0)
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, hφK] at this
    linear_combination this
  have hev : EllPts.ev W _ _ hab = φ.hom.comp (algebraMap _ (LB W x0)) :=
    EllPts.ringHom_ext W _ _ (EllPts.ev_alg W _ _ hab)
      (fun c => by simp [← IsScalarTower.algebraMap_apply, hφK]) (EllPts.ev_x W _ _ hab)
      (EllPts.ev_y W _ _ hab)
  have ha : φ.hom (algebraMap _ (LB W x0) (EllAlg.xA W)) ≠ x0 := by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := LB W x0) (gx W x0)).map φ.hom
    rw [← RingHom.comp_apply, ← hev, ev_gx] at hu
    exact sub_ne_zero.1 hu.ne_zero
  obtain ⟨z0⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine ⟨_, _, hab, ha, z0, ?_⟩
  have hpt : EllPts.pt W eW _ _ hab = q ≫ ιV W eW x0 := by
    rw [EllPts.pt, hev, ← hφ, ιV, jC, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      CommRingCat.ofHom_hom]
  rw [hpt, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]

end EllTrSch

namespace EllPts2

open Polynomial

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

private theorem exists_y [IsAlgClosed K] (a : K) : ∃ b, W.toAffine.Equation a b := by
  let p : K[X] := Polynomial.X ^ 2 + C (W.a₁ * a + W.a₃) * Polynomial.X -
    C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆)
  have hp : p.degree ≠ 0 := by
    have : p.natDegree = 2 := by
      simp only [p]; compute_degree!
    intro h; rw [degree_eq_natDegree (by intro h'; simp [h'] at this),
        this] at h; exact absurd h (by decide)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root p hp
  refine ⟨b, (WeierstrassCurve.Affine.equation_iff _ _).2 ?_⟩
  simp only [p, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hb
  linear_combination hb

private theorem pt_congr {C : Scheme.{u}} (eW : C ≅
    AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.projOf W)
    {x y x' y' : K} {h h'} (hx : x = x') (hy : y = y') :
    EllPts.pt W eW x y h = EllPts.pt W eW x' y' h' := by
  subst hx hy; rfl

end EllPts2

namespace EllInv

attribute [local instance] EllTrSch.isDomain_LB

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass EllTrRing EllTrSch

variable {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) (W : WeierstrassCurve K)
  (eW : C ≅ projOf W)

private theorem tr_tr [DecidableEq K] [W.IsElliptic] (x0 y0 : K) (h0 : W.toAffine.Equation x0 y0)
    (h0' : W.toAffine.Equation x0 (W.toAffine.negY x0 y0)) (a b : K)
    (h : W.toAffine.Equation a b) (ha : a ≠ x0) (ht : tX W x0 y0 a b ≠ x0) :
    tX W x0 (W.toAffine.negY x0 y0) (tX W x0 y0 a b) (tY W x0 y0 a b) = a ∧
      tY W x0 (W.toAffine.negY x0 y0) (tX W x0 y0 a b) (tY W x0 y0 a b) = b := by
  have e1 := add_eq W x0 y0 h0 a b h ha
  have e2 := add_eq W x0 (W.toAffine.negY x0 y0) h0' _ _ (equation_tX_tY W x0 y0 h0 a b h ha) ht
  have e3 : WeierstrassCurve.Affine.Point.some x0 (W.toAffine.negY x0 y0)
      (WeierstrassCurve.Affine.equation_iff_nonsingular.1 h0') =
      -WeierstrassCurve.Affine.Point.some x0 y0
        (WeierstrassCurve.Affine.equation_iff_nonsingular.1 h0) :=
    (WeierstrassCurve.Affine.Point.neg_some _).symm
  rw [e3, ← e1, add_neg_cancel_right] at e2
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at e2
  exact ⟨e2.1.symm, e2.2.symm⟩

private theorem comp_eq_id [IsAlgClosed K] [IsCurve K f] [Smooth f] [IsProper f] [IsIntegral C]
    [W.IsElliptic] (hover : eW.hom ≫ projectionOf W = f) (x0 y0 : K)
    (h0 : W.toAffine.Equation x0 y0) (h0' : W.toAffine.Equation x0 (W.toAffine.negY x0 y0))
    (ρ ρ' : C ⟶ C) (hρf : ρ ≫ f = f) (hρ'f : ρ' ≫ f = f)
    (hρ : ιV W eW x0 ≫ ρ = μ W eW x0 y0 h0)
    (hρ' : ιV W eW x0 ≫ ρ' = μ W eW x0 (W.toAffine.negY x0 y0) h0')
    (hne : (Set.range (ιV W eW x0) ∩ ρ ⁻¹' Set.range (ιV W eW x0)).Nonempty) :
    ρ ≫ ρ' = 𝟙 C := by
  classical
  haveI := isOpenImmersion_ιV W eW x0
  have hSo : IsOpen (Set.range (ιV W eW x0) ∩ ρ ⁻¹' Set.range (ιV W eW x0)) :=
    (ιV W eW x0).isOpenEmbedding.isOpen_range.inter
      ((ιV W eW x0).isOpenEmbedding.isOpen_range.preimage ρ.continuous)
  haveI : LocallyOfFiniteType ((ρ ≫ ρ') ≫ f) := by
    rw [Category.assoc, hρ'f, hρf]; infer_instance
  refine ext_of_apply_eq (K := K) f _ hSo.isLocallyClosed (hSo.dense hne) ?_ ?_
  · rintro z ⟨hz1, hz2⟩ hzc
    obtain ⟨a, b, h, ha, z0, rfl⟩ := exists_pt_of_mem f W eW x0 hover z hzc hz1
    have hz2' : (EllPts.pt W eW _ _ (equation_tX_tY W x0 y0 h0 a b h ha)) z0 ∈
        Set.range (ιV W eW x0) := by
      rw [← pt_ρ W eW x0 y0 h0 ρ hρ a b h ha, Scheme.Hom.comp_apply]; exact hz2
    have ht := ne_of_mem_V W eW x0 _ _ _ z0 hz2'
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, pt_ρ W eW x0 y0 h0 ρ hρ a b h ha,
      pt_ρ W eW x0 _ h0' ρ' hρ' _ _ _ ht]
    obtain ⟨e1, e2⟩ := tr_tr W x0 y0 h0 h0' a b h ha ht
    rw [EllPts2.pt_congr W eW e1 e2 (h' := h)]
    rfl
  · rw [Category.assoc, hρ'f, hρf, Category.id_comp]

private theorem exists_good [IsAlgClosed K] [DecidableEq K] [W.IsElliptic] (x0 y0 : K)
    (h0 : W.toAffine.Equation x0 y0) :
    ∃ a b, ∃ (h : W.toAffine.Equation a b) (ha : a ≠ x0), tX W x0 y0 a b ≠ x0 := by
  let Q := WeierstrassCurve.Affine.Point.some x0 y0
    (WeierstrassCurve.Affine.equation_iff_nonsingular.1 h0)
  let xP2 : K := match -(Q + Q) with
    | WeierstrassCurve.Affine.Point.some x _ _ => x
    | WeierstrassCurve.Affine.Point.zero => x0
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({x0, xP2} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨b, hb⟩ := EllPts2.exists_y W a
  refine ⟨a, b, hb, ha.1, fun ht => ?_⟩
  have e1 := add_eq W x0 y0 h0 a b hb ha.1
  have hX := (WeierstrassCurve.Affine.Point.X_eq_iff
    (h₁ := WeierstrassCurve.Affine.equation_iff_nonsingular.1
      (equation_tX_tY W x0 y0 h0 a b hb ha.1))
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.1 h0)).1 ht
  rw [← e1] at hX
  rcases hX with hX | hX
  · have : WeierstrassCurve.Affine.Point.some a b
        (WeierstrassCurve.Affine.equation_iff_nonsingular.1 hb) = 0 := by
      simpa using hX
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ this
  · have hP : -(Q + Q) = WeierstrassCurve.Affine.Point.some a b
        (WeierstrassCurve.Affine.equation_iff_nonsingular.1 hb) := by
      have hR : WeierstrassCurve.Affine.Point.some a b
          (WeierstrassCurve.Affine.equation_iff_nonsingular.1 hb) = -Q - Q :=
        eq_sub_iff_add_eq.2 hX
      rw [hR]; abel
    apply ha.2
    simp only [xP2, hP]

private theorem μ_congr (x0 : K) {y y' : K} (hy : y = y') (h h') : μ W eW x0 y h =
    μ W eW x0 y' h' := by
  subst hy; rfl

private theorem hne_of_good (x0 y0 : K) (h0 : W.toAffine.Equation x0 y0) (ρ : C ⟶ C)
    (hρ : ιV W eW x0 ≫ ρ = μ W eW x0 y0 h0) (a b : K) (h : W.toAffine.Equation a b) (ha : a ≠ x0)
    (ht : tX W x0 y0 a b ≠ x0) :
    (Set.range (ιV W eW x0) ∩ ρ ⁻¹' Set.range (ιV W eW x0)).Nonempty := by
  obtain ⟨z0⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine ⟨(EllPts.pt W eW a b h) z0, ?_, ?_⟩
  · rw [pt_eq_ιV W eW x0 a b h ha, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
  · show ρ ((EllPts.pt W eW a b h) z0) ∈ Set.range (ιV W eW x0)
    rw [← Scheme.Hom.comp_apply, pt_ρ W eW x0 y0 h0 ρ hρ a b h ha, pt_eq_ιV W eW x0 _ _ _ ht,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

private theorem exists_transIso [IsAlgClosed K] [IsCurve K f] [Smooth f] [IsProper f] [IsIntegral C]
    [W.IsElliptic] (hover : eW.hom ≫ projectionOf W = f) (x0 y0 : K)
    (h0 : W.toAffine.Equation x0 y0) :
    ∃ ρ : C ≅ C, ρ.hom ≫ f = f ∧ ιV W eW x0 ≫ ρ.hom = μ W eW x0 y0 h0 := by
  classical
  have h0' : W.toAffine.Equation x0 (W.toAffine.negY x0 y0) :=
    (WeierstrassCurve.Affine.equation_neg _ _).2 h0
  have h0'' : W.toAffine.Equation x0 (W.toAffine.negY x0 (W.toAffine.negY x0 y0)) :=
    (WeierstrassCurve.Affine.equation_neg _ _).2 h0'
  obtain ⟨ρ, hρf, hρ⟩ := exists_ρ f W eW x0 y0 h0 hover
  obtain ⟨ρ', hρ'f, hρ'⟩ := exists_ρ f W eW x0 _ h0' hover
  have hρ'' : ιV W eW x0 ≫ ρ = μ W eW x0 _ h0'' := by
    rw [hρ]; exact μ_congr W eW x0 (WeierstrassCurve.Affine.negY_negY _ _).symm _ _
  obtain ⟨a, b, h, ha, ht⟩ := exists_good W x0 y0 h0
  obtain ⟨a', b', h', ha', ht'⟩ := exists_good W x0 _ h0'
  have e1 := comp_eq_id f W eW hover x0 y0 h0 h0' ρ ρ' hρf hρ'f hρ hρ'
    (hne_of_good W eW x0 y0 h0 ρ hρ a b h ha ht)
  have e2 := comp_eq_id f W eW hover x0 _ h0' h0'' ρ' ρ hρ'f hρf hρ' hρ''
    (hne_of_good W eW x0 _ h0' ρ' hρ' a' b' h' ha' ht')
  exact ⟨⟨ρ, ρ', e1, e2⟩, hρf, hρ⟩

end EllInv

namespace EllChi

attribute [local instance] EllTrSch.isDomain_LB

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass EllTrRing EllTrSch EllGeo

private theorem appIso_nat {C : Scheme.{u}} {A₁ A₂ : CommRingCat.{u}} (j₁ : Spec A₁ ⟶ C) (j₂ : Spec
    A₂ ⟶ C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (k : C ⟶ C) (φ : A₁ ⟶ A₂)
    (hk : j₂ ≫ k = Spec.map φ ≫ j₁) (h : j₂ ''ᵁ ⊤ ≤ k ⁻¹ᵁ (j₁ ''ᵁ ⊤)) (s : Γ(C, j₁ ''ᵁ ⊤)) :
    ((j₂.appIso ⊤) ≪≫ Scheme.ΓSpecIso A₂).hom ((k.appLE _ _ h).hom s) =
      φ.hom (((j₁.appIso ⊤) ≪≫ Scheme.ΓSpecIso A₁).hom s) := by
  have key : (j₁.appIso ⊤).inv ≫ k.appLE _ _ h ≫ (j₂.appIso ⊤).hom = (Spec.map φ).appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE,
      EllPF.appLE_eq_of_eq hk _ (by simp), Scheme.Hom.comp_appLE,
      Scheme.Hom.appIso_inv_app_assoc]
    erw [Scheme.Hom.map_appLE]
    exact Scheme.Hom.appLE_eq_app _
  obtain ⟨t, rfl⟩ : ∃ t, s = (j₁.appIso ⊤).inv.hom t :=
    ⟨(j₁.appIso ⊤).hom.hom s, by simp⟩
  have h2 := congrArg (fun g => g.hom t) key
  simp only [CommRingCat.comp_apply] at h2
  simp only [Iso.trans_hom, CommRingCat.comp_apply, h2]
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  simp

private theorem chi_trans_eq_one {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
    (e : Scheme.Hom.relativeDifferentials f ≅ SheafOfModules.unit C.ringCatSheaf)
    (W : WeierstrassCurve K) [W.IsElliptic] (eW : C ≅ projOf W)
    (hover : eW.hom ≫ projectionOf W = f) (x0 y0 : K) (h0 : W.toAffine.Equation x0 y0)
    (ρ : C ≅ C) (hρ : ιV W eW x0 ≫ ρ.hom = μ W eW x0 y0 h0) (χ : K)
    (hc : ∀ (U : C.Opens) (a : Γ(C, U)), Dv f e (ρ.hom ⁻¹ᵁ U) ((ρ.hom.app U).hom a) =
      kap f _ χ * (ρ.hom.app U).hom (Dv f e U a)) : χ = 1 := by
  haveI := isOpenImmersion_jC W eW
  haveI := isOpenImmersion_ιV W eW x0
  let j := jC W eW
  let U0 := j ''ᵁ ⊤
  let V := (ιV W eW x0) ''ᵁ ⊤
  let ι0 : Γ(C, U0) ≃+* W.toAffine.CoordinateRing :=
      ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso (.of W.toAffine.CoordinateRing)).commRingCatIsoToRingEquiv
  let ιB : Γ(C, V) ≃+* LB W x0 :=
    (((ιV W eW x0).appIso ⊤) ≪≫ Scheme.ΓSpecIso (.of (LB W x0))).commRingCatIsoToRingEquiv
  have hι0 : ∀ c, ι0 (kap f U0 c) = algebraMap K W.toAffine.CoordinateRing c := fun c =>
    EllPF.appIso_kap f j _ (jC_f f W eW hover) c
  have hιB : ∀ c, ιB (kap f V c) = algebraMap K (LB W x0) c := fun c =>
    EllPF.appIso_kap f (ιV W eW x0) _ (ιV_f f W eW x0 hover) c
  let D0 := EllPF.transDer ι0 (kap f U0) hι0 (Dv f e U0) (Dv_add f e U0) (Dv_mul f e U0)
    (Dv_kap f e U0)
  let DB := EllPF.transDer ιB (kap f V) hιB (Dv f e V) (Dv_add f e V) (Dv_mul f e V)
    (Dv_kap f e V)
  have hU0aff : IsAffineOpen U0 := (isAffineOpen_top _).image_of_isOpenImmersion j
  have hD0 : Ideal.span (Set.range D0) = ⊤ :=
    EllPF.span_transDer ι0 _ hι0 _ _ _ _ (span_Dv_eq_top f e U0 hU0aff)
  obtain ⟨c, hc0, hDx, hDy⟩ := EllAlg.deriv_form W D0 hD0
  have hVρ : V ≤ ρ.hom ⁻¹ᵁ U0 := by
    rintro _ ⟨w, -, rfl⟩
    show ρ.hom ((ιV W eW x0) w) ∈ U0
    rw [← Scheme.Hom.comp_apply, hρ, μ, Scheme.Hom.comp_apply]
    exact ⟨_, trivial, rfl⟩
  have natρ : ∀ s, ιB ((ρ.hom.appLE U0 V hVρ).hom s) = transl W x0 y0 h0 (ι0 s) := fun s =>
    appIso_nat j (ιV W eW x0) ρ.hom (CommRingCat.ofHom (transl W x0 y0 h0)) hρ hVρ s
  have hV1 : V ≤ (𝟙 C) ⁻¹ᵁ U0 := by
    rintro _ ⟨w, -, rfl⟩
    show (ιV W eW x0) w ∈ U0
    rw [ιV, Scheme.Hom.comp_apply]
    exact ⟨_, trivial, rfl⟩
  have nat1 : ∀ s, ιB ((Scheme.Hom.appLE (𝟙 C) U0 V hV1).hom s) =
      algebraMap W.toAffine.CoordinateRing (LB W x0) (ι0 s) := fun s =>
    appIso_nat j (ιV W eW x0) (𝟙 C) (CommRingCat.ofHom (algebraMap W.toAffine.CoordinateRing (LB W
        x0)))
      (by rw [Category.comp_id]; rfl) hV1 s
  -- `DB` on the image of `A`
  have hDB1 : ∀ a, DB (algebraMap W.toAffine.CoordinateRing (LB W x0) a) =
      algebraMap W.toAffine.CoordinateRing (LB W x0) (D0 a) := by
    intro a
    have h1 : ιB.symm (algebraMap W.toAffine.CoordinateRing (LB W x0) a) =
        (Scheme.Hom.appLE (𝟙 C) U0 V hV1).hom (ι0.symm a) := by
      rw [RingEquiv.symm_apply_eq, nat1, RingEquiv.apply_symm_apply]
    simp only [DB, D0, EllPF.transDer_apply, h1]
    rw [Dv_appLE, Scheme.Hom.id_app]
    rw [← nat1]
    congr 1
  -- `DB` on the image of `transl`
  have hDBT : ∀ a, DB (transl W x0 y0 h0 a) =
      algebraMap K (LB W x0) χ * transl W x0 y0 h0 (D0 a) := by
    intro a
    have h1 : ιB.symm (transl W x0 y0 h0 a) = (ρ.hom.appLE U0 V hVρ).hom (ι0.symm a) := by
      rw [RingEquiv.symm_apply_eq, natρ, RingEquiv.apply_symm_apply]
    simp only [DB, D0, EllPF.transDer_apply, h1]
    rw [Dv_appLE, hc, map_mul, kap_res, map_mul, hιB, appLE_eq_res, natρ]
  have hκ : ∀ c,
      algebraMap W.toAffine.CoordinateRing (LB W x0) (algebraMap K W.toAffine.CoordinateRing c) =
      algebraMap K (LB W x0) c := fun c =>
    (IsScalarTower.algebraMap_apply K W.toAffine.CoordinateRing (LB W x0) c).symm
  have hXB : DB (algebraMap W.toAffine.CoordinateRing (LB W x0) (EllAlg.xA W)) =
      algebraMap K (LB W x0) c * (2 * algebraMap W.toAffine.CoordinateRing (LB W x0) (EllAlg.yA W) +
        algebraMap K (LB W x0) W.a₁ *
            algebraMap W.toAffine.CoordinateRing (LB W x0) (EllAlg.xA W) +
            algebraMap K (LB W x0) W.a₃) := by
    change DB _ = _
    rw [hDB1, hDx]; simp only [map_mul, map_add, map_ofNat, hκ]
  have hYB : DB (algebraMap W.toAffine.CoordinateRing (LB W x0) (EllAlg.yA W)) =
      -(algebraMap K (LB W x0) c * (algebraMap K (LB W x0) W.a₁ *
          algebraMap W.toAffine.CoordinateRing (LB W x0) (EllAlg.yA W) -
        3 * algebraMap W.toAffine.CoordinateRing (LB W x0) (EllAlg.xA W) ^ 2 - 2 *
            algebraMap K (LB W x0) W.a₂ *
            algebraMap W.toAffine.CoordinateRing (LB W x0) (EllAlg.xA W) -
          algebraMap K (LB W x0) W.a₄)) := by
    change DB _ = _
    rw [hDB1, hDy]; simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, hκ]; ring
  have hk0 : ∀ z : K, DB (algebraMap K (LB W x0) z) = 0 := fun z =>
    DB.map_algebraMap z
  obtain ⟨hTx, hTy⟩ := EllTr.tr_der DB _ _ _ _ _ _ _ _ _ _ _ (weierstrass_xy_eq_zero W x0)
    (weierstrass_base_eq_zero W x0 y0 h0) (sub_mul_Gi_sub_one W x0)
    ⟨hk0 _, hk0 _, hk0 _, hk0 _, hk0 _, hk0 _, hk0 _, hk0 c⟩ hXB hYB
  have hTDx : transl W x0 y0 h0 (D0 (EllAlg.xA W)) = algebraMap K (LB W x0) c *
      (2 * Yt W x0 y0 + algebraMap K (LB W x0) W.a₁ * Xt W x0 y0 + algebraMap K (LB W x0) W.a₃) :=
          by
    rw [hDx]; simp only [map_mul, map_add, map_ofNat, transl_algebraMap, transl_x, transl_y]
  have hTDy : transl W x0 y0 h0 (D0 (EllAlg.yA W)) = -(algebraMap K (LB W x0) c *
      (algebraMap K (LB W x0) W.a₁ * Yt W x0 y0 - 3 * Xt W x0 y0 ^ 2 -
        2 * algebraMap K (LB W x0) W.a₂ * Xt W x0 y0 - algebraMap K (LB W x0) W.a₄)) := by
    rw [hDy]
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, transl_algebraMap, transl_x,
      transl_y]
    ring
  have ex := hDBT (EllAlg.xA W)
  have ey := hDBT (EllAlg.yA W)
  rw [transl_x] at ex
  rw [transl_y] at ey
  change DB (Xt W x0 y0) = _ at ex
  change DB (Yt W x0 y0) = _ at ey
  rw [Xt, hTx, ← Xt, ← Yt, ← hTDx] at ex
  rw [Yt, hTy, ← Xt, ← Yt, ← hTDy] at ey
  by_contra hχ
  have hu : algebraMap K (LB W x0) (1 - χ) ≠ 0 := by
    rw [ne_eq,
        map_eq_zero_iff _ (algebraMap K (LB W x0)).injective]; exact sub_ne_zero.2 (Ne.symm hχ)
  have hx0 : transl W x0 y0 h0 (D0 (EllAlg.xA W)) = 0 := by
    have : algebraMap K (LB W x0) (1 - χ) * transl W x0 y0 h0 (D0 (EllAlg.xA W)) = 0 := by
      rw [map_sub, map_one]; linear_combination ex
    exact (mul_eq_zero.1 this).resolve_left hu
  have hy0 : transl W x0 y0 h0 (D0 (EllAlg.yA W)) = 0 := by
    have : algebraMap K (LB W x0) (1 - χ) * transl W x0 y0 h0 (D0 (EllAlg.yA W)) = 0 := by
      rw [map_sub, map_one]; linear_combination ey
    exact (mul_eq_zero.1 this).resolve_left hu
  have hc' : algebraMap K (LB W x0) c ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap K (LB W x0)).injective]; exact hc0
  rw [hTDx] at hx0
  rw [hTDy, neg_eq_zero] at hy0
  have hfy := (mul_eq_zero.1 hx0).resolve_left hc'
  have hfx := (mul_eq_zero.1 hy0).resolve_left hc'
  obtain ⟨Bx, By, hΔ⟩ := EllAlg.jacobian W
  have hTΔ := congrArg (transl W x0 y0 h0) hΔ
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, transl_algebraMap, transl_x,
    transl_y] at hTΔ
  have hΔ0 : algebraMap K (LB W x0) W.Δ = 0 := by
    rw [hTΔ]; linear_combination (transl W x0 y0 h0 Bx) * hfx + (transl W x0 y0 h0 By) * hfy
  rw [map_eq_zero_iff _ (algebraMap K (LB W x0)).injective] at hΔ0
  exact (WeierstrassCurve.IsElliptic.isUnit (W := W)).ne_zero hΔ0

end EllChi

namespace EllGrp

open WeierstrassCurve.Affine

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

private theorem exists_two_torsion [IsAlgClosed K] [CharZero K] [W.IsElliptic] :
    ∃ T : W.toAffine.Point, T ≠ 0 ∧ -T = T := by
  let p : Polynomial K := 4 * Polynomial.X ^ 3 + Polynomial.C W.b₂ * Polynomial.X ^ 2 +
    Polynomial.C (2 * W.b₄) * Polynomial.X + Polynomial.C W.b₆
  have hp : p.degree ≠ 0 := by
    have : p.natDegree = 3 := by simp only [p]; compute_degree!
    intro h; rw [Polynomial.degree_eq_natDegree (by intro h'; simp [h'] at this), this] at h
    exact absurd h (by decide)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p hp
  simp only [p, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat] at hx
  set y := -(W.a₁ * x + W.a₃) / 2 with hy
  have hE : W.toAffine.Equation x y := by
    rw [equation_iff]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hx
    rw [hy]; field_simp; linear_combination -hx
  have hN := equation_iff_nonsingular.1 hE
  refine ⟨Point.some x y hN, Point.some_ne_zero _, ?_⟩
  rw [Point.neg_some]
  congr 1
  rw [negY, hy]; field_simp; ring

private theorem infinite_points [IsAlgClosed K] [W.IsElliptic] : Infinite W.toAffine.Point := by
  classical
  have hy := fun a => EllPts2.exists_y W a
  let F : K → W.toAffine.Point := fun a =>
    Point.some a (Classical.choose (hy a)) (equation_iff_nonsingular.1 (Classical.choose_spec (hy
        a)))
  refine Infinite.of_injective F (fun a a' h => ?_)
  simp only [F, Point.some.injEq] at h
  exact h.1

end EllGrp

namespace EllChoice

private theorem exists_good_P {G : Type*} [AddCommGroup G] [Infinite G] (s t : G → G)
    (hst : ∀ P, s (t P) = P) (T₂ : G) (hT : T₂ ≠ 0) (hT' : -T₂ = T₂) :
    ∃ P, P ≠ 0 ∧ s P ≠ 0 ∧ s P + s P ≠ P := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨P', hP'⟩ := Infinite.exists_notMem_finset ({0, T₂, s 0, s 0 - T₂} : Finset G)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hP'
  obtain ⟨h1, h2, h3, h4⟩ := hP'
  have ha0 : t P' ≠ 0 := fun h => h3 (by rw [← hst P', h])
  have ha := hcon (t P') ha0 (by rw [hst]; exact h1)
  rw [hst] at ha
  have hb0 : t (P' + T₂) ≠ 0 := fun h => h4 (by
    have := hst (P' + T₂); rw [h] at this; rw [this]; abel)
  have hb1 : P' + T₂ ≠ 0 := fun h => h2 (by
    have : P' = -T₂ := eq_neg_of_add_eq_zero_left h
    rw [this, hT'])
  have hb := hcon (t (P' + T₂)) hb0 (by rw [hst]; exact hb1)
  rw [hst] at hb
  have hTT : T₂ + T₂ = 0 := by
    calc T₂ + T₂ = T₂ + -T₂ := by rw [hT']
      _ = 0 := add_neg_cancel T₂
  have hab : t P' = t (P' + T₂) := by
    rw [← ha, ← hb]
    calc P' + P' = P' + P' + (T₂ + T₂) := by rw [hTT, add_zero]
      _ = P' + T₂ + (P' + T₂) := by abel
  have := congrArg s hab
  rw [hst, hst] at this
  exact hT (by
    have h := congrArg (· - P') this
    simp at h
    exact h.symm)

end EllChoice

namespace EllNF

attribute [local instance] EllTrSch.isDomain_LB

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass EllGeo

private theorem chi_pow_of_no_fixed_point {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {C :
    Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
    (h0 : Module.finrank K (structureSheafCohomology f 0) = 1) (hg : genus f = 1)
    (hfr : Module.finrank K (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward f).obj (Scheme.Hom.relativeDifferentials f))) = 1)
    (e : Scheme.Hom.relativeDifferentials f ≅ SheafOfModules.unit C.ringCatSheaf)
    (σ : C ≅ C) (hσ : σ.hom ≫ f = f) (χ : K)
    (hc : ∀ (U : C.Opens) (a : Γ(C, U)), Dv f e (σ.hom ⁻¹ᵁ U) ((σ.hom.app U).hom a) =
      kap f _ χ * (σ.hom.app U).hom (Dv f e U a))
    (hnofix : ∀ p : Spec (.of K) ⟶ C, p ≫ f = 𝟙 _ → p ≫ σ.hom ≠ p) :
    χ ^ 4 = 1 ∨ χ ^ 6 = 1 := by
  classical
  haveI := smoothOfRelativeDimension_one_of_isCurve K f
  haveI : IsIntegral C := GenusOne.isIntegral f h0
  obtain ⟨o, ho⟩ := GenusOne.exists_section_of_isAlgClosed f
  obtain ⟨W, hW, eW, hover, hzero⟩ := EllW.exists_weierstrassCurve_iso f h0 hg o ho
  let s : W.toAffine.Point → (Spec (.of K) ⟶ C) := fun P => match P with
    | .zero => o
    | .some x y h => EllPts.pt W eW x y h.1
  have hs_sect : ∀ P, s P ≫ f = 𝟙 _ := by
    rintro (_ | ⟨x, y, h⟩)
    · exact ho
    · exact EllPts.pt_comp W f eW hover x y h.1
  have hs_surj : ∀ p, p ≫ f = 𝟙 _ → ∃ P, s P = p := by
    intro p hp
    rcases EllPts.sect_cases W f eW hover o hzero p hp with rfl | ⟨x, y, h, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨.some x y (WeierstrassCurve.Affine.equation_iff_nonsingular.1 h), rfl⟩
  have hs_inj : Function.Injective s := by
    rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hst
    · rfl
    · exact absurd hst.symm (EllPts.pt_ne W eW o hzero x' y' h'.1)
    · exact absurd hst (EllPts.pt_ne W eW o hzero x y h.1)
    · obtain ⟨rfl, rfl⟩ := EllPts.pt_inj W eW hst; rfl
  have hσinv : σ.inv ≫ f = f := by
    calc σ.inv ≫ f = σ.inv ≫ σ.hom ≫ f := by rw [hσ]
      _ = f := Iso.inv_hom_id_assoc _ _
  have hσsect : ∀ P, (s P ≫ σ.hom) ≫ f = 𝟙 _ := fun P => by rw [Category.assoc, hσ, hs_sect]
  have hσsect' : ∀ P, (s P ≫ σ.inv) ≫ f = 𝟙 _ := fun P => by
    rw [Category.assoc, hσinv, hs_sect]
  let sσ : W.toAffine.Point → W.toAffine.Point := fun P =>
    Classical.choose (hs_surj _ (hσsect P))
  have hsσ : ∀ P, s (sσ P) = s P ≫ σ.hom := fun P => Classical.choose_spec (hs_surj _ (hσsect P))
  let tσ : W.toAffine.Point → W.toAffine.Point := fun P =>
    Classical.choose (hs_surj _ (hσsect' P))
  have htσ : ∀ P, s (tσ P) = s P ≫ σ.inv := fun P =>
    Classical.choose_spec (hs_surj _ (hσsect' P))
  have hst : ∀ P, sσ (tσ P) = P := fun P => hs_inj (by
    rw [hsσ, htσ, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  haveI := EllGrp.infinite_points W
  obtain ⟨T₂, hT₂, hT₂'⟩ := EllGrp.exists_two_torsion W
  obtain ⟨P, hP0, hR0, hRR⟩ := EllChoice.exists_good_P sσ tσ hst T₂ hT₂ hT₂'
  have hPR : sσ P ≠ P := fun h => hnofix (s P) (hs_sect P) (by rw [← hsσ, h])
  obtain ⟨xR, yR, hRn, hR⟩ : ∃ x y h, sσ P = WeierstrassCurve.Affine.Point.some x y h := by
    rcases hRP : sσ P with _ | ⟨x, y, h⟩
    · exact absurd hRP hR0
    · exact ⟨x, y, h, rfl⟩
  obtain ⟨x0, y0, hQn, hQ⟩ : ∃ x y h, P - sσ P = WeierstrassCurve.Affine.Point.some x y h := by
    rcases hQP : P - sσ P with _ | ⟨x, y, h⟩
    · exact absurd (sub_eq_zero.1 hQP).symm hPR
    · exact ⟨x, y, h, rfl⟩
  have hx : xR ≠ x0 := by
    intro hxx
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := hRn) (h₂ := hQn)).1 hxx with h | h
    · rw [← hR, ← hQ] at h
      exact hRR (eq_sub_iff_add_eq.1 h)
    · rw [← hR, ← hQ, neg_sub] at h
      exact hP0 (sub_eq_self.1 h.symm)
  obtain ⟨ρ, hρf, hρ⟩ := EllInv.exists_transIso f W eW hover x0 y0 hQn.1
  have hρpt : s (sσ P) ≫ ρ.hom = s P := by
    have hadd := EllTrRing.add_eq W x0 y0 hQn.1 xR yR hRn.1 hx
    have hP : WeierstrassCurve.Affine.Point.some _ _
        (WeierstrassCurve.Affine.equation_iff_nonsingular.1
          (EllTrRing.equation_tX_tY W x0 y0 hQn.1 xR yR hRn.1 hx)) = P := by
      rw [← hadd]
      have e1 : WeierstrassCurve.Affine.Point.some xR yR
          (WeierstrassCurve.Affine.equation_iff_nonsingular.1 hRn.1) = sσ P := by rw [hR]
      have e2 : WeierstrassCurve.Affine.Point.some x0 y0
          (WeierstrassCurve.Affine.equation_iff_nonsingular.1 hQn.1) = P - sσ P := by rw [hQ]
      rw [e1, e2]; abel
    rw [hR]
    change EllPts.pt W eW xR yR hRn.1 ≫ ρ.hom = s P
    rw [EllTrSch.pt_ρ W eW x0 y0 hQn.1 ρ.hom hρ xR yR hRn.1 hx, ← hP]
  obtain ⟨χρ, hχρ⟩ := exists_Tm_eq_smul f ρ hρf hfr
  have hcρ := equivariance f e ρ hρf χρ hχρ
  have hχρ1 := EllChi.chi_trans_eq_one f e W eW hover x0 y0 hQn.1 ρ hρ χρ hcρ
  rw [hχρ1] at hcρ
  let ψ := σ ≪≫ ρ
  have hψf : ψ.hom ≫ f = f := by simp only [ψ, Iso.trans_hom, Category.assoc, hρf, hσ]
  have hψfix : s P ≫ ψ.hom = s P := by
    simp only [ψ, Iso.trans_hom, ← Category.assoc, ← hsσ, hρpt]
  have hcψ : ∀ (U : C.Opens) (a : Γ(C, U)), Dv f e (ψ.hom ⁻¹ᵁ U) ((ψ.hom.app U).hom a) =
      kap f _ χ * (ψ.hom.app U).hom (Dv f e U a) := by
    intro U a
    show Dv f e (σ.hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) ((σ.hom.app (ρ.hom ⁻¹ᵁ U)).hom ((ρ.hom.app U).hom a)) =
      kap f (σ.hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) χ *
        (σ.hom.app (ρ.hom ⁻¹ᵁ U)).hom ((ρ.hom.app U).hom (Dv f e U a))
    rw [hc, hcρ, kap_one, one_mul]
  obtain ⟨W', hW', eW', hover', hzero'⟩ :=
    EllW.exists_weierstrassCurve_iso f h0 hg (s P) (hs_sect P)
  exact EllPF.chi_pow_of_fixed_point f e W' eW' hover' (s P) hzero' ψ hψf hψfix χ hcψ

end EllNF

namespace EllMain

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass EllGeo

private theorem isTrivial_of_finrank_pos_of_invertibleCurveDegree_nonpos
    {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsProper f] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.property L]
    (hpos : 0 < Module.finrank K (cohomologyOverField K f L 0))
    (hdeg : invertibleCurveDegree K f hdim L ≤ 0) :
    SheafOfModules.IsTrivial C.presheaf C.ringCatSheaf.property L := by
  have := Module.nontrivial_of_finrank_pos hpos
  have := (cohomologyOverFieldZeroEquivSections K f L).injective.nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : Γ(L, ⊤))
  letI : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    inferInstanceAs (SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.property L)
  exact isTrivial_of_invertibleCurveDegree_nonpos K f hdim L
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf L t)
    (ne_of_eq_of_ne (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top L t) ht) hdeg

private theorem isTrivial_relativeDifferentials_of_genus_eq_one
    {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f]
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (hg : genus f = 1) :
    SheafOfModules.IsTrivial C.presheaf C.ringCatSheaf.property
      (Scheme.Hom.relativeDifferentials f) := by
  have := smoothOfRelativeDimension_one_of_isCurve K f
  have := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
  have : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Scheme.Hom.relativeDifferentials f) :=
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one C.toRingedSpace _
  have hdeg := curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two f
  refine isTrivial_of_finrank_pos_of_invertibleCurveDegree_nonpos f
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le _ ?_ ?_
  · rw [finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus, hg]; exact one_pos
  · rw [invertibleCurveDegree_eq_curveDegree, hdeg, hg]
    norm_num

private theorem main {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (hg : genus f = 1)
    (hfr : Module.finrank K (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward f).obj (Scheme.Hom.relativeDifferentials f))) = 1)
    (σ : C ≅ C) (hσ : σ.hom ≫ f = f) :
    ∃ χ : K, (χ ^ 4 = 1 ∨ χ ^ 6 = 1) ∧ ∀ ω, (Tm f σ hσ).hom ω = χ • ω := by
  have := smoothOfRelativeDimension_one_of_isCurve K f
  have h0 := GenusOne.finrank_structureSheafCohomology_zero_of_isAlgClosed f
  obtain ⟨e⟩ := isTrivial_relativeDifferentials_of_genus_eq_one f hg
  let e' : Scheme.Hom.relativeDifferentials f ≅ SheafOfModules.unit C.ringCatSheaf := e
  obtain ⟨χ, hT⟩ := exists_Tm_eq_smul f σ hσ hfr
  refine ⟨χ, ?_, hT⟩
  have hc := equivariance f e' σ hσ χ hT
  by_cases hfix : ∃ p : Spec (.of K) ⟶ C, p ≫ f = 𝟙 _ ∧ p ≫ σ.hom = p
  · obtain ⟨p, hp, hpf⟩ := hfix
    obtain ⟨W, hW, eW, hover, hzero⟩ := EllW.exists_weierstrassCurve_iso f h0 hg p hp
    exact EllPF.chi_pow_of_fixed_point f e' W eW hover p hzero σ hσ hpf χ hc
  · simp only [not_exists, not_and] at hfix
    exact EllNF.chi_pow_of_no_fixed_point f h0 hg hfr e' σ hσ χ hc hfix

end EllMain

namespace EllPow

open Opposite Stacks.SheafOfModules.OnSpace

/-- The adjoint transpose of `comparison ≫ (P ⊗ Q)` on a local pure tensor. -/
private theorem homEquiv_comparison_tensorHom_tmul {C : Scheme.{u}} (σ : C ⟶ C)
    (A B M N : C.Modules) (P : (Scheme.Modules.pullback σ).obj A ⟶ M)
    (Q : (Scheme.Modules.pullback σ).obj B ⟶ N) (U : C.Opens) (a : A.val.obj (op U))
    (b : B.val.obj (op U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction σ).homEquiv _ _
      (Stacks.RingedSpace.comparison σ.toLRSHom.toShHom A B ≫ (P ⊗ₘ Q))).val.app (op U)).hom
        (tensorObjTmul C.toRingedSpace A B (op U) a b) =
    tensorObjTmul C.toRingedSpace M N (op (σ ⁻¹ᵁ U))
      ((((Scheme.Modules.pullbackPushforwardAdjunction σ).homEquiv _ _ P).val.app (op U)).hom a)
      ((((Scheme.Modules.pullbackPushforwardAdjunction σ).homEquiv _ _ Q).val.app (op U)).hom
        b) := by
  have h0 := Stacks.RingedSpace.homEquiv_val_app σ.toLRSHom.toShHom _ _
    (Stacks.RingedSpace.comparison σ.toLRSHom.toShHom A B ≫ (P ⊗ₘ Q)) (op U)
    (tensorObjTmul C.toRingedSpace A B (op U) a b)
  have h0' := Stacks.RingedSpace.homEquiv_val_app σ.toLRSHom.toShHom _ _
    (Stacks.RingedSpace.comparison σ.toLRSHom.toShHom A B) (op U)
    (tensorObjTmul C.toRingedSpace A B (op U) a b)
  have h1 := Stacks.RingedSpace.comparison_homEquiv_unit_tmul σ.toLRSHom.toShHom A B (op U) a b
  have h2 := tensorHom_tmul C.toRingedSpace P Q (op (σ ⁻¹ᵁ U))
    (Stacks.RingedSpace.pullbackUnit σ.toLRSHom.toShHom A (op U) a)
    (Stacks.RingedSpace.pullbackUnit σ.toLRSHom.toShHom B (op U) b)
  refine h0.trans ?_
  refine (sheaf_comp_app_apply C.toRingedSpace _ _ _ _).trans ?_
  erw [← h0', h1]
  exact h2

/-- The adjoint transpose of the unit comparison is the structure map on sections. -/
private theorem homEquiv_pullbackUnitIso_apply {C : Scheme.{u}} (σ : C ⟶ C) (U : C.Opens)
    (r : Γ(C, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction σ).homEquiv _ _
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso σ.toLRSHom.toShHom).hom).val.app
        (op U)).hom
        r = (σ.app U).hom r := by
  change (((Scheme.Modules.pullbackPushforwardAdjunction σ).homEquiv _ _
    (((SheafOfModules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceModuleAdjunction.structureSheafHom σ.toLRSHom.toShHom)))).val.app
          (op U)).hom r = _
  erw [Equiv.apply_symm_apply]
  rfl

variable {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
  (e : Scheme.Hom.relativeDifferentials f ≅ SheafOfModules.unit C.ringCatSheaf)

/-- The trivialisation `ω^{⊗n} ≅ 𝒪_C` induced by a trivialisation of `ω`. -/
private noncomputable def trivPow : (n : ℕ) →
    (Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n ≅ 𝟙_ C.Modules)
  | 0 => Iso.refl _
  | n + 1 => (trivPow n ⊗ᵢ e) ≪≫ λ_ (𝟙_ C.Modules)

private theorem trivPow_succ_hom_tmul (n : ℕ) (U : C.Opens)
    (x : (Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n).val.obj
      (op U))
    (y : (Scheme.Hom.relativeDifferentials f).val.obj (op U)) :
    @id Γ(C, U) (((trivPow f e (n + 1)).hom.val.app (op U)).hom
      (tensorObjTmul C.toRingedSpace _ _ (op U) x y)) =
      @id Γ(C, U) (((trivPow f e n).hom.val.app (op U)).hom x) *
        @id Γ(C, U) ((e.hom.val.app (op U)).hom y) := by
  have h1 := tensorHom_tmul C.toRingedSpace (trivPow f e n).hom e.hom (op U) x y
  have h2 := leftUnitor_tmul C.toRingedSpace (𝟙_ C.Modules) (op U)
    (((trivPow f e n).hom.val.app (op U)).hom x) ((e.hom.val.app (op U)).hom y)
  exact (congrArg (fun z => ((λ_ (𝟙_ C.Modules)).hom.val.app (op U)).hom z) h1).trans h2

private theorem trivPow_succ_inv_one (n : ℕ) (U : C.Opens) :
    ((trivPow f e (n + 1)).inv.val.app (op U)).hom (1 : Γ(C, U)) =
      tensorObjTmul C.toRingedSpace _ _ (op U)
        (((trivPow f e n).inv.val.app (op U)).hom (1 : Γ(C, U)))
        ((e.inv.val.app (op U)).hom (1 : Γ(C, U))) := by
  have h1 := Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply C.toRingedSpace (𝟙_ C.Modules)
    (op U) (1 : Γ(C, U))
  have h2 := tensorHom_tmul C.toRingedSpace (trivPow f e n).inv e.inv (op U)
    (unitSection C.toRingedSpace (op U) 1) (1 : Γ(C, U))
  exact (congrArg (fun z => (((trivPow f e n).inv ⊗ₘ e.inv).val.app (op U)).hom z) h1).trans h2

open EllipticDifferentialCharacter.EllGeo in
private theorem trivPow_conj_inv_one (σ : C ≅ C) (hσ : σ.hom ≫ f = f)
    (ψ : (n : ℕ) → (Scheme.Modules.pullback σ.hom).obj
        (Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n) ⟶
      Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n)
    (h0 : ψ 0 = (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso σ.hom.toLRSHom.toShHom).hom)
    (hs : ∀ n, ψ (n + 1) = Stacks.RingedSpace.comparison σ.hom.toLRSHom.toShHom _ _ ≫
      (ψ n ⊗ₘ Scheme.Hom.relativeDifferentialsMap σ.hom f f (𝟙 _)
        (hσ.trans (Category.comp_id f).symm)))
    (χ : K)
    (hφ : @id Γ(C, ⊤) ((e.hom.val.app (op ⊤)).hom (((th f σ hσ).val.app (op ⊤)).hom
      ((e.inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))) = kTop f χ) (n : ℕ) :
    @id Γ(C, ⊤) (((trivPow f e n).hom.val.app (op ⊤)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _ (ψ n)).val.app
        (op ⊤)).hom (((trivPow f e n).inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))) =
      kTop f (χ ^ n) := by
  induction n with
  | zero =>
    rw [h0, pow_zero]
    refine (homEquiv_pullbackUnitIso_apply σ.hom ⊤ 1).trans ?_
    rw [map_one]
    simp [kTop]
    rfl
  | succ n ih =>
    rw [hs n, trivPow_succ_inv_one]
    have a2 := homEquiv_comparison_tensorHom_tmul σ.hom _ _ _ _ (ψ n)
      (Scheme.Hom.relativeDifferentialsMap σ.hom f f (𝟙 _) (hσ.trans (Category.comp_id f).symm))
      ⊤ (((trivPow f e n).inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤)))
      ((e.inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤)))
    have a3 := trivPow_succ_hom_tmul f e n (σ.hom ⁻¹ᵁ ⊤)
      ((((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _ (ψ n)).val.app
        (op ⊤)).hom (((trivPow f e n).inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))
      (((th f σ hσ).val.app (op ⊤)).hom ((e.inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))
    erw [a2]
    refine a3.trans ?_
    erw [ih, hφ]
    exact (show kTop f (χ ^ (n + 1)) = kTop f (χ ^ n) * kTop f χ by
      simp [kTop, pow_succ]).symm

/-- An automorphism over `K` fixes the constants. -/
private theorem app_top_kTop (σ : C ≅ C) (hσ : σ.hom ≫ f = f) (c : K) :
    (σ.hom.app ⊤).hom (EllipticDifferentialCharacter.EllGeo.kTop f c) =
      EllipticDifferentialCharacter.EllGeo.kTop f c := by
  have h : (σ.hom ≫ f).appTop = f.appTop := by rw [hσ]
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of K)).inv c)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
  exact this

private theorem trivPow_inv_hom (n : ℕ)
    (x : (Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n).val.obj
      (op ⊤)) :
    ((trivPow f e n).inv.val.app (op ⊤)).hom (((trivPow f e n).hom.val.app (op ⊤)).hom x) = x :=
  ((PresheafOfModules.evaluation _ (op ⊤)).mapIso
    ((SheafOfModules.forget _).mapIso (trivPow f e n))).hom_inv_id_apply x

open EllipticDifferentialCharacter.EllGeo in
private theorem homEquiv_app_top_eq_self [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]
    (σ : C ≅ C) (hσ : σ.hom ≫ f = f)
    (ψ : (n : ℕ) → (Scheme.Modules.pullback σ.hom).obj
        (Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n) ⟶
      Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n)
    (h0 : ψ 0 = (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso σ.hom.toLRSHom.toShHom).hom)
    (hs : ∀ n, ψ (n + 1) = Stacks.RingedSpace.comparison σ.hom.toLRSHom.toShHom _ _ ≫
      (ψ n ⊗ₘ Scheme.Hom.relativeDifferentialsMap σ.hom f f (𝟙 _)
        (hσ.trans (Category.comp_id f).symm)))
    (χ : K)
    (hφ : @id Γ(C, ⊤) ((e.hom.val.app (op ⊤)).hom (((th f σ hσ).val.app (op ⊤)).hom
      ((e.inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))) = kTop f χ) (n : ℕ) (hn : χ ^ n = 1)
    (s : (Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n).val.obj
      (op ⊤)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _ (ψ n)).val.app
      (op ⊤)).hom s = s := by
  have hT := trivPow_conj_inv_one f e σ hσ ψ h0 hs χ hφ n
  rw [hn] at hT
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)).2 (((trivPow f e n).hom.val.app (op ⊤)).hom s)
  let r : C.ringCatSheaf.obj.obj (op ⊤) := kTop f c
  have hsg : s = r • ((trivPow f e n).inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤)) := by
    refine (trivPow_inv_hom f e n s).symm.trans
      ((congrArg ((trivPow f e n).inv.val.app (op ⊤)).hom ?_).trans
      (((trivPow f e n).inv.val.app (op ⊤)).hom.map_smul r _))
    exact hc.symm.trans (mul_one r).symm
  have hTs : (((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _ (ψ n)).val.app
      (op ⊤)).hom s = r •
      (@id ((Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n).val.obj
        (op ⊤)) ((((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _
        (ψ n)).val.app (op ⊤)).hom (((trivPow f e n).inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))) := by
    rw [hsg]
    refine ((((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _
        (ψ n)).val.app (op ⊤)).hom.map_smul r _).trans ?_
    have := congrArg (fun x : C.ringCatSheaf.obj.obj (op ⊤) => x •
      (@id ((Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n).val.obj
        (op ⊤)) ((((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _
        (ψ n)).val.app (op ⊤)).hom (((trivPow f e n).inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))))
      (app_top_kTop f σ hσ c)
    exact this
  have h1 : ((trivPow f e n).hom.val.app (op ⊤)).hom
      (@id ((Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n).val.obj
        (op ⊤)) ((((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _
        (ψ n)).val.app (op ⊤)).hom (((trivPow f e n).inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))) =
        (1 : Γ(C, ⊤)) :=
    hT.trans (by simp [kTop])
  refine (trivPow_inv_hom f e n _).symm.trans
    ((congrArg ((trivPow f e n).inv.val.app (op ⊤)).hom ?_).trans (trivPow_inv_hom f e n s))
  refine (congrArg ((trivPow f e n).hom.val.app (op ⊤)).hom hTs).trans ?_
  refine (((trivPow f e n).hom.val.app (op ⊤)).hom.map_smul r _).trans ?_
  exact (congrArg (r • ·) h1).trans ((mul_one r).trans hc)

end EllPow

end EllipticDifferentialCharacter

open EllipticDifferentialCharacter EllipticDifferentialCharacter.EllGeo
  EllipticDifferentialCharacter.EllPow Opposite in
/-- **The differential character of an automorphism of a genus-one curve.** Let `f : C ⟶ Spec K`
be a smooth connected proper curve of genus one over an algebraically closed field `K` of
characteristic zero. Then `H⁰(C, Ω¹_{C/K})` is one-dimensional over `K`; every automorphism
`σ` of `C` over `K` acts on it by pullback of differentials as multiplication by a scalar `χ`
with `χ ^ 4 = 1` or `χ ^ 6 = 1`; and the induced action of `σ` on `H⁰(C, ω_C^{⊗12})`, the
`12`-th tensor power of the pullback of differentials, is the identity. -/
@[mmp "lem_mmp_surface_elliptic_differential_character"]
public theorem finrank_eq_one_and_exists_smul_of_genus_eq_one
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f] [ConnectedSpace C]
    (hg : genus f = 1) :
    Module.finrank K (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward f).obj (Scheme.Hom.relativeDifferentials f))) = 1 ∧
      (∀ (σ : C ≅ C) (hσ : σ.hom ≫ f = f), ∃ χ : K, (χ ^ 4 = 1 ∨ χ ^ 6 = 1) ∧
        ∀ ω : moduleSpecΓFunctor.obj
            ((Scheme.Modules.pushforward f).obj (Scheme.Hom.relativeDifferentials f)),
          (moduleSpecΓFunctor.map
              ((Scheme.Modules.pushforward f).map
                  ((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _
                    (Scheme.Hom.relativeDifferentialsMap σ.hom f f (𝟙 _)
                      (hσ.trans (Category.comp_id f).symm))) ≫
                (Scheme.Modules.pushforwardComp σ.hom f).hom.app _ ≫
                (Scheme.Modules.pushforwardCongr hσ).hom.app _)).hom ω = χ • ω) ∧
      ∀ (σ : C ≅ C) (hσ : σ.hom ≫ f = f)
        (ψ : (n : ℕ) → (Scheme.Modules.pullback σ.hom).obj
            (Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n) ⟶
          Intersection.Scheme.Modules.tensorPow (Scheme.Hom.relativeDifferentials f) n),
        ψ 0 = (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso σ.hom.toLRSHom.toShHom).hom →
        (∀ n, ψ (n + 1) = Stacks.RingedSpace.comparison σ.hom.toLRSHom.toShHom _ _ ≫
          (ψ n ⊗ₘ Scheme.Hom.relativeDifferentialsMap σ.hom f f (𝟙 _)
            (hσ.trans (Category.comp_id f).symm))) →
        moduleSpecΓFunctor.map
            ((Scheme.Modules.pushforward f).map
                ((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _ (ψ 12)) ≫
              (Scheme.Modules.pushforwardComp σ.hom f).hom.app _ ≫
              (Scheme.Modules.pushforwardCongr hσ).hom.app _) = 𝟙 _ := by
  have := isIso_appTop_of_isAlgClosed f
  have hfr := finrank_globalSections_relativeDifferentials f hg
  refine ⟨hfr, fun σ hσ => EllMain.main f hg hfr σ hσ, ?_⟩
  intro σ hσ ψ h0 hs
  obtain ⟨χ, hχ, hT⟩ := EllMain.main f hg hfr σ hσ
  have := smoothOfRelativeDimension_one_of_isCurve K f
  obtain ⟨e⟩ := EllMain.isTrivial_relativeDifferentials_of_genus_eq_one f hg
  let e' : Scheme.Hom.relativeDifferentials f ≅ SheafOfModules.unit C.ringCatSheaf := e
  have hφ : @id Γ(C, ⊤) ((e'.hom.val.app (op ⊤)).hom (((th f σ hσ).val.app (op ⊤)).hom
      ((e'.inv.val.app (op ⊤)).hom (1 : Γ(C, ⊤))))) = kTop f χ := by
    have h2 : (@id ((Scheme.Hom.relativeDifferentials f).val.obj (op ⊤))
        ((th f σ hσ).val.app (op ⊤) (om0 f e'))) = smulO f (kTop f χ) (om0 f e') :=
      (Tm_apply f σ hσ (om0 f e')).symm.trans ((hT _).trans (smul_top f χ _))
    have h3 := congrArg (co f e' ⊤) h2
    rwa [co_smulO, co_om0, mul_one] at h3
  have h12 : χ ^ 12 = 1 := by
    rcases hχ with h | h
    · rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, h, one_pow]
    · rw [show (12 : ℕ) = 6 * 2 from rfl, pow_mul, h, one_pow]
  refine ModuleCat.hom_ext (LinearMap.ext fun ω => ?_)
  exact (EllGeo.moduleSpecΓFunctor_map_apply f σ hσ _ _ ω).trans
    (homEquiv_app_top_eq_self f e' σ hσ ψ h0 hs χ hφ 12 h12 ω)

end MMP
