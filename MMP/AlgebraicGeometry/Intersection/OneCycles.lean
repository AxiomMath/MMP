module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.CartierCoefficients
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Intersection numbers, 1-cycles and numerical classes of curves

Let `X` be a proper scheme over a field `k`, `Z ⊆ X` a closed subscheme of dimension at most `d`
and `L₁, …, L_d` invertible sheaves on `X` (for instance `𝒪_X(D_j)` for Cartier divisors `D_j`).
The *intersection number* of Kollár–Mori, Notation 1.33–1.34, is
`(L₁ ⋯ L_d · Z) = ∑_{I ⊆ {1, …, d}} (-1)^{|I|} χ(Z, 𝒪_Z(-∑_{j ∈ I} L_j)) ∈ ℤ`. For a closed
subscheme `Z` of dimension `d` and an invertible sheaf `L` (for `Z ⊆ ℙᴺ_k`, `L = 𝒪(1)`) the
*degree* `deg Z` is `d!` times the coefficient of `t^d` in the Hilbert polynomial
`χ(Z, L|_Z^{⊗ t})`.

A *1-cycle* on a `k`-scheme `X` with coefficients in `A` is a finite formal sum `∑ aᵢ Cᵢ` of
proper curves `Cᵢ ⊆ X`. A morphism `g : X ⟶ Y` pushes 1-cycles forward,
`g_*[C] = [k(C) : k(g(C))] · [g(C)]` or `0`. A real 1-cycle `Z` has a degree `(Z · L)` against
every invertible sheaf `L`; numerical equivalence `Z ≡ Z'` means equal degrees against all of
them, and `N₁(X) = Z₁(X)_ℝ / ≡` is the real vector space of numerical classes of curves, with its
numerical topology, its Picard number `ρ(X) = dim_ℝ N₁(X)`, the group `Num(X) ⊆ N₁(X)^*` of
degree forms and the lattice `N₁(X)_ℤ` of classes with integral degrees.

## Main definitions

* `MMP.Mori.sheafIntersectionNumber`, `MMP.Mori.Divisor.intersectionNumberOn`: the intersection
  number `(L₁ ⋯ L_d · Z)` of invertible sheaves, and of Cartier divisors.
* `MMP.Mori.sheafSelfIntersectionNumber`, `MMP.Mori.sheafPowIntersectionNumber`,
  `MMP.Mori.sheafCombinationIntersectionNumber`: `(L^d · Z)`, `(L₁^{a₁} ⋯ L_r^{a_r} · Z)` and the
  multilinear expansion `(M^a · L₁ ⋯ L_b · Z)` for a linear combination `M = ∑ cⱼ Mⱼ`.
* `MMP.Mori.hilbertDegree`: the degree of a closed subscheme.
* `MMP.Mori.ProperCurve`, `MMP.Mori.OneCycle`, `MMP.Mori.ProperCurve.cycle`: proper curves,
  1-cycles and the cycle `[C]`.
* `MMP.Mori.OneCycle.pushforward`, `MMP.Mori.curvePushforward`: push-forward of 1-cycles.
* `MMP.Mori.OneCycle.degree`: the degree `(Z · L)`.
* `MMP.Mori.OneCycle.NumericallyEquivalent`, `MMP.Mori.NumericalCurveClasses`,
  `MMP.Mori.OneCycle.numericalClass`: numerical equivalence, `N₁(X)` and the class `[Z]`.
* `MMP.Mori.NumericalCurveClasses.instTopologicalSpace`: the numerical topology.
* `MMP.Mori.picardNumber`, `MMP.Mori.numericalDivisorGroup`, `MMP.Mori.numericalCurveLattice`,
  `MMP.Mori.IsNumericalPushforward`.
* `MMP.Mori.OneCycle.intersectionNumber`, `MMP.Mori.NumericalCurveClasses.intersectionNumber`,
  `MMP.Mori.NumericalCurveClasses.IntersectionNumberEq`: the intersection number `(Z · D)` of a
  real 1-cycle, and `(z · D)` of a numerical class, with an `ℝ`-Cartier divisor `D`.
* `MMP.Mori.KCartierDivisor.IsNef`: nef `ℝ`-Cartier divisors.

## Main results

* `MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber`: `(L₁ ⋯ L_d · Z)` agrees with
  `AlgebraicGeometry.intersectionNumber`, the coefficient of `n₁ ⋯ n_d` in the Snapper
  polynomial `n ↦ χ(Z, 𝒪_Z(∑ nⱼ Lⱼ))`.
* `MMP.Mori.Twist.twistedSheafUnitIsoTensorPower`: the twist of `𝒪_X` by `n` copies of one
  invertible sheaf `N` is `N^{⊗ ∑ nᵢ}`.
* `MMP.Mori.hilbertDegree_eq_factorial_mul_coeff`: `deg Z = d! · [t^d] P` for every polynomial
  `P` of degree at most `d` interpolating `t ↦ χ(Z, L|_Z^{⊗ t})` on `ℕ`.
* `MMP.Mori.OneCycle.numericalClass_eq_iff`: `[Z] = [Z']` if and only if `Z ≡ Z'`.
* `MMP.Mori.NumericalCurveClasses.continuous_degree`: each `z ↦ (z · L)` is continuous.
* `MMP.Mori.NumericalCurveClasses.intersectionNumberEq_iff`: `(z · D) = r` holds exactly for the
  value at `z` of the linear form `z ↦ (z · D)`, which is well defined on `N₁(X)`.
* `MMP.Mori.NumericalCurveClasses.intersectionNumber_ofCartier_mem`: for a Cartier divisor `E`,
  the form `z ↦ (z · E)` lies in `Num(X)`.

## Implementation notes

The intersection number is stated for invertible sheaves, the sheaves `𝒪_X(L_j)` of the Cartier
divisors of the source; `MMP.Mori.Divisor.intersectionNumberOn` is the case of Cartier divisors
on a normal scheme, where `MMP.Mori.Divisor.IsCartier` is defined. The sheaf
`𝒪_Z(-∑_{j ∈ I} L_j)` is the twist of `𝒪_Z` by the inverses `(L_j|_Z)^{⊗ -1}`, `j ∈ I`.

The Hilbert polynomial is not known to exist in the library, so the degree is defined by the
`d`-th forward difference `∑_{j=0}^{d} (-1)^{d-j} (d choose j) χ(Z, L|_Z^{⊗ j})`, which is `d!`
times the coefficient of `t^d` of every polynomial of degree at most `d` with these values
(`MMP.Mori.hilbertDegree_eq_factorial_mul_coeff`). It is stated for any proper `k`-scheme with
an invertible sheaf, of which `ℙᴺ_k` with `𝒪(1)` is the case of the source.

A proper curve is recorded by its generic point `x`: the reduced induced closed subscheme on the
closure of `x` is integral, and the conditions are that it has dimension one and is proper over
`k`. In a scheme two points with the same closure are equal, so distinct proper curves are
distinct subschemes. The function field `k(C)` is the residue field `κ(x)`, and
`[k(C) : k(g(C))]` is the degree of `κ(g(x)) ⟶ κ(x)`. The push-forward of `[C]` is taken to be
`0` unless `{g(x)}⁻` is a proper curve; when `Y` is separated over `k` the image `g(C)` is closed
and proper, so this is exactly the case `dim g(C) = 1` of the source.

Numerical equivalence is tested against all invertible sheaves `L` on `X`, the invertible sheaves
`𝒪_X(D)` of the Cartier divisors `D` of the source; on an integral scheme every invertible sheaf
is of that form. This needs no normality hypothesis on `X`, and agrees with the degree of
Cartier divisors where those are defined (`MMP.Mori.ProperCurve.degree_divisorialSheaf`).

The `ℝ`-Cartier divisors are `MMP.Mori.KCartierDivisor ℝ X`, the free real vector space on the
Cartier divisors `Div(X) = Γ(X, 𝒦_X^*/𝒪_X^*)` of an arbitrary scheme, and `(Z · D)` is defined on
it through the degrees `deg_{Cᵢ} 𝒪_X(Dⱼ)` of the invertible sheaves
`MMP.CartierDivisor.sheaf Dⱼ`; no normality hypothesis is needed. Nefness quantifies over the
proper curves of `X`, which on a proper `k`-scheme are all of its irreducible curves.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.16–1.17,
  1.33–1.35, 3.14–3.15, 3.27
* [R. Hartshorne, *Algebraic geometry*][Har77], I.7, II.6.15
* [W. Fulton, *Intersection theory*][Fulton], §1.4
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

/-! ### Intersection numbers of invertible sheaves with a closed subscheme -/

section IntersectionNumber

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The *intersection number* `(L₁ ⋯ L_d · Z)` of `d` invertible sheaves `L₁, …, L_d` on a
proper `k`-scheme `X` with a closed subscheme `i : Z ⟶ X` of dimension at most `d`:
`∑_{I ⊆ {1, …, d}} (-1)^{|I|} χ(Z, 𝒪_Z(-∑_{j ∈ I} L_j))`, where `𝒪_Z(-∑_{j ∈ I} L_j)` is the
twist of `𝒪_Z` by the inverses of the restrictions `L_j|_Z`, `j ∈ I`. -/
@[mmp "def_km1b_intersection_number"]
def sheafIntersectionNumber (d : ℕ) (_hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] : ℤ :=
  ∑ I : Finset (Fin d), (-1 : ℤ) ^ I.card *
    @eulerCharacteristic k _ Z (i ≫ f) inferInstance
      (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
        (fun j => (Scheme.Modules.pullback i).obj (L j)) (fun j => if j ∈ I then -1 else 0))
      (isCoherent_twistedSheafUnitPullback k f i L _)

/-- A family obtained by concatenating two families of invertible sheaves is invertible. -/
theorem isInvertible_finAppend {a b : ℕ} (A : Fin a → X.Modules) (B : Fin b → X.Modules)
    [hA : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (A j)]
    [hB : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (B j)] (t : Fin (a + b)) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (Fin.append A B t) := by
  induction t using Fin.addCases with
  | left j =>
    exact (congrArg (SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2)
      (Fin.append_left A B j)).mpr (hA j)
  | right j =>
    exact (congrArg (SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2)
      (Fin.append_right A B j)).mpr (hB j)

/-- The self-intersection number `(L^d · Z)`: the intersection number of `d` copies of `L`. -/
@[mmp "not_km1b_intersection_number"]
def sheafSelfIntersectionNumber (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : ℤ :=
  sheafIntersectionNumber k f i d hd fun _ => L

/-- The intersection number `(L₁^{a₁} ⋯ L_r^{a_r} · Z)`, with `L_j` repeated `a_j` times, against
a closed subscheme `Z` of dimension at most `∑ⱼ aⱼ`. -/
@[mmp "not_km1b_intersection_number"]
def sheafPowIntersectionNumber {r : ℕ} (a : Fin r → ℕ) (hd : topologicalKrullDim Z ≤ ∑ j, a j)
    (L : Fin r → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    ℤ :=
  sheafIntersectionNumber k f i (∑ j, a j) hd fun t => L (finSigmaFinEquiv.symm t).1

/-- The intersection number `(M^a · L₁ ⋯ L_b · Z)` of a linear combination `M = ∑ⱼ cⱼ Mⱼ` of
invertible sheaves with coefficients in a commutative ring `R` (for instance `ℚ` or `ℝ`), obtained
by expanding multilinearly:
`∑_{(j₁, …, j_a)} c_{j₁} ⋯ c_{j_a} (M_{j₁} ⋯ M_{j_a} · L₁ ⋯ L_b · Z)`. -/
@[mmp "not_km1b_intersection_number"]
def sheafCombinationIntersectionNumber (R : Type*) [CommRing R] {s : ℕ} (c : Fin s → R)
    (M : Fin s → X.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (a : ℕ) {b : ℕ} (L : Fin b → X.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hd : topologicalKrullDim Z ≤ (a + b : ℕ)) : R :=
  ∑ J : Fin a → Fin s, (∏ t, c (J t)) *
    (@sheafIntersectionNumber k _ X Z f _ i _ (a + b) hd (Fin.append (fun t => M (J t)) L)
      (isInvertible_finAppend (fun t => M (J t)) L (hA := fun t => hM (J t)) (hB := hL)) : R)

namespace Divisor

variable [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection number `(D₁ ⋯ D_d · Z)` of Cartier divisors `D₁, …, D_d` on a normal proper
`k`-scheme `X` with a closed subscheme `Z` of dimension at most `d`: the intersection number of
their invertible sheaves `𝒪_X(D_j)`. -/
@[mmp "def_km1b_intersection_number"]
def intersectionNumberOn (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (D : Fin d → Divisor X)
    (hD : ∀ j, (D j).IsCartier) : ℤ :=
  haveI := QuasiCompact.compactSpace_of_compactSpace f
  haveI := fun j => (hD j).isInvertibleModule_divisorialSheaf
  sheafIntersectionNumber k f i d hd fun j => (D j).divisorialSheaf

end Divisor

/-! ### The degree of a closed subscheme -/

/-- The *Hilbert function* `t ↦ χ(Z, L|_Z^{⊗ t})` of a closed subscheme `i : Z ⟶ X` of a proper
`k`-scheme with respect to an invertible sheaf `L` on `X`; for `X = ℙᴺ_k` and `L = 𝒪(1)` it is
`t ↦ χ(Z, 𝒪_Z(t))`. -/
def subschemeHilbertFunction (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (t : ℤ) : ℤ :=
  @eulerCharacteristic k _ Z (i ≫ f) inferInstance
    (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
      (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj L) fun _ => t)
    (isCoherent_twistedSheafUnitPullback k f i (fun _ : Fin 1 => L) _)

/-- The *degree* `deg Z` of a closed subscheme `i : Z ⟶ X` of dimension `d` of a proper
`k`-scheme with respect to an invertible sheaf `L` (for `X = ℙᴺ_k`, `L = 𝒪(1)`, the degree of
`Z ⊆ ℙᴺ_k`): `d!` times the coefficient of `t^d` in the Hilbert polynomial
`P_Z(t) = χ(Z, L|_Z^{⊗ t})`, computed as the `d`-th forward difference
`∑_{j=0}^{d} (-1)^{d-j} (d choose j) P_Z(j)`; see
`MMP.Mori.hilbertDegree_eq_factorial_mul_coeff`. -/
@[mmp "def_km1b_degree_projective_subscheme"]
def hilbertDegree (d : ℕ) (_hd : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : ℤ :=
  ∑ j ∈ Finset.range (d + 1),
    (-1 : ℤ) ^ (d - j) * (d.choose j : ℤ) * subschemeHilbertFunction k f i L j

/-- The `d`-th forward difference of a polynomial of degree at most `d` is `d!` times its
coefficient of `X^d`. -/
theorem fwdDiff_iter_eval_eq_factorial_mul_coeff {R : Type*} [CommRing R] (P : Polynomial R)
    {d : ℕ} (hP : P.natDegree ≤ d) (x : R) :
    (fwdDiff (1 : R))^[d] P.eval x = d.factorial * P.coeff d := by
  have h1 : P.eval = (fun r => ∑ j ∈ Finset.range d, P.coeff j * r ^ j) +
      P.coeff d • (fun r => r ^ d) := by
    funext r
    simp [P.eval_eq_sum_range' (show P.natDegree < d + 1 by omega), Finset.sum_range_succ]
  rw [h1, fwdDiff_iter_add, fwdDiff_iter_const_smul, fwdDiff_iter_sum_mul_pow_eq_zero,
    fwdDiff_iter_eq_factorial]
  simp [mul_comm]

/-- **The degree is read off the Hilbert polynomial.** If a rational polynomial `P` of degree at
most `d` takes the values `χ(Z, L|_Z^{⊗ t})` at the natural numbers `t`, then
`deg Z = d! · (coefficient of t^d in P)`. -/
theorem hilbertDegree_eq_factorial_mul_coeff (d : ℕ) (hd : topologicalKrullDim Z = d)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ d)
    (hval : ∀ t : ℕ, P.eval (t : ℚ) = subschemeHilbertFunction k f i L t) :
    (hilbertDegree k f i d hd L : ℚ) = d.factorial * P.coeff d := by
  rw [← fwdDiff_iter_eval_eq_factorial_mul_coeff P hP 0, fwdDiff_iter_eq_sum_shift,
    hilbertDegree]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zero_add, nsmul_eq_mul, mul_one, hval j, zsmul_eq_mul]
  push_cast
  ring

end IntersectionNumber

/-! ### The intersection number as a coefficient of the Snapper polynomial -/

namespace Snapper

open MvPolynomial

/-- The substitution `Xᵢ ↦ -Xᵢ`. -/
private def negSub {d : ℕ} : MvPolynomial (Fin d) ℚ →ₐ[ℚ] MvPolynomial (Fin d) ℚ :=
  aeval fun i => -X i

private theorem negSub_monomial {d : ℕ} (s : Fin d →₀ ℕ) (a : ℚ) :
    negSub (monomial s a) = monomial s (a * (-1) ^ s.sum fun _ e => e) := by
  rw [negSub, aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  have : ∀ i : Fin d, (-X i : MvPolynomial (Fin d) ℚ) ^ s i = (-1) ^ s i * X i ^ s i :=
    fun i => neg_pow _ _
  simp only [this, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp [map_mul, mul_assoc, algebraMap_eq]

private theorem coeff_negSub {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (s : Fin d →₀ ℕ) :
    (negSub P).coeff s = P.coeff s * (-1) ^ s.sum fun _ e => e := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [negSub_monomial]
    by_cases h : u = s
    · subst h; simp [coeff_monomial]
    · simp [coeff_monomial, h]
  | add p q hp hq => simp [map_add, hp, hq, add_mul]

private theorem eval_negSub {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (x : Fin d → ℚ) :
    eval x (negSub P) = eval (fun i => -x i) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [negSub_monomial, eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
    have : ∀ i : Fin d, (-x i) ^ u i = (-1) ^ u i * x i ^ u i := fun i => neg_pow _ _
    simp only [this, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    ring
  | add p q hp hq => simp [map_add, hp, hq]

private theorem totalDegree_negSub {d : ℕ} (P : MvPolynomial (Fin d) ℚ) :
    (negSub P).totalDegree ≤ P.totalDegree :=
  totalDegree_le_of_support_subset fun s hs => by
    rw [mem_support_iff, coeff_negSub] at hs
    exact mem_support_iff.2 fun h => hs (by simp [h])

/-- **The coefficient of `X₁ ⋯ X_d` by inclusion–exclusion at the vectors `-1_I`.** For a
polynomial `P` in `d` variables of total degree at most `d`,
`∑_{I ⊆ {1, …, d}} (-1)^{|I|} P(-1_I)` is the coefficient of `X₁ ⋯ X_d` in `P`. -/
theorem sum_neg_one_pow_card_mul_eval_neg_indicator {d : ℕ} (P : MvPolynomial (Fin d) ℚ)
    (hP : P.totalDegree ≤ d) :
    ∑ I : Finset (Fin d), (-1 : ℚ) ^ I.card *
        eval (fun j => if j ∈ I then (-1 : ℚ) else 0) P =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  have h := MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one (negSub P)
    ((totalDegree_negSub P).trans hP)
  have hs : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1).sum (fun _ e => e) = d := by
    rw [Finsupp.sum_fintype _ _ (by simp)]; simp
  have hI : ∀ I : Finset (Fin d), (-1 : ℚ) ^ (d - I.card) = (-1) ^ d * (-1) ^ I.card := by
    intro I
    rw [← mul_inv_eq_iff_eq_mul₀ (by simp), ← inv_pow, inv_neg_one, ← pow_add,
      Nat.sub_add_cancel (by simpa using Finset.card_le_univ I)]
  have he : ∀ I : Finset (Fin d), eval (fun j => if j ∈ I then (1 : ℚ) else 0) (negSub P) =
      eval (fun j => if j ∈ I then (-1 : ℚ) else 0) P := fun I => by
    rw [eval_negSub]
    exact congrArg (fun x => eval x P) (funext fun j => by split_ifs <;> simp)
  simp only [coeff_negSub, hs, he, hI, mul_assoc, ← Finset.mul_sum] at h
  have h2 : ((-1 : ℚ) ^ d) * (-1) ^ d = 1 := by rw [← mul_pow]; simp
  linear_combination (-1 : ℚ) ^ d * h - (∑ I : Finset (Fin d), (-1 : ℚ) ^ I.card *
    eval (fun j => if j ∈ I then (-1 : ℚ) else 0) P -
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1)) * h2

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The intersection number of Kollár–Mori is the Stacks intersection number.** Both are the
coefficient of `n₁ ⋯ n_d` in the Snapper polynomial `n ↦ χ(Z, 𝒪_Z(∑ nⱼ Lⱼ))`. -/
theorem sheafIntersectionNumber_eq_intersectionNumber (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k f i d hd L = AlgebraicGeometry.intersectionNumber k f i d hd L := by
  obtain ⟨P, hP0, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (i ≫ f)
    (fun j => (Scheme.Modules.pullback i).obj (L j)) (SheafOfModules.unit Z.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f))
  have hdeg : P.totalDegree ≤ d := by
    rcases hP0 with rfl | h
    · simp
    · exact_mod_cast h.trans ((topologicalKrullDim_subspace_le Z _).trans hd)
  apply Int.cast_injective (α := ℚ)
  rw [AlgebraicGeometry.intersectionNumber_eq_coeff k f i d hd L P (fun n => by rw [hP n]) hdeg,
    ← sum_neg_one_pow_card_mul_eval_neg_indicator P hdeg, sheafIntersectionNumber]
  push_cast
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← hP]
  exact congrArg (fun x => (-1) ^ I.card * eval x P) (funext fun j => by split_ifs <;> simp)

end Snapper

/-! ### Twists by a constant family -/

namespace Twist

open Stacks.SheafOfModules.Invertible

/-- **Integer tensor powers depend only on the isomorphism class of the invertible module.**
An isomorphism `M ≅ N` of invertible modules induces `M^{⊗ m} ≅ N^{⊗ m}` for every `m : ℤ`. -/
def tensorPowerIsoOfIso {X : Scheme.{u}} (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N m :=
  Stacks.Equivalence.powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj M).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj N).asEquivalence (𝟭 _)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).mapIso e) m
    (SheafOfModules.unit _)

/-- The fold over a list of indices of a constant family of invertible modules, started at a
tensor power, is the tensor power with the exponents added on. -/
def twistListTensorPowerIso {X : Scheme.{u}} {r : ℕ}
    (M : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M i)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : ∀ i, M i ≅ N) (n : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (m : ℤ),
      twistList M n l (tensorPower X.presheaf X.ringCatSheaf.2 N m) ≅
        tensorPower X.presheaf X.ringCatSheaf.2 N (l.foldl (fun z i => z + n i) m) := by
  intro l
  induction l with
  | nil => exact fun m => Iso.refl _
  | cons i t ih =>
      exact fun m =>
        twistListIso M n t
            (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
                (tensorPowerIsoOfIso (M i) N (e i) (n i)) ≪≫
              (tensorPowerCoherence X.presheaf X.ringCatSheaf.2 N).mulIso m (n i)) ≪≫
          ih (m + n i)

private theorem finRange_foldl_add {r : ℕ} (n : Fin r → ℤ) (z : ℤ) :
    (List.finRange r).foldl (fun a i => a + n i) z = z + ∑ i, n i := by
  induction r generalizing z with
  | zero => simp
  | succ r ih =>
      rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
      rw [ih (fun i => n i.succ) (z + n 0)]
      simp [Fin.sum_univ_succ, add_assoc]

/-- **A twist of the structure sheaf by a constant family is a single tensor power.**
`𝒪_X ⊗ M_1^{⊗ n_1} ⊗ ⋯ ⊗ M_r^{⊗ n_r} ≅ N^{⊗ (n_1 + ⋯ + n_r)}` whenever every `M_i` is
isomorphic to `N`. -/
def twistedSheafUnitIsoTensorPower {X : Scheme.{u}} {r : ℕ}
    (M : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M i)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : ∀ i, M i ≅ N) (n : Fin r → ℤ) :
    twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N (∑ i, n i) :=
  have hunit : (SheafOfModules.unit X.ringCatSheaf : X.Modules) =
      tensorPower X.presheaf X.ringCatSheaf.2 N 0 := rfl
  have hfold : (List.finRange r).foldl (fun z i => z + n i) 0 = ∑ i, n i := by
    rw [finRange_foldl_add]; ring
  twistListIso M n (List.finRange r) (eqToIso hunit) ≪≫
    twistListTensorPowerIso M N e n (List.finRange r) 0 ≪≫
    eqToIso (congrArg (tensorPower X.presheaf X.ringCatSheaf.2 N) hfold)

end Twist

/-! ### Proper curves and 1-cycles -/

section Cycles

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The reduced induced closed subscheme structure on the closure `{x}⁻` of a point `x` of `X`;
it is integral, with generic point `x`. -/
abbrev curveSubschemeAt (x : X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme

/-- The closed immersion `{x}⁻ ⟶ X` of the closure of a point. -/
abbrev curveSubschemeAtι (x : X) : curveSubschemeAt x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι

/-- A point `x` of a `k`-scheme `X` (structure morphism `sX`) is the generic point of a *proper
curve* if the integral closed subscheme `{x}⁻` has dimension one and is proper over `k`. -/
structure IsProperCurve (sX : X ⟶ Spec (.of k)) (x : X) : Prop where
  /-- The closure of `x` has dimension one. -/
  dim_eq : topologicalKrullDim (curveSubschemeAt x) = 1
  /-- The closure of `x` is proper over `k`. -/
  isProper : IsProper (curveSubschemeAtι x ≫ sX)

/-- On a proper `k`-scheme, the generic point of every one-dimensional integral closed subscheme
is the generic point of a proper curve. -/
theorem isProperCurve_of_isProper (sX : X ⟶ Spec (.of k)) [IsProper sX] {x : X}
    (h : topologicalKrullDim (curveSubschemeAt x) = 1) : IsProperCurve sX x :=
  ⟨h, inferInstance⟩

/-- A *proper curve* `C ⊆ X` on a `k`-scheme `X`: an irreducible and reduced closed subscheme of
dimension one which is proper over `k`, recorded by its generic point. Distinct points have
distinct closures, so distinct proper curves are distinct closed subschemes. -/
@[ext]
structure ProperCurve (sX : X ⟶ Spec (.of k)) where
  /-- The generic point of the curve. -/
  point : X
  isProperCurve : IsProperCurve sX point

namespace ProperCurve

variable {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX)

/-- The curve `C`, as a scheme. -/
abbrev scheme : Scheme.{u} := curveSubschemeAt C.point

/-- The closed immersion `C ⟶ X`. -/
abbrev ι : C.scheme ⟶ X := curveSubschemeAtι C.point

/-- The curve `C` is proper over `k`. -/
instance isProper_ι_comp : IsProper (C.ι ≫ sX) := C.isProperCurve.isProper

/-- The curve `C` has dimension one. -/
theorem dim_eq : topologicalKrullDim C.scheme = 1 := C.isProperCurve.dim_eq

/-- The curve `C` has dimension at most one. -/
theorem dim_le : topologicalKrullDim C.scheme ≤ 1 := C.dim_eq.le

end ProperCurve

/-- A *1-cycle* with coefficients in `A` (for instance `ℤ`, `ℚ` or `ℝ`) on a `k`-scheme `X`: a
formal finite sum `∑ᵢ aᵢ Cᵢ` of pairwise distinct proper curves `Cᵢ ⊆ X` with `aᵢ ∈ A`, that is,
a finitely supported function from proper curves to `A`. The *components* are the curves with
nonzero coefficient, the support of the function. -/
@[mmp "def_km1a_one_cycle"]
abbrev OneCycle (A : Type*) [Zero A] (sX : X ⟶ Spec (.of k)) : Type _ := ProperCurve sX →₀ A

/-- The 1-cycle `[C] = 1 · C` of a proper curve `C`. -/
@[mmp "def_km1a_one_cycle"]
def ProperCurve.cycle (A : Type*) [Zero A] [One A] {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    OneCycle A sX :=
  Finsupp.single C 1

/-- The components of a 1-cycle: the proper curves with nonzero coefficient. -/
abbrev OneCycle.components {A : Type*} [Zero A] {sX : X ⟶ Spec (.of k)} (Z : OneCycle A sX) :
    Finset (ProperCurve sX) :=
  Z.support

/-! ### Push-forward of 1-cycles -/

/-- The degree `[κ(x) : κ(g(x))]` of the residue field extension at a point `x` along a morphism
`g`; for the generic point `x` of a curve `C` it is `[k(C) : k(g(C))]`. -/
def residueFieldDegree (g : X ⟶ Y) (x : X) : ℕ :=
  letI := (g.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (g x)) (X.residueField x)

open Classical in
/-- The push-forward `g_*[{x}⁻] ∈ Z₁(Y)_A` of the closure of a point `x` along `g : X ⟶ Y`: if the
image `{g(x)}⁻ = g({x}⁻)` is a proper curve, it is `[κ(x) : κ(g(x))] · [g({x}⁻)]`, and it is `0`
otherwise, in particular when the image is a point. -/
def cyclePushforwardOfPoint (A : Type*) [Semiring A] (sY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (x : X) :
    OneCycle A sY :=
  if h : IsProperCurve sY (g x) then Finsupp.single ⟨g x, h⟩ (residueFieldDegree g x : A) else 0

/-- If the image `{g(x)}⁻` is a proper curve, `g_*[{x}⁻] = [κ(x) : κ(g(x))] · [{g(x)}⁻]`. -/
theorem cyclePushforwardOfPoint_of_isProperCurve (A : Type*) [Semiring A] (sY : Y ⟶ Spec (.of k))
    (g : X ⟶ Y) {x : X} (h : IsProperCurve sY (g x)) :
    cyclePushforwardOfPoint A sY g x = Finsupp.single ⟨g x, h⟩ (residueFieldDegree g x : A) := by
  simp [cyclePushforwardOfPoint, h]

/-- If the image `{g(x)}⁻` is not a proper curve, `g_*[{x}⁻] = 0`. -/
theorem cyclePushforwardOfPoint_of_not_isProperCurve (A : Type*) [Semiring A]
    (sY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) {x : X} (h : ¬IsProperCurve sY (g x)) :
    cyclePushforwardOfPoint A sY g x = 0 := by
  simp [cyclePushforwardOfPoint, h]

/-- The *push-forward* `g_* : Z₁(X)_A ⟶ Z₁(Y)_A` of 1-cycles along a morphism `g : X ⟶ Y` of
`k`-schemes: `g_*[C] = [k(C) : k(g(C))] · [g(C)]` when `g(C)` is a curve and `0` when it is a
point, extended `A`-linearly. -/
@[mmp "def_km1a_pushforward_one_cycle"]
def OneCycle.pushforward (A : Type*) [Semiring A] (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) : OneCycle A sX →ₗ[A] OneCycle A sY :=
  Finsupp.linearCombination A fun C => cyclePushforwardOfPoint A sY g C.point

/-- The push-forward of the cycle `[C]` is `g_*[C] = [k(C) : k(g(C))] · [g(C)]`, or `0` when
`g(C)` is a point. -/
theorem OneCycle.pushforward_cycle (A : Type*) [Semiring A] {sX : X ⟶ Spec (.of k)}
    (sY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (C : ProperCurve sX) :
    OneCycle.pushforward A sX sY g (C.cycle A) = cyclePushforwardOfPoint A sY g C.point := by
  simp [OneCycle.pushforward, ProperCurve.cycle]

/-- The push-forward `φ_*(C) := φ_*[C]` of an integral scheme `C` (a proper curve) along a
morphism `φ : C ⟶ X`: `[k(C) : k(φ(C))] · [φ(C)]` if the image `φ(C)` is a proper curve, and `0`
otherwise. -/
@[mmp "def_km1a_pushforward_one_cycle"]
def curvePushforward (A : Type*) [Semiring A] {C : Scheme.{u}} [IsIntegral C]
    (sX : X ⟶ Spec (.of k)) (φ : C ⟶ X) : OneCycle A sX :=
  cyclePushforwardOfPoint A sX φ (genericPoint C)

/-! ### Degrees of invertible sheaves on 1-cycles -/

variable (k) in
/-- The degree `deg_C L` of an invertible sheaf `L` on `X` along a proper curve `C ⊆ X`. -/
def ProperCurve.degree {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : ℤ :=
  degreeOn k sX C.ι C.dim_le L

/-- The degree `(Z · L) = ∑ᵢ aᵢ deg_{Cᵢ} L` of an invertible sheaf `L` on a 1-cycle
`Z = ∑ᵢ aᵢ Cᵢ`, an `A`-linear form on `Z₁(X)_A`. -/
def OneCycle.degree (A : Type*) [CommRing A] (sX : X ⟶ Spec (.of k)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : OneCycle A sX →ₗ[A] A :=
  Finsupp.linearCombination A fun C => (C.degree k L : A)

/-- The degree of `L` on `Z = ∑ᵢ aᵢ Cᵢ` is `∑ᵢ aᵢ deg_{Cᵢ} L`. -/
theorem OneCycle.degree_apply (A : Type*) [CommRing A] (sX : X ⟶ Spec (.of k))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (Z : OneCycle A sX) :
    OneCycle.degree A sX L Z = Z.sum fun C a => a * (C.degree k L : A) := by
  simp [OneCycle.degree, Finsupp.linearCombination_apply, smul_eq_mul]

/-- The degree of `L` on the cycle `[C]` is `deg_C L`. -/
theorem OneCycle.degree_cycle (A : Type*) [CommRing A] {sX : X ⟶ Spec (.of k)}
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (C : ProperCurve sX) : OneCycle.degree A sX L (C.cycle A) = C.degree k L := by
  simp [OneCycle.degree, ProperCurve.cycle]

/-- On a normal `k`-scheme, quasi-compact over `k`, the degree of the invertible sheaf `𝒪_X(D)`
of a Cartier divisor `D` along a proper curve `C` is the degree `D.degreeOn k sX C.ι` of `D`. -/
theorem ProperCurve.degree_divisorialSheaf {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] (C : ProperCurve sX) (D : Divisor X)
    (hD : D.IsCartier) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sX
    haveI := hD.isInvertibleModule_divisorialSheaf
    C.degree k D.divisorialSheaf = D.degreeOn k sX C.ι C.dim_le hD :=
  rfl

/-! ### Numerical equivalence and the space `N₁(X)` -/

variable (sX : X ⟶ Spec (.of k))

/-- The real 1-cycles which are *numerically trivial*: those `Z` with `(Z · L) = 0` for every
invertible sheaf `L` on `X`, the common kernel of the linear forms `Z ↦ (Z · L)`. -/
def OneCycle.numericallyTrivial : Submodule ℝ (OneCycle ℝ sX) :=
  ⨅ (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
    haveI := h
    LinearMap.ker (OneCycle.degree ℝ sX L)

variable {sX} in
/-- A real 1-cycle is numerically trivial if and only if `(Z · L) = 0` for every invertible
sheaf `L`. -/
theorem OneCycle.mem_numericallyTrivial {Z : OneCycle ℝ sX} :
    Z ∈ OneCycle.numericallyTrivial sX ↔
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        OneCycle.degree ℝ sX L Z = 0 := by
  simp only [OneCycle.numericallyTrivial, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Two real 1-cycles `Z, Z'` on `X` are *numerically equivalent*, `Z ≡ Z'`, if
`(Z · L) = (Z' · L)` for every invertible sheaf `L` on `X`, that is, `(Z · D) = (Z' · D)` for the
invertible sheaf `L = 𝒪_X(D)` of every Cartier divisor `D`. -/
@[mmp "def_km1b_numerical_equivalence_one_cycles"]
def OneCycle.NumericallyEquivalent (Z Z' : OneCycle ℝ sX) : Prop :=
  ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
    OneCycle.degree ℝ sX L Z = OneCycle.degree ℝ sX L Z'

variable {sX} in
/-- Two real 1-cycles are numerically equivalent if and only if their difference is numerically
trivial. -/
theorem OneCycle.numericallyEquivalent_iff_sub_mem {Z Z' : OneCycle ℝ sX} :
    OneCycle.NumericallyEquivalent sX Z Z' ↔ Z - Z' ∈ OneCycle.numericallyTrivial sX := by
  rw [OneCycle.mem_numericallyTrivial]
  refine forall_congr' fun L => ⟨fun h _ => ?_, fun h _ => ?_⟩
  · rw [map_sub, h, sub_self]
  · exact sub_eq_zero.mp (by rw [← map_sub]; exact h)

/-- The real vector space `N₁(X) = Z₁(X)_ℝ / ≡` of *numerical classes of curves*: the quotient
of the real 1-cycles by the subspace of numerically trivial ones. -/
@[mmp "def_km1b_numerical_curve_classes"]
abbrev NumericalCurveClasses : Type _ := OneCycle ℝ sX ⧸ OneCycle.numericallyTrivial sX

/-- The class `[Z] ∈ N₁(X)` of a real 1-cycle `Z`. -/
@[mmp "not_km1b_class_of_one_cycle"]
def OneCycle.numericalClass : OneCycle ℝ sX →ₗ[ℝ] NumericalCurveClasses sX :=
  (OneCycle.numericallyTrivial sX).mkQ

variable {sX} in
/-- Two real 1-cycles have the same class in `N₁(X)` if and only if they are numerically
equivalent. -/
theorem OneCycle.numericalClass_eq_iff {Z Z' : OneCycle ℝ sX} :
    OneCycle.numericalClass sX Z = OneCycle.numericalClass sX Z' ↔
      OneCycle.NumericallyEquivalent sX Z Z' := by
  rw [OneCycle.numericallyEquivalent_iff_sub_mem, OneCycle.numericalClass,
    Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

/-- Every element of `N₁(X)` is the class of a real 1-cycle. -/
theorem OneCycle.numericalClass_surjective :
    Function.Surjective (OneCycle.numericalClass sX) :=
  Submodule.mkQ_surjective _

/-- The degree `(z · L)` of an invertible sheaf `L` on a numerical class `z ∈ N₁(X)`, well
defined since numerically trivial cycles have degree zero. -/
def NumericalCurveClasses.degree (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  (OneCycle.numericallyTrivial sX).liftQ (OneCycle.degree ℝ sX L) fun _ hZ =>
    LinearMap.mem_ker.mpr (OneCycle.mem_numericallyTrivial.mp hZ L)

/-- The degree `([Z] · L)` of the class of a 1-cycle `Z` is `(Z · L)`. -/
theorem NumericalCurveClasses.degree_numericalClass (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (Z : OneCycle ℝ sX) :
    NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX Z) =
      OneCycle.degree ℝ sX L Z :=
  rfl

/-- The *numerical topology* on `N₁(X)`: the coarsest topology for which every linear form
`z ↦ (z · L)`, `L` an invertible sheaf (for instance `𝒪_X(D)` for a Cartier divisor `D`), is
continuous. -/
@[mmp "def_km1b_numerical_topology"]
instance NumericalCurveClasses.instTopologicalSpace :
    TopologicalSpace (NumericalCurveClasses sX) :=
  ⨅ (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
    haveI := h
    TopologicalSpace.induced (NumericalCurveClasses.degree sX L) inferInstance

/-- Each linear form `z ↦ (z · L)` is continuous for the numerical topology. -/
theorem NumericalCurveClasses.continuous_degree (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Continuous (NumericalCurveClasses.degree sX L) :=
  continuous_iff_le_induced.mpr (iInf₂_le L h)

/-- The *Picard number* `ρ(X) = dim_ℝ N₁(X) ∈ ℕ ∪ {∞}`. -/
@[mmp "def_km1b_picard_number"]
def picardNumber : ℕ∞ :=
  (Module.rank ℝ (NumericalCurveClasses sX)).toENat

/-- The group `Num(X) ⊆ N₁(X)^*` of the linear forms `z ↦ (L · z)`, `L` an invertible sheaf on
`X` (for instance `𝒪_X(D)` for a Cartier divisor `D`). -/
@[mmp "def_km3b_numerical_divisor_group"]
def numericalDivisorGroup : AddSubgroup (Module.Dual ℝ (NumericalCurveClasses sX)) :=
  AddSubgroup.closure {φ | ∃ (L : X.Modules)
    (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      φ = NumericalCurveClasses.degree sX L}

/-- The degree form `z ↦ (z · L)` of an invertible sheaf `L` lies in `Num(X)`. -/
theorem NumericalCurveClasses.degree_mem_numericalDivisorGroup (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    NumericalCurveClasses.degree sX L ∈ numericalDivisorGroup sX :=
  AddSubgroup.subset_closure ⟨L, inferInstance, rfl⟩

/-- The lattice `N₁(X)_ℤ = {z ∈ N₁(X) | (L · z) ∈ ℤ for every invertible sheaf L}` of
numerical classes with integral degrees. -/
@[mmp "def_km3b_numerical_curve_lattice"]
def numericalCurveLattice : AddSubgroup (NumericalCurveClasses sX) where
  carrier := {z | ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
    ∃ n : ℤ, NumericalCurveClasses.degree sX L z = n}
  zero_mem' _ _ := ⟨0, by simp⟩
  add_mem' {z z'} hz hz' L _ := by
    obtain ⟨n, hn⟩ := hz L
    obtain ⟨n', hn'⟩ := hz' L
    exact ⟨n + n', by rw [map_add, hn, hn', Int.cast_add]⟩
  neg_mem' {z} hz L _ := by
    obtain ⟨n, hn⟩ := hz L
    exact ⟨-n, by rw [map_neg, hn, Int.cast_neg]⟩

variable {sX} in
/-- A class `z ∈ N₁(X)` lies in `N₁(X)_ℤ` iff `(z · L) ∈ ℤ` for every invertible sheaf `L`. -/
theorem mem_numericalCurveLattice {z : NumericalCurveClasses sX} :
    z ∈ numericalCurveLattice sX ↔
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        ∃ n : ℤ, NumericalCurveClasses.degree sX L z = n :=
  Iff.rfl

variable {sX} in
/-- A real-linear map `φ : N₁(X) ⟶ N₁(Y)` is a *push-forward* for `g : X ⟶ Y` if
`φ([z]) = [g_* z]` for every real 1-cycle `z` on `X`. -/
@[mmp "def_km3b_pushforward_numerical_classes"]
def IsNumericalPushforward (sY : Y ⟶ Spec (.of k)) (g : X ⟶ Y)
    (φ : NumericalCurveClasses sX →ₗ[ℝ] NumericalCurveClasses sY) : Prop :=
  ∀ z : OneCycle ℝ sX,
    φ (OneCycle.numericalClass sX z) =
      OneCycle.numericalClass sY (OneCycle.pushforward ℝ sX sY g z)

/-! ### Intersection numbers of 1-cycles with `ℝ`-Cartier divisors -/

section RealCartier

variable {sX}

/-- The invertible sheaf `𝒪_X(E)` of a Cartier divisor `E` on an arbitrary scheme: finite locally
free of rank one, hence invertible. -/
instance isInvertible_cartierSheaf (E : X.CartierDivisor) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf E) :=
  (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one X
    (MMP.CartierDivisor.sheaf E)).mpr inferInstance

/-- The degree `Z ↦ ∑ᵢ aᵢ deg_{Cᵢ} 𝒪_X(E)` of a Cartier divisor `E` on real 1-cycles
`Z = ∑ᵢ aᵢ Cᵢ`, a linear form on `Z₁(X)_ℝ`. -/
def OneCycle.cartierDegree (E : X.CartierDivisor) : OneCycle ℝ sX →ₗ[ℝ] ℝ :=
  OneCycle.degree ℝ sX (MMP.CartierDivisor.sheaf E)

/-- The intersection pairing `(D, Z) ↦ (Z · D)` between `ℝ`-Cartier divisors and real 1-cycles,
`ℝ`-bilinear by construction. -/
def OneCycle.intersectionPairing : KCartierDivisor ℝ X →ₗ[ℝ] OneCycle ℝ sX →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ OneCycle.cartierDegree

/-- The *intersection number* `(Z · D) = ∑ᵢ ∑ⱼ aᵢ cⱼ deg_{Cᵢ} 𝒪_X(Dⱼ)` of a real 1-cycle
`Z = ∑ᵢ aᵢ Cᵢ` and an `ℝ`-Cartier divisor `D = ∑ⱼ cⱼ Dⱼ` on an arbitrary `k`-scheme, also written
`(D · Z)`; it is `ℝ`-bilinear in `(Z, D)` (`MMP.Mori.OneCycle.intersectionPairing`). -/
@[mmp "def_km1b_cycle_divisor_intersection"]
def OneCycle.intersectionNumber (Z : OneCycle ℝ sX) (D : KCartierDivisor ℝ X) : ℝ :=
  OneCycle.intersectionPairing D Z

/-- The intersection number of `Z = ∑ᵢ aᵢ Cᵢ` and `D = ∑ⱼ cⱼ Dⱼ` is
`∑ⱼ ∑ᵢ aᵢ cⱼ deg_{Cᵢ} 𝒪_X(Dⱼ)`. -/
theorem OneCycle.intersectionNumber_eq_sum (Z : OneCycle ℝ sX) (D : KCartierDivisor ℝ X) :
    Z.intersectionNumber D =
      D.sum fun E c => Z.sum fun C a =>
        a * c * (C.degree k (MMP.CartierDivisor.sheaf E) : ℝ) := by
  simp only [OneCycle.intersectionNumber, OneCycle.intersectionPairing,
    Finsupp.linearCombination_apply, LinearMap.sum_apply, Finsupp.sum,
    LinearMap.smul_apply, OneCycle.cartierDegree, OneCycle.degree_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun C _ => ?_
  ring

/-- `(Z · 1 · E) = deg_Z 𝒪_X(E)` for a Cartier divisor `E`. -/
theorem OneCycle.intersectionNumber_ofCartier (Z : OneCycle ℝ sX) (E : X.CartierDivisor) :
    Z.intersectionNumber (KCartierDivisor.ofCartier ℝ E) = OneCycle.cartierDegree E Z := by
  simp [OneCycle.intersectionNumber, OneCycle.intersectionPairing, KCartierDivisor.ofCartier]

/-- A numerically trivial 1-cycle has intersection number zero with every `ℝ`-Cartier divisor. -/
theorem OneCycle.intersectionNumber_eq_zero_of_mem {Z : OneCycle ℝ sX}
    (hZ : Z ∈ OneCycle.numericallyTrivial sX) (D : KCartierDivisor ℝ X) :
    Z.intersectionNumber D = 0 := by
  have h : ∀ E : X.CartierDivisor, OneCycle.cartierDegree E Z = 0 := fun E =>
    OneCycle.mem_numericallyTrivial.mp hZ _
  simp [OneCycle.intersectionNumber, OneCycle.intersectionPairing,
    Finsupp.linearCombination_apply, Finsupp.sum, h]

/-- The intersection number `(z · D)` of a numerical class `z ∈ N₁(X)` with an `ℝ`-Cartier
divisor `D`: the common value of `(Z · D)` over the 1-cycles `Z` with `[Z] = z`. -/
@[mmp "def_km1b_class_divisor_pairing"]
def NumericalCurveClasses.intersectionNumber (D : KCartierDivisor ℝ X) :
    NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  (OneCycle.numericallyTrivial sX).liftQ (OneCycle.intersectionPairing D) fun _ hZ =>
    LinearMap.mem_ker.mpr (OneCycle.intersectionNumber_eq_zero_of_mem hZ D)

/-- The intersection number `([Z] · D)` of the class of a 1-cycle `Z` is `(Z · D)`. -/
theorem NumericalCurveClasses.intersectionNumber_numericalClass (D : KCartierDivisor ℝ X)
    (Z : OneCycle ℝ sX) :
    NumericalCurveClasses.intersectionNumber D (OneCycle.numericalClass sX Z) =
      Z.intersectionNumber D :=
  rfl

/-- For a numerical class `z ∈ N₁(X)`, an `ℝ`-Cartier divisor `D` and `r ∈ ℝ`, `(z · D) = r`
means that `(Z · D) = r` for every real 1-cycle `Z` with `[Z] = z`. -/
@[mmp "def_km1b_class_divisor_pairing"]
def NumericalCurveClasses.IntersectionNumberEq (z : NumericalCurveClasses sX)
    (D : KCartierDivisor ℝ X) (r : ℝ) : Prop :=
  ∀ Z : OneCycle ℝ sX, OneCycle.numericalClass sX Z = z → Z.intersectionNumber D = r

/-- `(z · D) = r` holds exactly for the value `r` of the linear form
`MMP.Mori.NumericalCurveClasses.intersectionNumber D` at `z`. -/
theorem NumericalCurveClasses.intersectionNumberEq_iff (z : NumericalCurveClasses sX)
    (D : KCartierDivisor ℝ X) (r : ℝ) :
    z.IntersectionNumberEq D r ↔ NumericalCurveClasses.intersectionNumber D z = r := by
  refine ⟨fun h => ?_, fun h Z hZ => ?_⟩
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    exact h Z rfl
  · rw [← h, ← hZ, NumericalCurveClasses.intersectionNumber_numericalClass]

/-- The form `z ↦ (z · 1 · E)` of a Cartier divisor `E` is the degree form of `𝒪_X(E)`. -/
theorem NumericalCurveClasses.intersectionNumber_ofCartier (E : X.CartierDivisor) :
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
      NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E) := by
  apply Submodule.linearMap_qext
  ext C
  simp [NumericalCurveClasses.intersectionNumber, NumericalCurveClasses.degree,
    OneCycle.intersectionPairing, KCartierDivisor.ofCartier, OneCycle.cartierDegree]

/-- The form `z ↦ (z · 1 · E)` of a Cartier divisor `E` lies in `Num(X)`. -/
theorem NumericalCurveClasses.intersectionNumber_ofCartier_mem (E : X.CartierDivisor) :
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) ∈
      numericalDivisorGroup sX := by
  rw [NumericalCurveClasses.intersectionNumber_ofCartier]
  exact NumericalCurveClasses.degree_mem_numericalDivisorGroup sX _

variable (k sX) in
/-- An `ℝ`-Cartier divisor `D` on a `k`-scheme `X` is *nef* if `(C · D) ≥ 0` for every
irreducible curve `C ⊆ X` proper over `k`; when `X` is proper over `k` this is every irreducible
curve (`MMP.Mori.isProperCurve_of_isProper`). -/
@[mmp "def_km1b_nef_real"]
def KCartierDivisor.IsNef (D : KCartierDivisor ℝ X) : Prop :=
  ∀ C : ProperCurve sX, 0 ≤ (C.cycle ℝ).intersectionNumber D

end RealCartier

end Cycles

end MMP.Mori
