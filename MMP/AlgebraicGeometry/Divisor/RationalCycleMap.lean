module

public import MMP.AlgebraicGeometry.Divisor.OrderPullback

/-!
# The cycle map with real and rational coefficients (Lazarsfeld Rem. 9.1.3)

Let `X` be a Noetherian scheme of pure dimension `n`. Tensoring the cycle map
`Div(X) → WDiv(X)`, `D ↦ [D]`, with a coefficient ring `R` gives the cycle map
`Div_R(X) = Div(X) ⊗ R → WDiv(X) ⊗ R`, `∑ cᵢ Aᵢ ↦ ∑ cᵢ [Aᵢ]`. It commutes with multiplication of
the coefficients by elements of `R` and with every change of coefficients `R → S`, in particular
with `ℚ ⊆ ℝ`.

When the cycle map `Div(X) → WDiv(X)` is bijective (Lazarsfeld: on a non-singular variety), its
extension `Div_R(X) → WDiv_R(X)` is an isomorphism, and the real cycle map carries the
`ℚ`-divisors `Div_ℚ(X) ⊆ Div_ℝ(X)` onto the Weil `ℚ`-divisors `WDiv_ℚ(X) ⊆ WDiv_ℝ(X)`. If moreover
every prime divisor is the Weil divisor of an effective Cartier divisor, an `R`-divisor
(`R` an ordered ring) is effective if and only if its Weil divisor has non-negative coefficients.

## Main definitions

* `MMP.Intersection.CartierDivisorWithCoeffs.cycleMap`: the cycle map
  `Div_R(X) →ₗ[ℤ] WDiv(X) ⊗ R`.
* `MMP.Intersection.CartierDivisorWithCoeffs.cycleMapEquiv`: the cycle map as an isomorphism when
  the integral cycle map is bijective.
* `MMP.Intersection.coeffSMul`, `MMP.Intersection.coeffChange`: multiplication of coefficients by
  a scalar, and change of coefficients along a ring homomorphism, on `M ⊗ R`.

## Main results

* `MMP.Intersection.CartierDivisorWithCoeffs.IsWeilDivisorOf.eq_cycleMap`: the Weil divisor of an
  `R`-divisor relative to any representation is its image under the cycle map.
* `MMP.Intersection.CartierDivisorWithCoeffs.cycleMap_coeffSMul`,
  `MMP.Intersection.CartierDivisorWithCoeffs.cycleMap_coeffChange`: compatibility with scalars and
  with change of coefficients.
* `MMP.Intersection.CartierDivisorWithCoeffs.range_cycleMap_comp_coeffChange_of_bijective`: for a
  bijective integral cycle map, `Div_R(X)` is carried onto `WDiv_R(X)` inside `WDiv_S(X)`.
* `MMP.Intersection.CartierDivisorWithCoeffs.isEffective_iff_of_bijective`: effectivity of an
  `R`-divisor is effectivity of its Weil divisor.

## Implementation notes

The groups of divisors with coefficients are tensor products `M ⊗[ℤ] R` with `R` the right
factor, which carry no `R`-module instance; `R`-linearity is stated through `coeffSMul r`, the
map `m ⊗ s ↦ m ⊗ r s`. The Weil divisor `WDiv(X) ⊗ R` is identified with the finitely supported
`R`-valued functions on the `(n-1)`-dimensional subvarieties by
`MMP.Intersection.weilDivisorTensorEquiv`, and effectivity of a Weil divisor with coefficients is
non-negativity of all these values.

## References

* R. Lazarsfeld, *Positivity in Algebraic Geometry I*, Remarks 1.3.8 and 9.1.3.
-/

@[expose] public noncomputable section

universe u

open TopologicalSpace AlgebraicGeometry TensorProduct

namespace MMP.Intersection

/-! ### Scalars and change of coefficients on `M ⊗[ℤ] R` -/

section Coefficients

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Multiplication of the coefficients by `r ∈ R` on `M ⊗[ℤ] R`: `m ⊗ s ↦ m ⊗ r s`. -/
def coeffSMul {R : Type*} [Ring R] (r : R) : M ⊗[ℤ] R →ₗ[ℤ] M ⊗[ℤ] R :=
  LinearMap.lTensor M (LinearMap.mulLeft ℤ r)

/-- `coeffSMul r` sends `m ⊗ s` to `m ⊗ r s`. -/
@[simp]
theorem coeffSMul_tmul {R : Type*} [Ring R] (r : R) (m : M) (s : R) :
    coeffSMul r (m ⊗ₜ s) = m ⊗ₜ (r * s) := rfl

/-- Change of coefficients `M ⊗[ℤ] R → M ⊗[ℤ] S` along a ring homomorphism `f : R →+* S`. -/
def coeffChange {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    M ⊗[ℤ] R →ₗ[ℤ] M ⊗[ℤ] S :=
  LinearMap.lTensor M f.toAddMonoidHom.toIntLinearMap

/-- `coeffChange f` sends `m ⊗ s` to `m ⊗ f s`. -/
@[simp]
theorem coeffChange_tmul {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (m : M) (s : R) :
    coeffChange f (m ⊗ₜ s) = m ⊗ₜ f s := rfl

/-- For a linear map `φ : M → N`, the map `φ ⊗ R` commutes with `coeffSMul r`. -/
theorem rTensor_coeffSMul {R : Type*} [Ring R] (φ : M →ₗ[ℤ] N) (r : R) (x : M ⊗[ℤ] R) :
    φ.rTensor R (coeffSMul r x) = coeffSMul r (φ.rTensor R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m s => rfl
  | add x y hx hy => simp_all

/-- For a linear map `φ : M → N`, change of coefficients along `f : R →+* S` intertwines `φ ⊗ R`
and `φ ⊗ S`. -/
theorem rTensor_coeffChange {R S : Type*} [Ring R] [Ring S] (φ : M →ₗ[ℤ] N)
    (f : R →+* S) (x : M ⊗[ℤ] R) :
    φ.rTensor S (coeffChange f x) = coeffChange f (φ.rTensor R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m s => rfl
  | add x y hx hy => simp_all

end Coefficients

open scoped Classical in
/-- The coefficient of `V` in the Weil divisor `w ⊗ r` with coefficients in `R` is `w(V) r`. -/
theorem weilDivisorTensorEquiv_tmul_apply {R : Type*} [AddCommGroup R] {X : Scheme.{u}} {n : ℕ}
    (w : WeilDivisor X n) (r : R) (V : Codim1Subvariety X n) :
    weilDivisorTensorEquiv R n (w ⊗ₜ r) V = w V • r :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply w r V

namespace CartierDivisorWithCoeffs

variable {R : Type*} [CommRing R] {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]
  {n : ℕ} (hX : IsPureDimensional X n)

/-! ### The cycle map with coefficients -/

variable (R) in
/-- The cycle map `Div_R(X) → WDiv(X) ⊗ R`, `∑ cᵢ Aᵢ ↦ ∑ cᵢ [Aᵢ]` (Lazarsfeld Rem. 1.3.8),
the cycle map `MMP.Intersection.cycleMap` tensored with `R`. -/
def cycleMap : CartierDivisorWithCoeffs R X →ₗ[ℤ] WeilDivisor X n ⊗[ℤ] R :=
  (MMP.Intersection.cycleMap hX).toIntLinearMap.rTensor R

/-- The cycle map sends `A ⊗ r` to `[A] ⊗ r`. -/
@[simp]
theorem cycleMap_tmul (A : X.CartierDivisor) (r : R) :
    cycleMap R hX (A ⊗ₜ r) = MMP.Intersection.cycleMap hX A ⊗ₜ r := rfl

/-- The cycle map sends the `R`-divisor `A ⊗ 1` of a Cartier divisor `A` to `[A] ⊗ 1`. -/
@[simp]
theorem cycleMap_ofDivisor (A : X.CartierDivisor) :
    cycleMap R hX (ofDivisor R A) = MMP.Intersection.cycleMap hX A ⊗ₜ (1 : R) := rfl

/-- The cycle map commutes with multiplication of the coefficients by a scalar: it is
`R`-linear. -/
theorem cycleMap_coeffSMul (r : R) (D : CartierDivisorWithCoeffs R X) :
    cycleMap R hX (coeffSMul r D) = coeffSMul r (cycleMap R hX D) :=
  rTensor_coeffSMul _ r D

/-- The cycle map commutes with change of coefficients, e.g. along `ℚ ⊆ ℝ`. -/
theorem cycleMap_coeffChange {S : Type*} [CommRing S] (f : R →+* S)
    (D : CartierDivisorWithCoeffs R X) :
    cycleMap S hX (coeffChange f D) = coeffChange f (cycleMap R hX D) :=
  rTensor_coeffChange _ f D

/-- The Weil divisor of an `R`-divisor `D = ∑ cᵢ Aᵢ`, relative to any representation, is the image
of `D` under the cycle map; in particular it does not depend on the representation. -/
theorem IsWeilDivisorOf.eq_cycleMap {D : CartierDivisorWithCoeffs R X} {m : ℕ}
    {c : Fin m → R} {A : Fin m → X.CartierDivisor} {w : WeilDivisor X n ⊗[ℤ] R}
    (h : D.IsWeilDivisorOf c A w) : w = cycleMap R hX D := by
  obtain ⟨hD, wᵢ, hw, rfl⟩ := h
  have hwᵢ : ∀ i, wᵢ i = MMP.Intersection.cycleMap hX (A i) := fun i =>
    DFunLike.coe_injective <| (existsUnique_isWeilDivisorOf hX (A i)).unique (hw i)
      (isWeilDivisorOf_cycleMap hX (A i))
  rw [hD, map_sum]
  simp [hwᵢ]

/-! ### Bijectivity -/

variable (R) in
/-- When the cycle map `Div(X) → WDiv(X)` is bijective, so is its extension
`Div_R(X) → WDiv(X) ⊗ R`. -/
def cycleMapEquiv (h : Function.Bijective (MMP.Intersection.cycleMap hX)) :
    CartierDivisorWithCoeffs R X ≃ₗ[ℤ] WeilDivisor X n ⊗[ℤ] R :=
  LinearEquiv.rTensor R (AddEquiv.ofBijective _ h).toIntLinearEquiv

/-- The isomorphism `cycleMapEquiv` agrees with the cycle map `cycleMap`. -/
@[simp]
theorem cycleMapEquiv_apply (h : Function.Bijective (MMP.Intersection.cycleMap hX))
    (D : CartierDivisorWithCoeffs R X) : cycleMapEquiv R hX h D = cycleMap R hX D := rfl

/-- When the cycle map `Div(X) → WDiv(X)` is bijective, so is the cycle map
`Div_R(X) → WDiv(X) ⊗ R`. -/
theorem cycleMap_bijective (h : Function.Bijective (MMP.Intersection.cycleMap hX)) :
    Function.Bijective (cycleMap R hX) :=
  (cycleMapEquiv R hX h).bijective

/-- When the cycle map `Div(X) → WDiv(X)` is bijective, the cycle map with coefficients in `S`
carries `Div_R(X)` (inside `Div_S(X)` by change of coefficients along `f : R →+* S`) onto
`WDiv(X) ⊗ R` inside `WDiv(X) ⊗ S`; for `ℚ ⊆ ℝ` it carries `Div_ℚ(X)` onto `WDiv_ℚ(X)`. -/
theorem range_cycleMap_comp_coeffChange_of_bijective {S : Type*} [CommRing S] (f : R →+* S)
    (h : Function.Bijective (MMP.Intersection.cycleMap hX)) :
    Set.range (fun D : CartierDivisorWithCoeffs R X => cycleMap S hX (coeffChange f D)) =
      Set.range (coeffChange f : WeilDivisor X n ⊗[ℤ] R → WeilDivisor X n ⊗[ℤ] S) := by
  ext w
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨cycleMap R hX D, (cycleMap_coeffChange hX f D).symm⟩
  · rintro ⟨w', rfl⟩
    obtain ⟨D, rfl⟩ := (cycleMap_bijective (R := R) hX h).2 w'
    exact ⟨D, cycleMap_coeffChange hX f D⟩

/-! ### Effectivity -/

open scoped Classical in
/-- The coefficient of an `(n-1)`-dimensional subvariety `V` in the Weil divisor `[D]` of an
`R`-divisor `D = ∑ cᵢ Aᵢ` is `∑ ord_V(Aᵢ) cᵢ`. -/
theorem weilDivisorTensorEquiv_cycleMap_sum {m : ℕ} (c : Fin m → R)
    (A : Fin m → X.CartierDivisor) (V : Codim1Subvariety X n) :
    weilDivisorTensorEquiv R n (cycleMap R hX (∑ i, A i ⊗ₜ c i)) V =
      ∑ i, (MMP.Intersection.cycleMap hX (A i) V : R) * c i := by
  rw [map_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cycleMap_tmul, weilDivisorTensorEquiv_tmul_apply, zsmul_eq_mul]

variable [PartialOrder R] [IsOrderedRing R]

open scoped Classical in
/-- The Weil divisor of an effective `R`-divisor has non-negative coefficients. -/
theorem IsEffective.cycleMap_nonneg {D : CartierDivisorWithCoeffs R X} (hD : D.IsEffective)
    (V : Codim1Subvariety X n) : 0 ≤ weilDivisorTensorEquiv R n (cycleMap R hX D) V := by
  obtain ⟨m, c, A, rfl, hcA⟩ := hD
  rw [weilDivisorTensorEquiv_cycleMap_sum]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (hcA i).1
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le
    ((isWeilDivisorOf_cycleMap hX (A i)).nonneg_of_isEffective (hcA i).2 V)
  rw [hk, Int.cast_natCast]
  exact Nat.cast_nonneg k

open scoped Classical in
/-- When the cycle map `Div(X) → WDiv(X)` is bijective and every `(n-1)`-dimensional subvariety
is the Weil divisor of an effective Cartier divisor, an `R`-divisor is effective if and only if
its Weil divisor has non-negative coefficients. -/
theorem isEffective_iff_of_bijective (h : Function.Bijective (MMP.Intersection.cycleMap hX))
    (heff : ∀ V : Codim1Subvariety X n, ∃ C : X.CartierDivisor,
      MMP.Intersection.IsEffective C ∧ MMP.Intersection.cycleMap hX C = Finsupp.single V 1)
    (D : CartierDivisorWithCoeffs R X) :
    D.IsEffective ↔ ∀ V, 0 ≤ weilDivisorTensorEquiv R n (cycleMap R hX D) V := by
  refine ⟨fun hD V => hD.cycleMap_nonneg hX V, fun hw => ?_⟩
  choose C hC hCV using heff
  set w := weilDivisorTensorEquiv R n (cycleMap R hX D)
  let e := w.support.equivFin
  let V : Fin w.support.card → Codim1Subvariety X n := fun i => (e.symm i : _)
  refine ⟨w.support.card, fun i => w (V i), fun i => C (V i), ?_, fun i => ⟨hw _, hC _⟩⟩
  apply (cycleMap_bijective (R := R) hX h).1
  apply (weilDivisorTensorEquiv R n).injective
  ext W
  rw [weilDivisorTensorEquiv_cycleMap_sum]
  simp only [hCV, Finsupp.single_apply]
  change w W = _
  rw [e.symm.sum_comp (fun x : w.support => ((if (x : Codim1Subvariety X n) = W then 1 else 0 :
    ℤ) : R) * w x), Finset.sum_coe_sort w.support (fun x => ((if x = W then 1 else 0 : ℤ) : R) *
    w x)]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with hW
  · rfl
  · exact not_not.mp hW

end CartierDivisorWithCoeffs

end MMP.Intersection
