module

public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.PairComposition
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.AlgebraSheaf
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# The cyclic cover defined by a Weil divisor

Let `X` be a Noetherian normal scheme, `M` a Weil divisor on `X`, `m ≥ 1` and `φ ∈ K(X)^×` with
`div(φ) + mM` effective. The *cyclic cover defined by `(M, m, φ)`* is `p : Z = Spec_X 𝒜 → X` for
the `𝒪_X`-algebra
`𝒜 = ⊕_{i=0}^{m-1} 𝒪_X(-iM) eᵢ`, `(a eᵢ)(b eⱼ) = ab eᵢ₊ⱼ` if `i + j < m`, `= φab eᵢ₊ⱼ₋ₘ` if
`i + j ≥ m`, the products being products of rational functions (`φ 𝒪_X(-(i+j)M) ⊆
𝒪_X(-(i+j-m)M)` because `div(φ) + mM ≥ 0`). The group `μ_m` acts on `Z` over `X` by
`ζ · (a eᵢ) = ζⁱ a eᵢ`.

## Main definitions

* `MMP.Mori.DivisorialCyclicCover.algebraSheaf`: the `𝒪_X`-algebra `𝒜`.
* `MMP.Mori.DivisorialCyclicCover.cover`, `MMP.Mori.DivisorialCyclicCover.toBase`: the cyclic
  cover `p : Z = Spec_X 𝒜 → X`.
* `MMP.Mori.DivisorialCyclicCover.scaleSections`: the automorphism `σ_ζ` of `𝒜`.
* `MMP.Mori.DivisorialCyclicCover.scaling`, `MMP.Mori.DivisorialCyclicCover.scalingIso`: the
  `X`-automorphism `α_ζ` of `Z`, for `ζ ∈ Γ(X, 𝒪_X)^×` with `ζᵐ = 1`.

## Main results

* `MMP.Mori.DivisorialCyclicCover.mem_carrier_iff`, `MMP.Mori.DivisorialCyclicCover.coeffEquiv`:
  `𝒜(U) = ⊕_{i<m} 𝒪_X(-iM)(U) eᵢ`.
* `MMP.Mori.DivisorialCyclicCover.reduce_monomial_mul`,
  `MMP.Mori.DivisorialCyclicCover.reduce_monomial_of_le`: the multiplication rule of `𝒜`.
* `MMP.Mori.DivisorialCyclicCover.isQuasicoherent_algebraSheaf`: `𝒜` is quasi-coherent.
* `MMP.Mori.DivisorialCyclicCover.scaleSections_reduce_monomial`: `ζ · (a eₖ) = ζᵏ a eₖ`.
* `MMP.Mori.DivisorialCyclicCover.scaling_appLE`: `α_ζ^* = σ_ζ`.
* `MMP.Mori.DivisorialCyclicCover.scaling_comp`, `MMP.Mori.DivisorialCyclicCover.scaling_one`:
  `ζ ↦ α_ζ` is an action of `μ_m`.

## Implementation notes

The sections of `𝒜` over `U` are realized inside `∏_{η_Z ∈ U} K(Z)[t]/(tᵐ - φ_Z)`, the product
over the irreducible components `Z` meeting `U` (the factors of `𝒦_X(U)`), with `eᵢ = tⁱ`: they
are the images of the polynomials `∑ₖ aₖ tᵏ` with `aₖ ∈ 𝒪_X(-kM)(U)`. That these are exactly the
`∑_{i<m} aᵢ tⁱ` with `aᵢ ∈ 𝒪_X(-iM)(U)` (`mem_carrier_iff`) is where `div(φ) + mM ≥ 0` enters,
through `tᵏ = φ^{⌊k/m⌋} t^{k mod m}`. The multiplication is then that of the quotient ring, which
is the rule above. The ambient product is a sheaf and membership is local, so `𝒜` is a sheaf of
`𝒪_X`-algebras (`MMP.Mori.LocalSubalgebra`); it is quasi-coherent because each `𝒪_X(-iM)` is.

The roots of unity are taken among the global units `ζ ∈ Γ(X, 𝒪_X)^×` with `ζᵐ = 1`; for a
variety over a field `k` these include the `ζ ∈ k` with `ζᵐ = 1`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.52, 5.19,
  5.25
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Polynomial
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace MMP.Mori

namespace DivisorialCyclicCover

/-! ### The algebra `K(Z)[t]/(tᵐ - φ)` on each irreducible component -/

section Fiber

variable {X : Scheme.{u}} (m : ℕ) [NeZero m] (φ : (RationalFunctions X)ˣ)

/-- The polynomial `tᵐ - φ_Z` over the factor `𝒪_{X,η_Z}` of `K(X)` at an irreducible
component `Z`. -/
def poly (Z : irreducibleComponents X) : (X.presheaf.stalk (componentGenericPoint X Z))[X] :=
  Polynomial.X ^ m - C ((φ : RationalFunctions X) Z)

/-- The polynomial `tᵐ - φ_Z` is monic. -/
theorem poly_monic (Z : irreducibleComponents X) : (poly m φ Z).Monic :=
  monic_X_pow_sub_C _ (NeZero.ne m)

/-- The polynomial `tᵐ - φ_Z` has degree `m`. -/
theorem degree_poly (Z : irreducibleComponents X) : (poly m φ Z).degree = m :=
  degree_X_pow_sub_C (NeZero.pos m) _

/-- The algebra `𝒪_{X,η_Z}[t]/(tᵐ - φ_Z)` on an irreducible component `Z`. -/
abbrev Fiber (Z : irreducibleComponents X) : Type u := AdjoinRoot (poly m φ Z)

omit [NeZero m] in
/-- In `Fiber m φ Z`, the root `t` satisfies `tᵐ = φ_Z`. -/
theorem root_pow_m (Z : irreducibleComponents X) :
    AdjoinRoot.root (poly m φ Z) ^ m = AdjoinRoot.of _ ((φ : RationalFunctions X) Z) := by
  have h := AdjoinRoot.mk_self (f := poly m φ Z)
  rw [poly, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

omit [NeZero m] in
/-- In `Fiber m φ Z`, `tᵏ = φ_Z^{⌊k/m⌋} t^{k mod m}`. -/
theorem root_pow (Z : irreducibleComponents X) (k : ℕ) :
    AdjoinRoot.root (poly m φ Z) ^ k =
      AdjoinRoot.of _ ((φ : RationalFunctions X) Z ^ (k / m)) *
        AdjoinRoot.root (poly m φ Z) ^ (k % m) := by
  conv_lhs => rw [← Nat.div_add_mod k m]
  rw [pow_add, pow_mul, root_pow_m, map_pow]

/-- The reduction of `c tᵏ` modulo `tᵐ - φ_Z` is `c φ_Z^{⌊k/m⌋} t^{k mod m}`. -/
theorem modByMonicHom_mk_monomial (Z : irreducibleComponents X) (k : ℕ)
    (c : X.presheaf.stalk (componentGenericPoint X Z)) :
    AdjoinRoot.modByMonicHom (poly_monic m φ Z) (AdjoinRoot.mk _ (monomial k c)) =
      monomial (k % m) (c * (φ : RationalFunctions X) Z ^ (k / m)) := by
  have h : AdjoinRoot.mk (poly m φ Z) (monomial k c) =
      AdjoinRoot.mk _ (monomial (k % m) (c * (φ : RationalFunctions X) Z ^ (k / m))) := by
    simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      root_pow m φ Z k]
    ring
  rw [h, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (poly_monic m φ Z)).mpr]
  calc (monomial (k % m) _).degree ≤ ((k % m : ℕ) : WithBot ℕ) := degree_monomial_le _ _
    _ < m := by exact_mod_cast Nat.mod_lt k (NeZero.pos m)
    _ = (poly m φ Z).degree := (degree_poly m φ Z).symm

/-- The reduction modulo `tᵐ - φ_Z` of an element of `Fiber m φ Z` has degree less than `m`. -/
theorem natDegree_modByMonicHom_lt (Z : irreducibleComponents X) (x : Fiber m φ Z) :
    (AdjoinRoot.modByMonicHom (poly_monic m φ Z) x).natDegree < m := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.modByMonicHom_mk]
  have hne : poly m φ Z ≠ 1 := fun h => by
    have := degree_poly m φ Z
    rw [h, degree_one] at this
    exact NeZero.ne m (by exact_mod_cast this.symm)
  have := natDegree_modByMonic_lt p (poly_monic m φ Z) hne
  exact this.trans_eq (by rw [poly, natDegree_X_pow_sub_C])

end Fiber

/-! ### The ambient sheaf `U ↦ ∏_{η_Z ∈ U} K(Z)[t]/(tᵐ - φ_Z)` -/

section Ambient

variable {X : Scheme.{u}} (m : ℕ) [NeZero m] (φ : (RationalFunctions X)ˣ)

/-- The presheaf of rings `𝓛 : U ↦ ∏_{η_Z ∈ U} 𝒪_{X,η_Z}[t]/(tᵐ - φ_Z)`, the product over the
irreducible components meeting `U`, with the projections as restriction maps. -/
def ambient : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of
    (∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.unop}, Fiber m φ Z.1)
  map {U _} i := CommRingCat.ofHom
    (RingHom.pi fun Z => Pi.evalRingHom
      (fun Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.unop} =>
        Fiber m φ Z.1) ⟨Z.1, i.unop.le Z.2⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

omit [NeZero m] in
/-- The restriction maps of `ambient m φ` are the projections onto the components meeting the
smaller open. -/
@[simp]
theorem ambient_map_apply {U V : X.Opens} (i : V ⟶ U) (s : (ambient m φ).obj (op U))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V}) :
    (ambient m φ).map i.op s Z = s ⟨Z.1, i.le Z.2⟩ := rfl

omit [NeZero m] in
/-- The presheaf `ambient m φ` is a sheaf. -/
theorem isSheaf_ambient : (ambient m φ).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hmem : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ iSup U →
      ∃ i, componentGenericPoint X Z ∈ U i := fun Z h => Opens.mem_iSup.mp h
  have hagree : ∀ (i j : ι) (Z : irreducibleComponents X) (hi : componentGenericPoint X Z ∈ U i)
      (hj : componentGenericPoint X Z ∈ U j), sf i ⟨Z, hi⟩ = sf j ⟨Z, hj⟩ := by
    intro i j Z hi hj
    exact congrFun (hsf i j) ⟨Z, ⟨hi, hj⟩⟩
  refine ⟨fun Z => sf (hmem Z.1 Z.2).choose ⟨Z.1, (hmem Z.1 Z.2).choose_spec⟩, ?_, ?_⟩
  · intro i
    funext Z
    exact hagree _ _ _ _ _
  · intro s hs
    funext Z
    have := congrFun (hs (hmem Z.1 Z.2).choose) ⟨Z.1, (hmem Z.1 Z.2).choose_spec⟩
    exact this.symm ▸ rfl

/-- The inclusion `𝒦_X ⟶ 𝓛` of the constants. -/
def ofRationalFunctions : rationalFunctionsPresheaf X ⟶ ambient m φ where
  app _ := CommRingCat.ofHom (RingHom.pi fun Z => (AdjoinRoot.of _).comp (Pi.evalRingHom _ Z))
  naturality _ _ _ := rfl

/-- The structure morphism `𝒪_X ⟶ 𝓛`. -/
def structureMap : X.presheaf ⟶ ambient m φ :=
  toRationalFunctionsPresheaf X ≫ ofRationalFunctions m φ

/-- The component at `Z` of a section of `𝒦_X` over `U`. -/
def evalAt {U : X.Opens} (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    (rationalFunctionsPresheaf X).obj (op U) →+* X.presheaf.stalk (componentGenericPoint X Z.1) :=
  Pi.evalRingHom _ Z

/-- `evalAt Z f` is the component of `f` at `Z`. -/
theorem evalAt_apply {U : X.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U})
    (f : (rationalFunctionsPresheaf X).obj (op U)) : evalAt Z f = f Z := rfl

/-- The reduction `𝒦_X(U)[t] → 𝓛(U)`, componentwise the quotient map
`𝒪_{X,η_Z}[t] → 𝒪_{X,η_Z}[t]/(tᵐ - φ_Z)`. -/
def reduce (U : X.Opens) :
    ((rationalFunctionsPresheaf X).obj (op U))[X] →+* (ambient m φ).obj (op U) :=
  RingHom.pi fun Z => (AdjoinRoot.mk _).comp (mapRingHom (evalAt Z))

omit [NeZero m] in
/-- The component at `Z` of `reduce m φ U p` is the class of the image of `p` in
`𝒪_{X,η_Z}[t]/(tᵐ - φ_Z)`. -/
theorem reduce_apply {U : X.Opens} (p : ((rationalFunctionsPresheaf X).obj (op U))[X])
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    reduce m φ U p Z = AdjoinRoot.mk _ (p.map (evalAt Z)) := rfl

omit [NeZero m] in
/-- Reduction commutes with restriction: the restriction to `V` of `reduce m φ U p` is the
reduction of `p` with its coefficients restricted to `V`. -/
theorem ambient_map_reduce {U V : X.Opens} (i : V ⟶ U)
    (p : ((rationalFunctionsPresheaf X).obj (op U))[X]) :
    (ambient m φ).map i.op (reduce m φ U p) =
      reduce m φ V (p.map ((rationalFunctionsPresheaf X).map i.op).hom) := by
  funext Z
  rw [ambient_map_apply, reduce_apply, reduce_apply, Polynomial.map_map]
  rfl

/-- The coefficient of `tⁿ` of a section of `𝓛` over `U`, in the basis `1, t, …, tᵐ⁻¹`, as a
section of `𝒦_X` over `U`. -/
def coeff (U : X.Opens) (n : ℕ) :
    (ambient m φ).obj (op U) →+ (rationalFunctionsPresheaf X).obj (op U) :=
  AddMonoidHom.pi fun Z =>
    ((lcoeff _ n).comp (AdjoinRoot.modByMonicHom (poly_monic m φ Z.1))).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom _ Z)

/-- The component at `Z` of `coeff m φ U n x` is the coefficient of `tⁿ` of the reduction of `x Z`
modulo `tᵐ - φ_Z`. -/
theorem coeff_apply {U : X.Opens} (n : ℕ) (x : (ambient m φ).obj (op U))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    coeff m φ U n x Z = (AdjoinRoot.modByMonicHom (poly_monic m φ Z.1) (x Z)).coeff n := rfl

/-- Taking the coefficient of `tⁿ` commutes with restriction. -/
theorem coeff_map {U V : X.Opens} (i : V ⟶ U) (n : ℕ) (x : (ambient m φ).obj (op U)) :
    coeff m φ V n ((ambient m φ).map i.op x) =
      (rationalFunctionsPresheaf X).map i.op (coeff m φ U n x) := rfl

/-- The rational function `φ` restricted to `U`. -/
def phiOn (U : X.Opens) : (rationalFunctionsPresheaf X).obj (op U) :=
  fun Z => (φ : RationalFunctions X) Z.1

/-- The coefficient of `tⁿ` of `a tᵏ` is `a φ^{⌊k/m⌋}` if `k mod m = n`, and `0` otherwise. -/
theorem coeff_reduce_monomial {U : X.Opens} (k n : ℕ)
    (a : (rationalFunctionsPresheaf X).obj (op U)) :
    coeff m φ U n (reduce m φ U (monomial k a)) =
      if k % m = n then a * phiOn φ U ^ (k / m) else 0 := by
  funext Z
  rw [coeff_apply, reduce_apply, Polynomial.map_monomial, modByMonicHom_mk_monomial,
    coeff_monomial]
  split_ifs <;> rfl

/-- For `k < m`, the coefficient of `tⁿ` of `a tᵏ` is `a` if `k = n`, and `0` otherwise. -/
theorem coeff_reduce_monomial_of_lt {U : X.Opens} {k : ℕ} (hk : k < m) (n : ℕ)
    (a : (rationalFunctionsPresheaf X).obj (op U)) :
    coeff m φ U n (reduce m φ U (monomial k a)) = if k = n then a else 0 := by
  rw [coeff_reduce_monomial, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk, pow_zero, mul_one]

/-- A section `x` of the ambient sheaf is `∑_{n<m} cₙ tⁿ`, where `cₙ` is its coefficient of
`tⁿ`. -/
theorem reduce_sum_coeff {U : X.Opens} (x : (ambient m φ).obj (op U)) :
    reduce m φ U (∑ n ∈ Finset.range m, monomial n (coeff m φ U n x)) = x := by
  funext Z
  rw [reduce_apply, Polynomial.map_sum]
  simp only [Polynomial.map_monomial]
  conv_rhs => rw [← AdjoinRoot.mk_leftInverse (poly_monic m φ Z.1) (x Z)]
  congr 1
  exact ((AdjoinRoot.modByMonicHom (poly_monic m φ Z.1) (x Z)).as_sum_range' m
    (natDegree_modByMonicHom_lt m φ Z.1 (x Z))).symm

/-- The coefficient of `tⁿ` of `∑_{i<m} aᵢ tⁱ` is `aₙ` for `n < m`, and `0` otherwise. -/
theorem coeff_reduce_sum {U : X.Opens} (a : Fin m → (rationalFunctionsPresheaf X).obj (op U))
    (n : ℕ) :
    coeff m φ U n (reduce m φ U (∑ i : Fin m, monomial i (a i))) =
      if h : n < m then a ⟨n, h⟩ else 0 := by
  rw [map_sum, map_sum]
  simp only [fun i : Fin m => coeff_reduce_monomial_of_lt m φ i.2 n (a i)]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩ (fun b _ hb => ite_eq_right fun e => hb (Fin.ext e))
      (fun h' => absurd (Finset.mem_univ _) h'), ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun i _ => ite_eq_right fun e : (i : ℕ) = n => h (e ▸ i.2)

/-- The coefficient of `tⁿ` of `r x`, for `r ∈ 𝒪_X(U)`, is `r` times the coefficient of `tⁿ` of
`x`. -/
theorem coeff_structureMap_mul {U : X.Opens} (r : Γ(X, U)) (x : (ambient m φ).obj (op U))
    (n : ℕ) :
    coeff m φ U n (((structureMap m φ).app (op U)).hom r * x) = r • coeff m φ U n x := by
  funext Z
  rw [coeff_apply, rationalFunctions_smul_apply]
  change (AdjoinRoot.modByMonicHom (poly_monic m φ Z.1)
      (AdjoinRoot.of _ (X.presheaf.germ U _ Z.2 r) * x Z)).coeff n = _
  rw [← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def, map_smul, coeff_smul, smul_eq_mul]
  rfl

omit [NeZero m] in
/-- The product of `a tⁱ` and `b tʲ` is `ab tⁱ⁺ʲ`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
theorem reduce_monomial_mul {U : X.Opens} (i j : ℕ)
    (a b : (rationalFunctionsPresheaf X).obj (op U)) :
    reduce m φ U (monomial i a) * reduce m φ U (monomial j b) =
      reduce m φ U (monomial (i + j) (a * b)) := by
  rw [← map_mul, monomial_mul_monomial]

omit [NeZero m] in
/-- `c tᵏ = φc tᵏ⁻ᵐ` for `k ≥ m`: together with
`MMP.Mori.DivisorialCyclicCover.reduce_monomial_mul` this is the multiplication rule
`(a eᵢ)(b eⱼ) = φab eᵢ₊ⱼ₋ₘ` for `i + j ≥ m`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
theorem reduce_monomial_of_le {U : X.Opens} {k : ℕ} (hk : m ≤ k)
    (c : (rationalFunctionsPresheaf X).obj (op U)) :
    reduce m φ U (monomial k c) = reduce m φ U (monomial (k - m) (phiOn φ U * c)) := by
  funext Z
  rw [reduce_apply, reduce_apply, Polynomial.map_monomial, Polynomial.map_monomial,
    ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  conv_lhs => rw [← Nat.sub_add_cancel hk, pow_add, root_pow_m]
  change _ = AdjoinRoot.of _ ((φ : RationalFunctions X) Z.1) * _ * _
  ring

end Ambient

/-! ### The algebra `𝒜 = ⊕_{i<m} 𝒪_X(-iM) eᵢ` -/

section Algebra

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (M : Divisor X) {φ : (RationalFunctions X)ˣ}
  (hφ : 0 ≤ principalDivisor φ + m • M)

omit [NeZero m] in
include hφ in
/-- `φ^q` is a section of `𝒪_X(q m M)`, since `div(φ) + mM` is effective. -/
theorem isDivisorialSection_phiOn_pow (U : X.Opens) (q : ℕ) :
    (q • (m • M)).IsDivisorialSection U (phiOn φ U ^ q) := by
  intro E hE
  have hval : (phiOn φ U ^ q) ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
      ((φ ^ q : (RationalFunctions X)ˣ) : RationalFunctions X) E.component := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  rw [hval]
  refine PrimeDivisor.OrdGE.mono
    (show E.OrdGE (E.ord (φ ^ q)) _ from Or.inr (E.valuation_component (φ ^ q)).ge) ?_
  have h0 : 0 ≤ E.ord φ + (m : ℤ) * M.coeff E := by
    have := hφ E
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at this
    exact this
  rw [E.ord_pow, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul]
  simp only [nsmul_eq_mul]
  nlinarith [mul_nonneg (Int.natCast_nonneg q) h0]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [NeZero m] in
/-- `k • (-M) + ⌊k/m⌋ • (m • M) = (k mod m) • (-M)`. -/
theorem nsmul_neg_add_nsmul (k : ℕ) :
    k • -M + (k / m) • (m • M) = (k % m) • -M := by
  have hk : (k : ℤ) = ((k % m : ℕ) : ℤ) + (m : ℤ) * ((k / m : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div k m).symm
  ext E
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_neg, nsmul_eq_mul]
  linear_combination (-M.coeff E) * hk

include hφ in
/-- If `p` is a section of the divisorial algebra `⊕_{k ≥ 0} 𝒪_X(-kM) tᵏ`, the coefficient of `tⁿ`
of its reduction is a section of `𝒪_X(-nM)`. -/
theorem coeff_reduce_mem {U : X.Opens} {p : ((rationalFunctionsPresheaf X).obj (op U))[X]}
    (hp : p ∈ (-M).divisorialAlgebraSections U) (n : ℕ) :
    coeff m φ U n (reduce m φ U p) ∈ (n • -M).divisorialSubmodule U := by
  rw [p.as_sum_support, map_sum, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [coeff_reduce_monomial]
  split_ifs with hk
  · subst hk
    have := Divisor.IsDivisorialSection.mul (hp k) (isDivisorialSection_phiOn_pow m M hφ U (k / m))
    rwa [nsmul_neg_add_nsmul] at this
  · exact Submodule.zero_mem _

omit [CompactSpace X] in
/-- If the coefficient `cₙ` of `tⁿ` of `x` is a section of `𝒪_X(-nM)` for every `n`, then
`∑_{n<m} cₙ tⁿ` is a section of the divisorial algebra `⊕_{k ≥ 0} 𝒪_X(-kM) tᵏ`. -/
theorem sum_monomial_coeff_mem {U : X.Opens} {x : (ambient m φ).obj (op U)}
    (hx : ∀ n, coeff m φ U n x ∈ (n • -M).divisorialSubmodule U) :
    ∑ n ∈ Finset.range m, monomial n (coeff m φ U n x) ∈ (-M).divisorialAlgebraSections U :=
  fun k => by
    rw [finsetSum_coeff]
    refine Submodule.sum_mem _ fun n _ => ?_
    rw [coeff_monomial]
    split_ifs with h
    · subst h
      exact hx n
    · exact Submodule.zero_mem _

/-- The sections `𝒜(U) ⊆ 𝓛(U)` of the cyclic cover algebra over `U`: the reductions of the
sections `∑ aₖ tᵏ` of the divisorial algebra `⊕_{k ≥ 0} 𝒪_X(-kM)tᵏ`. -/
def carrier (U : X.Opens) : Subring ((ambient m φ).obj (op U)) :=
  ((-M).divisorialAlgebraSections U).toSubring.map (reduce m φ U)

include hφ in
/-- **A section of `𝓛` lies in `𝒜` if and only if its coefficient of `tⁱ` is a section of
`𝒪_X(-iM)` for every `i`**, that is, `𝒜(U) = ⊕_{i<m} 𝒪_X(-iM)(U) tⁱ`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
theorem mem_carrier_iff {U : X.Opens} {x : (ambient m φ).obj (op U)} :
    x ∈ carrier m M U ↔ ∀ n, coeff m φ U n x ∈ (n • -M).divisorialSubmodule U := by
  constructor
  · rintro ⟨p, hp, rfl⟩ n
    exact coeff_reduce_mem m M hφ hp n
  · intro hx
    exact ⟨_, sum_monomial_coeff_mem m M hx, reduce_sum_coeff m φ x⟩

/-- The cyclic cover algebra as a local family of subalgebras of `𝓛`. -/
def localSubalgebra : LocalSubalgebra (ambient m φ) (structureMap m φ) where
  carrier := carrier m M
  algebraMap_mem := fun {U} r => by
    refine ⟨algebraMap Γ(X, U) _ r, Subalgebra.algebraMap_mem _ r, ?_⟩
    funext Z
    rw [reduce_apply, Polynomial.algebraMap_apply, Polynomial.map_C, AdjoinRoot.mk_C]
    rfl
  map_mem := fun {U V} i {x} hx => by
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨_, Divisor.map_mem_divisorialAlgebraSections (-M) i hp,
      (ambient_map_reduce m φ i p).symm⟩
  mem_of_locally := fun {U} {x} hx => by
    rw [mem_carrier_iff m M hφ]
    intro n
    rw [Divisor.mem_divisorialSubmodule]
    intro E hE
    obtain ⟨y, hyE, hyU⟩ := hE
    obtain ⟨V, i, hyV, hV⟩ := hx y hyU
    rw [mem_carrier_iff m M hφ] at hV
    exact hV n E ⟨y, hyE, hyV⟩

end Algebra

/-! ### `𝒜 = ⊕_{i<m} 𝒪_X(-iM)` and quasi-coherence -/

section Quasicoherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (M : Divisor X) {φ : (RationalFunctions X)ˣ}
  (hφ : 0 ≤ principalDivisor φ + m • M)

/-- **The decomposition `𝒜(V) = ⊕_{i<m} 𝒪_X(-iM)(V)`**: a section of `𝒜` over `V` is the
family of its coefficients in the basis `1, t, …, tᵐ⁻¹`. -/
def coeffEquiv (V : X.Opens) :
    (localSubalgebra m M hφ).carrier V ≃ (∀ i : Fin m, Γ(((i : ℕ) • -M).divisorialSheaf, V)) where
  toFun x i := (⟨coeff m φ V i x.1, (mem_carrier_iff m M hφ).mp x.2 i⟩ :
    ((i : ℕ) • -M).divisorialSubmodule V)
  invFun a := ⟨reduce m φ V (∑ i : Fin m, monomial i (Divisor.secVal _ V (a i))),
    (mem_carrier_iff m M hφ).mpr fun n => by
      rw [coeff_reduce_sum]
      split_ifs with h
      · exact (a ⟨n, h⟩ : ((n : ℕ) • -M).divisorialSubmodule V).2
      · exact Submodule.zero_mem _⟩
  left_inv x := Subtype.ext <| by
    change reduce m φ V (∑ i : Fin m, monomial (i : ℕ) (coeff m φ V i x.1)) = x.1
    rw [Fin.sum_univ_eq_sum_range (fun n => monomial n (coeff m φ V n x.1))]
    exact reduce_sum_coeff m φ x.1
  right_inv a := funext fun i => Subtype.ext <| by
    change coeff m φ V i (reduce m φ V (∑ i : Fin m, monomial i (Divisor.secVal _ V (a i)))) = _
    rw [coeff_reduce_sum, dite_eq_left i.2]

/-- The `i`-th component of `coeffEquiv m M hφ V x` is the coefficient of `tⁱ` of `x`. -/
theorem coeff_coeffEquiv (V : X.Opens) (x : (localSubalgebra m M hφ).carrier V) (i : Fin m) :
    Divisor.secVal _ V (coeffEquiv m M hφ V x i) = coeff m φ V i x.1 := rfl

/-- `coeffEquiv` is additive. -/
theorem coeffEquiv_add (V : X.Opens) (x y : (localSubalgebra m M hφ).carrier V) :
    coeffEquiv m M hφ V (x + y) = coeffEquiv m M hφ V x + coeffEquiv m M hφ V y :=
  funext fun i => Subtype.ext (map_add (coeff m φ V i) x.1 y.1)

/-- `coeffEquiv` commutes with multiplication by sections of `𝒪_X` over `V`. -/
theorem coeffEquiv_smul (V : X.Opens) (r : Γ(X, V)) (x : (localSubalgebra m M hφ).carrier V) :
    coeffEquiv m M hφ V ((localSubalgebra m M hφ).algebraMap V r * x) =
      r • coeffEquiv m M hφ V x :=
  funext fun i => Subtype.ext (coeff_structureMap_mul m φ r x.1 i)

/-- The decomposition `𝒜(U) ≅ ⊕_{i<m} 𝒪_X(-iM)(U)` as an isomorphism of `𝒪_X(U)`-modules. -/
def coeffLinearEquiv (U : X.Opens) :
    letI := (localSubalgebra m M hφ).moduleSections U
    (localSubalgebra m M hφ).carrier U ≃ₗ[Γ(X, U)]
      (∀ i : Fin m, Γ(((i : ℕ) • -M).divisorialSheaf, U)) :=
  letI := (localSubalgebra m M hφ).moduleSections U
  (coeffEquiv m M hφ U).toLinearEquiv
    { map_add := coeffEquiv_add m M hφ U
      map_smul := fun r x => coeffEquiv_smul m M hφ U r x }

/-- The decomposition `𝒜(V) ≅ ⊕_{i<m} 𝒪_X(-iM)(V)`, `V ⊆ U`, as an isomorphism of
`𝒪_X(U)`-modules. -/
def coeffLinearEquivOfLE {U V : X.Opens} (h : V ≤ U) :
    letI := (localSubalgebra m M hφ).moduleOfLE h
    letI : ∀ i : Fin m, Module Γ(X, U) Γ(((i : ℕ) • -M).divisorialSheaf, V) :=
      fun _ => moduleOfLE _ h
    (localSubalgebra m M hφ).carrier V ≃ₗ[Γ(X, U)]
      (∀ i : Fin m, Γ(((i : ℕ) • -M).divisorialSheaf, V)) :=
  letI := (localSubalgebra m M hφ).moduleOfLE h
  letI : ∀ i : Fin m, Module Γ(X, U) Γ(((i : ℕ) • -M).divisorialSheaf, V) :=
    fun _ => moduleOfLE _ h
  (coeffEquiv m M hφ V).toLinearEquiv
    { map_add := coeffEquiv_add m M hφ V
      map_smul := fun r x => coeffEquiv_smul m M hφ V ((X.presheaf.map (homOfLE h).op).hom r) x }

/-- Under the decompositions `coeffLinearEquiv` and `coeffLinearEquivOfLE`, the restriction
`𝒜(U) → 𝒜(V)` is the product of the restrictions of the sheaves `𝒪_X(-iM)`. -/
theorem restrictₗ_eq {U V : X.Opens} (h : V ≤ U) :
    letI := (localSubalgebra m M hφ).moduleSections U
    letI := (localSubalgebra m M hφ).moduleOfLE h
    letI : ∀ i : Fin m, Module Γ(X, U) Γ(((i : ℕ) • -M).divisorialSheaf, V) :=
      fun _ => moduleOfLE _ h
    (localSubalgebra m M hφ).restrictₗ h =
      (coeffLinearEquivOfLE m M hφ h).symm.toLinearMap ∘ₗ
        (LinearMap.pi fun i => restrictₗ (((i : ℕ) • -M).divisorialSheaf) h ∘ₗ LinearMap.proj i) ∘ₗ
          (coeffLinearEquiv m M hφ U).toLinearMap := by
  let := (localSubalgebra m M hφ).moduleSections U
  let := (localSubalgebra m M hφ).moduleOfLE h
  let : ∀ i : Fin m, Module Γ(X, U) Γ(((i : ℕ) • -M).divisorialSheaf, V) :=
    fun _ => moduleOfLE _ h
  refine LinearMap.ext fun x => (coeffLinearEquivOfLE m M hφ h).injective ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact funext fun i => Subtype.ext rfl

/-- **The cyclic cover algebra is quasi-coherent**: its restriction to a basic open `D(a)` of an
affine open `U` is the localization away from `a`, factor by factor in
`𝒜 = ⊕_{i<m} 𝒪_X(-iM)`. -/
theorem isQuasicoherent_algebraSheaf :
    ((localSubalgebra m M hφ).algebraSheaf (isSheaf_ambient m φ)).IsQuasicoherent := by
  refine (localSubalgebra m M hφ).isQuasicoherent_algebraSheaf (isSheaf_ambient m φ)
    fun U _ a => ?_
  let := (localSubalgebra m M hφ).moduleSections U
  let := (localSubalgebra m M hφ).moduleOfLE (X.basicOpen_le a)
  let : ∀ i : Fin m, Module Γ(X, U) Γ(((i : ℕ) • -M).divisorialSheaf, X.basicOpen a) :=
    fun i => moduleOfLE _ (X.basicOpen_le a)
  have : ∀ i : Fin m, IsLocalizedModule (Submonoid.powers a)
      (restrictₗ (((i : ℕ) • -M).divisorialSheaf) (X.basicOpen_le a)) :=
    fun i => Divisor.isLocalizedModule_divisorialSheaf_restrictₗ _ a
  rw [restrictₗ_eq]
  infer_instance

end Quasicoherent

/-! ### The cyclic cover `p : Z = Spec_X 𝒜 → X` -/

section Cover

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (M : Divisor X) {φ : (RationalFunctions X)ˣ}
  (hφ : 0 ≤ principalDivisor φ + m • M)

/-- **The cyclic cover algebra** `𝒜 = ⊕_{i=0}^{m-1} 𝒪_X(-iM) eᵢ` of `(M, m, φ)`, as a sheaf of
commutative `𝒪_X`-algebras: `eᵢ = tⁱ` in `𝒦_X[t]/(tᵐ - φ)`, so that `(a eᵢ)(b eⱼ) = ab eᵢ₊ⱼ` for
`i + j < m` and `= φab eᵢ₊ⱼ₋ₘ` for `i + j ≥ m`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
abbrev algebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  (localSubalgebra m M hφ).algebraSheaf (isSheaf_ambient m φ)

/-- The relative-spectrum datum `(X, 𝒜)`. -/
abbrev situation : Stacks.RelativeSpec.RelativeSpecSituation.{u} where
  base := X
  algebra := algebraSheaf m M hφ
  isQuasicoherent := isQuasicoherent_algebraSheaf m M hφ

/-- **The cyclic cover** `Z = Spec_X 𝒜` defined by `(M, m, φ)`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
abbrev cover : Scheme.{u} := (Stacks.RelativeSpec.gluedSpectrum (situation m M hφ)).scheme

/-- The structure morphism `p : Z = Spec_X 𝒜 → X` of the cyclic cover defined by `(M, m, φ)`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
abbrev toBase : cover m M hφ ⟶ X := (Stacks.RelativeSpec.gluedSpectrum (situation m M hφ)).toBase

end Cover

/-! ### The action of `μ_m` -/

section Action

variable {X : Scheme.{u}} (m : ℕ) (φ : (RationalFunctions X)ˣ)
  (ζ : Γ(X, ⊤)ˣ)

/-- The value of a global unit `ζ` at the generic point of an irreducible component `Z`. -/
def zetaAt (Z : irreducibleComponents X) : X.presheaf.stalk (componentGenericPoint X Z) :=
  (X.presheaf.germ ⊤ (componentGenericPoint X Z) trivial).hom (ζ : Γ(X, ⊤))

/-- `zetaAt` is multiplicative in `ζ`. -/
@[simp]
theorem zetaAt_mul (η : Γ(X, ⊤)ˣ) (Z : irreducibleComponents X) :
    zetaAt (ζ * η) Z = zetaAt ζ Z * zetaAt η Z := by
  rw [zetaAt, Units.val_mul, map_mul]
  rfl

/-- The value of `1` at the generic point of `Z` is `1`. -/
@[simp]
theorem zetaAt_one (Z : irreducibleComponents X) : zetaAt (1 : Γ(X, ⊤)ˣ) Z = 1 := by
  rw [zetaAt, Units.val_one, map_one]

variable {ζ}

/-- If `ζᵐ = 1`, the value of `ζ` at the generic point of `Z` is an `m`-th root of unity. -/
theorem zetaAt_pow (hζ : ζ ^ m = 1) (Z : irreducibleComponents X) : zetaAt ζ Z ^ m = 1 := by
  rw [zetaAt, ← map_pow, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, map_one]

/-- Evaluating `tᵐ - φ_Z` along a ring homomorphism `f` at `x` gives `xᵐ - f(φ_Z)`. -/
theorem eval₂_poly {S : Type*} [CommRing S] (Z : irreducibleComponents X)
    (f : X.presheaf.stalk (componentGenericPoint X Z) →+* S) (x : S) :
    (poly m φ Z).eval₂ f x = x ^ m - f ((φ : RationalFunctions X) Z) := by
  rw [poly, eval₂_sub, eval₂_X_pow, eval₂_C]

/-- On a component `Z`, the automorphism `t ↦ ζ t` of `𝒪_{X,η_Z}[t]/(tᵐ - φ_Z)`, for `ζᵐ = 1`. -/
def fiberScale (hζ : ζ ^ m = 1) (Z : irreducibleComponents X) :
    Fiber m φ Z →ₐ[X.presheaf.stalk (componentGenericPoint X Z)] Fiber m φ Z :=
  AdjoinRoot.liftAlgHom (poly m φ Z)
    (Algebra.ofId (X.presheaf.stalk (componentGenericPoint X Z)) (Fiber m φ Z))
    (AdjoinRoot.of _ (zetaAt ζ Z) * AdjoinRoot.root _) (by
      rw [eval₂_poly, mul_pow, ← map_pow, zetaAt_pow m hζ, map_one, one_mul, root_pow_m]
      exact sub_eq_zero.mpr rfl)

/-- `fiberScale` fixes the elements of `𝒪_{X,η_Z}`. -/
@[simp]
theorem fiberScale_of (hζ : ζ ^ m = 1) (Z : irreducibleComponents X)
    (c : X.presheaf.stalk (componentGenericPoint X Z)) :
    fiberScale m φ hζ Z (AdjoinRoot.of _ c) = AdjoinRoot.of _ c := by
  rw [← AdjoinRoot.algebraMap_eq]
  exact (fiberScale m φ hζ Z).commutes c

/-- `fiberScale` sends `t` to `ζ t`. -/
@[simp]
theorem fiberScale_root (hζ : ζ ^ m = 1) (Z : irreducibleComponents X) :
    fiberScale m φ hζ Z (AdjoinRoot.root _) = AdjoinRoot.of _ (zetaAt ζ Z) * AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- `fiberScale` for `η` followed by `fiberScale` for `ζ` is `fiberScale` for `ζη`. -/
theorem fiberScale_comp {η : Γ(X, ⊤)ˣ} (hζ : ζ ^ m = 1) (hη : η ^ m = 1)
    (Z : irreducibleComponents X) (y : Fiber m φ Z) :
    fiberScale m φ hζ Z (fiberScale m φ hη Z y) =
      fiberScale m φ (by rw [mul_pow, hζ, hη, one_mul] : (ζ * η) ^ m = 1) Z y := by
  have : (fiberScale m φ hζ Z).comp (fiberScale m φ hη Z) =
      fiberScale m φ (by rw [mul_pow, hζ, hη, one_mul] : (ζ * η) ^ m = 1) Z := by
    refine AdjoinRoot.algHom_ext ?_
    rw [AlgHom.comp_apply, fiberScale_root, map_mul, fiberScale_of, fiberScale_root,
      fiberScale_root, zetaAt_mul, map_mul]
    ring
  exact congrArg (fun f => f y) this

/-- `fiberScale` for `ζ = 1` is the identity. -/
theorem fiberScale_one (Z : irreducibleComponents X) (y : Fiber m φ Z) :
    fiberScale m φ (one_pow m : (1 : Γ(X, ⊤)ˣ) ^ m = 1) Z y = y := by
  have : fiberScale m φ (one_pow m : (1 : Γ(X, ⊤)ˣ) ^ m = 1) Z = AlgHom.id _ _ := by
    refine AdjoinRoot.algHom_ext ?_
    rw [fiberScale_root, zetaAt_one, map_one, one_mul, AlgHom.id_apply]
  rw [this, AlgHom.id_apply]

/-- The automorphism `t ↦ ζ t` of the ambient sheaf over `U`. -/
def scale (hζ : ζ ^ m = 1) (U : X.Opens) : (ambient m φ).obj (op U) →+* (ambient m φ).obj (op U) :=
  RingHom.pi fun Z => (fiberScale m φ hζ Z.1).toRingHom.comp (Pi.evalRingHom _ Z)

/-- The component at `Z` of `scale m φ hζ U x` is `fiberScale m φ hζ Z (x Z)`. -/
theorem scale_apply (hζ : ζ ^ m = 1) {U : X.Opens} (x : (ambient m φ).obj (op U))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    scale m φ hζ U x Z = fiberScale m φ hζ Z.1 (x Z) := rfl

/-- The restriction of `ζ` to `U`. -/
def zetaOn (ζ : Γ(X, ⊤)ˣ) (U : X.Opens) : Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (ζ : Γ(X, ⊤))

/-- The germ of `zetaOn ζ U` at the generic point of `Z` is `zetaAt ζ Z`. -/
theorem germ_zetaOn (U : X.Opens)
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    (X.presheaf.germ U _ Z.2).hom (zetaOn ζ U) = zetaAt ζ Z.1 :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- `scale` sends `a tᵏ` to `ζᵏ a tᵏ`. -/
theorem scale_reduce_monomial (hζ : ζ ^ m = 1) {U : X.Opens} (k : ℕ)
    (a : (rationalFunctionsPresheaf X).obj (op U)) :
    scale m φ hζ U (reduce m φ U (monomial k a)) =
      reduce m φ U (monomial k (zetaOn ζ U ^ k • a)) := by
  funext Z
  rw [scale_apply, reduce_apply, reduce_apply, Polynomial.map_monomial, Polynomial.map_monomial,
    ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, fiberScale_of, fiberScale_root]
  change _ = AdjoinRoot.of _ ((X.presheaf.germ U _ Z.2).hom (zetaOn ζ U ^ k) * a Z) * _
  rw [map_pow, germ_zetaOn, map_mul, map_pow, evalAt_apply]
  ring

variable [NeZero m]

/-- The coefficient of `tⁿ` of a section of the ambient sheaf vanishes for `n ≥ m`. -/
theorem coeff_eq_zero_of_le {U : X.Opens} (x : (ambient m φ).obj (op U)) {n : ℕ} (hn : m ≤ n) :
    coeff m φ U n x = 0 := by
  funext Z
  rw [coeff_apply]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((natDegree_modByMonicHom_lt m φ Z.1 (x Z)).trans_le hn)

/-- **`ζ` acts on the coefficient of `tⁿ` by `ζⁿ`.** -/
theorem coeff_scale (hζ : ζ ^ m = 1) {U : X.Opens} (x : (ambient m φ).obj (op U)) (n : ℕ) :
    coeff m φ U n (scale m φ hζ U x) = zetaOn ζ U ^ n • coeff m φ U n x := by
  conv_lhs => rw [← reduce_sum_coeff m φ x]
  rw [map_sum, map_sum, map_sum]
  simp only [scale_reduce_monomial]
  rw [Finset.sum_congr rfl fun k hk => coeff_reduce_monomial_of_lt m φ (Finset.mem_range.mp hk) n _]
  by_cases hn : n < m
  · rw [Finset.sum_ite_eq' (Finset.range m) n, ite_eq_left (Finset.mem_range.mpr hn)]
  · rw [Finset.sum_eq_zero fun k hk =>
        ite_eq_right fun e : k = n => hn (e ▸ Finset.mem_range.mp hk),
      coeff_eq_zero_of_le m φ x (not_lt.mp hn), smul_zero]

omit [NeZero m] in
/-- `scale` fixes the image of the structure morphism `𝒪_X ⟶ ambient m φ`. -/
theorem scale_structureMap (hζ : ζ ^ m = 1) {U : X.Opens} (r : Γ(X, U)) :
    scale m φ hζ U (((structureMap m φ).app (op U)).hom r) =
      ((structureMap m φ).app (op U)).hom r :=
  funext fun Z => fiberScale_of m φ hζ Z.1 _

variable [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (M : Divisor X)
  (hφ : 0 ≤ principalDivisor φ + m • M)

include hφ in
/-- `scale` maps sections of `𝒜` to sections of `𝒜`. -/
theorem scale_mem (hζ : ζ ^ m = 1) {U : X.Opens} {x : (ambient m φ).obj (op U)}
    (hx : x ∈ carrier m M U) : scale m φ hζ U x ∈ carrier m M U := by
  rw [mem_carrier_iff m M hφ] at hx ⊢
  intro n
  rw [coeff_scale]
  exact Submodule.smul_mem _ _ (hx n)

/-- The automorphism `σ_ζ` of `𝒜(U)`, multiplication by `ζⁱ` on `𝒪_X(-iM) eᵢ`. -/
def scaleSections (hζ : ζ ^ m = 1) (U : X.Opens) :
    (localSubalgebra m M hφ).carrier U →+* (localSubalgebra m M hφ).carrier U :=
  (scale m φ hζ U).restrict _ _ fun _ hx => scale_mem m φ M hφ hζ hx

/-- The scaling `σ_ζ` of `𝒜`, as an endomorphism of the presheaf of `𝒪_X`-algebras. -/
def algebraScaling (hζ : ζ ^ m = 1) :
    Under.mk (situation m M hφ).algebra.hom.hom ⟶ Under.mk (situation m M hφ).algebra.hom.hom :=
  Under.homMk
    { app U := CommRingCat.ofHom (scaleSections m φ M hφ hζ U.unop)
      naturality _ _ _ := rfl }
    (NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun r =>
      Subtype.ext (scale_structureMap m φ hζ r))))

/-- **The action of `μ_m` on `𝒜`: `ζ · (a eₖ) = ζᵏ a eₖ`.** -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
theorem scaleSections_reduce_monomial (hζ : ζ ^ m = 1) (U : X.Opens) (k : ℕ)
    (x : (localSubalgebra m M hφ).carrier U) (a : (rationalFunctionsPresheaf X).obj (op U))
    (hx : (x : (ambient m φ).obj (op U)) = reduce m φ U (monomial k a)) :
    (scaleSections m φ M hφ hζ U x : (ambient m φ).obj (op U)) =
      reduce m φ U (monomial k (zetaOn ζ U ^ k • a)) := by
  change scale m φ hζ U x = _
  rw [hx, scale_reduce_monomial]

/-- On sections over `W`, `σ_η` followed by `σ_ζ` is `σ_{ζη}`. -/
theorem algebraScaling_comp {η : Γ(X, ⊤)ˣ} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (W : X.Opens) :
    (algebraScaling m φ M hφ hη).right.app (op W) ≫ (algebraScaling m φ M hφ hζ).right.app (op W) =
      (algebraScaling m φ M hφ (by rw [mul_pow, hζ, hη, one_mul] : (ζ * η) ^ m = 1)).right.app
        (op W) :=
  CommRingCat.hom_ext (RingHom.ext fun _ => Subtype.ext (funext fun Z =>
    fiberScale_comp m φ hζ hη Z.1 _))

/-- On sections over `W`, `σ_1` is the identity. -/
theorem algebraScaling_one (W : X.Opens) :
    (algebraScaling m φ M hφ (one_pow m : (1 : Γ(X, ⊤)ˣ) ^ m = 1)).right.app (op W) = 𝟙 _ :=
  CommRingCat.hom_ext (RingHom.ext fun _ => Subtype.ext (funext fun Z =>
    fiberScale_one m φ Z.1 _))

end Action

/-! ### The `X`-automorphisms `α_ζ` of the cyclic cover -/

section Scaling

/-- A morphism into a relative spectrum pulling the universal pair back to `q` acts on sections
over the preimage of any open of the base by the algebra map of `q`. -/
private lemma appLE_of_pullback_universal' {s : Stacks.RelativeSpec.RelativeSpecSituation.{u}}
    {T : Scheme.{u}} (f : T ⟶ (Stacks.RelativeSpec.gluedSpectrum s).scheme)
    (q : Stacks.RelativeSpec.RelativeSpecPair s T)
    (hq : Stacks.RelativeSpec.RelativeSpecPair.pullback f
      (Stacks.RelativeSpec.universalRelativeSpecPair s) = q) (U : s.base.Opens)
    (h : q.1 ⁻¹ᵁ U ≤ f ⁻¹ᵁ ((Stacks.RelativeSpec.gluedSpectrum s).toBase ⁻¹ᵁ U)) :
    (Stacks.RelativeSpec.universalAlgebraMap s).right.app (op U) ≫
        f.appLE ((Stacks.RelativeSpec.gluedSpectrum s).toBase ⁻¹ᵁ U) (q.1 ⁻¹ᵁ U) h =
      q.2.right.app (op U) := by
  subst hq
  exact congrArg (fun k => (Stacks.RelativeSpec.universalAlgebraMap s).right.app (op U) ≫ k)
    f.appLE_eq_app

/-- `Scheme.Hom.appLE_comp_appLE` with the inclusion for the composite given as an argument. -/
private lemma appLE_comp_appLE'' {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens)
    (V : B.Opens) (W : A.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V)
    (e : W ≤ (f ≫ g) ⁻¹ᵁ U) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ = (f ≫ g).appLE U W e :=
  Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (m : ℕ) [NeZero m] (M : Divisor X) {φ : (RationalFunctions X)ˣ}
  (hφ : 0 ≤ principalDivisor φ + m • M) {ζ : Γ(X, ⊤)ˣ}

/-- The relative-spectrum pair `(p, σ_ζ ≫ ψ)` over `Z`, where `ψ : 𝒜 ⟶ p_* 𝒪_Z` is the universal
algebra map. -/
def scalingPair (hζ : ζ ^ m = 1) :
    Stacks.RelativeSpec.RelativeSpecPair (situation m M hφ) (cover m M hφ) :=
  ⟨toBase m M hφ, algebraScaling m φ M hφ hζ ≫
    Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)⟩

/-- **The action of `μ_m` on the cyclic cover.** For an `m`-th root of unity `ζ` among the global
units of `X`, the `X`-endomorphism `α_ζ` of `Z = Spec_X 𝒜` whose pull-back on functions is `σ_ζ`,
`ζ · (a eᵢ) = ζⁱ a eᵢ`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
def scaling (hζ : ζ ^ m = 1) : cover m M hφ ⟶ cover m M hφ :=
  Stacks.RelativeSpec.pairToHom (scalingPair m M hφ hζ)

/-- `α_ζ` is a morphism over `X`. -/
@[reassoc (attr := simp)]
theorem scaling_toBase (hζ : ζ ^ m = 1) :
    scaling m M hφ hζ ≫ toBase m M hφ = toBase m M hφ :=
  Stacks.RelativeSpec.pairToHom_toBase (scalingPair m M hφ hζ)

/-- **`α_ζ^* = σ_ζ`**: on sections over the preimage of an open `W ⊆ X`, `α_ζ` acts by `σ_ζ`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
theorem scaling_appLE (hζ : ζ ^ m = 1) (W : X.Opens)
    (h : toBase m M hφ ⁻¹ᵁ W ≤ scaling m M hφ hζ ⁻¹ᵁ (toBase m M hφ ⁻¹ᵁ W)) :
    (Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)).right.app (op W) ≫
        (scaling m M hφ hζ).appLE (toBase m M hφ ⁻¹ᵁ W) (toBase m M hφ ⁻¹ᵁ W) h =
      (algebraScaling m φ M hφ hζ).right.app (op W) ≫
        (Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)).right.app (op W) :=
  appLE_of_pullback_universal' (scaling m M hφ hζ) (scalingPair m M hφ hζ)
    (Stacks.RelativeSpec.pullback_universalRelativeSpecPair_pairToHom (scalingPair m M hφ hζ)) W h

/-- The preimage under `α_ζ` of `p⁻¹(W)` is `p⁻¹(W)`. -/
theorem scaling_preimage (hζ : ζ ^ m = 1) (W : X.Opens) :
    scaling m M hφ hζ ⁻¹ᵁ (toBase m M hφ ⁻¹ᵁ W) = toBase m M hφ ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, scaling_toBase]

/-- An `X`-endomorphism of `Z` acting by `σ_ζ` over the affine opens of `X` is `α_ζ`. -/
theorem eq_scaling (hζ : ζ ^ m = 1) (f : cover m M hφ ⟶ cover m M hφ)
    (hb : f ≫ toBase m M hφ = toBase m M hφ)
    (hm : ∀ (U : X.affineOpens) (h : toBase m M hφ ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (toBase m M hφ ⁻¹ᵁ U.1)),
      (Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)).right.app (op U.1) ≫
          f.appLE (toBase m M hφ ⁻¹ᵁ U.1) (toBase m M hφ ⁻¹ᵁ U.1) h =
        (algebraScaling m φ M hφ hζ).right.app (op U.1) ≫
          (Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)).right.app (op U.1)) :
    f = scaling m M hφ hζ :=
  (Stacks.RelativeSpec.pairToHom_pullback_universalRelativeSpecPair f).symm.trans
    (congrArg Stacks.RelativeSpec.pairToHom
      (Stacks.RelativeSpec.pullback_universalRelativeSpecPair_eq (scalingPair m M hφ hζ) f hb hm))

/-- On sections over `p⁻¹(W)`, `α_ζ ≫ α_η` acts by `σ_{ζη}`. -/
theorem scaling_comp_appLE {η : Γ(X, ⊤)ˣ} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (W : X.Opens)
    (h : toBase m M hφ ⁻¹ᵁ W ≤
      (scaling m M hφ hζ ≫ scaling m M hφ hη) ⁻¹ᵁ (toBase m M hφ ⁻¹ᵁ W)) :
    (Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)).right.app (op W) ≫
        (scaling m M hφ hζ ≫ scaling m M hφ hη).appLE (toBase m M hφ ⁻¹ᵁ W)
          (toBase m M hφ ⁻¹ᵁ W) h =
      (algebraScaling m φ M hφ (by rw [mul_pow, hζ, hη, one_mul] : (ζ * η) ^ m = 1)).right.app
          (op W) ≫
        (Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)).right.app (op W) := by
  have h₁ : toBase m M hφ ⁻¹ᵁ W ≤ scaling m M hφ hη ⁻¹ᵁ (toBase m M hφ ⁻¹ᵁ W) :=
    (scaling_preimage m M hφ hη W).ge
  have h₂ : toBase m M hφ ⁻¹ᵁ W ≤ scaling m M hφ hζ ⁻¹ᵁ (toBase m M hφ ⁻¹ᵁ W) :=
    (scaling_preimage m M hφ hζ W).ge
  rw [← appLE_comp_appLE'' _ _ _ _ _ h₁ h₂ h, ← Category.assoc,
    scaling_appLE m M hφ hη W h₁, Category.assoc, scaling_appLE m M hφ hζ W h₂,
    ← Category.assoc, algebraScaling_comp m φ M hφ hζ hη W]

/-- **The automorphisms `α_ζ` compose as the roots of unity do**: `α_ζ ≫ α_η = α_{ζη}`. -/
theorem scaling_comp {η : Γ(X, ⊤)ˣ} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) :
    scaling m M hφ hζ ≫ scaling m M hφ hη =
      scaling m M hφ (by rw [mul_pow, hζ, hη, one_mul] : (ζ * η) ^ m = 1) :=
  eq_scaling m M hφ _ _
    (by rw [Category.assoc, scaling_toBase, scaling_toBase])
    (fun U h => scaling_comp_appLE m M hφ hζ hη U.1 h)

/-- `α_1` is the identity. -/
theorem scaling_one : scaling m M hφ (one_pow m : (1 : Γ(X, ⊤)ˣ) ^ m = 1) = 𝟙 _ := by
  refine (eq_scaling m M hφ _ (𝟙 _) (Category.id_comp _) fun U h => ?_).symm
  have hid : Scheme.Hom.appLE (𝟙 (cover m M hφ)) (toBase m M hφ ⁻¹ᵁ U.1)
      (toBase m M hφ ⁻¹ᵁ U.1) h = 𝟙 _ :=
    (Category.id_comp _).trans ((cover m M hφ).presheaf.map_id _)
  exact ((congrArg (fun k => _ ≫ k) hid).trans (Category.comp_id _)).trans
    (((congrArg (fun k => k ≫
      (Stacks.RelativeSpec.universalAlgebraMap (situation m M hφ)).right.app (op U.1))
      (algebraScaling_one m φ M hφ U.1)).trans (Category.id_comp _)).symm)

/-- **The action of `μ_m` on the cyclic cover**: the `X`-automorphism `α_ζ` of `Z = Spec_X 𝒜`,
with inverse `α_{ζ⁻¹}`, for an `m`-th root of unity `ζ`. -/
@[mmp "def_km5d_divisorial_cyclic_cover"]
def scalingIso (hζ : ζ ^ m = 1) : cover m M hφ ≅ cover m M hφ where
  hom := scaling m M hφ hζ
  inv := scaling m M hφ (by rw [inv_pow, hζ, inv_one] : ζ⁻¹ ^ m = 1)
  hom_inv_id := by
    rw [scaling_comp]
    simp only [mul_inv_cancel]
    exact scaling_one m M hφ
  inv_hom_id := by
    rw [scaling_comp]
    simp only [inv_mul_cancel]
    exact scaling_one m M hφ

/-- `α_ζ` is an isomorphism. -/
instance isIso_scaling (hζ : ζ ^ m = 1) : IsIso (scaling m M hφ hζ) :=
  (scalingIso m M hφ hζ).isIso_hom

end Scaling

end DivisorialCyclicCover

end MMP.Mori

end
