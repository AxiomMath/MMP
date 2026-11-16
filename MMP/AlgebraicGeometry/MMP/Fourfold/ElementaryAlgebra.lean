module

public import MMP.Attr
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Int.Interval

/-!
# Elementary algebra and convex geometry

This file proves three elementary results.

* A uniform bound on the order of a root of unity of bounded degree: a nonzero algebraic integer
  of degree at most `b`, all of whose conjugates have absolute value one, satisfies `u ^ N = 1`
  for an integer `N > 0` depending only on `b`.
* Gordan's lemma for a finitely generated rational cone: the integral points of a subgroup
  `L ≤ ℤ^r` lying in the real cone spanned by vectors of `L` form a finitely generated
  additive monoid.
* Openness along the smallest rational affine hull: if `N ⊆ ℝ^r` is cut out by finitely many
  rational affine equations and weak inequalities and `δ ∈ N`, then `N` contains a neighbourhood
  of `δ` in the smallest rational affine subspace `W` containing `δ`, and a rational
  parallelotope with `δ` in its relative interior and affine hull `W`.

## Main definitions

* `MMP.Fourfold.unitConjugates`: nonzero algebraic integers of degree at most `b` whose conjugates
  all have norm one.
* `MMP.Fourfold.coneIntegralPoints`: the additive monoid `L ∩ cone(v₁, …, v_s)`.
* `MMP.Fourfold.ratAffineForm`, `MMP.Fourfold.IsRationalPolyhedron`: rational affine functions,
  and subsets of `ℝ^r` cut out by finitely many rational affine equations and weak inequalities.
* `MMP.Fourfold.rationalAffineHull`: the smallest rational affine subspace containing a point.
* `MMP.Fourfold.IsRationalAffineSubspace`, `MMP.Fourfold.IsRationalParallelotope`.

## Main results

* `MMP.Fourfold.exists_pow_eq_one_of_bounded_degree_unit_conjugates`
* `MMP.Fourfold.coneIntegralPoints_fg`
* `MMP.Fourfold.rational_hull_neighborhood`
* `MMP.Fourfold.mem_span_rational_solutions`: the real solutions of a system of rational linear
  equations are spanned by its rational solutions.
* `MMP.Fourfold.exists_rational_frame`: the rational affine hull has a rational point and a
  rational direction basis.

## Implementation notes

The smallest rational affine hull of `δ ∈ ℝ^r` is the set of points satisfying every rational
affine equation satisfied by `δ`; this is the same notion as
`MMP.Fourfold.IsInSmallestRationalAffineHull` for divisors with `r` prime components. The relative
interior is Mathlib's `intrinsicInterior`.
-/

@[expose] public noncomputable section

open Polynomial Set Filter Topology Module
open scoped IntermediateField

namespace MMP.Fourfold

section Units

variable {A : Type*} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

/-- The nonzero algebraic integers of degree at most `b` whose conjugates all have norm one. -/
def unitConjugates (A : Type*) [NormedField A] [NormedAlgebra ℚ A] (b : ℕ) : Set A :=
  {u | u ≠ 0 ∧ IsIntegral ℤ u ∧ (minpoly ℚ u).natDegree ≤ b ∧
    ∀ z ∈ (minpoly ℚ u).rootSet A, ‖z‖ = 1}

/-- For each `b`, the set `unitConjugates A b` is finite. -/
theorem unitConjugates_finite (b : ℕ) : (unitConjugates A b).Finite := by
  classical
  let C := Nat.ceil (max (1:ℝ) 1 ^ b * b.choose (b / 2))
  have := bUnion_roots_finite (algebraMap ℤ A) b (finite_Icc (-C : ℤ) C)
  refine this.subset fun x hx => ?_
  obtain ⟨-, hxi, hdeg, hroots⟩ := hx
  simp_rw [mem_iUnion]
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hxi
  have hmonic := minpoly.monic hxi
  have hA : (minpoly ℤ x).map (algebraMap ℤ A) = (minpoly ℚ x).map (algebraMap ℚ A) := by
    rw [hmap, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hne := minpoly.ne_zero (IsIntegral.tower_top (R := ℤ) (A := ℚ) hxi)
  have hdegZ : (minpoly ℤ x).natDegree ≤ b := by
    rw [← hmonic.natDegree_map (algebraMap ℤ ℚ), ← hmap]
    exact hdeg
  have hrs : ∀ z, z ∈ ((minpoly ℤ x).map (algebraMap ℤ A)).roots ↔ z ∈ (minpoly ℚ x).rootSet A := by
    intro z
    rw [hA, mem_rootSet, mem_roots (by simpa using hne), IsRoot, eval_map_algebraMap]
    simp [aeval_def, hne]
  refine ⟨minpoly ℤ x, ⟨hdegZ, fun i => ?_⟩, ?_⟩
  · rw [mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
    have h1 : ‖(((minpoly ℤ x).map (algebraMap ℤ A)).coeff i)‖ ≤
        max (1:ℝ) 1 ^ b * b.choose (b / 2) :=
      coeff_bdd_of_roots_le (algebraMap ℤ A) hmonic (IsAlgClosed.splits _) hdegZ
        (fun z hz => le_of_eq (hroots z ((hrs z).1 hz))) i
    have h2 : ‖(((minpoly ℤ x).map (algebraMap ℤ A)).coeff i)‖ =
        |(((minpoly ℤ x).coeff i : ℤ) : ℝ)| := by
      rw [coeff_map, eq_intCast, ← map_intCast (algebraMap ℚ A), norm_algebraMap']
      simp [Int.norm_eq_abs]
    rw [h2] at h1
    simpa [C] using h1.trans (Nat.le_ceil _)
  · simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (hrs x).2 (mem_rootSet.2 ⟨hne, minpoly.aeval ℚ x⟩)

/-- If `u` is the image of an element `x` of a number field `K` of degree at most `b` over `ℚ`,
and all conjugates of `u` have norm one, then every power `u ^ k` has minimal polynomial of
degree at most `b` and all its conjugates have norm one. -/
theorem pow_mem_unitConjugates_aux {b : ℕ} (K : Type*) [Field K] [NumberField K] [Algebra K A]
    (x : K) (u : A) (hxu : algebraMap K A x = u) (hK : Module.finrank ℚ K ≤ b)
    (hroots : ∀ z ∈ (minpoly ℚ u).rootSet A, ‖z‖ = 1) (k : ℕ) :
    (minpoly ℚ (u ^ k)).natDegree ≤ b ∧ ∀ z ∈ (minpoly ℚ (u ^ k)).rootSet A, ‖z‖ = 1 := by
  have hm : ∀ y : K, minpoly ℚ (algebraMap K A y) = minpoly ℚ y :=
    fun y => minpoly.algebraMap_eq (algebraMap K A).injective y
  have hxk : minpoly ℚ (u ^ k) = minpoly ℚ (x ^ k) := by
    rw [← hxu, ← map_pow, hm]
  rw [hxk]
  refine ⟨(minpoly.natDegree_le (x ^ k)).trans hK, fun z hz => ?_⟩
  rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K A] at hz
  obtain ⟨φ, rfl⟩ := hz
  have : φ x ∈ (minpoly ℚ u).rootSet A := by
    rw [← hxu, hm x, ← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K A]
    exact ⟨φ, rfl⟩
  show ‖φ (x ^ k)‖ = 1
  rw [map_pow, norm_pow, hroots _ this, one_pow]

/-- Every power of an element of `unitConjugates A b` lies in `unitConjugates A b`. -/
theorem pow_mem_unitConjugates {b : ℕ} {u : A} (hu : u ∈ unitConjugates A b) (k : ℕ) :
    u ^ k ∈ unitConjugates A b := by
  obtain ⟨hu0, hui, hdeg, hroots⟩ := hu
  have hq : IsIntegral ℚ u := hui.tower_top
  have h1 : @Module.Finite ℚ ℚ⟮u⟯ _ _ (DivisionRing.toRatAlgebra (R := ℚ⟮u⟯)).toModule := by
    convert IntermediateField.adjoin.finiteDimensional hq
    all_goals first | rfl | exact Subsingleton.elim _ _
  have : NumberField ℚ⟮u⟯ := ⟨⟩
  have hfr : @Module.finrank ℚ ℚ⟮u⟯ _ _ (DivisionRing.toRatAlgebra (R := ℚ⟮u⟯)).toModule ≤ b := by
    have := (IntermediateField.adjoin.finrank hq).le.trans hdeg
    convert this using 2
    all_goals first | rfl | exact Subsingleton.elim _ _
  obtain ⟨h2, h3⟩ := pow_mem_unitConjugates_aux (A := A) ℚ⟮u⟯
    (IntermediateField.AdjoinSimple.gen ℚ u) u (IntermediateField.AdjoinSimple.algebraMap_gen ℚ u)
    hfr hroots k
  exact ⟨pow_ne_zero _ hu0, hui.pow k, h2, h3⟩

/-- **Uniform bounded order for bounded-degree algebraic unit conjugates.** For every `b` there
is `N > 0` such that every nonzero algebraic integer `u` of degree at most `b` (over `ℚ`), all of
whose conjugates (the roots in `A` of its minimal polynomial over `ℚ`) have norm one, satisfies
`u ^ N = 1`.

It is stated over any algebraically closed normed field `A` containing `ℚ` (for instance `ℂ`, where
the conjugates are the complex conjugates in the usual sense); the hypothesis `1 ≤ b` of the
source is not needed (for `b = 0` there is no such `u`). -/
@[mmp "lem_fourfold_bounded_degree_unit_conjugates"]
theorem exists_pow_eq_one_of_bounded_degree_unit_conjugates (b : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : A, u ≠ 0 → IsIntegral ℤ u → (minpoly ℚ u).natDegree ≤ b →
      (∀ z ∈ (minpoly ℚ u).rootSet A, ‖z‖ = 1) → u ^ N = 1 := by
  classical
  set T := (unitConjugates_finite (A := A) b).toFinset with hT
  refine ⟨(T.card).factorial, Nat.factorial_pos _, fun u hu0 hui hdeg hroots => ?_⟩
  have hu : u ∈ unitConjugates A b := ⟨hu0, hui, hdeg, hroots⟩
  have hmaps : ∀ k ∈ Finset.Icc 1 (T.card + 1), u ^ k ∈ T := by
    intro k _
    rw [hT, Set.Finite.mem_toFinset]
    exact pow_mem_unitConjugates hu k
  obtain ⟨a, ha, c, hc, hac, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp) hmaps
  wlog hlt : a < c generalizing a c
  · exact this c hc a ha hac.symm h.symm (hac.symm.lt_of_le (not_lt.1 hlt))
  simp only [Finset.mem_Icc] at ha hc
  have h1 : u ^ a * u ^ (c - a) = u ^ a * 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
    exact h.symm
  have h2 : u ^ (c - a) = 1 := mul_left_cancel₀ (pow_ne_zero _ hu0) h1
  obtain ⟨m, hm⟩ : c - a ∣ (T.card).factorial := Nat.dvd_factorial (by omega) (by omega)
  rw [hm, pow_mul, h2, one_pow]

end Units

/-- The additive submonoid of the integral points of the lattice `L ≤ ℤ^r` lying in the real
cone spanned by `v₁, …, v_s`. -/
def coneIntegralPoints {r s : ℕ} (L : AddSubgroup (Fin r → ℤ)) (v : Fin s → Fin r → ℤ) :
    AddSubmonoid (Fin r → ℤ) where
  carrier := {x | x ∈ L ∧ ∃ a : Fin s → ℝ, (∀ i, 0 ≤ a i) ∧
    (fun j => (x j : ℝ)) = ∑ i, a i • fun j => (v i j : ℝ)}
  zero_mem' := ⟨L.zero_mem, 0, fun _ => le_rfl, by ext; simp⟩
  add_mem' := by
    rintro x y ⟨hxL, a, ha, hx⟩ ⟨hyL, c, hc, hy⟩
    refine ⟨L.add_mem hxL hyL, a + c, fun i => add_nonneg (ha i) (hc i), ?_⟩
    ext j
    have hxj := congrFun hx j
    have hyj := congrFun hy j
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hxj hyj ⊢
    push_cast
    rw [hxj, hyj, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- An integer vector that is a combination of integer vectors `vᵢ` with real coefficients in
`[0, 1]` is bounded coordinatewise by `∑ᵢ |vᵢ|`. -/
theorem abs_le_sum_abs_of_eq_sum_smul {r s : ℕ} {v : Fin s → Fin r → ℤ} {y : Fin r → ℤ}
    {c : Fin s → ℝ} (hc₀ : ∀ i, 0 ≤ c i) (hc₁ : ∀ i, c i ≤ 1)
    (hy : (fun j => (y j : ℝ)) = ∑ i, c i • fun j => (v i j : ℝ)) (j : Fin r) :
    |y j| ≤ ∑ i, |v i j| := by
  have h := congrFun hy j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  have : |(y j : ℝ)| ≤ ∑ i, |(v i j : ℝ)| := by
    rw [h]
    calc |∑ i, c i * (v i j : ℝ)| ≤ ∑ i, |c i * (v i j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |(v i j : ℝ)| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hc₀ i)]
          exact mul_le_of_le_one_left (abs_nonneg _) (hc₁ i)
  exact_mod_cast this

/-- **Integral points of a finitely generated rational cone.** For a subgroup `L` of `ℤ^r` and
vectors `v₁, …, v_s ∈ L`, the additive semigroup `L ∩ {∑ aᵢ vᵢ | aᵢ ∈ ℝ≥0}` is finitely
generated. -/
@[mmp "lem_fourfold_cone_semigroup_finite"]
theorem coneIntegralPoints_fg {r s : ℕ} (L : AddSubgroup (Fin r → ℤ)) (v : Fin s → Fin r → ℤ)
    (hv : ∀ i, v i ∈ L) : (coneIntegralPoints L v).FG := by
  classical
  let B : Fin r → ℤ := fun j => ∑ i, |v i j|
  let G : Set (Fin r → ℤ) := range v ∪ (Icc (-B) B ∩ (coneIntegralPoints L v : Set _))
  have hGfin : G.Finite := (finite_range v).union ((Set.finite_Icc (-B) B).inter_of_left _)
  refine (AddSubmonoid.fg_iff _).2 ⟨G, ?_, hGfin⟩
  apply le_antisymm
  · rw [AddSubmonoid.closure_le]
    rintro y (⟨i, rfl⟩ | ⟨-, hy⟩)
    · exact ⟨hv i, Pi.single i 1, fun k => by by_cases h : k = i <;> simp [h],
        by
          ext j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, ite_mul,
            one_mul, zero_mul]
          simp⟩
    · exact hy
  · rintro x ⟨hxL, a, ha, hx⟩
    let m : Fin s → ℕ := fun i => ⌊a i⌋₊
    let y : Fin r → ℤ := x - ∑ i, m i • v i
    have hyL : y ∈ L := L.sub_mem hxL (L.sum_mem fun i _ => L.nsmul_mem (hv i) _)
    have hyR : (fun j => (y j : ℝ)) = ∑ i, (a i - m i) • fun j => (v i j : ℝ) := by
      ext j
      have hxj := congrFun hx j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hxj ⊢
      simp only [y, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
      push_cast
      rw [hxj, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        simp
        ring
    have hf0 : ∀ i, 0 ≤ a i - m i := fun i => sub_nonneg.2 (Nat.floor_le (ha i))
    have hf1 : ∀ i, a i - m i < 1 := fun i => by
      have := Nat.lt_floor_add_one (a i)
      simp only [m]
      linarith
    have hyN : y ∈ coneIntegralPoints L v := ⟨hyL, _, hf0, hyR⟩
    have hyB : y ∈ Icc (-B) B := by
      have h := abs_le_sum_abs_of_eq_sum_smul (c := fun i => a i - m i) hf0 (fun i => (hf1 i).le)
        hyR
      exact ⟨fun j => neg_le_of_abs_le (h j), fun j => le_of_abs_le (h j)⟩
    have hxy : x = y + ∑ i, m i • v i := by simp [y]
    rw [hxy]
    exact (AddSubmonoid.closure G).add_mem (AddSubmonoid.subset_closure (Or.inr ⟨hyB, hyN⟩))
      ((AddSubmonoid.closure G).sum_mem fun i _ => (AddSubmonoid.closure G).nsmul_mem
        (AddSubmonoid.subset_closure (Or.inl ⟨i, rfl⟩)) _)

/-- The basis `Basis.sumExtend hv` extending a linearly independent family `v` agrees with `v`
on the left summand. -/
theorem sumExtend_inl {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] (v : ι → V)
    (hv : LinearIndependent K v) (i : ι) : Basis.sumExtend hv (Sum.inl i) = v i := by
  simp [Basis.sumExtend, Basis.reindex_apply, Equiv.Set.sumDiffSubset, Equiv.Set.union]
  rfl

/-- An element `y` of a submodule `K` with basis `b` is `∑ᵢ (b.repr y i) • bᵢ` in the ambient
module. -/
theorem coe_eq_sum_repr_smul {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Fintype ι] {K : Submodule R M} (b : Basis ι R K) (y : K) :
    (y : M) = ∑ i, b.repr y i • (b i : M) := by
  have := congrArg Subtype.val (b.sum_repr y)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  exact this.symm

/-- For a subspace `S` of the dual of `V`, the coordinate functionals of the basis extending a
basis of `S.dualCoannihilator` lie in `S` on the extension part. -/
theorem sumExtend_coord_inr_mem {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Finite κ] {S : Submodule K (Dual K V)}
    (b : Basis κ K S.dualCoannihilator) (hv : LinearIndependent K fun i => (b i : V))
    (j : Basis.sumExtendIndex hv) : (Basis.sumExtend hv).coord (Sum.inr j) ∈ S := by
  have := Fintype.ofFinite κ
  refine (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)).le
    ((Submodule.mem_dualAnnihilator _).2 fun y hy => ?_)
  rw [show y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : V) from coe_eq_sum_repr_smul b ⟨y, hy⟩, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, show (b i : V) = Basis.sumExtend hv (Sum.inl i) from (sumExtend_inl _ hv i).symm]
  simp [Module.Basis.coord_apply]

section KeyLemma

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real functional with the rational coefficients of a rational functional `c`. -/
def realizeFunctional (c : Dual ℚ (ι → ℚ)) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, ((c (Pi.single i 1) : ℚ) : ℝ) • (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)

/-- `realizeFunctional c x` is `∑ᵢ c(eᵢ) xᵢ`. -/
theorem realizeFunctional_apply (c : Dual ℚ (ι → ℚ)) (x : ι → ℝ) :
    realizeFunctional c x = ∑ i, ((c (Pi.single i 1) : ℚ) : ℝ) * x i := by
  simp [realizeFunctional]

/-- On rational vectors, `realizeFunctional c` agrees with `c`. -/
theorem realizeFunctional_cast (c : Dual ℚ (ι → ℚ)) (y : ι → ℚ) :
    realizeFunctional c (fun i => (y i : ℝ)) = ((c y : ℚ) : ℝ) := by
  rw [realizeFunctional_apply]
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ c y]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (fun j => if i = j then (1:ℚ) else 0) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  simp [h, mul_comm]

/-- `realizeFunctional f` vanishes at a real solution `x` of a system `Φ` of rational linear
equations whenever `f` lies in the span of `Φ`. -/
theorem realizeFunctional_eq_zero_of_mem_span {Φ : Set (ι → ℚ)} {x : ι → ℝ}
    (hx : ∀ c ∈ Φ, ∑ i, (c i : ℝ) * x i = 0) {f : Dual ℚ (ι → ℚ)}
    (hf : f ∈ Submodule.span ℚ ((dotProductEquiv ℚ ι) '' Φ)) : realizeFunctional f x = 0 := by
  let L : Dual ℚ (ι → ℚ) →ₗ[ℚ] ℝ :=
    { toFun := fun f => realizeFunctional f x
      map_add' := fun f g => by simp [realizeFunctional_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun q f => by
        simp [realizeFunctional_apply, Rat.smul_def, Finset.mul_sum, mul_assoc] }
  have hSL : Submodule.span ℚ ((dotProductEquiv ℚ ι) '' Φ) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, L, LinearMap.coe_mk, AddHom.coe_mk]
    rw [realizeFunctional_apply, ← hx c hc]
    exact Finset.sum_congr rfl fun i _ => by simp
  exact hSL hf

/-- If the real basis `Bℝ` is the cast of the rational basis `B`, its coordinate functionals are
the realizations of those of `B`. -/
theorem coord_eq_realizeFunctional {κ : Type*} (B : Basis κ ℚ (ι → ℚ)) (Bℝ : Basis κ ℝ (ι → ℝ))
    (h : ∀ t, Bℝ t = fun i => (B t i : ℝ)) (k : κ) :
    Bℝ.coord k = realizeFunctional (B.coord k) := by
  classical
  refine Bℝ.ext fun t => ?_
  have h3 : Bℝ.coord k (Bℝ t) = if t = k then 1 else 0 := by
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  rw [h3, h, realizeFunctional_cast]
  have h4 : B.coord k (B t) = if t = k then 1 else 0 := by
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  rw [h4]
  split_ifs <;> simp

/-- The real solutions of a system of rational linear equations are spanned by the rational
solutions. -/
theorem mem_span_rational_solutions (Φ : Set (ι → ℚ)) (x : ι → ℝ)
    (hx : ∀ c ∈ Φ, ∑ i, (c i : ℝ) * x i = 0) :
    x ∈ Submodule.span ℝ ((fun y : ι → ℚ => fun i => (y i : ℝ)) ''
      {y | ∀ c ∈ Φ, ∑ i, c i * y i = 0}) := by
  classical
  set S : Submodule ℚ (Dual ℚ (ι → ℚ)) := Submodule.span ℚ ((dotProductEquiv ℚ ι) '' Φ)
  set KQ : Submodule ℚ (ι → ℚ) := S.dualCoannihilator
  have hKQmem : ∀ y, y ∈ KQ → ∀ c ∈ Φ, ∑ i, c i * y i = 0 := by
    intro y hy c hc
    have := (Submodule.mem_dualCoannihilator _).1 hy ((dotProductEquiv ℚ ι) c)
      (Submodule.subset_span ⟨c, hc, rfl⟩)
    simpa [dotProduct] using this
  let b := Module.finBasis ℚ KQ
  let v : Fin (finrank ℚ KQ) → ι → ℚ := fun i => (b i : ι → ℚ)
  have hv : LinearIndependent ℚ v := b.linearIndependent.map' KQ.subtype (by simp)
  let B := Basis.sumExtend hv
  have : Finite (Fin (finrank ℚ KQ) ⊕ Basis.sumExtendIndex hv) := Module.Finite.finite_basis B
  have := Fintype.ofFinite (Fin (finrank ℚ KQ) ⊕ Basis.sumExtendIndex hv)
  have hBℝ : LinearIndependent ℝ (fun t => fun i => ((B t i : ℚ) : ℝ)) :=
    (linearIndependent_algebraMap_comp_iff (ι := Fin (finrank ℚ KQ) ⊕ Basis.sumExtendIndex hv)
      (ι' := ι) (R := ℚ) (S := ℝ) (v := fun t => (B t : ι → ℚ))).2 B.linearIndependent
  have hcard : Fintype.card (Fin (finrank ℚ KQ) ⊕ Basis.sumExtendIndex hv) =
      finrank ℝ (ι → ℝ) := by
    rw [← Module.finrank_eq_card_basis B]
    simp
  let Bℝ := basisOfLinearIndependentOfCardEqFinrank' _ hBℝ hcard
  have hBℝ_apply : ∀ t, Bℝ t = fun i => ((B t i : ℚ) : ℝ) := fun t => by
    simp [Bℝ]
  rw [← Bℝ.sum_repr x]
  refine Submodule.sum_mem _ fun t _ => ?_
  rcases t with i | j
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, hKQmem _ (b i).2, ?_⟩)
    rw [hBℝ_apply]
    simp [B, v, sumExtend_inl]
  · have h2 : Bℝ.repr x (Sum.inr j) = 0 := by
      rw [← Module.Basis.coord_apply, coord_eq_realizeFunctional B Bℝ hBℝ_apply]
      exact realizeFunctional_eq_zero_of_mem_span hx (sumExtend_coord_inr_mem (S := S) b hv j)
    rw [h2, zero_smul]
    exact Submodule.zero_mem _

end KeyLemma

section RationalHull

variable {r : ℕ}

/-- The value `∑ⱼ cⱼ xⱼ + q` of the rational affine function with data `f = (c, q)`. -/
def ratAffineForm (f : (Fin r → ℚ) × ℚ) (x : Fin r → ℝ) : ℝ :=
  ∑ j, (f.1 j : ℝ) * x j + f.2

/-- A rational affine function is continuous. -/
theorem continuous_ratAffineForm (f : (Fin r → ℚ) × ℚ) : Continuous (ratAffineForm f) := by
  unfold ratAffineForm
  fun_prop

/-- A rational affine function `φ` satisfies
`φ (c • (x - y) + z) = c * (φ x - φ y) + φ z`. -/
theorem ratAffineForm_affine (f : (Fin r → ℚ) × ℚ) (c : ℝ) (x y z : Fin r → ℝ) :
    ratAffineForm f (c • (x - y) + z) = c * (ratAffineForm f x - ratAffineForm f y) +
      ratAffineForm f z := by
  simp only [ratAffineForm, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [show ∑ j, (f.1 j : ℝ) * (c * (x j - y j) + z j) =
      ∑ j, (c * ((f.1 j : ℝ) * x j) - c * ((f.1 j : ℝ) * y j) + (f.1 j : ℝ) * z j) from
    Finset.sum_congr rfl fun j _ => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The cone-like sets `N ⊆ ℝ^r` cut out by finitely many rational affine equations and weak
inequalities. -/
def IsRationalPolyhedron (N : Set (Fin r → ℝ)) : Prop :=
  ∃ E I : Finset ((Fin r → ℚ) × ℚ),
    N = {x | (∀ f ∈ E, ratAffineForm f x = 0) ∧ ∀ f ∈ I, 0 ≤ ratAffineForm f x}

/-- The smallest rational affine subspace containing `δ`. -/
def rationalAffineHull (δ : Fin r → ℝ) : AffineSubspace ℝ (Fin r → ℝ) where
  carrier := {x | ∀ f : (Fin r → ℚ) × ℚ, ratAffineForm f δ = 0 → ratAffineForm f x = 0}
  smul_vsub_vadd_mem' c p₁ p₂ p₃ h₁ h₂ h₃ f hf := by
    simp only [vsub_eq_sub, vadd_eq_add]
    rw [ratAffineForm_affine f c p₁ p₂ p₃, h₁ f hf, h₂ f hf, h₃ f hf]
    ring

/-- A point lies in `rationalAffineHull δ` iff it satisfies every rational affine equation
satisfied by `δ`. -/
theorem mem_rationalAffineHull {δ x : Fin r → ℝ} :
    x ∈ rationalAffineHull δ ↔ ∀ f, ratAffineForm f δ = 0 → ratAffineForm f x = 0 := Iff.rfl

/-- A point lies in its own rational affine hull. -/
theorem self_mem_rationalAffineHull (δ : Fin r → ℝ) : δ ∈ rationalAffineHull δ :=
  fun _ h => h

/-- A rational polyhedron `N` is a neighbourhood of each of its points `δ` within
`rationalAffineHull δ`. -/
theorem mem_nhdsWithin_rationalAffineHull {N : Set (Fin r → ℝ)} (hN : IsRationalPolyhedron N)
    {δ : Fin r → ℝ} (hδ : δ ∈ N) :
    N ∈ 𝓝[(rationalAffineHull δ : Set (Fin r → ℝ))] δ := by
  classical
  obtain ⟨E, I, rfl⟩ := hN
  obtain ⟨hE, hI⟩ := hδ
  set U : Set (Fin r → ℝ) := {x | ∀ f ∈ I, ratAffineForm f δ ≠ 0 → 0 < ratAffineForm f x}
  have hUn : U ∈ 𝓝 δ := by
    have : ∀ᶠ x in 𝓝 δ, ∀ f ∈ I, ratAffineForm f δ ≠ 0 → 0 < ratAffineForm f x := by
      refine (Filter.eventually_all_finset I).2 fun f hf => ?_
      by_cases h0 : ratAffineForm f δ = 0
      · simp [h0]
      · have hpos : 0 < ratAffineForm f δ := lt_of_le_of_ne (hI f hf) (Ne.symm h0)
        have := (continuous_ratAffineForm f).continuousAt.eventually (lt_mem_nhds hpos)
        filter_upwards [this] with x hx _ using hx
    exact this
  refine Filter.mem_of_superset (inter_mem (nhdsWithin_le_nhds hUn) self_mem_nhdsWithin)
    fun x ⟨hxU, hxW⟩ => ⟨fun f hf => hxW f (hE f hf), fun f hf => ?_⟩
  by_cases h0 : ratAffineForm f δ = 0
  · exact (hxW f h0).ge
  · exact (hxU f hf h0).le

/-- The hull `rationalAffineHull δ` contains a rational point. -/
theorem exists_rat_mem_rationalAffineHull (δ : Fin r → ℝ) :
    ∃ p : Fin r → ℚ, (fun j => (p j : ℝ)) ∈ rationalAffineHull δ := by
  classical
  set Z : Set ((Fin r → ℚ) × ℚ) := {f | ratAffineForm f δ = 0}
  let Φ1 : Set (Option (Fin r) → ℚ) := {c | ∃ f ∈ Z, c = fun o => o.elim f.2 f.1}
  let ŷ : Option (Fin r) → ℝ := fun o => o.elim 1 δ
  have h1 := mem_span_rational_solutions Φ1 ŷ (by
    rintro c ⟨f, hf, rfl⟩
    have hf' : ratAffineForm f δ = 0 := hf
    simpa [ŷ, Fintype.sum_option, ratAffineForm, add_comm] using hf')
  obtain ⟨y, hyR, hy0⟩ : ∃ y : Option (Fin r) → ℚ, (∀ c ∈ Φ1, ∑ i, c i * y i = 0) ∧ y none ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let π : (Option (Fin r) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj none
    have : Submodule.span ℝ ((fun y : Option (Fin r) → ℚ => fun i => (y i : ℝ)) ''
        {y | ∀ c ∈ Φ1, ∑ i, c i * y i = 0}) ≤ LinearMap.ker π := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp [π, hcon y hy]
    have := this h1
    simp [π, ŷ] at this
  refine ⟨fun j => y (some j) / y none, fun f hf => ?_⟩
  have := hyR _ ⟨f, hf, rfl⟩
  simp only [Fintype.sum_option, Option.elim] at this
  unfold ratAffineForm
  push_cast
  have h2 : (f.2 : ℝ) * (y none : ℝ) + ∑ j, (f.1 j : ℝ) * (y (some j) : ℝ) = 0 := by
    exact_mod_cast (by linarith : f.2 * y none + ∑ j, f.1 j * y (some j) = 0)
  have h3 : (y none : ℝ) ≠ 0 := by exact_mod_cast hy0
  have h4 : ∑ j, (f.1 j : ℝ) * ((y (some j) : ℝ) / y none) =
      (∑ j, (f.1 j : ℝ) * y (some j)) / y none := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h4, div_add' _ _ _ h3, div_eq_zero_iff]
  exact Or.inl (by linarith)

/-- If `p` lies in `rationalAffineHull δ` and the rational vectors `eᵢ` satisfy the linear part
of every rational affine equation satisfied by `δ`, then every `p + ∑ sᵢ eᵢ` lies in the hull. -/
theorem add_sum_mem_rationalAffineHull {δ : Fin r → ℝ} {p : Fin r → ℚ}
    (hpW : (fun j => (p j : ℝ)) ∈ rationalAffineHull δ) {m : ℕ} {e : Fin m → Fin r → ℚ}
    (he : ∀ i, ∀ f : (Fin r → ℚ) × ℚ, ratAffineForm f δ = 0 → ∑ j, f.1 j * e i j = 0)
    (s : Fin m → ℝ) :
    (fun j => (p j : ℝ) + ∑ i, s i * (e i j : ℝ)) ∈ rationalAffineHull δ := by
  intro f hf
  have h2 := hpW f hf
  simp only [ratAffineForm] at h2 ⊢
  have h4 : ∀ i, ∑ j, (f.1 j : ℝ) * (e i j : ℝ) = 0 := fun i => by exact_mod_cast he i f hf
  calc ∑ j, (f.1 j : ℝ) * ((p j : ℝ) + ∑ i, s i * (e i j : ℝ)) + (f.2 : ℝ)
      = (∑ j, (f.1 j : ℝ) * (p j : ℝ) + f.2) + ∑ i, s i * ∑ j, (f.1 j : ℝ) * (e i j : ℝ) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∑ i, ∑ j, (f.1 j : ℝ) * (s i * (e i j : ℝ)) =
            ∑ i, ∑ j, s i * ((f.1 j : ℝ) * (e i j : ℝ)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        rw [this]
        ring
    _ = 0 := by simp [h4, h2]

/-- The hull `rationalAffineHull δ` has a rational point and a rational direction basis. -/
theorem exists_rational_frame (δ : Fin r → ℝ) :
    ∃ (m : ℕ) (p : Fin r → ℚ) (e : Fin m → Fin r → ℚ), LinearIndependent ℚ e ∧
      (fun j => (p j : ℝ)) ∈ rationalAffineHull δ ∧
      ∀ x, x ∈ rationalAffineHull δ ↔
        ∃ s : Fin m → ℝ, x = fun j => (p j : ℝ) + ∑ i, s i * (e i j : ℝ) := by
  classical
  set Z : Set ((Fin r → ℚ) × ℚ) := {f | ratAffineForm f δ = 0}
  obtain ⟨p, hpW⟩ := exists_rat_mem_rationalAffineHull δ
  let R2 : Submodule ℚ (Fin r → ℚ) :=
    { carrier := {y | ∀ f ∈ Z, ∑ j, f.1 j * y j = 0}
      add_mem' := fun {y y'} hy hy' f hf => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hy f hf, hy' f hf, add_zero]
      zero_mem' := fun f _ => by simp
      smul_mem' := fun q y hy f hf => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ q, ← Finset.mul_sum, hy f hf,
          mul_zero] }
  let b := Module.finBasis ℚ R2
  let e : Fin (finrank ℚ R2) → Fin r → ℚ := fun i => (b i : Fin r → ℚ)
  refine ⟨finrank ℚ R2, p, e, b.linearIndependent.map' R2.subtype (by simp), hpW,
    fun x => ⟨fun hx => ?_, ?_⟩⟩
  · set z : Fin r → ℝ := x - fun j => (p j : ℝ) with hzdef
    have hz : ∀ c ∈ (fun f : (Fin r → ℚ) × ℚ => f.1) '' Z, ∑ j, (c j : ℝ) * z j = 0 := by
      rintro _ ⟨f, hf, rfl⟩
      have h1 := hx f hf
      have h2 := hpW f hf
      simp only [ratAffineForm] at h1 h2
      simp only [hzdef, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      linarith
    have hle : Submodule.span ℝ ((fun y : Fin r → ℚ => fun i => (y i : ℝ)) ''
        {y | ∀ c ∈ (fun f : (Fin r → ℚ) × ℚ => f.1) '' Z, ∑ i, c i * y i = 0}) ≤
        Submodule.span ℝ (Set.range fun i => fun j => (e i j : ℝ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ R2 := fun f hf => hy _ ⟨f, hf, rfl⟩
      have hy'' : y = ∑ i, (b.repr ⟨y, hy'⟩ i) • e i := coe_eq_sum_repr_smul b ⟨y, hy'⟩
      have : (fun j => (y j : ℝ)) =
          ∑ i, ((b.repr ⟨y, hy'⟩ i : ℚ) : ℝ) • fun j => (e i j : ℝ) := by
        ext j
        conv_lhs => rw [hy'']
        simp
      change (fun j => (y j : ℝ)) ∈ Submodule.span ℝ _
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
      (hle (mem_span_rational_solutions _ z hz))
    refine ⟨c, ?_⟩
    ext j
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hzdef, Pi.sub_apply] at this
    linarith
  · rintro ⟨s, rfl⟩
    exact add_sum_mem_rationalAffineHull hpW (fun i f hf => (b i).2 f hf) s

/-- The sets `{x | ∀ f ∈ F, f(x) = 0}` for finitely many rational affine functions `f`: the
rational affine subspaces of `ℝ^r`. -/
def IsRationalAffineSubspace (V : Set (Fin r → ℝ)) : Prop :=
  ∃ F : Finset ((Fin r → ℚ) × ℚ), V = {x | ∀ f ∈ F, ratAffineForm f x = 0}

/-- The hull is contained in every rational affine subspace containing `δ`. -/
theorem rationalAffineHull_le {δ : Fin r → ℝ} {V : Set (Fin r → ℝ)}
    (hV : IsRationalAffineSubspace V) (hδ : δ ∈ V) :
    (rationalAffineHull δ : Set (Fin r → ℝ)) ⊆ V := by
  obtain ⟨F, rfl⟩ := hV
  exact fun x hx f hf => hx f (hδ f hf)

/-- The hull is itself a rational affine subspace (it is cut out by finitely many rational
affine equations), so it is the smallest rational affine subspace containing `δ`. -/
theorem isRationalAffineSubspace_rationalAffineHull (δ : Fin r → ℝ) :
    IsRationalAffineSubspace (rationalAffineHull δ : Set (Fin r → ℝ)) := by
  classical
  let L : (Fin r → ℝ) → ((Fin r → ℚ) × ℚ) →ₗ[ℚ] ℝ := fun x =>
    { toFun := fun f => ratAffineForm f x
      map_add' := fun f g => by
        simp [ratAffineForm, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun q f => by
        simp [ratAffineForm, Rat.smul_def, Finset.mul_sum, mul_assoc] }
  let Zs : Submodule ℚ ((Fin r → ℚ) × ℚ) := LinearMap.ker (L δ)
  let b := Module.finBasis ℚ Zs
  refine ⟨Finset.univ.image fun i => (b i : (Fin r → ℚ) × ℚ), ?_⟩
  ext x
  refine ⟨fun hx f hf => ?_, fun hx f hf => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hf
    exact hx _ (b i).2
  · have hsub : Zs ≤ LinearMap.ker (L x) := by
      intro g hg
      have : g = ∑ i, (b.repr ⟨g, hg⟩ i) • (b i : (Fin r → ℚ) × ℚ) :=
        coe_eq_sum_repr_smul b ⟨g, hg⟩
      rw [LinearMap.mem_ker, this, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul]
      have := hx _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
      rw [this, smul_zero]
    exact hsub (show f ∈ Zs from hf)

/-- A rational parallelotope in `ℝ^r`: the image of a box `∏ [aᵢ, bᵢ]` with rational endpoints
under `s ↦ p + ∑ sᵢ eᵢ`, for a rational point `p` and `ℚ`-linearly independent rational vectors
`eᵢ`; its dimension is `d`. -/
def IsRationalParallelotope (Q : Set (Fin r → ℝ)) : Prop :=
  ∃ (d : ℕ) (p : Fin r → ℚ) (e : Fin d → Fin r → ℚ) (a b : Fin d → ℚ),
    LinearIndependent ℚ e ∧ (∀ i, a i < b i) ∧
    Q = {x | ∃ s : Fin d → ℝ, (∀ i, (a i : ℝ) ≤ s i ∧ s i ≤ b i) ∧
      x = fun j => (p j : ℝ) + ∑ i, s i * (e i j : ℝ)}

/-- For `ℚ`-linearly independent rational vectors `eᵢ` and a rational point `p`, the map
`s ↦ p + ∑ sᵢ eᵢ` has a continuous left inverse. -/
theorem exists_continuous_leftInverse_frame {m : ℕ} (p : Fin r → ℚ) {e : Fin m → Fin r → ℚ}
    (hind : LinearIndependent ℚ e) :
    ∃ Ψ : (Fin r → ℝ) → Fin m → ℝ, Continuous Ψ ∧
      ∀ s, Ψ (fun j => (p j : ℝ) + ∑ i, s i * (e i j : ℝ)) = s := by
  have hindR : LinearIndependent ℝ (fun i => fun j => (e i j : ℝ)) :=
    linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ) (v := e) |>.2 hind
  let Φ : (Fin m → ℝ) →ₗ[ℝ] (Fin r → ℝ) := Fintype.linearCombination ℝ (fun i j => (e i j : ℝ))
  obtain ⟨Ψ, hΨ⟩ := Φ.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hindR.fintypeLinearCombination_injective)
  refine ⟨fun x => Ψ (x - fun j => (p j : ℝ)),
    (LinearMap.continuous_of_finiteDimensional Ψ).comp (continuous_id.sub continuous_const),
    fun s => ?_⟩
  have h : (fun j => (p j : ℝ) + ∑ i, s i * (e i j : ℝ)) - (fun j => (p j : ℝ)) = Φ s := by
    ext j
    simp [Φ, Fintype.linearCombination_apply]
  exact (congrArg Ψ h).trans (LinearMap.congr_fun hΨ s)

/-- Every neighbourhood of `t` in `ℝ^m` contains a box with rational endpoints around `t`. -/
theorem exists_rat_box_subset {m : ℕ} {U : Set (Fin m → ℝ)} {t : Fin m → ℝ} (hU : U ∈ 𝓝 t) :
    ∃ a b : Fin m → ℚ, (∀ i, (a i : ℝ) < t i ∧ t i < b i) ∧
      ∀ s : Fin m → ℝ, (∀ i, (a i : ℝ) ≤ s i ∧ s i ≤ b i) → s ∈ U := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hU
  choose a ha1 ha2 using fun i => exists_rat_btwn (show t i - ρ < t i by linarith)
  choose b hb1 hb2 using fun i => exists_rat_btwn (show t i < t i + ρ by linarith)
  refine ⟨a, b, fun i => ⟨ha2 i, hb1 i⟩, fun s hs => hball ?_⟩
  rw [Metric.mem_ball]
  refine (dist_pi_lt_iff hρ).2 fun i => ?_
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [(hs i).1, (hs i).2, ha1 i, hb2 i]

/-- A subset `Q` of an affine subspace `W` which is a neighbourhood within `W` of a point of `W`
spans `W`. -/
theorem affineSpan_eq_of_mem_nhdsWithin {Q : Set (Fin r → ℝ)} {W : AffineSubspace ℝ (Fin r → ℝ)}
    {δ : Fin r → ℝ} (hδ : δ ∈ W) (hQW : Q ⊆ W) (hQ : Q ∈ 𝓝[(W : Set (Fin r → ℝ))] δ) :
    affineSpan ℝ Q = W := by
  refine le_antisymm (affineSpan_le.2 hQW) fun x hxW => ?_
  let g : ℝ → (Fin r → ℝ) := fun l => l • (x - δ) + δ
  have hgc : Continuous g := by
    simp only [g]
    fun_prop
  have hgW : ∀ l, g l ∈ W := fun l => W.smul_vsub_vadd_mem l hxW hδ hδ
  have hg0 : g 0 = δ := by simp [g]
  have hT : Tendsto g (𝓝 0) (𝓝[(W : Set (Fin r → ℝ))] δ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall hgW⟩
    have := hgc.tendsto 0
    rwa [hg0] at this
  obtain ⟨ε, hε, hεQ⟩ := Metric.mem_nhds_iff.1 (hT hQ)
  have hl : (ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hδa : δ ∈ affineSpan ℝ Q := subset_affineSpan ℝ Q (mem_of_mem_nhdsWithin hδ hQ)
  have := (affineSpan ℝ Q).smul_vsub_vadd_mem (2 / ε) (subset_affineSpan ℝ Q (hεQ hl)) hδa hδa
  have h6 : (2 / ε) • (g (ε / 2) -ᵥ δ) +ᵥ δ = x := by
    simp only [g, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul]
    rw [show 2 / ε * (ε / 2) = 1 by field_simp, one_smul]
    abel
  rwa [h6] at this

/-- A point of the affine span of `Q` at which `Q` is a neighbourhood within its affine span lies
in the intrinsic interior of `Q`. -/
theorem mem_intrinsicInterior_of_mem_nhdsWithin {Q : Set (Fin r → ℝ)} {δ : Fin r → ℝ}
    (hδ : δ ∈ affineSpan ℝ Q) (hQ : Q ∈ 𝓝[(affineSpan ℝ Q : Set (Fin r → ℝ))] δ) :
    δ ∈ intrinsicInterior ℝ Q := by
  rw [mem_intrinsicInterior]
  refine ⟨⟨δ, hδ⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds]
  exact (preimage_coe_mem_nhds_subtype (s := (affineSpan ℝ Q : Set (Fin r → ℝ))) (t := Q)
    (a := ⟨δ, hδ⟩)).2 hQ

/-- For a point `δ` of a rational polyhedron `N`, there is a rational parallelotope `Q`
contained in `N ∩ rationalAffineHull δ`, containing `δ` in its intrinsic interior, and whose
affine span is `rationalAffineHull δ`. -/
theorem exists_rationalParallelotope {N : Set (Fin r → ℝ)} (hN : IsRationalPolyhedron N)
    {δ : Fin r → ℝ} (hδ : δ ∈ N) :
    ∃ Q : Set (Fin r → ℝ), IsRationalParallelotope Q ∧
      Q ⊆ N ∩ (rationalAffineHull δ : Set (Fin r → ℝ)) ∧ δ ∈ intrinsicInterior ℝ Q ∧
      affineSpan ℝ Q = rationalAffineHull δ := by
  classical
  obtain ⟨m, p, e, hind, hpW, hchar⟩ := exists_rational_frame δ
  have hNn := mem_nhdsWithin_rationalAffineHull hN hδ
  set W := rationalAffineHull δ
  let φ : (Fin m → ℝ) → (Fin r → ℝ) := fun s j => (p j : ℝ) + ∑ i, s i * (e i j : ℝ)
  have hφW : ∀ s, φ s ∈ W := fun s => (hchar _).2 ⟨s, rfl⟩
  have hφc : Continuous φ := by
    refine continuous_pi fun j => ?_
    simp only [φ]
    fun_prop
  obtain ⟨t, ht⟩ := (hchar δ).1 (self_mem_rationalAffineHull δ)
  have ht' : φ t = δ := ht.symm
  obtain ⟨Ψ, hΨc, hΨ⟩ := exists_continuous_leftInverse_frame p hind
  have hΨφ : ∀ s, Ψ (φ s) = s := hΨ
  have hpre : φ ⁻¹' N ∈ 𝓝 t :=
    tendsto_nhdsWithin_iff.2 ⟨ht' ▸ hφc.tendsto t, Eventually.of_forall hφW⟩ hNn
  obtain ⟨a, b, hab, hsub⟩ := exists_rat_box_subset hpre
  let Q : Set (Fin r → ℝ) := {x | ∃ s : Fin m → ℝ, (∀ i, (a i : ℝ) ≤ s i ∧ s i ≤ b i) ∧ x = φ s}
  have hQpar : IsRationalParallelotope Q :=
    ⟨m, p, e, a, b, hind, fun i => by exact_mod_cast (hab i).1.trans (hab i).2, rfl⟩
  have hQN : Q ⊆ N ∩ (W : Set (Fin r → ℝ)) := by
    rintro x ⟨s, hs, rfl⟩
    exact ⟨hsub s hs, hφW s⟩
  let box : Set (Fin m → ℝ) := Set.pi univ fun i => Ioo (a i : ℝ) (b i)
  have hbox : IsOpen box := isOpen_set_pi finite_univ fun i _ => isOpen_Ioo
  have hV : Ψ ⁻¹' box ∈ 𝓝 δ := by
    refine (hbox.preimage hΨc).mem_nhds ?_
    rw [Set.mem_preimage, ← ht', hΨφ]
    exact fun i _ => hab i
  have hQnhds : Q ∈ 𝓝[(W : Set (Fin r → ℝ))] δ := by
    refine mem_of_superset (inter_mem (nhdsWithin_le_nhds hV) self_mem_nhdsWithin)
      fun x ⟨hx, hxW⟩ => ?_
    obtain ⟨s, rfl⟩ := (hchar x).1 hxW
    have hs : ∀ i, Ψ (φ s) i ∈ Ioo (a i : ℝ) (b i) := fun i => hx i (mem_univ i)
    rw [hΨφ] at hs
    exact ⟨s, fun i => ⟨(hs i).1.le, (hs i).2.le⟩, rfl⟩
  have hAff : affineSpan ℝ Q = W :=
    affineSpan_eq_of_mem_nhdsWithin (self_mem_rationalAffineHull δ) (fun x hx => (hQN hx).2) hQnhds
  exact ⟨Q, hQpar, hQN, mem_intrinsicInterior_of_mem_nhdsWithin
    (hAff ▸ self_mem_rationalAffineHull δ) (hAff ▸ hQnhds), hAff⟩

/-- **Openness along the smallest rational affine hull.** Let `N ⊆ ℝ^r` be cut out by finitely
many rational affine equations and weak inequalities, and let `δ ∈ N`. Let `W` be the smallest
rational affine subspace containing `δ`. Then `N` is a neighbourhood of `δ` in `W`, and there is a
rational parallelotope `Q ⊆ N ∩ W` with `δ` in its relative interior and with affine hull `W`
(when `dim W = 0`, necessarily `Q = {δ}`). -/
@[mmp "lem_fourfold_rational_hull_neighborhood"]
theorem rational_hull_neighborhood {N : Set (Fin r → ℝ)} (hN : IsRationalPolyhedron N)
    {δ : Fin r → ℝ} (hδ : δ ∈ N) :
    N ∈ 𝓝[(rationalAffineHull δ : Set (Fin r → ℝ))] δ ∧
      ∃ Q : Set (Fin r → ℝ), IsRationalParallelotope Q ∧
        Q ⊆ N ∩ (rationalAffineHull δ : Set (Fin r → ℝ)) ∧ δ ∈ intrinsicInterior ℝ Q ∧
        affineSpan ℝ Q = rationalAffineHull δ :=
  ⟨mem_nhdsWithin_rationalAffineHull hN hδ, exists_rationalParallelotope hN hδ⟩

end RationalHull

end MMP.Fourfold
