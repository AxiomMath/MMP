module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StableBase
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas

/-!
# Pull-backs of real Cartier divisors and fixed parts on a common birational model

## Main definitions

* `MMP.Fourfold.IsRelativelyFreeDivisor`: a divisor whose sheaf `𝒪_X(D)` is relatively free.

## Main results

* `MMP.Fourfold.isEffective_of_isRCartierPullback`: the pull-back of an effective real Cartier
  divisor under a dominant morphism of normal varieties is effective.
* `MMP.Fourfold.sections_and_fixed_part_of_pullback_eq_add`: sections and fixed parts on a
  common birational model.

## Auxiliary results

* `MMP.Fourfold.sum_mul_nonneg_of_forall_int`: a homogeneous implication between finitely many
  integral linear inequalities that holds over `ℤ` also holds over `ℝ`.
* `MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn`: pull-backs of Cartier divisors
  effective on an open are effective over it.
* `MMP.Fourfold.exists_coeff_add_ord_eq_zero_of_isRelativelyFree`: a relatively free Cartier
  divisor has, near every point, a relative section generating at that point.
* `MMP.Fourfold.exists_pullbackRationalFunction_eq`: pull-back of rational functions along a
  birational morphism is surjective on units.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Rational approximation of real solutions of integral linear inequalities -/

section LinearAlgebra

open Finset

/-- Clearing denominators: a homogeneous implication between finitely many integral linear
inequalities holds over `ℚ` once it holds over `ℤ`. -/
theorem sum_mul_nonneg_of_forall_int_rat {ι : Type*} {m : ℕ} (a : ι → Fin m → ℤ)
    (c : Fin m → ℤ)
    (hint : ∀ n : Fin m → ℤ, (∀ i, 0 ≤ ∑ j, a i j * n j) → 0 ≤ ∑ j, c j * n j)
    (n : Fin m → ℚ) (hn : ∀ i, 0 ≤ ∑ j, (a i j : ℚ) * n j) : 0 ≤ ∑ j, (c j : ℚ) * n j := by
  classical
  set D : ℕ := ∏ j, (n j).den with hD
  have hDpos : (0 : ℚ) < D := by
    rw [hD]
    push_cast
    exact Finset.prod_pos fun j _ => by exact_mod_cast (n j).den_pos
  let N : Fin m → ℤ := fun j => (n j).num * ∏ k ∈ univ.erase j, ((n k).den : ℤ)
  have hN : ∀ j, (N j : ℚ) = D * n j := by
    intro j
    have h1 : (D : ℚ) = (n j).den * ∏ k ∈ univ.erase j, ((n k).den : ℚ) := by
      rw [hD]
      push_cast
      exact (Finset.mul_prod_erase _ _ (mem_univ j)).symm
    simp only [N]
    push_cast
    rw [h1, ← Rat.mul_den_eq_num]
    ring
  have key : ∀ α : Fin m → ℤ, ((∑ j, α j * N j : ℤ) : ℚ) = D * ∑ j, (α j : ℚ) * n j := by
    intro α
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hN]
    ring
  have h := hint N fun i => by
    have h0 : (0 : ℚ) ≤ ((∑ j, a i j * N j : ℤ) : ℚ) := by
      rw [key]
      exact mul_nonneg hDpos.le (hn i)
    exact_mod_cast h0
  have h' : (0 : ℚ) ≤ ((∑ j, c j * N j : ℤ) : ℚ) := by exact_mod_cast h
  rw [key] at h'
  exact (mul_nonneg_iff_of_pos_left hDpos).mp h'

/-- **Rational points near a real point.** For `r ∈ ℝ^m` and finitely many integral `α` with
`α · r > 0`, there is a rational `n` with `α · n > 0` for each of them and `β · n = 0` for every
integral `β` with `β · r = 0`. -/
theorem exists_rat_sum_mul_pos_of_real {m : ℕ} (r : Fin m → ℝ) (S : Finset (Fin m → ℤ))
    (hS : ∀ α ∈ S, 0 < ∑ j, (α j : ℝ) * r j) :
    ∃ n : Fin m → ℚ, (∀ α ∈ S, 0 < ∑ j, (α j : ℚ) * n j) ∧
      ∀ β : Fin m → ℤ, ∑ j, (β j : ℝ) * r j = 0 → ∑ j, (β j : ℚ) * n j = 0 := by
  classical
  set V : Submodule ℚ ℝ := Submodule.span ℚ (Set.range r)
  have : FiniteDimensional ℚ V := FiniteDimensional.span_of_finite ℚ (Set.finite_range r)
  set b := Module.finBasis ℚ V
  set k := Module.finrank ℚ V
  let rv : Fin m → V := fun j => ⟨r j, Submodule.subset_span ⟨j, rfl⟩⟩
  let vec : (Fin m → ℤ) → V := fun α => ∑ j, (α j : ℚ) • rv j
  have hvec : ∀ α, ((vec α : V) : ℝ) = ∑ j, (α j : ℝ) * r j := by
    intro α
    simp only [vec, Submodule.coe_sum, Submodule.coe_smul, rv, Rat.smul_def]
    push_cast
    rfl
  let Λ : (Fin k → ℝ) → V → ℝ := fun x v => ∑ l, (b.repr v l : ℝ) * x l
  have hΛcont : ∀ v, Continuous fun x => Λ x v := fun v => by
    simp only [Λ]
    fun_prop
  let x₀ : Fin k → ℝ := fun l => (b l : ℝ)
  have hΛ₀ : ∀ v, Λ x₀ v = v := by
    intro v
    conv_rhs => rw [← b.sum_repr v]
    simp only [Λ, x₀, Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def]
  set O : Set (Fin k → ℝ) := {x | ∀ α ∈ S, 0 < Λ x (vec α)}
  have hO : IsOpen O := by
    have : O = ⋂ α ∈ S, {x | 0 < Λ x (vec α)} := by
      ext
      simp [O]
    rw [this]
    exact isOpen_biInter_finset fun α _ => isOpen_lt continuous_const (hΛcont _)
  have hx₀ : x₀ ∈ O := fun α hα => by
    rw [hΛ₀, hvec]
    exact hS α hα
  have hdense : Dense (Set.univ.pi fun _ : Fin k => Set.range (Rat.cast : ℚ → ℝ)) :=
    dense_pi _ fun _ _ => Rat.denseRange_cast
  obtain ⟨x, hxO, hxq⟩ := hdense.inter_open_nonempty O hO ⟨x₀, hx₀⟩
  choose y hy using fun l => hxq l (Set.mem_univ _)
  let n : Fin m → ℚ := fun j => ∑ l, b.repr (rv j) l * y l
  have hn : ∀ α : Fin m → ℤ, ((∑ j, (α j : ℚ) * n j : ℚ) : ℝ) = Λ x (vec α) := by
    intro α
    simp only [n, Λ, vec, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, ← hy]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine ⟨n, fun α hα => ?_, fun β hβ => ?_⟩
  · have h := hxO α hα
    rw [← hn] at h
    exact_mod_cast h
  · have hv : vec β = 0 := Subtype.ext ((hvec β).trans hβ)
    have h := hn β
    rw [hv] at h
    simp only [Λ, map_zero, Finsupp.coe_zero, Pi.zero_apply, Rat.cast_zero, zero_mul,
      Finset.sum_const_zero] at h
    exact_mod_cast h

/-- **Rational approximation.** Let `aᵢ, c ∈ ℤ^m` with only finitely many `aᵢ ≠ 0`. If every
integral `n` with `aᵢ · n ≥ 0` for all `i` has `c · n ≥ 0`, then every real `r` with `aᵢ · r ≥ 0`
for all `i` has `c · r ≥ 0`. -/
theorem sum_mul_nonneg_of_forall_int {ι : Type*} {m : ℕ} (a : ι → Fin m → ℤ)
    (c : Fin m → ℤ) (r : Fin m → ℝ) (hfin : {i | a i ≠ 0}.Finite)
    (hint : ∀ n : Fin m → ℤ, (∀ i, 0 ≤ ∑ j, a i j * n j) → 0 ≤ ∑ j, c j * n j)
    (hr : ∀ i, 0 ≤ ∑ j, (a i j : ℝ) * r j) : 0 ≤ ∑ j, (c j : ℝ) * r j := by
  classical
  by_contra hneg
  push Not at hneg
  set P := hfin.toFinset.filter fun i => 0 < ∑ j, (a i j : ℝ) * r j
  obtain ⟨n, hpos, hzero⟩ := exists_rat_sum_mul_pos_of_real r (insert (-c) (P.image a)) (by
    simp only [Finset.mem_insert, Finset.mem_image]
    rintro α (rfl | ⟨i, hi, rfl⟩)
    · simpa only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_pos]
        using hneg
    · exact (Finset.mem_filter.mp hi).2)
  have hrat := sum_mul_nonneg_of_forall_int_rat a c hint n fun i => by
    by_cases h0 : ∑ j, (a i j : ℝ) * r j = 0
    · exact (hzero _ h0).ge
    · have hai : a i ≠ 0 := by
        rintro hai
        apply h0
        simp [hai]
      have hiP : i ∈ P :=
        Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hai, lt_of_le_of_ne (hr i) (Ne.symm h0)⟩
      exact (hpos _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hiP))).le
  have hc := hpos (-c) (Finset.mem_insert_self _ _)
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_pos] at hc
  linarith

end LinearAlgebra

/-! ### Generic points of integral schemes -/

section Generic

variable {X Y : Scheme.{u}}

/-- On an irreducible scheme the generic point of every irreducible component is the generic point. -/
theorem componentGenericPoint_eq_genericPoint [IrreducibleSpace X] (Z : irreducibleComponents X) :
    componentGenericPoint X Z = genericPoint X := by
  have h1 := isGenericPoint_componentGenericPoint X Z
  have hZ : Z.1 = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using Z.2
  rw [hZ] at h1
  exact h1.eq (genericPoint_spec X)

/-- A dominant morphism of irreducible schemes maps the generic point outside the support of every
divisor. -/
theorem map_componentGenericPoint_notMem_supp_of_isDominant [IrreducibleSpace X] [IrreducibleSpace Y]
    (h : X ⟶ Y) [IsDominant h] (C : Divisor Y) (Z : irreducibleComponents X) :
    h (componentGenericPoint X Z) ∉ C.supp := by
  rw [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant,
    ← componentGenericPoint_eq_genericPoint (pointComponent (genericPoint Y))]
  exact MMP.Flips.componentGenericPoint_mem_divisorSuppCompl C _

/-- An irreducible space has a single irreducible component. -/
theorem subsingleton_irreducibleComponents [IrreducibleSpace X] :
    Subsingleton (irreducibleComponents X) :=
  ⟨fun a b => Subtype.ext (by
    have ha := a.2
    have hb := b.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at ha hb
    rw [ha, hb])⟩

/-- In an irreducible space every point lies on every irreducible component. -/
theorem mem_irreducibleComponent_of_irreducibleSpace [IrreducibleSpace X]
    (Z' : irreducibleComponents X) (x : X) : x ∈ Z'.1 := by
  have h' : Z'.1 = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using Z'.2
  rw [h']
  trivial

end Generic

/-! ### Effectivity of pull-backs of Cartier divisors -/

section CartierPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- **The pull-back of a Cartier divisor effective on `V` is effective on `f⁻¹V`.** If `B` has
nonnegative coefficients along the prime divisors meeting `V`, then its pull-back `B'` has
nonnegative coefficients along the prime divisors meeting `f⁻¹V`. -/
theorem coeff_nonneg_of_isPullback_of_isEffectiveOn {f : X ⟶ Y} {B : Divisor Y}
    (hBc : B.IsCartier) {V : Y.Opens}
    (hBV : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ V).Nonempty → 0 ≤ B.coeff P)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor X)
    (hE : (E.support ∩ f ⁻¹ᵁ V).Nonempty) : 0 ≤ B'.coeff E := by
  have hyV : f E.genericPoint ∈ V := (E.genericPoint_mem_iff (f ⁻¹ᵁ V)).mpr hE
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hφ' : B.IsLocalEquation (U ⊓ V) φ := hφ.mono inf_le_left
  have hE' : (E.support ∩ f ⁻¹ᵁ (U ⊓ V)).Nonempty :=
    (E.genericPoint_mem_iff (f ⁻¹ᵁ (U ⊓ V))).mp ⟨hU, hyV⟩
  rw [h (U ⊓ V) φ hφ' E hE']
  have hsp' : f (componentGenericPoint X E.component) ⤳ f E.genericPoint :=
    f.base.hom.map_specializes E.specializes_genericPoint
  set W := pointComponent (f (componentGenericPoint X E.component))
  have hW : f (componentGenericPoint X E.component) ∈ W.1 := mem_pointComponent _
  have hyW : f E.genericPoint ∈ W.1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  let ψ : ToType ((rationalFunctionsPresheaf Y).obj (op (U ⊓ V))) :=
    fun Z => (φ : RationalFunctions Y) Z.1
  have hψ : Divisor.IsDivisorialSection (0 : Divisor Y) (U ⊓ V) ψ := by
    intro P hP
    refine Or.inr ?_
    change WithZero.exp (-(0 : ℤ)) ≤ P.valuation ((φ : RationalFunctions Y) P.component)
    rw [P.valuation_component, neg_zero, WithZero.exp_le_exp, ← hφ' P hP]
    obtain ⟨x, hxP, hxU, hxV⟩ := hP
    exact hBV P ⟨x, hxP, hxV⟩
  obtain ⟨r, hr⟩ := hψ.exists_stalk_eq (x := f E.genericPoint) ⟨hU, hyV⟩ hyW
  have hZU : f (componentGenericPoint X E.component) ∈ U ⊓ V :=
    E.map_componentGenericPoint_mem f hE'
  obtain ⟨a', ha'⟩ := hφ'.exists_unit_stalk hZU (hB _) hW
  have hra : (Y.presheaf.stalkSpecializes hsp').hom r = a' := by
    apply stalkToRationalFunctions_injective hW
    rw [ha']
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact hr
  set u := pullbackComponent f hB hφ' E.component hZU with hu
  have hu' : (u : X.presheaf.stalk (componentGenericPoint X E.component)) =
      E.toComponent.hom ((f.stalkMap E.genericPoint).hom r) := by
    rw [hu, pullbackComponent_eq hB hφ' hZU hW a' ha']
    change (f.stalkMap (componentGenericPoint X E.component)).hom
      (a' : Y.presheaf.stalk (f (componentGenericPoint X E.component))) = _
    rw [← hra, Scheme.Hom.stalkSpecializes_stalkMap_apply]
    rfl
  have hs0 : (f.stalkMap E.genericPoint).hom r ≠ 0 := fun h0 =>
    u.ne_zero (by rw [hu', h0, map_zero])
  have h1 := E.one_le_valuation_toComponent hs0
  rwa [← hu', E.valuation_eq_exp_ordUnit, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- An integral combination of Cartier divisors is Cartier. -/
theorem isCartier_sum_zsmul {m : ℕ} (n : Fin m → ℤ) {L : Fin m → Divisor Y}
    (hL : ∀ j, (L j).IsCartier) (s : Finset (Fin m)) : (∑ j ∈ s, n j • L j).IsCartier := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Divisor.isCartier_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact ((hL j).zsmul _).add ih

/-- `h^*(∑ nⱼ Lⱼ) = ∑ nⱼ h^*Lⱼ` for Cartier divisors `Lⱼ` and a dominant `h` of integral
schemes. -/
theorem isPullback_sum_zsmul [IsIntegral X] [IsIntegral Y] (h : X ⟶ Y) [IsDominant h]
    {m : ℕ} (n : Fin m → ℤ) {L : Fin m → Divisor Y} {L' : Fin m → Divisor X}
    (hL : ∀ j, (L j).IsCartier)
    (hp : ∀ j, (L j).IsPullback h (map_componentGenericPoint_notMem_supp_of_isDominant h _)
      (L' j)) (s : Finset (Fin m)) :
    (∑ j ∈ s, n j • L j).IsPullback h (map_componentGenericPoint_notMem_supp_of_isDominant h _)
      (∑ j ∈ s, n j • L' j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Divisor.isPullback_zero _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact Divisor.IsPullback.add ((hL j).zsmul _) (isCartier_sum_zsmul n hL s) _
      ((hp j).zsmul (hL j) (n j) (map_componentGenericPoint_notMem_supp_of_isDominant h _)) ih

/-- The coefficients of a real combination of divisors. -/
theorem coeff_sum_smul_toRDivisor {Z : Scheme.{u}} {m : ℕ} (r : Fin m → ℝ) (C : Fin m → Divisor Z)
    (P : MMP.Mori.PrimeDivisor Z) :
    (∑ j, r j • Divisor.toRDivisor (C j)).coeff P = ∑ j, r j * ((C j).coeff P : ℝ) := by
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  rfl

/-- The coefficients of an integral combination of divisors. -/
theorem coeff_sum_zsmul {Z : Scheme.{u}} {m : ℕ} (n : Fin m → ℤ) (C : Fin m → Divisor Z)
    (P : MMP.Mori.PrimeDivisor Z) :
    (∑ j, n j • C j).coeff P = ∑ j, n j * (C j).coeff P := by
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul]

end CartierPullback

/-! ### Effectivity of pull-backs of real Cartier divisors -/

section Pullback

variable {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y] [CompactSpace T]
  [IsLocallyNoetherian T] [IsNormal T] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Pull-back of an effective real Cartier divisor.** If `h : T ⟶ Y` is a dominant morphism of
normal varieties and `L` is an effective real Cartier divisor on `Y`, then `h^*L` exists and
every pull-back `h^*L` (`MMP.Flips.IsRCartierPullback`) is effective. -/
@[mmp "lem_fourfold_effective_real_pullback"]
theorem isEffective_of_isRCartierPullback (h : T ⟶ Y) [IsDominant h] {L : RDivisor Y}
    (hLc : RDivisor.IsRCartier L) (hL : 0 ≤ L) :
    (∃ G, MMP.Flips.IsRCartierPullback h L G) ∧
      ∀ G, MMP.Flips.IsRCartierPullback h L G → 0 ≤ G := by
  constructor
  · obtain ⟨m, r, C, hC, hcoeff⟩ := hLc
    have hex := fun j => (hC j).exists_isPullback
      (map_componentGenericPoint_notMem_supp_of_isDominant h (C j))
    choose C' hC' using hex
    refine ⟨∑ j, r j • Divisor.toRDivisor (C' j), m, r, C, C', hC, ?_, fun j => ⟨_, hC' j⟩, rfl⟩
    ext P
    rw [hcoeff P, coeff_sum_smul_toRDivisor]
  · rintro G ⟨m, r, C, C', hC, hLeq, hp, rfl⟩
    have hp' : ∀ j, (C j).IsPullback h
        (map_componentGenericPoint_notMem_supp_of_isDominant h _) (C' j) := fun j =>
      (hp j).2
    rw [← DivisorWithCoeffs.isEffective_iff_nonneg]
    intro Γ
    rw [coeff_sum_smul_toRDivisor]
    have hG : ∑ j, r j * ((C' j).coeff Γ : ℝ) = ∑ j, ((C' j).coeff Γ : ℝ) * r j :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hG]
    refine sum_mul_nonneg_of_forall_int (fun P j => (C j).coeff P) (fun j => (C' j).coeff Γ) r
      ?_ ?_ ?_
    · refine (Set.Finite.biUnion (Set.finite_univ (α := Fin m)) fun j _ =>
        (C j).support.finite_toSet).subset ?_
      intro P hP
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hP
      exact Set.mem_biUnion (Set.mem_univ j) (Finsupp.mem_support_iff.mpr hj)
    · intro n hn
      have hBe : ∀ P, 0 ≤ (∑ j, n j • C j).coeff P := fun P => by
        rw [coeff_sum_zsmul]
        simpa [mul_comm] using hn P
      have := coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤)
        (isCartier_sum_zsmul n hC Finset.univ) (fun P _ => hBe P)
        (isPullback_sum_zsmul h n hC hp' Finset.univ) Γ
        ((Γ.genericPoint_mem_iff _).mp trivial)
      rw [coeff_sum_zsmul] at this
      simpa [mul_comm] using this
    · intro P
      have : 0 ≤ L.coeff P := hL P
      rw [hLeq, coeff_sum_smul_toRDivisor] at this
      simpa [mul_comm] using this

end Pullback

/-! ### Sections and fixed parts on a common birational model -/

section CommonModel

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor `D` on `X` is *relatively free* over `Z` for `f : X ⟶ Z` if the counit
`f^* f_* 𝒪_X(D) → 𝒪_X(D)` of the adjunction `f^* ⊣ f_*` is surjective. This is the
Weil-divisor analogue of `MMP.Mori.IsRelativelyFreeCartier`. -/
def IsRelativelyFreeDivisor {Z : Scheme.{u}} (f : X ⟶ Z) (D : Divisor X) : Prop :=
  Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app D.divisorialSheaf)

end CommonModel

section RelativeGerms

variable {X Z : Scheme.{u}} (f : X ⟶ Z) (F : X.Modules) (x : X)

omit F x in
/-- If the counit `f^* f_* F ⟶ F` is an epimorphism, morphisms out of `F` are detected after
push-forward. -/
theorem eq_of_epi_counit_of_pushforward_map_eq {F Q : X.Modules}
    (hε : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) {g h : F ⟶ Q}
    (hgh : (Scheme.Modules.pushforward f).map g = (Scheme.Modules.pushforward f).map h) :
    g = h := by
  have h1 := (Scheme.Modules.pullbackPushforwardAdjunction f).counit_naturality g
  have h2 := (Scheme.Modules.pullbackPushforwardAdjunction f).counit_naturality h
  rw [← cancel_epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F), ← h1, ← h2,
    hgh]

/-- The germs at `x` of the sections of `F` over the preimages `f⁻¹U` of opens `U ∋ f x`. -/
def relativeGerms : Set (Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F) :=
  {m | ∃ (U : Z.Opens) (hU : x ∈ f ⁻¹ᵁ U) (s : F.val.obj (op (f ⁻¹ᵁ U))),
    Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x F (f ⁻¹ᵁ U) hU s = m}

/-- **Relative freeness generates every stalk by relative sections.** If the counit
`f^* f_* F ⟶ F` is an epimorphism, the germs at `x` of sections of `F` over the opens `f⁻¹U`,
`f x ∈ U`, span the stalk `F_x`: the quotient map of `F_x` by their span gives a map from `F` to
the module skyscraper at `x` which vanishes after push-forward, hence vanishes. -/
theorem span_relativeGerms_eq_top
    (hε : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) :
    Submodule.span (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x) (relativeGerms f F x) = ⊤ := by
  set N := Submodule.span (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x) (relativeGerms f F x)
  let ψ : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F ⟶
      ModuleCat.of _ (Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F ⧸ N) :=
    ModuleCat.ofHom N.mkQ
  let g := Stacks.ModuleSkyscraper.ofStalkHom X.ringCatSheaf x F ψ
  let g₀ := Stacks.ModuleSkyscraper.ofStalkHom X.ringCatSheaf x F
    (0 : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F ⟶
      ModuleCat.of _ (Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F ⧸ N))
  have hg : g = g₀ := by
    refine eq_of_epi_counit_of_pushforward_map_eq (Q := (Stacks.ModuleSkyscraper.sheafObj
      X.ringCatSheaf x (ModuleCat.of _ (Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x F ⧸ N)) :
      X.Modules)) f hε ?_
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext s
    funext h
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨U, h.down, s, rfl⟩)
  rw [eq_top_iff]
  intro m _
  obtain ⟨U, h, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    F.val.presheaf m
  have := congrFun (congrArg (fun k : F ⟶ _ => k.val.app (op U) s) hg) ⟨h⟩
  exact (Submodule.Quotient.mk_eq_zero N).mp this

end RelativeGerms

section SectionValue

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) {x : X}
  {Zc : irreducibleComponents X} (hxZc : x ∈ Zc.1)

/-- The value at the generic point of the component `Zc ∋ x` of a section of `𝒪_X(D)` over an
open containing `x`. -/
def sectionValue {W : X.Opens} (hx : x ∈ W) (t : D.divisorialSheaf.val.obj (op W)) :
    X.presheaf.stalk (componentGenericPoint X Zc) :=
  (t : D.divisorialSubmodule W).1 ⟨Zc, (genericPoint_mem_iff Zc W).mpr ⟨x, hx, hxZc⟩⟩

/-- Sections with the same germ at `x` have the same value at the generic point. -/
theorem sectionValue_eq_of_germ_eq {W W' : X.Opens} (hx : x ∈ W) (hx' : x ∈ W')
    (t : D.divisorialSheaf.val.obj (op W)) (t' : D.divisorialSheaf.val.obj (op W'))
    (h : Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf W hx t =
      Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf W' hx' t') :
    sectionValue D hxZc hx t = sectionValue D hxZc hx' t' := by
  obtain ⟨W'', hx'', iU, iV, heq⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
    D.divisorialSheaf.val.presheaf x hx hx' t t' h
  exact congrArg (sectionValue D hxZc hx'') heq

/-- The value is unchanged by restriction. -/
theorem sectionValue_res {W W' : X.Opens} (i : W' ⟶ W) (hx' : x ∈ W')
    (t : D.divisorialSheaf.val.obj (op W)) :
    sectionValue D hxZc hx' (D.divisorialSheaf.val.presheaf.map i.op t) =
      sectionValue D hxZc (i.le hx') t := rfl

/-- The value is additive. -/
theorem sectionValue_add {W : X.Opens} (hx : x ∈ W) (t t' : D.divisorialSheaf.val.obj (op W)) :
    sectionValue D hxZc hx (t + t') = sectionValue D hxZc hx t + sectionValue D hxZc hx t' := rfl

/-- The value of `c • t` is the germ of `c` at the generic point times the value of `t`. -/
theorem sectionValue_smul {W : X.Opens} (hx : x ∈ W) (c : X.ringCatSheaf.obj.obj (op W))
    (t : D.divisorialSheaf.val.obj (op W)) :
    sectionValue D hxZc hx (c • t) =
      X.presheaf.germ W _ ((genericPoint_mem_iff Zc W).mpr ⟨x, hx, hxZc⟩) c *
        sectionValue D hxZc hx t := rfl

/-- Every element of the stalk is a germ. -/
theorem exists_modGerm_eq (m : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x
      D.divisorialSheaf) :
    ∃ (W : X.Opens) (hx : x ∈ W) (t : D.divisorialSheaf.val.obj (op W)),
      Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf W hx t = m :=
  TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) D.divisorialSheaf.val.presheaf m

/-- The value at the generic point of `Zc` of a germ at `x ∈ Zc` of `𝒪_X(D)`. -/
def stalkValue
    (m : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x D.divisorialSheaf) :
    X.presheaf.stalk (componentGenericPoint X Zc) :=
  sectionValue D hxZc (exists_modGerm_eq D m).choose_spec.choose
    (exists_modGerm_eq D m).choose_spec.choose_spec.choose

/-- The value of a germ is the value of any section representing it. -/
theorem stalkValue_modGerm {W : X.Opens} (hx : x ∈ W) (t : D.divisorialSheaf.val.obj (op W)) :
    stalkValue D hxZc (Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf W hx t) =
      sectionValue D hxZc hx t :=
  sectionValue_eq_of_germ_eq D hxZc _ _ _ _
    (exists_modGerm_eq D _).choose_spec.choose_spec.choose_spec

/-- The germ of a restriction. -/
theorem modGerm_res {W W' : X.Opens} (i : W' ⟶ W) (hx' : x ∈ W')
    (t : D.divisorialSheaf.val.obj (op W)) :
    Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf W' hx'
        (D.divisorialSheaf.val.presheaf.map i.op t) =
      Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf W (i.le hx') t :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) D.divisorialSheaf.val.presheaf i x hx' t

/-- The value of germs is additive. -/
theorem stalkValue_add (m m' : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x
      D.divisorialSheaf) :
    stalkValue D hxZc (m + m') = stalkValue D hxZc m + stalkValue D hxZc m' := by
  obtain ⟨W, hx, t, rfl⟩ := exists_modGerm_eq D m
  obtain ⟨W', hx', t', rfl⟩ := exists_modGerm_eq D m'
  have hxx : x ∈ W ⊓ W' := ⟨hx, hx'⟩
  have e1 := modGerm_res D (homOfLE inf_le_left) hxx t
  have e2 := modGerm_res D (homOfLE inf_le_right) hxx t'
  have e3 := (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) D.divisorialSheaf.val.presheaf
    (W ⊓ W') x hxx).hom.map_add (D.divisorialSheaf.val.presheaf.map (homOfLE inf_le_left).op t)
    (D.divisorialSheaf.val.presheaf.map (homOfLE inf_le_right).op t')
  refine (congrArg (stalkValue D hxZc) (congrArg₂ (· + ·) e1 e2)).symm.trans ?_
  refine (congrArg (stalkValue D hxZc) e3.symm).trans ?_
  refine (stalkValue_modGerm D hxZc hxx _).trans ?_
  rw [stalkValue_modGerm, stalkValue_modGerm]
  rfl

/-- The value of `c • m` is the germ of `c` at the generic point times the value of `m`. -/
theorem stalkValue_smul {V : X.Opens} (hxV : x ∈ V) (c : X.ringCatSheaf.obj.obj (op V))
    (m : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x D.divisorialSheaf) :
    stalkValue D hxZc ((TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj V x hxV).hom c
        • m) =
      X.presheaf.germ V _ ((genericPoint_mem_iff Zc V).mpr ⟨x, hxV, hxZc⟩) c *
        stalkValue D hxZc m := by
  obtain ⟨W, hx, t, rfl⟩ := exists_modGerm_eq D m
  have hxx : x ∈ V ⊓ W := ⟨hxV, hx⟩
  have e1 := modGerm_res D (homOfLE inf_le_right) hxx t
  have e2 := TopCat.Presheaf.germ_res_apply (C := RingCat.{u}) X.ringCatSheaf.obj
      (homOfLE inf_le_left) x hxx c
  have e3 := AlgebraicGeometry.SheafOfModules.germ_hom_smul X.ringCatSheaf x
    D.divisorialSheaf.val (V ⊓ W) hxx (X.ringCatSheaf.obj.map (homOfLE inf_le_left).op c)
    (D.divisorialSheaf.val.presheaf.map (homOfLE inf_le_right).op t)
  refine (congrArg (stalkValue D hxZc) (congrArg₂ (· • ·) e2 e1)).symm.trans ?_
  refine (congrArg (stalkValue D hxZc) e3.symm).trans ?_
  refine (stalkValue_modGerm D hxZc hxx _).trans ?_
  rw [stalkValue_modGerm]
  refine (sectionValue_smul D hxZc hxx _ _).trans ?_
  exact congrArg₂ (· * ·) (X.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ c) rfl

end SectionValue

section RelativelyFree

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- **Algebraic Hartogs for a section of `𝒪_X(D)`.** If `φ` is a local equation of `D` on
`U₀ ∋ x` and `s` is a section of `𝒪_X(D)` over `W ∋ x`, then `s · φ` is regular at `x`. -/
theorem exists_stalk_eq_sectionValue_mul {D : Divisor X} {x : X} {Zc : irreducibleComponents X}
    (hxZc : x ∈ Zc.1) {W U₀ : X.Opens} (hxW : x ∈ W) (hxU₀ : x ∈ U₀)
    (s : D.divisorialSheaf.val.obj (op W)) {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U₀ φ) :
    ∃ r : X.presheaf.stalk x, (stalkToRationalFunctions X hxZc).hom r =
      sectionValue D hxZc hxW s * (φ : RationalFunctions X) Zc := by
  let t : ToType ((rationalFunctionsPresheaf X).obj (op (W ⊓ U₀))) :=
    fun Z' => (s : D.divisorialSubmodule _).1 ⟨Z'.1, (inf_le_left : W ⊓ U₀ ≤ _) Z'.2⟩ *
      (φ : RationalFunctions X) Z'.1
  have ht : (0 : Divisor X).IsDivisorialSection (W ⊓ U₀) t := by
    intro P hP
    have h1 := (s : D.divisorialSubmodule _).2 P (hP.mono
      (Set.inter_subset_inter_right _ inf_le_left))
    have h2 : P.OrdGE (D.coeff P) ((φ : RationalFunctions X) P.component) := by
      refine Or.inr ?_
      rw [P.valuation_component, ← hφ P (hP.mono (Set.inter_subset_inter_right _
        inf_le_right))]
    have := h1.mul h2
    rw [neg_add_cancel] at this
    simpa using this
  exact ht.exists_stalk_eq (x := x) ⟨hxW, hxU₀⟩ hxZc

/-- If the values `sᵢ` at the generic point combine to `φ⁻¹` with coefficients `cᵢ`, and
`rᵢ ∈ 𝒪_{X,x}` represents `sᵢ · φ`, then `∑ cᵢ rᵢ = 1` in `𝒪_{X,x}`. -/
theorem sum_germ_mul_eq_one {D : Divisor X} {x : X} {Zc : irreducibleComponents X}
    (hxZc : x ∈ Zc.1) {n : ℕ} {V W : Fin n → X.Opens} (hV : ∀ i, x ∈ V i) (hW : ∀ i, x ∈ W i)
    (c' : ∀ i, X.ringCatSheaf.obj.obj (op (V i))) (s : ∀ i, D.divisorialSheaf.val.obj (op (W i)))
    {φ : (RationalFunctions X)ˣ} {r : Fin n → X.presheaf.stalk x}
    (hr : ∀ i, (stalkToRationalFunctions X hxZc).hom (r i) =
      sectionValue D hxZc (hW i) (s i) * (φ : RationalFunctions X) Zc)
    (hval : ∑ i, X.presheaf.germ (V i) _ ((genericPoint_mem_iff Zc (V i)).mpr
      ⟨x, hV i, hxZc⟩) (c' i) * sectionValue D hxZc (hW i) (s i) =
        ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Zc) :
    ∑ i, X.presheaf.germ (V i) x (hV i) (c' i) * r i = 1 := by
  have hgerm : ∀ i, X.presheaf.germ (V i) _ ((genericPoint_mem_iff Zc (V i)).mpr
      ⟨x, hV i, hxZc⟩) (c' i) = (stalkToRationalFunctions X hxZc).hom
        (X.presheaf.germ (V i) x (hV i) (c' i)) :=
    fun i => (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  have hone : (stalkToRationalFunctions X hxZc).hom
      (∑ i, X.presheaf.germ (V i) x (hV i) (c' i) * r i) = 1 := by
    rw [map_sum]
    simp only [map_mul, hr, ← hgerm]
    have : ∑ i, X.presheaf.germ (V i) _ ((genericPoint_mem_iff Zc (V i)).mpr
        ⟨x, hV i, hxZc⟩) (c' i) * (sectionValue D hxZc (hW i) (s i) *
          (φ : RationalFunctions X) Zc) = (∑ i, X.presheaf.germ (V i) _
            ((genericPoint_mem_iff Zc (V i)).mpr ⟨x, hV i, hxZc⟩) (c' i) *
              sectionValue D hxZc (hW i) (s i)) * (φ : RationalFunctions X) Zc := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    rw [this, hval, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Pi.one_apply]
  exact stalkToRationalFunctions_injective hxZc (by rw [hone, map_one])

/-- **A section with unit local generator.** If `s` is a section of `𝒪_X(D)` over `W ∋ x` and
`s · φ` is represented by a unit of `𝒪_{X,x}`, where `φ` is a local equation of `D` near `x`, then
the unit `ψ` of `K(X)` determined by `s` makes `D + div ψ` effective on `W` with coefficient `0`
along every prime divisor through `x`. -/
theorem exists_coeff_add_ord_eq_zero_of_isUnit [IsIntegral X] {D : Divisor X} {x : X}
    {Zc : irreducibleComponents X} (hxZc : x ∈ Zc.1) {W U₀ : X.Opens} (hxW : x ∈ W)
    (s : D.divisorialSheaf.val.obj (op W)) (hxU₀ : x ∈ U₀) {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U₀ φ) {r : X.presheaf.stalk x} (hri : IsUnit r)
    (hr : (stalkToRationalFunctions X hxZc).hom r =
      sectionValue D hxZc hxW s * (φ : RationalFunctions X) Zc) :
    ∃ ψ : (RationalFunctions X)ˣ,
      (∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ W).Nonempty → 0 ≤ D.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → D.coeff P + P.ord ψ = 0 := by
  have := subsingleton_irreducibleComponents (X := X)
  let sR : RationalFunctions X := fun Z' => (s : D.divisorialSubmodule _).1
    ⟨Z', (genericPoint_mem_iff Z' W).mpr
      ⟨x, hxW, mem_irreducibleComponent_of_irreducibleSpace Z' x⟩⟩
  have hvali : sectionValue D hxZc hxW s = (stalkToRationalFunctions X hxZc).hom r *
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Zc := by
    rw [hr, mul_assoc, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Pi.one_apply, mul_one]
  have hsR : IsUnit sR := by
    refine Pi.isUnit_iff.mpr fun Z' => ?_
    obtain rfl : Zc = Z' := Subsingleton.elim _ _
    change IsUnit (sectionValue D hxZc hxW s)
    rw [hvali]
    exact (hri.map _).mul ((φ⁻¹).isUnit.map (Pi.evalRingHom _ Zc))
  set ψ := hsR.unit
  have hψ : (ψ : RationalFunctions X) = sR := hsR.unit_spec
  have hgen : ∀ (Z' : irreducibleComponents X) (hx' : x ∈ Z'.1),
      (stalkToRationalFunctions X hx').hom r =
        ((ψ * φ : (RationalFunctions X)ˣ) : RationalFunctions X) Z' := by
    intro Z' hx'
    obtain rfl : Zc = Z' := Subsingleton.elim _ _
    rw [Units.val_mul, Pi.mul_apply, hψ]
    exact hr
  refine ⟨ψ, fun P hP => ?_, fun P hxP => ?_⟩
  · have h1 := (s : D.divisorialSubmodule _).2 P hP
    have hne : (ψ : RationalFunctions X) P.component ≠ 0 :=
      (ψ.isUnit.map (Pi.evalRingHom _ P.component)).ne_zero
    rw [hψ] at hne
    have h2 := h1.resolve_left hne
    change WithZero.exp (-D.coeff P) ≤ P.valuation (sR P.component) at h2
    rw [← hψ, P.valuation_component, WithZero.exp_le_exp] at h2
    linarith
  · have hspec : P.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
      exact specializes_iff_mem_closure.mpr hxP
    have hxPc : x ∈ P.component.1 := P.support_subset_component hxP
    have h0 : P.ord (ψ * φ) = 0 :=
      P.ord_eq_zero_of_isUnit (hri.map (X.presheaf.stalkSpecializes hspec).hom)
        (by rw [P.toComponent_stalkSpecializes hspec hxPc, hgen _ hxPc])
    rw [PrimeDivisor.ord_mul] at h0
    rw [hφ P ⟨x, hxP, hxU₀⟩]
    linarith

/-- **A relatively free Cartier divisor has a local generating relative section.** If `D` is
Cartier and relatively free over `Z` (`MMP.Fourfold.IsRelativelyFreeDivisor`), then for every
`x ∈ X` there are an open `U ∋ f x` and `ψ ∈ K(X)^×` with `D + div ψ` effective on `f⁻¹U` and with
coefficient `0` along every prime divisor through `x`. -/
theorem exists_coeff_add_ord_eq_zero_of_isRelativelyFree [IsIntegral X] (f : X ⟶ Z)
    {D : Divisor X} (hD : D.IsCartier) (hfree : IsRelativelyFreeDivisor f D) (x : X) :
    ∃ (U : Z.Opens) (_ : f x ∈ U) (ψ : (RationalFunctions X)ˣ),
      (∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty →
        0 ≤ D.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → D.coeff P + P.ord ψ = 0 := by
  classical
  obtain ⟨Zc, hxZc⟩ : ∃ Z' : irreducibleComponents X, x ∈ Z'.1 :=
    ⟨pointComponent x, mem_pointComponent x⟩
  obtain ⟨U₀, hxU₀, φ, hφ⟩ := hD x
  let e : D.divisorialSheaf.val.obj (op U₀) :=
    ⟨fun Z' => ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z'.1, fun P hP => by
      refine Or.inr ?_
      change WithZero.exp (-D.coeff P) ≤
        P.valuation (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) P.component)
      rw [P.valuation_component, PrimeDivisor.ord_inv, hφ P hP]⟩
  have hspan := span_relativeGerms_eq_top f D.divisorialSheaf x hfree
  have hmem : Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf U₀ hxU₀ e ∈
      Submodule.span (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x)
        (relativeGerms f D.divisorialSheaf x) := hspan ▸ Submodule.mem_top
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  choose U hU s hs using fun i => (g i).2
  choose V hV c' hc' using fun i =>
    TopCat.Presheaf.exists_germ_eq (C := RingCat.{u}) X.ringCatSheaf.obj (c i)
  let ev : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x D.divisorialSheaf →+
      X.presheaf.stalk (componentGenericPoint X Zc) :=
    AddMonoidHom.mk' (stalkValue D hxZc) (stalkValue_add D hxZc)
  have hval := congrArg ev hsum
  rw [map_sum] at hval
  have hterm : ∀ i, ev (c i • ↑(g i)) =
      X.presheaf.germ (V i) _ ((genericPoint_mem_iff Zc (V i)).mpr ⟨x, hV i, hxZc⟩) (c' i) *
        sectionValue D hxZc (hU i) (s i) := by
    intro i
    have h1 : c i • (↑(g i) : Stacks.ModuleSkyscraper.stalkMod X.ringCatSheaf x
        D.divisorialSheaf) =
        (TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj (V i) x (hV i)).hom (c' i) •
          Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf _ (hU i) (s i) :=
      congrArg₂ (· • ·) (hc' i).symm (hs i).symm
    refine (congrArg ev h1).trans ?_
    refine (stalkValue_smul D hxZc (hV i) (c' i) _).trans ?_
    rw [stalkValue_modGerm]
  have he : ev (Stacks.ModuleSkyscraper.modGerm X.ringCatSheaf x D.divisorialSheaf U₀ hxU₀ e) =
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Zc :=
    stalkValue_modGerm D hxZc hxU₀ e
  rw [he] at hval
  simp only [hterm] at hval
  choose r hr using fun i => exists_stalk_eq_sectionValue_mul hxZc (hU i) hxU₀ (s i) hφ
  have hone := sum_germ_mul_eq_one hxZc hV hU c' s hr hval
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hone ▸ isUnit_one :
    IsUnit (∑ i ∈ Finset.univ, X.presheaf.germ (V i) x (hV i) (c' i) * r i))
  obtain ⟨ψ, h₁, h₂⟩ := exists_coeff_add_ord_eq_zero_of_isUnit hxZc (hU i) (s i) hxU₀ hφ
    (isUnit_of_mul_isUnit_right hi) (hr i)
  exact ⟨U i, hU i, ψ, h₁, h₂⟩

end RelativelyFree

section RationalFunctionPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A birational morphism of integral schemes induces a surjection on function fields. -/
theorem surjective_stalkMap_of_isBirationalMorphism [IsIntegral X] [IsIntegral Y] {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) (x : X) (hx : x = genericPoint X) :
    Function.Surjective (f.stalkMap x).hom := by
  subst hx
  have := hf.isDominant
  have hb := hf.functionFieldMap_bijective
  intro b
  obtain ⟨a, ha⟩ := hb.2 b
  exact ⟨_, ha⟩

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Every unit of `K(X)` is the pull-back of a unit of `K(Y)` along a birational morphism
`X ⟶ Y` of integral schemes. -/
theorem exists_pullbackRationalFunction_eq [IsIntegral X] [IsIntegral Y] [CompactSpace Y]
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) (χ : (RationalFunctions X)ˣ) :
    ∃ (ψ : (RationalFunctions Y)ˣ) (hψ : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (principalDivisor ψ).supp),
      pullbackRationalFunction f ψ hψ = χ := by
  classical
  have := hf.isDominant
  have := subsingleton_irreducibleComponents (X := X)
  have := subsingleton_irreducibleComponents (X := Y)
  set Zx : irreducibleComponents X := pointComponent (genericPoint X)
  obtain ⟨a, ha⟩ := surjective_stalkMap_of_isBirationalMorphism hf (componentGenericPoint X Zx)
    (componentGenericPoint_eq_genericPoint Zx) ((χ : RationalFunctions X) Zx)
  set W := pointComponent (f (componentGenericPoint X Zx))
  have hW : f (componentGenericPoint X Zx) ∈ W.1 := mem_pointComponent _
  let sY : RationalFunctions Y := Function.update 1 W ((stalkToRationalFunctions Y hW).hom a)
  have hsYW : sY W = (stalkToRationalFunctions Y hW).hom a := Function.update_self _ _ _
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact ((χ.isUnit.map (Pi.evalRingHom _ Zx)).ne_zero) ha.symm
  have hsY : IsUnit sY := by
    refine Pi.isUnit_iff.mpr fun W' => ?_
    obtain rfl : W = W' := Subsingleton.elim _ _
    rw [hsYW]
    refine isUnit_of_ne_zero_stalk W fun h0 => ha0 ?_
    exact stalkToRationalFunctions_injective hW (h0.trans (map_zero _).symm)
  set ψ := hsY.unit
  have hψ : (ψ : RationalFunctions Y) = sY := hsY.unit_spec
  refine ⟨ψ, map_componentGenericPoint_notMem_supp_of_isDominant f _, ?_⟩
  ext Z
  obtain rfl : Zx = Z := Subsingleton.elim _ _
  obtain ⟨a', ha'⟩ := (Divisor.isLocalEquation_principalDivisor ψ ⊤).exists_unit_stalk trivial
    (map_componentGenericPoint_notMem_supp_of_isDominant f _ Zx) hW
  have haa : (a' : Y.presheaf.stalk _) = a :=
    stalkToRationalFunctions_injective hW (by rw [ha', hψ, hsYW])
  have hval : ((pullbackRationalFunction f ψ
      (map_componentGenericPoint_notMem_supp_of_isDominant f _) : RationalFunctions X) Zx) =
      (pullbackComponent f (map_componentGenericPoint_notMem_supp_of_isDominant f _)
        (Divisor.isLocalEquation_principalDivisor ψ ⊤) Zx trivial).val := rfl
  rw [hval]
  refine (congrArg Units.val (pullbackComponent_eq _ _ _ hW a' ha')).trans ?_
  change (f.stalkMap (componentGenericPoint X Zx)).hom
    (a' : Y.presheaf.stalk (f (componentGenericPoint X Zx))) = _
  rw [haa, ha]

end RationalFunctionPullback

/-! ### Sections of divisorial sheaves as units of the function field -/

section SectionsAsUnits

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsIntegral X] in
/-- The order of vanishing along `G` of a section of `𝒪_X(D)` whose component along `G` is the
unit `χ` is the coefficient of `G` in `D + div χ`. -/
theorem sectionVanishingOrder_eq_toNat {D : Divisor X} {G : MMP.Mori.PrimeDivisor X}
    {V : X.Opens} (h : (G.support ∩ (V : Set X)).Nonempty) (σ : D.divisorialSubmodule V)
    (χ : (RationalFunctions X)ˣ)
    (hχ : σ.1 ⟨G.component, G.componentGenericPoint_mem_of_nonempty h⟩ =
      (χ : RationalFunctions X) G.component) :
    sectionVanishingOrder D G h σ = ((D.coeff G + G.ord χ).toNat : ℕ∞) := by
  have hne : (χ : RationalFunctions X) G.component ≠ 0 :=
    (χ.isUnit.map (Pi.evalRingHom _ G.component)).ne_zero
  have hc : 0 ≤ D.coeff G + G.ord χ := by
    have h1 := σ.2 G h
    change G.OrdGE (-D.coeff G) (σ.1 ⟨G.component, G.componentGenericPoint_mem_of_nonempty h⟩)
      at h1
    rw [hχ] at h1
    have h2 := h1.resolve_left hne
    rw [G.valuation_component, WithZero.exp_le_exp] at h2
    linarith
  unfold sectionVanishingOrder
  rw [hχ]
  apply le_antisymm
  · refine iSup₂_le fun n hn => ?_
    have h2 := hn.resolve_left hne
    rw [G.valuation_component, WithZero.exp_le_exp] at h2
    exact_mod_cast (show n ≤ (D.coeff G + G.ord χ).toNat by omega)
  · refine le_iSup₂_of_le (D.coeff G + G.ord χ).toNat (Or.inr ?_) le_rfl
    rw [G.valuation_component, WithZero.exp_le_exp]
    omega

/-- A nonzero section of `𝒪_X(D)` over a nonempty open `V` of an integral scheme is a unit `χ` of
`K(X)` with `D + div χ` effective on `V`. -/
theorem exists_unit_of_divisorialSubmodule_ne_zero {D : Divisor X} {V : X.Opens}
    (hV : (V : Set X).Nonempty) (σ : D.divisorialSubmodule V) (hσ : σ ≠ 0) :
    ∃ χ : (RationalFunctions X)ˣ,
      (∀ (Z' : irreducibleComponents X) (hZ' : componentGenericPoint X Z' ∈ V),
        σ.1 ⟨Z', hZ'⟩ = (χ : RationalFunctions X) Z') ∧
      ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ V).Nonempty → 0 ≤ D.coeff P + P.ord χ := by
  obtain ⟨v, hv⟩ := hV
  have hmemV : ∀ Z' : irreducibleComponents X, componentGenericPoint X Z' ∈ V := fun Z' =>
    (genericPoint_mem_iff Z' V).mpr ⟨v, hv, mem_irreducibleComponent_of_irreducibleSpace Z' v⟩
  have := subsingleton_irreducibleComponents (X := X)
  let sR : RationalFunctions X := fun Z' => σ.1 ⟨Z', hmemV Z'⟩
  have hne : ∀ Z', sR Z' ≠ 0 := by
    intro Z' h0
    apply hσ
    refine Subtype.ext (funext fun Z'' => ?_)
    obtain ⟨Z'', hZ''⟩ := Z''
    obtain rfl : Z' = Z'' := Subsingleton.elim _ _
    exact h0
  have hsR : IsUnit sR := Pi.isUnit_iff.mpr fun Z' => isUnit_of_ne_zero_stalk Z' (hne Z')
  refine ⟨hsR.unit, fun Z' hZ' => by rw [hsR.unit_spec], fun P hP => ?_⟩
  have h2 := (σ.2 P hP).resolve_left (hne P.component)
  change WithZero.exp (-D.coeff P) ≤ P.valuation (sR P.component) at h2
  rw [← hsR.unit_spec, P.valuation_component, WithZero.exp_le_exp] at h2
  linarith

omit [IsIntegral X] in
/-- A unit `χ` of `K(X)` with `D + div χ` effective on `V` is a section of `𝒪_X(D)` over `V`. -/
theorem isDivisorialSection_of_unit {D : Divisor X} {V : X.Opens} (χ : (RationalFunctions X)ˣ)
    (h : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ V).Nonempty → 0 ≤ D.coeff P + P.ord χ) :
    D.IsDivisorialSection V fun Z => (χ : RationalFunctions X) Z.1 := fun P hP => by
  refine Or.inr ?_
  change WithZero.exp (-D.coeff P) ≤ P.valuation ((χ : RationalFunctions X) P.component)
  rw [P.valuation_component, WithZero.exp_le_exp]
  linarith [h P hP]

end SectionsAsUnits

section CommonModel'

variable {k : Type u} [Field k] {X Y T Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace Y] [CompactSpace T]

/-- On the common model, `D + div φ` is effective over `fX⁻¹U` exactly when `D' + div ψ` is
effective over `fY⁻¹U`, for units `φ, ψ` with the same pull-back to `T`. -/
theorem forall_coeff_nonneg_iff_of_pullbackRationalFunction_eq
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    {p : T ⟶ X} {q : T ⟶ Y} {fX : X ⟶ Z} {fY : Y ⟶ Z}
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hZc : p ≫ fX = q ≫ fY)
    {D : Divisor X} {D' : Divisor Y} (hD : D.IsCartier) (hD' : D'.IsCartier) {E : Divisor T}
    (hE : 0 ≤ E) (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0)
    {hB : ∀ W : irreducibleComponents T, p (componentGenericPoint T W) ∉ D.supp}
    {hB' : ∀ W : irreducibleComponents T, q (componentGenericPoint T W) ∉ D'.supp}
    (hpb : D.pullback hD hB = D'.pullback hD' hB' + E) (U : Z.Opens)
    {φ : (RationalFunctions X)ˣ} {ψ : (RationalFunctions Y)ˣ}
    {hφ : ∀ W : irreducibleComponents T,
      p (componentGenericPoint T W) ∉ (principalDivisor φ).supp}
    {hψ : ∀ W : irreducibleComponents T,
      q (componentGenericPoint T W) ∉ (principalDivisor ψ).supp}
    (heq : pullbackRationalFunction p φ hφ = pullbackRationalFunction q ψ hψ) :
    (∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ fX ⁻¹ᵁ U).Nonempty →
        0 ≤ (D + principalDivisor φ).coeff P) ↔
      ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ fY ⁻¹ᵁ U).Nonempty →
        0 ≤ (D' + principalDivisor ψ).coeff P := by
  have := hp.isDominant
  have := hq.isDominant
  have hpt : ∀ t : T, fX (p t) = fY (q t) := fun t => by
    rw [← Scheme.Hom.comp_apply, hZc, Scheme.Hom.comp_apply]
  have hpA : (D + principalDivisor φ).IsPullback p
      (map_componentGenericPoint_notMem_supp_of_isDominant p _)
      (D.pullback hD hB + principalDivisor (pullbackRationalFunction p φ hφ)) :=
    Divisor.IsPullback.add hD (Divisor.isCartier_principalDivisor φ) _
      (Divisor.isPullback_pullback hD hB) (Divisor.isPullback_principalDivisor φ hφ)
  have hqA : (D' + principalDivisor ψ).IsPullback q
      (map_componentGenericPoint_notMem_supp_of_isDominant q _)
      (D'.pullback hD' hB' + principalDivisor (pullbackRationalFunction q ψ hψ)) :=
    Divisor.IsPullback.add hD' (Divisor.isCartier_principalDivisor ψ) _
      (Divisor.isPullback_pullback hD' hB') (Divisor.isPullback_principalDivisor ψ hψ)
  have hrel : D.pullback hD hB + principalDivisor (pullbackRationalFunction p φ hφ) =
      D'.pullback hD' hB' + principalDivisor (pullbackRationalFunction q ψ hψ) + E := by
    rw [hpb, heq]
    abel
  constructor
  · intro hA P hP
    obtain ⟨P', hP'gen, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY
        (hqY ▸ hT) hq P
    have hc := MMP.Positivity.coeff_eq_of_isPullback P' P hP'gen
      (hD'.add (Divisor.isCartier_principalDivisor ψ)) hqA
    have hE0 : E.coeff P' = 0 := (hqE ▸ htr E).symm
    have hmeet : (P'.support ∩ p ⁻¹ᵁ (fX ⁻¹ᵁ U)).Nonempty := by
      refine (P'.genericPoint_mem_iff _).mp ?_
      change fX (p P'.genericPoint) ∈ U
      rw [hpt, hP'gen]
      exact (P.genericPoint_mem_iff (fY ⁻¹ᵁ U)).mpr hP
    have h1 := coeff_nonneg_of_isPullback_of_isEffectiveOn
      (hD.add (Divisor.isCartier_principalDivisor φ)) hA hpA P' hmeet
    rwa [hrel, DivisorWithCoeffs.coeff_add, hE0, add_zero, hc] at h1
  · intro hA' P hP
    obtain ⟨P', hP'gen, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX
        (hpX ▸ hT) hp P
    have hc := MMP.Positivity.coeff_eq_of_isPullback P' P hP'gen
      (hD.add (Divisor.isCartier_principalDivisor φ)) hpA
    have hmeet : (P'.support ∩ q ⁻¹ᵁ (fY ⁻¹ᵁ U)).Nonempty := by
      refine (P'.genericPoint_mem_iff _).mp ?_
      change fY (q P'.genericPoint) ∈ U
      rw [← hpt, hP'gen]
      exact (P.genericPoint_mem_iff (fX ⁻¹ᵁ U)).mpr hP
    have h1 := coeff_nonneg_of_isPullback_of_isEffectiveOn
      (hD'.add (Divisor.isCartier_principalDivisor ψ)) hA' hqA P' hmeet
    rw [← hc, hrel, DivisorWithCoeffs.coeff_add]
    exact add_nonneg h1 (hE P')

omit [IsIntegral Y] in
/-- On the common model, the coefficient of `G` in `D + div χ` is that of a prime divisor `G'` of
`T` over `G` in `q^*D' + div (q^*ψ) + E`, for units `χ, ψ` with the same pull-back to `T`. -/
theorem coeff_add_principalDivisor_eq_of_pullback_eq_add {p : T ⟶ X} {q : T ⟶ Y} [IsDominant p]
    {D : Divisor X} {D' : Divisor Y} (hD : D.IsCartier) (hD' : D'.IsCartier) {E : Divisor T}
    {hB : ∀ W : irreducibleComponents T, p (componentGenericPoint T W) ∉ D.supp}
    {hB' : ∀ W : irreducibleComponents T, q (componentGenericPoint T W) ∉ D'.supp}
    (hpb : D.pullback hD hB = D'.pullback hD' hB' + E) {G : MMP.Mori.PrimeDivisor X}
    {G' : MMP.Mori.PrimeDivisor T} (hG'gen : p G'.genericPoint = G.genericPoint)
    [IsIso (p.stalkMap G'.genericPoint)] {χ : (RationalFunctions X)ˣ}
    {ψ : (RationalFunctions Y)ˣ}
    {hχ : ∀ W : irreducibleComponents T,
      p (componentGenericPoint T W) ∉ (principalDivisor χ).supp}
    {hψ : ∀ W : irreducibleComponents T,
      q (componentGenericPoint T W) ∉ (principalDivisor ψ).supp}
    (heq : pullbackRationalFunction p χ hχ = pullbackRationalFunction q ψ hψ) :
    (D + principalDivisor χ).coeff G =
      (D'.pullback hD' hB' + principalDivisor (pullbackRationalFunction q ψ hψ)).coeff G' +
        E.coeff G' := by
  rw [← MMP.Positivity.coeff_eq_of_isPullback G' G hG'gen
    (hD.add (Divisor.isCartier_principalDivisor χ))
    (Divisor.IsPullback.add hD (Divisor.isCartier_principalDivisor χ)
      (map_componentGenericPoint_notMem_supp_of_isDominant p _)
      (Divisor.isPullback_pullback hD hB) (Divisor.isPullback_principalDivisor χ hχ)),
    hpb, heq]
  simp only [DivisorWithCoeffs.coeff_add]
  abel

/-- If `D'` is relatively free over `Z`, the relative fixed multiplicity of `D` along `G` is at
most the coefficient of `E` along a prime divisor `G'` of `T` over `G`. -/
theorem relativeFixedMultiplicity_le_of_pullback_eq_add
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    {p : T ⟶ X} {q : T ⟶ Y} {fX : X ⟶ Z} {fY : Y ⟶ Z}
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hZc : p ≫ fX = q ≫ fY)
    {D : Divisor X} {D' : Divisor Y} (hD : D.IsCartier) (hD' : D'.IsCartier) {E : Divisor T}
    (hE : 0 ≤ E) (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0)
    {hB : ∀ W : irreducibleComponents T, p (componentGenericPoint T W) ∉ D.supp}
    {hB' : ∀ W : irreducibleComponents T, q (componentGenericPoint T W) ∉ D'.supp}
    (hpb : D.pullback hD hB = D'.pullback hD' hB' + E) (hfree : IsRelativelyFreeDivisor fY D')
    {G : MMP.Mori.PrimeDivisor X} {G' : MMP.Mori.PrimeDivisor T}
    (hG'gen : p G'.genericPoint = G.genericPoint) [IsIso (p.stalkMap G'.genericPoint)] :
    relativeFixedMultiplicity fX D G ≤ (E.coeff G').toNat := by
  have := hp.isDominant
  have := hq.isDominant
  obtain ⟨U, hU, ψ, hψeff, hψ0⟩ :=
    exists_coeff_add_ord_eq_zero_of_isRelativelyFree fY hD' hfree (q G'.genericPoint)
  have hUG : fX G.genericPoint ∈ U := by
    rw [← hG'gen, ← Scheme.Hom.comp_apply, hZc, Scheme.Hom.comp_apply]
    exact hU
  obtain ⟨φ, hφ, hφψ⟩ := exists_pullbackRationalFunction_eq hp
    (pullbackRationalFunction q ψ (map_componentGenericPoint_notMem_supp_of_isDominant q _))
  have hAeff := (forall_coeff_nonneg_iff_of_pullbackRationalFunction_eq hX hY hT hp hq hpX hqY
    hZc hD hD' hE hqE hpb U hφψ).mpr fun P hP => by
      rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
      exact hψeff P hP
  have hAeff' : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ fX ⁻¹ᵁ U).Nonempty →
      0 ≤ D.coeff P + P.ord φ := fun P hP => by
    simpa only [DivisorWithCoeffs.coeff_add, coeff_principalDivisor] using hAeff P hP
  have hG'0 : (D'.pullback hD' hB' + principalDivisor (pullbackRationalFunction q ψ
      (map_componentGenericPoint_notMem_supp_of_isDominant q _))).coeff G' = 0 := by
    by_contra hne
    have hmem : G'.genericPoint ∈ (D'.pullback hD' hB' + principalDivisor
        (pullbackRationalFunction q ψ
          (map_componentGenericPoint_notMem_supp_of_isDominant q _))).supp :=
      DivisorWithCoeffs.mem_supp_iff.mpr ⟨G', hne, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl⟩
    have hy := MMP.Flips.supp_subset_preimage_supp_of_isPullback
      (hD'.add (Divisor.isCartier_principalDivisor ψ))
      (Divisor.IsPullback.add hD' (Divisor.isCartier_principalDivisor ψ)
        (map_componentGenericPoint_notMem_supp_of_isDominant q _)
        (Divisor.isPullback_pullback hD' hB') (Divisor.isPullback_principalDivisor ψ
          (map_componentGenericPoint_notMem_supp_of_isDominant q _))) hmem
    obtain ⟨P, hP0, hyP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    apply hP0
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    exact hψ0 P hyP
  have hcG := coeff_add_principalDivisor_eq_of_pullback_eq_add hD hD' hpb hG'gen hφψ
  rw [hG'0, zero_add, DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at hcG
  have hGmeet : (G.support ∩ (fX ⁻¹ᵁ U : Set X)).Nonempty :=
    support_inter_preimage_nonempty fX hUG
  let σ : D.divisorialSubmodule (fX ⁻¹ᵁ U) :=
    ⟨fun Z' => (φ : RationalFunctions X) Z'.1, isDivisorialSection_of_unit φ hAeff'⟩
  have hσ : σ ≠ 0 := by
    intro h0
    have := congrArg (fun τ : D.divisorialSubmodule (fX ⁻¹ᵁ U) =>
      τ.1 ⟨G.component, G.componentGenericPoint_mem_of_nonempty hGmeet⟩) h0
    exact (φ.isUnit.map (Pi.evalRingHom _ G.component)).ne_zero this
  refine iInf_le_of_le U (iInf_le_of_le hUG (iInf_le_of_le σ (iInf_le_of_le hσ ?_)))
  rw [sectionVanishingOrder_eq_toNat hGmeet σ φ rfl, hcG]

/-- The relative fixed multiplicity of `D` along `G` is at least the coefficient of `E` along a
prime divisor `G'` of `T` over `G`. -/
theorem le_relativeFixedMultiplicity_of_pullback_eq_add
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    {p : T ⟶ X} {q : T ⟶ Y} {fX : X ⟶ Z} {fY : Y ⟶ Z}
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hZc : p ≫ fX = q ≫ fY)
    {D : Divisor X} {D' : Divisor Y} (hD : D.IsCartier) (hD' : D'.IsCartier) {E : Divisor T}
    (hE : 0 ≤ E) (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0)
    {hB : ∀ W : irreducibleComponents T, p (componentGenericPoint T W) ∉ D.supp}
    {hB' : ∀ W : irreducibleComponents T, q (componentGenericPoint T W) ∉ D'.supp}
    (hpb : D.pullback hD hB = D'.pullback hD' hB' + E)
    {G : MMP.Mori.PrimeDivisor X} {G' : MMP.Mori.PrimeDivisor T}
    (hG'gen : p G'.genericPoint = G.genericPoint) [IsIso (p.stalkMap G'.genericPoint)] :
    ((E.coeff G').toNat : ℕ∞) ≤ relativeFixedMultiplicity fX D G := by
  have := hp.isDominant
  have := hq.isDominant
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun σ => le_iInf fun hσ => ?_
  have hGmeet : (G.support ∩ (fX ⁻¹ᵁ U : Set X)).Nonempty :=
    support_inter_preimage_nonempty fX hU
  obtain ⟨χ, hχval, hχeff⟩ := exists_unit_of_divisorialSubmodule_ne_zero
    (hGmeet.mono Set.inter_subset_right) σ hσ
  obtain ⟨ψ, hψ, hχψ⟩ := exists_pullbackRationalFunction_eq hq
    (pullbackRationalFunction p χ (map_componentGenericPoint_notMem_supp_of_isDominant p _))
  have hA'eff := (forall_coeff_nonneg_iff_of_pullbackRationalFunction_eq hX hY hT hp hq hpX hqY
    hZc hD hD' hE hqE hpb U hχψ.symm).mp fun P hP => by
      rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
      exact hχeff P hP
  have hmeetG : (G'.support ∩ q ⁻¹ᵁ (fY ⁻¹ᵁ U)).Nonempty := by
    refine (G'.genericPoint_mem_iff _).mp ?_
    change fY (q G'.genericPoint) ∈ U
    rw [← Scheme.Hom.comp_apply, ← hZc, Scheme.Hom.comp_apply, hG'gen]
    exact hU
  have h1 := coeff_nonneg_of_isPullback_of_isEffectiveOn
    (hD'.add (Divisor.isCartier_principalDivisor ψ)) hA'eff
    (Divisor.IsPullback.add hD' (Divisor.isCartier_principalDivisor ψ)
      (map_componentGenericPoint_notMem_supp_of_isDominant q _)
      (Divisor.isPullback_pullback hD' hB') (Divisor.isPullback_principalDivisor ψ hψ)) G' hmeetG
  have hcG := coeff_add_principalDivisor_eq_of_pullback_eq_add hD hD' hpb hG'gen hχψ.symm
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at hcG
  rw [sectionVanishingOrder_eq_toNat hGmeet σ χ (hχval _ _), hcG]
  exact_mod_cast Int.toNat_le_toNat (le_add_of_nonneg_left h1)

/-- **Sections and fixed parts on a common birational model.** Let `p : T ⟶ X` and `q : T ⟶ Y`
be proper birational morphisms of normal varieties over a variety `Z` (structure morphisms
`fX`, `fY`, with `p ≫ fX = q ≫ fY`), `D, D'` integral Cartier divisors on `X, Y` with
`p^*D = q^*D' + E`, `E` effective with `q_*E = 0`.

* The sheaves of relative sections of `D` and `D'` are identified by the common function field:
  a nonzero section of `𝒪_X(D)` over `fX⁻¹U` is a unit `φ` of `K(X)` with `D + div φ ≥ 0` on
  `fX⁻¹U`, similarly on `Y`, and for units `φ, ψ` with the same pull-back to `T` this holds for
  `φ` exactly when it holds for `ψ`; every `φ` has such a `ψ` and conversely.
* If `D'` is relatively free over `Z`, the relative fixed multiplicity of `D` along every prime
  divisor `G` of `X` is the coefficient of `G` in `p_*E`. -/
@[mmp "lem_fourfold_common_model_fixed_parts"]
theorem sections_and_fixed_part_of_pullback_eq_add
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    (hZ : Mori.IsVariety k sZ)
    (p : T ⟶ X) (q : T ⟶ Y) (fX : X ⟶ Z) (fY : Y ⟶ Z)
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hfX : fX ≫ sZ = sX) (hfY : fY ≫ sZ = sY)
    (hZc : p ≫ fX = q ≫ fY)
    {D : Divisor X} {D' : Divisor Y} (hD : D.IsCartier) (hD' : D'.IsCartier) {E : Divisor T}
    (hE : 0 ≤ E) (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0)
    (hpull : ∃ (hB : ∀ W : irreducibleComponents T, p (componentGenericPoint T W) ∉ D.supp)
      (hB' : ∀ W : irreducibleComponents T, q (componentGenericPoint T W) ∉ D'.supp),
      D.pullback hD hB = D'.pullback hD' hB' + E) :
    ((∀ (U : Z.Opens) (φ : (RationalFunctions X)ˣ) (ψ : (RationalFunctions Y)ˣ)
        (hφ : ∀ W : irreducibleComponents T,
          p (componentGenericPoint T W) ∉ (MMP.Mori.principalDivisor φ).supp)
        (hψ : ∀ W : irreducibleComponents T,
          q (componentGenericPoint T W) ∉ (MMP.Mori.principalDivisor ψ).supp),
        pullbackRationalFunction p φ hφ = pullbackRationalFunction q ψ hψ →
          (IsEffectiveOn (Divisor.toRDivisor (D + MMP.Mori.principalDivisor φ)) (fX ⁻¹ᵁ U) ↔
            IsEffectiveOn (Divisor.toRDivisor (D' + MMP.Mori.principalDivisor ψ)) (fY ⁻¹ᵁ U))) ∧
      (∀ φ : (RationalFunctions X)ˣ, ∃ (ψ : (RationalFunctions Y)ˣ)
        (hφ : ∀ W : irreducibleComponents T,
          p (componentGenericPoint T W) ∉ (MMP.Mori.principalDivisor φ).supp)
        (hψ : ∀ W : irreducibleComponents T,
          q (componentGenericPoint T W) ∉ (MMP.Mori.principalDivisor ψ).supp),
        pullbackRationalFunction p φ hφ = pullbackRationalFunction q ψ hψ) ∧
      (∀ ψ : (RationalFunctions Y)ˣ, ∃ (φ : (RationalFunctions X)ˣ)
        (hφ : ∀ W : irreducibleComponents T,
          p (componentGenericPoint T W) ∉ (MMP.Mori.principalDivisor φ).supp)
        (hψ : ∀ W : irreducibleComponents T,
          q (componentGenericPoint T W) ∉ (MMP.Mori.principalDivisor ψ).supp),
        pullbackRationalFunction p φ hφ = pullbackRationalFunction q ψ hψ)) ∧
    (IsRelativelyFreeDivisor fY D' →
      ∀ G : MMP.Mori.PrimeDivisor X, ∃ n : ℕ,
        (RationalMap.transformDivisor (X := T) p.toRationalMap E).coeff G = n ∧
          relativeFixedMultiplicity fX D G = n) := by
  obtain ⟨hB, hB', hpb⟩ := hpull
  have := hp.isDominant
  have := hq.isDominant
  refine ⟨⟨fun U φ ψ hφ hψ heq => ?_, fun φ => ?_, fun ψ => ?_⟩, fun hfree G => ?_⟩
  · simpa only [IsEffectiveOn, Divisor.coeff_toRDivisor, Int.cast_nonneg_iff] using
      forall_coeff_nonneg_iff_of_pullbackRationalFunction_eq hX hY hT hp hq hpX hqY hZc hD hD'
        hE hqE hpb U heq
  · obtain ⟨ψ, hψ, h⟩ := exists_pullbackRationalFunction_eq hq
      (pullbackRationalFunction p φ (map_componentGenericPoint_notMem_supp_of_isDominant p _))
    exact ⟨ψ, _, hψ, h.symm⟩
  · obtain ⟨φ, hφ, h⟩ := exists_pullbackRationalFunction_eq hp
      (pullbackRationalFunction q ψ (map_componentGenericPoint_notMem_supp_of_isDominant q _))
    exact ⟨φ, hφ, _, h⟩
  obtain ⟨G', hG'gen, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX (hpX ▸ hT) hp G
  have htrG : (RationalMap.transformDivisor (X := T) p.toRationalMap E).coeff G = E.coeff G' :=
    htr E
  exact ⟨(E.coeff G').toNat, htrG.trans (Int.toNat_of_nonneg (hE G')).symm, le_antisymm
    (relativeFixedMultiplicity_le_of_pullback_eq_add hX hY hT hp hq hpX hqY hZc hD hD' hE hqE
      hpb hfree hG'gen)
    (le_relativeFixedMultiplicity_of_pullback_eq_add hX hY hT hp hq hpX hqY hZc hD hD' hE hqE
      hpb hG'gen)⟩

end CommonModel'

end MMP.Fourfold
