module

public import MMP.Attr
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Root fields of a rational function field (Kollár, proof of Theorem 1.33)

Let `k` be a field of characteristic `p > 0`, `K = k(x₁, …, xₙ)` a rational function field and
`K̄` an algebraic closure. For `m ≥ 0` and a finite extension `k' ⊆ K̄` of `k`, the subring
`k'[x₁^{p^{-m}}, …, xₙ^{p^{-m}}]` of `K̄` is a finitely generated `k[x₁, …, xₙ]`-module, and
every finite purely inseparable extension of `K` inside `K̄` lies in some
`k'(x₁^{p^{-m}}, …, xₙ^{p^{-m}})` with `k'/k` finite purely inseparable.

## Main statements

* `MMP.Resolution.Kollar.exists_fg_eq_adjoin_roots`: `k'[x^{p^{-m}}]` is a finitely generated
  `k[x]`-module.
* `MMP.Resolution.Kollar.exists_le_adjoin_roots_of_isPurelyInseparable`: a finite purely
  inseparable `E/K` lies in `k'(x^{p^{-m}})` for some `m` and some finite purely inseparable
  `k'/k`.

## Implementation notes

`K` is `FractionRing (MvPolynomial (Fin n) k)` and `K̄` is `AlgebraicClosure K`; `xᵢ ∈ K̄` is the
image of `X i`, and `k[x₁, …, xₙ] ⊆ K̄` is `Algebra.adjoin k (range x)`, which makes `K̄` a
`k[x]`-module. The `p^m`-th roots `xᵢ^{p^{-m}} ∈ K̄` are elements `y i` with `y i ^ p^m = xᵢ`; in
characteristic `p` they are unique, so the statements quantify over them. Subrings and subfields
of `K̄` are compared as subsets of `K̄`.
-/

@[expose] public section

namespace MMP.Resolution.Kollar

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)

/-- The rational function field `K = k(x₁, …, xₙ)`. -/
abbrev RatFunField : Type _ := FractionRing (MvPolynomial (Fin n) k)

/-- The variable `xᵢ` as an element of the algebraic closure `K̄` of `k(x₁, …, xₙ)`. -/
noncomputable def varInClosure (i : Fin n) : AlgebraicClosure (RatFunField k n) :=
  algebraMap (RatFunField k n) (AlgebraicClosure (RatFunField k n))
    (algebraMap (MvPolynomial (Fin n) k) (RatFunField k n) (MvPolynomial.X i))

/-- Shorthand for the algebraic closure. -/
private abbrev Kbar : Type _ := AlgebraicClosure (RatFunField k n)

/-- The polynomial ring `k[x₁, …, xₙ]` as a subring of `K̄`. -/
noncomputable def polyInClosure : Subalgebra k (AlgebraicClosure (RatFunField k n)) :=
  Algebra.adjoin k (Set.range (varInClosure k n))

/-- Each variable `xᵢ` lies in `k[x₁, …, xₙ] ⊆ K̄`. -/
theorem varInClosure_mem_polyInClosure (i : Fin n) : varInClosure k n i ∈ polyInClosure k n :=
  Algebra.subset_adjoin ⟨i, rfl⟩

omit [CharP k p] in
/-- **Kollár, proof of Theorem 1.33** (tacit). Let `k` be a field of characteristic `p > 0`,
`K = k(x₁, …, xₙ)`, `K̄` an algebraic closure, `m ≥ 0`, and `k' ⊆ K̄` a finite extension of `k`.
Then the subring `R' = k'[x₁^{p^{-m}}, …, xₙ^{p^{-m}}]` of `K̄` is a finitely generated module over
`R = k[x₁, …, xₙ]`. (The characteristic hypothesis is not needed and is dropped.) -/
@[mmp "lem_kr1b_root_field_ring_finite"]
theorem exists_fg_eq_adjoin_roots (m : ℕ)
    (k' : IntermediateField k (AlgebraicClosure (RatFunField k n))) [FiniteDimensional k k']
    (y : Fin n → AlgebraicClosure (RatFunField k n)) (hy : ∀ i, y i ^ p ^ m = varInClosure k n i) :
    ∃ M : Submodule (polyInClosure k n) (AlgebraicClosure (RatFunField k n)),
      M.FG ∧ (M : Set (AlgebraicClosure (RatFunField k n))) = Algebra.adjoin k' (Set.range y) := by
  classical
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule k k').FG)
  let s : Set (Kbar k n) := (fun e : k' => (e : (Kbar k n))) '' (t : Set k') ∪ Set.range y
  let A' : Subalgebra (polyInClosure k n) (Kbar k n) := Algebra.adjoin (polyInClosure k n) s
  have hint : ∀ x ∈ s, IsIntegral (polyInClosure k n) x := by
    rintro x (⟨e, -, rfl⟩ | ⟨i, rfl⟩)
    · exact ((Algebra.IsIntegral.isIntegral (R := k) e).map k'.val).tower_top
    · refine ⟨Polynomial.X ^ p ^ m - Polynomial.C ⟨_, varInClosure_mem_polyInClosure k n i⟩,
        Polynomial.monic_X_pow_sub_C _ (pow_ne_zero m (Fact.out : p.Prime).ne_zero), ?_⟩
      simp [hy i]
  have : Module.Finite (polyInClosure k n) A' :=
    Algebra.finite_adjoin_of_finite_of_isIntegral
      ((t.finite_toSet.image _).union (Set.finite_range _)) hint
  have hR : polyInClosure k n ≤ (Algebra.adjoin k' (Set.range y)).restrictScalars k := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    rw [← hy i]
    have h : y i ∈ Algebra.adjoin k' (Set.range y) := Algebra.subset_adjoin ⟨i, rfl⟩
    exact pow_mem h _
  have hk : ∀ q : k', (q : (Kbar k n)) ∈ A' := by
    intro q
    have hq : q ∈ Submodule.span k (t : Set k') := ht ▸ Submodule.mem_top
    induction hq using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin (s := s) (Or.inl ⟨x, hx, rfl⟩)
    | zero => exact zero_mem A'
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha =>
      rw [show ((c • a : k') : Kbar k n) = algebraMap k (Kbar k n) c * (a : Kbar k n) by
        simp [Algebra.smul_def]]
      exact mul_mem (A'.algebraMap_mem (algebraMap k (polyInClosure k n) c)) ha
  refine ⟨Subalgebra.toSubmodule A', Module.Finite.iff_fg.mp inferInstance,
    Set.Subset.antisymm (fun x (hx : x ∈ A') => ?_) (fun x hx => ?_)⟩
  · induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨e, -, rfl⟩ | ⟨i, rfl⟩
      · exact Subalgebra.algebraMap_mem (Algebra.adjoin k' (Set.range y)) e
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r => exact hR r.2
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  · change x ∈ A'
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inr hx)
    | algebraMap q => exact hk q
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

private lemma algebraMap_algebraMap_eq_aeval (f : MvPolynomial (Fin n) k) :
    algebraMap (RatFunField k n) (Kbar k n)
      (algebraMap (MvPolynomial (Fin n) k) (RatFunField k n) f) =
      MvPolynomial.aeval (varInClosure k n) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | mul_X a i ha =>
    rw [map_mul, map_mul, ha, map_mul, MvPolynomial.aeval_X]
    rfl

private lemma algebraMap_algebraMap_mem (F : Subring (Kbar k n))
    (hk : ∀ a : k, algebraMap k (Kbar k n) a ∈ F) (hx : ∀ i, varInClosure k n i ∈ F)
    (f : MvPolynomial (Fin n) k) :
    algebraMap (RatFunField k n) (Kbar k n)
      (algebraMap (MvPolynomial (Fin n) k) (RatFunField k n) f) ∈ F := by
  rw [algebraMap_algebraMap_eq_aeval]
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C]
    exact hk a
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | mul_X a i ha =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact mul_mem ha (hx i)

private lemma algebraMap_mem_of_subfield (F : Subfield (Kbar k n))
    (hk : ∀ a : k, algebraMap k (Kbar k n) a ∈ F) (hx : ∀ i, varInClosure k n i ∈ F)
    (v : RatFunField k n) : algebraMap (RatFunField k n) (Kbar k n) v ∈ F := by
  obtain ⟨f, g, _, h⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) k) v
  rw [← h, map_div₀]
  exact div_mem (algebraMap_algebraMap_mem k n F.toSubring hk hx f)
    (algebraMap_algebraMap_mem k n F.toSubring hk hx g)

private lemma subset_of_basis_mem (E : IntermediateField (RatFunField k n) (Kbar k n))
    [FiniteDimensional (RatFunField k n) E] (F : Subfield (Kbar k n))
    (hk : ∀ a : k, algebraMap k (Kbar k n) a ∈ F) (hx : ∀ i, varInClosure k n i ∈ F)
    (hb : ∀ j, ((Module.finBasis (RatFunField k n) E j : E) : Kbar k n) ∈ F) :
    (E : Set (Kbar k n)) ⊆ F := by
  intro x hxE
  let b := Module.finBasis (RatFunField k n) E
  have hsum : x = ∑ i, algebraMap (RatFunField k n) (Kbar k n) (b.repr ⟨x, hxE⟩ i) *
      ((b i : E) : Kbar k n) := by
    simpa [Algebra.smul_def] using
      (congrArg (fun z : E => (z : Kbar k n)) (b.sum_repr ⟨x, hxE⟩)).symm
  rw [SetLike.mem_coe, hsum]
  exact sum_mem fun i _ => mul_mem (algebraMap_mem_of_subfield k n F hk hx _) (hb i)

private lemma exists_pow_eq_algebraMap (E : IntermediateField (RatFunField k n) (Kbar k n))
    [IsPurelyInseparable (RatFunField k n) E] {ι : Type*} [Finite ι] (v : ι → E) :
    ∃ a : ℕ, ∀ j, ∃ u : RatFunField k n,
      ((v j : E) : Kbar k n) ^ p ^ a = algebraMap (RatFunField k n) (Kbar k n) u := by
  have : ExpChar (RatFunField k n) p := ExpChar.prime (Fact.out)
  choose nn hnn using fun j => IsPurelyInseparable.pow_mem (RatFunField k n) p (v j)
  obtain ⟨a, ha⟩ := Finite.exists_le nn
  refine ⟨a, fun j => ?_⟩
  obtain ⟨u, hu⟩ := hnn j
  refine ⟨u ^ p ^ (a - nn j), ?_⟩
  have h1 : ((v j : E) : Kbar k n) ^ p ^ nn j = algebraMap (RatFunField k n) (Kbar k n) u :=
    (congrArg Subtype.val hu).symm
  rw [map_pow, ← h1, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (ha j)]

private lemma finiteDimensional_isPurelyInseparable_adjoin (a : ℕ) (S : Set (Kbar k n))
    (hS : S.Finite) (hSr : ∀ x ∈ S, ∃ c : k, x ^ p ^ a = algebraMap k (Kbar k n) c) :
    FiniteDimensional k (IntermediateField.adjoin k S) ∧
      IsPurelyInseparable k (IntermediateField.adjoin k S) := by
  have : ExpChar (Kbar k n) p := ExpChar.prime (Fact.out)
  refine ⟨?_, (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (Kbar k n) p).2
    fun x hx => ?_⟩
  · have := hS.to_subtype
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨c, hc⟩ := hSr x hx
    refine ⟨Polynomial.X ^ p ^ a - Polynomial.C c,
      Polynomial.monic_X_pow_sub_C _ (pow_pos (Fact.out : p.Prime).pos a).ne', ?_⟩
    simp [hc]
  · obtain ⟨c, hc⟩ := hSr x hx
    exact ⟨a, c, hc.symm⟩

private lemma exists_root_of_poly (m : ℕ) (r : k → Kbar k n)
    (hr : ∀ c, r c ^ p ^ m = algebraMap k (Kbar k n) c)
    (y : Fin n → Kbar k n) (hy : ∀ i, y i ^ p ^ m = varInClosure k n i)
    (f : MvPolynomial (Fin n) k) :
    ∃ z : Kbar k n, z ^ p ^ m = algebraMap (RatFunField k n) (Kbar k n)
      (algebraMap (MvPolynomial (Fin n) k) (RatFunField k n) f) ∧
      ∀ F : Subring (Kbar k n), (∀ s ∈ f.support, r (f.coeff s) ∈ F) → (∀ i, y i ∈ F) → z ∈ F := by
  refine ⟨∑ s ∈ f.support, r (f.coeff s) * s.prod fun i e => y i ^ e, ?_, ?_⟩
  · have : ExpChar (Kbar k n) p := ExpChar.prime (Fact.out)
    rw [sum_pow_char_pow, algebraMap_algebraMap_eq_aeval]
    conv_rhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_pow, hr, MvPolynomial.aeval_monomial, Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, hy]
  · exact fun F h1 h2 =>
      sum_mem fun s hs => mul_mem (h1 s hs) (prod_mem fun i _ => pow_mem (h2 i) _)

private lemma mem_of_pow_eq_algebraMap_div (m : ℕ) (r : k → Kbar k n)
    (hr : ∀ c, r c ^ p ^ m = algebraMap k (Kbar k n) c)
    (y : Fin n → Kbar k n) (hy : ∀ i, y i ^ p ^ m = varInClosure k n i)
    (F : Subfield (Kbar k n)) (hyF : ∀ i, y i ∈ F) (f g : MvPolynomial (Fin n) k)
    (hf : ∀ s ∈ f.support, r (f.coeff s) ∈ F) (hg : ∀ s ∈ g.support, r (g.coeff s) ∈ F)
    {w : Kbar k n} (hw : w ^ p ^ m = algebraMap (RatFunField k n) (Kbar k n)
      (algebraMap (MvPolynomial (Fin n) k) (RatFunField k n) f /
        algebraMap (MvPolynomial (Fin n) k) (RatFunField k n) g)) :
    w ∈ F := by
  have : ExpChar (Kbar k n) p := ExpChar.prime (Fact.out)
  obtain ⟨zf, hzf, hzf'⟩ := exists_root_of_poly k p n m r hr y hy f
  obtain ⟨zg, hzg, hzg'⟩ := exists_root_of_poly k p n m r hr y hy g
  have : zf / zg = w := by
    apply iterateFrobenius_inj (Kbar k n) p m
    simp only [iterateFrobenius_def]
    rw [div_pow, hzf, hzg, hw, map_div₀]
  rw [← this]
  exact div_mem (hzf' F.toSubring hf hyF) (hzg' F.toSubring hg hyF)

/-- **Kollár, proof of Theorem 1.33.** Let `k` be a field of characteristic `p > 0`,
`K = k(x₁, …, xₙ)`, `K̄` an algebraic closure, and `E ⊆ K̄` a finite purely inseparable extension
of `K`. Then there are `m ≥ 0` and a finite purely inseparable extension `k' ⊆ K̄` of `k` with
`E ⊆ k'(x₁^{p^{-m}}, …, xₙ^{p^{-m}})`, the subfield of `K̄` generated by `k'` and the `p^m`-th
roots of the `xᵢ`. -/
@[mmp "lem_kr1b_purely_inseparable_in_root_field"]
theorem exists_le_adjoin_roots_of_isPurelyInseparable
    (E : IntermediateField (RatFunField k n) (AlgebraicClosure (RatFunField k n)))
    [FiniteDimensional (RatFunField k n) E] [IsPurelyInseparable (RatFunField k n) E] :
    ∃ (m : ℕ) (k' : IntermediateField k (AlgebraicClosure (RatFunField k n))),
      FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
        ∀ y : Fin n → AlgebraicClosure (RatFunField k n),
          (∀ i, y i ^ p ^ m = varInClosure k n i) →
            (E : Set (AlgebraicClosure (RatFunField k n))) ⊆
              IntermediateField.adjoin k' (Set.range y) := by
  classical
  let b := Module.finBasis (RatFunField k n) E
  obtain ⟨a, hu⟩ := exists_pow_eq_algebraMap k p n E b
  choose u hu using hu
  choose f g hg hfg using fun j =>
    IsFractionRing.div_surjective (A := MvPolynomial (Fin n) k) (u j)
  choose r hr using fun c : k =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap k (Kbar k n) c) (pow_pos (Fact.out : p.Prime).pos a)
  let S : Set (Kbar k n) := ⋃ j, ((fun s => r ((f j).coeff s)) '' ((f j).support : Set _) ∪
    (fun s => r ((g j).coeff s)) '' ((g j).support : Set _))
  have hSfin : S.Finite := Set.finite_iUnion fun j =>
    ((Finset.finite_toSet _).image _).union ((Finset.finite_toSet _).image _)
  have hSr : ∀ x ∈ S, ∃ c, x ^ p ^ a = algebraMap k (Kbar k n) c := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rcases hj with ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩ <;> exact ⟨_, hr _⟩
  obtain ⟨hfin, hpi⟩ := finiteDimensional_isPurelyInseparable_adjoin k p n a S hSfin hSr
  refine ⟨a, IntermediateField.adjoin k S, hfin, hpi, fun y hy => ?_⟩
  let F := IntermediateField.adjoin (IntermediateField.adjoin k S) (Set.range y)
  have hk : ∀ q ∈ IntermediateField.adjoin k S, q ∈ F := fun q hq =>
    F.algebraMap_mem (⟨q, hq⟩ : IntermediateField.adjoin k S)
  have hyF : ∀ i, y i ∈ F := fun i =>
    IntermediateField.subset_adjoin (IntermediateField.adjoin k S) (Set.range y) ⟨i, rfl⟩
  refine subset_of_basis_mem k n E F.toSubfield
    (fun c => hk _ ((IntermediateField.adjoin k S).algebraMap_mem c))
    (fun i => hy i ▸ pow_mem (hyF i) _) fun j => ?_
  refine mem_of_pow_eq_algebraMap_div k p n a r hr y hy F.toSubfield hyF (f j) (g j)
    (fun s hs => hk _ (IntermediateField.subset_adjoin k S
      (Set.mem_iUnion.mpr ⟨j, Or.inl ⟨s, hs, rfl⟩⟩)))
    (fun s hs => hk _ (IntermediateField.subset_adjoin k S
      (Set.mem_iUnion.mpr ⟨j, Or.inr ⟨s, hs, rfl⟩⟩))) ?_
  rw [hu j, hfg j]

end MMP.Resolution.Kollar
