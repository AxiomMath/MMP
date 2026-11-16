module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialStepTermination
import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupSequence

/-!
# The monomial order reduction sequence reduces the maximal order

Let `(X, E, A)` be monomial data over a field `k` of characteristic zero with `X` equidimensional,
`n = dim X` and `m ≥ 1`. The monomial order reduction sequence of `(X, E, A, m)`, the concatenation
of the Step-3.1, …, Step-3.`n` sequences, is a smooth blow-up sequence of order `≥ m` starting with
the marked triple `(X, I_{E,A}, m, E)`, `I_{E,A} = 𝒪_X(-A)`, and the last ideal `I_r` of the
iterated birational transform along it has `maxord I_r < m`.

The proof runs through the steps. Each Step-3.`r` sequence is finite and ends with data satisfying
`m_t < m` for every `t ≤ r`; every single step is a smooth blow-up of the current marked triple
`(X_q, I_{E_q, A_q}, m, E_q)` whose birational transform is again the ideal of monomial data. At a
point `x` of the final scheme, with `J_x` the set of members of `E` through `x` (at most `n` of
them), `ord_x I_{E,A} ≤ σ_{J_x}(x) ≤ m_{|J_x|} < m`.

## Main results

* `MMP.Resolution.MonomialData.isOrderGeMarkedTripleSeq_monomialOrderReduction`: for monomial
  data `C` on an equidimensional `X` over a field of characteristic zero and `1 ≤ m`,
  `C.monomialOrderReduction m` is a smooth blow-up sequence of order `≥ m` starting with
  `(X, C.monomialIdeal, m, C.E)`, and the iterated birational transform of `(C.monomialIdeal, m)`
  along it has maximal order `< m`.

## Implementation notes

The hypothesis `CharZero C.k` is the standing characteristic-zero convention of Kollár's §3; it
is part of the definition of a triple (`MMP.Resolution.IsTriple`), so the conclusion cannot hold
without it. Likewise `Equidimensional X` is a clause of `IsTriple`, and monomial data does not
supply it: Kollár's `X` is a smooth variety. For `X = Spec k ⊔ 𝔸¹_k`, `E = ∅`, `A = 0`, `m = 1`
the sequence is empty and `(X, 𝒪_X, ∅)` is not a triple.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.111, Step 3]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

namespace MonomialData

open Aux

/-! ### Geometric input -/

/-- No prime divisor contains the generic point of an irreducible component. -/
private theorem notMem_support_of_closure_mem_irreducibleComponents {X : Scheme.{u}}
    (D : AlgebraicGeometry.PrimeDivisor X) {η : X}
    (hη : closure ({η} : Set X) ∈ irreducibleComponents X) : η ∉ D.support := by
  intro hηD
  have h0 : codimension (IrreducibleCloseds.closureSingleton D.genericPoint) = 0 := by
    rw [codimension_eq_coheight, Order.coheight_eq_zero]
    intro C hC
    have hDC : (D.support : Set X) ⊆ C := by
      rw [support_eq_closure_genericPoint]; exact hC
    have hηC : closure ({η} : Set X) ⊆ C :=
      closure_minimal (Set.singleton_subset_iff.2 (hDC hηD)) C.isClosed
    have hCeq : (C : Set X) = closure {η} := (hη.2 C.isIrreducible hηC).antisymm hηC
    change (C : Set X) ⊆ closure {D.genericPoint}
    rw [hCeq, ← support_eq_closure_genericPoint]
    exact closure_minimal (Set.singleton_subset_iff.2 hηD) D.idealSheaf.support.isClosed
  have h1 := D.codimension_one
  change codimension (IrreducibleCloseds.closureSingleton D.genericPoint) = 1 at h1
  rw [h0] at h1; exact zero_ne_one h1

/-- The ideal `𝒪_X(-A)` of monomial data is nonzero at every generic point of `X`. -/
private theorem isNonzeroAtGenericPoints_monomialIdeal {X : Scheme.{u}} (C : MonomialData X) :
    IsNonzeroAtGenericPoints C.monomialIdeal := by
  classical
  intro η hη
  have htop : IdealSheafData.stalk C.monomialIdeal η = ⊤ := by
    unfold MonomialData.monomialIdeal divisorIdeal
    by_cases hfin : (Function.mulSupport fun D : AlgebraicGeometry.PrimeDivisor X =>
        D.idealSheaf ^ C.A D).Finite
    · rw [finprod_eq_prod _ hfin, Aux.stalk_prod]
      rw [← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun D _ => ?_
      rw [Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
          (notMem_support_of_closure_mem_irreducibleComponents D hη),
        Ideal.top_pow, Ideal.one_eq_top]
    · rw [finprod_of_infinite_mulSupport hfin]
      exact stalk_one η
  rw [htop]; exact top_ne_bot

/-- A blow-up of a quasi-compact scheme locally of finite type over a field does not raise
`dimNat`. -/
private theorem dimNat_blowUp_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) : dimNat (blowUp Z) ≤ dimNat X := by
  have hle : topologicalKrullDim (blowUp Z) ≤ topologicalKrullDim X :=
    MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun C hC => by
      obtain ⟨D, -, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hC
      rw [h]; exact topologicalKrullDim_subspace_le X D
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hne : topologicalKrullDim X ≠ ⊤ := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  unfold dimNat
  generalize topologicalKrullDim X = b at hle hne
  generalize topologicalKrullDim (blowUp Z) = a at hle
  induction b using WithBot.recBotCoe with
  | bot => simp at hle; subst hle; simp
  | coe b =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe a =>
      simp only [WithBot.unbotD_coe]
      have : a ≤ b := WithBot.coe_le_coe.mp hle
      have hb : b ≠ ⊤ := fun h => hne (by simp [h])
      exact ENat.toNat_le_toNat this hb

open Classical in
/-- The members of `E` through `x`. -/
private noncomputable def throughIndex {X : Scheme.{u}} (C : MonomialData X) (x : X) :
    Finset (Fin C.E.s) :=
  Finset.univ.filter fun j => x ∈ ((C.E.E j).support : Set X)

/-- At most `dim X` members of the snc divisor `E` pass through a point. -/
private theorem card_throughIndex_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (x : X) : (throughIndex C x).card ≤ dimNat X := by
  classical
  obtain ⟨-, hlft, hqc, hsnc, -, -⟩ := hC
  have : LocallyOfFiniteType C.sX := hlft
  have : QuasiCompact C.sX := hqc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace C.sX
  have hne : topologicalKrullDim X ≠ ⊤ := topologicalKrullDim_ne_top_of_locallyOfFiniteType C.k C.sX
  obtain ⟨n, z, c, hz, -, hc⟩ := hsnc.2.2 x
  have hcard : (throughIndex C x).card ≤ n := by
    have := Fintype.card_le_of_injective c hc
    simp only [Fintype.card_fin] at this
    refine le_trans (le_of_eq ?_) this
    rw [Fintype.card_subtype]; rfl
  have hdim : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    have h1 : ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup_of_le x le_rfl
    rw [hz.2] at h1; exact_mod_cast h1
  refine hcard.trans ?_
  unfold dimNat
  generalize topologicalKrullDim X = b at hne hdim
  induction b using WithBot.recBotCoe with
  | bot => simp at hdim
  | coe b =>
    simp only [WithBot.unbotD_coe]
    have hb : b ≠ ⊤ := fun h => hne (by simp [h])
    have : (n : ℕ∞) ≤ b := WithBot.coe_le_coe.mp hdim
    lift b to ℕ using hb
    simpa using this

/-! ### Orders of monomials in a regular system of parameters -/

section RegularLocal

open IsLocalRing

/-- In a regular local ring, the monomial `x^e` in a minimal generating list `x` of `𝔪` does not
lie in `𝔪^(|e| + 1)`: its class in `𝔪^|e|/𝔪^(|e|+1)` is the image of the monomial `X^e` under the
isomorphism `κ[X_1, …, X_d] ≅ Gr_𝔪(R)`. -/
private theorem prod_pow_notMem_of_ofList {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (xs : List R) (hxs : Ideal.ofList xs = maximalIdeal R)
    (hmin : xs.length = (maximalIdeal R).spanFinrank) (e : Fin xs.length →₀ ℕ) :
    ∏ i, xs[i] ^ e i ∉ maximalIdeal R ^ (∑ i, e i + 1) := by
  intro hmem
  have hx : ∀ i : Fin xs.length, xs[i] ∈ maximalIdeal R := fun i => by
    rw [← hxs]; exact Ideal.subset_span (List.getElem_mem _)
  have hinj :=
    (IsRegularLocalRing.gradedRing_maximalIdeal_isPolynomialAlgebra xs hxs hmin hx).1.1
  have hmem' : (1 : R) * ∏ i, xs[i] ^ e i ∈ maximalIdeal R ^ (∑ i, e i) := by
    rw [one_mul]
    exact AssociatedGraded.prod_mem_pow_sum _ e (fun i => xs[i] ^ e i)
      (fun i => Ideal.pow_mem_pow (hx i) _) Finset.univ
  have h0 := AssociatedGraded.polyGradedHom_monomial (maximalIdeal R)
    (fun i : Fin xs.length => xs[i]) hx e 1 rfl hmem'
  have hz : AssociatedGraded.classOfPow (maximalIdeal R) (∑ i, e i)
      ⟨(1 : R) * ∏ i, xs[i] ^ e i, hmem'⟩ = 0 := by
    change DFinsupp.single _ _ = 0
    rw [DFinsupp.single_eq_zero]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change _ ∈ AssociatedGraded.power (M := R) (maximalIdeal R) (∑ i, e i + 1)
    rw [AssociatedGraded.ring_power_eq]
    simpa using hmem
  rw [hz, ← map_zero (AssociatedGraded.polyGradedHom (maximalIdeal R)
    (fun i : Fin xs.length => xs[i]) hx)] at h0
  have h1 := congrArg (·.coeff e) (hinj h0)
  rw [MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- In a Noetherian local ring with a regular system of parameters `z`, the monomial `z^e` does
not lie in `𝔪^(|e| + 1)`. -/
private theorem prod_pow_notMem_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {n : ℕ} {z : Fin n → R}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (e : Fin n → ℕ) :
    ∏ i, z i ^ e i ∉ maximalIdeal R ^ (∑ i, e i + 1) := by
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hlen : (List.ofFn z).length = n := List.length_ofFn
  have hxs : Ideal.ofList (List.ofFn z) = maximalIdeal R := by
    rw [← hz.1, Ideal.ofList]
    congr 1
    ext r; simp [List.mem_ofFn]
  have hmin : (List.ofFn z).length = (maximalIdeal R).spanFinrank := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hz.2] at h
    rw [hlen]; exact_mod_cast h.symm
  have := prod_pow_notMem_of_ofList (List.ofFn z) hxs hmin
    (Finsupp.equivFunOnFinite.symm fun i => e (Fin.cast hlen i))
  simp only [Finsupp.coe_equivFunOnFinite_symm, List.getElem_ofFn] at this
  have hp : ∏ i : Fin (List.ofFn z).length, (List.ofFn z)[i] ^ e (Fin.cast hlen i) =
      ∏ i, z i ^ e i := by
    rw [← Fin.prod_congr' (fun i => z i ^ e i) hlen]
    simp [Fin.cast]
  have hsum : ∑ i : Fin (List.ofFn z).length, e (Fin.cast hlen i) = ∑ i, e i :=
    Fin.sum_congr' e hlen
  rwa [hp, hsum] at this

/-- The order reverses inclusion of ideals. -/
private theorem idealOrder_anti {R : Type*} [CommRing R] [IsLocalRing R] {I J : Ideal R}
    (h : I ≤ J) : idealOrder J ≤ idealOrder I :=
  iSup₂_le fun j hj =>
    le_iSup₂_of_le (f := fun (j : ℕ) (_ : I ≤ maximalIdeal R ^ j) => (j : ℕ∞)) j (h.trans hj)
      le_rfl

/-- An element outside `𝔪^(d+1)` generates an ideal of order at most `d`. -/
private theorem idealOrder_span_singleton_le {R : Type*} [CommRing R] [IsLocalRing R] {f : R}
    {d : ℕ} (hf : f ∉ maximalIdeal R ^ (d + 1)) : idealOrder (Ideal.span {f}) ≤ d :=
  iSup₂_le fun j hj => by
    by_contra hlt
    have : d + 1 ≤ j := by exact_mod_cast Order.add_one_le_of_lt (not_le.1 hlt)
    exact hf (Ideal.pow_le_pow_right this ((Ideal.span_singleton_le_iff_mem _).1 hj))

end RegularLocal

/-! ### The order of `𝒪_X(-A)` at a point -/

/-- An ideal sheaf whose support contains a prime divisor `D` is contained in the ideal of `D`. -/
private theorem le_idealSheaf_of_support_subset {X : Scheme.{u}} (I : X.IdealSheafData)
    (D : AlgebraicGeometry.PrimeDivisor X) (h : (D.support : Set X) ⊆ I.support) :
    I ≤ D.idealSheaf := by
  haveI := D.integral
  have hD : Scheme.IdealSheafData.vanishingIdeal D.idealSheaf.support = D.idealSheaf :=
    (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl).symm
  rw [← hD]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 h

/-- An irreducible component of `D` lies in `D`. -/
private theorem subset_of_mem_componentsOf {T : Type*} [TopologicalSpace T] {D W : Set T}
    (h : W ∈ componentsOf D) : W ⊆ D := by
  simp only [componentsOf, Set.mem_setOf_eq] at h
  exact h.prop.2

open Classical in
/-- The prime divisors through `x` with nonzero coefficient in `A`. -/
private noncomputable def throughDivisors {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (x : X) : Finset (AlgebraicGeometry.PrimeDivisor X) :=
  hfin.toFinset.filter fun D => x ∈ (D.support : Set X)

private theorem mem_throughDivisors {X : Scheme.{u}} {C : MonomialData X}
    {hfin : (Function.support C.A).Finite} {x : X} {D : AlgebraicGeometry.PrimeDivisor X} :
    D ∈ throughDivisors C hfin x ↔ C.A D ≠ 0 ∧ x ∈ (D.support : Set X) := by
  simp [throughDivisors]

/-- The stalk of `𝒪_X(-A)` at `x` is `∏_{D ∋ x} (𝒪_X(-D))_x ^ a_D`. -/
private theorem stalk_monomialIdeal_eq_prod {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (x : X) :
    IdealSheafData.stalk C.monomialIdeal x =
      ∏ D ∈ throughDivisors C hfin x, IdealSheafData.stalk D.idealSheaf x ^ C.A D := by
  classical
  unfold MonomialData.monomialIdeal divisorIdeal
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) fun D hD => by
      simpa using fun h0 => hD (by simp [h0]),
    Aux.stalk_prod, ← Finset.prod_filter_mul_prod_filter_not hfin.toFinset
      fun D => x ∈ (D.support : Set X)]
  conv_rhs => rw [← mul_one (∏ D ∈ _, _)]
  congr 1
  · exact Finset.prod_congr rfl fun D _ => Aux.stalk_pow _ _ _
  · refine Finset.prod_eq_one fun D hD => ?_
    rw [Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
      (Finset.mem_filter.1 hD).2, Ideal.top_pow, Ideal.one_eq_top]

/-- Each prime divisor through `x` with nonzero coefficient is a component of a member of `E`
through `x`. -/
private theorem exists_component_of_mem_throughDivisors {X : Scheme.{u}} {C : MonomialData X}
    (hC : C.IsMonomialData) {x : X} {D : AlgebraicGeometry.PrimeDivisor X}
    (hD : D ∈ throughDivisors C hC.2.2.2.2.1 x) : ∃ i : Fin C.E.s,
      D.support ∈ componentsOf ((C.E.E i).support : Set X) ∧ x ∈ ((C.E.E i).support : Set X) := by
  rw [mem_throughDivisors] at hD
  obtain ⟨i, hi⟩ := hC.2.2.2.2.2 D hD.1
  exact ⟨i, hi, subset_of_mem_componentsOf hi hD.2⟩

/-- In coordinates `z` at `x` in which the members of `E` through `x` are `(z_{c(j)})`, the stalk
of `𝒪_X(-A)` contains a monomial in `z` of degree `∑_{D ∋ x} a_D`. -/
private theorem exists_monomial_le_stalk {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) {x : X} {n : ℕ} (z : Fin n → X.presheaf.stalk x)
    (c : {j // x ∈ ((C.E.E j).support : Set X)} → Fin n)
    (hzE : ∀ j, IdealSheafData.stalk (C.E.E j.1) x = Ideal.span {z (c j)}) :
    ∃ e : Fin n → ℕ, ∑ i, e i = ∑ D ∈ throughDivisors C hC.2.2.2.2.1 x, C.A D ∧
      Ideal.span {∏ i, z i ^ e i} ≤ IdealSheafData.stalk C.monomialIdeal x := by
  classical
  rw [stalk_monomialIdeal_eq_prod C hC.2.2.2.2.1]
  suffices ∀ t ⊆ throughDivisors C hC.2.2.2.2.1 x, ∃ e : Fin n → ℕ, ∑ i, e i = ∑ D ∈ t, C.A D ∧
      Ideal.span {∏ i, z i ^ e i} ≤ ∏ D ∈ t, IdealSheafData.stalk D.idealSheaf x ^ C.A D from
    this _ le_rfl
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; exact ⟨0, by simp, by simp⟩
  | insert D t hDt IH =>
    intro ht
    obtain ⟨e, he, hle⟩ := IH ((Finset.subset_insert _ _).trans ht)
    obtain ⟨i, hi, hxi⟩ := exists_component_of_mem_throughDivisors hC (ht (t.mem_insert_self D))
    refine ⟨fun j => e j + if j = c ⟨i, hxi⟩ then C.A D else 0, ?_, ?_⟩
    · simp [Finset.sum_insert hDt, Finset.sum_add_distrib, ← he, add_comm]
    · have hprod : ∏ j, z j ^ (e j + if j = c ⟨i, hxi⟩ then C.A D else 0) =
          z (c ⟨i, hxi⟩) ^ C.A D * ∏ j, z j ^ e j := by
        simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero]
        rw [mul_comm]
        simp
      rw [hprod, Finset.prod_insert hDt, ← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_pow, ← hzE ⟨i, hxi⟩]
      exact Ideal.mul_mono (Ideal.pow_right_mono (stalk_le_stalk_of_le
        (le_idealSheaf_of_support_subset _ _ (subset_of_mem_componentsOf hi)) x) _) hle

/-- `∑_{D ∋ x} a_D ≤ σ_{J_x}(x)`. -/
private theorem sum_throughDivisors_le_stratumWeight {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (x : X) :
    ∑ D ∈ throughDivisors C hC.2.2.2.2.1 x, C.A D ≤ C.stratumWeight (throughIndex C x) x := by
  classical
  have hfin := hC.2.2.2.2.1
  let f : Fin C.E.s → AlgebraicGeometry.PrimeDivisor X → ℕ := fun j D =>
    if D.support ∈ componentsOf ((C.E.E j).support : Set X) ∧ x ∈ (D.support : Set X)
    then C.A D else 0
  unfold MonomialData.stratumWeight
  calc ∑ D ∈ throughDivisors C hfin x, C.A D
      ≤ ∑ D ∈ throughDivisors C hfin x, ∑ j ∈ throughIndex C x, f j D := by
        refine Finset.sum_le_sum fun D hD => ?_
        obtain ⟨i, hi, hxi⟩ := exists_component_of_mem_throughDivisors hC hD
        refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := (f · D)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxi⟩ : i ∈ throughIndex C x))
        exact (if_pos ⟨hi, (mem_throughDivisors.1 hD).2⟩).symm
    _ = ∑ j ∈ throughIndex C x, ∑ D ∈ throughDivisors C hfin x, f j D := Finset.sum_comm
    _ ≤ ∑ j ∈ throughIndex C x, C.coeffAt j x := by
        refine Finset.sum_le_sum fun j _ => ?_
        unfold MonomialData.coeffAt
        rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun D hD => by
          simpa using fun h0 => hD (by simp [h0])]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Nat.zero_le _

/-- The order of `𝒪_X(-A)` at `x` is at most `σ_{J_x}(x)`, where `J_x` is the set of members of
`E` through `x`. -/
private theorem multAt_monomialIdeal_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (x : X) :
    multAt C.monomialIdeal x ≤ (C.stratumWeight (throughIndex C x) x : ℕ∞) := by
  have : LocallyOfFiniteType C.sX := hC.2.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  obtain ⟨n, z, c, hz, hzE, -⟩ := hC.2.2.2.1.2.2 x
  obtain ⟨e, he, hle⟩ := exists_monomial_le_stalk C hC z c hzE
  refine (idealOrder_anti hle).trans <| (idealOrder_span_singleton_le
    (prod_pow_notMem_of_isRegularSystemOfParameters hz e)).trans ?_
  rw [he]
  exact_mod_cast sum_throughDivisors_le_stratumWeight C hC x

/-! ### Bounds on weights -/

/-- A coefficient `a_j(x)` is at most the sum of all coefficients of `A`. -/
private theorem coeffAt_le_finsum {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (j : Fin C.E.s) (x : X) :
    C.coeffAt j x ≤ ∑ᶠ D, C.A D := by
  classical
  unfold MonomialData.coeffAt
  refine finsum_le_finsum' (hfin.subset fun D hD => ?_) hfin fun D => ?_
  · by_contra h
    exact hD (by simp [Function.notMem_support.1 h])
  · dsimp only
    split_ifs <;> simp

/-- A family bounded pointwise by `B` has bounded range. -/
private theorem bddAbove_range_of_le {ι : Sort*} {f : ι → ℕ} {B : ℕ} (h : ∀ i, f i ≤ B) :
    BddAbove (Set.range f) :=
  ⟨B, Set.forall_mem_range.2 h⟩

/-- Every weight `σ_J(x)`, `|J| = r`, is at most `m_r(E, A)`. -/
private theorem stratumWeight_le_maxStratumWeight {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) {r : ℕ} {J : Finset (Fin C.E.s)} (hJ : J.card = r)
    {x : X} (hx : x ∈ C.stratum J) : C.stratumWeight J x ≤ C.maxStratumWeight r := by
  have hB : ∀ J' : Finset (Fin C.E.s), J'.card = r → ∀ x',
      C.stratumWeight J' x' ≤ r * ∑ᶠ D, C.A D := fun J' hJ' x' => by
    unfold MonomialData.stratumWeight
    rw [← hJ', ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j _ => coeffAt_le_finsum C hfin j x'
  unfold MonomialData.maxStratumWeight
  exact le_ciSup_of_le (bddAbove_range_of_le fun J' => ciSup_le' fun hJ' => ciSup_le' fun x' =>
      ciSup_le' fun _ => hB J' hJ' x') J <|
    le_ciSup_of_le (bddAbove_range_of_le fun hJ' => ciSup_le' fun x' => ciSup_le' fun _ =>
      hB J hJ' x') hJ <|
    le_ciSup_of_le (bddAbove_range_of_le fun x' => ciSup_le' fun _ => hB J hJ x') x <|
    le_ciSup_of_le (bddAbove_range_of_le fun _ => hB J hJ x) hx le_rfl

/-! ### The invariant carried along the sequence -/

/-- The data carried along the sequence: monomial data in characteristic zero on an
equidimensional scheme of dimension at most `n`. -/
private def Inv (n : ℕ) {X : Scheme.{u}} (C : MonomialData X) : Prop :=
  C.IsMonomialData ∧ CharZero C.k ∧ Equidimensional X ∧ dimNat X ≤ n

/-- `m_t < m` for all `1 ≤ t < r`. -/
private def Lower (m r : ℕ) {X : Scheme.{u}} (C : MonomialData X) : Prop :=
  ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m

/-- The conclusion for a blow-up sequence `B` starting with the data `C`. -/
private def Good (m : ℕ) {X : Scheme.{u}} (C : MonomialData X) (B : ClosedBlowupSequence X) :
    Prop :=
  B.IsOrderGeMarkedTripleSeq C.sX ⟨C.monomialIdeal, m⟩ C.E ∧
    maxOrder (B.markedTransform ⟨C.monomialIdeal, m⟩).I < (m : ℕ∞)

private theorem isTriple_of_inv {n : ℕ} {X : Scheme.{u}} {C : MonomialData X} (h : Inv n C) :
    IsTriple C.sX C.monomialIdeal C.E := by
  obtain ⟨⟨hsm, hlft, hqc, hsnc, -, -⟩, hk, hX, -⟩ := h
  exact ⟨hk, hsm, hlft, hqc, hX, isNonzeroAtGenericPoints_monomialIdeal C, hsnc⟩

private theorem inv_step {n m r : ℕ} {X : Scheme.{u}} {C : MonomialData X} (h : Inv n C)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) : Inv n (C.step m r) := by
  obtain ⟨hC, hk, hX, hd⟩ := h
  have hspec := step_spec C hC hk hr hm hmr
  obtain ⟨-, hlft, hqc, -⟩ := hC
  haveI : LocallyOfFiniteType C.sX := hlft
  haveI : QuasiCompact C.sX := hqc
  exact ⟨hspec.2.2.2.1, hk, equidimensional_blowUp C.sX _ hX,
    (dimNat_blowUp_le C.sX _).trans hd⟩

private theorem lower_step {n m r : ℕ} {X : Scheme.{u}} {C : MonomialData X} (h : Inv n C)
    (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) (hl : Lower m r C) :
    Lower m r (C.step m r) := by
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · intro t ht1 htr; omega
  · exact maxStratumWeight_step_lt C h.1 h.2.1 hr2 hm hl hmr

/-- One Step-3.`r` blow-up in front of a good sequence gives a good sequence. -/
private theorem good_cons {n m r : ℕ} {X : Scheme.{u}} {C : MonomialData X} (h : Inv n C)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r)
    {B : ClosedBlowupSequence (blowUp (C.stepCenter r))} (hB : Good m (C.step m r) B) :
    Good m C (.cons (C.stepCenter r) B) := by
  obtain ⟨⟨hcodim, hsnc, hord⟩, -, hbt, -⟩ := step_spec C h.1 h.2.1 hr hm hmr
  have ha : (⟨C.monomialIdeal, m⟩ : MarkedIdeal X).birationalTransform (C.stepCenter r) =
      ⟨(C.step m r).monomialIdeal, m⟩ := by
    rw [← hbt]; rfl
  have ht := isTriple_of_inv h
  refine ⟨⟨ht, ?_, hcodim, hsnc, hord, ?_⟩, ?_⟩
  · exact isSmoothScheme_of_hasSNCWith
      { X := X, I := C.monomialIdeal, E := C.E, k := C.k, sX := C.sX } ht _ hsnc
  · rw [ha]; exact hB.1
  · simp only [ClosedBlowupSequence.markedTransform]
    rw [ha]; exact hB.2

/-- The first `q` Step-3.`r` blow-ups, while `m_r ≥ m`. -/
private theorem good_stepPhase {n m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (K : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y) :
    ∀ (q : ℕ) {X : Scheme.{u}} (C : MonomialData X), Inv n C → Lower m r C →
      (∀ q' < q, m ≤ (C.iterate m r q').2.maxStratumWeight r) →
      Inv n (C.iterate m r q).2 ∧ Lower m r (C.iterate m r q).2 ∧
        (Good m (C.iterate m r q).2 (K (C.iterate m r q).2) → Good m C (stepPhase m r K q C))
  | 0, X, C, h, hl, _ => ⟨h, hl, id⟩
  | q + 1, X, C, h, hl, hq => by
    have hmr : m ≤ C.maxStratumWeight r := hq 0 (Nat.succ_pos _)
    have IH := good_stepPhase hr hm K q (C.step m r) (inv_step h hr hm hmr)
      (lower_step h hm hmr hl) fun q' hq' => hq (q' + 1) (by omega)
    exact ⟨IH.1, IH.2.1, fun hK => good_cons h hr hm hmr (IH.2.2 hK)⟩

/-- At the end, `maxord I_{E,A} < m`. -/
private theorem good_nil {n m : ℕ} (hm : 1 ≤ m) {X : Scheme.{u}} {C : MonomialData X}
    (h : Inv n C) (hl : Lower m (n + 1) C) : Good m C (.nil X) := by
  refine ⟨isTriple_of_inv h, ?_⟩
  simp only [ClosedBlowupSequence.markedTransform]
  have hpt : ∀ x : X, multAt C.monomialIdeal x ≤ ((m - 1 : ℕ) : ℕ∞) := by
    intro x
    refine (multAt_monomialIdeal_le C h.1 x).trans ?_
    have hJ := card_throughIndex_le C h.1 x
    have hd := h.2.2.2
    rcases Nat.eq_zero_or_pos (throughIndex C x).card with h0 | h0
    · rw [Finset.card_eq_zero.1 h0]; simp [MonomialData.stratumWeight]
    · have hx : x ∈ C.stratum (throughIndex C x) := by
        simp [MonomialData.stratum, throughIndex]
      have h1 := stratumWeight_le_maxStratumWeight C h.1.2.2.2.2.1 rfl hx
      have h2 := hl _ h0 (by omega)
      exact_mod_cast (by omega : C.stratumWeight (throughIndex C x) x ≤ m - 1)
  unfold maxOrder maxOrderAlong
  refine lt_of_le_of_lt (iSup₂_le fun x _ => hpt x) ?_
  exact_mod_cast (by omega : m - 1 < m)

/-- The concatenation of the Step-3.`r`, …, Step-3.`n` sequences is good. -/
private theorem good_from {n m : ℕ} (hm : 1 ≤ m) :
    ∀ (j r : ℕ) {X : Scheme.{u}} (C : MonomialData X), Inv n C → 1 ≤ r → Lower m r C →
      r + j = n + 1 → Good m C (monomialOrderReductionFrom m j r C)
  | 0, r, X, C, h, _, hl, hrj => by
    obtain rfl : r = n + 1 := by omega
    exact good_nil hm h hl
  | j + 1, r, X, C, h, hr, hl, hrj => by
    have hex : ∃ N, (C.iterate m r N).2.maxStratumWeight r < m := by
      rcases Nat.lt_or_ge r 2 with hr2 | hr2
      · obtain rfl : r = 1 := by omega
        exact exists_maxStratumWeight_iterate_one_lt C h.1 h.2.1 hm
      · obtain ⟨N, hN⟩ := exists_maxStratumWeight_iterate_lt C h.1 h.2.1 hr2 hm hl
        exact ⟨N, hN r hr le_rfl⟩
    simp only [monomialOrderReductionFrom, dif_pos hex]
    obtain ⟨hinv, hlow, himp⟩ := good_stepPhase hr hm
      (fun D => monomialOrderReductionFrom m j (r + 1) D) (Nat.find hex) C h hl
      fun q' hq' => not_lt.1 (Nat.find_min hex hq')
    refine himp (good_from hm j (r + 1) _ hinv (by omega) ?_ (by omega))
    intro t ht1 htr
    rcases Nat.lt_or_ge t r with htr' | htr'
    · exact hlow t ht1 htr'
    · obtain rfl : t = r := by omega
      exact Nat.find_spec hex

/-- **Monomial order reduction** (Kollár 3.111, end of Step 3.`n`). For monomial data
`C = (X, E, A)` on an equidimensional `X` over a field of characteristic zero and `1 ≤ m`, the
monomial order reduction sequence `C.monomialOrderReduction m` is a smooth blow-up sequence of
order `≥ m` starting with the marked triple `(X, I_{E,A}, m, E)`, and the last ideal of the
iterated birational transform of `(I_{E,A}, m)` along it has maximal order `< m`. -/
@[mmp "lem_kr3e_monomial_order_reduction_result"]
public theorem isOrderGeMarkedTripleSeq_monomialOrderReduction {X : Scheme.{u}}
    (C : MonomialData X) (hC : C.IsMonomialData) (hk : CharZero C.k)
    (hX : Equidimensional X) {m : ℕ} (hm : 1 ≤ m) :
    (C.monomialOrderReduction m).IsOrderGeMarkedTripleSeq C.sX ⟨C.monomialIdeal, m⟩ C.E ∧
      maxOrder ((C.monomialOrderReduction m).markedTransform ⟨C.monomialIdeal, m⟩).I <
        (m : ℕ∞) :=
  good_from (n := dimNat X) hm (dimNat X) 1 C ⟨hC, hk, hX, le_rfl⟩ le_rfl
    (fun _ _ _ => by omega) (by omega)

end MonomialData

end MMP.Resolution
