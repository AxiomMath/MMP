module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.WeightedMonomials

/-!
# Cosupports of marked ideals and maximal coefficient ideals (Kollár 3.59, 3.98)

Elementary properties of the cosupport `cosupp(I, m) = {x : ord_x I ≥ m}` of a marked ideal
(`MMP.Resolution.MarkedIdeal.cosupport`, Kollár Def. 3.59) and of the maximal coefficient ideals
`W_s(I)` (`MMP.Resolution.maximalCoefficientIdeal`, Kollár Def. 3.98).

## Main statements

* `MMP.Resolution.Kollar.cosupport_subset_of_le`: `I ⊆ J ⇒ cosupp(I, m) ⊇ cosupp(J, m)`.
* `MMP.Resolution.Kollar.cosupport_add`: `cosupp(I₁ + I₂, m) = cosupp(I₁, m) ∩ cosupp(I₂, m)`.
* `MMP.Resolution.Kollar.higherDerivativeIdeal_higherDerivativeIdeal`: `D^r(D^s(I)) = D^{r+s}(I)`.
* `MMP.Resolution.Kollar.maximalCoefficientIdeal_succ_le`: `W_{s+1}(I) ⊆ W_s(I)`.
* `MMP.Resolution.Kollar.maximalCoefficientIdeal_mul_le`: `W_s(I) · W_t(I) ⊆ W_{s+t}(I)`.
* `MMP.Resolution.Kollar.maximalCoefficientIdeal_le_mul_of_forall_exists_split`:
  `W_{s+t}(I) ⊆ W_s(I) · W_t(I)` when every exponent vector of weight `≥ s + t` splits into ones
  of weights `≥ s` and `≥ t`.
* `MMP.Resolution.Kollar.maximalCoefficientIdeal_mul_eq`: `W_s(I) · W_t(I) = W_{s+t}(I)` when
  `s = rL` and `t ≥ (m - 1)L`, `L = lcm(2, …, m)`, `m = maxord I ≥ 1` (Kollár 3.99(6)).
* `MMP.Resolution.Kollar.le_divisorialPart`: an effective divisor `D'` with `I ⊆ 𝒪_X(-D')`
  satisfies `D' ≤ Div(I)` (Kollár Def. 3.48).

## Implementation notes

The source states these for a smooth scheme `X` (and `maxord I ≥ 1` for `W_s`); the proofs only
use the definitions, so those hypotheses are dropped. For `le_divisorialPart` the smooth scheme
of the source is replaced by a noetherian one, and "`I` is nonzero on every irreducible component
of `X`" is read as "`cosupp I` contains no irreducible component of `X`", which is the same
condition on a reduced scheme.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP.Resolution.Kollar

section Cosupport

section Order

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem natCast_le_idealOrder_iff (I : Ideal R) (m : ℕ) :
    (m : ℕ∞) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ m :=
  ⟨le_pow_of_le_idealOrder, fun h => le_iSup₂_of_le m h le_rfl⟩

end Order

variable {X : Scheme.{u}}

private theorem exists_affineOpen_mem (x : X) : ∃ U : X.affineOpens, x ∈ U.1 :=
  let ⟨W, hW, hx, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  ⟨⟨W, hW⟩, hx⟩

private theorem stalk_mono {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    IdealSheafData.stalk I x ≤ IdealSheafData.stalk J x := by
  obtain ⟨U, hx⟩ := exists_affineOpen_mem x
  rw [IdealSheafData.stalk_eq_map_germ I x U hx, IdealSheafData.stalk_eq_map_germ J x U hx]
  exact Ideal.map_mono (h U)

private theorem stalk_add (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I + J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨U, hx⟩ := exists_affineOpen_mem x
  rw [IdealSheafData.stalk_eq_map_germ _ x U hx, IdealSheafData.stalk_eq_map_germ I x U hx,
    IdealSheafData.stalk_eq_map_germ J x U hx,
    show (I + J).ideal U = I.ideal U ⊔ J.ideal U from rfl, Ideal.map_sup]

/-- **Kollár, Def. 3.59** (cosupport is antitone). Let `X` be a scheme, `I ⊆ J ⊆ 𝒪_X` ideal sheaves
and `m ∈ ℕ`. Then `cosupp(I, m) ⊇ cosupp(J, m)`. -/
@[mmp "lem_kr3c_marked_cosupport_antitone"]
theorem cosupport_subset_of_le {I J : X.IdealSheafData} (h : I ≤ J) (m : ℕ) :
    (⟨J, m⟩ : MarkedIdeal X).cosupport ⊆ (⟨I, m⟩ : MarkedIdeal X).cosupport := by
  intro x hx
  simp only [MarkedIdeal.cosupport, multAt, Set.mem_ofPred_eq,
    natCast_le_idealOrder_iff] at hx ⊢
  exact (stalk_mono h x).trans hx

/-- **Kollár, Def. 3.59** (cosupport of a sum). Let `X` be a scheme, `I₁, I₂ ⊆ 𝒪_X` ideal sheaves
and `m ∈ ℕ`. Then `cosupp(I₁ + I₂, m) = cosupp(I₁, m) ∩ cosupp(I₂, m)`. -/
@[mmp "lem_kr3c_marked_cosupport_sum"]
theorem cosupport_add (I₁ I₂ : X.IdealSheafData) (m : ℕ) :
    (⟨I₁ + I₂, m⟩ : MarkedIdeal X).cosupport =
      (⟨I₁, m⟩ : MarkedIdeal X).cosupport ∩ (⟨I₂, m⟩ : MarkedIdeal X).cosupport := by
  ext x
  simp only [MarkedIdeal.cosupport, multAt, Set.mem_inter_iff, Set.mem_ofPred_eq,
    natCast_le_idealOrder_iff]
  rw [stalk_add, sup_le_iff]

end Cosupport

section Coefficient

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- Multiplication of ideal sheaves distributes over arbitrary suprema on the left. -/
theorem iSup_mul_idealSheaf {ι : Sort*} (a : ι → X.IdealSheafData) (b : X.IdealSheafData) :
    (⨆ i, a i) * b = ⨆ i, a i * b := by
  rw [← iSup_plift_down, ← iSup_plift_down (f := fun i => a i * b)]
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_iSup, Pi.mul_apply,
    iSup_apply]
  exact Submodule.iSup_mul _ _

/-- Multiplication of ideal sheaves distributes over arbitrary suprema on the right. -/
theorem mul_iSup_idealSheaf {ι : Sort*} (a : X.IdealSheafData) (b : ι → X.IdealSheafData) :
    a * (⨆ i, b i) = ⨆ i, a * b i := by
  rw [mul_comm, iSup_mul_idealSheaf]
  simp_rw [mul_comm]

/-- **Kollár (3.73.2)** (composition of higher derivatives). Let `X` be a scheme over `k` and `I`
an ideal sheaf. Then `D^r(D^s(I)) = D^{r+s}(I)` for all `r, s ≥ 0`. (Kollár assumes `X` smooth;
the identity holds for any `X`, since `D^r` is the `r`-fold iterate of `D`.) -/
@[mmp "lem_kr3d_higher_derivative_composition"]
theorem higherDerivativeIdeal_higherDerivativeIdeal (I : X.IdealSheafData) (r s : ℕ) :
    higherDerivativeIdeal sX (higherDerivativeIdeal sX I s) r =
      higherDerivativeIdeal sX I (r + s) :=
  (Function.iterate_add_apply _ r s I).symm

/-- **Kollár, Def. 3.98** (the maximal coefficient ideals decrease). For every `s ∈ ℤ`,
`W_{s+1}(I) ⊆ W_s(I)`. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_antitone"]
theorem maximalCoefficientIdeal_succ_le (I : X.IdealSheafData) (s : ℤ) :
    maximalCoefficientIdeal sX I (s + 1) ≤ maximalCoefficientIdeal sX I s := by
  unfold maximalCoefficientIdeal
  exact iSup_mono fun _ => iSup_mono' fun _ => ⟨by omega, le_rfl⟩

/-- **Kollár, Def. 3.98** (the maximal coefficient ideals are multiplicative). For all
`s, t ∈ ℤ`, `W_s(I) · W_t(I) ⊆ W_{s+t}(I)`. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_mul_le"]
theorem maximalCoefficientIdeal_mul_le (I : X.IdealSheafData) (s t : ℤ) :
    maximalCoefficientIdeal sX I s * maximalCoefficientIdeal sX I t ≤
      maximalCoefficientIdeal sX I (s + t) := by
  unfold maximalCoefficientIdeal
  simp only [iSup_mul_idealSheaf, mul_iSup_idealSheaf]
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun c' => iSup_le fun hc' => ?_
  refine le_iSup_of_le (c + c') (le_iSup_of_le ?_ (le_of_eq ?_))
  · unfold coefficientWeight at hc hc' ⊢
    push_cast at hc hc' ⊢
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Nat.cast_add]
    omega
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun _ _ => by rw [Pi.add_apply, pow_add, mul_comm]

/-- The weight of `c ∈ ℕ^{m+1}` as a sum over the positive-weight indices `j = m - 1 - i`. -/
theorem coefficientWeight_eq_sum_rev (m : ℕ) (c : Fin (m + 1) → ℕ) :
    coefficientWeight m c = ∑ i : Fin m, c i.rev.castSucc * monomialWeight m i := by
  unfold coefficientWeight
  rw [Fin.sum_univ_castSucc, Fin.val_last, Nat.sub_self, zero_mul, add_zero,
    ← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.val_castSucc, Fin.val_rev, monomialWeight]
  rw [mul_comm]
  congr 1
  omega

/-- The weight of exponent vectors is additive. -/
theorem coefficientWeight_add (m : ℕ) (c₁ c₂ : Fin (m + 1) → ℕ) :
    coefficientWeight m (c₁ + c₂) = coefficientWeight m c₁ + coefficientWeight m c₂ := by
  simp [coefficientWeight, mul_add, Finset.sum_add_distrib]

/-- If every exponent vector of weight at least `s + t` splits as a sum of one of weight at
least `s` and one of weight at least `t`, then `W_{s+t}(I) ⊆ W_s(I) · W_t(I)`. -/
theorem maximalCoefficientIdeal_le_mul_of_forall_exists_split (I : X.IdealSheafData) (s t : ℤ)
    (h : ∀ c : Fin ((maxOrder I).toNat + 1) → ℕ, s + t ≤ coefficientWeight _ c →
      ∃ c₁ c₂, c = c₁ + c₂ ∧ s ≤ coefficientWeight _ c₁ ∧ t ≤ coefficientWeight _ c₂) :
    maximalCoefficientIdeal sX I (s + t) ≤
      maximalCoefficientIdeal sX I s * maximalCoefficientIdeal sX I t :=
  iSup₂_le fun c hc => by
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := h c hc
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    exact mul_le_mul' (le_iSup₂_of_le c₁ h₁ le_rfl) (le_iSup₂_of_le c₂ h₂ le_rfl)

/-- **Kollár, Prop. 3.99(6)**. Let `I` be an ideal sheaf with `m = maxord I ≥ 1` and
`L = lcm(2, …, m)`. If `s = rL` for an integer `r ≥ 0` and `t ≥ (m - 1)L`, then
`W_s(I) · W_t(I) = W_{s+t}(I)`. (Kollár assumes `X` smooth; no smoothness hypothesis is
needed here.) -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_mul_eq"]
theorem maximalCoefficientIdeal_mul_eq (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat)
    (r : ℕ) (t : ℤ) (ht : ((maxOrder I).toNat - 1 : ℤ) * lcmUpTo (maxOrder I).toNat ≤ t) :
    maximalCoefficientIdeal sX I ((r * lcmUpTo (maxOrder I).toNat : ℕ) : ℤ) *
        maximalCoefficientIdeal sX I t =
      maximalCoefficientIdeal sX I ((r * lcmUpTo (maxOrder I).toNat : ℕ) + t) := by
  refine le_antisymm (maximalCoefficientIdeal_mul_le sX I _ t)
    (maximalCoefficientIdeal_le_mul_of_forall_exists_split sX I _ t ?_)
  set m := (maxOrder I).toNat
  set L := lcmUpTo m
  intro c hc
  let U : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => c i.rev.castSucc
  have hwU : Finsupp.weight (monomialWeight m) U = coefficientWeight m c := by
    rw [coefficientWeight_eq_sum_rev, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [U, smul_eq_mul]
  obtain ⟨U₁, U₂, hU, hU₁⟩ := exists_weighted_monomial_split m hm r U (by
    have h1 : ((r + m - 1) * L : ℕ) = ((r * L : ℕ) : ℤ) + ((m : ℤ) - 1) * L := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      ring
    have : (((r + m - 1) * L : ℕ) : ℤ) ≤ (Finsupp.weight (monomialWeight m) U : ℤ) := by
      rw [h1, hwU]
      omega
    exact_mod_cast this)
  let c₁ : Fin (m + 1) → ℕ := Fin.snoc (α := fun _ => ℕ) (fun i => U₁ i.rev) 0
  let c₂ : Fin (m + 1) → ℕ := Fin.snoc (α := fun _ => ℕ) (fun i => U₂ i.rev) (c (Fin.last m))
  have hcc : c = c₁ + c₂ := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [c₁, c₂]
    | cast i =>
      have := congrArg (fun f : Fin m →₀ ℕ => f i.rev) hU
      simp only [Finsupp.coe_add, Pi.add_apply, U, Finsupp.equivFunOnFinite_symm_apply_apply,
        Fin.rev_rev] at this
      simpa [c₁, c₂] using this
  have hw₁ : coefficientWeight m c₁ = r * L := by
    rw [coefficientWeight_eq_sum_rev, ← hU₁, Finsupp.weight_apply,
      Finsupp.sum_fintype _ _ (by simp)]
    simp [c₁, smul_eq_mul]
  rw [hcc, coefficientWeight_add, hw₁] at hc
  exact ⟨c₁, c₂, hcc, by rw [hw₁], by push_cast at hc; omega⟩

end Coefficient

section DivisorialPart

variable {X : Scheme.{u}}

/-- If `I ⊆ ∏ᶠ_E I_E^{n_E}` for a finitely supported `n`, then `I_x ⊆ (I_{D,x})^{n_D}` at every
point `x`, for every prime divisor `D`. -/
private theorem stalk_le_stalk_pow_of_le_finprod {I : X.IdealSheafData} {D' : MMP.Mori.Divisor X}
    (hI : I ≤ ∏ᶠ E : AlgebraicGeometry.PrimeDivisor X, E.idealSheaf ^ (D' E).toNat)
    (D : AlgebraicGeometry.PrimeDivisor X) (x : X) :
    IdealSheafData.stalk I x ≤ IdealSheafData.stalk D.idealSheaf x ^ (D' D).toNat := by
  classical
  have hsub : (Function.mulSupport fun E : AlgebraicGeometry.PrimeDivisor X =>
      E.idealSheaf ^ (D' E).toNat) ⊆ (D'.support : Set _) := by
    intro E hE
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hE
    simp [h0]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hI
  refine (stalk_mono hI x).trans ?_
  rw [stalk_prod]
  by_cases hD : D ∈ D'.support
  · exact Ideal.prod_le_inf.trans ((Finset.inf_le hD).trans (IdealSheafData.stalk_pow _ _ _).le)
  · rw [Finsupp.notMem_support_iff.mp hD, Int.toNat_zero, pow_zero, Ideal.one_eq_top]
    exact le_top

private theorem isIrreducible_support (D : AlgebraicGeometry.PrimeDivisor X) :
    IsIrreducible D.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isIrreducible_singleton.closure

private theorem genericPoint_mem_support (D : AlgebraicGeometry.PrimeDivisor X) :
    D.genericPoint ∈ D.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- If `I_x ⊆ (I_{D,x})^a` at every point for some `a ≠ 0`, then the support of `D` lies in
the cosupport of `I`. -/
theorem support_subset_of_stalk_le_pow {I : X.IdealSheafData}
    (D : AlgebraicGeometry.PrimeDivisor X) {a : ℕ} (ha : a ≠ 0)
    (hst : ∀ x, IdealSheafData.stalk I x ≤ IdealSheafData.stalk D.idealSheaf x ^ a) :
    D.support ⊆ (I.support : Set X) := by
  intro x hx
  by_contra hxI
  have h1 := (IdealSheafData.stalk_eq_top_iff_notMem_support I x).2 hxI
  have h2 := (IdealSheafData.stalk_eq_top_iff_notMem_support D.idealSheaf x).not.2
    (not_not.2 hx)
  exact h2 (top_le_iff.mp (h1 ▸ (hst x).trans (Ideal.pow_le_self ha)))

/-- A prime divisor contained in `cosupp I` is an irreducible component of `cosupp I`, when
`cosupp I` contains no irreducible component of `X`. -/
theorem support_mem_componentsOf {I : X.IdealSheafData}
    (hI : ∀ T ∈ irreducibleComponents X, ¬ T ⊆ (I.support : Set X))
    (D : AlgebraicGeometry.PrimeDivisor X) (hsupp : D.support ⊆ (I.support : Set X)) :
    (D.support : Set X) ∈ componentsOf (I.support : Set X) := by
  refine ⟨⟨isIrreducible_support D, hsupp⟩, fun W ⟨hW, hWI⟩ hDW => ?_⟩
  by_contra hWD
  let C : TopologicalSpace.IrreducibleCloseds X := ⟨closure W, hW.closure, isClosed_closure⟩
  have hCI : closure W ⊆ (I.support : Set X) := I.support.isClosed.closure_subset_iff.mpr hWI
  obtain ⟨T, hT, hCT⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ hW.closure
  let T' : TopologicalSpace.IrreducibleCloseds X :=
    ⟨T, hT.1, isClosed_of_mem_irreducibleComponents T hT⟩
  have hCT' : C < T' := by
    refine lt_of_le_of_ne hCT fun h => hI T hT ?_
    have : (C : Set X) = T := congrArg SetLike.coe h
    exact this ▸ hCI
  have hYC : TopologicalSpace.IrreducibleCloseds.closureSingleton D.genericPoint < C := by
    have hY : (TopologicalSpace.IrreducibleCloseds.closureSingleton D.genericPoint : Set X) =
        D.support := by
      rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine lt_of_le_of_ne ?_ fun h => hWD ?_
    · change (TopologicalSpace.IrreducibleCloseds.closureSingleton D.genericPoint : Set X) ⊆
        closure W
      rw [hY]
      exact hDW.trans subset_closure
    · have : D.support = closure W := hY.symm.trans (congrArg SetLike.coe h)
      exact subset_closure.trans this.symm.subset
  have hY1 : Order.coheight
      (TopologicalSpace.IrreducibleCloseds.closureSingleton D.genericPoint) = 1 :=
    D.codimension_closureSingleton_genericPoint
  have h1 := Order.coheight_add_one_le hYC
  have hC0 : Order.coheight C ≠ 0 := fun h => (Order.coheight_eq_zero.mp h).not_lt hCT'
  rw [hY1] at h1
  generalize Order.coheight C = c at h1 hC0
  cases c with
  | top => simp at h1
  | coe n =>
    norm_cast at h1 hC0
    omega

/-- On a noetherian scheme, if `cosupp I` contains no irreducible component of `X`, then `I` has
finite order at the generic point of every prime divisor. -/
theorem multAt_genericPoint_ne_top [IsNoetherian X] {I : X.IdealSheafData}
    (hI : ∀ T ∈ irreducibleComponents X, ¬ T ⊆ (I.support : Set X))
    (D : AlgebraicGeometry.PrimeDivisor X) : multAt I D.genericPoint ≠ ⊤ := by
  intro htop
  have hbot : IdealSheafData.stalk I D.genericPoint = ⊥ := by
    have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal _)
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
    exact le_iInf fun n => le_pow_of_le_idealOrder
      (show (n : ℕ∞) ≤ multAt I D.genericPoint from htop ▸ le_top)
  obtain ⟨T, hT, hDT⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_support D)
  have hTirr := hT.1
  have hgen : IsGenericPoint hTirr.genericPoint T := by
    have := hTirr.isGenericPoint_genericPoint_closure
    rwa [(isClosed_of_mem_irreducibleComponents T hT).closure_eq] at this
  have hξη : hTirr.genericPoint ⤳ D.genericPoint :=
    hgen.specializes (hDT (genericPoint_mem_support D))
  have hξ : hTirr.genericPoint ∈ (I.support : Set X) := by
    by_contra hξ
    have h := (IdealSheafData.stalk_eq_top_iff_notMem_support I _).2 hξ
    rw [Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hξη, hbot, Ideal.map_bot] at h
    exact bot_ne_top h
  refine hI T hT ?_
  rw [← hgen.def]
  exact I.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξ)

/-- **Kollár, Def. 3.48** (`Div(I)` is the largest divisor dividing `I`). Let `X` be a noetherian
scheme and `I ⊆ 𝒪_X` an ideal sheaf whose cosupport contains no irreducible component of `X`. If
`D'` is an effective divisor with `I ⊆ 𝒪_X(-D') = ∏_D I_D^{D'(D)}`, then `D' ≤ Div(I)`. -/
@[mmp "lem_kr3c_divisorial_part_largest"]
theorem le_divisorialPart [IsNoetherian X] {I : X.IdealSheafData}
    (hI : ∀ T ∈ irreducibleComponents X, ¬ T ⊆ (I.support : Set X))
    {D' : MMP.Mori.Divisor X} (hD' : 0 ≤ D')
    (hle : I ≤ ∏ᶠ D : AlgebraicGeometry.PrimeDivisor X, D.idealSheaf ^ (D' D).toNat) :
    D' ≤ divisorialPart I := by
  classical
  intro D
  simp only [divisorialPart, finite_support_divisorialPartCoeff I, ↓reduceDIte,
    Finsupp.ofSupportFinite_coe]
  have h0 : 0 ≤ D' D := hD' D
  rcases eq_or_lt_of_le h0 with h | hpos
  · rw [← h]
    unfold divisorialPartCoeff
    split_ifs <;> positivity
  set a := (D' D).toNat
  have hDa : D' D = a := (Int.toNat_of_nonneg h0).symm
  have hst : ∀ x, IdealSheafData.stalk I x ≤ IdealSheafData.stalk D.idealSheaf x ^ a :=
    stalk_le_stalk_pow_of_le_finprod hle D
  have hcomp := support_mem_componentsOf hI D (support_subset_of_stalk_le_pow D (by omega) hst)
  have hne : IdealSheafData.stalk D.idealSheaf D.genericPoint ≠ ⊤ :=
    (IdealSheafData.stalk_eq_top_iff_notMem_support D.idealSheaf _).not.2
      (not_not.2 (genericPoint_mem_support D))
  have hmult : (a : ℕ∞) ≤ multAt I D.genericPoint := by
    rw [multAt, natCast_le_idealOrder_iff]
    exact (hst _).trans (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hne) a)
  simp only [divisorialPartCoeff, hcomp, ↓reduceIte]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (multAt_genericPoint_ne_top hI D)
  rw [hDa, ← hm, ENat.toNat_natCast]
  rw [← hm] at hmult
  exact_mod_cast hmult

end DivisorialPart

end MMP.Resolution.Kollar
