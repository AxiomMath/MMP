module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Cosupport
public import MMP.AlgebraicGeometry.Resolution.OrderRestriction

/-!
# Powers of maximal coefficient ideals and ideals containing a smooth subvariety

Two elementary facts from Kollár's treatment of resolution of singularities.

First, for an ideal sheaf `I` with `m = maxord I ≥ 1` and `L = lcm(2, …, m)`, the maximal
coefficient ideals `W_s(I)` with `s = rL`, `r ≥ m - 1`, satisfy `W_s(I)^j = W_{js}(I)` for every
`j ≥ 1` (Kollár, Prop. 3.99(7)).

Second, if `τ : Y ↪ X` is a closed embedding of smooth schemes such that no irreducible component
of `X` lies in `Y`, and `I ⊆ 𝒪_X` is an ideal sheaf with `𝒪_X / I = τ_*(𝒪_Y / J)` for an ideal
sheaf `J ⊆ 𝒪_Y`, then `maxord I ≤ 1` (Kollár 3.71).

## Main statements

* `MMP.Resolution.Kollar.maximalCoefficientIdeal_pow`: `W_s(I)^j = W_{js}(I)` for `s = rL`,
  `r ≥ m - 1` and `j ≥ 1` (Kollár, Prop. 3.99(7)).
* `MMP.Resolution.Kollar.multAt_antitone`: the order `multAt I x` is antitone in `I`.
* `MMP.Resolution.Kollar.maxOrder_le_one_of_eq_ker`: `maxord I ≤ 1` when `I` is the ideal sheaf
  of a closed subscheme of a smooth closed subscheme `Y ⊆ X` containing no irreducible component
  of `X` (Kollár 3.71).

## Implementation notes

For `maxOrder_le_one_of_eq_ker`, the closed subscheme `Y` is its ideal sheaf
`Y : X.IdealSheafData`, with closed immersion `τ = Y.subschemeι`, and `J` is an ideal sheaf on
`Y.subscheme`. The condition `𝒪_X / I = τ_*(𝒪_Y / J)` says that `I` is the kernel of
`𝒪_X → τ_*(𝒪_Y / J)`, that is, the ideal sheaf of the closed subscheme `J.subscheme` of `X`
embedded by `J.subschemeι ≫ Y.subschemeι`; it is encoded as
`I = (J.subschemeι ≫ Y.subschemeι).ker`. Smoothness of `X` and `Y` is used only through the
regularity of their local rings, which is assumed instead. Coherence of `I` and `J` is not used.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.Resolution.Kollar

section Pow

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **Kollár, Prop. 3.99(7)**. Let `I` be an ideal sheaf with `m = maxord I ≥ 1` and
`L = lcm(2, …, m)`. If `s = rL` for an integer `r ≥ m - 1`, `r ≥ 0`, then
`W_s(I)^j = W_{js}(I)` for every integer `j ≥ 1`. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_pow"]
theorem maximalCoefficientIdeal_pow (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat)
    (r : ℕ) (hr : (maxOrder I).toNat - 1 ≤ r) {j : ℕ} (hj : 1 ≤ j) :
    maximalCoefficientIdeal sX I ((r * lcmUpTo (maxOrder I).toNat : ℕ) : ℤ) ^ j =
      maximalCoefficientIdeal sX I (j * ((r * lcmUpTo (maxOrder I).toNat : ℕ) : ℤ)) := by
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [pow_succ, ih, mul_comm, maximalCoefficientIdeal_mul_eq sX I hm r]
    · congr 1
      push_cast
      ring
    · have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
      have hr' : ((maxOrder I).toNat - 1 : ℤ) ≤ r := by omega
      have hL : (0 : ℤ) ≤ lcmUpTo (maxOrder I).toNat := by positivity
      have hrL : (0 : ℤ) ≤ r * lcmUpTo (maxOrder I).toNat := by positivity
      push_cast
      nlinarith

end Pow

section OrderLeOne

variable {X : Scheme.{u}}

private theorem exists_affineOpen_mem (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU⟩

/-- The stalk of an ideal sheaf is monotone in the ideal sheaf. -/
theorem stalk_mono {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    IdealSheafData.stalk I x ≤ IdealSheafData.stalk J x := by
  obtain ⟨U, hx⟩ := exists_affineOpen_mem x
  rw [IdealSheafData.stalk_eq_map_germ I x U hx, IdealSheafData.stalk_eq_map_germ J x U hx]
  exact Ideal.map_mono (h U)

/-- The order of an ideal sheaf at a point is antitone in the ideal sheaf: a larger ideal sheaf
has smaller order. -/
theorem multAt_antitone {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    multAt J x ≤ multAt I x := by
  unfold multAt idealOrder
  exact iSup₂_mono' fun j hj => ⟨j, (stalk_mono h x).trans hj, le_rfl⟩

/-- Outside the support of an ideal sheaf, its stalk is the unit ideal. -/
private theorem stalk_eq_top_of_notMem_support {I : X.IdealSheafData} {x : X}
    (hx : x ∉ I.support) : IdealSheafData.stalk I x = ⊤ := by
  obtain ⟨U, hxU⟩ := exists_affineOpen_mem x
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, Scheme.mem_zeroLocus_iff] at hx
  push Not at hx
  obtain ⟨f, hf, hxf⟩ := hx
  rw [Scheme.mem_basicOpen _ _ _ hxU] at hxf
  rw [IdealSheafData.stalk_eq_map_germ I x U hxU]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf) hxf

/-- A zero stalk stays zero under generization. -/
private theorem stalk_eq_bot_of_specializes {I : X.IdealSheafData} {x y : X} (h : y ⤳ x)
    (hx : IdealSheafData.stalk I x = ⊥) : IdealSheafData.stalk I y = ⊥ := by
  obtain ⟨U, hxU⟩ := exists_affineOpen_mem x
  have hyU : y ∈ U.1 := h.mem_open U.1.isOpen hxU
  rw [IdealSheafData.stalk_eq_map_germ I x U hxU] at hx
  rw [IdealSheafData.stalk_eq_map_germ I y U hyU,
    ← X.presheaf.germ_stalkSpecializes hxU h, CommRingCat.hom_comp, ← Ideal.map_map, hx,
    Ideal.map_bot]

private theorem withBot_lt_of_add_one_le {d1 d2 d : WithBot ℕ∞} (h1 : d2 + 1 ≤ d)
    (h2 : d1 ≤ d2) (hfin : d < ⊤) (hb : d ≠ ⊥) : d1 < d := by
  refine h2.trans_lt ?_
  induction d2 using WithBot.recBotCoe with
  | bot => exact bot_lt_iff_ne_bot.mpr hb
  | coe e =>
    induction d using WithBot.recBotCoe with
    | bot => exact absurd rfl hb
    | coe f =>
      have hf : f < ⊤ := WithBot.coe_lt_coe.mp hfin
      have : e + 1 ≤ f := by exact_mod_cast h1
      exact WithBot.coe_lt_coe.mpr
        ((ENat.add_one_le_iff (ne_top_of_le_ne_top hf.ne (le_self_add.trans this))).mp this)

/-- **Kollár 3.71**. Let `τ : Y ↪ X` be a closed embedding of smooth schemes such that no
irreducible component of `X` is contained in `Y`, and `J ⊆ 𝒪_Y`, `I ⊆ 𝒪_X` ideal sheaves with
`𝒪_X / I = τ_*(𝒪_Y / J)`. Then `maxord I ≤ 1`.

Here `Y` is a closed subscheme of `X`, `τ = Y.subschemeι`, and `𝒪_X / I = τ_*(𝒪_Y / J)` is
`I = (J.subschemeι ≫ Y.subschemeι).ker`; smoothness is used only through the regularity of the
local rings of `X` and `Y`, which is assumed instead. -/
@[mmp "lem_kr3c_order_ideal_containing_smooth_subvariety_le_one"]
theorem maxOrder_le_one_of_eq_ker (Y : X.IdealSheafData) (J : Y.subscheme.IdealSheafData)
    (I : X.IdealSheafData) [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)]
    [∀ y : Y.subscheme, IsRegularLocalRing (Y.subscheme.presheaf.stalk y)]
    (hY : ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ (Y.support : Set X))
    (hI : I = (J.subschemeι ≫ Y.subschemeι).ker) :
    maxOrder I ≤ 1 := by
  have hYI : Y ≤ I := by
    rw [hI]
    exact (Scheme.IdealSheafData.ker_subschemeι Y).symm.le.trans (Scheme.Hom.le_ker_comp _ _)
  refine iSup₂_le fun x _ => (multAt_antitone hYI x).trans ?_
  by_cases hx : x ∈ Y.support
  · have hx' : x ∈ Set.range Y.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    obtain ⟨y, rfl⟩ := hx'
    refine (multAt_eq_one_of_finrank_cotangentSpace_lt Y y ?_).le
    set A := X.presheaf.stalk (Y.subschemeι y)
    set Jx := IdealSheafData.stalk Y (Y.subschemeι y)
    have hdom : IsDomain A := IsRegularLocalRing.isDomain A
    have hJ : Jx ≠ ⊥ := by
      intro hJ
      obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
        {Y.subschemeι y} isIrreducible_singleton
      have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
      have hgen := (hZ.1).isGenericPoint_genericPoint_closure
      rw [hZc.closure_eq] at hgen
      have hsp : hZ.1.genericPoint ⤳ Y.subschemeι y :=
        hgen.specializes (hxZ rfl)
      have hη : IdealSheafData.stalk Y hZ.1.genericPoint = ⊥ :=
        stalk_eq_bot_of_specializes hsp hJ
      have hηY : hZ.1.genericPoint ∈ Y.support := by
        by_contra hn
        have := stalk_eq_top_of_notMem_support hn
        rw [hη] at this
        exact bot_ne_top this
      refine hY Z hZ ?_
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηY) Y.support.isClosed
    obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    have hareg : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha0
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hareg
    have h2 : ringKrullDim (A ⧸ Jx) ≤ ringKrullDim (A ⧸ Ideal.span {a}) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor
        ((Ideal.span_singleton_le_iff_mem _).mpr haJ)) (Ideal.Quotient.factor_surjective _)
    have h3 : ringKrullDim (A ⧸ Jx) = ringKrullDim (Y.subscheme.presheaf.stalk y) :=
      ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv Y y)
    have hnB : IsNoetherianRing (Y.subscheme.presheaf.stalk y) :=
      IsRegularLocalRing.toIsNoetherian
    have hnA : IsNoetherianRing A := IsRegularLocalRing.toIsNoetherian
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace
      (Y.subscheme.presheaf.stalk y)).mp inferInstance
    rw [hreg, ← h3]
    exact withBot_lt_of_add_one_le h1 h2 ringKrullDim_lt_top ringKrullDim_ne_bot
  · rw [multAt, stalk_eq_top_of_notMem_support hx]
    refine iSup₂_le fun j hj => ?_
    by_contra hj1
    have h2 : 1 ≤ j := by
      by_contra h0
      exact hj1 (by simp [show j = 0 by omega])
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (top_le_iff.mp (hj.trans (Ideal.pow_le_self (by omega))))

end OrderLeOne

end MMP.Resolution.Kollar
