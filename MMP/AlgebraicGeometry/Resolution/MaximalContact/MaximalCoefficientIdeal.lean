module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Cosupport
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Functor
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientPowers
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialStepTermination
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform
import MMP.AlgebraicGeometry.Resolution.MaximalContact.AlongBlowupSequence
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MaxOrderControlledTransform
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealOrder
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DBalancedLogDerivative
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Resolution.Blowup.HypersurfaceTransform
import MMP.RingTheory.RegularLocalRing.CompletionStrictHenselization

/-!
# Maximal coefficient ideals and the order-reduction functors

Let `X` be smooth and equidimensional of dimension at least one over a field `k` of
characteristic zero, and `I` an ideal sheaf with `m = maxord I ≥ 1`. The maximal coefficient
ideals `W_s(I)` satisfy:

* `maxord W_s(I) = s` for `s ≥ 1`, and `MC(W_s(I)) = W_1(I)`;
* `W_s(I)` is MC-invariant, and `W_{m!}(I)` is D-balanced (Aside 3.99.10);
* `W_s` commutes with smooth pull-back with the same maximal order, and with change of the
  ground field (3.102(2), 3.103(2)).

These feed the order-reduction functors. The input `(S, W_0𝒪_S, m!, E_S)` that `bdFunctor`
hands to the marked family is a marked triple of dimension `n - 1`, and the global functor
`boFunctor` ignores empty entries of the divisor (3.72). Finally the birational transform of an
MC-hypersurface along a smooth blow-up sequence of order `m` is again an MC-hypersurface, as long
as the maximal order stays `m` (Lemma 3.103, Step 2).

## Main results

* `MMP.Resolution.Kollar.maxOrder_maximalCoefficientIdeal`
* `MMP.Resolution.Kollar.maximalContactIdeal_maximalCoefficientIdeal`
* `MMP.Resolution.Kollar.isDBalanced_maximalCoefficientIdeal_factorial`
* `MMP.Resolution.Kollar.isMCInvariant_maximalCoefficientIdeal`
* `MMP.Resolution.Kollar.maximalCoefficientIdeal_comap_of_smooth`
* `MMP.Resolution.Kollar.maximalCoefficientIdeal_comap_fieldChange`
* `MMP.Resolution.bdFunctor_input_mem_markedTriplesOfDim`
* `MMP.Resolution.ignoresEmptyEntries_boFunctor`
* `MMP.Resolution.ClosedBlowupSequence.IsOrderMTripleSeq.isMCHypersurface_ker_restrictHom`

## Implementation notes

The source works on a smooth variety. All statements here are local on `X`, so `X` only carries
the structure of a triple (smooth, locally of finite type, equidimensional over `k`) and need be
neither irreducible nor separated.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 3.72, 3.98–3.103
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace MMP.Resolution

/-- On an equidimensional space of positive dimension every irreducible component has positive
dimension. -/
private theorem pos_dim_of_equidimensional {Y : Type*} [TopologicalSpace Y]
    (hequi : Equidimensional Y) (hdim : 1 ≤ topologicalKrullDim Y) :
    ∀ Z ∈ irreducibleComponents Y, 0 < topologicalKrullDim Z := by
  intro Z hZ
  by_contra h
  push Not at h
  have := MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents (n := 0)
    fun W hW => (hequi W hW Z hZ).trans_le h
  exact absurd (hdim.trans this) (by decide)

end MMP.Resolution

namespace MMP.Resolution.Kollar

/-- The zero ideal of a local ring has infinite order. -/
private theorem idealOrder_bot {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊥ : Ideal R) = ⊤ :=
  ENat.eq_top_iff_forall_ge.2 fun n =>
    le_iSup₂_of_le (f := fun (j : ℕ) (_ : (⊥ : Ideal R) ≤ _ ^ j) => (j : ℕ∞)) n bot_le le_rfl

private theorem maxOrder_eq_iSup {X : Scheme.{u}} (I : X.IdealSheafData) :
    maxOrder I = ⨆ x, multAt I x := by
  rw [maxOrder, maxOrderAlong, iSup_univ]

private theorem multAt_le_maxOrder {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    multAt I x ≤ maxOrder I :=
  (le_iSup (multAt I) x).trans_eq (maxOrder_eq_iSup I).symm

/-- A finite positive maximal order is the order at some point. -/
private theorem exists_multAt_eq_maxOrder {X : Scheme.{u}} {I : X.IdealSheafData} {m : ℕ}
    (hm : maxOrder I = m) (hm1 : 1 ≤ m) : ∃ x, multAt I x = m := by
  rw [maxOrder_eq_iSup] at hm
  have : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [iSup_of_empty, bot_eq_zero', eq_comm, Nat.cast_eq_zero] at hm
    omega
  exact hm ▸ ENat.exists_eq_iSup_of_lt_top (hm ▸ ENat.natCast_lt_top m)

/-- An ideal sheaf of finite maximal order is nonzero at every generic point. -/
private theorem isNonzeroAtGenericPoints_of_maxOrder_ne_top {X : Scheme.{u}}
    {I : X.IdealSheafData} (h : maxOrder I ≠ ⊤) : IsNonzeroAtGenericPoints I := by
  intro η _ hη
  have := multAt_le_maxOrder I η
  rw [multAt, hη, idealOrder_bot, top_le_iff] at this
  exact h this

/-- **Kollár 3.98–3.99** (the maximal order of `W_s(I)`). Let `X` be a smooth equidimensional
scheme of finite type over a field `k` of characteristic zero with `dim X ≥ 1`, and `I`
an ideal sheaf with `m = maxord I ≥ 1`. Then for every `s ≥ 1`, `maxord W_s(I) = s`. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_max_order"]
public theorem maxOrder_maximalCoefficientIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : Mori.IsSmoothScheme sX)
    [QuasiCompact sX] (hequi : Equidimensional X)
    (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) {s : ℕ} (hs : 1 ≤ s) :
    maxOrder (maximalCoefficientIdeal sX I (s : ℤ)) = s := by
  have : Smooth sX := hX.smooth
  have hne : maxOrder I ≠ ⊤ := by rintro h; simp [h] at hm
  have hmeq : maxOrder I = (maxOrder I).toNat := (ENat.coe_toNat hne).symm
  have key := multAt_maximalCoefficientIdeal sX hequi (pos_dim_of_equidimensional hequi hdim)
    (isNonzeroAtGenericPoints_of_maxOrder_ne_top hne) hm hmeq hs
  obtain ⟨x, hx⟩ := exists_multAt_eq_maxOrder hmeq hm
  refine le_antisymm ((maxOrder_eq_iSup _).trans_le (iSup_le fun y => ?_))
    ((key x).1 hx ▸ multAt_le_maxOrder _ x)
  rcases ((multAt_le_maxOrder I y).trans hmeq.le).lt_or_eq with h | h
  · simp [(key y).2 h]
  · exact ((key y).1 h).le

/-- If the order of `J` shifted by `s - 1` is the order of `I` shifted by `m - 1`, where
`m = maxord I ≥ 1`, then `maxord J = s`. -/
private theorem maxOrder_eq_of_multAt_tsub {X : Scheme.{u}} {I J : X.IdealSheafData} {m s : ℕ}
    (hI : maxOrder I = m) (hm : 1 ≤ m) (hs : 1 ≤ s)
    (h : ∀ x, multAt J x - (s - 1 : ℕ) = multAt I x - (m - 1 : ℕ)) : maxOrder J = s := by
  obtain ⟨x₀, hx₀⟩ := exists_multAt_eq_maxOrder hI hm
  rw [maxOrder_eq_iSup]
  refine le_antisymm (iSup_le fun x => ?_) ((le_of_eq ?_).trans (le_iSup _ x₀))
  · have hx : multAt I x - (m - 1 : ℕ) ≤ 1 := by
      rw [tsub_le_iff_right]
      exact (multAt_le_maxOrder I x).trans (hI.le.trans (by norm_cast; omega))
    rw [← h, tsub_le_iff_right] at hx
    exact hx.trans (by norm_cast; omega)
  · have hx := h x₀
    rw [hx₀] at hx
    generalize multAt J x₀ = a at hx
    induction a with
    | top =>
      rw [ENat.top_sub_coe, ← ENat.coe_sub] at hx
      exact absurd hx (ENat.top_ne_coe _)
    | coe a => norm_cast at hx ⊢; omega

/-- `D^j(W_{t+j}(I)) = W_t(I)`. -/
private theorem higherDerivativeIdeal_maximalCoefficientIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (hXe : Equidimensional X)
    (hdim : 1 ≤ topologicalKrullDim X) (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat)
    (t j : ℕ) :
    higherDerivativeIdeal sX (maximalCoefficientIdeal sX I ((t + j : ℕ) : ℤ)) j =
      maximalCoefficientIdeal sX I t := by
  induction j generalizing t with
  | zero => simp [higherDerivativeIdeal_zero]
  | succ j ih =>
    have h1 := derivativeIdeal_maximalCoefficientIdeal_succ sX hXe hdim I hm (t + j)
    have e : ((t + (j + 1) : ℕ) : ℤ) = ((t + j : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [higherDerivativeIdeal, Function.iterate_succ_apply, e, h1]
    exact ih t

/-- **Kollár, Prop. 3.99(4)**, first equality. Let `X` be a smooth equidimensional scheme, locally
of finite type over a field `k` of characteristic zero, with `dim X ≥ 1`, and `I` an ideal sheaf
with `m = maxord I ≥ 1`. Then for every `s ≥ 1`, the maximal contact ideal of `W_s(I)` is `W_1(I)`.
-/
@[mmp "lem_kr3e_mc_of_maximal_coefficient_ideal"]
public theorem maximalContactIdeal_maximalCoefficientIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (hXe : Equidimensional X)
    (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) {s : ℕ} (hs : 1 ≤ s) :
    maximalContactIdeal sX (maximalCoefficientIdeal sX I (s : ℤ)) =
      maximalCoefficientIdeal sX I 1 := by
  have hcomp := pos_dim_of_equidimensional hXe hdim
  have hD := higherDerivativeIdeal_maximalCoefficientIdeal sX hXe hdim I hm 1 (s - 1)
  rw [show 1 + (s - 1) = s by omega, Nat.cast_one] at hD
  have hmax : maxOrder (maximalCoefficientIdeal sX I s) = s :=
    maxOrder_eq_of_multAt_tsub (ENat.coe_toNat (by rintro h; simp [h] at hm)).symm hm hs
      fun x => by
        rw [← multAt_higherDerivativeIdeal sX hcomp, hD,
          maximalCoefficientIdeal_one_eq_maximalContactIdeal sX hcomp I hm, maximalContactIdeal,
          multAt_higherDerivativeIdeal sX hcomp]
  rw [maximalContactIdeal, hmax, ENat.toNat_coe]
  exact hD

section Helpers

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `W_0(I) = 𝒪_X`. -/
private theorem maximalCoefficientIdeal_zero (I : X.IdealSheafData) :
    maximalCoefficientIdeal sX I 0 = ⊤ :=
  top_le_iff.mp (le_iSup₂_of_le 0 (by simp) (by
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one]
    exact le_rfl))

/-- `W_a(I)^n ⊆ W_b(I)` whenever `b ≤ na`. -/
private theorem maximalCoefficientIdeal_pow_le (I : X.IdealSheafData) {a b : ℤ} {n : ℕ}
    (h : b ≤ n * a) : maximalCoefficientIdeal sX I a ^ n ≤ maximalCoefficientIdeal sX I b := by
  refine le_trans (b := maximalCoefficientIdeal sX I (n * a)) ?_
    (iSup_mono fun _ => iSup_mono' fun hc => ⟨h.trans hc, le_rfl⟩)
  clear h
  induction n with
  | zero => simp [maximalCoefficientIdeal_zero]
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih le_rfl).trans ((maximalCoefficientIdeal_mul_le sX I _ _).trans ?_)
    exact le_of_eq (by congr 1; push_cast; ring)

/-- The order of the unit ideal sheaf is `0` everywhere. -/
private theorem multAt_top (x : X) : multAt (⊤ : X.IdealSheafData) x = 0 := by
  unfold multAt
  rw [MMP.Resolution.Aux.stalk_top, MMP.Threefold.Resolution.idealOrder_top]

variable [CharZero k] [Smooth sX]

/-- `maxord W_s(I) ≤ s`: `D^s(W_s(I)) = 𝒪_X` has order `0`, and each derivative lowers the order
by exactly one. -/
private theorem maxOrder_maximalCoefficientIdeal_le
    (hequi : Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) (s : ℕ) :
    maxOrder (maximalCoefficientIdeal sX I s) ≤ s := by
  have hD := higherDerivativeIdeal_maximalCoefficientIdeal sX hequi hdim I hm 0 s
  rw [zero_add, Nat.cast_zero, maximalCoefficientIdeal_zero] at hD
  refine iSup₂_le fun x _ => ?_
  have := multAt_higherDerivativeIdeal sX (pos_dim_of_equidimensional hequi hdim)
    (maximalCoefficientIdeal sX I s) s x
  rw [hD, multAt_top] at this
  exact tsub_eq_zero_iff_le.mp this.symm

/-- `W_{m!}(I)^n = W_{n·m!}(I)` for `n ≥ 1`, `m = maxord I ≥ 1`. -/
private theorem maximalCoefficientIdeal_factorial_pow (I : X.IdealSheafData)
    (hm : 1 ≤ (maxOrder I).toNat) {n : ℕ} (hn : 1 ≤ n) :
    maximalCoefficientIdeal sX I ((maxOrder I).toNat.factorial : ℤ) ^ n =
      maximalCoefficientIdeal sX I (n * ((maxOrder I).toNat.factorial : ℤ)) := by
  set m := (maxOrder I).toNat with hmdef
  have hdvd : lcmUpTo m ∣ m.factorial :=
    Finset.lcm_dvd fun i hi => by
      rw [Finset.mem_Icc] at hi
      exact Nat.dvd_factorial (show 0 < i by omega) hi.2
  have hL : 0 < lcmUpTo m := Nat.pos_of_dvd_of_pos hdvd (Nat.factorial_pos m)
  set r := m.factorial / lcmUpTo m
  have hr : r * lcmUpTo m = m.factorial := Nat.div_mul_cancel hdvd
  rcases le_or_gt 6 m with h6 | h5
  · have hr1 : m - 1 ≤ r := Nat.le_of_mul_le_mul_right
      ((sub_one_mul_lcm_le_factorial m h6).trans hr.ge) hL
    have := maximalCoefficientIdeal_pow sX I hm r hr1 hn
    rwa [hr] at this
  · induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [pow_succ', ih]
      have := maximalCoefficientIdeal_mul_eq_of_maxOrder_le_five sX I (by omega) r
        (n * (m.factorial : ℤ)) (by
          have : (1 : ℤ) ≤ n := by exact_mod_cast hn
          have : (0 : ℤ) ≤ m.factorial := by positivity
          nlinarith)
      rw [hr] at this
      rw [this]
      congr 1
      push_cast
      ring

end Helpers

/-- **Kollár, Aside 3.99.10**. On a smooth equidimensional scheme of positive dimension over a
field of characteristic zero, for an ideal sheaf `I` with `m = maxord I ≥ 1`, the maximal
coefficient ideal `W_{m!}(I)` is D-balanced. -/
@[mmp "lem_kr3e_factorial_coefficient_ideal_d_balanced"]
public theorem isDBalanced_maximalCoefficientIdeal_factorial {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hequi : Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) :
    IsDBalanced sX (maximalCoefficientIdeal sX I ((maxOrder I).toNat.factorial : ℤ)) := by
  set s := (maxOrder I).toNat.factorial
  have hM : (maxOrder (maximalCoefficientIdeal sX I s)).toNat ≤ s :=
    ENat.toNat_le_of_le_coe (maxOrder_maximalCoefficientIdeal_le sX hequi hdim I hm s)
  intro i hi
  set M := (maxOrder (maximalCoefficientIdeal sX I s)).toNat
  have hD := higherDerivativeIdeal_maximalCoefficientIdeal sX hequi hdim I hm (s - i) i
  rw [Nat.sub_add_cancel (by omega)] at hD
  rw [hD, maximalCoefficientIdeal_factorial_pow sX I hm (n := M - i) (by omega)]
  refine maximalCoefficientIdeal_pow_le sX I ?_
  push_cast [Nat.cast_sub hi.le, Nat.cast_sub (hi.le.trans hM)]
  nlinarith [mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℤ) |>.mpr hM) (Int.natCast_nonneg i)]

/-- **Kollár, Prop. 3.99(5)**. On a smooth variety of positive dimension over a
field of characteristic `0`, for an ideal sheaf `I`
with `maxord I ≥ 1` and every `s ≥ 1`, the maximal coefficient ideal `W_s(I)` is maximal contact
invariant: `MC(W_s(I)) · D(W_s(I)) ⊆ W_s(I)`. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_mc_invariant"]
public theorem isMCInvariant_maximalCoefficientIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hX : Mori.IsVariety k sX) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) {s : ℤ} (hs : 1 ≤ s) :
    IsMCInvariant sX (maximalCoefficientIdeal sX I s) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n + 1 := ⟨(s - 1).toNat, by omega⟩
  have hequi := TopologicalSpace.Equidimensional.of_preirreducibleSpace X
  have hMC := maximalContactIdeal_maximalCoefficientIdeal sX hequi hdim I hm (s := n + 1) (by omega)
  push_cast at hMC
  rw [IsMCInvariant, hMC, derivativeIdeal_maximalCoefficientIdeal_succ sX hequi hdim I hm n,
    add_comm]
  exact maximalCoefficientIdeal_mul_le sX I 1 n

/-- Higher derivative ideals commute with smooth pull-back: `D^r(f^*I) = f^*D^r(I)`. -/
private theorem higherDerivativeIdeal_comap_of_smooth {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX]
    (f : Y ⟶ X) [Smooth f] (hf : f ≫ sX = sY)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) (r : ℕ) :
    higherDerivativeIdeal sY (I.comap f) r = (higherDerivativeIdeal sX I r).comap f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih,
      derivativeIdeal_comap_of_smooth sX sY f hf hdim]

/-- **Kollár, 3.102(2) / 3.103(2)**. Let `k` be a field of characteristic `0`, `X` and `Y`
smooth, equidimensional, locally of finite type over `k` with `dim X ≥ 1`, `I` an ideal sheaf on
`X` with `m = maxord I ≥ 1`, and `h : Y ⟶ X` a smooth `k`-morphism with `maxord h^*I = m`. Then
for every `s : ℤ`, `W_s(h^*I) = h^*W_s(I)`. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_smooth_pullback"]
public theorem maximalCoefficientIdeal_comap_of_smooth {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hXs : Mori.IsSmoothScheme sX) (hYs : Mori.IsSmoothScheme sY)
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (hXe : Equidimensional X) (hYe : Equidimensional Y)
    (hdim : 1 ≤ topologicalKrullDim X)
    (h : Y ⟶ X) [Smooth h] (hh : h ≫ sX = sY)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat)
    (hmY : maxOrder (I.comap h) = maxOrder I) (s : ℤ) :
    maximalCoefficientIdeal sY (I.comap h) s = (maximalCoefficientIdeal sX I s).comap h := by
  haveI : Smooth sX := (Mori.isSmoothScheme_iff sX).1 hXs
  unfold maximalCoefficientIdeal
  rw [hmY]
  simp only [(Scheme.IdealSheafData.map_gc h).l_iSup, Stacks.IdealSheaf.comap_finset_prod,
    Stacks.IdealSheaf.comap_pow, higherDerivativeIdeal_comap_of_smooth sX sY h hh
      (pos_dim_of_equidimensional hXe hdim)]

/-- The higher derivative ideals commute with the pull-back along `X_L ⟶ X`. -/
private theorem higherDerivativeIdeal_comap_pullback_fst {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (I : X.IdealSheafData) (r : ℕ) :
    higherDerivativeIdeal (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
        (I.comap (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) r =
      (higherDerivativeIdeal sX I r).comap
        (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  letI := σ.toAlgebra
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih]
    exact (derivativeIdeal_comap_pullback_fst (L := L) sX).2 _

/-- A morphism of smooth schemes over fields of characteristic zero that commutes with all
higher derivative ideals of `I` preserves the order of `I` pointwise. -/
private theorem multAt_comap_eq_of_higherDerivativeIdeal {k K : Type u} [Field k] [CharZero k]
    [Field K] [CharZero K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of K))
    [Smooth sX] [Smooth sY] (f : Y ⟶ X) (I : X.IdealSheafData)
    (hD : ∀ j, higherDerivativeIdeal sY (I.comap f) j = (higherDerivativeIdeal sX I j).comap f)
    (y : Y) : multAt (I.comap f) y = multAt I (f y) := by
  have key (n : ℕ) : (n : ℕ∞) ≤ multAt (I.comap f) y ↔ (n : ℕ∞) ≤ multAt I (f y) := by
    cases n with
    | zero => simp
    | succ n =>
      rw [succ_le_multAt_iff_forall_mem_support sY, succ_le_multAt_iff_forall_mem_support sX]
      exact forall₂_congr fun j _ => hD j ▸ mem_support_comap_iff f _ y
  exact le_antisymm (ENat.forall_natCast_le_iff_le.mp fun n => (key n).1)
    (ENat.forall_natCast_le_iff_le.mp fun n => (key n).2)

/-- Pulling back along a surjection that preserves the order pointwise preserves the maximal
order. -/
private theorem maxOrder_comap_of_surjective {X Y : Scheme} (f : Y ⟶ X) (I : X.IdealSheafData)
    (hf : Function.Surjective f) (h : ∀ y, multAt (I.comap f) y = multAt I (f y)) :
    maxOrder (I.comap f) = maxOrder I := by
  simp only [maxOrder, maxOrderAlong, Set.mem_univ, iSup_pos, h]
  exact hf.iSup_comp (multAt I)

/-- **Kollár, 3.102(2) / 3.103(2)**. Let `X` be a smooth equidimensional scheme of positive
dimension over a field `k` of characteristic zero, `I` an ideal sheaf on `X` with `maxord I ≥ 1`,
`σ : k →+* L` a field extension and `p : X ×_{Spec k} Spec L ⟶ X` the projection, `X_L` being an
`L`-scheme by the second projection. Then for every `s : ℤ`, `W_s(p^*I) = p^*W_s(I)`. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_field_change"]
public theorem maximalCoefficientIdeal_comap_fieldChange {k L : Type u} [Field k] [CharZero k]
    [Field L] (σ : k →+* L) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hX : Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) (s : ℤ) :
    maximalCoefficientIdeal (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
        (I.comap (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) s =
      (maximalCoefficientIdeal sX I s).comap
        (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  haveI : CharZero L := charZero_of_injective_ringHom σ.injective
  have hD := higherDerivativeIdeal_comap_pullback_fst σ sX I
  set p := Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))
  rw [maximalCoefficientIdeal, maximalCoefficientIdeal, maxOrder_comap_of_surjective p I
    p.surjective (multAt_comap_eq_of_higherDerivativeIdeal sX _ p I hD)]
  simp only [(Scheme.IdealSheafData.map_gc p).l_iSup,
    Stacks.IdealSheaf.comap_finset_prod, Stacks.IdealSheaf.comap_pow, hD]

end MMP.Resolution.Kollar

namespace MMP.Resolution

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section SNC

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- A subfamily of a simple normal crossing family is a simple normal crossing family. -/
private theorem isSNCFamily_comp {Λ Λ' : Type*} {E : Λ → Y.IdealSheafData}
    (hE : IsSNCFamily sY E) {e : Λ' → Λ} (he : Function.Injective e) :
    IsSNCFamily sY (E ∘ e) := by
  refine ⟨fun i => hE.1 (e i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  refine ⟨n, z, fun i => c ⟨e i.1, i.2⟩, hz, fun i => hc ⟨e i.1, i.2⟩, fun i i' h => ?_⟩
  exact Subtype.ext (he (congrArg Subtype.val (hinj h)))

/-- Deleting the empty entries of an ordered snc divisor gives an ordered snc divisor. -/
private theorem isOrderedSNC_deleteEmpty {E : OrderedDivisor Y} (hE : E.IsOrderedSNC sY) :
    E.deleteEmpty.IsOrderedSNC sY :=
  ⟨fun i => hE.1 _,
    isSNCFamily_comp hE.2 (List.Nodup.injective_get ((List.nodup_finRange _).filter _))⟩

/-- A member `E^j` of a simple normal crossing family has simple normal crossings with any
subfamily. -/
private theorem hasSNCWith_comp {Λ Λ' : Type*} {E : Λ → Y.IdealSheafData}
    (hE : IsSNCFamily sY E) {e : Λ' → Λ} (he : Function.Injective e) (j : Λ) :
    HasSNCWith (E ∘ e) (E j) := by
  intro x hx
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  refine ⟨n, z, fun i => c ⟨e i.1, i.2⟩, {c ⟨j, hx⟩}, hz, fun i => hc ⟨e i.1, i.2⟩, ?_, ?_⟩
  · exact fun i i' h => Subtype.ext (he (congrArg Subtype.val (hinj h)))
  · rw [hc ⟨j, hx⟩]; simp

/-- In a simple normal crossing family no member contains an irreducible component of
another. -/
private theorem not_subset_of_mem_componentsOf [IsLocallyNoetherian Y] {Λ : Type*}
    {E : Λ → Y.IdealSheafData} (hE : IsSNCFamily sY E) {i j : Λ} (hij : i ≠ j) {C : Set Y}
    (hC : C ∈ componentsOf ((E j).support : Set Y)) : ¬ C ⊆ (E i).support := by
  intro hsub
  obtain ⟨x, hxC⟩ := hC.1.1.nonempty
  have hxj : x ∈ (E j).support := hC.1.2 hxC
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  have hJ : IdealSheafData.stalk (E j) x = (coordPrime hz {c ⟨j, hxj⟩}).asIdeal := by
    rw [hc ⟨j, hxj⟩]; simp [coordPrime]
  have hCeq := eq_closure_coordPrime_of_mem_componentsOf hz hJ hC hxC
  have hmem : Y.fromSpecStalk x (coordPrime hz {c ⟨j, hxj⟩}) ∈ ((E i).support : Set Y) :=
    hsub (hCeq ▸ subset_closure rfl)
  rw [fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hsub hxC⟩] at hmem
  have hne : c ⟨i, hsub hxC⟩ ≠ c ⟨j, hxj⟩ := fun h => hij (congrArg Subtype.val (hinj h))
  refine notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne.symm ?_
  have := hmem (Ideal.subset_span rfl)
  simpa [coordPrime] using this

end SNC

section Dimension

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- If the stalks of `D` are generated by members of regular systems of parameters, the local
ring of `D` at a point has dimension one less than that of `Y`. -/
private theorem exists_ringKrullDim_stalk_subscheme (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (s : D.subscheme) : ∃ m : ℕ, ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) = m ∧
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((m - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hz : D.subschemeι s ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact ⟨s, rfl⟩
  obtain ⟨m, w, j, hw, hy⟩ := hD _ hz
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hw
  refine ⟨m, hw.2, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv D s), hy]
  exact ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters hw j

/-- On an equidimensional scheme of dimension `d` locally of finite type over a field, a
nonempty quasi-compact closed subscheme whose stalk ideals are generated by members of regular
systems of parameters is equidimensional of dimension `d - 1`. -/
private theorem equidimensional_and_topologicalKrullDim_subscheme {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (he : Equidimensional Y) {d : ℕ}
    (hd : topologicalKrullDim Y = ((d : ℕ∞) : WithBot ℕ∞)) (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    [CompactSpace D.subscheme] [Nonempty D.subscheme] :
    Equidimensional D.subscheme ∧
      topologicalKrullDim D.subscheme = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hle : ∀ s, ringKrullDim (D.subscheme.presheaf.stalk s) ≤
      (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s
    obtain ⟨m, hm, hs⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have h1 : ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) ≤ topologicalKrullDim Y := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup (fun y => ringKrullDim (Y.presheaf.stalk y)) _
    rw [hm, hd] at h1
    have h2 : m ≤ d := by exact_mod_cast h1
    rw [hs]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast Nat.sub_le_sub_right h2 1)
  have hcl : ∀ s : D.subscheme, IsClosed ({s} : Set D.subscheme) →
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s hs
    obtain ⟨m, hm, hs'⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have hy : IsClosed ({D.subschemeι s} : Set Y) := by
      simpa using D.subschemeι.isClosedEmbedding.isClosedMap _ hs
    have h1 := topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sY _ hy
    rw [topologicalKrullDimAt_eq_of_equidimensional k Y sY he
      (d := d) (by rw [hd]; rfl), hm] at h1
    have h2 : m = d := by exact_mod_cast h1.symm
    rw [hs', h2]
  have hat : ∀ s : D.subscheme,
      topologicalKrullDimAt D.subscheme s = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    rw [topologicalKrullDimAt_eq_iInf_closedSpecializations (D.subschemeι ≫ sY) s]
    obtain ⟨s', hs'mem, hs'cl⟩ :=
      (isClosed_closure (s := ({s} : Set D.subscheme))).exists_closed_singleton
        ⟨s, subset_closure rfl⟩
    refine le_antisymm (iInf_le_of_le ⟨s', specializes_iff_mem_closure.2 hs'mem, hs'cl⟩
      (hcl s' hs'cl).le) (le_iInf fun x => (hcl x.1 x.2.2).ge)
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq k _ (D.subschemeι ≫ sY) hat, ?_⟩
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨s0, -, hs0⟩ :=
    isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := D.subscheme))
  exact le_antisymm (iSup_le hle) (le_iSup_of_le s0 (hcl s0 hs0).ge)

end Dimension

section Nonzero

/-- The image of the generic point of an irreducible component under a closed embedding is the
generic point of an irreducible component of the image. -/
private theorem closure_singleton_mem_componentsOf_range {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [QuasiSober B] {g : A → B} (hg : Topology.IsClosedEmbedding g) {η : A}
    (hη : closure {η} ∈ irreducibleComponents A) :
    closure {g η} ∈ componentsOf (Set.range g) := by
  refine ⟨⟨isIrreducible_singleton.closure,
    closure_minimal (Set.singleton_subset_iff.2 ⟨η, rfl⟩) hg.isClosed_range⟩, fun T hT hle => ?_⟩
  have hb : closure {hT.1.genericPoint} = closure T := hT.1.isGenericPoint_genericPoint_closure
  obtain ⟨a, ha⟩ : hT.1.genericPoint ∈ Set.range g :=
    closure_minimal hT.2 hg.isClosed_range (hb ▸ subset_closure rfl)
  rw [← ha] at hb
  have h1 : g a ⤳ g η :=
    specializes_iff_mem_closure.2 (by rw [hb]; exact subset_closure (hle (subset_closure rfl)))
  have h2 : a ⤳ η := hg.isInducing.specializes_iff.1 h1
  have h3 : closure {a} ⊆ closure {η} := hη.2 isIrreducible_singleton.closure h2.closure_subset
  have h5 : g η ⤳ g a := (specializes_iff_mem_closure.2 (h3 (subset_closure rfl))).map hg.continuous
  calc T ⊆ closure T := subset_closure
    _ = closure {g a} := hb.symm
    _ ⊆ closure {g η} := h5.closure_subset

/-- On a smooth scheme over a field of characteristic zero all of whose irreducible components
have positive dimension, an ideal `K` with `(D^i K)^μ ⊆ K^(μ-i)` for `i < μ` has
`cosupp K = cosupp (K, μ)`. -/
private theorem support_eq_cosupport_of_higherDerivativeIdeal_pow_le' {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hcomp : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C) {μ : ℕ} (hμ : 1 ≤ μ)
    {K : X.IdealSheafData} (hK : ∀ i < μ, higherDerivativeIdeal sX K i ^ μ ≤ K ^ (μ - i)) :
    (K.support : Set X) = (⟨K, μ⟩ : MarkedIdeal X).cosupport := by
  have hsub : ∀ r < μ, (K.support : Set X) ⊆ (higherDerivativeIdeal sX K r).support := by
    intro r hr x hx
    have hK' := hK (μ - 1) (by omega)
    rw [Nat.sub_sub_self hμ, pow_one] at hK'
    have h1 := Scheme.IdealSheafData.support_antitone hK' hx
    rw [Scheme.IdealSheafData.support_pow _ _ (by omega)] at h1
    exact Scheme.IdealSheafData.support_antitone
      ((monotone_nat_of_le_succ fun n => by
        rw [higherDerivativeIdeal_succ]; exact le_derivativeIdeal sX hcomp _ :
          Monotone (higherDerivativeIdeal sX K)) (by omega : r ≤ μ - 1)) h1
  ext x
  refine ⟨fun hx => ?_,
    fun hx => mem_support_of_one_le_multAt K ((Nat.one_le_cast.2 hμ).trans hx)⟩
  show (μ : ℕ∞) ≤ multAt K x
  by_contra! hlt
  have hrx : multAt K x = (multAt K x).toNat := (ENat.coe_toNat hlt.ne_top).symm
  have hr := hsub (multAt K x).toNat (by exact_mod_cast hrx ▸ hlt) hx
  have hne : IdealSheafData.stalk (higherDerivativeIdeal sX K (multAt K x).toNat) x ≠ ⊤ :=
    fun ht => (IdealSheafData.stalk_eq_top_iff_notMem_support _ x).1 ht hr
  have h1 : ((1 : ℕ) : ℕ∞) ≤ multAt (higherDerivativeIdeal sX K (multAt K x).toNat) x := by
    rw [multAt, natCast_le_idealOrder_iff', pow_one]
    exact IsLocalRing.le_maximalIdeal hne
  rw [multAt_higherDerivativeIdeal sX hcomp K _ x, ← hrx, tsub_self] at h1
  exact absurd h1 (by decide)

/-- Pulling back along an isomorphism, the ideal quotient of the pull-backs contains the
pull-back of the ideal quotient. -/
private theorem comap_idealColon_pow_le {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f]
    (A B : X.IdealSheafData) (μ : ℕ) :
    (idealColon A (B ^ μ)).comap f ≤ idealColon (A.comap f) (B.comap f ^ μ) := by
  unfold idealColon
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U x hx
  let V : X.affineOpens := ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩
  let φ := (f.appIso U).inv.hom
  have hK := Scheme.IdealSheafData.ideal_ofIdeals_le
    (fun V => Submodule.colon (A.ideal V) ((B ^ μ).ideal V : Set Γ(X, V))) V
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hx
  have hx' := hK hx
  rw [Submodule.mem_colon] at hx' ⊢
  intro p hp
  have hpow : ((B.comap f) ^ μ).ideal U = (B.ideal V).comap φ ^ μ := by
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  rw [hpow] at hp
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.mem_comap, smul_eq_mul,
    map_mul]
  have hφp : φ p ∈ (B ^ μ).ideal V := by
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    have := Ideal.mem_map_of_mem φ hp
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (Ideal.map_comap_le) μ this
  simpa [smul_eq_mul] using hx' _ hφp

/-- Along an isomorphism `π`, the closed subscheme cut out by `π^*D` maps onto the support
of `D`. -/
private theorem range_subschemeι_comp_comap {X Y : Scheme.{u}} (π : Y ⟶ X) [IsIso π]
    (D : X.IdealSheafData) :
    Set.range ((D.comap π).subschemeι ≫ π) = (D.support : Set X) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.support_comap]
  exact Set.image_preimage_eq _ π.surjective

/-- If the support of `W` is its cosupport and `I(W) : Z^m` is the unit ideal along the centre
`Z` of a divisor `D`, the birational transform of `W` restricted to the strict transform of `D` is
nonzero at generic points. -/
theorem isNonzeroAtGenericPoints_comap_birationalTransform {X : Scheme.{u}} (W : MarkedIdeal X)
    (D : X.IdealSheafData) [IsIso (blowUpToBase (divisorComponentCentre W D))]
    (hsupp : (W.I.support : Set X) = W.cosupport)
    (htop : ∀ x ∈ ((divisorComponentCentre W D).support : Set X),
      IdealSheafData.stalk (idealColon W.I (divisorComponentCentre W D ^ W.m)) x = ⊤) :
    IsNonzeroAtGenericPoints ((W.birationalTransform (divisorComponentCentre W D)).I.comap
      (D.comap (blowUpToBase (divisorComponentCentre W D))).subschemeι) := by
  set Z := divisorComponentCentre W D
  set π := blowUpToBase Z
  set τ := (D.comap π).subschemeι
  intro η hη hbot
  have hmem : η ∈ ((W.birationalTransform Z).I.comap τ).support := by
    by_contra h
    exact bot_ne_top
      (hbot.symm.trans ((IdealSheafData.stalk_eq_top_iff_notMem_support _ η).2 h))
  rw [Scheme.IdealSheafData.support_comap] at hmem
  have hy : π (τ η) ∈ (W.I.support : Set X) := by
    have := Scheme.IdealSheafData.support_antitone (le_idealColon _ _) hmem
    rwa [Scheme.IdealSheafData.support_comap] at this
  have hC := closure_singleton_mem_componentsOf_range (τ ≫ π).isClosedEmbedding hη
  rw [range_subschemeι_comp_comap] at hC
  have hyZ : π (τ η) ∈ (Z.support : Set X) := by
    have hsub : closure {π (τ η)} ⊆ W.cosupport := by
      rw [← hsupp]
      exact W.I.support.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hy)
    have : π (τ η) ∈ ⋃₀ {C | C ∈ componentsOf (D.support : Set X) ∧ C ⊆ W.cosupport} :=
      ⟨_, ⟨hC, hsub⟩, subset_closure rfl⟩
    show π (τ η) ∈ (Scheme.IdealSheafData.vanishingIdeal _).support
    simpa [Stacks.AffineClosedUnion.support_vanishingIdeal] using subset_closure this
  have hW0 : IdealSheafData.stalk (W.birationalTransform Z).I (τ η) = ⊤ := by
    refine top_le_iff.1 (le_trans ?_ (stalk_le_stalk_of_le (comap_idealColon_pow_le π W.I Z W.m) _))
    rw [IdealSheafData.stalk_comap, htop _ hyZ, Ideal.map_top]
  rw [IdealSheafData.stalk_comap, hW0, Ideal.map_top] at hbot
  exact top_ne_bot hbot

end Nonzero

/-- Let `(X, I, E)` be a triple of dimension `n ≥ 1` with `maxord I = m ≥ 1`. Put `μ = m!` and
`W = W_μ(I)`, let `Z = Z_{-1}(W, μ, E^j)` with blow-up `π`, and let `S` be the pull-back of `E^j`
with inclusion `τ`. If `S` is nonempty, then `(S, W_0𝒪_S, μ, E_S)` is a marked triple of
marking `μ` and dimension `n - 1`. Here `W_0𝒪_S` is the restriction to `S` of the birational
transform of `(W, μ)`, and `E_S = (E^i ∩ S)_{i ≠ j}` with its empty members deleted. -/
@[mmp "lem_kr3e_bd_input_is_marked_triple"]
public theorem bdFunctor_input_mem_markedTriplesOfDim {m n j : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) (hn : 1 ≤ n)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        (((t.E.comap π).deleteIndex j).comap τ).deleteEmpty⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    (S.support : Set (blowUp Z)).Nonempty → tS ∈ markedTriplesOfDim {n - 1} μ := by
  intro μ W Z π S τ tS hne
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hEo, hEsnc⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  have hDj := hEsnc.1 ⟨j, hj⟩
  haveI hiso : IsIso π :=
    isIso_blowUpToBase_divisorComponentCentre t.sX hsm W _ hDj.2.2 hDj.2.1
  obtain ⟨-, hsm0, hlft0, hqc0, -, -, hE0⟩ :=
    pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht') π
  replace hsm0 : IsSmoothScheme (π ≫ t.sX) := hsm0
  replace hE0 : IsSNCFamily (π ≫ t.sX) (fun i => (t.E.E i).comap π) := hE0
  haveI : LocallyOfFiniteType (π ≫ t.sX) := hlft0
  haveI : IsLocallyNoetherian (blowUp Z) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ t.sX)
  set L := (List.finRange t.E.s).filter fun i : Fin t.E.s => i.val ≠ j with hL
  have hLinj : Function.Injective L.get :=
    List.Nodup.injective_get ((List.nodup_finRange _).filter _)
  have hLne : ∀ i, L.get i ≠ ⟨j, hj⟩ := fun i h => by
    have := List.of_mem_filter (L.get_mem i)
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at this
    exact this (congrArg Fin.val h :)
  have hres := isSmoothScheme_and_isSNCFamily_comap_subschemeι (π ≫ t.sX) hsm0
    (isSNCFamily_comp hE0 hLinj) (hasSNCWith_comp hE0 hLinj ⟨j, hj⟩)
    (fun i C hC => not_subset_of_mem_componentsOf hE0 (hLne i) hC)
  haveI : IsLocallyNoetherian S.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (τ ≫ π ≫ t.sX)
  haveI : CompactSpace S.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (τ ≫ π ≫ t.sX)
  haveI : Nonempty S.subscheme := by
    obtain ⟨x, hx⟩ := hne
    rw [← S.range_subschemeι] at hx
    obtain ⟨s, -⟩ := hx
    exact ⟨s⟩
  have hdY : topologicalKrullDim (blowUp Z) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [← hdim]
    exact IsHomeomorph.topologicalKrullDim_eq _ π.homeomorph.isHomeomorph
  obtain ⟨hequiS, hdimS⟩ := equidimensional_and_topologicalKrullDim_subscheme (π ≫ t.sX)
    (equidimensional_blowUp t.sX Z hequi) hdY S (hE0.exists_stalk_eq_span_parameter ⟨j, hj⟩)
  have hdim1 : 1 ≤ topologicalKrullDim t.X := by
    rw [hdim]
    exact_mod_cast hn
  have hm' : 1 ≤ (maxOrder t.I).toNat := by rw [hmax]; simpa using hm
  have hμ : 1 ≤ μ := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
  have hWmax : maxOrder W.I = μ :=
    Kollar.maxOrder_maximalCoefficientIdeal t.sX hsm hequi hdim1 t.I hm' hμ
  haveI : Smooth t.sX := (isSmoothScheme_iff _).1 hsm
  have hbal := Kollar.isDBalanced_maximalCoefficientIdeal_factorial t.sX hequi hdim1 t.I hm'
  have htoNat : (maxOrder t.I).toNat = m := by rw [hmax]; rfl
  rw [htoNat] at hbal
  have hK : ∀ i < μ, higherDerivativeIdeal t.sX W.I i ^ μ ≤ W.I ^ (μ - i) := by
    rwa [IsDBalanced, show maxOrder W.I = μ from hWmax, ENat.toNat_coe] at hbal
  have hcomp := pos_dim_of_equidimensional hequi hdim1
  have hsupp := support_eq_cosupport_of_higherDerivativeIdeal_pow_le' t.sX hcomp hμ hK
  obtain ⟨-, -, htop⟩ := pow_mul_idealColon_divisorComponentCentre t.sX hsm W.I μ hμ
    hWmax.le _ hDj.2.2 hDj.2.1
  have hnonzero : IsNonzeroAtGenericPoints ((W.birationalTransform Z).I.comap τ) :=
    isNonzeroAtGenericPoints_comap_birationalTransform W _ hsupp htop
  refine ⟨?_, rfl, n - 1, rfl, hdimS⟩
  refine ⟨hchar, hres.1, inferInstance, inferInstance, hequiS, hnonzero,
    isOrderedSNC_deleteEmpty ⟨fun i => ?_, hres.2⟩⟩
  exact ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hres.2.exists_stalk_eq_span_parameter i),
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
      (hres.2.exists_stalk_eq_span_parameter i)⟩

section Flat

variable {X : Scheme.{u}}

open Classical in
/-- The list of the nonempty entries of an ordered divisor, in their order. -/
private noncomputable def flat (E : OrderedDivisor X) : List X.IdealSheafData :=
  (List.ofFn E.E).filter fun D => D ≠ ⊤

open Classical in
private theorem ofFn_deleteEmpty (E : OrderedDivisor X) :
    List.ofFn E.deleteEmpty.E = flat E := by
  show List.ofFn (E.E ∘ ((List.finRange E.s).filter fun i => E.E i ≠ ⊤).get) = flat E
  rw [← List.map_ofFn, List.ofFn_get, flat, List.ofFn_eq_map (f := E.E), List.filter_map]
  rfl

private theorem eq_of_ofFn_eq {E F : OrderedDivisor X} (h : List.ofFn E.E = List.ofFn F.E) :
    E = F := by
  obtain ⟨s, e⟩ := E
  obtain ⟨t, f⟩ := F
  rw [List.ofFn_inj'] at h
  cases h
  rfl

private theorem deleteEmpty_eq_iff {E F : OrderedDivisor X} :
    E.deleteEmpty = F.deleteEmpty ↔ flat E = flat F := by
  refine ⟨fun h => ?_, fun h => eq_of_ofFn_eq ?_⟩
  · rw [← ofFn_deleteEmpty, ← ofFn_deleteEmpty, h]
  · rw [ofFn_deleteEmpty, ofFn_deleteEmpty, h]

private theorem flat_deleteEmpty (E : OrderedDivisor X) : flat E.deleteEmpty = flat E := by
  rw [flat, ofFn_deleteEmpty, flat, List.filter_filter]
  simp

/-- `E^♭♭ = E^♭`. -/
private theorem deleteEmpty_deleteEmpty (E : OrderedDivisor X) :
    E.deleteEmpty.deleteEmpty = E.deleteEmpty :=
  deleteEmpty_eq_iff.2 (flat_deleteEmpty E)

/-- If `T` maps values failing `p` to values failing `p`, then the filtered image of a list
under `T` depends only on the filtered list. -/
private theorem filter_map_eq_of_filter_eq {α β : Type*} (p : α → Bool) (q : β → Bool)
    (T : α → β) (hT : ∀ a, p a = false → q (T a) = false) {l l' : List α}
    (h : l.filter p = l'.filter p) : (l.map T).filter q = (l'.map T).filter q := by
  have key : ∀ l : List α, (l.map T).filter q = ((l.filter p).map T).filter q := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        simp [List.filter_cons, ha', hT a ha', ih]
  rw [key l, key l', h]

/-- Inverse images of `∼`-related ordered divisors are `∼`-related. -/
private theorem deleteEmpty_comap_eq {Y : Scheme.{u}} {E F : OrderedDivisor X}
    (h : E.deleteEmpty = F.deleteEmpty) (f : Y ⟶ X) :
    (E.comap f).deleteEmpty = (F.comap f).deleteEmpty := by
  classical
  rw [deleteEmpty_eq_iff] at h ⊢
  have hE : List.ofFn (E.comap f).E = (List.ofFn E.E).map (·.comap f) := by
    rw [List.map_ofFn]
    rfl
  have hF : List.ofFn (F.comap f).E = (List.ofFn F.E).map (·.comap f) := by
    rw [List.map_ofFn]
    rfl
  rw [flat, flat, hE, hF]
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD, Scheme.IdealSheafData.comap_top]

open Classical in
/-- The indices of the nonempty entries. -/
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

private theorem injective_flatIdx_get (E : OrderedDivisor X) :
    Function.Injective (flatIdx E).get :=
  List.nodup_iff_injective_get.1 ((List.nodup_finRange _).filter _)

private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

end Flat

section InsertTop

variable {X : Scheme.{u}}

/-- `E` with an empty entry inserted at position `p` (`0`-based). -/
private def insertTop (E : OrderedDivisor X) (p : ℕ) (hp : p ≤ E.s) : OrderedDivisor X :=
  ⟨E.s + 1, fun i => if h : i.val < p then E.E ⟨i, by have := i.isLt; omega⟩
    else if h' : i.val = p then ⊤ else E.E ⟨i.val - 1, by have := i.isLt; omega⟩⟩

private theorem support_insertTop (E : OrderedDivisor X) (p : ℕ) (hp : p ≤ E.s) :
    (insertTop E p hp).support = E.support := by
  ext x
  simp only [OrderedDivisor.support, Set.mem_iUnion, insertTop]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h1 h2
    · exact ⟨_, hi⟩
    · simp [Scheme.IdealSheafData.support_top] at hi
    · exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    by_cases h : i.val < p
    · exact ⟨⟨i, by omega⟩, by simpa [h] using hi⟩
    · refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
      have h1 : ¬ (i.val + 1 < p) := by omega
      have h2 : ¬ (i.val + 1 = p) := by omega
      simpa [h1, h2] using hi

private theorem birationalEntry_top (Z : X.IdealSheafData) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (blowUpToBase Z ⁻¹' (((⊤ : X.IdealSheafData).support : Set X) \
        componentsOfCodimAtLeastTwo (Z.support : Set X)))) = ⊤ := by
  have : (Closeds.closure (blowUpToBase Z ⁻¹' (((⊤ : X.IdealSheafData).support : Set X) \
      componentsOfCodimAtLeastTwo (Z.support : Set X)))) = ⊥ := by
    ext x
    simp [Scheme.IdealSheafData.support_top]
  rw [this, Scheme.IdealSheafData.vanishingIdeal_bot]

private theorem totalTransform_insertTop (E : OrderedDivisor X) (p : ℕ) (hp : p ≤ E.s)
    (Z : X.IdealSheafData) :
    (insertTop E p hp).totalTransform Z =
      insertTop (E.totalTransform Z) p (by simp only [OrderedDivisor.totalTransform]; omega) := by
  have hs := support_insertTop E p hp
  simp only [OrderedDivisor.totalTransform, hs]
  simp only [insertTop, OrderedDivisor.mk.injEq, heq_eq_eq, true_and]
  funext ⟨i, hi⟩
  simp only [Fin.snoc, Fin.coe_castLT, cast_eq]
  split_ifs <;> first | omega | rfl | exact birationalEntry_top Z

private theorem ofFn_insertTop (E : OrderedDivisor X) (p : ℕ) (hp : p ≤ E.s) :
    List.ofFn (insertTop E p hp).E = (List.ofFn E.E).take p ++ ⊤ :: (List.ofFn E.E).drop p := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_take, List.length_cons,
      List.length_drop, insertTop]
    omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, insertTop]
    rcases lt_trichotomy i p with h | rfl | h
    · rw [List.getElem_append_left (by simp <;> omega)]
      simp [h]
    · rw [List.getElem_append_right (by simp <;> omega)]
      simp [show min i E.s = i by omega]
    · rw [List.getElem_append_right (by simp <;> omega)]
      have h3 : i - min p E.s = (i - 1 - p) + 1 := by omega
      simp only [List.length_take, List.length_ofFn, h3, List.getElem_cons_succ,
        List.getElem_drop, List.getElem_ofFn]
      rw [dif_neg (by omega), dif_neg (by omega)]
      congr 2
      omega

private theorem flat_insertTop (E : OrderedDivisor X) (p : ℕ) (hp : p ≤ E.s) :
    flat (insertTop E p hp) = flat E := by
  rw [flat, flat, ofFn_insertTop, List.filter_append, List.filter_cons]
  conv_rhs => rw [← List.take_append_drop p (List.ofFn E.E), List.filter_append]
  simp

private theorem orderedTotalTransform_s : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (E : OrderedDivisor X), (B.orderedTotalTransform E).s = E.s + B.length
  | _, .nil _, _ => rfl
  | _, .cons Z B, E => by
    rw [ClosedBlowupSequence.orderedTotalTransform, orderedTotalTransform_s B,
      ClosedBlowupSequence.length]
    show E.s + 1 + B.length = _
    omega

private theorem orderedTotalTransform_insertTop : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (E : OrderedDivisor X) (p : ℕ) (hp : p ≤ E.s) (h' : p ≤ (B.orderedTotalTransform E).s),
    B.orderedTotalTransform (insertTop E p hp) = insertTop (B.orderedTotalTransform E) p h'
  | _, .nil _, _, _, _, _ => rfl
  | _, .cons Z B, E, p, hp, h' => by
    simp only [ClosedBlowupSequence.orderedTotalTransform]
    rw [totalTransform_insertTop]
    exact orderedTotalTransform_insertTop B _ p _ h'

/-- `E` with its `p`-th entry removed. -/
private def removeAt {n : ℕ} (e : Fin (n + 1) → X.IdealSheafData) (p : ℕ) : OrderedDivisor X :=
  ⟨n, fun i => if i.val < p then e i.castSucc else e i.succ⟩

private theorem insertTop_removeAt {n : ℕ} (e : Fin (n + 1) → X.IdealSheafData) (p : Fin (n + 1))
    (he : e p = ⊤) : insertTop (removeAt e p) p (by simp [removeAt]; omega) = ⟨n + 1, e⟩ := by
  simp only [insertTop, removeAt, OrderedDivisor.mk.injEq, heq_eq_eq, true_and]
  funext ⟨i, hi⟩
  split_ifs with h1 h2 h3
  all_goals first
    | rfl
    | (exfalso; simp only [Fin.val_mk, Fin.coe_castSucc] at *; omega)
    | (rw [← he]; congr 1; ext; simp only [Fin.val_mk] at *; omega)
    | (congr 1; ext; simp only [Fin.val_mk, Fin.val_succ] at *; omega)
    | (simp only [Fin.val_mk] at h1 h2 h3
       exact congrArg e (Fin.ext (by simp only [Fin.val_succ]; omega)))

/-- A quantity depending on an ordered divisor that does not change when an empty entry is
inserted depends only on `E^♭`. -/
private theorem eq_of_deleteEmpty_eq {α : Sort*} (P : OrderedDivisor X → α)
    (hP : ∀ E p hp, P (insertTop E p hp) = P E) {E E' : OrderedDivisor X}
    (h : E.deleteEmpty = E'.deleteEmpty) : P E = P E' := by
  have key : ∀ n (E : OrderedDivisor X), E.s = n → P E = P E.deleteEmpty := by
    intro n
    induction n with
    | zero =>
      rintro ⟨s, e⟩ (rfl : s = 0)
      congr 1
      exact eq_of_ofFn_eq (by rw [ofFn_deleteEmpty]; simp [flat])
    | succ n ih =>
      rintro ⟨s, e⟩ (rfl : s = n + 1)
      by_cases hall : ∀ i, e i ≠ ⊤
      · congr 1
        refine eq_of_ofFn_eq ?_
        rw [ofFn_deleteEmpty, flat, List.filter_eq_self.2]
        intro D hD
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hD
        simpa using hall i
      · push Not at hall
        obtain ⟨p, hp⟩ := hall
        have hE := insertTop_removeAt e p hp
        rw [← hE, hP, ih _ rfl]
        congr 1
        exact deleteEmpty_eq_iff.2 (flat_insertTop _ _ _).symm
  rw [key _ E rfl, h, ← key _ E' rfl]

end InsertTop

section Reindex

variable {X : Scheme.{u}} {Λ Λ' : Type*} (E : Λ → X.IdealSheafData) (g : Λ' → Λ)

/-- A property of all entries may be checked on the nonempty ones. -/
private theorem forall_iff_forall_comp (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i)
    (R : X.IdealSheafData → Prop) (hR : R ⊤) :
    (∀ i, R (E i)) ↔ ∀ j, R (E (g j)) := by
  refine ⟨fun h j => h _, fun h i => ?_⟩
  by_cases hi : E i = ⊤
  · rw [hi]
    exact hR
  · obtain ⟨j, rfl⟩ := hg i hi
    exact h j

/-- The coordinate assignment of an snc family at a point may be taken over the nonempty
entries. -/
private theorem exists_coord_iff (hginj : Function.Injective g)
    (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x) :
    (∃ c : {i // x ∈ (E i).support} → Fin n,
        (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c) ↔
      ∃ c : {j // x ∈ (E (g j)).support} → Fin n,
        (∀ j, IdealSheafData.stalk (E (g j.1)) x = Ideal.span {z (c j)}) ∧
          Function.Injective c := by
  let φ : {j // x ∈ (E (g j)).support} → {i // x ∈ (E i).support} := fun j => ⟨g j.1, j.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (hginj (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨j, hj⟩ := hg i.1 fun h => by
      have := i.2
      rwa [h, Scheme.IdealSheafData.support_top] at this
    exact ⟨⟨j, hj ▸ i.2⟩, Subtype.ext hj⟩
  let e := Equiv.ofBijective φ hφ
  constructor
  · rintro ⟨c, hc, hinj⟩
    exact ⟨c ∘ φ, fun j => hc (φ j), hinj.comp hφ.1⟩
  · rintro ⟨c, hc, hinj⟩
    refine ⟨c ∘ e.symm, fun i => ?_, hinj.comp e.symm.injective⟩
    have h := hc (e.symm i)
    have hi : g (e.symm i).1 = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
    rwa [hi] at h

private theorem isSNCFamily_iff_comp {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hginj : Function.Injective g) (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) :
    IsSNCFamily sX E ↔ IsSNCFamily sX (E ∘ g) := by
  refine and_congr (forall_iff_forall_comp E g hg (fun D => IsReduced D.subscheme ∧
      MMP.Mori.IsPureCodimOne D.support ∧ MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
      ⟨?_, ?_, ?_⟩)
    (forall_congr' fun x => exists_congr fun n => exists_congr fun z => ?_)
  · exact isReduced_of_isAffine_isReduced _
  · intro W hW
    have h := hW.prop
    rw [Scheme.IdealSheafData.support_top] at h
    obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
    exact (h hw).elim
  · unfold MMP.Mori.IsSmoothScheme
    ext x
    exact isEmptyElim x
  · have key := exists_coord_iff E g hginj hg x z
    constructor
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.1 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.2 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩

end Reindex

private theorem isOrderedSNC_deleteEmpty_iff {X : Scheme.{u}} (E : OrderedDivisor X)
    {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) :
    E.IsOrderedSNC sX ↔ E.deleteEmpty.IsOrderedSNC sX :=
  and_congr
    (forall_iff_forall_comp E.E _ (exists_flatIdx_get E)
      (fun D => IsReduced D.subscheme ∧ Stacks.Divisors.IsEffectiveCartierDivisor D)
      ⟨isReduced_of_isAffine_isReduced _, Stacks.Divisors.isEffectiveCartierDivisor_top⟩)
    (isSNCFamily_iff_comp E.E _ sX (injective_flatIdx_get E) (exists_flatIdx_get E))

/-- `(X, I, E)` is a triple iff `(X, I, E')` is, for `E^♭ = E'^♭` (Kollár 3.72): the empty
entries are smooth, reduced effective Cartier divisors meeting no point, so they impose
nothing on the snc condition. -/
private theorem isTriple_iff_of_deleteEmpty_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) {E E' : OrderedDivisor X}
    (h : E.deleteEmpty = E'.deleteEmpty) : IsTriple sX I E ↔ IsTriple sX I E' := by
  unfold IsTriple
  rw [isOrderedSNC_deleteEmpty_iff E, h, ← isOrderedSNC_deleteEmpty_iff E']

private theorem append_nil : ∀ {X : Scheme.{u}} (P : ClosedBlowupSequence X),
    P.append (.nil P.target) = P
  | _, .nil _ => rfl
  | _, .cons Z P => congrArg (ClosedBlowupSequence.cons Z) (append_nil P)

private theorem pushforward_nil {S X : Scheme.{u}} (j : S ⟶ X) :
    (ClosedBlowupSequence.nil S).pushforward j = .nil X := by
  have hex : ∃ B', ClosedBlowupSequence.IsPushforward j (.nil S) B' := ⟨.nil X, trivial⟩
  unfold ClosedBlowupSequence.pushforward
  rw [dif_pos hex]
  have hs := hex.choose_spec
  generalize hex.choose = B at hs ⊢
  cases B with
  | nil => rfl
  | cons Z B => exact (hs : False).elim

private theorem reduction_cons_nil {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Z = ⊤) :
    (ClosedBlowupSequence.cons Z (.nil _)).reduction = .nil X := by
  subst hZ
  unfold ClosedBlowupSequence.reduction
  rw [ClosedBlowupSequence.pullbackReduced, dif_pos (Scheme.IdealSheafData.comap_top _)]
  rfl

private theorem divisorComponentCentre_top {X : Scheme.{u}} (K : MarkedIdeal X) :
    divisorComponentCentre K ⊤ = ⊤ := by
  have h0 : ⋃₀ {W | W ∈ componentsOf (((⊤ : X.IdealSheafData).support : Set X)) ∧
      W ⊆ K.cosupport} = ∅ := by
    refine Set.sUnion_eq_empty.2 fun W hW => ?_
    obtain ⟨⟨-, hsub⟩, -⟩ := hW.1
    exact Set.subset_empty_iff.1 (by simpa [Scheme.IdealSheafData.support_top] using hsub)
  have : Closeds.closure (⋃₀ {W | W ∈ componentsOf (((⊤ : X.IdealSheafData).support : Set X)) ∧
      W ⊆ K.cosupport}) = ⊥ := by
    rw [h0]
    ext
    simp
  rw [divisorComponentCentre, this, Scheme.IdealSheafData.vanishingIdeal_bot]

private theorem comap_eq_top_of_eq_top {X Y : Scheme.{u}} (f : Y ⟶ X) (D : X.IdealSheafData)
    (hD : D = ⊤) : D.comap f = ⊤ := by
  subst hD
  exact Scheme.IdealSheafData.comap_top _

/-- Step 1(a): `𝓑𝓓_{n,m,j}` at an empty entry is the empty sequence (its centre
`Z_{-1}(W, μ, ∅)` is empty, so is `S`, and the trivial blow-up is deleted). -/
private theorem bdFunctor_insertTop_self (M : MarkedFamily.{u}) (n m : ℕ)
    (u : FieldBlowupTriple.{u}) (p : ℕ) (hp : p ≤ u.E.s) :
    bdFunctor M n m p { u with E := insertTop u.E p hp } = .nil u.X := by
  unfold bdFunctor
  split_ifs with h
  · dsimp only
    have hE : (insertTop u.E p hp).E ⟨p, h.2⟩ = ⊤ := by simp [insertTop]
    rw [if_neg (fun hc => by
      obtain ⟨x, hx⟩ := hc.1
      rw [comap_eq_top_of_eq_top _ _ hE, Scheme.IdealSheafData.support_top] at hx
      exact hx), pushforward_nil]
    exact reduction_cons_nil _ (by rw [hE]; exact divisorComponentCentre_top _)
  · rfl

private theorem map_filter_finRange_ne {α : Type*} (n : ℕ) (f : Fin n → α) (j : ℕ) :
    ((List.finRange n).filter (fun i => i.val ≠ j)).map f = (List.ofFn f).eraseIdx j := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.ofFn_succ]
    rcases j with _ | j
    · simp [List.filter_map, Function.comp_def, List.map_map, List.ofFn_eq_map]
    · simp [List.filter_map, Function.comp_def, List.map_map, ← ih]

private theorem ofFn_deleteIndex {X : Scheme.{u}} (E : OrderedDivisor X) (j : ℕ) :
    List.ofFn (E.deleteIndex j).E = (List.ofFn E.E).eraseIdx j := by
  show List.ofFn (E.E ∘ ((List.finRange E.s).filter fun i : Fin E.s => i.val ≠ j).get) = _
  rw [← List.map_ofFn, List.ofFn_get, map_filter_finRange_ne]

private theorem filter_eraseIdx_insert_of_lt {α : Type*} (q : α → Bool) (a : α) (ha : q a = false)
    (L : List α) (p j : ℕ) (hp : p ≤ L.length) (hj : j < p) :
    ((L.take p ++ a :: L.drop p).eraseIdx j).filter q = (L.eraseIdx j).filter q := by
  have hlt : j < (L.take p).length := by simp; omega
  conv_rhs => rw [← List.take_append_drop p L]
  rw [List.eraseIdx_append_of_lt_length hlt, List.eraseIdx_append_of_lt_length hlt]
  simp [List.filter_append, List.filter_cons, ha]

private theorem filter_eraseIdx_insert_of_le {α : Type*} (q : α → Bool) (a : α) (ha : q a = false)
    (L : List α) (p j : ℕ) (hp : p ≤ L.length) (hj : p ≤ j) :
    ((L.take p ++ a :: L.drop p).eraseIdx (j + 1)).filter q = (L.eraseIdx j).filter q := by
  have hle : (L.take p).length ≤ j + 1 := by simp; omega
  have hle' : (L.take p).length ≤ j := by simp; omega
  conv_rhs => rw [← List.take_append_drop p L]
  rw [List.eraseIdx_append_of_length_le hle, List.eraseIdx_append_of_length_le hle']
  have h1 : j + 1 - (L.take p).length = (j - (L.take p).length) + 1 := by simp; omega
  rw [h1, List.eraseIdx_cons_succ]
  simp [List.filter_append, List.filter_cons, ha]

private theorem flat_deleteIndex_insertTop_of_lt {X : Scheme.{u}} (E : OrderedDivisor X) (p : ℕ)
    (hp : p ≤ E.s) (j : ℕ) (hj : j < p) :
    flat ((insertTop E p hp).deleteIndex j) = flat (E.deleteIndex j) := by
  classical
  rw [flat, flat, ofFn_deleteIndex, ofFn_deleteIndex, ofFn_insertTop]
  exact filter_eraseIdx_insert_of_lt _ _ (by simp) _ p j (by simpa using hp) hj

private theorem flat_deleteIndex_insertTop_of_le {X : Scheme.{u}} (E : OrderedDivisor X) (p : ℕ)
    (hp : p ≤ E.s) (j : ℕ) (hj : p ≤ j) :
    flat ((insertTop E p hp).deleteIndex (j + 1)) = flat (E.deleteIndex j) := by
  classical
  rw [flat, flat, ofFn_deleteIndex, ofFn_deleteIndex, ofFn_insertTop]
  exact filter_eraseIdx_insert_of_le _ _ (by simp) _ p j (by simpa using hp) hj

/-- `𝓑𝓓_{n,m,j}(X, I, E)` and `𝓑𝓓_{n,m,j'}(X, I, E')` agree when the `j`-th entry of `E` is the
`j'`-th entry of `E'` and the remaining entries agree up to empty ones, provided `𝓜_{n-1,m!}`
ignores empty entries and `X` has dimension `n` (Step 1(b)). -/
private theorem bdFunctor_congr (M : MarkedFamily.{u}) (n m : ℕ) (u : FieldBlowupTriple.{u})
    (E E' : OrderedDivisor u.X) (j j' : ℕ) (hs : j < E.s ↔ j' < E'.s)
    (hD : ∀ h h', E.E ⟨j, h⟩ = E'.E ⟨j', h'⟩)
    (hflat : flat (E.deleteIndex j) = flat (E'.deleteIndex j'))
    (hu : IsTriple u.sX u.I E) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hdim : Nonempty u.X → topologicalKrullDim u.X = ((n : ℕ∞) : WithBot ℕ∞))
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} m.factorial)
      (fun t _ => M (n - 1) m.factorial t)) :
    bdFunctor M n m j { u with E := E } = bdFunctor M n m j' { u with E := E' } := by
  unfold bdFunctor
  by_cases h : maxOrder u.I = m ∧ j < E.s
  · have h' : maxOrder u.I = m ∧ j' < E'.s := ⟨h.1, hs.1 h.2⟩
    rw [dif_pos h, dif_pos h']
    dsimp only
    have key : ∀ hX : Nonempty u.X, _ := fun hX =>
      bdFunctor_input_mem_markedTriplesOfDim (m := m) (n := n) (j := j) { u with E := E } hu hm
        h.1 h.2 hn (hdim hX)
    dsimp only at key
    rw [hD h.2 h'.2] at key ⊢
    generalize E'.E ⟨j', h'.2⟩ = D at key ⊢
    congr 3
    set Z := divisorComponentCentre
      ({ I := maximalCoefficientIdeal u.sX u.I m.factorial, m := m.factorial } : MarkedIdeal u.X) D
    set S := D.comap (blowUpToBase Z)
    have hdel : (((E.comap (blowUpToBase Z)).deleteIndex j).comap S.subschemeι).deleteEmpty =
        (((E'.comap (blowUpToBase Z)).deleteIndex j').comap S.subschemeι).deleteEmpty :=
      deleteEmpty_comap_eq (deleteEmpty_comap_eq (deleteEmpty_eq_iff.2 hflat) _) _
    have hiff := fun (I' : S.subscheme.IdealSheafData) =>
      isTriple_iff_of_deleteEmpty_eq (S.subschemeι ≫ blowUpToBase Z ≫ u.sX) I' hdel
    split_ifs with h1 h2 h2
    · have hX : Nonempty u.X := ⟨(blowUpToBase Z).base h1.1.some⟩
      have hmem := key hX h1.1
      obtain ⟨_, e1⟩ := hMe _ ⟨h1.2, rfl, hmem.2.2⟩
      obtain ⟨_, e2⟩ := hMe _ ⟨h2.2, rfl, hmem.2.2⟩
      beta_reduce at e1 e2
      rw [← e1, ← e2]
      unfold MarkedTriple.deleteEmpty
      dsimp only
      rw [hdel]
    · exact (h2 ⟨h1.1, (hiff _).1 h1.2⟩).elim
    · exact (h1 ⟨h2.1, (hiff _).2 h2.2⟩).elim
    · rfl
  · have h' : ¬ (maxOrder u.I = m ∧ j' < E'.s) := fun h' => h ⟨h'.1, hs.2 h'.2⟩
    rw [dif_neg h, dif_neg h']

/-- Step 1(b), entries before the inserted one: same index, same data. -/
private theorem bdFunctor_insertTop_of_lt (M : MarkedFamily.{u}) (n m : ℕ)
    (u : FieldBlowupTriple.{u}) (p : ℕ) (hp : p ≤ u.E.s) (j : ℕ) (hj : j < p)
    (hu : IsTriple u.sX u.I u.E) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hdim : Nonempty u.X → topologicalKrullDim u.X = ((n : ℕ∞) : WithBot ℕ∞))
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} m.factorial)
      (fun t _ => M (n - 1) m.factorial t)) :
    bdFunctor M n m j { u with E := insertTop u.E p hp } = bdFunctor M n m j u :=
  (bdFunctor_congr M n m u u.E (insertTop u.E p hp) j j
    ⟨fun _ => by show j < u.E.s + 1; omega, fun _ => by omega⟩
    (fun _ _ => by simp [insertTop, hj])
    (flat_deleteIndex_insertTop_of_lt u.E p hp j hj).symm hu hm hn hdim hMe).symm

/-- Step 1(b), entries after the inserted one: the index shifts by one. -/
private theorem bdFunctor_insertTop_of_le (M : MarkedFamily.{u}) (n m : ℕ)
    (u : FieldBlowupTriple.{u}) (p : ℕ) (hp : p ≤ u.E.s) (j : ℕ) (hj : p ≤ j)
    (hu : IsTriple u.sX u.I u.E) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hdim : Nonempty u.X → topologicalKrullDim u.X = ((n : ℕ∞) : WithBot ℕ∞))
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} m.factorial)
      (fun t _ => M (n - 1) m.factorial t)) :
    bdFunctor M n m (j + 1) { u with E := insertTop u.E p hp } = bdFunctor M n m j u :=
  (bdFunctor_congr M n m u u.E (insertTop u.E p hp) j (j + 1)
    ⟨fun _ => by show j + 1 < u.E.s + 1; omega, fun h => by
      have : j + 1 < u.E.s + 1 := h
      omega⟩
    (fun _ _ => by simp [insertTop, show ¬ j + 1 < p by omega, show j + 1 ≠ p by omega])
    (flat_deleteIndex_insertTop_of_le u.E p hp j hj).symm hu hm hn hdim hMe).symm

section Dimension

/-- A nonempty space all of whose irreducible components have dimension `n` has dimension `n`. -/
private theorem topologicalKrullDim_eq_of_forall_mem_irreducibleComponents {Y : Type*}
    [TopologicalSpace Y] [Nonempty Y] {n : WithBot ℕ∞}
    (h : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = n) :
    topologicalKrullDim Y = n := by
  refine le_antisymm ?_ ?_
  · exact MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun C hC =>
      (h C hC).le
  · obtain ⟨y⟩ := ‹Nonempty Y›
    rw [← h _ (irreducibleComponent_mem_irreducibleComponents y)]
    exact topologicalKrullDim_subspace_le _ _

/-- Every irreducible component of the end of a blow-up sequence has the dimension of an
irreducible component of the start. -/
private theorem exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_target
    {k : Type u} [Field k] {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    ∀ (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {C : Set S.target},
      C ∈ irreducibleComponents S.target →
        ∃ D ∈ irreducibleComponents X, topologicalKrullDim C = topologicalKrullDim D := by
  induction S with
  | nil X => exact fun _ _ C hC => ⟨C, hC, rfl⟩
  | cons Z B ih =>
    intro sX _ C hC
    haveI : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsProper (blowUpToBase Z) := AlgebraicGeometry.isProper_blowUpToBase (I := Z)
    haveI : LocallyOfFiniteType (blowUpToBase Z ≫ sX) := inferInstance
    obtain ⟨D, hD, h⟩ := ih (blowUpToBase Z ≫ sX) hC
    obtain ⟨D', hD', h'⟩ :=
      exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hD
    exact ⟨D', hD', h.trans h'⟩

/-- A nonempty end of a blow-up sequence starting with an equidimensional scheme of finite type of
dimension `n` has dimension `n`. -/
private theorem topologicalKrullDim_target_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hX : Equidimensional X) {n : WithBot ℕ∞}
    (hd : topologicalKrullDim X = n) (S : ClosedBlowupSequence X) (_ : Nonempty S.target) :
    topologicalKrullDim S.target = n := by
  refine topologicalKrullDim_eq_of_forall_mem_irreducibleComponents fun C hC => ?_
  obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_target S sX hC
  obtain ⟨x, -⟩ := hD.1.nonempty
  haveI : Nonempty X := ⟨x⟩
  rw [h, ← hd]
  exact (topologicalKrullDim_eq_of_forall_mem_irreducibleComponents fun D' hD' =>
    hX D' hD' D hD).symm

private theorem dimNat_of_eq {X : Scheme.{u}} {n : ℕ}
    (hd : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)) : dimNat X = n := by
  rw [dimNat, hd]
  rfl

end Dimension

section Loop

variable (M : MarkedFamily.{u}) (n μ : ℕ) (t : FieldBlowupTriple.{u}) (p : ℕ) (hp : p ≤ t.E.s)
  (P : ClosedBlowupSequence t.X) (hlft : LocallyOfFiniteType t.sX) (heq : Equidimensional t.X)
  (hd : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
  (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} μ.factorial)
    (fun t _ => M (n - 1) μ.factorial t))

omit P in
include hp in
private theorem le_endOf_s (P : ClosedBlowupSequence t.X) : p ≤ (t.endOf P).E.s := by
  simp only [FieldBlowupTriple.endOf, orderedTotalTransform_s]
  omega

private theorem endOf_E_insertTop :
    (({ t with E := insertTop t.E p hp } : FieldBlowupTriple.{u}).endOf P).E =
      insertTop (t.endOf P).E p (le_endOf_s t p hp P) :=
  orderedTotalTransform_insertTop P t.E p hp _

private theorem isTriple_endOf_insertTop_iff :
    IsTriple (({ t with E := insertTop t.E p hp } : FieldBlowupTriple.{u}).endOf P).sX
        (({ t with E := insertTop t.E p hp } : FieldBlowupTriple.{u}).endOf P).I
        (({ t with E := insertTop t.E p hp } : FieldBlowupTriple.{u}).endOf P).E ↔
      IsTriple (t.endOf P).sX (t.endOf P).I (t.endOf P).E := by
  rw [endOf_E_insertTop]
  exact isTriple_iff_of_deleteEmpty_eq _ _ (deleteEmpty_eq_iff.2 (flat_insertTop _ _ _))

private theorem bdFunctor_congr_E (j : ℕ) (u : FieldBlowupTriple.{u}) {q : ℕ} (hq : q ≤ u.E.s)
    (E' : OrderedDivisor u.X) (hE' : E' = insertTop u.E q hq) (B : ClosedBlowupSequence u.X)
    (h : bdFunctor M n μ j { u with E := insertTop u.E q hq } = B) :
    bdFunctor M n μ j { u with E := E' } = B := by
  subst hE'
  exact h

include hlft heq hd hn hμ hMe in
private theorem bdFunctor_endOf_insertTop_of_lt (j : ℕ) (hj : j < p)
    (hT : IsTriple (t.endOf P).sX (t.endOf P).I (t.endOf P).E) :
    bdFunctor M (dimNat t.X) μ j
        (({ t with E := insertTop t.E p hp } : FieldBlowupTriple.{u}).endOf P) =
      bdFunctor M (dimNat t.X) μ j (t.endOf P) := by
  rw [dimNat_of_eq hd]
  exact bdFunctor_congr_E M n μ j (t.endOf P) (le_endOf_s t p hp P) _
    (endOf_E_insertTop t p hp P) _
    (bdFunctor_insertTop_of_lt M n μ (t.endOf P) p _ j hj hT hμ hn
      (topologicalKrullDim_target_eq t.sX heq hd P) hMe)

include hlft heq hd hn hμ hMe in
private theorem bdFunctor_endOf_insertTop_of_le (j : ℕ) (hj : p ≤ j)
    (hT : IsTriple (t.endOf P).sX (t.endOf P).I (t.endOf P).E) :
    bdFunctor M (dimNat t.X) μ (j + 1)
        (({ t with E := insertTop t.E p hp } : FieldBlowupTriple.{u}).endOf P) =
      bdFunctor M (dimNat t.X) μ j (t.endOf P) := by
  rw [dimNat_of_eq hd]
  exact bdFunctor_congr_E M n μ (j + 1) (t.endOf P) (le_endOf_s t p hp P) _
    (endOf_E_insertTop t p hp P) _
    (bdFunctor_insertTop_of_le M n μ (t.endOf P) p _ j hj hT hμ hn
      (topologicalKrullDim_target_eq t.sX heq hd P) hMe)

/-- One step of the separation loop: if the sequences after `j'` steps on `E` with the empty entry
and after `j` steps on `E` agree, and so do the `𝓑𝓓`-steps they take next, then so do the
sequences after one more step. -/
private theorem divisorSeparationAux_succ_insertTop {j j' : ℕ}
    (hprev : divisorSeparationAux M μ { t with E := insertTop t.E p hp } j' =
      divisorSeparationAux M μ t j)
    (hbd : IsTriple (t.endOf (divisorSeparationAux M μ t j)).sX
        (t.endOf (divisorSeparationAux M μ t j)).I (t.endOf (divisorSeparationAux M μ t j)).E →
      bdFunctor M (dimNat t.X) μ j'
          (({ t with E := insertTop t.E p hp } : FieldBlowupTriple.{u}).endOf
            (divisorSeparationAux M μ t j)) =
        bdFunctor M (dimNat t.X) μ j (t.endOf (divisorSeparationAux M μ t j))) :
    divisorSeparationAux M μ { t with E := insertTop t.E p hp } (j' + 1) =
      divisorSeparationAux M μ t (j + 1) := by
  rw [divisorSeparationAux.eq_2, divisorSeparationAux.eq_2]
  dsimp only
  rw [hprev]
  split_ifs with h1 h2 h2
  · exact congrArg _ (hbd h2)
  · exact (h2 ((isTriple_endOf_insertTop_iff t p hp _).1 h1)).elim
  · exact (h1 ((isTriple_endOf_insertTop_iff t p hp _).2 h2)).elim
  · rfl

include hlft heq hd hn hμ hMe in
private theorem divisorSeparationAux_insertTop_of_le :
    ∀ j ≤ p, divisorSeparationAux M μ { t with E := insertTop t.E p hp } j =
      divisorSeparationAux M μ t j
  | 0, _ => rfl
  | j + 1, hj => divisorSeparationAux_succ_insertTop M μ t p hp
      (divisorSeparationAux_insertTop_of_le j (by omega))
      (bdFunctor_endOf_insertTop_of_lt M n μ t p hp _ hlft heq hd hn hμ hMe j (by omega))

include hlft heq hd hn hμ hMe in
private theorem divisorSeparationAux_insertTop_of_ge :
    ∀ j, p ≤ j → divisorSeparationAux M μ { t with E := insertTop t.E p hp } (j + 1) =
      divisorSeparationAux M μ t j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [divisorSeparationAux.eq_2]
    dsimp only
    rw [divisorSeparationAux_insertTop_of_le M n μ t p hp hlft heq hd hn hμ hMe p le_rfl]
    split_ifs
    · exact (congrArg (divisorSeparationAux M μ t p).append
        (bdFunctor_congr_E M (dimNat t.X) μ p (t.endOf _) (le_endOf_s t p hp _) _
          (endOf_E_insertTop t p hp _) _
          (bdFunctor_insertTop_self M _ μ _ p _))).trans (append_nil _)
    · rfl
  | succ j hj ih =>
    exact divisorSeparationAux_succ_insertTop M μ t p hp ih
      (bdFunctor_endOf_insertTop_of_le M n μ t p hp _ hlft heq hd hn hμ hMe j hj)

end Loop

/-- Steps 1–2 of the proof of Kollár 3.72 for `𝓑𝓞_{n,m}`, for one empty entry: inserting an
empty entry at position `p` does not change the divisor separation sequence. In the loop the
step at the empty entry adds the empty sequence, and the other steps call `𝓑𝓓` on the same
data, the restricted divisors `E_S^♭` agreeing. -/
private theorem divisorSeparationSequence_insertTop (M : MarkedFamily.{u}) (n μ : ℕ)
    (t : FieldBlowupTriple.{u}) (p : ℕ) (hp : p ≤ t.E.s) (hlft : LocallyOfFiniteType t.sX)
    (heq : Equidimensional t.X)
    (hd : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} μ.factorial)
      (fun t _ => M (n - 1) μ.factorial t)) :
    divisorSeparationSequence M μ { t with E := insertTop t.E p hp } =
      divisorSeparationSequence M μ t :=
  divisorSeparationAux_insertTop_of_ge M n μ t p hp hlft heq hd hn hμ hMe t.E.s hp

open Classical in
/-- The part of `boMaximalContact` after the divisor separation sequence `P`, as a function of the
open set `V`, of the transform `H'` and of the appended entries `G`. -/
private noncomputable def boTail (M : MarkedFamily.{u}) (μ n : ℕ) {X : Scheme.{u}} (k : Type u)
    [Field k] (sX : X ⟶ Spec (.of k)) (P : ClosedBlowupSequence X)
    (I H' : P.target.IdealSheafData) (V : P.target.Opens) (L : ℕ)
    (G : Fin L → P.target.IdealSheafData) : ClosedBlowupSequence X :=
  let EV : OrderedDivisor V :=
    ⟨L + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
      fun i => (G i).comap V.ι⟩
  let tV : FieldBlowupTriple.{u} := ⟨⟨V, I.comap V.ι, EV⟩, k, V.ι ≫ P.toBase ≫ sX⟩
  let BV : ClosedBlowupSequence V :=
    if (V : Set P.target).Nonempty ∧ IsTriple tV.sX tV.I tV.E then bdFunctor M n μ 0 tV
    else .nil _
  (P.append (BV.extendByClosure V.ι)).reduction

/-- `boTail` with `V` the complement of the first `s` entries of `F` and `G` the others. -/
private noncomputable def boTailOf (M : MarkedFamily.{u}) (μ n : ℕ) {X : Scheme.{u}}
    (k : Type u) [Field k] (sX : X ⟶ Spec (.of k)) (P : ClosedBlowupSequence X)
    (I H' : P.target.IdealSheafData) (F : OrderedDivisor P.target) (s : ℕ) :
    ClosedBlowupSequence X :=
  boTail M μ n k sX P I H' (⨆ i : Fin F.s, if (i : ℕ) < s then (F.E i).support else ⊥).compl
    (F.s - s) fun i => F.E ⟨s + i, by omega⟩

private theorem boMaximalContact_eq_boTailOf (M : MarkedFamily.{u}) (μ : ℕ)
    (t : FieldBlowupTriple.{u}) (H : t.X.IdealSheafData) :
    boMaximalContact M μ t H = boTailOf M μ (dimNat t.X) t.k t.sX
      (divisorSeparationSequence M μ t)
      ((divisorSeparationSequence M μ t).controlledTransform t.I)
      ((divisorSeparationSequence M μ t).restrictHom H).ker
      ((divisorSeparationSequence M μ t).orderedTotalTransform t.E) t.E.s :=
  rfl

private theorem boTail_congr (M : MarkedFamily.{u}) (μ n : ℕ) {X : Scheme.{u}} (k : Type u)
    [Field k] (sX : X ⟶ Spec (.of k)) (P : ClosedBlowupSequence X)
    (I H' : P.target.IdealSheafData) {V V' : P.target.Opens} (hV : V = V') {L L' : ℕ}
    (hL : L = L') {G : Fin L → P.target.IdealSheafData} {G' : Fin L' → P.target.IdealSheafData}
    (hG : ∀ i, G i = G' (Fin.cast hL i)) :
    boTail M μ n k sX P I H' V L G = boTail M μ n k sX P I H' V' L' G' := by
  subst hV hL
  obtain rfl : G = G' := funext hG
  rfl

private theorem iSup_insertTop {X : Scheme.{u}} (F : OrderedDivisor X) (p s : ℕ)
    (hps : p ≤ s) (h' : p ≤ F.s) :
    (⨆ i : Fin (insertTop F p h').s,
        if (i : ℕ) < s + 1 then ((insertTop F p h').E i).support else ⊥) =
      ⨆ i : Fin F.s, if (i : ℕ) < s then (F.E i).support else ⊥ := by
  apply le_antisymm
  · refine iSup_le fun ⟨i, hi⟩ => ?_
    have hi' : i < F.s + 1 := hi
    simp only [insertTop]
    split_ifs with h1 h2 h3
    · exact le_iSup_of_le ⟨i, by omega⟩ (by simp [show i < s by omega])
    · simp [Scheme.IdealSheafData.support_top]
    · exact le_iSup_of_le ⟨i - 1, by omega⟩ (by simp [show i - 1 < s by omega])
    · exact bot_le
  · refine iSup_le fun ⟨i, hi⟩ => ?_
    split_ifs with h1
    · simp only [Fin.val_mk] at h1
      by_cases h2 : i < p
      · refine le_iSup_of_le ⟨i, by simp [insertTop]; omega⟩ ?_
        simp [insertTop, h2, show i < s + 1 by omega, h1]
      · refine le_iSup_of_le ⟨i + 1, by simp [insertTop]; omega⟩ ?_
        simp [insertTop, show ¬ i + 1 < p by omega, show i + 1 ≠ p by omega,
          show i + 1 < s + 1 by omega, h1]
    · exact bot_le

private theorem boTailOf_insertTop (M : MarkedFamily.{u}) (μ n : ℕ) {X : Scheme.{u}}
    (k : Type u) [Field k] (sX : X ⟶ Spec (.of k)) (P : ClosedBlowupSequence X)
    (I H' : P.target.IdealSheafData) (F : OrderedDivisor P.target) (p s : ℕ) (hps : p ≤ s)
    (h' : p ≤ F.s) :
    boTailOf M μ n k sX P I H' (insertTop F p h') (s + 1) = boTailOf M μ n k sX P I H' F s := by
  unfold boTailOf
  refine boTail_congr M μ n k sX P I H' (by rw [iSup_insertTop F p s hps h'])
    (by simp [insertTop]) fun i => ?_
  simp only [insertTop, Fin.coe_cast]
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 2
  change s + 1 + (i : ℕ) - 1 = s + (i : ℕ)
  omega

/-- Step 3 of the proof of Kollár 3.72 for `𝓑𝓞_{n,m}`, for one empty entry: with the same
divisor separation sequence, the open set `V` and the divisor `E^V` only see the supports of the
transforms of the entries and the appended exceptional entries, which agree. -/
private theorem boMaximalContact_insertTop (M : MarkedFamily.{u}) (n μ : ℕ)
    (t : FieldBlowupTriple.{u}) (p : ℕ) (hp : p ≤ t.E.s) (hlft : LocallyOfFiniteType t.sX)
    (heq : Equidimensional t.X)
    (hd : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} μ.factorial)
      (fun t _ => M (n - 1) μ.factorial t))
    (H : t.X.IdealSheafData) :
    boMaximalContact M μ { t with E := insertTop t.E p hp } H = boMaximalContact M μ t H := by
  have hP := divisorSeparationSequence_insertTop M n μ t p hp hlft heq hd hn hμ hMe
  rw [boMaximalContact_eq_boTailOf, boMaximalContact_eq_boTailOf]
  dsimp only
  rw [hP, orderedTotalTransform_insertTop _ t.E p hp (by rw [orderedTotalTransform_s]; omega)]
  exact boTailOf_insertTop M μ _ t.k t.sX _ _ _ _ p t.E.s hp _

/-- Steps 1–3 of the proof of Kollár 3.72 for `𝓑𝓞_{n,m}`: the maximal-contact functor
`𝓑𝓞^H_μ(X, J, E)` depends on `E` only through `E^♭`. -/
private theorem boMaximalContact_congr_of_deleteEmpty_eq (M : MarkedFamily.{u}) (n μ : ℕ)
    (t : FieldBlowupTriple.{u}) (E' : OrderedDivisor t.X)
    (hE : E'.deleteEmpty = t.E.deleteEmpty) (hlft : LocallyOfFiniteType t.sX)
    (heq : Equidimensional t.X)
    (hd : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} μ.factorial)
      (fun t _ => M (n - 1) μ.factorial t)) (H : t.X.IdealSheafData) :
    boMaximalContact M μ { t with E := E' } H = boMaximalContact M μ t H := by
  let P : OrderedDivisor t.X → ClosedBlowupSequence t.X := fun E =>
    boMaximalContact M μ ({ t with E := E } : FieldBlowupTriple.{u}) H
  have hins : ∀ E p hp, P (insertTop E p hp) = P E := fun E p hp =>
    boMaximalContact_insertTop M n μ { t with E := E } p hp hlft heq hd hn hμ hMe H
  exact eq_of_deleteEmpty_eq P hins hE

/-- Step 4: `𝓑_{n,m}` on local triples depends on `E` only through `E^♭`. -/
private theorem boLocal_congr_of_deleteEmpty_eq (M : MarkedFamily.{u}) (n m : ℕ)
    (t : FieldBlowupTriple.{u}) (E' : OrderedDivisor t.X) (hE : E'.deleteEmpty = t.E.deleteEmpty)
    (ht : t ∈ mcLocalTriples n m) (hn : 1 ≤ n)
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} m.factorial.factorial)
      (fun t _ => M (n - 1) m.factorial.factorial t)) :
    boLocal M m { t with E := E' } = boLocal M m t := by
  obtain ⟨⟨-, -, hlft, -, heq, -, -⟩, ⟨n', hn', hd⟩, -⟩ := ht
  rw [Set.mem_singleton_iff] at hn'
  subst hn'
  unfold boLocal
  split_ifs with h
  · rfl
  · exact boMaximalContact_congr_of_deleteEmpty_eq M n' m.factorial
      ⟨⟨t.X, wellTunedIdeal t.sX t.I, t.E⟩, t.k, t.sX⟩ E' hE hlft heq hd hn
      (Nat.factorial_pos _) hMe (mcHypersurfaceChoice t)

/-- Membership in `𝓛𝓣_{n,m}` does not see the empty entries of the divisor. -/
private theorem mem_mcLocalTriples_iff {n m : ℕ} (t : FieldBlowupTriple.{u})
    (E' : OrderedDivisor t.X) (hE : E'.deleteEmpty = t.E.deleteEmpty) :
    { t with E := E' } ∈ mcLocalTriples n m ↔ t ∈ mcLocalTriples n m := by
  simp only [mcLocalTriples, triples, Set.mem_setOf_eq]
  rw [isTriple_iff_of_deleteEmpty_eq t.sX t.I hE]

open Classical in
/-- `𝓑𝓞_{n,m}` does not change from `(X, I, E)` to `(X, I, E^♭)` once membership in `𝓛𝓣_{n,m}`
and the values of `𝓑_{n,m}` do not change along any pull-back: the two sequences are chosen by
the same defining property. -/
private theorem boFunctor_deleteEmpty_eq (M : MarkedFamily.{u}) (n m : ℕ)
    (t : FieldBlowupTriple.{u})
    (hmem : ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X),
      t.deleteEmpty.pullback g ∈ mcLocalTriples n m ↔ t.pullback g ∈ mcLocalTriples n m)
    (hloc : ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X), t.pullback g ∈ mcLocalTriples n m →
      boLocal M m (t.deleteEmpty.pullback g) = boLocal M m (t.pullback g)) :
    boFunctor M n m t.deleteEmpty = boFunctor M n m t := by
  have hP : (fun B : ClosedBlowupSequence t.X => ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X),
      IsOpenCoverMap g → Surjective g → t.deleteEmpty.pullback g ∈ mcLocalTriples n m →
        B.pullback g = boLocal M m (t.deleteEmpty.pullback g)) =
      fun B => ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X),
        IsOpenCoverMap g → Surjective g → t.pullback g ∈ mcLocalTriples n m →
          B.pullback g = boLocal M m (t.pullback g) :=
    funext fun B => propext <| forall₂_congr fun X' g => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_ctx (hmem X' g) fun hl => by
        rw [hloc X' g hl]
        exact Iff.rfl
  exact congrArg (fun P : ClosedBlowupSequence t.X → Prop =>
    if h : ∃ B, P B then h.choose else ClosedBlowupSequence.nil t.X) hP

/-- **`𝓑𝓞_{n,m}` ignores empty entries** (needed for Kollár 3.72). Let `n ≥ 1`, `𝓜` a marked
order-reduction family on dimensions `0, …, n - 1` (`IsMarkedOrderReductionFamily`) each of whose
members `𝓜_{d,μ}`, `d ≤ n - 1`, `μ ≥ 1`, ignores empty entries on the marked triples of marking
`μ` and dimension `d` (`IgnoresEmptyEntriesMarked`), and `m ≥ 1`. Then `boFunctor M n m` ignores
empty entries on the triples of dimension `n` with `maxord I ≤ m` (`IgnoresEmptyEntries`). -/
@[mmp "lem_kr3e_bo_ignores_empty_entries"]
public theorem ignoresEmptyEntries_boFunctor {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (hMe : ∀ d ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t))
    (hm : 1 ≤ m) :
    IgnoresEmptyEntries (idealTriplesOfDim {n} m) (fun t _ => boFunctor M n m t) := by
  intro t ht
  have hE := deleteEmpty_deleteEmpty t.E
  exact ⟨⟨(isTriple_iff_of_deleteEmpty_eq t.sX t.I hE).2 ht.1, ht.2⟩,
    boFunctor_deleteEmpty_eq M n m t
      (fun _ g => mem_mcLocalTriples_iff (t.pullback g) _ (deleteEmpty_comap_eq hE g))
      fun _ g hl => boLocal_congr_of_deleteEmpty_eq M n m (t.pullback g) _
        (deleteEmpty_comap_eq hE g) hl hn
        (hMe (n - 1) ⟨Nat.zero_le _, le_rfl⟩ _ (Nat.factorial_pos _))⟩

end MMP.Resolution

namespace MMP.Resolution.ClosedBlowupSequence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- An ideal sheaf contained in one of order `≥ 1` along a smooth centre `Z` of a smooth scheme
is contained in the ideal sheaf of `Z`. -/
private theorem le_of_le_of_orderAlongGE_one {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) {K I : X.IdealSheafData} (hKI : K ≤ I)
    (hI : OrderAlongGE I (Z.support : Set X) ((1 : ℕ) : ℕ∞)) : K ≤ Z := by
  refine hKI.trans (IdealSheafData.le_of_stalk_le _ _ fun x => ?_)
  simpa using stalk_le_pow_of_orderAlongGE sX hX Z hZ I 1 hI x

/-- An effective Cartier divisor can be cancelled from an inclusion: `A·D ≤ B·D` forces
`A ≤ B`. -/
private theorem le_of_mul_le_mul_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    {A B D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (h : A * D ≤ B * D) : A ≤ B := by
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  obtain ⟨g, hg, hgs⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D hD y
  have hy := MMP.Resolution.stalk_le_stalk_of_le h y
  simp only [IdealSheafData.stalk_mul, hgs] at hy
  intro x hx
  have hxg : x * g ∈ IdealSheafData.stalk B y * Ideal.span {g} :=
    hy (Ideal.mul_mem_mul hx (Ideal.mem_span_singleton_self g))
  obtain ⟨b, hb, hbg⟩ := Ideal.mem_mul_span_singleton.mp hxg
  rw [hg.2 hbg] at hb
  exact hb

/-- The canonical lift of a closed immersion `j` has the same ideal sheaf as the canonical lift
of the closed immersion of the subscheme cut out by `ker j`. -/
private theorem ker_canonicalLift_eq {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (Z : X.IdealSheafData) :
    (canonicalLift j Z).ker = (canonicalLift j.ker.subschemeι Z).ker := by
  have hiso : IsIso j.toImage :=
    IsClosedImmersion.isIso_of_ker_eq j j.imageι j.toImage j.toImage_imageι (by simp)
  have key : ∀ (t : S ⟶ j.image) [IsIso t] (g : j.image ⟶ X),
      (canonicalLift (t ≫ g) Z).ker = (canonicalLift g Z).ker := by
    intro t _ g
    have : IsIso (canonicalLift t (Z.comap g)) := MMP.Resolution.Kollar.isIso_canonicalLift t _
    rw [← Scheme.Hom.ker_comp_of_isIso (eqToHom (congrArg blowUp
        (Scheme.IdealSheafData.comap_comp Z t g).symm)),
      ← canonicalLift_comp_canonicalLift, Scheme.Hom.ker_comp_of_isIso]
  conv_lhs => rw [← j.toImage_imageι]
  exact key j.toImage j.imageι

/-- Along a sequence of order `≥ 1` for a marked ideal `b` with `b.m = 1`, the pull-back of a
closed immersion `j` cut out by a smooth hypersurface inside `b.I` stays a smooth hypersurface
contained in the iterated marked transform of `b`. -/
private theorem ker_pullbackHom_le_markedTransform {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k))
    (b : MarkedIdeal X) (hb : b.m = 1) (hB : IsOrderGePlainSeq sX b B)
    {S : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (hH : IsSmoothHypersurface sX j.ker) (hle : j.ker ≤ b.I) :
    (B.pullbackHom j).ker ≤ (B.markedTransform b).I ∧
      IsSmoothHypersurface (B.toBase ≫ sX) (B.pullbackHom j).ker := by
  induction B generalizing S with
  | nil X =>
    refine ⟨hle, ?_⟩
    change IsSmoothHypersurface (𝟙 X ≫ sX) j.ker
    rwa [Category.id_comp]
  | cons Z₀ B'' ih =>
    obtain ⟨hX, -, hZ₀, hcodim, hord, hB''⟩ := hB
    have hK : j.ker ≤ Z₀ := le_of_le_of_orderAlongGE_one sX hX Z₀ hZ₀ hle (hb ▸ hord)
    have hlift := MMP.Resolution.ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hX j.ker Z₀
      hH hZ₀ hK
    have : IsClosedImmersion (canonicalLift j Z₀) :=
      MMP.Resolution.Bridges.isClosedImmersion_canonicalLift j Z₀
    have hbt := MarkedIdeal.birationalTransform_mul_eq sX hX Z₀ hZ₀ hcodim b hord
    rw [hb, pow_one] at hbt
    have h := ih _ (b.birationalTransform Z₀) hb hB'' (canonicalLift j Z₀)
      (by rw [ker_canonicalLift_eq]; exact hlift.2.2)
      (le_of_mul_le_mul_of_isEffectiveCartierDivisor
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z₀)
        (by rw [hbt, ker_canonicalLift_eq, hlift.2.1]
            exact Scheme.IdealSheafData.comap_mono _ hle))
    refine ⟨h.1, ?_⟩
    change IsSmoothHypersurface ((B''.toBase ≫ blowUpToBase Z₀) ≫ sX)
      (B''.pullbackHom (canonicalLift j Z₀)).ker
    rw [Category.assoc]
    exact h.2

/-- A smooth blow-up sequence of order `≥ m` starting with a marked triple is one starting with
the underlying marked ideal. -/
private theorem isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq sX a E → IsOrderGePlainSeq sX a B
  | _, nil _, _, _, _, h => ⟨h.2.1, h.2.2.2.2.2.1⟩
  | _, cons _ B, _, _, _, h =>
    ⟨h.1.2.1, h.1.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.1,
      isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq B _ _ _ h.2.2.2.2.2⟩

private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [ih]

/-- If `maxord K = m`, the maximal-contact ideal of `K` is `D^{m-1}K`. -/
private theorem maximalContactIdeal_eq_of_maxOrder_eq {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) {K : Y.IdealSheafData} {m : ℕ}
    (hK : maxOrder K = m) : maximalContactIdeal s K = higherDerivativeIdeal s K (m - 1) := by
  rw [maximalContactIdeal, hK, ENat.toNat_coe]

/-- **Kollár, Lemma 3.103 Step 2.** Let `X` be a smooth scheme over a field `k` of
characteristic zero with `dim X ≥ 1`, `I` an ideal sheaf with `m = maxord I ≥ 1`, `H` an
MC-hypersurface for `I`, and `B` a smooth blow-up sequence of order `m` starting with the triple
`(X, I, E)`. If the last controlled transform `I_r = B.controlledTransform I` still has maximal
order `m`, then the birational transform `H_r = ker (B.restrictHom H)` of `H` is an
MC-hypersurface for `I_r` on `X_r = B.target`. -/
@[mmp "lem_kr3e_maximal_contact_birational_transform"]
public theorem IsOrderMTripleSeq.isMCHypersurface_ker_restrictHom {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hdim : 1 ≤ topologicalKrullDim X)
    {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m) (hI : maxOrder I = m)
    {H : X.IdealSheafData} (hH : IsMCHypersurface sX I H)
    {E : OrderedDivisor X} {B : ClosedBlowupSequence X} (hB : IsOrderMTripleSeq sX I E m B)
    (hr : maxOrder (B.controlledTransform I) = m) :
    IsMCHypersurface (B.toBase ≫ sX) (B.controlledTransform I) (B.restrictHom H).ker := by
  have hT : IsTriple sX I E := by cases B <;> [exact hB; exact hB.1]
  obtain ⟨hchar, -, hlft, hqc, hequi, hnz, -⟩ := id hT
  haveI := hchar; haveI := hlft; haveI := hqc
  have hdim' := pos_dim_of_equidimensional hequi hdim
  have hiff := isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq sX I E hT m hI B
  have hplain : IsOrderGePlainSeq sX ⟨I, m⟩ B :=
    isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq B sX _ E (hiff.1.2 hB)
  have hctrl := hiff.2 hB
  obtain ⟨hB₁, hJ⟩ := isOrderGePlainSeq_higherDerivativeIdeal sX hequi hdim' ⟨I, m⟩ hnz B
    hplain (m - 1) (Nat.sub_le _ _)
  have hJle := derivedTransformJ_truncate_le_higherDerivativeIdeal sX hequi hdim'
    ⟨I, m⟩ hnz B hplain B.length le_rfl (m - 1) (Nat.sub_le _ _)
  simp only [hJ B.length le_rfl, Option.some.injEq, exists_eq_left'] at hJle
  rw [truncate_length] at hJle
  obtain ⟨hle, hsm⟩ := ker_pullbackHom_le_markedTransform B sX
    ⟨higherDerivativeIdeal sX I (m - 1), m - (m - 1)⟩ (by change m - (m - 1) = 1; omega) hB₁
    H.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hH.1)
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ← maximalContactIdeal_eq_of_maxOrder_eq sX hI]
        exact hH.2)
  refine ⟨hsm, ?_⟩
  rw [maximalContactIdeal_eq_of_maxOrder_eq _ hr, ← hctrl]
  exact hle.trans hJle

end MMP.Resolution.ClosedBlowupSequence

end
