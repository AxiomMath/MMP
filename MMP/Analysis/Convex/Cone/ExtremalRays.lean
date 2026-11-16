module

public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Extremal rays and faces of closed convex cones (KM 1.15, 3.3)

Let `V` be a finite-dimensional real vector space.

* A closed convex cone `N ⊆ V` with `N ∩ (-N) = {0}` is spanned by its extremal rays: every
  element of `N` is a finite sum of elements of extremal rays of `N`.
* A convex extremal face of a closed convex cone is closed.
* If `C = C' + R₁ + ⋯ + R_k` for a closed convex cone `C' ⊆ C` and rays `Rᵢ ⊆ C`, a convex extremal
  face `F` of `C` with `F ∩ C' = {0}` is the sum of the rays `Rᵢ` contained in `F`.

## Main results

* `MMP.Positivity.exists_sum_mem_isExtremalRay`
* `MMP.Positivity.IsExtremalFace.isClosed`
* `MMP.Positivity.IsExtremalFace.eq_sum_rays`
-/

@[expose] public noncomputable section

namespace MMP.Positivity

open MMP.Mori

section Helpers

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- A cone contains the nonnegative multiples of its elements. -/
theorem smul_mem_of_isCone {N : Set W} (hN : IsCone ℝ N) {x : W} (hx : x ∈ N) {c : ℝ}
    (hc : 0 ≤ c) : c • x ∈ N := by
  rcases hc.lt_or_eq with hc | rfl
  · exact hN.2 x hx c hc
  · simpa using hN.1

/-- A convex cone is closed under addition. -/
theorem add_mem_of_isCone_of_convex {N : Set W} (hN : IsCone ℝ N) (hNc : Convex ℝ N) {u w : W}
    (hu : u ∈ N) (hw : w ∈ N) : u + w ∈ N := by
  have h := hN.2 _ (hNc hu hw (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)) 2 two_pos
  convert h using 1
  rw [smul_add, smul_smul, smul_smul]
  norm_num

/-- An element of the span of a convex cone `N` is a difference of two elements of `N`. -/
theorem exists_sub_of_mem_span {N : Set W} (hN : IsCone ℝ N) (hNc : Convex ℝ N) {x : W}
    (hx : x ∈ Submodule.span ℝ N) : ∃ a ∈ N, ∃ b ∈ N, x = a - b := by
  obtain ⟨P, rfl⟩ := (isCone_and_add_mem_iff N).1
    ⟨hN, fun u hu w hw => add_mem_of_isCone_of_convex hN hNc hu hw⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨x, hx, 0, P.zero_mem, (sub_zero x).symm⟩
  | zero => exact ⟨0, P.zero_mem, 0, P.zero_mem, (sub_zero 0).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    exact ⟨a + a', P.add_mem ha ha', b + b', P.add_mem hb hb', by abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rcases le_total 0 c with hc | hc
    · exact ⟨c • a, P.smul_mem hc ha, c • b, P.smul_mem hc hb, smul_sub _ _ _⟩
    · refine ⟨(-c) • b, P.smul_mem (neg_nonneg.2 hc) hb, (-c) • a,
        P.smul_mem (neg_nonneg.2 hc) ha, ?_⟩
      rw [neg_smul, neg_smul, smul_sub]
      abel

/-- An extremal face of an extremal face of `N` is an extremal face of `N`. -/
theorem isExtremalFace_trans {N F R : Set W} (hF : IsExtremalFace ℝ N F)
    (hR : IsExtremalFace ℝ F R) : IsExtremalFace ℝ N R :=
  ⟨hR.1.trans hF.1, hR.2.1, hR.2.2.1, fun u hu v hv huv =>
    let h := hF.2.2.2 u hu v hv (hR.1 huv)
    hR.2.2.2 u h.1 v h.2 huv⟩

/-- If `p ∈ N` and `p + ε u ∉ N` for every `ε > 0`, where `u` lies in the span of the convex
cone `N`, then `p` lies in a convex extremal face of `N` whose span is strictly smaller than the
span of `N`. -/
theorem exists_isExtremalFace_span_lt {N : Set W} (hN : IsCone ℝ N) (hNc : Convex ℝ N) {p u : W}
    (hp : p ∈ N) (hu : u ∈ Submodule.span ℝ N) (hpu : ∀ ε : ℝ, 0 < ε → p + ε • u ∉ N) :
    ∃ F : Set W, IsExtremalFace ℝ N F ∧ Convex ℝ F ∧ p ∈ F ∧
      Submodule.span ℝ F < Submodule.span ℝ N := by
  set F : Set W := {x | x ∈ N ∧ ∃ t : ℝ, 0 < t ∧ t • p - x ∈ N} with hFdef
  have hFN : F ⊆ N := fun x hx => hx.1
  have hFcone : IsCone ℝ F := by
    refine ⟨⟨hN.1, 1, one_pos, by simpa using hp⟩, fun x hx c hc => ?_⟩
    obtain ⟨hxN, t, ht, hxt⟩ := hx
    refine ⟨hN.2 x hxN c hc, c * t, mul_pos hc ht, ?_⟩
    have := hN.2 _ hxt c hc
    rwa [smul_sub, smul_smul] at this
  have hFadd : ∀ x ∈ F, ∀ y ∈ F, x + y ∈ F := by
    rintro x ⟨hxN, t, ht, hxt⟩ y ⟨hyN, s, hs, hys⟩
    refine ⟨add_mem_of_isCone_of_convex hN hNc hxN hyN, t + s, add_pos ht hs, ?_⟩
    have := add_mem_of_isCone_of_convex hN hNc hxt hys
    convert this using 1
    rw [add_smul]
    abel
  have hFext : IsExtremalFace ℝ N F := by
    refine ⟨hFN, hFcone, hFadd, fun x hx y hy hxy => ?_⟩
    obtain ⟨-, t, ht, hxyt⟩ := hxy
    refine ⟨⟨hx, t, ht, ?_⟩, ⟨hy, t, ht, ?_⟩⟩
    · have := add_mem_of_isCone_of_convex hN hNc hxyt hy
      rwa [sub_add_eq_sub_sub, sub_add_cancel] at this
    · have := add_mem_of_isCone_of_convex hN hNc hxyt hx
      rwa [add_comm x y, sub_add_eq_sub_sub, sub_add_cancel] at this
  have hFc : Convex ℝ F := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hxN, t, ht, hxt⟩ := hx
    obtain ⟨hyN, s, hs, hys⟩ := hy
    refine ⟨hNc hxN hyN ha hb hab, a * t + b * s, ?_, ?_⟩
    · rcases ha.lt_or_eq with ha' | rfl
      · positivity
      · simp only [zero_add] at hab
        subst hab
        simpa using hs
    · have := hNc hxt hys ha hb hab
      convert this using 1
      simp only [smul_sub, add_smul, smul_smul]
      abel
  refine ⟨F, hFext, hFc, ⟨hp, 1, one_pos, by simpa using hN.1⟩,
    lt_of_le_of_ne (Submodule.span_mono hFN) fun heq => ?_⟩
  rw [← heq] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub_of_mem_span hFcone hFc hu
  obtain ⟨-, t, ht, hbt⟩ := hb
  apply hpu t⁻¹ (inv_pos.2 ht)
  have := add_mem_of_isCone_of_convex hN hNc (hN.2 a ha.1 t⁻¹ (inv_pos.2 ht))
    (hN.2 _ hbt t⁻¹ (inv_pos.2 ht))
  convert this using 1
  rw [smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  abel

/-- A salient convex cone all of whose elements are real multiples of a fixed nonzero `v ∈ N` is
an extremal ray of itself. -/
theorem isExtremalRay_self_of_forall_eq_smul {N : Set W} (hN : IsCone ℝ N) (hNc : Convex ℝ N)
    (hNs : N ∩ -N = {0}) {v : W} (hv : v ∈ N) (hv0 : v ≠ 0)
    (hall : ∀ w₀ ∈ N, ∃ c : ℝ, w₀ = c • v) : IsExtremalRay ℝ N N := by
  refine ⟨⟨subset_rfl, hN, fun u hu w hw => add_mem_of_isCone_of_convex hN hNc hu hw,
    fun u hu w hw _ => ⟨hu, hw⟩⟩, v, hv0, ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun ⟨c, hc, hcx⟩ => hcx ▸ smul_mem_of_isCone hN hv hc⟩
  obtain ⟨c, rfl⟩ := hall x hx
  refine ⟨c, not_lt.1 fun hc => hv0 ?_, rfl⟩
  have hneg : -v ∈ N := by
    have := hN.2 _ hx (-c)⁻¹ (inv_pos.2 (neg_pos.2 hc))
    rwa [smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hc.ne, neg_smul, one_smul] at this
  have : v ∈ N ∩ -N := ⟨hv, by simpa using hneg⟩
  rwa [hNs] at this

end Helpers

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]

/-- The ray `ℝ_{≥0} · v`. -/
def ray (v : V) : Set V := {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}

/-- A convex extremal face of a closed cone is closed (the proof of
`MMP.Positivity.IsExtremalFace.isClosed`). -/
theorem isClosed_of_isExtremalFace {C F : Set V} (hCcl : IsClosed C) (hF : IsExtremalFace ℝ C F)
    (hFc : Convex ℝ F) : IsClosed F := by
  refine closure_subset_iff_isClosed.1 fun x hx => ?_
  have hxC : x ∈ C := closure_minimal hF.1 hCcl hx
  have hxS : x ∈ Submodule.span ℝ F :=
    closure_minimal Submodule.subset_span (Submodule.closed_of_finiteDimensional _) hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub_of_mem_span hF.2.1 hFc hxS
  exact (hF.2.2.2 (a - b) hxC b (hF.1 hb) (by simpa using ha)).1

omit [T2Space V] [FiniteDimensional ℝ V] in
/-- For `x, w` in a closed salient convex cone `N` with `w ≠ 0`, there is a largest `t ≥ 0` with
`x - t w ∈ N`. -/
theorem exists_sub_smul_mem_maximal {N : Set V} (hN : IsCone ℝ N) (hNc : Convex ℝ N)
    (hNcl : IsClosed N) (hNs : N ∩ -N = {0}) {x w : V} (hx : x ∈ N) (hw : w ∈ N) (hw0 : w ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ x - t • w ∈ N ∧ ∀ ε : ℝ, 0 < ε → x - t • w + ε • (-w) ∉ N := by
  set T : Set ℝ := {t | 0 ≤ t ∧ x - t • w ∈ N} with hTdef
  have hTcl : IsClosed T :=
    isClosed_Ici.inter (hNcl.preimage (continuous_const.sub (continuous_id.smul continuous_const)))
  have hTne : T.Nonempty := ⟨0, le_rfl, by simpa using hx⟩
  have hTbdd : BddAbove T := by
    by_contra hb
    rw [not_bddAbove_iff] at hb
    have hall : ∀ s : ℝ, 0 < s → s • x - w ∈ N := by
      intro s hs
      obtain ⟨t', ⟨-, ht'⟩, hlt⟩ := hb s⁻¹
      have h1 := add_mem_of_isCone_of_convex hN hNc ht'
        (hN.2 w hw (t' - s⁻¹) (sub_pos.2 hlt))
      have h2 := hN.2 _ h1 s hs
      convert h2 using 1
      rw [sub_smul, smul_add, smul_sub, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hs.ne',
        one_smul]
      abel
    have hlim : Filter.Tendsto (fun s : ℝ => s • x - w) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-w)) := by
      have hc : Continuous fun s : ℝ => s • x - w :=
        (continuous_id.smul continuous_const).sub continuous_const
      have := hc.continuousAt (x := 0) |>.tendsto
      simp only [zero_smul, zero_sub] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hmem : -w ∈ N := hNcl.mem_of_tendsto hlim
      (eventually_nhdsWithin_of_forall fun s hs => hall s hs)
    have : w ∈ N ∩ -N := ⟨hw, by simpa using hmem⟩
    rw [hNs] at this
    exact hw0 this
  obtain ⟨ht0, htN⟩ := hTcl.csSup_mem hTne hTbdd
  refine ⟨sSup T, ht0, htN, fun ε hε hmem => ?_⟩
  have : sSup T + ε ∈ T := ⟨by linarith, by
    convert hmem using 1
    rw [add_smul, smul_neg]
    abel⟩
  linarith [le_csSup hTbdd this]

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [FiniteDimensional ℝ V] in
/-- Sums of finitely many elements of extremal rays can be added. -/
theorem exists_sum_add {N : Set V} {a b : V}
    (ha : ∃ (s : ℕ) (R : Fin s → Set V) (w : Fin s → V),
      (∀ i, IsExtremalRay ℝ N (R i) ∧ w i ∈ R i) ∧ a = ∑ i, w i)
    (hb : ∃ (s : ℕ) (R : Fin s → Set V) (w : Fin s → V),
      (∀ i, IsExtremalRay ℝ N (R i) ∧ w i ∈ R i) ∧ b = ∑ i, w i) :
    ∃ (s : ℕ) (R : Fin s → Set V) (w : Fin s → V),
      (∀ i, IsExtremalRay ℝ N (R i) ∧ w i ∈ R i) ∧ a + b = ∑ i, w i := by
  obtain ⟨s, R, w, hR, rfl⟩ := ha
  obtain ⟨s', R', w', hR', rfl⟩ := hb
  refine ⟨s + s', Fin.append R R', Fin.append w w', fun i => ?_, by simp [Fin.sum_univ_add]⟩
  induction i using Fin.addCases with
  | left j => simpa using hR j
  | right j => simpa using hR' j

/-- The induction behind `MMP.Positivity.exists_sum_mem_isExtremalRay`, on the dimension of the
span of the cone. -/
theorem exists_sum_mem_isExtremalRay_of_finrank_le (n : ℕ) :
    ∀ {N : Set V}, IsCone ℝ N → Convex ℝ N → IsClosed N → N ∩ -N = {0} →
      Module.finrank ℝ (Submodule.span ℝ N) ≤ n → ∀ {v : V}, v ∈ N →
      ∃ (s : ℕ) (R : Fin s → Set V) (w : Fin s → V),
        (∀ i, IsExtremalRay ℝ N (R i) ∧ w i ∈ R i) ∧ v = ∑ i, w i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hN hNc hNcl hNs hn v hv
  by_cases hv0 : v = 0
  · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp [hv0]⟩
  have key : ∀ p u : V, p ∈ N → u ∈ Submodule.span ℝ N → (∀ ε : ℝ, 0 < ε → p + ε • u ∉ N) →
      ∃ (s : ℕ) (R : Fin s → Set V) (w : Fin s → V),
        (∀ i, IsExtremalRay ℝ N (R i) ∧ w i ∈ R i) ∧ p = ∑ i, w i := by
    intro p u hp hu hpu
    obtain ⟨F, hFN, hFc, hpF, hlt⟩ := exists_isExtremalFace_span_lt hN hNc hp hu hpu
    have hFcl := isClosed_of_isExtremalFace hNcl hFN hFc
    have hFs : F ∩ -F = {0} := by
      refine Set.Subset.antisymm ?_ ?_
      · rw [← hNs]
        exact Set.inter_subset_inter hFN.1 (Set.neg_subset_neg.2 hFN.1)
      · rintro _ rfl
        exact ⟨hFN.2.1.1, by simpa using hFN.2.1.1⟩
    obtain ⟨s, R, w, hR, hsum⟩ :=
      ih _ ((Submodule.finrank_lt_finrank_of_lt hlt).trans_le hn) hFN.2.1 hFc hFcl hFs le_rfl hpF
    exact ⟨s, R, w, fun i => ⟨⟨isExtremalFace_trans hFN (hR i).1.1, (hR i).1.2⟩, (hR i).2⟩,
      hsum⟩
  by_cases hall : ∀ w₀ ∈ N, ∃ c : ℝ, w₀ = c • v
  · exact ⟨1, fun _ => N, fun _ => v,
      fun _ => ⟨isExtremalRay_self_of_forall_eq_smul hN hNc hNs hv hv0 hall, hv⟩, by simp⟩
  push Not at hall
  obtain ⟨w₀, hw₀, hw₀v⟩ := hall
  obtain ⟨s₀, -, hwN, hwb⟩ := exists_sub_smul_mem_maximal hN hNc hNcl hNs hw₀ hv hv0
  have hw0 : w₀ - s₀ • v ≠ 0 := fun h => hw₀v s₀ (sub_eq_zero.1 h)
  obtain ⟨t, ht, haN, hab⟩ := exists_sub_smul_mem_maximal hN hNc hNcl hNs hv hwN hw0
  have ha := key _ _ haN (neg_mem (Submodule.subset_span hwN)) hab
  obtain ⟨s, R, w, hR, hsum⟩ :=
    key _ _ hwN (neg_mem (Submodule.subset_span hv)) hwb
  have hb : ∃ (s : ℕ) (R : Fin s → Set V) (w : Fin s → V),
      (∀ i, IsExtremalRay ℝ N (R i) ∧ w i ∈ R i) ∧ t • (w₀ - s₀ • v) = ∑ i, w i :=
    ⟨s, R, fun i => t • w i, fun i => ⟨(hR i).1, smul_mem_of_isCone (hR i).1.1.2.1 (hR i).2 ht⟩,
      by rw [hsum, Finset.smul_sum]⟩
  have := exists_sum_add ha hb
  rwa [sub_add_cancel] at this

/-- **KM Def. 1.15, last sentence (corrected).** Let `N ⊆ V` be a closed convex cone with
`N ∩ (-N) = {0}`. Then every element of `N` is a finite sum `v₁ + ⋯ + v_s` (`s ≥ 0`) of elements
`vᵢ ∈ Rᵢ` of extremal rays `Rᵢ` of `N`. -/
@[mmp "lem_km1b_closed_convex_cone_hull_of_extremal_rays"]
theorem exists_sum_mem_isExtremalRay {N : Set V} (hN : IsCone ℝ N) (hNc : Convex ℝ N)
    (hNcl : IsClosed N) (hNs : N ∩ -N = {0}) {v : V} (hv : v ∈ N) :
    ∃ (s : ℕ) (R : Fin s → Set V) (w : Fin s → V),
      (∀ i, IsExtremalRay ℝ N (R i) ∧ w i ∈ R i) ∧ v = ∑ i, w i :=
  exists_sum_mem_isExtremalRay_of_finrank_le _ hN hNc hNcl hNs le_rfl hv

/-- **Convex faces are closed** (used in KM 3.3 Step 6). Let `C ⊆ V` be a closed convex cone and
`F` an extremal face of `C` which is convex. Then `F` is closed. Only closedness of `C` is used. -/
@[mmp "lem_km3b_cone_convex_face_closed"]
theorem IsExtremalFace.isClosed {C F : Set V} (hCcl : IsClosed C) (hF : IsExtremalFace ℝ C F)
    (hFc : Convex ℝ F) : IsClosed F :=
  isClosed_of_isExtremalFace hCcl hF hFc

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [FiniteDimensional ℝ V] in
/-- **KM 3.3 Step 6, "`F` is spanned by extremal rays".** Let `C ⊆ V` be a closed convex cone,
`C' ⊆ C` a closed convex cone and `R₁, …, R_k ⊆ C` rays with `C = C' + R₁ + ⋯ + R_k`, and let `F`
be a convex extremal face of `C` with `F ∩ C' = {0}`. Then `F = ∑_{i : Rᵢ ⊆ F} Rᵢ`. Neither
topology nor closedness, nor that `C'` is a cone or the `vᵢ` are nonzero, is used. -/
@[mmp "lem_km3b_cone_face_spanned_by_rays"]
theorem IsExtremalFace.eq_sum_rays {C C' F : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C)
    (hC'C : C' ⊆ C) {k : ℕ} (v : Fin k → V) (hvC : ∀ i, ray (v i) ⊆ C)
    (hsum : C = {x | ∃ c ∈ C', ∃ r : Fin k → V, (∀ i, r i ∈ ray (v i)) ∧ x = c + ∑ i, r i})
    (hF : IsExtremalFace ℝ C F) (hFc : Convex ℝ F) (hFC' : F ∩ C' = {0}) :
    F = {x | ∃ r : Fin k → V, (∀ i, r i ∈ ray (v i)) ∧ (∀ i, ¬ ray (v i) ⊆ F → r i = 0) ∧
      x = ∑ i, r i} := by
  have hCsum : ∀ (s : Finset (Fin k)) (r : Fin k → V), (∀ i, r i ∈ ray (v i)) →
      ∑ i ∈ s, r i ∈ C := by
    intro s r hr
    induction s using Finset.induction_on with
    | empty => simpa using hC.1
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact add_mem_of_isCone_of_convex hC hCc (hvC j (hr j)) ih
  have hFsum : ∀ (s : Finset (Fin k)) (r : Fin k → V), (∀ i ∈ s, r i ∈ F) →
      ∑ i ∈ s, r i ∈ F := by
    intro s r hr
    induction s using Finset.induction_on with
    | empty => simpa using hF.2.1.1
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact add_mem_of_isCone_of_convex hF.2.1 hFc (hr j (Finset.mem_insert_self j s))
        (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))
  ext x
  constructor
  · intro hx
    have hxC := hF.1 hx
    rw [hsum] at hxC
    obtain ⟨c, hc, r, hr, rfl⟩ := hxC
    have h1 := hF.2.2.2 c (hC'C hc) _ (hCsum Finset.univ r hr) hx
    have hc0 : c = 0 := by
      have : c ∈ F ∩ C' := ⟨h1.1, hc⟩
      rwa [hFC'] at this
    have hrF : ∀ i, r i ∈ F := by
      intro i
      have hsplit := Finset.add_sum_erase Finset.univ r (Finset.mem_univ i)
      exact (hF.2.2.2 (r i) (hvC i (hr i)) _ (hCsum _ r hr) (hsplit ▸ h1.2)).1
    refine ⟨r, hr, fun i hi => ?_, by rw [hc0, zero_add]⟩
    obtain ⟨t, ht, hti⟩ := hr i
    rcases ht.lt_or_eq with ht | rfl
    · refine absurd ?_ hi
      rintro _ ⟨c', hc', rfl⟩
      have := smul_mem_of_isCone hF.2.1 (hrF i) (div_nonneg hc' ht.le : 0 ≤ c' / t)
      rwa [← hti, smul_smul, div_mul_cancel₀ _ ht.ne'] at this
    · rw [← hti, zero_smul]
  · rintro ⟨r, hr, hr0, rfl⟩
    refine hFsum _ r fun i _ => ?_
    by_cases hi : ray (v i) ⊆ F
    · exact hi (hr i)
    · rw [hr0 i hi]
      exact hF.2.1.1

end MMP.Positivity
