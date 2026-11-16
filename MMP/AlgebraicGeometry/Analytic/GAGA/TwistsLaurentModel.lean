module

public import MMP.Topology.Sheaves.GodementFlasqueResolution
public import MMP.Topology.Sheaves.GodementOpenEmbedding
public import MMP.AlgebraicGeometry.AnalytificationStalk
public import MMP.Algebra.Category.ModuleCat.Sheaf.PullbackStalk
public import MMP.Analysis.Complex.CauchyOsgoodLaurent

/-!
# GAGA for the twisting sheaves of `ℙᴺ_ℂ`: Laurent models

This file models the ordered Čech complexes of the twisting sheaf `𝒪(k)` on `ℙᴺ_ℂ` and of its
analytification by Laurent coefficients. The convergent Laurent cochains deformation retract onto
the polynomial ones. Quasi-coherent modules have no higher Godement cohomology on affine opens.
Holomorphic functions on products of planes and punctured planes have unique absolutely
convergent Laurent expansions. On the standard charts of `(ℙᴺ_ℂ)^an`, the sections of `𝒪(k)^an`
over the opens `W(S) = α⁻¹ D₊(∏_{i ∈ S} xᵢ)` are given by convergent homogeneous Laurent series.

## Main definitions

* `anComplex`: The complex of absolutely convergent Laurent cochains.
* `polyComplex`: The complex of Laurent polynomial cochains.
* `stdChart`: The polynomial chart of the standard open `U_j` of `ℙᴺ_ℂ`.
* `secVal`: The value at a point of a section of `𝒪_{X^an}`, read in a chart.
* `gfun`: The holomorphic function of the affine coordinates of `U_j` representing a section of
  `𝒪(k)^an` over `W(S)`.

## Main results

* `polyHomotopyEquiv`: The polynomial cochains are a deformation retract of the convergent ones.
* `isZero_sheafCohomology_restrict_of_isAffineOpen`: A quasi-coherent module has no higher Godement
  cohomology on an affine open.
* `exists_laurent`: A holomorphic function on `lDom s` has an absolutely convergent Laurent
  expansion.
* `laurent_unique_torus`: An absolutely summable Laurent series vanishing on the torus has zero
  coefficients.
* `exists_sections_secVal_eq`: A holomorphic function of the coordinates of a chart defines a
  section of `𝒪_{X^an}`.
* `gfun_unitHom`: On `W(S)`, the coefficient function of the analytification of an algebraic
  section of `𝒪(k)` is its Laurent fraction, evaluated.
* `gfun_change`: The homogeneous function of a section of `𝒪(k)^an` does not depend on the chart.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §§12–13
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MMP.Analytic
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

namespace MMP.Analytic.ProjectiveTwists

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The twisting sheaf `𝒪(k)` of `ℙᴺ_ℂ = Proj ℂ[x₀, …, x_N]`. -/
local notation3 (prettyPrint := false) "𝒪ℙ[" N ", " k "]" =>
  (show (AlgebraicGeometry.Proj (polyGrading ℂ N)).Modules from
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading ℂ N) k)

/-! ### The Laurent coefficient model of the ordered Čech complexes

A degree-`q` cochain is a family `c_S` of Laurent coefficient families indexed by the
`(q + 1)`-element sets `S` of chart indices, with differential
`(d c)_S = ∑_{i ∈ S} ε(S, i) c_{S ∖ i}`. Splitting the coefficients by the set `T` of negative
exponents, the parts with `∅ ≠ T ≠ univ` are contracted by adjoining the least index not in `T`;
the two remaining parts have finitely many monomials. Hence the polynomial cochains are a
deformation retract of the absolutely convergent ones. -/

section CoefficientModel

open Stacks.ProjectiveSpace.Cohomology

variable {N : ℕ}

/-- Families of Laurent coefficients, one for each set of chart indices. -/
abbrev CoeffCochain (N : ℕ) := Finset (Fin (N + 1)) → ((Fin (N + 1) → ℤ) → ℂ)

/-- The Čech differential `(d c)_S = ∑_{i ∈ S} ε(S, i) c_{S ∖ i}` on coefficient families. -/
def coeffDiff (N : ℕ) : CoeffCochain N →+ CoeffCochain N where
  toFun c S := ∑ i ∈ S, Cech.cechSign S i • c (S.erase i)
  map_zero' := by funext S; simp
  map_add' c c' := by funext S; simp [Finset.sum_add_distrib, smul_add]

/-- The value of `coeffDiff N c` at `S` is `∑_{i ∈ S} ε(S, i) c_{S ∖ i}`. -/
lemma coeffDiff_apply (c : CoeffCochain N) (S : Finset (Fin (N + 1))) :
    coeffDiff N c S = ∑ i ∈ S, Cech.cechSign S i • c (S.erase i) := rfl

/-- The Čech differential on coefficient families squares to zero. -/
lemma coeffDiff_coeffDiff (c : CoeffCochain N) : coeffDiff N (coeffDiff N c) = 0 := by
  funext S
  rw [coeffDiff_apply, Pi.zero_apply, Finset.sum_congr rfl fun i (hi : i ∈ S) => by
      rw [coeffDiff_apply, Finset.smul_sum,
        Finset.sum_congr rfl fun j (hj : j ∈ S.erase i) => smul_smul _ _ _]]
  refine sum_sum_erase_eq_zero S _ fun i hi j hj hij => ?_
  rw [cechSign_mul_cechSign_erase_swap hi hj hij, neg_smul, Finset.erase_right_comm]

/-- The set of negative exponents of a Laurent monomial. -/
def negSet (β : Fin (N + 1) → ℤ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter fun i => β i < 0

/-- The part of a coefficient family on the monomials with negative exponents exactly at `T`. -/
def tpart (T : Finset (Fin (N + 1))) : CoeffCochain N →+ CoeffCochain N where
  toFun c S β := if negSet β = T then c S β else 0
  map_zero' := by funext S β; simp
  map_add' c c' := by funext S β; simp only [Pi.add_apply]; split_ifs <;> simp

/-- The value of `tpart T c` at `(S, β)` is `c S β` if `negSet β = T`, and `0` otherwise. -/
lemma tpart_apply (T : Finset (Fin (N + 1))) (c : CoeffCochain N) (S β) :
    tpart T c S β = if negSet β = T then c S β else 0 := rfl

/-- Taking the part with negative set `T` commutes with the Čech differential. -/
lemma tpart_coeffDiff (T : Finset (Fin (N + 1))) (c : CoeffCochain N) :
    tpart T (coeffDiff N c) = coeffDiff N (tpart T c) := by
  funext S β
  simp only [tpart_apply, coeffDiff_apply, Finset.sum_apply, Pi.smul_apply]
  split_ifs <;> simp

/-- A coefficient family is the sum of its parts over all negative sets `T`. -/
lemma sum_tpart (c : CoeffCochain N) : ∑ T, tpart T c = c := by
  funext S β
  simp only [Finset.sum_apply, tpart_apply]
  rw [Finset.sum_ite_eq]
  simp

/-- The contraction `(h c)_S = ε(S, v) c_{S ∪ v}` (and `0` if `v ∈ S`). -/
def contr (v : Fin (N + 1)) : CoeffCochain N →+ CoeffCochain N where
  toFun c S := if v ∈ S then 0 else Cech.cechSign S v • c (insert v S)
  map_zero' := by funext S; simp
  map_add' c c' := by funext S; simp only [Pi.add_apply]; split_ifs <;> simp [smul_add]

/-- The value of `contr v c` at `S` is `0` if `v ∈ S`, and `ε(S, v) c_{S ∪ v}` otherwise. -/
lemma contr_apply (v : Fin (N + 1)) (c : CoeffCochain N) (S) :
    contr v c S = if v ∈ S then 0 else Cech.cechSign S v • c (insert v S) := rfl

/-- The contraction `contr v` is a contracting homotopy: `d ∘ h + h ∘ d = id`. -/
lemma coeffDiff_contr_add (v : Fin (N + 1)) (c : CoeffCochain N) :
    coeffDiff N (contr v c) + contr v (coeffDiff N c) = c := by
  funext S
  rw [Pi.add_apply]
  by_cases hv : v ∈ S
  · rw [contr_apply v (coeffDiff N c), if_pos hv, add_zero, coeffDiff_apply,
      Finset.sum_eq_single v]
    · rw [contr_apply, if_neg (Finset.notMem_erase v S), Finset.insert_erase hv]
      have : Cech.cechSign (S.erase v) v = Cech.cechSign S v := by
        conv_rhs => rw [← Finset.insert_erase hv]
        exact (Cech.cechSign_insert v _).symm
      rw [this, cechSign_smul_cechSign_smul]
    · intro i _ hiv
      rw [contr_apply, if_pos (Finset.mem_erase.2 ⟨Ne.symm hiv, hv⟩), smul_zero]
    · intro h; exact absurd hv h
  · have h1 : coeffDiff N (contr v c) S = ∑ i ∈ S,
        (Cech.cechSign S i * Cech.cechSign (S.erase i) v) • c (insert v (S.erase i)) := by
      rw [coeffDiff_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [contr_apply, if_neg (fun h => hv (Finset.mem_of_mem_erase h)), smul_smul]
    have h2 : contr v (coeffDiff N c) S = c S + ∑ i ∈ S,
        (Cech.cechSign S v * Cech.cechSign (insert v S) i) • c (insert v (S.erase i)) := by
      rw [contr_apply, if_neg hv, coeffDiff_apply, Finset.sum_insert hv, Finset.erase_insert hv,
        Cech.cechSign_insert, smul_add, cechSign_smul_cechSign_smul, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.erase_insert_of_ne (by rintro rfl; exact hv hi), smul_smul]
    rw [h1, h2, add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [← add_smul, cechSign_mul_cechSign_erase hi hv, neg_add_cancel, zero_smul]

/-- The least index not in `T` (the first nonnegative exponent of a monomial with negative set
`T`). -/
noncomputable def firstOut (T : Finset (Fin (N + 1))) : Fin (N + 1) :=
  if h : Tᶜ.Nonempty then Tᶜ.min' h else 0

/-- If `T` is not everything, then `firstOut T ∉ T`. -/
lemma firstOut_notMem {T : Finset (Fin (N + 1))} (hT : T ≠ Finset.univ) :
    firstOut T ∉ T := by
  have h : Tᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]; exact hT
  rw [firstOut, dif_pos h]
  exact Finset.mem_compl.1 (Finset.min'_mem _ h)

/-- The middle negative sets: neither empty nor everything. -/
def midSets (N : ℕ) : Finset (Finset (Fin (N + 1))) :=
  Finset.univ.filter fun T => T ≠ ∅ ∧ T ≠ Finset.univ

/-- The contracting homotopy on the middle parts. -/
noncomputable def homot (N : ℕ) : CoeffCochain N →+ CoeffCochain N :=
  ∑ T ∈ midSets N, (contr (firstOut T)).comp (tpart T)

/-- The projection onto the two extreme parts. -/
def proj (N : ℕ) : CoeffCochain N →+ CoeffCochain N :=
  tpart ∅ + tpart Finset.univ

/-- The homotopy `homot N` satisfies `d ∘ h + h ∘ d = id - proj N`. -/
lemma coeffDiff_homot_add (c : CoeffCochain N) :
    coeffDiff N (homot N c) + homot N (coeffDiff N c) = c - proj N c := by
  simp only [homot, AddMonoidHom.finset_sum_apply, AddMonoidHom.comp_apply, map_sum,
    ← Finset.sum_add_distrib, tpart_coeffDiff, coeffDiff_contr_add]
  have hpair : (Finset.univ.filter fun T : Finset (Fin (N + 1)) => ¬(T ≠ ∅ ∧ T ≠ Finset.univ))
      = {∅, Finset.univ} := by
    ext T; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]; tauto
  have hne : (∅ : Finset (Fin (N + 1))) ≠ Finset.univ :=
    (Finset.univ_nonempty (α := Fin (N + 1))).ne_empty.symm
  have := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun T : Finset (Fin (N + 1)) => T ≠ ∅ ∧ T ≠ Finset.univ) (fun T => tpart T c)
  rw [hpair, Finset.sum_pair hne, sum_tpart] at this
  rw [midSets, proj, AddMonoidHom.add_apply, eq_sub_iff_add_eq, this]

/-- The projection onto the two extreme parts commutes with the Čech differential. -/
lemma proj_coeffDiff (c : CoeffCochain N) : proj N (coeffDiff N c) = coeffDiff N (proj N c) := by
  simp only [proj, AddMonoidHom.add_apply, tpart_coeffDiff, map_add]

/-- The Laurent monomial `z^β = ∏ᵢ zᵢ^βᵢ`. -/
noncomputable def mono (z : Fin (N + 1) → ℂ) (β : Fin (N + 1) → ℤ) : ℂ := ∏ i, z i ^ β i

/-- The analytic cochains of degree `q`: coefficient families concentrated on `(q + 1)`-element
sets `S`, supported on the degree-`k` monomials regular outside `S`, and absolutely convergent on
`{z | zᵢ ≠ 0 for i ∈ S}`. -/
def anCochains (N : ℕ) (k : ℤ) (q : ℕ) : AddSubgroup (CoeffCochain N) where
  carrier := {c | (∀ S β, c S β ≠ 0 → β ∈ laurentMonomials N k (S : Set (Fin (N + 1)))) ∧
    (∀ S (z : Fin (N + 1) → ℂ), (∀ i ∈ S, z i ≠ 0) → Summable fun β => ‖c S β * mono z β‖) ∧
    ∀ S : Finset (Fin (N + 1)), S.card ≠ q + 1 → c S = 0}
  add_mem' {c c'} hc hc' := by
    refine ⟨fun S β h => ?_, fun S z hz => ?_, fun S hS => ?_⟩
    · by_cases h0 : c S β = 0
      · refine hc'.1 S β fun h' => h ?_
        simp [h0, h']
      · exact hc.1 S β h0
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun β => ?_)
        ((hc.2.1 S z hz).add (hc'.2.1 S z hz))
      rw [Pi.add_apply, Pi.add_apply, add_mul]
      exact norm_add_le _ _
    · rw [Pi.add_apply, hc.2.2 S hS, hc'.2.2 S hS, add_zero]
  zero_mem' := ⟨fun _ _ h => absurd rfl h, fun _ _ _ => by simpa using summable_zero,
    fun _ _ => rfl⟩
  neg_mem' {c} hc := by
    refine ⟨fun S β h => hc.1 S β fun h' => h ?_, fun S z hz => ?_, fun S hS => ?_⟩
    · simp [h']
    · simpa [neg_mul, norm_neg] using hc.2.1 S z hz
    · rw [Pi.neg_apply, hc.2.2 S hS, neg_zero]

/-- The polynomial cochains: the analytic cochains with finitely many monomials in each
component. -/
def polyCochains (N : ℕ) (k : ℤ) (q : ℕ) : AddSubgroup (CoeffCochain N) where
  carrier := {c | c ∈ anCochains N k q ∧ ∀ S, (Function.support (c S)).Finite}
  add_mem' {c c'} hc hc' := ⟨add_mem hc.1 hc'.1, fun S =>
    ((hc.2 S).union (hc'.2 S)).subset (Function.support_add _ _)⟩
  zero_mem' := ⟨zero_mem _, fun S => by simp⟩
  neg_mem' {c} hc := ⟨neg_mem hc.1, fun S => by simpa [Function.support_neg] using hc.2 S⟩

/-- Every polynomial cochain is an analytic cochain. -/
lemma polyCochains_le (k : ℤ) (q : ℕ) : polyCochains N k q ≤ anCochains N k q :=
  fun _ hc => hc.1

/-- Multiplication by a Čech sign `ε(S, i)` preserves the norm. -/
lemma norm_cechSign_smul (S : Finset (Fin (N + 1))) (i : Fin (N + 1)) (x : ℂ) :
    ‖Cech.cechSign S i • x‖ = ‖x‖ := by
  rw [Cech.cechSign, zsmul_eq_mul]; simp

/-- The Čech differential maps analytic cochains of degree `q` to analytic cochains of degree
`q + 1`. -/
lemma coeffDiff_mem {k : ℤ} {q : ℕ} {c : CoeffCochain N} (hc : c ∈ anCochains N k q) :
    coeffDiff N c ∈ anCochains N k (q + 1) := by
  refine ⟨fun S β h => ?_, fun S z hz => ?_, fun S hS => ?_⟩
  · rw [coeffDiff_apply, Finset.sum_apply] at h
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hne' : c (S.erase i) β ≠ 0 := fun h0 => hne (by simp [h0])
    exact laurentMonomials_mono (by simp) (hc.1 _ β hne')
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun β => ?_)
      (summable_sum fun i (hi : i ∈ S) => hc.2.1 (S.erase i) z fun j hj =>
        hz j (Finset.mem_of_mem_erase hj))
    rw [coeffDiff_apply, Finset.sum_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Pi.smul_apply, smul_mul_assoc, norm_cechSign_smul]
  · rw [coeffDiff_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hc.2.2 (S.erase i) ?_, smul_zero]
    rw [Finset.card_erase_of_mem hi]
    have := Finset.card_pos.2 ⟨i, hi⟩
    omega

/-- The Čech differential maps polynomial cochains of degree `q` to polynomial cochains of degree
`q + 1`. -/
lemma coeffDiff_mem_poly {k : ℤ} {q : ℕ} {c : CoeffCochain N}
    (hc : c ∈ polyCochains N k q) : coeffDiff N c ∈ polyCochains N k (q + 1) := by
  refine ⟨coeffDiff_mem hc.1, fun S => ?_⟩
  refine (Set.Finite.biUnion (Finset.finite_toSet S) fun i _ => hc.2 (S.erase i)).subset ?_
  intro β hβ
  rw [Function.mem_support, coeffDiff_apply, Finset.sum_apply] at hβ
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  exact Set.mem_biUnion (Finset.mem_coe.2 hi)
    (Function.mem_support.2 fun h0 => hne (by rw [Pi.smul_apply, h0, smul_zero]))

/-- The part of an analytic cochain with negative set `T` is an analytic cochain. -/
lemma tpart_mem {k : ℤ} {q : ℕ} (T : Finset (Fin (N + 1))) {c : CoeffCochain N}
    (hc : c ∈ anCochains N k q) : tpart T c ∈ anCochains N k q := by
  refine ⟨fun S β h => ?_, fun S z hz => ?_, fun S hS => ?_⟩
  · rw [tpart_apply] at h
    split_ifs at h with h'
    exacts [hc.1 S β h, absurd rfl h]
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun β => ?_) (hc.2.1 S z hz)
    rw [tpart_apply]; split_ifs <;> simp; positivity
  · funext β; rw [tpart_apply, hc.2.2 S hS]; simp

/-- The part of a polynomial cochain with negative set `T` is a polynomial cochain. -/
lemma tpart_mem_poly {k : ℤ} {q : ℕ} (T : Finset (Fin (N + 1))) {c : CoeffCochain N}
    (hc : c ∈ polyCochains N k q) : tpart T c ∈ polyCochains N k q :=
  ⟨tpart_mem T hc.1, fun S => (hc.2 S).subset fun β hβ => by
    rw [Function.mem_support, tpart_apply] at hβ
    split_ifs at hβ with h'
    exacts [hβ, absurd rfl hβ]⟩

/-- `i ∈ negSet β` if and only if `β i < 0`. -/
lemma mem_negSet {β : Fin (N + 1) → ℤ} {i : Fin (N + 1)} : i ∈ negSet β ↔ β i < 0 := by
  simp [negSet]

/-- If `β v ≥ 0`, replacing a vanishing coordinate `z v` by `1` does not decrease `‖z^β‖`. -/
lemma norm_mono_le_update {z : Fin (N + 1) → ℂ} {β : Fin (N + 1) → ℤ} {v : Fin (N + 1)}
    (hβ : 0 ≤ β v) :
    ‖mono z β‖ ≤ ‖mono (Function.update z v (if z v = 0 then 1 else z v)) β‖ := by
  by_cases hz : z v = 0
  · rw [if_pos hz]
    rcases hβ.lt_or_eq with h | h
    · have : mono z β = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hz]; exact zero_zpow _ h.ne')
      rw [this, norm_zero]; exact norm_nonneg _
    · refine le_of_eq (congrArg _ (Finset.prod_congr rfl fun i _ => ?_))
      by_cases hi : i = v
      · subst hi; rw [← h, zpow_zero, zpow_zero]
      · rw [Function.update_of_ne hi]
  · rw [if_neg hz, Function.update_eq_self]

/-- For `v ∉ T`, contracting by `v` the part with negative set `T` of an analytic cochain of degree
`q + 1` gives an analytic cochain of degree `q`. -/
lemma contr_tpart_mem {k : ℤ} {q : ℕ} {T : Finset (Fin (N + 1))} {v : Fin (N + 1)}
    (hv : v ∉ T) {c : CoeffCochain N} (hc : c ∈ anCochains N k (q + 1)) :
    contr v (tpart T c) ∈ anCochains N k q := by
  refine ⟨fun S β h => ?_, fun S z hz => ?_, fun S hS => ?_⟩
  · rw [contr_apply] at h
    split_ifs at h with hvS
    · exact absurd rfl h
    have h' : tpart T c (insert v S) β ≠ 0 := fun h0 => h (by rw [Pi.smul_apply, h0, smul_zero])
    rw [tpart_apply] at h'
    split_ifs at h' with hT
    · obtain ⟨hsum, hpos⟩ := hc.1 _ β h'
      refine ⟨hsum, fun i hi => ?_⟩
      by_cases hiv : i = v
      · subst hiv
        exact not_lt.1 fun hlt => hv (hT ▸ mem_negSet.2 hlt)
      · exact hpos i (by simpa [hiv] using hi)
    · exact absurd rfl h'
  · by_cases hvS : v ∈ S
    · simp only [contr_apply, if_pos hvS, Pi.zero_apply, zero_mul, norm_zero]
      exact summable_zero
    set w := Function.update z v (if z v = 0 then 1 else z v)
    have hw : ∀ i ∈ insert v S, w i ≠ 0 := by
      intro i hi
      by_cases hiv : i = v
      · subst hiv; simp only [w, Function.update_self]; split_ifs with h0 <;> simp [h0]
      · simp only [w]
        rw [Function.update_of_ne hiv]
        exact hz i ((Finset.mem_insert.1 hi).resolve_left hiv)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun β => ?_)
      (hc.2.1 (insert v S) w hw)
    simp only [contr_apply, if_neg hvS, Pi.smul_apply, smul_mul_assoc, norm_cechSign_smul,
      tpart_apply]
    split_ifs with hT
    · rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left (norm_mono_le_update ?_) (norm_nonneg _)
      exact not_lt.1 fun hlt => hv (hT ▸ mem_negSet.2 hlt)
    · simp only [zero_mul, norm_zero]; exact norm_nonneg _
  · rw [contr_apply]
    split_ifs with hvS
    · rfl
    · have : c (insert v S) = 0 := hc.2.2 _ (by rw [Finset.card_insert_of_notMem hvS]; omega)
      funext β
      simp [tpart_apply, this]

/-- For `v ∉ T`, contracting by `v` the part with negative set `T` of a polynomial cochain of
degree `q + 1` gives a polynomial cochain of degree `q`. -/
lemma contr_tpart_mem_poly {k : ℤ} {q : ℕ} {T : Finset (Fin (N + 1))} {v : Fin (N + 1)}
    (hv : v ∉ T) {c : CoeffCochain N} (hc : c ∈ polyCochains N k (q + 1)) :
    contr v (tpart T c) ∈ polyCochains N k q := by
  refine ⟨contr_tpart_mem hv hc.1, fun S => ?_⟩
  refine (hc.2 (insert v S)).subset fun β hβ => ?_
  rw [Function.mem_support, contr_apply] at hβ
  split_ifs at hβ with hvS
  · exact absurd rfl hβ
  · rw [Pi.smul_apply, tpart_apply] at hβ
    split_ifs at hβ
    · exact Function.mem_support.2 fun h0 => hβ (by rw [h0, smul_zero])
    · exact absurd (smul_zero _) hβ

/-- The homotopy maps analytic cochains of degree `q + 1` to analytic cochains of degree `q`. -/
lemma homot_mem {k : ℤ} {q : ℕ} {c : CoeffCochain N} (hc : c ∈ anCochains N k (q + 1)) :
    homot N c ∈ anCochains N k q := by
  rw [homot, AddMonoidHom.finset_sum_apply]
  refine AddSubgroup.sum_mem _ fun T hT => contr_tpart_mem (firstOut_notMem ?_) hc
  exact (Finset.mem_filter.1 hT).2.2

/-- The homotopy maps polynomial cochains of degree `q + 1` to polynomial cochains of degree
`q`. -/
lemma homot_mem_poly {k : ℤ} {q : ℕ} {c : CoeffCochain N}
    (hc : c ∈ polyCochains N k (q + 1)) : homot N c ∈ polyCochains N k q := by
  rw [homot, AddMonoidHom.finset_sum_apply]
  refine AddSubgroup.sum_mem _ fun T hT => contr_tpart_mem_poly (firstOut_notMem ?_) hc
  exact (Finset.mem_filter.1 hT).2.2

/-- In degree `0` the homotopy vanishes: a degree-`0` cochain has no middle part. -/
lemma homot_eq_zero {k : ℤ} {c : CoeffCochain N} (hc : c ∈ anCochains N k 0) :
    homot N c = 0 := by
  funext S β
  rw [homot, AddMonoidHom.finset_sum_apply, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  obtain ⟨-, hT0, hTu⟩ := Finset.mem_filter.1 hT
  rw [AddMonoidHom.comp_apply, contr_apply]
  split_ifs with hvS
  · rfl
  rw [Pi.smul_apply, tpart_apply]
  split_ifs with hβ
  · by_cases h0 : c (insert (firstOut T) S) β = 0
    · rw [h0, smul_zero]
    exfalso
    obtain ⟨-, hpos⟩ := hc.1 _ β h0
    have hS : S = ∅ := by
      by_contra hne
      have := hc.2.2 (insert (firstOut T) S) (by
        rw [Finset.card_insert_of_notMem hvS]
        have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hne); omega)
      exact h0 (by rw [this]; rfl)
    subst hS
    obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hT0
    have htv : t = firstOut T := by
      by_contra hne
      have := hpos t (by simpa using hne)
      exact absurd (mem_negSet.1 (hβ ▸ ht)) (not_lt.2 this)
    exact firstOut_notMem hTu (htv ▸ ht)
  · rw [smul_zero]

/-- There are finitely many exponents `β` with all `βᵢ ≥ 0` and `∑ᵢ βᵢ = k`. -/
lemma finite_nonneg (k : ℤ) :
    {β : Fin (N + 1) → ℤ | (∀ i, 0 ≤ β i) ∧ ∑ i, β i = k}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.Icc 0 k)
    fun _ => Set.finite_Icc 0 k).subset fun β ⟨hβ, hs⟩ => ?_
  refine Set.mem_univ_pi.2 fun i => ⟨hβ i, ?_⟩
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hβ j) (Finset.mem_univ i)

/-- There are finitely many exponents `β` with all `βᵢ < 0` and `∑ᵢ βᵢ = k`. -/
lemma finite_neg (k : ℤ) :
    {β : Fin (N + 1) → ℤ | (∀ i, β i < 0) ∧ ∑ i, β i = k}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.Icc k (-1))
    fun _ => Set.finite_Icc k (-1)).subset fun β ⟨hβ, hs⟩ => ?_
  refine Set.mem_univ_pi.2 fun i => ⟨?_, by have := hβ i; omega⟩
  rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, β j ≤ 0 := Finset.sum_nonpos fun j _ => (hβ j).le
  omega

/-- The projection of an analytic cochain onto the two extreme parts is a polynomial cochain. -/
lemma proj_mem {k : ℤ} {q : ℕ} {c : CoeffCochain N} (hc : c ∈ anCochains N k q) :
    proj N c ∈ polyCochains N k q := by
  refine ⟨add_mem (tpart_mem _ hc) (tpart_mem _ hc), fun S => ?_⟩
  refine ((finite_nonneg k).union (finite_neg k)).subset fun β hβ => ?_
  rw [Function.mem_support, proj, AddMonoidHom.add_apply, Pi.add_apply, Pi.add_apply,
    tpart_apply, tpart_apply] at hβ
  have hc0 : c S β ≠ 0 := by
    intro h0; apply hβ; simp [h0]
  have hsum := (hc.1 S β hc0).1
  by_cases h1 : negSet β = ∅
  · left
    refine ⟨fun i => not_lt.1 fun hlt => ?_, hsum⟩
    have := mem_negSet.2 hlt; rw [h1] at this; simp at this
  · right
    rw [if_neg h1] at hβ
    by_cases h2 : negSet β = Finset.univ
    · refine ⟨fun i => mem_negSet.1 (h2 ▸ Finset.mem_univ i), hsum⟩
    · simp [h2] at hβ

/-! ### The two coefficient complexes -/

variable (N) in
/-- The Čech differential on the analytic cochains. -/
def anD (k : ℤ) (q : ℕ) : anCochains N k q →+ anCochains N k (q + 1) :=
  ((coeffDiff N).comp (anCochains N k q).subtype).codRestrict _ fun c => coeffDiff_mem c.2

variable (N) in
/-- The Čech differential on the polynomial cochains. -/
def polyD (k : ℤ) (q : ℕ) : polyCochains N k q →+ polyCochains N k (q + 1) :=
  ((coeffDiff N).comp (polyCochains N k q).subtype).codRestrict _ fun c => coeffDiff_mem_poly c.2

variable (N) in
/-- The complex of absolutely convergent Laurent cochains. -/
noncomputable def anComplex (k : ℤ) : CochainComplex AddCommGrpCat.{0} ℕ :=
  CochainComplex.of (fun q => AddCommGrpCat.of (anCochains N k q))
    (fun q => AddCommGrpCat.ofHom (anD N k q))
    (fun q => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c =>
      Subtype.ext (coeffDiff_coeffDiff c.1)))

variable (N) in
/-- The complex of Laurent polynomial cochains. -/
noncomputable def polyComplex (k : ℤ) : CochainComplex AddCommGrpCat.{0} ℕ :=
  CochainComplex.of (fun q => AddCommGrpCat.of (polyCochains N k q))
    (fun q => AddCommGrpCat.ofHom (polyD N k q))
    (fun q => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c =>
      Subtype.ext (coeffDiff_coeffDiff c.1)))

/-- The differential of `anComplex N k` in degree `q` is `anD N k q`. -/
lemma anComplex_d (k : ℤ) (q : ℕ) :
    (anComplex N k).d q (q + 1) = AddCommGrpCat.ofHom (anD N k q) := by
  simp [anComplex]

/-- The differential of `polyComplex N k` in degree `q` is `polyD N k q`. -/
lemma polyComplex_d (k : ℤ) (q : ℕ) :
    (polyComplex N k).d q (q + 1) = AddCommGrpCat.ofHom (polyD N k q) := by
  simp [polyComplex]

variable (N) in
/-- The inclusion of the polynomial cochains into the convergent ones. -/
noncomputable def polyToAn (k : ℤ) : polyComplex N k ⟶ anComplex N k :=
  CochainComplex.ofHom
    (fun q => AddCommGrpCat.ofHom (AddSubgroup.inclusion (polyCochains_le k q)))
    (fun q => by
      rw [anComplex_d, polyComplex_d]
      exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => rfl))

variable (N) in
/-- The projection onto the two extreme parts, on the analytic cochains of degree `q`. -/
def projHom (k : ℤ) (q : ℕ) : anCochains N k q →+ polyCochains N k q :=
  ((proj N).comp (anCochains N k q).subtype).codRestrict _ fun c => proj_mem c.2

variable (N) in
/-- The projection onto the two extreme parts, a map of complexes. -/
noncomputable def anToPoly (k : ℤ) : anComplex N k ⟶ polyComplex N k :=
  CochainComplex.ofHom
    (fun q => AddCommGrpCat.ofHom (projHom N k q))
    (fun q => by
      rw [anComplex_d, polyComplex_d]
      exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c =>
        Subtype.ext (proj_coeffDiff c.1).symm))

/-- The component of `polyToAn N k` in degree `q` is the inclusion. -/
lemma polyToAn_f (k : ℤ) (q : ℕ) :
    (polyToAn N k).f q = AddCommGrpCat.ofHom (AddSubgroup.inclusion (polyCochains_le k q)) := rfl

/-- The component of `anToPoly N k` in degree `q` is `projHom N k q`. -/
lemma anToPoly_f (k : ℤ) (q : ℕ) :
    (anToPoly N k).f q = AddCommGrpCat.ofHom (projHom N k q) := rfl

/-- A homotopy of maps of `ℕ`-indexed cochain complexes from a family `X (q + 1) ⟶ Y q`. -/
noncomputable def homotopyOfFamily {K L : CochainComplex AddCommGrpCat.{0} ℕ}
    (f g : K ⟶ L) (h : ∀ q, K.X (q + 1) ⟶ L.X q)
    (h0 : f.f 0 = K.d 0 1 ≫ h 0 + g.f 0)
    (hs : ∀ q, f.f (q + 1) = K.d (q + 1) (q + 2) ≫ h (q + 1) + h q ≫ L.d q (q + 1) + g.f (q + 1)) :
    Homotopy f g where
  hom i j := if hij : j + 1 = i then eqToHom (congrArg K.X hij.symm) ≫ h j else 0
  zero i j hij := dif_neg hij
  comm i := by
    rcases i with _ | q
    · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex, dif_pos rfl,
        eqToHom_refl,
        Category.id_comp, add_zero]
      exact h0
    · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex, dif_pos rfl,
        dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]
      exact hs q

variable (N) in
/-- The homotopy `homot N` on the analytic cochains. -/
noncomputable def homotHom (k : ℤ) (q : ℕ) : anCochains N k (q + 1) →+ anCochains N k q :=
  ((homot N).comp (anCochains N k (q + 1)).subtype).codRestrict _ fun c => homot_mem c.2

variable (N) in
/-- The homotopy `homot N` on the polynomial cochains. -/
noncomputable def polyHomotHom (k : ℤ) (q : ℕ) : polyCochains N k (q + 1) →+ polyCochains N k q :=
  ((homot N).comp (polyCochains N k (q + 1)).subtype).codRestrict _ fun c => homot_mem_poly c.2

variable (N) in
/-- The polynomial cochains are a deformation retract of the convergent ones. -/
noncomputable def polyHomotopyEquiv (k : ℤ) : HomotopyEquiv (polyComplex N k) (anComplex N k) where
  hom := polyToAn N k
  inv := anToPoly N k
  homotopyHomInvId := (homotopyOfFamily _ _ (fun q => AddCommGrpCat.ofHom (polyHomotHom N k q))
    (by
      rw [polyComplex_d]
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c => Subtype.ext ?_)
      simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f, polyToAn_f, anToPoly_f,
        AddCommGrpCat.hom_add, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
        AddCommGrpCat.hom_id, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, AddSubgroup.coe_add]
      have e := coeffDiff_homot_add c.1
      rw [homot_eq_zero c.2.1, map_zero, zero_add] at e
      change c.1 = homot N (coeffDiff N c.1) + proj N c.1
      rw [e, sub_add_cancel])
    (fun q => by
      rw [polyComplex_d, polyComplex_d]
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c => Subtype.ext ?_)
      simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f, polyToAn_f, anToPoly_f,
        AddCommGrpCat.hom_add, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
        AddCommGrpCat.hom_id, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, AddSubgroup.coe_add]
      have e := coeffDiff_homot_add c.1
      change c.1 = homot N (coeffDiff N c.1) + coeffDiff N (homot N c.1) + proj N c.1
      rw [add_comm (homot N _), e, sub_add_cancel])).symm
  homotopyInvHomId := (homotopyOfFamily _ _ (fun q => AddCommGrpCat.ofHom (homotHom N k q))
    (by
      rw [anComplex_d]
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c => Subtype.ext ?_)
      simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f, polyToAn_f, anToPoly_f,
        AddCommGrpCat.hom_add, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
        AddCommGrpCat.hom_id, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, AddSubgroup.coe_add]
      have e := coeffDiff_homot_add c.1
      rw [homot_eq_zero c.2, map_zero, zero_add] at e
      change c.1 = homot N (coeffDiff N c.1) + proj N c.1
      rw [e, sub_add_cancel])
    (fun q => by
      rw [anComplex_d, anComplex_d]
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c => Subtype.ext ?_)
      simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f, polyToAn_f, anToPoly_f,
        AddCommGrpCat.hom_add, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
        AddCommGrpCat.hom_id, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, AddSubgroup.coe_add]
      have e := coeffDiff_homot_add c.1
      change c.1 = homot N (coeffDiff N c.1) + coeffDiff N (homot N c.1) + proj N c.1
      rw [add_comm (homot N _), e, sub_add_cancel])).symm

/-- The inclusion of the polynomial cochains into the convergent ones is an isomorphism on
cohomology. -/
lemma isIso_homologyMap_polyToAn (k : ℤ) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (polyToAn N k) q) :=
  (inferInstance : IsIso ((polyHomotopyEquiv N k).toHomologyIso q).hom)

end CoefficientModel

/-! ### Godement cohomology of quasi-coherent modules on affine opens -/

section AffineVanishing

open TopologicalSpace MMP.Analytic

/-- Godement cohomology of a quasi-coherent module on an affine scheme vanishes. -/
theorem isZero_sheafCohomology_of_isAffine (X : Scheme.{0}) [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (hn : 0 < n) :
    IsZero ((sheafCohomology X.toTopCat n).obj ((SheafOfModules.toSheaf _).obj M)) := by
  have h0 := Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine X M n hn
  obtain ⟨-, -, hU⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying _ X.ringCatSheaf
  obtain ⟨eU, -⟩ := hU ⊤
  have h1 := h0.of_iso ((eU n).app M).symm
  obtain ⟨-, -, ⟨⟨E, -⟩, -⟩, -⟩ := sheafCohomology_toolkit.{0, 0, 0, 0, 0} X.toTopCat
  exact h1.of_iso ((E _ n).app _)

/-- Restriction of sections `F(V) ⟶ F(V ∩ W)`, as a map `F ⟶ ι_* (F|_W)` of abelian sheaves. -/
noncomputable def restrictComparison (X : Scheme.{0}) (W : X.Opens) (F : X.Modules) :
    (SheafOfModules.toSheaf _).obj F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (Opens.inclusion' (W : Opens X.toTopCat))).obj
        ((SheafOfModules.toSheaf _).obj (F.restrict W.ι)) :=
  (SheafOfModules.toSheaf _).map ((Scheme.Modules.restrictAdjunction W.ι).unit.app F)

/-- On an open `V` contained in `W`, the restriction `F(V) ⟶ F|_W(V)` is bijective. -/
lemma restrictComparison_app_bijective (X : Scheme.{0}) (W : X.Opens) (F : X.Modules)
    (V : Opens X.toTopCat)
    (hV : (V : Set X.toTopCat) ⊆ Set.range (Opens.inclusion' (W : Opens X.toTopCat))) :
    Function.Bijective ((restrictComparison X W F).hom.app (op V)) := by
  have hle : V ≤ W := fun x hx => by
    obtain ⟨y, hy⟩ := hV hx
    exact hy ▸ y.2
  have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hle
  change Function.Bijective (F.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op)
  rw [show homOfLE (W.ι.image_preimage_le V) = eqToHom e from Subsingleton.elim _ _]
  exact ConcreteCategory.bijective_of_isIso _

/-- The inverse image of `F` along `W ⊆ X` is the restriction `F|_W`. -/
noncomputable def pullbackRestrictHom (X : Scheme.{0}) (W : X.Opens) (F : X.Modules) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' (W : Opens X.toTopCat))).obj
        ((SheafOfModules.toSheaf _).obj F) ⟶ (SheafOfModules.toSheaf _).obj (F.restrict W.ι) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0}
    (Opens.inclusion' (W : Opens X.toTopCat))).homEquiv _ _).symm (restrictComparison X W F)

/-- The map `pullbackRestrictHom X W F` from the inverse image of `F` to `F|_W` is an
isomorphism. -/
lemma isIso_pullbackRestrictHom (X : Scheme.{0}) (W : X.Opens) (F : X.Modules) :
    IsIso (pullbackRestrictHom X W F) := by
  set adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0}
    (Opens.inclusion' (W : Opens X.toTopCat))
  set θ := pullbackRestrictHom X W F
  have hφ : restrictComparison X W F =
      adj.unit.app _ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} _).map θ :=
    ((adj.homEquiv _ _).apply_symm_apply _).symm.trans (adj.homEquiv_unit _ _ _)
  have hst : ∀ y, Function.Bijective (stalkMap _ (restrictComparison X W F) y) := fun y =>
    stalkMap_bijective_of_app_bijective (f := Opens.inclusion' (W : Opens X.toTopCat))
      (W : Opens X.toTopCat).isOpenEmbedding' (restrictComparison X W F)
      (fun V hV => restrictComparison_app_bijective X W F V hV) y
  haveI : ∀ y, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map θ.hom) := fun y => by
    have h1 := hst y
    rw [hφ] at h1
    rw [stalkMap_comp_pushforward (Opens.inclusion' (W : Opens X.toTopCat))
      (adj.unit.app ((SheafOfModules.toSheaf _).obj F)) θ y] at h1
    haveI := isIso_stalkMap_pullbackPushforwardAdjunction_unit
      (Opens.inclusion' (W : Opens X.toTopCat)) ((SheafOfModules.toSheaf _).obj F) y
    have h2 : Function.Bijective (stalkMap (Opens.inclusion' (W : Opens X.toTopCat))
        (adj.unit.app ((SheafOfModules.toSheaf _).obj F)) y) :=
      ConcreteCategory.bijective_of_isIso _
    have h3 :
        Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map θ.hom) := by
      change Function.Bijective (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map θ.hom) ∘
        (stalkMap _ (adj.unit.app _) y)) at h1
      exact (Function.Bijective.of_comp_iff _ h2).1 h1
    exact (ConcreteCategory.isIso_iff_bijective _).2 h3
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso θ

/-- A quasi-coherent module has no higher Godement cohomology on an affine open. -/
theorem isZero_sheafCohomology_restrict_of_isAffineOpen (X : Scheme.{0}) (W : X.Opens)
    (hW : IsAffineOpen W) (F : X.Modules) [F.IsQuasicoherent] (q : ℤ) (hq : 0 < q) :
    IsZero ((sheafCohomology ((Opens.toTopCat _).obj (W : Opens X.toTopCat)) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' (W : Opens X.toTopCat))).obj
        ((SheafOfModules.toSheaf _).obj F))) := by
  haveI : IsAffine W := hW
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, (Int.toNat_of_nonneg hq.le).symm⟩
  have h := isZero_sheafCohomology_of_isAffine W (F.restrict W.ι) n (by exact_mod_cast hq)
  exact h.of_iso ((sheafCohomology _ n).mapIso
    (@asIso _ _ _ _ (pullbackRestrictHom X W F) (isIso_pullbackRestrictHom X W F)))

end AffineVanishing

/-! ### The analytic Laurent model of `𝒪(k)^an` on the standard charts -/

section AnalyticModel

open Filter Topology TopologicalSpace MMP.Analytic.ComplexPoints MMP.Analytic.Analytification
open scoped ChangeOfRings

section LaurentAnalysis

open UnitAddTorus MeasureTheory

/-- The product of copies of `ℂ` (indices in `s`) and of `ℂ^*` (the others). -/
def lDom {n : ℕ} (s : Set (Fin n)) : Set (Fin n → ℂ) := {w | ∀ i, i ∉ s → w i ≠ 0}

/-- The set `lDom s` is open. -/
lemma isOpen_lDom {n : ℕ} (s : Set (Fin n)) : IsOpen (lDom s) := by
  have : lDom s = ⋂ i, {w : Fin n → ℂ | i ∉ s → w i ≠ 0} := by
    ext w; simp [lDom]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  by_cases hi : i ∈ s
  · simp [hi]
  · simpa [hi] using isOpen_ne_fun (continuous_apply i) continuous_const

/-- The set `lDom s` is the product of the punctured discs of inner radius `0` and outer radius `∞`
with the full planes at the indices in `s`. -/
lemma lDom_eq {n : ℕ} (s : Set (Fin n)) :
    (Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ ((fun _ => (0:ℝ)) j) < ‖w‖) ∧
      ‖w‖ₑ < (fun _ => (⊤ : ENNReal)) j}) = lDom s := by
  ext w
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, true_implies, lDom, norm_pos_iff,
    enorm_lt_top, and_true]
  exact forall_congr' fun i => by tauto

/-- **Laurent expansion** on `lDom s`. -/
lemma exists_laurent {n : ℕ} (s : Set (Fin n)) (f : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (lDom s)) :
    ∃ a : (Fin n → ℤ) → ℂ, (∀ γ, (∃ i ∈ s, γ i < 0) → a γ = 0) ∧
      ∀ w ∈ lDom s, Summable (fun γ => ‖a γ * ∏ i, w i ^ γ i‖) ∧
        HasSum (fun γ => a γ * ∏ i, w i ^ γ i) (f w) := by
  have h5 := (MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.2.2.1 n s (fun _ => 0)
    (fun _ => ⊤) f (fun _ _ => ⟨le_rfl, by simp⟩) (by rw [lDom_eq]; exact hf)
  obtain ⟨c, hc0, hsum, hmaj, -⟩ := h5
  refine ⟨c, hc0, fun w hw => ⟨?_, ?_⟩⟩
  · obtain ⟨u, hu, hle⟩ := hmaj {w} (by rw [lDom_eq]; simpa using hw) isCompact_singleton
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun γ => ?_) hu
    have := hle γ w rfl
    rwa [smul_eq_mul, mul_comm] at this
  · have := hsum w (by rw [lDom_eq]; exact hw)
    simpa [smul_eq_mul, mul_comm] using this

/-- For `0 < ρ ≤ x ≤ P` and any integer `m`, `x ^ m ≤ ρ ^ m + P ^ m`. -/
lemma zpow_le_add_zpow {x ρ P : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ x) (h2 : x ≤ P) (m : ℤ) :
    x ^ m ≤ ρ ^ m + P ^ m := by
  have hx : 0 < x := hρ.trans_le h1
  rcases le_or_gt 0 m with hm | hm
  · exact (zpow_le_zpow_left₀ hm hx.le h2).trans (le_add_of_nonneg_left (zpow_pos hρ m).le)
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -k := ⟨(-m).toNat, by omega⟩
    have : x ^ (-(k : ℤ)) ≤ ρ ^ (-(k : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (pow_pos hρ k) (pow_le_pow_left₀ hρ.le h1 k)
    exact this.trans (le_add_of_nonneg_right (zpow_pos (hρ.trans_le (h1.trans h2)) _).le)

/-- A Laurent monomial with nonnegative exponents at the indices in `s` is holomorphic on
`lDom s`. -/
lemma differentiableOn_monomial {n : ℕ} (s : Set (Fin n)) (γ : Fin n → ℤ)
    (h : ∀ i ∈ s, 0 ≤ γ i) :
    DifferentiableOn ℂ (fun w : Fin n → ℂ => ∏ i, w i ^ γ i) (lDom s) := by
  have := Finset.prod_induction (s := Finset.univ) (fun i (w : Fin n → ℂ) => w i ^ γ i)
    (fun f => DifferentiableOn ℂ f (lDom s)) (fun f g hf hg => hf.mul hg)
    (differentiableOn_const 1) (fun i _ => by
      intro w hw
      refine (DifferentiableAt.zpow (differentiableAt_apply i w) ?_).differentiableWithinAt
      by_cases hi : i ∈ s
      · exact Or.inr (h i hi)
      · exact Or.inl (hw i hi))
  convert this using 1
  ext w; simp [Finset.prod_apply]

/-- An absolutely convergent Laurent series on `lDom s` is holomorphic there. -/
lemma differentiableOn_laurent {n : ℕ} (s : Set (Fin n)) (a : (Fin n → ℤ) → ℂ)
    (ha0 : ∀ γ, (∃ i ∈ s, γ i < 0) → a γ = 0)
    (ha : ∀ w ∈ lDom s, Summable (fun γ => ‖a γ * ∏ i, w i ^ γ i‖)) :
    DifferentiableOn ℂ (fun w => ∑' γ, a γ * ∏ i, w i ^ γ i) (lDom s) := by
  classical
  refine (MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.2.2.2 n
    (atTop : Filter (Finset (Fin n → ℤ))) (lDom s)
    (fun S w => ∑ γ ∈ S, a γ * ∏ i, w i ^ γ i) _ (isOpen_lDom s)
    (Eventually.of_forall fun S => ?_) ?_
  · refine DifferentiableOn.fun_sum fun γ _ => ?_
    by_cases h : ∃ i ∈ s, γ i < 0
    · simp only [ha0 γ h, zero_mul]; exact differentiableOn_const _
    push Not at h
    exact (differentiableOn_monomial s γ h).const_mul _
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun w₀ hw₀ => ?_
  let P : Fin n → ℝ := fun i => ‖w₀ i‖ + 1
  let ρ : Fin n → ℝ := fun i => if i ∈ s then P i else ‖w₀ i‖ / 2
  have hP : ∀ i, 0 < P i := fun i => by positivity
  have hρ : ∀ i, 0 < ρ i := fun i => by
    simp only [ρ]; split_ifs with hi
    · exact hP i
    · have := norm_pos_iff.2 (hw₀ i hi); positivity
  let K : Set (Fin n → ℂ) := {w | ∀ i, ‖w i‖ < P i ∧ (i ∉ s → ρ i < ‖w i‖)}
  have hK : K ∈ 𝓝 w₀ := by
    have : K = ⋂ i, ({w : Fin n → ℂ | ‖w i‖ < P i} ∩ {w | i ∉ s → ρ i < ‖w i‖}) := by
      ext w; simp [K]
    rw [this]
    refine Filter.iInter_mem.2 fun i => Filter.inter_mem ?_ ?_
    · exact (isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const).mem_nhds
        (by simp [P])
    · by_cases hi : i ∈ s
      · simp [hi]
      · simp only [hi, not_false_eq_true, forall_const]
        refine (isOpen_lt continuous_const (continuous_norm.comp (continuous_apply i))).mem_nhds ?_
        change ρ i < ‖w₀ i‖
        simp only [ρ, hi, if_false]
        have := norm_pos_iff.2 (hw₀ i hi); linarith
  refine ⟨K, mem_nhdsWithin_of_mem_nhds hK, ?_⟩
  let c : Finset (Fin n) → Fin n → ℂ := fun T i => if i ∈ T then (ρ i : ℂ) else (P i : ℂ)
  have hc : ∀ T, c T ∈ lDom s := fun T i _ => by
    simp only [c]; split_ifs
    · exact Complex.ofReal_ne_zero.2 (hρ i).ne'
    · exact Complex.ofReal_ne_zero.2 (hP i).ne'
  refine tendstoUniformlyOn_tsum (u := fun γ => ∑ T : Finset (Fin n), ‖a γ * ∏ i, c T i ^ γ i‖)
    (summable_sum fun T _ => ha (c T) (hc T)) fun γ w hw => ?_
  by_cases h : ∃ i ∈ s, γ i < 0
  · simp only [ha0 γ h, zero_mul, norm_zero, Finset.sum_const_zero, le_refl]
  push Not at h
  have e : ∑ T : Finset (Fin n), ‖a γ * ∏ i, c T i ^ γ i‖ =
      ‖a γ‖ * ∏ i, (ρ i ^ γ i + P i ^ γ i) := by
    rw [Finset.prod_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [norm_mul, norm_prod, ← Finset.prod_mul_prod_compl T (fun i => ‖c T i ^ γ i‖)]
    congr 2
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp only [c, if_pos hi, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ i)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hi' : i ∉ T := (Finset.mem_sdiff.1 hi).2
      simp only [c, if_neg hi', norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hP i)]
  rw [e, norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_)
    (norm_nonneg _)
  rw [norm_zpow]
  obtain ⟨hwP, hwρ⟩ := hw i
  by_cases hi : i ∈ s
  · have hγ := h i hi
    have : ‖w i‖ ^ γ i ≤ P i ^ γ i := zpow_le_zpow_left₀ hγ (norm_nonneg _) hwP.le
    exact this.trans (le_add_of_nonneg_left (zpow_pos (hρ i) _).le)
  · exact zpow_le_add_zpow (hρ i) (hwρ hi).le hwP.le _

section Torus

/-- The Haar probability measure on the unit additive circle. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The Haar measure on the unit additive circle is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **Uniqueness of Laurent coefficients**: an absolutely summable Laurent series vanishing on
the torus has zero coefficients. -/
lemma laurent_unique_torus {n : ℕ} (a : (Fin n → ℤ) → ℂ) (ha : Summable fun γ => ‖a γ‖)
    (h0 : ∀ w : Fin n → ℂ, (∀ i, ‖w i‖ = 1) → ∑' γ, a γ * ∏ i, w i ^ γ i = 0) : a = 0 := by
  let F : (Fin n → ℤ) → C(UnitAddTorus (Fin n), ℂ) := fun γ => a γ • mFourier γ
  have hF : Summable fun γ => ‖F γ‖ := by
    refine ha.congr fun γ => ?_
    simp [F, norm_smul, mFourier_norm]
  obtain ⟨G, hG⟩ := hF.of_norm
  have hG0 : G = 0 := by
    ext t
    have h1 := hG.mapL (ContinuousMap.evalCLM ℂ t)
    have h2 : HasSum (fun γ => a γ * ∏ i, ((AddCircle.toCircle (t i) : Circle) : ℂ) ^ γ i)
        (G t) := by
      refine h1.congr_fun fun γ => ?_
      simp only [F, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul, mFourier,
        ContinuousMap.coe_mk, fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
    rw [h2.tsum_eq.symm, h0 _ (fun i => Circle.norm_coe _)]
    rfl
  have hL := hG.mapL (ContinuousMap.toLp (E := ℂ) 2 volume ℂ)
  rw [hG0, map_zero] at hL
  funext m
  have h3 := hL.mapL (innerSL ℂ (mFourierLp (d := Fin n) 2 m))
  rw [map_zero] at h3
  have h4 : HasSum (fun γ => if γ = m then a γ else 0) 0 := by
    refine h3.congr_fun fun γ => ?_
    have e : (innerSL ℂ (mFourierLp (d := Fin n) 2 m))
        ((ContinuousMap.toLp (E := ℂ) 2 volume ℂ) (F γ))
        = a γ * inner ℂ (mFourierLp (d := Fin n) 2 m) (mFourierLp 2 γ) := by
      simp only [F, map_smul, innerSL_apply_apply, smul_eq_mul]
    rw [e, orthonormal_iff_ite.1 orthonormal_mFourier]
    by_cases h : γ = m
    · subst h; simp
    · simp [h, Ne.symm h]
  have h6 : HasSum (fun γ => if γ = m then a γ else 0) (a m) :=
    (hasSum_ite_eq m (a m)).congr_fun fun γ => by split_ifs with h <;> simp_all
  exact h6.unique h4

end Torus

section Homog

/-- For `a ≠ 0`, `∏_{i ∈ s} a ^ f i = a ^ ∑_{i ∈ s} f i`. -/
lemma prod_zpow_eq_zpow_sum' {G ι : Type*} [CommGroupWithZero G] (s : Finset ι) (f : ι → ℤ)
    {a : G} (ha : a ≠ 0) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ ha]

variable {N : ℕ} (k : ℤ) (j : Fin (N + 1))

/-- The homogeneous exponent of degree `k` with dehomogenized part `γ`. -/
def homIdx (γ : Fin N → ℤ) : Fin (N + 1) → ℤ := Fin.insertNth j (k - ∑ i, γ i) γ

/-- The exponent `homIdx k j γ` at `j.succAbove i` is `γ i`. -/
lemma homIdx_succAbove (γ : Fin N → ℤ) (i : Fin N) : homIdx k j γ (j.succAbove i) = γ i :=
  Fin.insertNth_apply_succAbove _ _ _ _

/-- The exponent `homIdx k j γ` at `j` is `k - ∑ᵢ γ i`. -/
lemma homIdx_self (γ : Fin N → ℤ) : homIdx k j γ j = k - ∑ i, γ i :=
  Fin.insertNth_apply_same _ _ _

/-- The map `homIdx k j` is injective. -/
lemma homIdx_injective : Function.Injective (homIdx k j) := by
  intro γ γ' h
  funext i
  have := congrFun h (j.succAbove i)
  rwa [homIdx_succAbove, homIdx_succAbove] at this

/-- The exponent `homIdx k j γ` has total degree `k`. -/
lemma sum_homIdx (γ : Fin N → ℤ) : ∑ i, homIdx k j γ i = k := by
  rw [Fin.sum_univ_succAbove _ j, homIdx_self]
  simp only [homIdx_succAbove]
  ring

/-- An exponent `β` of total degree `k` is `homIdx k j` of its restriction to the indices other
than `j`. -/
lemma homIdx_of_sum (β : Fin (N + 1) → ℤ) (hβ : ∑ i, β i = k) :
    homIdx k j (β ∘ j.succAbove) = β := by
  refine Fin.insertNth_eq_iff.2 ⟨?_, rfl⟩
  rw [← hβ, Fin.sum_univ_succAbove _ j]
  simp

/-- An exponent is in the range of `homIdx k j` if and only if it has total degree `k`. -/
lemma mem_range_homIdx (β : Fin (N + 1) → ℤ) : β ∈ Set.range (homIdx k j) ↔ ∑ i, β i = k :=
  ⟨by rintro ⟨γ, rfl⟩; exact sum_homIdx k j γ, fun h => ⟨_, homIdx_of_sum k j β h⟩⟩

/-- The dehomogenization `x_{σ i} / x_j`. -/
noncomputable def dehom (z : Fin (N + 1) → ℂ) : Fin N → ℂ := fun i => z (j.succAbove i) / z j

/-- For `z j ≠ 0`, `z ^ homIdx k j γ = z j ^ k * (dehom j z) ^ γ`. -/
lemma mono_homIdx (z : Fin (N + 1) → ℂ) (hz : z j ≠ 0) (γ : Fin N → ℤ) :
    ∏ i, z i ^ homIdx k j γ i = z j ^ k * ∏ i, dehom j z i ^ γ i := by
  rw [Fin.prod_univ_succAbove _ j, homIdx_self]
  simp only [homIdx_succAbove, dehom, div_zpow, Finset.prod_div_distrib,
    prod_zpow_eq_zpow_sum' _ _ hz, zpow_sub₀ hz]
  field_simp

end Homog

end LaurentAnalysis

section Charts

open Stacks.AlgebraicGeometry.ProjPolyChart

variable (N : ℕ)

/-- The structure morphism `projToSpecCoeff ℂ N` of `ℙᴺ_ℂ = Proj (polyGrading ℂ N)`, with source
`Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveSpace ℂ N`, a reducible abbreviation of
`Proj ℂ[x₀, …, x_N]`. -/
noncomputable abbrev sP : Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveSpace ℂ N ⟶
    AlgebraicGeometry.Spec (.of ℂ) :=
  projToSpecCoeff ℂ N

/-- The base ring map of `sP N` on an open `U` is the structure ring map of `U`. -/
lemma baseRingHom_eq (U : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Opens) :
    baseRingHom (sP N) U = @MMP.UnderlyingSpace.structureRingHomOpens ℂ _ _ ⟨sP N⟩ U := by
  rw [baseRingHom]
  unfold MMP.UnderlyingSpace.structureRingHomOpens
  rw [CommRingCat.hom_comp]
  ext a
  rfl

variable (j : Fin (N + 1))

/-- The affine coordinates `x_{σ m} / x_j`, `σ = j.succAbove`, of the standard chart `U_j`. -/
noncomputable def stdGen (m : Fin N) :
    Γ(AlgebraicGeometry.Proj (polyGrading ℂ N),
      MMP.UnderlyingSpace.projectiveSpaceStdChart ℂ N j) :=
  MMP.UnderlyingSpace.projectiveSpaceStdCoord ℂ N j (j.succAbove m)

/-- `Fin N` enumerates the indices other than `j`. -/
abbrev succAboveEquiv : Fin N ≃ {m : Fin (N + 1) // m ≠ j} := finSuccAboveEquiv j

/-- The presentation of `Γ(U_j)` by the coordinates `stdGen N j` is the composite of the renaming,
the chart isomorphism `chartEquiv ℂ N j` and `Proj.awayToSection`. -/
lemma pres_eq :
    MvPolynomial.eval₂Hom (baseRingHom (sP N)
      (MMP.UnderlyingSpace.projectiveSpaceStdChart ℂ N j)) (stdGen N j) =
    (Proj.awayToSection (polyGrading ℂ N) (MvPolynomial.X j)).hom.comp
      ((chartEquiv ℂ N j).toRingHom.comp (MvPolynomial.rename (succAboveEquiv N j)).toRingHom) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)
  · simp only [MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_C, RingEquiv.toRingHom_eq_coe,
      chartEquiv_apply, chartHom_C]
    rw [baseRingHom_eq, MMP.UnderlyingSpace.structureRingHomOpens_projectiveSpaceStdChart
      (hO := ⟨sP N⟩) rfl]
  · simp only [MvPolynomial.eval₂Hom_X', RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_X, RingEquiv.toRingHom_eq_coe,
      chartEquiv_apply, chartHom_X]
    rfl

/-- The coordinates `stdGen N j` present `Γ(U_j)` as a polynomial ring in `N` variables. -/
lemma bijective_pres :
    Function.Bijective (MvPolynomial.eval₂Hom (baseRingHom (sP N)
      (MMP.UnderlyingSpace.projectiveSpaceStdChart ℂ N j)) (stdGen N j)) := by
  rw [pres_eq]
  have h1 : Function.Bijective (Proj.awayToSection (polyGrading ℂ N) (MvPolynomial.X j)).hom := by
    have := ConcreteCategory.bijective_of_isIso
      (Proj.basicOpenIsoAway (polyGrading ℂ N) (MvPolynomial.X j) (X_mem_one ℂ N j) one_pos).hom
    rwa [Proj.basicOpenIsoAway_hom] at this
  refine h1.comp ((chartEquiv ℂ N j).bijective.comp ?_)
  exact (MvPolynomial.renameEquiv ℂ (succAboveEquiv N j)).bijective

/-- The polynomial chart of the standard open `U_j`. -/
noncomputable def stdChart : Chart (sP N) where
  U := MMP.UnderlyingSpace.projectiveSpaceStdChart ℂ N j
  isAffineOpen := Proj.isAffineOpen_basicOpen (polyGrading ℂ N) (MvPolynomial.X j)
    (X_mem_one ℂ N j) one_pos
  n := N
  gen := stdGen N j
  surjective := (bijective_pres N j).2

/-- The structure morphism `sP N` is locally of finite type. -/
theorem locallyOfFiniteType_sP : LocallyOfFiniteType (sP N) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ N
  infer_instance

attribute [local instance] locallyOfFiniteType_sP

/-- The standard chart `U_j` has no relations. -/
lemma stdChart_ideal : (stdChart N j).ideal = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (bijective_pres N j).1

/-- The affine coordinates of the standard chart `U_j` take every value in `ℂᴺ`. -/
lemma range_coords_stdChart : Set.range (stdChart N j).coords = Set.univ := by
  rw [((stdChart N j).isOpen_chart_and_isEmbedding_coords).2.2.2, stdChart_ideal]
  ext p; simp [MvPolynomial.zeroLocus]

end Charts

section Sec

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- Evaluation at the point on the local ring of a chart. -/
noncomputable def stalkRingValue (c : Chart sX) (y : chart (sX := sX) c.U) :
    c.StalkRing (c.coords y) →+* ℂ :=
  Ideal.Quotient.lift _ (Filter.Germ.valueRingHom.comp (holGerms (c.coords y)).subtype) (by
    intro g hg
    have : c.ideal.map (polyGermHom (c.coords y)) ≤
        RingHom.ker (Filter.Germ.valueRingHom.comp (holGerms (c.coords y)).subtype) := by
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
      change MvPolynomial.eval (c.coords y) q = 0
      rw [← c.evalHom_pres, (RingHom.mem_ker).1 hq, map_zero]
    exact this hg)

/-- The value of the class of a holomorphic germ `g` is the value of `g` at the point. -/
lemma stalkRingValue_mk (c : Chart sX) (y : chart (sX := sX) c.U) (g : holGerms (c.coords y)) :
    stalkRingValue c y (Chart.StalkRing.mk c _ g) = Filter.Germ.value g.1 := rfl

/-- The value at the point is compatible with the transition maps of the stalk rings of charts. -/
lemma stalkRingValue_transition {c d : Chart sX} (m : ChartHom c d) (y : chart (sX := sX) d.U)
    (g : c.StalkRing (c.coords (m.incl y))) :
    stalkRingValue d y (m.transition y g) = stalkRingValue c (m.incl y) g := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  change stalkRingValue d y (m.transition y (Chart.StalkRing.mk c _ g)) =
    stalkRingValue c (m.incl y) (Chart.StalkRing.mk c _ g)
  rw [m.transition_mk, stalkRingValue_mk, stalkRingValue_mk, coe_holPullback]
  obtain ⟨g, hg⟩ := g
  induction g using Filter.Germ.inductionOn with
  | h f =>
    change f (m.polyMap (d.coords y)) = f (c.coords (m.incl y))
    rw [m.coords_incl]

/-- The value at `x` of a section of `𝒪_{X^an}`, read in the chart `c`. -/
noncomputable def secVal {W : Opens (space sX)} (s : sections sX W) (x : W) (c : Chart sX)
    (hx : x.1 ∈ chart (sX := sX) c.U) : ℂ :=
  stalkRingValue c ⟨x.1, hx⟩ (s.1 x ⟨c, hx⟩)

/-- The value of a section at `x` does not depend on the chart. -/
lemma secVal_indep [LocallyOfFiniteType sX] {W : Opens (space sX)} (s : sections sX W) (x : W)
    (c d : Chart sX) (hc : x.1 ∈ chart (sX := sX) c.U) (hd : x.1 ∈ chart (sX := sX) d.U) :
    secVal s x c hc = secVal s x d hd := by
  obtain ⟨f, e, he, hle, hz⟩ := Chart.exists_refinement c d x.1 (mem_chart_iff.1 hc)
    (mem_chart_iff.1 hd)
  have hz' : x.1 ∈ chart (sX := sX) e.U := mem_chart_iff.2 hz
  have hce : e.U ≤ c.U := he ▸ X.basicOpen_le f
  have k₁ := s.2.2 c e (ChartHom.ofLE c e hce) x hz'
  have k₂ := s.2.2 d e (ChartHom.ofLE d e hle) x hz'
  have e₁ : secVal s x c hc = stalkRingValue e ⟨x.1, hz'⟩ (s.1 x ⟨e, hz'⟩) := by
    rw [← k₁]; exact (stalkRingValue_transition (ChartHom.ofLE c e hce) ⟨x.1, hz'⟩ _).symm
  have e₂ : secVal s x d hd = stalkRingValue e ⟨x.1, hz'⟩ (s.1 x ⟨e, hz'⟩) := by
    rw [← k₂]; exact (stalkRingValue_transition (ChartHom.ofLE d e hle) ⟨x.1, hz'⟩ _).symm
  rw [e₁, e₂]

/-- The value of a product of sections is the product of the values. -/
lemma secVal_mul {W : Opens (space sX)} (s t : sections sX W) (x : W) (c : Chart sX)
    (hx : x.1 ∈ chart (sX := sX) c.U) : secVal (s * t) x c hx = secVal s x c hx * secVal t x c hx :=
  map_mul (stalkRingValue c ⟨x.1, hx⟩) _ _

/-- The value of a sum of sections is the sum of the values. -/
lemma secVal_add {W : Opens (space sX)} (s t : sections sX W) (x : W) (c : Chart sX)
    (hx : x.1 ∈ chart (sX := sX) c.U) : secVal (s + t) x c hx = secVal s x c hx + secVal t x c hx :=
  map_add (stalkRingValue c ⟨x.1, hx⟩) _ _

/-! ### Charts without relations -/

variable (c : Chart sX)

/-- The affine coordinates of a chart without relations are surjective. -/
lemma surjective_coords (hc : c.ideal = ⊥) : Function.Surjective c.coords := by
  obtain ⟨-, -, -, hrange⟩ := c.isOpen_chart_and_isEmbedding_coords
  rw [hc] at hrange
  exact fun p => (show p ∈ Set.range c.coords by rw [hrange]; simp [MvPolynomial.zeroLocus])

/-- The affine coordinates of a chart without relations are an open embedding. -/
lemma isOpenEmbedding_coords (hc : c.ideal = ⊥) : Topology.IsOpenEmbedding c.coords :=
  c.isOpen_chart_and_isEmbedding_coords.2.2.1.isOpenEmbedding_of_surjective (surjective_coords c hc)

/-- For a chart without relations, the map from holomorphic germs to its stalk ring is
injective. -/
lemma mk_injective (hc : c.ideal = ⊥) (p : Fin c.n → ℂ) :
    Function.Injective (Chart.StalkRing.mk c p) := by
  refine (injective_iff_map_eq_zero _).2 fun g hg => ?_
  have := Ideal.Quotient.eq_zero_iff_mem.1 hg
  rw [hc, Ideal.map_bot] at this
  exact (Submodule.mem_bot _).1 this

variable {c} (hc : c.ideal = ⊥) {W : Opens (space sX)} (hW : ∀ x : W, x.1 ∈ chart (sX := sX) c.U)

include hc in
/-- The affine coordinates of a chart without relations are injective. -/
lemma coords_injective : Function.Injective c.coords := (isOpenEmbedding_coords c hc).injective

/-- The holomorphic function of the coordinates of `c` representing a section over `W`. -/
noncomputable def holFun (s : sections sX W) : (Fin c.n → ℂ) → ℂ := fun p =>
  open Classical in
  if h : ∃ x : W, c.coords ⟨x.1, hW x⟩ = p then secVal s h.choose c (hW _) else 0

include hc in
/-- The function `holFun hW s` at the coordinates of `x` is the value of `s` at `x`. -/
lemma holFun_coords (s : sections sX W) (x : W) :
    holFun hW s (c.coords ⟨x.1, hW x⟩) = secVal s x c (hW x) := by
  have h : ∃ x' : W, c.coords ⟨x'.1, hW x'⟩ = c.coords ⟨x.1, hW x⟩ := ⟨x, rfl⟩
  rw [holFun, dif_pos h]
  have : h.choose = x := Subtype.ext (congrArg Subtype.val (coords_injective hc h.choose_spec) :)
  have key : ∀ (x' : W) (hx' : x'.1 ∈ chart (sX := sX) c.U), x' = x →
      secVal s x' c hx' = secVal s x c (hW x) := by rintro _ _ rfl; rfl
  exact key _ _ this

include hc in
/-- The component of `s` at `x` in the chart `c` is the class of the germ of `holFun hW s`. -/
lemma component_eq (s : sections sX W) (x : W) :
    ∃ hg : ((holFun hW s : (Fin c.n → ℂ) → ℂ) : Germ (𝓝 (c.coords ⟨x.1, hW x⟩)) ℂ) ∈
        holGerms (c.coords ⟨x.1, hW x⟩),
      s.1 x ⟨c, hW x⟩ = Chart.StalkRing.mk c _ ⟨_, hg⟩ := by
  obtain ⟨O, hO, hxO, h, hh⟩ := s.2.1 c x (hW x)
  have hO' : IsOpen O := by
    rw [← (c.isOpen_chart_and_isEmbedding_coords).2.1] at hO; exact hO
  have heq : ∀ y ∈ O, holFun hW s (c.coords y) = h (c.coords y) := by
    intro y hy
    obtain ⟨hyW, g, hg, hs⟩ := hh y hy
    have := holFun_coords hc hW s ⟨y.1, hyW⟩
    rw [show (⟨(⟨y.1, hyW⟩ : W).1, hW ⟨y.1, hyW⟩⟩ : chart (sX := sX) c.U) = y from rfl] at this
    rw [this, secVal]
    change stalkRingValue c y (s.1 ⟨y.1, hyW⟩ ⟨c, y.2⟩) = _
    rw [hs, stalkRingValue_mk, hg]
    rfl
  have hev : (holFun hW s : (Fin c.n → ℂ) → ℂ) =ᶠ[𝓝 (c.coords ⟨x.1, hW x⟩)] h := by
    have hmem : c.coords '' O ∈ 𝓝 (c.coords ⟨x.1, hW x⟩) :=
      ((isOpenEmbedding_coords c hc).isOpenMap O hO').mem_nhds ⟨_, hxO, rfl⟩
    filter_upwards [hmem] with p hp
    obtain ⟨y, hy, rfl⟩ := hp
    exact heq y hy
  obtain ⟨hxW, gx, hgx, hsx⟩ := hh ⟨x.1, hW x⟩ hxO
  have hgerm : ((holFun hW s : (Fin c.n → ℂ) → ℂ) : Germ (𝓝 (c.coords ⟨x.1, hW x⟩)) ℂ) =
      (gx : Germ _ ℂ) := by
    rw [hgx]; exact Germ.coe_eq.2 hev
  refine ⟨hgerm ▸ gx.2, ?_⟩
  refine hsx.trans (congrArg _ (Subtype.ext hgerm.symm))

include hc in
/-- The function `holFun hW s` is holomorphic at the coordinates of every point of `W`. -/
lemma differentiableAt_holFun (s : sections sX W) (x : W) :
    DifferentiableAt ℂ (holFun hW s) (c.coords ⟨x.1, hW x⟩) := by
  obtain ⟨hg, -⟩ := component_eq hc hW s x
  obtain ⟨h, hgh, hhd⟩ := hg
  have hev : h =ᶠ[𝓝 (c.coords ⟨x.1, hW x⟩)] holFun hW s := Germ.coe_eq.1 hgh
  exact (hev.differentiableAt_iff).1 hhd.self_of_nhds

include hc in
/-- Two sections over `W` with the same values at all points of `W` are equal. -/
lemma eq_of_secVal_eq [LocallyOfFiniteType sX] (s t : sections sX W)
    (h : ∀ x : W, secVal s x c (hW x) = secVal t x c (hW x)) :
    s = t := by
  rw [← sub_eq_zero]
  apply Subtype.ext
  funext x d
  have hopen : IsOpen (c.coords '' {y : chart (sX := sX) c.U | y.1 ∈ W}) := by
    refine (isOpenEmbedding_coords c hc).isOpenMap _ ?_
    exact @Continuous.isOpen_preimage _ _ _ _ _ continuous_subtype_val _ W.isOpen
  have hfun : (holFun hW s : (Fin c.n → ℂ) → ℂ) =ᶠ[𝓝 (c.coords ⟨x.1, hW x⟩)] holFun hW t := by
    filter_upwards [hopen.mem_nhds ⟨⟨x.1, hW x⟩, x.2, rfl⟩] with p hp
    obtain ⟨y, hy, rfl⟩ := hp
    have e1 := holFun_coords hc hW s ⟨y.1, hy⟩
    have e2 := holFun_coords hc hW t ⟨y.1, hy⟩
    exact e1.trans ((h ⟨y.1, hy⟩).trans e2.symm)
  obtain ⟨hs, es⟩ := component_eq hc hW s x
  obtain ⟨ht, et⟩ := component_eq hc hW t x
  have h0 : (s - t).1 x ⟨c, hW x⟩ = 0 := by
    change s.1 x ⟨c, hW x⟩ - t.1 x ⟨c, hW x⟩ = 0
    rw [es, et, sub_eq_zero]
    exact congrArg _ (Subtype.ext (Germ.coe_eq.2 hfun))
  obtain ⟨W', hxW', hW', hz⟩ := Chart.exists_eq_zero_of_apply_eq_zero (s - t) c x (hW x) h0
  exact hz ⟨x.1, hxW'⟩ d

omit hc in
/-- A holomorphic function of the coordinates of `c` on a neighbourhood of the image of `W`
defines a section of `𝒪_{X^an}` over `W` with these values. -/
lemma exists_sections_secVal_eq [LocallyOfFiniteType sX] {T : Set (Fin c.n → ℂ)} (hT : IsOpen T)
    (h : (Fin c.n → ℂ) → ℂ) (hh : DifferentiableOn ℂ h T)
    (hWT : ∀ x : W, c.coords ⟨x.1, hW x⟩ ∈ T) :
    ∃ s : sections sX W, ∀ x : W, secVal s x c (hW x) = h (c.coords ⟨x.1, hW x⟩) := by
  have hhd' : ∀ q ∈ T, ∀ᶠ x in 𝓝 q, DifferentiableAt ℂ h x := fun q hq =>
    Filter.eventually_of_mem (hT.mem_nhds hq) fun x hx => hh.differentiableAt (hT.mem_nhds hx)
  let germAt : ∀ x : W, c.StalkRing (c.coords ⟨x.1, hW x⟩) := fun x =>
    Chart.StalkRing.mk c _ ⟨(h : Germ (𝓝 (c.coords ⟨x.1, hW x⟩)) ℂ),
      coe_mem_holGerms (hhd' _ (hWT x))⟩
  let s₀ : ∀ x : W, Fibre x.1 := fun x d => Chart.transport c d.1 x.1 (hW x) d.2 (germAt x)
  have hcompat : IsCompatible s₀ := fun _ _ m x hx =>
    Chart.transition_transport m x.1 (hW x) hx (germAt x)
  have hhol : IsLocallyHolomorphic s₀ := by
    intro d x hx
    obtain ⟨f, e, he, hle, hz⟩ := Chart.exists_refinement d c x.1 (mem_chart_iff.1 hx)
      (mem_chart_iff.1 (hW x))
    have hde : e.U ≤ d.U := he ▸ X.basicOpen_le f
    obtain ⟨G, Q, hGw, hQd, hQw, hinv⟩ :=
      (ChartHom.ofLE d e hde).exists_inverse_of_eq_basicOpen he
    refine ⟨{w | w.1 ∈ W ∧ w.1.toScheme ∈ e.U},
      (chartTopology d.U).isOpen_inter _ _ (isOpen_chart_inter ⟨d.U, d.isAffineOpen⟩ W)
        (isOpen_toScheme_mem ⟨d.U, d.isAffineOpen⟩ e.U), ⟨x.2, hz⟩,
      h ∘ (ChartHom.ofLE c e hle).polyMap ∘ Q, fun w hw => ?_⟩
    obtain ⟨hwW, hwe⟩ := hw
    let w' : chart (sX := sX) e.U := ⟨w.1, mem_chart_iff.2 hwe⟩
    have hQd' : ∀ᶠ x in 𝓝 (d.coords ((ChartHom.ofLE d e hde).incl w')),
        DifferentiableAt ℂ Q x :=
      ((differentiable_eval_mvPolynomial G).continuous.continuousAt.eventually_ne
        (hGw w')).mono fun x hx => hQd x hx
    have hQ : Tendsto Q (𝓝 (d.coords ((ChartHom.ofLE d e hde).incl w'))) (𝓝 (e.coords w')) := by
      have := (hQd _ (hGw w')).continuousAt.tendsto
      rwa [hQw] at this
    let g₁ : holGerms (c.coords ((ChartHom.ofLE c e hle).incl w')) :=
      ⟨(h : Germ _ ℂ), coe_mem_holGerms (hhd' _ (hWT ⟨w.1, hwW⟩))⟩
    obtain ⟨-, hright, -⟩ := hinv w' hQd' hQ
    refine ⟨hwW, holPullbackAt Q hQd' hQ (holPullback (ChartHom.ofLE c e hle).polyMap
      (ChartHom.ofLE c e hle).differentiable_polyMap
      ((ChartHom.ofLE c e hle).tendsto_polyMap w') g₁), rfl, ?_⟩
    apply ((ChartHom.ofLE d e hde).bijective_transition w').1
    refine (Chart.transition_transport (ChartHom.ofLE d e hde) w.1 (hW ⟨w.1, hwW⟩) w'.2
      (germAt ⟨w.1, hwW⟩)).trans ?_
    refine (Chart.transport_transition (ChartHom.ofLE c e hle) w.1 w'.2
      (germAt ⟨w.1, hwW⟩)).trans ?_
    refine ((ChartHom.ofLE c e hle).transition_mk w' g₁).trans ?_
    exact (hright _).symm
  refine ⟨⟨s₀, hhol, hcompat⟩, fun x => ?_⟩
  change stalkRingValue c ⟨x.1, hW x⟩ (Chart.transport c c x.1 (hW x) (hW x) (germAt x)) = _
  rw [Chart.transport_self]
  rfl

omit hc in
/-- The value at `y` of the image of `a ∈ Γ(X, U)` in the stalk ring of `c` is the evaluation of
`a` at `y`. -/
lemma stalkRingValue_toStalkRing (y : chart (sX := sX) c.U) (a : Γ(X, c.U)) :
    stalkRingValue c y (c.toStalkRing (c.coords y) a) = evalHom c.U y a := by
  obtain ⟨q, rfl⟩ := c.surjective a
  change stalkRingValue c y (c.toStalkRing _ (c.pres q)) = _
  rw [c.toStalkRing_pres, show (MvPolynomial.eval₂Hom (baseRingHom sX c.U) c.gen) q = c.pres q
    from rfl, c.evalHom_pres]
  rfl

omit hc in
/-- The value of `α^#` of a section `b` over `U` is the evaluation of `b`. -/
lemma secVal_sharpHom_res {V : X.Opens} (hV : V ≤ c.U) (b : Γ(X, c.U))
    (x : (Opens.map (toSchemeHom sX)).obj V) (hx : x.1 ∈ chart (sX := sX) c.U) :
    secVal (sharpHom V (X.presheaf.map (homOfLE hV).op b)) x c hx = evalHom c.U ⟨x.1, hx⟩ b := by
  rw [secVal, sharpHom_apply,
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hV) x.1.toScheme x.2 b,
    c.stalkHom_germ ⟨x.1, hx⟩ b]
  exact stalkRingValue_toStalkRing ⟨x.1, hx⟩ b

end Sec

section P3

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The stalk map of the analytification morphism sends the germ of `r` to the germ of its image
under `ringCatSheafHom sX`. -/
theorem stalkMap_germ_ringCatSheafHom (y : ComplexPoints sX) (V : X.Opens)
    (hx : toSchemeHom sX y ∈ V) (r : X.sheaf.obj.obj (op V)) :
    ((analytificationHom sX).hom.stalkMap y).hom
        (TopCat.Presheaf.germ (C := CommRingCat.{0}) X.sheaf.obj V (toSchemeHom sX y) hx r) =
      TopCat.Presheaf.germ (C := CommRingCat.{0}) (structureSheaf sX).obj
        ((Opens.map (toSchemeHom sX)).obj V) y hx ((ringCatSheafHom sX).hom.app (op V) r) :=
  congrArg (fun φ => φ.hom r) (PresheafedSpace.stalkMap_germ (analytificationHom sX).hom V y hx)

variable {L : X.Modules} {U : X.Opens} {t : L.val.obj (op U)}

/-- Restricting `a • t|_V` to `V' ≤ V` gives `a|_{V'} • t|_{V'}`. -/
lemma map_smul_res {V V' : X.Opens} (h : V' ≤ V) (hV : V ≤ U)
    (a : X.ringCatSheaf.obj.obj (op V)) :
    L.val.map (homOfLE h).op (a • L.val.map (homOfLE hV).op t) =
      X.ringCatSheaf.obj.map (homOfLE h).op a • L.val.map (homOfLE (h.trans hV)).op t := by
  refine (L.val.map_smul (homOfLE h).op a _).trans ?_
  congr 1
  exact (L.val.map_comp_apply (homOfLE hV).op (homOfLE h).op t).symm

/-- If multiplication by `t` is bijective on every open of `U`, the germ of `t` is a basis of the
stalk at every point of `U`. -/
lemma bijective_smul_germ
    (hL : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective (fun a : X.ringCatSheaf.obj.obj (op V) => a • L.val.map (homOfLE hV).op t))
    (x : X) (hx : x ∈ U) :
    let L' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := L.val
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) L' x
    Function.Bijective (fun a : X.presheaf.stalk x =>
      a • (TopCat.Presheaf.germ L'.presheaf U x hx).hom t) := by
  intro L'
  letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) L' x
  have hsmul : ∀ (V : X.Opens) (hxV : x ∈ V) (hV : V ≤ U) (a : X.ringCatSheaf.obj.obj (op V)),
      (X.presheaf.germ V x hxV).hom a • (TopCat.Presheaf.germ L'.presheaf U x hx).hom t =
      (TopCat.Presheaf.germ L'.presheaf V x hxV).hom (a • L.val.map (homOfLE hV).op t) := by
    intro V hxV hV a
    have h1 := Stacks.ModuleSkyscraper.germ_smul' (R := X.presheaf) L' x V hxV a
      (L.val.map (homOfLE hV).op t)
    have h2 : (TopCat.Presheaf.germ L'.presheaf V x hxV).hom (L.val.map (homOfLE hV).op t) =
        (TopCat.Presheaf.germ L'.presheaf U x hx).hom t :=
      TopCat.Presheaf.germ_res_apply L'.presheaf (homOfLE hV) x hxV t
    rw [h2] at h1
    exact h1.symm
  constructor
  · intro a b hab
    rw [← sub_eq_zero]
    have h0 : (a - b) • (TopCat.Presheaf.germ L'.presheaf U x hx).hom t = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hab
    obtain ⟨V, hxV, c, hc⟩ := X.presheaf.exists_germ_eq (a - b)
    let V₁ := V ⊓ U
    have hxV₁ : x ∈ V₁ := ⟨hxV, hx⟩
    let c₁ : X.ringCatSheaf.obj.obj (op V₁) := X.presheaf.map (homOfLE inf_le_left).op c
    have hc₁ : (X.presheaf.germ V₁ x hxV₁).hom c₁ = a - b := by
      rw [← hc]
      exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x hxV₁ c
    rw [← hc₁, hsmul V₁ hxV₁ inf_le_right c₁] at h0
    rw [← map_zero (TopCat.Presheaf.germ L'.presheaf V₁ x hxV₁).hom] at h0
    obtain ⟨V₂, hxV₂, i₁, i₂, h₂⟩ := TopCat.Presheaf.germ_eq L'.presheaf x hxV₁ hxV₁ _ _ h0
    have hle : V₂ ≤ V₁ := i₁.le
    rw [show i₁ = homOfLE hle from rfl, show i₂ = homOfLE hle from rfl, map_zero] at h₂
    change L.val.map (homOfLE hle).op (c₁ • L.val.map (homOfLE inf_le_right).op t) = 0 at h₂
    replace h₂ := (map_smul_res (L := L) (t := t) hle inf_le_right c₁).symm.trans h₂
    have h₃ : X.ringCatSheaf.obj.map (homOfLE hle).op c₁ = 0 :=
      (hL V₂ (hle.trans inf_le_right)).1 (h₂.trans (zero_smul _ _).symm)
    rw [← hc₁, ← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) x hxV₂ c₁]
    change (X.presheaf.germ V₂ x hxV₂).hom (X.ringCatSheaf.obj.map (homOfLE hle).op c₁) = 0
    rw [h₃]
    exact map_zero _
  · intro m
    obtain ⟨V, hxV, m', rfl⟩ := TopCat.Presheaf.exists_germ_eq L'.presheaf m
    let V₁ := V ⊓ U
    have hxV₁ : x ∈ V₁ := ⟨hxV, hx⟩
    obtain ⟨c, hc⟩ := (hL V₁ inf_le_right).2 (L.val.map (homOfLE inf_le_left).op m')
    refine ⟨(X.presheaf.germ V₁ x hxV₁).hom c, ?_⟩
    change (X.presheaf.germ V₁ x hxV₁).hom c • (TopCat.Presheaf.germ L'.presheaf U x hx).hom t = _
    rw [hsmul V₁ hxV₁ inf_le_right c]
    change (TopCat.Presheaf.germ L'.presheaf V₁ x hxV₁).hom
      ((fun a : X.ringCatSheaf.obj.obj (op V₁) => a • L.val.map (homOfLE inf_le_right).op t) c) = _
    rw [hc]
    exact TopCat.Presheaf.germ_res_apply L'.presheaf (homOfLE inf_le_left) x hxV₁ m'

/-- The germ of the analytification of a basis `t` is a basis of every analytic stalk. -/
lemma bijective_smul_germ_an
    (hL : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective (fun a : X.ringCatSheaf.obj.obj (op V) => a • L.val.map (homOfLE hV).op t))
    (y : space sX) (hy : y ∈ (Opens.map (toSchemeHom sX)).obj U) :
    let M : PresheafOfModules ((structureSheaf sX).obj ⋙ forget₂ CommRingCat RingCat) :=
      ((analytifyModule sX).obj L).val
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (structureSheaf sX).obj) M y
    Function.Bijective
      (fun φ : TopCat.Presheaf.stalk (C := CommRingCat.{0}) (structureSheaf sX).obj y =>
        φ • (TopCat.Presheaf.germ M.presheaf ((Opens.map (toSchemeHom sX)).obj U) y hy).hom
          ((analytifyModuleUnit sX L).val.app (op U) t)) := by
  intro M
  letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (structureSheaf sX).obj) M y
  let ψ := ((analytificationHom sX).hom.stalkMap y).hom
  have hψ := stalkMap_germ_ringCatSheafHom (sX := sX) y
  let iso := (MMP.ModuleSkyscraper.stalkIso (toSchemeHom sX) (ringCatSheafHom sX) y ψ hψ
      (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX))).app L
  have h := MMP.ModuleSkyscraper.stalkIso_hom_app_one_tmul_germ (toSchemeHom sX)
      (ringCatSheafHom sX) y ψ hψ
      (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)) L U hy t
  have hb := bijective_smul_germ hL (toSchemeHom sX y) hy
  let x := toSchemeHom sX y
  let L' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := L.val
  let R0 := X.presheaf.stalk ((analytificationHom sX).hom.base y)
  let Lx : ModuleCat R0 := (MMP.ModuleSkyscraper.sheafStalkFunctor X.sheaf x).obj L
  let m : Lx := (TopCat.Presheaf.germ L'.presheaf U x hy).hom t
  let μ : R0 →ₗ[R0] Lx := LinearMap.toSpanSingleton _ _ m
  let μe := LinearEquiv.ofBijective μ hb
  let S' := (ModuleCat.restrictScalars ψ).obj
    (ModuleCat.of _ (TopCat.Presheaf.stalk (C := CommRingCat.{0}) (structureSheaf sX).obj y))
  let τ : S' → TensorProduct R0 S' Lx :=
    (LinearEquiv.lTensor S' μe) ∘ (TensorProduct.rid R0 S').symm
  have hτ : Function.Bijective τ := (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)
  have hτ_apply : ∀ φ : S', τ φ = φ ⊗ₜ m := fun φ => by
    change (LinearEquiv.lTensor S' μe) ((TensorProduct.rid R0 S').symm φ) = _
    rw [TensorProduct.rid_symm_apply, LinearEquiv.lTensor_tmul]
    change φ ⊗ₜ ((1 : R0) • m) = φ ⊗ₜ m
    rw [one_smul]
  have key : ∀ φ : TopCat.Presheaf.stalk (C := CommRingCat.{0}) (structureSheaf sX).obj y,
      φ • (TopCat.Presheaf.germ M.presheaf ((Opens.map (toSchemeHom sX)).obj U) y hy).hom
        ((analytifyModuleUnit sX L).val.app (op U) t) = iso.hom.hom (τ φ) := by
    intro φ
    let φ' : (analytification sX).presheaf.stalk y := φ
    let one_m : (ModuleCat.extendScalars ψ).obj Lx :=
      (1 : (analytification sX).presheaf.stalk y) ⊗ₜ[R0, ψ] m
    have e1 : τ φ = φ' • one_m := by
      rw [hτ_apply φ]
      change _ = (φ' * 1) ⊗ₜ[R0, ψ] m
      rw [mul_one]
      rfl
    rw [e1]
    exact ((LinearMap.map_smul iso.hom.hom φ' one_m).trans (congrArg (φ' • ·) h)).symm
  have e2 : (fun φ : TopCat.Presheaf.stalk (C := CommRingCat.{0}) (structureSheaf sX).obj y =>
      φ • (TopCat.Presheaf.germ M.presheaf ((Opens.map (toSchemeHom sX)).obj U) y hy).hom
        ((analytifyModuleUnit sX L).val.app (op U) t)) = iso.hom.hom ∘ τ := funext key
  rw [e2]
  exact (ConcreteCategory.bijective_of_isIso iso.hom).comp hτ

/-- The germ of `f` times the germ of the analytification of `t` is the germ of `f` times the
restriction of the analytification of `t` to `W`. -/
lemma germ_smul_unit (W : Opens (space sX)) (hW : W ≤ (Opens.map (toSchemeHom sX)).obj U)
    (y : space sX) (hy : y ∈ W) (f : (ringCatSheaf sX).obj.obj (op W)) :
    let M : PresheafOfModules ((structureSheaf sX).obj ⋙ forget₂ CommRingCat RingCat) :=
      ((analytifyModule sX).obj L).val
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (structureSheaf sX).obj) M y
    (TopCat.Presheaf.germ (C := CommRingCat.{0}) (structureSheaf sX).obj W y hy).hom f •
        (TopCat.Presheaf.germ M.presheaf ((Opens.map (toSchemeHom sX)).obj U) y (hW hy)).hom
          ((analytifyModuleUnit sX L).val.app (op U) t) =
      (TopCat.Presheaf.germ M.presheaf W y hy).hom
        (f • ((analytifyModule sX).obj L).val.map (homOfLE hW).op
          ((analytifyModuleUnit sX L).val.app (op U) t)) := by
  intro M
  have h1 := Stacks.ModuleSkyscraper.germ_smul' (R := (structureSheaf sX).obj) M y W hy f
    (((analytifyModule sX).obj L).val.map (homOfLE hW).op
      ((analytifyModuleUnit sX L).val.app (op U) t))
  have h2 : (TopCat.Presheaf.germ M.presheaf W y hy).hom (((analytifyModule sX).obj L).val.map
        (homOfLE hW).op ((analytifyModuleUnit sX L).val.app (op U) t)) =
      (TopCat.Presheaf.germ M.presheaf ((Opens.map (toSchemeHom sX)).obj U) y (hW hy)).hom
        ((analytifyModuleUnit sX L).val.app (op U) t) :=
    TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hW) y hy _
  rw [h2] at h1
  exact h1.symm

/-- If multiplication by `t` is bijective on every open of `U`, multiplication by the
analytification of `t` is injective on every open `W` of `α⁻¹ U`. -/
lemma injective_smul_unit
    (hL : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective (fun a : X.ringCatSheaf.obj.obj (op V) => a • L.val.map (homOfLE hV).op t))
    (W : Opens (space sX)) (hW : W ≤ (Opens.map (toSchemeHom sX)).obj U) :
    Function.Injective (fun f : (ringCatSheaf sX).obj.obj (op W) =>
      f • ((analytifyModule sX).obj L).val.map (homOfLE hW).op
        ((analytifyModuleUnit sX L).val.app (op U) t)) := by
  intro f g hfg
  refine TopCat.Presheaf.section_ext (structureSheaf sX) W f g fun y hy => ?_
  have hb := bijective_smul_germ_an hL y (hW hy)
  have e1 := germ_smul_unit (L := L) (t := t) W hW y hy f
  have e2 := germ_smul_unit (L := L) (t := t) W hW y hy g
  exact hb.1 (e1.trans ((congrArg _ hfg).trans e2.symm))

/-- Restriction commutes with multiplication by the analytification of `t`. -/
lemma map_smul_unit {W W' : Opens (space sX)} (hW : W ≤ (Opens.map (toSchemeHom sX)).obj U)
    (h : W' ≤ W) (f : (ringCatSheaf sX).obj.obj (op W)) :
    ((analytifyModule sX).obj L).val.map (homOfLE h).op
        (f • ((analytifyModule sX).obj L).val.map (homOfLE hW).op
          ((analytifyModuleUnit sX L).val.app (op U) t)) =
      (ringCatSheaf sX).obj.map (homOfLE h).op f •
        ((analytifyModule sX).obj L).val.map (homOfLE (h.trans hW)).op
          ((analytifyModuleUnit sX L).val.app (op U) t) := by
  refine (((analytifyModule sX).obj L).val.map_smul (homOfLE h).op f _).trans ?_
  congr 1
  exact (((analytifyModule sX).obj L).val.map_comp_apply (homOfLE hW).op (homOfLE h).op _).symm

/-- If multiplication by `t` is bijective on every open of `U`, multiplication by the
analytification of `t` is surjective on every open `W` of `α⁻¹ U`. -/
lemma surjective_smul_unit
    (hL : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective (fun a : X.ringCatSheaf.obj.obj (op V) => a • L.val.map (homOfLE hV).op t))
    (W : Opens (space sX)) (hW : W ≤ (Opens.map (toSchemeHom sX)).obj U) :
    Function.Surjective (fun f : (ringCatSheaf sX).obj.obj (op W) =>
      f • ((analytifyModule sX).obj L).val.map (homOfLE hW).op
        ((analytifyModuleUnit sX L).val.app (op U) t)) := by
  intro s
  let M : PresheafOfModules ((structureSheaf sX).obj ⋙ forget₂ CommRingCat RingCat) :=
    ((analytifyModule sX).obj L).val
  have hloc : ∀ y : W, ∃ (V : Opens (space sX)) (_ : y.1 ∈ V) (hVW : V ≤ W)
      (f : (ringCatSheaf sX).obj.obj (op V)),
      f • ((analytifyModule sX).obj L).val.map (homOfLE (hVW.trans hW)).op
          ((analytifyModuleUnit sX L).val.app (op U) t) =
        ((analytifyModule sX).obj L).val.map (homOfLE hVW).op s := by
    intro y
    obtain ⟨φ, hφ⟩ := (bijective_smul_germ_an hL y.1 (hW y.2)).2
      ((TopCat.Presheaf.germ M.presheaf W y.1 y.2).hom s)
    obtain ⟨V, hyV, f, rfl⟩ := TopCat.Presheaf.exists_germ_eq (structureSheaf sX).obj φ
    let V₁ := V ⊓ W
    have hyV₁ : y.1 ∈ V₁ := ⟨hyV, y.2⟩
    let f₁ : (ringCatSheaf sX).obj.obj (op V₁) :=
      (structureSheaf sX).obj.map (homOfLE inf_le_left).op f
    have hgerm :
        (TopCat.Presheaf.germ (C := CommRingCat.{0}) (structureSheaf sX).obj V₁ y.1 hyV₁).hom f₁ =
          (TopCat.Presheaf.germ (C := CommRingCat.{0}) (structureSheaf sX).obj V y.1 hyV).hom f :=
      TopCat.Presheaf.germ_res_apply (structureSheaf sX).obj (homOfLE inf_le_left) y.1 hyV₁ f
    have key : (TopCat.Presheaf.germ M.presheaf V₁ y.1 hyV₁).hom
        (f₁ • ((analytifyModule sX).obj L).val.map (homOfLE (inf_le_right.trans hW)).op
          ((analytifyModuleUnit sX L).val.app (op U) t)) =
        (TopCat.Presheaf.germ M.presheaf W y.1 y.2).hom s := by
      refine (germ_smul_unit (L := L) (t := t) V₁ (inf_le_right.trans hW) y.1 hyV₁
        f₁).symm.trans ?_
      rwa [hgerm]
    obtain ⟨V₂, hyV₂, i₁, i₂, h⟩ := TopCat.Presheaf.germ_eq M.presheaf y.1 hyV₁ y.2 _ _ key
    refine ⟨V₂, hyV₂, i₂.le, (ringCatSheaf sX).obj.map i₁.op f₁, ?_⟩
    exact (map_smul_unit (L := L) (t := t) (inf_le_right.trans hW) i₁.le f₁).symm.trans h
  choose V hyV hVW f hf using hloc
  have hcover : W ≤ iSup V := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible (structureSheaf sX).obj V f := by
    intro y y'
    have hle : V y ⊓ V y' ≤ (Opens.map (toSchemeHom sX)).obj U :=
      inf_le_left.trans ((hVW y).trans hW)
    apply injective_smul_unit hL (V y ⊓ V y') hle
    change (ringCatSheaf sX).obj.map (homOfLE inf_le_left).op (f y) • _ =
      (ringCatSheaf sX).obj.map (homOfLE inf_le_right).op (f y') • _
    rw [← map_smul_unit (L := L) (t := t) ((hVW y).trans hW) inf_le_left (f y),
      ← map_smul_unit (L := L) (t := t) ((hVW y').trans hW) inf_le_right (f y'), hf y, hf y']
    have := ((analytifyModule sX).obj L).val.congr_map_apply
      (Subsingleton.elim ((homOfLE (hVW y)).op ≫ (homOfLE inf_le_left).op)
        ((homOfLE (hVW y')).op ≫ (homOfLE (inf_le_right : V y ⊓ V y' ≤ V y')).op)) s
    exact (((analytifyModule sX).obj L).val.map_comp_apply (homOfLE (hVW y)).op
      (homOfLE inf_le_left).op s).symm.trans
      (this.trans (((analytifyModule sX).obj L).val.map_comp_apply (homOfLE (hVW y')).op
        (homOfLE (inf_le_right : V y ⊓ V y' ≤ V y')).op s))
  obtain ⟨g, hg, -⟩ := (structureSheaf sX).existsUnique_gluing' V W (fun y => homOfLE (hVW y))
    hcover f hcompat
  refine ⟨g, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj L))
    V W (fun y => homOfLE (hVW y)) hcover
  intro y
  have hg' : (ringCatSheaf sX).obj.map (homOfLE (hVW y)).op g = f y := hg y
  refine (map_smul_unit (L := L) (t := t) hW (hVW y) g).trans ?_
  rw [hg']
  exact hf y

/-- The unit `L(V) → L^an(α⁻¹ V)` on sections. -/
noncomputable def unitHom (V : X.Opens) :
    L.val.obj (op V) →+
      ((analytifyModule sX).obj L).val.obj (op ((Opens.map (toSchemeHom sX)).obj V)) :=
  ((analytifyModuleUnit sX L).val.app (op V)).hom.toAddMonoidHom

/-- The unit of the analytification is linear over `α^#`. -/
lemma unitHom_smul (V : X.Opens) (a : X.ringCatSheaf.obj.obj (op V)) (m : L.val.obj (op V)) :
    unitHom (sX := sX) (L := L) V (a • m) =
      (show (ringCatSheaf sX).obj.obj (op ((Opens.map (toSchemeHom sX)).obj V)) from
        sharpHom V a) • unitHom (sX := sX) (L := L) V m :=
  ((analytifyModuleUnit sX L).val.app (op V)).hom.map_smul a m

/-- The map `unitHom` commutes with restriction. -/
lemma unitHom_naturality {V V' : X.Opens} (h : V' ≤ V) (m : L.val.obj (op V)) :
    unitHom (sX := sX) (L := L) V' (L.val.map (homOfLE h).op m) =
      ((analytifyModule sX).obj L).val.map
        (homOfLE ((Opens.map (toSchemeHom sX)).monotone h)).op (unitHom (sX := sX) (L := L) V m) :=
  PresheafOfModules.naturality_apply (analytifyModuleUnit sX L).val (homOfLE h).op m

end P3

section Br

open Stacks.ProjectiveSpace.Cohomology

variable {N : ℕ} (S : Finset (Fin (N + 1))) (z : Fin (N + 1) → ℂ)

/-- For `zᵢ ≠ 0` on `S`, the value of `chartDenom ℂ N S` at `z` is a unit. -/
lemma isUnit_eval_chartDenom (hz : ∀ i ∈ S, z i ≠ 0) :
    IsUnit (MvPolynomial.eval z (chartDenom ℂ N S)) := by
  rw [chartDenom, map_prod]
  exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i hi => by simpa using hz i hi)

/-- Evaluation at `z` on `ℂ[x][1/∏_{i ∈ S} xᵢ]`, for `z` with `zᵢ ≠ 0` on `S`. -/
noncomputable def evQ (hz : ∀ i ∈ S, z i ≠ 0) :
    Localization.Away (chartDenom ℂ N S) →+* ℂ :=
  IsLocalization.Away.lift (chartDenom ℂ N S) (g := MvPolynomial.eval z)
    (isUnit_eval_chartDenom S z hz)

/-- The map `evQ S z hz` on a polynomial `a` is the evaluation of `a` at `z`. -/
lemma evQ_algebraMap (hz : ∀ i ∈ S, z i ≠ 0) (a : MvPolynomial (Fin (N + 1)) ℂ) :
    evQ S z hz (algebraMap _ (Localization.Away (chartDenom ℂ N S)) a) = MvPolynomial.eval z a := by
  unfold evQ; exact IsLocalization.Away.lift_eq _ _ _

/-- The map `evQ S z hz` on a fraction `a / s` is `a(z) / s(z)`. -/
lemma evQ_mk (hz : ∀ i ∈ S, z i ≠ 0) (a : MvPolynomial (Fin (N + 1)) ℂ)
    (s : Submonoid.powers (chartDenom ℂ N S)) :
    evQ S z hz (Localization.mk a s) = MvPolynomial.eval z a / MvPolynomial.eval z s := by
  have hs : MvPolynomial.eval z (s : MvPolynomial (Fin (N + 1)) ℂ) ≠ 0 := by
    obtain ⟨_, n, rfl⟩ := s
    change MvPolynomial.eval z (chartDenom ℂ N S ^ n) ≠ 0
    rw [map_pow]
    exact pow_ne_zero n (isUnit_eval_chartDenom S z hz).ne_zero
  refine eq_div_of_mul_eq hs ?_
  have h1 := congrArg (evQ S z hz)
    (IsLocalization.mk'_spec (Localization.Away (chartDenom ℂ N S)) a s)
  rw [map_mul, evQ_algebraMap, evQ_algebraMap] at h1
  rw [Localization.mk_eq_mk']
  exact h1

/-- The value of the monomial `x^m` at `z` is `∏ᵢ zᵢ ^ mᵢ`. -/
lemma eval_monomial_one (m : Fin (N + 1) →₀ ℕ) :
    MvPolynomial.eval z (MvPolynomial.monomial m (1 : ℂ)) = ∏ i, z i ^ m i := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype]
  intro i; rw [pow_zero]

/-- The value of the Laurent fraction `laurentFrac ℂ N S e` at `z` is `∏ᵢ zᵢ ^ eᵢ`. -/
lemma evQ_laurentFrac (hz : ∀ i ∈ S, z i ≠ 0) (e : Fin (N + 1) → ℤ)
    (hout : ∀ i ∉ S, 0 ≤ e i) :
    evQ S z hz (laurentFrac ℂ N S e) = ∏ i, z i ^ e i := by
  classical
  have hin := le_add_clearDen S e
  set M := clearDen S e
  change evQ S z hz (Localization.mk (MvPolynomial.monomial (numExp S e M) (1 : ℂ))
    (chartPow ℂ N S M)) = _
  rw [evQ_mk, eval_monomial_one]
  change _ / MvPolynomial.eval z (chartDenom ℂ N S ^ M) = _
  have hden : MvPolynomial.eval z (chartDenom ℂ N S ^ M) =
      ∏ i, z i ^ (if i ∈ S then (M : ℤ) else 0) := by
    rw [map_pow, chartDenom, map_prod, ← Finset.prod_pow]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
    have h1 : ∏ i ∈ Finset.univ.filter (fun i => i ∈ S), z i ^ (if i ∈ S then (M : ℤ) else 0) =
        ∏ i ∈ S, (MvPolynomial.eval z (MvPolynomial.X i)) ^ M := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_pos hi, zpow_natCast, MvPolynomial.eval_X]
    have h2 : ∏ i ∈ Finset.univ.filter (fun i => i ∉ S), z i ^ (if i ∈ S then (M : ℤ) else 0) = 1 :=
      Finset.prod_eq_one fun i hi => by rw [if_neg (Finset.mem_filter.1 hi).2, zpow_zero]
    rw [h1, h2, mul_one]
  have hnum : ∏ i, z i ^ (numExp S e M i) =
      (∏ i, z i ^ e i) * ∏ i, z i ^ (if i ∈ S then (M : ℤ) else 0) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, natCast_numExp_apply (fun i hi => hout i hi) hin i]
    by_cases hi : i ∈ S
    · rw [if_pos hi, zpow_add₀ (hz i hi)]
    · rw [if_neg hi, add_zero, zpow_zero, mul_one]
  have hne : ∏ i, z i ^ (if i ∈ S then (M : ℤ) else 0) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      by_cases hi : i ∈ S
      · rw [if_pos hi]; exact zpow_ne_zero _ (hz i hi)
      · rw [if_neg hi, zpow_zero]; exact one_ne_zero
  rw [hden, hnum, mul_div_cancel_right₀ _ hne]

/-- The map `evQ S z hz` is `ℂ`-linear. -/
lemma evQ_smul (hz : ∀ i ∈ S, z i ≠ 0) (r : ℂ)
    (m : LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ)) :
    evQ S z hz (r • m) = r * evQ S z hz m := by
  have : (r • m : Localization.Away (chartDenom ℂ N S)) =
      algebraMap (MvPolynomial (Fin (N + 1)) ℂ) _ (MvPolynomial.C r) * m := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  change evQ S z hz (r • m : Localization.Away (chartDenom ℂ N S)) = _
  rw [this, map_mul, evQ_algebraMap, MvPolynomial.eval_C]

/-- `evQ` as a `ℂ`-linear map. -/
noncomputable def evQₗ (hz : ∀ i ∈ S, z i ≠ 0) :
    LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ) →ₗ[ℂ] ℂ where
  toFun := evQ S z hz
  map_add' := map_add _
  map_smul' r m := evQ_smul S z hz r m

/-- **Evaluation of a Laurent polynomial section.** -/
lemma evQ_twistChart (hz : ∀ i ∈ S, z i ≠ 0) (d : ℤ)
    (P : twistChart ℂ N d (↑S : Set (Fin (N + 1)))) :
    evQ S z hz (twistChartEquivTwistSections ℂ N d S P :
        LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ)) =
      (P : (Fin (N + 1) → ℤ) →₀ ℂ).sum fun β r => r * ∏ i, z i ^ β i := by
  let G₁ : twistChart ℂ N d (↑S : Set (Fin (N + 1))) →ₗ[ℂ] ℂ :=
    (evQₗ S z hz) ∘ₗ (twistSections ℂ N d S).subtype ∘ₗ
      (twistChartEquivTwistSections ℂ N d S).toLinearMap
  let G₂ : twistChart ℂ N d (↑S : Set (Fin (N + 1))) →ₗ[ℂ] ℂ :=
    (Finsupp.linearCombination ℂ fun β : Fin (N + 1) → ℤ => ∏ i, z i ^ β i) ∘ₗ
      (twistChart ℂ N d (↑S : Set (Fin (N + 1)))).subtype
  let b := (Finsupp.basisSingleOne (R := ℂ)
    (ι := laurentMonomials N d (↑S : Set (Fin (N + 1))))).map
      (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ)
        (laurentMonomials N d (↑S : Set (Fin (N + 1))))).symm
  have hG : G₁ = G₂ := by
    refine b.ext fun β => ?_
    have hb : ((b β : twistChart ℂ N d (↑S : Set (Fin (N + 1)))) : (Fin (N + 1) → ℤ) →₀ ℂ) =
        Finsupp.single β.1 1 := by
      simp only [b, Module.Basis.map_apply, Finsupp.coe_basisSingleOne,
        Finsupp.supportedEquivFinsupp_symm_single]
    change evQ S z hz (twistChartEquivTwistSections ℂ N d S (b β) :
      LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ)) =
        Finsupp.linearCombination ℂ (fun β : Fin (N + 1) → ℤ => ∏ i, z i ^ β i) (b β : _)
    rw [coe_twistChartEquivTwistSections_single ℂ N d S β.2 _ hb, hb,
      Finsupp.linearCombination_single, one_smul,
      evQ_laurentFrac S z hz β.1 (fun i hi => β.2.2 i (by simpa using hi))]
  have := LinearMap.congr_fun hG P
  change _ = Finsupp.linearCombination ℂ (fun β : Fin (N + 1) → ℤ => ∏ i, z i ^ β i) (P : _) at this
  rw [Finsupp.linearCombination_apply] at this
  simp only [smul_eq_mul] at this
  exact this

end Br

section Triv

open Stacks.ProjectiveSpace.Cohomology Stacks.AlgebraicGeometry.ProjTrivialization
  Stacks.AlgebraicGeometry.ProjPolyChart AlgebraicGeometry.ProjectiveSpectrum.Proj

variable (N : ℕ) (k : ℤ) (j : Fin (N + 1))

/-- The trivializing function of `𝒪(k)` on an open `W ⊆ D₊(x_j)` is a section of `𝒪(k)` over
`W`. -/
lemma trivFun_mem {W : TopologicalSpace.Opens
      (ProjectiveSpectrum.top (polyGrading ℂ N))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading ℂ N)
      (MvPolynomial.X j)) :
    trivializingFun (polyGrading ℂ N) k hW ∈
      moduleSections (polyGrading ℂ N)
        (twistGrading (polyGrading ℂ N) k) W := by
  have := trivializingFun_mem (polyGrading ℂ N)
    (X_mem_one ℂ N j) k hW
  simpa using this

/-- The section `x_j ^ k` of `𝒪(k)` over `D₊(x_j)`. -/
noncomputable def tSec : (𝒪ℙ[N, k]).val.obj
    (op (ProjectiveSpectrum.basicOpen (polyGrading ℂ N)
      (MvPolynomial.X j))) :=
  ⟨trivializingFun (polyGrading ℂ N) k le_rfl,
    trivFun_mem N k j le_rfl⟩

/-- On every open `V ⊆ D₊(x_j)`, multiplication by the restriction of `x_j ^ k` is a bijection from
`𝒪(V)` onto `𝒪(k)(V)`. -/
lemma bijective_smul_tSec
    (V : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Opens)
    (hV : V ≤ ProjectiveSpectrum.basicOpen (polyGrading ℂ N)
      (MvPolynomial.X j)) :
    Function.Bijective (fun a : (AlgebraicGeometry.Proj
        (polyGrading ℂ N)).ringCatSheaf.obj.obj (op V) =>
      a • (𝒪ℙ[N, k]).val.map (homOfLE hV).op
        (tSec N k j)) := by
  have hval : ∀ (a : (AlgebraicGeometry.Proj (polyGrading ℂ N)).ringCatSheaf.obj.obj
      (op V)) (x : V),
      (a • (𝒪ℙ[N, k]).val.map (homOfLE hV).op
        (tSec N k j)).1 x =
      HomogeneousLocalization.val (a.1 x) *
        trivializingFun (polyGrading ℂ N) k hV x := fun _ _ => rfl
  constructor
  · intro a b h
    refine Subtype.ext (funext fun x => eq_of_val_mul_eq _ k hV x ?_)
    exact (hval a x).symm.trans ((congrFun (congrArg Subtype.val h) x).trans (hval b x))
  · intro s
    obtain ⟨r, hr⟩ := (bijective_trivializingHom (polyGrading ℂ N)
      (X_mem_one ℂ N j) k hV).2 ⟨s.1, by simpa using s.2⟩
    exact ⟨r, Subtype.ext (funext fun x => (hval r x).trans (congrFun (congrArg Subtype.val hr) x))⟩

variable (S : Finset (Fin (N + 1)))

/-- For `j ∈ S`, `∏_{i ∈ S} xᵢ = x_j * ∏_{i ∈ S ∖ j} xᵢ`. -/
lemma chartDenom_eq_mul (hj : j ∈ S) :
    chartDenom ℂ N S = MvPolynomial.X j * chartDenom ℂ N (S.erase j) :=
  (Finset.mul_prod_erase S _ hj).symm

/-- For `j ∈ S`, `D₊(∏_{i ∈ S} xᵢ) ⊆ D₊(x_j)`. -/
lemma basicOpen_chartDenom_le_X (hj : j ∈ S) :
    ProjectiveSpectrum.basicOpen (polyGrading ℂ N)
        (chartDenom ℂ N S) ≤
      ProjectiveSpectrum.basicOpen (polyGrading ℂ N)
        (MvPolynomial.X j) := by
  rw [chartDenom_eq_mul N j S hj]
  exact ProjectiveSpectrum.basicOpen_mul_le_left _ _ _

/-- For `j ∈ S`, the open `D₊(∏_{i ∈ S} xᵢ)` is contained in the standard chart `U_j`. -/
lemma le_stdChart (hj : j ∈ S) :
    Proj.basicOpen (polyGrading ℂ N)
      (chartDenom ℂ N S) ≤ (stdChart N j).U := basicOpen_chartDenom_le_X N j S hj

/-- The element `x_j ^ k⁺ * (∏_{i ∈ S ∖ j} xᵢ) ^ k⁻` is homogeneous of degree `k⁻ * |S|` in the
twisted grading of degree `k`. -/
lemma mem_twistGrading_tNum (hj : j ∈ S) :
    MvPolynomial.X j ^ k.toNat * chartDenom ℂ N (S.erase j) ^ (-k).toNat ∈
      twistGrading (polyGrading ℂ N) k
        ((-k).toNat • (S.card : ℤ)) := by
  have hcard : (S.erase j).card + 1 = S.card := Finset.card_erase_add_one hj
  have hdeg : (-k).toNat • (S.card : ℤ) + k =
      ((k.toNat + (-k).toNat * (S.erase j).card : ℕ) : ℤ) := by
    rw [← hcard, nsmul_eq_mul]; push_cast
    have := Int.toNat_sub_toNat_neg k
    linear_combination -this
  rw [twistGrading_apply, hdeg, integerGrading_natCast, mem_homogeneousSubmodule]
  refine SetLike.mul_mem_graded ?_ ?_
  · have := (MvPolynomial.mem_homogeneousSubmodule _ _).2
      ((MvPolynomial.isHomogeneous_X ℂ j).pow k.toNat)
    simpa using this
  · exact SetLike.pow_mem_graded _ (chartDenom_mem_homogeneousSubmodule (R := ℂ) N (S.erase j))

/-- The Laurent fraction of `x_j ^ k` on `D₊(∏_{i ∈ S} xᵢ)`. -/
lemma laurent_tSec (hj : j ∈ S) :
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
        (polyGrading ℂ N)
        (chartDenom_mem_homogeneousSubmodule N S) (Finset.card_pos.2 ⟨j, hj⟩) k
        ((𝒪ℙ[N, k]).val.map
          (homOfLE (le_stdChart N j S hj)).op (tSec N k j)) :
      LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ))) =
    LocalizedModule.mk (MvPolynomial.X j ^ k.toNat * chartDenom ℂ N (S.erase j) ^ (-k).toNat)
      (chartPow ℂ N S (-k).toNat) := by
  let m₀ := degreeZeroFraction (polyGrading ℂ N)
    (twistGrading (polyGrading ℂ N) k)
    (chartDenom_mem_homogeneousSubmodule N S) (-k).toNat _ (mem_twistGrading_tNum N k j S hj)
  have hsec : degreeZeroToSection (polyGrading ℂ N)
      (twistGrading (polyGrading ℂ N) k) (chartDenom ℂ N S) m₀ =
      (𝒪ℙ[N, k]).val.map
          (homOfLE (le_stdChart N j S hj)).op (tSec N k j) := by
    apply Subtype.ext
    funext x
    refine (degreeZeroToSection_fraction _ _ _ _ _ _ x).trans ?_
    change _ = Localization.mk _ _
    refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_eq_mul]
    rw [chartDenom_eq_mul N j S hj, mul_pow]
    ring
  have h2 : associatedModuleSheafStandardOpenEquiv (polyGrading ℂ N)
      (twistGrading (polyGrading ℂ N) k)
      (chartDenom_mem_homogeneousSubmodule N S) (Finset.card_pos.2 ⟨j, hj⟩)
      ((𝒪ℙ[N, k]).val.map
          (homOfLE (le_stdChart N j S hj)).op (tSec N k j)) = m₀ :=
    (LinearEquiv.symm_apply_eq _).2 hsec.symm
  exact congrArg Subtype.val h2

/-- The Laurent fraction of the restriction of `x_j ^ k` to `D₊(∏_{i ∈ S} xᵢ)` evaluates at `z` to
`z j ^ k`. -/
lemma evQ_laurent_tSec (hj : j ∈ S) (z : Fin (N + 1) → ℂ) (hz : ∀ i ∈ S, z i ≠ 0) :
    evQ S z hz ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
        (polyGrading ℂ N)
        (chartDenom_mem_homogeneousSubmodule N S) (Finset.card_pos.2 ⟨j, hj⟩) k
        ((𝒪ℙ[N, k]).val.map
          (homOfLE (le_stdChart N j S hj)).op (tSec N k j)) :
      LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ))) = z j ^ k := by
  rw [laurent_tSec N k j S hj]
  change evQ S z hz (Localization.mk _ _) = _
  rw [evQ_mk]
  have hg : MvPolynomial.eval z (chartDenom ℂ N (S.erase j)) ≠ 0 :=
    (isUnit_eval_chartDenom (S.erase j) z fun i hi => hz i (Finset.mem_of_mem_erase hi)).ne_zero
  have hzj := hz j hj
  change MvPolynomial.eval z
      (MvPolynomial.X j ^ k.toNat * chartDenom ℂ N (S.erase j) ^ (-k).toNat) /
    MvPolynomial.eval z (chartDenom ℂ N S ^ (-k).toNat) = _
  rw [chartDenom_eq_mul N j S hj, map_mul, map_pow, map_pow, map_pow, map_mul, MvPolynomial.eval_X,
    mul_pow, mul_div_mul_right _ _ (pow_ne_zero _ hg)]
  conv_rhs => rw [← Int.toNat_sub_toNat_neg k]
  rw [zpow_sub₀ hzj, zpow_natCast, zpow_natCast]

end Triv

section EvalAn

open Stacks.ProjectiveSpace.Cohomology Stacks.AlgebraicGeometry.ProjPolyChart
  AlgebraicGeometry.ProjectiveSpectrum.Proj MMP.UnderlyingSpace

variable (N : ℕ) (j : Fin (N + 1))

/-- The homogeneous coordinates `(x_m / x_j)(y)` of a point of the chart `U_j`. -/
noncomputable def hcoord (y : chart (sX := sP N) (stdChart N j).U) : Fin (N + 1) → ℂ :=
  fun m => evalHom (stdChart N j).U y (projectiveSpaceStdCoord ℂ N j m)

/-- The homogeneous coordinate `x_j / x_j` of a point of `U_j` is `1`. -/
lemma hcoord_self (y : chart (sX := sP N) (stdChart N j).U) : hcoord N j y j = 1 := by
  have h := projectiveSpaceStdCoord_self (K := ℂ) (n := N) j
  unfold hcoord
  refine Eq.trans ?_ (map_one (evalHom (stdChart N j).U y))
  exact congrArg (evalHom (stdChart N j).U y) h

/-- The homogeneous coordinate `x_{σ i} / x_j` of a point of `U_j` is its `i`-th affine
coordinate. -/
lemma hcoord_succAbove (y : chart (sX := sP N) (stdChart N j).U) (i : Fin N) :
    hcoord N j y (j.succAbove i) = (stdChart N j).coords y i := rfl

/-- At a point of `U_j` in `D₊(∏_{i ∈ S} xᵢ)`, the homogeneous coordinates indexed by `S` are
nonzero. -/
lemma hcoord_ne_zero (S : Finset (Fin (N + 1))) (y : chart (sX := sP N) (stdChart N j).U)
    (hy : y.1.toScheme ∈ Proj.basicOpen
      (polyGrading ℂ N) (chartDenom ℂ N S)) :
    ∀ i ∈ S, hcoord N j y i ≠ 0 := by
  intro i hi
  refine (toScheme_mem_basicOpen_iff y _).1 ?_
  have h := basicOpen_projectiveSpaceStdCoord (K := ℂ) (n := N) j i
  have hmem : y.1.toScheme ∈ projectiveSpaceStdChart ℂ N j ⊓ projectiveSpaceStdChart ℂ N i :=
    ⟨mem_chart_iff.1 y.2, basicOpen_chartDenom_le_X N i S hi hy⟩
  rwa [← h] at hmem

/-- **`α^#` on a standard open reads a degree-zero fraction at its homogeneous coordinates.** -/
lemma secVal_sharpHom_awayToSection (S : Finset (Fin (N + 1))) (hj : j ∈ S)
    (x : (Opens.map (toSchemeHom (sP N))).obj (Proj.basicOpen
      (polyGrading ℂ N) (chartDenom ℂ N S)))
    (hx : x.1 ∈ chart (sX := sP N) (stdChart N j).U)
    (q : HomogeneousLocalization.Away (polyGrading ℂ N)
      (chartDenom ℂ N S)) :
    secVal (sharpHom _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)) x (stdChart N j) hx =
      evQ S (hcoord N j ⟨x.1, hx⟩) (hcoord_ne_zero N j S ⟨x.1, hx⟩ x.2)
        (HomogeneousLocalization.val q) := by
  set y : chart (sX := sP N) (stdChart N j).U := ⟨x.1, hx⟩
  set z := hcoord N j y
  have hz := hcoord_ne_zero N j S y x.2
  let Φ1 : HomogeneousLocalization.Away (polyGrading ℂ N)
      (chartDenom ℂ N S) →+* ℂ :=
    ((stalkRingValue (stdChart N j) y).comp ((Chart.sectionComponent (stdChart N j) x.1 hx _
      x.2).comp (sharpHom _))).comp (Proj.awayToSection _ (chartDenom ℂ N S)).hom
  let Φ2 : HomogeneousLocalization.Away (polyGrading ℂ N)
      (chartDenom ℂ N S) →+* ℂ :=
    (evQ S z hz).comp (algebraMap _ (Localization.Away (chartDenom ℂ N S)))
  suffices h : Φ1 = Φ2 from RingHom.congr_fun h q
  have hg := chartDenom_mem_homogeneousSubmodule (R := ℂ) N (S.erase j)
  have hx' := chartDenom_eq_mul N j S hj
  letI := (HomogeneousLocalization.awayMap _ hg hx').toAlgebra
  haveI := HomogeneousLocalization.Away.isLocalization_mul (X_mem_one ℂ N j) hg hx' one_ne_zero
  refine IsLocalization.ringHom_ext (Submonoid.powers
    (HomogeneousLocalization.Away.isLocalizationElem (X_mem_one ℂ N j) hg)) ?_
  refine (RingHom.cancel_right (chartHom_surjective ℂ N j)).1 ?_
  have hres : ∀ a, (Proj.awayToSection _ (chartDenom ℂ N S)).hom
      (HomogeneousLocalization.awayMap _ hg hx' a) =
      (AlgebraicGeometry.Proj (polyGrading ℂ N)).presheaf.map
        (homOfLE (le_stdChart N j S hj)).op
        ((Proj.awayToSection _ (MvPolynomial.X j)).hom a) := fun a =>
    congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection _ hg hx')
  have e1 : ∀ a, Φ1 (HomogeneousLocalization.awayMap _ hg hx' a) =
      evalHom (stdChart N j).U y ((Proj.awayToSection _ (MvPolynomial.X j)).hom a) := by
    intro a
    refine (congrArg (fun t => secVal (sharpHom (Proj.basicOpen
      (polyGrading ℂ N) (chartDenom ℂ N S)) t) x (stdChart N j) hx)
      (hres a)).trans ?_
    exact secVal_sharpHom_res (c := stdChart N j) (le_stdChart N j S hj) _ x hx
  have hg0 : MvPolynomial.eval z (chartDenom ℂ N (S.erase j)) ≠ 0 :=
    (isUnit_eval_chartDenom (S.erase j) z fun i hi => hz i (Finset.mem_of_mem_erase hi)).ne_zero
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, chartHom_C]
    change Φ1 (HomogeneousLocalization.awayMap _ hg hx' (coeffToAway ℂ N j c)) =
      Φ2 (HomogeneousLocalization.awayMap _ hg hx' (coeffToAway ℂ N j c))
    rw [e1]
    have h1 : (Proj.awayToSection _ (MvPolynomial.X j)).hom (coeffToAway ℂ N j c) =
        baseRingHom (sP N) (stdChart N j).U c := by
      rw [baseRingHom_eq]
      exact (structureRingHomOpens_projectiveSpaceStdChart (hO := ⟨sP N⟩) rfl j c).symm
    rw [h1, evalHom_baseRingHom]
    change c = evQ S z hz (HomogeneousLocalization.val
      (HomogeneousLocalization.awayMap _ hg hx' (coeffToAway ℂ N j c)))
    rw [coeffToAway_eq_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
      evQ_mk]
    simp
  · simp only [RingHom.coe_comp, Function.comp_apply, chartHom_X]
    change Φ1 (HomogeneousLocalization.awayMap _ hg hx' (chartCoord ℂ N j m)) =
      Φ2 (HomogeneousLocalization.awayMap _ hg hx' (chartCoord ℂ N j m))
    rw [e1]
    change z m.1 = evQ S z hz (HomogeneousLocalization.val
      (HomogeneousLocalization.awayMap _ hg hx' (chartCoord ℂ N j m)))
    rw [chartCoord, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
      evQ_mk]
    change z m.1 = MvPolynomial.eval z (MvPolynomial.X m.1 * chartDenom ℂ N (S.erase j) ^ 1) /
      MvPolynomial.eval z (chartDenom ℂ N S ^ 1)
    rw [hx', pow_one, pow_one, map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X,
      show z j = 1 from hcoord_self N j y, one_mul, mul_div_cancel_right₀ _ hg0]

end EvalAn

section LaurentModel

open Stacks.ProjectiveSpace.Cohomology

variable (N : ℕ) (k : ℤ)

/-- The convergent Laurent coefficient families of degree `k` regular outside `S`. -/
def laurentSections (S : Finset (Fin (N + 1))) :
    AddSubgroup ((Fin (N + 1) → ℤ) → ℂ) where
  carrier := {f | (∀ β, f β ≠ 0 → β ∈ laurentMonomials N k (S : Set (Fin (N + 1)))) ∧
    ∀ z : Fin (N + 1) → ℂ, (∀ i ∈ S, z i ≠ 0) → Summable fun β => ‖f β * mono z β‖}
  add_mem' {f g} hf hg := by
    refine ⟨fun β h => ?_, fun z hz => ?_⟩
    · by_cases h0 : f β = 0
      · exact hg.1 β fun h' => h (by simp [h0, h'])
      · exact hf.1 β h0
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun β => ?_)
        ((hf.2 z hz).add (hg.2 z hz))
      rw [Pi.add_apply, add_mul]
      exact norm_add_le _ _
  zero_mem' := ⟨fun _ h => absurd rfl h, fun _ _ => by simpa using summable_zero⟩
  neg_mem' {f} hf := ⟨fun β h => hf.1 β fun h' => h (by simp [h']),
    fun z hz => by simpa [neg_mul, norm_neg] using hf.2 z hz⟩

variable {N} (S : Finset (Fin (N + 1))) (j : Fin (N + 1))

/-- The disc factors of the dehomogenized domain: the coordinates `x_{σ i} / x_j` with
`σ i ∉ S`. -/
def sdisc : Set (Fin N) := {i | j.succAbove i ∉ S}

variable {S j}

/-- For `j ∈ S` and `zᵢ ≠ 0` on `S`, the dehomogenization `dehom j z` lies in
`lDom (sdisc S j)`. -/
lemma dehom_mem (hj : j ∈ S) {z : Fin (N + 1) → ℂ} (hz : ∀ i ∈ S, z i ≠ 0) :
    dehom j z ∈ lDom (sdisc S j) := by
  intro i hi
  simp only [sdisc, Set.mem_setOf_eq, not_not] at hi
  exact div_ne_zero (hz _ hi) (hz j hj)

/-- The point `(w, 1)` with `1` inserted at `j`. -/
abbrev insertOne (j : Fin (N + 1)) (w : Fin N → ℂ) : Fin (N + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) j 1 w

/-- For `j ∈ S` and `w ∈ lDom (sdisc S j)`, the coordinates of `insertOne j w` indexed by `S` are
nonzero. -/
lemma insertNth_ne_zero (hj : j ∈ S) {w : Fin N → ℂ} (hw : w ∈ lDom (sdisc S j)) :
    ∀ i ∈ S, insertOne j w i ≠ 0 := by
  intro i hi
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨m, rfl⟩
  · simp [insertOne]
  · simp only [insertOne, Fin.insertNth_apply_succAbove]
    exact hw m (by simpa [sdisc] using hi)

/-- Dehomogenizing `insertOne j w` at `j` gives back `w`. -/
lemma dehom_insertNth (w : Fin N → ℂ) : dehom j (insertOne j w) = w := by
  funext i
  simp [dehom]

/-- **Laurent coefficients of a holomorphic function on the dehomogenized domain.** -/
lemma exists_laurentSections (hj : j ∈ S) (g : (Fin N → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g (lDom (sdisc S j))) :
    ∃ c ∈ laurentSections N k S, ∀ z : Fin (N + 1) → ℂ, (∀ i ∈ S, z i ≠ 0) →
      HasSum (fun β => c β * mono z β) (z j ^ k * g (dehom j z)) := by
  classical
  obtain ⟨a, ha0, ha⟩ := exists_laurent (sdisc S j) g hg
  let c : (Fin (N + 1) → ℤ) → ℂ := fun β => if ∑ i, β i = k then a (β ∘ j.succAbove) else 0
  have hca : ∀ γ, c (homIdx k j γ) = a γ := fun γ => by
    simp only [c, sum_homIdx, if_true]
    congr 1; funext i; exact homIdx_succAbove k j γ i
  have hc0 : ∀ β ∉ Set.range (homIdx k j), c β = 0 := fun β hβ => by
    rw [mem_range_homIdx] at hβ
    simp only [c, if_neg hβ]
  have key : ∀ z : Fin (N + 1) → ℂ, (∀ i ∈ S, z i ≠ 0) → ∀ γ,
      c (homIdx k j γ) * mono z (homIdx k j γ) =
        z j ^ k * (a γ * ∏ i, dehom j z i ^ γ i) := fun z hz γ => by
    rw [hca, mono, mono_homIdx k j z (hz j hj)]; ring
  refine ⟨c, ⟨fun β hβ => ?_, fun z hz => ?_⟩, fun z hz => ?_⟩
  · have hsum : ∑ i, β i = k := by by_contra h; exact hβ (by simp [c, h])
    refine ⟨hsum, fun i hi => ?_⟩
    have hij : i ≠ j := fun h => hi (by simpa [h] using hj)
    obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hij
    by_contra hneg
    push Not at hneg
    have : a (β ∘ j.succAbove) = 0 :=
      ha0 _ ⟨m, by simpa [sdisc] using hi, by simpa using hneg⟩
    exact hβ (by simp [c, hsum, this])
  · refine (homIdx_injective k j).summable_iff (f := fun β => ‖c β * mono z β‖)
      (fun β hβ => by simp [hc0 β hβ]) |>.1 ?_
    have h1 := ((ha (dehom j z) (dehom_mem hj hz)).1).mul_left ‖z j ^ k‖
    refine h1.congr fun γ => ?_
    simp only [Function.comp_apply]
    rw [key z hz γ, norm_mul, norm_mul, norm_mul]
  · refine (homIdx_injective k j).hasSum_iff (f := fun β => c β * mono z β)
      (fun β hβ => by simp [hc0 β hβ]) |>.1 ?_
    have h1 := ((ha (dehom j z) (dehom_mem hj hz)).2).mul_left (z j ^ k)
    refine h1.congr_fun fun γ => ?_
    simp only [Function.comp_apply]
    rw [key z hz γ]

omit j in
/-- **Uniqueness of convergent homogeneous Laurent expansions.** -/
lemma eq_of_hasSum_laurentSections {c c' : (Fin (N + 1) → ℤ) → ℂ} (hc : c ∈ laurentSections N k S)
    (hc' : c' ∈ laurentSections N k S) (G : (Fin (N + 1) → ℂ) → ℂ)
    (h : ∀ z : Fin (N + 1) → ℂ, (∀ i ∈ S, z i ≠ 0) → HasSum (fun β => c β * mono z β) (G z))
    (h' : ∀ z : Fin (N + 1) → ℂ, (∀ i ∈ S, z i ≠ 0) → HasSum (fun β => c' β * mono z β) (G z)) :
    c = c' := by
  have hd : c - c' ∈ laurentSections N k S := sub_mem hc hc'
  have hsum : Summable fun β => ‖(c - c') β‖ := by
    refine (hd.2 1 fun _ _ => one_ne_zero).congr fun β => ?_
    simp [mono]
  have h0 := laurent_unique_torus (n := N + 1) (c - c') hsum fun w hw => by
    have hw' : ∀ i ∈ S, w i ≠ 0 := fun i _ h0 => by simpa [h0] using hw i
    have := (h w hw').sub (h' w hw')
    rw [sub_self] at this
    refine Eq.trans ?_ this.tsum_eq
    congr 1; funext β; simp only [Pi.sub_apply, mono]; ring
  exact sub_eq_zero.1 h0

omit j in
/-- The dehomogenized coefficients of a homogeneous family. -/
def dehomCoeff (j' : Fin (N + 1)) (c : (Fin (N + 1) → ℤ) → ℂ) : (Fin N → ℤ) → ℂ :=
  fun γ => c (homIdx k j' γ)

/-- The dehomogenized coefficients of a family in `laurentSections N k S` vanish at exponents
negative at some index of `sdisc S j`. -/
lemma dehomCoeff_zero {c : (Fin (N + 1) → ℤ) → ℂ} (hc : c ∈ laurentSections N k S) :
    ∀ γ, (∃ i ∈ sdisc S j, γ i < 0) → dehomCoeff k j c γ = 0 := by
  rintro γ ⟨i, hi, hγ⟩
  by_contra h
  have := (hc.1 _ h).2 (j.succAbove i) (by simpa [sdisc] using hi)
  rw [homIdx_succAbove] at this
  omega

omit S in
/-- A family in `laurentSections N k S` vanishes off the exponents of total degree `k`. -/
lemma vanish_off_range {S : Finset (Fin (N + 1))} {c : (Fin (N + 1) → ℤ) → ℂ}
    (hc : c ∈ laurentSections N k S) :
    ∀ β ∉ Set.range (homIdx k j), c β = 0 := fun β hβ => by
  by_contra h
  exact hβ ((mem_range_homIdx k j β).2 (hc.1 β h).1)

/-- **A convergent homogeneous Laurent family defines a holomorphic function on the
dehomogenized domain.** -/
lemma differentiableOn_of_laurentSections (hj : j ∈ S) {c : (Fin (N + 1) → ℤ) → ℂ}
    (hc : c ∈ laurentSections N k S) :
    DifferentiableOn ℂ (fun w => ∑' γ, dehomCoeff k j c γ * ∏ i, w i ^ γ i) (lDom (sdisc S j)) ∧
      ∀ z : Fin (N + 1) → ℂ, (∀ i ∈ S, z i ≠ 0) →
        HasSum (fun β => c β * mono z β)
          (z j ^ k * ∑' γ, dehomCoeff k j c γ * ∏ i, dehom j z i ^ γ i) := by
  have key : ∀ z : Fin (N + 1) → ℂ, z j ≠ 0 → ∀ γ,
      c (homIdx k j γ) * mono z (homIdx k j γ) =
        z j ^ k * (dehomCoeff k j c γ * ∏ i, dehom j z i ^ γ i) := fun z hz γ => by
    rw [dehomCoeff, mono, mono_homIdx k j z hz]; ring
  have hsumw : ∀ w ∈ lDom (sdisc S j),
      Summable fun γ => ‖dehomCoeff k j c γ * ∏ i, w i ^ γ i‖ := by
    intro w hw
    have h1 := (hc.2 (insertOne j w) (insertNth_ne_zero hj hw)).comp_injective
      (homIdx_injective k j)
    refine h1.congr fun γ => ?_
    simp only [Function.comp_apply]
    rw [key _ (by simp [insertOne]) γ, dehom_insertNth]
    simp [insertOne]
  refine ⟨differentiableOn_laurent (sdisc S j) _ (dehomCoeff_zero k hc) hsumw, fun z hz => ?_⟩
  have hs : Summable fun β => c β * mono z β := (hc.2 z hz).of_norm
  have e : ∑' β, c β * mono z β =
      z j ^ k * ∑' γ, dehomCoeff k j c γ * ∏ i, dehom j z i ^ γ i := by
    rw [← (homIdx_injective k j).tsum_eq (f := fun β => c β * mono z β) (fun β hβ => by
      by_contra h
      exact hβ (by simp [vanish_off_range (j := j) k hc β h])), ← tsum_mul_left]
    congr 1
    funext γ
    exact key z (hz j hj) γ
  exact e ▸ hs.hasSum

end LaurentModel

section GeoModel

open Stacks.ProjectiveSpace.Cohomology Stacks.AlgebraicGeometry.ProjPolyChart
  AlgebraicGeometry.ProjectiveSpectrum.Proj MMP.UnderlyingSpace

attribute [local instance] locallyOfFiniteType_sP

variable (N : ℕ) (k : ℤ)

/-- A point lies in `D₊(∏_{i ∈ S} xᵢ)` if and only if it lies in `D₊(xᵢ)` for every `i ∈ S`. -/
lemma mem_basicOpen_chartDenom (S : Finset (Fin (N + 1)))
    (x : ProjectiveSpectrum (polyGrading ℂ N)) :
    x ∈ ProjectiveSpectrum.basicOpen (polyGrading ℂ N)
        (chartDenom ℂ N S) ↔
      ∀ i ∈ S, x ∈ ProjectiveSpectrum.basicOpen
        (polyGrading ℂ N) (MvPolynomial.X i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [chartDenom, ProjectiveSpectrum.basicOpen_one]
  | insert a S ha ih =>
    rw [chartDenom, Finset.prod_insert ha, ← chartDenom, ProjectiveSpectrum.basicOpen_mul]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    exact and_congr Iff.rfl ih

variable {N} (j : Fin (N + 1))

/-- A point `y` of `U_j` lies in `D₊(xᵢ)` if and only if its homogeneous coordinate `x_i / x_j` is
nonzero. -/
lemma toScheme_mem_X_iff (y : chart (sX := sP N) (stdChart N j).U) (i : Fin (N + 1)) :
    y.1.toScheme ∈ ProjectiveSpectrum.basicOpen
        (polyGrading ℂ N) (MvPolynomial.X i) ↔
      hcoord N j y i ≠ 0 := by
  have h := basicOpen_projectiveSpaceStdCoord (K := ℂ) (n := N) j i
  have e := toScheme_mem_basicOpen_iff y (projectiveSpaceStdCoord ℂ N j i)
  have h' : (AlgebraicGeometry.Proj (polyGrading ℂ N)).basicOpen
      (projectiveSpaceStdCoord ℂ N j i) ≤
      projectiveSpaceStdChart ℂ N i := h ▸ inf_le_right
  refine ⟨fun hi => e.1 ?_, fun hne => h' (e.2 hne)⟩
  have hmem : y.1.toScheme ∈ projectiveSpaceStdChart ℂ N j ⊓ projectiveSpaceStdChart ℂ N i :=
    ⟨mem_chart_iff.1 y.2, hi⟩
  rwa [← h] at hmem

/-- A point `y` of `U_j` lies in `D₊(∏_{i ∈ S} xᵢ)` if and only if its homogeneous coordinates
indexed by `S` are nonzero. -/
lemma toScheme_mem_chartDenom_iff (S : Finset (Fin (N + 1)))
    (y : chart (sX := sP N) (stdChart N j).U) :
    y.1.toScheme ∈ ProjectiveSpectrum.basicOpen
        (polyGrading ℂ N) (chartDenom ℂ N S) ↔
      ∀ i ∈ S, hcoord N j y i ≠ 0 :=
  (mem_basicOpen_chartDenom N S y.1.toScheme).trans
    (forall₂_congr fun i _ => toScheme_mem_X_iff j y i)

/-- The homogeneous coordinates of a point of `U_j` are its affine coordinates with `1` inserted at
`j`. -/
lemma hcoord_eq_insertOne (y : chart (sX := sP N) (stdChart N j).U) :
    hcoord N j y = insertOne j ((stdChart N j).coords y) := by
  funext m
  rcases Fin.eq_self_or_eq_succAbove j m with rfl | ⟨i, rfl⟩
  · rw [hcoord_self]
    exact (Fin.insertNth_apply_same (α := fun _ => ℂ) m 1 _).symm
  · rw [hcoord_succAbove]
    exact (Fin.insertNth_apply_succAbove (α := fun _ => ℂ) j 1 _ i).symm

/-- The points of the chart `U_j` are their affine coordinates. -/
noncomputable def coordsEquiv : chart (sX := sP N) (stdChart N j).U ≃ (Fin N → ℂ) :=
  Equiv.ofBijective _ ⟨coords_injective (c := stdChart N j) (stdChart_ideal N j),
    surjective_coords (stdChart N j) (stdChart_ideal N j)⟩

variable (N)

/-- `W(S) = α⁻¹ D₊(∏_{i ∈ S} xᵢ)`. -/
noncomputable abbrev WS (S : Finset (Fin (N + 1))) : TopologicalSpace.Opens (space (sP N)) :=
  (Opens.map (toSchemeHom (sP N))).obj
    (Proj.basicOpen (polyGrading ℂ N) (chartDenom ℂ N S))

variable {N}

/-- For `j ∈ S`, every point of `W(S)` lies in the chart `U_j`. -/
lemma mem_chart_of_WS {S : Finset (Fin (N + 1))} (hj : j ∈ S) (x : WS N S) :
    x.1 ∈ chart (sX := sP N) (stdChart N j).U :=
  mem_chart_iff.2 (le_stdChart N j S hj x.2)

/-- For `j ∈ S`, `W(S)` is contained in `α⁻¹ U_j`. -/
lemma WS_le {S : Finset (Fin (N + 1))} (hj : j ∈ S) :
    WS N S ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U :=
  fun _ hx => le_stdChart N j S hj hx

variable (N)

/-- `𝒪(k)^an`. -/
noncomputable abbrev Lan := (analytifyModule (sP N)).obj (𝒪ℙ[N, k])

/-- The analytification `u_j` of `x_j ^ k`. -/
noncomputable def uSec : (Lan N k).val.obj (op ((Opens.map (toSchemeHom (sP N))).obj
    (stdChart N j).U)) :=
  unitHom (sX := sP N) (L := 𝒪ℙ[N, k])
    (stdChart N j).U (tSec N k j)

/-- On every open `W ⊆ α⁻¹ U_j`, multiplication by the restriction of `u_j` is a bijection from
`𝒪_{X^an}(W)` onto `𝒪(k)^an(W)`. -/
lemma bijective_smul_uSec (W : TopologicalSpace.Opens (space (sP N)))
    (hW : W ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U) :
    Function.Bijective (fun f : (ringCatSheaf (sP N)).obj.obj (op W) =>
      f • (Lan N k).val.map (homOfLE hW).op (uSec N k j)) :=
  ⟨injective_smul_unit (fun V hV => bijective_smul_tSec N k j V hV) W hW,
    surjective_smul_unit (fun V hV => bijective_smul_tSec N k j V hV) W hW⟩

/-- The coefficient of a section of `𝒪(k)^an` with respect to `u_j`. -/
noncomputable def secOf (W : TopologicalSpace.Opens (space (sP N)))
    (hW : W ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op W)) : (ringCatSheaf (sP N)).obj.obj (op W) :=
  (Equiv.ofBijective _ (bijective_smul_uSec N k j W hW)).symm s

/-- A section `s` of `𝒪(k)^an` over `W ⊆ α⁻¹ U_j` is `secOf N k j W hW s` times `u_j`. -/
lemma secOf_smul (W : TopologicalSpace.Opens (space (sP N)))
    (hW : W ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op W)) :
    secOf N k j W hW s • (Lan N k).val.map (homOfLE hW).op (uSec N k j) = s :=
  (Equiv.ofBijective _ (bijective_smul_uSec N k j W hW)).apply_symm_apply s

/-- If `s = f • u_j` on `W ⊆ α⁻¹ U_j`, then `secOf N k j W hW s = f`. -/
lemma secOf_eq (W : TopologicalSpace.Opens (space (sP N)))
    (hW : W ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op W)) (f : (ringCatSheaf (sP N)).obj.obj (op W))
    (h : f • (Lan N k).val.map (homOfLE hW).op (uSec N k j) = s) :
    secOf N k j W hW s = f :=
  (Equiv.ofBijective _ (bijective_smul_uSec N k j W hW)).symm_apply_eq.2 h.symm

variable {N}

/-- The point of `W(S)` with affine coordinates `w` in the chart `U_j`. -/
noncomputable def ptW {S : Finset (Fin (N + 1))} (hj : j ∈ S) (w : Fin N → ℂ)
    (hw : w ∈ lDom (sdisc S j)) : WS N S :=
  ⟨((coordsEquiv j).symm w).1, by
    refine (toScheme_mem_chartDenom_iff j S ((coordsEquiv j).symm w)).2 ?_
    rw [hcoord_eq_insertOne]
    change ∀ i ∈ S, insertOne j (coordsEquiv j ((coordsEquiv j).symm w)) i ≠ 0
    rw [Equiv.apply_symm_apply]
    exact insertNth_ne_zero hj hw⟩

/-- The affine coordinates of `ptW j hj w hw` in the chart `U_j` are `w`. -/
lemma coords_ptW {S : Finset (Fin (N + 1))} (hj : j ∈ S) (w : Fin N → ℂ)
    (hw : w ∈ lDom (sdisc S j)) :
    (stdChart N j).coords ⟨(ptW j hj w hw).1, mem_chart_of_WS j hj _⟩ = w :=
  (coordsEquiv j).apply_symm_apply w

variable (N)

/-- The holomorphic function of the affine coordinates of `U_j` representing a section of
`𝒪(k)^an` over `W(S)`. -/
noncomputable def gfun {S : Finset (Fin (N + 1))} (hj : j ∈ S)
    (s : (Lan N k).val.obj (op (WS N S))) :
    (Fin N → ℂ) → ℂ :=
  holFun (c := stdChart N j) (mem_chart_of_WS j hj) (secOf N k j (WS N S) (WS_le j hj) s)

variable {N}

/-- The value of `gfun N k j hj s` at `w` is the value of the coefficient of `s` at
`ptW j hj w hw`. -/
lemma gfun_apply {S : Finset (Fin (N + 1))} (hj : j ∈ S) (s : (Lan N k).val.obj (op (WS N S)))
    (w : Fin N → ℂ) (hw : w ∈ lDom (sdisc S j)) :
    gfun N k j hj s w = secVal (secOf N k j (WS N S) (WS_le j hj) s) (ptW j hj w hw)
      (stdChart N j) (mem_chart_of_WS j hj _) := by
  have := holFun_coords (stdChart_ideal N j) (mem_chart_of_WS j hj)
    (secOf N k j (WS N S) (WS_le j hj) s) (ptW j hj w hw)
  rw [coords_ptW] at this
  exact this

/-- The function `gfun N k j hj s` is holomorphic on `lDom (sdisc S j)`. -/
lemma differentiableOn_gfun {S : Finset (Fin (N + 1))} (hj : j ∈ S)
    (s : (Lan N k).val.obj (op (WS N S))) :
    DifferentiableOn ℂ (gfun N k j hj s) (lDom (sdisc S j)) := by
  intro w hw
  have := differentiableAt_holFun (stdChart_ideal N j) (mem_chart_of_WS j hj)
    (secOf N k j (WS N S) (WS_le j hj) s) (ptW j hj w hw)
  rw [coords_ptW] at this
  exact this.differentiableWithinAt

/-- The map `evQ S z hz` depends only on `z`. -/
lemma evQ_congr {S : Finset (Fin (N + 1))} {z z' : Fin (N + 1) → ℂ} (h : z = z')
    (hz : ∀ i ∈ S, z i ≠ 0) (hz' : ∀ i ∈ S, z' i ≠ 0) (m : Localization.Away (chartDenom ℂ N S)) :
    evQ S z hz m = evQ S z' hz' m := by subst h; rfl

/-- The homogeneous coordinates of `ptW j hj w hw` in the chart `U_j` are `insertOne j w`. -/
lemma hcoord_ptW {S : Finset (Fin (N + 1))} (hj : j ∈ S) (w : Fin N → ℂ)
    (hw : w ∈ lDom (sdisc S j)) :
    hcoord N j ⟨(ptW j hj w hw).1, mem_chart_of_WS j hj _⟩ = insertOne j w := by
  rw [hcoord_eq_insertOne, coords_ptW]

/-- For nonempty `S`, the map `Proj.awayToSection` at `∏_{i ∈ S} xᵢ` is bijective. -/
lemma bijective_awayToSection {S : Finset (Fin (N + 1))} (hS : S.Nonempty) :
    Function.Bijective (Proj.awayToSection (polyGrading ℂ N)
      (chartDenom ℂ N S)).hom := by
  have := ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (polyGrading ℂ N) (chartDenom ℂ N S)
      (chartDenom_mem_homogeneousSubmodule N S) (Finset.card_pos.2 hS)).hom
  rwa [Proj.basicOpenIsoAway_hom] at this

/-- On `W(S)`, the coefficient function of the analytification of an algebraic
section of `𝒪(k)` is its Laurent fraction, evaluated. -/
lemma gfun_unitHom {S : Finset (Fin (N + 1))} (hj : j ∈ S)
    (c : (𝒪ℙ[N, k]).val.obj
      (op (Proj.basicOpen (polyGrading ℂ N) (chartDenom ℂ N S))))
    (w : Fin N → ℂ) (hw : w ∈ lDom (sdisc S j)) :
    gfun N k j hj (unitHom (sX := sP N) (L := 𝒪ℙ[N, k])
        _ c) w =
      evQ S (insertOne j w) (insertNth_ne_zero hj hw)
        ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
          (polyGrading ℂ N)
          (chartDenom_mem_homogeneousSubmodule N S) (Finset.card_pos.2 ⟨j, hj⟩) k c :
            LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ))) := by
  refine ((bijective_smul_tSec N k j
    (Proj.basicOpen (polyGrading ℂ N) (chartDenom ℂ N S))
    (le_stdChart N j S hj)).2 c).elim fun a ha => ?_
  refine ((bijective_awayToSection (S := S) ⟨j, hj⟩).2 a).elim fun q hq => ?_
  subst hq
  beta_reduce at ha
  have hu : unitHom (sX := sP N) (L := 𝒪ℙ[N, k]) _ c =
      (show (ringCatSheaf (sP N)).obj.obj (op (WS N S)) from
        sharpHom _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)) •
        (Lan N k).val.map (homOfLE (WS_le j hj)).op (uSec N k j) := by
    rw [← ha]
    refine (unitHom_smul (sX := sP N) (L := 𝒪ℙ[N, k])
      _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q) _).trans ?_
    congr 1
    exact unitHom_naturality (sX := sP N) (L := 𝒪ℙ[N, k])
      (le_stdChart N j S hj) (tSec N k j)
  have hsec := secOf_eq N k j (WS N S) (WS_le j hj) _ _ hu.symm
  have e1 : gfun N k j hj (unitHom (sX := sP N)
      (L := 𝒪ℙ[N, k]) _ c) w =
      secVal (sharpHom _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)) (ptW j hj w hw)
        (stdChart N j) (mem_chart_of_WS j hj _) :=
    (gfun_apply k j hj _ w hw).trans (congrArg (fun f => secVal f (ptW j hj w hw)
      (stdChart N j) (mem_chart_of_WS j hj _)) hsec)
  refine e1.trans ((secVal_sharpHom_awayToSection N j S hj (ptW j hj w hw)
    (mem_chart_of_WS j hj _) q).trans ?_)
  subst ha
  have e2 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul
    (polyGrading ℂ N) (chartDenom_mem_homogeneousSubmodule N S)
    (Finset.card_pos.2 ⟨j, hj⟩) k q
    ((𝒪ℙ[N, k]).val.map
      (homOfLE (le_stdChart N j S hj)).op (tSec N k j))
  have e3 := evQ_laurent_tSec N k j S hj (insertOne j w) (insertNth_ne_zero hj hw)
  have e4 : insertOne j w j = 1 := by simp [insertOne]
  refine (evQ_congr (hcoord_ptW j hj w hw) _ (insertNth_ne_zero hj hw) _).trans ?_
  refine Eq.trans ?_ (congrArg (evQ S (insertOne j w) (insertNth_ne_zero hj hw)) e2).symm
  change _ = evQ S (insertOne j w) _ (HomogeneousLocalization.val q * _)
  rw [map_mul, e3, e4, one_zpow, mul_one]

/-- For `S ⊆ S'`, `W(S') ⊆ W(S)`. -/
lemma WS_mono {S S' : Finset (Fin (N + 1))} (h : S ⊆ S') : WS N S' ≤ WS N S :=
  (Opens.map (toSchemeHom (sP N))).monotone (basicOpen_chartDenom_le ℂ N S S' h)

/-- For `S ⊆ S'`, `sdisc S' j ⊆ sdisc S j`. -/
lemma sdisc_mono {S S' : Finset (Fin (N + 1))} (h : S ⊆ S') : sdisc S' j ⊆ sdisc S j :=
  fun _ hi hS => hi (h hS)

/-- For `s' ⊆ s`, `lDom s' ⊆ lDom s`. -/
lemma lDom_mono {n : ℕ} {s s' : Set (Fin n)} (h : s' ⊆ s) : lDom s' ⊆ lDom s :=
  fun _ hw i hi => hw i fun hi' => hi (h hi')

/-- The coefficient with respect to `u_j` commutes with restriction from `W(S)` to `W(S')`. -/
lemma secOf_restrict {S S' : Finset (Fin (N + 1))} (hj : j ∈ S) (h : S ⊆ S')
    (s : (Lan N k).val.obj (op (WS N S))) :
    secOf N k j (WS N S') (WS_le j (h hj)) ((Lan N k).val.map (homOfLE (WS_mono h)).op s) =
      (ringCatSheaf (sP N)).obj.map (homOfLE (WS_mono h)).op
        (secOf N k j (WS N S) (WS_le j hj) s) := by
  refine secOf_eq N k j _ _ _ _ ?_
  conv_rhs => rw [← secOf_smul N k j (WS N S) (WS_le j hj) s]
  exact (map_smul_unit (L := 𝒪ℙ[N, k])
    (t := tSec N k j) (WS_le j hj) (WS_mono h) _).symm

/-- The function `gfun` commutes with restriction from `W(S)` to `W(S')`. -/
lemma gfun_restrict {S S' : Finset (Fin (N + 1))} (hj : j ∈ S) (h : S ⊆ S')
    (s : (Lan N k).val.obj (op (WS N S))) (w : Fin N → ℂ) (hw : w ∈ lDom (sdisc S' j)) :
    gfun N k j (h hj) ((Lan N k).val.map (homOfLE (WS_mono h)).op s) w = gfun N k j hj s w := by
  refine (gfun_apply k j (h hj) _ w hw).trans ?_
  refine Eq.trans ?_ (gfun_apply k j hj _ w (lDom_mono (sdisc_mono j h) hw)).symm
  exact congrArg (fun f => secVal f (ptW j (h hj) w hw) (stdChart N j) (mem_chart_of_WS j (h hj) _))
    (secOf_restrict k j hj h s)

/-- On `U_j ∩ U_{j'}`, the homogeneous coordinates satisfy
`x_m / x_{j'} = (x_j / x_{j'}) (x_m / x_j)`. -/
lemma hcoord_change (j' : Fin (N + 1)) (y : ComplexPoints (sP N))
    (hy : y ∈ chart (sX := sP N) (stdChart N j).U) (hy' : y ∈ chart (sX := sP N) (stdChart N j').U)
    (m : Fin (N + 1)) :
    hcoord N j' ⟨y, hy'⟩ m = hcoord N j' ⟨y, hy'⟩ j * hcoord N j ⟨y, hy⟩ m := by
  let V := Proj.basicOpen (polyGrading ℂ N)
    (MvPolynomial.X j' * MvPolynomial.X j)
  have hyV : y ∈ chart (sX := sP N) V := by
    refine mem_chart_iff.2 ?_
    change y.toScheme ∈ ProjectiveSpectrum.basicOpen _ (MvPolynomial.X j' * MvPolynomial.X j)
    rw [ProjectiveSpectrum.basicOpen_mul]
    exact ⟨mem_chart_iff.1 hy', mem_chart_iff.1 hy⟩
  have e := congrArg (evalHom V ⟨y, hyV⟩) (projectiveSpaceStdCoord_mul (K := ℂ) (n := N) j' m j)
  rwa [map_mul, ← evalHom_res, ← evalHom_res, ← evalHom_res] at e

/-- A degree-zero fraction `q` with `q · u_{j'} = u_j` on `D₊(x_S)` takes the value
`z_j ^ k` at every point `z` with `z_{j'} = 1`. -/
lemma evQ_val_of_smul_tSec {S : Finset (Fin (N + 1))} (j' : Fin (N + 1)) (hj : j ∈ S)
    (hj' : j' ∈ S)
    (q : HomogeneousLocalization.Away (polyGrading ℂ N)
      (chartDenom ℂ N S))
    (a : (AlgebraicGeometry.Proj (polyGrading ℂ N)).ringCatSheaf.obj.obj
      (op (Proj.basicOpen (polyGrading ℂ N) (chartDenom ℂ N S))))
    (hq : (Proj.awayToSection _ (chartDenom ℂ N S)).hom q = a)
    (ha : a • (𝒪ℙ[N, k]).val.map
        (homOfLE (le_stdChart N j' S hj')).op (tSec N k j') =
      (𝒪ℙ[N, k]).val.map
        (homOfLE (le_stdChart N j S hj)).op (tSec N k j))
    (z : Fin (N + 1) → ℂ) (hz : ∀ i ∈ S, z i ≠ 0) (hz1 : z j' = 1) :
    evQ S z hz (HomogeneousLocalization.val q) = z j ^ k := by
  subst hq
  have e2 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul
    (polyGrading ℂ N) (chartDenom_mem_homogeneousSubmodule N S)
    (Finset.card_pos.2 ⟨j, hj⟩) k q
    ((𝒪ℙ[N, k]).val.map
      (homOfLE (le_stdChart N j' S hj')).op (tSec N k j'))
  have e2' := (congrArg (fun y => (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
    (polyGrading ℂ N) (chartDenom_mem_homogeneousSubmodule N S)
    (Finset.card_pos.2 ⟨j, hj⟩) k y :
      LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ))) ha.symm).trans e2
  have e6 := (evQ_laurent_tSec N k j' S hj' z hz).trans
    ((congrArg (· ^ k) hz1).trans (one_zpow k))
  have e5 := evQ_laurent_tSec N k j S hj z hz
  exact ((mul_one _).symm.trans
    (congrArg (evQ S z hz (HomogeneousLocalization.val q) * ·) e6.symm)).trans
    ((map_mul (evQ S z hz) _ _).symm.trans ((congrArg (evQ S z hz) e2'.symm).trans e5))

/-- **Change of trivialization.** On `W(S)`, `u_j = α^#(q) u_{j'}` for a degree-zero fraction `q`
whose value at a point is `(x_j / x_{j'}) ^ k`. -/
lemma exists_uSec_change {S : Finset (Fin (N + 1))} (j' : Fin (N + 1)) (hj : j ∈ S) (hj' : j' ∈ S) :
    ∃ q : HomogeneousLocalization.Away (polyGrading ℂ N)
        (chartDenom ℂ N S),
      (Lan N k).val.map (homOfLE (WS_le j hj)).op (uSec N k j) =
        (show (ringCatSheaf (sP N)).obj.obj (op (WS N S)) from
          sharpHom _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)) •
          (Lan N k).val.map (homOfLE (WS_le j' hj')).op (uSec N k j') ∧
      ∀ (x : WS N S), secVal (sharpHom _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)) x
          (stdChart N j') (mem_chart_of_WS j' hj' x) =
        hcoord N j' ⟨x.1, mem_chart_of_WS j' hj' x⟩ j ^ k := by
  refine ((bijective_smul_tSec N k j'
    (Proj.basicOpen (polyGrading ℂ N) (chartDenom ℂ N S))
    (le_stdChart N j' S hj')).2
    ((𝒪ℙ[N, k]).val.map
      (homOfLE (le_stdChart N j S hj)).op (tSec N k j))).elim fun a ha => ?_
  refine ((bijective_awayToSection (S := S) ⟨j, hj⟩).2 a).elim fun q hq => ?_
  subst hq
  beta_reduce at ha
  refine ⟨q, ?_, fun x => ?_⟩
  · have e1 := unitHom_naturality (sX := sP N)
      (L := 𝒪ℙ[N, k]) (le_stdChart N j S hj) (tSec N k j)
    have e2 := unitHom_naturality (sX := sP N)
      (L := 𝒪ℙ[N, k]) (le_stdChart N j' S hj') (tSec N k j')
    have e3 := unitHom_smul (sX := sP N) (L := 𝒪ℙ[N, k])
      _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)
      ((𝒪ℙ[N, k]).val.map
        (homOfLE (le_stdChart N j' S hj')).op (tSec N k j'))
    refine e1.symm.trans ((congrArg (unitHom (sX := sP N)
      (L := 𝒪ℙ[N, k]) _) ha).symm.trans (e3.trans ?_))
    congr 1
  · exact (secVal_sharpHom_awayToSection N j' S hj' x (mem_chart_of_WS j' hj' x) q).trans
      (evQ_val_of_smul_tSec k j j' hj hj' q _ rfl ha _ _ (hcoord_self N j' _))

/-- For `z j ≠ 0`, the coordinates of `insertOne j (dehom j z)` are `z m / z j`. -/
lemma insertOne_dehom {z : Fin (N + 1) → ℂ} (hzj : z j ≠ 0) (m : Fin (N + 1)) :
    insertOne j (dehom j z) m = z m / z j := by
  rcases Fin.eq_self_or_eq_succAbove j m with rfl | ⟨i, rfl⟩
  · simp [insertOne, div_self hzj]
  · simp [insertOne, dehom]

/-- The homogeneous coordinates in the chart `U_{j'}` of the point of `W(S)` with homogeneous
coordinates `z` are `z m / z j'`. -/
lemma hcoord_ptW_change {S : Finset (Fin (N + 1))} (j' : Fin (N + 1)) (hj : j ∈ S) (hj' : j' ∈ S)
    {z : Fin (N + 1) → ℂ} (hz : ∀ i ∈ S, z i ≠ 0) (m : Fin (N + 1)) :
    hcoord N j' ⟨(ptW j hj (dehom j z) (dehom_mem hj hz)).1, mem_chart_of_WS j' hj' _⟩ m =
      z m / z j' := by
  set y := ptW j hj (dehom j z) (dehom_mem hj hz)
  have hH : ∀ m, hcoord N j ⟨y.1, mem_chart_of_WS j hj _⟩ m = z m / z j := fun m => by
    rw [hcoord_ptW]; exact insertOne_dehom j (hz j hj) m
  have hc := fun m => hcoord_change j j' y.1 (mem_chart_of_WS j hj y) (mem_chart_of_WS j' hj' y) m
  have hlam : hcoord N j' ⟨y.1, mem_chart_of_WS j' hj' y⟩ j = z j / z j' := by
    have h1 := hc j'
    rw [hcoord_self, hH] at h1
    have hzj := hz j hj
    have hzj' := hz j' hj'
    field_simp at h1
    rw [eq_div_iff hzj']
    exact h1.symm
  rw [hc m, hlam, hH]
  have hzj := hz j hj
  field_simp

/-- The points of `W(S)` with homogeneous coordinates `z`, built in the charts `U_j` and `U_{j'}`,
coincide. -/
lemma ptW_change {S : Finset (Fin (N + 1))} (j' : Fin (N + 1)) (hj : j ∈ S) (hj' : j' ∈ S)
    {z : Fin (N + 1) → ℂ} (hz : ∀ i ∈ S, z i ≠ 0) :
    ptW j' hj' (dehom j' z) (dehom_mem hj' hz) = ptW j hj (dehom j z) (dehom_mem hj hz) := by
  set y := ptW j hj (dehom j z) (dehom_mem hj hz)
  have : (coordsEquiv j').symm (dehom j' z) = ⟨y.1, mem_chart_of_WS j' hj' y⟩ := by
    rw [Equiv.symm_apply_eq]
    funext i
    change dehom j' z i = (stdChart N j').coords ⟨y.1, mem_chart_of_WS j' hj' y⟩ i
    rw [← hcoord_succAbove, hcoord_ptW_change j j' hj hj' hz]
    rfl
  exact Subtype.ext (congrArg (fun p : chart (sX := sP N) (stdChart N j').U => p.1) this)

/-- **Chart independence of the homogeneous function of a section.** -/
lemma gfun_change {S : Finset (Fin (N + 1))} (j' : Fin (N + 1)) (hj : j ∈ S) (hj' : j' ∈ S)
    (s : (Lan N k).val.obj (op (WS N S))) {z : Fin (N + 1) → ℂ} (hz : ∀ i ∈ S, z i ≠ 0) :
    z j ^ k * gfun N k j hj s (dehom j z) = z j' ^ k * gfun N k j' hj' s (dehom j' z) := by
  obtain ⟨q, hu, hval⟩ := exists_uSec_change (k := k) j j' hj hj'
  have hsec : secOf N k j' (WS N S) (WS_le j' hj') s =
      secOf N k j (WS N S) (WS_le j hj) s *
        (show (ringCatSheaf (sP N)).obj.obj (op (WS N S)) from
          sharpHom _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)) := by
    refine secOf_eq N k j' _ _ s _ ?_
    rw [mul_smul]
    rw [← hu]
    exact secOf_smul N k j _ _ s
  let y := ptW j hj (dehom j z) (dehom_mem hj hz)
  have hpt := ptW_change j j' hj hj' hz
  have hlam : hcoord N j' ⟨y.1, mem_chart_of_WS j' hj' y⟩ j = z j / z j' :=
    hcoord_ptW_change j j' hj hj' hz j
  have h1 : gfun N k j hj s (dehom j z) =
      secVal (secOf N k j (WS N S) (WS_le j hj) s) y (stdChart N j) (mem_chart_of_WS j hj y) :=
    gfun_apply k j hj s _ _
  have h2 : gfun N k j' hj' s (dehom j' z) =
      secVal (secOf N k j (WS N S) (WS_le j hj) s) y (stdChart N j) (mem_chart_of_WS j hj y) *
        (z j / z j') ^ k := by
    refine (gfun_apply k j' hj' s _ (dehom_mem hj' hz)).trans ?_
    have hpt' : secVal (secOf N k j' (WS N S) (WS_le j' hj') s)
        (ptW j' hj' (dehom j' z) (dehom_mem hj' hz)) (stdChart N j') (mem_chart_of_WS j' hj' _) =
        secVal (secOf N k j' (WS N S) (WS_le j' hj') s) y (stdChart N j')
          (mem_chart_of_WS j' hj' y) := by
      rw [hpt]
    refine hpt'.trans ?_
    refine (congrArg (fun f => secVal f y (stdChart N j') (mem_chart_of_WS j' hj' y)) hsec).trans ?_
    refine (secVal_mul (secOf N k j (WS N S) (WS_le j hj) s)
      (sharpHom _ ((Proj.awayToSection _ (chartDenom ℂ N S)).hom q)) y (stdChart N j')
      (mem_chart_of_WS j' hj' y)).trans ?_
    rw [← hlam]
    exact congrArg₂ (· * ·) (secVal_indep _ y (stdChart N j') (stdChart N j) _ _) (hval y)
  rw [h1, h2, div_zpow]
  have hzj' := zpow_ne_zero k (hz j' hj')
  field_simp

end GeoModel

end AnalyticModel

end MMP.Analytic.ProjectiveTwists
