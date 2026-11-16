module

public import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.PointBlowupCharts

/-!
# One blow-up of a point of a curve on a regular surface

Let `S` be a Noetherian scheme, `p ∈ S` a closed point with `R = 𝒪_{S,p}` regular of dimension
two, `C ⊆ S` an effective Cartier divisor with local equation `f ∈ R` and multiplicity
`m = mult_p C ≥ 1`, `π : B_pS → S` the blow-up of `p`, `E` its exceptional curve and `C₁` the
birational transform of `C`. The points of `C₁ ∩ E` have residue degrees `d_q` with
`∑ d_q · mult_q C₁ ≤ m`.

*Multiplicity drops unless the leading term is a power of a linear form* (Kollár 1.66). If a
point `q ∈ C₁ ∩ E` has `mult_q C₁ = m`, the inequality forces `d_q = 1` and
`C₁ ∩ E = {q}`, and there is a regular system of parameters `(x, y)` of `R` in which `f` is in
normal form and `q` is the point `(x, y/x)` of the chart `Spec R[y/x]`.

*Uniqueness of a point of the same multiplicity* (Kollár, proof of 1.67). If `m ≥ 2` and some
`q ∈ C₁ ∩ E` has `mult_q C₁ = m`, then `q` is the only point of `C₁` over `p`, and it is
singular; otherwise every point of `C₁` over `p` has multiplicity `< m`.

*The previous exceptional curve is not tangent* (Kollár, proof of 1.69). Along a blow-up
sequence `(p_i ∈ C_i ⊆ S_i)` of constant multiplicity `m ≥ 2` of a reduced curve on a
two-dimensional regular Noetherian scheme, every `𝒪_{S_j,p_j}` is regular of dimension two and
every `C_j` has principal stalks, so the results above apply at each step: `κ(p_i) → κ(p_{i+1})`
is bijective, `𝒪_{S_{i+1},p_{i+1}} / (I_{C_{i+1}} + I_E)` has length `m`, and the leading form
of a local equation of `E` does not divide the leading term of a local equation of `C_{i+1}`:
otherwise `f ≡ e h` modulo `𝔪^{m+1}` and the length would be at least `m + 1`.

## Main results

* `MMP.Resolution.exists_isInNormalForm_of_multAt_birationalTransform_eq`: a point of `C₁ ∩ E`
  of multiplicity `m` is rational, is the only point of `C₁ ∩ E`, and is the point `(x, y/x)` for
  a regular system of parameters in which `f` is in normal form.
* `MMP.Resolution.birationalTransform_fibre_eq_singleton_or_multAt_lt`: a point of the same
  multiplicity is the only point of `C₁` over `p`; otherwise the multiplicity drops everywhere.
* `MMP.Resolution.PointBlowupSequence.not_dvd_isLeadingTerm_of_isConstantMultiplicity`: the
  previous exceptional curve is not tangent to a transform of constant multiplicity.

## Implementation notes

The rationality of `q` is the bijectivity of the residue field map `κ(p) → κ(q)` of `π`. The
intersection `C₁ ∩ E` is the support of the sum of the ideal sheaves of `C₁` and `E`. That `q`
is the point `(x, y/x)` of the chart `Spec R[y/x]` is expressed in the local ring `𝒪_{B_pS,q}`:
`π(q) = p`, and the image of `y` is the image of `x` times an element `t` of the maximal ideal
of `𝒪_{B_pS,q}`. In the blow-up sequence, the index `k ≥ 1` is written `k = i + 1`, and the
exceptional curve `E_{i+1}` is the exceptional ideal of the blow-up of `p_i`, transported to
`S_{i+1}` along `blowupIso`. The linear form of `E_{i+1}` and the leading term of `C_{i+1}` are
taken with respect to an arbitrary regular system of parameters and arbitrary local equations
(`MMP.Resolution.IsLeadingTerm`), so that no choice is made.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 1.40, 1.66, proofs of 1.67
  and 1.69.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing MMP.Resolution.Kr1c

namespace MMP.Resolution

/-! ### Binary forms whose dehomogenisation is a power of a linear form -/

section Forms

open Polynomial

variable {κ : Type*} [Field κ]

private theorem aeval_eq_sum (F : MvPolynomial (Fin 2) κ) (v : Fin 2 → κ[X]) :
    MvPolynomial.aeval v F =
      ∑ d ∈ F.support, C (F.coeff d) * (v 0 ^ d 0 * v 1 ^ d 1) := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_two]
  rfl

/-- A form of degree `m` has `deg F(1, Y) ≤ m`. -/
private theorem natDegree_aeval_one_X_le {F : MvPolynomial (Fin 2) κ} {m : ℕ}
    (hF : F.IsHomogeneous m) :
    (MvPolynomial.aeval ![(1 : κ[X]), Polynomial.X] F).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [aeval_eq_sum, finset_sum_coeff]
  refine Finset.sum_eq_zero fun d hd => ?_
  have h := add_eq_of_mem_support hF hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow,
    one_mul, coeff_C_mul_X_pow]
  rw [if_neg (by omega)]

/-- A nonzero form `F` of degree `m` has `F(1, Y) ≠ 0`. -/
private theorem aeval_one_X_ne_zero {K : Type*} [CommRing K] {F : MvPolynomial (Fin 2) K}
    {m : ℕ} (hF : F.IsHomogeneous m) (h0 : F ≠ 0) :
    MvPolynomial.aeval (![1, Polynomial.X] : Fin 2 → K[X]) F ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h0
  intro h
  apply hd
  have hprod : ∀ v : Fin 2 →₀ ℕ,
      (v.prod fun i k => (![1, Polynomial.X] : Fin 2 → K[X]) i ^ k) = Polynomial.X ^ (v 1) := by
    intro v
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [F.as_sum, map_sum] at h
  simp only [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, hprod] at h
  have h2 := congrArg (fun P : K[X] => P.coeff (d 1)) h
  simp only [finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at h2
  rw [Finset.sum_eq_single d] at h2
  · simpa using h2
  · intro v hv hvd
    rw [if_neg]
    intro h1
    apply hvd
    have hv' := add_eq_of_mem_support hF hv
    have hd' := add_eq_of_mem_support hF (MvPolynomial.mem_support_iff.mpr hd)
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      omega
    · simpa using h1.symm
  · intro hdn
    exact absurd (MvPolynomial.notMem_support_iff.mp hdn) hd

/-- A form of degree `m` is determined by its dehomogenisation `F(1, Y)`: if
`F(1, Y) = a (Y - c)^m` then `F = a (Y - c X)^m`. -/
private theorem eq_C_mul_X_sub_C_mul_X_pow {F : MvPolynomial (Fin 2) κ} {m : ℕ}
    (hF : F.IsHomogeneous m) {a c : κ}
    (h : MvPolynomial.aeval ![(1 : κ[X]), Polynomial.X] F = C a * (Polynomial.X - C c) ^ m) :
    F = MvPolynomial.C a * (MvPolynomial.X 1 - MvPolynomial.C c * MvPolynomial.X 0) ^ m := by
  have hG : (MvPolynomial.C a * (MvPolynomial.X 1 - MvPolynomial.C c * MvPolynomial.X 0) ^ m :
      MvPolynomial (Fin 2) κ).IsHomogeneous m := by
    have h1 : (MvPolynomial.X 1 - MvPolynomial.C c * MvPolynomial.X 0 :
        MvPolynomial (Fin 2) κ).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X κ 1).sub (MvPolynomial.isHomogeneous_C_mul_X c 0)
    simpa using (MvPolynomial.isHomogeneous_C (Fin 2) a).mul (h1.pow m)
  by_contra hne
  refine aeval_one_X_ne_zero (hF.sub hG) (sub_ne_zero.mpr hne) ?_
  rw [map_sub, h]
  simp [Polynomial.algebraMap_eq]

/-- **A polynomial of degree at most `m` lying in the `m`-th symbolic power of a prime of
`κ[Y]`** is `a (Y - c)^m` with `a ≠ 0`, and `Y - c` lies in the prime. -/
private theorem exists_eq_C_mul_X_sub_C_pow {Q : Ideal κ[X]} [hQ : Q.IsPrime] {P s : κ[X]}
    {m : ℕ} (hm : 1 ≤ m) (hP : P ≠ 0) (hdeg : P.natDegree ≤ m) (hs : s ∉ Q)
    (hsP : s * P ∈ Q ^ m) :
    ∃ a c : κ, a ≠ 0 ∧ P = C a * (Polynomial.X - C c) ^ m ∧ Polynomial.X - C c ∈ Q := by
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal Q).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.mpr rfl] at hπ
    subst hπ
    rw [Ideal.bot_pow (by omega), Ideal.mem_bot] at hsP
    rcases mul_eq_zero.mp hsP with h | h
    · exact hs (h ▸ Ideal.zero_mem _)
    · exact hP h
  have hprime : Prime π := by
    rw [← Ideal.span_singleton_prime hπ0]
    rwa [hπ] at hQ
  have hsπ : ¬ π ∣ s := fun h => hs (hπ ▸ Ideal.mem_span_singleton.mpr h)
  have hdvd : π ^ m ∣ s * P := by
    rw [hπ, Ideal.span_singleton_pow] at hsP
    exact Ideal.mem_span_singleton.mp hsP
  obtain ⟨g, hg⟩ := hprime.pow_dvd_of_dvd_mul_left m hsπ hdvd
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hP (by simpa using hg)
  have hdegP : P.natDegree = m * π.natDegree + g.natDegree := by
    rw [hg, natDegree_mul (pow_ne_zero _ hπ0) hg0, natDegree_pow]
  have hπ1 : 1 ≤ π.natDegree := by
    by_contra h0
    have h0 : π.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero h0] at hprime
    exact hprime.not_unit (isUnit_C.mpr (IsUnit.mk0 _ (by
      intro h; apply hπ0; rw [eq_C_of_natDegree_eq_zero h0, h, C_0])))
  have hπ1' : π.natDegree = 1 := by
    have : m * π.natDegree ≤ m * 1 := by omega
    have := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  have hg0' : g.natDegree = 0 := by
    have : m * 1 ≤ m * π.natDegree := Nat.mul_le_mul_left _ hπ1
    omega
  set u := π.coeff 1
  set v := π.coeff 0
  have hu : u ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hπ0
    rwa [leadingCoeff, hπ1'] at this
  have hπeq : π = C u * (Polynomial.X - C (-v / u)) := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hπ1'.le]
    rw [mul_sub, ← C_mul, mul_div_cancel₀ _ hu]
    simp [sub_eq_add_neg, u, v]
  set g₀ := g.coeff 0
  have hgC : g = C g₀ := eq_C_of_natDegree_eq_zero hg0'
  refine ⟨u ^ m * g₀, -v / u, mul_ne_zero (pow_ne_zero _ hu) ?_, ?_, ?_⟩
  · exact fun h => hg0 (by rw [hgC, h, C_0])
  · rw [hg, hgC, hπeq, mul_pow, C_mul, ← C_pow]
    ring
  · have : Polynomial.X - C (-v / u) = C u⁻¹ * π := by
      rw [hπeq, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hu, C_1, one_mul]
    rw [this, hπ]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self π)

end Forms

/-! ### Normal forms from a leading term that is a power of a linear form -/

section NormalForm

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- If the leading term of `f` with respect to `(x, y)` is `a (Y - c X)^m` and `r` lifts `c`,
then `f` is in normal form with respect to `(x, y - r x)`. -/
private theorem isInNormalForm_sub_mul_of_isLeadingTerm {x y f : R}
    (hxy : maximalIdeal R = Ideal.span {x, y}) {m : ℕ} (hm : mult f = m)
    {F : MvPolynomial (Fin 2) (ResidueField R)} (hF : IsLeadingTerm x y f F)
    {a c : ResidueField R}
    (hFac : F = MvPolynomial.C a * (MvPolynomial.X 1 - MvPolynomial.C c * MvPolynomial.X 0) ^ m)
    (r : R) (hr : residue R r = c) :
    IsInNormalForm x (y - r * x) f := by
  have hx : x ∈ maximalIdeal R := hxy ▸ Ideal.subset_span (by simp)
  have hy : y ∈ maximalIdeal R := hxy ▸ Ideal.subset_span (by simp)
  have hspan : Ideal.span {x, y - r * x} = maximalIdeal R := by
    rw [hxy]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro z (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · exact Ideal.sub_mem _ (Ideal.subset_span (by simp))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rintro z (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [show z = (z - r * x) + r * x by ring]
        exact Ideal.add_mem _ (Ideal.subset_span (by simp))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  have hm' : (m : ℕ∞) = idealOrder (Ideal.span {f}) := hm.symm
  have hfm : f ∈ maximalIdeal R ^ m :=
    (Ideal.span_singleton_le_iff_mem _).mp (le_pow_of_le_idealOrder hm'.le)
  have hfm1 : f ∉ maximalIdeal R ^ (m + 1) := by
    intro h
    have : ((m + 1 : ℕ) : ℕ∞) ≤ idealOrder (Ideal.span {f}) :=
      le_iSup₂_of_le (m + 1) ((Ideal.span_singleton_le_iff_mem _).mpr h) le_rfl
    rw [← hm'] at this
    exact absurd (by exact_mod_cast this : m + 1 ≤ m) (by omega)
  refine ⟨hspan, m, hfm, hfm1, ?_⟩
  obtain ⟨m', hm'', -, G, hG, hGF, hfG⟩ := hF
  have hmm : m' = m := by exact_mod_cast hm''.symm.trans hm
  subst hmm
  obtain ⟨b, rfl⟩ := residue_surjective a
  set G' : MvPolynomial (Fin 2) R :=
    MvPolynomial.C b * (MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0) ^ m' with hG'
  have hG'h : G'.IsHomogeneous m' := by
    have h1 : (MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0 :
        MvPolynomial (Fin 2) R).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X R 1).sub (MvPolynomial.isHomogeneous_C_mul_X r 0)
    simpa using (MvPolynomial.isHomogeneous_C (Fin 2) b).mul (h1.pow m')
  have hmap : MvPolynomial.map (residue R) (G - G') = 0 := by
    rw [map_sub, hGF, hFac, hG']
    simp [hr]
  have hD := eval_mem_pow_succ_of_map_eq_zero hx hy (hG.sub hG'h) hmap
  have hev : MvPolynomial.eval ![x, y] G' = b * (y - r * x) ^ m' := by
    simp [hG']
  have hdecomp : f = b * (y - r * x) ^ m' +
      ((f - MvPolynomial.eval ![x, y] G) + MvPolynomial.eval ![x, y] (G - G')) := by
    rw [map_sub, hev]; ring
  rw [hdecomp]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _
    (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_right (Ideal.add_mem _ hfG hD))

/-- Being in normal form is invariant under multiplication by a unit. -/
private theorem IsInNormalForm.of_associated {x y f g : R} (h : IsInNormalForm x y f)
    (hfg : Associated f g) : IsInNormalForm x y g := by
  obtain ⟨hs, m, h1, h2, h3⟩ := h
  obtain ⟨u, rfl⟩ := hfg
  refine ⟨hs, m, Ideal.mul_mem_right _ _ h1, fun h => h2 ?_, Ideal.mul_mem_right _ _ h3⟩
  simpa using Ideal.mul_mem_right (↑u⁻¹ : R) _ h

end NormalForm

/-! ### Clearing denominators in a localization at a prime -/

/-- If the image of `b` in the localization `A = B_𝔮` lies in `𝔪_A^m`, then `s b ∈ 𝔮^m` for some
`s ∉ 𝔮`. -/
private theorem exists_mul_mem_pow_of_algebraMap_mem {B A : Type*} [CommRing B] [CommRing A]
    [IsLocalRing A] [Algebra B A] (Q : Ideal B) [Q.IsPrime] [IsLocalization.AtPrime A Q]
    {b : B} {m : ℕ}
    (hb : algebraMap B A b ∈ maximalIdeal A ^ m) :
    ∃ s ∉ Q, s * b ∈ Q ^ m := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q A, ← Ideal.map_pow] at hb
  obtain ⟨⟨a, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl A).mp hb
  simp only at h
  rw [← map_mul] at h
  obtain ⟨⟨t, ht⟩, h⟩ := (IsLocalization.eq_iff_exists Q.primeCompl A).mp h
  refine ⟨t * s, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim ht hs, ?_⟩
  simp only at h
  rw [show t * s * b = t * (b * s) by ring, h]
  exact Ideal.mul_mem_left _ _ a.2

/-! ### Coordinate neighbourhoods and the charts of the blow-up -/

/-- The evaluation at a closed point of an affine open is surjective. -/
private theorem evaluation_surjective {S : Scheme.{u}} {p : S} (hp : IsClosed ({p} : Set S))
    {U : S.Opens} (hU : IsAffineOpen U) (hpU : p ∈ U) :
    Function.Surjective (S.evaluation U p hpU).hom := by
  let := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨p, hpU⟩ : U)
  have := hU.isLocalization_stalk ⟨p, hpU⟩
  have := hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hpU⟩ hp
  intro k
  obtain ⟨r', hr⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal
    (hU.primeIdealOf ⟨p, hpU⟩).asIdeal (S.presheaf.stalk p)).surjective k
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
  refine ⟨r, ?_⟩
  rw [← hr]
  rfl

/-! ### Residue degrees and the sum of multiplicities -/

section Degrees

/-- A field extension of rank at most one is an isomorphism. -/
private theorem bijective_of_toENat_rank_le_one {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (h : (letI := φ.toAlgebra; (Module.rank K L).toENat) ≤ 1) : Function.Bijective φ := by
  letI := φ.toAlgebra
  have hr : Module.rank K L = 1 := by simpa using le_antisymm h (one_le_toENat_rank φ)
  exact ⟨φ.injective, fun l =>
    Algebra.mem_bot.mp (Subalgebra.bot_eq_top_of_rank_eq_one hr ▸ Algebra.mem_top)⟩

/-- If a finite sum of terms `≥ 1` is at most a finite `n`, and one term `f q` is already `≥ n`,
then `q` is the only index. -/
private theorem eq_of_le_of_sum_le {ι : Type*} {s : Finset ι} {f : ι → ℕ∞} {n : ℕ}
    (hf : ∀ i ∈ s, 1 ≤ f i) {q : ι} (hq : q ∈ s) (hfq : n ≤ f q) (hsum : ∑ i ∈ s, f i ≤ n) :
    ∀ i ∈ s, i = q := by
  intro i hi
  by_contra hne
  have h := (add_le_add hfq (hf i hi)).trans
    ((Finset.add_le_sum (fun _ _ => zero_le) hq hi (Ne.symm hne)).trans hsum)
  exact lt_irrefl _ ((ENat.add_one_le_iff (ENat.coe_ne_top n)).mp h)

/-- If `∑_{i ∈ s} d_i μ_i ≤ m` with all `d_i ≥ 1`, `μ_i ≥ 1` and `μ_q = m ≥ 1` for some `q ∈ s`,
then `d_q ≤ 1` and `s = {q}`. -/
private theorem le_one_and_eq_of_sum_mul_le {ι : Type*} {s : Finset ι}
    {d μ : ι → ℕ∞} {m : ℕ} (hm1 : 1 ≤ m) (hd : ∀ i, 1 ≤ d i) (hμ : ∀ i ∈ s, 1 ≤ μ i) {q : ι}
    (hq : q ∈ s) (hμq : μ q = m) (hsum : ∑ i ∈ s, d i * μ i ≤ m) :
    d q ≤ 1 ∧ ∀ i ∈ s, i = q := by
  refine ⟨?_, fun i hi => ?_⟩
  · have h1 : d q * μ q ≤ m :=
      (Finset.single_le_sum (f := fun i => d i * μ i) (fun i _ => zero_le) hq).trans hsum
    by_contra h2
    have h3 : (2 : ℕ∞) ≤ d q := by
      simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp h2)
    have h4 : ((2 * m : ℕ) : ℕ∞) ≤ m := by
      rw [Nat.cast_mul]
      exact (mul_le_mul' h3 hμq.ge).trans h1
    have := Nat.cast_le.mp h4
    omega
  · exact eq_of_le_of_sum_le (fun i hi => (hμ i hi).trans (le_mul_of_one_le_left' (hd i))) hq
      (by rw [← hμq]; exact le_mul_of_one_le_left' (hd q)) hsum i hi

end Degrees

/-! ### The point of the chart -/

section ChartPoint

/-- **The local computation on a chart `j : Spec B ⟶ B_pS`.** Suppose `j` is an open immersion
over `S` through `Spec(R → B)`, `z ∈ B` solves `x z = y`, `κ(p)[Y] ≃ B/xB` sends constants to
residues and `Y` to `z`, the exceptional curve and the birational transform are cut out on
`Spec B` by `x` and by `f₁` with `f₁ ≡ F(1, Y)` modulo `x`. If `mult_{j w} C₁ = m`, then for some
`r ∈ R`, `f` is in normal form with respect to `(x, y - r x)` and `π^*(y - r x) = π^* x · t`
with `t ∈ 𝔪_{j w}`. -/
private theorem exists_isInNormalForm_of_isOpenImmersion {S : Scheme.{u}} {p : S}
    (hp : IsClosed ({p} : Set S)) (C : S.IdealSheafData) (c : CoordinateNeighbourhood S p)
    (f : Γ(S, c.U)) (m : ℕ) (hm : mult ((S.presheaf.germ c.U p c.mem).hom f) = m) (hm1 : 1 ≤ m)
    (hmax : maximalIdeal (S.presheaf.stalk p) =
      Ideal.span {(S.presheaf.germ c.U p c.mem).hom c.x, (S.presheaf.germ c.U p c.mem).hom c.y})
    (F : MvPolynomial (Fin 2) (S.residueField p))
    (hF : IsLeadingTerm ((S.presheaf.germ c.U p c.mem).hom c.x)
      ((S.presheaf.germ c.U p c.mem).hom c.y) ((S.presheaf.germ c.U p c.mem).hom f) F)
    (hFm : F.IsHomogeneous m) (hFne : F ≠ 0)
    {B : Type u} [CommRing B] [Algebra Γ(S, c.U) B]
    (j : Spec (.of B) ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    [IsOpenImmersion j]
    (hjπ : j ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, c.U) B)) ≫ c.isAffineOpen.fromSpec)
    (z : B) (hz : algebraMap Γ(S, c.U) B c.x * z = algebraMap Γ(S, c.U) B c.y)
    (φ : Polynomial (S.residueField p) ≃+* B ⧸ Ideal.span {algebraMap Γ(S, c.U) B c.x})
    (hφC : ∀ r, φ (Polynomial.C ((S.evaluation c.U p c.mem).hom r)) =
      Ideal.Quotient.mk _ (algebraMap Γ(S, c.U) B r))
    (hφX : φ Polynomial.X = Ideal.Quotient.mk _ z)
    (f₁ : B) (hP : φ (MvPolynomial.aeval ![1, Polynomial.X] F) = Ideal.Quotient.mk _ f₁)
    (hE : (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).comap j =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {algebraMap Γ(S, c.U) B c.x})))).ker)
    (h₁ : (birationalTransform p hp C).comap j =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f₁})))).ker)
    (w : Spec (.of B))
    (hqE : j w ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support)
    (hmq : multAt (birationalTransform p hp C) (j w) = m)
    (hqp : (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base (j w) = p) :
    ∃ x y : S.presheaf.stalk p, IsInNormalForm x y ((S.presheaf.germ c.U p c.mem).hom f) ∧
      ∃ t ∈ maximalIdeal
          ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk (j w)),
        ((S.presheaf.stalkCongr (Inseparable.of_eq hqp)).inv ≫
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).stalkMap (j w)).hom
            y =
          ((S.presheaf.stalkCongr (Inseparable.of_eq hqp)).inv ≫
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).stalkMap (j w)).hom
            x * t := by
  haveI hwp : (w.asIdeal : Ideal B).IsPrime := w.isPrime
  letI : Algebra B ((Spec (.of B)).presheaf.stalk w) := StructureSheaf.stalkAlgebra (R := B) w
  haveI : IsLocalization.AtPrime ((Spec (.of B)).presheaf.stalk w) w.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B w
  -- the image of `f₁` in `𝒪_{Spec B, w}` lies in `𝔪^m`
  have hstalk : IdealSheafData.stalk (birationalTransform p hp C) (j w) ≤
      maximalIdeal _ ^ m :=
    (natCast_le_idealOrder_iff' _ m).mp hmq.ge
  have hmapmax : Ideal.map (j.stalkMap w).hom (maximalIdeal
      ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk (j w))) ≤
      maximalIdeal ((Spec (.of B)).presheaf.stalk w) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _ |>.mp ha) (isUnit_of_map_unit _ a hu)
  have hf₁mem : algebraMap B ((Spec (.of B)).presheaf.stalk w) f₁ ∈
      maximalIdeal ((Spec (.of B)).presheaf.stalk w) ^ m := by
    have h2 := MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map j
      (birationalTransform p hp C) w
    rw [h₁] at h2
    have h3 : algebraMap B ((Spec (.of B)).presheaf.stalk w) f₁ ∈ IdealSheafData.stalk
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f₁})))).ker w := by
      rw [IdealSheafData.stalk_eq_map_germ _ w ⟨⊤, isAffineOpen_top _⟩ trivial,
        ideal_ker_specMap_top]
      refine Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ?_)
      rw [Ideal.mk_ker]
      exact Ideal.mem_span_singleton_self _
    rw [h2] at h3
    refine (Ideal.map_mono hstalk).trans ?_ h3
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hmapmax m
  -- `x` vanishes at `w`
  have hxw : algebraMap Γ(S, c.U) B c.x ∈ w.asIdeal := by
    have h1 : w ∈ ((exceptionalIdeal
        (Scheme.IdealSheafData.vanishingIdeal ⟨({p} : Set S), hp⟩)).comap j).support := by
      rwa [Scheme.IdealSheafData.support_comap]
    rw [hE, Scheme.IdealSheafData.mem_support_iff] at h1
    have h2 := h1 ⟨⊤, isAffineOpen_top _⟩
    rw [ideal_ker_specMap_top, Ideal.mk_ker, Scheme.mem_zeroLocus_iff] at h2
    have h3 := h2 ((Scheme.ΓSpecIso (.of B)).inv.hom (algebraMap Γ(S, c.U) B c.x))
      (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
    rw [basicOpen_eq_of_affine] at h3
    by_contra hn
    exact h3 hn
  -- clearing denominators: `s f₁ ∈ 𝔮^m` for some `s ∉ 𝔮`
  obtain ⟨s, hs, hsf⟩ := exists_mul_mem_pow_of_algebraMap_mem (B := B) w.asIdeal hf₁mem
  -- the prime of `κ[Y]` below `w`
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {algebraMap Γ(S, c.U) B c.x})) ≤
      w.asIdeal := by
    rwa [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
  set J := w.asIdeal.map (Ideal.Quotient.mk (Ideal.span {algebraMap Γ(S, c.U) B c.x})) with hJdef
  haveI hJ : J.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hmemJ : ∀ b : B, Ideal.Quotient.mk _ b ∈ J ↔ b ∈ w.asIdeal := fun b => by
    rw [← Ideal.mem_comap, hJdef, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      sup_eq_left.mpr hker]
  set Qκ := J.comap φ.toRingHom with hQκ
  have hsQ : φ.symm (Ideal.Quotient.mk _ s) ∉ Qκ := by
    rw [hQκ, Ideal.mem_comap]
    change φ (φ.symm _) ∉ J
    rwa [RingEquiv.apply_symm_apply, hmemJ]
  have hsPQ :
      φ.symm (Ideal.Quotient.mk _ s) * MvPolynomial.aeval ![1, Polynomial.X] F ∈ Qκ ^ m := by
    have hsP : φ.symm (Ideal.Quotient.mk _ s) * MvPolynomial.aeval ![1, Polynomial.X] F =
        φ.symm (Ideal.Quotient.mk _ (s * f₁)) := by
      rw [map_mul, map_mul, ← hP, RingEquiv.symm_apply_apply]
    have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap Γ(S, c.U) B c.x}) (s * f₁) ∈ J ^ m := by
      rw [hJdef, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hsf
    have h2 : Qκ = J.map φ.symm := by
      rw [hQκ, Ideal.map_symm]; rfl
    rw [hsP, h2, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h1
  obtain ⟨a, c₀, ha, hPa, hXc⟩ := exists_eq_C_mul_X_sub_C_pow hm1 (aeval_one_X_ne_zero hFm hFne)
    (natDegree_aeval_one_X_le hFm) hsQ hsPQ
  have hFac := eq_C_mul_X_sub_C_mul_X_pow hFm hPa
  obtain ⟨r, hr⟩ := evaluation_surjective hp c.isAffineOpen c.mem c₀
  have hzr : z - algebraMap Γ(S, c.U) B r ∈ w.asIdeal := by
    rw [← hmemJ, map_sub, ← hφX, ← hφC, hr, ← map_sub]
    exact hXc
  have hNF := isInNormalForm_sub_mul_of_isLeadingTerm hmax hm hF hFac
    ((S.presheaf.germ c.U p c.mem).hom r) (by rw [← hr]; rfl)
  -- germs of sections of `R`, pulled back to `B_pS` and read on `Spec B`
  have hle : ⊤ ≤ (j ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      ⟨({p} : Set S), hp⟩)) ⁻¹ᵁ c.U := by
    intro w' _
    show (j ≫ _) w' ∈ c.U
    rw [hjπ, Scheme.Hom.comp_apply]
    exact c.isAffineOpen.range_fromSpec.subset ⟨_, rfl⟩
  have happLE := Stacks.Blowup.appLE_top_of_eq_specMap_fromSpec
    (⟨c.U, c.isAffineOpen⟩ : S.affineOpens) (CommRingCat.ofHom (algebraMap Γ(S, c.U) B)) hjπ hle
  have hcompat : ∀ s' : Γ(S, c.U), (j.stalkMap w).hom
      (((S.presheaf.stalkCongr (Inseparable.of_eq hqp)).inv ≫
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨({p} : Set S), hp⟩)).stalkMap
          (j w)).hom ((S.presheaf.germ c.U p c.mem).hom s')) =
      algebraMap B _ (algebraMap Γ(S, c.U) B s') := by
    intro s'
    rw [CommRingCat.comp_apply, stalkCongr_inv_germ hqp c.U c.mem s']
    have h1 := germ_appLE (j ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      ⟨({p} : Set S), hp⟩)) hle (trivial : w ∈ ⊤) s'
    rw [happLE, Scheme.Hom.stalkMap_comp, CommRingCat.comp_apply] at h1
    exact h1.symm
  haveI : IsIso (j.stalkMap w) := IsOpenImmersion.instIsIsoCommRingCatStalkMap j w
  have hσinj : Function.Injective (j.stalkMap w).hom :=
    (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.injective
  have hinv : ∀ a, (j.stalkMap w).hom ((inv (j.stalkMap w)).hom a) = a := fun a => by
    rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  refine ⟨_, _, hNF, (inv (j.stalkMap w)).hom (algebraMap B _ (z - algebraMap Γ(S, c.U) B r)),
    ?_, ?_⟩
  · have hm' : algebraMap B ((Spec (.of B)).presheaf.stalk w) (z - algebraMap Γ(S, c.U) B r) ∈
        maximalIdeal _ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ w.asIdeal _).mpr hzr
    rw [mem_maximalIdeal, mem_nonunits_iff] at hm' ⊢
    intro hu
    have h := hu.map (j.stalkMap w).hom
    rw [hinv] at h
    exact hm' h
  · apply hσinj
    have hy' : (S.presheaf.germ c.U p c.mem).hom c.y -
        (S.presheaf.germ c.U p c.mem).hom r * (S.presheaf.germ c.U p c.mem).hom c.x =
        (S.presheaf.germ c.U p c.mem).hom (c.y - r * c.x) := by
      rw [map_sub, map_mul]
    rw [hy', map_mul, hcompat, hcompat, hinv, ← map_mul]
    congr 1
    rw [map_sub, map_mul, ← hz]
    ring

/-- **The chart computation.** Let `c = (U, x, y)` be a coordinate neighbourhood of `p`, `C` cut
out by `f` on `U` with `mult_p f = m ≥ 1`, and `q` a point of the exceptional curve in the chart
`D₊(xt)` with `mult_q C₁ = m`. Then for some `r ∈ Γ(S, U)`, `f` is in normal form with respect
to `(x, y - r x)` and `π^*(y - r x) = π^* x · t` with `t ∈ 𝔪_q`. -/
private theorem exists_isInNormalForm_of_mem_chart {S : Scheme.{u}} [IsNoetherian S] {p : S}
    (hp : IsClosed ({p} : Set S))
    (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2)
    (C : S.IdealSheafData) (c : CoordinateNeighbourhood S p) (f : Γ(S, c.U))
    (hCf : C.ideal ⟨c.U, c.isAffineOpen⟩ = Ideal.span {f}) (m : ℕ)
    (hm : mult ((S.presheaf.germ c.U p c.mem).hom f) = m) (hm1 : 1 ≤ m)
    (hx : c.x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩)
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hqW : q ∈ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1)
    (hqE : q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support)
    (hmq : multAt (birationalTransform p hp C) q = m) :
    ∃ h : (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base q = p,
      ∃ x y : S.presheaf.stalk p, IsInNormalForm x y ((S.presheaf.germ c.U p c.mem).hom f) ∧
        ∃ t ∈ maximalIdeal
            ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk q),
          ((S.presheaf.stalkCongr (Inseparable.of_eq h)).inv ≫
              (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).stalkMap q).hom y =
            ((S.presheaf.stalkCongr (Inseparable.of_eq h)).inv ≫
              (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).stalkMap q).hom x *
              t := by
  have := c.isDomain
  haveI := hreg
  have hqp := (mem_support_exceptionalIdeal_iff p hp q).mp hqE
  refine ⟨hqp, ?_⟩
  -- the leading term of `f`
  have hmax : maximalIdeal (S.presheaf.stalk p) =
      Ideal.span {(S.presheaf.germ c.U p c.mem).hom c.x,
        (S.presheaf.germ c.U p c.mem).hom c.y} := by
    let := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨p, c.mem⟩ : c.U)
    have := c.isAffineOpen.isLocalization_stalk ⟨p, c.mem⟩
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      (c.isAffineOpen.primeIdealOf ⟨p, c.mem⟩).asIdeal, ← c.span_eq, Ideal.map_span,
      Set.image_pair]
    rfl
  obtain ⟨⟨F, hF, -⟩, hF0⟩ := MMP.Resolution.Kollar.existsUnique_isLeadingTerm hdim hmax
    (f := (S.presheaf.germ c.U p c.mem).hom f) (by rw [hm]; exact ENat.coe_ne_top m)
  have hFne := hF0 F hF
  have hFm : F.IsHomogeneous m := by
    obtain ⟨m', hm'', hFh, -⟩ := hF
    rwa [Nat.cast_inj.mp (hm''.symm.trans hm : (m' : ℕ∞) = m)] at hFh
  -- the chart `Spec R[y/x]`
  obtain ⟨hx', e, he⟩ := CoordinateNeighbourhood.exists_iso_spec_adjoin_div hp hreg hdim c
  obtain rfl : hx = hx' := rfl
  obtain ⟨hE, hφC, hφX⟩ :=
    CoordinateNeighbourhood.comap_exceptionalIdeal_eq_ker_and_exceptionalChartPolynomialEquiv
      hp hreg hdim c hx e he
  let φ := CoordinateNeighbourhood.exceptionalChartPolynomialEquiv hp hreg hdim c
  obtain ⟨f₁, hf₁, hφf⟩ := CoordinateNeighbourhood.exists_eq_pow_mul_and_mk_eq hp hreg hdim c f m
    hm F hF
  have hP := hφf φ.toRingHom hφC hφX
  have h₁ := CoordinateNeighbourhood.comap_birationalTransform_eq_ker hp hreg hdim c f m hm C hCf
    hx e he f₁ hf₁
  obtain ⟨z, hz⟩ := exists_mul_eq (y := c.y) (CoordinateNeighbourhood.x_ne_zero hdim c)
  obtain ⟨w, rfl⟩ : ∃ w, (e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal
      ⟨({p} : Set S), hp⟩) (⟨c.U, c.isAffineOpen⟩ : S.affineOpens) ⟨c.x, hx⟩).1.ι) w = q :=
    ⟨e.hom ⟨q, hqW⟩, by
      rw [Scheme.Hom.comp_apply]
      erw [Scheme.hom_inv_apply]
      rfl⟩
  exact exists_isInNormalForm_of_isOpenImmersion hp C c f m hm hm1 hmax F hF hFm hFne _
    (by rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]) z hz φ hφC (hφX z hz) f₁ hP hE h₁ w hqE
    hmq hqp

end ChartPoint

/-! ### The theorem -/

/-- Precomposing with an isomorphism keeps the residue field maps bijective. -/
private theorem bijective_residueFieldMap_comp_of_isIso {X Y Z : Scheme.{u}} (φ : X ⟶ Y)
    [IsIso φ] (g : Y ⟶ Z) (x : X) (h : Function.Bijective (g.residueFieldMap (φ x)).hom) :
    Function.Bijective ((φ ≫ g).residueFieldMap x).hom := by
  rw [Scheme.residueFieldMap_comp]
  exact (ConcreteCategory.bijective_of_isIso (φ.residueFieldMap x)).comp h

/-- **Multiplicity drops unless the leading term is a power of a linear form** (Kollár 1.66,
proof of 1.69). Let `S` be a Noetherian scheme, `p ∈ S` a closed point with `𝒪_{S,p}` regular
of dimension `2`, `C ⊆ S` an effective Cartier divisor with local equation `f ∈ 𝒪_{S,p}` and
`m = mult_p C ≥ 1`, `π : B_pS → S` the blow-up of `p`, `E` its exceptional curve and
`C₁ = MMP.Resolution.birationalTransform p hp C`. If a point `q ∈ C₁ ∩ E` has
`mult_q C₁ = m`, then `κ(p) → κ(q)` is bijective, `C₁ ∩ E = {q}`, `π q = p`, and there is a
regular system of parameters `(x, y)` of `𝒪_{S,p}` with `f` in normal form
(`MMP.Resolution.IsInNormalForm`) such that the image of `y` in `𝒪_{B_pS,q}` is the image of `x`
times an element `t` of the maximal ideal, i.e. `q` is the point `(x, y/x)` of `Spec R[y/x]`. -/
@[mmp "lem_kr1c_multiplicity_drops_unless_power_of_linear_form"]
public theorem exists_isInNormalForm_of_multAt_birationalTransform_eq
    {S : Scheme.{u}} [IsNoetherian S] {p : S} (hp : IsClosed ({p} : Set S))
    (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2)
    (C : S.IdealSheafData) (hC : MMP.Intersection.IsEffectiveCartierSubscheme C)
    (f : S.presheaf.stalk p) (hf : IdealSheafData.stalk C p = Ideal.span {f})
    (m : ℕ) (hm : multAt C p = m) (hm1 : 1 ≤ m)
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hqC : q ∈ (birationalTransform p hp C).support)
    (hqE : q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support)
    (hmq : multAt (birationalTransform p hp C) q = m) :
    Function.Bijective
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).residueFieldMap q).hom ∧
      ((birationalTransform p hp C ⊔
          exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support :
          Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))) = {q} ∧
      ∃ h : (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base q = p,
        ∃ x y : S.presheaf.stalk p, IsInNormalForm x y f ∧
          ∃ t ∈ maximalIdeal
              ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk q),
            ((S.presheaf.stalkCongr (Inseparable.of_eq h)).inv ≫
                (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).stalkMap q).hom y =
              ((S.presheaf.stalkCongr (Inseparable.of_eq h)).inv ≫
                (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).stalkMap q).hom x *
                t := by
  haveI := hreg
  haveI : IsDomain (S.presheaf.stalk p) := IsRegularLocalRing.isDomain _
  -- the residue degree at `q` and the uniqueness of `q`
  obtain ⟨hfin, hsum⟩ :=
    sum_residueDegree_mul_multAt_birationalTransform_le_multAt hp hreg hdim C hC
  rw [hm] at hsum
  classical
  obtain ⟨hdeg, huniq⟩ := le_one_and_eq_of_sum_mul_le hm1
    (fun q' => one_le_toENat_rank _)
    (fun q' hq' => one_le_multAt_of_mem_support ((mem_toFinset_support_sup_iff hfin).mp hq').1)
    ((mem_toFinset_support_sup_iff hfin).mpr ⟨hqC, hqE⟩) hmq hsum
  refine ⟨bijective_of_toENat_rank_le_one _ hdeg, ?_, ?_⟩
  · ext q'
    simp only [Set.mem_singleton_iff]
    refine ⟨fun hq' => huniq q' ((Set.Finite.mem_toFinset _).mpr hq'), ?_⟩
    rintro rfl
    exact (Set.Finite.mem_toFinset _).mp ((mem_toFinset_support_sup_iff hfin).mpr ⟨hqC, hqE⟩)
  -- the normal form, read on the chart containing `q`
  obtain ⟨c, f', hCf, hmult⟩ :=
    exists_coordinateNeighbourhood_of_isEffectiveCartierSubscheme hp hreg hdim C hC
  have hm' : mult ((S.presheaf.germ c.U p c.mem).hom f') = m := hmult.symm.trans hm
  have hassoc : Associated ((S.presheaf.germ c.U p c.mem).hom f') f := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hf,
      IdealSheafData.stalk_eq_map_germ C p ⟨c.U, c.isAffineOpen⟩ c.mem, hCf, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨hx, -⟩ := CoordinateNeighbourhood.exists_iso_spec_adjoin_div hp hreg hdim c
  obtain ⟨hy, -⟩ :=
    CoordinateNeighbourhood.exists_iso_spec_adjoin_div hp hreg hdim (swapCoordinates c)
  rcases mem_or_mem_of_mem_support hp c hx hy q hqE with hW | hW
  · obtain ⟨h, x, y, hNF, t, ht, heq⟩ :=
      exists_isInNormalForm_of_mem_chart hp hreg hdim C c f' hCf m hm' hm1 hx q hW hqE hmq
    exact ⟨h, x, y, IsInNormalForm.of_associated hNF hassoc, t, ht, heq⟩
  · obtain ⟨h, x, y, hNF, t, ht, heq⟩ :=
      exists_isInNormalForm_of_mem_chart hp hreg hdim C (swapCoordinates c) f' hCf m hm' hm1 hy
        q hW hqE hmq
    exact ⟨h, x, y, IsInNormalForm.of_associated hNF hassoc, t, ht, heq⟩

/-- **A point of the same multiplicity is the only point over the centre** (Kollár, proof of
1.67). Let `S` be a Noetherian scheme, `p ∈ S` a closed point with `𝒪_{S,p}` regular of
dimension `2`, `C ⊆ S` an effective Cartier divisor with `m = mult_p C ≥ 2`, let
`π : B_pS → S` be the blow-up of `p` and `C₁ = MMP.Resolution.birationalTransform p hp C`. If a
point `q` of `C₁` on the exceptional curve has `mult_q C₁ = m`, then `q` is the only point of `C₁`
over `p` and `mult_q C₁ ≥ 2`; if no point of `C₁` on the exceptional curve has multiplicity `m`,
then every point of `C₁` over `p` has multiplicity `< m`. -/
@[mmp "lem_kr1c_unique_point_of_same_multiplicity"]
public theorem birationalTransform_fibre_eq_singleton_or_multAt_lt
    {S : Scheme.{u}} [IsNoetherian S] {p : S} (hp : IsClosed ({p} : Set S))
    (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2)
    (C : S.IdealSheafData) (hC : MMP.Intersection.IsEffectiveCartierSubscheme C)
    (m : ℕ) (hm : multAt C p = m) (hm2 : 2 ≤ m) :
    (∀ q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩),
        q ∈ (birationalTransform p hp C).support →
        q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support →
        multAt (birationalTransform p hp C) q = m →
          {q' | q' ∈ (birationalTransform p hp C).support ∧
              (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base q' = p} =
            ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))) ∧
          2 ≤ multAt (birationalTransform p hp C) q) ∧
      ((∀ q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩),
          q ∈ (birationalTransform p hp C).support →
          q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support →
          multAt (birationalTransform p hp C) q ≠ m) →
        ∀ q' : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩),
          q' ∈ (birationalTransform p hp C).support →
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base q' = p →
          multAt (birationalTransform p hp C) q' < m) := by
  obtain ⟨hfin, hsum⟩ :=
    sum_residueDegree_mul_multAt_birationalTransform_le_multAt hp hreg hdim C hC
  rw [hm] at hsum
  have hmem {q'} (hq'C : q' ∈ (birationalTransform p hp C).support)
      (hq'p : (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base q' = p) :
      q' ∈ hfin.toFinset :=
    (mem_toFinset_support_sup_iff hfin).mpr
      ⟨hq'C, (mem_support_exceptionalIdeal_iff p hp q').mpr hq'p⟩
  have hle {q'} (hq' : q' ∈ hfin.toFinset) :=
    (le_sum_mul (fun _ _ => one_le_toENat_rank _) hq').trans hsum
  refine ⟨fun q hqC hqE hmq => ⟨?_, by rw [hmq]; exact_mod_cast hm2⟩, fun hno q' hq'C hq'p => ?_⟩
  · have huniq := eq_of_le_of_sum_le
      (fun q' hq' => (one_le_multAt_of_mem_support
        ((mem_toFinset_support_sup_iff hfin).mp hq').1).trans
          (le_mul_of_one_le_left' (one_le_toENat_rank _)))
      ((mem_toFinset_support_sup_iff hfin).mpr ⟨hqC, hqE⟩)
      (hmq ▸ le_mul_of_one_le_left' (one_le_toENat_rank _)) hsum
    ext q'
    exact ⟨fun ⟨hq'C, hq'p⟩ => huniq q' (hmem hq'C hq'p),
      by rintro rfl; exact ⟨hqC, (mem_support_exceptionalIdeal_iff p hp q').mp hqE⟩⟩
  · exact (hle (hmem hq'C hq'p)).lt_of_ne
      (hno q' hq'C ((mem_support_exceptionalIdeal_iff p hp q').mpr hq'p))

end MMP.Resolution

namespace MMP.Resolution.PointBlowupSequence

/-! ### Leading terms divisible by the leading form of a parameter -/

section Algebra

open MvPolynomial

/-- The homogeneous component of degree `n` of `φ * ψ`, for `φ` homogeneous of degree `d`. -/
private theorem homogeneousComponent_mul_of_isHomogeneous {σ R : Type*} [CommSemiring R]
    {φ : MvPolynomial σ R} {d : ℕ} (hφ : φ.IsHomogeneous d) (ψ : MvPolynomial σ R) (n : ℕ) :
    homogeneousComponent n (φ * ψ) =
      if d ≤ n then φ * homogeneousComponent (n - d) ψ else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent ψ]
  rw [Finset.mul_sum, map_sum]
  have hk : ∀ k, homogeneousComponent n (φ * homogeneousComponent k ψ) =
      if n = d + k then φ * homogeneousComponent k ψ else 0 := fun k =>
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      (hφ.mul (homogeneousComponent_isHomogeneous k ψ)))
  simp_rw [hk]
  split_ifs with hdn
  · rw [Finset.sum_eq_single (n - d)]
    · exact ite_cond_eq_true _ _ (eq_true (by omega))
    · intro k _ hk'
      exact ite_cond_eq_false _ _ (eq_false (by omega))
    · intro hnot
      have h1 : ψ.totalDegree < n - d := by
        simp only [Finset.mem_range, not_lt] at hnot
        omega
      rw [homogeneousComponent_eq_zero _ _ h1, mul_zero, ite_self]
  · exact Finset.sum_eq_zero fun k _ => ite_cond_eq_false _ _ (eq_false (by omega))

/-- Taking a homogeneous component commutes with mapping the coefficients. -/
private theorem map_homogeneousComponent {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (n : ℕ) (p : MvPolynomial σ R) :
    map g (homogeneousComponent n p) = homogeneousComponent n (map g p) := by
  ext d
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- A form of degree `n` in `x, y ∈ I` takes a value in `I^n`. -/
private theorem eval_mem_pow {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (hx : x ∈ I)
    (hy : y ∈ I) {n : ℕ} {G : MvPolynomial (Fin 2) R} (hG : G.IsHomogeneous n) :
    eval ![x, y] G ∈ I ^ n := by
  rw [eval_eq']
  refine Ideal.sum_mem _ fun d hd => ?_
  have hdeg : d 0 + d 1 = n := add_eq_of_mem_support hG hd
  have hp : (∏ i, (![x, y] : Fin 2 → R) i ^ d i) ∈ I ^ n := by
    rw [Fin.prod_univ_two, ← hdeg, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)
  exact Ideal.mul_mem_left _ _ hp

/-- If the leading form `L` of `e` divides the leading term `F` of `f` (of multiplicity `m`),
then `f ≡ e h` modulo `𝔪^{m+1}` for some `h`. -/
private theorem exists_sub_mul_mem_pow_succ_of_dvd {x y e f : A} (hx : x ∈ maximalIdeal A)
    (hy : y ∈ maximalIdeal A) {m : ℕ} (hm : mult f = m)
    {L F : MvPolynomial (Fin 2) (ResidueField A)} (hL : IsLeadingTerm x y e L)
    (hF : IsLeadingTerm x y f F) (hdvd : L ∣ F) :
    ∃ h : A, f - e * h ∈ maximalIdeal A ^ (m + 1) := by
  obtain ⟨d, -, hLh, Ge, hGe, hGeL, heGe⟩ := hL
  obtain ⟨m', hm', hFh, Gf, hGf, hGfF, hfGf⟩ := hF
  have hmm : m' = m := by exact_mod_cast hm'.symm.trans hm
  subst hmm
  obtain ⟨H, rfl⟩ := hdvd
  obtain ⟨H₀, hH₀⟩ := map_surjective (residue A) residue_surjective H
  have hFc := homogeneousComponent_mul_of_isHomogeneous hLh H m'
  rw [homogeneousComponent_eq_self hFh] at hFc
  by_cases hdm : d ≤ m'
  · simp only [hdm, ite_true] at hFc
    set H₁ := homogeneousComponent (m' - d) H₀ with hH₁
    have hH₁h : H₁.IsHomogeneous (m' - d) := homogeneousComponent_isHomogeneous _ _
    have hPh : (Gf - Ge * H₁).IsHomogeneous m' := by
      refine hGf.sub ?_
      have := hGe.mul hH₁h
      rwa [Nat.add_sub_cancel' hdm] at this
    have hP0 : map (residue A) (Gf - Ge * H₁) = 0 := by
      rw [map_sub, map_mul, hGfF, hGeL, hH₁, map_homogeneousComponent, hH₀, hFc, sub_self]
    have h1 := eval_mem_pow_succ_of_map_eq_zero hx hy hPh hP0
    have h2 : (e - MvPolynomial.eval ![x, y] Ge) * MvPolynomial.eval ![x, y] H₁ ∈
        maximalIdeal A ^ (m' + 1) := by
      have := Ideal.mul_mem_mul heGe (eval_mem_pow hx hy hH₁h)
      rwa [← pow_add, show d + 1 + (m' - d) = m' + 1 by omega] at this
    refine ⟨MvPolynomial.eval ![x, y] H₁, ?_⟩
    have : f - e * MvPolynomial.eval ![x, y] H₁ = (f - MvPolynomial.eval ![x, y] Gf) +
        MvPolynomial.eval ![x, y] (Gf - Ge * H₁) -
        (e - MvPolynomial.eval ![x, y] Ge) * MvPolynomial.eval ![x, y] H₁ := by
      rw [map_sub, map_mul]
      ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hfGf h1) h2
  · simp only [hdm, ite_false] at hFc
    have h1 := eval_mem_pow_succ_of_map_eq_zero hx hy hGf (by rw [hGfF, hFc])
    exact ⟨0, by simpa using Ideal.add_mem _ hfGf h1⟩

/-- In a Noetherian local ring `(A, 𝔪)` with `dim A/J ≥ 1`, `𝔪^k ⊄ J + 𝔪^{k+1}`. -/
private theorem not_pow_le_sup_pow_succ [IsNoetherianRing A] {J : Ideal A}
    (hdim : 1 ≤ ringKrullDim (A ⧸ J)) (k : ℕ) :
    ¬ maximalIdeal A ^ k ≤ J ⊔ maximalIdeal A ^ (k + 1) := by
  intro h
  set B := A ⧸ J
  have hB : Nontrivial B := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J
  have hm : (maximalIdeal A).map π = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective
  have h' : maximalIdeal B ^ k ≤ maximalIdeal B • maximalIdeal B ^ k := by
    have := Ideal.map_mono (f := π) h
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow, Ideal.map_pow, hm]
      at this
    rwa [smul_eq_mul, ← pow_succ']
  have hbot : maximalIdeal B ^ k = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h'
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  have : IsArtinianRing B :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal B).mpr ⟨k, hbot⟩
  have h0 : ringKrullDim B = 0 := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mp
    (isArtinianRing_iff_krullDimLE_zero.mp this)
  rw [h0] at hdim
  exact absurd hdim (by decide)

/-- If `dim A/J₂ ≥ 1` and `J₁ ⊆ 𝔪ʲ`, then `j ≤ length_A A/(J₁ + J₂)`. -/
private theorem le_length_quotient_of_le_pow [IsNoetherianRing A] {J₁ J₂ : Ideal A}
    (hdim : 1 ≤ ringKrullDim (A ⧸ J₂)) {j : ℕ} (hj : J₁ ≤ maximalIdeal A ^ j) :
    (j : ℕ∞) ≤ Module.length A (A ⧸ (J₁ ⊔ J₂)) := by
  set J : Ideal A := J₁ ⊔ J₂
  let f : ℕ → Submodule A (A ⧸ J) := fun k =>
    Submodule.map J.mkQ (maximalIdeal A ^ k : Ideal A)
  have hstep : ∀ k, k < j → f (k + 1) < f k := by
    intro k hk
    refine lt_of_le_of_ne (Submodule.map_mono (Ideal.pow_le_pow_right k.le_succ)) fun heq => ?_
    have h2 := congrArg (Submodule.comap J.mkQ) heq
    simp only [f, Submodule.comap_map_mkQ] at h2
    refine not_pow_le_sup_pow_succ hdim k ?_
    have hJ : J ≤ J₂ ⊔ maximalIdeal A ^ (k + 1) :=
      sup_le ((hj.trans (Ideal.pow_le_pow_right hk)).trans le_sup_right) le_sup_left
    calc maximalIdeal A ^ k ≤ J ⊔ maximalIdeal A ^ k := le_sup_right
      _ = J ⊔ maximalIdeal A ^ (k + 1) := h2.symm
      _ ≤ _ := sup_le hJ le_sup_right
  let p : LTSeries (Submodule A (A ⧸ J)) :=
    { length := j
      toFun := fun i => f (j - i)
      step := fun i => by
        simp only [Fin.val_castSucc, Fin.val_succ]
        rw [show j - (i : ℕ) = (j - (i + 1)) + 1 by omega]
        exact hstep _ (by omega) }
  have hlast : p.last = ⊤ := by simp [p, f, RelSeries.last]
  rw [Module.length_eq_height, ← hlast]
  exact Order.length_le_height_last (p := p)

/-- In a two-dimensional Noetherian local ring, `dim A/(e) ≥ 1` for `e ∈ 𝔪`. -/
private theorem one_le_ringKrullDim_quotient_span_singleton [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) {e : A} (he : e ∈ maximalIdeal A) :
    1 ≤ ringKrullDim (A ⧸ Ideal.span {e}) := by
  have := Ideal.height_le_ringKrullDim_quotient_add_one (p := maximalIdeal A) he
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim, ← one_add_one_eq_two] at this
  exact ENat.WithBot.add_le_add_natCast_right_iff.mp this

/-- Replacing `f` by `f - e h` does not change the ideal `(f, e)`. -/
private theorem span_sup_span_sub_mul {R : Type*} [CommRing R] (f e h : R) :
    Ideal.span {f - e * h} ⊔ Ideal.span {e} = Ideal.span {f} ⊔ Ideal.span {e} := by
  rw [← Ideal.span_insert, ← Ideal.span_insert, sub_eq_add_neg, mul_comm, ← neg_mul,
    Ideal.span_pair_add_mul_right]

/-- **The leading form of a regular curve does not divide the leading term**, once the
intersection length is the multiplicity: if `length A/(f, e) = mult f = m` in a two-dimensional
Noetherian local ring, the leading form `L` of `e ∈ 𝔪` does not divide the leading term `F` of
`f`; otherwise `f ≡ e h` modulo `𝔪^{m+1}` and the length would be at least `m + 1`. -/
private theorem not_dvd_of_length_eq [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    {x y e f : A} (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A) (he : e ∈ maximalIdeal A)
    {m : ℕ} (hm : mult f = m) {L F : MvPolynomial (Fin 2) (ResidueField A)}
    (hL : IsLeadingTerm x y e L) (hF : IsLeadingTerm x y f F)
    (hlen : Module.length A (A ⧸ (Ideal.span {f} ⊔ Ideal.span {e})) = m) : ¬ L ∣ F := by
  intro hdvd
  obtain ⟨h, hh⟩ := exists_sub_mul_mem_pow_succ_of_dvd hx hy hm hL hF hdvd
  have hle := le_length_quotient_of_le_pow (J₁ := Ideal.span {f - e * h})
    (one_le_ringKrullDim_quotient_span_singleton hdim he)
    ((Ideal.span_singleton_le_iff_mem _).mpr hh)
  rw [span_sup_span_sub_mul, hlen] at hle
  exact absurd (by exact_mod_cast hle : m + 1 ≤ m) (by omega)

end Algebra

/-! ### Transport along ring isomorphisms -/

section RingEquiv

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A surjection `R → T` with kernel `K` identifies the `R`-length of `R/K` with the length of
`T` over itself. -/
private theorem length_quotient_eq_of_surjective {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (hφ : Function.Surjective φ) {K : Ideal R} (hK : RingHom.ker φ = K) :
    Module.length R (R ⧸ K) = Module.length T T := by
  subst hK
  letI := φ.toAlgebra
  exact ((Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hφ).toLinearEquiv
    |>.length_eq).trans (Module.length_eq_of_surjective hφ)

/-- A ring isomorphism preserves the length of a cyclic quotient. -/
private theorem length_quotient_map_ringEquiv (σ : A ≃+* B) (J : Ideal A) :
    Module.length B (B ⧸ J.map σ) = Module.length A (A ⧸ J) := by
  have h1 := length_quotient_eq_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h2 := length_quotient_eq_of_surjective ((Ideal.Quotient.mk J).comp (σ.symm : B →+* A))
    (Ideal.Quotient.mk_surjective.comp σ.symm.surjective) (K := J.map σ) (by
      ext b
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        ← Ideal.symm_apply_mem_of_equiv_iff]
      rfl)
  rw [h1, h2]

end RingEquiv

/-! ### Stalks of ideal sheaves -/

section Stalks

variable {X Y : Scheme.{u}}

/-- The stalk of a sum of ideal sheaves is the sum of the stalks. -/
private theorem stalk_sup (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hxU, Scheme.IdealSheafData.ideal_sup,
    Pi.sup_apply, Ideal.map_sup]

private theorem multAt_comap_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j]
    (I : Y.IdealSheafData) (x : X) : multAt (I.comap j) x = multAt I (j x) := by
  rw [multAt, multAt, stalk_comap_eq_map_stalkEquiv,
    MMP.Threefold.Resolution.idealOrder_map_ringEquiv]

end Stalks

/-! ### Multiple points of reduced curves -/

section MultiplePoint

/-- **A multiple point of a reduced curve has a two-dimensional local ring** (Kollár §1.8). On a
regular scheme of dimension `2`, if `p` is a point of a reduced closed subscheme `C` whose stalk
is generated by a nonzerodivisor `g` with `mult_p C ≥ 2`, then `dim 𝒪_{S,p} = 2`: otherwise
`𝔪 = (t)` is principal, `g = a t²`, and `t a` would be a nonzero nilpotent of `𝒪_{C,p}`. -/
private theorem ringKrullDim_stalk_eq_two_of_two_le_multAt {S : Scheme.{u}}
    (hreg : ∀ q : S, IsRegularLocalRing (S.presheaf.stalk q)) (hdim : topologicalKrullDim S = 2)
    (C : S.IdealSheafData) [IsReduced C.subscheme] {p : S} (hpC : p ∈ C.support)
    {g : S.presheaf.stalk p} (hg : g ∈ nonZeroDivisors _)
    (hgen : IdealSheafData.stalk C p = Ideal.span {g}) (hm : 2 ≤ multAt C p) :
    ringKrullDim (S.presheaf.stalk p) = 2 := by
  obtain ⟨y, rfl⟩ : p ∈ Set.range C.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  haveI := hreg (C.subschemeι y)
  have hle : ringKrullDim (S.presheaf.stalk (C.subschemeι y)) ≤ 2 := by
    rw [← hdim, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact le_iSup (fun x : S => ringKrullDim (S.presheaf.stalk x)) _
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters
    (S.presheaf.stalk (C.subschemeι y))
  rw [hz.2] at hle ⊢
  have hn2 : n ≤ 2 := by exact_mod_cast hle
  by_contra hne
  have hn1 : n ≤ 1 := by
    have : n ≠ 2 := fun h => hne (by rw [h]; rfl)
    omega
  -- the maximal ideal is principal
  obtain ⟨t, ht⟩ : ∃ t, maximalIdeal (S.presheaf.stalk (C.subschemeι y)) = Ideal.span {t} := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl
    · exact ⟨0, by rw [← hz.1, Set.range_eq_empty, Ideal.span_empty,
        Ideal.span_singleton_eq_bot.mpr rfl]⟩
    · exact ⟨z 0, by rw [← hz.1, Set.range_unique]; rfl⟩
  have htm : t ∈ maximalIdeal (S.presheaf.stalk (C.subschemeι y)) :=
    ht ▸ Ideal.mem_span_singleton_self t
  -- `g = a t²`
  have hg2 : g ∈ maximalIdeal (S.presheaf.stalk (C.subschemeι y)) ^ 2 := by
    have h2 := (natCast_le_idealOrder_iff' (IdealSheafData.stalk C (C.subschemeι y)) 2).mp
      (by exact_mod_cast hm)
    rw [hgen] at h2
    exact h2 (Ideal.mem_span_singleton_self g)
  rw [ht, Ideal.span_singleton_pow] at hg2
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hg2
  -- the stalk of `C` is reduced
  have hker : RingHom.ker (C.subschemeι.stalkMap y).hom = Ideal.span {g} := by
    rw [← hgen, ← IdealSheafData.stalk_ker_of_isClosedImmersion,
      Scheme.IdealSheafData.ker_subschemeι]
  have hta : t * a ∈ Ideal.span {g} := by
    rw [← hker, RingHom.mem_ker]
    refine IsNilpotent.eq_zero ⟨2, ?_⟩
    rw [← map_pow, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
    exact ⟨a, by rw [← ha]; ring⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hta
  have hunit : IsUnit (1 - b * t) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((mem_maximalIdeal _).mp (Ideal.mul_mem_left _ b htm))
  have h0 : t * a * (1 - b * t) = 0 := by
    linear_combination -hb - b * ha
  have hta0 : t * a = 0 := (IsUnit.mul_left_eq_zero hunit).mp h0
  apply nonZeroDivisors.ne_zero hg
  rw [← ha, pow_two, ← mul_assoc, mul_comm a, hta0, zero_mul]

end MultiplePoint

/-! ### The local data along a blow-up sequence of constant multiplicity -/

section Sequence

/-- The `j`-th centre lies on the exceptional curve of the `j`-th blow-up. -/
private theorem mem_support_exceptionalIdeal {S₀ : Scheme.{u}}
    (s : PointBlowupSequence S₀) {C₀ : S₀.IdealSheafData} {m : ℕ}
    (hs : s.IsConstantMultiplicity C₀ m) (j : ℕ) (hj : (j : ℕ∞) < s.length) :
    (s.blowupIso j hj).hom (s.p (j + 1)) ∈ (exceptionalIdeal
      (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p j}, s.isClosed_p j hj⟩)).support := by
  rw [mem_support_exceptionalIdeal_iff]
  have := (hs.2 j hj).1
  rwa [PointBlowupSequence.σ, Scheme.Hom.comp_apply] at this

/-- **The local data of a blow-up sequence of multiplicity `m`.** At every centre `p_j`, `S_j` is
Noetherian, `𝒪_{S_j,p_j}` is regular of dimension `2`, and the stalks of `C_j` are generated by
nonzerodivisors. -/
private theorem invariants {S₀ : Scheme.{u}} [IsNoetherian S₀]
    (hreg : ∀ q : S₀, IsRegularLocalRing (S₀.presheaf.stalk q))
    (hdim : topologicalKrullDim S₀ = 2)
    (C₀ : S₀.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C₀)
    [IsReduced C₀.subscheme] {p₀ : S₀} (hp₀C : p₀ ∈ C₀.support) {m : ℕ} (hm : 2 ≤ m)
    (s : PointBlowupSequence S₀) (hp₀ : s.zeroIso.hom.base (s.p 0) = p₀)
    (hs : s.IsConstantMultiplicity C₀ m) :
    ∀ j : ℕ, (j : ℕ∞) < s.length → IsNoetherian (s.S j) ∧
      IsRegularLocalRing ((s.S j).presheaf.stalk (s.p j)) ∧
      ringKrullDim ((s.S j).presheaf.stalk (s.p j)) = 2 ∧
      HasPrincipalStalks (s.transformedSubscheme C₀ j)
  | 0, _ => by
    have hP : HasPrincipalStalks (s.transformedSubscheme C₀ 0) :=
      (hasPrincipalStalks_of_isEffectiveCartierDivisor hC).comap s.zeroIso.hom
    obtain ⟨g, hg, hgen⟩ := hasPrincipalStalks_of_isEffectiveCartierDivisor hC p₀
    have hm0 : multAt C₀ p₀ = m := by
      have := hs.1 0 zero_le
      rwa [show s.transformedSubscheme C₀ 0 = C₀.comap s.zeroIso.hom from rfl,
        multAt_comap_of_isOpenImmersion, hp₀] at this
    have hd := ringKrullDim_stalk_eq_two_of_two_le_multAt hreg hdim C₀ hp₀C hg hgen
      (by rw [hm0]; exact_mod_cast hm)
    subst hp₀
    haveI := hreg (s.zeroIso.hom (s.p 0))
    exact ⟨isNoetherian_of_iso s.zeroIso,
      IsRegularLocalRing.of_ringEquiv (stalkEquiv s.zeroIso.hom (s.p 0)),
      (ringKrullDim_eq_of_ringEquiv (stalkEquiv _ _)).symm.trans hd, hP⟩
  | j + 1, hj => by
    have hlt : (j : ℕ∞) < s.length :=
      lt_of_le_of_lt (by exact_mod_cast Nat.le_succ j) hj
    obtain ⟨hN, hR, hD, hP⟩ :=
      PointBlowupSequence.invariants hreg hdim C₀ hC hp₀C hm s hp₀ hs j hlt
    haveI := hN
    have hqE := PointBlowupSequence.mem_support_exceptionalIdeal s hs j hlt
    have hqcl : IsClosed ({(s.blowupIso j hlt).hom (s.p (j + 1))} : Set _) := by
      have := (Scheme.homeoOfIso (s.blowupIso j hlt)).isClosedMap _ (s.isClosed_p (j + 1) hj)
      rwa [Set.image_singleton] at this
    obtain ⟨hRq, hDq, -⟩ := isRegularLocalRing_stalk_blowUp_of_mem_support_exceptionalIdeal
      (s.p j) (s.isClosed_p j hlt) hR hD _ hqE
    haveI := Stacks.ResolutionOfSurfaces.isNoetherian_blowUp
      (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p j}, s.isClosed_p j hlt⟩)
    haveI := hRq
    refine ⟨isNoetherian_of_iso (s.blowupIso j hlt),
      IsRegularLocalRing.of_ringEquiv (stalkEquiv (s.blowupIso j hlt).hom (s.p (j + 1))),
      (ringKrullDim_eq_of_ringEquiv (stalkEquiv _ _)).symm.trans (hDq hqcl), ?_⟩
    rw [Kr1c.transformedSubscheme_succ s C₀ j hlt]
    exact (hasPrincipalStalks_birationalTransform _ hR hD hP
      (by rw [hs.1 j hlt.le]; exact ENat.coe_ne_top m)).comap _

end Sequence

/-! ### The point of constant multiplicity on the exceptional curve -/

section ExceptionalPoint

open MMP.Intersection

/-- A scheme finite over the spectrum of a field has finitely many points. -/
private theorem finite_univ_of_isFinite {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (.of K)) [IsFinite g] : (Set.univ : Set X).Finite := by
  simpa using g.finite_preimage (s := Set.univ) Set.finite_univ

/-- The `K`-algebra structure on the stalks of a scheme over `Spec K`, through the global
sections. -/
private noncomputable abbrev stalkAlgebra {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (.of K)) (z : X) : Algebra K (X.presheaf.stalk z) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ z trivial).hom.toAlgebra

/-- A finite scheme over a field is the disjoint union of its local rings: the dimension of its
ring of global sections is the sum of the dimensions of its stalks. -/
private theorem sum_finrank_stalk_eq_finrank_of_isFinite {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (.of K)) [IsFinite g] :
    ∑ z ∈ (finite_univ_of_isFinite g).toFinset,
        (letI := stalkAlgebra g z; Module.finrank K (X.presheaf.stalk z)) =
      (letI : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra;
        Module.finrank K Γ(X, ⊤)) := by
  classical
  letI alg : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra
  have : IsAffine X := isAffine_of_isAffineHom g
  have hU := isAffineOpen_top X
  haveI : Module.Finite K Γ(X, ⊤) := by
    have h : g.appTop.hom.Finite := ((isFinite_iff g).mp inferInstance).2 ⊤ (isAffineOpen_top _)
    have h2 : ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.Finite := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Finite.comp h (RingHom.Finite.of_surjective _
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2))
    exact h2
  haveI : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K _
  haveI : Fintype (PrimeSpectrum Γ(X, ⊤)) := Fintype.ofFinite _
  haveI : Finite X := Set.finite_univ_iff.mp (finite_univ_of_isFinite g)
  haveI : Fintype X := Fintype.ofFinite X
  show _ = Module.finrank K Γ(X, ⊤)
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum (R := Γ(X, ⊤)) K]
  let e : X ≃ PrimeSpectrum Γ(X, ⊤) :=
    (Equiv.Set.univ X).symm.trans
      (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso hU.isoSpec.hom.base))
  have hfs : (finite_univ_of_isFinite g).toFinset = Finset.univ := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_univ, Finset.mem_univ]
  rw [hfs]
  refine Fintype.sum_equiv e _ _ fun z => ?_
  letI := stalkAlgebra g z
  letI : Algebra Γ(X, ⊤) (X.presheaf.stalk z) :=
    X.presheaf.algebra_section_stalk (U := ⊤) ⟨z, trivial⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (e z).asIdeal :=
    hU.isLocalization_stalk ⟨z, trivial⟩
  haveI : IsScalarTower K Γ(X, ⊤) (X.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ((IsLocalization.algEquiv (e z).asIdeal.primeCompl (X.presheaf.stalk z)
    (Localization.AtPrime (e z).asIdeal)).restrictScalars K).toLinearEquiv.finrank_eq

/-- **Kollár, proof of 1.69, on the blow-up of one point.** Let `p` be a closed point of a
Noetherian scheme `S` with `𝒪_{S,p}` regular of dimension `2`, `C ⊆ S` a curve whose stalks are
generated by nonzerodivisors with `mult_p C = m ≥ 1`, and `q ∈ C₁ ∩ E` a point of the birational
transform on the exceptional curve with `mult_q C₁ = m`. Then `κ(p) → κ(q)` is bijective,
`𝒪_{B_pS,q}` is regular, and `length 𝒪_{B_pS,q}/(I_{C₁,q} + I_{E,q}) = m`: the intersection
`C₁ ∩ E` has degree `m` over `κ(p)` and is supported at the rational point `q`, while the order
of `I_{C₁,q}` bounds the length from below. -/
private theorem bijective_and_length_eq {S : Scheme.{u}} [IsNoetherian S] {p : S}
    (hp : IsClosed ({p} : Set S)) (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2) (C : S.IdealSheafData)
    (hC : HasPrincipalStalks C) (m : ℕ) (hm : multAt C p = m) (hm1 : 1 ≤ m)
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hqC : q ∈ (birationalTransform p hp C).support)
    (hqE : q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support)
    (hmq : multAt (birationalTransform p hp C) q = m) :
    Function.Bijective
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).residueFieldMap q).hom ∧
      IsRegularLocalRing
        ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk q) ∧
      Module.length ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk q)
        ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk q ⧸
          (IdealSheafData.stalk (birationalTransform p hp C) q ⊔
            IdealSheafData.stalk
              (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) q)) = m := by
  classical
  haveI := hreg
  haveI : IsLocallyNoetherian S := IsNoetherian.toIsLocallyNoetherian
  revert q hqC hqE hmq
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : TopologicalSpace.Closeds S)
  intro q hqC hqE hmq
  have hCc := isEffectiveCartierSubscheme_of_hasPrincipalStalks hC
  obtain ⟨f, -, hf⟩ := hC p
  set Z := birationalTransform p hp C ⊔ exceptionalIdeal I with hZ
  obtain ⟨g, hg, hgfin, hdeg⟩ :=
    exists_isFinite_finrank_birationalTransform_sup_exceptionalIdeal hp hreg hdim C hCc m hm
  haveI := hgfin
  have hqZ : q ∈ (Z.support : Set _) := by
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨hqC, hqE⟩
  obtain ⟨z, hz⟩ : q ∈ Set.range Z.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  -- the points of `C₁ ∩ E` are closed
  have hZaff : IsAffine Z.subscheme := isAffine_of_isAffineHom g
  haveI := AlgebraicGeometry.isArtinianRing_globalSections_of_isFinite_over_field _ g
  have hzc : IsClosed ({z} : Set Z.subscheme) := by
    rw [← (Scheme.homeoOfIso (Scheme.isoSpec _)).isClosed_image, Set.image_singleton]
    exact @isClosed_discrete _ _
      (IsArtinianRing.instDiscreteTopologyPrimeSpectrum _) _
  have hqc : IsClosed ({q} : Set (blowUp I)) := by
    have := Z.subschemeι.isClosedEmbedding.isClosedMap _ hzc
    rwa [Set.image_singleton, hz] at this
  obtain ⟨hbij, hsupp, -⟩ := MMP.Resolution.exists_isInNormalForm_of_multAt_birationalTransform_eq
    hp hreg hdim C hCc f hf m hm hm1 q hqC hqE hmq
  obtain ⟨hregq, hdim2, -⟩ :=
    isRegularLocalRing_stalk_blowUp_of_mem_support_exceptionalIdeal p hp hreg hdim q hqE
  have hdimq := hdim2 hqc
  haveI := hregq
  haveI : IsNoetherianRing ((blowUp I).presheaf.stalk q) := hregq.toIsNoetherian
  refine ⟨hbij, hregq, le_antisymm ?_ ?_⟩
  · -- `C₁ ∩ E` is one point, of degree `m`
    have hone : ∀ z' : Z.subscheme, z' = z := fun z' =>
      Z.subschemeι.isClosedEmbedding.injective (by
        have h1 : Z.subschemeι z' ∈ (Z.support : Set _) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z', rfl⟩
        rw [hsupp] at h1
        rw [h1, hz])
    have hsum := sum_finrank_stalk_eq_finrank_of_isFinite g
    have hfs : (finite_univ_of_isFinite g).toFinset = {z} := by
      ext z'
      simp only [Set.Finite.mem_toFinset, Set.mem_univ, Finset.mem_singleton, true_iff]
      exact hone z'
    rw [hfs, Finset.sum_singleton, hdeg] at hsum
    letI := stalkAlgebra g z
    haveI : Module.Finite (S.residueField p) (Z.subscheme.presheaf.stalk z) :=
      AlgebraicGeometry.finite_stalk_of_isFinite_over_field _ g z
    haveI : IsArtinianRing (Z.subscheme.presheaf.stalk z) :=
      IsArtinianRing.of_finite (S.residueField p) _
    haveI hnoeth : IsNoetherianRing (Z.subscheme.presheaf.stalk z) :=
      ((IsArtinianRing.tfae _ _).out 3 2).mp ‹_›
    have hfl := Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hnoeth, inferInstance⟩ :
        IsFiniteLength (Z.subscheme.presheaf.stalk z) (Z.subscheme.presheaf.stalk z))
    have hfinT := AlgebraicGeometry.finrank_stalk_eq_length_mul_finrank_residueField _ g z
    haveI : Module.Finite (S.residueField p)
        (IsLocalRing.ResidueField (Z.subscheme.presheaf.stalk z)) :=
      Module.Finite.of_surjective
        ((IsScalarTower.toAlgHom (S.residueField p) _ _).toLinearMap)
        IsLocalRing.residue_surjective
    have hpos : 0 < Module.finrank (S.residueField p)
        (IsLocalRing.ResidueField (Z.subscheme.presheaf.stalk z)) := Module.finrank_pos
    have hker : RingHom.ker (Z.subschemeι.stalkMap z).hom =
        IdealSheafData.stalk (birationalTransform p hp C) (Z.subschemeι z) ⊔
          IdealSheafData.stalk (exceptionalIdeal I) (Z.subschemeι z) := by
      rw [← IdealSheafData.stalk_ker_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι,
        stalk_sup]
    have hlenT := length_quotient_eq_of_surjective _ (Z.subschemeι.stalkMap_surjective z) hker
    subst hz
    rw [hlenT, ← ENat.coe_toNat hfl]
    have : (Module.length (Z.subscheme.presheaf.stalk z) (Z.subscheme.presheaf.stalk z)).toNat ≤
        m := by
      rw [← hsum, hfinT]
      exact Nat.le_mul_of_pos_right _ hpos
    exact_mod_cast this
  · -- the order of `I_{C₁,q}` bounds the length from below
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (blowUpToBase I q)) isOpen_univ
    obtain ⟨a, w, hw⟩ := exists_mem_range_blowupChartι I ⟨V, hV⟩
      (fun a : I.ideal ⟨V, hV⟩ => (a : Γ(S, V))) (fun a => a.2)
      (fun r hr => Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩) _ hpV
    have hqW : q ∈ (blowUpChartOpen I ⟨V, hV⟩ a).1 := ⟨w, trivial, hw⟩
    have hEst : IdealSheafData.stalk (exceptionalIdeal I) q =
        Ideal.span {(((blowUp I).presheaf.germ _ _ hqW).hom
          ((blowUpChartMap I ⟨V, hV⟩ a).hom (a : Γ(S, V))))} := by
      rw [IdealSheafData.stalk_eq_map_germ _ _ _ hqW, ideal_exceptionalIdeal_blowUpChartOpen,
        Ideal.map_span, Set.image_singleton]
    have he : ((blowUp I).presheaf.germ _ _ hqW).hom
        ((blowUpChartMap I ⟨V, hV⟩ a).hom (a : Γ(S, V))) ∈ maximalIdeal _ :=
      (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support _ q).mpr hqE
        (hEst ▸ Ideal.mem_span_singleton_self _)
    exact le_length_quotient_of_le_pow
      (J₁ := IdealSheafData.stalk (birationalTransform p hp C) q)
      (J₂ := IdealSheafData.stalk (exceptionalIdeal I) q)
      (by rw [hEst]; exact one_le_ringKrullDim_quotient_span_singleton hdimq he)
      ((natCast_le_idealOrder_iff' _ m).mp hmq.ge)

end ExceptionalPoint

/-! ### The theorem -/

/-- **The previous exceptional curve is not tangent** (Kollár, proof of 1.69). Let `S₀` be a
two-dimensional regular Noetherian scheme, `C₀ ⊆ S₀` a reduced effective Cartier divisor, `p₀ ∈ C₀`
a point and `m ≥ 2`, and let `s` be a blow-up sequence of multiplicity `m` for `C₀`
starting at `p₀` (`IsConstantMultiplicity`) of length at least `i + 1`. Let `E` be the exceptional
curve of `σ_{i+1} : S_{i+1} → S_i` and `C_{i+1} = s.transformedSubscheme C₀ (i + 1)`. Then
`κ(p_i) → κ(p_{i+1})` is bijective; for every regular system of parameters `(x, y)` of
`𝒪_{S_{i+1},p_{i+1}}`, the leading form `L` of a local equation of `E` does not divide the leading
term `F` of a local equation of `C_{i+1}`; and `𝒪_{S_{i+1},p_{i+1}} / (I_{C_{i+1}} + I_E)` has
length `m`. -/
@[mmp "lem_kr1c_tangent_direction_not_exceptional"]
public theorem not_dvd_isLeadingTerm_of_isConstantMultiplicity
    {S₀ : Scheme.{u}} [IsNoetherian S₀]
    (hreg : ∀ q : S₀, IsRegularLocalRing (S₀.presheaf.stalk q))
    (hdim : topologicalKrullDim S₀ = 2)
    (C₀ : S₀.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C₀)
    [IsReduced C₀.subscheme] {p₀ : S₀} (hp₀C : p₀ ∈ C₀.support) {m : ℕ} (hm : 2 ≤ m)
    (s : PointBlowupSequence S₀) (hp₀ : s.zeroIso.hom.base (s.p 0) = p₀)
    (hs : s.IsConstantMultiplicity C₀ m)
    (i : ℕ) (hk : ((i + 1 : ℕ) : ℕ∞) ≤ s.length) :
    Function.Bijective
        ((s.σ i (coe_lt_of_succ_le hk)).residueFieldMap (s.p (i + 1))).hom ∧
      (∀ x y : (s.S (i + 1)).presheaf.stalk (s.p (i + 1)),
        MMP.Mori.IsRegularSystemOfParameters ![x, y] →
        ∀ e : (s.S (i + 1)).presheaf.stalk (s.p (i + 1)),
          IdealSheafData.stalk
              ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
                ⟨{s.p i}, s.isClosed_p i (coe_lt_of_succ_le hk)⟩)).comap
                  (s.blowupIso i (coe_lt_of_succ_le hk)).hom) (s.p (i + 1)) =
            Ideal.span {e} →
        ∀ L, IsLeadingTerm x y e L →
        ∀ f : (s.S (i + 1)).presheaf.stalk (s.p (i + 1)),
          IdealSheafData.stalk (s.transformedSubscheme C₀ (i + 1)) (s.p (i + 1)) =
            Ideal.span {f} →
        ∀ F, IsLeadingTerm x y f F → ¬ L ∣ F) ∧
      Module.length ((s.S (i + 1)).presheaf.stalk (s.p (i + 1)))
          ((s.S (i + 1)).presheaf.stalk (s.p (i + 1)) ⧸
            (IdealSheafData.stalk (s.transformedSubscheme C₀ (i + 1)) (s.p (i + 1)) ⊔
              IdealSheafData.stalk
                ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
                  ⟨{s.p i}, s.isClosed_p i (coe_lt_of_succ_le hk)⟩)).comap
                    (s.blowupIso i (coe_lt_of_succ_le hk)).hom) (s.p (i + 1)))) = m := by
  have hlt := PointBlowupSequence.coe_lt_of_succ_le hk
  obtain ⟨hN, hR, hD, hP⟩ := PointBlowupSequence.invariants hreg hdim C₀ hC hp₀C hm s hp₀ hs i hlt
  haveI := hN
  set φ := (s.blowupIso i hlt).hom
  have hT := Kr1c.transformedSubscheme_succ s C₀ i hlt
  have hmi : multAt (s.transformedSubscheme C₀ i) (s.p i) = m := hs.1 i hlt.le
  have hmi1 : multAt (s.transformedSubscheme C₀ (i + 1)) (s.p (i + 1)) = m := hs.1 (i + 1) hk
  have hqC : s.p (i + 1) ∈ (s.transformedSubscheme C₀ (i + 1)).support :=
    (hs.2 i hlt).2.1.1
  rw [hT, multAt_comap_of_isOpenImmersion] at hmi1
  rw [hT, mem_support_comap_iff] at hqC
  have hqE := PointBlowupSequence.mem_support_exceptionalIdeal s hs i hlt
  obtain ⟨hbij, hregq, hlen⟩ := bijective_and_length_eq (s.isClosed_p i hlt) hR hD _ hP m hmi
    (by omega) _ hqC hqE hmi1
  -- the length on `S_{i+1}`
  have hlen' : Module.length ((s.S (i + 1)).presheaf.stalk (s.p (i + 1)))
      ((s.S (i + 1)).presheaf.stalk (s.p (i + 1)) ⧸
        (IdealSheafData.stalk (s.transformedSubscheme C₀ (i + 1)) (s.p (i + 1)) ⊔
          IdealSheafData.stalk
            ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
              ⟨{s.p i}, s.isClosed_p i hlt⟩)).comap φ) (s.p (i + 1)))) = m := by
    rw [hT, stalk_comap_eq_map_stalkEquiv, stalk_comap_eq_map_stalkEquiv, ← Ideal.map_sup,
      length_quotient_map_ringEquiv]
    exact hlen
  refine ⟨bijective_residueFieldMap_comp_of_isIso (s.blowupIso i hlt).hom _ _ hbij, ?_, hlen'⟩
  · intro x y hxy e he L hL f hf F hF
    have : IsNoetherianRing ((s.S (i + 1)).presheaf.stalk (s.p (i + 1))) :=
      (IsRegularLocalRing.of_ringEquiv (stalkEquiv φ (s.p (i + 1)))).toIsNoetherian
    have hmem : ∀ j, ![x, y] j ∈ maximalIdeal ((s.S (i + 1)).presheaf.stalk (s.p (i + 1))) :=
      fun j => hxy.1 ▸ Ideal.subset_span ⟨j, rfl⟩
    have heE : e ∈ maximalIdeal ((s.S (i + 1)).presheaf.stalk (s.p (i + 1))) := by
      refine (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support _ _).mpr ?_
        (he ▸ Ideal.mem_span_singleton_self e)
      rwa [mem_support_comap_iff]
    have hmf : mult f = m := by
      rw [mult, ← hf]
      exact hs.1 (i + 1) hk
    refine not_dvd_of_length_eq (by rw [hxy.2]; rfl) (hmem 0) (hmem 1) heE hmf hL hF ?_
    rw [← hf, ← he]
    exact hlen'

end MMP.Resolution.PointBlowupSequence

end
