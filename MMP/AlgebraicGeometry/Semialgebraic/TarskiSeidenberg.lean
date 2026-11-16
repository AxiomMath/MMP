module

public import MMP.AlgebraicGeometry.Semialgebraic.Basic
public import MMP.AlgebraicGeometry.Semialgebraic.PolynomialSignTransfer
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Multiset.DershowitzManna
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The Tarski–Seidenberg theorem

The projection `ℝ^{σ} × ℝ → ℝ^{σ}` maps semialgebraic sets to semialgebraic sets.

Following Hörmander, consider a finite family `F` of polynomials in one variable `t` whose
coefficients are polynomials in parameters `a ∈ ℝ^σ`. Every semialgebraic `A ⊆ ℝ^σ` is a finite
union of semialgebraic pieces on each of which the sign pattern of `t ↦ F(a, t)` (up to order
automorphisms of `ℝ`, `SameSignPattern`) is constant. The proof is by induction on the
multiset of degrees of `F` (Dershowitz–Manna order): on the part of `A` where the leading
coefficient of a member vanishes, that member is replaced by its truncation; where all leading
coefficients are invertible, a member `p` of maximal degree is replaced by `p'` and by the
pseudo-remainders of `p` by the other members and by `p'`, which determine the sign pattern
(`sameSignPattern_of_derivative`). A semialgebraic subset of `ℝ^σ × ℝ` is a finite union of sets
defined by sign conditions on finitely many polynomials, and whether such a condition is
realised over `a` only depends on the sign pattern at `a`.

## Main definitions

* `MMP.TarskiSeidenberg.specAt`: specialisation of the parameters.
* `MMP.TarskiSeidenberg.HasSignPatternCover`: a finite semialgebraic cover on
  whose pieces the sign pattern is constant.

## Main results

* `MMP.exists_pseudoDivision`: pseudo-division of polynomials over a commutative
  ring.
* `MMP.TarskiSeidenberg.hasSignPatternCover`: Hörmander's theorem.
* `MMP.IsSemialgebraic.exists_signConditions`: semialgebraic sets are defined by
  sign conditions.
* `MMP.IsSemialgebraic.projection`: the Tarski–Seidenberg theorem.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], §1.4, §2.2.
* [L. Hörmander, *The analysis of linear partial differential operators II*][hormander1983],
  Appendix A.2.
-/

@[expose] public section

open Polynomial

namespace MMP

/-! ### Pseudo-division -/

/-- **Pseudo-division.** Over a domain, for `F ≠ 0` and any `G` there are `k, q, r` with
`lc(F)ᵏ G = q F + r` and `deg r < deg F`. -/
theorem exists_pseudoDivision {R : Type*} [CommRing R] [IsDomain R] (F G : R[X]) (hF : F ≠ 0) :
    ∃ (k : ℕ) (q r : R[X]), C F.leadingCoeff ^ k * G = q * F + r ∧ r.degree < F.degree := by
  induction h : G.natDegree using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    by_cases hlt : G.degree < F.degree
    · exact ⟨0, 0, G, by simp, hlt⟩
    push Not at hlt
    have hG : G ≠ 0 := ne_zero_of_degree_ge_degree hlt hF
    have hmn : F.natDegree ≤ G.natDegree := natDegree_le_natDegree hlt
    have hc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hF
    have hcG : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hG
    set T := C G.leadingCoeff * X ^ (G.natDegree - F.natDegree) * F
    have hT : T.degree = G.degree := by
      simp only [T]
      rw [degree_mul, degree_C_mul_X_pow _ hcG, degree_eq_natDegree hF,
        degree_eq_natDegree hG]
      norm_cast
      omega
    have h1 : (C F.leadingCoeff * G).degree = G.degree := degree_C_mul hc
    have hlc : (C F.leadingCoeff * G).leadingCoeff = T.leadingCoeff := by
      simp only [T, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, mul_one]
      ring
    have hCG : C F.leadingCoeff * G ≠ 0 := mul_ne_zero (C_ne_zero.2 hc) hG
    set G' := C F.leadingCoeff * G - T
    have hG' : G'.degree < G.degree := by
      rw [← h1]
      exact degree_sub_lt_left (h1.trans hT.symm) hCG hlc
    have key : ∃ (k : ℕ) (q r : R[X]), C F.leadingCoeff ^ k * G' = q * F + r ∧
        r.degree < F.degree := by
      by_cases hlt' : G'.degree < F.degree
      · exact ⟨0, 0, G', by simp, hlt'⟩
      push Not at hlt'
      exact ih _ (h ▸ natDegree_lt_natDegree (ne_zero_of_degree_ge_degree hlt' hF) hG') G' rfl
    obtain ⟨k, q, r, hqr, hr⟩ := key
    refine ⟨k + 1, q + C F.leadingCoeff ^ k * C G.leadingCoeff * X ^ (G.natDegree - F.natDegree),
      r, ?_, hr⟩
    have : C F.leadingCoeff ^ (k + 1) * G = C F.leadingCoeff ^ k * G' +
        C F.leadingCoeff ^ k * T := by
      simp only [G']
      ring
    rw [this, hqr]
    simp only [T]
    ring

/-- Pseudo-division with an even power: `lc(F)^{2k} G = q F + r`, `deg r < deg F`. -/
theorem exists_pseudoDivision_even {R : Type*} [CommRing R] [IsDomain R] (F G : R[X])
    (hF : F ≠ 0) : ∃ (k : ℕ) (q r : R[X]), C F.leadingCoeff ^ (2 * k) * G = q * F + r ∧
      r.degree < F.degree := by
  obtain ⟨k, q, r, h, hr⟩ := exists_pseudoDivision F G hF
  have hc : F.leadingCoeff ^ k ≠ 0 := pow_ne_zero k (leadingCoeff_ne_zero.2 hF)
  refine ⟨k, C F.leadingCoeff ^ k * q, C F.leadingCoeff ^ k * r, ?_, ?_⟩
  · rw [two_mul, pow_add, mul_assoc, h]
    ring
  · rwa [← C_pow, degree_C_mul hc]

/-! ### Sign-pattern covers -/

namespace TarskiSeidenberg

variable {σ : Type*}

/-- Specialisation of the parameters at `a ∈ ℝ^σ`. -/
noncomputable abbrev specAt (a : σ → ℝ) : (MvPolynomial σ ℝ)[X] →+* ℝ[X] :=
  Polynomial.mapRingHom (MvPolynomial.eval a)

/-- `A ⊆ ℝ^σ` is a finite union of semialgebraic pieces on each of which the sign pattern of the
specialised family `t ↦ F i (a, t)` is constant. -/
def HasSignPatternCover {ι : Type*} (F : ι → (MvPolynomial σ ℝ)[X]) (A : Set (σ → ℝ)) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (C : κ → Set (σ → ℝ)), (∀ k, IsSemialgebraic (C k)) ∧
    (⋃ k, C k) = A ∧ ∀ k, ∀ a ∈ C k, ∀ b ∈ C k,
      SameSignPattern (fun i ↦ specAt a (F i)) (fun i ↦ specAt b (F i))

namespace HasSignPatternCover

variable {ι ι' : Type*} {F : ι → (MvPolynomial σ ℝ)[X]} {A A₁ A₂ : Set (σ → ℝ)}

/-- A set admitting a sign-pattern cover is semialgebraic. -/
theorem isSemialgebraic (h : HasSignPatternCover F A) : IsSemialgebraic A := by
  obtain ⟨κ, _, C, hC, hU, -⟩ := h
  rw [← hU]
  exact IsSemialgebraic.iUnion hC

/-- A cover for a family `G` whose sign pattern determines that of `F` on `A` is a cover for
`F`. -/
theorem of_imp {G : ι' → (MvPolynomial σ ℝ)[X]} (h : HasSignPatternCover G A)
    (himp : ∀ a ∈ A, ∀ b ∈ A,
      SameSignPattern (fun i ↦ specAt a (G i)) (fun i ↦ specAt b (G i)) →
      SameSignPattern (fun i ↦ specAt a (F i)) (fun i ↦ specAt b (F i))) :
    HasSignPatternCover F A := by
  obtain ⟨κ, hκ, C, hC, hU, hP⟩ := h
  have hmem : ∀ k, ∀ a ∈ C k, a ∈ A := fun k a ha ↦ hU ▸ Set.mem_iUnion.2 ⟨k, ha⟩
  exact ⟨κ, hκ, C, hC, hU, fun k a ha b hb ↦
    himp a (hmem k a ha) b (hmem k b hb) (hP k a ha b hb)⟩

/-- Sign-pattern covers of `A₁` and `A₂` for `F` give one of `A₁ ∪ A₂`. -/
theorem union (h₁ : HasSignPatternCover F A₁) (h₂ : HasSignPatternCover F A₂) :
    HasSignPatternCover F (A₁ ∪ A₂) := by
  obtain ⟨κ₁, _, C₁, hC₁, hU₁, hP₁⟩ := h₁
  obtain ⟨κ₂, _, C₂, hC₂, hU₂, hP₂⟩ := h₂
  refine ⟨κ₁ ⊕ κ₂, inferInstance, Sum.elim C₁ C₂, ?_, ?_, ?_⟩
  · rintro (k | k)
    exacts [hC₁ k, hC₂ k]
  · simp only [Set.iUnion_sum, Sum.elim_inl, Sum.elim_inr, hU₁, hU₂]
  · rintro (k | k)
    exacts [hP₁ k, hP₂ k]

/-- A semialgebraic set has a cover for any finite family of constants. -/
theorem of_natDegree_eq_zero {ι : Type} {F : ι → (MvPolynomial σ ℝ)[X]} [Finite ι]
    (hA : IsSemialgebraic A) (h0 : ∀ i, (F i).natDegree = 0) : HasSignPatternCover F A := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨ι → SignType, inferInstance,
    fun ε ↦ A ∩ {a | ∀ i, SignType.sign (MvPolynomial.eval a ((F i).coeff 0)) = ε i}, ?_, ?_, ?_⟩
  · intro ε
    simp only [Set.ofPred_forall]
    exact hA.inter (IsSemialgebraic.iInter fun i ↦ IsSemialgebraic.sign_eq _ _)
  · ext a
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨_, h, fun _ ↦ rfl⟩⟩
  · rintro ε a ⟨-, ha⟩ b ⟨-, hb⟩
    refine ⟨OrderIso.refl ℝ, fun i x ↦ ?_⟩
    change SignType.sign (eval x (specAt a (F i))) = SignType.sign (eval x (specAt b (F i)))
    rw [eq_C_of_natDegree_eq_zero (h0 i)]
    simp [ha i, hb i]

end HasSignPatternCover

/-! ### Hörmander's induction -/

open Classical in
/-- The multiset of degrees of the nonzero members of a finite family. -/
noncomputable def degreeMultiset {ι : Type*} [Fintype ι] (F : ι → (MvPolynomial σ ℝ)[X]) :
    Multiset ℕ :=
  ∑ i, if F i = 0 then 0 else {(F i).natDegree}

open Classical in
/-- `degreeMultiset F` splits as the contribution of `F i₀` plus that of the other members. -/
theorem degreeMultiset_eq_add {ι : Type*} [Fintype ι] (F : ι → (MvPolynomial σ ℝ)[X]) (i₀ : ι) :
    degreeMultiset F = (if F i₀ = 0 then 0 else {(F i₀).natDegree}) +
      ∑ i : {i // i ≠ i₀}, if F i = 0 then 0 else {(F i).natDegree} := by
  rw [degreeMultiset, ← (Equiv.optionSubtypeNe i₀).sum_comp, Fintype.sum_option]
  rfl

/-- Truncating a polynomial whose leading coefficient vanishes at `a` does not change its
specialisation at `a`. -/
theorem specAt_eraseLead (a : σ → ℝ) (P : (MvPolynomial σ ℝ)[X])
    (h : MvPolynomial.eval a P.leadingCoeff = 0) : specAt a P.eraseLead = specAt a P := by
  conv_rhs => rw [← eraseLead_add_C_mul_X_pow P]
  rw [map_add, map_mul, map_pow]
  simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X, h, map_zero, zero_mul, add_zero]

open Classical in
/-- The pseudo-remainder of `G` by `F` (with an even power of the leading coefficient), `0` for
`F = 0`. -/
noncomputable def pseudoRem (G F : (MvPolynomial σ ℝ)[X]) : (MvPolynomial σ ℝ)[X] :=
  if hF : F = 0 then 0 else (exists_pseudoDivision_even F G hF).choose_spec.choose_spec.choose

/-- For `F ≠ 0`, `lc(F)^{2k} G = q F + pseudoRem G F` for some `k, q`, and
`deg (pseudoRem G F) < deg F`. -/
theorem pseudoRem_spec (G F : (MvPolynomial σ ℝ)[X]) (hF : F ≠ 0) :
    (∃ (k : ℕ) (q : (MvPolynomial σ ℝ)[X]),
      C F.leadingCoeff ^ (2 * k) * G = q * F + pseudoRem G F) ∧
      (pseudoRem G F).degree < F.degree := by
  have h := (exists_pseudoDivision_even F G hF).choose_spec.choose_spec.choose_spec
  simp only [pseudoRem, hF, ↓reduceDIte]
  exact ⟨⟨_, _, h.1⟩, h.2⟩

/-- A nonzero pseudo-remainder of `G` by `F` has `natDegree` less than that of `F`. -/
theorem natDegree_pseudoRem_lt (G F : (MvPolynomial σ ℝ)[X]) (h : pseudoRem G F ≠ 0) :
    (pseudoRem G F).natDegree < F.natDegree := by
  have hF : F ≠ 0 := fun hF ↦ h (by simp [pseudoRem, hF])
  exact natDegree_lt_natDegree h (pseudoRem_spec G F hF).2

/-- At a zero of `F(a, ·)` with `lc(F)(a) ≠ 0`, `G(a, ·)` and its pseudo-remainder by `F` have the
same sign. -/
theorem sign_eval_specAt_pseudoRem (G F : (MvPolynomial σ ℝ)[X]) {a : σ → ℝ}
    (ha : MvPolynomial.eval a F.leadingCoeff ≠ 0) {x : ℝ} (hx : (specAt a F).eval x = 0) :
    SignType.sign ((specAt a G).eval x) = SignType.sign ((specAt a (pseudoRem G F)).eval x) := by
  have hF : F ≠ 0 := fun h ↦ ha (by simp [h])
  obtain ⟨k, q, h⟩ := (pseudoRem_spec G F hF).1
  have := congrArg (fun P ↦ (specAt a P).eval x) h
  simp only [map_mul, map_add, map_pow, eval_mul, eval_add, eval_pow] at this
  rw [hx, mul_zero, zero_add] at this
  rw [← this, sign_mul]
  simp only [coe_mapRingHom, map_C, eval_C]
  rw [sign_pos (Even.pow_pos (even_two_mul k) ha), one_mul]

variable {ι : Type}

/-- The family replacing `F i₀` by its derivative and by the pseudo-remainders of `F i₀` by the
other members and by its derivative. -/
noncomputable def hormanderFamily (F : ι → (MvPolynomial σ ℝ)[X]) (i₀ : ι) :
    {i // i ≠ i₀} ⊕ ({i // i ≠ i₀} ⊕ Bool) → (MvPolynomial σ ℝ)[X]
  | .inl i => F i
  | .inr (.inl i) => pseudoRem (F i₀) (F i)
  | .inr (.inr false) => derivative (F i₀)
  | .inr (.inr true) => pseudoRem (F i₀) (derivative (F i₀))

/-- Specialisation of the parameters commutes with the derivative in `X`. -/
theorem specAt_derivative (a : σ → ℝ) (P : (MvPolynomial σ ℝ)[X]) :
    specAt a (derivative P) = derivative (specAt a P) := by
  simp [derivative_map]

/-- **Hörmander's step.** On a set where the leading coefficients of the nonzero members never
vanish, the sign pattern of `hormanderFamily F i₀` determines that of `F`, for `F i₀`
non-constant. -/
theorem sameSignPattern_of_hormanderFamily [Finite ι] {F : ι → (MvPolynomial σ ℝ)[X]} {i₀ : ι}
    (hi₀ : 0 < (F i₀).natDegree) {a b : σ → ℝ}
    (ha : ∀ i, F i ≠ 0 → MvPolynomial.eval a (F i).leadingCoeff ≠ 0)
    (hb : ∀ i, F i ≠ 0 → MvPolynomial.eval b (F i).leadingCoeff ≠ 0)
    (h : SameSignPattern (fun j ↦ specAt a (hormanderFamily F i₀ j))
      (fun j ↦ specAt b (hormanderFamily F i₀ j))) :
    SameSignPattern (fun i ↦ specAt a (F i)) (fun i ↦ specAt b (F i)) := by
  classical
  have hF₀ : F i₀ ≠ 0 := ne_zero_of_natDegree_gt hi₀
  have : IsAddTorsionFree (MvPolynomial σ ℝ) := inferInstance
  have hd₀ : ∀ c : σ → ℝ, MvPolynomial.eval c (F i₀).leadingCoeff ≠ 0 →
      MvPolynomial.eval c (derivative (F i₀)).leadingCoeff ≠ 0 := fun c hc ↦ by
    rw [leadingCoeff_derivative, map_mul, map_natCast]
    exact mul_ne_zero hc (Nat.cast_ne_zero.2 hi₀.ne')
  have hspec : ∀ c : σ → ℝ, (∀ i, F i ≠ 0 → MvPolynomial.eval c (F i).leadingCoeff ≠ 0) →
      ∀ i x, specAt c (F i) ≠ 0 → (specAt c (F i)).eval x = 0 →
        SignType.sign ((specAt c (F i₀)).eval x) =
          SignType.sign ((specAt c (pseudoRem (F i₀) (F i))).eval x) := fun c hc i x hi hx ↦
    sign_eval_specAt_pseudoRem _ _ (hc i fun h ↦ hi (by simp [h])) hx
  have hspec₀ : ∀ c : σ → ℝ, MvPolynomial.eval c (F i₀).leadingCoeff ≠ 0 → ∀ x,
      (derivative (specAt c (F i₀))).eval x = 0 →
        SignType.sign ((specAt c (F i₀)).eval x) =
          SignType.sign ((specAt c (pseudoRem (F i₀) (derivative (F i₀)))).eval x) :=
    fun c hc x hx ↦ sign_eval_specAt_pseudoRem _ _ (hd₀ c hc) (by rwa [specAt_derivative])
  obtain ⟨φ, hφ⟩ := h
  have H := sameSignPattern_of_derivative (ι := {i // i ≠ i₀})
    (f := fun i ↦ specAt a (F i)) (g := fun i ↦ specAt b (F i))
    (r := fun i ↦ specAt a (pseudoRem (F i₀) (F i)))
    (s := fun i ↦ specAt b (pseudoRem (F i₀) (F i)))
    (p := specAt a (F i₀)) (q := specAt b (F i₀))
    (r₀ := specAt a (pseudoRem (F i₀) (derivative (F i₀))))
    (s₀ := specAt b (pseudoRem (F i₀) (derivative (F i₀))))
    (by simpa [natDegree_map_of_leadingCoeff_ne_zero _ (ha i₀ hF₀)] using hi₀)
    (by simpa [natDegree_map_of_leadingCoeff_ne_zero _ (hb i₀ hF₀)] using hi₀)
    (fun i x ↦ hspec a ha i x) (fun i x ↦ hspec b hb i x)
    (hspec₀ a (ha i₀ hF₀)) (hspec₀ b (hb i₀ hF₀)) φ
    (fun i x ↦ hφ (.inl i) x)
    (fun x ↦ by simpa [hormanderFamily, specAt_derivative] using hφ (.inr (.inr false)) x)
    (fun i x ↦ hφ (.inr (.inl i)) x) (fun x ↦ hφ (.inr (.inr true)) x)
  rw [← SameSignPattern.comp_equiv_iff (Equiv.optionSubtypeNe i₀)]
  convert H using 2 <;> rename_i o <;> cases o <;> rfl

open Classical in
/-- An element of `if P = 0 then 0 else {P.natDegree}` is `P.natDegree`, and then `P ≠ 0`. -/
theorem mem_degreeTerm {P : (MvPolynomial σ ℝ)[X]} {y : ℕ}
    (h : y ∈ (if P = 0 then 0 else {P.natDegree} : Multiset ℕ)) : P ≠ 0 ∧ y = P.natDegree := by
  split_ifs at h with hP
  · simp at h
  · exact ⟨hP, Multiset.mem_singleton.1 h⟩

open Classical in
/-- If `F i₀` is non-constant of maximal degree, the degree multiset of `hormanderFamily F i₀`
is smaller than that of `F` in the Dershowitz–Manna order. -/
theorem degreeMultiset_hormanderFamily_lt [Fintype ι] {F : ι → (MvPolynomial σ ℝ)[X]} {i₀ : ι}
    (hi₀ : 0 < (F i₀).natDegree) (hmax : ∀ i, (F i).natDegree ≤ (F i₀).natDegree) :
    Multiset.IsDershowitzMannaLT (degreeMultiset (hormanderFamily F i₀)) (degreeMultiset F) := by
  have hF₀ : F i₀ ≠ 0 := ne_zero_of_natDegree_gt hi₀
  rw [degreeMultiset_eq_add F i₀]
  simp only [hF₀, ↓reduceIte]
  set X := ∑ i : {i // i ≠ i₀}, if F i = 0 then (0 : Multiset ℕ) else {(F i).natDegree}
  set Y := (∑ i : {i // i ≠ i₀}, if pseudoRem (F i₀) (F i) = 0 then (0 : Multiset ℕ) else
      {(pseudoRem (F i₀) (F i)).natDegree}) +
    ((if pseudoRem (F i₀) (derivative (F i₀)) = 0 then (0 : Multiset ℕ) else
      {(pseudoRem (F i₀) (derivative (F i₀))).natDegree}) +
    (if derivative (F i₀) = 0 then (0 : Multiset ℕ) else {(derivative (F i₀)).natDegree}))
  have hQ : degreeMultiset (hormanderFamily F i₀) = X + Y := by
    simp only [degreeMultiset, Fintype.sum_sum_type, Fintype.sum_bool, hormanderFamily, X, Y]
    congr
  refine ⟨X, Y, {(F i₀).natDegree}, by simp, hQ, by rw [add_comm], fun y hy ↦
    ⟨_, Multiset.mem_singleton_self _, ?_⟩⟩
  have hd : (derivative (F i₀)).natDegree < (F i₀).natDegree := natDegree_derivative_lt hi₀.ne'
  simp only [Y, Multiset.mem_add, Multiset.mem_sum, Finset.mem_univ, true_and] at hy
  rcases hy with ⟨i, hi⟩ | hy | hy
  · obtain ⟨h0, rfl⟩ := mem_degreeTerm hi
    exact (natDegree_pseudoRem_lt _ _ h0).trans_le (hmax i)
  · obtain ⟨h0, rfl⟩ := mem_degreeTerm hy
    exact (natDegree_pseudoRem_lt _ _ h0).trans hd
  · obtain ⟨-, rfl⟩ := mem_degreeTerm hy
    exact hd

open Classical in
/-- Replacing a nonzero member `F i` by `(F i).eraseLead` decreases the degree multiset in the
Dershowitz–Manna order. -/
theorem degreeMultiset_update_eraseLead_lt [Fintype ι] {F : ι → (MvPolynomial σ ℝ)[X]} {i : ι}
    (hi : F i ≠ 0) :
    Multiset.IsDershowitzMannaLT (degreeMultiset (Function.update F i (F i).eraseLead))
      (degreeMultiset F) := by
  rw [degreeMultiset_eq_add F i, degreeMultiset_eq_add _ i, Function.update_self]
  simp only [hi, ↓reduceIte]
  have hX : (∑ j : {j // j ≠ i}, if Function.update F i (F i).eraseLead j = 0 then
      (0 : Multiset ℕ) else {(Function.update F i (F i).eraseLead j).natDegree}) =
      ∑ j : {j // j ≠ i}, if F j = 0 then (0 : Multiset ℕ) else {(F j).natDegree} :=
    Fintype.sum_congr _ _ fun j ↦ by rw [Function.update_of_ne j.2]
  rw [hX]
  refine ⟨_, _, {(F i).natDegree}, by simp, add_comm _ _, add_comm _ _, fun y hy ↦
    ⟨_, Multiset.mem_singleton_self _, ?_⟩⟩
  obtain ⟨h0, rfl⟩ := mem_degreeTerm hy
  exact (eraseLead_natDegree_lt_or_eraseLead_eq_zero (F i)).resolve_right h0

open Classical in
/-- A cover for `F` with `F i` replaced by its truncation is a cover for `F` on a set where the
leading coefficient of `F i` vanishes. -/
theorem HasSignPatternCover.of_update_eraseLead {F : ι → (MvPolynomial σ ℝ)[X]}
    {A : Set (σ → ℝ)} {i : ι} (h : HasSignPatternCover (Function.update F i (F i).eraseLead) A)
    (hA : ∀ a ∈ A, MvPolynomial.eval a (F i).leadingCoeff = 0) : HasSignPatternCover F A := by
  refine h.of_imp fun a ha b hb h ↦ ?_
  have e : ∀ c ∈ A, (fun j ↦ specAt c (Function.update F i (F i).eraseLead j)) =
      fun j ↦ specAt c (F j) := fun c hc ↦ by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, specAt_eraseLead c _ (hA c hc)]
    · rw [Function.update_of_ne hj]
  rwa [e a ha, e b hb] at h

open Classical in
/-- Restricting `A` to where the leading coefficient of a nonzero `F i` does not vanish, when it
vanishes somewhere on `A`, strictly decreases the number of members of `F` whose nonzero leading
coefficient vanishes somewhere on the set. -/
theorem card_filter_leadingCoeff_eq_zero_inter_lt [Fintype ι] {F : ι → (MvPolynomial σ ℝ)[X]}
    {A : Set (σ → ℝ)} {i : ι} (hi : F i ≠ 0) {a₀ : σ → ℝ} (ha₀ : a₀ ∈ A)
    (h₀ : MvPolynomial.eval a₀ (F i).leadingCoeff = 0) :
    (Finset.univ.filter fun j ↦ F j ≠ 0 ∧
      ∃ a ∈ A ∩ {a | MvPolynomial.eval a (F i).leadingCoeff ≠ 0},
        MvPolynomial.eval a (F j).leadingCoeff = 0).card <
      (Finset.univ.filter fun j ↦ F j ≠ 0 ∧ ∃ a ∈ A,
        MvPolynomial.eval a (F j).leadingCoeff = 0).card := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun j hj ↦ ?_).2
    ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, a₀, ha₀, h₀⟩, fun h ↦ ?_⟩)
  · obtain ⟨hj, a, ha, h0⟩ := (Finset.mem_filter.1 hj).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj, a, ha.1, h0⟩
  · obtain ⟨-, a, ha, h0⟩ := (Finset.mem_filter.1 h).2
    exact ha.2 h0

open Classical in
/-- **Hörmander's theorem.** For a finite family `F` of polynomials in one variable with
coefficients polynomial in parameters `a ∈ ℝ^σ`, every semialgebraic `A ⊆ ℝ^σ` is a finite union
of semialgebraic pieces on which the sign pattern of `F(a, ·)` is constant. -/
theorem hasSignPatternCover [Finite ι] (F : ι → (MvPolynomial σ ℝ)[X]) {A : Set (σ → ℝ)}
    (hA : IsSemialgebraic A) : HasSignPatternCover F A := by
  suffices H : ∀ m : Multiset ℕ, ∀ (ι : Type) [Fintype ι] (F : ι → (MvPolynomial σ ℝ)[X]),
      degreeMultiset F = m → ∀ A, IsSemialgebraic A → HasSignPatternCover F A from
    have := Fintype.ofFinite ι
    H _ ι F rfl A hA
  intro m
  induction m using (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction with
  | _ m IH =>
  intro ι _ F hm
  suffices H : ∀ n, ∀ A, IsSemialgebraic A →
      (Finset.univ.filter fun i ↦ F i ≠ 0 ∧ ∃ a ∈ A,
        MvPolynomial.eval a (F i).leadingCoeff = 0).card ≤ n → HasSignPatternCover F A from
    fun A hA ↦ H _ A hA le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro A hA hcard
  by_cases hbad : ∃ i, F i ≠ 0 ∧ ∃ a ∈ A, MvPolynomial.eval a (F i).leadingCoeff = 0
  · obtain ⟨i, hi, a₀, ha₀, h₀⟩ := hbad
    set A₁ := A ∩ {a | MvPolynomial.eval a (F i).leadingCoeff ≠ 0}
    set A₂ := A ∩ {a | MvPolynomial.eval a (F i).leadingCoeff = 0}
    have hA₁ : IsSemialgebraic A₁ := hA.inter (IsSemialgebraic.ne_zero _)
    have hA₂ : IsSemialgebraic A₂ := hA.inter (IsSemialgebraic.zero _)
    have hAeq : A = A₁ ∪ A₂ := by
      ext a
      simp only [A₁, A₂, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hAeq]
    refine HasSignPatternCover.union ?_ ?_
    · exact IHn _ ((card_filter_leadingCoeff_eq_zero_inter_lt hi ha₀ h₀).trans_le hcard) A₁ hA₁
        le_rfl
    · exact (IH _ (hm ▸ degreeMultiset_update_eraseLead_lt hi) ι
        (Function.update F i (F i).eraseLead) rfl A₂ hA₂).of_update_eraseLead fun _ h ↦ h.2
  · push Not at hbad
    by_cases h0 : ∀ i, (F i).natDegree = 0
    · exact HasSignPatternCover.of_natDegree_eq_zero hA h0
    push Not at h0
    obtain ⟨j, hj⟩ := h0
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i ↦ (F i).natDegree)
      ⟨j, Finset.mem_univ j⟩
    have hmax : ∀ i, (F i).natDegree ≤ (F i₀).natDegree := fun i ↦ hi₀ i (Finset.mem_univ i)
    have hpos : 0 < (F i₀).natDegree := (Nat.pos_of_ne_zero hj).trans_le (hmax j)
    exact (IH _ (hm ▸ degreeMultiset_hormanderFamily_lt hpos hmax) _
      (hormanderFamily F i₀) rfl A hA).of_imp fun a ha b hb h ↦
      sameSignPattern_of_hormanderFamily hpos (fun i hi ↦ hbad i hi a ha)
        (fun i hi ↦ hbad i hi b hb) h

end TarskiSeidenberg

/-! ### The projection theorem -/

/-- **Semialgebraic sets are defined by sign conditions.** A semialgebraic set is the set of
points where the signs of finitely many polynomials lie in a given set of sign vectors. -/
theorem IsSemialgebraic.exists_signConditions {τ : Type*} {S : Set (τ → ℝ)}
    (hS : IsSemialgebraic S) : ∃ (κ : Type) (_ : Fintype κ) (P : κ → MvPolynomial τ ℝ)
      (E : Set (κ → SignType)),
      S = {x | (fun k ↦ SignType.sign (MvPolynomial.eval x (P k))) ∈ E} := by
  induction hS with
  | pos p =>
    refine ⟨Unit, inferInstance, fun _ ↦ p, {v | v () = 1}, ?_⟩
    ext x
    simp [sign_eq_one_iff]
  | compl _ ih =>
    obtain ⟨κ, hκ, P, E, rfl⟩ := ih
    exact ⟨κ, hκ, P, Eᶜ, Set.ext fun x ↦ by simp⟩
  | inter _ _ ih₁ ih₂ =>
    obtain ⟨κ₁, _, P₁, E₁, rfl⟩ := ih₁
    obtain ⟨κ₂, _, P₂, E₂, rfl⟩ := ih₂
    refine ⟨κ₁ ⊕ κ₂, inferInstance, Sum.elim P₁ P₂, {v | v ∘ Sum.inl ∈ E₁ ∧ v ∘ Sum.inr ∈ E₂},
      ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rfl

namespace TarskiSeidenberg

/-- Evaluating a polynomial in the variables `Option σ` is evaluating its image in
`(MvPolynomial σ ℝ)[X]` at the parameters `x ∘ some` and the variable `x none`. -/
theorem eval_eq_eval_specAt_optionEquivLeft {σ : Type*} (P : MvPolynomial (Option σ) ℝ)
    (x : Option σ → ℝ) :
    MvPolynomial.eval x P =
      (specAt (x ∘ some) (MvPolynomial.optionEquivLeft ℝ σ P)).eval (x none) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f n hf =>
    cases n with
    | none => simp [hf]
    | some i => simp [hf]

end TarskiSeidenberg

open TarskiSeidenberg in
/-- **The Tarski–Seidenberg theorem.** The projection of a semialgebraic subset of
`ℝ^{Option σ} = ℝ × ℝ^σ` to `ℝ^σ` is semialgebraic. -/
theorem IsSemialgebraic.projection {σ : Type*} {S : Set (Option σ → ℝ)}
    (hS : IsSemialgebraic S) :
    IsSemialgebraic {a : σ → ℝ | ∃ t : ℝ, (fun o ↦ o.elim t a) ∈ S} := by
  obtain ⟨κ, _, P, E, rfl⟩ := hS.exists_signConditions
  set F : κ → (MvPolynomial σ ℝ)[X] := fun k ↦ MvPolynomial.optionEquivLeft ℝ σ (P k)
  have hev : ∀ (a : σ → ℝ) (t : ℝ) (k : κ),
      MvPolynomial.eval (fun o ↦ o.elim t a) (P k) = (specAt a (F k)).eval t := fun a t k ↦
    eval_eq_eval_specAt_optionEquivLeft (P k) _
  obtain ⟨κ', _, C, hC, hU, hP⟩ := hasSignPatternCover F (IsSemialgebraic.univ (σ := σ))
  set T := {a : σ → ℝ | ∃ t : ℝ, (fun o ↦ o.elim t a) ∈
    {x : Option σ → ℝ | (fun k ↦ SignType.sign (MvPolynomial.eval x (P k))) ∈ E}}
  have hT : T = ⋃ j ∈ {j | ∃ a ∈ C j, a ∈ T}, C j := by
    ext a
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨fun ha ↦ ?_, fun ⟨j, ⟨b, hb, t, ht⟩, ha⟩ ↦ ?_⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hU ▸ Set.mem_univ a : a ∈ ⋃ j, C j)
      exact ⟨j, ⟨a, hj, ha⟩, hj⟩
    · simp only [Set.mem_ofPred_eq, hev] at ht
      obtain ⟨t', ht'⟩ := ((hP j b hb a ha).exists_iff
        (fun k ↦ SignType.sign ((specAt b (F k)).eval t))).1 ⟨t, fun _ ↦ rfl⟩
      refine ⟨t', ?_⟩
      simp only [Set.mem_ofPred_eq, hev]
      convert ht using 1
      exact funext ht'
  change IsSemialgebraic T
  rw [hT]
  exact IsSemialgebraic.biUnion (Set.toFinite _) fun j _ ↦ hC j

end MMP
