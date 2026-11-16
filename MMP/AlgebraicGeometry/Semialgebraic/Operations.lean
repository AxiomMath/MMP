module

public import MMP.AlgebraicGeometry.Semialgebraic.TarskiSeidenberg
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Operations on semialgebraic sets

Consequences of the Tarski–Seidenberg theorem (`IsSemialgebraic.projection`): semialgebraic sets
are stable under projections along finitely many coordinates, under the corresponding universal
quantification, under images by polynomial maps between finite-dimensional spaces, and under
topological closure and interior.

## Main results

* `IsSemialgebraic.exists_sumElim`, `IsSemialgebraic.forall_sumElim`: eliminating finitely many
  existentially or universally quantified coordinates.
* `IsSemialgebraic.image_polynomialMap`: images by polynomial maps.
* `IsSemialgebraic.closure`, `IsSemialgebraic.interior`: closure and interior.
* `IsSemialgebraic.eventually_mem_or_eventually_notMem`: along a polynomial curve, membership in
  a semialgebraic set is eventually constant as `t → p⁺`.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], §2.2.
-/

@[expose] public section

open MvPolynomial Topology

namespace MMP

namespace IsSemialgebraic

variable {σ τ : Type*}

/-- Reindexing coordinates along an equivalence preserves and reflects semialgebraicity. -/
theorem preimage_comp_iff_of_equiv (e : τ ≃ σ) {s : Set (τ → ℝ)} :
    IsSemialgebraic ((fun x : σ → ℝ ↦ x ∘ e) ⁻¹' s) ↔ IsSemialgebraic s := by
  refine ⟨fun h ↦ ?_, preimage_comp e⟩
  convert preimage_comp e.symm h using 1
  ext x
  simp [Function.comp_def]

/-- `∃ b : Option α → β, P b` splits into a value at `none` and a function on `α`. -/
theorem _root_.MMP.exists_option_fun {α β : Type*} {P : (Option α → β) → Prop} :
    (∃ b : Option α → β, P b) ↔ ∃ b : α → β, ∃ t : β, P (fun o ↦ o.elim t b) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b ∘ some, b none, ?_⟩
    convert hb using 1
    funext o
    cases o <;> rfl
  · rintro ⟨b, t, h⟩
    exact ⟨_, h⟩

/-- **Elimination of finitely many existential coordinates.** If `S ⊆ ℝ^(σ ⊕ τ)` is
semialgebraic and `τ` is finite, then so is `{a | ∃ b, Sum.elim a b ∈ S}`. -/
theorem exists_sumElim [Finite τ] {S : Set (σ ⊕ τ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {a : σ → ℝ | ∃ b : τ → ℝ, Sum.elim a b ∈ S} := by
  revert σ
  refine Finite.induction_empty_option (P := fun τ ↦ ∀ {σ : Type _} {S : Set (σ ⊕ τ → ℝ)},
    IsSemialgebraic S → IsSemialgebraic {a : σ → ℝ | ∃ b : τ → ℝ, Sum.elim a b ∈ S})
    ?_ ?_ ?_ τ
  · intro α β e h σ S hS
    have hS' : IsSemialgebraic
        ((fun x : σ ⊕ α → ℝ ↦ x ∘ Sum.map id e.symm) ⁻¹' S) := preimage_comp _ hS
    convert h hS' using 1
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b ∘ e, ?_⟩
      convert hb using 1
      funext i
      rcases i with i | i <;> simp
    · rintro ⟨b, hb⟩
      refine ⟨b ∘ e.symm, ?_⟩
      convert hb using 1
      funext i
      rcases i with i | i <;> simp
  · intro σ S hS
    have h := preimage_polynomialMap
      (Sum.elim (fun i ↦ (X i : MvPolynomial σ ℝ)) (fun e : PEmpty ↦ e.elim)) hS
    convert h using 1
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨b, hb⟩
      convert hb using 1
      funext i
      rcases i with i | i
      · simp [polynomialMap]
      · exact i.elim
    · intro h
      refine ⟨fun e ↦ e.elim, ?_⟩
      convert h using 1
      funext i
      rcases i with i | i
      · simp [polynomialMap]
      · exact i.elim
  · intro α _ ih σ S hS
    let g : σ ⊕ Option α → Option (σ ⊕ α) :=
      Sum.elim (fun i ↦ some (Sum.inl i)) (fun o ↦ o.elim none fun j ↦ some (Sum.inr j))
    have h₁ : IsSemialgebraic ((fun x : Option (σ ⊕ α) → ℝ ↦ x ∘ g) ⁻¹' S) :=
      preimage_comp g hS
    convert ih h₁.projection using 1
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [exists_option_fun]
    refine exists_congr fun b ↦ exists_congr fun t ↦ ?_
    apply Eq.to_iff
    congr 1
    funext i
    rcases i with i | (_ | j) <;> rfl

/-- **Elimination of finitely many universal coordinates.** If `S ⊆ ℝ^(σ ⊕ τ)` is
semialgebraic and `τ` is finite, then so is `{a | ∀ b, Sum.elim a b ∈ S}`. -/
theorem forall_sumElim [Finite τ] {S : Set (σ ⊕ τ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {a : σ → ℝ | ∀ b : τ → ℝ, Sum.elim a b ∈ S} := by
  convert (exists_sumElim hS.compl).compl using 1
  ext a
  simp

/-- **Images by polynomial maps.** The image of a semialgebraic `S ⊆ ℝ^σ` under the polynomial
map `polynomialMap φ : ℝ^σ → ℝ^τ` is semialgebraic, for finite `σ` and `τ`. -/
theorem image_polynomialMap [Finite σ] [Finite τ] (φ : τ → MvPolynomial σ ℝ) {S : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) : IsSemialgebraic (polynomialMap φ '' S) := by
  set G : Set (τ ⊕ σ → ℝ) := (fun z ↦ z ∘ Sum.inr) ⁻¹' S ∩
    {z | ∀ i, eval z (X (Sum.inl i) - rename Sum.inr (φ i)) = 0} with hG
  have hGs : IsSemialgebraic G := (preimage_comp _ hS).inter (isSemialgebraic_zeroLocus _)
  convert exists_sumElim hGs using 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, hG, Set.mem_inter_iff, Set.mem_preimage, map_sub,
    eval_X, eval_rename, sub_eq_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, fun i ↦ by simp [Function.comp_def]⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, by simpa using hx, ?_⟩
    funext i
    simpa [Function.comp_def] using (h i).symm

/-- **Closures of semialgebraic sets are semialgebraic.** -/
protected theorem closure [Fintype σ] {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (closure S) := by
  -- `x ∈ closure S ↔ ∀ ε, 0 < ε → ∃ y ∈ S, ∀ i, (x i - y i) ^ 2 < ε`
  have key : ∀ x : σ → ℝ, x ∈ closure S ↔
      ∀ ε : Unit → ℝ, 0 < ε () → ∃ y : σ → ℝ, y ∈ S ∧ ∀ i, (x i - y i) ^ 2 < ε () := by
    intro x
    rw [Metric.mem_closure_iff]
    constructor
    · intro h ε hε
      obtain ⟨y, hy, hxy⟩ := h (Real.sqrt (ε ())) (Real.sqrt_pos.2 hε)
      refine ⟨y, hy, fun i ↦ ?_⟩
      have := (dist_pi_lt_iff (Real.sqrt_pos.2 hε)).1 hxy i
      rw [Real.dist_eq] at this
      calc (x i - y i) ^ 2 = |x i - y i| ^ 2 := (sq_abs _).symm
        _ < Real.sqrt (ε ()) ^ 2 := by gcongr
        _ = ε () := Real.sq_sqrt hε.le
    · intro h ε hε
      obtain ⟨y, hy, hxy⟩ := h (fun _ ↦ ε ^ 2) (by positivity)
      refine ⟨y, hy, (dist_pi_lt_iff hε).2 fun i ↦ ?_⟩
      rw [Real.dist_eq]
      exact abs_lt_of_sq_lt_sq (hxy i) hε.le
  -- the set of `(x, ε, y)` with `y ∈ S` and `(xᵢ - yᵢ)² < ε`
  set T : Set ((σ ⊕ Unit) ⊕ σ → ℝ) := (fun z ↦ z ∘ Sum.inr) ⁻¹' S ∩
    {z | ∀ i, eval z ((X (Sum.inl (Sum.inl i)) - X (Sum.inr i)) ^ 2) <
      eval z (X (Sum.inl (Sum.inr ())))}
  have hT : IsSemialgebraic T := by
    refine (preimage_comp _ hS).inter ?_
    simp only [Set.setOf_forall]
    exact iInter fun i ↦ lt _ _
  -- the set of `(x, ε)` with `0 < ε → ∃ y ...`
  set U : Set (σ ⊕ Unit → ℝ) := {z | eval z (X (Sum.inr ())) ≤ 0} ∪
    {a | ∃ b : σ → ℝ, Sum.elim a b ∈ T}
  have hU' : IsSemialgebraic U := (nonpos _).union (exists_sumElim hT)
  convert forall_sumElim hU' using 1
  ext x
  rw [key]
  simp only [U, T, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
    eval_X, map_pow, map_sub, Sum.elim_inl, Sum.elim_inr]
  refine forall_congr' fun ε ↦ ?_
  rw [imp_iff_not_or, not_lt]
  rfl

/-- **Interiors of semialgebraic sets are semialgebraic.** -/
protected theorem interior [Fintype σ] {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (interior S) := by
  rw [← compl_compl (interior S), ← closure_compl]
  exact hS.compl.closure.compl

/-! ### Semialgebraic sets along polynomial curves -/

/-- Evaluating `P` at the point `((φ i).eval t)ᵢ` is evaluating the one-variable polynomial
`aeval φ P` at `t`. -/
theorem _root_.MMP.eval_polynomial_eval_eq_eval_aeval (φ : σ → Polynomial ℝ)
    (P : MvPolynomial σ ℝ) (t : ℝ) :
    eval (fun i ↦ (φ i).eval t) P = (aeval φ P).eval t :=
  (comp_aeval_apply φ (Polynomial.aeval t) P).symm

/-- Near `p⁺` a real polynomial has constant sign. -/
theorem _root_.MMP.exists_eventually_sign_eval_eq (q : Polynomial ℝ) (p : ℝ) :
    ∃ s : SignType, ∀ᶠ t in 𝓝[>] p, SignType.sign (q.eval t) = s := by
  classical
  by_cases hq : q = 0
  · exact ⟨0, Filter.Eventually.of_forall fun t ↦ by simp [hq]⟩
  set R := (q.roots.toFinset.filter (p < ·))
  set δ := if h : R.Nonempty then R.min' h - p else 1
  have hδ : 0 < δ := by
    simp only [δ]
    split_ifs with h
    · exact sub_pos.2 (Finset.mem_filter.1 (R.min'_mem h)).2
    · exact one_pos
  have hno : ∀ t ∈ Set.Ioo p (p + δ), q.eval t ≠ 0 := by
    rintro t ⟨h1, h2⟩ h0
    have hR : t ∈ R := Finset.mem_filter.2 ⟨by simp [Polynomial.mem_roots hq, h0], h1⟩
    have hne : R.Nonempty := ⟨t, hR⟩
    have := R.min'_le t hR
    simp only [δ, dif_pos hne] at h2
    linarith
  refine ⟨SignType.sign (q.eval (p + δ / 2)), Filter.mem_of_superset
    (Ioo_mem_nhdsGT (show p < p + δ by linarith)) fun t ht ↦ ?_⟩
  refine sign_eval_eq_of_forall_ne_zero q fun x hx ↦ hno x ?_
  rcases Set.mem_uIcc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨ht.1.trans_le h1, by linarith⟩
  · exact ⟨by linarith [ht.1], h2.trans_lt ht.2⟩

/-- **Semialgebraic sets are eventually decided along polynomial curves.** For a semialgebraic
`S ⊆ ℝ^σ` and a polynomial curve `γ`, either `γ(t) ∈ S` for all `t > p` close to `p`, or
`γ(t) ∉ S` for all such `t`. -/
theorem eventually_mem_or_eventually_notMem {S : Set (σ → ℝ)} (hS : IsSemialgebraic S)
    (φ : σ → Polynomial ℝ) (p : ℝ) :
    (∀ᶠ t in 𝓝[>] p, (fun i ↦ (φ i).eval t) ∈ S) ∨
      ∀ᶠ t in 𝓝[>] p, (fun i ↦ (φ i).eval t) ∉ S := by
  induction hS with
  | pos P =>
    obtain ⟨s, hs⟩ := exists_eventually_sign_eval_eq (aeval φ P) p
    simp only [Set.mem_setOf_eq, eval_polynomial_eval_eq_eval_aeval]
    by_cases h1 : s = 1
    · left
      filter_upwards [hs] with t ht
      rwa [h1, sign_eq_one_iff] at ht
    · right
      filter_upwards [hs] with t ht h
      exact h1 (ht ▸ sign_pos h)
  | compl _ ih =>
    simpa only [Set.mem_compl_iff, not_not] using ih.symm
  | inter _ _ ih₁ ih₂ =>
    simp only [Set.mem_inter_iff]
    rcases ih₁ with h₁ | h₁
    · rcases ih₂ with h₂ | h₂
      · exact Or.inl (h₁.and h₂)
      · exact Or.inr (h₂.mono fun t h h' ↦ h h'.2)
    · exact Or.inr (h₁.mono fun t h h' ↦ h h'.1)

end IsSemialgebraic

end MMP
