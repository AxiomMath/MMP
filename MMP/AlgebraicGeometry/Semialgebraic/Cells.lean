module

public import MMP.AlgebraicGeometry.Semialgebraic.TarskiSeidenberg
public import MMP.AlgebraicGeometry.Semialgebraic.ThomLemma
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Continuity of the roots over a set of constant sign pattern

Let `F = (Fᵢ)` be a finite family of real polynomials in one variable `t` whose coefficients
depend on a parameter `a` in a topological space, in such a way that `a ↦ Fᵢ(a, x)` is continuous
for every `x`. Write `Z(a)` for the finite set of zeros of the members `Fᵢ(a, ·)` which are not
the zero polynomial. When the family is closed under `∂/∂t`, the zero set `Z(a)` is lower
semicontinuous: every zero `z` of `Fᵢ(a₀, ·)` is the limit of zeros of `Fⱼ(a, ·)`, `a → a₀`,
where `Fⱼ` is the derivative of `Fᵢ` of order one less than the multiplicity of `z`, which has
a simple zero at `z` and hence changes sign there.

If moreover the sign pattern of `F(a, ·)` (`SameSignPattern`) is constant on a set `C`, then
the number of points of `Z(a)` is constant on `C` and the `j`-th smallest point of `Z(a)` is a
continuous function of `a ∈ C`. These are the continuous root functions of a cylindrical
decomposition: over a cell of a decomposition adapted to Hörmander's sign-pattern cover
(`TarskiSeidenberg.hasSignPatternCover`), the zeros of the family are the graphs of
finitely many continuous functions.

## Main definitions

* `MMP.familyRoots`: the finite set of zeros of the nonzero members of a finite
  family of real polynomials.
* `MMP.familyRootsNth`: its `j`-th smallest point (`0` if there is none).
* `MMP.InFamilyRootsBand`: the `j`-th open interval cut out by these zeros.
* `MMP.derivativeClosure`: the family of all `t`-derivatives of a finite family.

## Main results

* `MMP.SameSignPattern.card_familyRoots_eq`: families with the same sign pattern
  have the same number of zeros.
* `MMP.eventually_exists_mem_familyRoots_dist_lt`: lower semicontinuity of the
  zero set of a family closed under derivation.
* `MMP.continuousWithinAt_familyRootsNth`: the root functions are continuous on
  a set of constant sign pattern.
* `MMP.SameSignPattern.sign_eval_familyRootsNth`,
  `MMP.SameSignPattern.sign_eval_of_inFamilyRootsBand`: the signs of the family on
  the graphs of the root functions and on the bands are constant over such a set.
* `MMP.isSemialgebraic_graph_familyRootsNth`,
  `MMP.isSemialgebraic_setOf_inFamilyRootsBand`: these graphs and bands are
  semialgebraic.

## Implementation notes

The closure of the family under `∂/∂t` is what makes the zeros of even multiplicity move
continuously: such a zero is not detected by a change of sign of the polynomial itself, but by
one of its derivatives. Hörmander's cover can be taken for any finite family, so this costs
nothing: one applies it to the family of all `t`-derivatives of the given polynomials.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], §2.3.
* [L. Hörmander, *The analysis of linear partial differential operators II*][hormander1983],
  Appendix A.2.
-/

@[expose] public section

open Polynomial Filter Topology

namespace MMP

/-! ### The zero set of a finite family -/

section FamilyRoots

variable {ι : Type*} [Fintype ι]

/-- The finite set of zeros of the nonzero members of a finite family of real polynomials. -/
noncomputable def familyRoots (f : ι → ℝ[X]) : Finset ℝ :=
  Finset.univ.biUnion fun i ↦ (f i).roots.toFinset

/-- A point lies in `familyRoots f` iff it is a zero of some nonzero member of `f`. -/
theorem mem_familyRoots {f : ι → ℝ[X]} {x : ℝ} :
    x ∈ familyRoots f ↔ ∃ i, f i ≠ 0 ∧ (f i).eval x = 0 := by
  classical
  simp [familyRoots, mem_roots']

/-- The `j`-th smallest zero of the nonzero members of a finite family of real polynomials,
counting from `0`; it is `0` when there are at most `j` zeros. -/
noncomputable def familyRootsNth (f : ι → ℝ[X]) (j : ℕ) : ℝ :=
  if h : j < (familyRoots f).card then (familyRoots f).orderEmbOfFin rfl ⟨j, h⟩ else 0

/-- `familyRootsNth f j` is `0` when `f` has at most `j` zeros. -/
theorem familyRootsNth_eq_zero_of_card_le {f : ι → ℝ[X]} {j : ℕ} (h : (familyRoots f).card ≤ j) :
    familyRootsNth f j = 0 := by
  rw [familyRootsNth, dite_cond_eq_false (eq_false (not_lt.2 h))]

/-- Below the number of zeros, `familyRootsNth f` is the order embedding of `Fin k` onto
`familyRoots f`. -/
theorem familyRootsNth_eq_orderEmbOfFin {f : ι → ℝ[X]} {k : ℕ} (hk : (familyRoots f).card = k)
    (j : Fin k) : familyRootsNth f j = (familyRoots f).orderEmbOfFin hk j := by
  subst hk
  rw [familyRootsNth, dite_cond_eq_true (eq_true j.2)]

/-- The `j`-th smallest zero lies in `familyRoots f` when there are more than `j` zeros. -/
theorem familyRootsNth_mem {f : ι → ℝ[X]} {j : ℕ} (h : j < (familyRoots f).card) :
    familyRootsNth f j ∈ familyRoots f := by
  rw [familyRootsNth, dite_cond_eq_true (eq_true h)]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- The root function `familyRootsNth f` is strictly increasing below the number of zeros. -/
theorem familyRootsNth_strictMonoOn {f : ι → ℝ[X]} :
    StrictMonoOn (familyRootsNth f) {j | j < (familyRoots f).card} := by
  intro j hj j' hj' hjj'
  simp only [Set.mem_ofPred_eq] at hj hj'
  rw [familyRootsNth, dite_cond_eq_true (eq_true hj), familyRootsNth,
    dite_cond_eq_true (eq_true hj')]
  exact ((familyRoots f).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 hjj')

/-- An order automorphism carrying the signs of `f` to those of `g` carries the zero set of `f`
onto that of `g`. -/
theorem mem_familyRoots_iff_of_sign_eq {f g : ι → ℝ[X]} (ψ : ℝ ≃o ℝ)
    (hψ : ∀ i x, SignType.sign ((f i).eval x) = SignType.sign ((g i).eval (ψ x))) (x : ℝ) :
    x ∈ familyRoots f ↔ ψ x ∈ familyRoots g := by
  have hz : ∀ i, f i = 0 ↔ g i = 0 := fun i ↦
    ⟨fun h ↦ Polynomial.funext fun y ↦ by
      have := hψ i (ψ.symm y)
      rw [h, eval_zero, sign_zero, eq_comm, sign_eq_zero_iff, ψ.apply_symm_apply] at this
      simpa using this,
    fun h ↦ Polynomial.funext fun y ↦ by
      have := hψ i y
      rw [h, eval_zero, sign_zero, sign_eq_zero_iff] at this
      simpa using this⟩
  have he : ∀ i, (f i).eval x = 0 ↔ (g i).eval (ψ x) = 0 := fun i ↦ by
    rw [← sign_eq_zero_iff, hψ i x, sign_eq_zero_iff]
  simp only [mem_familyRoots, Ne, hz, he]

/-- An order automorphism carrying the signs of `f` to those of `g` maps the zero set of `f`
onto that of `g`. -/
theorem familyRoots_eq_map_of_sign_eq {f g : ι → ℝ[X]} (ψ : ℝ ≃o ℝ)
    (hψ : ∀ i x, SignType.sign ((f i).eval x) = SignType.sign ((g i).eval (ψ x))) :
    familyRoots g = (familyRoots f).map ψ.toEquiv.toEmbedding := by
  ext y
  simp only [Finset.mem_map_equiv]
  rw [mem_familyRoots_iff_of_sign_eq ψ hψ]
  simp

/-- Families with the same sign pattern have the same number of zeros. -/
theorem SameSignPattern.card_familyRoots_eq {f g : ι → ℝ[X]} (H : SameSignPattern f g) :
    (familyRoots f).card = (familyRoots g).card := by
  obtain ⟨ψ, hψ⟩ := H
  rw [familyRoots_eq_map_of_sign_eq ψ hψ, Finset.card_map]

end FamilyRoots

/-! ### Zeros of a polynomial and its derivatives -/

/-- Below its multiplicity, each derivative lowers the multiplicity of a zero by one. -/
theorem rootMultiplicity_iterate_derivative {p : ℝ[X]} {z : ℝ} {n : ℕ}
    (hn : n < rootMultiplicity z p) :
    rootMultiplicity z (derivative^[n] p) = rootMultiplicity z p - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    have hroot : (derivative^[n] p).IsRoot z :=
      ((rootMultiplicity_pos' ).1 (by omega)).2
    rw [Function.iterate_succ_apply', derivative_rootMultiplicity_of_root hroot, ih]
    omega

/-- A real polynomial with a simple zero at `z` changes sign there. -/
theorem exists_mul_eval_neg_of_rootMultiplicity_eq_one {p : ℝ[X]} {z : ℝ}
    (hp : rootMultiplicity z p = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₁ x₂, z - ε < x₁ ∧ x₁ < z ∧ z < x₂ ∧ x₂ < z + ε ∧ p.eval x₁ * p.eval x₂ < 0 := by
  have hp0 : p ≠ 0 := fun h ↦ by simp [h] at hp
  have hpq := pow_mul_divByMonic_rootMultiplicity_eq p z
  have hq := eval_divByMonic_pow_rootMultiplicity_ne_zero z hp0
  generalize p /ₘ (X - C z) ^ rootMultiplicity z p = q at hpq hq
  rw [hp, pow_one] at hpq
  have hev : ∀ᶠ x in 𝓝 z, 0 < q.eval x * q.eval z :=
    continuousAt_const.eventually_lt (q.continuous.mul continuous_const).continuousAt
      (mul_self_pos.2 hq)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨h, hh, hhm⟩ := exists_between (lt_min hε hδ)
  rw [lt_min_iff] at hhm
  have h₁ := hball (y := z - h) (by simp [Real.dist_eq, abs_of_pos hh, hhm.2])
  have h₂ := hball (y := z + h) (by simp [Real.dist_eq, abs_of_pos hh, hhm.2])
  refine ⟨z - h, z + h, by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [← hpq, eval_mul, eval_mul]
  simp only [eval_sub, eval_X, eval_C, sub_sub_cancel_left, add_sub_cancel_left]
  have hz2 : 0 < q.eval z * q.eval z := mul_self_pos.2 hq
  have : 0 < (q.eval (z - h) * q.eval z) * (q.eval (z + h) * q.eval z) := mul_pos h₁ h₂
  nlinarith [mul_pos hh hh]

/-! ### Lower semicontinuity of the zero set -/

section Continuity

variable {T : Type*} [TopologicalSpace T] {ι : Type*} [Fintype ι] {F : ι → T → ℝ[X]}

omit [TopologicalSpace T] [Fintype ι] in
/-- In a family closed under derivation, so are its iterated derivatives. -/
theorem exists_eq_iterate_derivative (hder : ∀ i, ∃ j, ∀ a, F j a = derivative (F i a))
    (i : ι) (n : ℕ) : ∃ j, ∀ a, F j a = derivative^[n] (F i a) := by
  induction n with
  | zero => exact ⟨i, fun _ ↦ rfl⟩
  | succ n ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨j', hj'⟩ := hder j
    exact ⟨j', fun a ↦ by rw [hj', hj, Function.iterate_succ_apply']⟩

/-- **Lower semicontinuity of the zero set.** For a finite family of real polynomials `F(a, ·)`
closed under derivation, with `a ↦ Fᵢ(a, x)` continuous at `a₀` for every `x`, every zero of
`F(a₀, ·)` is the limit of zeros of `F(a, ·)` as `a → a₀`. -/
theorem eventually_exists_mem_familyRoots_dist_lt {a₀ : T}
    (hcont : ∀ i x, ContinuousAt (fun a ↦ (F i a).eval x) a₀)
    (hder : ∀ i, ∃ j, ∀ a, F j a = derivative (F i a))
    {z : ℝ} (hz : z ∈ familyRoots fun i ↦ F i a₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in 𝓝 a₀, ∃ w ∈ familyRoots (fun i ↦ F i a), |w - z| < ε := by
  obtain ⟨i, hi0, hiz⟩ := mem_familyRoots.1 hz
  set m := rootMultiplicity z (F i a₀)
  have hm : 0 < m := (rootMultiplicity_pos hi0).2 hiz
  obtain ⟨j, hj⟩ := exists_eq_iterate_derivative hder i (m - 1)
  have hj1 : rootMultiplicity z (F j a₀) = 1 := by
    rw [hj, rootMultiplicity_iterate_derivative (by omega)]
    omega
  obtain ⟨x₁, x₂, h₁, h₁', h₂', h₂, hneg⟩ := exists_mul_eval_neg_of_rootMultiplicity_eq_one hj1 hε
  have hev : ∀ᶠ a in 𝓝 a₀, (F j a).eval x₁ * (F j a).eval x₂ < 0 :=
    ((hcont j x₁).mul (hcont j x₂)).eventually_lt continuousAt_const hneg
  filter_upwards [hev] with a ha
  have hsign : SignType.sign ((F j a).eval x₁) ≠ SignType.sign ((F j a).eval x₂) := by
    rcases mul_neg_iff.1 ha with ⟨hp, hn⟩ | ⟨hn, hp⟩
    · rw [sign_pos hp, sign_neg hn]
      decide
    · rw [sign_neg hn, sign_pos hp]
      decide
  obtain ⟨w, hw, hw0⟩ := exists_mem_uIcc_eval_eq_zero _ hsign
  have hne : F j a ≠ 0 := fun h ↦ by simp [h] at ha
  refine ⟨w, mem_familyRoots.2 ⟨j, hne, hw0⟩, ?_⟩
  rw [Set.uIcc_of_le (by linarith)] at hw
  rw [abs_lt]
  constructor <;> linarith [hw.1, hw.2]

/-- **Continuity of the root functions.** Let `F(a, ·)` be a finite family of real polynomials
closed under derivation, with `a ↦ Fᵢ(a, x)` continuous for every `x`, whose sign pattern is
constant on `C`. Then for every `j` the `j`-th smallest zero of `F(a, ·)` is a continuous
function of `a ∈ C`. -/
theorem continuousWithinAt_familyRootsNth {C : Set T}
    (hC : ∀ a ∈ C, ∀ b ∈ C, SameSignPattern (fun i ↦ F i a) (fun i ↦ F i b))
    {a₀ : T} (ha₀ : a₀ ∈ C)
    (hcont : ∀ i x, ContinuousAt (fun a ↦ (F i a).eval x) a₀)
    (hder : ∀ i, ∃ j, ∀ a, F j a = derivative (F i a)) (j : ℕ) :
    ContinuousWithinAt (fun a ↦ familyRootsNth (fun i ↦ F i a) j) C a₀ := by
  classical
  set s₀ := familyRoots fun i ↦ F i a₀
  set k := s₀.card
  have hcard : ∀ a ∈ C, (familyRoots fun i ↦ F i a).card = k := fun a ha ↦
    (hC a ha a₀ ha₀).card_familyRoots_eq
  by_cases hjk : k ≤ j
  · exact (continuousWithinAt_const (b := (0 : ℝ))).congr
      (fun a ha ↦ familyRootsNth_eq_zero_of_card_le (hcard a ha ▸ hjk)) (familyRootsNth_eq_zero_of_card_le hjk)
  push Not at hjk
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ε ∧ ∀ z ∈ s₀, ∀ z' ∈ s₀, z < z' → 2 * δ < z' - z := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (Iio_mem_nhds hε)) ?_
    rw [eventually_all_finset]
    intro z _
    rw [eventually_all_finset]
    intro z' _
    by_cases hzz : z < z'
    · have : ∀ᶠ δ in 𝓝 (0 : ℝ), 2 * δ < z' - z :=
        (continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const
          (by simpa using hzz)
      filter_upwards [nhdsWithin_le_nhds this] with δ hδ _ using hδ
    · exact Eventually.of_forall fun _ h ↦ absurd h hzz
  obtain ⟨δ, ⟨hδε, hgap⟩, hδ0⟩ := (hδ.and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ0
  have hnear : ∀ᶠ a in 𝓝 a₀, ∀ z ∈ s₀, ∃ w ∈ familyRoots (fun i ↦ F i a), |w - z| < δ := by
    rw [eventually_all_finset]
    exact fun z hz ↦ eventually_exists_mem_familyRoots_dist_lt hcont hder hz hδ0
  filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with a ha haC
  choose w hw hwz using ha
  set e₀ := s₀.orderEmbOfFin rfl
  let g : Fin k → ℝ := fun i ↦ w (e₀ i) (s₀.orderEmbOfFin_mem rfl i)
  have hg : StrictMono g := fun i i' hii' ↦ by
    have hgap' := hgap _ (s₀.orderEmbOfFin_mem rfl i) _ (s₀.orderEmbOfFin_mem rfl i')
      (e₀.strictMono hii')
    have h₁ := hwz _ (s₀.orderEmbOfFin_mem rfl i)
    have h₂ := hwz _ (s₀.orderEmbOfFin_mem rfl i')
    rw [abs_lt] at h₁ h₂
    simp only [g]
    linarith [h₁.2, h₂.1]
  have hgeq := Finset.orderEmbOfFin_unique (hcard a haC) (fun i ↦ hw _ _) hg
  have hja : familyRootsNth (fun i ↦ F i a) j = g ⟨j, hjk⟩ :=
    (familyRootsNth_eq_orderEmbOfFin (hcard a haC) ⟨j, hjk⟩).trans (congrFun hgeq _).symm
  have hj₀ : familyRootsNth (fun i ↦ F i a₀) j = e₀ ⟨j, hjk⟩ :=
    familyRootsNth_eq_orderEmbOfFin rfl ⟨j, hjk⟩
  rw [hja, hj₀, Real.dist_eq]
  exact (hwz _ _).trans hδε

/-- The root functions are continuous on a set of constant sign pattern. -/
theorem continuousOn_familyRootsNth {C : Set T}
    (hC : ∀ a ∈ C, ∀ b ∈ C, SameSignPattern (fun i ↦ F i a) (fun i ↦ F i b))
    (hcont : ∀ i x, Continuous (fun a ↦ (F i a).eval x))
    (hder : ∀ i, ∃ j, ∀ a, F j a = derivative (F i a)) (j : ℕ) :
    ContinuousOn (fun a ↦ familyRootsNth (fun i ↦ F i a) j) C := fun _ ha ↦
  continuousWithinAt_familyRootsNth hC ha (fun i x ↦ (hcont i x).continuousAt) hder j

end Continuity

/-! ### Root functions and order automorphisms -/

section Transport

variable {ι : Type*} [Fintype ι]

/-- An order automorphism carrying the signs of `f` to those of `g` carries the `j`-th zero of
`f` to the `j`-th zero of `g`. -/
theorem familyRootsNth_eq_of_sign_eq {f g : ι → ℝ[X]} (ψ : ℝ ≃o ℝ)
    (hψ : ∀ i x, SignType.sign ((f i).eval x) = SignType.sign ((g i).eval (ψ x))) {j : ℕ}
    (hj : j < (familyRoots f).card) : ψ (familyRootsNth f j) = familyRootsNth g j := by
  have hcard : (familyRoots g).card = (familyRoots f).card :=
    (SameSignPattern.card_familyRoots_eq ⟨ψ, hψ⟩).symm
  have hu := Finset.orderEmbOfFin_unique hcard
    (f := fun i ↦ ψ ((familyRoots f).orderEmbOfFin rfl i))
    (fun i ↦ (mem_familyRoots_iff_of_sign_eq ψ hψ _).1 (Finset.orderEmbOfFin_mem _ _ _))
    (ψ.strictMono.comp ((familyRoots f).orderEmbOfFin rfl).strictMono)
  rw [familyRootsNth_eq_orderEmbOfFin rfl ⟨j, hj⟩,
    familyRootsNth_eq_orderEmbOfFin hcard ⟨j, hj⟩, ← hu]

/-- Families with the same sign pattern take the same signs at their `j`-th zeros. -/
theorem SameSignPattern.sign_eval_familyRootsNth {f g : ι → ℝ[X]} (H : SameSignPattern f g)
    (i : ι) {j : ℕ} (hj : j < (familyRoots f).card) :
    SignType.sign ((f i).eval (familyRootsNth f j)) =
      SignType.sign ((g i).eval (familyRootsNth g j)) := by
  obtain ⟨ψ, hψ⟩ := H
  rw [hψ i, familyRootsNth_eq_of_sign_eq ψ hψ hj]

/-- `t` lies in the `j`-th open interval cut out of `ℝ` by the zeros of `f`: it is not a zero, and
exactly `j` zeros lie below it. -/
def InFamilyRootsBand (f : ι → ℝ[X]) (j : ℕ) (t : ℝ) : Prop :=
  t ∉ familyRoots f ∧ ((familyRoots f).filter (· < t)).card = j

/-- Two points of the same band have the same zeros below them. -/
theorem InFamilyRootsBand.lt_iff_lt {f : ι → ℝ[X]} {j : ℕ} {t t' : ℝ}
    (ht : InFamilyRootsBand f j t) (ht' : InFamilyRootsBand f j t') {z : ℝ}
    (hz : z ∈ familyRoots f) : z < t ↔ z < t' := by
  classical
  have key : ∀ {t t'}, InFamilyRootsBand f j t → InFamilyRootsBand f j t' → z < t → z < t' :=
    fun {t t'} ht ht' hzt ↦ by
      by_contra hzt'
      push Not at hzt'
      have hsub : (familyRoots f).filter (· < t') ⊂ (familyRoots f).filter (· < t) := by
        refine Finset.ssubset_iff_of_subset (fun x hx ↦ ?_) |>.2 ⟨z, ?_, ?_⟩
        · simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.trans_le (hzt'.trans hzt.le)⟩
        · simp [hz, hzt]
        · simp [hzt']
      simpa [ht.2, ht'.2] using Finset.card_lt_card hsub
  exact ⟨key ht ht', key ht' ht⟩

/-- Every member of the family keeps one sign on a band. -/
theorem InFamilyRootsBand.sign_eval_eq {f : ι → ℝ[X]} {j : ℕ} {t t' : ℝ}
    (ht : InFamilyRootsBand f j t) (ht' : InFamilyRootsBand f j t') (i : ι) :
    SignType.sign ((f i).eval t) = SignType.sign ((f i).eval t') := by
  by_cases hi : f i = 0
  · simp [hi]
  refine sign_eval_eq_of_forall_ne_zero _ fun x hx hx0 ↦ ?_
  have hxZ : x ∈ familyRoots f := mem_familyRoots.2 ⟨i, hi, hx0⟩
  have hxt : x ≠ t := fun h ↦ ht.1 (h ▸ hxZ)
  have hxt' : x ≠ t' := fun h ↦ ht'.1 (h ▸ hxZ)
  have hiff := ht.lt_iff_lt ht' hxZ
  rcases Set.mem_uIcc.1 hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact absurd (hiff.2 (lt_of_le_of_ne h₂ hxt')) (not_lt.2 h₁)
  · exact absurd (hiff.1 (lt_of_le_of_ne h₂ hxt)) (not_lt.2 h₁)

/-- An order automorphism carrying the signs of `f` to those of `g` carries the bands of `f` to
the bands of `g`. -/
theorem inFamilyRootsBand_iff_of_sign_eq {f g : ι → ℝ[X]} (ψ : ℝ ≃o ℝ)
    (hψ : ∀ i x, SignType.sign ((f i).eval x) = SignType.sign ((g i).eval (ψ x))) (j : ℕ)
    (t : ℝ) : InFamilyRootsBand f j t ↔ InFamilyRootsBand g j (ψ t) := by
  classical
  have hfilt : (familyRoots g).filter (· < ψ t) =
      ((familyRoots f).filter (· < t)).map ψ.toEquiv.toEmbedding := by
    rw [familyRoots_eq_map_of_sign_eq ψ hψ, Finset.filter_map]
    congr 1
    ext x
    simp
  rw [InFamilyRootsBand, InFamilyRootsBand, hfilt, Finset.card_map,
    mem_familyRoots_iff_of_sign_eq ψ hψ]

/-- Families with the same sign pattern take the same signs on corresponding bands. -/
theorem SameSignPattern.sign_eval_of_inFamilyRootsBand {f g : ι → ℝ[X]}
    (H : SameSignPattern f g) {j : ℕ} {t t' : ℝ} (ht : InFamilyRootsBand f j t)
    (ht' : InFamilyRootsBand g j t') (i : ι) :
    SignType.sign ((f i).eval t) = SignType.sign ((g i).eval t') := by
  obtain ⟨ψ, hψ⟩ := H
  rw [hψ i]
  exact ((inFamilyRootsBand_iff_of_sign_eq ψ hψ j t).1 ht).sign_eval_eq ht' i

/-- If `t` lies above the `(j - 1)`-th zero of `f` and at or below the `j`-th, exactly `j` zeros
of `f` lie below `t`. -/
theorem card_filter_lt_of_familyRootsNth {f : ι → ℝ[X]} {j : ℕ} (hj : j ≤ (familyRoots f).card)
    {t : ℝ} (h₁ : ∀ _ : 0 < j, familyRootsNth f (j - 1) < t)
    (h₂ : j < (familyRoots f).card → t ≤ familyRootsNth f j) :
    ((familyRoots f).filter (· < t)).card = j := by
  classical
  set s := familyRoots f
  set e := s.orderEmbOfFin rfl
  have hiff : ∀ i : Fin s.card, e i < t ↔ (i : ℕ) < j := fun i ↦ by
    refine ⟨fun hi ↦ ?_, fun hij ↦ ?_⟩
    · by_contra hij
      push Not at hij
      have := h₂ (lt_of_le_of_lt hij i.2)
      rw [familyRootsNth_eq_orderEmbOfFin rfl ⟨j, lt_of_le_of_lt hij i.2⟩] at this
      exact absurd (hi.trans_le this) (not_lt.2 (e.monotone (Fin.mk_le_mk.2 hij)))
    · have := h₁ (by omega)
      rw [familyRootsNth_eq_orderEmbOfFin rfl
        ⟨j - 1, lt_of_lt_of_le (Nat.sub_lt (by omega) one_pos) hj⟩] at this
      refine lt_of_le_of_lt (e.monotone ?_) this
      rw [Fin.le_iff_val_le_val]
      dsimp only
      omega
  rw [← s.map_orderEmbOfFin_univ rfl, Finset.filter_map, Finset.card_map]
  simp [Function.comp_def, show ∀ i, s.orderEmbOfFin rfl i < t ↔ (i : ℕ) < j from hiff,
    Fin.card_filter_val_lt, hj]

/-- A point strictly between the `(j - 1)`-th and the `j`-th zero lies in the `j`-th band. -/
theorem inFamilyRootsBand_of_lt {f : ι → ℝ[X]} {j : ℕ} (hj : j ≤ (familyRoots f).card)
    {t : ℝ} (h₁ : ∀ _ : 0 < j, familyRootsNth f (j - 1) < t)
    (h₂ : j < (familyRoots f).card → t < familyRootsNth f j) : InFamilyRootsBand f j t := by
  refine ⟨fun ht ↦ ?_, card_filter_lt_of_familyRootsNth hj h₁ fun h ↦ (h₂ h).le⟩
  have : t ∈ Set.range ((familyRoots f).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact ht
  obtain ⟨i, hi⟩ := this
  rcases lt_or_ge (i : ℕ) j with hij | hij
  · have := h₁ (by omega)
    rw [familyRootsNth_eq_orderEmbOfFin rfl ⟨j - 1, by omega⟩, ← hi] at this
    exact absurd this (not_lt.2 (OrderEmbedding.monotone _ (Fin.mk_le_mk.2 (by omega))))
  · have := h₂ (lt_of_le_of_lt hij i.2)
    rw [familyRootsNth_eq_orderEmbOfFin rfl ⟨j, lt_of_le_of_lt hij i.2⟩, ← hi] at this
    exact absurd this (not_lt.2 (OrderEmbedding.monotone _ (Fin.mk_le_mk.2 hij)))

/-- A band is an interval. -/
theorem ordConnected_setOf_inFamilyRootsBand (f : ι → ℝ[X]) (j : ℕ) :
    {t | InFamilyRootsBand f j t}.OrdConnected := by
  refine Set.ordConnected_def.2 fun t ht t' ht' s hs ↦ ?_
  have hnot : s ∉ familyRoots f := fun hsZ ↦ by
    rcases eq_or_lt_of_le hs.1 with rfl | h1
    · exact ht.1 hsZ
    rcases eq_or_lt_of_le hs.2 with rfl | h2
    · exact ht'.1 hsZ
    exact absurd ((ht.lt_iff_lt ht' hsZ).2 h2) (not_lt.2 h1.le)
  refine ⟨hnot, ?_⟩
  rw [← (show InFamilyRootsBand f j t from ht).2]
  congr 1
  ext z
  simp only [Finset.mem_filter]
  refine and_congr_right fun hz ↦ ⟨fun h ↦ ?_, fun h ↦ h.trans_le hs.1⟩
  rcases lt_or_ge z t with hzt | hzt
  · exact hzt
  · exact absurd ((ht.lt_iff_lt ht' hz).2 (h.trans_le hs.2)) (not_lt.2 hzt)

/-- A band is open. -/
theorem isOpen_setOf_inFamilyRootsBand (f : ι → ℝ[X]) (j : ℕ) :
    IsOpen {t | InFamilyRootsBand f j t} := by
  refine Metric.isOpen_iff.2 fun t ht ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
    (familyRoots f).finite_toSet.isClosed.isOpen_compl t ht.1
  refine ⟨ε, hε, fun t' ht' ↦ ⟨hball ht', ?_⟩⟩
  rw [← (show InFamilyRootsBand f j t from ht).2]
  congr 1
  ext z
  simp only [Finset.mem_filter]
  refine and_congr_right fun hz ↦ ?_
  have hzb : z ∉ Metric.ball t ε := fun h ↦ hball h hz
  rw [Metric.mem_ball, Real.dist_eq, not_lt] at hzb
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht'
  constructor <;> intro h <;> by_contra h' <;> push Not at h' <;>
    rcases abs_cases (z - t) with h₁ | h₁ <;> linarith

end Transport

/-! ### Graphs and bands over a set of constant sign pattern -/

section Semialgebraic

open TarskiSeidenberg

variable {σ ι : Type*} [Fintype ι] {P : ι → (MvPolynomial σ ℝ)[X]}

/-- A zero of a member of a family closed under derivation is determined by the signs of the
family at it. -/
theorem eq_of_sign_eval_eq_of_mem_familyRoots {f : ι → ℝ[X]}
    (hder : ∀ i, ∃ j, f j = derivative (f i)) {t t' : ℝ} (ht : t ∈ familyRoots f)
    (h : ∀ i, SignType.sign ((f i).eval t') = SignType.sign ((f i).eval t)) : t' = t := by
  obtain ⟨i, hi, hit⟩ := mem_familyRoots.1 ht
  have hS := ordConnected_setOf_sign_eval_eq hder fun i ↦ SignType.sign ((f i).eval t)
  have hroot : ∀ s ∈ Set.uIcc t t', (f i).eval s = 0 := fun s hs ↦ by
    have := hS.uIcc_subset (x := t) (y := t') (fun _ ↦ rfl) h hs
    have := this i
    rwa [hit, sign_zero, sign_eq_zero_iff] at this
  by_contra hne
  have hinf : (Set.uIcc t t').Infinite := Set.Icc_infinite (inf_lt_sup.2 fun h ↦ hne h.symm)
  exact hinf (((f i).roots.toFinset.finite_toSet).subset fun s hs ↦ by
    simpa [mem_roots', hi] using hroot s hs)

/-- In a family closed under derivation, a point with the same signs as a point of a band lies in
that band. -/
theorem InFamilyRootsBand.of_sign_eval_eq {f : ι → ℝ[X]}
    (hder : ∀ i, ∃ j, f j = derivative (f i)) {j : ℕ} {t t' : ℝ} (ht : InFamilyRootsBand f j t)
    (h : ∀ i, SignType.sign ((f i).eval t') = SignType.sign ((f i).eval t)) :
    InFamilyRootsBand f j t' := by
  have hS := ordConnected_setOf_sign_eval_eq hder fun i ↦ SignType.sign ((f i).eval t)
  have hnot : ∀ z ∈ Set.uIcc t t', z ∉ familyRoots f := fun z hz hzZ ↦ by
    obtain ⟨i, hi, hiz⟩ := mem_familyRoots.1 hzZ
    have h₁ := hS.uIcc_subset (x := t) (y := t') (fun _ ↦ rfl) h hz i
    rw [hiz, sign_zero, eq_comm, sign_eq_zero_iff] at h₁
    exact ht.1 (mem_familyRoots.2 ⟨i, hi, h₁⟩)
  refine ⟨hnot _ Set.right_mem_uIcc, ?_⟩
  rw [← ht.2]
  congr 1
  ext z
  simp only [Finset.mem_filter]
  refine and_congr_right fun hz ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · by_contra h''
    push Not at h''
    exact hnot z (Set.mem_uIcc.2 (Or.inl ⟨h'', h'.le⟩)) hz
  · by_contra h''
    push Not at h''
    exact hnot z (Set.mem_uIcc.2 (Or.inr ⟨h'', h'.le⟩)) hz

omit [Fintype ι] in
/-- If the family `P` is closed under `t`-derivation, so is each of its specialisations. -/
theorem exists_specAt_eq_derivative_specAt (hder : ∀ i, ∃ j, P j = derivative (P i))
    (a : σ → ℝ) : ∀ i, ∃ j, specAt a (P j) = derivative (specAt a (P i)) := fun i ↦ by
  obtain ⟨j, hj⟩ := hder i
  exact ⟨j, by rw [hj, specAt_derivative]⟩

/-- The polynomial `Q` read in the variables `Option σ`, `none` being the variable `t`. -/
private theorem eval_optionEquivLeft_symm (Q : (MvPolynomial σ ℝ)[X]) (x : Option σ → ℝ) :
    MvPolynomial.eval x ((MvPolynomial.optionEquivLeft ℝ σ).symm Q) =
      (specAt (x ∘ some) Q).eval (x none) := by
  rw [eval_eq_eval_specAt_optionEquivLeft, AlgEquiv.apply_symm_apply]

omit [Fintype ι] in
/-- The set of `(a, t)`, `a ∈ C`, at which the family `P(a, t)` has the signs `ε`, is
semialgebraic. -/
theorem isSemialgebraic_setOf_sign_specAt [Finite ι] {C : Set (σ → ℝ)} (hC : IsSemialgebraic C)
    (ε : ι → SignType) :
    IsSemialgebraic {x : Option σ → ℝ | x ∘ some ∈ C ∧
      ∀ i, SignType.sign ((specAt (x ∘ some) (P i)).eval (x none)) = ε i} := by
  have h1 := IsSemialgebraic.preimage_comp (R := ℝ) some hC
  have h2 := IsSemialgebraic.iInter fun i ↦
    IsSemialgebraic.sign_eq ((MvPolynomial.optionEquivLeft ℝ σ).symm (P i)) (ε i)
  convert h1.inter h2 using 1
  ext x
  simp [eval_optionEquivLeft_symm]

/-- **Graphs of root functions are semialgebraic.** Over a semialgebraic set `C` on which the
sign pattern of a family closed under derivation is constant, the graph of the `j`-th root
function is semialgebraic. -/
theorem isSemialgebraic_graph_familyRootsNth (hder : ∀ i, ∃ j, P j = derivative (P i))
    {C : Set (σ → ℝ)} (hC : IsSemialgebraic C)
    (hpat : ∀ a ∈ C, ∀ b ∈ C, SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i)))
    (j : ℕ) :
    IsSemialgebraic {x : Option σ → ℝ | x ∘ some ∈ C ∧
      x none = familyRootsNth (fun i ↦ specAt (x ∘ some) (P i)) j} := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simpa using (IsSemialgebraic.empty (σ := Option σ) (R := ℝ))
  set k := (familyRoots fun i ↦ specAt a₀ (P i)).card
  have hcard : ∀ a ∈ C, (familyRoots fun i ↦ specAt a (P i)).card = k := fun a ha ↦
    (hpat a ha a₀ ha₀).card_familyRoots_eq
  by_cases hjk : k ≤ j
  · have h1 := IsSemialgebraic.preimage_comp (R := ℝ) some hC
    have h2 := IsSemialgebraic.zero (MvPolynomial.X (R := ℝ) (none : Option σ))
    convert h1.inter h2 using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, MvPolynomial.eval_X]
    exact ⟨fun ⟨h, hx⟩ ↦ ⟨h, hx.trans (familyRootsNth_eq_zero_of_card_le (hcard _ h ▸ hjk))⟩,
      fun ⟨h, hx⟩ ↦ ⟨h, hx.trans (familyRootsNth_eq_zero_of_card_le (hcard _ h ▸ hjk)).symm⟩⟩
  push Not at hjk
  convert isSemialgebraic_setOf_sign_specAt (P := P) hC
    (fun i ↦ SignType.sign ((specAt a₀ (P i)).eval (familyRootsNth (fun i ↦ specAt a₀ (P i)) j)))
    using 1
  ext x
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun hx ↦ ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rw [h]
    exact (hpat _ hx a₀ ha₀).sign_eval_familyRootsNth i (hcard _ hx ▸ hjk)
  · refine eq_of_sign_eval_eq_of_mem_familyRoots (exists_specAt_eq_derivative_specAt hder _)
      (familyRootsNth_mem (hcard _ hx ▸ hjk)) fun i ↦ ?_
    rw [h i]
    exact ((hpat _ hx a₀ ha₀).sign_eval_familyRootsNth i (hcard _ hx ▸ hjk)).symm

/-- **Bands between root functions are semialgebraic.** Over a semialgebraic set `C` on which
the sign pattern of a family closed under derivation is constant, the set of `(a, t)` with `t` in
the `j`-th band cut out by the zeros of `P(a, ·)` is semialgebraic. -/
theorem isSemialgebraic_setOf_inFamilyRootsBand (hder : ∀ i, ∃ j, P j = derivative (P i))
    {C : Set (σ → ℝ)} (hC : IsSemialgebraic C)
    (hpat : ∀ a ∈ C, ∀ b ∈ C, SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i)))
    (j : ℕ) :
    IsSemialgebraic {x : Option σ → ℝ | x ∘ some ∈ C ∧
      InFamilyRootsBand (fun i ↦ specAt (x ∘ some) (P i)) j (x none)} := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simpa using (IsSemialgebraic.empty (σ := Option σ) (R := ℝ))
  set E : Set (ι → SignType) := {ε | ∃ s, InFamilyRootsBand (fun i ↦ specAt a₀ (P i)) j s ∧
    ∀ i, SignType.sign ((specAt a₀ (P i)).eval s) = ε i}
  have hE : {x : Option σ → ℝ | x ∘ some ∈ C ∧
      InFamilyRootsBand (fun i ↦ specAt (x ∘ some) (P i)) j (x none)} =
      ⋃ ε ∈ E, {x : Option σ → ℝ | x ∘ some ∈ C ∧
        ∀ i, SignType.sign ((specAt (x ∘ some) (P i)).eval (x none)) = ε i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, E]
    constructor
    · rintro ⟨hx, hband⟩
      obtain ⟨ψ, hψ⟩ := hpat _ hx a₀ ha₀
      exact ⟨_, ⟨ψ (x none), (inFamilyRootsBand_iff_of_sign_eq ψ hψ j _).1 hband,
        fun i ↦ (hψ i _).symm⟩, hx, fun _ ↦ rfl⟩
    · rintro ⟨ε, ⟨s₀, hs₀, hsε⟩, hx, hxε⟩
      obtain ⟨ψ, hψ⟩ := hpat a₀ ha₀ _ hx
      exact ⟨hx, ((inFamilyRootsBand_iff_of_sign_eq ψ hψ j s₀).1 hs₀).of_sign_eval_eq
        (exists_specAt_eq_derivative_specAt hder _)
        fun i ↦ (hxε i).trans ((hsε i).symm.trans (hψ i s₀))⟩
  rw [hE]
  exact IsSemialgebraic.biUnion (Set.toFinite _) fun ε _ ↦ isSemialgebraic_setOf_sign_specAt hC ε

/-- The value of a specialised polynomial at a fixed point is continuous in the parameters. -/
theorem continuous_eval_specAt (Q : (MvPolynomial σ ℝ)[X]) (x : ℝ) :
    Continuous fun a : σ → ℝ ↦ (specAt a Q).eval x := by
  simp only [coe_mapRingHom, eval_map, eval₂_eq_sum, Polynomial.sum_def]
  exact continuous_finsetSum _ fun n _ ↦ (MvPolynomial.continuous_eval _).mul continuous_const

/-- The family of all `t`-derivatives of a finite family, indexed by the member and the order of
derivation up to one more than the maximal degree. -/
noncomputable def derivativeClosure (P : ι → (MvPolynomial σ ℝ)[X]) :
    ι × Fin (Finset.univ.sup (fun i ↦ (P i).natDegree) + 2) → (MvPolynomial σ ℝ)[X] :=
  fun p ↦ derivative^[p.2] (P p.1)

/-- The family `derivativeClosure P` is closed under `t`-derivation. -/
theorem derivativeClosure_derivative_closed (P : ι → (MvPolynomial σ ℝ)[X]) :
    ∀ p, ∃ q, derivativeClosure P q = derivative (derivativeClosure P p) := by
  rintro ⟨i, n⟩
  by_cases hn : (n : ℕ) + 1 < Finset.univ.sup (fun i ↦ (P i).natDegree) + 2
  · exact ⟨(i, ⟨n + 1, hn⟩), by simp [derivativeClosure, Function.iterate_succ_apply']⟩
  · refine ⟨(i, n), ?_⟩
    have hdeg : (P i).natDegree < n := by
      have := Finset.le_sup (f := fun i ↦ (P i).natDegree) (Finset.mem_univ i)
      omega
    simp only [derivativeClosure, iterate_derivative_eq_zero hdeg, derivative_zero]

/-- The member of `derivativeClosure P` of order `0` at `i` is `P i`. -/
theorem derivativeClosure_zero (P : ι → (MvPolynomial σ ℝ)[X]) (i : ι) :
    derivativeClosure P (i, 0) = P i := rfl

end Semialgebraic

end MMP
