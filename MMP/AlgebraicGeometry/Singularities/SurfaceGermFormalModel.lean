module

import MMP.RingTheory.PowerSeries.CompleteLocalRing
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
/-!
# Formal models of a smooth surface germ with smooth or nodal boundary

Let `Y` be a smooth surface over an algebraically closed field `K` of characteristic `0`,
`y ∈ Y` a closed point and `C ⊆ Y` a reduced curve through `y`, with ideal `I_{C,y} ⊆ 𝒪_{Y,y}`.
If `C` is smooth at `y`, there is a `K`-algebra isomorphism `𝒪̂_{Y,y} ≃ K[[u, v]]` carrying the
completed ideal `I_{C,y} 𝒪̂_{Y,y}` onto `(u)`. If `C` has an ordinary node at `y`, i.e. its local
equation `f` has degree-two initial form a product of two non-proportional linear forms, there is
one carrying `I_{C,y} 𝒪̂_{Y,y}` onto `(u v)`.

## Main results

* `MMP.Flips.exists_algEquiv_mvPowerSeries_map_ker_stalkMap_eq_span`: the two formal models.

## Implementation notes

* The curve `C` is a closed immersion `i : Z ⟶ Y` with `Z` reduced and every irreducible
  component of `Z` of dimension one, and `z ∈ Z` is the point over `y`. The ideal `I_{C,y}` is
  the kernel of the surjection `i.stalkMap z : 𝒪_{Y,y} → 𝒪_{Z,z}`. For an ideal sheaf `𝓘` this
  is `𝓘.subschemeι`, whose range is the support of `𝓘`.
* The completion `𝒪̂_{Y,y}` is `AdicCompletion (maximalIdeal 𝒪_{Y,y}) 𝒪_{Y,y}`. It is a
  `K`-algebra through the `K`-algebra structure of `𝒪_{Y,y}` given by
  `K = Γ(Spec K) → Γ(Y) → 𝒪_{Y,y}`. `K[[u, v]]` is `MvPowerSeries (Fin 2) K`, with `u = X 0`
  and `v = X 1`.
* *Smooth at `y`* means that `𝒪_{Z,z} = 𝒪_{Y,y} ⧸ I_{C,y}` is a regular local ring.
* *Ordinary node at `y`*: `I_{C,y} = (f)`, and there are `a, b ∈ 𝒪_{Y,y}` with
  `(a, b) = 𝔪_{Y,y}` and `f - a b ∈ 𝔪_{Y,y}³`. Since `𝒪_{Y,y}` is regular of dimension two,
  `(a, b) = 𝔪` says that the classes of `a, b` form a basis of `𝔪/𝔪²`. So the class of `f`
  in `𝔪²/𝔪³ = Sym² (𝔪/𝔪²)` is the product of two non-proportional linear forms. Conversely,
  any such product `c ℓ₁ ℓ₂` has this form, with `c` absorbed into `ℓ₁`.
* The formal Morse lemma is proved by successive approximation: if `g - (u + a)(v + b) ∈ 𝔪ⁿ⁺³`,
  write the error as `(u + a) Q + (v + b) P` with `P, Q ∈ 𝔪ⁿ⁺²` and correct `a, b` by `Q, P`;
  the new error `-P Q` lies in `𝔪ⁿ⁺⁴`, and the corrections converge in the complete ring `𝒪̂`.
  The two factors again generate `𝔪̂`, and the Cohen structure theorem `K[[u, v]] ≃ 𝒪̂`
  sending `u, v` to them gives the nodal model. In the smooth case `dim 𝒪_{Z,z} = 1` is read off
  the topology: `z` is closed, and a chain of two generizations of `z` would lie in one
  irreducible component, of dimension at least `2`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6.3
-/

public section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Topology TopologicalSpace

namespace MMP.Flips

/-! ### Dimension of the local ring of a curve -/

/-- A subspace of a `T₀` space containing distinct points `a, b, c` with `c ⤳ b ⤳ a` has
dimension at least `2`. -/
private theorem two_le_topologicalKrullDim_of_specializes {X : Type*} [TopologicalSpace X]
    [T0Space X] (W : Set X) {a b c : X} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hab : b ⤳ a)
    (hbc : c ⤳ b) (hne₁ : a ≠ b) (hne₂ : b ≠ c) : (2 : WithBot ℕ∞) ≤ topologicalKrullDim W := by
  have key : ∀ {p q : W}, (q : X) ⤳ p → (p : X) ≠ q →
      (⟨closure {p}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds W) <
        ⟨closure {q}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    intro p q hqp hpq
    have hqp' : q ⤳ p := IsInducing.subtypeVal.specializes_iff.1 hqp
    rw [← SetLike.coe_ssubset_coe]
    refine LE.le.ssubset_of_ne (specializes_iff_closure_subset.1 hqp') fun h => hpq ?_
    exact congrArg Subtype.val (inseparable_iff_closure_eq.2 h).eq
  let s : LTSeries (IrreducibleCloseds W) :=
    { length := 2
      toFun := ![⟨closure {⟨a, ha⟩}, isIrreducible_singleton.closure, isClosed_closure⟩,
        ⟨closure {⟨b, hb⟩}, isIrreducible_singleton.closure, isClosed_closure⟩,
        ⟨closure {⟨c, hc⟩}, isIrreducible_singleton.closure, isClosed_closure⟩]
      step := fun i => by
        fin_cases i
        · exact key (p := ⟨a, ha⟩) (q := ⟨b, hb⟩) hab hne₁
        · exact key (p := ⟨b, hb⟩) (q := ⟨c, hc⟩) hbc hne₂ }
  exact Order.LTSeries.length_le_krullDim s

private theorem coheight_le_one {Z : Scheme}
    (hcurve : ∀ W ∈ irreducibleComponents (Set.univ : Set Z), topologicalKrullDim W = 1)
    (z : Z) : Order.coheight z ≤ 1 := by
  by_contra hlt
  have h2 : ((2 : ℕ) : ℕ∞) ≤ Order.coheight z := Order.add_one_le_of_lt (not_le.1 hlt)
  obtain ⟨p, hp0, hplen⟩ := Order.exists_series_of_le_coheight z h2
  have h01 : p ⟨0, by omega⟩ < p ⟨1, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
  have h12 : p ⟨1, by omega⟩ < p ⟨2, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
  let q : Z → (Set.univ : Set Z) := fun x => ⟨x, trivial⟩
  have hirr : IsIrreducible (closure {q (p ⟨2, by omega⟩)}) := isIrreducible_singleton.closure
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  have hspec : ∀ {x y : Z}, x ⤳ y → q x ⤳ q y := fun {x y} h =>
    (IsInducing.subtypeVal.specializes_iff (x := q x) (y := q y)).1 h
  have hmem : ∀ x : Z, p ⟨2, by omega⟩ ⤳ x → q x ∈ W := fun x h =>
    hsub (specializes_iff_mem_closure.1 (hspec h))
  have h21 : p ⟨2, by omega⟩ ⤳ p ⟨1, by omega⟩ := h12.le
  have h10 : p ⟨1, by omega⟩ ⤳ p ⟨0, by omega⟩ := h01.le
  have := two_le_topologicalKrullDim_of_specializes W (hmem _ (h21.trans h10)) (hmem _ h21)
    (hmem _ specializes_rfl) (hspec h10) (hspec h21)
    (fun h => h01.ne (congrArg Subtype.val h)) (fun h => h12.ne (congrArg Subtype.val h))
  rw [hcurve W hW] at this
  exact absurd this (by decide)

private theorem coheight_pos {Z : Scheme}
    (hcurve : ∀ W ∈ irreducibleComponents (Set.univ : Set Z), topologicalKrullDim W = 1)
    {z : Z} (hz : IsClosed ({z} : Set Z)) : 0 < Order.coheight z := by
  rw [pos_iff_ne_zero, Ne, Order.coheight_eq_zero]
  intro hmax
  let z' : (Set.univ : Set Z) := ⟨z, trivial⟩
  have hirr : IsIrreducible (Subtype.val '' irreducibleComponent z') :=
    (isIrreducible_irreducibleComponent).image _ continuous_subtype_val.continuousOn
  have hgen := hirr.isGenericPoint_genericPoint_closure
  have hηz : hirr.genericPoint ⤳ z :=
    hgen.specializes (subset_closure ⟨z', mem_irreducibleComponent, rfl⟩)
  have heq : hirr.genericPoint = z := (hηz.antisymm (hmax hηz)).eq
  have hsub : Subtype.val '' irreducibleComponent z' ⊆ {z} := by
    rw [← hz.closure_eq, ← heq, hgen.def]
    exact subset_closure
  have : Subsingleton (irreducibleComponent z') := ⟨fun a b => Subtype.ext <| Subtype.ext <|
    (Set.mem_singleton_iff.1 (hsub ⟨a.1, a.2, rfl⟩)).trans
      (Set.mem_singleton_iff.1 (hsub ⟨b.1, b.2, rfl⟩)).symm⟩
  have h0 := @topologicalKrullDim_zero_of_discreteTopology (irreducibleComponent z') _
    Subsingleton.discreteTopology
  rw [hcurve _ (irreducibleComponent_mem_irreducibleComponents z')] at h0
  exact absurd h0 (by decide)

/-- A closed point of a scheme all of whose irreducible components have dimension `1` has
coheight `1`. -/
private theorem coheight_eq_one {Z : Scheme}
    (hcurve : ∀ W ∈ irreducibleComponents (Set.univ : Set Z), topologicalKrullDim W = 1)
    {z : Z} (hz : IsClosed ({z} : Set Z)) : Order.coheight z = 1 :=
  le_antisymm (coheight_le_one hcurve z) (Order.one_le_iff_pos.2 (coheight_pos hcurve hz))

/-! ### The formal Morse lemma for a node -/

section Morse

variable {R : Type*} [CommRing R] {M : Ideal R}

/-- Two elements congruent to generators of a finitely generated ideal `M ⊆ rad R` modulo `M²`
generate `M`. -/
private theorem span_pair_add_eq (hfg : M.FG) (hjac : M ≤ (⊥ : Ideal R).jacobson)
    {u v a b : R} (huv : Ideal.span {u, v} = M) (ha : a ∈ M ^ 2) (hb : b ∈ M ^ 2) :
    Ideal.span {u + a, v + b} = M := by
  have hsq : M ^ 2 ≤ M := Ideal.pow_le_self two_ne_zero
  have hu : u ∈ M := huv ▸ Ideal.subset_span (by simp)
  have hv : v ∈ M := huv ▸ Ideal.subset_span (by simp)
  refine le_antisymm (Ideal.span_le.2 ?_) (Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac ?_)
  · simp [Set.insert_subset_iff, M.add_mem hu (hsq ha), M.add_mem hv (hsq hb)]
  have h2 : M ^ 2 ≤ M • M := by rw [pow_two, Ideal.smul_eq_mul]
  rw [← huv, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, huv]
  exact ⟨by simpa using Submodule.add_mem_sup (Ideal.subset_span (by simp) :
      u + a ∈ Ideal.span {u + a, v + b}) (h2 (neg_mem ha)),
    by simpa using Submodule.add_mem_sup (Ideal.subset_span (by simp) :
      v + b ∈ Ideal.span {u + a, v + b}) (h2 (neg_mem hb))⟩

/-- An element of `M^(n+1)`, for `M = (u, v)`, is `u P + v Q` with `P, Q ∈ M^n`. -/
private theorem exists_eq_add_of_mem_pow_succ {u v e : R} (huv : Ideal.span {u, v} = M) {n : ℕ}
    (he : e ∈ M ^ (n + 1)) : ∃ P Q, P ∈ M ^ n ∧ Q ∈ M ^ n ∧ e = u * P + v * Q := by
  have he' : e ∈ Ideal.span {u, v} * M ^ n := by rwa [huv, ← pow_succ']
  rw [Ideal.span_insert, Ideal.sup_mul, Submodule.mem_sup] at he'
  obtain ⟨y, hy, z, hz, rfl⟩ := he'
  obtain ⟨P, hP, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  obtain ⟨Q, hQ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hz
  exact ⟨P, Q, hP, hQ, rfl⟩

/-- If `g ≡ (u + a)(v + b)` modulo `M ^ (n + 3)`, there are `a' ≡ a`, `b' ≡ b` modulo
`M ^ (n + 2)`, still in `M ^ 2`, with `g ≡ (u + a')(v + b')` modulo `M ^ (n + 4)`. -/
private theorem exists_sub_mul_mem_pow_add_four (hfg : M.FG)
    (hjac : M ≤ (⊥ : Ideal R).jacobson) {u v g : R} (huv : Ideal.span {u, v} = M) (n : ℕ)
    (a b : R) (ha : a ∈ M ^ 2) (hb : b ∈ M ^ 2) (he : g - (u + a) * (v + b) ∈ M ^ (n + 3)) :
    ∃ a' b', a' ∈ M ^ 2 ∧ b' ∈ M ^ 2 ∧ g - (u + a') * (v + b') ∈ M ^ (n + 4) ∧
      a' - a ∈ M ^ (n + 2) ∧ b' - b ∈ M ^ (n + 2) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_eq_add_of_mem_pow_succ
    (span_pair_add_eq hfg hjac huv ha hb) he
  have hle : M ^ (n + 2) ≤ M ^ 2 := Ideal.pow_le_pow_right (by omega)
  refine ⟨a + Q, b + P, (M ^ 2).add_mem ha (hle hQ),
    (M ^ 2).add_mem hb (hle hP), ?_, by simpa using hQ, by simpa using hP⟩
  rw [show g - (u + (a + Q)) * (v + (b + P)) = -(P * Q) by linear_combination hPQ]
  refine (M ^ (n + 4)).neg_mem ?_
  have : P * Q ∈ M ^ (n + 2 + (n + 2)) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hP hQ
  exact Ideal.pow_le_pow_right (by omega) this

private theorem mem_pow_smul_top {x : R} {n : ℕ} :
    x ∈ (M ^ n • ⊤ : Submodule R R) ↔ x ∈ M ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- In an `M`-adically precomplete ring, a sequence whose `n`-th step lies in `M ^ n` has a limit
`a`, with `x n - a ∈ M ^ n`. -/
private theorem exists_forall_sub_mem_pow [IsPrecomplete M R] {x : ℕ → R}
    (hx : ∀ n, x (n + 1) - x n ∈ M ^ n) : ∃ a, ∀ n, x n - a ∈ M ^ n := by
  obtain ⟨a, ha⟩ := IsPrecomplete.prec inferInstance ((AdicCompletion.isAdicCauchy_iff M R x).2
    fun n => by rw [SModEq.sub_mem, mem_pow_smul_top, ← neg_sub]; exact neg_mem (hx n))
  exact ⟨a, fun n => mem_pow_smul_top.1 (SModEq.sub_mem.1 (ha n))⟩

/-- **The formal Morse lemma for a node.** In a ring complete for a finitely generated ideal
`M = (u, v)`, an element `g ≡ uv` modulo `M³` factors as `g = (u + a)(v + b)` with
`a, b ∈ M²`. -/
private theorem exists_eq_mul_of_sub_mul_mem_pow_three [IsAdicComplete M R] (hfg : M.FG)
    {u v g : R} (huv : Ideal.span {u, v} = M) (hg : g - u * v ∈ M ^ 3) :
    ∃ a b, a ∈ M ^ 2 ∧ b ∈ M ^ 2 ∧ g = (u + a) * (v + b) := by
  let P : ℕ → R × R → Prop := fun n p =>
    p.1 ∈ M ^ 2 ∧ p.2 ∈ M ^ 2 ∧ g - (u + p.1) * (v + p.2) ∈ M ^ (n + 3)
  have hstep : ∀ n p, P n p → ∃ p', P (n + 1) p' ∧ p'.1 - p.1 ∈ M ^ n ∧ p'.2 - p.2 ∈ M ^ n := by
    rintro n ⟨a, b⟩ ⟨ha, hb, he⟩
    obtain ⟨a', b', ha', hb', he', hda, hdb⟩ :=
      exists_sub_mul_mem_pow_add_four hfg (IsAdicComplete.le_jacobson_bot M) huv n a b ha hb he
    have hle : M ^ (n + 2) ≤ M ^ n := Ideal.pow_le_pow_right (by omega)
    exact ⟨(a', b'), ⟨ha', hb', he'⟩, hle hda, hle hdb⟩
  choose! step hP hd₁ hd₂ using hstep
  let x : ℕ → R × R := fun n => n.rec (0, 0) step
  have hx : ∀ n, P n (x n) := fun n => n.rec (by simpa [P, x] using hg) fun n ih => hP n _ ih
  obtain ⟨a, ha⟩ := exists_forall_sub_mem_pow (x := fun n => (x n).1) fun n => hd₁ n _ (hx n)
  obtain ⟨b, hb⟩ := exists_forall_sub_mem_pow (x := fun n => (x n).2) fun n => hd₂ n _ (hx n)
  refine ⟨a, b, by simpa using (M ^ 2).sub_mem (hx 2).1 (ha 2),
    by simpa using (M ^ 2).sub_mem (hx 2).2.1 (hb 2),
    (IsHausdorff.eq_iff_smodEq (I := M)).2 fun n => SModEq.sub_mem.2 (mem_pow_smul_top.2 ?_)⟩
  have h := (M ^ n).add_mem (Ideal.pow_le_pow_right (by omega) (hx n).2.2) <|
    (M ^ n).add_mem (Ideal.mul_mem_right (v + (x n).2) _ (ha n))
      (Ideal.mul_mem_left _ (u + a) (hb n))
  convert h using 1
  ring

end Morse

/-! ### The two formal models -/

/-- Two generators of the maximal ideal of a Noetherian local ring `R` map to generators of the
maximal ideal of its completion `R̂`. -/
private theorem span_algebraMap_pair_eq_maximalIdeal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {a b : R} (hab : Ideal.span {a, b} = maximalIdeal R) :
    Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) a,
      algebraMap R (AdicCompletion (maximalIdeal R) R) b} =
        maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  have h := congrArg (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) hab
  rw [Ideal.map_span, Set.image_pair] at h
  rw [h, AdicCompletion.maximalIdeal_eq_map]

/-- **The smooth formal model.** If `R ⧸ I` is regular of dimension `1`, there is a `K`-algebra
isomorphism `R̂ ≃ K[[u, v]]` carrying `I R̂` onto `(u)`. -/
private theorem exists_algEquiv_map_eq_span_X {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2)
    (hcohen : ∀ z : Fin 2 → AdicCompletion (maximalIdeal R) R,
      Ideal.span (Set.range z) = maximalIdeal (AdicCompletion (maximalIdeal R) R) →
      ∃ Φ : MvPowerSeries (Fin 2) K ≃ₐ[K] AdicCompletion (maximalIdeal R) R,
        ∀ i, Φ (MvPowerSeries.X i) = z i)
    (I : Ideal R) (hreg : IsRegularLocalRing (R ⧸ I)) (hdimI : ringKrullDim (R ⧸ I) = 1) :
    ∃ φ : AdicCompletion (maximalIdeal R) R ≃ₐ[K] MvPowerSeries (Fin 2) K,
      Ideal.map φ (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) I) =
        Ideal.span {MvPowerSeries.X 0} := by
  set Rh := AdicCompletion (maximalIdeal R) R
  obtain ⟨xs, hgen, hlen, c, hc, hIc, hdc⟩ :=
    IsRegularLocalRing.exists_ofList_eq_maximalIdeal_length_eq_spanFinrank_and_ofList_take_eq I
      hreg
  have h2 : xs.length = 2 := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at this
    rw [hlen]
    exact_mod_cast this
  obtain rfl : c = 1 := by
    rw [hdimI, hdim] at hdc
    have : ((1 + c : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdc
    have := Nat.cast_injective this
    omega
  match xs, h2 with
  | [a, b], _ =>
    have hab : Ideal.span {a, b} = maximalIdeal R := by
      rw [← hgen]
      simp only [Ideal.ofList, List.mem_cons, List.not_mem_nil, or_false]
      rfl
    have hI : I = Ideal.span {a} := by
      rw [← hIc]
      simp [Ideal.ofList]
    obtain ⟨Φ, hΦ⟩ := hcohen ![algebraMap R Rh a, algebraMap R Rh b]
      (by rw [Matrix.range_cons_cons_empty]; exact span_algebraMap_pair_eq_maximalIdeal hab)
    refine ⟨Φ.symm, ?_⟩
    have h0 : Φ (MvPowerSeries.X 0) = algebraMap R Rh a := hΦ 0
    rw [hI, Ideal.map_span, Set.image_singleton, ← h0, Ideal.map_span, Set.image_singleton,
      AlgEquiv.symm_apply_apply]

/-- **The nodal formal model.** If `f ≡ a b` modulo `𝔪³` for generators `a, b` of `𝔪`, there is a
`K`-algebra isomorphism `R̂ ≃ K[[u, v]]` carrying `(f) R̂` onto `(u v)`. -/
private theorem exists_algEquiv_map_eq_span_X_mul_X {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [IsLocalRing R] [IsNoetherianRing R]
    (hcohen : ∀ z : Fin 2 → AdicCompletion (maximalIdeal R) R,
      Ideal.span (Set.range z) = maximalIdeal (AdicCompletion (maximalIdeal R) R) →
      ∃ Φ : MvPowerSeries (Fin 2) K ≃ₐ[K] AdicCompletion (maximalIdeal R) R,
        ∀ i, Φ (MvPowerSeries.X i) = z i)
    {f a b : R} (hab : Ideal.span {a, b} = maximalIdeal R) (hf : f - a * b ∈ maximalIdeal R ^ 3) :
    ∃ φ : AdicCompletion (maximalIdeal R) R ≃ₐ[K] MvPowerSeries (Fin 2) K,
      Ideal.map φ (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (Ideal.span {f})) =
        Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} := by
  set Rh := AdicCompletion (maximalIdeal R) R
  have hM := span_algebraMap_pair_eq_maximalIdeal hab
  have hfg : (maximalIdeal Rh).FG := hM ▸ Submodule.fg_span (Set.toFinite _)
  have hf' : algebraMap R Rh f - algebraMap R Rh a * algebraMap R Rh b ∈ maximalIdeal Rh ^ 3 := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← map_mul, ← map_sub]
    exact Ideal.mem_map_of_mem _ hf
  obtain ⟨α, β, hα, hβ, hfac⟩ := exists_eq_mul_of_sub_mul_mem_pow_three hfg hM hf'
  obtain ⟨Φ, hΦ⟩ := hcohen ![algebraMap R Rh a + α, algebraMap R Rh b + β] (by
    rw [Matrix.range_cons_cons_empty]
    exact span_pair_add_eq hfg (IsAdicComplete.le_jacobson_bot _) hM hα hβ)
  refine ⟨Φ.symm, ?_⟩
  have hX : Φ (MvPowerSeries.X 0 * MvPowerSeries.X 1) = algebraMap R Rh f := by
    rw [map_mul, hΦ 0, hΦ 1, hfac]
    rfl
  rw [Ideal.map_span, Set.image_singleton, ← hX, Ideal.map_span, Set.image_singleton,
    AlgEquiv.symm_apply_apply]

/-- **The Cohen structure theorem with given parameters.** Let `R` be a Noetherian local
`K`-algebra of dimension `n` whose residue field is `K`. For any `z₁, …, zₙ` generating the
maximal ideal of `R̂` there is a `K`-algebra isomorphism `K[[x₁, …, xₙ]] ≃ R̂` with `xᵢ ↦ zᵢ`. -/
private theorem exists_algEquiv_mvPowerSeries_X_eq {K R : Type*} [Field K] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Algebra K R]
    (hres : Function.Surjective (algebraMap K (R ⧸ maximalIdeal R))) {n : ℕ}
    (hdim : ringKrullDim R = n) (z : Fin n → AdicCompletion (maximalIdeal R) R)
    (hz : Ideal.span (Set.range z) = maximalIdeal (AdicCompletion (maximalIdeal R) R)) :
    ∃ Φ : MvPowerSeries (Fin n) K ≃ₐ[K] AdicCompletion (maximalIdeal R) R,
      ∀ i, Φ (MvPowerSeries.X i) = z i := by
  have hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
      (AdicCompletion (maximalIdeal R) R))).comp
        (algebraMap K (AdicCompletion (maximalIdeal R) R))) := by
    intro w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨r, hr⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue _ w)
    obtain ⟨r, rfl⟩ := residue_surjective r
    obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk _ r)
    refine ⟨c, ?_⟩
    change residue _ (algebraMap R (AdicCompletion (maximalIdeal R) R) (algebraMap K R c)) =
      residue _ w
    rw [← hr, ← ResidueField.map_residue]
    exact congrArg _ hc
  obtain ⟨F, hFs, hFX, hFC⟩ := Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) z hz _ hsurj
  have hinj := ResolutionInputs.injective_of_surjective_of_ringKrullDim_le F hFs
    (MvPowerSeries.ringKrullDim_le K n)
    (by rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hdim])
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective F ⟨hinj, hFs⟩) hFC, hFX⟩

/-! ### The local ring of a smooth surface at a closed point -/

/-- The local ring at a closed point of a scheme smooth of relative dimension `2` over an
algebraically closed field has dimension `2`. -/
private theorem ringKrullDim_stalk_eq_two {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sY] (y : Y)
    (hy : IsClosed ({y} : Set Y)) : ringKrullDim (Y.presheaf.stalk y) = 2 := by
  have : Smooth sY := SmoothOfRelativeDimension.smooth 2 sY
  have h1 := fiberDimensionAt_eq_of_smoothOfRelativeDimension sY 2 y
  rw [topologicalKrullDimAt_fiber_eq] at h1
  have h2 := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk K Y sY y
  let : Algebra K (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ sY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap K (Y.residueField y)) :=
    MMP.Mori.SurfaceAux.residue_surjective sY y hy
  have : Algebra.IsAlgebraic K (Y.residueField y) := ⟨fun r => by
    obtain ⟨a, rfl⟩ := hsurj r
    exact isAlgebraic_algebraMap a⟩
  have h0 : Algebra.trdeg K (Y.residueField y) = 0 := trdeg_eq_zero
  rw [h0, h1] at h2
  simpa using h2.symm

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}}
  (sY : Y ⟶ Spec (.of K))

/-- **Smooth and nodal boundary on a smooth surface germ.** Let `Y` be smooth of relative
dimension `2` over an algebraically closed field `K` of characteristic `0`, `y ∈ Y` a closed
point, and `i : Z ⟶ Y` a reduced curve through `y`, with `i z = y`. Write
`I = ker (i.stalkMap z) ⊆ 𝒪_{Y,y}`. Suppose `Z` is smooth at `z` (`𝒪_{Z,z}` is regular), or
suppose `Z` has an ordinary node there (`I = (f)` with `f ≡ a b mod 𝔪³` for generators `a, b` of
`𝔪_{Y,y}`). Then there is a `K`-algebra isomorphism `φ : 𝒪̂_{Y,y} ≃ K[[u, v]]` carrying
`I 𝒪̂_{Y,y}` onto `(u)` in the first case and onto `(u v)` in the second. -/
@[mmp "lem_mmp_foundation_fa16_empty_chain_smooth_germ"]
public theorem exists_algEquiv_mvPowerSeries_map_ker_stalkMap_eq_span
    [SmoothOfRelativeDimension 2 sY] (y : Y) (hy : IsClosed ({y} : Set Y))
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsReduced Z]
    (hcurve : ∀ W ∈ irreducibleComponents (Set.univ : Set Z), topologicalKrullDim W = 1)
    (z : Z) (hz : i z = y) (g : MvPowerSeries (Fin 2) K)
    (hcase : IsRegularLocalRing (Z.presheaf.stalk z) ∧ g = MvPowerSeries.X 0 ∨
      (∃ f a b : Y.presheaf.stalk (i z), RingHom.ker (i.stalkMap z).hom = Ideal.span {f} ∧
        Ideal.span {a, b} = maximalIdeal (Y.presheaf.stalk (i z)) ∧
        f - a * b ∈ maximalIdeal (Y.presheaf.stalk (i z)) ^ 3) ∧
        g = MvPowerSeries.X 0 * MvPowerSeries.X 1) :
    letI : Algebra K (Y.presheaf.stalk (i z)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ sY.appTop ≫
        Y.presheaf.germ ⊤ (i z) (Opens.mem_top _)).hom.toAlgebra
    ∃ φ : AdicCompletion (maximalIdeal (Y.presheaf.stalk (i z))) (Y.presheaf.stalk (i z)) ≃ₐ[K]
        MvPowerSeries (Fin 2) K,
      Ideal.map φ (Ideal.map (algebraMap (Y.presheaf.stalk (i z))
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk (i z))) (Y.presheaf.stalk (i z))))
          (RingHom.ker (i.stalkMap z).hom)) = Ideal.span {g} := by
  have : Smooth sY := SmoothOfRelativeDimension.smooth 2 sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  subst hz
  have hzcl : IsClosed ({z} : Set Z) :=
    i.isClosedEmbedding.isClosed_iff_image_isClosed.2 (by rwa [Set.image_singleton])
  let : Algebra K (Y.presheaf.stalk (i z)) := MMP.Mori.stalkAlgebra sY (i z)
  have hres : Function.Surjective
      (algebraMap K (Y.presheaf.stalk (i z) ⧸ maximalIdeal (Y.presheaf.stalk (i z)))) :=
    MMP.Mori.SurfaceAux.residue_surjective sY (i z) hy
  have := isRegularLocalRing_stalk_of_smooth_over_field sY (i z)
  have hdim := ringKrullDim_stalk_eq_two sY (i z) hy
  have hcohen := exists_algEquiv_mvPowerSeries_X_eq (K := K) hres (by rw [hdim]; rfl)
  rcases hcase with ⟨hZreg, rfl⟩ | ⟨⟨f, a, b, hI, hab, hf⟩, rfl⟩
  · let e := RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)
    refine exists_algEquiv_map_eq_span_X hdim hcohen _ (IsRegularLocalRing.of_ringEquiv e.symm) ?_
    rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_stalk_eq_coheight,
      coheight_eq_one hcurve hzcl]
    rfl
  · rw [hI]
    exact exists_algEquiv_map_eq_span_X_mul_X hcohen hab hf

end MMP.Flips
