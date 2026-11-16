module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier

section

/-!
# The relative Kleiman criterion for real Cartier divisors in characteristic zero

Let `k` be an algebraically closed field of characteristic zero, `f : Y ⟶ X` a projective
morphism of `k`-varieties, `N₁(Y/X)` the real 1-cycles on curves contracted by `f` modulo
numerical equivalence and `NE̅(Y/X) ⊆ N₁(Y/X)` the closed cone spanned by contracted curves.
A real Cartier divisor `B ∈ ℝ ⊗ Div(Y)` is a finite positive real combination of `f`-ample
Cartier divisors if and only if `(z · B) > 0` for every nonzero `z ∈ NE̅(Y/X)`. Consequently
this real `f`-ampleness depends only on the degrees of `B` on contracted curves, and a Cartier
divisor which is `f`-ample in the real sense is `f`-ample.

## Main results

* `MMP.Mori.exists_sum_tmul_isRelativelyAmple_iff_forall_relativeClosedConeOfCurves_pos`:
  the relative Kleiman criterion for real Cartier divisors, with its two consequences.

## Implementation notes

A real Cartier divisor is presented by a formal combination `B : KCartierDivisor ℝ Y`, i.e.
`∑ⱼ bⱼ Fⱼ` with `Fⱼ ∈ Div(Y)`; the divisor it presents is its image in `ℝ ⊗[ℤ] Div(Y)` under
`Fⱼ ↦ 1 ⊗ Fⱼ`. Being a positive combination of `f`-ample Cartier divisors `Aᵢ` means
`B = ∑ᵢ rᵢ (1 ⊗ Aᵢ)` in `ℝ ⊗[ℤ] Div(Y)` with at least one summand and all `rᵢ > 0`, so linear
relations among Cartier divisors are respected (`1 ⊗ 2D = 2 (1 ⊗ D)`). `f`-ampleness of a
Cartier divisor `A` is `MMP.Mori.IsRelativelyAmple` of `𝒪_Y(A)`, and `(z · B)` is
`MMP.Mori.RelativeNumericalCurveClasses.intersectionNumber`.

Write `K = NE̅(Y/X)`. The pairing `(z · ·)` with a class `z` is additive on Cartier divisors, so it
factors through `ℝ ⊗[ℤ] Div(Y)`; with the Cartier criterion this gives the forward implication.
Conversely, write `B = ∑_{D ∈ s} b_D D`. Since `N₁(Y/X)` is finite-dimensional and `K` is closed,
`K` meets the unit sphere (for any norm transported from `ℝⁿ`) in a compact set, on which `B` has a
positive minimum; hence every coefficient vector close enough to `b` still defines a form positive
on `K \ {0}`. With `L = 2Mn` (`n = #s`, `M ≫ 0`) and `c_D = ⌈L b_D⌉ - 1`, the `n + 1` integral
vectors `c` and `c + 2n e_D` lie in this neighbourhood after division by `L`, and `b` is a positive
combination of them. Each of them is a Cartier divisor positive on `K \ {0}`, hence `f`-ample by the
Cartier criterion.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.44
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][FA], 2.13
-/

namespace MMP.FourfoldProofs.MmpFoundationRelativeRealKleimanCharZeroProof

open AlgebraicGeometry CategoryTheory TensorProduct MMP.Mori

/-! ### Perturbing a form positive on a closed cone -/

/-- `|∑ᵢ (β'ᵢ - βᵢ) φᵢ(w)| ≤ ε ∑ᵢ ‖φᵢ‖` for a unit vector `w` and `|β'ᵢ - βᵢ| < ε`. -/
private theorem abs_sum_sub_mul_le {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (φ : ι → E →L[ℝ] ℝ) {w : E} (hw : ‖w‖ = 1) {β β' : ι → ℝ} {ε : ℝ}
    (hβ : ∀ i ∈ s, |β' i - β i| < ε) :
    |∑ i ∈ s, (β' i - β i) * φ i w| ≤ ε * ∑ i ∈ s, ‖φ i‖ := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul]
  have hb : |φ i w| ≤ ‖φ i‖ := by simpa [hw, Real.norm_eq_abs] using (φ i).le_opNorm w
  exact mul_le_mul (hβ i hi).le hb (abs_nonneg _) ((abs_nonneg _).trans (hβ i hi).le)

/-- If `∑ βᵢ φᵢ` is positive on `K \ {0}` for a closed cone `K` in a finite-dimensional normed
space, then so is `∑ β'ᵢ φᵢ` for every `β'` close enough to `β`. -/
private theorem exists_pos_of_isClosed_normed {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K)
    (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) (s : Finset ι) (φ : ι → E →ₗ[ℝ] ℝ)
    (β : ι → ℝ) (hpos : ∀ z ∈ K, z ≠ 0 → 0 < ∑ i ∈ s, β i * φ i z) :
    ∃ ε > 0, ∀ β' : ι → ℝ, (∀ i ∈ s, |β' i - β i| < ε) →
      ∀ z ∈ K, z ≠ 0 → 0 < ∑ i ∈ s, β' i * φ i z := by
  have hunit : ∀ z ∈ K, z ≠ 0 → ‖z‖⁻¹ • z ∈ K ∩ Metric.sphere 0 1 := fun z hz hz0 =>
    ⟨hcone z hz _ (inv_pos.2 (norm_pos_iff.2 hz0)), by
      simp [norm_smul, norm_ne_zero_iff.2 hz0]⟩
  by_cases hS : (K ∩ Metric.sphere (0 : E) 1).Nonempty
  swap
  · exact ⟨1, one_pos, fun β' _ z hz hz0 => absurd ⟨_, hunit z hz hz0⟩ hS⟩
  let g : E → ℝ := fun z => ∑ i ∈ s, β i * φ i z
  have hgc : Continuous g := by
    have := fun i => LinearMap.continuous_of_finiteDimensional (φ i)
    fun_prop
  obtain ⟨w0, hw0, hmin⟩ :=
    ((isCompact_sphere (0 : E) 1).inter_left hK).exists_isMinOn hS hgc.continuousOn
  have hw00 : w0 ≠ 0 := by
    rintro rfl
    simpa using hw0.2
  have hm : 0 < g w0 := hpos w0 hw0.1 hw00
  let C := ∑ i ∈ s, ‖LinearMap.toContinuousLinearMap (φ i)‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨g w0 / (C + 1), div_pos hm (by linarith), fun β' hβ' z hz hz0 => ?_⟩
  have hw := hunit z hz hz0
  set w := ‖z‖⁻¹ • z with hwdef
  have h1 : g w0 ≤ g w := hmin hw
  have hnw : ‖w‖ = 1 := by simpa using hw.2
  have h3 : ∑ i ∈ s, β' i * φ i w = g w + ∑ i ∈ s, (β' i - β i) * φ i w := by
    simp only [g, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h4 : |∑ i ∈ s, (β' i - β i) * φ i w| ≤ g w0 / (C + 1) * C :=
    abs_sum_sub_mul_le s (fun i => LinearMap.toContinuousLinearMap (φ i)) hnw hβ'
  have h5 : g w0 / (C + 1) * C < g w0 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have key : 0 < ∑ i ∈ s, β' i * φ i w := by
    rw [h3]
    linarith [neg_abs_le (∑ i ∈ s, (β' i - β i) * φ i w)]
  have hz' : ∑ i ∈ s, β' i * φ i z = ‖z‖ * ∑ i ∈ s, β' i * φ i w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, map_smul, smul_eq_mul]
    field_simp [norm_ne_zero_iff.2 hz0]
  rw [hz']
  exact mul_pos (norm_pos_iff.2 hz0) key

/-- The same perturbation statement in a finite-dimensional real vector space whose topology
makes every linear map from `ℝⁿ` continuous. -/
private theorem exists_pos_of_isClosed {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace V]
    (hcont : ∀ g : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V, Continuous g) {K : Set V}
    (hK : IsClosed K) (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) (s : Finset ι)
    (φ : ι → V →ₗ[ℝ] ℝ) (β : ι → ℝ) (hpos : ∀ z ∈ K, z ≠ 0 → 0 < ∑ i ∈ s, β i * φ i z) :
    ∃ ε > 0, ∀ β' : ι → ℝ, (∀ i ∈ s, |β' i - β i| < ε) →
      ∀ z ∈ K, z ≠ 0 → 0 < ∑ i ∈ s, β' i * φ i z := by
  let e := (Module.finBasis ℝ V).equivFun
  obtain ⟨ε, hε, h⟩ := exists_pos_of_isClosed_normed (K := e.symm ⁻¹' K)
    (hK.preimage (hcont e.symm.toLinearMap))
    (fun z hz t ht => by simpa [Set.mem_preimage, map_smul] using hcone _ hz t ht) s
    (fun i => (φ i).comp e.symm.toLinearMap) β
    (fun w hw hw0 => hpos _ hw (by simpa using hw0))
  refine ⟨ε, hε, fun β' hβ' z hz hz0 => ?_⟩
  simpa using h β' hβ' (e z) (by simpa using hz) (by simpa using hz0)

/-! ### A rational simplex around a real vector -/

/-- `0 < x - (⌈L x⌉ - 1) / L ≤ 1 / L` for `L > 0`. -/
private theorem sub_ceil_sub_one_div_bounds {L : ℝ} (hL : 0 < L) (x : ℝ) :
    0 < x - ((⌈L * x⌉ - 1 : ℤ) : ℝ) / L ∧ x - ((⌈L * x⌉ - 1 : ℤ) : ℝ) / L ≤ 1 / L := by
  have h1 := Int.le_ceil (L * x)
  have h2 := Int.ceil_lt_add_one (L * x)
  rw [Int.cast_sub, Int.cast_one]
  constructor
  · rw [sub_pos, div_lt_iff₀ hL]
    linarith
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hL]
    linarith

private theorem ite_div_nonneg_and_le (p : Prop) [Decidable p] {M n : ℝ} (hM : 0 < M)
    (hn : 0 < n) :
    0 ≤ (if p then 2 * n else 0) / (2 * M * n) ∧
      (if p then 2 * n else 0) / (2 * M * n) ≤ 1 / M := by
  split_ifs
  · exact ⟨by positivity, le_of_eq (by field_simp)⟩
  · simp only [zero_div]
    exact ⟨le_rfl, by positivity⟩

/-- A real vector `b` on a nonempty finite set `s` is a positive combination of `#s + 1` integral
vectors `a_j` which, after division by a common `L > 0`, are `ε`-close to `b`: the vectors
`c` and `c + 2n e_i`, with `n = #s`, `L = 2Mn` for `M ≫ 0` and `c_i = ⌈L b_i⌉ - 1`. -/
private theorem exists_rational_simplex {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (b : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∃ (r : Option ι → ℝ) (a : Option ι → ι → ℤ),
      (∀ j ∈ s.insertNone, 0 < r j) ∧
      (∀ j ∈ s.insertNone, ∀ i ∈ s, |(a j i : ℝ) / L - b i| < ε) ∧
      (∀ i ∈ s, ∑ j ∈ s.insertNone, r j * a j i = b i) := by
  obtain ⟨n, hn, hn0⟩ : ∃ n : ℕ, s.card = n ∧ 0 < n := ⟨_, rfl, Finset.card_pos.2 hs⟩
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hM0 : (0 : ℝ) < M := lt_trans (by positivity) hM
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * M * n := ⟨_, rfl⟩
  have hL0 : 0 < L := by
    rw [hL]
    positivity
  have hML : 1 / L ≤ 1 / (M : ℝ) := by
    rw [one_div_le_one_div hL0 hM0, hL]
    nlinarith
  have hM1 : 1 / (M : ℝ) < ε := by
    rw [div_lt_iff₀ hM0]
    rw [div_lt_iff₀ hε] at hM
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ι → ℤ, ∀ i, c i = ⌈L * b i⌉ - 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ι → ℝ, ∀ i, d i = b i - c i / L := ⟨_, fun _ => rfl⟩
  have hd : ∀ i, 0 < d i ∧ d i ≤ 1 / L := fun i => by
    rw [hdd, hc]
    exact sub_ceil_sub_one_div_bounds hL0 (b i)
  have hsum : ∑ i ∈ s, M * d i ≤ 1 / 2 :=
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hd i).2 hM0.le).trans_eq <| by
      rw [Finset.sum_const, hn, nsmul_eq_mul, hL]
      field_simp
  refine ⟨L, hL0, fun j => Option.elim j ((1 - ∑ i ∈ s, M * d i) / L) fun i => M * d i / L,
    fun j i => c i + if j = some i then 2 * n else 0, ?_, ?_, ?_⟩
  · rintro (_ | i) _
    · exact div_pos (by linarith) hL0
    · exact div_pos (mul_pos hM0 (hd i).1) hL0
  · intro j _ i _
    have hδ := ite_div_nonneg_and_le (j = some i) hM0 hn0'
    rw [← hL] at hδ
    have he : ((c i + if j = some i then 2 * n else 0 : ℤ) : ℝ) / L - b i =
        (if j = some i then (2 * n : ℝ) else 0) / L - d i := by
      rw [hdd]
      push_cast
      ring
    rw [he, abs_lt]
    constructor <;> linarith [(hd i).1, (hd i).2, hδ.1, hδ.2]
  · intro i hi
    rw [Finset.sum_insertNone]
    simp only [Option.elim_none, Option.elim_some, Option.some_inj, reduceCtorEq, if_false,
      add_zero]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', hi,
      if_true, ← Finset.sum_mul, ← Finset.sum_div]
    rw [hdd i, hL]
    field_simp
    ring

/-! ### The pairing on `ℝ ⊗[ℤ] Div(Y)` -/

section Pairing

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}

/-- `deg_C 𝒪_Y(E + E') = deg_C 𝒪_Y(E) + deg_C 𝒪_Y(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sY) (E E' : Y.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.presheaf Y.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sY C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

/-- The pairing `E ↦ (z · 1 · E)` with a relative class `z`, additive on Cartier divisors. -/
private noncomputable def cartierPairing (z : RelativeNumericalCurveClasses sY f) :
    Y.CartierDivisor →+ ℝ :=
  AddMonoidHom.mk' (fun E => RelativeNumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z) fun E E' => by
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sY f z
    simp only [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply]
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun C _ => ?_
    rw [degree_cartierSheaf_add]
    push_cast
    ring

private theorem cartierPairing_apply (z : RelativeNumericalCurveClasses sY f)
    (E : Y.CartierDivisor) :
    cartierPairing z E = RelativeNumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z :=
  rfl

/-- `(z · B) = ∑_D b_D (z · 1 · D)` for `B = ∑_D b_D D`. -/
private theorem intersectionNumber_eq_sum (B : KCartierDivisor ℝ Y)
    (z : RelativeNumericalCurveClasses sY f) :
    RelativeNumericalCurveClasses.intersectionNumber B z =
      B.sum fun D b => b * cartierPairing z D := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sY f z
  simp only [cartierPairing_apply,
    RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier]
  simp only [OneCycle.intersectionNumber, OneCycle.intersectionPairing,
    Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]

/-- The pairing with `z` factors through the realization in `ℝ ⊗[ℤ] Div(Y)`. -/
private theorem intersectionNumber_eq_liftBaseChange (B : KCartierDivisor ℝ Y)
    (z : RelativeNumericalCurveClasses sY f) :
    RelativeNumericalCurveClasses.intersectionNumber B z =
      (cartierPairing z).toIntLinearMap.liftBaseChange ℝ
        (Finsupp.linearCombination ℝ (fun D : Y.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] D) B) := by
  rw [intersectionNumber_eq_sum, Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun D _ => ?_
  simp

/-- `(z · 1 · ∑_D a_D D) = ∑_D a_D (z · 1 · D)` for integers `a_D`. -/
private theorem cartierPairing_sum {ι : Type*} (z : RelativeNumericalCurveClasses sY f)
    (s : Finset ι) (a : ι → ℤ) (D : ι → Y.CartierDivisor) :
    cartierPairing z (∑ i ∈ s, a i • D i) = ∑ i ∈ s, (a i : ℝ) * cartierPairing z (D i) := by
  simp [map_sum, map_zsmul]

/-- Every linear map from a finite-dimensional normed space into `N₁(Y/X)` is continuous. -/
private theorem continuous_linearMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E →ₗ[ℝ] RelativeNumericalCurveClasses sY f) : Continuous g :=
  continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 <| by
    have := h
    exact LinearMap.continuous_of_finiteDimensional
      ((RelativeNumericalCurveClasses.degree sY f L).comp g)

/-! ### Positive combinations of Cartier divisors -/

/-- `r ⊗ (∑ᵢ aᵢ Dᵢ) = ∑ᵢ (r aᵢ) (1 ⊗ Dᵢ)` in `ℝ ⊗[ℤ] M`. -/
private theorem tmul_sum_zsmul {M ι : Type*} [AddCommGroup M] (r : ℝ) (s : Finset ι)
    (a : ι → ℤ) (D : ι → M) :
    r ⊗ₜ[ℤ] (∑ i ∈ s, a i • D i) = ∑ i ∈ s, (r * a i) • ((1 : ℝ) ⊗ₜ[ℤ] D i) := by
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℝ,
    show r ⊗ₜ[ℤ] D i = r • ((1 : ℝ) ⊗ₜ[ℤ] D i) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    smul_smul, mul_comm]

/-- A positive combination `∑_{j ∈ T} rⱼ ⊗ Aⱼ` over a nonempty finset, reindexed by `Fin m`. -/
private theorem exists_fin_sum_tmul {M ι : Type*} [AddCommGroup M] (Q : M → Prop)
    (T : Finset ι) (hT : T.Nonempty) (r : ι → ℝ) (A : ι → M) (hr : ∀ j ∈ T, 0 < r j)
    (hA : ∀ j ∈ T, Q (A j)) :
    ∃ (m : ℕ) (r' : Fin m → ℝ) (A' : Fin m → M), 1 ≤ m ∧ (∀ i, 0 < r' i) ∧ (∀ i, Q (A' i)) ∧
      ∑ j ∈ T, r j ⊗ₜ[ℤ] A j = ∑ i, r' i ⊗ₜ[ℤ] A' i := by
  refine ⟨T.card, fun i => r (T.equivFin.symm i), fun i => A (T.equivFin.symm i),
    Finset.card_pos.2 hT, fun i => hr _ (T.equivFin.symm i).2,
    fun i => hA _ (T.equivFin.symm i).2, ?_⟩
  rw [← Finset.sum_coe_sort T]
  exact (Equiv.sum_comp T.equivFin.symm (fun j : T => r j ⊗ₜ[ℤ] A j)).symm

/-- A positive combination of Cartier divisors positive on `NE̅(Y/X) \ {0}` is positive there. -/
private theorem intersectionNumber_pos_of_eq_sum_tmul (B : KCartierDivisor ℝ Y) {m : ℕ}
    (hm : 1 ≤ m) (r : Fin m → ℝ) (A : Fin m → Y.CartierDivisor) (hr : ∀ i, 0 < r i)
    (hA : ∀ i, ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 →
      0 < RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ (A i)) z)
    (hB : Finsupp.linearCombination ℝ (fun D : Y.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] D) B =
      ∑ i, r i ⊗ₜ[ℤ] A i)
    {z : RelativeNumericalCurveClasses sY f} (hz : z ∈ relativeClosedConeOfCurves sY f)
    (hz0 : z ≠ 0) : 0 < RelativeNumericalCurveClasses.intersectionNumber B z := by
  rw [intersectionNumber_eq_liftBaseChange, hB, map_sum]
  simp only [LinearMap.liftBaseChange_tmul, AddMonoidHom.coe_toIntLinearMap, smul_eq_mul]
  exact Finset.sum_pos (fun i _ => mul_pos (hr i) (hA i z hz hz0)) ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- **The rational approximation step.** When `N₁(Y/X)` is finite-dimensional, a real Cartier
divisor positive on `NE̅(Y/X) \ {0}` is a positive combination of Cartier divisors that are
themselves positive on `NE̅(Y/X) \ {0}`. -/
private theorem exists_sum_tmul_of_forall_pos
    [FiniteDimensional ℝ (RelativeNumericalCurveClasses sY f)] (B : KCartierDivisor ℝ Y)
    (hB : ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 →
      0 < RelativeNumericalCurveClasses.intersectionNumber B z) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (A : Fin m → Y.CartierDivisor), 1 ≤ m ∧ (∀ i, 0 < r i) ∧
      (∀ i, ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 <
        RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ (A i)) z) ∧
      Finsupp.linearCombination ℝ (fun D : Y.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] D) B =
        ∑ i, r i ⊗ₜ[ℤ] A i := by
  classical
  have hpos : ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 →
      0 < ∑ D ∈ B.support, B D * cartierPairing z D := fun z hz hz0 => by
    simpa only [intersectionNumber_eq_sum, Finsupp.sum] using hB z hz hz0
  by_cases hB0 : B = 0
  · subst hB0
    refine ⟨1, fun _ => 1, fun _ => 0, le_rfl, fun _ => one_pos, fun _ z hz hz0 => ?_, by simp⟩
    simpa using hpos z hz hz0
  obtain ⟨ε, hε, hpert⟩ := exists_pos_of_isClosed continuous_linearMap
    (K := (relativeClosedConeOfCurves sY f : Set (RelativeNumericalCurveClasses sY f)))
    (by simpa only [coe_relativeClosedConeOfCurves] using isClosed_closure)
    (fun z hz t ht => (relativeClosedConeOfCurves sY f).smul_mem ht.le hz)
    B.support (fun D => RelativeNumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ D)) B hpos
  obtain ⟨L, hL0, r, a, hr, ha, hra⟩ :=
    exists_rational_simplex B.support (Finsupp.support_nonempty_iff.2 hB0) B hε
  obtain ⟨m, r', A', hm, hr', hA', heq⟩ := exists_fin_sum_tmul
    (fun A => ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 < cartierPairing z A)
    B.support.insertNone ⟨none, by simp⟩ r (fun j => ∑ D ∈ B.support, a j D • D) hr
    fun j hj z hz hz0 => by
      have e : cartierPairing z (∑ D ∈ B.support, a j D • D) = L * ∑ D ∈ B.support,
          (a j D : ℝ) / L * cartierPairing z D := by
        rw [cartierPairing_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun D _ => by field_simp
      rw [e]
      exact mul_pos hL0 (hpert _ (ha j hj) z hz hz0)
  refine ⟨m, r', A', hm, hr', hA', heq ▸ ?_⟩
  simp only [tmul_sum_zsmul, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun D hD => ?_
  rw [← Finset.sum_smul, hra D hD]

end Pairing

end MMP.FourfoldProofs.MmpFoundationRelativeRealKleimanCharZeroProof

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

namespace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.FourfoldProofs.MmpFoundationRelativeRealKleimanCharZeroProof in
/-- **Relative Kleiman criterion for real Cartier divisors.** Let `k` be algebraically closed of
characteristic zero and `f : Y ⟶ X` a projective morphism of `k`-varieties. Then:
1. a real Cartier divisor `B` is a finite positive real combination of `f`-ample Cartier divisors
   if and only if `(z · B) > 0` for every nonzero `z` in the closed relative cone of curves
   `NE̅(Y/X)`;
2. hence two real Cartier divisors with the same degrees on `NE̅(Y/X)` are both or neither such
   combinations;
3. a Cartier divisor `D` with `1 · D` such a combination is `f`-ample. -/
@[mmp "lem_mmp_foundation_relative_real_kleiman_char_zero"]
public theorem exists_sum_tmul_isRelativelyAmple_iff_forall_relativeClosedConeOfCurves_pos
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]
    (f : Y ⟶ X) (hf : IsProjective f) (hfs : f ≫ sX = sY) :
    let IsAmpleCombination : KCartierDivisor ℝ Y → Prop := fun B =>
      ∃ (m : ℕ) (r : Fin m → ℝ) (A : Fin m → Y.CartierDivisor), 1 ≤ m ∧ (∀ i, 0 < r i) ∧
        (∀ i, IsRelativelyAmple f (MMP.CartierDivisor.sheaf (A i))) ∧
        Finsupp.linearCombination ℝ (fun D : Y.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] D) B =
          ∑ i, r i ⊗ₜ[ℤ] A i
    (∀ B : KCartierDivisor ℝ Y, IsAmpleCombination B ↔
      ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 →
        0 < RelativeNumericalCurveClasses.intersectionNumber B z) ∧
    (∀ B B' : KCartierDivisor ℝ Y,
      (∀ z ∈ relativeClosedConeOfCurves sY f,
        RelativeNumericalCurveClasses.intersectionNumber B z =
          RelativeNumericalCurveClasses.intersectionNumber B' z) →
      (IsAmpleCombination B ↔ IsAmpleCombination B')) ∧
    ∀ D : Y.CartierDivisor, IsAmpleCombination (KCartierDivisor.ofCartier ℝ D) →
      IsRelativelyAmple f (MMP.CartierDivisor.sheaf D) := by
  intro P
  have hcrit := fun D =>
    isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sX sY f hf hfs D
  have h1 : ∀ B, P B ↔ ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 →
      0 < RelativeNumericalCurveClasses.intersectionNumber B z := by
    refine fun B => ⟨fun ⟨m, r, A, hm, hr, hA, hB⟩ z hz hz0 =>
      intersectionNumber_pos_of_eq_sum_tmul B hm r A hr (fun i => (hcrit (A i)).1 (hA i)) hB hz
        hz0, fun hB => ?_⟩
    have : IsProper f := hf.isProper
    have := (RelativeNumericalCurveClasses.exists_linearEquiv_dual_of_isProper sY sX f hfs).1
    obtain ⟨m, r, A, hm, hr, hA, heq⟩ := exists_sum_tmul_of_forall_pos B hB
    exact ⟨m, r, A, hm, hr, fun i => (hcrit (A i)).2 (hA i), heq⟩
  refine ⟨h1, fun B B' h => ?_, fun D hD => (hcrit D).2 ((h1 _).1 hD)⟩
  rw [h1, h1]
  exact forall₂_congr fun z hz => by rw [h z hz]

end MMP.Mori

end
