module

public import MMP.Analysis.Complex.Coherent.OkaWeierstrassReduction
public import MMP.AlgebraicGeometry.AnalytificationStalk

/-!
# Oka coherence: the inductive step and the analytification

The assembly of the Weierstrass case of Oka's relation theorem, its induction on the dimension,
coherence of the sheaf of holomorphic functions on a complex manifold, and coherence of the
analytification's structure sheaf and of analytified coherent modules.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry MMP.Analytic
open scoped Manifold ContDiff

namespace MMP.Analytic.OkaCoherence

section Weierstrass

open Filter Topology

section Assembly

/-- **A generic direction.** Finitely many holomorphic functions not vanishing identically near
`x` are all non-zero along some line through `x` whose direction has non-zero last coordinate. -/
lemma exists_direction {m p : ℕ} {V : Set (Fin (m + 1) → ℂ)} (hV : IsOpen V)
    {x : Fin (m + 1) → ℂ} (hx : x ∈ V) (f : Fin p → (Fin (m + 1) → ℂ) → ℂ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) V) (S : Finset (Fin p))
    (hS : ∀ i ∈ S, ¬ ∀ᶠ y in 𝓝 x, f i y = 0) :
    ∃ v : Fin (m + 1) → ℂ, v (Fin.last m) ≠ 0 ∧
      ∀ i ∈ S, ¬ ∀ᶠ t in 𝓝 (0 : ℂ), f i (x + t • v) = 0 := by
  classical
  obtain ⟨r0, hr0, hBV⟩ := Metric.isOpen_iff.1 hV x hx
  set B := Metric.ball x r0 with hB
  have hfan : ∀ i, AnalyticOnNhd ℂ (f i) B := fun i =>
    (analyticOnNhd_of_differentiableOn' hV (hf i)).mono hBV
  have hBc : IsPreconnected B := (convex_ball x r0).isPreconnected
  have hzero : ∀ i ∈ S, ∀ U : Set (Fin (m + 1) → ℂ), IsOpen U → (U ∩ B).Nonempty →
      ∃ y ∈ U ∩ B, f i y ≠ 0 := by
    intro i hi U hU ⟨y0, hy0⟩
    by_contra hcon
    push Not at hcon
    have hev : f i =ᶠ[𝓝 y0] 0 :=
      Filter.eventually_of_mem ((hU.inter Metric.isOpen_ball).mem_nhds hy0) fun y hy => hcon y hy
    have heq := (hfan i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc hy0.2 hev
    exact hS i hi (Filter.eventually_of_mem (Metric.ball_mem_nhds x hr0) fun y hy => heq hy)
  let O : Fin p → Set (Fin (m + 1) → ℂ) := fun i =>
    if i ∈ S then (closure B)ᶜ ∪ (B ∩ f i ⁻¹' {0}ᶜ) else Set.univ
  have hOo : ∀ i, IsOpen (O i) := fun i => by
    simp only [O]
    split_ifs
    · exact isClosed_closure.isOpen_compl.union
        (((hf i).mono hBV).continuousOn.isOpen_inter_preimage Metric.isOpen_ball
          isOpen_compl_singleton)
    · exact isOpen_univ
  have hOd : ∀ i, Dense (O i) := fun i => by
    simp only [O]
    split_ifs with hi
    · refine dense_iff_inter_open.2 fun U hU ⟨y, hyU⟩ => ?_
      by_cases hyc : y ∈ closure B
      · obtain ⟨z, hzU, hzB⟩ := mem_closure_iff.1 hyc U hU hyU
        obtain ⟨w, hw, hfw⟩ := hzero i hi U hU ⟨z, hzU, hzB⟩
        exact ⟨w, hw.1, Or.inr ⟨hw.2, hfw⟩⟩
      · exact ⟨y, hyU, Or.inl hyc⟩
    · exact dense_univ
  have hH : Dense {y : Fin (m + 1) → ℂ | y (Fin.last m) ≠ x (Fin.last m)} :=
    (dense_compl_singleton (x (Fin.last m))).preimage (isOpenMap_eval (Fin.last m))
  have hD : Dense ((⋂ i, O i) ∩ {y : Fin (m + 1) → ℂ | y (Fin.last m) ≠ x (Fin.last m)}) :=
    (dense_iInter_of_isOpen hOo hOd).inter_of_isOpen_left hH (isOpen_iInter_of_finite hOo)
  obtain ⟨y, hyB, hyO, hyl⟩ := hD.inter_open_nonempty B Metric.isOpen_ball
    ⟨x, Metric.mem_ball_self hr0⟩
  have hyx : y ≠ x := by rintro rfl; exact hyl rfl
  refine ⟨y - x, by simpa [sub_eq_zero] using hyl, fun i hi hev => ?_⟩
  have hfy : f i y ≠ 0 := by
    have := Set.mem_iInter.1 hyO i
    simp only [O, if_pos hi] at this
    rcases this with h | h
    · exact absurd (subset_closure hyB) h
    · exact h.2
  have hv0 : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  set ρ := r0 / ‖y - x‖
  have hT : ∀ t ∈ Metric.ball (0 : ℂ) ρ, x + t • (y - x) ∈ B := fun t ht => by
    rw [hB, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    rw [Metric.mem_ball, dist_zero_right] at ht
    rwa [lt_div_iff₀ hv0] at ht
  have hgan : AnalyticOnNhd ℂ (fun t : ℂ => f i (x + t • (y - x))) (Metric.ball 0 ρ) :=
    fun t ht => by
      have hin : AnalyticAt ℂ (fun t : ℂ => x + t • (y - x)) t :=
        analyticAt_const.add (analyticAt_id.smul analyticAt_const)
      exact AnalyticAt.comp (g := f i) (f := fun t : ℂ => x + t • (y - x)) (hfan i _ (hT t ht)) hin
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, norm_one, lt_div_iff₀ hv0, one_mul, ← dist_eq_norm]
    exact hyB
  have := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 ρ).isPreconnected
    (Metric.mem_ball_self (div_pos hr0 hv0)) hev h1
  exact hfy (by simpa using this)

/-- A degree-`di` monic coefficient sequence padded with zeros up to degree `d` sums to
`w ^ di + ∑ m < di, a m * w ^ m`. -/
lemma sum_range_monic_coeff {R : Type*} [Semiring R] {d di : ℕ} (hdi : di ≤ d) (a : ℕ → R)
    (w : R) :
    ∑ m ∈ Finset.range (d + 1), (if m = di then 1 else if m < di then a m else 0) * w ^ m =
      w ^ di + ∑ m ∈ Finset.range di, a m * w ^ m := by
  rw [← Finset.sum_range_add_sum_Ico _ (show di ≤ d + 1 by omega), add_comm]
  congr 1
  · rw [Finset.sum_eq_single_of_mem di (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩)]
    · simp
    · intro m hm hne
      rw [Finset.mem_Ico] at hm
      rw [if_neg hne, if_neg (by omega), zero_mul]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [if_neg (by omega), if_pos hm]

variable {n : ℕ}

/-- The point `x + (z', w) ↦ x + (z' + w v', w vₙ)` of the change of coordinates. -/
noncomputable def chartMap (x v : Fin (n + 1) → ℂ) (z : (Fin n → ℂ) × ℂ) :
    Fin (n + 1) → ℂ :=
  x + Fin.snoc (z.1 + z.2 • Fin.init v) (z.2 * v (Fin.last n))

/-- The inverse of `chartMap`. -/
noncomputable def chartInv (x v : Fin (n + 1) → ℂ) (y : Fin (n + 1) → ℂ) :
    (Fin n → ℂ) × ℂ :=
  (Fin.init (y - x) - ((y - x) (Fin.last n) / v (Fin.last n)) • Fin.init v,
    (y - x) (Fin.last n) / v (Fin.last n))

/-- `chartInv x v` is a right inverse of `chartMap x v` when `v` has non-zero last coordinate. -/
lemma chartMap_chartInv (x v : Fin (n + 1) → ℂ) (hv : v (Fin.last n) ≠ 0)
    (y : Fin (n + 1) → ℂ) :
    chartMap x v (chartInv x v y) = y := by
  simp only [chartMap, chartInv, sub_add_cancel, div_mul_cancel₀ _ hv, Fin.snoc_init_self]
  abel

/-- `chartInv x v` is a left inverse of `chartMap x v` when `v` has non-zero last coordinate. -/
lemma chartInv_chartMap (x v : Fin (n + 1) → ℂ) (hv : v (Fin.last n) ≠ 0)
    (z : (Fin n → ℂ) × ℂ) :
    chartInv x v (chartMap x v z) = z := by
  simp only [chartMap, chartInv, add_sub_cancel_left, Fin.init_snoc, Fin.snoc_last,
    mul_div_cancel_right₀ _ hv, add_sub_cancel_right]

/-- The change of coordinates `chartMap x v` is complex differentiable. -/
lemma differentiable_chartMap (x v : Fin (n + 1) → ℂ) :
    Differentiable ℂ (chartMap x v) := by
  refine (differentiable_const _).add (differentiable_pi.2 fun j => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
    fun_prop
  · simp only [Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.init]
    fun_prop

/-- The inverse change of coordinates `chartInv x v` is complex differentiable. -/
lemma differentiable_chartInv (x v : Fin (n + 1) → ℂ) :
    Differentiable ℂ (chartInv x v) := by
  refine Differentiable.prodMk (differentiable_pi.2 fun i => ?_) ?_
  · simp only [Fin.init, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  · simp only [Pi.sub_apply]
    fun_prop

/-- `chartMap x v` sends `(0, t)` to the point `x + t • v` of the line through `x` in direction
`v`. -/
lemma chartMap_zero_snd (x v : Fin (n + 1) → ℂ) (t : ℂ) :
    chartMap x v (0, t) = x + t • v := by
  simp only [chartMap, zero_add]
  congr 1
  refine Fin.lastCases ?_ (fun i => ?_) (n := n) |> funext
  · simp [mul_comm]
  · simp [Fin.init]

/-- **The Weierstrass case of the inductive step of Oka's theorem.** -/
theorem generatedNear_of_forall_eq_zero
    (ih : ∀ q, HolomorphicRelationsLocallyFinite (Fin n → ℂ) q) {V : Set (Fin (n + 1) → ℂ)}
    (hV : IsOpen V) {p : ℕ} {F : Fin p → Fin 1 → (Fin (n + 1) → ℂ) → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) V) {x : Fin (n + 1) → ℂ} (hx : x ∈ V)
    (h0 : ∀ i, F i 0 x = 0) : HolomorphicRelationsGeneratedNear V F x := by
  classical
  by_cases hall : ∀ i, ∀ᶠ y in 𝓝 x, F i 0 y = 0
  · exact generatedNear_of_eventually_zero hV hx hall
  push Not at hall
  obtain ⟨i0, hi0⟩ := hall
  set Nz : Finset (Fin p) := Finset.univ.filter fun i => ¬ ∀ᶠ y in 𝓝 x, F i 0 y = 0 with hNz
  have hi0Nz : i0 ∈ Nz := by simp [hNz, hi0]
  obtain ⟨v, hvl, hline⟩ := exists_direction hV hx (fun i => F i 0) (fun i => hF i 0) Nz
    (fun i hi => (Finset.mem_filter.1 hi).2)
  set Φ := chartMap x v
  set Ψ := chartInv x v
  have hΦd := differentiable_chartMap x v
  have hΨd := differentiable_chartInv x v
  have hΦ0 : Φ 0 = x := by
    change chartMap x v (0, 0) = x
    simpa using chartMap_zero_snd x v 0
  have hΨx : Ψ x = 0 := by
    rw [← hΦ0]; exact chartInv_chartMap x v hvl 0
  have hVo : IsOpen (Φ ⁻¹' V) := hV.preimage hΦd.continuous
  have h0V : (0 : (Fin n → ℂ) × ℂ) ∈ Φ ⁻¹' V := by simpa [Set.mem_preimage, hΦ0] using hx
  set g : Fin p → (Fin n → ℂ) × ℂ → ℂ := fun i z => F i 0 (Φ z)
  have hgd : ∀ i, DifferentiableOn ℂ (g i) (Φ ⁻¹' V) := fun i =>
    (hF i 0).comp hΦd.differentiableOn (fun _ h => h)
  have hgan : ∀ i, AnalyticAt ℂ (g i) 0 := fun i =>
    analyticOnNhd_of_differentiableOn' hVo (hgd i) 0 h0V
  have hprep : ∀ i, ∃ (di : ℕ) (u : (Fin n → ℂ) × ℂ → ℂ) (a : ℕ → (Fin n → ℂ) → ℂ),
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
        g i =ᶠ[𝓝 0] fun z => u z * (if i ∈ Nz then z.2 ^ di +
          ∑ m ∈ Finset.range di, a m z.1 * z.2 ^ m else 0) := by
    intro i
    by_cases hi : i ∈ Nz
    · have hord : analyticOrderAt (fun t : ℂ => g i (0, t)) 0 ≠ ⊤ := by
        intro htop
        refine hline i hi ((analyticOrderAt_eq_top.1 htop).mono fun t ht => ?_)
        simpa [g, Φ, chartMap_zero_snd] using ht
      obtain ⟨di, hdi⟩ := ENat.ne_top_iff_exists.1 hord
      have hdi1 : 1 ≤ di := by
        rcases Nat.eq_zero_or_pos di with h | h
        · exfalso
          rw [h] at hdi
          rcases analyticOrderAt_eq_zero.1 hdi.symm with h' | h'
          · exact h' ((hgan i).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl)
          · exact h' (by simpa [g, Φ, chartMap_zero_snd] using h0 i)
        · exact h
      obtain ⟨u, a, ⟨hu, hu0, ha, hfa⟩, -⟩ :=
        MMP.Convergent.existsUnique_weierstrassPreparation hdi1 (hgan i) hdi.symm
      refine ⟨di, u, fun j => if h : j < di then a ⟨j, h⟩ else 0, hu, hu0, fun j => ?_, ?_⟩
      · dsimp only
        split_ifs
        · exact (ha _).1
        · exact analyticAt_const
      · filter_upwards [hfa] with z hz
        rw [hz, if_pos hi, Finset.sum_range]
        simp
    · refine ⟨0, 1, 0, analyticAt_const, one_ne_zero, fun _ => analyticAt_const, ?_⟩
      have hev : ∀ᶠ y in 𝓝 x, F i 0 y = 0 := by simpa [hNz] using hi
      have hcont : Tendsto Φ (𝓝 0) (𝓝 x) := hΦ0 ▸ hΦd.continuous.tendsto 0
      filter_upwards [hcont.eventually hev] with z hz
      simp [g, hz, hi]
  choose di u a hu hu0 ha hga using hprep
  set d := ∑ i, di i
  have hdid : ∀ i, di i ≤ d := fun i =>
    Finset.single_le_sum (f := di) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set c : Fin p → ℕ → (Fin n → ℂ) → ℂ := fun i m =>
    if i ∈ Nz then (if m = di i then (fun _ => 1) else if m < di i then a i m else 0) else 0
  have hcoefev : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ i, ∀ j : Fin (d + 1),
      DifferentiableAt ℂ (a i j) y :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      (ha i j).eventually_analyticAt.mono fun _ h => h.differentiableAt
  obtain ⟨W', hW'a, hW'o, h0W'⟩ := eventually_nhds_iff.1 hcoefev
  have hcd : ∀ i m, d < m → c i m = 0 := fun i m hm => by
    have := hdid i
    simp only [c]
    split_ifs <;> first | rfl | omega
  have hc : ∀ i m, DifferentiableOn ℂ (c i m) W' := fun i m => by
    by_cases hm : d < m
    · rw [hcd i m hm]
      exact differentiableOn_const _
    · simp only [c]
      split_ifs
      · exact differentiableOn_const _
      · exact fun y hy => (hW'a y hy i ⟨m, by omega⟩).differentiableWithinAt
      · exact differentiableOn_const _
      · exact differentiableOn_const _
  have hm1 : c i0 (di i0) = fun _ => 1 := by simp [c, hi0Nz]
  have hm0 : ∀ m, di i0 < m → c i0 m = 0 := fun m hm => by
    simp only [c, if_pos hi0Nz]
    rw [if_neg (by omega), if_neg (by omega)]
  have hP := polyRelations_generatedNear ih hW'o h0W' c hc hcd i0 (hdid i0) hm1 hm0 0
  have hNev : ∀ᶠ z in 𝓝 (0 : (Fin n → ℂ) × ℂ), z ∈ Φ ⁻¹' V ∧ ∀ i,
      DifferentiableAt ℂ (u i) z ∧ u i z ≠ 0 ∧ g i z = u i z * (if i ∈ Nz then z.2 ^ di i +
          ∑ m ∈ Finset.range (di i), a i m z.1 * z.2 ^ m else 0) :=
    (show ∀ᶠ z in 𝓝 (0 : (Fin n → ℂ) × ℂ), z ∈ Φ ⁻¹' V from hVo.mem_nhds h0V).and
      (Filter.eventually_all.2 fun i =>
      ((hu i).eventually_analyticAt.mono fun _ h => h.differentiableAt).and
        (((hu i).continuousAt.eventually_ne (hu0 i)).and (hga i)))
  obtain ⟨N0, hN0a, hN0o, h0N0⟩ := eventually_nhds_iff.1 hNev
  have hFG : ∀ i, ∀ z ∈ N0, F i 0 (Φ z) = u i z *
      ∑ m ∈ Finset.range (d + 1), c i m z.1 * z.2 ^ m := by
    intro i z hz
    refine ((hN0a z hz).2 i).2.2.trans ?_
    congr 1
    by_cases hi : i ∈ Nz
    · simp only [c, if_pos hi]
      rw [← sum_range_monic_coeff (hdid i) (fun m => a i m z.1) z.2]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> rfl
    · simp [c, hi]
  have hg := generatedNear_of_eq_mul hN0o (fun z hz => (hN0a z hz).1) h0N0
    (fun i z hz => ((hN0a z hz).2 i).1.differentiableWithinAt)
    (fun i z hz => ((hN0a z hz).2 i).2.1) (F := fun i j z => F i j (Φ z))
    (G := fun i (_ : Fin 1) (q : (Fin n → ℂ) × ℂ) =>
      ∑ m ∈ Finset.range (d + 1), c i m q.1 * q.2 ^ m) hFG (x := ((0 : Fin n → ℂ), (0 : ℂ))) hP
  refine generatedNear_of_comp Φ Ψ hΦd hΨd (chartMap_chartInv x v hvl) (chartInv_chartMap x v hvl)
    ?_
  rw [hΨx]
  exact hg

end Assembly

end Weierstrass

/-- **The inductive step of Oka's theorem.** If the relations among holomorphic vectors on
`ℂⁿ` are locally finitely generated, so are the relations among holomorphic functions on
`ℂⁿ⁺¹`: after a linear change of coordinates making the functions regular in the last variable,
Weierstrass preparation replaces them by Weierstrass polynomials, whose relations are generated
by polynomial relations of bounded degree, and the coefficients of these form the kernel of a
map of free modules over `ℂⁿ`. -/
theorem holomorphicRelationsLocallyFinite_pi_succ {n : ℕ}
    (ih : ∀ q, HolomorphicRelationsLocallyFinite (Fin n → ℂ) q) :
    HolomorphicRelationsLocallyFinite (Fin (n + 1) → ℂ) 1 := by
  intro V hV p F hF x hx
  by_cases hunit : ∃ i, F i 0 x ≠ 0
  · obtain ⟨i₀, h0⟩ := hunit
    exact holomorphicRelationsGeneratedNear_of_ne_zero hV hF hx i₀ h0
  push Not at hunit
  exact generatedNear_of_forall_eq_zero ih hV hF hx hunit

/-- **Oka's relation theorem** on `ℂⁿ`: finitely many holomorphic functions on an open subset of
`ℂⁿ` have, near every point, finitely many relations which locally generate all their
relations. -/
theorem holomorphicRelationsLocallyFinite_pi (n : ℕ) :
    HolomorphicRelationsLocallyFinite (Fin n → ℂ) 1 := by
  induction n with
  | zero => exact holomorphicRelationsLocallyFinite_pi_zero
  | succ n ih =>
    exact holomorphicRelationsLocallyFinite_pi_succ (holomorphicRelationsLocallyFinite_of_one ih)

/-- Oka's relation theorem on a complex manifold. -/
theorem relationsLocallyFinite_holomorphic (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] :
    RelationsLocallyFinite (holomorphicRingCatSheaf n M) 1 :=
  relationsLocallyFinite_of_holomorphic <|
    (holomorphicRelationsLocallyFinite_pi n).of_continuousLinearEquiv
      (EuclideanSpace.equiv (Fin n) ℂ).symm

/-- Oka's theorem proper: `𝒪_M` is a coherent sheaf of rings. -/
theorem isCoherentRing_holomorphicRingCatSheaf (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] :
    IsCoherentRing (holomorphicRingCatSheaf n M) :=
  isCoherentRing_of_relationsLocallyFinite (relationsLocallyFinite_holomorphic n M)

/-! ### The structure sheaf of the analytification -/

section Analytification

open Filter Topology TopologicalSpace
open MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.Analytic.Chart

section GermAlg

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function representing a holomorphic germ at `p` is complex differentiable at every point
near `p`. -/
lemma holGerms_eventually_differentiableAt {p : E} (g : holGerms p) {h : E → ℂ}
    (hg : (g : Germ (𝓝 p) ℂ) = h) : ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ h y := by
  obtain ⟨f, hf, hfd⟩ := g.2
  have hfh : f =ᶠ[𝓝 p] h := Germ.coe_eq.1 (hf.trans hg)
  filter_upwards [hfd, hfh.eventually_nhds] with y hy hy'
  exact hy.congr_of_eventuallyEq (Filter.EventuallyEq.symm hy')

/-- The underlying germ of `∑ i ∈ s, a i * b i` is the germ of `fun z ↦ ∑ i ∈ s, A i z * B i z`
when each `a i` and `b i` is the germ of `A i` and `B i` respectively. -/
lemma coe_sum_mul {q : E} {ι : Type} (s : Finset ι) (a b : ι → holGerms q)
    (A B : ι → E → ℂ) (ha : ∀ i, (a i : Germ (𝓝 q) ℂ) = A i)
    (hb : ∀ i, (b i : Germ (𝓝 q) ℂ) = B i) :
    ((∑ i ∈ s, a i * b i : holGerms q) : Germ (𝓝 q) ℂ) =
      ((fun z => ∑ i ∈ s, A i z * B i z : E → ℂ) : Germ (𝓝 q) ℂ) := by
  change (holGerms q).subtype _ = Germ.coeRingHom (𝓝 q) _
  rw [map_sum, show (fun z => ∑ i ∈ s, A i z * B i z) = ∑ i ∈ s, A i * B i from by
    ext; simp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul]
  change (a i : Germ (𝓝 q) ℂ) * (b i : Germ (𝓝 q) ℂ) = _
  rw [ha, hb]
  rfl

end GermAlg

/-- A germ combination equal near `q` to a combination of polynomials of `I` lies in `I 𝒪_q`. -/
lemma sum_mul_mem_map {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {p t : ℕ} (a g : Fin p → holGerms q) (A h : Fin p → (Fin n → ℂ) → ℂ)
    (ha : ∀ i, (a i : Germ (𝓝 q) ℂ) = A i) (hg : ∀ i, (g i : Germ (𝓝 q) ℂ) = h i)
    (b : Fin t → holGerms q) (B : Fin t → (Fin n → ℂ) → ℂ) (hb : ∀ j, (b j : Germ (𝓝 q) ℂ) = B j)
    (P : Fin t → MvPolynomial (Fin n) ℂ) (hP : ∀ j, P j ∈ I)
    (heq : ∀ᶠ z in 𝓝 q, ∑ i, A i z * h i z = ∑ j, B j z * MvPolynomial.eval z (P j)) :
    ∑ i, a i * g i ∈ I.map (polyGermHom q) := by
  have : ∑ i, a i * g i = ∑ j, b j * polyGermHom q (P j) := by
    apply Subtype.ext
    rw [coe_sum_mul _ _ _ _ _ ha hg, coe_sum_mul _ _ _ _ _ hb (fun j => coe_polyGermHom q (P j))]
    exact Germ.coe_eq.2 heq
  rw [this]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP j))

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

/-- Every `ℂ`-point lies in a chart. -/
lemma exists_chart (x : ComplexPoints sX) : ∃ c : Chart sX, x ∈ chart (sX := sX) c.U := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x.toScheme) (U := ⊤) trivial
  obtain ⟨c, hc⟩ := Chart.exists_eq (sX := sX) hU
  exact ⟨c, mem_chart_iff.2 (hc ▸ hxU)⟩

/-- A section over an open of a chart vanishes as soon as its components in that chart do. -/
lemma section_eq_zero {W : Opens (space sX)} (s : sections sX W) (c : Chart sX)
    (hW : ∀ y : W, y.1 ∈ chart (sX := sX) c.U) (h0 : ∀ y : W, s.1 y ⟨c, hW y⟩ = 0) : s = 0 := by
  apply Subtype.ext
  funext y d
  obtain ⟨W', hyW', hW', h⟩ := Chart.exists_eq_zero_of_apply_eq_zero s c y (hW y) (h0 y)
  exact h ⟨y.1, hyW'⟩ d

/-- **Sections from holomorphic functions in a chart.** A function holomorphic on an open `T` of
the coordinate space of a chart defines a section of `𝒪_{X^an}` over every open of the chart
whose coordinates lie in `T`. -/
theorem exists_section_of_differentiableOn (c : Chart sX) {T : Set (Fin c.n → ℂ)}
    (hTo : IsOpen T) {h : (Fin c.n → ℂ) → ℂ} (hhd : DifferentiableOn ℂ h T)
    (W : Opens (space sX)) (hWc : ∀ x : W, x.1 ∈ chart (sX := sX) c.U)
    (hWT : ∀ x : W, c.coords ⟨x.1, hWc x⟩ ∈ T) :
    ∃ s : sections sX W, ∀ (x : W) (g : holGerms (c.coords ⟨x.1, hWc x⟩)),
      (g : Germ (𝓝 (c.coords ⟨x.1, hWc x⟩)) ℂ) = h → s.1 x ⟨c, hWc x⟩ = StalkRing.mk c _ g := by
  have hhd' : ∀ q ∈ T, ∀ᶠ x in 𝓝 q, DifferentiableAt ℂ h x := fun q hq =>
    Filter.eventually_of_mem (hTo.mem_nhds hq) fun z hz => hhd.differentiableAt (hTo.mem_nhds hz)
  let germAt : ∀ x : W, c.StalkRing (c.coords ⟨x.1, hWc x⟩) := fun x =>
    StalkRing.mk c _ ⟨(h : Germ (𝓝 (c.coords ⟨x.1, hWc x⟩)) ℂ), coe_mem_holGerms (hhd' _ (hWT x))⟩
  let s₀ : ∀ x : W, Fibre x.1 := fun x d => transport c d.1 x.1 (hWc x) d.2 (germAt x)
  have hcompat : IsCompatible s₀ := fun _ _ m x hx =>
    transition_transport m x.1 (hWc x) hx (germAt x)
  have hhol : IsLocallyHolomorphic s₀ := by
    intro d x hx
    obtain ⟨f, e, he, hle, hz⟩ := exists_refinement d c x.1 (mem_chart_iff.1 hx)
      (mem_chart_iff.1 (hWc x))
    have hde : e.U ≤ d.U := he ▸ X.basicOpen_le f
    obtain ⟨G, Q, hGw, hQd, hQw, hinv⟩ := (ChartHom.ofLE d e hde).exists_inverse_of_eq_basicOpen he
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
    refine (transition_transport (ChartHom.ofLE d e hde) w.1 (hWc ⟨w.1, hwW⟩) w'.2
      (germAt ⟨w.1, hwW⟩)).trans ?_
    refine (transport_transition (ChartHom.ofLE c e hle) w.1 w'.2 (germAt ⟨w.1, hwW⟩)).trans ?_
    refine ((ChartHom.ofLE c e hle).transition_mk w' g₁).trans ?_
    exact (hright _).symm
  refine ⟨⟨s₀, hhol, hcompat⟩, fun x g hg => ?_⟩
  change transport c c x.1 (hWc x) (hWc x) (germAt x) = _
  rw [transport_self]
  exact congrArg (StalkRing.mk c _) (Subtype.ext hg.symm)

/-- The component in a chart at a point, on sections of `𝒪_{X^an}` as a sheaf of rings. -/
noncomputable abbrev compAt {W : Opens (space sX)} (y : W) (c : Chart sX)
    (hy : y.1 ∈ chart (sX := sX) c.U) :
    (ringCatSheaf sX).obj.obj (op W) →+* c.StalkRing (c.coords ⟨y.1, hy⟩) :=
  sectionComponent c y.1 hy W y.2

/-- The component of a restricted section at a point is the component of the section there. -/
lemma compAt_res {W W' : Opens (space sX)} (hW : W' ≤ W) (y : W') (c : Chart sX)
    (hy : y.1 ∈ chart (sX := sX) c.U) (s : (ringCatSheaf sX).obj.obj (op W)) :
    compAt y c hy (res hW s) = compAt ⟨y.1, hW y.2⟩ c hy s := rfl

/-- A section whose open set lies in a chart and whose components at every point vanish is zero. -/
lemma compAt_eq_zero {W : Opens (space sX)} (s : (ringCatSheaf sX).obj.obj (op W))
    (c : Chart sX) (hW : ∀ y : W, y.1 ∈ chart (sX := sX) c.U)
    (h0 : ∀ y : W, compAt y c (hW y) s = 0) :
    s = 0 :=
  section_eq_zero (W := W) s c hW h0

/-- **Relations among sections of `𝒪_{X^an}` are locally finitely generated.** -/
theorem relationsLocallyFinite_ringCatSheaf : RelationsLocallyFinite (ringCatSheaf sX) 1 := by
  classical
  intro V p F x hx
  set f : Fin p → sections sX V := fun i => F i 0
  obtain ⟨c, hxc⟩ := exists_chart x
  choose O hO hxO h hh using fun i => (f i).2.1 c ⟨x, hx⟩ hxc
  have hhx : ∀ i, ∀ᶠ z in 𝓝 (c.coords ⟨x, hxc⟩), DifferentiableAt ℂ (h i) z := fun i => by
    obtain ⟨-, g, hg, -⟩ := hh i ⟨x, hxc⟩ (hxO i)
    exact holGerms_eventually_differentiableAt g hg
  obtain ⟨t, gens, hgens⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian c.ideal)
  have hgensI : ∀ j, gens j ∈ c.ideal := fun j => hgens ▸ Submodule.subset_span ⟨j, rfl⟩
  let H : Fin (p + t) → Fin 1 → (Fin c.n → ℂ) → ℂ := fun k _ =>
    Fin.addCases h (fun j z => MvPolynomial.eval z (gens j)) k
  obtain ⟨Ω, hΩd, hΩo, hxΩ⟩ := eventually_nhds_iff.1 (Filter.eventually_all.2 hhx)
  have hHd : ∀ k j, DifferentiableOn ℂ (H k j) Ω := fun k j => by
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) k
    · simp only [H, Fin.addCases_left]
      exact fun z hz => (hΩd z hz i).differentiableWithinAt
    · simp only [H, Fin.addCases_right]
      exact (differentiable_eval_mvPolynomial _).differentiableOn
  obtain ⟨WE, hWEo, hWEΩ, hxWE, s, ρ, hρd, hρ, hgen⟩ :=
    holomorphicRelationsLocallyFinite_pi c.n Ω hΩo (p + t) H hHd _ hxΩ
  set O' : Set (chart (sX := sX) c.U) := (⋂ i, O i) ∩ c.coords ⁻¹' WE ∩ {y | y.1 ∈ V}
  have hO'o : IsOpen[chartTopology c.U] O' := by
    refine (chartTopology c.U).isOpen_inter _ _ ((chartTopology c.U).isOpen_inter _ _
      (@isOpen_iInter_of_finite _ _ (chartTopology c.U) _ _ hO)
      (@Continuous.isOpen_preimage _ _ (chartTopology c.U) _ _ c.continuous_coords _ hWEo))
      (isOpen_chart_inter ⟨c.U, c.isAffineOpen⟩ V)
  let W : Opens (space sX) := ⟨Subtype.val '' O', c.isOpen_image_val hO'o⟩
  have hWc : ∀ y : W, y.1 ∈ chart (sX := sX) c.U := fun y => by
    obtain ⟨o, -, ho⟩ := y.2
    exact ho ▸ o.2
  have hWO' : ∀ y : W, (⟨y.1, hWc y⟩ : chart (sX := sX) c.U) ∈ O' := fun y => by
    obtain ⟨o, ho, hoy⟩ := y.2
    have : (⟨y.1, hWc y⟩ : chart (sX := sX) c.U) = o := Subtype.ext hoy.symm
    rw [this]
    exact ho
  have hWV : W ≤ V := fun y hy => (hWO' ⟨y, hy⟩).2
  have hxW : x ∈ W := ⟨⟨x, hxc⟩, ⟨⟨Set.mem_iInter.2 hxO, hxWE⟩, hx⟩, rfl⟩
  have hrs : ∀ k (i : Fin p), ∃ r : (ringCatSheaf sX).obj.obj (op W),
      ∀ (y : W) (g : holGerms (c.coords ⟨y.1, hWc y⟩)),
      (g : Germ (𝓝 (c.coords ⟨y.1, hWc y⟩)) ℂ) = ρ k (Fin.castAdd t i) →
        compAt y c (hWc y) r = StalkRing.mk c _ g := fun k i => by
    obtain ⟨r, hr⟩ :=
      exists_section_of_differentiableOn c hWEo (hρd k _) W hWc (fun y => (hWO' y).1.2)
    exact ⟨r, hr⟩
  choose r hr using hrs
  have hmk_sum : ∀ {ι : Type} [Fintype ι] {q : Fin c.n → ℂ} (a b : ι → holGerms q),
      ∑ i, StalkRing.mk c q (a i) * StalkRing.mk c q (b i) = StalkRing.mk c q (∑ i, a i * b i) := by
    intro ι _ q a b
    rw [map_sum]
    simp only [map_mul]
  refine ⟨W, hWV, hxW, s, r, fun k j => ?_, fun U hUW a ha y hy => ?_⟩
  · -- the `rᵏ` are relations
    rw [Subsingleton.elim j 0]
    apply compAt_eq_zero _ c hWc
    intro y
    have hyO := (hWO' y).1.1
    have hyWE := (hWO' y).1.2
    choose hyV gf hgf hfy using fun i => hh i ⟨y.1, hWc y⟩ (Set.mem_iInter.1 hyO i)
    have hρev : ∀ m, ∀ᶠ z in 𝓝 (c.coords ⟨y.1, hWc y⟩), DifferentiableAt ℂ (ρ k m) z := fun m =>
      Filter.eventually_of_mem (hWEo.mem_nhds hyWE) fun z hz =>
        (hρd k m).differentiableAt (hWEo.mem_nhds hz)
    let gρ : Fin (p + t) → holGerms (c.coords ⟨y.1, hWc y⟩) := fun m =>
      ⟨(ρ k m : Germ _ ℂ), coe_mem_holGerms (hρev m)⟩
    rw [map_sum]
    have hterm : ∀ i, compAt y c (hWc y) (r k i * res hWV (F i 0)) =
        StalkRing.mk c _ (gρ (Fin.castAdd t i)) * StalkRing.mk c _ (gf i) := fun i => by
      rw [map_mul, compAt_res]
      exact congrArg₂ (· * ·) (hr k i y _ rfl) (hfy i)
    simp only [hterm, hmk_sum]
    refine StalkRing.mk_eq_zero_of_mem c ?_
    refine sum_mul_mem_map (fun i => gρ (Fin.castAdd t i)) gf _ h (fun i => rfl) hgf
      (fun j => -gρ (Fin.natAdd p j)) (fun j z => -ρ k (Fin.natAdd p j) z) (fun j => rfl)
      gens hgensI ?_
    filter_upwards [hWEo.mem_nhds hyWE] with z hz
    have := hρ k 0 z hz
    rw [Fin.sum_univ_add] at this
    simp only [H, Fin.addCases_left, Fin.addCases_right] at this
    simp only [neg_mul, Finset.sum_neg_distrib]
    linear_combination this
  · -- the `rᵏ` generate
    have hyW := hUW hy
    have hyc : y ∈ chart (sX := sX) c.U := hWc ⟨y, hyW⟩
    have hyO' := hWO' ⟨y, hyW⟩
    set q := c.coords ⟨y, hyc⟩
    choose Oa hOa hyOa α hα using fun i => (a i).2.1 c ⟨y, hy⟩ hyc
    choose hyU ga hga hay using fun i => hα i ⟨y, hyc⟩ (hyOa i)
    choose hyV gf hgf hfy using fun i => hh i ⟨y, hyc⟩ (Set.mem_iInter.1 hyO'.1.1 i)
    have hrel0 : ∑ i, ga i * gf i ∈ c.ideal.map (polyGermHom q) := by
      have := congrArg (compAt ⟨y, hy⟩ c hyc) (ha 0)
      rw [map_sum, map_zero] at this
      have hterm : ∀ i, compAt ⟨y, hy⟩ c hyc (a i * res (hUW.trans hWV) (F i 0)) =
          StalkRing.mk c _ (ga i) * StalkRing.mk c _ (gf i) := fun i => by
        rw [map_mul, compAt_res]
        exact congrArg₂ (· * ·) (hay i) (hfy i)
      simp only [hterm, hmk_sum] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have hmap : c.ideal.map (polyGermHom q) =
        Ideal.span (Set.range fun j => polyGermHom q (gens j)) := by
      rw [show c.ideal = Ideal.span (Set.range gens) from hgens.symm, Ideal.map_span,
        ← Set.range_comp]
      rfl
    rw [hmap] at hrel0
    obtain ⟨β, hβ⟩ := Ideal.mem_span_range_iff_exists_fun.1 hrel0
    choose B hB hBd using fun j => (β j).2
    have hαd : ∀ i, ∀ᶠ z in 𝓝 q, DifferentiableAt ℂ (α i) z := fun i =>
      holGerms_eventually_differentiableAt (ga i) (hga i)
    have heq : ∀ᶠ z in 𝓝 q, ∑ i, α i z * h i z = ∑ j, B j z * MvPolynomial.eval z (gens j) := by
      have h1 := coe_sum_mul Finset.univ ga gf α h hga hgf
      have h2 := coe_sum_mul Finset.univ β (fun j => polyGermHom q (gens j)) B
        (fun j z => MvPolynomial.eval z (gens j)) (fun j => (hB j).symm)
        (fun j => coe_polyGermHom q (gens j))
      rw [hβ] at h2
      exact Germ.coe_eq.1 (h1.symm.trans h2)
    obtain ⟨UE, hUEa, hUEo, hyUE⟩ := eventually_nhds_iff.1
      (((Filter.eventually_all.2 hαd).and (Filter.eventually_all.2 hBd)).and
        (heq.and (show ∀ᶠ z in 𝓝 q, z ∈ WE from hWEo.mem_nhds hyO'.1.2)))
    let a' : Fin (p + t) → (Fin c.n → ℂ) → ℂ := fun m =>
      Fin.addCases α (fun j z => -B j z) m
    have ha'd : ∀ m, DifferentiableOn ℂ (a' m) UE := fun m => by
      refine Fin.addCases (fun i => ?_) (fun j => ?_) m
      · simp only [a', Fin.addCases_left]
        exact fun z hz => ((hUEa z hz).1.1 i).differentiableWithinAt
      · simp only [a', Fin.addCases_right]
        exact fun z hz => ((hUEa z hz).1.2 j).neg.differentiableWithinAt
    have ha'rel : ∀ j, ∀ z ∈ UE, ∑ m, a' m z * H m j z = 0 := fun j z hz => by
      rw [Fin.sum_univ_add]
      simp only [a', H, Fin.addCases_left, Fin.addCases_right, neg_mul, Finset.sum_neg_distrib]
      rw [(hUEa z hz).2.1]
      ring
    obtain ⟨U'E, hU'Eo, hU'EUE, hyU'E, cc, hccd, hcc⟩ :=
      hgen UE hUEo (fun z hz => (hUEa z hz).2.2) a' ha'd ha'rel q hyUE
    set O'' : Set (chart (sX := sX) c.U) := (⋂ i, Oa i) ∩ c.coords ⁻¹' U'E ∩ {z | z.1 ∈ U}
    have hO''o : IsOpen[chartTopology c.U] O'' := by
      refine (chartTopology c.U).isOpen_inter _ _ ((chartTopology c.U).isOpen_inter _ _
        (@isOpen_iInter_of_finite _ _ (chartTopology c.U) _ _ hOa)
        (@Continuous.isOpen_preimage _ _ (chartTopology c.U) _ _ c.continuous_coords _ hU'Eo))
        (isOpen_chart_inter ⟨c.U, c.isAffineOpen⟩ U)
    let U' : Opens (space sX) := ⟨Subtype.val '' O'', c.isOpen_image_val hO''o⟩
    have hU'c : ∀ z : U', z.1 ∈ chart (sX := sX) c.U := fun z => by
      obtain ⟨o, -, ho⟩ := z.2
      exact ho ▸ o.2
    have hU'O'' : ∀ z : U', (⟨z.1, hU'c z⟩ : chart (sX := sX) c.U) ∈ O'' := fun z => by
      obtain ⟨o, ho, hoz⟩ := z.2
      have : (⟨z.1, hU'c z⟩ : chart (sX := sX) c.U) = o := Subtype.ext hoz.symm
      rw [this]
      exact ho
    have hU'U : U' ≤ U := fun z hz => (hU'O'' ⟨z, hz⟩).2
    have hyU' : y ∈ U' := ⟨⟨y, hyc⟩, ⟨⟨Set.mem_iInter.2 hyOa, hyU'E⟩, hy⟩, rfl⟩
    have hCs : ∀ k, ∃ C : (ringCatSheaf sX).obj.obj (op U'),
        ∀ (z : U') (g : holGerms (c.coords ⟨z.1, hU'c z⟩)),
        (g : Germ (𝓝 (c.coords ⟨z.1, hU'c z⟩)) ℂ) = cc k →
          compAt z c (hU'c z) C = StalkRing.mk c _ g := fun k => by
      obtain ⟨C, hC⟩ :=
        exists_section_of_differentiableOn c hU'Eo (hccd k) U' hU'c (fun z => (hU'O'' z).1.2)
      exact ⟨C, hC⟩
    choose C hC using hCs
    refine ⟨U', hU'U, hyU', C, fun i => ?_⟩
    rw [← sub_eq_zero]
    apply compAt_eq_zero _ c hU'c
    intro z
    obtain ⟨hzU, gaz, hgaz, hazz⟩ := hα i ⟨z.1, hU'c z⟩ (Set.mem_iInter.1 (hU'O'' z).1.1 i)
    have hzU'E := (hU'O'' z).1.2
    have hev : ∀ φ : (Fin c.n → ℂ) → ℂ, DifferentiableOn ℂ φ U'E →
        ∀ᶠ w in 𝓝 (c.coords ⟨z.1, hU'c z⟩), DifferentiableAt ℂ φ w := fun φ hφ =>
      Filter.eventually_of_mem (hU'Eo.mem_nhds hzU'E) fun w hw =>
        hφ.differentiableAt (hU'Eo.mem_nhds hw)
    let gc : Fin s → holGerms (c.coords ⟨z.1, hU'c z⟩) := fun k =>
      ⟨(cc k : Germ _ ℂ), coe_mem_holGerms (hev _ (hccd k))⟩
    let gr : Fin s → holGerms (c.coords ⟨z.1, hU'c z⟩) := fun k =>
      ⟨(ρ k (Fin.castAdd t i) : Germ _ ℂ), coe_mem_holGerms (hev _ ((hρd k _).mono
        (hU'EUE.trans fun w hw => (hUEa w hw).2.2)))⟩
    have hzW : z.1 ∈ W := hUW (hU'U z.2)
    rw [map_sub, map_sum, compAt_res]
    have hterm : ∀ k, compAt z c (hU'c z) (C k * res (hU'U.trans hUW) (r k i)) =
        StalkRing.mk c _ (gc k) * StalkRing.mk c _ (gr k) := fun k => by
      rw [map_mul, compAt_res]
      exact congrArg₂ (· * ·) (hC k z _ rfl) (hr k i ⟨z.1, hzW⟩ _ rfl)
    simp only [hterm, hmk_sum]
    rw [show compAt ⟨z.1, hU'U z.2⟩ c (hU'c z) (a i) = StalkRing.mk c _ gaz from hazz, ← map_sub]
    convert map_zero (StalkRing.mk c (c.coords ⟨z.1, hU'c z⟩)) using 2
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, coe_sum_mul _ gc gr _ _ (fun _ => rfl) (fun _ => rfl), hgaz,
      ZeroMemClass.coe_zero, ← Germ.coe_sub]
    refine Germ.coe_eq.2 (Filter.eventually_of_mem (hU'Eo.mem_nhds hzU'E) fun w hw => ?_)
    have := hcc (Fin.castAdd t i) w hw
    simp only [a', Fin.addCases_left] at this
    simp only [Pi.sub_apply, Pi.zero_apply, this, sub_self]

end Analytification

/-- The structure sheaf of `X^an` is coherent. -/
theorem isCoherentRing_ringCatSheaf (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] : IsCoherentRing (ringCatSheaf sX) :=
  isCoherentRing_of_relationsLocallyFinite (relationsLocallyFinite_ringCatSheaf (sX := sX))

/-- Analytification preserves coherence. -/
theorem isCoherentModule_analytifyModule (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (F : X.Modules) (hF : IsCoherentModule F) :
    IsCoherentModule ((analytifyModule sX).obj F) := by
  refine isCoherentModule_of_presentations
    (relationsLocallyFinite_ringCatSheaf (sX := sX)) fun y => ?_
  obtain ⟨U, hxU, P, hPg, hPr⟩ :=
    exists_presentation_of_isCoherentModule hF (Analytification.toSchemeHom sX y)
  obtain ⟨P', h1, h2⟩ :=
    exists_presentation_pullback (Analytification.toSchemeHom sX) (ringCatSheafHom sX) U F P
  exact ⟨(TopologicalSpace.Opens.map (Analytification.toSchemeHom sX)).obj U, hxU, P', h1, h2⟩

end MMP.Analytic.OkaCoherence
