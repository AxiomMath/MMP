module

public import MMP.Analysis.Complex.CauchyTransformRungeMontel

/-!
# Cartan's splitting of holomorphic matrices on adjacent blocks

A *block* in `ℂ^ι` is a product `∏ᵢ ([x₀ i, x₁ i] ×ℂ [y₀ i, y₁ i])` of closed rectangles
with sides parallel to the axes, possibly degenerate to segments or points. Cut a block `K`
by the real hyperplane `Re zᵢ₀ = a`, where `a` lies strictly inside the real side of the
factor `i₀`, into the two blocks `K' = K ∩ {Re zᵢ₀ ≤ a}` and `K'' = K ∩ {Re zᵢ₀ ≥ a}`, which
meet along `L = K' ∩ K''`. Cartan's lemma says that every invertible holomorphic matrix `g`
on a neighbourhood of `L` factors near `L` as `g = g' (g'')⁻¹`, where `g'` and `g''` are
invertible holomorphic matrices on neighbourhoods of `K'` and `K''`.

## Main results

* `MMP.Gaga.exists_eq_mul_inv_of_isUnit_of_differentiableOn_block`: Cartan's matrix splitting.

## Implementation notes

The coordinates are indexed by an arbitrary finite type `ι`, and the cut is along any
coordinate `i₀`; the source's `ℂⁿ` cut along the first coordinate is `ι = Fin n`, `i₀ = 0`.
The matrices are indexed by an arbitrary finite type `m`. A matrix-valued function is
holomorphic on an open set when each of its entries is; invertibility is pointwise
invertibility of the matrix. "Factors on a neighbourhood of `L`" is phrased with the filter
`𝓝ˢ L` of neighbourhoods of `L`.

The proof reduces to the case of a matrix uniformly close to the identity. An invertible
holomorphic `g` near a block containing `L` is a constant times a finite product of
exponentials of holomorphic matrices (logarithms of the ratios `g_{t_l}⁻¹ g_{t_{l+1}}` of
contractions of `g`), so Runge approximation of the exponents gives an entire invertible `P`
with `P⁻¹ g` close to `1`. The near-identity case is Cartan's iteration: for `f` holomorphic
near a rectangle `R` in the cut variable, the Cauchy integrals over the parts of `∂R` in
`Re ζ ≥ a` and `Re ζ ≤ a` are holomorphic off those parts, differ by `f` inside `R`, and are
bounded by `length (∂R) · sup ‖f‖ / η` at distance `η`. Starting from `h = 1 + F 0` on
shrinking rectangles, `1 + F (k + 1) = (1 + F⁺ k)⁻¹ (1 + F k) (1 + F⁻ k)` converges
quadratically to `1`, and the products of the factors `1 + F⁺ k`, `1 + F⁻ k` converge
uniformly to the required `g'`, `g''`. Holomorphy of the parametric edge integrals uses
differentiation under the integral sign for a `C¹` integrand (holomorphic functions of several
variables are analytic, by Osgood's lemma); holomorphy of the uniform limits uses the
several-variable Weierstrass theorem. Matrices carry the operator norm for the sup norm.

## References

* [H. Cartan, *Sur les matrices holomorphes de n variables complexes*]
-/

open Set Filter Topology Complex Uniformity

namespace MMP.Gaga

section Helpers

variable {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]

/-- `h` splits as `g' (g'')⁻¹` near `L = K' ∩ K''`, with `g'`, `g''` holomorphic and invertible
near `K'`, `K''`. -/
private def Splits (K : Set (ι → ℂ)) (i₀ : ι) (a : ℝ) (h : (ι → ℂ) → Matrix m m ℂ) : Prop :=
  ∃ (U' U'' : Set (ι → ℂ)) (g' g'' : (ι → ℂ) → Matrix m m ℂ),
      IsOpen U' ∧ K ∩ {z | (z i₀).re ≤ a} ⊆ U' ∧
      (∀ i j, DifferentiableOn ℂ (fun z => g' z i j) U') ∧ (∀ z ∈ U', IsUnit (g' z)) ∧
      IsOpen U'' ∧ K ∩ {z | a ≤ (z i₀).re} ⊆ U'' ∧
      (∀ i j, DifferentiableOn ℂ (fun z => g'' z i j) U'') ∧ (∀ z ∈ U'', IsUnit (g'' z)) ∧
      ∀ᶠ z in 𝓝ˢ (K ∩ {z | (z i₀).re ≤ a} ∩ (K ∩ {z | a ≤ (z i₀).re})),
        h z = g' z * (g'' z)⁻¹

section MatrixLog

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

omit [Fintype ι] in
/-- A holomorphic logarithm of matrices near `1`: there is an open neighbourhood `N` of `1` and
a holomorphic `lg` on `N` with `exp (lg y) = y`. -/
private theorem exists_matrix_log :
    ∃ N : Set (Matrix m m ℂ), IsOpen N ∧ (1 : Matrix m m ℂ) ∈ N ∧
      ∃ lg : Matrix m m ℂ → Matrix m m ℂ, DifferentiableOn ℂ lg N ∧
        ∀ y ∈ N, NormedSpace.exp (lg y) = y := by
  have hstrict : HasStrictFDerivAt (NormedSpace.exp : Matrix m m ℂ → Matrix m m ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix m m ℂ) : Matrix m m ℂ →L[ℂ] Matrix m m ℂ)) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  have hcd : ContDiffAt ℂ 1 (NormedSpace.exp : Matrix m m ℂ → Matrix m m ℂ) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (0 : Matrix m m ℂ)).contDiffAt
  have h1 := (hcd.to_localInverse hstrict.hasFDerivAt one_ne_zero).eventually (by simp)
  have h2 := (hcd.hasStrictFDerivAt' hstrict.hasFDerivAt one_ne_zero).eventually_right_inverse
  rw [NormedSpace.exp_zero] at h1 h2
  obtain ⟨N, hNsub, hNo, hN1⟩ := mem_nhds_iff.1 (h1.and h2)
  exact ⟨N, hNo, hN1, hcd.localInverse hstrict.hasFDerivAt one_ne_zero,
    fun y hy => ((hNsub hy).1.differentiableAt one_ne_zero).differentiableWithinAt,
    fun y hy => (hNsub hy).2⟩

end MatrixLog

section ExpRegularity

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem differentiable_matrix_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : E → Matrix m m ℂ} :
    Differentiable ℂ B ↔ ∀ i j, Differentiable ℂ (fun z => B z i j) := by
  constructor
  · intro hB i j
    exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable.comp hB
  · intro hB
    have : Differentiable ℂ (fun z => fun i j => B z i j) :=
      differentiable_pi.2 fun i => differentiable_pi.2 fun j => hB i j
    exact (LinearMap.toContinuousLinearMap
      ((Matrix.ofLinearEquiv ℂ : (m → m → ℂ) ≃ₗ[ℂ] Matrix m m ℂ) :
        (m → m → ℂ) →ₗ[ℂ] Matrix m m ℂ)).differentiable.comp this

-- Stated where the operator norm is in force, so that it can be used outside this section.
/-- The matrix exponential is continuous. -/
private theorem continuous_matrix_exp :
    Continuous (NormedSpace.exp : Matrix m m ℂ → Matrix m m ℂ) :=
  NormedSpace.exp_continuous

/-- The matrix exponential of an entrywise holomorphic matrix is entrywise holomorphic. -/
private theorem differentiable_exp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : E → Matrix m m ℂ} (hB : ∀ i j, Differentiable ℂ (fun z => B z i j)) (i j : m) :
    Differentiable ℂ (fun z => NormedSpace.exp (B z) i j) := by
  have hexp : Differentiable ℂ (NormedSpace.exp : Matrix m m ℂ → Matrix m m ℂ) :=
    fun x => (NormedSpace.exp_analytic x).differentiableAt
  exact differentiable_matrix_iff.1 (hexp.comp (differentiable_matrix_iff.2 hB)) i j

end ExpRegularity

private theorem list_prod_mul_prod_reverse {α M : Type*} [Monoid M] (L : List α) (a b : α → M)
    (h : ∀ x, a x * b x = 1) : (L.map a).prod * (L.reverse.map b).prod = 1 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (L.map a).prod, ih, one_mul, h]

/-- Points of a compact set `T` and points close to them have close images under a continuous
function of two variables, uniformly on `T`. -/
private theorem exists_mem_uniformity_diag {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    {F : X × X → Y} (hF : Continuous F) {T : Set X} (hT : IsCompact T) {r : Set (Y × Y)}
    (hr : r ∈ 𝓤 Y) : ∃ V ∈ 𝓤 X, ∀ x ∈ T, ∀ y, (x, y) ∈ V → (F (x, x), F (x, y)) ∈ r := by
  have hS : IsCompact ((fun x => (x, x)) '' T) := hT.image (continuous_id.prodMk continuous_id)
  have h := hS.uniformContinuousAt_of_continuousAt F (fun a _ => hF.continuousAt) hr
  rw [uniformity_prod] at h
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_inf_iff.1 h
  obtain ⟨V₁, hV₁, hV₁s⟩ := Filter.mem_comap.1 ht₁
  obtain ⟨V₂, hV₂, hV₂s⟩ := Filter.mem_comap.1 ht₂
  refine ⟨V₂, hV₂, fun x hx y hxy => ?_⟩
  have hp : ((x, x), (x, y)) ∈ t₁ ∩ t₂ :=
    ⟨hV₁s (refl_mem_uniformity hV₁), hV₂s hxy⟩
  rw [← hsub] at hp
  exact hp ⟨x, hx, rfl⟩

private theorem differentiableOn_mul_apply {s : Set (ι → ℂ)}
    {A B : (ι → ℂ) → Matrix m m ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (hB : ∀ i j, DifferentiableOn ℂ (fun z => B z i j) s) (i j : m) :
    DifferentiableOn ℂ (fun z => (A z * B z) i j) s := by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hA i k).mul (hB k j)

private theorem differentiable_list_prod_apply {α : Type*} (L : List α)
    {f : α → (ι → ℂ) → Matrix m m ℂ} (hf : ∀ l i j, Differentiable ℂ (fun z => f l z i j))
    (i j : m) : Differentiable ℂ fun z => (L.map fun l => f l z).prod i j := by
  induction L generalizing i j with
  | nil => simpa using differentiable_const _
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← differentiableOn_univ]
    exact differentiableOn_mul_apply (fun i j => (hf x i j).differentiableOn)
      (fun i j => (ih i j).differentiableOn) i j

private theorem list_prod_inverse_mul_telescope {M : Type*} [MonoidWithZero M] (u : ℕ → M) :
    ∀ k : ℕ, (∀ l ≤ k, IsUnit (u l)) →
      ((List.finRange k).map fun l : Fin k => Ring.inverse (u l) * u (l + 1)).prod =
        Ring.inverse (u 0) * u k
  | 0, hu => by simp [Ring.inverse_mul_cancel _ (hu 0 le_rfl)]
  | k + 1, hu => by
    rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map]
    have ih := list_prod_inverse_mul_telescope u k fun l hl => hu l (hl.trans k.le_succ)
    simp only [Function.comp_def, Fin.val_castSucc, Fin.val_last, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [ih, mul_assoc, ← mul_assoc (u k), Ring.mul_inverse_cancel _ (hu k k.le_succ), one_mul]

section ExpFactorization

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem differentiableOn_matrix_of_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {B : E → Matrix m m ℂ} {s : Set E}
    (hB : ∀ i j, DifferentiableOn ℂ (fun z => B z i j) s) : DifferentiableOn ℂ B s := by
  have : DifferentiableOn ℂ (fun z => fun i j => B z i j) s :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => hB i j
  exact (LinearMap.toContinuousLinearMap
    ((Matrix.ofLinearEquiv ℂ : (m → m → ℂ) ≃ₗ[ℂ] Matrix m m ℂ) :
      (m → m → ℂ) →ₗ[ℂ] Matrix m m ℂ)).differentiable.comp_differentiableOn this

/-- Logarithmic factorization: on a neighbourhood of a block
`∏ᵢ [u₀ i, u₁ i] ×ℂ [v₀ i, v₁ i] ⊆ U`, an invertible holomorphic
`g` is a constant invertible matrix times a finite product of exponentials of holomorphic
matrices. The factors are `log (g_{t_l}⁻¹ g_{t_{l+1}})` for the contractions
`g_t (z) = g (c + t (z - c))` towards a point `c` of the block. -/
private theorem exists_exp_factorization
    (g : (ι → ℂ) → Matrix m m ℂ) (U : Set (ι → ℂ)) (hU : IsOpen U)
    (hg : ∀ i j, DifferentiableOn ℂ (fun z => g z i j) U)
    (hgu : ∀ z ∈ U, IsUnit (g z)) (u₀ u₁ v₀ v₁ : ι → ℝ)
    (hLU : (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) ⊆ U) :
    ∃ (k : ℕ) (c₀ : (Matrix m m ℂ)ˣ) (W : Set (ι → ℂ)) (A : Fin k → (ι → ℂ) → Matrix m m ℂ),
      IsOpen W ∧ (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) ⊆ W ∧
      (∀ l i j, DifferentiableOn ℂ (fun z => A l z i j) W) ∧
      ∀ z ∈ W, g z = c₀ * ((List.finRange k).map fun l => NormedSpace.exp (A l z)).prod := by
  set S := (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) with hSdef
  rcases S.eq_empty_or_nonempty with hSe | ⟨c, hc⟩
  · exact ⟨0, 1, ∅, fun l => l.elim0, isOpen_empty, hSe.subset, fun l => l.elim0,
      fun z hz => absurd hz (notMem_empty z)⟩
  have hScpt : IsCompact S := isCompact_univ_pi fun i => isCompact_Icc.reProdIm isCompact_Icc
  have hSconv : Convex ℝ S := convex_pi fun i _ => by
    simpa [Complex.convexHull_reProdIm, (convex_Icc _ _).convexHull_eq] using
      convex_convexHull ℝ (Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i))
  obtain ⟨N, hNo, hN1, lg, hlg, hexplg⟩ := exists_matrix_log (m := m)
  have hgd : DifferentiableOn ℂ g U := differentiableOn_matrix_of_apply hg
  have hgc : ContinuousOn g U := hgd.continuousOn
  let φ : ℝ → (ι → ℂ) → (ι → ℂ) := fun t z => c + (t : ℂ) • (z - c)
  have hφS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ S, φ t z ∈ S := by
    intro t ht z hz
    have := hSconv hc hz (sub_nonneg.2 ht.2) ht.1 (by ring)
    convert this using 1
    ext i
    simp only [φ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hφd : ∀ t, Differentiable ℂ (φ t) := fun t =>
    (differentiable_const c).add ((differentiable_id.sub_const c).const_smul (t : ℂ))
  let Kc : Set (ℝ × (ι → ℂ)) := Icc 0 1 ×ˢ S
  have hKc : IsCompact Kc := isCompact_Icc.prod hScpt
  let G : ℝ × (ι → ℂ) → Matrix m m ℂ := fun p => g (φ p.1 p.2)
  have hφc : Continuous fun p : ℝ × (ι → ℂ) => φ p.1 p.2 :=
    continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).smul
      (continuous_snd.sub continuous_const))
  have hGc : ContinuousOn G Kc :=
    hgc.comp hφc.continuousOn fun p hp => hLU (hφS p.1 hp.1 p.2 hp.2)
  have hGu : ∀ p ∈ Kc, IsUnit (G p) := fun p hp => hgu _ (hLU (hφS p.1 hp.1 p.2 hp.2))
  have hHc : ContinuousOn (fun p => Ring.inverse (G p)) Kc := fun p hp => by
    have := NormedRing.inverse_continuousAt (hGu p hp).unit
    rw [IsUnit.unit_spec] at this
    exact this.comp_continuousWithinAt (hGc p hp)
  let Ψ : (ℝ × (ι → ℂ)) × (ℝ × (ι → ℂ)) → Matrix m m ℂ := fun q => Ring.inverse (G q.1) * G q.2
  have hΨc : ContinuousOn Ψ (Kc ×ˢ Kc) :=
    (hHc.comp continuousOn_fst fun q hq => hq.1).mul (hGc.comp continuousOn_snd fun q hq => hq.2)
  have hΨu := (hKc.prod hKc).uniformContinuousOn_of_continuous hΨc
  obtain ⟨ε, hε, hεN⟩ := Metric.isOpen_iff.1 hNo 1 hN1
  obtain ⟨δ, hδ, hδΨ⟩ := Metric.uniformContinuousOn_iff.1 hΨu ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set k := n + 1 with hkdef
  have hk : (0 : ℝ) < k := by positivity
  let τ : ℕ → ℝ := fun l => l / k
  have hτ : ∀ l ≤ k, τ l ∈ Icc (0 : ℝ) 1 := fun l hl =>
    ⟨by positivity, (div_le_one hk).2 (by exact_mod_cast hl)⟩
  let h : ℕ → (ι → ℂ) → Matrix m m ℂ := fun l z =>
    Ring.inverse (g (φ (τ l) z)) * g (φ (τ (l + 1)) z)
  let O : Set (ι → ℂ) := ⋂ l : Fin (k + 1), φ (τ l) ⁻¹' U
  have hOo : IsOpen O := isOpen_iInter_of_finite fun l => hU.preimage (hφd _).continuous
  have hOU : ∀ z ∈ O, ∀ l ≤ k, φ (τ l) z ∈ U := fun z hz l hl =>
    mem_iInter.1 hz ⟨l, Nat.lt_succ_of_le hl⟩
  have hhd : ∀ l < k, DifferentiableOn ℂ (h l) O := by
    intro l hl z hz
    have h1 : DifferentiableWithinAt ℂ (fun z => g (φ (τ l) z)) O z :=
      (hgd _ (hOU z hz l hl.le)).comp z (hφd _).differentiableAt.differentiableWithinAt
        fun w hw => hOU w hw l hl.le
    have h2 : DifferentiableWithinAt ℂ (fun z => g (φ (τ (l + 1)) z)) O z :=
      (hgd _ (hOU z hz (l + 1) hl)).comp z (hφd _).differentiableAt.differentiableWithinAt
        fun w hw => hOU w hw (l + 1) hl
    exact ((differentiableAt_inverse (hgu _ (hOU z hz l hl.le))).comp_differentiableWithinAt
      z h1).mul h2
  let W : Set (ι → ℂ) := O ∩ ⋂ l : Fin k, (O ∩ h l ⁻¹' N)
  have hWo : IsOpen W := hOo.inter (isOpen_iInter_of_finite fun l =>
    (hhd l l.2).continuousOn.isOpen_inter_preimage hOo hNo)
  have hSO : S ⊆ O := fun z hz => mem_iInter.2 fun l =>
    hLU (hφS _ (hτ l (Nat.lt_succ_iff.1 l.2)) z hz)
  have hhN : ∀ z ∈ S, ∀ l < k, h l z ∈ N := by
    intro z hz l hl
    have hp : ((τ l, z) : ℝ × (ι → ℂ)) ∈ Kc := ⟨hτ l hl.le, hz⟩
    have hq : ((τ (l + 1), z) : ℝ × (ι → ℂ)) ∈ Kc := ⟨hτ (l + 1) hl, hz⟩
    have hd : dist (((τ l, z), (τ l, z)) : (ℝ × (ι → ℂ)) × (ℝ × (ι → ℂ)))
        ((τ l, z), (τ (l + 1), z)) < δ := by
      have e : τ l - τ (l + 1) = -(1 / k) := by
        simp only [τ, Nat.cast_add, Nat.cast_one]; field_simp; ring
      have h1k : (0 : ℝ) < 1 / k := by positivity
      rw [Prod.dist_eq, dist_self, Prod.dist_eq, dist_self, Real.dist_eq, e, abs_neg,
        abs_of_pos h1k, max_eq_left h1k.le, max_eq_right h1k.le]
      rw [hkdef]; push_cast; exact hn
    have := hδΨ _ ⟨hp, hp⟩ _ ⟨hp, hq⟩ hd
    have h1 : Ψ ((τ l, z), (τ l, z)) = 1 := Ring.inverse_mul_cancel _ (hGu _ hp)
    rw [h1, dist_comm] at this
    exact hεN this
  refine ⟨k, (hgu c (hLU hc)).unit, W, fun l z => lg (h l z), hWo, fun z hz =>
    ⟨hSO hz, mem_iInter.2 fun l => ⟨hSO hz, hhN z hz l l.2⟩⟩, ?_, ?_⟩
  · intro l i j
    have hA : DifferentiableOn ℂ (fun z => lg (h l z)) W :=
      hlg.comp ((hhd l l.2).mono inter_subset_left) fun z hz => (mem_iInter.1 hz.2 l).2
    exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable
      |>.comp_differentiableOn hA
  · intro z hz
    have hmap : ((List.finRange k).map fun l : Fin k => NormedSpace.exp (lg (h l z))) =
        (List.finRange k).map fun l : Fin k => h l z :=
      List.map_congr_left fun l _ => hexplg _ (mem_iInter.1 hz.2 l).2
    rw [hmap]
    have ht := list_prod_inverse_mul_telescope (fun l => g (φ (τ l) z)) k
      fun l hl => hgu _ (hOU z hz.1 l hl)
    have e0 : φ (τ 0) z = c := by simp [φ, τ]
    have ek : φ (τ k) z = z := by
      simp only [φ, τ, div_self hk.ne', Complex.ofReal_one, one_smul]; abel
    simp only [e0, ek] at ht
    change _ = _ * ((List.finRange k).map fun l : Fin k =>
      Ring.inverse (g (φ (τ l) z)) * g (φ (τ (l + 1)) z)).prod
    rw [ht, IsUnit.unit_spec, ← mul_assoc, Ring.mul_inverse_cancel _ (hgu c (hLU hc)), one_mul]

end ExpFactorization

private theorem differentiable_finset_prod_apply {E κ : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset κ) {g : κ → E → ℂ} (h : ∀ j ∈ s, Differentiable ℂ (g j)) :
    Differentiable ℂ fun z => ∏ j ∈ s, g j z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem abs_sub_clamp_le {a b x t : ℝ} (hab : a ≤ b) (ht : 0 ≤ t) (h₁ : a - t ≤ x)
    (h₂ : x ≤ b + t) : |x - max a (min x b)| ≤ t := by
  rcases le_total x b with h | h
  · rw [min_eq_left h]
    rcases le_total a x with h' | h'
    · rw [max_eq_right h', sub_self, abs_zero]; exact ht
    · rw [max_eq_left h', abs_le]; constructor <;> linarith
  · rw [min_eq_right h, max_eq_right hab, abs_le]; constructor <;> linarith

/-- Runge approximation on a block: a function holomorphic near a block is uniformly
approximated on it by entire functions. -/
private theorem exists_entire_approx_scalar (f : (ι → ℂ) → ℂ) (W : Set (ι → ℂ))
    (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) (u₀ u₁ v₀ v₁ : ι → ℝ)
    (hLW : (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) ⊆ W) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : (ι → ℂ) → ℂ, Differentiable ℂ p ∧
      ∀ z ∈ (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)), ‖p z - f z‖ < δ := by
  set S := (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) with hSdef
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · exact ⟨0, differentiable_const 0, fun z hz => by
      rw [hSe] at hz; exact absurd hz (Set.notMem_empty z)⟩
  have hz₀' := fun i => Complex.mem_reProdIm.1 (hz₀ i (mem_univ i))
  have hu : ∀ i, u₀ i ≤ u₁ i := fun i => (hz₀' i).1.1.trans (hz₀' i).1.2
  have hv : ∀ i, v₀ i ≤ v₁ i := fun i => (hz₀' i).2.1.trans (hz₀' i).2.2
  have hScpt : IsCompact S := isCompact_univ_pi fun i => isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨δ', hδ', hthick⟩ := hScpt.exists_thickening_subset_open hW hLW
  set t := δ' / 4 with ht
  have ht0 : 0 ≤ t := by positivity
  set S' := (univ.pi fun i =>
    Icc (u₀ i - t) (u₁ i + t) ×ℂ Icc (v₀ i - t) (v₁ i + t)) with hS'def
  have hS'W : S' ⊆ W := by
    intro z hz
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨fun i => ⟨max (u₀ i) (min (z i).re (u₁ i)), max (v₀ i) (min (z i).im (v₁ i))⟩,
      fun i _ => Complex.mem_reProdIm.2 ⟨⟨le_max_left _ _, max_le (hu i) (min_le_right _ _)⟩,
        ⟨le_max_left _ _, max_le (hv i) (min_le_right _ _)⟩⟩, ?_⟩
    refine (dist_pi_lt_iff hδ').2 fun i => ?_
    have hzi := Complex.mem_reProdIm.1 (hz i (mem_univ i))
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    have h1 := abs_sub_clamp_le (hu i) ht0 hzi.1.1 hzi.1.2
    have h2 := abs_sub_clamp_le (hv i) ht0 hzi.2.1 hzi.2.2
    simp only [Complex.sub_re, Complex.sub_im]
    linarith
  set n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let π : (Fin n → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e i)
  let K : Fin n → Set ℂ := fun j =>
    Icc (u₀ (e.symm j) - t) (u₁ (e.symm j) + t) ×ℂ Icc (v₀ (e.symm j) - t) (v₁ (e.symm j) + t)
  have hKU : univ.pi K ⊆ π ⁻¹' W := by
    intro w hw
    apply hS'W
    intro i _
    have := hw (e i) (mem_univ _)
    simpa [K, π] using this
  obtain ⟨s, cf, hsβ, happ⟩ := (MMP.Gaga.cauchyTransform_runge_montel).2.1 n K ∅ 0
    (by simp)
    (fun j _ => Or.inl ⟨_, _, _, _, by linarith [hu (e.symm j)], by linarith [hv (e.symm j)],
      rfl⟩)
    (π ⁻¹' W) (f ∘ π) (hW.preimage π.continuous) hKU
    (hf.comp π.differentiableOn (fun w hw => hw)) δ hδ
  refine ⟨fun z => ∑ β ∈ s, cf β * ∏ j, ((fun j => z (e.symm j)) j - (0 : Fin n → ℂ) j) ^ β j,
    ?_, ?_⟩
  · refine Differentiable.fun_sum fun β hβ => (differentiable_const _).mul
      (differentiable_finset_prod_apply _ fun j _ => ?_)
    exact ((differentiable_apply (e.symm j)).sub_const _).zpow
      (Or.inr (hsβ β hβ j (notMem_empty j)))
  · intro z hz
    have hw : (fun j => z (e.symm j)) ∈ univ.pi K := fun j _ => by
      have hzj := Complex.mem_reProdIm.1 (hz (e.symm j) (mem_univ _))
      exact Complex.mem_reProdIm.2 ⟨⟨by linarith [hzj.1.1], by linarith [hzj.1.2]⟩,
        ⟨by linarith [hzj.2.1], by linarith [hzj.2.2]⟩⟩
    have hπw : π (fun j => z (e.symm j)) = z := funext fun i => by simp [π]
    have := happ _ hw
    rw [Function.comp_apply, hπw] at this
    rw [norm_sub_rev]
    exact this

/-- Approximation step: an invertible holomorphic `g` on an open set containing a block `L⁺`
is uniformly approximated on `L⁺` by an entire invertible matrix `P = Q⁻¹`, in the sense that
`Q g` is entrywise `ε`-close to `1` on `L⁺`. -/
private theorem exists_entire_approx
    (g : (ι → ℂ) → Matrix m m ℂ) (U : Set (ι → ℂ)) (hU : IsOpen U)
    (hg : ∀ i j, DifferentiableOn ℂ (fun z => g z i j) U)
    (hgu : ∀ z ∈ U, IsUnit (g z)) (u₀ u₁ v₀ v₁ : ι → ℝ)
    (hLU : (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P Q : (ι → ℂ) → Matrix m m ℂ,
      (∀ i j, Differentiable ℂ (fun z => P z i j)) ∧
      (∀ i j, Differentiable ℂ (fun z => Q z i j)) ∧
      (∀ z, P z * Q z = 1) ∧ (∀ z, Q z * P z = 1) ∧
      ∀ z ∈ (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)), ∀ i j,
        ‖(Q z * g z) i j - (1 : Matrix m m ℂ) i j‖ ≤ ε := by
  set S := (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) with hSdef
  obtain ⟨k, c₀, W, A, hW, hSW, hA, hgA⟩ :=
    exists_exp_factorization g U hU hg hgu u₀ u₁ v₀ v₁ hLU
  have hScpt : IsCompact S := isCompact_univ_pi fun i => isCompact_Icc.reProdIm isCompact_Icc
  let Φ : (Fin k → Matrix m m ℂ) → Matrix m m ℂ := fun x =>
    ((List.finRange k).map fun l => NormedSpace.exp (x l)).prod
  let Φ' : (Fin k → Matrix m m ℂ) → Matrix m m ℂ := fun x =>
    ((List.finRange k).reverse.map fun l => NormedSpace.exp (-x l)).prod
  have hexp1 : ∀ x : Matrix m m ℂ, NormedSpace.exp x * NormedSpace.exp (-x) = 1 := fun x => by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl x)), add_neg_cancel,
      NormedSpace.exp_zero]
  have hexp2 : ∀ x : Matrix m m ℂ, NormedSpace.exp (-x) * NormedSpace.exp x = 1 := fun x => by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl x)), neg_add_cancel,
      NormedSpace.exp_zero]
  have hΦΦ' : ∀ x, Φ x * Φ' x = 1 := fun x =>
    list_prod_mul_prod_reverse _ (fun l => NormedSpace.exp (x l))
      (fun l => NormedSpace.exp (-x l)) fun l => hexp1 _
  have hΦ'Φ : ∀ x, Φ' x * Φ x = 1 := fun x => by
    have h := list_prod_mul_prod_reverse (List.finRange k).reverse
      (fun l => NormedSpace.exp (-x l)) (fun l => NormedSpace.exp (x l)) fun l => hexp2 _
    rw [List.reverse_reverse] at h
    exact h
  have hΦc : Continuous Φ :=
    continuous_list_prod _ fun l _ => continuous_matrix_exp.comp (continuous_apply l)
  have hΦ'c : Continuous Φ' :=
    continuous_list_prod _ fun l _ => continuous_matrix_exp.comp (continuous_apply l).neg
  let F : (Fin k → Matrix m m ℂ) × (Fin k → Matrix m m ℂ) → Matrix m m ℂ :=
    fun p => Φ' p.2 * Φ p.1
  have hFc : Continuous F := (hΦ'c.comp continuous_snd).mul (hΦc.comp continuous_fst)
  let a : (ι → ℂ) → (Fin k → Matrix m m ℂ) := fun z l => A l z
  have hac : ContinuousOn a S := continuousOn_pi.2 fun l => continuousOn_pi.2 fun i =>
    continuousOn_pi.2 fun j => ((hA l i j).mono hSW).continuousOn
  have hT : IsCompact (a '' S) := hScpt.image_of_continuousOn hac
  let r : Set (Matrix m m ℂ × Matrix m m ℂ) := ⋂ i, ⋂ j, {p | dist (p.1 i j) (p.2 i j) < ε}
  have hr : r ∈ 𝓤 (Matrix m m ℂ) := by
    refine Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => ?_
    have hu : UniformContinuous fun M : Matrix m m ℂ => M i j :=
      (Pi.uniformContinuous_proj (fun _ => ℂ) j).comp (Pi.uniformContinuous_proj _ i)
    exact hu (Metric.dist_mem_uniformity hε)
  obtain ⟨V, hV, hVr⟩ := exists_mem_uniformity_diag hFc hT hr
  have hV' : V ∈ 𝓤 (Fin k → m → m → ℂ) := hV
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_uniformity_dist.1 hV'
  choose p hp hpS using fun l i j =>
    exists_entire_approx_scalar (fun z => A l z i j) W hW (hA l i j) u₀ u₁ v₀ v₁ hSW δ hδ
  let Bm : (ι → ℂ) → Fin k → Matrix m m ℂ := fun z l => Matrix.of fun i j => p l i j z
  refine ⟨fun z => (c₀ : Matrix m m ℂ) * Φ (Bm z), fun z => Φ' (Bm z) * c₀.inv,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [← differentiableOn_univ]
    exact differentiableOn_mul_apply (A := fun _ => (c₀ : Matrix m m ℂ))
      (B := fun z => Φ (Bm z)) (fun _ _ => differentiableOn_const _)
      (fun i j => (differentiable_list_prod_apply _
        (fun l => differentiable_exp_apply (fun i j => hp l i j)) i j).differentiableOn) i j
  · intro i j
    rw [← differentiableOn_univ]
    exact differentiableOn_mul_apply (A := fun z => Φ' (Bm z)) (B := fun _ => c₀.inv)
      (fun i j => (differentiable_list_prod_apply _
        (fun l => differentiable_exp_apply (B := fun z => -Bm z l)
          (fun i j => (hp l i j).neg)) i j).differentiableOn)
      (fun _ _ => differentiableOn_const _) i j
  · intro z
    change (c₀ : Matrix m m ℂ) * Φ (Bm z) * (Φ' (Bm z) * c₀.inv) = 1
    rw [mul_assoc, ← mul_assoc (Φ _), hΦΦ', one_mul, Units.val_inv]
  · intro z
    change Φ' (Bm z) * c₀.inv * ((c₀ : Matrix m m ℂ) * Φ (Bm z)) = 1
    rw [mul_assoc, ← mul_assoc (c₀.inv : Matrix m m ℂ), Units.inv_val, one_mul, hΦ'Φ]
  · intro z hz i j
    have key : Φ' (Bm z) * c₀.inv * g z = F (a z, Bm z) := by
      rw [hgA z (hSW hz), ← mul_assoc, mul_assoc _ (c₀.inv : Matrix m m ℂ), Units.inv_val,
        mul_one]
    have hd : dist (fun l (i j : m) => A l z i j) (fun l (i j : m) => p l i j z) < δ :=
      (dist_pi_lt_iff hδ).2 fun l => (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2
        fun j => by rw [dist_comm, dist_eq_norm]; exact hpS l i j z hz
    have hmem := hVr (a z) ⟨z, hz, rfl⟩ (Bm z) (hδV hd)
    have h1 : F (a z, a z) = 1 := hΦ'Φ _
    rw [h1] at hmem
    have := mem_iInter.1 (mem_iInter.1 hmem i) j
    simp only [mem_setOf_eq] at this
    rw [dist_comm, dist_eq_norm] at this
    change ‖(Φ' (Bm z) * c₀.inv * g z) i j - _‖ ≤ ε
    rw [key]
    exact this.le

section CartanIteration

open MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [DecidableEq ι]

private theorem analyticOnNhd_of_differentiableOn {H E : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : H → E} {Ω : Set H} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    AnalyticOnNhd ℂ f Ω := by
  set n := Module.finrank ℂ H
  let e : H ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  have h3 := (MMP.SeveralComplex.cauchy_osgood_laurent.{_, 0} E).2.2.1 n (e.symm ⁻¹' Ω) (f ∘ e.symm)
    (hΩ.preimage e.symm.continuous) (hf.continuousOn.comp e.symm.continuous.continuousOn
      fun _ h => h) (fun ζ hζ j => by
        have hd : DifferentiableAt ℂ f (e.symm (Function.update ζ j (ζ j))) := by
          rw [Function.update_eq_self]; exact hf.differentiableAt (hΩ.mem_nhds hζ)
        have hu : DifferentiableAt ℂ (fun w : ℂ => Function.update ζ j w) (ζ j) := by
          rw [differentiableAt_pi]
          intro i
          by_cases hi : i = j
          · subst hi; simpa using differentiableAt_id
          · simpa [Function.update_of_ne hi] using differentiableAt_const _
        exact hd.comp (ζ j) (e.symm.differentiableAt.comp (ζ j) hu))
  intro x hx
  have := h3.2.1 (e x) (by simpa using hx)
  have h' := this.comp (e.analyticAt x)
  simpa [Function.comp_def] using h'

private theorem differentiableOn_of_tendstoUniformlyOn {H E : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F : ℕ → H → E} {f : H → E} {Ω : Set H} (hΩ : IsOpen Ω)
    (hF : ∀ k, DifferentiableOn ℂ (F k) Ω) (hlim : TendstoUniformlyOn F f atTop Ω) :
    DifferentiableOn ℂ f Ω := by
  set n := Module.finrank ℂ H
  let e : H ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  have h6 := (MMP.SeveralComplex.cauchy_osgood_laurent.{_, 0} E).2.2.2.2.2 n atTop (e.symm ⁻¹' Ω)
    (fun k => F k ∘ e.symm) (f ∘ e.symm) (hΩ.preimage e.symm.continuous)
    (Eventually.of_forall fun k => (hF k).comp e.symm.differentiableOn fun _ h => h)
    (hlim.comp e.symm).tendstoLocallyUniformlyOn
  have := h6.comp e.differentiableOn (fun x hx => by simpa using hx)
  simpa [Function.comp_def] using this

/-- Holomorphy of a parametric interval integral with a `C¹` integrand. -/
private theorem differentiableAt_intervalIntegral {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G : (ι → ℂ) × ℂ → E} {Ω₂ : Set ((ι → ℂ) × ℂ)} (hΩ₂ : IsOpen Ω₂)
    (hG : ContDiffOn ℂ 1 G Ω₂) {γ : ℝ → ℂ} (hγ : Continuous γ) (s t : ℝ) {z₀ : ι → ℂ}
    (hz : ∀ x ∈ uIcc s t, (z₀, γ x) ∈ Ω₂) :
    DifferentiableAt ℂ (fun z => ∫ x in s..t, G (z, γ x)) z₀ := by
  set C := (fun x => (z₀, γ x)) '' uIcc s t
  have hC : IsCompact C := isCompact_uIcc.image (continuous_const.prodMk hγ)
  obtain ⟨δ, hδ, hδΩ⟩ := hC.exists_thickening_subset_open hΩ₂ (by
    rintro _ ⟨x, hx, rfl⟩; exact hz x hx)
  set r := δ / 2
  have hr : 0 < r := by positivity
  set C' := closedBall z₀ r ×ˢ (γ '' uIcc s t)
  have hC' : IsCompact C' := (isCompact_closedBall z₀ r).prod (isCompact_uIcc.image hγ)
  have hC'Ω : C' ⊆ Ω₂ := by
    rintro ⟨z, w⟩ ⟨hz', x, hx, rfl⟩
    apply hδΩ
    rw [Metric.mem_thickening_iff]
    refine ⟨(z₀, γ x), ⟨x, hx, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact (mem_closedBall.1 hz').trans_lt (by simp [r]; linarith)
  have hcont : ContinuousOn (fderiv ℂ G) Ω₂ := hG.continuousOn_fderiv_of_isOpen hΩ₂ le_rfl
  obtain ⟨B, hB⟩ := hC'.exists_bound_of_continuousOn (hcont.mono hC'Ω)
  have hGc : ContinuousOn G Ω₂ := hG.continuousOn
  have hmem : ∀ z ∈ closedBall z₀ r, ∀ x ∈ uIcc s t, (z, γ x) ∈ Ω₂ := fun z hz' x hx =>
    hC'Ω ⟨hz', x, hx, rfl⟩
  have hFc : ∀ z ∈ closedBall z₀ r, ContinuousOn (fun x => G (z, γ x)) (uIcc s t) :=
    fun z hz' => hGc.comp (continuous_const.prodMk hγ).continuousOn fun x hx => hmem z hz' x hx
  have hderiv : ∀ z ∈ closedBall z₀ r, ∀ x ∈ uIcc s t,
      HasFDerivAt (fun z => G (z, γ x))
        ((fderiv ℂ G (z, γ x)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ)) z := by
    intro z hz' x hx
    have h1 : HasFDerivAt G (fderiv ℂ G (z, γ x)) (z, γ x) :=
      ((hG.differentiableOn one_ne_zero).differentiableAt
        (hΩ₂.mem_nhds (hmem z hz' x hx))).hasFDerivAt
    exact h1.comp z ((hasFDerivAt_id z).prodMk (hasFDerivAt_const _ _))
  have hball : ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hsub : ball z₀ r ⊆ closedBall z₀ r := Metric.ball_subset_closedBall
  have hI : uIoc s t ⊆ uIcc s t := uIoc_subset_uIcc
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := volume) (bound := fun _ => B * ‖ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ‖)
    (F' := fun z x => (fderiv ℂ G (z, γ x)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ))
    hball ?_ ?_ ?_ ?_ ?_ ?_).differentiableAt
  · filter_upwards [hball] with z hz'
    exact ((hFc z (hsub hz')).mono hI).aestronglyMeasurable measurableSet_uIoc
  · exact (hFc z₀ (mem_closedBall_self hr.le)).intervalIntegrable
  · have : ContinuousOn (fun x => (fderiv ℂ G (z₀, γ x)).comp
        (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ)) (uIcc s t) :=
      ((hcont.comp (continuous_const.prodMk hγ).continuousOn fun x hx =>
        hmem z₀ (mem_closedBall_self hr.le) x hx).clm_comp continuousOn_const)
    exact (this.mono hI).aestronglyMeasurable measurableSet_uIoc
  · refine Eventually.of_forall fun x hx z hz' => ?_
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    gcongr
    exact hB _ ⟨hsub hz', x, hI hx, rfl⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun x hx z hz' => hderiv z (hsub hz') x (hI hx)

/-- The points whose `i₀`-th coordinate lies in `D` and whose other coordinates lie in `Ob`. -/
private def slab (i₀ : ι) (Ob : ι → Set ℂ) (D : Set ℂ) : Set (ι → ℂ) :=
  {z | z i₀ ∈ D ∧ ∀ i, i ≠ i₀ → z i ∈ Ob i}

private theorem isOpen_slab {i₀ : ι} {Ob : ι → Set ℂ} {D : Set ℂ} (hOb : ∀ i, IsOpen (Ob i))
    (hD : IsOpen D) : IsOpen (slab i₀ Ob D) := by
  have : slab i₀ Ob D = (fun z : ι → ℂ => z i₀) ⁻¹' D ∩ ⋂ i, ⋂ (_ : i ≠ i₀),
      (fun z : ι → ℂ => z i) ⁻¹' Ob i := by
    ext z; simp [slab]
  rw [this]
  exact (hD.preimage (continuous_apply i₀)).inter (isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun _ => (hOb i).preimage (continuous_apply i))

private theorem update_mem_slab {i₀ : ι} {Ob : ι → Set ℂ} {D : Set ℂ} {z : ι → ℂ} {ζ : ℂ} :
    Function.update z i₀ ζ ∈ slab i₀ Ob D ↔ ζ ∈ D ∧ ∀ i, i ≠ i₀ → z i ∈ Ob i := by
  simp only [slab, mem_setOf_eq, Function.update_self]
  exact and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => by
    rw [Function.update_of_ne hi]

private theorem slab_mono {i₀ : ι} {Ob : ι → Set ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    slab i₀ Ob D ⊆ slab i₀ Ob D' := fun _ hz => ⟨h hz.1, hz.2⟩

private theorem differentiable_update_pair (i₀ : ι) :
    Differentiable ℂ (fun p : (ι → ℂ) × ℂ => Function.update p.1 i₀ p.2) := by
  rw [differentiable_pi]
  intro i
  by_cases hi : i = i₀
  · subst hi; simpa using differentiable_snd
  · simp only [Function.update_of_ne hi]; fun_prop

/-- The Cauchy kernel in the `i₀`-th variable. -/
private noncomputable def kern (f : (ι → ℂ) → E) (i₀ : ι) (z : ι → ℂ) (ζ : ℂ) : E :=
  (ζ - z i₀)⁻¹ • f (Function.update z i₀ ζ)

/-- The closed rectangle `[a - ρ, a + ρ] × [c - ρ, d + ρ]`. -/
private def rectC (a c d ρ : ℝ) : Set ℂ := Icc (a - ρ) (a + ρ) ×ℂ Icc (c - ρ) (d + ρ)

/-- The open rectangle `(a - ρ, a + ρ) × (c - ρ, d + ρ)`. -/
private def rectO (a c d ρ : ℝ) : Set ℂ := Ioo (a - ρ) (a + ρ) ×ℂ Ioo (c - ρ) (d + ρ)

/-- The Cauchy integral of `f` over the part of `∂ (rectC a c d ρ)` in `Re ζ ≥ a`. -/
private noncomputable def splitP (f : (ι → ℂ) → E) (i₀ : ι) (a c d ρ : ℝ) (z : ι → ℂ) : E :=
  (2 * Real.pi * I : ℂ)⁻¹ • ((∫ x : ℝ in a..a + ρ, kern f i₀ z (x + ((c - ρ : ℝ) : ℂ) * I)) -
    (∫ x : ℝ in a..a + ρ, kern f i₀ z (x + ((d + ρ : ℝ) : ℂ) * I)) +
    I • ∫ y : ℝ in (c - ρ)..(d + ρ), kern f i₀ z (((a + ρ : ℝ) : ℂ) + y * I))

/-- Minus the Cauchy integral of `f` over the part of `∂ (rectC a c d ρ)` in `Re ζ ≤ a`. -/
private noncomputable def splitM (f : (ι → ℂ) → E) (i₀ : ι) (a c d ρ : ℝ) (z : ι → ℂ) : E :=
  -((2 * Real.pi * I : ℂ)⁻¹ • ((∫ x : ℝ in (a - ρ)..a, kern f i₀ z (x + ((c - ρ : ℝ) : ℂ) * I)) -
    (∫ x : ℝ in (a - ρ)..a, kern f i₀ z (x + ((d + ρ : ℝ) : ℂ) * I)) -
    I • ∫ y : ℝ in (c - ρ)..(d + ρ), kern f i₀ z (((a - ρ : ℝ) : ℂ) + y * I)))

private theorem mem_rectC {a c d ρ : ℝ} {ζ : ℂ} :
    ζ ∈ rectC a c d ρ ↔ (a - ρ ≤ ζ.re ∧ ζ.re ≤ a + ρ) ∧ (c - ρ ≤ ζ.im ∧ ζ.im ≤ d + ρ) := by
  simp [rectC, Complex.mem_reProdIm]

private theorem mem_rectO {a c d ρ : ℝ} {ζ : ℂ} :
    ζ ∈ rectO a c d ρ ↔ (a - ρ < ζ.re ∧ ζ.re < a + ρ) ∧ (c - ρ < ζ.im ∧ ζ.im < d + ρ) := by
  simp [rectO, Complex.mem_reProdIm]

/-- The point `x + y i` lies in `rectC a c d ρ` when `x` and `y` lie in its sides. -/
private theorem ofReal_add_mul_I_mem_rectC {a c d ρ x y : ℝ} (h₁ : a - ρ ≤ x) (h₂ : x ≤ a + ρ)
    (h₃ : c - ρ ≤ y) (h₄ : y ≤ d + ρ) : (x : ℂ) + (y : ℂ) * I ∈ rectC a c d ρ := by
  simp [mem_rectC, *]

private theorem isOpen_rectO (a c d ρ : ℝ) : IsOpen (rectO a c d ρ) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

private theorem rectC_subset_rectO {a c d r r' : ℝ} (h : r < r') :
    rectC a c d r ⊆ rectO a c d r' := fun ζ hζ => by
  rw [mem_rectC] at hζ; rw [mem_rectO]
  exact ⟨⟨by linarith [hζ.1.1], by linarith [hζ.1.2]⟩, by linarith [hζ.2.1], by linarith [hζ.2.2]⟩

private theorem rectO_subset_rectO {a c d r r' : ℝ} (h : r ≤ r') :
    rectO a c d r ⊆ rectO a c d r' := fun ζ hζ => by
  rw [mem_rectO] at hζ ⊢
  exact ⟨⟨by linarith [hζ.1.1], by linarith [hζ.1.2]⟩, by linarith [hζ.2.1], by linarith [hζ.2.2]⟩

private theorem rectC_subset_rectC {a c d r r' : ℝ} (h : r ≤ r') :
    rectC a c d r ⊆ rectC a c d r' := fun ζ hζ => by
  rw [mem_rectC] at hζ ⊢
  exact ⟨⟨by linarith [hζ.1.1], by linarith [hζ.1.2]⟩, by linarith [hζ.2.1], by linarith [hζ.2.2]⟩

private theorem rectO_subset_rectC {a c d r r' : ℝ} (h : r ≤ r') :
    rectO a c d r ⊆ rectC a c d r' := fun ζ hζ => by
  rw [mem_rectO] at hζ; rw [mem_rectC]
  exact ⟨⟨by linarith [hζ.1.1], by linarith [hζ.1.2]⟩, by linarith [hζ.2.1], by linarith [hζ.2.2]⟩

section Split

variable {f : (ι → ℂ) → E} {i₀ : ι} {Ob : ι → Set ℂ} {D : Set ℂ} {a c d ρ : ℝ}

private theorem continuousOn_kern (hf : ContinuousOn f (slab i₀ Ob D)) {z : ι → ℂ}
    (hz : ∀ i, i ≠ i₀ → z i ∈ Ob i) :
    ContinuousOn (kern f i₀ z) {ζ | ζ ∈ D ∧ ζ ≠ z i₀} := by
  intro ζ hζ
  have h1 : ContinuousWithinAt (fun ζ => f (Function.update z i₀ ζ)) {ζ | ζ ∈ D ∧ ζ ≠ z i₀} ζ :=
    (hf _ (update_mem_slab.2 ⟨hζ.1, hz⟩)).comp
      ((differentiable_update_pair i₀).continuous.comp
        (continuous_const.prodMk continuous_id)).continuousWithinAt
      fun w hw => update_mem_slab.2 ⟨hw.1, hz⟩
  have h2 : ContinuousWithinAt (fun ζ : ℂ => (ζ - z i₀)⁻¹) {ζ | ζ ∈ D ∧ ζ ≠ z i₀} ζ :=
    ((continuous_id.sub continuous_const).continuousAt.inv₀ (sub_ne_zero.2 hζ.2)).continuousWithinAt
  exact h2.smul h1

/-- Holomorphy of the edge integrals in all variables. -/
private theorem differentiableAt_edge (hD : IsOpen D) (hOb : ∀ i, IsOpen (Ob i))
    (hf : DifferentiableOn ℂ f (slab i₀ Ob D)) {γ : ℝ → ℂ} (hγ : Continuous γ) (s t : ℝ)
    {z₀ : ι → ℂ} (hz₀ : ∀ i, i ≠ i₀ → z₀ i ∈ Ob i) (hγD : ∀ x ∈ uIcc s t, γ x ∈ D)
    (hγz : ∀ x ∈ uIcc s t, γ x ≠ z₀ i₀) :
    DifferentiableAt ℂ (fun z => ∫ x in s..t, kern f i₀ z (γ x)) z₀ := by
  set Ω₂ : Set ((ι → ℂ) × ℂ) :=
    {p | Function.update p.1 i₀ p.2 ∈ slab i₀ Ob D ∧ p.2 - p.1 i₀ ≠ 0}
  have hφ := differentiable_update_pair (ι := ι) i₀
  have hΩ₂ : IsOpen Ω₂ := ((isOpen_slab hOb hD).preimage hφ.continuous).inter
    (isOpen_ne.preimage (continuous_snd.sub ((continuous_apply i₀).comp continuous_fst)))
  let G : (ι → ℂ) × ℂ → E := fun p => (p.2 - p.1 i₀)⁻¹ • f (Function.update p.1 i₀ p.2)
  have hGd : DifferentiableOn ℂ G Ω₂ := by
    intro p hp
    have h1 : DifferentiableWithinAt ℂ (fun p : (ι → ℂ) × ℂ => f (Function.update p.1 i₀ p.2))
        Ω₂ p :=
      (hf _ hp.1).comp p hφ.differentiableAt.differentiableWithinAt fun q hq => hq.1
    have h2 : DifferentiableAt ℂ (fun p : (ι → ℂ) × ℂ => (p.2 - p.1 i₀)⁻¹) p :=
      DifferentiableAt.inv (by fun_prop) hp.2
    exact h2.differentiableWithinAt.smul h1
  have hG : ContDiffOn ℂ 1 G Ω₂ :=
    (analyticOnNhd_of_differentiableOn hΩ₂ hGd).contDiffOn hΩ₂.uniqueDiffOn
  exact differentiableAt_intervalIntegral hΩ₂ hG hγ s t fun x hx =>
    ⟨update_mem_slab.2 ⟨hγD x hx, hz₀⟩, sub_ne_zero.2 (hγz x hx)⟩

private theorem norm_two_pi_I_inv_le : ‖(2 * Real.pi * I : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])

private theorem differentiableOn_splitP (hρ : 0 < ρ) (hcd : c ≤ d) (hD : IsOpen D)
    (hOb : ∀ i, IsOpen (Ob i)) (hRD : rectC a c d ρ ⊆ D)
    (hf : DifferentiableOn ℂ f (slab i₀ Ob D)) :
    DifferentiableOn ℂ (splitP f i₀ a c d ρ)
      (slab i₀ Ob {ζ | ζ.re < a + ρ ∧ c - ρ < ζ.im ∧ ζ.im < d + ρ}) := by
  intro z hz
  obtain ⟨⟨hz1, hz2, hz3⟩, hzO⟩ := hz
  have hab : a ≤ a + ρ := by linarith
  have hcd' : c - ρ ≤ d + ρ := by linarith
  have e1 := differentiableAt_edge (f := f) hD hOb hf
    (γ := fun x : ℝ => (x : ℂ) + ((c - ρ : ℝ) : ℂ) * I) (by fun_prop) a (a + ρ) hzO
    (fun x hx => hRD (by
      rw [uIcc_of_le hab] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have e2 := differentiableAt_edge (f := f) hD hOb hf
    (γ := fun x : ℝ => (x : ℂ) + ((d + ρ : ℝ) : ℂ) * I) (by fun_prop) a (a + ρ) hzO
    (fun x hx => hRD (by
      rw [uIcc_of_le hab] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have e3 := differentiableAt_edge (f := f) hD hOb hf
    (γ := fun y : ℝ => ((a + ρ : ℝ) : ℂ) + (y : ℂ) * I) (by fun_prop) (c - ρ) (d + ρ) hzO
    (fun x hx => hRD (by
      rw [uIcc_of_le hcd'] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.re h; simp at this; linarith)
  exact (((e1.sub e2).add (e3.const_smul I)).const_smul _).differentiableWithinAt

private theorem differentiableOn_splitM (hρ : 0 < ρ) (hcd : c ≤ d) (hD : IsOpen D)
    (hOb : ∀ i, IsOpen (Ob i)) (hRD : rectC a c d ρ ⊆ D)
    (hf : DifferentiableOn ℂ f (slab i₀ Ob D)) :
    DifferentiableOn ℂ (splitM f i₀ a c d ρ)
      (slab i₀ Ob {ζ | a - ρ < ζ.re ∧ c - ρ < ζ.im ∧ ζ.im < d + ρ}) := by
  intro z hz
  obtain ⟨⟨hz1, hz2, hz3⟩, hzO⟩ := hz
  have hab : a - ρ ≤ a := by linarith
  have hcd' : c - ρ ≤ d + ρ := by linarith
  have e1 := differentiableAt_edge (f := f) hD hOb hf
    (γ := fun x : ℝ => (x : ℂ) + ((c - ρ : ℝ) : ℂ) * I) (by fun_prop) (a - ρ) a hzO
    (fun x hx => hRD (by
      rw [uIcc_of_le hab] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have e2 := differentiableAt_edge (f := f) hD hOb hf
    (γ := fun x : ℝ => (x : ℂ) + ((d + ρ : ℝ) : ℂ) * I) (by fun_prop) (a - ρ) a hzO
    (fun x hx => hRD (by
      rw [uIcc_of_le hab] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have e3 := differentiableAt_edge (f := f) hD hOb hf
    (γ := fun y : ℝ => ((a - ρ : ℝ) : ℂ) + (y : ℂ) * I) (by fun_prop) (c - ρ) (d + ρ) hzO
    (fun x hx => hRD (by
      rw [uIcc_of_le hcd'] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.re h; simp at this; linarith)
  exact ((((e1.sub e2).sub (e3.const_smul I)).const_smul _).neg).differentiableWithinAt

private theorem norm_kern_le {D' : Set ℂ} {M η : ℝ} {z : ι → ℂ}
    (hz : ∀ i, i ≠ i₀ → z i ∈ Ob i) (hM : ∀ w ∈ slab i₀ Ob D', ‖f w‖ ≤ M) (hM0 : 0 ≤ M)
    (hη : 0 < η) {ζ : ℂ} (hζ : ζ ∈ D') (hd : η ≤ ‖ζ - z i₀‖) :
    ‖kern f i₀ z ζ‖ ≤ M / η := by
  rw [kern, norm_smul, norm_inv, div_eq_inv_mul]
  exact mul_le_mul (inv_anti₀ hη hd) (hM _ (update_mem_slab.2 ⟨hζ, hz⟩)) (norm_nonneg _)
    (inv_nonneg.2 hη.le)

private theorem norm_splitP_le (hρ : 0 < ρ) (hcd : c ≤ d) {M η : ℝ}
    (hM : ∀ w ∈ slab i₀ Ob (rectC a c d ρ), ‖f w‖ ≤ M) (hM0 : 0 ≤ M) (hη : 0 < η)
    {z : ι → ℂ} (hz : ∀ i, i ≠ i₀ → z i ∈ Ob i) (h1 : (z i₀).re ≤ a + ρ - η)
    (h2 : c - ρ + η ≤ (z i₀).im) (h3 : (z i₀).im ≤ d + ρ - η) :
    ‖splitP f i₀ a c d ρ z‖ ≤ (4 * ρ + (d - c)) * (M / η) := by
  have hab : a ≤ a + ρ := by linarith
  have hcd' : c - ρ ≤ d + ρ := by linarith
  have hMη : 0 ≤ M / η := div_nonneg hM0 hη.le
  have b1 : ‖∫ x : ℝ in a..a + ρ, kern f i₀ z (x + ((c - ρ : ℝ) : ℂ) * I)‖ ≤ M / η * ρ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + ρ)
      (C := M / η) (f := fun x : ℝ => kern f i₀ z (x + ((c - ρ : ℝ) : ℂ) * I)) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        refine norm_kern_le hz hM hM0 hη ?_ ?_
        · exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
            (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
        · refine le_trans ?_ (Complex.abs_im_le_norm _)
          simp only [ofReal_sub, sub_im, add_im, ofReal_im, mul_im, sub_re, ofReal_re, I_im,
            mul_one, sub_self, I_re, mul_zero, add_zero, zero_add]
          rw [abs_of_nonpos (by linarith)]
          linarith)
    simpa [abs_of_pos hρ] using this
  have b2 : ‖∫ x : ℝ in a..a + ρ, kern f i₀ z (x + ((d + ρ : ℝ) : ℂ) * I)‖ ≤ M / η * ρ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + ρ)
      (C := M / η) (f := fun x : ℝ => kern f i₀ z (x + ((d + ρ : ℝ) : ℂ) * I)) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        refine norm_kern_le hz hM hM0 hη ?_ ?_
        · exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
            (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
        · refine le_trans ?_ (Complex.abs_im_le_norm _)
          simp only [ofReal_add, sub_im, add_im, ofReal_im, mul_im, add_re, ofReal_re, I_im,
            mul_one, add_zero, I_re, mul_zero, zero_add]
          rw [abs_of_nonneg (by linarith)]
          linarith)
    simpa [abs_of_pos hρ] using this
  have b3 : ‖∫ y : ℝ in (c - ρ)..(d + ρ), kern f i₀ z (((a + ρ : ℝ) : ℂ) + y * I)‖ ≤
      M / η * (d + ρ - (c - ρ)) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c - ρ) (b := d + ρ)
      (C := M / η) (f := fun y : ℝ => kern f i₀ z (((a + ρ : ℝ) : ℂ) + y * I)) (fun x hx => by
        rw [uIoc_of_le hcd'] at hx
        refine norm_kern_le hz hM hM0 hη ?_ ?_
        · exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
            (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
        · refine le_trans ?_ (Complex.abs_re_le_norm _)
          simp only [ofReal_add, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
            mul_one, sub_self, add_zero]
          rw [abs_of_nonneg (by linarith)]
          linarith)
    rwa [abs_of_nonneg (by linarith)] at this
  rw [splitP, norm_smul]
  refine (mul_le_of_le_one_left (norm_nonneg _) norm_two_pi_I_inv_le).trans ?_
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) (by rw [norm_smul, Complex.norm_I, one_mul])).trans ?_
  nlinarith

private theorem norm_splitM_le (hρ : 0 < ρ) (hcd : c ≤ d) {M η : ℝ}
    (hM : ∀ w ∈ slab i₀ Ob (rectC a c d ρ), ‖f w‖ ≤ M) (hM0 : 0 ≤ M) (hη : 0 < η)
    {z : ι → ℂ} (hz : ∀ i, i ≠ i₀ → z i ∈ Ob i) (h1 : a - ρ + η ≤ (z i₀).re)
    (h2 : c - ρ + η ≤ (z i₀).im) (h3 : (z i₀).im ≤ d + ρ - η) :
    ‖splitM f i₀ a c d ρ z‖ ≤ (4 * ρ + (d - c)) * (M / η) := by
  have hab : a - ρ ≤ a := by linarith
  have hcd' : c - ρ ≤ d + ρ := by linarith
  have hMη : 0 ≤ M / η := div_nonneg hM0 hη.le
  have b1 : ‖∫ x : ℝ in (a - ρ)..a, kern f i₀ z (x + ((c - ρ : ℝ) : ℂ) * I)‖ ≤ M / η * ρ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a - ρ) (b := a)
      (C := M / η) (f := fun x : ℝ => kern f i₀ z (x + ((c - ρ : ℝ) : ℂ) * I)) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        refine norm_kern_le hz hM hM0 hη ?_ ?_
        · exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
            (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
        · refine le_trans ?_ (Complex.abs_im_le_norm _)
          simp only [ofReal_sub, sub_im, add_im, ofReal_im, mul_im, sub_re, ofReal_re, I_im,
            mul_one, sub_self, I_re, mul_zero, add_zero, zero_add]
          rw [abs_of_nonpos (by linarith)]
          linarith)
    simpa [abs_of_pos hρ] using this
  have b2 : ‖∫ x : ℝ in (a - ρ)..a, kern f i₀ z (x + ((d + ρ : ℝ) : ℂ) * I)‖ ≤ M / η * ρ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a - ρ) (b := a)
      (C := M / η) (f := fun x : ℝ => kern f i₀ z (x + ((d + ρ : ℝ) : ℂ) * I)) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        refine norm_kern_le hz hM hM0 hη ?_ ?_
        · exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
            (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
        · refine le_trans ?_ (Complex.abs_im_le_norm _)
          simp only [ofReal_add, sub_im, add_im, ofReal_im, mul_im, add_re, ofReal_re, I_im,
            mul_one, add_zero, I_re, mul_zero, zero_add]
          rw [abs_of_nonneg (by linarith)]
          linarith)
    simpa [abs_of_pos hρ] using this
  have b3 : ‖∫ y : ℝ in (c - ρ)..(d + ρ), kern f i₀ z (((a - ρ : ℝ) : ℂ) + y * I)‖ ≤
      M / η * (d + ρ - (c - ρ)) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c - ρ) (b := d + ρ)
      (C := M / η) (f := fun y : ℝ => kern f i₀ z (((a - ρ : ℝ) : ℂ) + y * I)) (fun x hx => by
        rw [uIoc_of_le hcd'] at hx
        refine norm_kern_le hz hM hM0 hη ?_ ?_
        · exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
            (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
        · refine le_trans ?_ (Complex.abs_re_le_norm _)
          simp only [ofReal_sub, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
            mul_one, sub_self, add_zero]
          rw [abs_of_nonpos (by linarith)]
          linarith)
    rwa [abs_of_nonneg (by linarith)] at this
  rw [splitM, norm_neg, norm_smul]
  refine (mul_le_of_le_one_left (norm_nonneg _) norm_two_pi_I_inv_le).trans ?_
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) (by rw [norm_smul, Complex.norm_I, one_mul])).trans ?_
  nlinarith

private theorem intervalIntegrable_kern (hf : ContinuousOn f (slab i₀ Ob D)) {z : ι → ℂ}
    (hz : ∀ i, i ≠ i₀ → z i ∈ Ob i) {γ : ℝ → ℂ} (hγ : Continuous γ) {s t : ℝ}
    (hγD : ∀ x ∈ uIcc s t, γ x ∈ D) (hγz : ∀ x ∈ uIcc s t, γ x ≠ z i₀) :
    IntervalIntegrable (fun x => kern f i₀ z (γ x)) volume s t :=
  ((continuousOn_kern hf hz).comp hγ.continuousOn fun x hx =>
    ⟨hγD x hx, hγz x hx⟩).intervalIntegrable

/-- The additive splitting `f = splitP f - splitM f` inside the rectangle, by Cauchy's formula. -/
private theorem splitP_sub_splitM (hρ : 0 < ρ) (hcd : c ≤ d) (hD : IsOpen D)
    (hRD : rectC a c d ρ ⊆ D) (hf : DifferentiableOn ℂ f (slab i₀ Ob D)) {z : ι → ℂ}
    (hz : z ∈ slab i₀ Ob (rectO a c d ρ)) :
    splitP f i₀ a c d ρ z - splitM f i₀ a c d ρ z = f z := by
  obtain ⟨hz1, hzO⟩ := hz
  have hupd : Differentiable ℂ (fun ζ : ℂ => Function.update z i₀ ζ) :=
    (differentiable_update_pair i₀).comp ((differentiable_const z).prodMk differentiable_id)
  have hdiff : DifferentiableOn ℂ (fun ζ => f (Function.update z i₀ ζ)) D :=
    hf.comp hupd.differentiableOn fun ζ hζ => update_mem_slab.2 ⟨hζ, hzO⟩
  have hint : z i₀ ∈ interior (rectC a c d ρ) := by
    rw [rectC, Complex.interior_reProdIm, interior_Icc, interior_Icc]; exact hz1
  have hz1' := hz1
  rw [rectO, Complex.mem_reProdIm] at hz1'
  obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hz1'
  have h1 := (MMP.SeveralComplex.cauchy_osgood_laurent.{_, 0} E).1 (rectC a c d ρ)
    (fun g => (∫ x : ℝ in (a - ρ)..(a + ρ), g (x + ((c - ρ : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in (a - ρ)..(a + ρ), g (x + ((d + ρ : ℝ) : ℂ) * I)) +
      I • (∫ y : ℝ in (c - ρ)..(d + ρ), g (((a + ρ : ℝ) : ℂ) + y * I)) -
      I • ∫ y : ℝ in (c - ρ)..(d + ρ), g (((a - ρ : ℝ) : ℂ) + y * I))
    (Or.inl ⟨⟨a - ρ, c - ρ⟩, ⟨a + ρ, d + ρ⟩, by dsimp; linarith, by dsimp; linarith, rfl, rfl⟩)
    D (fun ζ => f (Function.update z i₀ ζ)) hD hRD hdiff (z i₀) hint
  simp only [Function.update_eq_self] at h1
  have hfc := hf.continuousOn
  have hab : a - ρ ≤ a := by linarith
  have hab' : a ≤ a + ρ := by linarith
  have k1 := intervalIntegrable_kern hfc hzO (γ := fun x : ℝ => (x : ℂ) + ((c - ρ : ℝ) : ℂ) * I)
    (by fun_prop) (s := a - ρ) (t := a)
    (fun x hx => hRD (by
      rw [uIcc_of_le hab] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have k2 := intervalIntegrable_kern hfc hzO (γ := fun x : ℝ => (x : ℂ) + ((c - ρ : ℝ) : ℂ) * I)
    (by fun_prop) (s := a) (t := a + ρ)
    (fun x hx => hRD (by
      rw [uIcc_of_le hab'] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have k3 := intervalIntegrable_kern hfc hzO (γ := fun x : ℝ => (x : ℂ) + ((d + ρ : ℝ) : ℂ) * I)
    (by fun_prop) (s := a - ρ) (t := a)
    (fun x hx => hRD (by
      rw [uIcc_of_le hab] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have k4 := intervalIntegrable_kern hfc hzO (γ := fun x : ℝ => (x : ℂ) + ((d + ρ : ℝ) : ℂ) * I)
    (by fun_prop) (s := a) (t := a + ρ)
    (fun x hx => hRD (by
      rw [uIcc_of_le hab'] at hx
      exact ofReal_add_mul_I_mem_rectC (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])
          (by linarith [hx.1, hx.2]) (by linarith [hx.1, hx.2])))
    (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have s1 := intervalIntegral.integral_add_adjacent_intervals k1 k2
  have s2 := intervalIntegral.integral_add_adjacent_intervals k3 k4
  simp only [kern] at s1 s2
  rw [← s1, ← s2] at h1
  rw [← h1, splitP, splitM]
  simp only [kern]
  module

end Split

section NearOne

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem norm_matrix_le_of_entries (A : Matrix m m ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ i j, ‖A i j‖ ≤ ε) : ‖A‖ ≤ Fintype.card m * ε := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤
      (⟨Fintype.card m * ε, by positivity⟩ : NNReal) := by
    refine Finset.sup_le fun i _ => ?_
    refine NNReal.coe_le_coe.1 ?_
    push_cast
    refine (Finset.sum_le_card_nsmul _ _ ε fun j _ => h i j).trans ?_
    simp only [nsmul_eq_mul, Finset.card_univ]; exact le_rfl
  exact_mod_cast this

private theorem norm_one_matrix_le :
    ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty m with hm | hm
  · rw [Subsingleton.elim (1 : Matrix m m ℂ) 0, norm_zero]; exact zero_le_one
  · rw [norm_one]

private theorem isUnit_one_add_and_norm_inverse_le {R : Type*} [NormedRing R]
    [HasSummableGeomSeries R] (hR : ‖(1 : R)‖ ≤ 1) {p : R} (hp : ‖p‖ ≤ 1 / 2) :
    IsUnit (1 + p) ∧ ‖Ring.inverse (1 + p)‖ ≤ 2 := by
  have hu : IsUnit (1 + p) := by
    have h' : ‖-p‖ < 1 := by rw [norm_neg]; linarith
    refine ⟨Units.oneSub (-p) h', ?_⟩
    simp [sub_eq_add_neg]
  refine ⟨hu, ?_⟩
  set u := Ring.inverse (1 + p)
  have h1 : (1 + p) * u = 1 := Ring.mul_inverse_cancel _ hu
  have h2 : u = 1 - p * u := by
    have : u + p * u = 1 := by rw [← h1]; noncomm_ring
    rw [← this]; abel
  have h3 : ‖u‖ ≤ 1 + 1 / 2 * ‖u‖ := by
    calc ‖u‖ = ‖1 - p * u‖ := by rw [← h2]
      _ ≤ ‖(1 : R)‖ + ‖p * u‖ := norm_sub_le _ _
      _ ≤ 1 + ‖p‖ * ‖u‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ 1 + 1 / 2 * ‖u‖ := by gcongr
  linarith

/-- Uniform convergence of a product `∏ (1 + u k)` with `‖u k‖ ≤ 2⁻ᵏ⁻³`; the limit is within
`1 / 2` of `1`. -/
private theorem exists_tendstoUniformlyOn_prod {R X : Type*} [NormedRing R]
    [CompleteSpace R] (hR : ‖(1 : R)‖ ≤ 1) {s : Set X} (u : ℕ → X → R)
    (hu : ∀ k, ∀ x ∈ s, ‖u k x‖ ≤ (1 / 2 : ℝ) ^ (k + 3)) :
    ∃ g : X → R, TendstoUniformlyOn
      (fun k x => ((List.range k).map fun j => 1 + u j x).prod) g atTop s ∧
      ∀ x ∈ s, ‖g x - 1‖ ≤ 1 / 2 := by
  set A : ℕ → X → R := fun k x => ((List.range k).map fun j => 1 + u j x).prod with hA
  have hA0 : ∀ x, A 0 x = 1 := fun x => by simp [hA]
  have hAs : ∀ k x, A (k + 1) x = A k x * (1 + u k x) := fun k x => by
    simp only [hA]; rw [List.prod_range_succ]
  have hinv : ∀ k, ∀ x ∈ s, ‖A k x - 1‖ ≤ 1 / 2 - (1 / 2 : ℝ) ^ (k + 1) := by
    intro k x hx
    induction k with
    | zero => simp [hA0]
    | succ k ih =>
      have hAk : ‖A k x‖ ≤ 3 / 2 := by
        have := norm_le_norm_add_norm_sub' (A k x) 1
        have := hR
        have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
        linarith
      rw [hAs, mul_add, mul_one, add_sub_right_comm]
      have h4 := (norm_mul_le (A k x) (u k x)).trans
        (mul_le_mul hAk (hu k x hx) (norm_nonneg _) (by norm_num))
      have e : (1 / 2 : ℝ) ^ (k + 1 + 1) = (1 / 2) ^ (k + 1) / 2 := by ring
      have e' : (1 / 2 : ℝ) ^ (k + 3) = (1 / 2) ^ (k + 1) / 4 := by ring
      rw [e'] at h4
      rw [e]
      have h5 := norm_add_le (A k x - 1) (A k x * u k x)
      have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
      linarith
  have hdiff : ∀ k, ∀ x ∈ s, ‖A (k + 1) x - A k x‖ ≤ (1 / 2 : ℝ) / 2 / 2 ^ k := by
    intro k x hx
    have hAk : ‖A k x‖ ≤ 3 / 2 := by
      have := norm_le_norm_add_norm_sub' (A k x) 1
      have := hR
      have h := hinv k x hx
      have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
      linarith
    rw [hAs, mul_add, mul_one, add_sub_cancel_left]
    have h4 := (norm_mul_le (A k x) (u k x)).trans
      (mul_le_mul hAk (hu k x hx) (norm_nonneg _) (by norm_num))
    have : (1 / 2 : ℝ) / 2 / 2 ^ k = 2 * (1 / 2) ^ (k + 3) := by
      rw [pow_add, one_div_pow]; field_simp
    rw [this]
    have : (0 : ℝ) ≤ (1 / 2) ^ (k + 3) := by positivity
    linarith
  have hsum : Summable fun k : ℕ => (1 / 2 : ℝ) / 2 / 2 ^ k := (hasSum_geometric_two' _).summable
  have hT := tendstoUniformlyOn_tsum_nat hsum (f := fun k x => A (k + 1) x - A k x) hdiff
  refine ⟨fun x => 1 + ∑' k, (A (k + 1) x - A k x), ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
    intro ε hε
    filter_upwards [hT ε hε] with N hN x hx
    have : A N x = 1 + ∑ k ∈ Finset.range N, (A (k + 1) x - A k x) := by
      rw [Finset.sum_range_sub (fun k => A k x), hA0]; abel
    rw [this, dist_add_left]; exact hN x hx
  · intro x hx
    rw [add_sub_cancel_left]
    exact tsum_of_norm_bounded (hasSum_geometric_two' (1 / 2 : ℝ)) fun k => hdiff k x hx

private theorem differentiableOn_prod_range {S : Set (ι → ℂ)} (u : ℕ → (ι → ℂ) → Matrix m m ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (u j) S) (k : ℕ) :
    DifferentiableOn ℂ (fun z => ((List.range k).map fun j => 1 + u j z).prod) S := by
  induction k with
  | zero => simpa using differentiableOn_const _
  | succ k ih =>
    simp only [List.prod_range_succ]
    exact ih.mul ((hu k).const_add 1)

private theorem isUnit_of_norm_sub_one_le {A : Matrix m m ℂ} (h : ‖A - 1‖ ≤ 1 / 2) : IsUnit A := by
  have h' : ‖1 - A‖ < 1 := by rw [norm_sub_rev]; linarith
  exact ⟨Units.oneSub (1 - A) h', by simp⟩

/-- The near-identity splitting on slabs: a holomorphic `h` uniformly close to `1` near
`rectC a c d (2 μ)` satisfies `h g'' = g'` near the cut, with `g'`, `g''` holomorphic and
invertible on the half-strips `N'`, `N''`. The factors are the limits of the products of
`1 + splitP (F k)` and `1 + splitM (F k)` along Cartan's iteration
`1 + F (k + 1) = (1 + splitP (F k))⁻¹ (1 + F k) (1 + splitM (F k))`. -/
private theorem near_one_split (i₀ : ι)
    (Ob : ι → Set ℂ) (hOb : ∀ i, IsOpen (Ob i)) (a c d μ : ℝ) (hμ : 0 < μ) (hcd : c ≤ d)
    (h : (ι → ℂ) → Matrix m m ℂ)
    (hh : DifferentiableOn ℂ h (slab i₀ Ob (rectO a c d (3 * μ))))
    (hb : ∀ z ∈ slab i₀ Ob (rectO a c d (3 * μ)), ‖h z - 1‖ ≤ μ / (32 * (8 * μ + (d - c)))) :
    ∃ g' g'' : (ι → ℂ) → Matrix m m ℂ,
      DifferentiableOn ℂ g'
        (slab i₀ Ob {ζ | ζ.re < a + μ / 2 ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2}) ∧
      (∀ z ∈ slab i₀ Ob {ζ | ζ.re < a + μ / 2 ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2},
        IsUnit (g' z)) ∧
      DifferentiableOn ℂ g''
        (slab i₀ Ob {ζ | a - μ / 2 < ζ.re ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2}) ∧
      (∀ z ∈ slab i₀ Ob {ζ | a - μ / 2 < ζ.re ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2},
        IsUnit (g'' z)) ∧
      ∀ z ∈ slab i₀ Ob (rectO a c d (μ / 2)), h z * g'' z = g' z := by
  set ℓ := 8 * μ + (d - c) with hℓ
  have hℓ0 : 0 < ℓ := by rw [hℓ]; linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ρ = fun k => μ * (1 + (1 / 2) ^ k) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℝ, σ = fun k => μ * (1 + 3 / 2 * (1 / 2) ^ k) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℝ, η = fun k => μ * (1 / 2) ^ k / 4 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, T = fun k => (1 / 2) ^ (2 ^ k) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun k => μ * T k * (1 / 2) ^ k / (16 * ℓ) := ⟨_, rfl⟩
  have hr0 : ∀ k : ℕ, (0 : ℝ) < (1 / 2) ^ k := fun k => by positivity
  have hr1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hT0 : ∀ k, 0 ≤ T k := fun k => by rw [hT]; positivity
  have hT1 : ∀ k, T k ≤ 1 := fun k => by rw [hT]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have N1 : ∀ k, 0 < ρ k := fun k => by rw [hρ]; have := hr0 k; positivity
  have N2 : ∀ k, ρ k < σ k := fun k => by
    rw [hρ, hσ]; have := hr0 k; dsimp only; nlinarith
  have N3 : ∀ k, σ (k + 1) = ρ k - η k := fun k => by
    rw [hρ, hσ, hη]; dsimp only; rw [pow_succ]; ring
  have N5 : ∀ k, μ ≤ ρ k - η k := fun k => by
    rw [hρ, hη]; have := hr0 k; dsimp only; nlinarith
  have N6 : ∀ k, ρ k ≤ 2 * μ := fun k => by
    rw [hρ]; have := hr1 k; dsimp only; nlinarith
  have N8 : ∀ k, 0 < η k := fun k => by rw [hη]; have := hr0 k; positivity
  have N9 : ∀ k, 0 ≤ e k := fun k => by rw [he]; have := hT0 k; have := hr0 k; positivity
  have N10 : ∀ k, (4 * ρ k + (d - c)) * (e k / η k) ≤ T k / 4 := fun k => by
    have h1 : e k / η k = T k / (4 * ℓ) := by
      rw [he, hη]; dsimp only; have := hr0 k; field_simp; ring
    rw [h1]
    have h2 : 4 * ρ k + (d - c) ≤ ℓ := by have := N6 k; rw [hℓ]; linarith
    calc (4 * ρ k + (d - c)) * (T k / (4 * ℓ)) ≤ ℓ * (T k / (4 * ℓ)) := by
          gcongr; exact div_nonneg (hT0 k) (by positivity)
      _ = T k / 4 := by field_simp
  have N11 : ∀ k, T k / 4 ≤ (1 / 2 : ℝ) ^ (k + 3) := fun k => by
    have h1 : T k ≤ (1 / 2 : ℝ) ^ (k + 1) := by
      rw [hT]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_two_pow_self)
    have : (1 / 2 : ℝ) ^ (k + 3) = (1 / 2) ^ (k + 1) / 4 := by ring
    rw [this]; linarith
  have N13 : ∀ k, 2 * e k * (T k / 4) = e (k + 1) := fun k => by
    rw [he, hT]; dsimp only; rw [pow_succ 2 k, pow_mul, pow_succ (1 / 2 : ℝ) k]; ring
  set N' : Set ℂ := {ζ | ζ.re < a + μ / 2 ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2} with hN'
  set N'' : Set ℂ := {ζ | a - μ / 2 < ζ.re ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2} with hN''
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → (ι → ℂ) → Matrix m m ℂ, F 0 = (fun z => h z - 1) ∧
      ∀ k, F (k + 1) = fun z => Ring.inverse (1 + splitP (F k) i₀ a c d (ρ k) z) * F k z *
        splitM (F k) i₀ a c d (ρ k) z :=
    ⟨fun k => Nat.rec (fun z => h z - 1) (fun k Fk z => Ring.inverse
      (1 + splitP Fk i₀ a c d (ρ k) z) * Fk z * splitM Fk i₀ a c d (ρ k) z) k, rfl, fun k => rfl⟩
  have inv : ∀ k, DifferentiableOn ℂ (F k) (slab i₀ Ob (rectO a c d (σ k))) ∧
      ∀ z ∈ slab i₀ Ob (rectC a c d (ρ k)), ‖F k z‖ ≤ e k := by
    intro k
    induction k with
    | zero =>
      have hσ0 : σ 0 ≤ 3 * μ := by rw [hσ]; dsimp only; norm_num; linarith
      have hρ0 : ρ 0 < 3 * μ := by rw [hρ]; dsimp only; norm_num; linarith
      refine ⟨?_, fun z hz => ?_⟩
      · rw [hF0]
        exact (hh.mono (slab_mono (rectO_subset_rectO hσ0))).sub_const 1
      · rw [hF0]
        have : e 0 = μ / (32 * ℓ) := by rw [he, hT]; dsimp only; norm_num; ring_nf
        rw [this]
        exact hb z (slab_mono (rectC_subset_rectO hρ0) hz)
    | succ k ih =>
      have hRD : rectC a c d (ρ k) ⊆ rectO a c d (σ k) := rectC_subset_rectO (N2 k)
      have pd := differentiableOn_splitP (N1 k) hcd (isOpen_rectO a c d (σ k)) hOb hRD ih.1
      have qd := differentiableOn_splitM (N1 k) hcd (isOpen_rectO a c d (σ k)) hOb hRD ih.1
      have hS : ∀ z ∈ slab i₀ Ob (rectO a c d (σ (k + 1))),
          ‖splitP (F k) i₀ a c d (ρ k) z‖ ≤ T k / 4 ∧
            ‖splitM (F k) i₀ a c d (ρ k) z‖ ≤ T k / 4 := by
        intro z hz
        obtain ⟨hz1, hzO⟩ := hz
        rw [mem_rectO, N3] at hz1
        exact ⟨(norm_splitP_le (N1 k) hcd ih.2 (N9 k) (N8 k) hzO (by linarith [hz1.1.2])
            (by linarith [hz1.2.1]) (by linarith [hz1.2.2])).trans (N10 k),
          (norm_splitM_le (N1 k) hcd ih.2 (N9 k) (N8 k) hzO (by linarith [hz1.1.1])
            (by linarith [hz1.2.1]) (by linarith [hz1.2.2])).trans (N10 k)⟩
      have hT8 : T k / 4 ≤ 1 / 2 := by have := hT1 k; linarith
      have hsub : rectO a c d (σ (k + 1)) ⊆ rectO a c d (σ k) :=
        rectO_subset_rectO (by have := N2 (k + 1); have := N3 k; have := N8 k
                               have := N2 k; linarith)
      refine ⟨?_, fun z hz => ?_⟩
      · rw [hFs]
        intro z hz
        have hu := (isUnit_one_add_and_norm_inverse_le norm_one_matrix_le ((hS z hz).1.trans hT8)).1
        have hz' := hz
        obtain ⟨hz1, hzO⟩ := hz'
        rw [mem_rectO, N3] at hz1
        have hP : z ∈ slab i₀ Ob {ζ | ζ.re < a + ρ k ∧ c - ρ k < ζ.im ∧ ζ.im < d + ρ k} :=
          ⟨⟨by linarith [hz1.1.2, N8 k], by linarith [hz1.2.1, N8 k],
            by linarith [hz1.2.2, N8 k]⟩, hzO⟩
        have hM : z ∈ slab i₀ Ob {ζ | a - ρ k < ζ.re ∧ c - ρ k < ζ.im ∧ ζ.im < d + ρ k} :=
          ⟨⟨by linarith [hz1.1.1, N8 k], by linarith [hz1.2.1, N8 k],
            by linarith [hz1.2.2, N8 k]⟩, hzO⟩
        have h1 : DifferentiableWithinAt ℂ (fun z => 1 + splitP (F k) i₀ a c d (ρ k) z)
            (slab i₀ Ob (rectO a c d (σ (k + 1)))) z :=
          ((pd z hP).const_add 1).mono fun w hw => by
            obtain ⟨hw1, hwO⟩ := hw
            rw [mem_rectO, N3] at hw1
            exact ⟨⟨by linarith [hw1.1.2, N8 k], by linarith [hw1.2.1, N8 k],
              by linarith [hw1.2.2, N8 k]⟩, hwO⟩
        have h2 : DifferentiableWithinAt ℂ (splitM (F k) i₀ a c d (ρ k))
            (slab i₀ Ob (rectO a c d (σ (k + 1)))) z :=
          (qd z hM).mono fun w hw => by
            obtain ⟨hw1, hwO⟩ := hw
            rw [mem_rectO, N3] at hw1
            exact ⟨⟨by linarith [hw1.1.1, N8 k], by linarith [hw1.2.1, N8 k],
              by linarith [hw1.2.2, N8 k]⟩, hwO⟩
        have h3 : DifferentiableWithinAt ℂ (F k) (slab i₀ Ob (rectO a c d (σ (k + 1)))) z :=
          (ih.1 z (slab_mono hsub hz)).mono (slab_mono hsub)
        exact (((differentiableAt_inverse hu).comp_differentiableWithinAt z h1).mul h3).mul h2
      · have hz' : z ∈ slab i₀ Ob (rectO a c d (σ (k + 1))) :=
          slab_mono (rectC_subset_rectO (N2 (k + 1))) hz
        have hzk : z ∈ slab i₀ Ob (rectC a c d (ρ k)) :=
          slab_mono (rectC_subset_rectC (by
            rw [hρ]; dsimp only; have := hr0 k; rw [pow_succ]; nlinarith)) hz
        have hinv := (isUnit_one_add_and_norm_inverse_le norm_one_matrix_le
          ((hS z hz').1.trans hT8)).2
        rw [hFs, ← N13]
        dsimp only
        calc ‖Ring.inverse (1 + splitP (F k) i₀ a c d (ρ k) z) * F k z *
              splitM (F k) i₀ a c d (ρ k) z‖
            ≤ ‖Ring.inverse (1 + splitP (F k) i₀ a c d (ρ k) z)‖ * ‖F k z‖ *
              ‖splitM (F k) i₀ a c d (ρ k) z‖ :=
              (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
          _ ≤ 2 * e k * (T k / 4) :=
              mul_le_mul (mul_le_mul hinv (ih.2 z hzk) (norm_nonneg _) (by norm_num))
                (hS z hz').2 (norm_nonneg _) (by have := N9 k; positivity)
  have hT8 : ∀ k, T k / 4 ≤ 1 / 2 := fun k => by have := hT1 k; linarith
  have hσρ : ∀ k, σ (k + 1) ≤ ρ k := fun k => by have := N3 k; have := N8 k; linarith
  have hσk : ∀ k, σ (k + 1) ≤ σ k := fun k => (hσρ k).trans (N2 k).le
  have hPb : ∀ k z, (∀ i, i ≠ i₀ → z i ∈ Ob i) → (z i₀).re ≤ a + ρ k - η k →
      c - ρ k + η k ≤ (z i₀).im → (z i₀).im ≤ d + ρ k - η k →
      ‖splitP (F k) i₀ a c d (ρ k) z‖ ≤ T k / 4 := fun k z hz h1 h2 h3 =>
    (norm_splitP_le (N1 k) hcd (inv k).2 (N9 k) (N8 k) hz h1 h2 h3).trans (N10 k)
  have hQb : ∀ k z, (∀ i, i ≠ i₀ → z i ∈ Ob i) → a - ρ k + η k ≤ (z i₀).re →
      c - ρ k + η k ≤ (z i₀).im → (z i₀).im ≤ d + ρ k - η k →
      ‖splitM (F k) i₀ a c d (ρ k) z‖ ≤ T k / 4 := fun k z hz h1 h2 h3 =>
    (norm_splitM_le (N1 k) hcd (inv k).2 (N9 k) (N8 k) hz h1 h2 h3).trans (N10 k)
  obtain ⟨A, hA⟩ : ∃ A : ℕ → (ι → ℂ) → Matrix m m ℂ, A = fun k z =>
      ((List.range k).map fun j => 1 + splitP (F j) i₀ a c d (ρ j) z).prod := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → (ι → ℂ) → Matrix m m ℂ, B = fun k z =>
      ((List.range k).map fun j => 1 + splitM (F j) i₀ a c d (ρ j) z).prod := ⟨_, rfl⟩
  have rel : ∀ k, ∀ z ∈ slab i₀ Ob (rectO a c d (σ k)), h z * B k z = A k z * (1 + F k z) := by
    intro k
    induction k with
    | zero => intro z _; rw [hA, hB, hF0]; simp
    | succ k ih =>
      intro z hz
      have hzk := slab_mono (rectO_subset_rectO (hσk k)) hz
      have hzρ := slab_mono (rectO_subset_rectO (hσρ k)) hz
      have hsplit := splitP_sub_splitM (N1 k) hcd (isOpen_rectO a c d (σ k))
        (rectC_subset_rectO (N2 k)) (inv k).1 hzρ
      have hpb : ‖splitP (F k) i₀ a c d (ρ k) z‖ ≤ 1 / 2 := by
        obtain ⟨hz1, hzO⟩ := hz
        rw [mem_rectO, N3] at hz1
        exact (hPb k z hzO (by linarith [hz1.1.2]) (by linarith [hz1.2.1])
          (by linarith [hz1.2.2])).trans (hT8 k)
      have hu := (isUnit_one_add_and_norm_inverse_le norm_one_matrix_le hpb).1
      have hAs : A (k + 1) z = A k z * (1 + splitP (F k) i₀ a c d (ρ k) z) := by
        rw [hA]; simp only [List.prod_range_succ]
      have hBs : B (k + 1) z = B k z * (1 + splitM (F k) i₀ a c d (ρ k) z) := by
        rw [hB]; simp only [List.prod_range_succ]
      rw [hAs, hBs, ← mul_assoc, ih z hzk, hFs]
      dsimp only
      rw [← hsplit]
      set p := splitP (F k) i₀ a c d (ρ k) z
      set q := splitM (F k) i₀ a c d (ρ k) z
      have h1 : (1 + p) * Ring.inverse (1 + p) = 1 := Ring.mul_inverse_cancel _ hu
      calc A k z * (1 + (p - q)) * (1 + q) = A k z * ((1 + p) + (p - q) * q) := by noncomm_ring
        _ = A k z * ((1 + p) + (1 + p) * Ring.inverse (1 + p) * ((p - q) * q)) := by
            rw [h1, one_mul]
        _ = A k z * (1 + p) * (1 + Ring.inverse (1 + p) * (p - q) * q) := by noncomm_ring
  have hN'o : IsOpen N' := (isOpen_lt continuous_re continuous_const).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))
  have hN''o : IsOpen N'' := (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))
  have hN'b : ∀ k, ∀ z ∈ slab i₀ Ob N',
      ‖splitP (F k) i₀ a c d (ρ k) z‖ ≤ (1 / 2 : ℝ) ^ (k + 3) := by
    intro k z hz
    obtain ⟨⟨h1, h2, h3⟩, hzO⟩ := hz
    exact (hPb k z hzO (by linarith [N5 k]) (by linarith [N5 k]) (by linarith [N5 k])).trans
      (N11 k)
  have hN''b : ∀ k, ∀ z ∈ slab i₀ Ob N'',
      ‖splitM (F k) i₀ a c d (ρ k) z‖ ≤ (1 / 2 : ℝ) ^ (k + 3) := by
    intro k z hz
    obtain ⟨⟨h1, h2, h3⟩, hzO⟩ := hz
    exact (hQb k z hzO (by linarith [N5 k]) (by linarith [N5 k]) (by linarith [N5 k])).trans
      (N11 k)
  obtain ⟨g', hg'lim, hg'1⟩ := exists_tendstoUniformlyOn_prod norm_one_matrix_le
    (s := slab i₀ Ob N') (fun k z => splitP (F k) i₀ a c d (ρ k) z) hN'b
  obtain ⟨g'', hg''lim, hg''1⟩ := exists_tendstoUniformlyOn_prod norm_one_matrix_le
    (s := slab i₀ Ob N'') (fun k z => splitM (F k) i₀ a c d (ρ k) z) hN''b
  have hAd : ∀ k, DifferentiableOn ℂ
      (fun z => ((List.range k).map fun j => 1 + splitP (F j) i₀ a c d (ρ j) z).prod)
      (slab i₀ Ob N') := fun k =>
    differentiableOn_prod_range (fun j z => splitP (F j) i₀ a c d (ρ j) z) (fun j =>
      (differentiableOn_splitP (N1 j) hcd (isOpen_rectO _ _ _ _) hOb (rectC_subset_rectO (N2 j))
        (inv j).1).mono (slab_mono fun ζ hζ => by
          obtain ⟨h1, h2, h3⟩ := hζ
          exact ⟨by linarith [N5 j, N8 j], by linarith [N5 j, N8 j], by linarith [N5 j, N8 j]⟩)) k
  have hBd : ∀ k, DifferentiableOn ℂ
      (fun z => ((List.range k).map fun j => 1 + splitM (F j) i₀ a c d (ρ j) z).prod)
      (slab i₀ Ob N'') := fun k =>
    differentiableOn_prod_range (fun j z => splitM (F j) i₀ a c d (ρ j) z) (fun j =>
      (differentiableOn_splitM (N1 j) hcd (isOpen_rectO _ _ _ _) hOb (rectC_subset_rectO (N2 j))
        (inv j).1).mono (slab_mono fun ζ hζ => by
          obtain ⟨h1, h2, h3⟩ := hζ
          exact ⟨by linarith [N5 j, N8 j], by linarith [N5 j, N8 j], by linarith [N5 j, N8 j]⟩)) k
  refine ⟨g', g'', differentiableOn_of_tendstoUniformlyOn (isOpen_slab hOb hN'o) hAd hg'lim,
    fun z hz => isUnit_of_norm_sub_one_le (hg'1 z hz),
    differentiableOn_of_tendstoUniformlyOn (isOpen_slab hOb hN''o) hBd hg''lim,
    fun z hz => isUnit_of_norm_sub_one_le (hg''1 z hz), fun z hz => ?_⟩
  obtain ⟨hz1, hzO⟩ := hz
  rw [mem_rectO] at hz1
  have hzN' : z ∈ slab i₀ Ob N' := ⟨⟨by linarith [hz1.1.2], by linarith [hz1.2.1],
    by linarith [hz1.2.2]⟩, hzO⟩
  have hzN'' : z ∈ slab i₀ Ob N'' := ⟨⟨by linarith [hz1.1.1], by linarith [hz1.2.1],
    by linarith [hz1.2.2]⟩, hzO⟩
  have hμσ : ∀ k, μ / 2 ≤ σ k := fun k => by
    have := N2 k; have := N5 k; have := N8 k; linarith
  have hμρ : ∀ k, μ / 2 ≤ ρ k := fun k => by have := N5 k; have := N8 k; linarith
  have hzσ : ∀ k, z ∈ slab i₀ Ob (rectO a c d (σ k)) := fun k =>
    slab_mono (rectO_subset_rectO (hμσ k)) ⟨(mem_rectO).2 hz1, hzO⟩
  have hzρ : ∀ k, z ∈ slab i₀ Ob (rectC a c d (ρ k)) := fun k =>
    slab_mono (rectO_subset_rectC (hμρ k)) ⟨(mem_rectO).2 hz1, hzO⟩
  have hFlim : Tendsto (fun k => F k z) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => μ / (16 * ℓ) * (1 / 2 : ℝ) ^ k) (fun k => ?_) ?_
    · refine ((inv k).2 z (hzρ k)).trans ?_
      rw [he]; dsimp only
      have := hT1 k; have := hr0 k
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := mul_le_mul_of_nonneg_left (hT1 k) (le_of_lt (mul_pos hμ (hr0 k)))
      nlinarith
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (μ / (16 * ℓ))
  have t1 : Tendsto (fun k => A k z * (1 + F k z)) atTop (𝓝 (h z * g'' z)) := by
    have : Tendsto (fun k => B k z) atTop (𝓝 (g'' z)) := by
      rw [hB]; exact hg''lim.tendsto_at hzN''
    exact (this.const_mul (h z)).congr fun k => rel k z (hzσ k)
  have t2 : Tendsto (fun k => A k z * (1 + F k z)) atTop (𝓝 (g' z * (1 + 0))) := by
    have : Tendsto (fun k => A k z) atTop (𝓝 (g' z)) := by
      rw [hA]; exact hg'lim.tendsto_at hzN'
    exact this.mul (tendsto_const_nhds.add hFlim)
  simpa using tendsto_nhds_unique t1 t2

end NearOne

end CartanIteration

section NearOneSplitting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Near-identity step: there are an open `V ⊇ L` and a block `L⁺` with `V ⊆ L⁺ ⊆ U`, and an
`ε > 0`, such that every holomorphic `h` on `V` with entries `ε`-close to those of `1` on `V`
splits. -/
private theorem splits_of_near_one
    (x₀ x₁ y₀ y₁ : ι → ℝ) (hx : ∀ i, x₀ i ≤ x₁ i) (hy : ∀ i, y₀ i ≤ y₁ i)
    (K : Set (ι → ℂ)) (hK : K = univ.pi fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i))
    (i₀ : ι) (a : ℝ) (ha₀ : x₀ i₀ < a) (ha₁ : a < x₁ i₀)
    (U : Set (ι → ℂ)) (hU : IsOpen U)
    (hLU : K ∩ {z | (z i₀).re ≤ a} ∩ (K ∩ {z | a ≤ (z i₀).re}) ⊆ U) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧
      K ∩ {z | (z i₀).re ≤ a} ∩ (K ∩ {z | a ≤ (z i₀).re}) ⊆ V ∧
      ∃ u₀ u₁ v₀ v₁ : ι → ℝ,
      V ⊆ (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) ∧
      (univ.pi fun i => Icc (u₀ i) (u₁ i) ×ℂ Icc (v₀ i) (v₁ i)) ⊆ U ∧ ∃ ε > (0 : ℝ),
      ∀ h : (ι → ℂ) → Matrix m m ℂ, (∀ i j, DifferentiableOn ℂ (fun z => h z i j) V) →
        (∀ z ∈ V, ∀ i j, ‖h z i j - (1 : Matrix m m ℂ) i j‖ ≤ ε) → Splits K i₀ a h := by
  classical
  subst hK
  set c := y₀ i₀
  set d := y₁ i₀
  have hcd : c ≤ d := hy i₀
  set L := (univ.pi fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i)) ∩ {z | (z i₀).re ≤ a} ∩
    ((univ.pi fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i)) ∩ {z | a ≤ (z i₀).re}) with hL
  have hKc : IsCompact (univ.pi fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i)) :=
    isCompact_univ_pi fun i => isCompact_Icc.reProdIm isCompact_Icc
  have hLc : IsCompact L :=
    (hKc.inter_right (isClosed_le (continuous_re.comp (continuous_apply i₀))
      continuous_const)).inter_right
      (hKc.isClosed.inter (isClosed_le continuous_const (continuous_re.comp (continuous_apply i₀))))
  obtain ⟨δ', hδ', hthick⟩ := hLc.exists_thickening_subset_open hU hLU
  set μ := δ' / 8 with hμdef
  have hμ : 0 < μ := by positivity
  set Ob : ι → Set ℂ := fun i =>
    Ioo (x₀ i - 3 * μ) (x₁ i + 3 * μ) ×ℂ Ioo (y₀ i - 3 * μ) (y₁ i + 3 * μ)
  have hOb : ∀ i, IsOpen (Ob i) := fun i => isOpen_Ioo.reProdIm isOpen_Ioo
  set ℓ := 8 * μ + (d - c) with hℓ
  have hℓ0 : 0 < ℓ := by rw [hℓ]; linarith
  have hmemL : ∀ z, z ∈ L ↔
      (∀ i, z i ∈ Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i)) ∧ (z i₀).re = a := by
    intro z
    simp only [hL, mem_inter_iff, mem_univ_pi, mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3⟩; exact ⟨h1, le_antisymm h2 h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h1, h2.ge⟩
  have hLV : L ⊆ slab i₀ Ob (rectO a c d (3 * μ)) := by
    intro z hz
    rw [hmemL] at hz
    obtain ⟨h1, h2⟩ := hz
    refine ⟨?_, fun i _ => ?_⟩
    · have := Complex.mem_reProdIm.1 (h1 i₀)
      rw [mem_rectO]
      exact ⟨⟨by linarith, by linarith⟩, by linarith [this.2.1], by linarith [this.2.2]⟩
    · have := Complex.mem_reProdIm.1 (h1 i)
      exact Complex.mem_reProdIm.2 ⟨⟨by linarith [this.1.1], by linarith [this.1.2]⟩,
        by linarith [this.2.1], by linarith [this.2.2]⟩
  refine ⟨slab i₀ Ob (rectO a c d (3 * μ)), isOpen_slab hOb (isOpen_rectO _ _ _ _), hLV,
    fun i => if i = i₀ then a - 3 * μ else x₀ i - 3 * μ,
    fun i => if i = i₀ then a + 3 * μ else x₁ i + 3 * μ,
    fun i => y₀ i - 3 * μ, fun i => y₁ i + 3 * μ, ?_, ?_,
    μ / (32 * ℓ) / (Fintype.card m + 1), by positivity, ?_⟩
  · intro z hz
    obtain ⟨hz1, hzO⟩ := hz
    intro i _
    by_cases hi : i = i₀
    · subst hi
      rw [mem_rectO] at hz1
      simp only [if_pos rfl]
      exact Complex.mem_reProdIm.2 ⟨⟨hz1.1.1.le, hz1.1.2.le⟩, hz1.2.1.le, hz1.2.2.le⟩
    · simp only [if_neg hi]
      have := Complex.mem_reProdIm.1 (hzO i hi)
      exact Complex.mem_reProdIm.2 ⟨⟨this.1.1.le, this.1.2.le⟩, this.2.1.le, this.2.2.le⟩
  · intro z hz
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨fun i => ⟨if i = i₀ then a else max (x₀ i) (min (z i).re (x₁ i)),
      max (y₀ i) (min (z i).im (y₁ i))⟩, ?_, ?_⟩
    · rw [hmemL]
      refine ⟨fun i => ?_, by simp⟩
      refine Complex.mem_reProdIm.2 ⟨?_, le_max_left _ _, max_le (hy i) (min_le_right _ _)⟩
      by_cases hi : i = i₀
      · subst hi; simp only [if_pos rfl]; exact ⟨ha₀.le, ha₁.le⟩
      · simp only [if_neg hi]; exact ⟨le_max_left _ _, max_le (hx i) (min_le_right _ _)⟩
    · refine (dist_pi_lt_iff hδ').2 fun i => ?_
      have hzi := Complex.mem_reProdIm.1 (hz i (mem_univ i))
      rw [dist_eq_norm]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
      simp only [Complex.sub_re, Complex.sub_im]
      have h2 := abs_sub_clamp_le (hy i) (by linarith : (0 : ℝ) ≤ 3 * μ) hzi.2.1 hzi.2.2
      by_cases hi : i = i₀
      · simp only [if_pos hi] at hzi ⊢
        have h1 : |(z i).re - a| ≤ 3 * μ := abs_le.2 ⟨by linarith [hzi.1.1], by linarith [hzi.1.2]⟩
        linarith
      · simp only [if_neg hi] at hzi ⊢
        have h1 := abs_sub_clamp_le (hx i) (by linarith : (0 : ℝ) ≤ 3 * μ) hzi.1.1 hzi.1.2
        linarith
  · intro h hh hclose
    have hb : ∀ z ∈ slab i₀ Ob (rectO a c d (3 * μ)), ‖h z - 1‖ ≤ μ / (32 * (8 * μ + (d - c))) := by
      intro z hz
      have hε0 : (0 : ℝ) ≤ μ / (32 * ℓ) / (Fintype.card m + 1) := by positivity
      refine (norm_matrix_le_of_entries _ hε0 fun i j => by
        rw [Matrix.sub_apply]; exact hclose z hz i j).trans ?_
      rw [← hℓ, mul_div_assoc']
      apply div_le_of_le_mul₀ (by positivity) (by positivity)
      have : (0 : ℝ) ≤ μ / (32 * ℓ) := by positivity
      nlinarith
    obtain ⟨g', g'', hg'd, hg'u, hg''d, hg''u, hrel⟩ :=
      near_one_split i₀ Ob hOb a c d μ hμ hcd h (differentiableOn_matrix_of_apply hh) hb
    have hN'o : IsOpen {ζ : ℂ | ζ.re < a + μ / 2 ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2} :=
      (isOpen_lt continuous_re continuous_const).inter
        ((isOpen_lt continuous_const continuous_im).inter
          (isOpen_lt continuous_im continuous_const))
    have hN''o : IsOpen {ζ : ℂ | a - μ / 2 < ζ.re ∧ c - μ / 2 < ζ.im ∧ ζ.im < d + μ / 2} :=
      (isOpen_lt continuous_const continuous_re).inter
        ((isOpen_lt continuous_const continuous_im).inter
          (isOpen_lt continuous_im continuous_const))
    have hOK : ∀ z ∈ univ.pi (fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i)),
        ∀ i, i ≠ i₀ → z i ∈ Ob i := fun z hz i _ => by
      have := Complex.mem_reProdIm.1 (hz i (mem_univ i))
      exact Complex.mem_reProdIm.2 ⟨⟨by linarith [this.1.1], by linarith [this.1.2]⟩,
        by linarith [this.2.1], by linarith [this.2.2]⟩
    have hentry : ∀ {S : Set (ι → ℂ)} {g : (ι → ℂ) → Matrix m m ℂ}, DifferentiableOn ℂ g S →
        ∀ i j, DifferentiableOn ℂ (fun z => g z i j) S := fun hg i j =>
      (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable
        |>.comp_differentiableOn hg
    refine ⟨_, _, g', g'', isOpen_slab hOb hN'o, fun z hz => ⟨?_, hOK z hz.1⟩, hentry hg'd, hg'u,
      isOpen_slab hOb hN''o, fun z hz => ⟨?_, hOK z hz.1⟩, hentry hg''d, hg''u, ?_⟩
    · have := Complex.mem_reProdIm.1 (hz.1 i₀ (mem_univ _))
      exact ⟨by linarith [hz.2.out], by linarith [this.2.1], by linarith [this.2.2]⟩
    · have := Complex.mem_reProdIm.1 (hz.1 i₀ (mem_univ _))
      exact ⟨by linarith [hz.2.out], by linarith [this.2.1], by linarith [this.2.2]⟩
    · have hW : IsOpen (slab i₀ Ob (rectO a c d (μ / 2))) := isOpen_slab hOb (isOpen_rectO _ _ _ _)
      have hLW : L ⊆ slab i₀ Ob (rectO a c d (μ / 2)) := by
        intro z hz
        have hz' := hz
        rw [hmemL] at hz'
        obtain ⟨h1, h2⟩ := hz'
        refine ⟨?_, hOK z (fun i _ => h1 i)⟩
        have := Complex.mem_reProdIm.1 (h1 i₀)
        rw [mem_rectO]
        exact ⟨⟨by linarith, by linarith⟩, by linarith [this.2.1], by linarith [this.2.2]⟩
      filter_upwards [hW.mem_nhdsSet.2 hLW] with z hz
      obtain ⟨hz1, hzO⟩ := hz
      have hz1' := hz1
      rw [mem_rectO] at hz1'
      have hu := hg''u z ⟨⟨by linarith [hz1'.1.1], by linarith [hz1'.2.1], by linarith [hz1'.2.2]⟩,
        hzO⟩
      rw [← hrel z ⟨hz1, hzO⟩, mul_assoc, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 hu), mul_one]

end NearOneSplitting

end Helpers

/-- **Cartan's lemma** on adjacent blocks. Let `K = ∏ᵢ ([x₀ i, x₁ i] ×ℂ [y₀ i, y₁ i])` be a
block in `ℂ^ι` and `x₀ i₀ < a < x₁ i₀`. Every matrix function `g` that is holomorphic and
invertible on an open neighbourhood of `L = K ∩ {Re zᵢ₀ = a}` factors near `L` as
`g = g' * (g'')⁻¹`, with `g'`, `g''` holomorphic and invertible on open neighbourhoods of
`K ∩ {Re zᵢ₀ ≤ a}` and `K ∩ {a ≤ Re zᵢ₀}` respectively. -/
@[mmp "lem_mmp_gaga_cartan_matrix_splitting"]
public theorem exists_eq_mul_inv_of_isUnit_of_differentiableOn_block
    {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]
    (x₀ x₁ y₀ y₁ : ι → ℝ) (hx : ∀ i, x₀ i ≤ x₁ i) (hy : ∀ i, y₀ i ≤ y₁ i)
    (K : Set (ι → ℂ)) (hK : K = univ.pi fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i))
    (i₀ : ι) (a : ℝ) (ha₀ : x₀ i₀ < a) (ha₁ : a < x₁ i₀)
    (g : (ι → ℂ) → Matrix m m ℂ) (U : Set (ι → ℂ)) (hU : IsOpen U)
    (hLU : K ∩ {z | (z i₀).re ≤ a} ∩ (K ∩ {z | a ≤ (z i₀).re}) ⊆ U)
    (hg : ∀ i j, DifferentiableOn ℂ (fun z => g z i j) U)
    (hgu : ∀ z ∈ U, IsUnit (g z)) :
    ∃ (U' U'' : Set (ι → ℂ)) (g' g'' : (ι → ℂ) → Matrix m m ℂ),
      IsOpen U' ∧ K ∩ {z | (z i₀).re ≤ a} ⊆ U' ∧
      (∀ i j, DifferentiableOn ℂ (fun z => g' z i j) U') ∧ (∀ z ∈ U', IsUnit (g' z)) ∧
      IsOpen U'' ∧ K ∩ {z | a ≤ (z i₀).re} ⊆ U'' ∧
      (∀ i j, DifferentiableOn ℂ (fun z => g'' z i j) U'') ∧ (∀ z ∈ U'', IsUnit (g'' z)) ∧
      ∀ᶠ z in 𝓝ˢ (K ∩ {z | (z i₀).re ≤ a} ∩ (K ∩ {z | a ≤ (z i₀).re})),
        g z = g' z * (g'' z)⁻¹ := by
  obtain ⟨V, hV, hLV, u₀, u₁, v₀, v₁, hVL, hLpU, ε, hε, hsplit⟩ :=
    splits_of_near_one (m := m) x₀ x₁ y₀ y₁ hx hy K hK i₀ a ha₀ ha₁ U hU hLU
  obtain ⟨P, Q, hP, hQ, hPQ, hQP, hclose⟩ :=
    exists_entire_approx g U hU hg hgu u₀ u₁ v₀ v₁ hLpU ε hε
  have hVU' : V ⊆ U := hVL.trans hLpU
  obtain ⟨U', U'', h', h'', hU', hKU', hh', hh'u, hU'', hKU'', hh'', hh''u, hev⟩ :=
    hsplit (fun z => Q z * g z)
      (differentiableOn_mul_apply (fun i j => (hQ i j).differentiableOn)
        (fun i j => (hg i j).mono hVU')) (fun z hz => hclose z (hVL hz))
  have hPu : ∀ z, IsUnit (P z) := fun z => ⟨⟨P z, Q z, hPQ z, hQP z⟩, rfl⟩
  refine ⟨U', U'', fun z => P z * h' z, h'', hU', hKU',
    differentiableOn_mul_apply (fun i j => (hP i j).differentiableOn) hh',
    fun z hz => (hPu z).mul (hh'u z hz), hU'', hKU'', hh'', hh''u, ?_⟩
  filter_upwards [hev] with z hz
  rw [mul_assoc, ← hz, ← mul_assoc, hPQ, one_mul]

end MMP.Gaga
