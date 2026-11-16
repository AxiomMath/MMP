module

public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Basic
public import MMP.AlgebraicTopology.FundamentalClass.RealLine

/-!
# The first Chern class of a complex line bundle is its Euler class

Let `E → B` be a complex topological line bundle on a space `B`, with Thom class
`u_E ∈ H²(E, E - 0_E; ℤ)` (`MMP.ThomClass.thomClass`) and first Chern class
`c₁(E) ∈ H²(B; ℤ)`, the class of the obstruction cocycle `n ∘ ρ`
(`MMP.Analytic.firstChernClass`). The Euler class of `E` is the restriction `0_E^* u_E` of the
Thom class along the zero section. We show `0_E^* u_E = c₁(E)` (Milnor–Stasheff, Thm. 12.5 and
§14), with no sign: both are taken for the orientation of the fibres given by their complex
structure.

The proof is on cochains. Off the zero section a vector `p` over `b` has a ratio
`λ(p) = p / r(b) ∈ ℂ^×` to the reference vector `r(b)` of the obstruction cocycle. Over a
trivializing open, the increment of a continuous logarithm of the coordinate of a `1`-simplex `τ`
minus the edge phase of `π ∘ τ` (`angleIncrement τ`) does not depend on the trivialization, and
differs from `log λ(τ(1)) - log λ(τ(0))` by `2πi` times an integer `w(τ)` (`windingEdge`). The
Thom cochain `π^* n + δ w` vanishes on small simplices off the zero section, because there the
coboundary of the angle increments is minus the obstruction phase; transported by the
small-chains map `ρ` it is a relative cocycle of `(E, E - 0_E)` (`thomCocycle`). On a
positively oriented triangle around `0` in a fibre its value is the winding number `1` of the
triangle around `0`, so its class is the Thom class (`thomClass_eq`). Along the zero section the
winding cochain vanishes and the Thom cochain is the obstruction cochain; two cocycles agreeing on
small simplices are cohomologous, whence the Euler class is `c₁(E)`.

## Main definitions

* `MMP.Analytic.ComplexLineBundle.coord`, `fibreRatio`: the coordinate of a vector in a
  trivialization, and its ratio `λ(p) = p / r(π p)` to the reference vector.
* `MMP.Analytic.ComplexLineBundle.angleIncrement`: the increment of the angle of a `1`-simplex of
  the total space relative to the reference path.
* `MMP.Analytic.ComplexLineBundle.windingEdge`: the winding cochain `w`.
* `MMP.Analytic.ComplexLineBundle.thomCochain`, `thomCocycle`: the Thom cochain `π^* n + δ w`
  and the relative cocycle it gives.

## Main results

* `MMP.Analytic.log_div_sub_log_div_add_log_div`: the winding number of a counterclockwise
  triangle around `0` is `1`.
* `MMP.Analytic.ComplexLineBundle.angleIncrement_eq`: the angle increment does not depend on the
  trivialization.
* `MMP.Analytic.ComplexLineBundle.thomCocycle_eq_zero`: the Thom cocycle vanishes off the zero
  section.
* `MMP.Analytic.ComplexLineBundle.thomCocycle_fibreSimplex`: its value on a positively oriented
  simplex around `0` in a fibre is `1`.
* `MMP.Analytic.ComplexLineBundle.thomClass_eq`: the Thom class is the class of the Thom cocycle.
* `MMP.Analytic.ComplexLineBundle.congrIndex_eulerClass_eq_firstChernClass`: `0_E^* u_E = c₁(E)`.

## Implementation notes

* The line bundle is a Mathlib vector bundle with fibre `ℂ`, as for
  `MMP.Analytic.firstChernClass`. The Thom class lives in degree `2 · dim_ℂ ℂ`; the Euler class is
  moved to degree `2` by `MMP.cohomologyWithSupports.congrIndex`.
* The Euler class `0_E^* u_E` is written out as the pull-back of the Thom class along the zero
  section, the same class as `MMP.Topology.eulerClass ℤ ℂ E` of the Gysin construction.

## References

* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–12, 14.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
-/

@[expose] public noncomputable section

open Complex

namespace MMP.Analytic

section Triangle

/-- `D(x, y) = Im (x̄ y)`, the oriented area form of `ℂ = ℝ²`. -/
private lemma div_im_eq (x y : ℂ) :
    (y / x).im = (x.re * y.im - x.im * y.re) / normSq x := by
  rw [div_im]
  ring

/-- **The winding number of a triangle around an interior point.** If `a₀, a₁, a₂ ∈ ℂ` turn
counterclockwise (`Im (a₁ / a₀) > 0`, `Im (a₂ / a₁) > 0`, `Im (a₂ / a₀) < 0`), the principal
logarithms of the ratios along the edges add up to `2πi`. -/
lemma log_div_sub_log_div_add_log_div {a₀ a₁ a₂ : ℂ} (h₀₁ : 0 < (a₁ / a₀).im)
    (h₁₂ : 0 < (a₂ / a₁).im) (h₀₂ : (a₂ / a₀).im < 0) :
    log (a₂ / a₁) - log (a₂ / a₀) + log (a₁ / a₀) = 2 * Real.pi * I := by
  have ne : ∀ {x y : ℂ}, 0 < (y / x).im ∨ (y / x).im < 0 → x ≠ 0 ∧ y ≠ 0 := by
    intro x y h
    constructor <;> rintro rfl <;> simp at h
  obtain ⟨h0, h1⟩ := ne (Or.inl h₀₁)
  obtain ⟨-, h2⟩ := ne (Or.inl h₁₂)
  set S := log (a₂ / a₁) - log (a₂ / a₀) + log (a₁ / a₀) with hS
  have hexp : exp S = 1 := by
    rw [hS, exp_add, exp_sub, exp_log (div_ne_zero h2 h1), exp_log (div_ne_zero h2 h0),
      exp_log (div_ne_zero h1 h0)]
    field_simp
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 hexp
  have him : S.im = (a₂ / a₁).arg - (a₂ / a₀).arg + (a₁ / a₀).arg := by
    simp [hS, log_im]
  have p1 : 0 < (a₂ / a₁).arg := lt_of_le_of_ne (arg_nonneg_iff.2 h₁₂.le)
    (fun h ↦ h₁₂.ne' (arg_eq_zero_iff.1 h.symm).2)
  have p2 : 0 < (a₁ / a₀).arg := lt_of_le_of_ne (arg_nonneg_iff.2 h₀₁.le)
    (fun h ↦ h₀₁.ne' (arg_eq_zero_iff.1 h.symm).2)
  have p3 := arg_neg_iff.2 h₀₂
  have q1 := arg_le_pi (a₂ / a₁)
  have q2 := arg_le_pi (a₁ / a₀)
  have q3 := neg_pi_lt_arg (a₂ / a₀)
  have hnim : S.im = n * (2 * Real.pi) := by
    rw [hn]
    simp
  have hpi := Real.pi_pos
  have hn1 : n = 1 := by
    have lo : (0 : ℝ) < n * (2 * Real.pi) := by linarith
    have hi : (n : ℝ) * (2 * Real.pi) < 3 * Real.pi := by linarith
    have h0 : (0 : ℝ) < n := by nlinarith
    have h2 : (n : ℝ) < 2 := by nlinarith
    have h0' : 0 < n := by exact_mod_cast h0
    have h2' : n < 2 := by exact_mod_cast h2
    omega
  rw [hn, hn1]
  simp

open MMP.ThomClass in
/-- The coordinates of `u ∈ ℂ¹` in the real basis `e₁, i e₁` are `Re u₀, Im u₀`. -/
private lemma complexOrientationBasis_one_repr (u : Fin 1 → ℂ) :
    (complexOrientationBasis 1).repr u 0 = (u 0).re ∧
      (complexOrientationBasis 1).repr u 1 = (u 0).im := by
  have h0 : complexOrientationBasis 1 0 = fun _ ↦ 1 := by
    have := complexOrientationBasis_apply 1 0 0
    rw [show finCongr (Nat.mul_comm 1 2) (finProdFinEquiv ((0 : Fin 1), (0 : Fin 2))) = 0 from
      Fin.ext rfl] at this
    rw [this]
    funext j
    simp [Subsingleton.elim j 0]
  have h1 : complexOrientationBasis 1 1 = fun _ ↦ I := by
    have := complexOrientationBasis_apply 1 0 1
    rw [show finCongr (Nat.mul_comm 1 2) (finProdFinEquiv ((0 : Fin 1), (1 : Fin 2))) = 1 from
      Fin.ext rfl] at this
    rw [this]
    funext j
    simp [Subsingleton.elim j 0]
  have hu : u = (u 0).re • complexOrientationBasis 1 0 +
      (u 0).im • complexOrientationBasis 1 1 := by
    rw [h0, h1]
    funext j
    fin_cases j
    simp
  constructor <;> (conv_lhs => rw [hu]) <;> simp

open MMP.ThomClass in
/-- The vertices `a₀, a₁, a₂ ∈ ℂ` of a simplex around `0` oriented by `1, i` turn
counterclockwise. -/
lemma im_div_of_isOrientedSimplexAroundZero {v : Fin (2 * 1 + 1) → (Fin 1 → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis 1) v) :
    0 < (v 1 0 / v 0 0).im ∧ 0 < (v 2 0 / v 1 0).im ∧ (v 2 0 / v 0 0).im < 0 := by
  obtain ⟨⟨t, ht, hsum, hzero⟩, hdet⟩ := hv
  have hz := congrFun hzero 0
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.re_sum, Complex.im_sum, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    Complex.zero_re, Complex.zero_im] at hre him
  change ∑ k : Fin 3, _ = _ at hre him hsum
  simp only [Fin.sum_univ_three] at hre him hsum
  rw [Module.Basis.det_apply] at hdet
  change 0 < Matrix.det (n := Fin 2) _ at hdet
  rw [Matrix.det_fin_two] at hdet
  simp only [Module.Basis.toMatrix_apply] at hdet
  obtain ⟨r10, r11⟩ := complexOrientationBasis_one_repr (v 1 - v 0)
  obtain ⟨r20, r21⟩ := complexOrientationBasis_one_repr (v 2 - v 0)
  change 0 < (complexOrientationBasis 1).repr (v 1 - v 0) 0 *
      (complexOrientationBasis 1).repr (v 2 - v 0) 1 -
    (complexOrientationBasis 1).repr (v 2 - v 0) 0 *
      (complexOrientationBasis 1).repr (v 1 - v 0) 1 at hdet
  rw [r10, r11, r20, r21] at hdet
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im] at hdet
  set X₀ := (v 0 0).re
  set X₁ := (v 1 0).re
  set X₂ := (v 2 0).re
  set Y₀ := (v 0 0).im
  set Y₁ := (v 1 0).im
  set Y₂ := (v 2 0).im
  set d := (X₁ - X₀) * (Y₂ - Y₀) - (X₂ - X₀) * (Y₁ - Y₀)
  have e01 : X₀ * Y₁ - Y₀ * X₁ = t 2 * d := by
    linear_combination (Y₁ - Y₀) * hre - (X₁ - X₀) * him - (X₀ * Y₁ - Y₀ * X₁) * hsum
  have e12 : X₁ * Y₂ - Y₁ * X₂ = t 0 * d := by
    linear_combination (Y₂ - Y₁) * hre - (X₂ - X₁) * him - (X₁ * Y₂ - Y₁ * X₂) * hsum
  have e20 : X₂ * Y₀ - Y₂ * X₀ = t 1 * d := by
    linear_combination (Y₀ - Y₂) * hre - (X₀ - X₂) * him - (X₂ * Y₀ - Y₂ * X₀) * hsum
  have p01 : 0 < X₀ * Y₁ - Y₀ * X₁ := e01 ▸ mul_pos (ht 2) hdet
  have p12 : 0 < X₁ * Y₂ - Y₁ * X₂ := e12 ▸ mul_pos (ht 0) hdet
  have p20 : 0 < X₂ * Y₀ - Y₂ * X₀ := e20 ▸ mul_pos (ht 1) hdet
  have nz : ∀ k : Fin (2 * 1 + 1), (∀ h : (v k 0).re = 0 ∧ (v k 0).im = 0, False) →
      0 < normSq (v k 0) := fun k hk ↦ normSq_pos.2 fun h ↦ hk (by simp [h])
  have n0 := nz 0 fun h ↦ by
    have : X₀ = 0 := h.1
    have : Y₀ = 0 := h.2
    simp_all
  have n1 := nz 1 fun h ↦ by
    have : X₁ = 0 := h.1
    have : Y₁ = 0 := h.2
    simp_all
  refine ⟨?_, ?_, ?_⟩
  · rw [div_im_eq]
    exact div_pos p01 n0
  · rw [div_im_eq]
    exact div_pos p12 n1
  · rw [div_im_eq]
    exact div_neg_of_neg_of_pos (by linarith) n0

end Triangle

namespace ComplexLineBundle

open Bundle FiberBundle MMP MMP.SingularChain MMP.SingularCochain

variable {B : Type} [TopologicalSpace B] {E : B → Type} [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [TopologicalSpace (TotalSpace ℂ E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]

section coord

/-- The coordinate `e(p) ∈ ℂ` of a vector `p` of a complex line bundle in a trivialization `e`. -/
def coord (e : Trivialization ℂ (π ℂ E)) (p : TotalSpace ℂ E) : ℂ := (e p).2

/-- The ratio `p / r(π p) ∈ ℂ` of a vector `p` over `b` to the reference vector `r(b)`, the vector
of coordinate `1` in `trivializationAt b`: the coordinate of `p` in `trivializationAt b`. -/
def fibreRatio (p : TotalSpace ℂ E) : ℂ := coord (trivializationAt ℂ E p.proj) p

variable (E) in
/-- The projection of the total space, as a continuous map. -/
def projMap : C(TotalSpace ℂ E, B) := ⟨TotalSpace.proj, FiberBundle.continuous_proj ℂ E⟩

variable (E) in
/-- The zero section, as a continuous map. -/
def zeroMap : C(B, TotalSpace ℂ E) := ⟨zeroSection ℂ E, Trivialization.continuous_zeroSection ℂ⟩

/-- Over the base of `e`, the coordinate of `p` in `e` is the `e`-coordinate of the reference
vector over `π p` times the ratio `p / r(π p)`. -/
lemma coord_eq_mul {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {p : TotalSpace ℂ E} (hp : p.proj ∈ e.baseSet) :
    coord e p = vertexCoord e p.proj * fibreRatio p := by
  set e₀ := trivializationAt ℂ E p.proj
  have hb₀ : p.proj ∈ e₀.baseSet := mem_baseSet_trivializationAt ℂ E p.proj
  have h := Trivialization.coordChangeL_apply (R := ℂ) e₀ e ⟨hb₀, hp⟩ (e₀ p).2
  rw [Trivialization.symm_apply_apply_mk e₀ hb₀ p.2] at h
  rw [coordChangeL_eq_mul_transition ⟨hb₀, hp⟩] at h
  rw [coord, ← h, fibreRatio, coord, vertexCoord, mul_comm]

/-- Changing the trivialization from `e` to `e'` multiplies the coordinate by the transition
function. -/
lemma coord_eq_transition_mul {e e' : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] {p : TotalSpace ℂ E} (hp : p.proj ∈ e.baseSet)
    (hp' : p.proj ∈ e'.baseSet) :
    coord e' p = transition e e' p.proj * coord e p := by
  rw [coord_eq_mul hp, coord_eq_mul hp', vertexCoord_eq hp hp', mul_assoc]

/-- Over the base of `e`, the coordinate of `p` in `e` vanishes if and only if `p` lies on the zero
section. -/
lemma coord_eq_zero_iff {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {p : TotalSpace ℂ E} (hp : p.proj ∈ e.baseSet) :
    coord e p = 0 ↔ p ∈ Set.range (zeroSection ℂ E) := by
  rw [ThomClass.mem_range_zeroSection_iff]
  have hc : coord e p = Trivialization.linearMapAt ℂ e p.proj p.2 := by
    rw [Trivialization.coe_linearMapAt_of_mem (R := ℂ) e hp]
    rfl
  constructor
  · intro h0
    have hy := Trivialization.symm_apply_apply_mk e hp p.2
    change e.symm p.proj (coord e p) = p.2 at hy
    rw [h0, ← Trivialization.symmₗ_apply (R := ℂ) e hp, map_zero] at hy
    exact hy.symm
  · intro h0
    rw [hc, h0, map_zero]

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle ℂ E] [_root_.VectorBundle ℂ ℂ E] in
/-- The coordinate in `e` is continuous on the preimage of the base of `e`. -/
lemma continuousOn_coord (e : Trivialization ℂ (π ℂ E)) :
    ContinuousOn (coord e) (TotalSpace.proj ⁻¹' e.baseSet) := by
  rw [← e.source_eq]
  exact continuous_snd.comp_continuousOn e.continuousOn

/-- Over the base of `e`, the coordinate of a vector off the zero section is nonzero. -/
lemma coord_ne_zero {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {p : TotalSpace ℂ E} (hp : p.proj ∈ e.baseSet) (h0 : p ∉ Set.range (zeroSection ℂ E)) :
    coord e p ≠ 0 :=
  fun h ↦ h0 ((coord_eq_zero_iff hp).1 h)

/-- The ratio `p / r(π p)` of a vector off the zero section is nonzero. -/
lemma fibreRatio_ne_zero {p : TotalSpace ℂ E} (h0 : p ∉ Set.range (zeroSection ℂ E)) :
    fibreRatio p ≠ 0 :=
  coord_ne_zero (mem_baseSet_trivializationAt ℂ E p.proj) h0

end coord

section angle

/-- `exp` of the increment of a continuous logarithm is the ratio of the end values. -/
lemma exp_logIncrement {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {τ : Simplex Y 1}
    (h : ∃ L : C(stdSimplex ℝ (Fin 2), ℂ), ∀ x, exp (L x) = f (τ x)) :
    exp (logIncrement f τ) = f (τ (stdSimplex.vertex 1)) / f (τ (stdSimplex.vertex 0)) := by
  obtain ⟨L, hL⟩ := h
  rw [logIncrement_eq L hL, exp_sub, hL, hL]

/-- Changing the trivialization changes the edge phase by the increment of the logarithm of the
transition function. -/
lemma edgePhase_change {e e' : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] {τ : Simplex B 1} (hτ : Set.range τ ⊆ e.baseSet)
    (hτ' : Set.range τ ⊆ e'.baseSet) :
    edgePhase e' τ = edgePhase (E := E) e τ + logIncrement (transition e e') τ := by
  have hs := range_subset_simplexTriv (E := E) (MemTrivializationAtlas.out (e := e)) hτ
  simp only [edgePhase]
  rw [add_assoc, logIncrement_mul (g := transition (simplexTriv (E := E) τ) e)
    (h := transition e e')]
  · intro x
    rw [transition_trans (hs ⟨x, rfl⟩) (hτ ⟨x, rfl⟩) (hτ' ⟨x, rfl⟩), mul_comm]
  · exact exists_continuous_log_comp τ continuousOn_transition
      (fun y hy ↦ transition_ne_zero hy) (Set.subset_inter hs hτ)
  · exact exists_continuous_log_comp τ continuousOn_transition
      (fun y hy ↦ transition_ne_zero hy) (Set.subset_inter hτ hτ')

/-- The *angle increment* of a `1`-simplex `τ` of the total space: the increment of the
logarithm of the coordinate of `τ`, in the trivialization of its projection, minus the edge phase
of the projection. For `τ` off the zero section and over a trivializing open, it is the increment
of a continuous logarithm of the ratio `τ / r` of `τ` to the reference path `r` over `π ∘ τ`. -/
def angleIncrement (τ : Simplex (TotalSpace ℂ E) 1) : ℂ :=
  logIncrement (coord (simplexTriv (E := E) ((projMap E).comp τ))) τ -
    edgePhase (simplexTriv (E := E) ((projMap E).comp τ)) ((projMap E).comp τ)

/-- A simplex of the total space off the zero section and over the base of `e` has a continuous
logarithm of its coordinate in `e`. -/
lemma exists_log_coord {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e] {n : ℕ}
    {τ : Simplex (TotalSpace ℂ E) n} (hτ : Set.range ((projMap E).comp τ) ⊆ e.baseSet)
    (h0 : Set.range τ ⊆ (Set.range (zeroSection ℂ E))ᶜ) :
    ∃ L : C(stdSimplex ℝ (Fin (n + 1)), ℂ), ∀ x, exp (L x) = coord e (τ x) :=
  exists_continuous_log_comp τ ((continuousOn_coord e).mono Set.inter_subset_left)
    (fun _ hp ↦ coord_ne_zero hp.1 hp.2)
    (fun _ ⟨x, hx⟩ ↦ hx ▸ ⟨hτ ⟨x, rfl⟩, h0 ⟨x, rfl⟩⟩)

/-- The angle increment may be computed in any trivialization over the projection. -/
lemma angleIncrement_eq {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {τ : Simplex (TotalSpace ℂ E) 1} (hτ : Set.range ((projMap E).comp τ) ⊆ e.baseSet)
    (h0 : Set.range τ ⊆ (Set.range (zeroSection ℂ E))ᶜ) :
    angleIncrement τ = logIncrement (coord e) τ - edgePhase e ((projMap E).comp τ) := by
  set s := simplexTriv (E := E) ((projMap E).comp τ)
  have hs : Set.range ((projMap E).comp τ) ⊆ s.baseSet :=
    range_subset_simplexTriv (E := E) (MemTrivializationAtlas.out (e := e)) hτ
  have hlog : logIncrement (coord e) τ =
      logIncrement (fun p ↦ transition s e p.proj) τ + logIncrement (coord s) τ := by
    refine logIncrement_mul (fun x ↦ coord_eq_transition_mul (hs ⟨x, rfl⟩) (hτ ⟨x, rfl⟩)) ?_
      (exists_log_coord hs h0)
    exact exists_continuous_log_comp ((projMap E).comp τ) continuousOn_transition
      (fun y hy ↦ transition_ne_zero hy) (Set.subset_inter hs hτ)
  have htr : logIncrement (fun p ↦ transition s e p.proj) τ =
      logIncrement (transition s e) ((projMap E).comp τ) := rfl
  rw [angleIncrement, hlog, htr, edgePhase_change hs hτ]
  ring

/-- The alternating sum of a `0`-coboundary over the faces of a `2`-simplex vanishes. -/
lemma coboundary_comp_face_alternating {Y : Type} [TopologicalSpace Y]
    (f : Simplex Y 0 → ℂ) (σ : Simplex Y 2) :
    coboundary ℂ 0 f (σ.comp (face 1 0)) - coboundary ℂ 0 f (σ.comp (face 1 1)) +
      coboundary ℂ 0 f (σ.comp (face 1 2)) = 0 := by
  have := congr_fun (coboundary_coboundary 0 f) σ
  rw [coboundary_apply] at this
  simp [Fin.sum_univ_succ] at this
  linear_combination this

end angle

section thomCochain

/-- The `0`-cochain `p ↦ log (p / r(π p))` on the total space. -/
def logFibreRatio : Simplex (TotalSpace ℂ E) 0 → ℂ :=
  fun p ↦ log (fibreRatio (p (stdSimplex.vertex 0)))

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [_root_.VectorBundle ℂ ℂ E] in
/-- The coboundary of `logFibreRatio` on a `1`-simplex `τ` is `log λ(τ(1)) - log λ(τ(0))`. -/
lemma coboundary_logFibreRatio (τ : Simplex (TotalSpace ℂ E) 1) :
    coboundary ℂ 0 (logFibreRatio (E := E)) τ =
      log (fibreRatio (τ (stdSimplex.vertex 1))) - log (fibreRatio (τ (stdSimplex.vertex 0))) := by
  rw [coboundary_apply, Fin.sum_univ_two]
  simp only [logFibreRatio, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul,
    ContinuousMap.comp_apply]
  have e0 : face 0 0 (stdSimplex.vertex 0) = stdSimplex.vertex 1 := by
    simp [face, stdSimplex.map_vertex]
  have e1 : face 0 1 (stdSimplex.vertex 0) = stdSimplex.vertex 0 := by
    simp [face, stdSimplex.map_vertex]
  rw [e0, e1]
  ring

/-- A simplex of the total space is *small off the zero section* if it lies over the base of a
trivialization of the atlas and avoids the zero section. -/
def IsSmallOff {n : ℕ} (τ : Simplex (TotalSpace ℂ E) n) : Prop :=
  (∃ e ∈ trivializationAtlas ℂ E, Set.range ((projMap E).comp τ) ⊆ e.baseSet) ∧
    Set.range τ ⊆ (Set.range (zeroSection ℂ E))ᶜ

omit [∀ b, Module ℂ (E b)] [_root_.VectorBundle ℂ ℂ E] in
/-- A simplex obtained from one small off the zero section by precomposition is small off the zero
section. -/
lemma IsSmallOff.comp {n m : ℕ} {τ : Simplex (TotalSpace ℂ E) n} (hτ : IsSmallOff τ)
    (g : C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ (Fin (n + 1)))) : IsSmallOff (τ.comp g) := by
  obtain ⟨⟨e, he, hπ⟩, h0⟩ := hτ
  exact ⟨⟨e, he, fun _ ⟨x, hx⟩ ↦ hπ ⟨g x, hx⟩⟩, fun _ ⟨x, hx⟩ ↦ h0 ⟨g x, hx⟩⟩

/-- On a `1`-simplex small off the zero section, the angle increment differs from the coboundary of
`logFibreRatio` by an integer multiple of `2πi`. -/
lemma exists_angleIncrement_sub_eq {τ : Simplex (TotalSpace ℂ E) 1} (hτ : IsSmallOff τ) :
    ∃ k : ℤ, angleIncrement τ - coboundary ℂ 0 (logFibreRatio (E := E)) τ =
      k * (2 * Real.pi * I) := by
  obtain ⟨⟨e, he, hπ⟩, h0⟩ := hτ
  have : MemTrivializationAtlas e := ⟨he⟩
  refine exp_eq_one_iff.1 ?_
  have h1 : (τ (stdSimplex.vertex 1)) ∉ Set.range (zeroSection ℂ E) := h0 ⟨_, rfl⟩
  have h0' : (τ (stdSimplex.vertex 0)) ∉ Set.range (zeroSection ℂ E) := h0 ⟨_, rfl⟩
  have b1 : (τ (stdSimplex.vertex 1)).proj ∈ e.baseSet := hπ ⟨_, rfl⟩
  have b0 : (τ (stdSimplex.vertex 0)).proj ∈ e.baseSet := hπ ⟨_, rfl⟩
  rw [angleIncrement_eq hπ h0, coboundary_logFibreRatio, exp_sub, exp_sub, exp_sub,
    exp_logIncrement (exists_log_coord hπ h0), exp_edgePhase hπ,
    exp_log (fibreRatio_ne_zero h1), exp_log (fibreRatio_ne_zero h0'),
    coord_eq_mul b1, coord_eq_mul b0]
  have := vertexCoord_ne_zero (E := E) b1
  have := vertexCoord_ne_zero (E := E) b0
  have := fibreRatio_ne_zero h1
  have := fibreRatio_ne_zero h0'
  change _ / (vertexCoord e (τ (stdSimplex.vertex 1)).proj /
    vertexCoord e (τ (stdSimplex.vertex 0)).proj) / _ = 1
  field_simp

/-- The winding cochain: on a `1`-simplex `τ` small off the zero section, the integer
`(angleIncrement τ - δ log (τ / r)) / 2πi`; `0` elsewhere. -/
def windingEdge (τ : Simplex (TotalSpace ℂ E) 1) : ℤ := by
  classical
  exact if h : IsSmallOff τ then (exists_angleIncrement_sub_eq h).choose else 0

/-- On a `1`-simplex `τ` small off the zero section, `2πi · windingEdge τ` is
`angleIncrement τ - δ log (τ / r)`. -/
lemma windingEdge_mul {τ : Simplex (TotalSpace ℂ E) 1} (hτ : IsSmallOff τ) :
    (windingEdge τ : ℂ) * (2 * Real.pi * I) =
      angleIncrement τ - coboundary ℂ 0 (logFibreRatio (E := E)) τ := by
  rw [windingEdge, dite_eq_left hτ]
  exact (exists_angleIncrement_sub_eq hτ).choose_spec.symm

/-- The winding cochain vanishes on `1`-simplices not small off the zero section. -/
lemma windingEdge_of_not {τ : Simplex (TotalSpace ℂ E) 1} (hτ : ¬IsSmallOff τ) :
    windingEdge τ = 0 := by
  rw [windingEdge, dite_eq_right hτ]

/-- The *Thom cochain* on `2`-simplices of the total space: the obstruction cochain of the
projection plus the coboundary of the winding cochain. -/
def thomCochain (σ : Simplex (TotalSpace ℂ E) 2) : ℤ :=
  obstructionCochain (E := E) ((projMap E).comp σ) + coboundary ℤ 1 windingEdge σ

private lemma two_pi_I_ne_zero : (2 * Real.pi * I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, I_ne_zero]

/-- The Thom cochain vanishes on the `2`-simplices small off the zero section. -/
lemma thomCochain_eq_zero {σ : Simplex (TotalSpace ℂ E) 2} (hσ : IsSmallOff σ) :
    thomCochain σ = 0 := by
  obtain ⟨⟨e, he, hπ⟩, h0⟩ := hσ
  have : MemTrivializationAtlas e := ⟨he⟩
  have hface : ∀ k : Fin 3, IsSmallOff (σ.comp (face 1 k)) :=
    fun k ↦ IsSmallOff.comp ⟨⟨e, he, hπ⟩, h0⟩ _
  have hface' : ∀ k : Fin 3, Set.range ((projMap E).comp (σ.comp (face 1 k))) ⊆ e.baseSet :=
    fun k ↦ fun _ ⟨x, hx⟩ ↦ hπ ⟨face 1 k x, hx⟩
  have hface0 : ∀ k : Fin 3, Set.range (σ.comp (face 1 k)) ⊆ (Set.range (zeroSection ℂ E))ᶜ :=
    fun k ↦ fun _ ⟨x, hx⟩ ↦ h0 ⟨face 1 k x, hx⟩
  have hsum := sum_logIncrement_face σ (exists_log_coord hπ h0)
  have hob : (obstructionCochain (E := E) ((projMap E).comp σ) : ℂ) * (2 * Real.pi * I) =
      edgePhase e (((projMap E).comp σ).comp (face 1 0)) -
        edgePhase e (((projMap E).comp σ).comp (face 1 1)) +
        edgePhase e (((projMap E).comp σ).comp (face 1 2)) := by
    rw [obstructionCochain_mul (E := E) hπ, obstructionPhase_eq_coboundary hπ, coboundary_apply]
    simp [Fin.sum_univ_succ]
    ring
  have hw : ∀ k : Fin 3, (windingEdge (σ.comp (face 1 k)) : ℂ) * (2 * Real.pi * I) =
      logIncrement (coord e) (σ.comp (face 1 k)) -
        edgePhase e (((projMap E).comp σ).comp (face 1 k)) -
        coboundary ℂ 0 (logFibreRatio (E := E)) (σ.comp (face 1 k)) := fun k ↦ by
    rw [windingEdge_mul (hface k), angleIncrement_eq (hface' k) (hface0 k)]
    rfl
  have key : ((thomCochain σ : ℤ) : ℂ) * (2 * Real.pi * I) = 0 := by
    rw [thomCochain, coboundary_apply]
    push_cast
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two] at hsum ⊢
    linear_combination hob + hw 0 - hw 1 + hw 2 + hsum -
      coboundary_comp_face_alternating (logFibreRatio (E := E)) σ
  exact_mod_cast (mul_eq_zero.1 key).resolve_right two_pi_I_ne_zero

/-- The Thom cochain is the pull-back of the obstruction cochain along the projection plus the
coboundary of the winding cochain. -/
lemma thomCochain_eq : thomCochain (E := E) =
    (fun σ ↦ obstructionCochain (E := E) ((projMap E).comp σ)) + coboundary ℤ 1 windingEdge :=
  rfl

/-- The Thom cochain is a cocycle on the `3`-simplices over a trivializing open. -/
lemma coboundary_thomCochain {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {ρ : Simplex (TotalSpace ℂ E) 3} (hρ : Set.range ((projMap E).comp ρ) ⊆ e.baseSet) :
    coboundary ℤ 2 (thomCochain (E := E)) ρ = 0 := by
  rw [thomCochain_eq, map_add, coboundary_coboundary, add_zero]
  have h := coboundary_obstructionCochain (E := E) hρ
  rw [coboundary_apply] at h ⊢
  exact h

variable (E) in
/-- The cover of the total space by the preimages of the trivializing opens. -/
def totalCover : Set (Set (TotalSpace ℂ E)) := (fun U ↦ TotalSpace.proj ⁻¹' U) '' atlasCover E

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [_root_.VectorBundle ℂ ℂ E] in
/-- Each member of `totalCover E` is open. -/
lemma isOpen_of_mem_totalCover {V : Set (TotalSpace ℂ E)} (hV : V ∈ totalCover E) : IsOpen V := by
  obtain ⟨U, hU, rfl⟩ := hV
  exact (isOpen_of_mem_atlasCover hU).preimage (FiberBundle.continuous_proj ℂ E)

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [_root_.VectorBundle ℂ ℂ E] in
/-- The sets of `totalCover E` cover the total space. -/
lemma sUnion_totalCover : ⋃₀ totalCover E = Set.univ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  obtain ⟨U, hU, hp⟩ := Set.mem_sUnion.1
    ((sUnion_atlasCover (E := E)).symm ▸ Set.mem_univ p.proj : p.proj ∈ ⋃₀ atlasCover E)
  exact ⟨_, ⟨U, hU, rfl⟩, hp⟩

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [_root_.VectorBundle ℂ ℂ E] in
/-- A simplex contained in a member of `totalCover E` lies over the base of a trivialization of the
atlas. -/
lemma exists_of_mem_totalCover {n : ℕ} {τ : Simplex (TotalSpace ℂ E) n}
    (hτ : ∃ V ∈ totalCover E, Set.range τ ⊆ V) :
    ∃ e ∈ trivializationAtlas ℂ E, Set.range ((projMap E).comp τ) ⊆ e.baseSet := by
  obtain ⟨_, ⟨_, ⟨e, he, rfl⟩, rfl⟩, hτ⟩ := hτ
  exact ⟨e, he, fun _ ⟨x, hx⟩ ↦ hx ▸ hτ ⟨x, rfl⟩⟩

variable (E) in
/-- The *Thom cocycle*: the Thom cochain on the simplices over trivializing opens, transported to
all `2`-simplices of the total space by the small-chains map `ρ`. -/
def thomCocycle : Simplex (TotalSpace ℂ E) 2 → ℤ :=
  SingularCochain.pullback (smallChainMap ℤ (totalCover E) 2) (thomCochain (E := E))

/-- A cochain vanishing on every simplex in the support of a chain vanishes on the chain. -/
lemma eval_eq_zero_of_forall_mem_support {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {φ : Simplex Y n → ℤ} {c : Chain ℤ Y n} (h : ∀ σ ∈ c.support, φ σ = 0) :
    SingularCochain.eval φ c = 0 := by
  rw [SingularCochain.eval, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun σ hσ ↦ by rw [h σ hσ, smul_zero]

/-- The Thom cocycle is a cocycle. -/
lemma coboundary_thomCocycle : coboundary ℤ 2 (thomCocycle E) = 0 := by
  rw [thomCocycle, coboundary_pullback_smallChainMap]
  funext σ
  refine ComplexLineBundle.eval_eq_zero_of_mem_small (𝒰 := totalCover E) ?_
    (smallChainMap_single_mem_small (fun _ hV ↦ isOpen_of_mem_totalCover hV) 3
      (by rw [sUnion_totalCover]; exact Set.subset_univ _))
  intro ρ hρ
  obtain ⟨e, he, hρ'⟩ := exists_of_mem_totalCover hρ
  have : MemTrivializationAtlas e := ⟨he⟩
  exact coboundary_thomCochain hρ'

/-- The Thom cocycle vanishes on the simplices off the zero section. -/
lemma thomCocycle_eq_zero {σ : Simplex (TotalSpace ℂ E) 2}
    (hσ : Set.range σ ⊆ (Set.range (zeroSection ℂ E))ᶜ) : thomCocycle E σ = 0 := by
  have h1 := smallChainMap_single_mem_small (R := ℤ) (fun _ hV ↦ isOpen_of_mem_totalCover hV) 2
    (σ := σ) (by rw [sUnion_totalCover]; exact Set.subset_univ _)
  have h2 := smallChainMap_mem_inside (R := ℤ) (totalCover E) 2 (single_mem_inside (R := ℤ) hσ)
  refine eval_eq_zero_of_forall_mem_support fun τ hτ ↦ thomCochain_eq_zero ?_
  exact ⟨exists_of_mem_totalCover ((Finsupp.mem_supported ℤ _).1 h1 hτ),
    (Finsupp.mem_supported ℤ _).1 h2 hτ⟩

end thomCochain

section fibre

/-- The increment of a logarithm along a constant `1`-simplex is `0`. -/
lemma logIncrement_of_const {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {τ : Simplex Y 1}
    {y : Y} (hτ : ∀ t, τ t = y) : logIncrement f τ = 0 := by
  by_cases h : ∃ L : C(stdSimplex ℝ (Fin 2), ℂ), ∀ x, exp (L x) = f (τ x)
  · obtain ⟨L, hL⟩ := h
    rw [logIncrement_eq L hL]
    have := continuous_log_sub_eq (n := 1) (L := L)
      (L' := ContinuousMap.const _ (L (stdSimplex.vertex 0)))
      (fun x ↦ by simp only [ContinuousMap.const_apply, hL, hτ]) (stdSimplex.vertex 1)
      (stdSimplex.vertex 0)
    simpa using this
  · rw [logIncrement, dite_eq_right h]

omit [∀ b, Module ℂ (E b)] [_root_.VectorBundle ℂ ℂ E] in
/-- The edge phase of a constant `1`-simplex is `0`. -/
lemma edgePhase_of_const (e : Trivialization ℂ (π ℂ E)) {τ : Simplex B 1} {x : B}
    (hτ : ∀ t, τ t = x) : edgePhase (E := E) e τ = 0 := by
  rw [edgePhase, logIncrement_of_const hτ, add_zero, edgeLog, hτ, hτ]
  by_cases h : vertexCoord (simplexTriv (E := E) τ) x = 0
  · rw [h, div_zero, log_zero]
  · rw [div_self h, log_one]

/-- The obstruction cochain vanishes on a constant `2`-simplex. -/
lemma obstructionCochain_of_const {σ : Simplex B 2} {x : B} (hσ : ∀ t, σ t = x) :
    obstructionCochain (E := E) σ = 0 := by
  have hrange : Set.range σ ⊆ (trivializationAt ℂ E x).baseSet := by
    rintro _ ⟨t, rfl⟩
    rw [hσ]
    exact mem_baseSet_trivializationAt ℂ E x
  have h := obstructionCochain_mul (E := E) hrange
  have h0 : obstructionPhase (E := E) σ = 0 := by
    rw [obstructionPhase]
    exact Finset.sum_eq_zero fun k _ ↦ by
      rw [edgePhase_of_const _ (x := x) (fun t ↦ hσ _), mul_zero]
  rw [h0] at h
  exact_mod_cast (mul_eq_zero.1 h).resolve_right two_pi_I_ne_zero

/-- **The increment of the logarithm along a segment.** If `f ∘ τ` is
`t ↦ c (t₀ a + t₁ b)` with `c, a ≠ 0` and `b / a` in the slit plane, the increment of a
continuous logarithm of `f` along `τ` is `log (b / a)`. -/
lemma logIncrement_of_segment {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {τ : Simplex Y 1}
    {a b c : ℂ} (hc : c ≠ 0) (ha : a ≠ 0) (hab : b / a ∈ slitPlane)
    (hf : ∀ t, f (τ t) = c * ((t 0 : ℂ) * a + (t 1 : ℂ) * b)) :
    logIncrement f τ = log (b / a) := by
  set w := b / a
  have hmem : ∀ t : stdSimplex ℝ (Fin 2), 1 + ((t 1 : ℝ) : ℂ) * (w - 1) ∈ slitPlane := fun t ↦ by
    have := StarConvex.add_smul_mem starConvex_one_slitPlane (y := w - 1)
      (by rwa [add_sub_cancel]) (stdSimplex.zero_le t 1)
      (stdSimplex.le_one t 1)
    simpa [Complex.real_smul] using this
  let L : C(stdSimplex ℝ (Fin 2), ℂ) :=
    ⟨fun t ↦ log (c * a) + log (1 + ((t 1 : ℝ) : ℂ) * (w - 1)),
      continuous_const.add (Continuous.clog (continuous_const.add
        ((continuous_ofReal.comp ((continuous_apply 1).comp continuous_subtype_val)).mul
          continuous_const)) hmem)⟩
  have hL : ∀ t, exp (L t) = f (τ t) := fun t ↦ by
    change exp (log (c * a) + log (1 + ((t 1 : ℝ) : ℂ) * (w - 1))) = _
    rw [exp_add, exp_log (mul_ne_zero hc ha), exp_log (slitPlane_ne_zero (hmem t)), hf]
    have h01 : (t 0 : ℂ) = 1 - (t 1 : ℂ) := by
      have := stdSimplex.add_eq_one t
      rw [eq_sub_iff_add_eq]
      exact_mod_cast this
    rw [h01]
    simp only [w]
    field_simp
    ring
  rw [logIncrement_eq L hL]
  change log (c * a) + log (1 + ((stdSimplex.vertex (S := ℝ) (1 : Fin 2) 1 : ℝ) : ℂ) * (w - 1)) -
    (log (c * a) + log (1 + ((stdSimplex.vertex (S := ℝ) (0 : Fin 2) 1 : ℝ) : ℂ) * (w - 1))) = _
  simp

private lemma face_apply_self (k : Fin 3) (t : stdSimplex ℝ (Fin 2)) : face 1 k t k = 0 := by
  simp [face, FunOnFinite.linearMap_apply_apply, Fin.succAbove_ne]

open ThomClass in
/-- **The Thom cocycle on a fibre.** On a positively oriented `2`-simplex around `0` in a fibre
`E_x ≅ ℂ`, the Thom cocycle takes the value `1`. -/
theorem thomCocycle_fibreSimplex (x : B) (ψ : (Fin 1 → ℂ) ≃L[ℂ] E x)
    (v : Fin (2 * 1 + 1) → (Fin 1 → ℂ))
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis 1) v) :
    thomCocycle E (fibreSimplex ℂ x ψ v) = 1 := by
  set σ : Simplex (TotalSpace ℂ E) 2 := fibreSimplex ℂ x ψ v with hσdef
  set e := trivializationAt ℂ E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ E x
  have hπ : ∀ t, ((projMap E).comp σ) t = x := fun t ↦ rfl
  have hsmall : ∃ V ∈ totalCover E, Set.range σ ⊆ V :=
    ⟨_, ⟨e.baseSet, ⟨e, trivialization_mem_atlas ℂ E x, rfl⟩, rfl⟩,
      fun _ ⟨t, ht⟩ ↦ ht ▸ hx⟩
  have hval : thomCocycle E σ = thomCochain σ := by
    simp only [thomCocycle, SingularCochain.pullback, LinearMap.coe_mk, AddHom.coe_mk,
      smallChainMap_single_of_subset hsmall, eval_single_one]
  rw [hval, thomCochain, obstructionCochain_of_const hπ, zero_add]
  have hface : ∀ k : Fin 3, IsSmallOff (σ.comp (face 1 k)) := fun k ↦
    ⟨⟨e, trivialization_mem_atlas ℂ E x, fun _ ⟨t, ht⟩ ↦ ht ▸ hx⟩, fun _ ⟨t, ht⟩ ↦ ht ▸
      fibreSimplex_notMem_range_zeroSection ℂ x ψ hv (face 1 k t) ⟨k, face_apply_self k t⟩⟩
  set c := coord e ⟨x, ψ (fun _ ↦ 1)⟩
  have hlin : ∀ z : Fin 1 → ℂ, coord e ⟨x, ψ z⟩ = c * z 0 := fun z ↦ by
    have h := Trivialization.coe_linearMapAt_of_mem (R := ℂ) e hx
    have hz : z = z 0 • (fun _ ↦ (1 : ℂ)) := by
      funext j
      simp [Subsingleton.elim j 0]
    change (e ⟨x, ψ z⟩).2 = (e ⟨x, ψ (fun _ ↦ 1)⟩).2 * z 0
    rw [← congrFun h, ← congrFun h, hz, map_smul, map_smul, smul_eq_mul, mul_comm]
    simp
  have hc : c ≠ 0 := by
    refine coord_ne_zero hx fun h ↦ ?_
    rw [ThomClass.mem_range_zeroSection_iff] at h
    have : (fun _ ↦ (1 : ℂ)) = (0 : Fin 1 → ℂ) := ψ.injective (h.trans (map_zero ψ).symm)
    simpa using congrFun this 0
  obtain ⟨h01, h12, h02⟩ := im_div_of_isOrientedSimplexAroundZero hv
  have ne : ∀ {p q : ℂ}, (q / p).im ≠ 0 → p ≠ 0 := by
    rintro p q h rfl
    simp at h
  have hseg : ∀ (k : Fin 3), v (k.succAbove 0) 0 ≠ 0 →
      v (k.succAbove 1) 0 / v (k.succAbove 0) 0 ∈ slitPlane →
      logIncrement (coord e) (σ.comp (face 1 k)) =
        log (v (k.succAbove 1) 0 / v (k.succAbove 0) 0) := fun k ha hab ↦ by
    refine logIncrement_of_segment hc ha hab fun t ↦ ?_
    change coord e ⟨x, ψ (affineSimplex v (face 1 k t))⟩ = _
    have haff : affineSimplex v (face 1 k t) = affineSimplex (v ∘ k.succAbove) t :=
      DFunLike.congr_fun (FundamentalClass.affineSimplex_comp_face (n := 1) v k) t
    rw [hlin, haff, affineSimplex_apply, Fin.sum_univ_two]
    simp [Complex.real_smul]
  have hw : ∀ k : Fin 3, (windingEdge (σ.comp (face 1 k)) : ℂ) * (2 * Real.pi * I) =
      logIncrement (coord e) (σ.comp (face 1 k)) -
        coboundary ℂ 0 (logFibreRatio (E := E)) (σ.comp (face 1 k)) := fun k ↦ by
    rw [windingEdge_mul (hface k), angleIncrement_eq (e := e) (fun _ ⟨t, ht⟩ ↦ ht ▸ hx)
      (hface k).2, edgePhase_of_const e (x := x) (fun t ↦ rfl), sub_zero]
  have h01' : 0 < (v (1 : Fin 3) 0 / v (0 : Fin 3) 0).im := h01
  have h12' : 0 < (v (2 : Fin 3) 0 / v (1 : Fin 3) 0).im := h12
  have h02' : (v (2 : Fin 3) 0 / v (0 : Fin 3) 0).im < 0 := h02
  have slit : ∀ {p : ℂ}, p.im ≠ 0 → p ∈ slitPlane := fun h ↦ mem_slitPlane_iff.2 (Or.inr h)
  have s0 : logIncrement (coord e) (σ.comp (face 1 0)) = log (v 2 0 / v 1 0) :=
    hseg 0 (ne h12'.ne') (slit h12'.ne')
  have s1 : logIncrement (coord e) (σ.comp (face 1 1)) = log (v 2 0 / v 0 0) :=
    hseg 1 (ne h02'.ne) (slit h02'.ne)
  have s2 : logIncrement (coord e) (σ.comp (face 1 2)) = log (v 1 0 / v 0 0) :=
    hseg 2 (ne h01'.ne') (slit h01'.ne')
  have htri := log_div_sub_log_div_add_log_div h01' h12' h02'
  have key : ((coboundary ℤ 1 windingEdge σ : ℤ) : ℂ) * (2 * Real.pi * I) =
      1 * (2 * Real.pi * I) := by
    rw [coboundary_apply]
    push_cast
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
    linear_combination hw 0 - hw 1 + hw 2 + s0 - s1 + s2 -
      coboundary_comp_face_alternating (logFibreRatio (E := E)) σ + htri
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero key

end fibre

section thomClass

/-- The Thom cocycle is a relative cocycle of `(E, E - 0_E)`. -/
lemma thomCocycle_mem_relCocycles :
    thomCocycle E ∈ relCocycles ℤ (Set.range (zeroSection ℂ E))ᶜ 2 :=
  ⟨fun _ hσ ↦ thomCocycle_eq_zero hσ, LinearMap.mem_ker.2 coboundary_thomCocycle⟩

variable (E) in
/-- The Thom cocycle in a degree `d = 2`. -/
def thomCocycleOfEq {d : ℕ} (h : d = 2) : Simplex (TotalSpace ℂ E) d → ℤ :=
  fun σ ↦ thomCocycle E (h ▸ σ)

/-- The Thom cocycle in a degree `d = 2` is a relative cocycle of `(E, E - 0_E)`. -/
lemma thomCocycleOfEq_mem_relCocycles {d : ℕ} (h : d = 2) :
    thomCocycleOfEq E h ∈ relCocycles ℤ (Set.range (zeroSection ℂ E))ᶜ d := by
  subst h
  exact thomCocycle_mem_relCocycles

/-- `2 · dim_ℂ ℂ = 2`. -/
lemma two_mul_finrank_eq : 2 * Module.finrank ℂ ℂ = 2 := by simp

open ThomClass in
/-- The class of the Thom cocycle is a Thom class. -/
theorem isThomClass_thomCocycle :
    IsThomClass (R := ℤ) ℂ E ((relativeSingularCohomologyEquiv ℤ
      (Y := TopCat.of (TotalSpace ℂ E)) (Set.range (zeroSection ℂ E))ᶜ
        (2 * Module.finrank ℂ ℂ)).symm (Submodule.Quotient.mk
          ⟨thomCocycleOfEq E two_mul_finrank_eq,
            thomCocycleOfEq_mem_relCocycles two_mul_finrank_eq⟩)) := by
  intro x ψ v hv
  rw [LinearEquiv.apply_symm_apply, relEval_mk, eval_single_one]
  change thomCocycleOfEq E two_mul_finrank_eq (fibreSimplex ℂ x ψ v) = 1
  have hr := Module.finrank_self ℂ
  generalize two_mul_finrank_eq = h
  revert ψ v hv h
  generalize Module.finrank ℂ ℂ = r at hr ⊢
  subst hr
  intro ψ v hv h
  exact thomCocycle_fibreSimplex x ψ v hv

/-- The Thom class of a complex line bundle is the class of its Thom cocycle. -/
theorem thomClass_eq :
    ThomClass.thomClass ℤ ℂ E = (relativeSingularCohomologyEquiv ℤ
      (Y := TopCat.of (TotalSpace ℂ E)) (Set.range (zeroSection ℂ E))ᶜ
        (2 * Module.finrank ℂ ℂ)).symm (Submodule.Quotient.mk
          ⟨thomCocycleOfEq E two_mul_finrank_eq,
            thomCocycleOfEq_mem_relCocycles two_mul_finrank_eq⟩) :=
  (ThomClass.eq_thomClass ℂ E isThomClass_thomCocycle).symm

end thomClass

section coboundary

/-! ### Cocycles agreeing on small simplices -/

variable {Y : Type} [TopologicalSpace Y]

private theorem eval_linearMap' {n k : ℕ} (T : Chain ℤ Y n →ₗ[ℤ] Chain ℤ Y k)
    (ψ : Simplex Y k → ℤ) (c : Chain ℤ Y n) :
    eval ψ (T c) = eval (fun τ ↦ eval ψ (T (Finsupp.single τ 1))) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul, map_smul]
    simp

private theorem eval_eq_of_eqOn_small' {n : ℕ} {𝒰 : Set (Set Y)} {φ φ' : Simplex Y n → ℤ}
    (h : ∀ σ : Simplex Y n, (∃ U ∈ 𝒰, Set.range σ ⊆ U) → φ σ = φ' σ) {c : Chain ℤ Y n}
    (hc : c ∈ small ℤ n 𝒰) : eval φ c = eval φ' c := by
  rw [← sub_eq_zero, ← eval_sub_cochain]
  exact ComplexLineBundle.eval_eq_zero_of_mem_small (fun σ hσ ↦ by simp [h σ hσ]) hc

private theorem pullback_smallChainMap_sub' (𝒰 : Set (Set Y)) {ψ : Simplex Y 2 → ℤ}
    (hδ : coboundary ℤ 2 ψ = 0) :
    SingularCochain.pullback (smallChainMap ℤ 𝒰 2) ψ - ψ =
      coboundary ℤ 1 (fun τ ↦ -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) := by
  funext σ
  have e1 : eval ψ (bd ℤ 2 (smallHomotopy ℤ 𝒰 2 (Finsupp.single σ 1))) = 0 := by
    rw [← eval_coboundary, hδ]
    simp
  have e2 : eval ψ (smallHomotopy ℤ 𝒰 1 (bd ℤ 1 (Finsupp.single σ 1))) =
      coboundary ℤ 1 (fun τ ↦ eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) σ := by
    rw [eval_linearMap', ← eval_coboundary]
    simp
  change eval ψ (smallChainMap ℤ 𝒰 (1 + 1) (Finsupp.single σ 1)) - ψ σ = _
  have hneg : (fun τ ↦ -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) =
      -(fun τ ↦ eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) := rfl
  rw [smallChainMap_succ, map_sub, map_sub, e1, e2, hneg, map_neg]
  simp

/-- A `2`-cocycle vanishing on the small simplices of an open cover is a coboundary. -/
theorem exists_eq_coboundary_of_eqOn_small {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : ⋃₀ 𝒰 = Set.univ) {ψ : Simplex Y 2 → ℤ} (hδ : coboundary ℤ 2 ψ = 0)
    (hψ : ∀ σ : Simplex Y 2, (∃ U ∈ 𝒰, Set.range σ ⊆ U) → ψ σ = 0) :
    ∃ m : Simplex Y 1 → ℤ, ψ = coboundary ℤ 1 m := by
  have hρ : SingularCochain.pullback (smallChainMap ℤ 𝒰 2) ψ = 0 := by
    funext σ
    have hsmall := smallChainMap_single_mem_small (R := ℤ) h𝒰 2 (σ := σ)
      (by rw [hcov]; exact Set.subset_univ _)
    change eval ψ (smallChainMap ℤ 𝒰 2 (Finsupp.single σ 1)) = 0
    rw [eval_eq_of_eqOn_small' (φ' := 0) (fun σ h ↦ hψ σ h) hsmall]
    simp
  refine ⟨-(fun τ ↦ -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))), ?_⟩
  rw [map_neg, ← pullback_smallChainMap_sub' 𝒰 hδ, hρ, zero_sub, neg_neg]

end coboundary

section euler

/-- On the zero section, the Thom cocycle is the obstruction cocycle on small simplices. -/
lemma thomCocycle_zeroMap_comp {σ : Simplex B 2} (hσ : ∃ U ∈ atlasCover E, Set.range σ ⊆ U) :
    thomCocycle E ((zeroMap E).comp σ) = obstructionCocycle E σ := by
  obtain ⟨U, hU, hσU⟩ := hσ
  have hsmall : ∃ V ∈ totalCover E, Set.range ((zeroMap E).comp σ) ⊆ V :=
    ⟨_, ⟨U, hU, rfl⟩, fun _ ⟨t, ht⟩ ↦ ht ▸ hσU ⟨t, rfl⟩⟩
  have h1 : thomCocycle E ((zeroMap E).comp σ) = thomCochain ((zeroMap E).comp σ) := by
    simp only [thomCocycle, SingularCochain.pullback, LinearMap.coe_mk, AddHom.coe_mk,
      smallChainMap_single_of_subset hsmall, eval_single_one]
  have h2 : obstructionCocycle E σ = obstructionCochain (E := E) σ := by
    simp only [obstructionCocycle, SingularCochain.pullback, LinearMap.coe_mk, AddHom.coe_mk,
      smallChainMap_single_of_subset ⟨U, hU, hσU⟩, eval_single_one]
  have hface : ∀ k : Fin 3, windingEdge (((zeroMap E).comp σ).comp (face 1 k)) = 0 := fun k ↦
    windingEdge_of_not fun h ↦ h.2 ⟨stdSimplex.vertex 0, rfl⟩ ⟨_, rfl⟩
  rw [h1, h2, thomCochain, coboundary_apply]
  simp only [hface, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- **The first Chern class of a complex line bundle is its Euler class** (Milnor–Stasheff,
§14, Thm. 12.5): the restriction `0^* u_E ∈ H²(B; ℤ)` of the Thom class of `E` along the zero
section is the first Chern class `c₁(E)`. The Euler class lives in degree `2 · dim_ℂ ℂ`, moved to
degree `2` by `MMP.cohomologyWithSupports.congrIndex`. -/
theorem congrIndex_eulerClass_eq_firstChernClass :
    cohomologyWithSupports.congrIndex ℤ (TopCat.of B) rfl (by rw [two_mul_finrank_eq])
      ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom ⟨zeroSection ℂ E, Trivialization.continuous_zeroSection ℂ⟩)
        (A' := Set.univᶜ) (fun x hx ↦ (hx (Set.mem_univ x)).elim) _).hom
          (ThomClass.thomClass ℤ ℂ E)) = firstChernClass E := by
  rw [thomClass_eq]
  suffices aux : ∀ {d : ℕ} (h : d = 2) (hk : ((d : ℕ) : ℤ) = ((2 : ℕ) : ℤ)),
      cohomologyWithSupports.congrIndex ℤ (TopCat.of B) rfl hk
        ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
          (TopCat.ofHom ⟨zeroSection ℂ E, Trivialization.continuous_zeroSection ℂ⟩)
          (A' := Set.univᶜ) (fun x hx ↦ (hx (Set.mem_univ x)).elim) d).hom
            ((relativeSingularCohomologyEquiv ℤ (Y := TopCat.of (TotalSpace ℂ E))
              (Set.range (zeroSection ℂ E))ᶜ d).symm (Submodule.Quotient.mk
                ⟨thomCocycleOfEq E h, thomCocycleOfEq_mem_relCocycles h⟩))) =
        firstChernClass E from aux two_mul_finrank_eq _
  intro d h hk
  subst h
  change (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom ⟨zeroSection ℂ E, Trivialization.continuous_zeroSection ℂ⟩)
      (A' := Set.univᶜ) (fun x hx ↦ (hx (Set.mem_univ x)).elim) (2 : ℕ)).hom
        ((relativeSingularCohomologyEquiv ℤ (Y := TopCat.of (TotalSpace ℂ E))
          (Set.range (zeroSection ℂ E))ᶜ 2).symm (Submodule.Quotient.mk
            ⟨thomCocycleOfEq E rfl, thomCocycleOfEq_mem_relCocycles rfl⟩)) = firstChernClass E
  apply (relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set (TopCat.of B)) 2).injective
  erw [relativeSingularCohomologyEquiv_map, LinearEquiv.apply_symm_apply, relCohomologyMap_mk]
  rw [firstChernClass, cohomologyWithSupports.ofCocycle, LinearEquiv.apply_symm_apply]
  refine (Submodule.Quotient.eq _).2 ?_
  change cochainPullback ℤ (TopCat.ofHom (zeroMap E)) 2 (thomCocycle E) - obstructionCocycle E ∈
    relCoboundaries ℤ (Set.univᶜ : Set (TopCat.of B)) (1 + 1)
  obtain ⟨m, hm⟩ := exists_eq_coboundary_of_eqOn_small (𝒰 := atlasCover E)
    (fun _ hU ↦ isOpen_of_mem_atlasCover hU) sUnion_atlasCover
    (ψ := cochainPullback ℤ (TopCat.ofHom (zeroMap E)) 2 (thomCocycle E) - obstructionCocycle E)
    (by
      rw [map_sub, coboundary_obstructionCocycle, sub_zero]
      funext ρ
      have h := congr_fun (coboundary_thomCocycle (E := E)) ((zeroMap E).comp ρ)
      rw [coboundary_apply] at h ⊢
      exact h)
    (fun σ hσ ↦ by
      rw [Pi.sub_apply, cochainPullback_apply, sub_eq_zero]
      exact thomCocycle_zeroMap_comp hσ)
  exact ⟨m, fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp), hm.symm⟩

end euler

end ComplexLineBundle

end MMP.Analytic
