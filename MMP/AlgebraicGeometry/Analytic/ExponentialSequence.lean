module
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Germ
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularIdealSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule

/-!
# The exponential sequence on the analytification

Let `X` be a scheme of finite type over `ℂ` and `X^an` its analytification
(`MMP.Analytic.analytification`),
with its full structure sheaf `𝒪_{X^an}`, nilpotents included: on the `ℂ`-points of an affine
chart `Spec ℂ[z₁, …, zₙ]/I` it is `(𝒪_{ℂⁿ}/I 𝒪_{ℂⁿ})|_Z`. The exponential sequence
`0 → ℤ_{X^an} → 𝒪_{X^an} → 𝒪_{X^an}^× → 1` is a short exact sequence of sheaves of abelian
groups on `X(ℂ)`; the first map sends an integer `n` to the constant section `n`, and the second
sends the class of a holomorphic germ `u` to the class of `exp(2πi u)`.

## Main results

* `MMP.Analytic.exists_shortExact_exponentialSequence`: the exponential sequence, with both of
  its maps pinned down.

## Implementation notes

* `𝒪_{X^an}` as a sheaf of abelian groups is the additive group of the sheaf of rings
  `MMP.Analytic.ringCatSheaf`.
* `𝒪_{X^an}^×` is the units sheaf `Stacks.Cohomology.Generators.unitsSheaf` of the ringed
  space `X^an`, written additively; `ℤ_{X^an}` is the constant sheaf, the sheafification of the
  constant presheaf `ℤ`.
* A section of `𝒪_{X^an}` over `W` is a family, over the points `x ∈ W` and the charts `c`
  containing `x`, of classes of holomorphic germs at the coordinates of `x` in `c`; the second
  map is pinned by its value on each such component: if the component of `s` is the class of
  the germ of `f`, that of its image is the class of the germ of `exp(2πi f)`. The first map is
  pinned on the image of the constant presheaf, which generates `ℤ_{X^an}` locally.

## References

* [H. Grauert, R. Remmert, *Coherent Analytic Sheaves*][grauertremmert1984], Ch. V.
-/

open CategoryTheory Opposite TopologicalSpace Filter Topology AlgebraicGeometry

namespace MMP.Analytic

open Analytification
open scoped ZeroObject

section Stalk

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}

/-- `z ↦ exp(2πi z)`. -/
private noncomputable def expTwoPiI (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

private lemma differentiable_expTwoPiI : Differentiable ℂ expTwoPiI :=
  (differentiable_id.const_mul _).cexp

private lemma expTwoPiI_add (a b : ℂ) : expTwoPiI (a + b) = expTwoPiI a * expTwoPiI b := by
  simp [expTwoPiI, mul_add, Complex.exp_add]

private lemma expTwoPiI_intCast (k : ℤ) : expTwoPiI k = 1 :=
  Complex.exp_eq_one_iff.2 ⟨k, by ring⟩

/-- The difference quotient `(expTwoPiI z - 1) / z`, extended by its derivative at `0`. -/
private noncomputable def dslopeExpTwoPiI : ℂ → ℂ := dslope expTwoPiI 0

private lemma differentiable_dslopeExpTwoPiI : Differentiable ℂ dslopeExpTwoPiI := by
  intro z
  have := (Complex.differentiableOn_dslope (f := expTwoPiI) (s := Set.univ) (c := 0)
    Filter.univ_mem).2 differentiable_expTwoPiI.differentiableOn
  exact (this z (Set.mem_univ _)).differentiableAt Filter.univ_mem

private lemma expTwoPiI_sub_one (z : ℂ) : expTwoPiI z - 1 = z * dslopeExpTwoPiI z := by
  have := sub_smul_dslope expTwoPiI 0 z
  simp only [sub_zero, smul_eq_mul] at this
  rw [dslopeExpTwoPiI, this]
  simp [expTwoPiI]

private lemma dslopeExpTwoPiI_zero_ne_zero : dslopeExpTwoPiI 0 ≠ 0 := by
  rw [dslopeExpTwoPiI, dslope_same]
  have hE : expTwoPiI = fun z => Complex.exp (2 * Real.pi * Complex.I * id z) := rfl
  have := ((hasDerivAt_id (0 : ℂ)).const_mul (2 * Real.pi * Complex.I)).cexp
  rw [hE, this.deriv]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Composition of a holomorphic germ with an entire function. -/
private noncomputable def compGerm (F : ℂ → ℂ) (hF : Differentiable ℂ F) {p : Fin n → ℂ}
    (g : holGerms p) : holGerms p :=
  ⟨Germ.map F (g : Germ (𝓝 p) ℂ), by
    obtain ⟨f, hf, hd⟩ := g.2
    rw [← hf, Germ.map_coe]
    exact coe_mem_holGerms (hd.mono fun y hy => (hF _).comp y hy)⟩

private lemma coe_compGerm (F : ℂ → ℂ) (hF : Differentiable ℂ F) {p : Fin n → ℂ}
    (g : holGerms p) (f : (Fin n → ℂ) → ℂ) (hg : (g : Germ (𝓝 p) ℂ) = f) :
    (compGerm F hF g : Germ (𝓝 p) ℂ) = ((F ∘ f : (Fin n → ℂ) → ℂ) : Germ (𝓝 p) ℂ) := by
  change Germ.map F (g : Germ (𝓝 p) ℂ) = _
  rw [hg, Germ.map_coe]

private lemma exists_rep {p : Fin n → ℂ} (g : holGerms p) :
    ∃ f : (Fin n → ℂ) → ℂ, (g : Germ (𝓝 p) ℂ) = f ∧ ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f, hf, hd⟩ := g.2
  exact ⟨f, hf.symm, hd⟩

private lemma compGerm_expTwoPiI_sub {p : Fin n → ℂ} (g₁ g₂ : holGerms p) :
    compGerm expTwoPiI differentiable_expTwoPiI g₁ -
        compGerm expTwoPiI differentiable_expTwoPiI g₂ =
      compGerm expTwoPiI differentiable_expTwoPiI g₂ *
        ((g₁ - g₂) * compGerm dslopeExpTwoPiI differentiable_dslopeExpTwoPiI (g₁ - g₂)) := by
  obtain ⟨f₁, h₁, -⟩ := exists_rep g₁
  obtain ⟨f₂, h₂, -⟩ := exists_rep g₂
  apply Subtype.ext
  change Germ.map expTwoPiI (g₁ : Germ (𝓝 p) ℂ) - Germ.map expTwoPiI (g₂ : Germ (𝓝 p) ℂ) =
    Germ.map expTwoPiI (g₂ : Germ (𝓝 p) ℂ) * (((g₁ : Germ (𝓝 p) ℂ) - (g₂ : Germ (𝓝 p) ℂ)) *
      Germ.map dslopeExpTwoPiI ((g₁ : Germ (𝓝 p) ℂ) - (g₂ : Germ (𝓝 p) ℂ)))
  rw [h₁, h₂, ← Germ.coe_sub, Germ.map_coe, Germ.map_coe, Germ.map_coe, ← Germ.coe_sub,
    ← Germ.coe_mul, ← Germ.coe_mul]
  congr 1
  funext z
  simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
  rw [← expTwoPiI_sub_one, mul_sub, mul_one, ← expTwoPiI_add, add_sub_cancel]

private lemma compGerm_expTwoPiI_sub_one {p : Fin n → ℂ} (g : holGerms p) :
    compGerm expTwoPiI differentiable_expTwoPiI g - 1 =
      g * compGerm dslopeExpTwoPiI differentiable_dslopeExpTwoPiI g := by
  have := compGerm_expTwoPiI_sub g 0
  have h0 : compGerm expTwoPiI differentiable_expTwoPiI (0 : holGerms p) = 1 := by
    apply Subtype.ext
    rw [coe_compGerm _ _ _ 0 (by simp)]
    simp [expTwoPiI]
  rwa [h0, one_mul, sub_zero] at this

private lemma compGerm_expTwoPiI_add {p : Fin n → ℂ} (g₁ g₂ : holGerms p) :
    compGerm expTwoPiI differentiable_expTwoPiI (g₁ + g₂) =
      compGerm expTwoPiI differentiable_expTwoPiI g₁ *
        compGerm expTwoPiI differentiable_expTwoPiI g₂ := by
  obtain ⟨f₁, h₁, -⟩ := exists_rep g₁
  obtain ⟨f₂, h₂, -⟩ := exists_rep g₂
  apply Subtype.ext
  change Germ.map expTwoPiI ((g₁ : Germ (𝓝 p) ℂ) + (g₂ : Germ (𝓝 p) ℂ)) =
    Germ.map expTwoPiI (g₁ : Germ (𝓝 p) ℂ) * Germ.map expTwoPiI (g₂ : Germ (𝓝 p) ℂ)
  rw [h₁, h₂, ← Germ.coe_add, Germ.map_coe, Germ.map_coe, Germ.map_coe, ← Germ.coe_mul]
  congr 1
  funext z
  simp [expTwoPiI_add]

private lemma isUnit_of_value_ne_zero {p : Fin n → ℂ} (g : holGerms p)
    (hg : Germ.value (g : Germ (𝓝 p) ℂ) ≠ 0) : IsUnit g := by
  obtain ⟨f, hf, hd⟩ := exists_rep g
  rw [hf] at hg
  change f p ≠ 0 at hg
  have hne : ∀ᶠ y in 𝓝 p, f y ≠ 0 := hd.self_of_nhds.continuousAt.eventually_ne hg
  refine IsUnit.of_mul_eq_one (b := ⟨((f⁻¹ : (Fin n → ℂ) → ℂ) : Germ (𝓝 p) ℂ),
    coe_mem_holGerms ((hd.and hne).mono fun y hy => hy.1.inv hy.2)⟩) (Subtype.ext ?_)
  change (g : Germ (𝓝 p) ℂ) * ((f⁻¹ : (Fin n → ℂ) → ℂ) : Germ (𝓝 p) ℂ) = 1
  rw [hf, ← Germ.coe_mul]
  exact Germ.coe_eq.2 (hne.mono fun y hy => by simp [hy])

/-- The exponential `u ↦ exp(2πi u)` on the local ring of a chart. -/
private noncomputable def stalkExp (c : Chart sX) (p : Fin c.n → ℂ) :
    c.StalkRing p → c.StalkRing p := fun a =>
  Chart.StalkRing.mk c p (compGerm expTwoPiI differentiable_expTwoPiI
    (Classical.choose (Ideal.Quotient.mk_surjective (I := c.ideal.map (polyGermHom p)) a)))

private lemma stalkExp_mk (c : Chart sX) (p : Fin c.n → ℂ) (g : holGerms p) :
    stalkExp c p (Chart.StalkRing.mk c p g) =
      Chart.StalkRing.mk c p (compGerm expTwoPiI differentiable_expTwoPiI g) := by
  set g' := Classical.choose (Ideal.Quotient.mk_surjective
    (I := c.ideal.map (polyGermHom p)) (Chart.StalkRing.mk c p g))
  have hg' : (Ideal.Quotient.mk (c.ideal.map (polyGermHom p)) g' :
      holGerms p ⧸ c.ideal.map (polyGermHom p)) = Ideal.Quotient.mk _ g :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective
      (I := c.ideal.map (polyGermHom p)) (Chart.StalkRing.mk c p g))
  change Ideal.Quotient.mk _ (compGerm expTwoPiI differentiable_expTwoPiI g') =
    Ideal.Quotient.mk _ (compGerm expTwoPiI differentiable_expTwoPiI g)
  rw [Ideal.Quotient.eq] at hg' ⊢
  rw [compGerm_expTwoPiI_sub]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hg')

private lemma mk_surjective (c : Chart sX) (p : Fin c.n → ℂ) (a : c.StalkRing p) :
    ∃ g, Chart.StalkRing.mk c p g = a :=
  Ideal.Quotient.mk_surjective a

private lemma stalkExp_add (c : Chart sX) (p : Fin c.n → ℂ) (a b : c.StalkRing p) :
    stalkExp c p (a + b) = stalkExp c p a * stalkExp c p b := by
  obtain ⟨g, rfl⟩ := mk_surjective c p a
  obtain ⟨h, rfl⟩ := mk_surjective c p b
  rw [← map_add, stalkExp_mk, stalkExp_mk, stalkExp_mk, compGerm_expTwoPiI_add, map_mul]

private lemma stalkExp_zero (c : Chart sX) (p : Fin c.n → ℂ) : stalkExp c p 0 = 1 := by
  rw [← map_zero (Chart.StalkRing.mk c p), stalkExp_mk]
  have := compGerm_expTwoPiI_sub_one (0 : holGerms p)
  rw [zero_mul, sub_eq_zero] at this
  rw [this, map_one]

private lemma stalkExp_intCast (c : Chart sX) (p : Fin c.n → ℂ) (k : ℤ) :
    stalkExp c p k = 1 := by
  rw [← map_intCast (Chart.StalkRing.mk c p), stalkExp_mk]
  have : compGerm expTwoPiI differentiable_expTwoPiI (k : holGerms p) = 1 := by
    apply Subtype.ext
    rw [coe_compGerm _ _ _ (fun _ => (k : ℂ)) (by simp)]
    change ((fun _ => expTwoPiI k : (Fin c.n → ℂ) → ℂ) : Germ (𝓝 p) ℂ) = 1
    rw [expTwoPiI_intCast]
    rfl
  rw [this, map_one]

private lemma stalkExp_mul_neg (c : Chart sX) (p : Fin c.n → ℂ) (a : c.StalkRing p) :
    stalkExp c p a * stalkExp c p (-a) = 1 := by
  rw [← stalkExp_add, add_neg_cancel, stalkExp_zero]

private lemma value_compGerm (F : ℂ → ℂ) (hF : Differentiable ℂ F) {p : Fin n → ℂ}
    (g : holGerms p) :
    Germ.value (compGerm F hF g : Germ (𝓝 p) ℂ) = F (Germ.value (g : Germ (𝓝 p) ℂ)) := by
  obtain ⟨f, hf, -⟩ := exists_rep g
  rw [coe_compGerm _ _ _ _ hf, hf]
  rfl

/-- The residue `𝒪_{U,y} → ℂ` at a `ℂ`-point `y` of a chart: the value at `z(y)`. -/
private noncomputable def residue (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U) :
    c.StalkRing (c.coords y) →+* ℂ :=
  Ideal.Quotient.lift (c.ideal.map (polyGermHom (c.coords y)))
    ((Germ.valueRingHom).comp (holGerms (c.coords y)).subtype) (by
      have : c.ideal.map (polyGermHom (c.coords y)) ≤
          RingHom.ker ((Germ.valueRingHom).comp (holGerms (c.coords y)).subtype) := by
        rw [Ideal.map_le_iff_le_comap]
        intro q hq
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change MvPolynomial.eval (c.coords y) q = 0
        rw [← c.evalHom_pres, (RingHom.mem_ker).1 hq, map_zero]
      exact fun g hg => this hg)

private lemma residue_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (g : holGerms (c.coords y)) :
    residue c y (Chart.StalkRing.mk c _ g) = Germ.value (g : Germ (𝓝 (c.coords y)) ℂ) :=
  Ideal.Quotient.lift_mk _ _ _

private lemma residue_of_eq_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    {a : c.StalkRing (c.coords y)} {g : holGerms (c.coords y)} {f : (Fin c.n → ℂ) → ℂ}
    (ha : a = Chart.StalkRing.mk c _ g) (hg : (g : Germ (𝓝 (c.coords y)) ℂ) = f) :
    residue c y a = f (c.coords y) := by
  rw [ha, residue_mk, hg]
  rfl

private lemma residue_stalkExp (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (a : c.StalkRing (c.coords y)) : residue c y (stalkExp c _ a) = expTwoPiI (residue c y a) := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  rw [stalkExp_mk, residue_mk, residue_mk, value_compGerm]

/-- The kernel of the exponential on a chart's local ring consists of the integer constants. -/
private lemma eq_intCast_of_stalkExp_eq_one (c : Chart sX)
    (y : ComplexPoints.chart (sX := sX) c.U) (a : c.StalkRing (c.coords y))
    (ha : stalkExp c _ a = 1) : ∃ k : ℤ, a = k := by
  have hr : expTwoPiI (residue c y a) = 1 := by rw [← residue_stalkExp, ha, map_one]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hr
  have hrk : residue c y a = k := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [hk]
    ring
  refine ⟨k, ?_⟩
  set K : c.StalkRing (c.coords y) := (k : c.StalkRing (c.coords y)) with hK
  have h1 : stalkExp c _ (a - K) = 1 := by
    have := stalkExp_add c _ (a - K) K
    rwa [sub_add_cancel, ha, stalkExp_intCast, mul_one, eq_comm] at this
  obtain ⟨h, hh⟩ := mk_surjective c _ (a - K)
  have hv : Germ.value (h : Germ (𝓝 (c.coords y)) ℂ) = 0 := by
    rw [← residue_mk, hh, map_sub, hrk, hK, map_intCast, sub_self]
  rw [← hh, stalkExp_mk] at h1
  have hmem :
      compGerm expTwoPiI differentiable_expTwoPiI h - 1 ∈
        c.ideal.map (polyGermHom (c.coords y)) := by
    have : Chart.StalkRing.mk c _ (compGerm expTwoPiI differentiable_expTwoPiI h - 1) = 0 := by
      rw [map_sub, h1, map_one, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  rw [compGerm_expTwoPiI_sub_one] at hmem
  have hu : IsUnit (compGerm dslopeExpTwoPiI differentiable_dslopeExpTwoPiI h) :=
    isUnit_of_value_ne_zero _ (by rw [value_compGerm, hv]; exact dslopeExpTwoPiI_zero_ne_zero)
  rw [Ideal.mul_unit_mem_iff_mem _ hu] at hmem
  rw [← sub_eq_zero, ← hh]
  exact Chart.StalkRing.mk_eq_zero_of_mem c hmem

private lemma eventually_differentiableAt_of_coe_eq {p : Fin n → ℂ} (g : holGerms p)
    {f : (Fin n → ℂ) → ℂ} (hf : (g : Germ (𝓝 p) ℂ) = f) :
    ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f', hf', hd⟩ := exists_rep g
  have heq : f' =ᶠ[𝓝 p] f := Germ.coe_eq.1 (hf'.symm.trans hf)
  exact (hd.and heq.eventuallyEq_nhds).mono fun y hy => hy.1.congr_of_eventuallyEq hy.2.symm

/-- The logarithm `(log c₀ + log (f / c₀)) / 2πi` of the class of a holomorphic germ `f` whose
value lies in `c₀ · (ℂ ∖ (-∞, 0])`. -/
private lemma exists_stalkLog_of_coe_eq (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (g : holGerms (c.coords y)) {f : (Fin c.n → ℂ) → ℂ}
    (hf : (g : Germ (𝓝 (c.coords y)) ℂ) = f) {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    (ha : f (c.coords y) / c₀ ∈ Complex.slitPlane) :
    ∃ ℓ : holGerms (c.coords y), (ℓ : Germ (𝓝 (c.coords y)) ℂ) =
        ((fun z => (Complex.log c₀ + Complex.log (f z / c₀)) / (2 * Real.pi * Complex.I) :
          (Fin c.n → ℂ) → ℂ) : Germ (𝓝 (c.coords y)) ℂ) ∧
      stalkExp c _ (Chart.StalkRing.mk c _ ℓ) = Chart.StalkRing.mk c _ g ∧
      residue c y (Chart.StalkRing.mk c _ ℓ) =
        (Complex.log c₀ + Complex.log (f (c.coords y) / c₀)) / (2 * Real.pi * Complex.I) := by
  have hd := eventually_differentiableAt_of_coe_eq g hf
  set L : (Fin c.n → ℂ) → ℂ :=
    fun z => (Complex.log c₀ + Complex.log (f z / c₀)) / (2 * Real.pi * Complex.I)
  have hslit : ∀ᶠ z in 𝓝 (c.coords y), f z / c₀ ∈ Complex.slitPlane :=
    (hd.self_of_nhds.continuousAt.div_const c₀).eventually_mem
      (Complex.isOpen_slitPlane.mem_nhds ha)
  have hL : ∀ᶠ z in 𝓝 (c.coords y), DifferentiableAt ℂ L z := (hd.and hslit).mono fun z hz => by
    have h₁ : DifferentiableAt ℂ (fun t => f t / c₀) z := by
      simp_rw [div_eq_mul_inv]; exact hz.1.mul_const _
    have h₂ : DifferentiableAt ℂ (fun t => Complex.log (f t / c₀)) z := h₁.clog hz.2
    have h₃ := (differentiableAt_const (Complex.log c₀)).add h₂
    simp_rw [L, div_eq_mul_inv]
    exact h₃.mul_const _
  refine ⟨⟨(L : Germ (𝓝 (c.coords y)) ℂ), coe_mem_holGerms hL⟩, rfl, ?_, ?_⟩
  · rw [stalkExp_mk]
    congr 1
    apply Subtype.ext
    rw [coe_compGerm _ _ _ L rfl, hf]
    refine Germ.coe_eq.2 (hslit.mono fun z hz => ?_)
    simp only [Function.comp_apply, L, expTwoPiI]
    rw [mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_add, Complex.exp_log hc₀,
      Complex.exp_log (Complex.slitPlane_ne_zero hz), mul_div_cancel₀ _ hc₀]
  · rw [residue_mk]
    rfl

/-- A logarithm, with prescribed residue, of an element of a chart's local ring whose residue
lies in `c₀ · (ℂ ∖ (-∞, 0])`. -/
private lemma exists_stalkLog (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (a : c.StalkRing (c.coords y)) {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    (ha : residue c y a / c₀ ∈ Complex.slitPlane) :
    ∃ ℓ, stalkExp c _ ℓ = a ∧ residue c y ℓ =
      (Complex.log c₀ + Complex.log (residue c y a / c₀)) / (2 * Real.pi * Complex.I) := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  obtain ⟨f, hf, -⟩ := exists_rep g
  have hv := residue_of_eq_mk c y rfl hf
  rw [hv] at ha ⊢
  obtain ⟨ℓ, -, h₁, h₂⟩ := exists_stalkLog_of_coe_eq c y g hf hc₀ ha
  exact ⟨_, h₁, h₂⟩

/-- A logarithm in a chart's local ring is determined by its residue. -/
private lemma stalkLog_unique (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    {ℓ₁ ℓ₂ : c.StalkRing (c.coords y)} (he : stalkExp c _ ℓ₁ = stalkExp c _ ℓ₂)
    (hr : residue c y ℓ₁ = residue c y ℓ₂) : ℓ₁ = ℓ₂ := by
  have h1 : stalkExp c _ (ℓ₁ - ℓ₂) = 1 := by
    have := stalkExp_add c _ (ℓ₁ - ℓ₂) ℓ₂
    rw [sub_add_cancel, he] at this
    have h := congrArg (· * stalkExp c _ (-ℓ₂)) this
    simp only [mul_assoc, stalkExp_mul_neg, mul_one] at h
    exact h.symm
  obtain ⟨k, hk⟩ := eq_intCast_of_stalkExp_eq_one c y _ h1
  have : (k : ℂ) = 0 := by rw [← map_intCast (residue c y), ← hk, map_sub, hr, sub_self]
  rw [Int.cast_eq_zero.1 this, Int.cast_zero, sub_eq_zero] at hk
  exact hk

private lemma holPullback_compGerm {c d : Chart sX} (m : ChartHom c d)
    (y : ComplexPoints.chart (sX := sX) d.U) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (g : holGerms (c.coords (m.incl y))) :
    holPullback m.polyMap m.differentiable_polyMap (m.tendsto_polyMap y) (compGerm F hF g) =
      compGerm F hF (holPullback m.polyMap m.differentiable_polyMap (m.tendsto_polyMap y) g) := by
  obtain ⟨f, hf, -⟩ := exists_rep g
  apply Subtype.ext
  rw [coe_holPullback, coe_compGerm _ _ _ _ hf,
    coe_compGerm _ _ _ (f ∘ m.polyMap) (by rw [coe_holPullback, hf, Germ.coe_compTendsto]),
    Germ.coe_compTendsto]
  rfl

private lemma transition_stalkExp {c d : Chart sX} (m : ChartHom c d)
    (y : ComplexPoints.chart (sX := sX) d.U) (a : c.StalkRing (c.coords (m.incl y))) :
    m.transition y (stalkExp c _ a) = stalkExp d _ (m.transition y a) := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  rw [stalkExp_mk, m.transition_mk, m.transition_mk, stalkExp_mk, holPullback_compGerm]

private lemma residue_transition {c d : Chart sX} (m : ChartHom c d)
    (y : ComplexPoints.chart (sX := sX) d.U) (a : c.StalkRing (c.coords (m.incl y))) :
    residue d y (m.transition y a) = residue c (m.incl y) a := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  obtain ⟨f, hf, -⟩ := exists_rep g
  rw [m.transition_mk, residue_mk, residue_mk, coe_holPullback, hf, Germ.coe_compTendsto]
  change f (m.polyMap (d.coords y)) = f (c.coords (m.incl y))
  rw [m.coords_incl]

end Stalk

section Sections

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

private lemma isLocallyHolomorphic_stalkExp {W : Opens (space sX)} {s : ∀ x : W, Fibre x.1}
    (hs : IsLocallyHolomorphic s) :
    IsLocallyHolomorphic (fun x (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) =>
      stalkExp c.1 _ (s x c)) := by
  intro c x hx
  obtain ⟨O, hO, hxO, h, hh⟩ := hs c x hx
  refine ⟨O, hO, hxO, expTwoPiI ∘ h, fun y hy => ?_⟩
  obtain ⟨hyW, g, hg, hsg⟩ := hh y hy
  exact ⟨hyW, compGerm expTwoPiI differentiable_expTwoPiI g, coe_compGerm _ _ _ _ hg,
    (congrArg (stalkExp c _) hsg).trans (stalkExp_mk c _ g)⟩

private lemma isCompatible_stalkExp {W : Opens (space sX)} {s : ∀ x : W, Fibre x.1}
    (hs : IsCompatible s) :
    IsCompatible (fun x (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) =>
      stalkExp c.1 _ (s x c)) := fun c d m x hx =>
  (transition_stalkExp m ⟨x.1, hx⟩ _).trans (congrArg _ (hs c d m x hx))

/-- The exponential `s ↦ exp(2πi s)` on sections of `𝒪_{X^an}`. -/
private noncomputable def expSec {W : Opens (space sX)} (s : sections sX W) : sections sX W :=
  ⟨fun x c => stalkExp c.1 _ (s.1 x c),
    isLocallyHolomorphic_stalkExp s.2.1, isCompatible_stalkExp s.2.2⟩

private lemma expSec_add {W : Opens (space sX)} (s t : sections sX W) :
    expSec (s + t) = expSec s * expSec t :=
  Subtype.ext (funext fun _ => funext fun c => stalkExp_add c.1 _ _ _)

private lemma expSec_zero {W : Opens (space sX)} : expSec (0 : sections sX W) = 1 :=
  Subtype.ext (funext fun _ => funext fun c => stalkExp_zero c.1 _)

private lemma expSec_intCast {W : Opens (space sX)} (k : ℤ) :
    expSec (k : sections sX W) = 1 :=
  Subtype.ext (funext fun _ => funext fun c => by
    change stalkExp c.1 _ (((k : sections sX W) : ∀ x : W, Fibre x.1) _ c) = 1
    rw [Subring.coe_intCast, Pi.intCast_apply, Pi.intCast_apply]
    exact stalkExp_intCast c.1 _ k)

/-- `exp(2πi s)` as a unit. -/
private noncomputable def expUnit {W : Opens (space sX)} (s : sections sX W) :
    (sections sX W)ˣ where
  val := expSec s
  inv := expSec (-s)
  val_inv := by rw [← expSec_add, add_neg_cancel, expSec_zero]
  inv_val := by rw [← expSec_add, neg_add_cancel, expSec_zero]

/-- `s ↦ exp(2πi s)` as a homomorphism from the additive group of sections to their units. -/
private noncomputable def expHom (W : Opens (space sX)) :
    sections sX W →+ Additive (sections sX W)ˣ where
  toFun s := Additive.ofMul (expUnit s)
  map_zero' := by
    apply Additive.toMul.injective
    exact Units.ext expSec_zero
  map_add' s t := by
    apply Additive.toMul.injective
    exact Units.ext (expSec_add s t)

/-- For `X` locally of finite type over `ℂ`, the sections over an affine open are a finitely
generated `ℂ`-algebra. -/
private lemma exists_gens [LocallyOfFiniteType sX] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (gen : Fin n → Γ(X, U)),
      Function.Surjective (MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen) := by
  have h₁ : (sX.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType (f := sX) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (ComplexPoints.baseRingHom sX U).FiniteType := by
    have : ComplexPoints.baseRingHom sX U =
        (sX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom := rfl
    rw [this]
    exact h₁.comp (RingHom.FiniteType.of_surjective _ fun a =>
      ⟨(Scheme.ΓSpecIso (.of ℂ)).hom a, Iso.hom_inv_id_apply _ a⟩)
  letI := (ComplexPoints.baseRingHom sX U).toAlgebra
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h₂
  refine ⟨n, fun i => φ (MvPolynomial.X i), ?_⟩
  have : MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U)
      (fun i => φ (MvPolynomial.X i)) = φ.toRingHom :=
    MvPolynomial.ringHom_ext (fun a => by simp [RingHom.algebraMap_toAlgebra])
      (fun i => by simp)
  rwa [this]

/-- For `X` locally of finite type over `ℂ`, every `ℂ`-point lies in a chart: an affine open
containing it has finitely generated sections. -/
private lemma exists_chart [LocallyOfFiniteType sX] (x : space sX) :
    ∃ c : Chart sX, x ∈ ComplexPoints.chart c.U := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top (ComplexPoints.toScheme x))
  obtain ⟨n, gen, h⟩ := exists_gens (sX := sX) hU
  exact ⟨⟨U, hU, n, gen, h⟩, ComplexPoints.mem_chart_iff.2 hxU⟩

/-- Two charts at a point are refined by a third: its generators are those of both, restricted,
together with generators of a smaller affine open. -/
private lemma exists_chartHom_chartHom [LocallyOfFiniteType sX] (c d : Chart sX)
    {y : ComplexPoints sX} (hc : y ∈ ComplexPoints.chart c.U)
    (hd : y ∈ ComplexPoints.chart d.U) :
    ∃ (e : Chart sX) (_ : ChartHom c e) (_ : ChartHom d e), y ∈ ComplexPoints.chart e.U := by
  obtain ⟨U, hU, hyU, hUcd⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := c.U ⊓ d.U) (x := y.toScheme)
    ⟨ComplexPoints.mem_chart_iff.1 hc, ComplexPoints.mem_chart_iff.1 hd⟩
  obtain ⟨k, g, hg⟩ := exists_gens (sX := sX) hU
  let gen : Fin (c.n + d.n + k) → Γ(X, U) :=
    Fin.append (Fin.append
      (fun i => X.presheaf.map (homOfLE (hUcd.trans inf_le_left)).op (c.gen i))
      (fun j => X.presheaf.map (homOfLE (hUcd.trans inf_le_right)).op (d.gen j))) g
  have hsurj : Function.Surjective
      (MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen) := by
    intro a
    obtain ⟨q, rfl⟩ := hg a
    refine ⟨MvPolynomial.rename (Fin.natAdd (c.n + d.n)) q, ?_⟩
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
    congr 1
    funext i
    exact Fin.append_right _ _ i
  let e : Chart sX := ⟨U, hU, c.n + d.n + k, gen, hsurj⟩
  refine ⟨e, ⟨hUcd.trans inf_le_left,
    fun i => MvPolynomial.X (Fin.castAdd k (Fin.castAdd d.n i)), fun i => ?_⟩,
    ⟨hUcd.trans inf_le_right, fun j => MvPolynomial.X (Fin.castAdd k (Fin.natAdd c.n j)),
      fun j => ?_⟩, ComplexPoints.mem_chart_iff.2 hyU⟩
  · change _ = MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen (MvPolynomial.X _)
    rw [MvPolynomial.eval₂Hom_X']
    simp only [gen, Fin.append_left]
  · change _ = MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen (MvPolynomial.X _)
    rw [MvPolynomial.eval₂Hom_X']
    simp only [gen, Fin.append_left, Fin.append_right]

/-- For a compatible family, the residue at a point does not depend on the chart. -/
private lemma residue_eq_of_isCompatible [LocallyOfFiniteType sX] {W : Opens (space sX)}
    {s : ∀ x : W, Fibre x.1} (hs : IsCompatible s) (x : W) (c d : Chart sX)
    (hc : x.1 ∈ ComplexPoints.chart c.U) (hd : x.1 ∈ ComplexPoints.chart d.U) :
    residue c ⟨x.1, hc⟩ (s x ⟨c, hc⟩) = residue d ⟨x.1, hd⟩ (s x ⟨d, hd⟩) := by
  obtain ⟨e, m₁, m₂, he⟩ := exists_chartHom_chartHom c d hc hd
  exact ((residue_transition m₁ ⟨x.1, he⟩ _).symm.trans (congrArg _ (hs c e m₁ x he))).trans
    ((congrArg _ (hs d e m₂ x he)).symm.trans (residue_transition m₂ ⟨x.1, he⟩ _))

/-- The `ℂ`-points of an open `U` at which the value of a section `f ∈ Γ(X, U)` lies in an open
set form an open subset of `X(ℂ)`. -/
private lemma isOpen_setOf_evalHom_mem (U : X.Opens) (f : Γ(X, U)) {T : Set ℂ}
    (hT : IsOpen T) :
    IsOpen {y : ComplexPoints sX | ∃ hy : y ∈ ComplexPoints.chart U,
      ComplexPoints.evalHom U ⟨y, hy⟩ f ∈ T} := by
  rw [ComplexPoints.isOpen_iff]
  intro U'
  letI := ComplexPoints.chartTopology (sX := sX) (U' : X.Opens)
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨hyU, hyT⟩
  obtain ⟨g, hgU, hyg⟩ := U'.2.exists_basicOpen_le
    ⟨y.1.toScheme, ComplexPoints.mem_chart_iff.1 hyU⟩ (ComplexPoints.mem_chart_iff.1 y.2)
  have := U'.2.isLocalization_basicOpen g
  obtain ⟨⟨a, _, k, rfl⟩, hak⟩ := IsLocalization.mk'_surjective (Submonoid.powers g)
    (X.presheaf.map (homOfLE hgU).op f)
  have hval : ∀ z : ComplexPoints.chart (sX := sX) (U' : X.Opens),
      ComplexPoints.evalHom (U' : X.Opens) z g ≠ 0 →
        ∃ hzU : z.1 ∈ ComplexPoints.chart U, ComplexPoints.evalHom U ⟨z.1, hzU⟩ f =
          ComplexPoints.evalHom (U' : X.Opens) z a /
            ComplexPoints.evalHom (U' : X.Opens) z g ^ k := by
    intro z hz
    have hzD : z.1.toScheme ∈ X.basicOpen g := (ComplexPoints.toScheme_mem_basicOpen_iff z g).2 hz
    let zB : ComplexPoints.chart (sX := sX) (X.basicOpen g) :=
      ⟨z.1, ComplexPoints.mem_chart_iff.2 hzD⟩
    have hres : ∀ b : Γ(X, (U' : X.Opens)), ComplexPoints.evalHom (U' : X.Opens) z b =
        ComplexPoints.evalHom (X.basicOpen g) zB
          (algebraMap Γ(X, (U' : X.Opens)) Γ(X, X.basicOpen g) b) :=
      fun b => ComplexPoints.evalHom_res (X.basicOpen_le g) zB b
    refine ⟨ComplexPoints.mem_chart_iff.2 (hgU hzD), ?_⟩
    rw [ComplexPoints.evalHom_res hgU zB f, ← hak, eq_div_iff (pow_ne_zero _ hz), hres, hres,
      ← map_pow, ← map_mul, ← map_pow, IsLocalization.mk'_spec]
  refine ⟨{z | ComplexPoints.evalHom (U' : X.Opens) z g ≠ 0} ∩
      (fun z => ComplexPoints.evalHom (U' : X.Opens) z a /
        ComplexPoints.evalHom (U' : X.Opens) z g ^ k) ⁻¹' T, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hzT⟩
    obtain ⟨hzU, hzv⟩ := hval z hz
    exact ⟨hzU, by rwa [hzv]⟩
  · refine ContinuousOn.isOpen_inter_preimage ?_
      (isOpen_compl_singleton.preimage (ComplexPoints.continuous_eval _ g)) hT
    exact (ComplexPoints.continuous_eval _ a).continuousOn.div
      ((ComplexPoints.continuous_eval _ g).pow k).continuousOn fun z hz => pow_ne_zero _ hz
  · have hy : ComplexPoints.evalHom (U' : X.Opens) y g ≠ 0 :=
      (ComplexPoints.toScheme_mem_basicOpen_iff y g).1 hyg
    obtain ⟨_, hyv⟩ := hval y hy
    exact ⟨hy, by rwa [Set.mem_preimage, ← hyv]⟩

/-- A subset of the `ℂ`-points of an affine open, open for its chart topology, is open in
`X(ℂ)`. -/
private lemma isOpen_setOf_mem_chart (U : X.affineOpens)
    {O : Set (ComplexPoints.chart (sX := sX) (U : X.Opens))}
    (hO : IsOpen[ComplexPoints.chartTopology (U : X.Opens)] O) :
    IsOpen {y : ComplexPoints sX | ∃ hy : y ∈ ComplexPoints.chart (U : X.Opens), ⟨y, hy⟩ ∈ O} := by
  have hS : IsOpen (ComplexPoints.chart (sX := sX) (U : X.Opens)) := by
    have : ComplexPoints.chart (sX := sX) (U : X.Opens) =
        ComplexPoints.toScheme ⁻¹' ((U : X.Opens) : Set X) :=
      Set.ext fun _ => ComplexPoints.mem_chart_iff
    rw [this]
    exact (U : X.Opens).2.preimage ComplexPoints.continuous_toScheme
  have hid : @Continuous _ _ instTopologicalSpaceSubtype
      (ComplexPoints.chartTopology (U : X.Opens))
      (id : ComplexPoints.chart (sX := sX) (U : X.Opens) → _) := by
    refine continuous_iInf_rng.2 fun f => continuous_induced_rng.2 ?_
    refine continuous_def.2 fun T hT => ?_
    convert (isOpen_setOf_evalHom_mem (sX := sX) (U : X.Opens) f hT).preimage
      continuous_subtype_val using 1
    ext q
    exact ⟨fun h => ⟨q.2, h⟩, fun ⟨_, h⟩ => h⟩
  convert hS.isOpenMap_subtype_val _
    (@IsOpen.preimage _ _ instTopologicalSpaceSubtype (ComplexPoints.chartTopology _) _ hid _ hO)
    using 1
  ext y
  exact ⟨fun ⟨hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨q, hq, e⟩ => e ▸ ⟨q.2, hq⟩⟩

/-- A neighbourhood, in the chart topology, of a point of a chart, on which the coordinates lie
in a prescribed neighbourhood, contains an open of `X(ℂ)` around the point. -/
private lemma exists_opens_of_mem_chart (c : Chart sX)
    {O : Set (ComplexPoints.chart (sX := sX) c.U)}
    (hO : IsOpen[ComplexPoints.chartTopology c.U] O) (y : ComplexPoints.chart (sX := sX) c.U)
    (hy : y ∈ O) {N : Set (Fin c.n → ℂ)} (hN : N ∈ 𝓝 (c.coords y)) :
    ∃ V : Opens (space sX), y.1 ∈ V ∧ ∀ z ∈ V, ∃ hz : z ∈ ComplexPoints.chart c.U,
      ⟨z, hz⟩ ∈ O ∧ c.coords ⟨z, hz⟩ ∈ N := by
  letI := ComplexPoints.chartTopology (sX := sX) c.U
  obtain ⟨B, hBN, hB, hyB⟩ := mem_nhds_iff.1 hN
  have hcont : Continuous c.coords :=
    continuous_pi fun i => ComplexPoints.continuous_eval c.U (c.gen i)
  have hO' : IsOpen (O ∩ c.coords ⁻¹' B) := hO.inter (hB.preimage hcont)
  refine ⟨⟨_, isOpen_setOf_mem_chart ⟨c.U, c.isAffineOpen⟩ hO'⟩, ⟨y.2, hy, hyB⟩, ?_⟩
  rintro z ⟨hz, hzO, hzB⟩
  exact ⟨hz, hzO, hBN hzB⟩

/-- The residue of a section of `𝒪_{X^an}` is continuous: near a point `x`, its residues in
every chart lie in any prescribed neighbourhood of its residue at `x`. -/
private lemma exists_opens_residue_mem [LocallyOfFiniteType sX] {W : Opens (space sX)}
    (s : sections sX W) (x : W) (c : Chart sX) (hc : x.1 ∈ ComplexPoints.chart c.U) {N : Set ℂ}
    (hN : N ∈ 𝓝 (residue c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩))) :
    ∃ V : Opens (space sX), x.1 ∈ V ∧ ∀ y : W, y.1 ∈ V → ∀ (d : Chart sX)
      (hd : y.1 ∈ ComplexPoints.chart d.U), residue d ⟨y.1, hd⟩ (s.1 y ⟨d, hd⟩) ∈ N := by
  obtain ⟨O, hO, hxO, h, hh⟩ := s.2.1 c x hc
  have hres : ∀ y ∈ O, ∀ hyW : y.1 ∈ W,
      residue c y (s.1 ⟨y.1, hyW⟩ ⟨c, y.2⟩) = h (c.coords y) := fun y hy _ => by
    obtain ⟨_, g, hg, hsg⟩ := hh y hy
    exact residue_of_eq_mk c y hsg hg
  obtain ⟨_, g₀, hg₀, -⟩ := hh _ hxO
  rw [hres _ hxO x.2] at hN
  obtain ⟨V, hxV, hV⟩ := exists_opens_of_mem_chart c hO _ hxO
    ((eventually_differentiableAt_of_coe_eq g₀ hg₀).self_of_nhds.continuousAt.preimage_mem_nhds hN)
  refine ⟨V, hxV, fun y hyV d hd => ?_⟩
  obtain ⟨hyc, hyO, hyN⟩ := hV y.1 hyV
  rwa [residue_eq_of_isCompatible s.2.2 y d c hd hyc, hres _ hyO]

/-- An integer constant vanishing as a section over a nonempty open is zero. -/
private lemma intCast_eq_zero [LocallyOfFiniteType sX] {W : Opens (space sX)} (x : W) (k : ℤ)
    (hk : (k : sections sX W) = 0) : k = 0 := by
  obtain ⟨c, hc⟩ := exists_chart x.1
  have h := congrArg (fun s : sections sX W => residue c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩)) hk
  change residue c ⟨x.1, hc⟩ (k : c.StalkRing _) = residue c ⟨x.1, hc⟩ 0 at h
  rw [map_intCast, map_zero] at h
  exact_mod_cast h

/-- The kernel of the exponential consists, locally, of integer constants. -/
private lemma exists_eq_intCast_of_expSec_eq_one [LocallyOfFiniteType sX] {W : Opens (space sX)}
    (s : sections sX W) (hs : expSec s = 1) (x : W) :
    ∃ (V : Opens (space sX)) (_ : x.1 ∈ V) (h : V ≤ W) (k : ℤ), restrictHom h s = k := by
  have key : ∀ (y : W) (d : Chart sX) (hd : y.1 ∈ ComplexPoints.chart d.U),
      ∃ k : ℤ, s.1 y ⟨d, hd⟩ = k ∧ residue d ⟨y.1, hd⟩ (s.1 y ⟨d, hd⟩) = k := by
    intro y d hd
    have h1 : stalkExp d _ (s.1 y ⟨d, hd⟩) = 1 :=
      congrArg (fun t : sections sX W => t.1 y ⟨d, hd⟩) hs
    obtain ⟨k, hk⟩ := eq_intCast_of_stalkExp_eq_one d ⟨y.1, hd⟩ _ h1
    exact ⟨k, hk, by rw [hk, map_intCast]⟩
  obtain ⟨c, hc⟩ := exists_chart x.1
  obtain ⟨k₀, -, hk₀⟩ := key x c hc
  obtain ⟨V, hxV, hV⟩ := exists_opens_residue_mem s x c hc
    (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨V ⊓ W, ⟨hxV, x.2⟩, inf_le_right, k₀, Subtype.ext (funext fun y => funext fun d => ?_)⟩
  change s.1 ⟨y.1, y.2.2⟩ d = ((k₀ : sections sX (V ⊓ W)) : ∀ x : (V ⊓ W : Opens _), Fibre x.1) y d
  rw [Subring.coe_intCast, Pi.intCast_apply, Pi.intCast_apply]
  obtain ⟨k, hk, hkr⟩ := key ⟨y.1, y.2.2⟩ d.1 d.2
  refine hk.trans (congrArg _ ?_)
  have hlt : ‖((k - k₀ : ℤ) : ℂ)‖ < 1 := by
    have := hV ⟨y.1, y.2.2⟩ y.2.1 d.1 d.2
    rw [hkr, hk₀, Metric.mem_ball, dist_eq_norm] at this
    push_cast
    linarith
  rw [Complex.norm_intCast, ← Int.cast_abs] at hlt
  have : |k - k₀| < 1 := by exact_mod_cast hlt
  rw [abs_lt] at this
  omega

/-- Every unit section of `𝒪_{X^an}` has, locally, a logarithm. -/
private lemma exists_expSec_eq [LocallyOfFiniteType sX] {W : Opens (space sX)}
    (u : (sections sX W)ˣ) (x : W) :
    ∃ (V : Opens (space sX)) (_ : x.1 ∈ V) (h : V ≤ W) (ℓ : sections sX V),
      expSec ℓ = restrictHom h u := by
  set s : sections sX W := (u : sections sX W)
  have hunit : ∀ (y : W) (d : Chart sX) (hd : y.1 ∈ ComplexPoints.chart d.U),
      residue d ⟨y.1, hd⟩ (s.1 y ⟨d, hd⟩) ≠ 0 := by
    intro y d hd h0
    have : residue d ⟨y.1, hd⟩ (s.1 y ⟨d, hd⟩ * (u.inv : sections sX W).1 y ⟨d, hd⟩) = 1 :=
      (congrArg (fun t : sections sX W => residue d ⟨y.1, hd⟩ (t.1 y ⟨d, hd⟩)) u.val_inv).trans
        (map_one _)
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  obtain ⟨c, hc⟩ := exists_chart x.1
  set a₀ := residue c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩)
  have ha₀ : a₀ ≠ 0 := hunit x c hc
  obtain ⟨V, hxV, hV⟩ := exists_opens_residue_mem s x c hc
    ((continuous_id.div_const a₀).continuousAt.preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds ((div_self ha₀).symm ▸ Complex.one_mem_slitPlane)))
  have hslit : ∀ (y : (V ⊓ W : Opens (space sX))) (d : Chart sX)
      (hd : y.1 ∈ ComplexPoints.chart d.U),
      residue d ⟨y.1, hd⟩ (s.1 ⟨y.1, y.2.2⟩ ⟨d, hd⟩) / a₀ ∈ Complex.slitPlane :=
    fun y d hd => hV ⟨y.1, y.2.2⟩ y.2.1 d hd
  let R : ℂ → ℂ := fun z =>
    (Complex.log a₀ + Complex.log (z / a₀)) / (2 * Real.pi * Complex.I)
  let ℓf : ∀ y : (V ⊓ W : Opens (space sX)), Fibre y.1 := fun y d =>
    Classical.epsilon fun ℓ => stalkExp d.1 _ ℓ = s.1 ⟨y.1, y.2.2⟩ d ∧
      residue d.1 ⟨y.1, d.2⟩ ℓ = R (residue d.1 ⟨y.1, d.2⟩ (s.1 ⟨y.1, y.2.2⟩ d))
  have hℓ : ∀ y d, stalkExp d.1 _ (ℓf y d) = s.1 ⟨y.1, y.2.2⟩ d ∧
      residue d.1 ⟨y.1, d.2⟩ (ℓf y d) = R (residue d.1 ⟨y.1, d.2⟩ (s.1 ⟨y.1, y.2.2⟩ d)) :=
    fun y d => Classical.epsilon_spec (exists_stalkLog d.1 ⟨y.1, d.2⟩ _ ha₀ (hslit y d.1 d.2))
  have hcompat : IsCompatible ℓf := by
    intro d e m y hy
    refine stalkLog_unique e ⟨y.1, hy⟩ ?_ ?_
    · exact ((transition_stalkExp m ⟨y.1, hy⟩ _).symm.trans
        ((congrArg _ (hℓ y ⟨d, _⟩).1).trans (s.2.2 d e m ⟨y.1, y.2.2⟩ hy))).trans
        (hℓ y ⟨e, hy⟩).1.symm
    · refine ((residue_transition m ⟨y.1, hy⟩ _).trans ((hℓ y ⟨d, _⟩).2.trans ?_)).trans
        (hℓ y ⟨e, hy⟩).2.symm
      exact congrArg R ((residue_transition m ⟨y.1, hy⟩ _).symm.trans
        (congrArg _ (s.2.2 d e m ⟨y.1, y.2.2⟩ hy)))
  have hloc : IsLocallyHolomorphic ℓf := by
    intro d y hy
    obtain ⟨O₁, hO₁, hyO₁, h₁, hh₁⟩ := s.2.1 d ⟨y.1, y.2.2⟩ hy
    refine ⟨O₁ ∩ {z | z.1 ∈ V ⊓ W}, (ComplexPoints.chartTopology d.U).isOpen_inter _ _ hO₁
      (isOpen_chart_inter ⟨d.U, d.isAffineOpen⟩ (V ⊓ W)), ⟨hyO₁, y.2⟩, fun p => R (h₁ p),
      fun z hz => ?_⟩
    obtain ⟨hzW, g, hg, hsg⟩ := hh₁ z hz.1
    have hr : residue d z (s.1 ⟨z.1, hzW⟩ ⟨d, z.2⟩) = h₁ (d.coords z) :=
      residue_of_eq_mk d z hsg hg
    have hsl : h₁ (d.coords z) / a₀ ∈ Complex.slitPlane := hr ▸ hslit ⟨z.1, hz.2⟩ d z.2
    obtain ⟨ℓg, hℓg, hexp, hlres⟩ := exists_stalkLog_of_coe_eq d z g hg ha₀ hsl
    refine ⟨hz.2, ℓg, hℓg, stalkLog_unique d z ?_ ?_⟩
    · exact (hℓ ⟨z.1, hz.2⟩ ⟨d, z.2⟩).1.trans (hsg.trans hexp.symm)
    · exact (hℓ ⟨z.1, hz.2⟩ ⟨d, z.2⟩).2.trans ((congrArg R hr).trans hlres.symm)
  exact ⟨V ⊓ W, ⟨hxV, x.2⟩, inf_le_right, ⟨ℓf, hloc, hcompat⟩,
    Subtype.ext (funext fun y => funext fun d => (hℓ y d).1)⟩

end Sections

section Maps

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- The inclusion of the constant presheaf `ℤ` into `𝒪_{X^an}`. -/
private noncomputable def intToO :
    (Functor.const _).obj (AddCommGrpCat.of ℤ) ⟶
      ((sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
        (ringCatSheaf sX)).obj where
  app W := AddCommGrpCat.ofHom (Int.castAddHom (sections sX W.unop))
  naturality W W' i := by
    ext n
    exact (map_intCast (restrictHom i.unop.le) n).symm

/-- The map `ℤ_{X^an} ⟶ 𝒪_{X^an}`. -/
private noncomputable def ιMap :
    (constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ) ⟶
      (sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
        (ringCatSheaf sX) :=
  ⟨sheafifyLift _ (intToO sX)
    ((sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
      (ringCatSheaf sX)).property⟩

/-- The map `𝒪_{X^an} ⟶ 𝒪_{X^an}^×`, `s ↦ exp(2πi s)`. -/
private noncomputable def eMap :
    (sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
        (ringCatSheaf sX) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification sX) :=
  ⟨{ app := fun W => AddCommGrpCat.ofHom (expHom W.unop)
     naturality := fun W W' i => by
       ext s
       apply Additive.toMul.injective
       exact Units.ext rfl }⟩

end Maps

/-- Sections of the constant sheaf are locally constant. -/
private lemma exists_toSheafify_eq {T : TopCat.{0}} {U : Opens T}
    (σ : ToType (((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).obj.obj (op U))) {x : T} (hx : x ∈ U) :
    ∃ (V : Opens T) (i : V ⟶ U) (_ : x ∈ V) (n : ℤ),
      (toSheafify _ ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op V) n =
        ((constantSheaf _ AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj.map i.op σ := by
  obtain ⟨V, i, ⟨n, hn⟩, hxV⟩ := (Opens.mem_grothendieckTopology _).1
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology T)
      (toSheafify _ ((Functor.const _).obj (AddCommGrpCat.of ℤ))) σ) x hx
  exact ⟨V, i, hxV, n, hn⟩

/-- `ℤ_{X^an} ⟶ 𝒪_{X^an}` sends the constant `n` to the integer constant `n`. -/
private lemma ιMap_toSheafify {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (W : Opens (space sX))
    (n : ℤ) :
    (ιMap sX).hom.app (op W) ((toSheafify (Opens.grothendieckTopology (space sX))
      ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n) = (n : sections sX W) :=
  congrArg (fun φ => φ.app (op W) n) (toSheafify_sheafifyLift _ (intToO sX)
    ((sheafCompose _ (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)).property)

/-- `ℤ_{X^an} ⟶ 𝒪_{X^an}` is a monomorphism: checked on stalks, a germ of the constant sheaf is
locally the constant `n`, whose image vanishes near `x` only if `n = 0` (`intCast_eq_zero`). -/
private lemma mono_ιMap {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] :
    Mono (ιMap sX) := by
  set ZA := (constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)
  set O := (sheafCompose (Opens.grothendieckTopology (space sX))
    (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
  refine (ShortComplex.exact_iff_mono (ShortComplex.mk (0 : 0 ⟶ ZA) (ιMap sX)
    (Limits.zero_comp)) rfl).1 ?_
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro t ht
  refine ⟨0, (map_zero _).trans ?_⟩
  obtain ⟨U, hxU, σ, rfl⟩ := TopCat.Presheaf.germ_exist _ t
  obtain ⟨V, i, hxV, n, hn⟩ := exists_toSheafify_eq σ hxU
  have hσ : TopCat.Presheaf.germ ZA.obj U x hxU σ = TopCat.Presheaf.germ ZA.obj V x hxV
      ((toSheafify (Opens.grothendieckTopology (space sX))
        ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op V) n) :=
    (TopCat.Presheaf.germ_res_apply ZA.obj i x hxV σ).symm.trans
      (congrArg (TopCat.Presheaf.germ ZA.obj V x hxV) hn.symm)
  have ht2 : TopCat.Presheaf.germ O.obj V x hxV (n : sections sX V) =
      TopCat.Presheaf.germ O.obj V x hxV 0 :=
    (congrArg (TopCat.Presheaf.germ O.obj V x hxV) (ιMap_toSheafify sX V n)).symm.trans
      ((TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV (ιMap sX).hom _).symm.trans
        ((congrArg _ hσ.symm).trans (ht.trans (map_zero _).symm)))
  obtain ⟨V', hxV', iV, iV', hV'⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV _ _ ht2
  have hn0 : n = 0 := intCast_eq_zero (W := V') ⟨x, hxV'⟩ n
    (((map_intCast (restrictHom iV.le) n).symm.trans hV').trans (map_zero _))
  have h0 : (toSheafify (Opens.grothendieckTopology (space sX))
      ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op V) n = 0 := by
    rw [hn0]
    exact map_zero _
  exact (hσ.trans ((congrArg (TopCat.Presheaf.germ ZA.obj V x hxV) h0).trans
    (map_zero _))).symm

/-- The composite `ℤ_{X^an} ⟶ 𝒪_{X^an} ⟶ 𝒪_{X^an}^×` vanishes, as `exp(2πi n) = 1`. -/
private lemma ιMap_comp_eMap {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) : ιMap sX ≫ eMap sX = 0 := by
  apply Sheaf.hom_ext
  change sheafifyLift _ (intToO sX) _ ≫ (eMap sX).hom = 0
  apply sheafify_hom_ext _ _ _
    (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)).property
  rw [← Category.assoc, toSheafify_sheafifyLift, Limits.comp_zero]
  ext W n
  apply Additive.toMul.injective
  exact Units.ext (expSec_intCast n)

/-- Exactness of `ℤ_{X^an} ⟶ 𝒪_{X^an} ⟶ 𝒪_{X^an}^×` in the middle: a germ with `exp(2πi f) = 1`
is locally an integer constant. -/
private lemma exact_ιMap_eMap {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] :
    (ShortComplex.mk (ιMap sX) (eMap sX) (ιMap_comp_eMap sX)).Exact := by
  set ZA := (constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)
  set O := (sheafCompose (Opens.grothendieckTopology (space sX))
    (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
  set Ou := Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro t ht
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist _ t
  have ht2 : TopCat.Presheaf.germ Ou.obj U x hxU ((eMap sX).hom.app (op U) s) =
      TopCat.Presheaf.germ Ou.obj U x hxU 0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU (eMap sX).hom s).symm.trans
      (ht.trans (map_zero _).symm)
  obtain ⟨V, hxV, iU, iU', hV⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ ht2
  have hexp : expSec (restrictHom iU.le s) = 1 :=
    congrArg (fun u => ((Additive.toMul u : (sections sX V)ˣ) : sections sX V))
      (hV.trans (map_zero _))
  obtain ⟨V', hxV', hV'V, k, hk⟩ := exists_eq_intCast_of_expSec_eq_one _ hexp ⟨x, hxV⟩
  refine ⟨TopCat.Presheaf.germ ZA.obj V' x hxV'
    ((toSheafify (Opens.grothendieckTopology (space sX))
      ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op V') k), ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply V' x hxV' (ιMap sX).hom _).trans ?_
  refine (congrArg (TopCat.Presheaf.germ O.obj V' x hxV') (ιMap_toSheafify sX V' k)).trans ?_
  refine Eq.trans ?_
    (TopCat.Presheaf.germ_res_apply O.obj (homOfLE (hV'V.trans iU.le)) x hxV' s)
  exact congrArg (TopCat.Presheaf.germ O.obj V' x hxV') hk.symm

/-- `𝒪_{X^an} ⟶ 𝒪_{X^an}^×` is an epimorphism: every unit germ has a local logarithm. -/
private lemma epi_eMap {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] :
    Epi (eMap sX) := by
  set O := (sheafCompose (Opens.grothendieckTopology (space sX))
    (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
  set Ou := Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
  refine (ShortComplex.exact_iff_epi (ShortComplex.mk (eMap sX) (0 : Ou ⟶ 0)
    Limits.comp_zero) rfl).1 ?_
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro t _
  obtain ⟨U, hxU, u, rfl⟩ := TopCat.Presheaf.germ_exist _ t
  obtain ⟨V, hxV, hVU, ℓ, hℓ⟩ :=
    exists_expSec_eq (Additive.toMul u : (sections sX U)ˣ) ⟨x, hxU⟩
  refine ⟨TopCat.Presheaf.germ O.obj V x hxV ℓ, ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV (eMap sX).hom ℓ).trans ?_
  refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply Ou.obj (homOfLE hVU) x hxV u)
  refine congrArg (TopCat.Presheaf.germ Ou.obj V x hxV) ?_
  apply Additive.toMul.injective
  exact Units.ext hℓ

/-- **The exponential sequence** on the analytification `X^an` of a scheme `X` over `ℂ`, with its
full structure sheaf: `0 → ℤ_{X^an} → 𝒪_{X^an} → 𝒪_{X^an}^× → 1` is a short exact sequence of
sheaves of abelian groups, where the first map sends an integer to the corresponding constant
section and the second sends the class of a holomorphic germ `f` to the class of
`exp(2πi f)`. -/
@[mmp "lem_mmp_analytic_exponential_sequence"]
public theorem exists_shortExact_exponentialSequence {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] :
    let J := Opens.grothendieckTopology (space sX)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∃ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0), (ShortComplex.mk ι e w).ShortExact ∧
      (∀ (W : Opens (space sX)) (n : ℤ),
        (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) ∧
      (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
        (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
        (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
        (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ g →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
          (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') := by
  intro J O Ou ZA
  refine ⟨ιMap sX, eMap sX, ιMap_comp_eMap sX,
    .mk' (exact_ιMap_eMap sX) (mono_ιMap sX) (epi_eMap sX), ιMap_toSheafify sX, ?_⟩
  intro W s x c f g g' hg hg' hs
  change stalkExp c.1 _ (s.1 x c) = _
  rw [hs, stalkExp_mk]
  congr 1
  apply Subtype.ext
  rw [coe_compGerm _ _ _ _ hg, hg']
  rfl

end MMP.Analytic
