module

public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.EtaleCoordinates
public import MMP.AlgebraicGeometry.DeRham.BettiComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
public import MMP.AlgebraicGeometry.Analytic.Curve.AmpleChernClassPositivity
public import MMP.Analysis.Complex.OrientedConeSimplices
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti

/-!
# Positivity of `i [ω] ∪ \overline{[ω]}` on a smooth projective curve

Let `X` be a smooth projective complex curve, `ω ≠ 0` a global holomorphic one-form with de Rham
class `α ∈ H¹(X^an; ℂ)` (the class of its line integrals), and `L` an ample invertible module.
Then `i (α ∪ \overline{α}) = s · c₁(L)` in `H²(X^an; ℂ)` for a real `s > 0`.

Since `H²(X^an; ℂ)` has dimension at most one and `c₁(L) ≠ 0`, `i (α ∪ \overline{α})` is a
complex multiple of `c₁(L)`. Both classes are evaluated on a fundamental cycle `z` of `X` made of
oriented chart triangles. The class `c₁(L)` takes the value `deg L > 0`. The class
`i (α ∪ \overline{α})` is represented by an explicit cocycle built from local primitives of `ω`,
and by Stokes' theorem on each triangle its value is `2 ∫ |f|² > 0`, in a local coordinate in
which `ω = f dz`.

## Main definitions

* `MMP.Fourfold.Polarization.HasFundamentalChartCycle`: a smooth projective curve has fine
  fundamental cycles of oriented chart triangles.

## Main results

* `MMP.Fourfold.Polarization.HasFundamentalChartCycle.exists_pos_smul_cup_curve`:
  `i (α ∪ \overline{α}) = s · c₁(L)` with `s > 0`, on a curve with fine fundamental chart cycles.
* `MMP.Fourfold.Polarization.HasFundamentalChartCycle.exists_fundamental_chart_cycle`: on such a
  cycle, `c₁(L)` takes the positive real value `deg L`.
* `MMP.Fourfold.Polarization.exists_smul_cup_conjH_eq_ofCocycle`: a cocycle representing
  `i (α ∪ \overline{α})`, built from local primitives.
* `MMP.Fourfold.Polarization.eval_eq_sum_integral`: its value on a cycle of chart triangles is a
  sum of Jacobian integrals.

## Implementation notes

The fundamental cycle of oriented chart triangles, a smooth cellulation of `X^an`, is taken as
the hypothesis `HasFundamentalChartCycle X`; everything else is proved. The value `deg L` of
`c₁(L)` on it is `MMP.Analytic.PolarizationPositivity.exists_pos_eval_eq_of_isAmple`.

## References

* [P. Griffiths, J. Harris, *Principles of algebraic geometry*][GriffithsHarris], §0.6–0.7.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite MMP
open MMP.SingularChain MMP.SingularCochain
open MMP.Analytic

namespace MMP.Fourfold.Polarization

open MMP.Analytic.CurveCupPositivity (squareCollapse face_apply_one face_apply_two
  stdSimplex_continuous_apply stdSimplex_apply_nonneg stdSimplex_two_add stdSimplex_three_add
  coe_projIcc_of_mem)

section LineIntegral

open Set

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

/-- The line integral `∫₀¹ ∑ⱼ fⱼ(p t) (gⱼ ∘ p)'(t) dt` of the algebraic one-form `∑ⱼ fⱼ dgⱼ` on an
open `U` along a path `p` in `U(ℂ)`. -/
noncomputable def lineInt {U : V.Opens}
    (p : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) {m : ℕ} (f g : Fin m → Γ(V, U)) :
    ℂ :=
  ∫ t in (0 : ℝ)..1, ∑ j, ComplexPoints.eval U (f j) (p t) *
    deriv (fun s ↦ ComplexPoints.eval U (g j) (p s)) t

/-- Every regular function is `C¹` along `p` on `[0, 1]`. -/
def IsC1Path {U : V.Opens} (p : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) :
    Prop :=
  ∀ h : Γ(V, U), ContDiffOn ℝ 1 (fun t ↦ ComplexPoints.eval U h (p t)) (Icc 0 1)

/-- The integrand of a line integral along a `C¹` path is interval integrable. -/
theorem intervalIntegrable_lineInt {U : V.Opens}
    {p : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U} (hC : IsC1Path p) {m : ℕ}
    (f g : Fin m → Γ(V, U)) :
    IntervalIntegrable (fun t ↦ ∑ j, ComplexPoints.eval U (f j) (p t) *
      deriv (fun s ↦ ComplexPoints.eval U (g j) (p s)) t) MeasureTheory.volume 0 1 := by
  have hterm : ∀ j, IntervalIntegrable (fun t ↦ ComplexPoints.eval U (f j) (p t) *
      deriv (fun s ↦ ComplexPoints.eval U (g j) (p s)) t) MeasureTheory.volume 0 1 := by
    intro j
    have hc : ContinuousOn (fun t ↦ ComplexPoints.eval U (f j) (p t) *
        derivWithin (fun s ↦ ComplexPoints.eval U (g j) (p s)) (Icc 0 1) t) (Icc 0 1) :=
      (hC (f j)).continuousOn.mul
        ((hC (g j)).continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl)
    refine (hc.intervalIntegrable_of_Icc zero_le_one).congr_uIoo fun t ht ↦ ?_
    rw [uIoo_of_le zero_le_one] at ht
    simp only
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hfun : (fun t ↦ ∑ j, ComplexPoints.eval U (f j) (p t) *
      deriv (fun s ↦ ComplexPoints.eval U (g j) (p s)) t) =
      ∑ j, fun t ↦ ComplexPoints.eval U (f j) (p t) *
        deriv (fun s ↦ ComplexPoints.eval U (g j) (p s)) t := by
    funext t
    simp only [Finset.sum_apply]
  rw [hfun]
  exact IntervalIntegrable.sum Finset.univ fun j _ ↦ hterm j

/-- Every Kähler differential is a finite sum `∑ fⱼ dgⱼ`. -/
theorem exists_eq_sum_smul_D {A : Type*} [CommRing A] [Algebra ℂ A] (x : Ω[A⁄ℂ]) :
    ∃ (m : ℕ) (f g : Fin m → A), x = ∑ j, f j • KaehlerDifferential.D ℂ A (g j) := by
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact ⟨1, fun _ ↦ 1, fun _ ↦ a, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, f, g, rfl⟩ := hy
    obtain ⟨m', f', g', rfl⟩ := hz
    exact ⟨m + m', Fin.append f f', Fin.append g g', by simp [Fin.sum_univ_add]⟩
  | smul c y _ hy =>
    obtain ⟨m, f, g, rfl⟩ := hy
    exact ⟨m, fun j ↦ c * f j, g, by simp [Finset.smul_sum, mul_smul]⟩

/-- The point of `U(ℂ)` at time `t` of a singular `1`-simplex lying in `U(ℂ)`, the simplex being
parametrised from its vertex `0` to its vertex `1`. -/
noncomputable abbrev simplexPath (U : V.Opens)
    (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
    (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) (t : ℝ) :
    ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U :=
  ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one t)), hσ _⟩

variable (V) in
/-- `α ∈ H¹(V^an; ℂ)` is a de Rham class of the global one-form `ω`: it is the class of a cocycle
whose value on every `C¹` singular `1`-simplex in an affine chart `U` is the line integral of
`ω|_U`. -/
def IsDR (ω : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (α : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) : Prop :=
  ∃ (φ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1 → ℂ)
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set (Analytification.space (V ↘ Spec (.of ℂ)))) 1),
    α = cohomologyWithSupports.ofCocycle ℂ _ 1 φ hφ ∧
    ∀ (U : V.affineOpens) (m : ℕ) (f g : Fin m → Γ(V, U)),
      (letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens);
        MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
          (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j))) →
      ∀ (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
        (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) (U : V.Opens)),
        IsC1Path (simplexPath (U : V.Opens) σ hσ) →
        φ σ = lineInt (simplexPath (U : V.Opens) σ hσ) f g

/-- Every restricted form has a presentation in `⋀¹`. -/
theorem exists_rep
    (ω : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (U : V.affineOpens) :
    ∃ (m : ℕ) (f g : Fin m → Γ(V, U)),
      (letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens);
        MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
          (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j))) := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
  obtain ⟨m, f, g, h⟩ := exists_eq_sum_smul_D (exteriorPower.oneEquiv Γ(V, U) Ω[Γ(V, U)⁄ℂ]
    (MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
      (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE le_top).op ω)))
  refine ⟨m, f, g, ?_⟩
  apply (exteriorPower.oneEquiv Γ(V, U) Ω[Γ(V, U)⁄ℂ]).injective
  rw [h, map_sum]
  simp only [map_smul, exteriorPower.oneEquiv_ιMulti]

/-- The class of a difference of cocycles is the difference of the classes. -/
theorem ofCocycle_sub {Y : TopCat.{0}} {k : ℕ} {φ ψ : Simplex Y k → ℂ}
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) k) (hψ : ψ ∈ relCocycles ℂ (Set.univᶜ : Set Y) k) :
    cohomologyWithSupports.ofCocycle ℂ Y k (φ - ψ) (sub_mem hφ hψ) =
      cohomologyWithSupports.ofCocycle ℂ Y k φ hφ -
        cohomologyWithSupports.ofCocycle ℂ Y k ψ hψ := by
  simp only [cohomologyWithSupports.ofCocycle, ← map_sub, ← Submodule.Quotient.mk_sub]
  rfl

/-- The class of a scaled cocycle is the scaled class. -/
theorem ofCocycle_smul {Y : TopCat.{0}} {k : ℕ} {φ : Simplex Y k → ℂ}
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) k) (c : ℂ) :
    cohomologyWithSupports.ofCocycle ℂ Y k (c • φ) (Submodule.smul_mem _ c hφ) =
      c • cohomologyWithSupports.ofCocycle ℂ Y k φ hφ := by
  simp only [cohomologyWithSupports.ofCocycle, ← map_smul, ← Submodule.Quotient.mk_smul]
  rfl

end LineIntegral

section EvalForms

variable {A : Type*} [CommRing A] [Algebra ℂ A] (ev : A →+* ℂ)

/-- A `ℂ`-derivation `A → ℂ` at the point `ev`, from its additivity, `ℂ`-linearity and Leibniz
rule. -/
noncomputable def derivationAt (hev : ∀ c, ev (algebraMap ℂ A c) = c) (D : A → ℂ)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hsmul : ∀ (c : ℂ) a, D (algebraMap ℂ A c * a) = c * D a)
    (hmul : ∀ a b, D (a * b) = ev a * D b + ev b * D a) :
    letI : Module A ℂ := Module.compHom ℂ ev
    Derivation ℂ A ℂ :=
  letI : Module A ℂ := Module.compHom ℂ ev
  { toFun := D
    map_add' := hadd
    map_smul' := fun c a ↦ by rw [Algebra.smul_def, hsmul]; rfl
    map_one_eq_zero' := by
      have h := hmul 1 1
      rw [mul_one, map_one, one_mul] at h
      change D 1 = 0
      linear_combination -h
    leibniz' := fun a b ↦ hmul a b }

/-- **A vanishing algebraic `2`-form vanishes on pairs of derivations.** If
`∑ⱼ dfⱼ ∧ dgⱼ = 0` in `⋀² Ω[A⁄ℂ]`, then `∑ⱼ (D₁ fⱼ · D₂ gⱼ - D₂ fⱼ · D₁ gⱼ) = 0` for any two
derivations `D₁, D₂ : A → ℂ` at a point `ev`. -/
theorem sum_derivation_antisymm (hev : ∀ c, ev (algebraMap ℂ A c) = c)
    (D₁ D₂ : A → ℂ)
    (hadd₁ : ∀ a b, D₁ (a + b) = D₁ a + D₁ b)
    (hsmul₁ : ∀ (c : ℂ) a, D₁ (algebraMap ℂ A c * a) = c * D₁ a)
    (hmul₁ : ∀ a b, D₁ (a * b) = ev a * D₁ b + ev b * D₁ a)
    (hadd₂ : ∀ a b, D₂ (a + b) = D₂ a + D₂ b)
    (hsmul₂ : ∀ (c : ℂ) a, D₂ (algebraMap ℂ A c * a) = c * D₂ a)
    (hmul₂ : ∀ a b, D₂ (a * b) = ev a * D₂ b + ev b * D₂ a)
    {m : ℕ} (f g : Fin m → A)
    (h : ∑ j, exteriorPower.ιMulti A 2 ![KaehlerDifferential.D ℂ A (f j),
      KaehlerDifferential.D ℂ A (g j)] = 0) :
    ∑ j, (D₁ (f j) * D₂ (g j) - D₂ (f j) * D₁ (g j)) = 0 := by
  letI : Module A ℂ := Module.compHom ℂ ev
  have e : ∀ (a : A) (z : ℂ), a • z = ev a * z := fun _ _ ↦ rfl
  haveI : IsScalarTower ℂ A ℂ := ⟨fun c a z ↦ by
    rw [e, e, Algebra.smul_def, map_mul, hev, smul_eq_mul, mul_assoc]⟩
  haveI : SMulCommClass A ℂ ℂ := ⟨fun a c z ↦ by
    rw [e, e, smul_eq_mul, smul_eq_mul]; ring⟩
  have hl₁ : ∀ a, (derivationAt ev hev D₁ hadd₁ hsmul₁ hmul₁).liftKaehlerDifferential
      (KaehlerDifferential.D ℂ A a) = D₁ a := fun a ↦
    Derivation.liftKaehlerDifferential_comp_D _ a
  have hl₂ : ∀ a, (derivationAt ev hev D₂ hadd₂ hsmul₂ hmul₂).liftKaehlerDifferential
      (KaehlerDifferential.D ℂ A a) = D₂ a := fun a ↦
    Derivation.liftKaehlerDifferential_comp_D _ a
  let F : Ω[A⁄ℂ] →ₗ[A] Ω[A⁄ℂ] [⋀^Fin 1]→ₗ[A] ℂ :=
    { toFun := fun x ↦ AlternatingMap.ofSubsingleton A _ ℂ (0 : Fin 1)
        ((derivationAt ev hev D₁ hadd₁ hsmul₁ hmul₁).liftKaehlerDifferential x •
          (derivationAt ev hev D₂ hadd₂ hsmul₂ hmul₂).liftKaehlerDifferential)
      map_add' := fun x y ↦ by ext v; simp [add_mul]
      map_smul' := fun a x ↦ by
        ext v
        simp only [AlternatingMap.ofSubsingleton_apply_apply, LinearMap.smul_apply, map_smul,
          RingHom.id_apply, AlternatingMap.smul_apply, e, smul_eq_mul]
        ring }
  have key := congrArg (exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.alternatizeUncurryFin F)) h
  rw [map_sum, map_zero] at key
  simp only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two] at key
  have r0 : ∀ a b : Ω[A⁄ℂ], Fin.removeNth 0 ![a, b] 0 = b := fun _ _ ↦ rfl
  have r1 : ∀ a b : Ω[A⁄ℂ], Fin.removeNth 1 ![a, b] 0 = a := fun _ _ ↦ rfl
  simp only [F, LinearMap.coe_mk, AddHom.coe_mk, AlternatingMap.ofSubsingleton_apply_apply,
    LinearMap.smul_apply, smul_eq_mul, r0, r1, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, hl₁, hl₂] at key
  rw [← key]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fin.sum_univ_two, r0, r1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hl₁, hl₂,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  ring

end EvalForms

section Transfer

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- **Regular functions on another open are locally quotients.** If `y ∈ U(ℂ) ∩ V(ℂ)` with `U`
affine, a regular function `h` on `V` is near `y` a quotient `a / sᵏ` of regular functions on
`U` with `s(y) ≠ 0`: take a basic open `D(s) ⊆ U ∩ V` around `y`, on which `Γ(D(s)) = Γ(U)_s`. -/
theorem exists_eval_mul_pow_eq (U : X.affineOpens) (V : X.Opens) {y : ComplexPoints sX}
    (hyU : y ∈ ComplexPoints.chart (sX := sX) (U : X.Opens))
    (hyV : y ∈ ComplexPoints.chart (sX := sX) V) (h : Γ(X, V)) :
    ∃ (a s : Γ(X, U)) (k : ℕ), ComplexPoints.evalHom (U : X.Opens) ⟨y, hyU⟩ s ≠ 0 ∧
      ∀ y' (hy'U : y' ∈ ComplexPoints.chart (sX := sX) (U : X.Opens)),
        ComplexPoints.evalHom (U : X.Opens) ⟨y', hy'U⟩ s ≠ 0 →
        ∃ hy'V : y' ∈ ComplexPoints.chart (sX := sX) V,
          ComplexPoints.evalHom V ⟨y', hy'V⟩ h *
              ComplexPoints.evalHom (U : X.Opens) ⟨y', hy'U⟩ s ^ k =
            ComplexPoints.evalHom (U : X.Opens) ⟨y', hy'U⟩ a := by
  obtain ⟨s, hsV, hys⟩ := U.2.exists_basicOpen_le (V := (U : X.Opens) ⊓ V)
    ⟨y.toScheme, ComplexPoints.mem_chart_iff.1 hyU, ComplexPoints.mem_chart_iff.1 hyV⟩
    (ComplexPoints.mem_chart_iff.1 hyU)
  have hloc := U.2.isLocalization_basicOpen s
  have hDV : X.basicOpen s ≤ V := hsV.trans inf_le_right
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hak⟩ := IsLocalization.surj (Submonoid.powers s)
    (X.presheaf.map (homOfLE hDV).op h)
  refine ⟨a, s, k, (ComplexPoints.toScheme_mem_basicOpen_iff ⟨y, hyU⟩ s).1 hys,
    fun y' hy'U hy's ↦ ?_⟩
  have hy'D : y' ∈ ComplexPoints.chart (sX := sX) (X.basicOpen s) :=
    ComplexPoints.mem_chart_iff.2 ((ComplexPoints.toScheme_mem_basicOpen_iff ⟨y', hy'U⟩ s).2 hy's)
  refine ⟨ComplexPoints.chart_mono hDV hy'D, ?_⟩
  have hDU : X.basicOpen s ≤ (U : X.Opens) := X.basicOpen_le s
  have e1 := ComplexPoints.evalHom_res hDV ⟨y', hy'D⟩ h
  have e2 := ComplexPoints.evalHom_res hDU ⟨y', hy'D⟩ s
  have e3 := ComplexPoints.evalHom_res hDU ⟨y', hy'D⟩ a
  have hak' := congrArg (ComplexPoints.evalHom (X.basicOpen s) ⟨y', hy'D⟩) hak
  simp only [map_mul, map_pow] at hak'
  rw [e1, e2, e3]
  convert hak' using 2 <;> rfl

open Classical in
/-- Evaluation of a regular function on `U` at a point of `X^an`, extended by `0` off `U(ℂ)`. -/
noncomputable def evalT (U : X.Opens) (h : Γ(X, U)) (y : ComplexPoints sX) : ℂ :=
  if hy : y ∈ ComplexPoints.chart (sX := sX) U then ComplexPoints.eval U h ⟨y, hy⟩ else 0

/-- On `U(ℂ)`, `evalT U h` is evaluation of `h` at the point. -/
theorem evalT_of_mem {U : X.Opens} (h : Γ(X, U)) {y : ComplexPoints sX}
    (hy : y ∈ ComplexPoints.chart (sX := sX) U) :
    evalT U h y = ComplexPoints.evalHom U ⟨y, hy⟩ h := by
  rw [evalT, dif_pos hy, ComplexPoints.evalHom_apply]

/-- `evalT U` is additive in the function. -/
theorem evalT_add {U : X.Opens} (a b : Γ(X, U)) (y : ComplexPoints sX) :
    evalT U (a + b) y = evalT U a y + evalT U b y := by
  by_cases hy : y ∈ ComplexPoints.chart (sX := sX) U
  · simp only [evalT_of_mem _ hy, map_add]
  · simp [evalT, dif_neg hy]

/-- `evalT U` is multiplicative in the function. -/
theorem evalT_mul {U : X.Opens} (a b : Γ(X, U)) (y : ComplexPoints sX) :
    evalT U (a * b) y = evalT U a y * evalT U b y := by
  by_cases hy : y ∈ ComplexPoints.chart (sX := sX) U
  · simp only [evalT_of_mem _ hy, map_mul]
  · simp [evalT, dif_neg hy]

/-- `evalT U` of a product with a constant `c ∈ ℂ` is `c` times `evalT U`. -/
theorem evalT_baseRingHom_mul {U : X.Opens} (c : ℂ) (a : Γ(X, U))
    (y : ComplexPoints sX) :
    evalT U (ComplexPoints.baseRingHom sX U c * a) y = c * evalT U a y := by
  by_cases hy : y ∈ ComplexPoints.chart (sX := sX) U
  · simp only [evalT_of_mem _ hy, map_mul, ComplexPoints.evalHom_baseRingHom]
  · simp [evalT, dif_neg hy]

/-- Evaluation commutes with restriction. -/
theorem evalT_res {U W : X.Opens} (hWU : W ≤ U) (a : Γ(X, U)) {y : ComplexPoints sX}
    (hy : y ∈ ComplexPoints.chart (sX := sX) W) :
    evalT W (X.presheaf.map (homOfLE hWU).op a) y = evalT U a y := by
  rw [evalT_of_mem _ hy, evalT_of_mem _ (ComplexPoints.chart_mono hWU hy),
    ComplexPoints.evalHom_res hWU ⟨y, hy⟩ a]

/-- **Differentiability transfers between affine charts.** If every regular function on the
affine `U` is differentiable along `q` at `t`, so is every regular function on any `V` with
`q t ∈ V(ℂ)`. -/
theorem differentiableAt_evalT_comp (U : X.affineOpens) (V : X.Opens) {q : ℝ → ComplexPoints sX}
    {t : ℝ} (hq : ContinuousAt q t) (hU : q t ∈ ComplexPoints.chart (sX := sX) (U : X.Opens))
    (hV : q t ∈ ComplexPoints.chart (sX := sX) V)
    (hd : ∀ h : Γ(X, U), DifferentiableAt ℝ (fun t ↦ evalT (U : X.Opens) h (q t)) t)
    (h : Γ(X, V)) : DifferentiableAt ℝ (fun t ↦ evalT V h (q t)) t := by
  obtain ⟨a, s, k, hs, hloc⟩ := exists_eval_mul_pow_eq U V hU hV h
  have hsU : ∀ᶠ t' in nhds t, q t' ∈ ComplexPoints.chart (sX := sX) (U : X.Opens) :=
    hq.preimage_mem_nhds ((ComplexPoints.isOpen_chart sX _).mem_nhds hU)
  have hs0 : evalT (U : X.Opens) s (q t) ≠ 0 := by rwa [evalT_of_mem _ hU]
  have hs' : ∀ᶠ t' in nhds t, evalT (U : X.Opens) s (q t') ≠ 0 :=
    (hd s).continuousAt.eventually_ne hs0
  refine ((hd a).div ((hd s).pow k) (pow_ne_zero _ hs0)).congr_of_eventuallyEq ?_
  filter_upwards [hsU, hs'] with t' h1 h2
  rw [evalT_of_mem _ h1] at h2
  obtain ⟨h3, h4⟩ := hloc (q t') h1 h2
  simp only [Pi.div_apply, Pi.pow_apply]
  rw [evalT_of_mem _ h3, evalT_of_mem _ h1, evalT_of_mem _ h1, ← h4,
    mul_div_assoc, div_self (pow_ne_zero _ h2), mul_one]

end Transfer

section Primitive

/-- **Poincaré lemma for `∑ fⱼ dgⱼ`.** On a convex open set of a complex normed space, if the
functions `fⱼ, gⱼ` are holomorphic and `∑ⱼ dfⱼ ∧ dgⱼ = 0`, the one-form `∑ⱼ fⱼ dgⱼ` has a
primitive. -/
theorem exists_hasFDerivAt_sum_smul_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {D : Set E} (hD : Convex ℝ D) (hDo : IsOpen D) {m : ℕ}
    (Hf Hg : Fin m → E → ℂ) (hf : ∀ j, ∀ z ∈ D, AnalyticAt ℂ (Hf j) z)
    (hg : ∀ j, ∀ z ∈ D, AnalyticAt ℂ (Hg j) z)
    (hanti : ∀ z ∈ D, ∀ u v : E, ∑ j, (fderiv ℝ (Hf j) z u * fderiv ℝ (Hg j) z v -
      fderiv ℝ (Hf j) z v * fderiv ℝ (Hg j) z u) = 0) :
    ∃ Φ : E → ℂ, ∀ z ∈ D, HasFDerivAt Φ (∑ j, Hf j z • fderiv ℝ (Hg j) z) z := by
  have hgC : ∀ j, ∀ z ∈ D, ContDiffAt ℝ ⊤ (Hg j) z := fun j z hz ↦
    (hg j z hz).contDiffAt.restrict_scalars ℝ
  have hfC : ∀ j, ∀ z ∈ D, ContDiffAt ℝ ⊤ (Hf j) z := fun j z hz ↦
    (hf j z hz).contDiffAt.restrict_scalars ℝ
  have hterm : ∀ z ∈ D, HasFDerivAt (fun w ↦ ∑ j, Hf j w • fderiv ℝ (Hg j) w)
      (∑ j, (Hf j z • fderiv ℝ (fderiv ℝ (Hg j)) z +
        (fderiv ℝ (Hf j) z).smulRight (fderiv ℝ (Hg j) z))) z := by
    intro z hz
    refine HasFDerivAt.fun_sum fun j _ ↦ ?_
    exact ((hfC j z hz).differentiableAt (by simp)).hasFDerivAt.fun_smul
      (((hgC j z hz).fderiv_right (m := 1) le_top).differentiableAt (by simp)).hasFDerivAt
  refine hD.exists_forall_hasFDerivAt_of_fderiv_symmetric hDo
    (fun z hz ↦ (hterm z hz).differentiableAt.differentiableWithinAt) fun z hz u v ↦ ?_
  rw [(hterm z hz).fderiv]
  have hs : ∀ j, fderiv ℝ (fderiv ℝ (Hg j)) z u v = fderiv ℝ (fderiv ℝ (Hg j)) z v u :=
    fun j ↦ ((hgC j z hz).isSymmSndFDerivAt (by simp)) u v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hs,
    Finset.sum_add_distrib]
  have := hanti z hz u v
  rw [Finset.sum_sub_distrib] at this
  linear_combination this

end Primitive

section CrossChart

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

set_option maxRecDepth 8000 in
/-- A presentation `ω|_U = ∑ fⱼ dgⱼ` restricts to the presentation `∑ fⱼ|_W d(gⱼ|_W)` on a smaller
affine open `W`. -/
theorem oneEquiv_res_eq_of_rep
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    {U W : X.affineOpens} (hWU : (W : X.Opens) ≤ U) {m : ℕ} (f g : Fin m → Γ(X, U))
    (h : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f j • exteriorPower.ιMulti Γ(X, U) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, U) (g j))) :
    letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (W : X.Opens)
    exteriorPower.oneEquiv Γ(X, W) Ω[Γ(X, W)⁄ℂ] (MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 W
      (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE le_top).op ω)) =
      ∑ j, X.presheaf.map (homOfLE hWU).op (f j) •
        KaehlerDifferential.D ℂ Γ(X, W) (X.presheaf.map (homOfLE hWU).op (g j)) := by
  letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens)
  letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (W : X.Opens)
  letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res (X ↘ Spec (.of ℂ)) hWU
  have hres : ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (le_top : (W : X.Opens) ≤ ⊤)).op ω =
      ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE hWU).op (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op ω) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hres, MMP.DeRham.formsAlgEquiv_restrict (X ↘ Spec (.of ℂ)) 1 hWU, h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, KaehlerDifferential.mapExteriorPower_ιMulti, ← algebraMap_smul Γ(X, W) (f j),
    map_smul, exteriorPower.oneEquiv_ιMulti, KaehlerDifferential.map_D]
  rfl

set_option maxRecDepth 8000 in
/-- **The integrand at a time does not depend on the affine chart.** If `q t` lies in the affine
opens `U₁` and `U₂` and regular functions on `U₁` are differentiable along `q` at `t`, then two
presentations of `ω` on `U₁` and `U₂` give the same value of `∑ⱼ fⱼ(q t) (gⱼ ∘ q)'(t)`: both
restrict to presentations on a basic open `W ⊆ U₁ ∩ U₂` around `q t`, where
`h ↦ (h ∘ q)'(t)` is a derivation. -/
theorem sum_evalT_mul_deriv_congr
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    {U₁ U₂ : X.affineOpens} {m₁ m₂ : ℕ} (f₁ g₁ : Fin m₁ → Γ(X, U₁)) (f₂ g₂ : Fin m₂ → Γ(X, U₂))
    (h₁ : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U₁ : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U₁
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f₁ j • exteriorPower.ιMulti Γ(X, U₁) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, U₁) (g₁ j)))
    (h₂ : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U₂ : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U₂
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f₂ j • exteriorPower.ιMulti Γ(X, U₂) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, U₂) (g₂ j)))
    {q : ℝ → ComplexPoints (X ↘ Spec (.of ℂ))} {t : ℝ} (hq : ContinuousAt q t)
    (hU₁ : q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U₁ : X.Opens))
    (hU₂ : q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U₂ : X.Opens))
    (hd : ∀ h : Γ(X, U₁), DifferentiableAt ℝ (fun t ↦ evalT (U₁ : X.Opens) h (q t)) t) :
    ∑ j, evalT (U₁ : X.Opens) (f₁ j) (q t) * deriv (fun s ↦ evalT (U₁ : X.Opens) (g₁ j) (q s)) t =
      ∑ j, evalT (U₂ : X.Opens) (f₂ j) (q t) *
        deriv (fun s ↦ evalT (U₂ : X.Opens) (g₂ j) (q s)) t := by
  obtain ⟨s, hsV, hys⟩ := U₁.2.exists_basicOpen_le (V := (U₁ : X.Opens) ⊓ U₂)
    ⟨(q t).toScheme, ComplexPoints.mem_chart_iff.1 hU₁, ComplexPoints.mem_chart_iff.1 hU₂⟩
    (ComplexPoints.mem_chart_iff.1 hU₁)
  let W : X.affineOpens := ⟨X.basicOpen s, U₁.2.basicOpen s⟩
  have hW₁ : (W : X.Opens) ≤ U₁ := hsV.trans inf_le_left
  have hW₂ : (W : X.Opens) ≤ U₂ := hsV.trans inf_le_right
  have hqW : q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (W : X.Opens) :=
    ComplexPoints.mem_chart_iff.2 hys
  have hWnhds :
      ∀ᶠ t' in nhds t, q t' ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (W : X.Opens) :=
    hq.preimage_mem_nhds ((ComplexPoints.isOpen_chart _ _).mem_nhds hqW)
  have hdW : ∀ h : Γ(X, W), DifferentiableAt ℝ (fun t ↦ evalT (W : X.Opens) h (q t)) t :=
    differentiableAt_evalT_comp U₁ (W : X.Opens) hq hU₁ hqW hd
  have hderiv : ∀ {U : X.affineOpens} (hWU : (W : X.Opens) ≤ U) (a : Γ(X, U)),
      deriv (fun s ↦ evalT (W : X.Opens) (X.presheaf.map (homOfLE hWU).op a) (q s)) t =
        deriv (fun s ↦ evalT (U : X.Opens) a (q s)) t := fun hWU a ↦
    Filter.EventuallyEq.deriv_eq (by
      filter_upwards [hWnhds] with t' ht'
      exact evalT_res hWU a ht')
  letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (W : X.Opens)
  let ev := ComplexPoints.evalHom (W : X.Opens) ⟨q t, hqW⟩
  have hev : ∀ c, ev (algebraMap ℂ Γ(X, W) c) = c := fun c ↦
    ComplexPoints.evalHom_baseRingHom _ _ c
  have hevT : ∀ a, ev a = evalT (W : X.Opens) a (q t) := fun a ↦ (evalT_of_mem a hqW).symm
  have key := sum_derivation_antisymm (A := Γ(X, W)) ev hev
  let Dt : Γ(X, W) → ℂ := fun h ↦ deriv (fun s ↦ evalT (W : X.Opens) h (q s)) t
  have hadd : ∀ a b, Dt (a + b) = Dt a + Dt b := fun a b ↦ by
    simp only [Dt, evalT_add]
    exact deriv_fun_add (hdW a) (hdW b)
  have hsmul : ∀ (c : ℂ) a, Dt (algebraMap ℂ Γ(X, W) c * a) = c * Dt a := fun c a ↦ by
    simp only [Dt]
    change deriv (fun s ↦ evalT (W : X.Opens)
      (ComplexPoints.baseRingHom (X ↘ Spec (.of ℂ)) (W : X.Opens) c * a) (q s)) t = _
    simp only [evalT_baseRingHom_mul]
    exact deriv_const_mul c (hdW a)
  have hmul : ∀ a b, Dt (a * b) = ev a * Dt b + ev b * Dt a := fun a b ↦ by
    simp only [Dt, evalT_mul, hevT]
    rw [deriv_fun_mul (hdW a) (hdW b)]
    ring
  letI : Module Γ(X, W) ℂ := Module.compHom ℂ ev
  have e : ∀ (a : Γ(X, W)) (z : ℂ), a • z = ev a * z := fun _ _ ↦ rfl
  haveI : IsScalarTower ℂ Γ(X, W) ℂ := ⟨fun c a z ↦ by
    rw [e, e, Algebra.smul_def, map_mul, hev, smul_eq_mul, mul_assoc]⟩
  let l := (derivationAt ev hev Dt hadd hsmul hmul).liftKaehlerDifferential
  have hl : ∀ a, l (KaehlerDifferential.D ℂ Γ(X, W) a) = Dt a := fun a ↦
    Derivation.liftKaehlerDifferential_comp_D _ a
  have r₁ := congrArg l (oneEquiv_res_eq_of_rep ω hW₁ f₁ g₁ h₁)
  have r₂ := congrArg l (oneEquiv_res_eq_of_rep ω hW₂ f₂ g₂ h₂)
  rw [r₁] at r₂
  simpa only [map_sum, map_smul, hl, e, hevT, Dt, hderiv, evalT_res _ _ hqW] using r₂

set_option maxRecDepth 8000 in
/-- **Closedness on an affine open.** If the global one-form `ω` is closed and `ω|_U = ∑ fⱼ dgⱼ`
then `∑ⱼ dfⱼ ∧ dgⱼ = 0` in `⋀² Ω[Γ(U)⁄ℂ]`. -/
theorem sum_ιMulti_two_eq_zero_of_rep
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (hd : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) ω = 0)
    (U : X.affineOpens) {m : ℕ} (f g : Fin m → Γ(X, U))
    (h : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f j • exteriorPower.ιMulti Γ(X, U) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, U) (g j))) :
    letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens)
    ∑ j, exteriorPower.ιMulti Γ(X, U) 2
      ![KaehlerDifferential.D ℂ Γ(X, U) (f j), KaehlerDifferential.D ℂ Γ(X, U) (g j)] = 0 := by
  letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens)
  have hd' : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 (1 + 1)).val.app (op ⊤) ω = 0 := hd
  have hnat := (PresheafOfModules.naturality_apply
    (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 (1 + 1)).val
    (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op ω).symm
  have h5 := MMP.DeRham.formsAlgEquiv_d (X ↘ Spec (.of ℂ)) 1 U
    (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE le_top).op ω)
  erw [← hnat, hd', map_zero, map_zero, h, map_sum] at h5
  rw [h5]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show (![KaehlerDifferential.D ℂ Γ(X, U) (f j), KaehlerDifferential.D ℂ Γ(X, U) (g j)] :
      Fin 2 → Ω[Γ(X, U)⁄ℂ]) = fun i ↦ KaehlerDifferential.D ℂ Γ(X, U) (![f j, g j] i) by
    ext i; fin_cases i <;> rfl]
  exact (KaehlerDifferential.deRhamDifferential_smul_ιMulti_D (A := ℂ) (B := Γ(X, U)) 1
    ![f j, g j]).symm

/-- A regular function read through the inverse of an étale chart is holomorphic. -/
theorem analyticAt_evalT_symm {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (V : X.Opens) (h : Γ(X, V))
    {z : Fin n → ℂ} (hz : z ∈ c.toOpenPartialHomeomorph.target ∩
      c.toOpenPartialHomeomorph.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V) :
    AnalyticAt ℂ (fun w ↦ evalT V h (c.toOpenPartialHomeomorph.symm w)) z := by
  obtain ⟨G, hG, hGe⟩ := c.exists_analyticOnNhd V h
  have hSo : IsOpen (c.toOpenPartialHomeomorph.target ∩
      c.toOpenPartialHomeomorph.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V) :=
    c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm (ComplexPoints.isOpen_chart _ V)
  refine (hG z hz).congr ?_
  filter_upwards [hSo.mem_nhds hz] with w hw
  rw [evalT_of_mem _ hw.2, ComplexPoints.evalHom_apply,
    hGe _ (c.toOpenPartialHomeomorph_symm_mem hw.1) hw.2,
    c.toOpenPartialHomeomorph.right_inv hw.1]

set_option maxRecDepth 8000 in
/-- **Local primitives of a closed one-form.** Every point of `X^an` has an open neighbourhood `B`
carrying a function `F` whose increments along every path `q` in `B` along which the regular
functions of some affine chart `U` are differentiable are the line integrals of `ω`, read through
any presentation of `ω|_U`. -/
theorem exists_local_primitive {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (hd : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) ω = 0)
    (x : ComplexPoints (X ↘ Spec (.of ℂ))) :
    ∃ (B : Set (ComplexPoints (X ↘ Spec (.of ℂ)))) (F : ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ),
      IsOpen B ∧ x ∈ B ∧
      ∀ (U : X.affineOpens) {m : ℕ} (f g : Fin m → Γ(X, U)),
        (letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens);
          MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U
            (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
              (homOfLE le_top).op ω) =
            ∑ j, f j • exteriorPower.ιMulti Γ(X, U) 1
              (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, U) (g j))) →
        ∀ (q : ℝ → ComplexPoints (X ↘ Spec (.of ℂ))), Continuous q → ∀ {a b : ℝ}, a ≤ b →
          (∀ t ∈ Set.Icc a b, q t ∈ B) →
          (∀ t ∈ Set.Icc a b, q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U : X.Opens)) →
          (∀ h' : Γ(X, U), ∀ t ∈ Set.Ioo a b,
            DifferentiableAt ℝ (fun t ↦ evalT (U : X.Opens) h' (q t)) t) →
          IntervalIntegrable (fun t ↦ ∑ j, evalT (U : X.Opens) (f j) (q t) *
            deriv (fun s ↦ evalT (U : X.Opens) (g j) (q s)) t) MeasureTheory.volume a b →
          F (q b) - F (q a) = ∫ t in a..b, ∑ j, evalT (U : X.Opens) (f j) (q t) *
            deriv (fun s ↦ evalT (U : X.Opens) (g j) (q s)) t := by
  obtain ⟨c, hxc⟩ := ComplexPoints.EtaleCoordinateChart.exists_mem_W (sX := X ↘ Spec (.of ℂ))
    (n := n) x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x.toScheme) isOpen_univ
  set e := c.toOpenPartialHomeomorph
  have hsrc : e.source = c.W := c.source_toOpenPartialHomeomorph
  have hxe : x ∈ e.source := hsrc ▸ hxc
  set S := e.target ∩ e.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V
  have hSo : IsOpen S := e.isOpen_inter_preimage_symm (ComplexPoints.isOpen_chart _ V)
  have hxS : e x ∈ S :=
    ⟨e.map_source hxe, by
      rw [Set.mem_preimage, e.left_inv hxe]
      exact ComplexPoints.mem_chart_iff.2 hxV⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo (e x) hxS
  set D := Metric.ball (e x) r
  have hD : Convex ℝ D := convex_ball _ _
  have hDo : IsOpen D := Metric.isOpen_ball
  let V' : X.affineOpens := ⟨V, hV⟩
  obtain ⟨m₀, f₀, g₀, h₀⟩ := exists_rep ω V'
  let H : Γ(X, V) → (Fin n → ℂ) → ℂ := fun h w ↦ evalT V h (e.symm w)
  have hH : ∀ h, ∀ z ∈ D, AnalyticAt ℂ (H h) z := fun h z hz ↦
    analyticAt_evalT_symm c V h (hball hz)
  have hHd : ∀ h, ∀ z ∈ D, DifferentiableAt ℝ (H h) z := fun h z hz ↦
    ((hH h z hz).differentiableAt).restrictScalars ℝ
  have hclosed := sum_ιMulti_two_eq_zero_of_rep ω hd V' f₀ g₀ h₀
  have hanti : ∀ z ∈ D, ∀ u v : Fin n → ℂ, ∑ j, (fderiv ℝ (H (f₀ j)) z u *
      fderiv ℝ (H (g₀ j)) z v - fderiv ℝ (H (f₀ j)) z v * fderiv ℝ (H (g₀ j)) z u) = 0 := by
    intro z hz u v
    have hzV : e.symm z ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V := (hball hz).2
    letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) V
    let ev := ComplexPoints.evalHom V ⟨e.symm z, hzV⟩
    have hev : ∀ c, ev (algebraMap ℂ Γ(X, V) c) = c := fun c ↦
      ComplexPoints.evalHom_baseRingHom _ _ c
    have hevH : ∀ a, ev a = H a z := fun a ↦ (evalT_of_mem a hzV).symm
    have hadd : ∀ (w : Fin n → ℂ) (a b : Γ(X, V)),
        fderiv ℝ (H (a + b)) z w = fderiv ℝ (H a) z w + fderiv ℝ (H b) z w := fun w a b ↦ by
      have : H (a + b) = fun w ↦ H a w + H b w := funext fun w ↦ evalT_add _ _ _
      rw [this, fderiv_fun_add (hHd a z hz) (hHd b z hz)]
      rfl
    have hsmul : ∀ (w : Fin n → ℂ) (c : ℂ) (a : Γ(X, V)),
        fderiv ℝ (H (algebraMap ℂ Γ(X, V) c * a)) z w = c * fderiv ℝ (H a) z w := fun w c a ↦ by
      have : H (algebraMap ℂ Γ(X, V) c * a) = fun w ↦ c * H a w :=
        funext fun w ↦ evalT_baseRingHom_mul c a _
      rw [this, fderiv_const_mul (hHd a z hz)]
      rfl
    have hmul : ∀ (w : Fin n → ℂ) (a b : Γ(X, V)),
        fderiv ℝ (H (a * b)) z w = ev a * fderiv ℝ (H b) z w + ev b * fderiv ℝ (H a) z w :=
      fun w a b ↦ by
        have : H (a * b) = fun w ↦ H a w * H b w := funext fun w ↦ evalT_mul _ _ _
        rw [this, fderiv_fun_mul (hHd a z hz) (hHd b z hz), hevH, hevH]
        simp [smul_eq_mul]
    exact sum_derivation_antisymm ev hev (fun h ↦ fderiv ℝ (H h) z u)
      (fun h ↦ fderiv ℝ (H h) z v) (hadd u) (hsmul u) (hmul u) (hadd v) (hsmul v) (hmul v)
      f₀ g₀ hclosed
  obtain ⟨Φ, hΦ⟩ := exists_hasFDerivAt_sum_smul_fderiv hD hDo (fun j ↦ H (f₀ j))
    (fun j ↦ H (g₀ j)) (fun j ↦ hH (f₀ j)) (fun j ↦ hH (g₀ j)) hanti
  refine ⟨e.source ∩ e ⁻¹' D, fun y ↦ Φ (e y), e.isOpen_inter_preimage hDo,
    ⟨hxe, Metric.mem_ball_self hr⟩, ?_⟩
  intro U m f g hrep q hq a b hab hqB hqU hC hint
  have hqV : ∀ t ∈ Set.Icc a b, q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V :=
    fun t ht ↦ by
      have := (hball (hqB t ht).2).2
      rwa [Set.mem_preimage, e.left_inv (hqB t ht).1] at this
  show Φ (e (q b)) - Φ (e (q a)) = _
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t ↦ Φ (e (q t))) hab ?_
    (fun t ht ↦ ?_) hint).symm
  · refine ContinuousOn.comp (g := Φ) (fun z hz ↦ (hΦ z hz).continuousAt.continuousWithinAt)
      ?_ (fun t ht ↦ (hqB t ht).2)
    exact e.continuousOn.comp hq.continuousOn fun t ht ↦ (hqB t ht).1
  · have htI : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
    have hW : q t ∈ c.W := hsrc ▸ (hqB t htI).1
    have hcU : q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) c.U := c.subset hW
    have hcoord : DifferentiableAt ℝ (fun t' ↦ fun i ↦ evalT c.U (c.z i) (q t')) t :=
      differentiableAt_pi.2 fun i ↦ differentiableAt_evalT_comp U c.U hq.continuousAt
        (hqU t htI) hcU (fun h' ↦ hC h' t ht) (c.z i)
    have heq : (fun t' ↦ e (q t')) =ᶠ[nhds t] fun t' ↦ fun i ↦ evalT c.U (c.z i) (q t') := by
      have hWo : IsOpen c.W := c.isOpen
      filter_upwards [hq.continuousAt.preimage_mem_nhds (hWo.mem_nhds hW)] with t' ht'
      funext i
      rw [c.toOpenPartialHomeomorph_apply ht' i, evalT_of_mem _ (c.subset ht'),
        ComplexPoints.evalHom_apply]
    have hw : HasDerivAt (fun t' ↦ e (q t')) (deriv (fun t' ↦ e (q t')) t) t := by
      have := hcoord.hasDerivAt
      rw [← heq.deriv_eq] at this
      exact this.congr_of_eventuallyEq heq
    have hzD : e (q t) ∈ D := (hqB t htI).2
    have hchain := (hΦ (e (q t)) hzD).comp_hasDerivAt t hw
    refine hchain.congr_deriv ?_
    beta_reduce
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hterm : ∀ j, H (f₀ j) (e (q t)) * fderiv ℝ (H (g₀ j)) (e (q t))
        (deriv (fun t' ↦ e (q t')) t) =
        evalT V (f₀ j) (q t) * deriv (fun s ↦ evalT V (g₀ j) (q s)) t := by
      intro j
      have hHq : H (f₀ j) (e (q t)) = evalT V (f₀ j) (q t) := by
        simp only [H, e.left_inv (hqB t htI).1]
      have hg := ((hHd (g₀ j) _ hzD).hasFDerivAt.comp_hasDerivAt t hw).deriv
      have hgq : (fun s ↦ H (g₀ j) (e (q s))) =ᶠ[nhds t] fun s ↦ evalT V (g₀ j) (q s) := by
        filter_upwards [hq.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds
          (hqB t htI).1)] with s hs
        simp only [H, e.left_inv hs]
      rw [hHq, ← hg]
      exact congrArg _ hgq.deriv_eq
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j]
    exact (sum_evalT_mul_deriv_congr ω f g f₀ g₀ hrep h₀ hq.continuousAt (hqU t htI)
      (hqV t htI) fun h' ↦ hC h' t ht).symm

/-- The property of a local primitive `F` of `ω` on `B`, as produced by
`exists_local_primitive`. -/
def IsLocalPrimitive
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (B : Set (ComplexPoints (X ↘ Spec (.of ℂ)))) (F : ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ) :
    Prop :=
  ∀ (U : X.affineOpens) {m : ℕ} (f g : Fin m → Γ(X, U)),
    (letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens);
      MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U
        (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE le_top).op ω) =
        ∑ j, f j • exteriorPower.ιMulti Γ(X, U) 1
          (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, U) (g j))) →
    ∀ (q : ℝ → ComplexPoints (X ↘ Spec (.of ℂ))), Continuous q → ∀ {a b : ℝ}, a ≤ b →
      (∀ t ∈ Set.Icc a b, q t ∈ B) →
      (∀ t ∈ Set.Icc a b, q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U : X.Opens)) →
      (∀ h' : Γ(X, U), ∀ t ∈ Set.Ioo a b,
        DifferentiableAt ℝ (fun t ↦ evalT (U : X.Opens) h' (q t)) t) →
      IntervalIntegrable (fun t ↦ ∑ j, evalT (U : X.Opens) (f j) (q t) *
        deriv (fun s ↦ evalT (U : X.Opens) (g j) (q s)) t) MeasureTheory.volume a b →
      F (q b) - F (q a) = ∫ t in a..b, ∑ j, evalT (U : X.Opens) (f j) (q t) *
        deriv (fun s ↦ evalT (U : X.Opens) (g j) (q s)) t

set_option maxRecDepth 8000 in
/-- **Two local primitives differ by a locally constant function.** Near each point of
`B₁ ∩ B₂`, both have the same increments along the straight segments of an étale coordinate
ball. -/
theorem eventually_sub_eq_of_isLocalPrimitive {n : ℕ}
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    {B₁ B₂ : Set (ComplexPoints (X ↘ Spec (.of ℂ)))} {F₁ F₂ : ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ}
    (hB₁ : IsOpen B₁) (hB₂ : IsOpen B₂) (h₁ : IsLocalPrimitive ω B₁ F₁)
    (h₂ : IsLocalPrimitive ω B₂ F₂) {w : ComplexPoints (X ↘ Spec (.of ℂ))} (hw : w ∈ B₁ ∩ B₂) :
    ∀ᶠ y in nhds w, F₁ y - F₂ y = F₁ w - F₂ w := by
  obtain ⟨c, hwc⟩ := ComplexPoints.EtaleCoordinateChart.exists_mem_W (sX := X ↘ Spec (.of ℂ))
    (n := n) w
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w.toScheme) isOpen_univ
  set e := c.toOpenPartialHomeomorph
  have hsrc : e.source = c.W := c.source_toOpenPartialHomeomorph
  have hwe : w ∈ e.source := hsrc ▸ hwc
  set S := e.target ∩ e.symm ⁻¹' (ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V ∩ (B₁ ∩ B₂))
  have hSo : IsOpen S := e.isOpen_inter_preimage_symm
    ((ComplexPoints.isOpen_chart _ V).inter (hB₁.inter hB₂))
  have hwS : e w ∈ S :=
    ⟨e.map_source hwe, by
      rw [Set.mem_preimage, e.left_inv hwe]
      exact ⟨ComplexPoints.mem_chart_iff.2 hwV, hw⟩⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo (e w) hwS
  have hD : Convex ℝ (Metric.ball (e w) r) := convex_ball _ _
  filter_upwards [e.open_source.mem_nhds hwe,
    e.continuousAt hwe (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with y hy hyD
  let V' : X.affineOpens := ⟨V, hV⟩
  obtain ⟨m, f, g, hrep⟩ := exists_rep ω V'
  let L : ℝ → Fin n → ℂ := fun t ↦
    (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)) • e w +
      (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) • e y
  have hLc : Continuous L := by
    have := continuous_subtype_val.comp (continuous_projIcc (a := (0 : ℝ)) (b := 1)
      (h := zero_le_one))
    exact ((continuous_const.sub this).smul continuous_const).add (this.smul continuous_const)
  have hLD : ∀ t, L t ∈ Metric.ball (e w) r := fun t ↦
    hD (Metric.mem_ball_self hr) hyD (sub_nonneg.2 (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.2)
      (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.1 (by ring)
  let q : ℝ → ComplexPoints (X ↘ Spec (.of ℂ)) := fun t ↦ e.symm (L t)
  have hq : Continuous q :=
    e.continuousOn_symm.comp_continuous hLc fun t ↦ (hball (hLD t)).1
  have hqS : ∀ t, q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V ∩ (B₁ ∩ B₂) :=
    fun t ↦ (hball (hLD t)).2
  have hLt : ∀ t ∈ Set.Icc (0 : ℝ) 1, L t = (1 - t) • e w + t • e y := fun t ht ↦ by
    simp only [L, Set.projIcc_of_mem _ ht]
  have hG : ∀ h : Γ(X, V), ∃ G : (Fin n → ℂ) → ℂ, (∀ z ∈ Metric.ball (e w) r, AnalyticAt ℂ G z) ∧
      ∀ t, evalT V h (q t) = G (L t) := fun h ↦ by
    obtain ⟨G, hG, hGe⟩ := c.exists_analyticOnNhd V h
    refine ⟨G, fun z hz ↦ hG z ⟨(hball hz).1, (hball hz).2.1⟩, fun t ↦ ?_⟩
    rw [evalT_of_mem _ (hqS t).1, ComplexPoints.evalHom_apply,
      hGe _ (c.toOpenPartialHomeomorph_symm_mem (hball (hLD t)).1) (hqS t).1,
      e.right_inv (hball (hLD t)).1]
  have hLd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt L (e y - e w) t := fun t ht ↦ by
    have h1 : HasDerivAt (fun s : ℝ ↦ (1 - s) • e w + s • e y) (e y - e w) t := by
      refine HasDerivAt.congr_deriv ((((hasDerivAt_id' t).const_sub 1).smul_const (e w)).add
        ((hasDerivAt_id' t).smul_const (e y))) ?_
      simp only [neg_smul, one_smul, sub_eq_neg_add]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hLt s hs
  have hdiff : ∀ h' : Γ(X, V), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t ↦ evalT V h' (q t)) t := fun h' t ht ↦ by
    obtain ⟨G, hGa, hGe⟩ := hG h'
    simp only [hGe]
    exact (((hGa _ (hLD t)).differentiableAt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hLd t ht)).differentiableAt
  have hint : IntervalIntegrable (fun t ↦ ∑ j, evalT V (f j) (q t) *
      deriv (fun s ↦ evalT V (g j) (q s)) t) MeasureTheory.volume 0 1 := by
    have hterm : ∀ j, IntervalIntegrable (fun t ↦ evalT V (f j) (q t) *
        deriv (fun s ↦ evalT V (g j) (q s)) t) MeasureTheory.volume 0 1 := by
      intro j
      obtain ⟨Gf, hGfa, hGfe⟩ := hG (f j)
      obtain ⟨Gg, hGga, hGge⟩ := hG (g j)
      have hGfc : ContinuousOn Gf (Metric.ball (e w) r) := fun z hz ↦
        (hGfa z hz).continuousAt.continuousWithinAt
      have hGgc : ContinuousOn (fderiv ℝ Gg) (Metric.ball (e w) r) := fun z hz ↦
        ((((hGga z hz).contDiffAt (n := ⊤)).restrict_scalars ℝ).fderiv_right (m := 0)
          le_top).continuousAt.continuousWithinAt
      have hc : Continuous fun t ↦ Gf (L t) * fderiv ℝ Gg (L t) (e y - e w) :=
        (hGfc.comp_continuous hLc hLD).mul
          ((hGgc.comp_continuous hLc hLD).clm_apply continuous_const)
      refine (hc.intervalIntegrable 0 1).congr_uIoo fun t ht ↦ ?_
      rw [Set.uIoo_of_le zero_le_one] at ht
      simp only [hGfe]
      rw [show (fun s ↦ evalT V (g j) (q s)) = fun s ↦ Gg (L s) from funext hGge]
      exact congrArg _ (((hGga _ (hLD t)).differentiableAt.restrictScalars ℝ
        ).hasFDerivAt.comp_hasDerivAt t (hLd t ht)).deriv.symm
    have hfun : (fun t ↦ ∑ j, evalT V (f j) (q t) * deriv (fun s ↦ evalT V (g j) (q s)) t) =
        ∑ j, fun t ↦ evalT V (f j) (q t) * deriv (fun s ↦ evalT V (g j) (q s)) t := by
      funext t
      simp only [Finset.sum_apply]
    rw [hfun]
    exact IntervalIntegrable.sum Finset.univ fun j _ ↦ hterm j
  have e1 := h₁ V' f g hrep q hq zero_le_one (fun t _ ↦ (hqS t).2.1) (fun t _ ↦ (hqS t).1)
    hdiff hint
  have e2 := h₂ V' f g hrep q hq zero_le_one (fun t _ ↦ (hqS t).2.2) (fun t _ ↦ (hqS t).1)
    hdiff hint
  have hq0 : q 0 = w := by
    simp only [q, hLt 0 ⟨le_rfl, zero_le_one⟩, sub_zero, one_smul, zero_smul, add_zero]
    exact e.left_inv hwe
  have hq1 : q 1 = y := by
    simp only [q, hLt 1 ⟨zero_le_one, le_rfl⟩, sub_self, one_smul, zero_smul, zero_add]
    exact e.left_inv hy
  rw [hq0, hq1] at e1 e2
  linear_combination e1 - e2

end CrossChart

section Small

open SingularChain Finsupp

/-- A cocycle vanishing on every simplex that is small for some open cover is a coboundary:
it agrees up to a coboundary with its transport by the small-chains map, which is zero. -/
theorem ofCocycle_eq_zero_of_forall_small {Y : TopCat.{0}} {k : ℕ} {ψ : Simplex Y k → ℂ}
    (hψ : ψ ∈ relCocycles ℂ (Set.univᶜ : Set Y) k)
    (hloc : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∀ σ : Simplex Y k, Set.range σ ⊆ B → ψ σ = 0) :
    cohomologyWithSupports.ofCocycle ℂ Y k ψ hψ = 0 := by
  set 𝒰 : Set (Set Y) := {B | IsOpen B ∧ ∀ σ : Simplex Y k, Set.range σ ⊆ B → ψ σ = 0}
  have h𝒰 : ∀ U ∈ 𝒰, IsOpen U := fun U hU ↦ hU.1
  have hcov : ∀ σ : Simplex Y k, Set.range σ ⊆ ⋃₀ 𝒰 := fun σ y _ ↦ by
    obtain ⟨B, hB, hyB, h⟩ := hloc y
    exact ⟨B, ⟨hB, h⟩, hyB⟩
  have hρ : SingularCochain.pullback (smallChainMap ℂ 𝒰 k) ψ = 0 := by
    funext σ
    have hs := smallChainMap_single_mem_small (R := ℂ) h𝒰 k (hcov σ)
    rw [Finsupp.mem_supported] at hs
    change SingularCochain.eval ψ (smallChainMap ℂ 𝒰 k (Finsupp.single σ 1)) = 0
    rw [SingularCochain.eval, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun τ hτ ↦ ?_
    obtain ⟨U, hU, hτU⟩ := hs hτ
    rw [hU.2 τ hτU, smul_zero]
  have hmem := pullback_smallChainMap_sub_mem_relCoboundaries 𝒰 hψ
  rw [hρ, zero_sub, neg_mem_iff] at hmem
  simp only [cohomologyWithSupports.ofCocycle]
  rw [show (Submodule.Quotient.mk ⟨ψ, hψ⟩ :
      relCohomology ℂ (Set.univᶜ : Set Y) k) = 0 from (Submodule.Quotient.mk_eq_zero _).2 hmem,
    map_zero]

section Convex

variable {Y : TopCat.{0}} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph Y E) {D : Set E} (hD : Convex ℝ D) (hDt : D ⊆ e.target)

include hD in
/-- An affine combination `(1 - s) a + s b`, `s ∈ [0, 1]`, of points of a convex set `D` lies in
`D`. -/
theorem segment_mem {a b : E} (ha : a ∈ D) (hb : b ∈ D) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ 1) : (1 - s) • a + s • b ∈ D :=
  hD ha hb (sub_nonneg.2 h1) h0 (by ring)

/-- The singular `1`-simplex `x ↦ e⁻¹((1 - x₁) a + x₁ b)` running along the segment `[a, b]` of
a convex subset of the target of a chart. -/
noncomputable def segSimplex {a b : E} (ha : a ∈ D) (hb : b ∈ D) : Simplex Y 1 :=
  ⟨fun x ↦ e.symm ((1 - x 1) • a + x 1 • b), by
    refine e.continuousOn_symm.comp_continuous
      (((continuous_const.sub (stdSimplex_continuous_apply 1)).smul continuous_const).add
        ((stdSimplex_continuous_apply 1).smul continuous_const)) fun x ↦
      hDt (segment_mem hD ha hb (stdSimplex_apply_nonneg x 1) ?_)
    linarith [stdSimplex_apply_nonneg x 0, stdSimplex_two_add x]⟩

include hD hDt in
/-- **A cocycle vanishing on segments of a convex chart vanishes on all its simplices.** A
singular `1`-simplex `σ` in the chart is joined to the segment between its ends by the
straight-line homotopy; the square of that homotopy is cut along its diagonal into two
singular `2`-simplices, whose other faces are constant. -/
theorem eq_zero_of_forall_segSimplex {ψ : Simplex Y 1 → ℂ}
    (hψ : coboundary ℂ 1 ψ = 0)
    (hseg : ∀ (a b : E) (ha : a ∈ D) (hb : b ∈ D), ψ (segSimplex e hD hDt ha hb) = 0)
    (σ : Simplex Y 1) (hσ : ∀ x, σ x ∈ e.source ∧ e (σ x) ∈ D) : ψ σ = 0 := by
  have hx1 := stdSimplex_two_add
  have ht := stdSimplex_three_add
  have hnn := @stdSimplex_apply_nonneg
  let pt : ℝ → stdSimplex ℝ (Fin 2) := fun r ↦
    stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one r)
  have hpt : Continuous pt := stdSimplexHomeomorphUnitInterval.symm.continuous.comp
    continuous_projIcc
  have hpt_x : ∀ x : stdSimplex ℝ (Fin 2), pt (x 1) = x := fun x ↦ by
    have hx : Set.projIcc (0 : ℝ) 1 zero_le_one (x 1) = stdSimplexHomeomorphUnitInterval x :=
      Set.projIcc_of_mem _ ⟨hnn x 1, by linarith [hnn x 0, hx1 x]⟩
    simp only [pt, hx, Homeomorph.symm_apply_apply]
  let P : ℝ → E := fun r ↦ e (σ (pt r))
  have hP : Continuous P :=
    e.continuousOn.comp_continuous (σ.continuous.comp hpt) fun r ↦ (hσ _).1
  have hPD : ∀ r, P r ∈ D := fun r ↦ (hσ _).2
  have hA0 := hPD 0
  have hA1 := hPD 1
  let H : ℝ → ℝ → E := fun r μ ↦ (1 - μ) • P r + μ • ((1 - r) • P 0 + r • P 1)
  have hH : Continuous fun p : ℝ × ℝ ↦ H p.1 p.2 := by
    simp only [H]
    fun_prop
  have hHD : ∀ r μ, 0 ≤ r → r ≤ 1 → 0 ≤ μ → μ ≤ 1 → H r μ ∈ D := fun r μ hr0 hr1 hμ0 hμ1 ↦
    segment_mem hD (hPD r) (segment_mem hD hA0 hA1 hr0 hr1) hμ0 hμ1
  let T₁ : Simplex Y 2 := ⟨fun t ↦ e.symm (H (t 1 + t 2) (t 2)), by
    refine e.continuousOn_symm.comp_continuous
      (hH.comp (((stdSimplex_continuous_apply 1).add (stdSimplex_continuous_apply 2)).prodMk
        (stdSimplex_continuous_apply 2)))
      fun t ↦ hDt (hHD _ _ (add_nonneg (hnn t 1) (hnn t 2)) (by linarith [ht t, hnn t 0])
        (hnn t 2) (by linarith [ht t, hnn t 0, hnn t 1]))⟩
  let T₂ : Simplex Y 2 := ⟨fun t ↦ e.symm (H (t 2) (t 1 + t 2)), by
    refine e.continuousOn_symm.comp_continuous
      (hH.comp ((stdSimplex_continuous_apply 2).prodMk
        ((stdSimplex_continuous_apply 1).add (stdSimplex_continuous_apply 2))))
      fun t ↦ hDt (hHD _ _ (hnn t 2) (by linarith [ht t, hnn t 0, hnn t 1])
        (add_nonneg (hnn t 1) (hnn t 2)) (by linarith [ht t, hnn t 0]))⟩
  have hf : ∀ (T' : Simplex Y 2) (k : Fin 3) (x : stdSimplex ℝ (Fin 2)),
      T'.comp (face 1 k) x = T' (face 1 k x) := fun _ _ _ ↦ rfl
  have c0 : ∀ x, (face 1 0 x) 1 = x 0 ∧ (face 1 0 x) 2 = x 1 := fun x ↦
    ⟨by simp [face_apply_one], by simp [face_apply_two]⟩
  have c1 : ∀ x, (face 1 1 x) 1 = 0 ∧ (face 1 1 x) 2 = x 1 := fun x ↦
    ⟨by simp [face_apply_one], by simp [face_apply_two]⟩
  have c2 : ∀ x, (face 1 2 x) 1 = x 1 ∧ (face 1 2 x) 2 = 0 := fun x ↦
    ⟨by simp [face_apply_one], by simp [face_apply_two]⟩
  have e10 : T₁.comp (face 1 0) = segSimplex e hD hDt hA1 hA1 := by
    ext x
    rw [hf]
    simp only [T₁, segSimplex, ContinuousMap.coe_mk, (c0 x).1, (c0 x).2, hx1 x, H]
    congr 1
    module
  have e11 : T₁.comp (face 1 1) = T₂.comp (face 1 1) := by
    ext x
    rw [hf, hf]
    simp only [T₁, T₂, ContinuousMap.coe_mk, (c1 x).1, (c1 x).2, zero_add]
  have e12 : T₁.comp (face 1 2) = σ := by
    ext x
    rw [hf]
    simp only [T₁, ContinuousMap.coe_mk, (c2 x).1, (c2 x).2, add_zero, H, sub_zero, one_smul,
      zero_smul, P, hpt_x]
    exact e.left_inv (hσ x).1
  have e20 : T₂.comp (face 1 0) = segSimplex e hD hDt hA0 hA1 := by
    ext x
    rw [hf]
    simp only [T₂, segSimplex, ContinuousMap.coe_mk, (c0 x).1, (c0 x).2, hx1 x, H]
    congr 1
    module
  have e22 : T₂.comp (face 1 2) = segSimplex e hD hDt hA0 hA0 := by
    ext x
    rw [hf]
    simp only [T₂, segSimplex, ContinuousMap.coe_mk, (c2 x).1, (c2 x).2, zero_add, H]
    congr 1
    module
  have h1 := congrFun hψ T₁
  have h2 := congrFun hψ T₂
  rw [coboundary_apply, Fin.sum_univ_three] at h1 h2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_mul,
    neg_one_mul, Pi.zero_apply] at h1 h2
  rw [e10, e11, e12, hseg] at h1
  rw [e20, e22, hseg, hseg] at h2
  linear_combination h1 - h2

end Convex

/-- For `t ∈ [0, 1]`, the point of `Δ¹` corresponding to `t` has coordinate `t` at vertex `1`. -/
theorem symm_projIcc_apply_one {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one t)) 1 = t := by
  rw [Set.projIcc_of_mem _ ht]
  rfl

/-- **Locally, a cocycle vanishing on `C¹` chart simplices vanishes.** On a smooth complex scheme,
every point of `X^an` has a neighbourhood, a ball in étale coordinates inside an affine chart,
on all of whose singular `1`-simplices such a cocycle vanishes: the straight segments of the ball
are `C¹` chart simplices, since regular functions are analytic in étale coordinates. -/
theorem exists_nhds_forall_eq_zero {n : ℕ} {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    {ψ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1 → ℂ} (hψ : coboundary ℂ 1 ψ = 0)
    (h0 : ∀ (U : X.affineOpens) (σ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1)
      (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U : X.Opens)),
      IsC1Path (simplexPath (U : X.Opens) σ hσ) → ψ σ = 0)
    (x : Analytification.space (X ↘ Spec (.of ℂ))) :
    ∃ B : Set (Analytification.space (X ↘ Spec (.of ℂ))), IsOpen B ∧ x ∈ B ∧
      ∀ σ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1, Set.range σ ⊆ B → ψ σ = 0 := by
  obtain ⟨c, hxc⟩ :=
    ComplexPoints.EtaleCoordinateChart.exists_mem_W (sX := X ↘ Spec (.of ℂ)) (n := n) x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x.toScheme) isOpen_univ
  set e := c.toOpenPartialHomeomorph
  have hsrc : e.source = c.W := c.source_toOpenPartialHomeomorph
  have hxe : x ∈ e.source := hsrc ▸ hxc
  set S := e.target ∩ e.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V
  have hSo : IsOpen S := e.isOpen_inter_preimage_symm (ComplexPoints.isOpen_chart _ V)
  have hxS : e x ∈ S :=
    ⟨e.map_source hxe, by
      rw [Set.mem_preimage, e.left_inv hxe]
      exact ComplexPoints.mem_chart_iff.2 hxV⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo (e x) hxS
  have hD : Convex ℝ (Metric.ball (e x) r) := convex_ball _ _
  have hDt : Metric.ball (e x) r ⊆ e.target := fun v hv ↦ (hball hv).1
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r, e.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hxe, Metric.mem_ball_self hr⟩, fun σ hσ ↦ ?_⟩
  refine eq_zero_of_forall_segSimplex (Y := Analytification.space (X ↘ Spec (.of ℂ))) e hD hDt
    hψ (fun a b ha hb ↦ ?_) σ (fun s ↦ hσ ⟨s, rfl⟩)
  have hLD : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → (1 - t) • a + t • b ∈ Metric.ball (e x) r :=
    fun t ht ↦ segment_mem hD ha hb ht.1 ht.2
  have hmem : ∀ s, segSimplex (Y := Analytification.space (X ↘ Spec (.of ℂ))) e hD hDt ha hb s ∈
      ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) ((⟨V, hV⟩ : X.affineOpens) : X.Opens) :=
    fun s ↦ (hball (segment_mem hD ha hb (stdSimplex_apply_nonneg s 1)
      (by linarith [stdSimplex_apply_nonneg s 0, stdSimplex_two_add s]))).2
  refine h0 ⟨V, hV⟩ _ hmem fun h ↦ ?_
  obtain ⟨G, hG, hGe⟩ := c.exists_analyticOnNhd V h
  have hL : ContDiff ℝ 1 fun t : ℝ ↦ (1 - t) • a + t • b :=
    ((contDiff_const.sub contDiff_id).smul contDiff_const).add (contDiff_id.smul contDiff_const)
  refine ContDiffOn.congr (f := fun t ↦ G ((1 - t) • a + t • b)) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · exact (((hG _ (hball (hLD t ht))).contDiffAt.restrict_scalars ℝ).comp t
      hL.contDiffAt).contDiffWithinAt
  · simp only [simplexPath, segSimplex, ContinuousMap.coe_mk, symm_projIcc_apply_one ht]
    have hv := hDt (hLD t ht)
    rw [hGe _ (c.toOpenPartialHomeomorph_symm_mem hv), e.right_inv hv]

/-- **Gluing local functions with locally constant differences into a cocycle.** If every point
`y` of `Y` has an open neighbourhood `B y` with a function `F y`, and `F y₁ - F y₂` is locally
constant on `B y₁ ∩ B y₂`, there is a `1`-cocycle whose value on every simplex in some `B y` is
the increment of `F y` between its vertices: the increments form a cocycle on small simplices,
transported to all simplices by the small-chains map. -/
theorem exists_cocycle_of_eventually_sub_eq {Y : TopCat.{0}} (B : Y → Set Y)
    (F : Y → Y → ℂ) (hBo : ∀ y, IsOpen (B y)) (hmem : ∀ y, y ∈ B y)
    (hcomp : ∀ y₁ y₂, ∀ w ∈ B y₁ ∩ B y₂, ∀ᶠ z in nhds w, F y₁ z - F y₂ z = F y₁ w - F y₂ w) :
    ∃ (φ : Simplex Y 1 → ℂ) (_ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) 1),
      ∀ (σ : Simplex Y 1) (y : Y), Set.range σ ⊆ B y →
        φ σ = F y (σ (stdSimplex.vertex 1)) - F y (σ (stdSimplex.vertex 0)) := by
  classical
  have hsub : ∀ {k : ℕ} (τ : Simplex Y k) (y₁ y₂ : Y), Set.range τ ⊆ B y₁ ∩ B y₂ →
      ∀ i j : Fin (k + 1), F y₁ (τ (stdSimplex.vertex i)) - F y₂ (τ (stdSimplex.vertex i)) =
        F y₁ (τ (stdSimplex.vertex j)) - F y₂ (τ (stdSimplex.vertex j)) := by
    intro k τ y₁ y₂ hτ i j
    have hlc : IsLocallyConstant fun t ↦ F y₁ (τ t) - F y₂ (τ t) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
      exact (τ.continuous.tendsto t).eventually (hcomp y₁ y₂ (τ t) (hτ ⟨t, rfl⟩))
    exact hlc.apply_eq_of_preconnectedSpace _ _
  let 𝒰 : Set (Set Y) := Set.range B
  have h𝒰 : ∀ U ∈ 𝒰, IsOpen U := by rintro _ ⟨y, rfl⟩; exact hBo y
  let φ₀ : Simplex Y 1 → ℂ := fun σ ↦
    if h : ∃ y, Set.range σ ⊆ B y then
      F h.choose (σ (stdSimplex.vertex 1)) - F h.choose (σ (stdSimplex.vertex 0)) else 0
  have hφ₀ : ∀ (σ : Simplex Y 1) (y : Y), Set.range σ ⊆ B y →
      φ₀ σ = F y (σ (stdSimplex.vertex 1)) - F y (σ (stdSimplex.vertex 0)) := by
    intro σ y hσ
    have h : ∃ y, Set.range σ ⊆ B y := ⟨y, hσ⟩
    simp only [φ₀, dif_pos h]
    have := hsub σ h.choose y (Set.subset_inter h.choose_spec hσ) 1 0
    linear_combination this
  let φ := SingularCochain.pullback (smallChainMap ℂ 𝒰 1) φ₀
  have hfix : ∀ (σ : Simplex Y 1) (y : Y), Set.range σ ⊆ B y → φ σ = φ₀ σ := by
    intro σ y hσ
    have := smallChainMap_single_of_subset (R := ℂ) (𝒰 := 𝒰) ⟨B y, ⟨y, rfl⟩, hσ⟩
    simp [φ, SingularCochain.pullback, this]
  have hcov : ∀ {k : ℕ} (σ : Simplex Y k), Set.range σ ⊆ ⋃₀ 𝒰 := fun σ x _ ↦
    ⟨B x, ⟨x, rfl⟩, hmem x⟩
  have hδ : coboundary ℂ 1 φ = 0 := by
    rw [coboundary_pullback_smallChainMap]
    funext T
    have hs := smallChainMap_single_mem_small (R := ℂ) h𝒰 2 (hcov T)
    rw [Finsupp.mem_supported] at hs
    change SingularCochain.eval (coboundary ℂ 1 φ₀) (smallChainMap ℂ 𝒰 2 (Finsupp.single T 1)) = 0
    rw [SingularCochain.eval, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun T' hT' ↦ ?_
    obtain ⟨_, ⟨y, rfl⟩, hT'B⟩ := hs hT'
    have hface : ∀ k : Fin 3, Set.range (T'.comp (face 1 k)) ⊆ B y :=
      fun k _ ⟨t, ht⟩ ↦ hT'B ⟨_, ht⟩
    rw [coboundary_apply, Fin.sum_univ_three, hφ₀ _ y (hface 0), hφ₀ _ y (hface 1),
      hφ₀ _ y (hface 2)]
    simp only [ContinuousMap.comp_apply, face_vertex]
    have h0 : (0 : Fin 3).succAbove 0 = 1 := rfl
    have h1 : (0 : Fin 3).succAbove 1 = 2 := rfl
    have h2 : (1 : Fin 3).succAbove 0 = 0 := rfl
    have h3 : (1 : Fin 3).succAbove 1 = 2 := rfl
    have h4 : (2 : Fin 3).succAbove 0 = 0 := rfl
    have h5 : (2 : Fin 3).succAbove 1 = 1 := rfl
    simp only [h0, h1, h2, h3, h4, h5]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_mul,
      neg_one_mul, smul_eq_mul]
    ring
  exact ⟨φ, ⟨fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
    LinearMap.mem_ker.2 hδ⟩, fun σ y hσ ↦ (hfix σ y hσ).trans (hφ₀ σ y hσ)⟩

/-- The point of `Δ¹` with coordinate `r` at vertex `1`, clamping `r` to `[0, 1]`. -/
noncomputable abbrev ptI (r : ℝ) : stdSimplex ℝ (Fin 2) :=
  stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one r)

/-- `ptI` is continuous. -/
theorem continuous_ptI : Continuous ptI :=
  stdSimplexHomeomorphUnitInterval.symm.continuous.comp continuous_projIcc

/-- A point of `Δ¹` is `ptI` of its coordinate at vertex `1`. -/
theorem ptI_apply_one (x : stdSimplex ℝ (Fin 2)) : ptI (x 1) = x := by
  have hx : Set.projIcc (0 : ℝ) 1 zero_le_one (x 1) = stdSimplexHomeomorphUnitInterval x :=
    Set.projIcc_of_mem _ ⟨stdSimplex_apply_nonneg x 1,
      by linarith [stdSimplex_apply_nonneg x 0, stdSimplex_two_add x]⟩
  simp only [ptI, hx, Homeomorph.symm_apply_apply]

/-- The restriction `x ↦ σ((1 - x₁) a + x₁ b)` of a singular `1`-simplex `σ`, read as a path on
`[0, 1]`, to the interval from `a` to `b`. -/
noncomputable def subSimplex {Y : TopCat.{0}} (σ : Simplex Y 1) (a b : ℝ) : Simplex Y 1 :=
  ⟨fun x ↦ σ (ptI ((1 - x 1) * a + x 1 * b)), σ.continuous.comp (continuous_ptI.comp
    (((continuous_const.sub (stdSimplex_continuous_apply 1)).mul continuous_const).add
      ((stdSimplex_continuous_apply 1).mul continuous_const)))⟩

/-- The value of `subSimplex σ a b` at `x` is `σ (ptI ((1 - x₁) a + x₁ b))`. -/
theorem subSimplex_apply {Y : TopCat.{0}} (σ : Simplex Y 1) (a b : ℝ)
    (x : stdSimplex ℝ (Fin 2)) : subSimplex σ a b x = σ (ptI ((1 - x 1) * a + x 1 * b)) := rfl

/-- The restriction of `σ` to the interval from `0` to `1` is `σ`. -/
theorem subSimplex_zero_one {Y : TopCat.{0}} (σ : Simplex Y 1) : subSimplex σ 0 1 = σ := by
  ext x
  rw [subSimplex_apply, mul_zero, zero_add, mul_one, ptI_apply_one]

/-- **A cocycle is additive under subdivision of a path.** The degenerate `2`-simplex
`t ↦ σ(t₀ a + t₁ s + t₂ b)` has faces the restrictions of `σ` to `[s, b]`, `[a, b]`, `[a, s]`. -/
theorem subSimplex_add {Y : TopCat.{0}} {φ : Simplex Y 1 → ℂ} (hφ : coboundary ℂ 1 φ = 0)
    (σ : Simplex Y 1) (a s b : ℝ) :
    φ (subSimplex σ a b) = φ (subSimplex σ a s) + φ (subSimplex σ s b) := by
  have hx1 := stdSimplex_two_add
  let T : Simplex Y 2 := ⟨fun t ↦ σ (ptI ((1 - t 1 - t 2) * a + t 1 * s + t 2 * b)),
    σ.continuous.comp (continuous_ptI.comp
      ((((continuous_const.sub (stdSimplex_continuous_apply 1)).sub
        (stdSimplex_continuous_apply 2)).mul continuous_const).add
        ((stdSimplex_continuous_apply 1).mul continuous_const) |>.add
        ((stdSimplex_continuous_apply 2).mul continuous_const)))⟩
  have hf : ∀ (k : Fin 3) (x : stdSimplex ℝ (Fin 2)), T.comp (face 1 k) x = T (face 1 k x) :=
    fun _ _ ↦ rfl
  have e0 : T.comp (face 1 0) = subSimplex σ s b := by
    ext x
    rw [hf, subSimplex_apply]
    simp only [T, ContinuousMap.coe_mk, face_apply_one, face_apply_two]
    simp only [if_true, show ((0 : Fin 3) = 2) = False from by decide, if_false]
    congr 2
    linear_combination (s - a) * hx1 x
  have e1 : T.comp (face 1 1) = subSimplex σ a b := by
    ext x
    rw [hf, subSimplex_apply]
    simp only [T, ContinuousMap.coe_mk, face_apply_one, face_apply_two]
    simp only [if_true, show ((1 : Fin 3) = 0) = False from by decide,
      show ((1 : Fin 3) = 2) = False from by decide, if_false]
    congr 2
    ring
  have e2 : T.comp (face 1 2) = subSimplex σ a s := by
    ext x
    rw [hf, subSimplex_apply]
    simp only [T, ContinuousMap.coe_mk, face_apply_one, face_apply_two]
    simp only [if_true, show ((2 : Fin 3) = 0) = False from by decide,
      show ((2 : Fin 3) = 1) = False from by decide, if_false]
    congr 2
    ring
  have h := congrFun hφ T
  rw [coboundary_apply, Fin.sum_univ_three] at h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_mul,
    neg_one_mul, Pi.zero_apply, e0, e1, e2] at h
  linear_combination -h

/-- **A cocycle given by integrals on short pieces is the integral.** If a `1`-cocycle takes the
value `∫ₐᵇ I` on the restriction of `σ` to every interval `[a, b] ⊆ [0, 1]` of length `< δ`,
then its value on `σ` is `∫₀¹ I`: cut `[0, 1]` into intervals of length `< δ`. -/
theorem eq_integral_of_forall_subSimplex {Y : TopCat.{0}} {φ : Simplex Y 1 → ℂ}
    (hφ : coboundary ℂ 1 φ = 0) (σ : Simplex Y 1) {I : ℝ → ℂ}
    (hI : IntervalIntegrable I MeasureTheory.volume 0 1) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → b - a < δ →
      φ (subSimplex σ a b) = ∫ t in a..b, I t) :
    φ σ = ∫ t in (0 : ℝ)..1, I t := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set M : ℝ := (n : ℝ) + 1
  have hM : 0 < M := by positivity
  have hmem : ∀ k : ℕ, k ≤ n + 1 → (k : ℝ) / M ∈ Set.uIcc (0 : ℝ) 1 := fun k hk ↦ by
    rw [Set.uIcc_of_le zero_le_one]
    refine ⟨by positivity, (div_le_one hM).2 ?_⟩
    simp only [M]
    exact_mod_cast hk
  have key : ∀ k : ℕ, k ≤ n + 1 →
      φ (subSimplex σ 0 ((k : ℝ) / M)) = ∫ t in (0 : ℝ)..(k : ℝ) / M, I t := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using h 0 0 le_rfl le_rfl zero_le_one (by simpa using hδ)
    | succ k ih =>
      intro hk
      have hk' : k ≤ n + 1 := by omega
      rw [subSimplex_add hφ σ 0 ((k : ℝ) / M), ih hk', h _ _ (by positivity)
        (div_le_div_of_nonneg_right (by push_cast; linarith) hM.le)
        (by have := hmem _ hk; rw [Set.uIcc_of_le zero_le_one] at this; exact this.2)
        (by rw [← sub_div]; push_cast; rw [add_sub_cancel_left]; exact hn),
        intervalIntegral.integral_add_adjacent_intervals]
      · exact hI.mono_set (Set.uIcc_subset_uIcc (by simp) (hmem _ hk'))
      · exact hI.mono_set (Set.uIcc_subset_uIcc (hmem _ hk') (hmem _ hk))
  have := key (n + 1) le_rfl
  rwa [show ((n + 1 : ℕ) : ℝ) / M = 1 by simp only [M]; push_cast; exact div_self hM.ne',
    subSimplex_zero_one] at this

end Small

section Gluing

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

set_option maxRecDepth 8000 in
/-- **Gluing local primitives into a de Rham class.** If every point `y` of `X^an` has an open
neighbourhood `B y` carrying a local primitive `F y` of `ω`, the increments of the `F y` glue to
a cocycle whose class is a de Rham class of `ω`: on a `C¹` chart simplex, cut into pieces each
lying in some `B y`, it is the line integral by the fundamental theorem of calculus. -/
theorem isDR_of_isLocalPrimitive {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (B : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))))
    (F : ComplexPoints (X ↘ Spec (.of ℂ)) → ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ)
    (hBo : ∀ y, IsOpen (B y)) (hmem : ∀ y, y ∈ B y) (hprim : ∀ y, IsLocalPrimitive ω (B y) (F y)) :
    ∃ (φ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1 → ℂ)
      (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) 1),
      IsDR X ω (cohomologyWithSupports.ofCocycle ℂ _ 1 φ hφ) ∧
      ∀ (σ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1) (y : ComplexPoints _),
        Set.range σ ⊆ B y →
          φ σ = F y (σ (stdSimplex.vertex 1)) - F y (σ (stdSimplex.vertex 0)) := by
  obtain ⟨φ, hφ, hval⟩ := exists_cocycle_of_eventually_sub_eq
    (Y := Analytification.space (X ↘ Spec (.of ℂ))) B F hBo hmem
    (fun y₁ y₂ w hw ↦ eventually_sub_eq_of_isLocalPrimitive (n := n) ω (hBo y₁) (hBo y₂) (hprim y₁)
      (hprim y₂) hw)
  refine ⟨φ, hφ, ⟨φ, hφ, rfl, ?_⟩, hval⟩
  intro U m f g hrep σ hσ hC
  let q : ℝ → Analytification.space (X ↘ Spec (.of ℂ)) := fun t ↦ σ (ptI t)
  have hq : Continuous q := σ.continuous.comp continuous_ptI
  have hqU : ∀ t, q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U : X.Opens) :=
    fun t ↦ hσ _
  have hev : ∀ h : Γ(X, U), (fun t ↦ evalT (U : X.Opens) h (q t)) =
      fun t ↦ ComplexPoints.eval (U : X.Opens) h (simplexPath (U : X.Opens) σ hσ t) :=
    fun h ↦ funext fun t ↦ by rw [evalT_of_mem _ (hqU t), ComplexPoints.evalHom_apply]
  set I : ℝ → ℂ := fun t ↦ ∑ j, evalT (U : X.Opens) (f j) (q t) *
    deriv (fun s ↦ evalT (U : X.Opens) (g j) (q s)) t with hIdef
  have hI : I = fun t ↦ ∑ j, ComplexPoints.eval (U : X.Opens) (f j)
      (simplexPath (U : X.Opens) σ hσ t) *
      deriv (fun s ↦
        ComplexPoints.eval (U : X.Opens) (g j) (simplexPath (U : X.Opens) σ hσ s)) t := by
    funext t
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hev (g j)]
    exact congrArg (· * _) (congrFun (hev (f j)) t)
  have hIint : IntervalIntegrable I MeasureTheory.volume 0 1 := by
    rw [hI]; exact intervalIntegrable_lineInt hC f g
  have hdiff : ∀ h' : Γ(X, U), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t ↦ evalT (U : X.Opens) h' (q t)) t := fun h' t ht ↦ by
    rw [hev]
    exact ((hC h').differentiableOn one_ne_zero t (Set.Ioo_subset_Icc_self ht)).differentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := Set.Icc (0 : ℝ) 1)
    (c := fun y ↦ q ⁻¹' B y) isCompact_Icc (fun y ↦ (hBo y).preimage hq)
    (fun t _ ↦ Set.mem_iUnion.2 ⟨q t, hmem (q t)⟩)
  change φ σ = lineInt _ f g
  rw [lineInt, ← hI]
  refine eq_integral_of_forall_subSimplex (LinearMap.mem_ker.1 hφ.2) σ hIint hδ ?_
  intro a b ha hab hb hlen
  obtain ⟨y, hy⟩ := hleb a ⟨ha, hab.trans hb⟩
  have hqB : ∀ t ∈ Set.Icc a b, q t ∈ B y := fun t ht ↦
    hy (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  have hrange : Set.range (subSimplex σ a b) ⊆ B y := by
    rintro _ ⟨x, rfl⟩
    have h0 := stdSimplex_apply_nonneg x 1
    have h1 : x 1 ≤ 1 := by linarith [stdSimplex_apply_nonneg x 0, stdSimplex_two_add x]
    refine hqB _ ⟨?_, ?_⟩ <;> nlinarith
  have hv1 : (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 1 = 1 := by
    simp [stdSimplex.vertex_coe]
  have hv0 : (stdSimplex.vertex (S := ℝ) (0 : Fin 2) : stdSimplex ℝ (Fin 2)) 1 = 0 := by
    simp [stdSimplex.vertex_coe]
  rw [hval _ y hrange, subSimplex_apply, subSimplex_apply, hv1, hv0]
  simp only [sub_self, one_mul, zero_mul, add_zero, sub_zero, mul_one, zero_add]
  exact hprim y U f g hrep q hq hab hqB (fun t _ ↦ hqU t)
    (fun h' t ht ↦ hdiff h' t ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)
    (hIint.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le zero_le_one]; exact ⟨ha, hab.trans hb⟩)
      (by rw [Set.uIcc_of_le zero_le_one]; exact ⟨ha.trans hab, hb⟩)))

/-- A ball in étale coordinates around `x` whose points lie in an affine chart and in a given
open set `N ∋ x`. -/
theorem exists_chartBall {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    {N : Set (ComplexPoints (X ↘ Spec (.of ℂ)))} (hN : IsOpen N)
    {x : ComplexPoints (X ↘ Spec (.of ℂ))} (hx : x ∈ N) :
    ∃ (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (V : X.affineOpens) (r : ℝ),
      0 < r ∧ x ∈ c.toOpenPartialHomeomorph.source ∧
      Metric.ball (c.toOpenPartialHomeomorph x) r ⊆ c.toOpenPartialHomeomorph.target ∩
        c.toOpenPartialHomeomorph.symm ⁻¹'
          (ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens) ∩ N) := by
  obtain ⟨c, hxc⟩ := ComplexPoints.EtaleCoordinateChart.exists_mem_W (sX := X ↘ Spec (.of ℂ))
    (n := n) x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x.toScheme) isOpen_univ
  have hsrc : c.toOpenPartialHomeomorph.source = c.W := c.source_toOpenPartialHomeomorph
  have hxe : x ∈ c.toOpenPartialHomeomorph.source := hsrc ▸ hxc
  have hSo := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm
    ((ComplexPoints.isOpen_chart (X ↘ Spec (.of ℂ)) V).inter hN)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo (c.toOpenPartialHomeomorph x)
    ⟨c.toOpenPartialHomeomorph.map_source hxe, by
      rw [Set.mem_preimage, c.toOpenPartialHomeomorph.left_inv hxe]
      exact ⟨ComplexPoints.mem_chart_iff.2 hxV, hx⟩⟩
  exact ⟨c, ⟨V, hV⟩, r, hr, hxe, hball⟩

/-- Étale coordinates are differentiable along a path along which the regular functions of an
affine chart are differentiable. -/
theorem hasDerivAt_chart_comp {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (U : X.affineOpens)
    {q : ℝ → ComplexPoints (X ↘ Spec (.of ℂ))} {t : ℝ} (hq : ContinuousAt q t) (hW : q t ∈ c.W)
    (hU : q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U : X.Opens))
    (hC : ∀ h : Γ(X, U), DifferentiableAt ℝ (fun t ↦ evalT (U : X.Opens) h (q t)) t) :
    HasDerivAt (fun t' ↦ c.toOpenPartialHomeomorph (q t'))
      (deriv (fun t' ↦ c.toOpenPartialHomeomorph (q t')) t) t := by
  have hcU : q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) c.U := c.subset hW
  have hcoord : DifferentiableAt ℝ (fun t' ↦ fun i ↦ evalT c.U (c.z i) (q t')) t :=
    differentiableAt_pi.2 fun i ↦ differentiableAt_evalT_comp U c.U hq hU hcU hC (c.z i)
  have heq : (fun t' ↦ c.toOpenPartialHomeomorph (q t')) =ᶠ[nhds t]
      fun t' ↦ fun i ↦ evalT c.U (c.z i) (q t') := by
    have hWo : IsOpen c.W := c.isOpen
    filter_upwards [hq.preimage_mem_nhds (hWo.mem_nhds hW)] with t' ht'
    funext i
    rw [c.toOpenPartialHomeomorph_apply ht' i, evalT_of_mem _ (c.subset ht'),
      ComplexPoints.evalHom_apply]
  have := hcoord.hasDerivAt
  rw [← heq.deriv_eq] at this
  exact this.congr_of_eventuallyEq heq

set_option maxRecDepth 8000 in
/-- **A primitive in étale coordinates is a local primitive.** If `Φ` is, on an open set `D` of
étale coordinates over an affine chart `V`, a primitive of the coordinate expression of a
presentation of `ω|_V`, then `Φ ∘ e` is a local primitive of `ω` on `e⁻¹ D`. -/
theorem isLocalPrimitive_comp {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (V : X.affineOpens)
    {D : Set (Fin n → ℂ)} (hD : D ⊆ c.toOpenPartialHomeomorph.target ∩
      c.toOpenPartialHomeomorph.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens))
    {m₀ : ℕ} (f₀ g₀ : Fin m₀ → Γ(X, V))
    (h₀ : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (V : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 V
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f₀ j • exteriorPower.ιMulti Γ(X, V) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, V) (g₀ j)))
    {Φ : (Fin n → ℂ) → ℂ}
    (hΦ : ∀ z ∈ D, HasFDerivAt Φ
      (∑ j, evalT (V : X.Opens) (f₀ j) (c.toOpenPartialHomeomorph.symm z) •
      fderiv ℝ (fun w ↦ evalT (V : X.Opens) (g₀ j) (c.toOpenPartialHomeomorph.symm w)) z) z) :
    IsLocalPrimitive ω (c.toOpenPartialHomeomorph.source ∩ c.toOpenPartialHomeomorph ⁻¹' D)
      (fun y ↦ Φ (c.toOpenPartialHomeomorph y)) := by
  set e := c.toOpenPartialHomeomorph
  have hHd : ∀ (h : Γ(X, V)), ∀ z ∈ D,
      DifferentiableAt ℝ (fun w ↦ evalT (V : X.Opens) h (e.symm w)) z := fun h z hz ↦
    ((analyticAt_evalT_symm c V h (hD hz)).differentiableAt).restrictScalars ℝ
  intro U m f g hrep q hq a b hab hqB hqU hC hint
  have hqV : ∀ t ∈ Set.Icc a b, q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V :=
    fun t ht ↦ by
      have := (hD (hqB t ht).2).2
      rwa [Set.mem_preimage, e.left_inv (hqB t ht).1] at this
  show Φ (e (q b)) - Φ (e (q a)) = _
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t ↦ Φ (e (q t))) hab ?_
    (fun t ht ↦ ?_) hint).symm
  · refine ContinuousOn.comp (g := Φ) (fun z hz ↦ (hΦ z hz).continuousAt.continuousWithinAt)
      ?_ (fun t ht ↦ (hqB t ht).2)
    exact e.continuousOn.comp hq.continuousOn fun t ht ↦ (hqB t ht).1
  · have htI : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
    have hW : q t ∈ c.W := c.source_toOpenPartialHomeomorph ▸ (hqB t htI).1
    have hw := hasDerivAt_chart_comp c U hq.continuousAt hW (hqU t htI) fun h' ↦ hC h' t ht
    have hzD : e (q t) ∈ D := (hqB t htI).2
    have hchain := (hΦ (e (q t)) hzD).comp_hasDerivAt t hw
    refine hchain.congr_deriv ?_
    beta_reduce
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hterm : ∀ j, evalT (V : X.Opens) (f₀ j) (e.symm (e (q t))) *
        fderiv ℝ (fun w ↦ evalT (V : X.Opens) (g₀ j) (e.symm w)) (e (q t))
          (deriv (fun t' ↦ e (q t')) t) =
        evalT (V : X.Opens) (f₀ j) (q t) * deriv (fun s ↦ evalT (V : X.Opens) (g₀ j) (q s)) t := by
      intro j
      have hHq : evalT (V : X.Opens) (f₀ j) (e.symm (e (q t))) = evalT (V : X.Opens) (f₀ j) (q t) :=
        by rw [e.left_inv (hqB t htI).1]
      have hg := ((hHd (g₀ j) _ hzD).hasFDerivAt.comp_hasDerivAt t hw).deriv
      have hgq : (fun s ↦ evalT (V : X.Opens) (g₀ j) (e.symm (e (q s)))) =ᶠ[nhds t]
          fun s ↦ evalT (V : X.Opens) (g₀ j) (q s) := by
        filter_upwards [hq.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds
          (hqB t htI).1)] with s hs
        rw [e.left_inv hs]
      rw [hHq, ← hg]
      exact congrArg _ hgq.deriv_eq
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j]
    exact (sum_evalT_mul_deriv_congr ω f g f₀ g₀ hrep h₀ hq.continuousAt (hqU t htI)
      (hqV t htI) fun h' ↦ hC h' t ht).symm

set_option maxRecDepth 8000 in
/-- **Closedness in étale coordinates.** If `ω` is closed and `ω|_V = ∑ fⱼ dgⱼ`, then in étale
coordinates `∑ⱼ dfⱼ ∧ dgⱼ` vanishes on every pair of tangent vectors. -/
theorem sum_fderiv_antisymm_chart {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (hd : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) ω = 0)
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (V : X.affineOpens)
    {m₀ : ℕ} (f₀ g₀ : Fin m₀ → Γ(X, V))
    (h₀ : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (V : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 V
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f₀ j • exteriorPower.ιMulti Γ(X, V) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, V) (g₀ j)))
    {z : Fin n → ℂ} (hz : z ∈ c.toOpenPartialHomeomorph.target ∩
      c.toOpenPartialHomeomorph.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens))
    (u v : Fin n → ℂ) :
    ∑ j, (fderiv ℝ (fun w ↦ evalT (V : X.Opens) (f₀ j) (c.toOpenPartialHomeomorph.symm w)) z u *
      fderiv ℝ (fun w ↦ evalT (V : X.Opens) (g₀ j) (c.toOpenPartialHomeomorph.symm w)) z v -
      fderiv ℝ (fun w ↦ evalT (V : X.Opens) (f₀ j) (c.toOpenPartialHomeomorph.symm w)) z v *
      fderiv ℝ (fun w ↦ evalT (V : X.Opens) (g₀ j) (c.toOpenPartialHomeomorph.symm w)) z u) =
        0 := by
  set e := c.toOpenPartialHomeomorph
  let H : Γ(X, V) → (Fin n → ℂ) → ℂ := fun h w ↦ evalT (V : X.Opens) h (e.symm w)
  have hHd : ∀ h, DifferentiableAt ℝ (H h) z := fun h ↦
    ((analyticAt_evalT_symm c V h hz).differentiableAt).restrictScalars ℝ
  have hclosed := sum_ιMulti_two_eq_zero_of_rep ω hd V f₀ g₀ h₀
  have hzV : e.symm z ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens) := hz.2
  letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (V : X.Opens)
  let ev := ComplexPoints.evalHom (V : X.Opens) ⟨e.symm z, hzV⟩
  have hev : ∀ c, ev (algebraMap ℂ Γ(X, V) c) = c := fun c ↦
    ComplexPoints.evalHom_baseRingHom _ _ c
  have hevH : ∀ a, ev a = H a z := fun a ↦ (evalT_of_mem a hzV).symm
  have hadd : ∀ (w : Fin n → ℂ) (a b : Γ(X, V)),
      fderiv ℝ (H (a + b)) z w = fderiv ℝ (H a) z w + fderiv ℝ (H b) z w := fun w a b ↦ by
    have : H (a + b) = fun w ↦ H a w + H b w := funext fun w ↦ evalT_add _ _ _
    rw [this, fderiv_fun_add (hHd a) (hHd b)]
    rfl
  have hsmul : ∀ (w : Fin n → ℂ) (c : ℂ) (a : Γ(X, V)),
      fderiv ℝ (H (algebraMap ℂ Γ(X, V) c * a)) z w = c * fderiv ℝ (H a) z w := fun w c a ↦ by
    have : H (algebraMap ℂ Γ(X, V) c * a) = fun w ↦ c * H a w :=
      funext fun w ↦ evalT_baseRingHom_mul c a _
    rw [this, fderiv_const_mul (hHd a)]
    rfl
  have hmul : ∀ (w : Fin n → ℂ) (a b : Γ(X, V)),
      fderiv ℝ (H (a * b)) z w = ev a * fderiv ℝ (H b) z w + ev b * fderiv ℝ (H a) z w :=
    fun w a b ↦ by
      have : H (a * b) = fun w ↦ H a w * H b w := funext fun w ↦ evalT_mul _ _ _
      rw [this, fderiv_fun_mul (hHd a) (hHd b), hevH, hevH]
      simp [smul_eq_mul]
  exact sum_derivation_antisymm ev hev (fun h ↦ fderiv ℝ (H h) z u)
    (fun h ↦ fderiv ℝ (H h) z v) (hadd u) (hsmul u) (hmul u) (hadd v) (hsmul v) (hmul v)
    f₀ g₀ hclosed

/-- **Gluing local cochains which agree on overlaps.** -/
theorem exists_cochain_of_forall_eq {Y : TopCat.{0}} {k : ℕ} (B : Y → Set Y)
    (θ : Y → Simplex Y k → ℂ)
    (h : ∀ (τ : Simplex Y k) (y₁ y₂ : Y), Set.range τ ⊆ B y₁ → Set.range τ ⊆ B y₂ →
      θ y₁ τ = θ y₂ τ) :
    ∃ Θ : Simplex Y k → ℂ, ∀ (τ : Simplex Y k) (y : Y), Set.range τ ⊆ B y → Θ τ = θ y τ := by
  classical
  refine ⟨fun τ ↦ if hτ : ∃ y, Set.range τ ⊆ B y then θ hτ.choose τ else 0, fun τ y hτ ↦ ?_⟩
  have hτ' : ∃ y, Set.range τ ⊆ B y := ⟨y, hτ⟩
  simp only [dif_pos hτ']
  exact h τ _ _ hτ'.choose_spec hτ

/-- A locally constant function on a set takes the same value at all vertices of a simplex lying
in that set. -/
theorem apply_vertex_eq_of_eventually {Y : TopCat.{0}} {k : ℕ} (τ : Simplex Y k)
    {f : Y → ℂ} {A : Set Y} (hτ : Set.range τ ⊆ A) (hf : ∀ w ∈ A, ∀ᶠ z in nhds w, f z = f w)
    (i j : Fin (k + 1)) : f (τ (stdSimplex.vertex i)) = f (τ (stdSimplex.vertex j)) := by
  have hlc : IsLocallyConstant fun t ↦ f (τ t) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦
      (τ.continuous.tendsto t).eventually (hf (τ t) (hτ ⟨t, rfl⟩))
  exact hlc.apply_eq_of_preconnectedSpace _ _

end Gluing

section TopDegree

/-- **`H_0` of a compact path-connected space is spanned by one class**, the class of a point:
a `0`-chain differs from its augmentation times a point by the boundary of a sum of paths. The
degree is any `i` equal to `0`, so that it can be read off a difference of degrees. -/
theorem exists_forall_smul_eq_borelMooreHomology_zero {R : Type} [CommRing R]
    (Y : TopCat.{0}) [CompactSpace Y] [PathConnectedSpace Y] (i : ℤ) (hi : i = 0) :
    ∃ v : borelMooreHomology R (ModuleCat.of R R) Y i, ∀ a, ∃ r : R, r • v = a := by
  subst hi
  set C := borelMooreChainComplex R (ModuleCat.of R R) Y
  set ι := borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y 0
  obtain ⟨p⟩ := (inferInstance : Nonempty Y)
  haveI : IsIso (C.iCycles 0) := C.isIso_iCycles 0 0 (by simp) (by simp)
  let cyc : C.X 0 → C.cycles 0 := fun x ↦ (inv (C.iCycles 0)) x
  have hcyc : ∀ x, C.iCycles 0 (cyc x) = x := fun x ↦ by
    simp only [cyc]
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  set σ₀ : Simplex Y 0 := ContinuousMap.const _ p
  set v₀ : C.X 0 := borelMooreHomology.ofFinsupp (Finsupp.single σ₀ (1 : R))
  refine ⟨ι.inv (C.homologyπ 0 (cyc v₀)), fun a ↦ ?_⟩
  have hsurjπ := (ModuleCat.epi_iff_surjective (C.homologyπ 0)).1 inferInstance
  obtain ⟨z, hz⟩ := hsurjπ (ι.hom a)
  set x := C.iCycles 0 z
  have hfin : (Function.support x.1).Finite := by
    have := x.2.finite_inter_compact (isCompact_univ (X := Y))
    refine this.subset fun σ hσ ↦ ⟨hσ, ?_⟩
    obtain ⟨y, hy⟩ := MMP.nonempty_singularSimplexImage σ
    exact ⟨y, hy, Set.mem_univ _⟩
  set f := borelMooreHomology.toFinsupp x hfin
  set r := aug R 0 f
  refine ⟨r, ?_⟩
  obtain ⟨w, -, hw⟩ := reducedZeroVanishing_of_joinedIn (R := R) (A := (Set.univ : Set Y))
    (fun x _ y _ ↦ joinedIn_univ.2 (PathConnectedSpace.joined x y)) (f - Finsupp.single σ₀ r)
    (by simp [inside]) (by rw [map_sub, aug_single, sub_self])
  have hx : x - r • v₀ = (C.d 1 0) (borelMooreHomology.ofFinsupp w) := by
    rw [borelMooreHomology.d_ofFinsupp, hw, borelMooreHomology.ofFinsupp_sub,
      borelMooreHomology.ofFinsupp_toFinsupp,
      show Finsupp.single σ₀ r = r • Finsupp.single σ₀ (1 : R) by rw [Finsupp.smul_single_one]]
    rfl
  have h0 : C.homologyπ 0 (z - r • cyc v₀) = 0 := by
    have he : z - r • cyc v₀ = C.toCycles 1 0 (borelMooreHomology.ofFinsupp w) := by
      apply (ModuleCat.mono_iff_injective (C.iCycles 0)).1 inferInstance
      rwa [map_sub, map_smul, hcyc, ← ConcreteCategory.comp_apply, C.toCycles_i]
    rw [he, ← ConcreteCategory.comp_apply, C.toCycles_comp_homologyπ]
    rfl
  rw [map_sub, sub_eq_zero, map_smul, hz] at h0
  simpa using (congrArg ι.inv h0).symm

end TopDegree

section Decomposition

variable {n : ℕ} {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]

variable (X) in
/-- Conjugation of coefficients on `H¹(X^an; ℂ)`. -/
noncomputable abbrev conjH :
    analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1 →ₛₗ[starRingEnd ℂ]
      analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1 :=
  singularCohomology.mapCoeff (Y := Analytification.space (X ↘ Spec (.of ℂ))) (starRingEnd ℂ) 1

set_option maxRecDepth 8000 in
/-- **Uniqueness of de Rham classes.** A cocycle vanishing on `C¹` chart simplices is a
coboundary, since such simplices carry `H₁`. -/
theorem IsDR.unique (hn : n = 1 ∨ n = 2)
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {α β : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1}
    (hα : IsDR X ω α) (hβ : IsDR X ω β) : α = β := by
  obtain ⟨φ, hφ, rfl, hφi⟩ := hα
  obtain ⟨φ', hφ', rfl, hφi'⟩ := hβ
  rw [← sub_eq_zero, ← ofCocycle_sub hφ hφ']
  refine ofCocycle_eq_zero_of_forall_small (sub_mem hφ hφ') fun x ↦ ?_
  refine exists_nhds_forall_eq_zero (n := n) (LinearMap.mem_ker.1 (sub_mem hφ hφ').2)
    (fun U σ hσ hC ↦ ?_) x
  obtain ⟨m, f, g, h⟩ := exists_rep ω U
  rw [Pi.sub_apply, hφi U m f g h σ hσ hC, hφi' U m f g h σ hσ hC, sub_self]

/-- A function whose real derivative is `∑ⱼ Hfⱼ • d Hgⱼ` with `Hgⱼ` holomorphic is holomorphic:
its real derivative is complex linear. -/
theorem differentiableOn_of_hasFDerivAt_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {D : Set E} {m : ℕ} (Hf Hg : Fin m → E → ℂ)
    (hg : ∀ j, ∀ z ∈ D, AnalyticAt ℂ (Hg j) z) {Φ : E → ℂ}
    (hΦ : ∀ z ∈ D, HasFDerivAt Φ (∑ j, Hf j z • fderiv ℝ (Hg j) z) z) :
    DifferentiableOn ℂ Φ D := fun w hw ↦ by
  have hcoe : ⇑(∑ j, Hf j w • fderiv ℂ (Hg j) w) = ⇑(∑ j, Hf j w • fderiv ℝ (Hg j) w) := by
    ext u
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [(hg j w hw).differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have h : HasFDerivAt Φ (∑ j, Hf j w • fderiv ℂ (Hg j) w) w := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, hcoe]
    exact hasFDerivAt_iff_isLittleO_nhds_zero.1 (hΦ w hw)
  exact h.differentiableAt.differentiableWithinAt

/-- The data of a closed one-form read in an étale coordinate ball `D` around a point: a
presentation `ω|_V = ∑ fⱼ dgⱼ` on an affine chart and a primitive `Φ` of its coordinate
expression on `D`. -/
def IsChartPrimitive
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (D : Set (Fin n → ℂ))
    (Φ : (Fin n → ℂ) → ℂ) : Prop :=
  ∃ (V : X.affineOpens) (m₀ : ℕ) (f₀ g₀ : Fin m₀ → Γ(X, V)),
    (letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (V : X.Opens);
      MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 V
        (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE le_top).op ω) =
        ∑ j, f₀ j • exteriorPower.ιMulti Γ(X, V) 1
          (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, V) (g₀ j))) ∧
    D ⊆ c.toOpenPartialHomeomorph.target ∩ c.toOpenPartialHomeomorph.symm ⁻¹'
      ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens) ∧
    ∀ z ∈ D, HasFDerivAt Φ (∑ j, evalT (V : X.Opens) (f₀ j) (c.toOpenPartialHomeomorph.symm z) •
      fderiv ℝ (fun w ↦ evalT (V : X.Opens) (g₀ j) (c.toOpenPartialHomeomorph.symm w)) z) z

set_option maxRecDepth 8000 in
/-- **Holomorphic primitives of two closed forms in a common étale ball.** -/
theorem exists_chartPrimitive_pair
    (ω η : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (hdω : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) ω = 0)
    (hdη : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) η = 0)
    (x : ComplexPoints (X ↘ Spec (.of ℂ))) :
    ∃ (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (D : Set (Fin n → ℂ))
      (Φ₁ Φ₂ : (Fin n → ℂ) → ℂ),
      x ∈ c.toOpenPartialHomeomorph.source ∧ c.toOpenPartialHomeomorph x ∈ D ∧ IsOpen D ∧
      Convex ℝ D ∧ D ⊆ c.toOpenPartialHomeomorph.target ∧
      DifferentiableOn ℂ Φ₁ D ∧ DifferentiableOn ℂ Φ₂ D ∧
      IsLocalPrimitive ω (c.toOpenPartialHomeomorph.source ∩ c.toOpenPartialHomeomorph ⁻¹' D)
        (fun y ↦ Φ₁ (c.toOpenPartialHomeomorph y)) ∧
      IsLocalPrimitive η (c.toOpenPartialHomeomorph.source ∩ c.toOpenPartialHomeomorph ⁻¹' D)
        (fun y ↦ Φ₂ (c.toOpenPartialHomeomorph y)) ∧
      IsChartPrimitive ω c D Φ₁ := by
  obtain ⟨c, V, r, hr, hxe, hball⟩ := exists_chartBall (n := n) isOpen_univ (Set.mem_univ x)
  set e := c.toOpenPartialHomeomorph
  set D := Metric.ball (e x) r
  have hD : Convex ℝ D := convex_ball _ _
  have hDo : IsOpen D := Metric.isOpen_ball
  have hDV : D ⊆ e.target ∩
      e.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens) :=
    fun z hz ↦ ⟨(hball hz).1, (hball hz).2.1⟩
  have hH : ∀ h : Γ(X, V), ∀ z ∈ D, AnalyticAt ℂ (fun w ↦ evalT (V : X.Opens) h (e.symm w)) z :=
    fun h z hz ↦ analyticAt_evalT_symm c V h (hDV hz)
  obtain ⟨m₁, f₁, g₁, h₁⟩ := exists_rep ω V
  obtain ⟨m₂, f₂, g₂, h₂⟩ := exists_rep η V
  obtain ⟨Φ₁, hΦ₁⟩ := exists_hasFDerivAt_sum_smul_fderiv hD hDo
    (fun j w ↦ evalT (V : X.Opens) (f₁ j) (e.symm w))
    (fun j w ↦ evalT (V : X.Opens) (g₁ j) (e.symm w)) (fun j ↦ hH (f₁ j)) (fun j ↦ hH (g₁ j))
    (fun z hz u v ↦ sum_fderiv_antisymm_chart ω hdω c V f₁ g₁ h₁ (hDV hz) u v)
  obtain ⟨Φ₂, hΦ₂⟩ := exists_hasFDerivAt_sum_smul_fderiv hD hDo
    (fun j w ↦ evalT (V : X.Opens) (f₂ j) (e.symm w))
    (fun j w ↦ evalT (V : X.Opens) (g₂ j) (e.symm w)) (fun j ↦ hH (f₂ j)) (fun j ↦ hH (g₂ j))
    (fun z hz u v ↦ sum_fderiv_antisymm_chart η hdη c V f₂ g₂ h₂ (hDV hz) u v)
  exact ⟨c, D, Φ₁, Φ₂, hxe, Metric.mem_ball_self hr, hDo, hD, fun z hz ↦ (hDV hz).1,
    differentiableOn_of_hasFDerivAt_sum _ _ (fun j ↦ hH (g₁ j)) hΦ₁,
    differentiableOn_of_hasFDerivAt_sum _ _ (fun j ↦ hH (g₂ j)) hΦ₂,
    isLocalPrimitive_comp ω c V hDV f₁ g₁ h₁ hΦ₁, isLocalPrimitive_comp η c V hDV f₂ g₂ h₂ hΦ₂,
    V, m₁, f₁, g₁, h₁, hDV, hΦ₁⟩

set_option maxRecDepth 8000 in
/-- **A cocycle for `i a ∪ ā` depending only on vertices.** Let `F y` be local primitives of `ω`
on open neighbourhoods `B y` of the points `y`. With `θ(τ) = |F(τ₁) - F(τ₀)|² / 2`, a cochain
independent of the ball,
`i (φ ∪ φ̄ + δθ)` is a cocycle representing `i a ∪ ā` whose value on a `2`-simplex in a ball is
`Im (\overline{p₁ - p₀} (p₂ - p₀))`, for `pᵢ = F(σ(vᵢ))`: twice the signed area of the triangle
with vertices `p₀, p₁, p₂`. -/
theorem exists_smul_cup_conjH_eq_ofCocycle (hn : n = 1 ∨ n = 2)
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (ha : IsDR X ω a)
    (B : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))))
    (F : ComplexPoints (X ↘ Spec (.of ℂ)) → ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ)
    (hBo : ∀ y, IsOpen (B y)) (hmem : ∀ y, y ∈ B y) (hprim : ∀ y, IsLocalPrimitive ω (B y) (F y)) :
      ∃ (Ψ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℂ)
        (hΨ : Ψ ∈ relCocycles ℂ
          (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) (1 + 1)),
        Complex.I • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 a (conjH X a) =
          cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) Ψ hΨ ∧
        ∀ (σ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1)) (y : ComplexPoints _),
          Set.range σ ⊆ B y →
            Ψ σ = ((starRingEnd ℂ (F y (σ (stdSimplex.vertex 1)) - F y (σ (stdSimplex.vertex 0))) *
              (F y (σ (stdSimplex.vertex 2)) - F y (σ (stdSimplex.vertex 0)))).im : ℂ) := by
  obtain ⟨φ, hφ, hφDR, hφv⟩ := isDR_of_isLocalPrimitive (n := n) ω B F hBo hmem hprim
  rw [IsDR.unique hn ha hφDR, singularCohomology.mapCoeff_ofCocycle,
    cupNatUniv_ofCocycle _ 1 1 hφ _]
  set ψ := singularCohomology.cochainMap (starRingEnd ℂ) 1 φ with hψdef
  have hψv : ∀ σ, ψ σ = starRingEnd ℂ (φ σ) := fun _ ↦ rfl
  let θ : ComplexPoints (X ↘ Spec (.of ℂ)) →
      Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1 → ℂ := fun y τ ↦
    ((Complex.normSq (F y (τ (stdSimplex.vertex 1)) - F y (τ (stdSimplex.vertex 0))) / 2 : ℝ) : ℂ)
  obtain ⟨Θ, hΘ⟩ := exists_cochain_of_forall_eq (Y := Analytification.space (X ↘ Spec (.of ℂ)))
    B θ fun τ y₁ y₂ h₁ h₂ ↦ by
      have h₁₂ : Set.range τ ⊆ B y₁ ∩ B y₂ := Set.subset_inter h₁ h₂
      have eF := apply_vertex_eq_of_eventually τ (f := fun z ↦ F y₁ z - F y₂ z) h₁₂
        (fun w hw ↦ eventually_sub_eq_of_isLocalPrimitive (n := n) ω (hBo y₁) (hBo y₂) (hprim y₁)
          (hprim y₂) hw) 1 0
      simp only [θ]
      congr 3
      linear_combination eF
  have hφ0 : coboundary ℂ 1 φ = 0 := LinearMap.mem_ker.1 hφ.2
  have hψ0 : coboundary ℂ 1 ψ = 0 := LinearMap.mem_ker.1
    (singularCohomology.cochainMap_mem_relCocycles (starRingEnd ℂ) hφ).2
  set χ := cup 1 1 (1 + 1) rfl φ ψ + coboundary ℂ 1 Θ with hχdef
  have hχ : χ ∈ relCocycles ℂ
      (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) (1 + 1) := by
    refine ⟨fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp), LinearMap.mem_ker.2 ?_⟩
    rw [hχdef, map_add, coboundary_cup, hφ0, hψ0, coboundary_coboundary]
    simp
  have heq : cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) (cup 1 1 (1 + 1) rfl φ ψ)
      (cup_mem_relCocycles_compl_univ rfl hφ
        (singularCohomology.cochainMap_mem_relCocycles (starRingEnd ℂ) hφ)) =
      cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ := by
    simp only [cohomologyWithSupports.ofCocycle]
    congr 1
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    refine Submodule.mem_map.2 ⟨-Θ, fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
      ?_⟩
    show coboundary ℂ 1 (-Θ) = cup 1 1 (1 + 1) rfl φ ψ - χ
    rw [hχdef, map_neg]
    abel
  refine ⟨Complex.I • χ, Submodule.smul_mem _ _ hχ, ?_, fun σ y hσ ↦ ?_⟩
  · rw [ofCocycle_smul hχ Complex.I, ← heq]
  have hface : ∀ k : Fin 3, Set.range (σ.comp (face 1 k)) ⊆ B y :=
    fun k _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  have hfr : Set.range (σ.comp (smap (front 1 (1 + 1) (by omega)))) ⊆ B y :=
    fun _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  have hbk : Set.range (σ.comp (smap (back 1 (1 + 1) 1 (by omega)))) ⊆ B y :=
    fun _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  rw [Pi.smul_apply, hχdef, Pi.add_apply, cup_apply, hψv, hφv _ y hfr, hφv _ y hbk,
    coboundary_apply, Fin.sum_univ_three, hΘ _ y (hface 0), hΘ _ y (hface 1), hΘ _ y (hface 2)]
  have vf0 : (σ.comp (smap (front 1 (1 + 1) (by omega)))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (0 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have vf1 : (σ.comp (smap (front 1 (1 + 1) (by omega)))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have vb0 : (σ.comp (smap (back 1 (1 + 1) 1 (by omega)))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have vb1 : (σ.comp (smap (back 1 (1 + 1) 1 (by omega)))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (2 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have v00 : (σ.comp (face 1 (0 : Fin 3))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (face_vertex (0 : Fin 3) (0 : Fin 2))
  have v01 : (σ.comp (face 1 (0 : Fin 3))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (2 : Fin 3)) := congrArg σ (face_vertex (0 : Fin 3) (1 : Fin 2))
  have v10 : (σ.comp (face 1 (1 : Fin 3))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (0 : Fin 3)) := congrArg σ (face_vertex (1 : Fin 3) (0 : Fin 2))
  have v11 : (σ.comp (face 1 (1 : Fin 3))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (2 : Fin 3)) := congrArg σ (face_vertex (1 : Fin 3) (1 : Fin 2))
  have v20 : (σ.comp (face 1 (2 : Fin 3))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (0 : Fin 3)) := congrArg σ (face_vertex (2 : Fin 3) (0 : Fin 2))
  have v21 : (σ.comp (face 1 (2 : Fin 3))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (face_vertex (2 : Fin 3) (1 : Fin 2))
  simp only [θ]
  rw [vf0, vf1, vb0, vb1, v00, v01, v10, v11, v20, v21]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_mul,
    neg_one_mul, smul_eq_mul]
  generalize F y (σ (stdSimplex.vertex 0)) = p₀
  generalize F y (σ (stdSimplex.vertex 1)) = p₁
  generalize F y (σ (stdSimplex.vertex 2)) = p₂
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

/-- **Top-degree cohomology is at most a line**: `dim H^{2n}(X^an; R) ≤ 1` over a field `R`.
Capping with the
fundamental class of `X(ℂ)` is injective on `H^{2n}` (Poincaré duality), with values in `H_0`
of the compact path-connected `X(ℂ)`, which is spanned by the class of a point. -/
theorem finrank_analyticSingularCohomology_two_mul_le_one (R : Type) [Field R] :
    Module.finrank R (analyticSingularCohomology R (X ↘ Spec (.of ℂ)) (2 * n)) ≤ 1 := by
  haveI hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ (IsProjectiveVariety.isProjective (k := ℂ))
  haveI : IsComplexScheme X :=
    MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  obtain ⟨μ, hμ, -, -⟩ := existsUnique_isVarietyFundamentalClass R (V := X)
    (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) n)
  have hb := borelMooreHomology.bijective_capProduct_univ_of_isVarietyFundamentalClass hμ
    ((2 * n : ℕ) : ℤ)
  haveI : ConnectedSpace (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    MMP.Fourfold.connectedSpace_analyticSpace (X ↘ Spec (.of ℂ))
  haveI : LocallyPathConnectedSpace (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℂ (Fin n)) _
  haveI : PathConnectedSpace (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    pathConnectedSpace_iff_connectedSpace.2 inferInstance
  haveI : PathConnectedSpace (UnderlyingSpace ℂ X) :=
    ComplexPoints.homeomorphUnderlyingSpace.surjective.pathConnectedSpace
      ComplexPoints.homeomorphUnderlyingSpace.continuous
  have e := MMP.specOverSpec_over_self (K := ℂ)
  haveI : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) := ⟨by rw [e, Category.comp_id]⟩
  have hsub : Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))) := ⟨fun p q ↦ UnderlyingSpace.ext (by
    have h1 := p.toHom_comp_over
    have h2 := q.toHom_comp_over
    rw [e, Category.comp_id] at h1 h2
    rw [h1, h2])⟩
  have hp := UnderlyingSpace.isProperMap_map (K := ℂ) (X ↘ Spec (.of ℂ))
  haveI : CompactSpace (UnderlyingSpace ℂ X) := by
    refine ⟨?_⟩
    have := hp.isCompact_preimage (Set.subsingleton_of_subsingleton (s := Set.univ)).isCompact
    simpa using this
  obtain ⟨v, hv⟩ := exists_forall_smul_eq_borelMooreHomology_zero (R := R)
    (TopCat.of (UnderlyingSpace ℂ X)) (((2 * n : ℕ) : ℤ) - ((2 * n : ℕ) : ℤ)) (by ring)
  let anHom : TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩
  let anInv : Analytification.space (X ↘ Spec (.of ℂ)) ⟶ TopCat.of (UnderlyingSpace ℂ X) :=
    TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.continuous⟩
  have hinvhom : anInv ≫ anHom = 𝟙 _ :=
    TopCat.hom_ext (ContinuousMap.ext fun x ↦
      ComplexPoints.homeomorphUnderlyingSpace.symm_apply_apply x)
  have hpb : Function.Injective (cohomologyWithSupports.pullback R (ModuleCat.of R R) anHom
      Set.univ ((2 * n : ℕ) : ℤ)).hom := by
    have key : ∀ c, (cohomologyWithSupports.pullback R (ModuleCat.of R R) anInv
        (anHom ⁻¹' Set.univ) ((2 * n : ℕ) : ℤ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) anHom Set.univ
          ((2 * n : ℕ) : ℤ)).hom c) = c := by
      intro c
      rw [← ModuleCat.comp_apply, ← cohomologyWithSupports.pullback_comp]
      generalize hφ : anInv ≫ anHom = φ
      rw [hinvhom] at hφ
      subst hφ
      rw [cohomologyWithSupports.pullback_id]
      rfl
    exact Function.LeftInverse.injective key
  let Φ := (borelMooreHomology.capProductPullback R anHom Set.univ ((2 * n : ℕ) : ℤ)
    ((2 * n : ℕ) : ℤ)).flip μ
  have hΦ : Function.Injective Φ := fun c c' h ↦ hpb (hb.1 h)
  haveI : FiniteDimensional R (borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ X)) (((2 * n : ℕ) : ℤ) - ((2 * n : ℕ) : ℤ))) :=
    ⟨⟨{v}, eq_top_iff.2 fun w _ ↦ by
      obtain ⟨r, rfl⟩ := hv w
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))⟩⟩
  exact (LinearMap.finrank_le_finrank_of_injective hΦ).trans (finrank_le_one v hv)

/-- `H^k(X^an; R)` is finite dimensional over a field `R`: `X^an` has a finite free chain
model. -/
theorem finiteDimensional_analyticSingularCohomology (R : Type) [Field R] (k : ℕ) :
    FiniteDimensional R (analyticSingularCohomology R (X ↘ Spec (.of ℂ)) k) :=
  MMP.Analytic.finite_analyticSingularCohomology_of_isProjectiveMorphism (X ↘ Spec (.of ℂ))
    (IsProjectiveVariety.isProjective (k := ℂ)) R k

/-- In a space of dimension at most one, every vector is a multiple of a nonzero vector. -/
theorem exists_smul_eq_of_finrank_le_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (h : Module.finrank K V ≤ 1) {v : V} (hv : v ≠ 0)
    (w : V) : ∃ s : K, s • v = w := by
  have h1 := finrank_span_singleton (K := K) hv
  have htop : Submodule.span K {v} = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by rwa [h1]))
  exact Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top)

/-- A class is zero iff a cocycle representing it is a coboundary. -/
theorem ofCocycle_eq_zero_iff {R : Type} [CommRing R] {Y : TopCat.{0}} {k : ℕ}
    {φ : Simplex Y k → R} (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) k) :
    cohomologyWithSupports.ofCocycle R Y k φ hφ = 0 ↔
      φ ∈ relCoboundaries R (Set.univᶜ : Set Y) k := by
  rw [cohomologyWithSupports.ofCocycle, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  rfl

omit [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] in
/-- A projective variety is proper. -/
theorem isProper_structureMorphism : IsProper (X ↘ Spec (.of ℂ)) :=
  isProper_of_isProjectiveMorphism _ (IsProjectiveVariety.isProjective (k := ℂ))

/-- **Green's theorem for the area form on the unit square.** For a `C²` map `G` from a
neighbourhood of `[0, 1]²` to `ℂ`, the integral of `∂₁G · \overline{∂₂G} - ∂₂G · \overline{∂₁G}`
(that is `-2i` times the Jacobian of `G`) over the square is the line integral of `G d\overline{G}`
around its boundary. -/
theorem integral_jacobian_eq_boundary {G : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsub : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U) (hG : ContDiffOn ℝ 2 G U) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (fderiv ℝ G (x, y) (1, 0) * star (fderiv ℝ G (x, y) (0, 1)) -
          fderiv ℝ G (x, y) (0, 1) * star (fderiv ℝ G (x, y) (1, 0)))) =
      (((∫ x in (0 : ℝ)..1, -(G (x, 1) * star (fderiv ℝ G (x, 1) (1, 0)))) -
          ∫ x in (0 : ℝ)..1, -(G (x, 0) * star (fderiv ℝ G (x, 0) (1, 0)))) +
        ∫ y in (0 : ℝ)..1, G (1, y) * star (fderiv ℝ G (1, y) (0, 1))) -
        ∫ y in (0 : ℝ)..1, G (0, y) * star (fderiv ℝ G (0, y) (0, 1)) := by
  have hsq : Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (0 : ℝ) 1 ⊆ U := by
    rwa [Set.uIcc_of_le zero_le_one]
  have hGa : ∀ p ∈ U, ContDiffAt ℝ 2 G p := fun p hp ↦ hG.contDiffAt (hU.mem_nhds hp)
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ G) U := hG.fderiv_of_isOpen hU (by norm_num)
  have hGc : ContinuousOn G U := hG.continuousOn
  have hDc : ContinuousOn (fderiv ℝ G) U := hD1.continuousOn
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ G)) U :=
    hD1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hG' : ∀ p ∈ U, HasFDerivAt G (fderiv ℝ G p) p := fun p hp ↦
    ((hGa p hp).differentiableAt (by norm_num)).hasFDerivAt
  have hD' : ∀ p ∈ U, HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) p) p := fun p hp ↦
    ((hD1.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero).hasFDerivAt
  have hpart : ∀ (v : ℝ × ℝ), ∀ p ∈ U, HasFDerivAt (fun q ↦ fderiv ℝ G q v)
      ((fderiv ℝ (fderiv ℝ G) p).flip v) p := fun v p hp ↦ by
    simpa using (hD' p hp).clm_apply (hasFDerivAt_const v p)
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p ↦
    G p • (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ (fderiv ℝ G) p).flip (0, 1))) +
      star (fderiv ℝ G p (0, 1)) • fderiv ℝ G p
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p ↦
    -(G p • (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ (fderiv ℝ G) p).flip (1, 0))) +
      star (fderiv ℝ G p (1, 0)) • fderiv ℝ G p)
  have hf : ∀ p ∈ U, HasFDerivAt (fun q ↦ G q * star (fderiv ℝ G q (0, 1))) (f' p) p :=
    fun p hp ↦ (hG' p hp).mul ((hpart (0, 1) p hp).star)
  have hg : ∀ p ∈ U, HasFDerivAt (fun q ↦ -(G q * star (fderiv ℝ G q (1, 0)))) (g' p) p :=
    fun p hp ↦ ((hG' p hp).mul ((hpart (1, 0) p hp).star)).neg
  have hcont : ∀ v : ℝ × ℝ, ContinuousOn (fun q ↦ fderiv ℝ G q v) U := fun v ↦
    hDc.clm_apply continuousOn_const
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (fun q ↦ G q * star (fderiv ℝ G q (0, 1))) (fun q ↦ -(G q * star (fderiv ℝ G q (1, 0))))
    f' g' 0 0 1 1
    ((hGc.mul (hcont (0, 1)).star).mono hsq) (((hGc.mul (hcont (1, 0)).star).neg).mono hsq)
    (fun p hp ↦ hf p (hsub ⟨Set.Ioo_subset_Icc_self (by simpa using hp.1),
      Set.Ioo_subset_Icc_self (by simpa using hp.2)⟩))
    (fun p hp ↦ hg p (hsub ⟨Set.Ioo_subset_Icc_self (by simpa using hp.1),
      Set.Ioo_subset_Icc_self (by simpa using hp.2)⟩))
    (by
      refine ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) ?_
      refine ContinuousOn.add ?_ ?_
      · simp only [f', ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul]
        exact ((hGc.mul ((hD2c.clm_apply continuousOn_const).clm_apply
          continuousOn_const).star).add ((hcont (0, 1)).star.mul (hcont (1, 0)))).mono hsq
      · simp only [g', ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.coe_coe, starL'_apply,
          smul_eq_mul]
        exact (((hGc.mul ((hD2c.clm_apply continuousOn_const).clm_apply
          continuousOn_const).star).add ((hcont (1, 0)).star.mul (hcont (0, 1)))).neg).mono hsq)
  rw [← key]
  refine intervalIntegral.integral_congr fun x hx ↦ intervalIntegral.integral_congr fun y hy ↦ ?_
  have hp : (x, y) ∈ U := hsq ⟨hx, hy⟩
  have hsymm := (hGa (x, y) hp).isSymmSndFDerivAt (by simp) (1, 0) (0, 1)
  simp only [f', g', ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul,
    hsymm]
  ring

/-- The imaginary part of an interval integral of a function continuous on `[0, 1]`. -/
theorem im_intervalIntegral_of_continuousOn {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, f x).im = ∫ x in (0 : ℝ)..1, (f x).im := by
  simpa using (Complex.imCLM.intervalIntegral_comp_comm
    (hf.intervalIntegrable_of_Icc zero_le_one)).symm

/-- An integral over `[0, 1]` of a function continuous on the unit square depends continuously
on the parameter in `[0, 1]`. -/
theorem continuousOn_intervalIntegral_of_continuousOn_square {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : ℝ × ℝ → E}
    (hP : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x ↦ ∫ y in (0 : ℝ)..1, P (x, y)) (Set.Icc 0 1) := by
  let Q : ℝ → ℝ → E := fun x y ↦
    P ((Set.projIcc (0 : ℝ) 1 zero_le_one x : ℝ), (Set.projIcc (0 : ℝ) 1 zero_le_one y : ℝ))
  have hQ : Continuous (Function.uncurry Q) := by
    refine hP.comp_continuous (by fun_prop) fun p ↦
      ⟨(Set.projIcc (0 : ℝ) 1 zero_le_one p.1).2, (Set.projIcc (0 : ℝ) 1 zero_le_one p.2).2⟩
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ 0 1
    ).continuousOn.congr fun x hx ↦ intervalIntegral.integral_congr fun y hy ↦ ?_
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp only [Q, Set.projIcc_of_mem _ hx, Set.projIcc_of_mem _ hy]

/-- **Green's theorem for the real one-form `Im (ḡ dg)` on the unit square.** For a `C²` map
`G` from a neighbourhood of `[0, 1]²` to `ℂ`, twice the integral of `Im (\overline{∂₁G} ∂₂G)`,
the Jacobian of `G`, over the square is the integral of `Im (Ḡ dG)` around its boundary. -/
theorem integral_im_jacobian_eq_boundary {G : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hsub : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U)
    (hG : ContDiffOn ℝ 2 G U) :
    2 * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (star (fderiv ℝ G (x, y) (1, 0)) * fderiv ℝ G (x, y) (0, 1)).im) =
      (((∫ x in (0 : ℝ)..1, (star (G (x, 0)) * fderiv ℝ G (x, 0) (1, 0)).im) +
          ∫ y in (0 : ℝ)..1, (star (G (1, y)) * fderiv ℝ G (1, y) (0, 1)).im) -
        ∫ x in (0 : ℝ)..1, (star (G (x, 1)) * fderiv ℝ G (x, 1) (1, 0)).im) -
        ∫ y in (0 : ℝ)..1, (star (G (0, y)) * fderiv ℝ G (0, y) (0, 1)).im := by
  have hD : ContinuousOn (fderiv ℝ G) U :=
    (hG.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn
  have hGc : ContinuousOn G U := hG.continuousOn
  have hDv : ∀ v : ℝ × ℝ, ContinuousOn (fun p ↦ fderiv ℝ G p v) U := fun v ↦
    hD.clm_apply continuousOn_const
  have hsq : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, (x, y) ∈ U :=
    fun x hx y hy ↦ hsub ⟨hx, hy⟩
  have hP : ContinuousOn (fun p : ℝ × ℝ ↦ fderiv ℝ G p (1, 0) * star (fderiv ℝ G p (0, 1)) -
      fderiv ℝ G p (0, 1) * star (fderiv ℝ G p (1, 0))) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    (((hDv _).mul (hDv _).star).sub ((hDv _).mul (hDv _).star)).mono hsub
  have hrow : ∀ (v : ℝ × ℝ) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 →
      ContinuousOn (fun x ↦ G (x, y) * star (fderiv ℝ G (x, y) v)) (Set.Icc 0 1) :=
    fun v y hy ↦ (hGc.mul (hDv v).star).comp (by fun_prop) fun x hx ↦ hsq x hx y hy
  have hcol : ∀ (v : ℝ × ℝ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      ContinuousOn (fun y ↦ G (x, y) * star (fderiv ℝ G (x, y) v)) (Set.Icc 0 1) :=
    fun v x hx ↦ (hGc.mul (hDv v).star).comp (by fun_prop) fun y hy ↦ hsq x hx y hy
  have h := congrArg Complex.im (integral_jacobian_eq_boundary hU hsub hG)
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [Complex.sub_im, Complex.add_im, Complex.sub_im,
    im_intervalIntegral_of_continuousOn (continuousOn_intervalIntegral_of_continuousOn_square hP),
    im_intervalIntegral_of_continuousOn
      (f := fun x ↦ -(G (x, 1) * star (fderiv ℝ G (x, 1) (1, 0)))) (hrow _ 1 h11).neg,
    im_intervalIntegral_of_continuousOn
      (f := fun x ↦ -(G (x, 0) * star (fderiv ℝ G (x, 0) (1, 0)))) (hrow _ 0 h01).neg,
    im_intervalIntegral_of_continuousOn
      (f := fun y ↦ G (1, y) * star (fderiv ℝ G (1, y) (0, 1))) (hcol _ 1 h11),
    im_intervalIntegral_of_continuousOn
      (f := fun y ↦ G (0, y) * star (fderiv ℝ G (0, y) (0, 1))) (hcol _ 0 h01)] at h
  have hin : ∀ x ∈ Set.uIcc (0 : ℝ) 1, (∫ y in (0 : ℝ)..1,
      (fderiv ℝ G (x, y) (1, 0) * star (fderiv ℝ G (x, y) (0, 1)) -
        fderiv ℝ G (x, y) (0, 1) * star (fderiv ℝ G (x, y) (1, 0)))).im =
      ∫ y in (0 : ℝ)..1, (-2) *
        (star (fderiv ℝ G (x, y) (1, 0)) * fderiv ℝ G (x, y) (0, 1)).im := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [im_intervalIntegral_of_continuousOn (f := fun y ↦
        fderiv ℝ G (x, y) (1, 0) * star (fderiv ℝ G (x, y) (0, 1)) -
          fderiv ℝ G (x, y) (0, 1) * star (fderiv ℝ G (x, y) (1, 0)))
      (hP.comp (f := fun y : ℝ ↦ (x, y)) (by fun_prop) fun y hy ↦ ⟨hx, hy⟩)]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [Complex.sub_im, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [intervalIntegral.integral_congr hin] at h
  have k1 : ∀ a b : ℂ, (-(a * star b)).im = (star a * b).im := fun a b ↦ by
    simp only [Complex.neg_im, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    ring
  have k2 : ∀ a b : ℂ, (a * star b).im = -(star a * b).im := fun a b ↦ by
    simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simp only [k1, k2, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at h
  linarith

/-- **A complex-linear form on `ℂ¹` scales the Jacobian by `|L 1|²`**: for `u, v ∈ ℂ¹`,
`Im (\overline{L u} L v) = |L 1|² Im (\overline{u₀} v₀)`. -/
theorem im_star_mul_eq_normSq_mul (L : (Fin 1 → ℂ) →L[ℂ] ℂ) (u v : Fin 1 → ℂ) :
    (star (L u) * L v).im = Complex.normSq (L fun _ ↦ 1) * (star (u 0) * v 0).im := by
  have hu : u = u 0 • (fun _ ↦ (1 : ℂ)) := by ext i; fin_cases i; simp
  have hv : v = v 0 • (fun _ ↦ (1 : ℂ)) := by ext i; fin_cases i; simp
  rw [hu, hv]
  simp only [map_smul, smul_eq_mul, Pi.smul_apply, mul_one]
  generalize L (fun _ ↦ 1) = c
  simp only [Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- **Algebraic coordinates at a closed point.** A closed point of `X` has an affine open
neighbourhood `W` with regular functions `z₁, …, zₙ` whose differentials form a basis of
`Ω[Γ(W)⁄ℂ]`. -/
theorem exists_basis_D_of_isClosed (x : X) (hx : IsClosed {x}) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (_ : x ∈ W) (z : Fin n → Γ(X, W)),
      letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) W
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(X, W) (z i) := by
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ (IsProjectiveVariety.isProjective (k := ℂ))
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨cs, -, -, -, -, Θ, -, h⟩ :=
    MMP.Analytic.analytification_smooth_differentials_of_smoothOfRelativeDimension
      (X ↘ Spec (.of ℂ)) (n := n) (0 : MMP.Mori.Divisor X)
      (MMP.Mori.DivisorWithCoeffs.isSNC_zero _)
  obtain ⟨W, hW, hxW, k, hk, z, -, -, hb, -⟩ := h x hx
  exact ⟨W, hW, hxW, z, hb⟩

set_option maxRecDepth 8000 in
/-- **The coefficients of a form with locally constant chart primitives vanish.** Let
`ω|_W = ∑ᵢ aᵢ dzᵢ` in a basis `dzᵢ` of `Ω[Γ(W)⁄ℂ]`. If near every point the chart primitive of
`ω` has derivative zero, then every `aₖ` vanishes at every point `y` of `W(ℂ)`: differentiating
along the lines `t ↦ e⁻¹ (e y + t v)` of an étale chart `e` at `y` gives `∑ᵢ aᵢ(y) mᵢ(v) = 0`,
where `m(v) = (d zᵢ (v))ᵢ`, and `m` is injective, since a derivation at `y` killing every `zᵢ`
kills `Γ(W)`, hence the coordinates of `e`. -/
theorem evalT_eq_zero_of_isChartPrimitive
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    (hω : ∀ x : ComplexPoints (X ↘ Spec (.of ℂ)),
      ∃ (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (D : Set (Fin n → ℂ))
        (Φ : (Fin n → ℂ) → ℂ), x ∈ c.toOpenPartialHomeomorph.source ∧
        c.toOpenPartialHomeomorph x ∈ D ∧ IsOpen D ∧ IsChartPrimitive ω c D Φ ∧
        ∀ z ∈ D, HasFDerivAt Φ (0 : (Fin n → ℂ) →L[ℝ] ℂ) z)
    (W : X.affineOpens) (z a : Fin n → Γ(X, W))
    (hb : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (W : X.Opens)
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(X, W) (z i))
    (ha : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (W : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 W
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, a j • exteriorPower.ιMulti Γ(X, W) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, W) (z j)))
    {y : ComplexPoints (X ↘ Spec (.of ℂ))}
    (hy : y ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (W : X.Opens)) (k : Fin n) :
    evalT (W : X.Opens) (a k) y = 0 := by
  obtain ⟨c, D, Φ, hys, hyD, hDo, ⟨V, m₀, f₀, g₀, h₀, hDV, hΦ⟩, hΦ0⟩ := hω y
  set e := c.toOpenPartialHomeomorph
  have hyt : e y ∈ e.target := e.map_source hys
  have hsymm : e.symm (e y) = y := e.left_inv hys
  let q : (Fin n → ℂ) → ℝ → ComplexPoints (X ↘ Spec (.of ℂ)) := fun v t ↦ e.symm (e y + t • v)
  have hq0 : ∀ v, q v 0 = y := fun v ↦ by simp [q, hsymm]
  have hline : ∀ v : Fin n → ℂ, HasDerivAt (fun t : ℝ ↦ e y + t • v) v 0 := fun v ↦ by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (e y)
  have hqc : ∀ v, ContinuousAt (q v) 0 := fun v ↦ by
    refine ContinuousAt.comp (f := fun t : ℝ ↦ e y + t • v) (g := e.symm) ?_
      (hline v).continuousAt
    simpa using e.continuousAt_symm hyt
  have hder : ∀ (V' : X.Opens) (h : Γ(X, V')),
      y ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V' → ∀ v,
      HasDerivAt (fun t ↦ evalT V' h (q v t))
        (fderiv ℝ (fun w ↦ evalT V' h (e.symm w)) (e y) v) 0 := by
    intro V' h hyV' v
    have hA := analyticAt_evalT_symm c V' h (z := e y)
      ⟨hyt, by rwa [Set.mem_preimage, hsymm]⟩
    exact (hA.differentiableAt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline v)
      (by simp)
  have hyV : y ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens) := by
    have := (hDV hyD).2
    rwa [Set.mem_preimage, hsymm] at this
  let m : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun v i ↦ fderiv ℝ (fun w ↦ evalT (W : X.Opens) (z i) (e.symm w)) (e y) v
      map_add' := fun v v' ↦ by ext i; simp
      map_smul' := fun r v ↦ by ext i; simp }
  have hvan : ∀ v, ∑ i, evalT (W : X.Opens) (a i) y * m v i = 0 := by
    intro v
    have key := sum_evalT_mul_deriv_congr ω f₀ g₀ a z h₀ ha (q := q v) (t := 0) (hqc v)
      ((hq0 v).symm ▸ hyV) ((hq0 v).symm ▸ hy)
      (fun h ↦ (hder (V : X.Opens) h hyV v).differentiableAt)
    simp only [hq0, fun i ↦ (hder (W : X.Opens) (z i) hy v).deriv,
      fun j ↦ (hder (V : X.Opens) (g₀ j) hyV v).deriv] at key
    show ∑ i, evalT (W : X.Opens) (a i) y *
      fderiv ℝ (fun w ↦ evalT (W : X.Opens) (z i) (e.symm w)) (e y) v = 0
    rw [← key]
    have h1 := (hΦ (e y) hyD).unique (hΦ0 (e y) hyD)
    have h2 := congrArg (fun L : (Fin n → ℂ) →L[ℝ] ℂ ↦ L v) h1
    simpa [hsymm] using h2
  have hinj : Function.Injective m := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hdW : ∀ a' : Γ(X, W), DifferentiableAt ℝ (fun t ↦ evalT (W : X.Opens) a' (q v t)) 0 :=
      fun a' ↦ (hder _ a' hy v).differentiableAt
    have hkill : ∀ a' : Γ(X, W), deriv (fun t ↦ evalT (W : X.Opens) a' (q v t)) 0 = 0 := by
      letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (W : X.Opens)
      let ev := ComplexPoints.evalHom (W : X.Opens) ⟨y, hy⟩
      have hev : ∀ c, ev (algebraMap ℂ Γ(X, W) c) = c := fun c ↦
        ComplexPoints.evalHom_baseRingHom _ _ c
      have hevT : ∀ a', ev a' = evalT (W : X.Opens) a' (q v 0) := fun a' ↦ by
        rw [hq0]; exact (evalT_of_mem a' hy).symm
      let Dt : Γ(X, W) → ℂ := fun h ↦ deriv (fun t ↦ evalT (W : X.Opens) h (q v t)) 0
      have hadd : ∀ a b, Dt (a + b) = Dt a + Dt b := fun a b ↦ by
        simp only [Dt, evalT_add]
        exact deriv_fun_add (hdW a) (hdW b)
      have hsmul : ∀ (c : ℂ) a, Dt (algebraMap ℂ Γ(X, W) c * a) = c * Dt a := fun c a ↦ by
        simp only [Dt]
        change deriv (fun t ↦ evalT (W : X.Opens)
          (ComplexPoints.baseRingHom (X ↘ Spec (.of ℂ)) (W : X.Opens) c * a) (q v t)) 0 = _
        simp only [evalT_baseRingHom_mul]
        exact deriv_const_mul c (hdW a)
      have hmul : ∀ a b, Dt (a * b) = ev a * Dt b + ev b * Dt a := fun a b ↦ by
        simp only [Dt, evalT_mul, hevT]
        rw [deriv_fun_mul (hdW a) (hdW b)]
        ring
      letI : Module Γ(X, W) ℂ := Module.compHom ℂ ev
      have e' : ∀ (a : Γ(X, W)) (z : ℂ), a • z = ev a * z := fun _ _ ↦ rfl
      haveI : IsScalarTower ℂ Γ(X, W) ℂ := ⟨fun c a z ↦ by
        rw [e', e', Algebra.smul_def, map_mul, hev, smul_eq_mul, mul_assoc]⟩
      let l := (derivationAt ev hev Dt hadd hsmul hmul).liftKaehlerDifferential
      have hl : ∀ a, l (KaehlerDifferential.D ℂ Γ(X, W) a) = Dt a := fun a ↦
        Derivation.liftKaehlerDifferential_comp_D _ a
      obtain ⟨b, hbz⟩ := hb
      have hl0 : l = 0 := b.ext fun i ↦ by
        rw [hbz, hl, LinearMap.zero_apply]
        show deriv (fun t ↦ evalT (W : X.Opens) (z i) (q v t)) 0 = 0
        rw [(hder _ (z i) hy v).deriv]
        exact congrFun hv i
      intro a'
      show Dt a' = 0
      rw [← hl a', hl0, LinearMap.zero_apply]
    have hzero : ∀ a' : Γ(X, W), HasDerivAt (fun t ↦ evalT (W : X.Opens) a' (q v t)) 0 0 :=
      fun a' ↦ by
        have h := (hdW a').hasDerivAt
        rwa [hkill a'] at h
    funext k'
    have hcW : y ∈ c.W := c.source_toOpenPartialHomeomorph ▸ hys
    have hcU : y ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) c.U := c.subset hcW
    obtain ⟨a', s, kk, hs, hloc⟩ := exists_eval_mul_pow_eq W c.U hy hcU (c.z k')
    have hWn : ∀ᶠ t in nhds (0 : ℝ),
        q v t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (W : X.Opens) :=
      (hqc v).preimage_mem_nhds ((ComplexPoints.isOpen_chart _ _).mem_nhds ((hq0 v).symm ▸ hy))
    have hs0 : evalT (W : X.Opens) s (q v 0) ≠ 0 := by
      rwa [hq0, evalT_of_mem _ hy]
    have hsn : ∀ᶠ t in nhds (0 : ℝ), evalT (W : X.Opens) s (q v t) ≠ 0 :=
      (hdW s).continuousAt.eventually_ne hs0
    have hev : ∀ᶠ t in nhds (0 : ℝ),
        evalT (W : X.Opens) a' (q v t) =
          evalT c.U (c.z k') (q v t) * evalT (W : X.Opens) s (q v t) ^ kk := by
      filter_upwards [hWn, hsn] with t h1 h2
      rw [evalT_of_mem _ h1] at h2
      obtain ⟨h3, h4⟩ := hloc (q v t) h1 h2
      rw [evalT_of_mem _ h3, evalT_of_mem _ h1, evalT_of_mem _ h1, h4]
    have hcoord : ∀ᶠ t in nhds (0 : ℝ), evalT c.U (c.z k') (q v t) = (e y + t • v) k' := by
      filter_upwards [(hline v).continuousAt.preimage_mem_nhds
        (e.open_target.mem_nhds (by simpa using hyt))] with t ht
      have hp : q v t ∈ c.W := c.source_toOpenPartialHomeomorph ▸ e.map_target ht
      have h1 : e (q v t) = e y + t • v := e.right_inv ht
      rw [← h1, c.toOpenPartialHomeomorph_apply hp k', evalT_of_mem _ (c.subset hp),
        ComplexPoints.evalHom_apply]
    have hf : HasDerivAt (fun t ↦ evalT c.U (c.z k') (q v t)) (v k') 0 :=
      ((hasDerivAt_pi.1 (hline v)) k').congr_of_eventuallyEq hcoord
    have hprod := (hf.mul ((hzero s).pow kk)).congr_of_eventuallyEq hev
    have h0 := hprod.unique (hzero a')
    simp only [mul_zero, add_zero] at h0
    exact (mul_eq_zero.1 h0).resolve_right (pow_ne_zero _ hs0)
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.1 hinj) (Pi.single k 1)
  have := hvan v
  rw [hv] at this
  simpa [Pi.single_apply] using this

set_option maxRecDepth 8000 in
/-- **A one-form whose chart primitives are locally constant is zero.** Near every closed point
`ω = ∑ aᵢ dzᵢ` in algebraic coordinates, and every `aᵢ` vanishes at every `ℂ`-point
(`evalT_eq_zero_of_isChartPrimitive`), so is zero, since regular functions on the reduced
scheme `X` are determined by their values. Every point of the Jacobson scheme `X` specializes to a
closed point,
so these neighbourhoods cover `X`. -/
theorem eq_zero_of_forall_isChartPrimitive
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    (hω : ∀ x : ComplexPoints (X ↘ Spec (.of ℂ)),
      ∃ (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (D : Set (Fin n → ℂ))
        (Φ : (Fin n → ℂ) → ℂ), x ∈ c.toOpenPartialHomeomorph.source ∧
        c.toOpenPartialHomeomorph x ∈ D ∧ IsOpen D ∧ IsChartPrimitive ω c D Φ ∧
        ∀ z ∈ D, HasFDerivAt Φ (0 : (Fin n → ℂ) →L[ℝ] ℂ) z) :
    ω = 0 := by
  haveI hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  haveI := isProper_structureMorphism (X := X)
  let L := (X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)
  have hclosed : ∀ x : X, IsClosed {x} → ∃ U₀ : X.Opens, x ∈ U₀ ∧
      L.presheaf.map (homOfLE (le_top : U₀ ≤ ⊤)).op ω = 0 := by
    intro x hx
    obtain ⟨W, hW, hxW, z, hb⟩ := exists_basis_D_of_isClosed (n := n) x hx
    letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) W
    obtain ⟨b, hbz⟩ := hb
    let W' : X.affineOpens := ⟨W, hW⟩
    set ωW := exteriorPower.oneEquiv Γ(X, W) Ω[Γ(X, W)⁄ℂ]
      (MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 W' (L.presheaf.map (homOfLE le_top).op ω))
    let a : Fin n → Γ(X, W) := fun i ↦ b.repr ωW i
    have ha : MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 W'
        (L.presheaf.map (homOfLE le_top).op ω) =
          ∑ j, a j • exteriorPower.ιMulti Γ(X, W) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, W) (z j)) := by
      apply (exteriorPower.oneEquiv Γ(X, W) Ω[Γ(X, W)⁄ℂ]).injective
      rw [map_sum]
      simp only [map_smul, exteriorPower.oneEquiv_ιMulti, ← hbz]
      exact (b.sum_repr ωW).symm
    have ha0 : ∀ k, a k = 0 := fun k ↦
      MMP.JacobianLogarithm.Fam.eq_zero_of_forall_evalHom_eq_zero (sX := X ↘ Spec (.of ℂ)) hW (a k)
        fun ⟨y, hy⟩ ↦ by
      rw [← evalT_of_mem _ hy]
      exact evalT_eq_zero_of_isChartPrimitive hω W' z a ⟨b, hbz⟩ ha hy k
    refine ⟨W, hxW, (MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 W').injective ?_⟩
    rw [ha, map_zero]
    simp [ha0]
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  have hloc : ∀ p : X, ∃ U₀ : X.Opens, p ∈ U₀ ∧
      L.presheaf.map (homOfLE (le_top : U₀ ≤ ⊤)).op ω = 0 := by
    intro p
    obtain ⟨x, hxp, hx⟩ := nonempty_inter_closedPoints
      (⟨p, subset_closure rfl⟩ : (closure ({p} : Set X)).Nonempty)
      isClosed_closure.isLocallyClosed
    obtain ⟨U₀, hxU₀, hU₀⟩ := hclosed x ((mem_closedPoints_iff).1 hx)
    obtain ⟨_, ⟨hq, rfl⟩⟩ := mem_closure_iff.1 hxp _ U₀.isOpen hxU₀
    exact ⟨U₀, hq, hU₀⟩
  choose U₀ hxU₀ hU₀ using hloc
  refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf X.ringCatSheaf).obj L)
    U₀ ⊤ (fun x ↦ homOfLE le_top)
    (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU₀ y⟩) _ _ fun x ↦ ?_
  change L.presheaf.map (homOfLE le_top).op ω = L.presheaf.map (homOfLE le_top).op 0
  rw [map_zero]
  exact hU₀ x

/-- The coordinate `1` of `squareCollapse (x, y)` is `x (1 - y)`, with `x` and `y` clamped to
`[0, 1]`. -/
theorem squareCollapse_apply_one' (x y : ℝ) :
    squareCollapse (x, y) 1 = (Set.projIcc (0 : ℝ) 1 zero_le_one x : ℝ) *
      (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one y : ℝ)) := rfl

/-- The coordinate `2` of `squareCollapse (x, y)` is `x y`, with `x` and `y` clamped to
`[0, 1]`. -/
theorem squareCollapse_apply_two' (x y : ℝ) :
    squareCollapse (x, y) 2 = (Set.projIcc (0 : ℝ) 1 zero_le_one x : ℝ) *
      (Set.projIcc (0 : ℝ) 1 zero_le_one y : ℝ) := rfl

/-- A point of `Δ²` is determined by its coordinates `1` and `2`. -/
theorem stdSimplex_three_ext {t t' : stdSimplex ℝ (Fin 3)} (h1 : t 1 = t' 1)
    (h2 : t 2 = t' 2) : t = t' := by
  have a := stdSimplex_three_add t
  have b := stdSimplex_three_add t'
  apply Subtype.ext
  funext i
  fin_cases i
  · show t 0 = t' 0
    linarith
  · exact h1
  · exact h2

/-- For `t ∈ [0, 1]`, the coordinate of `ptI t` at vertex `0` is `1 - t`. -/
theorem ptI_apply_zero {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ptI t 0 = 1 - t := by
  have h := stdSimplex_two_add (ptI t)
  have h1 : ptI t 1 = t := symm_projIcc_apply_one ht
  linarith

/-- The face `2` of `ptI t` is `squareCollapse (t, 0)`. -/
theorem face_two_ptI {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    face 1 2 (ptI t) = squareCollapse (t, 0) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine stdSimplex_three_ext ?_ ?_
  · rw [face_apply_one, squareCollapse_apply_one', if_neg (by decide), if_neg (by decide),
      symm_projIcc_apply_one ht, coe_projIcc_of_mem ht, coe_projIcc_of_mem h0]
    ring
  · rw [face_apply_two, squareCollapse_apply_two', if_pos rfl, coe_projIcc_of_mem h0, mul_zero]

/-- The face `0` of `ptI t` is `squareCollapse (1, t)`. -/
theorem face_zero_ptI {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    face 1 0 (ptI t) = squareCollapse (1, t) := by
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine stdSimplex_three_ext ?_ ?_
  · rw [face_apply_one, squareCollapse_apply_one', if_pos rfl, ptI_apply_zero ht,
      coe_projIcc_of_mem ht, coe_projIcc_of_mem h1, one_mul]
  · rw [face_apply_two, squareCollapse_apply_two', if_neg (by decide), symm_projIcc_apply_one ht,
      coe_projIcc_of_mem ht, coe_projIcc_of_mem h1, one_mul]

/-- The face `1` of `ptI t` is `squareCollapse (t, 1)`. -/
theorem face_one_ptI {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    face 1 1 (ptI t) = squareCollapse (t, 1) := by
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine stdSimplex_three_ext ?_ ?_
  · rw [face_apply_one, squareCollapse_apply_one', if_neg (by decide), if_pos rfl,
      coe_projIcc_of_mem ht, coe_projIcc_of_mem h1, sub_self, mul_zero]
  · rw [face_apply_two, squareCollapse_apply_two', if_neg (by decide), symm_projIcc_apply_one ht,
      coe_projIcc_of_mem ht, coe_projIcc_of_mem h1, mul_one]

/-- `squareCollapse` sends the edge `{0} × ℝ` to the vertex `squareCollapse (0, 0)`. -/
theorem squareCollapse_zero_left (y : ℝ) : squareCollapse (0, y) = squareCollapse (0, 0) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine stdSimplex_three_ext ?_ ?_
  · rw [squareCollapse_apply_one', squareCollapse_apply_one', coe_projIcc_of_mem h0, zero_mul,
      zero_mul]
  · rw [squareCollapse_apply_two', squareCollapse_apply_two', coe_projIcc_of_mem h0, zero_mul,
      zero_mul]

/-- The vertices `0`, `1`, `2` of `Δ²` are the images under `squareCollapse` of `(0, 0)`, `(1, 0)`
and `(1, 1)`. -/
theorem vertex_eq_squareCollapse :
    stdSimplex.vertex (S := ℝ) (0 : Fin 3) = squareCollapse (0, 0) ∧
      stdSimplex.vertex (S := ℝ) (1 : Fin 3) = squareCollapse (1, 0) ∧
      stdSimplex.vertex (S := ℝ) (2 : Fin 3) = squareCollapse (1, 1) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨stdSimplex_three_ext ?_ ?_, stdSimplex_three_ext ?_ ?_, stdSimplex_three_ext ?_ ?_⟩ <;>
    simp only [squareCollapse_apply_one', squareCollapse_apply_two', coe_projIcc_of_mem h0,
      coe_projIcc_of_mem h1] <;>
    simp [stdSimplex.vertex_coe]

open Classical in
/-- The edge correction `Im (∫_τ Ḡ dG - Ḡ(τ₀) G(τ₁))` of a singular `1`-simplex `τ` read
through `G`, when `G` is `C¹` along `τ` (and `0` otherwise). It is unchanged by adding a constant
to `G`. -/
noncomputable def edgeCorrection {Y : TopCat.{0}} (G : Y → ℂ) (τ : Simplex Y 1) : ℂ :=
  if ContDiffOn ℝ 1 (fun t ↦ G (τ (ptI t))) (Set.Icc 0 1) then
    (((∫ t in (0 : ℝ)..1, star (G (τ (ptI t))) * deriv (fun s ↦ G (τ (ptI s))) t) -
      star (G (τ (ptI 0))) * G (τ (ptI 1))).im : ℂ)
  else 0

/-- `edgeCorrection G τ` depends only on the values of `G` along `τ`. -/
theorem edgeCorrection_congr {Y : TopCat.{0}} {G G' : Y → ℂ} {τ : Simplex Y 1}
    (h : ∀ x, G (τ x) = G' (τ x)) : edgeCorrection G τ = edgeCorrection G' τ := by
  have e : (fun t ↦ G (τ (ptI t))) = fun t ↦ G' (τ (ptI t)) := funext fun t ↦ h _
  unfold edgeCorrection
  rw [e]
  simp only [h]

/-- `edgeCorrection G τ` is unchanged by adding a constant to `G`. -/
theorem edgeCorrection_add_const {Y : TopCat.{0}} (G : Y → ℂ) (c : ℂ) (τ : Simplex Y 1) :
    edgeCorrection (fun z ↦ G z + c) τ = edgeCorrection G τ := by
  set g : ℝ → ℂ := fun t ↦ G (τ (ptI t)) with hg
  have hC : ContDiffOn ℝ 1 (fun t ↦ G (τ (ptI t)) + c) (Set.Icc 0 1) ↔
      ContDiffOn ℝ 1 g (Set.Icc 0 1) :=
    ⟨fun h ↦ by simpa using h.sub (contDiffOn_const (c := c)), fun h ↦ h.add contDiffOn_const⟩
  unfold edgeCorrection
  by_cases h : ContDiffOn ℝ 1 g (Set.Icc 0 1)
  · rw [if_pos (hC.2 h), if_pos h]
    have hd : deriv (fun s ↦ G (τ (ptI s)) + c) = deriv g := funext fun t ↦ deriv_add_const c
    rw [hd]
    have hdc : ContinuousOn (derivWithin g (Set.Icc 0 1)) (Set.Icc 0 1) :=
      h.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
    have hEq : Set.EqOn (derivWithin g (Set.Icc 0 1)) (deriv g) (Set.uIoo 0 1) := fun t ht ↦ by
      rw [Set.uIoo_of_le zero_le_one] at ht
      exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    have hi1 : IntervalIntegrable (deriv g) MeasureTheory.volume 0 1 :=
      (hdc.intervalIntegrable_of_Icc zero_le_one).congr_uIoo hEq
    have hi2 : IntervalIntegrable (fun t ↦ star (g t) * deriv g t) MeasureTheory.volume 0 1 :=
      ((h.continuousOn.star.mul hdc).intervalIntegrable_of_Icc zero_le_one).congr_uIoo
        fun t ht ↦ congrArg (star (g t) * ·) (hEq ht)
    have hftc : ∫ t in (0 : ℝ)..1, deriv g t = g 1 - g 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one h.continuousOn
        (fun t ht ↦ ((h.differentiableOn one_ne_zero t
          (Set.Ioo_subset_Icc_self ht)).differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt) hi1
    have hsplit : (∫ t in (0 : ℝ)..1, star (G (τ (ptI t)) + c) * deriv g t) =
        (∫ t in (0 : ℝ)..1, star (g t) * deriv g t) + star c * (g 1 - g 0) := by
      rw [← hftc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi2
        (hi1.const_mul _)]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      simp only [hg, star_add]
      ring
    rw [hsplit]
    congr 1
    simp only [hg, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.sub_re, map_add]
    ring
  · rw [if_neg (mt hC.1 h), if_neg h]

/-- A locally constant function on a set takes the same value at all points of a simplex lying
in that set. -/
theorem apply_eq_of_eventually {Y : TopCat.{0}} {k : ℕ} (τ : Simplex Y k) {f : Y → ℂ}
    {A : Set Y} (hτ : Set.range τ ⊆ A) (hf : ∀ w ∈ A, ∀ᶠ z in nhds w, f z = f w)
    (s t : stdSimplex ℝ (Fin (k + 1))) : f (τ s) = f (τ t) := by
  have hlc : IsLocallyConstant fun t ↦ f (τ t) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦
      (τ.continuous.tendsto t).eventually (hf (τ t) (hτ ⟨t, rfl⟩))
  exact hlc.apply_eq_of_preconnectedSpace _ _

/-- **Green's theorem on a singular triangle.** If `G₀ ∘ σ ∘ s = G` on the unit square, for the
collapse `s` of the square onto `Δ²` and a `C²` map `G` near the square, then twice the area
`Im (\overline{p₁ - p₀} (p₂ - p₀))` of the triangle with vertices `pᵢ = G₀(σ(vᵢ))` is the integral
of the Jacobian of `G` minus the alternating sum of the edge corrections of the faces of `σ`. -/
theorem im_cross_eq_integral_sub_edgeCorrection {Y : TopCat.{0}} (G₀ : Y → ℂ)
    (σ : Simplex Y (1 + 1)) {G : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsub : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U) (hG : ContDiffOn ℝ 2 G U)
    (hGσ : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, G p = G₀ (σ (squareCollapse p))) :
    ((star (G₀ (σ (stdSimplex.vertex 1)) - G₀ (σ (stdSimplex.vertex 0))) *
        (G₀ (σ (stdSimplex.vertex 2)) - G₀ (σ (stdSimplex.vertex 0)))).im : ℂ) =
      ((2 * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          (star (fderiv ℝ G (x, y) (1, 0)) * fderiv ℝ G (x, y) (0, 1)).im : ℝ) : ℂ) -
        (edgeCorrection G₀ (σ.comp (face 1 0)) - edgeCorrection G₀ (σ.comp (face 1 1)) +
          edgeCorrection G₀ (σ.comp (face 1 2))) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hGd : ∀ p ∈ U, HasFDerivAt G (fderiv ℝ G p) p := fun p hp ↦
    ((hG.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hDc : ContinuousOn (fderiv ℝ G) U :=
    (hG.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn
  have hedge : ∀ (τ : Simplex Y 1) (γ : ℝ → ℝ × ℝ) (v : ℝ × ℝ), ContDiff ℝ 2 γ →
      (∀ t, HasDerivAt γ v t) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, τ (ptI t) = σ (squareCollapse (γ t))) →
      edgeCorrection G₀ τ = (((∫ t in (0 : ℝ)..1, (star (G (γ t)) * fderiv ℝ G (γ t) v).im) -
        (star (G (γ 0)) * G (γ 1)).im : ℝ) : ℂ) := by
    intro τ γ v hγ hγd hγs hτ
    have heq : ∀ t ∈ Set.Icc (0 : ℝ) 1, G₀ (τ (ptI t)) = G (γ t) := fun t ht ↦ by
      rw [hτ t ht, hGσ _ (hγs t ht)]
    have hIcc : Set.Icc (0 : ℝ) 1 ⊆ γ ⁻¹' U := fun t ht ↦ hsub (hγs t ht)
    have hC2 : ContDiffOn ℝ 2 (fun t ↦ G (γ t)) (γ ⁻¹' U) :=
      hG.comp hγ.contDiffOn fun _ ht ↦ ht
    have hC1 : ContDiffOn ℝ 1 (fun t ↦ G₀ (τ (ptI t))) (Set.Icc 0 1) :=
      ((hC2.mono hIcc).of_le (by norm_num)).congr heq
    have hcont : ContinuousOn (fun t ↦ star (G (γ t)) * fderiv ℝ G (γ t) v) (Set.Icc 0 1) :=
      ((hG.continuousOn.comp hγ.continuous.continuousOn fun t ht ↦ hIcc ht).star).mul
        ((hDc.comp hγ.continuous.continuousOn fun t ht ↦ hIcc ht).clm_apply continuousOn_const)
    have hint : (∫ t in (0 : ℝ)..1, star (G₀ (τ (ptI t))) * deriv (fun s ↦ G₀ (τ (ptI s))) t) =
        ∫ t in (0 : ℝ)..1, star (G (γ t)) * fderiv ℝ G (γ t) v := by
      rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
      have htI := Set.Ioo_subset_Icc_self ht
      have hev : (fun s ↦ G₀ (τ (ptI s))) =ᶠ[nhds t] fun s ↦ G (γ s) := by
        filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
        exact heq s hs
      rw [heq t htI, hev.deriv_eq]
      exact congrArg _ ((hGd _ (hIcc htI)).comp_hasDerivAt t (hγd t)).deriv
    rw [edgeCorrection, if_pos hC1, hint, heq 0 h0, heq 1 h1]
    congr 1
    rw [Complex.sub_im, im_intervalIntegral_of_continuousOn hcont]
  have e2 := hedge (σ.comp (face 1 2)) (fun t ↦ (t, 0)) (1, 0)
    (contDiff_id.prodMk contDiff_const) (fun t ↦ (hasDerivAt_id' t).prodMk (hasDerivAt_const t 0))
    (fun t ht ↦ ⟨ht, h0⟩) (fun t ht ↦ congrArg σ (face_two_ptI ht))
  have e0 := hedge (σ.comp (face 1 0)) (fun t ↦ (1, t)) (0, 1)
    (contDiff_const.prodMk contDiff_id) (fun t ↦ (hasDerivAt_const t 1).prodMk (hasDerivAt_id' t))
    (fun t ht ↦ ⟨h1, ht⟩) (fun t ht ↦ congrArg σ (face_zero_ptI ht))
  have e1 := hedge (σ.comp (face 1 1)) (fun t ↦ (t, 1)) (1, 0)
    (contDiff_id.prodMk contDiff_const) (fun t ↦ (hasDerivAt_id' t).prodMk (hasDerivAt_const t 1))
    (fun t ht ↦ ⟨ht, h1⟩) (fun t ht ↦ congrArg σ (face_one_ptI ht))
  obtain ⟨hv0, hv1, hv2⟩ := vertex_eq_squareCollapse
  have p0 : G₀ (σ (stdSimplex.vertex 0)) = G (0, 0) := by
    rw [hGσ _ ⟨h0, h0⟩]; exact congrArg (fun t ↦ G₀ (σ t)) hv0
  have p1 : G₀ (σ (stdSimplex.vertex 1)) = G (1, 0) := by
    rw [hGσ _ ⟨h1, h0⟩]; exact congrArg (fun t ↦ G₀ (σ t)) hv1
  have p2 : G₀ (σ (stdSimplex.vertex 2)) = G (1, 1) := by
    rw [hGσ _ ⟨h1, h1⟩]; exact congrArg (fun t ↦ G₀ (σ t)) hv2
  have hG01 : G (0, 1) = G (0, 0) := by
    rw [hGσ _ ⟨h0, h1⟩, hGσ _ ⟨h0, h0⟩, squareCollapse_zero_left]
  have hzero : (∫ y in (0 : ℝ)..1, (star (G (0, y)) * fderiv ℝ G (0, y) (0, 1)).im) = 0 := by
    rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine (MeasureTheory.setIntegral_congr_fun (g := fun _ ↦ (0 : ℝ)) measurableSet_Ioo
      fun y hy ↦ ?_).trans (by simp)
    have hyI := Set.Ioo_subset_Icc_self hy
    have hd := (hGd _ (hsub ⟨h0, hyI⟩)).comp_hasDerivAt y
      ((hasDerivAt_const y (0 : ℝ)).prodMk (hasDerivAt_id' y))
    have hc : HasDerivAt (fun y' ↦ G (0, y')) 0 y := by
      refine (hasDerivAt_const y (G (0, 0))).congr_of_eventuallyEq ?_
      filter_upwards [Icc_mem_nhds hy.1 hy.2] with y' hy'
      rw [hGσ _ ⟨h0, hy'⟩, hGσ _ ⟨h0, h0⟩, squareCollapse_zero_left]
    have := hd.unique hc
    simp [this]
  have hgreen := integral_im_jacobian_eq_boundary hU hsub hG
  rw [e0, e1, e2, p0, p1, p2, hG01]
  have key : (star (G (1, 0) - G (0, 0)) * (G (1, 1) - G (0, 0))).im =
      2 * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          (star (fderiv ℝ G (x, y) (1, 0)) * fderiv ℝ G (x, y) (0, 1)).im) -
        ((((∫ t in (0 : ℝ)..1, (star (G (1, t)) * fderiv ℝ G (1, t) (0, 1)).im) -
            (star (G (1, 0)) * G (1, 1)).im) -
          ((∫ t in (0 : ℝ)..1, (star (G (t, 1)) * fderiv ℝ G (t, 1) (1, 0)).im) -
            (star (G (0, 0)) * G (1, 1)).im)) +
          ((∫ t in (0 : ℝ)..1, (star (G (t, 0)) * fderiv ℝ G (t, 0) (1, 0)).im) -
            (star (G (0, 0)) * G (1, 0)).im)) := by
    rw [hgreen, hzero]
    simp only [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [key]
  push_cast
  ring

/-- **The edge corrections of local primitives glue.** If `F y₁ - F y₂` is locally constant on
`B y₁ ∩ B y₂`, there is a `1`-cochain `κ` with `Im (\overline{p₁ - p₀} (p₂ - p₀)) =
2 ∬ Jac - δκ(σ)` on every singular triangle `σ` in some `B y` along which `F y` is `C²`. -/
theorem exists_im_cross_eq_integral_sub_coboundary {Y : TopCat.{0}} (B : Y → Set Y)
    (F : Y → Y → ℂ)
    (hcomp : ∀ y₁ y₂, ∀ w ∈ B y₁ ∩ B y₂, ∀ᶠ z in nhds w, F y₁ z - F y₂ z = F y₁ w - F y₂ w) :
    ∃ κ : Simplex Y 1 → ℂ, ∀ (σ : Simplex Y (1 + 1)) (y : Y), Set.range σ ⊆ B y →
      ∀ {G : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)}, IsOpen U →
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U → ContDiffOn ℝ 2 G U →
        (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, G p = F y (σ (squareCollapse p))) →
        ((star (F y (σ (stdSimplex.vertex 1)) - F y (σ (stdSimplex.vertex 0))) *
            (F y (σ (stdSimplex.vertex 2)) - F y (σ (stdSimplex.vertex 0)))).im : ℂ) =
          ((2 * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
              (star (fderiv ℝ G (x, y) (1, 0)) * fderiv ℝ G (x, y) (0, 1)).im : ℝ) : ℂ) -
            coboundary ℂ 1 κ σ := by
  obtain ⟨κ, hκ⟩ := exists_cochain_of_forall_eq (Y := Y) B (fun y τ ↦ edgeCorrection (F y) τ)
    fun τ y₁ y₂ h₁ h₂ ↦ by
      have h₁₂ : Set.range τ ⊆ B y₁ ∩ B y₂ := Set.subset_inter h₁ h₂
      have hc := apply_eq_of_eventually τ (f := fun z ↦ F y₁ z - F y₂ z) h₁₂
        (fun w hw ↦ hcomp y₁ y₂ w hw)
      rw [edgeCorrection_congr (G' := fun z ↦ F y₂ z +
        (F y₁ (τ (stdSimplex.vertex 0)) - F y₂ (τ (stdSimplex.vertex 0)))) fun x ↦ by
          have := hc x (stdSimplex.vertex 0)
          linear_combination this, edgeCorrection_add_const]
  refine ⟨κ, fun σ y hσ G U hU hsub hG hGσ ↦ ?_⟩
  have hface : ∀ k : Fin 3, Set.range (σ.comp (face 1 k)) ⊆ B y :=
    fun k _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  rw [im_cross_eq_integral_sub_edgeCorrection (F y) σ hU hsub hG hGσ, coboundary_apply,
    Fin.sum_univ_three, hκ _ y (hface 0), hκ _ y (hface 1), hκ _ y (hface 2)]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_mul,
    neg_one_mul]
  ring

/-- **The Jacobian of a holomorphic function of an oriented map.** For `H` holomorphic on `ℂ¹`
and `g` real differentiable, the Jacobian `Im (\overline{∂₁ (H ∘ g)} ∂₂ (H ∘ g))` is
`|H'|²` times that of `g`. -/
theorem im_star_fderiv_comp_eq {H : (Fin 1 → ℂ) → ℂ} {g : ℝ × ℝ → (Fin 1 → ℂ)}
    {p : ℝ × ℝ} (hH : DifferentiableAt ℂ H (g p)) (hg : DifferentiableAt ℝ g p) :
    (star (fderiv ℝ (H ∘ g) p (1, 0)) * fderiv ℝ (H ∘ g) p (0, 1)).im =
      Complex.normSq (fderiv ℂ H (g p) fun _ ↦ 1) *
        (star (fderiv ℝ g p (1, 0) 0) * fderiv ℝ g p (0, 1) 0).im := by
  rw [fderiv_comp p (hH.restrictScalars ℝ) hg, hH.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  exact im_star_mul_eq_normSq_mul _ _ _

/-- **Evaluation of the area cocycle on a cycle of `C²` triangles.** If `Ψ` is, on triangles in
`B y`, twice the area of the triangle of the values of `F y` at the vertices, then on a cycle `z`
whose triangles are `C²` for `F y` (`G σ = F y ∘ σ ∘ s` on the square) the value of `Ψ` is the
weighted sum of twice the integrals of the Jacobians of the `G σ`: the edge corrections cancel. -/
theorem eval_eq_sum_integral {Y : TopCat.{0}} (B : Y → Set Y) (F : Y → Y → ℂ)
    (hcomp : ∀ y₁ y₂, ∀ w ∈ B y₁ ∩ B y₂, ∀ᶠ z in nhds w, F y₁ z - F y₂ z = F y₁ w - F y₂ w)
    (Ψ : Simplex Y (1 + 1) → ℂ)
    (hΨ : ∀ (σ : Simplex Y (1 + 1)) (y : Y), Set.range σ ⊆ B y →
      Ψ σ = ((star (F y (σ (stdSimplex.vertex 1)) - F y (σ (stdSimplex.vertex 0))) *
        (F y (σ (stdSimplex.vertex 2)) - F y (σ (stdSimplex.vertex 0)))).im : ℂ))
    (z : Simplex Y (1 + 1) →₀ ℂ) (hz : bd ℂ 1 z = 0) (r : Simplex Y (1 + 1) → ℝ)
    (G : Simplex Y (1 + 1) → ℝ × ℝ → ℂ)
    (hgood : ∀ σ ∈ z.support, z σ = r σ ∧ ∃ y, Set.range σ ⊆ B y ∧ ∃ U : Set (ℝ × ℝ),
      IsOpen U ∧ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ 2 (G σ) U ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, G σ p = F y (σ (squareCollapse p))) :
    SingularCochain.eval Ψ z = ((∑ σ ∈ z.support, r σ * (2 * ∫ x in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..1, (star (fderiv ℝ (G σ) (x, y) (1, 0)) *
        fderiv ℝ (G σ) (x, y) (0, 1)).im) : ℝ) : ℂ) := by
  obtain ⟨κ, hκ⟩ := exists_im_cross_eq_integral_sub_coboundary B F hcomp
  have h0 : SingularCochain.eval (coboundary ℂ 1 κ) z = 0 := by
    rw [eval_coboundary, hz]
    simp [SingularCochain.eval]
  rw [SingularCochain.eval, Finsupp.linearCombination_apply, Finsupp.sum] at h0 ⊢
  have hsplit : ∑ σ ∈ z.support, z σ • Ψ σ =
      ∑ σ ∈ z.support, (z σ • Ψ σ + z σ • coboundary ℂ 1 κ σ) := by
    rw [Finset.sum_add_distrib, h0, add_zero]
  rw [hsplit]
  push_cast
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  obtain ⟨hr, y, hy, U, hU, hsub, hG, hGσ⟩ := hgood σ hσ
  have e := hκ σ y hy hU hsub hG hGσ
  rw [← hΨ σ y hy] at e
  rw [← smul_add, e, hr, smul_eq_mul]
  push_cast
  ring

/-- Cocycles with proportional classes take proportional values on cycles. -/
theorem eval_eq_mul_of_ofCocycle_eq_smul {Y : TopCat.{0}} {k : ℕ}
    {φ ψ : Simplex Y (k + 1) → ℂ} (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) (k + 1))
    (hψ : ψ ∈ relCocycles ℂ (Set.univᶜ : Set Y) (k + 1)) {s : ℂ}
    (h : cohomologyWithSupports.ofCocycle ℂ Y (k + 1) φ hφ =
      s • cohomologyWithSupports.ofCocycle ℂ Y (k + 1) ψ hψ)
    {z : Simplex Y (k + 1) →₀ ℂ} (hz : bd ℂ k z = 0) :
    SingularCochain.eval φ z = s * SingularCochain.eval ψ z := by
  have h0 : cohomologyWithSupports.ofCocycle ℂ Y (k + 1) (φ - s • ψ)
      (sub_mem hφ (Submodule.smul_mem _ s hψ)) = 0 := by
    rw [ofCocycle_sub hφ (Submodule.smul_mem _ s hψ), ofCocycle_smul hψ, h, sub_self]
  rw [ofCocycle_eq_zero_iff] at h0
  obtain ⟨β, -, hβ⟩ := h0
  have e := congrArg (fun c ↦ SingularCochain.eval c z) hβ
  rw [eval_coboundary, hz] at e
  simp only [SingularCochain.eval, Finsupp.linearCombination_apply, Finsupp.sum, map_zero,
    Finsupp.support_zero, Finset.sum_empty, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hσ : ∀ σ, z σ * φ σ - s * (z σ * ψ σ) = z σ * (φ σ - s * ψ σ) := fun σ ↦ by ring
  simp only [hσ]
  exact e.symm

/-- A function on `ℂ¹` holomorphic on an open set is analytic there. -/
theorem analyticAt_of_differentiableOn_fin_one {D : Set (Fin 1 → ℂ)} (hDo : IsOpen D)
    {Φ : (Fin 1 → ℂ) → ℂ} (hΦ : DifferentiableOn ℂ Φ D) {z : Fin 1 → ℂ} (hz : z ∈ D) :
    AnalyticAt ℂ Φ z := by
  let φ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hd' : DifferentiableOn ℂ (Φ ∘ φ.symm) (φ.symm ⁻¹' D) :=
    hΦ.comp (φ.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).differentiableOn fun _ h ↦ h
  have ha := hd'.analyticAt ((hDo.preimage φ.symm.continuous).mem_nhds
    (show φ.symm (φ z) ∈ D by simpa using hz))
  have hΦφ : Φ = (Φ ∘ φ.symm) ∘ φ := by ext; simp
  rw [hΦφ]
  exact ha.comp ((φ : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt z)

/-- A nonzero linear form on `ℂ¹` does not vanish on a nonzero vector. -/
theorem clm_fin_one_apply_ne_zero {L : (Fin 1 → ℂ) →L[ℂ] ℂ} (hL : L ≠ 0)
    {u : Fin 1 → ℂ} (hu : u ≠ 0) : L u ≠ 0 := by
  have e : ∀ w : Fin 1 → ℂ, w = w 0 • (fun _ ↦ (1 : ℂ)) := fun w ↦ by ext i; fin_cases i; simp
  have hL1 : L (fun _ ↦ 1) ≠ 0 := fun h ↦ hL (ContinuousLinearMap.ext fun w ↦ by
    rw [e w, map_smul, h, smul_zero, ContinuousLinearMap.zero_apply])
  have hu0 : u 0 ≠ 0 := fun h ↦ hu (by rw [e u, h, zero_smul])
  rw [e u, map_smul, smul_eq_mul]
  exact mul_ne_zero hu0 hL1

/-- **Transition maps of étale coordinates are biholomorphic**: on a curve, the derivative of a
transition map does not vanish. -/
theorem fderiv_transition_apply_ne_zero [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (c c' : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1) {v : Fin 1 → ℂ}
    (hv : v ∈ (c.toOpenPartialHomeomorph.symm.trans c'.toOpenPartialHomeomorph).source) :
    fderiv ℂ (c.toOpenPartialHomeomorph.symm.trans c'.toOpenPartialHomeomorph) v
      (fun _ ↦ 1) ≠ 0 := by
  set T := c.toOpenPartialHomeomorph.symm.trans c'.toOpenPartialHomeomorph
  set T' := c'.toOpenPartialHomeomorph.symm.trans c.toOpenPartialHomeomorph
  have hvs : v ∈ c.toOpenPartialHomeomorph.target ∧
      c.toOpenPartialHomeomorph.symm v ∈ c'.toOpenPartialHomeomorph.source := by
    simpa [T, OpenPartialHomeomorph.trans_source] using hv
  have hT := ComplexPoints.EtaleCoordinateChart.analyticOnNhd_transition c c' v hv
  have hTv : T v ∈ T'.source := by
    simp only [T, T', OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    refine ⟨c'.toOpenPartialHomeomorph.map_source hvs.2, ?_⟩
    rw [c'.toOpenPartialHomeomorph.left_inv hvs.2]
    exact c.toOpenPartialHomeomorph.map_target hvs.1
  have hT' := ComplexPoints.EtaleCoordinateChart.analyticOnNhd_transition c' c (T v) hTv
  have hinv : (fun w ↦ T' (T w)) =ᶠ[nhds v] id := by
    filter_upwards [T.open_source.mem_nhds hv] with w hw
    have hws : w ∈ c.toOpenPartialHomeomorph.target ∧
        c.toOpenPartialHomeomorph.symm w ∈ c'.toOpenPartialHomeomorph.source := by
      simpa [T, OpenPartialHomeomorph.trans_source] using hw
    simp only [T, T', OpenPartialHomeomorph.coe_trans, Function.comp_apply, id]
    rw [c'.toOpenPartialHomeomorph.left_inv hws.2, c.toOpenPartialHomeomorph.right_inv hws.1]
  have hcomp := hT'.differentiableAt.hasFDerivAt.comp v hT.differentiableAt.hasFDerivAt
  have hid := (hasFDerivAt_id (𝕜 := ℂ) v).congr_of_eventuallyEq hinv
  have heq := hcomp.unique hid
  intro h0
  have h0' : (fderiv ℂ (c.toOpenPartialHomeomorph.symm.trans c'.toOpenPartialHomeomorph) v)
      (fun _ ↦ 1) = 0 := h0
  have := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ) ↦ L (fun _ ↦ 1)) heq
  simp only [ContinuousLinearMap.comp_apply, h0', map_zero, ContinuousLinearMap.id_apply] at this
  exact one_ne_zero (congrFun this 0).symm

/-- **A holomorphic function of étale coordinates along a `C²` map.** If `g` is `C²` on `U` with
values in the target of an étale chart `c`, and `Φ` is holomorphic on an open `D` in the
coordinates of a chart `c₀`, then `p ↦ Φ (c₀ (c⁻¹ (g p)))` is `C²` near every compact `K ⊆ U`
along which `c⁻¹ ∘ g` stays in `c₀⁻¹ D`, with Jacobian `|H'|²` times that of `g`, for the
holomorphic `H = Φ ∘ c₀ ∘ c⁻¹`. -/
theorem exists_contDiffOn_chartTriangle [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (c c₀ : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1) {D : Set (Fin 1 → ℂ)}
    (hDo : IsOpen D) {Φ : (Fin 1 → ℂ) → ℂ} (hΦ : DifferentiableOn ℂ Φ D)
    {g : ℝ × ℝ → (Fin 1 → ℂ)} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hgt : Set.MapsTo g U c.toOpenPartialHomeomorph.target) {K : Set (ℝ × ℝ)} (hK : K ⊆ U)
    (hKB : ∀ p ∈ K, c.toOpenPartialHomeomorph.symm (g p) ∈
      c₀.toOpenPartialHomeomorph.source ∩ c₀.toOpenPartialHomeomorph ⁻¹' D) :
    ∃ U' : Set (ℝ × ℝ), IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧
      ContDiffOn ℝ 2 (fun p ↦ Φ (c₀.toOpenPartialHomeomorph
        (c.toOpenPartialHomeomorph.symm (g p)))) U' ∧
      ∀ p ∈ U', (star (fderiv ℝ (fun p ↦ Φ (c₀.toOpenPartialHomeomorph
          (c.toOpenPartialHomeomorph.symm (g p)))) p (1, 0)) *
          fderiv ℝ (fun p ↦ Φ (c₀.toOpenPartialHomeomorph
            (c.toOpenPartialHomeomorph.symm (g p)))) p (0, 1)).im =
        Complex.normSq (fderiv ℂ (fun v ↦ Φ (c₀.toOpenPartialHomeomorph
          (c.toOpenPartialHomeomorph.symm v))) (g p) fun _ ↦ 1) *
          (star (fderiv ℝ g p (1, 0) 0) * fderiv ℝ g p (0, 1) 0).im := by
  set T := c.toOpenPartialHomeomorph.symm.trans c₀.toOpenPartialHomeomorph
  set S : Set (Fin 1 → ℂ) := T.source ∩ T ⁻¹' D
  have hSo : IsOpen S := T.isOpen_inter_preimage hDo
  have hH : ∀ v ∈ S, AnalyticAt ℂ (fun v ↦ Φ (c₀.toOpenPartialHomeomorph
      (c.toOpenPartialHomeomorph.symm v))) v := fun v hv ↦
    (analyticAt_of_differentiableOn_fin_one hDo hΦ hv.2).comp
      (ComplexPoints.EtaleCoordinateChart.analyticOnNhd_transition c c₀ v hv.1)
  refine ⟨U ∩ g ⁻¹' S, hg.continuousOn.isOpen_inter_preimage hU hSo, fun p hp ↦ ⟨hK hp, ?_⟩,
    Set.inter_subset_left, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · refine ⟨?_, (hKB p hp).2⟩
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨hgt (hK hp), (hKB p hp).1⟩
  · exact (((hH _ hp.2).contDiffAt.restrict_scalars ℝ).comp p
      (hg.contDiffAt (hU.mem_nhds hp.1))).contDiffWithinAt
  · exact im_star_fderiv_comp_eq (hH _ hp.2).differentiableAt
      ((hg.contDiffAt (hU.mem_nhds hp.1)).differentiableAt (by norm_num))

/-- A nonnegative function continuous on the unit square and positive at one of its points has
positive integral. -/
theorem integral_square_pos {J : ℝ × ℝ → ℝ}
    (hJ : ContinuousOn J (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (h0 : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ J p)
    {p : ℝ × ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (hpos : 0 < J p) :
    0 < ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, J (x, y) := by
  have hrow : ∀ x ∈ Set.Icc (0 : ℝ) 1, ContinuousOn (fun y ↦ J (x, y)) (Set.Icc 0 1) :=
    fun x hx ↦ hJ.comp (by fun_prop) fun y hy ↦ ⟨hx, hy⟩
  refine intervalIntegral.integral_pos zero_lt_one
    (continuousOn_intervalIntegral_of_continuousOn_square hJ)
    (fun x hx ↦ intervalIntegral.integral_nonneg zero_le_one fun y hy ↦
      h0 _ ⟨Set.Ioc_subset_Icc_self hx, hy⟩) ⟨p.1, hp.1, ?_⟩
  exact intervalIntegral.integral_pos zero_lt_one (hrow _ hp.1)
    (fun y hy ↦ h0 _ ⟨hp.1, Set.Ioc_subset_Icc_self hy⟩) ⟨p.2, hp.2, hpos⟩

variable (X) in
/-- **Fine fundamental cycles of oriented chart triangles.** A smooth projective curve `X` has
fine fundamental chart cycles if, for every open neighbourhood `B y` of each point `y` of
`X(ℂ)`, there is a singular `2`-cycle `z = ∑ r_σ σ` of `X^an` with real coefficients whose class
is the fundamental class of `X`, each triangle lying in some `B y` and being, on the unit square
through the collapse `squareCollapse`, an étale chart read of a `C²` map `g_σ` whose Jacobian has
the sign of `r_σ`, and the triangles reaching every open set at points where `r_σ` times the
Jacobian is positive. -/
def HasFundamentalChartCycle : Prop :=
  ∀ [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))],
  haveI : IsComplexScheme X := MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  haveI : IsIntegral X :=
    (inferInstance : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ))).toIsIntegral
  ∀ (B : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ)))),
    (∀ y, IsOpen (B y)) → (∀ y, y ∈ B y) →
    ∃ (z : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →₀ ℂ)
      (r : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℝ)
      (Y' : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →
        ComplexPoints (X ↘ Spec (.of ℂ)))
      (c : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →
        ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1)
      (g : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℝ × ℝ → (Fin 1 → ℂ))
      (U : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → Set (ℝ × ℝ))
      (hz : bd ℂ 1 z = 0),
      (∀ σ ∈ z.support, z σ = r σ ∧ Set.range σ ⊆ B (Y' σ) ∧ IsOpen (U σ) ∧
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U σ ∧ ContDiffOn ℝ 2 (g σ) (U σ) ∧
        Set.MapsTo (g σ) (U σ) (c σ).toOpenPartialHomeomorph.target ∧
        (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
          σ (squareCollapse p) = (c σ).toOpenPartialHomeomorph.symm (g σ p)) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, ∀ i : Fin 1,
          0 ≤ r σ * (star (fderiv ℝ (g σ) p (1, 0) i) * fderiv ℝ (g σ) p (0, 1) i).im) ∧
      (∀ W : Set (ComplexPoints (X ↘ Spec (.of ℂ))), IsOpen W → W.Nonempty →
        ∃ σ ∈ z.support, ∃ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
          σ (squareCollapse p) ∈ W ∧ ∀ i : Fin 1,
            0 < r σ * (star (fderiv ℝ (g σ) p (1, 0) i) * fderiv ℝ (g σ) p (0, 1) i).im) ∧
      IsVarietyFundamentalClass ℂ
        (PolarizationPositivity.natCast_one_eq_dimension
          PolarizationPositivity.topologicalKrullDim_eq_one)
        (PolarizationPositivity.finiteCycleClass (Y := TopCat.of (UnderlyingSpace ℂ X))
          (postcomp ℂ ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩ (1 + 1) z)
          (PolarizationPositivity.bd_postcomp_homeomorphUnderlyingSpace_eq_zero hz))

/-- **A fine fundamental cycle of oriented chart triangles.** Given fine fundamental chart
cycles, for every open neighbourhood `B y` of each point `y` of a smooth projective curve, there
is a singular `2`-cycle `z = ∑ r_σ σ` with real coefficients, each triangle lying in some `B y`
and being, on the unit square through the collapse `s`, an étale chart read of a `C²` map `g_σ`
whose Jacobian has the sign of `r_σ`; the triangles reach every open set at points where `r_σ`
times the Jacobian is positive; and the first Chern class of the given ample `L` takes a positive
real value on `z`, namely `deg L`. -/
theorem HasFundamentalChartCycle.exists_fundamental_chart_cycle
    (hcyc : HasFundamentalChartCycle X) (h1 : n = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L)
    (B : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))))
    (hBo : ∀ y, IsOpen (B y)) (hmem : ∀ y, y ∈ B y) :
    ∃ (z : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →₀ ℂ)
      (r : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℝ)
      (Y' : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →
        ComplexPoints (X ↘ Spec (.of ℂ)))
      (c : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →
        ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n)
      (g : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℝ × ℝ → (Fin n → ℂ))
      (U : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → Set (ℝ × ℝ)),
      bd ℂ 1 z = 0 ∧
      (∀ σ ∈ z.support, z σ = r σ ∧ Set.range σ ⊆ B (Y' σ) ∧ IsOpen (U σ) ∧
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U σ ∧ ContDiffOn ℝ 2 (g σ) (U σ) ∧
        Set.MapsTo (g σ) (U σ) (c σ).toOpenPartialHomeomorph.target ∧
        (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
          σ (squareCollapse p) = (c σ).toOpenPartialHomeomorph.symm (g σ p)) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, ∀ i : Fin n,
          0 ≤ r σ * (star (fderiv ℝ (g σ) p (1, 0) i) * fderiv ℝ (g σ) p (0, 1) i).im) ∧
      (∀ W : Set (ComplexPoints (X ↘ Spec (.of ℂ))), IsOpen W → W.Nonempty →
        ∃ σ ∈ z.support, ∃ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
          σ (squareCollapse p) ∈ W ∧ ∀ i : Fin n,
            0 < r σ * (star (fderiv ℝ (g σ) p (1, 0) i) * fderiv ℝ (g σ) p (0, 1) i).im) ∧
      ∀ (χ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℂ)
        (hχ : χ ∈ relCocycles ℂ
          (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) (1 + 1)),
        cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ =
          singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) →
        ∃ q : ℝ, 0 < q ∧ SingularCochain.eval χ z = q := by
  subst h1
  haveI : IsComplexScheme X := MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  haveI : IsIntegral X :=
    (inferInstance : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ))).toIsIntegral
  obtain ⟨z, r, Y', c, g, U, hz, hgood, hdense, hfund⟩ := hcyc B hBo hmem
  exact ⟨z, r, Y', c, g, U, hz, hgood, hdense,
    PolarizationPositivity.exists_pos_eval_eq_of_isAmple z hz hfund L hL⟩

/-- **Positivity on a curve.** For a holomorphic one-form `ω ≠ 0` and `L` ample, `i [ω] ∪
\overline{[ω]}` is a positive multiple of `c₁(L)` in `H²(X^an; ℂ)`: over a fundamental cycle of
orientation-preserving `C¹` chart squares, Stokes makes the integral of `i [ω] ∪ \overline{[ω]}`
equal to `2 ∫ |f|² > 0` in a local coordinate with `ω = f dz`, while that of `c₁(L)` is
`deg L > 0`. -/
theorem HasFundamentalChartCycle.exists_pos_smul_cup_curve (hcyc : HasFundamentalChartCycle X)
    (h1 : n = 1)
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (hω : ω ≠ 0) (hα : IsDR X ω α)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L) :
    ∃ s : ℝ, 0 < s ∧
      Complex.I • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 α (conjH X α) =
        (s : ℂ) •
          singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) := by
  subst h1
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨-, -, hcl⟩ := exists_deRhamCohomology_linearEquiv_singularCohomology
  have hd := (hcl X (X ↘ Spec (.of ℂ)) (MMP.Flips.isSmoothScheme_of_smooth _)).2 ω
  choose c' D Φ Φ₂ hxs hxD hDo hDc hDt hΦ hΦ₂ hP hP₂ hcp using
    fun y ↦ exists_chartPrimitive_pair (n := 1) ω ω hd hd y
  set E := fun y ↦ (c' y).toOpenPartialHomeomorph with hE
  set B : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    fun y ↦ (E y).source ∩ E y ⁻¹' D y with hB
  set F : ComplexPoints (X ↘ Spec (.of ℂ)) → ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ :=
    fun y w ↦ Φ y (E y w) with hF
  have hBo : ∀ y, IsOpen (B y) := fun y ↦ (E y).isOpen_inter_preimage (hDo y)
  have hBm : ∀ y, y ∈ B y := fun y ↦ ⟨hxs y, hxD y⟩
  have hcomp : ∀ y₁ y₂, ∀ w ∈ B y₁ ∩ B y₂, ∀ᶠ x in nhds w,
      F y₁ x - F y₂ x = F y₁ w - F y₂ w := fun y₁ y₂ w hw ↦
    eventually_sub_eq_of_isLocalPrimitive (n := 1) ω (hBo y₁) (hBo y₂) (hP y₁) (hP y₂) hw
  obtain ⟨Ψ, hΨ, hIΨ, hΨv⟩ :=
    exists_smul_cup_conjH_eq_ofCocycle (n := 1) (Or.inl rfl) hα B F hBo hBm hP
  obtain ⟨z, r, Y', c, g, U, hz, hgood, hdense, hc₁⟩ :=
    hcyc.exists_fundamental_chart_cycle (n := 1) rfl L hL B hBo hBm
  obtain ⟨χ, hχ, hχe⟩ := cohomologyWithSupports.exists_ofCocycle_eq (1 + 1)
    (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) :
      analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) (1 + 1))
  obtain ⟨q, hq, hqz⟩ := hc₁ χ hχ hχe
  have hc0 : (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) :
      analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) (2 * 1)) ≠ 0 := by
    intro h0
    have h0' : cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ =
        (0 : ℂ) • cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ := by
      rwa [zero_smul, hχe]
    have := eval_eq_mul_of_ofCocycle_eq_smul hχ hχ h0' hz
    rw [zero_mul, hqz] at this
    exact hq.ne' (by exact_mod_cast this)
  haveI := finiteDimensional_analyticSingularCohomology (X := X) ℂ (2 * 1)
  obtain ⟨s, hs⟩ := exists_smul_eq_of_finrank_le_one
    (finrank_analyticSingularCohomology_two_mul_le_one (n := 1) (X := X) ℂ) hc0
    (Complex.I • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 α (conjH X α))
  have hΨs : cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) Ψ hΨ =
      s • cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ := by
    rw [← hIΨ, hχe]; exact hs.symm
  have hevs := eval_eq_mul_of_ofCocycle_eq_smul hΨ hχ hΨs hz
  rw [hqz] at hevs
  let G : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℝ × ℝ → ℂ :=
    fun σ p ↦ Φ (Y' σ) (E (Y' σ) ((c σ).toOpenPartialHomeomorph.symm (g σ p)))
  have hsqB : ∀ σ ∈ z.support, ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      (c σ).toOpenPartialHomeomorph.symm (g σ p) ∈ B (Y' σ) := fun σ hσ p hp ↦ by
    obtain ⟨-, hrB, -, -, -, -, hσg, -⟩ := hgood σ hσ
    rw [← hσg p hp]
    exact hrB ⟨_, rfl⟩
  have hdata : ∀ σ ∈ z.support, ∃ U' : Set (ℝ × ℝ), IsOpen U' ∧
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U' ∧ U' ⊆ U σ ∧ ContDiffOn ℝ 2 (G σ) U' ∧
      ∀ p ∈ U', (star (fderiv ℝ (G σ) p (1, 0)) * fderiv ℝ (G σ) p (0, 1)).im =
        Complex.normSq (fderiv ℂ (fun v ↦ Φ (Y' σ) (E (Y' σ)
          ((c σ).toOpenPartialHomeomorph.symm v))) (g σ p) fun _ ↦ 1) *
          (star (fderiv ℝ (g σ) p (1, 0) 0) * fderiv ℝ (g σ) p (0, 1) 0).im := fun σ hσ ↦ by
    obtain ⟨-, -, hUo, hsU, hgC, hgt, -, -⟩ := hgood σ hσ
    exact exists_contDiffOn_chartTriangle (c σ) (c' (Y' σ)) (hDo _) (hΦ _) hUo hgC hgt hsU
      (hsqB σ hσ)
  choose! U' hU'o hsU' hU'U hGC hGJ using hdata
  have hGσ : ∀ σ ∈ z.support, ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      G σ p = F (Y' σ) (σ (squareCollapse p)) := fun σ hσ p hp ↦ by
    obtain ⟨-, -, -, -, -, -, hσg, -⟩ := hgood σ hσ
    simp only [G, F, hσg p hp]
  have hev := eval_eq_sum_integral (Y := Analytification.space (X ↘ Spec (.of ℂ))) B F hcomp Ψ
    hΨv z hz r G fun σ hσ ↦ by
      obtain ⟨hr, hrB, -⟩ := hgood σ hσ
      exact ⟨hr, Y' σ, hrB, U' σ, hU'o σ hσ, hsU' σ hσ, hGC σ hσ, hGσ σ hσ⟩
  have hJc : ∀ σ ∈ z.support, ContinuousOn (fun p ↦
      (star (fderiv ℝ (G σ) p (1, 0)) * fderiv ℝ (G σ) p (0, 1)).im)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := fun σ hσ ↦ by
    have hDc : ContinuousOn (fderiv ℝ (G σ)) (U' σ) :=
      ((hGC σ hσ).fderiv_of_isOpen (hU'o σ hσ) (m := 1) (by norm_num)).continuousOn
    exact (Complex.continuous_im.comp_continuousOn
      (((hDc.clm_apply continuousOn_const).star).mul (hDc.clm_apply continuousOn_const))).mono
      (hsU' σ hσ)
  have hJ0 : ∀ σ ∈ z.support, ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      0 ≤ r σ * (star (fderiv ℝ (G σ) p (1, 0)) * fderiv ℝ (G σ) p (0, 1)).im :=
    fun σ hσ p hp ↦ by
      obtain ⟨-, -, -, -, -, -, -, hJac⟩ := hgood σ hσ
      rw [hGJ σ hσ p (hsU' σ hσ hp), mul_left_comm]
      exact mul_nonneg (Complex.normSq_nonneg _) (hJac p hp 0)
  have hrI : ∀ σ, r σ * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      (star (fderiv ℝ (G σ) (x, y) (1, 0)) * fderiv ℝ (G σ) (x, y) (0, 1)).im) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        r σ * (star (fderiv ℝ (G σ) (x, y) (1, 0)) * fderiv ℝ (G σ) (x, y) (0, 1)).im :=
    fun σ ↦ by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ ↦ ?_
      exact (intervalIntegral.integral_const_mul _ _).symm
  have hI0 : ∀ σ ∈ z.support, 0 ≤ r σ * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      (star (fderiv ℝ (G σ) (x, y) (1, 0)) * fderiv ℝ (G σ) (x, y) (0, 1)).im :=
    fun σ hσ ↦ by
      rw [hrI]
      exact intervalIntegral.integral_nonneg zero_le_one fun x hx ↦
        intervalIntegral.integral_nonneg zero_le_one fun y hy ↦ hJ0 σ hσ _ ⟨hx, hy⟩
  obtain ⟨y₀, v₀, hv₀, hv₀d⟩ : ∃ y₀, ∃ v₀ ∈ D y₀, fderiv ℂ (Φ y₀) v₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hω (eq_zero_of_forall_isChartPrimitive (n := 1) fun x ↦
      ⟨c' x, D x, Φ x, hxs x, hxD x, hDo x, hcp x, fun w hw ↦ ?_⟩)
    have h := ((hΦ x w hw).differentiableAt ((hDo x).mem_nhds hw)).hasFDerivAt.restrictScalars ℝ
    rw [hcon x w hw] at h
    simpa using h
  have hΦa : ∀ v ∈ D y₀, AnalyticAt ℂ (Φ y₀) v := fun v hv ↦
    analyticAt_of_differentiableOn_fin_one (hDo y₀) (hΦ y₀) hv
  have hdc : ContinuousOn (fderiv ℂ (Φ y₀)) (D y₀) := fun v hv ↦
    ((hΦa v hv).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num) |>.continuousWithinAt
  set N := D y₀ ∩ fderiv ℂ (Φ y₀) ⁻¹' {0}ᶜ
  have hNo : IsOpen N := hdc.isOpen_inter_preimage (hDo y₀) isOpen_compl_singleton
  set W := (E y₀).source ∩ E y₀ ⁻¹' N
  have hWo : IsOpen W := (E y₀).isOpen_inter_preimage hNo
  have hWne : W.Nonempty := ⟨(E y₀).symm v₀, (E y₀).map_target (hDt y₀ hv₀), by
    show E y₀ ((E y₀).symm v₀) ∈ N
    rw [(E y₀).right_inv (hDt y₀ hv₀)]
    exact ⟨hv₀, hv₀d⟩⟩
  obtain ⟨σ, hσ, p, hp, hpW, hJp⟩ := hdense W hWo hWne
  obtain ⟨-, hrB, -, hsU, -, hgt, hσg, -⟩ := hgood σ hσ
  set w := σ (squareCollapse p)
  have hwB : w ∈ B (Y' σ) ∩ B y₀ := ⟨hrB ⟨_, rfl⟩, hpW.1, hpW.2.1⟩
  have hgpt : g σ p ∈ (c σ).toOpenPartialHomeomorph.target := hgt (hsU hp)
  have hsymm : (c σ).toOpenPartialHomeomorph.symm (g σ p) = w := (hσg p hp).symm
  have hloc : (fun v ↦ Φ (Y' σ) (E (Y' σ) ((c σ).toOpenPartialHomeomorph.symm v))) =ᶠ[nhds (g σ p)]
      fun v ↦ Φ y₀ (E y₀ ((c σ).toOpenPartialHomeomorph.symm v)) +
        (F (Y' σ) w - F y₀ w) := by
    have h := ((c σ).toOpenPartialHomeomorph.continuousAt_symm hgpt).eventually
      (by rw [hsymm]; exact hcomp (Y' σ) y₀ w hwB)
    filter_upwards [h] with v hv
    simp only [F] at hv ⊢
    linear_combination hv
  have hT₀s : g σ p ∈ ((c σ).toOpenPartialHomeomorph.symm.trans (E y₀)).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨hgpt, by rw [Set.mem_preimage, hsymm]; exact hpW.1⟩
  have hT₀a := ComplexPoints.EtaleCoordinateChart.analyticOnNhd_transition (c σ) (c' y₀) _ hT₀s
  have hTw : ((c σ).toOpenPartialHomeomorph.symm.trans (E y₀)) (g σ p) ∈ N := by
    show E y₀ ((c σ).toOpenPartialHomeomorph.symm (g σ p)) ∈ N
    rw [hsymm]; exact hpW.2
  have hderiv : fderiv ℂ (fun v ↦ Φ (Y' σ) (E (Y' σ) ((c σ).toOpenPartialHomeomorph.symm v)))
      (g σ p) (fun _ ↦ 1) ≠ 0 := by
    rw [hloc.fderiv_eq, fderiv_add_const]
    have hc := fderiv_comp (g σ p) (hΦa _ hTw.1).differentiableAt hT₀a.differentiableAt
    have hcomp' : (fun v ↦ Φ y₀ (E y₀ ((c σ).toOpenPartialHomeomorph.symm v))) =
        Φ y₀ ∘ ((c σ).toOpenPartialHomeomorph.symm.trans (E y₀)) := rfl
    rw [hcomp', hc, ContinuousLinearMap.comp_apply]
    exact clm_fin_one_apply_ne_zero hTw.2
      (fderiv_transition_apply_ne_zero (c σ) (c' y₀) hT₀s)
  have hJpos : 0 < r σ * (star (fderiv ℝ (G σ) p (1, 0)) * fderiv ℝ (G σ) p (0, 1)).im := by
    rw [hGJ σ hσ p (hsU' σ hσ hp), mul_left_comm]
    exact mul_pos (Complex.normSq_pos.2 hderiv) (hJp 0)
  have hIpos := integral_square_pos (J := fun p ↦ r σ *
    (star (fderiv ℝ (G σ) p (1, 0)) * fderiv ℝ (G σ) p (0, 1)).im)
    (continuousOn_const.mul (hJc σ hσ)) (hJ0 σ hσ) hp hJpos
  rw [← hrI] at hIpos
  set t := ∑ σ ∈ z.support, r σ * (2 * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
    (star (fderiv ℝ (G σ) (x, y) (1, 0)) * fderiv ℝ (G σ) (x, y) (0, 1)).im) with ht
  have htpos : 0 < t := Finset.sum_pos'
    (fun σ hσ ↦ by rw [mul_left_comm]; exact mul_nonneg zero_le_two (hI0 σ hσ))
    ⟨σ, hσ, by rw [mul_left_comm]; exact mul_pos zero_lt_two hIpos⟩
  rw [hev] at hevs
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨t / q, div_pos htpos hq, ?_⟩
  rw [← hs]
  congr 1
  rw [Complex.ofReal_div, eq_div_iff hq0, ← hevs]

end Decomposition

end MMP.Fourfold.Polarization

end
