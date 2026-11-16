module
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.RingTheory.PowerSeries.CompleteLocalRing
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.Algebra.Homology.SpectralObject.PageIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardZeroAbelianVariety
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms
public import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle

/-!
# The Jacobian of a pointed smooth projective curve over `ℂ`

Let `f : C ⟶ Spec ℂ` be a smooth projective connected curve with a section `σ`. The functor of
degree-zero line bundles on `C` rigidified along `σ`,
`Stacks.RigidifiedPicard.functorZero f hdim σ hσ`, is representable by an abelian variety `J`.
Its tangent space at the identity is `H¹(C, 𝒪_C)`, its dimension is `h¹(C, 𝒪_C)`, and the
identity of `J` corresponds to a universal rigidified degree-zero line bundle on `C × J`.

## Main results

* `MMP.Conductor.exists_jacobian_of_isProjective`: existence of the Jacobian, with its
  tangent space, its dimension, and the universal normalized line bundle.

## Implementation notes

The tangent space at the identity is the space of dotted tangent arrows `DottedTangentArrow`.
It is a vector space over the residue field at the identity, and it is identified with
`H¹(C, 𝒪_C)` semilinearly along `sectionResidueFieldEquiv`, the canonical identification of
that residue field with `ℂ`. Representability is an isomorphism of group-valued functors
`yonedaGrp.obj J ≅ functorZero`. The universal bundle is the class `P` that corresponds to the
identity of `J`: every `T`-point `a` of `J` is the pullback of `P` along `a`. Normalization at
the marked point is built into `functorZero`, whose sections are rigidified along `σ`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel
open scoped CategoryTheory.MonObj TensorProduct
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic Stacks.RigidifiedPicard

namespace MMP.Analytic.Proof_lem_mmp_conductor_curve_jacobian

/-- Finite-dimensional spaces of equal dimension over fields identified by `ρ` are
`ρ`-semilinearly equivalent. -/
private noncomputable def semilinearEquivOfFinrankEq {K L V W : Type*} [Field K] [Field L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    [FiniteDimensional K V] [FiniteDimensional L W] (ρ : K ≃+* L)
    [RingHomInvPair (ρ : K →+* L) (ρ.symm : L →+* K)]
    [RingHomInvPair (ρ.symm : L →+* K) (ρ : K →+* L)]
    (h : Module.finrank K V = Module.finrank L W) : V ≃ₛₗ[(ρ : K →+* L)] W :=
  let b := Module.finBasis K V
  let b' := (Module.finBasis L W).reindex (finCongr h.symm)
  let e : (Fin (Module.finrank K V) → K) ≃ₛₗ[(ρ : K →+* L)] (Fin (Module.finrank K V) → L) :=
    { toFun := fun v i => ρ (v i)
      invFun := fun v i => ρ.symm (v i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun c v => by ext i; simp
      left_inv := fun v => by ext i; simp
      right_inv := fun v => by ext i; simp }
  (b.equivFun.trans e).trans b'.equivFun.symm

open Stacks.SmoothAtJacobian (relativeDifferentialStalk relativeDifferentialStalkModule) in
/-- The tangent space of a morphism locally of finite type is finite-dimensional. -/
private lemma finiteDimensional_dottedTangentArrow {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    FiniteDimensional (X.residueField x) (DottedTangentArrow f x) := by
  letI := relativeDifferentialStalkModule f x
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk x) (X.residueField x) (X.residueField x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : FiniteDimensional (X.residueField x)
      (X.residueField x ⊗[X.presheaf.stalk x] relativeDifferentialStalk f x) :=
    AlgebraicGeometry.finiteDimensional_relativeCotangentSpace f x
  exact LinearEquiv.finiteDimensional ((tangentSpaceEquivCotangentSpace f x).trans
    (LinearMap.liftBaseChangeEquiv (R := X.presheaf.stalk x) (X.residueField x))).symm

end MMP.Analytic.Proof_lem_mmp_conductor_curve_jacobian

namespace MMP.Conductor

open MMP.Analytic.Proof_lem_mmp_conductor_curve_jacobian in
/-- **The Jacobian of a pointed curve.** For a smooth projective connected curve `C` over `ℂ`
with a section `σ`, there is an abelian variety `J` that represents degree-zero line bundles
rigidified along `σ`. The tangent space of `J` at the identity is `H¹(C, 𝒪_C)`,
`dim J = h¹(C, 𝒪_C)`, and there is a universal rigidified line bundle `P` on `C × J`. -/
@[mmp "lem_mmp_conductor_curve_jacobian"]
public theorem exists_jacobian_of_isProjective {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ))
    (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f] [ConnectedSpace C]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    ∃ (J : Grp (Over (Spec (.of ℂ))))
      (e : yonedaGrp.obj J ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
      IsAbelianVariety ℂ J.X ∧
      (haveI := RingHomInvPair.of_ringEquiv
        (sectionResidueFieldEquiv J.X.hom η[J.X].left (Over.w η[J.X]))
      haveI := RingHomInvPair.of_ringEquiv_symm
        (sectionResidueFieldEquiv J.X.hom η[J.X].left (Over.w η[J.X]))
      Nonempty (DottedTangentArrow J.X.hom (η[J.X].left (closedPoint ℂ)) ≃ₛₗ[
        (sectionResidueFieldEquiv J.X.hom η[J.X].left (Over.w η[J.X]) :
          J.X.left.residueField (η[J.X].left (closedPoint ℂ)) →+* ℂ)]
        structureSheafCohomology f 1)) ∧
      Stacks.Groupoids.abelianVarietyDimension J.X =
        Module.finrank ℂ (structureSheafCohomology f 1) ∧
      ∃ P : Stacks.RigidifiedPicard.functorZero f hdim σ hσ |>.obj (op J.X),
        ∀ (T : Over (Spec (.of ℂ))) (a : T ⟶ J.X),
          (e.hom.app (op T)).hom a =
            ((Stacks.RigidifiedPicard.functorZero f hdim σ hσ).map a.op).hom P := by
  haveI := hproj.isProper
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  haveI : IsIntegral C := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f
  haveI : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed ℂ C f
  have h0 := Stacks.WeilCohomology.curveHasOneDimensionalSections ℂ f
  haveI : IsCurve ℂ f := GenusOne.isCurve f h0
  have hdimX : topologicalKrullDim C ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := ℂ) (f :=
      f)).le
  have hpm : IsProjectiveMorphism f := isProjectiveMorphism_of_isProper_of_isCurve ℂ f
  have HH : ∀ d : ℕ, Σ H : Over (Spec (.of ℂ)),
      Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d := fun d =>
    (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism
      (Over.mk f) hpm d).some
  haveI := GenusOne.isEffectiveCartierDivisor f h0 σ hσ
  set θ : Stacks.Picard.ofScheme C := genus f • Stacks.Divisors.picardClass
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point σ}, GenusOne.isClosed_point f σ hσ⟩ : TopologicalSpace.Closeds C))
  have hθ : invertibleCurveDegreeHom ℂ f hdimX θ = genus f := by
    rw [map_nsmul, invertibleCurveDegreeHom_divisorPicardClass_point ℂ f
      hdimX h0 σ hσ, nsmul_eq_mul, mul_one]
  have hθ' : ∀ s, relativeInvertibleDegreeHomAt f hdim s θ = genus f :=
    fun s => by rw [Stacks.RigidifiedPicard.relativeInvertibleDegreeHomAt_spec f hdimX hdim s θ, hθ]
  obtain ⟨A, ⟨e⟩, hP⟩ := Stacks.RigidifiedPicard.exists_grp_iso_functorZero f hdim σ hσ
    (Stacks.RigidifiedPicard.isIso_bcProj_c f σ hσ)
    (perfectDerivedPushforward_of_baseChange
      baseChangeDerivedPushforward)
    baseChangeDerivedPushforward θ hθ' (HH (genus f)).2
    (fun T c => Stacks.WeilCohomology.cohomologyLocusDivisorExistence ℂ f T c)
    (fun T Z Z' => Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness ℂ f T Z Z')
    (Stacks.RigidifiedPicard.exists_translate_mem_cohomologySubfunctorZero f hdimX hdim σ hσ θ
      (fun L _ _ c hc =>
        Stacks.WeilCohomology.prescribedCohomologyTranslate_of_isSepClosed ℂ f L c _ hc θ hθ))
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (genus f)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  haveI hAg : SmoothOfRelativeDimension (genus f) A.X.hom :=
    hP _ (Stacks.Hilbert.smoothOfRelativeDimension_of_represents (fun d => (HH d).1)
      (fun d => (HH d).2) (genus f))
  haveI : Smooth A.X.hom := SmoothOfRelativeDimension.smooth (genus f) _
  haveI hAV : IsAbelianVariety ℂ A.X :=
    Stacks.RigidifiedPicard.isAbelianVariety_of_iso_functorZero_field f hdim σ hσ e hdimX
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : (SheafOfModules.unit C.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  haveI : FiniteDimensional ℂ (cohomologyOverField ℂ f (SheafOfModules.unit C.ringCatSheaf) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper ℂ f _ 1
  haveI : FiniteDimensional ℂ (structureSheafCohomology f 1) :=
    (structureSheafCohomologyIsoCohomologyOverField ℂ f 1).toLinearEquiv.symm.finiteDimensional
  refine ⟨A, e, hAV, ?_, ?_, (e.hom.app (op A.X)).hom (𝟙 A.X), fun T a => ?_⟩
  · have hT := Scheme.Hom.finrank_dottedTangentArrow_of_smoothOfRelativeDimension A.X.hom
      (genus f) (η[A.X].left (closedPoint ℂ))
    haveI := finiteDimensional_dottedTangentArrow A.X.hom (η[A.X].left (closedPoint ℂ))
    letI := RingHomInvPair.of_ringEquiv
      (sectionResidueFieldEquiv A.X.hom η[A.X].left (Over.w η[A.X]))
    letI := RingHomInvPair.of_ringEquiv_symm
      (sectionResidueFieldEquiv A.X.hom η[A.X].left (Over.w η[A.X]))
    exact ⟨semilinearEquivOfFinrankEq _ hT⟩
  · haveI : Nonempty A.X.left := ⟨(η[A.X]).left (closedPoint ℂ)⟩
    have h1 := AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
      (genus f) A.X.hom
    have h2 := Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension A.X
    rw [h1] at h2
    exact_mod_cast h2.symm
  · have h := congrArg (fun φ => GrpCat.Hom.hom φ (𝟙 A.X)) (e.hom.naturality a.op)
    simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at h
    exact Eq.trans (congrArg _ (Category.comp_id a).symm) h

end MMP.Conductor

end

/-!
# Weierstrass division for convergent power series

Let `z = (z₁, …, zₖ)` and let `f` be a convergent power series in `(z, w)` over `ℂ` whose
restriction `w ↦ f (0, w)` vanishes to order exactly `d ≥ 1` at the origin. Every convergent
`h` can be written uniquely as `h = f q + r` with `q` convergent and `r` a polynomial in `w` of
degree `< d` whose coefficients are convergent series in `z`.

## Main results

* `MMP.Convergent.existsUnique_weierstrassDivision`: existence and uniqueness of the division.

## Implementation notes

The ring `ℂ{z, w}` of convergent power series is realised as the ring of germs at `0` of
functions `(Fin k → ℂ) × ℂ → ℂ` analytic at `0`: a convergent series is the germ of its sum,
and two series agree iff their sums agree near `0`. The hypothesis `f (0, w) = w ^ d u₀ (w)`
with `u₀` convergent and `u₀ 0 ≠ 0` is stated as `analyticOrderAt (fun w ↦ f (0, w)) 0 = d`.
The remainder is given by its coefficients `a : Fin d → (Fin k → ℂ) → ℂ`, each analytic at `0`,
as `r (z, w) = ∑ i, a i z * w ^ i`; uniqueness is uniqueness of the germs of `q` and of each
`a i`.

## References

* [Grauert, Remmert, *Coherent analytic sheaves*], Weierstrass division theorem.
-/

section

open Filter Topology Metric
open Complex Real

namespace MMP.Analytic.Proof_lem_mmp_convergent_weierstrass_division

section Existence

/-- Division by `(w - c) ^ m` with polynomial remainder of degree `< m`. -/
private theorem exists_eq_sub_pow_mul_add {ψ : ℂ → ℂ} {s : Set ℂ} {c : ℂ} (hs : s ∈ 𝓝 c)
    (hψ : DifferentiableOn ℂ ψ s) (m : ℕ) :
    ∃ ψ₁ : ℂ → ℂ, ∃ P : Polynomial ℂ, P.degree < m ∧ DifferentiableOn ℂ ψ₁ s ∧
      ∀ w, ψ w = (w - c) ^ m * ψ₁ w + P.eval w := by
  induction m with
  | zero => exact ⟨ψ, 0, by simp, hψ, fun w ↦ by simp⟩
  | succ m ih =>
    obtain ⟨ψ₁, P, hP, hψ₁, he⟩ := ih
    refine ⟨dslope ψ₁ c, (Polynomial.X - Polynomial.C c) ^ m * Polynomial.C (ψ₁ c) + P, ?_,
      (differentiableOn_dslope hs).2 hψ₁, fun w ↦ ?_⟩
    · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ (hP.trans ?_))
      · refine (Polynomial.degree_mul_le _ _).trans_lt ?_
        refine lt_of_le_of_lt (add_le_add (Polynomial.degree_pow_le _ _)
          Polynomial.degree_C_le) ?_
        rw [Polynomial.degree_X_sub_C, add_zero, nsmul_eq_mul, mul_one]
        exact_mod_cast Nat.lt_succ_self m
      · exact_mod_cast Nat.lt_succ_self m
    · have h1 := sub_smul_dslope ψ₁ c w
      rw [smul_eq_mul] at h1
      rw [he w]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      linear_combination -((w - c) ^ m * h1)

/-- Extracting a zero of finite order. -/
private theorem exists_eq_sub_pow_mul {F : ℂ → ℂ} {s : Set ℂ} {c : ℂ} (hs : IsOpen s) (hc : c ∈ s)
    (hF : DifferentiableOn ℂ F s) (hFc : F c = 0) (hF0 : ¬ ∀ᶠ w in 𝓝 c, F w = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ F₁ : ℂ → ℂ, DifferentiableOn ℂ F₁ s ∧ F₁ c ≠ 0 ∧
      ∀ w, F w = (w - c) ^ m * F₁ w := by
  have hFa : AnalyticAt ℂ F c := hF.analyticAt (hs.mem_nhds hc)
  have htop : analyticOrderAt F c ≠ ⊤ := fun h ↦ hF0 (analyticOrderAt_eq_top.mp h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hg, hg0, hFg⟩ := hFa.analyticOrderAt_eq_natCast.mp hm.symm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have := hFg.self_of_nhds
      simp only [pow_zero, one_smul] at this
      exact absurd (this ▸ hFc) hg0
    · exact h0
  classical
  let F₁ : ℂ → ℂ := fun w ↦ if w = c then g c else F w / (w - c) ^ m
  have hF₁c : F₁ c = g c := by simp [F₁]
  have hfac : ∀ w, F w = (w - c) ^ m * F₁ w := by
    intro w
    by_cases hw : w = c
    · subst hw; rw [hFc, sub_self, zero_pow (by omega), zero_mul]
    · have : (w - c) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
      simp only [F₁, hw, ite_false]
      field_simp
  refine ⟨m, hm1, F₁, fun w hw ↦ ?_, hF₁c ▸ hg0, hfac⟩
  by_cases hwc : w = c
  · subst hwc
    have : F₁ =ᶠ[𝓝 w] g := by
      filter_upwards [hFg] with v hv
      by_cases hvc : v = w
      · subst hvc; exact hF₁c
      · have : (v - w) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hvc)
        simp only [F₁, hvc, ite_false, smul_eq_mul] at hv ⊢
        rw [hv]; field_simp
    exact (hg.differentiableAt.congr_of_eventuallyEq this).differentiableWithinAt
  · have : F₁ =ᶠ[𝓝 w] fun v ↦ F v / (v - c) ^ m := by
      filter_upwards [isOpen_ne.mem_nhds hwc] with v hv
      simp [F₁, hv]
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ this).differentiableWithinAt
    exact ((hF w hw).differentiableAt (hs.mem_nhds hw)).div
      ((differentiableAt_id.sub_const c).pow m) (pow_ne_zero _ (sub_ne_zero.mpr hwc))

/-- The logarithmic integral picks up the order of an extracted zero. -/
private theorem circleIntegral_logDeriv_sub_pow_mul {F₁ : ℂ → ℂ} {τ R : ℝ} (hτR : τ < R) {c : ℂ}
    (hc : ‖c‖ < τ) {m : ℕ} (hm : 1 ≤ m) (hF₁ : DifferentiableOn ℂ F₁ (ball 0 R))
    (hF₁0 : ∀ t ∈ sphere (0 : ℂ) τ, F₁ t ≠ 0) :
    (∮ t in C(0, τ), deriv (fun w ↦ (w - c) ^ m * F₁ w) t / ((t - c) ^ m * F₁ t)) =
      2 * π * I * m + ∮ t in C(0, τ), deriv F₁ t / F₁ t := by
  have hτ : 0 < τ := (norm_nonneg c).trans_lt hc
  have hsub : closedBall (0 : ℂ) τ ⊆ ball 0 R := closedBall_subset_ball hτR
  have hd' : DifferentiableOn ℂ (deriv F₁) (ball 0 R) := hF₁.deriv isOpen_ball
  have hne : ∀ t ∈ sphere (0 : ℂ) τ, t - c ≠ 0 := by
    intro t ht h
    rw [sub_eq_zero] at h
    subst h
    rw [mem_sphere_zero_iff_norm] at ht
    linarith
  have hpt : ∀ t ∈ sphere (0 : ℂ) τ,
      deriv (fun w ↦ (w - c) ^ m * F₁ w) t / ((t - c) ^ m * F₁ t) =
        m * (t - c)⁻¹ + deriv F₁ t / F₁ t := by
    intro t ht
    have htR : t ∈ ball (0 : ℂ) R := hsub (sphere_subset_closedBall ht)
    have hdF := (hF₁ t htR).differentiableAt (isOpen_ball.mem_nhds htR)
    have h1 : HasDerivAt (fun w ↦ (w - c) ^ m * F₁ w)
        ((m : ℂ) * (t - c) ^ (m - 1) * 1 * F₁ t + (t - c) ^ m * deriv F₁ t) t :=
      (((hasDerivAt_id t).sub_const c).pow m).mul hdF.hasDerivAt
    rw [h1.deriv]
    have h2 := hne t ht
    have h3 := hF₁0 t ht
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  have hcont1 : ContinuousOn (fun t : ℂ ↦ (m : ℂ) * (t - c)⁻¹) (sphere 0 τ) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ hne)
  have hcont2 : ContinuousOn (fun t : ℂ ↦ deriv F₁ t / F₁ t) (sphere 0 τ) :=
    ((hd'.mono (sphere_subset_closedBall.trans hsub)).continuousOn).div
      ((hF₁.mono (sphere_subset_closedBall.trans hsub)).continuousOn) hF₁0
  rw [circleIntegral.integral_congr hτ.le hpt,
    circleIntegral.integral_add (hcont1.circleIntegrable hτ.le) (hcont2.circleIntegrable hτ.le)]
  congr 1
  rw [show (fun t : ℂ ↦ (m : ℂ) * (t - c)⁻¹) = fun t ↦ (m : ℂ) • (t - c)⁻¹ from rfl,
    circleIntegral.integral_smul, circleIntegral.integral_sub_inv_of_mem_ball
      (by simpa using hc), smul_eq_mul]
  ring

/-- A function holomorphic on `ball 0 R` and nonvanishing on the annulus `τ ≤ ‖t‖ < R` is not
the zero germ at any point of the ball. -/
private theorem not_eventually_eq_zero {F : ℂ → ℂ} {τ R : ℝ} (hτ : 0 < τ) (hτR : τ < R)
    (hF : DifferentiableOn ℂ F (ball 0 R)) (hF0 : ∀ t ∈ ball (0 : ℂ) R, τ ≤ ‖t‖ → F t ≠ 0)
    {c : ℂ} (hc : c ∈ ball (0 : ℂ) R) : ¬ ∀ᶠ w in 𝓝 c, F w = 0 := by
  intro h
  have hz := (hF.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hc h
  have hτm : ((τ : ℂ)) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hτ.le]; exact hτR
  exact hF0 _ hτm (by rw [Complex.norm_real, Real.norm_of_nonneg hτ.le]) (hz hτm)

private theorem finite_zeros {F : ℂ → ℂ} {τ R : ℝ} (hτ : 0 < τ) (hτR : τ < R)
    (hF : DifferentiableOn ℂ F (ball 0 R)) (hF0 : ∀ t ∈ ball (0 : ℂ) R, τ ≤ ‖t‖ → F t ≠ 0) :
    {t ∈ closedBall (0 : ℂ) τ | F t = 0}.Finite := by
  by_contra hinf
  obtain ⟨c, hcK, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_closedBall 0 τ) (Set.sep_subset _ _)
  have hcR : c ∈ ball (0 : ℂ) R := closedBall_subset_ball hτR hcK
  have hFa : AnalyticAt ℂ F c := hF.analyticAt (isOpen_ball.mem_nhds hcR)
  apply not_eventually_eq_zero hτ hτR hF hF0 hcR
  rw [← hFa.frequently_zero_iff_eventually_zero]
  exact (accPt_iff_frequently_nhdsNE.mp hacc).mono fun y hy ↦ hy.2

/-- The logarithmic integral of a nonvanishing holomorphic function is zero. -/
private theorem circleIntegral_logDeriv_eq_zero {F : ℂ → ℂ} {τ R : ℝ} (hτ : 0 ≤ τ) (hτR : τ < R)
    (hF : DifferentiableOn ℂ F (ball 0 R)) (hne : ∀ t ∈ ball (0 : ℂ) R, F t ≠ 0) :
    (∮ t in C(0, τ), deriv F t / F t) = 0 := by
  have hsub : closedBall (0 : ℂ) τ ⊆ ball 0 R := closedBall_subset_ball hτR
  have hd' : DifferentiableOn ℂ (deriv F) (ball 0 R) := hF.deriv isOpen_ball
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hτ
    Set.countable_empty ?_ fun t ht ↦ ?_
  · exact ((hd'.mono hsub).continuousOn).div ((hF.mono hsub).continuousOn)
      fun t ht ↦ hne t (hsub ht)
  · have htR := hsub (ball_subset_closedBall ht.1)
    exact ((hd' t htR).differentiableAt (isOpen_ball.mem_nhds htR)).div
      ((hF t htR).differentiableAt (isOpen_ball.mem_nhds htR)) (hne t htR)

private theorem oneVar_division_aux {τ R : ℝ} (hτ : 0 < τ) (hτR : τ < R) (Z : Finset ℂ) :
    ∀ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 R) →
      (∀ t ∈ ball (0 : ℂ) R, τ ≤ ‖t‖ → F t ≠ 0) → (∀ t ∈ ball (0 : ℂ) R, F t = 0 → t ∈ Z) →
      ∃ n : ℕ, (∮ t in C(0, τ), deriv F t / F t) = 2 * π * I * n ∧
        ∀ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (ball 0 R) →
          ∃ χ : ℂ → ℂ, ∃ P : Polynomial ℂ, P.degree < n ∧ DifferentiableOn ℂ χ (ball 0 R) ∧
            ∀ w ∈ ball (0 : ℂ) R, ψ w = F w * χ w + P.eval w := by
  classical
  have hsub : closedBall (0 : ℂ) τ ⊆ ball 0 R := closedBall_subset_ball hτR
  induction Z using Finset.induction_on with
  | empty =>
    intro F hF hF0 hZ
    have hne : ∀ t ∈ ball (0 : ℂ) R, F t ≠ 0 := fun t ht h ↦ by simpa using hZ t ht h
    refine ⟨0, ?_, fun ψ hψ ↦ ⟨fun w ↦ ψ w / F w, 0, by simp, hψ.div hF hne, fun w hw ↦ ?_⟩⟩
    · rw [Nat.cast_zero, mul_zero, circleIntegral_logDeriv_eq_zero hτ.le hτR hF hne]
    · have := hne w hw
      simp only [Polynomial.eval_zero, add_zero]
      field_simp
  | insert c Z hcZ ih =>
    intro F hF hF0 hZ
    by_cases hc : c ∈ ball (0 : ℂ) R ∧ F c = 0
    · obtain ⟨hcR, hFc⟩ := hc
      obtain ⟨m, hm1, F₁, hF₁, hF₁c, hfac⟩ := exists_eq_sub_pow_mul isOpen_ball hcR hF hFc
        (not_eventually_eq_zero hτ hτR hF hF0 hcR)
      have hcτ : ‖c‖ < τ := by
        by_contra h
        exact hF0 c hcR (not_lt.mp h) hFc
      have hF₁0 : ∀ t ∈ ball (0 : ℂ) R, τ ≤ ‖t‖ → F₁ t ≠ 0 := by
        intro t ht hτt h
        exact hF0 t ht hτt (by rw [hfac t, h, mul_zero])
      have hZ₁ : ∀ t ∈ ball (0 : ℂ) R, F₁ t = 0 → t ∈ Z := by
        intro t ht h
        have ht' := hZ t ht (by rw [hfac t, h, mul_zero])
        rcases Finset.mem_insert.mp ht' with h' | h'
        · subst h'; exact absurd h hF₁c
        · exact h'
      obtain ⟨n₁, hwind, hdiv⟩ := ih F₁ hF₁ hF₁0 hZ₁
      have hFeq : F = fun w ↦ (w - c) ^ m * F₁ w := funext hfac
      refine ⟨m + n₁, ?_, fun ψ hψ ↦ ?_⟩
      · have hsph : ∀ t ∈ sphere (0 : ℂ) τ, F₁ t ≠ 0 := fun t ht ↦
          hF₁0 t (hsub (sphere_subset_closedBall ht)) (by rw [mem_sphere_zero_iff_norm.mp ht])
        have := circleIntegral_logDeriv_sub_pow_mul hτR hcτ hm1 hF₁ hsph
        rw [hFeq, this, hwind]
        push_cast
        ring
      · obtain ⟨ψ₁, π₀, hπ₀, hψ₁, hψe⟩ :=
          exists_eq_sub_pow_mul_add (isOpen_ball.mem_nhds hcR) hψ m
        obtain ⟨χ, P₁, hP₁, hχ, hχe⟩ := hdiv ψ₁ hψ₁
        refine ⟨χ, (Polynomial.X - Polynomial.C c) ^ m * P₁ + π₀, ?_, hχ, fun w hw ↦ ?_⟩
        · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
          · rw [Polynomial.degree_mul, Polynomial.degree_pow, Polynomial.degree_X_sub_C,
              nsmul_eq_mul, mul_one]
            rcases eq_or_ne P₁ 0 with h0 | h0
            · simp [h0]
            · rw [Polynomial.degree_eq_natDegree h0] at hP₁ ⊢
              have : P₁.natDegree < n₁ := by exact_mod_cast hP₁
              exact_mod_cast (by omega : m + P₁.natDegree < m + n₁)
          · exact hπ₀.trans_le (by exact_mod_cast Nat.le_add_right m n₁)
        · rw [hψe w, hχe w hw, hfac w]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          ring
    · refine ih F hF hF0 fun t ht h ↦ ?_
      rcases Finset.mem_insert.mp (hZ t ht h) with h' | h'
      · subst h'; exact absurd ⟨ht, h⟩ hc
      · exact h'

/-- One-variable division by a function with finitely many zeros inside a circle. -/
private theorem oneVar_division {F : ℂ → ℂ} {τ R : ℝ} (hτ : 0 < τ) (hτR : τ < R)
    (hF : DifferentiableOn ℂ F (ball 0 R)) (hF0 : ∀ t ∈ ball (0 : ℂ) R, τ ≤ ‖t‖ → F t ≠ 0) :
    ∃ n : ℕ, (∮ t in C(0, τ), deriv F t / F t) = 2 * π * I * n ∧
      ∀ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (ball 0 R) →
        ∃ χ : ℂ → ℂ, ∃ P : Polynomial ℂ, P.degree < n ∧ DifferentiableOn ℂ χ (ball 0 R) ∧
          ∀ w ∈ ball (0 : ℂ) R, ψ w = F w * χ w + P.eval w := by
  refine oneVar_division_aux hτ hτR (finite_zeros hτ hτR hF hF0).toFinset F hF hF0
    fun t ht h ↦ ?_
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, h⟩
  rw [mem_closedBall_zero_iff]
  by_contra h'
  exact hF0 t ht (not_le.mp h').le h

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] {Y : Type*} [NormedAddCommGroup
    Y] [NormedSpace ℂ Y]

private theorem update_apply_eval {ι : Type*} [DecidableEq ι] (φ : ι → C(K, Y)) (i : ι)
    (v : C(K, Y)) (k : K) :
    (fun j ↦ Function.update φ i v j k) = Function.update (fun j ↦ φ j k) i (v k) :=
  funext (Function.apply_update (fun _ (g : C(K, Y)) ↦ g k) φ i v)

/-- Pointwise application of a multilinear map to continuous maps on a compact space. -/
private noncomputable def liftCM {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ Y) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ C(K, Y)) C(K, ℂ) :=
  MultilinearMap.mkContinuous
    { toFun := fun φ ↦ ⟨fun k ↦ q (fun i ↦ φ i k),
        q.cont.comp (continuous_pi fun i ↦ (φ i).continuous)⟩
      map_update_add' := by
        intro _ φ i x y
        ext k
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [update_apply_eval, update_apply_eval, update_apply_eval, ContinuousMap.add_apply,
          q.map_update_add]
      map_update_smul' := by
        intro _ φ i c x
        ext k
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply]
        rw [update_apply_eval, update_apply_eval, ContinuousMap.smul_apply, q.map_update_smul] }
    ‖q‖ fun φ ↦ by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun k ↦ ?_
      refine (q.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        fun i _ ↦ ContinuousMap.norm_coe_le_norm _ _

private theorem norm_liftCM_le {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ Y) ℂ) :
    ‖(liftCM q : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ C(K, Y)) C(K, ℂ))‖ ≤ ‖q‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- The superposition `φ ↦ A ∘ φ`, for `A` given by a power series around `0`, is analytic on
`C(K, Y)` near maps with values in the ball of convergence. -/
private theorem exists_analyticAt_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {A : Y → ℂ} {p : FormalMultilinearSeries ℂ Y ℂ} {R : ENNReal}
    (hA : HasFPowerSeriesOnBall A p 0 R) {ι : X → C(K, Y)} {x₀ : X}
    (hι : AnalyticAt ℂ ι x₀) (hx₀ : (‖ι x₀‖₊ : ENNReal) < R) :
    ∃ Ah : X → C(K, ℂ), AnalyticAt ℂ Ah x₀ ∧ ∀ᶠ x in 𝓝 x₀, ∀ k, Ah x k = A (ι x k) := by
  let p' : FormalMultilinearSeries ℂ C(K, Y) C(K, ℂ) := fun n ↦ liftCM (p n)
  have hrad : p.radius ≤ p'.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
    obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
    exact p'.le_radius_of_bound C fun n ↦
      (mul_le_mul_of_nonneg_right (norm_liftCM_le (p n)) (by positivity)).trans (hC n)
  have hRp' : R ≤ p'.radius := hA.r_le.trans hrad
  have hp' : HasFPowerSeriesOnBall p'.sum p' 0 p'.radius :=
    p'.hasFPowerSeriesOnBall (hA.r_pos.trans_le hRp')
  have hmem : ι x₀ ∈ Metric.eball (0 : C(K, Y)) p'.radius := by
    rw [Metric.mem_eball, edist_zero_right]; exact hx₀.trans_le hRp'
  refine ⟨fun x ↦ p'.sum (ι x), (hp'.analyticAt_of_mem hmem).comp hι, ?_⟩
  have hev : ∀ᶠ x in 𝓝 x₀, (‖ι x‖₊ : ENNReal) < R := by
    have hc : ContinuousAt (fun x ↦ (‖ι x‖₊ : ENNReal)) x₀ :=
      ENNReal.continuous_coe.continuousAt.comp hι.continuousAt.nnnorm
    exact hc.eventually (gt_mem_nhds hx₀)
  filter_upwards [hev] with x hx k
  have hmx : ι x ∈ Metric.eball (0 : C(K, Y)) p'.radius := by
    rw [Metric.mem_eball, edist_zero_right]; exact hx.trans_le hRp'
  have h1 := (p'.hasSum hmx).mapL (ContinuousMap.evalCLM ℂ k)
  have hk : (‖ι x k‖₊ : ENNReal) < R :=
    lt_of_le_of_lt (by exact_mod_cast ContinuousMap.norm_coe_le_norm (ι x) k) hx
  have h2 := hA.hasSum (y := ι x k) (by rw [Metric.mem_eball, edist_zero_right]; exact hk)
  rw [zero_add] at h2
  exact h1.unique h2

/-- Integration over the circle of radius `τ`, as a continuous linear functional on
`C(sphere 0 τ, ℂ)`. -/
private noncomputable def circleCLM {τ : ℝ} (hτ : 0 ≤ τ) : C(sphere (0 : ℂ) τ, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ ↦ ∫ θ in (0 : ℝ)..2 * π,
        deriv (circleMap 0 τ) θ • φ ⟨circleMap 0 τ θ, circleMap_mem_sphere 0 hτ θ⟩
      map_add' := by
        intro φ ψ
        have hc : ∀ φ : C(sphere (0 : ℂ) τ, ℂ), Continuous fun θ ↦
            deriv (circleMap 0 τ) θ • φ ⟨circleMap 0 τ θ, circleMap_mem_sphere 0 hτ θ⟩ := by
          intro φ
          simp only [deriv_circleMap, smul_eq_mul]
          exact ((continuous_circleMap 0 τ).mul continuous_const).mul
            (φ.continuous.comp ((continuous_circleMap 0 τ).subtype_mk _))
        simp only [ContinuousMap.add_apply, smul_add]
        exact intervalIntegral.integral_add ((hc φ).intervalIntegrable _ _)
          ((hc ψ).intervalIntegrable _ _)
      map_smul' := by
        intro c φ
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← intervalIntegral.integral_const_mul]
        congr 1; funext θ; ring }
    (τ * (2 * π)) fun φ ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
        (C := τ * ‖φ‖) (f := fun θ ↦
          deriv (circleMap 0 τ) θ • φ ⟨circleMap 0 τ θ, circleMap_mem_sphere 0 hτ θ⟩)
        fun θ _ ↦ by
          rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I,
            mul_one, abs_of_nonneg hτ]
          exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) hτ
      rw [sub_zero, abs_of_pos (by positivity)] at this
      linarith

private theorem circleCLM_apply {τ : ℝ} (hτ : 0 ≤ τ) (φ : C(sphere (0 : ℂ) τ, ℂ)) :
    circleCLM hτ φ = ∫ θ in (0 : ℝ)..2 * π,
      deriv (circleMap 0 τ) θ • φ ⟨circleMap 0 τ θ, circleMap_mem_sphere 0 hτ θ⟩ := rfl

/-- A circle integral `∮ A x t / F x t` is analytic in the parameter, when `A x` and `F x`
restricted to the circle are analytic as maps into `C(sphere 0 τ, ℂ)`. -/
private theorem analyticAt_circleIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {τ : ℝ} (hτ : 0 ≤ τ) {Ah Fh : X → C(sphere (0 : ℂ) τ, ℂ)} {x₀ : X}
    (hAh : AnalyticAt ℂ Ah x₀) (hFh : AnalyticAt ℂ Fh x₀) (hF0 : ∀ t, Fh x₀ t ≠ 0)
    {A F : X → ℂ → ℂ} (hAe : ∀ᶠ x in 𝓝 x₀, ∀ t : sphere (0 : ℂ) τ, Ah x t = A x t)
    (hFe : ∀ᶠ x in 𝓝 x₀, ∀ t : sphere (0 : ℂ) τ, Fh x t = F x t) :
    AnalyticAt ℂ (fun x ↦ ∮ t in C(0, τ), A x t / F x t) x₀ := by
  let v : C(sphere (0 : ℂ) τ, ℂ) := ⟨fun t ↦ (Fh x₀ t)⁻¹, (Fh x₀).continuous.inv₀ hF0⟩
  let u : C(sphere (0 : ℂ) τ, ℂ)ˣ := ⟨Fh x₀, v, by ext t; simp [v, hF0 t], by ext t; simp [v, hF0
      t]⟩
  have hinv : AnalyticAt ℂ (Ring.inverse : C(sphere (0 : ℂ) τ, ℂ) → C(sphere (0 : ℂ) τ, ℂ))
      (Fh x₀) := analyticAt_inverse (𝕜 := ℂ) u
  have hG : AnalyticAt ℂ (fun x ↦ circleCLM hτ (Ah x * Ring.inverse (Fh x))) x₀ :=
    ((circleCLM hτ).analyticAt _).comp (hAh.mul (hinv.comp hFh))
  refine hG.congr ?_
  have hunit : ∀ᶠ x in 𝓝 x₀, IsUnit (Fh x) :=
    hFh.continuousAt.eventually (Units.isOpen.mem_nhds u.isUnit)
  filter_upwards [hunit, hAe, hFe] with x hx hxA hxF
  rw [circleCLM_apply, circleIntegral]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  congr 1
  rw [ContinuousMap.mul_apply, hxA, div_eq_mul_inv]
  congr 1
  rw [show F x (circleMap 0 τ θ) = Fh x ⟨circleMap 0 τ θ, circleMap_mem_sphere 0 hτ θ⟩ from
    (hxF ⟨circleMap 0 τ θ, circleMap_mem_sphere 0 hτ θ⟩).symm]
  have h1 := congrArg (fun g : C(sphere (0 : ℂ) τ, ℂ) ↦
    g ⟨circleMap 0 τ θ, circleMap_mem_sphere 0 hτ θ⟩) (Ring.inverse_mul_cancel _ hx)
  simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply] at h1
  exact eq_inv_of_mul_eq_one_left h1

private theorem analyticAt_det {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {n : ℕ}
    {M : X → Matrix (Fin n) (Fin n) ℂ} {x₀ : X}
    (hM : ∀ i j, AnalyticAt ℂ (fun x ↦ M x i j) x₀) :
    AnalyticAt ℂ (fun x ↦ (M x).det) x₀ := by
  simp_rw [Matrix.det_apply]
  refine Finset.analyticAt_fun_sum _ fun σ _ ↦ ?_
  simp_rw [Units.smul_def, zsmul_eq_mul]
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ ↦ hM _ _)

private theorem analyticAt_inv_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {n : ℕ}
    {M : X → Matrix (Fin n) (Fin n) ℂ} {x₀ : X}
    (hM : ∀ i j, AnalyticAt ℂ (fun x ↦ M x i j) x₀) (h0 : (M x₀).det ≠ 0) (i j : Fin n) :
    AnalyticAt ℂ (fun x ↦ (M x)⁻¹ i j) x₀ := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((analyticAt_det hM).inv h0).mul (analyticAt_det fun i' j' ↦ ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact analyticAt_const
  · exact hM _ _

/-- The restriction to `{z} × sphere 0 τ` of a function given by a power series on a ball
containing that sphere, as an analytic map of `z` into `C(sphere 0 τ, ℂ)`. -/
private theorem exists_analyticAt_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E × ℂ → ℂ} {p : FormalMultilinearSeries ℂ (E × ℂ) ℂ} {r : ENNReal}
    (hg : HasFPowerSeriesOnBall g p 0 r) {τ : ℝ} (hτ : 0 ≤ τ) (hτr : ENNReal.ofReal τ < r) :
    ∃ G : E → C(sphere (0 : ℂ) τ, ℂ), AnalyticAt ℂ G 0 ∧
      ∀ᶠ z in 𝓝 0, ∀ t : sphere (0 : ℂ) τ, G z t = g (z, t) := by
  let ι : E → C(sphere (0 : ℂ) τ, E × ℂ) := fun z ↦
    ⟨fun t ↦ (z, (t : ℂ)), continuous_const.prodMk continuous_subtype_val⟩
  let J : E →L[ℂ] C(sphere (0 : ℂ) τ, E × ℂ) := LinearMap.mkContinuous
    { toFun := fun z ↦ ContinuousMap.const _ (z, 0)
      map_add' := fun x y ↦ by ext <;> simp
      map_smul' := fun c x ↦ by ext <;> simp } 1 fun z ↦ by
        refine (ContinuousMap.norm_le _ (by positivity)).2 fun t ↦ ?_
        simp [Prod.norm_def]
  have hι : ι = fun z ↦ J z + ι 0 := by
    funext z; ext t <;> simp [ι, J]
  have hιa : AnalyticAt ℂ ι 0 := by
    rw [hι]; exact (J.analyticAt 0).add analyticAt_const
  have hle : ‖ι 0‖ ≤ τ := by
    refine (ContinuousMap.norm_le _ hτ).2 fun t ↦ ?_
    simp [ι, Prod.norm_def, (mem_sphere_zero_iff_norm.mp t.2), hτ]
  have hlt : (‖ι 0‖₊ : ENNReal) < r := by
    refine lt_of_le_of_lt ?_ hτr
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hle
  obtain ⟨G, hG, hGe⟩ := exists_analyticAt_comp hg hιa hlt
  exact ⟨G, hG, hGe.mono fun z hz t ↦ hz t⟩

private theorem deriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E × ℂ → ℂ}
    {z : E} {t : ℂ} (hf : DifferentiableAt ℂ f (z, t)) :
    deriv (fun s ↦ f (z, s)) t = fderiv ℂ f (z, t) (0, 1) := by
  have h1 : HasDerivAt (fun s : ℂ ↦ (z, s)) ((0 : E), (1 : ℂ)) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  exact (hf.hasFDerivAt.comp_hasDerivAt t h1).deriv

end Existence

/-- The germ of an analytic function `f` on `E × ℂ` whose slice `w ↦ f (0, w)` is not the zero
germ is a non-zero-divisor: `f * q = 0` near `0` forces `q = 0` near `0`. -/
private theorem eventuallyEq_zero_of_mul_eventuallyEq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f q : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : ¬ (fun w : ℂ ↦ f (0, w)) =ᶠ[𝓝 0] 0)
    (hq : AnalyticAt ℂ q 0) (h : (fun p ↦ f p * q p) =ᶠ[𝓝 0] 0) : q =ᶠ[𝓝 0] 0 := by
  obtain ⟨r₁, hr₁, hfa⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hqa⟩ := hq.exists_ball_analyticOnNhd
  obtain ⟨r₃, hr₃, h₃⟩ := Metric.eventually_nhds_iff_ball.mp h
  set r := min r₁ (min r₂ r₃)
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
  have hrr₁ : Metric.ball (0 : E × ℂ) r ⊆ Metric.ball 0 r₁ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hrr₂ : Metric.ball (0 : E × ℂ) r ⊆ Metric.ball 0 r₂ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hrr₃ : Metric.ball (0 : E × ℂ) r ⊆ Metric.ball 0 r₃ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  -- by the identity theorem, `f` is not the zero germ at any point of the ball
  have key : ∀ p ∈ Metric.ball (0 : E × ℂ) r, ¬ f =ᶠ[𝓝 p] 0 := by
    intro p hp hfp
    apply hf0
    have hz := (hfa.mono hrr₁).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball _ _).isPreconnected hp hfp
    have hc : Tendsto (fun w : ℂ ↦ ((0 : E), w)) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun w : ℂ ↦ ((0 : E), w)) := by fun_prop
      simpa [← Prod.zero_eq_mk] using this.tendsto 0
    filter_upwards [hc (Metric.ball_mem_nhds 0 hr)] with w hw using hz hw
  filter_upwards [Metric.ball_mem_nhds (0 : E × ℂ) hr] with p hp
  by_contra hqp
  apply key p hp
  have hcont : ContinuousAt q p := (hqa p (hrr₂ hp)).continuousAt
  filter_upwards [hcont.eventually_ne hqp, Metric.isOpen_ball.mem_nhds hp] with y hy₁ hy₂
  exact (mul_eq_zero.mp (h₃ y (hrr₃ hy₂))).resolve_right hy₁

/-- A circle integral `∮ g t / F x t` depends continuously on the parameter `x` at `x₀`, when
`F` is jointly continuous at the points `(x₀, t)` of the circle and `F x₀` does not vanish on
it. -/
private theorem continuousAt_circleIntegral_div {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {F : X → ℂ → ℂ} {x₀ : X} {g : ℂ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hg : Continuous g)
    (hF : ∀ t ∈ sphere (0 : ℂ) τ, ContinuousAt (fun p : X × ℂ ↦ F p.1 p.2) (x₀, t))
    (hFc : ∀ᶠ x in 𝓝 x₀, ContinuousOn (F x) (sphere 0 τ))
    (hF0 : ∀ t ∈ sphere (0 : ℂ) τ, F x₀ t ≠ 0) :
    ContinuousAt (fun x ↦ ∮ t in C(0, τ), g t / F x t) x₀ := by
  have hF₀ : ∀ t ∈ sphere (0 : ℂ) τ, ContinuousAt (fun p : X × ℂ ↦ F x₀ p.2) (x₀, t) :=
    fun t ht ↦ ContinuousAt.comp_of_eq (f := fun p : X × ℂ ↦ (x₀, p.2)) (x := (x₀, t))
      (hF t ht) (by fun_prop) rfl
  have hbig : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ sphere (0 : ℂ) τ, ‖F x₀ t‖ / 2 < ‖F x t‖ := by
    apply (isCompact_sphere (0 : ℂ) τ).eventually_forall_of_forall_eventually
    intro t ht
    have h1 : ContinuousAt (fun p : X × ℂ ↦ ‖F p.1 p.2‖ - ‖F x₀ p.2‖ / 2) (x₀, t) :=
      (hF t ht).norm.sub ((hF₀ t ht).norm.div_const 2)
    have h3 : (0 : ℝ) < ‖F x₀ t‖ - ‖F x₀ t‖ / 2 := by
      have := norm_pos_iff.2 (hF0 t ht); linarith
    filter_upwards [h1.eventually (lt_mem_nhds h3)] with p hp
    linarith
  have hcm : ∀ θ, circleMap 0 τ θ ∈ sphere (0 : ℂ) τ := circleMap_mem_sphere 0 hτ
  have hF₀c : Continuous fun θ ↦ F x₀ (circleMap 0 τ θ) := by
    have : ContinuousOn (F x₀) (sphere 0 τ) := fun t ht ↦
      (ContinuousAt.comp_of_eq (f := fun s : ℂ ↦ (x₀, s)) (x := t) (hF₀ t ht)
        (by fun_prop) rfl).continuousWithinAt
    exact this.comp_continuous (continuous_circleMap 0 τ) hcm
  simp only [circleIntegral]
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun θ ↦ |τ| * ‖g (circleMap 0 τ θ)‖ / (‖F x₀ (circleMap 0 τ θ)‖ / 2)) ?_ ?_ ?_ ?_
  · filter_upwards [hFc, hbig] with x hx hx'
    apply Continuous.aestronglyMeasurable
    have hne : ∀ θ, F x (circleMap 0 τ θ) ≠ 0 := fun θ h0 ↦ by
      have := hx' _ (hcm θ)
      rw [h0, norm_zero] at this
      linarith [norm_nonneg (F x₀ (circleMap 0 τ θ))]
    have : Continuous fun θ ↦ F x (circleMap 0 τ θ) :=
      hx.comp_continuous (continuous_circleMap 0 τ) hcm
    simp only [deriv_circleMap, smul_eq_mul]
    exact ((continuous_circleMap 0 τ).mul continuous_const).mul
      ((hg.comp (continuous_circleMap 0 τ)).div this hne)
  · filter_upwards [hbig] with x hx'
    refine Eventually.of_forall fun θ _ ↦ ?_
    have hpos : 0 < ‖F x₀ (circleMap 0 τ θ)‖ / 2 := by
      have := norm_pos_iff.2 (hF0 _ (hcm θ)); positivity
    rw [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
      norm_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) hpos (hx' _ (hcm θ)).le
  · refine Continuous.intervalIntegrable ?_ _ _
    refine (continuous_const.mul (hg.comp (continuous_circleMap 0 τ)).norm).div
      (hF₀c.norm.div_const 2) fun θ ↦ ?_
    have := norm_pos_iff.2 (hF0 _ (hcm θ)); positivity
  · refine Eventually.of_forall fun θ _ ↦ ?_
    simp only [smul_eq_mul]
    exact continuousAt_const.mul (continuousAt_const.div
      (ContinuousAt.comp_of_eq (f := fun x ↦ (x, circleMap 0 τ θ)) (x := x₀) (hF _ (hcm θ))
        (by fun_prop) rfl) (hF0 _ (hcm θ)))

/-- The pairing matrix `(∮ tⁱ⁺⁽ᵈ⁻¹⁻ʲ⁾ / F t)ᵢⱼ` is upper triangular with diagonal `2πi / u 0`,
hence invertible, when `F = tᵈ u` on the circle with `u` holomorphic and nonvanishing on the
closed disc. -/
private theorem det_circleIntegral_ne_zero {d : ℕ} {F u : ℂ → ℂ} {τ : ℝ} (hτ : 0 < τ)
    (hu : ∀ t ∈ closedBall (0 : ℂ) τ, DifferentiableAt ℂ u t)
    (hu0 : ∀ t ∈ closedBall (0 : ℂ) τ, u t ≠ 0) (hF : ∀ t ∈ sphere (0 : ℂ) τ, F t = t ^ d * u t) :
    (Matrix.of fun i j : Fin d ↦ ∮ t in C(0, τ), t ^ ((i : ℕ) + (d - 1 - j)) / F t).det ≠ 0 := by
  rcases d with _ | n
  · simp
  rw [Matrix.det_of_upperTriangular]
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    simp only [Matrix.of_apply]
    have hi : (i : ℕ) + (n + 1 - 1 - i) = n := by omega
    rw [hi, circleIntegral.integral_congr hτ.le (g := fun t ↦ (t - 0)⁻¹ • (u t)⁻¹)]
    · have hdc : DiffContOnCl ℂ (fun t ↦ (u t)⁻¹) (ball (0 : ℂ) τ) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball _ hτ.ne']
        exact fun t ht ↦ ((hu t ht).inv (hu0 t ht)).differentiableWithinAt
      rw [hdc.circleIntegral_sub_inv_smul (mem_ball_self hτ)]
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hu0 0 (mem_closedBall_self hτ.le)]
    · intro t ht
      have ht0 : t ≠ 0 := ne_of_mem_sphere ht hτ.ne'
      have := hu0 t (sphere_subset_closedBall ht)
      simp only [sub_zero, smul_eq_mul, hF t ht]
      field_simp
      ring
  · intro i j hij
    simp only [Matrix.of_apply]
    obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) + (n + 1 - 1 - j) = (n + 1) + m :=
      ⟨i - j - 1, by have : (j : ℕ) < i := hij; omega⟩
    rw [hm, circleIntegral.integral_congr hτ.le (g := fun t ↦ t ^ m / u t)]
    · refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hτ.le
        Set.countable_empty (fun t ht ↦ ?_) (fun t ht ↦ ?_)
      · exact ((continuousAt_id.pow m).div (hu t ht).continuousAt
          (hu0 t ht)).continuousWithinAt
      · have ht' := ball_subset_closedBall ht.1
        exact (differentiableAt_id.pow m).div (hu t ht') (hu0 t ht')
    · intro t ht
      have ht0 : t ≠ 0 := ne_of_mem_sphere ht hτ.ne'
      have := hu0 t (sphere_subset_closedBall ht)
      simp only [hF t ht]
      rw [pow_add]
      field_simp

/-- Pairing a division `g = F χ + ∑ i < n, cᵢ tⁱ` on a circle against `tᵉ / F` kills the
quotient `χ`, holomorphic on the closed disc: the moments of the remainder against the weights
`tⁱ⁺ᵉ / F` are the moments of `g`. -/
private theorem sum_mul_circleIntegral_pow_div_eq {n : ℕ} {F χ g : ℂ → ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hF : ContinuousOn F (sphere 0 τ)) (hF0 : ∀ t ∈ sphere (0 : ℂ) τ, F t ≠ 0)
    (hχ : DifferentiableOn ℂ χ (closedBall 0 τ)) (c : Fin n → ℂ)
    (hg : ∀ t ∈ sphere (0 : ℂ) τ, g t = F t * χ t + ∑ i, c i * t ^ (i : ℕ)) (e : ℕ) :
    ∑ i, c i * (∮ t in C(0, τ), t ^ ((i : ℕ) + e) / F t) =
      ∮ t in C(0, τ), g t * t ^ e / F t := by
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      CircleIntegrable (fun t ↦ c i * (t ^ ((i : ℕ) + e) / F t)) 0 τ := fun i _ ↦
    ContinuousOn.circleIntegrable hτ fun t ht ↦
      continuousWithinAt_const.mul (((continuous_pow _).continuousWithinAt).div (hF t ht) (hF0 t
          ht))
  have hχe : DifferentiableOn ℂ (fun t ↦ χ t * t ^ e) (closedBall 0 τ) :=
    hχ.mul (differentiable_pow e).differentiableOn
  have hzero : (∮ t in C(0, τ), χ t * t ^ e) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hτ Set.countable_empty
      hχe.continuousOn fun t ht ↦
        (hχe.mono ball_subset_closedBall).differentiableAt (isOpen_ball.mem_nhds ht.1)
  calc ∑ i, c i * (∮ t in C(0, τ), t ^ ((i : ℕ) + e) / F t)
      = (∮ t in C(0, τ), χ t * t ^ e) +
          ∮ t in C(0, τ), ∑ i, c i * (t ^ ((i : ℕ) + e) / F t) := by
        simp [hzero, circleIntegral.integral_fun_sum hint, circleIntegral.integral_const_mul]
    _ = ∮ t in C(0, τ), g t * t ^ e / F t := by
        rw [← circleIntegral.integral_add
          ((hχe.continuousOn.mono sphere_subset_closedBall).circleIntegrable hτ)
          (CircleIntegrable.fun_sum _ hint)]
        refine circleIntegral.integral_congr hτ fun t ht ↦ ?_
        have := hF0 t ht
        rw [hg t ht, add_mul, add_div, Finset.sum_mul, Finset.sum_div]
        congr 1
        · field_simp
        · exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_add]; ring

/-- The remainder of a Weierstrass division of `0` by `f` vanishes: pairing `f q + r = 0` with
`tʲ / f (z, t)` over a small circle gives `r · M(z) = 0` for a matrix `M(z)` of circle integrals,
which is invertible at `z = 0` and depends continuously on `z`. -/
private theorem eventuallyEq_zero_of_weierstrassRemainder {k d : ℕ} (hd : 1 ≤ d)
    {f : (Fin k → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfd : analyticOrderAt (fun w : ℂ ↦ f (0, w)) 0 = d)
    {q : (Fin k → ℂ) × ℂ → ℂ} {a : Fin d → (Fin k → ℂ) → ℂ}
    (hq : AnalyticAt ℂ q 0) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (h0 : (fun p ↦ f p * q p + ∑ i, a i p.1 * p.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0) :
    ∀ i, a i =ᶠ[𝓝 0] 0 := by
  have hslice : AnalyticAt ℂ (fun w : ℂ ↦ f (0, w)) 0 :=
    AnalyticAt.comp_of_eq (g := f) (f := fun w : ℂ ↦ ((0 : Fin k → ℂ), w)) hf
      (analyticAt_const.prod analyticAt_id) (by simp)
  obtain ⟨u, hu, hu0, hfu⟩ := hslice.analyticOrderAt_eq_natCast.mp hfd
  obtain ⟨ε₁, hε₁, hfa⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hqa⟩ := hq.exists_ball_analyticOnNhd
  obtain ⟨ε₃, hε₃, heq⟩ := Metric.eventually_nhds_iff_ball.mp h0
  set ε := min ε₁ (min ε₂ ε₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  have hmem : ∀ (z : Fin k → ℂ) (t : ℂ), ‖z‖ < ε → ‖t‖ < ε →
      (z, t) ∈ ball (0 : (Fin k → ℂ) × ℂ) ε₁ ∧ (z, t) ∈ ball (0 : (Fin k → ℂ) × ℂ) ε₂ ∧
        (z, t) ∈ ball (0 : (Fin k → ℂ) × ℂ) ε₃ := by
    intro z t hz ht
    have h : ‖(z, t)‖ < ε := by rw [Prod.norm_def]; exact max_lt hz ht
    refine ⟨mem_ball_zero_iff.2 (h.trans_le (min_le_left _ _)),
      mem_ball_zero_iff.2 (h.trans_le ((min_le_right _ _).trans (min_le_left _ _))),
      mem_ball_zero_iff.2 (h.trans_le ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hgood : ∀ᶠ w in 𝓝 (0 : ℂ), AnalyticAt ℂ u w ∧ u w ≠ 0 ∧ f (0, w) = w ^ d * u w ∧
      w ∈ ball (0 : ℂ) ε :=
    hu.eventually_analyticAt.and ((hu.continuousAt.eventually_ne hu0).and
      ((hfu.mono fun w hw ↦ by simpa using hw).and (ball_mem_nhds 0 hε)))
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.mp hgood
  set τ := δ / 2
  have hτ : 0 < τ := half_pos hδ
  have hPτ : ∀ t ∈ closedBall (0 : ℂ) τ, AnalyticAt ℂ u t ∧ u t ≠ 0 ∧
      f (0, t) = t ^ d * u t ∧ t ∈ ball (0 : ℂ) ε := fun t ht ↦
    hP (lt_of_le_of_lt (mem_closedBall.1 ht) (half_lt_self hδ))
  have hτε : ∀ t ∈ closedBall (0 : ℂ) τ, ‖t‖ < ε := fun t ht ↦ mem_ball_zero_iff.1 (hPτ t ht).2.2.2
  have hf0 : ∀ t ∈ sphere (0 : ℂ) τ, f (0, t) ≠ 0 := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_mem_sphere ht hτ.ne'
    rw [(hPτ t (sphere_subset_closedBall ht)).2.2.1]
    exact mul_ne_zero (pow_ne_zero _ ht0) (hPτ t (sphere_subset_closedBall ht)).2.1
  have hfc : ∀ t ∈ sphere (0 : ℂ) τ,
      ContinuousAt (fun p : (Fin k → ℂ) × ℂ ↦ f (p.1, p.2)) (0, t) := fun t ht ↦
    (hfa _ (hmem 0 t (by simpa using hε) (hτε t (sphere_subset_closedBall ht))).1).continuousAt
  let M : (Fin k → ℂ) → Matrix (Fin d) (Fin d) ℂ := fun z ↦ Matrix.of fun i j ↦
    ∮ t in C(0, τ), t ^ ((i : ℕ) + (d - 1 - j)) / f (z, t)
  have hM0 : (M 0).det ≠ 0 :=
    det_circleIntegral_ne_zero hτ (fun t ht ↦ (hPτ t ht).1.differentiableAt)
      (fun t ht ↦ (hPτ t ht).2.1) fun t ht ↦ (hPτ t (sphere_subset_closedBall ht)).2.2.1
  have hMc : ContinuousAt M 0 := by
    refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
    refine continuousAt_circleIntegral_div (F := fun z t ↦ f (z, t)) hτ.le (continuous_pow
        _) hfc ?_ hf0
    filter_upwards [ball_mem_nhds (0 : Fin k → ℂ) hε] with z hz t ht
    exact (ContinuousAt.comp_of_eq (f := fun s : ℂ ↦ (z, s)) (x := t)
      (hfa _ (hmem z t (mem_ball_zero_iff.1 hz)
        (hτε t (sphere_subset_closedBall ht))).1).continuousAt (by fun_prop) rfl).continuousWithinAt
  have hdet : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), (M z).det ≠ 0 :=
    ((continuous_id.matrix_det).continuousAt.comp hMc).eventually_ne hM0
  have hne : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), ∀ t ∈ sphere (0 : ℂ) τ, f (z, t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) τ).eventually_forall_of_forall_eventually fun t ht ↦
      (hfc t ht).eventually_ne (hf0 t ht)
  have hall : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), ∀ i, a i z = 0 := by
    filter_upwards [hdet, hne, ball_mem_nhds (0 : Fin k → ℂ) hε] with z hz hzne hzε
    have hzε' : ‖z‖ < ε := mem_ball_zero_iff.1 hzε
    have hv : Matrix.vecMul (fun i ↦ a i z) (M z) = 0 := by
      funext j
      have hfz : ContinuousOn (fun t ↦ f (z, t)) (sphere 0 τ) := fun t ht ↦
        (ContinuousAt.comp_of_eq (f := fun s : ℂ ↦ (z, s)) (x := t)
          (hfa _ (hmem z t hzε' (hτε t (sphere_subset_closedBall ht))).1).continuousAt
          (by fun_prop) rfl).continuousWithinAt
      have hqz : DifferentiableOn ℂ (fun t ↦ q (z, t)) (closedBall 0 τ) := fun t ht ↦
        (DifferentiableAt.comp (f := fun s : ℂ ↦ (z, s)) t
          (hqa _ (hmem z t hzε' (hτε t ht)).2.1).differentiableAt
          (by fun_prop)).differentiableWithinAt
      have := sum_mul_circleIntegral_pow_div_eq hτ.le hfz hzne hqz (fun i ↦ a i z) (g := 0)
        (fun t ht ↦ by
          have h1 := heq (z, t) (hmem z t hzε' (hτε t (sphere_subset_closedBall ht))).2.2
          simp only [Pi.zero_apply] at h1 ⊢
          linear_combination -h1) (d - 1 - j)
      simp only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply]
      exact this.trans (by simp [circleIntegral])
    have := Matrix.eq_zero_of_vecMul_eq_zero hz hv
    exact fun i ↦ congrFun this i
  exact fun i ↦ hall.mono fun z hz ↦ hz i

/-- The Weierstrass division of `0` by `f` is trivial. -/
private theorem eventuallyEq_zero_of_weierstrassDivision_zero {k d : ℕ} (hd : 1 ≤ d)
    {f : (Fin k → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfd : analyticOrderAt (fun w : ℂ ↦ f (0, w)) 0 = d)
    {q : (Fin k → ℂ) × ℂ → ℂ} {a : Fin d → (Fin k → ℂ) → ℂ}
    (hq : AnalyticAt ℂ q 0) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (h0 : (fun p ↦ f p * q p + ∑ i, a i p.1 * p.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0) :
    q =ᶠ[𝓝 0] 0 ∧ ∀ i, a i =ᶠ[𝓝 0] 0 := by
  have ha0 := eventuallyEq_zero_of_weierstrassRemainder hd hf hfd hq ha h0
  refine ⟨eventuallyEq_zero_of_mul_eventuallyEq_zero hf ?_ hq ?_, ha0⟩
  · intro hz
    rw [analyticOrderAt_eq_top.mpr hz] at hfd
    exact ENat.top_ne_coe d hfd
  · have hfst : Tendsto (fun p : (Fin k → ℂ) × ℂ ↦ p.1) (𝓝 0) (𝓝 0) :=
      continuous_fst.tendsto 0
    have hall : ∀ᶠ p : (Fin k → ℂ) × ℂ in 𝓝 0, ∀ i, a i p.1 = 0 :=
      Filter.eventually_all.mpr fun i ↦ hfst.eventually (ha0 i)
    filter_upwards [h0, hall] with p hp hp'
    simpa [hp'] using hp

/-- Existence of a Weierstrass division of `h` by `f`. -/
private theorem exists_weierstrassDivision {k d : ℕ} (hd : 1 ≤ d)
    {f : (Fin k → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfd : analyticOrderAt (fun w : ℂ ↦ f (0, w)) 0 = d)
    {h : (Fin k → ℂ) × ℂ → ℂ} (hh : AnalyticAt ℂ h 0) :
    ∃ q : (Fin k → ℂ) × ℂ → ℂ, ∃ a : Fin d → (Fin k → ℂ) → ℂ,
      AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (a i) 0) ∧
        h =ᶠ[𝓝 0] fun p ↦ f p * q p + ∑ i, a i p.1 * p.2 ^ (i : ℕ) := by
  classical
  obtain ⟨pf, rf, hpf⟩ := id hf
  obtain ⟨ph, rh, hph⟩ := id hh
  have hslice : AnalyticAt ℂ (fun w : ℂ ↦ f (0, w)) 0 :=
    AnalyticAt.comp_of_eq (g := f) (f := fun w : ℂ ↦ ((0 : Fin k → ℂ), w)) hf
      (analyticAt_const.prod analyticAt_id) (by simp)
  obtain ⟨u, hu, hu0, hfu⟩ := hslice.analyticOrderAt_eq_natCast.mp hfd
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_min hpf.r_pos hph.r_pos)
  have hgood : ∀ᶠ w in 𝓝 (0 : ℂ), AnalyticAt ℂ u w ∧ u w ≠ 0 ∧ f (0, w) = w ^ d * u w :=
    hu.eventually_analyticAt.and ((hu.continuousAt.eventually_ne hu0).and
      (hfu.mono fun w hw ↦ by simpa using hw))
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.mp hgood
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  set ρ : ℝ := min δ r with hρdef
  have hρ : 0 < ρ := lt_min hδ hr0'
  set τ : ℝ := ρ / 2 with hτdef
  set R : ℝ := 3 * ρ / 4 with hRdef
  have hτ : 0 < τ := by positivity
  have hτR : τ < R := by rw [hτdef, hRdef]; linarith
  have hRρ : R < ρ := by rw [hRdef]; linarith
  have hρr : ENNReal.ofReal ρ ≤ r := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hρf : ENNReal.ofReal ρ < rf := hρr.trans_lt (hr.trans_le (min_le_left _ _))
  have hρh : ENNReal.ofReal ρ < rh := hρr.trans_lt (hr.trans_le (min_le_right _ _))
  have hτf : ENNReal.ofReal τ < rf :=
    (ENNReal.ofReal_le_ofReal (by linarith : τ ≤ ρ)).trans_lt hρf
  have hτh : ENNReal.ofReal τ < rh :=
    (ENNReal.ofReal_le_ofReal (by linarith : τ ≤ ρ)).trans_lt hρh
  have hmemρ : ∀ y : (Fin k → ℂ) × ℂ, ‖y‖ < ρ → ∀ {r' : ENNReal}, ENNReal.ofReal ρ < r' →
      y ∈ Metric.eball (0 : (Fin k → ℂ) × ℂ) r' := by
    intro y hy r' hr'
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hr'
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hy.le
  have hfA : ∀ y : (Fin k → ℂ) × ℂ, ‖y‖ < ρ → AnalyticAt ℂ f y := fun y hy ↦
    hpf.analyticAt_of_mem (hmemρ y hy hρf)
  have hhA : ∀ y : (Fin k → ℂ) × ℂ, ‖y‖ < ρ → AnalyticAt ℂ h y := fun y hy ↦
    hph.analyticAt_of_mem (hmemρ y hy hρh)
  have hnorm : ∀ (z : Fin k → ℂ) (t : ℂ), ‖z‖ < ρ → ‖t‖ < ρ → ‖(z, t)‖ < ρ := by
    intro z t hz ht; rw [Prod.norm_def]; exact max_lt hz ht
  have hu' : ∀ w : ℂ, ‖w‖ < ρ → AnalyticAt ℂ u w ∧ u w ≠ 0 ∧ f (0, w) = w ^ d * u w :=
    fun w hw ↦ hP (by rw [dist_zero_right]; exact hw.trans_le (min_le_left _ _))
  have hf0ne : ∀ t : ℂ, t ≠ 0 → ‖t‖ < ρ → f (0, t) ≠ 0 := by
    intro t ht0 ht
    rw [(hu' t ht).2.2]; exact mul_ne_zero (pow_ne_zero _ ht0) (hu' t ht).2.1
  have hsphτ : ∀ t ∈ sphere (0 : ℂ) τ, ‖t‖ = τ := fun t ht ↦ mem_sphere_zero_iff_norm.mp ht
  have hτρ : τ < ρ := by linarith
  -- the slices are holomorphic
  have hsliceD : ∀ {g : (Fin k → ℂ) × ℂ → ℂ}, (∀ y : (Fin k → ℂ) × ℂ, ‖y‖ < ρ → AnalyticAt ℂ g y)
      → ∀ z : Fin k → ℂ, ‖z‖ < ρ → DifferentiableOn ℂ (fun s ↦ g (z, s)) (ball 0 R) := by
    intro g hg z hz s hs
    have hs' : ‖s‖ < ρ := (mem_ball_zero_iff.mp hs).trans hRρ
    exact (DifferentiableAt.comp (f := fun s : ℂ ↦ (z, s)) s
      (hg _ (hnorm z s hz hs')).differentiableAt (by fun_prop)).differentiableWithinAt
  -- nonvanishing on the annulus, for `z` near `0`
  have hann : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), ∀ t ∈ {t : ℂ | τ ≤ ‖t‖ ∧ ‖t‖ ≤ R}, f (z, t) ≠ 0 := by
    have hK : IsCompact {t : ℂ | τ ≤ ‖t‖ ∧ ‖t‖ ≤ R} :=
      (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
        ((isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const))
        fun t ht ↦ mem_closedBall_zero_iff.2 ht.2
    refine hK.eventually_forall_of_forall_eventually fun t ht ↦ ?_
    have htρ : ‖t‖ < ρ := ht.2.trans_lt hRρ
    have ht0 : t ≠ 0 := by
      rintro rfl; simp at ht; linarith [ht.1]
    have hc : ContinuousAt (fun p : (Fin k → ℂ) × ℂ ↦ f (p.1, p.2)) (0, t) :=
      (hfA _ (hnorm 0 t (by simpa using hρ) htρ)).continuousAt
    exact hc.eventually_ne (hf0ne t ht0 htρ)
  -- continuous maps on the circle
  let S := sphere (0 : ℂ) τ
  let T : C(S, ℂ) := ⟨((↑) : S → ℂ), continuous_subtype_val⟩
  have hT : ∀ t : S, T t = t := fun _ ↦ rfl
  obtain ⟨Fh, hFh, hFhe⟩ := exists_analyticAt_restrict hpf hτ.le hτf
  obtain ⟨Hh, hHh, hHhe⟩ := exists_analyticAt_restrict hph hτ.le hτh
  obtain ⟨Dh, hDh, hDhe⟩ := exists_analyticAt_restrict
    ((ContinuousLinearMap.apply ℂ ℂ (((0 : Fin k → ℂ), (1 : ℂ)) : (Fin k → ℂ) ×
        ℂ)).comp_hasFPowerSeriesOnBall
      hpf.fderiv) hτ.le hτf
  have hsph0 : ∀ t ∈ sphere (0 : ℂ) τ, f (0, t) ≠ 0 := fun t ht ↦
    hf0ne t (ne_of_mem_sphere ht hτ.ne') (by rw [hsphτ t ht]; exact hτρ)
  have hFh0 : ∀ t : S, Fh 0 t ≠ 0 := fun t ↦ by
    rw [hFhe.self_of_nhds t]; exact hsph0 t t.2
  -- the pairing matrix and the moments
  let M : (Fin k → ℂ) → Matrix (Fin d) (Fin d) ℂ := fun z ↦ Matrix.of fun i j ↦
    ∮ t in C(0, τ), t ^ ((i : ℕ) + (d - 1 - j)) / f (z, t)
  let b : (Fin k → ℂ) → Fin d → ℂ := fun z j ↦
    ∮ t in C(0, τ), h (z, t) * t ^ (d - 1 - (j : ℕ)) / f (z, t)
  let a : Fin d → (Fin k → ℂ) → ℂ := fun i z ↦ Matrix.vecMul (b z) (M z)⁻¹ i
  let q : (Fin k → ℂ) × ℂ → ℂ := fun p ↦ (2 * π * I)⁻¹ *
    ∮ t in C(0, τ), (h (p.1, t) - ∑ i, a i p.1 * t ^ (i : ℕ)) / (f (p.1, t) * (t - p.2))
  have hM : ∀ i j, AnalyticAt ℂ (fun z ↦ M z i j) 0 := by
    intro i j
    simp only [M, Matrix.of_apply]
    exact analyticAt_circleIntegral hτ.le (analyticAt_const (v := T ^ ((i : ℕ) + (d - 1 - j))))
      hFh hFh0 (A := fun _ t ↦ t ^ ((i : ℕ) + (d - 1 - j))) (F := fun z t ↦ f (z, t))
      (Eventually.of_forall fun _ t ↦ by simp [hT]) hFhe
  have hb : ∀ j, AnalyticAt ℂ (fun z ↦ b z j) 0 := by
    intro j
    exact analyticAt_circleIntegral hτ.le (hHh.mul (analyticAt_const (v := T ^ (d - 1 - (j : ℕ)))))
      hFh hFh0 (A := fun z t ↦ h (z, t) * t ^ (d - 1 - (j : ℕ))) (F := fun z t ↦ f (z, t))
      (hHhe.mono fun z hz t ↦ by simp [hz t, hT]) hFhe
  have hM0 : (M 0).det ≠ 0 :=
    det_circleIntegral_ne_zero hτ
      (fun t ht ↦ (hu' t ((mem_closedBall_zero_iff.mp ht).trans_lt hτρ)).1.differentiableAt)
      (fun t ht ↦ (hu' t ((mem_closedBall_zero_iff.mp ht).trans_lt hτρ)).2.1)
      fun t ht ↦ (hu' t (by rw [hsphτ t ht]; exact hτρ)).2.2
  have ha : ∀ i, AnalyticAt ℂ (a i) 0 := by
    intro i
    simp only [a, Matrix.vecMul, dotProduct]
    exact Finset.analyticAt_fun_sum _ fun j _ ↦
      (hb j).mul (analyticAt_inv_apply hM hM0 j i)
  -- the logarithmic integral counts the zeros inside the circle
  let W : (Fin k → ℂ) → ℂ := fun z ↦
    ∮ t in C(0, τ), fderiv ℂ f (z, t) ((0 : Fin k → ℂ), (1 : ℂ)) / f (z, t)
  have hWc : ContinuousAt W 0 :=
    (analyticAt_circleIntegral hτ.le hDh hFh hFh0
      (A := fun z t ↦ fderiv ℂ f (z, t) ((0 : Fin k → ℂ), (1 : ℂ))) (F := fun z t ↦ f (z, t))
      (hDhe.mono fun z hz t ↦ by simp [hz t]) hFhe).continuousAt
  have hWslice : ∀ z : Fin k → ℂ, ‖z‖ < ρ →
      W z = ∮ t in C(0, τ), deriv (fun s ↦ f (z, s)) t / f (z, t) := by
    intro z hz
    refine circleIntegral.integral_congr hτ.le fun t ht ↦ ?_
    have htρ : ‖t‖ < ρ := by rw [hsphτ t ht]; exact hτρ
    rw [deriv_slice (hfA _ (hnorm z t hz htρ)).differentiableAt]
  have hW0 : W 0 = 2 * π * I * d := by
    rw [hWslice 0 (by simpa using hρ)]
    have hu1 : DifferentiableOn ℂ u (ball 0 R) := fun t ht ↦
      (hu' t ((mem_ball_zero_iff.mp ht).trans hRρ)).1.differentiableAt.differentiableWithinAt
    have hu2 : ∀ t ∈ sphere (0 : ℂ) τ, u t ≠ 0 := fun t ht ↦
      (hu' t (by rw [hsphτ t ht]; exact hτρ)).2.1
    have key := circleIntegral_logDeriv_sub_pow_mul hτR (c := 0) (by simpa using hτ) hd hu1 hu2
    rw [circleIntegral_logDeriv_eq_zero hτ.le hτR hu1 fun t ht ↦
      (hu' t ((mem_ball_zero_iff.mp ht).trans hRρ)).2.1, add_zero] at key
    rw [← key]
    refine circleIntegral.integral_congr hτ.le fun t ht ↦ ?_
    have htρ : ‖t‖ < ρ := by rw [hsphτ t ht]; exact hτρ
    have hev : (fun s ↦ f (0, s)) =ᶠ[𝓝 t] fun w ↦ (w - 0) ^ d * u w := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr htρ)] with s hs
      rw [sub_zero]; exact (hu' s (mem_ball_zero_iff.mp hs)).2.2
    rw [hev.deriv_eq, (hu' t htρ).2.2, sub_zero]
  have hWev : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), ‖W z - 2 * π * I * d‖ < 2 * π := by
    have := hWc.eventually (Metric.ball_mem_nhds (W 0) (by positivity : (0 : ℝ) < 2 * π))
    filter_upwards [this] with z hz
    rwa [dist_eq_norm, hW0] at hz
  have hdet : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), (M z).det ≠ 0 :=
    (analyticAt_det hM).continuousAt.eventually_ne hM0
  have hzρ : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), ‖z‖ < ρ := by
    filter_upwards [ball_mem_nhds (0 : Fin k → ℂ) hρ] with z hz using mem_ball_zero_iff.mp hz
  -- division in `w` for each fixed small `z`
  have key : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ), ∀ w ∈ ball (0 : ℂ) τ,
      h (z, w) = f (z, w) * q (z, w) + ∑ i, a i z * w ^ (i : ℕ) := by
    filter_upwards [hzρ, hann, hWev, hdet] with z hz hzann hzW hzdet
    have hFd := hsliceD hfA z hz
    have hHd := hsliceD hhA z hz
    have hF0 : ∀ t ∈ ball (0 : ℂ) R, τ ≤ ‖t‖ → f (z, t) ≠ 0 := fun t ht hτt ↦
      hzann t ⟨hτt, (mem_ball_zero_iff.mp ht).le⟩
    obtain ⟨n, hn, hdiv⟩ := oneVar_division hτ hτR hFd hF0
    have hnd : n = d := by
      rw [hWslice z hz, hn, ← mul_sub, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg pi_pos.le] at hzW
      have h1 : ‖((n : ℂ) - d)‖ < 1 := by
        have : (0 : ℝ) < 2 * π := by positivity
        nlinarith [norm_nonneg ((n : ℂ) - d)]
      rw [show ((n : ℂ) - d) = (((n : ℝ) - d : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_lt] at h1
      obtain ⟨h1, h2⟩ := h1
      have h3 : (n : ℝ) < d + 1 := by linarith
      have h4 : (d : ℝ) < n + 1 := by linarith
      have h3' : n < d + 1 := by exact_mod_cast h3
      have h4' : d < n + 1 := by exact_mod_cast h4
      omega
    subst hnd
    obtain ⟨χ, P, hPdeg, hχ, hχe⟩ := hdiv _ hHd
    have hsub : closedBall (0 : ℂ) τ ⊆ ball 0 R := closedBall_subset_ball hτR
    have hsph : ∀ t ∈ sphere (0 : ℂ) τ, f (z, t) ≠ 0 := fun t ht ↦
      hF0 t (hsub (sphere_subset_closedBall ht)) (by rw [hsphτ t ht])
    have hPnat : P.natDegree < n := by
      rcases eq_or_ne P 0 with h0 | h0
      · rw [h0, Polynomial.natDegree_zero]; omega
      · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hPdeg
    have hPeval : ∀ w, P.eval w = ∑ i : Fin n, P.coeff i * w ^ (i : ℕ) := by
      intro w
      rw [Polynomial.eval_eq_sum_range' hPnat, ← Fin.sum_univ_eq_sum_range]
    have hfc : ∀ t ∈ sphere (0 : ℂ) τ, ContinuousAt (fun s ↦ f (z, s)) t := fun t ht ↦
      (hFd.differentiableAt (isOpen_ball.mem_nhds (hsub (sphere_subset_closedBall
          ht)))).continuousAt
    -- the coefficients of the remainder are the `a i z`
    have hvec : Matrix.vecMul (fun i : Fin n ↦ P.coeff (i : ℕ)) (M z) = b z := funext fun j ↦
      sum_mul_circleIntegral_pow_div_eq hτ.le (fun t ht ↦ (hfc t ht).continuousWithinAt) hsph
        (hχ.mono hsub) _ (fun t ht ↦ by rw [hχe t (hsub (sphere_subset_closedBall ht)), hPeval t])
        (n - 1 - j)
    have hcoef : ∀ i, a i z = P.coeff i := by
      intro i
      have : Matrix.vecMul (b z) (M z)⁻¹ = fun i : Fin n ↦ P.coeff (i : ℕ) := by
        rw [← hvec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hzdet),
          Matrix.vecMul_one]
      exact congrFun this i
    intro w hw
    have hwR : w ∈ ball (0 : ℂ) R := ball_subset_ball hτR.le hw
    have hq : q (z, w) = χ w := by
      simp only [q]
      have hχd : DifferentiableOn ℂ χ (closedBall 0 τ) := hχ.mono hsub
      rw [circleIntegral.integral_congr hτ.le (g := fun t ↦ (t - w)⁻¹ • χ t),
        hχd.circleIntegral_sub_inv_smul hw, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_mul]
      intro t ht
      have h1 := hχe t (hsub (sphere_subset_closedBall ht))
      have h2 := hsph t ht
      have h3 : t - w ≠ 0 := by
        intro h0
        rw [sub_eq_zero] at h0
        subst h0
        rw [mem_ball_zero_iff, hsphτ t ht] at hw
        exact lt_irrefl _ hw
      simp only [hcoef, smul_eq_mul]
      rw [h1, hPeval t]
      field_simp
      ring
    rw [hq, hχe w hwR, hPeval w]
    simp only [hcoef]
  -- conclusion
  refine ⟨q, a, ?_, ha, ?_⟩
  · have hfstA : AnalyticAt ℂ (fun p : (Fin k → ℂ) × ℂ ↦ p.1) 0 := analyticAt_fst
    have hsndA : AnalyticAt ℂ (fun p : (Fin k → ℂ) × ℂ ↦ p.2) 0 := analyticAt_snd
    have hnum : AnalyticAt ℂ (fun p : (Fin k → ℂ) × ℂ ↦
        Hh p.1 - ∑ i, a i p.1 • T ^ (i : ℕ)) 0 :=
      (hHh.comp_of_eq hfstA rfl).sub (Finset.analyticAt_fun_sum _ fun i _ ↦
        ((ha i).comp_of_eq hfstA rfl).smul analyticAt_const)
    have hden : AnalyticAt ℂ (fun p : (Fin k → ℂ) × ℂ ↦
        Fh p.1 * (T - p.2 • (1 : C(S, ℂ)))) 0 :=
      (hFh.comp_of_eq hfstA rfl).mul (analyticAt_const.sub (hsndA.smul analyticAt_const))
    have hfst : Tendsto (fun p : (Fin k → ℂ) × ℂ ↦ p.1) (𝓝 0) (𝓝 0) :=
      continuous_fst.tendsto 0
    refine analyticAt_const.mul (analyticAt_circleIntegral hτ.le hnum hden ?_
      (A := fun p t ↦ h (p.1, t) - ∑ i, a i p.1 * t ^ (i : ℕ))
      (F := fun p t ↦ f (p.1, t) * (t - p.2)) ?_ ?_)
    · intro t
      have := hFh0 t
      simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, hT]
      simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, sub_zero]
      exact mul_ne_zero this (ne_of_mem_sphere t.2 hτ.ne')
    · filter_upwards [hfst.eventually hHhe] with p hp t
      simp [hp t, hT]
    · filter_upwards [hfst.eventually hFhe] with p hp t
      simp [hp t, hT]
  · have hfst : Tendsto (fun p : (Fin k → ℂ) × ℂ ↦ p.1) (𝓝 0) (𝓝 0) :=
      continuous_fst.tendsto 0
    have hsnd : Tendsto (fun p : (Fin k → ℂ) × ℂ ↦ p.2) (𝓝 0) (𝓝 0) :=
      continuous_snd.tendsto 0
    filter_upwards [hfst.eventually key, hsnd.eventually (ball_mem_nhds (0 : ℂ) hτ)]
      with p hp1 hp2 using hp1 p.2 hp2

end MMP.Analytic.Proof_lem_mmp_convergent_weierstrass_division

namespace MMP.Convergent

open MMP.Analytic.Proof_lem_mmp_convergent_weierstrass_division in
/-- **Weierstrass division** in the ring of convergent power series `ℂ{z, w}`: if
`w ↦ f (0, w)` has order exactly `d ≥ 1` at `0`, then every germ `h` analytic at `0` is
`f * q + ∑ i < d, a i (z) * w ^ i` near `0`, with `q` and the `a i` analytic at `0`, and the
germs of `q` and of the `a i` are unique. -/
@[mmp "lem_mmp_convergent_weierstrass_division"]
public theorem existsUnique_weierstrassDivision {k d : ℕ} (hd : 1 ≤ d)
    {f : (Fin k → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfd : analyticOrderAt (fun w : ℂ ↦ f (0, w)) 0 = d)
    {h : (Fin k → ℂ) × ℂ → ℂ} (hh : AnalyticAt ℂ h 0) :
    ∃ q : (Fin k → ℂ) × ℂ → ℂ, ∃ a : Fin d → (Fin k → ℂ) → ℂ,
      (AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (a i) 0) ∧
        h =ᶠ[𝓝 0] fun p ↦ f p * q p + ∑ i, a i p.1 * p.2 ^ (i : ℕ)) ∧
      ∀ (q' : (Fin k → ℂ) × ℂ → ℂ) (a' : Fin d → (Fin k → ℂ) → ℂ),
        AnalyticAt ℂ q' 0 → (∀ i, AnalyticAt ℂ (a' i) 0) →
        (h =ᶠ[𝓝 0] fun p ↦ f p * q' p + ∑ i, a' i p.1 * p.2 ^ (i : ℕ)) →
        q' =ᶠ[𝓝 0] q ∧ ∀ i, a' i =ᶠ[𝓝 0] a i := by
  obtain ⟨q, a, hq, ha, hqa⟩ := exists_weierstrassDivision hd hf hfd hh
  refine ⟨q, a, ⟨hq, ha, hqa⟩, fun q' a' hq' ha' hqa' => ?_⟩
  have key := eventuallyEq_zero_of_weierstrassDivision_zero hd hf hfd (hq'.sub hq)
    (fun i => (ha' i).sub (ha i)) (q := q' - q) (a := fun i => a' i - a i) <| by
    filter_upwards [hqa, hqa'] with p h1 h2
    simp only [Pi.sub_apply, Pi.zero_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    linear_combination h1 - h2
  refine ⟨?_, fun i => ?_⟩
  · filter_upwards [key.1] with p hp
    exact sub_eq_zero.mp hp
  · filter_upwards [key.2 i] with z hz
    exact sub_eq_zero.mp hz

end MMP.Convergent

end

/-!
# The ring of convergent germs is a regular local ring

The ring `ℂ{z₁, …, zₙ}` of convergent power series, realised as the ring
`MMP.Analytic.holGerms 0` of germs at the origin of `ℂⁿ` of holomorphic functions, is a
Noetherian regular local ring of Krull dimension `n`. Its maximal ideal is generated by the
germs of the coordinate functions `z₁, …, zₙ`, and its completion at the maximal ideal is the
formal power series ring `ℂ[[z₁, …, zₙ]]`, by the isomorphism that is the identity on
polynomials.

## Main results

* `MMP.Analytic.isRegularLocalRing_holGerms`: regularity, dimension, generators of the maximal
  ideal and the completion of `holGerms (0 : Fin n → ℂ)`.

## Implementation notes

Regularity is `IsRegularLocalRing`, which contains the local and Noetherian properties; it is
stated as an existential so that the remaining clauses can use the local ring structure. The
completion is `AdicCompletion` at the maximal ideal, and the isomorphism with
`MvPowerSeries (Fin n) ℂ` is pinned by its value on the image of `MvPolynomial (Fin n) ℂ` under
`MMP.Analytic.polyGermHom`: there it is the inclusion of polynomials into power series. This
characterises it, since polynomial germs are dense in the completion and ring maps between
these complete local `ℂ`-algebras are continuous.

## References

* [Grauert, Remmert, *Coherent analytic sheaves*], Chapter 2.
-/

section

open IsLocalRing Filter Topology MMP.Analytic
open Complex Metric Real

variable {n : ℕ}

namespace MMP.Analytic.Proof_lem_mmp_convergent_germ_ring_noetherian_regular

/-- Evaluation of a holomorphic germ at the origin. -/
private noncomputable def evalZero (n : ℕ) : holGerms (0 : Fin n → ℂ) →+* ℂ :=
  (Germ.valueRingHom (X := Fin n → ℂ) (x := 0) (E := ℂ)).comp (holGerms (0 : Fin n → ℂ)).subtype

/-- A holomorphic germ not vanishing at the base point is a unit. -/
private lemma isUnit_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E}
    {g : holGerms p} {f : E → ℂ} (hfg : (f : Germ (𝓝 p) ℂ) = g)
    (hf : ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y) (hval : f p ≠ 0) : IsUnit g := by
  have hne : ∀ᶠ y in 𝓝 p, f y ≠ 0 := hf.self_of_nhds.continuousAt.eventually_ne hval
  refine IsUnit.of_mul_eq_one (b := ⟨(f⁻¹ : E → ℂ), coe_mem_holGerms
    ((hf.and hne).mono fun y hy => hy.1.inv hy.2)⟩) (Subtype.ext ?_)
  change (g : Germ (𝓝 p) ℂ) * ((f⁻¹ : E → ℂ) : Germ _ ℂ) = 1
  rw [← hfg]
  change ((f * f⁻¹ : E → ℂ) : Germ (𝓝 p) ℂ) = ((1 : E → ℂ) : Germ (𝓝 p) ℂ)
  exact Germ.coe_eq.2 (hne.mono fun y hy => by simp [hy])

private lemma evalZero_eq {g : holGerms (0 : Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (hfg : (f : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = g) : evalZero n g = f 0 := by
  simp only [evalZero, RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, ← hfg]
  rfl

private lemma isUnit_iff_evalZero_ne_zero (g : holGerms (0 : Fin n → ℂ)) :
    IsUnit g ↔ evalZero n g ≠ 0 := by
  refine ⟨fun hg => (hg.map (evalZero n)).ne_zero, fun h0 => ?_⟩
  obtain ⟨f, hfg, hf⟩ := g.2
  exact isUnit_of_ne_zero hfg hf (evalZero_eq hfg ▸ h0)

private lemma isLocalRing_holGerms (n : ℕ) : IsLocalRing (holGerms (0 : Fin n → ℂ)) := by
  have : Nontrivial (holGerms (0 : Fin n → ℂ)) := (evalZero n).domain_nontrivial
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  simp only [mem_nonunits_iff, isUnit_iff_evalZero_ne_zero, not_not, map_add] at *
  rw [ha, hb, add_zero]

attribute [local instance] isLocalRing_holGerms

section Osgood

private lemma continuous_torusMap' {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Continuous (torusMap
    c R) := by
  unfold torusMap; fun_prop

private lemma norm_torusMap_sub {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) (i :
    Fin n) :
    ‖torusMap c (fun _ => r) θ i - c i‖ = r := by
  simp [torusMap, norm_exp_ofReal_mul_I, abs_of_nonneg hr]

private lemma torusMap_mem_closedBall {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) :
    torusMap c (fun _ => r) θ ∈ closedBall c r := by
  rw [mem_closedBall, dist_pi_le_iff hr]
  intro i; rw [dist_eq_norm, norm_torusMap_sub c hr]

private lemma norm_sub_lt_of_mem_ball {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hz : z ∈ ball c r) (i :
    Fin n) :
    ‖z i - c i‖ < r := by
  rw [← dist_eq_norm]
  exact lt_of_le_of_lt (dist_le_pi_dist z c i) (mem_ball.1 hz)

private lemma torusMap_sub_ne_zero {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r) (hz : z ∈ ball c
    r)
    (θ : Fin n → ℝ) (i : Fin n) : torusMap c (fun _ => r) θ i - z i ≠ 0 := by
  intro h
  have h1 := norm_torusMap_sub c hr θ i
  have h2 := norm_sub_lt_of_mem_ball hz i
  rw [sub_eq_zero.1 h] at h1
  linarith

private lemma differentiable_cons {k : ℕ} (t : ℂ) :
    Differentiable ℂ (fun y : Fin k → ℂ => (Fin.cons t y : Fin (k+1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cons_succ]; fun_prop

private lemma differentiable_cons_left {k : ℕ} (y : Fin k → ℂ) :
    Differentiable ℂ (fun t : ℂ => (Fin.cons t y : Fin (k+1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; fun_prop
  · simp

private lemma cons_mem_closedBall {k : ℕ} {c : Fin (k+1) → ℂ} {r : ℝ} (hr : 0 ≤ r) {t : ℂ} {y :
    Fin k → ℂ}
    (ht : t ∈ closedBall (c 0) r) (hy : y ∈ closedBall (Fin.tail c) r) :
    (Fin.cons t y : Fin (k+1) → ℂ) ∈ closedBall c r := by
  rw [mem_closedBall, dist_pi_le_iff hr] at *
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ht
  · simpa [Fin.tail] using hy j

/-- Cauchy integral formula on a polydisc. -/
private lemma torusIntegral_prod_sub_inv_smul {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r :
    ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c r)) (hz : z ∈ ball c r) :
    (∯ w in T(c, fun _ => r), (∏ i, (w i - z i)⁻¹) • f w) = (2 * π * I) ^ n • f z := by
  induction n with
  | zero =>
    simp [Subsingleton.elim c z]
  | succ k ih =>
    have hr : 0 ≤ r := le_trans dist_nonneg (mem_ball.1 hz).le
    have hint : TorusIntegrable (fun w : Fin (k+1) → ℂ => (∏ i, (w i - z i)⁻¹) • f w) c (fun _ =>
        r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      show Continuous fun θ => (∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹) • f (torusMap c (fun _
          => r) θ)
      refine Continuous.smul (M := ℂ) ?_ (hf.continuousOn.comp_continuous (continuous_torusMap' _ _)
        (torusMap_mem_closedBall c hr))
      have hcont : ∀ i, Continuous fun θ : Fin (k+1) → ℝ => (torusMap c (fun _ => r) θ i - z i)⁻¹ :=
        fun i => (((continuous_apply i).comp (continuous_torusMap' c fun _ => r)).sub
          continuous_const).inv₀ (torusMap_sub_ne_zero hr hz · i)
      exact continuous_finset_prod Finset.univ fun i _ => hcont i
    rw [torusIntegral_succ hint]
    have hz' : Fin.tail z ∈ ball (Fin.tail c) r := by
      rw [mem_ball, dist_pi_lt_iff (lt_of_le_of_lt dist_nonneg (mem_ball.1 hz))]
      intro j; rw [dist_eq_norm]; exact norm_sub_lt_of_mem_ball hz j.succ
    have hz0 : z 0 ∈ ball (c 0) r := by
      rw [mem_ball, dist_eq_norm]; exact norm_sub_lt_of_mem_ball hz 0
    rw [circleIntegral.integral_congr hr (g := fun t => (2 * π * I) ^ k • ((t - z 0)⁻¹ • f
        (Fin.cons t (Fin.tail z))))]
    · rw [circleIntegral.integral_smul, DifferentiableOn.circleIntegral_sub_inv_smul _ hz0,
        Fin.cons_self_tail, smul_smul, pow_succ]
      refine hf.comp (differentiable_cons_left _).differentiableOn fun t ht => ?_
      exact cons_mem_closedBall hr ht (ball_subset_closedBall hz')
    · intro t ht
      have ht' : t ∈ closedBall (c 0) r := sphere_subset_closedBall ht
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_smul]
      rw [torusIntegral_smul, smul_comm]
      congr 1
      have := ih (f := fun y => f (Fin.cons t y)) (c := Fin.tail c) (z := Fin.tail z)
        (hf.comp (differentiable_cons t).differentiableOn fun y hy => cons_mem_closedBall hr ht'
            hy) hz'
      exact this

/-- A complex function differentiable on a closed polydisc is analytic at its center. -/
private lemma analyticAt_of_differentiableOn_closedBall {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall c r)) :
    AnalyticAt ℂ f c := by
  set S : Set (Fin n → ℝ) := Set.Icc 0 fun _ => 2 * π
  set e : (Fin n → ℝ) → (Fin n → Circle) := fun θ i => Circle.exp (θ i)
  have he : Continuous e :=
    continuous_pi fun i => (map_continuous Circle.exp).comp (continuous_apply i)
  let u : Fin n → (Fin n → ℂ) → C(Fin n → Circle, ℂ) := fun i z =>
    ⟨fun w => c i + r * (w i : ℂ) - z i, by fun_prop⟩
  have hu : ∀ i, u i = fun z => (⟨fun w => c i + r * (w i : ℂ), by fun_prop⟩ : C(Fin n → Circle,
      ℂ)) - z i • (1 : C(Fin n → Circle, ℂ)) := by
    intro i; funext z; ext w
    rw [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      ContinuousMap.coe_mk]
    simp [u]
  have hunit : ∀ z ∈ ball c r, ∀ i, IsUnit (u i z) := by
    intro z hz i
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro w h
    have h2 := norm_sub_lt_of_mem_ball hz i
    have : z i - c i = r * (w i : ℂ) := by simp [u] at h; linear_combination -h
    rw [this, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg
        hr.le] at h2
    exact lt_irrefl _ h2
  set K : (Fin n → ℂ) → C(Fin n → Circle, ℂ) := fun z => ∏ i, Ring.inverse (u i z)
  have hK : AnalyticAt ℂ K c := by
    have := Finset.analyticAt_prod (𝕜 := ℂ) (c := c) (f := fun i z => Ring.inverse (u i z))
      Finset.univ fun i _ => by
        refine (analyticAt_inverse (𝕜 := ℂ) (hunit c (mem_ball_self hr) i).unit).comp_of_eq ?_ rfl
        rw [hu i]
        exact analyticAt_const.sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt c).smul
            analyticAt_const)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [K, Finset.prod_apply]
  have hKe : ∀ z ∈ ball c r, ∀ θ, K z (e θ) = ∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹ := by
    intro z hz θ
    show (∏ i, Ring.inverse (u i z)) (e θ) = _
    rw [ContinuousMap.prod_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : (Ring.inverse (u i z) * u i z) (e θ) = (1 : C(Fin n → Circle, ℂ)) (e θ) := by
      rw [Ring.inverse_mul_cancel _ (hunit z hz i)]
    rw [ContinuousMap.mul_apply, ContinuousMap.one_apply] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    simp [u, e, torusMap, Circle.coe_exp]
  set Φ : (Fin n → ℝ) → ℂ := fun θ =>
    (∏ i, (r : ℂ) * exp (θ i * I) * I) * f (torusMap c (fun _ => r) θ)
  have hΦ : Continuous Φ :=
    (continuous_finset_prod _ fun i _ => by fun_prop).mul
      (hf.continuousOn.comp_continuous (continuous_torusMap' _ _) (torusMap_mem_closedBall c hr.le))
  have hint : ∀ g : C(Fin n → Circle, ℂ), MeasureTheory.IntegrableOn (fun θ => Φ θ * g (e θ)) S :=
    fun g => (hΦ.mul (g.continuous.comp he)).integrableOn_Icc
  let L : C(Fin n → Circle, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ θ in S, Φ θ * g (e θ)
      map_add' := fun g h => by
        show ∫ θ in S, Φ θ * (g + h) (e θ) = (∫ θ in S, Φ θ * g (e θ)) + ∫ θ in S, Φ θ * h (e θ)
        simp only [ContinuousMap.add_apply, mul_add]
        exact MeasureTheory.integral_add (hint g) (hint h)
      map_smul' := fun a g => by
        show ∫ θ in S, Φ θ * (a • g) (e θ) = a • ∫ θ in S, Φ θ * g (e θ)
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]
        exact MeasureTheory.integral_const_mul a _ }
  let Λ : C(Fin n → Circle, ℂ) →L[ℂ] ℂ := L.mkContinuous (∫ θ in S, ‖Φ θ‖) fun g => by
    change ‖∫ θ in S, Φ θ * g (e θ)‖ ≤ _
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.norm_integral_le_of_norm_le
      ((hΦ.norm.mul continuous_const).integrableOn_Icc) (Filter.Eventually.of_forall fun θ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _)
  have heq : ∀ z ∈ ball c r, f z = ((2 * π * I) ^ n)⁻¹ * Λ (K z) := by
    intro z hz
    have h2 : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [pi_ne_zero, I_ne_zero])
    rw [eq_inv_mul_iff_mul_eq₀ h2, ← smul_eq_mul, ← torusIntegral_prod_sub_inv_smul hf hz]
    change torusIntegral _ _ _ = ∫ θ in S, Φ θ * K z (e θ)
    unfold torusIntegral
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [Φ, hKe z hz, smul_eq_mul]
    ring
  have hA : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * Λ (K z)) c :=
    analyticAt_const.mul ((Λ.analyticAt _).comp hK)
  refine hA.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  exact (heq z hz).symm

end Osgood

/-- A function on a finite-dimensional complex space that is complex differentiable near a point
is analytic there (Osgood's lemma). -/
private lemma analyticAt_of_eventually_differentiableAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {f : E → ℂ} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y) : AnalyticAt ℂ f x := by
  let φ : (Fin (Module.finrank ℂ E) → ℂ) ≃L[ℂ] E :=
    (Module.finBasis ℂ E).equivFun.symm.toContinuousLinearEquiv
  have hφ : Tendsto φ (𝓝 (φ.symm x)) (𝓝 x) :=
    φ.continuous.tendsto' _ _ (φ.apply_symm_apply x)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hφ.eventually hf)
  have hg : AnalyticAt ℂ (f ∘ φ) (φ.symm x) :=
    analyticAt_of_differentiableOn_closedBall (half_pos hr) fun y hy =>
      ((hball y (Metric.closedBall_subset_ball (half_lt_self hr) hy)).comp y
        φ.differentiableAt).differentiableWithinAt
  have := hg.comp_of_eq ((φ.symm : E →L[ℂ] _).analyticAt x) rfl
  simpa [Function.comp_def] using this

private lemma eventually_differentiableAt_of_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y :=
  hf.eventually_analyticAt.mono fun _ hy => hy.differentiableAt

/-- Hadamard's lemma at the origin: a germ holomorphic near `0` and vanishing at `0` is
`∑ i, zᵢ hᵢ` with `hᵢ` holomorphic near `0`. Weierstrass division by the coordinate `z₀` writes
`f = z₀ q + a(z₁, …)`, and the remainder `a` is treated by induction. -/
private lemma exists_eventuallyEq_sum_mul : ∀ (n : ℕ) {f : (Fin n → ℂ) → ℂ},
    (∀ᶠ y in 𝓝 0, DifferentiableAt ℂ f y) → f 0 = 0 →
    ∃ h : Fin n → (Fin n → ℂ) → ℂ, (∀ i, ∀ᶠ y in 𝓝 0, DifferentiableAt ℂ (h i) y) ∧
      f =ᶠ[𝓝 0] fun z => ∑ i, z i * h i z
  | 0, f, _, hf0 => ⟨Fin.elim0, fun i => i.elim0,
      Eventually.of_forall fun z => by rw [Subsingleton.elim z 0, hf0]; simp⟩
  | k + 1, f, hf, hf0 => by
    set c : (Fin k → ℂ) × ℂ → (Fin (k + 1) → ℂ) := fun p => Fin.cons p.2 p.1
    have hc : Differentiable ℂ c := differentiable_pi.2 fun i =>
      Fin.cases (by simp only [c, Fin.cons_zero]; fun_prop)
        (fun j => by simp only [c, Fin.cons_succ]; fun_prop) i
    have hc0 : c 0 = 0 := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [c]
    have hct : Tendsto c (𝓝 0) (𝓝 0) := hc0 ▸ hc.continuous.tendsto 0
    have hF : ∀ᶠ y in 𝓝 0, DifferentiableAt ℂ (f ∘ c) y :=
      (hct.eventually hf).mono fun y hy => hy.comp y (hc y)
    have hord : analyticOrderAt (fun w : ℂ => (Prod.snd : (Fin k → ℂ) × ℂ → ℂ) (0, w)) 0 =
        ((1 : ℕ) : ℕ∞) :=
      (analyticAt_id.analyticOrderAt_eq_natCast).2
        ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun z => by simp⟩
    obtain ⟨q, a, ⟨hq, ha, heq⟩, -⟩ := MMP.Convergent.existsUnique_weierstrassDivision le_rfl
      analyticAt_snd hord (analyticAt_of_eventually_differentiableAt hF)
    have ha0 : a 0 0 = 0 := by
      have := heq.self_of_nhds
      simp only [Function.comp_apply, hc0, hf0, Prod.snd_zero, Prod.fst_zero, zero_mul,
        zero_add, Fin.sum_univ_one, Fin.val_zero, pow_zero, mul_one] at this
      exact this.symm
    obtain ⟨h, hh, hheq⟩ := exists_eventuallyEq_sum_mul k
      (eventually_differentiableAt_of_analyticAt (ha 0)) ha0
    set t : (Fin (k + 1) → ℂ) → (Fin k → ℂ) × ℂ := fun x => (Fin.tail x, x 0)
    have htail : Differentiable ℂ (Fin.tail : (Fin (k + 1) → ℂ) → Fin k → ℂ) :=
      differentiable_pi.2 fun j => by simp only [Fin.tail]; fun_prop
    have ht : Differentiable ℂ t := htail.prodMk (by fun_prop)
    have htt : Tendsto t (𝓝 0) (𝓝 0) := ht.continuous.tendsto' 0 0 rfl
    have htailt : Tendsto (Fin.tail : (Fin (k + 1) → ℂ) → Fin k → ℂ) (𝓝 0) (𝓝 0) :=
      htail.continuous.tendsto' 0 0 rfl
    refine ⟨Fin.cons (q ∘ t) (fun i => h i ∘ Fin.tail), fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (htt.eventually (eventually_differentiableAt_of_analyticAt hq)).mono
          fun y hy => hy.comp y (ht y)
      · simp only [Fin.cons_succ]
        exact (htailt.eventually (hh j)).mono fun y hy => hy.comp y (htail y)
    · filter_upwards [htt.eventually heq, htailt.eventually hheq] with x h1 h2
      have hx : (f ∘ c) (t x) = f x := by simp [c, t, Fin.cons_self_tail]
      rw [← hx, h1, Fin.sum_univ_succ (n := k)]
      simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, mul_one, Fin.cons_zero,
        Fin.cons_succ, Function.comp_apply, t] at h2 ⊢
      rw [h2]
      rfl

/-- Hadamard's lemma for convergent series: the germs vanishing at the origin are the ideal
generated by the coordinates. -/
private lemma maximalIdeal_eq_span_coordinates (n : ℕ) :
    maximalIdeal (holGerms (0 : Fin n → ℂ)) =
      Ideal.span (Set.range fun i : Fin n ↦ polyGermHom 0 (MvPolynomial.X i)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨f, hfg, hf⟩ := g.2
    have hf0 : f 0 = 0 := by
      by_contra h
      exact hg ((isUnit_iff_evalZero_ne_zero g).2 (evalZero_eq hfg ▸ h))
    obtain ⟨h, hh, hfh⟩ := exists_eventuallyEq_sum_mul n hf hf0
    have : g = ∑ i, polyGermHom 0 (MvPolynomial.X i) *
        ⟨((h i : (Fin n → ℂ) → ℂ) : Germ _ ℂ), coe_mem_holGerms (hh i)⟩ := by
      apply Subtype.ext
      rw [← hfg, Germ.coe_eq.2 hfh]
      simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, coe_polyGermHom,
        MvPolynomial.eval_X]
      have e : (fun z => ∑ i, z i * h i z) = ∑ i, (fun y : Fin n → ℂ => y i) * h i := by
        funext z; simp [Finset.sum_apply]
      rw [e]
      exact (map_sum (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)))
        (fun i => (fun y : Fin n → ℂ => y i) * h i) _).trans (by simp only [map_mul]; rfl)
    rw [this]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    intro hu
    have := (isUnit_iff_evalZero_ne_zero _).1 hu
    apply this
    show ((polyGermHom 0 (MvPolynomial.X i) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ)).value = 0
    simp

/-- A continuous linear equivalence identifies the rings of holomorphic germs at the origin. -/
private noncomputable def holGermsEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (φ : E ≃L[ℂ] F) :
    holGerms (0 : F) ≃+* holGerms (0 : E) :=
  RingEquiv.ofRingHom (holPullback φ φ.differentiable (φ.continuous.tendsto' 0 0 (map_zero φ)))
    (holPullback φ.symm φ.symm.differentiable (φ.symm.continuous.tendsto' 0 0 (map_zero _)))
    (RingHom.ext fun g => Subtype.ext <| by
      obtain ⟨f, hf, -⟩ := g.2
      simp only [RingHom.coe_comp, Function.comp_apply, coe_holPullback, RingHom.id_apply, ← hf]
      exact Germ.coe_eq.2 (Eventually.of_forall fun x => by simp))
    (RingHom.ext fun g => Subtype.ext <| by
      obtain ⟨f, hf, -⟩ := g.2
      simp only [RingHom.coe_comp, Function.comp_apply, coe_holPullback, RingHom.id_apply, ← hf]
      exact Germ.coe_eq.2 (Eventually.of_forall fun x => by simp))

/-- The Weierstrass step: over a Noetherian ring of germs in `k` variables, an ideal of germs in
`(z, w)` containing a germ `f` with `w ↦ f (0, w)` not identically zero is finitely generated.
By division by `f`, the ideal is generated by `f` and the polynomials in `w` of degree `< d` that
it contains, and the coefficient vectors of the latter form a submodule of a finite free module
over the Noetherian coefficient ring. -/
private lemma fg_of_mem_of_not_eventuallyEq_zero {k : ℕ}
    [IsNoetherianRing (holGerms (0 : Fin k → ℂ))] (I : Ideal (holGerms (0 : (Fin k → ℂ) × ℂ)))
    {g : holGerms (0 : (Fin k → ℂ) × ℂ)} (hgI : g ∈ I) {f : (Fin k → ℂ) × ℂ → ℂ}
    (hfg : (f : Germ (𝓝 (0 : (Fin k → ℂ) × ℂ)) ℂ) = g)
    (hf : ∀ᶠ y in 𝓝 (0 : (Fin k → ℂ) × ℂ), DifferentiableAt ℂ f y)
    (hord : ¬ (fun w : ℂ => f (0, w)) =ᶠ[𝓝 0] 0) : I.FG := by
  classical
  by_cases hf0 : f 0 ≠ 0
  · rw [Ideal.eq_top_of_isUnit_mem _ hgI (isUnit_of_ne_zero hfg hf hf0)]
    exact ⟨{1}, by simp⟩
  push Not at hf0
  have hfa : AnalyticAt ℂ f 0 := analyticAt_of_eventually_differentiableAt hf
  have hfa' : AnalyticAt ℂ (fun w : ℂ => f (0, w)) 0 :=
    hfa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  obtain ⟨d, hd⟩ : ∃ d : ℕ, analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d :=
    ENat.ne_top_iff_exists.1 (fun h => hord (analyticOrderAt_eq_top.1 h)) |>.imp fun _ h => h.symm
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · have := (analyticOrderAt_eq_zero.1 (by exact_mod_cast hd)).resolve_left (not_not.2 hfa')
      exact absurd hf0 this
    · exact h
  set ι : holGerms (0 : Fin k → ℂ) →+* holGerms (0 : (Fin k → ℂ) ×
      ℂ) := holPullback Prod.fst differentiable_fst
    (continuous_fst.tendsto' 0 0 rfl)
  set W : holGerms (0 : (Fin k → ℂ) × ℂ) := ⟨((Prod.snd : (Fin k → ℂ) × ℂ → ℂ) : Germ _ ℂ),
    coe_mem_holGerms (Eventually.of_forall fun _ => differentiableAt_snd)⟩
  set poly : (Fin d → holGerms (0 : Fin k → ℂ)) → holGerms (0 : (Fin k → ℂ) ×
      ℂ) := fun a => ∑ i, ι (a i) * W ^ (i : ℕ)
  have poly_add : ∀ a b, poly (a + b) = poly a + poly b := fun a b => by
    simp only [poly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have poly_smul : ∀ (c : holGerms (0 : Fin k → ℂ)) a, poly (c • a) = ι c * poly a := fun c a => by
    simp only [poly, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  let N : Submodule (holGerms (0 : Fin k → ℂ)) (Fin d → holGerms (0 : Fin k → ℂ)) :=
    { carrier := {a | poly a ∈ I}
      add_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq, poly_add] at *
        exact I.add_mem ha hb
      zero_mem' := by simp [poly]
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, poly_smul] at *
        exact I.mul_mem_left _ ha }
  obtain ⟨T, hT⟩ := IsNoetherian.noetherian N
  refine ⟨insert g (T.image poly), le_antisymm ?_ fun h hh => ?_⟩
  · rw [Ideal.span_le, Finset.coe_insert, Finset.coe_image, Set.insert_subset_iff]
    refine ⟨hgI, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (show t ∈ N from hT ▸ Submodule.subset_span ht)
  · obtain ⟨h₀, hh₀, hh₀d⟩ := h.2
    obtain ⟨q, a, ⟨hq, ha, heq⟩, -⟩ := MMP.Convergent.existsUnique_weierstrassDivision hd1 hfa hd
      (analyticAt_of_eventually_differentiableAt hh₀d)
    set q' : holGerms (0 : (Fin k → ℂ) × ℂ) := ⟨(q : Germ _ ℂ), coe_mem_holGerms
        (eventually_differentiableAt_of_analyticAt hq)⟩
    set a' : Fin d → holGerms (0 : Fin k → ℂ) := fun i =>
      ⟨(a i : Germ _ ℂ), coe_mem_holGerms (eventually_differentiableAt_of_analyticAt (ha i))⟩
    have hsplit : h = g * q' + poly a' := by
      apply Subtype.ext
      have e : (fun p : (Fin k → ℂ) × ℂ => f p * q p + ∑ i, a i p.1 * p.2 ^ (i : ℕ)) =
          f * q + ∑ i, (a i ∘ Prod.fst) * (Prod.snd) ^ (i : ℕ) := by
        funext p
        simp [Finset.sum_apply]
      have hc : ((f * q + ∑ i, (a i ∘ Prod.fst) * (Prod.snd) ^ (i : ℕ) :
          (Fin k → ℂ) × ℂ → ℂ) : Germ (𝓝 (0 : (Fin k → ℂ) × ℂ)) ℂ) =
          Germ.coeRingHom _ f * Germ.coeRingHom _ q +
            ∑ i, Germ.coeRingHom _ (a i ∘ Prod.fst) * Germ.coeRingHom _ Prod.snd ^ (i : ℕ) := by
        simp only [← map_mul, ← map_pow, ← map_sum, ← map_add]
        rfl
      rw [← hh₀, Germ.coe_eq.2 heq, e, hc]
      simp only [poly, Subring.coe_add, Subring.coe_mul, AddSubmonoidClass.coe_finset_sum,
        SubmonoidClass.coe_pow, ← hfg]
      rfl
    have ha'N : a' ∈ N := by
      change poly a' ∈ I
      have : poly a' = h - g * q' := by rw [hsplit]; ring
      rw [this]
      exact I.sub_mem hh (I.mul_mem_right _ hgI)
    have hpoly : ∀ x ∈ Submodule.span (holGerms (0 : Fin k → ℂ)) (T : Set (Fin d → holGerms (0 :
        Fin k → ℂ))),
        poly x ∈ Ideal.span (↑(insert g (T.image poly)) : Set (holGerms (0 : (Fin k → ℂ) ×
            ℂ))) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Ideal.subset_span (by
          simp only [Finset.coe_insert, Finset.coe_image]
          exact Or.inr ⟨x, hx, rfl⟩)
      | zero => simp [poly]
      | add x y _ _ hx hy => rw [poly_add]; exact Ideal.add_mem _ hx hy
      | smul c x _ hx => rw [poly_smul]; exact Ideal.mul_mem_left _ _ hx
    rw [hsplit]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (hpoly _ (hT ▸ ha'N))

/-- A linear coordinate change putting a given nonzero vector on the last axis. -/
private lemma exists_continuousLinearEquiv_apply_zero_eq {k : ℕ} {v : Fin (k + 1) → ℂ}
    (hv : v ≠ 0) :
    ∃ φ : ((Fin k → ℂ) × ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ), ∀ w : ℂ, φ (0, w) = w • v := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (ℂ ∙ v)
  have hrank : Module.finrank ℂ W = k := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [finrank_span_singleton hv] at this
    simp only [Module.finrank_fin_fun] at this
    omega
  let eW : (Fin k → ℂ) ≃ₗ[ℂ] W := LinearEquiv.ofFinrankEq _ _ (by simp [hrank])
  let e : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) :=
    (eW.prodCongr (LinearEquiv.toSpanNonzeroSingleton ℂ _ v hv)).trans
      (Submodule.prodEquivOfIsCompl W (ℂ ∙ v) hW.symm)
  refine ⟨e.toContinuousLinearEquiv, fun w => ?_⟩
  simp [e, Submodule.coe_prodEquivOfIsCompl']

/-- A germ that vanishes on every line through the origin is zero. -/
private lemma exists_not_eventuallyEq_zero_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} (hf : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℂ f y)
    (hne : ¬ f =ᶠ[𝓝 0] 0) : ∃ v : E, ¬ (fun t : ℂ => f (t • v)) =ᶠ[𝓝 0] 0 := by
  by_contra! h
  apply hne
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff_ball.1 hf
  filter_upwards [Metric.ball_mem_nhds _ hr] with y hy
  set L : ℂ → E := fun t => t • y
  have hL : Continuous L := by fun_prop
  set U : Set ℂ := L ⁻¹' Metric.ball 0 r
  have hU : IsOpen U := Metric.isOpen_ball.preimage hL
  have hUc : IsPreconnected U := Convex.isPreconnected
    ((convex_ball (0 : E) r).linear_preimage
      ((LinearMap.toSpanSingleton ℂ E y).restrictScalars ℝ))
  have hφ : AnalyticOnNhd ℂ (f ∘ L) U := by
    refine DifferentiableOn.analyticOnNhd (fun t ht => ?_) hU
    exact ((hall _ ht).comp t (by fun_prop : DifferentiableAt ℂ L t)).differentiableWithinAt
  have := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc
    (show (0 : ℂ) ∈ U by simpa [U, L] using hr) (h y) (show (1 : ℂ) ∈ U by simpa [U, L] using hy)
  simpa [L] using this

/-- Noetherianity, by induction on `n` through Weierstrass division. -/
private lemma isNoetherianRing_holGerms (n : ℕ) : IsNoetherianRing (holGerms (0 : Fin n → ℂ)) := by
  induction n with
  | zero =>
    have hm := maximalIdeal_eq_span_coordinates 0
    rw [Set.range_eq_empty, Ideal.span_empty] at hm
    letI := ((IsLocalRing.isField_iff_maximalIdeal_eq).2 hm).toField
    infer_instance
  | succ k ih =>
    refine (isNoetherianRing_iff_ideal_fg _).2 fun J => ?_
    by_cases hJ : J = ⊥
    · exact hJ ▸ Submodule.fg_bot
    obtain ⟨g, hgJ, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    obtain ⟨f, hfg, hf⟩ := g.2
    by_cases hf0 : f 0 ≠ 0
    · rw [Ideal.eq_top_of_isUnit_mem _ hgJ (isUnit_of_ne_zero hfg hf hf0)]
      exact ⟨{1}, by simp⟩
    push Not at hf0
    have hfne : ¬ f =ᶠ[𝓝 0] 0 := fun h => hg0 (Subtype.ext (by
      rw [← hfg]
      exact Germ.coe_eq.2 h))
    obtain ⟨v, hv⟩ := exists_not_eventuallyEq_zero_smul hf hfne
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv (Eventually.of_forall fun t => by simp [hf0])
    obtain ⟨φ, hφ⟩ := exists_continuousLinearEquiv_apply_zero_eq hv0
    set Ψ := holGermsEquiv φ
    have hφt : Tendsto φ (𝓝 0) (𝓝 0) := φ.continuous.tendsto' 0 0 (map_zero φ)
    have hfφ : ∀ᶠ y in 𝓝 (0 : (Fin k → ℂ) × ℂ), DifferentiableAt ℂ (f ∘ φ) y :=
      (hφt.eventually hf).mono fun y hy => hy.comp y φ.differentiableAt
    have hΨ : ((f ∘ φ : (Fin k → ℂ) × ℂ → ℂ) : Germ (𝓝 (0 : (Fin k → ℂ) × ℂ)) ℂ) = Ψ g := by
      change _ = (g : Germ (𝓝 (0 : Fin (k + 1) → ℂ)) ℂ).compTendsto φ hφt
      rw [← hfg]
      rfl
    have hfg' := fg_of_mem_of_not_eventuallyEq_zero
      (J.map (Ψ : holGerms (0 : Fin (k + 1) → ℂ) →+* holGerms (0 : (Fin k → ℂ) × ℂ)))
      (Ideal.mem_map_of_mem _ hgJ) hΨ hfφ (by simpa [hφ] using hv)
    have := hfg'.map (Ψ.symm : holGerms (0 : (Fin k → ℂ) × ℂ) →+* holGerms (0 : Fin (k + 1) → ℂ))
    rwa [Ideal.map_map, RingEquiv.symm_comp, Ideal.map_id] at this

private lemma isDomain_holGerms (n : ℕ) : IsDomain (holGerms (0 : Fin n → ℂ)) := by
  have : Nontrivial (holGerms (0 : Fin n → ℂ)) := (evalZero n).domain_nontrivial
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} hab => ?_⟩
  obtain ⟨f, hfa, hf⟩ := a.2
  obtain ⟨g, hgb, hg⟩ := b.2
  have hfg : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), f y * g y = 0 := by
    have : ((f * g : (Fin n → ℂ) → ℂ) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = (0 : (Fin n → ℂ) → ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    exact (Germ.coe_eq.1 this).mono fun y hy => by simpa using hy
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff_ball.1 ((hf.and hg).and hfg)
  by_cases h : ∀ y ∈ Metric.ball (0 : Fin n → ℂ) r, f y = 0
  · left
    apply Subtype.ext
    rw [← hfa]
    exact Germ.coe_eq.2 (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) fun y hy => h y hy)
  · right
    push Not at h
    obtain ⟨x, hx, hfx⟩ := h
    have hgx : g =ᶠ[𝓝 x] 0 := by
      have h1 : ∀ᶠ y in 𝓝 x, f y ≠ 0 :=
        (hall x hx).1.1.continuousAt.eventually_ne hfx
      have h2 : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball (0 : Fin n → ℂ) r :=
        Metric.isOpen_ball.mem_nhds hx
      filter_upwards [h1, h2] with y hy1 hy2
      simpa [hy1] using (hall y hy2).2
    have hA : AnalyticOnNhd ℂ g (Metric.ball 0 r) := fun y hy =>
      analyticAt_of_eventually_differentiableAt
        (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy) fun z hz => (hall z hz).1.2)
    have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball _ _).isPreconnected hx hgx
    apply Subtype.ext
    rw [← hgb]
    exact Germ.coe_eq.2 (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) fun y hy => this hy)

/-- The projection killing the first `i` coordinates. -/
private def killCoords (n i : ℕ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun j => if (j : ℕ) < i then 0 else x j

private lemma differentiable_killCoords (n i : ℕ) : Differentiable ℂ (killCoords n i) := by
  rw [differentiable_pi]
  intro j
  unfold killCoords
  split_ifs <;> fun_prop

private lemma tendsto_killCoords (n i : ℕ) :
    Tendsto (killCoords n i) (𝓝 0) (𝓝 0) := by
  have := (differentiable_killCoords n i).continuous.tendsto 0
  have h0 : killCoords n i 0 = 0 := by funext j; simp [killCoords]
  rwa [h0] at this

/-- The prime of germs vanishing on the subspace where the first `i` coordinates vanish. -/
private noncomputable def coordPrime (n i : ℕ) : PrimeSpectrum (holGerms (0 : Fin n → ℂ)) :=
  haveI := isDomain_holGerms n
  ⟨RingHom.ker (holPullback (killCoords n i) (differentiable_killCoords n i)
    (tendsto_killCoords n i)), RingHom.ker_isPrime _⟩

private lemma mem_coordPrime {n i : ℕ} {g : holGerms (0 : Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (hfg : (f : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = g) :
    g ∈ (coordPrime n i).asIdeal ↔ ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), f (killCoords n i y) = 0 := by
  change holPullback _ _ _ g = 0 ↔ _
  rw [← Subtype.val_inj, coe_holPullback, ← hfg]
  exact Germ.coe_eq

private lemma coordPrime_strictMono (n : ℕ) :
    StrictMono fun i : Fin (n + 1) => coordPrime n i := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  refine lt_of_le_of_ne (fun g hg => ?_) fun h => ?_
  · obtain ⟨f, hfg, -⟩ := g.2
    rw [mem_coordPrime hfg] at hg ⊢
    have : Tendsto (killCoords n (i.succ : ℕ)) (𝓝 0) (𝓝 0) := tendsto_killCoords n _
    filter_upwards [this.eventually hg] with y hy
    have : killCoords n (i.castSucc : ℕ) (killCoords n (i.succ : ℕ) y) = killCoords n (i.succ :
        ℕ) y := by
      funext j
      simp only [killCoords]
      split_ifs with h1 h2 <;> simp_all
      omega
    rwa [this] at hy
  · set j : Fin n := ⟨i, i.2⟩
    have hmem := (mem_coordPrime (i := (i.succ : ℕ)) (coe_polyGermHom 0 (MvPolynomial.X j)).symm).2
      (Eventually.of_forall fun y => by simp [killCoords, j])
    have h' : (coordPrime n (i.castSucc : ℕ)).asIdeal = (coordPrime n (i.succ : ℕ)).asIdeal :=
      congrArg PrimeSpectrum.asIdeal h
    rw [← h', mem_coordPrime (coe_polyGermHom 0 (MvPolynomial.X j)).symm] at hmem
    have hc : Tendsto (fun t : ℂ => (Pi.single j t : Fin n → ℂ)) (𝓝 0) (𝓝 0) := by
      have := ((continuous_single (A := fun _ : Fin n => ℂ) j).tendsto (0 : ℂ))
      simpa using this
    obtain ⟨t, ht, ht0⟩ := (((hc.eventually hmem).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {t : ℂ | t ≠ 0} ∈ 𝓝[≠] 0)).exists
    exact ht0 (by simpa [killCoords, j] using ht)

/-- The germs vanishing on the subspaces `{z₀ = ⋯ = z_{i-1} = 0}`, for `i = 0, …, n`, form a strict
chain of primes of length `n`. -/
private lemma le_ringKrullDim_holGerms (n : ℕ) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (holGerms (0 : Fin n → ℂ)) :=
  Order.LTSeries.length_le_krullDim (LTSeries.mk n _ (coordPrime_strictMono n))

private lemma evalZero_polyGermHom (q : MvPolynomial (Fin n) ℂ) :
    evalZero n (polyGermHom 0 q) = MvPolynomial.eval 0 q := by
  show ((polyGermHom 0 q : Germ (𝓝 (0 : Fin n → ℂ)) ℂ)).value = _
  rw [coe_polyGermHom]
  rfl

/-- The completion at the maximal ideal is the formal power series ring: the constants of the
completion form a field of representatives and the coordinates a regular system of parameters. -/
private lemma exists_adicCompletion_ringEquiv (n : ℕ) [IsNoetherianRing (holGerms (0 : Fin n → ℂ))]
    (hdim : ringKrullDim (holGerms (0 : Fin n → ℂ)) = n) :
    ∃ e : AdicCompletion (maximalIdeal (holGerms (0 : Fin n → ℂ))) (holGerms (0 : Fin n → ℂ))
        ≃+* MvPowerSeries (Fin n) ℂ,
      ∀ q : MvPolynomial (Fin n) ℂ,
        e (algebraMap _ _ (polyGermHom 0 q)) = (q : MvPowerSeries (Fin n) ℂ) := by
  set R := holGerms (0 : Fin n → ℂ)
  set Â := AdicCompletion (maximalIdeal R) R
  have hx : MMP.Mori.IsRegularSystemOfParameters
      (fun i : Fin n ↦ polyGermHom 0 (MvPolynomial.X i)) :=
    ⟨(maximalIdeal_eq_span_coordinates n).symm, hdim⟩
  set ι : ℂ →+* Â := (algebraMap R Â).comp ((polyGermHom 0).comp MvPolynomial.C)
  set K := ι.range
  let eK : ℂ ≃+* K := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b h => ι.injective (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  have hKf : IsField K := eK.symm.toMulEquiv.isField (Field.toIsField ℂ)
  have hK : MMP.Resolution.IsFieldOfRepresentatives K := by
    refine ⟨hKf, ?_, fun y => ?_⟩
    · letI := hKf.toField
      exact RingHom.injective _
    · obtain ⟨z, rfl⟩ := residue_surjective y
      obtain ⟨w, hw⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue Â z)
      obtain ⟨r, rfl⟩ := residue_surjective w
      refine ⟨⟨ι (evalZero n r), ⟨_, rfl⟩⟩, ?_⟩
      rw [← hw, ResidueField.map_residue]
      change residue Â (algebraMap R Â (polyGermHom 0 (MvPolynomial.C (evalZero n r)))) = _
      rw [← ResidueField.map_residue (algebraMap R Â), ← ResidueField.map_residue (algebraMap R Â)]
      congr 1
      refine Ideal.Quotient.eq.2 ((mem_maximalIdeal _).2 fun hu => ?_)
      refine (isUnit_iff_evalZero_ne_zero _).1 hu ?_
      rw [map_sub, evalZero_polyGermHom]
      simp
  obtain ⟨F,
      hF⟩ := MMP.Flips.ResolutionInputs.exists_algHom_X_eq_of_isFieldOfRepresentatives hx K hK
  have hFb := MMP.Flips.ResolutionInputs.bijective_of_isFieldOfRepresentatives hx K hK F hF
  have hmap : Function.Bijective (MvPowerSeries.map (σ := Fin n) (eK : ℂ →+* K)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨MvPowerSeries.map (eK.symm : K →+* ℂ), ?_, ?_⟩ <;>
      intro g <;> ext m <;> simp [MvPowerSeries.coeff_map]
  let E : MvPowerSeries (Fin n) ℂ ≃+* Â :=
    RingEquiv.ofBijective (F.toRingHom.comp (MvPowerSeries.map (eK : ℂ →+* K))) (hFb.comp hmap)
  refine ⟨E.symm, fun q => E.symm_apply_eq.2 ?_⟩
  have := congrArg (fun φ : MvPolynomial (Fin n) ℂ →+* Â => φ q)
    (show (E : MvPowerSeries (Fin n) ℂ →+* Â).comp (MvPolynomial.coeToMvPowerSeries.ringHom) =
      (algebraMap R Â).comp (polyGermHom 0) from by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · change F (MvPowerSeries.map (eK : ℂ →+* K) (MvPolynomial.C c : MvPolynomial (Fin n) ℂ)) = ι c
      rw [MvPolynomial.coe_C, MvPowerSeries.map_C,
        MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap, AlgHom.commutes]
      rfl
    · change F (MvPowerSeries.map (eK : ℂ →+* K) (MvPolynomial.X i : MvPolynomial (Fin n) ℂ)) = _
      rw [MvPolynomial.coe_X, MvPowerSeries.map_X, hF]
      rfl)
  exact this.symm

/-- The maximal ideal is generated by the `n` coordinate germs. -/
private lemma spanFinrank_maximalIdeal_le (n : ℕ) :
    ((maximalIdeal (holGerms (0 : Fin n → ℂ))).spanFinrank : WithBot ℕ∞) ≤ n := by
  rw [maximalIdeal_eq_span_coordinates]
  have hcard : (Set.range fun i : Fin n ↦ polyGermHom 0 (MvPolynomial.X i)).ncard ≤ n := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
  exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans hcard

end MMP.Analytic.Proof_lem_mmp_convergent_germ_ring_noetherian_regular

namespace MMP.Analytic

open MMP.Analytic.Proof_lem_mmp_convergent_germ_ring_noetherian_regular in
/-- The ring `ℂ{z₁, …, zₙ}` of holomorphic germs at the origin of `ℂⁿ` is a regular local ring
of Krull dimension `n`, its maximal ideal is generated by the coordinate germs, and its
`maximalIdeal`-adic completion is `ℂ[[z₁, …, zₙ]]` via the ring isomorphism extending the
inclusion of polynomials into power series. -/
@[mmp "lem_mmp_convergent_germ_ring_noetherian_regular"]
public theorem isRegularLocalRing_holGerms (n : ℕ) :
    ∃ _ : IsRegularLocalRing (holGerms (0 : Fin n → ℂ)),
      ringKrullDim (holGerms (0 : Fin n → ℂ)) = n ∧
      maximalIdeal (holGerms (0 : Fin n → ℂ)) =
        Ideal.span (Set.range fun i : Fin n ↦ polyGermHom 0 (MvPolynomial.X i)) ∧
      ∃ e : AdicCompletion (maximalIdeal (holGerms (0 : Fin n → ℂ))) (holGerms (0 : Fin n → ℂ))
          ≃+* MvPowerSeries (Fin n) ℂ,
        ∀ q : MvPolynomial (Fin n) ℂ,
          e (algebraMap _ _ (polyGermHom 0 q)) = (q : MvPowerSeries (Fin n) ℂ) := by
  haveI := isLocalRing_holGerms n
  haveI := isNoetherianRing_holGerms n
  have hspan := spanFinrank_maximalIdeal_le n
  have hdim : ringKrullDim (holGerms (0 : Fin n → ℂ)) = n :=
    le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hspan)
      (le_ringKrullDim_holGerms n)
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hdim ▸ hspan), hdim,
    maximalIdeal_eq_span_coordinates n,
    exists_adicCompletion_ringEquiv n hdim⟩

end MMP.Analytic

end

/-!
# Quasi-finite birational morphisms to normal varieties

Let `u : V ⟶ X` be a morphism of varieties over a field `k` with `X` normal. If `u` is locally
quasi-finite and birational, then `u` is an open immersion; if moreover `u` is finite, then `u`
is an isomorphism. This is a consequence of Zariski's main theorem: the relative normalization
of `X` in `V` is `X` itself, because `X` is normal and `u` is birational.

## Main results

* `MMP.Mori.isOpenImmersion_and_isIso_of_locallyQuasiFinite_of_isBirationalMorphism`
-/

section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Analytic.Proof_lem_mmp_fa15_quasifinite_birational_open

open MMP.Mori

/-- An integrally closed domain `A` is integrally closed in an `A`-algebra `B` that embeds into
the fraction field of `A`, compatibly with `A`. -/
private theorem bijective_algebraMap_integralClosure {A B K L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Algebra A B] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing L] (ψ : K →+* L) (hψ : Function.Bijective ψ) (φ : B →+* L)
    (hφ : Function.Injective φ) (h : ∀ a, φ (algebraMap A B a) = ψ (algebraMap A K a)) :
    Function.Bijective (algebraMap A (integralClosure A B)) := by
  have hAB : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply IsFractionRing.injective A K
    apply hψ.1
    rw [← h, ← h, hab]
  refine ⟨fun a b hab ↦ hAB (congrArg Subtype.val hab), fun x ↦ ?_⟩
  obtain ⟨p, hp, hpx⟩ := x.2
  obtain ⟨c, hc⟩ := hψ.2 (φ x.1)
  have hcomp : φ.comp (algebraMap A B) = ψ.comp (algebraMap A K) := RingHom.ext h
  have hint : IsIntegral A c := by
    refine ⟨p, hp, hψ.1 ?_⟩
    rw [map_zero, Polynomial.hom_eval₂, ← hcomp, hc, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, Subtype.ext (hφ ?_)⟩
  change φ (algebraMap A B a) = φ x.1
  rw [h, ha, hc]

/-- The extension of function fields of a dominant morphism of integral schemes is compatible
with the pull-back of sections over an open. -/
private theorem germ_app_eq_functionFieldMap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) [Nonempty U] (hη : genericPoint Y ∈ f ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hη).hom (f.app U a) =
      functionFieldMap f (X.germToFunctionField U a) := by
  have key : X.germToFunctionField U ≫ (X.presheaf.stalkCongr
      (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom ≫
      f.stalkMap (genericPoint Y) = f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hη := by
    rw [Scheme.germToFunctionField, TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rw [Scheme.Hom.germ_stalkMap]
  exact congr($(key.symm).hom a)

/-- **The normalization step.** If `u : V ⟶ X` is a quasi-compact, quasi-separated dominant
morphism of integral schemes inducing an isomorphism of function fields and `X` is normal, then
`X` is its own normalization in `V`: the map `u.fromNormalization` is an isomorphism. -/
private theorem isIso_fromNormalization {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X]
    [IsNormal X] (u : V ⟶ X) [QuasiCompact u] [QuasiSeparated u] [IsDominant u]
    (hψ : Function.Bijective (functionFieldMap u)) : IsIso u.fromNormalization := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) fun x ↦ ?_
  obtain ⟨_, ⟨U, hU', rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨U, hxU, ?_⟩
  change IsIso _
  rw [isIso_morphismRestrict_iff_isIso_app _ hU', Scheme.Hom.fromNormalization_app _ hU']
  let := (u.app U).hom.toAlgebra
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hηV : genericPoint V ∈ u ⁻¹ᵁ U :=
    show u (genericPoint V) ∈ U by
      rw [map_genericPoint_of_isDominant u]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hxU⟩
  have : Nonempty (u ⁻¹ᵁ U) := ⟨⟨_, hηV⟩⟩
  have : IsIntegrallyClosed Γ(X, U) :=
    (isNormal_iff_forall_affineOpen_normal X).mp ‹_› ⟨U, hU'⟩ ‹_›
  have := functionField_isFractionRing_of_isAffineOpen X U hU'
  have hbij := bijective_algebraMap_integralClosure (A := Γ(X, U)) (B := Γ(V, u ⁻¹ᵁ U))
    (K := X.functionField) (functionFieldMap u) hψ (V.germToFunctionField (u ⁻¹ᵁ U)).hom
    (germ_injective_of_isIntegral V _ hηV) (germ_app_eq_functionFieldMap u U hηV)
  have : IsIso (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) Γ(V, u ⁻¹ᵁ U)))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  infer_instance

end MMP.Analytic.Proof_lem_mmp_fa15_quasifinite_birational_open

namespace MMP.Mori

open MMP.Analytic.Proof_lem_mmp_fa15_quasifinite_birational_open in
/-- **Quasi-finite birational morphisms to normal varieties are open immersions.** A locally
quasi-finite birational `k`-morphism `u : V ⟶ X` of `k`-varieties with `X` normal is an open
immersion, and it is an isomorphism when it is finite. -/
@[mmp "lem_mmp_fa15_quasifinite_birational_open"]
public theorem isOpenImmersion_and_isIso_of_locallyQuasiFinite_of_isBirationalMorphism
    {k : Type u} [Field k] {V X : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (hV : IsVariety k sV) (hX : IsNormalVariety k sX) (u : V ⟶ X) (hu : u ≫ sX = sV)
    [LocallyQuasiFinite u] (hb : IsBirationalMorphism u) :
    IsOpenImmersion u ∧ (IsFinite u → IsIso u) := by
  obtain ⟨hXv, hXn⟩ := hX
  subst hu
  have := hV.toLocallyOfFiniteType
  have := hV.toIsSeparated
  have := hV.toQuasiCompact
  have := hV.toIsIntegral
  have := hXv.toIsIntegral
  have : LocallyOfFiniteType u := locallyOfFiniteType_of_comp u sX
  have : IsSeparated u := IsSeparated.of_comp u sX
  have : QuasiCompact u := QuasiCompact.of_comp u sX
  have : IsDominant u := hb.isDominant
  have := isIso_fromNormalization u hb.functionFieldMap_bijective
  refine ⟨?_, fun _ ↦ ?_⟩ <;> rw [← u.toNormalization_fromNormalization] <;> infer_instance

end MMP.Mori

end

/-!
# A rational map over a proper target is a morphism in codimension one

Let `X` be a normal variety over a field `k`, let `Y` and `Z` be varieties over `k`, let
`q : Y ⟶ Z` be a proper `k`-morphism, `p : X ⟶ Z` a `k`-morphism and `φ : X ⤏ Y` a rational map
with `q ∘ φ = p`. Then `φ` is defined on an open subset of `X` whose complement has codimension
at least two. At a point of codimension one the local ring of `X` is a discrete valuation ring,
and the valuative criterion of properness for `q` extends `φ` across it.

## Main results

* `MMP.Flips.RationalMap.exists_partialMap_two_le_closedsCodimension_of_isOver`: `φ` has a
  representative `g : X.PartialMap Y` whose domain has complement of codimension at least two.

## Implementation notes

The varieties are schemes with structure morphisms `sX`, `sY`, `sZ` to `Spec k`; that `p` and
`q` are morphisms of varieties is the compatibility `p ≫ sZ = sX` and `q ≫ sZ = sY`. "Defined on
an open subset whose complement has codimension `≥ 2`" is stated literally, as the existence of a
partial map representing `φ` whose domain has such a complement. The more general
`MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver` needs only that `X` is a normal variety
and that `q` is proper.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.4.1
-/

section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips.RationalMap

/-- **A rational map over a proper target is a morphism in codimension one.** Let `X` be a normal
variety and `Y`, `Z` varieties over `k`, `p : X ⟶ Z` a `k`-morphism, `q : Y ⟶ Z` a proper
`k`-morphism and `φ : X ⤏ Y` a rational map with `q ∘ φ = p`. Then `φ` is represented by a
partial map defined on an open subset of `X` whose complement has codimension at least two. -/
@[mmp "lem_mmp_foundation_rational_map_proper_target_codimension_one"]
public theorem exists_partialMap_two_le_closedsCodimension_of_isOver {k : Type u} [Field k]
    {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} (hX : MMP.Mori.IsNormalVariety k sX)
    (hY : MMP.Mori.IsVariety k sY) (hZ : MMP.Mori.IsVariety k sZ)
    (p : X ⟶ Z) (q : Y ⟶ Z) [IsProper q] (hp : p ≫ sZ = sX) (hq : q ≫ sZ = sY)
    (φ : X.RationalMap Y) (hφ : IsOver p q φ) :
    ∃ g : X.PartialMap Y, g.toRationalMap = φ ∧
      2 ≤ MMP.Mori.closedsCodimension g.domain.compl := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsSeparated sY := hY.toIsSeparated
  have : Y.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sY]; infer_instance⟩
  exact ⟨φ.toPartialMap, φ.toRationalMap_toPartialMap,
    MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX p q φ hφ⟩

end MMP.Flips.RationalMap

end

/-!
# The relative Leray spectral sequence of a sheaf of modules and its bottom-row edge

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces and `ℱ` an `𝒪_X`-module. Write
`K = R f_*(ℱ[0])` in the bounded below derived category of `𝒪_Y`-modules. The canonical
truncation tower of `K`, pushed forward by `R g_*` and read through cohomology, is a spectral
object (`Stacks.Cohomology.LerayTruncation.cohomologySpectralObjectFunctor`), and its spectral
sequence `E` is a spectral sequence of `𝒪_Z`-modules with second page
`E₂^{p,q} ≅ Rᵖ g_*(R^q f_* ℱ)` (`Stacks.Cohomology.LerayCard.pageTwoNatIsoDerived`).
This file states that it is a first-quadrant spectral sequence converging to
`R^{p+q}(g ∘ f)_* ℱ` through a finite filtration `F^• Rⁿ(g ∘ f)_* ℱ` with `F⁰ = Rⁿ(g ∘ f)_* ℱ` and
`F^{n+1} = 0`, the abutment being read through the composition isomorphism
`R f_* ⋙ R g_* ≅ R (g ∘ f)_*`
(`Stacks.Cohomology.DerivedDirectImageComposition.higherDirectImagesCompIso`), and that its
bottom-row edge

`Rᵖ g_*(f_* ℱ) ≅ E₂^{p,0} ↠ E_∞^{p,0} ≅ Fᵖ Rᵖ(g ∘ f)_* ℱ ⊆ Rᵖ(g ∘ f)_* ℱ`

is the natural map: `Rᵖ g_*` of the unit `(f_* ℱ)[0] ⟶ R f_*(ℱ[0])` of the right derived
functor of `f_*`, followed by the composition isomorphism, in degree `p`.

## Main results

* `MMP.RelativeLeray.exists_abutment_spectralSequence_edge`: convergence, first quadrant, and
  the identification of the bottom-row edge.

## Implementation notes

Higher direct images are the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`, i.e.
`(-)[0]` followed by the bounded below right derived functor and `Hⁿ`. The degree-zero direct
image `R⁰ f_* ℱ` is identified with `f_* ℱ` by `Stacks.RightDerivedPlus.rightDerivedPlusZeroIso`.
Convergence is spelled as an explicit finite filtration indexed by `ℕ`, so that the edge can be
stated against the same filtration.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

section

universe u w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComposableArrows
open RingedSpaceModuleAdjunction Stacks.Cohomology
open Abelian.SpectralObject

namespace MMP.Analytic.Proof_thm_mmp_module_relative_leray_with_edge

@[expose] public noncomputable section

attribute [local instance] HasDerivedCategory.standard

-- The locally small models of `Stacks.SmallDerivedModel` take precedence over the standard model,
-- as they did while they were global Stacks instances.
open scoped Stacks.SmallDerivedModel

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  DerivedPushforwardSections.modulePushforward_additive
  LerayTruncation.commShiftRightDerivedFunctorPlus
  LerayTruncation.isTriangulatedRightDerivedFunctorPlus

section SpectralEdge

variable {C : Type*} [Category C] [Abelian C] (X : Abelian.SpectralObject C EInt)
  [X.IsFirstQuadrant]

private lemma isZero_bot (p q r : ℤ) (hq : q = 0) (hr : 2 ≤ r) :
    IsZero ((X.H (p + q + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q - r + 2 : ℤ) : EInt))))) :=
  X.isZero₁_of_isFirstQuadrant _ _ _ (WithBotTop.coe_le_coe.2 (by lia)) _

private noncomputable def edgeΨ (p q r : ℤ) (hq : q = 0) (hr : 2 ≤ r) :
    ((X.spectralSequence coreE₂Cohomological).page r hr).X (p, q) ⟶ X.EFull p q :=
  (X.spectralSequencePageXIso coreE₂Cohomological r hr (p, q)
      ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
      (by simp only [coreE₂Cohomological_deg])).hom ≫
    (X.isoMapFourδ₁Toδ₀' ⊥ ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
        ((q + r - 1 : ℤ) : EInt) bot_le
        (WithBotTop.coe_le_coe.2 (show q - r + 2 ≤ q by lia))
        (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia))
        (WithBotTop.coe_le_coe.2 (show q + 1 ≤ q + r - 1 by lia))
        (p + q - 1) (p + q) (p + q + 1) (isZero_bot X p q r hq hr)).inv ≫
    X.mapFourδ₄Toδ₃' ⊥ (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt) ⊤
      bot_le (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia))
      (WithBotTop.coe_le_coe.2 (show q + 1 ≤ q + r - 1 by lia)) le_top
      (p + q - 1) (p + q) (p + q + 1)

private lemma edgeΨ_eq_pageXIsoEFull (p q : ℤ) (hp : 0 ≤ p) (hq : q = 0) h₁ h₂ :
    edgeΨ X p q (p + q + 2) hq (by lia) = (X.pageXIsoEFull p q (p + q + 2) (by lia) h₁ h₂).hom :=
  rfl

/-- The page-to-page isomorphism `E_r^{p,q}`-homology `≅ E_{r+1}^{p,q}` of the spectral sequence
of `X`, written through the homology data of the page `r` at `(p, q)` and the identification of
`E_{r+1}^{p,q}` with `E^{p+q}(q - r + 1 ≤ q ≤ q + 1 ≤ q + r)`. -/
private def StepIso (p q r : ℤ) (hr : 2 ≤ r) : Prop :=
  ∀ (hprev : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).prev (p, q) = (p - r, q + r - 1))
      (hnext : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).next (p, q) = (p + r, q + 1 - r)),
      (X.spectralSequence coreE₂Cohomological).iso r (r + 1) (p, q) rfl hr =
      ((X.spectralSequence coreE₂Cohomological).page r hr).homologyIsoSc' _ (p, q) _ hprev hnext ≪≫
      (X.spectralSequenceHomologyData coreE₂Cohomological r (r + 1) rfl hr _ (p, q) _ hprev hnext
        ((q - (r + 1) + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
        ((q + r - 1 : ℤ) : EInt) ((q + (r + 1) - 1 : ℤ) : EInt)
        rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
        (by simp only [coreE₂Cohomological_deg]) (sub_add_cancel _ _) rfl).left.homologyIso ≪≫
      (X.spectralSequencePageXIso coreE₂Cohomological (r + 1) (by lia) (p, q)
          ((q - (r + 1) + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
          ((q + (r + 1) - 1 : ℤ) : EInt)
          rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
          (by simp only [coreE₂Cohomological_deg])).symm

omit [X.IsFirstQuadrant] in
private theorem stepIso (p q r : ℤ) (hr : 2 ≤ r) : StepIso X p q r hr := by
  intro hprev hnext
  exact MMP.Homology.spectralSequence_iso_eq X coreE₂Cohomological r (r + 1) rfl hr (by lia) _ (p,
      q) _
    hprev hnext
    _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
    (by simp only [coreE₂Cohomological_deg]) (sub_add_cancel _ _) rfl

omit [X.IsFirstQuadrant] in
private lemma step (p q r : ℤ) (hr : 2 ≤ r)
    [(X.spectralSequence coreE₂Cohomological).HasEdgeEpiAt (p, q) r]
    (H : StepIso X p q r hr) :
    (X.spectralSequence coreE₂Cohomological).edgeEpiStep (p, q) r (r + 1) ≫
        (X.spectralSequencePageXIso coreE₂Cohomological (r + 1) (by lia) (p, q)
          ((q - (r + 1) + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
          ((q + (r + 1) - 1 : ℤ) : EInt)
          rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
          (by simp only [coreE₂Cohomological_deg])).hom ≫
        X.mapFourδ₁Toδ₀' ((q - (r + 1) + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt)
          ((q + 1 : ℤ) : EInt) ((q + (r + 1) - 1 : ℤ) : EInt)
          (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
          (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
          (p + q - 1) (p + q) (p + q + 1) =
      (X.spectralSequencePageXIso coreE₂Cohomological r hr (p, q)
          ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
          rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
          (by simp only [coreE₂Cohomological_deg])).hom ≫
        X.mapFourδ₄Toδ₃' ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
          ((q + r - 1 : ℤ) : EInt) ((q + (r + 1) - 1 : ℤ) : EInt)
          (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
          (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
          (p + q - 1) (p + q) (p + q + 1) := by
  have hprev : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).prev (p, q) = (p - r, q + r - 1) :=
    ComplexShape.prev_eq' _ (by
      show ((p - r, q + r - 1) : ℤ × ℤ) + (r, 1 - r) = (p, q)
      ext <;> simp)
  have hnext : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).next (p, q) = (p + r, q + 1 - r) :=
    ComplexShape.next_eq' _ (by
      show ((p, q) : ℤ × ℤ) + (r, 1 - r) = (p + r, q + 1 - r)
      ext <;> simp
      lia)
  have hrl := X.spectralSequenceHomologyData_right_homologyIso_eq_left_homologyIso
    coreE₂Cohomological r (r + 1) rfl hr _ (p, q) _
    hprev hnext ((q - (r + 1) + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) :
        EInt) ((q + r - 1 : ℤ) : EInt) ((q + (r + 1) - 1 :
            ℤ) : EInt) rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
    (by simp only [coreE₂Cohomological_deg]) (sub_add_cancel _ _) rfl
  have hι := X.spectralSequenceHomologyData_right_ι
    coreE₂Cohomological r (r + 1) rfl hr _ (p, q) _
    hprev hnext ((q - (r + 1) + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) :
        EInt) ((q + r - 1 : ℤ) : EInt) ((q + (r + 1) - 1 :
            ℤ) : EInt) rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
    (by simp only [coreE₂Cohomological_deg]) (sub_add_cancel _ _) rfl
  have hp := X.spectralSequenceHomologyData_right_p
    coreE₂Cohomological r (r + 1) rfl hr _ (p, q) _
    hprev hnext ((q - (r + 1) + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) :
        EInt) ((q + r - 1 : ℤ) : EInt) ((q + (r + 1) - 1 :
            ℤ) : EInt) rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
    (by simp only [coreE₂Cohomological_deg]) (sub_add_cancel _ _) rfl
  have hiso := H hprev hnext
  have hS := (X.spectralSequence coreE₂Cohomological).rightHomologyData_ι_edgeEpiStep_compatibility
    r (r + 1) _ (p, q) _ hprev hnext (hr := hr)
    (X.spectralSequenceHomologyData coreE₂Cohomological r (r + 1) rfl hr _ (p, q) _ hprev hnext
      ((q - (r + 1) + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q
          + r - 1 : ℤ) : EInt) ((q + (r +
              1) - 1 : ℤ) : EInt) rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
      (by simp only [coreE₂Cohomological_deg]) (sub_add_cancel _ _) rfl).right (hrr' := rfl)
  rw [hiso, hrl, hι, hp] at hS
  erw [Iso.trans_inv, Iso.trans_inv, Iso.symm_inv] at hS
  simp only [Category.assoc] at hS
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc] at hS
  exact hS

omit [X.IsFirstQuadrant] in
private lemma key {W : C} (j₀' j₀ j₁ j₂ j₃ j₃' : EInt) (h₀' : j₀' ≤ j₀) (h₀ : j₀ ≤ j₁) (h₁ : j₁ ≤
    j₂)
    (h₂ : j₂ ≤ j₃) (h₃ : j₃ ≤ j₃') (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (z : IsZero ((X.H n₂).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ j₀)))))
    (z' : IsZero ((X.H n₂).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ j₀')))))
    (x : W ⟶ X.E (homOfLE (h₀'.trans h₀)) (homOfLE h₁) (homOfLE (h₂.trans h₃)) n₀ n₁ n₂ hn₁ hn₂)
    (y : W ⟶ X.E (homOfLE h₀) (homOfLE h₁) (homOfLE h₂) n₀ n₁ n₂ hn₁ hn₂)
    (hxy : x ≫ X.mapFourδ₁Toδ₀' j₀' j₀ j₁ j₂ j₃' h₀' h₀ h₁ (h₂.trans h₃) n₀ n₁ n₂ hn₁ hn₂ =
      y ≫ X.mapFourδ₄Toδ₃' j₀ j₁ j₂ j₃ j₃' h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn₁ hn₂) :
    x ≫ (X.isoMapFourδ₁Toδ₀' ⊥ j₀' j₁ j₂ j₃' bot_le (h₀'.trans h₀) h₁ (h₂.trans h₃)
        n₀ n₁ n₂ z' hn₁ hn₂).inv ≫
      X.mapFourδ₄Toδ₃' ⊥ j₁ j₂ j₃' ⊤ bot_le h₁ (h₂.trans h₃) le_top n₀ n₁ n₂ hn₁ hn₂ =
    y ≫ (X.isoMapFourδ₁Toδ₀' ⊥ j₀ j₁ j₂ j₃ bot_le h₀ h₁ h₂ n₀ n₁ n₂ z hn₁ hn₂).inv ≫
      X.mapFourδ₄Toδ₃' ⊥ j₁ j₂ j₃ ⊤ bot_le h₁ h₂ le_top n₀ n₁ n₂ hn₁ hn₂ := by
  have hc : (X.isoMapFourδ₁Toδ₀' ⊥ j₀ j₁ j₂ j₃ bot_le h₀ h₁ h₂ n₀ n₁ n₂ z hn₁ hn₂).inv ≫
      X.mapFourδ₄Toδ₃' ⊥ j₁ j₂ j₃ j₃' bot_le h₁ h₂ h₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.mapFourδ₄Toδ₃' j₀ j₁ j₂ j₃ j₃' h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X.isoMapFourδ₁Toδ₀' ⊥ j₀ j₁ j₂ j₃' bot_le h₀ h₁ (h₂.trans h₃) n₀ n₁ n₂ z hn₁ hn₂).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [isoMapFourδ₁Toδ₀'_hom]
    exact (X.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' ⊥ j₀ j₁ j₂ j₃ j₃' bot_le h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn₁
        hn₂).symm
  have hd : X.mapFourδ₁Toδ₀' j₀' j₀ j₁ j₂ j₃' h₀' h₀ h₁ (h₂.trans h₃) n₀ n₁ n₂ hn₁ hn₂ ≫
      (X.isoMapFourδ₁Toδ₀' ⊥ j₀ j₁ j₂ j₃' bot_le h₀ h₁ (h₂.trans h₃) n₀ n₁ n₂ z hn₁ hn₂).inv =
      (X.isoMapFourδ₁Toδ₀' ⊥ j₀' j₁ j₂ j₃' bot_le (h₀'.trans h₀) h₁ (h₂.trans h₃)
        n₀ n₁ n₂ z' hn₁ hn₂).inv := by
    rw [Iso.comp_inv_eq, Iso.eq_inv_comp]
    simp only [isoMapFourδ₁Toδ₀'_hom]
    exact X.mapFourδ₁Toδ₀'_comp ⊥ j₀' j₀ j₁ j₂ j₃' bot_le h₀' h₀ h₁ (h₂.trans h₃)
      n₀ n₁ n₂ hn₁ hn₂
  rw [← X.mapFourδ₄Toδ₃'_comp ⊥ j₁ j₂ j₃ j₃' ⊤ bot_le h₁ h₂ h₃ le_top n₀ n₁ n₂ hn₁ hn₂,
    reassoc_of% hc, ← reassoc_of% hxy, reassoc_of% hd]

private lemma edgeEpiStep_edgeΨ (p q r r' : ℤ) (hq : q = 0) (hr : 2 ≤ r) (hrr' : r + 1 = r')
    [(X.spectralSequence coreE₂Cohomological).HasEdgeEpiAt (p, q) r] :
    (X.spectralSequence coreE₂Cohomological).edgeEpiStep (p, q) r r' hrr' ≫
        edgeΨ X p q r' hq (by lia) = edgeΨ X p q r hq hr := by
  subst hrr'
  have hs := step X p q r hr (stepIso X p q r hr)
  have hk := key X (((q - (r + 1) + 2 : ℤ)) : EInt) (((q - r + 2 : ℤ)) : EInt) (q : EInt)
    (((q + 1 : ℤ)) : EInt) (((q + r - 1 : ℤ)) : EInt) (((q + (r + 1) - 1 : ℤ)) : EInt)
    (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
    (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
    (WithBotTop.coe_le_coe.2 (by lia)) (p + q - 1) (p + q) (p + q + 1) (by lia) (by lia)
    (isZero_bot X p q r hq hr) (isZero_bot X p q (r + 1) hq (by lia)) _ _ ((Category.assoc _ _
        _).trans hs)
  simp only [edgeΨ]
  exact (Category.assoc _ _ _).symm.trans hk

private lemma hom_eq {n : ℕ} {D D' : ComposableArrows EInt n} (a b : D ⟶ D') : a = b := by
  ext; exact Subsingleton.elim _ _

private lemma pageXIsoOfEq_edgeΨ (p q r r' : ℤ) (hq : q = 0) (hr : 2 ≤ r) (h : r = r') :
    ((X.spectralSequence coreE₂Cohomological).pageXIsoOfEq (p, q) r r' h hr).hom ≫
      edgeΨ X p q r' hq (by lia) = edgeΨ X p q r hq hr := by
  subst h
  simp [SpectralSequence.pageXIsoOfEq]

private lemma edgeEpiSteps_edgeΨ (p q r : ℤ) (hq : q = 0) (hr : 2 ≤ r)
    [(X.spectralSequence coreE₂Cohomological).HasPageInfinityAt (p, q)]
    [(X.spectralSequence coreE₂Cohomological).HasEdgeEpiAtFrom (p, q) 2] :
    (X.spectralSequence coreE₂Cohomological).edgeEpiSteps (p, q) 2 r hr ≫
      edgeΨ X p q r hq hr = edgeΨ X p q 2 hq le_rfl := by
  obtain ⟨k, rfl⟩ := Int.le.dest hr
  rw [SpectralSequence.edgeEpiSteps_eq_edgeEpiSteps']
  induction k with
  | zero =>
    rw [SpectralSequence.edgeEpiSteps'_zero, Iso.inv_comp_eq, pageXIsoOfEq_edgeΨ]
  | succ k ih =>
    rw [SpectralSequence.edgeEpiSteps'_succ, Category.assoc, edgeEpiStep_edgeΨ X p q _ _ hq (by
        lia),
      ← ih (by lia)]

private lemma base (p q : ℤ) (hq : q = 0) :
    (X.H (p + q)).map (twoδ₁Toδ₀' (⊥ : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) bot_le
        (WithBotTop.coe_le_coe.2 (by lia))) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) (q : EInt) ((q + 1 : ℤ) : EInt)
        rfl rfl (p + q) rfl).inv ≫ edgeΨ X p q 2 hq le_rfl =
    X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (p + q) ≫
      X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ (q : EInt)))
        (homOfLE (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt))) rfl (p + q - 1) (p + q) (p + q +
            1) := by
  subst hq
  rw [X.spectralSequenceFirstPageXIso_inv coreE₂Cohomological (p, 0) ((0 : ℤ) : EInt)
    ((0 + 1 : ℤ) : EInt) rfl rfl (p + 0 - 1) (p + 0) (p + 0 + 1) rfl]
  simp only [edgeΨ, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  have h01 : ((0 : ℤ) : EInt) ≤ ((0 + 1 : ℤ) : EInt) := WithBotTop.coe_le_coe.2 (by lia)
  change _ ≫ _ ≫ (X.isoMapFourδ₁Toδ₀' ⊥ ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) ((0 + 1 : ℤ) : EInt)
    ((0 + 1 : ℤ) : EInt) bot_le le_rfl h01 le_rfl (p + 0 - 1) (p + 0) (p + 0 + 1) _ _ _).inv ≫
    X.mapFourδ₄Toδ₃' ⊥ ((0 : ℤ) : EInt) ((0 + 1 : ℤ) : EInt) ((0 + 1 : ℤ) : EInt) ⊤
      bot_le h01 le_rfl le_top (p + 0 - 1) (p + 0) (p + 0 + 1) _ _ = _
  have hb0 : (⊥ : EInt) ≤ ((0 : ℤ) : EInt) := bot_le
  have hb1 : (⊥ : EInt) ≤ ((0 + 1 : ℤ) : EInt) := bot_le
  have e1 : (X.EIsoH (homOfLE h01) (p + 0 - 1) (p + 0) (p + 0 + 1)).inv =
      X.toCycles (𝟙 _) (homOfLE h01) (homOfLE h01) (by simp) (p + 0) ≫
        X.πE (𝟙 _) (homOfLE h01) (𝟙 _) (p + 0 - 1) (p + 0) (p + 0 + 1) := by
    rw [← X.cyclesIsoH_hom_EIsoH_inv (p + 0 - 1) (p + 0) (p + 0 + 1) (by lia) rfl (homOfLE h01),
      ← X.cyclesIsoH_inv (homOfLE h01) (p + 0) (p + 0 + 1) rfl, Iso.inv_hom_id_assoc]
  have e2 : (X.H (p + 0)).map (twoδ₁Toδ₀' (⊥ : EInt) ((0 : ℤ) : EInt) ((0 + 1 : ℤ) : EInt) hb0
      h01) ≫
      X.toCycles (𝟙 _) (homOfLE h01) (homOfLE h01) (by simp) (p + 0) =
      X.toCycles (homOfLE hb0) (homOfLE h01) (homOfLE hb1) rfl (p + 0) ≫
        X.cyclesMap (homOfLE hb0) (homOfLE h01) (𝟙 _) (homOfLE h01)
          (homMk₂ (homOfLE hb0) (𝟙 _) (𝟙 _) (Subsingleton.elim _ _) (Subsingleton.elim _ _))
          (p + 0) :=
    (X.toCycles_cyclesMap _ _ _ _ _ _ _ _ _ _ (p + 0) (Subsingleton.elim _ _)
      (Subsingleton.elim _ _)).symm
  have e3 : X.cyclesMap (homOfLE hb0) (homOfLE h01) (𝟙 _) (homOfLE h01)
          (homMk₂ (homOfLE hb0) (𝟙 _) (𝟙 _) (Subsingleton.elim _ _) (Subsingleton.elim _ _))
          (p + 0) ≫ X.πE (𝟙 _) (homOfLE h01) (𝟙 _) (p + 0 - 1) (p + 0) (p + 0 + 1) =
      X.πE (homOfLE hb0) (homOfLE h01) (𝟙 _) (p + 0 - 1) (p + 0) (p + 0 + 1) ≫
        X.mapFourδ₁Toδ₀' ⊥ ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) ((0 + 1 : ℤ) : EInt)
          ((0 + 1 : ℤ) : EInt) bot_le le_rfl h01 le_rfl (p + 0 - 1) (p + 0) (p + 0 + 1) :=
    (X.πE_map _ _ _ _ _ _ _ _ (p + 0 - 1) (p + 0) (p + 0 + 1) (hom_eq _ _)).symm
  have e4 : X.πE (homOfLE hb0) (homOfLE h01) (𝟙 _) (p + 0 - 1) (p + 0) (p + 0 + 1) ≫
      X.mapFourδ₄Toδ₃' ⊥ ((0 : ℤ) : EInt) ((0 + 1 : ℤ) : EInt) ((0 + 1 : ℤ) : EInt) ⊤
        bot_le h01 le_rfl le_top (p + 0 - 1) (p + 0) (p + 0 + 1) =
      X.πE (homOfLE hb0) (homOfLE h01) (homOfLE (le_top : ((0 + 1 : ℤ) : EInt) ≤ ⊤))
        (p + 0 - 1) (p + 0) (p + 0 + 1) :=
    (X.πE_map _ _ _ _ _ _ _ (𝟙 _) (p + 0 - 1) (p + 0) (p + 0 + 1) (hom_eq _ _)).trans
      (by rw [cyclesMap_id, Category.id_comp])
  rw [X.p_opcyclesToE _ _ _ _ _ (p + 0 - 1) (p + 0) (p + 0 + 1), e1,
    Category.assoc, reassoc_of% e2,
    reassoc_of% e3]
  simp only [isoMapFourδ₁Toδ₀'_hom_inv_id_assoc]
  rw [e4]

private lemma edge_formula (p q : ℤ) (hp : 0 ≤ p) (hq : q = 0)
    [(X.spectralSequence coreE₂Cohomological).HasEdgeEpiAtFrom (p, q) 2]
    [(X.spectralSequence coreE₂Cohomological).HasEdgeMonoAtFrom (p, q) (p + q + 2)]
    [(X.spectralSequence coreE₂Cohomological).HasEdgeEpiAtFrom (p, q) (p + q + 2)] (h₁ h₂) :
    (X.H (p + q)).map (twoδ₁Toδ₀' (⊥ : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) bot_le
        (WithBotTop.coe_le_coe.2 (by lia))) ≫
      (X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) (q : EInt) ((q + 1 : ℤ) : EInt)
        rfl rfl (p + q) rfl).inv ≫
      (X.spectralSequence coreE₂Cohomological).edgeEpi (p, q) 2 ≫
      ((X.spectralSequence coreE₂Cohomological).pageInfinityIso (p, q) (p + q + 2)).hom ≫
      (X.pageXIsoEFull p q (p + q + 2) (by lia) h₁ h₂).hom =
    X.pOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (p + q) ≫
      X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ (q : EInt)))
        (homOfLE (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt))) rfl (p + q - 1) (p + q) (p + q +
            1) := by
  rw [← (X.spectralSequence coreE₂Cohomological).edgeEpiSteps_pageInfinityIso_inv' (p, q) 2
    (p + q + 2) (by lia), Category.assoc, Iso.inv_hom_id_assoc,
    ← edgeΨ_eq_pageXIsoEFull X p q hp hq, edgeEpiSteps_edgeΨ X p q _ hq, base X p q hq]

omit [X.IsFirstQuadrant] in
private lemma π_cokernelIsoCokernelOfLE_hom {U V T O Y : C} (a : U ⟶ T) (b : V ⟶ T)
    (h : imageSubobject a ≤ imageSubobject b)
    (e : V ⟶ O) [Epi e] (m : O ⟶ T) [Mono m] (he : e ≫ m = b)
    (f : U ⟶ O) (hf : f ≫ m = a)
    (φ : cokernel (Subobject.ofLE (imageSubobject a) (imageSubobject b) h) ⟶ Y) (ψ : T ⟶ Y)
    (hφ : cokernel.π _ ≫ φ = (imageSubobject b).arrow ≫ ψ) :
    cokernel.π f ≫ (cokernelIsoCokernelOfLE a b h e m he f hf).hom ≫ φ = m ≫ ψ := by
  have := strongEpi_of_epi e
  simp [cokernelIsoCokernelOfLE, hφ, reassoc_of% image.isoStrongEpiMono_hom_comp_ι e m he]

omit [X.IsFirstQuadrant] in
private lemma π_cokernelOfLECongr_hom {Z Y : C} {A B A' : Subobject Z} (hA : A = A')
    (h : A ≤ B) (h' : A' ≤ B) (φ : cokernel (Subobject.ofLE A' B h') ⟶ Y) :
    cokernel.π (Subobject.ofLE A B h) ≫ (cokernelOfLECongr hA rfl h h').hom ≫ φ =
      cokernel.π (Subobject.ofLE A' B h') ≫ φ := by
  subst hA
  simp [cokernelOfLECongr]

omit [X.IsFirstQuadrant] in
private lemma opcyclesToE_EIsoCokernelOfLE_hom {i j k l : EInt}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l) (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (f₁₂₃ : i ⟶ l) (h₁₂₃ : f₁₂ ≫ f₃ = f₁₂₃) (n : ℤ) {Y : C}
    (φ : cokernel (Subobject.ofLE
        (imageSubobject ((X.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫
          (X.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃)))
        (imageSubobject ((X.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃)))
        (imageSubobject_comp_le _ _)) ⟶ Y)
    (ψ : (X.H n).obj (mk₁ f₁₂₃) ⟶ Y)
    (hφ : cokernel.π _ ≫ φ =
      (imageSubobject ((X.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃))).arrow ≫ ψ) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ (n - 1) n (n + 1) ≫
      (X.EIsoCokernelOfLE f₁ f₂ f₃ f₁₂ h₁₂ f₁₂₃ h₁₂₃ n).hom ≫ φ =
    X.fromOpcycles f₁₂ f₃ f₁₂₃ h₁₂₃ n ≫ ψ := by
  dsimp only [EIsoCokernelOfLE]
  refine (Category.assoc _ _ _).symm.trans ?_
  show (_ ≫ _ ≫ _) ≫ φ = _
  rw [← Category.assoc, Category.assoc _ _ φ]
  have h1 := IsColimit.comp_coconePointUniqueUpToIso_hom
    (X.cokernelSequenceOpcyclesE_exact f₁ f₂ f₃ f₁₂ h₁₂ (n - 1) n (n + 1)).gIsCokernel
    (cokernelIsCokernel _) WalkingParallelPair.one
  refine (congrArg (· ≫ _) h1).trans ?_
  exact π_cokernelIsoCokernelOfLE_hom (e := X.pOpcycles f₁₂ f₃ n)
    (m := X.fromOpcycles f₁₂ f₃ f₁₂₃ h₁₂₃ n) _ _ _ _ _ _ _ _ hφ

omit [X.IsFirstQuadrant] in
private lemma opcyclesToE_EFullIsoCokernelOfLE_hom (p q : ℤ) {Y : C}
    (φ : cokernel (Subobject.ofLE (X.abutmentFiltration (p + q) (q : EInt))
      (X.abutmentFiltration (p + q) ((q + 1 : ℤ) : EInt))
      (X.abutmentFiltration_monotone (p + q)
        (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia)))) ⟶ Y)
    (ψ : X.abutment (p + q) ⟶ Y)
    (hφ : cokernel.π _ ≫ φ = (X.abutmentFiltration (p + q) ((q + 1 : ℤ) : EInt)).arrow ≫ ψ) :
    X.opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ (q : EInt)))
        (homOfLE (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt))) rfl (p + q - 1) (p + q) (p + q + 1) ≫
      (X.EFullIsoCokernelOfLE p q).hom ≫ φ =
    X.fromOpcycles (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)) rfl
        (p + q) ≫ ψ := by
  dsimp only [EFullIsoCokernelOfLE]
  show _ ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc]
  exact opcyclesToE_EIsoCokernelOfLE_hom X _ _ _ _ rfl _ rfl (p + q) _ ψ
    ((π_cokernelOfLECongr_hom _ _ _ _).trans hφ)

end SpectralEdge

section Chains

variable {C : Type*} [Category C]

private lemma chain_left {W P Q R N T T' : C} (x : P ⟶ Q) (F : W ≅ Q) (a : Q ⟶ R) (s : R ⟶ R)
    (b : R ⟶ N) (c : N ⟶ T') (d : N ⟶ T) (e : T ⟶ T') (y : P ⟶ T) (hs : s = 𝟙 _)
    (h : x ≫ a ≫ b ≫ d = y) (hc : c = d ≫ e) :
    x ≫ F.inv ≫ ((F.hom ≫ (a ≫ s)) ≫ b ≫ c) = y ≫ e := by
  subst hs hc h
  simp

private lemma chain_right' {W P Q E₁ E₁' E₁'' E₂ E₃ E₄ O T' Y₀ : C} (x : P ⟶ Q) (F : W ≅ Q)
    (e : W ⟶ E₁) (i1 : E₁ ⟶ E₁') (i2 : E₁' ⟶ E₁'') (i3 : E₁'' ⟶ E₂) (i45 : E₂ ⟶ E₃)
    (dsc : E₃ ⟶ E₄) (arr : E₄ ⟶ Y₀) (po : P ⟶ O) (ot : O ⟶ E₁'') (fo : O ⟶ T')
    (ψ : T' ⟶ Y₀) (y : P ⟶ T') (hE : x ≫ F.inv ≫ e ≫ i1 ≫ i2 = po ≫ ot)
    (h3 : ot ≫ i3 ≫ i45 ≫ dsc ≫ arr = fo ≫ ψ) (hpf : po ≫ fo = y) :
    y ≫ ψ = x ≫ F.inv ≫ ((e ≫ (i1 ≫ i2 ≫ i3 ≫ i45) ≫ dsc) ≫ arr) := by
  have : x ≫ F.inv ≫ ((e ≫ (i1 ≫ i2 ≫ i3 ≫ i45) ≫ dsc) ≫ arr) =
      (x ≫ F.inv ≫ e ≫ i1 ≫ i2) ≫ i3 ≫ i45 ≫ dsc ≫ arr := by simp only [Category.assoc]
  rw [this, hE, Category.assoc, h3, ← Category.assoc, hpf]

end Chains

section HeartExt

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

private lemma heart_ext {W W' : DerivedCategory.Plus A} [W.IsGE 0] [W.IsLE 0] [W'.IsGE 0]
    [W'.IsLE 0] (a b : W ⟶ W')
    (h : (DerivedCategory.Plus.homologyFunctor A 0).map a =
      (DerivedCategory.Plus.homologyFunctor A 0).map b) : a = b := by
  obtain ⟨A₁, ⟨e₁⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Plus.ι.obj W) 0
  obtain ⟨A₂, ⟨e₂⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Plus.ι.obj W') 0
  let E₁ : W ≅ (DerivedCategory.Plus.singleFunctor A 0).obj A₁ :=
    DerivedCategory.Plus.ι.preimageIso e₁
  let E₂ : W' ≅ (DerivedCategory.Plus.singleFunctor A 0).obj A₂ :=
    DerivedCategory.Plus.ι.preimageIso e₂
  let S := DerivedCategory.Plus.singleFunctor A 0
  let H := DerivedCategory.Plus.homologyFunctor A 0
  have key : ∀ g g' : A₁ ⟶ A₂, H.map (S.map g) = H.map (S.map g') → g = g' := by
    intro g g' hg
    have n₁ := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := A)
        0).hom.naturality g
    have n₂ := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := A)
        0).hom.naturality g'
    dsimp at n₁ n₂
    rw [← cancel_epi ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := A)
        0).hom.app A₁),
      ← n₁, ← n₂]
    exact congrArg (· ≫ _) hg
  have hc : E₁.inv ≫ a ≫ E₂.hom = E₁.inv ≫ b ≫ E₂.hom := by
    rw [← S.map_preimage (E₁.inv ≫ a ≫ E₂.hom), ← S.map_preimage (E₁.inv ≫ b ≫ E₂.hom)]
    congr 1
    apply key
    rw [S.map_preimage, S.map_preimage, H.map_comp, H.map_comp, H.map_comp, H.map_comp, h]
  simpa using hc

private lemma hom_ext_truncLT_of_H0 {K : DerivedCategory.Plus A} [K.IsGE 0]
    (a b : (DerivedCategory.Plus.TStructure.t.truncLT 1).obj K ⟶ K)
    (h : (DerivedCategory.Plus.homologyFunctor A 0).map a =
      (DerivedCategory.Plus.homologyFunctor A 0).map b) : a = b := by
  let t := DerivedCategory.Plus.TStructure.t (C := A)
  have : t.IsLE ((t.truncLT 1).obj K) 0 := t.isLE_truncLT_obj _ _ _
  have : t.IsGE ((t.truncLT 1).obj K) 0 := inferInstance
  have ha := t.liftTruncLT_ι a 0 1 (by lia)
  have hb := t.liftTruncLT_ι b 0 1 (by lia)
  rw [← ha, ← hb]
  congr 1
  have := DerivedCategory.Plus.isIso_homologyMap_truncLTι_app (C := A) 1 0 (by lia) K
  apply heart_ext
  rw [← cancel_mono ((DerivedCategory.Plus.homologyFunctor A 0).map ((t.truncLTι 1).app K)),
    ← Functor.map_comp, ← Functor.map_comp, ha, hb, h]

private lemma H_map_single (q : ℤ) {P Q : A} (x : P ⟶ Q) :
    (DerivedCategory.Plus.homologyFunctor A q).map ((DerivedCategory.Plus.singleFunctor A q).map
        x) =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso q).hom.app P ≫ x ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso q).inv.app Q := by
  have := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := A) q).hom.naturality x
  dsimp at this
  rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

private lemma H_map_truncGELTIso_gen (q : ℤ) {T : DerivedCategory.Plus A ⥤ DerivedCategory.Plus A}
    (L : DerivedCategory.Plus A ⥤ A) (e : L ⋙ DerivedCategory.Plus.singleFunctor A q ≅ T)
    (θ : T ⋙ DerivedCategory.Plus.homologyFunctor A q ≅ DerivedCategory.Plus.homologyFunctor A q)
    (K : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor A q).map (e.inv.app K) ≫
      (DerivedCategory.Plus.homologyFunctor A q).map
          ((DerivedCategory.Plus.singleFunctor A q).map (L.rightUnitor.inv.app K)) ≫
        (DerivedCategory.Plus.homologyFunctor A q).map
            ((DerivedCategory.Plus.singleFunctor A q).map
              ((L.isoWhiskerLeft
                (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso q).symm).hom.app K)) ≫
          (DerivedCategory.Plus.homologyFunctor A q).map
              ((DerivedCategory.Plus.singleFunctor A q).map
                ((L.associator (DerivedCategory.Plus.singleFunctor A q)
                  (DerivedCategory.Plus.homologyFunctor A q)).inv.app K)) ≫
            (DerivedCategory.Plus.homologyFunctor A q).map
                ((DerivedCategory.Plus.singleFunctor A q).map
                  ((DerivedCategory.Plus.homologyFunctor A q).map (e.hom.app K))) ≫
              (DerivedCategory.Plus.homologyFunctor A q).map
                ((DerivedCategory.Plus.singleFunctor A q).map (θ.hom.app K)) =
    θ.hom.app K ≫ (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso q).inv.app
        ((DerivedCategory.Plus.homologyFunctor A q).obj K) := by
  simp only [H_map_single]
  simp

private lemma H_map_truncGELTIso_hom (q : ℤ) (K : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor A q).map
      ((DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor q).hom.app K) =
    (DerivedCategory.Plus.truncGELTCompHomologyFunctorIso q).hom.app K ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso q).inv.app
        ((DerivedCategory.Plus.homologyFunctor A q).obj K) := by
  unfold DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor
  dsimp only
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp]
  exact H_map_truncGELTIso_gen q _ _ _ K

private lemma truncGEπ_truncGELTCompHomologyFunctorIso_hom (q : ℤ) (K : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor A q).map
        ((DerivedCategory.Plus.TStructure.t.truncGEπ q).app
          ((DerivedCategory.Plus.TStructure.t.truncLT (q + 1)).obj K)) ≫
      (DerivedCategory.Plus.truncGELTCompHomologyFunctorIso q).hom.app K =
    (DerivedCategory.Plus.homologyFunctor A q).map
      ((DerivedCategory.Plus.TStructure.t.truncLTι (q + 1)).app K) := by
  simp [DerivedCategory.Plus.truncGELTCompHomologyFunctorIso,
    DerivedCategory.Plus.truncGECompHomologyFunctorIso,
    DerivedCategory.Plus.truncLTCompHomologyFunctorIso]

omit [HasDerivedCategory A] in
private lemma π_congr_mapIso_desc_arrow {Z₀ Z' : A} (n : Z₀ ⟶ Z') [Mono n]
    {P Q P' Q' : Subobject Z₀} (hP : P = P') (hQ : Q = Q') (h : P ≤ Q) (h' : P' ≤ Q')
    (w : Subobject.ofLE ((Subobject.map n).obj P') ((Subobject.map n).obj Q')
      ((Subobject.map n).monotone h') ≫ 𝟙 _ = 0) :
    cokernel.π (Subobject.ofLE P Q h) ≫
      (Abelian.SpectralObject.cokernelOfLECongr hP hQ h h').hom ≫
      (Abelian.Subobject.cokernelOfLEMapIso n h').symm.hom ≫
      cokernel.desc _ (𝟙 _) w ≫ ((Subobject.map n).obj Q').arrow = Q.arrow ≫ n := by
  subst hP hQ
  have e : cokernel.π (Subobject.ofLE P Q h) ≫ (Abelian.Subobject.cokernelOfLEMapIso n h').inv =
      (Subobject.mapObjIso n Q).inv ≫ cokernel.π _ := by
    rw [Iso.comp_inv_eq, Category.assoc, Abelian.Subobject.π_cokernelOfLEMapIso_hom,
      Iso.inv_hom_id_assoc]
  simp only [Abelian.SpectralObject.cokernelOfLECongr, Iso.refl_hom, Category.id_comp,
    Iso.symm_hom]
  rw [reassoc_of% e, cokernel.π_desc_assoc, Category.id_comp, Subobject.mapObjIso_inv_arrow]

end HeartExt

section

variable {X Y Z : RingedSpace.{w, w}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : ModuleSheaves X)

/-- `R f_*(ℱ[0])`. -/
private abbrev derivedPushforward : DerivedCategory.Plus (ModuleSheaves Y) :=
  (modulePushforward f).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M)

/-- The cohomology spectral object of the truncation tower of `R f_*(ℱ[0])` under `R g_*`. -/
private abbrev spectralObj : Abelian.SpectralObject (ModuleSheaves Z) EInt :=
  (LerayTruncation.cohomologySpectralObjectFunctor
    (modulePushforward g).rightDerivedFunctorPlus).obj (derivedPushforward f M)

private theorem isGE_derivedPushforward :
    DerivedCategory.Plus.IsGE (derivedPushforward f M) 0 :=
  Functor.isGE_rightDerivedFunctorPlus_obj (modulePushforward f) _ 0

private theorem coe_add_one_le_of_lt {n : ℤ} {i : EInt} (h : (n : EInt) < i) :
    ((n + 1 : ℤ) : EInt) ≤ i := by
  induction i using WithBotTop.rec with
  | bot => exact absurd h (not_lt_bot)
  | top => exact le_top
  | coe k =>
    rw [WithBotTop.coe_lt_coe] at h
    exact WithBotTop.coe_le_coe.2 (by lia)

/-- The truncation spectral object of `R f_*(ℱ[0])` under `R g_*` is first-quadrant. -/
private theorem isFirstQuadrant_spectralObj : (spectralObj f g M).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    have := isGE_derivedPushforward f M
    change IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) n).obj
      ((modulePushforward g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj (derivedPushforward f M)))))
    exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
      (DerivedCategory.Plus.TStructure.t.isZero_eTruncLT_obj_obj _ 0 j hj)))
  isZero₂ i j hij n hi := by
    change IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) n).obj
      ((modulePushforward g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj (derivedPushforward f M)))))
    have h₁ : DerivedCategory.Plus.IsGE
        ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
          ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj (derivedPushforward f M)))
          (n + 1) :=
      DerivedCategory.Plus.TStructure.t.isGE_eTruncGE_obj_obj (n + 1) i
        (coe_add_one_le_of_lt hi) _
    have := Functor.isGE_rightDerivedFunctorPlus_obj (modulePushforward g)
      ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
          ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj (derivedPushforward f M)))
      (n + 1)
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ (n + 1) n (by lia)

attribute [local instance] isFirstQuadrant_spectralObj

private theorem isZero_page_two (p q : ℤ) (hpq : p < 0 ∨ q < 0) :
    IsZero ((((spectralObj f g M).spectralSequence
      Abelian.SpectralObject.coreE₂Cohomological).page 2).X (p, q)) := by
  refine IsZero.of_iso ?_ (LerayTruncation.pageTwoXIso _ (derivedPushforward f M) p q)
  change IsZero (((spectralObj f g M).H (p + q)).obj
    (mk₁ (homOfLE (LerayTruncation.le_succ_eInt q))))
  rcases hpq with hp | hq
  · exact (spectralObj f g M).isZero₂_of_isFirstQuadrant _ _ _ _
      (WithBotTop.coe_lt_coe.2 (by lia))
  · exact (spectralObj f g M).isZero₁_of_isFirstQuadrant _ _ _
      (WithBotTop.coe_le_coe.2 (by lia)) _

/-- The abutment `H^n(⊥ ≤ ⊤) = H^n(R g_*(R f_*(ℱ[0])))` of the spectral object is
`Rⁿ(g ∘ f)_* ℱ`, through the composition isomorphism of derived direct images. -/
private def abutmentIso (n : ℤ) :
    (spectralObj f g M).abutment n ≅ ((modulePushforward (f ≫ g)).rightDerivedPlus n).obj M :=
  (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) n).mapIso
    ((DerivedDirectImageComposition.higherDirectImagesCompIso f g).app
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M))

/-- The abutment filtration, moved to `Rⁿ(g ∘ f)_* ℱ` and indexed decreasingly by `p`:
`Fᵖ` is the image of `H^n(⊥ ≤ n - p + 1)`. -/
private def filt (n p : ℤ) : Subobject (((modulePushforward (f ≫ g)).rightDerivedPlus n).obj M) :=
  (Subobject.map (abutmentIso f g M n).hom).obj
    ((spectralObj f g M).abutmentFiltration n ((n - p + 1 : ℤ) : EInt))

private theorem filt_antitone (n : ℤ) : Antitone (filt f g M n) := fun _ _ hpp' ↦
  (Subobject.map (abutmentIso f g M n).hom).monotone
    ((spectralObj f g M).abutmentFiltration_monotone n (WithBotTop.coe_le_coe.2 (by lia)))

private theorem filt_zero (n : ℤ) : filt f g M n 0 = ⊤ := by
  rw [filt, Abelian.SpectralObject.abutmentFiltration_eq_top _ _ _
    ((spectralObj f g M).isZero₂_of_isFirstQuadrant _ _ _ _
      (WithBotTop.coe_lt_coe.2 (by lia))), Subobject.map_top, Subobject.mk_eq_top_of_isIso]

private theorem filt_succ (n : ℤ) : filt f g M n (n + 1) = ⊥ := by
  rw [filt, Abelian.SpectralObject.abutmentFiltration_eq_bot _ _ _
    ((spectralObj f g M).isZero₁_of_isFirstQuadrant _ _ _
      (WithBotTop.coe_le_coe.2 (by lia)) _), Subobject.map_bot]

/-- The spectral sequence of the truncation tower. -/
private abbrev seq : E₂CohomologicalSpectralSequence (ModuleSheaves Z) :=
  (spectralObj f g M).spectralSequence Abelian.SpectralObject.coreE₂Cohomological

/-- From the page `p + q + 2` on, nothing enters `(p, q)` (`p, q ≥ 0`). -/
private theorem seq_hasEdgeMonoAtFrom (p q r : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : p + q + 2 ≤ r) :
    (seq f g M).HasEdgeMonoAtFrom (p, q) r :=
  SpectralSequence.HasEdgeMonoAtFrom.mk' _ _ r (fun k ↦
    (spectralObj f g M).hasEdgeMonoAt p q (r + k) (p + q) (by lia)
      (fun i j hij hi ↦ (spectralObj f g M).isZero₂_of_isFirstQuadrant _ _ _ _
        (lt_of_lt_of_le (WithBotTop.coe_lt_coe.2 (by lia)) hi)) (by lia)) (by lia)

/-- From the page `max 2 (q + 2)` on, nothing leaves `(p, q)`. -/
private theorem seq_hasEdgeEpiAtFrom (p q r : ℤ) (hr₂ : 2 ≤ r) (hr : q + 2 ≤ r) :
    (seq f g M).HasEdgeEpiAtFrom (p, q) r :=
  SpectralSequence.HasEdgeEpiAtFrom.mk' _ _ r (fun k ↦
    (spectralObj f g M).hasEdgeEpiAt p q (r + k) 0 (by lia)
      (fun i j hij hj ↦ (spectralObj f g M).isZero₁_of_isFirstQuadrant _ _ _ hj _) (by lia))
      (by lia)

/-- The infinity page at `(p, q)` is the graded piece `F^p/F^{p+1}` of `R^{p+q}(g ∘ f)_* ℱ`,
read through the page `p + q + 2`. -/
private def gr (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (seq f g M).pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE (filt f g M (p + q) (p + 1)) (filt f g M (p + q) p)
        (filt_antitone f g M (p + q) (by lia))) :=
  have := seq_hasEdgeMonoAtFrom f g M p q (p + q + 2) hp hq le_rfl
  have := seq_hasEdgeEpiAtFrom f g M p q (p + q + 2) (by lia) (by lia)
  (seq f g M).pageInfinityIso (p, q) (p + q + 2) ≪≫
    (spectralObj f g M).pageXIsoEFull p q (p + q + 2) (by lia)
      ((spectralObj f g M).isZero₁_of_isFirstQuadrant _ _ _
        (WithBotTop.coe_le_coe.2 (by lia)) _)
      ((spectralObj f g M).isZero₂_of_isFirstQuadrant _ _ _ _
        (WithBotTop.coe_lt_coe.2 (by lia))) ≪≫
    (spectralObj f g M).EFullIsoCokernelOfLE p q ≪≫
    Abelian.SpectralObject.cokernelOfLECongr
      ((spectralObj f g M).abutmentFiltration_congr (p + q)
        (show q = p + q - (p + 1) + 1 by lia))
      ((spectralObj f g M).abutmentFiltration_congr (p + q) (show q + 1 = p + q - p + 1 by lia))
      _ ((spectralObj f g M).abutmentFiltration_monotone (p + q)
        (WithBotTop.coe_le_coe.2 (by lia))) ≪≫
    (Abelian.Subobject.cokernelOfLEMapIso (abutmentIso f g M (p + q)).hom _).symm

/-- The natural map `Rᵖ g_*(f_* ℱ) ⟶ Rᵖ(g ∘ f)_* ℱ`, read on `E₂^{p,0}`: `Rᵖ g_*` of the unit
`(f_* ℱ)[0] ⟶ R f_*(ℱ[0])`, followed by the composition isomorphism. -/
private def naturalEdge (p : ℕ) :
    ((seq f g M).page 2).X ((p : ℤ), ((0 : ℕ) : ℤ)) ⟶
      ((modulePushforward (f ≫ g)).rightDerivedPlus (p : ℤ)).obj M :=
  ((LerayCard.pageTwoNatIsoDerived (modulePushforward g).rightDerivedFunctorPlus
      (p : ℤ) ((0 : ℕ) : ℤ)).app (derivedPushforward f M)).hom ≫
    ((modulePushforward g).rightDerivedPlus (p : ℤ)).map
      ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (modulePushforward f)).hom.app M) ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) (p : ℤ)).map
      ((modulePushforward g).rightDerivedFunctorPlus.map
          ((Functor.mapSingleFunctorCompQhIso (modulePushforward f)).inv.app M ≫
            (modulePushforward f).rightDerivedFunctorPlusUnith.app
              ((HomotopyCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M) ≫
            (modulePushforward f).rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := ModuleSheaves X) 0).inv.app M)) ≫
        (DerivedDirectImageComposition.higherDirectImagesCompIso f g).hom.app
          ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M))

/-- An inclusion of the zero subobject is zero. -/
private theorem ofLE_eq_zero_of_eq_bot {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] {A : C} {P Q : Subobject A} (hP : P = ⊥) (h : P ≤ Q) :
    Subobject.ofLE P Q h = 0 := by
  subst hP
  rw [← cancel_mono Q.arrow, Subobject.ofLE_arrow, Subobject.bot_arrow, zero_comp]

/-- Since `F^{p+1} Rᵖ(g ∘ f)_* ℱ = 0`, the graded piece `F^p/F^{p+1}` maps back onto `F^p`. -/
private def grDesc (p : ℕ) :
    cokernel (Subobject.ofLE (filt f g M ((p : ℤ) + ((0 : ℕ) : ℤ)) ((p : ℤ) + 1))
      (filt f g M ((p : ℤ) + ((0 : ℕ) : ℤ)) (p : ℤ)) (filt_antitone f g M _ (by lia))) ⟶
        (filt f g M (p : ℤ) (p : ℤ) : ModuleSheaves Z) :=
  cokernel.desc _ (𝟙 _) (by
    rw [Category.comp_id]
    exact ofLE_eq_zero_of_eq_bot (filt_succ f g M (p : ℤ)) _)

private theorem grDesc_comp_π (p : ℕ) :
    grDesc f g M p ≫ cokernel.π (Subobject.ofLE (filt f g M ((p : ℤ) + ((0 : ℕ) : ℤ)) ((p : ℤ) + 1))
      (filt f g M ((p : ℤ) + ((0 : ℕ) : ℤ)) (p : ℤ)) (filt_antitone f g M _ (by lia))) = 𝟙 _ := by
  refine coequalizer.hom_ext ?_
  rw [grDesc, cokernel.π_desc_assoc, Category.id_comp, Category.comp_id]

private lemma H_map_eq (n : ℤ) {a b : ComposableArrows EInt 1} (α : a ⟶ b) :
    ((spectralObj f g M).H n).map α =
      (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) n).map
        ((modulePushforward g).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.TStructure.t.ω₁.map α).app (derivedPushforward f M))) := rfl

open DerivedCategory.Plus.TStructure in
private lemma ω₁_map_app_δ₁ (q : ℤ) (K : DerivedCategory.Plus (ModuleSheaves Y)) :
    (t.ω₁.map (twoδ₁Toδ₀' (⊥ : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) bot_le
      (WithBotTop.coe_le_coe.2 (by lia)))).app K =
        (t.truncGEπ q).app ((t.truncLT (q + 1)).obj K) := by
  dsimp only [Triangulated.TStructure.ω₁]
  rw [NatTrans.hcomp_app]
  have h1 : ((twoδ₁Toδ₀' (⊥ : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) bot_le
      (WithBotTop.coe_le_coe.2 (by lia))).app 1) = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

open DerivedCategory.Plus.TStructure in
private lemma ω₁_map_app_δ₂ (q : ℤ) (K : DerivedCategory.Plus (ModuleSheaves Y)) :
    (t.ω₁.map (twoδ₂Toδ₁' (⊥ : EInt) ((q + 1 : ℤ) : EInt) ⊤ bot_le le_top)).app K =
      (t.truncLTι (q + 1)).app K := by
  dsimp only [Triangulated.TStructure.ω₁]
  rw [NatTrans.hcomp_app]
  have h0 : ((twoδ₂Toδ₁' (⊥ : EInt) ((q + 1 : ℤ) : EInt) ⊤ bot_le le_top).app 0) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h0, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

private lemma shift_aux {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [Φ.CommShift ℤ] (p : ℤ)
    (n : ℤ) (hn : n = 0) (h1 : n + 0 = 0) (h3 : n + p = p) (Z₀ : A) :
    (DerivedCategory.Plus.homologyFunctor B p).map
        (Φ.map (((DerivedCategory.Plus.singleFunctors A).shiftIso n 0 0 h1).inv.app Z₀)) ≫
      (DerivedCategory.Plus.homologyFunctor B p).map
        ((Φ.commShiftIso n).hom.app ((DerivedCategory.Plus.singleFunctor A 0).obj Z₀)) ≫
      ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso n p p h3).hom.app
        (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj Z₀)) = 𝟙 _ := by
  subst hn
  rw [SingleFunctors.shiftIso_zero, Functor.commShiftIso_zero, Functor.shiftIso_zero_hom_app]
  have e1 : (Functor.isoWhiskerLeft ((DerivedCategory.Plus.singleFunctors A).functor 0)
      (shiftFunctorZero (DerivedCategory.Plus A) ℤ)).inv.app Z₀ =
      (shiftFunctorZero (DerivedCategory.Plus A) ℤ).inv.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj Z₀) := rfl
  have e2 : (Functor.CommShift.isoZero Φ ℤ).hom.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj Z₀) =
      Φ.map ((shiftFunctorZero (DerivedCategory.Plus A) ℤ).hom.app _) ≫
        (shiftFunctorZero (DerivedCategory.Plus B) ℤ).inv.app _ := by
    simp [Functor.CommShift.isoZero]
  rw [e1, e2]
  change (DerivedCategory.Plus.homologyFunctor B p).map _ ≫
    (DerivedCategory.Plus.homologyFunctor B p).map (_ ≫ _) ≫
    (DerivedCategory.Plus.homologyFunctor B p).map _ = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Category.assoc,
    ← Φ.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Φ.map_id, Category.id_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]

private lemma chain_aux {C : Type*} [Category C] {P Q R R' N N' : C} (Hπ : P ⟶ Q) (θ : Q ⟶ R)
    (Hι : P ⟶ R) (Hα : Q ⟶ R') (σ₁ : R ≅ R') (HSβ : R' ⟶ N') (β : R ≅ N) (σ₂ : N ≅ N')
    (Hη : N' ⟶ R) (h1 : Hπ ≫ θ = Hι) (h2 : Hα = θ ≫ σ₁.hom) (h3 : HSβ = σ₁.inv ≫ β.hom ≫ σ₂.hom)
    (h4 : β.inv = σ₂.hom ≫ Hη) :
    Hπ ≫ Hα ≫ HSβ ≫ Hη = Hι := by
  subst h2 h3
  have h5 : σ₂.hom ≫ Hη = β.inv := h4.symm
  simp only [Category.assoc, h5, Iso.hom_inv_id, Category.comp_id]
  exact h1

private lemma unit_comp :
    (DerivedCategory.Plus.TStructure.t.truncGEπ 0).app
        ((DerivedCategory.Plus.TStructure.t.truncLT (0 + 1)).obj (derivedPushforward f M)) ≫
      (DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor 0).hom.app
        (derivedPushforward f M) ≫
      (DerivedCategory.Plus.singleFunctor (ModuleSheaves Y) 0).map
        ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (modulePushforward f)).hom.app M) ≫
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (modulePushforward f)).app M =
    (DerivedCategory.Plus.TStructure.t.truncLTι (0 + 1)).app (derivedPushforward f M) := by
  have := isGE_derivedPushforward f M
  apply hom_ext_truncLT_of_H0
  simp only [Functor.map_comp]
  exact chain_aux _ _ _ _
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app _).symm _
    ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (modulePushforward f)).app M)
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app _).symm _
    (truncGEπ_truncGELTCompHomologyFunctorIso_hom (A := ModuleSheaves Y) 0 _)
    (H_map_truncGELTIso_hom (A := ModuleSheaves Y) 0 _)
    (H_map_single (A := ModuleSheaves Y) 0 _)
    (Stacks.DerivedIndexing.rightDerivedPlusZeroIso_inv_app _ M)

private lemma shiftIso_app_hom_zero {A B : Type*} [Category A] [Category B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [Φ.CommShift ℤ] (p : ℕ) (Z₀ : A) :
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso Φ (p : ℤ)
      ((0 : ℕ) : ℤ)).app Z₀).hom = 𝟙 _ := by
  simp only [DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso,
    DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIsoOfEq, Iso.app_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Functor.comp_map]
  exact shift_aux Φ (p : ℤ) (-((0 : ℕ) : ℤ)) (by simp) _ _ Z₀

/-- The natural edge map is the bottom-row edge of the truncation spectral sequence. -/
private theorem naturalEdge_eq (p : ℕ) [(seq f g M).HasEdgeEpiAtFrom ((p : ℤ), ((0 : ℕ) : ℤ)) 2] :
    naturalEdge f g M p = ((seq f g M).edgeEpi ((p : ℤ), ((0 : ℕ) : ℤ)) 2 ≫
      (gr f g M p ((0 : ℕ) : ℤ) (by lia) le_rfl).hom ≫ grDesc f g M p) ≫
        (filt f g M (p : ℤ) (p : ℤ)).arrow := by
  have := seq_hasEdgeMonoAtFrom f g M p ((0 : ℕ) : ℤ) ((p : ℤ) + ((0 : ℕ) : ℤ) + 2)
    (by lia) le_rfl le_rfl
  have := seq_hasEdgeEpiAtFrom f g M p ((0 : ℕ) : ℤ) ((p : ℤ) + ((0 : ℕ) : ℤ) + 2)
    (by lia) (by lia)
  have e1 : naturalEdge f g M p =
      (((spectralObj f g M).spectralSequenceFirstPageXIso Abelian.SpectralObject.coreE₂Cohomological
          ((p : ℤ), ((0 : ℕ) : ℤ)) (((0 : ℕ) : ℤ) : EInt) ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt)
          rfl rfl ((p : ℤ) + ((0 : ℕ) : ℤ)) rfl).hom ≫
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) ((p : ℤ) + ((0 : ℕ) : ℤ))).map
          ((modulePushforward g).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor
              ((0 : ℕ) : ℤ)).hom.app (derivedPushforward f M))) ≫
          ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
            (modulePushforward g).rightDerivedFunctorPlus (p : ℤ) ((0 : ℕ) : ℤ)).app
              ((DerivedCategory.Plus.homologyFunctor (ModuleSheaves Y) ((0 : ℕ) : ℤ)).obj
                (derivedPushforward f M))).hom)) ≫
      ((modulePushforward g).rightDerivedPlus (p : ℤ)).map
          ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (modulePushforward f)).hom.app M) ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) (p : ℤ)).map
          ((modulePushforward g).rightDerivedFunctorPlus.map
              ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (modulePushforward f)).app M) ≫
            (DerivedDirectImageComposition.higherDirectImagesCompIso f g).hom.app
              ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M)) := rfl
  have := isGE_derivedPushforward f M
  have hπ : IsIso ((DerivedCategory.Plus.TStructure.t.truncGEπ ((0 : ℕ) : ℤ)).app
      ((DerivedCategory.Plus.TStructure.t.truncLT (((0 : ℕ) : ℤ) + 1)).obj
        (derivedPushforward f M))) :=
    (DerivedCategory.Plus.TStructure.t.isGE_iff_isIso_truncGEπ_app _ _).1 inferInstance
  have hπ' : IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z)
      ((p : ℤ) + ((0 : ℕ) : ℤ))).map ((modulePushforward g).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncGEπ ((0 : ℕ) : ℤ)).app
          ((DerivedCategory.Plus.TStructure.t.truncLT (((0 : ℕ) : ℤ) + 1)).obj
            (derivedPushforward f M))))) := by
    have := Functor.map_isIso (modulePushforward g).rightDerivedFunctorPlus
      ((DerivedCategory.Plus.TStructure.t.truncGEπ ((0 : ℕ) : ℤ)).app
          ((DerivedCategory.Plus.TStructure.t.truncLT (((0 : ℕ) : ℤ) + 1)).obj
            (derivedPushforward f M)))
    exact Functor.map_isIso _ _
  have hπe : Epi ((DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z)
      ((p : ℤ) + ((0 : ℕ) : ℤ))).map ((modulePushforward g).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncGEπ ((0 : ℕ) : ℤ)).app
          ((DerivedCategory.Plus.TStructure.t.truncLT (((0 : ℕ) : ℤ) + 1)).obj
            (derivedPushforward f M))))) := @IsIso.epi_of_iso _ _ _ _ _ hπ'
  apply (cancel_epi ((spectralObj f g M).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), ((0 : ℕ) : ℤ)) (((0 : ℕ) : ℤ) : EInt)
    ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt) rfl rfl ((p : ℤ) + ((0 : ℕ) : ℤ)) rfl).inv).1
  apply (cancel_epi ((DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z)
      ((p : ℤ) + ((0 : ℕ) : ℤ))).map ((modulePushforward g).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncGEπ ((0 : ℕ) : ℤ)).app
          ((DerivedCategory.Plus.TStructure.t.truncLT (((0 : ℕ) : ℤ) + 1)).obj
            (derivedPushforward f M)))))).1
  trans (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) (p : ℤ)).map
      ((modulePushforward g).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLTι (((0 : ℕ) : ℤ) + 1)).app
          (derivedPushforward f M))) ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) (p : ℤ)).map
      ((DerivedDirectImageComposition.higherDirectImagesCompIso f g).hom.app
              ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M))
  · rw [e1]
    refine chain_left _ _ _ _ _ _ _ _ _ (shiftIso_app_hom_zero _ p _) ?_
      (CategoryTheory.Functor.map_comp _ _ _)
    have h' := congrArg (fun z => (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z)
      (p : ℤ)).map ((modulePushforward g).rightDerivedFunctorPlus.map z)) (unit_comp f M)
    simp only [Functor.map_comp] at h'
    exact h'
  · refine chain_right' _ _ _ _ _ _ _ _ _
      ((spectralObj f g M).pOpcycles
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt) ≤ ⊤)) ((p : ℤ) + ((0 : ℕ) : ℤ)))
      ((spectralObj f g M).opcyclesToE (homOfLE (bot_le : (⊥ : EInt) ≤ (((0 : ℕ) : ℤ) : EInt)))
        (homOfLE (WithBotTop.coe_le_coe.2 (Int.le_add_one (le_refl ((0 : ℕ) : ℤ)))))
        (homOfLE (le_top : ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt) ≤ ⊤))
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt))) rfl
        ((p : ℤ) + ((0 : ℕ) : ℤ) - 1) ((p : ℤ) + ((0 : ℕ) : ℤ)) ((p : ℤ) + ((0 : ℕ) : ℤ) + 1)
        (sub_add_cancel _ _) rfl)
      ((spectralObj f g M).fromOpcycles
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt) ≤ ⊤))
        (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)) rfl ((p : ℤ) + ((0 : ℕ) : ℤ))) _ _ ?_ ?_ ?_
    · have hu : ((spectralObj f g M).H ((p : ℤ) + ((0 : ℕ) : ℤ))).map
          (twoδ₁Toδ₀' (⊥ : EInt) (((0 : ℕ) : ℤ) : EInt) ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt) bot_le
            (WithBotTop.coe_le_coe.2 (Int.le_add_one (le_refl ((0 : ℕ) : ℤ))))) =
          (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z)
            ((p : ℤ) + ((0 : ℕ) : ℤ))).map ((modulePushforward g).rightDerivedFunctorPlus.map
              ((DerivedCategory.Plus.TStructure.t.truncGEπ ((0 : ℕ) : ℤ)).app
                ((DerivedCategory.Plus.TStructure.t.truncLT (((0 : ℕ) : ℤ) + 1)).obj
                  (derivedPushforward f M)))) :=
        (H_map_eq f g M _ _).trans (congrArg (fun z =>
          (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z)
            ((p : ℤ) + ((0 : ℕ) : ℤ))).map ((modulePushforward g).rightDerivedFunctorPlus.map z))
          (ω₁_map_app_δ₁ _ _))
      rw [← hu]
      exact edge_formula (spectralObj f g M) (p : ℤ) ((0 : ℕ) : ℤ) (Int.natCast_nonneg p)
        Nat.cast_zero _ _
    · exact opcyclesToE_EFullIsoCokernelOfLE_hom _ _ _ _ _
        ((congrArg (cokernel.π _ ≫ ·) (Category.assoc _ _ _)).trans
          (π_congr_mapIso_desc_arrow _ _ _ _ _ _))
    · rw [Abelian.SpectralObject.p_fromOpcycles]
      exact (H_map_eq f g M _ _).trans (congrArg (fun z =>
          (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z)
            ((p : ℤ) + ((0 : ℕ) : ℤ))).map ((modulePushforward g).rightDerivedFunctorPlus.map z))
          ((congrArg (fun α => (DerivedCategory.Plus.TStructure.t.ω₁.map α).app
            (derivedPushforward f M)) (hom_eq _ (twoδ₂Toδ₁' (⊥ : EInt)
              ((((0 : ℕ) : ℤ) + 1 : ℤ) : EInt) ⊤ bot_le le_top))).trans (ω₁_map_app_δ₂ _ _)))

/-- The natural edge map lands in `Fᵖ Rᵖ(g ∘ f)_* ℱ`. -/
private theorem factors_naturalEdge (p : ℕ) :
    (filt f g M (p : ℤ) (p : ℤ)).Factors (naturalEdge f g M p) := by
  have := seq_hasEdgeEpiAtFrom f g M p ((0 : ℕ) : ℤ) 2 le_rfl (by lia)
  rw [naturalEdge_eq f g M p]
  exact (filt f g M (p : ℤ) (p : ℤ)).factors_comp_arrow _

/-- The bottom-row edge, read through `gr`, is the natural edge map. -/
private theorem edgeEpi_comp_gr_hom (p : ℕ) [(seq f g M).HasEdgeEpiAtFrom ((p : ℤ), ((0 : ℕ) : ℤ))
    2] :
    (seq f g M).edgeEpi ((p : ℤ), ((0 : ℕ) : ℤ)) 2 ≫ (gr f g M p ((0 : ℕ) : ℤ) (by lia)
        le_rfl).hom =
      (filt f g M (p : ℤ) (p : ℤ)).factorThru (naturalEdge f g M p) (factors_naturalEdge f g M p) ≫
        cokernel.π (Subobject.ofLE (filt f g M ((p : ℤ) + ((0 : ℕ) : ℤ)) ((p : ℤ) + 1))
          (filt f g M ((p : ℤ) + ((0 : ℕ) : ℤ)) (p : ℤ)) (filt_antitone f g M _ (by lia))) := by
  have h : (filt f g M (p : ℤ) (p : ℤ)).factorThru (naturalEdge f g M p)
      (factors_naturalEdge f g M p) = (seq f g M).edgeEpi ((p : ℤ), ((0 : ℕ) : ℤ)) 2 ≫
        (gr f g M p ((0 : ℕ) : ℤ) (by lia) le_rfl).hom ≫ grDesc f g M p := by
    rw [← cancel_mono (filt f g M (p : ℤ) (p : ℤ)).arrow, Subobject.factorThru_arrow,
      naturalEdge_eq f g M p]
  rw [h, Category.assoc, Category.assoc, grDesc_comp_π, Category.comp_id]

end

end

end MMP.Analytic.Proof_thm_mmp_module_relative_leray_with_edge

namespace MMP.RelativeLeray

attribute [local instance] HasDerivedCategory.standard

-- The locally small models of `Stacks.SmallDerivedModel` take precedence over the standard model,
-- as they did while they were global Stacks instances.
open scoped Stacks.SmallDerivedModel

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  DerivedPushforwardSections.modulePushforward_additive
  LerayTruncation.commShiftRightDerivedFunctorPlus
  LerayTruncation.isTriangulatedRightDerivedFunctorPlus

open MMP.Analytic.Proof_thm_mmp_module_relative_leray_with_edge in
/-- **The relative Leray spectral sequence of a sheaf of modules, with its bottom-row edge.**
For morphisms of ringed spaces `f : X ⟶ Y`, `g : Y ⟶ Z` and an `𝒪_X`-module `ℱ`, let `E` be the
spectral sequence of the canonical truncation tower of `R f_*(ℱ[0])` pushed forward by `R g_*`
(with `E₂^{p,q} ≅ Rᵖ g_*(R^q f_* ℱ)` by `Stacks.Cohomology.LerayCard.pageTwoNatIsoDerived`).
Then `E` is first-quadrant, has an infinity page everywhere, and there is a finite decreasing
filtration `F n` of `Rⁿ(g ∘ f)_* ℱ` with `F n 0 = ⊤`, `F n (n + 1) = ⊥` and
`E_∞^{p,q} ≅ F (p+q) p / F (p+q) (p+1)`, such that in every degree `p` the bottom-row edge
`E₂^{p,0} ↠ E_∞^{p,0} ≅ F p p ⊆ Rᵖ(g ∘ f)_* ℱ`, read on `E₂^{p,0} ≅ Rᵖ g_*(f_* ℱ)`, is the
natural map `Rᵖ g_*(f_* ℱ) ⟶ Rᵖ(g ∘ f)_* ℱ`. -/
@[mmp "thm_mmp_module_relative_leray_with_edge"]
public theorem exists_abutment_spectralSequence_edge {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : ModuleSheaves X) :
    let K := (modulePushforward f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M)
    let E := (Abelian.SpectralObject.E₂SpectralSequenceFunctor (ModuleSheaves Z)).obj
      ((LerayTruncation.cohomologySpectralObjectFunctor
        (modulePushforward g).rightDerivedFunctorPlus).obj K)
    let H : ℕ → ModuleSheaves Z := fun n ↦
      ((modulePushforward (f ≫ g)).rightDerivedPlus (n : ℤ)).obj M
    (∀ p q : ℤ, (p < 0 ∨ q < 0) → IsZero ((E.page 2).X (p, q))) ∧
    ∃ (_ : ∀ p q : ℤ, E.HasPageInfinityAt (p, q))
      (F : ∀ n : ℕ, ℤ → Subobject (H n)) (hF : ∀ n : ℕ, Antitone (F n)),
      (∀ n : ℕ, F n 0 = ⊤) ∧ (∀ n : ℕ, F n ((n : ℤ) + 1) = ⊥) ∧
      ∃ (gr : ∀ p q : ℕ, E.pageInfinity ((p : ℤ), (q : ℤ)) ≅
          cokernel (Subobject.ofLE (F (p + q) ((p : ℤ) + 1)) (F (p + q) (p : ℤ))
            (hF (p + q) (by omega)))),
        ∀ p : ℕ, ∃ (_ : E.HasEdgeEpiAtFrom ((p : ℤ), ((0 : ℕ) : ℤ)) 2)
          (ε : (E.page 2).X ((p : ℤ), ((0 : ℕ) : ℤ)) ⟶ (F p (p : ℤ) : ModuleSheaves Z)),
          ε ≫ (F p (p : ℤ)).arrow =
            ((LerayCard.pageTwoNatIsoDerived (modulePushforward g).rightDerivedFunctorPlus
                (p : ℤ) ((0 : ℕ) : ℤ)).app K).hom ≫
              ((modulePushforward g).rightDerivedPlus (p : ℤ)).map
                ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (modulePushforward f)).hom.app
                  M) ≫
              (DerivedCategory.Plus.homologyFunctor (ModuleSheaves Z) (p : ℤ)).map
                ((modulePushforward g).rightDerivedFunctorPlus.map
                    ((Functor.mapSingleFunctorCompQhIso (modulePushforward f)).inv.app M ≫
                      (modulePushforward f).rightDerivedFunctorPlusUnith.app
                        ((HomotopyCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M) ≫
                      (modulePushforward f).rightDerivedFunctorPlus.map
                        ((Functor.singleFunctorPlusIsoCompQh (A := ModuleSheaves X) 0).inv.app
                          M)) ≫
                  (DerivedDirectImageComposition.higherDirectImagesCompIso f g).hom.app
                    ((DerivedCategory.Plus.singleFunctor (ModuleSheaves X) 0).obj M)) ∧
          E.edgeEpi ((p : ℤ), ((0 : ℕ) : ℤ)) 2 ≫ (gr p 0).hom =
            ε ≫ cokernel.π (Subobject.ofLE (F (p + 0) ((p : ℤ) + 1)) (F (p + 0) (p : ℤ))
              (hF (p + 0) (by omega))) := by
  intro K E H
  have := isFirstQuadrant_spectralObj f g M
  refine ⟨isZero_page_two f g M, fun p q ↦ inferInstanceAs ((seq f g M).HasPageInfinityAt (p, q)),
    fun n ↦ filt f g M n, fun n ↦ filt_antitone f g M n, fun n ↦ filt_zero f g M n,
    fun n ↦ filt_succ f g M n, fun p q ↦ gr f g M p q (by lia) (by lia), fun p ↦ ?_⟩
  have := seq_hasEdgeEpiAtFrom f g M p ((0 : ℕ) : ℤ) 2 le_rfl (by lia)
  exact ⟨this, (filt f g M (p : ℤ) (p : ℤ)).factorThru (naturalEdge f g M p)
    (factors_naturalEdge f g M p), Subobject.factorThru_arrow _ _ _, edgeEpi_comp_gr_hom f g M p⟩

end MMP.RelativeLeray

end
