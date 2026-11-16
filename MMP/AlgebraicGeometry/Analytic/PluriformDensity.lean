module
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AlgebraicChartDifferential
public import MMP.AlgebraicGeometry.Analytic.PluriformDensityDefs
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SubsingletonSectionsStalk
public import MMP.Analysis.Complex.CauchyOsgoodLaurent
import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle

/-!
# Étale coordinates give a holomorphic atlas on `X^an`

Let `X` be a smooth complex variety of dimension `n`, with structure morphism
`sX : X ⟶ Spec ℂ`, and let `X^an = MMP.Analytic.ComplexPoints sX` be its complex realization.
*Étale coordinates* on a Zariski open `U ⊆ X` are regular functions `z_1, …, z_n ∈ Γ(X, U)` for
which the morphism `(z_1, …, z_n) : U ⟶ 𝔸ⁿ_ℂ` is étale, i.e. whose differentials form a basis of
`Ω_{U/ℂ}`. On the `ℂ`-points of `U` they give the map `y ↦ (z_1(y), …, z_n(y)) ∈ ℂⁿ`.

Étale coordinates exist around every point of `X^an`; around every point of `U(ℂ)` the map they
define restricts to a homeomorphism of an open neighbourhood in `X^an` onto an open subset of
`ℂⁿ`; and on such a chart every regular function of `X` is a holomorphic function of the
coordinates. In particular two such charts differ by a holomorphic map with holomorphic inverse,
so they form a complex-analytic atlas on `X^an` for its analytic topology.

## Main results

* `MMP.Analytic.ComplexPoints.etaleCoordinate_atlas`: the three statements above.

## Implementation notes

* Étale coordinates are expressed by `AlgebraicGeometry.Etale` of
  `AlgebraicGeometry.AffineSpace.homOfVector`; for `X` smooth of relative dimension `n` over
  `ℂ` this is equivalent to `dz_1, …, dz_n` being a basis of `Ω_{U/ℂ}`, and it makes sense for
  every open `U`, affine or not.
* A chart is an open subset `W ⊆ U(ℂ)` of `X^an` on which the coordinate map is an open
  embedding into `ℂⁿ = Fin n → ℂ`. The compatibility of charts is stated for an arbitrary
  regular function `f ∈ Γ(X, U')`: on `W ∩ U'(ℂ)` it equals `G ∘ z` for a function `G`
  holomorphic on the image of `W ∩ U'(ℂ)`. Applied to the coordinates `w_j` of a second chart
  and, symmetrically, to the `z_i`, this says that the transition maps are biholomorphic.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*]
* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

section

open CategoryTheory AlgebraicGeometry Topology MMP.Analytic MMP.Analytic.ComplexPoints
open Stacks.RelativeDifferentialStalkMap
open MMP MMP.UnderlyingSpace Filter
open MMP.Intersection.Scheme (dimension)
open scoped ContDiff

namespace MMP.Analytic.Proof_lem_mmp_analytic_etale_chart_atlas

/-- On a scheme smooth of relative dimension `n` over `ℂ`, the stalk of `Ω_{X/ℂ}` at every
point has rank `n`. -/
private theorem _root_.MMP.Analytic.finrank_kaehlerDifferential_stalk
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n sX] (p : X) :
    letI := (sX.stalkMap p).hom.toAlgebra
    Module.finrank (X.presheaf.stalk p)
      Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)] = n := by
  classical
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  letI := algebraStalkMap sX p
  have hrank := AlgebraicGeometry.finrank_stalk_relativeDifferentials_eq_fiberDimensionAt sX p
  obtain ⟨U₀, hU₀, V, hV, hpV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := sX) p
  let algAB : Algebra Γ(Spec (.of ℂ), U₀) Γ(X, V) := (sX.appLE U₀ V e).hom.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Spec (.of ℂ), U₀) Γ(X, V) := hstd
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ := hsm.out
  have : Finite σ := hσ
  have : Finite ι := hι
  have hdim := Stacks.RelativeDifferentialStalkMap.fiberDimensionAt_eq_of_submersivePresentation
    sX p ⟨V, hV⟩ ⟨U₀, hU₀⟩ hpV e rfl P
  rw [hdim] at hrank
  have hPd : Nat.card ι - Nat.card σ = n := by
    rw [← hP]; rfl
  rw [(relativeDifferentialsStalkKaehlerEquiv sX p).finrank_eq, hPd] at hrank
  exact_mod_cast hrank

/-- Étale coordinates exist around every complex point. -/
private theorem exists_etale_coordinates {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX] :
    ∀ x : ComplexPoints sX, ∃ (U : X.Opens) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧ x ∈ chart U := by
  intro x
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  let q : Spec (.of ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  let p : X := x.hom q
  obtain ⟨U, -, hpU, π, hπ, hover⟩ :=
    MMP.Flips.ResolutionInputs.exists_isAffineOpen_etale_affineSpace sX p
  revert π
  rw [finrank_kaehlerDifferential_stalk (n := n) sX p]
  intro π hπ hover
  refine ⟨U, fun i ↦ U.topIso.hom (π.appTop (AffineSpace.coord _ ⟨i⟩)), ?_, ?_⟩
  · convert hπ
    ext1
    · simp [hover]
    · rename_i i
      rw [AffineSpace.homOfVector_appTop_coord]
      exact Iso.hom_inv_id_apply U.topIso _
  · show x.hom ⁻¹ᵁ U = ⊤
    refine eq_top_iff.mpr fun r _ ↦ ?_
    have : r = q := Subsingleton.elim _ _
    subst this
    exact hpU

private theorem _root_.MMP.Analytic.etale_eval₂Hom_of_etale_homOfVector
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {n : ℕ} (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    (MvPolynomial.eval₂Hom (sX.appLE ⊤ V le_top).hom
      (fun i : ULift.{0} (Fin n) ↦ X.presheaf.map (homOfLE hVU).op (z i.down))).Etale := by
  have : IsAffine V.toScheme := hV
  set w : ULift.{0} (Fin n) → Γ(X, V) := fun i ↦ X.presheaf.map (homOfLE hVU).op (z i.down)
  set φ := MvPolynomial.eval₂Hom (sX.appLE ⊤ V le_top).hom w
  set π := AffineSpace.homOfVector (V.ι ≫ sX) (fun i ↦ V.topIso.inv (w i))
  have hπ : Etale π := by
    have h1 : Etale (X.homOfLE hVU ≫ AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) := by
      have := hz; infer_instance
    convert h1 using 1
    rw [AffineSpace.comp_homOfVector, ← Category.assoc, Scheme.homOfLE_ι]
    refine congrArg (AffineSpace.homOfVector (V.ι ≫ sX)) (funext fun i ↦ ?_)
    simp only [Function.comp_apply, w, Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
    show (X.presheaf.map (homOfLE hVU).op ≫ X.presheaf.map (eqToHom (by simp)).op) (z i.down) =
      (X.presheaf.map (eqToHom (by simp)).op ≫ X.presheaf.map (homOfLE (by simpa using hVU)).op)
          (z i.down)
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have H : Etale (π ≫ (AffineSpace.isoOfIsAffine _ (Spec (.of ℂ))).hom) := inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.comp_appTop,
    AffineSpace.isoOfIsAffine_hom_appTop] at H
  have heq : (π.appTop.hom).comp (MvPolynomial.eval₂Hom
      ((AffineSpace (ULift.{0} (Fin n)) (Spec (.of ℂ)) ↘ Spec (.of ℂ)).appTop).hom
      (AffineSpace.coord (Spec (.of ℂ)))) = V.topIso.inv.hom.comp φ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := congrArg (fun g ↦ g.appTop.hom r) (AffineSpace.homOfVector_over (V.ι ≫ sX)
        (fun i ↦ V.topIso.inv (w i)))
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, φ]
      have key : (V.ι ≫ sX).appTop = sX.appLE ⊤ V le_top ≫ V.topIso.inv := by
        rw [Iso.eq_comp_inv, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop,
          Scheme.Opens.topIso_hom]
        simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        erw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
      rw [h1, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, key]
      rfl
    · intro i
      simp [π, φ]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at H
  rw [← RingHom.comp_assoc, heq] at H
  have H2 := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{0} (Fin n)) Γ(Spec (.of ℂ), ⊤)))).inv))
    (RingHom.Etale.stableUnderComposition _ _ H
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso V.topIso.hom)))
  convert H2 using 1
  refine RingHom.ext fun x ↦ ?_
  simp only [RingHom.comp_apply]
  erw [CommRingCat.inv_hom_apply]
  exact (Iso.inv_hom_id_apply V.topIso (φ x)).symm

/-- A derivation into a residue field vanishing on the image of an étale ring map vanishes. -/
private theorem eq_zero_of_etale {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A)
    (hφ : φ.Etale) (ev : A →+* ℂ) (D : A → ℂ) (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = ev a * D b + ev b * D a) (hφD : ∀ r, D (φ r) = 0) (a : A) :
    D a = 0 := by
  letI := φ.toAlgebra
  letI : Algebra A ℂ := ev.toAlgebra
  letI : Algebra R ℂ := (ev.comp φ).toAlgebra
  haveI : IsScalarTower R A ℂ := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hE : Algebra.Etale R A := hφ
  let D' : Derivation R A ℂ := Derivation.mk'
    { toFun := D
      map_add' := hadd
      map_smul' := fun r b ↦ by
        change D (φ r * b) = ev (φ r) * D b
        rw [hmul, hφD, mul_zero, add_zero] } (fun a b ↦ hmul a b)
  change D' a = 0
  rw [← D'.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D R A a) 0,
    map_zero]

section ChartDerivatives

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ
    E]

private theorem chartDeriv_apply_eq_zero {n : ℕ}
    {e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) E} (he : IsAlgebraicChart e)
    {p : UnderlyingSpace ℂ X} (hp : p ∈ e.source) {V : X.Opens} (hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V)
    (w : ULift.{0} (Fin n) → Γ(X, V))
    (hw : (MvPolynomial.eval₂Hom ((X ↘ Spec (.of ℂ)).appLE ⊤ V le_top).hom w).Etale)
    (v : E) (hv : ∀ i, chartDeriv e V p (w i) v = 0) (c : Γ(X, V)) :
    chartDeriv e V p c v = 0 := by
  refine eq_zero_of_etale _ hw (evalRingHom p hpV) (fun c ↦ chartDeriv e V p c v) ?_ ?_ ?_ c
  · intro a b
    simp [chartDeriv_add he hp hpV]
  · intro a b
    rw [chartDeriv_mul he hp hpV]
    simp [evalRingHom_apply, evalExt_of_le _ hpV, add_comm]
  · intro r
    induction r using MvPolynomial.induction_on with
    | C a =>
      have : (MvPolynomial.eval₂Hom ((X ↘ Spec (.of ℂ)).appLE ⊤ V le_top).hom w)
          (MvPolynomial.C a) = constSection V ((Scheme.ΓSpecIso _).hom a) := by
        refine (MvPolynomial.eval₂_C _ _ _).trans ?_
        show _ = X.presheaf.map (homOfLE le_top).op (((Scheme.ΓSpecIso _).inv ≫
          (X ↘ Spec (.of ℂ)).appTop) ((Scheme.ΓSpecIso _).hom a))
        rw [CommRingCat.comp_apply, Iso.hom_inv_id_apply]
        rfl
      exact (congrArg (fun c ↦ chartDeriv e V p c v) this).trans
        (by rw [chartDeriv_constSection hp hpV]; rfl)
    | add a b ha hb =>
      simp only [map_add, chartDeriv_add he hp hpV, ContinuousLinearMap.add_apply, ha, hb,
        add_zero]
    | mul_X a i ha =>
      simp only [map_mul, chartDeriv_mul he hp hpV, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ha, MvPolynomial.eval₂Hom_X', hv, smul_zero, add_zero]

private theorem chartDeriv_res {e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) E}
    {p : UnderlyingSpace ℂ X} (hp : p ∈ e.source) {U V : X.Opens} (hVU : V ≤ U)
    (hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V) (a : Γ(X, U)) :
    chartDeriv e V p (X.presheaf.map (homOfLE hVU).op a) = chartDeriv e U p a := by
  unfold chartDeriv
  refine EventuallyEq.fderiv_eq ?_
  filter_upwards [eventually_mem_target_and_le hp hpV] with k hk
  rw [evalExt_of_le _ hk.2, evalExt_of_le _ (hk.2.trans (Scheme.Hom.preimage_mono _ hVU)),
    eval_restrict]

private theorem injective_fderiv [FiniteDimensional ℂ E] {n : ℕ}
    {e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) E} (he : IsAlgebraicChart e)
    {p : UnderlyingSpace ℂ X} (hp : p ∈ e.source) (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ X ↘ Spec (.of ℂ))
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (hpU : ⊤ ≤ p.toHom ⁻¹ᵁ U) :
    Function.Injective (fderiv ℂ (fun k i ↦ evalExt U (z i) (e.symm k)) (e p)) := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.toHom (IsLocalRing.closedPoint ℂ)) ((top_le_preimage_iff p U).1 hpU)
  have hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V := (top_le_preimage_iff p V).2 hxV
  have hw := etale_eval₂Hom_of_etale_homOfVector _ U z hz V hV hVU
  have hd : ∀ i, DifferentiableAt ℂ (fun k ↦ evalExt U (z i) (e.symm k)) (e p) :=
    fun i ↦ differentiableAt_evalExt he hp hpU (z i)
  rw [fderiv_pi hd]
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  have hzi : ∀ i, chartDeriv e V p (X.presheaf.map (homOfLE hVU).op (z (ULift.down i))) v = 0 := by
    intro i
    exact (congrArg (fun f : E →L[ℂ] ℂ ↦ f v) (chartDeriv_res hp hVU hpV (z i.down))).trans
      (congrFun hv i.down)
  have hall := chartDeriv_apply_eq_zero he hp hpV _ hw v hzi
  have hspan := span_chartDeriv_eq_top he hp hV hpV
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ ↦ ?_
  have hle : Submodule.span ℂ (Set.range (chartDeriv e V p)) ≤
      LinearMap.ker ((ContinuousLinearMap.apply ℂ ℂ v).toLinearMap) := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact hall c
  rw [hspan] at hle
  exact hle (Submodule.mem_top (x := φ))

private theorem exists_chart_hasStrictFDerivAt [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] {n : ℕ}
    (hn : Nonempty X → (n : WithBot ℕ∞) = dimension X) (hreg : ∀ p : UnderlyingSpace ℂ X, p ∈
        regularPart ℂ X)
    (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ X ↘ Spec (.of ℂ))
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (p : UnderlyingSpace ℂ X) (hpU : ⊤ ≤ p.toHom ⁻¹ᵁ U) :
    ∃ (e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)))
      (f' : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ)), p ∈ e.source ∧ IsAlgebraicChart e ∧
      HasStrictFDerivAt (fun k i ↦ evalExt U (z i) (e.symm k)) (f' : _ →L[ℂ] _) (e p) := by
  obtain ⟨e, hp, he⟩ := exists_isAlgebraicChart_of_dimension_eq (hn ⟨p.toHom
      (IsLocalRing.closedPoint ℂ)⟩) p
    (hreg p)
  have hcd : ContDiffAt ℂ ω (fun k i ↦ evalExt U (z i) (e.symm k)) (e p) := by
    refine contDiffAt_pi.2 fun i ↦ ?_
    have ho : IsOpen (e.target ∩ e.symm ⁻¹' {q : UnderlyingSpace ℂ X | ⊤ ≤ q.toHom ⁻¹ᵁ U}) :=
      e.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage U)
    exact (he.contDiffOn_evalExt U (z i)).contDiffAt (ho.mem_nhds ⟨e.map_source hp,
      by simpa [e.left_inv hp] using hpU⟩)
  have hs := hcd.hasStrictFDerivAt (by simp)
  let f' := (LinearMap.linearEquivOfInjective _ (injective_fderiv he hp U z hz hpU)
    (by simp)).toContinuousLinearEquiv
  exact ⟨e, f', hp, he, hs⟩

variable (X) in
private abbrev toUnderlying :
    MMP.Analytic.ComplexPoints (X ↘ Spec (.of ℂ)) ≃ₜ UnderlyingSpace ℂ X :=
  MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace

private theorem eval_eq_evalExt (U : X.Opens) (a : Γ(X, U))
    (y : ComplexPoints (X ↘ Spec (.of ℂ))) (hy : y ∈ chart U) :
    ComplexPoints.eval U a ⟨y, hy⟩ = evalExt U a (toUnderlying X y) :=
  (evalExt_of_le _ (top_le_preimage_of_mem_chart ⟨y, hy⟩)).symm

private theorem isOpenEmbedding_coordinates [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] {n : ℕ}
    (hn : Nonempty X → (n : WithBot ℕ∞) = dimension X) (hreg : ∀ p : UnderlyingSpace ℂ X, p ∈
        regularPart ℂ X)
    (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ X ↘ Spec (.of ℂ))
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (x : ComplexPoints (X ↘ Spec (.of ℂ))) (hx : x ∈ chart U) :
    ∃ (W : Set (ComplexPoints (X ↘ Spec (.of ℂ)))) (hW : W ⊆ chart U),
        IsOpen W ∧ x ∈ W ∧
          IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) := by
  have hpU := top_le_preimage_of_mem_chart ⟨x, hx⟩
  obtain ⟨e, f', hp, he, hs⟩ := exists_chart_hasStrictFDerivAt hn hreg U z hz (toUnderlying X x) hpU
  let T := e.trans (hs.toOpenPartialHomeomorph _)
  have hT : ∀ q ∈ T.source, T q = fun i ↦ evalExt U (z i) q := by
    intro q hq
    simp only [T, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    rw [e.left_inv hq.1]
  let W : Set (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    toUnderlying X ⁻¹' (T.source ∩ {q | ⊤ ≤ q.toHom ⁻¹ᵁ U})
  have hW : W ⊆ chart U := fun y hy ↦ top_le_iff.1 hy.2
  have hWo : IsOpen W :=
    (T.open_source.inter (isOpen_setOf_le_preimage U)).preimage (toUnderlying X).continuous
  refine ⟨W, hW, hWo, ⟨⟨hp, ?_⟩, hpU⟩, ?_⟩
  · exact hs.mem_toOpenPartialHomeomorph_source
  have hfun : (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) =
      fun y : W ↦ T (toUnderlying X y.1) := by
    funext y
    rw [hT _ y.2.1]
    funext i
    exact eval_eq_evalExt U (z i) y.1 (hW y.2)
  rw [hfun]
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact T.continuousOn.comp_continuous ((toUnderlying X).continuous.comp continuous_subtype_val)
      (fun y ↦ y.2.1)
  · intro y y' h
    exact Subtype.ext ((toUnderlying X).injective (T.injOn y.2.1 y'.2.1 h))
  · intro S hS
    have h1 : IsOpen ((toUnderlying X) '' (Subtype.val '' S)) :=
      (toUnderlying X).isOpenMap _ (hWo.isOpenMap_subtype_val _ hS)
    have h2 := T.isOpen_image_of_subset_source h1 (by
      rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact y.2.1)
    rwa [Set.image_image, Set.image_image] at h2

private theorem exists_differentiableOn_coordinates [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] {n : ℕ}
    (hn : Nonempty X → (n : WithBot ℕ∞) = dimension X) (hreg : ∀ p : UnderlyingSpace ℂ X, p ∈
        regularPart ℂ X)
    (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ X ↘ Spec (.of ℂ))
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints (X ↘ Spec (.of ℂ)))) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hemb : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩))
    (U' : X.Opens) (f : Γ(X, U')) : ∃ G : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ G
        ((fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) '' {y | y.1 ∈ chart U'}) ∧
      ∀ (y : W) (hy : y.1 ∈ chart U'),
        ComplexPoints.eval U' f ⟨y.1, hy⟩ = G (fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩)
            := by
  set Z := fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩ with hZ
  rcases isEmpty_or_nonempty W with hE | hne
  · exact ⟨0, by simp [Set.image_eq_empty.2 (Set.eq_empty_of_isEmpty _)],
      fun y ↦ (IsEmpty.false y).elim⟩
  let G : (Fin n → ℂ) → ℂ := fun v ↦ evalExt U' f (toUnderlying X (Function.invFun Z v).1)
  have hinv : ∀ y : W, Function.invFun Z (Z y) = y :=
    Function.leftInverse_invFun hemb.injective
  refine ⟨G, ?_, fun y hy ↦ ?_⟩
  swap
  · change _ = evalExt U' f (toUnderlying X (Function.invFun Z (Z y)).1)
    rw [hinv]
    exact eval_eq_evalExt U' f y.1 hy
  rintro _ ⟨y, hy, rfl⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  have hqU := top_le_preimage_of_mem_chart ⟨y.1, hW y.2⟩
  have hqU' := top_le_preimage_of_mem_chart ⟨y.1, hy⟩
  obtain ⟨e, f', hq, he, hs⟩ :=
    exists_chart_hasStrictFDerivAt hn hreg U z hz (toUnderlying X y.1) hqU
  set Φ := fun k i ↦ evalExt U (z i) (e.symm k)
  set g := hs.localInverse Φ f' (e (toUnderlying X y.1))
  have hZΦ : ∀ y' : W, toUnderlying X y'.1 ∈ e.source → Z y' = Φ (e (toUnderlying X y'.1)) := by
    intro y' hy'
    funext i
    simp only [hZ, Φ, e.left_inv hy']
    exact eval_eq_evalExt U (z i) y'.1 (hW y'.2)
  have hZy : Z y = Φ (e (toUnderlying X y.1)) := hZΦ y hq
  have hN : IsOpen (e.source ∩ (toUnderlying X).symm ⁻¹' W) :=
    e.open_source.inter (hWo.preimage (toUnderlying X).symm.continuous)
  have hgZ : g (Z y) = e (toUnderlying X y.1) := by rw [hZy]; exact hs.localInverse_apply_image
  have hgc : ContinuousAt g (Z y) := by rw [hZy]; exact hs.localInverse_continuousAt
  have hcont : ContinuousAt (fun v ↦ e.symm (g v)) (Z y) := by
    refine ContinuousAt.comp (f := g) ?_ hgc
    rw [hgZ]; exact e.continuousAt_symm (e.map_source hq)
  have hev1 : ∀ᶠ v in 𝓝 (Z y), e.symm (g v) ∈ e.source ∩ (toUnderlying X).symm ⁻¹' W := by
    refine hcont.preimage_mem_nhds (hN.mem_nhds ?_)
    simp only [hgZ, e.left_inv hq]
    exact ⟨hq, by simpa using y.2⟩
  have hev2 : ∀ᶠ v in 𝓝 (Z y), g v ∈ e.target :=
    hgc.preimage_mem_nhds (e.open_target.mem_nhds (hgZ ▸ e.map_source hq))
  have hev3 : ∀ᶠ v in 𝓝 (Z y), Φ (g v) = v := by rw [hZy]; exact hs.eventually_right_inverse
  have heq : G =ᶠ[𝓝 (Z y)] fun v ↦ evalExt U' f (e.symm (g v)) := by
    filter_upwards [hev1, hev2, hev3] with v h1 h2 h3
    let y' : W := ⟨(toUnderlying X).symm (e.symm (g v)), h1.2⟩
    have hy'v : Z y' = v := by
      rw [hZΦ y' (by simpa [y'] using h1.1)]
      simpa [y', e.right_inv h2] using h3
    have : Function.invFun Z v = y' :=
      hemb.injective (by rw [Function.invFun_eq ⟨y', hy'v⟩, hy'v])
    simp only [G, this, y', Homeomorph.apply_symm_apply]
  refine heq.differentiableAt_iff.2 ?_
  have hd := differentiableAt_evalExt he hq hqU' f
  rw [← hgZ] at hd
  exact hd.comp (Z y) (by rw [hZy]; exact hs.to_localInverse.differentiableAt)

end ChartDerivatives

end MMP.Analytic.Proof_lem_mmp_analytic_etale_chart_atlas

namespace MMP.Analytic.ComplexPoints

open MMP.Analytic.Proof_lem_mmp_analytic_etale_chart_atlas in
/-- **Étale coordinates form a holomorphic atlas.** Let `X` be a smooth complex variety of
dimension `n`. Then

1. every point of `X^an` lies in `U(ℂ)` for some Zariski open `U` carrying étale coordinates
   `z : Fin n → Γ(X, U)`;
2. for étale coordinates `z` on `U` and `x ∈ U(ℂ)`, there is an open neighbourhood `W ⊆ U(ℂ)`
   of `x` in `X^an` on which `y ↦ (z_i(y))_i` is an open embedding into `ℂⁿ`;
3. on such a chart `W`, every regular function `f` on an open `U'` is, on `W ∩ U'(ℂ)`, a
   holomorphic function of the coordinates `z`.

In particular any two such charts differ by a holomorphic map with holomorphic inverse. -/
@[mmp "lem_mmp_analytic_etale_chart_atlas"]
public theorem etaleCoordinate_atlas {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX] :
    (∀ x : ComplexPoints sX, ∃ (U : X.Opens) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧ x ∈ chart U) ∧
    (∀ (U : X.Opens) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) →
      ∀ x ∈ chart (sX := sX) U, ∃ (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U),
        IsOpen W ∧ x ∈ W ∧
          IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) ∧
    (∀ (U : X.Opens) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) →
      ∀ (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U), IsOpen W →
        IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩) →
        ∀ (U' : X.Opens) (f : Γ(X, U')), ∃ G : (Fin n → ℂ) → ℂ,
          DifferentiableOn ℂ G
            ((fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩) '' {y | y.1 ∈ chart U'}) ∧
          ∀ (y : W) (hy : y.1 ∈ chart U'),
            eval U' f ⟨y.1, hy⟩ = G (fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType sX)
  haveI : QuasiCompact (X ↘ Spec (.of ℂ)) := inferInstanceAs (QuasiCompact sX)
  have hn : Nonempty X → (n : WithBot ℕ∞) = dimension X := fun _ ↦
    (topologicalKrullDim_eq_of_relativeDimension sX
      (SmoothOfRelativeDimension.relativeDimension n sX)).symm
  have hreg (p : MMP.UnderlyingSpace ℂ X) :
      p ∈ MMP.UnderlyingSpace.regularPart ℂ X :=
    (MMP.UnderlyingSpace.mem_regularPart_iff p).2
      ((((isRegular_tfae X).out 1 2).mp (isRegular_of_smooth_over_field sX) :
        IsLocallyNoetherian X ∧ ∀ q : X, IsRegularLocalRing (X.presheaf.stalk q)).2 _)
  exact ⟨exists_etale_coordinates sX, isOpenEmbedding_coordinates hn hreg,
    exists_differentiableOn_coordinates hn hreg⟩

end MMP.Analytic.ComplexPoints

end

/-!
## The density of a rational pluriform is intrinsic

Let `X` be a smooth complex variety of dimension `n`, `m > 0`, and `s` a rational section of
`ω_X^{⊗m}`. On each étale chart `W` the chart measure `|φ|^{2/m} dλ` of `s`
(`MMP.Analytic.ComplexPoints.pluriformChartMeasure`) is defined in terms of the coordinates. If
`w` is a second coordinate system with complex Jacobian `J` then the coefficient of `s` changes by
`(det J)^{-m}`, its density by `|det J|^{-2}`, and the real Jacobian of `w` is `|det J|^2`; so the
chart measures agree on overlaps and glue to a measure `μ_s` on `X^an`, independent of the
coordinates. Moreover `μ_{cs} = |c|^{2/m} μ_s` for `c ∈ ℂ`, and `μ_{g^*s} = g^*μ_s` for every
isomorphism `g` of smooth varieties.

### Main results

* `MMP.Analytic.ComplexPoints.pluriformChartMeasure_intrinsic`: the four statements above.
* `MMP.Analytic.ComplexPoints.map_realize_eq_restrict_of_isOpenImmersion`: for an open immersion
  `j : U ⟶ X`, `μ_{j^*s}` is the restriction of `μ_s` to `U^an ⊆ X^an`.

### Implementation notes

* The glued measure is characterised as the unique measure on `X^an` whose restriction to every
  chart `W` is the chart measure on `W`; homogeneity and naturality are stated for measures with
  this property, so that they hold for `μ_s` without naming a choice of it.
* `g^*μ_s` is expressed by push-forward: for an isomorphism `g : Y ⟶ X`, with `Y` a `ℂ`-scheme
  through `g ≫ s_X`, the push-forward of `μ_{g^*s}` along the realization
  `MMP.Analytic.ComplexPoints.realize g` is `μ_s`; as the realization is a homeomorphism this is
  equivalent to `μ_{g^*s}` being the pull-back of `μ_s`. The pull-back of forms is
  `MMP.Mori.pullbackRationalPluriForms`.
* The measurable structures on `X^an` and `Y^an` are their Borel structures.

### References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory MMP.Analytic MMP.Analytic.ComplexPoints

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [MeasurableSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m)

namespace MMP.Analytic.Proof_lem_mmp_analytic_pluriform_density_intrinsic

section Evaluation

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

private lemma eval_mul (V : X.Opens) (f g : Γ(X, V)) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (f * g) y = ComplexPoints.eval V f y * ComplexPoints.eval V g y := by
  simp [ComplexPoints.eval]

private lemma eval_add (V : X.Opens) (f g : Γ(X, V)) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (f + g) y = ComplexPoints.eval V f y + ComplexPoints.eval V g y := by
  simp [ComplexPoints.eval]

private lemma eval_pow (V : X.Opens) (f : Γ(X, V)) (k : ℕ) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (f ^ k) y = ComplexPoints.eval V f y ^ k := by
  simp [ComplexPoints.eval]

/-- A function pulled back from the base `Spec ℂ` evaluates to the corresponding constant. -/
private lemma eval_appLE (V : X.Opens) (e : V ≤ sX ⁻¹ᵁ ⊤) (a : Γ(Spec (.of ℂ), ⊤))
    (y : chart (sX := sX) V) :
    ComplexPoints.eval V (sX.appLE ⊤ V e a) y = (Scheme.ΓSpecIso (.of ℂ)).hom a := by
  have h2 : y.1.hom ≫ sX = 𝟙 _ := y.1.2
  have key : sX.appLE ⊤ V e ≫ y.1.hom.appLE V ⊤ y.2.ge = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have aux : ∀ (f : Spec (.of ℂ) ⟶ Spec (.of ℂ)), f = 𝟙 _ → ∀ e, f.appLE ⊤ ⊤ e = 𝟙 _ := by
      rintro _ rfl e; simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact (Spec (.of ℂ)).presheaf.map_id _
    exact aux _ h2 _
  have := congrArg (fun φ => (Scheme.ΓSpecIso (.of ℂ)).hom.hom (φ.hom a)) key
  exact this

/-- A point of `Spec ℂ` mapped into `U` by a point of `chart U`. -/
private lemma mem_of_mem_chart {U : X.Opens} {y : ComplexPoints sX} (hy : y ∈ chart U)
    (q : Spec (.of ℂ)) : y.hom.base q ∈ U := by
  have : q ∈ y.hom ⁻¹ᵁ U := by
    change y.hom ⁻¹ᵁ U = ⊤ at hy
    rw [hy]; trivial
  exact this

private lemma mem_chart_of_mem {U : X.Opens} {y : ComplexPoints sX} (q : Spec (.of ℂ))
    (hq : y.hom.base q ∈ U) : y ∈ chart U := by
  change y.hom ⁻¹ᵁ U = ⊤
  ext q'
  rw [Subsingleton.elim q' q]
  simpa using hq

private lemma chart_mono {U V : X.Opens} (h : V ≤ U) : chart (sX := sX) V ⊆ chart U :=
  fun y hy ↦ top_le_iff.1 ((top_le_iff.2 hy).trans (Scheme.Hom.preimage_mono _ h))

end Evaluation

section Constants

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- The constant section `c` of `𝒪_X` over `V`. -/
private noncomputable def constSec (V : X.Opens) (c : ℂ) : Γ(X, V) :=
  X.presheaf.map (homOfLE le_top).op (sX.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c))

private lemma eval_constSec (V : X.Opens) (c : ℂ) (y : chart (sX := sX) V) :
    ComplexPoints.eval V (constSec sX V c) y = c :=
  (eval_appLE sX V le_top _ y).trans (by simp)

private lemma germ_constSec_mul [IsIntegral X] (V : X.Opens) (c : ℂ) (g : Γ(X, V))
    (hg : genericPoint X ∈ V) :
    X.presheaf.germ V (genericPoint X) hg (constSec sX V c * g) =
      @algebraMap ℂ X.functionField _ _ (MMP.Mori.functionFieldAlgebra sX) c *
        X.presheaf.germ V (genericPoint X) hg g := by
  rw [map_mul]
  congr 1
  unfold constSec
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

private lemma pluriformCoeff_smul [IsIntegral X] {n m : ℕ} (s : MMP.Mori.RationalPluriForms sX n m)
    (a : X.functionField) (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U)) :
    pluriformCoeff sX (a • s : MMP.Mori.RationalPluriForms sX n m) U z =
      a * pluriformCoeff sX s U z := by
  unfold pluriformCoeff
  dsimp only
  split_ifs with h
  · letI := MMP.Mori.functionFieldAlgebra sX
    exact (DFunLike.congr_fun (LinearEquiv.map_smul (MMP.Mori.ZTensorPower.basis _ _).repr a
      (show MMP.Mori.ZTensorPower X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄ℂ]) (m :
          ℤ) from s)) ()).trans (Finsupp.smul_apply _ _ _)
  · simp

private lemma ofReal_norm_rpow_mul (c w : ℂ) (p : ℝ) :
    ENNReal.ofReal (‖c * w‖ ^ p) = ENNReal.ofReal (‖c‖ ^ p) * ENNReal.ofReal (‖w‖ ^ p) := by
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    ENNReal.ofReal_mul (by positivity)]

private lemma pluriformDensity_algebraMap_mul [IsIntegral X] (m : ℕ) (hm : 0 < m) (c : ℂ)
    (φ : X.functionField) :
    pluriformDensity sX m (@algebraMap ℂ X.functionField _ _ (MMP.Mori.functionFieldAlgebra sX) c
        * φ) =
      fun y ↦ ENNReal.ofReal (‖c‖ ^ (2 / m : ℝ)) * pluriformDensity sX m φ y := by
  letI := MMP.Mori.functionFieldAlgebra sX
  funext y
  unfold pluriformDensity
  by_cases hc : c = 0
  · subst hc
    simp only [map_zero, zero_mul, norm_zero, Real.zero_rpow (by positivity : (2 / m : ℝ) ≠ 0),
      ENNReal.ofReal_zero]
    refine le_antisymm ?_ zero_le
    refine iSup_le fun V ↦ iSup_le fun g ↦ iSup_le fun hy ↦ iSup_le fun hg ↦ iSup_le fun hgφ ↦ ?_
    have : g = 0 := by
      haveI : Nonempty V := ⟨⟨_, hg⟩⟩
      exact germ_injective_of_isIntegral X _ hg (hgφ.trans (map_zero _).symm)
    subst this
    simp [ComplexPoints.eval, Real.zero_rpow (by positivity : (2 / m : ℝ) ≠ 0)]
  · simp only [ENNReal.mul_iSup]
    apply le_antisymm
    · refine iSup_le fun V ↦ iSup_le fun g ↦ iSup_le fun hy ↦ iSup_le fun hg ↦ iSup_le fun hgφ ↦ ?_
      refine le_iSup_of_le V <| le_iSup_of_le (constSec sX V c⁻¹ * g) <| le_iSup_of_le hy <|
        le_iSup_of_le hg <| le_iSup_of_le ?_ (le_of_eq ?_)
      · rw [germ_constSec_mul, hgφ, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
      · rw [eval_mul, eval_constSec, ← ofReal_norm_rpow_mul _ _ _, ← mul_assoc,
          mul_inv_cancel₀ hc, one_mul]
    · refine iSup_le fun V ↦ iSup_le fun g ↦ iSup_le fun hy ↦ iSup_le fun hg ↦ iSup_le fun hgφ ↦ ?_
      refine le_iSup_of_le V <| le_iSup_of_le (constSec sX V c * g) <| le_iSup_of_le hy <|
        le_iSup_of_le hg <| le_iSup_of_le ?_ (le_of_eq ?_)
      · rw [germ_constSec_mul, hgφ]
      · rw [eval_mul, eval_constSec, ← ofReal_norm_rpow_mul _ _ _]

end Constants

section Lindelof

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- The `ℂ`-points of an affine open are Lindelöf: their topology is coarser than the one induced
by the values of finitely many algebra generators, which embeds them in some `ℂ^N`. -/
private lemma isLindelof_chart [LocallyOfFiniteType sX] (U : X.affineOpens) :
    @IsLindelof _ (chartTopology (sX := sX) (U : X.Opens)) Set.univ := by
  have e : (U : X.Opens) ≤ sX ⁻¹ᵁ ⊤ := by simp
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType sX ‹_›
    ⟨⊤, isAffineOpen_top (Spec (.of ℂ))⟩ U e
  letI := (sX.appLE ⊤ (U : X.Opens) e).hom.toAlgebra
  obtain ⟨t, ht⟩ := (hft : Algebra.FiniteType _ _).out
  let Φ : chart (sX := sX) (U : X.Opens) → (t → ℂ) := fun y i ↦ ComplexPoints.eval _ i.1 y
  letI T : TopologicalSpace (chart (sX := sX) (U : X.Opens)) := TopologicalSpace.induced Φ
      inferInstance
  have hT : ∀ f, Continuous (ComplexPoints.eval (sX := sX) (U : X.Opens) f) := by
    intro f
    have hf : f ∈ (⊤ : Subalgebra Γ(Spec (.of ℂ), ⊤) Γ(X, (U : X.Opens))) := trivial
    rw [← ht] at hf
    induction hf using Algebra.adjoin_induction with
    | mem x hx =>
      exact (continuous_apply (A := fun _ : t ↦ ℂ) (⟨x, hx⟩ : t)).comp
        (continuous_induced_dom (f := Φ))
    | algebraMap a =>
      have : ComplexPoints.eval (sX := sX) (U : X.Opens) (algebraMap _ _ a) =
          fun _ ↦ (Scheme.ΓSpecIso (.of ℂ)).hom a := funext (eval_appLE sX _ e a)
      rw [this]; exact continuous_const
    | add x y _ _ hx hy =>
      have : ComplexPoints.eval (sX := sX) (U : X.Opens) (x + y) =
          fun p ↦ ComplexPoints.eval _ x p + ComplexPoints.eval _ y p := funext (eval_add sX _ x y)
      rw [this]; exact hx.add hy
    | mul x y _ _ hx hy =>
      have : ComplexPoints.eval (sX := sX) (U : X.Opens) (x * y) =
          fun p ↦ ComplexPoints.eval _ x p * ComplexPoints.eval _ y p := funext (eval_mul sX _ x y)
      rw [this]; exact hx.mul hy
  have hle : T ≤ chartTopology (sX := sX) (U : X.Opens) :=
    le_iInf fun f ↦ continuous_iff_le_induced.1 (hT f)
  haveI : SecondCountableTopology (chart (sX := sX) (U : X.Opens)) :=
    Topology.IsInducing.secondCountableTopology (f := Φ) ⟨rfl⟩
  have := @IsLindelof.image _ _ T (chartTopology (sX := sX) (U : X.Opens)) _ _
    isLindelof_univ (continuous_id_of_le hle)
  rwa [Set.image_id] at this

/-- `X^an` is Lindelöf for `X` quasi-compact and locally of finite type over `ℂ`. -/
private lemma isLindelof_univ_complexPoints [LocallyOfFiniteType sX] [QuasiCompact sX] :
    IsLindelof (Set.univ : Set (ComplexPoints sX)) := by
  have hX : IsCompact (Set.univ : Set X) := by
    simpa using QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U : Set X) := fun x _ ↦ by
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨s, hs⟩ := hX.elim_finite_subcover _ (fun U : X.affineOpens ↦ U.1.isOpen) hcov
  have q : Spec (.of ℂ) := Classical.arbitrary _
  have hsub : (Set.univ : Set (ComplexPoints sX)) ⊆
      ⋃ U ∈ (s : Set X.affineOpens), Subtype.val '' (Set.univ : Set (chart (sX := sX) (U :
          X.Opens))) := by
    intro y _
    obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (y.hom.base q)))
    exact Set.mem_iUnion₂.2 ⟨U, hU, ⟨y, mem_chart_of_mem sX q hyU⟩, trivial, rfl⟩
  refine IsLindelof.of_isClosed_subset ?_ isClosed_univ hsub
  refine s.finite_toSet.isLindelof_biUnion fun U _ ↦ ?_
  exact @IsLindelof.image _ _ (chartTopology (sX := sX) (U : X.Opens)) _ _ _
    (isLindelof_chart sX U) (continuous_chart_val U)

end Lindelof

section Charts

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (n : ℕ)

/-- An étale chart of `X^an`: étale coordinates `z` on a Zariski open `U` together with an open
`W ⊆ U(ℂ)` on which `z` is an open embedding into `ℂⁿ`. -/
private structure EtaleChart where
  U : X.Opens
  ne : Nonempty U
  z : Fin n → Γ(X, U)
  hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
    (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))
  W : Set (ComplexPoints sX)
  hW : W ⊆ chart U
  hWo : IsOpen W
  hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)

end Charts

section Overlap

/-- If `R₀[w] → Γ(X, V)` is étale, the differentials `dw_j` span `Ω_{Γ(X, V)/ℂ}`. -/
private theorem D_mem_span_of_etale {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (V : X.Opens)
    {ι : Type} (w : ι → Γ(X, V)) (hφ : (MvPolynomial.eval₂Hom (sX.appLE ⊤ V le_top).hom w).Etale)
    (b : Γ(X, V)) :
    letI := MMP.Mori.sectionAlgebra sX V
    KaehlerDifferential.D ℂ Γ(X, V) b ∈
      Submodule.span Γ(X, V) (Set.range fun j ↦ KaehlerDifferential.D ℂ Γ(X, V) (w j)) := by
  letI := MMP.Mori.sectionAlgebra sX V
  set φ := MvPolynomial.eval₂Hom (sX.appLE ⊤ V le_top).hom w
  set N := Submodule.span Γ(X, V) (Set.range fun j ↦ KaehlerDifferential.D ℂ Γ(X, V) (w j))
  letI : Algebra (MvPolynomial ι Γ(Spec (.of ℂ), ⊤)) Γ(X, V) := φ.toAlgebra
  have hE : Algebra.Etale (MvPolynomial ι Γ(Spec (.of ℂ), ⊤)) Γ(X, V) := hφ
  have : IsScalarTower (MvPolynomial ι Γ(Spec (.of ℂ), ⊤)) Γ(X, V) (Ω[Γ(X, V)⁄ℂ] ⧸ N) :=
      inferInstance
  let D₀ : Γ(X, V) → Ω[Γ(X, V)⁄ℂ] ⧸ N := fun a ↦ N.mkQ (KaehlerDifferential.D ℂ Γ(X, V) a)
  have hleib : ∀ a c, D₀ (a * c) = a • D₀ c + c • D₀ a := fun a c ↦ by
    simp only [D₀, Derivation.leibniz, map_add, map_smul]
  have hadd : ∀ a c, D₀ (a + c) = D₀ a + D₀ c := fun a c ↦ by simp [D₀]
  have hφ0 : ∀ r, D₀ (φ r) = 0 := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a =>
      have : φ (MvPolynomial.C a) = algebraMap ℂ Γ(X, V) ((Scheme.ΓSpecIso (.of ℂ)).hom a) := by
        simp only [φ, MvPolynomial.eval₂Hom_C]
        change _ = ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appLE ⊤ V _) ((Scheme.ΓSpecIso (.of ℂ)).hom
            a)
        rw [CommRingCat.comp_apply, Iso.hom_inv_id_apply]
      simp [D₀, this]
    | add p q hp hq => rw [map_add, hadd, hp, hq, add_zero]
    | mul_X p j hp =>
      have hw : D₀ (w j) = 0 := (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨j, rfl⟩)
      rw [map_mul, hleib, hp, smul_zero, add_zero, MvPolynomial.eval₂Hom_X', hw, smul_zero]
  let D' : Derivation (MvPolynomial ι Γ(Spec (.of ℂ), ⊤)) Γ(X, V) (Ω[Γ(X, V)⁄ℂ] ⧸ N) :=
    Derivation.mk'
      { toFun := D₀
        map_add' := hadd
        map_smul' := fun r a ↦ by
          change D₀ (φ r * a) = φ r • D₀ a
          rw [hleib, hφ0, smul_zero, add_zero] } hleib
  have h0 : D' b = 0 := by
    rw [← D'.liftKaehlerDifferential_comp_D,
      Subsingleton.elim (KaehlerDifferential.D (MvPolynomial ι Γ(Spec (.of ℂ), ⊤)) Γ(X, V) b) 0,
      map_zero]
  exact (Submodule.Quotient.mk_eq_zero N).1 h0

private lemma alternatingMap_eq_det_smul {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    {n : ℕ} (g : (Fin n → R) [⋀^Fin n]→ₗ[R] N) (v : Fin n → Fin n → R) :
    g v = (Matrix.of v).det • g (Pi.basisFun R (Fin n)) := by
  set e := Pi.basisFun R (Fin n)
  have hg : g = e.det.smulRight (g e) := by
    refine e.ext_alternating fun σ hσ ↦ ?_
    let p := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ)
    have h1 : (fun i ↦ e (σ i)) = (⇑e) ∘ ⇑p := rfl
    rw [AlternatingMap.smulRight_apply, h1, AlternatingMap.map_perm, AlternatingMap.map_perm,
      e.det_self, Units.smul_def, Units.smul_def, smul_assoc, one_smul]
  conv_lhs => rw [hg]
  rw [AlternatingMap.smulRight_apply, e.det_apply]
  congr 1
  rw [← Matrix.det_transpose]
  congr 1

private lemma ιMulti_sum_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (u : Fin n → M) (a : Matrix (Fin n) (Fin n) R) :
    exteriorPower.ιMulti R n (fun i ↦ ∑ j, a i j • u j) = a.det • exteriorPower.ιMulti R n u := by
  let g := (exteriorPower.ιMulti R n (M := M)).compLinearMap (Fintype.linearCombination R u)
  have h := alternatingMap_eq_det_smul g (fun i ↦ a i)
  have h1 : g (fun i ↦ a i) = exteriorPower.ιMulti R n (fun i ↦ ∑ j, a i j • u j) := by
    simp [g, Fintype.linearCombination_apply]
  have h2 : g (Pi.basisFun R (Fin n)) = exteriorPower.ιMulti R n u := by
    simp [g, Fintype.linearCombination_apply_single]
  rw [← h1, h, h2]
  rfl

private lemma topForms_eq_det_smul {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X]
    (V : X.Opens) [Nonempty V] {n : ℕ} (w w' : Fin n → Γ(X, V))
    (a : Matrix (Fin n) (Fin n) Γ(X, V))
    (ha : letI := MMP.Mori.sectionAlgebra sX V
      ∀ i, KaehlerDifferential.D ℂ Γ(X, V) (w' i) = ∑ j, a i j • KaehlerDifferential.D ℂ Γ(X, V)
          (w j)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    exteriorPower.ιMulti X.functionField n
        (fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField V (w' i))) =
      X.germToFunctionField V a.det • exteriorPower.ιMulti X.functionField n
        (fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField V (w i))) := by
  letI := MMP.Mori.sectionAlgebra sX V
  letI := MMP.Mori.functionFieldAlgebra sX
  haveI := MMP.Mori.isScalarTower_section_functionField sX V
  have h0 : exteriorPower.ιMulti Γ(X, V) n (fun i ↦ KaehlerDifferential.D ℂ Γ(X, V) (w' i)) =
      a.det • exteriorPower.ιMulti Γ(X, V) n (fun j ↦ KaehlerDifferential.D ℂ Γ(X, V) (w j)) := by
    rw [← ιMulti_sum_smul]
    exact congrArg _ (funext ha)
  have h1 := congrArg (MMP.Mori.topFormsMap ℂ Γ(X, V) X.functionField n) h0
  rw [map_smul, MMP.Mori.topFormsMap_ιMulti, MMP.Mori.topFormsMap_ιMulti, ← algebraMap_smul
      X.functionField] at h1
  simp only [KaehlerDifferential.map_D] at h1
  exact h1

section Density

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

private lemma eval_res {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : ComplexPoints sX)
    (hy : y ∈ chart V) :
    ComplexPoints.eval V (X.presheaf.map (homOfLE h).op f) ⟨y, hy⟩ =
      ComplexPoints.eval U f ⟨y, chart_mono sX h hy⟩ := by
  simp only [ComplexPoints.eval]
  congr 1
  change (X.presheaf.map (homOfLE h).op ≫ y.hom.appLE V ⊤ _) f = _
  rw [Scheme.Hom.map_appLE]

private lemma mem_chart_inf {V V' : X.Opens} {y : ComplexPoints sX} (hy : y ∈ chart V)
    (hy' : y ∈ chart V') : y ∈ chart (V ⊓ V') := by
  change y.hom ⁻¹ᵁ (V ⊓ V') = ⊤
  have h1 : y.hom ⁻¹ᵁ V = ⊤ := hy
  have h2 : y.hom ⁻¹ᵁ V' = ⊤ := hy'
  rw [Scheme.Hom.preimage_inf, h1, h2, top_inf_eq]

variable [IsIntegral X]

/-- The density at a point where the rational function has a regular representative. -/
private lemma pluriformDensity_eq (m : ℕ) (φ : X.functionField) (y : ComplexPoints sX)
    (V : X.Opens) (g : Γ(X, V)) (hy : y ∈ chart V) (hg : genericPoint X ∈ V)
    (hgφ : X.presheaf.germ V (genericPoint X) hg g = φ) :
    pluriformDensity sX m φ y = ENNReal.ofReal (‖ComplexPoints.eval V g ⟨y, hy⟩‖ ^ (2 / m : ℝ)) :=
        by
  refine le_antisymm ?_ (le_iSup_of_le V <| le_iSup_of_le g <| le_iSup_of_le hy <|
    le_iSup_of_le hg <| le_iSup_of_le hgφ le_rfl)
  refine iSup_le fun V₂ ↦ iSup_le fun g₂ ↦ iSup_le fun hy₂ ↦ iSup_le fun hg₂ ↦ iSup_le fun hgφ₂ ↦ ?_
  have hη : genericPoint X ∈ V ⊓ V₂ := ⟨hg, hg₂⟩
  haveI : Nonempty (V ⊓ V₂ : X.Opens) := ⟨⟨_, hη⟩⟩
  have hres : X.presheaf.map (homOfLE (inf_le_left : V ⊓ V₂ ≤ V)).op g =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ V₂ ≤ V₂)).op g₂ := by
    apply germ_injective_of_isIntegral X _ hη
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hgφ, hgφ₂]
  have hyy := mem_chart_inf sX hy hy₂
  have e1 := eval_res sX (inf_le_left : V ⊓ V₂ ≤ V) g y hyy
  have e2 := eval_res sX (inf_le_right : V ⊓ V₂ ≤ V₂) g₂ y hyy
  rw [hres] at e1
  rw [← e2, e1]

private lemma pluriformDensity_eq_zero (m : ℕ) (φ : X.functionField) (y : ComplexPoints sX)
    (h : ¬∃ (V : X.Opens) (g : Γ(X, V)) (_ : y ∈ chart V) (hg : genericPoint X ∈ V),
      X.presheaf.germ V (genericPoint X) hg g = φ) :
    pluriformDensity sX m φ y = 0 := by
  refine le_antisymm (iSup_le fun V ↦ iSup_le fun g ↦ iSup_le fun hy ↦ iSup_le fun hg ↦
    iSup_le fun hgφ ↦ ?_) zero_le
  exact (h ⟨V, g, hy, hg, hgφ⟩).elim

/-- If `φ = φ' c^m` and `φ' = φ c'^m` with `c, c'` regular at `y`, then
`|φ(y)|^{2/m} = |φ'(y)|^{2/m} |c(y)|^2`. -/
private lemma pluriformDensity_mul_pow (m : ℕ) (hm : 0 < m) (φ φ' : X.functionField)
    (V : X.Opens) (hV : genericPoint X ∈ V) (c c' : Γ(X, V))
    (h1 : φ = φ' * X.presheaf.germ V (genericPoint X) hV c ^ m)
    (h2 : φ' = φ * X.presheaf.germ V (genericPoint X) hV c' ^ m)
    (y : ComplexPoints sX) (hy : y ∈ chart V) :
    pluriformDensity sX m φ y = pluriformDensity sX m φ' y *
      ENNReal.ofReal (‖ComplexPoints.eval V c ⟨y, hy⟩‖ ^ 2) := by
  have hp : (0 : ℝ) ≤ 2 / m := by positivity
  by_cases h' : ∃ (V₂ : X.Opens) (g : Γ(X, V₂)) (_ : y ∈ chart V₂) (hg : genericPoint X ∈ V₂),
      X.presheaf.germ V₂ (genericPoint X) hg g = φ'
  · obtain ⟨V₂, g₂, hy₂, hg₂, hgφ₂⟩ := h'
    have hη : genericPoint X ∈ V₂ ⊓ V := ⟨hg₂, hV⟩
    let g : Γ(X, V₂ ⊓ V) := X.presheaf.map (homOfLE (inf_le_left : V₂ ⊓ V ≤ V₂)).op g₂ *
      X.presheaf.map (homOfLE (inf_le_right : V₂ ⊓ V ≤ V)).op c ^ m
    have hyy := mem_chart_inf sX hy₂ hy
    have hgφ : X.presheaf.germ (V₂ ⊓ V) (genericPoint X) hη g = φ := by
      simp only [g, map_mul, map_pow, TopCat.Presheaf.germ_res_apply, hgφ₂, h1]
    rw [pluriformDensity_eq sX m φ y _ g hyy hη hgφ, pluriformDensity_eq sX m φ' y _ g₂ hy₂ hg₂
        hgφ₂]
    simp only [g, eval_mul, eval_pow, eval_res, norm_mul, norm_pow]
    rw [Real.mul_rpow (norm_nonneg _) (by positivity), ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      show (m : ℝ) * (2 / m) = ((2 : ℕ) : ℝ) by field_simp; norm_num, Real.rpow_natCast]
  · rw [pluriformDensity_eq_zero sX m φ' y h', zero_mul]
    refine pluriformDensity_eq_zero sX m φ y fun ⟨V₂, g₂, hy₂, hg₂, hgφ₂⟩ ↦ h' ?_
    have hη : genericPoint X ∈ V₂ ⊓ V := ⟨hg₂, hV⟩
    refine ⟨V₂ ⊓ V, X.presheaf.map (homOfLE (inf_le_left : V₂ ⊓ V ≤ V₂)).op g₂ *
      X.presheaf.map (homOfLE (inf_le_right : V₂ ⊓ V ≤ V)).op c' ^ m,
      mem_chart_inf sX hy₂ hy, hη, ?_⟩
    simp only [map_mul, map_pow, TopCat.Presheaf.germ_res_apply, hgφ₂, h2]

end Density

section Coeff

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X]

private lemma germToFunctionField_res {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (f : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op f) = X.germToFunctionField U f :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

private lemma generator_of_smul {K L : Type*} [Field K] [AddCommGroup L] [Module K L] {ω ω' : L}
    {c c' : K} (h1 : ω' = c • ω) (h2 : ω = c' • ω')
    (h : Submodule.span K {ω} = ⊤ ∧ ω ≠ 0) : Submodule.span K {ω'} = ⊤ ∧ ω' ≠ 0 := by
  have hω' : ω' ≠ 0 := fun h0 ↦ h.2 (by rw [h2, h0, smul_zero])
  have hc : c ≠ 0 := by rintro rfl; exact hω' (by rw [h1, zero_smul])
  refine ⟨?_, hω'⟩
  rw [h1, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc), h.1]

private lemma pluriformCoeff_rel {n m : ℕ} (s : MMP.Mori.RationalPluriForms sX n m)
    (U U' : X.Opens) [Nonempty U] [Nonempty U'] (z : Fin n → Γ(X, U)) (z' : Fin n → Γ(X, U'))
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') (hη : genericPoint X ∈ V)
    (a a' : Matrix (Fin n) (Fin n) Γ(X, V))
    (ha : letI := MMP.Mori.sectionAlgebra sX V
      ∀ i, KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU').op (z' i)) =
        ∑ j, a i j • KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU).op (z j)))
    (ha' : letI := MMP.Mori.sectionAlgebra sX V
      ∀ i, KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU).op (z i)) =
        ∑ j, a' i j • KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU').op (z' j))) :
    pluriformCoeff sX s U z =
        pluriformCoeff sX s U' z' * X.presheaf.germ V (genericPoint X) hη a.det ^ m ∧
      pluriformCoeff sX s U' z' =
        pluriformCoeff sX s U z * X.presheaf.germ V (genericPoint X) hη a'.det ^ m := by
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  letI := MMP.Mori.functionFieldAlgebra sX
  have r1 := topForms_eq_det_smul sX V _ _ a ha
  have r2 := topForms_eq_det_smul sX V _ _ a' ha'
  simp only [germToFunctionField_res] at r1 r2
  set c := X.germToFunctionField V a.det
  set c' := X.germToFunctionField V a'.det
  unfold pluriformCoeff
  dsimp only
  split_ifs with h h' h'
  · have e1 := MMP.Mori.ZTensorPower.basis_repr_of_eq_smul
      (b := MMP.Mori.basisOfSpanSingleton h.1 h.2) (b' := MMP.Mori.basisOfSpanSingleton h'.1 h'.2)
      (c := c) (by simpa using r1) (m : ℤ) s
    have e2 := MMP.Mori.ZTensorPower.basis_repr_of_eq_smul
      (b := MMP.Mori.basisOfSpanSingleton h'.1 h'.2) (b' := MMP.Mori.basisOfSpanSingleton h.1 h.2)
      (c := c') (by simpa using r2) (m : ℤ) s
    have hc0 : c ≠ 0 := by rintro h0; rw [h0, zero_smul] at r1; exact h'.2 r1
    have hc0' : c' ≠ 0 := by rintro h0; rw [h0, zero_smul] at r2; exact h.2 r2
    rw [zpow_natCast] at e1 e2
    have hm1 : c ^ m ≠ 0 := pow_ne_zero _ hc0
    have hm2 : c' ^ m ≠ 0 := pow_ne_zero _ hc0'
    constructor
    · rw [e1, mul_comm, ← mul_assoc, mul_inv_cancel₀ hm1, one_mul]
    · rw [e2, mul_comm, ← mul_assoc, mul_inv_cancel₀ hm2, one_mul]
  · exact (h' (generator_of_smul r1 r2 h)).elim
  · exact (h (generator_of_smul r2 r1 h')).elim
  · simp

end Coeff

section Analytic

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

private lemma isOpen_chart (V : X.Opens) : IsOpen (chart (sX := sX) V) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  exact MMP.Analytic.InvertibleModule.isOpen_chart V

private lemma eval_algebraMap (V : X.Opens) (c : ℂ) (y : chart (sX := sX) V) :
    letI := MMP.Mori.sectionAlgebra sX V
    ComplexPoints.eval V (algebraMap ℂ Γ(X, V) c) y = c := by
  letI := MMP.Mori.sectionAlgebra sX V
  change ComplexPoints.eval V (sX.appLE ⊤ V _ ((Scheme.ΓSpecIso (.of ℂ)).inv c)) y = c
  rw [eval_appLE]
  simp

/-- Evaluation at a point of `V(ℂ)` as a ring homomorphism. -/
private noncomputable def evalRingHom (V : X.Opens) (y : chart (sX := sX) V) : Γ(X, V) →+* ℂ :=
  (y.1.hom.appLE V ⊤ y.2.ge ≫ (Scheme.ΓSpecIso (.of ℂ)).hom).hom

private lemma evalRingHom_apply (V : X.Opens) (y : chart (sX := sX) V) (f : Γ(X, V)) :
    evalRingHom sX V y f = ComplexPoints.eval V f y := rfl

variable {n : ℕ} {W : Set (ComplexPoints sX)}

open Classical in
/-- A section `f` on `V`, read through the coordinates `Z` of the chart `W`. -/
private noncomputable def chartPull (Z : W → (Fin n → ℂ)) (V : X.Opens) (f : Γ(X, V)) :
    (Fin n → ℂ) → ℂ := fun x ↦
  if h : ∃ y : W, Z y = x ∧ y.1 ∈ chart V then
    ComplexPoints.eval V f ⟨h.choose.1, h.choose_spec.2⟩ else 0

private lemma chartPull_apply {Z : W → (Fin n → ℂ)} (hZ : Function.Injective Z) (V : X.Opens)
    (f : Γ(X, V)) (y : W) (hy : y.1 ∈ chart V) :
    chartPull sX Z V f (Z y) = ComplexPoints.eval V f ⟨y.1, hy⟩ := by
  have h : ∃ y' : W, Z y' = Z y ∧ y'.1 ∈ chart V := ⟨y, rfl, hy⟩
  have e : h.choose = y := hZ h.choose_spec.1
  simp only [chartPull, dite_eq_left h]
  congr 2
  exact congrArg Subtype.val e

private lemma eventually_mem_chart {Z : W → (Fin n → ℂ)} (hZ : IsOpenEmbedding Z) (V : X.Opens)
    (y : W) (hy : y.1 ∈ chart V) :
    ∀ᶠ x in 𝓝 (Z y), ∃ y' : W, Z y' = x ∧ y'.1 ∈ chart V := by
  have ho : IsOpen (Z '' {y' : W | y'.1 ∈ chart V}) :=
    hZ.isOpenMap _ ((isOpen_chart sX V).preimage continuous_subtype_val)
  filter_upwards [ho.mem_nhds ⟨y, hy, rfl⟩] with x ⟨y', hy', hx⟩ using ⟨y', hx, hy'⟩

/-- Pointwise identities between sections give eventual identities of their pull-backs. -/
private lemma eventually_chartPull {Z : W → (Fin n → ℂ)} (hZ : IsOpenEmbedding Z) (V : X.Opens)
    (y : W) (hy : y.1 ∈ chart V) (P : (Fin n → ℂ) → Prop)
    (hP : ∀ (y' : W) (hy' : y'.1 ∈ chart V), P (Z y')) : ∀ᶠ x in 𝓝 (Z y), P x := by
  filter_upwards [eventually_mem_chart sX hZ V y hy] with x ⟨y', hx, hy'⟩
  exact hx ▸ hP y' hy'

private lemma differentiableAt_chartPull {Z : W → (Fin n → ℂ)} (hZ : IsOpenEmbedding Z)
    (V : X.Opens) (f : Γ(X, V))
    (hG : ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (Z '' {y | y.1 ∈ chart V}) ∧
      ∀ (y : W) (hy : y.1 ∈ chart V), ComplexPoints.eval V f ⟨y.1, hy⟩ = G (Z y))
    (y : W) (hy : y.1 ∈ chart V) : DifferentiableAt ℂ (chartPull sX Z V f) (Z y) := by
  obtain ⟨G, hGd, hGe⟩ := hG
  have ho : IsOpen (Z '' {y' : W | y'.1 ∈ chart V}) :=
    hZ.isOpenMap _ ((isOpen_chart sX V).preimage continuous_subtype_val)
  have hGa : DifferentiableAt ℂ G (Z y) := hGd.differentiableAt (ho.mem_nhds ⟨y, hy, rfl⟩)
  refine hGa.congr_of_eventuallyEq ?_
  exact eventually_chartPull sX hZ V y hy _ fun y' hy' ↦ by
    rw [chartPull_apply sX hZ.injective V f y' hy', hGe y' hy']

/-- The analytic differential at `y` of the chart reading of sections is a derivation, so it
respects every relation among Kähler differentials. -/
private lemma fderiv_chartPull_eq_sum {Z : W → (Fin n → ℂ)} (hZ : IsOpenEmbedding Z)
    (V : X.Opens)
    (hG : ∀ f : Γ(X, V), ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (Z '' {y | y.1 ∈ chart V}) ∧
      ∀ (y : W) (hy : y.1 ∈ chart V), ComplexPoints.eval V f ⟨y.1, hy⟩ = G (Z y))
    (y : W) (hy : y.1 ∈ chart V) {ι : Type} [Fintype ι] (w : ι → Γ(X, V)) (f : Γ(X, V))
    (b : ι → Γ(X, V))
    (hD : letI := MMP.Mori.sectionAlgebra sX V
      KaehlerDifferential.D ℂ Γ(X, V) f = ∑ j, b j • KaehlerDifferential.D ℂ Γ(X, V) (w j)) :
    fderiv ℂ (chartPull sX Z V f) (Z y) =
      ∑ j, ComplexPoints.eval V (b j) ⟨y.1, hy⟩ • fderiv ℂ (chartPull sX Z V (w j)) (Z y) := by
  letI := MMP.Mori.sectionAlgebra sX V
  have hd : ∀ f : Γ(X, V), DifferentiableAt ℂ (chartPull sX Z V f) (Z y) := fun f ↦
    differentiableAt_chartPull sX hZ V f (hG f) y hy
  have hval : ∀ f : Γ(X, V), chartPull sX Z V f (Z y) = ComplexPoints.eval V f ⟨y.1, hy⟩ :=
    fun f ↦ chartPull_apply sX hZ.injective V f y hy
  have hadd : ∀ f g : Γ(X, V), fderiv ℂ (chartPull sX Z V (f + g)) (Z y) =
      fderiv ℂ (chartPull sX Z V f) (Z y) + fderiv ℂ (chartPull sX Z V g) (Z y) := by
    intro f g
    rw [← fderiv_add (hd f) (hd g)]
    refine Filter.EventuallyEq.fderiv_eq (eventually_chartPull sX hZ V y hy _ fun y' hy' ↦ ?_)
    simp only [Pi.add_apply, chartPull_apply sX hZ.injective V _ y' hy']
    exact map_add (evalRingHom sX V ⟨y'.1, hy'⟩) f g
  have hmul : ∀ f g : Γ(X, V), fderiv ℂ (chartPull sX Z V (f * g)) (Z y) =
      ComplexPoints.eval V f ⟨y.1, hy⟩ • fderiv ℂ (chartPull sX Z V g) (Z y) +
        ComplexPoints.eval V g ⟨y.1, hy⟩ • fderiv ℂ (chartPull sX Z V f) (Z y) := by
    intro f g
    rw [← hval f, ← hval g, ← fderiv_mul (hd f) (hd g)]
    refine Filter.EventuallyEq.fderiv_eq (eventually_chartPull sX hZ V y hy _ fun y' hy' ↦ ?_)
    simp only [Pi.mul_apply, chartPull_apply sX hZ.injective V _ y' hy']
    exact map_mul (evalRingHom sX V ⟨y'.1, hy'⟩) f g
  have hconst : ∀ c : ℂ, fderiv ℂ (chartPull sX Z V (algebraMap ℂ Γ(X, V) c)) (Z y) = 0 := by
    intro c
    rw [← fderiv_const_apply (𝕜 := ℂ) (x := Z y) c]
    refine Filter.EventuallyEq.fderiv_eq (eventually_chartPull sX hZ V y hy _ fun y' hy' ↦ ?_)
    rw [chartPull_apply sX hZ.injective V _ y' hy', eval_algebraMap]
  ext1 v
  letI : Algebra Γ(X, V) ℂ := (evalRingHom sX V ⟨y.1, hy⟩).toAlgebra
  haveI : IsScalarTower ℂ Γ(X, V) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (eval_algebraMap sX V c ⟨y.1, hy⟩).symm
  let d : Γ(X, V) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ fderiv ℂ (chartPull sX Z V f) (Z y) v
      map_add' := fun f g ↦ by simp only [hadd, ContinuousLinearMap.add_apply]
      map_smul' := fun c f ↦ by
        change fderiv ℂ (chartPull sX Z V (c • f)) (Z y) v = c • fderiv ℂ (chartPull sX Z V f) (Z
            y) v
        rw [Algebra.smul_def, hmul, hconst, eval_algebraMap sX V c ⟨y.1, hy⟩]
        simp }
  let D' : Derivation ℂ Γ(X, V) ℂ := Derivation.mk' d fun f g ↦ by
    change fderiv ℂ (chartPull sX Z V (f * g)) (Z y) v = _
    rw [hmul]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Algebra.smul_def]
    rfl
  have h := congrArg D'.liftKaehlerDifferential hD
  rw [D'.liftKaehlerDifferential_comp_D, map_sum] at h
  simp only [map_smul, D'.liftKaehlerDifferential_comp_D] at h
  change d f = _ at h
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply]
  rw [show fderiv ℂ (chartPull sX Z V f) (Z y) v = d f from rfl, h]
  rfl

end Analytic

section Local

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX]

/-- The differentials of étale coordinates span `Ω_{Γ(X, V)/ℂ}` on an affine `V ⊆ U`. -/
private lemma exists_coeffs_of_etale (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U) (f : Γ(X, V)) :
    letI := MMP.Mori.sectionAlgebra sX V
    ∃ b : Fin n → Γ(X, V), KaehlerDifferential.D ℂ Γ(X, V) f =
      ∑ j, b j • KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU).op (z j)) := by
  letI := MMP.Mori.sectionAlgebra sX V
  have h := D_mem_span_of_etale sX V _
    (etale_eval₂Hom_of_etale_homOfVector sX U z hz V hV hVU) f
  have hr : (Set.range fun j : ULift.{0} (Fin n) ↦
      KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU).op (z j.down))) =
      Set.range fun j : Fin n ↦
        KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU).op (z j)) := by
    ext ω
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨j.down, hj⟩, fun ⟨j, hj⟩ ↦ ⟨⟨j⟩, hj⟩⟩
  rw [hr] at h
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, V)).1 h
  exact ⟨b, hb.symm⟩

/-- Around a point of `W ∩ U'(ℂ)`: an affine `V` on which both coordinate systems are related by
matrices `a`, `a'` of regular functions, and the transition `z' ∘ z⁻¹` has complex derivative
with determinant `det a`. -/
private lemma exists_local_jacobian (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩))
    (U' : X.Opens) (z' : Fin n → Γ(X, U'))
    (hz' : Etale (AffineSpace.homOfVector (U'.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U'.topIso.inv (z' i.down))))
    (y : W) (hyU' : y.1 ∈ chart U') :
    ∃ (V : X.Opens) (hη : genericPoint X ∈ V) (hyV : y.1 ∈ chart V) (hVU : V ≤ U)
      (hVU' : V ≤ U') (a a' : Matrix (Fin n) (Fin n) Γ(X, V))
      (J : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)),
      (letI := MMP.Mori.sectionAlgebra sX V
        ∀ i, KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU').op (z' i)) =
          ∑ j, a i j • KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU).op (z j))) ∧
      (letI := MMP.Mori.sectionAlgebra sX V
        ∀ i, KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU).op (z i)) =
          ∑ j, a' i j • KaehlerDifferential.D ℂ Γ(X, V) (X.presheaf.map (homOfLE hVU').op (z' j))) ∧
      HasFDerivAt (fun x i ↦ chartPull sX
        (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) U' (z' i) x) J
        ((fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) y) ∧
      J.det = ComplexPoints.eval V a.det ⟨y.1, hyV⟩ := by
  set Z := fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩ with hZdef
  let q : Spec (.of ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : y.1.hom.base q ∈ U ⊓ U' := ⟨mem_of_mem_chart sX (hW y.2) q, mem_of_mem_chart sX hyU' q⟩
  obtain ⟨V, hV, hpV, hVle⟩ := exists_isAffineOpen_mem_and_subset hp
  have hVU : V ≤ U := hVle.trans inf_le_left
  have hVU' : V ≤ U' := hVle.trans inf_le_right
  have hyV : y.1 ∈ chart V := mem_chart_of_mem sX q hpV
  have hη : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨_, trivial, hpV⟩
  choose a ha using fun i ↦ exists_coeffs_of_etale sX U z hz V hV hVU
    (X.presheaf.map (homOfLE hVU').op (z' i))
  choose a' ha' using fun i ↦ exists_coeffs_of_etale sX U' z' hz' V hV hVU'
    (X.presheaf.map (homOfLE hVU).op (z i))
  have hG := fun f : Γ(X, V) ↦ (etaleCoordinate_atlas sX).2.2 U z hz W hW hWo hWz V f
  have hj : ∀ j, fderiv ℂ (chartPull sX Z V (X.presheaf.map (homOfLE hVU).op (z j))) (Z y) =
      (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ) := by
    intro j
    rw [← (hasFDerivAt_apply j (Z y)).fderiv]
    refine Filter.EventuallyEq.fderiv_eq (eventually_chartPull sX hWz V y hyV _ fun y' hy' ↦ ?_)
    rw [chartPull_apply sX hWz.injective V _ y' hy', eval_res]
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j ↦ evalRingHom sX V ⟨y.1, hyV⟩ (a i j)
  let P : Fin n → ((Fin n → ℂ) →L[ℂ] ℂ) := fun j ↦ ContinuousLinearMap.proj j
  let J : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i ↦ ∑ j, A i j • P j
  have hi : ∀ i, HasFDerivAt (fun x ↦ chartPull sX Z U' (z' i) x)
      (∑ j, A i j • P j) (Z y) := by
    intro i
    have d := differentiableAt_chartPull sX hWz V (X.presheaf.map (homOfLE hVU').op (z' i))
      (hG _) y hyV
    have e := fderiv_chartPull_eq_sum sX hWz V hG y hyV
      (fun j ↦ X.presheaf.map (homOfLE hVU).op (z j)) _ (a i) (ha i)
    simp only [hj] at e
    have h1 := d.hasFDerivAt
    rw [e] at h1
    refine h1.congr_of_eventuallyEq ?_
    refine eventually_chartPull sX hWz V y hyV _ fun y' hy' ↦ ?_
    dsimp only
    rw [chartPull_apply sX hWz.injective V _ y' hy', eval_res,
      chartPull_apply sX hWz.injective U' _ y' (chart_mono sX hVU' hy')]
  refine ⟨V, hη, hyV, hVU, hVU', a, a', J, ha, ha', ?_, ?_⟩
  · exact hasFDerivAt_pi.2 fun i ↦ by simpa [J] using hi i
  · have hJ : (J : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = Matrix.toLin' A := by
      refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
      simp [J, P, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    change LinearMap.det (J : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = _
    rw [hJ, LinearMap.det_toLin', ← evalRingHom_apply]
    exact (RingHom.map_det _ _).symm

end Local

section Integral

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [MeasurableSpace (ComplexPoints sX)] [BorelSpace
    (ComplexPoints sX)] {n : ℕ}

open Classical in
/-- A density on `X^an` read through the coordinates `Z` of a chart. -/
private noncomputable def chartDensity {W : Set (ComplexPoints sX)} (Z : W → (Fin n → ℂ))
    (ρ : ComplexPoints sX → ENNReal) : (Fin n → ℂ) → ENNReal := fun x ↦
  if h : ∃ y : W, Z y = x then ρ h.choose.1 else 0

private lemma chartDensity_apply {W : Set (ComplexPoints sX)} {Z : W → (Fin n → ℂ)}
    (hZ : Function.Injective Z) (ρ : ComplexPoints sX → ENNReal) (y : W) :
    chartDensity Z ρ (Z y) = ρ y.1 := by
  have h : ∃ y' : W, Z y' = Z y := ⟨y, rfl⟩
  simp only [chartDensity, dite_eq_left h]
  rw [hZ h.choose_spec]

/-- The chart measure of a measurable set as an integral over `ℂⁿ`. -/
private lemma withDensity_map_comap_apply {W : Set (ComplexPoints sX)} (hWo : IsOpen W)
    {Z : W → (Fin n → ℂ)} (hZ : IsOpenEmbedding Z) (ρ : ComplexPoints sX → ENNReal)
    {T : Set (ComplexPoints sX)} (hT : MeasurableSet T) :
    (((volume : Measure (Fin n → ℂ)).comap Z).map Subtype.val).withDensity ρ T =
      ∫⁻ x in Z '' (Subtype.val ⁻¹' T), chartDensity Z ρ x := by
  have hval : MeasurableEmbedding (Subtype.val : W → ComplexPoints sX) :=
    MeasurableEmbedding.subtype_coe hWo.measurableSet
  have hZm : MeasurableEmbedding Z := hZ.measurableEmbedding
  have hS : MeasurableSet (Subtype.val ⁻¹' T : Set W) := measurable_subtype_coe hT
  rw [withDensity_apply _ hT, hval.restrict_map, hval.lintegral_map]
  have e1 : ∀ y : W, ρ y.1 = chartDensity Z ρ (Z y) := fun y ↦
    (chartDensity_apply hZ.injective ρ y).symm
  simp_rw [e1]
  have h2 := hZm.restrict_map ((volume : Measure (Fin n → ℂ)).comap Z) (Z '' (Subtype.val ⁻¹' T))
  rw [Set.preimage_image_eq _ hZ.injective] at h2
  rw [← hZm.lintegral_map, ← h2, hZm.map_comap,
    Measure.restrict_restrict (hZm.measurableSet_image.2 hS),
    Set.inter_eq_left.2 (Set.image_subset_range _ _)]

end Integral

private lemma det_restrictScalars_complex {n : ℕ} (J : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (J.restrictScalars ℝ).det = Complex.normSq J.det := by
  change LinearMap.det ((J : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- The chart measures of `s` agree on overlaps (change of variables, the real Jacobian of the
holomorphic transition being `|det J|²`). -/
private lemma chartMeasure_restrict_inter_eq {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m)
    (s : MMP.Mori.RationalPluriForms sX n m)
    (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩))
    (U' : X.Opens) [Nonempty U'] (z' : Fin n → Γ(X, U'))
    (hz' : Etale (AffineSpace.homOfVector (U'.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U'.topIso.inv (z' i.down))))
    (W' : Set (ComplexPoints sX)) (hW' : W' ⊆ chart U') (hWo' : IsOpen W')
    (hWz' : IsOpenEmbedding (fun y : W' ↦ fun i ↦ ComplexPoints.eval U' (z' i) ⟨y.1, hW' y.2⟩)) :
    (pluriformChartMeasure sX hm s U z hz W hW hWo hWz).restrict (W ∩ W') =
      (pluriformChartMeasure sX hm s U' z' hz' W' hW' hWo' hWz').restrict (W ∩ W') := by
  set Z := fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩ with hZ
  set Z' := fun y : W' ↦ fun i ↦ ComplexPoints.eval U' (z' i) ⟨y.1, hW' y.2⟩ with hZ'
  set ρ := pluriformDensity sX m (pluriformCoeff sX s U z)
  set ρ' := pluriformDensity sX m (pluriformCoeff sX s U' z')
  let τ : (Fin n → ℂ) → (Fin n → ℂ) := fun x i ↦ chartPull sX Z U' (z' i) x
  have hτ : ∀ (y : W) (hy : y.1 ∈ W'), τ (Z y) = Z' ⟨y.1, hy⟩ := by
    intro y hy
    funext i
    exact chartPull_apply sX hWz.injective U' (z' i) y (hW' hy)
  have hloc : ∀ (y : W) (hy : y.1 ∈ W'), ∃ J : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ),
      HasFDerivAt τ J (Z y) ∧ ρ y.1 = ρ' y.1 * ENNReal.ofReal (Complex.normSq J.det) := by
    intro y hy
    obtain ⟨V, hη, hyV, hVU, hVU', a, a', J, ha, ha', hJ, hdet⟩ :=
      exists_local_jacobian sX U z hz W hW hWo hWz U' z' hz' y (hW' hy)
    obtain ⟨h1, h2⟩ := pluriformCoeff_rel sX s U U' z z' V hVU hVU' hη a a' ha ha'
    refine ⟨J, hJ, ?_⟩
    rw [show ρ y.1 = _ from pluriformDensity_mul_pow sX m hm _ _ V hη _ _ h1 h2 y.1 hyV, hdet,
      Complex.normSq_eq_norm_sq]
  ext T hT
  rw [Measure.restrict_apply hT, Measure.restrict_apply hT]
  have hTA : MeasurableSet (T ∩ (W ∩ W')) := hT.inter (hWo.measurableSet.inter hWo'.measurableSet)
  unfold pluriformChartMeasure
  rw [withDensity_map_comap_apply hWo hWz _ hTA, withDensity_map_comap_apply hWo' hWz' _ hTA]
  set S := Z '' (Subtype.val ⁻¹' (T ∩ (W ∩ W')))
  have hS : MeasurableSet S :=
    hWz.measurableEmbedding.measurableSet_image.2 (measurable_subtype_coe hTA)
  have hSimg : τ '' S = Z' '' (Subtype.val ⁻¹' (T ∩ (W ∩ W'))) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨⟨y.1, hy.2.2⟩, hy, (hτ y hy.2.2).symm⟩
    · rintro ⟨y', hy', rfl⟩
      exact ⟨Z ⟨y'.1, hy'.2.1⟩, ⟨⟨y'.1, hy'.2.1⟩, hy', rfl⟩, hτ ⟨y'.1, hy'.2.1⟩ hy'.2.2⟩
  have hderiv : ∀ x ∈ S, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) S x := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨J, hJ, -⟩ := hloc y hy.2.2
    rw [hJ.fderiv]
    exact hJ.restrictScalars ℝ |>.hasFDerivWithinAt
  have hinj : Set.InjOn τ S := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ h
    rw [hτ y₁ hy₁.2.2, hτ y₂ hy₂.2.2] at h
    have := congrArg Subtype.val (hWz'.injective h)
    exact congrArg Z (Subtype.ext this)
  rw [← hSimg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hderiv hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨J, hJ, hρ⟩ := hloc y hy.2.2
  beta_reduce
  rw [chartDensity_apply hWz.injective, hτ y hy.2.2, chartDensity_apply hWz'.injective, hJ.fderiv,
    det_restrictScalars_complex, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact hρ.trans (mul_comm _ _)

end Overlap

section Naturality

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}

private lemma mem_chart_realize_of_le (f : Y ⟶ X) (hf : f ≫ sX = sY) {U : X.Opens} {V : Y.Opens}
    (e : V ≤ f ⁻¹ᵁ U) {y : ComplexPoints sY} (hy : y ∈ chart V) :
    realize f hf y ∈ chart U := by
  change (y.hom ≫ f) ⁻¹ᵁ U = ⊤
  rw [Scheme.Hom.comp_preimage]
  exact top_le_iff.1 (hy.ge.trans (Scheme.Hom.preimage_mono _ e))

private lemma eval_appLE_realize (f : Y ⟶ X) (hf : f ≫ sX = sY) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) (y : ComplexPoints sY) (hy : y ∈ chart V) :
    ComplexPoints.eval V (f.appLE U V e a) ⟨y, hy⟩ =
      ComplexPoints.eval U a ⟨realize f hf y, mem_chart_realize_of_le f hf e hy⟩ := by
  simp only [ComplexPoints.eval]
  congr 1
  change (f.appLE U V e ≫ y.hom.appLE V ⊤ _) a = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

private lemma continuous_realize_of_isIso (f : Y ⟶ X) [IsIso f] (hf : f ≫ sX = sY) :
    Continuous (realize f hf) := by
  refine continuous_iSup_dom.2 fun V ↦ continuous_coinduced_dom.2 ?_
  let U : X.affineOpens := ⟨f ''ᵁ (V : Y.Opens), V.2.image_of_isOpenImmersion f⟩
  have e : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens) := (Scheme.Hom.preimage_image_eq f _).ge
  let φ : chart (sX := sY) (V : Y.Opens) → chart (sX := sX) (U : X.Opens) :=
    fun y ↦ ⟨realize f hf y.1, mem_chart_realize_of_le f hf e y.2⟩
  have hφ : Continuous[chartTopology (V : Y.Opens), chartTopology (U : X.Opens)] φ := by
    rw [continuous_iff_le_induced]
    change _ ≤ TopologicalSpace.induced φ (⨅ a : Γ(X, (U : X.Opens)), _)
    rw [induced_iInf]
    refine le_iInf fun a ↦ ?_
    rw [induced_compose]
    have : (ComplexPoints.eval (U : X.Opens) a ∘ φ) =
        ComplexPoints.eval (V : Y.Opens) (f.appLE _ _ e a) :=
      funext fun y ↦ (eval_appLE_realize f hf _ _ e a y.1 y.2).symm
    rw [this]
    exact continuous_iff_le_induced.1 (continuous_eval _ _)
  exact @Continuous.comp _ _ _ (chartTopology _) (chartTopology _) _ _ _ (continuous_chart_val U) hφ

/-- The realization of an isomorphism over `ℂ` is a homeomorphism. -/
private noncomputable def realizeHomeomorph (f : Y ⟶ X) [IsIso f] (hf : f ≫ sX = sY) :
    ComplexPoints sY ≃ₜ ComplexPoints sX where
  toFun := realize f hf
  invFun := realize (inv f) (by rw [← hf, IsIso.inv_hom_id_assoc])
  left_inv y := by ext1; simp
  right_inv x := by ext1; simp
  continuous_toFun := continuous_realize_of_isIso f hf
  continuous_invFun := continuous_realize_of_isIso _ _

private lemma germ_app_eq_functionFieldMap (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U)) (hY : genericPoint Y ∈ f ⁻¹ᵁ U) :
    Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hY (f.app U a) =
      functionFieldMap f (X.presheaf.germ U (genericPoint X) hU a) := by
  calc Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hY (f.app U a)
      = (X.presheaf.germ U (f (genericPoint Y)) hY ≫ f.stalkMap (genericPoint Y)) a := by
        rw [Scheme.Hom.germ_stalkMap f U (genericPoint Y) hY]
        rfl
    _ = ((X.presheaf.germ U (genericPoint X) hU ≫ X.presheaf.stalkSpecializes
          (Inseparable.of_eq (map_genericPoint_of_isDominant f)).specializes) ≫
          f.stalkMap (genericPoint Y)) a := by
        rw [TopCat.Presheaf.germ_stalkSpecializes X.presheaf hU
          (Inseparable.of_eq (map_genericPoint_of_isDominant f)).specializes]
    _ = _ := rfl

private lemma functionFieldMap_functionFieldMap [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) (f' : X ⟶ Y)
    [IsDominant f] [IsDominant f'] (h : f' ≫ f = 𝟙 X) (φ : X.functionField) :
    functionFieldMap f' (functionFieldMap f φ) = φ := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq φ
  have hY : genericPoint Y ∈ f ⁻¹ᵁ U := by
    change f (genericPoint Y) ∈ U
    rwa [map_genericPoint_of_isDominant f]
  have hX : genericPoint X ∈ f' ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    change f' (genericPoint X) ∈ f ⁻¹ᵁ U
    rwa [map_genericPoint_of_isDominant f']
  rw [← germ_app_eq_functionFieldMap f U hU a hY,
    ← germ_app_eq_functionFieldMap f' _ hY _ hX]
  have key : ∀ (k : X ⟶ X), k = 𝟙 X → ∀ (hk : genericPoint X ∈ k ⁻¹ᵁ U),
      X.presheaf.germ (k ⁻¹ᵁ U) (genericPoint X) hk (k.app U a) =
        X.presheaf.germ U (genericPoint X) hU a := by
    rintro k rfl hk
    rfl
  have e : f'.app (f ⁻¹ᵁ U) (f.app U a) = (f' ≫ f).app U a := by
    rw [Scheme.Hom.comp_app]; rfl
  rw [e]
  exact key _ h hX

private lemma eval_app_realize (f : Y ⟶ X) (hf : f ≫ sX = sY) (U : X.Opens) (a : Γ(X, U))
    (y : ComplexPoints sY) (hy : y ∈ chart (f ⁻¹ᵁ U)) :
    ComplexPoints.eval (f ⁻¹ᵁ U) (f.app U a) ⟨y, hy⟩ =
      ComplexPoints.eval U a ⟨realize f hf y, mem_chart_realize_of_le f hf le_rfl hy⟩ := by
  rw [← eval_appLE_realize f hf U _ le_rfl a y hy, Scheme.Hom.appLE_eq_app]

private lemma pluriformDensity_realize_le [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hf : f ≫ sX = sY) (m : ℕ) (φ : X.functionField) (y : ComplexPoints sY) :
    pluriformDensity sX m φ (realize f hf y) ≤ pluriformDensity sY m (functionFieldMap f φ) y := by
  unfold pluriformDensity
  refine iSup_le fun U ↦ iSup_le fun a ↦ iSup_le fun hy ↦ iSup_le fun hg ↦ iSup_le fun hga ↦ ?_
  have hy' : y ∈ chart (f ⁻¹ᵁ U) := by
    change y.hom ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤
    have : (y.hom ≫ f) ⁻¹ᵁ U = ⊤ := hy
    rwa [Scheme.Hom.comp_preimage] at this
  have hg' : genericPoint Y ∈ f ⁻¹ᵁ U := by
    change f (genericPoint Y) ∈ U; rwa [map_genericPoint_of_isDominant f]
  refine le_iSup_of_le (f ⁻¹ᵁ U) <| le_iSup_of_le (f.app U a) <| le_iSup_of_le hy' <|
    le_iSup_of_le hg' <| le_iSup_of_le ?_ (le_of_eq ?_)
  · rw [germ_app_eq_functionFieldMap f U hg a hg', hga]
  · rw [eval_app_realize f hf U a y hy']

private lemma span_topFormsMap_of_bijective {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    (hb : Function.Bijective (algebraMap K K')) {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : Submodule.span K {ω} = ⊤) :
    Submodule.span K' {MMP.Mori.topFormsMap k K K' d ω} = ⊤ := by
  haveI : IsLocalization (⊥ : Submonoid K) K := IsLocalization.self bot_le
  haveI : IsLocalization (⊥ : Submonoid K) K' := IsLocalization.isLocalization_of_algEquiv
    (S := K) ⊥ (AlgEquiv.ofBijective (Algebra.ofId K K') hb)
  exact MMP.Mori.span_singleton_topFormsMap (⊥ : Submonoid K) hω

private lemma pluriformDensity_functionFieldMap [IsIntegral X] (g : Y ⟶ X) [IsIso g]
    [IsIntegral Y] (m : ℕ) (φ : X.functionField) (y : ComplexPoints (g ≫ sX)) :
    pluriformDensity (g ≫ sX) m (functionFieldMap g φ) y =
      pluriformDensity sX m φ (realize g rfl y) := by
  refine le_antisymm ?_ (pluriformDensity_realize_le g rfl m φ y)
  have h' : inv g ≫ g ≫ sX = sX := IsIso.inv_hom_id_assoc g sX
  have := pluriformDensity_realize_le (sX := g ≫ sX) (sY := sX) (inv g) h' m
    (functionFieldMap g φ) (realize g rfl y)
  have e1 : realize (inv g) h' (realize g rfl y) = y := by ext1; simp
  rwa [e1, functionFieldMap_functionFieldMap g (inv g) (IsIso.inv_hom_id g)] at this

private lemma repr_smul_basisOfSpanSingleton {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    {ω ω' : L} (h : ω' = ω) (h1 : Submodule.span K {ω} = ⊤) (h2 : ω ≠ 0)
    (h1' : Submodule.span K {ω'} = ⊤) (h2' : ω' ≠ 0) (m : ℤ) (c : K) :
    (MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton h1 h2) m).repr
      (c • MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton h1' h2') m ()) () = c := by
  subst h
  simp

/-- If `g^* : ℂ(X) → ℂ(Y)` is bijective, the coefficient of `g^*s` along the coordinates `g^*z`
is `g^*` of the coefficient of `s` along `z`. -/
private lemma pluriformCoeff_pullback_of_bijective [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X)
    [IsDominant g] (hbij : Function.Bijective (functionFieldMap g)) {n m : ℕ}
    (s : MMP.Mori.RationalPluriForms sX n m) (U : X.Opens) [Nonempty U] [Nonempty (g ⁻¹ᵁ U)]
    (z : Fin n → Γ(X, U)) :
    pluriformCoeff (g ≫ sX) (MMP.Mori.pullbackRationalPluriForms sX g s) (g ⁻¹ᵁ U)
        (fun i ↦ g.app U (z i)) = functionFieldMap g (pluriformCoeff sX s U z) := by
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (g ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap sX g
  let eg : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap g) hbij
  have hgerm : ∀ i, Y.germToFunctionField (g ⁻¹ᵁ U) (g.app U (z i)) =
      algebraMap X.functionField Y.functionField (X.germToFunctionField U (z i)) := fun i ↦
    germ_app_eq_functionFieldMap g U _ (z i) _
  have hb1 : ∀ φ : X.functionField, eg.symm (algebraMap X.functionField Y.functionField φ) = φ :=
    eg.symm_apply_apply
  have hb : Function.Bijective (algebraMap X.functionField Y.functionField) := hbij
  unfold pluriformCoeff
  dsimp only
  set dzX : ⋀[X.functionField]^n Ω[X.functionField⁄ℂ] := exteriorPower.ιMulti X.functionField n
    (fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField U (z i))) with hdzX
  set dzY : ⋀[Y.functionField]^n Ω[Y.functionField⁄ℂ] := exteriorPower.ιMulti Y.functionField n
    (fun i ↦ KaehlerDifferential.D ℂ Y.functionField
      (Y.germToFunctionField (g ⁻¹ᵁ U) (g.app U (z i)))) with hdzY
  have hdz : dzY = MMP.Mori.topFormsMap ℂ X.functionField Y.functionField n dzX := by
    rw [hdzY, MMP.Mori.topFormsMap_ιMulti]
    congr 1
    funext i
    rw [KaehlerDifferential.map_D, hgerm]
  let alg' : Algebra Y.functionField X.functionField := eg.symm.toRingHom.toAlgebra
  have : IsScalarTower ℂ Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext c
    change _ = eg.symm (algebraMap ℂ Y.functionField c)
    rw [IsScalarTower.algebraMap_apply ℂ X.functionField Y.functionField c]
    exact (hb1 _).symm
  have hb' : Function.Bijective (algebraMap Y.functionField X.functionField) := eg.symm.bijective
  have hdz' : dzX = MMP.Mori.topFormsMap ℂ Y.functionField X.functionField n dzY := by
    rw [hdzY, MMP.Mori.topFormsMap_ιMulti, hdzX]
    congr 1
    funext i
    rw [KaehlerDifferential.map_D, hgerm]
    exact congrArg _ (hb1 _).symm
  split_ifs with hY hX hX
  · have hY' : Submodule.span Y.functionField {dzY} = ⊤ ∧ dzY ≠ 0 := hY
    have hX' : Submodule.span X.functionField {dzX} = ⊤ ∧ dzX ≠ 0 := hX
    have hω : MMP.Mori.IsPullbackGenerator Y.functionField dzX :=
      ⟨hX'.1, hdz ▸ hY'.1, hdz ▸ hY'.2⟩
    unfold MMP.Mori.pullbackRationalPluriForms
    erw [MMP.Mori.pullbackForms_eq hω]
    unfold MMP.Mori.pullbackFormsAlong
    exact repr_smul_basisOfSpanSingleton (ω := dzY)
      (ω' := MMP.Mori.topFormsMap ℂ X.functionField Y.functionField n dzX) hdz.symm _ _ _ _ _ _
  · exfalso
    have hY' : Submodule.span Y.functionField {dzY} = ⊤ ∧ dzY ≠ 0 := hY
    refine hX ⟨?_, fun h0 ↦ hY'.2 ?_⟩
    · change Submodule.span X.functionField {dzX} = ⊤
      rw [hdz']
      exact span_topFormsMap_of_bijective hb' hY'.1
    · change dzX = 0 at h0
      rw [hdz, h0, map_zero]
  · exfalso
    have hX' : Submodule.span X.functionField {dzX} = ⊤ ∧ dzX ≠ 0 := hX
    refine hY ⟨?_, fun h0 ↦ hX'.2 ?_⟩
    · change Submodule.span Y.functionField {dzY} = ⊤
      rw [hdz]
      exact span_topFormsMap_of_bijective hb hX'.1
    · change dzY = 0 at h0
      rw [hdz', h0, map_zero]
  · exact (map_zero _).symm

private lemma mem_chart_preimage_iff (f : Y ⟶ X) (hf : f ≫ sX = sY) (U : X.Opens)
    (y : ComplexPoints sY) :
    y ∈ chart (f ⁻¹ᵁ U) ↔ realize f hf y ∈ chart U := by
  change y.hom ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ ↔ (y.hom ≫ f) ⁻¹ᵁ U = ⊤
  rw [Scheme.Hom.comp_preimage]

/-- Étale coordinates pull back to étale coordinates along an open immersion. -/
private lemma etale_pullback_coords (g : Y ⟶ X) [IsOpenImmersion g] {n : ℕ} (U : X.Opens)
    (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))) :
    Etale (AffineSpace.homOfVector ((g ⁻¹ᵁ U).ι ≫ g ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ (g ⁻¹ᵁ U).topIso.inv (g.app U (z i.down)))) := by
  have e : AffineSpace.homOfVector ((g ⁻¹ᵁ U).ι ≫ g ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ (g ⁻¹ᵁ U).topIso.inv (g.app U (z i.down))) =
      g.resLE U (g ⁻¹ᵁ U) le_rfl ≫ AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)) := by
    rw [AffineSpace.comp_homOfVector, Scheme.Hom.resLE_comp_ι_assoc]
    congr 1
    funext i
    change _ = (g.resLE U (g ⁻¹ᵁ U) le_rfl).app ⊤ (U.topIso.inv (z i.down))
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
    exact (congrArg (fun φ : Γ(X, U) ⟶ Γ(g ⁻¹ᵁ U, ⊤) ↦ φ (z i.down))
      (Iso.inv_hom_id_assoc U.topIso (g.app U ≫ (g ⁻¹ᵁ U).topIso.inv))).symm
  have : IsOpenImmersion (g.resLE U (g ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  rw [e]
  infer_instance

private lemma map_map_comap_comp_restrictPreimage {α β γ : Type*} [TopologicalSpace α]
    [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [TopologicalSpace γ]
    [MeasurableSpace γ] [BorelSpace γ] (e : α ≃ₜ β) {W : Set β} (ζ : W → γ)
    (hζ : IsOpenEmbedding ζ) (μ : Measure γ) :
    ((μ.comap (ζ ∘ W.restrictPreimage e)).map Subtype.val).map e =
      (μ.comap ζ).map Subtype.val := by
  let eW : (e ⁻¹' W) ≃ₜ W := e.subtype fun _ ↦ Iff.rfl
  let mW := eW.toMeasurableEquiv
  have hcomp : ζ ∘ W.restrictPreimage e = ζ ∘ mW := rfl
  have hval : (e : α → β) ∘ (Subtype.val : e ⁻¹' W → α) = Subtype.val ∘ mW := rfl
  rw [Measure.map_map e.continuous.measurable measurable_subtype_coe, hval,
    ← Measure.map_map measurable_subtype_coe mW.measurable, hcomp,
    ← Measure.comap_comap (fun s hs ↦ mW.measurableEmbedding.measurableSet_image' hs)
      hζ.injective (fun s hs ↦ hζ.measurableEmbedding.measurableSet_image' hs)]
  congr 1
  rw [← mW.symm_symm, MeasurableEquiv.comap_symm, MeasurableEquiv.symm_symm,
    MeasurableEquiv.map_map_symm]

/-- Push-forward of a density along a measurable embedding. -/
private lemma map_withDensity_comp_of_measurableEmbedding {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {e : α → β} (he : MeasurableEmbedding e) (μ : Measure α)
    (f : β → ENNReal) :
    (μ.withDensity (f ∘ e)).map e = (μ.map e).withDensity f := by
  ext A hA
  rw [he.map_apply, withDensity_apply _ (he.measurable hA), withDensity_apply _ hA,
    he.restrict_map, he.lintegral_map]
  rfl

end Naturality

private lemma chartMeasure_map_realize {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m)
    (s : MMP.Mori.RationalPluriForms sX n m)
    {Y : Scheme.{0}} (g : Y ⟶ X) [IsIso g]
    [AlgebraicGeometry.IsVariety ℂ (g ≫ sX)] [SmoothOfRelativeDimension n (g ≫ sX)]
    [MeasurableSpace (ComplexPoints (g ≫ sX))] [BorelSpace (ComplexPoints (g ≫ sX))]
    (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩))
    [Nonempty (g ⁻¹ᵁ U)]
    (hz' : Etale (AffineSpace.homOfVector ((g ⁻¹ᵁ U).ι ≫ g ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ (g ⁻¹ᵁ U).topIso.inv (g.app U (z i.down)))))
    (hW' : realize g rfl ⁻¹' W ⊆ chart (g ⁻¹ᵁ U)) (hWo' : IsOpen (realize g rfl ⁻¹' W))
    (hWz' : IsOpenEmbedding (fun y : (realize g rfl ⁻¹' W : Set (ComplexPoints (g ≫ sX))) ↦
      fun i ↦ ComplexPoints.eval (g ⁻¹ᵁ U) (g.app U (z i)) ⟨y.1, hW' y.2⟩)) :
    (pluriformChartMeasure (g ≫ sX) hm (MMP.Mori.pullbackRationalPluriForms sX g s) (g ⁻¹ᵁ U)
      (fun i ↦ g.app U (z i)) hz' _ hW' hWo' hWz').map (realize g rfl) =
      pluriformChartMeasure sX hm s U z hz W hW hWo hWz := by
  let e := (realizeHomeomorph (sX := sX) (sY := g ≫ sX) g rfl).toMeasurableEquiv
  have he : (e : ComplexPoints (g ≫ sX) → ComplexPoints sX) = realize g rfl := rfl
  have hζ : (fun y : (realize g rfl ⁻¹' W : Set (ComplexPoints (g ≫ sX))) ↦
      fun i ↦ ComplexPoints.eval (g ⁻¹ᵁ U) (g.app U (z i)) ⟨y.1, hW' y.2⟩) =
      (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) ∘
        W.restrictPreimage (realizeHomeomorph (sX := sX) (sY := g ≫ sX) g rfl) := by
    funext y i
    exact eval_app_realize g rfl U (z i) y.1 (hW' y.2)
  have hbase := map_map_comap_comp_restrictPreimage (realizeHomeomorph (sX := sX) (sY := g ≫ sX) g
      rfl) _ hWz
    (volume : Measure (Fin n → ℂ))
  have hρ : ∀ y, pluriformDensity (g ≫ sX) m (pluriformCoeff (g ≫ sX)
      (MMP.Mori.pullbackRationalPluriForms sX g s) (g ⁻¹ᵁ U) (fun i ↦ g.app U (z i))) y =
      pluriformDensity sX m (pluriformCoeff sX s U z) (e y) := fun y ↦ by
    rw [pluriformCoeff_pullback_of_bijective g ⟨(functionFieldMap g).injective, fun ψ ↦
      ⟨_, functionFieldMap_functionFieldMap (inv g) g (IsIso.hom_inv_id g) ψ⟩⟩,
      pluriformDensity_functionFieldMap]; rfl
  unfold pluriformChartMeasure
  rw [hζ, ← hbase, show pluriformDensity (g ≫ sX) m (pluriformCoeff (g ≫ sX)
      (MMP.Mori.pullbackRationalPluriForms sX g s) (g ⁻¹ᵁ U) (fun i ↦ g.app U (z i))) =
      pluriformDensity sX m (pluriformCoeff sX s U z) ∘ e from funext hρ]
  exact map_withDensity_comp_of_measurableEmbedding e.measurableEmbedding _ _

/-- Naturality: an isomorphism `g` carries the glued measure of `g^*s` to that of `s`. -/
private lemma map_realize_isGlued {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m)
    (s : MMP.Mori.RationalPluriForms sX n m)
    {Y : Scheme.{0}} (g : Y ⟶ X) [IsIso g]
    [AlgebraicGeometry.IsVariety ℂ (g ≫ sX)] [SmoothOfRelativeDimension n (g ≫ sX)]
    [MeasurableSpace (ComplexPoints (g ≫ sX))] [BorelSpace (ComplexPoints (g ≫ sX))]
    (ν : Measure (ComplexPoints (g ≫ sX)))
    (hν : ∀ (V : Y.Opens) [Nonempty V] (z : Fin n → Γ(Y, V))
        (hz : Etale (AffineSpace.homOfVector (V.ι ≫ g ≫ sX)
          (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
        (W : Set (ComplexPoints (g ≫ sX))) (hW : W ⊆ chart V) (hWo : IsOpen W)
        (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval V (z i) ⟨y.1, hW y.2⟩)),
        ν.restrict W = pluriformChartMeasure (g ≫ sX) hm
          (MMP.Mori.pullbackRationalPluriForms sX g s) V z hz W hW hWo hWz) :
    ∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩)),
      (ν.map (realize g rfl)).restrict W = pluriformChartMeasure sX hm s U z hz W hW hWo hWz := by
  intro U _ z hz W hW hWo hWz
  let r := realizeHomeomorph (sX := sX) (sY := g ≫ sX) g rfl
  have : Nonempty (g ⁻¹ᵁ U) := by
    obtain ⟨x⟩ := ‹Nonempty U›
    refine ⟨⟨(inv g).base x.1, ?_⟩⟩
    change g.base ((inv g).base x.1) ∈ U
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    exact x.2
  have hW' : realize g rfl ⁻¹' W ⊆ chart (g ⁻¹ᵁ U) := fun y hy ↦
    (mem_chart_preimage_iff g rfl U y).2 (hW hy)
  have hWo' : IsOpen (realize g rfl ⁻¹' W) := hWo.preimage (continuous_realize_of_isIso g rfl)
  have hζ : (fun y : (realize g rfl ⁻¹' W : Set (ComplexPoints (g ≫ sX))) ↦
      fun i ↦ ComplexPoints.eval (g ⁻¹ᵁ U) (g.app U (z i)) ⟨y.1, hW' y.2⟩) =
      (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) ∘
        W.restrictPreimage r := by
    funext y i
    exact eval_app_realize g rfl U (z i) y.1 (hW' y.2)
  have hWz' : IsOpenEmbedding (fun y : (realize g rfl ⁻¹' W : Set (ComplexPoints (g ≫ sX))) ↦
      fun i ↦ ComplexPoints.eval (g ⁻¹ᵁ U) (g.app U (z i)) ⟨y.1, hW' y.2⟩) := by
    rw [hζ]
    exact hWz.comp (r.isOpenEmbedding.restrictPreimage W)
  have hz' := etale_pullback_coords (sX := sX) g U z hz
  let e := r.toMeasurableEquiv
  calc (ν.map (realize g rfl)).restrict W = (ν.map e).restrict W := rfl
    _ = (ν.restrict (e ⁻¹' W)).map e := e.restrict_map ν W
    _ = (pluriformChartMeasure (g ≫ sX) hm (MMP.Mori.pullbackRationalPluriForms sX g s)
          (g ⁻¹ᵁ U) (fun i ↦ g.app U (z i)) hz' _ hW' hWo' hWz').map e := by
        rw [← hν (g ⁻¹ᵁ U) (fun i ↦ g.app U (z i)) hz' _ hW' hWo' hWz']
        rfl
    _ = _ := chartMeasure_map_realize sX hm s g U z hz W hW hWo hWz hz' hW' hWo' hWz'

/-- `μ` restricts on every étale chart `W` to the chart measure of `s` on `W`. -/
private def IsGlued (s : MMP.Mori.RationalPluriForms sX n m) (μ : Measure (ComplexPoints sX)) :
    Prop :=
  ∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
    μ.restrict W = pluriformChartMeasure sX hm s U z hz W hW hWo hWz

/-- Every point of `X^an` lies in an étale chart
(`MMP.Analytic.ComplexPoints.etaleCoordinate_atlas`). -/
private lemma exists_etaleChart_mem (x : ComplexPoints sX) : ∃ c : EtaleChart sX n, x ∈ c.W := by
  obtain ⟨U, z, hz, hx⟩ := (etaleCoordinate_atlas sX (n := n)).1 x
  obtain ⟨W, hW, hWo, hxW, hWz⟩ := (etaleCoordinate_atlas sX (n := n)).2.1 U z hz x hx
  have hU : Nonempty U := ⟨⟨_, mem_of_mem_chart sX hx (Classical.arbitrary _)⟩⟩
  exact ⟨⟨U, hU, z, hz, W, hW, hWo, hWz⟩, hxW⟩

/-- Countably many étale charts cover `X^an`: the charts cover it
(`MMP.Analytic.ComplexPoints.etaleCoordinate_atlas`) and `X^an` is Lindelöf, being covered by the
finitely many affine charts `U(ℂ) ⊆ ℂ^N` of a finite affine cover of `X`. -/
private lemma exists_countable_etaleChart_cover :
    ∃ S : Set (EtaleChart sX n), S.Countable ∧ ⋃ c ∈ S, c.W = Set.univ := by
  have hcov : (Set.univ : Set (ComplexPoints sX)) ⊆ ⋃ c : EtaleChart sX n, c.W := fun x _ ↦
    Set.mem_iUnion.2 (exists_etaleChart_mem sX x)
  obtain ⟨r, hr, hsub⟩ := (isLindelof_univ_complexPoints sX).elim_countable_subcover
    (fun c : EtaleChart sX n ↦ c.W) (fun c ↦ c.hWo) hcov
  exact ⟨r, hr, Set.eq_univ_of_univ_subset hsub⟩

/-- A chart measure is supported on its chart. -/
private lemma pluriformChartMeasure_restrict_self (s : MMP.Mori.RationalPluriForms sX n m)
    (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩))
    (hWm : MeasurableSet W) :
    (pluriformChartMeasure sX hm s U z hz W hW hWo hWz).restrict W =
      pluriformChartMeasure sX hm s U z hz W hW hWo hWz := by
  unfold pluriformChartMeasure
  rw [restrict_withDensity hWm, Measure.restrict_map measurable_subtype_coe hWm,
    Subtype.coe_preimage_self, Measure.restrict_univ]

/-- Two measures on `X^an` with the same restriction to every étale chart are equal: the charts
cover `X^an` (`MMP.Analytic.ComplexPoints.etaleCoordinate_atlas`) and countably many suffice. -/
private lemma eq_of_forall_restrict_chart_eq [BorelSpace (ComplexPoints sX)]
    (μ μ' : Measure (ComplexPoints sX))
    (h : ∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
      μ.restrict W = μ'.restrict W) :
    μ = μ' := by
  obtain ⟨S, hSc, hSu⟩ := exists_countable_etaleChart_cover sX (n := n)
  refine (Measure.ext_iff_of_sUnion_eq_univ (S := EtaleChart.W '' S) (hSc.image _)
    (by rwa [Set.sUnion_image])).2 ?_
  rintro _ ⟨c, -, rfl⟩
  haveI := c.ne
  exact h c.U c.z c.hz c.W c.hW c.hWo c.hWz

private lemma isGlued_unique [BorelSpace (ComplexPoints sX)]
    (s : MMP.Mori.RationalPluriForms sX n m)
    {μ μ' : Measure (ComplexPoints sX)} (h : IsGlued sX hm s μ) (h' : IsGlued sX hm s μ') :
    μ = μ' :=
  eq_of_forall_restrict_chart_eq sX μ μ' fun U _ z hz W hW hWo hWz ↦ by
    rw [h U z hz W hW hWo hWz, h' U z hz W hW hWo hWz]

/-- The chart measures of `s` glue to a measure on `X^an`. -/
private lemma exists_isGlued [BorelSpace (ComplexPoints sX)]
    (s : MMP.Mori.RationalPluriForms sX n m) :
    ∃ μ, IsGlued sX hm s μ := by
  obtain ⟨S, hSc, hSu⟩ := exists_countable_etaleChart_cover sX (n := n)
  rcases S.eq_empty_or_nonempty with hS | hS
  · have : IsEmpty (ComplexPoints sX) := ⟨fun y ↦ by
      have : y ∈ ⋃ c ∈ S, c.W := hSu ▸ Set.mem_univ y
      simp [hS] at this⟩
    exact ⟨0, fun U _ z hz W hW hWo hWz ↦ Measure.ext fun A _ ↦ by
      simp [Set.eq_empty_of_isEmpty A]⟩
  obtain ⟨f, rfl⟩ := hSc.exists_eq_range hS
  let M : ℕ → Measure (ComplexPoints sX) := fun k ↦ haveI := (f k).ne
    pluriformChartMeasure sX hm s (f k).U (f k).z (f k).hz (f k).W (f k).hW (f k).hWo (f k).hWz
  let D := disjointed (fun k ↦ (f k).W)
  have hDm : ∀ k, MeasurableSet (D k) :=
    MeasurableSet.disjointed fun k ↦ (f k).hWo.measurableSet
  have hDu : ⋃ k, D k = Set.univ := by
    rw [iUnion_disjointed, ← hSu, Set.biUnion_range]
  refine ⟨Measure.sum fun k ↦ (M k).restrict (D k), fun U _ z hz W hW hWo hWz ↦ ?_⟩
  set ν := pluriformChartMeasure sX hm s U z hz W hW hWo hWz
  have hWm := hWo.measurableSet
  calc (Measure.sum fun k ↦ (M k).restrict (D k)).restrict W
      = Measure.sum fun k ↦ ((M k).restrict (D k)).restrict W := Measure.restrict_sum _ hWm
    _ = Measure.sum fun k ↦ (ν.restrict W).restrict (D k) := by
        congr 1
        funext k
        have hsub : W ∩ D k ⊆ (f k).W ∩ W := fun x hx ↦ ⟨disjointed_subset (fun k ↦ (f k).W) k
            hx.2, hx.1⟩
        have hov : (M k).restrict ((f k).W ∩ W) = ν.restrict ((f k).W ∩ W) := by
          haveI := (f k).ne
          exact chartMeasure_restrict_inter_eq sX hm s (f k).U (f k).z (f k).hz (f k).W (f k).hW
            (f k).hWo (f k).hWz U z hz W hW hWo hWz
        rw [Measure.restrict_restrict hWm, Measure.restrict_restrict (hDm k), Set.inter_comm (D k)
            W,
          ← Measure.restrict_restrict_of_subset hsub, hov, Measure.restrict_restrict_of_subset hsub]
    _ = (ν.restrict W).restrict (⋃ k, D k) :=
        (Measure.restrict_iUnion (disjoint_disjointed _) hDm).symm
    _ = ν := by
        rw [hDu, Measure.restrict_univ]
        exact pluriformChartMeasure_restrict_self sX hm s U z hz W hW hWo hWz hWm

/-- Homogeneity of the chart measure: `μ_{cs} = |c|^{2/m} μ_s` on each chart. -/
private lemma chartMeasure_smul (s : MMP.Mori.RationalPluriForms sX n m) (c : ℂ)
    (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) :
    pluriformChartMeasure sX hm
        (@algebraMap ℂ X.functionField _ _ (MMP.Mori.functionFieldAlgebra sX) c • s)
        U z hz W hW hWo hWz =
      ENNReal.ofReal (‖c‖ ^ (2 / m : ℝ)) • pluriformChartMeasure sX hm s U z hz W hW hWo hWz := by
  unfold pluriformChartMeasure
  rw [pluriformCoeff_smul, pluriformDensity_algebraMap_mul sX m hm]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

end MMP.Analytic.Proof_lem_mmp_analytic_pluriform_density_intrinsic

namespace MMP.Analytic.ComplexPoints

open MMP.Analytic.Proof_lem_mmp_analytic_pluriform_density_intrinsic in
/-- **The density of a rational pluriform is intrinsic.** Let `X` be a smooth complex variety of
dimension `n`, `m > 0` and `s` a rational `m`-canonical form on `X`. Then

1. the chart measures of `s` (`MMP.Analytic.ComplexPoints.pluriformChartMeasure`) on two charts
   `W`, `W'` agree on `W ∩ W'`;
2. there is a unique measure `μ_s` on `X^an` whose restriction to every chart `W` is the chart
   measure of `s` on `W`;
3. for `c ∈ ℂ`, `μ_{c s} = |c|^{2/m} μ_s`;
4. for an isomorphism `g : Y ⟶ X`, the push-forward of `μ_{g^*s}` along `X^an ← Y^an` is `μ_s`. -/
@[mmp "lem_mmp_analytic_pluriform_density_intrinsic"]
public theorem pluriformChartMeasure_intrinsic {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m)
    (s : MMP.Mori.RationalPluriForms sX n m) :
    -- (1) chart measures agree on overlaps
    (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩))
      (U' : X.Opens) [Nonempty U'] (z' : Fin n → Γ(X, U'))
      (hz' : Etale (AffineSpace.homOfVector (U'.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U'.topIso.inv (z' i.down))))
      (W' : Set (ComplexPoints sX)) (hW' : W' ⊆ chart U') (hWo' : IsOpen W')
      (hWz' : IsOpenEmbedding (fun y : W' ↦ fun i ↦ eval U' (z' i) ⟨y.1, hW' y.2⟩)),
      (pluriformChartMeasure sX hm s U z hz W hW hWo hWz).restrict (W ∩ W') =
        (pluriformChartMeasure sX hm s U' z' hz' W' hW' hWo' hWz').restrict (W ∩ W')) ∧
    -- (2) they glue to a unique measure on `X^an`
    (∃! μ : Measure (ComplexPoints sX),
      ∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
        (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
          (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
        (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
        (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
        μ.restrict W = pluriformChartMeasure sX hm s U z hz W hW hWo hWz) ∧
    -- (3) homogeneity `μ_{cs} = |c|^{2/m} μ_s`
    (∀ (c : ℂ) (μ μ' : Measure (ComplexPoints sX)),
      (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
        (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
          (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
        (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
        (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
        μ.restrict W = pluriformChartMeasure sX hm s U z hz W hW hWo hWz) →
      (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
        (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
          (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
        (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
        (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
        μ'.restrict W = pluriformChartMeasure sX hm
          (@algebraMap ℂ X.functionField _ _ (MMP.Mori.functionFieldAlgebra sX) c • s)
          U z hz W hW hWo hWz) →
      μ' = ENNReal.ofReal (‖c‖ ^ (2 / m : ℝ)) • μ) ∧
    -- (4) naturality `μ_{g^*s} = g^*μ_s` under isomorphisms
    (∀ {Y : Scheme.{0}} (g : Y ⟶ X) [IsIso g]
      [AlgebraicGeometry.IsVariety ℂ (g ≫ sX)] [SmoothOfRelativeDimension n (g ≫ sX)]
      [MeasurableSpace (ComplexPoints (g ≫ sX))] [BorelSpace (ComplexPoints (g ≫ sX))]
      (μ : Measure (ComplexPoints sX)) (ν : Measure (ComplexPoints (g ≫ sX))),
      (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
        (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
          (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
        (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
        (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
        μ.restrict W = pluriformChartMeasure sX hm s U z hz W hW hWo hWz) →
      (∀ (V : Y.Opens) [Nonempty V] (z : Fin n → Γ(Y, V))
        (hz : Etale (AffineSpace.homOfVector (V.ι ≫ g ≫ sX)
          (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
        (W : Set (ComplexPoints (g ≫ sX))) (hW : W ⊆ chart V) (hWo : IsOpen W)
        (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hW y.2⟩)),
        ν.restrict W = pluriformChartMeasure (g ≫ sX) hm
          (MMP.Mori.pullbackRationalPluriForms sX g s) V z hz W hW hWo hWz) →
      ν.map (realize g rfl) = μ) := by
  refine ⟨fun U _ z hz W hW hWo hWz U' _ z' hz' W' hW' hWo' hWz' ↦
      chartMeasure_restrict_inter_eq sX hm s U z hz W hW hWo hWz U' z' hz' W' hW' hWo' hWz', ?_,
      ?_, ?_⟩
  · obtain ⟨μ, hμ⟩ := exists_isGlued sX hm s
    exact ⟨μ, hμ, fun μ' hμ' ↦ isGlued_unique sX hm s hμ' hμ⟩
  · intro c μ μ' hμ hμ'
    refine isGlued_unique sX hm _ hμ' ?_
    intro U _ z hz W hW hWo hWz
    rw [Measure.restrict_smul, hμ U z hz W hW hWo hWz, chartMeasure_smul]
  · intro Y g _ _ _ _ _ μ ν hμ hν
    exact isGlued_unique sX hm s (map_realize_isGlued sX hm s g ν hν) hμ

end MMP.Analytic.ComplexPoints

namespace MMP.Analytic.Proof_lem_mmp_analytic_pluriform_density_intrinsic

section OpenImmersion

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The realization of an open immersion over `ℂ` is an open embedding. -/
private lemma isOpenEmbedding_realize_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j] :
    IsOpenEmbedding (realize (sX := j ≫ sX) j rfl) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : Y.Over (Spec (.of ℂ)) := ⟨j ≫ sX⟩
  have : j.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have h : realize (sX := j ≫ sX) j rfl = (homeomorphUnderlyingSpace (X := X)).symm ∘
      MMP.UnderlyingSpace.map (K := ℂ) j ∘ homeomorphUnderlyingSpace (X := Y) :=
    rfl
  rw [h]
  exact (homeomorphUnderlyingSpace (X := X)).symm.isOpenEmbedding.comp
    ((MMP.UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) j).comp
      (homeomorphUnderlyingSpace (X := Y)).isOpenEmbedding)

/-- For a dominant `f`, the germ at the generic point of `f^*a` is the image of the germ of `a`
under `f^* : ℂ(X) → ℂ(Y)`. -/
private lemma germ_appLE_eq_functionFieldMap [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (hU : genericPoint X ∈ U)
    (hV : genericPoint Y ∈ V) (a : Γ(X, U)) :
    Y.presheaf.germ V (genericPoint Y) hV (f.appLE U V e a) =
      functionFieldMap f (X.presheaf.germ U (genericPoint X) hU a) := by
  rw [← germ_app_eq_functionFieldMap f U hU a (e hV), Scheme.Hom.appLE, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_res_apply]

/-- The density of `j^*φ` at `y` is the density of `φ` at `j(y)`, for an open immersion `j`. -/
private lemma pluriformDensity_functionFieldMap_of_isOpenImmersion [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j] (m : ℕ) (φ : X.functionField)
    (y : ComplexPoints (j ≫ sX)) :
    pluriformDensity (j ≫ sX) m (functionFieldMap j φ) y =
      pluriformDensity sX m φ (realize j rfl y) := by
  refine le_antisymm ?_ (pluriformDensity_realize_le j rfl m φ y)
  unfold pluriformDensity
  refine iSup_le fun V ↦ iSup_le fun a ↦ iSup_le fun hy ↦ iSup_le fun hg ↦ iSup_le fun hga ↦ ?_
  have e : V ≤ j ⁻¹ᵁ (j ''ᵁ V) := (Scheme.Hom.preimage_image_eq j V).ge
  have hg' : genericPoint X ∈ j ''ᵁ V := by
    rw [← map_genericPoint_of_isDominant j]; exact ⟨_, hg, rfl⟩
  have ha : j.appLE (j ''ᵁ V) V e ((j.appIso V).inv a) = a := by
    rw [← Scheme.Hom.appIso_hom']; exact Iso.inv_hom_id_apply _ _
  refine le_iSup_of_le (j ''ᵁ V) <| le_iSup_of_le ((j.appIso V).inv a) <|
    le_iSup_of_le (mem_chart_realize_of_le j rfl e hy) <| le_iSup_of_le hg' <|
    le_iSup_of_le ?_ (le_of_eq ?_)
  · apply (functionFieldMap j).injective
    rw [← germ_appLE_eq_functionFieldMap j _ V e hg' hg, ha, hga]
  · rw [← eval_appLE_realize j rfl (j ''ᵁ V) V e _ y hy, ha]

end OpenImmersion

/-- Transporting a chart along an open embedding `r` and pushing forward again restricts the
chart's measure to the range of `r`. -/
private lemma map_map_comap_comp_restrictPreimage_of_isOpenEmbedding {α β γ : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    {r : α → β} (hr : IsOpenEmbedding r) {W : Set β} (hWo : IsOpen W) (ζ : W → γ)
    (hζ : IsOpenEmbedding ζ) (μ : Measure γ) :
    ((μ.comap (ζ ∘ W.restrictPreimage r)).map Subtype.val).map r =
      ((μ.comap ζ).map Subtype.val).restrict (Set.range r) := by
  have hρ := (hr.restrictPreimage W).measurableEmbedding
  have hζm := hζ.measurableEmbedding
  have hval : (r : α → β) ∘ (Subtype.val : r ⁻¹' W → α) = Subtype.val ∘ W.restrictPreimage r :=
    rfl
  rw [Measure.map_map hr.continuous.measurable measurable_subtype_coe, hval,
    ← Measure.map_map measurable_subtype_coe hρ.measurable,
    ← Measure.comap_comap hρ.measurableSet_image' hζ.injective hζm.measurableSet_image',
    hρ.map_comap, (MeasurableEmbedding.subtype_coe hWo.measurableSet).restrict_map,
    Set.range_restrictPreimage]

/-- For an open immersion `j`, the chart measure of `j^*s` on `j^{-1}(W)` pushes forward to the
chart measure of `s` on `W`, restricted to the image of `j`. -/
private lemma chartMeasure_map_realize_of_isOpenImmersion {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [MeasurableSpace (ComplexPoints sX)]
    [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m) (s : MMP.Mori.RationalPluriForms sX n m)
    {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [AlgebraicGeometry.IsVariety ℂ (j ≫ sX)] [SmoothOfRelativeDimension n (j ≫ sX)]
    [MeasurableSpace (ComplexPoints (j ≫ sX))] [BorelSpace (ComplexPoints (j ≫ sX))]
    (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩))
    [Nonempty (j ⁻¹ᵁ U)]
    (hz' : Etale (AffineSpace.homOfVector ((j ⁻¹ᵁ U).ι ≫ j ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ (j ⁻¹ᵁ U).topIso.inv (j.app U (z i.down)))))
    (hW' : realize j rfl ⁻¹' W ⊆ chart (j ⁻¹ᵁ U)) (hWo' : IsOpen (realize j rfl ⁻¹' W))
    (hWz' : IsOpenEmbedding (fun y : (realize j rfl ⁻¹' W : Set (ComplexPoints (j ≫ sX))) ↦
      fun i ↦ ComplexPoints.eval (j ⁻¹ᵁ U) (j.app U (z i)) ⟨y.1, hW' y.2⟩)) :
    (pluriformChartMeasure (j ≫ sX) hm (MMP.Mori.pullbackRationalPluriForms sX j s) (j ⁻¹ᵁ U)
      (fun i ↦ j.app U (z i)) hz' _ hW' hWo' hWz').map (realize j rfl) =
      (pluriformChartMeasure sX hm s U z hz W hW hWo hWz).restrict (Set.range (realize j rfl)) := by
  have hr := isOpenEmbedding_realize_of_isOpenImmersion (sX := sX) j
  have hζ : (fun y : (realize j rfl ⁻¹' W : Set (ComplexPoints (j ≫ sX))) ↦
      fun i ↦ ComplexPoints.eval (j ⁻¹ᵁ U) (j.app U (z i)) ⟨y.1, hW' y.2⟩) =
      (fun y : W ↦ fun i ↦ ComplexPoints.eval U (z i) ⟨y.1, hW y.2⟩) ∘
        W.restrictPreimage (realize j rfl) := by
    funext y i
    exact eval_app_realize j rfl U (z i) y.1 (hW' y.2)
  have hbij : Function.Bijective (functionFieldMap j) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion j ⊤ ⟨genericPoint Y, trivial⟩
  have hρ : pluriformDensity (j ≫ sX) m (pluriformCoeff (j ≫ sX)
      (MMP.Mori.pullbackRationalPluriForms sX j s) (j ⁻¹ᵁ U) (fun i ↦ j.app U (z i))) =
      pluriformDensity sX m (pluriformCoeff sX s U z) ∘ realize j rfl := funext fun y ↦ by
    rw [pluriformCoeff_pullback_of_bijective j hbij,
      pluriformDensity_functionFieldMap_of_isOpenImmersion]
    rfl
  unfold pluriformChartMeasure
  rw [hζ, hρ, map_withDensity_comp_of_measurableEmbedding hr.measurableEmbedding,
    map_map_comap_comp_restrictPreimage_of_isOpenEmbedding hr hWo _ hWz,
    restrict_withDensity hr.isOpen_range.measurableSet]

end MMP.Analytic.Proof_lem_mmp_analytic_pluriform_density_intrinsic

namespace MMP.Analytic.ComplexPoints

open MMP.Analytic.Proof_lem_mmp_analytic_pluriform_density_intrinsic in
/-- **The glued measure of a rational pluriform restricts along open immersions.** Let `X` be a
smooth complex variety of dimension `n`, `m > 0`, `s` a rational `m`-canonical form on `X` and
`j : U ⟶ X` an open immersion. If `μ` is the glued measure `μ_s` of `s` on `X^an` and `ν` that of
`j^*s` on `U^an` (each restricts on every étale chart to the chart measure), then the push-forward
of `ν` along `U^an → X^an` is the restriction of `μ` to the image `U^an ⊆ X^an`:
`μ_{j^*s} = μ_s|_{U^an}`. -/
public theorem map_realize_eq_restrict_of_isOpenImmersion {X U : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [MeasurableSpace (ComplexPoints sX)]
    [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m) (s : MMP.Mori.RationalPluriForms sX n m)
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [AlgebraicGeometry.IsVariety ℂ (j ≫ sX)] [SmoothOfRelativeDimension n (j ≫ sX)]
    [MeasurableSpace (ComplexPoints (j ≫ sX))] [BorelSpace (ComplexPoints (j ≫ sX))]
    (μ : Measure (ComplexPoints sX)) (ν : Measure (ComplexPoints (j ≫ sX)))
    (hμ : ∀ (V : X.Opens) [Nonempty V] (z : Fin n → Γ(X, V))
      (hz : Etale (AffineSpace.homOfVector (V.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart V) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hW y.2⟩)),
      μ.restrict W = pluriformChartMeasure sX hm s V z hz W hW hWo hWz)
    (hν : ∀ (V : U.Opens) [Nonempty V] (z : Fin n → Γ(U, V))
      (hz : Etale (AffineSpace.homOfVector (V.ι ≫ j ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
      (W : Set (ComplexPoints (j ≫ sX))) (hW : W ⊆ chart V) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hW y.2⟩)),
      ν.restrict W = pluriformChartMeasure (j ≫ sX) hm
        (MMP.Mori.pullbackRationalPluriForms sX j s) V z hz W hW hWo hWz) :
    ν.map (realize j rfl) = μ.restrict (Set.range (realize j rfl)) := by
  have hr := isOpenEmbedding_realize_of_isOpenImmersion (sX := sX) j
  have hRm : MeasurableSet (Set.range (realize j rfl)) := hr.isOpen_range.measurableSet
  refine eq_of_forall_restrict_chart_eq sX (n := n) _ _ fun V _ z hz W hW hWo hWz ↦ ?_
  have hW' : realize j rfl ⁻¹' W ⊆ chart (j ⁻¹ᵁ V) := fun y hy ↦
    (mem_chart_preimage_iff j rfl V y).2 (hW hy)
  rw [hr.measurableEmbedding.restrict_map, Measure.restrict_restrict hWo.measurableSet,
    Set.inter_comm, ← Measure.restrict_restrict hRm, hμ V z hz W hW hWo hWz]
  rcases isEmpty_or_nonempty (j ⁻¹ᵁ V) with hV | hV
  · have h0 : realize j rfl ⁻¹' W = ∅ := Set.eq_empty_of_forall_notMem fun y hy ↦
      hV.false ⟨_, mem_of_mem_chart (j ≫ sX) (hW' hy) (Classical.arbitrary _)⟩
    have h1 : Set.range (realize j rfl) ∩ W = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨y, rfl⟩, hy⟩
      have : y ∈ realize j rfl ⁻¹' W := hy
      rw [h0] at this
      exact this
    rw [h0, Measure.restrict_empty, Measure.map_zero, ← hμ V z hz W hW hWo hWz,
      Measure.restrict_restrict hRm, h1, Measure.restrict_empty]
  · have hWo' : IsOpen (realize j rfl ⁻¹' W) := hWo.preimage hr.continuous
    have hWz' : IsOpenEmbedding (fun y : (realize j rfl ⁻¹' W : Set (ComplexPoints (j ≫ sX))) ↦
        fun i ↦ eval (j ⁻¹ᵁ V) (j.app V (z i)) ⟨y.1, hW' y.2⟩) := by
      have hζ : (fun y : (realize j rfl ⁻¹' W : Set (ComplexPoints (j ≫ sX))) ↦
          fun i ↦ eval (j ⁻¹ᵁ V) (j.app V (z i)) ⟨y.1, hW' y.2⟩) =
          (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hW y.2⟩) ∘
            W.restrictPreimage (realize j rfl) := by
        funext y i
        exact eval_app_realize j rfl V (z i) y.1 (hW' y.2)
      rw [hζ]
      exact hWz.comp (hr.restrictPreimage W)
    have hz' := etale_pullback_coords (sX := sX) j V z hz
    rw [hν (j ⁻¹ᵁ V) (fun i ↦ j.app V (z i)) hz' _ hW' hWo' hWz']
    exact chartMeasure_map_realize_of_isOpenImmersion sX hm s j V z hz W hW hWo hWz hz' hW' hWo'
      hWz'

end MMP.Analytic.ComplexPoints

end

/-!
## Proper Zariski closed subsets are null for pluriform measures

Let `X` be a smooth irreducible complex variety and `Z ⊊ X` a proper Zariski closed subset.
Then `Z^an`, the set of `ℂ`-points of `X` landing in `Z`, has measure zero for every chart
measure `|φ|^{2/m} dλ` of a rational pluriform `s`. Conversely, if `s ≠ 0`, the chart measure
of `s` on a chart `W` charges every open subset of `X^an` meeting `W`.

### Main results

* `MMP.Analytic.ComplexPoints.pluriformChartMeasure_proper_closed_null`: both statements.

### Implementation notes

* `Z^an` is written `{x | Set.range x.hom.base ⊆ Z}`: a `ℂ`-point `x : Spec ℂ ⟶ X` lies over
  `Z` when its (unique) image point lies in `Z`.
* The measure `μ_s` on `X^an` is glued from the chart measures
  `MMP.Analytic.ComplexPoints.pluriformChartMeasure`, and it agrees with the chart measure on
  the chart `W`. The statements are therefore made chart by chart: nullity for every chart
  measure (which gives nullity for `μ_s`, as countably many charts cover `X^an`), and
  positivity of the chart measure of `s ≠ 0` on every open set meeting its chart.
* The measurable structure on `X^an` is the Borel one (`BorelSpace`).

### References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Analytic.Proof_lem_mmp_analytic_proper_closed_null

/-- Lebesgue measure on `ℂⁿ` transported to the chart `W` and pushed to `X^an`. -/
private noncomputable abbrev chartLebesgue {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [MeasurableSpace (ComplexPoints sX)] (U : X.Opens) (z : Fin n → Γ(X, U))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) : Measure (ComplexPoints sX) :=
  (Measure.comap (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)
      (volume : Measure (Fin n → ℂ))).map Subtype.val

private theorem chartLebesgue_pos {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)]
    (U : X.Opens) (z : Fin n → Γ(X, U))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩))
    (V : Set (ComplexPoints sX)) (hV : IsOpen V) (hVW : (V ∩ W).Nonempty) :
    0 < chartLebesgue sX U z W hW V := by
  have hme := hWz.measurableEmbedding
  rw [chartLebesgue, Measure.map_apply measurable_subtype_coe hV.measurableSet,
    hme.comap_apply]
  obtain ⟨x, hxV, hxW⟩ := hVW
  exact (hWz.isOpenMap _ (hV.preimage continuous_subtype_val)).measure_pos _
    ⟨_, ⟨⟨x, hxW⟩, hxV, rfl⟩⟩

open Metric Set Filter in
/-- The zeros of a holomorphic function on a convex open set, not vanishing at some point of it,
form a Lebesgue-null set (polar coordinates around that point). -/
private theorem volume_inter_preimage_zero_of_convex {n : ℕ} {G : (Fin n → ℂ) → ℂ}
    {B : Set (Fin n → ℂ)} (hBo : IsOpen B) (hBc : Convex ℝ B) (hG : DifferentiableOn ℂ G B)
    {p : Fin n → ℂ} (hp : p ∈ B) (hGp : G p ≠ 0) :
    volume (B ∩ G ⁻¹' {0}) = 0 := by
  set S := B ∩ G ⁻¹' {0} with hSdef
  have hSm : MeasurableSet S := by
    have h1 : IsOpen (B ∩ G ⁻¹' {0}ᶜ) :=
      hG.continuousOn.isOpen_inter_preimage hBo isOpen_compl_singleton
    have : S = B \ (B ∩ G ⁻¹' {0}ᶜ) := by ext x; simp [S]
    rw [this]; exact hBo.measurableSet.diff h1.measurableSet
  set S' : Set (Fin n → ℂ) := (fun v ↦ p + v) ⁻¹' S with hS'def
  have hS'm : MeasurableSet S' := (measurable_const_add p) hSm
  rw [← measure_preimage_add volume p S]
  change volume S' = 0
  have h0 : S' ⊆ ({0}ᶜ : Set (Fin n → ℂ)) := by
    intro v hv h0
    simp only [mem_singleton_iff] at h0
    subst h0
    exact hGp (by simpa [S', S] using hv.2)
  set h := homeomorphUnitSphereProd (Fin n → ℂ)
  have hemb : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set (Fin n → ℂ)) → _) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton 0).compl
  have e1 : volume S' = (volume.comap Subtype.val) (Subtype.val ⁻¹' S' :
      Set ({0}ᶜ : Set (Fin n → ℂ))) := by
    rw [hemb.comap_apply, Subtype.image_preimage_coe, inter_eq_right.2 h0]
  set T : Set (sphere (0 : Fin n → ℂ) 1 × Ioi (0 : ℝ)) := {q | (h.symm q : Fin n → ℂ) ∈ S'}
  have hT : MeasurableSet T :=
    (continuous_subtype_val.comp h.symm.continuous).measurable hS'm
  have e2 : (Subtype.val ⁻¹' S' : Set ({0}ᶜ : Set (Fin n → ℂ))) = h ⁻¹' T := by
    ext v; simp [T]
  rw [e1, e2, (volume.measurePreserving_homeomorphUnitSphereProd).measure_preimage
    hT.nullMeasurableSet]
  rw [Measure.measure_prod_null hT]
  refine Filter.Eventually.of_forall fun u ↦ ?_
  -- the slice
  set D : Set ℂ := {t | p + t • (u : Fin n → ℂ) ∈ B}
  set g : ℂ → ℂ := fun t ↦ G (p + t • (u : Fin n → ℂ))
  have hline : Continuous fun t : ℂ ↦ p + t • (u : Fin n → ℂ) := by fun_prop
  have hDo : IsOpen D := hBo.preimage hline
  have hDc : Convex ℝ D := by
    intro a ha b hb α β hα hβ hαβ
    have := hBc ha hb hα hβ hαβ
    have h1 : (α : ℂ) + β = 1 := by exact_mod_cast hαβ
    show p + (α • a + β • b) • (u : Fin n → ℂ) ∈ B
    convert this using 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    linear_combination (-(p i)) * h1
  have hg : AnalyticOnNhd ℂ g D :=
    (hG.comp (show Differentiable ℂ fun t : ℂ ↦ p + t • (u : Fin n → ℂ) by
      fun_prop).differentiableOn fun t ht ↦ ht).analyticOnNhd hDo
  have hcount := MMP.SmoothLocusConnected.countable_inter_preimage_zero hg
    hDc.isPreconnected (t₀ := 0) (by simpa [D] using hp) (by simpa [g] using hGp)
  have hsl : (Prod.mk u ⁻¹' T).Countable := by
    refine (hcount.preimage (f := fun r : Ioi (0 : ℝ) ↦ ((r : ℝ) : ℂ)) ?_).mono ?_
    · intro a b hab; exact Subtype.ext (by simpa using hab)
    · intro r hr
      simp only [T, mem_preimage, mem_ofPred_eq, h, homeomorphUnitSphereProd_symm_apply_coe] at hr
      refine ⟨hr.1, ?_⟩
      simpa [g, Complex.coe_smul] using hr.2
  have hν : (Measure.comap Subtype.val volume : Measure (Ioi (0:ℝ))) (Prod.mk u ⁻¹' T) = 0 := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply]
    exact (hsl.image _).measure_zero _
  exact withDensity_absolutelyContinuous _ _ hν

open Metric Set Filter in
/-- The zeros of a holomorphic function on an open set, with empty interior, are Lebesgue-null. -/
private theorem volume_inter_preimage_zero {n : ℕ} {G : (Fin n → ℂ) → ℂ} {O : Set (Fin n → ℂ)}
    (hO : IsOpen O) (hG : DifferentiableOn ℂ G O) (hint : interior (O ∩ G ⁻¹' {0}) = ∅) :
    volume (O ∩ G ⁻¹' {0}) = 0 := by
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x hx.1
  have hne : ∃ p ∈ ball x ε, G p ≠ 0 := by
    by_contra! H
    have : ball x ε ⊆ interior (O ∩ G ⁻¹' {0}) :=
      interior_maximal (fun y hy ↦ ⟨hball hy, H y hy⟩) isOpen_ball
    rw [hint] at this
    exact this (mem_ball_self hε)
  obtain ⟨p, hp, hGp⟩ := hne
  refine ⟨ball x ε ∩ G ⁻¹' {0}, ?_,
    volume_inter_preimage_zero_of_convex isOpen_ball (convex_ball x ε) (hG.mono hball) hp hGp⟩
  exact mem_nhdsWithin.2 ⟨ball x ε, isOpen_ball, mem_ball_self hε, fun y hy ↦ ⟨hy.1, hy.2.2⟩⟩

/-- For an étale map of domains `R → A`, every nonzero `f ∈ A` divides the image of some
nonzero `r ∈ R`. -/
private theorem exists_ne_zero_mem_span_of_etale {R A : Type} [CommRing R] [IsDomain R] [CommRing A]
    [IsDomain A] (φ : R →+* A) (hφ : φ.Etale) {f : A} (hf : f ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ φ r ∈ Ideal.span {f} := by
  letI := φ.toAlgebra
  haveI : Algebra.Etale R A := hφ
  by_contra! H
  set M : Submonoid A := (nonZeroDivisors R).map φ
  have hdisj : Disjoint (Ideal.span {f} : Set A) M := by
    rw [Set.disjoint_left]
    rintro a ha ⟨r, hr, rfl⟩
    exact H r (nonZeroDivisors.ne_zero hr) ha
  obtain ⟨Q, hQ, hfQ, hQM⟩ := Ideal.exists_le_prime_disjoint _ M hdisj
  have hQ0 : (⊥ : Ideal A) = Q := by
    refine Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) ⊥ Q bot_le ?_
    ext r
    simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h; rw [h]; exact zero_mem _
    · intro h
      by_contra hr
      have hr' : r ≠ 0 := fun h0 ↦ hr (by rw [h0, map_zero])
      exact Set.disjoint_left.1 hQM h ⟨r, mem_nonZeroDivisors_of_ne_zero hr', rfl⟩
  have : f ∈ (⊥ : Ideal A) := hQ0 ▸ hfQ (Ideal.mem_span_singleton_self f)
  exact hf (by simpa using this)

/-- Evaluating the image of a polynomial in the coordinates at a `ℂ`-point evaluates the
polynomial at the coordinates of the point. -/
private theorem evalHom_eval₂Hom {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    (U : X.Opens) (z : Fin n → Γ(X, U)) (V : X.Opens) (hVU : V ≤ U) (y : chart (sX := sX) V)
    (r : MvPolynomial (ULift.{0} (Fin n)) Γ(Spec (.of ℂ), ⊤)) :
    evalHom V y (MvPolynomial.eval₂Hom (sX.appLE ⊤ V le_top).hom
        (fun i : ULift.{0} (Fin n) ↦ X.presheaf.map (homOfLE hVU).op (z i.down)) r) =
      MvPolynomial.eval (fun i : ULift.{0} (Fin n) ↦ eval U (z i.down) ⟨y.1, chart_mono hVU y.2⟩)
        (MvPolynomial.map (Scheme.ΓSpecIso (.of ℂ)).hom.hom r) := by
  rw [MvPolynomial.eval_map, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  have h1 : (evalHom V y).comp (sX.appLE ⊤ V le_top).hom = (Scheme.ΓSpecIso (.of ℂ)).hom.hom := by
    have key : ∀ (g : Spec (.of ℂ) ⟶ Spec (.of ℂ)) (_ : g = 𝟙 _) (e : ⊤ ≤ g ⁻¹ᵁ ⊤),
        g.appLE ⊤ ⊤ e = 𝟙 _ := by
      rintro _ rfl e
      simp [Scheme.Hom.appLE]
      rfl
    have h2 : sX.appLE ⊤ V le_top ≫ y.1.hom.appLE V ⊤ y.2.ge = 𝟙 _ :=
      (Scheme.Hom.appLE_comp_appLE y.1.hom sX ⊤ V ⊤ _ _).trans
        (key _ y.1.hom_comp_structure _)
    simp only [evalHom]
    rw [RingHom.comp_assoc, ← CommRingCat.hom_comp, h2]
    rfl
  rw [h1]
  simp only [MvPolynomial.coe_eval₂Hom]
  congr 1
  funext i
  exact (evalHom_res hVU y (z i.down)).symm

/-- A nonzero regular function on an integral complex variety does not vanish identically on a
nonempty open subset of a chart of étale coordinates. -/
private theorem not_forall_eval_eq_zero {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [IsIntegral X] (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩))
    (U' : X.Opens) (f : Γ(X, U')) (hf : f ≠ 0) (Ω : Set (ComplexPoints sX)) (hΩo : IsOpen Ω)
    (hΩW : Ω ⊆ W) (hΩU' : Ω ⊆ chart U') (hΩ : Ω.Nonempty)
    (h0 : ∀ y (hy : y ∈ Ω), eval U' f ⟨y, hΩU' hy⟩ = 0) : False := by
  obtain ⟨y₀, hy₀⟩ := hΩ
  have hp : y₀.toScheme ∈ U ⊓ U' :=
    ⟨mem_chart_iff.1 (hW (hΩW hy₀)), mem_chart_iff.1 (hΩU' hy₀)⟩
  obtain ⟨V, hVa, hpV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hp
  have hVU : V ≤ U := hVle.trans inf_le_left
  have hVU' : V ≤ U' := hVle.trans inf_le_right
  haveI : Nonempty V := ⟨⟨_, hpV⟩⟩
  set ζ : W → (Fin n → ℂ) := fun y ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩
  set Ω' : Set (ComplexPoints sX) := Ω ∩ chart V
  have hΩ'o : IsOpen Ω' :=
    hΩo.inter (Proof_lem_mmp_analytic_pluriform_density_intrinsic.isOpen_chart sX V)
  have hy₀' : y₀ ∈ Ω' := ⟨hy₀, mem_chart_iff.2 hpV⟩
  set O' : Set (Fin n → ℂ) := ζ '' {y : W | y.1 ∈ Ω'}
  have hO'o : IsOpen O' := hWz.isOpenMap _ (hΩ'o.preimage continuous_subtype_val)
  -- the algebra
  have hφ := etale_eval₂Hom_of_etale_homOfVector sX U z hz V hVa hVU
  set f' := X.presheaf.map (homOfLE hVU').op f
  have hf' : f' ≠ 0 := fun h ↦ hf (map_injective_of_isIntegral X (homOfLE hVU') (by
    rw [map_zero]; exact h))
  obtain ⟨r, hr, hrf⟩ := exists_ne_zero_mem_span_of_etale _ hφ hf'
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hrf
  set r' := MvPolynomial.map (Scheme.ΓSpecIso (.of ℂ)).hom.hom r
  have hr' : r' ≠ 0 := fun h ↦ hr (MvPolynomial.map_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of ℂ)).hom).1
      (by rw [map_zero]; exact h))
  have hvan : ∀ y (hy : y ∈ Ω'),
      MvPolynomial.eval (fun i : ULift.{0} (Fin n) ↦ eval U (z i.down) ⟨y, hW (hΩW hy.1)⟩) r' =
        0 := by
    intro y hy
    have h1 := evalHom_eval₂Hom sX U z V hVU ⟨y, hy.2⟩ r
    rw [← ha, map_mul] at h1
    have h2 : evalHom V ⟨y, hy.2⟩ f' = 0 := by
      rw [← evalHom_res hVU' ⟨y, hy.2⟩ f]; exact h0 y hy.1
    rw [h2, mul_zero] at h1
    exact h1.symm
  obtain ⟨x, hxO, hx⟩ :=
    (MMP.SmoothLocusConnected.dense_setOf_eval_ne_zero hr').inter_open_nonempty
    ((fun x : ULift.{0} (Fin n) → ℂ ↦ fun i ↦ x ⟨i⟩) ⁻¹' O')
    (hO'o.preimage (by fun_prop)) ⟨fun i ↦ ζ ⟨y₀, hΩW hy₀⟩ i.down, ⟨⟨y₀, hΩW hy₀⟩, hy₀', rfl⟩⟩
  obtain ⟨y, hy, hyx⟩ := hxO
  apply hx
  have hx' : x = fun i : ULift.{0} (Fin n) ↦ ζ y i.down := by
    funext i; exact (congrFun hyx i.down).symm
  rw [hx']
  exact hvan y.1 hy
/-- An alternating map in `n` variables on a module with a basis indexed by `Fin n` vanishes as
soon as it vanishes on the basis. -/
private theorem alternatingMap_eq_zero_of_apply_basis {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {n : ℕ}
    (b : Module.Basis (Fin n) A M) (g : M [⋀^Fin n]→ₗ[A] N) (hg : g b = 0) : g = 0 := by
  refine Module.Basis.ext_alternating b fun i h ↦ ?_
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change g (b ∘ σ) = (0 : M [⋀^Fin n]→ₗ[A] N) (b ∘ σ)
  rw [g.map_perm, hg, smul_zero]
  rfl

/-- For a basis `b` of a free module `M` of rank `n`, the wedge `b₁ ∧ ⋯ ∧ bₙ` spans `⋀ⁿ M`. -/
private theorem span_ιMulti_basis_eq_top {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {n : ℕ} (b : Module.Basis (Fin n) A M) :
    Submodule.span A {exteriorPower.ιMulti A n (b : Fin n → M)} = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  have hv := congrArg (fun g ↦ g v) (alternatingMap_eq_zero_of_apply_basis b
    ((Submodule.span A {exteriorPower.ιMulti A n (b : Fin n → M)}).mkQ.compAlternatingMap
      (exteriorPower.ιMulti A n)) (by
      simpa using Submodule.mem_span_singleton_self _))
  simpa using hv

/-- For a basis `b` of a free module `M` of rank `n` over a nontrivial ring, the wedge
`b₁ ∧ ⋯ ∧ bₙ` is nonzero. -/
private theorem ιMulti_basis_ne_zero {A M : Type*} [CommRing A] [Nontrivial A] [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) :
    exteriorPower.ιMulti A n (b : Fin n → M) ≠ 0 := by
  intro h0
  have htop := exteriorPower.ιMulti_span (R := A) (n := n) (M := M)
  rw [alternatingMap_eq_zero_of_apply_basis b _ h0] at htop
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp⟩
  apply (b.exteriorPower n).ne_zero s
  have : (b.exteriorPower n) s ∈ (⊤ : Submodule A (⋀[A]^n M)) := trivial
  rw [← htop] at this
  have hsub : Set.range (0 : M [⋀^Fin n]→ₗ[A] ⋀[A]^n M) ⊆ {0} := by
    rintro _ ⟨v, rfl⟩; rfl
  simpa using Submodule.span_mono hsub this

/-- Étale coordinates `z` on `U` give a basis `dz₁, …, dzₙ` of `Ω_{ℂ(X)/ℂ}`. -/
private theorem _root_.MMP.Analytic.exists_basis_kaehler_functionField
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {n : ℕ} [IsIntegral X] (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ∃ b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ],
      ∀ i, b i = KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField U (z i)) := by
  letI := MMP.Mori.functionFieldAlgebra sX
  obtain ⟨u⟩ := ‹Nonempty U›
  obtain ⟨V, hVa, hpV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens u.2
  haveI : Nonempty V := ⟨⟨_, hpV⟩⟩
  letI : Algebra ℂ Γ(X, V) := MMP.Mori.sectionAlgebra sX V
  haveI : IsScalarTower ℂ Γ(X, V) X.functionField :=
    MMP.Mori.isScalarTower_section_functionField sX V
  haveI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hVa
  let w : ULift.{0} (Fin n) → Γ(X, V) := fun i ↦ X.presheaf.map (homOfLE hVU).op (z i.down)
  letI : Algebra (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V) :=
    (MvPolynomial.aeval w).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((MvPolynomial.aeval w).commutes c).symm
  letI : Algebra (MvPolynomial (ULift.{0} (Fin n)) ℂ) X.functionField :=
    ((algebraMap Γ(X, V) X.functionField).comp
      (algebraMap (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower ℂ (MvPolynomial (ULift.{0} (Fin n)) ℂ) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply ℂ Γ(X, V) X.functionField,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V)]
      rfl
  haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V) := by
    have hφ := etale_eval₂Hom_of_etale_homOfVector sX U z hz V hVa hVU
    let e : ℂ ≃+* Γ(Spec (.of ℂ), ⊤) :=
      (Scheme.ΓSpecIso (.of ℂ)).symm.commRingCatIsoToRingEquiv
    have heq : algebraMap (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V) =
        (MvPolynomial.eval₂Hom (sX.appLE ⊤ V le_top).hom w).comp
          (MvPolynomial.mapEquiv (ULift.{0} (Fin n)) e).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
          MvPolynomial.eval₂Hom_C]
        change MvPolynomial.aeval w (MvPolynomial.C c) = _
        rw [MvPolynomial.aeval_C]
        rfl
      · intro i
        simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, MvPolynomial.mapEquiv_apply, MvPolynomial.map_X,
          MvPolynomial.eval₂Hom_X']
        exact MvPolynomial.aeval_X w i
    have hE : (algebraMap (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V)).Etale := by
      rw [heq]
      exact RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.of_bijective (MvPolynomial.mapEquiv _ e).bijective) hφ
    have : Algebra.Etale (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V) := hE
    infer_instance
  haveI : Algebra.FormallyEtale Γ(X, V) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(X, V))
  haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin n)) ℂ) X.functionField :=
    Algebra.FormallyEtale.comp (MvPolynomial (ULift.{0} (Fin n)) ℂ) Γ(X, V) X.functionField
  let b₀ := ((KaehlerDifferential.mvPolynomialBasis ℂ (ULift.{0} (Fin n))).baseChange
      X.functionField).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ (MvPolynomial (ULift.{0} (Fin n)) ℂ)
      X.functionField)
  refine ⟨b₀.reindex Equiv.ulift, fun i ↦ ?_⟩
  simp only [b₀, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  congr 1
  change algebraMap Γ(X, V) X.functionField (MvPolynomial.aeval w (MvPolynomial.X _)) = _
  rw [MvPolynomial.aeval_X]
  change X.germToFunctionField V (X.presheaf.map (homOfLE hVU).op (z _)) = _
  simp [Scheme.germToFunctionField]

/-- The coefficient of a nonzero rational pluriform along `(dz₁ ∧ ⋯ ∧ dzₙ)^{⊗m}` is nonzero. -/
private theorem pluriformCoeff_ne_zero {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [IsIntegral X] {m : ℕ} (s : MMP.Mori.RationalPluriForms sX n m) (U : X.Opens) [Nonempty U]
    (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (hs : s ≠ 0) :
    pluriformCoeff sX s U z ≠ 0 := by
  letI := MMP.Mori.functionFieldAlgebra sX
  obtain ⟨b, hb⟩ := exists_basis_kaehler_functionField sX U z hz
  have hb' : (b : Fin n → _) =
      fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField U (z i)) := funext hb
  have hspan := span_ιMulti_basis_eq_top b
  have hne := ιMulti_basis_ne_zero b
  rw [hb'] at hspan hne
  unfold pluriformCoeff
  dsimp only
  rw [dif_pos ⟨hspan, hne⟩]
  intro h0
  apply hs
  set B := MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hspan hne) (m : ℤ)
  have : B.repr s = 0 := Finsupp.ext fun u ↦ by cases u; exact h0
  exact B.repr.map_eq_zero_iff.1 this

/- The two geometric inputs.

`chartLebesgue_complexPoints_null`: near a point of `Z^an ∩ W`, take an affine open `U'` and a
nonzero `f ∈ Γ(X, U')` with `Z ∩ U' ⊆ V(f)`. On the chart, `f` is a holomorphic function `G` of
the coordinates (`etaleCoordinate_atlas`, clause 3); the zeros of `G` have empty interior
(`not_forall_eval_eq_zero`), hence are Lebesgue-null (`volume_inter_preimage_zero`).

`pluriformDensity_pos_off_closed`: for `s ≠ 0` the coefficient `φ` is nonzero
(`pluriformCoeff_ne_zero`), so it is the germ of some `g` on `V`, and the density is positive on
`D(g)(ℂ)`; take `Z = D(g)ᶜ`. -/

private theorem chartLebesgue_complexPoints_null {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)]
    (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩))
    (Z : Set X) (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    chartLebesgue sX U z W hW {x : ComplexPoints sX | Set.range x.hom.base ⊆ Z} = 0 := by
  classical
  have hval : MeasurableEmbedding (Subtype.val : W → ComplexPoints sX) :=
    MeasurableEmbedding.subtype_coe hWo.measurableSet
  rw [chartLebesgue, hval.map_apply, hWz.measurableEmbedding.comap_apply]
  set ζ : W → (Fin n → ℂ) := fun y ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩ with hζ
  set S := {x : ComplexPoints sX | Set.range x.hom.base ⊆ Z}
  refine measure_null_of_locally_null _ ?_
  rintro _ ⟨y, hyS, rfl⟩
  obtain ⟨U', hU'a, hyU', -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show y.1.toScheme ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨q, hqU', hqZ⟩ : ((U' : Set X) ∩ Zᶜ).Nonempty :=
    nonempty_preirreducible_inter U'.isOpen hZ.isOpen_compl ⟨_, hyU'⟩ (Set.nonempty_compl.2 hZne)
  obtain ⟨f, hfle, hqf⟩ := IsAffineOpen.exists_basicOpen_le hU'a
    (V := U' ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) ⟨q, hqU', hqZ⟩ hqU'
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hqf
    exact hqf
  obtain ⟨G, hGd, hGf⟩ := (etaleCoordinate_atlas sX (n := n)).2.2 U z hz W hW hWo hWz U' f
  set O := ζ '' {y : W | y.1 ∈ chart U'}
  have hOo : IsOpen O := hWz.isOpenMap _
    ((Proof_lem_mmp_analytic_pluriform_density_intrinsic.isOpen_chart sX U').preimage
      continuous_subtype_val)
  have hfS : ∀ y' : W, y'.1 ∈ S → ∀ hy' : y'.1 ∈ chart U', eval U' f ⟨y'.1, hy'⟩ = 0 := by
    intro y' hy'S hy'
    by_contra hne
    have hmem := (toScheme_mem_basicOpen_iff ⟨y'.1, hy'⟩ f).2 hne
    exact (hfle hmem).2 (hy'S ⟨default, rfl⟩)
  have hsub : O ∩ ζ '' (Subtype.val ⁻¹' S) ⊆ O ∩ G ⁻¹' {0} := by
    rintro _ ⟨⟨y'', hy''U', rfl⟩, ⟨y', hy'S, hy'eq⟩⟩
    have : y' = y'' := hWz.injective hy'eq
    subst this
    refine ⟨⟨y', hy''U', rfl⟩, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hGf y' hy''U']
    exact hfS y' hy'S hy''U'
  have hint : interior (O ∩ G ⁻¹' {0}) = ∅ := by
    by_contra hne
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hBsub : interior (O ∩ G ⁻¹' {0}) ⊆ O ∩ G ⁻¹' {0} := interior_subset
    refine not_forall_eval_eq_zero sX U z hz W hW hWz U' f hf
      (Subtype.val '' (ζ ⁻¹' interior (O ∩ G ⁻¹' {0})))
      (hWo.isOpenMap_subtype_val _ (isOpen_interior.preimage hWz.continuous)) ?_ ?_ ?_ ?_
    · rintro _ ⟨y', -, rfl⟩; exact y'.2
    · rintro _ ⟨y', hy', rfl⟩
      obtain ⟨⟨y'', hy'', hyeq⟩, -⟩ := hBsub hy'
      rw [← hWz.injective hyeq]; exact hy''
    · obtain ⟨⟨y', -, hy'⟩, -⟩ := hBsub hw
      exact ⟨y'.1, y', by rw [Set.mem_preimage, hy']; exact hw, rfl⟩
    · rintro _ ⟨y', hy', rfl⟩
      obtain ⟨⟨y'', hy'', hyeq⟩, hG0⟩ := hBsub hy'
      have := hWz.injective hyeq; subst this
      rw [hGf y'' hy'']; exact hG0
  exact ⟨O ∩ G ⁻¹' {0}, mem_nhdsWithin.2 ⟨O, hOo, ⟨y, mem_chart_iff.2 hyU', rfl⟩, hsub⟩,
    volume_inter_preimage_zero hOo hGd hint⟩

/-- `y ↦ |g(y)|^{2/m}` on `V(ℂ)`, and `0` off it, is lower semicontinuous on `X^an`. -/
private theorem lowerSemicontinuous_iSup_mem_chart {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (p : ℝ) (hp : 0 ≤ p) (V : X.Opens) (g : Γ(X, V)) :
    LowerSemicontinuous fun y : ComplexPoints sX ↦
      ⨆ hy : y ∈ chart V, ENNReal.ofReal (‖eval V g ⟨y, hy⟩‖ ^ p) := by
  classical
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have hS : IsOpen (chart (sX := sX) V) :=
    Proof_lem_mmp_analytic_pluriform_density_intrinsic.isOpen_chart sX V
  let e : ComplexPoints sX → ℂ := fun y ↦ if hy : y ∈ chart V then eval V g ⟨y, hy⟩ else 0
  have hev : ContinuousOn e (chart (sX := sX) V) :=
    MMP.Analytic.InvertibleModule.continuousOn_evalExt V g
  have hK : ContinuousOn (fun y ↦ ENNReal.ofReal (‖e y‖ ^ p)) (chart (sX := sX) V) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((continuous_norm.comp_continuousOn hev).rpow_const fun _ _ ↦ Or.inr hp)
  intro y c hc
  simp only at hc ⊢
  by_cases hy : y ∈ chart (sX := sX) V
  · rw [iSup_pos hy] at hc
    have hc' : c < ENNReal.ofReal (‖e y‖ ^ p) := by simpa [e, dif_pos hy] using hc
    filter_upwards [(hK.continuousAt (hS.mem_nhds hy)).eventually (lt_mem_nhds hc'),
      hS.mem_nhds hy] with y' h1 h2
    rw [iSup_pos h2]
    simpa [e, dif_pos h2] using h1
  · simp [hy] at hc

/-- The density `|φ|^{2/m}` is lower semicontinuous on `X^an`. -/
private theorem lowerSemicontinuous_pluriformDensity {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] (m : ℕ) (φ : X.functionField) :
    LowerSemicontinuous (pluriformDensity sX m φ) := by
  unfold pluriformDensity
  refine lowerSemicontinuous_iSup fun V ↦ lowerSemicontinuous_iSup fun g ↦ ?_
  have : (fun y : ComplexPoints sX ↦ ⨆ (hy : y ∈ chart V) (hg : genericPoint X ∈ V)
      (_ : X.presheaf.germ V (genericPoint X) hg g = φ),
        ENNReal.ofReal (‖eval V g ⟨y, hy⟩‖ ^ (2 / m : ℝ))) =
      fun y ↦ ⨆ (hg : genericPoint X ∈ V) (_ : X.presheaf.germ V (genericPoint X) hg g = φ)
        (hy : y ∈ chart V), ENNReal.ofReal (‖eval V g ⟨y, hy⟩‖ ^ (2 / m : ℝ)) := by
    funext y
    rw [iSup_comm]
    exact iSup_congr fun _ ↦ iSup_comm
  rw [this]
  exact lowerSemicontinuous_iSup fun _ ↦ lowerSemicontinuous_iSup fun _ ↦
    lowerSemicontinuous_iSup_mem_chart sX _ (by positivity) V g

private theorem pluriformDensity_pos_off_closed {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX] {m : ℕ}
    (s : MMP.Mori.RationalPluriForms sX n m) (U : X.Opens) [Nonempty U]
    (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (hs : s ≠ 0) :
    ∃ Z : Set X, IsClosed Z ∧ Z ≠ Set.univ ∧ ∀ y : ComplexPoints sX,
      pluriformDensity sX m (pluriformCoeff sX s U z) y = 0 → Set.range y.hom.base ⊆ Z := by
  obtain ⟨V, hgV, g, hg⟩ := X.presheaf.exists_germ_eq (pluriformCoeff sX s U z)
  have hφ := pluriformCoeff_ne_zero sX s U z hz hs
  refine ⟨(X.basicOpen g : Set X)ᶜ, (X.basicOpen g).isOpen.isClosed_compl, ?_, ?_⟩
  · intro h
    have hgen : genericPoint X ∈ X.basicOpen g := by
      rw [Scheme.mem_basicOpen X g _ hgV]
      change IsUnit (X.presheaf.germ V (genericPoint X) hgV g)
      rw [hg]
      exact isUnit_iff_ne_zero.2 hφ
    have : genericPoint X ∈ ((X.basicOpen g : Set X)ᶜ) := h ▸ Set.mem_univ _
    exact this hgen
  · intro y hy
    rintro _ ⟨t, rfl⟩ hmem
    rw [Subsingleton.elim t default] at hmem
    have hyV : y ∈ chart V := mem_chart_iff.2 (X.basicOpen_le g hmem)
    have hne : evalHom V ⟨y, hyV⟩ g ≠ 0 := (toScheme_mem_basicOpen_iff ⟨y, hyV⟩ g).1 hmem
    have hle : ENNReal.ofReal (‖eval V g ⟨y, hyV⟩‖ ^ (2 / m : ℝ)) ≤
        pluriformDensity sX m (pluriformCoeff sX s U z) y := by
      unfold pluriformDensity
      exact le_iSup_of_le V (le_iSup_of_le g (le_iSup_of_le hyV (le_iSup_of_le hgV
        (le_iSup_of_le hg le_rfl))))
    rw [hy, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
    have hpos : 0 < ‖eval V g ⟨y, hyV⟩‖ ^ (2 / m : ℝ) :=
      Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _
    linarith

end MMP.Analytic.Proof_lem_mmp_analytic_proper_closed_null

namespace MMP.Analytic.ComplexPoints

open MMP.Analytic.Proof_lem_mmp_analytic_proper_closed_null in
/-- **Proper closed subsets are null.** Let `X` be a smooth irreducible complex variety,
`m > 0`, `s` a rational section of `ω_X^{⊗m}`, and `W` a chart of étale coordinates `z` on `U`.
For a proper Zariski closed subset `Z ⊊ X`, the set `Z^an` of `ℂ`-points of `X` over `Z` is null
for the chart measure `|φ|^{2/m} dλ` of `s` on `W`; and if `s ≠ 0`, this chart measure is
positive on every open subset of `X^an` meeting `W`. -/
public theorem pluriformChartMeasure_proper_closed_null {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m)
    (s : MMP.Mori.RationalPluriForms sX n m) (U : X.Opens) [Nonempty U]
    (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
    (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) :
    (∀ Z : Set X, IsClosed Z → Z ≠ Set.univ →
      pluriformChartMeasure sX hm s U z hz W hW hWo hWz
        {x : ComplexPoints sX | Set.range x.hom.base ⊆ Z} = 0) ∧
    (s ≠ 0 → ∀ V : Set (ComplexPoints sX), IsOpen V → (V ∩ W).Nonempty →
      0 < pluriformChartMeasure sX hm s U z hz W hW hWo hWz V) := by
  have hac : pluriformChartMeasure sX hm s U z hz W hW hWo hWz ≪ chartLebesgue sX U z W hW :=
    withDensity_absolutelyContinuous _ _
  refine ⟨fun Z hZ hZne ↦ hac (chartLebesgue_complexPoints_null sX U z hz W hW hWo hWz Z hZ hZne),
    fun hs V hV hVW ↦ ?_⟩
  obtain ⟨Z, hZ, hZne, hρ⟩ := pluriformDensity_pos_off_closed sX s U z hz hs
  have hnull := chartLebesgue_complexPoints_null sX U z hz W hW hWo hWz Z hZ hZne
  refine pos_iff_ne_zero.2 fun h0 ↦ (chartLebesgue_pos sX U z W hW hWz V hV hVW).ne' ?_
  rw [pluriformChartMeasure, withDensity_apply_eq_zero'
    (lowerSemicontinuous_pluriformDensity sX m _).measurable.aemeasurable] at h0
  refine measure_mono_null (fun y hy ↦ ?_) (measure_union_null h0 hnull)
  by_cases hy0 : pluriformDensity sX m (pluriformCoeff sX s U z) y = 0
  · exact Or.inr (hρ y hy0)
  · exact Or.inl ⟨hy0, hy⟩

end MMP.Analytic.ComplexPoints

end

/-!
## Integrability of a pluriform density near an snc divisor

Let `X` be a smooth projective complex variety of dimension `n`, `B = ∑ bᵢ Bᵢ` a `ℚ`-divisor
with snc support and every `bᵢ < 1`, and `s` a rational section of `ω_X^{⊗m}` (`m > 0`) with
`div(s) + mB ≥ 0`. Then the measure `μ_s = |φ|^{2/m} dλ` of `s` is finite on `X^an`.

Near a point, in étale coordinates in which the components of `B` through it are coordinate
hyperplanes, `s = ψ ∏ zᵢ^{-m bᵢ} (dz)^{⊗m}` with `ψ` holomorphic, so on a small polydisc the
density is at most `C ∏ |zᵢ|^{-2bᵢ}`; and `∏ |wᵢ|^{-2eᵢ}` is integrable on every polydisc of
`ℂ^ι` as soon as all `eᵢ < 1`. Compactness of `X^an` then gives finiteness.

### Main results

* `MMP.Analytic.ComplexPoints.isFiniteMeasure_pluriformChartMeasure_of_isSNC`: every chart
  measure `MMP.Analytic.ComplexPoints.pluriformChartMeasure` of `s` is finite; every point has
  a chart whose image is a polydisc on which the chart measure is bounded by
  `C ∏ |zᵢ - zᵢ(x)|^{-2eᵢ} dλ` with all `eᵢ < 1`; and such products are integrable on
  polydiscs.

### Implementation notes

* The global measure `μ_s` restricts on every chart `W` to the chart measure, and finitely
  many charts cover the compact space `X^an`; so `μ_s(X^an) < ∞` is equivalent to the
  finiteness of every chart measure, which is how it is stated.
* The condition `div(s) + mB ≥ 0` is stated coefficientwise: `ord_Γ(s) + m·b_Γ ≥ 0` for every
  prime divisor `Γ`.
* Densities are `ℝ≥0∞`-valued, so `|w|^{-2e}` is `∞` at `w = 0` when `e > 0`.

### References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory MMP.Analytic MMP.Analytic.ComplexPoints
open scoped ENNReal NNReal TensorProduct
open IsLocalRing

namespace MMP.Analytic.Proof_lem_mmp_analytic_snc_density_integrable

/-- `|w - c|^{-2e}` is integrable on every disc around `c` in `ℂ` when `e < 1`. -/
private theorem integrableOn_ball_norm_sub_rpow {e : ℝ} (he : e < 1) (c : ℂ) (ε : ℝ) :
    IntegrableOn (fun x : ℂ ↦ ‖x - c‖ ^ (-2 * e)) (Metric.ball c ε) := by
  have h0 : IntegrableOn (fun x : ℂ ↦ ‖x‖ ^ (-2 * e)) (Metric.ball 0 ε) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 2 * e)
      (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex]; linarith)
      (Filter.Eventually.of_forall fun x ↦ ?_) ?_
    · simp [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), neg_mul]
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  have hmp := measurePreserving_sub_right (volume : Measure ℂ) c
  have := (hmp.integrableOn_comp_preimage (MeasurableEquiv.subRight c).measurableEmbedding).2 h0
  have hs : (fun x : ℂ ↦ x - c) ⁻¹' Metric.ball 0 ε = Metric.ball c ε := by
    ext x; simp [dist_eq_norm]
  rw [hs] at this
  exact this

/-- `∏ᵢ |wᵢ - cᵢ|^{-2eᵢ}` has finite integral on every polydisc of `ℂ^ι` when all `eᵢ < 1`. -/
private theorem lintegral_pi_ball_prod_enorm_sub_rpow_lt_top (ι : Type) [Fintype ι] (e : ι → ℝ)
    (he : ∀ i, e i < 1) (c : ι → ℂ) (ε : ℝ) :
    ∫⁻ w in Set.univ.pi (fun i ↦ Metric.ball (c i) ε), ∏ i, ‖w i - c i‖ₑ ^ (-2 * e i) < ∞ := by
  have hint : Integrable (fun w : ι → ℂ ↦ ∏ i, ‖w i - c i‖ ^ (-2 * e i))
      (Measure.pi fun i ↦ (volume : Measure ℂ).restrict (Metric.ball (c i) ε)) :=
    Integrable.fintype_prod (f := fun i x ↦ ‖x - c i‖ ^ (-2 * e i))
      fun i ↦ integrableOn_ball_norm_sub_rpow (he i) _ _
  rw [← Measure.restrict_pi_pi, ← volume_pi] at hint
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hint.2
  have hne : ∀ᵐ w : ι → ℂ ∂(volume.restrict (Set.univ.pi fun i ↦ Metric.ball (c i) ε)),
      ∀ i, w i ≠ c i := by
    refine ae_restrict_of_ae ?_
    rw [ae_all_iff]
    intro i
    rw [volume_pi, ae_iff]
    simpa using Measure.pi_hyperplane (fun _ : ι ↦ (volume : Measure ℂ)) i (c i)
  filter_upwards [hne] with w hw
  rw [enorm_eq_nnnorm, nnnorm_prod]
  push_cast
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hpos : 0 < ‖w i - c i‖ := norm_pos_iff.2 (sub_ne_zero.2 (hw i))
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos hpos, ← enorm_eq_nnnorm,
    Real.enorm_of_nonneg (Real.rpow_nonneg hpos.le _)]

/-- The complex realization of a projective complex variety is compact: the structure morphism
is proper, so the map of underlying spaces to the point `Spec ℂ` is proper. -/
private theorem compactSpace_complexPoints {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sX] (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX) :
    CompactSpace (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  have : IsProper sX := inferInstance
  have : sX.IsOver (Spec (.of ℂ)) := ⟨Category.comp_id sX⟩
  have : LocallyOfFiniteType (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (𝟙 _) from inferInstance
  have hp := MMP.UnderlyingSpace.isProperMap_map (K := ℂ) sX
  have : Subsingleton (MMP.UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    ⟨fun p q ↦ MMP.UnderlyingSpace.ext
      (((Category.comp_id _).symm.trans p.toHom_comp_over).trans
        ((Category.comp_id _).symm.trans q.toHom_comp_over).symm)⟩
  have hc : CompactSpace (MMP.UnderlyingSpace ℂ X) :=
    ⟨by simpa using hp.isCompact_preimage (Set.subsingleton_univ.isCompact)⟩
  exact (homeomorphUnderlyingSpace (X := X)).symm.compactSpace

/-- Shrinking a chart to a polydisc: if `F` restricted to an open `W'` is an open embedding into
`ℂⁿ` and `x ∈ W' ∩ N` with `N` open, there is an open `W ∋ x` inside `W' ∩ N` on which `F` is
an open embedding with image a polydisc around `F x`. -/
private theorem exists_isOpenEmbedding_range_eq_pi_ball {T : Type} [TopologicalSpace T]
    {S : Set T} {n : ℕ} (F : S → (Fin n → ℂ)) (W' : Set T) (hW' : W' ⊆ S) (hWo' : IsOpen W')
    (hemb : IsOpenEmbedding (fun y : W' ↦ F ⟨y.1, hW' y.2⟩)) (N : Set T) (hN : IsOpen N)
    (x : T) (hx : x ∈ W') (hxN : x ∈ N) :
    ∃ (W : Set T) (hW : W ⊆ S), IsOpen W ∧ W ⊆ N ∧ ∃ hxW : x ∈ W, ∃ ε : ℝ, 0 < ε ∧
      IsOpenEmbedding (fun y : W ↦ F ⟨y.1, hW y.2⟩) ∧
      Set.range (fun y : W ↦ F ⟨y.1, hW y.2⟩) =
        Set.univ.pi (fun i ↦ Metric.ball (F ⟨x, hW hxW⟩ i) ε) := by
  set φ := fun y : W' ↦ F ⟨y.1, hW' y.2⟩ with hφ
  have hO : IsOpen (φ '' (Subtype.val ⁻¹' N)) :=
    hemb.isOpenMap _ (hN.preimage continuous_subtype_val)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO (φ ⟨x, hx⟩) ⟨⟨x, hx⟩, hxN, rfl⟩
  set W : Set T := Subtype.val '' (φ ⁻¹' Metric.ball (φ ⟨x, hx⟩) ε) with hWdef
  have hWW' : W ⊆ W' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hWS : W ⊆ S := hWW'.trans hW'
  have hWo : IsOpen W :=
    hWo'.isOpenMap_subtype_val _ (Metric.isOpen_ball.preimage hemb.continuous)
  have hxW : x ∈ W := ⟨⟨x, hx⟩, Metric.mem_ball_self hε, rfl⟩
  have hcomp : (fun y : W ↦ F ⟨y.1, hWS y.2⟩) = φ ∘ Set.inclusion hWW' := rfl
  have hincl : IsOpenEmbedding (Set.inclusion hWW') :=
    IsOpenEmbedding.inclusion hWW' (hWo.preimage continuous_subtype_val)
  have hrange : Set.range (fun y : W ↦ F ⟨y.1, hWS y.2⟩) = Metric.ball (φ ⟨x, hx⟩) ε := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨_, ⟨y, hy, rfl⟩⟩, rfl⟩
      exact hy
    · intro w hw
      obtain ⟨y, -, rfl⟩ := hball hw
      exact ⟨⟨y.1, y, hw, rfl⟩, rfl⟩
  refine ⟨W, hWS, hWo, ?_, hxW, ε, hε, hcomp ▸ hemb.comp hincl, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy'N, hy'⟩ := hball hy
    rw [← hemb.injective hy']
    exact hy'N
  · rw [hrange, ball_pi _ hε]

/-- The base measure of a chart (Lebesgue measure transported by an open embedding `f` of an
open `W`) integrates a function of the coordinates as Lebesgue measure on the image. -/
private theorem lintegral_map_comap_eq_setLIntegral_range {T : Type} [TopologicalSpace T]
    [MeasurableSpace T] [BorelSpace T] {n : ℕ} (W : Set T) (hWo : IsOpen W)
    (f : W → (Fin n → ℂ)) (hf : IsOpenEmbedding f) (G : (Fin n → ℂ) → ℝ≥0∞) (g : T → ℝ≥0∞)
    (hg : ∀ y : W, g y = G (f y)) :
    ∫⁻ y, g y ∂((Measure.comap f volume).map Subtype.val) = ∫⁻ w in Set.range f, G w := by
  have hv : MeasurableEmbedding (Subtype.val : W → T) :=
    MeasurableEmbedding.subtype_coe hWo.measurableSet
  have hfm : MeasurableEmbedding f := hf.measurableEmbedding
  rw [hv.lintegral_map]
  simp_rw [hg]
  rw [← hfm.lintegral_map, hfm.map_comap]

/-- A measure pushed forward from a subset `W` and given a density vanishes off `W`. -/
private theorem withDensity_map_subtype_val_compl {T : Type} [MeasurableSpace T] (W : Set T)
    (hW : MeasurableSet W) (ν : Measure W) (ρ : T → ℝ≥0∞) :
    ((ν.map Subtype.val).withDensity ρ) Wᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.map_apply measurable_subtype_coe hW.compl]
  simp

private theorem isOpen_setOf_norm_eval_lt_of_over {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (U : X.Opens) (h : Γ(X, U)) (r : ℝ) :
    IsOpen {y : ComplexPoints (X ↘ Spec (.of ℂ)) | ∃ hy : y ∈ chart U, ‖eval U h ⟨y, hy⟩‖ < r} := by
  have hc := MMP.Analytic.InvertibleModule.continuousOn_evalExt (X := X) U h
  have : {y : ComplexPoints (X ↘ Spec (.of ℂ)) | ∃ hy : y ∈ chart U, ‖eval U h ⟨y, hy⟩‖ < r} =
      chart (sX := X ↘ Spec (.of ℂ)) U ∩
        MMP.Analytic.InvertibleModule.evalExt U h ⁻¹' {w | ‖w‖ < r} := by
    ext y
    constructor
    · rintro ⟨hy, hlt⟩
      exact ⟨hy, by rwa [Set.mem_preimage, MMP.Analytic.InvertibleModule.evalExt_of_mem _ hy]⟩
    · rintro ⟨hy, hlt⟩
      rw [Set.mem_preimage, MMP.Analytic.InvertibleModule.evalExt_of_mem _ hy] at hlt
      exact ⟨hy, hlt⟩
  rw [this]
  exact hc.isOpen_inter_preimage (MMP.Analytic.InvertibleModule.isOpen_chart U) (isOpen_lt
      continuous_norm continuous_const)

/-- `{y ∈ U(ℂ) | |h(y)| < r}` is open in `X^an` for a section `h` over `U`. -/
private theorem isOpen_setOf_norm_eval_lt {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (U : X.Opens) (h : Γ(X, U)) (r : ℝ) :
    IsOpen {y : ComplexPoints sX | ∃ hy : y ∈ chart U, ‖eval U h ⟨y, hy⟩‖ < r} := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  exact isOpen_setOf_norm_eval_lt_of_over U h r

/-- The pointwise estimate: if `g · ∏ zᵢ^{kᵢ} = a` and `|a|^{2/m} ≤ C`, then
`|g|^{2/m} ≤ C ∏ |zᵢ|^{-2kᵢ/m}` (both sides `∞` when some `zᵢ = 0` with `kᵢ > 0`). -/
private theorem ofReal_norm_rpow_le_mul_prod {n m : ℕ} (hm : 0 < m) (a g : ℂ) (zs : Fin n → ℂ)
    (k : Fin n → ℕ) (hfac : g * ∏ i, zs i ^ k i = a) (C : ℝ≥0) (hC : C ≠ 0)
    (ha : ‖a‖ₑ ^ (2 / m : ℝ) ≤ C) :
    ENNReal.ofReal (‖g‖ ^ (2 / m : ℝ)) ≤ (C : ℝ≥0∞) * ∏ i, ‖zs i‖ₑ ^ (-2 * ((k i : ℝ) / m)) := by
  have hr : (0 : ℝ) < 2 / m := by positivity
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le, ofReal_norm]
  have hfac' : ∀ i, ‖zs i‖ₑ ^ (-2 * ((k i : ℝ) / m)) = (‖zs i‖ₑ ^ k i) ^ (-(2 / m : ℝ)) := by
    intro i
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  simp_rw [hfac']
  rw [ENNReal.prod_rpow_of_ne_top (f := fun i ↦ ‖zs i‖ₑ ^ k i)
    (fun i _ ↦ ENNReal.pow_ne_top enorm_ne_top)]
  have hPZ : ∏ i, ‖zs i‖ₑ ^ k i = ‖∏ i, zs i ^ k i‖ₑ := by
    simp only [enorm_eq_nnnorm, nnnorm_prod, nnnorm_pow]; push_cast; rfl
  rw [hPZ]
  set Z := ∏ i, zs i ^ k i with hZ
  rcases eq_or_ne Z 0 with h0 | h0
  · rw [h0, enorm_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top (by simpa using hC)]
    exact le_top
  · have hg : g = a * Z⁻¹ := by rw [← hfac, mul_assoc, mul_inv_cancel₀ h0, mul_one]
    rw [hg, enorm_mul, enorm_inv h0, ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.inv_rpow,
      ENNReal.rpow_neg]
    gcongr

/-- **The density bound from a local factorisation.** If `φ · ∏ zᵢ^{kᵢ}` is regular on an open
`U' ∋ x`, given there by `h`, and every `zᵢ` with `kᵢ > 0` vanishes at `x`, then near `x` the
density `|φ|^{2/m}` is at most `C ∏ |zᵢ - zᵢ(x)|^{-2kᵢ/m}`. -/
private theorem pluriformDensity_le_of_germ_eq_mul_prod {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] {m : ℕ} (hm : 0 < m) (φ : X.functionField) {n : ℕ}
    (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U)) (U' : X.Opens) [Nonempty U']
    (hU' : U' ≤ U) (h : Γ(X, U')) (k : Fin n → ℕ)
    (hfac : X.germToFunctionField U' h = φ * ∏ i, X.germToFunctionField U (z i) ^ k i)
    (x : ComplexPoints sX) (hxU : x ∈ chart U) (hx : x ∈ chart U')
    (hz0 : ∀ i, 0 < k i → eval U (z i) ⟨x, hxU⟩ = 0) :
    ∃ (N : Set (ComplexPoints sX)) (C : ℝ≥0), IsOpen N ∧ x ∈ N ∧
      ∀ (y : ComplexPoints sX) (hy : y ∈ chart U), y ∈ N →
        pluriformDensity sX m φ y ≤
          (C : ℝ≥0∞) * ∏ i, ‖eval U (z i) ⟨y, hy⟩ - eval U (z i) ⟨x, hxU⟩‖ₑ ^
            (-2 * ((k i : ℝ) / m)) := by
  set r := ‖eval U' h ⟨x, hx⟩‖ + 1 with hr
  have hr0 : 0 < r := by positivity
  refine ⟨{y | ∃ hy : y ∈ chart U', ‖eval U' h ⟨y, hy⟩‖ < r}, Real.toNNReal (r ^ (2 / m : ℝ)),
    isOpen_setOf_norm_eval_lt U' h r, ⟨hx, by simp [r]⟩, ?_⟩
  rintro y hy ⟨hy', hlt⟩
  simp only [pluriformDensity]
  refine iSup_le fun V ↦ iSup_le fun g ↦ iSup_le fun hyV ↦ iSup_le fun hgen ↦
    iSup_le fun hgφ ↦ ?_
  have : Nonempty V := ⟨⟨_, hgen⟩⟩
  have hyQ : y ∈ chart (V ⊓ U') := mem_chart_iff.2 ⟨mem_chart_iff.1 hyV, mem_chart_iff.1 hy'⟩
  have : Nonempty (V ⊓ U' : X.Opens) := ⟨⟨_, mem_chart_iff.1 hyQ⟩⟩
  have hsec : X.presheaf.map (homOfLE (inf_le_left : V ⊓ U' ≤ V)).op g *
      ∏ i, (X.presheaf.map (homOfLE ((inf_le_right : V ⊓ U' ≤ U').trans hU')).op (z i)) ^ k i =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ U' ≤ U')).op h := by
    apply X.germToFunctionField_injective (V ⊓ U')
    have hres := @Proof_lem_mmp_analytic_pluriform_density_intrinsic.germToFunctionField_res
    rw [map_mul, map_prod, hres, hres, hfac]
    simp_rw [map_pow, hres]
    rw [← hgφ]
  have hev := congrArg (evalHom (V ⊓ U') ⟨y, hyQ⟩) hsec
  rw [map_mul, map_prod] at hev
  simp_rw [map_pow, ← evalHom_res, evalHom_apply] at hev
  refine ofReal_norm_rpow_le_mul_prod hm (eval U' h ⟨y, hy'⟩) _
    (fun i ↦ eval U (z i) ⟨y, hy⟩ - eval U (z i) ⟨x, hxU⟩) k ?_ _ ?_ ?_
  · rw [← hev]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos (k i) with hk | hk
    · simp [hk]
    · rw [hz0 i hk, sub_zero]
  · exact (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hr0 _)).ne'
  · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (norm_nonneg _) hlt.le (by positivity))

/-- The point of `X` under a `ℂ`-point is closed: a section of `X → Spec ℂ` is a closed
immersion. -/
private theorem isClosed_singleton_toScheme {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (x : ComplexPoints sX) : IsClosed ({x.toScheme} : Set X) := by
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id sX x.hom x.2
  convert x.hom.isClosedEmbedding.isClosed_range using 1
  ext y
  constructor
  · rintro rfl; exact ⟨default, rfl⟩
  · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q default]; rfl

/-- Over a base change `R → R₀` with bijective structure map, differentials forming a basis of
`κ(B) ⊗ Ω[B⁄R]` also form a basis of `κ(B) ⊗ Ω[B⁄R₀]`. -/
private theorem isBasis_D_of_bijective_algebraMap {R R₀ B : Type*} [CommRing R] [CommRing R₀]
    [CommRing B] [IsLocalRing B] [Algebra R R₀] [Algebra R₀ B] [Algebra R B]
    [IsScalarTower R R₀ B] (hR : Function.Bijective (algebraMap R R₀)) {ι : Type*} (b : ι → B)
    (hli : LinearIndependent (ResidueField B)
      (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i)))
    (hsp : Submodule.span (ResidueField B)
      (Set.range (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i))) = ⊤) :
    LinearIndependent (ResidueField B)
      (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i)) ∧
    Submodule.span (ResidueField B)
      (Set.range (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i))) = ⊤ := by
  have : Algebra.FormallyEtale R R₀ :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R R₀) hR)
  have : Subsingleton Ω[R₀⁄R] := (Algebra.formallyUnramified_iff R R₀).mp inferInstance
  have hbij : Function.Bijective (KaehlerDifferential.map R R₀ B B) := by
    refine ⟨?_, KaehlerDifferential.map_surjective R R₀ B⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R₀ B x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  let e : Ω[B⁄R] ≃ₗ[B] Ω[B⁄R₀] := LinearEquiv.ofBijective (KaehlerDifferential.map R R₀ B B) hbij
  let e' := e.baseChange B (ResidueField B)
  have hcomp : (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i)) =
      e' ∘ (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i)) := by
    funext i
    change _ = (1 : ResidueField B) ⊗ₜ[B]
      KaehlerDifferential.map R R₀ B B (KaehlerDifferential.D R B (b i))
    rw [KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hcomp]
  refine ⟨hli.map' e'.toLinearMap (LinearEquiv.ker e'), ?_⟩
  rw [Set.range_comp, ← LinearEquiv.coe_coe, ← Submodule.map_span, hsp, Submodule.map_top,
    LinearEquiv.range]

/-- At a closed point of a smooth complex scheme, the differentials of a regular system of
parameters form a basis of the fibre `κ(p) ⊗ Ω_{𝒪_{X,p}/ℂ}`. -/
private theorem isBasis_D_stalk_of_isRegularSystemOfParameters {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [Smooth sX] (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ}
    (t : Fin n → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    let := MMP.Mori.stalkAlgebra sX p
    LinearIndependent (ResidueField (X.presheaf.stalk p))
      (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i)) ∧
    Submodule.span (ResidueField (X.presheaf.stalk p))
      (Set.range (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i))) = ⊤ := by
  classical
  let := MMP.Mori.stalkAlgebra sX p
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sX p
  have := h1
  have := h2
  have := h3
  have : Module.Finite ℂ (ResidueField (X.presheaf.stalk p)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX p hp
  have : Algebra.FormallyUnramified ℂ (ResidueField (X.presheaf.stalk p)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular t ht.1 ht.2
  exact ⟨MMP.Flips.ResolutionInputs.linearIndependent_tmul_D ℂ t ht0 hli,
    top_le_iff.mp (MMP.Flips.ResolutionInputs.span_tmul_D ℂ t ht.1)⟩

/-- The structure map from `ℂ` to the stalk of `Spec ℂ` at its point is bijective. -/
private theorem bijective_germ_comp_ΓSpecIso_inv (q : Spec (.of ℂ)) :
    Function.Bijective ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec (.of ℂ)).presheaf.germ ⊤ q trivial).hom := by
  refine ⟨RingHom.injective _, ?_⟩
  have hloc := (isAffineOpen_top (Spec (.of ℂ))).isLocalization_stalk ⟨q, trivial⟩
  have hu : ∀ y : ((isAffineOpen_top (Spec (.of ℂ))).primeIdealOf ⟨q, trivial⟩).asIdeal.primeCompl,
      IsUnit (y : Γ(Spec (.of ℂ), ⊤)) := by
    intro y
    have hy0 : (y : Γ(Spec (.of ℂ), ⊤)) ≠ 0 := fun h0 ↦ y.2 (h0 ▸ Ideal.zero_mem _)
    have : (Scheme.ΓSpecIso (.of ℂ)).hom (y : Γ(Spec (.of ℂ), ⊤)) ≠ 0 := by
      intro h; apply hy0
      rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of ℂ)) (y : Γ(Spec (.of ℂ), ⊤)), h, map_zero]
    have hU := (IsUnit.mk0 _ this).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
    rwa [Iso.hom_inv_id_apply] at hU
  let := TopCat.Presheaf.algebra_section_stalk (Spec (.of ℂ)).presheaf (U := ⊤) ⟨q, trivial⟩
  have hs := (IsLocalization.atUnits Γ(Spec (.of ℂ), ⊤) _ (S := (Spec (.of ℂ)).presheaf.stalk q)
    (fun y hy ↦ hu ⟨y, hy⟩)).surjective
  intro r
  obtain ⟨a, ha⟩ := hs r
  refine ⟨(Scheme.ΓSpecIso (.of ℂ)).hom a, ?_⟩
  rw [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply]
  exact ha

/-- At a closed point `p` of a smooth complex scheme, the differentials of a regular system of
parameters form a basis of `κ(p) ⊗ Ω[𝒪_{X,p} ⁄ 𝒪_{Spec ℂ, sX p}]`. -/
private theorem isBasis_D_stalk_base_of_isRegularSystemOfParameters {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [Smooth sX] (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ}
    (t : Fin n → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    let := (sX.stalkMap p).hom.toAlgebra
    LinearIndependent (ResidueField (X.presheaf.stalk p))
      (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (t i)) ∧
    Submodule.span (ResidueField (X.presheaf.stalk p))
      (Set.range (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (t i))) = ⊤ := by
  let := MMP.Mori.stalkAlgebra sX p
  let := (sX.stalkMap p).hom.toAlgebra
  let : Algebra ℂ ((Spec (.of ℂ)).presheaf.stalk (sX p)) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).presheaf.germ ⊤ (sX p) trivial).hom.toAlgebra
  have : IsScalarTower ℂ ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom =
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).presheaf.germ ⊤ (sX p)
        (TopologicalSpace.Opens.mem_top _) ≫ sX.stalkMap p).hom
    rw [Scheme.Hom.germ_stalkMap]
    rfl
  obtain ⟨hli, hsp⟩ := isBasis_D_stalk_of_isRegularSystemOfParameters sX p hp t ht
  exact isBasis_D_of_bijective_algebraMap (bijective_germ_comp_ΓSpecIso_inv (sX p)) t hli hsp

/-- At a closed point of a smooth complex variety of relative dimension `n`, a regular system of
parameters has `n` elements. -/
private theorem eq_of_isRegularSystemOfParameters {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {n : ℕ} [SmoothOfRelativeDimension n sX] (p : X) (hp : IsClosed ({p} : Set X)) {n' : ℕ}
    (t : Fin n' → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) : n' = n := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  let := (sX.stalkMap p).hom.toAlgebra
  obtain ⟨hli, hsp⟩ := isBasis_D_stalk_base_of_isRegularSystemOfParameters sX p hp t ht
  obtain ⟨hfree, -⟩ := MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk sX p
  let b := Module.Basis.mk hli hsp.ge
  have h1 := finrank_kaehlerDifferential_stalk (n := n) sX p
  have h2 : Module.finrank (ResidueField (X.presheaf.stalk p))
      (ResidueField (X.presheaf.stalk p) ⊗[X.presheaf.stalk p]
        Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)]) =
      Module.finrank (X.presheaf.stalk p)
        Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)] :=
    Module.finrank_baseChange
  rw [← h1, ← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- **Étale coordinates through a regular system of parameters.** At a closed point `p` of a
smooth complex variety of relative dimension `n`, a regular system of parameters `t₁, …, tₙ` of
`𝒪_{X,p}` consists of the germs of étale coordinates on an open neighbourhood of `p`. -/
private theorem exists_etale_coordinates_germ_eq {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {n : ℕ} [SmoothOfRelativeDimension n sX] (p : X) (hp : IsClosed ({p} : Set X))
    (t : Fin n → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    ∃ (U : X.Opens) (hpU : p ∈ U) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧
      ∀ i, X.presheaf.germ U p hpU (z i) = t i := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  obtain ⟨hli, hsp⟩ := isBasis_D_stalk_base_of_isRegularSystemOfParameters sX p hp t ht
  obtain ⟨V, -, hpV, a, ha⟩ := MMP.Flips.ResolutionInputs.exists_affineOpen_germ_eq p t
  obtain ⟨U, -, hpU, hUV, het⟩ :=
    MMP.Flips.ResolutionInputs.exists_isAffineOpen_etale_homOfVector sX p V hpV a
      (by dsimp only; simp only [ha]; exact ⟨hli, hsp⟩)
  refine ⟨U, hpU, fun i ↦ X.presheaf.map (homOfLE hUV).op (a i), het, fun i ↦ ?_⟩
  rw [← ha i]
  exact X.presheaf.germ_res_apply (homOfLE hUV) p hpU (a i)

/-- At a closed point of a smooth complex scheme, the differentials of a regular system of
parameters form a basis of `Ω_{𝒪_{X,p}/ℂ}`. -/
private theorem exists_basis_kaehler_stalk {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [Smooth sX]
    (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ} (t : Fin n → X.presheaf.stalk p)
    (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    letI := MMP.Mori.stalkAlgebra sX p
    ∃ b : Module.Basis (Fin n) (X.presheaf.stalk p) Ω[X.presheaf.stalk p⁄ℂ],
      ∀ i, b i = KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i) := by
  let := MMP.Mori.stalkAlgebra sX p
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sX p
  have := h1
  have := h2
  have := h3
  have : Module.Projective (X.presheaf.stalk p) Ω[X.presheaf.stalk p⁄ℂ] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  have : Module.Flat (X.presheaf.stalk p) Ω[X.presheaf.stalk p⁄ℂ] := Module.Flat.of_projective
  obtain ⟨hli, hsp⟩ := isBasis_D_stalk_of_isRegularSystemOfParameters sX p hp t ht
  have hbij : Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk p)
      (fun i ↦ KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    refine ⟨hli, ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hsp
  exact ⟨MMP.Flips.ResolutionInputs.basisOfBijective _ hbij,
    MMP.Flips.ResolutionInputs.basisOfBijective_apply _ hbij⟩

/-- The basis of a line given by a spanning vector depends only on the vector. -/
private theorem basisOfSpanSingleton_congr {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    {ω ω' : L} (h : ω = ω') (hω : Submodule.span K {ω} = ⊤) (h0 : ω ≠ 0)
    (hω' : Submodule.span K {ω'} = ⊤) (h0' : ω' ≠ 0) :
    MMP.Mori.basisOfSpanSingleton hω h0 = MMP.Mori.basisOfSpanSingleton hω' h0' := by
  subst h; rfl

/-- Along a prime divisor `Γ` through a closed point `p`, the order of a rational pluriform `s`
is the order of its coefficient `φ` in `s = φ (dz₁ ∧ ⋯ ∧ dzₙ)^{⊗m}`, for étale coordinates `z`
whose germs at `p` are a regular system of parameters. -/
private theorem ordForm_eq_ord_pluriformCoeff {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [IsIntegral X] [IsLocallyNoetherian X] [Smooth sX] {m : ℕ}
    (s : MMP.Mori.RationalPluriForms sX n m) (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (p : X) (hp : IsClosed ({p} : Set X)) (hpU : p ∈ U)
    (ht : MMP.Mori.IsRegularSystemOfParameters (fun i ↦ X.presheaf.germ U p hpU (z i)))
    (Γ : MMP.Mori.PrimeDivisor X) (hΓ : p ∈ Γ.support) :
    Γ.ordForm s = X.ord (pluriformCoeff sX s U z) Γ.genericPoint := by
  let := MMP.Mori.stalkAlgebra sX p
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_stalk_functionField sX p
  obtain ⟨b, hb⟩ := exists_basis_kaehler_stalk sX p hp _ ht
  have hσ := Proof_lem_mmp_analytic_proper_closed_null.span_ιMulti_basis_eq_top b
  have hb' : (b : Fin n → _) = fun i ↦
      KaehlerDifferential.D ℂ (X.presheaf.stalk p) (X.presheaf.germ U p hpU (z i)) := funext hb
  rw [hb'] at hσ
  obtain ⟨bK, hbK⟩ := exists_basis_kaehler_functionField sX U z hz
  have hspan := Proof_lem_mmp_analytic_proper_closed_null.span_ιMulti_basis_eq_top bK
  have hne := Proof_lem_mmp_analytic_proper_closed_null.ιMulti_basis_ne_zero bK
  have hbK' : (bK : Fin n → _) =
      fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField U (z i)) := funext hbK
  rw [hbK'] at hspan hne
  have htop : MMP.Mori.topFormsMap ℂ (X.presheaf.stalk p) X.functionField n
      (exteriorPower.ιMulti (X.presheaf.stalk p) n (fun i ↦
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (X.presheaf.germ U p hpU (z i)))) =
      exteriorPower.ιMulti X.functionField n
        (fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField U (z i))) := by
    rw [MMP.Mori.topFormsMap_ιMulti]
    congr 1
    funext i
    rw [KaehlerDifferential.map_D, Scheme.algebraMap_germ_eq_germToFunctionField]
  have h0 : MMP.Mori.topFormsMap ℂ (X.presheaf.stalk p) X.functionField n
      (exteriorPower.ιMulti (X.presheaf.stalk p) n (fun i ↦
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (X.presheaf.germ U p hpU (z i)))) ≠ 0 :=
    htop ▸ hne
  rw [MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sX p Γ hΓ hσ h0 s]
  congr 1
  unfold pluriformCoeff MMP.Mori.formCoeff MMP.Mori.topFormsBasis
  dsimp only
  split_ifs with hc
  · rw [basisOfSpanSingleton_congr htop _ h0 hc.1 hc.2]
  · exact absurd ⟨hspan, hne⟩ hc

section Valuation

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A function regular at a point `p` of a prime divisor `Γ` has `v_Γ ≤ 1`. -/
private theorem divisorialValuation_germToFunctionField_le_one (Γ : MMP.Mori.PrimeDivisor X)
    {p : X} (hΓ : p ∈ Γ.support) (U : X.Opens) [Nonempty U] (hpU : p ∈ U) (g : Γ(X, U)) :
    Γ.divisorialValuation (X.germToFunctionField U g) ≤ 1 := by
  have hs : Γ.genericPoint ⤳ p := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
    exact specializes_iff_mem_closure.mpr hΓ
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
  refine ⟨X.presheaf.stalkSpecializes hs (X.presheaf.germ U p hpU g), ?_⟩
  rw [MMP.Mori.algebraMap_stalkSpecializes, Scheme.algebraMap_germ_eq_germToFunctionField]

/-- A function regular at a point `p` of a prime divisor `Γ`, whose germ at `p` lies in the ideal
of `Γ`, has `v_Γ < 1`. -/
private theorem divisorialValuation_germToFunctionField_lt_one (Γ : MMP.Mori.PrimeDivisor X)
    {p : X} (hΓ : p ∈ Γ.support) (U : X.Opens) [Nonempty U] (hpU : p ∈ U) (g : Γ(X, U))
    (hg : X.presheaf.germ U p hpU g ∈ IdealSheafData.stalk Γ.idealSheaf p) :
    Γ.divisorialValuation (X.germToFunctionField U g) < 1 := by
  have hs : Γ.genericPoint ⤳ p := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
    exact specializes_iff_mem_closure.mpr hΓ
  have hη : Γ.genericPoint ∈ Γ.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hpU,
    ← MMP.Mori.algebraMap_stalkSpecializes hs,
    MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
  obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : X.Opens) from trivial)
  have hηW : Γ.genericPoint ∈ W := hs.mem_open W.isOpen hpW
  rw [IdealSheafData.stalk_eq_map_germ _ p ⟨W, hW⟩ hpW] at hg
  have h1 := Ideal.mem_map_of_mem (X.presheaf.stalkSpecializes hs).hom hg
  rw [Ideal.map_map, ← CommRingCat.hom_comp, X.presheaf.germ_stalkSpecializes] at h1
  refine Ideal.map_le_iff_le_comap.mpr (fun f hf ↦ ?_) h1
  have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hηW).1 hη
  rw [Scheme.mem_zeroLocus_iff] at hz
  have hnot := hz f hf
  rw [Scheme.mem_basicOpen _ _ _ hηW] at hnot
  exact (IsLocalRing.mem_maximalIdeal _).mpr hnot

/-- **Nonnegative order of `φ ∏ zᵢ^{kᵢ}`** along a prime divisor `Γ` through `p`, where the `zᵢ`
are regular at `p`: either `φ` already has nonnegative order along `Γ`, or some `z_{i₀}` lies in
the ideal of `Γ` at `p` with `k_{i₀} ≥ -ord_Γ φ`. -/
private theorem zero_le_ord_mul_prod (Γ : MMP.Mori.PrimeDivisor X) {p : X} (hΓ : p ∈ Γ.support)
    (φ : X.functionField) (U : X.Opens) [Nonempty U] (hpU : p ∈ U) {n : ℕ}
    (z : Fin n → Γ(X, U)) (k : Fin n → ℕ)
    (hg : φ * ∏ i, X.germToFunctionField U (z i) ^ k i ≠ 0)
    (hbound : 0 ≤ X.ord φ Γ.genericPoint ∨ ∃ i₀,
      X.presheaf.germ U p hpU (z i₀) ∈ IdealSheafData.stalk Γ.idealSheaf p ∧
        -X.ord φ Γ.genericPoint ≤ k i₀) :
    0 ≤ X.ord (φ * ∏ i, X.germToFunctionField U (z i) ^ k i) Γ.genericPoint := by
  have hφ : φ ≠ 0 := left_ne_zero_of_mul hg
  have hv := Γ.divisorialValuation_eq_exp_neg_ord hg
  suffices H : Γ.divisorialValuation (φ * ∏ i, X.germToFunctionField U (z i) ^ k i) ≤
      WithZero.exp 0 by
    rw [hv, WithZero.exp_le_exp] at H
    omega
  have hle : ∀ i, Γ.divisorialValuation (X.germToFunctionField U (z i)) ^ k i ≤ 1 :=
    fun i ↦ pow_le_one' (divisorialValuation_germToFunctionField_le_one Γ hΓ U hpU (z i)) _
  rw [map_mul, map_prod, Γ.divisorialValuation_eq_exp_neg_ord hφ]
  simp_rw [map_pow]
  rcases hbound with h | ⟨i₀, hi₀, hk⟩
  · calc WithZero.exp (-X.ord φ Γ.genericPoint) *
          ∏ i, Γ.divisorialValuation (X.germToFunctionField U (z i)) ^ k i
        ≤ WithZero.exp 0 * 1 := by
          gcongr
          · rw [WithZero.exp_le_exp]; omega
          · exact Finset.prod_le_one' fun i _ ↦ hle i
      _ = WithZero.exp 0 := mul_one _
  · classical
    have hlt := (WithZero.lt_mul_exp_iff_le (y := WithZero.exp (-1)) WithZero.exp_ne_zero).1 (by
      rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      exact divisorialValuation_germToFunctionField_lt_one Γ hΓ U hpU (z i₀) hi₀)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
    calc WithZero.exp (-X.ord φ Γ.genericPoint) *
          (Γ.divisorialValuation (X.germToFunctionField U (z i₀)) ^ k i₀ *
            ∏ i ∈ Finset.univ.erase i₀, Γ.divisorialValuation (X.germToFunctionField U (z i)) ^ k i)
        ≤ WithZero.exp (-X.ord φ Γ.genericPoint) * (WithZero.exp (-1) ^ k i₀ * 1) := by
          gcongr
          exacts [zero_le', Finset.prod_le_one' fun i _ ↦ hle i]
      _ = WithZero.exp (-X.ord φ Γ.genericPoint - k i₀) := by
          rw [mul_one, ← WithZero.exp_nsmul, ← WithZero.exp_add]
          congr 1
          simp only [nsmul_eq_mul, mul_neg, mul_one]
          ring
      _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega

end Valuation

/-- **Coordinates adapted to an snc divisor and the local factorisation.** Around every point
`x` there are étale coordinates `z₁, …, zₙ` on `U ∋ x` and an open `U' ∋ x` inside `U` on which
`φ · ∏ zᵢ^{kᵢ}` is regular, where `s = φ · (dz₁ ∧ ⋯ ∧ dzₙ)^{⊗m}`, with every `kᵢ < m` and
`zᵢ(x) = 0` whenever `kᵢ > 0`.

The snc condition at the closed point `p` of `X` under `x` gives a regular system of parameters
`t` of `𝒪_{X,p}` in which each component `E` of `B` through `p` is cut out by `t_{j(E)}`; the `t`
are the germs of étale coordinates `z` near `p`. Take `k_{j(E)} = max(0, -ord_E s) < m` and
`kᵢ = 0` otherwise. Since `dz` generates the top forms at `p`, `ord_Γ φ = ord_Γ s` for every prime
divisor `Γ` through `p`, and `ord_E z_{j(E)} ≥ 1`, `ord_Γ zᵢ ≥ 0`; so `φ ∏ zᵢ^{kᵢ}` has
nonnegative order along every prime divisor through `p`, and is regular at `p` by Hartogs. -/
private theorem exists_etale_coordinates_germ_eq_mul_prod {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [IsLocallyNoetherian X]
    (B : MMP.Mori.DivisorWithCoeffs ℚ X) (hB : B.IsSNC sX) (hb : ∀ E, B.coeff E < 1)
    {m : ℕ} (hm : 0 < m) (s : MMP.Mori.RationalPluriForms sX n m)
    (hs : ∀ E : MMP.Mori.PrimeDivisor X, 0 ≤ (E.ordForm s : ℚ) + m * B.coeff E)
    (x : ComplexPoints sX) :
    ∃ (U : X.Opens) (_ : Nonempty U) (z : Fin n → Γ(X, U))
      (_ : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (hxU : x ∈ chart U) (U' : X.Opens) (_ : Nonempty U') (_ : U' ≤ U) (_ : x ∈ chart U')
      (h : Γ(X, U')) (k : Fin n → ℕ), (∀ i, k i < m) ∧
      X.germToFunctionField U' h =
        pluriformCoeff sX s U z * ∏ i, X.germToFunctionField U (z i) ^ k i ∧
      ∀ i, 0 < k i → eval U (z i) ⟨x, hxU⟩ = 0 := by
  classical
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : IsNormal (Spec (.of ℂ)) := isNormal_spec_of_isIntegrallyClosed _
  have : IsNormal X := AlgebraicGeometry.isNormal_of_smooth sX
  set p := x.toScheme with hpdef
  have hp := isClosed_singleton_toScheme x
  obtain ⟨n', t, j, ht, hj, hI⟩ := hB.2 p
  obtain rfl := eq_of_isRegularSystemOfParameters (n := n) sX p hp t ht
  obtain ⟨U, hpU, z, hz, hzt⟩ := exists_etale_coordinates_germ_eq sX p hp t ht
  have hU : Nonempty U := ⟨⟨p, hpU⟩⟩
  have hxU : x ∈ chart U := mem_chart_iff.2 hpU
  have hzt' : (fun i ↦ X.presheaf.germ U p hpU (z i)) = t := funext hzt
  have ht' : MMP.Mori.IsRegularSystemOfParameters (fun i ↦ X.presheaf.germ U p hpU (z i)) := by
    rw [hzt']; exact ht
  set φ := pluriformCoeff sX s U z with hφdef
  -- the exponents
  let k : Fin n' → ℕ := fun i ↦
    if h : ∃ E, j E = i then (-(h.choose.1.ordForm s)).toNat else 0
  have hk : ∀ E, k (j E) = (-(E.1.ordForm s)).toNat := by
    intro E
    have h : ∃ E', j E' = j E := ⟨E, rfl⟩
    simp only [k, h, ↓reduceDIte]
    rw [hj h.choose_spec]
  have hkm : ∀ i, k i < m := by
    intro i
    by_cases h : ∃ E, j E = i
    · obtain ⟨E, rfl⟩ := h
      rw [hk E]
      have h1 := hs E.1
      have h2 := hb E.1
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      have h3 : (-(E.1.ordForm s : ℚ)) < m := by nlinarith [mul_lt_mul_of_pos_left h2 hm']
      have h4 : (-(E.1.ordForm s)) < (m : ℤ) := by exact_mod_cast h3
      omega
    · simp only [k, h, ↓reduceDIte]; exact hm
  have hz0 : ∀ i, 0 < k i → eval U (z i) ⟨x, hxU⟩ = 0 := by
    intro i _
    have hmem : X.presheaf.germ U p hpU (z i) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) := by
      rw [hzt i, ← ht.1]; exact Ideal.subset_span ⟨i, rfl⟩
    by_contra hne
    have hb' := (toScheme_mem_basicOpen_iff ⟨x, hxU⟩ (z i)).2 hne
    rw [Scheme.mem_basicOpen _ _ _ hpU] at hb'
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem hb'
  -- the factorisation
  by_cases hg : φ * ∏ i, X.germToFunctionField U (z i) ^ k i = 0
  · exact ⟨U, hU, z, hz, hxU, U, hU, le_rfl, hxU, 0, k, hkm, by rw [map_zero, hg], hz0⟩
  obtain ⟨r, hr⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord p hg
    (fun Γ hΓ ↦ by
      refine zero_le_ord_mul_prod Γ hΓ φ U hpU z k hg ?_
      rw [← ordForm_eq_ord_pluriformCoeff sX s U z hz p hp hpU ht' Γ hΓ]
      by_cases hΓB : Γ ∈ B.support
      · refine Or.inr ⟨j ⟨Γ, hΓB, hΓ⟩, ?_, ?_⟩
        · rw [hzt, hI ⟨Γ, hΓB, hΓ⟩]
          exact Ideal.mem_span_singleton_self _
        · rw [hk ⟨Γ, hΓB, hΓ⟩]
          dsimp only
          omega
      · refine Or.inl ?_
        have h1 := hs Γ
        rw [show B.coeff Γ = 0 from Finsupp.notMem_support_iff.mp hΓB, mul_zero, add_zero] at h1
        exact_mod_cast h1)
  obtain ⟨V, hpV, h, rfl⟩ := X.presheaf.exists_germ_eq r
  have hV : Nonempty V := ⟨⟨p, hpV⟩⟩
  have hU' : Nonempty (V ⊓ U : X.Opens) := ⟨⟨p, hpV, hpU⟩⟩
  refine ⟨U, hU, z, hz, hxU, V ⊓ U, hU', inf_le_right, mem_chart_iff.2 ⟨hpV, hpU⟩,
    X.presheaf.map (homOfLE inf_le_left).op h, k, hkm, ?_, hz0⟩
  rw [Proof_lem_mmp_analytic_pluriform_density_intrinsic.germToFunctionField_res, ← hr,
    Scheme.algebraMap_germ_eq_germToFunctionField]

/-- **The local bound of the density**: around every point there are étale coordinates `z` on
`U` and an open neighbourhood `N` of `x` on which the density of `s` is at most
`C ∏ |zᵢ - zᵢ(x)|^{-2eᵢ}` with all `eᵢ < 1`. -/
private theorem exists_pluriformDensity_le {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [IsLocallyNoetherian X]
    (B : MMP.Mori.DivisorWithCoeffs ℚ X) (hB : B.IsSNC sX) (hb : ∀ E, B.coeff E < 1)
    {m : ℕ} (hm : 0 < m) (s : MMP.Mori.RationalPluriForms sX n m)
    (hs : ∀ E : MMP.Mori.PrimeDivisor X, 0 ≤ (E.ordForm s : ℚ) + m * B.coeff E)
    (x : ComplexPoints sX) :
    ∃ (U : X.Opens) (_ : Nonempty U) (z : Fin n → Γ(X, U))
      (_ : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (hxU : x ∈ chart U) (N : Set (ComplexPoints sX)) (C : ℝ≥0) (e : Fin n → ℝ),
      IsOpen N ∧ x ∈ N ∧ (∀ i, e i < 1) ∧
      ∀ (y : ComplexPoints sX) (hy : y ∈ chart U), y ∈ N →
        pluriformDensity sX m (pluriformCoeff sX s U z) y ≤
          (C : ℝ≥0∞) * ∏ i, ‖eval U (z i) ⟨y, hy⟩ - eval U (z i) ⟨x, hxU⟩‖ₑ ^ (-2 * e i) := by
  obtain ⟨U, hU, z, hz, hxU, U', hU'n, hU', hx, h, k, hk, hfac, hz0⟩ :=
    exists_etale_coordinates_germ_eq_mul_prod sX B hB hb hm s hs x
  obtain ⟨N, C, hNo, hxN, hle⟩ := pluriformDensity_le_of_germ_eq_mul_prod sX hm
    (pluriformCoeff sX s U z) U z U' hU' h k hfac x hxU hx hz0
  refine ⟨U, hU, z, hz, hxU, N, C, fun i ↦ (k i : ℝ) / m, hNo, hxN, fun i ↦ ?_, hle⟩
  rw [div_lt_one (by exact_mod_cast hm)]
  exact_mod_cast hk i

open scoped Classical in
/-- The local bound near an snc divisor (clause 2). -/
private theorem exists_chart_le_withDensity {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [IsLocallyNoetherian X]
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)]
    (B : MMP.Mori.DivisorWithCoeffs ℚ X) (hB : B.IsSNC sX) (hb : ∀ E, B.coeff E < 1)
    {m : ℕ} (hm : 0 < m) (s : MMP.Mori.RationalPluriForms sX n m)
    (hs : ∀ E : MMP.Mori.PrimeDivisor X, 0 ≤ (E.ordForm s : ℚ) + m * B.coeff E) :
    ∀ x : ComplexPoints sX, ∃ (U : X.Opens) (_ : Nonempty U) (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩))
      (hx : x ∈ W) (ε : ℝ) (C : ℝ≥0) (e : Fin n → ℝ), 0 < ε ∧ (∀ i, e i < 1) ∧
        Set.range (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩) =
          Set.univ.pi (fun i ↦ Metric.ball (eval U (z i) ⟨x, hW hx⟩) ε) ∧
        pluriformChartMeasure sX hm s U z hz W hW hWo hWz ≤
          (C : ℝ≥0∞) • ((Measure.comap (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)
            (volume : Measure (Fin n → ℂ))).map Subtype.val).withDensity
            (fun y ↦ if hy : y ∈ chart U then
              ∏ i, ‖eval U (z i) ⟨y, hy⟩ - eval U (z i) ⟨x, hW hx⟩‖ₑ ^ (-2 * e i)
              else 0) := by
  intro x
  obtain ⟨U, hU, z, hz, hxU, N, C, e, hNo, hxN, he, hle⟩ :=
    exists_pluriformDensity_le sX B hB hb hm s hs x
  obtain ⟨W', hW', hW'o, hxW', hW'z⟩ :=
    (etaleCoordinate_atlas sX).2.1 U z hz x hxU
  obtain ⟨W, hW, hWo, hWN, hx, ε, hε, hWz, hrange⟩ :=
    exists_isOpenEmbedding_range_eq_pi_ball (S := chart U)
      (fun y ↦ fun i ↦ eval U (z i) y) W' hW' hW'o hW'z N hNo x hxW' hxN
  refine ⟨U, hU, z, hz, W, hW, hWo, hWz, hx, ε, C, e, hε, he, hrange, ?_⟩
  have hbase : ((Measure.comap (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)
      (volume : Measure (Fin n → ℂ))).map Subtype.val) Wᶜ = 0 := by
    rw [Measure.map_apply measurable_subtype_coe hWo.measurableSet.compl]
    simp
  refine (withDensity_mono (ae_iff.2 (measure_mono_null (fun y hy ↦ ?_) hbase))).trans_eq
    (withDensity_smul' (C : ℝ≥0∞) _ ENNReal.coe_ne_top)
  intro hyW
  apply hy
  have hyU : y ∈ chart U := hW hyW
  simp only [Pi.smul_apply, smul_eq_mul, dif_pos hyU]
  exact hle y hyU (hWN hyW)

/-- Finiteness of every chart measure (clause 1): finitely many of the charts of the local
bound cover the compact space `X^an`, each has finite measure by the integrability of
`∏ |wᵢ - cᵢ|^{-2eᵢ}` on polydiscs, and any chart measure agrees with them on the overlaps. -/
private theorem isFiniteMeasure_pluriformChartMeasure {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [IsLocallyNoetherian X]
    (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX)
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)]
    (B : MMP.Mori.DivisorWithCoeffs ℚ X) (hB : B.IsSNC sX) (hb : ∀ E, B.coeff E < 1)
    {m : ℕ} (hm : 0 < m) (s : MMP.Mori.RationalPluriForms sX n m)
    (hs : ∀ E : MMP.Mori.PrimeDivisor X, 0 ≤ (E.ordForm s : ℚ) + m * B.coeff E) :
    ∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
        IsFiniteMeasure (pluriformChartMeasure sX hm s U z hz W hW hWo hWz) := by
  classical
  intro U _ z hz W hW hWo hWz
  have := compactSpace_complexPoints sX hX
  have hloc := exists_chart_le_withDensity sX B hB hb hm s hs
  choose Ux hUx zx hzx Wx hWx hWox hWzx hx εx Cx ex hεx hex hrangex hlex using hloc
  -- each chart of the local bound has finite measure
  have hfin : ∀ x, pluriformChartMeasure sX hm s (Ux x) (zx x) (hzx x) (Wx x) (hWx x)
      (hWox x) (hWzx x) Set.univ < ∞ := by
    intro x
    have : Nonempty (Ux x) := hUx x
    refine (hlex x Set.univ).trans_lt ?_
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_map_comap_eq_setLIntegral_range (Wx x) (hWox x) _ (hWzx x)
        (fun w ↦ ∏ i, ‖w i - eval (Ux x) (zx x i) ⟨x, hWx x (hx x)⟩‖ₑ ^ (-2 * ex x i))
        _ (fun y ↦ by rw [dif_pos (hWx x y.2)]), hrangex x, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (lintegral_pi_ball_prod_enorm_sub_rpow_lt_top (Fin n) (ex x) (hex x) _ (εx x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover Wx hWox
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  set μ := pluriformChartMeasure sX hm s U z hz W hW hWo hWz
  refine ⟨?_⟩
  calc μ Set.univ ≤ μ (⋃ x ∈ t, Wx x) := measure_mono ht
    _ ≤ ∑ x ∈ t, μ (Wx x) := measure_biUnion_finset_le t _
    _ < ∞ := by
      refine ENNReal.sum_lt_top.2 fun x _ ↦ ?_
      have : Nonempty (Ux x) := hUx x
      have hsupp : μ Wᶜ = 0 := withDensity_map_subtype_val_compl W hWo.measurableSet _ _
      calc μ (Wx x) ≤ μ (W ∩ Wx x) + μ Wᶜ := by
            refine (measure_mono fun y hy ↦ ?_).trans (measure_union_le _ _)
            by_cases hyW : y ∈ W
            · exact Or.inl ⟨hyW, hy⟩
            · exact Or.inr hyW
        _ = (μ.restrict (W ∩ Wx x)) Set.univ := by
            rw [hsupp, add_zero, Measure.restrict_apply_univ]
        _ = (pluriformChartMeasure sX hm s (Ux x) (zx x) (hzx x) (Wx x) (hWx x)
              (hWox x) (hWzx x)).restrict (W ∩ Wx x) Set.univ := by
            rw [(pluriformChartMeasure_intrinsic sX hm s).1 U z hz W hW hWo hWz (Ux x) (zx x)
              (hzx x) (Wx x) (hWx x) (hWox x) (hWzx x)]
        _ ≤ pluriformChartMeasure sX hm s (Ux x) (zx x) (hzx x) (Wx x) (hWx x)
              (hWox x) (hWzx x) Set.univ := Measure.restrict_apply_le _ _
        _ < ∞ := hfin x

end MMP.Analytic.Proof_lem_mmp_analytic_snc_density_integrable

namespace MMP.Analytic.ComplexPoints

open scoped Classical in
open MMP.Analytic.Proof_lem_mmp_analytic_snc_density_integrable in
/-- **Integrability near an snc divisor.** Let `X` be a smooth projective complex variety of
dimension `n`, `B` a `ℚ`-divisor with snc support and all coefficients `< 1`, and `s` a rational
section of `ω_X^{⊗m}`, `m > 0`, with `div(s) + mB ≥ 0`. Then

1. every chart measure `pluriformChartMeasure` of `s` is finite, i.e. `μ_s(X^an) < ∞`;
2. every point `x` lies in a chart `W` whose image under the coordinates is a polydisc around
   `z(x)`, on which the chart measure is at most `C ∏ᵢ |zᵢ - zᵢ(x)|^{-2eᵢ} dλ` for some
   constant `C` and exponents `eᵢ < 1`;
3. `∏ᵢ |wᵢ|^{-2eᵢ}` is integrable on every polydisc of `ℂ^ι` whenever all `eᵢ < 1`. -/
@[mmp "lem_mmp_analytic_snc_density_integrable"]
public theorem isFiniteMeasure_pluriformChartMeasure_of_isSNC {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [IsLocallyNoetherian X]
    (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX)
    [MeasurableSpace (ComplexPoints sX)] [BorelSpace (ComplexPoints sX)]
    (B : MMP.Mori.DivisorWithCoeffs ℚ X) (hB : B.IsSNC sX) (hb : ∀ E, B.coeff E < 1)
    {m : ℕ} (hm : 0 < m) (s : MMP.Mori.RationalPluriForms sX n m)
    (hs : ∀ E : MMP.Mori.PrimeDivisor X, 0 ≤ (E.ordForm s : ℚ) + m * B.coeff E) :
    (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
        IsFiniteMeasure (pluriformChartMeasure sX hm s U z hz W hW hWo hWz)) ∧
    (∀ x : ComplexPoints sX, ∃ (U : X.Opens) (_ : Nonempty U) (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩))
      (hx : x ∈ W) (ε : ℝ) (C : ℝ≥0) (e : Fin n → ℝ), 0 < ε ∧ (∀ i, e i < 1) ∧
        Set.range (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩) =
          Set.univ.pi (fun i ↦ Metric.ball (eval U (z i) ⟨x, hW hx⟩) ε) ∧
        pluriformChartMeasure sX hm s U z hz W hW hWo hWz ≤
          (C : ℝ≥0∞) • ((Measure.comap (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)
            (volume : Measure (Fin n → ℂ))).map Subtype.val).withDensity
            (fun y ↦ if hy : y ∈ chart U then
              ∏ i, ‖eval U (z i) ⟨y, hy⟩ - eval U (z i) ⟨x, hW hx⟩‖ₑ ^ (-2 * e i)
              else 0)) ∧
    (∀ (ι : Type) [Fintype ι] (e : ι → ℝ), (∀ i, e i < 1) → ∀ (c : ι → ℂ) (ε : ℝ),
      ∫⁻ w in Set.univ.pi (fun i ↦ Metric.ball (c i) ε), ∏ i, ‖w i - c i‖ₑ ^ (-2 * e i) < ∞) := by
  exact ⟨isFiniteMeasure_pluriformChartMeasure sX hX B hB hb hm s hs,
    exists_chart_le_withDensity sX B hB hb hm s hs,
    fun ι _ e he c ε ↦ lintegral_pi_ball_prod_enorm_sub_rpow_lt_top ι e he c ε⟩

end MMP.Analytic.ComplexPoints

end

/-!
## Étale morphisms realize to local homeomorphisms

Let `f : X ⟶ S` be an étale morphism of schemes of finite type over `ℂ`, possibly singular,
compatible with the structure morphisms `sX` and `sS`. Then the realized map
`f^an : X^an ⟶ S^an` of complex realizations, `x ↦ x ≫ f`, is a local homeomorphism.

### Main results

* `MMP.Analytic.ComplexPoints.isLocalHomeomorph_realize_of_etale`: the realization of an étale
  morphism of schemes of finite type over `ℂ` is a local homeomorphism.

### Implementation notes

* "Finite type over `ℂ`" is spelled `LocallyOfFiniteType` together with `QuasiCompact` of the
  structure morphism, for both `X` and `S`.
* A morphism of schemes over `ℂ` is a morphism `f : X ⟶ S` with `f ≫ sS = sX`; its
  realization is `MMP.Analytic.ComplexPoints.realize f hf`.

### References

* [Serre, *Géométrie algébrique et géométrie analytique*]
* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

section

open CategoryTheory AlgebraicGeometry Topology Polynomial MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Analytic.Proof_lem_mmp_realization_etale_local_homeomorphism

section SimpleRoot

/-- A complex-linear map `ℂ → ℂ` given by a nonzero derivative is invertible. -/
private theorem isInvertible_of_deriv {g : ℂ → ℂ} {z : ℂ} (h : deriv g z ≠ 0) :
    (fderiv ℂ g z).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h), ?_⟩
  ext
  simp [fderiv_apply_one_eq_deriv]

/-- Implicit function theorem for simple roots: on the locus of pairs `(t, z)` where `z` is a
root of `∑ cᵢ(t) zⁱ` with `G(t, z) ≠ 0`, at which every root is simple, the projection to `t`
is a local homeomorphism. -/
private theorem isLocalHomeomorph_fst_of_deriv_ne_zero {T : Type*} [TopologicalSpace T] {m : ℕ}
    {c : T → Fin m → ℂ} (hc : Continuous c) {G : T × ℂ → ℂ} (hG : Continuous G)
    (hd : ∀ q : T × ℂ, (∑ i, c q.1 i * q.2 ^ (i : ℕ)) = 0 → G q ≠ 0 →
      deriv (fun z => ∑ i, c q.1 i * z ^ (i : ℕ)) q.2 ≠ 0) :
    IsLocalHomeomorph (fun q : {q : T × ℂ // (∑ i, c q.1 i * q.2 ^ (i : ℕ)) = 0 ∧ G q ≠ 0} =>
      q.1.1) := by
  classical
  set Z := {q : T × ℂ // (∑ i, c q.1 i * q.2 ^ (i : ℕ)) = 0 ∧ G q ≠ 0}
  let Φ : (Fin m → ℂ) × ℂ → ℂ := fun v => ∑ i, v.1 i * v.2 ^ (i : ℕ)
  have hΦ : ContDiff ℂ ⊤ Φ := by fun_prop
  refine IsLocalHomeomorph.mk _ fun q₀ => ?_
  let u : (Fin m → ℂ) × ℂ := (c q₀.1.1, q₀.1.2)
  have dfu : HasStrictFDerivAt Φ (fderiv ℂ Φ u) u :=
    hΦ.contDiffAt.hasStrictFDerivAt (by simp)
  have hcomp : fderiv ℂ Φ u ∘L .inr ℂ (Fin m → ℂ) ℂ = fderiv ℂ (fun z => Φ (u.1, z)) u.2 := by
    have h1 := (hΦ.differentiable (by simp) u).hasFDerivAt.comp u.2
      (hasFDerivAt_prodMk_right u.1 u.2)
    exact (h1.fderiv).symm
  have if₂u : (fderiv ℂ Φ u ∘L .inr ℂ (Fin m → ℂ) ℂ).IsInvertible := by
    rw [hcomp]
    exact isInvertible_of_deriv (hd q₀.1 q₀.2.1 q₀.2.2)
  let φ := dfu.implicitFunctionDataOfProdDomain if₂u
  let H := φ.toOpenPartialHomeomorph
  have hH : ∀ v, H v = (Φ v, v.1) := fun v => by
    simp only [H, ImplicitFunctionData.toOpenPartialHomeomorph_coe,
      ImplicitFunctionData.prodFun_apply, φ,
      HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
      HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain]
  -- the implicit function
  let τ : T → ℂ := fun t => (H.symm (0, c t)).2
  have hsymm : ∀ t, (0, c t) ∈ H.target → H.symm (0, c t) = (c t, τ t) ∧ Φ (c t, τ t) = 0 := by
    intro t ht
    have e := H.right_inv ht
    rw [hH] at e
    have e1 : (H.symm (0, c t)).1 = c t := congrArg Prod.snd e
    have e2 : Φ (H.symm (0, c t)) = 0 := congrArg Prod.fst e
    refine ⟨Prod.ext e1 rfl, ?_⟩
    rwa [← e1]
  let D : Set T := {t | (0, c t) ∈ H.target ∧ G (t, τ t) ≠ 0}
  have hτD : ∀ t ∈ D, (∑ i, c t i * τ t ^ (i : ℕ)) = 0 ∧ G (t, τ t) ≠ 0 :=
    fun t ht => ⟨(hsymm t ht.1).2, ht.2⟩
  let σ : T → Z := fun t => if h : t ∈ D then ⟨(t, τ t), hτD t h⟩ else q₀
  have hcont1 : Continuous fun q : Z => (c q.1.1, q.1.2) :=
    (hc.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)
  have hτc : ContinuousOn τ {t | (0, c t) ∈ H.target} :=
    continuous_snd.comp_continuousOn (H.continuousOn_symm.comp
      (continuous_const.prodMk hc).continuousOn fun t ht => ht)
  have hopenT : IsOpen {t | (0, c t) ∈ H.target} :=
    H.open_target.preimage (continuous_const.prodMk hc)
  have hsrc : ∀ q : Z, (c q.1.1, q.1.2) ∈ H.source →
      (0, c q.1.1) ∈ H.target ∧ τ q.1.1 = q.1.2 := by
    intro q hq
    have e : H (c q.1.1, q.1.2) = (0, c q.1.1) := by rw [hH]; exact Prod.ext q.2.1 rfl
    have ht := H.map_source hq
    rw [e] at ht
    refine ⟨ht, ?_⟩
    have := H.left_inv hq
    rw [e] at this
    exact congrArg Prod.snd this
  have hsrcD : ∀ q : Z, (c q.1.1, q.1.2) ∈ H.source → q.1.1 ∈ D := fun q hq =>
    ⟨(hsrc q hq).1, by rw [(hsrc q hq).2]; exact q.2.2⟩
  let e : OpenPartialHomeomorph Z T :=
    { toFun := fun q => q.1.1
      invFun := σ
      source := {q | (c q.1.1, q.1.2) ∈ H.source}
      target := D
      map_source' := hsrcD
      map_target' := fun t ht => by
        simp only [σ, dif_pos ht, Set.mem_setOf_eq]
        have := H.map_target ht.1
        rwa [(hsymm t ht.1).1] at this
      left_inv' := fun q hq => by
        simp only [σ, dif_pos (hsrcD q hq)]
        exact Subtype.ext (Prod.ext rfl (hsrc q hq).2)
      right_inv' := fun t ht => by simp only [σ, dif_pos ht]
      open_source := H.open_source.preimage hcont1
      open_target := by
        have hf : ContinuousOn (fun t => G (t, τ t)) {t | (0, c t) ∈ H.target} :=
          hG.comp_continuousOn (continuousOn_id.prodMk hτc)
        exact hf.isOpen_inter_preimage hopenT isOpen_compl_singleton
      continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        convert (Continuous.subtype_mk (f := fun t : D => (t.1, τ t.1))
          (p := fun q : T × ℂ => (∑ i, c q.1 i * q.2 ^ (i : ℕ)) = 0 ∧ G q ≠ 0)
          (continuous_subtype_val.prodMk
          (hτc.mono fun t ht => ht.1).restrict) (fun t : D => hτD t.1 t.2)) using 1
        funext t
        simp only [Set.restrict_apply, σ, dif_pos t.2] }
  refine ⟨e, ?_, fun _ _ => rfl⟩
  have := φ.pt_mem_toOpenPartialHomeomorph_source
  rwa [HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain] at this

end SimpleRoot

section StandardEtale

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra A B]
    [IsScalarTower ℂ A B]

/-- A `ℂ`-algebra map `χ : B → ℂ` evaluates `p(x)`, `p ∈ A[X]`, as `p^ψ(χ x)` with `ψ = χ|_A`. -/
private theorem apply_aeval_eq (χ : B →ₐ[ℂ] ℂ) (x : B) (p : A[X]) :
    χ (aeval x p) = (p.map (χ.comp (IsScalarTower.toAlgHom ℂ A B)).toRingHom).eval (χ x) := by
  rw [Polynomial.eval_map, aeval_def, ← RingHom.coe_coe χ, hom_eval₂]
  rfl

/-- If `b · g(x)ⁿ = p(x)`, a `ℂ`-algebra map `χ : B → ℂ` with `g^ψ(χ x) ≠ 0`, `ψ = χ|_A`, takes
the value `p^ψ(χ x) / g^ψ(χ x)ⁿ` at `b`. -/
private theorem apply_eq_div_of_mul_eq (χ : B →ₐ[ℂ] ℂ) {x b : B} {g p : A[X]} {n : ℕ}
    (hg : (g.map (χ.comp (IsScalarTower.toAlgHom ℂ A B)).toRingHom).eval (χ x) ≠ 0)
    (hb : b * aeval x g ^ n = aeval x p) :
    χ b = (p.map (χ.comp (IsScalarTower.toAlgHom ℂ A B)).toRingHom).eval (χ x) /
      (g.map (χ.comp (IsScalarTower.toAlgHom ℂ A B)).toRingHom).eval (χ x) ^ n := by
  refine eq_div_of_mul_eq (pow_ne_zero _ hg) ?_
  have := congrArg χ hb
  rwa [map_mul, map_pow, apply_aeval_eq, apply_aeval_eq] at this

/-- Evaluation of `p^ψ` as a sum over the coefficients of `p`. -/
private theorem sum_eq_eval (ψ : A →ₐ[ℂ] ℂ) (p : A[X]) (z : ℂ) :
    (∑ i : Fin (p.natDegree + 1), ψ (p.coeff i) * z ^ (i : ℕ)) = (p.map ψ.toRingHom).eval z := by
  rw [Polynomial.eval_map, eval₂_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range (fun i => ψ.toRingHom (p.coeff i) * z ^ i)]
  rfl

/-- For `B` standard étale over `A`, restriction of `ℂ`-algebra maps `B → ℂ` to `A` is a local
homeomorphism for the topologies of pointwise convergence. -/
private theorem isLocalHomeomorph_comp_of_standardEtale (P : StandardEtalePresentation A B) :
    letI : TopologicalSpace (B →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
    letI : TopologicalSpace (A →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
    IsLocalHomeomorph (fun χ : B →ₐ[ℂ] ℂ => χ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  letI tB : TopologicalSpace (B →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
  letI tA : TopologicalSpace (A →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
  have hev : ∀ a : A, Continuous fun ψ : A →ₐ[ℂ] ℂ => ψ a :=
    fun a => (continuous_apply a).comp continuous_induced_dom
  have hevB : ∀ b : B, Continuous fun χ : B →ₐ[ℂ] ℂ => χ b :=
    fun b => (continuous_apply b).comp continuous_induced_dom
  let res : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ) := fun χ => χ.comp (IsScalarTower.toAlgHom ℂ A B)
  have hres : Continuous res := continuous_induced_rng.2 (continuous_pi fun a => hevB _)
  -- polynomial evaluation is continuous in the coefficients
  have hpoly : ∀ p : A[X],
      Continuous fun q : (A →ₐ[ℂ] ℂ) × ℂ => (p.map q.1.toRingHom).eval q.2 := by
    intro p
    simp_rw [← sum_eq_eval]
    exact continuous_finset_sum _ fun i _ =>
      ((hev _).comp continuous_fst).mul (continuous_snd.pow _)
  let c : (A →ₐ[ℂ] ℂ) → Fin (P.f.natDegree + 1) → ℂ := fun ψ i => ψ (P.f.coeff i)
  let G : (A →ₐ[ℂ] ℂ) × ℂ → ℂ := fun q => (P.g.map q.1.toRingHom).eval q.2
  have hfz : ∀ (ψ : A →ₐ[ℂ] ℂ) (z : ℂ) (p : A[X]), (p.map ψ.toRingHom).eval z =
      letI : Algebra A ℂ := ψ.toRingHom.toAlgebra; aeval z p := fun ψ z p => by
    letI : Algebra A ℂ := ψ.toRingHom.toAlgebra
    rw [aeval_def, Polynomial.eval_map]; rfl
  have key := isLocalHomeomorph_fst_of_deriv_ne_zero (c := c) (G := G)
    (continuous_pi fun i => hev _) (hpoly P.g) ?_
  swap
  · rintro ⟨ψ, z⟩ h0 hg
    have e : (fun z => ∑ i, c ψ i * z ^ (i : ℕ)) = fun z => (P.f.map ψ.toRingHom).eval z :=
      funext fun z => sum_eq_eval ψ P.f z
    simp only [e, Polynomial.deriv]
    simp only [c, sum_eq_eval] at h0
    obtain ⟨p₁, p₂, n, hn⟩ := P.cond
    have := congrArg (fun r : A[X] => (r.map ψ.toRingHom).eval z) hn
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, h0, zero_mul, add_zero, ← derivative_map] at this
    intro h
    rw [h, zero_mul] at this
    exact pow_ne_zero n hg this.symm
  let Z := {q : (A →ₐ[ℂ] ℂ) × ℂ // (∑ i, c q.1 i * q.2 ^ (i : ℕ)) = 0 ∧ G q ≠ 0}
  have hχ : ∀ χ : B →ₐ[ℂ] ℂ, (∑ i, c (res χ) i * (χ P.x) ^ (i : ℕ)) = 0 ∧ G (res χ, χ P.x) ≠ 0 := by
    intro χ
    simp only [c, G, sum_eq_eval]
    refine ⟨?_, fun h => (P.hasMap.2.map χ).ne_zero ?_⟩
    · have := apply_aeval_eq χ P.x P.f
      rw [P.hasMap.1, map_zero] at this
      exact this.symm
    · rw [apply_aeval_eq]; exact h
  have hinj : ∀ χ₁ χ₂ : B →ₐ[ℂ] ℂ, res χ₁ = res χ₂ → χ₁ P.x = χ₂ P.x → χ₁ = χ₂ := by
    intro χ₁ χ₂ h1 h2
    ext b
    obtain ⟨p, n, hb⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x b
    simp only [res] at h1
    rw [apply_eq_div_of_mul_eq χ₁ (hχ χ₁).2 hb, apply_eq_div_of_mul_eq χ₂ (hχ χ₂).2 hb, h1, h2]
  -- construction of the inverse
  have hcon : ∀ q : Z, ∃ χ : B →ₐ[ℂ] ℂ, res χ = q.1.1 ∧ χ P.x = q.1.2 := by
    rintro ⟨⟨ψ, z⟩, h0, hg⟩
    letI : Algebra A ℂ := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
    simp only [c, G, sum_eq_eval, hfz] at h0 hg
    have hm : P.HasMap z := ⟨h0, isUnit_iff_ne_zero.2 hg⟩
    refine ⟨((P.lift z hm).comp P.equivRing.toAlgHom).restrictScalars ℂ, ?_, ?_⟩
    · ext a
      change (P.lift z hm) (P.equivRing (algebraMap A B a)) = ψ a
      rw [AlgEquiv.commutes, AlgHom.commutes]; rfl
    · change (P.lift z hm) (P.equivRing P.x) = z
      rw [StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X]
  choose inv hinv1 hinv2 using hcon
  let Θ : (B →ₐ[ℂ] ℂ) ≃ Z :=
    { toFun := fun χ => ⟨(res χ, χ P.x), hχ χ⟩
      invFun := inv
      left_inv := fun χ => hinj _ _ (hinv1 _) (hinv2 _)
      right_inv := fun q => Subtype.ext (Prod.ext (hinv1 q) (hinv2 q)) }
  let Θh : (B →ₐ[ℂ] ℂ) ≃ₜ Z :=
    { Θ with
      continuous_toFun := Continuous.subtype_mk (hres.prodMk (hevB _)) _
      continuous_invFun := by
        refine continuous_induced_rng.2 (continuous_pi fun b => ?_)
        obtain ⟨p, n, hb⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x b
        have e : ∀ q : Z, inv q b = (p.map q.1.1.toRingHom).eval q.1.2 / G q.1 ^ n := by
          intro q
          have h1 := hinv1 q
          simp only [res] at h1
          rw [apply_eq_div_of_mul_eq (inv q) (hχ (inv q)).2 hb, h1, hinv2 q]
        change Continuous fun q : Z => inv q b
        rw [show (fun q : Z => inv q b) = _ from funext e]
        exact ((hpoly p).comp continuous_subtype_val).div
          (((hpoly P.g).comp continuous_subtype_val).pow n) fun q => pow_ne_zero _ q.2.2 }
  change IsLocalHomeomorph ((fun q : Z => q.1.1) ∘ Θh)
  exact key.comp Θh.isLocalHomeomorph

end StandardEtale

section Charts

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}

/-- The ring maps of a morphism over `ℂ` are `ℂ`-linear. -/
private theorem appLE_baseRingHom (f : X ⟶ S) (hf : f ≫ sS = sX) {U : S.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (a : ℂ) :
    (f.appLE U V e).hom (baseRingHom sS U a) = baseRingHom sX V a := by
  subst hf
  have key : sS.appTop ≫ S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ f.appLE U V e =
      (f ≫ sS).appTop ≫ X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop, Category.assoc]
    rfl
  have h := congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of ℂ)).inv a)) key
  exact h

/-- Evaluation at the realized point `y ≫ f` is evaluation at `y` after pulling back along `f`. -/
private theorem evalHom_realize (f : X ⟶ S) (hf : f ≫ sS = sX) {U : S.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (y : chart (sX := sX) V) :
    evalHom U ⟨realize f hf y.1, mem_chart_iff.2 (e (mem_chart_iff.1 y.2))⟩ =
      (evalHom V y).comp (f.appLE U V e).hom := by
  have key : f.appLE U V e ≫ y.1.hom.appLE V ⊤ y.2.ge =
      (realize f hf y.1).hom.appLE U ⊤ (mem_chart_iff.2 (e (mem_chart_iff.1 y.2))).ge :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  ext a
  have h := congrArg (fun φ => (Scheme.ΓSpecIso (.of ℂ)).hom (φ a)) key
  simpa [evalHom] using h.symm

/-- Evaluation at a `ℂ`-point of `V`, as a `ℂ`-algebra map `Γ(X, V) → ℂ`. -/
private noncomputable def evalAlgHom (V : X.Opens) (y : chart (sX := sX) V) :
    @AlgHom ℂ Γ(X, V) ℂ _ _ _ (baseRingHom sX V).toAlgebra _ :=
  letI := (baseRingHom sX V).toAlgebra
  { evalHom V y with commutes' := evalHom_baseRingHom V y }

/-- On an affine open `V`, evaluation identifies `V(ℂ)` (with the topology of `X^an`) with the
space of `ℂ`-algebra maps `Γ(X, V) → ℂ` (with the topology of pointwise convergence). -/
private theorem isHomeomorph_evalAlgHom {V : X.Opens} (hV : IsAffineOpen V) :
    letI := (baseRingHom sX V).toAlgebra
    letI : TopologicalSpace (Γ(X, V) →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
    IsHomeomorph (evalAlgHom (sX := sX) V) := by
  letI := (baseRingHom sX V).toAlgebra
  letI tB : TopologicalSpace (Γ(X, V) →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
  -- the topology of `X^an` on `V(ℂ)` is the one induced by the evaluations
  have htop : (inferInstance : TopologicalSpace (chart (sX := sX) V)) = chartTopology V := by
    refine le_antisymm ?_ (continuous_iff_le_induced.1 (continuous_chart_val ⟨V, hV⟩))
    refine le_iInf fun g => continuous_iff_le_induced.1 ?_
    letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
    have h := (InvertibleModule.continuousOn_evalExt (X := X) V g)
    rw [continuousOn_iff_continuous_restrict] at h
    exact (continuous_congr fun y : chart (sX := sX) V =>
      (InvertibleModule.evalExt_of_mem (X := X) g y.2).symm).2 h
  have hind : IsInducing (evalAlgHom (sX := sX) V) := by
    rw [← (IsInducing.induced (DFunLike.coe : (Γ(X, V) →ₐ[ℂ] ℂ) → Γ(X, V) → ℂ)).of_comp_iff]
    refine ⟨htop.trans ?_⟩
    change ⨅ g : Γ(X, V), TopologicalSpace.induced (eval V g) inferInstance = _
    rw [Pi.topologicalSpace, induced_iInf]
    simp_rw [induced_compose]
    rfl
  haveI : IsIso (isAffineOpen_top (Spec (.of ℂ))).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  have hinj : Function.Injective (evalAlgHom (sX := sX) V) := by
    intro y y' h
    have hev : evalHom V y = evalHom V y' := RingHom.ext fun a => congrArg (fun φ => φ a) h
    have happ : y.1.hom.appLE V ⊤ y.2.ge = y'.1.hom.appLE V ⊤ y'.2.ge := by
      refine (cancel_mono (Scheme.ΓSpecIso (.of ℂ)).hom).1 ?_
      ext1
      exact hev
    refine Subtype.ext (ComplexPoints.ext ((cancel_epi (isAffineOpen_top _).fromSpec).1 ?_))
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top _) y.2.ge,
      ← IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top _) y'.2.ge, happ]
  have hsurj : Function.Surjective (evalAlgHom (sX := sX) V) := by
    intro φ
    let x : Spec (.of ℂ) ⟶ X := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec
    have hmem : x ⁻¹ᵁ V = ⊤ := by
      refine eq_top_iff.2 fun t _ => ?_
      change x t ∈ V
      rw [Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← hV.range_fromSpec]
      exact ⟨_, rfl⟩
    have htop' : (isAffineOpen_top (Spec (.of ℂ))).fromSpec =
        Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
      rfl
    have hsec : x ≫ sX = 𝟙 _ := by
      have h := IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hV (by simp)
      rw [Category.assoc, ← h, htop', ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id,
        Spec.map_inj]
      ext a
      change φ (baseRingHom sX V a) = a
      exact φ.commutes a
    have happ : x.appLE V ⊤ hmem.ge =
        CommRingCat.ofHom φ.toRingHom ≫ (Scheme.ΓSpecIso (.of ℂ)).inv := by
      rw [← Spec.map_inj, Spec.map_comp, ← htop']
      refine (cancel_mono hV.fromSpec).1 ?_
      rw [IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top _) hmem.ge, Category.assoc]
    refine ⟨⟨⟨x, hsec⟩, hmem⟩, AlgHom.ext fun a => ?_⟩
    change (Scheme.ΓSpecIso (.of ℂ)).hom (x.appLE V ⊤ hmem.ge a) = φ a
    rw [happ]
    exact Iso.inv_hom_id_apply _ _
  exact (isHomeomorph_iff_isEmbedding_surjective).2 ⟨⟨hind, hinj⟩, hsurj⟩

/-- An étale morphism is, locally on source and target, standard étale on sections. -/
private theorem exists_standardEtalePresentation (f : X ⟶ S) [Etale f] (p : X) :
    ∃ (U : S.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : p ∈ V)
      (e : V ≤ f ⁻¹ᵁ U), Nonempty (@StandardEtalePresentation Γ(S, U) Γ(X, V) _ _
        (f.appLE U V e).hom.toAlgebra) := by
  obtain ⟨U, hU, hfp, -⟩ := exists_isAffineOpen_mem_and_subset (Set.mem_univ (f p)) (U := ⊤)
  obtain ⟨V₀, hV₀, hp, e₀'⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := f ⁻¹ᵁ U) hfp
  have e₀ : V₀ ≤ f ⁻¹ᵁ U := e₀'
  letI : Algebra Γ(S, U) Γ(X, V₀) := (f.appLE U V₀ e₀).hom.toAlgebra
  haveI : Algebra.Etale Γ(S, U) Γ(X, V₀) := Etale.etale_appLE f hU hV₀ e₀
  let Q := (hV₀.primeIdealOf ⟨p, hp⟩).asIdeal
  haveI : Algebra.IsEtaleAt Γ(S, U) Q := inferInstance
  obtain ⟨g, hgQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := Γ(S, U)) Q
  have hpg : p ∈ X.basicOpen g := by
    have h := hV₀.fromSpec_primeIdealOf ⟨p, hp⟩
    have : hV₀.primeIdealOf ⟨p, hp⟩ ∈ hV₀.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hV₀.fromSpec_preimage_basicOpen]
      exact hgQ
    change hV₀.fromSpec _ ∈ X.basicOpen g at this
    rwa [h] at this
  have e : X.basicOpen g ≤ f ⁻¹ᵁ U := (X.basicOpen_le g).trans e₀
  refine ⟨U, X.basicOpen g, hU, hV₀.basicOpen g, hpg, e, ?_⟩
  letI : Algebra Γ(X, V₀) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(X, X.basicOpen g) := (f.appLE U (X.basicOpen g) e).hom.toAlgebra
  haveI : IsScalarTower Γ(S, U) Γ(X, V₀) Γ(X, X.basicOpen g) := .of_algebraMap_eq fun a => by
    change _ = (X.presheaf.map _).hom ((f.appLE U V₀ e₀).hom a)
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    rfl
  haveI := hV₀.isLocalization_basicOpen g
  let eq : Localization.Away g ≃ₐ[Γ(S, U)] Γ(X, X.basicOpen g) :=
    (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      Γ(X, X.basicOpen g)).restrictScalars Γ(S, U)
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  exact ⟨P.mapEquiv eq⟩

end Charts

end MMP.Analytic.Proof_lem_mmp_realization_etale_local_homeomorphism

namespace MMP.Analytic.ComplexPoints

open MMP.Analytic.Proof_lem_mmp_realization_etale_local_homeomorphism in
/-- **Étale morphisms realize to local homeomorphisms.** Let `f : X ⟶ S` be an étale morphism
of schemes of finite type over `ℂ` (no smoothness is assumed). Then the realized map
`f^an : X^an → S^an`, `x ↦ x ≫ f`, is a local homeomorphism. -/
@[mmp "lem_mmp_realization_etale_local_homeomorphism"]
public theorem isLocalHomeomorph_realize_of_etale {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] [QuasiCompact sX]
    [LocallyOfFiniteType sS] [QuasiCompact sS] (f : X ⟶ S) (hf : f ≫ sS = sX) [Etale f] :
    IsLocalHomeomorph (realize f hf) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  intro x _
  obtain ⟨U, V, hU, hV, hp, e, ⟨P⟩⟩ := exists_standardEtalePresentation f x.toScheme
  letI : Algebra ℂ Γ(S, U) := (baseRingHom sS U).toAlgebra
  letI : Algebra ℂ Γ(X, V) := (baseRingHom sX V).toAlgebra
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  haveI : IsScalarTower ℂ Γ(S, U) Γ(X, V) :=
    .of_algebraMap_eq fun a => (appLE_baseRingHom f hf e a).symm
  letI tB : TopologicalSpace (Γ(X, V) →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
  letI tA : TopologicalSpace (Γ(S, U) →ₐ[ℂ] ℂ) := .induced DFunLike.coe inferInstance
  have hres := isLocalHomeomorph_comp_of_standardEtale P
  let EV := (isHomeomorph_evalAlgHom (sX := sX) hV).homeomorph
  let EU := (isHomeomorph_evalAlgHom (sX := sS) hU).homeomorph
  let r : chart (sX := sX) V → chart (sX := sS) U :=
    fun y => ⟨realize f hf y.1, mem_chart_iff.2 (e (mem_chart_iff.1 y.2))⟩
  have hsq : r = EU.symm ∘ (fun χ : Γ(X, V) →ₐ[ℂ] ℂ => χ.comp (IsScalarTower.toAlgHom ℂ _ _)) ∘
      EV := by
    funext y
    apply EU.injective
    rw [Function.comp_apply, Homeomorph.apply_symm_apply]
    refine AlgHom.ext fun a => ?_
    exact congrArg (fun φ : Γ(S, U) →+* ℂ => φ a) (evalHom_realize f hf e y)
  have hr : IsLocalHomeomorph r := by
    rw [hsq]
    exact EU.symm.isLocalHomeomorph.comp (hres.comp EV.isLocalHomeomorph)
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : S.Over (Spec (.of ℂ)) := ⟨sS⟩
  have h1 : IsLocalHomeomorph (realize f hf ∘ (Subtype.val : chart (sX := sX) V → _)) :=
    (InvertibleModule.isOpen_chart U).isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp hr
  have h2 := (InvertibleModule.isOpen_chart V).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have := IsLocalHomeomorphOn.of_comp_right (s := Set.univ) (h1.isLocalHomeomorphOn (s := Set.univ))
    (h2.isLocalHomeomorphOn (s := Set.univ))
  exact this x ⟨⟨x, mem_chart_iff.2 hp⟩, trivial, rfl⟩

end MMP.Analytic.ComplexPoints

end

/-! ## Proper Zariski closed subsets for the glued measure `μ_s` -/

section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Analytic.ComplexPoints

open MMP.Analytic.Proof_lem_mmp_analytic_pluriform_density_intrinsic in
/-- **Proper closed subsets are null; `μ_s` charges nonempty opens.** Let `X` be a smooth
irreducible complex variety of dimension `n`, `m > 0` and `s` a rational section of
`ω_X^{⊗m}`. Then

1. for every étale chart `W`, the chart measure `|φ|^{2/m} dλ` of `s` on `W` vanishes on `Z^an`
   for every proper Zariski closed `Z ⊊ X`, and, if `s ≠ 0`, is positive on every open set
   meeting `W`;
2. if `μ` is the glued measure `μ_s` (its restriction to every étale chart is the chart measure
   of `s`), then `μ(Z^an) = 0` for every proper Zariski closed `Z ⊊ X`;
3. if moreover `s ≠ 0`, then `μ(W) > 0` for every nonempty open `W ⊆ X^an`. -/
@[mmp "lem_mmp_analytic_proper_closed_null"]
public theorem measure_proper_closed_null_and_pos_of_isGlued {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) {n : ℕ} [AlgebraicGeometry.IsVariety ℂ sX]
    [SmoothOfRelativeDimension n sX] [MeasurableSpace (ComplexPoints sX)]
    [BorelSpace (ComplexPoints sX)] {m : ℕ} (hm : 0 < m)
    (s : MMP.Mori.RationalPluriForms sX n m) :
    -- (a) the chart-level statement
    (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
      (∀ Z : Set X, IsClosed Z → Z ≠ Set.univ →
        pluriformChartMeasure sX hm s U z hz W hW hWo hWz
          {x : ComplexPoints sX | Set.range x.hom.base ⊆ Z} = 0) ∧
      (s ≠ 0 → ∀ V : Set (ComplexPoints sX), IsOpen V → (V ∩ W).Nonempty →
        0 < pluriformChartMeasure sX hm s U z hz W hW hWo hWz V)) ∧
    -- (b), (c) the glued measure `μ_s`
    (∀ μ : Measure (ComplexPoints sX),
      (∀ (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
        (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
          (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
        (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
        (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)),
        μ.restrict W = pluriformChartMeasure sX hm s U z hz W hW hWo hWz) →
      (∀ Z : Set X, IsClosed Z → Z ≠ Set.univ →
        μ {x : ComplexPoints sX | Set.range x.hom.base ⊆ Z} = 0) ∧
      (s ≠ 0 → ∀ W : Set (ComplexPoints sX), IsOpen W → W.Nonempty → 0 < μ W)) := by
  have ha := fun (U : X.Opens) [Nonempty U] (z : Fin n → Γ(X, U))
      (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (hWo : IsOpen W)
      (hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) ↦
    pluriformChartMeasure_proper_closed_null sX hm s U z hz W hW hWo hWz
  refine ⟨ha, fun μ hμ ↦ ⟨fun Z hZ hZne ↦ ?_, fun hs V hV ⟨x, hxV⟩ ↦ ?_⟩⟩
  · obtain ⟨S, hSc, hSu⟩ := exists_countable_etaleChart_cover sX (n := n)
    set Zan := {x : ComplexPoints sX | Set.range x.hom.base ⊆ Z}
    have hsub : Zan ⊆ ⋃ c ∈ S, Zan ∩ c.W := by
      intro y hy
      have : y ∈ ⋃ c ∈ S, c.W := hSu ▸ Set.mem_univ y
      obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 this
      exact Set.mem_iUnion₂.2 ⟨c, hc, hy, hyc⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff hSc).2 fun c _ ↦ ?_)
    haveI := c.ne
    rw [← Measure.restrict_apply' c.hWo.measurableSet, hμ c.U c.z c.hz c.W c.hW c.hWo c.hWz]
    exact (ha c.U c.z c.hz c.W c.hW c.hWo c.hWz).1 Z hZ hZne
  · obtain ⟨c, hxc⟩ := exists_etaleChart_mem sX (n := n) x
    haveI := c.ne
    have hpos := (ha c.U c.z c.hz c.W c.hW c.hWo c.hWz).2 hs V hV ⟨x, hxV, hxc⟩
    rw [← hμ c.U c.z c.hz c.W c.hW c.hWo c.hWz,
      Measure.restrict_apply' c.hWo.measurableSet] at hpos
    exact hpos.trans_le (measure_mono Set.inter_subset_left)

end MMP.Analytic.ComplexPoints

end

/-!
## Proper morphisms realize to proper maps

For a proper morphism `f : X ⟶ S` of schemes of finite type over `ℂ`, the realized map
`f^an : X^an → S^an` is separated and proper (continuous and universally closed). Under the
homeomorphism `X^an ≃ₜ X(ℂ)` with Fulton's underlying space the realized map is the induced map
of underlying spaces, which is proper by `MMP.UnderlyingSpace.isProperMap_map`.
Separatedness comes from the diagonal: the diagonal `X ⟶ X ×_S X` of the separated morphism `f`
is a closed immersion, so its realization is a closed embedding, and `(X ×_S X)(ℂ)` is the
topological fibre product `X(ℂ) ×_{S(ℂ)} X(ℂ)`.

Universal closedness of a continuous map is Mathlib's `IsProperMap` (Bourbaki properness,
`isProperMap_iff_universally_closed`); separatedness is `IsSeparatedMap`.

As an application, the topological derived proper base change theorem
`MMP.isIso_baseChange_of_isProperMap` applies to every cartesian square of topological spaces
over `f^an`: the base change morphism `g⁻¹ R(f^an)_* K ⟶ Rf'_* g'⁻¹ K` is an isomorphism for
every bounded below complex `K` of abelian sheaves, or of sheaves of `R`-modules over a
`ℚ`-algebra `R`, on `X^an`. Taking `Y'` a point `s` of `S^an` identifies the stalk
`(R(f^an)_* K)_s` with the hypercohomology of the fibre `(f^an)⁻¹(s)`.

### Main results

* `MMP.Analytic.ComplexPoints.isSeparatedMap_and_isProperMap_realize`: the realization of a
  proper morphism of finite-type complex schemes is a separated proper map.
* `MMP.Analytic.ComplexPoints.isIso_baseChange_analyticMap_of_isProper`: derived proper base
  change for the realization of a proper morphism, and the stalk formula
  `(Hᵠ R(f^an)_* K)_s ≅ Hᵠ((f^an)⁻¹(s), K|_{(f^an)⁻¹(s)})`.

### References

* [Serre, *Géométrie algébrique et géométrie analytique*]
* [Stacks Project, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
* [SGA4, Exposé XII, 5.1]
-/

section

open CategoryTheory AlgebraicGeometry MMP UnderlyingSpace

namespace MMP.Analytic.ComplexPoints

section Separated

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [ContinuousInv₀ K] [T1Space K]

/-- For a pullback square `P = A ×_S B` over `K`, the map `P(K) → A(K) ×_{S(K)} B(K)` into the
topological fibre product is a closed embedding (indeed a homeomorphism). -/
private lemma isClosedEmbedding_toPullback {P A B S : Scheme.{0}} [P.Over (Spec (.of K))]
    [A.Over (Spec (.of K))] [B.Over (Spec (.of K))] [S.Over (Spec (.of K))]
    {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S} [fst.IsOver (Spec (.of K))]
    [snd.IsOver (Spec (.of K))] [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))]
    (H : IsPullback fst snd f g) :
    Topology.IsClosedEmbedding fun z : UnderlyingSpace K P ↦ (⟨prodMap fst snd z,
      UnderlyingSpace.ext (by simp [prodMap, H.w])⟩ :
        Function.Pullback (UnderlyingSpace.map f) (UnderlyingSpace.map g)) := by
  refine ⟨(isEmbedding_prodMap_of_isPullback (K := K) H).codRestrict
    {p | UnderlyingSpace.map f p.1 = UnderlyingSpace.map g p.2}
      fun z ↦ UnderlyingSpace.ext (by simp [prodMap, H.w]), ?_⟩
  convert isClosed_univ
  refine Set.eq_univ_of_forall fun ⟨p, hp⟩ ↦ ?_
  obtain ⟨z, rfl⟩ : p ∈ Set.range (prodMap (K := K) fst snd) :=
    range_prodMap_of_isPullback (K := K) H ▸ hp
  exact ⟨z, rfl⟩

/-- The map of underlying spaces induced by a separated morphism over `K` is a separated map:
the topological diagonal is the realized diagonal closed immersion, read through
`(X ×_Y X)(K) ≃ X(K) ×_{Y(K)} X(K)`. -/
private lemma isSeparatedMap_map {X Y : Scheme.{0}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsSeparated f] :
    IsSeparatedMap (UnderlyingSpace.map (K := K) f) := by
  letI : (Limits.pullback f f).Over (Spec (.of K)) :=
    ⟨Limits.pullback.fst f f ≫ X ↘ Spec (.of K)⟩
  haveI : (Limits.pullback.fst f f).IsOver (Spec (.of K)) := ⟨rfl⟩
  haveI : (Limits.pullback.snd f f).IsOver (Spec (.of K)) :=
    ⟨by rw [← comp_over f (Spec (.of K)), ← Category.assoc, ← Limits.pullback.condition,
      Category.assoc, comp_over f (Spec (.of K))]; rfl⟩
  haveI : (Limits.pullback.diagonal f).IsOver (Spec (.of K)) :=
    ⟨Limits.pullback.diagonal_fst_assoc f _⟩
  rw [isSeparatedMap_iff_isClosedEmbedding]
  convert (isClosedEmbedding_toPullback (K := K) (IsPullback.of_hasPullback f f)).comp
    (isClosedEmbedding_map_of_isClosedImmersion (K := K) (Limits.pullback.diagonal f))
  funext x
  exact Subtype.ext (Prod.ext (UnderlyingSpace.ext (by simp [prodMap]))
    (UnderlyingSpace.ext (by simp [prodMap])))

end Separated

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}

/-- The realized map `f^an : X^an → S^an` of a proper morphism `f : X ⟶ S` of schemes of finite
type over `ℂ` is separated and proper, i.e. continuous and universally closed. -/
@[mmp "thm_mmp_proper_realization"]
public theorem isSeparatedMap_and_isProperMap_realize
    [LocallyOfFiniteType sX] [QuasiCompact sX] [LocallyOfFiniteType sS] [QuasiCompact sS]
    (f : X ⟶ S) [IsProper f] (hf : f ≫ sS = sX) :
    IsSeparatedMap (realize f hf) ∧ IsProperMap (realize f hf) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : S.Over (Spec (.of ℂ)) := ⟨sS⟩
  have : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sS›
  have heq : realize f hf = homeomorphUnderlyingSpace.symm ∘
      UnderlyingSpace.map (K := ℂ) f ∘ homeomorphUnderlyingSpace := by
    funext x
    exact homeomorphUnderlyingSpace.eq_symm_apply.mpr (UnderlyingSpace.ext rfl)
  rw [heq]
  refine ⟨?_, ?_⟩
  · exact ((isSeparatedMap_map f).comp_right homeomorphUnderlyingSpace.continuous
      homeomorphUnderlyingSpace.injective).comp_left homeomorphUnderlyingSpace.symm.injective
  · exact homeomorphUnderlyingSpace.symm.isProperMap.comp
      ((isProperMap_map f).comp homeomorphUnderlyingSpace.isProperMap)

end MMP.Analytic.ComplexPoints

end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Analytic.ComplexPoints

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}

/-- The fibre of a continuous map over a point, with its inclusion and the map to the point,
is a cartesian square of topological spaces. -/
private lemma isPullback_fibre {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) :
    IsPullback (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of (f ⁻¹' {y}) ⟶ X)
      (TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩ :
        TopCat.of (f ⁻¹' {y}) ⟶ TopCat.of PUnit.{1})
      f (TopCat.ofHom ⟨fun _ => y, continuous_const⟩) :=
  ⟨⟨by ext x; exact x.2⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => TopCat.ofHom ⟨fun t => ⟨c.fst t, ConcreteCategory.congr_hom c.condition t⟩,
      c.fst.hom.continuous.subtype_mk _⟩)
    (fun c => by ext; rfl) (fun c => by ext)
    (fun c m h₁ _ => by ext t; exact congrArg (· t) (congrArg (fun φ => φ.hom.toFun) h₁))⟩⟩

/-- An exact functor `Φ` commutes with cohomology on bounded below derived categories:
`Φ(Hᵠ M) ≅ Hᵠ(RΦ M)`. -/
private noncomputable def homologyIsoOfExact {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (Φ : A ⥤ B) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (q : ℤ) (M : DerivedCategory.Plus A) :
    Φ.obj ((DerivedCategory.Plus.homologyFunctor A q).obj M) ≅
      (DerivedCategory.Plus.homologyFunctor B q).obj (Φ.rightDerivedFunctorPlus.obj M) :=
  ((Φ.mapDerivedCategoryHomologyIso q).app M.obj).symm ≪≫
    (DerivedCategory.homologyFunctor B q).mapIso (DerivedCategory.Plus.ι.mapIso
      ((Φ.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).app M).symm)

/-- **The stalk formula from base change to a point.** Let `g : ⋆ ⟶ Y` pick out `y` and let
`f' : X' ⟶ ⋆`. An isomorphism `g⁻¹ L ≅ Rf'_* N` in `D⁺(⋆)` identifies the stalk at `y` of
`Hᵠ L` with the hypercohomology `Hᵠ(X', N)`: the stalk at `y` is the stalk of `g⁻¹`, inverse
image and stalks commute with cohomology, and on `⋆` the stalk is the global sections, so that
global sections on `X'` are `f'_*` followed by the stalk at `⋆`. -/
private theorem nonempty_stalk_homology_iso {C : Type 1} [Category.{0} C] [HasColimits C]
    [HasLimits C] {FC : C → C → Type*} {CC : C → Type} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
    [PreservesLimits (CategoryTheory.forget C)] [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [Abelian C] [HasDerivedCategory C] {Y X' : TopCat.{0}} (y : Y)
    (f' : X' ⟶ TopCat.of PUnit.{1})
    [EnoughInjectives (TopCat.Sheaf C Y)] [EnoughInjectives (TopCat.Sheaf C X')]
    [EnoughInjectives (TopCat.Sheaf C (TopCat.of PUnit.{1}))]
    [(TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y, continuous_const⟩)).Additive]
    [PreservesFiniteLimits
      (TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y, continuous_const⟩))]
    [(TopCat.Sheaf.pushforward C f').Additive]
    [(TopCat.Sheaf.forget C X' ⋙ (evaluation _ C).obj (Opposite.op ⊤)).Additive]
    (L : DerivedCategory.Plus (TopCat.Sheaf C Y)) (N : DerivedCategory.Plus (TopCat.Sheaf C X'))
    (β : (TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y,
        continuous_const⟩)).rightDerivedFunctorPlus.obj L ≅
      (TopCat.Sheaf.pushforward C f').rightDerivedFunctorPlus.obj N) (q : ℤ) :
    Nonempty (((DerivedCategory.Plus.homologyFunctor _ q).obj L).presheaf.stalk y ≅
      (DerivedCategory.Plus.homologyFunctor C q).obj
        ((TopCat.Sheaf.forget C X' ⋙
          (evaluation _ C).obj (Opposite.op ⊤)).rightDerivedFunctorPlus.obj N)) := by
  let g : TopCat.of PUnit.{1} ⟶ Y := TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  let σ := TopCat.Sheaf.forget C (TopCat.of PUnit.{1}) ⋙
    TopCat.Presheaf.stalkFunctor C PUnit.unit
  let e : TopCat.Sheaf.pushforward C f' ⋙ σ ≅
      TopCat.Sheaf.forget C X' ⋙ (evaluation _ C).obj (Opposite.op ⊤) :=
    (NatIso.ofComponents (fun N => @asIso _ _ _ _ (TopCat.Presheaf.germ
        ((TopCat.Sheaf.pushforward C f').obj N).presheaf ⊤ PUnit.unit trivial)
        (Stacks.Topology.isIso_germ_of_subsingleton _ _ _ _)) (fun φ => by
      exact (TopCat.Presheaf.stalkFunctor_map_germ ⊤ PUnit.unit trivial
        ((TopCat.Sheaf.pushforward C f').map φ).hom).symm)).symm
  exact ⟨asIso (Stacks.Topology.ambientStalkHom g _ PUnit.unit) ≪≫
    σ.mapIso (homologyIsoOfExact (TopCat.Sheaf.pullback C g) q L ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso β) ≪≫
    homologyIsoOfExact σ q _ ≪≫ (DerivedCategory.Plus.homologyFunctor C q).mapIso
      (((Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ σ
        (fun _ _ => σ.rightAcyclic_of_exact _)).app N).symm ≪≫
      (Functor.rightDerivedFunctorPlusNatIso e).app N)⟩

/-- **Derived proper base change for complex schemes.** Let `f : X ⟶ S` be a proper morphism of
schemes of finite type over `ℂ`. For every cartesian square of topological spaces over the
realized map `analyticMap f hf : X^an ⟶ S^an`, the base change morphism
`g⁻¹ R(f^an)_* K ⟶ Rf'_* g'⁻¹ K` is an isomorphism for every bounded below complex `K` of
abelian sheaves on `X^an`, and for every bounded below complex `K` of sheaves of `R`-modules on
`X^an`, `R` any `ℚ`-algebra (for instance sheaves of `ℚ`-vector spaces). In both cases the stalk
at a point `s` of `S^an` of the `q`-th cohomology sheaf of `R(f^an)_* K` is the hypercohomology
`Hᵠ((f^an)⁻¹(s), K|_{(f^an)⁻¹(s)})` of the fibre with the restricted complex. -/
@[mmp "thm_mmp_complex_proper_base_change"]
public theorem isIso_baseChange_analyticMap_of_isProper
    [LocallyOfFiniteType sX] [QuasiCompact sX] [LocallyOfFiniteType sS] [QuasiCompact sS]
    (f : X ⟶ S) [IsProper f] (hf : f ≫ sS = sX)
    {X' Y' : TopCat.{0}} (f' : X' ⟶ Y') (g : Y' ⟶ analyticSpace sS)
    (g' : X' ⟶ analyticSpace sX) (hcart : IsPullback g' f' (analyticMap f hf) g) :
    (∀ K : DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{0} (analyticSpace sX)),
      IsIso ((Stacks.Cohomology.BaseChange.abelianBaseChange (analyticMap f hf) f' g g'
        hcart.w).app K)) ∧
    (∀ (R : Type) [Ring R] [Algebra ℚ R],
      letI : (TopCat.Sheaf.pushforward (ModuleCat.{0} R) (analyticMap f hf)).Additive :=
        (TopCat.Sheaf.pushforward (ModuleCat.{0} R)
          (analyticMap f hf)).additive_of_preserves_binary_products
      letI : (TopCat.Sheaf.pushforward (ModuleCat.{0} R) f').Additive :=
        (TopCat.Sheaf.pushforward (ModuleCat.{0} R) f').additive_of_preserves_binary_products
      letI : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{0} R) g) :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      letI : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{0} R) g') :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      letI : (TopCat.Sheaf.pullback (ModuleCat.{0} R) g).Additive :=
        Functor.additive_of_preservesBinaryBiproducts _
      letI : (TopCat.Sheaf.pullback (ModuleCat.{0} R) g').Additive :=
        Functor.additive_of_preservesBinaryBiproducts _
      letI : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} R) g) :=
        (fun {Y : TopCat.{0}} (k : Y' ⟶ Y) =>
          (by apply Functor.sheafPullbackConstruction.preservesFiniteLimits :
            PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} R) k))) g
      haveI : IsIso (TopCat.Sheaf.pullback (ModuleCat.{0} R) g).rightDerivedFunctorPlusUnith :=
        Stacks.Cohomology.BaseChange.exactUnit_isIso _
      ∀ K : DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} R) (analyticSpace sX)),
        IsIso ((Stacks.Cohomology.BaseChange.derived
          (TopCat.Sheaf.pushforward (ModuleCat.{0} R) (analyticMap f hf))
          (TopCat.Sheaf.pushforward (ModuleCat.{0} R) f')
          (TopCat.Sheaf.pullback (ModuleCat.{0} R) g)
          (TopCat.Sheaf.pullback (ModuleCat.{0} R) g')
          (Stacks.Cohomology.BaseChange.mate
            (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} R) g)
            (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} R) g')
            (TopCat.Sheaf.pushforward (ModuleCat.{0} R) (analyticMap f hf))
            (TopCat.Sheaf.pushforward (ModuleCat.{0} R) f')
            (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} R)) hcart.w)))
          (asIso (TopCat.Sheaf.pullback (ModuleCat.{0} R) g).rightDerivedFunctorPlusUnith)).app
            K)) ∧
    (∀ (K : DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{0} (analyticSpace sX)))
      (s : analyticSpace sS) (q : ℤ),
      letI : (TopCat.Sheaf.forget AddCommGrpCat.{0} (TopCat.of (analyticMap f hf ⁻¹' {s})) ⋙
          (evaluation _ AddCommGrpCat.{0}).obj (Opposite.op ⊤)).Additive := ⟨fun {_ _ _ _} => rfl⟩
      Nonempty (((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
            (analyticMap f hf)).rightDerivedFunctorPlus.obj K)).presheaf.stalk s ≅
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} q).obj
          ((TopCat.Sheaf.forget AddCommGrpCat.{0} (TopCat.of (analyticMap f hf ⁻¹' {s})) ⋙
            (evaluation _ AddCommGrpCat.{0}).obj (Opposite.op ⊤)).rightDerivedFunctorPlus.obj
              ((Stacks.Cohomology.BaseChange.abelianPullback (TopCat.ofHom
                ⟨Subtype.val, continuous_subtype_val⟩ :
                  TopCat.of (analyticMap f hf ⁻¹' {s}) ⟶ analyticSpace sX)).obj K)))) ∧
    ∀ (R : Type) [Ring R] [Algebra ℚ R]
      (K : DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} R) (analyticSpace sX)))
      (s : analyticSpace sS) (q : ℤ),
      letI : (TopCat.Sheaf.pushforward (ModuleCat.{0} R) (analyticMap f hf)).Additive :=
        (TopCat.Sheaf.pushforward (ModuleCat.{0} R)
          (analyticMap f hf)).additive_of_preserves_binary_products
      letI : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{0} R)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of (analyticMap f hf ⁻¹' {s}) ⟶ analyticSpace sX)) :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      letI : (TopCat.Sheaf.pullback (ModuleCat.{0} R)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of (analyticMap f hf ⁻¹' {s}) ⟶ analyticSpace sX)).Additive :=
        Functor.additive_of_preservesBinaryBiproducts _
      letI : (TopCat.Sheaf.forget (ModuleCat.{0} R) (TopCat.of (analyticMap f hf ⁻¹' {s})) ⋙
          (evaluation _ (ModuleCat.{0} R)).obj (Opposite.op ⊤)).Additive := ⟨fun {_ _ _ _} => rfl⟩
      Nonempty (((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((TopCat.Sheaf.pushforward (ModuleCat.{0} R)
            (analyticMap f hf)).rightDerivedFunctorPlus.obj K)).presheaf.stalk s ≅
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} R) q).obj
          ((TopCat.Sheaf.forget (ModuleCat.{0} R) (TopCat.of (analyticMap f hf ⁻¹' {s})) ⋙
            (evaluation _ (ModuleCat.{0} R)).obj (Opposite.op ⊤)).rightDerivedFunctorPlus.obj
              ((TopCat.Sheaf.pullback (ModuleCat.{0} R) (TopCat.ofHom
                ⟨Subtype.val, continuous_subtype_val⟩ :
                  TopCat.of (analyticMap f hf ⁻¹' {s}) ⟶
                    analyticSpace sX)).rightDerivedFunctorPlus.obj K))) := by
  have h := isSeparatedMap_and_isProperMap_realize f hf
  have hp : StacksDraft.Topology.IsProperMap (analyticMap f hf).hom :=
    ⟨h.1, h.2.isUniversallyClosedMap⟩
  refine ⟨(MMP.isIso_baseChange_of_isProperMap _ f' g g' hcart hp).1,
    (MMP.isIso_baseChange_of_isProperMap _ f' g g' hcart hp).2, fun K s q => ?_,
    fun R _ _ K s q => ?_⟩
  · have hA := (MMP.isIso_baseChange_of_isProperMap _ _ _ _
      (isPullback_fibre (analyticMap f hf) s) hp).1 K
    have : (TopCat.Sheaf.forget AddCommGrpCat.{0} (TopCat.of (analyticMap f hf ⁻¹' {s})) ⋙
        (evaluation _ AddCommGrpCat.{0}).obj (Opposite.op ⊤)).Additive := ⟨fun {_ _ _ _} => rfl⟩
    exact nonempty_stalk_homology_iso s _ _ _ (@asIso _ _ _ _ _ hA) q
  · let g₀ : TopCat.of PUnit.{1} ⟶ analyticSpace sS := TopCat.ofHom ⟨fun _ => s, continuous_const⟩
    let p : TopCat.of (analyticMap f hf ⁻¹' {s}) ⟶ TopCat.of PUnit.{1} :=
      TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
    have : (TopCat.Sheaf.pushforward (ModuleCat.{0} R) p).Additive :=
      (TopCat.Sheaf.pushforward (ModuleCat.{0} R) p).additive_of_preserves_binary_products
    have : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{0} R) g₀) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    have : (TopCat.Sheaf.pullback (ModuleCat.{0} R) g₀).Additive :=
      Functor.additive_of_preservesBinaryBiproducts _
    have : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} R) g₀) :=
      (fun {Z Y : TopCat.{0}} (k : Z ⟶ Y) =>
        (by apply Functor.sheafPullbackConstruction.preservesFiniteLimits :
          PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} R) k))) g₀
    have hR := (MMP.isIso_baseChange_of_isProperMap _ _ _ _
      (isPullback_fibre (analyticMap f hf) s) hp).2 R K
    have : (TopCat.Sheaf.forget (ModuleCat.{0} R) (TopCat.of (analyticMap f hf ⁻¹' {s})) ⋙
        (evaluation _ (ModuleCat.{0} R)).obj (Opposite.op ⊤)).Additive := ⟨fun {_ _ _ _} => rfl⟩
    exact nonempty_stalk_homology_iso s p _ _ (@asIso _ _ _ _ _ hR) q

end MMP.Analytic.ComplexPoints

end
