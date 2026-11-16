module

public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.Uniformisation
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Étale coordinates, the function model of `𝒪_{X^an}`, and boxes

Auxiliary results for the holomorphic logarithm of the family of degree-zero classes of a curve.
In étale coordinates algebraic and analytic derivatives agree; sections of `𝒪_{X^an}` are read as
holomorphic functions, and the exponential sequence becomes `exp (2πi ·)` on functions. Regular
functions on a reduced scheme of finite type over `ℂ` are determined by their values at
`ℂ`-points. The Picard class of a pulled-back invertible module is computed from local
generators, Čech `H¹` of a standard cover of an affine open vanishes, and regular functions on a
box `A × V` of affine opens are finite sums of products.

## Main results

* `MMP.JacobianLogarithm.Fam.eq_zero_of_forall_evalHom_eq_zero`: regular functions are determined
  by their values.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Filter Topology
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints

namespace MMP.JacobianLogarithm

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance] CategoryTheory.Hom.group

section FamilyLogarithm

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Filter Topology Limits
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff Interval
open KaehlerDifferential TensorProduct MeasureTheory Set intervalIntegral

namespace Fam

universe u

/-- If `G' = G k` on `[0, 1]` with `k` continuous, then `G 1 = G 0 · exp (∫₀¹ k)`. -/
theorem eq_mul_exp_integral_of_hasDerivAt {G k : ℝ → ℂ}
    (hG : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt G (G s * k s) s) (hk : Continuous k) :
    G 1 = G 0 * Complex.exp (∫ s in (0 : ℝ)..1, k s) := by
  let K : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, k s
  have hK : ∀ t, HasDerivAt K (k t) t := fun t =>
    (hk.integral_hasStrictDerivAt 0 t).hasDerivAt
  let Φ : ℝ → ℂ := fun s => G s * Complex.exp (-K s)
  have hΦ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt Φ 0 s := by
    intro s hs
    have h1 := (hG s hs).mul ((hK s).neg.cexp)
    have e : G s * k s * Complex.exp ((-K) s) + G s * (Complex.exp ((-K) s) * -k s) = 0 := by
      simp only [Pi.neg_apply]
      ring
    rwa [e] at h1
  have hconst : Φ 1 = Φ 0 := by
    have hd : DifferentiableOn ℝ Φ (Icc 0 1) := fun s hs =>
      (hΦ s hs).differentiableAt.differentiableWithinAt
    refine ((convex_Icc (0 : ℝ) 1).is_const_of_fderivWithin_eq_zero hd ?_
      (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one))
    intro s hs
    rw [((hΦ s hs).hasDerivWithinAt (s := Icc 0 1)).hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc zero_lt_one) s hs)]
    ext
    simp
  change G 1 * Complex.exp (-K 1) = G 0 * Complex.exp (-K 0) at hconst
  rw [show K 0 = 0 from integral_same, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- Two derivations of a formally unramified `S`-algebra that agree on the image of `S`
are equal. -/
theorem derivation_eq_of_formallyUnramified {R S T M : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyUnramified S T] [AddCommGroup M] [Module T M] [Module R M]
    [IsScalarTower R T M] (D₁ D₂ : Derivation R T M)
    (h : ∀ s : S, D₁ (algebraMap S T s) = D₂ (algebraMap S T s)) : D₁ = D₂ := by
  letI : Module S M := Module.compHom M (algebraMap S T)
  haveI : IsScalarTower S T M := ⟨fun s t m => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have hsub : Subsingleton Ω[T⁄S] := (Algebra.formallyUnramified_iff S T).mp inferInstance
  let D : Derivation S T M :=
    { toFun := fun t => D₁ t - D₂ t
      map_add' := fun a b => by simp only [map_add]; abel
      map_smul' := fun s t => by
        change D₁ (s • t) - D₂ (s • t) = s • (D₁ t - D₂ t)
        rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz, h s]
        change _ = algebraMap S T s • (D₁ t - D₂ t)
        rw [smul_sub]; abel
      map_one_eq_zero' := by
        change D₁ 1 - D₂ 1 = 0
        rw [Derivation.map_one_eq_zero, Derivation.map_one_eq_zero, sub_self]
      leibniz' := fun a b => by
        change D₁ (a * b) - D₂ (a * b) = a • (D₁ b - D₂ b) + b • (D₁ a - D₂ a)
        rw [Derivation.leibniz, Derivation.leibniz, smul_sub, smul_sub]; abel }
  have hD : D = 0 := by
    rw [← Derivation.liftKaehlerDifferential_comp D]
    ext t
    simp [Subsingleton.elim (KaehlerDifferential.D S T t) 0]
  ext t
  exact sub_eq_zero.mp (congrArg (fun E : Derivation S T M => E t) hD)

/-- **Derivations along étale coordinates.** If `T` is formally étale over `R[X₁, …, Xₙ]`, there
are `R`-derivations `D i` of `T` with `D i (Xⱼ) = δᵢⱼ`. -/
theorem exists_derivation_of_formallyEtale (R T : Type*) [CommRing R] [CommRing T] (ι : Type*)
    [DecidableEq ι] [Algebra R T] [Algebra (MvPolynomial ι R) T]
    [IsScalarTower R (MvPolynomial ι R) T]
    [Algebra.FormallyEtale (MvPolynomial ι R) T] :
    ∃ D : ι → Derivation R T T, ∀ i j,
      D i (algebraMap (MvPolynomial ι R) T (MvPolynomial.X j)) =
        if j = i then 1 else 0 := by
  classical
  let c : ι → (Ω[MvPolynomial ι R⁄R] →ₗ[MvPolynomial ι R]
      MvPolynomial ι R) := fun i => (mvPolynomialBasis R ι).coord i
  let ℓ : ι → (Ω[T⁄R] →ₗ[T] T) := fun i =>
    ((Algebra.TensorProduct.rid (MvPolynomial ι R) T T).toLinearMap.comp
      (((c i).baseChange T).restrictScalars T)).comp
        (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial ι R) T).symm.toLinearMap
  refine ⟨fun i => (ℓ i).compDer (KaehlerDifferential.D R T), fun i j => ?_⟩
  change ℓ i (KaehlerDifferential.D R T (algebraMap _ T (MvPolynomial.X j))) = _
  simp only [ℓ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearMap.coe_restrictScalars,
    LinearMap.baseChange_tmul, c, Module.Basis.coord_apply, mvPolynomialBasis_repr_D_X,
    AlgEquiv.toLinearMap_apply, Algebra.TensorProduct.rid_tmul, Finsupp.single_apply]
  split_ifs with h1 <;> simp

/-- **The ring map of étale coordinates is étale.** Converse of
`MMP.Flips.ResolutionInputs.etale_homOfVector_of_etale`. -/
theorem etale_eval₂Hom_of_etale_homOfVector {X S : Scheme.{u}} [IsAffine S] (h : X ⟶ S)
    (U : X.Opens) (hU : IsAffineOpen U) {ι : Type u} (w : ι → Γ(X, U))
    (het : Etale (AffineSpace.homOfVector (U.ι ≫ h) (fun i ↦ U.topIso.inv (w i)))) :
    (MvPolynomial.eval₂Hom (h.appLE ⊤ U le_top).hom w).Etale := by
  have : IsAffine U.toScheme := hU
  set π := AffineSpace.homOfVector (U.ι ≫ h) (fun i ↦ U.topIso.inv (w i))
  set φ := MvPolynomial.eval₂Hom (h.appLE ⊤ U le_top).hom w
  have H : Etale (π ≫ (AffineSpace.isoOfIsAffine ι S).hom) := inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.comp_appTop,
    AffineSpace.isoOfIsAffine_hom_appTop] at H
  have heq : (π.appTop.hom).comp (MvPolynomial.eval₂Hom ((AffineSpace ι S ↘ S).appTop).hom
      (AffineSpace.coord S)) = U.topIso.inv.hom.comp φ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := congrArg (fun g ↦ g.appTop.hom r) (AffineSpace.homOfVector_over (U.ι ≫ h)
        (fun i ↦ U.topIso.inv (w i)))
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, φ]
      have key : (U.ι ≫ h).appTop = h.appLE ⊤ U le_top ≫ U.topIso.inv := by
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
  have hφ : φ = (U.topIso.hom.hom.comp (((U.topIso.inv.hom.comp φ).comp
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι Γ(S, ⊤)))).hom.hom))).comp
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι Γ(S, ⊤)))).inv.hom := by
    have e1 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι Γ(S, ⊤)))).hom.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι Γ(S, ⊤)))).inv.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, Iso.inv_hom_id]; rfl
    have e2 : U.topIso.hom.hom.comp U.topIso.inv.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, Iso.inv_hom_id]; rfl
    rw [RingHom.comp_assoc, RingHom.comp_assoc, e1, RingHom.comp_id, ← RingHom.comp_assoc, e2,
      RingHom.id_comp]
  rw [hφ]
  refine RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)) ?_
  exact RingHom.Etale.stableUnderComposition _ _ H
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _))

/-- The derivations `∂/∂zᵢ` of the ring of an affine open `U` carrying étale coordinates `z`. -/
noncomputable def etaleDerivation {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} (U : X.Opens)
    (hU : IsAffineOpen U) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))) :
    Fin n → (Γ(X, U) →+ Γ(X, U)) := by
  classical
  let R := Γ(Spec (.of ℂ), ⊤)
  let ι := ULift.{0} (Fin n)
  let w : ι → Γ(X, U) := fun i => z i.down
  let ψ : MvPolynomial ι R →+* Γ(X, U) := MvPolynomial.eval₂Hom (sX.appLE ⊤ U le_top).hom w
  have hψ : ψ.Etale := etale_eval₂Hom_of_etale_homOfVector sX U hU w hz
  letI : Algebra R Γ(X, U) := (sX.appLE ⊤ U le_top).hom.toAlgebra
  letI : Algebra (MvPolynomial ι R) Γ(X, U) := ψ.toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (sX.appLE ⊤ U le_top).hom r = MvPolynomial.eval₂Hom _ w (MvPolynomial.C r)
      rw [MvPolynomial.eval₂Hom_C]
  haveI : Algebra.Etale (MvPolynomial ι R) Γ(X, U) := hψ
  exact fun i =>
    (Classical.choose (exists_derivation_of_formallyEtale R Γ(X, U) ι) ⟨i⟩).toAddMonoidHom

/-- **Algebraic and analytic derivatives agree in étale coordinates.** On an étale coordinate
chart with affine domain `U`, there are derivations `D i` of `Γ(U)` with `D i zⱼ = δᵢⱼ`, and for
every regular function `q` on `U` its analytic representative in the coordinates has partial
derivatives `D i q`. -/
theorem exists_derivation_etaleChart {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    [SmoothOfRelativeDimension n sX] (c : EtaleCoordinateChart sX n) (hU : IsAffineOpen c.U)
    (q : Γ(X, c.U)) :
      ∃ G : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ G c.toOpenPartialHomeomorph.target ∧
        (∀ (y : ComplexPoints sX) (hy : y ∈ c.W),
          eval c.U q ⟨y, c.subset hy⟩ = G (c.toOpenPartialHomeomorph y)) ∧
        ∀ (y : ComplexPoints sX) (hy : y ∈ c.W) (i : Fin n),
          fderiv ℂ G (c.toOpenPartialHomeomorph y) (Pi.single i 1) =
            eval c.U (etaleDerivation c.U hU c.z c.etale i q) ⟨y, c.subset hy⟩ := by
  classical
  set φ := c.toOpenPartialHomeomorph with hφdef
  have hsrc : φ.source = c.W := c.source_toOpenPartialHomeomorph
  let R := Γ(Spec (.of ℂ), ⊤)
  let ι := ULift.{0} (Fin n)
  let w : ι → Γ(X, c.U) := fun i => c.z i.down
  let ψ : MvPolynomial ι R →+* Γ(X, c.U) := MvPolynomial.eval₂Hom (sX.appLE ⊤ c.U le_top).hom w
  have hψ : ψ.Etale := etale_eval₂Hom_of_etale_homOfVector sX c.U hU w c.etale
  letI : Algebra R Γ(X, c.U) := (sX.appLE ⊤ c.U le_top).hom.toAlgebra
  letI : Algebra (MvPolynomial ι R) Γ(X, c.U) := ψ.toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) Γ(X, c.U) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (sX.appLE ⊤ c.U le_top).hom r = MvPolynomial.eval₂Hom _ w (MvPolynomial.C r)
      rw [MvPolynomial.eval₂Hom_C]
  haveI : Algebra.Etale (MvPolynomial ι R) Γ(X, c.U) := hψ
  let D' := Classical.choose (exists_derivation_of_formallyEtale R Γ(X, c.U) ι)
  have hD' := Classical.choose_spec (exists_derivation_of_formallyEtale R Γ(X, c.U) ι)
  have hrep : ∀ q : Γ(X, c.U), ∃ G : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ G φ.target ∧
      ∀ (y : ComplexPoints sX) (hy : y ∈ c.W), eval c.U q ⟨y, c.subset hy⟩ = G (φ y) := by
    intro q
    obtain ⟨G, hG, hGe⟩ := c.exists_analyticOnNhd c.U q
    refine ⟨G, fun v hv => hG v ⟨hv, ?_⟩, fun y hy => hGe y hy (c.subset hy)⟩
    exact c.subset (hsrc ▸ φ.map_target hv)
  choose Gf hGf hGfe using hrep
  have hGt : ∀ (q : Γ(X, c.U)) (v : Fin n → ℂ) (hv : v ∈ φ.target),
      Gf q v = eval c.U q ⟨φ.symm v, c.subset (hsrc ▸ φ.map_target hv)⟩ := by
    intro q v hv
    rw [hGfe q _ (hsrc ▸ φ.map_target hv), φ.right_inv hv]
  refine ⟨Gf q, hGf q, hGfe q, fun y hy i => ?_⟩
  set p := φ y with hpdef
  have hp : p ∈ φ.target := φ.map_source (hsrc.symm ▸ hy)
  have htn : φ.target ∈ 𝓝 p := φ.open_target.mem_nhds hp
  have hdiff : ∀ q, DifferentiableAt ℂ (Gf q) p := fun q => (hGf q p hp).differentiableAt
  have hval : ∀ q, Gf q p = eval c.U q ⟨y, c.subset hy⟩ := fun q => (hGfe q y hy).symm
  have hGadd : ∀ a b, Gf (a + b) =ᶠ[𝓝 p] Gf a + Gf b := fun a b =>
    Filter.eventually_of_mem htn fun v hv => by
      rw [Pi.add_apply, hGt _ v hv, hGt _ v hv, hGt _ v hv]
      exact map_add (evalHom c.U _) a b
  have hGmul : ∀ a b, Gf (a * b) =ᶠ[𝓝 p] Gf a * Gf b := fun a b =>
    Filter.eventually_of_mem htn fun v hv => by
      rw [Pi.mul_apply, hGt _ v hv, hGt _ v hv, hGt _ v hv]
      exact map_mul (evalHom c.U _) a b
  have hconst : ∀ (y' : chart (sX := sX) c.U) (r : R),
      eval c.U (algebraMap R Γ(X, c.U) r) y' = (Scheme.ΓSpecIso (.of ℂ)).hom r := by
    intro y' r
    change (Scheme.ΓSpecIso (.of ℂ)).hom ((sX.appLE ⊤ c.U le_top ≫
      y'.1.hom.appLE c.U ⊤ y'.2.ge) r) = _
    have e : sX.appLE ⊤ c.U le_top ≫ y'.1.hom.appLE c.U ⊤ y'.2.ge = 𝟙 _ := by
      rw [Scheme.Hom.appLE]
      exact appTop_map_appLE c.U y'
    rw [e]
    rfl
  have hGalg : ∀ r : R, Gf (algebraMap R Γ(X, c.U) r) =ᶠ[𝓝 p]
      fun _ => (Scheme.ΓSpecIso (.of ℂ)).hom r := fun r =>
    Filter.eventually_of_mem htn fun v hv => by
      rw [hGt _ v hv, hconst]
  letI : Algebra Γ(X, c.U) ℂ := (evalHom c.U ⟨y, c.subset hy⟩).toAlgebra
  letI : Algebra R ℂ := ((evalHom c.U ⟨y, c.subset hy⟩).comp (algebraMap R Γ(X, c.U))).toAlgebra
  haveI : IsScalarTower R Γ(X, c.U) ℂ := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hRalg : ∀ r : R, algebraMap R ℂ r = (Scheme.ΓSpecIso (.of ℂ)).hom r := fun r =>
    hconst ⟨y, c.subset hy⟩ r
  let δ : Derivation R Γ(X, c.U) ℂ :=
    { toFun := fun a => fderiv ℂ (Gf a) p (Pi.single i 1)
      map_add' := fun a b => by
        change fderiv ℂ (Gf (a + b)) p _ = fderiv ℂ (Gf a) p _ + fderiv ℂ (Gf b) p _
        rw [(hGadd a b).fderiv_eq, fderiv_add (hdiff a) (hdiff b)]; rfl
      map_smul' := fun r a => by
        change fderiv ℂ (Gf (r • a)) p _ = r • fderiv ℂ (Gf a) p _
        have h1 : Gf (r • a) =ᶠ[𝓝 p] fun v => (Scheme.ΓSpecIso (.of ℂ)).hom r * Gf a v :=
          ((hGmul _ a).trans ((hGalg r).mul (EventuallyEq.refl _ _))).mono fun v hv => by
            rw [Algebra.smul_def]; exact hv
        rw [h1.fderiv_eq, fderiv_const_mul (hdiff a), Algebra.smul_def, hRalg]; rfl
      map_one_eq_zero' := by
        change fderiv ℂ (Gf 1) p _ = 0
        have h1 : Gf 1 =ᶠ[𝓝 p] fun _ => (Scheme.ΓSpecIso (.of ℂ)).hom 1 := by
          have := hGalg 1
          rwa [map_one] at this
        rw [h1.fderiv_eq, fderiv_const_apply]; rfl
      leibniz' := fun a b => by
        change fderiv ℂ (Gf (a * b)) p _ = a • fderiv ℂ (Gf b) p _ + b • fderiv ℂ (Gf a) p _
        rw [(hGmul a b).fderiv_eq, fderiv_mul (hdiff a) (hdiff b), Algebra.smul_def,
          Algebra.smul_def]
        change Gf a p * _ + Gf b p * _ = _
        rw [hval a, hval b]; rfl }
  let D₂ : Derivation R Γ(X, c.U) ℂ := (Algebra.linearMap Γ(X, c.U) ℂ).compDer (D' ⟨i⟩)
  have hw : ∀ j : ι, w j = algebraMap (MvPolynomial ι R) Γ(X, c.U) (MvPolynomial.X j) :=
    fun j => by
      change c.z j.down = MvPolynomial.eval₂Hom _ w (MvPolynomial.X j)
      rw [MvPolynomial.eval₂Hom_X']
  have hbase : ∀ j : ι, δ (w j) = D₂ (w j) := by
    intro j
    have h1 : Gf (w j) =ᶠ[𝓝 p] fun v => v j.down :=
      Filter.eventually_of_mem htn fun v hv => by
        rw [hGt _ v hv]
        have := c.toOpenPartialHomeomorph_apply (hsrc ▸ φ.map_target hv) j.down
        rw [φ.right_inv hv] at this
        exact this.symm
    change fderiv ℂ (Gf (w j)) p _ = algebraMap Γ(X, c.U) ℂ (D' ⟨i⟩ (w j))
    rw [h1.fderiv_eq, hw j, hD']
    have hproj : HasFDerivAt (fun v : Fin n → ℂ => v j.down)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j.down) p :=
      hasFDerivAt_apply j.down p
    rw [hproj.fderiv]
    change (Pi.single i (1 : ℂ) : Fin n → ℂ) j.down = algebraMap Γ(X, c.U) ℂ _
    by_cases hji : j = ⟨i⟩
    · subst hji
      simp
    · have : j.down ≠ i := fun h => hji (ULift.ext h)
      simp [hji, this]
  have hagree : ∀ s : MvPolynomial ι R,
      δ (algebraMap (MvPolynomial ι R) Γ(X, c.U) s) =
        D₂ (algebraMap (MvPolynomial ι R) Γ(X, c.U) s) := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C r =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        Derivation.map_algebraMap, Derivation.map_algebraMap]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | mul_X a j ha =>
      rw [map_mul, Derivation.leibniz, Derivation.leibniz, ha, ← hw j, hbase j]
  exact congrArg (fun E : Derivation R Γ(X, c.U) ℂ => E q)
    (derivation_eq_of_formallyUnramified δ D₂ hagree)

section Theta

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
  [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]

/-- The constant section `a` of `𝒪_{X^an}` over `W`. -/
noncomputable def constSection (W : Opens (space sX)) (a : ℂ) :
    (structureSheaf sX).obj.obj (op W) :=
  (structureSheaf sX).obj.map (homOfLE (le_top : W ≤ ⊤)).op
    ((ringCatSheafHom sX).hom.app (op ⊤) (ComplexPoints.baseRingHom sX ⊤ a))

/-- The value of the constant section `a` at a point, read in a chart stalk, is `a`. -/
theorem stalkEval_constSection (W : Opens (space sX)) (a : ℂ) (x : W)
    (c : Chart sX) (hc : x.1 ∈ chart c.U) :
    stalkEval c ⟨x.1, hc⟩ ((constSection W a).1 x ⟨c, hc⟩) = a :=
  stalkEval_const a ⟨x.1, trivial⟩ ⟨c, hc⟩

/-- If `Θ` is compatible with evaluation of regular functions, it sends the constant section `a`
to the constant function `a`. -/
theorem theta_constSection (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
    (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (W : Opens (space sX)) (a : ℂ) (x : W) :
    Θ.hom.hom.app (op W) (constSection W a) x = a := by
  let z := (ringCatSheafHom sX).hom.app (op ⊤) (ComplexPoints.baseRingHom sX ⊤ a)
  have h : Θ.hom.hom.app (op W) ((structureSheaf sX).obj.map (homOfLE (le_top : W ≤ ⊤)).op z) =
      (𝒪[n, ComplexPoints sX]).obj.map (homOfLE (le_top : W ≤ ⊤)).op (Θ.hom.hom.app (op ⊤) z) := by
    change ((structureSheaf sX).obj.map _ ≫ Θ.hom.hom.app (op W)) z = _
    erw [Θ.hom.hom.naturality]
    rfl
  change (Θ.hom.hom.app (op W) ((structureSheaf sX).obj.map (homOfLE le_top).op z)) x = a
  rw [h]
  change Θ.hom.hom.app (op ⊤) ((analytificationHom sX).hom.c.app (op ⊤)
    (ComplexPoints.baseRingHom sX ⊤ a)) ⟨x.1, trivial⟩ = a
  exact (hΘ ⊤ _ ⟨x.1, trivial⟩).trans (evalHom_baseRingHom _ _ a)

/-- Applying `Θ.hom` and then `Θ.inv` to a section over `W` returns it. -/
theorem theta_hom_inv_apply (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
    (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) :
    Θ.inv.hom.app (op W) (Θ.hom.hom.app (op W) s) = s := by
  have h : Θ.hom.hom.app (op W) ≫ Θ.inv.hom.app (op W) = 𝟙 _ :=
    congrArg (fun φ => φ.hom.app (op W)) Θ.hom_inv_id
  simpa using ConcreteCategory.congr_hom h s

/-- Applying `Θ.inv` and then `Θ.hom` to a function over `W` returns it. -/
theorem theta_inv_hom_apply (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
    (W : Opens (space sX)) (s : (𝒪[n, ComplexPoints sX]).obj.obj (op W)) :
    Θ.hom.hom.app (op W) (Θ.inv.hom.app (op W) s) = s := by
  have h : Θ.inv.hom.app (op W) ≫ Θ.hom.hom.app (op W) = 𝟙 _ :=
    congrArg (fun φ => φ.hom.app (op W)) Θ.inv_hom_id
  simpa using ConcreteCategory.congr_hom h s

/-- The function `Θ` attaches to the restriction of a section to `W' ≤ W` is the restriction of
the function attached to the section. -/
theorem theta_res (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
    {W W' : Opens (space sX)} (h : W' ≤ W) (s : (structureSheaf sX).obj.obj (op W)) (x : W') :
    Θ.hom.hom.app (op W') ((structureSheaf sX).obj.map (homOfLE h).op s) x =
      Θ.hom.hom.app (op W) s ⟨x.1, h x.2⟩ := by
  have e : Θ.hom.hom.app (op W') ((structureSheaf sX).obj.map (homOfLE h).op s) =
      (𝒪[n, ComplexPoints sX]).obj.map (homOfLE h).op (Θ.hom.hom.app (op W) s) := by
    change ((structureSheaf sX).obj.map _ ≫ Θ.hom.hom.app (op W')) s = _
    erw [Θ.hom.hom.naturality]
    rfl
  rw [e]
  rfl

/-- **Sections of `𝒪_{X^an}` read as holomorphic functions take their values.** Under an
isomorphism `Θ` of `𝒪_{X^an}` with the sheaf of holomorphic functions that is the evaluation on
regular functions, every section is sent to the function of its values. -/
theorem theta_apply_eq_stalkEval (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
    (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
    (c : Chart sX) (hc : x.1 ∈ chart c.U) :
    Θ.hom.hom.app (op W) s x = stalkEval c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩) := by
  set a := stalkEval c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩) with ha
  set t := s - constSection W a with ht
  have ht0 : stalkEval c ⟨x.1, hc⟩ (t.1 x ⟨c, hc⟩) = 0 := by
    change stalkEval c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩ - (constSection W a).1 x ⟨c, hc⟩) = 0
    rw [map_sub, stalkEval_constSection, ← ha, sub_self]
  have key : Θ.hom.hom.app (op W) t x = 0 := by
    by_contra hne
    set F := Θ.hom.hom.app (op W) t with hF
    have hFs : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, ℂ) ∞ (fun z : W => F z) :=
      smoothSheaf.contMDiff_section (IM := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (I := 𝓘(ℂ, ℂ))
        (M := ComplexPoints sX) (N := ℂ) (U := op W) F
    have hFc : Continuous (fun z : W => F z) := hFs.continuous
    let W' : Opens (space sX) := ⟨Subtype.val '' {z : W | F z ≠ 0},
      W.2.isOpenEmbedding_subtypeVal.isOpenMap _ (isOpen_ne_fun hFc continuous_const)⟩
    have hW'W : W' ≤ W := by
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    have hx' : x.1 ∈ W' := ⟨x, hne, rfl⟩
    have hFne : ∀ z : W', F ⟨z.1, hW'W z.2⟩ ≠ 0 := by
      rintro ⟨_, ⟨z, hz, rfl⟩⟩
      exact hz
    let G : (𝒪[n, ComplexPoints sX]).obj.obj (op W') :=
      ⟨fun z => (F ⟨z.1, hW'W z.2⟩)⁻¹, (hFs.comp (contMDiff_inclusion hW'W)).inv₀ hFne⟩
    have hmul : (structureSheaf sX).obj.map (homOfLE hW'W).op t *
        Θ.inv.hom.app (op W') G = 1 := by
      have hinj : Function.Injective (Θ.hom.hom.app (op W')) := fun p q hpq => by
        rw [← theta_hom_inv_apply Θ W' p, ← theta_hom_inv_apply Θ W' q, hpq]
      apply hinj
      rw [map_mul, map_one, theta_inv_hom_apply]
      refine Subtype.ext (funext fun z => ?_)
      change Θ.hom.hom.app (op W') ((structureSheaf sX).obj.map (homOfLE hW'W).op t) z *
        (F ⟨z.1, hW'W z.2⟩)⁻¹ = 1
      rw [theta_res]
      exact mul_inv_cancel₀ (hFne z)
    have := congrArg (fun r : (structureSheaf sX).obj.obj (op W') =>
      stalkEval c ⟨x.1, hc⟩ (r.1 ⟨x.1, hx'⟩ ⟨c, hc⟩)) hmul
    simp only at this
    change stalkEval c ⟨x.1, hc⟩ (t.1 x ⟨c, hc⟩ * _) = stalkEval c ⟨x.1, hc⟩ 1 at this
    rw [map_mul, ht0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hs : s = t + constSection W a := by rw [ht, sub_add_cancel]
  rw [hs, map_add]
  change Θ.hom.hom.app (op W) t x + Θ.hom.hom.app (op W) (constSection W a) x = a
  rw [key, theta_constSection Θ hΘ, zero_add]

/-- **The exponential sequence in the function model.** If `e : 𝒪 ⟶ 𝒪^×` is `exp (2πi ·)` on
germs, then under `Θ` it is `exp (2πi ·)` on functions. -/
theorem theta_exp [LocallyOfFiniteType sX] (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
    (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (e : (sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
        (ringCatSheaf sX) ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (he : ∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
        (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
          (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ')
    (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W) :
    Θ.hom.hom.app (op W) ((Additive.toMul (e.hom.app (op W) s) :
        ((structureSheaf sX).obj.obj (op W))ˣ) : (structureSheaf sX).obj.obj (op W)) x =
      Complex.exp (2 * Real.pi * Complex.I * Θ.hom.hom.app (op W) s x) := by
  obtain ⟨c, hc⟩ := exists_chart_mem x.1
  obtain ⟨O, -, hxO, h, hh⟩ := s.2.1 c x hc
  obtain ⟨hyW, gs, hgs, hsg⟩ := hh ⟨x.1, hc⟩ hxO
  obtain ⟨f₀, hf₀, hf₀d⟩ : ∃ f : (Fin c.n → ℂ) → ℂ, (f : Germ (𝓝 (c.coords ⟨x.1, hc⟩)) ℂ) =
      (gs : Germ (𝓝 (c.coords ⟨x.1, hc⟩)) ℂ) ∧
      ∀ᶠ y in 𝓝 (c.coords ⟨x.1, hc⟩), DifferentiableAt ℂ f y := gs.2
  have hfh : (f₀ : Germ (𝓝 (c.coords ⟨x.1, hc⟩)) ℂ) = h := hf₀.trans hgs
  have hhd : ∀ᶠ y in 𝓝 (c.coords ⟨x.1, hc⟩), DifferentiableAt ℂ h y := by
    have h1 : ∀ᶠ y in 𝓝 (c.coords ⟨x.1, hc⟩), ∀ᶠ z in 𝓝 y, f₀ z = h z :=
      (Germ.coe_eq.1 hfh).eventually_nhds
    filter_upwards [h1, hf₀d] with y hy hdy
    exact hdy.congr_of_eventuallyEq (hy.mono fun z hz => hz.symm)
  let γ' : holGerms (c.coords ⟨x.1, hc⟩) :=
    ⟨((fun z => Complex.exp (2 * Real.pi * Complex.I * h z)) :
      Germ (𝓝 (c.coords ⟨x.1, hc⟩)) ℂ), _, rfl, hhd.mono fun y hy =>
        ((hy.const_mul _).cexp)⟩
  have hes := he W s x ⟨c, hc⟩ h gs γ' hgs rfl hsg
  rw [theta_apply_eq_stalkEval Θ hΘ W _ x c hc, theta_apply_eq_stalkEval Θ hΘ W s x c hc,
    hes, hsg, stalkEval_mk, stalkEval_mk]
  change Germ.value (((fun z => Complex.exp (2 * Real.pi * Complex.I * h z)) :
      Germ (𝓝 (c.coords ⟨x.1, hc⟩)) ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * Germ.value (gs : Germ (𝓝 (c.coords ⟨x.1, hc⟩)) ℂ))
  rw [hgs, Germ.value_ofFun, Germ.value_ofFun]

end Theta

/-- `sheafCohomologyOneExtEquiv` is the component of the composite of its two defining natural
isomorphisms. -/
theorem sheafCohomologyOneExtEquiv_hom_apply (Y : TopCat.{0})
    (H : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (x : Stacks.Cohomology.SheafTorsor.sheafCohomologyOne Y H) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv Y H).hom x =
      (ModuleSheafCohomology.rightDerivedIso (Stacks.Thickenings.sectionsCoyonedaIso Y).symm 1 ≪≫
        ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
          ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
            (AddCommGrpCat.of (ULift.{0} ℤ))) 0).hom.app H x := by
  rw [Stacks.Thickenings.sheafCohomologyOneExtEquiv]
  rfl

/-- `sheafCohomologyOneExtEquiv` is natural in the sheaf. -/
theorem sheafCohomologyOneExtEquiv_naturality (Y : TopCat.{0})
    {F G : TopCat.Sheaf AddCommGrpCat.{0} Y} (g : F ⟶ G)
    (z : Stacks.Cohomology.SheafTorsor.sheafCohomologyOne Y F) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv Y G).hom
        ((((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
          (op (⊤ : Opens Y))).rightDerived 1).map g z) =
      Sheaf.H.map g 1 ((Stacks.Thickenings.sheafCohomologyOneExtEquiv Y F).hom z) := by
  have key := (ModuleSheafCohomology.rightDerivedIso
    (Stacks.Thickenings.sectionsCoyonedaIso Y).symm 1 ≪≫
      ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift.{0} ℤ))) 0).hom.naturality g
  refine (sheafCohomologyOneExtEquiv_hom_apply Y G _).trans ?_
  refine (ConcreteCategory.congr_hom key z).trans ?_
  exact (congrArg (fun y => Sheaf.H.map g 1 y) (sheafCohomologyOneExtEquiv_hom_apply Y F z)).symm

/-- **Regular functions on a reduced scheme of finite type over `ℂ` are determined by their
values.** A section over an affine open vanishing at every `ℂ`-point is zero: it lies in every
maximal ideal, since closed points are `ℂ`-points, hence in the Jacobson radical, which is the
nilradical. -/
theorem eq_zero_of_forall_evalHom_eq_zero {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsReduced X] {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U)) (ha : ∀ y : chart (sX := sX) U, evalHom U y a = 0) : a = 0 := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨c, hc⟩ := Chart.exists_eq (sX := sX) hU
  haveI : IsJacobsonRing Γ(X, U) := by
    subst hc
    exact isJacobsonRing_of_surjective ⟨c.pres, c.surjective⟩
  have hmem : ∀ m : Ideal Γ(X, U), m.IsMaximal → a ∈ m := by
    intro m hm
    let P : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
    set p := hU.fromSpec P with hpdef
    have hpU : p ∈ U := by
      have : p ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
      rwa [hU.range_fromSpec] at this
    have hcl : IsClosed ({p} : Set X) := by
      refine isClosed_singleton_of_isLocallyClosed_singleton ?_
      have hPcl : IsClosed ({P} : Set (Spec Γ(X, U))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 hm
      rw [show ({p} : Set X) = hU.fromSpec '' ({P} : Set (Spec Γ(X, U))) from
        (Set.image_singleton (f := hU.fromSpec) (a := P)).symm]
      exact hPcl.isLocallyClosed.image hU.fromSpec.isOpenEmbedding.isInducing
        hU.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
    obtain ⟨y, hy⟩ : p ∈ Set.range (ComplexPoints.toScheme (sX := sX)) := by
      rwa [(analytification_stalks sX).1.2.2.1]
    have hyU : y ∈ chart (sX := sX) U := mem_chart_iff.2 (hy ▸ hpU)
    have h0 := ha ⟨y, hyU⟩
    by_contra hna
    refine evalHom_ne_zero_of_notMem hU ⟨y, hyU⟩ a ?_ h0
    have hP : hU.primeIdealOf ⟨y.toScheme, mem_chart_iff.1 hyU⟩ = P :=
      hU.fromSpec.isOpenEmbedding.injective (by rwa [hU.fromSpec_primeIdealOf])
    rwa [hP]
  have hjac : a ∈ (⊥ : Ideal Γ(X, U)).jacobson :=
    Ideal.mem_sInf.2 fun m hm => hmem m hm.2
  rwa [IsJacobsonRing.out' (⊥ : Ideal Γ(X, U)) Ideal.isRadical_bot] at hjac

/-- Every element of a pushout `S'` of commutative rings along `S ← R → R'` is a finite sum of
products `inl a * inr b` with `a ∈ S` and `b ∈ R'`. -/
theorem exists_sum_mul_of_isPushout {R S R' S' : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ R'}
    {inl : S ⟶ S'} {inr : R' ⟶ S'} (h : IsPushout f g inl inr) (x : S') :
    ∃ (n : ℕ) (a : Fin n → S) (b : Fin n → R'), x = ∑ l, inl (a l) * inr (b l) := by
  letI : Algebra R S := f.hom.toAlgebra
  letI : Algebra R R' := g.hom.toAlgebra
  letI : Algebra S S' := inl.hom.toAlgebra
  letI : Algebra R' S' := inr.hom.toAlgebra
  letI : Algebra R S' := (f ≫ inl).hom.toAlgebra
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => by
    change (f ≫ inl).hom r = inr (g r)
    rw [h.w]; rfl
  have h' : Algebra.IsPushout R S R' S' := by rwa [← CommRingCat.isPushout_iff_isPushout]
  obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv R S R' S').surjective x
  obtain ⟨T, rfl⟩ := TensorProduct.exists_finset t
  refine ⟨T.card, fun l => (T.equivFin.symm l).1.1, fun l => (T.equivFin.symm l).1.2, ?_⟩
  rw [map_sum]
  simp only [Algebra.IsPushout.equiv_tmul]
  rw [← Finset.sum_coe_sort T]
  exact (Fintype.sum_equiv T.equivFin _ _ fun i => by simp; rfl).trans rfl

section L1

open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
open IsLocalRing (maximalIdeal)

variable {X Y : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  [∀ y : Y.carrier, IsLocalRing (ringStalk Y y)]

/-- For `ψ` with local stalk maps and `s` a generator of the invertible module `L` on `U`, the
germ at `x ∈ ψ⁻¹ U` of the pullback of `s` to `ψ^* L` does not lie in `𝔪ₓ · (ψ^* L)ₓ`. -/
theorem notMem_maximalIdeal_smul_top_pullbackUnit' (ψ : X ⟶ Y)
    (hψ : ∀ x, IsLocalHom (ψ.hom.stalkMap x).hom)
    (L : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y).property L)
    (U : Opens Y.carrier) (s : Stacks.SheafOfModules.GeneratorSections Y L U)
    (x : X.carrier) (hx : x ∈ (opensMap ψ).obj U) :
    grpGerm X ((Stacks.RingedSpace.pullbackFunctor ψ).obj L).val x ((opensMap ψ).obj U) hx
        (Stacks.RingedSpace.pullbackUnit ψ L (op U) s.val) ∉
      maximalIdeal (ringStalk X x) •
        (⊤ : Submodule (ringStalk X x)
          (grpStalk X ((Stacks.RingedSpace.pullbackFunctor ψ).obj L).val x)) := by
  have hxU : ψ.hom.base x ∈ U := hx
  let _ : Algebra (ringStalk Y (ψ.hom.base x)) (ringStalk X x) :=
    (ψ.hom.stalkMap x).hom.toAlgebra
  have _hlocal : IsLocalHom (algebraMap (ringStalk Y (ψ.hom.base x))
      (ringStalk X x)) := hψ x
  obtain ⟨e, he⟩ := Stacks.RingedSpace.pullbackStalkFormula ψ L x
  have := hL
  have hs := Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_generator L s (ψ.hom.base x) hxU
  intro hmem
  refine hs ?_
  refine (Stacks.SheafOfModules.mem_maximalIdeal_smul_iff_tmul
    (A := ringStalk Y (ψ.hom.base x)) (B := ringStalk X x)
    (M := grpStalk Y L.val (ψ.hom.base x))
    (grpGerm Y L.val (ψ.hom.base x) U hxU s.val)).mpr ?_
  refine Eq.mp (congrArg (fun y => y ∈ maximalIdeal (ringStalk X x) •
    (⊤ : Submodule (ringStalk X x) _)) (he U hxU s.val)) ?_
  exact (Stacks.SheafOfModules.mem_ideal_smul_top_iff_of_linearEquiv
    (maximalIdeal (ringStalk X x)) e _).mp hmem

/-- The pullback of a generator along a morphism of ringed spaces with local stalk maps. -/
noncomputable def pullbackGenerator' (ψ : X ⟶ Y)
    (hψ : ∀ x, IsLocalHom (ψ.hom.stalkMap x).hom)
    (L : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y).property L)
    (U : Opens Y.carrier) (s : Stacks.SheafOfModules.GeneratorSections Y L U) :
    Stacks.SheafOfModules.GeneratorSections X ((modulePullback ψ).obj L) ((opensMap ψ).obj U) := by
  classical
  refine ⟨Stacks.RingedSpace.pullbackUnit ψ L (op U) s.val, ?_⟩
  have hYinv : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (structureSheafRing Y).property L := hL
  have hinv : Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property
      ((modulePullback ψ).obj L) :=
    Stacks.RingedSpace.isInvertible_modulePullback ψ L
  choose W hxW hWU hbij using fun z : ((opensMap ψ).obj U : Opens X.carrier) =>
    Stacks.SheafOfModules.exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top
      ((modulePullback ψ).obj L)
      (Stacks.RingedSpace.pullbackUnit ψ L (op U) s.val) z.val z.property
      (notMem_maximalIdeal_smul_top_pullbackUnit' ψ hψ L hL U s z.val z.property)
  exact fun V hV => Stacks.SheafOfModules.bijective_smul_of_bijective_on_cover
    ((modulePullback ψ).obj L) _ W hWU
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hxW ⟨z, hz⟩⟩) hbij V hV

/-- The unit relating the pullbacks of two generators `s` and `t` of `L` on `U` is the image under
`ψ` of the unit relating `s` and `t`. -/
theorem generatorRatioUnit_pullbackGenerator' (ψ : X ⟶ Y)
    (hψ : ∀ x, IsLocalHom (ψ.hom.stalkMap x).hom)
    (L : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y).property L)
    (U : Opens Y.carrier) (s t : Stacks.SheafOfModules.GeneratorSections Y L U) :
    Stacks.SheafOfModules.generatorRatioUnit ((modulePullback ψ).obj L) ((opensMap ψ).obj U)
        (pullbackGenerator' ψ hψ L hL U s) (pullbackGenerator' ψ hψ L hL U t) =
      Units.map (ψ.hom.c.app (op U)).hom.toMonoidHom
        (Stacks.SheafOfModules.generatorRatioUnit L U s t) := by
  refine Stacks.SheafOfModules.generatorRatioUnit_eq _ _ _ _ _ ?_
  change Stacks.RingedSpace.pullbackUnit ψ L (op U) t.val = _
  rw [Stacks.SheafOfModules.generatorRatio_spec L U s t]
  exact Stacks.RingedSpace.pullbackUnit_smul ψ L (op U)
    (Stacks.SheafOfModules.generatorRatio L U s t) s.val

end L1

section Transition

open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{0, 0}}
  [∀ x : X, IsLocalRing (X.presheaf.stalk x)] [∀ y : Y, IsLocalRing (Y.presheaf.stalk y)]

omit [∀ x : X, IsLocalRing (X.presheaf.stalk x)] in
/-- Restricting a restricted section further only depends on the smallest open. -/
theorem restrictₛₗ_restrict_eq {L : _root_.SheafOfModules.{0} (structureSheafRing X)}
    {U V₁ V₂ W : Opens X} (h₁ : V₁ ≤ U) (h₂ : V₂ ≤ U) (k₁ : W ≤ V₁) (k₂ : W ≤ V₂)
    (m : L.val.obj (op U)) :
    L.val.restrictₛₗ (homOfLE k₁).op (L.val.restrictₛₗ (homOfLE h₁).op m) =
      L.val.restrictₛₗ (homOfLE k₂).op (L.val.restrictₛₗ (homOfLE h₂).op m) := by
  change L.val.map (homOfLE k₁).op (L.val.map (homOfLE h₁).op m) =
    L.val.map (homOfLE k₂).op (L.val.map (homOfLE h₂).op m)
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply L.val (Subsingleton.elim _ _) m

/-- Pulling back a generator commutes with restricting it from `U` to `V ≤ U`. -/
theorem pullbackGenerator'_restrict (ψ : X ⟶ Y) (hψ : ∀ x, IsLocalHom (ψ.hom.stalkMap x).hom)
    (L : _root_.SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf Y))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y).property L)
    {U V : Opens Y} (h : V ≤ U) (s : Stacks.SheafOfModules.GeneratorSections Y L U) :
    Stacks.SheafOfModules.generatorRestrict ((modulePullback ψ).obj L)
        ((opensMap ψ).map (homOfLE h)).le (pullbackGenerator' ψ hψ L hL U s) =
      pullbackGenerator' ψ hψ L hL V (Stacks.SheafOfModules.generatorRestrict L h s) :=
  Subtype.ext (Stacks.RingedSpace.pullbackUnit_restrict ψ L (homOfLE h).op s.val)

/-- The unit relating the restricted pulled-back generators of `ε (ρ (i 0))` and
`ε (ρ (i 1))` on the overlap `W (i 0) ⊓ W (i 1)`. -/
noncomputable def pullTransUnit (ψ : X ⟶ Y)
    (L : _root_.SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf Y))
    {I : Type} (N : I → Opens Y) (ε : ∀ j, Stacks.SheafOfModules.GeneratorSections Y L (N j))
    {A : Type} (W : A → Opens X) (ρ : A → I) (hWρ : ∀ a, W a ≤ (opensMap ψ).obj (N (ρ a)))
    (i : Fin 2 → A) : (X.presheaf.obj (op (CechCochains.inter W i)))ˣ :=
  Units.map (X.presheaf.map (homOfLE (show CechCochains.inter W i ≤
      (opensMap ψ).obj (N (ρ (i 0)) ⊓ N (ρ (i 1))) from
        le_inf ((iInf_le (fun k => W (i k)) 0).trans (hWρ (i 0)))
          ((iInf_le (fun k => W (i k)) 1).trans (hWρ (i 1))))).op).hom.toMonoidHom
    (Units.map (ψ.hom.c.app (op (N (ρ (i 0)) ⊓ N (ρ (i 1))))).hom.toMonoidHom
      (Stacks.SheafOfModules.generatorRatioUnit L (N (ρ (i 0)) ⊓ N (ρ (i 1)))
        (Stacks.SheafOfModules.generatorRestrict L inf_le_left (ε (ρ (i 0))))
        (Stacks.SheafOfModules.generatorRestrict L inf_le_right (ε (ρ (i 1))))))

/-- **The Picard class of a pulled-back invertible module by local generators.** Let `ψ` be a
morphism of ringed spaces with local stalk maps, `L` an invertible module on the target with
generators `ε j` on opens `N j`, and `W` an open cover of the source refining the `ψ⁻¹ (N j)`
through `ρ`. Then the class of `ψ^* L` is the Čech class of the transition units of the
restricted pulled-back generators. -/
theorem torsorClass_pullback_eq_cech (ψ : X ⟶ Y) (hψ : ∀ x, IsLocalHom (ψ.hom.stalkMap x).hom)
    (L : _root_.SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf Y))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y).property L)
    {I : Type} (N : I → Opens Y) (ε : ∀ j, Stacks.SheafOfModules.GeneratorSections Y L (N j))
    {A : Type} (W : A → Opens X) (hW : (⊤ : Opens X) = ⨆ a, W a) (ρ : A → I)
    (hWρ : ∀ a, W a ≤ (opensMap ψ).obj (N (ρ a)))
    (hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property
      ((modulePullback ψ).obj L)) :
    ∃ z : CechCochains.cocycles1 W (Stacks.Cohomology.Generators.unitsSheaf X).presheaf,
      (∀ i, z.val i = Additive.ofMul (pullTransUnit ψ L N ε W ρ hWρ i)) ∧
      Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne X
        (Stacks.Cohomology.Generators.unitsSheaf X)
        (Quotient.mk _ (Stacks.Cohomology.Generators.generatorTorsorOfInvertible X
          ((modulePullback ψ).obj L) hinv).toTorsor) =
      Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X ⊤ W hW
        (Stacks.Cohomology.Generators.unitsSheaf X) (CechCochains.cls W _ z) := by
  let ε' : ∀ a, Stacks.SheafOfModules.GeneratorSections X ((modulePullback ψ).obj L) (W a) :=
    fun a => Stacks.SheafOfModules.generatorRestrict _ (hWρ a)
      (pullbackGenerator' ψ hψ L hL (N (ρ a)) (ε (ρ a)))
  have hu : ∀ i : Fin 2 → A,
      @SMul.smul ((structureSheafRing X).obj.obj (op (CechCochains.inter W i)))
        (((modulePullback ψ).obj L).val.obj (op (CechCochains.inter W i))) _
        (pullTransUnit ψ L N ε W ρ hWρ i).val
        (((modulePullback ψ).obj L).val.restrictₛₗ
          (homOfLE (iInf_le (fun k => W (i k)) 0)).op (ε' (i 0)).val) =
      ((modulePullback ψ).obj L).val.restrictₛₗ
          (homOfLE (iInf_le (fun k => W (i k)) 1)).op (ε' (i 1)).val := by
    intro i
    have hiV : CechCochains.inter W i ≤ (opensMap ψ).obj (N (ρ (i 0)) ⊓ N (ρ (i 1))) :=
      le_inf ((iInf_le (fun k => W (i k)) 0).trans (hWρ (i 0)))
        ((iInf_le (fun k => W (i k)) 1).trans (hWρ (i 1)))
    have he₀ := pullbackGenerator'_restrict ψ hψ L hL
      (inf_le_left : N (ρ (i 0)) ⊓ N (ρ (i 1)) ≤ N (ρ (i 0))) (ε (ρ (i 0)))
    have he₁ := pullbackGenerator'_restrict ψ hψ L hL
      (inf_le_right : N (ρ (i 0)) ⊓ N (ρ (i 1)) ≤ N (ρ (i 1))) (ε (ρ (i 1)))
    have k0 : ((modulePullback ψ).obj L).val.restrictₛₗ
        (homOfLE (iInf_le (fun k => W (i k)) 0)).op (ε' (i 0)).val =
        ((modulePullback ψ).obj L).val.restrictₛₗ (homOfLE hiV).op
          (pullbackGenerator' ψ hψ L hL _
            (Stacks.SheafOfModules.generatorRestrict L inf_le_left (ε (ρ (i 0))))).val := by
      rw [← he₀]
      exact restrictₛₗ_restrict_eq _ _ _ _ _
    have k1 : ((modulePullback ψ).obj L).val.restrictₛₗ
        (homOfLE (iInf_le (fun k => W (i k)) 1)).op (ε' (i 1)).val =
        ((modulePullback ψ).obj L).val.restrictₛₗ (homOfLE hiV).op
          (pullbackGenerator' ψ hψ L hL _
            (Stacks.SheafOfModules.generatorRestrict L inf_le_right (ε (ρ (i 1))))).val := by
      rw [← he₁]
      exact restrictₛₗ_restrict_eq _ _ _ _ _
    rw [k0, k1]
    have hspec := Stacks.SheafOfModules.generatorRatio_spec ((modulePullback ψ).obj L) _
      (pullbackGenerator' ψ hψ L hL _
        (Stacks.SheafOfModules.generatorRestrict L inf_le_left (ε (ρ (i 0)))))
      (pullbackGenerator' ψ hψ L hL _
        (Stacks.SheafOfModules.generatorRestrict L inf_le_right (ε (ρ (i 1)))))
    have hunit := generatorRatioUnit_pullbackGenerator' ψ hψ L hL
      (N (ρ (i 0)) ⊓ N (ρ (i 1)))
      (Stacks.SheafOfModules.generatorRestrict L inf_le_left (ε (ρ (i 0))))
      (Stacks.SheafOfModules.generatorRestrict L inf_le_right (ε (ρ (i 1))))
    rw [hspec]
    erw [← Stacks.SheafOfModules.generatorRatioUnit_val ((modulePullback ψ).obj L), hunit,
      PresheafOfModules.map_smul]
    rfl
  let T := Stacks.Cohomology.Generators.generatorTorsorOfInvertible X ((modulePullback ψ).obj L)
    hinv
  let s : ∀ a, T.F.obj (W a) := fun a => (T.sectionsEquiv (W a)).symm (ε' a)
  refine ⟨Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle T.toTorsor W s, fun i => ?_,
    Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_of_cocycle X _ T.toTorsor
      W hW s _ (Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec T.toTorsor W s)⟩
  rw [Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_val]
  apply Stacks.Cohomology.SheafTorsor.torsorDifference_eq
  apply (T.sectionsEquiv _).injective
  apply Subtype.ext
  change (T.sectionsEquiv _ (T.action.act (Multiplicative.ofAdd (Additive.ofMul _)) _)).val = _
  erw [T.sectionsEquiv_smul, T.sectionsEquiv_restrict, T.sectionsEquiv_restrict]
  simp only [s, Equiv.apply_symm_apply]
  exact hu i

end Transition

section LeraySec

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange Stacks.CategoryTheory.CechComplex
open Stacks.RingTheory.CechAcyclicity

/-- The intersection `V (x 0) ⊓ ⋯ ⊓ V (x m)` is contained in each `V (x k)`. -/
theorem inter_le_const {X : Scheme.{0}} {s : ℕ} (V : Fin s → X.Opens) {m : ℕ}
    (x : Fin (m + 1) → Fin s) (k : Fin (m + 1)) :
    inter V x ≤ inter V (fun _ : Fin 1 ↦ x k) := by
  rw [inter_eq_iInf, inter_eq_iInf]
  exact le_iInf fun _ => iInf_le _ k

/-- **Čech `H¹` of a standard cover of an affine open vanishes.** Let `U` be affine and
`g₁, …, gₛ` sections over `U` generating the unit ideal. A family `κ` of sections over the
pairwise intersections of the basic opens `D(gₘ)` satisfying the Čech cocycle identity is a
coboundary. -/
theorem exists_coboundary_of_standardCover {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {s : ℕ} (g : Fin s → Γ(X, U)) (hg : Ideal.span (Set.range g) = ⊤)
    (κ : ∀ x : Fin 2 → Fin s, Γ(X, inter (fun i ↦ X.basicOpen (g i)) x))
    (hκ : ∀ y : Fin 3 → Fin s,
      X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 0)).op
          (κ fun i ↦ y ((0 : Fin 3).succAbove i)) -
        X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 1)).op
          (κ fun i ↦ y ((1 : Fin 3).succAbove i)) +
        X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 2)).op
          (κ fun i ↦ y ((2 : Fin 3).succAbove i)) = 0) :
    ∃ h : ∀ m : Fin s, Γ(X, inter (fun i ↦ X.basicOpen (g i)) (fun _ : Fin 1 ↦ m)),
      ∀ x : Fin 2 → Fin s,
        κ x = X.presheaf.map (homOfLE (inter_le_const _ x 1)).op (h (x 1)) -
          X.presheaf.map (homOfLE (inter_le_const _ x 0)).op (h (x 0)) := by
  classical
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  haveI : F.IsQuasicoherent := inferInstance
  let e := fun {m : ℕ} (x : Fin (m + 1) → Fin s) => Stacks.Cohomology.Cech.interEquiv F hU g x
  let s₁ : CechTerm Γ(F, U) g 1 1 := fun x => (e x).symm (κ x)
  have hres : ∀ (y : Fin 3 → Fin s) (j : Fin 3),
      letI := moduleOfLE F (Stacks.Cohomology.Cech.inter_le g y)
      resAway Γ(F, U) (dvd_face g 1 y j) (s₁ fun i ↦ y (j.succAbove i)) =
        (e y).symm (X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y j)).op
          (κ fun i ↦ y (j.succAbove i))) := by
    intro y j
    rw [Stacks.Cohomology.Cech.resAway_eq_interEquiv F hU g y j]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, s₁, e]
    erw [LinearEquiv.apply_symm_apply]
    rfl
  have hs : cechD Γ(F, U) g 1 1 s₁ = 0 := by
    funext y
    rw [Stacks.RingTheory.CechAcyclicity.cechD_apply]
    change ∑ j : Fin 3, _ = 0
    rw [Fin.sum_univ_three, hres, hres, hres]
    letI := moduleOfLE F (Stacks.Cohomology.Cech.inter_le g y)
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      Fin.val_two, even_two, Even.neg_pow, one_pow]
    have key := congrArg (e y).symm (hκ y)
    erw [LinearEquiv.map_zero, LinearEquiv.map_add, map_sub] at key
    rwa [← sub_eq_add_neg]
  obtain ⟨u, hu⟩ := cech_exact g hg 1 0 s₁ hs
  refine ⟨fun m => e (fun _ : Fin 1 => m) (u fun _ => m), fun x => ?_⟩
  have h1 := congrFun hu x
  rw [Stacks.RingTheory.CechAcyclicity.cechD_apply, Fin.sum_univ_two] at h1
  rw [Stacks.Cohomology.Cech.resAway_eq_interEquiv F hU g x 0,
    Stacks.Cohomology.Cech.resAway_eq_interEquiv F hU g x 1] at h1
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h1
  have hz : ∀ (m : Fin s) (z : Fin 1 → Fin s) (_ : z = fun _ => m)
      (hle : inter (fun i ↦ X.basicOpen (g i)) x ≤ inter (fun i ↦ X.basicOpen (g i)) z)
      (hle' : inter (fun i ↦ X.basicOpen (g i)) x ≤
        inter (fun i ↦ X.basicOpen (g i)) (fun _ : Fin 1 => m)),
      X.presheaf.map (homOfLE hle).op (e z (u z)) =
        X.presheaf.map (homOfLE hle').op (e (fun _ : Fin 1 => m) (u fun _ => m)) := by
    intro m z hzm hle hle'
    subst hzm
    rfl
  have h0 : (fun i : Fin 1 => x ((0 : Fin 2).succAbove i)) = fun _ => x 1 := by
    funext i
    fin_cases i
    rfl
  have h1' : (fun i : Fin 1 => x ((1 : Fin 2).succAbove i)) = fun _ => x 0 := by
    funext i
    fin_cases i
    rfl
  apply (e x).symm.injective
  change _ = (e x).symm (κ x) at h1
  rw [← h1]
  erw [map_sub]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
  rw [sub_eq_add_neg]
  refine congrArg₂ (· + ·) ?_ (congrArg Neg.neg ?_)
  · exact congrArg (e x).symm (hz _ _ h0 _ _)
  · exact congrArg (e x).symm (hz _ _ h1' _ _)

end LeraySec

open Stacks.CategoryTheory.CechComplex

section Box

variable {C J : Scheme.{0}} {f : C ⟶ Spec (.of ℂ)} {sJ : J ⟶ Spec (.of ℂ)}

/-- The structure morphism of `C ×_ℂ J`. -/
noncomputable abbrev prodHom (f : C ⟶ Spec (.of ℂ)) (sJ : J ⟶ Spec (.of ℂ)) :
    pullback f sJ ⟶ Spec (.of ℂ) := pullback.snd f sJ ≫ sJ

/-- The `ℂ`-point `(x, t)` of `C ×_ℂ J`. -/
noncomputable def pair (x : ComplexPoints f) (t : ComplexPoints sJ) :
    ComplexPoints (prodHom f sJ) :=
  ⟨pullback.lift x.hom t.hom (by rw [x.hom_comp_structure, t.hom_comp_structure]), by
    rw [prodHom, ← Category.assoc, pullback.lift_snd]; exact t.hom_comp_structure⟩

/-- The first projection of the point `(x, t)` is `x`. -/
theorem pair_hom_fst (x : ComplexPoints f) (t : ComplexPoints sJ) :
    (pair x t).hom ≫ pullback.fst f sJ = x.hom := pullback.lift_fst _ _ _

/-- The second projection of the point `(x, t)` is `t`. -/
theorem pair_hom_snd (x : ComplexPoints f) (t : ComplexPoints sJ) :
    (pair x t).hom ≫ pullback.snd f sJ = t.hom := pullback.lift_snd _ _ _

/-- The box `A × V` in `C ×_ℂ J`. -/
noncomputable abbrev box (A : C.Opens) (V : J.Opens) : (pullback f sJ).Opens :=
  pullback.fst f sJ ⁻¹ᵁ A ⊓ pullback.snd f sJ ⁻¹ᵁ V

/-- If `x` is a point of `A` and `t` a point of `V`, then `(x, t)` is a point of `A × V`. -/
theorem mem_chart_box {A : C.Opens} {V : J.Opens} {x : ComplexPoints f} {t : ComplexPoints sJ}
    (hx : x ∈ chart A) (ht : t ∈ chart V) :
    pair x t ∈ chart (sX := prodHom f sJ) (box (f := f) (sJ := sJ) A V) := by
  rw [mem_chart_iff] at hx ht ⊢
  have e1 : pullback.fst f sJ (pair x t).toScheme = x.toScheme := by
    simp only [toScheme, ← Scheme.Hom.comp_apply, pair_hom_fst]
  have e2 : pullback.snd f sJ (pair x t).toScheme = t.toScheme := by
    simp only [toScheme, ← Scheme.Hom.comp_apply, pair_hom_snd]
  exact ⟨show pullback.fst f sJ _ ∈ A from e1 ▸ hx, show pullback.snd f sJ _ ∈ V from e2 ▸ ht⟩

/-- The box `A × V` of affine opens `A` and `V` is affine. -/
theorem isAffineOpen_box {A : C.Opens} {V : J.Opens} (hA : IsAffineOpen A) (hV : IsAffineOpen V) :
    IsAffineOpen (box (f := f) (sJ := sJ) A V) :=
  IsAffineOpen.inf_preimage_of_isPullback (IsPullback.of_hasPullback f sJ)
    (isAffineOpen_top (Spec (.of ℂ))) hA le_top hV le_top rfl

/-- **Künneth for boxes.** Every regular function on `A × V`, for `A` and `V` affine, is a finite
sum of products of pulled-back functions. -/
theorem exists_sum_box {A : C.Opens} {V : J.Opens} (hA : IsAffineOpen A) (hV : IsAffineOpen V)
    (a : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)) :
    ∃ (n : ℕ) (p : Fin n → Γ(C, A)) (q : Fin n → Γ(J, V)),
      a = ∑ l, (pullback.fst f sJ).appLE A (box (f := f) (sJ := sJ) A V) inf_le_left (p l) *
        (pullback.snd f sJ).appLE V (box (f := f) (sJ := sJ) A V) inf_le_right (q l) :=
  exists_sum_mul_of_isPushout (isPushout_appLE_of_isPullback (IsPullback.of_hasPullback f sJ)
    (isAffineOpen_top (Spec (.of ℂ))) hA le_top hV le_top rfl) a

/-- The image of `(x, t)` under the first projection is `x`. -/
theorem realize_fst_pair (x : ComplexPoints f) (t : ComplexPoints sJ) :
    realize (pullback.fst f sJ) (by rw [prodHom, ← pullback.condition]) (pair x t) = x :=
  ComplexPoints.ext (pair_hom_fst x t)

/-- The image of `(x, t)` under the second projection is `t`. -/
theorem realize_snd_pair (x : ComplexPoints f) (t : ComplexPoints sJ) :
    realize (pullback.snd f sJ) rfl (pair x t) = t :=
  ComplexPoints.ext (pair_hom_snd x t)

/-- The pullback of `p ∈ Γ(C, A)` to `A × V` takes the value `p x` at `(x, t)`. -/
theorem eval_fst_pair {A : C.Opens} {V : J.Opens} (p : Γ(C, A)) {x : ComplexPoints f}
    {t : ComplexPoints sJ} (hx : x ∈ chart A) (ht : t ∈ chart V) :
    eval (box (f := f) (sJ := sJ) A V)
        ((pullback.fst f sJ).appLE A (box (f := f) (sJ := sJ) A V) inf_le_left p)
        ⟨pair x t, mem_chart_box hx ht⟩ = eval A p ⟨x, hx⟩ := by
  have h1 := evalHom_res (sX := prodHom f sJ) (inf_le_left : box (f := f) (sJ := sJ) A V ≤ _)
    ⟨pair x t, mem_chart_box hx ht⟩ ((pullback.fst f sJ).app A p)
  change evalHom _ _ (((pullback.fst f sJ).app A ≫ (pullback f sJ).presheaf.map _) p) = _
  rw [CommRingCat.comp_apply, ← h1]
  have h2 := evalHom_realize (pullback.fst f sJ) (by rw [prodHom, ← pullback.condition]) A p
    (pair x t) (by rw [realize_fst_pair]; exact hx)
    (show pair x t ∈ chart (pullback.fst f sJ ⁻¹ᵁ A) from
      chart_mono inf_le_left (mem_chart_box hx ht))
  refine h2.symm.trans ?_
  have key : ∀ (z : ComplexPoints f) (hz : z = x) (hzA : z ∈ chart A),
      evalHom A ⟨z, hzA⟩ p = eval A p ⟨x, hx⟩ := by rintro _ rfl _; rfl
  exact key _ (realize_fst_pair x t) _

/-- The pullback of `q ∈ Γ(J, V)` to `A × V` takes the value `q t` at `(x, t)`. -/
theorem eval_snd_pair {A : C.Opens} {V : J.Opens} (q : Γ(J, V)) {x : ComplexPoints f}
    {t : ComplexPoints sJ} (hx : x ∈ chart A) (ht : t ∈ chart V) :
    eval (box (f := f) (sJ := sJ) A V)
        ((pullback.snd f sJ).appLE V (box (f := f) (sJ := sJ) A V) inf_le_right q)
        ⟨pair x t, mem_chart_box hx ht⟩ = eval V q ⟨t, ht⟩ := by
  have h1 := evalHom_res (sX := prodHom f sJ) (inf_le_right : box (f := f) (sJ := sJ) A V ≤ _)
    ⟨pair x t, mem_chart_box hx ht⟩ ((pullback.snd f sJ).app V q)
  change evalHom _ _ (((pullback.snd f sJ).app V ≫ (pullback f sJ).presheaf.map _) q) = _
  rw [CommRingCat.comp_apply, ← h1]
  have h2 := evalHom_realize (pullback.snd f sJ) rfl V q
    (pair x t) (by rw [realize_snd_pair]; exact ht)
    (show pair x t ∈ chart (pullback.snd f sJ ⁻¹ᵁ V) from
      chart_mono inf_le_right (mem_chart_box hx ht))
  refine h2.symm.trans ?_
  have key : ∀ (z : ComplexPoints sJ) (hz : z = t) (hzV : z ∈ chart V),
      evalHom V ⟨z, hzV⟩ q = eval V q ⟨t, ht⟩ := by rintro _ rfl _; rfl
  exact key _ (realize_snd_pair x t) _

/-- Every `ℂ`-point of `C ×_ℂ J` is the pair of its two projections. -/
theorem pair_realize (q : ComplexPoints (prodHom f sJ)) :
    pair (realize (pullback.fst f sJ) (by rw [prodHom, ← pullback.condition]) q)
      (realize (pullback.snd f sJ) rfl q) = q := by
  apply ComplexPoints.ext
  apply pullback.hom_ext
  · rw [pair_hom_fst]; rfl
  · rw [pair_hom_snd]; rfl

end Box

/-- **Quotient rule for `A / Gx ^ k`.** If `A` and `Gx` have derivatives `A'` and `G'` at `w`
and `Gx w ≠ 0`, then `A / Gx ^ k` has at `w` the derivative
`e ↦ A' e / Gx w ^ k - k * A w * G' e / Gx w ^ (k + 1)`. -/
theorem hasFDerivAt_div_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A Gx : E → ℂ} {A' G' : E →L[ℂ] ℂ} {w : E} (hA : HasFDerivAt A A' w)
    (hG : HasFDerivAt Gx G' w) (h0 : Gx w ≠ 0) (k : ℕ) :
    ∃ F' : E →L[ℂ] ℂ, HasFDerivAt (fun y => A y / Gx y ^ k) F' w ∧
      ∀ e, F' e = A' e / Gx w ^ k - k * A w * G' e / Gx w ^ (k + 1) := by
  have hGk : HasFDerivAt (fun y => Gx y ^ k) ((k * Gx w ^ (k - 1)) • G') w := by
    simpa using hG.pow k
  have hk0 : Gx w ^ k ≠ 0 := pow_ne_zero k h0
  have hinv := (hasDerivAt_inv hk0).comp_hasFDerivAt w hGk
  have hprod := hA.mul hinv
  refine ⟨_, hprod.congr_fderiv rfl |>.congr_of_eventuallyEq ?_, fun e => ?_⟩
  · exact Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv]
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Function.comp_apply, ContinuousLinearMap.neg_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      field_simp
      ring

end Fam

end FamilyLogarithm

end MMP.JacobianLogarithm

end
