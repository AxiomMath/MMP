module

public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization

/-!
# Base change of the ground field: ampleness, rays, canonical divisors and top forms

Let `k₀ ⊆ K` be algebraically closed fields. This file gathers what the comparison of a program
over `k₀` with its base change to `K` uses about relative ampleness, extremal rays and rational
top forms:

* relative ampleness of an invertible sheaf is insensitive to base change of the target;
* the curve form of a `ℚ`-Cartier divisor is determined on classes of curves, and linear
  equivalences carry extremal rays to extremal rays;
* orders of vanishing of rational top forms are computed in charts, and are compatible with
  base change along prime divisors;
* pull-backs of rational top forms along birational morphisms, crepant boundaries obtained from
  pull-backs of `ℚ`-Cartier divisors, and pull-backs of divisors along composites.

## Main results

* `MMP.ProgramBaseChange.isRelativelyAmple_iff_of_isPullback`: relative ampleness and base change.
* `MMP.ProgramBaseChange.isExtremalRay_image_iff`: extremal rays and linear equivalences.
* `MMP.ProgramBaseChange.isCrepantBoundary_pullback`: crepant boundaries from Cartier pull-backs.

## References

* [KM98] Kollár, Mori, *Birational Geometry of Algebraic Varieties*.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold
open MMP.Spreading (chart_dim_eq_of_isPullback form_eq_smul_of_isPullback
  functionFieldMap_germToFunctionField germToFunctionField_app_map)

universe u

namespace MMP.ProgramBaseChange

section Helpers

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

/-! ### Relative ampleness under base change -/

section RelativeAmple

/-- Ampleness relative to a quasi-compact morphism, in the two senses. -/
private theorem isRelativelyAmple_iff_stacks {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hf : QuasiCompact f) :
    MMP.Mori.IsRelativelyAmple f L ↔ Stacks.RelativeAmple.IsRelativelyAmple f L :=
  (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover f L hf).symm

/-- **Relative ampleness descends along fpqc base change.** -/
public theorem isRelativelyAmple_iff_of_isPullback {X₀ X Z₀ Z : Scheme.{u}} {π : X ⟶ X₀} {f : X ⟶ Z}
    {f₀ : X₀ ⟶ Z₀} {πZ : Z ⟶ Z₀} (hsq : IsPullback π f f₀ πZ) [Flat πZ] [Surjective πZ]
    [QuasiCompact πZ] [QuasiCompact f₀] [QuasiCompact f] (L₀ : X₀.Modules)
    [Stacks.Ample.IsInvertibleModule X₀ L₀] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (e : L ≅ (Scheme.Modules.pullback π).obj L₀) :
    MMP.Mori.IsRelativelyAmple f₀ L₀ ↔ MMP.Mori.IsRelativelyAmple f L := by
  rw [isRelativelyAmple_iff_stacks f₀ L₀ ‹_›, isRelativelyAmple_iff_stacks f L ‹_›]
  have hcov : Presieve.ofArrows (fun _ : PUnit.{u + 1} => Z) (fun _ => πZ) ∈
      Scheme.fpqcPrecoverage Z₀ := by
    rw [Presieve.ofArrows_pUnit]
    exact πZ.singleton_mem_fpqcPrecoverage
  rw [Stacks.Descent.isRelativelyAmple_iff_forall_of_fpqcCover hcov f₀ L₀ (fun _ => hsq)]
  refine ⟨fun H => ?_, fun H _ => ?_⟩
  · exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr f _ _
      ((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback π).app L₀ ≪≫ e.symm)).mp
        (H PUnit.unit)
  · exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr f _ _
      ((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback π).app L₀ ≪≫
        e.symm)).mpr H

end RelativeAmple

/-! ### Curve forms and extremal rays -/

section CurveForm

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The curve form of a `ℚ`-Cartier `ℚ`-divisor on the class of a proper curve is its
intersection number with that curve. -/
public theorem curveForm_numericalClass_cycle (D : QDivisor X) (h : D.IsQCartier)
    (C : ProperCurve sX) :
    QDivisor.curveForm sX D h (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (D.intersectionNumber k sX C.ι C.dim_le h : ℝ) := by
  have hC := Divisor.mem_cartierSubgroup.mp (D.cartierIndexSMul h).2
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D h _ hC
      (QDivisor.toQDivisor_cartierIndexSMul D h),
    QDivisor.curveForm, QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier,
    Finsupp.smul_single, Finsupp.sum_single_index (by simp), LinearMap.smul_apply,
    NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  simp only [smul_eq_mul, mul_one]
  rw [ProperCurve.degree_divisorialSheaf C _ hC]
  push_cast
  ring

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
/-- Two linear maps on `N₁(X)_ℝ` agreeing on the classes of proper curves are equal. -/
public theorem linearMap_ext_numericalClass_cycle {W : Type*} [AddCommGroup W] [Module ℝ W]
    {φ ψ : NumericalCurveClasses sX →ₗ[ℝ] W}
    (h : ∀ C : ProperCurve sX,
      φ (OneCycle.numericalClass sX (C.cycle ℝ)) = ψ (OneCycle.numericalClass sX (C.cycle ℝ))) :
    φ = ψ :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun C => LinearMap.ext_ring (h C))

end CurveForm

section ExtremalRay

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Linear equivalences carry extremal rays to extremal rays. -/
public theorem isExtremalRay_image (e : V ≃ₗ[ℝ] W) {N R : Set V}
    (h : MMP.Mori.IsExtremalRay ℝ N R) : MMP.Mori.IsExtremalRay ℝ (e '' N) (e '' R) := by
  obtain ⟨⟨hRN, ⟨h0, hsm⟩, hadd, hext⟩, v, hv, hR⟩ := h
  refine ⟨⟨Set.image_mono hRN, ⟨⟨0, h0, map_zero e⟩, ?_⟩, ?_, ?_⟩, e v,
    fun h0 => hv (e.injective (h0.trans (map_zero e).symm)), ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ c hc
    exact ⟨c • w, hsm w hw c hc, map_smul e c w⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩
    exact ⟨u + w, hadd u hu w hw, map_add e u w⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩ ⟨z, hz, hzuw⟩
    have huw : u + w = z := e.injective ((map_add e u w).trans hzuw.symm)
    obtain ⟨h1, h2⟩ := hext u hu w hw (huw ▸ hz)
    exact ⟨⟨u, h1, rfl⟩, ⟨w, h2, rfl⟩⟩
  · rw [hR]
    ext w'
    constructor
    · rintro ⟨w, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, (map_smul e c v).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, map_smul e c v⟩

/-- Linear equivalences preserve and reflect extremal rays. -/
public theorem isExtremalRay_image_iff (e : V ≃ₗ[ℝ] W) {N R : Set V} :
    MMP.Mori.IsExtremalRay ℝ (e '' N) (e '' R) ↔ MMP.Mori.IsExtremalRay ℝ N R := by
  refine ⟨fun h => ?_, isExtremalRay_image e⟩
  simpa [Set.image_image] using isExtremalRay_image e.symm h

end ExtremalRay

/-! ### Rational top forms under base change -/

section ChartForms

/-- **The order of a chart form.** On an affine chart `V` with étale coordinates `g(Xᵢ)`, for
sections `z` over `V₁` and a basic open `D(f) ⊆ V₁` of `V` on which `dz = h₀ · dg(X)`, the order of
the rational form `dz` of a fibre along a prime divisor over `V` is the order of `h₀`. -/
public theorem ordForm_chart {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y} {snd : F ⟶ Spec (.of L)}
    (hpb : IsPullback fst snd q t) [IsIntegral F] [IsLocallyNoetherian F] {V : Y.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V))
    (hg : g.Etale) (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) {V₁ : Y.Opens}
    (z : Fin n → Γ(Y, V₁)) (f : Γ(Y, V)) (hf : Y.basicOpen f ≤ V₁)
    [Nonempty (fst ⁻¹ᵁ Y.basicOpen f)] [Nonempty (fst ⁻¹ᵁ V₁)] (h₀ : Γ(Y, Y.basicOpen f))
    (hrel : letI := (q.appLE ⊤ (Y.basicOpen f) le_top).hom.toAlgebra
      exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n
          (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
            (Y.presheaf.map (homOfLE hf).op (z i))) =
        h₀ • exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n (fun i =>
          KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
            (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g (MvPolynomial.X i)))))
    (Γ : MMP.Mori.PrimeDivisor F) (hΓ : Γ.genericPoint ∈ fst ⁻¹ᵁ V)
    (ω : MMP.Mori.RationalTopForms snd n)
    (hω : letI := MMP.Mori.functionFieldAlgebra snd
      ω = exteriorPower.ιMulti F.functionField n fun i =>
        KaehlerDifferential.D L F.functionField
            (F.germToFunctionField (fst ⁻¹ᵁ V₁) (fst.app V₁ (z i)))) :
    Γ.ordForm (ω.toPluriForms snd) =
      F.ord (F.germToFunctionField (fst ⁻¹ᵁ Y.basicOpen f) (fst.app _ h₀)) Γ.genericPoint := by
  letI := MMP.Mori.functionFieldAlgebra snd
  refine MMP.Spreading.ordForm_eq_ord_of_isPullback hpb V hV g hg hgC (Y.basicOpen f)
    (Y.basicOpen_le f) (fun i => Y.presheaf.map (homOfLE hf).op (z i)) h₀ hrel Γ hΓ ω
    (hω.trans ?_)
  congr 1
  funext i
  rw [germToFunctionField_app_map fst hf (z i)]

/-- Generic germs through the identity square. -/
public theorem germToFunctionField_id_app {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens} [Nonempty W]
    [Nonempty ((𝟙 Y) ⁻¹ᵁ W)] (a : Γ(Y, W)) :
    Y.germToFunctionField ((𝟙 Y) ⁻¹ᵁ W) (Scheme.Hom.app (𝟙 Y) W a) =
      Y.germToFunctionField W a := rfl

end ChartForms

section OrdBaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

attribute [local instance] MMP.Resolution.componentField

/-- The generic point of an integral scheme lies in every nonempty open. -/
private theorem componentGenericPoint_mem {X : Scheme.{u}} [IsIntegral X] {W : X.Opens} [Nonempty W]
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∈ W := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
  obtain ⟨x⟩ := ‹Nonempty W›
  exact (genericPoint_spec X).specializes trivial |>.mem_open W.isOpen x.2

/-- The generic germ of a regular function is the image of its germ at the generic point of a
component. -/
private theorem germToFunctionField_eq_componentToFunctionField {X : Scheme.{u}} [IsIntegral X]
    {W : X.Opens} [Nonempty W] (a : Γ(X, W)) (Z : irreducibleComponents X) :
    X.germToFunctionField W a = (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)).hom
        ((X.presheaf.germ W (componentGenericPoint X Z) (componentGenericPoint_mem Z)).hom a) :=
  (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _).symm

/-- **The orders of a regular function are those of a unit of `K(X)`.** -/
private theorem exists_units_ord_germToFunctionField {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {W : X.Opens} [Nonempty W] (a : Γ(X, W))
    (ha : X.germToFunctionField W a ≠ 0) :
    ∃ φ : (RationalFunctions X)ˣ, (∀ Z : irreducibleComponents X,
        (φ : RationalFunctions X) Z =
          (X.presheaf.germ W (componentGenericPoint X Z) (componentGenericPoint_mem Z)).hom a) ∧
      ∀ Γ : MMP.Mori.PrimeDivisor X,
        X.ord (X.germToFunctionField W a) Γ.genericPoint = Γ.ord φ := by
  have hne (Z : irreducibleComponents X) :
      (X.presheaf.germ W (componentGenericPoint X Z) (componentGenericPoint_mem Z)).hom a ≠ 0 :=
    fun h0 => ha (by rw [germToFunctionField_eq_componentToFunctionField a Z, h0, map_zero])
  let φ : (RationalFunctions X)ˣ :=
    (RationalFunctions.unitsEquiv X).symm fun Z => Units.mk0 _ (hne Z)
  refine ⟨φ, fun Z => rfl, fun Γ => ?_⟩
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField Γ φ,
    germToFunctionField_eq_componentToFunctionField a Γ.component]
  rfl

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X] [IsNormal X₀] [IsNormal X]
  [IsLocallyNoetherian X₀] [IsLocallyNoetherian X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

omit [IsLocallyNoetherian X₀] [IsLocallyNoetherian X] in
/-- The pull-back of a regular function with nonzero generic germ has nonzero generic germ. -/
public theorem germToFunctionField_app_ne_zero [IsDominant π] {W : X₀.Opens} [Nonempty W]
    [Nonempty (π ⁻¹ᵁ W)] (a : Γ(X₀, W)) (ha : X₀.germToFunctionField W a ≠ 0) :
    X.germToFunctionField (π ⁻¹ᵁ W) (π.app W a) ≠ 0 := by
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X₀) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X₀)⟩⟩
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X)⟩⟩
  rw [germToFunctionField_eq_componentToFunctionField _ Z]
  rw [germToFunctionField_eq_componentToFunctionField a Z₀] at ha
  have h1 : (X₀.presheaf.germ W (componentGenericPoint X₀ Z₀) (componentGenericPoint_mem Z₀)).hom a
      ≠ 0 := fun h0 => ha (by rw [h0, map_zero])
  have e := MMP.Fourfold.fieldMap_germ π Z₀ Z (componentGenericPoint_mem Z₀) a
  refine fun h0 => h1 ((MMP.Fourfold.fieldMap π Z₀ Z).injective ?_)
  rw [map_zero, e]
  exact (map_eq_zero_iff _ (RingHom.injective _)).mp h0

omit [IsAlgClosed K] in
/-- **Orders of pulled-back regular functions along base-changed prime divisors.** -/
public theorem ord_germToFunctionField_app_of_closure_eq [LocallyOfFiniteType s₀] [IsDominant π]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {P₀ : MMP.Mori.PrimeDivisor X₀} {P : MMP.Mori.PrimeDivisor X}
    (hP : closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint}) {W : X₀.Opens}
    [Nonempty W] [Nonempty (π ⁻¹ᵁ W)] (a : Γ(X₀, W)) (ha : X₀.germToFunctionField W a ≠ 0) :
    X.ord (X.germToFunctionField (π ⁻¹ᵁ W) (π.app W a)) P.genericPoint =
      X₀.ord (X₀.germToFunctionField W a) P₀.genericPoint := by
  obtain ⟨φ₀, hφ₀, hord₀⟩ := exists_units_ord_germToFunctionField a ha
  obtain ⟨φ, hφ, hord⟩ := exists_units_ord_germToFunctionField (π.app W a)
    (germToFunctionField_app_ne_zero a ha)
  rw [hord P, hord₀ P₀]
  have e1 := P.valuation_component φ
  rw [hφ P.component, ← MMP.Fourfold.fieldMap_germ π P₀.component P.component
    (componentGenericPoint_mem P₀.component) a, valuation_fieldMap_of_closure_eq h hP,
    ← hφ₀ P₀.component, P₀.valuation_component] at e1
  exact (WithZero.exp_injective e1).symm

omit [IsLocallyNoetherian X₀] in
/-- **Orders of pulled-back regular functions along prime divisors over the generic point.** -/
public theorem ord_germToFunctionField_app_eq_zero [IsDominant π] {P : MMP.Mori.PrimeDivisor X}
    (hP : π P.genericPoint = genericPoint X₀) {W : X₀.Opens} [Nonempty W] [Nonempty (π ⁻¹ᵁ W)]
    (a : Γ(X₀, W)) (ha : X₀.germToFunctionField W a ≠ 0) :
    X.ord (X.germToFunctionField (π ⁻¹ᵁ W) (π.app W a)) P.genericPoint = 0 := by
  obtain ⟨φ, hφ, hord⟩ := exists_units_ord_germToFunctionField (π.app W a)
    (germToFunctionField_app_ne_zero a ha)
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X₀) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X₀)⟩⟩
  rw [hord P]
  have hu : IsUnit ((X₀.presheaf.germ W (componentGenericPoint X₀ Z₀)
      (componentGenericPoint_mem Z₀)).hom a) := by
    refine Ne.isUnit fun h0 => ha ?_
    rw [germToFunctionField_eq_componentToFunctionField a Z₀, h0, map_zero]
  have e1 := P.valuation_component φ
  rw [hφ P.component, ← MMP.Fourfold.fieldMap_germ π Z₀ P.component
    (componentGenericPoint_mem Z₀) a, valuation_fieldMap_eq_one hP Z₀ hu] at e1
  exact WithZero.exp_eq_one.mp e1.symm

end OrdBaseChange

/-! ### Pull-backs of top forms -/

section FormPullback

variable {k : Type u} [Field k]

private theorem subsingletonEquiv_basis_one {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis Unit K L) :
    PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => L) 0
      (ZTensorPower.basis b 1 ()) = b () := by
  erw [ZTensorPower.basis_ofNat b 1]
  exact PiTensorProduct.subsingletonEquiv_apply_tprod _ _

/-- Pull-back of top forms along a pull-back generator is `topFormsMap`. -/
private theorem subsingletonEquiv_pullbackForms {K K' : Type u} [Field K] [Field K'] [Algebra k K]
    [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ} {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : MMP.Mori.IsPullbackGenerator K' ω) (τ : MMP.Mori.PluriForms k K d 1) :
    PiTensorProduct.subsingletonEquiv (R := K') (s := fun _ : Fin 1 => ⋀[K']^d Ω[K'⁄k]) 0
        (MMP.Mori.pullbackForms (K' := K') 1 τ) =
      MMP.Mori.topFormsMap k K K' d
        (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => ⋀[K]^d Ω[K⁄k]) 0 τ) := by
  rw [MMP.Mori.pullbackForms_eq hω]
  unfold MMP.Mori.pullbackFormsAlong
  set b := MMP.Mori.basisOfSpanSingleton hω.1 hω.ne_zero
  conv_rhs => rw [← MMP.Mori.basis_unit_repr_smul (ZTensorPower.basis b 1) τ]
  erw [LinearEquiv.map_smul, LinearEquiv.map_smul, subsingletonEquiv_basis_one,
    subsingletonEquiv_basis_one, LinearMap.map_smul, algebraMap_smul]
  simp [b]

/-- **Pull-back of a top form.** If `σ` is a top form on `Z` whose image `σ'` under the map of
function fields of `μ` is nonzero, and `Z`, `W` have the same dimension, then `μ^*σ = σ'`. -/
public theorem pullbackRationalPluriForms_toPluriForms_eq [PerfectField k] {Z W : Scheme.{u}}
    [IsIntegral Z] [IsIntegral W] (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] (μ : W ⟶ Z)
    [IsDominant μ] [LocallyOfFiniteType (μ ≫ sZ)] {n : ℕ} (hZ : topologicalKrullDim Z = n)
    (hW : topologicalKrullDim W = n) (σ : MMP.Mori.RationalTopForms sZ n)
    (σ' : MMP.Mori.RationalTopForms (μ ≫ sZ) n)
    (hσσ' : letI := MMP.Mori.functionFieldAlgebra sZ
      letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
      letI := MMP.Mori.functionFieldMapAlgebra μ
      haveI := MMP.Mori.isScalarTower_functionFieldMap sZ μ
      σ' = MMP.Mori.topFormsMap k Z.functionField W.functionField n σ) (hσ' : σ' ≠ 0) :
    MMP.Mori.pullbackRationalPluriForms sZ μ (σ.toPluriForms sZ) = σ'.toPluriForms (μ ≫ sZ) := by
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
  letI := MMP.Mori.functionFieldMapAlgebra μ
  haveI := MMP.Mori.isScalarTower_functionFieldMap sZ μ
  obtain ⟨B⟩ := MMP.Fourfold.exists_basis_topForms (sX := sZ) hZ
  obtain ⟨B'⟩ := MMP.Fourfold.exists_basis_topForms (sX := μ ≫ sZ) hW
  have hσ : (σ : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) ≠ 0 := by
    intro h0
    apply hσ'
    rw [hσσ']
    change MMP.Mori.topFormsMap k Z.functionField W.functionField n
      (σ : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) = 0
    rw [show (σ : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) = 0 from h0]
    exact map_zero (MMP.Mori.topFormsMap k Z.functionField W.functionField n)
  have hgen : MMP.Mori.IsPullbackGenerator W.functionField
      (σ : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) :=
    ⟨MMP.Spreading.span_singleton_eq_top_of_basis_unit B hσ,
      MMP.Spreading.span_singleton_eq_top_of_basis_unit B' (hσσ' ▸ hσ'), hσσ' ▸ hσ'⟩
  apply (PiTensorProduct.subsingletonEquiv (R := W.functionField)
    (s := fun _ : Fin 1 => ⋀[W.functionField]^n Ω[W.functionField⁄k]) 0).injective
  refine (subsingletonEquiv_pullbackForms hgen (σ.toPluriForms sZ)).trans ?_
  erw [PiTensorProduct.subsingletonEquiv_apply_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]
  exact hσσ'.symm

end FormPullback

/-! ### Crepant boundaries from Cartier pull-backs -/

section CrepantFromCartier

variable {k : Type u} [Field k]

attribute [local instance] MMP.Resolution.componentField

/-- **The crepant boundary through the Cartier pull-back.** Let `ω ≠ 0` be a rational top form of
a normal variety `Z` of dimension `n`, `L = m(div ω + Δ)` a Cartier divisor and `μ : W ⟶ Z` a
birational morphism from a normal variety of dimension `n`. Then
`Δ_W = (1/m) μ^*L - div(μ^*ω)` is the crepant boundary of `(Z, Δ)` for the canonical divisor
`div ω`. -/
public theorem isCrepantBoundary_pullback [PerfectField k] {Z W : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [LocallyOfFiniteType sZ] (hZ : MMP.Mori.IsNormalVariety k sZ) {n : ℕ}
    (hn : topologicalKrullDim Z = n) {μ : W ⟶ Z} (hW : MMP.Mori.IsNormalVariety k (μ ≫ sZ))
    (hμ : MMP.Mori.IsBirationalMorphism μ) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] [LocallyOfFiniteType (μ ≫ sZ)] (hnW : topologicalKrullDim W = n)
    {Δ : QDivisor Z} {ω : MMP.Mori.RationalTopForms sZ n} (hω : ω ≠ 0) {m : ℕ} (hm : 0 < m)
    {L : Divisor Z} (hL : Divisor.toQDivisor L = (m : ℤ) •
        (Divisor.toQDivisor (MMP.Mori.topFormDivisor sZ ω) + Δ))
    (hLc : L.IsCartier) :
    haveI := hμ.isDominant
    MMP.Mori.IsCrepantBoundary sZ n (MMP.Mori.topFormDivisor sZ ω) Δ μ hW hμ
      ((1 / (m : ℚ)) • Divisor.toQDivisor (L.pullback hLc
          (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant μ L)) -
        Divisor.toQDivisor (MMP.Mori.divisorOfForm
          (MMP.Mori.pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ)))) := by
  haveI := hμ.isDominant
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant μ L
  have hpb := Divisor.isPullback_pullback hLc hB
  refine MMP.Spreading.isCrepantBoundary_of_localEquations hZ hn hW hμ hnW hω hm hL hLc
    fun F => ?_
  obtain ⟨U, hU, ψ, hψ⟩ := hLc (μ F.genericPoint)
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents Z) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint Z)⟩⟩
  obtain ⟨V, hV, a, ha⟩ := Z.presheaf.exists_germ_eq ((ψ : RationalFunctions Z) Z₀)
  haveI : Nonempty V := ⟨⟨_, hV⟩⟩
  obtain ⟨ZW⟩ : Nonempty (irreducibleComponents W) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint W)⟩⟩
  haveI : Nonempty (μ ⁻¹ᵁ V) := ⟨⟨componentGenericPoint W ZW, by
    change μ _ ∈ V
    rwa [MMP.Fourfold.map_componentGenericPoint μ ZW Z₀]⟩⟩
  have hsub : Subsingleton (irreducibleComponents Z) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hne : Z.germToFunctionField V a ≠ 0 := by
    rw [germToFunctionField_eq_componentToFunctionField a Z₀]
    intro h0
    refine (ψ.isUnit.map (RationalFunctions.component Z Z₀)).ne_zero ?_
    change (ψ : RationalFunctions Z) Z₀ = 0
    rw [← ha]
    exact (map_eq_zero_iff _ (RingHom.injective _)).mp h0
  refine ⟨U, Z.germToFunctionField V a, hne, hU, fun Γ hΓ => ?_, ?_⟩
  · obtain ⟨φ'', hφ'', hord⟩ := exists_units_ord_germToFunctionField a hne
    have hψφ : ψ = φ'' := by
      apply (RationalFunctions.unitsEquiv Z).injective
      funext Z'
      obtain rfl : Z' = Z₀ := Subsingleton.elim _ _
      apply Units.ext
      change (ψ : RationalFunctions Z) Z' = (φ'' : RationalFunctions Z) Z'
      rw [hφ'' Z', ← ha]
    rw [hord Γ, hψ Γ hΓ, hψφ]
  · haveI : Nonempty ((𝟙 W) ⁻¹ᵁ (μ ⁻¹ᵁ V)) := ‹Nonempty (μ ⁻¹ᵁ V)›
    have e1 := functionFieldMap_germToFunctionField μ V (μ ⁻¹ᵁ V) le_rfl a
    rw [← Scheme.Hom.app_eq_appLE] at e1
    rw [e1]
    obtain ⟨φW, hφW, hordW⟩ := exists_units_ord_germToFunctionField (μ.app V a)
      (e1 ▸ (map_ne_zero _).mpr hne)
    rw [hordW F]
    have hE : (F.support ∩ μ ⁻¹ᵁ U).Nonempty := ⟨F.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hU⟩
    have e2 := MMP.Fourfold.valuation_fieldMap_of_isPullback μ hpb hψ F hE Z₀
    rw [← ha, MMP.Fourfold.fieldMap_germ, ← hφW F.component, F.valuation_component] at e2
    have e3 := WithZero.exp_injective e2
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      MMP.Mori.coeff_divisorOfForm]
    rw [e3]
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    change (((L.pullback hLc hB).coeff F : ℤ) : ℚ) =
      m * (_ + ((1 / (m : ℚ)) • (((L.pullback hLc hB).coeff F : ℤ) : ℚ) - _))
    simp only [smul_eq_mul, add_sub_cancel]
    field_simp

end CrepantFromCartier

/-! ### Principal divisors under base change -/

section PrincipalDescent

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

attribute [local instance] MMP.Resolution.componentField

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X] [IsNormal X₀] [IsNormal X]
  [IsLocallyNoetherian X₀] [IsLocallyNoetherian X] [CompactSpace X₀] [CompactSpace X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- The germs of a constant at the generic points of the components. -/
public noncomputable abbrev cstGerm (s : X ⟶ Spec (.of K)) (Z : irreducibleComponents X) (c : K) :
    X.presheaf.stalk (componentGenericPoint X Z) :=
  (X.presheaf.germ ⊤ (componentGenericPoint X Z) (by simp)).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c))

end PrincipalDescent

/-! ### Pull-backs along composites, and pull-backs of forms -/

section PullbackComp

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = e^*L` for `e = f ∘ g`. -/
public theorem divisor_isPullback_comp {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Z] [IsNormal Z] {f : Y ⟶ X} {g : Z ⟶ Y} {e : Z ⟶ X} (he : g ≫ f = e)
    {L : Divisor X} {L' : Divisor Y} {L'' : Divisor Z}
    {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, e (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback e hB'' L'' := by
  subst he
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes
        (f.base.hom.map_specializes hspec)).hom.toMonoidHom a) ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes
          (f.base.hom.map_specializes hspec)).hom a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- Germs at the generic point of the pull-backs of a section along equal morphisms agree. -/
public theorem germToFunctionField_app_congr {W Z : Scheme.{u}} [IsIntegral W] {e e' : W ⟶ Z}
    (h : e = e') (V : Z.Opens) [Nonempty (e ⁻¹ᵁ V)] [Nonempty (e' ⁻¹ᵁ V)] (t : Γ(Z, V)) :
    W.germToFunctionField (e ⁻¹ᵁ V) (e.app V t) =
      W.germToFunctionField (e' ⁻¹ᵁ V) (e'.app V t) := by
  subst h
  rfl

/-- The image of `dz₁ ∧ ⋯ ∧ dzₙ` under a dominant morphism `μ` is `d(μ^*z₁) ∧ ⋯ ∧ d(μ^*zₙ)`. -/
public theorem topFormsMap_ιMulti_germ {k : Type u} [Field k] {Z W : Scheme.{u}} [IsIntegral Z]
    [IsIntegral W] (sZ : Z ⟶ Spec (.of k)) (μ : W ⟶ Z) [IsDominant μ] {n : ℕ} (V : Z.Opens)
    [Nonempty V] [Nonempty (μ ⁻¹ᵁ V)] (z : Fin n → Γ(Z, V)) :
    letI := MMP.Mori.functionFieldAlgebra sZ
    letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
    letI := MMP.Mori.functionFieldMapAlgebra μ
    haveI := MMP.Mori.isScalarTower_functionFieldMap sZ μ
    MMP.Mori.topFormsMap k Z.functionField W.functionField n
        (exteriorPower.ιMulti Z.functionField n fun i =>
          KaehlerDifferential.D k Z.functionField (Z.germToFunctionField V (z i))) =
      exteriorPower.ιMulti W.functionField n fun i =>
        KaehlerDifferential.D k W.functionField
          (W.germToFunctionField (μ ⁻¹ᵁ V) (μ.app V (z i))) := by
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
  letI := MMP.Mori.functionFieldMapAlgebra μ
  haveI := MMP.Mori.isScalarTower_functionFieldMap sZ μ
  rw [MMP.Mori.topFormsMap_ιMulti]
  congr 1
  funext i
  rw [KaehlerDifferential.map_D]
  congr 1
  rw [Scheme.Hom.app_eq_appLE]
  exact functionFieldMap_germToFunctionField μ V (μ ⁻¹ᵁ V) le_rfl (z i)

end PullbackComp

/-- Base changes are compatible with scalar multiplication of coefficients. -/
public theorem IsBaseChange.smul {R S : Type*} [Zero R] [SMulZeroClass S R] {X₀ X : Scheme.{u}}
    {π : X ⟶ X₀} {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X}
    (hD : IsBaseChange π D₀ D) (c : S) : IsBaseChange π (c • D₀) (c • D) :=
  ⟨fun P₀ P hP => by simp [hD.1 P₀ P hP], fun P hP => hD.2 P fun h => hP (by simp [h])⟩

end Helpers

end MMP.ProgramBaseChange
