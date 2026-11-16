module

public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.FamilyLogarithm
import MMP.AlgebraicGeometry.Analytic.CornerPresentation
import MMP.AlgebraicGeometry.Analytic.ExponentialSequence
public import MMP.Attr

/-!
# Logarithmic coordinates on the analytic Picard group of a curve

Let `C` be a smooth projective connected curve over `ℂ` with a marked point, `A = C^an` its
analytification, and `0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0` the exponential sequence, `u ↦ exp (2πi u)`.
The first cohomology `H¹(A, 𝒪_A)` is a finite-dimensional complex vector space. The image of
`H¹(A, ℤ_A)` in it is a full lattice `Λ`. The exponential map
`H¹(A, 𝒪_A) → H¹(A, 𝒪_A^×) ≃ Pic(A)` has kernel `Λ`. Its image is the degree-zero part of
`Pic(A)`, the kernel of the obstruction map `Pic(A) → H²(A, ℤ_A)`. So the analytic degree-zero
Picard group is the compact complex torus `H¹(A, 𝒪_A) / Λ`. Moreover, the analytification of
the Jacobian `J` of `C` is uniformised by `H¹(A, 𝒪_A)`: there is a holomorphic map
`H¹(A, 𝒪_A) → J(ℂ)` that is biholomorphic near `0`. On the group `J(ℂ)` of rigidified
degree-zero classes it is a surjective homomorphism with kernel `Λ`.

## Main results

* `MMP.Conductor.exists_isZLattice_exponential_of_isProjective`: logarithmic coordinates on the
  analytic degree-zero Picard group and on the Jacobian of a pointed curve.

## Implementation notes

`H¹(A, 𝒪_A)` is the `Ext`-cohomology `Sheaf.H` of the additive sheaf of `𝒪_A`. That group
carries no `ℂ`-module instance, so the complex structure is given by an additive isomorphism
`φ : ℂⁿ ≃+ H¹(A, 𝒪_A)`, which intertwines scalar multiplication by `c` with `H¹` of the sheaf
endomorphism `m c` of `𝒪_A`. Here `m c` is multiplication by the constant `c`. The exponential
sequence is quantified over by the two formulas that determine its maps, as in
`MMP.Analytic.exact_picardObstruction_analytification`. These formulas determine the maps
(`MMP.JacobianLogarithm.eq_of_exponential_formulas`), so the short exactness of the sequence is
that of `MMP.Analytic.exists_shortExact_exponentialSequence`. The exponential map to `Pic(A)`
is `H¹` of `𝒪_A ⟶ 𝒪_A^×`, followed by the canonical isomorphism
`Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`.

The Jacobian is any abelian variety representing `Stacks.RigidifiedPicard.functorZero`, as in
`MMP.Conductor.exists_jacobian_of_isProjective`. A `ℂ`-point `x` of `J` gives the rigidified
class `e(x)`. A map `Φ` from `ℂⁿ` to `J(ℂ)` is holomorphic when, in every affine chart of `J`,
its coordinates are near each point those of a holomorphic map. Its inverse near `Φ 0` is
holomorphic in the same sense: in every chart it is locally a holomorphic function of the
coordinates.

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

/-- Multiplication `m c` by the constant `c` on `𝒪_{C^an}` is additive and multiplicative in
`c`, and `m 1` is the identity. -/
theorem smulConst_add_mul_one {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) :
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    ∀ (m : ℂ → (O ⟶ O)),
      (∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s) →
      (∀ a b : ℂ, m (a + b) = m a + m b) ∧ (∀ a b : ℂ, m (a * b) = m b ≫ m a) ∧ m 1 = 𝟙 O := by
  intro J O m hm
  refine ⟨fun a b => ?_, fun a b => ?_, ?_⟩
  · ext ⟨W⟩ s
    have h1 := hm (a + b) W s
    have h2 := hm a W s
    have h3 := hm b W s
    simp only at h1 h2 h3
    change ((m (a + b)).hom.app (op W)) s = (m a).hom.app (op W) s + (m b).hom.app (op W) s
    erw [h1, h2, h3]
    simp only [map_add]
    erw [map_add, map_add]
    exact add_mul (R := (Analytification.structureSheaf f).obj.obj (op W)) _ _ s
  · ext ⟨W⟩ s
    have h1 := hm (a * b) W s
    have h3 := hm b W s
    simp only at h1 h3
    change ((m (a * b)).hom.app (op W)) s = (m a).hom.app (op W) ((m b).hom.app (op W) s)
    have h2 := hm a W ((m b).hom.app (op W) s)
    simp only at h2
    erw [h1, h2, h3]
    simp only [map_mul]
    erw [map_mul, map_mul]
    exact mul_assoc (G := (Analytification.structureSheaf f).obj.obj (op W)) _ _ s
  · ext ⟨W⟩ s
    have h1 := hm 1 W s
    simp only at h1
    change ((m 1).hom.app (op W)) s = s
    erw [h1]
    simp only [map_one]
    erw [map_one, map_one]
    exact one_mul (M := (Analytification.structureSheaf f).obj.obj (op W)) s

/-- The kernel of the exponential map `H¹(A, 𝒪_A) → Pic(A)` is the image of `H¹(A, ℤ_A)`, and its
image is the kernel of the obstruction map: exactness of the long exact cohomology sequence of
`0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0` at `H¹(A, 𝒪_A)` and at `H¹(A, 𝒪_A^×)`. -/
theorem ker_range_expPic {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) [IsProper f] {n : ℕ} :
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification f)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∀ (i : ZA ⟶ O) (e : O ⟶ Ou) (w : i ≫ e = 0) (hS : (ShortComplex.mk i e w).ShortExact)
      (φ : (Fin n → ℂ) ≃+ Sheaf.H O 1),
      letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      let expPic :=
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
          (analytification f)).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) Ou)).symm.toAddMonoidHom.comp (Sheaf.H.map e 1))
      let Λ : Submodule ℤ (Fin n → ℂ) :=
        ((Sheaf.H.map i 1).range.comap φ.toAddMonoidHom).toIntSubmodule
      (expPic.comp φ.toAddMonoidHom).ker = Λ.toAddSubgroup ∧
        (expPic.comp φ.toAddMonoidHom).range = (picardObstruction (analytification f) hS).ker := by
  intro J O Ou ZA i e w hS φ
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  intro expPic Λ
  have hexq := Stacks.Thickenings.cohomology_exact_quotient hS 1
  refine ⟨?_, ?_⟩
  · ext x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, expPic, Λ,
      Submodule.toAddSubgroup_toIntSubmodule, AddSubgroup.mem_comap, AddMonoidHom.mem_range,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff]
    change _ ↔ φ x ∈ Set.range (Sheaf.H.map i 1)
    exact Stacks.Thickenings.cohomology_exact_middle hS 1 (φ x)
  · ext y
    let E' := (Stacks.Thickenings.sheafCohomologyOneExtEquiv (space f) Ou).addCommGroupIsoToAddEquiv
    let h1 := Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification f)
    have hob : picardObstruction (analytification f) hS y =
        Stacks.Thickenings.cohomologyBoundary hS 1 (E' (h1.symm y)) :=
      picardObstruction_apply _ hS y
    rw [AddMonoidHom.mem_ker, hob, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      change Stacks.Thickenings.cohomologyBoundary hS 1
        (E' (h1.symm (h1 (E'.symm (Sheaf.H.map e 1 (φ x)))))) = 0
      rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      exact hexq.apply_apply_eq_zero _
    · intro hy
      obtain ⟨z, hz⟩ := (hexq _).mp hy
      refine ⟨φ.symm z, ?_⟩
      change h1 (E'.symm (Sheaf.H.map e 1 (φ (φ.symm z)))) = y
      rw [AddEquiv.apply_symm_apply, show Sheaf.H.map e 1 z = E' (h1.symm y) from hz,
        AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

/-- A representative of the rigidified degree-zero Picard functor is proper over `ℂ`. -/
theorem isProper_jacobian {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    ∀ (JX : Grp (Over (Spec (.of ℂ)))),
      (yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ) →
      IsProper JX.X.hom := by
  have := hproj.isProper
  intro JX eJ
  obtain ⟨J0, e0, hab, -⟩ := MMP.Conductor.exists_jacobian_of_isProjective f hproj hdim σ hσ
  have : IsProper J0.X.hom := hab.toIsProperVariety.toIsProper
  let isoJ : JX.X ≅ J0.X :=
    (Grp.forget _).mapIso (yonedaGrpFullyFaithful.preimageIso (eJ ≪≫ e0.symm))
  rw [← Over.w isoJ.hom]
  infer_instance

/-- A representative of the rigidified degree-zero Picard functor is smooth over `ℂ` of relative
dimension `h¹(𝒪_C)`. -/
theorem smoothOfRelativeDimension_jacobian {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    ∀ (JX : Grp (Over (Spec (.of ℂ)))),
      (yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ) →
      SmoothOfRelativeDimension (Module.finrank ℂ (structureSheafCohomology f 1)) JX.X.hom := by
  have := hproj.isProper
  intro JX eJ
  obtain ⟨J0, e0, hab, -, hdimJ, -⟩ :=
    MMP.Conductor.exists_jacobian_of_isProjective f hproj hdim σ hσ
  have : Smooth J0.X.hom := smooth_of_isAbelianVariety ℂ J0.X
  have : Nonempty J0.X.left := ⟨(MonObj.one (X := J0.X)).left (IsLocalRing.closedPoint ℂ)⟩
  have : MMP.Mori.IsVariety ℂ J0.X.hom := hab.toIsProperVariety.toIsVariety
  have hK := Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J0.X
  rw [hdimJ] at hK
  have := MMP.Intersection.smoothOfRelativeDimension_of_isVariety J0.X.hom _ hK
  let isoJ : JX.X ≅ J0.X :=
    (Grp.forget _).mapIso (yonedaGrpFullyFaithful.preimageIso (eJ ≪≫ e0.symm))
  rw [← Over.w isoJ.hom]
  simpa using (inferInstance : SmoothOfRelativeDimension
    (0 + Module.finrank ℂ (structureSheafCohomology f 1)) (isoJ.hom.left ≫ J0.X.hom))

/-- For a representative `J` of the rigidified degree-zero Picard functor, `x ↦ e(x)` is a
bijection from `J(ℂ)` onto the group of rigidified classes. -/
theorem bijective_cls {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f)
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    ∀ (JX : Grp (Over (Spec (.of ℂ))))
      (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
    let cls : ComplexPoints JX.X.hom →
        (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
      fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
    Function.Bijective cls := by
  have := hproj.isProper
  intro JX eJ cls
  have hb := ConcreteCategory.bijective_of_isIso (eJ.hom.app (op (Over.mk (𝟙 _))))
  refine ⟨fun x y hxy => Subtype.ext (congrArg CommaMorphism.left (hb.1 hxy)), fun g => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 g
  refine ⟨⟨a.left, by simpa using Over.w a⟩, ?_⟩
  refine Eq.trans ?_ ha
  change (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk a.left _) = _
  congr 1

/-- The `ℂ`-points of a representative `J` of the rigidified degree-zero Picard functor form a
connected space. -/
theorem connectedSpace_space_jacobian {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    ∀ (JX : Grp (Over (Spec (.of ℂ)))),
      (yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ) →
      ConnectedSpace (space JX.X.hom) := by
  have := hproj.isProper
  intro JX eJ
  obtain ⟨J0, e0, hab, -⟩ := MMP.Conductor.exists_jacobian_of_isProjective f hproj hdim σ hσ
  let isoJ : JX.X ≅ J0.X :=
    (Grp.forget _).mapIso (yonedaGrpFullyFaithful.preimageIso (eJ ≪≫ e0.symm))
  let g' := ComplexPoints.realize isoJ.inv.left (Over.w isoJ.inv)
  obtain ⟨y0, -⟩ := (bijective_cls f hproj hdim σ hσ JX eJ).2 1
  have := connectedSpace_space_of_isProjective J0.X.hom
    (isProjective_of_isAbelianVariety ℂ J0.X)
    (ComplexPoints.realize isoJ.hom.left (Over.w isoJ.hom) y0)
  have hg : ∀ y, g' (ComplexPoints.realize isoJ.hom.left (Over.w isoJ.hom) y) = y := by
    intro y
    apply Subtype.ext
    change (y.1 ≫ isoJ.hom.left) ≫ isoJ.inv.left = y.1
    rw [Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]
  exact (Function.LeftInverse.surjective hg).connectedSpace
    (ComplexPoints.continuous_realize isoJ.inv.left (Over.w isoJ.inv))

/-- **The group of `ℂ`-points of the Jacobian.** For a representative `J` of the rigidified
degree-zero Picard functor, `x ↦ e(x)` is a bijection from `J(ℂ)` onto the group of rigidified
classes, `J(ℂ)` is connected, and the translations of `J(ℂ)` are continuous open maps covering
multiplication, preserving holomorphy, and rational in the charts. -/
theorem jacobian_points_translations {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) (n : ℕ) :
    haveI := hproj.isProper
    ∀ (JX : Grp (Over (Spec (.of ℂ))))
      (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
    let cls : ComplexPoints JX.X.hom →
        (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
      fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
    Function.Bijective cls ∧ ConnectedSpace (space JX.X.hom) ∧
    ∃ τ : space JX.X.hom → space JX.X.hom → space JX.X.hom,
      (∀ t y, cls (τ t y) = cls t * cls y) ∧ (∀ t, Continuous (τ t)) ∧
      (∀ t, IsOpenMap (τ t)) ∧
      (∀ t (F : (Fin n → ℂ) → space JX.X.hom) v,
        ChartHolomorphicAt F v → ChartHolomorphicAt (τ t ∘ F) v) ∧
      ∀ t (d c : Chart JX.X.hom) (x : space JX.X.hom) (hx : x ∈ chart d.U)
        (_ : τ t x ∈ chart c.U),
        ∃ (R : (Fin d.n → ℂ) → (Fin c.n → ℂ)) (Q : MvPolynomial (Fin d.n) ℂ),
          MvPolynomial.eval (d.coords ⟨x, hx⟩) Q ≠ 0 ∧
          (∀ z, MvPolynomial.eval z Q ≠ 0 → DifferentiableAt ℂ R z) ∧
          ∀ (y : space JX.X.hom) (hy : y ∈ chart d.U),
            MvPolynomial.eval (d.coords ⟨y, hy⟩) Q ≠ 0 →
            ∃ h' : τ t y ∈ chart c.U, c.coords ⟨τ t y, h'⟩ = R (d.coords ⟨y, hy⟩) := by
  have := hproj.isProper
  intro JX eJ cls
  have hclsb : Function.Bijective cls := bijective_cls f hproj hdim σ hσ JX eJ
  refine ⟨hclsb, connectedSpace_space_jacobian f hproj hdim σ hσ JX eJ, ?_⟩
  have : IsProper JX.X.hom := isProper_jacobian f hproj hdim σ hσ JX eJ
  let P : Over (Spec (.of ℂ)) := Over.mk (𝟙 _)
  let pt : space JX.X.hom → (P ⟶ JX.X) := fun x => Over.homMk x.1 x.2
  let T : space JX.X.hom → (JX.X ⟶ JX.X) := fun t =>
    (Over.homMk (JX.X.hom ≫ t.1) (by rw [Category.assoc, t.2, Category.comp_id]) :
      JX.X ⟶ JX.X) * 𝟙 JX.X
  let τ : space JX.X.hom → space JX.X.hom → space JX.X.hom := fun t =>
    ComplexPoints.realize (T t).left (Over.w (T t))
  have hτ : ∀ t y, cls (τ t y) = cls t * cls y := by
    intro t y
    have h1 : pt (τ t y) = pt y ≫ T t := Over.OverMorphism.ext rfl
    have h2 : pt y ≫ (Over.homMk (JX.X.hom ≫ t.1)
        (by rw [Category.assoc, t.2, Category.comp_id]) : JX.X ⟶ JX.X) = pt t :=
      Over.OverMorphism.ext (by
        change y.1 ≫ JX.X.hom ≫ t.1 = t.1
        rw [← Category.assoc, y.2, Category.id_comp])
    have h3 : pt y ≫ T t = pt t * pt y := by
      rw [MonObj.comp_mul, h2, Category.comp_id]
    change (eJ.hom.app (op P)).hom (pt (τ t y)) =
      (eJ.hom.app (op P)).hom (pt t) * (eJ.hom.app (op P)).hom (pt y)
    rw [h1, h3]
    exact (eJ.hom.app (op P)).hom.map_mul (pt t) (pt y)
  refine ⟨τ, hτ, fun t => ComplexPoints.continuous_realize _ _, fun t => ?_,
    fun t F v hF => hF.realize _ _,
    fun t d c x hx hgx => exists_rational_coords_realize _ _ d c x hx hgx⟩
  obtain ⟨s, hs⟩ := hclsb.2 (cls t)⁻¹
  have h1 : ∀ y, τ s (τ t y) = y := fun y =>
    hclsb.1 (by rw [hτ s, hτ t, hs, inv_mul_cancel_left])
  have h2 : ∀ y, τ t (τ s y) = y := fun y =>
    hclsb.1 (by rw [hτ t, hτ s, hs, mul_inv_cancel_left])
  exact (Homeomorph.mk ⟨τ t, τ s, h1, h2⟩
    (ComplexPoints.continuous_realize (T t).left (Over.w (T t)))
    (ComplexPoints.continuous_realize (T s).left (Over.w (T s)))).isOpenMap

/-- The first projection `C ×_ℂ ℂ ⟶ C` followed by `x ↦ (x, f x)` is the identity of `C ×_ℂ ℂ`. -/
theorem pullback_fst_comp_lift_id {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) :
    Limits.pullback.fst f (Over.mk (𝟙 (Spec (.of ℂ)))).hom ≫
      (Limits.pullback.lift (𝟙 C) f (by simp) :
        C ⟶ Stacks.RigidifiedPicard.bc f (Over.mk (𝟙 _))) = 𝟙 _ := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
    exact Limits.pullback.condition.trans (Category.comp_id _)

/-- Base change of the section `C → C ×_ℂ ℂ` along a `ℂ`-point `y` of `X` is the slice at `y`. -/
theorem lift_id_comp_bcMap {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) (X : Over (Spec (.of ℂ)))
    (y : ComplexPoints X.hom) :
    (Limits.pullback.lift (𝟙 C) f (by simp) :
        C ⟶ Stacks.RigidifiedPicard.bc f (Over.mk (𝟙 _))) ≫
      Stacks.RigidifiedPicard.bcMap f (Over.homMk y.1 y.2 : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X) =
      Fam.sliceAt f X.hom y := by
  apply Limits.pullback.hom_ext
  · simp only [Fam.sliceAt, Stacks.RigidifiedPicard.bcMap, Category.assoc,
      Limits.pullback.lift_fst, Limits.pullback.map]
    rw [Category.comp_id]
    exact Limits.pullback.lift_fst _ _ _
  · simp only [Fam.sliceAt, Stacks.RigidifiedPicard.bcMap, Category.assoc,
      Limits.pullback.lift_snd, Limits.pullback.map]
    rw [← Category.assoc]
    erw [Limits.pullback.lift_snd]
    rfl

/-- Pulling back line bundle classes along the section `C → C ×_ℂ ℂ` of the first projection is
injective. -/
theorem injective_schemePullbackClass_lift {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) :
    Function.Injective (Stacks.Picard.schemePullbackClass
      (Limits.pullback.lift (𝟙 C) f (by simp) :
        C ⟶ Stacks.RigidifiedPicard.bc f (Over.mk (𝟙 (Spec (.of ℂ)))))) := by
  intro x y h
  have h' := congrArg (Stacks.Picard.schemePullbackClass
    (Limits.pullback.fst f (Over.mk (𝟙 (Spec (.of ℂ)))).hom)) h
  rwa [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    pullback_fst_comp_lift_id, Stacks.Picard.schemePullbackClass_id,
    Stacks.Picard.schemePullbackClass_id] at h'

/-- Restriction along the section `C → C ×_ℂ ℂ` followed by the GAGA comparison is an injective
homomorphism `ι` from the rigidified degree-zero classes over `ℂ` to the analytic Picard group of
`C^an`; it sends a class restricting to the class of `L` on `C` to the analytic class of `L^an`. -/
theorem exists_injective_toAnalyticPicard {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f)
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    ∃ ι : Multiplicative (Stacks.RigidifiedPicard.groupZero f hdim σ hσ (Over.mk (𝟙 _))) →*
        Multiplicative (Additive (Stacks.SheafPicardGroup.PicardGroup
          (J := Opens.grothendieckTopology (space f)) (structureSheaf f).obj (ringCatSheaf f).2)),
      Function.Injective ι ∧
      ∀ (x : Stacks.RigidifiedPicard.groupZero f hdim σ hσ (Over.mk (𝟙 _)))
        (Lm : SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf C.toRingedSpace))
        (hLm : Stacks.SheafOfModules.IsInvertible C.presheaf _ Lm)
        (hy : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
          (structureSheaf (analytification f : RingedSpace).sheaf).property
          ((RingedSpaceModuleAdjunction.modulePullback (X := (analytification f : RingedSpace))
            (Y := C.toRingedSpace) (analytificationHom f)).obj Lm)),
        Stacks.Picard.schemePullbackClass (Limits.pullback.lift (𝟙 C) f (by simp) :
            C ⟶ Stacks.RigidifiedPicard.bc f (Over.mk (𝟙 _)))
            (Stacks.RigidifiedPicard.smallEquiv _ x.1.1) =
          Stacks.SheafOfModules.picardClass C.presheaf _ Lm hLm →
        ι (Multiplicative.ofAdd x) = Multiplicative.ofAdd (ringedPicardToSheafPicardHom
          (analytification f) (Stacks.SheafOfModules.Picard.classOf _ _ _ hy)) := by
  have := hproj.isProper
  obtain ⟨hinvG, eG, heG, -⟩ := exists_mulEquiv_picardGroup_analytification_of_isProjective f hproj
  let P1 : Over (Spec (.of ℂ)) := Over.mk (𝟙 _)
  let g : C ⟶ Stacks.RigidifiedPicard.bc f P1 := Limits.pullback.lift (𝟙 C) f (by simp [P1])
  let H := Stacks.RigidifiedPicard.groupZero f hdim σ hσ P1
  let ιadd : H →+ Additive (Stacks.SheafPicardGroup.PicardGroup
      (J := Opens.grothendieckTopology (space f)) (structureSheaf f).obj (ringCatSheaf f).2) :=
    (MulEquiv.toAdditive eG).toAddMonoidHom.comp
      ((toSheafPicardHom C.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)).comp
        ((Stacks.Picard.schemePullbackClassHom g).comp
          ((Stacks.RigidifiedPicard.smallEquiv _).toAddMonoidHom.comp
            ((Stacks.RigidifiedPicard.group f σ hσ P1).subtype.comp H.subtype))))
  have hιadd : Function.Injective ιadd := fun x y hxy => by
    have h := toSheafPicardHom_injective _ _ ((MulEquiv.toAdditive eG).injective hxy)
    change Stacks.Picard.schemePullbackClass g _ = Stacks.Picard.schemePullbackClass g _ at h
    exact Subtype.ext (Subtype.ext ((Stacks.RigidifiedPicard.smallEquiv _).injective
      (injective_schemePullbackClass_lift f h)))
  refine ⟨AddMonoidHom.toMultiplicative ιadd, fun x y h =>
    Multiplicative.toAdd.injective (hιadd (congrArg Multiplicative.toAdd h)),
    fun x Lm hLm hy hx => ?_⟩
  have hx' : Stacks.Picard.schemePullbackClass g (Stacks.RigidifiedPicard.smallEquiv _ x.1.1) =
      Stacks.SheafOfModules.picardClass C.presheaf _ Lm hLm := hx
  have h4 : ιadd x = Additive.ofMul (eG (Stacks.SheafPicardGroup.schemeClassOf C Lm)) := by
    change Additive.ofMul (eG (Additive.toMul (toSheafPicardHom C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
      (Stacks.Picard.schemePullbackClass g (Stacks.RigidifiedPicard.smallEquiv _ x.1.1))))) = _
    rw [hx']
    change Additive.ofMul (eG (Additive.toMul (toSheafPicard C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
      (Stacks.SheafOfModules.picardClass C.presheaf _ Lm hLm)))) = _
    exact (congrArg (fun z => Additive.ofMul (eG (Additive.toMul z)))
      (toSheafPicard_picardClass C.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) Lm hLm)).trans rfl
  change Multiplicative.ofAdd (ιadd x) = Multiplicative.ofAdd (picardToSheafPicard _ _ _)
  rw [h4, heG Lm]
  exact congrArg Multiplicative.ofAdd (picardToSheafPicard_classOf
    (analytification f : RingedSpace).sheaf.obj
    (structureSheaf (analytification f : RingedSpace).sheaf).property _ hy).symm

/-- For a representative `J` of the rigidified degree-zero Picard functor, there are an injective
homomorphism `ι` from the rigidified classes to the analytic Picard group of `C^an` and an
invertible sheaf `M` on `C × J` such that `ι (e(y))` is the analytic class of the slice of `M` at
`y`, for every `y ∈ J(ℂ)`. -/
theorem exists_injective_eq_classOf_slice {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    ∀ (JX : Grp (Over (Spec (.of ℂ))))
      (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
      let cls : ComplexPoints JX.X.hom →
          (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
        fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
      ∃ ι : Multiplicative (Stacks.RigidifiedPicard.groupZero f hdim σ hσ (Over.mk (𝟙 _))) →*
          Multiplicative (Additive (Stacks.SheafPicardGroup.PicardGroup
            (J := Opens.grothendieckTopology (space f)) (structureSheaf f).obj (ringCatSheaf f).2)),
        Function.Injective ι ∧
        ∃ M : SheafOfModules.{0}
            (Stacks.RingedSpace.structureRingSheaf (Limits.pullback f JX.X.hom).toRingedSpace),
          Stacks.SheafOfModules.IsInvertible
            (Limits.pullback f JX.X.hom).toRingedSpace.sheaf.obj _ M ∧
          ∀ (y : space JX.X.hom) (hy : Stacks.SheafOfModules.IsInvertible
              (analytification f : RingedSpace).sheaf.obj
              (structureSheaf (analytification f : RingedSpace).sheaf).property
              ((RingedSpaceModuleAdjunction.modulePullback (X := (analytification f : RingedSpace))
                (Y := C.toRingedSpace) (analytificationHom f)).obj
                ((RingedSpaceModuleAdjunction.modulePullback
                  (Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom).obj M))),
            ι (cls y) = Multiplicative.ofAdd (ringedPicardToSheafPicardHom (analytification f)
              (Stacks.SheafOfModules.Picard.classOf _ _ _ hy)) := by
  have := hproj.isProper
  intro JX eJ cls
  have : IsProper JX.X.hom := isProper_jacobian f hproj hdim σ hσ JX eJ
  obtain ⟨ι, hι, hιL⟩ := exists_injective_toAnalyticPicard f hproj hdim σ hσ
  let Puniv := (eJ.hom.app (op JX.X)).hom (𝟙 JX.X)
  obtain ⟨M, hM, hMu⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _
    (Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd Puniv).1.1)
  have hM' : Stacks.SheafOfModules.IsInvertible
      (Limits.pullback f JX.X.hom).toRingedSpace.sheaf.obj _ M := hM
  refine ⟨ι, hι, M, hM', fun y hy => ?_⟩
  let yy : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X := Over.homMk y.1 y.2
  have hP : cls y = ((Stacks.RigidifiedPicard.functorZero f hdim σ hσ).map yy.op).hom Puniv := by
    have h := ConcreteCategory.congr_hom (eJ.hom.naturality yy.op) (𝟙 JX.X)
    refine Eq.trans ?_ h
    change (eJ.hom.app _).hom yy = (eJ.hom.app _).hom (yy ≫ 𝟙 JX.X)
    rw [Category.comp_id]
  have h1 : (Multiplicative.toAdd (cls y)).1.1 = Stacks.Picard.smallSchemePullbackClassHom
      (Stacks.RigidifiedPicard.bcMap f yy) (Multiplicative.toAdd Puniv).1.1 := by
    rw [hP]
    rfl
  let Lm := (RingedSpaceModuleAdjunction.modulePullback
    (Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom).obj M
  have hLm : Stacks.SheafOfModules.IsInvertible C.presheaf _ Lm :=
    Stacks.RingedSpace.isInvertible_modulePullback _ _
  refine hιL (Multiplicative.toAdd (cls y)) Lm hLm hy ?_
  rw [show (Multiplicative.toAdd (cls y) :
      Stacks.RigidifiedPicard.groupZero f hdim σ hσ (Over.mk (𝟙 _))).1.1 = _ from h1,
    Stacks.RigidifiedPicard.smallEquiv_smallSchemePullbackClassHom, ← hMu,
    Stacks.Picard.schemePullbackClass_comp, lift_id_comp_bcMap f JX.X y]
  exact Stacks.Picard.pullbackClass_classOf _ M hM

/-- **Local logarithm on the Jacobian.** If an injective homomorphism `ι` sends `e(y)` to the
analytic class of the slice at `y` of an invertible sheaf `M` on `C × J`, then on an open set of
an étale coordinate chart of `J`, `ι ∘ e` is the exponential map composed with a holomorphic map
`L`. -/
theorem exists_localLog_of_eq_classOf_slice {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification f)
    ∀ (e : O ⟶ Ou),
      (∀ (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)) (x : W)
        (c : {c : Chart f // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf f).obj.obj (op W))ˣ) :
          (structureSheaf f).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') →
      ∀ (m : ℂ → (O ⟶ O)),
      (∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s) →
      ∀ {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H O 1),
      (∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v)) →
      n = Module.finrank ℂ (structureSheafCohomology f 1) →
      letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      let expPic :=
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
          (analytification f)).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) Ou)).symm.toAddMonoidHom.comp (Sheaf.H.map e 1))
      let E := (ringedPicardToSheafPicardHom (analytification f)).comp
        (expPic.comp φ.toAddMonoidHom)
      ∀ (JX : Grp (Over (Spec (.of ℂ))))
      (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
      let cls : ComplexPoints JX.X.hom →
          (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
        fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
      ∀ (ι : Multiplicative (Stacks.RigidifiedPicard.groupZero f hdim σ hσ (Over.mk (𝟙 _))) →*
          Multiplicative (Additive (Stacks.SheafPicardGroup.PicardGroup
            (J := Opens.grothendieckTopology (space f)) (structureSheaf f).obj (ringCatSheaf f).2)))
        (M : SheafOfModules.{0}
          (Stacks.RingedSpace.structureRingSheaf (Limits.pullback f JX.X.hom).toRingedSpace))
        (_ : Stacks.SheafOfModules.IsInvertible
          (Limits.pullback f JX.X.hom).toRingedSpace.sheaf.obj _ M),
        (∀ (y : space JX.X.hom) (hy : Stacks.SheafOfModules.IsInvertible
            (analytification f : RingedSpace).sheaf.obj
            (structureSheaf (analytification f : RingedSpace).sheaf).property
            ((RingedSpaceModuleAdjunction.modulePullback (X := (analytification f : RingedSpace))
              (Y := C.toRingedSpace) (analytificationHom f)).obj
              ((RingedSpaceModuleAdjunction.modulePullback
                (Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom).obj M))),
          ι (cls y) = Multiplicative.ofAdd (ringedPicardToSheafPicardHom (analytification f)
            (Stacks.SheafOfModules.Picard.classOf _ _ _ hy))) →
      ∃ (c : ComplexPoints.EtaleCoordinateChart JX.X.hom n)
        (L : (Fin n → ℂ) → (Fin n → ℂ))
        (Ω : Set (Fin n → ℂ)), IsOpen Ω ∧ ContDiffOn ℂ 1 L Ω ∧
        (∃ y ∈ c.W, c.toOpenPartialHomeomorph y ∈ Ω) ∧
        ∀ y ∈ c.W, c.toOpenPartialHomeomorph y ∈ Ω →
          ι (cls y) = Multiplicative.ofAdd (E (L (c.toOpenPartialHomeomorph y))) := by
  have := hproj.isProper
  intro J O Ou e he m hm n φ hφ hrank
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  intro expPic E JX eJ cls ι M hM hkey
  obtain ⟨hmadd, hmmul, -⟩ := smulConst_add_mul_one f m hm
  have hclsb : Function.Bijective cls := bijective_cls f hproj hdim σ hσ JX eJ
  have : IsProper JX.X.hom := isProper_jacobian f hproj hdim σ hσ JX eJ
  have : SmoothOfRelativeDimension n JX.X.hom := by
    rw [hrank]
    exact smoothOfRelativeDimension_jacobian f hproj hdim σ hσ JX eJ
  have hinvy : ∀ y : space JX.X.hom, Stacks.SheafOfModules.IsInvertible
      (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((RingedSpaceModuleAdjunction.modulePullback (X := (analytification f : RingedSpace))
        (Y := C.toRingedSpace) (analytificationHom f)).obj
        ((RingedSpaceModuleAdjunction.modulePullback
          (Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom).obj M)) := by
    intro y
    have := Stacks.RingedSpace.isInvertible_modulePullback
      ((Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom) M
    exact Stacks.RingedSpace.isInvertible_modulePullback _ _
  have hsc : ∀ y : space JX.X.hom, Fam.sliceClass f JX.X.hom M hM y =
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification f)).symm
        (Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy y)) := fun y =>
    (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf _ _ _).symm
  obtain ⟨e₀, he₀1⟩ := hclsb.2 1
  have he₀ : Fam.sliceClass f JX.X.hom M hM e₀ = 0 := by
    have h1 := hkey e₀ (hinvy e₀)
    have h0 : ι (cls e₀) = 1 := by
      rw [he₀1]
      exact map_one ι
    rw [h0] at h1
    have h2 : ringedPicardToSheafPicardHom (analytification f)
        (Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy e₀)) = 0 :=
      congrArg Multiplicative.toAdd h1.symm
    have h3 : Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy e₀) = 0 :=
      (ringedPicardToSheafPicardHom_injective (analytification f)) (h2.trans (map_zero _).symm)
    rw [hsc, h3, map_zero]
  obtain ⟨c, L, Ω, hΩ, hLd, he₀W, he₀Ω, hfam⟩ :=
    Fam.exists_etaleCoordinateChart_sliceClass_eq f JX.X.hom M hM e₀ he₀ e he m hm hmadd hmmul φ hφ
  refine ⟨c, L, Ω, hΩ, hLd, ⟨e₀, he₀W, he₀Ω⟩, fun y hy hyΩ => ?_⟩
  rw [hkey y (hinvy y)]
  congr 1
  have h5 : Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy y) =
      Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification f)
        ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
          (space f) Ou)).symm (Sheaf.H.map e 1 (φ (L (c.toOpenPartialHomeomorph y))))) := by
    rw [← (hsc y).symm.trans (hfam y hy hyΩ), AddEquiv.apply_symm_apply]
  rw [h5]
  rfl

/-- **Uniformisation from a local logarithm.** If an injective homomorphism `ι` turns the
classes `e(y)` into the exponential map composed with a holomorphic map `L` on an open set of an
étale chart of `J`, then the exponential map uniformises `J(ℂ)` as in
`exists_uniformisation_jacobian`. -/
theorem exists_uniformisation_of_localLog {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification f)
    ∀ (e : O ⟶ Ou),
      ∀ {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H O 1),
      n = Module.finrank ℂ (structureSheafCohomology f 1) →
      letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      let expPic :=
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
          (analytification f)).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) Ou)).symm.toAddMonoidHom.comp (Sheaf.H.map e 1))
      ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (expPic.comp φ.toAddMonoidHom).ker = Λ.toAddSubgroup →
      ∀ (JX : Grp (Over (Spec (.of ℂ))))
      (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
      let cls : ComplexPoints JX.X.hom →
          (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
        fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
      ∀ (ι : Multiplicative (Stacks.RigidifiedPicard.groupZero f hdim σ hσ (Over.mk (𝟙 _))) →*
          Multiplicative (Additive (Stacks.SheafPicardGroup.PicardGroup
            (J := Opens.grothendieckTopology (space f)) (structureSheaf f).obj
            (ringCatSheaf f).2))),
        Function.Injective ι →
      let E := (ringedPicardToSheafPicardHom (analytification f)).comp
        (expPic.comp φ.toAddMonoidHom)
      ∀ (c : ComplexPoints.EtaleCoordinateChart JX.X.hom n) (L : (Fin n → ℂ) → (Fin n → ℂ))
        (Ω : Set (Fin n → ℂ)), IsOpen Ω → ContDiffOn ℂ 1 L Ω →
        (∃ y ∈ c.W, c.toOpenPartialHomeomorph y ∈ Ω) →
        (∀ y ∈ c.W, c.toOpenPartialHomeomorph y ∈ Ω →
          ι (cls y) = Multiplicative.ofAdd (E (L (c.toOpenPartialHomeomorph y)))) →
      ∃ Φ : (Fin n → ℂ) → space JX.X.hom, Continuous Φ ∧
        (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ ComplexPoints.chart c.U),
          ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
            ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ ComplexPoints.chart c.U, c.coords ⟨Φ v', h'⟩ = F v') ∧
        (∃ U : Set (Fin n → ℂ), IsOpen U ∧ 0 ∈ U ∧ ∃ V : Opens (space JX.X.hom),
          Set.BijOn Φ U V ∧ ∃ Ψ : space JX.X.hom → (Fin n → ℂ), Set.LeftInvOn Ψ Φ U ∧
            ∀ (y : space JX.X.hom) (_ : y ∈ V) (c : Chart JX.X.hom)
              (hy : y ∈ ComplexPoints.chart c.U),
              ∃ G : (Fin c.n → ℂ) → (Fin n → ℂ), DifferentiableAt ℂ G (c.coords ⟨y, hy⟩) ∧
                ∀ᶠ y' in 𝓝 y, ∀ hy' : y' ∈ ComplexPoints.chart c.U, y' ∈ V →
                  Ψ y' = G (c.coords ⟨y', hy'⟩)) ∧
        (∀ v v', cls (Φ (v + v')) = cls (Φ v) * cls (Φ v')) ∧
        (∀ v, cls (Φ v) = 1 ↔ v ∈ Λ) ∧
        Function.Surjective (cls ∘ Φ) ∧ IsOpenMap Φ := by
  have := hproj.isProper
  intro J O Ou e n φ hrank
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  intro expPic Λ hker JX eJ cls ι hι E c L Ω hΩ hLd hne hlog
  obtain ⟨hclsb, hconn, τ, hτ, hτc, hτo, hτh, hτr⟩ :=
    jacobian_points_translations f hproj hdim σ hσ n JX eJ
  replace hclsb : Function.Bijective cls := hclsb
  replace hτ : ∀ t y, cls (τ t y) = cls t * cls y := hτ
  have hE : ∀ v, E v = 0 ↔ v ∈ Λ := by
    intro v
    change ringedPicardToSheafPicardHom (analytification f) _ = 0 ↔ _
    refine (map_eq_zero_iff _ (ringedPicardToSheafPicardHom_injective _)).trans ?_
    rw [← AddMonoidHom.mem_ker, hker]
    rfl
  have : SmoothOfRelativeDimension n JX.X.hom := by
    rw [hrank]
    exact smoothOfRelativeDimension_jacobian f hproj hdim σ hσ JX eJ
  have : Smooth JX.X.hom := SmoothOfRelativeDimension.smooth n JX.X.hom
  obtain ⟨Φ0, U, hU, h0, hΦ0, hc, ho, hh, V, hbij, Ψ, hinv, hΨ⟩ :=
    exists_localExp_of_localLog cls hclsb ι hι E τ hτ hτc hτo hτh hτr c L Ω hΩ hLd hne hlog
  obtain ⟨Φ, hΦc, hΦh, hΦeq, hΦo, hΦhom, hΦker, hΦs⟩ :=
    exists_uniformisation_of_localExp cls hclsb ι hι E
      ChartHolomorphicAt (fun _ _ _ h hF => hF.congr h) (fun _ _ _ hF => hF.comp_sub)
      τ hτ hτc hτo hτh Φ0 U hU h0 hΦ0 hc ho hh
  refine ⟨Φ, hΦc, hΦh, ⟨U, hU, h0, V, hbij.congr hΦeq.symm, Ψ,
    fun x hx => hΦeq hx ▸ hinv hx, hΨ⟩, hΦhom, fun v => (hΦker v).trans (hE v), hΦs, hΦo⟩

/-- **The exponential uniformisation of the Jacobian.** For any representative `J` of the
rigidified degree-zero Picard functor, a `ℂ`-linear coordinate system `φ : ℂⁿ ≃ H¹(C^an, 𝒪)`
with `n = h¹(𝒪_C)` gives a holomorphic open map `Φ : ℂⁿ → J(ℂ)`, biholomorphic near `0`, such
that `v ↦ e(Φ v)` is a surjective homomorphism onto the rigidified classes with kernel the kernel
`Λ` of the exponential map. -/
theorem exists_uniformisation_jacobian {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification f)
    ∀ (e : O ⟶ Ou),
      (∀ (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)) (x : W)
        (c : {c : Chart f // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf f).obj.obj (op W))ˣ) :
          (structureSheaf f).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') →
      ∀ (m : ℂ → (O ⟶ O)),
      (∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s) →
      ∀ {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H O 1),
      (∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v)) →
      n = Module.finrank ℂ (structureSheafCohomology f 1) →
      letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      let expPic :=
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
          (analytification f)).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) Ou)).symm.toAddMonoidHom.comp (Sheaf.H.map e 1))
      ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (expPic.comp φ.toAddMonoidHom).ker = Λ.toAddSubgroup →
      ∀ (JX : Grp (Over (Spec (.of ℂ))))
      (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
      let cls : ComplexPoints JX.X.hom →
          (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
        fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
      ∃ Φ : (Fin n → ℂ) → space JX.X.hom, Continuous Φ ∧
        (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ ComplexPoints.chart c.U),
          ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
            ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ ComplexPoints.chart c.U, c.coords ⟨Φ v', h'⟩ = F v') ∧
        (∃ U : Set (Fin n → ℂ), IsOpen U ∧ 0 ∈ U ∧ ∃ V : Opens (space JX.X.hom),
          Set.BijOn Φ U V ∧ ∃ Ψ : space JX.X.hom → (Fin n → ℂ), Set.LeftInvOn Ψ Φ U ∧
            ∀ (y : space JX.X.hom) (_ : y ∈ V) (c : Chart JX.X.hom)
              (hy : y ∈ ComplexPoints.chart c.U),
              ∃ G : (Fin c.n → ℂ) → (Fin n → ℂ), DifferentiableAt ℂ G (c.coords ⟨y, hy⟩) ∧
                ∀ᶠ y' in 𝓝 y, ∀ hy' : y' ∈ ComplexPoints.chart c.U, y' ∈ V →
                  Ψ y' = G (c.coords ⟨y', hy'⟩)) ∧
        (∀ v v', cls (Φ (v + v')) = cls (Φ v) * cls (Φ v')) ∧
        (∀ v, cls (Φ v) = 1 ↔ v ∈ Λ) ∧
        Function.Surjective (cls ∘ Φ) ∧ IsOpenMap Φ := by
  have := hproj.isProper
  intro J O Ou e he m hm n φ hφ hrank
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  intro expPic Λ hker JX eJ
  obtain ⟨ι, hι, M, hM, hkey⟩ := exists_injective_eq_classOf_slice f hproj hdim σ hσ JX eJ
  obtain ⟨c, L, Ω, hΩ, hLd, hne, hlog⟩ := exists_localLog_of_eq_classOf_slice f hproj hdim σ hσ
    e he m hm φ hφ hrank JX eJ ι M hM hkey
  exact exists_uniformisation_of_localLog f hproj hdim σ hσ e φ hrank Λ hker JX eJ ι hι
    c L Ω hΩ hLd hne hlog

/-- The two maps of the exponential sequence are determined by their defining formulas: a map
`ℤ_A ⟶ 𝒪_A` is determined by its values on the constant sections, since `ℤ_A` is the
sheafification of the constant presheaf, and a map `𝒪_A ⟶ 𝒪_A^×` sending the class of every
holomorphic germ `g` to the class of `exp (2πi g)` is determined componentwise. -/
theorem eq_of_exponential_formulas {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    let J := Opens.grothendieckTopology (space sX)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∀ (i i' : ZA ⟶ O) (e e' : O ⟶ Ou),
      (∀ (W : Opens (space sX)) (n : ℤ),
        (show (structureSheaf sX).obj.obj (op W) from i.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
      (∀ (W : Opens (space sX)) (n : ℤ),
        (show (structureSheaf sX).obj.obj (op W) from i'.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
      (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
        (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
          (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') →
      (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
        (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e'.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
          (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') →
      i = i' ∧ e = e' := by
  intro J O Ou ZA i i' e e' hi hi' he he'
  refine ⟨?_, ?_⟩
  · apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ O.property
    ext W n
    exact (hi W.unop n).trans (hi' W.unop n).symm
  · apply Sheaf.hom_ext
    ext W s
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    funext x c
    obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective (s.1 x c)
    obtain ⟨g, hg, hd⟩ := γ.2
    let γ' : holGerms (c.1.coords ⟨x.1, c.2⟩) :=
      ⟨((fun z => Complex.exp (2 * Real.pi * Complex.I * g z) : (Fin c.1.n → ℂ) → ℂ) :
          Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ),
        coe_mem_holGerms (hd.mono fun y hy => ((hy.const_mul _).cexp))⟩
    exact (he W.unop s x c g γ γ' hg.symm rfl hγ.symm).trans
      (he' W.unop s x c g γ γ' hg.symm rfl hγ.symm).symm

/-- `H¹(A, 𝒪_A)` has `ℂ`-linear coordinates: an additive isomorphism `ℂⁿ ≃+ H¹(A, 𝒪_A)` with
`n = h¹(𝒪_C)` that intertwines scalar multiplication by `a` with `H¹` of multiplication by the
constant `a`. -/
theorem exists_linear_coords_H1 {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) :
    haveI := hproj.isProper
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    ∀ (m : ℂ → (O ⟶ O)),
      (∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s) →
      ∃ (n : ℕ) (φ : (Fin n → ℂ) ≃+ Sheaf.H O 1),
        (∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v)) ∧
        n = Module.finrank ℂ (structureSheafCohomology f 1) := by
  have := hproj.isProper
  intro J O m hm
  obtain ⟨hmadd, hmmul, hmone⟩ := smulConst_add_mul_one f m hm
  have hmzero : ∀ x : Sheaf.H O 1, Sheaf.H.map (m 0) 1 x = 0 := by
    intro x
    have h := Sheaf.H.map_add_apply (m 0) (m 0) x
    rw [← hmadd, add_zero] at h
    exact left_eq_add.mp h
  letI hmod : Module ℂ (Sheaf.H O 1) :=
    { smul := fun a x => Sheaf.H.map (m a) 1 x
      one_smul := fun x => by
        change Sheaf.H.map (m 1) 1 x = x
        rw [hmone, Sheaf.H.map_id_apply]
      mul_smul := fun a b x => by
        change Sheaf.H.map (m (a * b)) 1 x = Sheaf.H.map (m a) 1 (Sheaf.H.map (m b) 1 x)
        rw [hmmul, Sheaf.H.map_comp_apply]
      smul_zero := fun a => map_zero (Sheaf.H.map (m a) 1)
      smul_add := fun a x y => map_add (Sheaf.H.map (m a) 1) x y
      add_smul := fun a b x => by
        change Sheaf.H.map (m (a + b)) 1 x = Sheaf.H.map (m a) 1 x + Sheaf.H.map (m b) 1 x
        rw [hmadd, Sheaf.H.map_add_apply]
      zero_smul := hmzero }
  obtain ⟨E, hE⟩ := exists_addEquiv_H1 f hproj m hm
  let L : Sheaf.H O 1 ≃ₗ[ℂ] cohomologyOverField ℂ f (SheafOfModules.unit C.ringCatSheaf) 1 :=
    { E with map_smul' := fun a x => hE a x }
  have hfin : FiniteDimensional ℂ (Sheaf.H O 1) := by
    have : (SheafOfModules.unit C.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit ℂ f
    have := finiteDimensional_cohomologyOverField_of_isProper ℂ f
      (SheafOfModules.unit C.ringCatSheaf) 1
    exact LinearEquiv.finiteDimensional L.symm
  have hrank :
      Module.finrank ℂ (Sheaf.H O 1) = Module.finrank ℂ (structureSheafCohomology f 1) :=
    L.finrank_eq.trans
      (structureSheafCohomologyIsoCohomologyOverField ℂ f 1).toLinearEquiv.finrank_eq.symm
  let b := Module.finBasis ℂ (Sheaf.H O 1)
  exact ⟨_, b.equivFun.symm.toAddEquiv, fun a v => b.equivFun.symm.map_smul a v, hrank⟩

/-- Version of `MMP.Conductor.exists_isZLattice_exponential_of_isProjective` assuming the
exponential sequence `0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0` is short exact. -/
theorem exists_isZLattice_exponential_of_shortExact {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification f)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∀ (i : ZA ⟶ O) (e : O ⟶ Ou) (w : i ≫ e = 0) (hS : (ShortComplex.mk i e w).ShortExact),
      (∀ (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)) (x : W)
        (c : {c : Chart f // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf f).obj.obj (op W))ˣ) :
          (structureSheaf f).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') →
      ∀ (m : ℂ → (O ⟶ O)),
      (∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s) →
      letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      let expPic :=
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
          (analytification f)).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) Ou)).symm.toAddMonoidHom.comp (Sheaf.H.map e 1))
      ∃ (n : ℕ) (φ : (Fin n → ℂ) ≃+ Sheaf.H O 1),
        (∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v)) ∧
        let Λ : Submodule ℤ (Fin n → ℂ) :=
          ((Sheaf.H.map i 1).range.comap φ.toAddMonoidHom).toIntSubmodule
        ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧
        (expPic.comp φ.toAddMonoidHom).ker = Λ.toAddSubgroup ∧
        (expPic.comp φ.toAddMonoidHom).range = (picardObstruction (analytification f) hS).ker ∧
        ∀ (JX : Grp (Over (Spec (.of ℂ))))
          (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
          let cls : ComplexPoints JX.X.hom →
              (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
            fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
          ∃ Φ : (Fin n → ℂ) → space JX.X.hom, Continuous Φ ∧
            (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ ComplexPoints.chart c.U),
              ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
                ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ ComplexPoints.chart c.U, c.coords ⟨Φ v', h'⟩ = F v') ∧
            (∃ U : Set (Fin n → ℂ), IsOpen U ∧ 0 ∈ U ∧ ∃ V : Opens (space JX.X.hom),
              Set.BijOn Φ U V ∧ ∃ Ψ : space JX.X.hom → (Fin n → ℂ), Set.LeftInvOn Ψ Φ U ∧
                ∀ (y : space JX.X.hom) (_ : y ∈ V) (c : Chart JX.X.hom)
                  (hy : y ∈ ComplexPoints.chart c.U),
                  ∃ G : (Fin c.n → ℂ) → (Fin n → ℂ), DifferentiableAt ℂ G (c.coords ⟨y, hy⟩) ∧
                    ∀ᶠ y' in 𝓝 y, ∀ hy' : y' ∈ ComplexPoints.chart c.U, y' ∈ V →
                      Ψ y' = G (c.coords ⟨y', hy'⟩)) ∧
            (∀ v v', cls (Φ (v + v')) = cls (Φ v) * cls (Φ v')) ∧
            (∀ v, cls (Φ v) = 1 ↔ v ∈ Λ) ∧
            Function.Surjective (cls ∘ Φ) := by
  have := hproj.isProper
  intro J O Ou ZA i e w hS he m hm
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  intro expPic
  obtain ⟨n, φ, hφ, hrank⟩ := exists_linear_coords_H1 f hproj m hm
  refine ⟨n, φ, hφ, ?_⟩
  intro Λ
  obtain ⟨hker, hrange⟩ := ker_range_expPic f i e w hS φ
  have huni := exists_uniformisation_jacobian f hproj hdim σ hσ e he m hm φ hφ hrank Λ hker
  obtain ⟨J0, e0, hab, -⟩ := MMP.Conductor.exists_jacobian_of_isProjective f hproj hdim σ hσ
  have : IsProper J0.X.hom := hab.toIsProperVariety.toIsProper
  have : CompactSpace (space J0.X.hom) :=
    MMP.Proof_lem_mmp_projective_corner_presentation.compactSpace_complexPoints J0.X.hom
  obtain ⟨Φ, -, -, ⟨U, hU, h0, V, hbij, -⟩, hhom, hker', hsurj, hopen⟩ := huni J0 e0
  have hinj : Function.Injective fun x : ComplexPoints J0.X.hom =>
      (e0.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2) :=
    (bijective_cls f hproj hdim σ hσ J0 e0).1
  obtain ⟨hdisc, hlat⟩ := lattice_of_uniformisation Λ _ hinj Φ hopen hhom hker' hsurj U hU h0
    hbij.injOn
  refine ⟨hdisc, hlat, hker, hrange, fun JX eJ => ?_⟩
  obtain ⟨Φ, h1, h2, h3, h4, h5, h6, -⟩ := huni JX eJ
  exact ⟨Φ, h1, h2, h3, h4, h5, h6⟩

end MMP.JacobianLogarithm

namespace MMP.Conductor

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

/-- **Logarithmic coordinates on the curve Picard group.** Let `C` be a smooth projective
connected curve over `ℂ` with a section `σ`, and let `A = C^an`. Let `i : ℤ_A ⟶ 𝒪_A` and
`e : 𝒪_A ⟶ 𝒪_A^×` be the maps of the exponential sequence, `n ↦ n` and `u ↦ exp (2πi u)`, and
let `m c` be multiplication by `c ∈ ℂ` on `𝒪_A`. Then `0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0` is short
exact, and there is a `ℂ`-linear identification `φ : ℂⁿ ≃+ H¹(A, 𝒪_A)` with the following
properties:
* the preimage `Λ` of the image of `H¹(A, ℤ_A)` is a discrete full lattice;
* the exponential map `H¹(A, 𝒪_A) → Pic(A)` has kernel exactly the image of `H¹(A, ℤ_A)`;
* its range is the degree-zero part `ker (picardObstruction A)`.

Further, for every group object `J` over `ℂ` representing the rigidified degree-zero Picard
functor by `eJ`, there is a continuous holomorphic map `Φ : ℂⁿ → J(ℂ)` with the following
properties:
* `Φ` maps an open neighbourhood `U` of `0` bijectively onto an open set `V`, with a left
  inverse on `U` that is holomorphic on `V`;
* on rigidified classes, `Φ` is a surjective homomorphism with kernel `Λ`. -/
@[mmp "lem_mmp_conductor_curve_jacobian_logarithm"]
theorem exists_isZLattice_exponential_of_isProjective {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    haveI := hproj.isProper
    let J := Opens.grothendieckTopology (space f)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification f)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∀ (i : ZA ⟶ O) (e : O ⟶ Ou) (w : i ≫ e = 0),
      (∀ (W : Opens (space f)) (n : ℤ),
        (show (structureSheaf f).obj.obj (op W) from i.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
      (∀ (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)) (x : W)
        (c : {c : Chart f // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf f).obj.obj (op W))ˣ) :
          (structureSheaf f).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ') →
      ∀ (m : ℂ → (O ⟶ O)),
      (∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s) →
      letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      let expPic :=
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
          (analytification f)).toAddMonoidHom.comp
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) Ou)).symm.toAddMonoidHom.comp (Sheaf.H.map e 1))
      ∃ (hS : (ShortComplex.mk i e w).ShortExact) (n : ℕ) (φ : (Fin n → ℂ) ≃+ Sheaf.H O 1),
        (∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v)) ∧
        let Λ : Submodule ℤ (Fin n → ℂ) :=
          ((Sheaf.H.map i 1).range.comap φ.toAddMonoidHom).toIntSubmodule
        ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧
        (expPic.comp φ.toAddMonoidHom).ker = Λ.toAddSubgroup ∧
        (expPic.comp φ.toAddMonoidHom).range = (picardObstruction (analytification f) hS).ker ∧
        ∀ (JX : Grp (Over (Spec (.of ℂ))))
          (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ),
          let cls : ComplexPoints JX.X.hom →
              (Stacks.RigidifiedPicard.functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _))) :=
            fun x => (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)
          ∃ Φ : (Fin n → ℂ) → space JX.X.hom, Continuous Φ ∧
            (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ ComplexPoints.chart c.U),
              ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
                ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ ComplexPoints.chart c.U, c.coords ⟨Φ v', h'⟩ = F v') ∧
            (∃ U : Set (Fin n → ℂ), IsOpen U ∧ 0 ∈ U ∧ ∃ V : Opens (space JX.X.hom),
              Set.BijOn Φ U V ∧ ∃ Ψ : space JX.X.hom → (Fin n → ℂ), Set.LeftInvOn Ψ Φ U ∧
                ∀ (y : space JX.X.hom) (_ : y ∈ V) (c : Chart JX.X.hom)
                  (hy : y ∈ ComplexPoints.chart c.U),
                  ∃ G : (Fin c.n → ℂ) → (Fin n → ℂ), DifferentiableAt ℂ G (c.coords ⟨y, hy⟩) ∧
                    ∀ᶠ y' in 𝓝 y, ∀ hy' : y' ∈ ComplexPoints.chart c.U, y' ∈ V →
                      Ψ y' = G (c.coords ⟨y', hy'⟩)) ∧
            (∀ v v', cls (Φ (v + v')) = cls (Φ v) * cls (Φ v')) ∧
            (∀ v, cls (Φ v) = 1 ↔ v ∈ Λ) ∧
            Function.Surjective (cls ∘ Φ) := by
  have := hproj.isProper
  intro J O Ou ZA i e w hi he m hm
  obtain ⟨ι₀, e₀, w₀, hS₀, hι₀, he₀⟩ := MMP.Analytic.exists_shortExact_exponentialSequence f
  obtain ⟨rfl, rfl⟩ :=
    MMP.JacobianLogarithm.eq_of_exponential_formulas f i ι₀ e e₀ hi hι₀ he he₀
  exact ⟨hS₀, MMP.JacobianLogarithm.exists_isZLattice_exponential_of_shortExact f hproj hdim σ hσ
    i e w hS₀ he m hm⟩

end MMP.Conductor

end
