module

public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.PicardLogCoordinates
public import MMP.AlgebraicGeometry.Analytic.CornerPresentation
public import MMP.AlgebraicGeometry.Analytic.ExponentialSequence

/-!
# The exponential uniformisation of a curve Jacobian is `GAGA⁻¹ ∘ exp`

Let `C` be a smooth projective connected curve over `ℂ` with a point `σ`, `A = C^an`, and
`φ : ℂⁿ ≃ H¹(A, 𝒪_A)` a `ℂ`-linear coordinate system. For a Jacobian `J` of `C`, representing
the rigidified degree-zero Picard functor, the exponential uniformisation `Φ : ℂⁿ → J(ℂ)` is
built from the exponential sequence: the class of `Φ v` is the algebraic line bundle whose
analytification is `exp (φ v) ∈ Pic(A)`. This file records that pin. Concretely, if `L` is an
invertible `𝒪_C`-module whose class on `C ×_ℂ Spec ℂ` is the rigidified class of `Φ v`, then the
class of `L^an` in `Pic(A) ≅ H¹(A, 𝒪_A^×)` is the image of `φ v` under the exponential map
`H¹(A, 𝒪_A) → H¹(A, 𝒪_A^×)`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.IsExpUniformisation`: `Φ : ℂⁿ → J(ℂ)` is `GAGA⁻¹ ∘ exp ∘ φ`, read
  on invertible modules representing the classes of `Φ v`.

## Main results

* `MMP.Analytic.SurfaceHodge.exists_uniformisation_jacobian_pinned`: the uniformisation of a
  Jacobian attached to a coordinate system `φ`, with the pin `[L^an] = exp (φ v)`.
* `MMP.Analytic.SurfaceHodge.exists_isZLattice_exponential_pinned_of_shortExact`: the
  logarithmic coordinates of `MMP.JacobianLogarithm.exists_isZLattice_exponential_of_shortExact`
  for a given short exact exponential sequence, with the uniformisation pinned.
* `MMP.Analytic.SurfaceHodge.exists_isZLattice_exponential_pinned_of_isProjective`: the
  logarithmic coordinates of `MMP.Conductor.exists_isZLattice_exponential_of_isProjective`, with
  the uniformisation pinned to the exponential map.
* `MMP.Analytic.SurfaceHodge.exists_schemePullbackClass_eq_of_isExpUniformisation`: if
  `exp (φ v)` is the class of `(ι^* L_X)^an` for an invertible `L_X` on `X`, then `Φ v` is a
  restriction point of `ι : C ⟶ X`; `exists_schemePullbackClass_eq_of_mem_range` for all `v` with
  `φ v` in the range of a map whose exponentials are such classes.
* `MMP.Analytic.SurfaceHodge.classOf_analytify_pullback_eq_of_isExpUniformisation`: conversely,
  at a restriction point `Φ v` the class of `(ι^* L_X)^an` is `exp (φ v)`.
* `MMP.Analytic.SurfaceHodge.exists_classOf_analytifyModule_eq`: GAGA on the Picard group
  `H¹(X^an, 𝒪^×)` of a projective `X`: every class is that of some `L_X^an`.

## Implementation notes

The uniformisation is the unique map `Φ` with `ι (cls (Φ v)) = E v` for every `v`, where `cls`
is the classifying bijection of `J(ℂ)`, `ι` is GAGA on rigidified classes and `E` is the
exponential map, both landing in the group-of-units model of the analytic Picard group. The
library proves this identity near `0`; it holds on all of `ℂⁿ` because `Φ` is a homomorphism. The
analytic class is read in the shrunk model `Stacks.SheafOfModules.Picard.PicardGroup`, the
target of `Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`. It is compared with the
group-of-units model, the target of GAGA, through the injective
`MMP.JacobianLogarithm.ringedPicardToSheafPicardHom`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Filter Topology
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open MMP.JacobianLogarithm

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance] CategoryTheory.Hom.group

/-- `Φ : ℂⁿ → J(ℂ)` is the **exponential uniformisation** of the Jacobian `J` of `C` (with
classifying isomorphism `eJ`) for coordinates `φ : ℂⁿ ≃ H` and a map `expPic : H → Pic(C^an)`
(in use, `H = H¹(C^an, 𝒪)` and `expPic` the exponential map): for every `v` and every
invertible `𝒪_C`-module `L` whose class on `C ×_ℂ Spec ℂ` is the rigidified class of `Φ v`, the
class of `L^an` in `Pic(C^an)` is `expPic (φ v)`. -/
def IsExpUniformisation {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) [IsProper f]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ)
    {H : Type} [AddCommGroup H]
    (expPic : letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      H →+ Stacks.SheafOfModules.Picard.PicardGroup (analytification f : RingedSpace).sheaf.obj
        (structureSheaf (analytification f : RingedSpace).sheaf).property)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ H) (Φ : (Fin n → ℂ) → space JX.X.hom) : Prop :=
  ∀ (v : Fin n → ℂ) (L : C.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) L)
    (hLan : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((analytifyModule f).obj L)),
    Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _))
        (Stacks.SheafOfModules.picardClass C.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) L hL) =
      Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
        ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1 →
    Stacks.SheafOfModules.Picard.classOf _ _ _ hLan = expPic (φ v)

/-- Two maps from a topological vector space over a characteristic-zero topological division
semiring to a monoid which send sums to products and agree near `0` agree everywhere. -/
theorem eq_of_eventuallyEq_nhds_zero (𝕜 : Type*) {V M : Type*} [DivisionSemiring 𝕜]
    [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] [Monoid M] {F G : V → M}
    (hF : ∀ v w, F (v + w) = F v * F w) (hG : ∀ v w, G (v + w) = G v * G w)
    (hFG : ∀ᶠ u in 𝓝 0, F u = G u) (v : V) : F v = G v := by
  have hpow : ∀ u, F u = G u → ∀ k : ℕ, F ((k + 1) • u) = G ((k + 1) • u) := by
    intro u hu k
    induction k with
    | zero => rwa [zero_add, one_nsmul]
    | succ k ih => rw [succ_nsmul, hF, hG, ih, hu]
  have ht : Tendsto (fun N : ℕ => ((N : 𝕜) + 1)⁻¹ • v) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := 𝕜)).smul_const v
  obtain ⟨N, hN⟩ := (ht.eventually hFG).exists
  have hv : (N + 1) • (((N : 𝕜) + 1)⁻¹ • v) = v := by
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (Nat.cast_add_one_ne_zero N), one_smul]
  simpa only [hv] using hpow _ hN N

/-- A representative `J` of the rigidified degree-zero Picard functor of a smooth projective
connected curve `C` over `ℂ` is smooth of relative dimension `h¹(𝒪_C)`. -/
theorem smoothOfRelativeDimension_of_iso_functorZero {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ) {n : ℕ}
    (hrank : n = Module.finrank ℂ (structureSheafCohomology f 1)) :
    SmoothOfRelativeDimension n JX.X.hom := by
  obtain ⟨J0, e0, hab, -, hdimJ, -⟩ :=
    MMP.Conductor.exists_jacobian_of_isProjective f hproj hdim σ hσ
  haveI : Smooth J0.X.hom := smooth_of_isAbelianVariety ℂ J0.X
  haveI : Nonempty J0.X.left :=
    ⟨(MonObj.one (X := J0.X)).left (IsLocalRing.closedPoint ℂ)⟩
  haveI : MMP.Mori.IsVariety ℂ J0.X.hom := hab.toIsProperVariety.toIsVariety
  have hK := Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J0.X
  rw [hdimJ, ← hrank] at hK
  haveI : SmoothOfRelativeDimension n J0.X.hom :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety J0.X.hom _ hK
  let isoJ : JX.X ≅ J0.X :=
    (Grp.forget _).mapIso (yonedaGrpFullyFaithful.preimageIso (eJ ≪≫ e0.symm))
  rw [← Over.w isoJ.hom]
  simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (isoJ.hom.left ≫ J0.X.hom))

/-- A representative `J` of the rigidified degree-zero Picard functor of a smooth projective
connected curve `C` over `ℂ` is proper. -/
theorem isProper_of_iso_functorZero {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C] (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ) :
    IsProper JX.X.hom := by
  obtain ⟨J0, e0, hab, -⟩ := MMP.Conductor.exists_jacobian_of_isProjective f hproj hdim σ hσ
  haveI : IsProper J0.X.hom := hab.toIsProperVariety.toIsProper
  let isoJ : JX.X ≅ J0.X :=
    (Grp.forget _).mapIso (yonedaGrpFullyFaithful.preimageIso (eJ ≪≫ e0.symm))
  rw [← Over.w isoJ.hom]
  infer_instance

/-- The `ℂ`-module structure on `H¹(A, 𝒪_A)` in which `a ∈ ℂ` acts through `H¹` of `m a`. -/
noncomputable abbrev moduleH1OfSmulConst {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ))
    (m : ℂ → ((sheafCompose (Opens.grothendieckTopology (space f))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f) ⟶
        (sheafCompose (Opens.grothendieckTopology (space f))
          (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)))
    (hmadd : ∀ a b : ℂ, m (a + b) = m a + m b) (hmmul : ∀ a b : ℂ, m (a * b) = m b ≫ m a)
    (hmone : m 1 = 𝟙 _) :
    Module ℂ (Sheaf.H ((sheafCompose (Opens.grothendieckTopology (space f))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf f)) 1) where
  smul a x := Sheaf.H.map (m a) 1 x
  one_smul x := by
    change Sheaf.H.map (m 1) 1 x = x
    rw [hmone, Sheaf.H.map_id_apply]
  mul_smul a b x := by
    change Sheaf.H.map (m (a * b)) 1 x = Sheaf.H.map (m a) 1 (Sheaf.H.map (m b) 1 x)
    rw [hmmul, Sheaf.H.map_comp_apply]
  smul_zero a := map_zero (Sheaf.H.map (m a) 1)
  smul_add a x y := map_add (Sheaf.H.map (m a) 1) x y
  add_smul a b x := by
    change Sheaf.H.map (m (a + b)) 1 x = Sheaf.H.map (m a) 1 x + Sheaf.H.map (m b) 1 x
    rw [hmadd, Sheaf.H.map_add_apply]
  zero_smul x := by
    have h := Sheaf.H.map_add_apply (m 0) (m 0) x
    rw [← hmadd, add_zero] at h
    exact left_eq_add.mp h

/-- **The exponential uniformisation of the Jacobian, pinned to the exponential map.** For any
representative `J` of the rigidified degree-zero Picard functor, a `ℂ`-linear coordinate system
`φ : ℂⁿ ≃ H¹(C^an, 𝒪)` with `n = h¹(𝒪_C)` gives a holomorphic, open homomorphism
`Φ : ℂⁿ → J(ℂ)`, biholomorphic near `0`, onto `J(ℂ)`, whose kernel is the kernel `Λ` of the
exponential map, and which is the exponential uniformisation (`IsExpUniformisation`). -/
theorem exists_uniformisation_jacobian_pinned {C : Scheme.{0}}
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
        (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (hv : Φ v ∈ ComplexPoints.chart c.U),
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
        Function.Surjective (cls ∘ Φ) ∧ IsOpenMap Φ ∧
        IsExpUniformisation f hdim σ hσ eJ expPic φ Φ := by
  haveI := hproj.isProper
  intro J O Ou e he m hm n φ hφ hrank
  obtain ⟨hmadd, hmmul, -⟩ := smulConst_add_mul_one f m hm
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  intro expPic Λ hker JX eJ cls
  obtain ⟨hclsb, hconn, τ, hτ, hτc, hτo, hτh, hτr⟩ :=
    jacobian_points_translations f hproj hdim σ hσ n JX eJ
  replace hclsb : Function.Bijective cls := hclsb
  replace hτ : ∀ t y, cls (τ t y) = cls t * cls y := hτ
  obtain ⟨_hinvG, eG, heG, -⟩ := exists_mulEquiv_picardGroup_analytification_of_isProjective f hproj
  let P1 : Over (Spec (.of ℂ)) := Over.mk (𝟙 _)
  let g : C ⟶ Stacks.RigidifiedPicard.bc f P1 := Limits.pullback.lift (𝟙 C) f (by simp [P1])
  have hg : Limits.pullback.fst f P1.hom ≫ g = 𝟙 _ := pullback_fst_comp_lift_id f
  let H := Stacks.RigidifiedPicard.groupZero f hdim σ hσ P1
  let ιadd : H →+ Additive (Stacks.SheafPicardGroup.PicardGroup
      (J := Opens.grothendieckTopology (space f)) (structureSheaf f).obj (ringCatSheaf f).2) :=
    (MulEquiv.toAdditive eG).toAddMonoidHom.comp
      ((toSheafPicardHom C.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)).comp
        ((Stacks.Picard.schemePullbackClassHom g).comp
          ((Stacks.RigidifiedPicard.smallEquiv _).toAddMonoidHom.comp
            ((Stacks.RigidifiedPicard.group f σ hσ P1).subtype.comp H.subtype))))
  have hιadd : Function.Injective ιadd := by
    intro x y hxy
    have h3 := congrArg (Stacks.Picard.schemePullbackClass (Limits.pullback.fst f P1.hom))
      (toSheafPicardHom_injective _ _ ((MulEquiv.toAdditive eG).injective hxy))
    change Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass g _) =
      Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass g _) at h3
    rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp, hg,
      Stacks.Picard.schemePullbackClass_id, Stacks.Picard.schemePullbackClass_id] at h3
    exact Subtype.ext (Subtype.ext ((Stacks.RigidifiedPicard.smallEquiv _).injective h3))
  let ι := AddMonoidHom.toMultiplicative ιadd
  have hι : Function.Injective ι := fun _ _ h =>
    Multiplicative.toAdd.injective (hιadd (congrArg Multiplicative.toAdd h))
  have hcls : ∀ (y : space JX.X.hom) (Lm : C.Modules)
      (hLm : Stacks.SheafOfModules.IsInvertible C.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) Lm),
      Stacks.Picard.schemePullbackClass g (Stacks.RigidifiedPicard.smallEquiv _
        (Multiplicative.toAdd (cls y)).1.1) =
        Stacks.SheafOfModules.picardClass C.presheaf _ Lm hLm →
      ∀ [Stacks.Ample.IsInvertibleModule C Lm], ιadd (Multiplicative.toAdd (cls y)) =
        Additive.ofMul (eG (Stacks.SheafPicardGroup.schemeClassOf C Lm)) := by
    intro y Lm hLm h2 _
    change Additive.ofMul (eG (Additive.toMul (toSheafPicardHom C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
      (Stacks.Picard.schemePullbackClass g (Stacks.RigidifiedPicard.smallEquiv _
        (Multiplicative.toAdd (cls y)).1.1))))) = _
    rw [h2]
    change Additive.ofMul (eG (Additive.toMul (toSheafPicard C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
      (Stacks.SheafOfModules.picardClass C.presheaf _ Lm hLm)))) = _
    exact (congrArg (fun z => Additive.ofMul (eG (Additive.toMul z)))
      (toSheafPicard_picardClass C.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) Lm hLm)).trans rfl
  let E := (ringedPicardToSheafPicardHom (analytification f)).comp
    (expPic.comp φ.toAddMonoidHom)
  have hE : ∀ v, E v = 0 ↔ v ∈ Λ := by
    intro v
    change ringedPicardToSheafPicardHom (analytification f) _ = 0 ↔ _
    refine (map_eq_zero_iff _ (ringedPicardToSheafPicardHom_injective _)).trans ?_
    rw [← AddMonoidHom.mem_ker, hker]
    rfl
  let Puniv := (eJ.hom.app (op JX.X)).hom (𝟙 JX.X)
  have hPuniv : ∀ y : space JX.X.hom, cls y =
      ((Stacks.RigidifiedPicard.functorZero f hdim σ hσ).map
        (Over.homMk y.1 y.2 : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X).op).hom Puniv := by
    intro y
    let yy : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X := Over.homMk y.1 y.2
    have h := ConcreteCategory.congr_hom (eJ.hom.naturality yy.op) (𝟙 JX.X)
    refine Eq.trans ?_ h
    change (eJ.hom.app _).hom yy = (eJ.hom.app _).hom (yy ≫ 𝟙 JX.X)
    rw [Category.comp_id]
  haveI : SmoothOfRelativeDimension n JX.X.hom :=
    smoothOfRelativeDimension_of_iso_functorZero f hproj hdim σ hσ eJ hrank
  obtain ⟨c, L, Ω, hΩ, hLd, hne, hlog⟩ :
      ∃ (c : ComplexPoints.EtaleCoordinateChart JX.X.hom n) (L : (Fin n → ℂ) → (Fin n → ℂ))
        (Ω : Set (Fin n → ℂ)), IsOpen Ω ∧ ContDiffOn ℂ 1 L Ω ∧
        (∃ y ∈ c.W, c.toOpenPartialHomeomorph y ∈ Ω) ∧
        ∀ y ∈ c.W, c.toOpenPartialHomeomorph y ∈ Ω →
          ι (cls y) = Multiplicative.ofAdd (E (L (c.toOpenPartialHomeomorph y))) := by
    haveI : IsProper JX.X.hom := isProper_of_iso_functorZero f hproj hdim σ hσ eJ
    obtain ⟨M, hM, hMu⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _
      (Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd Puniv).1.1)
    have hM' : Stacks.SheafOfModules.IsInvertible
        (Limits.pullback f JX.X.hom).toRingedSpace.sheaf.obj _ M := hM
    have hinvy : ∀ y : space JX.X.hom, Stacks.SheafOfModules.IsInvertible
        (analytification f : RingedSpace).sheaf.obj
        (structureSheaf (analytification f : RingedSpace).sheaf).property
        ((RingedSpaceModuleAdjunction.modulePullback (X := (analytification f : RingedSpace))
          (Y := C.toRingedSpace) (analytificationHom f)).obj
          ((RingedSpaceModuleAdjunction.modulePullback
            (Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom).obj M)) := by
      intro y
      haveI := Stacks.RingedSpace.isInvertible_modulePullback
        ((Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom) M
      exact Stacks.RingedSpace.isInvertible_modulePullback _ _
    have hkey : ∀ y : space JX.X.hom, ι (cls y) = Multiplicative.ofAdd
        (ringedPicardToSheafPicardHom (analytification f)
          (Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy y))) := by
      intro y
      let yy : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X := Over.homMk y.1 y.2
      have hgj : g ≫ Stacks.RigidifiedPicard.bcMap f yy = Fam.sliceAt f JX.X.hom y :=
        lift_id_comp_bcMap f JX.X y
      have h1 : (Multiplicative.toAdd (cls y)).1.1 = Stacks.Picard.smallSchemePullbackClassHom
          (Stacks.RigidifiedPicard.bcMap f yy) (Multiplicative.toAdd Puniv).1.1 := by
        rw [hPuniv y]
        rfl
      let Lm := (RingedSpaceModuleAdjunction.modulePullback
        (Fam.sliceAt f JX.X.hom y).toLRSHom.toShHom).obj M
      have hLm : Stacks.SheafOfModules.IsInvertible C.presheaf _ Lm := by
        exact Stacks.RingedSpace.isInvertible_modulePullback _ _
      have h2 : Stacks.Picard.schemePullbackClass g (Stacks.RigidifiedPicard.smallEquiv _
          (Multiplicative.toAdd (cls y)).1.1) =
          Stacks.SheafOfModules.picardClass C.presheaf _ Lm hLm := by
        rw [h1, Stacks.RigidifiedPicard.smallEquiv_smallSchemePullbackClassHom, ← hMu,
          Stacks.Picard.schemePullbackClass_comp, hgj]
        exact Stacks.Picard.pullbackClass_classOf _ M hM
      haveI : Stacks.Ample.IsInvertibleModule C Lm :=
        (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ Lm).1 hLm
      have h5 := picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
        (structureSheaf (analytification f : RingedSpace).sheaf).property _ (hinvy y)
      change Multiplicative.ofAdd (ιadd (Multiplicative.toAdd (cls y))) =
        Multiplicative.ofAdd (picardToSheafPicard _ _ _)
      rw [hcls y Lm hLm h2, heG Lm]
      exact congrArg Multiplicative.ofAdd h5.symm
    have hsc : ∀ y : space JX.X.hom, Fam.sliceClass f JX.X.hom M hM' y =
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification f)).symm
          (Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy y)) := fun y =>
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf _ _ _).symm
    obtain ⟨e₀, he₀1⟩ := hclsb.2 1
    have he₀ : Fam.sliceClass f JX.X.hom M hM' e₀ = 0 := by
      have h1 := hkey e₀
      have h0 : ι (cls e₀) = 1 := by rw [he₀1]; exact map_one ι
      rw [h0] at h1
      have h3 : Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy e₀) = 0 :=
        (ringedPicardToSheafPicardHom_injective (analytification f))
          ((congrArg Multiplicative.toAdd h1.symm).trans (map_zero _).symm)
      rw [hsc, h3, map_zero]
    obtain ⟨c, L, Ω, hΩ, hLd, he₀W, he₀Ω, hfam⟩ :=
      Fam.exists_etaleCoordinateChart_sliceClass_eq f JX.X.hom M hM' e₀ he₀ e he m hm hmadd hmmul
        φ hφ
    refine ⟨c, L, Ω, hΩ, hLd, ⟨e₀, he₀W, he₀Ω⟩, fun y hy hyΩ => ?_⟩
    rw [hkey y]
    congr 1
    have h4 := (hsc y).symm.trans (hfam y hy hyΩ)
    have h5 : Stacks.SheafOfModules.Picard.classOf _ _ _ (hinvy y) =
        Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification f)
          ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) Ou)).symm (Sheaf.H.map e 1 (φ (L (c.toOpenPartialHomeomorph y))))) := by
      rw [← h4, AddEquiv.apply_symm_apply]
    rw [h5]
    rfl
  haveI : Smooth JX.X.hom := SmoothOfRelativeDimension.smooth n JX.X.hom
  obtain ⟨Φ0, U, hU, h0, hΦ0, hc, ho, hh, V, hbij, Ψ, hinv, hΨ⟩ :=
    exists_localExp_of_localLog cls hclsb ι hι E τ hτ hτc hτo hτh hτr c L Ω hΩ hLd hne hlog
  obtain ⟨Φ, hΦc, hΦh, hΦeq, hΦo, hΦhom, hΦker, hΦs⟩ :=
    exists_uniformisation_of_localExp cls hclsb ι hι E
      ChartHolomorphicAt (fun _ _ _ h hF => hF.congr h) (fun _ _ _ hF => hF.comp_sub)
      τ hτ hτc hτo hτh Φ0 U hU h0 hΦ0 hc ho hh
  have hpin : ∀ v, ι (cls (Φ v)) = Multiplicative.ofAdd (E v) :=
    eq_of_eventuallyEq_nhds_zero ℂ (F := fun v => ι (cls (Φ v)))
      (G := fun v => Multiplicative.ofAdd (E v))
      (fun v w => (congrArg ι (hΦhom v w)).trans (map_mul ι _ _))
      (fun v w => congrArg Multiplicative.ofAdd (map_add E v w))
      (Filter.eventually_of_mem (hU.mem_nhds h0) fun u hu =>
        (congrArg (fun x => ι (cls x)) (hΦeq hu)).trans (hΦ0 u hu))
  refine ⟨Φ, hΦc, hΦh, ⟨U, hU, h0, V, hbij.congr hΦeq.symm, Ψ,
    fun x hx => (congrArg Ψ (hΦeq hx)).trans (hinv hx), hΨ⟩, hΦhom,
    fun v => (hΦker v).trans (hE v), hΦs, hΦo, ?_⟩
  intro v Lm hLm hLan hcl
  have hg' : g ≫ Limits.pullback.fst f (𝟙 _) = 𝟙 C := Limits.pullback.lift_fst _ _ _
  have h2 : Stacks.Picard.schemePullbackClass g (Stacks.RigidifiedPicard.smallEquiv _
      (Multiplicative.toAdd (cls (Φ v))).1.1) =
      Stacks.SheafOfModules.picardClass C.presheaf _ Lm hLm := by
    rw [← hcl]
    erw [Stacks.Picard.schemePullbackClass_comp g (Limits.pullback.fst f (𝟙 _)), hg',
      Stacks.Picard.schemePullbackClass_id]
  haveI : Stacks.Ample.IsInvertibleModule C Lm :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ Lm).1 hLm
  have h7 : ιadd (Multiplicative.toAdd (cls (Φ v))) = E v :=
    congrArg Multiplicative.toAdd (hpin v)
  apply ringedPicardToSheafPicardHom_injective (analytification f)
  refine Eq.trans ?_ h7
  rw [hcls _ Lm hLm h2, heG Lm]
  exact picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
    (structureSheaf (analytification f : RingedSpace).sheaf).property _ hLan

/-- **Logarithmic coordinates with a pinned uniformisation**, for a given short exact
exponential sequence: `MMP.JacobianLogarithm.exists_isZLattice_exponential_of_shortExact` with
the uniformisation `Φ` pinned to the exponential map,
`[L^an] = exp (φ v)` whenever `L` represents the class of `Φ v`. -/
theorem exists_isZLattice_exponential_pinned_of_shortExact {C : Scheme.{0}}
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
            (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (hv : Φ v ∈ ComplexPoints.chart c.U),
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
            Function.Surjective (cls ∘ Φ) ∧
            IsExpUniformisation f hdim σ hσ eJ expPic φ Φ := by
  haveI := hproj.isProper
  intro J O Ou ZA i e w hS he m hm
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  intro expPic
  obtain ⟨hmadd, hmmul, hmone⟩ := smulConst_add_mul_one f m hm
  letI : Module ℂ (Sheaf.H O 1) := moduleH1OfSmulConst f m hmadd hmmul hmone
  obtain ⟨E, hE⟩ := exists_addEquiv_H1 f hproj m hm
  let L : Sheaf.H O 1 ≃ₗ[ℂ] cohomologyOverField ℂ f (SheafOfModules.unit C.ringCatSheaf) 1 :=
    { E with map_smul' := fun a x => hE a x }
  have hfin : FiniteDimensional ℂ (Sheaf.H O 1) := by
    haveI : (SheafOfModules.unit C.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit ℂ f
    haveI := finiteDimensional_cohomologyOverField_of_isProper ℂ f
      (SheafOfModules.unit C.ringCatSheaf) 1
    exact LinearEquiv.finiteDimensional L.symm
  have hrank :
      Module.finrank ℂ (Sheaf.H O 1) = Module.finrank ℂ (structureSheafCohomology f 1) :=
    L.finrank_eq.trans
      (structureSheafCohomologyIsoCohomologyOverField ℂ f 1).toLinearEquiv.finrank_eq.symm
  let b := Module.finBasis ℂ (Sheaf.H O 1)
  let φ : (Fin (Module.finrank ℂ (Sheaf.H O 1)) → ℂ) ≃+ Sheaf.H O 1 :=
    b.equivFun.symm.toAddEquiv
  have hφ : ∀ (a : ℂ) (v : Fin (Module.finrank ℂ (Sheaf.H O 1)) → ℂ),
      φ (a • v) = Sheaf.H.map (m a) 1 (φ v) := fun a v =>
    b.equivFun.symm.map_smul a v
  refine ⟨_, φ, hφ, ?_⟩
  intro Λ
  obtain ⟨hker, hrange⟩ := ker_range_expPic f i e w hS φ
  have huni := exists_uniformisation_jacobian_pinned f hproj hdim σ hσ e he m hm φ hφ hrank Λ hker
  obtain ⟨J0, e0, hab, -⟩ := MMP.Conductor.exists_jacobian_of_isProjective f hproj hdim σ hσ
  haveI : IsProper J0.X.hom := hab.toIsProperVariety.toIsProper
  haveI : CompactSpace (space J0.X.hom) :=
    MMP.Proof_lem_mmp_projective_corner_presentation.compactSpace_complexPoints J0.X.hom
  obtain ⟨Φ, -, -, ⟨U, hU, h0, V, hbij, -⟩, hhom, hker', hsurj, hopen, -⟩ := huni J0 e0
  have hinj : Function.Injective fun x : ComplexPoints J0.X.hom =>
      (e0.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2) := by
    intro x y hxy
    have h := (ConcreteCategory.bijective_of_isIso (e0.hom.app (op (Over.mk (𝟙 _))))).1 hxy
    exact Subtype.ext (congrArg CommaMorphism.left h)
  obtain ⟨hdisc, hlat⟩ := lattice_of_uniformisation Λ _ hinj Φ hopen hhom hker' hsurj U hU h0
    hbij.injOn
  refine ⟨hdisc, hlat, hker, hrange, fun JX eJ => ?_⟩
  obtain ⟨Φ, h1, h2, h3, h4, h5, h6, -, h7⟩ := huni JX eJ
  exact ⟨Φ, h1, h2, h3, h4, h5, h6, h7⟩

/-- **Logarithmic coordinates on the curve Picard group, with the uniformisation pinned to the
exponential map.** Let `C` be a smooth projective connected curve over `ℂ` with a section `σ`,
`A = C^an`, `i : ℤ_A ⟶ 𝒪_A` and `e : 𝒪_A ⟶ 𝒪_A^×` the maps `n ↦ n` and `u ↦ exp (2πi u)`, and
`m c` multiplication by `c ∈ ℂ` on `𝒪_A`. Then `0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0` is short exact and
there is a `ℂ`-linear `φ : ℂⁿ ≃+ H¹(A, 𝒪_A)` such that
* the preimage `Λ` of the image of `H¹(A, ℤ_A)` is a discrete full lattice;
* the exponential map `H¹(A, 𝒪_A) → Pic(A)` has kernel the image of `H¹(A, ℤ_A)` and range the
  kernel of `picardObstruction A`;
* for every Jacobian `J` of `C`, representing the rigidified degree-zero Picard functor by `eJ`,
  there is a continuous holomorphic `Φ : ℂⁿ → J(ℂ)`, biholomorphic near `0`, which on rigidified
  classes is a surjective homomorphism with kernel `Λ`, and which is `GAGA⁻¹ ∘ exp ∘ φ`: for every
  `v` and every invertible `𝒪_C`-module `L` whose class on `C ×_ℂ Spec ℂ` is the class of `Φ v`,
  the class of `L^an` in `Pic(A)` is the exponential of `φ v`. -/
theorem exists_isZLattice_exponential_pinned_of_isProjective {C : Scheme.{0}}
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
            (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (hv : Φ v ∈ ComplexPoints.chart c.U),
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
            Function.Surjective (cls ∘ Φ) ∧
            IsExpUniformisation f hdim σ hσ eJ expPic φ Φ := by
  haveI := hproj.isProper
  intro J O Ou ZA i e w hi he m hm
  obtain ⟨ι₀, e₀, w₀, hS₀, hι₀, he₀⟩ := MMP.Analytic.exists_shortExact_exponentialSequence f
  obtain ⟨rfl, rfl⟩ :=
    MMP.JacobianLogarithm.eq_of_exponential_formulas f i ι₀ e e₀ hi hι₀ he he₀
  exact ⟨hS₀, exists_isZLattice_exponential_pinned_of_shortExact f hproj hdim σ hσ i e w hS₀ he
    m hm⟩

section Restriction

variable {X C : Scheme.{0}} (ι : C ⟶ X) (f : C ⟶ Spec (.of ℂ)) [IsProper f]
  (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
  (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ)
  {H : Type} [AddCommGroup H]
  (expPic : letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
    H →+ Stacks.SheafOfModules.Picard.PicardGroup (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property)
  {n : ℕ} (φ : (Fin n → ℂ) ≃+ H) (Φ : (Fin n → ℂ) → space JX.X.hom)

/-- **Restriction points from the exponential.** Let `Φ` be the exponential uniformisation of the
Jacobian of a projective curve `C`, and `ι : C ⟶ X`. If the analytification of the restriction
`ι^* L_X` of an invertible module on `X` has class `expPic (φ v)`, then the rigidified class of
`Φ v` is the restriction of the class of `L_X`: `Φ v` is a restriction point of `ι`. -/
theorem exists_schemePullbackClass_eq_of_isExpUniformisation (hproj : IsProjective f)
    (hΦ : IsExpUniformisation f hdim σ hσ eJ expPic φ Φ) (v : Fin n → ℂ) (LX : X.Modules)
    (hLX : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
    (hLan : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((analytifyModule f).obj ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX)))
    (hexp : Stacks.SheafOfModules.Picard.classOf _ _ _ hLan = expPic (φ v)) :
    ∃ y : Stacks.Picard.ofScheme X,
      Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _) ≫ ι) y =
        Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
          ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1 := by
  set x := Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
    ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1
  let g : C ⟶ Limits.pullback f (𝟙 (Spec (.of ℂ))) := Limits.pullback.lift (𝟙 C) f (by simp)
  have hg : Limits.pullback.fst f (𝟙 _) ≫ g = 𝟙 _ := pullback_fst_comp_lift_id f
  obtain ⟨L, hL, hLc⟩ := Stacks.SheafOfModules.exists_picardClass_eq C.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
    (Stacks.Picard.schemePullbackClass g x)
  have hfx : Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _))
      (Stacks.SheafOfModules.picardClass C.presheaf _ L hL) = x := by
    rw [hLc, Stacks.Picard.schemePullbackClass_comp, hg, Stacks.Picard.schemePullbackClass_id]
  obtain ⟨_hinvG, eG, heG, -⟩ := exists_mulEquiv_picardGroup_analytification_of_isProjective f hproj
  have hLan1 : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((analytifyModule f).obj L) :=
    @Stacks.RingedSpace.isInvertible_modulePullback _ _ (analytificationHom f) L hL
  have h1 := (hΦ v L hL hLan1 hfx).trans hexp.symm
  have h2 := ((picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
    (structureSheaf (analytification f : RingedSpace).sheaf).property _ hLan1).symm.trans
      (congrArg (picardToSheafPicard _ _) h1)).trans
    (picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property _ hLan)
  set M := (Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX
  have hM : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) M :=
    Stacks.RingedSpace.modulePullback_isInvertible_of _ LX hLX
  haveI : Stacks.Ample.IsInvertibleModule C L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1 hL
  haveI : Stacks.Ample.IsInvertibleModule C M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).1 hM
  have h3 : eG (Stacks.SheafPicardGroup.schemeClassOf C L) =
      eG (Stacks.SheafPicardGroup.schemeClassOf C M) :=
    (heG L).trans ((Additive.ofMul.injective h2).trans (heG M).symm)
  have h5 : Stacks.SheafOfModules.picardClass C.presheaf _ L hL =
      Stacks.SheafOfModules.picardClass C.presheaf _ M hM :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ L M hL hM).2
      ((Stacks.SheafPicardGroup.schemeClassOf_eq_schemeClassOf_iff C L M).1 (eG.injective h3))
  refine ⟨Stacks.SheafOfModules.picardClass X.presheaf _ LX hLX, ?_⟩
  rw [← Stacks.Picard.schemePullbackClass_comp]
  exact (congrArg (Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _)))
    ((Stacks.Picard.pullbackClass_classOf ι.toLRSHom.toShHom LX hLX).trans h5.symm)).trans hfx

/-- **The exponential of a restriction point.** If `Φ v` is a restriction point of `ι`, the
rigidified class of `Φ v` being the restriction of the class of `L_X`, then the analytification
of `ι^* L_X` has class `expPic (φ v)`. -/
theorem classOf_analytify_pullback_eq_of_isExpUniformisation
    (hΦ : IsExpUniformisation f hdim σ hσ eJ expPic φ Φ) (v : Fin n → ℂ) (LX : X.Modules)
    (hLX : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
    (hLan : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((analytifyModule f).obj ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX)))
    (hy : Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _) ≫ ι)
        (Stacks.SheafOfModules.picardClass X.presheaf _ LX hLX) =
      Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
        ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1) :
    Stacks.SheafOfModules.Picard.classOf _ _ _ hLan = expPic (φ v) := by
  have hM : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
      ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of _ LX hLX
  refine hΦ v _ hM hLan ?_
  rw [← hy, ← Stacks.Picard.schemePullbackClass_comp]
  exact congrArg (Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _)))
    (Stacks.Picard.pullbackClass_classOf ι.toLRSHom.toShHom LX hLX).symm

/-- **Restriction points over a subgroup of exponentials.** Let `Φ` be the exponential
uniformisation of the Jacobian of a projective curve `C`, `ι : C ⟶ X`, and `res : H' → H` a map
(in use, the restriction `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`) such that `expPic (res w)` is, for every
`w`, the class of the analytified restriction `(ι^* L_X)^an` of an invertible module on `X`. Then
`Φ v` is a restriction point of `ι` for every `v` with `φ v` in the range of `res`. -/
theorem exists_schemePullbackClass_eq_of_mem_range (hproj : IsProjective f)
    (hΦ : IsExpUniformisation f hdim σ hσ eJ expPic φ Φ) {H' : Type*} (res : H' → H)
    (hres : ∀ w : H', ∃ (LX : X.Modules)
      (_ : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
      (hLan : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
        (structureSheaf (analytification f : RingedSpace).sheaf).property
        ((analytifyModule f).obj
          ((Stacks.RingedSpace.pullbackFunctor ι.toLRSHom.toShHom).obj LX))),
      Stacks.SheafOfModules.Picard.classOf _ _ _ hLan = expPic (res w))
    (v : Fin n → ℂ) (hv : φ v ∈ Set.range res) :
    ∃ y : Stacks.Picard.ofScheme X,
      Stacks.Picard.schemePullbackClass (Limits.pullback.fst f (𝟙 _) ≫ ι) y =
        Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
          ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2))).1.1 := by
  obtain ⟨w, hw⟩ := hv
  obtain ⟨LX, hLX, hLan, h⟩ := hres w
  exact exists_schemePullbackClass_eq_of_isExpUniformisation ι f hdim σ hσ eJ expPic φ Φ hproj
    hΦ v LX hLX hLan (h.trans (congrArg expPic hw))

end Restriction

/-- **GAGA on analytic Picard classes.** For a projective `X` over `ℂ`, every class in the
Picard group `Pic(X^an) ≅ H¹(X^an, 𝒪^×)` (the target of
`Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`) is the class of the analytification
of an invertible `𝒪_X`-module. -/
theorem exists_classOf_analytifyModule_eq {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjective sX)
    (p : Stacks.SheafOfModules.Picard.PicardGroup (analytification sX : RingedSpace).sheaf.obj
      (structureSheaf (analytification sX : RingedSpace).sheaf).property) :
    ∃ (LX : X.Modules) (_ : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX)
      (hLan : Stacks.SheafOfModules.IsInvertible (analytification sX : RingedSpace).sheaf.obj
        (structureSheaf (analytification sX : RingedSpace).sheaf).property
        ((analytifyModule sX).obj LX)),
      Stacks.SheafOfModules.Picard.classOf _ _ _ hLan = p := by
  obtain ⟨_hinv, eG, heG, -⟩ := exists_mulEquiv_picardGroup_analytification_of_isProjective sX hX
  obtain ⟨LX, hLXi, hLXc⟩ := Stacks.SheafPicardGroup.exists_classOf _ _
    (eG.symm (Additive.toMul (picardToSheafPicard _ _ p)))
  haveI : Stacks.Ample.IsInvertibleModule X LX := hLXi
  have hLX : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) LX :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ LX).2 hLXi
  have hLan := @Stacks.RingedSpace.isInvertible_modulePullback _ _ (analytificationHom sX) LX hLX
  refine ⟨LX, hLX, hLan, ?_⟩
  apply ringedPicardToSheafPicardHom_injective (analytification sX)
  refine (picardToSheafPicard_classOf _ _ _ hLan).trans ?_
  refine (congrArg Additive.ofMul (heG LX).symm).trans ?_
  rw [show Stacks.SheafPicardGroup.schemeClassOf X LX = _ from hLXc, MulEquiv.apply_symm_apply]
  rfl

end MMP.Analytic.SurfaceHodge

end
