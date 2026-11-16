module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.RestrictionPoints
public import MMP.AlgebraicGeometry.Divisor.LineBundleFamiliesCountable
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSpecField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurveAmple
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple

/-!
# Families of line bundles restricted to a curve, as families in its Jacobian

Let `X` be a projective variety over `ℂ`, `ι : C ⟶ X` a smooth projective curve on it with a
point `σ`, and `J` the Jacobian of `C`: a group scheme representing the degree-zero Picard functor
of `C` rigidified along `σ`. The line bundles of `X` form countably many algebraic families
`𝓛ᵢ` on `X ×_ℂ Tᵢ`, `Tᵢ` of finite type over `ℂ`. Restricting each family to `C ×_ℂ Tᵢ`,
rigidifying it along `σ`, and keeping the open and closed part of `Tᵢ` where the restriction has
degree zero gives morphisms `gᵢ : Tᵢ° ⟶ J`. A `ℂ`-point `u` of `Tᵢ°` goes to the point
classifying `𝓛ᵢ|_{X × {u}}` restricted to `C`. So every restriction point of `J`, the class of
`L|_C` for a line bundle `L` on `X`, lies in the image of some `gᵢ`.

Each image closure has dimension at most `h¹(X, 𝒪_X)`, because the differential of `gᵢ` factors
through the Kodaira–Spencer map of the family, valued in `H¹(X, 𝒪_X)`. That bound is isolated
here as the hypothesis `RestrictionFamilyDimensionBound`, about a single family.

## Main definitions

* `MMP.Analytic.SurfaceHodge.rigidifyClass`: the rigidification `c - π^* σ_T^* c` of a Picard
  class on `C ×_S T`.
* `MMP.Analytic.SurfaceHodge.RestrictionFamilyDimensionBound`: the image closure of a morphism
  `T ⟶ J` classifying the restrictions of a family of line bundles on `X` has dimension at most
  `h¹(X, 𝒪_X)`.

## Main results

* `MMP.Analytic.SurfaceHodge.exists_jacobian_family`: a Picard class on `C ×_ℂ T` gives a
  morphism to `J` from the open subscheme of `T` where it has degree zero.
* `MMP.Analytic.SurfaceHodge.exists_families_restriction_isRestrictionPoint`: countably many
  finite-type families `gₖ : Tₖ ⟶ J`, each classifying the restrictions of a family of line
  bundles on `X`, whose images contain every restriction point.
* `MMP.Analytic.SurfaceHodge.exists_families_of_restrictionFamilyDimensionBound`: the same
  families have image closures of dimension at most `h¹(X, 𝒪_X)`, given
  `RestrictionFamilyDimensionBound`.

## Implementation notes

The degree is locally constant on the base by
`AlgebraicGeometry.isLocallyConstant_relativeInvertibleDegreeHom`, since `C ×_ℂ T ⟶ T` is flat,
proper and of finite presentation. Over a `ℂ`-point the rigidifying class is pulled back from
`Pic(Spec ℂ) = 0`, so the class of `g(u)` is the plain restriction of the family.

## References

* [D. Mumford, *Lectures on curves on an algebraic surface*], Lecture 19.
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MMP.Analytic MMP.Analytic.ComplexPoints
open MMP.Intersection.Scheme.Modules (IsLineBundle)

namespace MMP.Analytic.SurfaceHodge

open Stacks.RigidifiedPicard in
/-- The rigidification `c - π^* σ_T^* c` of a Picard class of `C_T`. -/
noncomputable def rigidifyClass {C S : Scheme.{0}} (f : C ⟶ S) (σ : S ⟶ C) (hσ : σ ≫ f = 𝟙 S)
    (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)) : Stacks.Picard.ofScheme (bc f T) :=
  c - Stacks.Picard.schemePullbackClassHom (bcProj f T)
    (Stacks.Picard.schemePullbackClassHom (bcSection f σ hσ T) c)

open Stacks.RigidifiedPicard in
/-- The rigidification is killed by pullback along the induced section `σ_T`. -/
theorem schemePullbackClass_bcSection_rigidifyClass {C S : Scheme.{0}} (f : C ⟶ S) (σ : S ⟶ C)
    (hσ : σ ≫ f = 𝟙 S) (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)) :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) (rigidifyClass f σ hσ T c) = 0 := by
  have h1 := Stacks.Picard.schemePullbackClass_comp (bcSection f σ hσ T) (bcProj f T)
    (Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c)
  rw [bcSection_comp_snd, Stacks.Picard.schemePullbackClass_id] at h1
  change Stacks.Picard.schemePullbackClassHom _ (c - Stacks.Picard.schemePullbackClassHom _ _) = 0
  rw [map_sub]
  exact sub_eq_zero.2 h1.symm

open Stacks.RigidifiedPicard in
/-- Over a `ℂ`-point the rigidification does not change the class. -/
theorem schemePullbackClass_bcMap_rigidifyClass {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ))
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) (T : Over (Spec (.of ℂ)))
    (φ : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ T) (c : Stacks.Picard.ofScheme (bc f T)) :
    Stacks.Picard.schemePullbackClass (bcMap f φ) (rigidifyClass f σ hσ T c) =
      Stacks.Picard.schemePullbackClass (bcMap f φ) c := by
  have h1 := Stacks.Picard.schemePullbackClass_comp (bcMap f φ) (bcProj f T)
    (Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c)
  rw [bcMap_snd, ← Stacks.Picard.schemePullbackClass_comp (bcProj f _),
    Stacks.Picard.eq_zero_of_isField ℂ (Stacks.Picard.schemePullbackClass φ.left _)] at h1
  change Stacks.Picard.schemePullbackClassHom _ (c - Stacks.Picard.schemePullbackClassHom _ _) = _
  rw [map_sub]
  exact sub_eq_self.2 (h1.trans (map_zero (Stacks.Picard.schemePullbackClassHom (bcProj f _))))

open Stacks.RigidifiedPicard in
/-- **From a family of Picard classes to the Jacobian.** Let `C` be a proper flat relative curve
over `ℂ` of finite presentation, with a section `σ`, and `JX` a representative of its
degree-zero rigidified Picard functor. A Picard class `c` on `C ×_ℂ T`, for a finite-type
`ℂ`-scheme `T`, gives an open subscheme `U ⊆ T`, of finite type, and a morphism `g : U ⟶ JX`
sending a `ℂ`-point `u` to the point whose class is `c` restricted to the fibre over `u`; every
`ℂ`-point `t` of `T` over which `c` has degree zero lies in `U`. -/
theorem exists_jacobian_family {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) [IsProper f] [Flat f]
    (hfp : FinitePresentation f) (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ functorZero f hdim σ hσ)
    {T : Scheme.{0}} (p : T ⟶ Spec (.of ℂ)) [QuasiCompact p] [LocallyOfFiniteType p]
    (c : Stacks.Picard.ofScheme (pullback f p)) :
    ∃ (U : Scheme.{0}) (j : U ⟶ T) (_ : QuasiCompact (j ≫ p)) (_ : LocallyOfFiniteType (j ≫ p))
      (g : U ⟶ JX.X.left) (hg : g ≫ JX.X.hom = j ≫ p),
      (∀ (u : Spec (.of ℂ) ⟶ U) (hu : u ≫ j ≫ p = 𝟙 _),
        smallEquiv _ (Multiplicative.toAdd ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom
          (Over.homMk (u ≫ g) (by rw [Category.assoc, hg, hu]; rfl) :
            Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X))).1.1 =
        Stacks.Picard.schemePullbackClass
          (bcMap f (Over.homMk (u ≫ j) (by simpa using hu) :
            Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Over.mk p)) c) ∧
      ∀ (t : Spec (.of ℂ) ⟶ T) (ht : t ≫ p = 𝟙 _)
        (z : (functorZero f hdim σ hσ).obj (op (Over.mk (𝟙 _)))),
        smallEquiv _ (Multiplicative.toAdd z).1.1 =
          Stacks.Picard.schemePullbackClass
            (bcMap f (Over.homMk t ht : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Over.mk p)) c →
        ∃ u : Spec (.of ℂ) ⟶ U, u ≫ j = t := by
  let TT : Over (Spec (.of ℂ)) := Over.mk p
  let rs := (smallEquiv (bc f TT)).symm (rigidifyClass f σ hσ TT c)
  have hrs : rs ∈ group f σ hσ TT := by
    rw [mem_group_iff, AddEquiv.apply_symm_apply]
    exact schemePullbackClass_bcSection_rigidifyClass f σ hσ TT c
  obtain ⟨hlfp, hqc, hqs⟩ := hfp
  have hd : IsLocallyConstant (degree f hdim TT rs) :=
    isLocallyConstant_relativeInvertibleDegreeHom (bcProj f TT)
      ⟨inferInstance, inferInstance, inferInstance⟩
      (topologicalKrullDim_fiber_bcProj_le f hdim TT) _
  let U : T.Opens := ⟨degree f hdim TT rs ⁻¹' {0}, hd.isOpen_fiber 0⟩
  have : CompactSpace TT.left := QuasiCompact.compactSpace_of_compactSpace p
  let φ : Over.mk (U.ι ≫ p) ⟶ TT := Over.homMk U.ι rfl
  let e0 : group f σ hσ (Over.mk (U.ι ≫ p)) := groupMap f σ hσ φ ⟨rs, hrs⟩
  have he0 : e0 ∈ groupZero f hdim σ hσ (Over.mk (U.ι ≫ p)) := by
    rw [mem_groupZero_iff]
    intro u
    rw [coe_groupMap, degree_smallSchemePullbackClassHom_bcMap]
    exact u.2
  let z0 : (functorZero f hdim σ hσ).obj (op (Over.mk (U.ι ≫ p))) := Multiplicative.ofAdd ⟨e0, he0⟩
  let gO : Over.mk (U.ι ≫ p) ⟶ JX.X := (eJ.inv.app (op (Over.mk (U.ι ≫ p)))).hom z0
  refine ⟨U, U.ι, (quasiCompact_iff_compactSpace _).2
    (isCompact_iff_compactSpace.1 (hd.isClosed_fiber 0).isCompact), inferInstance, gO.left,
    Over.w gO, ?_, ?_⟩
  · intro u hu
    let ψ : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Over.mk (U.ι ≫ p) := Over.homMk u hu
    have h1 : (Over.homMk (u ≫ gO.left) (by rw [Category.assoc, Over.w gO]; exact hu) :
        Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X) = ((yonedaGrp.obj JX).map ψ.op).hom gO :=
      Over.OverMorphism.ext rfl
    have h2 : (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (((yonedaGrp.obj JX).map ψ.op).hom gO) =
        ((functorZero f hdim σ hσ).map ψ.op).hom
          ((eJ.hom.app (op (Over.mk (U.ι ≫ p)))).hom gO) :=
      congrArg (fun h => h.hom gO) (eJ.hom.naturality ψ.op)
    have h3 : (eJ.hom.app (op (Over.mk (U.ι ≫ p)))).hom gO = z0 :=
      congrArg (fun h => h.hom z0) (eJ.inv_hom_id_app (op (Over.mk (U.ι ≫ p))))
    rw [h1, h2, h3]
    change smallEquiv _ (Stacks.Picard.smallSchemePullbackClassHom (bcMap f ψ)
      (Stacks.Picard.smallSchemePullbackClassHom (bcMap f φ) rs)) = _
    rw [smallEquiv_smallSchemePullbackClassHom, smallEquiv_smallSchemePullbackClassHom,
      AddEquiv.apply_symm_apply, Stacks.Picard.schemePullbackClass_comp, ← bcMap_comp,
      show ψ ≫ φ = (Over.homMk (u ≫ U.ι) (by simpa using hu) :
        Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Over.mk p) from Over.OverMorphism.ext rfl]
    exact schemePullbackClass_bcMap_rigidifyClass f σ hσ TT _ c
  · intro t ht z hz
    let ψ : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ TT := Over.homMk t ht
    have key : Stacks.Picard.smallSchemePullbackClassHom (bcMap f ψ) rs =
        (Multiplicative.toAdd z).1.1 := by
      apply (smallEquiv _).injective
      rw [smallEquiv_smallSchemePullbackClassHom, AddEquiv.apply_symm_apply,
        schemePullbackClass_bcMap_rigidifyClass, hz]
    have h0 := (mem_groupZero_iff f hdim σ hσ _ _).1 (Multiplicative.toAdd z).2
      (default : Spec (.of ℂ))
    rw [← key, degree_smallSchemePullbackClassHom_bcMap] at h0
    refine ⟨IsOpenImmersion.lift U.ι t ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι, Subsingleton.elim x default]

/-- A line bundle (locally free of rank one) is an invertible `𝒪_X`-module. -/
private theorem isInvertibleModule_of_isLineBundle {X : Scheme.{0}} {L : X.Modules}
    (hL : IsLineBundle L) : Stacks.Ample.IsInvertibleModule X L := by
  refine (AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit X L).2 fun x => ?_
  obtain ⟨U, hxU, ⟨e⟩⟩ := hL x
  exact ⟨U, hxU, ⟨e ≪≫ Limits.coproductUniqueIso _⟩⟩

/-- An invertible `𝒪_X`-module is a line bundle (locally free of rank one). -/
private theorem isLineBundle_of_isInvertibleModule {X : Scheme.{0}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : IsLineBundle L := by
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ :=
    (AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit X L).1 ‹_› x
  exact ⟨U, hxU, ⟨e ≪≫ (Limits.coproductUniqueIso (fun _ : ULift.{0} (Fin 1) =>
    SheafOfModules.unit (U : Scheme.{0}).ringCatSheaf)).symm⟩⟩

/-- A projective variety over `ℂ` carries a very ample line bundle. -/
theorem exists_isLineBundle_isVeryAmple {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] :
    ∃ H : X.Modules, IsLineBundle H ∧ MMP.Intersection.IsVeryAmple ℂ H := by
  obtain ⟨n, i, hi, hover⟩ :=
    (IsProjectiveVariety.isProjective : IsProjectiveMorphism (X ↘ Spec (.of ℂ)))
  let A₀ := (Scheme.Modules.pullback i).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of ℂ)))
  exact ⟨A₀, isLineBundle_of_isInvertibleModule A₀,
    MMP.Resolution.Bridges.isVeryAmple_of_isClosedImmersion ℂ A₀ A₀ (Iso.refl _) n i hover
      (Iso.refl _)⟩

/-- The fibre of `C ×_ℂ T ⟶ X ×_ℂ T` over a `ℂ`-point `u` of `T` is `C ⟶ X` followed by the
inclusion of `X` as the fibre of `X ×_ℂ T` over `u`. -/
theorem bcMap_comp_pullbackMap {X C : Scheme.{0}} [X.Over (Spec (.of ℂ))] (ι : C ⟶ X)
    {T : Scheme.{0}} (p : T ⟶ Spec (.of ℂ)) (u : Spec (.of ℂ) ⟶ T) (hu : u ≫ p = 𝟙 _) :
    Stacks.RigidifiedPicard.bcMap (ι ≫ X ↘ Spec (.of ℂ))
        (Over.homMk u hu : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Over.mk p) ≫
      pullback.map (ι ≫ X ↘ Spec (.of ℂ)) p (X ↘ Spec (.of ℂ)) p ι (𝟙 _) (𝟙 _) (by simp)
        (by simp) =
      pullback.fst (ι ≫ X ↘ Spec (.of ℂ)) (𝟙 _) ≫ ι ≫ pullback.lift (𝟙 X) (X ↘ Spec (.of ℂ) ≫ u)
        (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc]
    erw [pullback.lift_fst, Category.comp_id]
    exact Stacks.RigidifiedPicard.bcMap_fst_assoc _ _ _
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
    erw [Stacks.RigidifiedPicard.bcMap_snd]
    rw [Category.assoc, Category.assoc]
    erw [pullback.lift_snd]
    rw [← Category.assoc ι, ← Category.assoc (pullback.fst _ _), pullback.condition]
    simp only [Over.mk_left, Over.homMk_left, Category.comp_id]
    rfl

/-- Being a line bundle is invariant under isomorphism. -/
private theorem isLineBundle_of_iso {X : Scheme.{0}} {A B : X.Modules} (e : A ≅ B)
    (hA : IsLineBundle A) : IsLineBundle B := by
  intro x
  obtain ⟨U, hx, ⟨f⟩⟩ := hA x
  exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ f⟩⟩

/-- The inclusion of the fibre over `u ≫ j` factors through the base change along `j`. -/
theorem pullbackLift_comp_pullbackMap {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    {T U : Scheme.{0}} (p : T ⟶ Spec (.of ℂ)) (j : U ⟶ T) (u : Spec (.of ℂ) ⟶ U)
    (hu : u ≫ j ≫ p = 𝟙 _) :
    pullback.lift (𝟙 X) (X ↘ Spec (.of ℂ) ≫ u)
        (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp]) ≫
      pullback.map (X ↘ Spec (.of ℂ)) (j ≫ p) (X ↘ Spec (.of ℂ)) p (𝟙 _) j (𝟙 _) (by simp)
        (by simp) =
      pullback.lift (𝟙 X) (X ↘ Spec (.of ℂ) ≫ u ≫ j)
        (by rw [Category.assoc, Category.assoc, hu, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
    erw [pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd]
    rw [Category.assoc]

/-- For a curve `ι : C ⟶ X` on a projective variety over `ℂ`, smooth of
dimension one with a point `σ`, and `JX` the Jacobian of `C`, there are countably many
finite-type `ℂ`-schemes `T k` with Picard classes `c k` on `X ×_ℂ T k` and morphisms
`g k : T k ⟶ JX` over `ℂ` such that
* `g k` sends a `ℂ`-point `u` of `T k` to the point of `JX` classifying the restriction to `C` of
  the class `c k` on the fibre `X ≅ X ×_ℂ {u}`;
* every restriction point of `JX` is the image of a `ℂ`-point under some `g k`. -/
theorem exists_families_restriction_isRestrictionPoint {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] {C : Scheme.{0}}
    (ι : C ⟶ X) [IsClosedImmersion ι] [IsProper (ι ≫ (X ↘ Spec (.of ℂ)))]
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ) :
    ∃ (κ : Type) (_ : Countable κ) (T : κ → Scheme.{0}) (p : ∀ k, T k ⟶ Spec (.of ℂ))
      (_ : ∀ k, QuasiCompact (p k)) (_ : ∀ k, LocallyOfFiniteType (p k))
      (c : ∀ k, Stacks.Picard.ofScheme (pullback (X ↘ Spec (.of ℂ)) (p k)))
      (g : ∀ k, T k ⟶ JX.X.left) (hg : ∀ k, g k ≫ JX.X.hom = p k),
      (∀ k (u : Spec (.of ℂ) ⟶ T k) (hu : u ≫ p k = 𝟙 _),
        Stacks.Picard.schemePullbackClass (pullback.fst (ι ≫ X ↘ Spec (.of ℂ)) (𝟙 _) ≫ ι ≫
            pullback.lift (𝟙 X) (X ↘ Spec (.of ℂ) ≫ u)
              (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp])) (c k) =
          Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
            ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom
              (Over.homMk (u ≫ g k) (by rw [Category.assoc, hg, hu]; rfl) :
                Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X))).1.1) ∧
      ∀ x : ComplexPoints JX.X.hom, IsRestrictionPoint ι _ hdim σ hσ eJ x →
        x.toScheme ∈ ⋃ k, Set.range (g k).base := by
  have : Smooth (ι ≫ X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  have hfp : FinitePresentation (ι ≫ X ↘ Spec (.of ℂ)) :=
    ⟨instLocallyOfFinitePresentationOfSmooth _, inferInstance,
      @IsSeparated.instQuasiSeparated _ _ _ inferInstance⟩
  obtain ⟨H, hH, hHva⟩ := exists_isLineBundle_isVeryAmple (X := X)
  obtain ⟨κ, hκ, T, p, hqc, hlft, 𝓛, h𝓛, hcov⟩ :=
    MMP.exists_countable_isLineBundle_families ℂ X
      ((isProjective_iff_isProjectiveMorphism_of_isAffine _).2 IsProjectiveVariety.isProjective)
      H hH hHva
  let cls𝓛 : ∀ k, Stacks.Picard.ofScheme (pullback (X ↘ Spec (.of ℂ)) (p k)) := fun k =>
    haveI := isInvertibleModule_of_isLineBundle (h𝓛 k)
    AlgebraicGeometry.ExceptionalCurveContraction.cls (𝓛 k)
  let jm : ∀ k, pullback (ι ≫ X ↘ Spec (.of ℂ)) (p k) ⟶ pullback (X ↘ Spec (.of ℂ)) (p k) :=
    fun k => pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  choose U j hqcU hlftU g hg hpt hcovU using fun k =>
    haveI := hqc k
    haveI := hlft k
    exists_jacobian_family (ι ≫ X ↘ Spec (.of ℂ)) hfp hdim σ hσ eJ (p k)
      (Stacks.Picard.schemePullbackClass (jm k) (cls𝓛 k))
  refine ⟨κ, hκ, U, fun k => j k ≫ p k, hqcU, hlftU, fun k =>
    Stacks.Picard.schemePullbackClass (pullback.map (X ↘ Spec (.of ℂ)) (j k ≫ p k)
      (X ↘ Spec (.of ℂ)) (p k) (𝟙 _) (j k) (𝟙 _) (by simp) (by simp)) (cls𝓛 k),
    g, hg, ?_, ?_⟩
  · intro k u hu
    rw [hpt k u hu, show jm k = pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
      Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp]
    erw [bcMap_comp_pullbackMap ι (p k) (u ≫ j k) (by rwa [Category.assoc])]
    rw [Category.assoc, Category.assoc,
      pullbackLift_comp_pullbackMap (X := X) (p k) (j k) u hu]
  · rintro x ⟨y, hy⟩
    let L := (Stacks.Picard.picardRepresentative X.toRingedSpace y).obj
    have hLi : Stacks.Ample.IsInvertibleModule X L :=
      (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
        (Stacks.Picard.picardRepresentative X.toRingedSpace y).property
    obtain ⟨k, t, ht, ⟨e⟩⟩ := hcov L (isLineBundle_of_isInvertibleModule L)
    have := isInvertibleModule_of_isLineBundle (h𝓛 k)
    have := isInvertibleModule_of_isLineBundle
      (isLineBundle_of_iso e (isLineBundle_of_isInvertibleModule L))
    have hyL : y = AlgebraicGeometry.ExceptionalCurveContraction.cls L :=
      (Stacks.Picard.classOf_picardRepresentative _ y).symm
    have hy' : y = Stacks.Picard.schemePullbackClass (pullback.lift (𝟙 X)
        (X ↘ Spec (.of ℂ) ≫ t) (by rw [Category.assoc, ht, Category.comp_id, Category.id_comp]))
        (cls𝓛 k) := by
      rw [hyL, AlgebraicGeometry.ExceptionalCurveContraction.cls_eq_of_iso e,
        AlgebraicGeometry.ExceptionalCurveContraction.schemePullbackClass_cls]
    have hz : Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
        ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2))).1.1 =
        Stacks.Picard.schemePullbackClass (Stacks.RigidifiedPicard.bcMap (ι ≫ X ↘ Spec (.of ℂ))
          (Over.homMk t ht : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Over.mk (p k)))
          (Stacks.Picard.schemePullbackClass (jm k) (cls𝓛 k)) := by
      rw [← hy, hy', show jm k = pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        Stacks.Picard.schemePullbackClass_comp,
        Stacks.Picard.schemePullbackClass_comp, bcMap_comp_pullbackMap, Category.assoc]
    obtain ⟨u, rfl⟩ := hcovU k t ht _ hz
    have hu : u ≫ j k ≫ p k = 𝟙 _ := by rwa [← Category.assoc]
    have hinj : Function.Injective (eJ.hom.app (op (Over.mk (𝟙 (Spec (.of ℂ)))))).hom :=
      fun a b hab => by
        simpa using congrArg (eJ.inv.app (op (Over.mk (𝟙 (Spec (.of ℂ)))))).hom hab
    have heq := hinj (a₁ := (Over.homMk (u ≫ g k) (by rw [Category.assoc, hg k, hu]; rfl) :
        Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X)) (a₂ := Over.homMk x.1 x.2)
      (Multiplicative.toAdd.injective <| Subtype.ext <| Subtype.ext <|
        (Stacks.RigidifiedPicard.smallEquiv _).injective (by rw [hpt k u hu, hz]))
    have hx : x.1 = u ≫ g k := (congrArg CommaMorphism.left heq).symm
    refine Set.mem_iUnion.2 ⟨k, u.base default, ?_⟩
    change _ = x.1.base default
    rw [hx]
    rfl

/-- **The dimension bound for one family of restrictions.** For every finite-type `ℂ`-scheme
`T`, Picard class `c` on `X ×_ℂ T` and morphism `g : T ⟶ JX` over `ℂ` sending each `ℂ`-point `u`
of `T` to the point classifying the restriction to `C` of the class `c` on the fibre over `u`,
the closure of the image of `g` has dimension at most `h¹(X, 𝒪_X)`. -/
def RestrictionFamilyDimensionBound {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] {C : Scheme.{0}}
    (ι : C ⟶ X) [IsClosedImmersion ι] [IsProper (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ) : Prop :=
  ∀ (T : Scheme.{0}) (p : T ⟶ Spec (.of ℂ)) (_ : QuasiCompact p) (_ : LocallyOfFiniteType p)
    (c : Stacks.Picard.ofScheme (pullback (X ↘ Spec (.of ℂ)) p))
    (g : T ⟶ JX.X.left) (hg : g ≫ JX.X.hom = p),
    (∀ (u : Spec (.of ℂ) ⟶ T) (hu : u ≫ p = 𝟙 _),
      Stacks.Picard.schemePullbackClass (pullback.fst (ι ≫ X ↘ Spec (.of ℂ)) (𝟙 _) ≫ ι ≫
          pullback.lift (𝟙 X) (X ↘ Spec (.of ℂ) ≫ u)
            (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp])) c =
        Stacks.RigidifiedPicard.smallEquiv _ (Multiplicative.toAdd
          ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom
            (Over.homMk (u ≫ g) (by rw [Category.assoc, hg, hu]; rfl) :
              Over.mk (𝟙 (Spec (.of ℂ))) ⟶ JX.X))).1.1) →
    topologicalKrullDim (closure (Set.range g.base)) ≤
      Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1)

/-- If the dimension bound `RestrictionFamilyDimensionBound` holds, the restriction points of
the Jacobian lie in the images of countably many morphisms from finite-type `ℂ`-schemes whose
image closures have dimension at most `h¹(X, 𝒪_X)`. -/
theorem exists_families_of_restrictionFamilyDimensionBound {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] {C : Scheme.{0}}
    (ι : C ⟶ X) [IsClosedImmersion ι] [IsProper (ι ≫ (X ↘ Spec (.of ℂ)))]
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    (hbound : RestrictionFamilyDimensionBound ι hdim σ hσ eJ) :
    ∃ (κ : Type) (_ : Countable κ) (T : κ → Scheme.{0}) (p : ∀ k, T k ⟶ Spec (.of ℂ))
      (_ : ∀ k, QuasiCompact (p k)) (_ : ∀ k, LocallyOfFiniteType (p k))
      (g : ∀ k, T k ⟶ JX.X.left), (∀ k, g k ≫ JX.X.hom = p k) ∧
      (∀ k, topologicalKrullDim (closure (Set.range (g k).base)) ≤
        Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
          (SheafOfModules.unit X.ringCatSheaf) 1)) ∧
      ∀ x : ComplexPoints JX.X.hom, IsRestrictionPoint ι _ hdim σ hσ eJ x →
        x.toScheme ∈ ⋃ k, Set.range (g k).base := by
  obtain ⟨κ, hκ, T, p, hqc, hlft, c, g, hg, hpt, hcov⟩ :=
    exists_families_restriction_isRestrictionPoint ι hdim σ hσ eJ
  exact ⟨κ, hκ, T, p, hqc, hlft, g, hg,
    fun k => hbound (T k) (p k) (hqc k) (hlft k) (c k) (g k) (hg k) (hpt k), hcov⟩

end MMP.Analytic.SurfaceHodge
