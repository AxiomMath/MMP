module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeNormal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# Stein factorization of a proper morphism from a variety

Let `f : X ⟶ Y` be a proper morphism of `k`-schemes, `X` a variety and `Y` locally of finite type
over `k`. The Stein factorization `X ⟶ Y' ⟶ Y` of [Stacks, Tag 03H0]
(`Stacks.SteinFactorization.exists_isSteinFactorization`) has `Y'` a variety; `Y'` is projective
when `Y` is, normal when `X` is, and the first factor is projective when `f` is. A curve of `X`
is contracted by `f` exactly when it is contracted by the first factor.

For a proper birational morphism `f : X ⟶ Z` of varieties with `Z` normal, `f_* 𝒪_X = 𝒪_Z`
and all fibres of `f` are connected ([Stacks, Tag 0AY8]).

## Implementation notes

* The factorization is the one of the library: `Y'` is `f.normalization`, the first factor
  `f.toNormalization` and the second `f.fromNormalization`, and the conclusion carries the whole
  of `Stacks.SteinFactorization.IsSteinFactorization` (in particular `Y' = Spec_Y(f_* 𝒪_X)`).
* `f_* 𝒪_X = 𝒪_{Y'}` is stated as `∀ U, IsIso (f'.app U)`, the form of
  `MMP.Mori.IsContraction.isIso_app`; connected fibres as `IsConnected (f' ⁻¹' {y})`.
* "Projective" is H-projectivity, `AlgebraicGeometry.IsProjectiveMorphism`, as in
  `MMP.Mori.IsProjectiveVariety`; "birational" is `MMP.Mori.IsBirationalMorphism`.
* Separatedness of `Y'` over `k` is descended along the surjective universally closed `f'`
  ([Stacks, Tag 09MQ]), so `Y` itself need not be separated.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace MMP.Resolution.Bridges

open MMP.Mori (ProperCurve IsBirationalMorphism IsNormalVariety)

/-- A finite morphism is quasi-projective: the structure sheaf of its source is relatively ample,
the inverse image of an affine open being affine. -/
private theorem isQuasiProjective_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    IsQuasiProjective f := by
  refine ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule X,
    Stacks.Ample.isInvertibleModule_unit X, ?_⟩
  refine (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f
    (Stacks.Ample.unitModule X)).mp ?_
  refine (Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff f).mpr ?_
  intro V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  infer_instance

/-- A finite morphism into a scheme which is H-projective over a field is H-projective over that
field. -/
private theorem isProjectiveMorphism_comp_of_isFinite {k : Type u} [Field k]
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g] (sY : Y ⟶ Spec (.of k))
    (hY : IsProjectiveMorphism sY) : IsProjectiveMorphism (g ≫ sY) := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sY
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sY hY.isHQuasiProjective)
  exact (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective g L hLa (isQuasiProjective_of_isFinite g),
      inferInstance⟩).comp hY

/-- Two points of a fibre of a finite morphism, one specializing to the other, are equal. -/
private theorem eq_of_specializes_of_isFinite {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g]
    {a b : Y'} (hab : a ⤳ b) (hg : g a = g b) : a = b := by
  have : DiscreteTopology (g ⁻¹' {g b}) := (g.isDiscrete_preimage_singleton (g b)).to_subtype
  have hs : (⟨a, hg⟩ : g ⁻¹' {g b}) ⤳ ⟨b, rfl⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp hab
  have := hs.mem_open (isOpen_discrete {⟨b, rfl⟩}) rfl
  exact congrArg Subtype.val this

/-- A proper curve is contracted by `f' ≫ g`, `g` finite, exactly when it is contracted by
`f'`. -/
private theorem isContractedBy_comp_iff {k : Type u} [Field k] {X Y' Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (f' : X ⟶ Y') (g : Y' ⟶ Y) [IsFinite g] :
    C.IsContractedBy (f' ≫ g) ↔ C.IsContractedBy f' := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ by simp [h x hx]⟩
  refine (eq_of_specializes_of_isFinite g
    ((specializes_iff_mem_closure.mpr hx).map f'.continuous) ?_).symm
  simpa only [Scheme.Hom.comp_apply] using (h x hx).symm

/-- The Stein factorization of [Stacks, Tag 03H0] with its canonical witnesses: the
normalization of `S` in `X`, `f.toNormalization` and `f.fromNormalization`. These are the
witnesses of `Stacks.SteinFactorization.exists_isSteinFactorization`, named here so that the
instances on `f.normalization` apply. -/
private noncomputable def steinFactorizationNormalization {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper f] :
    Stacks.SteinFactorization.IsSteinFactorization f f.toNormalization f.fromNormalization where
  comp := Stacks.SteinFactorization.toNormalization_fromNormalization f
  isProper := Stacks.SteinFactorization.isProper_toNormalization f
  geometricallyConnected := Stacks.SteinFactorization.geometricallyConnected_toNormalization f
  isFinite := Stacks.SteinFactorization.isFinite_fromNormalization f
  structureSheaf := Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper f
  relativeSpectrum := Stacks.SteinFactorization.overIsoPushforwardSpectrum_of_isProper f
  relativeSpectrum_hom_left :=
    Stacks.SteinFactorization.toNormalization_overIsoPushforwardSpectrum_hom_left_of_isProper f
  normalization := Iso.refl _
  normalization_hom_left := Category.comp_id _

/-- **Stein factorization and projectivity for a proper morphism from a variety.** Let
`f : X → Y` be a proper morphism with `X` a variety. Then `f = g ∘ f'` where
`Y' = Spec_Y f_* 𝒪_X` is a variety, `f' : X → Y'` is proper and surjective with
`f'_* 𝒪_X = 𝒪_{Y'}` and connected fibres, and `g : Y' → Y` is finite. If `Y` is projective, so is
`Y'`; if `X` is normal, so is `Y'`; if `f` is projective, so is `f'`. In particular (as `g` is
finite) an irreducible curve `C ⊂ X` has `f(C)` a point if and only if `f'(C)` is a point.

Here `X` and `Y` are `k`-schemes through `sX` and `sY`, `Y` locally of finite type over `k`, and
`f` a `k`-morphism. -/
@[mmp "lem_mmp_foundation_variety_stein_factorization"]
theorem exists_steinFactorization_of_isVariety {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) :
    ∃ (Y' : Scheme.{u}) (f' : X ⟶ Y') (g : Y' ⟶ Y),
      Nonempty (Stacks.SteinFactorization.IsSteinFactorization f f' g) ∧
      IsProper f' ∧ Surjective f' ∧ (∀ U : Y'.Opens, IsIso (f'.app U)) ∧
      (∀ y : Y', _root_.IsConnected (f' ⁻¹' {y})) ∧ IsFinite g ∧
      IsVariety k (g ≫ sY) ∧
      (IsProjectiveMorphism sY → MMP.Mori.IsProjectiveVariety k (g ≫ sY)) ∧
      (IsNormal X → IsNormal Y') ∧
      (IsProjectiveMorphism f → IsProjectiveMorphism f') ∧
      ∀ C : ProperCurve sX, C.IsContractedBy f ↔ C.IsContractedBy f' := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hXc : CompactSpace X := (quasiCompact_iff_compactSpace sX).mp inferInstance
  have hS := steinFactorizationNormalization f
  set Y' := f.normalization
  set f' := f.toNormalization
  set g := f.fromNormalization
  have := hS.isProper
  have := hS.geometricallyConnected
  have := hS.isFinite
  have := hS.structureSheaf
  have hcomp := hS.comp
  have hsurj : Surjective f' := ⟨fun y ↦ (f'.isConnected_preimage_singleton y).nonempty⟩
  have hvar : IsVariety k (g ≫ sY) := by
    have : CompactSpace Y' := by
      refine ⟨?_⟩
      have := isCompact_univ.image f'.continuous
      rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj.surj] at this
    have hqc : QuasiCompact (g ≫ sY) := (quasiCompact_iff_compactSpace _).mpr inferInstance
    let φ : Over.mk sX ⟶ Over.mk (g ≫ sY) :=
      Over.homMk f' (by change f' ≫ g ≫ sY = sX; rw [← Category.assoc, hcomp, hf])
    have : Surjective φ.left := hsurj
    have : UniversallyClosed φ.left := (inferInstance : UniversallyClosed f')
    have : IsSeparated (Over.mk sX).hom := (inferInstance : IsSeparated sX)
    have hsep : IsSeparated (g ≫ sY) := isSeparated_of_surjective_universallyClosed φ
    exact ⟨⟩
  refine ⟨Y', f', g, ⟨hS⟩, inferInstance, hsurj, fun U ↦ ?_, f'.isConnected_preimage_singleton,
    inferInstance, hvar, fun hY ↦ ?_, fun hX ↦ ?_, fun hfp ↦ ?_, fun C ↦ ?_⟩
  · exact NatIso.isIso_app_of_isIso f'.c (Opposite.op U)
  · exact (MMP.Mori.isProjectiveVariety_iff k _).mpr
      ⟨hvar, isProjectiveMorphism_comp_of_isFinite g sY hY⟩
  · have : IsNoetherian X := ⟨⟩
    exact isNormal_normalization f fun V _ ↦
      @TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _ _
        (TopologicalSpace.NoetherianSpace.set (V : Set X))
  · rw [← hcomp] at hfp
    exact IsProjectiveMorphism.of_comp f' g hfp
  · rw [← hcomp]
    exact isContractedBy_comp_iff C f' g

/-- **Stein factorization of a proper morphism from a normal variety.** Every proper morphism
`f : X → Z` of varieties, with `X` normal, factors as `X →h W →κ Z` with
`h_* 𝒪_X = 𝒪_W` (connected fibres), `W` normal, and `κ` finite.

The factorization is the Stein factorization of [Stacks, Tag 03H0], so `W = Spec_Z(f_* 𝒪_X)`;
`W` is a normal variety over `k` through `κ ≫ sZ`. -/
@[mmp "lem_mmp_foundation_normal_variety_stein_factorization"]
theorem exists_steinFactorization_of_isNormalVariety {k : Type u} [Field k] {X Z : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hZ : MMP.Mori.IsVariety k sZ) (f : X ⟶ Z) [IsProper f] (hf : f ≫ sZ = sX) :
    ∃ (W : Scheme.{u}) (h : X ⟶ W) (κ : W ⟶ Z),
      Nonempty (Stacks.SteinFactorization.IsSteinFactorization f h κ) ∧
      IsProper h ∧ Surjective h ∧ (∀ U : W.Opens, IsIso (h.app U)) ∧
      (∀ w : W, _root_.IsConnected (h ⁻¹' {w})) ∧ IsFinite κ ∧
      IsNormalVariety k (κ ≫ sZ) := by
  have := hX.1
  have := hX.2
  have := hZ.toLocallyOfFiniteType
  obtain ⟨W, h, κ, hS, hP, hs, hiso, hconn, hfin, hvar, -, hnorm, -, -⟩ :=
    exists_steinFactorization_of_isVariety sX sZ f hf
  exact ⟨W, h, κ, hS, hP, hs, hiso, hconn, hfin, ⟨hvar, hnorm hX.2⟩⟩

/-- A birational morphism of integral schemes, in the sense of rational maps
(`MMP.Mori.IsBirationalMorphism`), is birational in the sense of [Stacks, Tag 01RO]: it maps the
generic point to the generic point and is an isomorphism on the stalks there. -/
theorem isBirational_of_isBirationalMorphism {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    {f : X ⟶ Z} (hb : IsBirationalMorphism f) : IsBirational f := by
  have := hb.isDominant
  have hη : f (genericPoint X) = genericPoint Z := map_genericPoint_of_isDominant f
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hη]
    exact Set.bijOn_singleton.mpr rfl
  · obtain rfl : x = genericPoint X := by
      rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    have : IsIso ((Z.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
        f.stalkMap (genericPoint X)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hb.functionFieldMap_bijective
    exact IsIso.of_isIso_comp_left (Z.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom _

/-- **Proper birational morphisms onto normal varieties.** If `f : X → Z` is a proper birational
morphism of varieties and `Z` is normal, then `f_* 𝒪_X = 𝒪_Z` and all fibres of `f` are
connected ([Stacks, Tag 0AY8]). -/
@[mmp "lem_mmp_foundation_normal_variety_stein_factorization"]
theorem isIso_app_and_isConnected_of_isBirationalMorphism {k : Type u} [Field k]
    {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (hX : MMP.Mori.IsVariety k sX) (hZ : IsNormalVariety k sZ) (f : X ⟶ Z) [IsProper f]
    (hb : IsBirationalMorphism f) :
    (∀ U : Z.Opens, IsIso (f.app U)) ∧ ∀ z : Z, _root_.IsConnected (f ⁻¹' {z}) := by
  have := hX.toIsIntegral
  have := hZ.1.toIsIntegral
  have := hZ.2
  have hbir := isBirational_of_isBirationalMorphism hb
  have hfib : IsIso (f.fiberToSpecResidueField (genericPoint Z)) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational f hbir
  have hfibΓ : IsIso (f.fiberToSpecResidueField (genericPoint Z)).appTop := by
    have : IsIso (f.fiberToSpecResidueField (genericPoint Z)).c :=
      PresheafedSpace.c_isIso_of_iso (f.fiberToSpecResidueField (genericPoint Z)).toPshHom
    exact NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  have hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint Z := fun x hx ↦ by
    simpa [genericPoints_eq_singleton] using hbir.1.mapsTo hx
  have hc : IsIso f.c := Stacks.SteinFactorization.isIso_c_of_isNormal f hgen inferInstance
  refine ⟨fun U ↦ NatIso.isIso_app_of_isIso f.c (Opposite.op U), fun z ↦ ?_⟩
  have : IsIso f.fromNormalization :=
    Stacks.SteinFactorization.isIso_fromNormalization_of_isNormal f hgen hfibΓ
  have := Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper f
  have hpre : f ⁻¹' {z} = f.toNormalization ⁻¹' {(inv f.fromNormalization) z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx : f x = f.fromNormalization (f.toNormalization x) := by
      rw [← Scheme.Hom.comp_apply, Stacks.SteinFactorization.toNormalization_fromNormalization]
    rw [hx]
    constructor
    · rintro rfl
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
    · rintro hx
      rw [hx, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
  rw [hpre]
  exact f.toNormalization.isConnected_preimage_singleton _

end MMP.Resolution.Bridges
