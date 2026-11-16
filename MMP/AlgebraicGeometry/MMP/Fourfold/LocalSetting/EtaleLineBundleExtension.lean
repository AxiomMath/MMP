module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Morphisms.Etale.HenselizationColimit
import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Preimage
import MMP.AlgebraicGeometry.Resolution.EtaleBaseChange
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.HenselianDescent
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical

/-!
# Étale extension of line bundles

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), with `η_T` the generic
point of `T` and `F_{η_T} = Ỹ ×_Y Spec κ(η_T)` the generic scheme fibre of `π : Ỹ ⟶ Y`. For any
line bundles `L_1, …, L_b` on `F_{η_T}` there is a local étale datum
`(Y_e, q, η', L̃_1, …, L̃_b)` (`MMP.Fourfold.LocalEtaleDatum`) whose base-changed resolution
`π_e : Ỹ_e = Ỹ ×_Y Y_e ⟶ Y_e` is again a resolution of singularities: `Ỹ_e` is a smooth
(integral) variety and `π_e` is projective and birational.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_localEtaleDatum_isResolution`

## Implementation notes

* "`Ỹ_e` smooth and integral, `π_e` projective and birational" is
  `MMP.Intersection.IsResolution` for `π_e` over `Y_e`, with `Y_e` over `ℂ` through `q ≫ s_Y`;
  this is the same notion that makes `π` a resolution in `MMP.Fourfold.IsLocalSetting`.
* Line bundles are invertible modules (`Stacks.Ample.IsInvertibleModule`), as in
  `MMP.Fourfold.LocalEtaleDatum`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Mori MMP.Fourfold
open MMP.Resolution.Bridges Opposite

namespace MMP.Fourfold.EtaleLineBundleExtension

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Section

variable {S : Scheme.{0}} {s : S}

private lemma fromSpecResidueField_toBase (U : ElementaryEtaleNeighborhood S s) :
    U.obj.scheme.fromSpecResidueField U.obj.point ≫ U.obj.toBase =
      Spec.map U.obj.residueFieldMap ≫ S.fromSpecResidueField s := by
  rw [EtaleNeighborhood.residueFieldMap_def, Spec.map_comp, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  congr 1
  rw [← Scheme.residueFieldCongr_fromSpecResidueField U.obj.map_point.symm]
  rfl

/-- A morphism `Spec κ(s) ⟶ U` through the residue field of the distinguished point of an
elementary étale neighbourhood `(U, u)` of `(S, s)`, lying over `Spec κ(s) ⟶ S`, is the section
through `u`. -/
private lemma eq_elementaryNeighborhoodSection (U : ElementaryEtaleNeighborhood S s)
    (h : U.obj.scheme.residueField U.obj.point ⟶ S.residueField s)
    (hh : (Spec.map h ≫ U.obj.scheme.fromSpecResidueField U.obj.point) ≫ U.obj.toBase =
      S.fromSpecResidueField s) :
    Spec.map h ≫ U.obj.scheme.fromSpecResidueField U.obj.point =
      elementaryNeighborhoodSection U := by
  haveI : IsIso U.obj.residueFieldMap := U.property
  have key : U.obj.residueFieldMap ≫ h = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono (S.fromSpecResidueField s), Spec.map_comp, Spec.map_id, Category.id_comp,
      Category.assoc, ← fromSpecResidueField_toBase, ← Category.assoc, hh]
  obtain rfl := IsIso.eq_inv_of_hom_inv_id key
  rfl

end Section

/-! ### The limit `Ỹ ×_S Spec Rh` of the `Ỹ ×_S U` -/

section Limit

variable {S : Scheme.{0}} {s : S} {Rh : Type} [CommRing Rh] [IsLocalRing Rh]
  [Algebra (S.presheaf.stalk s) Rh]

private instance (U : AffineElementaryEtaleNeighborhood S s) : IsAffine U.obj.obj.scheme :=
  U.property

variable (s Rh) in
/-- The morphism `Spec Rh ⟶ Spec 𝒪_{S,s}` of the structure map. -/
private noncomputable def specAlg : Spec (CommRingCat.of Rh) ⟶ Spec (S.presheaf.stalk s) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh))

private noncomputable def specLeg (U : AffineElementaryEtaleNeighborhood S s)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh) :
    Spec (CommRingCat.of Rh) ⟶ U.obj.obj.scheme :=
  Spec.map f ≫ U.obj.obj.scheme.isoSpec.inv

private lemma exists_specLeg_eq (U : AffineElementaryEtaleNeighborhood S s)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (hf : IsOverStalk S s Rh U.obj f.hom) :
    ∃ g : U.obj.obj.scheme.presheaf.stalk U.obj.obj.point →+* Rh, IsLocalHom g ∧
      g.comp (stalkMap S s U.obj) = algebraMap (S.presheaf.stalk s) Rh ∧
      specLeg U f = Spec.map (CommRingCat.ofHom g) ≫
        U.obj.obj.scheme.fromSpecStalk U.obj.obj.point := by
  obtain ⟨g, hg, hg', hfg⟩ := hf
  refine ⟨g, hg, hg', ?_⟩
  have hf' : Spec.map f = Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (U.obj.obj.scheme.presheaf.germ ⊤ U.obj.obj.point (Set.mem_univ _)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x; exact congrArg (fun φ => φ x) hfg
  rw [specLeg, hf', Category.assoc, ← IsAffineOpen.fromSpec_top,
    ← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk (isAffineOpen_top _) (Set.mem_univ _)]
  rfl

private lemma specLeg_comp' {U V : AffineElementaryEtaleNeighborhood S s} (a : U ⟶ V)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (f' : Γ(V.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (h : a.hom.hom.hom.appTop ≫ f = f') :
    specLeg U f ≫ a.hom.hom.hom = specLeg V f' := by
  rw [specLeg, specLeg, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
    ← Spec.map_comp, h]

private lemma specLeg_toBase (U : AffineElementaryEtaleNeighborhood S s)
    (f : Γ(U.obj.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (hf : IsOverStalk S s Rh U.obj f.hom) :
    specLeg U f ≫ U.obj.obj.toBase = specAlg s Rh ≫ S.fromSpecStalk s := by
  unfold specAlg
  obtain ⟨g, -, hg', he⟩ := exists_specLeg_eq U f hf
  rw [he, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hg',
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      (Inseparable.of_eq U.obj.obj.map_point.symm).ge]
  simp only [stalkMap, ← Spec.map_comp, ← Category.assoc]
  congr 2

private lemma specLeg_comp {U V : AffineElementaryEtaleNeighborhood S s} (a : U ⟶ V)
    (ι : affineGlobalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh)) :
    specLeg U (ι.app (op U)) ≫ a.hom.hom.hom = specLeg V (ι.app (op V)) := by
  have hn := ι.naturality a.op
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hn
  exact specLeg_comp' a _ _ hn

variable {Yt : Scheme.{0}} (π : Yt ⟶ S)

private abbrev Idx (S : Scheme.{0}) (s : S) := (AffineElementaryEtaleNeighborhood S s)ᵒᵖᵒᵖ

private noncomputable abbrev stage : Idx S s ⥤ Scheme.{0} where
  obj j := pullback π j.unop.unop.obj.obj.toBase
  map g := pullback.map π _ π _ (𝟙 _) g.unop.unop.hom.hom.hom (𝟙 _) (by simp)
    (by simp [g.unop.unop.hom.hom.over])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp g h := by apply pullback.hom_ext <;> simp

private noncomputable def stageFst (j : Idx S s) : (stage π).obj j ⟶ Yt := pullback.fst _ _
private noncomputable def stageSnd (j : Idx S s) : (stage π).obj j ⟶ j.unop.unop.obj.obj.scheme :=
  pullback.snd _ _

private lemma stage_condition (j : Idx S s) :
    stageFst π j ≫ π = stageSnd π j ≫ j.unop.unop.obj.obj.toBase := pullback.condition

private lemma stage_hom_ext {j : Idx S s} {T : Scheme.{0}} {a b : T ⟶ (stage π).obj j}
    (h₁ : a ≫ stageFst π j = b ≫ stageFst π j) (h₂ : a ≫ stageSnd π j = b ≫ stageSnd π j) :
    a = b := pullback.hom_ext h₁ h₂

@[reassoc]
private lemma stage_map_fst {j k : Idx S s} (g : j ⟶ k) :
    (stage π).map g ≫ stageFst π k = stageFst π j :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
private lemma stage_map_snd {j k : Idx S s} (g : j ⟶ k) :
    (stage π).map g ≫ stageSnd π k = stageSnd π j ≫ g.unop.unop.hom.hom.hom :=
  pullback.lift_snd _ _ _

variable (s Rh) in
private noncomputable abbrev limitPt : Scheme.{0} :=
  pullback (pullback.snd π (S.fromSpecStalk s))
    (specAlg s Rh)

variable (ι : affineGlobalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh))
  (hι : ∀ U : (AffineElementaryEtaleNeighborhood S s)ᵒᵖ,
    IsOverStalk S s Rh U.unop.obj (ι.app U).hom)

variable (s) in
private noncomputable def isoSpecHom (j : Idx S s) :
    j.unop.unop.obj.obj.scheme ⟶ ((affineGlobalSections S s).op ⋙ Scheme.Spec).obj j :=
  j.unop.unop.obj.obj.scheme.isoSpec.hom

private instance (j : Idx S s) : IsIso (isoSpecHom s j) :=
  (inferInstance : IsIso j.unop.unop.obj.obj.scheme.isoSpec.hom)

private noncomputable def leg (j : Idx S s) :
    Spec (CommRingCat.of Rh) ⟶ j.unop.unop.obj.obj.scheme :=
  specLeg j.unop.unop (ι.app j.unop)

private lemma leg_comp {j k : Idx S s} (g : j ⟶ k) : leg ι j ≫ g.unop.unop.hom.hom.hom = leg ι k :=
  specLeg_comp g.unop.unop ι

include hι in
private lemma leg_toBase (j : Idx S s) :
    leg ι j ≫ j.unop.unop.obj.obj.toBase = specAlg s Rh ≫ S.fromSpecStalk s :=
  specLeg_toBase _ _ (hι j.unop)

private lemma leg_isoSpec (j : Idx S s) :
    leg ι j ≫ isoSpecHom s j =
      (Scheme.Spec.mapCone (Cocone.mk _ ι).op).π.app j := by
  unfold leg specLeg isoSpecHom
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private lemma leg_spec (j : Idx S s) {T : Scheme.{0}} (b : T ⟶ Spec (CommRingCat.of Rh))
    (t : T ⟶ j.unop.unop.obj.obj.scheme)
    (h : b ≫ (Scheme.Spec.mapCone (Cocone.mk _ ι).op).π.app j =
      t ≫ isoSpecHom s j) : b ≫ leg ι j = t :=
  (cancel_mono (isoSpecHom s j)).1 (by rwa [Category.assoc, leg_isoSpec])

private noncomputable def stageConeπ (j : Idx S s) : limitPt s Rh π ⟶ (stage π).obj j :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ leg ι j) (by
      rw [Category.assoc, Category.assoc, leg_toBase ι hι, pullback.condition,
        ← Category.assoc, pullback.condition, Category.assoc])

@[reassoc]
private lemma stageConeπ_fst (j : Idx S s) : stageConeπ π ι hι j ≫ stageFst π j =
    pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc]
private lemma stageConeπ_snd (j : Idx S s) : stageConeπ π ι hι j ≫ stageSnd π j =
    pullback.snd _ _ ≫ leg ι j := pullback.lift_snd _ _ _

private lemma stageConeπ_comp {j k : Idx S s} (g : j ⟶ k) :
    stageConeπ π ι hι j ≫ (stage π).map g = stageConeπ π ι hι k := by
  apply stage_hom_ext
  · rw [Category.assoc, stage_map_fst, stageConeπ_fst, stageConeπ_fst]
  · rw [Category.assoc, stage_map_snd, stageConeπ_snd_assoc, stageConeπ_snd,
      leg_comp ι g]

private noncomputable abbrev stageCone : Cone (stage (s := s) π) where
  pt := limitPt s Rh π
  π :=
  { app j := stageConeπ π ι hι j
    naturality j k g := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      exact (stageConeπ_comp π ι hι g).symm }

private lemma cone_π_fst_eq [IsFiltered (AffineElementaryEtaleNeighborhood S s)ᵒᵖ]
    (c : Cone (stage (s := s) π)) (j k : Idx S s) :
    c.π.app j ≫ stageFst π j = c.π.app k ≫ stageFst π k := by
  obtain ⟨m, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j.unop k.unop
  rw [← c.w a.op, ← c.w b.op, Category.assoc, Category.assoc, stage_map_fst, stage_map_fst]

private lemma stage_map_snd_isoSpec {j k : Idx S s} (g : j ⟶ k) :
    (stage π).map g ≫ stageSnd π k ≫ isoSpecHom s k =
      stageSnd π j ≫ isoSpecHom s j ≫ ((affineGlobalSections S s).op ⋙ Scheme.Spec).map g := by
  rw [stage_map_snd_assoc]
  exact congrArg (stageSnd π j ≫ ·)
    (Scheme.isoSpec_hom_naturality g.unop.unop.hom.hom.hom).symm

private noncomputable def specCone (c : Cone (stage (s := s) π)) :
    Cone ((affineGlobalSections S s).op ⋙ Scheme.Spec) where
  pt := c.pt
  π :=
  { app j := c.π.app j ≫ stageSnd π j ≫ isoSpecHom s j
    naturality j k g := by
      refine (Category.id_comp _).trans ?_
      rw [← c.w g, Category.assoc, stage_map_snd_isoSpec, Category.assoc, Category.assoc] }

private noncomputable def isLimitStageCone [IsFiltered (AffineElementaryEtaleNeighborhood S s)ᵒᵖ]
    (hc : IsColimit (Cocone.mk _ ι)) : IsLimit (stageCone π ι hι) := by
  have hS : IsLimit (Scheme.Spec.mapCone (Cocone.mk _ ι).op) :=
    isLimitOfPreserves _ hc.op
  let j₀ : Idx S s :=
    op (IsFiltered.nonempty (C := (AffineElementaryEtaleNeighborhood S s)ᵒᵖ)).some
  let ℓ : ∀ c : Cone (stage (s := s) π), c.pt ⟶ Spec (CommRingCat.of Rh) :=
    fun c => hS.lift (specCone π c)
  have hℓ : ∀ (c : Cone (stage (s := s) π)) (j : Idx S s),
      ℓ c ≫ leg ι j = c.π.app j ≫ stageSnd π j :=
    fun c j => leg_spec ι j _ _ (hS.fac (specCone π c) j)
  have hlift : ∀ c : Cone (stage (s := s) π),
      (c.π.app j₀ ≫ stageFst π j₀) ≫ π =
        (ℓ c ≫ specAlg s Rh) ≫
          S.fromSpecStalk s := fun c => by
    rw [Category.assoc, Category.assoc, ← leg_toBase ι hι j₀, ← Category.assoc (ℓ c),
      hℓ, stage_condition, Category.assoc]
  let lift : ∀ c : Cone (stage (s := s) π), c.pt ⟶ limitPt s Rh π := fun c =>
    pullback.lift (pullback.lift (c.π.app j₀ ≫ stageFst π j₀)
      (ℓ c ≫ specAlg s Rh) (hlift c))
      (ℓ c) (pullback.lift_snd _ _ _)
  have hlift_fst : ∀ c, lift c ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      c.π.app j₀ ≫ stageFst π j₀ := fun c => by
    simp only [lift, pullback.lift_fst_assoc, pullback.lift_fst]
  have hlift_snd : ∀ c, lift c ≫ pullback.snd _ _ = ℓ c := fun c => pullback.lift_snd _ _ _
  refine
  { lift := lift
    fac c j := ?_
    uniq c m hm := ?_ }
  · apply stage_hom_ext
    · change lift c ≫ stageConeπ π ι hι j ≫ _ = _
      rw [stageConeπ_fst, hlift_fst]
      exact cone_π_fst_eq π c j₀ j
    · change lift c ≫ stageConeπ π ι hι j ≫ _ = _
      rw [stageConeπ_snd, ← Category.assoc, hlift_snd]
      exact hℓ c j
  · have hm' : ∀ j, m ≫ stageConeπ π ι hι j = c.π.app j := hm
    have hsnd : m ≫ pullback.snd _ _ = ℓ c := by
      refine hS.uniq (specCone π c) _ (fun j => ?_)
      change (m ≫ pullback.snd _ _) ≫ (Scheme.Spec.mapCone (Cocone.mk _ ι).op).π.app j =
        c.π.app j ≫ stageSnd π j ≫ isoSpecHom s j
      rw [← hm' j, Category.assoc, Category.assoc, stageConeπ_snd_assoc, leg_isoSpec]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, ← stageConeπ_fst π ι hι j₀, ← Category.assoc, hm', Category.assoc,
          hlift_fst]
      · rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, Category.assoc,
          pullback.condition, ← Category.assoc, hlift_snd]
    · rw [hsnd, hlift_snd]

private lemma isPullback_stage_map {j k : Idx S s} (g : j ⟶ k) :
    IsPullback (stageSnd π j) ((stage π).map g) g.unop.unop.hom.hom.hom (stageSnd π k) := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := stageFst π k) (v₁₃ := π)
    (h₂₂ := k.unop.unop.obj.obj.toBase) ?_ (stage_map_snd π g)
    (IsPullback.of_hasPullback π _))
  rw [stage_map_fst, g.unop.unop.hom.hom.over]
  exact IsPullback.of_hasPullback π _

private instance isAffineHom_stage_map {j k : Idx S s} (g : j ⟶ k) :
    IsAffineHom ((stage π).map g) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_stage_map π g) inferInstance

private instance compactSpace_stage_obj [QuasiCompact π] (j : Idx S s) :
    CompactSpace ((stage π).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd π j.unop.unop.obj.obj.toBase)

private instance quasiSeparatedSpace_stage_obj [QuasiSeparated π] (j : Idx S s) :
    QuasiSeparatedSpace ((stage π).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd π j.unop.unop.obj.obj.toBase)

include hι in
/-- The composite `Spec κ(s) ⟶ Spec Rh ⟶ U` of a local map `σ : Rh ⟶ κ(s)` over `𝒪_{S,s}` and a
leg is the section of `U` through its distinguished point. -/
private lemma specMap_comp_leg (j : Idx S s) (σ : CommRingCat.of Rh ⟶ S.residueField s)
    [IsLocalHom σ.hom] (hσ : σ.hom.comp (algebraMap _ Rh) = (S.residue s).hom) :
    Spec.map σ ≫ leg ι j = elementaryNeighborhoodSection j.unop.unop.obj := by
  obtain ⟨g, hg, -, he⟩ := exists_specLeg_eq j.unop.unop (ι.app j.unop) (hι j.unop)
  have hc : IsLocalHom (σ.hom.comp g) := RingHom.isLocalHom_comp _ _
  let h : j.unop.unop.obj.obj.scheme.residueField j.unop.unop.obj.obj.point ⟶ S.residueField s :=
    CommRingCat.ofHom (@IsLocalRing.ResidueField.lift _ _ _ _ _ (σ.hom.comp g) hc)
  have key : Spec.map σ ≫ leg ι j =
      Spec.map h ≫ j.unop.unop.obj.obj.scheme.fromSpecResidueField j.unop.unop.obj.obj.point := by
    rw [leg, he, ← Category.assoc, ← Spec.map_comp, Scheme.fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
  have hb : Spec.map σ ≫ specAlg s Rh ≫ S.fromSpecStalk s = S.fromSpecResidueField s := by
    have h₁ : CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh) ≫ σ = S.residue s := by
      ext x; exact congrArg (fun φ => φ x) hσ
    have e₁ : Spec.map σ ≫ specAlg s Rh = Spec.map (S.residue s) :=
      (Spec.map_comp _ _).symm.trans (congrArg Spec.map h₁)
    rw [← Category.assoc, e₁]
    rfl
  rw [key]
  apply eq_elementaryNeighborhoodSection
  rw [← key, Category.assoc, leg_toBase ι hι, hb]

end Limit

/-! ### Integral neighbourhoods -/

section Integral

variable {S : Scheme.{0}} {s : S}

/-- In a Noetherian scheme, a point whose local ring is a domain has an irreducible open
neighbourhood. -/
private lemma exists_isOpen_isIrreducible (X : Scheme.{0}) [NoetherianSpace X] (x : X)
    [IsDomain (X.presheaf.stalk x)] : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsIrreducible V := by
  have hG : IsIrreducible (Set.range (X.fromSpecStalk x)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (X.fromSpecStalk x).continuous.continuousOn
  obtain ⟨C, hC, hGC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hG
  let s : Set (Set X) := {C' | C' ∈ irreducibleComponents X ∧ x ∉ C'}
  have hF : IsClosed (⋃ C' ∈ s, C') :=
    (NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun C' h => isClosed_of_mem_irreducibleComponents _ h.1
  refine ⟨(⋃ C' ∈ s, C')ᶜ, hF.isOpen_compl, ?_, ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun C' h => h.2
  have hVC : (⋃ C' ∈ s, C')ᶜ ⊆ C := by
    intro y hy
    obtain ⟨C'', hC'', hyC''⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
    have hxC'' : x ∈ C'' := by
      by_contra hx
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy
      exact hy C'' ⟨hC'', hx⟩ (hyC'' rfl)
    have hcl := isClosed_of_mem_irreducibleComponents _ hC''
    have hgen := hC''.1.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hgen
    have hgx : hC''.1.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hgen.def]
      exact hxC''
    have hgC : hC''.1.genericPoint ∈ C := hGC (by rw [Scheme.range_fromSpecStalk]; exact hgx)
    have : C'' ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents _ hC).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hgC)
    exact this (hyC'' rfl)
  exact ⟨⟨x, by simpa using fun C' h => h.2⟩, hC.1.2.open_subset hF.isOpen_compl hVC⟩

private lemma exists_isIntegral_hom [IsLocallyNoetherian S] [IsNormal S]
    (U : AffineElementaryEtaleNeighborhood S s) :
    ∃ V : AffineElementaryEtaleNeighborhood S s, IsIntegral V.obj.obj.scheme ∧
      Nonempty (V ⟶ U) := by
  have : IsNormal U.obj.obj.scheme := isNormal_of_etale U.obj.obj.toBase
  have : IsLocallyNoetherian U.obj.obj.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian U.obj.obj.toBase
  have : IsNoetherian U.obj.obj.scheme := {}
  have : IsDomain (U.obj.obj.scheme.presheaf.stalk U.obj.obj.point) :=
    IsNormal.stalk_isDomain _
  obtain ⟨V₀, hV₀, hu, hirr⟩ := exists_isOpen_isIrreducible U.obj.obj.scheme U.obj.obj.point
  obtain ⟨O, hO, huO, hOV⟩ := exists_isAffineOpen_mem_and_subset (X := U.obj.obj.scheme)
    (x := U.obj.obj.point) (U := ⟨V₀, hV₀⟩) hu
  let W : EtaleNeighborhood S s :=
    { scheme := O
      point := ⟨U.obj.obj.point, huO⟩
      toBase := O.ι ≫ U.obj.obj.toBase
      map_point := U.obj.obj.map_point }
  have hW : W.IsElementary := by
    have hU : U.obj.obj.IsElementary := U.obj.property
    change IsIso ((S.residueFieldCongr W.map_point).inv ≫
      W.toBase.residueFieldMap W.point)
    rw [Scheme.residueFieldMap_comp]
    change IsIso (((S.residueFieldCongr U.obj.obj.map_point).inv ≫
      U.obj.obj.toBase.residueFieldMap U.obj.obj.point) ≫ O.ι.residueFieldMap W.point)
    exact IsIso.comp_isIso' hU (inferInstance : IsIso (O.ι.residueFieldMap W.point))
  have hOirr : IsIrreducible (O : Set U.obj.obj.scheme) :=
    ⟨⟨_, huO⟩, hirr.2.open_subset O.isOpen hOV⟩
  have : IrreducibleSpace O := Subtype.irreducibleSpace hOirr
  have : IsIntegral O.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  exact ⟨⟨⟨W, hW⟩, hO⟩, this, ⟨⟨⟨⟨O.ι, rfl, rfl⟩⟩⟩⟩⟩

end Integral

/-! ### The fibre `F_y` as the thickening `F_0` -/

section Fibre

variable {Y Yt : Scheme.{0}} (π : Yt ⟶ Y) (y : Y)

private noncomputable def residueQuotEquiv :
    (Y.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) ≃+*
      IsLocalRing.ResidueField (Y.presheaf.stalk y) :=
  Ideal.quotEquivOfEq (by rw [zero_add, pow_one])

private noncomputable def residueQuotHom : CommRingCat.of (Y.presheaf.stalk y ⧸
    IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) ⟶ Y.residueField y :=
  CommRingCat.ofHom (residueQuotEquiv y).toRingHom

private noncomputable def residueQuotInvHom :
    Y.residueField y ⟶ CommRingCat.of (Y.presheaf.stalk y ⧸
    IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) :=
  CommRingCat.ofHom (residueQuotEquiv y).symm.toRingHom

/-- `Spec κ(y) ⟶ Spec A/𝔪`. -/
private noncomputable def specResidueQuot :
    Spec (Y.residueField y) ⟶ Spec (CommRingCat.of (Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))) :=
  Spec.map (residueQuotHom y)

private noncomputable def specResidueQuotInv :
    Spec (CommRingCat.of (Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))) ⟶ Spec (Y.residueField y) :=
  Spec.map (residueQuotInvHom y)

private lemma specResidueQuotInv_comp : specResidueQuotInv y ≫ specResidueQuot y = 𝟙 _ := by
  rw [specResidueQuotInv, specResidueQuot, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact (residueQuotEquiv y).symm_apply_apply x

private lemma specResidueQuot_comp : specResidueQuot y ≫ specResidueQuotInv y = 𝟙 _ := by
  rw [specResidueQuotInv, specResidueQuot, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact (residueQuotEquiv y).apply_symm_apply x

private lemma specResidueQuot_fromSpecStalk :
    specResidueQuot y ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))) ≫ Y.fromSpecStalk y =
      Y.fromSpecResidueField y := by
  rw [specResidueQuot, ← Category.assoc, ← Spec.map_comp, Scheme.fromSpecResidueField]
  congr 2

/-- `F_y ⟶ F_0`. -/
private noncomputable def fibreToThickening :
    pointSettingFibre π y ⟶ pointSettingThickening π y 0 :=
  pullback.lift (pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ specResidueQuot y ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))))
      (by
        calc pullback.fst _ _ ≫ π = pullback.snd _ _ ≫ Y.fromSpecResidueField y :=
              pullback.condition
          _ = pullback.snd _ _ ≫ specResidueQuot y ≫ Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))) ≫
                Y.fromSpecStalk y := by rw [specResidueQuot_fromSpecStalk]
          _ = _ := by simp only [Category.assoc]; rfl))
    (pullback.snd _ _ ≫ specResidueQuot y) (by rw [pullback.lift_snd, Category.assoc]; rfl)

private noncomputable def thickeningToFibre :
    pointSettingThickening π y 0 ⟶ pointSettingFibre π y :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ specResidueQuotInv y)
    (by
      have h₁ := pullback.condition (f := pullback.snd π (Y.fromSpecStalk y))
        (g := Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))))
      rw [← specResidueQuot_fromSpecStalk y]
      simp only [Category.assoc]
      rw [← Category.assoc (specResidueQuotInv y), specResidueQuotInv_comp, Category.id_comp,
        pullback.condition, ← Category.assoc, h₁, Category.assoc]
      rfl)

private lemma fibreToThickening_fst_fst :
    fibreToThickening π y ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  unfold fibreToThickening
  rw [pullback.lift_fst_assoc, pullback.lift_fst]

private lemma fibreToThickening_snd :
    fibreToThickening π y ≫ pullback.snd _ _ = pullback.snd _ _ ≫ specResidueQuot y :=
  pullback.lift_snd _ _ _

private lemma fibreToThickening_thickeningToFibre :
    fibreToThickening π y ≫ thickeningToFibre π y = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, thickeningToFibre, pullback.lift_fst, fibreToThickening_fst_fst,
      Category.id_comp]
  · rw [Category.assoc, thickeningToFibre, pullback.lift_snd, ← Category.assoc,
      fibreToThickening_snd, Category.assoc, specResidueQuot_comp, Category.comp_id,
      Category.id_comp]

end Fibre

/-! ### A small cofinal family of neighbourhoods -/

section Small

variable {S : Scheme.{0}} {s : S}

/-- An elementary étale neighbourhood whose scheme is `Spec ℂ[x₁, …, xₙ]/I`. -/
private structure SmallNbhd (S : Scheme.{0}) (s : S) where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) ℂ)
  toBase : Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I)) ⟶ S
  point : Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I))
  etale : Etale toBase
  map_point : toBase point = s
  isElementary : IsIso (toBase.residueFieldMap point)

/-- The small neighbourhood as an object of the index category. -/
private noncomputable def SmallNbhd.toIdx (t : SmallNbhd S s) : Idx S s :=
  op (op ⟨⟨@EtaleNeighborhood.mk S s _ t.point t.toBase t.etale t.map_point,
    (EtaleNeighborhood.isElementary_iff _).mpr t.isElementary⟩,
    inferInstanceAs (IsAffine (Spec _))⟩)

/-- Every affine elementary étale neighbourhood of a point of a scheme of finite type over `ℂ`
receives a map from a small one. -/
private lemma exists_smallNbhd_hom (sS : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sS] (X : Idx S s) :
    ∃ t : SmallNbhd S s, Nonempty (t.toIdx ⟶ X) := by
  let U := X.unop.unop
  let Xs := U.obj.obj.scheme
  let φ : CommRingCat.of ℂ ⟶ Γ(Xs, ⊤) :=
    (Scheme.ΓSpecIso (.of ℂ)).inv ≫ (U.obj.obj.toBase ≫ sS).appTop
  have h₁ : (U.obj.obj.toBase ≫ sS).appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  have hft : φ.hom.FiniteType :=
    h₁.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective)
  letI := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Xs, ⊤) := hft
  obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  let e : CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker ψ.toRingHom) ≅ Γ(Xs, ⊤) :=
    (RingHom.quotientKerEquivOfSurjective (f := ψ.toRingHom) hψ).toCommRingCatIso
  let ψS : Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker ψ.toRingHom)) ≅ Xs :=
    (Scheme.Spec.mapIso e.op).symm ≪≫ Xs.isoSpec.symm
  have hu : ψS.hom (ψS.inv U.obj.obj.point) = U.obj.obj.point := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hel : IsIso (U.obj.obj.toBase.residueFieldMap U.obj.obj.point) :=
    (EtaleNeighborhood.isElementary_iff _).mp U.obj.property
  let t : SmallNbhd S s :=
    { n := n
      I := RingHom.ker ψ.toRingHom
      toBase := ψS.hom ≫ U.obj.obj.toBase
      point := ψS.inv U.obj.obj.point
      etale := inferInstance
      map_point := by rw [Scheme.Hom.comp_apply, hu, U.obj.obj.map_point]
      isElementary := by
        rw [Scheme.residueFieldMap_comp]
        have h₂ : IsIso (U.obj.obj.toBase.residueFieldMap (ψS.hom (ψS.inv U.obj.obj.point))) := by
          rwa [hu]
        exact IsIso.comp_isIso' h₂ (inferInstance : IsIso (ψS.hom.residueFieldMap _)) }
  let f : t.toIdx.unop.unop ⟶ U := ⟨⟨⟨ψS.hom, rfl, hu⟩⟩⟩
  exact ⟨t, ⟨f.op.op⟩⟩

end Small

/-! ### The comparison of the fibre maps -/

section FibreMap

variable {Y Yt : Scheme.{0}} (π : Yt ⟶ Y) (y : Y) {Rh : Type} [CommRing Rh] [IsLocalRing Rh]
  [Algebra (Y.presheaf.stalk y) Rh]

/-- The closed immersion `F_0 ⟶ Ỹ ×_Y Spec Rh` induced by an `𝒪_{Y,y}`-algebra map
`ρ : Rh ⟶ 𝒪_{Y,y}/𝔪`. -/
private noncomputable def thickeningToLimit
    (ρ : Rh →ₐ[Y.presheaf.stalk y] Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)) :
    pointSettingThickening π y 0 ⟶ limitPt y Rh π :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ρ.toRingHom)) (𝟙 _)
    (by simp) (by
      rw [Category.comp_id]
      exact (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦
        (ρ.commutes x).symm))).trans (Spec.map_comp _ _))

variable (ι : affineGlobalSections Y y ⟶ (Functor.const _).obj (CommRingCat.of Rh))
  (hι : ∀ U : (AffineElementaryEtaleNeighborhood Y y)ᵒᵖ,
    IsOverStalk Y y Rh U.unop.obj (ι.app U).hom)

include hι in
/-- The identification of `F_y` with the scheme fibre of `Ỹ ×_Y U ⟶ U` over the distinguished
point factors through `F_y = F_0 ⟶ Ỹ ×_Y Spec Rh ⟶ Ỹ ×_Y U`. -/
private lemma localEtaleFibreMap_eq (j : Idx Y y) (σ : CommRingCat.of Rh ⟶ Y.residueField y)
    [IsLocalHom σ.hom] (hσ : σ.hom.comp (algebraMap _ Rh) = (Y.residue y).hom)
    (ρ : Rh →ₐ[Y.presheaf.stalk y] Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))
    (hρ : CommRingCat.ofHom ρ.toRingHom ≫ residueQuotHom y = σ) :
    localEtaleFibreMap π j.unop.unop.obj =
      fibreToThickening π y ≫ thickeningToLimit π y ρ ≫ stageConeπ π ι hι j := by
  apply stage_hom_ext π
  · have h₁ : thickeningToLimit π y ρ ≫ pullback.fst _ _ = pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [Category.assoc, Category.assoc, stageConeπ_fst, reassoc_of% h₁,
      fibreToThickening_fst_fst]
    exact localEtaleFibreMap_fst π _
  · have h₁ : thickeningToLimit π y ρ ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) :=
      pullback.lift_snd _ _ _
    have h₂ : specResidueQuot y ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) = Spec.map σ := by
      rw [specResidueQuot, ← Spec.map_comp, hρ]
    rw [Category.assoc, Category.assoc, stageConeπ_snd, reassoc_of% h₁,
      reassoc_of% (fibreToThickening_snd π y), reassoc_of% h₂, specMap_comp_leg ι hι j σ hσ]
    exact localEtaleFibreMap_snd π _

end FibreMap

/-! ### Henselization data -/

/-- A henselization `Rh` of `𝒪_{S,s}` with the induced maps `σ : Rh ⟶ κ(s)` and
`ρ : Rh ⟶ 𝒪_{S,s}/𝔪`. -/
private lemma exists_henselization_data (S : Scheme.{0}) (s : S) :
    ∃ (Rh : Type) (_ : CommRing Rh) (_ : IsLocalRing Rh) (_ : Algebra (S.presheaf.stalk s) Rh)
      (_ : IsLocalRing.IsHenselization (S.presheaf.stalk s)
        (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh)
      (σ : CommRingCat.of Rh ⟶ S.residueField s) (_ : IsLocalHom σ.hom)
      (_ : σ.hom.comp (algebraMap _ Rh) = (S.residue s).hom)
      (ρ : Rh →ₐ[S.presheaf.stalk s] S.presheaf.stalk s ⧸
        IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ (0 + 1)),
      CommRingCat.ofHom ρ.toRingHom ≫ residueQuotHom s = σ := by
  obtain ⟨Rh, hCR, hAlg, hLR, hLH, hhens, hind, -, hres⟩ :=
    IsLocalRing.exists_henselization (S.presheaf.stalk s)
  letI := hCR; letI := hAlg; letI := hLR; haveI := hLH
  let e : IsLocalRing.ResidueField (S.presheaf.stalk s) ≃+* IsLocalRing.ResidueField Rh :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map (algebraMap (S.presheaf.stalk s) Rh)) hres
  have hH : IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh :=
    { henselian := hhens
      ind_etale := (CommAlgCat.etale _).ind.prop_of_iso
        (CommAlgCat.isoMk (ULift.algEquiv : ULift.{0} _ ≃ₐ[_] _).symm) hind
      exists_residueFieldEquiv := ⟨e, fun x => by simp [e, IsLocalRing.ResidueField.map_residue]⟩ }
  let σ₀ : Rh →+* IsLocalRing.ResidueField (S.presheaf.stalk s) :=
    e.symm.toRingHom.comp (IsLocalRing.residue Rh)
  have hσ₀ : σ₀.comp (algebraMap _ Rh) = IsLocalRing.residue _ := by
    ext x
    change e.symm (IsLocalRing.residue Rh (algebraMap _ Rh x)) = _
    rw [← IsLocalRing.ResidueField.map_residue, RingEquiv.symm_apply_eq]
    rfl
  haveI : IsLocalHom σ₀ := RingHom.isLocalHom_comp _ _
  let ρ : Rh →ₐ[S.presheaf.stalk s] S.presheaf.stalk s ⧸
      IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ (0 + 1) :=
    { toRingHom := (residueQuotEquiv s).symm.toRingHom.comp σ₀
      commutes' := fun x => by
        change (residueQuotEquiv s).symm (σ₀ (algebraMap _ Rh x)) = Ideal.Quotient.mk _ x
        rw [show σ₀ (algebraMap _ Rh x) = IsLocalRing.residue _ x from
          congrArg (fun φ => φ x) hσ₀, RingEquiv.symm_apply_eq]
        rfl }
  refine ⟨Rh, hCR, hLR, hAlg, hH, CommRingCat.ofHom σ₀, ‹_›, hσ₀, ρ, ?_⟩
  ext x
  exact (residueQuotEquiv s).apply_symm_apply (σ₀ x)

/-! ### Descent of the line bundles to an integral neighbourhood -/

open MMP.Fourfold.IsLocalSetting in
/-- **Descent of the line bundles.** In a local setting, line bundles `L_i` on the generic
scheme fibre `F_{η_T}` extend to `Ỹ ×_Y U` for some affine elementary étale neighbourhood
`(U, u)` of `(Y, η_T)` with `U` integral. -/
private lemma exists_isIntegral_bundles
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) {b : ℕ}
    (L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules)
    (hL : ∀ i, Stacks.Ample.IsInvertibleModule _ (L i)) :
    ∃ (V : AffineElementaryEtaleNeighborhood Y (localSettingGenericPoint T))
      (N : Fin b → (pullback π V.obj.obj.toBase).Modules),
      IsIntegral V.obj.obj.scheme ∧ (∀ i, Stacks.Ample.IsInvertibleModule _ (N i)) ∧
      ∀ i, Nonempty ((Scheme.Modules.pullback (localEtaleFibreMap π V.obj)).obj (N i) ≅ L i) := by
  obtain ⟨hvarY, -, -, hprojπ, -⟩ := h.isResolution
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ hprojπ
  -- a henselization `Aʰ` of `A = 𝒪_{Y,η_T}`
  obtain ⟨Ah, _, _, _, _, σ, _, hσ, ρ, hρ⟩ :=
    exists_henselization_data Y (localSettingGenericPoint T)
  -- the line bundles on `F_0`, and their extensions to `Z_{Aʰ}`
  let L₀ : Fin b → (pointSettingThickening π (localSettingGenericPoint T) 0).Modules :=
    fun i => (Scheme.Modules.pullback (thickeningToFibre π _)).obj (L i)
  have hdesc : ∀ i, ∃ (Lh : (limitPt (localSettingGenericPoint T) Ah π).Modules)
      (_ : SheafOfModules.IsInvertible _ _ Lh),
      Nonempty ((Scheme.Modules.pullback (thickeningToLimit π _ ρ)).obj Lh ≅ L₀ i) := fun i =>
    haveI := hL i
    haveI : SheafOfModules.IsInvertible _ _ (L₀ i) := SheafOfModules.isInvertible_pullback _ _
    exists_isInvertible_pullback_henselization_iso h Ah ρ (L₀ i)
  choose Lh hLh eLh using hdesc
  -- `Z_{Aʰ}` is the limit of the `Ỹ ×_Y U`, and the extensions descend to a stage
  obtain ⟨hF, ιc, hover, ⟨hc⟩⟩ :=
    isFiltered_affineElementaryEtaleNeighborhood_and_isColimit Y (localSettingGenericPoint T) Ah
  haveI := hF
  -- restrict to the small neighbourhoods, which form an initial subcategory
  haveI := hvarY
  let G := inducedFunctor (fun t : SmallNbhd Y (localSettingGenericPoint T) => t.toIdx)
  have hcof : ∀ X : Idx Y (localSettingGenericPoint T), ∃ t, Nonempty (G.obj t ⟶ X) :=
    fun X => exists_smallNbhd_hom sY X
  haveI : IsCofiltered (InducedCategory (Idx Y (localSettingGenericPoint T))
      (fun t : SmallNbhd Y (localSettingGenericPoint T) => t.toIdx)) :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful G hcof
  haveI : G.Initial := Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful G hcof
  have hlimG := (Functor.Initial.isLimitWhiskerEquiv G (stageCone π ιc hover)).symm
    (isLimitStageCone π ιc hover hc)
  haveI : ∀ {i j} (f : i ⟶ j), IsAffineHom ((G ⋙ stage π).map f) :=
    fun f => isAffineHom_stage_map π (G.map f)
  haveI : ∀ i, CompactSpace ((G ⋙ stage π).obj i) := fun i => compactSpace_stage_obj π (G.obj i)
  haveI : ∀ i, QuasiSeparatedSpace ((G ⋙ stage π).obj i) :=
    fun i => quasiSeparatedSpace_stage_obj π (G.obj i)
  choose jj M hM eM using fun i =>
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
      (D := G ⋙ stage π) (c := (stageCone π ιc hover).whisker G) hlimG (Lh i) (hLh i)
  -- a common stage, which may be taken integral
  classical
  obtain ⟨j₁, hj₁⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image jj)
  obtain ⟨V, hVint, ⟨a⟩⟩ := exists_isIntegral_hom (G.obj j₁).unop.unop
  let j : Idx Y (localSettingGenericPoint T) := op (op V)
  let g : ∀ i, j ⟶ G.obj (jj i) := fun i =>
    a.op.op ≫ G.map (hj₁ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  let N : Fin b → ((stage π).obj j).Modules := fun i =>
    (Scheme.Modules.pullback ((stage π).map (g i))).obj (M i)
  have eN : ∀ i, Lh i ≅ (Scheme.Modules.pullback (stageConeπ π ιc hover j)).obj (N i) := fun i =>
    (eM i).some ≪≫ (Scheme.Modules.pullbackCongr ((stageCone π ιc hover).w (g i)).symm).app (M i) ≪≫
      ((Scheme.Modules.pullbackComp _ _).app (M i)).symm
  have hfib := localEtaleFibreMap_eq π (localSettingGenericPoint T) ιc hover j σ hσ ρ hρ
  -- the restrictions of the bundles to the fibre
  refine ⟨V, N, hVint, fun i => @SheafOfModules.isInvertible_pullback _ _ _ _ (hM i), fun i => ?_⟩
  exact ⟨(Scheme.Modules.pullbackCongr (hfib.trans (Category.assoc _ _ _).symm)).app (N i) ≪≫
      ((Scheme.Modules.pullbackComp _ _).app (N i)).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (eN i).symm ≪≫
      ((Scheme.Modules.pullbackComp _ _).app (Lh i)).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (eLh i).some ≪≫
      (Scheme.Modules.pullbackComp _ _).app (L i) ≪≫
      (Scheme.Modules.pullbackCongr (fibreToThickening_thickeningToFibre π _)).app (L i) ≪≫
      (Scheme.Modules.pullbackId _).app (L i)⟩

/-! ### Étale base change of the resolution -/

open MMP.Fourfold.IsLocalSetting in
/-- In a local setting, the base change of `π` along an étale morphism `q : U ⟶ Y` from a
variety is a resolution of `U`. -/
private lemma isResolution_pullback_snd
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) {U : Scheme.{0}} (q : U ⟶ Y) [Etale q]
    [AlgebraicGeometry.IsVariety ℂ (q ≫ sY)] :
    MMP.Intersection.IsResolution (q ≫ sY) (pullback.snd π q) := by
  obtain ⟨hvarY, hvarYt, hsmYt, hprojπ, -⟩ := h.isResolution
  haveI := hvarY
  haveI : IsNormal U := isNormal_of_etale q
  have hdense : Dense (smoothLocus sY : Set Y) :=
    (smoothLocus sY).isOpen.dense
      ⟨_, MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus' (k := ℂ) (f := sY)⟩
  haveI := hvarYt
  haveI : Smooth (π ≫ sY) := (MMP.Mori.isSmoothScheme_iff (π ≫ sY)).mp hsmYt
  obtain ⟨hv, hsm, hproj, -, hbir, -⟩ := MMP.Fourfold.isVariety_pullback_snd_of_etale
    (k := ℂ) (s₀ := sY) (sₑ := q ≫ sY) (sW := π ≫ sY) q rfl π rfl
    hprojπ (smoothLocus sY) hdense h.isBiregular
  haveI := hv
  haveI := hsm
  exact ⟨inferInstance, hv, (MMP.Mori.isSmoothScheme_iff _).mpr hsm, hproj, hbir⟩

end

end MMP.Fourfold.EtaleLineBundleExtension

end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Mori

namespace MMP.Fourfold.IsLocalSetting

/-- **Étale extension of line bundles.** In a local setting `(Y, Θ, T, π)`, for any line bundles
`L_1, …, L_b` on the generic scheme fibre `F_{η_T}` there is a local étale datum
`(Y_e, q, η', L̃_1, …, L̃_b)` for which `π_e : Ỹ_e ⟶ Y_e` is a resolution: `Ỹ_e` is a smooth
integral variety and `π_e` is projective and birational. -/
@[mmp "lem_oai4_local_etale_lines"]
public theorem exists_localEtaleDatum_isResolution
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) {b : ℕ}
    (L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules)
    (hL : ∀ i, Stacks.Ample.IsInvertibleModule _ (L i)) :
    ∃ E : LocalEtaleDatum sY T π L,
      MMP.Intersection.IsResolution (E.map ≫ sY) E.resolutionMap := by
  obtain ⟨V, N, hVint, hN, eR⟩ :=
    MMP.Fourfold.EtaleLineBundleExtension.exists_isIntegral_bundles h L hL
  haveI := h.isResolution.1
  haveI : IsAffineHom (V.obj.obj.toBase ≫ sY) := isAffineHom_of_isAffine _
  haveI : AlgebraicGeometry.IsVariety ℂ (V.obj.obj.toBase ≫ sY) := { }
  exact ⟨{ neighborhood := V.obj
           isQuasiProjectiveVariety :=
             ⟨Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom _ inferInstance⟩
           isNormal := isNormal_of_etale V.obj.obj.toBase
           bundle := N
           isInvertibleModule := hN
           restrict := eR },
    MMP.Fourfold.EtaleLineBundleExtension.isResolution_pullback_snd h V.obj.obj.toBase⟩

end MMP.Fourfold.IsLocalSetting
