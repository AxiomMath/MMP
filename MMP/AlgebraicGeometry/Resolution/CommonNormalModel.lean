module

public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate

/-!
# Common normal models and minimal resolutions over the smooth locus

Two results on birational models over a field `k`.

Let `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S` be proper morphisms from normal varieties over `k`, and
let `φ : X₁ ⤏ X₂` be a birational map with `f₂ ∘ φ = f₁`. Then there are a normal variety `Z`
and proper birational morphisms `g₁ : Z ⟶ X₁`, `g₂ : Z ⟶ X₂` with `g₂ = φ ∘ g₁` as rational
maps and `g₁ ≫ f₁ = g₂ ≫ f₂`. One takes for `Z` the normalization of the closure `Γ` of the
graph of a representative `a : W ⟶ X₂` of `φ` in `X₁ ×_S X₂`: the graph is a quasi-compact
immersion, so `W` is an open subscheme of `Γ`; the projections of `Γ` are proper and are open
immersions on `W`, hence birational; and the relation `g₂ = a ∘ g₁` holds on a dense open and
extends since `f₂` is separated and `Z` is reduced.

Let `k` be algebraically closed, `X` a normal surface over `k` and `f : Y ⟶ X` a minimal
resolution, i.e. a resolution of `X` none of whose exceptional curves is a smooth rational
curve of self-intersection `-1`. Then `f` restricts to an isomorphism `f⁻¹(V) ⟶ V` over the
smooth locus `V` of `X`: over `V`, `f` is a proper birational morphism of smooth surfaces, hence
a composite of point blow-ups, and the exceptional curve of the last blow-up would be an
`f`-exceptional `(-1)`-curve.

## Main results

* `MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism`: the common normal model.
* `MMP.Mori.isIso_morphismRestrict_smoothLocus_of_isMinimalSurfaceResolution`: a minimal
  resolution of a normal surface is an isomorphism over the smooth locus.

## Implementation notes

The base `S` is an arbitrary scheme. The condition `f₂ ∘ φ = f₁` is
`φ.compHom f₂ = f₁.toRationalMap`. The relation `g₂ = φ ∘ g₁` of rational maps is stated
through a representative `φ'` of `φ`: on the open `g₁⁻¹(dom φ')`, which is dense since `g₁`
is birational, `g₂` agrees with `g₁` followed by `φ'`. The variety structure of `Z` is the one
induced by `g₁`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, proofs of 3.38,
  3.51 and 3.52; 4.5, 4.7.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

universe u

section CommonNormalModel

open Limits

/-- An open immersion with nonempty source into a preirreducible scheme is dominant. -/
private lemma isDominant_of_isOpenImmersion {T B : Scheme.{u}} [PreirreducibleSpace B]
    (s : T ⟶ B) [IsOpenImmersion s] [Nonempty T] : IsDominant s :=
  ⟨s.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- The target of a dominant morphism from an irreducible scheme is irreducible. -/
private lemma irreducibleSpace_of_isDominant {A B : Scheme.{u}} [IrreducibleSpace A]
    (f : A ⟶ B) [IsDominant f] : IrreducibleSpace B := by
  have h := (IrreducibleSpace.isIrreducible_univ A).image f f.continuous.continuousOn
  rw [Set.image_univ] at h
  have h' := h.closure
  rw [f.denseRange.closure_range] at h'
  exact (irreducibleSpace_def _).mpr h'

/-- A quasi-compact morphism is scheme-theoretically dominant onto its scheme-theoretic image. -/
private lemma isSchemeTheoreticallyDominant_toImage {A B : Scheme.{u}} (f : A ⟶ B)
    [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : B.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U, U.2.preimage f.imageι⟩) ?_ ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top B, Scheme.Hom.preimage_top]
  · intro U
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism `a : A ⟶ B` to an irreducible scheme is birational as soon as some open
immersion `s : T ⟶ A` with dense image and nonempty source makes `s ≫ a` an open immersion. -/
private lemma isBirationalMorphism_of_isOpenImmersion_comp {T A B : Scheme.{u}}
    [IrreducibleSpace B] (a : A ⟶ B) (s : T ⟶ A) [IsOpenImmersion s] [IsDominant s]
    [Nonempty T] [IsOpenImmersion (s ≫ a)] : IsBirationalMorphism a := by
  have := isDominant_of_isOpenImmersion (s ≫ a)
  refine ⟨⟨s.opensRange, s.denseRange, (s ≫ a).opensRange, (s ≫ a).denseRange,
    s.isoOpensRange.symm ≪≫ (s ≫ a).isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.Hom.toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  have hle : s.opensRange ≤ a.toPartialMap.domain := le_top
  refine ⟨s.opensRange, s.denseRange, le_rfl, hle, ?_⟩
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A birational morphism is an open immersion on some dense open. -/
private lemma exists_isOpenImmersion_of_isBirationalMorphism {A B : Scheme.{u}} {a : A ⟶ B}
    (h : IsBirationalMorphism a) :
    ∃ T : A.Opens, Dense (T : Set A) ∧ IsOpenImmersion (T.ι ≫ a) := by
  obtain ⟨e, he⟩ := h
  rw [Scheme.PartialIso.toRationalMap, Scheme.Hom.toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨T, hT, h₁, h₂, heq⟩ := he
  refine ⟨T, hT, ?_⟩
  have h₁' : T ≤ e.source := h₁
  have : T.ι ≫ a = A.homOfLE h₁' ≫ e.iso.hom ≫ e.target.ι := by
    simpa using heq.symm
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given proper morphisms `f₁ : X₁ ⟶ S`, `f₂ : X₂ ⟶ S` from normal `k`-varieties and a birational
map `φ : X₁ ⤏ X₂` with `f₂ ∘ φ = f₁`, there are a normal variety `Z` (with structure morphism
`g₁ ≫ sX₁`) and proper birational morphisms `g₁ : Z ⟶ X₁`, `g₂ : Z ⟶ X₂` such that `g₂` agrees
with `φ ∘ g₁` on the preimage of the domain of a representative of `φ`, and
`g₁ ≫ f₁ = g₂ ≫ f₂`. -/
@[mmp "lem_km3c_common_normal_model"]
public theorem exists_isNormalVariety_isProper_isBirationalMorphism {k : Type u} [Field k]
    {X₁ X₂ S : Scheme.{u}} {sX₁ : X₁ ⟶ Spec (.of k)} {sX₂ : X₂ ⟶ Spec (.of k)}
    (hX₁ : IsNormalVariety k sX₁) (hX₂ : IsNormalVariety k sX₂)
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) [IsProper f₁] [IsProper f₂]
    (φ : RationalMap X₁ X₂) (hφ : φ.IsBirational) (hφS : φ.compHom f₂ = f₁.toRationalMap) :
    ∃ (Z : Scheme.{u}) (g₁ : Z ⟶ X₁) (g₂ : Z ⟶ X₂),
      IsNormalVariety k (g₁ ≫ sX₁) ∧
      IsProper g₁ ∧ IsProper g₂ ∧ IsBirationalMorphism g₁ ∧ IsBirationalMorphism g₂ ∧
      (∃ φ' : X₁.PartialMap X₂, φ'.toRationalMap = φ ∧
        (g₁ ⁻¹ᵁ φ'.domain).ι ≫ g₂ = (g₁ ∣_ φ'.domain) ≫ φ'.hom) ∧
      g₁ ≫ f₁ = g₂ ≫ f₂ := by
  have hV₁ : AlgebraicGeometry.IsVariety k sX₁ := hX₁.1
  have hV₂ : AlgebraicGeometry.IsVariety k sX₂ := hX₂.1
  have : IsLocallyNoetherian (Spec (.of k)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian sX₁
  obtain ⟨e, rfl⟩ := hφ
  rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hφS
  obtain ⟨W, hW, hWl, hWr, hWeq⟩ := hφS
  -- the representative `a` of `φ` on `W`, where `f₂ ∘ φ = f₁` holds
  have hWl' : W ≤ e.source := hWl
  let a : W.toScheme ⟶ X₂ := X₁.homOfLE hWl' ≫ e.iso.hom ≫ e.target.ι
  have hcomm : W.ι ≫ f₁ = a ≫ f₂ := by
    simp only [a, Category.assoc]
    simpa using hWeq.symm
  have : IsOpenImmersion a := by
    dsimp only [a]
    infer_instance
  have : Nonempty W := hW.nonempty.to_subtype
  -- the graph `j : W ⟶ X₁ ×_S X₂` and its closure `Γ`
  let j : W.toScheme ⟶ pullback f₁ f₂ := pullback.lift W.ι a hcomm
  have hj₁ : j ≫ pullback.fst f₁ f₂ = W.ι := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd f₁ f₂ = a := pullback.lift_snd _ _ _
  have : IsImmersion j := by
    have : IsImmersion (j ≫ pullback.fst f₁ f₂) := by rw [hj₁]; infer_instance
    exact IsImmersion.of_comp j (pullback.fst f₁ f₂)
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ pullback.fst f₁ f₂) := by rw [hj₁]; infer_instance
    -- explicit instances: an unguided search for `QuasiSeparated (pullback.fst f₁ f₂)` with the
    -- current imports wanders through `ValuativeCommSq` families and times out
    have : IsSeparated (pullback.fst f₁ f₂) :=
      MorphismProperty.pullback_fst (P := @IsSeparated) f₁ f₂ (inferInstanceAs (IsSeparated f₂))
    have : QuasiSeparated (pullback.fst f₁ f₂) := IsSeparated.instQuasiSeparated _
    exact QuasiCompact.of_comp j (pullback.fst f₁ f₂)
  let Γ := j.image
  let t : W.toScheme ⟶ Γ := j.toImage
  let i : Γ ⟶ pullback f₁ f₂ := j.imageι
  have hti : t ≫ i = j := j.toImage_imageι
  have : IrreducibleSpace Γ := irreducibleSpace_of_isDominant t
  have := isSchemeTheoreticallyDominant_toImage j
  have : IsReduced Γ := IsSchemeTheoreticallyDominant.isReduced t
  have : IsIntegral Γ := isIntegral_of_irreducibleSpace_of_isReduced Γ
  let p₁ : Γ ⟶ X₁ := i ≫ pullback.fst f₁ f₂
  let p₂ : Γ ⟶ X₂ := i ≫ pullback.snd f₁ f₂
  have : AlgebraicGeometry.IsVariety k (p₁ ≫ sX₁) := {}
  have ht₁ : t ≫ p₁ = W.ι := by simp only [p₁, reassoc_of% hti, hj₁]
  have ht₂ : t ≫ p₂ = a := by simp only [p₂, reassoc_of% hti, hj₂]
  -- the open `O = t(W)` of `Γ`, on which both projections are open immersions
  let O := t.opensRange
  have hO₁ : O.ι ≫ p₁ = t.isoOpensRange.inv ≫ W.ι := by
    rw [← t.isoOpensRange_inv_comp, Category.assoc, ht₁]
  have hO₂ : O.ι ≫ p₂ = t.isoOpensRange.inv ≫ a := by
    rw [← t.isoOpensRange_inv_comp, Category.assoc, ht₂]
  -- the normalization `ν : Z ⟶ Γ`
  obtain ⟨⟨hZvar, hZnorm, hfin, hsurj, hνbir⟩, -⟩ := MMP.Threefold.normalization_spec (p₁ ≫ sX₁)
  generalize Γ.normalization _ = ν at hZvar hfin hsurj hνbir
  generalize Γ.normalizationScheme _ = Z at ν hZvar hZnorm
  have : AlgebraicGeometry.IsIntegral Z := hZvar.toIsIntegral
  -- a dense open `T` of `Z` on which `ν` is an open immersion into `O`
  obtain ⟨D, hD, hDi⟩ := exists_isOpenImmersion_of_isBirationalMorphism hνbir
  let c : D.toScheme ⟶ Γ := D.ι ≫ ν
  have : Nonempty D := hD.nonempty.to_subtype
  let T : D.toScheme.Opens := c ⁻¹ᵁ O
  have : Nonempty T := by
    obtain ⟨y, ⟨d, rfl⟩, ⟨w, hw⟩⟩ := nonempty_preirreducible_inter c.isOpenEmbedding.isOpen_range
      O.isOpen (Set.range_nonempty c) ⟨t (Classical.arbitrary W), ⟨_, rfl⟩⟩
    exact ⟨⟨d, ⟨w, hw⟩⟩⟩
  let sT : T.toScheme ⟶ Z := T.ι ≫ D.ι
  have : IsDominant sT := isDominant_of_isOpenImmersion sT
  have hsT : sT ≫ ν = (c ∣_ O) ≫ O.ι := by
    simp only [sT, Category.assoc, morphismRestrict_ι]; rfl
  have hbir {X : Scheme.{u}} [IrreducibleSpace X] (p : Γ ⟶ X) (b : W.toScheme ⟶ X)
      [IsOpenImmersion b] (hp : O.ι ≫ p = t.isoOpensRange.inv ≫ b) :
      IsBirationalMorphism (ν ≫ p) := by
    have : IsOpenImmersion (sT ≫ ν ≫ p) := by rw [reassoc_of% hsT, hp]; infer_instance
    exact isBirationalMorphism_of_isOpenImmersion_comp _ sT
  have hf : (ν ≫ p₁) ≫ f₁ = (ν ≫ p₂) ≫ f₂ := by
    simp only [p₁, p₂, Category.assoc, pullback.condition]
  refine ⟨Z, ν ≫ p₁, ν ≫ p₂, ⟨by simpa only [Category.assoc] using hZvar, hZnorm⟩,
    inferInstance, inferInstance, hbir p₁ W.ι hO₁, hbir p₂ a hO₂, ⟨⟨W, hW, a⟩, ?_, ?_⟩, hf⟩
  · exact e.toPartialMap.restrict_toRationalMap W hW hWl
  · change ((ν ≫ p₁) ⁻¹ᵁ W).ι ≫ ν ≫ p₂ = ((ν ≫ p₁) ∣_ W) ≫ a
    let V : Z.Opens := ν ⁻¹ᵁ O
    have hV : V ≤ (ν ≫ p₁) ⁻¹ᵁ W := by
      rintro x ⟨w, hw⟩
      change (ν ≫ p₁) x ∈ W
      rw [Scheme.Hom.comp_apply, ← hw, ← Scheme.Hom.comp_apply, ht₁]
      exact w.2
    have : Nonempty V := by
      obtain ⟨x, hx⟩ := ν.surjective (t (Classical.arbitrary W))
      exact ⟨⟨x, ⟨_, hx.symm⟩⟩⟩
    have : IrreducibleSpace ((ν ≫ p₁) ⁻¹ᵁ W) := by
      obtain ⟨⟨x, hx⟩⟩ := this
      exact Subtype.irreducibleSpace ⟨⟨x, hV hx⟩,
        (IrreducibleSpace.isIrreducible_univ Z).isPreirreducible.open_subset
          ((ν ≫ p₁) ⁻¹ᵁ W).isOpen (Set.subset_univ _)⟩
    have := isDominant_of_isOpenImmersion (Z.homOfLE hV)
    have hres : Z.homOfLE hV ≫ ((ν ≫ p₁) ∣_ W) = (ν ∣_ O) ≫ t.isoOpensRange.inv := by
      rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
        Category.assoc, ← hO₁, morphismRestrict_ι_assoc]
    refine ext_of_isDominant_of_isSeparated f₂ ?_ (Z.homOfLE hV) ?_
    · have hf' : ν ≫ p₁ ≫ f₁ = ν ≫ p₂ ≫ f₂ := by simpa only [Category.assoc] using hf
      simp only [Category.assoc, ← hcomm, morphismRestrict_ι_assoc, hf']
    · rw [reassoc_of% hres, ← hO₂, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc]

end CommonNormalModel

section MinimalResolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Threefold.Resolution Stacks.Intersection

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Every source of a chain of point blow-ups of a smooth surface is a smooth surface. -/
private theorem isSmoothSurface_of_pointBlowupChain [IsAlgClosed k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) (hW : Mori.IsVariety k sW) [Smooth sW]
    (hWd : topologicalKrullDim W = 2) {Z : Scheme.{u}} {h : Z ⟶ W}
    (hh : Stacks.ResolutionOfSurfaces.PointBlowupChain W Set.univ Z h) :
    Mori.IsVariety k (h ≫ sW) ∧ Smooth (h ≫ sW) ∧ topologicalKrullDim Z = 2 := by
  induction hh with
  | refl => simpa using ⟨hW, ‹Smooth sW›, hWd⟩
  | step hh w hw _ ih =>
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    obtain ⟨h₁, h₂, h₃, -⟩ :=
      isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve _ ih₁ ih₃ hw
    simp only [Category.assoc]
    exact ⟨h₁, h₂, h₃⟩

/-- The nonempty smooth locus of a variety of dimension two over `k` is a smooth surface. -/
private theorem isSmoothSurface_smoothLocus (sX : X ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX)
    (hdim : topologicalKrullDim X = 2) (hV : smoothLocus sX ≠ ⊥) :
    Mori.IsVariety k ((smoothLocus sX).ι ≫ sX) ∧ Smooth ((smoothLocus sX).ι ≫ sX) ∧
      topologicalKrullDim (smoothLocus sX) = 2 := by
  have : Nonempty (smoothLocus sX) := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hV
    exact ⟨⟨x, hx⟩⟩
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  refine ⟨RationalEquivalenceProduct.isVariety_opens_ι k sX _,
    ?_, (RationalEquivalenceProduct.topologicalKrullDim_opens k sX _).trans hdim⟩
  rw [smoothLocus_eq_smoothLocus, ← Scheme.Hom.smoothLocus_eq_top_iff,
    ← Scheme.Hom.preimage_smoothLocus_eq]
  simp

/-- The preimage of a nonempty open of a variety under a resolution is a smooth surface, when the
target is a surface. -/
private theorem isSmoothSurface_preimage (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) (f : Y ⟶ X) (hf : IsSmoothResolution sX f)
    (V : X.Opens) (hV : V ≠ ⊥) :
    Mori.IsVariety k ((f ⁻¹ᵁ V).ι ≫ f ≫ sX) ∧ IsSmoothScheme ((f ⁻¹ᵁ V).ι ≫ f ≫ sX) ∧
      topologicalKrullDim (f ⁻¹ᵁ V) = 2 := by
  obtain ⟨⟨hY, -⟩, hYd, -⟩ := hf.isNormalVariety hX
  have := hf.isBirationalMorphism.isDominant
  have : Nonempty (f ⁻¹ᵁ V) := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hV
    obtain ⟨y, hy⟩ := f.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
    exact ⟨⟨y, hy⟩⟩
  have : Smooth (f ≫ sX) := (Mori.isSmoothScheme_iff _).mp hf.isSmoothScheme
  exact ⟨RationalEquivalenceProduct.isVariety_opens_ι k (f ≫ sX) _,
    (Mori.isSmoothScheme_iff _).mpr inferInstance,
    (RationalEquivalenceProduct.topologicalKrullDim_opens k (f ≫ sX) _).trans
      (hYd.trans hdim)⟩

/-- A prime divisor whose reduced subscheme is one-dimensional and proper over `k` is a proper
curve, at its generic point. -/
private theorem isProperCurve_genericPoint {W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W]
    (s : W ⟶ Spec (.of k)) (P : Mori.PrimeDivisor W)
    (hdim : topologicalKrullDim P.idealSheaf.subscheme = 1)
    [IsProper (P.idealSheaf.subschemeι ≫ s)] : IsProperCurve s P.genericPoint := by
  obtain ⟨e, he⟩ := exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf P)
  refine ⟨?_, ?_⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact hdim
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {P.genericPoint})).subschemeι ≫ s)
    rw [← he, Category.assoc]
    infer_instance

open MMP.Threefold.Mori in
/-- Intersection numbers of a prime divisor with a proper curve may be computed on an open
subscheme `j : Z ⟶ W` containing the curve: `(P · C_Z) = (j_* P · C)`. -/
private theorem intersectionNumber_single_primeDivisorMap {W Z : Scheme.{u}}
    {s : W ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian W] [IsNormal W]
    (hsm : IsSmoothScheme s) (j : Z ⟶ W) [IsOpenImmersion j] [QuasiCompact (j ≫ s)]
    [IsLocallyNoetherian Z] [IsNormal Z] (hsmZ : IsSmoothScheme (j ≫ s))
    (P : Mori.PrimeDivisor Z) (CZ : ProperCurve (j ≫ s)) (C : ProperCurve s)
    (hC : j CZ.point = C.point) (hCZ : closure ({C.point} : Set W) ⊆ Set.range j) :
    (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k (j ≫ s) CZ.ι CZ.dim_le
        (isQCartier_single_of_isSmoothScheme hsmZ P) =
      (Divisor.toQDivisor (Finsupp.single (OpenWeilRestriction.primeDivisorMap j P) 1)
        ).intersectionNumber k s C.ι C.dim_le (isQCartier_single_of_isSmoothScheme hsm _) := by
  set P' := OpenWeilRestriction.primeDivisorMap j P
  have := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P'
  have := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsmZ P
  have hcomap : P'.idealSheaf.comap j = P.idealSheaf := by
    rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf,
      ← vanishingIdeal_closure_genericPoint_eq_idealSheaf P,
      show Mori.PrimeDivisor.genericPoint P' = j P.genericPoint from
        OpenWeilRestriction.genericPoint_primeDivisorMap j P]
    exact comap_vanishingIdeal_closure_singleton j _
  have : Stacks.Divisors.IsPullbackDefined j P'.idealSheaf := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (P'.idealSheaf.comap j)
    rw [hcomap]; infer_instance
  rw [intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsm P' C,
    intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsmZ P CZ]
  obtain ⟨e, he⟩ := exists_curveSubschemeAt_iso j CZ.point hC hCZ
  have : IsProper ((CZ.ι ≫ j) ≫ s) := by rw [Category.assoc]; infer_instance
  have h1 := degreeOn_eq_of_iso_comp k s C.ι (CZ.ι ≫ j) C.dim_le CZ.dim_le e.symm (by
    rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm)
    (Stacks.Divisors.invertibleSheaf' P'.idealSheaf : W.Modules)
  have h2 := degreeOn_comp k s j CZ.ι CZ.dim_le
    (Stacks.Divisors.invertibleSheaf' P'.idealSheaf : W.Modules)
  obtain ⟨e₂⟩ := nonempty_invertibleSheaf'_iso_of_eq hcomap
  have h3 := Mori.degreeOn_eq_of_iso k (j ≫ s) CZ.ι CZ.dim_le
    (Stacks.Divisors.invertibleSheafPullbackIso j P'.idealSheaf ≪≫ e₂)
  refine congrArg (fun n : ℤ => (n : ℚ)) ?_
  exact (h1.trans (h2.trans h3)).symm

open MMP.Threefold.Mori in
/-- A `(-1)`-curve on an open subscheme of `Y` that `f` contracts to a point is an `f`-exceptional
`(-1)`-curve of `Y`, so `f` is not a minimal resolution. -/
private theorem not_isMinimalSurfaceResolution_of_isMinusOneCurve (sX : X ⟶ Spec (.of k))
    (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (f ≫ sX)] {Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (sZ : Z ⟶ Spec (.of k)) (hsZ : j ≫ f ≫ sX = sZ) [QuasiCompact sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (hsmZ : IsSmoothScheme sZ) (F : Mori.PrimeDivisor Z)
    (hF : IsMinusOneCurve sZ F) (x : X) (hx : (j ≫ f).base '' (F.support : Set Z) ⊆ {x}) :
    ¬ IsMinimalSurfaceResolution sX f := by
  subst hsZ
  rintro ⟨hf, hmin⟩
  apply hmin
  have hsm : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  set E := OpenWeilRestriction.primeDivisorMap j F
  set η := F.genericPoint
  have hEη : E.genericPoint = j η := OpenWeilRestriction.genericPoint_primeDivisorMap j F
  obtain ⟨hprop, ⟨eF, heF⟩, hnum⟩ := hF
  have hηF : η ∈ (F.support : Set Z) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have : IsProper (F.idealSheaf.subschemeι ≫ j) := by
    have : IsProper ((F.idealSheaf.subschemeι ≫ j) ≫ f ≫ sX) := by
      simpa only [Category.assoc] using hprop
    exact IsProper.of_comp _ (f ≫ sX)
  have hclosed : IsClosed (j.base '' (F.support : Set Z)) := by
    have h := (F.idealSheaf.subschemeι ≫ j).isClosedMap.isClosed_range
    convert h using 1
    show j.base '' (F.idealSheaf.support : Set Z) = _
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.range_comp]
    rfl
  have hEsupp : (E.support : Set Y) ⊆ j.base '' (F.support : Set Z) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hEη]
    exact closure_minimal (Set.singleton_subset_iff.2 ⟨η, hηF, rfl⟩) hclosed
  have hfE : ∀ z ∈ (E.support : Set Y), f z = x := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := hEsupp hz
    exact hx ⟨w, hw, rfl⟩
  have hErange : closure ({E.genericPoint} : Set Y) ⊆ Set.range j := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hEsupp.trans (Set.image_subset_range _ _)
  obtain ⟨e₁, he₁⟩ :=
    exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf F)
  obtain ⟨e₂, he₂⟩ := exists_curveSubschemeAt_iso j η hEη.symm hErange
  obtain ⟨e₃, he₃⟩ :=
    exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf E)
  let eE : F.idealSheaf.subscheme ≅ E.idealSheaf.subscheme := e₁.symm ≪≫ e₂ ≪≫ e₃
  have heE : eE.hom ≫ E.idealSheaf.subschemeι = F.idealSheaf.subschemeι ≫ j := by
    simp only [eE, Iso.trans_hom, Iso.symm_hom, Category.assoc, he₃, he₂]
    rw [← Category.assoc]
    congr 1
    rw [Iso.inv_comp_eq]
    exact he₁.symm
  have hdimP : topologicalKrullDim (projectiveLine k) = 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq (projectiveLineIsoProj k).hom
      (projectiveLineIsoProj k).hom.homeomorph.isHomeomorph]
    exact topologicalKrullDim_projectiveLineProj k
  have hdimF : topologicalKrullDim F.idealSheaf.subscheme = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq eF.hom eF.hom.homeomorph.isHomeomorph]
    exact hdimP
  have hdimE : topologicalKrullDim E.idealSheaf.subscheme = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq eE.hom eE.hom.homeomorph.isHomeomorph]
    exact hdimF
  have hCE : IsCurveIn E.idealSheaf := ⟨E.integral, hdimE⟩
  have hpropE : IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) := by
    have : E.idealSheaf.subschemeι = eE.inv ≫ F.idealSheaf.subschemeι ≫ j := by
      rw [← heE, Iso.inv_hom_id_assoc]
    rw [this]
    simp only [Category.assoc]
    infer_instance
  let eP := eF ≪≫ eE
  have heP : eP.hom ≫ E.idealSheaf.subschemeι ≫ f ≫ sX = projectiveLine k ↘ Spec (.of k) := by
    simp only [eP, Iso.trans_hom, Category.assoc, reassoc_of% heE]
    exact heF
  have hexc : E.support ⊆ (exceptionalSet f : Set Y) := by
    intro z hz
    rw [SetLike.mem_coe, mem_exceptionalSet]
    intro hzW
    have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
    have key : ∀ c ∈ (E.support : Set Y), c = z := fun c hc =>
      Stacks.Models.eq_of_isIso_morphismRestrict f _
        (show f c ∈ biregularLocus f by rw [hfE c hc, ← hfE z hz]; exact hzW)
        ((hfE c hc).trans (hfE z hz).symm)
    exact IsCurveIn.not_subsingleton hCE fun a ha b hb => (key a ha).trans (key b hb).symm
  let CZ : ProperCurve (j ≫ f ≫ sX) := ⟨η, isProperCurve_genericPoint _ F hdimF⟩
  let CE : ProperCurve (f ≫ sX) := ⟨E.genericPoint, isProperCurve_genericPoint _ E hdimE⟩
  have hkey := intersectionNumber_single_primeDivisorMap hsm j hsmZ F CZ CE hEη.symm hErange
  have hFnum := isIntersectionNumber_of_properCurve _
    (isQCartier_single_of_isSmoothScheme hsmZ F) CZ F rfl
  have h1 : IsIntersectionNumber (j ≫ f ≫ sX) (Divisor.toQDivisor (Finsupp.single F 1))
      F.idealSheaf (-1) := by
    rw [toQDivisor_single, Int.cast_one]
    exact hnum
  have hval := hFnum.unique h1
  have hEnum := isIntersectionNumber_of_properCurve _
    (isQCartier_single_of_isSmoothScheme hsm E) CE E rfl
  rw [← hkey, hval, toQDivisor_single, Int.cast_one] at hEnum
  exact ⟨E, hexc, ⟨⟨hCE, hpropE, eP.hom, heP, inferInstance, isBirationalMorphism_of_isIso _⟩,
    eP, heP⟩, hEnum⟩

/-- Over an algebraically closed field, a minimal resolution `f : Y ⟶ X` of a normal surface `X`
restricts to an isomorphism `f⁻¹(V) ⟶ V` over the smooth locus `V` of `X`. -/
@[mmp "lem_km4a_minimal_resolution_isomorphism_over_smooth_locus"]
public theorem isIso_morphismRestrict_smoothLocus_of_isMinimalSurfaceResolution [IsAlgClosed k]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsMinimalSurfaceResolution sX f) :
    IsIso (f ∣_ smoothLocus sX) := by
  by_cases hV : smoothLocus sX = ⊥
  · rw [hV]
    have : IsEmpty ((⊥ : X.Opens) : Scheme) := ⟨fun x => x.2⟩
    have : IsEmpty ((f ⁻¹ᵁ (⊥ : X.Opens)) : Scheme) := ⟨fun x => x.2⟩
    exact isIso_of_isEmpty _
  set V := smoothLocus sX
  obtain ⟨hV₁, hV₂, hV₃⟩ := isSmoothSurface_smoothLocus sX hX.1 hdim hV
  obtain ⟨hU₁, hU₂, hU₃⟩ := isSmoothSurface_preimage sX hX hdim f hf.1 V hV
  have : IsProper (f ∣_ V) := IsZariskiLocalAtTarget.restrict hf.1.isProper V
  obtain ⟨Z, h, hch, e, he⟩ := MMP.Resolution.Bridges.factorsAsPointBlowups_of_isSmoothSurface k
    hV₁ ((Mori.isSmoothScheme_iff _).mpr hV₂) hV₃ hU₁ hU₂ hU₃ (f ∣_ V)
    (by rw [morphismRestrict_ι_assoc]) ((hf.1.isNormalVariety hX).2.2.restrict V)
  cases hch with
  | refl =>
    rw [← he, Category.comp_id]
    infer_instance
  | @step W₀ h₀ hh w hw _ =>
    exfalso
    obtain ⟨hW₁, hW₂, hW₃⟩ := isSmoothSurface_of_pointBlowupChain (V.ι ≫ sX) hV₁ hV₃ hh
    obtain ⟨-, -, -, -, -, -, F, -, hFsupp, hF⟩ :=
      isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve _ hW₁ hW₃ hw
    have hj : e.inv ≫ (f ⁻¹ᵁ V).ι ≫ f =
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h₀ ≫ V.ι := by
      rw [← morphismRestrict_ι, ← he]
      simp
    have hsm := MMP.Threefold.Resolution.isSmoothScheme_blowUp_singleton hW₁
      ((Mori.isSmoothScheme_iff _).mpr hW₂) hW₃ hw
    obtain ⟨_, _⟩ := isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
    haveI := (MMP.Threefold.Resolution.isVariety_blowUp_singleton hW₁ hW₃ hw).toQuasiCompact
    have : IsSeparated (f ≫ sX) := (hf.1.isNormalVariety hX).1.1.toIsSeparated
    refine not_isMinimalSurfaceResolution_of_isMinusOneCurve sX f (e.inv ≫ (f ⁻¹ᵁ V).ι)
      _ (by simp only [Category.assoc]; rw [reassoc_of% hj]) hsm F hF
      (V.ι (h₀ w)) ?_ hf
    rintro _ ⟨y, hy, rfl⟩
    rw [hFsupp] at hy
    simp only [Category.assoc, hj, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
      Set.mem_singleton_iff]
    rw [show (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).base y = w from hy]

end MinimalResolution

end MMP.Mori

end
