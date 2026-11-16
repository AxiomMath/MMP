module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform

/-!
# Smooth common models of modifications and crepancy of nef weak models

Let `X`, `Y` be normal varieties and `Z` a variety over a field of characteristic zero,
`f : X ⟶ Z` and `g : Y ⟶ Z` proper morphisms, and `φ : X ⤏ Y` a modification of `f` into `g`. A resolution of the closure
in `X ×_Z Y` of the graph of `φ` is a smooth common model `p : W ⟶ X`, `q : W ⟶ Y` with
`q = φ ∘ p`. Using such common models, two nef weak models `φ₁ : Y ⤏ Z₁`, `φ₂ : Y ⤏ Z₂` of a pair
`(Y, C)` over a separated base have equal adjoint pull-backs on every common projective
birational model, and in characteristic zero they are equivalent nef models.

## Main results

* `MMP.Flips.IsModificationOf.exists_smooth_common_model`: the smooth common model of a
  modification over a base.
* `MMP.Fourfold.IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent`: two nef weak
  models are crepant to each other.

## Implementation notes

Mathlib's rational maps compose with morphisms only on the left
(`AlgebraicGeometry.Scheme.RationalMap.compHom`), so `q = φ ∘ p` is stated as `φ = q ∘ p⁻¹`
through an inverse `ψ` of `p`. A common projective model of `Z₁` and `Z₂` over `Y` is a normal
variety with projective birational morphisms `p_i : W ⟶ Z_i` and a rational map `h : Y ⤏ W` with
`p_i ∘ h = φ_i`. The canonical divisor of `Z_i` is `φ_{i*} K_Y`, so the two adjoints are cut out
by one rational top form. The auxiliary lemmas of the proofs live in the namespaces
`Proof_lem_fa2_common_model_exists` and `Proof_lem_fourfold_two_weak_models_crepant`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.23, 2.24,
  2.28
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Proof_lem_fa2_common_model_exists

open CategoryTheory.Limits

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A morphism `f : Γ ⟶ Y` of irreducible schemes is birational when its composite with an open
immersion from a nonempty scheme is an open immersion. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {O Γ Y : Scheme.{u}}
    [IrreducibleSpace Γ] [IrreducibleSpace Y] [Nonempty O] (j : O ⟶ Γ) [IsOpenImmersion j]
    (f : Γ ⟶ Y) [IsOpenImmersion (j ≫ f)] : MMP.Mori.IsBirationalMorphism f := by
  have hle : j.opensRange ≤ f ⁻¹ᵁ (j ≫ f).opensRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨o⟩ := ‹Nonempty O›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f j.opensRange (j ≫ f).opensRange
    ⟨j o, o, rfl⟩ ⟨(j ≫ f) o, o, rfl⟩ hle ?_
  have e : (Scheme.Hom.isoOpensRange j).hom ≫ f.resLE _ _ hle =
      (Scheme.Hom.isoOpensRange (j ≫ f)).hom := by
    rw [← cancel_mono (j ≫ f).opensRange.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have h : f.resLE _ _ hle =
      (Scheme.Hom.isoOpensRange j).inv ≫ (Scheme.Hom.isoOpensRange (j ≫ f)).hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- Let `p : W ⟶ X` and `q : W ⟶ Y` be morphisms from an irreducible scheme to an irreducible
scheme `X`, and `A ⊆ W` a nonempty open on which `p` is an open immersion. If on `A` the map `q`
agrees with `h ∘ p` for a morphism `h : B ⟶ Y` on a dense open `B ⊆ X`, then `p` has a rational
inverse `ψ` with `q ∘ ψ = h` as rational maps. -/
private theorem exists_isInverse_compHom_eq {W X Y : Scheme.{u}} [IrreducibleSpace W]
    [IrreducibleSpace X] (p : W ⟶ X) (q : W ⟶ Y) (A : W.Opens) (hA : (A : Set W).Nonempty)
    [IsOpenImmersion (A.ι ≫ p)] (B : X.Opens) (hB : Dense (B : Set X)) (h : B.toScheme ⟶ Y)
    (l : A.toScheme ⟶ B) (hl₁ : l ≫ B.ι = A.ι ≫ p) (hl₂ : l ≫ h = A.ι ≫ q) :
    ∃ ψ : X.RationalMap W, MMP.Mori.RationalMap.IsInverse p.toRationalMap ψ ∧
      ψ.compHom q = (Scheme.PartialMap.mk B hB h).toRationalMap := by
  let R := (A.ι ≫ p).opensRange
  obtain ⟨a, ha⟩ := hA
  have hR : (R : Set X).Nonempty := ⟨(A.ι ≫ p) ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩
  let e : W.PartialIso X :=
    { source := A
      dense_source := A.isOpen.dense ⟨a, ha⟩
      target := R
      dense_target := R.isOpen.dense hR
      iso := Scheme.Hom.isoOpensRange (A.ι ≫ p) }
  have he : e.toRationalMap = p.toRationalMap := by
    rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨A, A.isOpen.dense ⟨a, ha⟩, le_rfl, le_top, ?_⟩
    change W.homOfLE le_rfl ≫ (Scheme.Hom.isoOpensRange (A.ι ≫ p)).hom ≫
        (A.ι ≫ p).opensRange.ι = W.homOfLE (le_top : A ≤ ⊤) ≫ W.topIso.hom ≫ p
    rw [Scheme.Hom.isoOpensRange_hom_ι, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc,
      Scheme.homOfLE_ι_assoc]
  refine ⟨e.symm.toRationalMap, ⟨e, he, rfl⟩, ?_⟩
  have hRle : R ≤ B := by
    rintro _ ⟨x, rfl⟩
    rw [← hl₁]
    exact (l x).2
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨R, R.isOpen.dense hR, le_rfl, hRle, ?_⟩
  have key : e.iso.inv ≫ l = X.homOfLE hRle := by
    rw [← cancel_mono B.ι, Category.assoc, hl₁, Scheme.homOfLE_ι]
    change (Scheme.Hom.isoOpensRange (A.ι ≫ p)).inv ≫ A.ι ≫ p = (A.ι ≫ p).opensRange.ι
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  change X.homOfLE le_rfl ≫ (e.iso.inv ≫ A.ι) ≫ q = X.homOfLE hRle ≫ h
  rw [Scheme.homOfLE_rfl, Category.id_comp, ← key, Category.assoc, Category.assoc, hl₂]

/-- A modification `φ` of `f` into `g` is, on a dense open `O ⊆ X`, an open immersion
`h : O ⟶ Y` over `Z`: `h ≫ g = O ↪ X ≫ f`. -/
private theorem exists_isOpenImmersion_of_isModificationOf {X Y Z : Scheme.{u}} {f : X ⟶ Z}
    {g : Y ⟶ Z} {φ : X.RationalMap Y} (hφ : MMP.Flips.IsModificationOf f g φ) :
    ∃ (O : X.Opens) (hO : Dense (O : Set X)) (h : O.toScheme ⟶ Y), IsOpenImmersion h ∧
      (Scheme.PartialMap.mk O hO h).toRationalMap = φ ∧ h ≫ g = O.ι ≫ f := by
  obtain ⟨⟨e, he⟩, hover⟩ := hφ
  rw [MMP.Flips.RationalMap.IsOver, ← he, Scheme.PartialIso.toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hover
  obtain ⟨O, hO, hOe, hOt, hOeq⟩ := hover
  replace hOe : O ≤ e.source := hOe
  refine ⟨O, hO, X.homOfLE hOe ≫ e.iso.hom ≫ e.target.ι, inferInstance, ?_, ?_⟩
  · rw [← he, Scheme.PartialIso.toRationalMap,
      ← Scheme.PartialMap.restrict_toRationalMap e.toPartialMap O hO hOe]
    rfl
  · simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom_hom,
      Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom] at hOeq
    have h2 : X.homOfLE hOe ≫ e.iso.hom ≫ e.target.ι ≫ g =
        X.homOfLE (le_top : O ≤ ⊤) ≫ (⊤ : X.Opens).ι ≫ f := hOeq
    rw [Scheme.homOfLE_ι_assoc] at h2
    simpa only [Category.assoc] using h2

/-- A birational morphism `r : W ⟶ Γ` onto an irreducible scheme maps some nonempty open
`A ⊆ W` isomorphically onto an open of any given nonempty open subscheme `j : O ⟶ Γ`. -/
private theorem exists_isOpenImmersion_lift {W Γ O : Scheme.{u}} [Nonempty W]
    [IrreducibleSpace Γ] [Nonempty O] {r : W ⟶ Γ} (hr : MMP.Mori.IsBirationalMorphism r)
    (j : O ⟶ Γ) [IsOpenImmersion j] :
    ∃ (A : W.Opens) (m : A.toScheme ⟶ O), (A : Set W).Nonempty ∧ IsOpenImmersion m ∧
      m ≫ j = A.ι ≫ r := by
  obtain ⟨W₀, ⟨w, hw⟩, h₀⟩ := hr.exists_isOpenImmersion
  obtain ⟨o⟩ := ‹Nonempty O›
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := nonempty_preirreducible_inter (W₀.ι ≫ r).opensRange.isOpen
    j.opensRange.isOpen ⟨(W₀.ι ≫ r) ⟨w, hw⟩, ⟨w, hw⟩, rfl⟩ ⟨j o, o, rfl⟩
  let A : W.Opens := W₀ ⊓ r ⁻¹ᵁ j.opensRange
  have : IsOpenImmersion (A.ι ≫ r) := by
    rw [← Scheme.homOfLE_ι W (inf_le_left : A ≤ W₀), Category.assoc]
    infer_instance
  let m := IsOpenImmersion.lift j (A.ι ≫ r) (by rintro _ ⟨a, rfl⟩; exact a.2.2)
  have hm : m ≫ j = A.ι ≫ r := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (m ≫ j) := by
    rw [hm]
    infer_instance
  exact ⟨A, m, ⟨x.1, x.2, hx⟩, .of_comp m j, hm⟩

end

end Proof_lem_fa2_common_model_exists

namespace MMP.Flips

open CategoryTheory.Limits Proof_lem_fa2_common_model_exists

/-- **Smooth common model of a modification over a base.** Let `X`, `Y` be normal varieties
and `Z` a variety over a field `k` of characteristic zero, `f : X ⟶ Z` and `g : Y ⟶ Z` proper
morphisms, and `φ : X ⤏ Y` a modification of `f` into `g`. Then there are a smooth variety `W` and proper birational
morphisms `p : W ⟶ X`, `q : W ⟶ Y` with `q = φ ∘ p` as maps: some inverse `ψ` of `p` has
`ψ.compHom q = φ`. In particular `p ≫ f = q ≫ g`. -/
@[mmp "lem_fa2_common_model_exists"]
public theorem IsModificationOf.exists_smooth_common_model {k : Type u} [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) (hX : Mori.IsNormalVariety k sX) (hY : Mori.IsNormalVariety k sY)
    (hZ : Mori.IsVariety k sZ) (f : X ⟶ Z) (g : Y ⟶ Z) (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    [IsProper f] [IsProper g] (φ : X.RationalMap Y) (hφ : IsModificationOf f g φ) :
    ∃ (W : Scheme.{u}) (p : W ⟶ X) (q : W ⟶ Y),
      Mori.IsVariety k (p ≫ sX) ∧ Mori.IsSmoothScheme (p ≫ sX) ∧
        IsProper p ∧ IsProper q ∧
        Mori.IsBirationalMorphism p ∧ Mori.IsBirationalMorphism q ∧
        (∃ ψ : X.RationalMap W, Mori.RationalMap.IsInverse p.toRationalMap ψ ∧
          ψ.compHom q = φ) ∧
        p ≫ f = q ≫ g := by
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sY := hY.1
  have : IsIntegral X := IsVariety.toIsIntegral (k := k) (f := sX)
  have : IsIntegral Y := IsVariety.toIsIntegral (k := k) (f := sY)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType sX
  /- Step 1: an open `O ⊆ X` on which `φ` is an open immersion `h` with `h ≫ g = f`. -/
  obtain ⟨O, hO, h, _, hPφ, hcomm⟩ := exists_isOpenImmersion_of_isModificationOf hφ
  have : Nonempty O := hO.nonempty.to_subtype
  /- Step 2: the closure `Γ ⊆ X ×_Z Y` of the graph of `h`. -/
  let s : O.toScheme ⟶ pullback f g := pullback.lift O.ι h hcomm.symm
  have : IsImmersion s := by
    have : IsImmersion (s ≫ pullback.fst f g) := by rw [pullback.lift_fst]; infer_instance
    exact IsImmersion.of_comp s (pullback.fst _ _)
  have : TopologicalSpace.NoetherianSpace O := TopologicalSpace.NoetherianSpace.set (O : Set X)
  have : QuasiCompact s := quasiCompact_of_noetherianSpace_source s
  have : IsOpenImmersion s.toImage := isOpenImmersion_toImage s (.inl inferInstance)
  let p₁ : s.image ⟶ X := s.imageι ≫ pullback.fst f g
  let p₂ : s.image ⟶ Y := s.imageι ≫ pullback.snd f g
  let sΓ : s.image ⟶ Spec (.of k) := p₁ ≫ sX
  have hΓ : AlgebraicGeometry.IsVariety k sΓ := by
    simpa only [sΓ, p₁, Category.assoc] using
      Scheme.Hom.isVariety_image k s (pullback.fst f g ≫ sX)
  have : IsProper p₁ := by dsimp only [p₁]; infer_instance
  have : IsProper p₂ := by dsimp only [p₂]; infer_instance
  /- Step 3: a resolution `r : W ⟶ Γ`. -/
  obtain ⟨W, r, hW, hr, hbr, hsm, -, -⟩ := MMP.Resolution.exists_isStrongResolution sΓ hΓ
  have : IsProper r := hr.isProper
  have : IsIntegral W := hW.toIsIntegral
  have : IsIntegral s.image := hΓ.toIsIntegral
  /- Step 4: a nonempty open `A ⊆ W` mapped by `r` isomorphically into the graph of `h`. -/
  obtain ⟨A, m, hA, _, hm⟩ := exists_isOpenImmersion_lift hbr s.toImage
  have : Nonempty A := hA.to_subtype
  have hm₁ : m ≫ O.ι = A.ι ≫ r ≫ p₁ := by
    rw [← reassoc_of% hm, ← Category.assoc s.toImage, Scheme.Hom.toImage_imageι,
      pullback.lift_fst]
  have hm₂ : m ≫ h = A.ι ≫ r ≫ p₂ := by
    rw [← reassoc_of% hm, ← Category.assoc s.toImage, Scheme.Hom.toImage_imageι,
      pullback.lift_snd]
  have : IsOpenImmersion (A.ι ≫ r ≫ p₁) := by rw [← hm₁]; infer_instance
  have : IsOpenImmersion (A.ι ≫ r ≫ p₂) := by rw [← hm₂]; infer_instance
  /- Step 5: the common model `p = r ≫ p₁`, `q = r ≫ p₂`. -/
  obtain ⟨ψ, hψ, hψq⟩ := exists_isInverse_compHom_eq (r ≫ p₁) (r ≫ p₂) A hA O hO h m hm₁ hm₂
  have hassoc : (r ≫ p₁) ≫ sX = r ≫ sΓ := by simp only [sΓ, Category.assoc]
  refine ⟨W, r ≫ p₁, r ≫ p₂, hassoc ▸ hW, hassoc ▸ hsm, inferInstance, inferInstance,
    hψ.isBirational, isBirationalMorphism_of_isOpenImmersion_comp A.ι (r ≫ p₂),
    ⟨ψ, hψ, hψq.trans hPφ⟩, ?_⟩
  simp only [p₁, p₂, Category.assoc, pullback.condition]

end MMP.Flips

namespace Proof_lem_fourfold_two_weak_models_crepant

open MMP.Mori MMP.Fourfold

/-! ### Generalities on points and partial maps -/

section Generalities

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A morphism of irreducible schemes sending the generic point to the generic point is
dominant. -/
private theorem isDominant_of_apply_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) :
    IsDominant f := by
  rw [isDominant_iff]
  intro y
  have hy : y ∈ closure ({genericPoint Y} : Set Y) := by
    rw [(genericPoint_spec Y).def]; trivial
  have hmem : genericPoint Y ∈ Set.range (f : X → Y) := ⟨genericPoint X, h⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hy

/-- The local ring of a normal locally noetherian integral scheme at a point of coheight at most
one is a valuation ring (a field or a discrete valuation ring). -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (hx : Order.coheight x ≤ 1) :
    ValuationRing (X.presheaf.stalk x) := by
  rcases lt_or_eq_of_le hx with h | h
  · have hmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h)
    have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    have hx' : x ⤳ genericPoint X := hmax (show x ≤ genericPoint X from hgen)
    have hgx : genericPoint X = x := (hgen.antisymm hx').eq
    subst hgx
    have : IsField (X.presheaf.stalk (genericPoint X)) := Field.toIsField X.functionField
    letI := this.toField
    infer_instance
  · have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h]; rfl
    have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
        ringKrullDim (X.presheaf.stalk x) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal x, hdim⟩
    have h1 : ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
      ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
    have := h1.choose_spec
    infer_instance

/-- A dominant morphism of integral schemes, with normal target, that is bijective on function
fields induces an isomorphism of local rings at every point over a point of coheight at most one. -/
private theorem isIso_stalkMap_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x : X} (hx : Order.coheight (f x) ≤ 1) :
    IsIso (f.stalkMap x) := by
  have := valuationRing_stalk_of_coheight_le_one hx
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

private theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) (hx : Order.coheight (f x₁) ≤ 1) : x₁ = x₂ := by
  have := valuationRing_stalk_of_coheight_le_one hx
  have := isIso_stalkMap_of_coheight_le_one f hf hx
  have : IsIso (f.stalkMap x₂) :=
    isIso_stalkMap_of_coheight_le_one f hf (by rwa [h])
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf h

/-- Two partial maps with the same domain representing the same rational map to a separated
scheme are equal. -/
private theorem hom_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) {f g : U.toScheme ⟶ Y}
    (h : (⟨U, hU, f⟩ : X.PartialMap Y).toRationalMap =
      (⟨U, hU, g⟩ : X.PartialMap Y).toRationalMap) :
    f = g := by
  have := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ Scheme)
    (f := ⟨U, hU, f⟩) (g := ⟨U, hU, g⟩) rfl).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  injection this

/-- The partial map given by the restriction of `g` to `U`, composed with `q`, represents
`g ∘ q`. -/
private theorem toRationalMap_restrict_comp {X Y Z : Scheme.{u}} (g : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hle : U ≤ g.domain) (q : Y ⟶ Z) :
    (⟨U, hU, (g.restrict U hU hle).hom ≫ q⟩ : X.PartialMap Z).toRationalMap =
      g.toRationalMap.compHom q := by
  rw [← Scheme.PartialMap.restrict_toRationalMap g U hU hle,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

/-- The partial map given by the inclusion of a dense open `U`, composed with `q`, represents
`q`. -/
private theorem toRationalMap_ι_comp {X Z : Scheme.{u}} {U : X.Opens} (hU : Dense (U : Set X))
    (q : X ⟶ Z) :
    (⟨U, hU, U.ι ≫ q⟩ : X.PartialMap Z).toRationalMap = q.toRationalMap := by
  change _ = q.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap q.toPartialMap U hU le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change U.ι ≫ q = (X.isoOfEq rfl).hom ≫ (X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ q)
  simp [Scheme.topIso_hom]

/-- Two representatives, restricted to a common dense open `U` and composed with morphisms to a
separated scheme, agree on `U` when the composite rational maps agree. -/
private theorem comp_eq_comp_of_compHom_eq {X Y₁ Y₂ Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) (g₁ : X.PartialMap Y₁)
    (g₂ : X.PartialMap Y₂) (h₁ : U ≤ g₁.domain) (h₂ : U ≤ g₂.domain) (q₁ : Y₁ ⟶ Z)
    (q₂ : Y₂ ⟶ Z) (h : g₁.toRationalMap.compHom q₁ = g₂.toRationalMap.compHom q₂) :
    (X.homOfLE h₁ ≫ g₁.hom) ≫ q₁ = (X.homOfLE h₂ ≫ g₂.hom) ≫ q₂ :=
  hom_eq_of_toRationalMap_eq hU ((toRationalMap_restrict_comp g₁ hU h₁ q₁).trans
    (h.trans (toRationalMap_restrict_comp g₂ hU h₂ q₂).symm))

/-- A representative restricted to a dense open `U` and composed with a morphism agrees on `U`
with a morphism `r` when the composite rational map is `r`. -/
private theorem comp_eq_ι_comp_of_compHom_eq {X Y Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) (g : X.PartialMap Y)
    (h₁ : U ≤ g.domain) (q : Y ⟶ Z) (r : X ⟶ Z)
    (h : g.toRationalMap.compHom q = r.toRationalMap) :
    (X.homOfLE h₁ ≫ g.hom) ≫ q = U.ι ≫ r :=
  hom_eq_of_toRationalMap_eq hU ((toRationalMap_restrict_comp g hU h₁ q).trans
    (h.trans (toRationalMap_ι_comp hU r).symm))

/-- `(φ ∘ f) ∘ g = φ ∘ (g ∘ f)` for a rational map `φ` and morphisms `f`, `g`. -/
private theorem compHom_compHom {X Y Z T : Scheme.{u}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ', rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

/-- If `h` is an inverse of the morphism `p`, then `p ∘ h` is the identity. -/
private theorem compHom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : Y ⟶ X} {h : X.RationalMap Y}
    (hinv : RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [show e.source.ι ≫ p = e.iso.hom ≫ e.target.ι from
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he1)).symm, Iso.inv_hom_id_assoc,
    Category.comp_id]

/-- A morphism whose composite with `s` is a given separated morphism is separated. -/
private theorem isSeparated_of_comp_eq {X Y T : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ T}
    {t : X ⟶ T} (h : f ≫ s = t) [IsSeparated t] : IsSeparated f := by
  subst h
  exact IsSeparated.of_comp f s

/-- **Cancelling a local isomorphism at a codimension-one point.** If `f ≫ g` induces an
isomorphism of local rings at `x`, and `g` is a separated dominant morphism of normal integral
schemes inducing an isomorphism of function fields with `f x` over a point of coheight at most
one, then `f` induces an isomorphism of local rings at `x`. -/
private theorem isIso_stalkMap_of_isIso_comp {X Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant g]
    (hg : Function.Bijective (functionFieldMap g)) (x : X) [h : IsIso ((f ≫ g).stalkMap x)]
    (hx : Order.coheight (g (f x)) ≤ 1) : IsIso (f.stalkMap x) := by
  have := isIso_stalkMap_of_coheight_le_one g hg hx
  rw [Scheme.Hom.stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (g.stalkMap (f x)) (f.stalkMap x) this h

end Generalities

/-! ### Transforms of prime divisors -/

section Transforms

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ,
    TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- A representative of `φ` defined at `η_Q` sends `η_Q` to `η_P` when `φ_* Q = P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

end Transforms

/-! ### Pull-backs along composites -/

section Pullback

/-- On an irreducible space every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (Z : irreducibleComponents T) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (g ≫ f)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) ((eq_univ_of_irreducibleComponents
    (pointComponent ((g ≫ f) z))).ge (Set.mem_univ _))
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
      ((eq_univ_of_irreducibleComponents (pointComponent ((g ≫ f) z))).ge (Set.mem_univ _))
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
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

/-- If `G = f^*D` and `f` maps `η_E` to `η_P` with an isomorphism of local rings, then the
coefficient of `E` in `G` is the coefficient of `P` in `D`. -/
private theorem coeff_eq_of_isRCartierPullback {W Y : Scheme.{u}} [IsLocallyNoetherian W]
    [IsNormal W] [IsLocallyNoetherian Y] [IsNormal Y] {f : W ⟶ Y} {D : RDivisor Y}
    {G : RDivisor W} (hG : MMP.Flips.IsRCartierPullback f D G) (E : MMP.Mori.PrimeDivisor W)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] : G.coeff E = D.coeff P := by
  obtain ⟨m, r, L, L', hLc, hL, hLpb, hG⟩ := hG
  rw [hG, hL, MMP.Flips.coeff_sum_smul_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨hB, hpbj⟩ := hLpb j
  congr 1
  exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback E P heq (hLc j) hpbj

/-- **Pulling a pull-back back once more.** Let `g^*M = D` be an `ℝ`-Cartier pull-back and
`f : V ⟶ W` dominant from a quasi-compact normal integral scheme. Then `M` has a pull-back `G`
along `f ≫ g` whose coefficient along a prime divisor `E` of `V` dominating a prime divisor `P` of
`W` with an isomorphism of local rings is the coefficient of `D` along `P`. -/
private theorem exists_isRCartierPullback_comp {V W Z : Scheme.{u}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (f : V ⟶ W) [IsDominant f]
    (g : W ⟶ Z) [IsDominant g] {M : RDivisor Z} {D : RDivisor W}
    (hD : MMP.Flips.IsRCartierPullback g M D) :
    ∃ G : RDivisor V, MMP.Flips.IsRCartierPullback (f ≫ g) M G ∧
      ∀ (E : MMP.Mori.PrimeDivisor V) (P : MMP.Mori.PrimeDivisor W),
        f E.genericPoint = P.genericPoint → IsIso (f.stalkMap E.genericPoint) →
          G.coeff E = D.coeff P := by
  obtain ⟨m, r, L, L', hLc, hM, hpb, rfl⟩ := hD
  have hL'c : ∀ j, (L' j).IsCartier := fun j => ((hpb j).2).isCartier (hLc j)
  let L'' : Fin m → Divisor V := fun j =>
    (L' j).pullback (hL'c j) (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _)
  have hL'' : ∀ j, (L' j).IsPullback f
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  refine ⟨∑ j, r j • Divisor.toRDivisor (L'' j), ⟨m, r, L, L'', hLc, hM, fun j =>
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (f ≫ g) _,
      isPullback_comp (hpb j).2 (hL'' j) _⟩, rfl⟩, fun E P heq hiso => ?_⟩
  rw [MMP.Flips.coeff_sum_smul_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback E P heq (hL'c j) (hL'' j)

end Pullback

/-! ### Dominance -/

section Dominance

/-- The partial map underlying a partial isomorphism is dominant. -/
private theorem isDominant_toPartialMap_hom {X Y : Scheme.{u}} (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  change IsDominant (e.iso.hom ≫ e.target.ι)
  haveI : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  infer_instance

/-- A representative of a birational map is dominant. -/
private theorem isDominant_hom_of_isBirational {X Y : Scheme.{u}} {φ : X.RationalMap Y}
    (hφ : RationalMap.IsBirational φ) (g : X.PartialMap Y) (hg : g.toRationalMap = φ) :
    IsDominant g.hom := by
  obtain ⟨e, he⟩ := hφ
  exact (Scheme.PartialMap.isDominant_hom_iff_of_equiv _ _
    (Scheme.PartialMap.toRationalMap_eq_iff.mp (he.trans hg.symm))).mp
    (isDominant_toPartialMap_hom e)

/-- If `a ≫ p` is dominant, with `p` a separated dominant morphism of integral schemes inducing
an isomorphism of function fields onto a normal scheme, then `a` is dominant. -/
private theorem isDominant_of_isDominant_comp {V W T : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (a : V ⟶ W) (p : W ⟶ T) [IsSeparated p]
    [IsDominant p] (hp : Function.Bijective (functionFieldMap p)) [IsDominant (a ≫ p)] :
    IsDominant a := by
  refine isDominant_of_apply_genericPoint a ?_
  have h1 : p (a (genericPoint V)) = genericPoint T := by
    rw [← Scheme.Hom.comp_apply]; exact MMP.Positivity.map_genericPoint_eq_of_isDominant (a ≫ p)
  have h2 : p (genericPoint W) = genericPoint T :=
    MMP.Positivity.map_genericPoint_eq_of_isDominant p
  refine (eq_of_apply_eq_of_coheight_le_one p hp (h1.trans h2.symm) ?_).symm
  rw [h2, Order.coheight_eq_zero.mpr fun y _ => (genericPoint_spec T).specializes (Set.mem_univ y)]
  exact zero_le_one

end Dominance

/-! ### Composites of rational maps -/

section Composition

/-- **A representative of a composite.** If `f` maps a dense open `O ⊆ dom f` into `dom g`
through `β`, then `g ∘ f` is represented on `O` by `β` followed by `g`. -/
private theorem comp_toRationalMap_eq {X Y Z : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {O : X.Opens}
    (hO : Dense (O : Set X)) (hOf : O ≤ f.domain) (β : O.toScheme ⟶ g.domain.toScheme)
    (hβ : β ≫ g.domain.ι = X.homOfLE hOf ≫ f.hom) :
    f.toRationalMap.comp g.toRationalMap = (⟨O, hO, β ≫ g.hom⟩ : X.PartialMap Z).toRationalMap := by
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hOc : O ≤ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := by
    intro x hx
    let y : O.toScheme := ⟨x, hx⟩
    have h1 : f.hom (X.homOfLE hOf y) = g.domain.ι (β y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hβ]
    refine ⟨X.homOfLE hOf y, ?_, ?_⟩
    · show f.hom (X.homOfLE hOf y) ∈ g.domain
      rw [h1]; exact (β y).2
    · show f.domain.ι (X.homOfLE hOf y) = x
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]; rfl
  have key2 : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      (f.hom ⁻¹ᵁ g.domain).ι = X.homOfLE hOf := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc]
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have key : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      f.hom ∣_ g.domain = β := by
    rw [← cancel_mono g.domain.ι, hβ, ← key2]
    simp only [Category.assoc, morphismRestrict_ι]
  refine ⟨O, hO, hOc, le_rfl, ?_⟩
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom, Scheme.homOfLE_rfl,
    Category.id_comp]
  rw [← key]
  rfl

/-- A birational map is dominant. -/
private theorem isDominant_of_isBirational {X Y : Scheme.{u}} {φ : X.RationalMap Y}
    (hφ : RationalMap.IsBirational φ) : φ.IsDominant := by
  obtain ⟨e, rfl⟩ := hφ
  have := isDominant_toPartialMap_hom e
  infer_instance

/-- A birational map followed by its inverse is the identity. -/
private theorem comp_eq_id_of_isInverse {X Y : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    {f : X.RationalMap Y} [f.IsDominant] {h : Y.RationalMap X}
    (H : RationalMap.IsInverse f h) : f.comp h = Scheme.RationalMap.id X := by
  obtain ⟨e, rfl, rfl⟩ := H
  have := isDominant_toPartialMap_hom e
  rw [comp_toRationalMap_eq e.toPartialMap e.symm.toPartialMap (O := e.source) e.dense_source le_rfl
    e.iso.hom (by
      change e.iso.hom ≫ e.target.ι = X.homOfLE le_rfl ≫ e.iso.hom ≫ e.target.ι
      rw [Scheme.homOfLE_rfl, Category.id_comp])]
  have : (⟨e.source, e.dense_source, e.iso.hom ≫ e.symm.toPartialMap.hom⟩ : X.PartialMap X) =
      ⟨e.source, e.dense_source, e.source.ι ≫ 𝟙 X⟩ := by
    congr 1
    change e.iso.hom ≫ e.iso.inv ≫ e.source.ι = _
    simp
  exact (congrArg Scheme.PartialMap.toRationalMap this).trans (toRationalMap_ι_comp _ (𝟙 X))

/-- A partial map which is an open immersion represents a birational map. -/
private theorem isBirational_of_isOpenImmersion {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (c : X.PartialMap Y) [IsOpenImmersion c.hom] [Nonempty c.domain] :
    RationalMap.IsBirational c.toRationalMap := by
  have hd : Dense (c.hom.opensRange : Set Y) :=
    c.hom.opensRange.2.dense ⟨_, Classical.arbitrary c.domain, rfl⟩
  refine ⟨⟨c.domain, c.dense_domain, c.hom.opensRange, hd, c.hom.isoOpensRange⟩, ?_⟩
  change Scheme.PartialMap.toRationalMap
    ⟨c.domain, c.dense_domain, c.hom.isoOpensRange.hom ≫ c.hom.opensRange.ι⟩ = _
  rw [Scheme.Hom.isoOpensRange_hom_ι]

/-- If a partial isomorphism `e` followed by `b` is `a`, then `e⁻¹` followed by `a` is `b`. -/
private theorem symm_compHom_eq {X Y T : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [IsSeparated (T ↘ ⊤_ Scheme)] (e : X.PartialIso Y) (a : X ⟶ T) (b : Y ⟶ T)
    (h : e.toRationalMap.compHom b = a.toRationalMap) :
    e.symm.toRationalMap.compHom a = b.toRationalMap := by
  have h1 : (e.iso.hom ≫ e.target.ι) ≫ b = e.source.ι ≫ a :=
    hom_eq_of_toRationalMap_eq e.dense_source
      ((Scheme.RationalMap.compHom_toRationalMap e.toPartialMap b).trans
        (h.trans (toRationalMap_ι_comp e.dense_source a).symm))
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← toRationalMap_ι_comp e.dense_target b]
  congr 1
  change (⟨e.target, e.dense_target, (e.iso.inv ≫ e.source.ι) ≫ a⟩ : Y.PartialMap T) =
    ⟨e.target, e.dense_target, e.target.ι ≫ b⟩
  congr 1
  rw [Category.assoc, ← h1]
  simp

/-- `(g ∘ f) ∘ q = (q ∘ g) ∘ f` for dominant `f`, `g` and a morphism `q`. -/
private theorem comp_compHom {X Y Z T : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [Nonempty Y] [Nonempty Z] (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) [g.IsDominant] (q : Z ⟶ T) :
    (f.comp g).compHom q = f.comp (g.compHom q) := by
  rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc,
    Scheme.RationalMap.comp_toRationalMap]

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.homOfLE_ι X (inf_le_left : U ≤ U₁), Category.assoc]
    infer_instance
  have := IsOpenImmersion.of_comp (f.resLE U₂ U hle) U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U (U.2.dense hne)

/-- Composition on the left respects equality of the first map. -/
private theorem comp_eq_comp_of_eq {X Y Z : Scheme.{u}} [IrreducibleSpace X] [Nonempty Y]
    {f f' : X ⤏ Y} [f.IsDominant] [f'.IsDominant] (h : f = f') (g : Y ⤏ Z) :
    f.comp g = f'.comp g := by
  subst h
  rfl

/-- **Uniqueness of a section of a birational morphism.** If `p : W ⟶ Z` is a dominant morphism
with inverse `ψ`, a dominant rational map `χ : Z ⤏ W` with `p ∘ χ = id` is `ψ`. -/
private theorem eq_of_compHom_eq_id {Z W : Scheme.{u}} [IsIntegral Z] [IsIntegral W]
    {p : W ⟶ Z} [IsDominant p] {ψ χ : Z.RationalMap W} [χ.IsDominant]
    (hψ : RationalMap.IsInverse p.toRationalMap ψ)
    (hχ : χ.compHom p = Scheme.Hom.toRationalMap (𝟙 Z)) : χ = ψ := by
  calc χ = χ.comp (Scheme.RationalMap.id W) := (Scheme.RationalMap.comp_id χ).symm
    _ = χ.comp (p.toRationalMap.comp ψ) := by rw [comp_eq_id_of_isInverse hψ]
    _ = (χ.comp p.toRationalMap).comp ψ := (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (Scheme.RationalMap.id Z).comp ψ :=
        comp_eq_comp_of_eq (by rw [Scheme.RationalMap.comp_toRationalMap, hχ]) ψ
    _ = ψ := Scheme.RationalMap.id_comp ψ

end Composition

/-! ### Pull-backs of rational forms along birational morphisms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k]

/-- Along a dominant morphism inducing an isomorphism of function fields, the pull-back of a
nonzero rational form is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X V : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (f : V ⟶ X) [IsIntegral X] [IsIntegral V] [IsDominant f] [LocallyOfFiniteType sX]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  have h1 : pullbackRationalPluriForms sX f τ =
      pullbackFormsAlong (K' := V.functionField) hω m τ := pullbackForms_eq hω m τ
  rw [h1]
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    ((ZTensorPower.basis _ m).ne_zero ())

/-- Along a dominant morphism inducing an isomorphism of function fields, every rational form is
a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq {X V : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (f : V ⟶ X) [IsIntegral X] [IsIntegral V] [IsDominant f] [LocallyOfFiniteType sX]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    (σ : RationalPluriForms (f ≫ sX) d m) :
    ∃ τ : RationalPluriForms sX d m, pullbackRationalPluriForms sX f τ = σ ∧ (σ ≠ 0 → τ ≠ 0) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let B' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  let B := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (B'.repr σ ())
  refine ⟨c • B (), ?_, fun hσ => smul_ne_zero ?_ (B.ne_zero ())⟩
  swap
  · rintro rfl
    rw [map_zero] at hc
    apply hσ
    have h2 := (B'.sum_repr σ).symm
    simp only [← hc, Finset.univ_unique, Finset.sum_singleton, zero_smul] at h2
    exact h2
  change pullbackForms (K := X.functionField) (K' := V.functionField) m (c • B ()) = σ
  rw [pullbackForms_eq hω, pullbackFormsAlong, show B.repr (c • B ()) () = c by simp]
  change functionFieldMap f c • B' () = σ
  rw [hc]
  simpa using B'.sum_repr σ

/-- The order of a rational form does not see a rewriting of the structure morphism. -/
private theorem ordForm_cast {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s s' : V ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ} (τ : RationalPluriForms s d m)
    (E : MMP.Mori.PrimeDivisor V) :
    E.ordForm (cast (congrArg (fun t => RationalPluriForms t d m) h) τ) = E.ordForm τ := by
  subst h
  rfl

private theorem cast_rationalPluriForms_ne_zero {V : Scheme.{u}} [IsIntegral V]
    {s s' : V ⟶ Spec (.of k)}
    (h : s = s') {d : ℕ} {m : ℤ} {τ : RationalPluriForms s d m} (hτ : τ ≠ 0) :
    cast (congrArg (fun t => RationalPluriForms t d m) h) τ ≠ 0 := by
  subst h
  exact hτ

end Forms

/-! ### Existence of canonical divisors on normal varieties -/

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl : Z = Z' := Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF, evFF_restrictRF U V ψ _
        ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
          (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  refine ⟨fun h P hP => ?_, fun h E' hE' => (key E' hE' ((hmem E').1 hE')).2
    (h _ ((hmem E').1 hE'))⟩
  have hPU : P.genericPoint ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
    rw [← hx]
    exact x.2
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
  exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _,
    Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · exact Subtype.ext (restrictRF_injective U V (congrArg Subtype.val h))
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  have e₀ := (@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom T KS)).symm
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

/-! ### The comparison of two nef weak models -/

section Comparison

variable {k : Type u} [Field k] {Y Z₁ Z₂ S : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
    [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
    {sY : Y ⟶ Spec (.of k)} {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)}
    [QuasiCompact s₁] [QuasiCompact s₂] {sS : S ⟶ Spec (.of k)}
    {πY : Y ⟶ S} {π₁ : Z₁ ⟶ S} {π₂ : Z₂ ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ₁ : Y.RationalMap Z₁} {φ₂ : Y.RationalMap Z₂}

/-- A rational map `Y ⤏ V` inverse to a proper morphism `p : V ⟶ Y` is defined at the generic
point of every prime divisor of `Y`. -/
private theorem exists_rep_mem_domain {V : Scheme.{u}} [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p] {h : Y.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ g : Y.PartialMap V, g.toRationalMap = h ∧ Q.genericPoint ∈ g.domain := by
  have hhp := compHom_eq_of_isInverse hinv
  obtain ⟨g, hg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 Y) p h hhp
      (Q.coheight_genericPoint.le))
  exact ⟨g, hg', hg⟩

/-- **The point over a source prime.** Let `p : V ⟶ Y` be proper with inverse `h`, and
`q : V ⟶ T` with `q ∘ h = φ`. If `φ_* R = P`, then the image under `h` of `η_R` is a point of `V`
lying over `η_R` and over `η_P`. -/
private theorem exists_apply_eq_genericPoint {V T : Scheme.{u}} [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (T ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p]
    {q : V ⟶ T} {h : Y.RationalMap V} {φ : Y.RationalMap T}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (hq : h.compHom q = φ)
    {R : MMP.Mori.PrimeDivisor Y} {P : MMP.Mori.PrimeDivisor T}
    (hR : MMP.Mori.RationalMap.transformPrimeDivisor φ R = some P) :
    ∃ w : V, q w = P.genericPoint ∧ p w = R.genericPoint := by
  obtain ⟨g, hg, hRg⟩ := exists_rep_mem_domain hinv R
  refine ⟨g.hom ⟨R.genericPoint, hRg⟩, (genericPoint_eq_of_transformPrimeDivisor_eq_some hR
    (g.compHom q) (by rw [Scheme.RationalMap.compHom_toRationalMap, hg, hq]) hRg).symm, ?_⟩
  have he : g.hom ≫ p = g.domain.ι ≫ 𝟙 Y :=
    hom_eq_of_toRationalMap_eq g.dense_domain <| by
      rw [toRationalMap_ι_comp]
      change (g.compHom p).toRationalMap = _
      rw [Scheme.RationalMap.compHom_toRationalMap, hg, compHom_eq_of_isInverse hinv]
  calc p (g.hom ⟨R.genericPoint, hRg⟩) = (g.hom ≫ p) ⟨R.genericPoint, hRg⟩ :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = R.genericPoint := by rw [he]; simp

/-- **The source prime of a prime of a weak model.** For a nef weak model `φ : Y ⤏ Z` and a prime
divisor `P` of `Z`, there is a prime divisor `Q` of `Y` with `φ_* Q = P`, and the
coefficient of `P` in `φ_* D` is the coefficient of `Q` in `D`. -/
private theorem exists_transformDivisor_apply_eq {sS : S ⟶ Spec (.of k)} {πZ : Z₁ ⟶ S}
    (h₁ : IsNefWeakModel sY s₁ sS πY πZ KY C φ₁) (P : MMP.Mori.PrimeDivisor Z₁) :
    ∃ Q : MMP.Mori.PrimeDivisor Y,
      MMP.Mori.RationalMap.transformPrimeDivisor φ₁ Q = some P ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Y),
        MMP.Mori.RationalMap.transformDivisor φ₁ D P = D Q := by
  obtain ⟨Q, hQ⟩ : ∃ Q, MMP.Mori.RationalMap.transformPrimeDivisor φ₁ Q = some P := by
    have := h₁.not_isInverseExceptional P
    simpa [MMP.Flips.RationalMap.IsInverseExceptional] using this
  refine ⟨Q, hQ, fun D => ?_⟩
  obtain ⟨W₁, _, _, _, sW₁, p, q, h', hW₁v, -, hps, hqs, hpproj, hqproj, hpb, hqb, hinv, hh', -⟩ :=
    h₁.exists_resolution
  have := h₁.isNormalVariety_source.1
  have := h₁.isNormalVariety_target.1
  have := hW₁v
  have := isSeparated_toTerminal sY
  have := isSeparated_toTerminal s₁
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have : IsSeparated q := isSeparated_of_comp_eq hqs
  have : IsDominant q := hqb.isDominant
  have hqbij := hqb.functionFieldMap_bijective
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hQ (fun Q' hQ' => ?_) D
  obtain ⟨w, hwq, hwp⟩ := exists_apply_eq_genericPoint hinv hh' hQ
  obtain ⟨w', hwq', hwp'⟩ := exists_apply_eq_genericPoint hinv hh' hQ'
  have hww : w = w' := eq_of_apply_eq_of_coheight_le_one q hqbij (hwq'.trans hwq.symm)
    (by rw [hwq]; exact P.coheight_genericPoint.le)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hwp'.symm.trans (hww ▸ hwp))

/-- **The canonical divisor of a weak model.** For a nef weak model `φ : Y ⤏ Z` over a perfect
field, `φ_* K_Y` is a canonical divisor of `Z`. -/
private theorem exists_isCanonicalDivisor_transformDivisor [PerfectField k] {sS : S ⟶ Spec (.of k)}
    {πZ : Z₁ ⟶ S} (h₁ : IsNefWeakModel sY s₁ sS πY πZ KY C φ₁) :
    ∃ m : ℕ, Divisor.IsCanonicalDivisor s₁ m (MMP.Mori.RationalMap.transformDivisor φ₁ KY) := by
  obtain ⟨n, hKY⟩ := h₁.isCanonicalDivisor
  refine ⟨n, ?_⟩
  have hYv := h₁.isNormalVariety_source
  have hZv := h₁.isNormalVariety_target
  have := hYv.1
  have := hZv.1
  have : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType s₁ := hZv.1.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace Z₁ := QuasiCompact.compactSpace_of_compactSpace s₁
  have := isSeparated_toTerminal sY
  have := isSeparated_toTerminal s₁
  obtain ⟨W₁, _, _, _, sW₁, p, q, h', hW₁v, -, hps, hqs, hpproj, hqproj, hpb, hqb, hinv, hh', -⟩ :=
    h₁.exists_resolution
  subst hps
  have := hW₁v
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have : IsProper q := isProper_of_isProjectiveMorphism q hqproj
  have : IsSeparated p := IsSeparated.of_comp p sY
  have : IsSeparated q := isSeparated_of_comp_eq hqs
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
    hKY.topologicalKrullDim_eq
  have htr : (letI := functionFieldAlgebra s₁; Algebra.trdeg k Z₁.functionField) =
      (letI := functionFieldAlgebra sY; Algebra.trdeg k Y.functionField) := by
    rw [trdeg_functionField_eq_of_bijective s₁ q hqbij,
      trdeg_functionField_eq_of_bijective sY p hpbij]
    exact congrArg (fun t => (letI := functionFieldAlgebra t; Algebra.trdeg k W₁.functionField))
      hqs
  have hdZ : (letI := functionFieldAlgebra s₁; Algebra.trdeg k Z₁.functionField).toNat = n := by
    rwa [htr]
  have hnZ : topologicalKrullDim Z₁ = n := by
    rw [← toENat_trdeg_functionField (sX := s₁), htr, toENat_trdeg_functionField (sX := sY)]
    exact hKY.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor s₁ hZv hnZ
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYv hKY
  have hω'0 := pullbackRationalPluriForms_ne_zero sY p hpbij hdY hω0
  obtain ⟨τ, hτ, hτ0'⟩ := exists_pullbackRationalPluriForms_eq s₁ q hqbij hdZ
    (cast (congrArg (fun t => RationalPluriForms t n 1) hqs.symm)
      (pullbackRationalPluriForms sY p ω))
  have hτ0 : τ ≠ 0 := hτ0' (cast_rationalPluriForms_ne_zero hqs.symm hω'0)
  have hdiv : MMP.Mori.RationalMap.transformDivisor φ₁ KY = divisorOfForm τ := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨Q, hQ, htrQ⟩ := exists_transformDivisor_apply_eq h₁ P
    obtain ⟨E, hEP, hEiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hZv (f := q)
        (by rw [hqs]; exact ⟨hW₁v, inferInstance⟩) hqb P
    have hpE : p E.genericPoint = Q.genericPoint := by
      obtain ⟨w, hwq, hwp⟩ := exists_apply_eq_genericPoint hinv hh' hQ
      rwa [eq_of_apply_eq_of_coheight_le_one q hqbij (hwq.trans hEP.symm)
        (by rw [hEP]; exact P.coheight_genericPoint.le)]
    have : IsIso (p.stalkMap E.genericPoint) := isIso_stalkMap_of_coheight_le_one p hpbij
      (by rw [hpE]; exact Q.coheight_genericPoint.le)
    change (MMP.Mori.RationalMap.transformDivisor φ₁ KY).coeff P = (divisorOfForm τ).coeff P
    have hK : (MMP.Mori.RationalMap.transformDivisor φ₁ KY).coeff P = KY.coeff Q := htrQ KY
    rw [hK, coeff_divisorOfForm, ← hω Q,
      ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpbij hdY E Q hpE ω,
      ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso q hqbij hdZ E P hEP τ, hτ,
      ordForm_cast hqs.symm]
  rw [hdiv]
  exact hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hZv hK₀ hτ0)

/-- The adjoint `K_Z + C_Z` of a nef weak model is a real combination of Cartier divisors. -/
private theorem isCartierCombination_logCanonicalDivisor {πZ : Z₁ ⟶ S}
    (h₁ : IsNefWeakModel sY s₁ sS πY πZ KY C φ₁) :
    MMP.Flips.IsCartierCombination
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₁ C)) := by
  obtain ⟨m, r, L, hLc, heq, -⟩ := h₁.isRelativelyNef
  exact ⟨m, r, L, hLc, by rw [heq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

/-- A weak model, followed by the structure morphism of its target, is the structure morphism of
the source. -/
private theorem compHom_eq_toRationalMap_of_isNefWeakModel {sS : S ⟶ Spec (.of k)} {πZ : Z₁ ⟶ S}
    (h₁ : IsNefWeakModel sY s₁ sS πY πZ KY C φ₁) : φ₁.compHom s₁ = sY.toRationalMap := by
  rw [← h₁.comp_eq_target, ← compHom_compHom, h₁.isOver, ← h₁.comp_eq_source]
  change (πY.toPartialMap.toRationalMap).compHom sS = (πY ≫ sS).toPartialMap.toRationalMap
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toPartialMap_compHom]

/-- **The cross comparison.** Let `φ₁`, `φ₂` be nef weak models of `(Y, C)` and `p₁ : W ⟶ Z₁`,
`p₂ : W ⟶ Z₂` a common model with `h : Y ⤏ W`. If `Q ↦ P` under `φ₁` and `E` is the strict
transform of `P` on `W`, the coefficient of `E` in `p₂^*(K_{Z₂} + C_{Z₂})` is at most the
coefficient of `Q` in `K_Y + C`. -/
private theorem coeff_le_of_isNefWeakModel
    (h₁ : IsNefWeakModel sY s₁ sS πY π₁ KY C φ₁)
    (h₂ : IsNefWeakModel sY s₂ sS πY π₂ KY C φ₂)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {p₁ : W ⟶ Z₁} {p₂ : W ⟶ Z₂} {h : Y.RationalMap W}
    {D₂ : RDivisor W} (hW : MMP.Mori.IsVariety k sW) (hp₁s : p₁ ≫ s₁ = sW)
    (hp₁ : IsProjectiveMorphism p₁)
    (hp₁b : IsBirationalMorphism p₁) (hp₂b : IsBirationalMorphism p₂)
    (hh₁ : h.compHom p₁ = φ₁) (hh₂ : h.compHom p₂ = φ₂)
    (hD₂ : MMP.Flips.IsRCartierPullback p₂
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₂ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₂ C)) D₂)
    {Q : MMP.Mori.PrimeDivisor Y} {P : MMP.Mori.PrimeDivisor Z₁}
    (hQ : MMP.Mori.RationalMap.transformPrimeDivisor φ₁ Q = some P)
    {E : MMP.Mori.PrimeDivisor W} (hEP : p₁ E.genericPoint = P.genericPoint) :
    D₂.coeff E ≤ (MMP.Flips.logCanonicalDivisor KY C).coeff Q := by
  have hYv := h₁.isNormalVariety_source
  have := hYv.1
  have := h₁.isNormalVariety_target.1
  have := h₂.isNormalVariety_target.1
  have := hW
  have := isSeparated_toTerminal sY
  have := isSeparated_toTerminal s₁
  have := isSeparated_toTerminal s₂
  have : IsProper p₁ := isProper_of_isProjectiveMorphism p₁ hp₁
  have : IsSeparated p₁ := isSeparated_of_comp_eq hp₁s
  have : IsDominant p₁ := hp₁b.isDominant
  have : IsDominant p₂ := hp₂b.isDominant
  have hp₁bij := hp₁b.functionFieldMap_bijective
  obtain ⟨W₂, _, _, _, sW₂, p, q, h₂', hW₂v, -, hps, hqs, hpproj, hqproj, hpb, hqb, hinv₂, hh₂',
    GY, GZ, hGY, hGZ, hnn, -⟩ := h₂.exists_resolution
  obtain ⟨W₁, _, _, _, sW₁, p', q', h₁', hW₁v, -, hps', hqs', hpproj', hqproj', hpb', hqb',
    hinv₁, hh₁', -⟩ := h₁.exists_resolution
  have := hW₂v
  have := hW₁v
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have : IsProper p' := isProper_of_isProjectiveMorphism p' hpproj'
  have : IsSeparated p := isSeparated_of_comp_eq hps
  have : IsSeparated p' := isSeparated_of_comp_eq hps'
  have : IsDominant p := hpb.isDominant
  have : IsDominant p' := hpb'.isDominant
  have : IsDominant q := hqb.isDominant
  have : IsDominant q' := hqb'.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hp'bij := hpb'.functionFieldMap_bijective
  have hq'bij := hqb'.functionFieldMap_bijective
  obtain ⟨E₂, hE₂, hE₂iso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYv (f := p)
      (by rw [hps]; exact ⟨hW₂v, inferInstance⟩) hpb Q
  obtain ⟨g, hg, hQg⟩ : ∃ g : Y.PartialMap W, g.toRationalMap = h ∧ Q.genericPoint ∈ g.domain := by
    have : IsProper s₁ := isProper_of_isProjectiveMorphism s₁
      h₁.isProjectiveVariety_target.isProjective
    have : IsProper sW := by rw [← hp₁s]; infer_instance
    have hsW : h.compHom sW = sY.toRationalMap := by
      rw [← hp₁s, ← compHom_compHom, hh₁, compHom_eq_toRationalMap_of_isNefWeakModel h₁]
    obtain ⟨g, hg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
      (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one sY sW h hsW
        (Q.coheight_genericPoint.le))
    exact ⟨g, hg', hg⟩
  obtain ⟨g₂, hg₂, hQg₂⟩ := exists_rep_mem_domain hinv₂ Q
  obtain ⟨g₁, hg₁, hQg₁⟩ := exists_rep_mem_domain hinv₁ Q
  let U : Y.Opens := g.domain ⊓ g₂.domain ⊓ g₁.domain
  have hU : Dense (U : Set Y) := by
    simp only [U, TopologicalSpace.Opens.coe_inf]
    exact (g.dense_domain.inter_of_isOpen_left g₂.dense_domain g.domain.isOpen).inter_of_isOpen_left
      g₁.dense_domain (g.domain.isOpen.inter g₂.domain.isOpen)
  have hQU : Q.genericPoint ∈ U := ⟨⟨hQg, hQg₂⟩, hQg₁⟩
  haveI : Nonempty U := ⟨⟨_, hQU⟩⟩
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set Y))
  have hle : U ≤ g.domain := le_trans inf_le_left inf_le_left
  have hle₂ : U ≤ g₂.domain := le_trans inf_le_left inf_le_right
  have hle₁ : U ≤ g₁.domain := inf_le_right
  let a : U.toScheme ⟶ W := Y.homOfLE hle ≫ g.hom
  let b : U.toScheme ⟶ W₂ := Y.homOfLE hle₂ ≫ g₂.hom
  let c : U.toScheme ⟶ W₁ := Y.homOfLE hle₁ ≫ g₁.hom
  have hab : a ≫ p₂ = b ≫ q := comp_eq_comp_of_compHom_eq hU g g₂ hle hle₂ p₂ q
    (by rw [hg, hg₂, hh₂, hh₂'])
  have hbp : b ≫ p = U.ι := by
    have := comp_eq_ι_comp_of_compHom_eq hU g₂ hle₂ p (𝟙 Y)
      (by rw [hg₂, compHom_eq_of_isInverse hinv₂])
    rwa [Category.comp_id] at this
  have hcp : c ≫ p' = U.ι := by
    have := comp_eq_ι_comp_of_compHom_eq hU g₁ hle₁ p' (𝟙 Y)
      (by rw [hg₁, compHom_eq_of_isInverse hinv₁])
    rwa [Category.comp_id] at this
  have hac : a ≫ p₁ = c ≫ q' := comp_eq_comp_of_compHom_eq hU g g₁ hle hle₁ p₁ q'
    (by rw [hg, hg₁, hh₁, hh₁'])
  obtain ⟨QU, hQU'⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq U Q hQU
  have hx : U.ι QU.genericPoint = Q.genericPoint := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hQU']
  have hxeq : QU.genericPoint = ⟨Q.genericPoint, hQU⟩ := Subtype.ext hx
  have hpbx : p (b QU.genericPoint) = Q.genericPoint := by
    calc p (b QU.genericPoint) = (b ≫ p) QU.genericPoint := (Scheme.Hom.comp_apply _ _ _).symm
      _ = Q.genericPoint := by rwa [hbp]
  have hp'cx : p' (c QU.genericPoint) = Q.genericPoint := by
    calc p' (c QU.genericPoint) = (c ≫ p') QU.genericPoint := (Scheme.Hom.comp_apply _ _ _).symm
      _ = Q.genericPoint := by rwa [hcp]
  have hbx : b QU.genericPoint = E₂.genericPoint :=
    (eq_of_apply_eq_of_coheight_le_one p hpbij (hpbx.trans hE₂.symm)
      (by rw [hE₂]; exact Q.coheight_genericPoint.le)).symm
  have hq'cx : q' (c QU.genericPoint) = P.genericPoint := by
    have := genericPoint_eq_of_transformPrimeDivisor_eq_some hQ ⟨U, hU, c ≫ q'⟩
      ((toRationalMap_restrict_comp g₁ hU hle₁ q').trans (by rw [hg₁, hh₁'])) hQU
    rw [this, ← hxeq]
    exact Scheme.Hom.comp_apply _ _ _
  have hp₁ax : p₁ (a QU.genericPoint) = P.genericPoint := by
    calc p₁ (a QU.genericPoint) = (a ≫ p₁) QU.genericPoint := (Scheme.Hom.comp_apply _ _ _).symm
      _ = q' (c QU.genericPoint) := by rw [hac]; exact Scheme.Hom.comp_apply _ _ _
      _ = P.genericPoint := hq'cx
  have hax : a QU.genericPoint = E.genericPoint :=
    (eq_of_apply_eq_of_coheight_le_one p₁ hp₁bij (hp₁ax.trans hEP.symm)
      (by rw [hEP]; exact P.coheight_genericPoint.le)).symm
  have hbiso : IsIso (b.stalkMap QU.genericPoint) := by
    have : IsIso ((b ≫ p).stalkMap QU.genericPoint) := by rw [hbp]; infer_instance
    exact isIso_stalkMap_of_isIso_comp b p hpbij _
      (by rw [hpbx]; exact Q.coheight_genericPoint.le)
  have hciso : IsIso (c.stalkMap QU.genericPoint) := by
    have : IsIso ((c ≫ p').stalkMap QU.genericPoint) := by rw [hcp]; infer_instance
    exact isIso_stalkMap_of_isIso_comp c p' hp'bij _
      (by rw [hp'cx]; exact Q.coheight_genericPoint.le)
  have haiso : IsIso (a.stalkMap QU.genericPoint) := by
    have : IsIso (q'.stalkMap (c QU.genericPoint)) := isIso_stalkMap_of_coheight_le_one q'
      hq'bij (by rw [hq'cx]; exact P.coheight_genericPoint.le)
    have : IsIso ((a ≫ p₁).stalkMap QU.genericPoint) := by
      rw [hac, Scheme.Hom.stalkMap_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ this hciso
    exact isIso_stalkMap_of_isIso_comp a p₁ hp₁bij _
      (by rw [hp₁ax]; exact P.coheight_genericPoint.le)
  haveI : IsDominant U.ι := Opens.isDominant_ι hU
  have : IsDominant (b ≫ p) := by rw [hbp]; infer_instance
  have : IsDominant b := isDominant_of_isDominant_comp b p hpbij
  have : IsDominant (c ≫ p') := by rw [hcp]; infer_instance
  have : IsDominant c := isDominant_of_isDominant_comp c p' hp'bij
  have : IsDominant (a ≫ p₁) := by rw [hac]; infer_instance
  have : IsDominant a := isDominant_of_isDominant_comp a p₁ hp₁bij
  obtain ⟨G₁, hG₁, hG₁c⟩ := exists_isRCartierPullback_comp a p₂ hD₂
  obtain ⟨G₂, hG₂, hG₂c⟩ := exists_isRCartierPullback_comp b q hGZ
  rw [hab] at hG₁
  have hG : G₁ = G₂ := MMP.Flips.IsRCartierPullback.eq (b ≫ q) hG₁ hG₂
  have e1 : G₁.coeff QU = D₂.coeff E := hG₁c QU E hax haiso
  have e2 : G₂.coeff QU = GZ.coeff E₂ := hG₂c QU E₂ hbx hbiso
  have e3 : GY.coeff E₂ = (MMP.Flips.logCanonicalDivisor KY C).coeff Q :=
    coeff_eq_of_isRCartierPullback hGY E₂ Q hE₂
  have e4 := hnn E₂
  rw [MMP.Mori.DivisorWithCoeffs.coeff_sub] at e4
  rw [hG] at e1
  linarith

/-- **One half of the comparison.** On a common projective model `p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂`
of two nef weak models, `p₁^*D₁ - p₂^*D₂` is effective. -/
private theorem nonneg_sub_of_isNefWeakModel [IsSeparated sS]
    (h₁ : IsNefWeakModel sY s₁ sS πY π₁ KY C φ₁)
    (h₂ : IsNefWeakModel sY s₂ sS πY π₂ KY C φ₂)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {p₁ : W ⟶ Z₁} {p₂ : W ⟶ Z₂} {h : Y.RationalMap W}
    {D₁ D₂ : RDivisor W} (hW : MMP.Mori.IsVariety k sW) (hp₁s : p₁ ≫ s₁ = sW)
    (hp₂s : p₂ ≫ s₂ = sW) (hp₁ : IsProjectiveMorphism p₁) (hp₂ : IsProjectiveMorphism p₂)
    (hp₁b : IsBirationalMorphism p₁) (hp₂b : IsBirationalMorphism p₂)
    (hh₁ : h.compHom p₁ = φ₁) (hh₂ : h.compHom p₂ = φ₂)
    (hD₁ : MMP.Flips.IsRCartierPullback p₁
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₁ C)) D₁)
    (hD₂ : MMP.Flips.IsRCartierPullback p₂
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₂ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₂ C)) D₂) :
    0 ≤ D₁ - D₂ := by
  have := h₁.isNormalVariety_source.1
  have := h₁.isNormalVariety_target.1
  have := h₂.isNormalVariety_target.1
  have := hW
  have : IsProper p₁ := isProper_of_isProjectiveMorphism p₁ hp₁
  have : IsSeparated p₁ := isSeparated_of_comp_eq hp₁s
  have : IsDominant p₁ := hp₁b.isDominant
  have hp₁bij := hp₁b.functionFieldMap_bijective
  have hWp : MMP.Mori.IsProjectiveVariety k sW := by
    rw [← hp₁s]
    have : MMP.Mori.IsVariety k (p₁ ≫ s₁) := by rwa [hp₁s]
    exact ⟨hp₁.comp h₁.isProjectiveVariety_target.isProjective⟩
  have hpq : p₁ ≫ π₁ = p₂ ≫ π₂ := by
    obtain ⟨g, hg⟩ := h.exists_rep
    have := isSeparated_toTerminal sS
    haveI : Nonempty g.domain := g.dense_domain.nonempty.to_subtype
    have : IsDominant (g.hom ≫ p₁) := isDominant_hom_of_isBirational h₁.isBirational
      (g.compHom p₁) (by rw [Scheme.RationalMap.compHom_toRationalMap, hg, hh₁])
    have : IsDominant g.hom := isDominant_of_isDominant_comp g.hom p₁ hp₁bij
    refine ext_of_isDominant_of_isSeparated sS ?_ g.hom ?_
    · rw [Category.assoc, Category.assoc, h₁.comp_eq_target, h₂.comp_eq_target, hp₁s, hp₂s]
    · have e1 := comp_eq_ι_comp_of_compHom_eq g.dense_domain g le_rfl (p₁ ≫ π₁) πY
        (by rw [hg, ← compHom_compHom, hh₁, h₁.isOver])
      have e2 := comp_eq_ι_comp_of_compHom_eq g.dense_domain g le_rfl (p₂ ≫ π₂) πY
        (by rw [hg, ← compHom_compHom, hh₂, h₂.isOver])
      simp only [Scheme.homOfLE_rfl, Category.id_comp] at e1 e2
      rw [e1, e2]
  refine MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub sW s₁ s₂ ⟨hW, inferInstance⟩ hWp
    h₁.isNormalVariety_target h₁.isProjectiveVariety_target h₂.isNormalVariety_target
    h₂.isProjectiveVariety_target π₁ π₂ p₁ p₂ hp₁s hp₂s hpq hp₁ hp₁b hp₂ hp₂b
    (isCartierCombination_logCanonicalDivisor h₁)
    h₂.isRelativelyNef hD₁ hD₂ ?_
  rw [Finsupp.le_def]
  intro P
  obtain ⟨E, hEP, hEiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0}
      h₁.isNormalVariety_target (f := p₁) (by rw [hp₁s]; exact ⟨hW, inferInstance⟩) hp₁b P
  obtain ⟨Q, hQ, htrQ⟩ := exists_transformDivisor_apply_eq h₁ P
  have e1 : D₁.coeff E = (MMP.Flips.logCanonicalDivisor
      (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₁ C)).coeff P :=
    coeff_eq_of_isRCartierPullback hD₁ E P hEP
  have e2 : (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
      (MMP.Mori.RationalMap.transformDivisor φ₁ C)).coeff P =
        (MMP.Flips.logCanonicalDivisor KY C).coeff Q := by
    simp only [MMP.Flips.logCanonicalDivisor, MMP.Mori.DivisorWithCoeffs.coeff_add,
      MMP.Mori.Divisor.coeff_toRDivisor]
    have hK : (MMP.Mori.RationalMap.transformDivisor φ₁ KY).coeff P = KY.coeff Q := htrQ KY
    have hC : (MMP.Mori.RationalMap.transformDivisor φ₁ C).coeff P = C.coeff Q := htrQ C
    rw [hK, hC]
  have e3 := coeff_le_of_isNefWeakModel h₁ h₂ hW hp₁s hp₁ hp₁b hp₂b hh₁ hh₂ hD₂ hQ hEP
  have e4 : (MMP.Mori.RationalMap.transformDivisor p₁.toRationalMap (D₁ - D₂)) P =
      (D₁ - D₂).coeff E := htr (D₁ - D₂)
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [e4, MMP.Mori.DivisorWithCoeffs.coeff_sub]
  linarith

/-- **Two nef weak models have equal adjoint pull-backs** on every common projective model. -/
private theorem eq_of_isNefWeakModel [IsSeparated sS]
    (h₁ : IsNefWeakModel sY s₁ sS πY π₁ KY C φ₁)
    (h₂ : IsNefWeakModel sY s₂ sS πY π₂ KY C φ₂)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {p₁ : W ⟶ Z₁} {p₂ : W ⟶ Z₂} {h : Y.RationalMap W}
    {D₁ D₂ : RDivisor W} (hW : MMP.Mori.IsVariety k sW) (hp₁s : p₁ ≫ s₁ = sW)
    (hp₂s : p₂ ≫ s₂ = sW) (hp₁ : IsProjectiveMorphism p₁) (hp₂ : IsProjectiveMorphism p₂)
    (hp₁b : IsBirationalMorphism p₁) (hp₂b : IsBirationalMorphism p₂)
    (hh₁ : h.compHom p₁ = φ₁) (hh₂ : h.compHom p₂ = φ₂)
    (hD₁ : MMP.Flips.IsRCartierPullback p₁
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₁ C)) D₁)
    (hD₂ : MMP.Flips.IsRCartierPullback p₂
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₂ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₂ C)) D₂) :
    D₁ = D₂ :=
  le_antisymm
    (sub_nonneg.mp (nonneg_sub_of_isNefWeakModel h₂ h₁ hW hp₂s hp₁s hp₂ hp₁
      hp₂b hp₁b hh₂ hh₁ hD₂ hD₁))
    (sub_nonneg.mp (nonneg_sub_of_isNefWeakModel h₁ h₂ hW hp₁s hp₂s hp₁ hp₂
      hp₁b hp₂b hh₁ hh₂ hD₁ hD₂))

/-- `ψ = φ₁⁻¹ ∘ φ₂` when `ψ ∘ φ₁ = φ₂`. -/
private theorem eq_comp_of_comp_eq {T : Scheme.{u}} {χ : Z₁.RationalMap Y}
    [χ.IsDominant] [φ₁.IsDominant] (hχ : RationalMap.IsInverse φ₁ χ) {ψ : Z₁.RationalMap T}
    {φ : Y.RationalMap T} (hψ : φ₁.comp ψ = φ) : ψ = χ.comp φ := by
  rw [← hψ, ← Scheme.RationalMap.comp_assoc,
    comp_eq_comp_of_eq (comp_eq_id_of_isInverse hχ.symm) ψ, Scheme.RationalMap.id_comp]

/-- **Two nef weak models are equivalent nef models.** In characteristic zero, along the map
`ψ = φ₁⁻¹ ∘ φ₂` the targets of two nef weak models of `(Y, C)` are equivalent nef models: on a
smooth projective common model the adjoint pull-backs coincide, by
`eq_of_isNefWeakModel`. -/
private theorem isNefModelEquivalent_of_isNefWeakModel [CharZero k] [IsSeparated sS]
    (h₁ : IsNefWeakModel sY s₁ sS πY π₁ KY C φ₁)
    (h₂ : IsNefWeakModel sY s₂ sS πY π₂ KY C φ₂)
    (ψ : Z₁.RationalMap Z₂) [φ₁.IsDominant] (hψ : φ₁.comp ψ = φ₂) :
    IsNefModelEquivalent s₁ s₂ sS π₁ π₂
      (MMP.Mori.RationalMap.transformDivisor φ₁ KY) (MMP.Mori.RationalMap.transformDivisor φ₁ C)
      (MMP.Mori.RationalMap.transformDivisor φ₂ KY) (MMP.Mori.RationalMap.transformDivisor φ₂ C)
      ψ := by
  have hYv := h₁.isNormalVariety_source
  have hZ₁v := h₁.isNormalVariety_target
  have hZ₂v := h₂.isNormalVariety_target
  have := hYv.1
  have := hZ₁v.1
  have := hZ₂v.1
  have := isSeparated_toTerminal sY
  have := isSeparated_toTerminal s₁
  have := isSeparated_toTerminal s₂
  have := isSeparated_toTerminal sS
  have : IsProper s₁ := isProper_of_isProjectiveMorphism s₁
    h₁.isProjectiveVariety_target.isProjective
  have : IsProper s₂ := isProper_of_isProjectiveMorphism s₂
    h₂.isProjectiveVariety_target.isProjective
  obtain ⟨e₁, he₁⟩ := h₁.isBirational
  obtain ⟨e₂, he₂⟩ := h₂.isBirational
  have hχ : RationalMap.IsInverse φ₁ e₁.symm.toRationalMap := ⟨e₁, he₁, rfl⟩
  haveI : e₁.symm.toRationalMap.IsDominant := isDominant_of_isBirational hχ.isBirational_inverse
  haveI : φ₂.IsDominant := isDominant_of_isBirational h₂.isBirational
  have hψχ : ψ = e₁.symm.toRationalMap.comp φ₂ := eq_comp_of_comp_eq hχ hψ
  have hψb : RationalMap.IsBirational ψ := by
    have := isDominant_toPartialMap_hom e₁.symm
    have : IsOpenImmersion e₁.symm.toPartialMap.hom := by
      change IsOpenImmersion (e₁.iso.inv ≫ e₁.source.ι)
      infer_instance
    have : IsOpenImmersion e₂.toPartialMap.hom := by
      change IsOpenImmersion (e₂.iso.hom ≫ e₂.target.ι)
      infer_instance
    have : IsOpenImmersion (e₁.symm.toPartialMap.hom ∣_ e₂.toPartialMap.domain) := by
      have : IsOpenImmersion ((e₁.symm.toPartialMap.hom ∣_ e₂.toPartialMap.domain) ≫
          e₂.toPartialMap.domain.ι) := by
        rw [morphismRestrict_ι]
        infer_instance
      exact IsOpenImmersion.of_comp _ e₂.toPartialMap.domain.ι
    have : IsOpenImmersion (e₁.symm.toPartialMap.comp e₂.toPartialMap).hom := by
      simp only [Scheme.PartialMap.comp_hom]
      have h2 : IsOpenImmersion (e₁.symm.toPartialMap.hom ∣_ e₂.toPartialMap.domain ≫
          e₂.toPartialMap.hom) := IsOpenImmersion.comp _ _
      exact @IsOpenImmersion.comp _ _ _ _ _ (@IsOpenImmersion.of_isIso _ _ _ (Iso.isIso_inv _)) h2
    have : Nonempty (e₁.symm.toPartialMap.comp e₂.toPartialMap).domain :=
      (e₁.symm.toPartialMap.comp e₂.toPartialMap).dense_domain.nonempty.to_subtype
    rw [hψχ, ← he₂, Scheme.RationalMap.toRationalMap_comp]
    exact isBirational_of_isOpenImmersion _
  have hover : ∀ {T : Scheme.{u}} [IsSeparated (T ↘ ⊤_ Scheme)] (t₁ : Z₁ ⟶ T) (t₂ : Z₂ ⟶ T)
      (tY : Y ⟶ T), φ₁.compHom t₁ = tY.toRationalMap → φ₂.compHom t₂ = tY.toRationalMap →
        ψ.compHom t₂ = t₁.toRationalMap := by
    intro T _ t₁ t₂ tY ht₁ ht₂
    rw [hψχ, comp_compHom, ht₂, Scheme.RationalMap.comp_toRationalMap]
    exact symm_compHom_eq e₁ tY t₁ (by rwa [he₁])
  have hψS : MMP.Flips.RationalMap.IsOver π₁ π₂ ψ := hover π₁ π₂ πY h₁.isOver h₂.isOver
  have hψk : MMP.Flips.RationalMap.IsOver s₁ s₂ ψ :=
    hover s₁ s₂ sY (compHom_eq_toRationalMap_of_isNefWeakModel h₁)
      (compHom_eq_toRationalMap_of_isNefWeakModel h₂)
  obtain ⟨W, p, q, hWv, hWsm, _, _, hpb, hqb, ⟨ψ', hψ'inv, hψ'q⟩, hpq⟩ :=
    MMP.Flips.IsModificationOf.exists_smooth_common_model s₁ s₂ (𝟙 _) hZ₁v hZ₂v IsVariety.mk
      s₁ s₂ (Category.comp_id _) (Category.comp_id _) ψ ⟨hψb, hψk⟩
  have := hWv
  have : IsIntegral W := hWv.toIsIntegral
  have hWn := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWsm
  have := hWn.1
  have := hWn.2
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  obtain ⟨W', w, hW'v, hwb, g, hW'sm, hwproj, hg, -, hW'proj⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (S := Z₁) s₁
      (ι := Unit) (X := fun _ => W) (fun _ => p) (fun _ => hpb) (fun _ => ⟨hWv, inferInstance⟩)
      (κ := Empty) Empty.elim (fun j => j.elim)
  obtain ⟨hgw, hgproj, hgb⟩ := hg ()
  have := hW'v.1
  have := hW'v.2
  have : IsIntegral W' := hW'v.1.toIsIntegral
  have : LocallyOfFiniteType (w ≫ s₁) := hW'v.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (w ≫ s₁)
  have : IsProper w := isProper_of_isProjectiveMorphism w hwproj
  have : IsProper (g ()) := isProper_of_isProjectiveMorphism _ hgproj
  have : IsDominant w := hwb.isDominant
  have : IsDominant (g ()) := hgb.isDominant
  have hW'p := hW'proj h₁.isProjectiveVariety_target
  have := IsProjectiveVariety.isQuasiProjectiveVariety k (w ≫ s₁)
  have hp₂s : (g () ≫ q) ≫ s₂ = w ≫ s₁ := by
    rw [Category.assoc, ← hpq, ← Category.assoc, hgw]
  have hp₂proj : IsProjectiveMorphism (g () ≫ q) :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety (w ≫ s₁) s₂ _ hp₂s
  have hp₂b : IsBirationalMorphism (g () ≫ q) := isBirationalMorphism_comp hgb hqb
  obtain ⟨h, hh⟩ := hwb.exists_isInverse
  haveI : h.IsDominant := isDominant_of_isBirational hh.isBirational_inverse
  have hhw := compHom_eq_of_isInverse hh
  have hhg : h.compHom (g ()) = ψ' := by
    haveI : (h.compHom (g ())).IsDominant := by
      rw [← Scheme.RationalMap.comp_toRationalMap]; infer_instance
    refine eq_of_compHom_eq_id hψ'inv ?_
    rw [compHom_compHom, hgw, hhw]
  have hhψ : h.compHom (g () ≫ q) = ψ := by rw [← compHom_compHom, hhg, hψ'q]
  have hh₁ : (φ₁.comp h).compHom w = φ₁ := by
    rw [comp_compHom, hhw]
    exact Scheme.RationalMap.comp_id φ₁
  have hh₂ : (φ₁.comp h).compHom (g () ≫ q) = φ₂ := by
    rw [comp_compHom, hhψ, hψ]
  have : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (w ≫ s₁)
  obtain ⟨D₁, hD₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback w
    (isCartierCombination_logCanonicalDivisor h₁)
  obtain ⟨D₂, hD₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback (g () ≫ q)
    (isCartierCombination_logCanonicalDivisor h₂)
  have hD : D₁ = D₂ := eq_of_isNefWeakModel h₁ h₂ hW'v.1 rfl hp₂s hwproj hp₂proj hwb hp₂b
    hh₁ hh₂ hD₁ hD₂
  subst hD
  exact
    { isNormalVariety₁ := hZ₁v
      isProjectiveVariety₁ := h₁.isProjectiveVariety_target
      comp_eq₁ := h₁.comp_eq_target
      isCanonicalDivisor₁ := exists_isCanonicalDivisor_transformDivisor h₁
      isRelativelyNef₁ := h₁.isRelativelyNef
      isNormalVariety₂ := hZ₂v
      isProjectiveVariety₂ := h₂.isProjectiveVariety_target
      comp_eq₂ := h₂.comp_eq_target
      isCanonicalDivisor₂ := exists_isCanonicalDivisor_transformDivisor h₂
      isRelativelyNef₂ := h₂.isRelativelyNef
      isBirational := hψb
      isOver := hψS
      exists_resolution := ⟨W', inferInstance, inferInstance, inferInstance, w ≫ s₁, inferInstance,
        w, g () ≫ q, h, hW'v.1, hW'sm, rfl, hp₂s, hwproj, hp₂proj, hwb, hp₂b, hh, hhψ, D₁, D₁, hD₁,
        hD₂, fun _ _ => Iff.rfl⟩ }

end Comparison

end Proof_lem_fourfold_two_weak_models_crepant

namespace MMP.Fourfold

open MMP.Mori Proof_lem_fourfold_two_weak_models_crepant

/-- **Two nef weak models are crepant.** Let `φ₁ : Y ⤏ Z₁` and `φ₂ : Y ⤏ Z₂` be nef weak models
over a separated base `S` of the same pair `(Y, C)` with canonical divisor `K_Y`. Then

1. on every common projective birational normal model `p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂` with a
   rational map `h : Y ⤏ W` such that `p_i ∘ h = φ_i`, the pull-backs of the adjoints
   `K_{Z_i} + C_{Z_i}` (with `K_{Z_i} = φ_{i*} K_Y`, `C_{Z_i} = φ_{i*} C`) to `W` are equal;
2. in characteristic zero, the nef models `(Z₁, C_{Z₁})` and `(Z₂, C_{Z₂})` are equivalent
   (`MMP.Fourfold.IsNefModelEquivalent`) along any `ψ : Z₁ ⤏ Z₂` with `ψ ∘ φ₁ = φ₂`. -/
@[mmp "lem_fourfold_two_weak_models_crepant"]
public theorem IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent
    {k : Type u} [Field k] {Y Z₁ Z₂ S : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
    [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
    {sY : Y ⟶ Spec (.of k)} {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)}
    [QuasiCompact s₁] [QuasiCompact s₂] {sS : S ⟶ Spec (.of k)}
    [IsSeparated sS]
    {πY : Y ⟶ S} {π₁ : Z₁ ⟶ S} {π₂ : Z₂ ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ₁ : Y.RationalMap Z₁} {φ₂ : Y.RationalMap Z₂}
    (h₁ : IsNefWeakModel sY s₁ sS πY π₁ KY C φ₁)
    (h₂ : IsNefWeakModel sY s₂ sS πY π₂ KY C φ₂) :
    (∀ {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
      (sW : W ⟶ Spec (.of k)) (p₁ : W ⟶ Z₁) (p₂ : W ⟶ Z₂) (h : Y.RationalMap W)
      {D₁ D₂ : RDivisor W},
      MMP.Mori.IsVariety k sW → p₁ ≫ s₁ = sW → p₂ ≫ s₂ = sW →
        IsProjectiveMorphism p₁ → IsProjectiveMorphism p₂ →
        IsBirationalMorphism p₁ → IsBirationalMorphism p₂ →
        h.compHom p₁ = φ₁ → h.compHom p₂ = φ₂ →
        MMP.Flips.IsRCartierPullback p₁
          (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
            (MMP.Mori.RationalMap.transformDivisor φ₁ C)) D₁ →
        MMP.Flips.IsRCartierPullback p₂
          (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₂ KY)
            (MMP.Mori.RationalMap.transformDivisor φ₂ C)) D₂ →
        D₁ = D₂) ∧
    ∀ [CharZero k] (ψ : Z₁.RationalMap Z₂) [φ₁.IsDominant], φ₁.comp ψ = φ₂ →
      IsNefModelEquivalent s₁ s₂ sS π₁ π₂
        (MMP.Mori.RationalMap.transformDivisor φ₁ KY) (MMP.Mori.RationalMap.transformDivisor φ₁ C)
        (MMP.Mori.RationalMap.transformDivisor φ₂ KY) (MMP.Mori.RationalMap.transformDivisor φ₂ C)
        ψ := by
  refine ⟨fun {W} _ _ _ sW p₁ p₂ h D₁ D₂ hW hp₁s hp₂s hp₁ hp₂ hp₁b hp₂b hh₁ hh₂ hD₁ hD₂ ↦
    eq_of_isNefWeakModel h₁ h₂ hW hp₁s hp₂s hp₁ hp₂ hp₁b hp₂b hh₁ hh₂ hD₁ hD₂, ?_⟩
  intro _ ψ _ hψ
  exact isNefModelEquivalent_of_isNefWeakModel h₁ h₂ ψ hψ

end MMP.Fourfold
