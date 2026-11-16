module

public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.Analysis.Complex.WeierstrassDivision
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverseSeparator
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Projective
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjChartBridge
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.GlueAlgebra
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardLeray
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.CoordinateImmersion
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport

/-!
# Foundations: fibres, blowups, completions, direct images and Weierstrass preparation

This file collects the following foundational results of the minimal model program.

* **Fibres of contractions.** A contraction `f : Y ⟶ X` of varieties (proper, with
  `𝒪_X ⟶ f_* 𝒪_Y` an isomorphism) has nonempty connected fibres.
* **Blowups.** For the blowup `π : X' ⟶ X` of a Noetherian scheme in a coherent ideal `ℐ`, the
  inverse image ideal `ℐ·𝒪_{X'} = 𝒪_{X'}(-E)` of the exceptional divisor is the twisting sheaf
  `𝒪_{X'}(1)`; it is invertible and `π`-ample, it is the pullback of `𝒪(1)` along a closed
  immersion of `X'` into the projective bundle `𝐏(ℐ)` over `X`, and over every affine open `V`
  of `X` it comes from an immersion of `π⁻¹(V)` into a projective space `𝐏ⁿ_V`.
* **Completions along étale maps.** An étale morphism `ψ : U ⟶ X` with trivial residue field
  extension at `u` induces an isomorphism of completed local rings `𝒪̂_{X,ψ u} ≃ 𝒪̂_{U,u}`.
* **Direct images supported on a fibre.** For `f : X ⟶ Y` proper, `y : Y`, `j : X_y ⟶ X` the
  fibre and `𝒢` coherent on `X_y`, `(Rⁱ f_* j_* 𝒢)_y ≅ Hⁱ(X_y, 𝒢)` naturally in `𝒢`.
* **Zariski's main theorem.** A proper birational morphism `f : X ⟶ Y` of varieties onto a
  normal variety satisfies `f_* 𝒪_X = 𝒪_Y` and has connected fibres.
* **Fibre dimension.** For a morphism of varieties `g : X ⟶ Y`, the locus where the local
  dimension of the fibre is at least `e` is closed.
* **Weierstrass preparation.** A convergent power series `f(z, w)` with `f(0, w)` of order
  exactly `d ≥ 1` is uniquely a unit times a Weierstrass polynomial of degree `d` in `w`.

## Main results

* `MMP.Flips.IsContraction.isConnected_preimage_singleton`
* `MMP.Foundations.isRelativelyAmple_exceptionalIdealModule`
* `MMP.Foundations.completedStalkRingEquiv_comp_algebraMap`
* `MMP.Foundations.nonempty_rightDerivedPushforwardFiberι_stalk_iso`
* `MMP.Mori.isIso_app_and_isConnected_of_isProper_of_isBirationalMorphism`
* `MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism`
* `MMP.isClosed_setOf_le_fiberDimensionAt`
* `MMP.Convergent.existsUnique_weierstrassPreparation`

## Implementation notes

`f_* 𝒪_X = 𝒪_Y` is stated as `∀ U, IsIso (f.app U)`, the comorphism being an isomorphism on
every open. The fibre of a morphism is the topological preimage `f ⁻¹' {y}`, and `IsConnected`
includes nonemptiness. The exceptional divisor `-E` is read through its ideal sheaf
`AlgebraicGeometry.exceptionalIdealModule ℐ`. The completion of a local ring `R` is
`AdicCompletion (IsLocalRing.maximalIdeal R) R`, and the isomorphism of completions is pinned by
extending the stalk map. The local fibre dimension is the neighbourhood dimension
`topologicalKrullDimAt` of the scheme-theoretic fibre. The ring `ℂ{z, w}` is modelled by germs at
`0` of functions analytic at `0`, its units being the germs not vanishing at `0`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.1.3
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998]
* [Stacks Project, Tags 01VM, 02NS, 02OS, 03FD, 01E4, 01F5, 01XC, 02FZ, 0AY8, 0B3F]
* [A. Grothendieck, *EGA IV₃*][EGA4], 13.1.3
* [Grauert, Remmert, *Coherent analytic sheaves*], Weierstrass preparation theorem
-/

universe u

open CategoryTheory AlgebraicGeometry

/-! ### Fibres of contractions -/

/-- Every fibre `f⁻¹{x}` of a contraction `f : Y ⟶ X` of varieties is nonempty and connected. -/
@[mmp "lem_mmp_contraction_connected_fibres_dictionary"]
public theorem MMP.Flips.IsContraction.isConnected_preimage_singleton
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Scheme.{u}}
    {sX : X ⟶ AlgebraicGeometry.Spec (.of k)} {sY : Y ⟶ AlgebraicGeometry.Spec (.of k)}
    {f : Y ⟶ X} (hf : MMP.Flips.IsContraction k sX sY f) (x : X) :
    _root_.IsConnected (f ⁻¹' {x}) :=
  have := hf.isProper
  f.isConnected_preimage_singleton_of_isIso_app hf.isIso_app x

/-! ### The inverse image of the centre of a blowup is relatively (very) ample -/

section Blowup

open CategoryTheory.Limits MonoidalCategory TopologicalSpace Opposite HomogeneousIdeal
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.AlgebraicGeometry.ProjThetaCompare
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjTwistComparison
open Stacks.RelativeVeryAmple
open Stacks.Tag01VMVeryAmple

/-! ### The twist of the blowup is the relative twist of the Rees algebra -/

section Rees

open Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The chart data of the comparison -/

/-- An affine open of the base, as an object of the small affine Zariski site. -/
private abbrev siteOf (W : X.affineOpens) : X.AffineZariskiSite :=
  ⟨W.1, show IsAffineOpen W.1 from W.2⟩

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` holds for the graded comparison of the
two spellings of the Rees algebra's sections: it is an isomorphism, with two-sided inverse
`Stacks.Blowup.reesChartGradedInv`. -/
private theorem irrelevant_le_map_reesChartGradedHom (W : X.affineOpens) :
    HomogeneousIdeal.irrelevant
          ((AlgebraicGeometry.reesSituation I).sectionRingGrading W.1)
      ≤ (HomogeneousIdeal.irrelevant ((reesSheafGradedAlgebra I).grading W.1)).map
          (reesChartGradedHom I (siteOf W)) := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun n hn x hx => ?_
  rw [← reesChartGradedHom_inv_apply I (siteOf W) x]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn
    ((reesChartGradedInv I (siteOf W)).map_mem hx))

/-- **The chart of the blowup over an affine open of the base, followed by the identification of
the blowup with the relative `Proj` of the Rees algebra, is the chart there**, through the graded
comparison of the two spellings of the Rees algebra's sections.

This is `Stacks.Blowup.chart_reesProjBlowUpIso_hom` read in the other direction: its chart
comparison is `(Stacks.Blowup.reesChartProjIso …).hom`, whose inverse is
`AlgebraicGeometry.Proj.map (reesChartGradedHom …)`. -/
private theorem relativeProjChart_comp_reesProjBlowUpIso_inv (W : X.affineOpens) :
    Stacks.RelativeProj.Situation.relativeProjChart (AlgebraicGeometry.reesSituation I) W
          ≫ (reesProjBlowUpIso I).inv
      = AlgebraicGeometry.Proj.map (reesChartGradedHom I (siteOf W))
            (irrelevant_le_map_reesChartGradedHom I W)
        ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
            (reesSheafGradedAlgebra I)).chart W.1 W.2 := by
  refine (Iso.comp_inv_eq _).2 ?_
  exact ((reesChartProjIso I (siteOf W)).inv_hom_id_assoc _).symm.trans
    ((whisker_eq _ (chart_reesProjBlowUpIso_hom I (siteOf W)).symm).trans
      (Category.assoc _ _ _).symm)

/-! ### The degreewise comparison -/

/-- **The relative twist of the Rees algebra, transported to the blowup.** -/
private noncomputable def blowUpTwistReesIso (n : ℤ) :
    (Scheme.Modules.pullback (reesProjBlowUpIso I).inv).obj
        (relativeTwist (reesSheafGradedAlgebra I) n)
      ≅ AlgebraicGeometry.blowUpTwist I n :=
  twistSheafAlgebraComparisonIso (s := AlgebraicGeometry.reesSituation I)
    (reesSheafGradedAlgebra I) n (reesProjBlowUpIso I).inv
    (fun W => reesChartGradedHom I (siteOf W))
    (fun W => irrelevant_le_map_reesChartGradedHom I W)
    (fun W => relativeProjChart_comp_reesProjBlowUpIso_inv I W)
    (fun {W W'} h => (reesChartGradedHom_comp_res I (siteOf W') (siteOf W) h).symm)
    (fun W => isIso_twistMap_of_comp_eq_id _ _ n (reesChartGradedInv I (siteOf W))
      (reesChartGradedHom_comp_inv I (siteOf W)) (reesChartGradedInv_comp_hom I (siteOf W)))

end Rees

/-! ### Relative very ampleness restricts to an open of the base -/

section Restrict

/-- **Stacks Tag 01O3 for the sheaf symmetric algebra, in degree one.** For `g : S' ⟶ S`, a
quasi-coherent `E` on `S` and a quasi-coherent `E'` on `S'` identified with `g^* E`, there is a
morphism `b : 𝐏(E') ⟶ 𝐏(E)` exhibiting `𝐏(E')` as the fibre product `S' ×_S 𝐏(E)` and pulling
`𝒪_{𝐏(E)}(1)` back to `𝒪_{𝐏(E')}(1)`. -/
private theorem exists_isPullback_projectiveBundle_twistOne_iso {S S' : Scheme.{u}} (g : S' ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (E' : S'.Modules) [E'.IsQuasicoherent]
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E) :
    ∃ b : (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E')).scheme ⟶
        (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).scheme,
      IsPullback (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E')).toBase b g
          (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).toBase ∧
        Nonempty ((Scheme.Modules.pullback b).obj (twistOne E) ≅ twistOne E') := by
  refine ⟨Stacks.ProjectiveBundle.baseChangeHom g E
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) E'
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E') hE,
    Stacks.ProjectiveBundle.isPullback_baseChangeHom g E _ E' _ hE, ⟨?_⟩⟩
  exact Stacks.Chow.GenuineChern.twistPullbackIso g
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E') hE.inv _
    (Stacks.ProjectiveBundle.isPullback_baseChangeHom g E _ E' _ hE).w.symm
    (Stacks.ProjectiveBundle.exists_chart_baseChangeHom g E _ E' _ hE)

/-- **Stacks Tag 0B3F: relative very ampleness is preserved by base change.** Let `f : X ⟶ S` be
a morphism of schemes, `L` an invertible `𝒪_X`-module which is very ample relative to `f`, and
`g : S' ⟶ S` a morphism of schemes. Then the pullback of `L` to `S' ×_S X` is very ample relative
to the projection `S' ×_S X ⟶ S'`.

The proof is the source's. Relative very ampleness gives a quasi-coherent `𝒪_S`-module `E`, an
immersion `i : X ⟶ 𝐏(E)` over `S` and an isomorphism `L ≅ i^* 𝒪_{𝐏(E)}(1)`. The module `g^* E` is
quasi-coherent (Tag 01BG), its projective bundle is the base change of `𝐏(E)` and the comparison
morphism `b` pulls the twist back to the twist (Tag 01O3,
`Stacks.Tag01VMVeryAmple.projectiveBundleTwistBaseChange`), so the morphism `i'` induced by
`S' ×_S X ⟶ X ⟶ 𝐏(E)` and `S' ×_S X ⟶ S'` is a base change of `i`, hence an immersion
(Tag 01JY), it lies over `S'`, and the pullback of `L` is `i'^* 𝒪_{𝐏(g^* E)}(1)`. -/
private theorem isRelativelyVeryAmple_pullback_fst {S X S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsRelativelyVeryAmple f L) :
    IsRelativelyVeryAmple (pullback.fst g f)
      ((Scheme.Modules.pullback (pullback.snd g f)).obj L) := by
  obtain ⟨E, hE, i, him, hover, ⟨e⟩⟩ := hL
  have : E.IsQuasicoherent := hE
  have : ((Scheme.Modules.pullback g).obj E).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent S'.toRingedSpace
      S.toRingedSpace g.toLRSHom.toShHom E hE
  obtain ⟨b, hsq, ⟨tw⟩⟩ :=
    exists_isPullback_projectiveBundle_twistOne_iso g E ((Scheme.Modules.pullback g).obj E)
      (Iso.refl _)
  have hs : IsPullback (pullback.snd g f) (pullback.fst g f)
      (i ≫ (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).toBase) g := by
    rw [hover]
    exact (IsPullback.of_hasPullback g f).flip
  have hsqfinal := hs.of_bot' hsq.flip
  set i' := hsq.flip.lift (pullback.snd g f ≫ i) (pullback.fst g f)
    (by rw [Category.assoc, hs.w])
  have hfst : i' ≫ b = pullback.snd g f ≫ i := hsq.flip.lift_fst _ _ _
  have hsnd : i' ≫ (relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pullback g).obj E))).toBase =
        pullback.fst g f :=
    hsq.flip.lift_snd _ _ _
  have himm : IsImmersion i' :=
    IsImmersion.isStableUnderBaseChange.of_isPullback hsqfinal him
  have eL : (Scheme.Modules.pullback (pullback.snd g f)).obj L ≅
      (Scheme.Modules.pullback i').obj (twistOne ((Scheme.Modules.pullback g).obj E)) :=
    (Scheme.Modules.pullback (pullback.snd g f)).mapIso e ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd g f) i).app (twistOne E) ≪≫
      (Scheme.Modules.pullbackCongr hfst.symm).app (twistOne E) ≪≫
      ((Scheme.Modules.pullbackComp i' b).app (twistOne E)).symm ≪≫
      (Scheme.Modules.pullback i').mapIso tw
  exact isRelativelyVeryAmple_of_immersion _ _ ((Scheme.Modules.pullback g).obj E) i'
    himm hsnd eL

/-- **Relative very ampleness restricts to an open of the base.** If `L` is very ample relative
to `f : X ⟶ S`, then for every open `V ⊆ S` the restriction of `L` to `f⁻¹(V)` is very ample
relative to `f ∣_ V : f⁻¹(V) ⟶ V`.

It is the base change of `f` along the inclusion of `V` (Stacks Tag 0B3F), read through the
identification of `V ×_S X` with `f⁻¹(V)`. -/
private theorem isRelativelyVeryAmple_morphismRestrict {S X : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsRelativelyVeryAmple f L) (V : S.Opens) :
    IsRelativelyVeryAmple (f ∣_ V) ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) := by
  have h := isRelativelyVeryAmple_pullback_fst f V.ι L hL
  let p : (f ⁻¹ᵁ V).toScheme ⟶ pullback V.ι f :=
    (pullbackRestrictIsoRestrict f V).inv ≫ (pullbackSymmetry f V.ι).hom
  have hp₁ : p ≫ pullback.fst V.ι f = f ∣_ V := by
    simp only [p, Category.assoc, pullbackSymmetry_hom_comp_fst,
      Iso.inv_comp_eq, pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hp₂ : p ≫ pullback.snd V.ι f = (f ⁻¹ᵁ V).ι := by
    simp only [p, Category.assoc, pullbackSymmetry_hom_comp_snd,
      pullbackRestrictIsoRestrict_inv_fst]
  have e : (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L ≅
      (Scheme.Modules.pullback p).obj
        ((Scheme.Modules.pullback (pullback.snd V.ι f)).obj L) :=
    (Scheme.Modules.pullbackCongr hp₂.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp p (pullback.snd V.ι f)).app L).symm
  have h' := isRelativelyVeryAmple_of_isIso p (pullback.fst V.ι f) _ _ e h
  rwa [hp₁] at h'

end Restrict

/-! ### The blowup inside the projective bundle of the ideal -/

/-- **The blowup is a closed subscheme of `𝐏(ℐ)` over `X`, cut out so that `𝒪_{𝐏(ℐ)}(1)` restricts
to `ℐ·𝒪_{X'}`.** Here `ℐ` is the degree-one piece of the Rees algebra, which generates it; the
canonical surjection `Sym ℐ ↠ ⨁ ℐⁿ` gives the closed immersion
`Stacks.Tag01VMRelativeVeryAmple.canonicalSymProjHom`, pulling `𝒪(1)` back to the relative twist
of the Rees algebra, which `blowUpTwistReesIso` and
`AlgebraicGeometry.twistOneIsoExceptionalIdealModule` identify with `ℐ·𝒪_{X'}`. -/
private theorem exists_isClosedImmersion_projectiveBundle {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : I.IsFiniteType) :
    ∃ (E : X.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType)
        (i : blowUp I ⟶
          (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
            (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).scheme),
      IsClosedImmersion i ∧
        i ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
            (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).toBase = blowUpToBase I ∧
        Nonempty (exceptionalIdealModule I ≅
          (Scheme.Modules.pullback i).obj (Stacks.Tag01VMVeryAmple.twistOne E)) := by
  let A := Stacks.Blowup.reesSheafGradedAlgebra I
  have hgen := isGeneratedInDegreeOne_reesSheafGradedAlgebra I
  let r := Stacks.Blowup.reesProjBlowUpIso I
  haveI := Stacks.Tag01VMRelativeVeryAmple.isClosedImmersion_canonicalSymProjHom A hgen
  refine ⟨A.piece 1, inferInstance,
    by simpa using Stacks.Blowup.isFiniteType_reesSheafGradedAlgebra_piece I hI 1,
    r.inv ≫ Stacks.Tag01VMRelativeVeryAmple.canonicalSymProjHom A hgen, inferInstance, ?_,
    ⟨(twistOneIsoExceptionalIdealModule I).symm ≪≫ (blowUpTwistReesIso I 1).symm ≪≫
      (Scheme.Modules.pullback r.inv).mapIso
        (Stacks.Tag07ZRVeryAmple.twistOneIsoPullback A hgen) ≪≫
      (Scheme.Modules.pullbackComp r.inv _).app _⟩⟩
  rw [Category.assoc, Stacks.Tag01VMRelativeVeryAmple.canonicalSymProjHom_comp_toBase,
    ← Stacks.Blowup.reesProjBlowUpIso_hom_blowUpToBase I, Iso.inv_hom_id_assoc]

namespace MMP.Foundations

/-- **The inverse image of the centre of a blowup is relatively ample.** Let `X` be a Noetherian
scheme, `ℐ` a coherent sheaf of ideals on `X` and `π : X' ⟶ X` its blowup. The ideal sheaf
`ℐ·𝒪_{X'} = 𝒪_{X'}(-E)` of the exceptional divisor `E` is isomorphic to the twisting sheaf
`𝒪_{X'}(1)`, is invertible, and

* is `π`-ample,
* is very ample relative to `π` via a closed immersion over `X` into the projective bundle
  `𝐏(ℰ)` of a coherent `𝒪_X`-module `ℰ`, pulling `𝒪_{𝐏(ℰ)}(1)` back to it, and
* is very ample on `π⁻¹(V)` for every affine open `V` of `X`: there is an immersion of `π⁻¹(V)`
  into some `𝐏ⁿ_V` over `V` pulling the hyperplane sheaf back to its restriction. -/
@[mmp "lem_mmp_foundation_blowup_exceptional_negative_relatively_ample"]
public theorem isRelativelyAmple_exceptionalIdealModule {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.IsFiniteType) :
    Nonempty (blowUpTwist I 1 ≅ exceptionalIdealModule I) ∧
    ∃ _ : Stacks.Ample.IsInvertibleModule (blowUp I) (exceptionalIdealModule I),
      MMP.Mori.IsRelativelyAmple (blowUpToBase I) (exceptionalIdealModule I) ∧
      (∃ (E : X.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType)
          (i : blowUp I ⟶
            (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
              (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).scheme),
        IsClosedImmersion i ∧
          i ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
              (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).toBase = blowUpToBase I ∧
          Nonempty (exceptionalIdealModule I ≅
            (Scheme.Modules.pullback i).obj (Stacks.Tag01VMVeryAmple.twistOne E))) ∧
      ∀ V : X.Opens, IsAffineOpen V →
        Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver (blowUpToBase I ∣_ V)
          ((modulePullback (blowUpToBase I ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
            (exceptionalIdealModule I)) := by
  let e := twistOneIsoExceptionalIdealModule I
  haveI := Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso e
  have hP := exists_isClosedImmersion_projectiveBundle I hI
  obtain ⟨E, _, _, i, _, hover, ⟨e'⟩⟩ := id hP
  refine ⟨⟨e⟩, inferInstance, MMP.Mori.IsRelativelyAmple.of_stacks _ _
      ((isRelativelyAmple_congr _ _ _ e).mp (isRelativelyAmple_blowUpTwist I hI)), hP,
    fun V hV => ?_⟩
  haveI : IsAffine V.toScheme := hV
  haveI : IsProper (blowUpToBase I) := (isProjective_blowUpToBase I hI).isProper
  exact Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple _ _
    (isRelativelyVeryAmple_morphismRestrict _ _
      (isRelativelyVeryAmple_of_immersion _ _ E i inferInstance hover e') V)

end MMP.Foundations

end Blowup

/-! ### Completions along an étale map with trivial residue extension -/

section Etale

open IsLocalRing AdicCompletion

namespace MMP.AdicCompletionAux

open _root_.AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
  (hle : ∀ n, I ^ n ≤ (J ^ n).comap f)

private lemma factorPow_quotientMap {m n : ℕ} (h : m ≤ n) (y : A ⧸ I ^ n) :
    Ideal.Quotient.factorPow J h (Ideal.quotientMap (J ^ n) f (hle n) y) =
      Ideal.quotientMap (J ^ m) f (hle m) (Ideal.Quotient.factorPow I h y) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp only [Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

private lemma factorPow_comp_quotientMap_comp_evalₐ {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp ((Ideal.quotientMap (J ^ n) f (hle n)).comp
      (evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)) =
      (Ideal.quotientMap (J ^ m) f (hle m)).comp
        (evalₐ I m : AdicCompletion I A →+* A ⧸ I ^ m) := by
  ext x
  simp only [RingHom.comp_apply, RingHom.coe_coe, factorPow_quotientMap, factorPow_evalₐ]

/-- The ring map `AdicCompletion I A →+* AdicCompletion J B` induced by `f`, through the
truncations `A ⧸ Iⁿ → B ⧸ Jⁿ`. -/
private noncomputable def ringHomOfLE : AdicCompletion I A →+* AdicCompletion J B :=
  liftRingHom J (fun n => (Ideal.quotientMap (J ^ n) f (hle n)).comp
      (evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n))
    (factorPow_comp_quotientMap_comp_evalₐ f I J hle)

private lemma evalₐ_ringHomOfLE (n : ℕ) (x : AdicCompletion I A) :
    evalₐ J n (ringHomOfLE f I J hle x) = Ideal.quotientMap (J ^ n) f (hle n) (evalₐ I n x) :=
  evalₐ_liftRingHom J _ (factorPow_comp_quotientMap_comp_evalₐ f I J hle) n x

variable (hbij : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) f (hle n)))

private lemma factorPow_symm {m n : ℕ} (h : m ≤ n) (y : B ⧸ J ^ n) :
    Ideal.Quotient.factorPow I h ((RingEquiv.ofBijective _ (hbij n)).symm y) =
      (RingEquiv.ofBijective _ (hbij m)).symm (Ideal.Quotient.factorPow J h y) := by
  apply (RingEquiv.ofBijective _ (hbij m)).injective
  rw [RingEquiv.apply_symm_apply, RingEquiv.ofBijective_apply, ← factorPow_quotientMap]
  congr 1
  exact (RingEquiv.ofBijective _ (hbij n)).apply_symm_apply y

private lemma factorPow_comp_symm_comp_evalₐ {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp
      (((RingEquiv.ofBijective _ (hbij n)).symm : B ⧸ J ^ n →+* A ⧸ I ^ n).comp
        (evalₐ J n : AdicCompletion J B →+* B ⧸ J ^ n)) =
      (((RingEquiv.ofBijective _ (hbij m)).symm : B ⧸ J ^ m →+* A ⧸ I ^ m).comp
        (evalₐ J m : AdicCompletion J B →+* B ⧸ J ^ m)) := by
  ext x
  simp only [RingHom.comp_apply, RingHom.coe_coe, factorPow_symm, factorPow_evalₐ]

/-- The inverse of `ringHomOfLE f I J hle` when every truncation of `f` is bijective. -/
private noncomputable def ringHomInvOfBijective : AdicCompletion J B →+* AdicCompletion I A :=
  liftRingHom I (fun n => ((RingEquiv.ofBijective _ (hbij n)).symm : B ⧸ J ^ n →+* A ⧸ I ^ n).comp
      (evalₐ J n : AdicCompletion J B →+* B ⧸ J ^ n))
    (factorPow_comp_symm_comp_evalₐ f I J hle hbij)

private lemma evalₐ_ringHomInvOfBijective (n : ℕ) (x : AdicCompletion J B) :
    evalₐ I n (ringHomInvOfBijective f I J hle hbij x) =
      (RingEquiv.ofBijective _ (hbij n)).symm (evalₐ J n x) :=
  evalₐ_liftRingHom I _ (factorPow_comp_symm_comp_evalₐ f I J hle hbij) n x

/-- A ring map `f : A →+* B` inducing bijections `A ⧸ Iⁿ → B ⧸ Jⁿ` for all `n` induces an
isomorphism of the adic completions `AdicCompletion I A ≃+* AdicCompletion J B`: its value on a
compatible family is the family of images under the truncations of `f`. -/
public noncomputable def ringEquivOfBijective : AdicCompletion I A ≃+* AdicCompletion J B :=
  RingEquiv.ofRingHom (ringHomOfLE f I J hle) (ringHomInvOfBijective f I J hle hbij)
    (RingHom.ext fun x => ext_evalₐ fun n => by
      simp only [RingHom.comp_apply, RingHom.id_apply, evalₐ_ringHomOfLE,
        evalₐ_ringHomInvOfBijective]
      exact (RingEquiv.ofBijective _ (hbij n)).apply_symm_apply _)
    (RingHom.ext fun x => ext_evalₐ fun n => by
      simp only [RingHom.comp_apply, RingHom.id_apply, evalₐ_ringHomOfLE,
        evalₐ_ringHomInvOfBijective]
      exact (RingEquiv.ofBijective _ (hbij n)).symm_apply_apply _)

/-- `ringEquivOfBijective` is computed on each truncation by the truncation of `f`. -/
@[simp]
public lemma evalₐ_ringEquivOfBijective (n : ℕ) (x : AdicCompletion I A) :
    evalₐ J n (ringEquivOfBijective f I J hle hbij x) =
      Ideal.quotientMap (J ^ n) f (hle n) (evalₐ I n x) :=
  evalₐ_ringHomOfLE f I J hle n x

/-- `ringEquivOfBijective` extends `f`: it commutes with the maps into the completions. -/
public lemma ringEquivOfBijective_comp_algebraMap :
    (ringEquivOfBijective f I J hle hbij : AdicCompletion I A →+* AdicCompletion J B).comp
        (algebraMap A (AdicCompletion I A)) =
      (algebraMap B (AdicCompletion J B)).comp f :=
  RingHom.ext fun a => ext_evalₐ fun n => by
    simp [evalₐ_ringEquivOfBijective, AdicCompletion.algebraMap_apply]

end MMP.AdicCompletionAux

/-- If `B = f(A) + I B`, then every element of `(I B)ⁿ` agrees with the image of an element
of `Iⁿ` modulo `(I B)ⁿ⁺¹`. -/
private lemma exists_sub_mem_map_pow_succ {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) (hs : ∀ b, ∃ a, b - f a ∈ I.map f) {n : ℕ} {y : B} (hy : y ∈ (I.map f) ^ n) :
    ∃ a ∈ I ^ n, y - f a ∈ (I.map f) ^ (n + 1) := by
  rw [← Ideal.map_pow] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a₁, h₁, e₁⟩ := hx
    obtain ⟨a₂, h₂, e₂⟩ := hy
    refine ⟨a₁ + a₂, add_mem h₁ h₂, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact add_mem e₁ e₂
  | smul c y _ hy =>
    obtain ⟨a₁, h₁, e₁⟩ := hy
    obtain ⟨c₀, hc⟩ := hs c
    refine ⟨c₀ * a₁, Ideal.mul_mem_left _ _ h₁, ?_⟩
    have : c • y - f (c₀ * a₁) = c * (y - f a₁) + (c - f c₀) * f a₁ := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this, pow_succ']
    exact add_mem (Ideal.mul_mem_left _ _ (pow_succ' (I.map f) n ▸ e₁))
      (Ideal.mul_mem_mul hc (Ideal.map_pow f I n ▸ Ideal.mem_map_of_mem f h₁))

/-- If `B = f(A) + I B`, then `B = f(A) + (I B)ⁿ` for every `n`. -/
private lemma exists_sub_mem_map_pow {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) (hs : ∀ b, ∃ a, b - f a ∈ I.map f) (n : ℕ) (b : B) :
    ∃ a, b - f a ∈ (I.map f) ^ n := by
  induction n generalizing b with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih b
    obtain ⟨a', -, ha'⟩ := exists_sub_mem_map_pow_succ f I hs ha
    exact ⟨a + a', by rwa [map_add, ← sub_sub]⟩

/-- For a faithfully flat `A → B` with `B = A + I B`, each truncation `A ⧸ Iⁿ → B ⧸ (I B)ⁿ` is
bijective. -/
private lemma bijective_quotientMap_map_pow {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (I : Ideal A)
    (hs : ∀ b, ∃ a, b - algebraMap A B a ∈ I.map (algebraMap A B)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((I.map (algebraMap A B)) ^ n) (algebraMap A B)
      (Ideal.map_pow (algebraMap A B) I n ▸ Ideal.le_comap_map)) := by
  refine ⟨?_, fun y => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_pow,
      ← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat] at hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow _ I hs n b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    exact (Ideal.neg_mem_iff _).mp (by simpa using ha)

/-- If `κ(ψ u) → κ(u)` is an isomorphism, every element of `𝒪_{U,u}` is congruent to the image
of an element of `𝒪_{X,ψ u}` modulo `𝔪_u`. -/
private lemma exists_sub_stalkMap_mem_maximalIdeal {U X : Scheme} (ψ : U ⟶ X) (u : U)
    [IsIso (ψ.residueFieldMap u)] (b : U.presheaf.stalk u) :
    ∃ a, b - ψ.stalkMap u a ∈ maximalIdeal (U.presheaf.stalk u) := by
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (ψ.residueFieldMap u)).2 (U.residue u b)
  obtain ⟨a, rfl⟩ := X.residue_surjective _ y
  have h := congr($(Scheme.residue_residueFieldMap ψ u) a)
  simp only [CommRingCat.comp_apply] at h
  rw [h] at hy
  exact ⟨a, by rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]; exact hy.symm⟩

/-- For an étale `ψ`, the maximal ideal of `𝒪_{X,ψ u}` generates the maximal ideal of `𝒪_{U,u}`. -/
private lemma map_maximalIdeal_stalkMap {U X : Scheme} (ψ : U ⟶ X) [Etale ψ] (u : U) :
    (maximalIdeal (X.presheaf.stalk (ψ.base u))).map (ψ.stalkMap u).hom =
      maximalIdeal (U.presheaf.stalk u) := by
  algebraize [(ψ.stalkMap u).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u)) :=
    inferInstanceAs <| IsLocalHom (ψ.stalkMap u).hom
  have : Algebra.EssFiniteType (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u) :=
    (RingHom.essFiniteType_algebraMap).mp (LocallyOfFiniteType.stalkMap ψ u)
  have : Algebra.FormallyUnramified (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u) :=
    (RingHom.formallyUnramified_algebraMap).mp (FormallyUnramified.stalkMap ψ u)
  exact Algebra.FormallyUnramified.map_maximalIdeal
    (R := X.presheaf.stalk (ψ.base u)) (S := U.presheaf.stalk u)

private lemma pow_maximalIdeal_le_comap_stalkMap {U X : Scheme} (ψ : U ⟶ X) [Etale ψ] (u : U)
    (n : ℕ) :
    maximalIdeal (X.presheaf.stalk (ψ.base u)) ^ n ≤
      (maximalIdeal (U.presheaf.stalk u) ^ n).comap (ψ.stalkMap u).hom := by
  rw [← map_maximalIdeal_stalkMap ψ u, ← Ideal.map_pow]
  exact Ideal.le_comap_map

/-- For an étale `ψ` with `κ(ψ u) ≅ κ(u)`, each truncation `𝒪_{X,ψ u} ⧸ 𝔪ⁿ → 𝒪_{U,u} ⧸ 𝔪ⁿ` of
the stalk map is bijective. -/
private lemma bijective_quotientMap_stalkMap {U X : Scheme} (ψ : U ⟶ X) [Etale ψ] (u : U)
    [IsIso (ψ.residueFieldMap u)] (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (maximalIdeal (U.presheaf.stalk u) ^ n)
      (ψ.stalkMap u).hom (pow_maximalIdeal_le_comap_stalkMap ψ u n)) := by
  algebraize [(ψ.stalkMap u).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u)) :=
    inferInstanceAs <| IsLocalHom (ψ.stalkMap u).hom
  have : Module.Flat (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u) :=
    RingHom.flat_algebraMap_iff.mp (Flat.stalkMap ψ u)
  have : Module.FaithfullyFlat (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u) :=
    .of_flat_of_isLocalHom
  have key : ∀ (J : Ideal (U.presheaf.stalk u))
      (_ : (maximalIdeal (X.presheaf.stalk (ψ.base u))).map
        (algebraMap (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u)) = J)
      (h : maximalIdeal (X.presheaf.stalk (ψ.base u)) ^ n ≤ (J ^ n).comap
        (algebraMap (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u))),
      Function.Bijective (Ideal.quotientMap (J ^ n)
        (algebraMap (X.presheaf.stalk (ψ.base u)) (U.presheaf.stalk u)) h) := by
    rintro _ rfl h
    exact bijective_quotientMap_map_pow _
      (map_maximalIdeal_stalkMap ψ u ▸ exists_sub_stalkMap_mem_maximalIdeal ψ u) n
  exact key _ (map_maximalIdeal_stalkMap ψ u) _

namespace MMP.Foundations

/-- **The completed stalk map** `ψ̂^* : 𝒪̂_{X,ψ u} ≃+* 𝒪̂_{U,u}` of an étale morphism `ψ : U ⟶ X`
inducing an isomorphism of residue fields `κ(ψ u) ≅ κ(u)`: the extension of the stalk map
`ψ.stalkMap u` to the maximal-ideal-adic completions, which is an isomorphism since each truncation
`𝒪_{X,ψ u} ⧸ 𝔪ⁿ → 𝒪_{U,u} ⧸ 𝔪ⁿ` is. -/
public noncomputable def completedStalkRingEquiv {U X : Scheme}
    (ψ : U ⟶ X) [Etale ψ] (u : U) [IsIso (ψ.residueFieldMap u)] :
    AdicCompletion (maximalIdeal (X.presheaf.stalk (ψ.base u))) (X.presheaf.stalk (ψ.base u)) ≃+*
      AdicCompletion (maximalIdeal (U.presheaf.stalk u)) (U.presheaf.stalk u) :=
  MMP.AdicCompletionAux.ringEquivOfBijective (ψ.stalkMap u).hom _ _
    (pow_maximalIdeal_le_comap_stalkMap ψ u) (bijective_quotientMap_stalkMap ψ u)

/-- An étale morphism `ψ : U ⟶ X` inducing an isomorphism of residue fields `κ(ψ u) ≅ κ(u)`
induces an isomorphism of the completed local rings `ψ̂^* : 𝒪̂_{X,ψ u} ≃+* 𝒪̂_{U,u}`: the ring
isomorphism `completedStalkRingEquiv ψ u` extends the stalk map `ψ.stalkMap u`. -/
@[mmp "lem_mmp_foundation_etale_residue_iso_completion"]
public theorem completedStalkRingEquiv_comp_algebraMap
    {U X : Scheme} (ψ : U ⟶ X) [Etale ψ] (u : U) [IsIso (ψ.residueFieldMap u)] :
    (completedStalkRingEquiv ψ u : _ →+* _).comp (algebraMap (X.presheaf.stalk (ψ.base u))
        (AdicCompletion (maximalIdeal (X.presheaf.stalk (ψ.base u)))
          (X.presheaf.stalk (ψ.base u)))) =
      (algebraMap (U.presheaf.stalk u)
        (AdicCompletion (maximalIdeal (U.presheaf.stalk u)) (U.presheaf.stalk u))).comp
        (ψ.stalkMap u).hom :=
  MMP.AdicCompletionAux.ringEquivOfBijective_comp_algebraMap _ _ _ _ _

end MMP.Foundations

end Etale

/-! ### Higher direct images of modules supported on a fibre -/

section FibreDirectImage

open CategoryTheory.Limits Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImagePresheaf

attribute [local instance 3000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Leray

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The pushforward of an injective module is acyclic for any further pushforward, its underlying
abelian sheaf being flasque. -/
private theorem rightAcyclic_modulePushforward_obj_of_injective
    (I : SheafOfModules.{u} (structureSheafRing X)) (hI : Injective I) :
    (modulePushforward g).rightAcyclic ((modulePushforward f).obj I) := by
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  refine (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n _).2 ?_
  exact @Stacks.Cohomology.FlasquePushforward.isZero_rightDerivedPlus_modulePushforward_of_isFlasque
    _ _ g _
    (Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isFlasque_toSheaf_modulePushforward
      f I hI)
    (n : ℤ) (by exact_mod_cast hn)

/-- `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` on bounded below derived categories ([Stacks, Tag 01F5]). -/
private noncomputable def derivedPushforwardPlusCompIso :
    (modulePushforward (f ≫ g)).rightDerivedFunctorPlus ≅
      (modulePushforward f).rightDerivedFunctorPlus ⋙
        (modulePushforward g).rightDerivedFunctorPlus :=
  have _ : IsIso (Functor.rightDerivedFunctorPlusComp
      (modulePushforward f) (modulePushforward g)) :=
    Stacks.Cohomology.AcyclicCollapse.isIso_derivedComposition _ _
      (fun I hI => rightAcyclic_modulePushforward_obj_of_injective f g I hI)
  Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso
      (Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso f g) ≪≫
    asIso (Functor.rightDerivedFunctorPlusComp
      (modulePushforward f) (modulePushforward g))

/-- The Leray comparison `Rᵖ g_* ∘ f_* ⟶ Rᵖ (f ≫ g)_*`. -/
private noncomputable def compNatTrans (p : ℤ) :
    modulePushforward f ⋙ (modulePushforward g).rightDerivedPlus p ⟶
      (modulePushforward (f ≫ g)).rightDerivedPlus p :=
  Functor.whiskerRight (Stacks.AffineCohomologyPushforward.singlePushforwardUnit f)
      ((modulePushforward g).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ p) ≫
    Functor.whiskerLeft
      (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0)
      (Functor.whiskerRight (derivedPushforwardPlusCompIso f g).inv
        (DerivedCategory.Plus.homologyFunctor _ p))

/-- The Leray comparison is invertible on `f_*`-acyclic modules. -/
private theorem isIso_compNatTrans_app (p : ℤ)
    {F : SheafOfModules.{u} (structureSheafRing X)} (hF : (modulePushforward f).rightAcyclic F) :
    IsIso ((compNatTrans f g p).app F) := by
  have hσ : IsIso ((Stacks.AffineCohomologyPushforward.singlePushforwardUnit f).app F) :=
    Stacks.AffineCohomologyPushforward.isIso_singlePushforwardUnit_app f hF
  change IsIso
    (((modulePushforward g).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ p).map
          ((Stacks.AffineCohomologyPushforward.singlePushforwardUnit f).app F) ≫
      (DerivedCategory.Plus.homologyFunctor _ p).map
        ((derivedPushforwardPlusCompIso f g).inv.app
          ((DerivedCategory.Plus.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)))
  infer_instance

end Leray

/-- If the restriction maps of `P` between open neighbourhoods of `y` are invertible, the germ
of the global sections at `y` is invertible. -/
private theorem isIso_germ_top {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{u} T) (y : T)
    (h : ∀ (U V : Opens T) (hUV : U ≤ V), y ∈ U → IsIso (P.map (homOfLE hUV).op)) :
    IsIso (P.germ ⊤ y trivial) := by
  have hT : IsTerminal (⊤ : OpenNhds y) :=
    IsTerminal.ofUniqueHom (fun V => homOfLE (le_top : V ≤ ⊤))
      (fun _ _ => Subsingleton.elim _ _)
  haveI : ∀ (i j : (OpenNhds y)ᵒᵖ) (f : j ⟶ i),
      IsIso (((OpenNhds.inclusion y).op ⋙ P).map f) := by
    intro i j f
    exact h i.unop.1 j.unop.1 (leOfHom f.unop) i.unop.2
  exact isIso_ι_of_isInitial hT.op ((OpenNhds.inclusion y).op ⋙ P)

/-- The germ at `y` of global sections, natural in the presheaf. -/
private noncomputable def germTopNatTrans (T : TopCat.{u}) (y : T) :
    (evaluation (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) ⟶
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y where
  app P := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := T) P ⊤ y trivial
  naturality P Q f := (TopCat.Presheaf.stalkFunctor_map_germ ⊤ y trivial f).symm

/-- Restriction in cohomology along an equality of opens is invertible. -/
private theorem isIso_Hrestrict_of_eq {T : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
    {U V : Opens T} (h : U ≤ V) (e : U = V) (n : ℕ) (F : SheafOfModules.{u} R) :
    IsIso (Hrestrict R h n F) := by
  subst e
  have : secRestrict R h = 𝟙 _ := by
    have : homOfLE h = 𝟙 U := Subsingleton.elim _ _
    simp only [secRestrict, this, op_id, CategoryTheory.Functor.map_id]
    rfl
  change IsIso ((NatTrans.rightDerived (secRestrict R h) n).app F)
  rw [this, NatTrans.rightDerived_id]
  infer_instance

attribute [local instance] RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint

/-- Sheafifying a presheaf of modules does not change its stalks. -/
private noncomputable def stalkSheafificationIso {T : TopCat.{u}}
    (RS : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (y : T) :
    PresheafOfModules.toPresheaf RS.obj ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y ≅
      PresheafOfModules.sheafification (𝟙 RS.obj) ⋙ SheafOfModules.toSheaf RS ⋙
        sheafToPresheaf _ _ ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y :=
  haveI : IsIso (Functor.whiskerRight (Functor.whiskerLeft (PresheafOfModules.toPresheaf RS.obj)
      (sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{u}).unit)
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y)) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun P => ?_)
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y AddCommGrpCat.{u}
      ((PresheafOfModules.toPresheaf RS.obj).obj P)
  asIso (Functor.whiskerRight (Functor.whiskerLeft (PresheafOfModules.toPresheaf RS.obj)
      (sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{u}).unit)
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y)) ≪≫
    Functor.isoWhiskerRight (PresheafOfModules.sheafificationCompToSheaf (𝟙 RS.obj)).symm
      (sheafToPresheaf _ _ ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y)

/-- If `(opensMap f).obj V = ⊤` for every open neighbourhood `V` of `y`, then
`(Rⁿ f_* 𝒢)_y ≅ Hⁿ(X, 𝒢)`, naturally in `𝒢`, for a morphism of ringed spaces `f : X ⟶ Y`: the
cohomology presheaf `V ↦ Hⁿ(f⁻¹ V, 𝒢)` is constant near `y`. -/
private noncomputable def MMP.Foundations.stalkRightDerivedPlusIsoAux {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (y : Y) (hy : ∀ V : Opens Y.carrier, y ∈ V → (opensMap f).obj V = ⊤) (n : ℕ) :
    (modulePushforward f).rightDerivedPlus (n : ℤ) ⋙
        SheafOfModules.toSheaf (structureSheafRing Y) ⋙ sheafToPresheaf _ _ ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y ≅
      Hfunctor (structureSheafRing X) ((opensMap f).obj ⊤) n := by
  let F := cohFunctor.{u, u, u, u, u, u} (opensMap f) (structureSheafRing X)
    (structureSheafRing Y) (structureSheafHom f)
  let RS := structureSheafRing Y
  let germ := Functor.whiskerLeft (F.rightDerived n ⋙ PresheafOfModules.toPresheaf RS.obj)
    (germTopNatTrans Y.carrier y)
  haveI : IsIso germ := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun G => ?_)
    refine isIso_germ_top _ y (fun U V hUV hyU => ?_)
    have key := preimageCohomologyPresheaf_map_eq_Hrestrict f hUV n G
    have hR : IsIso (Hrestrict (structureSheafRing X)
        (leOfHom ((opensMap f).map (homOfLE hUV))) n G) :=
      isIso_Hrestrict_of_eq _ _ ((hy U hyU).trans (hy V (hUV hyU)).symm) n G
    have : ((PresheafOfModules.toPresheaf RS.obj).obj ((F.rightDerived n).obj G)).map
        (homOfLE hUV).op =
        ((preimageCohomologyPresheaf_evaluation_iso f V n).app G).hom ≫
          Hrestrict (structureSheafRing X)
            (leOfHom ((opensMap f).map (homOfLE hUV))) n G ≫
          ((preimageCohomologyPresheaf_evaluation_iso f U n).app G).inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact key
    change IsIso (((PresheafOfModules.toPresheaf RS.obj).obj ((F.rightDerived n).obj G)).map
        (homOfLE hUV).op)
    rw [this]
    infer_instance
  have e1 : (modulePushforward f).rightDerivedPlus (n : ℤ) ⋙
        SheafOfModules.toSheaf (structureSheafRing Y) ⋙ sheafToPresheaf _ _ ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y ≅
      F.rightDerived n ⋙ PresheafOfModules.sheafification (𝟙 RS.obj) ⋙
        SheafOfModules.toSheaf RS ⋙ sheafToPresheaf _ _ ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y :=
    Functor.isoWhiskerRight (higherDirectImage_iso_sheafify_preimageCohomology f n) _
  have e2 : F.rightDerived n ⋙ PresheafOfModules.sheafification (𝟙 RS.obj) ⋙
        SheafOfModules.toSheaf RS ⋙ sheafToPresheaf _ _ ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y ≅
      F.rightDerived n ⋙ PresheafOfModules.toPresheaf RS.obj ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y :=
    Functor.isoWhiskerLeft (F.rightDerived n) (stalkSheafificationIso RS y).symm
  have e3 : F.rightDerived n ⋙ PresheafOfModules.toPresheaf RS.obj ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y ≅
      F.rightDerived n ⋙ PresheafOfModules.toPresheaf RS.obj ⋙
        (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
    (asIso germ).symm
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ preimageCohomologyPresheaf_evaluation_iso f ⊤ n

open Stacks.SchemeCohomology in
/-- If `h ⁻¹ᵁ V = ⊤` for every open neighbourhood `V` of `y`, then `(Rⁿ h_* 𝒢)_y ≅ Hⁿ(W, 𝒢)`,
naturally in `𝒢`: the cohomology presheaf `V ↦ Hⁿ(h⁻¹ V, 𝒢)` is constant near `y`. -/
private noncomputable def stalkRightDerivedPlusIso {W Y : Scheme.{u}} (h : W ⟶ Y) (y : Y)
    (hy : ∀ V : Y.Opens, y ∈ V → h ⁻¹ᵁ V = ⊤) (n : ℕ) :
    (Scheme.Modules.pushforward h).rightDerivedPlus (n : ℤ) ⋙ Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor _ y ≅ Hfunctor W.ringCatSheaf ⊤ n :=
  MMP.Foundations.stalkRightDerivedPlusIsoAux (hom h) y hy n

/-- Module cohomology of the global sections is abelian sheaf cohomology ([Stacks, Tag 03FD]). -/
private noncomputable def hfunctorTopIso {W : Scheme.{u}} (n : ℕ) :
    Hfunctor W.ringCatSheaf ⊤ n ≅
      SheafOfModules.toSheaf W.ringCatSheaf ⋙
        Sheaf.functorH.{u} (Opens.grothendieckTopology W) n :=
  haveI := Stacks.Cohomology.GlobalSections.additive_Γ.{u, u, u} (Opens.grothendieckTopology W)
  ModuleSheafCohomology.sectionsComparisonIso _ W.ringCatSheaf ⊤ n ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.rightDerivedIsoOfNatIso
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology W) AddCommGrpCat.{u}
          isTerminalTop) n).symm ≪≫
        Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH _ n)

/-- `Spec κ(y) ⟶ Y` is affine: the preimage of any open is empty or everything. -/
private theorem isAffineHom_fromSpecResidueField {Y : Scheme.{u}} (y : Y) :
    IsAffineHom (Y.fromSpecResidueField y) :=
  ⟨fun U _ => (Opens.eq_bot_or_top ((Y.fromSpecResidueField y) ⁻¹ᵁ U)).elim
    (fun h => h ▸ isAffineOpen_bot _) (fun h => h ▸ isAffineOpen_top _)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre inclusion is affine, as a base change of `Spec κ(y) ⟶ Y`. -/
private theorem isAffineHom_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    IsAffineHom (f.fiberι y) :=
  MorphismProperty.pullback_fst _ _ (isAffineHom_fromSpecResidueField y)

/-- The fibre maps entirely into every neighbourhood of `y`. -/
private theorem preimage_fiberι_comp_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (V : Y.Opens) (hV : y ∈ V) : (f.fiberι y ≫ f) ⁻¹ᵁ V = ⊤ := by
  ext x
  have : f (f.fiberι y x) = y :=
    (f.range_fiberι y ▸ Set.mem_range_self x : f.fiberι y x ∈ f ⁻¹' {y})
  simpa [this] using hV

namespace MMP.Foundations

/-- For a proper morphism `f : X ⟶ Y` and a point `y : Y`, the stalk at `y` of
`Rⁱ f_* (j_* 𝒢)`, where `j = f.fiberι y` is the inclusion of the fibre, is naturally
isomorphic to `Hⁱ(X_y, 𝒢)`, for `𝒢` a coherent module on the fibre `f.fiber y`. -/
@[mmp "lem_mmp_foundation_fibre_supported_direct_image_stalk"]
public theorem nonempty_rightDerivedPushforwardFiberι_stalk_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (y : Y) (i : ℕ) :
    Nonempty
      (ObjectProperty.ι (Stacks.SheafOfModules.coherentModules (f.fiber y).ringCatSheaf) ⋙
          Scheme.Modules.pushforward (f.fiberι y) ⋙
          (Scheme.Modules.pushforward f).rightDerived i ⋙
          Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor _ y ≅
        ObjectProperty.ι (Stacks.SheafOfModules.coherentModules (f.fiber y).ringCatSheaf) ⋙
          SheafOfModules.toSheaf (f.fiber y).ringCatSheaf ⋙
          Sheaf.functorH.{u} (Opens.grothendieckTopology (f.fiber y)) i) := by
  let P := Stacks.SheafOfModules.coherentModules (f.fiber y).ringCatSheaf
  haveI := isAffineHom_fiberι f y
  let c : ObjectProperty.ι P ⋙ Scheme.Modules.pushforward (f.fiberι y) ⋙
      (Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ) ⟶
      ObjectProperty.ι P ⋙ (Scheme.Modules.pushforward (f.fiberι y ≫ f)).rightDerivedPlus (i : ℤ) :=
    Functor.whiskerLeft (ObjectProperty.ι P)
      (compNatTrans (Stacks.SchemeCohomology.hom (f.fiberι y)) (Stacks.SchemeCohomology.hom f) i)
  haveI : IsIso c := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M => ?_)
    haveI : M.obj.IsQuasicoherent := @isQuasicoherent_of_isCoherent _ _ _ M.obj
      (CoherentAbelian.isCoherent_of_stacksIsCoherent M.property)
    exact isIso_compNatTrans_app _ _ _
      (Stacks.AffineHigherDirectImage.rightAcyclic_pushforward (f.fiberι y) M.obj)
  exact ⟨Functor.isoWhiskerLeft (ObjectProperty.ι P)
      (Functor.isoWhiskerLeft (Scheme.Modules.pushforward (f.fiberι y))
        (Functor.isoWhiskerRight
          (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i) _)) ≪≫
    Functor.isoWhiskerRight (asIso c) (Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor _ y) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι P)
      (stalkRightDerivedPlusIso (f.fiberι y ≫ f) y (preimage_fiberι_comp_eq_top f y) i ≪≫
        hfunctorTopIso i)⟩

end MMP.Foundations

end FibreDirectImage

/-! ### Zariski's main theorem for proper birational morphisms -/

namespace MMP.Mori

/-- **Zariski's main theorem for proper birational morphisms.** If `f : X ⟶ Y` is a proper
birational morphism of varieties over `k` and `Y` is normal, then `f_* 𝒪_X = 𝒪_Y` — the canonical
map `f.app U : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)` is an isomorphism for every open `U` of `Y` — and every
fibre `f ⁻¹' {y}` is connected. -/
@[mmp "lem_mmp_foundation_km3c_birational_pushforward_connected"]
public theorem isIso_app_and_isConnected_of_isProper_of_isBirationalMorphism {k : Type u}
    [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : IsVariety k sX) (hY : IsNormalVariety k sY) (f : X ⟶ Y) [IsProper f]
    (hb : IsBirationalMorphism f) :
    (∀ U : Y.Opens, IsIso (f.app U)) ∧ ∀ y : Y, _root_.IsConnected (f ⁻¹' {y}) :=
  MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sX sY hX hY f hb

/-- **Zariski's main theorem, structure-sheaf form.** If `f : X ⟶ Z` is a proper birational
morphism of varieties over `k` and `Z` is normal, then `f_* 𝒪_X = 𝒪_Z`: the canonical map
`f.app U : Γ(Z, U) ⟶ Γ(X, f ⁻¹ᵁ U)` is an isomorphism for every open `U` of `Z`. -/
@[mmp "lem_mmp_foundation_proper_birational_normal_structure_sheaf"]
public theorem isIso_app_of_isProper_of_isBirationalMorphism {k : Type u} [Field k]
    {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (hX : IsVariety k sX) (hZ : IsNormalVariety k sZ) (f : X ⟶ Z) [IsProper f]
    (hb : IsBirationalMorphism f) (U : Z.Opens) :
    IsIso (f.app U) :=
  (isIso_app_and_isConnected_of_isProper_of_isBirationalMorphism sX sZ hX hZ f hb).1 U

end MMP.Mori

/-! ### Upper semicontinuity of the local fibre dimension -/

namespace MMP

/-- In `WithBot ℕ∞`, `e + 1 ≤ d` exactly when `d ≤ e` fails. -/
private lemma natCast_succ_le_iff_not_le (d : WithBot ℕ∞) (e : ℕ) :
    ((e + 1 : ℕ) : WithBot ℕ∞) ≤ d ↔ ¬ d ≤ e := by
  rw [not_le]
  induction d using WithBot.recBotCoe with
  | bot => simp
  | coe d =>
    norm_cast
    exact ENat.add_one_le_iff (ENat.coe_ne_top e)

/-- For a morphism of varieties `g : X ⟶ Y` over a field `k` and a natural number `e`, the set of
points `x` at which the fibre `g⁻¹(g(x))` has local dimension at least `e` is closed. -/
@[mmp "lem_mmp_foundation_variety_fibre_dimension_semicontinuity"]
public theorem isClosed_setOf_le_fiberDimensionAt (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsVariety k pX] [IsVariety k pY]
    (g : X ⟶ Y) (hg : g ≫ pY = pX) (e : ℕ) :
    IsClosed {x : X | (e : WithBot ℕ∞) ≤ topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x)} := by
  have : LocallyOfFiniteType pX := IsVariety.toLocallyOfFiniteType (k := k)
  have : LocallyOfFiniteType (g ≫ pY) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g pY
  rcases e with _ | e
  · convert isClosed_univ
    exact Set.eq_univ_of_forall fun x => by simpa using topologicalKrullDimAt_nonneg _
  · simpa only [natCast_succ_le_iff_not_le, ← Set.compl_setOf] using
      (isOpen_setOf_fiberDimensionAt_le g e).isClosed_compl

end MMP

/-! ### Weierstrass preparation -/

namespace MMP.Convergent

open Filter Topology

/-- The remainder coefficients of the division of `w ^ d` by `f` vanish at `z = 0`, and the
quotient does not vanish at the origin. -/
private theorem weierstrassDivision_coeff_eq_zero_and_ne_zero {k d : ℕ} (hd : 1 ≤ d)
    {f : (Fin k → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfd : analyticOrderAt (fun w : ℂ ↦ f (0, w)) 0 = d)
    {q : (Fin k → ℂ) × ℂ → ℂ} {b : Fin d → (Fin k → ℂ) → ℂ} (hq : AnalyticAt ℂ q 0)
    (hb : ∀ i, AnalyticAt ℂ (b i) 0)
    (hdiv : (fun p : (Fin k → ℂ) × ℂ ↦ p.2 ^ d) =ᶠ[𝓝 0]
      fun p ↦ f p * q p + ∑ i, b i p.1 * p.2 ^ (i : ℕ)) :
    (∀ i, b i 0 = 0) ∧ q 0 ≠ 0 := by
  -- the restriction map `(z', w) ↦ (0, w)` on `(Fin 0 → ℂ) × ℂ`
  let ι : ((Fin 0 → ℂ) × ℂ) →L[ℂ] ((Fin k → ℂ) × ℂ) :=
    (0 : ((Fin 0 → ℂ) × ℂ) →L[ℂ] (Fin k → ℂ)).prod (ContinuousLinearMap.snd ℂ _ ℂ)
  have hι : ∀ p, ι p = (0, p.2) := fun p ↦ rfl
  have hι0 : Tendsto ι (𝓝 0) (𝓝 0) := ι.continuous.tendsto' 0 0 (map_zero ι)
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.comp_of_eq (analyticAt_const.prod analyticAt_id)
    (by simp) |>.analyticOrderAt_eq_natCast).1 hfd
  have hf0 : AnalyticAt ℂ (fun p : (Fin 0 → ℂ) × ℂ ↦ f (0, p.2)) 0 :=
    hf.comp_of_eq (ι.analyticAt 0) (by simp [hι])
  obtain ⟨q₀, c, -, huniq⟩ := MMP.Convergent.existsUnique_weierstrassDivision hd hf0 hfd
    (h := fun p ↦ p.2 ^ d) (analyticAt_snd.pow d)
  have hA := huniq (fun p ↦ q (0, p.2)) (fun i _ ↦ b i 0)
    (hq.comp_of_eq (ι.analyticAt 0) (by simp [hι])) (fun _ ↦ analyticAt_const)
    (by filter_upwards [hι0.eventually hdiv] with p hp using by simpa [hι] using hp)
  have hgw : Tendsto (fun p : (Fin 0 → ℂ) × ℂ ↦ p.2) (𝓝 0) (𝓝 0) :=
    continuous_snd.tendsto' 0 0 rfl
  have hB := huniq (fun p ↦ (g p.2)⁻¹) (fun _ _ ↦ 0)
    ((hg.inv hg0).comp_of_eq analyticAt_snd rfl) (fun _ ↦ analyticAt_const)
    (by
      filter_upwards [hgw.eventually hfg, hgw.eventually (hg.continuousAt.eventually_ne hg0)]
        with p hp hp'
      simp only [Function.comp_apply, sub_zero, smul_eq_mul, id] at hp
      simp [hp, hp'])
  refine ⟨fun i ↦ by simpa using ((hA.2 i).trans (hB.2 i).symm).self_of_nhds, ?_⟩
  rw [Prod.zero_eq_mk,
    show q (0, 0) = (g 0)⁻¹ by simpa using (hA.1.trans hB.1.symm).self_of_nhds]
  exact inv_ne_zero hg0

/-- **Weierstrass preparation** in the ring of convergent power series `ℂ{z, w}`: if
`w ↦ f (0, w)` has order exactly `d ≥ 1` at `0`, then near `0`,
`f = u * (w ^ d + ∑ i < d, a i (z) * w ^ i)` with `u` analytic at `0` and `u 0 ≠ 0` (a unit),
and each `a i` analytic at `0` with `a i 0 = 0`; the germs of `u` and of the `a i` are
unique. -/
@[mmp "thm_mmp_convergent_weierstrass_preparation"]
public theorem existsUnique_weierstrassPreparation {k d : ℕ} (hd : 1 ≤ d)
    {f : (Fin k → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfd : analyticOrderAt (fun w : ℂ ↦ f (0, w)) 0 = d) :
    ∃ u : (Fin k → ℂ) × ℂ → ℂ, ∃ a : Fin d → (Fin k → ℂ) → ℂ,
      (AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧ (∀ i, AnalyticAt ℂ (a i) 0 ∧ a i 0 = 0) ∧
        f =ᶠ[𝓝 0] fun p ↦ u p * (p.2 ^ d + ∑ i, a i p.1 * p.2 ^ (i : ℕ))) ∧
      ∀ (u' : (Fin k → ℂ) × ℂ → ℂ) (a' : Fin d → (Fin k → ℂ) → ℂ),
        AnalyticAt ℂ u' 0 → u' 0 ≠ 0 → (∀ i, AnalyticAt ℂ (a' i) 0 ∧ a' i 0 = 0) →
        (f =ᶠ[𝓝 0] fun p ↦ u' p * (p.2 ^ d + ∑ i, a' i p.1 * p.2 ^ (i : ℕ))) →
        u' =ᶠ[𝓝 0] u ∧ ∀ i, a' i =ᶠ[𝓝 0] a i := by
  obtain ⟨q, b, ⟨hq, hb, hdiv⟩, huniq⟩ := MMP.Convergent.existsUnique_weierstrassDivision hd hf
    hfd (h := fun p ↦ p.2 ^ d) (analyticAt_snd.pow d)
  obtain ⟨hb0, hq0⟩ := weierstrassDivision_coeff_eq_zero_and_ne_zero hd hf hfd hq hb hdiv
  refine ⟨fun p ↦ (q p)⁻¹, fun i z ↦ -b i z, ⟨hq.inv hq0, inv_ne_zero hq0,
    fun i ↦ ⟨(hb i).neg, by simp [hb0 i]⟩, ?_⟩, ?_⟩
  · filter_upwards [hdiv, hq.continuousAt.eventually_ne hq0] with p hp hp'
    simp only [neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, hp]
    field_simp
    ring
  · intro u' a' hu' hu'0 ha' hfeq
    have h := huniq (fun p ↦ (u' p)⁻¹) (fun i z ↦ -a' i z) (hu'.inv hu'0)
      (fun i ↦ (ha' i).1.neg) (by
        filter_upwards [hfeq, hu'.continuousAt.eventually_ne hu'0] with p hp hp'
        simp only [hp, neg_mul, Finset.sum_neg_distrib]
        field_simp
        ring)
    refine ⟨?_, fun i ↦ ?_⟩
    · filter_upwards [h.1] with p hp
      rw [← hp, inv_inv]
    · filter_upwards [h.2 i] with z hz
      simp [← hz]

end MMP.Convergent
