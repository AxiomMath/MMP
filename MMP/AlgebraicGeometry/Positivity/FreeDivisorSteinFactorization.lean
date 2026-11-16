module
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.VectorBundleIso
public import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne
import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafInvertible
/-!
# Foundational lemmas: Stein factors of free divisors, regular parameters

This file collects foundational results used throughout the minimal model program.

* On an integral, locally Noetherian, normal, quasi-compact scheme `Y` every invertible
  `𝒪_Y`-module is `𝒪_Y(D)` for a Cartier divisor `D`.
* Let `g : Y ⟶ Z` be a proper morphism of varieties over a field `k`, with `Y` normal, and let
  `L` be a `g`-free Cartier divisor: the counit `g^* g_* 𝒪_Y(L) ⟶ 𝒪_Y(L)` is surjective. With
  `G = g_* 𝒪_Y(L)` and `P = Proj_Z(Sym G)`, the morphism `Φ : Y ⟶ P` defined by `L` is the
  `Z`-morphism with an isomorphism `Φ^* 𝒪_P(1) ≅ 𝒪_Y(L)` carrying the pulled-back tautological
  map `Φ^* π^* G ⟶ Φ^* 𝒪_P(1)` to the counit. If `Y ⟶ Y_L ⟶ P` is its Stein factorization
  `Φ = τ ∘ ρ`, then `Y_L` is a normal variety, `ρ_* 𝒪_Y = 𝒪_{Y_L}`, `τ` is finite, and
  `L ∼ ρ^* A` for a Cartier divisor `A` on `Y_L` with `𝒪_{Y_L}(A) ≅ τ^* 𝒪_P(1)` which is ample
  over `Z`.
* Let `(R, 𝔪)` be a regular local ring of dimension `d` and `x₁, …, x_i ∈ 𝔪`. Then
  `R / (x₁, …, x_i)` is a regular local ring of dimension `d - i` if and only if `x₁, …, x_i`
  extends to a regular system of parameters `x₁, …, x_i, t₁, …, t_m`.

## Main results

* `MMP.Mori.exists_isCartier_divisorialSheaf_iso_of_isInvertible`: on an integral, locally
  Noetherian, normal, quasi-compact scheme every invertible module is `𝒪(D)` for a Cartier
  divisor `D`.
* `MMP.Mori.IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier`: the Stein factor of
  the morphism defined by a relatively free Cartier divisor, and the relatively ample divisor on
  it.
* `MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff` (registered here):
  regular quotients of complementary dimension are quotients by partial regular systems of
  parameters.

## Implementation notes

* `P` is `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of the symmetric algebra of `G`,
  with twist `Stacks.ProjectiveBundleSplitting.tautologicalTwist` and tautological map
  `Stacks.ProjectiveBundleSplitting.tautologicalMap : π^* G ⟶ 𝒪_P(1)`. The morphism defined by
  `L` is characterized by its universal property (quotient-line convention); the statement
  asserts that such a morphism exists, and makes its claims for every morphism with that
  property. Linear equivalence `L ∼ ρ^* A` is recorded as an isomorphism
  `𝒪_Y(L) ≅ ρ^* 𝒪_{Y_L}(A)` of invertible sheaves, and `ρ_* 𝒪_Y = 𝒪_{Y_L}` as
  `∀ U, IsIso (ρ.app U)`. The Stein factorization is any
  `Stacks.SteinFactorization.IsSteinFactorization` of `Φ`; properness of `Φ`, needed to speak of
  it, is part of the conclusion.
* Ampleness of `𝒪_P(1)` over an affine `U ⊆ Z` is read off the chart `Proj Γ(U, Sym G)` of `P`
  over `U`, on which the twist is the absolute `𝒪(1)`: that ring is generated in degree one, and
  the chart is quasi-compact because `P ⟶ Z` is proper. The source instead embeds `P_U` in a
  projective space over `U`.
* A regular system of parameters is `MMP.Mori.IsRegularSystemOfParameters`; being *part of* one
  is extension by a family `t : Fin m → R` via `Fin.append`. "Of dimension `d - i`" is written
  `dim R / (x) + i = d` in `WithBot ℕ∞`. The equivalence holds without `xⱼ ∈ 𝔪`: this is
  `MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.22.3
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*]
* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-! ### The Stein factor of a relatively free Cartier divisor -/

namespace MMP.Mori

/-- **Invertible modules are divisorial sheaves of Cartier divisors.** On an integral, locally
Noetherian, normal, quasi-compact scheme every invertible module is `𝒪(D)` for a Cartier divisor
`D`. This refines `MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible` by the Cartier
conclusion. -/
theorem exists_isCartier_divisorialSheaf_iso_of_isInvertible {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := ha, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

section SteinFactor

open Stacks.AlgebraicGeometry.RelativeProj Stacks.SymGraded Stacks.ProjectiveBundleSplitting

section Universal

open MMP.Intersection.Scheme.Modules

/-- The coherence of the inverse-image pseudofunctor used to move the tautological quotient
across a comparison `b : P' ⟶ P` over the base. -/
private theorem pullbackComp_coherence {Y P P' X : Scheme.{u}} (h : Y ⟶ P') (b : P' ⟶ P)
    (π : P ⟶ X) (π' : P' ⟶ X) (γ : b ≫ π = π') (p : Y ⟶ X) (hh : h ≫ π' = p)
    (hf : (h ≫ b) ≫ π = p) (M : X.Modules) :
    (Scheme.Modules.pullbackCongr hh).inv.app M ≫
      (Scheme.Modules.pullbackComp h π').inv.app M ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackCongr γ).inv.app M) ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp b π).inv.app M) ≫
      (Scheme.Modules.pullbackComp h b).hom.app ((Scheme.Modules.pullback π).obj M) =
      (Scheme.Modules.pullbackCongr hf).inv.app M ≫
        (Scheme.Modules.pullbackComp (h ≫ b) π).inv.app M := by
  subst γ hh
  have key := Stacks.Modules.pullbackComp_congr_assoc h b π _ rfl _ rfl _ hf M
  have : Mono ((Scheme.Modules.pullbackComp (h ≫ b) π).hom.app M ≫
      (Scheme.Modules.pullbackCongr hf).hom.app M) :=
    inferInstanceAs (Mono ((Scheme.Modules.pullbackComp (h ≫ b) π).app M ≪≫
      (Scheme.Modules.pullbackCongr hf).app M).hom)
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (h ≫ b) π).hom.app M ≫
    (Scheme.Modules.pullbackCongr hf).hom.app M)]
  simp only [Functor.map_comp, Category.assoc] at key
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, NatTrans.id_app, CategoryTheory.Functor.map_id] at key ⊢
  rw [← key]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp

/-- The tautological quotient of `Stacks.RelativeProj.projectiveBundle X ℰ`, pulled back along
`h`, agrees with the tautological map of `projectiveBundle ℰ` pulled back along
`h ≫ (bundlePresentationIso ℰ).inv`, up to the composition isomorphism of inverse images. -/
private theorem overQuotientMap_comp_pullbackComp {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {Y : Scheme.{u}} {p : Y ⟶ X}
    (h : Y ⟶ Stacks.RelativeProj.projectiveBundle X E)
    (hh : h ≫ Stacks.RelativeProj.projectiveBundleToBase X E = p)
    (hf : (h ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv) ≫
      projectiveBundleToBase E = p) :
    (Stacks.RelativeProj.tautologicalDatum E).overQuotientMap h hh ≫
        (Scheme.Modules.pullbackComp h (Stacks.RelativeProj.bundlePresentationIso E).inv).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) =
      (Scheme.Modules.pullbackCongr hf).inv.app E ≫
        (Scheme.Modules.pullbackComp (h ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)
          (projectiveBundleToBase E)).inv.app E ≫
        (Scheme.Modules.pullback (h ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)).map
          (Stacks.ProjectiveBundleSplitting.tautologicalMap E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) := by
  have nat := (Scheme.Modules.pullbackComp h
    (Stacks.RelativeProj.bundlePresentationIso E).inv).hom.naturality
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E))
  simp only [Functor.comp_map] at nat
  have coh := pullbackComp_coherence h (Stacks.RelativeProj.bundlePresentationIso E).inv
    (projectiveBundleToBase E) _ (Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase E)
    p hh hf E
  unfold Stacks.RelativeProj.TautologicalDatum.overQuotientMap
  dsimp only [Stacks.RelativeProj.tautologicalDatum]
  unfold Stacks.RelativeProj.tautologicalDatumUniv
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [nat]
  simp only [← Category.assoc] at coh ⊢
  rw [coh]

/-- An invertible quotient `Q` of `p^*ℰ` is classified, in the sense of the canonical tautological
datum on `Stacks.RelativeProj.projectiveBundle X ℰ`, by `g` only when the tautological quotient
of `projectiveBundle ℰ`, pulled back along `g ≫ (bundlePresentationIso ℰ).inv`, is isomorphic to
`Q` under `p^*ℰ`. -/
private theorem exists_iso_comp_eq_of_isEquivalent {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {Y : Scheme.{u}} {p : Y ⟶ X}
    (Q : Stacks.Divisors.InvertibleQuotient Y ((Scheme.Modules.pullback p).obj E))
    (g : Y ⟶ Stacks.RelativeProj.projectiveBundle X E)
    (hg : g ≫ Stacks.RelativeProj.projectiveBundleToBase X E = p)
    (hf : (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv) ≫
      projectiveBundleToBase E = p)
    (hQ : ((Stacks.RelativeProj.tautologicalDatum E).overQuotient _ (Iso.refl _) g hg).IsEquivalent
      Q) :
    ∃ φ : (Scheme.Modules.pullback (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) ≅ Q.L,
        (Scheme.Modules.pullbackCongr hf).inv.app E ≫
          (Scheme.Modules.pullbackComp (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)
            (projectiveBundleToBase E)).inv.app E ≫
          (Scheme.Modules.pullback (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)).map
            (Stacks.ProjectiveBundleSplitting.tautologicalMap E
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) ≫ φ.hom = Q.q := by
  have K := overQuotientMap_comp_pullbackComp E g hg hf
  obtain ⟨α, hα⟩ := hQ
  refine ⟨((Scheme.Modules.pullbackComp g
    (Stacks.RelativeProj.bundlePresentationIso E).inv).app _).symm ≪≫ α, ?_⟩
  simp only [Stacks.RelativeProj.TautologicalDatum.overQuotient_q, Iso.refl_hom,
    Category.id_comp] at hα
  exact (K =≫ ((Scheme.Modules.pullbackComp g
    (Stacks.RelativeProj.bundlePresentationIso E).inv).inv.app _ ≫ α.hom)).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg _ (Iso.hom_inv_id_app_assoc _ _ _)).trans hα))

/-- The morphism defined by an invertible quotient `q : p^* ℰ ⟶ ℒ` of the pull-back of a
quasi-coherent `ℰ`: a morphism `Φ` to `ℙ(ℰ)` over the base and an isomorphism `Φ^* 𝒪(1) ≅ ℒ`
carrying the pulled-back tautological map to `q`. -/
private theorem exists_hom_projectiveBundle {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    {Y : Scheme.{u}} (p : Y ⟶ X) (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    (q : (Scheme.Modules.pullback p).obj E ⟶ L) [Epi q] :
    ∃ (Φ : Y ⟶ projectiveBundle E) (h : Φ ≫ projectiveBundleToBase E = p)
      (φ : (Scheme.Modules.pullback Φ).obj (tautologicalTwist E
        (isQuasicoherentPieces_of_isQuasicoherent E)) ≅ L),
      (Scheme.Modules.pullback Φ).map
          (tautologicalMap E (isQuasicoherentPieces_of_isQuasicoherent E)) ≫ φ.hom =
        (Scheme.Modules.pullbackComp Φ (projectiveBundleToBase E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr h).hom.app E ≫ q := by
  let Q : Stacks.Divisors.InvertibleQuotient Y ((Scheme.Modules.pullback p).obj E) :=
    ⟨L, (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL, q, inferInstance⟩
  let D := Stacks.RelativeProj.tautologicalDatum E
  let c := D.classifyingMorphismOver _ (Iso.refl _) Q
  have hc : (c.1 ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv) ≫
      projectiveBundleToBase E = p := by
    rw [Category.assoc, Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase, c.2]
  obtain ⟨φ, hφ⟩ := exists_iso_comp_eq_of_isEquivalent E Q c.1 c.2 hc
    (D.overQuotient_classifyingMorphismOver_isEquivalent _ (Iso.refl _) Q)
  refine ⟨_, hc, φ, ?_⟩
  change _ = q at hφ
  rw [← hφ, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

end Universal

/-- The projection of `ℙ(G) = Proj_Z(Sym G)` is proper when `G` is quasi-coherent of finite
type: the two presentations of the projective bundle agree over the base. -/
private theorem isProper_relativeProj_toBase {Z : Scheme.{u}} (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] :
    IsProper (relativeProj (schemeSheafGradedAlgebra G
      (isQuasicoherentPieces_of_isQuasicoherent G))).toBase := by
  have h := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType Z G
  rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase G] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp h

/-- **`𝒪_P(1)` is ample over every affine open of the base.** Over an affine `U ⊆ Z` the part of
`P = Proj_Z(Sym G)` over `U` is the chart `Proj Γ(U, Sym G)`, on which the twist is the absolute
`𝒪(1)`; that ring is generated in degree one, and the chart is quasi-compact because `P ⟶ Z` is,
so `𝒪(1)` is ample there. -/
private theorem isAmple_tautologicalTwist_preimage {Z : Scheme.{u}} (G : Z.Modules)
    [G.IsQuasicoherent] (hG : IsQuasicoherentPieces G)
    [QuasiCompact (relativeProj (schemeSheafGradedAlgebra G hG)).toBase]
    (U : Z.Opens) (hU : IsAffineOpen U) :
    Stacks.Ample.IsAmple ((relativeProj (schemeSheafGradedAlgebra G hG)).toBase ⁻¹ᵁ U).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule
        ((relativeProj (schemeSheafGradedAlgebra G hG)).toBase ⁻¹ᵁ U).ι
        (tautologicalTwist G hG)) := by
  set P := relativeProj (schemeSheafGradedAlgebra G hG)
  set D := (projectiveBundleTwistData G hG).chartData
  haveI := D.chart_isOpenImmersion U hU
  set c := P.chart U hU
  have hrange : Set.range c.base = Set.range (P.toBase ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι, ← D.chart_range U hU]
    simp only [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange]
    rfl
  set φ := IsOpenImmersion.isoOfRangeEq c (P.toBase ⁻¹ᵁ U).ι hrange
  have hfac' : φ.inv ≫ c = (P.toBase ⁻¹ᵁ U).ι := (Iso.inv_comp_eq φ).mpr
    (IsOpenImmersion.isoOfRangeEq_hom_fac c (P.toBase ⁻¹ᵁ U).ι hrange).symm
  haveI : CompactSpace (P.toBase ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := P.toBase) _ U.isOpen hU.isCompact)
  haveI : CompactSpace (AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra G hG).grading U)) :=
    QuasiCompact.compactSpace_of_compactSpace φ.hom
  have hcov : ∀ x : ProjectiveSpectrum.top ((schemeSheafGradedAlgebra G hG).grading U),
      ∃ g ∈ (schemeSheafGradedAlgebra G hG).grading U 1,
        x ∈ ProjectiveSpectrum.basicOpen ((schemeSheafGradedAlgebra G hG).grading U) g := by
    intro x
    obtain ⟨a, ha⟩ := Stacks.SymGraded.exists_degreeOne_notMem G hG hU x
    exact ⟨a, a.2, ha⟩
  haveI : Stacks.Ample.IsInvertibleModule
      (AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra G hG).grading U))
      (Stacks.ProjTwistSection.twistingModule ((schemeSheafGradedAlgebra G hG).grading U) 1) :=
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf _
      (Stacks.ProjDegreeOneCover.degreeOneCover_of_forall_exists _ hcov) 1
  have hA0 : Stacks.Ample.IsAmple
      (AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra G hG).grading U))
      (Stacks.ProjTwistSection.twistingModule ((schemeSheafGradedAlgebra G hG).grading U) 1) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (Stacks.ProjDegreeOneCover.isAmple_twistingModule_one _ inferInstance hcov)
  have e₁ : (Scheme.Modules.pullback c).obj (tautologicalTwist G hG) ≅
      Stacks.ProjTwistSection.twistingModule ((schemeSheafGradedAlgebra G hG).grading U) 1 :=
    ((Scheme.Modules.restrictFunctorIsoPullback c).app _).symm ≪≫ D.chartIso U hU 1
  have e : Stacks.AmpleLocallyClosed.pullbackModule φ.inv
        (Stacks.ProjTwistSection.twistingModule ((schemeSheafGradedAlgebra G hG).grading U) 1) ≅
      Stacks.AmpleLocallyClosed.pullbackModule (P.toBase ⁻¹ᵁ U).ι (tautologicalTwist G hG) :=
    (Scheme.Modules.pullback φ.inv).mapIso e₁.symm ≪≫
      (Scheme.Modules.pullbackComp φ.inv c).app _ ≪≫ (Scheme.Modules.pullbackCongr hfac').app _
  haveI : Stacks.Ample.IsInvertibleModule P.scheme (tautologicalTwist G hG) :=
    isInvertible_tautologicalTwist G hG
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp
    (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom φ.inv _ hA0)

/-- If `T` on `P` is ample over every affine open of `Z` (via `π`) and `τ` is affine, then a
Cartier divisor `A` with `𝒪(A) ≅ τ^* T` is ample relative to `τ ≫ π`. -/
private theorem isRelativelyAmpleCartier_of_iso_pullback {YL P Z : Scheme.{u}}
    [IsLocallyNoetherian YL] [IsNormal YL] [CompactSpace YL]
    (τ : YL ⟶ P) [IsAffineHom τ] (π : P ⟶ Z) (T : P.Modules) [Stacks.Ample.IsInvertibleModule P T]
    (hT : ∀ U : Z.Opens, IsAffineOpen U →
      Stacks.Ample.IsAmple (π ⁻¹ᵁ U).toScheme
        (Stacks.AmpleLocallyClosed.pullbackModule (π ⁻¹ᵁ U).ι T))
    (A : MMP.Mori.Divisor YL) (hA : A.IsCartier)
    (eA : A.divisorialSheaf ≅ (Scheme.Modules.pullback τ).obj T) :
    MMP.Flips.IsRelativelyAmpleCartier (τ ≫ π) A := by
  refine ⟨hA, fun U hU => ?_⟩
  haveI := hA.isInvertibleModule_divisorialSheaf
  have h1 := Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (τ ∣_ (π ⁻¹ᵁ U))
    (Stacks.AmpleLocallyClosed.pullbackModule (π ⁻¹ᵁ U).ι T) (hT U hU)
  have e : Stacks.AmpleLocallyClosed.pullbackModule (τ ∣_ (π ⁻¹ᵁ U))
      (Stacks.AmpleLocallyClosed.pullbackModule (π ⁻¹ᵁ U).ι T) ≅
      Stacks.AmpleLocallyClosed.pullbackModule (τ ⁻¹ᵁ (π ⁻¹ᵁ U)).ι A.divisorialSheaf :=
    (Scheme.Modules.pullbackComp (τ ∣_ (π ⁻¹ᵁ U)) (π ⁻¹ᵁ U).ι).app T ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι τ (π ⁻¹ᵁ U))).app T ≪≫
      ((Scheme.Modules.pullbackComp (τ ⁻¹ᵁ (π ⁻¹ᵁ U)).ι τ).app T).symm ≪≫
      (Scheme.Modules.pullback (τ ⁻¹ᵁ (π ⁻¹ᵁ U)).ι).mapIso eA.symm
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp h1

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **The Stein factor of a proper morphism from a normal variety is a normal variety.** If
`Φ : Y ⟶ P` is proper, `Y` is a normal variety over `k` and `P` is locally of finite type over
`k`, then the middle scheme of any Stein factorization `Φ = τ ∘ ρ` is a normal variety over `k`. -/
theorem isNormalVariety_of_isSteinFactorization {k : Type u} [Field k] {Y P YL : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsNormalVariety k sY) (t : P ⟶ Spec (.of k))
    [LocallyOfFiniteType t] {Φ : Y ⟶ P} [IsProper Φ] (hf : Φ ≫ t = sY) {ρ : Y ⟶ YL}
    {τ : YL ⟶ P} (hS : Stacks.SteinFactorization.IsSteinFactorization Φ ρ τ) :
    MMP.Mori.IsNormalVariety k (τ ≫ t) := by
  have := hY.1
  obtain ⟨Y', f', g', ⟨hS'⟩, -, -, -, -, -, hvar, -, hnorm, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sY t Φ hf
  let E := hS.normalization ≪≫ hS'.normalization.symm
  let φ : YL ⟶ Y' := E.hom.left
  have hE : φ ≫ g' = τ := Over.w E.hom
  haveI : IsIso φ := inferInstanceAs (IsIso ((Over.forget _).map E.hom))
  haveI : IsNormal Y' := hnorm hY.2
  haveI : IsIntegral Y' := hvar.toIsIntegral
  haveI : Nonempty YL := ⟨(inv φ) (Classical.arbitrary Y')⟩
  refine ⟨(MMP.Mori.isVariety_iff k _).mpr ⟨isIntegral_of_isOpenImmersion φ, ?_, ?_, ?_⟩,
    AlgebraicGeometry.isNormal_of_isOpenImmersion φ⟩ <;> rw [← hE, Category.assoc] <;>
    infer_instance

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **The Stein factor of a relatively free Cartier divisor.** Let `g : Y ⟶ Z` be a proper
morphism of varieties over `k` with `Y` normal, and `L` a `g`-free Cartier divisor. Write
`G = g_* 𝒪_Y(L)` and `P = Proj_Z(Sym G)`. Then the morphism `Φ : Y ⟶ P` over `Z` defined by `L`
exists (an isomorphism `e : Φ^* 𝒪_P(1) ≅ 𝒪_Y(L)` carries the pulled-back tautological map to the
counit of `g^* ⊣ g_*`), and for every such `Φ` and every Stein factorization `Φ = τ ∘ ρ`,
`ρ : Y ⟶ Y_L`, `τ : Y_L ⟶ P`: `Y_L` is a normal variety, `ρ_* 𝒪_Y = 𝒪_{Y_L}`, `τ` is finite, and
there is a Cartier divisor `A` on `Y_L`, ample over `Z`, with `𝒪_{Y_L}(A) ≅ τ^* 𝒪_P(1)` and
`𝒪_Y(L) ≅ ρ^* 𝒪_{Y_L}(A)`, i.e. `L ∼ ρ^* A`. -/
@[mmp "lem_mmp_foundation_free_divisor_stein_ample_model"]
public theorem IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (hY : IsNormalVariety k sY) (hZ : IsVariety k sZ) (g : Y ⟶ Z) [IsProper g]
    (hg : g ≫ sZ = sY) (L : Y.CartierDivisor) (hL : IsRelativelyFreeCartier g L) :
    letI : ((Scheme.Modules.pushforward g).obj
        (MMP.CartierDivisor.sheaf L)).IsQuasicoherent :=
      ProperCoherentFiniteType.isQuasicoherent_pushforward g _ inferInstance
    let G := (Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf L)
    let hG := isQuasicoherentPieces_of_isQuasicoherent G
    let P := relativeProj (schemeSheafGradedAlgebra G hG)
    let IsDefinedBy : ∀ Φ : Y ⟶ P.scheme, Φ ≫ P.toBase = g →
        ((Scheme.Modules.pullback Φ).obj (tautologicalTwist G hG) ≅
          MMP.CartierDivisor.sheaf L) → Prop := fun Φ hΦ e ↦
      (Scheme.Modules.pullback Φ).map (tautologicalMap G hG) ≫ e.hom =
        (Scheme.Modules.pullbackComp Φ P.toBase).hom.app G ≫
          (Scheme.Modules.pullbackCongr hΦ).hom.app G ≫
            (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
              (MMP.CartierDivisor.sheaf L)
    (∃ (Φ : Y ⟶ P.scheme) (hΦ : Φ ≫ P.toBase = g) (e : _), IsDefinedBy Φ hΦ e) ∧
    ∀ (Φ : Y ⟶ P.scheme) (hΦ : Φ ≫ P.toBase = g) (e : _), IsDefinedBy Φ hΦ e →
      ∃ _ : IsProper Φ, ∀ (YL : Scheme.{u}) (ρ : Y ⟶ YL) (τ : YL ⟶ P.scheme),
        Stacks.SteinFactorization.IsSteinFactorization Φ ρ τ →
          MMP.Mori.IsNormalVariety k (τ ≫ P.toBase ≫ sZ) ∧ (∀ U : YL.Opens, IsIso (ρ.app U)) ∧
            IsFinite τ ∧
            ∃ (_ : IsLocallyNoetherian YL) (_ : IsNormal YL) (_ : CompactSpace YL)
              (A : MMP.Mori.Divisor YL),
              MMP.Flips.IsRelativelyAmpleCartier (τ ≫ P.toBase) A ∧
              Nonempty (A.divisorialSheaf ≅
                (Scheme.Modules.pullback τ).obj (tautologicalTwist G hG)) ∧
              Nonempty (MMP.CartierDivisor.sheaf L ≅
                (Scheme.Modules.pullback ρ).obj A.divisorialSheaf) := by
  intro G hG P IsDefinedBy
  refine ⟨?exists_hom, ?stein⟩
  case exists_hom =>
    exact @exists_hom_projectiveBundle _ G
      (ProperCoherentFiniteType.isQuasicoherent_pushforward g _ inferInstance) _ g _
      (MMP.CartierDivisor.isInvertible_sheaf L) _ hL
  case stein =>
    intro Φ hΦ e _
    have : IsSeparated P.toBase :=
      Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase _ P
    have : IsProper (Φ ≫ P.toBase) := hΦ ▸ inferInstance
    have : IsProper Φ := IsProper.of_comp Φ P.toBase
    refine ⟨this, fun YL ρ τ hS => ?_⟩
    have := hS.structureSheaf
    have hYv := hY.1
    have : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : G.IsFiniteType :=
      (AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward g
        (MMP.CartierDivisor.sheaf L)).isFiniteType
    haveI : IsProper P.toBase := isProper_relativeProj_toBase G
    have hf : Φ ≫ P.toBase ≫ sZ = sY := by rw [reassoc_of% hΦ, hg]
    have hnv := isNormalVariety_of_isSteinFactorization hY (P.toBase ≫ sZ) hf hS
    have hYLv := hnv.1
    haveI : IsIntegral YL := hYLv.toIsIntegral
    haveI : IsNormal YL := hnv.2
    haveI : IsLocallyNoetherian YL := LocallyOfFiniteType.isLocallyNoetherian (τ ≫ P.toBase ≫ sZ)
    haveI : CompactSpace YL :=
      (quasiCompact_iff_compactSpace (τ ≫ P.toBase ≫ sZ)).mp inferInstance
    haveI : IsFinite τ := hS.isFinite
    haveI : Stacks.Ample.IsInvertibleModule P.scheme (tautologicalTwist G hG) :=
      isInvertible_tautologicalTwist G hG
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible YL.sheaf.obj
        YL.ringCatSheaf.property ((Scheme.Modules.pullback τ).obj (tautologicalTwist G hG)) :=
      Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback τ.toLRSHom.toShHom _
    obtain ⟨A, hAc, ⟨eA⟩⟩ := exists_isCartier_divisorialSheaf_iso_of_isInvertible
      ((Scheme.Modules.pullback τ).obj (tautologicalTwist G hG))
    refine ⟨hnv, fun U => NatIso.isIso_app_of_isIso ρ.c (Opposite.op U), hS.isFinite,
      inferInstance, inferInstance, inferInstance, A,
      isRelativelyAmpleCartier_of_iso_pullback τ P.toBase _
        (fun U hU => isAmple_tautologicalTwist_preimage G hG U hU) A hAc eA, ⟨eA⟩, ⟨?_⟩⟩
    exact e.symm ≪≫ (Scheme.Modules.pullbackCongr hS.comp.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp ρ τ).app _).symm ≪≫ (Scheme.Modules.pullback ρ).mapIso eA.symm

end SteinFactor

end MMP.Mori

/-! ### Regular quotients and partial regular systems of parameters -/

namespace MMP

open IsLocalRing MMP.Mori

/- `lem_mmp_foundation_km_regular_parameter_quotients` is stated by the declaration
`MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff`, which needs neither
`dim R = d` as a hypothesis nor `xⱼ ∈ 𝔪`; it is registered on it. -/
attribute [mmp "lem_mmp_foundation_km_regular_parameter_quotients"]
  MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff

end MMP

end
