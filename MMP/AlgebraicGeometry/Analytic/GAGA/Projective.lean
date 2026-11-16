module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.Topology.Sheaves.Godement
public import MMP.Analysis.Complex.Submanifold
public import MMP.AlgebraicGeometry.DeRham.FormsSectionsAlgebra
public import MMP.AlgebraicGeometry.DeRham.LogCartierCoordinates
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Divisor.LineBundle
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.MMP.Models
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.OpenRestriction
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Analytic.GAGA.Differentials
import MMP.AlgebraicGeometry.Analytic.GAGA.Hypercohomology
import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveCohomology
import MMP.AlgebraicGeometry.Analytic.GAGA.Stalks
import MMP.Analysis.Complex.Coherent.CoherenceCalculus
import MMP.Analysis.Complex.Coherent.MatrixMapsSubmanifolds
import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveSpaceTwists
import MMP.Analysis.Complex.Coherent.OkaCartanBlocks
import MMP.AlgebraicGeometry.Analytic.GAGA.AnalyticSerreTheorem
import MMP.Analysis.Complex.Coherent.OkaInduction
import MMP.AlgebraicGeometry.Analytic.GAGA.TwistsCechComparison
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedProjectiveSpace
import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.PlaneConic
import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyQuasiAffineHom
import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
import StacksFrontier.AlgebraicGeometry.Modules.PushforwardUnitHomEquiv
import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible

/-!
# GAGA for projective complex schemes

Let `X` be a projective scheme over `ℂ`, possibly nonreduced, `X^an` its analytification,
`α_X : X^an → X` the comparison morphism and `F ↦ F^an` the analytification of `𝒪_X`-modules.

1. For every coherent `F` and every `q` the comparison map
   `c^q_F : H^q(X, F) → H^q(X^an, F^an)` is an isomorphism. The maps `c^q` are natural for
   every pair `(φ, ψ)` of a `ℂ`-linear map of sheaves `φ : F → G` and a map
   `ψ : F^an → G^an` with `ψ(s ⊗ 1) = φ(s) ⊗ 1`, and commute with the connecting maps of short
   exact sequences.
2. For a bounded complex `K^•` of coherent sheaves with `ℂ`-linear differentials and
   differentials on `K^{•,an}` compatible with them, the map
   `ℍ^n(X, K^•) → ℍ^n(X^an, K^{•,an})` induced by `α_X⁻¹ K^• → K^{•,an}` is an isomorphism,
   and on the graded pieces of the stupid filtration it is `c^q`.
3. Analytification carries invertible `𝒪_X`-modules to invertible `𝒪_{X^an}`-modules and
   induces an isomorphism of Picard groups `Pic X ≃* Pic X^an`, `[L] ↦ [L^an]`, compatible with
   restriction to closed subschemes: for a closed immersion `i : Z → X` over `ℂ`,
   `(i^* L)^an ≅ (i^an)^* L^an`. In particular `H^0(X^an, 𝒪) = H^0(X, 𝒪_X)`.
4. If `X` is smooth and `E` a reduced simple normal crossing divisor, the connected components
   of `X` are open, and on each of them, a smooth projective variety of some dimension `n` with
   the restriction of `E`, the analytification is a complex manifold in algebraic coordinates,
   `(Ω^p_X)^an` is the sheaf of holomorphic `p`-forms through `s ⊗ 1 ↦ s^an`, compatibly with the
   exterior derivatives, and the logarithmic forms `Ω^p_X(log E)` analytify to the holomorphic
   logarithmic forms, freely generated by the same products of `dzᵢ/zᵢ` and `dz_j`.

Parts (1), (2) and (4) are landed comparison theorems. The proof of (3) occupies most of this
file. Analytification commutes with tensor products and sends `𝒪_X` to `𝒪_{X^an}`, so
`L ↦ L^an` induces a homomorphism of Picard groups. It is injective: if `F` is coherent and
`F^an ≅ 𝒪_{X^an}`, a generating section of `F^an` is algebraic by the comparison theorem in
degree zero, and the morphism `𝒪_X ⟶ F` it defines analytifies to an isomorphism, hence is one,
since analytification is exact and detects vanishing of modules of finite type.

It is surjective. Let `i : X ⟶ ℙᴺ` be a closed immersion and `M` an invertible `𝒪_{X^an}`-module.
The stalks of `𝒪_{X^an}` are local, so `M` is locally trivial and its direct image `i^an_* M` is
locally isomorphic to `i^an_* 𝒪_{X^an} ≅ (i_* 𝒪_X)^an`, hence coherent. Serre's theorem on
`(ℙᴺ)^an`, applied to `i^an_* M` and to a kernel, presents a twist of `i^an_* M` by global
sections of the analytification of a coherent sheaf; these are algebraic, so
`i^an_* M ≅ G^an` for a coherent `G` on `ℙᴺ`. The ring map `𝒪_{(ℙᴺ)^an} ⟶ i^an_* 𝒪_{X^an}` is
locally surjective, being the analytification of `𝒪_{ℙᴺ} ⟶ i_* 𝒪_X`, so `i^an_*` is fully
faithful and `L = i^* G` has `L^an ≅ i^{an,*} G^an ≅ i^{an,*} i^an_* M ≅ M`. Applying this to
`M` and to `M⁻¹` gives coherent `L`, `L'` with `(L ⊗ L')^an ≅ 𝒪_{X^an}`, so `L ⊗ L' ≅ 𝒪_X` by
injectivity and `L` is invertible.

## Main results

* `MMP.Analytic.exists_mulEquiv_picardGroup_analytification_of_isProjective`: GAGA for Picard
  groups, `Pic X ≃* Pic X^an`, compatible with restriction to closed subschemes.
* The four statements together, `MMP.Analytic.analytification_gaga_projective`, are in
  `MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveGAGA`, built from the named parts in
  `GAGA/ProjectiveParts/` and `GAGA/Differentials.lean`.

## Implementation notes

* Cohomology is Godement cohomology with values in abelian groups
  (`MMP.Analytic.sheafCohomology`), and `c^q_F` is `MMP.Analytic.comparisonMap`. The degree
  `q` ranges over `ℤ`; both sides vanish in negative degrees.
* Connecting maps are `CategoryTheory.ShortComplex.ShortExact.δ` of the total complexes of
  Godement sections, whose homology is `MMP.Analytic.sheafCohomology`.
* A complex `K^•` is indexed by `ℤ` and bounded by arbitrary `a ≤ b` rather than by `0, m`.
  The identification of the graded pieces uses isomorphisms
  `ℍ^n(T, G[-p]) ≅ H^{n-p}(T, G)` natural in `G`.
* The Picard groups are `Stacks.SheafPicardGroup.schemePicardGroup X` and
  `Stacks.SheafPicardGroup.PicardGroup` of the structure sheaf of `X^an`; the isomorphism is
  pinned by `e (schemeClassOf X L) = classOf (L^an)`. The ring map
  `θ : 𝒪_{X^an} → i^an_* 𝒪_{Z^an}` of `i^an` is characterised by `θ ∘ α_X^# = α_Z^# ∘ i^#` on
  algebraic sections; the compatibility with restriction is asserted for every such `θ`.
* A line bundle is a module locally isomorphic to the structure sheaf, on `X` and on `X^an`
  alike (`MMP.Analytic.IsLocallyTrivial`).
* The algebraic line bundle with analytification `M` is obtained as the pullback `i^* G` of the
  algebraization `G` of `i^an_* M`, the identification `i^{an,*} i^an_* M ≅ M` coming from the
  full faithfulness of `i^an_*`; this replaces the verification that `G` is killed by the ideal
  of `X`. Its invertibility is deduced from that of `M` through injectivity applied to
  `L ⊗ L'`, which replaces the stalkwise Nakayama argument.
* Part 4 is stated on the connected components of `X`: an open immersion `j : Y ⟶ X` onto a
  connected component, with structure morphism `j ≫ sX`, the restriction `E|_Y` of `E` and
  `n = dim Y`. A connected component of a smooth projective scheme is a smooth projective
  variety, of pure dimension `n`, where algebraic coordinates `z₁, …, zₙ` exist, and it is open,
  so every point of `X` lies on one. Holomorphic forms are read on the charts of the manifold
  structure, as continuous alternating maps.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §§2–3, Théorèmes 1–3,
  Proposition 18.
* [Deligne, *Équations différentielles à points singuliers réguliers*], II.3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic.Analytification
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

namespace MMP.Analytic

/-! ### Restriction along a morphism over `ℂ` -/

/-- Pullbacks of sheaves of modules along equal morphisms of sheaves of rings agree. -/
private theorem pullback_obj_congr {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{0} J K).obj R}
    (e : φ = ψ) [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]
    [(SheafOfModules.pushforward.{0} ψ).IsRightAdjoint] (M : SheafOfModules.{0} S) :
    (SheafOfModules.pullback.{0} φ).obj M = (SheafOfModules.pullback.{0} ψ).obj M := by
  subst e
  rfl

/-- **Analytification commutes with pullback.** For a morphism `i : Z ⟶ X` over `ℂ` and a
morphism of sheaves of rings `θ : 𝒪_{X^an} ⟶ i^an_* 𝒪_{Z^an}` extending `i^#`, the
analytification of `i^* L` is the pullback along `θ` of `L^an`. -/
private theorem nonempty_analytifyModule_pullback_iso {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (i : Z ⟶ X) (hi : i ≫ sX = sZ) :
    haveI : (Opens.map (ComplexPoints.analyticMap i hi)).IsContinuous
        (Opens.grothendieckTopology (space sX)) (Opens.grothendieckTopology (space sZ)) :=
      Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
        (coverPreserving_opens_map _)
    ∀ θ : ringCatSheaf sX ⟶
        ((Opens.map (ComplexPoints.analyticMap i hi)).sheafPushforwardContinuous
          RingCat.{0} (Opens.grothendieckTopology (space sX))
          (Opens.grothendieckTopology (space sZ))).obj (ringCatSheaf sZ),
      (∀ (V : X.Opens) (f : Γ(X, V)),
        θ.hom.app (op ((Opens.map (toSchemeHom sX)).obj V))
            ((ringCatSheafHom sX).hom.app (op V) f) =
          (ringCatSheafHom sZ).hom.app (op (i ⁻¹ᵁ V)) (i.app V f)) →
      haveI : (PresheafOfModules.pushforward.{0} θ.hom).IsRightAdjoint :=
        PresheafOfModules.instIsRightAdjointPushforward _
      haveI : (SheafOfModules.pushforward.{0} θ).IsRightAdjoint :=
        (SheafOfModules.PullbackConstruction.adjunction.{0} θ).isRightAdjoint
      ∀ L : X.Modules,
        Nonempty ((analytifyModule sZ).obj ((Scheme.Modules.pullback i).obj L) ≅
          (SheafOfModules.pullback.{0} θ).obj ((analytifyModule sX).obj L)) := by
  haveI : (Opens.map (ComplexPoints.analyticMap i hi)).IsContinuous
      (Opens.grothendieckTopology (space sX)) (Opens.grothendieckTopology (space sZ)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
      (coverPreserving_opens_map _)
  intro θ hθ
  haveI : (PresheafOfModules.pushforward.{0} θ.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  haveI : (SheafOfModules.pushforward.{0} θ).IsRightAdjoint :=
    (SheafOfModules.PullbackConstruction.adjunction.{0} θ).isRightAdjoint
  intro L
  haveI : (Opens.map i.base ⋙ Opens.map (toSchemeHom sZ)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (space sZ)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology Z) _
  haveI : (Opens.map (toSchemeHom sX) ⋙ Opens.map (ComplexPoints.analyticMap i hi)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (space sZ)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (space sX)) _
  let φ₁ : X.ringCatSheaf ⟶ ((Opens.map i.base ⋙
      Opens.map (toSchemeHom sZ)).sheafPushforwardContinuous RingCat.{0} _ _).obj
        (ringCatSheaf sZ) :=
    i.toRingCatSheafHom ≫
      ((Opens.map i.base).sheafPushforwardContinuous RingCat.{0} _ _).map (ringCatSheafHom sZ)
  let φ₂ : X.ringCatSheaf ⟶ ((Opens.map i.base ⋙
      Opens.map (toSchemeHom sZ)).sheafPushforwardContinuous RingCat.{0} _ _).obj
        (ringCatSheaf sZ) :=
    ringCatSheafHom sX ≫
      ((Opens.map (toSchemeHom sX)).sheafPushforwardContinuous RingCat.{0} _ _).map θ
  have h : φ₁ = φ₂ := by
    apply Sheaf.hom_ext
    ext V f
    exact (hθ V.unop f).symm
  haveI : (PresheafOfModules.pushforward.{0} φ₁.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  haveI : (PresheafOfModules.pushforward.{0} φ₂.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  exact ⟨(SheafOfModules.pullbackComp.{0} i.toRingCatSheafHom (ringCatSheafHom sZ)).app L ≪≫
    eqToIso (@pullback_obj_congr _ _ _ _ _ _ _ _ _ _ _ _ h
      (SheafOfModules.PullbackConstruction.adjunction.{0} φ₁).isRightAdjoint
      (SheafOfModules.PullbackConstruction.adjunction.{0} φ₂).isRightAdjoint L) ≪≫
    ((SheafOfModules.pullbackComp.{0} (ringCatSheafHom sX) θ).app L).symm⟩

/-! ### Analytification of the structure sheaf and of invertible modules -/

/-- The analytification of the structure sheaf of `X` is the structure sheaf of `X^an`. -/
public noncomputable def analytifyUnitIso {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    (analytifyModule sX).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (ringCatSheaf sX) := by
  haveI := Stacks.Topology.final_opensMap (toSchemeHom sX)
  exact @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom sX))
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (ringCatSheafHom sX))

/-- `𝒪_X^an ≅ 𝒪_{X^an}` sends the analytification of `1` to `1`. -/
public theorem analytifyUnitIso_hom_unit_one {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    (analytifyUnitIso sX).hom.val.app (op ⊤)
      ((analytifyModuleUnit sX (SheafOfModules.unit X.ringCatSheaf)).val.app (op ⊤)
        (1 : X.ringCatSheaf.obj.obj (op ⊤))) = (1 : (ringCatSheaf sX).obj.obj (op ⊤)) := by
  haveI := Stacks.Topology.final_opensMap (toSchemeHom sX)
  have h := (Adjunction.homEquiv_unit _ _ _
    (SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom sX))).symm.trans
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (ringCatSheafHom sX))
  refine (congrArg (fun g => g.val.app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤))) h).trans ?_
  exact (SheafOfModules.unitToPushforwardObjUnit_val_app_apply (ringCatSheafHom sX)
    (1 : X.ringCatSheaf.obj.obj (op ⊤))).trans (map_one ((ringCatSheafHom sX).hom.app (op ⊤)).hom)

/-- Invertibility is invariant under isomorphism. -/
private theorem isInvertible_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{0})
    (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
    [J.WEqualsLocallyBijective AddCommGrpCat.{0}] [HasWeakSheafify J AddCommGrpCat.{0}]
    {L N : SheafOfModules.{0} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (e : L ≅ N) (h : SheafOfModules.IsInvertible 𝒪 h𝒪 L) : SheafOfModules.IsInvertible 𝒪 h𝒪 N := by
  refine (Stacks.SheafPicardGroup.isInvertible_iff_isUnit 𝒪 h𝒪 N).2 ?_
  rw [← Stacks.SheafPicardGroup.mk_eq_mk_of_iso 𝒪 h𝒪 e]
  exact (Stacks.SheafPicardGroup.isInvertible_iff_isUnit 𝒪 h𝒪 L).1 h

section Picard

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [QuasiCompact sX]

/-- **Analytification commutes with tensor products.** -/
private theorem nonempty_analytify_sheafTensor_iso (F G : X.Modules) :
    Nonempty ((analytifyModule sX).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj F).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj
        ((analytifyModule sX).obj F)).obj ((analytifyModule sX).obj G)) := by
  obtain ⟨-, -, -, -, -, htens, -⟩ := analytification_stalks sX
  obtain ⟨t, -⟩ := htens F G
  exact ⟨t⟩

/-- **Analytification preserves invertibility.** -/
private theorem isInvertible_analytify (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L) :
    SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2 ((analytifyModule sX).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).1
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 hL)
  obtain ⟨t⟩ := nonempty_analytify_sheafTensor_iso sX L N
  refine (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 ?_
  exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).2
    ⟨(analytifyModule sX).obj N, ⟨t.symm ≪≫ (analytifyModule sX).mapIso e ≪≫ analytifyUnitIso sX⟩⟩

/-- The Picard group of `X^an`. -/
private abbrev PicAn : Type 1 :=
  Stacks.SheafPicardGroup.PicardGroup (J := Opens.grothendieckTopology (space sX))
    (structureSheaf sX).obj (ringCatSheaf sX).2

/-- `[L] ↦ [L^an]` on Picard classes, through a chosen representative. -/
private noncomputable def picardFun (x : Stacks.SheafPicardGroup.schemePicardGroup X) : PicAn sX :=
  @Stacks.SheafPicardGroup.classOf _ _ (Opens.grothendieckTopology (space sX))
    (structureSheaf sX).obj (ringCatSheaf sX).2 _ _
    ((analytifyModule sX).obj (Stacks.SheafPicardGroup.exists_classOf _ _ x).choose)
    (isInvertible_analytify sX _ (Stacks.SheafPicardGroup.exists_classOf _ _ x).choose_spec.choose)

private theorem picardFun_classOf (L : X.Modules) [hL : Stacks.Ample.IsInvertibleModule X L] :
    picardFun sX (Stacks.SheafPicardGroup.schemeClassOf X L) =
      @Stacks.SheafPicardGroup.classOf _ _ (Opens.grothendieckTopology (space sX))
        (structureSheaf sX).obj (ringCatSheaf sX).2 _ _ ((analytifyModule sX).obj L)
        (isInvertible_analytify sX L hL) := by
  obtain ⟨h1, h2⟩ := (Stacks.SheafPicardGroup.exists_classOf _ _
    (Stacks.SheafPicardGroup.schemeClassOf X L)).choose_spec
  obtain ⟨e⟩ := (@Stacks.SheafPicardGroup.classOf_eq_classOf_iff _ _ _ _ _ _ _ _ _ h1 hL).1 h2
  exact (@Stacks.SheafPicardGroup.classOf_eq_classOf_iff _ _ _ _ _ _ _ _ _
    (isInvertible_analytify sX _ h1) (isInvertible_analytify sX L hL)).2
    ⟨(analytifyModule sX).mapIso e⟩

private theorem picardFun_one : picardFun sX 1 = 1 := by
  refine (congrArg (picardFun sX) (Stacks.SheafPicardGroup.classOf_unit X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))).symm.trans
    ((picardFun_classOf sX _).trans ?_)
  exact (@Stacks.SheafPicardGroup.classOf_eq_one_iff _ _ _ _ _ _ _ _
    (isInvertible_analytify sX _ inferInstance)).2 ⟨analytifyUnitIso sX⟩

private theorem picardFun_mul (x y : Stacks.SheafPicardGroup.schemePicardGroup X) :
    picardFun sX (x * y) = picardFun sX x * picardFun sX y := by
  obtain ⟨L, hL, rfl⟩ := Stacks.SheafPicardGroup.exists_classOf _ _ x
  obtain ⟨N, hN, rfl⟩ := Stacks.SheafPicardGroup.exists_classOf _ _ y
  haveI : Stacks.Ample.IsInvertibleModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj N) :=
    isInvertible_of_iso _ _ (AlgebraicGeometry.SheafOfModules.tensorIso _ _ L N)
      (AlgebraicGeometry.SheafOfModules.isInvertible_tensor _ _ L N)
  obtain ⟨t⟩ := nonempty_analytify_sheafTensor_iso sX L N
  have hLa := isInvertible_analytify sX L hL
  have hNa := isInvertible_analytify sX N hN
  have hT : SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2
      (((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj
        ((analytifyModule sX).obj L)).obj ((analytifyModule sX).obj N)) :=
    isInvertible_of_iso _ _ (AlgebraicGeometry.SheafOfModules.tensorIso _ _ _ _)
      (AlgebraicGeometry.SheafOfModules.isInvertible_tensor _ _ _ _)
  change picardFun sX (Stacks.SheafPicardGroup.schemeClassOf X L *
    Stacks.SheafPicardGroup.schemeClassOf X N) = _
  refine (congrArg (picardFun sX)
    (Stacks.SheafPicardGroup.schemeClassOf_tensorSheaf X L N)).symm.trans
    ((picardFun_classOf sX _).trans ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (picardFun_classOf sX L).symm
    (picardFun_classOf sX N).symm)
  refine Eq.trans ?_ (@Stacks.SheafPicardGroup.classOf_tensorSheaf _ _ _ _ _ _ _ _ _ hLa hNa hT)
  exact (@Stacks.SheafPicardGroup.classOf_eq_classOf_iff _ _ _ _ _ _ _ _ _
    (isInvertible_analytify sX _ inferInstance) hT).2 ⟨t⟩

/-- **The analytification homomorphism** `Pic X → Pic X^an`, `[L] ↦ [L^an]`. -/
private noncomputable def picardHom : Stacks.SheafPicardGroup.schemePicardGroup X →* PicAn sX where
  toFun := picardFun sX
  map_one' := picardFun_one sX
  map_mul' := picardFun_mul sX

end Picard

/-! ### Morphisms out of the structure sheaf -/

section Unit

variable {T : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}

/-- The global section of `M` determined by an element over the whole space. -/
private noncomputable def topSection (M : SheafOfModules.{0} R) (s : M.val.obj (op ⊤)) :
    M.sections :=
  PresheafOfModules.sectionsMk (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
    (fun U V f => by
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

private theorem topSection_val_top (M : SheafOfModules.{0} R) (s : M.val.obj (op ⊤)) :
    (topSection M s).val (op ⊤) = s := by
  change M.val.map (homOfLE (le_top : (⊤ : Opens T) ≤ ⊤)).op s = s
  rw [show (homOfLE (le_top : (⊤ : Opens T) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _,
    PresheafOfModules.map_id]
  rfl

/-- A morphism out of the structure sheaf is determined by the image of `1` over the whole
space. -/
private theorem hom_ext_unit {M : SheafOfModules.{0} R} {f g : SheafOfModules.unit R ⟶ M}
    (h : f.val.app (op ⊤) (1 : R.obj.obj (op ⊤)) = g.val.app (op ⊤) (1 : R.obj.obj (op ⊤))) :
    f = g := by
  apply M.unitHomEquiv.injective
  ext U
  have hf := PresheafOfModules.sections_property (M.unitHomEquiv f)
    (homOfLE (le_top : U.unop ≤ ⊤)).op
  have hg := PresheafOfModules.sections_property (M.unitHomEquiv g)
    (homOfLE (le_top : U.unop ≤ ⊤)).op
  rw [← hf, ← hg]
  exact congrArg _ h

end Unit

/-! ### Coherence -/

/-- A coherent sheaf of modules in the sense of `Stacks.SheafOfModules.IsCoherent` is coherent in
the sense of `MMP.Analytic.IsCoherentModule`. -/
private theorem isCoherentModule_of_isCoherent {T : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
    {M : SheafOfModules.{0} R} (h : Stacks.SheafOfModules.IsCoherent M) : IsCoherentModule M :=
  ⟨h.isFiniteType, fun V p s => h.kernel_isFiniteType V (Fin p) inferInstance _⟩

/-! ### Global sections -/

/-- **GAGA in degree zero**: for a coherent module `F` on a projective `ℂ`-scheme, every global
section of `F^an` is the analytification of a global section of `F`. -/
private theorem exists_analytifyModuleUnit_app_top_eq {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjective sX) (F : X.Modules) (hF : Stacks.SheafOfModules.IsCoherent F)
    (t : ((analytifyModule sX).obj F).val.obj (op ((Opens.map (toSchemeHom sX)).obj ⊤))) :
    ∃ s : F.val.obj (op ⊤), (analytifyModuleUnit sX F).val.app (op ⊤) s = t := by
  have hc := isIso_comparisonMap_of_isProjective sX hX F hF 0
  have hΓ := MMP.Analytic.ProjectiveTwists.isIso_globalSections_homEquiv _
    (toSchemeHom sX) _ (analytifyModuleι sX F) hc
  erw [analytifyModuleι, Equiv.apply_symm_apply] at hΓ
  exact (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ hΓ).2 t

/-- Two global sections of a sheaf of modules agree once they agree over the whole space. -/
private theorem sections_ext_top {T : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}} {M : SheafOfModules.{0} R}
    {s t : M.sections} (h : s.val (op ⊤) = t.val (op ⊤)) : s = t := by
  ext U
  rw [← PresheafOfModules.sections_property s (homOfLE (le_top : U.unop ≤ ⊤)).op,
    ← PresheafOfModules.sections_property t (homOfLE (le_top : U.unop ≤ ⊤)).op, h]

/-- The analytification of the morphism `free J ⟶ F` given by global sections `t j` of `F` is,
up to `(free J)^an ≅ free J`, the morphism given by any family of sections of `F^an` extending
the analytifications of the `t j`. -/
private theorem exists_analytify_map_freeHomEquiv_symm {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (F : X.Modules) {J : Type} (t : J → F.val.obj (op ⊤))
    (s : J → ((analytifyModule sX).obj F).sections)
    (h : ∀ j, (analytifyModuleUnit sX F).val.app (op ⊤) (t j) = (s j).val (op ⊤)) :
    ∃ e : (analytifyModule sX).obj (SheafOfModules.free J) ≅ SheafOfModules.free J,
      (analytifyModule sX).map (F.freeHomEquiv.symm fun j => topSection F (t j)) =
        e.hom ≫ ((analytifyModule sX).obj F).freeHomEquiv.symm s := by
  haveI := Stacks.Topology.final_opensMap (toSchemeHom sX)
  refine ⟨SheafOfModules.pullbackObjFreeIso (ringCatSheafHom sX) J, ?_⟩
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)
  let ψa : SheafOfModules.free J ⟶ F := F.freeHomEquiv.symm fun j => topSection F (t j)
  let ψ' := ((analytifyModule sX).obj F).freeHomEquiv.symm s
  apply (adj.homEquiv _ _).injective
  have eL : adj.homEquiv _ _ ((analytifyModule sX).map ψa) = ψa ≫ adj.unit.app F :=
    (Adjunction.homEquiv_unit _ _ _ _).trans (adj.unit.naturality ψa).symm
  have eR : adj.homEquiv _ _ ((SheafOfModules.pullbackObjFreeIso (ringCatSheafHom sX) J).hom ≫ ψ')
      = adj.homEquiv _ _ (SheafOfModules.pullbackObjFreeIso (ringCatSheafHom sX) J).hom ≫
        (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map ψ' :=
    Adjunction.homEquiv_naturality_right _ _ _
  refine eL.trans (Eq.trans ?_ eR.symm)
  apply (SheafOfModules.freeHomEquiv _).injective
  funext j
  apply sections_ext_top
  have e1 : SheafOfModules.ιFree j ≫ ψa = F.unitHomEquiv.symm (topSection F (t j)) :=
    (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply ψa j).symm.trans
      (congrArg F.unitHomEquiv.symm (congrFun (F.freeHomEquiv.apply_symm_apply _) j))
  have e2 : SheafOfModules.ιFree j ≫ ψ' =
      ((analytifyModule sX).obj F).unitHomEquiv.symm (s j) :=
    (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply ψ' j).symm.trans
      (congrArg _ (congrFun (((analytifyModule sX).obj F).freeHomEquiv.apply_symm_apply _) j))
  have e3 : SheafOfModules.ιFree j ≫
      adj.homEquiv _ _ (SheafOfModules.pullbackObjFreeIso (ringCatSheafHom sX) J).hom =
      SheafOfModules.unitToPushforwardObjUnit (ringCatSheafHom sX) ≫
        (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map (SheafOfModules.ιFree j) :=
    (Adjunction.homEquiv_naturality_left _ _ _).symm.trans
      ((congrArg (adj.homEquiv _ _)
        (SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ j)).trans
        ((Adjunction.homEquiv_naturality_right _ _ _).trans (congrArg (· ≫ _)
          (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _))))
  have e4 : SheafOfModules.ιFree j ≫ adj.homEquiv _ _
      (SheafOfModules.pullbackObjFreeIso (ringCatSheafHom sX) J).hom ≫
        (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map ψ' =
      SheafOfModules.unitToPushforwardObjUnit (ringCatSheafHom sX) ≫
        (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map
          (((analytifyModule sX).obj F).unitHomEquiv.symm (s j)) := by
    rw [← Category.assoc, e3, Category.assoc, ← Functor.map_comp, e2]
  have e5 : SheafOfModules.ιFree j ≫ ψa ≫ adj.unit.app F =
      F.unitHomEquiv.symm (topSection F (t j)) ≫ adj.unit.app F :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ adj.unit.app F) e1)
  change (SheafOfModules.ιFree j ≫ ψa ≫ adj.unit.app F).val.app (op ⊤)
      (1 : X.ringCatSheaf.obj.obj (op ⊤)) =
    (SheafOfModules.ιFree j ≫ adj.homEquiv _ _
      (SheafOfModules.pullbackObjFreeIso (ringCatSheafHom sX) J).hom ≫
        (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map ψ').val.app (op ⊤)
      (1 : X.ringCatSheaf.obj.obj (op ⊤))
  rw [e4, e5]
  change (adj.unit.app F).val.app (op ⊤) ((F.unitHomEquiv.symm (topSection F (t j))).val.app
      (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤))) =
    (((analytifyModule sX).obj F).unitHomEquiv.symm (s j)).val.app _
      ((ringCatSheafHom sX).hom.app (op ⊤) 1)
  have h1 := SheafOfModules.unitHomEquiv_apply_coe F (F.unitHomEquiv.symm (topSection F (t j)))
    (op ⊤)
  have h2 := SheafOfModules.unitHomEquiv_apply_coe ((analytifyModule sX).obj F)
    (((analytifyModule sX).obj F).unitHomEquiv.symm (s j)) (op ⊤)
  rw [Equiv.apply_symm_apply] at h1 h2
  refine (congrArg _ (h1.symm.trans (topSection_val_top F (t j)))).trans ((h j).trans ?_)
  exact h2.trans (congrArg _ (map_one _).symm)

/-! ### Injectivity -/

section Injective

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [QuasiCompact sX]

/-- **A coherent module with trivial analytification is trivial.** -/
private theorem nonempty_iso_unit_of_analytify (hX : IsProjective sX) [IsLocallyNoetherian X]
    (F : X.Modules) (hF : Stacks.SheafOfModules.IsCoherent F)
    (φ : (analytifyModule sX).obj F ≅ SheafOfModules.unit (ringCatSheaf sX)) :
    Nonempty (F ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨-, -, -, hlim, hcolim, -, -, hvan, -⟩ := analytification_stalks sX
  let t : ((analytifyModule sX).obj F).val.obj (op ((Opens.map (toSchemeHom sX)).obj ⊤)) :=
    φ.inv.val.app (op ⊤) (1 : (ringCatSheaf sX).obj.obj (op ⊤))
  obtain ⟨s₀, hs₀⟩ := exists_analytifyModuleUnit_app_top_eq sX hX F hF t
  let g : SheafOfModules.unit X.ringCatSheaf ⟶ F := F.unitHomEquiv.symm (topSection F s₀)
  have hg1 : g.val.app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤)) = s₀ := by
    have := SheafOfModules.unitHomEquiv_apply_coe F g (op ⊤)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm.trans (topSection_val_top F s₀)
  -- the analytification of `g` is an isomorphism
  have hga : (analytifyModule sX).map g = (analytifyUnitIso sX).hom ≫ φ.inv := by
    let adj := SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)
    apply (adj.homEquiv _ _).injective
    have e1 : adj.homEquiv _ _ ((analytifyModule sX).map g) = g ≫ adj.unit.app F :=
      (Adjunction.homEquiv_unit _ _ _ _).trans (adj.unit.naturality g).symm
    have e2 : adj.homEquiv _ _ ((analytifyUnitIso sX).hom ≫ φ.inv) =
        SheafOfModules.unitToPushforwardObjUnit (ringCatSheafHom sX) ≫
          (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map φ.inv :=
      (Adjunction.homEquiv_naturality_right _ _ _).trans (congrArg (· ≫ _)
        (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _))
    refine e1.trans (Eq.trans ?_ e2.symm)
    apply hom_ext_unit
    change (analytifyModuleUnit sX F).val.app (op ⊤) (g.val.app (op ⊤) _) =
      φ.inv.val.app _ ((ringCatSheafHom sX).hom.app (op ⊤) 1)
    rw [hg1, map_one]
    exact hs₀
  haveI : IsIso ((analytifyModule sX).map g) := by rw [hga]; infer_instance
  -- kernel and cokernel of `g`
  have hK : IsZero (kernel g) := by
    have hkK : IsCoherentModule (kernel g) :=
      MMP.Analytic.CoherentAnalytic.isCoherentModule_kernel g
        (isCoherentModule_of_isCoherent
          (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
            (Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X)))
        (isCoherentModule_of_isCoherent hF)
    refine hvan _ hkK.1 ?_
    exact (isZero_kernel_of_mono ((analytifyModule sX).map g)).of_iso
      (PreservesKernel.iso (analytifyModule sX) g)
  have hC : IsZero (cokernel g) := by
    haveI : Epi (cokernel.π g) := coequalizer.π_epi
    refine hvan _ (MMP.Analytic.CoherentAnalytic.isFiniteType_of_epi (cokernel.π g)
      hF.isFiniteType) ?_
    exact (isZero_cokernel_of_epi ((analytifyModule sX).map g)).of_iso
      (PreservesCokernel.iso (analytifyModule sX) g)
  haveI := Preadditive.mono_of_isZero_kernel g hK
  haveI := Preadditive.epi_of_isZero_cokernel g hC
  haveI := isIso_of_mono_of_epi g
  exact ⟨(asIso g).symm⟩

/-- **Analytification is injective on Picard groups.** -/
private theorem injective_picardHom (hX : IsProjective sX) [IsLocallyNoetherian X] :
    Function.Injective (picardHom sX) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨L, hL, rfl⟩ := Stacks.SheafPicardGroup.exists_classOf _ _ x
  obtain ⟨φ⟩ := (@Stacks.SheafPicardGroup.classOf_eq_one_iff _ _ _ _ _ _ _ _
    (isInvertible_analytify sX L hL)).1 ((picardFun_classOf sX L).symm.trans hx)
  have hcoh : Stacks.SheafOfModules.IsCoherent L :=
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L)
  obtain ⟨e⟩ := nonempty_iso_unit_of_analytify sX hX L hcoh φ
  exact (Stacks.SheafPicardGroup.classOf_eq_one_iff _ _ L).2 ⟨e⟩

end Injective

/-! ### Tensor products on `X^an` -/

section Tensor

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- The tensor product `A ⊗ B` of sheaves of `𝒪_{X^an}`-modules. -/
private noncomputable abbrev tensAn (A B : SheafOfModules.{0} (ringCatSheaf sX)) :
    SheafOfModules.{0} (ringCatSheaf sX) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj A).obj B

/-- Associativity of the tensor product on `X^an`. -/
private noncomputable def tensAnAssoc (A B C : SheafOfModules.{0} (ringCatSheaf sX)) :
    tensAn sX (tensAn sX A B) C ≅ tensAn sX A (tensAn sX B C) := by
  letI := Stacks.SheafOfModules.Strict.monoidalCategory (structureSheaf sX).obj
    (ringCatSheaf sX).2
  exact MonoidalCategoryStruct.associator (C := SheafOfModules.{0}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf (structureSheaf sX).obj
      (ringCatSheaf sX).2)) A B C

/-- Commutativity of the tensor product on `X^an`. -/
private noncomputable def tensAnBraid (A B : SheafOfModules.{0} (ringCatSheaf sX)) :
    tensAn sX A B ≅ tensAn sX B A :=
  Stacks.SheafOfModules.Strict.braiding (structureSheaf sX).obj (ringCatSheaf sX).2 A B

/-- The structure sheaf is a unit for the tensor product on `X^an`. -/
private noncomputable def tensAnUnit (A : SheafOfModules.{0} (ringCatSheaf sX)) :
    tensAn sX (SheafOfModules.unit (ringCatSheaf sX)) A ≅ A := by
  letI := Stacks.SheafOfModules.Strict.monoidalCategory (structureSheaf sX).obj
    (ringCatSheaf sX).2
  exact MonoidalCategoryStruct.leftUnitor (C := SheafOfModules.{0}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf (structureSheaf sX).obj
      (ringCatSheaf sX).2)) A

/-- Tensoring with an invertible sheaf of `𝒪_{X^an}`-modules is an equivalence. -/
private theorem isEquivalence_tensAn (V : SheafOfModules.{0} (ringCatSheaf sX))
    (hV : SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2 V) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj V).IsEquivalence :=
  (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ V).1
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ V).2 hV)

/-- `V ⊗ (S ⊗ T) ≅ S` when `T ⊗ V ≅ 𝒪`. -/
private noncomputable def tensAnCancel (S T V : SheafOfModules.{0} (ringCatSheaf sX))
    (e : tensAn sX T V ≅ SheafOfModules.unit (ringCatSheaf sX)) :
    tensAn sX V (tensAn sX S T) ≅ S :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj V).mapIso
      (tensAnBraid sX S T) ≪≫ (tensAnAssoc sX V T S).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).mapIso
      (tensAnBraid sX V T ≪≫ e)).app S ≪≫ tensAnUnit sX S

variable [LocallyOfFiniteType sX] [QuasiCompact sX]

/-- An invertible `𝒪_X`-module has a coherent inverse whose analytification is an inverse of the
analytification. -/
private theorem exists_analytify_tensAn_inverse [IsLocallyNoetherian X] (L : X.Modules)
    [hL : Stacks.Ample.IsInvertibleModule X L] :
    ∃ I : X.Modules, Stacks.SheafOfModules.IsCoherent I ∧
      SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
        (structureSheaf sX).obj (ringCatSheaf sX).2 ((analytifyModule sX).obj I) ∧
      Nonempty (tensAn sX ((analytifyModule sX).obj L) ((analytifyModule sX).obj I) ≅
        SheafOfModules.unit (ringCatSheaf sX)) := by
  let I := AlgebraicGeometry.SheafOfModules.tensorInv X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L
  haveI hI : Stacks.Ample.IsInvertibleModule X I :=
    AlgebraicGeometry.SheafOfModules.isInvertible_tensorInv X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L
  obtain ⟨t⟩ := nonempty_analytify_sheafTensor_iso sX L I
  refine ⟨I, AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
    (Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X I),
    isInvertible_analytify sX I hI, ⟨t.symm ≪≫ (analytifyModule sX).mapIso
      ((AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L I).symm ≪≫
        AlgebraicGeometry.SheafOfModules.tensorInvMulIso X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L ≪≫
        AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)) ≪≫ analytifyUnitIso sX⟩⟩

end Tensor

/-- A finite free module on a locally Noetherian scheme is coherent. -/
private theorem isCoherent_free {X : Scheme.{0}} [IsLocallyNoetherian X] (I : Type) [Finite I] :
    Stacks.SheafOfModules.IsCoherent (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  let e : I ≃ ULift.{0} (Fin (Nat.card I)) := (Finite.equivFin I).trans Equiv.ulift.symm
  exact AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
    (Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso'
      ((SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso)
      (Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_free_ulift (Nat.card I)))

/-- The tensor product of coherent modules on a scheme is coherent. -/
private theorem isCoherent_sheafTensor {X : Scheme.{0}} {A B : X.Modules}
    (hA : Stacks.SheafOfModules.IsCoherent A) (hB : Stacks.SheafOfModules.IsCoherent B) :
    Stacks.SheafOfModules.IsCoherent
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj B) :=
  AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
    (@AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace A B
      (AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent hA)
      (AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent hB))

/-- **Analytification preserves coherence** (Oka). -/
private theorem isCoherentModule_analytify {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] {F : X.Modules} (hF : Stacks.SheafOfModules.IsCoherent F) :
    IsCoherentModule ((analytifyModule sX).obj F) :=
  (MMP.Analytic.isCoherentRing_holomorphic_and_analytification.2 X sX).2 F
    (isCoherentModule_of_isCoherent hF)

/-! ### Coherent analytic sheaves on projective space are algebraic -/

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The twisting sheaf `𝒪(k)` of `ℙᴺ_ℂ = Proj (polyGrading ℂ N)`. -/
local notation3 (prettyPrint := false) "𝒪ℙ[" N ", " k "]" =>
  (show (AlgebraicGeometry.Proj (polyGrading ℂ N)).Modules from
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading ℂ N) k)

variable (N : ℕ)

/-- **Every coherent analytic sheaf on `(ℙᴺ)^an` is algebraic**: it is the analytification of a
coherent algebraic sheaf. -/
private theorem exists_isCoherent_analytify_iso_projectiveSpace
    (S : SheafOfModules.{0} (ringCatSheaf (projToSpecCoeff ℂ N)))
    (hS : IsCoherentModule S) :
    ∃ G : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Modules, Stacks.SheafOfModules.IsCoherent G ∧
      Nonempty ((analytifyModule (projToSpecCoeff ℂ N)).obj G ≅ S) := by
  haveI : IsProper (projToSpecCoeff ℂ N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ N
  haveI : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading ℂ N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff ℂ N)
  have hP : IsProjective (projToSpecCoeff ℂ N) :=
    Stacks.WeilDeRham.isProjective_projToSpecCoeff ℂ N
  obtain ⟨-, -, -, -, hcolim, -⟩ :=
    analytification_stalks (projToSpecCoeff ℂ N)
  -- the first twist: `𝒮` is a quotient of `E₁^an`
  obtain ⟨a, ha⟩ := MMP.Analytic.exists_isFiniteType_generatingSections_isZero_sheafCohomology_twist
    N S hS
  obtain ⟨⟨σ, hσ⟩, -⟩ := ha a le_rfl
  obtain ⟨Ia, hIa, hIainv, ⟨ea⟩⟩ := exists_analytify_tensAn_inverse
    (projToSpecCoeff ℂ N)
    (𝒪ℙ[N, a])
  haveI := Stacks.Topology.final_opensMap (toSchemeHom (projToSpecCoeff ℂ N))
  haveI := hcolim
  haveI := isEquivalence_tensAn (projToSpecCoeff ℂ N)
    ((analytifyModule (projToSpecCoeff ℂ N)).obj Ia) hIainv
  let E₁ : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Modules :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor (AlgebraicGeometry.Proj (polyGrading ℂ N)).sheaf).obj
      Ia).obj (SheafOfModules.free σ.I)
  have hE₁ : Stacks.SheafOfModules.IsCoherent E₁ := isCoherent_sheafTensor hIa (isCoherent_free σ.I)
  obtain ⟨tE₁⟩ := nonempty_analytify_sheafTensor_iso (projToSpecCoeff ℂ N)
    Ia (SheafOfModules.free σ.I)
  let FV := (Stacks.SheafOfModules.Tensor.sheafTensor
    (structureSheaf (projToSpecCoeff ℂ N))).obj
      ((analytifyModule (projToSpecCoeff ℂ N)).obj Ia)
  let q₁ : (analytifyModule (projToSpecCoeff ℂ N)).obj E₁ ⟶ S :=
    tE₁.hom ≫ FV.map (SheafOfModules.pullbackObjFreeIso
      (ringCatSheafHom (projToSpecCoeff ℂ N)) σ.I).hom ≫
      FV.map σ.π ≫ (tensAnCancel (projToSpecCoeff ℂ N) S _ _ ea).hom
  haveI : Epi q₁ :=
    epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) <|
      epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ FV _
        (Iso.isIso_hom _))) <|
      epi_comp' (FV.map_epi σ.π) (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))
  -- the second twist: the kernel of `q₁` is a quotient of a free module after twisting
  have hK : IsCoherentModule (kernel q₁) := MMP.Analytic.CoherentAnalytic.isCoherentModule_kernel q₁
    (isCoherentModule_analytify (projToSpecCoeff ℂ N) hE₁) hS
  obtain ⟨b, hb⟩ := MMP.Analytic.exists_isFiniteType_generatingSections_isZero_sheafCohomology_twist
    N (kernel q₁) hK
  obtain ⟨⟨σ₂, hσ₂⟩, -⟩ := hb b le_rfl
  haveI := isEquivalence_tensAn (projToSpecCoeff ℂ N)
    ((analytifyModule (projToSpecCoeff ℂ N)).obj
      (𝒪ℙ[N, b]))
    (isInvertible_analytify _ _ inferInstance)
  let FT := (Stacks.SheafOfModules.Tensor.sheafTensor
    (structureSheaf (projToSpecCoeff ℂ N))).obj
      ((analytifyModule (projToSpecCoeff ℂ N)).obj
        (𝒪ℙ[N, b]))
  let ψ₀ : SheafOfModules.free σ₂.I ⟶ FT.obj (kernel q₁) :=
    σ₂.π ≫ (tensAnBraid (projToSpecCoeff ℂ N) (kernel q₁) _).hom
  haveI : Epi ψ₀ := @epi_comp _ _ _ _ _ σ₂.π inferInstance _
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))
  let ψ := ψ₀ ≫ FT.map (kernel.ι q₁)
  have cψ : cokernel ψ ≅ FT.obj S :=
    cokernelEpiComp ψ₀ (FT.map (kernel.ι q₁)) ≪≫ (PreservesCokernel.iso FT (kernel.ι q₁)).symm ≪≫
      FT.mapIso ((cokernelIsCokernel (kernel.ι q₁)).coconePointUniqueUpToIso
        (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι q₁) (kernel.condition q₁))
          (kernelIsKernel q₁)))
  -- algebraization of the presentation
  let E₂ : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Modules :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor (AlgebraicGeometry.Proj (polyGrading ℂ N)).sheaf).obj
      (𝒪ℙ[N, b])).obj E₁
  have hE₂ : Stacks.SheafOfModules.IsCoherent E₂ := isCoherent_sheafTensor
    (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible _ _)) hE₁
  obtain ⟨tE₂⟩ := nonempty_analytify_sheafTensor_iso (projToSpecCoeff ℂ N)
    (𝒪ℙ[N, b]) E₁
  let ψ' := ψ ≫ tE₂.inv
  have ht := fun j => exists_analytifyModuleUnit_app_top_eq
    (projToSpecCoeff ℂ N) hP E₂ hE₂
    ((((analytifyModule (projToSpecCoeff ℂ N)).obj E₂).freeHomEquiv ψ'
      j).val (op ⊤))
  choose t ht using ht
  obtain ⟨e, he⟩ := exists_analytify_map_freeHomEquiv_symm
    (projToSpecCoeff ℂ N) E₂ t _ ht
  replace he := he.trans (congrArg (e.hom ≫ ·) (Equiv.symm_apply_apply _ ψ'))
  let ψa : SheafOfModules.free σ₂.I ⟶ E₂ := E₂.freeHomEquiv.symm fun j => topSection E₂ (t j)
  have hG'' : Stacks.SheafOfModules.IsCoherent (cokernel ψa) := by
    haveI := AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
      (isCoherent_free (X := AlgebraicGeometry.Proj (polyGrading ℂ N)) σ₂.I)
    haveI := AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent hE₂
    exact AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel ψa)
  have cG'' : (analytifyModule (projToSpecCoeff ℂ N)).obj (cokernel ψa) ≅
      FT.obj S :=
    PreservesCokernel.iso (analytifyModule (projToSpecCoeff ℂ N)) ψa ≪≫
      cokernelIsoOfEq he ≪≫ cokernelEpiComp e.hom ψ' ≪≫
        @cokernelCompIsIso _ _ _ _ _ _ ψ tE₂.inv _ (Iso.isIso_inv tE₂) ≪≫ cψ
  -- untwisting
  obtain ⟨Ib, hIb, -, ⟨eb⟩⟩ := exists_analytify_tensAn_inverse
    (projToSpecCoeff ℂ N)
    (𝒪ℙ[N, b])
  obtain ⟨tG⟩ := nonempty_analytify_sheafTensor_iso (projToSpecCoeff ℂ N)
    Ib (cokernel ψa)
  let FVb := (Stacks.SheafOfModules.Tensor.sheafTensor
    (structureSheaf (projToSpecCoeff ℂ N))).obj
      ((analytifyModule (projToSpecCoeff ℂ N)).obj Ib)
  exact ⟨_, isCoherent_sheafTensor hIb hG'', ⟨tG ≪≫ FVb.mapIso cG'' ≪≫
    FVb.mapIso (tensAnBraid (projToSpecCoeff ℂ N) _ S) ≪≫
    tensAnCancel (projToSpecCoeff ℂ N) S _ _ eb⟩⟩

end ProjectiveSpace

/-! ### Coherence is local -/

section Local

open MMP.Analytic.CoherentAnalytic

variable {T : TopCat.{0}} {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}

/-- **Coherence is local**: a sheaf of modules which, near every point, has sections linearly and
compatibly isomorphic to those of a coherent sheaf is coherent. -/
private theorem isCoherentModule_of_locally {S Q : SheafOfModules.{0} A} (hQ : IsCoherentModule Q)
    (hloc : ∀ x : T, ∃ W : Opens T, x ∈ W ∧ ∃ φ : ∀ U : Opens T, U ≤ W →
      (S.val.obj (op U) ≃ₗ[A.obj.obj (op U)] Q.val.obj (op U)),
      ∀ (U U' : Opens T) (hU : U ≤ W) (h : U' ≤ U) (s : S.val.obj (op U)),
        resM Q h (φ U hU s) = φ U' (h.trans hU) (resM S h s)) :
    IsCoherentModule S := by
  refine isCoherentModule_of_finGen_of_relFin ?_ ?_
  · intro x
    obtain ⟨W, hxW, φ, hφ⟩ := hloc x
    obtain ⟨W₁, hxW₁, m, g, hg⟩ := (isFiniteType_iff_finGen Q).1 hQ.1 x
    refine ⟨W ⊓ W₁, ⟨hxW, hxW₁⟩, m,
      fun k => (φ (W ⊓ W₁) inf_le_left).symm (resM Q inf_le_right (g k)), ?_⟩
    refine locallyGenerates_of_nhds _ fun U hU t y hy => ?_
    obtain ⟨U', h, hy', c, hc⟩ :=
      hg.exists_nhds (hU.trans inf_le_right) (φ U (hU.trans inf_le_left) t) hy
    refine ⟨U', h, hy', c, (φ U' ((h.trans hU).trans inf_le_left)).injective ?_⟩
    rw [map_sum, ← hφ U U' (hU.trans inf_le_left) h t, hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearEquiv.map_smul, ← hφ (W ⊓ W₁) U' inf_le_left (h.trans hU),
      LinearEquiv.apply_symm_apply, resM_resM]
  · intro V p f x hx
    obtain ⟨W, hxW, φ, hφ⟩ := hloc x
    obtain ⟨W'', hW''V', hxW'', s, r, hrel, hcomp⟩ := relFin_of_isCoherentModule hQ (V ⊓ W) p
      (fun j => φ (V ⊓ W) inf_le_right (resM S inf_le_left (f j))) x ⟨hx, hxW⟩
    have key : ∀ (U : Opens T) (hU : U ≤ V ⊓ W) (j : Fin p),
        φ U (hU.trans inf_le_right) (resM S (hU.trans inf_le_left) (f j)) =
          resM Q hU (φ (V ⊓ W) inf_le_right (resM S inf_le_left (f j))) := fun U hU j => by
      rw [hφ (V ⊓ W) U inf_le_right hU, resM_resM]
    refine ⟨W'', hW''V'.trans inf_le_left, hxW'', s, r, fun k => ?_,
      fun U hUW a ha y hy => hcomp U hUW a ?_ y hy⟩
    · apply (φ W'' (hW''V'.trans inf_le_right)).injective
      rw [map_zero, map_sum, ← hrel k]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearEquiv.map_smul, key W'' hW''V' j]
    · have h := congrArg (φ U ((hUW.trans hW''V').trans inf_le_right)) ha
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearEquiv.map_smul, key U (hUW.trans hW''V') j]

/-- The sections of two sheaves of modules isomorphic over `W` are linearly and compatibly
isomorphic over the opens contained in `W`. -/
private theorem exists_linearEquiv_of_over_iso {S Q : SheafOfModules.{0} A} {W : Opens T}
    (e : S.over W ≅ Q.over W) :
    ∃ φ : ∀ U : Opens T, U ≤ W →
      (S.val.obj (op U) ≃ₗ[A.obj.obj (op U)] Q.val.obj (op U)),
      ∀ (U U' : Opens T) (hU : U ≤ W) (h : U' ≤ U) (s : S.val.obj (op U)),
        resM Q h (φ U hU s) = φ U' (h.trans hU) (resM S h s) := by
  let V : ∀ U : Opens T, U ≤ W → Over W := fun U hU => Over.mk (homOfLE hU)
  refine ⟨fun U hU =>
    { toFun := fun s => (e.hom.val.app (op (V U hU))).hom s
      invFun := fun q => (e.inv.val.app (op (V U hU))).hom q
      map_add' := fun a b => (e.hom.val.app (op (V U hU))).hom.map_add a b
      map_smul' := fun a s => (e.hom.val.app (op (V U hU))).hom.map_smul a s
      left_inv := fun s => ConcreteCategory.congr_hom
        (congrArg (fun g => g.val.app (op (V U hU))) e.hom_inv_id) s
      right_inv := fun q => ConcreteCategory.congr_hom
        (congrArg (fun g => g.val.app (op (V U hU))) e.inv_hom_id) q }, ?_⟩
  intro U U' hU h s
  exact (ConcreteCategory.congr_hom (e.hom.val.naturality
    (Over.homMk (U := V U' (h.trans hU)) (V := V U hU) (homOfLE h)).op) s).symm

end Local

/-! ### Direct images along embeddings -/

section Embedding

variable {T T' : TopCat.{0}} (f : T' ⟶ T)
  {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
  {B : Sheaf (Opens.grothendieckTopology T') RingCat.{0}}
  [(Opens.map f).IsContinuous (Opens.grothendieckTopology T) (Opens.grothendieckTopology T')]
  (θ : A ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{0} (Opens.grothendieckTopology T)
    (Opens.grothendieckTopology T')).obj B)

/-- `θ : A ⟶ f_* B` is *locally surjective*: a section of `B` over `f⁻¹ W` is, near each point,
the image of a section of `A`. -/
private def IsLocallySurjectiveOnSections : Prop :=
  ∀ (W : Opens T) (b : B.obj.obj (op ((Opens.map f).obj W))) (x : T'), f x ∈ W →
    ∃ (W' : Opens T) (h : W' ≤ W), f x ∈ W' ∧ ∃ a : A.obj.obj (op W'),
      θ.hom.app (op W') a = B.obj.map ((Opens.map f).map (homOfLE h)).op b

/-- An epimorphism `𝒪_T ⟶ θ_* 𝒪_{T'}` makes `θ` locally surjective. -/
private theorem isLocallySurjectiveOnSections_of_epi
    [Epi (SheafOfModules.unitToPushforwardObjUnit θ)] : IsLocallySurjectiveOnSections f θ := by
  intro W b x hx
  have hl := MMP.Analytic.CoherentAnalytic.liftSieve_mem_of_epi
    (SheafOfModules.unitToPushforwardObjUnit θ) (X := W) b
  obtain ⟨W', g, ⟨a, ha⟩, hxW'⟩ := (Opens.mem_grothendieckTopology _).1 hl (f x) hx
  exact ⟨W', g.le, hxW', a, ha⟩

variable {f θ}

/-- Every open subset of the source of an inducing map is a preimage. -/
private theorem exists_opensMap_eq (hf : Topology.IsInducing f) (U : Opens T') :
    ∃ W : Opens T, (Opens.map f).obj W = U := by
  obtain ⟨t, ht, hts⟩ := hf.isOpen_iff.1 U.isOpen
  exact ⟨⟨t, ht⟩, Opens.ext hts⟩

/-- Direct image along an inducing map is faithful. -/
private theorem faithful_pushforward (hf : Topology.IsInducing f) :
    (SheafOfModules.pushforward.{0} θ).Faithful := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  haveI : IsIso adj.counit := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun S => MMP.Analytic.CoherentAnalytic.isIso_pullbackPushforwardAdjunction_counit hf S)
  refine ⟨fun {N N'} u₁ u₂ h => (SheafOfModules.toSheaf B).map_injective
    (adj.fullyFaithfulROfIsIsoCounit.map_injective ?_)⟩
  exact congrArg (SheafOfModules.toSheaf A).map h

/-- **Direct image along an embedding is full** when the ring map is locally surjective: a
morphism of direct images comes from a morphism of abelian sheaves, since `f⁻¹ f_* ≅ id`, and
that morphism is linear because it is linear over the image of `θ`, which generates locally. -/
private theorem full_pushforward (hf : Topology.IsInducing f)
    (hθ : IsLocallySurjectiveOnSections f θ) : (SheafOfModules.pushforward.{0} θ).Full := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  haveI : IsIso adj.counit := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun S => MMP.Analytic.CoherentAnalytic.isIso_pullbackPushforwardAdjunction_counit hf S)
  let ffR := adj.fullyFaithfulROfIsIsoCounit
  refine ⟨fun {N N'} w => ?_⟩
  let w' : (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj ((SheafOfModules.toSheaf B).obj N) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj ((SheafOfModules.toSheaf B).obj N') :=
    (SheafOfModules.toSheaf A).map w
  let uab := ffR.preimage w'
  have hkey : ∀ W : Opens T, uab.hom.app (op ((Opens.map f).obj W)) = w'.hom.app (op W) :=
    fun W => congrArg (fun φ => φ.hom.app (op W)) (ffR.map_preimage w')
  have hlin : ∀ (U : (Opens T')ᵒᵖ) (r : B.obj.obj U) (m : N.val.obj U),
      uab.hom.app U (r • m) = r • (show N'.val.obj U from uab.hom.app U m) := by
    intro U r m
    induction U using Opposite.rec with | op U =>
    obtain ⟨W, rfl⟩ := exists_opensMap_eq hf U
    refine sub_eq_zero.1 (MMP.Analytic.CoherentAnalytic.eq_zero_of_locally_eq_zero N' _ ?_)
    intro x hx
    obtain ⟨W', hW'W, hxW', a, ha⟩ := hθ W r x hx
    let ρ : (Opens.map f).obj W' ⟶ (Opens.map f).obj W := (Opens.map f).map (homOfLE hW'W)
    refine ⟨(Opens.map f).obj W', ρ.le, hxW', ?_⟩
    let a' : B.obj.obj (op ((Opens.map f).obj W')) := θ.hom.app (op W') a
    have ha' : a' = B.obj.map ρ.op r := ha
    let resN : N.val.obj (op ((Opens.map f).obj W)) → N.val.obj (op ((Opens.map f).obj W')) :=
      fun n => N.val.map ρ.op n
    let resN' : N'.val.obj (op ((Opens.map f).obj W)) → N'.val.obj (op ((Opens.map f).obj W')) :=
      fun n => N'.val.map ρ.op n
    let u₀ : N.val.obj (op ((Opens.map f).obj W)) → N'.val.obj (op ((Opens.map f).obj W)) :=
      fun n => uab.hom.app (op ((Opens.map f).obj W)) n
    let u₁ : N.val.obj (op ((Opens.map f).obj W')) → N'.val.obj (op ((Opens.map f).obj W')) :=
      fun n => uab.hom.app (op ((Opens.map f).obj W')) n
    have e1 : ∀ n, resN' (u₀ n) = u₁ (resN n) := fun n =>
      (ConcreteCategory.congr_hom (uab.hom.naturality ρ.op) n).symm
    have e3 : resN (r • m) = a' • resN m := by
      change N.val.map ρ.op (r • m) = a' • N.val.map ρ.op m
      rw [PresheafOfModules.map_smul, ha']
    have e5 : resN' (r • u₀ m) = a' • resN' (u₀ m) := by
      change N'.val.map ρ.op (r • u₀ m) = a' • N'.val.map ρ.op (u₀ m)
      rw [PresheafOfModules.map_smul, ha']
    have e4 : ∀ n, u₁ (a' • n) = a' • u₁ n := by
      intro n
      let n' : ((SheafOfModules.pushforward.{0} θ).obj N).val.obj (op W') := n
      have k1 : u₁ (a' • n) = (w.val.app (op W')).hom (a • n') :=
        ConcreteCategory.congr_hom (hkey W') (a' • n)
      have k2 : u₁ n = (w.val.app (op W')).hom n' := ConcreteCategory.congr_hom (hkey W') n
      rw [k1, k2]
      exact (w.val.app (op W')).hom.map_smul a n'
    change resN' (u₀ (r • m) - r • u₀ m) = 0
    have hsub : resN' (u₀ (r • m) - r • u₀ m) = resN' (u₀ (r • m)) - resN' (r • u₀ m) :=
      map_sub (N'.val.map ρ.op).hom _ _
    rw [hsub, sub_eq_zero, e1, e3, e4, e5, e1]
  let u : N ⟶ N' := ⟨PresheafOfModules.homMk uab.hom hlin⟩
  refine ⟨u, ?_⟩
  ext W m
  induction W using Opposite.rec with | op W =>
  exact ConcreteCategory.congr_hom (hkey W) m

/-- The counit `θ^* θ_* M ⟶ M` is an isomorphism for an embedding with locally surjective `θ`. -/
private theorem isIso_pullbackPushforwardAdjunction_counit_app (hf : Topology.IsInducing f)
    (hθ : IsLocallySurjectiveOnSections f θ) [(SheafOfModules.pushforward.{0} θ).IsRightAdjoint]
    (M : SheafOfModules.{0} B) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction.{0} θ).counit.app M) := by
  haveI := faithful_pushforward (θ := θ) hf
  haveI := full_pushforward hf hθ
  infer_instance

/-- The direct image of a locally trivial module along a closed embedding is coherent, given that
the direct image of the structure sheaf is coherent. -/
private theorem isCoherentModule_pushforward_of_locallyTrivial (hf : Topology.IsClosedEmbedding f)
    [(SheafOfModules.pushforward.{0} θ).IsRightAdjoint]
    (hQ : IsCoherentModule ((SheafOfModules.pushforward.{0} θ).obj (SheafOfModules.unit B)))
    (M : SheafOfModules.{0} B)
    (hM : ∀ y : T', ∃ W : Opens T', y ∈ W ∧
      Nonempty (M.over W ≅ (SheafOfModules.unit B).over W)) :
    IsCoherentModule ((SheafOfModules.pushforward.{0} θ).obj M) := by
  refine isCoherentModule_of_locally hQ fun x => ?_
  by_cases hx : x ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hx
    obtain ⟨W₀, hyW₀, ⟨e₀⟩⟩ := hM y
    obtain ⟨W, rfl⟩ := exists_opensMap_eq hf.isInducing W₀
    obtain ⟨φ, hφ⟩ := exists_linearEquiv_of_over_iso e₀
    refine ⟨W, hyW₀, fun U hU =>
      { toFun := φ ((Opens.map f).obj U) ((Opens.map f).map (homOfLE hU)).le
        invFun := (φ ((Opens.map f).obj U) ((Opens.map f).map (homOfLE hU)).le).symm
        map_add' := map_add _
        map_smul' := fun a m => (φ _ _).map_smul (θ.hom.app (op U) a) m
        left_inv := (φ _ _).left_inv
        right_inv := (φ _ _).right_inv }, ?_⟩
    intro U U' hU h m
    exact hφ _ _ _ ((Opens.map f).map (homOfLE h)).le m
  · have hbot : ∀ U : Opens T, U ≤ ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩ →
        (Opens.map f).obj U = ⊥ := fun U hU => by
      ext y
      simp only [Opens.map_obj, Opens.mem_mk, Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun hy => hU hy ⟨y, rfl⟩, fun h => h.elim⟩
    refine ⟨⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩, hx, fun U hU => ?_, ?_⟩
    · haveI : Subsingleton (((SheafOfModules.pushforward.{0} θ).obj M).val.obj (op U)) :=
        (MMP.Analytic.CoherentAnalytic.subsingleton_of_isTerminal
          (TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf B).obj M) (hbot U hU)) :
            Subsingleton (M.val.obj (op ((Opens.map f).obj U))))
      haveI : Subsingleton (((SheafOfModules.pushforward.{0} θ).obj
          (SheafOfModules.unit B)).val.obj (op U)) :=
        (MMP.Analytic.CoherentAnalytic.subsingleton_of_isTerminal
          (TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf B).obj
            (SheafOfModules.unit B)) (hbot U hU)) :
              Subsingleton ((SheafOfModules.unit B).val.obj (op ((Opens.map f).obj U))))
      exact LinearEquiv.ofSubsingleton _ _
    · intro U U' hU h m
      haveI : Subsingleton (((SheafOfModules.pushforward.{0} θ).obj
          (SheafOfModules.unit B)).val.obj (op U')) :=
        (MMP.Analytic.CoherentAnalytic.subsingleton_of_isTerminal
          (TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf B).obj
            (SheafOfModules.unit B)) (hbot U' (h.trans hU))) :
              Subsingleton ((SheafOfModules.unit B).val.obj (op ((Opens.map f).obj U'))))
      exact Subsingleton.elim _ _

end Embedding

/-! ### Local rings of `X^an` -/

/-- A holomorphic germ not vanishing at the base point is a unit. -/
private theorem isUnit_holGerms_of_value_ne_zero {n : ℕ} {p : Fin n → ℂ} (g : holGerms p)
    (hg : Filter.Germ.value (g : Filter.Germ (nhds p) ℂ) ≠ 0) : IsUnit g := by
  obtain ⟨f, hfg, hf⟩ := g.2
  have hfp : f p ≠ 0 := by rwa [← hfg] at hg
  have hne : ∀ᶠ y in nhds p, f y ≠ 0 :=
    hf.self_of_nhds.continuousAt.eventually_ne hfp
  refine IsUnit.of_mul_eq_one (b := ⟨((f⁻¹ : (Fin n → ℂ) → ℂ) : Filter.Germ (nhds p) ℂ),
    coe_mem_holGerms ((hf.and hne).mono fun y h => h.1.inv h.2)⟩) (Subtype.ext ?_)
  change (g : Filter.Germ (nhds p) ℂ) * ((f⁻¹ : (Fin n → ℂ) → ℂ) : Filter.Germ (nhds p) ℂ) = 1
  rw [← hfg]
  change ((f * f⁻¹ : (Fin n → ℂ) → ℂ) : Filter.Germ (nhds p) ℂ) =
    ((1 : (Fin n → ℂ) → ℂ) : Filter.Germ (nhds p) ℂ)
  exact Filter.Germ.coe_eq.2 (hne.mono fun y hy => by simp [hy])

/-- The ring of holomorphic germs at a point is local. -/
private theorem isLocalRing_holGerms {n : ℕ} (p : Fin n → ℂ) : IsLocalRing (holGerms p) := by
  let ev : holGerms p →+* ℂ := Filter.Germ.valueRingHom.comp (holGerms p).subtype
  have hev : ∀ g, ev g = Filter.Germ.value (g : Filter.Germ (nhds p) ℂ) := fun _ => rfl
  haveI : Nontrivial (holGerms p) := ⟨⟨0, 1, fun h => by
    have := congrArg ev h
    rw [map_zero, map_one] at this
    exact zero_ne_one this⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun g => ?_
  by_cases hg : ev g = 0
  · right
    refine isUnit_holGerms_of_value_ne_zero _ ?_
    rw [← hev, map_sub, map_one, hg, sub_zero]
    exact one_ne_zero
  · exact Or.inl (isUnit_holGerms_of_value_ne_zero g hg)

section LocalRing

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [QuasiCompact sX]

/-- The stalks of `𝒪_{X^an}` are local rings. -/
private theorem isLocalRing_analytification_stalk (y : ComplexPoints sX) :
    IsLocalRing ((analytification sX).presheaf.stalk y) := by
  obtain ⟨⟨-, -, -, hchart⟩, hflat, -⟩ := analytification_stalks sX
  obtain ⟨c, hc⟩ := MMP.Analytic.OkaCoherence.exists_chart y
  obtain ⟨e, -⟩ := hchart y c hc
  haveI hB : Nontrivial ((analytification sX).presheaf.stalk y) := by
    obtain ⟨hloc, -⟩ := hflat y
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h0 : IsUnit (((analytificationHom sX).hom.stalkMap y).hom 0) := isUnit_of_subsingleton _
    exact not_isUnit_zero (hloc.map_nonunit 0 h0)
  haveI := isLocalRing_holGerms (c.coords ⟨y, hc⟩)
  haveI : Nontrivial (c.StalkRing (c.coords ⟨y, hc⟩)) := e.injective.nontrivial
  haveI : IsLocalRing (c.StalkRing (c.coords ⟨y, hc⟩)) :=
    IsLocalRing.of_surjective' (Chart.StalkRing.mk c _) Ideal.Quotient.mk_surjective
  exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective

/-- **An invertible sheaf of `𝒪_{X^an}`-modules is locally trivial.** -/
private theorem exists_over_iso_unit_of_isInvertible (M : SheafOfModules.{0} (ringCatSheaf sX))
    (hM : SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2 M) (y : ComplexPoints sX) :
    ∃ W : Opens (space sX), y ∈ W ∧
      Nonempty (M.over W ≅ (SheafOfModules.unit (ringCatSheaf sX)).over W) := by
  haveI : ∀ y, IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
      (analytification sX) y) := isLocalRing_analytification_stalk sX
  haveI : Stacks.SheafOfModules.IsInvertible (analytification sX).presheaf
      (structureSheafRing (analytification sX)).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).2 hM
  obtain ⟨I, Xs, hXs, hiso⟩ := (Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible
    (X := analytification sX) M).exists_trivializing_cover
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff (U := Xs)).1 hXs).exists_mem y
  exact ⟨Xs i, hi, hiso i⟩

end LocalRing

/-- A projective `ℂ`-scheme embeds as a closed subscheme of some `ℙᴺ_ℂ`. -/
private theorem exists_isClosedImmersion_projectiveSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) :
    ∃ (N : ℕ) (i : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ N)), IsClosedImmersion i ∧
      i ≫ projToSpecCoeff ℂ N = sX := by
  obtain ⟨n, j, hj, hjs⟩ := isProjectiveMorphism_of_isProjective_of_isAffine sX hX
  let L := Stacks.AmpleProjectiveImmersion.linearEmbeddingOver (Spec (.of ℂ)) (Nat.le_succ n)
  haveI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun a c ha hc => @IsClosedImmersion.comp _ _ _ a c ha hc⟩
  have hL : IsClosedImmersion L :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance
      (Stacks.AmpleProjectiveImmersion.isClosedImmersion_linearEmbeddingAtUniverse
        (Nat.le_succ n)) (Category.id_comp _).symm (by simp)
  let e := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ (n + 1)
  refine ⟨n + 1, j ≫ L ≫ e.iso.hom, ?_, ?_⟩
  · haveI := hj
    infer_instance
  · rw [Category.assoc, Category.assoc, projToSpecCoeff, e.toBase]
    erw [Stacks.AmpleProjectiveImmersion.linearEmbeddingOver_comp_fst]
    exact hjs

/-! ### The ring map of a closed immersion is locally surjective -/

/-- **The ring map `θ : 𝒪_{P^an} ⟶ i^an_* 𝒪_{X^an}` of a closed immersion is an epimorphism of
modules**: it is the analytification of the epimorphism `𝒪_P ⟶ i_* 𝒪_X`, up to the
identification `(i_* 𝒪_X)^an ≅ i^an_* 𝒪_X^an`. -/
private theorem epi_unitToPushforwardObjUnit_of_isClosedImmersion {X P : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (sP : P ⟶ Spec (.of ℂ)) (i : X ⟶ P) [IsClosedImmersion i]
    (hi : i ≫ sP = sX)
    [(Opens.map (ComplexPoints.analyticMap i hi)).IsContinuous
      (Opens.grothendieckTopology (space sP)) (Opens.grothendieckTopology (space sX))]
    (θ : ringCatSheaf sP ⟶
      ((Opens.map (ComplexPoints.analyticMap i hi)).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology (space sP)) (Opens.grothendieckTopology (space sX))).obj
        (ringCatSheaf sX))
    [(SheafOfModules.pushforward.{0} θ).IsRightAdjoint]
    (e : (analytifyModule sP).obj ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≅
      (SheafOfModules.pushforward.{0} θ).obj
        ((analytifyModule sX).obj (SheafOfModules.unit X.ringCatSheaf)))
    (he : e.hom.val.app (op ((Opens.map (toSchemeHom sP)).obj ⊤))
        ((analytifyModuleUnit sP ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit X.ringCatSheaf))).val.app (op ⊤)
          (1 : X.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ ⊤)))) =
      (analytifyModuleUnit sX (SheafOfModules.unit X.ringCatSheaf)).val.app (op (i ⁻¹ᵁ ⊤))
        (1 : X.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ ⊤)))) :
    Epi (SheafOfModules.unitToPushforwardObjUnit θ) := by
  let u := AlgebraicGeometry.ClosedImmersionCoherentImage.unitToPushforwardUnit i
  have hu : Epi u := AlgebraicGeometry.ClosedImmersionCoherentImage.epi_unitToPushforwardUnit i
  let c := (analytifyUnitIso sP).inv ≫ (analytifyModule sP).map u ≫ e.hom ≫
    (SheafOfModules.pushforward.{0} θ).map (analytifyUnitIso sX).hom
  have hc : Epi c := by
    haveI : (analytifyModule sP).IsLeftAdjoint :=
      (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sP)).isLeftAdjoint
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) <|
      epi_comp' (@Functor.map_epi _ _ _ _ (analytifyModule sP) _ _ _ u hu) <|
      epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom e))
        (@IsIso.epi_of_iso _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _
          (SheafOfModules.pushforward.{0} θ) _ (Iso.isIso_hom _)))
  suffices hceq : c = SheafOfModules.unitToPushforwardObjUnit θ by rwa [← hceq]
  apply hom_ext_unit
  let adjP := SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sP)
  -- the inverse of `𝒪_P^an ≅ 𝒪_{P^an}` sends `1` to the analytification of `1`
  have s1 : (analytifyUnitIso sP).inv.val.app (op ⊤) (1 : (ringCatSheaf sP).obj.obj (op ⊤)) =
      (analytifyModuleUnit sP (SheafOfModules.unit P.ringCatSheaf)).val.app (op ⊤)
        (1 : P.ringCatSheaf.obj.obj (op ⊤)) := by
    rw [← analytifyUnitIso_hom_unit_one sP]
    exact congrArg (fun g => g.val.app (op ⊤) ((analytifyModuleUnit sP
      (SheafOfModules.unit P.ringCatSheaf)).val.app (op ⊤) (1 : P.ringCatSheaf.obj.obj (op ⊤))))
      (analytifyUnitIso sP).hom_inv_id
  -- naturality of the unit along `u`
  have s2 : ((analytifyModule sP).map u).val.app (op ⊤)
      ((analytifyModuleUnit sP (SheafOfModules.unit P.ringCatSheaf)).val.app (op ⊤)
        (1 : P.ringCatSheaf.obj.obj (op ⊤))) =
      (analytifyModuleUnit sP ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit X.ringCatSheaf))).val.app (op ⊤)
        (1 : X.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ ⊤))) := by
    refine (congrArg (fun g => g.val.app (op ⊤) (1 : P.ringCatSheaf.obj.obj (op ⊤)))
      (adjP.unit.naturality u)).symm.trans ?_
    have hu1 : u.val.app (op ⊤) (1 : P.ringCatSheaf.obj.obj (op ⊤)) =
        (1 : X.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ ⊤))) :=
      (SheafOfModules.unitToPushforwardObjUnit_val_app_apply _ _).trans (map_one (i.app ⊤).hom)
    change (analytifyModuleUnit sP ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf))).val.app (op ⊤) (u.val.app (op ⊤)
        (1 : P.ringCatSheaf.obj.obj (op ⊤))) = _
    rw [hu1]
  change (analytifyUnitIso sX).hom.val.app _ (e.hom.val.app _ (((analytifyModule sP).map u).val.app
    _ ((analytifyUnitIso sP).inv.val.app (op ⊤) (1 : (ringCatSheaf sP).obj.obj (op ⊤))))) =
      θ.hom.app (op ⊤) (1 : (ringCatSheaf sP).obj.obj (op ⊤))
  rw [s1, s2]
  have he' : (e.hom.val.app (op ⊤)) ((analytifyModuleUnit sP ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf))).val.app (op ⊤)
        (1 : X.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ ⊤)))) =
      (analytifyModuleUnit sX (SheafOfModules.unit X.ringCatSheaf)).val.app (op ⊤)
        (1 : X.ringCatSheaf.obj.obj (op ⊤)) := he
  refine (congrArg _ he').trans ?_
  exact (analytifyUnitIso_hom_unit_one sX).trans (map_one (θ.hom.app (op ⊤)).hom).symm

/-! ### Surjectivity -/

section Surjective

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [QuasiCompact sX]

/-- **Every analytic line bundle is the analytification of a coherent module.** -/
private theorem exists_isCoherent_analytify_iso (hX : IsProjective sX) [IsLocallyNoetherian X]
    (M : SheafOfModules.{0} (ringCatSheaf sX))
    (hM : SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2 M) :
    ∃ L : X.Modules, Stacks.SheafOfModules.IsCoherent L ∧
      Nonempty ((analytifyModule sX).obj L ≅ M) := by
  obtain ⟨N, i, hi, his⟩ := exists_isClosedImmersion_projectiveSpace sX hX
  haveI := hi
  haveI : IsProper (projToSpecCoeff ℂ N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ N
  haveI : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading ℂ N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff ℂ N)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h5⟩ := analytification_stalks sX
  obtain ⟨hemb, -, θ, hθ, hpush⟩ := h5 (projToSpecCoeff ℂ N) i his
  haveI : (Opens.map (ComplexPoints.analyticMap i his)).IsContinuous
      (Opens.grothendieckTopology (space (projToSpecCoeff ℂ N)))
      (Opens.grothendieckTopology (space sX)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
      (coverPreserving_opens_map _)
  haveI : (PresheafOfModules.pushforward.{0} θ.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  haveI : (SheafOfModules.pushforward.{0} θ).IsRightAdjoint :=
    (SheafOfModules.PullbackConstruction.adjunction.{0} θ).isRightAdjoint
  obtain ⟨e₀, he₀, -⟩ := hpush (SheafOfModules.unit X.ringCatSheaf)
  haveI := epi_unitToPushforwardObjUnit_of_isClosedImmersion sX _ i his θ e₀
    (he₀ ⊤ (1 : X.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ ⊤))))
  have hls := isLocallySurjectiveOnSections_of_epi (ComplexPoints.analyticMap i his) θ
  have hf : Topology.IsClosedEmbedding (ComplexPoints.analyticMap i his) := hemb
  -- the direct image of `M` is coherent
  have hQ : IsCoherentModule ((SheafOfModules.pushforward.{0} θ).obj
      (SheafOfModules.unit (ringCatSheaf sX))) :=
    MMP.Analytic.CoherentAnalytic.isCoherentModule_of_iso'
      ((SheafOfModules.pushforward.{0} θ).mapIso (analytifyUnitIso sX).symm ≪≫ e₀.symm)
      (isCoherentModule_analytify _
        (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
          (AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_unit i)))
  have hS := isCoherentModule_pushforward_of_locallyTrivial hf hQ M
    (exists_over_iso_unit_of_isInvertible sX M hM)
  -- it is algebraic on projective space
  obtain ⟨G, hG, ⟨eG⟩⟩ := exists_isCoherent_analytify_iso_projectiveSpace N _ hS
  haveI := AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent hG
  refine ⟨(Scheme.Modules.pullback i).obj G,
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (AlgebraicGeometry.isCoherent_pullback i G), ?_⟩
  -- `(i^* G)^an ≅ θ^* G^an ≅ θ^* θ_* M ≅ M`
  obtain ⟨eP⟩ := nonempty_analytifyModule_pullback_iso _ sX i his θ hθ G
  haveI := isIso_pullbackPushforwardAdjunction_counit_app hf.isInducing hls M
  exact ⟨eP ≪≫ (SheafOfModules.pullback.{0} θ).mapIso eG ≪≫
    asIso ((SheafOfModules.pullbackPushforwardAdjunction.{0} θ).counit.app M)⟩

/-- **Analytification is surjective on Picard groups.** If `L^an ≅ M` and `L'^an ≅ M⁻¹` with `L`,
`L'` coherent, then `(L ⊗ L')^an ≅ 𝒪_{X^an}`, so `L ⊗ L' ≅ 𝒪_X` and `L` is invertible. -/
private theorem surjective_picardHom (hX : IsProjective sX) [IsLocallyNoetherian X] :
    Function.Surjective (picardHom sX) := by
  intro y
  obtain ⟨M, hM, rfl⟩ := Stacks.SheafPicardGroup.exists_classOf _ _ y
  let M' := AlgebraicGeometry.SheafOfModules.tensorInv _ _ M
  have hM' : SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
      (structureSheaf sX).obj (ringCatSheaf sX).2 M' :=
    AlgebraicGeometry.SheafOfModules.isInvertible_tensorInv _ _ M
  obtain ⟨L, hLc, ⟨eL⟩⟩ := exists_isCoherent_analytify_iso sX hX M hM
  obtain ⟨L', hL'c, ⟨eL'⟩⟩ := exists_isCoherent_analytify_iso sX hX M' hM'
  -- `L ⊗ L' ≅ 𝒪_X`
  have hT := isCoherent_sheafTensor hLc hL'c
  obtain ⟨t⟩ := nonempty_analytify_sheafTensor_iso sX L L'
  have eMM : ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj M).obj M' ≅
      SheafOfModules.unit (ringCatSheaf sX) :=
    (AlgebraicGeometry.SheafOfModules.tensorIso _ _ M M').symm ≪≫
      AlgebraicGeometry.SheafOfModules.tensorInvMulIso _ _ M ≪≫
      AlgebraicGeometry.SheafOfModules.unitIso _ _
  let φ : (analytifyModule sX).obj (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj
      L') ≅ SheafOfModules.unit (ringCatSheaf sX) :=
    t ≪≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).mapIso eL).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf sX)).obj M).mapIso eL' ≪≫ eMM
  obtain ⟨e⟩ := nonempty_iso_unit_of_analytify sX hX _ hT φ
  have hL1 : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).2 ⟨L', ⟨e⟩⟩
  haveI hL : Stacks.Ample.IsInvertibleModule X L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1 hL1
  refine ⟨Stacks.SheafPicardGroup.schemeClassOf X L, (picardFun_classOf sX L).trans ?_⟩
  exact (@Stacks.SheafPicardGroup.classOf_eq_classOf_iff _ _ _ _ _ _ _ _ _
    (isInvertible_analytify sX L hL) hM).2 ⟨eL⟩

end Surjective

/-! ### GAGA for Picard groups -/

/-- **GAGA for Picard groups.** For a projective scheme `X` over `ℂ` (possibly nonreduced),
analytification of invertible `𝒪_X`-modules induces an isomorphism of Picard groups
`Pic X ≃* Pic X^an`, `[L] ↦ [L^an]`, compatible with restriction to closed subschemes. -/
@[mmp "thm_mmp_gaga_projective_picard"]
public theorem exists_mulEquiv_picardGroup_analytification_of_isProjective {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) :
    ∃ (hinv : ∀ L : X.Modules, Stacks.Ample.IsInvertibleModule X L →
        SheafOfModules.IsInvertible (J := Opens.grothendieckTopology (space sX))
          (structureSheaf sX).obj (ringCatSheaf sX).2 ((analytifyModule sX).obj L))
      (e : Stacks.SheafPicardGroup.schemePicardGroup X ≃*
        Stacks.SheafPicardGroup.PicardGroup (J := Opens.grothendieckTopology (space sX))
          (structureSheaf sX).obj (ringCatSheaf sX).2),
      (∀ (L : X.Modules) [hL : Stacks.Ample.IsInvertibleModule X L],
        e (Stacks.SheafPicardGroup.schemeClassOf X L) =
          @Stacks.SheafPicardGroup.classOf _ _ (Opens.grothendieckTopology (space sX))
            (structureSheaf sX).obj (ringCatSheaf sX).2 _ _ ((analytifyModule sX).obj L)
            (hinv L hL)) ∧
      ∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (i : Z ⟶ X) [IsClosedImmersion i]
        (hi : i ≫ sX = sZ),
        haveI : (Opens.map (ComplexPoints.analyticMap i hi)).IsContinuous
            (Opens.grothendieckTopology (space sX)) (Opens.grothendieckTopology (space sZ)) :=
          Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
            (coverPreserving_opens_map _)
        ∀ θ : ringCatSheaf sX ⟶
            ((Opens.map (ComplexPoints.analyticMap i hi)).sheafPushforwardContinuous
              RingCat.{0} (Opens.grothendieckTopology (space sX))
              (Opens.grothendieckTopology (space sZ))).obj (ringCatSheaf sZ),
          (∀ (V : X.Opens) (f : Γ(X, V)),
            θ.hom.app (op ((Opens.map (toSchemeHom sX)).obj V))
                ((ringCatSheafHom sX).hom.app (op V) f) =
              (ringCatSheafHom sZ).hom.app (op (i ⁻¹ᵁ V)) (i.app V f)) →
          haveI : (PresheafOfModules.pushforward.{0} θ.hom).IsRightAdjoint :=
            PresheafOfModules.instIsRightAdjointPushforward _
          haveI : (SheafOfModules.pushforward.{0} θ).IsRightAdjoint :=
            (SheafOfModules.PullbackConstruction.adjunction.{0} θ).isRightAdjoint
          ∀ L : X.Modules,
            Nonempty ((analytifyModule sZ).obj ((Scheme.Modules.pullback i).obj L) ≅
              (SheafOfModules.pullback.{0} θ).obj ((analytifyModule sX).obj L)) := by
  obtain ⟨N, i, hi, his⟩ := exists_isClosedImmersion_projectiveSpace sX hX
  haveI := hi
  haveI : IsProper (projToSpecCoeff ℂ N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ N
  haveI : LocallyOfFiniteType sX := his ▸ inferInstance
  haveI : QuasiCompact sX := his ▸ inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine ⟨isInvertible_analytify sX,
    MulEquiv.ofBijective (picardHom sX) ⟨injective_picardHom sX hX, surjective_picardHom sX hX⟩,
    fun L hL => picardFun_classOf sX L, ?_⟩
  intro Z sZ j _ hj
  exact nonempty_analytifyModule_pullback_iso sX sZ j hj

/-! ### Connected components and snc restriction -/

/-- An open immersion onto a connected component of a smooth proper `ℂ`-scheme is a variety. -/
theorem isVariety_of_range_eq_connectedComponent {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX] (hsm : Mori.IsSmoothScheme sX) (j : Y ⟶ X)
    [IsOpenImmersion j] {x : X} (hj : Set.range j.base = connectedComponent x) :
    Mori.IsVariety ℂ (j ≫ sX) := by
  haveI : Smooth sX := (Mori.isSmoothScheme_iff sX).1 hsm
  haveI : CompactSpace X := (quasiCompact_iff_compactSpace sX).1 inferInstance
  have hemb : Topology.IsClosedEmbedding j.base :=
    ⟨j.isOpenEmbedding.isEmbedding, hj ▸ isClosed_connectedComponent⟩
  haveI : CompactSpace Y := hemb.compactSpace
  haveI : ConnectedSpace Y := by
    rw [connectedSpace_iff_univ]
    refine ⟨?_, ?_⟩
    · obtain ⟨y, -⟩ : x ∈ Set.range j.base := hj ▸ mem_connectedComponent
      exact ⟨y, trivial⟩
    · rw [← j.isOpenEmbedding.isInducing.isPreconnected_image, Set.image_univ, hj]
      exact isPreconnected_connectedComponent
  haveI : IsIntegral Y := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (j ≫ sX)
  exact (Mori.isVariety_iff ℂ (j ≫ sX)).2 ⟨inferInstance, inferInstance, inferInstance,
    (quasiCompact_iff_compactSpace _).2 inferInstance⟩

/-- The restriction of an snc divisor along an open immersion is snc. -/
theorem isSNC_comapDomain {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (E : Mori.Divisor X) (hE : E.IsSNC sX) (j : Y ⟶ X)
    [IsOpenImmersion j] :
    Mori.DivisorWithCoeffs.IsSNC (j ≫ sX) (Finsupp.comapDomain
      (OpenWeilRestriction.primeDivisorMap j) E
      (OpenWeilRestriction.primeDivisorMap_injective j).injOn) := by
  refine ⟨fun P hP => ?_, fun y =>
    (Threefold.Mori.OpenRestriction.sncStalk_restrict_iff j E y).2 (hE.2 (j y))⟩
  have hP' : OpenWeilRestriction.primeDivisorMap j P ∈ E.support := by
    rwa [Finsupp.mem_support_iff] at hP ⊢
  have hsm := hE.1 _ hP'
  have : LocallyOfFinitePresentation
      ((OpenWeilRestriction.primeDivisorMap j P).idealSheaf.subschemeι ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [Mori.IsSmoothScheme, Mori.smoothLocus_eq_smoothLocus] at hsm
  refine (Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff j sX _ P.idealSheaf
    (Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap j P)).2 fun z _ => ?_
  rw [hsm]
  trivial

end MMP.Analytic

end
