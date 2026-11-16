module

public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Divisor.LineBundleFamiliesCountable
public import MMP.AlgebraicGeometry.Resolution.DivisorTupleTransform
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
public import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Line-bundle families, reflexive sheaves, differentials, nef volume and restriction lifts

This file collects five independent results used in the MMP: finite-type parameter families
for line bundles on the closed fibres of an adapted family, the Hartogs characterisation of
reflexive coherent sheaves on a normal variety, the splitting of differentials at a horizontal
codimension-one point, the growth of `(tL + qM)^d` in a nontrivial nef direction, and the
lifting of order-one transformations from a transverse smooth divisor. Each topic is in its own
section below.

## Main results

* `MMP.Fourfold.exists_countable_families_isInvertible_pointFibre_iso`
* `MMP.Foundations.isReflexive_iff_isTorsionFree_and_bijective_restrict`
* `MMP.Mori.PrimeDivisor.exact_mapBaseChange_map_localRing`
* `MMP.Mori.tendsto_sheafCombinationIntersectionNumber_atTop_of_isNef`
* `MMP.Resolution.OrderedDivisorTuple.exists_isPushforward_transform_restrict`
-/

universe u v

/-!
## Finite-type parameter families for the line bundles on the closed fibres over an adapted open

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`) and `T° ⊆ T` a
`π`-adapted open (`MMP.Fourfold.IsAdaptedOpen`), with family `𝓕 = Ỹ ×_Y T° ⟶ T°`
(`MMP.Fourfold.adaptedFamily`). There are countably many `T°`-schemes of finite type
`M α ⟶ T°` with invertible sheaves `𝓤 α` on `𝓕 ×_{T°} M α` such that for every complex point
`t` of `T°` and every invertible sheaf `𝓛` on the scheme fibre `F_t`
(`MMP.Fourfold.pointFibre`), some `α` and some complex point `μ` of `M α` over `t` have
`𝓤 α |_{F_t × {μ}} ≅ 𝓛`.

### Main results

* `MMP.Fourfold.exists_countable_families_isInvertible_pointFibre_iso`.

### Implementation notes

* The closed points of the finite-type complex curve `T°` are its complex points, so the closed
  points `t ∈ T°` are the `ℂ`-points `t : Spec ℂ ⟶ T°`, as for `MMP.Fourfold.pointFibre`. A point
  `μ ∈ M α` over `t` is likewise a morphism `μ : Spec ℂ ⟶ M α` with `μ ≫ g α = t`.
* The sheet `F_t × {μ}` is `F_t`, mapped into `𝓕 ×_{T°} M α` by the morphism whose components
  are the inclusion `F_t ⟶ 𝓕` (`MMP.Fourfold.pointFibreToFamily`) and `F_t ⟶ Spec ℂ ⟶ M α`
  through `μ`; the restriction is the module pull-back along it.
* "Finite type" is `LocallyOfFiniteType` together with `QuasiCompact`; a line bundle is an
  invertible sheaf of modules, `SheafOfModules.IsInvertible`, as in
  `MMP.Fourfold.IsPuncturedIndependent`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.Internal.RelativeLineBundleParameterSpaces

open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private def modulePullbackIso {X Y : Scheme.{0}} (f : X ⟶ Y) (F : Y.Modules) :
    (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj F ≅
      (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- If a `K`-point of a `K`-scheme `X` factors through `Spec κ(x)` along `φ : κ(x) ⟶ K`, then
`Spec φ` is an isomorphism: `K ⟶ κ(x) ⟶ K` is the identity, so `φ` is a surjective, hence
bijective, map of fields. -/
private theorem isIso_SpecMap_of_comp_eq_id {K : Type} [Field K] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of K)) {x : X} (φ : X.residueField x ⟶ .of K)
    (h : Spec.map φ ≫ X.fromSpecResidueField x ≫ sX = 𝟙 _) : IsIso (Spec.map φ) := by
  obtain ⟨a, ha⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ sX)
  have hid : a ≫ φ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, ha, h, Spec.map_id])
  have hbij : Function.Bijective φ.hom := by
    refine ⟨φ.hom.injective, fun y => ⟨a.hom y, ?_⟩⟩
    change (a ≫ φ).hom y = y
    rw [hid]; rfl
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr hbij
  infer_instance

/-- Pull-backs along a section transport an identification: if `ψ ≫ χ = 𝟙` and
`ℓ^* U ≅ χ^* L`, then `(ψ ≫ ℓ)^* U ≅ L`. -/
private def pullbackCompIsoOfRetraction {A B C : Scheme.{0}} {ψ : A ⟶ B} {χ : B ⟶ A}
    (h : ψ ≫ χ = 𝟙 A) (ℓ : B ⟶ C) {U : C.Modules} {L : A.Modules}
    (e : (Scheme.Modules.pullback ℓ).obj U ≅ (Scheme.Modules.pullback χ).obj L) :
    (Scheme.Modules.pullback (ψ ≫ ℓ)).obj U ≅ L :=
  ((Scheme.Modules.pullbackComp ψ ℓ).app U).symm ≪≫ (Scheme.Modules.pullback ψ).mapIso e ≪≫
    (Scheme.Modules.pullbackComp ψ χ).app L ≪≫
    eqToIso (congrArg (fun h => (Scheme.Modules.pullback h).obj L) h) ≪≫
    (Scheme.Modules.pullbackId _).app L

end MMP.Fourfold.Internal.RelativeLineBundleParameterSpaces

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

open MMP.Fourfold.Internal.RelativeLineBundleParameterSpaces in
/-- **Finite-type parameter families for all line bundles on the closed fibres over an adapted
open.** For a local setting `(Y, Θ, T, π)` and a `π`-adapted open `T°` with family
`𝓕 = Ỹ ×_Y T° ⟶ T°`, there are a countable index type `ι`, finite-type `T°`-schemes
`g α : M α ⟶ T°` and invertible sheaves `𝓤 α` on `𝓕 ×_{T°} M α` such that for every complex point
`t` of `T°` and every invertible sheaf `𝓛` on `F_t`, some `α` and some complex point `μ` of `M α`
over `t` have the restriction of `𝓤 α` to `F_t × {μ}` isomorphic to `𝓛`. -/
@[mmp "lem_mmp_foundation_oai_relative_line_bundle_parameter_spaces"]
public theorem exists_countable_families_isInvertible_pointFibre_iso
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y) (T : IrreducibleCloseds Y) (π : Yt ⟶ Y)
    (hS : IsLocalSetting sY Θ T π)
    (To : (curveScheme T).Opens) (hTo : IsAdaptedOpen sY π To) :
    ∃ (ι : Type) (_ : Countable ι) (M : ι → Scheme.{0}) (g : ∀ α, M α ⟶ (To : Scheme.{0}))
      (_ : ∀ α, LocallyOfFiniteType (g α)) (_ : ∀ α, QuasiCompact (g α))
      (U : ∀ α, (pullback (pullback.snd π (To.ι ≫ curveι T)) (g α)).Modules)
      (_ : ∀ α, SheafOfModules.IsInvertible
        (pullback (pullback.snd π (To.ι ≫ curveι T)) (g α)).presheaf
        (pullback (pullback.snd π (To.ι ≫ curveι T)) (g α)).ringCatSheaf.2 (U α)),
      ∀ (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) (L : (pointFibre sY π To t).Modules),
        SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2 L →
        ∃ (α : ι) (μ : Spec (.of ℂ) ⟶ M α) (hμ : μ ≫ g α = t.hom),
          Nonempty ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To t)
            (pointFibreSnd sY π To t ≫ μ)
            (by rw [Category.assoc, hμ]; exact pullback.lift_snd _ _ _))).obj (U α) ≅ L) := by
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hS.isProjectiveVariety
  have : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  set f := pullback.snd π (To.ι ≫ curveι T) with hf
  have : Flat f := hTo.flat
  have hfp : IsProjective f := hTo.isProjectiveMorphism.isProjective
  have : IsProper f := isProper_of_isProjectiveMorphism f hTo.isProjectiveMorphism
  set sS : (To : Scheme.{0}) ⟶ Spec (.of ℂ) := To.ι ≫ curveι T ≫ sY with hsS
  have : LocallyOfFiniteType sS := by rw [hsS]; infer_instance
  have : QuasiCompact sS := by rw [hsS]; infer_instance
  obtain ⟨H, hH, hHva⟩ := hfp.exists_isRelativelyVeryAmple
  have hHa : IsRelativelyAmple f H :=
    IsRelativelyAmple.of_stacks _ _
      (Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f H inferInstance hHva)
  obtain ⟨ι, hι, M, g, hg1, hg2, U, hU, hcov⟩ :=
    MMP.exists_countable_families_isInvertibleModule_fiber_iso f hfp sS H hHa
  refine ⟨ι, hι, M, g, hg1, hg2, U, hU, fun t L hL => ?_⟩
  -- `t` factors through `Spec κ(s)` for its image `s`, along an isomorphism.
  set s : (To : Scheme.{0}) := t.hom (IsLocalRing.closedPoint ℂ) with hs_def
  set φ := Scheme.descResidueField (Scheme.stalkClosedPointTo t.hom) with hφ_def
  have hc : Spec.map φ ≫ (To : Scheme.{0}).fromSpecResidueField s = t.hom :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ _ t.hom
  have : IsIso (Spec.map φ) := isIso_SpecMap_of_comp_eq_id sS φ
    (by rw [← Category.assoc, hc]; exact t.hom_comp_structure)
  have hc' : (To : Scheme.{0}).fromSpecResidueField s = inv (Spec.map φ) ≫ t.hom :=
    ((IsIso.inv_comp_eq _).mpr hc.symm).symm
  -- `s` is a closed point.
  have : JacobsonSpace (To : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace sS
  have : LocallyOfFiniteType t.hom := by
    have : LocallyOfFiniteType (t.hom ≫ sS) := by
      rw [show t.hom ≫ sS = 𝟙 _ from t.hom_comp_structure]; infer_instance
    exact locallyOfFiniteType_of_comp t.hom sS
  have hs : IsClosed ({s} : Set (To : Scheme.{0})) :=
    isClosed_singleton_iff_locallyOfFiniteType.mpr (by rw [hc']; infer_instance)
  -- The comparison `𝓕_s ⟶ F_t` and its section `F_t ⟶ 𝓕_s`.
  let χ : f.fiber s ⟶ pointFibre sY π To t :=
    pullback.lift (f.fiberι s ≫ pullback.fst π _) (f.fiberToSpecResidueField s ≫ inv (Spec.map φ))
      (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, ← hf, Scheme.Hom.fiber_fac,
          Category.assoc, hc']
        simp only [Category.assoc])
  let ψ : pointFibre sY π To t ⟶ f.fiber s :=
    pullback.lift (pointFibreToFamily sY π To t) (pointFibreSnd sY π To t ≫ Spec.map φ)
      (by
        rw [Category.assoc, hc]
        exact pullback.lift_snd _ _ _)
  have hψ₁ : ψ ≫ f.fiberι s = pointFibreToFamily sY π To t := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ f.fiberToSpecResidueField s = pointFibreSnd sY π To t ≫ Spec.map φ :=
    pullback.lift_snd _ _ _
  have hχ₁ : χ ≫ pointFibreFst sY π To t = f.fiberι s ≫ pullback.fst π _ :=
    pullback.lift_fst _ _ _
  have hχ₂ : χ ≫ pointFibreSnd sY π To t = f.fiberToSpecResidueField s ≫ inv (Spec.map φ) :=
    pullback.lift_snd _ _ _
  have hψχ : ψ ≫ χ = 𝟙 _ := by
    apply pullback.hom_ext
    · change (ψ ≫ χ) ≫ pointFibreFst sY π To t = 𝟙 _ ≫ pointFibreFst sY π To t
      rw [Category.assoc, hχ₁, reassoc_of% hψ₁, Category.id_comp]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    · change (ψ ≫ χ) ≫ pointFibreSnd sY π To t = 𝟙 _ ≫ pointFibreSnd sY π To t
      rw [Category.assoc, hχ₂, reassoc_of% hψ₂]
      simp
  have : Stacks.Ample.IsInvertibleModule (pointFibre sY π To t) L := hL
  obtain ⟨i, μ', hμ', ⟨e⟩⟩ := hcov s hs ((Scheme.Modules.pullback χ).obj L) inferInstance
  refine ⟨i, Spec.map φ ≫ μ', by rw [Category.assoc, hμ', hc], ⟨?_⟩⟩
  set ℓ := pullback.lift (f.fiberι s) (f.fiberToSpecResidueField s ≫ μ')
    (by rw [Category.assoc, hμ', Scheme.Hom.fiber_fac]) with hℓ
  have hψℓ : ψ ≫ ℓ = pullback.lift (pointFibreToFamily sY π To t)
      (pointFibreSnd sY π To t ≫ Spec.map φ ≫ μ')
      (by rw [Category.assoc, Category.assoc, hμ', hc]; exact pullback.lift_snd _ _ _) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hψ₁, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, reassoc_of% hψ₂, pullback.lift_snd]
  exact eqToIso (congrArg (fun h => (Scheme.Modules.pullback h).obj (U i)) hψℓ.symm) ≪≫
    pullbackCompIsoOfRetraction hψχ ℓ ((modulePullbackIso ℓ (U i)).symm ≪≫ e)

end MMP.Fourfold

end

/-!
## Reflexive sheaves on a normal variety: torsion-freeness and Hartogs extension

Let `X` be a normal variety over a field `k` and `𝒢` a coherent `𝒪_X`-module. Then `𝒢` is
reflexive, i.e. the canonical evaluation map `𝒢 ⟶ 𝒢^∨∨` into the double dual
(`𝒢^∨ = 𝓗om(𝒢, 𝒪_X)`) is an isomorphism, if and only if `𝒢` is torsion free and its sections
extend uniquely across closed subsets of codimension at least two: for every pair of opens
`V ⊆ U` of `X` such that the closed subset `U \ V` of `U` has codimension `≥ 2` in `U`, the
restriction map `𝒢(U) → 𝒢(V)` is bijective.

### Main results

* `MMP.Foundations.isReflexive_iff_isTorsionFree_and_bijective_restrict`: the equivalence.

### Implementation notes

A closed subset `W` of an open `U` is recorded through its open complement `V = U \ W`, so that
the closed subsets `W ⊆ U` of codimension `≥ 2` correspond to the opens `V ≤ U` with
`2 ≤ MMP.Mori.closedsCodimension (U.ι ⁻¹ᵁ V).compl`, the codimension being computed in the
space `U`. Codimension of a closed set is the infimum of the codimensions of the irreducible
closed subsets it contains, so `W = ∅` (that is, `V = U`) has codimension `⊤`.
Reflexivity is `Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive`, the canonical map being
`Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual`; torsion-freeness is
`Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree` (every local section whose germs are
all torsion vanishes).

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [Stacks Project, Tags 0AVR, 0AY2](https://stacks.math.columbia.edu/tag/0AY2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveEquivalence

namespace MMP.Foundations.Internal.ReflexiveSheafHartogs

variable {X : Scheme.{u}}

/-- The codimension of the closure of a point is the same in an open subscheme as in `X`:
both are the Krull dimension of the local ring at the point. -/
private lemma codimension_closureSingleton_opens (U : X.Opens) (x : U.toScheme) :
    codimension (IrreducibleCloseds.closureSingleton x) =
      codimension (IrreducibleCloseds.closureSingleton (U.ι x)) := by
  have h : ringKrullDim (U.toScheme.presheaf.stalk x) =
      ringKrullDim (X.presheaf.stalk (U.ι x)) :=
    ringKrullDim_eq_of_ringEquiv (U.stalkIso x).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
    coheight_eq_codimension_closureSingleton,
    coheight_eq_codimension_closureSingleton] at h
  exact_mod_cast h

/-- A closed subset of an open `U` of codimension at least two in `U` is cut out on `U` by
the complement of an open of `X` off which every point has codimension at least two. -/
private lemma exists_inf_eq_of_two_le_closedsCodimension [NoetherianSpace X]
    (U V : X.Opens) (hVU : V ≤ U)
    (h : 2 ≤ MMP.Mori.closedsCodimension (U.ι ⁻¹ᵁ V).compl) :
    ∃ V' : X.Opens, V' ⊓ U = V ∧
      ∀ x : X, x ∉ V' → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  set S : Set X := (U : Set X) \ V with hS
  refine ⟨⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩, ?_, ?_⟩
  · have hcl : closure S ⊆ (V : Set X)ᶜ :=
      closure_minimal (fun y hy => hy.2) V.isOpen.isClosed_compl
    ext x
    simp only [Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_compl_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨hx, hxU⟩
      by_contra hxV
      exact hx (subset_closure ⟨hxU, hxV⟩)
    · intro hxV
      exact ⟨fun hx => hcl hx hxV, hVU hxV⟩
  · intro x hx
    simp only [Opens.mem_mk, Set.mem_compl_iff, not_not] at hx
    set C : Set U.toScheme := (((U.ι ⁻¹ᵁ V).compl : Closeds U.toScheme) : Set U.toScheme)
      with hC
    have : NoetherianSpace U.toScheme := inferInstanceAs (NoetherianSpace (U : Set X))
    have hCc : IsClosed C := ((U.ι ⁻¹ᵁ V).compl).isClosed
    obtain ⟨T, hTfin, hTcl, hTirr, hCT⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible hCc
    have hSC : S = (fun y : U.toScheme => U.ι y) '' C := by
      ext y
      constructor
      · rintro ⟨hyU, hyV⟩
        exact ⟨⟨y, hyU⟩, hyV, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz⟩
    rw [hSC, hCT, Set.image_sUnion, Set.sUnion_image,
      hTfin.closure_biUnion] at hx
    obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨η, hη⟩ := QuasiSober.sober (hTirr t htT) (hTcl t htT)
    have hxη : closure {x} ⊆ closure {U.ι η} := by
      refine closure_minimal ?_ isClosed_closure
      rw [Set.singleton_subset_iff]
      refine closure_minimal ?_ isClosed_closure hxt
      rw [← hη.def]
      exact (image_closure_subset_closure_image U.ι.continuous).trans
        (by rw [Set.image_singleton])
    have hηC : closure {η} ⊆ C := by
      rw [hη.def, hCT]
      exact Set.subset_sUnion_of_mem htT
    have h2 : (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton (X := U.toScheme) η) :=
      MMP.Mori.le_closedsCodimension_iff.mp h _ hηC
    rw [codimension_closureSingleton_opens] at h2
    exact h2.trans (Order.coheight_anti hxη)

/-- Conversely, an open `U₀` of `X` off which every point has codimension at least two meets
every open `W` in an open whose complement in `W` has codimension at least two. -/
private lemma two_le_closedsCodimension_inf (U₀ W : X.Opens)
    (h : ∀ x : X, x ∉ U₀ → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    2 ≤ MMP.Mori.closedsCodimension (W.ι ⁻¹ᵁ (U₀ ⊓ W)).compl := by
  rw [MMP.Mori.le_closedsCodimension_iff]
  intro T hT
  obtain ⟨η, hη⟩ := QuasiSober.sober T.isIrreducible T.isClosed
  have hTη : T = IrreducibleCloseds.closureSingleton η := by
    ext1
    exact hη.def.symm
  have hηT : η ∈ (T : Set W.toScheme) := hη.mem
  have hηU : W.ι η ∉ U₀ := fun h' => hT hηT ⟨h', η.2⟩
  rw [hTη, codimension_closureSingleton_opens]
  exact h _ hηU

/-- The unit `ℋ ⟶ j_*(ℋ|_V)` of the restriction to an open `V` is an isomorphism as soon as
restriction `Γ(W, ℋ) → Γ(V ⊓ W, ℋ)` is bijective for every open `W`. -/
private lemma isIso_unit_of_bijective (V : X.Opens) (H : X.Modules)
    (h : ∀ W : X.Opens,
      Function.Bijective (H.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H) := by
  have hL : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app H) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    have key : ∀ (A : X.Opens) (hA : A ≤ W), A = V ⊓ W →
        Function.Bijective (H.presheaf.map (homOfLE hA).op) := by
      rintro A hA rfl
      exact h W
    have himg : V.ι ''ᵁ V.ι ⁻¹ᵁ W = V ⊓ W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (key _ (V.ι.image_preimage_le W) himg)
  have hcomp : (Scheme.Modules.restrictAdjunction V.ι).unit.app H ≫
      (Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app H) =
      (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ H
  rw [← hcomp]
  infer_instance

/-- The set of points having an open neighbourhood on which every stalk of `F` is free. -/
private def freeLocus (F : X.Modules) : X.Opens where
  carrier := {x | ∃ W : X.Opens, x ∈ W ∧
    ∀ y : X, y ∈ W → Module.Free (X.presheaf.stalk y) (F.presheaf.stalk y)}
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, hxW, hW⟩
    exact ⟨W, fun y hy => ⟨W, hy, hW⟩, W.isOpen, hxW⟩

/-- A coherent module with free stalk at `x` is free on a neighbourhood of `x`. -/
private lemma mem_freeLocus_of_free_stalk [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (x : X)
    (hfree : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    x ∈ freeLocus F := by
  have : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  let b := Module.Free.chooseBasis (X.presheaf.stalk x) (F.presheaf.stalk x)
  have : Finite (Module.Free.ChooseBasisIndex (X.presheaf.stalk x) (F.presheaf.stalk x)) :=
    Module.Finite.finite_basis b
  obtain ⟨W, hxW, ⟨e⟩⟩ := Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis F x b
  refine ⟨W, hxW, fun y hy => ?_⟩
  let G : (F.over W).GeneratingSections :=
    { I := Module.Free.ChooseBasisIndex (X.presheaf.stalk x) (F.presheaf.stalk x)
      s := (F.over W).freeHomEquiv e.inv
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }
  have : IsIso G.π := by
    change IsIso ((F.over W).freeHomEquiv.symm ((F.over W).freeHomEquiv e.inv))
    rw [Equiv.symm_apply_apply]
    infer_instance
  obtain ⟨ey⟩ := Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv W F G hy
  exact Module.Free.of_equiv ey.symm

/-- On a normal integral locally Noetherian scheme, every point off the free locus of a
torsion-free coherent module has codimension at least two: at a point of codimension at most
one the local ring is regular of dimension at most one, over which a finite torsion-free module
is free. -/
private lemma two_le_codimension_of_notMem_freeLocus [IsLocallyNoetherian X] [IsIntegral X]
    [IsNormal X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (hTF : IsTorsionFree F) {x : X}
    (hx : x ∉ freeLocus F) : (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  by_contra hnot
  have hdim : ringKrullDim (X.presheaf.stalk x) ≤ (1 : WithBot ℕ∞) := by
    refine withBot_lt_two_le_one ?_
    rw [ringKrullDim_stalk_eq_coheight, coheight_eq_codimension_closureSingleton]
    exact WithBot.coe_lt_coe.mpr (lt_of_not_ge hnot)
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp
      inferInstance).2 x hdim
  have : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  have : Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    (isTorsionFree_iff_forall_stalk F).mp hTF x
  exact hx (mem_freeLocus_of_free_stalk F x
    (Module.free_of_isTorsionFree_of_ringKrullDim_le_one hdim))

/-- A coherent module is finite locally free on its free locus. -/
private lemma isFiniteLocallyFree_restrict_freeLocus [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] :
    SheafOfModules.IsFiniteLocallyFree (F.restrict (freeLocus F).ι) := by
  set U : X.Opens := freeLocus F
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : (F.restrict U.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor U.ι F
  have : _root_.SheafOfModules.IsCoherent (F.restrict U.ι) := isCoherent_restrict U F
  have h := (Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae (F.restrict U.ι)).out 2 4
  refine h.mp ⟨_root_.isFinitePresentation_of_isCoherent _, fun y => ?_⟩
  have : RingHomInvPair
      (openImmersionStalkRingEquiv U.ι y :
        U.toScheme.presheaf.stalk y →+* X.presheaf.stalk (U.ι y))
      ((openImmersionStalkRingEquiv U.ι y).symm :
        X.presheaf.stalk (U.ι y) →+* U.toScheme.presheaf.stalk y) :=
    RingHomInvPair.of_ringEquiv _
  have : RingHomInvPair
      ((openImmersionStalkRingEquiv U.ι y).symm :
        X.presheaf.stalk (U.ι y) →+* U.toScheme.presheaf.stalk y)
      (openImmersionStalkRingEquiv U.ι y :
        U.toScheme.presheaf.stalk y →+* X.presheaf.stalk (U.ι y)) :=
    RingHomInvPair.of_ringEquiv_symm _
  have : Module.Free (X.presheaf.stalk (U.ι y)) (F.presheaf.stalk (U.ι y)) :=
    y.2.elim fun _ h => h.2 _ h.1
  exact Module.Free.of_equiv (restrictStalkSemilinearEquiv U.ι F y).symm

end MMP.Foundations.Internal.ReflexiveSheafHartogs

namespace MMP.Foundations

open MMP.Foundations.Internal.ReflexiveSheafHartogs in
/-- On a normal variety `X`, a coherent `𝒪_X`-module `𝒢` is reflexive if and only if it is
torsion free and, for all opens `V ≤ U` whose complement `U \ V` has codimension at least two
in `U`, the restriction `𝒢(U) → 𝒢(V)` is bijective. -/
@[mmp "lem_mmp_foundation_reflexive_sheaf_hartogs_equivalence"]
public theorem isReflexive_iff_isTorsionFree_and_bijective_restrict (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsNormalVariety k sX)
    (G : X.Modules) [SheafOfModules.IsCoherent G] :
    IsReflexive G ↔
      IsTorsionFree G ∧
        ∀ (U V : X.Opens) (hVU : V ≤ U),
          2 ≤ MMP.Mori.closedsCodimension (U.ι ⁻¹ᵁ V).compl →
            Function.Bijective (G.presheaf.map (homOfLE hVU).op) := by
  haveI := hX.1
  haveI := hX.2
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  have htfae := isReflexive_isTorsionFree_propertyS2_extension_tfae X G
  constructor
  · intro hR
    refine ⟨isTorsionFree_of_isReflexive_of_isLocallyNoetherian G hR, fun U V hVU hcod => ?_⟩
    obtain ⟨V', hV'U, hV'⟩ := exists_inf_eq_of_two_le_closedsCodimension U V hVU hcod
    subst hV'U
    exact Stacks.AlgebraicGeometry.PushforwardRegularity.bijective_resF_inf_of_isIso_unit V'
      G (Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive V' G hR
        (two_le_depth_stalk_of_notMem_of_two_le_codimension V' hV')) U
  · rintro ⟨hTF, hH⟩
    have hcodim := fun x => two_le_codimension_of_notMem_freeLocus G hTF (x := x)
    refine (htfae.out 3 1).mp ?_
    exact ⟨freeLocus G, hcodim, isFiniteLocallyFree_restrict_freeLocus G,
      isIso_unit_of_bijective _ G fun W =>
        hH W (freeLocus G ⊓ W) inf_le_right (two_le_closedsCodimension_inf _ W hcodim)⟩

end MMP.Foundations

end

/-!
## Splitting of differentials at a horizontal codimension-one point

Let `k` be a field of characteristic zero, `Y` a normal variety over `k` of dimension `n`, and
`t₁, …, tₘ ∈ 𝒪(Y)` algebraically independent over `k`. Let `Γ` be a prime divisor of `Y` at whose
generic point `η` every nonzero polynomial in the `tᵢ` is a unit, so that the local ring
`R = 𝒪_{Y,η}` is an algebra over `K = k(t₁, …, tₘ)`, essentially of finite type (it is the local
ring of the generic fibre `Y_K` at the image of `η`). Then the transitivity sequence
`0 → R ⊗_K Ω_{K/k} → Ω_{R/k} → Ω_{R/K} → 0` is exact, the three modules are free of ranks `m`,
`n` and `n - m`, the first with basis `1 ⊗ dtᵢ`, and consequently a family
`ω₁, …, ω_{n-m}` in `Ω_{R/k}` gives a generator `dt₁ ∧ ⋯ ∧ dtₘ ∧ ω₁ ∧ ⋯ ∧ ω_{n-m}` of
`Ω^n_{R/k}` exactly when the images of the `ωⱼ` give a generator of `Ω^{n-m}_{R/K}`.

### Main results

* `MMP.Mori.PrimeDivisor.exact_mapBaseChange_map_localRing`

### Implementation notes

The field `K` is any fraction field of `k[X₁, …, Xₘ]`, and its algebra structure on `𝒪_{Y,η}` is
part of the data, pinned by sending `Xᵢ` to the germ of `tᵢ`; such a structure exists exactly when
every nonzero polynomial in the `tᵢ` is a unit at `η`, and is then unique. That `𝒪_{Y,η}` is the
local ring of the finite-type `K`-scheme `Y_K` at the image of `η` is recorded algebraically, as
`𝒪_{Y,η}` being essentially of finite type over `K`. The top exterior power of `Ω_{R/k}` is
indexed by `m + (n - m)`, the length of the concatenated family.

### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential
open scoped TensorProduct

namespace MMP.Mori.Internal.CanonicalSplitting

/-- A regular local ring essentially of finite type over a perfect field is formally smooth over
it: it is the localization of a finitely generated algebra at a prime with separable residue field,
and regularity there is smoothness (Stacks 00TV). -/
private theorem formallySmooth_of_essFiniteType {K R : Type*} [Field K] [PerfectField K]
    [CommRing R] [Algebra K R] [IsLocalRing R] [IsRegularLocalRing R]
    [Algebra.EssFiniteType K R] : Algebra.FormallySmooth K R := by
  let A := Algebra.EssFiniteType.subalgebra K R
  let q : Ideal A := (IsLocalRing.maximalIdeal R).comap (algebraMap A R)
  have hS : Algebra.EssFiniteType.submonoid K R = q.primeCompl := by
    ext x
    simp [Algebra.EssFiniteType.submonoid, q, Ideal.primeCompl, IsLocalRing.notMem_maximalIdeal]
    rfl
  have : IsLocalization.AtPrime R q := by
    have := Algebra.EssFiniteType.isLocalization K R
    rwa [hS] at this
  have := Algebra.isSeparableExtension_of_perfectField K q.ResidueField
  have hs : Algebra.IsSmoothAt K q :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q R).mpr inferInstance
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R).restrictScalars K)

/-- For a free module `M` of rank `N`, the wedge `v₁ ∧ ⋯ ∧ v_N` generates `⋀^N M` exactly when the
`vᵢ` span `M`: one direction evaluates the determinant of a basis, the other uses that a spanning
family of `N` vectors is a basis. -/
private theorem span_ιMulti_eq_top_iff {A M : Type*} [CommRing A] [Nontrivial A]
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] {N : ℕ}
    (h : Module.finrank A M = N) (v : Fin N → M) :
    Submodule.span A {exteriorPower.ιMulti A N v} = ⊤ ↔
      Submodule.span A (Set.range v) = ⊤ := by
  constructor
  · intro hv
    let b : Module.Basis (Fin N) A M := Module.finBasisOfFinrankEq A M h
    have hmem : exteriorPower.ιMulti A N b ∈ Submodule.span A {exteriorPower.ιMulti A N v} :=
      hv ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) hc
    rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self,
      smul_eq_mul] at this
    exact ((b.is_basis_iff_det).mpr (isUnit_of_dvd_one ⟨c, this.symm.trans (mul_comm _ _)⟩)).2
  · intro hv
    have hli : LinearIndependent A v :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [h])
    let B : Module.Basis (Fin N) A M := Module.Basis.mk hli hv.ge
    obtain ⟨σ, hσ⟩ := MMP.Mori.exists_span_singleton_eq_top_exteriorPower h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (hσ ▸ Submodule.mem_top : exteriorPower.ιMulti A N v ∈ Submodule.span A {σ})
    have := congrArg (exteriorPower.alternatingMapLinearEquiv B.det) ha
    rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, smul_eq_mul] at this
    have hB : B.det v = 1 := by
      have : (B : Fin N → M) = v := Module.Basis.coe_mk hli hv.ge
      rw [← this, Module.Basis.det_self]
    rw [hB] at this
    rw [← ha, Submodule.span_singleton_smul_eq (isUnit_of_dvd_one ⟨_, this.symm⟩), hσ]

/-- In an exact sequence `F → M → P → 0`, the images `f(bᵢ)` of a basis of `F` together with a
family `ω` span `M` exactly when the images `g(ωⱼ)` span `P`. -/
private theorem span_range_append_eq_top_iff {A F M P : Type*} [CommRing A]
    [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    {f : F →ₗ[A] M} {g : M →ₗ[A] P} (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {m l : ℕ} (b : Module.Basis (Fin m) A F) (ω : Fin l → M) :
    Submodule.span A (Set.range (Fin.append (fun i => f (b i)) ω)) = ⊤ ↔
      Submodule.span A (Set.range (fun j => g (ω j))) = ⊤ := by
  have hl : ∀ i, f (b i) ∈ Submodule.span A (Set.range (Fin.append (fun i => f (b i)) ω)) :=
    fun i => Submodule.subset_span ⟨Fin.castAdd l i, Fin.append_left _ _ _⟩
  have hr : ∀ j, ω j ∈ Submodule.span A (Set.range (Fin.append (fun i => f (b i)) ω)) :=
    fun j => Submodule.subset_span ⟨Fin.natAdd m j, Fin.append_right _ _ _⟩
  constructor
  · intro h
    have hle : Submodule.span A (Set.range (Fin.append (fun i => f (b i)) ω)) ≤
        (Submodule.span A (Set.range (fun j => g (ω j)))).comap g := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp [hfg.apply_apply_eq_zero]
      · simpa using Submodule.subset_span (Set.mem_range_self (f := fun j => g (ω j)) j)
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := hg y
    exact hle (h ▸ Submodule.mem_top)
  · intro h
    rw [eq_top_iff]
    rintro x -
    have hx : g x ∈ (Submodule.span A (Set.range ω)).map g := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact h ▸ Submodule.mem_top
    obtain ⟨x', hx', hgx⟩ := hx
    have hk : x - x' ∈ LinearMap.range f := (hfg (x - x')).mp (by simp [hgx])
    obtain ⟨z, hz⟩ := hk
    have hz' : f z ∈ Submodule.span A (Set.range (Fin.append (fun i => f (b i)) ω)) := by
      have : z ∈ Submodule.span A (Set.range b) := b.span_eq ▸ Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := f) this
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact Submodule.span_le.mpr (Set.range_subset_iff.2 hl) this
    have hx'' : x' ∈ Submodule.span A (Set.range (Fin.append (fun i => f (b i)) ω)) :=
      Submodule.span_le.mpr (Set.range_subset_iff.2 hr) hx'
    have : x = f z + x' := by rw [hz]; abel
    rw [this]
    exact add_mem hz' hx''

/-- In a short exact sequence `0 → F → M → P → 0` of finite free modules with `P` projective, the
ranks add up: a section of `M → P` identifies `M` with `F × P`. -/
private theorem finrank_add_finrank_of_exact {A F M P : Type*} [CommRing A] [Nontrivial A]
    [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    [Module.Free A F] [Module.Finite A F] [Module.Free A P] [Module.Finite A P]
    {f : F →ₗ[A] M} {g : M →ₗ[A] P} (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Module.finrank A F + Module.finrank A P = Module.finrank A M := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  rw [← Module.finrank_prod, ((hfg.splitSurjectiveEquiv hf) ⟨l, hl⟩).1.finrank_eq]

end MMP.Mori.Internal.CanonicalSplitting

namespace MMP.Mori.PrimeDivisor

open MMP.Mori.Internal.CanonicalSplitting in
/-- **Splitting of differentials at a horizontal codimension-one point.** For a normal variety
`X` of dimension `n` over a field `k` of characteristic zero, algebraically independent
`t : Fin m → Γ(X, ⊤)`, and a prime divisor `Γ` whose local ring `R` is a `K = k(t)`-algebra
(`Xᵢ ↦ tᵢ`), the sequence `0 → R ⊗_K Ω_{K/k} → Ω_{R/k} → Ω_{R/K} → 0` is exact, `R ⊗_K Ω_{K/k}`
has basis `1 ⊗ dXᵢ`, `Ω_{R/k}` and `Ω_{R/K}` are finite free of ranks `n` and `n - m`, and
`dt₁ ∧ ⋯ ∧ dtₘ ∧ ω₁ ∧ ⋯ ∧ ω_{n-m}` generates `⋀^n Ω_{R/k}` iff the images of the `ωⱼ` wedge to
a generator of `⋀^{n-m} Ω_{R/K}`. -/
@[mmp "lem_mmp_indexc_canonical_splitting"]
public theorem exact_mapBaseChange_map_localRing
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) {n m : ℕ} (hn : topologicalKrullDim X = n)
    (t : Fin m → Γ(X, ⊤)) (ht : letI := sectionAlgebra sX ⊤; AlgebraicIndependent k t)
    (Γ : PrimeDivisor X)
    (K : Type*) [Field K] [Algebra k K] [Algebra (MvPolynomial (Fin m) k) K]
    [IsScalarTower k (MvPolynomial (Fin m) k) K] [IsFractionRing (MvPolynomial (Fin m) k) K]
    [Algebra K Γ.localRing]
    (hT : letI := stalkAlgebra sX Γ.genericPoint; IsScalarTower k K Γ.localRing)
    (hK : ∀ i, algebraMap K Γ.localRing (algebraMap (MvPolynomial (Fin m) k) K (.X i)) =
      X.presheaf.germ ⊤ Γ.genericPoint trivial (t i))
    (hft : Algebra.EssFiniteType K Γ.localRing) :
    letI := stalkAlgebra sX Γ.genericPoint
    haveI := hT
    Function.Injective (mapBaseChange k K Γ.localRing) ∧
    Function.Exact (mapBaseChange k K Γ.localRing) (map k K Γ.localRing Γ.localRing) ∧
    Function.Surjective (map k K Γ.localRing Γ.localRing) ∧
    (∃ b : Module.Basis (Fin m) Γ.localRing (Γ.localRing ⊗[K] Ω[K⁄k]),
      ∀ i, b i = 1 ⊗ₜ D k K (algebraMap (MvPolynomial (Fin m) k) K (.X i))) ∧
    (Module.Free Γ.localRing Ω[Γ.localRing⁄k] ∧ Module.Finite Γ.localRing Ω[Γ.localRing⁄k] ∧
      Module.finrank Γ.localRing Ω[Γ.localRing⁄k] = n) ∧
    (Module.Free Γ.localRing Ω[Γ.localRing⁄K] ∧ Module.Finite Γ.localRing Ω[Γ.localRing⁄K] ∧
      Module.finrank Γ.localRing Ω[Γ.localRing⁄K] = n - m) ∧
    ∀ ω : Fin (n - m) → Ω[Γ.localRing⁄k],
      (Submodule.span Γ.localRing {(exteriorPower.ιMulti Γ.localRing (m + (n - m))
          (Fin.append (fun i => D k Γ.localRing (X.presheaf.germ ⊤ Γ.genericPoint trivial (t i)))
            ω))} = ⊤ ↔
        Submodule.span Γ.localRing {(exteriorPower.ιMulti Γ.localRing (n - m)
          (fun j => map k K Γ.localRing Γ.localRing (ω j)))} = ⊤) := by
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := hT
  obtain ⟨hV, hN⟩ := hX
  have := hV.toIsIntegral
  have := hV.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := Γ.isDiscreteValuationRing_localRing
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  -- `Ω_{Γ.localRing/k}` is free of rank `n`
  obtain ⟨hfree, hfin⟩ := Γ.free_kaehlerDifferential_localRing (sX := sX)
  have hrk : Module.finrank Γ.localRing Ω[Γ.localRing⁄k] = n :=
    Γ.finrank_kaehlerDifferential_localRing.trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  -- `Γ.localRing` is formally smooth over `K`, so `Ω_{Γ.localRing/K}` is finite free
  have hsm : Algebra.FormallySmooth K Γ.localRing := formallySmooth_of_essFiniteType
  have hfreeK : Module.Free Γ.localRing Ω[Γ.localRing⁄K] := Module.free_of_flat_of_isLocalRing
  -- the transitivity sequence
  have hinj : Function.Injective (mapBaseChange k K Γ.localRing) :=
    (injective_iff_map_eq_zero _).mpr fun x hx => by
      obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k K Γ.localRing x).mp hx
      rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map k K Γ.localRing
  have hsurj := map_surjective k K Γ.localRing
  -- the basis `1 ⊗ dXᵢ`
  let b0 := (mvPolynomialBasis k (Fin m)).ofIsLocalizedModule K
    (nonZeroDivisors (MvPolynomial (Fin m) k)) (map k k (MvPolynomial (Fin m) k) K)
  let b := b0.baseChange Γ.localRing
  have hb : ∀ i, b i = 1 ⊗ₜ D k K (algebraMap (MvPolynomial (Fin m) k) K (.X i)) := fun i => by
    simp [b, b0, Module.Basis.ofIsLocalizedModule_apply]
  have hbD : ∀ i, mapBaseChange k K Γ.localRing (b i) =
      D k Γ.localRing (X.presheaf.germ ⊤ Γ.genericPoint trivial (t i)) := fun i => by
    rw [hb, mapBaseChange_tmul, one_smul, map_D, ← hK]
  -- ranks through a splitting
  have : Module.Free Γ.localRing (Γ.localRing ⊗[K] Ω[K⁄k]) := .of_basis b
  have : Module.Finite Γ.localRing (Γ.localRing ⊗[K] Ω[K⁄k]) := .of_basis b
  have h1 := finrank_add_finrank_of_exact hex hinj hsurj
  rw [hrk, Module.finrank_eq_card_basis b, Fintype.card_fin] at h1
  have hrkK : Module.finrank Γ.localRing Ω[Γ.localRing⁄K] = n - m := by omega
  refine ⟨hinj, hex, hsurj, ⟨b, hb⟩, ⟨hfree, hfin, hrk⟩, ⟨hfreeK, inferInstance, hrkK⟩,
    fun ω => ?_⟩
  rw [span_ιMulti_eq_top_iff (hrk.trans (by omega)), span_ιMulti_eq_top_iff hrkK,
    ← span_range_append_eq_top_iff hex hsurj b ω]
  simp_rw [hbD]

end MMP.Mori.PrimeDivisor

end

/-!
## Volume growth in a nontrivial nef direction

Let `W` be a projective variety of dimension `d > 0` over a field `k`, `L` a nef invertible
sheaf on `W` which is not numerically trivial (some proper curve `C ⊆ W` has `deg_C L ≠ 0`), and
`M` an ample invertible sheaf. Then for every `q > 0` the top self-intersection
`(tL + qM)^d` tends to `+∞` as the real parameter `t` tends to `+∞`.

### Main results

* `MMP.Mori.tendsto_sheafCombinationIntersectionNumber_atTop_of_isNef`: the statement above.

### Implementation notes

The nef Cartier divisor `L` of the source is its invertible sheaf `𝒪_W(L)`. An ample rational
Cartier divisor `A` is `q M` with `M = 𝒪_W(mA)` an ample invertible sheaf and `q = 1/m`; the
statement is given for every real `q > 0`. The number `(tL + qM)^d` is the multilinear expansion
`MMP.Mori.sheafCombinationIntersectionNumber` of the combination `t L + q M`, taken in `ℝ`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.38
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter
open CategoryTheory AlgebraicGeometry Filter MMP.Mori

namespace MMP.Mori.Internal.LcBpfNefVolumeGrowth

section Aux

open MvPolynomial

private noncomputable def negSub {d : ℕ} : MvPolynomial (Fin d) ℚ →ₐ[ℚ] MvPolynomial (Fin d) ℚ :=
  aeval (fun i => - X i)

private theorem negSub_monomial {d : ℕ} (s : Fin d →₀ ℕ) (a : ℚ) :
    negSub (monomial s a) = monomial s (a * (-1) ^ s.sum fun _ e => e) := by
  rw [negSub, aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  have : ∀ i : Fin d, (-X i : MvPolynomial (Fin d) ℚ) ^ s i = (-1) ^ s i * X i ^ s i := by
    intro i; rw [neg_pow]
  simp only [this, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp [map_mul, mul_assoc, algebraMap_eq]

private theorem coeff_negSub {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (s : Fin d →₀ ℕ) :
    (negSub P).coeff s = P.coeff s * (-1) ^ s.sum fun _ e => e := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [negSub_monomial]
    by_cases h : u = s
    · subst h; simp [coeff_monomial]
    · simp [coeff_monomial, h]
  | add p q hp hq => simp [map_add, hp, hq, add_mul]

private theorem eval_negSub {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (x : Fin d → ℚ) :
    eval x (negSub P) = eval (fun i => - x i) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [negSub_monomial, eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
    have : ∀ i : Fin d, (-x i) ^ u i = (-1) ^ u i * x i ^ u i := by
      intro i; rw [neg_pow]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    ring
  | add p q hp hq => simp [map_add, hp, hq]

private theorem totalDegree_negSub {d : ℕ} (P : MvPolynomial (Fin d) ℚ) :
    (negSub P).totalDegree ≤ P.totalDegree := by
  refine totalDegree_le_of_support_subset ?_
  intro s hs
  rw [mem_support_iff, coeff_negSub] at hs
  exact mem_support_iff.2 fun h => hs (by simp [h])

private theorem sum_neg_indicator {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (hP : P.totalDegree ≤ d) :
    ∑ I : Finset (Fin d), (-1 : ℚ) ^ I.card *
        eval (fun j => if j ∈ I then (-1 : ℚ) else 0) P =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  have h := MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one (negSub P)
    ((totalDegree_negSub P).trans hP)
  rw [coeff_negSub] at h
  have hs : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1).sum (fun _ e => e) = d := by
    rw [Finsupp.sum_fintype _ _ (by simp)]; simp
  rw [hs] at h
  have e1 : ∀ I : Finset (Fin d), eval (fun j => if j ∈ I then (1 : ℚ) else 0) (negSub P) =
      eval (fun j => if j ∈ I then (-1 : ℚ) else 0) P := by
    intro I; rw [eval_negSub]
    have : (fun j => -(if j ∈ I then (1 : ℚ) else 0)) = fun j => if j ∈ I then (-1 : ℚ) else 0 := by
      funext j; split_ifs <;> simp
    rw [this]
  simp only [e1] at h
  have : ∀ I : Finset (Fin d), (-1 : ℚ) ^ (d - I.card) = (-1) ^ d * (-1) ^ I.card := by
    intro I
    have hI : I.card ≤ d := by simpa using Finset.card_le_univ I
    have : (-1 : ℚ) ^ d = (-1) ^ (d - I.card) * (-1) ^ I.card := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  simp only [this, mul_assoc, ← Finset.mul_sum] at h
  have h2 : ((-1 : ℚ) ^ d) * ((-1) ^ d) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination ((-1:ℚ)^d) * h - (∑ I : Finset (Fin d), (-1 : ℚ) ^ I.card *
        eval (fun j => if j ∈ I then (-1 : ℚ) else 0) P -
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1)) * h2

private theorem sheafIntersectionNumber_eq_intersectionNumber (k : Type u) [Field k]
    {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k f i d hd L = AlgebraicGeometry.intersectionNumber k f i d hd L := by
  have hc := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  obtain ⟨P, hP0, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (i ≫ f)
    (fun j => (Scheme.Modules.pullback i).obj (L j)) (SheafOfModules.unit Z.ringCatSheaf) hc
  have hdeg : P.totalDegree ≤ d := by
    rcases hP0 with rfl | h
    · simp
    · have h2 := h.trans (le_trans (topologicalKrullDim_subspace_le Z _) hd)
      exact_mod_cast h2
  have hcoeff := AlgebraicGeometry.intersectionNumber_eq_coeff k f i d hd L P
    (fun n => by rw [hP n]) hdeg
  apply Int.cast_injective (α := ℚ)
  rw [hcoeff, ← sum_neg_indicator P hdeg]
  unfold sheafIntersectionNumber
  push_cast
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  have h := hP fun j => if j ∈ I then (-1 : ℤ) else 0
  rw [show (fun j : Fin d => (((if j ∈ I then (-1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun j : Fin d => if j ∈ I then (-1 : ℚ) else 0 from
      funext fun j => by split_ifs <;> simp] at h
  rw [h]

end Aux

section Mixed

open AlgebraicGeometry
open Stacks.SheafOfModules.Invertible (tensorPower)

/-- The family with the sheaf `M` in the slots satisfying `lab` and `L` in the others. -/
private def mixFam {X : Scheme.{u}} (L M : X.Modules) {d : ℕ} (lab : Fin d → Prop)
    [DecidablePred lab] : Fin d → X.Modules := fun q => if lab q then M else L

private instance mixFam_isInvertible {X : Scheme.{u}} (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] {d : ℕ} (lab : Fin d → Prop)
    [DecidablePred lab] (q : Fin d) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (mixFam L M lab q) := by
  unfold mixFam; split_ifs <;> infer_instance

/-- An intersection number is a positive integral combination of the intersection numbers of the
finitely many top-dimensional components, the weights being their multiplicities
(`AlgebraicGeometry.intersectionNumber_eq_sum_topDimComponents`). -/
private theorem exists_pos_weights_topDimComponents (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    ∃ (_ : Fintype (TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))))
      (w : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) → ℤ),
      (∀ W, 0 < w W) ∧ intersectionNumber k f i d hd.le L = ∑ W, w W *
        intersectionNumber k f W.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd W) L := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := ⟨⟩
  haveI : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  haveI : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i (Stacks.Ample.unitModule Z)
  haveI : Finite (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :=
    finite_topDimIntegralSubscheme k f _
  classical
  haveI := Fintype.ofFinite (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)))
  exact ⟨inferInstance, _, sheafMultiplicity_genericPt_pos k f _, by
    rw [intersectionNumber_eq_sum_topDimComponents k f i d hd L, finsum_eq_sum_of_fintype]⟩

/-- Nonnegativity of an intersection number from nonnegativity on the top-dimensional
components, as `AlgebraicGeometry.intersectionNumber_pos_of_pos_topDimComponents`. -/
private theorem intersectionNumber_nonneg_of_nonneg_topDimComponents (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hnn : ∀ W : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        0 ≤ intersectionNumber k f W.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd W) L) :
    0 ≤ intersectionNumber k f i d hd.le L := by
  obtain ⟨_, w, hw, h⟩ := exists_pos_weights_topDimComponents k f i d hd L
  exact h ▸ Finset.sum_nonneg fun W _ => mul_nonneg (hw W).le (hnn W)

/-- **The induction behind the mixed nonnegativity** (KM Theorem 1.38, proof), following the proof
of [Stacks, Tag 0BEV] in `AlgebraicGeometry.intersectionNumber_pos`: if `(L^j · W) ≥ 0` for every
integral closed `W` of dimension `j` and `M` is ample, then every closed subscheme `Z` of
dimension `j + s` has `(L^j M^s · Z) ≥ 0`, the family being `L` in some `j` slots and `M` in the
other `s`. -/
private theorem mixed_nonneg_aux (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hM : Stacks.Ample.IsAmple X M) (j : ℕ)
    (hL : ∀ (W : Scheme.{u}) (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
      (hW : topologicalKrullDim W = (j : WithBot ℕ∞)),
      0 ≤ intersectionNumber k f i j hW.le (fun _ => L)) :
    ∀ (s d : ℕ), d = j + s → ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (hdim : topologicalKrullDim Z = (d : WithBot ℕ∞)) (lab : Fin d → Prop)
      [DecidablePred lab], (∑ q, if lab q then 1 else 0) = s →
      0 ≤ intersectionNumber k f i d hdim.le (mixFam L M lab) := by
  classical
  intro s
  induction s with
  | zero =>
    intro d hdj Z i _ hdim lab _ hcnt
    refine intersectionNumber_nonneg_of_nonneg_topDimComponents k f i d hdim _ (fun W => ?_)
    haveI : IsIntegral W.1.subscheme := W.2.1
    have hdimW : topologicalKrullDim W.1.subscheme = (d : WithBot ℕ∞) := by
      refine W.2.2.2.trans ?_
      rw [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i]
      exact hdim
    have hlab : ∀ q, ¬ lab q := by
      intro q hq
      have : 0 < ∑ q, if lab q then 1 else 0 :=
        Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨q, Finset.mem_univ _, by simp [hq]⟩
      omega
    have hfam : mixFam L M lab = fun _ => L := funext fun q => if_neg (hlab q)
    have hdj' : d = j := by omega
    subst hdj'
    rw [intersectionNumber_congr_family k f W.1.subschemeι d _ hfam]
    exact hL W.1.subscheme W.1.subschemeι hdimW
  | succ s ih =>
    intro d hdj Z i _ hdim lab _ hcnt
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨j + s, by omega⟩
    have hex : ∃ q0, lab q0 := by
      by_contra h
      push Not at h
      simp [h] at hcnt
    obtain ⟨q0, hq0⟩ := hex
    let σ : Equiv.Perm (Fin (d' + 1)) := Equiv.swap 0 q0
    have hlab0 : lab (σ 0) := by simp [σ, hq0]
    suffices H : ∀ (lab' : Fin (d' + 1) → Prop) [DecidablePred lab'], lab' 0 →
        (∑ q, if lab' q then 1 else 0) = s + 1 →
        0 ≤ intersectionNumber k f i (d' + 1) hdim.le (mixFam L M lab') by
      have h1 := H (fun q => lab (σ q)) hlab0 (by
        rw [← hcnt]; exact Equiv.sum_comp σ (fun q => if lab q then 1 else 0))
      have hperm := intersectionNumber_comp_perm k f i (d' + 1) hdim.le (mixFam L M lab) σ
      rw [← hperm]
      exact h1
    intro lab' _ h0 hcnt'
    set T : Fin d' → X.Modules := mixFam L M (fun t : Fin d' => lab' t.succ) with hT
    have hGeq : mixFam L M lab' = (Fin.cons M T : Fin (d' + 1) → X.Modules) := by
      funext q
      refine Fin.cases ?_ (fun t => ?_) q
      · exact if_pos h0
      · rfl
    haveI hGinv : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((Fin.cons M T : Fin (d' + 1) → X.Modules) q) := isInvertible_finCons M T
    rw [intersectionNumber_congr_family k f i (d' + 1) hdim.le hGeq]
    refine intersectionNumber_nonneg_of_nonneg_topDimComponents k f i (d' + 1) hdim _
      (fun W => ?_)
    haveI : IsIntegral W.1.subscheme := W.2.1
    have hdimW : topologicalKrullDim W.1.subscheme = ((d' + 1 : ℕ) : WithBot ℕ∞) := by
      refine W.2.2.2.trans ?_
      rw [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i]
      exact hdim
    have hposdim : 0 < topologicalKrullDim W.1.subscheme := by
      rw [hdimW]
      exact_mod_cast Nat.succ_pos d'
    haveI hMinv : Stacks.Ample.IsInvertibleModule W.1.subscheme
        ((Scheme.Modules.pullback W.1.subschemeι).obj M) := inferInstance
    have hMample : Scheme.Modules.IsAmple W.1.subscheme
        ((Scheme.Modules.pullback W.1.subschemeι).obj M) :=
      Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
        (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
          W.1.subschemeι M hM (Or.inl ⟨inferInstance, inferInstance⟩))
    obtain ⟨n, D, hn, hDcartier, hDne, ⟨e⟩⟩ :=
      exists_effectiveCartierDivisor_tensorPower_of_isAmple k (W.1.subschemeι ≫ f) hposdim
        ((Scheme.Modules.pullback W.1.subschemeι).obj M) hMample
    haveI : Nonempty D.subscheme := hDne
    have hDdim : topologicalKrullDim D.subscheme = (d' : WithBot ℕ∞) :=
      topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k
        (W.1.subschemeι ≫ f) D hDcartier hdimW
    set G : Fin (d' + 1) → X.Modules := Fin.cons M T with hG
    set N : Fin (d' + 1) → X.Modules :=
      Function.update G 0 (tensorPower X.presheaf X.ringCatSheaf.2 (G 0) (n : ℤ)) with hN
    haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
      isInvertible_update G 0 _
    have hNsucc : ∀ t : Fin d', N t.succ = T t := fun t =>
      (Function.update_of_ne (Fin.succ_ne_zero t) _ _).trans (Fin.cons_succ _ _ _)
    have hNiso : (Scheme.Modules.pullback W.1.subschemeι).obj (N 0) ≅
        (Stacks.Divisors.invertibleSheaf D : W.1.subscheme.Modules) :=
      eqToIso (congrArg (Scheme.Modules.pullback W.1.subschemeι).obj
          (Function.update_self (0 : Fin (d' + 1)) _ G)) ≪≫
        Scheme.Modules.pullbackTensorPowerIso W.1.subschemeι (G 0) n ≪≫ e
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hDcartier
    have hBEU := intersectionNumber_eq_of_isEffectiveCartierDivisor k f W.1.subschemeι d'
      (le_of_eq hdimW) N D (le_of_eq hDdim) hNiso
    have hrec : 0 ≤ intersectionNumber k f (D.subschemeι ≫ W.1.subschemeι) d'
        (le_of_eq hDdim) (fun t : Fin d' => N t.succ) := by
      have hNs : (fun t : Fin d' => N t.succ) = T := funext hNsucc
      rw [intersectionNumber_congr_family k f _ d' _ hNs]
      refine ih d' (by omega) (D.subschemeι ≫ W.1.subschemeι) hDdim
        (fun t : Fin d' => lab' t.succ) ?_
      rw [Fin.sum_univ_succ] at hcnt'
      simp only [h0, if_true] at hcnt'
      omega
    have hNnn : 0 ≤ intersectionNumber k f W.1.subschemeι (d' + 1) (le_of_eq hdimW) N := by
      rwa [hBEU]
    have hmul := intersectionNumber_update_tensorPower k f W.1.subschemeι (d' + 1)
      (le_of_eq hdimW) G 0 n
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hprod : 0 ≤ (n : ℤ) * intersectionNumber k f W.1.subschemeι (d' + 1)
        (le_of_eq hdimW) G := by
      rwa [← hmul]
    exact le_of_not_gt fun h => by nlinarith

end Mixed

/-! ### Positivity along a curve of positive degree -/

section Positivity

/-- A closed subset of an irreducible set of the same finite dimension is all of it. -/
private theorem eq_of_isClosed_subset_of_topologicalKrullDim_eq {T : Type*} [TopologicalSpace T]
    {A B : Set T} (hA : IsClosed A) (hB : IsIrreducible B) (hAB : A ⊆ B) {n : ℕ}
    (hAd : topologicalKrullDim A = n) (hBd : topologicalKrullDim B = n) : A = B := by
  by_contra hne
  haveI : IrreducibleSpace B := Subtype.irreducibleSpace hB
  set A' : Set B := Subtype.val ⁻¹' A
  have hA' : IsClosed A' := hA.preimage continuous_subtype_val
  have hne' : A' ≠ Set.univ := by
    intro h
    apply hne
    refine subset_antisymm hAB fun b hb => ?_
    exact (h ▸ Set.mem_univ _ : (⟨b, hb⟩ : B) ∈ A')
  have hlt := AlgebraicGeometry.topologicalKrullDim_lt_of_isClosed_ne_univ hA' hne'
    (by rw [hBd]; exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top n))
  let g : A → A' := fun a => ⟨⟨a.1, hAB a.2⟩, a.2⟩
  have hg : Topology.IsInducing g := by
    refine Topology.IsInducing.of_comp (g := fun x : A' => (x.1.1 : T)) ?_ (by fun_prop) ?_
    · fun_prop
    · exact Topology.IsInducing.subtypeVal
  have h := hg.topologicalKrullDim_le.trans_lt hlt
  rw [hAd, hBd] at h
  exact lt_irrefl _ h

/-- Two closed subschemes with reduced structure and the same support are equal. -/
private theorem idealSheafData_eq_of_support_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    [IsReduced I.subscheme] [IsReduced J.subscheme]
    (h : (I.support : Set X) = J.support) : I = J := by
  have hI : I = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range I.subschemeι)) := by
    conv_lhs => rw [← I.ker_subschemeι]
    exact Scheme.Hom.ker_eq_vanishingIdeal_closure_range _
  have hJ : J = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range J.subschemeι)) := by
    conv_lhs => rw [← J.ker_subschemeι]
    exact Scheme.Hom.ker_eq_vanishingIdeal_closure_range _
  rw [hI, hJ, I.range_subschemeι, J.range_subschemeι]
  congr 2

/-- The image of an irreducible scheme is irreducible. -/
private theorem isIrreducible_range {X Z : Scheme.{u}} (i : Z ⟶ X) [IrreducibleSpace Z] :
    IsIrreducible (Set.range i) := by
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ Z).image _ i.base.hom.continuous.continuousOn

/-- The support of a top-dimensional component of a closed integral subscheme is its image. -/
private theorem support_eq_range_of_topDimIntegralSubscheme {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] {n : ℕ} (hZ : topologicalKrullDim Z = n)
    (V : TopDimIntegralSubscheme ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :
    (V.1.support : Set X) = Set.range i := by
  have hsupp := Stacks.Chow.supp_pushforwardStructureSheaf i
  have hsub : (V.1.support : Set X) ⊆ Set.range i := hsupp ▸ V.2.2.1
  refine eq_of_isClosed_subset_of_topologicalKrullDim_eq V.1.support.isClosed
    (isIrreducible_range i) hsub ?_
    (by rw [topologicalKrullDim_range_eq i, hZ])
  have h2 := V.2.2.2
  have h3 : topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) = n := by
    rw [hsupp, topologicalKrullDim_range_eq i, hZ]
  rw [← V.1.range_subschemeι, topologicalKrullDim_range_eq V.1.subschemeι, h2, h3]

/-- An intersection number is a positive combination of the intersection numbers of the
top-dimensional components: if every component contributes `≥ 0` and one contributes `> 0`, the
intersection number is positive. -/
private theorem intersectionNumber_pos_of_nonneg_of_pos_component (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hnn : ∀ V : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        0 ≤ intersectionNumber k f V.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd V) L)
    (V₀ : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)))
    (hpos : 0 < intersectionNumber k f V₀.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd V₀) L) :
    0 < intersectionNumber k f i d hd.le L := by
  obtain ⟨_, w, hw, h⟩ := exists_pos_weights_topDimComponents k f i d hd L
  exact h ▸ Finset.sum_pos' (fun V _ => mul_nonneg (hw V).le (hnn V))
    ⟨V₀, Finset.mem_univ _, mul_pos (hw V₀) hpos⟩

/-- A positive intersection number has a top-dimensional component of positive intersection
number. -/
private theorem exists_pos_component_of_intersectionNumber_pos (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hpos : 0 < intersectionNumber k f i d hd.le L) :
    ∃ V : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        0 < intersectionNumber k f V.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd V) L := by
  by_contra h
  push Not at h
  obtain ⟨_, w, hw, hsum⟩ := exists_pos_weights_topDimComponents k f i d hd L
  exact hpos.not_ge (hsum ▸ Finset.sum_nonpos fun V _ =>
    mul_nonpos_of_nonneg_of_nonpos (hw V).le (h V))

/-- **The base case.** If a closed integral curve `c : C ⟶ X` has positive degree for `L` and its
image lies in the image of a closed integral curve `j : Z ⟶ X`, then `L` has positive degree
on `Z`. -/
private theorem intersectionNumber_pos_of_range_subset_curve (k : Type u) [Field k]
    {X C Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (c : C ⟶ X) [IsClosedImmersion c] [IsIntegral C]
    (hC : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞))
    (j : Z ⟶ X) [IsClosedImmersion j] [IsIntegral Z]
    (hZ : topologicalKrullDim Z = ((1 : ℕ) : WithBot ℕ∞))
    (hcj : Set.range c ⊆ Set.range j)
    (hpos : 0 < intersectionNumber k f c 1 hC.le (fun _ => L)) :
    0 < intersectionNumber k f j 1 hZ.le (fun _ => L) := by
  have hrange : Set.range c = Set.range j :=
    eq_of_isClosed_subset_of_topologicalKrullDim_eq c.isClosedEmbedding.isClosed_range
      (isIrreducible_range j) hcj (by rw [topologicalKrullDim_range_eq c, hC])
      (by rw [topologicalKrullDim_range_eq j, hZ])
  obtain ⟨V, hV⟩ := exists_pos_component_of_intersectionNumber_pos k f c 1 hC _ hpos
  refine intersectionNumber_pos_of_pos_topDimComponents k f j 1 hZ _ fun V' => ?_
  haveI := V.2.1
  haveI := V'.2.1
  have hVV : V'.1 = V.1 := idealSheafData_eq_of_support_eq _ _ (by
    rw [support_eq_range_of_topDimIntegralSubscheme j hZ V',
      support_eq_range_of_topDimIntegralSubscheme c hC V, hrange])
  rw [intersectionNumber_congr_ideal k f hVV 1 _
    (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme c hC V)]
  exact hV

section Divisor

open Opposite

/-- **An ample divisor through a closed subset.** On an integral scheme `Z` proper over a field
with an ample invertible module `𝓜`, every closed subset `S ≠ Z` lies in an effective Cartier
divisor `D` with `𝓜^{⊗ n} ≅ 𝒪_Z(D)` for some `n ≥ 1`: a section `s` of a power of `𝓜` with
`Z_s ⊆ Z ∖ S` and `Z_s` nonempty exists by [Stacks, Tag 09NV], and its zero scheme is `D`. -/
private theorem exists_effectiveCartierDivisor_tensorPower_supset (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsProper g] [IsIntegral Z] (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M] (hM : Stacks.Ample.IsAmple Z M) (S : Set Z)
    (hS : IsClosed S) (hSne : S ≠ Set.univ) :
    ∃ (n : ℕ) (D : Z.IdealSheafData), 1 ≤ n ∧
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧ S ⊆ D.supportSet ∧
      Nonempty (Scheme.Modules.tensorPowerModules M (n : ℤ) ≅
        Stacks.Divisors.invertibleSheaf D) := by
  classical
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨x₀, hx₀S⟩ : ∃ x₀, x₀ ∉ S := by
    by_contra h
    push Not at h
    exact hSne (Set.eq_univ_of_forall h)
  obtain ⟨n, hn, s, -, hTs, hsU⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite M hM
      (Set.finite_singleton x₀) ⟨Sᶜ, hS.isOpen_compl⟩ (by simpa using hx₀S)
  haveI : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule Z M (n : ℤ)) :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hx₀ : x₀ ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s :=
    (Stacks.AmpleTheory.coe_powNonvanishingOpen Z M n s) ▸ hTs rfl
  have hne0 : s ≠ 0 := by
    intro h
    rw [h, Stacks.Ample.mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection Z.sheaf.obj Z.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  refine ⟨n, zeroScheme Z (Stacks.Ample.tensorPowModule Z M (n : ℤ))
      ((Stacks.SheafOfModules.sectionsOfTop
        (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s).eval (op ⊤)),
    hn, (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Z _ _).2 hreg, ?_, ?_⟩
  · have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme
      (Stacks.Ample.tensorPowModule Z M (n : ℤ)) _ hne0'
    have hloc : Stacks.Ample.nonvanishingLocus
        (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s =
        ((zeroScheme Z (Stacks.Ample.tensorPowModule Z M (n : ℤ))
          ((Stacks.SheafOfModules.sectionsOfTop
            (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s).eval (op ⊤))).supportSet)ᶜ := by
      have h1 : Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s =
          ((Stacks.SheafOfModules.nonvanishingOpen (Stacks.Ample.tensorPowModule Z M (n : ℤ))
            (Stacks.SheafOfModules.sectionsOfTop
              (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s)) : Set Z) := by
        conv_lhs => rw [← hevaltop]
        rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Z _
          (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s)]
      rw [h1]
      exact hcompl
    intro x hx
    by_contra hxD
    have hxloc : x ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.Ample.tensorPowModule Z M (n : ℤ)) s := by
      rwa [hloc]
    rw [← Stacks.AmpleTheory.coe_powNonvanishingOpen Z M n s] at hxloc
    exact hsU hxloc hx
  · obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme Z _ _ hreg).exists
    exact ⟨(Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso Z M (n : ℤ)).trans e.symm⟩

/-- **Every irreducible component of an effective Cartier divisor has codimension one.** On an
integral scheme `Z` of dimension `e + 1` locally of finite type over a field, the closure of the
generic point `x` of an irreducible component of an effective Cartier divisor, with its reduced
structure, has dimension `e`: `dim 𝒪_{Z,x} = 1` by Krull's height theorem [Stacks, Tag 0BCN],
and the dimension of `closure {x}` is the relative dimension of `x` [Stacks, Tags 02JW, 02QO]. -/
private theorem topologicalKrullDim_vanishingIdeal_closure_component (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [IsIntegral Z]
    (D : Z.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {e : ℕ}
    (hZ : topologicalKrullDim Z = ((e + 1 : ℕ) : WithBot ℕ∞)) (ξ : D.subscheme)
    (hξ : ∃ Y : irreducibleComponents D.subscheme, IsGenericPoint ξ (Y : Set D.subscheme)) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {D.subschemeι ξ})).subscheme = (e : WithBot ℕ∞) := by
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have hco : Order.coheight (D.subschemeι ξ) = 1 := by
    exact_mod_cast (ringKrullDim_stalk_eq_coheight (D.subschemeι ξ)).symm.trans
      (ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD ξ hξ)
  have hn := Stacks.Chow.schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (k := k) g hZ
  have hrel : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation k).dimensionFunction g
      (D.subschemeι ξ) = ((e + 1 : ℕ) : ℤ) - 1 :=
    Stacks.Chow.relativeDimension_eq_sub_one_of_coheight_eq_one (Stacks.Chow.fieldChowSituation k)
      g hn hco
  haveI hint :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (D.subschemeι ξ)
  have hgen := Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure
    (D.subschemeι ξ)
  rw [Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat (Stacks.Chow.fieldChowSituation k)
    (fun _ _ => rfl) g (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {D.subschemeι ξ})).subschemeι (genericPoint _)
      (genericPoint_spec _), hgen, hrel]
  norm_num

/-- **A top-dimensional component of a divisor through a given point.** Let `j : Z ⟶ X` be a
closed integral subscheme of dimension `e + 1` and `D ⊆ Z` an effective Cartier divisor. Every
point `y` of `D` lies in the support of a top-dimensional component of `D`: the closure of the
generic point of an irreducible component of `D` through `y`, which has dimension `e` by
`topologicalKrullDim_vanishingIdeal_closure_component`. -/
private theorem exists_topDimIntegralSubscheme_mem_support (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (j : Z ⟶ X) [IsClosedImmersion j]
    [IsIntegral Z] {e : ℕ} (hZ : topologicalKrullDim Z = ((e + 1 : ℕ) : WithBot ℕ∞))
    (D : Z.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (p : D.subscheme) :
    ∃ V : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward (D.subschemeι ≫ j)).obj (Stacks.Ample.unitModule D.subscheme)),
      (D.subschemeι ≫ j) p ∈ (V.1.support : Set X) := by
  haveI : Nonempty D.subscheme := ⟨p⟩
  obtain ⟨Y, hY, hpY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({p} : Set D.subscheme)) isIrreducible_singleton.closure
  have hYclosed : IsClosed Y := isClosed_of_mem_irreducibleComponents Y hY
  set ξ := hY.1.genericPoint with hξdef
  have hξ : IsGenericPoint ξ Y := hY.1.isGenericPoint_genericPoint hYclosed
  set x : Z := D.subschemeι ξ with hx
  have hdimx := topologicalKrullDim_vanishingIdeal_closure_component k (j ≫ f) D hD hZ ξ
    ⟨⟨Y, hY⟩, hξ⟩
  set I : Z.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {x}) with hI
  haveI hint := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (j x)
  have hDdim : topologicalKrullDim D.subscheme = (e : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (j ≫ f) D hD hZ
  have hrangeI : Set.range I.subschemeι = closure ({x} : Set Z) := by
    rw [I.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hsuppV : ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {j x})).support : Set X) =
      Set.range (I.subschemeι ≫ j) := by
    have hr : Set.range (I.subschemeι ≫ j) = j '' Set.range I.subschemeι := by
      rw [← Set.range_comp]; rfl
    rw [hr, hrangeI, ← j.isClosedEmbedding.closure_image_eq, Set.image_singleton,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hsupp := Stacks.Chow.supp_pushforwardStructureSheaf (D.subschemeι ≫ j)
  have hcomp : (D.subschemeι ≫ j) ξ = j x := rfl
  refine ⟨⟨Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {j x}),
    hint, ?_, ?_⟩, ?_⟩
  · rw [hsupp, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact closure_minimal (Set.singleton_subset_iff.mpr ⟨ξ, hcomp⟩)
      (D.subschemeι ≫ j).isClosedEmbedding.isClosed_range
  · rw [hsupp, topologicalKrullDim_range_eq, hDdim,
      ← topologicalKrullDim_range_eq (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure {j x})).subschemeι,
      Scheme.IdealSheafData.range_subschemeι, hsuppV, topologicalKrullDim_range_eq, hdimx]
  · rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    have hξp : ξ ⤳ p := specializes_iff_mem_closure.mpr (by
      rw [hξ.def]; exact hpY (subset_closure rfl))
    have := specializes_iff_mem_closure.mp (hξp.map (D.subschemeι ≫ j).base.hom.continuous)
    rwa [← hcomp]

end Divisor

section Induction

open Stacks.SheafOfModules.Invertible (tensorPower)

/-- The family `(M, …, M, L)` of length `e + 1`, with `L` in the last slot. -/
private def lastFam {X : Scheme.{u}} (L M : X.Modules) : (e : ℕ) → Fin (e + 1) → X.Modules
  | 0 => fun _ => L
  | e + 1 => Fin.cons M (lastFam L M e)

private instance lastFam_isInvertible {X : Scheme.{u}} (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    ∀ (e : ℕ) (q : Fin (e + 1)),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (lastFam L M e q)
  | 0, _ => ‹_›
  | e + 1, q => by
    haveI := lastFam_isInvertible L M e
    exact isInvertible_finCons M (lastFam L M e) q

private theorem lastFam_eq_ite {X : Scheme.{u}} (L M : X.Modules) :
    ∀ (e : ℕ) (q : Fin (e + 1)), lastFam L M e q = if q = Fin.last e then L else M
  | 0, q => by
    obtain rfl : q = Fin.last 0 := Subsingleton.elim (α := Fin 1) _ _
    simp [lastFam]
  | e + 1, q => by
    refine Fin.cases ?_ (fun t => ?_) q
    · simp [lastFam, (Fin.last_pos (n := e)).ne]
    · rw [show lastFam L M (e + 1) t.succ = lastFam L M e t from rfl, lastFam_eq_ite L M e t]
      simp [← Fin.succ_last, Fin.succ_inj]

/-- **Positivity of `(M^e · L · Z)` for `Z` through a curve of positive degree** (the proof of
the lemma). Let `L` be nonnegative on every closed integral curve, `M` ample, and `C ⊆ X` a
closed integral curve with `(L · C) > 0`. Then `(M^e · L · Z) > 0` for every closed integral
`Z ⊇ C` of dimension `e + 1`. By induction on `e`: for `e = 0`, `Z = C`; for `e > 0`, a
positive power of `M` restricted to `Z` is `𝒪_Z(D)` for an effective Cartier divisor
`D ⊇ C` (`exists_effectiveCartierDivisor_tensorPower_supset`), so that
`n (M^e · L · Z) = (M^{e-1} · L · D)`, a sum of nonnegative contributions of the components of
`D` (`mixed_nonneg_aux`) among which the component through `C` contributes positively. -/
private theorem intersectionNumber_lastFam_pos (k : Type u) [Field k] {X C : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [Stacks.Ample.IsInvertibleModule X M] (hM : Stacks.Ample.IsAmple X M)
    (hL1 : ∀ (V : Scheme.{u}) (i : V ⟶ X) [IsClosedImmersion i] [IsIntegral V]
      (hV : topologicalKrullDim V = ((1 : ℕ) : WithBot ℕ∞)),
      0 ≤ intersectionNumber k f i 1 hV.le (fun _ => L))
    (c : C ⟶ X) [IsClosedImmersion c] [IsIntegral C]
    (hC : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞))
    (hc : 0 < intersectionNumber k f c 1 hC.le (fun _ => L)) :
    ∀ (e : ℕ) {Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j] [IsIntegral Z]
      (hZ : topologicalKrullDim Z = ((e + 1 : ℕ) : WithBot ℕ∞)),
      Set.range c ⊆ Set.range j → 0 < intersectionNumber k f j (e + 1) hZ.le (lastFam L M e) := by
  classical
  intro e
  induction e with
  | zero =>
    intro Z j _ _ hZ hcj
    exact intersectionNumber_pos_of_range_subset_curve k f L c hC j hZ hcj hc
  | succ e ih =>
    intro Z j _ _ hZ hcj
    haveI hMinv : Stacks.Ample.IsInvertibleModule Z ((Scheme.Modules.pullback j).obj M) :=
      inferInstance
    have hMZ : Stacks.Ample.IsAmple Z ((Scheme.Modules.pullback j).obj M) :=
      Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding j M hM
        (Or.inl ⟨inferInstance, inferInstance⟩)
    set S : Set Z := j.base ⁻¹' Set.range c with hSdef
    have hSclosed : IsClosed S :=
      c.isClosedEmbedding.isClosed_range.preimage j.base.hom.continuous
    have hSne : S ≠ Set.univ := by
      intro h
      have hsub : Set.range j ⊆ Set.range c := by
        rintro _ ⟨z, rfl⟩
        exact (h ▸ Set.mem_univ z : z ∈ S)
      have hle := topologicalKrullDim_le_of_subset hsub
      rw [topologicalKrullDim_range_eq j, topologicalKrullDim_range_eq c, hZ, hC] at hle
      have : e + 1 + 1 ≤ 1 := by exact_mod_cast hle
      omega
    obtain ⟨n, D, hn, hDc, hSD, ⟨eD⟩⟩ := exists_effectiveCartierDivisor_tensorPower_supset k
      (j ≫ f) ((Scheme.Modules.pullback j).obj M) hMZ S hSclosed hSne
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hDc
    -- a point of `D` over the generic point of `C`
    obtain ⟨z, hz⟩ := hcj ⟨genericPoint C, rfl⟩
    have hzS : z ∈ S := by
      show j z ∈ Set.range c
      rw [hz]; exact ⟨_, rfl⟩
    have hzD : z ∈ Set.range D.subschemeι := by
      rw [D.range_subschemeι]; exact hSD hzS
    obtain ⟨p, hp⟩ := hzD
    haveI : Nonempty D.subscheme := ⟨p⟩
    have hDdim : topologicalKrullDim D.subscheme = ((e + 1 : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (j ≫ f) D hDc hZ
    -- the component through `C`
    obtain ⟨V₀, hV₀⟩ := exists_topDimIntegralSubscheme_mem_support k f j hZ D hDc p
    have hsupp := Stacks.Chow.supp_pushforwardStructureSheaf (D.subschemeι ≫ j)
    have hVdim : ∀ V : TopDimIntegralSubscheme ((Scheme.Modules.pushforward
        (D.subschemeι ≫ j)).obj (Stacks.Ample.unitModule D.subscheme)),
        topologicalKrullDim V.1.subscheme = ((e + 1 : ℕ) : WithBot ℕ∞) := by
      intro V
      refine V.2.2.2.trans ?_
      rw [hsupp, topologicalKrullDim_range_eq]
      exact hDdim
    have hcV₀ : Set.range c ⊆ Set.range V₀.1.subschemeι := by
      rw [V₀.1.range_subschemeι]
      rintro _ ⟨w, rfl⟩
      have hw : genericPoint C ⤳ w :=
        specializes_iff_mem_closure.mpr (by rw [(genericPoint_spec C).def]; trivial)
      have h1 := specializes_iff_mem_closure.mp (hw.map c.base.hom.continuous)
      refine (closure_minimal (Set.singleton_subset_iff.mpr ?_) V₀.1.support.isClosed) h1
      rw [← hz, ← hp]
      exact hV₀
    haveI := V₀.2.1
    have hpos₀ := ih V₀.1.subschemeι (hVdim V₀) hcV₀
    have hrec : 0 < intersectionNumber k f (D.subschemeι ≫ j) (e + 1) hDdim.le
        (lastFam L M e) := by
      refine intersectionNumber_pos_of_nonneg_of_pos_component k f (D.subschemeι ≫ j) (e + 1)
        hDdim _ (fun V => ?_) V₀ hpos₀
      haveI := V.2.1
      have h := mixed_nonneg_aux k f L M hM 1 hL1 e (e + 1) (by omega) V.1.subschemeι (hVdim V)
        (fun q => q ≠ Fin.last e) (by
          rw [Fin.sum_univ_castSucc]
          simp [(Fin.castSucc_lt_last _).ne])
      rwa [intersectionNumber_congr_family k f V.1.subschemeι (e + 1) (hVdim V).le
        (M := lastFam L M e) (funext fun q => by
          rw [lastFam_eq_ite]; unfold mixFam; by_cases hq : q = Fin.last e <;> simp [hq])] at h
    -- `n (M^{e+1} · L · Z) = (M^e · L · D)`
    set G : Fin (e + 1 + 1) → X.Modules := lastFam L M (e + 1) with hG
    set N : Fin (e + 1 + 1) → X.Modules :=
      Function.update G 0 (tensorPower X.presheaf X.ringCatSheaf.2 (G 0) (n : ℤ)) with hN
    haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
      isInvertible_update G 0 _
    have hNsucc : (fun t : Fin (e + 1) => N t.succ) = lastFam L M e := funext fun t =>
      (Function.update_of_ne (Fin.succ_ne_zero t) _ _).trans (Fin.cons_succ _ _ _)
    have hNiso : (Scheme.Modules.pullback j).obj (N 0) ≅
        (Stacks.Divisors.invertibleSheaf D : Z.Modules) :=
      eqToIso (congrArg (Scheme.Modules.pullback j).obj
          (Function.update_self (0 : Fin (e + 1 + 1)) _ G)) ≪≫
        Scheme.Modules.pullbackTensorPowerIso j (G 0) n ≪≫ eD
    have hBEU := intersectionNumber_eq_of_isEffectiveCartierDivisor k f j (e + 1) hZ.le N D
      hDdim.le hNiso
    rw [intersectionNumber_congr_family k f _ (e + 1) _ hNsucc] at hBEU
    have hmul := intersectionNumber_update_tensorPower k f j (e + 1 + 1) hZ.le G 0 n
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hprod : 0 < (n : ℤ) * intersectionNumber k f j (e + 1 + 1) hZ.le G := by
      rwa [← hmul, hBEU]
    exact pos_of_mul_pos_right hprod hn'.le

end Induction

end Positivity

variable (k : Type u) [Field k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [IsProper f]

/-- Every mixed intersection number of a nef `L` and an ample `M` is nonnegative. -/
private theorem sheafIntersectionNumber_nonneg_of_isNef
    (hW : MMP.Mori.IsProjectiveVariety k f) {d : ℕ} (hdim : topologicalKrullDim W = d)
    (L M : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]
    [Stacks.Ample.IsInvertibleModule W M] (hM : Stacks.Ample.IsAmple W M)
    (hL : IsNef k f L) (F : Fin d → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (F j)]
    (hF : ∀ j, F j = L ∨ F j = M) :
    0 ≤ sheafIntersectionNumber k f (𝟙 W) d hdim.le F := by
  classical
  have hFeq : F = mixFam L M (fun q => F q = M) := by
    funext q
    unfold mixFam
    split_ifs with h
    · exact h
    · exact (hF q).resolve_right h
  set s : ℕ := ∑ q, if F q = M then 1 else 0 with hs
  have hsd : s ≤ d := by
    calc s ≤ ∑ _q : Fin d, 1 := Finset.sum_le_sum fun q _ => by split_ifs <;> omega
      _ = d := by simp
  rw [sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_congr_family k f (𝟙 W) d hdim.le hFeq]
  refine mixed_nonneg_aux k f L M hM (d - s) (fun W' i _ _ hW' => ?_) s d (by omega) (𝟙 W)
    hdim (fun q => F q = M) hs.symm
  have h := sheafSelfIntersectionNumber_nonneg_of_isNef k f hW L hL W' i hW'
  unfold sheafSelfIntersectionNumber at h
  rwa [sheafIntersectionNumber_eq_intersectionNumber] at h

/-- `(L · M^{d-1}) > 0` for nef, not numerically trivial `L` and ample `M`. -/
private theorem sheafIntersectionNumber_pos_of_not_numericallyTrivial
    (hW : MMP.Mori.IsProjectiveVariety k f) {d : ℕ} (hdim : topologicalKrullDim W = d) (hd : 0 < d)
    (L M : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]
    [Stacks.Ample.IsInvertibleModule W M] (hM : Stacks.Ample.IsAmple W M)
    (hL : IsNef k f L)
    (hLtriv : ¬ ∀ (C : Scheme.{u}) (i : C ⟶ W) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ f)] (hC : topologicalKrullDim C = 1), degreeOn k f i hC.le L = 0)
    (F : Fin d → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (F j)]
    (hF0 : F ⟨0, hd⟩ = L) (hF : ∀ j, j ≠ ⟨0, hd⟩ → F j = M) :
    0 < sheafIntersectionNumber k f (𝟙 W) d hdim.le F := by
  classical
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  -- nonnegativity on curves
  have hL1 : ∀ (V : Scheme.{u}) (i : V ⟶ W) [IsClosedImmersion i] [IsIntegral V]
      (hV : topologicalKrullDim V = ((1 : ℕ) : WithBot ℕ∞)),
      0 ≤ intersectionNumber k f i 1 hV.le (fun _ => L) := by
    intro V i _ _ hV
    have h := hL V i (by exact_mod_cast hV)
    rw [MMP.Mori.degreeOn_eq_invertibleCurveDegree,
      ← intersectionNumber_one_eq_invertibleCurveDegree] at h
    exact h
  -- a curve of positive degree
  obtain ⟨C, c, _, _, hC, hc⟩ : ∃ (C : Scheme.{u}) (c : C ⟶ W) (_ : IsClosedImmersion c)
      (_ : IsIntegral C) (hC : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞)),
      0 < intersectionNumber k f c 1 hC.le (fun _ => L) := by
    by_contra hcon
    apply hLtriv
    intro C i _ _ _ hC
    have h0 := hL C i hC
    have hnot : ¬ 0 < degreeOn k f i hC.le L := fun hpos => hcon ⟨C, i, inferInstance,
      inferInstance, by exact_mod_cast hC, by
        rw [MMP.Mori.degreeOn_eq_invertibleCurveDegree,
          ← intersectionNumber_one_eq_invertibleCurveDegree] at hpos
        exact hpos⟩
    omega
  have key := intersectionNumber_lastFam_pos k f L M hM hL1 c hC hc e (𝟙 W) hdim
    (by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩)
  rw [sheafIntersectionNumber_eq_intersectionNumber,
    ← intersectionNumber_comp_perm k f (𝟙 W) (e + 1) hdim.le F Fin.revPerm]
  have h0 : (⟨0, hd⟩ : Fin (e + 1)) = 0 := by ext; simp
  rw [intersectionNumber_congr_family k f (𝟙 W) (e + 1) hdim.le (M := lastFam L M e)
    (funext fun q => ?_)]
  · exact key
  rw [lastFam_eq_ite, Fin.revPerm_apply]
  by_cases hq : q = Fin.last e
  · subst hq
    rw [if_pos rfl, Fin.rev_last, ← h0, hF0]
  · rw [if_neg hq]
    refine hF _ fun h => hq ?_
    rw [← Fin.rev_rev q, h, h0, Fin.rev_zero]

end MMP.Mori.Internal.LcBpfNefVolumeGrowth

namespace MMP.Mori

open MMP.Mori.Internal.LcBpfNefVolumeGrowth in
/-- **Unbounded volume in a nontrivial nef direction.** Let `W` be a projective variety of
dimension `d > 0` over `k`, `L` a nef invertible sheaf on `W` which is not numerically trivial and
`M` an ample invertible sheaf. For every real `q > 0`, the top intersection number
`(tL + qM)^d` tends to `+∞` as `t → +∞`. -/
@[mmp "lem_mmp_lc_bpf_nef_volume_growth"]
public theorem tendsto_sheafCombinationIntersectionNumber_atTop_of_isNef
    (k : Type u) [Field k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [IsProper f]
    (hW : IsProjectiveVariety k f) {d : ℕ} (hdim : topologicalKrullDim W = d) (hd : 0 < d)
    (L M : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]
    [Stacks.Ample.IsInvertibleModule W M] (hM : Stacks.Ample.IsAmple W M)
    (hL : IsNef k f L)
    (hLtriv : ¬ ∀ (C : Scheme.{u}) (i : C ⟶ W) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ f)] (hC : topologicalKrullDim C = 1), degreeOn k f i hC.le L = 0)
    {q : ℝ} (hq : 0 < q) :
    haveI : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (![L, M] j) := by
      intro j; fin_cases j <;> assumption
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![] : Fin 0 → W.Modules) j) := fun j => j.elim0
    Tendsto (fun t : ℝ => sheafCombinationIntersectionNumber k f (𝟙 W) ℝ ![t, q] ![L, M] d ![]
      (by rw [hdim]; simp)) atTop atTop := by
  haveI : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (![L, M] j) := by
    intro j; fin_cases j <;> assumption
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((![] : Fin 0 → W.Modules) j) := fun j => j.elim0
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hdim' : topologicalKrullDim W = ((n + 1 + 0 : ℕ) : WithBot ℕ∞) := hdim
  have happ : ∀ (a : Fin (n + 1) → W.Modules) (j : Fin (n + 1 + 0)),
      Fin.append a (![] : Fin 0 → W.Modules) j = a j := by
    intro a j
    simp [Fin.append_right_nil]
  have hfam : ∀ (J : Fin (n + 1) → Fin 2) (j : Fin (n + 1 + 0)),
      Fin.append (fun s => ![L, M] (J s)) (![] : Fin 0 → W.Modules) j = L ∨
        Fin.append (fun s => ![L, M] (J s)) (![] : Fin 0 → W.Modules) j = M := by
    intro J j
    rw [happ]
    generalize J j = a
    fin_cases a <;> simp
  set J₀ : Fin (n + 1) → Fin 2 := Fin.cons 0 fun _ => 1 with hJ₀
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_mul_const (r := q ^ n *
    ((@sheafIntersectionNumber k _ W W f _ (𝟙 W) _ (n + 1 + 0) hdim'.le
      (Fin.append (fun s => ![L, M] (J₀ s)) (![] : Fin 0 → W.Modules))
      (isInvertible_finAppend _ _) : ℤ) : ℝ)) ?_)
  · filter_upwards [eventually_ge_atTop 0] with t ht
    unfold sheafCombinationIntersectionNumber
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun J _ => ?_) (Finset.mem_univ J₀))
    · simp [hJ₀, Fin.prod_univ_succ]
      ring
    · refine mul_nonneg (Finset.prod_nonneg fun s _ => ?_) ?_
      · generalize J s = a
        fin_cases a
        · exact ht
        · exact hq.le
      · exact_mod_cast @sheafIntersectionNumber_nonneg_of_isNef k _ W f _ hW _ hdim' L M _ _ _
          hM hL _ (isInvertible_finAppend _ _) (hfam J)
  · refine mul_pos (pow_pos hq n) ?_
    exact_mod_cast @sheafIntersectionNumber_pos_of_not_numericallyTrivial k _ W f _ hW _ hdim'
      (by omega) L M _ _ _ hM hL hLtriv _ (isInvertible_finAppend _ _)
      ((happ _ _).trans (by simp [hJ₀]))
      (fun j hj => by
        obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hj
        exact (happ _ _).trans (by simp [hJ₀]))

end MMP.Mori

end

/-!
## Lifting order-one transformations from a transverse smooth divisor

Let `(V, (I_1, …, I_m), E)` be an ordered divisor tuple over a field `k` and let `H ⊆ V` be a
smooth divisor such that `H + E` is a simple normal crossing divisor and no `I_j` vanishes
identically on an irreducible component of `H`. Restricting along `ι : H ↪ V` gives the tuple
`(H, (I_1|_H, …, I_m|_H), E|_H)`. Every sequence of order-one transformations of the restricted
tuple, with centres `C_0 ⊆ H_0 = H`, `C_1 ⊆ H_1 = Bl_{C_0} H`, …, lifts to a sequence of order-one
transformations of the ambient tuple with the same centres: the `i`-th ambient centre is the
scheme-theoretic image `(ι_i)_* C_i` of `C_i` along the closed immersion `ι_i : H_i → V_i`, where
`ι_0 = ι` and `ι_{i+1}` is the canonical lift of `ι_i` (identifying `H_{i+1}` with the strict
transform of `H_i`), and its inverse image along `ι_i` is `C_i` again. Moreover restricting to
the strict transform commutes with every step: the restriction along `ι_{i+1}` of each
transformed ambient ideal is the corresponding transformed ideal of the restricted tuple, and the
restriction of the transformed ambient boundary has the same support as the transformed
boundary of the restricted tuple.

### Main results

* `MMP.Resolution.OrderedDivisorTuple.exists_isPushforward_transform_restrict`: the lifting.

### Implementation notes

The sequences are `MMP.Resolution.ClosedBlowupSequence`s and the lifted sequence is a
push-forward in the sense of `MMP.Resolution.ClosedBlowupSequence.IsPushforward`. The
conditions along a sequence are stated by recursion on the sequence on `H`: the condition that
each centre is a centre of an order-one transformation
(`MMP.Resolution.OrderedDivisorTuple.IsTransformCentre`) of the current tuple, and, for the lift,
that the pushed-forward centre is one for the current ambient tuple, pulls back to the given
centre, and that restriction along the canonical lift commutes with the transformation.

The boundaries are compared as divisors, by their supports `MMP.Resolution.OrderedDivisor.support`,
not entry by entry: the ordering of the entries is not preserved. On `𝔸²` with `E = (y = 0)` and
`H = (x = 0)`, blowing up the origin `C` of `H` adds no new entry on `H`, since `C` is a
component of `E|_H`, so the transformed boundary on `H` is `((y), 𝒪_H)`; on `𝔸²` the strict
transform of `(y = 0)` misses the strict transform of `H` and the exceptional divisor is a new
last entry, so the restricted boundary is `(𝒪, (y))`. The supports agree.

### References

* [J. Kollár, *Semi log resolutions*, arXiv:0812.3592, Proposition 6]
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MMP.Resolution MMP.Resolution.OrderedDivisorTuple

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Resolution.Internal.TupleRestrictionLift

/-- The tuple of the source restricted along a morphism `ι : S → W`. -/
public abbrev restrictTuple {S W : Scheme.{v}} (ι : S ⟶ W) (T : OrderedDivisorTuple W) :
    OrderedDivisorTuple S :=
  ⟨T.m, fun j => (T.I j).comap ι, T.E.comap ι⟩

/-- `B` is a sequence of order-one transformations of the tuple `T`. -/
private def IsTransformSeq {k : Type v} [Field k] {S : Scheme.{v}} (B : ClosedBlowupSequence S) :
    (S ⟶ Spec (.of k)) → OrderedDivisorTuple S → Prop :=
  ClosedBlowupSequence.rec
    (motive := fun S _ => (S ⟶ Spec (.of k)) → OrderedDivisorTuple S → Prop)
    (fun _ _ _ => True)
    (fun Z _ ih s TS => TS.IsTransformCentre s Z ∧ ih (blowUpToBase Z ≫ s) (TS.transform Z)) B

private theorem isTransformSeq_cons {k : Type v} [Field k] {S : Scheme.{v}}
    (Z : S.IdealSheafData) (B : ClosedBlowupSequence (blowUp Z)) (s : S ⟶ Spec (.of k))
    (T : OrderedDivisorTuple S) :
    IsTransformSeq (.cons Z B) s T ↔
      T.IsTransformCentre s Z ∧ IsTransformSeq B (blowUpToBase Z ≫ s) (T.transform Z) :=
  Iff.rfl

/-- The conclusion of the lifting along a sequence `B` on `S`, for `ι : S → W`. -/
private def LiftClause {k : Type v} [Field k] {S : Scheme.{v}} (B : ClosedBlowupSequence S) :
    ∀ W : Scheme.{v}, (S ⟶ W) → (W ⟶ Spec (.of k)) → OrderedDivisorTuple W → Prop :=
  ClosedBlowupSequence.rec
    (motive := fun S _ => ∀ W : Scheme.{v}, (S ⟶ W) → (W ⟶ Spec (.of k)) →
      OrderedDivisorTuple W → Prop)
    (fun _ _ ι s TW => IsClosedImmersion ι ∧ IsOrderedDivisorTuple s TW ∧
      IsSNCFamily s fun o : Option (Fin TW.E.s) => o.elim ι.ker TW.E.E)
    (fun Z _ ih W ι s TW =>
      TW.IsTransformCentre s (Z.map ι) ∧
        ∃ h : (Z.map ι).comap ι = Z,
          (∀ j, ((TW.transform (Z.map ι)).I j).comap
              (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι)) =
            ((restrictTuple ι TW).transform Z).I j) ∧
          ((TW.transform (Z.map ι)).E.comap
              (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι))).support =
            ((restrictTuple ι TW).transform Z).E.support ∧
          ih (blowUp (Z.map ι))
            (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι))
            (blowUpToBase (Z.map ι) ≫ s) (TW.transform (Z.map ι))) B

/-- The invariant carried along the induction: `ι` is a closed immersion, `T` is an ordered
divisor tuple, and the image of `ι` together with the boundary of `T` is snc. -/
@[expose] public def LiftInvariant {k : Type v} [Field k] {S W : Scheme.{v}} (ι : S ⟶ W)
    (s : W ⟶ Spec (.of k)) (T : OrderedDivisorTuple W) : Prop :=
  IsClosedImmersion ι ∧ IsOrderedDivisorTuple s T ∧
    IsSNCFamily s fun o : Option (Fin T.E.s) => o.elim ι.ker T.E.E

/-- Composing with the identification of blow-ups along equal centres does not change the
blow-down map. -/
public theorem eqToHom_comp_blowUpToBase {X : Scheme.{v}} {A B : X.IdealSheafData} (h : A = B) :
    eqToHom (congrArg blowUp h.symm) ≫ blowUpToBase A = blowUpToBase B := by
  subst h; simp

/-! ### Ideal-theoretic helpers -/

/-- In a ring, multiplying by a principal ideal generated by a regular element and dividing by it
again gives back the ideal. -/
public theorem span_singleton_mul_colon_cancel {A : Type*} [CommRing A] {b : A}
    (hb : IsRegular b) (K : Ideal A) :
    (Ideal.span {b} * K).colon ((Ideal.span {b} : Ideal A) : Set A) = K := by
  rw [Ideal.colon_span]
  ext a
  rw [Submodule.mem_colon_singleton, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨c, hc, he⟩
    have : c = a := hb.1 (by simpa [smul_eq_mul, mul_comm] using he)
    exact this ▸ hc
  · intro ha
    exact ⟨a, ha, by simp [smul_eq_mul, mul_comm]⟩

/-- Dividing `F * K` by an effective Cartier divisor `F` gives back `K`. -/
public theorem idealColon_mul_cancel {X : Scheme.{v}} (F K : X.IdealSheafData)
    (hF : Stacks.Divisors.IsEffectiveCartierDivisor F) : idealColon (F * K) F = K := by
  have hfg := AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor F hF
  have hcol : idealColon (F * K) F = Scheme.IdealSheafData.colon (F * K) F hfg := by
    unfold idealColon
    exact Scheme.IdealSheafData.ofIdeals_ideal (Scheme.IdealSheafData.colon (F * K) F hfg)
  rw [hcol]
  choose U hU hxU b hb hgen using fun x : X =>
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor F hF x
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun x : X => (⟨U x, hU x⟩ : X.affineOpens)) ?_ fun x => ?_
  · exact top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩
  · rw [Scheme.IdealSheafData.ideal_colon, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hgen x]
    exact span_singleton_mul_colon_cancel (hb x) _

/-- If `F` is an effective Cartier divisor and `A ≤ F`, then `F * (A : F) = A`. -/
public theorem mul_idealColon_eq {X : Scheme.{v}} (F A : X.IdealSheafData)
    (hF : Stacks.Divisors.IsEffectiveCartierDivisor F) (hAF : A ≤ F) :
    F * idealColon A F = A := by
  have hfg := AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor F hF
  have hcol : idealColon A F = Scheme.IdealSheafData.colon A F hfg := by
    unfold idealColon
    exact Scheme.IdealSheafData.ofIdeals_ideal (Scheme.IdealSheafData.colon A F hfg)
  rw [hcol]
  exact AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor _ _ hF hAF

/-- An ideal sheaf whose cosupport contains a closed subscheme `C` having snc with some family is
contained in the ideal of `C`: the stalks of `C` are prime. -/
public theorem le_of_hasSNCWith_of_support_subset {X : Scheme.{v}} [IsLocallyNoetherian X]
    {Λ : Type*} {E : Λ → X.IdealSheafData} {C I : X.IdealSheafData} (hC : HasSNCWith E C)
    (h : (C.support : Set X) ⊆ I.support) : I ≤ C := by
  refine IdealSheafData.le_of_stalk_le _ _ fun x => ?_
  by_cases hx : x ∈ (C.support : Set X)
  · obtain ⟨n, z, c, J, hz, -, -, hJ⟩ := hC x hx
    let P : PrimeSpectrum (X.presheaf.stalk x) :=
      ⟨_, span_image_isPrime_of_isRegularSystemOfParameters hz J⟩
    have h1 : X.fromSpecStalk x P ∈ (C.support : Set X) :=
      (fromSpecStalk_mem_support_iff_stalk_le C x P).2 hJ.le
    rw [hJ]
    exact (fromSpecStalk_mem_support_iff_stalk_le I x P).1 (h h1)
  · rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support C x).2 hx]
    exact le_top

/-! ### Closed immersions and local coordinates -/

/-- The kernel of the stalk map of a closed immersion at `y` is the stalk at `ι y` of its
kernel. -/
public theorem ker_stalkMap_eq_stalk_ker {S W : Scheme.{v}} (ι : S ⟶ W) [IsClosedImmersion ι]
    (y : S) : RingHom.ker (ι.stalkMap y).hom = IdealSheafData.stalk ι.ker (ι y) := by
  have key : ∀ (K : W.IdealSheafData) (t : S ⟶ K.subscheme) [IsIso t],
      RingHom.ker ((t ≫ K.subschemeι).stalkMap y).hom =
        IdealSheafData.stalk K ((t ≫ K.subschemeι) y) := by
    intro K t _
    have : IsIso (t.stalkMap y) :=
      (IsOpenImmersion.iff_isIso_stalkMap.1 (IsOpenImmersion.of_isIso t)).2 y
    rw [Scheme.Hom.stalkMap_comp]
    change RingHom.ker ((t.stalkMap y).hom.comp (K.subschemeι.stalkMap (t y)).hom) =
      IdealSheafData.stalk K (K.subschemeι (t y))
    rw [RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (t.stalkMap y)).1]
    exact Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk K (t y)
  have e : ι.toImage ≫ ι.ker.subschemeι = ι := ι.toImage_imageι
  have := key ι.ker ι.toImage
  rwa [e] at this

/-- **Local coordinates on a smooth hypersurface `H = ι(S)` adapted to the restricted boundary.**
If `H + ∑ᵢ E^i` is an snc family, `H` the image of a closed immersion `ι : S → W`, then at every
point of `S` the inverse images `ι⁻¹E^i` through it are distinct coordinate hyperplanes. -/
public theorem exists_coordinates_comap_of_isSNCFamily {k : Type v} [Field k] {S W : Scheme.{v}}
    [IsLocallyNoetherian W] (ι : S ⟶ W) [IsClosedImmersion ι] (s : W ⟶ Spec (.of k))
    {n₀ : ℕ} (E : Fin n₀ → W.IdealSheafData)
    (hHE : IsSNCFamily s fun o : Option (Fin n₀) => o.elim ι.ker E) (y : S) :
    ∃ (m : ℕ) (w : Fin m → S.presheaf.stalk y)
      (c' : {i // y ∈ ((E i).comap ι).support} → Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((E i.1).comap ι) y = Ideal.span {w (c' i)}) ∧
        Function.Injective c' := by
  classical
  have hxH : ι y ∈ ((Option.elim none ι.ker E : W.IdealSheafData).support : Set W) :=
    ι.range_subset_ker_support ⟨y, rfl⟩
  obtain ⟨n, z, c, hz, hE, hc⟩ := hHE.2 (ι y)
  set J : Finset (Fin n) := {c ⟨none, hxH⟩} with hJdef
  have hZx : IdealSheafData.stalk ι.ker (ι y) = Ideal.span (z '' (J : Set (Fin n))) := by
    rw [hJdef, Finset.coe_singleton, Set.image_singleton]
    exact hE ⟨none, hxH⟩
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hq⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  let e : (W.presheaf.stalk (ι y) ⧸ Ideal.span (z '' (J : Set (Fin n)))) ≃+*
      S.presheaf.stalk y :=
    (Ideal.quotEquivOfEq (hZx.symm.trans (ker_stalkMap_eq_stalk_ker ι y).symm)).trans
      (RingHom.quotientKerEquivOfSurjective (ι.stalkMap_surjective y))
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = (ι.stalkMap y).hom a := fun a => rfl
  have hmem : ∀ i : {i // y ∈ ((E i).comap ι).support},
      ι y ∈ ((Option.elim (some i.1) ι.ker E : W.IdealSheafData).support : Set W) :=
    fun i => (mem_support_comap_iff _ _ y).1 i.2
  have hnot : ∀ i : {i // y ∈ ((E i).comap ι).support}, c ⟨some i.1, hmem i⟩ ∈ Jᶜ := by
    intro i
    rw [Finset.mem_compl, hJdef, Finset.mem_singleton]
    intro h
    exact Option.some_ne_none _ (congrArg Subtype.val (hc h))
  let o := Jᶜ.orderIsoOfFin rfl
  refine ⟨Jᶜ.card, fun j => e (Ideal.Quotient.mk _ (z (Jᶜ.orderEmbOfFin rfl j))),
    fun i => o.symm ⟨c ⟨some i.1, hmem i⟩, hnot i⟩, hq.map_ringEquiv e, fun i => ?_, ?_⟩
  · dsimp only
    rw [IdealSheafData.stalk_comap, show IdealSheafData.stalk (E i.1) (ι y) =
        Ideal.span {z (c ⟨some i.1, hmem i⟩)} from hE ⟨some i.1, hmem i⟩, Ideal.map_span,
      Set.image_singleton, he, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · intro i j hij
    exact Subtype.ext (Option.some_injective _
      (congrArg Subtype.val (hc (congrArg Subtype.val (o.symm.injective hij)))))

/-- The entries of the restricted boundary are of pure codimension one. -/
public theorem isPureCodimOne_comap_of_isSNCFamily {k : Type v} [Field k] {S W : Scheme.{v}}
    [IsLocallyNoetherian W] (ι : S ⟶ W) [IsClosedImmersion ι] (s : W ⟶ Spec (.of k))
    {n₀ : ℕ} (E : Fin n₀ → W.IdealSheafData)
    (hHE : IsSNCFamily s fun o : Option (Fin n₀) => o.elim ι.ker E) (i : Fin n₀) :
    MMP.Mori.IsPureCodimOne ((E i).comap ι).support := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian ι
  refine isPureCodimOne_support_of_stalk_eq_span_parameter _ fun y hy => ?_
  obtain ⟨m, w, c', hw, hc', -⟩ := exists_coordinates_comap_of_isSNCFamily ι s E hHE y
  exact ⟨m, w, c' ⟨i, hy⟩, hw, hc' ⟨i, hy⟩⟩

/-- The total transform of a closed subset `A` under a blow-up is the inverse image of `A ∪ Z`. -/
public theorem totalTransformStep_eq {X : Scheme.{v}} (Z : X.IdealSheafData) {A : Set X}
    (hA : IsClosed A) :
    ClosedBlowupSequence.totalTransformStep Z A = blowUpToBase Z ⁻¹' (A ∪ Z.support) := by
  apply subset_antisymm
  · rintro y (hy | hy)
    · exact Or.inl (closure_minimal (fun y hy => hy.1) (hA.preimage (blowUpToBase Z).continuous) hy)
    · exact Or.inr hy
  · rintro y (hy | hy)
    · by_cases hyZ : blowUpToBase Z y ∈ (Z.support : Set X)
      · exact Or.inr hyZ
      · exact Or.inl (subset_closure ⟨hy, hyZ⟩)
    · exact Or.inr hy

/-- The support of the inverse image of an ordered divisor is the preimage of its support. -/
public theorem support_comap_orderedDivisor {X Y : Scheme.{v}} (E : OrderedDivisor X)
    (f : Y ⟶ X) : (E.comap f).support = f ⁻¹' E.support := by
  ext y
  simp [OrderedDivisor.support, OrderedDivisor.comap, Scheme.IdealSheafData.support_comap]

/-- **Exchanging coordinates.** Let `A` and `B` be families of ideal sheaves with the same union
of supports, and `y` a point at which the members of `A` through `y` are distinct coordinate
hyperplanes for some regular system of parameters `v`, and the members of `B` through `y` are
coordinate hyperplanes for a regular system of parameters `w`. Then the members of `A` through
`y` are distinct coordinate hyperplanes for `w`. -/
public theorem exists_coordinates_of_iUnion_support_eq {X : Scheme.{v}} [IsLocallyNoetherian X]
    {ΛA ΛB : Type*} {A : ΛA → X.IdealSheafData} {B : ΛB → X.IdealSheafData}
    (hAB : (⋃ i, ((A i).support : Set X)) = ⋃ j, ((B j).support : Set X)) (y : X)
    {n : ℕ} {v : Fin n → X.presheaf.stalk y} (hv : MMP.Mori.IsRegularSystemOfParameters v)
    (d : {i // y ∈ (A i).support} → Fin n)
    (hd : ∀ i, IdealSheafData.stalk (A i.1) y = Ideal.span {v (d i)}) (hdinj : Function.Injective d)
    {m : ℕ} {w : Fin m → X.presheaf.stalk y} (hw : MMP.Mori.IsRegularSystemOfParameters w)
    (c : {j // y ∈ (B j).support} → Fin m)
    (hc : ∀ j, IdealSheafData.stalk (B j.1) y = Ideal.span {w (c j)}) :
    ∃ c' : {i // y ∈ (A i).support} → Fin m,
      (∀ i, IdealSheafData.stalk (A i.1) y = Ideal.span {w (c' i)}) ∧ Function.Injective c' := by
  have key : ∀ i : {i // y ∈ (A i).support}, ∃ j : {j // y ∈ (B j).support},
      IdealSheafData.stalk (A i.1) y = Ideal.span {w (c j)} := by
    intro i
    let P : PrimeSpectrum (X.presheaf.stalk y) :=
      ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hv (d i)⟩
    have hP : X.fromSpecStalk y P ∈ ⋃ j, ((B j).support : Set X) := by
      rw [← hAB]
      exact Set.mem_iUnion.2 ⟨i.1, (fromSpecStalk_mem_support_iff_stalk_le _ y P).2 (hd i).le⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hP
    have hyj : y ∈ (B j).support :=
      (fromSpecStalk_specializes_self y P).mem_closed (B j).support.isClosed hj
    have hjP := (fromSpecStalk_mem_support_iff_stalk_le _ y P).1 hj
    rw [hc ⟨j, hyj⟩] at hjP
    let Q : PrimeSpectrum (X.presheaf.stalk y) :=
      ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hw (c ⟨j, hyj⟩)⟩
    have hQ : X.fromSpecStalk y Q ∈ ⋃ i, ((A i).support : Set X) := by
      rw [hAB]
      exact Set.mem_iUnion.2 ⟨j, (fromSpecStalk_mem_support_iff_stalk_le _ y Q).2
        (hc ⟨j, hyj⟩).le⟩
    obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hQ
    have hyl : y ∈ (A l).support :=
      (fromSpecStalk_specializes_self y Q).mem_closed (A l).support.isClosed hl
    have hlQ := (fromSpecStalk_mem_support_iff_stalk_le _ y Q).1 hl
    rw [hd ⟨l, hyl⟩] at hlQ
    have hdl : d ⟨l, hyl⟩ = d i := by
      by_contra hne
      exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hv (Ne.symm hne)
        (hjP (hlQ (Ideal.subset_span rfl)))
    refine ⟨⟨j, hyj⟩, ?_⟩
    rw [hd i]
    refine le_antisymm ?_ hjP
    rw [← hdl]
    exact hlQ
  choose j hj using key
  refine ⟨fun i => c (j i), hj, fun i₁ i₂ h => ?_⟩
  have h1 : Ideal.span {v (d i₁)} = Ideal.span {v (d i₂)} := by
    rw [← hd, ← hd, hj, hj]
    exact congrArg (fun a => Ideal.span {w a}) h
  apply hdinj
  by_contra hne
  exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hv hne
    (by rw [h1]; exact Ideal.subset_span rfl)

/-- **Snc inside the image of a closed immersion lifts** (the argument of
`MMP.Resolution.Kollar.hasSNCWith_cons_of_hasSNCWith_comap`, for a closed immersion
`ι : S → X` with image `H`). If `H + ∑ᵢ E^i` is an snc family, `Z ⊆ X` a closed subscheme
contained in `H` (that is, `ker ι ≤ Z`) and `ι⁻¹Z` has simple normal crossings with `ι⁻¹E`,
then `Z` has simple normal crossings with `E`. -/
public theorem hasSNCWith_of_hasSNCWith_comap {k : Type v} [Field k] {S X : Scheme.{v}}
    [IsLocallyNoetherian X] (ι : S ⟶ X) [IsClosedImmersion ι] (sX : X ⟶ Spec (.of k))
    {n₀ : ℕ} (E : Fin n₀ → X.IdealSheafData)
    (hHE : IsSNCFamily sX fun o : Option (Fin n₀) => o.elim ι.ker E)
    (Z : X.IdealSheafData) (hZH : ι.ker ≤ Z)
    (hZ : HasSNCWith (fun i => (E i).comap ι) (Z.comap ι)) :
    HasSNCWith E Z := by
  intro x hx
  have hxH : x ∈ (ι.ker.support : Set X) := Scheme.IdealSheafData.support_antitone hZH hx
  have hr : (ι.ker.support : Set X) = Set.range ι := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  obtain ⟨y, rfl⟩ : x ∈ Set.range ι := hr ▸ hxH
  have hyZ : y ∈ ((Z.comap ι).support : Set S) := (mem_support_comap_iff _ _ y).2 hx
  obtain ⟨n, w, c', J', hw, hwE, hwinj, hwZ⟩ := hZ y hyZ
  obtain ⟨n₁, z₀, c₀, hz₀, hz₀E, hz₀inj⟩ := hHE.2 (ι y)
  have hx0 : ι y ∈ ((Option.elim none ι.ker E : X.IdealSheafData).support : Set X) := hxH
  set φ := (ι.stalkMap y).hom with hφdef
  have hφ : Function.Surjective φ := ι.stalkMap_surjective y
  have hker : RingHom.ker φ = Ideal.span {z₀ (c₀ ⟨none, hx0⟩)} := by
    rw [hφdef, ker_stalkMap_eq_stalk_ker]
    exact hz₀E ⟨none, hx0⟩
  have hsupp : ∀ i, y ∈ ((E i).comap ι).support ↔ ι y ∈ (E i).support :=
    fun i => mem_support_comap_iff _ _ y
  have hxs : ∀ i : {i : Fin n₀ // y ∈ ((E i).comap ι).support},
      ι y ∈ ((Option.elim (some i.1) ι.ker E : X.IdealSheafData).support : Set X) :=
    fun i => (hsupp i.1).1 i.2
  have hE : ∀ i ∈ (Set.univ : Set {i : Fin n₀ // y ∈ ((E i).comap ι).support}),
      Ideal.span {w (c' i)} = (Ideal.span {z₀ (c₀ ⟨some i.1, hxs i⟩)}).map φ := by
    intro i _
    rw [← hwE i]
    show IdealSheafData.stalk ((E i.1).comap ι) y = _
    rw [IdealSheafData.stalk_comap]
    exact congrArg (Ideal.map φ) (hz₀E ⟨some i.1, hxs i⟩)
  have hinj : ∀ i ∈ (Set.univ : Set {i : Fin n₀ // y ∈ ((E i).comap ι).support}),
      ∀ i' ∈ (Set.univ : Set {i : Fin n₀ // y ∈ ((E i).comap ι).support}),
      c' i = c' i' → i = i' :=
    fun i _ i' _ h => hwinj h
  obtain ⟨t, ht, ht0, htφ, htE⟩ := MMP.Mori.exists_lift_isRegularSystemOfParameters φ hφ hz₀
    (c₀ ⟨none, hx0⟩) hker hw c' (fun i => z₀ (c₀ ⟨some i.1, hxs i⟩)) _ hE hinj
  refine ⟨n + 1, t, fun i => (c' ⟨i.1, (hsupp i.1).2 i.2⟩).succ,
    insert 0 (J'.image Fin.succ), ht, ?_, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    rw [htE ⟨i, (hsupp i).2 hi⟩ trivial]
    exact hz₀E ⟨some i, hi⟩
  · rintro ⟨i, hi⟩ ⟨i', hi'⟩ h
    have := congrArg Subtype.val (hwinj (Fin.succ_injective _ h))
    exact Subtype.ext this
  · have h1 : IdealSheafData.stalk Z (ι y) =
        Ideal.comap φ (Ideal.span (w '' (J' : Set (Fin n)))) := by
      rw [← hwZ, IdealSheafData.stalk_comap, Ideal.comap_map_of_surjective φ hφ]
      have h3 : IdealSheafData.stalk ι.ker (ι y) ≤ IdealSheafData.stalk Z (ι y) :=
        stalk_le_stalk_of_le hZH _
      have h4 : Ideal.comap φ ⊥ = IdealSheafData.stalk ι.ker (ι y) := by
        rw [← ker_stalkMap_eq_stalk_ker]; rfl
      rw [h4]
      exact (sup_eq_left.mpr h3).symm
    rw [h1]
    have h5 : w '' (J' : Set (Fin n)) = φ '' ((fun k => t k.succ) '' (J' : Set (Fin n))) := by
      rw [Set.image_image]
      simp only [htφ]
    have hk : Ideal.comap φ ⊥ = Ideal.span {z₀ (c₀ ⟨none, hx0⟩)} := hker
    rw [h5, ← Ideal.map_span, Ideal.comap_map_of_surjective φ hφ, hk, ← ht0, ← Ideal.span_union]
    congr 1
    ext a
    simp only [Finset.coe_insert, Finset.coe_image, Set.image_insert_eq, Set.image_image,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto

open IsLocalRing MMP.Mori in
/-- **The entries of `π⁻¹_*H + π⁻¹_tot(E)` at a point of the blow-up.** Let `H + ∑ᵢ E^i` be a
family whose members through every point are distinct coordinate hyperplanes, and `Z ⊆ H` a
closed subscheme having simple normal crossings with `H + ∑ᵢ E^i`. At every point `x'` of
`B_ZX` there are local coordinates `w` and an assignment `d` of at most one coordinate to the
strict transform `π⁻¹(H ∖ Z)‾` of `H` and to every entry of `π⁻¹_tot(E)`, distinct sets getting
distinct coordinates, such that on `Spec 𝒪_{B,x'}` each set is `(w_{d(o)} = 0)` (empty if it has
no coordinate). This is `MMP.Resolution.exists_assignment_totalTransformSet` with the strict
transform of `H` added. -/
public theorem exists_assignment_strictTransform {X : Scheme.{v}} [IsLocallyNoetherian X]
    [CompactSpace X] (E : OrderedDivisor X) (H : X.IdealSheafData)
    (hE : ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x)
      (c : {i // x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) H E.E) i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk ((Fin.cons (α := fun _ => X.IdealSheafData) H E.E) i.1) x =
          Ideal.span {z (c i)}) ∧ Function.Injective c)
    {Z : X.IdealSheafData} (hZ : HasSNCWith (Fin.cons (α := fun _ => X.IdealSheafData) H E.E) Z)
    (hHZ : (Z.support : Set X) ⊆ H.support) (x' : blowUp Z) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (d : Option (Fin (E.s + 1)) → Option (Fin N)),
      MMP.Mori.IsRegularSystemOfParameters w ∧
      (∀ o (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        (blowUp Z).fromSpecStalk x' p ∈ closure (Option.elim o
          (blowUpToBase Z ⁻¹' ((H.support : Set X) \ Z.support)) (totalTransformSet E Z)) ↔
          ∃ c, d o = some c ∧ w c ∈ p.asIdeal) ∧
      (∀ o o' c, d o = some c → d o' = some c → o = o') := by
  classical
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  set π := blowUpToBase Z
  set x := π x'
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x'
  have key : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      π (f' p) = X.fromSpecStalk x (PrimeSpectrum.comap φ p) :=
    fun p => apply_fromSpecStalk π x' p
  have hspec : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), π (f' p) ⤳ x := fun p => by
    rw [key]; exact fromSpecStalk_specializes_self x _
  have hZ2c : IsClosed (componentsOfCodimAtLeastTwo (Z.support : Set X)) :=
    isClosed_componentsOfCodimAtLeastTwo Z.support.isClosed
  have hZ2Z : componentsOfCodimAtLeastTwo (Z.support : Set X) ⊆ Z.support := by
    intro y hy
    simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at hy
    obtain ⟨W, hW, -, hyW⟩ := hy
    exact hW.1.2 hyW
  have hCL : ∀ (i : Fin E.s) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
      f' p ∈ closure (totalTransformSet E Z (Fin.castSucc i)) ↔
        ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
          π (f' q) ∈ ((E.E i).support : Set X) ∧
            π (f' q) ∉ componentsOfCodimAtLeastTwo (Z.support : Set X) := by
    intro i p
    simp only [totalTransformSet, Fin.snoc_castSucc]
    exact fromSpecStalk_mem_closure_preimage_diff_iff x' (E.E i).support.isClosed hZ2c p
  have hLZ : totalTransformSet E Z (Fin.last E.s) ⊆ π ⁻¹' (Z.support : Set X) := by
    intro y hy
    simp only [totalTransformSet, Fin.snoc_last, Set.mem_iUnion] at hy
    obtain ⟨W, hW, -, hyW⟩ := hy
    exact hW.1.2 hyW
  have hHL : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      f' p ∈ closure (π ⁻¹' ((H.support : Set X) \ Z.support)) ↔
        ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
          π (f' q) ∈ (H.support : Set X) ∧ π (f' q) ∉ (Z.support : Set X) := fun p =>
    fromSpecStalk_mem_closure_preimage_diff_iff x' H.support.isClosed Z.support.isClosed p
  by_cases hx : x ∈ (Z.support : Set X)
  · -- the point lies over the centre
    obtain ⟨n, z, cc, J, hz, hcc, hinjc, hJ⟩ := hZ x hx
    have hxH : x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) H E.E 0).support : Set X) := by
      simpa using hHZ hx
    have hxs : ∀ i : {i // x ∈ (E.E i).support},
        x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) H E.E i.1.succ).support : Set X) :=
      fun i => by simpa using i.2
    set a := cc ⟨0, hxH⟩ with ha
    have hcH : IdealSheafData.stalk H x = Ideal.span {z a} := by simpa using hcc ⟨0, hxH⟩
    obtain ⟨c, hc, hinj, hac⟩ : ∃ c : {i // x ∈ (E.E i).support} → Fin n,
        (∀ i, IdealSheafData.stalk (E.E i.1) x = Ideal.span {z (c i)}) ∧
          Function.Injective c ∧ ∀ i, c i ≠ a := by
      refine ⟨fun i => cc ⟨i.1.succ, hxs i⟩, fun i => by simpa using hcc ⟨i.1.succ, hxs i⟩,
        fun i j h => ?_, fun i h => ?_⟩
      · have := congrArg Subtype.val (hinjc h)
        exact Subtype.ext (Fin.succ_injective _ this)
      · exact Fin.succ_ne_zero _ (congrArg Subtype.val (hinjc h))
    obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, hU, hwi₀, hout, hin, hunit, hσ₀⟩ :=
      exists_chart_coordinates Z x' hx hz hJ
    have hwi₀' : w i₀ = φ (z m) := hwi₀
    have hout' : ∀ j ∉ J, w (σ j) = φ (z j) := hout
    have hin' : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀ := hin
    have hunit' : ∀ j ∈ U, ∃ u, IsUnit u ∧ φ (z j) = u * w i₀ := hunit
    have := isRegularLocalRing_of_isRegularSystemOfParameters hz
    have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
    have := isRegularLocalRing_of_isRegularSystemOfParameters hw
    have := IsRegularLocalRing.isDomain ((blowUp Z).presheaf.stalk x')
    have hφinj : Function.Injective φ := injective_stalkMap_blowUpToBase Z x'
    have hJ' : IdealSheafData.stalk Z x = (coordPrime hz J).asIdeal := hJ
    set W₀ := closure {X.fromSpecStalk x (coordPrime hz J)}
    set b : Prop := ∃ hW : IsIrreducible W₀, 2 ≤ codimension (irreducibleClosure hW)
    set b' : Prop := W₀ ∉ componentsOf E.support
    have hUJ : ∀ j ∈ U, j ∈ J ∧ j ≠ m := fun j hj =>
      ⟨(Finset.mem_erase.1 (hU hj)).2, (Finset.mem_erase.1 (hU hj)).1⟩
    have hJm : ¬ b → ∀ j ∈ J, j = m := by
      intro hnb j hj
      by_contra hjm
      exact hnb ⟨isIrreducible_singleton.closure,
        two_le_codimension_closure_coordPrime hz hj hmJ hjm _⟩
    -- membership in `Z`, `Z^{≥2}`, `E^i` and the last entry, on `Spec 𝒪_{B,x'}`
    have mZ : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        (coordPrime hz J).asIdeal ≤ (PrimeSpectrum.comap φ q).asIdeal ↔ w i₀ ∈ q.asIdeal := by
      intro q
      change Ideal.span (z '' (J : Set (Fin n))) ≤ _ ↔ _
      rw [Ideal.span_le]
      constructor
      · intro h
        rw [hwi₀]
        exact h ⟨m, hmJ, rfl⟩
      · rintro h _ ⟨j, hj, rfl⟩
        change φ (z j) ∈ q.asIdeal
        by_cases hjm : j = m
        · rwa [hjm, ← hwi₀]
        by_cases hjU : j ∈ U
        · obtain ⟨u, -, hu⟩ := hunit j hjU
          rw [hu]
          exact Ideal.mul_mem_left _ _ h
        · rw [hin j hj hjm hjU]
          exact Ideal.mul_mem_left _ _ h
    have mZ2 : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' q) ∈ componentsOfCodimAtLeastTwo (Z.support : Set X) ↔
        b ∧ w i₀ ∈ q.asIdeal := by
      intro q
      rw [key, componentsOfCodimAtLeastTwo_eq,
        fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ' hx _ _, mZ]
    have mL : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        f' p ∈ closure (totalTransformSet E Z (Fin.last E.s)) ↔
        b' ∧ w i₀ ∈ p.asIdeal := by
      have hLeq : totalTransformSet E Z (Fin.last E.s) = π ⁻¹'
          (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
            (_ : W ∉ componentsOf E.support), W) := by
        simp only [totalTransformSet, Fin.snoc_last, Set.preimage_iUnion]
        rfl
      have hLc : IsClosed (totalTransformSet E Z (Fin.last E.s)) := by
        rw [hLeq]
        exact (isClosed_biUnion_componentsOf Z.support.isClosed _).preimage π.continuous
      intro p
      rw [hLc.closure_eq, hLeq, Set.mem_preimage, key,
        fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ' hx _ _, mZ]
    have mE : ∀ (i : Fin E.s) (q : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        π (f' q) ∈ ((E.E i).support : Set X) ↔
        ∃ h : x ∈ (E.E i).support, φ (z (c ⟨i, h⟩)) ∈ q.asIdeal := by
      intro i q
      constructor
      · intro h
        have hxi : x ∈ (E.E i).support := (hspec q).mem_closed (E.E i).support.isClosed h
        refine ⟨hxi, ?_⟩
        rw [key, fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩] at h
        exact h (Ideal.subset_span rfl)
      · rintro ⟨hxi, h⟩
        rw [key, fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩, Ideal.span_le,
          Set.singleton_subset_iff]
        exact h
    -- the coordinate hyperplane `(w_j = 0)`
    let P₀ : Fin N → PrimeSpectrum ((blowUp Z).presheaf.stalk x') := fun j =>
      ⟨Ideal.span {w j}, span_singleton_isPrime_of_isRegularSystemOfParameters hw j⟩
    have hP₀ : ∀ j, j ≠ i₀ → w i₀ ∉ (P₀ j).asIdeal := fun j hj =>
      notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hj
    -- distinct indices outside `U ∪ {m}` give distinct coordinates
    have hσinj : ∀ a a', a ≠ m → a ∉ U → a' ≠ m → a' ∉ U → σ a = σ a' → a = a' := by
      have hval : ∀ a, a ≠ m → a ∉ U →
          (a ∉ J ∧ φ (z a) = w (σ a)) ∨ (a ∈ J ∧ φ (z a) = w (σ a) * w i₀) := by
        intro a ham haU
        by_cases haJ : a ∈ J
        · exact Or.inr ⟨haJ, hin a haJ ham haU⟩
        · exact Or.inl ⟨haJ, (hout a haJ).symm⟩
      intro a a' ham haU ham' haU' hσ
      by_contra hne
      rcases hval a ham haU with ⟨-, ha⟩ | ⟨-, ha⟩ <;>
        rcases hval a' ham' haU' with ⟨-, ha'⟩ | ⟨-, ha'⟩
      · exact ne_of_isRegularSystemOfParameters hz hne (hφinj (by rw [ha, ha', hσ]))
      · -- `z_{a'} = z_a z_m`
        have : z a' = z a * z m := hφinj (by rw [ha', map_mul, ha, hσ, hwi₀])
        exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne
          (this ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      · have : z a = z a' * z m := hφinj (by rw [ha, map_mul, ha', hσ, hwi₀])
        exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz (Ne.symm hne)
          (this ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      · exact ne_of_isRegularSystemOfParameters hz hne (hφinj (by rw [ha, ha', hσ]))
    let dE : Fin E.s → Option (Fin N) := fun i =>
      if h : x ∈ (E.E i).support then
        (if c ⟨i, h⟩ = m then (if b then none else some i₀)
          else if c ⟨i, h⟩ ∈ U then none else some (σ (c ⟨i, h⟩)))
      else none
    let d : Fin (E.s + 1) → Option (Fin N) :=
      Fin.snoc (α := fun _ => Option (Fin N)) dE (if b' then some i₀ else none)
    have hdE : ∀ i c₀, dE i = some c₀ → ∃ h : x ∈ (E.E i).support,
        (c ⟨i, h⟩ = m ∧ ¬ b ∧ c₀ = i₀) ∨
          (c ⟨i, h⟩ ≠ m ∧ c ⟨i, h⟩ ∉ U ∧ c₀ = σ (c ⟨i, h⟩)) := by
      intro i c₀ h
      simp only [dE] at h
      split_ifs at h with h1 h2 h3 h4
      · exact ⟨h1, Or.inl ⟨h2, h3, (Option.some_inj.1 h).symm⟩⟩
      · exact ⟨h1, Or.inr ⟨h2, h4, (Option.some_inj.1 h).symm⟩⟩
    have hmemE : ∀ (i : Fin (E.s + 1)) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        f' p ∈ closure (totalTransformSet E Z i) ↔ ∃ c, d i = some c ∧ w c ∈ p.asIdeal := by
      intro i p
      induction i using Fin.lastCases with
      | last =>
        rw [mL]
        simp only [d, Fin.snoc_last]
        split_ifs with h
        · simp [h]
        · simp [h]
      | cast i =>
        rw [hCL]
        simp only [d, Fin.snoc_castSucc, dE]
        by_cases hxi : x ∈ (E.E i).support
        · rw [dite_eq_left hxi]
          set a := c ⟨i, hxi⟩
          have hEq : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
              π (f' q) ∈ ((E.E i).support : Set X) ↔ φ (z a) ∈ q.asIdeal := fun q =>
            (mE i q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hxi, h⟩⟩
          have key2 : (∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
              q.asIdeal ≤ p.asIdeal ∧ π (f' q) ∈ ((E.E i).support : Set X) ∧
                π (f' q) ∉ componentsOfCodimAtLeastTwo (Z.support : Set X)) ↔
              ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
                q.asIdeal ≤ p.asIdeal ∧ φ (z a) ∈ q.asIdeal ∧ ¬ (b ∧ w i₀ ∈ q.asIdeal) :=
            exists_congr fun q => and_congr_right fun _ => and_congr (hEq q) (not_congr (mZ2 q))
          rw [key2]
          by_cases ham : a = m
          · rw [ite_eq_left ham]
            have hza : φ (z a) = w i₀ := by rw [ham]; exact hwi₀'.symm
            rw [hza]
            by_cases hbb : b
            · rw [ite_eq_left hbb]
              constructor
              · rintro ⟨q, -, h1, h2⟩; exact absurd ⟨hbb, h1⟩ h2
              · rintro ⟨c', hc', -⟩
                exact absurd hc' (by simp)
            · rw [ite_eq_right hbb]
              constructor
              · rintro ⟨q, hq, h1, -⟩; exact ⟨i₀, rfl, hq h1⟩
              · rintro ⟨c', hc', h⟩
                obtain rfl := Option.some_inj.1 hc'
                exact ⟨p, le_rfl, h, fun h' => hbb h'.1⟩
          rw [ite_eq_right ham]
          by_cases haU : a ∈ U
          · rw [ite_eq_left haU]
            constructor
            · rintro ⟨q, -, h1, h2⟩
              obtain ⟨haJ, -⟩ := hUJ a haU
              by_cases hbb : b
              · obtain ⟨u, hu, hu'⟩ := hunit' a haU
                rw [hu'] at h1
                refine absurd ⟨hbb, (q.isPrime.mem_or_mem h1).resolve_left fun h' => ?_⟩ h2
                exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
              · exact absurd (hJm hbb a haJ) ham
            · rintro ⟨c', hc', -⟩
              exact absurd hc' (by simp)
          rw [ite_eq_right haU]
          have hσ : σ a ≠ i₀ := hσ₀ a ham haU
          constructor
          · rintro ⟨q, hq, h1, h2⟩
            refine ⟨σ a, rfl, hq ?_⟩
            by_cases haJ : a ∈ J
            · rw [hin' a haJ ham haU] at h1
              by_cases hbb : b
              · exact (q.isPrime.mem_or_mem h1).resolve_right fun h' => h2 ⟨hbb, h'⟩
              · exact absurd (hJm hbb a haJ) ham
            · rwa [hout' a haJ]
          · rintro ⟨c', hc', h⟩
            obtain rfl := Option.some_inj.1 hc'
            refine ⟨P₀ (σ a), (Ideal.span_singleton_le_iff_mem _).2 h, ?_,
              fun h' => hP₀ (σ a) hσ h'.2⟩
            by_cases haJ : a ∈ J
            · rw [hin' a haJ ham haU]
              exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
            · rw [← hout' a haJ]
              exact Ideal.subset_span rfl
        · rw [dite_eq_right hxi]
          constructor
          · rintro ⟨q, -, h1, -⟩
            exact absurd ((hspec q).mem_closed (E.E i).support.isClosed h1) hxi
          · rintro ⟨c', hc', -⟩
            exact absurd hc' (by simp)
    have hlast : ∀ c₀, d (Fin.last E.s) = some c₀ → b' ∧ c₀ = i₀ := by
      intro c₀ h
      simp only [d, Fin.snoc_last] at h
      split_ifs at h with hb'
      exact ⟨hb', (Option.some_inj.1 h).symm⟩
    have hinjE : ∀ i j c₀, d i = some c₀ → d j = some c₀ → i = j := by
      have hcross : ∀ i c₀, dE i = some c₀ → b' → c₀ ≠ i₀ := by
        intro i c₀ hi hbb' hc₀
        obtain ⟨hxi, ⟨ham, hnb, -⟩ | ⟨ham, haU, hc₀'⟩⟩ := hdE i c₀ hi
        · have hJc : J = {c ⟨i, hxi⟩} := by
            rw [ham]
            exact Finset.eq_singleton_iff_unique_mem.2 ⟨hmJ, hJm hnb⟩
          exact hbb' (closure_coordPrime_mem_componentsOf_iUnion hz E.E c hc ⟨i, hxi⟩ hJc)
        · exact hσ₀ _ ham haU (hc₀' ▸ hc₀)
      intro i j c₀ hi hj
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j =>
          obtain ⟨hbb', rfl⟩ := hlast _ hi
          simp only [d, Fin.snoc_castSucc] at hj
          exact absurd rfl (hcross j _ hj hbb')
      | cast i =>
        simp only [d, Fin.snoc_castSucc] at hi
        induction j using Fin.lastCases with
        | last =>
          obtain ⟨hbb', rfl⟩ := hlast _ hj
          exact absurd rfl (hcross i _ hi hbb')
        | cast j =>
          simp only [d, Fin.snoc_castSucc] at hj
          congr 1
          obtain ⟨hxi, hi'⟩ := hdE i c₀ hi
          obtain ⟨hxj, hj'⟩ := hdE j c₀ hj
          have hcij : c ⟨i, hxi⟩ = c ⟨j, hxj⟩ := by
            rcases hi' with ⟨hai, -, hci⟩ | ⟨hai, haU, hci⟩ <;>
              rcases hj' with ⟨haj, -, hcj⟩ | ⟨haj, haU', hcj⟩
            · rw [hai, haj]
            · exact absurd (hcj ▸ hci) (hσ₀ _ haj haU')
            · exact absurd (hci ▸ hcj) (hσ₀ _ hai haU)
            · exact hσinj _ _ hai haU haj haU' (hci ▸ hcj)
          exact congrArg Subtype.val (hinj hcij)
    -- the strict transform of `H`
    have mH : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' q) ∈ (H.support : Set X) ↔ φ (z a) ∈ q.asIdeal := by
      intro q
      rw [key, fromSpecStalk_mem_support_iff_stalk_le, hcH, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Iff.rfl
    have mZq : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' q) ∈ (Z.support : Set X) ↔ w i₀ ∈ q.asIdeal := by
      intro q
      rw [key, fromSpecStalk_mem_support_iff_stalk_le, hJ']
      exact mZ q
    let dH : Option (Fin N) := if a = m then none else if a ∈ U then none else some (σ a)
    have hmemH : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        f' p ∈ closure (π ⁻¹' ((H.support : Set X) \ Z.support)) ↔
          ∃ c, dH = some c ∧ w c ∈ p.asIdeal := by
      intro p
      rw [hHL]
      by_cases ham : a = m
      · simp only [dH, if_pos ham]
        constructor
        · rintro ⟨q, -, h1, h2⟩
          rw [mH, ham, ← hwi₀'] at h1
          exact absurd ((mZq q).2 h1) h2
        · rintro ⟨c', hc', -⟩
          exact absurd hc' (by simp)
      by_cases haU : a ∈ U
      · simp only [dH, if_neg ham, if_pos haU]
        constructor
        · rintro ⟨q, -, h1, h2⟩
          obtain ⟨u, hu, hu'⟩ := hunit' a haU
          rw [mH, hu'] at h1
          refine absurd ((mZq q).2 ((q.isPrime.mem_or_mem h1).resolve_left fun h' => ?_)) h2
          exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
        · rintro ⟨c', hc', -⟩
          exact absurd hc' (by simp)
      simp only [dH, if_neg ham, if_neg haU]
      have hσ : σ a ≠ i₀ := hσ₀ a ham haU
      have hval : φ (z a) = w (σ a) ∨ φ (z a) = w (σ a) * w i₀ := by
        by_cases haJ : a ∈ J
        · exact Or.inr (hin' a haJ ham haU)
        · exact Or.inl (hout' a haJ).symm
      constructor
      · rintro ⟨q, hq, h1, h2⟩
        refine ⟨σ a, rfl, hq ?_⟩
        rw [mH] at h1
        rw [mZq] at h2
        rcases hval with hv | hv
        · rwa [hv] at h1
        · rw [hv] at h1
          exact (q.isPrime.mem_or_mem h1).resolve_right h2
      · rintro ⟨c', hc', h⟩
        obtain rfl := Option.some_inj.1 hc'
        refine ⟨P₀ (σ a), (Ideal.span_singleton_le_iff_mem _).2 h, ?_,
          fun h' => hP₀ (σ a) hσ ((mZq _).1 h')⟩
        rw [mH]
        rcases hval with hv | hv
        · rw [hv]; exact Ideal.subset_span rfl
        · rw [hv]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hinjH : ∀ i c₀, dH = some c₀ → d i = some c₀ → False := by
      intro i c₀ hH hi
      have hHv : a ≠ m ∧ a ∉ U ∧ c₀ = σ a := by
        simp only [dH] at hH
        split_ifs at hH with h1 h2
        exact ⟨h1, h2, (Option.some_inj.1 hH).symm⟩
      obtain ⟨ham, haU, rfl⟩ := hHv
      induction i using Fin.lastCases with
      | last => exact hσ₀ a ham haU (hlast _ hi).2
      | cast i =>
        simp only [d, Fin.snoc_castSucc] at hi
        obtain ⟨hxi, ⟨-, -, hci⟩ | ⟨hai, haU', hci⟩⟩ := hdE i _ hi
        · exact hσ₀ a ham haU hci
        · exact hac ⟨i, hxi⟩ (hσinj _ _ hai haU' ham haU hci.symm)
    refine ⟨N, w, fun o => o.elim dH d, hw, ?_, ?_⟩
    · rintro (_ | i) p
      · exact hmemH p
      · exact hmemE i p
    · rintro (_ | i) (_ | j) c₀ hi hj
      · rfl
      · exact (hinjH j c₀ hi hj).elim
      · exact (hinjH i c₀ hj hi).elim
      · exact congrArg some (hinjE i j c₀ hi hj)
  · -- the point lies off the centre: `π` is an isomorphism near `x'`
    obtain ⟨n, z, cc, hz, hcc, hinjc⟩ := hE x
    have hxs : ∀ i : {i // x ∈ (E.E i).support},
        x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) H E.E i.1.succ).support : Set X) :=
      fun i => by simpa using i.2
    obtain ⟨c, hc, hinj, hac⟩ : ∃ c : {i // x ∈ (E.E i).support} → Fin n,
        (∀ i, IdealSheafData.stalk (E.E i.1) x = Ideal.span {z (c i)}) ∧
          Function.Injective c ∧ ∀ i h0, c i ≠ cc ⟨0, h0⟩ := by
      refine ⟨fun i => cc ⟨i.1.succ, hxs i⟩, fun i => by simpa using hcc ⟨i.1.succ, hxs i⟩,
        fun i j h => ?_, fun i h0 h => ?_⟩
      · have := congrArg Subtype.val (hinjc h)
        exact Subtype.ext (Fin.succ_injective _ this)
      · exact Fin.succ_ne_zero _ (congrArg Subtype.val (hinjc h))
    have hiso : IsIso (π.stalkMap x') :=
      isIso_stalkMap_of_isIso_morphismRestrict π (isIso_blowUpToBase_restrict_compl_support Z)
        (show x' ∈ π ⁻¹ᵁ Z.support.compl from hx)
    let e := (asIso (π.stalkMap x')).commRingCatIsoToRingEquiv
    have hw : IsRegularSystemOfParameters fun i => φ (z i) :=
      isRegularSystemOfParameters_map_ringEquiv e hz
    have hnZ : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' q) ∉ (Z.support : Set X) := fun q h =>
      hx ((hspec q).mem_closed Z.support.isClosed h)
    have mE : ∀ (i : Fin E.s) (q : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        π (f' q) ∈ ((E.E i).support : Set X) ↔
        ∃ h : x ∈ (E.E i).support, φ (z (c ⟨i, h⟩)) ∈ q.asIdeal := by
      intro i q
      constructor
      · intro h
        have hxi : x ∈ (E.E i).support := (hspec q).mem_closed (E.E i).support.isClosed h
        refine ⟨hxi, ?_⟩
        rw [key, fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩] at h
        exact h (Ideal.subset_span rfl)
      · rintro ⟨hxi, h⟩
        rw [key, fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩, Ideal.span_le,
          Set.singleton_subset_iff]
        exact h
    let dE : Fin E.s → Option (Fin n) := fun i =>
      if h : x ∈ (E.E i).support then some (c ⟨i, h⟩) else none
    let d : Fin (E.s + 1) → Option (Fin n) := Fin.snoc (α := fun _ => Option (Fin n)) dE none
    have hmemE : ∀ (i : Fin (E.s + 1)) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        f' p ∈ closure (totalTransformSet E Z i) ↔
          ∃ c, d i = some c ∧ (fun i => φ (z i)) c ∈ p.asIdeal := by
      intro i p
      induction i using Fin.lastCases with
      | last =>
        simp only [d, Fin.snoc_last, reduceCtorEq, false_and, exists_false, iff_false]
        intro h
        have h' := closure_minimal hLZ (Z.support.isClosed.preimage π.continuous) h
        exact hnZ p h'
      | cast i =>
        rw [hCL]
        simp only [d, Fin.snoc_castSucc, dE]
        by_cases hxi : x ∈ (E.E i).support
        · simp only [hxi, dite_true, Option.some.injEq, exists_eq_left']
          constructor
          · rintro ⟨q, hq, h1, -⟩
            obtain ⟨_, h1⟩ := (mE i q).1 h1
            exact hq h1
          · intro h
            exact ⟨p, le_rfl, (mE i p).2 ⟨hxi, h⟩, fun h' => hnZ p (hZ2Z h')⟩
        · simp only [hxi, dite_false, reduceCtorEq, false_and, exists_false, iff_false]
          rintro ⟨q, -, h1, -⟩
          exact hxi ((hspec q).mem_closed (E.E i).support.isClosed h1)
    have hinjE : ∀ i j c₀, d i = some c₀ → d j = some c₀ → i = j := by
      intro i j c₀ hi hj
      induction i using Fin.lastCases with
      | last => simp [d] at hi
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [d] at hj
        | cast j =>
          simp only [d, Fin.snoc_castSucc, dE] at hi hj
          split_ifs at hi hj with hxi hxj
          congr 1
          exact congrArg Subtype.val (hinj ((Option.some_inj.1 hi).trans
            (Option.some_inj.1 hj).symm))

    have h0 : ∀ h : x ∈ (H.support : Set X),
        x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) H E.E 0).support : Set X) :=
      fun h => by simpa using h
    let dH : Option (Fin n) := if h : x ∈ (H.support : Set X) then some (cc ⟨0, h0 h⟩) else none
    have hmemH : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        f' p ∈ closure (π ⁻¹' ((H.support : Set X) \ Z.support)) ↔
          ∃ c, dH = some c ∧ (fun i => φ (z i)) c ∈ p.asIdeal := by
      intro p
      rw [hHL]
      by_cases hxH : x ∈ (H.support : Set X)
      · simp only [dH, dif_pos hxH]
        have hcH : IdealSheafData.stalk H x = Ideal.span {z (cc ⟨0, h0 hxH⟩)} := by
          simpa using hcc ⟨0, h0 hxH⟩
        have mH : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
            π (f' q) ∈ (H.support : Set X) ↔ φ (z (cc ⟨0, h0 hxH⟩)) ∈ q.asIdeal := by
          intro q
          rw [key, fromSpecStalk_mem_support_iff_stalk_le, hcH, Ideal.span_le,
            Set.singleton_subset_iff]
          exact Iff.rfl
        constructor
        · rintro ⟨q, hq, h1, -⟩
          exact ⟨_, rfl, hq ((mH q).1 h1)⟩
        · rintro ⟨c', hc', h⟩
          obtain rfl := Option.some_inj.1 hc'
          exact ⟨p, le_rfl, (mH p).2 h, hnZ p⟩
      · simp only [dH, dif_neg hxH]
        constructor
        · rintro ⟨q, -, h1, -⟩
          exact absurd ((hspec q).mem_closed H.support.isClosed h1) hxH
        · rintro ⟨c', hc', -⟩
          exact absurd hc' (by simp)
    have hinjH : ∀ i c₀, dH = some c₀ → d i = some c₀ → False := by
      intro i c₀ hH hi
      simp only [dH] at hH
      split_ifs at hH with hxH
      induction i using Fin.lastCases with
      | last => simp [d] at hi
      | cast i =>
        simp only [d, Fin.snoc_castSucc, dE] at hi
        split_ifs at hi with hxi
        exact hac ⟨i, hxi⟩ (h0 hxH) ((Option.some_inj.1 hi).trans (Option.some_inj.1 hH).symm)
    refine ⟨n, fun i => φ (z i), fun o => o.elim dH d, hw, ?_, ?_⟩
    · rintro (_ | i) p
      · exact hmemH p
      · exact hmemE i p
    · rintro (_ | i) (_ | j) c₀ hi hj
      · rfl
      · exact (hinjH j c₀ hi hj).elim
      · exact (hinjH i c₀ hj hi).elim
      · exact congrArg some (hinjE i j c₀ hi hj)

/-! ### The strict transform of the hypersurface -/

/-- The complement of the exceptional divisor is dense in a blow-up: every generic point of
`B_ZX` lies off `π⁻¹(Z)`. -/
public theorem closure_preimage_compl_support_eq_univ {X : Scheme.{v}} (Z : X.IdealSheafData) :
    closure (blowUpToBase Z ⁻¹' (Z.support : Set X)ᶜ) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨Y, hY, hxY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have hYc : IsClosed Y := isClosed_of_mem_irreducibleComponents Y hY
  have hgen := (hY.1 : IsIrreducible Y).isGenericPoint_genericPoint_closure
  rw [hYc.closure_eq] at hgen
  set η := (hY.1 : IsIrreducible Y).genericPoint
  have hη : η ∈ genericPoints (blowUp Z) := by
    show closure {η} ∈ irreducibleComponents (blowUp Z)
    rw [hgen.def]
    exact hY
  obtain ⟨-, hZ⟩ := (bijOn_genericPoints_blowUpToBase Z).1 hη
  have hηV : η ∈ blowUpToBase Z ⁻¹' (Z.support : Set X)ᶜ := fun h =>
    hZ (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 h)
  have hxη : x ∈ closure {η} := by rw [hgen.def]; exact hxY rfl
  exact closure_mono (Set.singleton_subset_iff.2 hηV) hxη

/-- **The image of the strict transform.** For a closed immersion `j : S → X` and a closed
subscheme `Z ⊆ X`, the image of the canonical lift `B_{j⁻¹Z}S → B_ZX` is the closure of
`π⁻¹(j(S) ∖ Z)`. -/
public theorem range_canonicalLift_eq_closure {S X : Scheme.{v}} (j : S ⟶ X)
    [IsClosedImmersion j] (Z : X.IdealSheafData) :
    Set.range (canonicalLift j Z) =
      closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X))) := by
  set f := canonicalLift j Z with hf
  set T : Set (blowUp Z) := blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)) with hT
  have hsq : ∀ v, blowUpToBase Z (f v) = j (blowUpToBase (Z.comap j) v) := fun v ↦ by
    rw [← Scheme.Hom.comp_apply, hf, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  have : IsClosedImmersion f := Bridges.isClosedImmersion_canonicalLift j Z
  set V : Set (blowUp (Z.comap j)) :=
    blowUpToBase (Z.comap j) ⁻¹' ((Z.comap j).support : Set S)ᶜ with hV
  have hVdense : closure V = Set.univ := closure_preimage_compl_support_eq_univ (Z.comap j)
  have himage : f '' V = T := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨_, (hsq v).symm⟩, ?_⟩
      rw [hsq v]
      simpa [hV] using hv
    · rintro ⟨⟨s, hs⟩, hyZ⟩
      have hs' : s ∉ ((Z.comap j).support : Set S) := by
        simpa [hs] using hyZ
      obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap j) hs'
      refine ⟨v, by simpa [hV, hv] using hs', ?_⟩
      have hfv : blowUpToBase Z (f v) = blowUpToBase Z y := by rw [hsq v, hv, hs]
      exact blowUpToBase_injective_of_notMem_support Z (by rwa [hfv]) hfv
  apply subset_antisymm
  · rw [← Set.image_univ, ← hVdense, ← himage]
    exact image_closure_subset_closure_image f.continuous
  · rw [← himage]
    exact closure_minimal (Set.image_subset_range _ _) f.isClosedEmbedding.isClosed_range

/-- For a closed immersion `j : S → X` of a reduced scheme, the kernel of the canonical lift is the
reduced ideal of the closure of `π⁻¹(j(S) ∖ Z)`. -/
public theorem ker_canonicalLift_eq_vanishingIdeal {S X : Scheme.{v}} (j : S ⟶ X)
    [IsClosedImmersion j] [IsReduced S] (Z : X.IdealSheafData) :
    (canonicalLift j Z).ker = Scheme.IdealSheafData.vanishingIdeal
      (.closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)))) := by
  have : IsReduced (blowUp (Z.comap j)) := isReduced_blowUp (Z.comap j)
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, range_canonicalLift_eq_closure]
  congr 1
  exact TopologicalSpace.Closeds.ext (by
    rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure,
      closure_closure])

/-- An snc family stays one after reindexing along an injective map. -/
public theorem isSNCFamily_comp {k : Type v} [Field k] {X : Scheme.{v}} {s : X ⟶ Spec (.of k)}
    {Λ Λ' : Type*} {E : Λ → X.IdealSheafData} (h : IsSNCFamily s E) (g : Λ' → Λ)
    (hg : Function.Injective g) : IsSNCFamily s (E ∘ g) := by
  refine ⟨fun i => h.1 (g i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h.2 x
  exact ⟨n, z, fun i => c ⟨g i.1, i.2⟩, hz, fun i => hc ⟨g i.1, i.2⟩,
    fun i j hij => Subtype.ext (hg (congrArg Subtype.val (hinj hij)))⟩

/-! ### The steps of the induction -/

/-- The inverse image of the scheme-theoretic image along a closed immersion. -/
public theorem comap_map_of_isClosedImmersion {S W : Scheme.{v}} (ι : S ⟶ W)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) : (Z.map ι).comap ι = Z := by
  have hp : IsPullback Z.subschemeι (𝟙 _) ι (Z.subschemeι ≫ ι) := by
    have h1 : IsPullback (𝟙 S) (𝟙 S) ι ι := IsKernelPair.id_of_mono ι
    have h2 : IsPullback Z.subschemeι (𝟙 _) (𝟙 S) Z.subschemeι :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    simpa using h2.paste_horiz h1
  have he : Limits.pullback.fst ι (Z.subschemeι ≫ ι) = hp.isoPullback.inv ≫ Z.subschemeι := by
    simp
  rw [Scheme.IdealSheafData.map, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, he,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- A centre having snc with the restricted boundary pushes forward to a centre having snc with
the ambient boundary: at `x` take coordinates `(h, z_2, …, z_n)` with `H = (h)` and the ambient
boundary components coordinate hyperplanes, and lift the coordinates of the centre on `H`. -/
public theorem hasSNCWith_map {k : Type v} [Field k] {S W : Scheme.{v}} {ι : S ⟶ W}
    {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {ES : OrderedDivisor S} (hES : ES.support = (T.E.comap ι).support) {Z : S.IdealSheafData}
    (hZ : HasSNCWith ES.E Z) :
    HasSNCWith T.E.E (Z.map ι) := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian ι
  have hZ' : HasSNCWith (fun i => (T.E.E i).comap ι) Z := by
    intro y hy
    obtain ⟨n, w, c', J, hw, hwE, -, hwZ⟩ := hZ y hy
    obtain ⟨m, v, d, hv, hvE, hd⟩ :=
      exists_coordinates_comap_of_isSNCFamily ι s T.E.E hinv.2.2 y
    obtain ⟨c'', hc'', hinj⟩ := exists_coordinates_of_iUnion_support_eq
      (A := fun i => (T.E.E i).comap ι) (B := ES.E) hES.symm y hv d hvE hd hw c' hwE
    exact ⟨n, w, c'', J, hw, hc'', hinj, hwZ⟩
  have h := comap_map_of_isClosedImmersion ι Z
  exact hasSNCWith_of_hasSNCWith_comap ι s T.E.E hinv.2.2 (Z.map ι)
    (Scheme.Hom.le_ker_comp Z.subschemeι ι) (h.symm ▸ hZ')

/-- A centre of an order-one transformation of the restricted tuple pushes forward to a centre
of an order-one transformation of the ambient tuple. -/
public theorem isTransformCentre_map {k : Type v} [Field k] {S W : Scheme.{v}} {ι : S ⟶ W}
    {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {ES : OrderedDivisor S} (hES : ES.support = (T.E.comap ι).support) {Z : S.IdealSheafData}
    (hZ : (⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple S).IsTransformCentre
      (ι ≫ s) Z) :
    T.IsTransformCentre s (Z.map ι) := by
  have : IsClosedImmersion ι := hinv.1
  exact ⟨isSmoothScheme_map_subschemeι_comp ι s Z hZ.1, hasSNCWith_map hinv hES hZ.2⟩

/-- Restriction to the strict transform commutes with the transformation of the ideals. -/
public theorem comap_transform_I {k : Type v} [Field k] {S W : Scheme.{v}} {ι : S ⟶ W}
    {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {Z : S.IdealSheafData} (hc : T.IsTransformCentre s (Z.map ι)) (h : (Z.map ι).comap ι = Z)
    (j : Fin T.m) :
    ((T.transform (Z.map ι)).I j).comap
        (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι)) =
      ((restrictTuple ι T).transform Z).I j := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have hsupp : ((Z.map ι).support : Set W) = ι '' Z.support := by
    rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure,
      (ι.isClosedEmbedding.isClosedMap _ Z.support.isClosed).closure_eq]
  have hiff : ((Z.map ι).support : Set W) ⊆ (T.I j).support ↔
      (Z.support : Set S) ⊆ ((T.I j).comap ι).support := by
    rw [hsupp, Set.image_subset_iff, Scheme.IdealSheafData.support_comap]
    rfl
  generalize Z.map ι = C at hc h hiff ⊢
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  by_cases hle : (C.support : Set W) ⊆ (T.I j).support
  · rw [transform_I_of_le _ _ _ hle]
    rw [show ((restrictTuple ι T).transform (C.comap ι)).I j = idealColon
        (((T.I j).comap ι).comap (blowUpToBase (C.comap ι)))
        ((C.comap ι).comap (blowUpToBase (C.comap ι))) from
      transform_I_of_le (restrictTuple ι T) _ j (hiff.1 hle)]
    have hF := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal C
    have hFH := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (C.comap ι)
    have hIC : T.I j ≤ C := le_of_hasSNCWith_of_support_subset hc.2 hle
    have hFG : C.comap (blowUpToBase C) * idealColon ((T.I j).comap (blowUpToBase C))
        (C.comap (blowUpToBase C)) = (T.I j).comap (blowUpToBase C) :=
      mul_idealColon_eq _ _ hF (Scheme.IdealSheafData.comap_mono _ hIC)
    have hFH' : Stacks.Divisors.IsEffectiveCartierDivisor
        ((C.comap (blowUpToBase C)).comap (canonicalLift ι C)) := by
      rw [Kollar.comap_canonicalLift_comap_blowUpToBase]
      exact hFH
    rw [← Kollar.comap_canonicalLift_comap_blowUpToBase ι C (T.I j),
      ← Kollar.comap_canonicalLift_comap_blowUpToBase ι C C]
    conv_rhs => rw [← hFG, AlgebraicGeometry.comap_mul]
    exact (idealColon_mul_cancel _ _ hFH').symm
  · rw [transform_I_of_not_le _ _ _ hle]
    rw [show ((restrictTuple ι T).transform (C.comap ι)).I j =
        ((T.I j).comap ι).comap (blowUpToBase (C.comap ι)) from
      transform_I_of_not_le (restrictTuple ι T) _ j (mt hiff.2 hle)]
    exact Kollar.comap_canonicalLift_comap_blowUpToBase ι C (T.I j)

/-- Restriction to the strict transform commutes with the total transform of the boundary, up
to support. -/
public theorem support_comap_transform_E {k : Type v} [Field k] {S W : Scheme.{v}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {Z : S.IdealSheafData} (hc : T.IsTransformCentre s (Z.map ι)) (h : (Z.map ι).comap ι = Z) :
    ((T.transform (Z.map ι)).E.comap
        (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι))).support =
      ((restrictTuple ι T).transform Z).E.support := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have hpW : ∀ i, MMP.Mori.IsPureCodimOne (T.E.E i).support := fun i =>
    (hinv.2.1.2.2.2.2.2.1 i).2.1
  have hpS : ∀ i, MMP.Mori.IsPureCodimOne ((T.E.comap ι).E i).support :=
    isPureCodimOne_comap_of_isSNCFamily ι s T.E.E hinv.2.2
  have hSE : IsClosed T.E.support :=
    isClosed_iUnion_of_finite fun i => (T.E.E i).support.isClosed
  generalize Z.map ι = C at hc h ⊢
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  rw [OrderedDivisorTuple.transform_E, OrderedDivisorTuple.transform_E,
    support_comap_orderedDivisor, OrderedDivisor.support_totalTransform _ hpW,
    OrderedDivisor.support_totalTransform _ hpS, totalTransformStep_eq _ hSE,
    totalTransformStep_eq _ ((support_comap_orderedDivisor T.E ι).symm ▸
      hSE.preimage ι.continuous), support_comap_orderedDivisor, Scheme.IdealSheafData.support_comap]
  ext y
  simp only [Set.mem_preimage, Set.mem_union, TopologicalSpace.Closeds.coe_preimage]
  rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]

/-- An ideal sheaf on an irreducible scheme whose support has pure codimension one is
nonzero. -/
public theorem ne_bot_of_isPureCodimOne_support {X : Scheme.{v}} [IrreducibleSpace X]
    (I : X.IdealSheafData) (h : MMP.Mori.IsPureCodimOne I.support) : I ≠ ⊥ := by
  rintro rfl
  let W₀ : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds X ↦
      (W' : Set X) ⊆ (⊥ : X.IdealSheafData).support) W₀ :=
    ⟨by simp [W₀], fun W _ _ x _ => Set.mem_univ (α := X) x⟩
  have h0 : codimension W₀ = 0 := by
    rw [codimension, Order.coheight_eq_zero]
    intro W _ x _
    exact Set.mem_univ (α := X) x
  simpa [h0] using h W₀ hmax

/-- The blow-up of the ambient variety along the pushed-forward centre is a variety. -/
private theorem isVariety_blowUp_map {k : Type v} [Field k] {S W : Scheme.{v}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {Z : S.IdealSheafData} :
    MMP.Mori.IsVariety k (blowUpToBase (Z.map ι) ≫ s) := by
  have hvar : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsIntegral W := hvar.toIsIntegral
  have hker : ι.ker ≠ ⊥ := ne_bot_of_isPureCodimOne_support _ (hinv.2.2.1 none).2.1
  have hne : Z.map ι ≠ ⊥ := fun h0 =>
    hker (eq_bot_iff.2 ((Scheme.Hom.le_ker_comp Z.subschemeι ι).trans (eq_bot_iff.1 h0)))
  exact (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational s
    (Z.map ι) hne).1

/-- The transformed ideals are nonzero and invertible. -/
private theorem transform_I_ne_bot_and_cartier {k : Type v} [Field k] {S W : Scheme.{v}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {Z : S.IdealSheafData} (hc : T.IsTransformCentre s (Z.map ι)) (j : Fin T.m) :
    (T.transform (Z.map ι)).I j ≠ ⊥ ∧
      Stacks.Divisors.IsEffectiveCartierDivisor ((T.transform (Z.map ι)).I j) := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have hvar := isVariety_blowUp_map (Z := Z) hinv
  have : IsIntegral (blowUp (Z.map ι)) := hvar.toIsIntegral
  have hIc := (hinv.2.1.2.2.2.1 j).2
  have hpb : Stacks.Divisors.IsEffectiveCartierDivisor
      ((T.I j).comap (blowUpToBase (Z.map ι))) :=
    AlgebraicGeometry.isPullbackDefined_blowUpToBase _ _ hIc
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor ((T.transform (Z.map ι)).I j) := by
    by_cases hle : ((Z.map ι).support : Set W) ⊆ (T.I j).support
    · rw [transform_I_of_le _ _ _ hle]
      have hF := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.map ι)
      have hIC : T.I j ≤ Z.map ι := le_of_hasSNCWith_of_support_subset hc.2 hle
      obtain ⟨E, hE, hEq⟩ := AlgebraicGeometry.exists_isEffectiveCartierDivisor_mul_eq_of_le
        _ _ hF hpb (Scheme.IdealSheafData.comap_mono _ hIC)
      rw [hEq, idealColon_mul_cancel _ _ hF]
      exact hE
    · rw [transform_I_of_not_le _ _ _ hle]
      exact hpb
  exact ⟨AlgebraicGeometry.ne_bot_of_isEffectiveCartierDivisor hcart, hcart⟩

/-- The strict transform of `H` together with the transformed boundary is snc. -/
public theorem isSNCFamily_transform {k : Type v} [Field k] {S W : Scheme.{v}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {Z : S.IdealSheafData} (hc : T.IsTransformCentre s (Z.map ι)) (h : (Z.map ι).comap ι = Z) :
    IsSNCFamily (blowUpToBase (Z.map ι) ≫ s) fun o : Option (Fin (T.transform (Z.map ι)).E.s) =>
      o.elim (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι)).ker
        (T.transform (Z.map ι)).E.E := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace s
  have : CharZero k := hinv.2.1.1
  have hHE := hinv.2.2
  have hred : IsReduced ι.ker.subscheme := (hinv.2.2.1 none).1
  have : IsReduced S := isReduced_of_isOpenImmersion ι.toImage
  have hHC : ι.ker ≤ Z.map ι := Scheme.Hom.le_ker_comp Z.subschemeι ι
  generalize Z.map ι = C at hc h hHC ⊢
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  have hcons : IsSNCFamily s (Fin.cons (α := fun _ => W.IdealSheafData) ι.ker T.E.E) := by
    have := isSNCFamily_comp hHE (finSuccEquiv T.E.s) (finSuccEquiv T.E.s).injective
    convert this using 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hZcons := Kollar.hasSNCWith_cons_of_hasSNCWith s T.E ι.ker hcons C hHC hc.2
  have hHZ : (C.support : Set W) ⊆ ι.ker.support := Scheme.IdealSheafData.support_antitone hHC
  have : IsLocallyNoetherian (blowUp C) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase C ≫ s)
  have hr : Set.range ι = (ι.ker.support : Set W) := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  let Tset : Option (Fin (T.E.s + 1)) → Set (blowUp C) := fun o =>
    o.elim (blowUpToBase C ⁻¹' ((ι.ker.support : Set W) \ C.support)) (totalTransformSet T.E C)
  have hfam : (fun o : Option (Fin (T.transform C).E.s) =>
      o.elim (canonicalLift ι C).ker (T.transform C).E.E) = fun o =>
        Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure (Tset o)) := by
    funext o
    cases o with
    | none =>
      show (canonicalLift ι C).ker = _
      rw [ker_canonicalLift_eq_vanishingIdeal, hr]
      rfl
    | some i => exact totalTransform_E_eq T.E C i
  rw [hfam]
  have hcoord : ∀ x' : blowUp C, ∃ (N : ℕ) (w : Fin N → (blowUp C).presheaf.stalk x')
      (c : {o // x' ∈ (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Tset o))).support} → Fin N),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        (∀ o, IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Tset o.1))) x' = Ideal.span {w (c o)}) ∧
        Function.Injective c := by
    intro x'
    obtain ⟨N, w, d, hw, h1, h2⟩ :=
      exists_assignment_strictTransform T.E ι.ker hcons.2 hZcons hHZ x'
    obtain ⟨c, hc, hinj⟩ := exists_stalk_eq_of_assignment Tset x' hw d h1 h2
    exact ⟨N, w, c, hw, hc, hinj⟩
  have hpar : ∀ o, ∀ y ∈ (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Tset o))).support,
      ∃ (m : ℕ) (w : Fin m → (blowUp C).presheaf.stalk y) (j : Fin m),
        MMP.Mori.IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
            (TopologicalSpace.Closeds.closure (Tset o))) y = Ideal.span {w j} := by
    intro o y hy
    obtain ⟨N, w, c, hw, hc, -⟩ := hcoord y
    exact ⟨N, w, c ⟨o, hy⟩, hw, hc ⟨o, hy⟩⟩
  exact ⟨fun o => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar o),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar o),
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar o)⟩, hcoord⟩

/-- The invariant passes to the transformed tuple and the canonical lift. -/
public theorem liftInvariant_transform {k : Type v} [Field k] {S W : Scheme.{v}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {Z : S.IdealSheafData} (hc : T.IsTransformCentre s (Z.map ι)) (h : (Z.map ι).comap ι = Z) :
    LiftInvariant (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι))
      (blowUpToBase (Z.map ι) ≫ s) (T.transform (Z.map ι)) := by
  have : IsClosedImmersion ι := hinv.1
  have : IsClosedImmersion (canonicalLift ι (Z.map ι)) :=
    Bridges.isClosedImmersion_canonicalLift ι (Z.map ι)
  obtain ⟨hchar, hvar, -, -, hE⟩ := hinv.2.1
  have : AlgebraicGeometry.IsVariety k s := hvar
  refine ⟨inferInstance, ⟨hchar, isVariety_blowUp_map hinv,
    MMP.Mori.isSmoothScheme_of_smooth
      (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup s (Z.map ι)
        ⟨hinv.2.1.2.2.1, hc.1⟩).1,
    transform_I_ne_bot_and_cartier hinv hc, ?_⟩, isSNCFamily_transform hinv hc h⟩
  exact isOrderedSNC_totalTransform s hE.2 hc.2

/-- The support of the total transform `π⁻¹_tot(E)`: the closure of `π⁻¹(Supp E ∖ Z^{≥2})`
together with the closure of the preimages of the components of `Z` that are no components of
`Supp E`. -/
public theorem support_totalTransform {S : Scheme.{v}} (E : OrderedDivisor S)
    (Z : S.IdealSheafData) :
    (E.totalTransform Z).support =
      closure (blowUpToBase Z ⁻¹' (E.support \ componentsOfCodimAtLeastTwo (Z.support : Set S))) ∪
        closure (⋃ (W : Set S) (_ : W ∈ componentsOf (Z.support : Set S))
          (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W) := by
  have h1 : (⋃ i : Fin E.s, closure (blowUpToBase Z ⁻¹' (((E.E i).support : Set S) \
      componentsOfCodimAtLeastTwo (Z.support : Set S)))) =
      closure (blowUpToBase Z ⁻¹' ((⋃ i, ((E.E i).support : Set S)) \
        componentsOfCodimAtLeastTwo (Z.support : Set S))) := by
    rw [← closure_iUnion_of_finite, ← Set.preimage_iUnion, ← Set.iUnion_diff]
  ext x
  simp only [OrderedDivisor.support, OrderedDivisor.totalTransform, Set.mem_iUnion,
    Set.mem_union]
  rw [Fin.exists_fin_succ', ← h1, Set.mem_iUnion]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_closure, SetLike.mem_coe]

/-- The support of the total transform of an ordered divisor depends only on its support. -/
public theorem support_totalTransform_congr {S : Scheme.{v}} {E E' : OrderedDivisor S}
    (hE : E.support = E'.support) (Z : S.IdealSheafData) :
    (E.totalTransform Z).support = (E'.totalTransform Z).support := by
  rw [support_totalTransform, support_totalTransform, hE]

/-! ### The induction -/

private theorem liftClause_of_isTransformSeq {k : Type v} [Field k] {S : Scheme.{v}}
    (B : ClosedBlowupSequence S) :
    ∀ (W : Scheme.{v}) (ι : S ⟶ W) (s : W ⟶ Spec (.of k)) (T : OrderedDivisorTuple W)
      (ES : OrderedDivisor S), LiftInvariant ι s T → ES.support = (T.E.comap ι).support →
      IsTransformSeq B (ι ≫ s) ⟨T.m, fun j => (T.I j).comap ι, ES⟩ →
      ∃ B' : ClosedBlowupSequence W, ClosedBlowupSequence.IsPushforward ι B B' ∧
        LiftClause B W ι s T := by
  induction B with
  | nil S => exact fun W _ _ _ _ hinv _ _ => ⟨.nil W, trivial, hinv⟩
  | cons Z B ih =>
    intro W ι s T ES hinv hES hB
    rw [isTransformSeq_cons] at hB
    have : IsClosedImmersion ι := hinv.1
    have h := comap_map_of_isClosedImmersion ι Z
    have hc := isTransformCentre_map hinv hES hB.1
    have hI := comap_transform_I hinv hc h
    have hE := support_comap_transform_E hinv hc h
    set φ := eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι) with hφ
    have hbase : φ ≫ blowUpToBase (Z.map ι) ≫ s = blowUpToBase Z ≫ ι ≫ s := by
      rw [hφ, Category.assoc, ← Category.assoc (canonicalLift _ _),
        canonicalLift_comp_blowUpToBase, ← Category.assoc, ← Category.assoc,
        eqToHom_comp_blowUpToBase h, Category.assoc]
    have htuple : (⟨(T.transform (Z.map ι)).m, fun j => ((T.transform (Z.map ι)).I j).comap φ,
        ES.totalTransform Z⟩ : OrderedDivisorTuple (blowUp Z)) =
        (⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple _).transform Z := by
      simp only [OrderedDivisorTuple.transform]
      congr 1
      funext j
      exact (hI j).trans rfl
    obtain ⟨B', hP, hL⟩ := ih (blowUp (Z.map ι)) φ (blowUpToBase (Z.map ι) ≫ s)
      (T.transform (Z.map ι)) (ES.totalTransform Z) (liftInvariant_transform hinv hc h)
      ((support_totalTransform_congr hES Z).trans hE.symm) (by rw [hbase, htuple]; exact hB.2)
    exact ⟨.cons (Z.map ι) B', ⟨h, rfl, hP⟩, hc, h, hI, hE, hL⟩

end MMP.Resolution.Internal.TupleRestrictionLift

namespace MMP.Resolution.OrderedDivisorTuple

open MMP.Resolution.Internal.TupleRestrictionLift in
/-- **Lifting order-one transformations from a transverse divisor.** Let `T = ((I_j), E)` be an
ordered divisor tuple on `V` over `k`, and `H ⊆ V` a closed subscheme with `H + E` a simple
normal crossing divisor, no `cosupp I_j` containing an irreducible component of `H`. Let `B` be
a sequence of order-one transformations of the restricted tuple `T|_H` on `H`. Then there is a
blow-up sequence `B'` of `V`, the push-forward of `B` along `ι : H ↪ V`, such that at every step
`i`, with `ι_i : H_i → V_i` the iterated canonical lift and `C_i` the centre of `B`:
the image `(ι_i)_* C_i` is a centre of an order-one transformation of the current ambient tuple
`T_i`, its inverse image along `ι_i` is `C_i`, the restriction along `ι_{i+1}` of each ideal of
`T_{i+1}` is the corresponding ideal of the transform of `T_i|_{H_i}` along `C_i`, and the
restriction of the boundary of `T_{i+1}` has the same support as the boundary of that
transform. At the last stage `r`, `ι_r` is a closed immersion, `T_r` is an ordered divisor tuple,
and the strict transform `ι_r(H_r)` together with the boundary of `T_r` is snc. -/
@[mmp "lem_mmp_tuple_restriction_lift"]
public theorem exists_isPushforward_transform_restrict {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (H : V.IdealSheafData)
    (hH : IsSNCFamily sV fun o : Option (Fin T.E.s) => o.elim H T.E.E)
    (hI : ∀ j, ∀ W ∈ componentsOf (H.support : Set V), ¬ W ⊆ ((T.I j).support : Set V))
    (B : ClosedBlowupSequence H.subscheme)
    (hB : ClosedBlowupSequence.rec
      (motive := fun S _ => (S ⟶ Spec (.of k)) → OrderedDivisorTuple S → Prop)
      (fun _ _ _ => True)
      (fun Z _ ih s TS => TS.IsTransformCentre s Z ∧ ih (blowUpToBase Z ≫ s) (TS.transform Z))
      B (H.subschemeι ≫ sV) ⟨T.m, fun j => (T.I j).comap H.subschemeι, T.E.comap H.subschemeι⟩) :
    ∃ B' : ClosedBlowupSequence V, ClosedBlowupSequence.IsPushforward H.subschemeι B B' ∧
      ClosedBlowupSequence.rec
        (motive := fun S _ => ∀ W : Scheme.{u}, (S ⟶ W) → (W ⟶ Spec (.of k)) →
          OrderedDivisorTuple W → Prop)
        (fun _ _ ι s TW => IsClosedImmersion ι ∧ IsOrderedDivisorTuple s TW ∧
          IsSNCFamily s fun o : Option (Fin TW.E.s) => o.elim ι.ker TW.E.E)
        (fun Z _ ih W ι s TW =>
          TW.IsTransformCentre s (Z.map ι) ∧
            ∃ h : (Z.map ι).comap ι = Z,
              (∀ j, ((TW.transform (Z.map ι)).I j).comap
                  (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι)) =
                ((⟨TW.m, fun j => (TW.I j).comap ι, TW.E.comap ι⟩ :
                  OrderedDivisorTuple _).transform Z).I j) ∧
              ((TW.transform (Z.map ι)).E.comap
                  (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι))).support =
                ((⟨TW.m, fun j => (TW.I j).comap ι, TW.E.comap ι⟩ :
                  OrderedDivisorTuple _).transform Z).E.support ∧
              ih (blowUp (Z.map ι))
                (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι))
                (blowUpToBase (Z.map ι) ≫ s) (TW.transform (Z.map ι)))
        B V H.subschemeι sV T :=
  liftClause_of_isTransformSeq B V H.subschemeι sV T (T.E.comap H.subschemeι)
    ⟨inferInstance, hT, by rwa [Scheme.IdealSheafData.ker_subschemeι]⟩ rfl hB

end MMP.Resolution.OrderedDivisorTuple

end
