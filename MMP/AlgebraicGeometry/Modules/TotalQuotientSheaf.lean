/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Adjunction.DifferentDefs
public import StacksFrontier.AlgebraicGeometry.RationalFunctions.Meromorphic
public import MMP.AlgebraicGeometry.Cohomology.Duality.NormalizedDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedSeparatedNagata
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorComparison
public import StacksFrontier.RingTheory.Dualizing.NormalizedSingleSelfField
public import StacksFrontier.RingTheory.Dualizing.NormalizedUniqueness
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Restriction
public import StacksFrontier.RingTheory.Depth.SemilinearEquiv
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk

/-!
# The total quotient sheaf of a reduced scheme and the dualizing sheaf inside it

* `MMP.Flips.exists_totalQuotientSheaf_ringEquiv_pi_residueField`: on a reduced Noetherian
  scheme, `K(X)(V) ≅ ∏_{ηᵢ ∈ V} k(ηᵢ)`, naturally, and `𝒪_X(V) → K(X)(V)` is injective.
* `MMP.Flips.IsDualizingSheaf.isCoherent_exists_injective`: for `X` reduced and pure dimensional,
  `ω_X` is coherent and embeds `𝒪_X`-linearly into `K(X)`.
* `MMP.Flips.IsDualizingSheaf.isSaturated_image`: every such embedding has saturated image.

## Implementation notes

`K(X)` in the first lemma is the sheaf of total quotient rings (`Scheme.totalQuotientSheaf`). In
FA 16, and in the two lemmas on `ω_X`, `K(X)` is the sheaf `U ↦ ∏_{ηᵢ ∈ U} 𝒪_{X,ηᵢ}` of
`MMP.Mori.rationalFunctionsPresheaf` as an `𝒪_X`-module (`MMP.Flips.rationalFunctionsModule`);
on a reduced Noetherian scheme the two agree by the first lemma, since `𝒪_{X,ηᵢ} = k(ηᵢ)`.

The image `φ(ω_X) ⊆ K(X)` of a morphism `φ` of `𝒪_X`-modules is the subsheaf of `K(X)` of the
sections that are locally images of sections of `ω_X` (`MMP.Flips.imageSubmodule`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

open scoped Stacks.SmallDerivedModel

namespace MMP.Flips

open MMP.Mori

/-! ### The total quotient sheaf of a reduced Noetherian scheme -/

section TotalQuotient

variable {X : Scheme.{u}}

/-- The ring map `𝒪_X(V) → ∏_{ηᵢ ∈ V} k(ηᵢ)` sending a section to its values at the generic
points `ηᵢ` of the irreducible components lying in `V`. -/
def toPiResidueField (V : X.Opens) :
    Γ(X, V) →+* ∀ η : {η : X // η ∈ genericPoints X ∧ η ∈ V}, X.residueField η.1 :=
  RingHom.pi fun η => (X.presheaf.germ V η.1 η.2.2 ≫ X.residue η.1).hom

private lemma specStalk_res (η : genericPoints X) {V V' : X.Opens} (hV' : η.1 ∈ V') (hV : η.1 ∈ V)
    (i : V' ⟶ V) (x : Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ V)) :
    specStalkSectionsAlgEquiv η hV'
      ((stalkSpecPushforward X η.1).presheaf.map i.op x) = specStalkSectionsAlgEquiv η hV x := by
  unfold specStalkSectionsAlgEquiv
  refine congrArg (fun y => (Scheme.ΓSpecIso (X.presheaf.stalk η.1)).hom.hom y) ?_
  change ((Spec (X.presheaf.stalk η.1)).presheaf.map _).hom
    (((Spec (X.presheaf.stalk η.1)).presheaf.map _).hom x) =
      ((Spec (X.presheaf.stalk η.1)).presheaf.map _).hom x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private def rhoGen (η : genericPoints X) {V : X.Opens} (hV : η.1 ∈ V) :
    Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ V) →+* X.residueField η.1 :=
  letI : Algebra Γ(X, V) (X.presheaf.stalk η.1) := X.presheaf.algebra_section_stalk ⟨η.1, hV⟩
  (X.residue η.1).hom.comp (specStalkSectionsAlgEquiv η hV).toRingEquiv.toRingHom

private lemma residue_bijective_of_isField [IsReduced X] (η : genericPoints X) :
    Function.Bijective (X.residue η.1).hom := by
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk η.1) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp
      (isField_stalk_of_closure_mem_irreducibleComponents X η.1 η.2)
  refine ⟨?_, IsLocalRing.residue_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : a ∈ RingHom.ker (X.residue η.1).hom := ha
  have h2 : RingHom.ker (X.residue η.1).hom = IsLocalRing.maximalIdeal (X.presheaf.stalk η.1) :=
    IsLocalRing.ker_residue
  rwa [h2, hm, Ideal.mem_bot] at this

private lemma rhoGen_bijective [IsReduced X] (η : genericPoints X) {V : X.Opens} (hV : η.1 ∈ V) :
    Function.Bijective (rhoGen η hV) := by
  unfold rhoGen
  exact (residue_bijective_of_isField η).comp (RingEquiv.bijective _)

private lemma rhoGen_res (η : genericPoints X) {V V' : X.Opens} (hV' : η.1 ∈ V')
    (hV : η.1 ∈ V) (i : V' ⟶ V) (x : Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ V)) :
    rhoGen η hV' ((stalkSpecPushforward X η.1).presheaf.map i.op x) = rhoGen η hV x := by
  simp only [rhoGen, RingHom.comp_apply]
  exact congrArg (X.residue η.1).hom (specStalk_res η hV' hV i x)

private def phiGen (V : X.Opens) :
    X.totalQuotientSheaf.presheaf.obj (op V) →+*
      ∀ η : {η : X // η ∈ genericPoints X ∧ η ∈ V}, X.residueField η.1 :=
  RingHom.pi fun η => (rhoGen ⟨η.1, η.2.1⟩ η.2.2).comp
    ((toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩).hom.app (op V)).hom

private lemma bijective_pi_rhoGen [IsReduced X] (V : X.Opens) :
    Function.Bijective (fun (y : ∀ η : genericPoints X,
        Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ V))
        (η : {η : X // η ∈ genericPoints X ∧ η ∈ V}) =>
      rhoGen ⟨η.1, η.2.1⟩ η.2.2 (y ⟨η.1, η.2.1⟩)) := by
  classical
  constructor
  · intro a b hab
    funext η
    by_cases hη : η.1 ∈ V
    · exact (rhoGen_bijective η hη).1 (congrFun hab ⟨η.1, η.2, hη⟩)
    · exact (subsingleton_specStalkSections η hη).elim _ _
  · intro t
    refine ⟨fun η => if h : η.1 ∈ V then
      (Function.surjInv (rhoGen_bijective η h).2) (t ⟨η.1, η.2, h⟩) else 0, ?_⟩
    funext η
    simp only [η.2.2, dite_true]
    exact Function.surjInv_eq (rhoGen_bijective ⟨η.1, η.2.1⟩ η.2.2).2 _

private lemma phiGen_bijective [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]
    (V : X.Opens) : Function.Bijective (phiGen V) := by
  have hiso : IsIso (toGenericPointStalkProduct X) := isIso_toGenericPointStalkProduct
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset
    (finite_irreducibleComponents_of_isCompact X)
  have hhom : IsIso (toGenericPointStalkProduct X).hom :=
    Functor.map_isIso (TopCat.Sheaf.forget CommRingCat.{u} X) (toGenericPointStalkProduct X)
  have happ : Function.Bijective (((toGenericPointStalkProduct X).hom.app (op V)).hom) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  let E := ringSheafSectionsPiEquiv (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) V
  let F : (∀ η : genericPoints X, Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ V)) →
      ∀ η : {η : X // η ∈ genericPoints X ∧ η ∈ V}, X.residueField η.1 :=
    fun y η => rhoGen ⟨η.1, η.2.1⟩ η.2.2 (y ⟨η.1, η.2.1⟩)
  have hcomp :
      ∀ s, phiGen V s = F (E (((toGenericPointStalkProduct X).hom.app (op V)).hom s)) := by
    intro s
    funext η
    have h1 : (toGenericPointStalkProduct X).hom ≫
        (Limits.Pi.π (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) ⟨η.1, η.2.1⟩).hom =
        (toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩).hom :=
      congrArg (fun t : X.totalQuotientSheaf ⟶ stalkSpecPushforward X η.1 ↦ t.hom)
        (Limits.Pi.lift_comp_π (fun η ↦ toStalkSpecPushforwardSheaf η) ⟨η.1, η.2.1⟩)
    have h2 := ringSheafSectionsPiEquiv_apply
      (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) V
      (((toGenericPointStalkProduct X).hom.app (op V)).hom s) ⟨η.1, η.2.1⟩
    simp only [phiGen, F, RingHom.pi_apply]
    refine congrArg (rhoGen _ _) (Eq.trans ?_ h2.symm)
    exact (ConcreteCategory.congr_hom (congrArg (fun t => t.app (op V)) h1) s).symm
  rw [show phiGen V = F ∘ E ∘ ((toGenericPointStalkProduct X).hom.app (op V)).hom from
    funext hcomp]
  exact (bijective_pi_rhoGen V).comp (E.bijective.comp happ)

private lemma phiGen_toTotalQuotientSheaf (V : X.Opens) (s : Γ(X, V)) :
    phiGen V ((X.toTotalQuotientSheaf.hom.app (op V)).hom s) = toPiResidueField V s := by
  funext η
  have h1 := toTotalQuotientSheaf_comp_toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩
  have h2 : ((toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩).hom.app (op V)).hom
      ((X.toTotalQuotientSheaf.hom.app (op V)).hom s) = ((X.fromSpecStalk η.1).app V).hom s :=
    ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app (op V)) h1) s
  change rhoGen ⟨η.1, η.2.1⟩ η.2.2
      (((toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩).hom.app (op V)).hom
        ((X.toTotalQuotientSheaf.hom.app (op V)).hom s)) =
    ((X.presheaf.germ V η.1 η.2.2 ≫ X.residue η.1).hom) s
  rw [h2]
  unfold rhoGen
  letI : Algebra Γ(X, V) (X.presheaf.stalk η.1) := X.presheaf.algebra_section_stalk ⟨η.1, η.2.2⟩
  exact congrArg (X.residue η.1).hom ((specStalkSectionsAlgEquiv ⟨η.1, η.2.1⟩ η.2.2).commutes s)

private lemma phiGen_res {V V' : X.Opens} (i : V' ⟶ V)
    (s : X.totalQuotientSheaf.presheaf.obj (op V)) :
    phiGen V' ((X.totalQuotientSheaf.presheaf.map i.op).hom s) =
      fun η : {η : X // η ∈ genericPoints X ∧ η ∈ V'} =>
        phiGen V s ⟨η.1, η.2.1, leOfHom i η.2.2⟩ := by
  funext η
  have h :=
    NatTrans.naturality_apply (toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩).hom i.op s
  change rhoGen ⟨η.1, η.2.1⟩ η.2.2
      (((toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩).hom.app (op V')).hom
        ((X.totalQuotientSheaf.presheaf.map i.op).hom s)) =
    rhoGen ⟨η.1, η.2.1⟩ (leOfHom i η.2.2)
      (((toStalkSpecPushforwardSheaf (X := X) ⟨η.1, η.2.1⟩).hom.app (op V)).hom s)
  rw [h]
  exact rhoGen_res _ _ _ i _

/-- **Total quotient sheaf of a reduced Noetherian scheme.** Let `X` be a reduced Noetherian
scheme with generic points `η₁, …, η_r` of its irreducible components. For every open `V ⊆ X`
the natural map `K(X)(V) → ∏_{ηᵢ ∈ V} k(ηᵢ)` is a ring isomorphism, compatible with restriction
to smaller opens; here "natural" means that on `𝒪_X(V)` it is the map to the values at the
`ηᵢ`. Moreover `𝒪_X(V) → K(X)(V)` is injective. -/
@[mmp "lem_mmp_foundation_reduced_total_quotient_sheaf"]
theorem exists_totalQuotientSheaf_ringEquiv_pi_residueField [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] :
    ∃ e : ∀ V : X.Opens, X.totalQuotientSheaf.presheaf.obj (op V) ≃+*
        ∀ η : {η : X // η ∈ genericPoints X ∧ η ∈ V}, X.residueField η.1,
      (∀ (V : X.Opens) (s : Γ(X, V)),
        e V ((X.toTotalQuotientSheaf.hom.app (op V)).hom s) = toPiResidueField V s) ∧
      (∀ {V V' : X.Opens} (i : V' ⟶ V) (s : X.totalQuotientSheaf.presheaf.obj (op V)),
        e V' ((X.totalQuotientSheaf.presheaf.map i.op).hom s) =
          fun η : {η : X // η ∈ genericPoints X ∧ η ∈ V'} =>
            e V s ⟨η.1, η.2.1, leOfHom i η.2.2⟩) ∧
      ∀ V : X.Opens, Function.Injective (X.toTotalQuotientSheaf.hom.app (op V)).hom := by
  refine ⟨fun V => RingEquiv.ofBijective (phiGen V) (phiGen_bijective V),
    fun V s => phiGen_toTotalQuotientSheaf V s, fun i s => phiGen_res i s, fun V => ?_⟩
  exact injective_toTotalQuotientSheaf_app
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset
    (finite_irreducibleComponents_of_isCompact X) V

/-- **Total quotient sheaf of a reduced Noetherian scheme**, restriction: if `V' ⊆ V` are open and
`V'` contains every generic point of an irreducible component of `X` that lies in `V`, the
restriction `K(X)(V) → K(X)(V')` is an isomorphism. -/
@[mmp "lem_mmp_foundation_reduced_total_quotient_sheaf"]
theorem bijective_totalQuotientSheaf_map_of_genericPoints [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] {V V' : X.Opens} (i : V' ⟶ V) (h : ∀ η ∈ genericPoints X, η ∈ V → η ∈ V') :
    Function.Bijective (X.totalQuotientSheaf.presheaf.map i.op).hom := by
  let P : (∀ η : {η : X // η ∈ genericPoints X ∧ η ∈ V}, X.residueField η.1) →
      ∀ η : {η : X // η ∈ genericPoints X ∧ η ∈ V'}, X.residueField η.1 :=
    fun t η => t ⟨η.1, η.2.1, leOfHom i η.2.2⟩
  have hP : Function.Bijective P :=
    ⟨fun a b hab => funext fun η => congrFun hab ⟨η.1, η.2.1, h _ η.2.1 η.2.2⟩,
      fun t => ⟨fun η => t ⟨η.1, η.2.1, h _ η.2.1 η.2.2⟩, rfl⟩⟩
  have : (X.totalQuotientSheaf.presheaf.map i.op).hom =
      (RingEquiv.ofBijective _ (phiGen_bijective V')).symm ∘ P ∘ phiGen V :=
    funext fun s => (RingEquiv.eq_symm_apply _).2 (phiGen_res i s)
  rw [this]
  exact (RingEquiv.bijective _).comp (hP.comp (phiGen_bijective V))

end TotalQuotient

/-! ### The dualizing sheaf inside `K(X)` -/

section Dualizing

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The image `φ(𝓕) ⊆ K(X)` of a morphism of `𝒪_X`-modules `φ : 𝓕 ⟶ K(X)`: the sections of
`K(X)` which are locally images of sections of `𝓕`. -/
def imageSubmodule {F : X.Modules} (φ : F ⟶ rationalFunctionsModule X) :
    RationalFunctionsSubmodule X :=
  RationalFunctionsSubmodule.localClosure
    (fun U => Submodule.span Γ(X, U)
      {t | ∃ f : F.val.obj (op U), ((φ.val.app (op U)) f).1 = t}) (by
      intro U V j s hs
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, rfl⟩ := hx
        refine Submodule.subset_span ⟨F.val.map j.op f, ?_⟩
        exact congrArg Subtype.val (ConcreteCategory.congr_hom (φ.val.naturality j.op) f)
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | smul r x _ hx =>
        rw [rationalFunctionsPresheaf_map_smul]
        exact Submodule.smul_mem _ _ hx)

/-- If `ω` is a dualizing sheaf for `π : X ⟶ Spec k`, then `X` is Noetherian and `π` is locally
of finite type. -/
lemma isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf {π : X ⟶ Spec (.of k)}
    {d : ℕ} {ω : X.Modules} (h : IsDualizingSheaf π d ω) :
    IsNoetherian X ∧ LocallyOfFiniteType π := by
  obtain ⟨-, Xbar, j, hj, πbar, hp, hjp, -⟩ := h
  subst hjp
  have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian πbar
  have : CompactSpace Xbar := QuasiCompact.compactSpace_of_compactSpace πbar
  have : IsNoetherian Xbar := {}
  exact ⟨Stacks.Coherent.isNoetherian_of_isOpenImmersion j, inferInstance⟩

/-- `j^* H^{-d}(π̄^× k) ≅ H^{-d}(K_X)` for the dualizing complex `K_X` of `X` normalized relative
to `k[0]`. -/
private lemma nonempty_restrict_dualizingModuleOverField_iso {π : X ⟶ Spec (.of k)}
    {Xbar : Scheme.{u}} (j : X ⟶ Xbar) [IsOpenImmersion j] (πbar : Xbar ⟶ Spec (.of k))
    [IsProper πbar] (hjp : j ≫ πbar = π) [IsNoetherian X] [LocallyOfFiniteType π] (d : ℕ) :
    Nonempty ((Scheme.Modules.restrictFunctor j).obj
        (Stacks.Duality.dualizingModuleOverField πbar d) ≅
      (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
        (normalizedDualizingComplexOverField π).complex.obj.obj) := by
  subst hjp
  let hps := Stacks.Duality.isShriekable_of_field (j ≫ πbar)
  let c : CompactificationOf (Over.mk (j ≫ πbar)) :=
    ⟨StructuredArrow.mk (Y := Over.mk πbar) (Over.homMk j rfl),
      ⟨(inferInstance : IsOpenImmersion j), (inferInstance : IsProper πbar)⟩⟩
  let e1 := Stacks.Duality.NormalizedOnOpens.isoUpperShriekPlusNagata
    (hp := isFiniteTypeOverNoetherian_of_field (j ≫ πbar))
    (Stacks.Duality.isDualizingComplex_derivedStructureSheafPlus_of_field k) hps
    (Stacks.Duality.normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field (j ≫ πbar)) _
      (Stacks.Duality.isDualizingComplex_derivedStructureSheafPlus_of_field k)) c
  let e1' := (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso e1)
  let e2 : (Stacks.Duality.quasiCoherentDerivedPullback' j).obj
      (Stacks.Duality.dualizingComplexOverField πbar) ≅ _ :=
    ((Stacks.Duality.restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback j).app _).symm
  let e3 := (ObjectProperty.ι _).mapIso e2
  have e4 := (Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso (-(d : ℤ))
  exact ⟨((e4.app (Stacks.Duality.dualizingComplexOverField πbar).obj).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).mapIso (e3.symm ≪≫ e1'.symm))⟩

/-- `ω ≅ H^{-d}(K_X)` for a dualizing sheaf `ω`, `K_X` normalized relative to `k[0]`. -/
lemma IsDualizingSheaf.nonempty_iso_homology {π : X ⟶ Spec (.of k)}
    {d : ℕ} {ω : X.Modules} (h : IsDualizingSheaf π d ω) [IsNoetherian X]
    [LocallyOfFiniteType π] :
    Nonempty (ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) := by
  obtain ⟨-, Xbar, j, hj, πbar, hp, hjp, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := nonempty_restrict_dualizingModuleOverField_iso j πbar hjp d
  exact ⟨e ≪≫ e'⟩

section InjectiveHelpers

/-- The `𝒪_{X,x}`-linear equivalence of stalks `F_x ≃ₗ G_x` induced by an isomorphism `F ≅ G`. -/
private def stalkEquivOfIso (x : X) {F G : X.Modules} (e : F ≅ G) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) := by
  letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
  let f := AlgebraicGeometry.stalkMapLinear F.val G.val e.hom.val x
  let g := AlgebraicGeometry.stalkMapLinear G.val F.val e.inv.val x
  have hf : ∀ (U : X.Opens) (hx : x ∈ U) (s : F.val.obj (op U)),
      f (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx s) =
        TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf U x hx ((e.hom.val.app (op U)).hom s) :=
    fun U hx s => TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
      ((PresheafOfModules.toPresheaf _).map e.hom.val) s
  have hg : ∀ (U : X.Opens) (hx : x ∈ U) (s : G.val.obj (op U)),
      g (TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf U x hx s) =
        TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx ((e.inv.val.app (op U)).hom s) :=
    fun U hx s => TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
      ((PresheafOfModules.toPresheaf _).map e.inv.val) s
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · refine LinearMap.ext fun m => ?_
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) G.val.presheaf m
    refine (congrArg f (hg U hx s)).trans ((hf U hx _).trans ?_)
    have h2 : (e.hom.val.app (op U)).hom ((e.inv.val.app (op U)).hom s) = s :=
      congrArg (fun t => (t.val.app (op U)).hom s) e.inv_hom_id
    rw [h2]
    rfl
  · refine LinearMap.ext fun m => ?_
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) F.val.presheaf m
    refine (congrArg g (hf U hx s)).trans ((hg U hx _).trans ?_)
    have h2 : (e.inv.val.app (op U)).hom ((e.hom.val.app (op U)).hom s) = s :=
      congrArg (fun t => (t.val.app (op U)).hom s) e.hom_inv_id
    rw [h2]
    rfl

/-- Depth bound at every point, for `ω ≅ H^{-d}(K_X)`. -/
private lemma exists_depth_le_of_iso [IsNoetherian X] {π : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType π]
    {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) (x : X) :
    ∃ h : ℕ, ringKrullDim (X.presheaf.stalk x) = h ∧
      letI :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
      min (h : ℕ∞) 2 ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf x) := by
  obtain ⟨-, -, hK3⟩ := normalizedDualizingComplexOverField_spec π
  obtain ⟨-, hx⟩ := hK3 d hd
  obtain ⟨D, e', h, -, -, hh, -, -, hdepth⟩ := hx x
  refine ⟨h, hh, ?_⟩
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  have h2 := Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (stalkEquivOfIso x e)
  rw [h2]
  have hh' := AlgebraicGeometry.TildeTensor.stalkModule_eq_presheafModule (X := X)
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  rwa [hh'] at hdepth

/-- At a point where the local ring is a field, `ω_x` is one-dimensional: `ω_x ≃ 𝒪_{X,x}`. -/
private lemma nonempty_stalk_linearEquiv_of_isField [IsNoetherian X] {π : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType π] {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) (x : X)
    (hx : IsField (X.presheaf.stalk x)) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
    Nonempty ((TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x) := by
  obtain ⟨-, -, hK3⟩ := normalizedDualizingComplexOverField_spec π
  obtain ⟨-, hx'⟩ := hK3 d hd
  obtain ⟨D, e', h, hD, -, hh, hed, hiso, -⟩ := hx' x
  have h0 : h = 0 := by
    have := ringKrullDim_eq_zero_of_isField hx
    rw [this] at hh
    exact_mod_cast hh.symm
  have he0 : e' = d := by omega
  obtain ⟨E1⟩ := hiso (-(d : ℤ))
  have hdeg : (-(d : ℤ)) + (e' : ℤ) = 0 := by omega
  rw [hdeg] at E1
  have hl : IsLocallyNoetherian X := ‹AlgebraicGeometry.IsNoetherian X›.toIsLocallyNoetherian
  have hsingle : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) :=
    Dualizing.isNormalizedDualizingComplex_single_self_of_isField hx
  obtain ⟨E2⟩ := Dualizing.IsNormalizedDualizingComplex.nonempty_iso hD hsingle
  have hh := AlgebraicGeometry.TildeTensor.stalkModule_eq_presheafModule (X := X)
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  rw [hh] at E1
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  let E3 : (Stacks.Duality.standardHomology D 0) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
    (@DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) _ _
      (HasDerivedCategory.standard _) 0).mapIso E2 ≪≫
      (@DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} (X.presheaf.stalk x))
        _ _ (HasDerivedCategory.standard _) 0).app _
  exact ⟨(stalkEquivOfIso x e).trans (E1.trans E3.toLinearEquiv)⟩

/-- Build a morphism `ω ⟶ K(X)` from linear identifications of the generic stalks. -/
private def homToRationalFunctions (ω : X.Modules)
    (b : ∀ Z : irreducibleComponents X,
      letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val
        (componentGenericPoint X Z)
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf (componentGenericPoint X Z)) ≃ₗ[
        X.presheaf.stalk (componentGenericPoint X Z)]
        X.presheaf.stalk (componentGenericPoint X Z)) :
    ω ⟶ rationalFunctionsModule X := by
  let Φ : ∀ U : X.Opens, ω.val.obj (op U) →+ ToType ((rationalFunctionsPresheaf X).obj (op U)) :=
    fun U =>
      { toFun := fun s Z => b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2 s)
        map_zero' := by
          funext Z
          exact (congrArg (b Z.1) (map_zero (ConcreteCategory.hom
            (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2)))).trans (map_zero _)
        map_add' := by
          intro s t
          funext Z
          exact (congrArg (b Z.1) (map_add (ConcreteCategory.hom
            (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2)) s t)).trans
              (map_add _ _ _) }
  have hΦres : ∀ {U V : X.Opens} (i : V ⟶ U) (s : ω.val.obj (op U)),
      Φ V ((ω.val.presheaf.map i.op).hom s) = (rationalFunctionsPresheaf X).map i.op (Φ U s) := by
    intro U V i s
    funext Z
    show b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V _ Z.2 _) =
      b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ (i.le Z.2) s)
    exact congrArg (b Z.1) (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) ω.val.presheaf i _ _ s)
  let φab : ω.val.presheaf ⟶ (RationalFunctionsSubmodule.top X).presheafAb :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => ⟨Φ U.unop s, Submodule.mem_top⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun s t => Subtype.ext (map_add _ s t) }
      naturality := by
        intro U V i
        ext s
        exact Subtype.ext (hΦres i.unop s) }
  have hφ : ∀ (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj U) (m : ω.val.obj U),
      φab.app U (r • m) = r • φab.app U m := by
    intro U r m
    refine Subtype.ext (funext fun Z => ?_)
    show b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U.unop _ Z.2 (r • m)) =
      X.presheaf.germ U.unop _ Z.2 r *
        b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U.unop _ Z.2 m)
    have h1 := PresheafOfModules.germ_smul (R := X.presheaf) ω.val (componentGenericPoint X Z.1)
      U.unop Z.2 r m
    exact (congrArg (b Z.1) h1).trans ((map_smul (b Z.1) _ _).trans rfl)
  exact ⟨PresheafOfModules.homMk φab hφ⟩

open Stacks.AlgebraicGeometry.AssociatedPointsMono in
/-- Variant of Stacks 0AVL (`injective_app_of_isAffineOpen`) with no hypothesis on the target. -/
private lemma injective_app_of_isAffineOpen' [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ y ∈ Stacks.Divisors.associatedPoints F, ∀ (U : X.Opens) (hy : y ∈ U) (s : Γ(F, U)),
      f.app U s = 0 → F.presheaf.germ U y hy s = 0)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (f.app U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) :=
    { toFun := f.app U
      map_add' := map_add _
      map_smul' := fun r x => f.app_smul r x }
  have hker : LinearMap.ker φ = ⊥ := by
    by_contra hne
    have : Nontrivial (LinearMap.ker φ) := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨q, hq⟩ := associatedPrimes.nonempty Γ(X, U) (LinearMap.ker φ)
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hq
    obtain ⟨hqp, k, hkq⟩ := hq
    have hcol : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
        (Submodule.span Γ(X, U) {(k : Γ(F, U))}) = q := by
      rw [Submodule.colon_span]
      ext r
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hkq,
        Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    set u : U := hU.isoSpec.inv ⟨q, hqp⟩
    have hpq : hU.primeIdealOf u = ⟨q, hqp⟩ := primeIdealOf_isoSpec_inv hU _
    have hcol' : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
        (Submodule.span Γ(X, U) {(k : Γ(F, U))})
          = (hU.primeIdealOf ⟨(u : X), u.2⟩).asIdeal := by
      rw [hcol]
      exact congrArg PrimeSpectrum.asIdeal hpq.symm
    let : Module (X.presheaf.stalk (u : X)) (F.presheaf.stalk (u : X)) :=
      stalkModule F (u : X)
    have hann := colon_germ_eq F hU (u : X) u.2 (k : Γ(F, U)) hcol'
    have hassoc : (u : X) ∈ Stacks.Divisors.associatedPoints F := ⟨inferInstance, _, hann⟩
    have hgz : F.presheaf.germ U (u : X) u.2 (k : Γ(F, U)) ≠ 0 := by
      intro h
      have h1 : (1 : X.presheaf.stalk (u : X)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk (u : X)) := by
        rw [← hann, Submodule.colon_span, Submodule.mem_colon_singleton, h, smul_zero]
        exact Submodule.zero_mem _
      exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk (u : X))).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    exact hgz (hf (u : X) hassoc U u.2 (k : Γ(F, U)) k.2)
  have key : ∀ t : Γ(F, U), f.app U t = 0 → t = 0 := by
    intro t ht
    have htk : t ∈ LinearMap.ker φ := ht
    rw [hker, Submodule.mem_bot] at htk
    exact htk
  intro a b hab
  exact sub_eq_zero.mp (key (a - b) (by rw [map_sub, hab, sub_self]))

/-- General opens: injectivity of `f.app U` from the germ condition at associated points. -/
private lemma injective_app_of_germ_zero [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ y ∈ Stacks.Divisors.associatedPoints F, ∀ (U : X.Opens) (hy : y ∈ U) (s : Γ(F, U)),
      f.app U s = 0 → F.presheaf.germ U y hy s = 0) (U : X.Opens) :
    Function.Injective (f.app U) := by
  have key : ∀ s : Γ(F, U), f.app U s = 0 → s = 0 := by
    intro s hs
    refine TopCat.Presheaf.section_ext (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩ U s 0 fun x hx => ?_
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU'⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    have hVU : (V : X.Opens) ≤ U := hVU'
    have hnat : f.app (V : X.Opens) (F.presheaf.map (homOfLE hVU).op s)
        = G.presheaf.map (homOfLE hVU).op (f.app U s) := by
      simpa only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] using
        congr($(f.mapPresheaf.naturality (homOfLE hVU).op) s)
    have hs0 : F.presheaf.map (homOfLE hVU).op s = 0 := by
      refine injective_app_of_isAffineOpen' f hf hV ?_
      rw [hnat, hs, map_zero, map_zero]
    rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV s, hs0, map_zero, map_zero]
  intro a b hab
  exact sub_eq_zero.mp (key (a - b) (by rw [map_sub, hab, sub_self]))

private lemma mem_genericPoints_of_ringKrullDim_stalk_eq_zero (y : X)
    (h : ringKrullDim (X.presheaf.stalk y) = 0) : y ∈ genericPoints X := by
  rw [ringKrullDim_stalk_eq_coheight] at h
  have hmax : IsMax y := Order.coheight_eq_zero.mp (by exact_mod_cast h)
  have key : ∀ b : X, b ⤳ y → b = y := fun b hb =>
    (hb.antisymm (Scheme.le_iff_specializes.mp (hmax (Scheme.le_iff_specializes.mpr hb)))).eq
  show closure ({y} : Set X) ∈ irreducibleComponents X
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro T hT hle
  have hspec : IsGenericPoint (IsIrreducible.genericPoint hT) (closure T) :=
    IsIrreducible.isGenericPoint_genericPoint_closure hT
  have hy : y ∈ closure T := subset_closure (hle (subset_closure rfl))
  have hg := key _ (hspec.specializes hy)
  intro t ht
  have : t ∈ closure ({IsIrreducible.genericPoint hT} : Set X) := by
    rw [hspec.def]
    exact subset_closure ht
  rwa [hg] at this

/-- On a reduced scheme, the stalk at the generic point of an irreducible component is a field. -/
lemma isField_stalk_componentGenericPoint [IsReduced X] (Z : irreducibleComponents X) :
    IsField (X.presheaf.stalk (componentGenericPoint X Z)) :=
  isField_stalk_of_closure_mem_irreducibleComponents X _ (by
    rw [(isGenericPoint_componentGenericPoint X Z).def]
    exact Z.2)

/-- On a reduced scheme, the generic point of an irreducible component has coheight zero. -/
lemma coheight_componentGenericPoint_eq_zero [IsReduced X] (Z : irreducibleComponents X) :
    Order.coheight (componentGenericPoint X Z) = 0 := by
  have h0 := ringKrullDim_eq_zero_of_isField (isField_stalk_componentGenericPoint Z)
  rw [ringKrullDim_stalk_eq_coheight] at h0
  exact_mod_cast h0

/-- `ω` is coherent when `ω ≅ H^{-d}(K_X)`. -/
lemma isCoherent_of_iso_homology [IsNoetherian X] {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π]
    {d : ℕ} {ω : X.Modules}
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) :
    _root_.SheafOfModules.IsCoherent ω :=
  AlgebraicGeometry.isCoherent_of_moduleIso e.symm
    ((normalizedDualizingComplexOverField_spec π).2.1 (-(d : ℤ)))

end InjectiveHelpers

/-- For `X` reduced and pure of dimension `d` and `ω ≅ H^{-d}(K_X)`, there is an `𝒪_X`-linear map
`ω ⟶ K(X)` injective on all sections. -/
private lemma exists_injective_of_iso_homology [IsReduced X] [IsNoetherian X]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) :
    ∃ φ : ω ⟶ rationalFunctionsModule X, ∀ U : X.Opens, Function.Injective (φ.val.app (op U)) := by
  have hl : IsLocallyNoetherian X := ‹AlgebraicGeometry.IsNoetherian X›.toIsLocallyNoetherian
  have hcoh : _root_.SheafOfModules.IsCoherent ω := isCoherent_of_iso_homology e
  have hqc : ω.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent ω).1
  let b := fun Z : irreducibleComponents X =>
    (nonempty_stalk_linearEquiv_of_isField hd e _ (isField_stalk_componentGenericPoint Z)).some
  refine ⟨homToRationalFunctions ω b, fun U => ?_⟩
  refine injective_app_of_germ_zero (homToRationalFunctions ω b) ?_ U
  intro y hy V hyV s hs
  obtain ⟨h, hh, hdep⟩ := exists_depth_le_of_iso hd e y
  have hdep0 : Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal _)
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf y) = 0 := by
    by_contra hne
    exact Stacks.Divisors.notMem_associatedPoints_of_one_le_depth ω y
      (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hne)) hy
  have hh0 : ringKrullDim (X.presheaf.stalk y) = 0 := by
    rw [hh]
    rw [hdep0] at hdep
    have : min (h : ℕ∞) 2 = 0 := le_antisymm hdep bot_le
    obtain rfl : h = 0 := by
      by_contra hne
      have h1 : (1 : ℕ∞) ≤ h := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
      have : (1 : ℕ∞) ≤ min (h : ℕ∞) 2 := le_min h1 (by norm_num)
      rw [‹min (h : ℕ∞) 2 = 0›] at this
      exact absurd this (by norm_num)
    rfl
  have hyg : y ∈ genericPoints X := mem_genericPoints_of_ringKrullDim_stalk_eq_zero y hh0
  obtain ⟨Z, rfl⟩ : ∃ Z : irreducibleComponents X, componentGenericPoint X Z = y :=
    ⟨genericPoints.component ⟨y, hyg⟩, (isGenericPoint_componentGenericPoint X _).eq
      (genericPoints.isGenericPoint ⟨y, hyg⟩)⟩
  have h3 : b Z (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V _ hyV s) = 0 :=
    congrFun (congrArg Subtype.val
      (show (homToRationalFunctions ω b).val.app (op V) s = 0 from hs)) ⟨Z, hyV⟩
  exact (b Z).injective (h3.trans (map_zero _).symm)

/-- Elements of the span of the images of `φ` over `W` are images. -/
private lemma exists_eq_of_mem_span_image {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (W : X.Opens) {u : ToType ((rationalFunctionsPresheaf X).obj (op W))}
    (hu : u ∈ Submodule.span Γ(X, W)
      {t | ∃ f : ω.val.obj (op W), ((φ.val.app (op W)) f).1 = t}) :
    ∃ f : ω.val.obj (op W), ((φ.val.app (op W)) f).1 = u := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    exact ⟨f + g, by rw [map_add]; rfl⟩
  | smul r x _ hx =>
    obtain ⟨f, rfl⟩ := hx
    let r' : X.ringCatSheaf.obj.obj (op W) := r
    exact ⟨r' • f, congrArg Subtype.val ((φ.val.app (op W)).hom.map_smul r' f)⟩

private lemma val_app_map {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    {U V : X.Opens} (j : V ⟶ U) (g : ω.val.obj (op U)) :
    ((φ.val.app (op V)) ((ω.val.map j.op) g)).1 =
      (rationalFunctionsPresheaf X).map j.op ((φ.val.app (op U) g).1) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (φ.val.naturality j.op) g)

/-- A section of `K(X)` over `O` lying in the image sheaf of an injective `φ` is the image of a
section of `ω` over `O`. -/
lemma exists_preimage_of_mem_imageSubmodule {ω : X.Modules}
    (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) {O : X.Opens}
    {s : ToType ((rationalFunctionsPresheaf X).obj (op O))}
    (hs : s ∈ (imageSubmodule φ).sections O) :
    ∃ t : ω.val.obj (op O), ((φ.val.app (op O)) t).1 = s := by
  rw [imageSubmodule, RationalFunctionsSubmodule.mem_localClosure_iff] at hs
  choose W i hyW hP using hs
  choose f hf using fun y hy => exists_eq_of_mem_span_image φ (W y hy) (hP y hy)
  let ι := {y : X // y ∈ O}
  let U : ι → X.Opens := fun y => W y.1 y.2
  let sf : ∀ y : ι, ω.presheaf.obj (op (U y)) := fun y => f y.1 y.2
  have hcompat : TopCat.Presheaf.IsCompatible ω.presheaf U sf := by
    intro a b
    refine hφ (U a ⊓ U b) (Subtype.ext ?_)
    have e1 := val_app_map φ (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)) (sf a)
    have e2 := val_app_map φ (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)) (sf b)
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [show ((φ.val.app (op (U a))) (sf a)).1 = _ from hf a.1 a.2,
      show ((φ.val.app (op (U b))) (sf b)).1 = _ from hf b.1 b.2]
    rfl
  obtain ⟨t0, ht0, -⟩ :=
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing ω.presheaf).mp ω.isSheaf U sf hcompat
  have hle : O ≤ iSup U := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyW y hy⟩
  refine ⟨(ω.val.map (homOfLE hle).op) t0, funext fun Z => ?_⟩
  let y : ι := ⟨componentGenericPoint X Z.1, Z.2⟩
  have hsy : (ω.val.map (i y.1 y.2).op) ((ω.val.map (homOfLE hle).op) t0) = sf y := by
    rw [← ht0 y]
    change ω.presheaf.map _ (ω.presheaf.map _ t0) = ω.presheaf.map _ t0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have h1 := val_app_map φ (i y.1 y.2) ((ω.val.map (homOfLE hle).op) t0)
  rw [hsy, show ((φ.val.app (op (U y))) (sf y)).1 = _ from hf y.1 y.2] at h1
  exact (congrFun h1 ⟨Z.1, hyW y.1 y.2⟩).symm

private lemma map_maximalIdeal_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) :
    (IsLocalRing.maximalIdeal A).map (e : A →+* B) = IsLocalRing.maximalIdeal B :=
  IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)

open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.SheafOfModules.SheafHomStalk in
private lemma two_le_depth_stalk_restrict {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W)
    (h : letI :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (j w)
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk (j w)) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (j w))) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((Scheme.Modules.restrictFunctor j).obj F).val w
    (2 : ℕ∞) ≤ Module.depth (W.presheaf.stalk w) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.restrictFunctor j).obj F).val.presheaf w) := by
  have : IsLocalRing (ringStalk W.sheaf w) := inferInstanceAs (IsLocalRing (W.presheaf.stalk w))
  have : IsLocalRing (ringStalk X.sheaf (j w)) :=
    inferInstanceAs (IsLocalRing (X.presheaf.stalk (j w)))
  have key := Module.depth_eq_of_semilinearEquiv (restrictStalkRingEquiv j w)
    (IsLocalRing.maximalIdeal (ringStalk W.sheaf w))
    (restrictStalkAddEquiv j F w) (fun r m => restrictStalkHom_smul j F w r m)
  rw [map_maximalIdeal_ringEquiv (restrictStalkRingEquiv j w)] at key
  exact key ▸ h

private lemma bijective_map_congr (F : X.Modules) {A A' B B' : X.Opens} (hA : A = A')
    (hB : B = B') (h : B ≤ A) (h' : B' ≤ A')
    (hb : Function.Bijective (F.presheaf.map (homOfLE h).op)) :
    Function.Bijective (F.presheaf.map (homOfLE h').op) := by
  subst hA hB
  exact hb

/-- **Hartogs, local form.** If `O ⊆ V` are open and the stalks of the coherent module `F` have
depth `≥ 2` at every point of `V` outside `O`, then restriction `F(V) → F(O)` is bijective
(Stacks, Tag 0E9I, applied to the open subscheme `V`). -/
lemma restriction_bijective_of_depth_ge_two_of_le [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] {O V : X.Opens} (hOV : O ≤ V)
    (hdepth : ∀ x : X, x ∈ V → x ∉ O →
      letI :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    Function.Bijective (F.presheaf.map (homOfLE hOV).op) := by
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have hc : ((Scheme.Modules.restrictFunctor V.ι).obj F).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion V.ι F ‹_›
  have hb := restriction_bijective_of_depth_ge_two V.toScheme
    ((Scheme.Modules.restrictFunctor V.ι).obj F) (V.ι ⁻¹ᵁ O)
    (fun x' hx' => two_le_depth_stalk_restrict V.ι F x' (hdepth (V.ι x') x'.2 hx'))
  have hb' : Function.Bijective (F.presheaf.map (homOfLE (show V.ι ''ᵁ (V.ι ⁻¹ᵁ O) ≤ V.ι ''ᵁ ⊤ from
      Set.image_mono (fun _ _ => trivial))).op) := hb
  have hA : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  have hB : V.ι ''ᵁ (V.ι ⁻¹ᵁ O) = O := by
    ext y
    refine ⟨?_, fun hy => ⟨⟨y, hOV hy⟩, hy, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact hx
  exact bijective_map_congr F (A := V.ι ''ᵁ ⊤) (A' := V) (B := V.ι ''ᵁ (V.ι ⁻¹ᵁ O)) (B' := O)
    hA hB _ hOV hb'

/-- For `ω ≅ H^{-d}(K_X)`, the stalk `ω_y` has depth `≥ 2` wherever `y` has coheight `≥ 2`. -/
lemma two_le_depth_of_two_le_coheight [IsNoetherian X] {π : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType π] {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) (y : X)
    (h2 : (2 : ℕ∞) ≤ Order.coheight y) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val y
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal _)
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf y) := by
  obtain ⟨h, hh, hdep⟩ := exists_depth_le_of_iso hd e y
  rw [ringKrullDim_stalk_eq_coheight] at hh
  have h3 : (2 : ℕ∞) ≤ h := by
    have : Order.coheight y = (h : ℕ∞) := by exact_mod_cast hh
    rwa [this] at h2
  rwa [min_eq_right h3] at hdep

/-- If `X` is reduced of pure dimension `d` and `ω ≅ H^{-d}(K_X)`, then every sectionwise
injective `φ : ω ⟶ K(X)` has saturated image. -/
private lemma isSaturated_image_of_iso_homology [IsReduced X] [IsNoetherian X]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj)
    (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) :
    (imageSubmodule φ).IsSaturated := by
  have hl : IsLocallyNoetherian X := ‹AlgebraicGeometry.IsNoetherian X›.toIsLocallyNoetherian
  have hcoh : _root_.SheafOfModules.IsCoherent ω := isCoherent_of_iso_homology e
  refine RationalFunctionsSubmodule.ext fun U => le_antisymm ?_ ?_
  · intro s hs η hη _
    exact ⟨U, hη, s, hs, rfl⟩
  intro s hs
  let O : X.Opens := ⨆ W : {W : X.Opens // ∃ h : W ≤ U,
    (rationalFunctionsPresheaf X).map (homOfLE h).op s ∈ (imageSubmodule φ).sections W}, W.1
  have hOU : O ≤ U := iSup_le fun W => W.2.1
  have hsO : (rationalFunctionsPresheaf X).map (homOfLE hOU).op s ∈
      (imageSubmodule φ).sections O := by
    refine (imageSubmodule φ).mem_of_locally fun x hx => ?_
    obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp hx
    exact ⟨W.1, homOfLE (le_iSup (fun W : {W : X.Opens // ∃ h : W ≤ U,
      (rationalFunctionsPresheaf X).map (homOfLE h).op s ∈ (imageSubmodule φ).sections W} =>
        W.1) W), hxW, W.2.2⟩
  have hbad : ∀ y : X, y ∈ U → y ∉ O → (2 : ℕ∞) ≤ Order.coheight y := by
    intro y hy hyO
    by_contra hc
    obtain ⟨W, i, hyW, hmem⟩ := ((imageSubmodule φ).germ_mem_stalkSet_iff hy s).mp
      (hs y hy (Order.le_of_lt_add_one (not_le.mp hc)))
    exact hyO (Opens.mem_iSup.mpr ⟨⟨W, i.le, hmem⟩, hyW⟩)
  obtain ⟨t, ht⟩ := exists_preimage_of_mem_imageSubmodule φ hφ hsO
  obtain ⟨t', ht'⟩ := (restriction_bijective_of_depth_ge_two_of_le ω hOU fun y hy hyO =>
    two_le_depth_of_two_le_coheight hd e y (hbad y hy hyO)).2 t
  have hgen : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ U →
      componentGenericPoint X Z ∈ O := by
    intro Z hZ
    by_contra hZO
    have h2 := hbad _ hZ hZO
    rw [coheight_componentGenericPoint_eq_zero] at h2
    exact absurd h2 (by norm_num)
  have hφt : ((φ.val.app (op U)) t').1 = s := by
    funext Z
    have h2 : (rationalFunctionsPresheaf X).map (homOfLE hOU).op ((φ.val.app (op U) t').1) =
        (rationalFunctionsPresheaf X).map (homOfLE hOU).op s := by
      refine (val_app_map φ (homOfLE hOU) t').symm.trans (Eq.trans ?_ ht)
      rw [show (ω.val.map (homOfLE hOU).op) t' = t from ht']
    exact congrFun h2 ⟨Z.1, hgen Z.1 Z.2⟩
  rw [imageSubmodule, RationalFunctionsSubmodule.mem_localClosure_iff]
  intro x hx
  refine ⟨U, 𝟙 U, hx, ?_⟩
  rw [rationalFunctionsPresheaf_map_id_apply]
  exact Submodule.subset_span ⟨t', hφt⟩

/-- **The dualizing sheaf is coherent and embeds into `K(X)`.** For `X` reduced and of pure
dimension `d`, the dualizing sheaf `ω_X` is coherent, and there is an injective `𝒪_X`-linear map
`ω_X → K(X)`. -/
@[mmp "lem_mmp_foundation_fa16_canonical_coherent_torsion_free_rank_one"]
theorem IsDualizingSheaf.isCoherent_exists_injective [IsReduced X] {π : X ⟶ Spec (.of k)}
    {d : ℕ} {ω : X.Modules} (h : IsDualizingSheaf π d ω) :
    Stacks.SheafOfModules.IsCoherent ω ∧ ∃ φ : ω ⟶ rationalFunctionsModule X,
      ∀ U : X.Opens, Function.Injective (φ.val.app (op U)) := by
  obtain ⟨hN, hL⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf h
  obtain ⟨e⟩ := IsDualizingSheaf.nonempty_iso_homology h
  exact ⟨Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent (isCoherent_of_iso_homology e),
    exists_injective_of_iso_homology h.1 e⟩

/-- **Every fractional-ideal realization of the dualizing sheaf is saturated.** For `X` reduced
and of pure dimension `d` and every injective `𝒪_X`-linear map `φ : ω_X → K(X)`, the image
`φ(ω_X)` is saturated. -/
@[mmp "lem_mmp_foundation_fa16_canonical_saturated"]
theorem IsDualizingSheaf.isSaturated_image [IsReduced X] {π : X ⟶ Spec (.of k)} {d : ℕ}
    {ω : X.Modules} (h : IsDualizingSheaf π d ω) (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) :
    (imageSubmodule φ).IsSaturated := by
  obtain ⟨hN, hL⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf h
  obtain ⟨e⟩ := IsDualizingSheaf.nonempty_iso_homology h
  exact isSaturated_image_of_iso_homology h.1 e φ hφ

end Dualizing

end MMP.Flips
