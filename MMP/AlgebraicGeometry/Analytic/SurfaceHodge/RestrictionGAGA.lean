module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.AnalyticRestriction
public import MMP.AlgebraicGeometry.Analytic.GAGA.Projective
public import MMP.Topology.Sheaves.GodementFlasqueResolution
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.Injective
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianExact
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialAbelian
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Vanishing.KodairaCharZero
public import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition

/-!
# GAGA and the restriction of `H¹(𝒪)` to a closed subscheme

Let `X` be a smooth projective variety over `ℂ` and `i : Z ⟶ X` a closed immersion with `Z`
smooth over `ℂ`, for instance the zero scheme of a section of an invertible sheaf. The analytic
restriction `H¹(X^an, 𝒪) ⟶ H¹(Z^an, 𝒪)` (`MMP.Analytic.SurfaceHodge.analyticRestrictionH1`)
and the algebraic restriction `H¹(X, 𝒪_X) ⟶ H¹(X, i_* 𝒪_Z) ≅ H¹(Z, 𝒪_Z)` are conjugate by
additive isomorphisms. The comparison runs through Godement cohomology:

* a morphism `ψ : A ⟶ f_* B` of abelian sheaves along a continuous map `f : T' ⟶ T` induces
  `H^n(T, A) ⟶ H^n(T', B)`, the pullback followed by the adjoint `f⁻¹ A ⟶ B` of `ψ`; these maps
  compose along composites of continuous maps and are natural in both sheaves;
* along `α_X : X^an ⟶ X` and `α_X^# : 𝒪_X ⟶ (α_X)_* 𝒪_{X^an}` this map is the GAGA comparison
  map for `𝒪_X`, an isomorphism for `X` projective;
* restricting a regular function to `Z` and analytifying is analytifying and composing with
  `i^an`, so the analytic and the algebraic restriction of functions agree along
  `i^an ≫ α_X = α_Z ≫ i`;
* along a closed embedding the map `H^n(X, i_* G) ⟶ H^n(Z, G)` is bijective, the pushforward of
  an injective resolution being an injective resolution with the same global sections;
* Godement cohomology of the abelian sheaf underlying an `𝒪_X`-module is naturally isomorphic to
  its derived functor cohomology `cohomologyOverField`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.sheafCohomologyMapAlong`: the map `H^n(T, A) ⟶ H^n(T', B)` induced
  by `ψ : A ⟶ f_* B`.
* `MMP.Analytic.SurfaceHodge.analyticSharp`: `α_X^#` as a morphism of abelian sheaves.

## Main results

* `MMP.Analytic.SurfaceHodge.sheafCohomologyMapAlong_comp`: the maps along continuous maps
  compose.
* `MMP.Analytic.SurfaceHodge.bijective_sheafCohomologyMapAlong_id_of_isClosedEmbedding`:
  `H^n(T, f_* G) ⟶ H^n(T', G)` is bijective along a closed embedding.
* `MMP.Analytic.SurfaceHodge.isIso_sheafCohomologyMapAlong_analyticSharp`: GAGA for `𝒪`.
* `MMP.Analytic.SurfaceHodge.exists_addEquiv_analyticRestrictionH1`: the analytic restriction is
  conjugate to the algebraic one; `exists_addEquiv_analyticRestrictionH1_zeroScheme` for the zero
  scheme of a section of an invertible sheaf.
* `MMP.Analytic.SurfaceHodge.injective_analyticRestrictionH1_of_injective`: the analytic
  restriction is injective when the algebraic one is;
  `injective_analyticRestrictionH1_zeroScheme_of_injective` for zero schemes.

## Implementation notes

The isomorphism `H¹(Z^an, 𝒪) ≃ H¹(Z, 𝒪_Z)` of `exists_addEquiv_analyticRestrictionH1` is GAGA
for `Z` followed by the inverse of `H¹(X, i_* 𝒪_Z) ⟶ H¹(Z, 𝒪_Z)` on Godement cohomology, the
identification of Godement with derived functor cohomology on `X`, and the identification
`H¹(X, i_* 𝒪_Z) ≅ H¹(Z, 𝒪_Z)` of cohomology over `ℂ` along the closed immersion.

## References

* [J.-P. Serre, *Géométrie algébrique et géométrie analytique*]
* [R. Godement, *Topologie algébrique et théorie des faisceaux*]
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints

namespace MMP.Analytic.SurfaceHodge

universe u

/-! ### Godement sections along a composite of continuous maps -/

section GodementComp

open MMP.Analytic.CokernelCoresolution

variable {C : Type (u + 1)} [Category.{u} C] [Preadditive C] [HasCokernels C]
  {D : Type (u + 1)} [Category.{u} D] [Preadditive D] [HasCokernels D]
  {E : Type (u + 1)} [Category.{u} E] [Preadditive E] [HasCokernels E]
  {G₁ : C ⥤ C} {η₁ : 𝟭 C ⟶ G₁} {G₂ : D ⥤ D} {η₂ : 𝟭 D ⟶ G₂} {G₃ : E ⥤ E} {η₃ : 𝟭 E ⟶ G₃}
  {P₁ : D ⥤ C} {P₂ : E ⥤ D} [P₁.PreservesZeroMorphisms] [P₂.PreservesZeroMorphisms]

/-- Lifts that compose give maps of coresolutions that compose. -/
private theorem homX_comp_lift (Λ₁ : Lift G₁ η₁ G₂ η₂ P₁) (Λ₂ : Lift G₂ η₂ G₃ η₃ P₂)
    (Λ₁₂ : Lift G₁ η₁ G₃ η₃ (P₂ ⋙ P₁))
    (hcomp : ∀ {A : C} {B : D} {B' : E} (φ : A ⟶ P₁.obj B) (ψ : B ⟶ P₂.obj B'),
      Λ₁.lift φ ≫ P₁.map (Λ₂.lift ψ) = Λ₁₂.lift (φ ≫ P₁.map ψ))
    {A : C} {B : D} {B' : E} (φ : A ⟶ P₁.obj B) (ψ : B ⟶ P₂.obj B') (n : ℕ) :
    homX Λ₁ φ n ≫ P₁.map (homX Λ₂ ψ n) = homX Λ₁₂ (φ ≫ P₁.map ψ) n := by
  suffices H : ∀ n, (stageHom Λ₁ φ n).1 ≫ P₁.map (stageHom Λ₂ ψ n).1 =
      (stageHom Λ₁₂ (φ ≫ P₁.map ψ) n).1 ∧
      homX Λ₁ φ n ≫ P₁.map (homX Λ₂ ψ n) = homX Λ₁₂ (φ ≫ P₁.map ψ) n from (H n).2
  intro n
  induction n with
  | zero => exact ⟨rfl, hcomp φ ψ⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change Λ₁.lift (cokerDesc (stageHom Λ₁ φ n)) ≫ P₁.map (Λ₂.lift (cokerDesc (stageHom Λ₂ ψ n))) =
      Λ₁₂.lift (cokerDesc (stageHom Λ₁₂ (φ ≫ P₁.map ψ) n))
    rw [hcomp]
    congr 1
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    rw [π_cokerDesc_assoc, ← P₁.map_comp, π_cokerDesc, π_cokerDesc]
    change homX Λ₁ φ n ≫ P₁.map (homX Λ₂ ψ n ≫ P₂.map (cokernel.π _)) =
      homX Λ₁₂ (φ ≫ P₁.map ψ) n ≫ (P₂ ⋙ P₁).map (cokernel.π _)
    rw [P₁.map_comp, ← Category.assoc, ih.2]
    rfl

end GodementComp

section GodComp

open TopCat TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Sheaf

variable {T T' T'' : TopCat.{u}} (f : T' ⟶ T) (f' : T'' ⟶ T')

private theorem godementLiftHom_comp {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'} {B' : TopCat.Sheaf AddCommGrpCat.{u} T''}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B)
    (ψ : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f').obj B') :
    godementLiftHom f φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map (godementLiftHom f' ψ) =
      (godementLiftHom (f' ≫ f) (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map ψ) :) := by
  refine sheafHom_ext fun U s => funext fun z => ?_
  change B'.presheaf.stalkPushforward AddCommGrpCat f' z
      ((stalkFunctor AddCommGrpCat (f' z)).map ψ.hom
        (B.presheaf.stalkPushforward AddCommGrpCat f (f' z)
          ((stalkFunctor AddCommGrpCat (f (f' z))).map φ.hom (s ⟨f (f' z), z.2⟩)))) =
    B'.presheaf.stalkPushforward AddCommGrpCat (f' ≫ f) z
      ((stalkFunctor AddCommGrpCat ((f' ≫ f) z)).map
        (φ.hom ≫ (Presheaf.pushforward AddCommGrpCat f).map ψ.hom) (s ⟨(f' ≫ f) z, z.2⟩))
  rw [TopCat.Presheaf.stalkPushforward.comp]
  erw [CategoryTheory.Functor.map_comp]
  exact congrArg (B'.presheaf.stalkPushforward AddCommGrpCat f' z)
    (stalkFunctor_map_pushforward_comp_stalkPushforward_apply f ψ.hom (f' z) _).symm

/-- The Godement lifts along a composite, read through the composite of pushforwards. -/
private noncomputable def compLift : CokernelCoresolution.Lift (godementFunctor T)
    (godementUnit T) (godementFunctor T'') (godementUnit T'')
    (TopCat.Sheaf.pushforward AddCommGrpCat f' ⋙ TopCat.Sheaf.pushforward AddCommGrpCat f) where
  lift φ := godementLiftHom (f' ≫ f) φ
  app_comp_lift φ := (godementPullbackLift (f' ≫ f)).app_comp_lift φ
  lift_precomp a φ := (godementPullbackLift (f' ≫ f)).lift_precomp a φ
  lift_postcomp φ b := (godementPullbackLift (f' ≫ f)).lift_postcomp φ b

private theorem complexHom_comp {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'} {B' : TopCat.Sheaf AddCommGrpCat.{u} T''}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B)
    (ψ : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f').obj B') (n : ℕ) :
    CokernelCoresolution.homX (godementPullbackLift f) φ n ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map
          (CokernelCoresolution.homX (godementPullbackLift f') ψ n) =
      CokernelCoresolution.homX (godementPullbackLift (f' ≫ f))
        (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map ψ) n :=
  homX_comp_lift (godementPullbackLift f) (godementPullbackLift f') (compLift f f')
    (fun φ ψ => godementLiftHom_comp f f' φ ψ) φ ψ n

/-- The map of Godement section complexes induced by `ψ : A ⟶ f_* B`. -/
private noncomputable def secHom {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B) :
    (godementSections T).obj A ⟶ (godementSections T').obj B :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).map
    (((globalSections T).mapHomologicalComplex _).map
      (CokernelCoresolution.complexHom (godementPullbackLift f) ψ))

private theorem secHom_comp {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'} {B' : TopCat.Sheaf AddCommGrpCat.{u} T''}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B)
    (χ : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f').obj B') :
    secHom f ψ ≫ secHom f' χ =
      secHom (f' ≫ f) (ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map χ) := by
  unfold secHom
  refine (Functor.map_comp _ _ _).symm.trans (congrArg _ ?_)
  ext n : 1
  exact (Functor.map_comp (globalSections T) _ _).symm.trans
    (congrArg (globalSections T).map (complexHom_comp f f' ψ χ n))

private theorem godementSectionsPullback_comp_map (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    {L : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (b : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ L) :
    godementSectionsPullback f F ≫ (godementSections T').map b =
      secHom f ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map b) := by
  unfold godementSectionsPullback secHom
  refine (Functor.map_comp _ _ _).symm.trans (congrArg _ ?_)
  have h := CokernelCoresolution.complexFunctor_map_comp_complexHom (godementPullbackLift f)
    (𝟙 F) b ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat f).map b) (by rw [Category.id_comp])
  rw [CategoryTheory.Functor.map_id] at h
  have h' := (Category.id_comp _).symm.trans h
  ext n : 1
  exact (Functor.map_comp (globalSections T) _ _).symm.trans
    (congrArg (globalSections T).map (congrArg (fun φ => φ.f n) h'.symm))

end GodComp

/-! ### The map on Godement cohomology along a continuous map -/

section MapAlong

variable {T T' T'' : TopCat.{u}}

/-- The map `H^n(T, A) ⟶ H^n(T', B)` on Godement cohomology induced by `ψ : A ⟶ f_* B` along a
continuous map `f : T' ⟶ T`: the pullback `H^n(T, A) ⟶ H^n(T', f⁻¹ A)` followed by the adjoint
`f⁻¹ A ⟶ B` of `ψ`. -/
noncomputable def sheafCohomologyMapAlong (f : T' ⟶ T) {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (n : ℤ) :
    (sheafCohomology T n).obj A ⟶ (sheafCohomology T' n).obj B :=
  sheafCohomologyPullback f A n ≫ (sheafCohomology T' n).map
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv A B).symm ψ)

/-- The map along `f` induced by `ψ`, as one map of Godement double complexes. -/
private noncomputable def mapAlongDC (f : T' ⟶ T) {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) :
    godementSectionsDoubleComplex T ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A) ⟶
      godementSectionsDoubleComplex T'
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B) :=
  godementSectionsDoubleComplexPullback f _ ≫
    ((godementSections T').mapHomologicalComplex _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) 0).hom.app A ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv A B).symm
            ψ))

/-- Homology in degree `n` of the total complex of a double complex, as a functor. -/
private noncomputable abbrev totalH (n : ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      AddCommGrpCat.{u} :=
  HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c₁₂ := ComplexShape.up ℤ) ⋙ HomologicalComplex.homologyFunctor _ _ n

private theorem sheafCohomologyMapAlong_eq (f : T' ⟶ T) {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (n : ℤ) :
    sheafCohomologyMapAlong f ψ n = (totalH n).map (mapAlongDC f ψ) := by
  rw [mapAlongDC, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

private theorem mapAlongDC_f_zero (f : T' ⟶ T) {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) :
    (mapAlongDC f ψ).f 0 = secHom f ψ := by
  have h := godementSectionsPullback_comp_map f A
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv A B).symm ψ)
  have h2 : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app A ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat f).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv A B).symm ψ) =
      ψ :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  rw [h2] at h
  refine Eq.trans ?_ h
  simp [mapAlongDC, godementSectionsDoubleComplexPullback,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToHom_map]
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem mapAlongDC_f_eq_of_ne {A : TopCat.Sheaf AddCommGrpCat.{u} T} {q : ℤ}
    (hq : q ≠ 0)
    {K : CochainComplex AddCommGrpCat.{u} ℤ}
    (a b : (godementSectionsDoubleComplex T
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A)).X q ⟶ K) : a = b :=
  ((godementSections T).map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)).eq_of_src _ _

/-- **The maps along continuous maps compose.** -/
@[reassoc]
theorem sheafCohomologyMapAlong_comp (f : T' ⟶ T) (f' : T'' ⟶ T')
    {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    {B' : TopCat.Sheaf AddCommGrpCat.{u} T''}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (χ : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').obj B') (n : ℤ) :
    sheafCohomologyMapAlong f ψ n ≫ sheafCohomologyMapAlong f' χ n =
      sheafCohomologyMapAlong (f' ≫ f)
        (ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map χ) n := by
  rw [sheafCohomologyMapAlong_eq (f' ≫ f)]
  refine Eq.trans (b := (totalH n).map (mapAlongDC f ψ ≫ mapAlongDC f' χ)) ?_ (congrArg _ ?_)
  · rw [Functor.map_comp, sheafCohomologyMapAlong_eq, sheafCohomologyMapAlong_eq]
    rfl
  ext q : 1
  by_cases hq : q = 0
  · subst hq
    rw [HomologicalComplex.comp_f, mapAlongDC_f_zero, mapAlongDC_f_zero, mapAlongDC_f_zero]
    exact secHom_comp f f' ψ χ
  · exact mapAlongDC_f_eq_of_ne hq _ _

/-- The Godement pullback is natural in the sheaf. -/
@[reassoc]
private theorem sheafCohomology_map_comp_sheafCohomologyPullback (f : T' ⟶ T)
    {A A' : TopCat.Sheaf AddCommGrpCat.{u} T} (a : A ⟶ A') (n : ℤ) :
    (sheafCohomology T n).map a ≫ sheafCohomologyPullback f A' n =
      sheafCohomologyPullback f A n ≫
        (sheafCohomology T' n).map ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a) := by
  have hn := (HomologicalComplex.singleMapHomologicalComplex
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) 0).hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [sheafCohomologyPullback, sheafCohomology, Functor.comp_map]
  rw [hypercohomology_map_comp_hypercohomologyPullback_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, hn]

/-- **The map along `f` is natural in the source sheaf.** -/
@[reassoc]
theorem sheafCohomology_map_comp_sheafCohomologyMapAlong (f : T' ⟶ T)
    {A A' : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (a : A ⟶ A') (ψ : A' ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (n : ℤ) :
    (sheafCohomology T n).map a ≫ sheafCohomologyMapAlong f ψ n =
      sheafCohomologyMapAlong f (a ≫ ψ) n := by
  rw [sheafCohomologyMapAlong, sheafCohomologyMapAlong,
    sheafCohomology_map_comp_sheafCohomologyPullback_assoc, ← Functor.map_comp,
    Adjunction.homEquiv_naturality_left_symm]

/-- **The map along `f` is natural in the target sheaf.** -/
@[reassoc]
theorem sheafCohomologyMapAlong_comp_sheafCohomology_map (f : T' ⟶ T)
    {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B B' : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (b : B ⟶ B') (n : ℤ) :
    sheafCohomologyMapAlong f ψ n ≫ (sheafCohomology T' n).map b =
      sheafCohomologyMapAlong f (ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map b) n := by
  rw [sheafCohomologyMapAlong, sheafCohomologyMapAlong, Category.assoc, ← Functor.map_comp,
    Adjunction.homEquiv_naturality_right_symm]

end MapAlong

/-! ### Along a closed embedding -/

attribute [local instance] MMP.Analytic.globalSections_additive

section ClosedEmbedding

variable {T T' : TopCat.{u}}

/-- The pushforward of an injective resolution along a closed embedding, an injective resolution
of the pushforward: the pushforward is exact and preserves injectives. -/
private noncomputable def pushforwardInjectiveResolution (f : T' ⟶ T)
    (hf : Topology.IsClosedEmbedding f.hom) {G : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (J : InjectiveResolution G) :
    InjectiveResolution ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G) :=
  haveI : PreservesFiniteLimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) :=
    Stacks.ClosedImmersion.preservesFiniteLimits_closedInclusionPushforward f hf
  haveI : PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) :=
    Stacks.ClosedImmersion.preservesFiniteColimits_closedInclusionPushforward f hf
  haveI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  { cocomplex := ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj
      J.cocomplex
    injective := fun n =>
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).injective_obj (J.cocomplex.X n)
    ι := (HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (ComplexShape.up ℕ) 0).inv.app G ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map J.ι }

/-- **Along a closed embedding `f`, the map `H^n(T, f_* G) ⟶ H^n(T', G)` along `f` of the identity
of `f_* G` is bijective.** -/
theorem bijective_sheafCohomologyMapAlong_id_of_isClosedEmbedding (f : T' ⟶ T)
    (hf : Topology.IsClosedEmbedding f.hom) (G : TopCat.Sheaf AddCommGrpCat.{u} T') (n : ℕ) :
    Function.Bijective
      (sheafCohomologyMapAlong f (𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G)) n) := by
  obtain ⟨E, hE⟩ := (sheafCohomology_toolkit.{u, 0, 0, 0, 0} T).2.2.1.1
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  let J' : InjectiveResolution G := injectiveResolution G
  let J := pushforwardInjectiveResolution f hf J'
  have key := hE f _ G (adj.counit.app G) J J' (𝟙 _) ?_ n
  swap
  · rw [Adjunction.right_triangle_components]
    simp [J, pushforwardInjectiveResolution,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
    erw [eqToIso.hom, eqToIso.inv, eqToHom_refl, eqToHom_refl, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp]
  have hP : sheafCohomologyMapAlong f (𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G)) n =
      sheafCohomologyPullback f _ n ≫ (sheafCohomology T' n).map (adj.counit.app G) := by
    rw [sheafCohomologyMapAlong, Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hidx : ∀ z, HomologicalComplex.homologyMap
      (((globalSections T).mapHomologicalComplex _).map (𝟙 J.cocomplex)) n z = z := fun z => by
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
    rfl
  rw [hP]
  let aE := ((E T n).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G)
    ).addCommGroupIsoToAddEquiv
  let aJ := (J.isoRightDerivedObj (globalSections T) n).addCommGroupIsoToAddEquiv
  let aJ' := (J'.isoRightDerivedObj (globalSections T') n).symm.addCommGroupIsoToAddEquiv
  let aE' := ((E T' n).app G).addCommGroupIsoToAddEquiv
  refine ⟨?_, fun z => ⟨aE.symm (aJ.symm (aJ'.symm (aE' z))), ?_⟩⟩
  swap
  · apply aE'.injective
    have kw := ConcreteCategory.congr_hom key (aE.symm (aJ.symm (aJ'.symm (aE' z))))
    simp only [ConcreteCategory.comp_apply] at kw
    refine kw.trans ?_
    erw [ConcreteCategory.comp_apply, hidx]
    exact (congrArg aJ' ((congrArg aJ (aE.apply_symm_apply _)).trans
      (aJ.apply_symm_apply _))).trans (aJ'.apply_symm_apply _)
  intro x y hxy
  have kx := ConcreteCategory.congr_hom key x
  have ky := ConcreteCategory.congr_hom key y
  simp only [ConcreteCategory.comp_apply] at kx ky hxy
  rw [hxy, ky] at kx
  have h3 := aJ'.injective kx
  erw [hidx, hidx] at h3
  exact aE.injective (aJ.injective h3).symm

end ClosedEmbedding

/-! ### Derived functor cohomology and Godement cohomology -/

section ModuleCohomology

/-- **Injectivity on cohomology over a field gives injectivity on Godement cohomology.** For a
morphism `φ` of `𝒪_X`-modules on a scheme over a field `k`, if `φ` induces an injection on
`cohomologyOverField`, it induces an injection on the Godement cohomology of the underlying
abelian sheaves: the two cohomologies are naturally isomorphic. -/
theorem injective_sheafCohomology_map_of_injective_cohomologyOverFieldMap {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {M N : X.Modules} (φ : M ⟶ N) (n : ℕ)
    (h : Function.Injective (cohomologyOverFieldMap k f φ n).hom) :
    Function.Injective ((sheafCohomology X.toPresheafedSpace.carrier n).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)) := by
  obtain ⟨E, -⟩ := (sheafCohomology_toolkit.{u, 0, 0, 0, 0} X.toPresheafedSpace.carrier).2.2.1.1
  have h0 : Function.Injective
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).map φ).hom :=
    by
      have hm : Mono (cohomologyOverFieldMap k f φ n) := (ModuleCat.mono_iff_injective _).2 h
      unfold cohomologyOverFieldMap at hm
      have hm2 := (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mono_of_mono_map hm
      exact (ModuleCat.mono_iff_injective _).1 hm2
  have h1 : Function.Injective
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map φ) :=
    fun x y hxy => h0 hxy
  have h2 := Stacks.Cohomology.TopDegree.injective_map_of_natIso
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ n) φ h1
  have h3 := Stacks.Cohomology.TopDegree.injective_map_of_natIso
    (Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf ⊤ n) φ h2
  exact Stacks.Cohomology.TopDegree.injective_map_of_natIso (E X.toPresheafedSpace.carrier n).symm
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) h3

/-- Godement cohomology of the abelian sheaf underlying an `𝒪_X`-module, naturally isomorphic to
its derived functor cohomology, given a natural identification `E` of Godement cohomology with the
right derived functors of global sections. -/
private noncomputable def godementIso
    (E : ∀ (S : TopCat.{u}) (n : ℕ), sheafCohomology S n ≅ (globalSections S).rightDerived n)
    (X : Scheme.{u}) (n : ℕ) :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafCohomology X.toPresheafedSpace.carrier n ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft _ (E X.toPresheafedSpace.carrier n) ≪≫
    (Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf ⊤ n).symm ≪≫
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ n).symm

/-- The identification of Godement cohomology with cohomology over the base field. -/
private noncomputable def godementAddEquiv
    (E : ∀ (S : TopCat.{u}) (n : ℕ), sheafCohomology S n ≅ (globalSections S).rightDerived n)
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (M : X.Modules) (n : ℕ) :
    (sheafCohomology X.toPresheafedSpace.carrier n).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≃+
      cohomologyOverField k f M n :=
  ((godementIso E X n).app M).addCommGroupIsoToAddEquiv

private theorem godementAddEquiv_naturality
    (E : ∀ (S : TopCat.{u}) (n : ℕ), sheafCohomology S n ≅ (globalSections S).rightDerived n)
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {M N : X.Modules}
    (φ : M ⟶ N) (n : ℕ) (x) :
    godementAddEquiv E f N n ((sheafCohomology X.toPresheafedSpace.carrier n).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x) =
      (cohomologyOverFieldMap k f φ n).hom (godementAddEquiv E f M n x) := by
  have h := ConcreteCategory.congr_hom ((godementIso E X n).hom.naturality φ) x
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  rw [cohomologyOverFieldMap]
  rfl

end ModuleCohomology

/-! ### The analytic restriction and the algebraic one -/

section Analytic

variable {X Z : Scheme.{0}}

/-- `α_X^#` as a morphism of abelian sheaves `𝒪_X ⟶ (α_X)_* 𝒪_{X^an}`. -/
noncomputable def analyticSharp (sX : X ⟶ Spec (.of ℂ)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).obj (analyticO sX) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map
    (SheafOfModules.unitToPushforwardObjUnit (ringCatSheafHom sX))

/-- **Analytification commutes with restriction of functions**: restricting a regular function
to `Z` and analytifying is analytifying and composing with `i^an`. -/
private theorem analyticSharp_comp_analyticPullbackOfModel {sX : X ⟶ Spec (.of ℂ)}
    (i : Z ⟶ X) (MX : HolomorphicModel sX) (MZ : HolomorphicModel (i ≫ sX)) :
    (analyticSharp sX ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).map
        (analyticPullbackOfModel MX MZ i rfl) :
      _ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom (i ≫ sX) ≫ i.base)).obj
        (analyticO (i ≫ sX))) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map
          (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} i.base).map (analyticSharp (i ≫ sX)) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  ext s
  refine MZ.ext fun y => ?_
  obtain ⟨W⟩ := W
  let := MX.cs
  let := MZ.cs
  have hf := contMDiff_realize i rfl MX.atlas_coords MZ.Θ MZ.hΘ
  have e1 := analyticPullback_apply i rfl hf MX.Θ MZ.Θ ((Opens.map (toSchemeHom sX)).obj W)
    ((analytificationHom sX).hom.c.app (op W) s) y
  have e2 := MX.hΘ W s ⟨realize i rfl y.1, y.2⟩
  have e3 := MZ.hΘ (i ⁻¹ᵁ W) (i.app W s) y
  have e4 := evalHom_appLE_realize (sX := sX) i rfl (le_refl (i ⁻¹ᵁ W))
    ⟨y.1, mem_chart_iff.2 y.2⟩ s
  rw [← Scheme.Hom.app_eq_appLE] at e4
  exact e1.trans (e2.trans (e4.symm.trans e3.symm))

/-- The comparison map of GAGA for `𝒪_X`, followed by `𝒪_X^an ≅ 𝒪_{X^an}`, is the map along
`α_X` induced by `α_X^#`. -/
private theorem comparisonMap_comp_eq_sheafCohomologyMapAlong (sX : X ⟶ Spec (.of ℂ)) (q : ℤ) :
    comparisonMap sX (SheafOfModules.unit X.ringCatSheaf) q ≫
        (sheafCohomology (space sX) q).map ((SheafOfModules.toSheaf _).map
          (SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom sX))) =
      sheafCohomologyMapAlong (toSchemeHom sX) (analyticSharp sX) q := by
  unfold comparisonMap sheafCohomologyMapAlong
  refine (Category.assoc _ _ _).trans (congrArg (sheafCohomologyPullback _ _ q ≫ ·) ?_)
  refine (Functor.map_comp _ _ _).symm.trans (congrArg _ ?_)
  have hmod : (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)).unit.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map
        (SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom sX)) =
      SheafOfModules.unitToPushforwardObjUnit (ringCatSheafHom sX) :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  refine (Equiv.eq_symm_apply _).2 ?_
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  exact ((SheafOfModules.toSheaf X.ringCatSheaf).map_comp _ _).symm.trans
    (congrArg (SheafOfModules.toSheaf X.ringCatSheaf).map hmod)

/-- **GAGA for `𝒪` in every degree**, as the map along `α_X` induced by `α_X^#`: for `X`
projective over `ℂ` it is an isomorphism `H^q(X, 𝒪_X) ≅ H^q(X^an, 𝒪_{X^an})`. -/
theorem isIso_sheafCohomologyMapAlong_analyticSharp (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjective sX) (q : ℤ) :
    IsIso (sheafCohomologyMapAlong (toSchemeHom sX) (analyticSharp sX) q) := by
  have : IsProper sX := hX.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have h0 : IsIso (comparisonMap sX (SheafOfModules.unit X.ringCatSheaf) q) :=
    isIso_comparisonMap_of_isProjective sX hX _
      (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
        (Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X)) _
  have := Stacks.Topology.final_opensMap (toSchemeHom sX)
  have h1 : IsIso (SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom sX)) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (ringCatSheafHom sX)
  have h2 : IsIso ((sheafCohomology (space sX) q).map ((SheafOfModules.toSheaf _).map
      (SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom sX)))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ h1)
  rw [← comparisonMap_comp_eq_sheafCohomologyMapAlong]
  exact IsIso.comp_isIso' h0 h2

/-- The diagram chase behind `exists_addEquiv_analyticRestrictionH1`: a map conjugate, through
equivalences, to a map that factors as an equivalence after a map conjugate to `q`, is
conjugate to an equivalence after `q`. -/
private theorem exists_addEquiv_comp_eq {HX HZ GanX GanZ GX GZ GP AX AP AZ : Type*} [Add HX]
    [Add HZ] [Add GanX] [Add GanZ] [Add GX] [Add GZ] [Add GP] [Add AX] [Add AP] [Add AZ]
    (res : HX → HZ) (e1 : HX ≃+ GanX) (R : GanX → GanZ) (e2 : GanZ ≃+ HZ)
    (hres : ∀ x, res x = e2 (R (e1 x))) (cX : GX ≃+ GanX) (cZ : GZ ≃+ GanZ) (G : GX → GZ)
    (hsq : ∀ v, R (cX v) = cZ (G v)) (P : GP ≃+ GZ) (Q : GX → GP) (hG : ∀ v, G v = P (Q v))
    (DX : GX ≃+ AX) (DP : GP ≃+ AP) (q : AX → AP) (hD : ∀ v, DP (Q v) = q (DX v))
    (p : AP ≃+ AZ) :
    ∃ (eX : HX ≃+ AX) (eZ : HZ ≃+ AZ), ∀ x, eZ (res x) = p (q (eX x)) := by
  refine ⟨e1.trans (cX.symm.trans DX), e2.symm.trans (cZ.symm.trans (P.symm.trans (DP.trans p))),
    fun x => ?_⟩
  obtain ⟨v, hv⟩ := cX.surjective (e1 x)
  simp only [AddEquiv.trans_apply, hres, ← hv, hsq, hG, AddEquiv.symm_apply_apply, hD]

/-- **GAGA intertwines the analytic and the algebraic restriction of `H¹(𝒪)`.** Let `X` be a
smooth projective variety over `ℂ` and `i : Z ⟶ X` a closed immersion with `Z` smooth over `ℂ`.
There are additive isomorphisms `H¹(X^an, 𝒪) ≃ H¹(X, 𝒪_X)` and `H¹(Z^an, 𝒪) ≃ H¹(Z, 𝒪_Z)`
carrying the restriction `H¹(X^an, 𝒪) ⟶ H¹(Z^an, 𝒪)` to the algebraic restriction
`H¹(X, 𝒪_X) ⟶ H¹(X, i_* 𝒪_Z) ≅ H¹(Z, 𝒪_Z)`. -/
theorem exists_addEquiv_analyticRestrictionH1
    (f : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f] (i : Z ⟶ X) [IsClosedImmersion i]
    {nX nZ : ℕ} [SmoothOfRelativeDimension nX f] [SmoothOfRelativeDimension nZ (i ≫ f)] :
    ∃ (eX : Sheaf.H (analyticO f) 1 ≃+
        cohomologyOverField ℂ f (SheafOfModules.unit X.ringCatSheaf) 1)
      (eZ : Sheaf.H (analyticO (i ≫ f)) 1 ≃+
        cohomologyOverField ℂ (i ≫ f) (SheafOfModules.unit Z.ringCatSheaf) 1),
      ∀ x, eZ (analyticRestrictionH1 (sX := f) i rfl x) =
        (cohomologyOverFieldMap ℂ f
            (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) 1 ≫
          (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion ℂ i f
            (SheafOfModules.unit Z.ringCatSheaf) 1).inv).hom (eX x) := by
  obtain ⟨E, -⟩ := (sheafCohomology_toolkit.{0, 0, 0, 0, 0} X.toPresheafedSpace.carrier).2.2.1.1
  have hX : IsProjective f := ((isProjectiveVariety_iff_isProjective' ℂ f).mp inferInstance).2
  have hZ : IsProjective (i ≫ f) :=
    Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion i f
      inferInstance hX
  obtain ⟨MX, MZ, hres⟩ :=
    exists_analyticRestrictionH1_eq (nX := nX) (nC := nZ) (sX := f) (sC := i ≫ f) i rfl
  let u := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  let uab : (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} i.base).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (SheafOfModules.unit Z.ringCatSheaf)) :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map u
  let cX := sheafCohomologyMapAlong (toSchemeHom f) (analyticSharp f) ((1 : ℕ) : ℤ)
  let cZ := sheafCohomologyMapAlong (toSchemeHom (i ≫ f)) (analyticSharp (i ≫ f)) ((1 : ℕ) : ℤ)
  let R := sheafCohomologyMapAlong (analyticMap i rfl) (analyticPullbackOfModel MX MZ i rfl)
    ((1 : ℕ) : ℤ)
  let P := sheafCohomologyMapAlong i.base
    (𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} i.base).obj
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (SheafOfModules.unit Z.ringCatSheaf))))
    ((1 : ℕ) : ℤ)
  have : IsIso cX := isIso_sheafCohomologyMapAlong_analyticSharp f hX _
  have : IsIso cZ := isIso_sheafCohomologyMapAlong_analyticSharp (i ≫ f) hZ _
  have hPb : Function.Bijective P :=
    bijective_sheafCohomologyMapAlong_id_of_isClosedEmbedding i.base i.isClosedEmbedding _ 1
  let aP := AddEquiv.ofBijective P.hom hPb
  let e1 := ((MMP.JacobianLogarithm.extIso (analyticSpace f)).app (analyticO f)).symm
  let e2 := (MMP.JacobianLogarithm.extIso (analyticSpace (i ≫ f))).app (analyticO (i ≫ f))
  have hsq : cX ≫ R = sheafCohomologyMapAlong i.base uab ((1 : ℕ) : ℤ) ≫ cZ :=
    (sheafCohomologyMapAlong_comp _ _ _ _ _).trans
      ((congrArg (fun Φ => sheafCohomologyMapAlong (toSchemeHom (i ≫ f) ≫ i.base) Φ
        ((1 : ℕ) : ℤ)) (analyticSharp_comp_analyticPullbackOfModel i MX MZ)).trans
        (sheafCohomologyMapAlong_comp _ _ _ _ _).symm)
  have hGP : (sheafCohomology X.toPresheafedSpace.carrier ((1 : ℕ) : ℤ)).map uab ≫ P =
      sheafCohomologyMapAlong i.base uab ((1 : ℕ) : ℤ) :=
    (sheafCohomology_map_comp_sheafCohomologyMapAlong i.base uab (𝟙 _) ((1 : ℕ) : ℤ)).trans
      (congrArg (fun ψ => sheafCohomologyMapAlong i.base ψ ((1 : ℕ) : ℤ)) (Category.comp_id uab))
  have hres' : ∀ x, analyticRestrictionH1 (sX := f) i rfl x =
      e2.addCommGroupIsoToAddEquiv (R (e1.addCommGroupIsoToAddEquiv x)) := by
    intro x
    rw [hres]
    rfl
  exact exists_addEquiv_comp_eq (analyticRestrictionH1 (sX := f) i rfl)
    e1.addCommGroupIsoToAddEquiv R e2.addCommGroupIsoToAddEquiv hres'
    (asIso cX).addCommGroupIsoToAddEquiv (asIso cZ).addCommGroupIsoToAddEquiv
    (sheafCohomologyMapAlong i.base uab ((1 : ℕ) : ℤ))
    (fun v => by
      have k := ConcreteCategory.congr_hom hsq v
      simp only [ConcreteCategory.comp_apply] at k
      exact k)
    aP ((sheafCohomology X.toPresheafedSpace.carrier ((1 : ℕ) : ℤ)).map uab)
    (fun v => by
      have k := (ConcreteCategory.congr_hom hGP v).symm
      simp only [ConcreteCategory.comp_apply] at k
      exact k)
    (godementAddEquiv E f (SheafOfModules.unit X.ringCatSheaf) 1)
    (godementAddEquiv E f ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) 1)
    (cohomologyOverFieldMap ℂ f u 1).hom (godementAddEquiv_naturality E f u 1)
    (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion ℂ i f
      (SheafOfModules.unit Z.ringCatSheaf) 1).symm.toLinearEquiv.toAddEquiv

/-- **The analytic restriction of `H¹(𝒪)` to a closed subscheme is injective when the algebraic
one is.** Let `X` be a smooth projective variety over `ℂ` and `i : Z ⟶ X` a closed immersion
with `Z` smooth over `ℂ`. If the algebraic restriction
`H¹(X, 𝒪_X) ⟶ H¹(X, i_* 𝒪_Z) ≅ H¹(Z, 𝒪_Z)` is injective, then so is the restriction
`H¹(X^an, 𝒪) ⟶ H¹(Z^an, 𝒪)` of the analytifications. -/
theorem injective_analyticRestrictionH1_of_injective
    (f : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f] (i : Z ⟶ X) [IsClosedImmersion i]
    {nX nZ : ℕ} [SmoothOfRelativeDimension nX f] [SmoothOfRelativeDimension nZ (i ≫ f)]
    (h : Function.Injective (cohomologyOverFieldMap ℂ f
        (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) 1 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion ℂ i f
        (SheafOfModules.unit Z.ringCatSheaf) 1).inv).hom) :
    Function.Injective (analyticRestrictionH1 (sX := f) i rfl) := by
  obtain ⟨eX, eZ, he⟩ := exists_addEquiv_analyticRestrictionH1 (nX := nX) (nZ := nZ) f i
  intro x y hxy
  exact eX.injective (h (by rw [← he, ← he, hxy]))

/-- GAGA intertwines `analyticRestrictionH1` along the zero scheme `Z` of a section `s` of
an invertible sheaf `L` with the algebraic restriction
`H¹(X, 𝒪_X) ⟶ H¹(X, i_* 𝒪_Z) ≅ H¹(Z, 𝒪_Z)`. -/
theorem exists_addEquiv_analyticRestrictionH1_zeroScheme
    (f : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f] {nX nZ : ℕ}
    [SmoothOfRelativeDimension nX f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    [SmoothOfRelativeDimension nZ ((zeroScheme X L s).subschemeι ≫ f)] :
    ∃ (eX : Sheaf.H (analyticO f) 1 ≃+
        cohomologyOverField ℂ f (SheafOfModules.unit X.ringCatSheaf) 1)
      (eZ : Sheaf.H (analyticO ((zeroScheme X L s).subschemeι ≫ f)) 1 ≃+
        cohomologyOverField ℂ ((zeroScheme X L s).subschemeι ≫ f)
          (SheafOfModules.unit (zeroScheme X L s).subscheme.ringCatSheaf) 1),
      ∀ x, eZ (analyticRestrictionH1 (sX := f) (zeroScheme X L s).subschemeι rfl x) =
        (cohomologyOverFieldMap ℂ f
            (Stacks.IdealSheafSequence.divisorQuotientMap (zeroScheme X L s)) 1 ≫
          (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion ℂ (zeroScheme X L s).subschemeι f
            (SheafOfModules.unit (zeroScheme X L s).subscheme.ringCatSheaf) 1).inv).hom
          (eX x) :=
  exists_addEquiv_analyticRestrictionH1 (nX := nX) (nZ := nZ) f (zeroScheme X L s).subschemeι

/-- **The analytic restriction of `H¹(𝒪)` to the zero scheme of a section is injective when the
algebraic one is.** -/
theorem injective_analyticRestrictionH1_zeroScheme_of_injective
    (f : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f] {nX nZ : ℕ}
    [SmoothOfRelativeDimension nX f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    [SmoothOfRelativeDimension nZ ((zeroScheme X L s).subschemeι ≫ f)]
    (h : Function.Injective (cohomologyOverFieldMap ℂ f
        (Stacks.IdealSheafSequence.divisorQuotientMap (zeroScheme X L s)) 1 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion ℂ (zeroScheme X L s).subschemeι f
        (SheafOfModules.unit (zeroScheme X L s).subscheme.ringCatSheaf) 1).inv).hom) :
    Function.Injective
      (analyticRestrictionH1 (sX := f) (zeroScheme X L s).subschemeι rfl) :=
  injective_analyticRestrictionH1_of_injective (nX := nX) (nZ := nZ) f
    (zeroScheme X L s).subschemeι h

end Analytic

end MMP.Analytic.SurfaceHodge
