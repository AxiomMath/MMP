module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegBirational
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageRingedSpace
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityFromCechVanishing
import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle
import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryPushforward
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Singularities.DltLogResolutionCriterion
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Vanishing.CoveringTrick
import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction

/-!
# The round down of a plt dlt pair is normal

Let `(X, Δ)` be a dlt pair of dimension `n ≥ 2` with `Δ` effective, over an algebraically
closed field of characteristic zero. If `(X, Δ)` is plt, then the reduced scheme on the support
of `⌊Δ⌋` is normal.

Take a log resolution `g : Y ⟶ X` on which the strict transforms `T_P` of the components `P` of
`⌊Δ⌋` are smooth and pairwise disjoint, and let `Θ` be the crepant boundary,
`K_Y + Θ = g^*(K_X + Δ)`. Since `(X, Δ)` is plt, `G = -⌊Θ⌋` has coefficient `-1` along each
`T_P` and is effective elsewhere, and `H = G + ∑ T_P` is effective and `g`-exceptional. Relative
Kawamata–Viehweg vanishing gives `R¹g_* 𝒪_Y(G) = 0`, so over an affine open `U ⊆ X` every family
of local sections of `𝒪_Y(H)` that agree along the `T_P` modulo `𝒪_Y(G)` lifts to a section
of `𝒪_Y(H)` over `g⁻¹U`, which is a regular function on `U` because `H` is effective and
exceptional. Applied to locally constant data this shows that the components of `⌊Δ⌋` are
disjoint, and applied to the local lifts of a function integral over `𝒪(P ∩ U)` (which is
regular on the normal `T_P`) it shows that `P ∩ U` is normal.

## Main results

* `MMP.Mori.IsDltPair.isNormal_suppScheme_roundDown`: if a dlt pair `(X, Δ)` is plt, then
  `⌊Δ⌋` is normal.

## Implementation notes

The source passes through the sheaf `𝒪_{⌊Δ'⌋}(⌈E⌉)` and the normalisation of `⌊Δ⌋`. Here the
quotient `𝒪_Y(H)/𝒪_Y(G)` plays the role of `𝒪_{⌊Δ'⌋}(⌈E⌉)`, and surjectivity of
`Γ(g⁻¹U, 𝒪_Y(H)) → Γ(g⁻¹U, 𝒪_Y(H)/𝒪_Y(G))` is used in the form of a lifting property for local
regular functions modulo vanishing along the `T_P`. Normality is then checked directly on affine
charts: `𝒪(U)/𝔭_P` embeds in the residue field of `Y` at the generic point of `T_P`, and an
element integral over it is regular on the normal `T_P ∩ g⁻¹U`, hence lifts. This is the same
argument with the normalisation replaced by integral closure in the function field.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.51
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

@[expose] public section

namespace MMP.Mori

/-! ### Lifting through a subsheaf without first higher direct image -/

section Lift

private theorem isZero_rightDerived_one_sections_preimage {X Y : Scheme.{0}} (g : Y ⟶ X)
    [QuasiCompact g] [QuasiSeparated g] {U : X.Opens} (hU : IsAffineOpen U) (A : Y.Modules)
    [A.IsQuasicoherent] (h : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj A)) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections (g ⁻¹ᵁ U).toScheme).rightDerived
      1).obj ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).obj A)) := by
  haveI : IsAffine U.toScheme := hU
  have h1 : IsZero (((Scheme.Modules.pushforward (g ∣_ U)).rightDerived 1).obj
      ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).obj A)) :=
    (Functor.map_isZero (Scheme.Modules.restrictFunctor U.ι) h).of_iso
      ((Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso g U 1).app A)
  have h3 := (Functor.map_isZero (Stacks.Cohomology.AffineBase.moduleGlobalSections U.toScheme)
    h1).of_iso ((Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso (g ∣_ U) 1).app
      ⟨(Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).obj A, inferInstance⟩)
  rwa [ModuleCat.isZero_iff_subsingleton] at h3 ⊢

private theorem shortExact_cokernel {Y : Scheme.{0}} {A B : Y.Modules} (ι : A ⟶ B) [Mono ι] :
    (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι))
    inferInstance inferInstance

private theorem surjective_cokernel_π_app_preimage {X Y : Scheme.{0}} (g : Y ⟶ X)
    [QuasiCompact g] [QuasiSeparated g] {U : X.Opens} (hU : IsAffineOpen U) {A B : Y.Modules}
    (ι : A ⟶ B) [Mono ι] [A.IsQuasicoherent]
    (h : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj A)) :
    Function.Surjective ((cokernel.π ι).app (g ⁻¹ᵁ U)) := by
  have hSV := (shortExact_cokernel ι).map_of_exact
    (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι)
  have hs := (ModuleCat.epi_iff_surjective _).mp
    (Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (g ⁻¹ᵁ U).toScheme) hSV
      (isZero_rightDerived_one_sections_preimage g hU A h)).epi_g
  change Function.Surjective ((cokernel.π ι).app ((g ⁻¹ᵁ U).ι ''ᵁ ⊤)) at hs
  rwa [Scheme.Opens.ι_image_top] at hs

private theorem exists_app_eq_of_cokernel_π_app_eq_zero {Y : Scheme.{0}} {A B : Y.Modules}
    (ι : A ⟶ B) [Mono ι] (W : Y.Opens) (x : B.presheaf.obj (op W))
    (hx : (cokernel.π ι).app W x = 0) : ∃ a, ι.app W a = x := by
  have hE := (shortExact_cokernel ι).exact.map_of_mono_of_preservesKernel
    (Scheme.Modules.restrictFunctor W.ι ⋙
      Stacks.Cohomology.AffineBase.moduleGlobalSections W.toScheme) inferInstance inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hE
  have key : ∀ x : B.presheaf.obj (op (W.ι ''ᵁ ⊤)), (cokernel.π ι).app (W.ι ''ᵁ ⊤) x = 0 →
      ∃ a, ι.app (W.ι ''ᵁ ⊤) a = x := fun x hx => hE x hx
  rw [Scheme.Opens.ι_image_top] at key
  exact key x hx

private theorem exists_presheaf_map_eq_of_isCompatible {Y : Scheme.{0}} (Q : Y.Modules) {I : Type}
    (W : I → Y.Opens) (q : ∀ i, Q.presheaf.obj (op (W i)))
    (hq : ∀ i j, Q.presheaf.map (homOfLE inf_le_left : W i ⊓ W j ⟶ W i).op (q i) =
      Q.presheaf.map (homOfLE inf_le_right : W i ⊓ W j ⟶ W j).op (q j)) :
    ∃ s : Q.presheaf.obj (op (⨆ i, W i)), ∀ i,
      Q.presheaf.map (homOfLE (le_iSup W i)).op s = q i := by
  have hsh : TopCat.Presheaf.IsSheaf Q.presheaf := Q.isSheaf
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing] at hsh
  obtain ⟨s, hs, -⟩ := hsh W q hq
  exact ⟨s, hs⟩

/-- **Lifting modulo a subsheaf with vanishing `R¹g_*`.** Let `g : Y ⟶ X` be quasi-compact and
quasi-separated, `A ⊆ B` modules on `Y` with `A` quasi-coherent and `R¹g_* A = 0`, and `U ⊆ X`
an affine open. Then a family of sections `bᵢ` of `B` on an open cover of `g⁻¹U` which agree
modulo `A` on overlaps is congruent modulo `A` to a single section of `B` over `g⁻¹U`: the class
of the family is a section of `B / A` over `g⁻¹U`, and `Γ(g⁻¹U, B) → Γ(g⁻¹U, B / A)` is onto
because `H¹(g⁻¹U, A) = Γ(U, R¹g_* A) = 0`. -/
private theorem exists_sub_mem_range_of_isZero_rightDerived_one {X Y : Scheme.{0}} (g : Y ⟶ X)
    [QuasiCompact g] [QuasiSeparated g] {U : X.Opens} (hU : IsAffineOpen U) {A B : Y.Modules}
    (ι : A ⟶ B) [Mono ι] [A.IsQuasicoherent]
    (h : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj A)) {I : Type}
    (W : I → Y.Opens) (hW : ⨆ i, W i = g ⁻¹ᵁ U) (b : ∀ i, B.presheaf.obj (op (W i)))
    (hb : ∀ i j, B.presheaf.map (homOfLE inf_le_left : W i ⊓ W j ⟶ W i).op (b i) -
      B.presheaf.map (homOfLE inf_le_right : W i ⊓ W j ⟶ W j).op (b j) ∈
        Set.range (ι.app (W i ⊓ W j))) :
    ∃ r : B.presheaf.obj (op (g ⁻¹ᵁ U)), ∀ i,
      B.presheaf.map (homOfLE (hW ▸ le_iSup W i : W i ≤ g ⁻¹ᵁ U)).op r - b i ∈
        Set.range (ι.app (W i)) := by
  set π := cokernel.π ι
  obtain ⟨s, hs⟩ := exists_presheaf_map_eq_of_isCompatible (cokernel ι) W (fun i => π.app _ (b i))
    fun i j => by
      rw [← Scheme.Modules.Hom.app_presheaf_map, ← Scheme.Modules.Hom.app_presheaf_map,
        ← sub_eq_zero, ← map_sub]
      obtain ⟨a, ha⟩ := hb i j
      rw [← ha]
      change (ι ≫ π).app _ a = 0
      rw [cokernel.condition]
      rfl
  obtain ⟨r, hr⟩ := surjective_cokernel_π_app_preimage g hU ι h
    ((cokernel ι).presheaf.map (eqToHom hW.symm).op s)
  refine ⟨r, fun i => exists_app_eq_of_cokernel_π_app_eq_zero ι _ _ ?_⟩
  rw [map_sub, Scheme.Modules.Hom.app_presheaf_map, hr, ← hs i, sub_eq_zero]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end Lift

/-! ### Vanishing along a prime divisor and the lifting property -/

/-- A section `φ` of `𝒪_Y` over `W` *vanishes along* the prime divisor `E` if, when `E` meets
`W`, the germ of `φ` at the generic point of `E` lies in the maximal ideal of `𝒪_{Y,E}`. -/
private def VanishesAlong {Y : Scheme.{0}} (E : MMP.Mori.PrimeDivisor Y) (W : Y.Opens)
    (φ : Γ(Y, W)) : Prop :=
  ∀ h : E.genericPoint ∈ W, Y.presheaf.germ W E.genericPoint h φ ∈
    IsLocalRing.maximalIdeal (Y.presheaf.stalk E.genericPoint)

/-- The lifting property delivered by Kawamata–Viehweg vanishing: over an affine open `U ⊆ X`,
regular functions on an open cover of `g⁻¹U` that agree along the `T P` on overlaps are, along the
`T P`, the pullback of a single regular function on `U`. -/
private def HasLift {X Y : Scheme.{0}} (g : Y ⟶ X) (S : Finset (MMP.Mori.PrimeDivisor X))
    (T : S → MMP.Mori.PrimeDivisor Y) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ (I : Type) (W : I → Y.Opens) (hW : ⨆ i, W i = g ⁻¹ᵁ U)
    (φ : ∀ i, Γ(Y, W i)),
    (∀ i j, ∀ P : S, VanishesAlong (T P) (W i ⊓ W j)
      (Y.presheaf.map (homOfLE inf_le_left : W i ⊓ W j ⟶ W i).op (φ i) -
        Y.presheaf.map (homOfLE inf_le_right : W i ⊓ W j ⟶ W j).op (φ j))) →
    ∃ ψ : Γ(X, U), ∀ i, ∀ P : S, VanishesAlong (T P) (W i)
      (Y.presheaf.map (homOfLE (hW ▸ le_iSup W i : W i ≤ g ⁻¹ᵁ U)).op (g.app U ψ) - φ i)

/-! ### The lifting property from the vanishing of `R¹g_* 𝒪_Y(G)` -/

section HasLift

/-- An element of `𝒪_{Y,E}` has `v_E ≥ 0`. -/
private theorem ordGE_zero_toComponent {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (b : E.localRing) : E.OrdGE 0 (E.toComponent.hom b) := by
  by_cases hb : b = 0
  · exact Or.inl (by rw [hb, map_zero])
  · exact Or.inr (by rw [WithZero.exp_zero]; exact E.one_le_valuation_toComponent hb)

/-- The component of a regular function along a prime divisor `E` is its germ at `η_E`. -/
private theorem toRationalFunctionsPresheaf_app_apply_eq_toComponent {Y : Scheme.{0}}
    (E : MMP.Mori.PrimeDivisor Y) {W : Y.Opens} (h : (E.support ∩ W).Nonempty) (φ : Γ(Y, W)) :
    (toRationalFunctionsPresheaf Y).app (op W) φ
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty h⟩ =
      E.toComponent.hom
        (Y.presheaf.germ W E.genericPoint (E.genericPoint_mem_of_nonempty h) φ) := by
  rw [toRationalFunctionsPresheaf_app_apply]
  exact (TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf _ _ φ).symm

/-- For a divisor `G` with coefficient `-1` along each `T P` and effective elsewhere, a regular
function is a section of `𝒪_Y(G)` exactly when it vanishes along every `T P`. -/
private theorem isDivisorialSection_iff_vanishesAlong {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] {ι : Type} (T : ι → MMP.Mori.PrimeDivisor Y) (G : Divisor Y)
    (hGT : ∀ P, G.coeff (T P) = -1) (hGE : ∀ E, (∀ P, E ≠ T P) → 0 ≤ G.coeff E)
    (W : Y.Opens) (φ : Γ(Y, W)) :
    G.IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) φ) ↔
      ∀ P, VanishesAlong (T P) W φ := by
  constructor
  · intro h P hP
    have hne : ((T P).support ∩ W).Nonempty := ⟨_, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, hP⟩
    have := h (T P) hne
    rwa [hGT, neg_neg, toRationalFunctionsPresheaf_app_apply_eq_toComponent _ hne,
      MMP.Mori.ordGE_one_toComponent_iff] at this
  · intro h E hE
    rw [toRationalFunctionsPresheaf_app_apply_eq_toComponent _ hE]
    by_cases hET : ∃ P, E = T P
    · obtain ⟨P, rfl⟩ := hET
      rw [hGT, neg_neg, MMP.Mori.ordGE_one_toComponent_iff]
      exact h P _
    · simp only [not_exists] at hET
      exact (ordGE_zero_toComponent E _).mono (neg_nonpos.mpr (hGE E hET))

/-- **The lifting property.** Let `G ≤ H` be divisors on `Y` with `H` effective, `G` of
coefficient `-1` along each `T P` and effective elsewhere, such that sections of `𝒪_Y(H)` over
`g⁻¹U` are pullbacks of regular functions on `U`. If `R¹g_* 𝒪_Y(G) = 0`, then `g` has the lifting
property along the `T P`. -/
private theorem hasLift_of_isZero_rightDerived {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (g : Y ⟶ X) [QuasiCompact g] [QuasiSeparated g]
    (S : Finset (MMP.Mori.PrimeDivisor X)) (T : S → MMP.Mori.PrimeDivisor Y)
    {G H : Divisor Y} (hGH : G ≤ H) (hH : 0 ≤ H)
    (hGT : ∀ P, G.coeff (T P) = -1) (hGE : ∀ E, (∀ P, E ≠ T P) → 0 ≤ G.coeff E)
    (hsec : ∀ U : X.Opens, IsAffineOpen U → ∀ r, H.IsDivisorialSection (g ⁻¹ᵁ U) r →
      ∃ ψ : Γ(X, U), (toRationalFunctionsPresheaf Y).app (op (g ⁻¹ᵁ U)) (g.app U ψ) = r)
    (hR1 : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj G.divisorialSheaf)) :
    HasLift g S T := by
  intro U hU I W hW φ hφ
  let ι := Divisor.divisorialSheafInclusion hGH
  let b : ∀ i, H.divisorialSheaf.presheaf.obj (op (W i)) := fun i =>
    (Divisor.structureSheafToDivisorialSheaf hH).app (W i) (φ i)
  have hrange : ∀ (W' : Y.Opens) (x : H.divisorialSheaf.presheaf.obj (op W')),
      x ∈ Set.range (ι.app W') ↔ G.IsDivisorialSection W' x.1 := fun W' x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x.1, h⟩, rfl⟩⟩
  obtain ⟨r, hr⟩ := exists_sub_mem_range_of_isZero_rightDerived_one g hU ι hR1 W hW b
    fun i j => by
      rw [hrange]
      have := (isDivisorialSection_iff_vanishesAlong T G hGT hGE _ _).mpr (hφ i j)
      convert this using 1
      rw [map_sub, toRationalFunctionsPresheaf_app_map, toRationalFunctionsPresheaf_app_map,
        ← Divisor.coe_structureSheafToDivisorialSheaf_app hH,
        ← Divisor.coe_structureSheafToDivisorialSheaf_app hH]
      rfl
  obtain ⟨ψ, hψ⟩ := hsec U hU r.1 r.2
  refine ⟨ψ, fun i => ?_⟩
  have := (hrange _ _).mp (hr i)
  rw [← isDivisorialSection_iff_vanishesAlong T G hGT hGE]
  convert this using 1
  rw [map_sub, toRationalFunctionsPresheaf_app_map, hψ,
    ← Divisor.coe_structureSheafToDivisorialSheaf_app hH]
  rfl

/-! #### Sections of `𝒪_Y(H)` for an effective exceptional `H` -/

private theorem germ_eq_rationalFunctionsEquivFunctionField_symm {X : Scheme.{0}} [IsIntegral X]
    (U : X.Opens) (s : Γ(X, U)) (h : genericPoint X ∈ U) (Z : irreducibleComponents X)
    (hZ : componentGenericPoint X Z ∈ U) :
    (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s) Z =
      X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let D : Stacks.Chow.DenseOpen X := ⟨U, U.isOpen.dense ⟨_, h⟩⟩
  have key : (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s)
      = (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X D s) := by
    rw [RingEquiv.symm_apply_eq, ← (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 D s h]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm _)
    rw [RingEquiv.symm_apply_apply]
  rw [key]
  exact (Stacks.Chow.rationalFunctionsEquivStalks X).2 D s Z hZ

/-- On an integral scheme, a regular function, as a section of `𝒦_X`, is determined by its germ
at the generic point. -/
private theorem toRationalFunctionsPresheaf_app_eq {X : Scheme.{0}} [IsIntegral X] (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(X, U)) :
    (toRationalFunctionsPresheaf X).app (op U) s =
      (rationalFunctionsPresheaf X).map (homOfLE le_top : U ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv X).symm
          ((rationalFunctionsEquivFunctionField X).symm
            (X.presheaf.germ U (genericPoint X) h s))) := by
  funext Z
  rw [toRationalFunctionsPresheaf_app_apply]
  exact (germ_eq_rationalFunctionsEquivFunctionField_symm U s h Z.1 Z.2).symm

private theorem functionFieldMap_germ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X)
    [IsDominant g] (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U))
    (hY : genericPoint Y ∈ g ⁻¹ᵁ U) :
    functionFieldMap g (X.presheaf.germ U (genericPoint X) hU a) =
      Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hY (g.app U a) := by
  have hx : g (genericPoint Y) ∈ U := hY
  have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g (genericPoint Y)
    (X.presheaf.germ U (g (genericPoint Y)) hx a)
  have hn : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hn' : Nonempty (g ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hY⟩⟩
  rwa [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a,
    Scheme.Hom.germ_stalkMap_apply g U (genericPoint Y) hx a,
    Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := g ⁻¹ᵁ U) hY _] at h1

/-- **Sections of `𝒪_Y(H)` over `g⁻¹U`, `H` effective and exceptional, are regular functions on
`U`**, pulled back along the proper birational `g`. -/
private theorem exists_app_eq_of_isDivisorialSection {k : Type} [Field k] [PerfectField k]
    {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : IsNormalVariety k (g ≫ sX)) [IsProper g] (hg : IsBirationalMorphism g) {n : ℕ}
    (hn : topologicalKrullDim X = n) {H : Divisor Y} (hH : DivisorWithCoeffs.IsEffective H)
    (hexc : ∀ E, H.coeff E ≠ 0 → RationalMap.IsExceptional g.toRationalMap E)
    (U : X.Opens) (r : ToType ((rationalFunctionsPresheaf Y).obj (op (g ⁻¹ᵁ U))))
    (hr : H.IsDivisorialSection (g ⁻¹ᵁ U) r) :
    ∃ ψ : Γ(X, U), (toRationalFunctionsPresheaf Y).app (op (g ⁻¹ᵁ U)) (g.app U ψ) = r := by
  haveI := hg.isDominant
  by_cases hV : genericPoint Y ∈ g ⁻¹ᵁ U
  swap
  · refine ⟨0, funext fun Z => absurd ?_ hV⟩
    exact MMP.Fourfold.componentGenericPoint_eq_genericPoint Z.1 ▸ Z.2
  have hU : genericPoint X ∈ U := by
    have : g (genericPoint Y) ∈ U := hV
    rwa [map_genericPoint_of_isDominant] at this
  let t : RationalFunctions Y := fun Z =>
    r ⟨Z, (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z).symm ▸ hV⟩
  obtain ⟨φX, hφX⟩ := hg.functionFieldMap_bijective.2 (rationalFunctionsEquivFunctionField Y t)
  have hrep : r = (rationalFunctionsPresheaf Y).map (homOfLE le_top : g ⁻¹ᵁ U ⟶ ⊤).op
      ((rationalFunctionsPresheafTopEquiv Y).symm
        ((rationalFunctionsEquivFunctionField Y).symm (functionFieldMap g φX))) := by
    rw [hφX, RingEquiv.symm_apply_apply]
    rfl
  have hsec := (pushforward_divisorialSheaf_le sX hX g hY hg hn H).2.2 hH hexc U φX
  beta_reduce at hsec
  rw [← hrep] at hsec
  obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq (hsec.mp hr)
  have hsφ : X.presheaf.germ U (genericPoint X) hU s = φX := by
    rw [toRationalFunctionsPresheaf_app_eq U hU] at hs
    refine (rationalFunctionsEquivFunctionField X).symm.injective (funext fun Z => ?_)
    exact congrFun hs ⟨Z, (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z).symm ▸ hU⟩
  refine ⟨s, ?_⟩
  rw [toRationalFunctionsPresheaf_app_eq _ hV, ← functionFieldMap_germ g U hU s hV, hsφ, ← hrep]

end HasLift

/-! ### The endgame: normality of the round down from the lifting property -/

section Endgame

variable {X Y : Scheme.{0}}

/-- Units go to units, so an element mapped into the maximal ideal lies in the maximal ideal. -/
private theorem mem_maximalIdeal_of_map_mem {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) {r : R}
    (h : φ r ∈ IsLocalRing.maximalIdeal S) : r ∈ IsLocalRing.maximalIdeal R := by
  by_contra hr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
  exact (IsLocalRing.mem_maximalIdeal _).mp h (hr.map φ)

/-- If the pullback of `ψ` vanishes along `E`, then `ψ` vanishes at `g(η_E)`. -/
private theorem germ_mem_maximalIdeal_of_vanishesAlong (g : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    (hWU : W ≤ g ⁻¹ᵁ U) (E : MMP.Mori.PrimeDivisor Y) (hE : E.genericPoint ∈ W) (ψ : Γ(X, U))
    (h : VanishesAlong E W (Y.presheaf.map (homOfLE hWU).op (g.app U ψ))) :
    X.presheaf.germ U (g E.genericPoint) (hWU hE) ψ ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (g E.genericPoint)) := by
  refine mem_maximalIdeal_of_map_mem (g.stalkMap E.genericPoint).hom ?_
  have h1 := h hE
  rw [TopCat.Presheaf.germ_res_apply] at h1
  convert h1 using 1
  exact Scheme.Hom.germ_stalkMap_apply g U _ _ ψ

/-- Vanishing at a point passes to its specializations. -/
private theorem germ_mem_maximalIdeal_of_specializes {Z : Scheme.{0}} {x y : Z} (hxy : x ⤳ y)
    {U : Z.Opens} (hy : y ∈ U) (s : Γ(Z, U))
    (h : Z.presheaf.germ U x (hxy.mem_open U.isOpen hy) s ∈
      IsLocalRing.maximalIdeal (Z.presheaf.stalk x)) :
    Z.presheaf.germ U y hy s ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk y) := by
  refine mem_maximalIdeal_of_map_mem (Z.presheaf.stalkSpecializes hxy).hom ?_
  rwa [TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- For finitely many pairwise disjoint prime divisors `T R`, the union of those other than
`T P` is a closed set disjoint from `T P` containing their generic points. -/
private theorem exists_isClosed_disjoint_genericPoint_mem {ι : Type*} [Finite ι]
    (T : ι → MMP.Mori.PrimeDivisor Y)
    (hdisj : ∀ P Q, P ≠ Q → Disjoint ((T P).support : Set Y) (T Q).support) (P : ι) :
    ∃ O : Set Y, IsClosed O ∧ Disjoint ((T P).support : Set Y) O ∧
      ∀ R, R ≠ P → (T R).genericPoint ∈ O :=
  ⟨⋃ R : {R // R ≠ P}, (T R).support,
    isClosed_iUnion_of_finite fun R => (T R.1).idealSheaf.support.isClosed,
    Set.disjoint_iUnion_right.mpr fun R => hdisj P R (Ne.symm R.2),
    fun R hRP => Set.mem_iUnion.mpr ⟨⟨R, hRP⟩, MMP.Flips.primeDivisor_genericPoint_mem_support _⟩⟩

/-- The components of `D` are pairwise disjoint. -/
private theorem disjoint_support_of_hasLift (g : Y ⟶ X) (D : Divisor X)
    (T : D.support → MMP.Mori.PrimeDivisor Y)
    (hT : ∀ P, g (T P).genericPoint = P.1.genericPoint ∧ IsIso (g.stalkMap (T P).genericPoint))
    (hdisj : ∀ P Q, P ≠ Q → Disjoint ((T P).support : Set Y) (T Q).support)
    (hlift : HasLift g D.support T) (P Q : D.support) (hPQ : P ≠ Q) :
    Disjoint (P.1.support : Set X) Q.1.support := by
  classical
  refine Set.disjoint_left.mpr fun x hxP hxQ => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  set V := g ⁻¹ᵁ U
  obtain ⟨O, hO, hTO, hmemO⟩ := exists_isClosed_disjoint_genericPoint_mem T hdisj P
  let W : Bool → Y.Opens := fun b => if b then V ⊓ ⟨Oᶜ, hO.isOpen_compl⟩ else
    V ⊓ ⟨((T P).support : Set Y)ᶜ, (T P).idealSheaf.support.isClosed.isOpen_compl⟩
  have hW : ⨆ b, W b = V := by
    refine le_antisymm (iSup_le fun b => ?_) fun y hy => ?_
    · cases b <;> exact inf_le_left
    · by_cases hyT : y ∈ ((T P).support : Set Y)
      · exact Opens.mem_iSup.mpr ⟨true, hy, Set.disjoint_left.mp hTO hyT⟩
      · exact Opens.mem_iSup.mpr ⟨false, hy, hyT⟩
  let φ : ∀ b, Γ(Y, W b) := fun b => if b then 1 else 0
  have hV : ∀ R : D.support, x ∈ R.1.support → (T R).genericPoint ∈ V := fun R hxR => by
    change g (T R).genericPoint ∈ U
    rw [(hT R).1]
    exact R.1.genericPoint_mem_of_nonempty ⟨x, hxR, hxU⟩
  obtain ⟨ψ, hψ⟩ := hlift U hU Bool W hW φ fun i j R hR => by
    by_cases hij : i = j
    · subst hij
      rw [sub_self, map_zero]
      exact zero_mem _
    · exfalso
      obtain ⟨hRi, hRj⟩ := hR
      have hR' : (T R).genericPoint ∈ W true ⊓ W false := by
        cases i <;> cases j <;> simp_all
      obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := hR'
      by_cases hRP : R = P
      · subst hRP
        exact h2 (MMP.Flips.primeDivisor_genericPoint_mem_support (T R))
      · exact h1 (hmemO R hRP)
  -- `ψ - 1` vanishes along `P` and `ψ` vanishes along `Q`
  have hP1 : (T P).genericPoint ∈ W true :=
    ⟨hV P hxP, Set.disjoint_left.mp hTO (MMP.Flips.primeDivisor_genericPoint_mem_support (T P))⟩
  have hQ0 : (T Q).genericPoint ∈ W false :=
    ⟨hV Q hxQ, Set.disjoint_right.mp (hdisj P Q hPQ)
      (MMP.Flips.primeDivisor_genericPoint_mem_support (T Q))⟩
  have hWU : ∀ b, W b ≤ V := fun b => hW ▸ le_iSup W b
  have h1 : VanishesAlong (T P) (W true)
      (Y.presheaf.map (homOfLE (hWU true)).op (g.app U (ψ - 1))) := by
    simpa [φ, map_sub, map_one] using hψ true P
  have h0 : VanishesAlong (T Q) (W false)
      (Y.presheaf.map (homOfLE (hWU false)).op (g.app U ψ)) := by
    simpa [φ] using hψ false Q
  have m1 := germ_mem_maximalIdeal_of_vanishesAlong g (hWU true) (T P) hP1 _ h1
  have m0 := germ_mem_maximalIdeal_of_vanishesAlong g (hWU false) (T Q) hQ0 _ h0
  have hsp : ∀ R : D.support, x ∈ R.1.support → g (T R).genericPoint ⤳ x := fun R hxR => by
    rw [(hT R).1, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at *
    exact specializes_iff_mem_closure.mpr hxR
  have n1 := germ_mem_maximalIdeal_of_specializes (hsp P hxP) hxU _ m1
  have n0 := germ_mem_maximalIdeal_of_specializes (hsp Q hxQ) hxU _ m0
  have := sub_mem n0 n1
  rw [← map_sub, sub_sub_cancel, map_one] at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr this)

/-- Integrality over a quotient gives integrality over the ring. -/
private theorem isIntegralElem_comp_of_surjective {R A L : Type*} [CommRing R] [CommRing A]
    [Nontrivial A] [CommRing L] {q : R →+* A} (hq : Function.Surjective q) {f : A →+* L} {a : L}
    (h : f.IsIntegralElem a) : (f.comp q).IsIntegralElem a := by
  obtain ⟨p, hp, hpa⟩ := h
  obtain ⟨p', hp'⟩ := Polynomial.map_surjective q hq p
  obtain ⟨p'', hmap, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts p |>.mpr ⟨p', hp'⟩) hp
  refine ⟨p'', hmon, ?_⟩
  rw [← Polynomial.eval₂_map, hmap, hpa]

/-- For a closed immersion `ι : Z ⟶ Y` of a normal integral scheme, the image of `𝒪_{Y,ι z}` in
the residue field of `Y` at the image of the generic point of `Z` is integrally closed: it is
`𝒪_{Z,z}` inside its fraction field `k(Z)`. -/
private theorem exists_residue_eq_of_isIntegralElem_of_isClosedImmersion {Z : Scheme.{0}}
    (ι : Z ⟶ Y) [IsClosedImmersion ι] [IsIntegral Z] [IsNormal Z]
    (z : Z) (a : IsLocalRing.ResidueField (Y.presheaf.stalk (ι (genericPoint Z))))
    (ha : ((IsLocalRing.residue _).comp (Y.presheaf.stalkSpecializes
      ((genericPoint_specializes z).map ι.continuous)).hom).IsIntegralElem a) :
    ∃ s, (IsLocalRing.residue _).comp (Y.presheaf.stalkSpecializes
      ((genericPoint_specializes z).map ι.continuous)).hom s = a := by
  set τ := (ι.stalkMap (genericPoint Z)).hom with hτ
  have hsurj : Function.Surjective τ := ι.stalkMap_surjective _
  have hker : RingHom.ker τ = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.ker_eq_maximalIdeal τ hsurj
  let e : IsLocalRing.ResidueField (Y.presheaf.stalk (ι (genericPoint Z))) ≃+* Z.functionField :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ s, e (IsLocalRing.residue _ s) = τ s := fun s => rfl
  have hsq : ∀ s, τ (Y.presheaf.stalkSpecializes ((genericPoint_specializes z).map ι.continuous)
      s) = algebraMap (Z.presheaf.stalk z) Z.functionField (ι.stalkMap z s) := by
    intro s
    exact congrArg (fun φ => φ.hom s) (Scheme.Hom.stalkSpecializes_stalkMap ι (genericPoint Z) z
      (genericPoint_specializes z))
  have hcomp : (e.toRingHom.comp ((IsLocalRing.residue _).comp (Y.presheaf.stalkSpecializes
      ((genericPoint_specializes z).map ι.continuous)).hom)) =
      (algebraMap (Z.presheaf.stalk z) Z.functionField).comp (ι.stalkMap z).hom := by
    ext s
    exact (he _).trans (hsq s)
  have h1 : (e.toRingHom.comp ((IsLocalRing.residue _).comp (Y.presheaf.stalkSpecializes
      ((genericPoint_specializes z).map ι.continuous)).hom)).IsIntegralElem (e a) :=
    RingHom.IsIntegralElem.map ha e.toRingHom
  rw [hcomp] at h1
  have h2 : _root_.IsIntegral (Z.presheaf.stalk z) (e a) := h1.of_comp
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  obtain ⟨s, rfl⟩ := ι.stalkMap_surjective z t
  refine ⟨s, e.injective ?_⟩
  rw [← ht]
  exact (he _).trans (hsq s)

/-- **Normality of a prime divisor, at the stalks.** If the prime divisor `E` is normal, then
for every `y ∈ E` the image of `𝒪_{Y,y}` in the residue field `κ(η_E)` is integrally closed in
`κ(η_E)`. -/
private theorem exists_residue_eq_of_isIntegralElem (E : MMP.Mori.PrimeDivisor Y)
    [IsNormal E.idealSheaf.subscheme] {y : Y} (hy : y ∈ (E.support : Set Y))
    (hsp : E.genericPoint ⤳ y) (a : IsLocalRing.ResidueField (Y.presheaf.stalk E.genericPoint))
    (ha : ((IsLocalRing.residue _).comp (Y.presheaf.stalkSpecializes hsp).hom).IsIntegralElem a) :
    ∃ s, IsLocalRing.residue _ (Y.presheaf.stalkSpecializes hsp s) = a := by
  have := E.integral
  set ι := E.idealSheaf.subschemeι
  have hrange : Set.range ι = (E.support : Set Y) := Scheme.IdealSheafData.range_subschemeι _
  have hη : ι (genericPoint E.idealSheaf.subscheme) = E.genericPoint := by
    obtain ⟨w, hw⟩ : E.genericPoint ∈ Set.range ι := by
      rw [hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have h1 : ι (genericPoint E.idealSheaf.subscheme) ⤳ E.genericPoint :=
      hw ▸ (genericPoint_specializes w).map ι.continuous
    have h2 : E.genericPoint ⤳ ι (genericPoint E.idealSheaf.subscheme) := by
      have : ι (genericPoint E.idealSheaf.subscheme) ∈ (E.support : Set Y) :=
        hrange ▸ Set.mem_range_self _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    exact (h1.antisymm h2).eq
  have key : ∀ (e y : Y) (he : ι (genericPoint E.idealSheaf.subscheme) = e)
      (hy : y ∈ Set.range ι) (hsp : e ⤳ y) (a : IsLocalRing.ResidueField (Y.presheaf.stalk e)),
      ((IsLocalRing.residue _).comp (Y.presheaf.stalkSpecializes hsp).hom).IsIntegralElem a →
      ∃ s, IsLocalRing.residue _ (Y.presheaf.stalkSpecializes hsp s) = a := by
    rintro e y rfl ⟨z, rfl⟩ hsp a ha
    exact exists_residue_eq_of_isIntegralElem_of_isClosedImmersion ι z a ha
  exact key _ y hη (hrange ▸ hy) hsp a ha

/-- If `g η` is the generic point of `P`, the kernel of `𝒪(U) → κ(η)` is the ideal of `P`. -/
private theorem ker_residue_comp_stalkMap_germ (g : Y ⟶ X) (P : MMP.Mori.PrimeDivisor X) {η : Y}
    (hgη : g η = P.genericPoint) (U : X.affineOpens) (hηU : g η ∈ U.1) :
    RingHom.ker ((IsLocalRing.residue (Y.presheaf.stalk η)).comp
      ((g.stalkMap η).hom.comp (X.presheaf.germ U.1 (g η) hηU).hom)) = P.idealSheaf.ideal U := by
  ext ψ
  rw [RingHom.mem_ker, MMP.Mori.PrimeDivisor.mem_ideal_idealSheaf_iff]
  simp only [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h _ hb
    have hm := mem_maximalIdeal_of_map_mem _ h
    rw [← hgη] at hb
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ((Scheme.mem_basicOpen X ψ _ hηU).mp hb)
  · intro h
    have hnb := h (hgη ▸ hηU)
    rw [← hgη] at hnb
    have hm : X.presheaf.germ U.1 (g η) hηU ψ ∈ IsLocalRing.maximalIdeal _ := fun hu =>
      hnb ((Scheme.mem_basicOpen X ψ _ hηU).mpr hu)
    by_contra hc
    exact hm (isUnit_of_map_unit _ _ (Classical.byContradiction hc))

/-- **The ring of a component on an affine chart is an integrally closed domain.** Let `U` be
an affine open meeting the component `P` of `D` and `𝔭 ⊆ 𝒪(U)` the ideal of `P`. Then `𝒪(U)/𝔭`
embeds in the residue field `κ` of `Y` at the generic point of `T_P`. An element `a ∈ κ`
integral over `𝒪(U)/𝔭` is integral over the image of every `𝒪_{Y,y}`, `y ∈ T_P ∩ g⁻¹U`, which is
integrally closed since `T_P` is normal, so `a` lifts locally to regular functions on `Y`; the
lifting property glues these lifts to a regular function on `U` with residue `a`. -/
private theorem isIntegrallyClosed_quotient_of_hasLift
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (g : Y ⟶ X) (D : Divisor X)
    (T : D.support → MMP.Mori.PrimeDivisor Y)
    (hT : ∀ P, g (T P).genericPoint = P.1.genericPoint ∧ IsIso (g.stalkMap (T P).genericPoint))
    (hdisj : ∀ P Q, P ≠ Q → Disjoint ((T P).support : Set Y) (T Q).support)
    (hnorm : ∀ P, IsNormal (T P).idealSheaf.subscheme)
    (hlift : HasLift g D.support T) (P : D.support) (U : X.affineOpens)
    (hU : P.1.genericPoint ∈ U.1) :
    ∃ _ : IsDomain (Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U),
      IsIntegrallyClosed (Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U) := by
  classical
  set η := (T P).genericPoint with hη_def
  have hgη : g η = P.1.genericPoint := (hT P).1
  have hηU : g η ∈ U.1 := hgη ▸ hU
  set V := g ⁻¹ᵁ U.1
  have hηV : η ∈ V := hηU
  let ρ : Γ(X, U.1) →+* IsLocalRing.ResidueField (Y.presheaf.stalk η) :=
    (IsLocalRing.residue _).comp ((g.stalkMap η).hom.comp (X.presheaf.germ U.1 (g η) hηU).hom)
  have hker : RingHom.ker ρ = P.1.idealSheaf.ideal U :=
    ker_residue_comp_stalkMap_germ g P.1 hgη U hηU
  let ρ' : Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U →+* IsLocalRing.ResidueField
      (Y.presheaf.stalk η) :=
    Ideal.Quotient.lift _ ρ fun a ha => by rwa [← RingHom.mem_ker, hker]
  have hρ' : ∀ ψ, ρ' (Ideal.Quotient.mk _ ψ) = ρ ψ := fun ψ => rfl
  have hinj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨ψ, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hker]
    exact ha
  haveI : IsDomain (Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U) := hinj.isDomain ρ'
  refine ⟨inferInstance, ?_⟩
  rw [isIntegrallyClosed_iff (FractionRing (Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U))]
  intro x hx
  let j : FractionRing (Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U) →+*
      IsLocalRing.ResidueField (Y.presheaf.stalk η) := IsFractionRing.lift hinj
  have hj : ∀ b, j (algebraMap _ _ b) = ρ' b := IsFractionRing.lift_algebraMap hinj
  have ha : ρ.IsIntegralElem (j x) := by
    have h1 : (j.comp (algebraMap _
        (FractionRing (Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U)))).IsIntegralElem (j x) :=
      RingHom.IsIntegralElem.map hx j
    have h2 : j.comp (algebraMap _ (FractionRing (Γ(X, U.1) ⧸ P.1.idealSheaf.ideal U))) = ρ' :=
      RingHom.ext hj
    rw [h2] at h1
    have h3 : ρ = ρ'.comp (Ideal.Quotient.mk _) := RingHom.ext fun ψ => (hρ' ψ).symm
    rw [h3]
    exact isIntegralElem_comp_of_surjective Ideal.Quotient.mk_surjective h1
  obtain ⟨O, hO, hTO, hmemO⟩ := exists_isClosed_disjoint_genericPoint_mem T hdisj P
  have hspec : ∀ y ∈ ((T P).support : Set Y), η ⤳ y := fun y hy => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
    exact specializes_iff_mem_closure.mpr hy
  -- local lifts of `j x` around each point of `T_P ∩ g⁻¹U`
  have hlocal : ∀ y : {y : Y // y ∈ ((T P).support : Set Y) ∧ y ∈ V}, ∃ (W : Y.Opens)
      (φ : Γ(Y, W)), y.1 ∈ W ∧ W ≤ V ∧ Disjoint (W : Set Y) O ∧ ∀ hηW : η ∈ W,
        IsLocalRing.residue _ (Y.presheaf.germ W η hηW φ) = j x := by
    rintro ⟨y, hyT, hyV⟩
    have hsp := hspec y hyT
    haveI := hnorm P
    have hcomp : ρ = ((IsLocalRing.residue _).comp (Y.presheaf.stalkSpecializes hsp).hom).comp
        ((Y.presheaf.germ V y hyV).hom.comp (g.app U.1).hom) := by
      ext ψ
      simp only [ρ, RingHom.comp_apply]
      congr 1
      exact (Scheme.Hom.germ_stalkMap_apply g U.1 η hηU ψ).trans
        (TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hyV hsp _).symm
    rw [hcomp] at ha
    obtain ⟨s, hs⟩ := exists_residue_eq_of_isIntegralElem (T P) hyT hsp (j x) ha.of_comp
    obtain ⟨W₀, hyW₀, t, ht⟩ := TopCat.Presheaf.germ_exist Y.presheaf s
    let W : Y.Opens := W₀ ⊓ V ⊓ ⟨Oᶜ, hO.isOpen_compl⟩
    have hyW : y ∈ W := ⟨⟨hyW₀, hyV⟩, Set.disjoint_left.mp hTO hyT⟩
    refine ⟨W, Y.presheaf.map (homOfLE (inf_le_left.trans inf_le_left : W ≤ W₀)).op t,
      hyW, inf_le_left.trans inf_le_right,
      Set.disjoint_left.mpr fun z hz hzO => hz.2 hzO, fun hηW => ?_⟩
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hyW hsp,
      TopCat.Presheaf.germ_res_apply, ht]
    exact hs
  choose Wl φl hyWl hWlV hWlO hφl using hlocal
  let I := Option {y : Y // y ∈ ((T P).support : Set Y) ∧ y ∈ V}
  let W : I → Y.Opens := fun i => match i with
    | none => V ⊓ ⟨((T P).support : Set Y)ᶜ, (T P).idealSheaf.support.isClosed.isOpen_compl⟩
    | some y => Wl y
  let φ : ∀ i, Γ(Y, W i) := fun i => match i with
    | none => 0
    | some y => φl y
  have hW : ⨆ i, W i = V := by
    refine le_antisymm (iSup_le fun i => ?_) fun y hy => ?_
    · cases i with
      | none => exact inf_le_left
      | some y => exact hWlV y
    · by_cases hyT : y ∈ ((T P).support : Set Y)
      · exact Opens.mem_iSup.mpr ⟨some ⟨y, hyT, hy⟩, hyWl _⟩
      · exact Opens.mem_iSup.mpr ⟨none, hy, hyT⟩
  obtain ⟨ψ, hψ⟩ := hlift U.1 U.2 I W hW φ fun i k R hR => by
    rw [map_sub, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    by_cases hRP : R = P
    · obtain rfl := hRP
      rcases i with _ | y
      · exact absurd (MMP.Flips.primeDivisor_genericPoint_mem_support (T R)) hR.1.2
      rcases k with _ | y'
      · exact absurd (MMP.Flips.primeDivisor_genericPoint_mem_support (T R)) hR.2.2
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      exact sub_eq_zero.mpr ((hφl y hR.1).trans (hφl y' hR.2).symm)
    · rcases i with _ | y
      · rcases k with _ | y'
        · change _ - _ ∈ _
          simp only [φ, map_zero, sub_self]
          exact zero_mem _
        · exact absurd (hmemO R hRP) (Set.disjoint_left.mp (hWlO y') hR.2)
      · exact absurd (hmemO R hRP) (Set.disjoint_left.mp (hWlO y) hR.1)
  let y₀ : {y : Y // y ∈ ((T P).support : Set Y) ∧ y ∈ V} :=
    ⟨η, MMP.Flips.primeDivisor_genericPoint_mem_support _, hηV⟩
  have hv := hψ (some y₀) P (hyWl y₀)
  rw [map_sub, TopCat.Presheaf.germ_res_apply, ← IsLocalRing.residue_eq_zero_iff, map_sub,
    sub_eq_zero] at hv
  have e := hφl y₀ (hyWl y₀)
  refine ⟨Ideal.Quotient.mk _ ψ, j.injective ?_⟩
  rw [hj, hρ', ← e]
  refine Eq.trans ?_ hv
  simp only [ρ, RingHom.comp_apply]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply g U.1 η hηU ψ

/-- Each component of `D` is normal. -/
private theorem isNormal_subscheme_of_hasLift
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (g : Y ⟶ X) (D : Divisor X)
    (T : D.support → MMP.Mori.PrimeDivisor Y)
    (hT : ∀ P, g (T P).genericPoint = P.1.genericPoint ∧ IsIso (g.stalkMap (T P).genericPoint))
    (hdisj : ∀ P Q, P ≠ Q → Disjoint ((T P).support : Set Y) (T Q).support)
    (hnorm : ∀ P, IsNormal (T P).idealSheaf.subscheme)
    (hlift : HasLift g D.support T) (P : D.support) :
    IsNormal P.1.idealSheaf.subscheme := by
  let I := {U : X.affineOpens // P.1.genericPoint ∈ U.1}
  apply ((isNormal_tfae P.1.idealSheaf.subscheme).out 3 1).mp
  refine ⟨I, fun U => ⟨P.1.idealSheaf.subschemeι ⁻¹ᵁ U.1.1, U.1.2.preimage _⟩, ?_, fun U => ?_⟩
  · refine IsOpenCover.mk (eq_top_iff.mpr fun z _ => ?_)
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (P.1.idealSheaf.subschemeι z)) isOpen_univ
    have hz : P.1.idealSheaf.subschemeι z ∈ (P.1.support : Set X) := by
      rw [AlgebraicGeometry.PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self z
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, P.1.genericPoint_mem_of_nonempty ⟨_, hz, hzU⟩⟩, hzU⟩
  · obtain ⟨_, _⟩ := isIntegrallyClosed_quotient_of_hasLift g D T hT hdisj hnorm hlift P U.1 U.2
    exact IsNormalRing.congr (P.1.idealSheaf.subschemeObjIso U.1).commRingCatIsoToRingEquiv.symm
      (IsNormalRing.of_isIntegrallyClosed _)

/-- Two closed subsets agreeing on an affine open `U` have the same vanishing ideal on `U`. -/
private theorem ideal_vanishingIdeal_congr {Z Z' : Closeds X} (U : X.affineOpens)
    (h : (Z : Set X) ∩ U = (Z' : Set X) ∩ U) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal U =
      (Scheme.IdealSheafData.vanishingIdeal Z').ideal U := by
  have e : ∀ W : Closeds X, (Scheme.IdealSheafData.vanishingIdeal W).ideal U =
      PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (W : Set X)) := fun W => rfl
  rw [e, e]
  congr 1
  ext x
  have hx : U.2.fromSpec x ∈ (U : Set X) := U.2.range_fromSpec ▸ Set.mem_range_self x
  exact ⟨fun h1 => ((Set.ext_iff.mp h _).mp ⟨h1, hx⟩).1,
    fun h1 => ((Set.ext_iff.mp h _).mpr ⟨h1, hx⟩).1⟩

/-- A divisor whose components are pairwise disjoint and normal has normal support: near a
component `E`, the reduced subschemes `E` and `Supp D` have the same ideal. -/
private theorem isNormal_suppScheme_of_isNormal_subscheme (D : Divisor X)
    (hdisj : ∀ P ∈ D.support, ∀ Q ∈ D.support, P ≠ Q →
      Disjoint (P.support : Set X) Q.support)
    (hnorm : ∀ P ∈ D.support, IsNormal P.idealSheaf.subscheme) :
    IsNormal D.suppScheme := by
  classical
  let C : MMP.Mori.PrimeDivisor X → Set X := fun E => ⋃ P ∈ D.support.filter (· ≠ E), P.support
  have hC : ∀ E, IsClosed (C E) := fun E =>
    isClosed_biUnion_finset fun P _ => P.idealSheaf.support.isClosed
  have hEC : ∀ E ∈ D.support, Disjoint (E.support : Set X) (C E) := by
    intro E hE
    simp only [C, Set.disjoint_iUnion_right, Finset.mem_filter]
    exact fun P ⟨hP, hPE⟩ => hdisj E hE P hP (Ne.symm hPE)
  have hideal : ∀ E ∈ D.support, ∀ U : X.affineOpens, Disjoint (U : Set X) (C E) →
      D.suppIdeal.ideal U = E.idealSheaf.ideal U := by
    intro E hE U hU
    have := E.integral
    rw [AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
    refine ideal_vanishingIdeal_congr U ?_
    rw [DivisorWithCoeffs.coe_supp]
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨?_, hxU⟩
      simp only [Set.mem_iUnion] at hx
      obtain ⟨P, hP, hxP⟩ := hx
      by_contra hxE
      have hPE : P ≠ E := by rintro rfl; exact hxE hxP
      exact Set.disjoint_left.mp hU hxU (by
        simp only [C, Set.mem_iUnion, Finset.mem_filter]
        exact ⟨P, ⟨hP, hPE⟩, hxP⟩)
    · rintro ⟨hx, hxU⟩
      refine ⟨?_, hxU⟩
      simp only [Set.mem_iUnion]
      exact ⟨E, hE, hx⟩
  let I := {q : MMP.Mori.PrimeDivisor X × X.affineOpens //
    q.1 ∈ D.support ∧ Disjoint (q.2 : Set X) (C q.1)}
  apply ((isNormal_tfae D.suppScheme).out 3 1).mp
  refine ⟨I, fun q => ⟨D.suppIdeal.subschemeι ⁻¹ᵁ q.1.2.1, q.1.2.2.preimage _⟩, ?_, fun q => ?_⟩
  · refine IsOpenCover.mk (eq_top_iff.mpr fun y _ => ?_)
    have hy : D.suppIdeal.subschemeι y ∈ (D.supp : Set X) := by
      rw [← DivisorWithCoeffs.coe_support_suppIdeal, ← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self y
    rw [DivisorWithCoeffs.coe_supp] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨E, hE, hyE⟩ := hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUC⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.disjoint_left.mp (hEC E hE) hyE) (hC E).isOpen_compl
    exact Opens.mem_iSup.mpr
      ⟨⟨(E, ⟨U, hU⟩), hE, Set.subset_compl_iff_disjoint_right.mp hUC⟩, hyU⟩
  · haveI := hnorm q.1.1 q.2.1
    have hE := ((isNormal_tfae q.1.1.idealSheaf.subscheme).out 1 2).mp ‹_›
    let e1 := (q.1.1.idealSheaf.subschemeObjIso q.1.2).commRingCatIsoToRingEquiv
    let e2 := Ideal.quotEquivOfEq (hideal q.1.1 q.2.1 q.1.2 q.2.2).symm
    let e3 := (D.suppIdeal.subschemeObjIso q.1.2).commRingCatIsoToRingEquiv.symm
    exact IsNormalRing.congr (e1.trans (e2.trans e3))
      (hE ⟨_, q.1.2.2.preimage q.1.1.idealSheaf.subschemeι⟩)

private theorem isNormal_suppScheme_of_hasLift
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (g : Y ⟶ X) (D : Divisor X)
    (T : D.support → MMP.Mori.PrimeDivisor Y)
    (hT : ∀ P, g (T P).genericPoint = P.1.genericPoint ∧ IsIso (g.stalkMap (T P).genericPoint))
    (hdisj : ∀ P Q, P ≠ Q → Disjoint ((T P).support : Set Y) (T Q).support)
    (hnorm : ∀ P, IsNormal (T P).idealSheaf.subscheme)
    (hlift : HasLift g D.support T) :
    IsNormal D.suppScheme :=
  isNormal_suppScheme_of_isNormal_subscheme D
    (fun P hP Q hQ hPQ => disjoint_support_of_hasLift g D T hT hdisj hlift ⟨P, hP⟩ ⟨Q, hQ⟩
      fun h => hPQ (congrArg Subtype.val h))
    fun P hP => isNormal_subscheme_of_hasLift g D T hT hdisj hnorm hlift ⟨P, hP⟩

end Endgame

/-! ### The resolution and the vanishing -/

/-- Every `ℚ`-divisor has a positive integral multiple with integral coefficients. -/
private theorem exists_pos_smul_mem_range_toQDivisor {Y : Scheme.{0}} (B : QDivisor Y) :
    ∃ m : ℕ, 0 < m ∧ ∃ B' : Divisor Y, Divisor.toQDivisor B' = ((m : ℤ) • B) := by
  refine ⟨∏ E ∈ B.support, (B E).den, Finset.prod_pos fun E _ => (B E).den_pos, ?_⟩
  have := (QDivisor.mem_range_toQDivisor_iff (((∏ E ∈ B.support, (B E).den : ℕ) : ℤ) • B)).mpr
    fun E => ?_
  · exact this
  by_cases hE : E ∈ B.support
  · obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun E => (B E).den) hE
    refine ⟨t * (B E).num, ?_⟩
    change (((∏ E ∈ B.support, (B E).den : ℕ) : ℤ) • B) E = _
    rw [Finsupp.smul_apply, ht, zsmul_eq_mul]
    push_cast
    rw [mul_comm ((B E).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  · refine ⟨0, ?_⟩
    change (((∏ E ∈ B.support, (B E).den : ℕ) : ℤ) • B) E = _
    rw [Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hE, smul_zero, Int.cast_zero]

/-- **Kawamata–Viehweg vanishing for `-⌊Θ⌋`.** On a smooth `Y` proper birational over `X`, if
`m(K_Y + Θ)` is a divisor of degree zero on every curve contracted by `f` and the fractional part
`{Θ}` is snc, then `R¹f_* 𝒪_Y(-⌊Θ⌋) = 0`: write `-⌊Θ⌋ = K_Y + A` with `A - {Θ} = -(K_Y + Θ)`,
which is numerically trivial over `X`. -/
private theorem isZero_rightDerived_one_neg_roundDown {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k sX] [MMP.Mori.IsVariety k sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (f : Y ⟶ X) [IsProper f] (hfs : f ≫ sX = sY)
    (hf : IsBirationalMorphism f) {n : ℕ} (KY : Divisor Y) (hKY : KY.IsCanonicalDivisor sY n)
    (Θ : QDivisor Y) (hsnc : (Θ - Divisor.toQDivisor Θ.roundDown).IsSNC sY)
    {m : ℕ} (hm : 0 < m) (L : Divisor Y)
    (hL : Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor KY + Θ))
    (hLC : ∀ C : ProperCurve sY, C.IsContractedBy f →
      L.degreeOn k sY C.ι C.dim_le
        (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm L) = 0) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (-Θ.roundDown).divisorialSheaf) := by
  classical
  set A : Divisor Y := -Θ.roundDown - KY with hA
  set B : QDivisor Y := Θ - Divisor.toQDivisor Θ.roundDown with hB
  set M : QDivisor Y := Divisor.toQDivisor A - B with hM
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  have hMeq : Divisor.toQDivisor (-L) = (m : ℤ) • M := by
    rw [map_neg, hL, hM, hA, hB, map_sub, map_neg,
      show -Divisor.toQDivisor Θ.roundDown - Divisor.toQDivisor KY -
        (Θ - Divisor.toQDivisor Θ.roundDown) = -(Divisor.toQDivisor KY + Θ) by abel, smul_neg]
  have hMq : M.IsQCartier := ⟨m, by exact_mod_cast hm.ne', -L, hMeq, (hcart L).neg⟩
  let φ : ProperCurve sY → Divisor Y →+ ℤ := fun C =>
    { toFun := fun D => D.degreeOn k sY C.ι C.dim_le (hcart D)
      map_zero' := Divisor.degreeOn_zero' k sY C.ι C.dim_le
      map_add' := fun D D' => Divisor.degreeOn_add k sY C.ι C.dim_le D D' _ _ }
  have hφ : ∀ C D, D.degreeOn k sY C.ι C.dim_le (hcart D) = φ C D := fun _ _ => rfl
  have hMC : ∀ C : ProperCurve sY, C.IsContractedBy f →
      M.intersectionNumber k sY C.ι C.dim_le hMq = 0 := by
    intro C hC
    rw [QDivisor.intersectionNumber_eq_of_smul k sY C.ι C.dim_le M hMq hm (-L) (hcart _) hMeq,
      hφ, map_neg, ← hφ, hLC C hC]
    simp
  have hMnef : M.IsRelativelyNef sY f :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sY hMq fun C hC =>
      (hMC C hC).ge
  have hB0 : ∀ E, 0 ≤ B E := fun E => by
    change 0 ≤ B.coeff E
    rw [hB, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_roundDown, sub_nonneg]
    exact Int.floor_le _
  have hB1 : ∀ E, B E < 1 := fun E => by
    change B.coeff E < 1
    rw [hB, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_roundDown, sub_lt_iff_lt_add']
    exact Int.lt_floor_add_one _
  obtain ⟨N, hN, B', hB'⟩ := exists_pos_smul_mem_range_toQDivisor B
  have hB'E : ∀ E, (B' E : ℚ) = N * B E := fun E => by
    have := congrArg (fun D : QDivisor Y => D.coeff E) hB'
    simp only [Divisor.coeff_toQDivisor] at this
    refine this.trans ?_
    change (((N : ℤ) • B) E) = _
    rw [Finsupp.smul_apply, zsmul_eq_mul]
    push_cast
    rfl
  have hsupp : B'.support ⊆ B.support := fun E hE => by
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro h0
    have := hB'E E
    rw [h0, mul_zero] at this
    exact hE (by exact_mod_cast this)
  have hAMB : ∀ C : ProperCurve sY, C.IsContractedBy f →
      (A.degreeOn k sY C.ι C.dim_le (hcart A) : ℚ) =
        M.intersectionNumber k sY C.ι C.dim_le hMnef.1 +
          ∑ E ∈ B.support, B E * (Divisor.degreeOn k sY C.ι C.dim_le
            (Finsupp.single E 1)
            (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E) : ℚ) := by
    intro C hC
    have hD : Divisor.toQDivisor ((N : ℤ) • A - B') = (N : ℤ) • M := by
      rw [map_sub, map_zsmul, hB', hM, ← smul_sub]
    have h0 := hMC C hC
    rw [QDivisor.intersectionNumber_eq_of_smul k sY C.ι C.dim_le M hMq hN _ (hcart _) hD,
      div_eq_zero_iff, hφ] at h0
    have hB'sum : φ C B' = ∑ E ∈ B.support, B' E * φ C (Finsupp.single E 1) := by
      conv_lhs => rw [← Finsupp.sum_single B',
        Finsupp.sum_of_support_subset B' hsupp _ (fun _ _ => Finsupp.single_zero _)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul]
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    rcases h0 with h0 | h0
    · rw [map_sub, map_zsmul, hB'sum, smul_eq_mul] at h0
      push_cast at h0
      have h1 : (N : ℚ) * (φ C A : ℚ) =
          ∑ E ∈ B.support, (B' E : ℚ) * (φ C (Finsupp.single E 1) : ℚ) := by linarith
      simp only [hB'E] at h1
      rw [hMC C hC, zero_add, hφ]
      simp only [hφ]
      have h2 : ∑ E ∈ B.support, (N : ℚ) * B E * (φ C (Finsupp.single E 1) : ℚ) =
          N * ∑ E ∈ B.support, B E * (φ C (Finsupp.single E 1) : ℚ) := by
        simp only [Finset.mul_sum, mul_assoc]
      rw [h2] at h1
      exact mul_left_cancel₀ hN' h1
    · exact absurd h0 hN'
  have key := isZero_rightDerived_pushforward_canonical_add_of_isBirationalMorphism sX sY hsm f
    hfs hf A M hMnef B hsnc hB0 hB1 hAMB KY hKY (i := 1) one_pos
  rwa [show KY + A = -Θ.roundDown by rw [hA]; abel] at key

/-- A prime divisor of `Y` whose generic point maps to the generic point of a prime divisor of
`X` is not `f`-exceptional: the closure of its image has codimension one. -/
private theorem not_isExceptional_of_map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X ↘ Limits.terminal Scheme)]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    {E : MMP.Mori.PrimeDivisor Y} {P : MMP.Mori.PrimeDivisor X}
    (heq : f E.genericPoint = P.genericPoint) :
    ¬ RationalMap.IsExceptional f.toRationalMap E := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  intro h
  have hsub : (IrreducibleCloseds.closureSingleton (f E.genericPoint) : Set X) ⊆
      (Closeds.closure (f '' (E.idealSheaf.support : Set Y)) : Set X) := by
    rw [IrreducibleCloseds.coe_closureSingleton, Closeds.coe_closure]
    refine closure_mono (Set.singleton_subset_iff.mpr ⟨E.genericPoint, ?_, rfl⟩)
    change E.genericPoint ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hle := le_closedsCodimension_iff.mp h _ hsub
  rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton (f E.genericPoint) =
    (irreducibleSetEquivPoints (α := X)).symm (f E.genericPoint) from rfl,
    Order.coheight_orderIso, heq, P.coheight_genericPoint] at hle
  exact absurd hle (by decide)

/-- **The resolution.** A log resolution of the plt dlt pair `(X, Δ)` on which the strict
transforms of the components of `⌊Δ⌋` are normal and pairwise disjoint and have the lifting
property. -/
private theorem exists_hasLift {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (h : IsDltPair sX n K Δ) (hplt : IsPltPair sX n K Δ) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (g : Y ⟶ X) (T : Δ.roundDown.support → MMP.Mori.PrimeDivisor Y),
      (∀ P, g (T P).genericPoint = P.1.genericPoint ∧ IsIso (g.stalkMap (T P).genericPoint)) ∧
      (∀ P Q, P ≠ Q → Disjoint ((T P).support : Set Y) (T Q).support) ∧
      (∀ P, IsNormal (T P).idealSheaf.subscheme) ∧
      HasLift g Δ.roundDown.support T := by
  classical
  set S := Δ.roundDown.support
  have hX : IsNormalVariety k sX := h.1.1
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hK : K.IsCanonicalDivisor sX n := h.1.2.1
  have hdimX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  -- the coefficients of `Δ`
  have hS1 : ∀ P ∈ S, Δ.coeff P = 1 := by
    intro P hP
    have h0 : ⌊Δ.coeff P⌋ ≠ 0 := by
      rw [← DivisorWithCoeffs.coeff_roundDown]; exact Finsupp.mem_support_iff.mp hP
    obtain ⟨h1, h2⟩ := h.2.1 P
    by_contra hne
    exact h0 (Int.floor_eq_zero_iff.mpr ⟨h1, lt_of_le_of_ne h2 hne⟩)
  have hS0 : ∀ P ∉ S, ⌊Δ.coeff P⌋ = 0 := fun P hP => by
    rw [← DivisorWithCoeffs.coeff_roundDown]; exact Finsupp.notMem_support_iff.mp hP
  have hSΔ : ∀ P ∈ S, P ∈ Δ.support := fun P hP =>
    Finsupp.mem_support_iff.mpr ((hS1 P hP).trans_ne one_ne_zero)
  -- the log resolution
  obtain ⟨Y, f, hf, hsmT, hdisjT⟩ :=
    exists_isLogResolution_disjoint_inverseTransformPrimeDivisor sX Δ h.isPair
  obtain ⟨hY, hdimY, -⟩ := hf.toIsSmoothResolution.isNormalVariety hX
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : MMP.Mori.IsVariety k (f ≫ sX) := hY.1
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsProper f := hf.isProper
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  set hfb := hf.isBirationalMorphism
  haveI : IsDominant f := hfb.isDominant
  have hdimY' : topologicalKrullDim Y = n := hdimY.trans hdimX
  -- a rational top form `σ` on `X` and its pullback `σ'`
  have hbij := hfb.functionFieldMap_bijective
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra f
  haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
  obtain ⟨σ, hσ⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective sX f hbij
    (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimX)
  let σ' : RationalTopForms (f ≫ sX) n := topFormsMap k X.functionField Y.functionField n σ
  have hσ0 : (σ : RationalTopForms sX n) ≠ 0 := hσ.ne_zero
  have hσ'0 : σ' ≠ 0 := hσ.2.2
  have hK'K := MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hX hdimX hσ0 hK
  set KY : Divisor Y := topFormDivisor (f ≫ sX) σ'
  have hKY : KY.IsCanonicalDivisor (f ≫ sX) n :=
    MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hY hdimY' hσ'0
  have hpull := MMP.ProgramBaseChange.pullbackRationalPluriForms_toPluriForms_eq sX f hdimX hdimY'
    σ σ' rfl hσ'0
  -- the crepant boundary `Θ = (1/m) f^*L - K_Y`, `L = m (K_X + Δ)`
  have hQ' : (Divisor.toQDivisor (topFormDivisor sX σ) + Δ).IsQCartier :=
    h.1.2.2.add_of_linearlyEquivalent hK'K.symm
  obtain ⟨m, hm, L, hL, hLc⟩ := hQ'.exists_pos
  have hB0 := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f L
  have hΘ' := MMP.ProgramBaseChange.isCrepantBoundary_pullback hX hdimX hY hfb hdimY' hσ0 hm hL hLc
  rw [hpull] at hΘ'
  set Θ : QDivisor Y := (1 / (m : ℚ)) • Divisor.toQDivisor (L.pullback hLc hB0) -
    Divisor.toQDivisor KY with hΘ_def
  have hΘ : IsCrepantBoundary sX n K Δ f hY hfb Θ := fun F =>
    MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hΘ' F) hK'K.symm
  have hLY : Divisor.toQDivisor (L.pullback hLc hB0) = (m : ℤ) • (Divisor.toQDivisor KY + Θ) := by
    have hm' : ((m : ℤ) : ℚ) * (1 / (m : ℚ)) = 1 := by
      have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [hΘ_def, add_sub_cancel, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, hm', one_smul]
  -- the coefficients of `Θ`
  have hΘexc : ∀ E : MMP.Mori.PrimeDivisor Y,
      (⟨Y, f, hY, hfb, E⟩ : DivisorOver k sX).IsExceptional → Θ.coeff E < 1 := fun E hE => by
    have := lt_of_lt_of_le hplt.2 (discrep_le hE (hΘ E))
    have : ((Θ.coeff E : ℝ) : EReal) < ((1 : ℝ) : EReal) := by simpa using this
    exact_mod_cast EReal.coe_lt_coe_iff.mp this
  have hΘnexc : ∀ E : MMP.Mori.PrimeDivisor Y,
      ¬ (⟨Y, f, hY, hfb, E⟩ : DivisorOver k sX).IsExceptional → ∃ P : MMP.Mori.PrimeDivisor X,
        Θ.coeff E = Δ.coeff P ∧ f E.genericPoint = P.genericPoint ∧
          inverseTransformPrimeDivisor f P = some E := fun E hE =>
    exists_coeff_eq_of_not_isExceptional h.1 hY hfb hΘ hE
  -- the strict transforms of the components of `⌊Δ⌋`
  have hbir : ∀ P : S, P.1.genericPoint ∈ biregularLocus f := fun P =>
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb
      P.1.coheight_genericPoint.le
  choose T hTinv hTη using fun P : S =>
    MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P.1 (hbir P)
  have hTinj : ∀ P Q, T P = T Q → P = Q := fun P Q hPQ =>
    Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hTη P).symm.trans ((congrArg (fun E => f E.genericPoint) hPQ).trans (hTη Q))))
  haveI : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hTnexc : ∀ P, ¬ (⟨Y, f, hY, hfb, T P⟩ : DivisorOver k sX).IsExceptional := fun P =>
    not_isExceptional_of_map_genericPoint_eq f (hTη P)
  have hΘT : ∀ P, Θ.coeff (T P) = 1 := fun P => by
    obtain ⟨P', hc, hη, -⟩ := hΘnexc (T P) (hTnexc P)
    obtain rfl : P' = P.1 := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hη.symm.trans (hTη P))
    rw [hc, hS1 P.1 P.2]
  -- the divisors `G = -⌊Θ⌋` and `H = G + ∑ T P`
  set G : Divisor Y := -Θ.roundDown with hG_def
  set F : Divisor Y := ∑ P : S, Finsupp.single (T P) (1 : ℤ) with hF_def
  have hFcoeff : ∀ E, F.coeff E = if ∃ P, T P = E then 1 else 0 := fun E => by
    change (∑ P : S, Finsupp.single (T P) (1 : ℤ)) E = _
    rw [Finsupp.finset_sum_apply]
    split_ifs with hE
    · obtain ⟨P₀, rfl⟩ := hE
      rw [Finset.sum_eq_single P₀ (fun P _ hP => Finsupp.single_eq_of_ne
        (fun h => hP (hTinj _ _ h.symm))) (fun h => absurd (Finset.mem_univ _) h)]
      exact Finsupp.single_eq_same
    · exact Finset.sum_eq_zero fun P _ => Finsupp.single_eq_of_ne fun h => hE ⟨P, h.symm⟩
  set H : Divisor Y := G + F with hH_def
  have hGT : ∀ P, G.coeff (T P) = -1 := fun P => by
    rw [hG_def, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown, hΘT, Int.floor_one]
  have hGE : ∀ E, (∀ P, E ≠ T P) → 0 ≤ G.coeff E := fun E hE => by
    rw [hG_def, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown, neg_nonneg]
    by_cases hexc : (⟨Y, f, hY, hfb, E⟩ : DivisorOver k sX).IsExceptional
    · exact Int.floor_le_iff.mpr (by push_cast; linarith [hΘexc E hexc])
    · obtain ⟨P, hc, hη, hinv⟩ := hΘnexc E hexc
      have hPS : P ∉ S := fun hPS => hE ⟨P, hPS⟩ (Option.some.inj ((hinv.symm.trans
        (hTinv ⟨P, hPS⟩))))
      rw [hc, hS0 P hPS]
  have hHeff : DivisorWithCoeffs.IsEffective H := fun E => by
    rw [hH_def, DivisorWithCoeffs.coeff_add, hFcoeff]
    split_ifs with hE
    · obtain ⟨P, rfl⟩ := hE
      rw [hGT]
      norm_num
    · simp only [not_exists] at hE
      simpa using hGE E fun P h => hE P h.symm
  have hH0 : 0 ≤ H := DivisorWithCoeffs.le_iff_isEffective_sub.mpr (by simpa using hHeff)
  have hGH : G ≤ H := DivisorWithCoeffs.le_iff_isEffective_sub.mpr fun E => by
    rw [hH_def, add_sub_cancel_left, hFcoeff]
    split_ifs <;> norm_num
  have hHexc : ∀ E, H.coeff E ≠ 0 → RationalMap.IsExceptional f.toRationalMap E := by
    intro E hE
    by_contra hexc
    obtain ⟨P, hc, hη, hinv⟩ := hΘnexc E hexc
    apply hE
    rw [hH_def, DivisorWithCoeffs.coeff_add, hFcoeff]
    by_cases hPS : P ∈ S
    · have hET : T ⟨P, hPS⟩ = E := Option.some.inj ((hTinv ⟨P, hPS⟩).symm.trans hinv)
      rw [if_pos ⟨_, hET⟩, ← hET, hGT]
      norm_num
    · have hnT : ¬ ∃ Q, T Q = E := fun ⟨Q, hQ⟩ => hPS (by
        have : Q.1 = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          ((hTη Q).symm.trans ((congrArg (fun E => f E.genericPoint) hQ).trans hη))
        exact this ▸ Q.2)
      rw [if_neg hnT, hG_def, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown, hc,
        hS0 P hPS]
      norm_num
  -- the fractional part of `Θ` is snc
  obtain ⟨Ssnc, hsncS, hmemS⟩ := MMP.Mori.exists_finset_isSNC hf.isSmoothScheme hf.isSNCSubset
  have hsnc : (Θ - Divisor.toQDivisor Θ.roundDown).IsSNC (f ≫ sX) := by
    refine hsncS.of_support_subset fun E hE => ?_
    have hΘE : Θ.coeff E ≠ 0 := by
      intro h0
      apply Finsupp.mem_support_iff.mp hE
      change (Θ - Divisor.toQDivisor Θ.roundDown).coeff E = 0
      rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown,
        h0]
      simp
    have hES : E ∈ Ssnc := hmemS E (by
      by_cases hexc : (⟨Y, f, hY, hfb, E⟩ : DivisorOver k sX).IsExceptional
      · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet E hexc
          (MMP.Flips.primeDivisor_genericPoint_mem_support E))
      · obtain ⟨P, hc, hη, -⟩ := hΘnexc E hexc
        refine Or.inr ?_
        change f E.genericPoint ∈ (QDivisor.toRDivisor Δ).supp
        rw [hη]
        refine DivisorWithCoeffs.support_subset_supp ?_
          (MMP.Flips.primeDivisor_genericPoint_mem_support P)
        rw [QDivisor.coeff_toRDivisor]
        exact_mod_cast hc ▸ hΘE)
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
      Finset.sum_eq_single E (fun b _ hb => Finsupp.single_eq_of_ne hb.symm)
        (fun h => absurd hES h), Finsupp.single_eq_same]
    exact one_ne_zero
  -- Kawamata–Viehweg vanishing
  have hR1 := isZero_rightDerived_one_neg_roundDown sX (f ≫ sX) hf.isSmoothScheme f rfl hfb KY hKY
    Θ hsnc hm (L.pullback hLc hB0) hLY fun C hC =>
      Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f rfl hLc hB0 C hC
  refine ⟨Y, inferInstance, inferInstance, inferInstance, f, T, fun P => ⟨hTη P, ?_⟩,
    fun P Q hPQ => hdisjT P.1 (hSΔ P.1 P.2) Q.1 (hSΔ Q.1 Q.2) (fun h => hPQ (Subtype.ext h)) _ _
      (hTinv P) (hTinv Q), fun P => ?_, ?_⟩
  · exact MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f
      (by rw [hTη P]; exact hbir P)
  · exact isNormal_of_isRegular _ (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme
      (hsmT P.1 (hSΔ P.1 P.2) (T P) (hTinv P)))
  · exact hasLift_of_isZero_rightDerived f S T hGH hH0 hGT hGE
      (fun U _ r hr => exists_app_eq_of_isDivisorialSection sX hX f hY hfb hdimX hHeff hHexc U r hr)
      hR1

section Main

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- **The round down of a plt dlt pair is normal.** Let `(X, Δ)` be a dlt pair with canonical
divisor `K` of dimension `n ≥ 2` over an algebraically closed field of characteristic zero, with
`Δ` effective. If `(X, Δ)` is plt, then the reduced closed subscheme on the support of `⌊Δ⌋` is
normal. -/
@[mmp "prop_km5b_dlt_plt_implies_floor_normal"]
public theorem IsDltPair.isNormal_suppScheme_roundDown [IsAlgClosed k] [CharZero k]
    (h : IsDltPair sX n K Δ) (hplt : IsPltPair sX n K Δ) (_hn : 2 ≤ n) (_hΔ : 0 ≤ Δ) :
    IsNormal Δ.roundDown.suppScheme := by
  obtain ⟨Y, _, _, _, g, T, hT, hdisj, hnorm, hlift⟩ := exists_hasLift h hplt
  exact isNormal_suppScheme_of_hasLift g Δ.roundDown T hT hdisj hnorm hlift

end Main

end MMP.Mori

end
