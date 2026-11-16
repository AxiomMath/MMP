module

public import MMP.Attr
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCommonMultiple.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothFibreTwist
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import StacksFrontier.AlgebraicGeometry.Picard.ClosedPointDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate

/-!
# The blow-up of a point of a smooth surface

Let `Y` be a smooth surface over an algebraically closed field `k`, of any characteristic, let
`y ∈ Y` be a closed point and `π : Y' ⟶ Y` the blow-up of the reduced point `y`. Then `Y'` is
smooth over `k`, `π` is proper, birational and an isomorphism over `Y ∖ {y}`, and the exceptional
curve `F = π⁻¹(y)` is isomorphic to `ℙ¹_k` and has self-intersection `F² = -1`.

The first assertions are the smooth blow-up statements with a centre of codimension `c = 2`:
the reduced point is `Spec k`, because `k` is algebraically closed, so `κ(y) = k` and the
fibre `ℙ¹_{κ(y)}` of `F ⟶ {y}` is `ℙ¹_k`. The self-intersection is the degree on `F` of
`𝒪_{Y'}(F)|_F`, which the smooth blow-up statements identify with `𝒪_{ℙ¹}(-1)`; and
`deg 𝒪_{ℙ¹}(-1) = χ(𝒪(-1)) - χ(𝒪) = 0 - 1 = -1`, by Serre's computation of the cohomology of
twists on the projective line and `H⁰(ℙ¹, 𝒪) = k`, `H¹(ℙ¹, 𝒪) = 0`.

## Main results

All in the namespace `MMP.Threefold.Resolution`.

* `invertibleCurveDegree_twistingSheaf_projSpace_neg_one`: `deg 𝒪_{ℙ¹_K}(-1) = -1` over any field
  `K`.
* `invertibleCurveDegree_comp_specMap`: degrees of invertible sheaves on curves are unchanged by an
  isomorphism of base fields.
* `exists_exceptional_iso_projSpace_singleton`: the exceptional curve of the blow-up of a closed
  point of a smooth surface is `ℙ¹_k`.
* `intersectionNumber_exceptional_self_eq_neg_one`: its self-intersection is `-1`.
* `blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection`: all clauses
  together.

## Implementation notes

* A smooth surface is a variety `Y` over `k` with `MMP.Mori.IsSmoothScheme sY` and
  `topologicalKrullDim Y = 2`; the blown-up point is `Scheme.IdealSheafData.vanishingIdeal {y}`.
* `ℙ¹_K` is `MMP.Intersection.ProjSpace K (ULift (Fin 2))` over `Spec K`, and `𝒪(-1)` its
  twisting sheaf. The degree of an invertible sheaf on a proper curve over `k` is
  `AlgebraicGeometry.invertibleCurveDegree`, through `MMP.Mori.degreeOn` along a curve in a
  `k`-scheme.
* The self-intersection `F²` is the intersection number `(F · C)` of the prime divisor `F` with
  the proper curve `C` of the same generic point, as in
  `MMP.Threefold.Resolution.intersectionNumber_self_neg_of_isBirationalMorphism`.
* The degree of `𝒪(-1)` is computed on the model `Proj K[T₀, T₁]`, where Serre's computation and
  the global functions are available, and transported along the renaming isomorphism.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.19]
* [Stacks Project, Tags 01XT, 01XU, 0AYR](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Threefold.Resolution

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

/-- `Proj K[T₀, T₁]` has dimension one. -/
theorem topologicalKrullDim_proj_polyGrading_one :
    topologicalKrullDim (AlgebraicGeometry.Proj (polyGrading K 1)) = 1 := by
  rw [Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin K (r := 2) (by norm_num)]; rfl

/-- `H⁰(Proj K[T₀, …, Tₙ], 𝒪) = K`, through the structure morphism. -/
theorem isIso_globalSections_projToSpecCoeff (n : ℕ) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (projToSpecCoeff K n).appTop) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections K n)

/-- The twisting sheaf `𝒪(m)` on `Proj R[T₀, …, Tₙ]` is invertible. -/
theorem isInvertible_twistingSheaf_polyGrading_algebraicGeometry (R : Type u) [CommRing R]
    (n : ℕ) (m : ℤ) :
    SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (polyGrading R n)).presheaf
      (AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf.2
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) m) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.isInvertible_twistingSheaf_of_cover
      (polyGrading R n) (fun i : Fin (n + 1) => (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
      (fun _ => 1) (fun i => MvPolynomial.isHomogeneous_X R i)
      (Stacks.AlgebraicGeometry.ProjPolyChart.iSup_basicOpen_X_eq_top R n) (fun _ => m)
      (fun _ => mul_one m))

/-- `deg 𝒪(-1) = -1` on `Proj K[T₀, T₁]`: `H⁰` and `H¹` of `𝒪(-1)` vanish, `H⁰(𝒪) = K` and the
genus is zero, so Riemann–Roch `h⁰ - h¹ = deg + 1 - g` gives `0 = deg + 1`. -/
theorem invertibleCurveDegree_twistingSheaf_polyGrading_neg_one :
    haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := K) 1
    haveI := isInvertible_twistingSheaf_polyGrading_algebraicGeometry K 1 (-1)
    invertibleCurveDegree K (projToSpecCoeff K 1) (topologicalKrullDim_proj_polyGrading_one K).le
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1)) = -1 := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := K) 1
  have := isInvertible_twistingSheaf_polyGrading_algebraicGeometry K 1 (-1)
  have := isIso_globalSections_projToSpecCoeff K 1
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus K (projToSpecCoeff K 1)
    (topologicalKrullDim_proj_polyGrading_one K).le
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1))
  have h0 : Module.finrank K (cohomologyOverField K (projToSpecCoeff K 1)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1)) 0) = 0 := by
    have := ModuleCat.subsingleton_of_isZero
      (Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_zero_of_neg K (d := -1)
        (by norm_num))
    have hs : Subsingleton (cohomologyOverField K (projToSpecCoeff K 1)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1)) 0) := this
    exact Module.finrank_zero_of_subsingleton
  have h1 : Module.finrank K (cohomologyOverField K (projToSpecCoeff K 1)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1)) 1) = 0 := by
    have := ModuleCat.subsingleton_of_isZero
      (Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le K (d := -1)
        le_rfl)
    have hs : Subsingleton (cohomologyOverField K (projToSpecCoeff K 1)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1)) 1) := this
    exact Module.finrank_zero_of_subsingleton
  rw [h0, h1, Stacks.Curves.genus_projToSpecCoeff_one] at h
  omega

/-- Invertibility of `𝒪(m)` on `ℙ^{ULift (Fin (n + 1))}_R`. -/
theorem isInvertible_twistingSheaf_projSpace (R : Type u) [CommRing R] (n : ℕ) (m : ℤ) :
    SheafOfModules.IsInvertible (MMP.Intersection.ProjSpace R (ULift.{u} (Fin (n + 1)))).presheaf
      (MMP.Intersection.ProjSpace R (ULift.{u} (Fin (n + 1)))).ringCatSheaf.2
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R) m) :=
  have := isInvertible_twistingSheaf_polyGrading_algebraicGeometry R n m
  Stacks.UFDExtensionGlobal.isInvertible_of_iso
    (MMP.Intersection.ProjSpace.twistingSheafIsoPullback R n m)
    (MMP.Mori.isInvertible_pullback_obj _ _)

/-- `ℙ¹_K` has dimension one. -/
theorem topologicalKrullDim_projSpace_one :
    topologicalKrullDim (MMP.Intersection.ProjSpace K (ULift.{u} (Fin 2))) = 1 := by
  rw [Stacks.ProjectiveSpace.topologicalKrullDim_proj K (ULift.{u} (Fin 2))]
  simp

/-- **`deg 𝒪_{ℙ¹_K}(-1) = -1`.** On the projective line `ℙ¹_K = ProjSpace K (ULift (Fin 2))`
over a field `K`, the twisting sheaf `𝒪(-1)` has degree `-1`. -/
theorem invertibleCurveDegree_twistingSheaf_projSpace_neg_one :
    haveI := isInvertible_twistingSheaf_projSpace K 1 (-1)
    invertibleCurveDegree K (MMP.Intersection.ProjSpace.toSpec K (ULift.{u} (Fin 2)))
      (topologicalKrullDim_projSpace_one K).le
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) K) (-1)) = -1 := by
  have := isInvertible_twistingSheaf_projSpace K 1 (-1)
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := K) 1
  have := isInvertible_twistingSheaf_polyGrading_algebraicGeometry K 1 (-1)
  have := MMP.Mori.isInvertible_pullback_obj (MMP.Intersection.ProjSpace.isoPolyGrading K 1).hom
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1))
  have hover : (MMP.Intersection.ProjSpace.isoPolyGrading K 1).hom ≫ projToSpecCoeff K 1 =
      MMP.Intersection.ProjSpace.toSpec K (ULift.{u} (Fin 2)) := by
    rw [← isoPolyGrading_inv_comp_toSpec, Iso.hom_inv_id_assoc]
  rw [← invertibleCurveDegree_eq_of_iso K _ _
    (MMP.Intersection.ProjSpace.twistingSheafIsoPullback K 1 (-1)),
    invertibleCurveDegree_congr K hover.symm]
  exact (invertibleCurveDegree_pullback_of_isIso (k := K)
    (e := (MMP.Intersection.ProjSpace.isoPolyGrading K 1).hom)
    (g := projToSpecCoeff K 1) (hB := (topologicalKrullDim_proj_polyGrading_one K).le)
    (L := ProjectiveSpectrum.Proj.twistingSheaf (polyGrading K 1) (-1)) ..).trans
    (invertibleCurveDegree_twistingSheaf_polyGrading_neg_one K)

/-- **Degrees are unchanged by an isomorphism of base fields.** If `φ : k ⟶ K` is bijective and
`f : X ⟶ Spec K` is proper, then the cohomology of a module `F` on `X` has the same dimension over
`k`, through `f ≫ Spec φ`, as over `K`, through `f`. -/
theorem finrank_cohomologyOverField_comp_specMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    (hφ : Function.Bijective φ) (F : X.Modules) (n : ℕ) :
    Module.finrank k (cohomologyOverField k (f ≫ Spec.map φ) F n) =
      Module.finrank K (cohomologyOverField K f F n) := by
  rw [cohomologyOverField_eq_restrictScalars_appTop, cohomologyOverField_eq_restrictScalars_appTop]
  have hψ : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ Spec.map φ).appTop =
      φ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  rw [hψ]
  have h := rank_eq_of_equiv_equiv (R := k) (R' := K) φ.hom (AddEquiv.refl _) hφ
    (fun r m => rfl) (M := (ModuleCat.restrictScalars
      (φ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F))
    (M₁ := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F))
  simp only [Module.finrank, h]

/-- **The degree of an invertible sheaf is unchanged by an isomorphism of base fields.** -/
theorem invertibleCurveDegree_comp_specMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f] (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    [IsProper (f ≫ Spec.map φ)] (hφ : Function.Bijective φ)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    invertibleCurveDegree k (f ≫ Spec.map φ) hdim L = invertibleCurveDegree K f hdim L := by
  unfold invertibleCurveDegree
  simp only [finrank_cohomologyOverField_comp_specMap K f φ hφ]
  congr 1
  exact finsum_congr fun n => by
    erw [finrank_cohomologyOverField_comp_specMap K f φ hφ]

section BaseChange

open CategoryTheory.Limits

variable {k : Type u} [Field k] (φ : CommRingCat.of k ⟶ CommRingCat.of K) [IsIso φ] (n : ℕ)

/-- An isomorphism of fields `k ≅ K` identifies `ℙⁿ_K` with `ℙⁿ_k`, over `Spec K ≅ Spec k`. -/
def projSpaceIsoOfIsIso :
    MMP.Intersection.ProjSpace K (ULift.{u} (Fin (n + 1))) ≅
      MMP.Intersection.ProjSpace k (ULift.{u} (Fin (n + 1))) :=
  MMP.Intersection.ProjSpace.isoProjectiveSpaceOver K n ≪≫
    asIso (pullback.map (terminal.from (Spec (.of K)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) (Spec.map φ) (𝟙 _) (𝟙 _)
      (terminal.hom_ext _ _) (by simp)) ≪≫
    (MMP.Intersection.ProjSpace.isoProjectiveSpaceOver k n).symm

/-- The isomorphism `projSpaceIsoOfIsIso` lies over `Spec φ`. -/
theorem projSpaceIsoOfIsIso_hom_toSpec :
    (projSpaceIsoOfIsIso K φ n).hom ≫ MMP.Intersection.ProjSpace.toSpec k _ =
      MMP.Intersection.ProjSpace.toSpec K _ ≫ Spec.map φ := by
  rw [← MMP.Intersection.ProjSpace.isoProjectiveSpaceOver_hom_fst k n,
    ← MMP.Intersection.ProjSpace.isoProjectiveSpaceOver_hom_fst K n]
  simp [projSpaceIsoOfIsIso]

end BaseChange

/-! ### The centre of the blow-up of a closed point -/

section PointCentre

open TopologicalSpace

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType sY] {y : Y} (hy : IsClosed ({y} : Set Y))

/-- The reduced closed point `{y}`, as an ideal sheaf. -/
local notation "𝓘[" y ", " hy "]" =>
  Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : TopologicalSpace.Closeds _)

/-- Over an algebraically closed field, the reduced closed point `{y}` of a `k`-scheme locally of
finite type maps isomorphically to `Spec k`. -/
theorem isIso_subschemeι_vanishingIdeal_singleton_comp :
    IsIso ((𝓘[y, hy]).subschemeι ≫ sY) := by
  have := isIso_subschemeι_ker_pointOfClosedPoint_comp k sY hy
  rwa [ker_pointOfClosedPoint_eq_vanishingIdeal k sY hy, ← closeds_singleton_eq_closure hy]
    at this

include sY in
/-- The reduced closed point `{y}` has a single point. -/
theorem subsingleton_subscheme_vanishingIdeal_singleton :
    Subsingleton (𝓘[y, hy]).subscheme := by
  have := isIso_subschemeι_vanishingIdeal_singleton_comp sY hy
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact (asIso ((𝓘[y, hy]).subschemeι ≫
    sY)).hom.homeomorph.injective.subsingleton

include sY in
/-- Every point of the reduced closed point `{y}` is closed. -/
theorem isClosed_singleton_subscheme_vanishingIdeal_singleton
    (z : (𝓘[y, hy]).subscheme) :
    IsClosed ({z} : Set _) := by
  have := subsingleton_subscheme_vanishingIdeal_singleton sY hy
  rw [show ({z} : Set _) = Set.univ from Set.eq_univ_of_forall fun w => Subsingleton.elim w z]
  exact isClosed_univ

/-- The residue field `κ(z)` of the reduced closed point is `k`, through the structure morphism:
`Spec κ(z) ⟶ {y} ⟶ Spec k` is `Spec` of an isomorphism of rings. -/
theorem specMap_residueFieldIsoBase_inv_vanishingIdeal_singleton
    (z : (𝓘[y, hy]).subscheme) :
    Spec.map (residueFieldIsoBase
        ((𝓘[y, hy]).subschemeι ≫ sY) z
        (isClosed_singleton_subscheme_vanishingIdeal_singleton sY hy z)).inv =
      (𝓘[y, hy]).subscheme.fromSpecResidueField
          z ≫ (𝓘[y, hy]).subschemeι ≫ sY :=
  SpecMap_residueFieldIsoBase_inv _ _ _

include sY in
/-- The point `Spec κ(z) ⟶ {y}` of the reduced closed point is an isomorphism. -/
theorem isIso_fromSpecResidueField_vanishingIdeal_singleton
    (z : (𝓘[y, hy]).subscheme) :
    IsIso ((𝓘[y, hy]).subscheme.fromSpecResidueField
      z) := by
  have := isIso_subschemeι_vanishingIdeal_singleton_comp sY hy
  have h := specMap_residueFieldIsoBase_inv_vanishingIdeal_singleton sY hy z
  have : IsIso ((𝓘[y, hy]).subscheme.fromSpecResidueField
      z ≫ (𝓘[y, hy]).subschemeι ≫ sY) := by
    rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((𝓘[y, hy]).subschemeι ≫ sY)

end PointCentre

/-! ### The self-intersection of the exceptional curve -/

section SelfIntersection

open TopologicalSpace Stacks.AlgebraicGeometry MMP.Mori MMP.Threefold.Mori

/-- The reduced closed point `{y}`, as an ideal sheaf. -/
local notation "𝓘[" y ", " hy "]" =>
  Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : TopologicalSpace.Closeds _)

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- A closed point of a smooth surface over an algebraically closed field has codimension two. -/
theorem codimension_vanishingIdeal_singleton_eq_two (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    codimension (⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support,
      isIrreducible_support_vanishingIdeal_singleton hy,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support.isClosed⟩ :
        IrreducibleCloseds Y) = 2 := by
  have heq : (⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support,
      isIrreducible_support_vanishingIdeal_singleton hy,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support.isClosed⟩ :
        IrreducibleCloseds Y) = IrreducibleCloseds.closureSingleton y := by
    ext1
    change ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support : Set Y) =
      closure {y}
    rw [support_vanishingIdeal_singleton hy, hy.closure_eq]
  rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton,
    coheight_eq_two_of_isClosed hY hYd hy]

/-- **The exceptional curve of the blow-up of a point of a smooth surface has `F² = -1`.**
Let `Y` be a smooth surface over an algebraically closed field `k`, `y ∈ Y` a closed point,
`π : Y' ⟶ Y` the blow-up of `y`, `F` the exceptional prime divisor and `C` the proper curve with
the same generic point. Then the intersection number `(F · C)` is `-1`. -/
theorem intersectionNumber_exceptional_self_eq_neg_one (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y))
    (F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))))
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (C : ProperCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY))
    (hC : C.point = F.genericPoint) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
    haveI := (isVariety_blowUp_singleton hY hYd hy).toQuasiCompact
    (Divisor.toQDivisor (Finsupp.single F 1)).intersectionNumber k
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) C.ι C.dim_le
        (isQCartier_single_of_isSmoothScheme (isSmoothScheme_blowUp_singleton hY hYs hYd hy) F) =
      -1 := by
  have hsm := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).2
  have := (isVariety_blowUp_singleton hY hYd hy).toQuasiCompact
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
  obtain ⟨b⟩ := nonempty_invertibleSheaf'_iso_of_eq hF
  suffices h : Mori.degreeOn k (blowUpToBase 𝓘[y, hy] ≫ sY) C.ι C.dim_le
      (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal 𝓘[y, hy]) :
        (blowUp 𝓘[y, hy]).Modules) = -1 by
    rw [intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsm F C,
      Mori.degreeOn_eq_of_iso k _ C.ι C.dim_le b, h]
    norm_num
  -- the fibre of `E ⟶ {y}` over the point `z` is `ℙ¹_{κ(z)}`, and `𝒪(E)` restricts to `𝒪(-1)`
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := isIrreducible_support_vanishingIdeal_singleton hy
  have hcodim := codimension_vanishingIdeal_singleton_eq_two hY hYd hy
  obtain ⟨c, hc, hfib⟩ := exists_fiber_iso_projSpace_pullback_invertibleSheaf_exceptionalIdeal sY
    𝓘[y, hy] hsb hirr (by rw [hcodim])
  have hc2 : c = 2 := by rw [hcodim] at hc; exact_mod_cast hc
  subst hc2
  have := isIso_subschemeι_vanishingIdeal_singleton_comp sY hy
  obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
  obtain ⟨z⟩ : Nonempty 𝓘[y, hy].subscheme := ⟨(inv (𝓘[y, hy].subschemeι ≫ sY)) p⟩
  obtain ⟨e, he, ⟨ι⟩⟩ := hfib z
  have hz := isClosed_singleton_subscheme_vanishingIdeal_singleton sY hy z
  set φ := (residueFieldIsoBase (𝓘[y, hy].subschemeι ≫ sY) z hz).inv
  have hφ : Function.Bijective φ := (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hiz := isIso_fromSpecResidueField_vanishingIdeal_singleton sY hy z
  have : IsIso ((exceptionalSubschemeMap 𝓘[y, hy]).fiberι z) :=
    Limits.pullback_fst_iso_of_right_iso _ _
  -- the curve `C` is the exceptional divisor `E`, hence the fibre, hence `ℙ¹_{κ(z)}`
  have hCI : Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set _)) =
      exceptionalIdeal 𝓘[y, hy] := by
    rw [hC, vanishingIdeal_closure_genericPoint_eq_idealSheaf, hF]
  obtain ⟨b', hb'⟩ := exists_subscheme_iso_of_eq hCI
  set g := (exceptionalSubschemeMap 𝓘[y, hy]).fiberι z ≫ (exceptionalIdeal 𝓘[y, hy]).subschemeι
  obtain ⟨a, ha⟩ : ∃ a : C.scheme ≅
      MMP.Intersection.ProjSpace (𝓘[y, hy].subscheme.residueField z) (ULift.{u} (Fin 2)),
      a.hom ≫ (e.inv ≫ g) = C.ι :=
    ⟨b' ≪≫ (asIso ((exceptionalSubschemeMap 𝓘[y, hy]).fiberι z)).symm ≪≫ e, by
      simp only [g, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
        Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc]
      exact hb'⟩
  have hj : e.inv ≫ g = a.inv ≫ C.ι := by rw [← ha, Iso.inv_hom_id_assoc]
  have : IsProper ((e.inv ≫ g) ≫ blowUpToBase 𝓘[y, hy] ≫ sY) := by
    rw [hj, Category.assoc]; infer_instance
  have hjs : (e.inv ≫ g) ≫ blowUpToBase 𝓘[y, hy] ≫ sY =
      MMP.Intersection.ProjSpace.toSpec (𝓘[y, hy].subscheme.residueField z)
        (ULift.{u} (Fin 2)) ≫ Spec.map φ := by
    simp only [g, Category.assoc]
    rw [← Scheme.IdealSheafData.subschemeMap_subschemeι_assoc (exceptionalIdeal 𝓘[y, hy]) 𝓘[y, hy]
      (blowUpToBase 𝓘[y, hy]) (𝓘[y, hy].le_map_comap (blowUpToBase 𝓘[y, hy])),
      Scheme.Hom.fiber_fac_assoc, ← he,
      Category.assoc, Iso.inv_hom_id_assoc,
      specMap_residueFieldIsoBase_inv_vanishingIdeal_singleton]
  refine (degreeOn_eq_of_iso_comp k _ C.ι (e.inv ≫ g) C.dim_le
    (topologicalKrullDim_projSpace_one (𝓘[y, hy].subscheme.residueField z)).le a ha
    (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal 𝓘[y, hy]) :
      (blowUp 𝓘[y, hy]).Modules)).trans ?_
  unfold Mori.degreeOn
  have := isInvertible_twistingSheaf_projSpace (𝓘[y, hy].subscheme.residueField z) 1 (-1)
  have : IsProper (MMP.Intersection.ProjSpace.toSpec (𝓘[y, hy].subscheme.residueField z)
      (ULift.{u} (Fin 2)) ≫ Spec.map φ) := by
    rw [← hjs]; infer_instance
  let isoT : (Scheme.Modules.pullback (e.inv ≫ g)).obj
        (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal 𝓘[y, hy]) :
          (blowUp 𝓘[y, hy]).Modules) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2))
        (𝓘[y, hy].subscheme.residueField z)) (-1) :=
    ((Scheme.Modules.pullbackComp e.inv g).app _).symm ≪≫
      (Scheme.Modules.pullback e.inv).mapIso ι ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr e.inv_hom_id).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _
  rw [invertibleCurveDegree_eq_of_iso k _ _ isoT]
  exact (invertibleCurveDegree_congr k hjs _ _).trans
    ((invertibleCurveDegree_comp_specMap (𝓘[y, hy].subscheme.residueField z) _ φ hφ _ _).trans
      (invertibleCurveDegree_twistingSheaf_projSpace_neg_one (𝓘[y, hy].subscheme.residueField z)))

/-- **The exceptional curve is `ℙ¹_k`.** The exceptional divisor `E = π⁻¹(y)` of the blow-up of
a closed point of a smooth surface over an algebraically closed field `k` is isomorphic over `k`
to the projective line. -/
theorem exists_exceptional_iso_projSpace_singleton (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) :
    ∃ e : (exceptionalIdeal 𝓘[y, hy]).subscheme ≅
        MMP.Intersection.ProjSpace k (ULift.{u} (Fin 2)),
      e.hom ≫ MMP.Intersection.ProjSpace.toSpec k _ =
        (exceptionalIdeal 𝓘[y, hy]).subschemeι ≫ blowUpToBase 𝓘[y, hy] ≫ sY := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := isIrreducible_support_vanishingIdeal_singleton hy
  have hcodim := codimension_vanishingIdeal_singleton_eq_two hY hYd hy
  obtain ⟨-, -, c, hc, hfib⟩ := smooth_exceptionalDivisor_and_fiber_iso_projSpace sY
    𝓘[y, hy] hsb hirr (by rw [hcodim])
  have hc2 : c = 2 := by rw [hcodim] at hc; exact_mod_cast hc
  subst hc2
  have := isIso_subschemeι_vanishingIdeal_singleton_comp sY hy
  obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
  obtain ⟨z⟩ : Nonempty 𝓘[y, hy].subscheme := ⟨(inv (𝓘[y, hy].subschemeι ≫ sY)) p⟩
  obtain ⟨e, he⟩ := hfib z
  have hz := isClosed_singleton_subscheme_vanishingIdeal_singleton sY hy z
  have hiz := isIso_fromSpecResidueField_vanishingIdeal_singleton sY hy z
  have : IsIso ((exceptionalSubschemeMap 𝓘[y, hy]).fiberι z) :=
    Limits.pullback_fst_iso_of_right_iso _ _
  refine ⟨(asIso ((exceptionalSubschemeMap 𝓘[y, hy]).fiberι z)).symm ≪≫ e ≪≫
    projSpaceIsoOfIsIso (𝓘[y, hy].subscheme.residueField z)
      (residueFieldIsoBase (𝓘[y, hy].subschemeι ≫ sY) z hz).inv 1, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [projSpaceIsoOfIsIso_hom_toSpec, reassoc_of% he,
    specMap_residueFieldIsoBase_inv_vanishingIdeal_singleton, ← Scheme.Hom.fiber_fac_assoc,
    IsIso.inv_hom_id_assoc, Scheme.IdealSheafData.subschemeMap_subschemeι_assoc]

open MMP.Resolution in
/-- **The blow-up of a point of a smooth surface.** Let `Y` be a smooth surface over an
algebraically closed field `k` (of any characteristic), `y ∈ Y` a closed point and
`π : Y' = Bl_y Y ⟶ Y` the blow-up of the reduced point `y`. Then `Y'` is smooth over `k`; `π` is
proper, birational, and an isomorphism over `Y ∖ {y}`; and there is a prime divisor `F` of `Y'`,
the exceptional curve `π⁻¹(y)`, which is isomorphic over `k` to `ℙ¹_k`, is the generic point of a
proper curve, and has self-intersection `F² = (F · F) = -1`. -/
@[mmp "lem_mmp_threefold_surface_blowup"]
theorem blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection
    (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    Smooth (blowUpToBase 𝓘[y, hy] ≫ sY) ∧ IsProper (blowUpToBase 𝓘[y, hy]) ∧
      MMP.Mori.IsBirationalMorphism (blowUpToBase 𝓘[y, hy]) ∧
      IsIso (blowUpToBase 𝓘[y, hy] ∣_ (⟨{y}ᶜ, hy.isOpen_compl⟩ : Y.Opens)) ∧
      ∃ F : Mori.PrimeDivisor (blowUp 𝓘[y, hy]),
        F.idealSheaf = exceptionalIdeal 𝓘[y, hy] ∧
        (∃ e : (exceptionalIdeal 𝓘[y, hy]).subscheme ≅
            MMP.Intersection.ProjSpace k (ULift.{u} (Fin 2)),
          e.hom ≫ MMP.Intersection.ProjSpace.toSpec k _ =
            (exceptionalIdeal 𝓘[y, hy]).subschemeι ≫ blowUpToBase 𝓘[y, hy] ≫ sY) ∧
        IsProperCurve (blowUpToBase 𝓘[y, hy] ≫ sY) F.genericPoint ∧
        ∀ C : ProperCurve (blowUpToBase 𝓘[y, hy] ≫ sY), C.point = F.genericPoint →
          haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
            (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
          haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
            (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
          haveI := (isVariety_blowUp_singleton hY hYd hy).toQuasiCompact
          (Divisor.toQDivisor (Finsupp.single F 1)).intersectionNumber k
              (blowUpToBase 𝓘[y, hy] ≫ sY) C.ι C.dim_le
              (isQCartier_single_of_isSmoothScheme
                (isSmoothScheme_blowUp_singleton hY hYs hYd hy) F) = -1 := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := isIrreducible_support_vanishingIdeal_singleton hy
  have hcodim := codimension_vanishingIdeal_singleton_eq_two hY hYd hy
  have hc2 : 2 ≤ codimension (⟨(𝓘[y, hy]).support, hirr, (𝓘[y, hy]).support.isClosed⟩ :
      IrreducibleCloseds Y) := by rw [hcodim]
  obtain ⟨hsm, -, hbir, hiso, -, -⟩ :=
    smooth_isProjective_isBirationalMorphism_blowUpToBase sY 𝓘[y, hy] hsb hirr hc2
  have hU : (⟨(𝓘[y, hy]).supportᶜ, (𝓘[y, hy]).support.isClosed.isOpen_compl⟩ : Y.Opens) =
      ⟨{y}ᶜ, hy.isOpen_compl⟩ := by
    ext1
    change ((𝓘[y, hy]).support : Set Y)ᶜ = {y}ᶜ
    rw [support_vanishingIdeal_singleton hy]
  rw [hU] at hiso
  have hproper : IsProper (blowUpToBase 𝓘[y, hy]) :=
    TwoStepTower.isProper_blowUpToBase
      (TwoStepTower.isFiniteType_of_isLocallyNoetherian _)
  let F : Mori.PrimeDivisor (blowUp 𝓘[y, hy]) :=
    exceptionalPrimeDivisor sY 𝓘[y, hy] hsb hirr (le_trans (by norm_num) hc2)
  have hF : F.idealSheaf = exceptionalIdeal 𝓘[y, hy] := rfl
  obtain ⟨e, he⟩ := exists_exceptional_iso_projSpace_singleton hY hYs hYd hy
  refine ⟨hsm, hproper, hbir, hiso, F, hF, ⟨e, he⟩, ?_,
    fun C hC => intersectionNumber_exceptional_self_eq_neg_one hY hYs hYd hy F hF C hC⟩
  -- `F` is a proper curve: its reduced subscheme is `E ≅ ℙ¹_k`
  have hsmY' := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsmY').1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsmY').2
  have hCI : Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({F.genericPoint} : Set _)) =
      exceptionalIdeal 𝓘[y, hy] := by
    rw [vanishingIdeal_closure_genericPoint_eq_idealSheaf, hF]
  obtain ⟨b, hb⟩ := exists_subscheme_iso_of_eq hCI
  refine ⟨?_, ?_⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq _ (b ≪≫ e).hom.homeomorph.isHomeomorph]
    exact topologicalKrullDim_projSpace_one k
  · have hι : curveSubschemeAtι F.genericPoint ≫ blowUpToBase 𝓘[y, hy] ≫ sY =
        (b ≪≫ e).hom ≫ MMP.Intersection.ProjSpace.toSpec k _ := by
      rw [Iso.trans_hom, Category.assoc, he, reassoc_of% hb]
    rw [hι]
    infer_instance

end SelfIntersection

end MMP.Threefold.Resolution
