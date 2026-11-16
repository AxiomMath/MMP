module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.Geometrically.NumericalDivisorClassesBaseChange
import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModels
import MMP.AlgebraicGeometry.SpreadingOut.GenericFibreDimension
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.OpenLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# Curves and their classes under change of algebraically closed field

Let `k₀ ⊆ K` be algebraically closed fields, `X₀` a projective variety over `k₀` and
`X = X₀ ×_{k₀} K` its base change, with projection `π : X ⟶ X₀`. For an integral curve
`C₀ ⊆ X₀` the preimage `(C₀)_K = π⁻¹(C₀)` is again an integral curve, and degrees of invertible
sheaves pulled back from `X₀` are the same on `C₀` and on `(C₀)_K`, Euler characteristics being
invariant under extension of the ground field.

Conversely every integral curve `C ⊆ X` is numerically equivalent to some `(C₀)_K`: `C` spreads
out to a flat proper closed subscheme of `X₀ ×_{k₀} Spec A` over a finitely generated
`k₀`-subalgebra `A ⊆ K`, whose fibre `C₀` at a `k₀`-point of `Spec A` where the fibres are
geometrically integral curves has the same degrees, Euler characteristics being constant in the
flat family over the connected `Spec A`. Hence base extension of curves induces an isomorphism
`φ : N₁(X₀)_ℝ ≃ N₁(X)_ℝ`; it is the transpose of the pull-back isomorphism on `N¹`, so it is a
homeomorphism for the numerical topologies and carries `NE̅(X₀)` onto `NE̅(X)`. For a morphism
`f₀ : X₀ ⟶ Z₀` of projective varieties with base change `f`, an ample sheaf on `Z₀` detects the
contracted curves on both sides, so `φ` maps the span of the `f₀`-contracted curve classes onto
that of the `f`-contracted ones.

Finally, if the contraction `f : X ⟶ Z` of the ray `φ(R₀)` spreads out to a projective
morphism `f_S : X₀ ×_{k₀} S ⟶ Z_S` over an integral `k₀`-scheme `S` with an `S`-ample sheaf,
then the fibre of `f_S` at every `k₀`-point of `S` contracts exactly the curves with class in
`R₀`: degrees of `f_S^* H_S` are constant in the family `C ×_{k₀} S ⟶ S`.

## Main results

* `MMP.Fourfold.exists_properCurve_degree_eq_of_isPullback`: every integral curve class on `X`
  is the class of the base change of an integral curve on `X₀`.
* `MMP.Fourfold.numericalCurveClassesBaseChange`: base extension of curves induces
  `N₁(X₀)_ℝ ≃ N₁(X)_ℝ`.
* `MMP.Fourfold.map_closedConeOfCurves_eq_of_isPullback`: `φ(NE̅(X₀)) = NE̅(X)`.
* `MMP.Fourfold.map_span_contractedCurveClasses_eq_of_isPullback`: `φ` maps the span of the
  `f₀`-contracted curve classes isomorphically onto the span of the `f`-contracted ones.
* `MMP.Fourfold.IsContractionOfRay.isContractedBy_fibre_iff`: the fibre of a spread
  contraction contracts exactly the given ray.

## Implementation notes

Every base change is an abstract pull-back square, as for
`MMP.Fourfold.numericalDivisorClassesBaseChange_eq_of_isPullback`, and the base change
`(C₀)_K` of a proper curve `C₀` is recorded as the proper curve of `X` whose closure is
`π⁻¹(closure C₀)`. Since `k₀` is algebraically closed this preimage is irreducible and reduced,
so it determines `(C₀)_K`. The maps `φ` are taken to be any linear maps with
`φ [C₀] = [(C₀)_K]`; curve classes span `N₁(X₀)_ℝ`, so this determines `φ`.

The spreading of curves is done without a characteristic hypothesis: the geometric integrality
of the fibres comes from the characteristic-free Stacks 0559, 0578 and 05F7. That `φ` is a
homeomorphism is deduced from the transpose relation `(Φ c₀ · φ z) = (c₀ · z)` rather than from
finite-dimensionality of `N₁`. In the spread contraction the family `Z_S ⟶ S` need not be of
finite type, so positivity of degrees on its fibre is proved for a morphism to an arbitrary
scheme: a non-constant proper morphism from a proper curve is finite.

## References

* [KM98] Kollár, Mori, *Birational Geometry of Algebraic Varieties*.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori RingedSpaceModuleAdjunction

-- Without this, instance search for `IsIntegral` and finiteness classes on the images and
-- fibres below loops through `IsVariety` and times out.
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

universe u

/-! ### Contracted curves and ample degrees -/

section Contraction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- A proper curve which is not contracted by `g` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (g : X ⟶ Y) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : ¬ ∃ y : Y, Set.range (Γ.ι ≫ g) = {y} := by
  rintro ⟨y, hy⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨c, rfl⟩ := hx
  have h1 : (Γ.ι ≫ g) c ∈ Set.range (Γ.ι ≫ g) := ⟨c, rfl⟩
  have h2 : (Γ.ι ≫ g) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ g) := ⟨_, rfl⟩
  rw [hy] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- The image of a proper curve not contracted by `g` is a proper curve. -/
private theorem isProperCurve_map (g : X ⟶ Y) (hg : g ≫ sY = sX) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : IsProperCurve sY (g Γ.point) := by
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hcurve := isCurve_imageι_comp sY φ (not_exists_range_eq_singleton g Γ h)
  have hker := Γ.ker_comp g
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (g Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (g Γ.point) ≫ sY) := by
    have h1 : IsProper (φ.imageι ≫ sY) := isProper_imageι_comp φ sY
    change IsProper (φ.ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- A morphism over `k` which does not contract a proper curve has positive residue degree at
its generic point: `k(C)` is a finite extension of the function field of the image curve. -/
private theorem residueFieldDegree_pos_of_not_isContractedBy (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (Γ : ProperCurve sX) (h : ¬ Γ.IsContractedBy g) : 0 < residueFieldDegree g Γ.point := by
  have hnc := not_exists_range_eq_singleton g Γ h
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree g Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι g (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- An ample invertible sheaf has positive degree on every proper curve. -/
private theorem degree_pos_of_isAmple (D : ProperCurve sY) (H : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple Y H) : 0 < D.degree k H := by
  have := D.isCurve
  exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k (D.ι ≫ sY) D.dim_le _
    (isAmple_pullback_of_isFinite D.ι H hH)

/-- **Contraction is detected by an ample degree.** If the pull-back of an ample invertible
sheaf along `g` has degree zero on a proper curve, then `g` contracts the curve. -/
private theorem isContractedBy_of_degree_pullback_eq_zero (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (H : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple Y H) (Γ : ProperCurve sX)
    (h0 : Γ.degree k ((Scheme.Modules.pullback g).obj H) = 0) : Γ.IsContractedBy g := by
  by_contra hc
  have hD := isProperCurve_map g hg Γ hc
  rw [Γ.degree_pullback g hg H, dif_pos hD] at h0
  have h1 := residueFieldDegree_pos_of_not_isContractedBy g hg Γ hc
  have h2 := degree_pos_of_isAmple ⟨g Γ.point, hD⟩ H hH
  have : (0 : ℤ) <
      (residueFieldDegree g Γ.point : ℤ) * (⟨g Γ.point, hD⟩ : ProperCurve sY).degree k H :=
    mul_pos (by exact_mod_cast h1) h2
  omega

end Contraction

/-! ### Curves as closed subschemes -/

section CurveLemmas

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced {Y W : Scheme.{u}} (ι : Y ⟶ W)
    [IsClosedImmersion ι] [IsReduced Y] (T : TopologicalSpace.Closeds W)
    (hT : (T : Set W) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    rw [RingHom.mem_ker]
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  have : ι.ker.support = T := TopologicalSpace.Closeds.ext <| by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq, hT]
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A closed immersion from an integral scheme is, up to isomorphism, the closed immersion of the
closure of the image of the generic point. -/
private theorem exists_iso_curveSubschemeAt {Y W : Scheme.{u}} [IsIntegral Y] (ι : Y ⟶ W)
    [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : Set.range ι = closure {ι (genericPoint Y)} := by
    rw [← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec Y).def]
    simp
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced ι (TopologicalSpace.Closeds.closure
      {ι (genericPoint Y)}) hrange.symm]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
  have hf : IsIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  exact ⟨asIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- An integral one-dimensional closed subscheme `ι : Y ⟶ X`, proper over `k`, is a proper curve
`C` of `X`, with `Y ≅ C` over `X`. -/
private theorem exists_properCurve_of_isClosedImmersion {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {Y : Scheme.{u}}
    [IsIntegral Y] (ι : Y ⟶ X) [IsClosedImmersion ι] [IsProper (ι ≫ sX)]
    (hdim : topologicalKrullDim Y = 1) :
    ∃ (C : ProperCurve sX) (e : Y ≅ C.scheme), e.hom ≫ C.ι = ι := by
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt ι
  refine ⟨⟨ι (genericPoint Y), ⟨?_, ?_⟩⟩, e, he⟩
  · rw [← (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq, hdim]
  · rw [← (Iso.inv_comp_eq e).mpr he.symm, Category.assoc]
    infer_instance

end CurveLemmas

/-! ### Euler characteristics in flat proper families -/

section EulerAcrossPoints

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic CategoryTheory.Limits

/-- An invertible module on a scheme flat over `S` is flat over `S`. -/
private theorem isFlatOver_of_isInvertibleModule {X S : Scheme.{u}} (π : X ⟶ S) [Flat π]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] :
    IsFlatOver π.toLRSHom.toShHom F := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf _ _).mp ‹_›
  have : F.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule F
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ F h0)
  obtain ⟨-, hfree⟩ :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae F).out 4 2).mp hflf
  intro x
  letI := (π.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (π x)) (X.presheaf.stalk x) := Flat.stalkMap π x
  have := hfree x
  letI : Module (S.presheaf.stalk (π x)) (F.presheaf.stalk x) :=
    Module.compHom _ (π.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) := Module.Flat.of_free
  exact Module.Flat.trans (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- The fibre Euler characteristic of an invertible module in a flat proper family of finite
presentation over a connected base is independent of the point. -/
private theorem fibreEulerCharacteristic_eq_of_connected {W S : Scheme.{u}} (f : W ⟶ S) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f] [ConnectedSpace S]
    (F : W.Modules) [Stacks.Ample.IsInvertibleModule W F] (s s' : S) :
    fibreEulerCharacteristic f F s = fibreEulerCharacteristic f F s' := by
  have h := (MMP.fibreEulerCharacteristic_tensorPowModule_eq f F).1 1 s s'
  have e : ∀ t, fibreEulerCharacteristic f (Stacks.Ample.tensorPowModule W F 1) t =
      fibreEulerCharacteristic f F t := fun t =>
    eulerSum_congr _ _ ((Scheme.Modules.pullback (f.fiberι t)).mapIso
      (Stacks.Ample.tensorPowModuleOneIso W F))
  rwa [e, e] at h

/-- **Euler characteristics at two field-valued points of a connected base agree.** Let
`f : W ⟶ S` be flat, proper and of finite presentation over a connected `S` and `F` an invertible
module on `W`. For two field-valued points `p_i : Spec k_i ⟶ S` with base changes
`q_i : Y_i ⟶ W`, `χ(Y_1, q_1^* F) = χ(Y_2, q_2^* F)`. -/
private theorem eulerSum_eq_of_isPullback {W S : Scheme.{u}} (f : W ⟶ S) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] [ConnectedSpace S]
    (F : W.Modules) [Stacks.Ample.IsInvertibleModule W F]
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] (p₁ : Spec (.of k₁) ⟶ S) (p₂ : Spec (.of k₂) ⟶ S)
    {Y₁ Y₂ : Scheme.{u}} (q₁ : Y₁ ⟶ W) (g₁ : Y₁ ⟶ Spec (.of k₁)) (q₂ : Y₂ ⟶ W)
    (g₂ : Y₂ ⟶ Spec (.of k₂)) (h₁ : IsPullback q₁ g₁ f p₁) (h₂ : IsPullback q₂ g₂ f p₂) :
    eulerSum k₁ g₁ ((Scheme.Modules.pullback q₁).obj F) =
      eulerSum k₂ g₂ ((Scheme.Modules.pullback q₂).obj F) := by
  have hfp : FinitePresentation f :=
    ⟨inferInstance, inferInstanceAs (QuasiCompact f),
      @IsSeparated.instQuasiSeparated _ _ f IsProper.toIsSeparated⟩
  have hF : SheafOfModules.IsFinitePresentation F :=
    @Stacks.Divisors.isFinitePresentation_of_isInvertible _ F
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        W.presheaf _ _).mp ‹_›)
  have hflat := isFlatOver_of_isInvertibleModule f F
  have key : ∀ {k : Type u} [Field k] (p : Spec (.of k) ⟶ S) {Y : Scheme.{u}} (q : Y ⟶ W)
      (g : Y ⟶ Spec (.of k)) (h : IsPullback q g f p) (pt : Spec (.of k)),
      eulerSum k g ((Scheme.Modules.pullback q).obj F) = fibreEulerCharacteristic f F (p pt) := by
    intro k _ p Y q g h pt
    rw [← chiDerivedFibre_eq_eulerSum f hfp F hF hflat k p q g h pt,
      congrFun (fibreEulerCharacteristic_eq_chiDerivedFibre f hfp F hF hflat) (p pt)]
  rw [key p₁ q₁ g₁ h₁ (IsLocalRing.closedPoint k₁), key p₂ q₂ g₂ h₂ (IsLocalRing.closedPoint k₂)]
  exact fibreEulerCharacteristic_eq_of_connected f F _ _

/-- **Degrees at two field-valued points of a connected base agree.** In the situation of
`eulerSum_eq_of_isPullback`, if both base changes have dimension at most one, the degrees of
`q_i^* F` on them agree. -/
private theorem invertibleCurveDegree_eq_of_isPullback {W S : Scheme.{u}} (f : W ⟶ S) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f] [ConnectedSpace S]
    (F : W.Modules) [Stacks.Ample.IsInvertibleModule W F]
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] (p₁ : Spec (.of k₁) ⟶ S) (p₂ : Spec (.of k₂) ⟶ S)
    {Y₁ Y₂ : Scheme.{u}} (q₁ : Y₁ ⟶ W) (g₁ : Y₁ ⟶ Spec (.of k₁)) (q₂ : Y₂ ⟶ W)
    (g₂ : Y₂ ⟶ Spec (.of k₂)) (h₁ : IsPullback q₁ g₁ f p₁) (h₂ : IsPullback q₂ g₂ f p₂)
    [IsProper g₁] [IsProper g₂] (hdim₁ : topologicalKrullDim Y₁ ≤ 1)
    (hdim₂ : topologicalKrullDim Y₂ ≤ 1)
    [SheafOfModules.IsInvertible Y₁.presheaf Y₁.ringCatSheaf.2
      ((Scheme.Modules.pullback q₁).obj F)]
    [SheafOfModules.IsInvertible Y₂.presheaf Y₂.ringCatSheaf.2
      ((Scheme.Modules.pullback q₂).obj F)] :
    invertibleCurveDegree k₁ g₁ hdim₁ ((Scheme.Modules.pullback q₁).obj F) =
      invertibleCurveDegree k₂ g₂ hdim₂ ((Scheme.Modules.pullback q₂).obj F) := by
  have e₁ := eulerSum_eq_of_isPullback f F p₁ p₂ q₁ g₁ q₂ g₂ h₁ h₂
  have e₂ := eulerSum_eq_of_isPullback f (SheafOfModules.unit W.ringCatSheaf) p₁ p₂ q₁ g₁ q₂ g₂
    h₁ h₂
  have u₁ : eulerSum k₁ g₁ ((Scheme.Modules.pullback q₁).obj (SheafOfModules.unit W.ringCatSheaf)) =
      eulerSum k₁ g₁ (SheafOfModules.unit Y₁.ringCatSheaf) :=
    eulerSum_congr k₁ g₁ (Scheme.Modules.pullbackUnitIso q₁)
  have u₂ : eulerSum k₂ g₂ ((Scheme.Modules.pullback q₂).obj (SheafOfModules.unit W.ringCatSheaf)) =
      eulerSum k₂ g₂ (SheafOfModules.unit Y₂.ringCatSheaf) :=
    eulerSum_congr k₂ g₂ (Scheme.Modules.pullbackUnitIso q₂)
  rw [u₁, u₂] at e₂
  change eulerSum k₁ g₁ _ - eulerSum k₁ g₁ _ = eulerSum k₂ g₂ _ - eulerSum k₂ g₂ _
  rw [e₁, e₂]

/-- **A constant family has constant Euler characteristic.** Let `S` be a connected scheme over
`k₀`, `M` an invertible module on `X₀ ×_{k₀} S`, and `Y` a proper `k₀`-scheme with a morphism
`y : Y ⟶ X₀`. For two `k₀`-points `τ, τ'` of `S`, the Euler characteristics of the pull-backs of
`M` along `(y, τ)` and `(y, τ')` agree. -/
private theorem eulerSum_constantFamily {k₀ : Type u} [Field k₀] {S X₀ Y : Scheme.{u}}
    (gS : S ⟶ Spec (.of k₀)) (s₀ : X₀ ⟶ Spec (.of k₀)) [ConnectedSpace S]
    (M : (pullback gS s₀).Modules)
    [SheafOfModules.IsInvertible (pullback gS s₀).presheaf (pullback gS s₀).ringCatSheaf.2 M]
    (gY : Y ⟶ Spec (.of k₀)) [IsProper gY] (y : Y ⟶ X₀) (hy : y ≫ s₀ = gY)
    (τ τ' : Spec (.of k₀) ⟶ S) (hτ : τ ≫ gS = 𝟙 _) (hτ' : τ' ≫ gS = 𝟙 _) :
    eulerSum k₀ gY ((Scheme.Modules.pullback (pullback.lift (gY ≫ τ) y (by
        rw [Category.assoc, hτ, Category.comp_id, hy]))).obj M) =
      eulerSum k₀ gY ((Scheme.Modules.pullback (pullback.lift (gY ≫ τ') y (by
        rw [Category.assoc, hτ', Category.comp_id, hy]))).obj M) := by
  classical
  have hflat : Flat gY := inferInstance
  have hlf : LocallyOfFinitePresentation gY :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
      (inferInstance : IsProper gY).toLocallyOfFiniteType
  let fS : pullback gY gS ⟶ S := pullback.snd gY gS
  have hP : IsPullback (pullback.fst gY gS) fS gY gS := IsPullback.of_hasPullback gY gS
  have hfl : Flat fS := MorphismProperty.of_isPullback (P := @Flat) hP hflat
  have hpr : IsProper fS := MorphismProperty.of_isPullback (P := @IsProper) hP ‹IsProper gY›
  let w : pullback gY gS ⟶ pullback gS s₀ :=
    pullback.lift fS (pullback.fst gY gS ≫ y) (by rw [Category.assoc, hy, ← pullback.condition])
  let F : (pullback gY gS).Modules := (Scheme.Modules.pullback w).obj M
  have hFi : SheafOfModules.IsInvertible (pullback gY gS).presheaf
      (pullback gY gS).ringCatSheaf.2 F :=
    inferInstance
  haveI : Stacks.Ample.IsInvertibleModule (pullback gY gS) F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      (pullback gY gS).presheaf _ _).mpr hFi
  have key : ∀ (τ : Spec (.of k₀) ⟶ S) (hτ : τ ≫ gS = 𝟙 _),
      ∃ q : Y ⟶ pullback gY gS, IsPullback q gY fS τ ∧ q ≫ w = pullback.lift (gY ≫ τ) y (by
        rw [Category.assoc, hτ, Category.comp_id, hy]) := by
    intro τ hτ
    let q : Y ⟶ pullback gY gS := pullback.lift (𝟙 Y) (gY ≫ τ) (by
      rw [Category.assoc, hτ, Category.comp_id, Category.id_comp])
    have hq1 : q ≫ pullback.fst gY gS = 𝟙 Y := pullback.lift_fst _ _ _
    have hq2 : q ≫ fS = gY ≫ τ := pullback.lift_snd _ _ _
    have hw1 : w ≫ pullback.fst gS s₀ = fS := pullback.lift_fst _ _ _
    have hw2 : w ≫ pullback.snd gS s₀ = pullback.fst gY gS ≫ y := pullback.lift_snd _ _ _
    refine ⟨q, ?_, ?_⟩
    · refine IsPullback.of_right (h₁₁ := q) (h₁₂ := pullback.fst gY gS) (v₁₁ := gY)
        (v₁₂ := fS) (v₁₃ := gY) (h₂₁ := τ) (h₂₂ := gS) ?_ hq2 hP
      rw [hq1, hτ]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hw1, hq2, pullback.lift_fst]
      · rw [Category.assoc, hw2, ← Category.assoc, hq1, Category.id_comp, pullback.lift_snd]
  obtain ⟨q, hq, hqw⟩ := key τ hτ
  obtain ⟨q', hq', hqw'⟩ := key τ' hτ'
  have e := eulerSum_eq_of_isPullback fS F τ τ' q gY q' gY hq hq'
  have e1 := eulerSum_congr k₀ gY
    ((Scheme.Modules.pullbackComp q w).app M ≪≫ (Scheme.Modules.pullbackCongr hqw).app M)
  have e2 := eulerSum_congr k₀ gY
    ((Scheme.Modules.pullbackComp q' w).app M ≪≫ (Scheme.Modules.pullbackCongr hqw').app M)
  exact e1.symm.trans (e.trans e2)

/-- **Euler characteristics along a spread-out family.** Let `f : W ⟶ S` be a flat proper family
of finite presentation over a connected `S` over `k₀`, with a morphism `u : W ⟶ X₀` over `k₀`, and
let `M` be an invertible module on `X₀ ×_{k₀} S₁` for a connected `S₁` under `S`, with two
`k₀`-points `τ` of `S` and `τ₀` of `S₁`. For `v = (f, u) : W ⟶ X₀ ×_{k₀} S₁` and
`σ₀ = (τ₀, 𝟙) : X₀ ⟶ X₀ ×_{k₀} S₁`
the pull-backs of `M` along `v` and `u ≫ σ₀` have the same Euler characteristic on every fibre of
`f` over a field-valued point of `S`. -/
private theorem eulerSum_spread_eq {k₀ : Type u} [Field k₀] {X₀ S S₁ W C' : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (g₁ : S₁ ⟶ Spec (.of k₀)) (g : S ⟶ Spec (.of k₀)) (r : S ⟶ S₁)
    (hr : r ≫ g₁ = g) [ConnectedSpace S] [ConnectedSpace S₁]
    (M : (pullback g₁ s₀).Modules)
    [SheafOfModules.IsInvertible (pullback g₁ s₀).presheaf (pullback g₁ s₀).ringCatSheaf.2 M]
    (τ : Spec (.of k₀) ⟶ S) (hτ : τ ≫ g = 𝟙 _) (τ₀ : Spec (.of k₀) ⟶ S₁) (hτ₀ : τ₀ ≫ g₁ = 𝟙 _)
    (f : W ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f] (u : W ⟶ X₀)
    (hu : u ≫ s₀ = f ≫ g)
    (v : W ⟶ pullback g₁ s₀) (hv₁ : v ≫ pullback.fst g₁ s₀ = f ≫ r)
    (hv₂ : v ≫ pullback.snd g₁ s₀ = u)
    (σ₀ : X₀ ⟶ pullback g₁ s₀) (hσ₁ : σ₀ ≫ pullback.fst g₁ s₀ = s₀ ≫ τ₀)
    (hσ₂ : σ₀ ≫ pullback.snd g₁ s₀ = 𝟙 _)
    {k : Type u} [Field k] (p : Spec (.of k) ⟶ S) (j : C' ⟶ W) (φ : C' ⟶ Spec (.of k))
    (hpb : IsPullback j φ f p) :
    eulerSum k φ ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback v).obj M)) =
      eulerSum k φ ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback u).obj
        ((Scheme.Modules.pullback σ₀).obj M))) := by
  classical
  let F₁ : W.Modules := (Scheme.Modules.pullback v).obj M
  let F₂ : W.Modules := (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback σ₀).obj M)
  have hF₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 F₁ := inferInstance
  have hF₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 F₂ := inferInstance
  haveI : Stacks.Ample.IsInvertibleModule W F₁ :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      W.presheaf _ _).mpr hF₁
  haveI : Stacks.Ample.IsInvertibleModule W F₂ :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      W.presheaf _ _).mpr hF₂
  let Y : Scheme.{u} := pullback f τ
  let qY : Y ⟶ W := pullback.fst f τ
  let gY : Y ⟶ Spec (.of k₀) := pullback.snd f τ
  have hY : IsPullback qY gY f τ := IsPullback.of_hasPullback f τ
  have hqf : qY ≫ f = gY ≫ τ := hY.w
  have hy : (qY ≫ u) ≫ s₀ = gY := by
    rw [Category.assoc, hu, ← Category.assoc, hqf, Category.assoc, hτ, Category.comp_id]
  have e₁ := eulerSum_eq_of_isPullback f F₁ p τ j φ qY gY hpb hY
  have e₂ := eulerSum_eq_of_isPullback f F₂ p τ j φ qY gY hpb hY
  have hτ₁ : (τ ≫ r) ≫ g₁ = 𝟙 _ := by rw [Category.assoc, hr, hτ]
  have hm₁ : qY ≫ v = pullback.lift (gY ≫ (τ ≫ r)) (qY ≫ u) (by
      rw [Category.assoc, hτ₁, Category.comp_id, hy]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₁, ← Category.assoc, hqf, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, hv₂, pullback.lift_snd]
  have hm₂ : qY ≫ u ≫ σ₀ = pullback.lift (gY ≫ τ₀) (qY ≫ u) (by
      rw [Category.assoc, hτ₀, Category.comp_id, hy]) := by
    apply pullback.hom_ext
    · have hy' : qY ≫ u ≫ s₀ = gY := by rw [← Category.assoc, hy]
      rw [Category.assoc, Category.assoc, hσ₁, pullback.lift_fst, ← hy']
      simp only [Category.assoc]
    · rw [Category.assoc, Category.assoc, hσ₂, Category.comp_id, pullback.lift_snd]
  have e₃ := eulerSum_constantFamily g₁ s₀ M gY (qY ≫ u) hy (τ ≫ r) τ₀ hτ₁ hτ₀
  have c₁ := eulerSum_congr k₀ gY
    ((Scheme.Modules.pullbackComp qY v).app M ≪≫ (Scheme.Modules.pullbackCongr hm₁).app M)
  have c₂ := eulerSum_congr k₀ gY
    (((Scheme.Modules.pullbackComp qY u).app ((Scheme.Modules.pullback σ₀).obj M)) ≪≫
      (Scheme.Modules.pullbackComp (qY ≫ u) σ₀).app M ≪≫
      (Scheme.Modules.pullbackCongr (by rw [Category.assoc, hm₂])).app M)
  exact e₁.trans (c₁.trans (e₃.trans (c₂.symm.trans e₂.symm)))

end EulerAcrossPoints

/-! ### Base change of curves -/

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)

/-- The degree of a pulled-back invertible sheaf on a base change of a curve: if `Y → C₀` is the
base change of the curve `C₀` along `k₀ → K` and `Y → X` is the induced morphism, then the degree
of `π^* L` on `Y` equals the degree of `L` on `C₀`, Euler characteristics being invariant under
extension of the ground field. -/
private theorem degreeOn_baseChange {C₀ Y : Scheme.{u}} (ι₀ : C₀ ⟶ X₀) (ι : Y ⟶ X)
    (j : Y ⟶ C₀) [IsProper (ι₀ ≫ s₀)]
    (hc : ι ≫ π = j ≫ ι₀)
    (h : IsPullback j (ι ≫ s) (ι₀ ≫ s₀) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hdim : topologicalKrullDim C₀ ≤ 1) (hdim' : topologicalKrullDim Y ≤ 1)
    (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L]
    [IsProper (ι ≫ s)] :
    degreeOn K s ι hdim' ((Scheme.Modules.pullback π).obj L) = degreeOn k₀ s₀ ι₀ hdim L := by
  have e : (Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback π).obj L) ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι₀).obj L) :=
    (Scheme.Modules.pullbackComp ι π).app L ≪≫ (Scheme.Modules.pullbackCongr hc).app L ≪≫
      ((Scheme.Modules.pullbackComp j ι₀).app L).symm
  unfold degreeOn invertibleCurveDegree
  congr 1
  · refine finsum_congr fun n => ?_
    rw [finrank_cohomologyOverField_eq_of_iso K (ι ≫ s) e n,
      finrank_cohomologyOverField_baseChange_field k₀ K j (ι ≫ s) (ι₀ ≫ s₀) h _ n]
  · refine finsum_congr fun n => ?_
    have eu : SheafOfModules.unit Y.ringCatSheaf ≅
        (Scheme.Modules.pullback j).obj (SheafOfModules.unit C₀.ringCatSheaf) :=
      (Scheme.Modules.pullbackUnitIso j).symm
    have : (SheafOfModules.unit C₀.ringCatSheaf).IsQuasicoherent := inferInstance
    rw [finrank_cohomologyOverField_eq_of_iso K (ι ≫ s) eu n,
      finrank_cohomologyOverField_baseChange_field k₀ K j (ι ≫ s) (ι₀ ≫ s₀) h
        (SheafOfModules.unit C₀.ringCatSheaf) n]

variable [IsAlgClosed k₀]

/-- **Base change of curves.** Every proper curve `C₀ ⊆ X₀` has a base change, a proper curve
`C ⊆ X` with closure `π⁻¹(C₀)`, together with a morphism `a : C ⟶ C₀` over `π` exhibiting `C` as
the base change `C₀ ×_{k₀} K`. -/
private theorem exists_properCurve_isPullback
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (C₀ : ProperCurve s₀) :
    ∃ C : ProperCurve s, closure {C.point} = π.base ⁻¹' closure {C₀.point} ∧
      ∃ a : C.scheme ⟶ C₀.scheme, C.ι ≫ π = a ≫ C₀.ι ∧
        IsPullback a (C.ι ≫ s) (C₀.ι ≫ s₀) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) with hg
  set t₀ : C₀.scheme ⟶ Spec (.of k₀) := C₀.ι ≫ s₀ with ht₀
  have hpb : IsPullback (pullback.snd t₀ g) (pullback.fst t₀ g) g t₀ :=
    (IsPullback.of_hasPullback t₀ g).flip
  obtain ⟨Y, j, t, hpb⟩ : ∃ (Y : Scheme.{u}) (j : Y ⟶ C₀.scheme) (t : Y ⟶ Spec (.of K)),
      IsPullback t j g t₀ := ⟨_, _, _, hpb⟩
  have hcomm : (j ≫ C₀.ι) ≫ s₀ = t ≫ g := by
    simpa only [Category.assoc, ← ht₀] using hpb.w.symm
  set ι' : Y ⟶ X := h.lift (j ≫ C₀.ι) t hcomm with hι'
  have hι'π : ι' ≫ π = j ≫ C₀.ι := h.lift_fst _ _ _
  have hι's : ι' ≫ s = t := h.lift_snd _ _ _
  have hsq : IsPullback j ι' C₀.ι π := by
    refine (IsPullback.of_right (h₁₁ := ι') (h₁₂ := s) (h₂₁ := C₀.ι) (h₂₂ := s₀)
      (v₁₁ := j) (v₁₂ := π) (v₁₃ := g) ?_ hι'π h.flip).flip
    rwa [hι's]
  haveI : IsClosedImmersion ι' := MorphismProperty.of_isPullback hsq inferInstance
  have hproper : IsProper t₀ := C₀.isProperCurve.isProper
  haveI : IsProper t := MorphismProperty.of_isPullback hpb.flip hproper
  haveI : IrreducibleSpace C₀.scheme := inferInstance
  haveI : GeometricallyIrreducible t₀ :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k₀ C₀.scheme t₀
  haveI : GeometricallyReduced t₀ := geometricallyReduced_of_isReduced t₀
  haveI : GeometricallyIntegral t₀ :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible t₀
  haveI : GeometricallyIntegral t := MorphismProperty.of_isPullback hpb.flip inferInstance
  haveI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton t
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt ι'
  have key : e.inv ≫ ι' = curveSubschemeAtι (ι' (genericPoint Y)) :=
    (Iso.inv_comp_eq _).2 he.symm
  haveI : LocallyOfFiniteType t₀ := inferInstance
  have hdimY : topologicalKrullDim Y = topologicalKrullDim C₀.scheme :=
    topologicalKrullDim_baseChange k₀ K j t t₀ hpb.flip
  have hdimC : topologicalKrullDim (curveSubschemeAt (ι' (genericPoint Y))) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph, hdimY]
    exact C₀.dim_eq
  have hpropC : IsProper (curveSubschemeAtι (ι' (genericPoint Y)) ≫ s) := by
    have : curveSubschemeAtι (ι' (genericPoint Y)) ≫ s = e.inv ≫ t := by
      rw [← key, Category.assoc, hι's]
    rw [this]; infer_instance
  let C : ProperCurve s := ⟨ι' (genericPoint Y), ⟨hdimC, hpropC⟩⟩
  have hc : C.ι ≫ π = (e.inv ≫ j) ≫ C₀.ι := by
    change curveSubschemeAtι (ι' (genericPoint Y)) ≫ π = _
    rw [← key]; simp [hι'π]
  have hsqC : IsPullback (e.inv ≫ j) (C.ι ≫ s) (C₀.ι ≫ s₀) g := by
    refine hpb.flip.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_
      (by simp [ht₀]) (by simp)
    change e.inv ≫ t = curveSubschemeAtι (ι' (genericPoint Y)) ≫ s
    rw [← key, Category.assoc, hι's]
  refine ⟨C, ?_, e.inv ≫ j, hc, hsqC⟩
  have hrange : Set.range ι' = π ⁻¹' Set.range C₀.ι := by
    have hs : Function.Surjective hsq.isoPullback.hom :=
      (Scheme.homeoOfIso hsq.isoPullback).surjective
    rw [← hsq.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      hs.range_eq, Set.image_univ, Scheme.Pullback.range_snd]
  have he' : Function.Surjective e.inv := (Scheme.homeoOfIso e.symm).surjective
  rw [← C.range_ι, ← C₀.range_ι, ← hrange]
  change Set.range (curveSubschemeAtι (ι' (genericPoint Y))) = _
  rw [← key, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, he'.range_eq,
    Set.image_univ]

/-- **Base change of curves and degrees.** The base change `C ⊆ X` of a proper curve `C₀ ⊆ X₀`
carries every invertible sheaf pulled back from `X₀` with the degree it has on `C₀`. -/
private theorem exists_properCurve_baseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (C₀ : ProperCurve s₀) :
    ∃ C : ProperCurve s, closure {C.point} = π.base ⁻¹' closure {C₀.point} ∧
      ∀ (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L],
        C.degree K ((Scheme.Modules.pullback π).obj L) = C₀.degree k₀ L := by
  obtain ⟨C, hC, a, hc, hsq⟩ := exists_properCurve_isPullback s₀ s π h C₀
  exact ⟨C, hC, fun L _ => degreeOn_baseChange s₀ s π C₀.ι C.ι a hc hsq C₀.dim_le C.dim_le L⟩

/-- A proper curve on `X` whose closure is `π⁻¹(C₀)` has, against every invertible sheaf pulled
back from `X₀`, the degree that sheaf has on `C₀`. -/
private theorem degree_pullback_eq_of_closure_eq
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {C₀ : ProperCurve s₀} {C : ProperCurve s}
    (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point})
    (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L] :
    C.degree K ((Scheme.Modules.pullback π).obj L) = C₀.degree k₀ L := by
  obtain ⟨C', hC', hdeg⟩ := exists_properCurve_baseChange s₀ s π h C₀
  obtain rfl : C' = C := ProperCurve.ext (inseparable_iff_closure_eq.mpr (hC'.trans hC.symm)).eq
  exact hdeg L

/-- **Injectivity.** A linear map `N₁(X₀)_ℝ → N₁(X)_ℝ` sending the class of each proper curve to
the class of its base change is injective: the degree of `π^* L` on `φ z` is the degree of `L`
on `z`. -/
private theorem injective_of_map_numericalClass
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C.cycle ℝ)) :
    Function.Injective φ := by
  have hφdeg (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L]
      (Z : OneCycle ℝ s₀) :
      NumericalCurveClasses.degree s ((Scheme.Modules.pullback π).obj L)
          (φ (OneCycle.numericalClass s₀ Z)) = OneCycle.degree ℝ s₀ L Z := by
    induction Z using Finsupp.induction_linear with
    | zero => simp
    | add Z₁ Z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single C₀ a =>
      obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
      have hsingle : Finsupp.single C₀ a = a • C₀.cycle ℝ := by
        simp [ProperCurve.cycle, Finsupp.smul_single]
      rw [hsingle, map_smul, map_smul, map_smul, map_smul, hφ C₀ C hC,
        NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
        OneCycle.degree_cycle, degree_pullback_eq_of_closure_eq s₀ s π h hC L]
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective s₀ z
  change (OneCycle.numericallyTrivial s₀).mkQ Z = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, OneCycle.mem_numericallyTrivial]
  intro L _
  rw [← hφdeg L Z, LinearMap.mem_ker.mp hz, map_zero]

end BaseChange

/-! ### Degrees on curves mapping to a scheme of arbitrary type -/

section Fibre

open RingedSpaceModuleAdjunction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The degree of an invertible sheaf on a proper curve only depends on its isomorphism class. -/
private theorem degree_congr (C : ProperCurve sX) {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    C.degree k L = C.degree k L' :=
  invertibleCurveDegree_eq_of_iso k (C.ι ≫ sX) C.dim_le ((Scheme.Modules.pullback C.ι).mapIso e)

/-- The degree of a twice pulled-back invertible sheaf only depends on the composite morphism. -/
private theorem invertibleCurveDegree_pullback_pullback_eq {C A A' B : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [IsProper sC] (hdim : topologicalKrullDim C ≤ 1)
    {a : C ⟶ A} {b : A ⟶ B} {a' : C ⟶ A'} {b' : A' ⟶ B} (hab : a ≫ b = a' ≫ b')
    (M : B.Modules) [SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 M] :
    invertibleCurveDegree k sC hdim ((Scheme.Modules.pullback a).obj
        ((Scheme.Modules.pullback b).obj M)) =
      invertibleCurveDegree k sC hdim ((Scheme.Modules.pullback a').obj
        ((Scheme.Modules.pullback b').obj M)) :=
  invertibleCurveDegree_eq_of_iso k sC hdim ((Scheme.Modules.pullbackComp a b).app M ≪≫
    (Scheme.Modules.pullbackCongr hab).app M ≪≫ ((Scheme.Modules.pullbackComp a' b').app M).symm)

/-- **A contracted curve has degree zero**, for a morphism `g : X ⟶ Y` to an arbitrary scheme:
the curve maps into a trivialising open of the invertible sheaf. -/
private theorem degree_pullback_eq_zero_of_isContractedBy' (g : X ⟶ Y) (C : ProperCurve sX)
    (hC : C.IsContractedBy g) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    C.degree k ((Scheme.Modules.pullback g).obj L) = 0 := by
  obtain ⟨U, hzU, ⟨e⟩⟩ := (isInvertible_iff_exists_restrict_iso_unit Y L).mp ‹_› (g C.point)
  have hr : Set.range (C.ι ≫ g) ⊆ Set.range U.ι := by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hc : C.ι c ∈ closure ({C.point} : Set X) := C.range_ι ▸ ⟨c, rfl⟩
    change g (C.ι c) ∈ U
    rw [hC _ hc]
    exact hzU
  set ψ := IsOpenImmersion.lift U.ι (C.ι ≫ g) hr
  have hψ : ψ ≫ U.ι = C.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  let e' : (Scheme.Modules.pullback C.ι).obj ((Scheme.Modules.pullback g).obj L) ≅
      SheafOfModules.unit C.scheme.ringCatSheaf :=
    (Scheme.Modules.pullbackComp C.ι g).app L ≪≫ (Scheme.Modules.pullbackCongr hψ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp ψ U.ι).app L).symm ≪≫
      (Scheme.Modules.pullback ψ).mapIso
        (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm ≪≫ e) ≪≫
      Scheme.Modules.pullbackUnitIso ψ
  change invertibleCurveDegree k (C.ι ≫ sX) C.dim_le _ = 0
  rw [invertibleCurveDegree_eq_of_iso k _ _ e']
  exact sub_self _

/-- **A curve which is not contracted has positive degree** against an invertible sheaf on an
arbitrary scheme `Y` over `k`, provided the curve maps into an open `U` on which the sheaf is
ample: the induced morphism from the curve to `U` is proper and non-constant, hence finite. -/
private theorem degree_pullback_pos_of_not_isContractedBy {sY : Y ⟶ Spec (.of k)} (g : X ⟶ Y)
    (hg : g ≫ sY = sX) (C : ProperCurve sX) (hC : ¬ C.IsContractedBy g) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [Stacks.Ample.IsInvertibleModule Y L] (U : Y.Opens)
    (hU : ∀ x ∈ closure ({C.point} : Set X), g x ∈ U)
    (hamp : Stacks.Ample.IsAmple U.toScheme ((modulePullback U.ι.toLRSHom.toShHom).obj L)) :
    0 < C.degree k ((Scheme.Modules.pullback g).obj L) := by
  set M := (modulePullback U.ι.toLRSHom.toShHom).obj L with hM
  haveI : SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2 M :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      U.ι.toLRSHom.toShHom _ inferInstance
  have h1 : Scheme.Modules.IsAmple U.toScheme M :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hamp
  haveI : U.toScheme.IsSeparated := Scheme.Modules.IsAmple.isSeparated M h1
  have hr : Set.range (C.ι ≫ g) ⊆ Set.range U.ι := by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU _ (C.range_ι ▸ ⟨c, rfl⟩)
  set ψ := IsOpenImmersion.lift U.ι (C.ι ≫ g) hr
  have hψ : ψ ≫ U.ι = C.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hψs : ψ ≫ U.ι ≫ sY = C.ι ≫ sX := by rw [← Category.assoc, hψ, Category.assoc, hg]
  haveI : IsProper (ψ ≫ U.ι ≫ sY) := hψs ▸ inferInstance
  haveI : IsProper ψ := IsProper.of_comp ψ (U.ι ≫ sY)
  haveI := C.isCurve
  haveI : IsLocallyNoetherian C.scheme := LocallyOfFiniteType.isLocallyNoetherian (C.ι ≫ sX)
  haveI : CompactSpace C.scheme := QuasiCompact.compactSpace_of_compactSpace (C.ι ≫ sX)
  haveI : IsNoetherian C.scheme := ⟨⟩
  obtain ⟨x, hx, hne⟩ : ∃ x ∈ closure ({C.point} : Set X), g x ≠ g C.point := by
    simpa [ProperCurve.IsContractedBy] using hC
  obtain ⟨c, rfl⟩ : x ∈ Set.range C.ι := C.range_ι ▸ hx
  haveI : IsFinite ψ := by
    refine isFinite_of_isProper_of_exists_apply_ne ψ C.dim_le ⟨c, genericPoint C.scheme, ?_⟩
    intro hc
    apply hne
    have := congrArg U.ι hc
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ] at this
    simpa [C.ι_genericPoint] using this
  haveI := MMP.Mori.isInvertible_pullback_obj ψ M
  have h2 := isAmple_pullback_of_isFinite ψ M h1
  have h3 := invertibleCurveDegree_pos_of_isAmple_of_isCurve k (C.ι ≫ sX) C.dim_le _ h2
  let e : (Scheme.Modules.pullback ψ).obj M ≅
      (Scheme.Modules.pullback C.ι).obj ((Scheme.Modules.pullback g).obj L) :=
    (Scheme.Modules.pullback ψ).mapIso ((modulePullbackIsoSchemePullback U.ι).app L) ≪≫
      (Scheme.Modules.pullbackComp ψ U.ι).app L ≪≫ (Scheme.Modules.pullbackCongr hψ).app L ≪≫
      ((Scheme.Modules.pullbackComp C.ι g).app L).symm
  change 0 < invertibleCurveDegree k (C.ι ≫ sX) C.dim_le _
  rw [← invertibleCurveDegree_eq_of_iso k _ _ e]
  exact h3

end Fibre

/-! ### Descent of curve classes -/

section GeometricFibres

open CategoryTheory.Limits

/-- A property respecting isomorphisms passes along a commutative square whose horizontal
edges are isomorphisms. -/
private lemma of_isPullback_of_isIso {C : Type*} [Category C] {P : MorphismProperty C}
    [P.RespectsIso] {A B Y Z : C} {a : A ⟶ B} {p : A ⟶ Y} {q : B ⟶ Z} {e : Y ⟶ Z}
    (hsq : IsPullback a p q e) [IsIso e] (h : P p) : P q :=
  have := hsq.isIso_fst_of_isIso
  (P.arrow_mk_iso_iff (Arrow.isoMk (asIso a) (asIso e) hsq.w)).1 h

/-- The fibre of `f` at the image of `u` is a base change of the fibre of `f ∣_ U` at `u`, the
residue fields being isomorphic. -/
private lemma fiber_of_restrict {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (u : U.toScheme)
    (h : P ((f ∣_ U).fiberToSpecResidueField u)) :
    P (f.fiberToSpecResidueField (U.ι u)) :=
  of_isPullback_of_isIso
    (isPullback_fiberToSpecResidueField_of_isPullback (isPullback_morphismRestrict f U).flip u) h

/-- If `P` holds for `f ∣_ U`, it holds for the fibre of `f` over every point of `U`. -/
private lemma fiber_of_morphismRestrict {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (h : P (f ∣_ U))
    {y : Y} (hy : y ∈ U) : P (f.fiberToSpecResidueField y) :=
  fiber_of_restrict (P := P) f U ⟨y, hy⟩ (P.pullback_snd _ _ h)

/-- **Geometrically integral proper generic fibres spread** (Stacks 0559, 0578, 05F7). Let
`f : X ⟶ Spec R` be proper over a domain `R`, with geometrically integral generic fibre of
dimension `n`. There is a nonzero `r : R` such that over `D(r)` every fibre of `f` is
geometrically integral of dimension `n`. -/
private theorem exists_ne_zero_forall_geometricallyIntegral_fiber
    {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (n : ℕ)
    (hgi : GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R)))))
    (hn : topologicalKrullDim (f.fiber (genericPoint (Spec (CommRingCat.of R)))) = n) :
    ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R), r ∉ s.asIdeal →
      GeometricallyIntegral (f.fiberToSpecResidueField s) ∧
        topologicalKrullDim (f.fiber s) = n := by
  set η := genericPoint (Spec (CommRingCat.of R))
  have hη : IsGenericPoint η Set.univ := genericPoint_spec _
  obtain ⟨V₁, hV₁, hirr⟩ := geometricallyIrreducibleAfterShrinking f inferInstance inferInstance
    inferInstance η hη inferInstance
  obtain ⟨V₂, hV₂, hred⟩ :=
    exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType f η hη
  obtain ⟨V₃, hV₃, hdim⟩ := exists_nonempty_open_fiberDimension_eq f n η hη hn
  have hV : ((V₁ : Set (Spec (CommRingCat.of R))) ∩ V₂ ∩ V₃).Nonempty :=
    nonempty_preirreducible_inter (V₁.isOpen.inter V₂.isOpen) V₃.isOpen
      (nonempty_preirreducible_inter V₁.isOpen V₂.isOpen (Set.nonempty_coe_sort.1 hV₁)
        (Set.nonempty_coe_sort.1 hV₂)) hV₃
  obtain ⟨r, hr, hrV⟩ := MMP.Threefold.Bridges.exists_ne_zero_forall_mem_of_isOpen
    (R := R) _ ((V₁.isOpen.inter V₂.isOpen).inter V₃.isOpen) hV
  refine ⟨r, hr, fun s hs => ?_⟩
  obtain ⟨⟨hs₁, hs₂⟩, hs₃⟩ := hrV s hs
  have := fiber_of_morphismRestrict (P := @GeometricallyIrreducible) f V₁ hirr hs₁
  have := fiber_of_morphismRestrict (P := @GeometricallyReduced) f V₂ hred hs₂
  exact ⟨.of_geometricallyReduced_of_geometricallyIrreducible _, hdim s hs₃⟩

/-- Two field extensions of a field have a common extension. -/
private lemma exists_field_algHom_algHom (F K K' : Type u) [Field F] [Field K] [Field K']
    [Algebra F K] [Algebra F K'] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L),
      Nonempty (K →ₐ[F] L) ∧ Nonempty (K' →ₐ[F] L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct F K K')
  letI := Ideal.Quotient.field m
  exact ⟨_ ⧸ m, inferInstance, inferInstance,
    ⟨(Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeLeft⟩,
    ⟨(Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight⟩⟩

private lemma surjective_specMap_of_field {k L : Type u} [Field k] [Field L] (φ : k →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- A base change `T ×_Y X ⟶ T` is geometrically `P` as soon as `T` lands in a set of points of
`Y` over which the fibres of `X ⟶ Y` are geometrically `P`. -/
private lemma geometrically_pullback_snd_of_fibers {P : ObjectProperty Scheme.{u}}
    [P.IsClosedUnderIsomorphisms] {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (U : Set Y)
    (hg : Set.range g.base ⊆ U) (hU : ∀ y ∈ U, geometrically P (f.fiberToSpecResidueField y)) :
    geometrically P (pullback.snd f g) := by
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  set e := Scheme.SpecToEquivOfField K Y (y ≫ g) with he
  have hy : y ≫ g = Spec.map e.2 ≫ Y.fromSpecResidueField e.1 := by
    have := (Scheme.SpecToEquivOfField K Y).symm_apply_apply (y ≫ g)
    rw [← this]
    rfl
  have hsU : e.1 ∈ U := hg ⟨(y.base (IsLocalRing.closedPoint K)), rfl⟩
  refine P.prop_of_iso (pullbackLeftPullbackSndIso f g y).symm ?_
  refine P.prop_of_iso (pullback.congrHom rfl hy).symm ?_
  exact P.prop_of_iso (pullbackLeftPullbackSndIso f _ _)
    (pullback_of_geometrically (hU _ hsU) K (Spec.map e.2))

/-- **Geometric integrality is detected over an algebraically closed extension**: if
`X = Y ×_F K` is integral and `K ⊇ F` is algebraically closed, then `Y` is geometrically integral
over `F`. Reducedness passes through the perfect field `K` (Stacks 0384); irreducibility through a
common extension of `K` and any other extension of `F`. -/
private lemma geometricallyIntegral_of_isPullback {F K : Type u} [Field F] [Field K]
    [IsAlgClosed K] [Algebra F K] {Y X : Scheme.{u}} (f : Y ⟶ Spec (.of F))
    (g : X ⟶ Spec (.of K)) (p : X ⟶ Y)
    (h : IsPullback p g f (Spec.map (CommRingCat.ofHom (algebraMap F K)))) [IsIntegral X] :
    GeometricallyIntegral f := by
  have : GeometricallyReduced f := by
    rw [geometricallyReduced_iff_baseChange_fieldExtension F K f]
    have : GeometricallyReduced g := geometricallyReduced_of_isReduced g
    have hsq : IsPullback h.isoPullback.inv
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F K)))) g (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback hsq this
  have : GeometricallyIrreducible f := by
    constructor
    rw [geometrically_iff_of_isClosedUnderIsomorphisms]
    intro K' _ y
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    letI : Algebra F K' := φ.hom.toAlgebra
    obtain ⟨L, _, _, ⟨σ⟩, ⟨τ⟩⟩ := exists_field_algHom_algHom F K K'
    let σ' : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom σ.toRingHom)
    let τ' : Spec (.of L) ⟶ Spec (.of K') := Spec.map (CommRingCat.ofHom τ.toRingHom)
    have hσ : σ' ≫ Spec.map (CommRingCat.ofHom (algebraMap F K)) =
          Spec.map (CommRingCat.ofHom (algebraMap F L)) := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact σ.commutes x
    have hτ : τ' ≫ Spec.map φ = Spec.map (CommRingCat.ofHom (algebraMap F L)) := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact τ.commutes x
    have hgi := geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K X g
    have i1 : IrreducibleSpace (pullback (C := Scheme.{u}) g σ') :=
      pullback_of_geometrically hgi.1 L _
    have hP := (IsPullback.of_hasPullback g σ').paste_horiz h
    have i2 : IrreducibleSpace (pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom (algebraMap F L)))) :=
      ObjectProperty.prop_of_iso (P := fun X : Scheme.{u} => IrreducibleSpace X)
        (hP.isoPullback ≪≫ pullback.congrHom rfl hσ) i1
    have i3 : IrreducibleSpace (pullback (C := Scheme.{u}) (pullback.snd f (Spec.map φ)) τ') :=
      ObjectProperty.prop_of_iso (P := fun X : Scheme.{u} => IrreducibleSpace X)
        ((pullback.congrHom rfl hτ).symm ≪≫ (pullbackLeftPullbackSndIso f _ _).symm) i2
    have h₄ := surjective_specMap_of_field τ.toRingHom
    have : Surjective (pullback.fst (pullback.snd f (Spec.map φ)) τ') :=
      MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback (pullback.snd f (Spec.map φ)) τ').flip h₄
    exact Function.Surjective.irreducibleSpace
      (pullback.fst (pullback.snd f (Spec.map φ)) τ').continuous
      (pullback.fst (pullback.snd f (Spec.map φ)) τ').surjective
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

/-- Extending the ground field does not change the dimension. -/
private lemma geometrically_topologicalKrullDim_eq {F : Type u} [Field F] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of F)) [LocallyOfFiniteType f] :
    geometrically (fun Z : Scheme.{u} => topologicalKrullDim Z = topologicalKrullDim Y) f := by
  rw [geometrically_iff_of_commRing]
  intro K _ _ Z fst snd h
  exact topologicalKrullDim_baseChange F K fst snd f h

private lemma isClosedUnderIsomorphisms_isIntegral :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) IsIntegral :=
  ⟨fun e h => have := h; IsIntegral.of_isIso e.hom⟩

private lemma isClosedUnderIsomorphisms_topologicalKrullDim (d : WithBot ℕ∞) :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u})
      (fun X => topologicalKrullDim X = d) :=
  ⟨fun e h => by
    change topologicalKrullDim _ = d
    rwa [← (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq]⟩

/-- **Geometric integrality and dimension of the fibres of a proper model.** Let
`f : Y ⟶ Spec R` be proper over a finitely generated `k₀`-subalgebra `R ⊆ K` of an algebraically
closed field `K`, with integral base change `X'` to `K` of dimension `n`. Outside the zero set of
one nonzero element of `R` the fibres of `f` are geometrically integral of dimension `n`. -/
private lemma exists_ne_zero_geometric {k₀ K : Type u} [Field k₀] [Field K] [IsAlgClosed K]
    [Algebra k₀ K] (R : Subalgebra k₀ K) {Y X' : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] (p : X' ⟶ Y) (s : X' ⟶ Spec (.of K))
    (hps : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIntegral X']
    (n : ℕ) (hn : topologicalKrullDim X' = n) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : Spec (.of R), r ∉ y.asIdeal →
      geometrically (fun Z : Scheme.{u} => IsIntegral Z) (f.fiberToSpecResidueField y) ∧
      geometrically (fun Z : Scheme.{u} => topologicalKrullDim Z = n)
        (f.fiberToSpecResidueField y) := by
  classical
  have hlft : LocallyOfFiniteType f := inferInstance
  let κ : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  -- the point `Spec K ⟶ Spec R` factors through the generic point
  let e := Scheme.SpecToEquivOfField K (Spec (.of R)) κ
  have hκ : κ = Spec.map e.2 ≫ (Spec (.of R)).fromSpecResidueField e.1 := by
    have := (Scheme.SpecToEquivOfField K (Spec (.of R))).symm_apply_apply κ
    rw [← this]
    rfl
  have he : e.1 = genericPoint (Spec (.of R)) := by
    rw [genericPoint_eq_bot_of_affine]
    change PrimeSpectrum.comap (algebraMap R K) (IsLocalRing.closedPoint K) = ⊥
    ext r
    change algebraMap R K r ∈ IsLocalRing.maximalIdeal K ↔ r ∈ (⊥ : Ideal R)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not,
      Ideal.mem_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R K)]
  -- `X'` is the base change of the generic fibre
  letI : Algebra ((Spec (.of R)).residueField e.1) K := e.2.hom.toAlgebra
  let ρ := (Spec (.of R)).fromSpecResidueField e.1
  let q : X' ⟶ pullback f ρ := pullback.lift p (s ≫ Spec.map e.2)
    (by rw [Category.assoc, ← hκ]; exact hps.w)
  have hsq : IsPullback q s (pullback.snd f ρ)
      (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of R)).residueField e.1) K))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f _)
    have h1 : q ≫ pullback.fst f ρ = p := pullback.lift_fst _ _ _
    rw [h1]
    exact hκ ▸ hps
  have hlft' : LocallyOfFiniteType (pullback.snd f ρ) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f ρ) hlft
  have hgi : GeometricallyIntegral (f.fiberToSpecResidueField e.1) :=
    geometricallyIntegral_of_isPullback (F := (Spec (.of R)).residueField e.1) (K := K)
      (pullback.snd f ρ) s q hsq
  have hdim : topologicalKrullDim X' = topologicalKrullDim (f.fiber e.1) :=
    @topologicalKrullDim_baseChange ((Spec (.of R)).residueField e.1) K _ _ _ _ _ q
      s (pullback.snd f ρ) hsq hlft'
  obtain ⟨r, hr, H⟩ := exists_ne_zero_forall_geometricallyIntegral_fiber f n (he ▸ hgi)
    (he ▸ hdim ▸ hn)
  refine ⟨r, hr, fun y hy => ⟨(geometricallyIntegral_iff _).mp (H y hy).1, ?_⟩⟩
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (fun Z : Scheme.{u} => topologicalKrullDim Z = (n : WithBot ℕ∞)) :=
    isClosedUnderIsomorphisms_topologicalKrullDim _
  have hl : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f _) hlft
  have h₃ := @geometrically_topologicalKrullDim_eq _ _ _ (f.fiberToSpecResidueField y) hl
  rwa [(H y hy).2] at h₃

/-- The fibres of a proper model over the field-valued points outside the zero set of the element
of `exists_ne_zero_geometric` are integral of dimension `n`. -/
private lemma fibre_of_exists_ne_zero_geometric {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (r : R) (n : ℕ)
    (H : ∀ y : Spec (.of R), r ∉ y.asIdeal →
      geometrically (fun Z : Scheme.{u} => IsIntegral Z) (f.fiberToSpecResidueField y) ∧
      geometrically (fun Z : Scheme.{u} => topologicalKrullDim Z = n)
        (f.fiberToSpecResidueField y))
    (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of R))
    (ht : r ∉ (t.base (IsLocalRing.closedPoint L)).asIdeal) :
    IsIntegral (pullback (C := Scheme.{u}) f t) ∧
      topologicalKrullDim (pullback (C := Scheme.{u}) f t) = n := by
  have hU : Set.range t.base ⊆ {y : Spec (.of R) | r ∉ y.asIdeal} := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint L)]
  have := isClosedUnderIsomorphisms_isIntegral
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (fun Z : Scheme.{u} => topologicalKrullDim Z = (n : WithBot ℕ∞)) :=
    isClosedUnderIsomorphisms_topologicalKrullDim _
  have e : pullback (C := Scheme.{u}) (pullback.snd f t) (𝟙 (Spec (.of L))) ≅
      pullback (C := Scheme.{u}) f t :=
    asIso (pullback.fst (pullback.snd f t) (𝟙 (Spec (.of L))))
  have g₁ := pullback_of_geometrically
    (geometrically_pullback_snd_of_fibers f t _ hU fun y hy => (H y hy).1) L (𝟙 _)
  have g₂ := pullback_of_geometrically
    (geometrically_pullback_snd_of_fibers f t _ hU fun y hy => (H y hy).2) L (𝟙 _)
  exact ⟨ObjectProperty.prop_of_iso _ e g₁, ObjectProperty.prop_of_iso
    (fun Z : Scheme.{u} => topologicalKrullDim Z = (n : WithBot ℕ∞)) e g₂⟩

end GeometricFibres

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)

section Descent

open AlgebraicGeometry.FieldExtensionDescent CategoryTheory.Limits

omit [IsAlgClosed K] in
/-- **Descent of an invertible module to a finitely generated stage.** An invertible module `L`
on the base change `X` of the `k₀`-scheme `X₀` is, for some finitely generated `k₀`-subalgebra
`A ⊆ K`, the pull-back of an invertible module `M` on `X₀ ×_{k₀} Spec A` along the canonical
morphism `ρ : X ⟶ X₀ ×_{k₀} Spec A`. -/
private theorem exists_descent
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ (A : FGSubalgebra k₀ K)
      (M : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K))))
        s₀).Modules)
      (_ : SheafOfModules.IsInvertible
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))) s₀).presheaf
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K))))
          s₀).ringCatSheaf.2 M)
      (ρ : X ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))) s₀),
      ρ ≫ pullback.fst _ _ =
          s ≫ Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K)) ∧
        ρ ≫ pullback.snd _ _ = π ∧ Nonempty (L ≅ (Scheme.Modules.pullback ρ).obj M) := by
  have : QuasiCompact s₀ := inferInstance
  have : QuasiSeparated s₀ := inferInstance
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  have : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated s₀
  let ε : X ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀ := h.flip.isoPullback
  let LK : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀).Modules :=
    (Scheme.Modules.pullback ε.inv).obj L
  have hLK : SheafOfModules.IsInvertible
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀).presheaf
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀).ringCatSheaf.2 LK :=
    inferInstance
  obtain ⟨i, Li, hLi, ⟨e⟩⟩ := exists_isInvertible_baseChangeDiagram_pullback_iso k₀ K s₀ LK hLK
  let cA : pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) s₀ ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (i.unop : Subalgebra k₀ K)))) s₀ :=
    (baseChangeLimitCone k₀ K s₀).cone.π.app i
  refine ⟨i.unop, Li, hLi, ε.hom ≫ cA, ?_, ?_, ?_⟩
  · have h1 : cA ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (i.unop : Subalgebra k₀ K) K)) :=
      pullback.lift_fst _ _ _
    have h2 : ε.hom ≫ pullback.fst _ _ = s := h.flip.isoPullback_hom_fst
    rw [Category.assoc, h1, ← Category.assoc, h2]
  · have h1 : cA ≫ pullback.snd _ _ = pullback.snd _ _ :=
      pullback.lift_snd _ _ _
    have h2 : ε.hom ≫ pullback.snd _ _ = π := h.flip.isoPullback_hom_snd
    rw [Category.assoc, h1, h2]
  · exact ⟨((Scheme.Modules.pullbackId X).app L).symm ≪≫
      (Scheme.Modules.pullbackCongr ε.hom_inv_id.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp ε.hom ε.inv).app L).symm ≪≫
      (Scheme.Modules.pullback ε.hom).mapIso e ≪≫ (Scheme.Modules.pullbackComp ε.hom cA).app Li⟩

end Descent

section Spreading

open AlgebraicGeometry.FieldExtensionDescent CategoryTheory.Limits Opposite

open CategoryTheory.Limits in
/-- Spreading out a morphism to a scheme of finite presentation over the base. -/
private theorem exists_spread_morphism
    {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {T X₀ : Scheme.{u}} (s₀ : X₀ ⟶ T) [LocallyOfFinitePresentation s₀] [QuasiCompact s₀]
    [QuasiSeparated s₀] (t : ∀ i, D.obj i ⟶ T) (ht : ∀ {i j : I} (e : j ⟶ i), D.map e ≫ t i = t j)
    (tc : c.pt ⟶ T) (htc : ∀ i, c.π.app i ≫ t i = tc)
    (i : I) {W C : Scheme.{u}} (p : W ⟶ D.obj i) (hp : FinitePresentation p)
    (a : C ⟶ W) (φ : C ⟶ c.pt) (hpb : IsPullback a φ p (c.π.app i))
    (ψ : C ⟶ X₀) (hψ : ψ ≫ s₀ = φ ≫ tc) :
    ∃ (j : I) (e : j ⟶ i) (v : pullback p (D.map e) ⟶ X₀),
      pullback.lift a (φ ≫ c.π.app j) (by rw [hpb.w, Category.assoc, c.w e]) ≫ v = ψ ∧
      v ≫ s₀ = pullback.snd p (D.map e) ≫ t j := by
  let Z : Over (D.obj i) := Over.mk p
  let Y : Over (D.obj i) := (Over.pullback (t i)).obj (Over.mk s₀)
  have hY : FinitePresentation Y.hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd s₀ (t i))),
    inferInstanceAs (QuasiCompact (pullback.snd s₀ (t i))),
    inferInstanceAs (QuasiSeparated (pullback.snd s₀ (t i)))⟩
  let ιP := hpb.isoPullback
  have h1 : (ιP.inv ≫ ψ) ≫ s₀ = (pullback.fst p (c.π.app i) ≫ p) ≫ t i := by
    have : ιP.inv ≫ φ = pullback.snd p (c.π.app i) :=
      (Iso.inv_comp_eq _).2 hpb.isoPullback_hom_snd.symm
    have e1 : (ιP.inv ≫ ψ) ≫ s₀ = pullback.snd p (c.π.app i) ≫ tc := by
      rw [Category.assoc, hψ, ← Category.assoc, this]
    have e2 : (pullback.fst p (c.π.app i) ≫ p) ≫ t i = pullback.snd p (c.π.app i) ≫ tc := by
      rw [pullback.condition, Category.assoc, htc]
    exact e1.trans e2.symm
  let F : pullback p (c.π.app i) ⟶ pullback Y.hom (c.π.app i) :=
    pullback.lift (pullback.lift (ιP.inv ≫ ψ) (pullback.fst p (c.π.app i) ≫ p) h1)
      (pullback.snd p (c.π.app i)) (by
        change _ ≫ pullback.snd s₀ (t i) = _
        exact (pullback.lift_snd _ _ _).trans pullback.condition)
  let f : (Over.pullback (c.π.app i)).obj Z ⟶ (Over.pullback (c.π.app i)).obj Y :=
    Over.homMk F (pullback.lift_snd _ _ _)
  obtain ⟨j, e, g, α, β, hα, hβ, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc i Z Y hp hY f
  let J : C ⟶ pullback p (D.map e) :=
    pullback.lift a (φ ≫ c.π.app j) (by rw [hpb.w, Category.assoc, c.w e])
  have hJs : J ≫ pullback.snd p (D.map e) = φ ≫ c.π.app j := pullback.lift_snd _ _ _
  have hJf : J ≫ pullback.fst p (D.map e) = a := pullback.lift_fst _ _ _
  let θ : C ⟶ pullback (pullback.snd p (D.map e)) (c.π.app j) := pullback.lift J φ hJs
  have hαw := Over.w α.hom
  have hθf : θ ≫ pullback.fst ((Over.pullback (D.map e)).obj Z).hom (c.π.app j) = J :=
    pullback.lift_fst _ _ _
  have hθs : θ ≫ pullback.snd ((Over.pullback (D.map e)).obj Z).hom (c.π.app j) = φ :=
    pullback.lift_snd _ _ _
  have hθ : θ ≫ α.hom.left = ιP.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα, ← Category.assoc, hθf]
      exact hJf.trans hpb.isoPullback_hom_fst.symm
    · rw [Category.assoc]
      refine Eq.trans ?_ hpb.isoPullback_hom_snd.symm
      exact (congrArg (fun q => θ ≫ q) hαw).trans hθs
  refine ⟨j, e, g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i), ?_, ?_⟩
  · have hmf := overPullback_map_left_fst (c.π.app j) g
    have hleft : α.hom.left ≫ F = ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left :=
      congrArg Over.Hom.left hcomm
    have hFf : F ≫ pullback.fst Y.hom (c.π.app i) =
        pullback.lift (ιP.inv ≫ ψ) (pullback.fst p (c.π.app i) ≫ p) h1 := pullback.lift_fst _ _ _
    have hff : pullback.lift (ιP.inv ≫ ψ) (pullback.fst p (c.π.app i) ≫ p) h1 ≫
        pullback.fst s₀ (t i) = ιP.inv ≫ ψ := pullback.lift_fst _ _ _
    have hk : (((Over.pullback (c.π.app j)).map g).left ≫
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j)) ≫
          pullback.fst Y.hom (D.map e) =
        (((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left) ≫
          pullback.fst Y.hom (c.π.app i) := by
      rw [Category.assoc, Category.assoc, hβ]
    calc J ≫ g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i)
        = θ ≫ (pullback.fst ((Over.pullback (D.map e)).obj Z).hom (c.π.app j) ≫ g.left) ≫
            pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i) := by
          rw [← hθf]; simp only [Category.assoc]
      _ = θ ≫ ((((Over.pullback (c.π.app j)).map g).left ≫
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j)) ≫
            pullback.fst Y.hom (D.map e)) ≫ pullback.fst s₀ (t i) := by
          rw [hmf]; simp only [Category.assoc]
      _ = θ ≫ ((((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left) ≫
            pullback.fst Y.hom (c.π.app i)) ≫ pullback.fst s₀ (t i) := by rw [hk]
      _ = θ ≫ (α.hom.left ≫ F ≫ pullback.fst Y.hom (c.π.app i)) ≫ pullback.fst s₀ (t i) := by
          rw [← hleft]; simp only [Category.assoc]
      _ = (θ ≫ α.hom.left) ≫ (F ≫ pullback.fst Y.hom (c.π.app i)) ≫ pullback.fst s₀ (t i) := by
          simp only [Category.assoc]
      _ = ψ := by
          rw [hθ, hFf, hff]; simp
  · have hgw := Over.w g
    calc (g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.fst s₀ (t i)) ≫ s₀
        = g.left ≫ pullback.fst Y.hom (D.map e) ≫ pullback.snd s₀ (t i) ≫ t i := by
          rw [Category.assoc, Category.assoc, ← pullback.condition (f := s₀) (g := t i)]
      _ = g.left ≫ pullback.snd Y.hom (D.map e) ≫ D.map e ≫ t i := by
          have hc2 : pullback.fst Y.hom (D.map e) ≫ pullback.snd s₀ (t i) =
              pullback.snd Y.hom (D.map e) ≫ D.map e := pullback.condition
          rw [← Category.assoc (pullback.fst Y.hom (D.map e)), hc2]
          simp only [Category.assoc]
      _ = pullback.snd p (D.map e) ≫ t j := by
          rw [ht e, ← Category.assoc]
          exact congrArg (· ≫ t j) hgw

open CategoryTheory.Limits in
/-- A flat proper model at some stage. -/
private theorem exists_flat_proper_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i, AlgebraicGeometry.IsNoetherian (D.obj i)]
    {S' : Scheme.{u}} (φ : S' ⟶ c.pt) [Flat φ] [IsProper φ] [LocallyOfFinitePresentation φ] :
    ∃ (j : I) (W : Scheme.{u}) (p : W ⟶ D.obj j) (a : S' ⟶ W), IsPullback a φ p (c.π.app j) ∧
      Flat p ∧ IsProper p ∧ LocallyOfFinitePresentation p := by
  have hqc : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have hqs : QuasiSeparated φ := IsSeparated.instQuasiSeparated φ
  have hφfp : FinitePresentation φ :=
    ⟨‹LocallyOfFinitePresentation φ›, hqc, hqs⟩
  obtain ⟨i, Z, hZfp, hZflat, ⟨e⟩⟩ := exists_flat_model_of_small_limit D c hc φ hφfp
  have hpbC : IsPullback (e.hom.left ≫ pullback.fst Z.hom (c.π.app i)) φ Z.hom (c.π.app i) := by
    have hw : e.hom.left ≫ pullback.snd Z.hom (c.π.app i) = φ := Over.w e.hom
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e) rfl hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  have hZp : IsProper (pullback.snd Z.hom (c.π.app i)) := by
    rw [← hpbC.isoPullback_inv_snd]
    infer_instance
  have : LocallyOfFinitePresentation Z.hom := hZfp.1
  have : QuasiCompact Z.hom := hZfp.2.1
  have : QuasiSeparated Z.hom := hZfp.2.2
  have : Flat Z.hom := hZflat
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f₀ : Z ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk Z.hom (by simp)
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : IsProper ((Over.pullback (c.π.app i)).map f₀).left :=
    (overPullback_map_homMk_left_iff @IsProper Z.hom (c.π.app i)).mpr hZp
  obtain ⟨j, w, hprop⟩ := exists_isProper_baseChange_of_isLimit D c i hc Z _ f₀
  have hprop' : IsProper (pullback.snd Z.hom (D.map w)) :=
    (overPullback_map_homMk_left_iff @IsProper Z.hom (D.map w)).mp hprop
  exact ⟨j, _, pullback.snd Z.hom (D.map w), _, IsPullback.pullbackSnd_of_isLimit c w hpbC,
    inferInstance, hprop', inferInstance⟩

omit [IsAlgClosed K] in
/-- **Spreading out a proper curve.** Every proper curve `C ⊆ X` over `K` is the base change
`𝒲 ×_{Spec A} Spec K` of a flat proper family `𝒲 ⟶ Spec A` of finite presentation over a finitely
generated `k₀`-subalgebra `A ⊆ K` containing any prescribed `A₀`, together with a morphism
`u : 𝒲 ⟶ X₀` over `k₀` compatible with `π` on `C`. The family is the model of `C ⟶ Spec K` over a
stage of the cofiltered system `Spec A` (`exists_flat_model_of_small_limit`), the morphism to `X₀`
is spread out by `exists_morphism_after_baseChange`, and properness by
`exists_isProper_baseChange_of_isLimit`. -/
private theorem exists_spreading
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (A₀ : FGSubalgebra k₀ K) (C : ProperCurve s) :
    ∃ (A : FGSubalgebra k₀ K) (_ : A₀ ≤ A) (W : Scheme.{u})
      (f : W ⟶ Spec (.of (A : Subalgebra k₀ K))) (u : W ⟶ X₀)
      (j : C.scheme ⟶ W) (_ : Flat f) (_ : IsProper f) (_ : LocallyOfFinitePresentation f),
      u ≫ s₀ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K))) ∧
      CategoryTheory.IsPullback j (C.ι ≫ s) f
        (Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K))) ∧
      j ≫ u = C.ι ≫ π := by
  classical
  let D : (FGSubalgebra k₀ K)ᵒᵖ ⥤ Scheme.{u} := specDiagram k₀ K ⋙ Over.forget _
  let c : Cone D := (Over.forget _).mapCone (specLimitCone k₀ K).cone
  have hc : IsLimit c := isLimitOfPreserves _ (specLimitCone k₀ K).isLimit
  have : ∀ {i j : (FGSubalgebra k₀ K)ᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) := by
    intro i j e
    change IsAffineHom (Spec.map _)
    infer_instance
  have : ∀ i, CompactSpace (D.obj i) := fun i => by
    change CompactSpace (Spec _)
    infer_instance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  have : ∀ i, IsNoetherian (D.obj i) := fun i => by
    have : Algebra.FiniteType k₀ (i.unop : Subalgebra k₀ K) := finiteType_coe k₀ K i.unop
    have : IsNoetherianRing (i.unop : Subalgebra k₀ K) := Algebra.FiniteType.isNoetherianRing k₀ _
    change IsNoetherian (Spec (CommRingCat.of (i.unop : Subalgebra k₀ K)))
    infer_instance
  have hφp : IsProper (C.ι ≫ s) := inferInstance
  have hFl : Flat (C.ι ≫ s) := inferInstance
  have hLf : LocallyOfFinitePresentation (C.ι ≫ s) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hφp.toLocallyOfFiniteType
  obtain ⟨j₁, W₁, p₁, a₁, hpb₁, hfl₁, hpr₁, hlf₁⟩ :=
    @exists_flat_proper_model _ _ _ D c hc _ _ _ _ _ (C.ι ≫ s) hFl hφp hLf
  let k₀' := IsCofiltered.min j₁ (op A₀)
  let m := IsCofiltered.minToLeft j₁ (op A₀)
  have hpb₂ := IsPullback.pullbackSnd_of_isLimit c m hpb₁
  have hfl₂ : Flat (pullback.snd p₁ (D.map m)) := inferInstance
  have hpr₂ : IsProper (pullback.snd p₁ (D.map m)) := inferInstance
  have hlf₂ : LocallyOfFinitePresentation (pullback.snd p₁ (D.map m)) := inferInstance
  have hfp₂ : FinitePresentation (pullback.snd p₁ (D.map m)) :=
    ⟨hlf₂, instQuasiCompactOfUniversallyClosed _, IsSeparated.instQuasiSeparated _⟩
  have hψ : (C.ι ≫ π) ≫ s₀ = (C.ι ≫ s) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) := by
    rw [Category.assoc, h.w, Category.assoc]
  obtain ⟨j, e₂, v, hv₁, hv₂⟩ := exists_spread_morphism D c hc s₀
    (fun i => ((specDiagram k₀ K).obj i).hom)
    (fun e => Over.w ((specDiagram k₀ K).map e))
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    (fun i => Over.w ((specLimitCone k₀ K).cone.π.app i)) k₀' _ hfp₂ _ (C.ι ≫ s) hpb₂ (C.ι ≫ π) hψ
  have hpb₃ := IsPullback.pullbackSnd_of_isLimit c e₂ hpb₂
  have hle : A₀ ≤ j.unop := by
    refine le_trans ?_ (leOfHom e₂.unop)
    exact leOfHom (IsCofiltered.minToRight j₁ (op A₀)).unop
  have hfl₃ : Flat (pullback.snd (pullback.snd p₁ (D.map m)) (D.map e₂)) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback (pullback.snd p₁ (D.map m)) (D.map e₂)) hfl₂
  have hpr₃ : IsProper (pullback.snd (pullback.snd p₁ (D.map m)) (D.map e₂)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (pullback.snd p₁ (D.map m)) (D.map e₂)) hpr₂
  have hlf₃ : LocallyOfFinitePresentation (pullback.snd (pullback.snd p₁ (D.map m)) (D.map e₂)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback (pullback.snd p₁ (D.map m)) (D.map e₂)) hlf₂
  exact ⟨j.unop, hle, _, pullback.snd _ (D.map e₂), v, _, hfl₃, hpr₃, hlf₃, hv₂, hpb₃, hv₁⟩

omit [IsAlgClosed K] in
/-- **Spreading out a proper curve as a closed subscheme.** In `exists_spreading` the stage can
be chosen so that the morphism `(f, u) : 𝒲 ⟶ X₀ ×_{k₀} Spec A` is a closed immersion: it becomes
the closed immersion `C ⟶ X` after base change to `K`, so it is one at a finite stage
(Stacks 01ZP, `exists_isClosedImmersion_baseChange_of_isLimit`). -/
private theorem exists_spreading_closedImmersion
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C : ProperCurve s) :
    ∃ (A : FGSubalgebra k₀ K) (W : Scheme.{u})
      (f : W ⟶ Spec (.of (A : Subalgebra k₀ K))) (u : W ⟶ X₀)
      (j : C.scheme ⟶ W) (_ : Flat f) (_ : IsProper f) (_ : LocallyOfFinitePresentation f),
      u ≫ s₀ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K))) ∧
      CategoryTheory.IsPullback j (C.ι ≫ s) f
        (Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K))) ∧
      j ≫ u = C.ι ≫ π ∧
      ∀ ψ : W ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))) s₀,
        ψ ≫ pullback.fst _ _ = f → ψ ≫ pullback.snd _ _ = u → IsClosedImmersion ψ := by
  classical
  obtain ⟨A₁, -, W₁, f₁, u₁, j₁, hfl₁, hpr₁, hlf₁, hu₁, hpb₁, hju₁⟩ :=
    exists_spreading s₀ s π h hX₀ ⟨⊥, Subalgebra.fg_bot⟩ C
  let D : (FGSubalgebra k₀ K)ᵒᵖ ⥤ Scheme.{u} := specDiagram k₀ K ⋙ Over.forget _
  let c : Cone D := (Over.forget _).mapCone (specLimitCone k₀ K).cone
  have hc : IsLimit c := isLimitOfPreserves _ (specLimitCone k₀ K).isLimit
  have : ∀ {i j : (FGSubalgebra k₀ K)ᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) := by
    intro i j e
    change IsAffineHom (Spec.map _)
    infer_instance
  have : ∀ i, CompactSpace (D.obj i) := fun i => by
    change CompactSpace (Spec _)
    infer_instance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  let g₁ : Spec (.of (A₁ : Subalgebra k₀ K)) ⟶ Spec (.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (A₁ : Subalgebra k₀ K)))
  let κ₁ : Spec (.of K) ⟶ Spec (.of (A₁ : Subalgebra k₀ K)) := c.π.app (op A₁)
  have hκ : κ₁ ≫ g₁ = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) :=
    Over.w ((specLimitCone k₀ K).cone.π.app (op A₁))
  have hpb₁' : IsPullback j₁ (C.ι ≫ s) f₁ κ₁ := hpb₁
  let ψ₁ : W₁ ⟶ pullback g₁ s₀ := pullback.lift f₁ u₁ hu₁.symm
  let X₁ : Over (D.obj (op A₁)) := Over.mk f₁
  let Y₁ : Over (D.obj (op A₁)) := Over.mk (pullback.fst g₁ s₀)
  let f₀ : X₁ ⟶ Y₁ := Over.homMk ψ₁ (pullback.lift_fst _ _ _)
  -- finiteness instances
  have : IsProper (pullback.fst g₁ s₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback g₁ s₀).flip inferInstance
  have : CompactSpace X₁.left := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁.left := quasiSeparatedSpace_of_quasiSeparated f₁
  have : CompactSpace Y₁.left := QuasiCompact.compactSpace_of_compactSpace (pullback.fst g₁ s₀)
  have : QuasiSeparatedSpace Y₁.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst g₁ s₀)
  have : LocallyOfFiniteType f₀.left := by
    have : LocallyOfFiniteType (ψ₁ ≫ pullback.fst g₁ s₀) := by
      rw [pullback.lift_fst]; infer_instance
    exact LocallyOfFiniteType.of_comp this
  -- over `K`, the morphism is the closed immersion `C ⟶ X`
  let ρ : X ⟶ pullback g₁ s₀ := pullback.lift (s ≫ κ₁) π (by
    rw [Category.assoc, hκ, h.w])
  have hρ : IsPullback ρ s (pullback.fst g₁ s₀) κ₁ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd g₁ s₀) (v₁₃ := s₀) (h₂₂ := g₁) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback g₁ s₀).flip
    rw [pullback.lift_snd, hκ]
    exact h
  have hjψ : j₁ ≫ ψ₁ = C.ι ≫ ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, hpb₁'.w,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, hju₁]
  have : IsClosedImmersion ((Over.pullback (c.π.app (op A₁))).map f₀).left := by
    refine (baseChangeMap_prop_iff @IsClosedImmersion κ₁ X₁ Y₁ f₀).mp ?_
    have heq := isoPullback_hom_comp_baseChangeMap κ₁ f₀ hpb₁'.flip hρ.flip C.ι rfl hjψ.symm
    rw [← Iso.eq_inv_comp] at heq
    rw [heq]
    infer_instance
  obtain ⟨i, hi, hci⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc (op A₁) X₁ Y₁ f₀
  -- the new stage
  let r : Spec (.of (i.unop : Subalgebra k₀ K)) ⟶ Spec (.of (A₁ : Subalgebra k₀ K)) := D.map hi
  have hr : r ≫ g₁ = Spec.map (CommRingCat.ofHom (algebraMap k₀ (i.unop : Subalgebra k₀ K))) :=
    Over.w ((specDiagram k₀ K).map hi)
  let κ : Spec (.of K) ⟶ Spec (.of (i.unop : Subalgebra k₀ K)) := c.π.app i
  have hκr : κ ≫ r = κ₁ := c.w hi
  let jW : C.scheme ⟶ pullback r f₁ := pullback.lift ((C.ι ≫ s) ≫ κ) j₁ (by
    rw [Category.assoc, hκr]; exact hpb₁'.w.symm)
  have hpb : IsPullback jW (C.ι ≫ s) (pullback.fst r f₁) κ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd r f₁) (v₁₃ := f₁) (h₂₂ := r) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback r f₁).flip
    rw [pullback.lift_snd, hκr]
    exact hpb₁'
  refine ⟨i.unop, pullback r f₁, pullback.fst r f₁, pullback.snd r f₁ ≫ u₁, jW, inferInstance,
    inferInstance, inferInstance, ?_, hpb, ?_, ?_⟩
  · rw [Category.assoc, hu₁, ← Category.assoc, ← pullback.condition, Category.assoc, hr]
  · rw [← Category.assoc, pullback.lift_snd, hju₁]
  · intro ψ hψ₁ hψ₂
    have hQ : IsPullback (pullback.fst r (pullback.fst g₁ s₀))
        (pullback.snd r (pullback.fst g₁ s₀) ≫ pullback.snd g₁ s₀)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (i.unop : Subalgebra k₀ K)))) s₀ := by
      rw [← hr]
      exact (IsPullback.of_hasPullback r (pullback.fst g₁ s₀)).paste_vert
        (IsPullback.of_hasPullback g₁ s₀)
    have hcb : IsClosedImmersion (baseChangeMap r X₁ Y₁ f₀) :=
      (baseChangeMap_prop_iff @IsClosedImmersion r X₁ Y₁ f₀).mpr hci
    have hψ : ψ = baseChangeMap r X₁ Y₁ f₀ ≫ hQ.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [hψ₁, Category.assoc, hQ.isoPullback_hom_fst]
        exact (baseChangeMap_fst r X₁ Y₁ f₀).symm
      · rw [hψ₂, Category.assoc, hQ.isoPullback_hom_snd, ← Category.assoc]
        refine Eq.trans ?_
          (congrArg (· ≫ pullback.snd g₁ s₀) (baseChangeMap_snd r X₁ Y₁ f₀)).symm
        exact (congrArg (pullback.snd r f₁ ≫ ·) (pullback.lift_snd f₁ u₁ hu₁.symm)).symm.trans
          (Category.assoc _ _ _).symm
    rw [hψ]
    infer_instance

end Spreading

omit [IsAlgClosed K] in
/-- The degree of an invertible module along a curve is the difference of Euler characteristics. -/
private theorem degreeOn_eq_eulerSum {X C : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    degreeOn K sX i hdim L =
      ProperFlatFibreEulerCharacteristic.eulerSum K (i ≫ sX) ((Scheme.Modules.pullback i).obj L) -
        ProperFlatFibreEulerCharacteristic.eulerSum K (i ≫ sX)
          (SheafOfModules.unit C.ringCatSheaf) := rfl

/-- A finitely generated subalgebra of an extension of an algebraically closed field `k₀` has a
`k₀`-point: by Zariski's lemma its residue field at a maximal ideal is finite over `k₀`, hence
equal to `k₀`. -/
private theorem nonempty_algHom_fgSubalgebra (k₀ K : Type u) [Field k₀] [IsAlgClosed k₀]
    [Field K] [Algebra k₀ K] (i : AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra k₀ K) :
    Nonempty ((i : Subalgebra k₀ K) →ₐ[k₀] k₀) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (i : Subalgebra k₀ K)
  have := hm
  letI : Field ((i : Subalgebra k₀ K) ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k₀ ((i : Subalgebra k₀ K) ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k₀ m) Ideal.Quotient.mk_surjective
  have : Module.Finite k₀ ((i : Subalgebra k₀ K) ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k₀ ((i : Subalgebra k₀ K) ⧸ m)
  have : Algebra.IsIntegral k₀ ((i : Subalgebra k₀ K) ⧸ m) := Algebra.IsIntegral.of_finite _ _
  have hbij : Function.Bijective (algebraMap k₀ ((i : Subalgebra k₀ K) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k₀ ((i : Subalgebra k₀ K) ⧸ m)) hbij).symm.toAlgHom
    |>.comp (Ideal.Quotient.mkₐ k₀ m)⟩

/-- A `k₀`-point of a `k₀`-algebra `A` gives a section of `Spec A ⟶ Spec k₀`. -/
private theorem specMap_algHom_comp_algebraMap {k₀ A : Type u} [Field k₀] [CommRing A]
    [Algebra k₀ A] (t : A →ₐ[k₀] k₀) :
    Spec.map (CommRingCat.ofHom t.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) =
      𝟙 (Spec (.of k₀)) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  simp

open AlgebraicGeometry.FieldExtensionDescent CategoryTheory.Limits in
/-- Descent of a line bundle up to numerical equivalence: every invertible sheaf `L` on the base
change is numerically equivalent to the pull-back of an invertible sheaf `L₀` on `X₀`: `L`
descends to `X_A` for a finitely generated `k₀`-subalgebra `A ⊆ K`
(`FieldExtensionDescent.exists_isInvertible_baseChangeDiagram_pullback_iso`), `L₀` is its fibre at
a `k₀`-point of `Spec A`, and each curve `C ⊆ X` spreads out to a flat proper family over a larger
`A'`; the fibre Euler characteristics of `L` and of `π^* L₀` on that family agree on the
`k₀`-points (`fibreEulerCharacteristic_tensorPowModule_eq`). -/
private theorem exists_isInvertible_numerically_pullback
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ (L₀ : X₀.Modules) (hL₀ : SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L₀),
      ∀ C : ProperCurve s, degreeOn K s C.ι C.dim_le L =
        degreeOn K s C.ι C.dim_le ((Scheme.Modules.pullback π).obj L₀) := by
  classical
  obtain ⟨A₁, M, hM, ρ, hρ₁, hρ₂, ⟨eL⟩⟩ := exists_descent s₀ s π h hX₀ L
  obtain ⟨t₀⟩ := nonempty_algHom_fgSubalgebra k₀ K A₁
  let g₁ : Spec (.of (A₁ : Subalgebra k₀ K)) ⟶ Spec (.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (A₁ : Subalgebra k₀ K)))
  let τ₀ : Spec (.of k₀) ⟶ Spec (.of (A₁ : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom t₀.toRingHom)
  have hτ₀ : τ₀ ≫ g₁ = 𝟙 _ := specMap_algHom_comp_algebraMap t₀
  let σ₀ : X₀ ⟶ pullback g₁ s₀ := pullback.lift (s₀ ≫ τ₀) (𝟙 X₀) (by
    rw [Category.assoc, hτ₀, Category.comp_id, Category.id_comp])
  have hσ₁ : σ₀ ≫ pullback.fst g₁ s₀ = s₀ ≫ τ₀ := pullback.lift_fst _ _ _
  have hσ₂ : σ₀ ≫ pullback.snd g₁ s₀ = 𝟙 _ := pullback.lift_snd _ _ _
  haveI hL₀ : SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2
      ((Scheme.Modules.pullback σ₀).obj M) := inferInstance
  refine ⟨(Scheme.Modules.pullback σ₀).obj M, hL₀, fun C => ?_⟩
  obtain ⟨A, hle, W, f, u, j, hfl, hpr, hlf, hu, hpb, hju⟩ := exists_spreading s₀ s π h hX₀ A₁ C
  obtain ⟨t₁⟩ := nonempty_algHom_fgSubalgebra k₀ K A
  let gA : Spec (.of (A : Subalgebra k₀ K)) ⟶ Spec (.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (A : Subalgebra k₀ K)))
  let τ : Spec (.of k₀) ⟶ Spec (.of (A : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom t₁.toRingHom)
  have hτ : τ ≫ gA = 𝟙 _ := specMap_algHom_comp_algebraMap t₁
  let r : Spec (.of (A : Subalgebra k₀ K)) ⟶ Spec (.of (A₁ : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (show (A₁ : Subalgebra k₀ K) ≤ A from hle)).toRingHom)
  have hr : r ≫ g₁ = gA := by
    rw [← Spec.map_comp]
    congr 1
  have hr' : Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K)) ≫ r =
      Spec.map (CommRingCat.ofHom (algebraMap (A₁ : Subalgebra k₀ K) K)) := by
    rw [← Spec.map_comp]
    congr 1
  let v : W ⟶ pullback g₁ s₀ := pullback.lift (f ≫ r) u (by rw [Category.assoc, hr, hu])
  have hv₁ : v ≫ pullback.fst g₁ s₀ = f ≫ r := pullback.lift_fst _ _ _
  have hv₂ : v ≫ pullback.snd g₁ s₀ = u := pullback.lift_snd _ _ _
  have key := eulerSum_spread_eq s₀ g₁ gA r hr M τ hτ τ₀ hτ₀ f u hu v hv₁ hv₂ σ₀ hσ₁ hσ₂
    (Spec.map (CommRingCat.ofHom (algebraMap (A : Subalgebra k₀ K) K))) j (C.ι ≫ s) hpb
  have hιρ : C.ι ≫ ρ = j ≫ v := by
    apply pullback.hom_ext
    · rw [Category.assoc, hρ₁, Category.assoc, hv₁, ← Category.assoc j, hpb.w, Category.assoc,
        hr', Category.assoc]
    · rw [Category.assoc, hρ₂, Category.assoc, hv₂, hju]
  rw [degreeOn_eq_eulerSum, degreeOn_eq_eulerSum]
  congr 1
  have c₁ := ProperFlatFibreEulerCharacteristic.eulerSum_congr K (C.ι ≫ s)
    ((Scheme.Modules.pullback C.ι).mapIso eL ≪≫ (Scheme.Modules.pullbackComp C.ι ρ).app M ≪≫
      (Scheme.Modules.pullbackCongr hιρ).app M ≪≫ ((Scheme.Modules.pullbackComp j v).app M).symm)
  have c₂ := ProperFlatFibreEulerCharacteristic.eulerSum_congr K (C.ι ≫ s)
    ((Scheme.Modules.pullbackComp C.ι π).app ((Scheme.Modules.pullback σ₀).obj M) ≪≫
      (Scheme.Modules.pullbackCongr hju.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp j u).app ((Scheme.Modules.pullback σ₀).obj M)).symm)
  exact c₁.trans (key.trans c₂.symm)

open CategoryTheory.Limits in
/-- **The fibre of a closed subscheme of `S ×_T X₀` at a section of `S ⟶ T` is a closed
subscheme of `X₀`.** If `(f, u) : W ⟶ S ×_T X₀` is a closed immersion and `τ` is a section of
`g : S ⟶ T`, then `W ×_{S, τ} T ⟶ W ⟶ X₀` is a closed immersion. -/
private theorem isClosedImmersion_fibre {T S X₀ W : Scheme.{u}} (s₀ : X₀ ⟶ T) (g : S ⟶ T)
    (f : W ⟶ S) (u : W ⟶ X₀) (ψ : W ⟶ pullback g s₀)
    (hψ₁ : ψ ≫ pullback.fst _ _ = f) (hψ₂ : ψ ≫ pullback.snd _ _ = u) [IsClosedImmersion ψ]
    (τ : T ⟶ S) (hτ : τ ≫ g = 𝟙 _) :
    IsClosedImmersion (pullback.fst f τ ≫ u) := by
  -- the fibre of `ψ`
  let m : pullback f τ ⟶ pullback (pullback.fst g s₀) τ :=
    pullback.lift (pullback.fst f τ ≫ ψ) (pullback.snd f τ) (by
      rw [Category.assoc, hψ₁, pullback.condition])
  have hm : IsPullback (pullback.fst f τ) m ψ (pullback.fst (pullback.fst g s₀) τ) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd (pullback.fst g s₀) τ)
      (v₂₂ := pullback.fst g s₀) (h₃₁ := τ) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_snd, hψ₁]
    exact IsPullback.of_hasPullback f τ
  have : IsClosedImmersion m := MorphismProperty.of_isPullback hm inferInstance
  -- the fibre of `Spec A ×_{k₀} X₀` at `τ` is `X₀`
  have hP : IsPullback (pullback.fst (pullback.fst g s₀) τ ≫ pullback.snd g s₀)
      (pullback.snd (pullback.fst g s₀) τ) s₀ (𝟙 _) := by
    rw [← hτ]
    exact (IsPullback.of_hasPullback (pullback.fst g s₀) τ).paste_horiz
      (IsPullback.of_hasPullback g s₀).flip
  have : IsIso (pullback.fst (pullback.fst g s₀) τ ≫ pullback.snd g s₀) := hP.isIso_fst_of_isIso
  have he : pullback.fst f τ ≫ u =
      m ≫ pullback.fst (pullback.fst g s₀) τ ≫ pullback.snd g s₀ := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, hψ₂]
  rw [he]
  infer_instance

/-- A nonzero element of a finitely generated subalgebra of an extension of an algebraically closed
field `k₀` is nonzero at some `k₀`-point: adjoin its inverse and take a `k₀`-point of the larger
finitely generated subalgebra (Zariski's lemma). -/
private theorem exists_algHom_ne_zero {k₀ K : Type u} [Field k₀] [IsAlgClosed k₀] [Field K]
    [Algebra k₀ K] (A : AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra k₀ K)
    (b : (A : Subalgebra k₀ K)) (hb0 : b ≠ 0) :
    ∃ t : (A : Subalgebra k₀ K) →ₐ[k₀] k₀, t b ≠ 0 := by
  have hbK : (b : K) ≠ 0 := fun h => hb0 (Subtype.ext h)
  let A' : AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra k₀ K :=
    ⟨(A : Subalgebra k₀ K) ⊔ Algebra.adjoin k₀ {((b : K))⁻¹},
      A.2.sup ⟨{((b : K))⁻¹}, by simp⟩⟩
  have hbA : (b : K) ∈ (A' : Subalgebra k₀ K) := (le_sup_left : (A : Subalgebra k₀ K) ≤ _) b.2
  have hbi : ((b : K))⁻¹ ∈ (A' : Subalgebra k₀ K) :=
    (le_sup_right : Algebra.adjoin k₀ {((b : K))⁻¹} ≤ (A' : Subalgebra k₀ K))
      (Algebra.subset_adjoin rfl)
  obtain ⟨t'⟩ := nonempty_algHom_fgSubalgebra k₀ K A'
  refine ⟨t'.comp (Subalgebra.inclusion (le_sup_left : (A : Subalgebra k₀ K) ≤ _)), ?_⟩
  intro h0
  have hmul : (⟨(b : K), hbA⟩ : (A' : Subalgebra k₀ K)) * ⟨((b : K))⁻¹, hbi⟩ = 1 :=
    Subtype.ext (mul_inv_cancel₀ hbK)
  have := congrArg t' hmul
  rw [map_mul, map_one] at this
  have h00 : t' ⟨(b : K), hbA⟩ = 0 := h0
  rw [h00, zero_mul] at this
  exact zero_ne_one this

/-- The degree along a curve is unchanged by an isomorphism of the curve. -/
private theorem degreeOn_iso {k : Type u} [Field k] {X₀ Y C₀ : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k)) (ι₀ : C₀ ⟶ X₀) (e : Y ≅ C₀) {i : Y ⟶ X₀} (hi : e.hom ≫ ι₀ = i)
    [IsProper (ι₀ ≫ s₀)] [IsProper (i ≫ s₀)] (hdim : topologicalKrullDim C₀ ≤ 1)
    (hdim' : topologicalKrullDim Y ≤ 1) (L : X₀.Modules)
    [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L] :
    degreeOn k s₀ i hdim' L = degreeOn k s₀ ι₀ hdim L := by
  subst hi
  have hsq : IsPullback e.hom ((e.hom ≫ ι₀) ≫ s₀) (ι₀ ≫ s₀)
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [← degreeOn_baseChange (K := k) s₀ s₀ (𝟙 X₀) ι₀ (e.hom ≫ ι₀) e.hom
    (by rw [Category.comp_id]) hsq hdim hdim' L]
  exact degreeOn_eq_of_iso k s₀ (e.hom ≫ ι₀) hdim' ((Scheme.Modules.pullbackId X₀).app L).symm

open CategoryTheory.Limits in
/-- **A curve on `X` specialises to a curve on `X₀` with the same degrees.** For every proper
curve `C` on the base change `X` there is a proper curve `C₀` on `X₀` such that pull-backs of
invertible sheaves on `X₀` have the same degree on `C` as on `C₀`. Spread `C` out to a flat proper
closed subscheme `𝒲 ⊆ X₀ ×_{k₀} Spec A`; its fibre at a `k₀`-point of `Spec A` where the fibres
are geometrically integral curves is `C₀`, and degrees are constant in the flat family `𝒲`. -/
private theorem exists_properCurve_degreeOn_pullback_eq
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C : ProperCurve s) :
    ∃ C₀ : ProperCurve s₀, ∀ (L₀ : X₀.Modules)
      [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L₀],
      degreeOn K s C.ι C.dim_le ((Scheme.Modules.pullback π).obj L₀) =
        degreeOn k₀ s₀ C₀.ι C₀.dim_le L₀ := by
  classical
  obtain ⟨A, W, f, u, j, hfl, hpr, hlf, hu, hpb, hju, hψ⟩ :=
    exists_spreading_closedImmersion s₀ s π h hX₀ C
  -- over `D(r)` the fibres are integral curves; pick a `k₀`-point `τ` there
  haveI : IsIntegral C.scheme := isIntegral_of_irreducibleSpace_of_isReduced C.scheme
  obtain ⟨r, hr, H⟩ := exists_ne_zero_geometric (A : Subalgebra k₀ K) f j (C.ι ≫ s) hpb 1
    (by rw [C.dim_eq]; rfl)
  obtain ⟨t, ht⟩ := exists_algHom_ne_zero A r hr
  let τ : Spec (.of k₀) ⟶ Spec (.of (A : Subalgebra k₀ K)) :=
    Spec.map (CommRingCat.ofHom t.toRingHom)
  have hτ := specMap_algHom_comp_algebraMap t
  have hτr : r ∉ (τ.base (IsLocalRing.closedPoint k₀)).asIdeal := by
    show r ∉ Ideal.comap t.toRingHom (IsLocalRing.closedPoint k₀).asIdeal
    rwa [show (IsLocalRing.closedPoint k₀).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot,
      Ideal.mem_comap, Ideal.mem_bot]
  obtain ⟨hYint, hYdim⟩ := fibre_of_exists_ne_zero_geometric f r 1 H k₀ τ hτr
  -- the fibre `Y` at `τ` is a closed subscheme of `X₀`, hence a proper curve `C₀`
  let y : pullback f τ ⟶ X₀ := pullback.fst f τ ≫ u
  haveI := hψ _ (pullback.lift_fst f u hu.symm) (pullback.lift_snd f u hu.symm)
  haveI : IsClosedImmersion y := isClosedImmersion_fibre s₀ _ f u _
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) τ hτ
  have hY : IsPullback (pullback.fst f τ) (y ≫ s₀) f τ := by
    rw [Category.assoc, hu, ← Category.assoc, pullback.condition, Category.assoc, hτ,
      Category.comp_id]
    exact IsPullback.of_hasPullback f τ
  haveI : IsProper (y ≫ s₀) := MorphismProperty.of_isPullback hY hpr
  haveI : IsIntegral (pullback f τ) := hYint
  obtain ⟨C₀, e, he⟩ := exists_properCurve_of_isClosedImmersion s₀ y (by rw [hYdim]; rfl)
  refine ⟨C₀, fun L₀ _ => ?_⟩
  -- degrees are constant in the flat family `𝒲`
  haveI : Stacks.Ample.IsInvertibleModule W ((Scheme.Modules.pullback u).obj L₀) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      W.presheaf _ _).mpr inferInstance
  calc degreeOn K s C.ι C.dim_le ((Scheme.Modules.pullback π).obj L₀)
      = invertibleCurveDegree K (C.ι ≫ s) C.dim_le
          ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback u).obj L₀)) :=
        invertibleCurveDegree_eq_of_iso K _ _ ((Scheme.Modules.pullbackComp C.ι π).app L₀ ≪≫
          (Scheme.Modules.pullbackCongr hju.symm).app L₀ ≪≫
          ((Scheme.Modules.pullbackComp j u).app L₀).symm)
    _ = invertibleCurveDegree k₀ (y ≫ s₀) hYdim.le ((Scheme.Modules.pullback
          (pullback.fst f τ)).obj ((Scheme.Modules.pullback u).obj L₀)) :=
        invertibleCurveDegree_eq_of_isPullback f _ _ τ j _ _ _ hpb hY C.dim_le hYdim.le
    _ = degreeOn k₀ s₀ y hYdim.le L₀ :=
        invertibleCurveDegree_eq_of_iso k₀ _ _ ((Scheme.Modules.pullbackComp _ u).app L₀)
    _ = degreeOn k₀ s₀ C₀.ι C₀.dim_le L₀ := degreeOn_iso s₀ C₀.ι e he C₀.dim_le hYdim.le L₀

end BaseChange

/-- **Integral curve classes descend along algebraically closed base extension.** For
algebraically closed fields `k₀ → K`, a projective variety `X₀` over `k₀` and a base change
`X = X₀ ×_{k₀} K` with projection `π`, every proper curve `C` on `X` has, against every
invertible sheaf `L` on `X`, the same degree as the base change `(C₀)_K` of some proper curve
`C₀` on `X₀`; here `(C₀)_K` is the proper curve of `X` whose closure is
`π⁻¹(closure C₀)`. -/
@[mmp "lem_oai4_numerical_extension_b"]
public theorem exists_properCurve_degree_eq_of_isPullback
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C : ProperCurve s) :
    ∃ (C₀ : ProperCurve s₀) (C₀K : ProperCurve s),
      closure {C₀K.point} = π.base ⁻¹' closure {C₀.point} ∧
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        C₀K.degree K L = C.degree K L := by
  obtain ⟨C₀, hC₀⟩ := exists_properCurve_degreeOn_pullback_eq s₀ s π h hX₀ C
  obtain ⟨C₀K, hcl, j₀, hc₀, hpbK⟩ := exists_properCurve_isPullback s₀ s π h C₀
  refine ⟨C₀, C₀K, hcl, fun L _ => ?_⟩
  -- degrees: reduce to pull-backs of invertible sheaves on `X₀`
  obtain ⟨L₀, hL₀, hdeg⟩ := exists_isInvertible_numerically_pullback s₀ s π h hX₀ L
  rw [ProperCurve.degree, ProperCurve.degree, hdeg, hdeg, hC₀,
    degreeOn_baseChange s₀ s π C₀.ι C₀K.ι j₀ hc₀ hpbK C₀.dim_le C₀K.dim_le L₀]

/-! ### Pull-back of Cartier divisors along a dominant morphism -/

section SheafPullback

open MMP.Intersection
open MMP.CartierDivisorSheaf Opposite
  TopologicalSpace

section KModel

variable {X : Scheme.{u}} [IsIntegral X]

private noncomputable def ιK (U : X.Opens) :
    X.functionField →+* X.totalQuotientSheaf.obj.obj (op U) :=
  ((functionFieldToTotalQuotientSheaf X).app (op U)).hom

private theorem genericPoint_mem {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U := by
  obtain ⟨x, hx⟩ := hU
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ _, hx⟩

private theorem ιK_germ (U : X.Opens) (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    ιK U (X.presheaf.germ U (genericPoint X) h a) = toK U a :=
  functionFieldToTotalQuotientSheaf_germ X U a h

private theorem ιK_res {U V : X.Opens} (h : V ≤ U) (c : X.functionField) :
    resK h (ιK U c) = ιK V c :=
  (congrArg (fun φ => φ.hom c)
    ((functionFieldToTotalQuotientSheaf X).naturality (homOfLE h).op)).symm

private theorem ιK_injective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Injective (ιK U) :=
  functionFieldToTotalQuotientSheaf_app_injective X U hU

private theorem ιK_surjective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ιK U) := by
  intro s
  have : Nonempty U := hU.to_subtype
  obtain ⟨a, ha⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U inferInstance
    (((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U)) s)
  refine ⟨a, ?_⟩
  change ((totalQuotientSheafIsoConstant X).val.inv.hom.app (op U))
    (((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)) a) = s
  rw [← ha]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.hom_inv_id) s

end KModel

section Dominant

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

private theorem functionFieldMap_germ (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U))
    (hY : genericPoint Y ∈ g ⁻¹ᵁ U) :
    functionFieldMap g (X.presheaf.germ U (genericPoint X) hU a) =
      Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hY (g.app U a) := by
  have hx : g (genericPoint Y) ∈ U := hY
  have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g (genericPoint Y)
    (X.presheaf.germ U (g (genericPoint Y)) hx a)
  have hn : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hn' : Nonempty (g ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hY⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a] at h1
  erw [Scheme.Hom.germ_stalkMap_apply g U (genericPoint Y) hx a] at h1
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := g ⁻¹ᵁ U) hY _] at h1
  exact h1

end Dominant

section LocalFraction

variable {Z : Scheme.{u}}

private theorem exists_common_rep (x : Z) (a b : Z.presheaf.stalk x) :
    ∃ (U : Z.Opens) (hx : x ∈ U) (A B : Γ(Z, U)),
      Z.presheaf.germ U x hx A = a ∧ Z.presheaf.germ U x hx B = b := by
  obtain ⟨U₁, hx₁, A₁, rfl⟩ := Z.presheaf.exists_germ_eq a
  obtain ⟨U₂, hx₂, B₂, rfl⟩ := Z.presheaf.exists_germ_eq b
  refine ⟨U₁ ⊓ U₂, ⟨hx₁, hx₂⟩, Z.presheaf.map (homOfLE inf_le_left).op A₁,
    Z.presheaf.map (homOfLE inf_le_right).op B₂, ?_, ?_⟩
  · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem exists_local_fraction {D : Z.CartierDivisor} {x : Z} {U : Z.Opens} (hxU : x ∈ U)
    (A B : Γ(Z, U)) {e : Z.totalQuotientSheaf.presheaf.stalk x} (he : IsLocalEquationAt D x e)
    (hf : IsFraction e (Z.presheaf.germ U x hxU A) (Z.presheaf.germ U x hxU B)) :
    ∃ (U₀ : Z.Opens) (h₀ : U₀ ≤ U) (_ : x ∈ U₀) (f : (Z.totalQuotientSheaf.obj.obj (op U₀))ˣ),
      IsLocalEquationOn D U₀ f ∧
      toK U₀ (Z.presheaf.map (homOfLE h₀).op B) * (f : Z.totalQuotientSheaf.obj.obj (op U₀)) =
        toK U₀ (Z.presheaf.map (homOfLE h₀).op A) := by
  obtain ⟨U₁, hx₁, f₁, hf₁, rfl⟩ := he
  have h2 := hf.2
  rw [← germ_toTotalQuotient, ← germ_toTotalQuotient] at h2
  have hxW : x ∈ U ⊓ U₁ := ⟨hxU, hx₁⟩
  have e : Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
      (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) * resK inf_le_right (f₁ : _)) =
      Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
        (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := by
    rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    exact h2
  obtain ⟨U₀, hx₀, i, j, hij⟩ := Z.totalQuotientSheaf.presheaf.germ_eq x hxW hxW _ _ e
  have hij' : i = j := Subsingleton.elim _ _
  subst hij'
  refine ⟨U₀, i.le.trans inf_le_left, hx₀, MMP.Intersection.resUnit (i ≫ homOfLE inf_le_right) f₁,
    isLocalEquationOn_resUnit _ hf₁, ?_⟩
  have h3 : resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) *
      resK inf_le_right (f₁ : _)) =
        resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := hij
  rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A, resK_resK, resK_resK,
    resK_resK] at h3
  rw [← resK_toK _ B, ← resK_toK _ A]
  convert h3 using 2
  rfl

end LocalFraction

section Rho

private theorem subsingleton_totalQuotient_of_not_nonempty {Z : Scheme.{u}} {U : Z.Opens}
    (h : ¬ (U : Set Z).Nonempty) : Subsingleton (Z.totalQuotientSheaf.obj.obj (op U)) := by
  have : U = ⊥ := TopologicalSpace.Opens.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
  subst this
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.totalQuotientSheaf)

private def trivRingHom (R S : Type*) [CommRing R] [CommRing S] [Subsingleton S] : R →+* S where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

omit [IsIntegral X] [IsIntegral Y] [IsDominant g] in
private theorem not_nonempty_preimage {U : X.Opens} (h : ¬ (U : Set X).Nonempty) :
    ¬ ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  rintro ⟨y, hy⟩
  exact h ⟨g y, hy⟩

private theorem nonempty_preimage {U : X.Opens} (h : (U : Set X).Nonempty) :
    ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  have hη : genericPoint X ∈ U := genericPoint_mem h
  refine ⟨genericPoint Y, ?_⟩
  change g (genericPoint Y) ∈ U
  rwa [map_genericPoint_of_isDominant g]

open Classical in
/-- The ring map `𝓜_X(U) → 𝓜_Y(g⁻¹U)` induced by the extension of function fields. -/
private noncomputable def rho (U : X.Opens) :
    X.totalQuotientSheaf.obj.obj (op U) →+* Y.totalQuotientSheaf.obj.obj (op (g ⁻¹ᵁ U)) :=
  if hU : (U : Set X).Nonempty then
    (ιK (g ⁻¹ᵁ U)).comp ((functionFieldMap g).comp
      (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm.toRingHom)
  else
    haveI := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    trivRingHom _ _

private theorem rho_ιK {U : X.Opens} (hU : (U : Set X).Nonempty) (κ : X.functionField) :
    rho g U (ιK U κ) = ιK (g ⁻¹ᵁ U) (functionFieldMap g κ) := by
  unfold rho
  simp only [hU, ↓reduceDIte, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm (ιK U κ) =
      κ :=
    (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm_apply_apply κ
  rw [this]

private theorem rho_res {U V : X.Opens} (h : V ≤ U) (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    resK (g.preimage_mono h) (rho g U σ) = rho g V (resK h σ) := by
  by_cases hV : (V : Set X).Nonempty
  · have hU : (U : Set X).Nonempty := hV.mono h
    obtain ⟨κ, rfl⟩ := ιK_surjective U hU σ
    rw [rho_ιK g hU, ιK_res h, ιK_res (g.preimage_mono h), rho_ιK g hV]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hV)
    exact Subsingleton.elim _ _

private theorem rho_toK (U : X.Opens) (a : Γ(X, U)) :
    rho g U (toK U a) = toK (g ⁻¹ᵁ U) (g.app U a) := by
  by_cases hU : (U : Set X).Nonempty
  · have hη : genericPoint X ∈ U := genericPoint_mem hU
    have hY : genericPoint Y ∈ g ⁻¹ᵁ U := genericPoint_mem (nonempty_preimage g hU)
    rw [← ιK_germ U hη a, rho_ιK g hU, functionFieldMap_germ g U hη a hY, ιK_germ _ hY]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    exact Subsingleton.elim _ _

end Rho

section Key

private theorem exists_common_rep_le {Z : Scheme.{u}} (x : Z) (W : Z.Opens) (hxW : x ∈ W)
    (a b : Z.presheaf.stalk x) :
    ∃ (U : Z.Opens) (_ : U ≤ W) (hx : x ∈ U) (A B : Γ(Z, U)),
      Z.presheaf.germ U x hx A = a ∧ Z.presheaf.germ U x hx B = b := by
  obtain ⟨U, hx, A, B, h1, h2⟩ := exists_common_rep x a b
  refine ⟨U ⊓ W, inf_le_right, ⟨hx, hxW⟩, Z.presheaf.map (homOfLE inf_le_left).op A,
    Z.presheaf.map (homOfLE inf_le_left).op B, ?_, ?_⟩
  · rw [← h1]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · rw [← h2]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem mul_left_cancel_totalQuotient {Z : Scheme.{u}} [IsIntegral Z] {V : Z.Opens}
    (hV : (V : Set Z).Nonempty) {B x y : Z.totalQuotientSheaf.obj.obj (op V)} (hB : B ≠ 0)
    (h : B * x = B * y) : x = y := by
  obtain ⟨x', rfl⟩ := ιK_surjective V hV x
  obtain ⟨y', rfl⟩ := ιK_surjective V hV y
  obtain ⟨B', rfl⟩ := ιK_surjective V hV B
  have hB' : B' ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
  have h' : B' * x' = B' * y' := ιK_injective V hV (by simpa only [map_mul] using h)
  rw [mul_left_cancel₀ hB' h']

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

/-- Local equations of a pull-back are the pulled-back local equations. -/
private theorem exists_local_pullback_equation {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (y : Y) (W : X.Opens) (hW : g y ∈ W) :
    ∃ (U₀ : X.Opens) (_ : U₀ ≤ W) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U₀) (_ : y ∈ V)
      (f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ) (f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ),
      IsLocalEquationOn E U₀ f₀ ∧ IsLocalEquationOn E' V f' ∧
        resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
          (f' : Y.totalQuotientSheaf.obj.obj (op V)) := by
  obtain ⟨a, b, ⟨e, he, hf⟩, -, hb, e', he', hf'⟩ := h.2 y
  obtain ⟨U, hUW, hxU, A, B, rfl, rfl⟩ := exists_common_rep_le (g y) W hW a b
  obtain ⟨U₀, h₀, hx₀, f₀, hf₀, hAB⟩ := exists_local_fraction hxU A B he hf
  have hyU₀ : y ∈ g ⁻¹ᵁ U₀ := hx₀
  set A₀ := X.presheaf.map (homOfLE h₀).op A with hA₀
  set B₀ := X.presheaf.map (homOfLE h₀).op B with hB₀
  have hgA : X.presheaf.germ U₀ (g y) hx₀ A₀ = X.presheaf.germ U (g y) hxU A :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgB : X.presheaf.germ U₀ (g y) hx₀ B₀ = X.presheaf.germ U (g y) hxU B :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hfr : IsFraction e' (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ A₀))
      (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ B₀)) := by
    rw [← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀, ← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀,
      hgA, hgB]
    exact hf'
  obtain ⟨V, h₁, hy₁, f', hf'', hAB'⟩ := exists_local_fraction hyU₀ _ _ he' hfr
  refine ⟨U₀, h₀.trans hUW, V, h₁, hy₁, f₀, f', hf₀, hf'', ?_⟩
  have hne : toK V (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) ≠ 0 := by
    intro h0
    have h1 : Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀) = 0 :=
      MMP.Intersection.injective_toTotalQuotient V (by rw [h0, map_zero])
    have h2 : Y.presheaf.germ V y hy₁ (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) =
        (g.stalkMap y).hom (X.presheaf.germ U (g y) hxU B) := by
      erw [TopCat.Presheaf.germ_res_apply]
      rw [← hgB]
      exact (Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀ B₀).symm
    rw [h1, map_zero] at h2
    rw [← h2] at hb
    exact zero_notMem_nonZeroDivisors hb
  have e1 := congrArg (fun t => resK h₁ (rho g U₀ t)) hAB
  simp only [map_mul] at e1
  rw [rho_toK, rho_toK, resK_toK, resK_toK] at e1
  exact mul_left_cancel_totalQuotient ⟨y, hy₁⟩ hne (e1.trans hAB'.symm)

private theorem resK_rho_inv {U₀ : X.Opens} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U₀)
    {f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ} {f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ}
    (hff : resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (f' : Y.totalQuotientSheaf.obj.obj (op V))) :
    resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (↑f'⁻¹ : Y.totalQuotientSheaf.obj.obj (op V)) := by
  have hinv : resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) *
      (f' : Y.totalQuotientSheaf.obj.obj (op V)) = 1 := by
    rw [← hff, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  exact Units.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])

/-- The pull-back of a section of `𝒪_X(E)` over `W` is a section of `𝒪_Y(E')` over `g⁻¹W`. -/
private theorem mem_rho {E : X.CartierDivisor} {E' : Y.CartierDivisor} (h : IsPullback g E E')
    (W : X.Opens) (s : X.totalQuotientSheaf.obj.obj (op W)) (hs : Mem E W s) :
    Mem E' (g ⁻¹ᵁ W) (rho g W s) := by
  refine Mem.of_locally fun y hy => ?_
  obtain ⟨U₀, hU₀, V, hV, hyV, f₀, f', hf₀, hf', hff⟩ := exists_local_pullback_equation g h y W hy
  refine ⟨V, hV.trans (g.preimage_mono hU₀), hyV, ?_⟩
  refine (mem_iff (U := V) (V := V) hf' le_rfl _).2 ?_
  obtain ⟨C, hC⟩ := (mem_iff (U := U₀) (V := U₀) hf₀ le_rfl _).1 (hs.res hU₀)
  refine ⟨Y.presheaf.map (homOfLE hV).op (g.app U₀ C), ?_⟩
  have e1 : resK (hV.trans (g.preimage_mono hU₀)) (rho g W s) =
      resK hV (rho g U₀ (resK hU₀ s)) := by
    rw [← rho_res g hU₀ s, resK_resK]
  rw [e1, ← hC, map_mul, map_mul, rho_toK, resK_toK]
  simp only [resK_id]
  rw [resK_rho_inv g hV hff]

open Opposite in
private theorem epi_of_surjective_on_covering {Z : Scheme.{u}} (B : Z.Opens → Prop)
    (hB : ∀ (U : Z.Opens) (T : CategoryTheory.Sieve U),
      (∀ ⦃V : Z.Opens⦄ (f : V ⟶ U), B V → T f) → T ∈ Opens.grothendieckTopology Z U)
    {M N : Z.Modules} (φ : M ⟶ N)
    (hφ : ∀ V : Z.Opens, B V → Function.Surjective (φ.val.app (op V))) : Epi φ := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map φ).hom :=
    ⟨fun s => hB _ _ fun V f hV => hφ V hV (N.val.map f.op s)⟩
  exact (SheafOfModules.toSheaf Z.ringCatSheaf).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- The map `𝒪_X(E) ⟶ g_* 𝒪_Y(E')`, `s ↦ g^*s`. -/
private noncomputable def lambdaPre {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    (MMP.CartierDivisor.sheaf E).val ⟶
      ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')).val :=
    (PresheafOfModules.homMk
      { app := fun U => AddCommGrpCat.ofHom
          { toFun := fun s => (⟨rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s),
              mem_rho g h U.unop _ (show ↥((MMP.CartierDivisor.sheafSubmodule E).obj U) from s).2⟩ :
                ↥((MMP.CartierDivisor.sheafSubmodule E').obj (op (g ⁻¹ᵁ U.unop))))
            map_zero' := Subtype.ext (by change rho g U.unop 0 = 0; exact map_zero _)
            map_add' := fun s t => Subtype.ext (by
              exact map_add (rho g U.unop) _ _) }
        naturality := fun {U V} i => by
          ext s
          exact Subtype.ext (rho_res g i.unop.le _).symm }
      (fun U r s => Subtype.ext (by
        change rho g U.unop (toK U.unop r * MMP.CartierDivisorSheaf.sectionVal s) =
          toK (g ⁻¹ᵁ U.unop) (g.app U.unop r) *
            rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s)
        rw [map_mul]
        exact congrArg (· * rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s))
          (rho_toK g U.unop r))))

private noncomputable def lambdaHom {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    MMP.CartierDivisor.sheaf E ⟶ (Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E') :=
  (SheafOfModules.fullyFaithfulForget _).preimage (lambdaPre g h)

private theorem lambdaHom_val {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') : (lambdaHom g h).val = lambdaPre g h :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage
    (show (SheafOfModules.forget X.ringCatSheaf).obj (MMP.CartierDivisor.sheaf E) ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj
        ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')) from lambdaPre g h)

private theorem sectionVal_lambdaHom_app {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (U : X.Opens) (s : Γ(MMP.CartierDivisor.sheaf E, U)) :
    MMP.CartierDivisorSheaf.sectionVal ((lambdaHom g h).app U s) =
      rho g U (MMP.CartierDivisorSheaf.sectionVal s) := by
  have := congrArg (fun φ => φ.app (op U) s) (lambdaHom_val g h)
  exact congrArg MMP.CartierDivisorSheaf.sectionVal this

end Key

/-- The pull-back of `𝒪_X(D)` along a dominant morphism of integral schemes is `𝒪_Y(D')` for
`D'` a pull-back of `D`. -/
private theorem nonempty_pullback_sheaf_iso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g]
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D') :
    Nonempty ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D) ≅
      MMP.CartierDivisor.sheaf D') := by
  have hinvpb : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D)) :=
    SheafOfModules.isInvertible_pullback g _
  let ℓ := lambdaHom g hD'
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let ψ : (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D) ⟶
      MMP.CartierDivisor.sheaf D' := (adj.homEquiv _ _).symm ℓ
  have hψ : ∀ (U : X.Opens) (s : Γ(MMP.CartierDivisor.sheaf D, U)),
      ψ.app (g ⁻¹ᵁ U) ((adj.unit.app (MMP.CartierDivisor.sheaf D)).app U s) =
        ℓ.app U s := by
    have h1 : ℓ = adj.unit.app (MMP.CartierDivisor.sheaf D) ≫
        (Scheme.Modules.pushforward g).map ψ := by
      have := (adj.homEquiv _ _).apply_symm_apply ℓ
      rw [Adjunction.homEquiv_unit] at this
      exact this.symm
    exact fun U s => (congrArg (fun φ => φ.app U s) h1).symm
  have hepi : Epi ψ := by
    refine epi_of_surjective_on_covering
      (fun V : Y.Opens => Function.Surjective (ψ.app V)) ?_ ψ (fun V hV => hV)
    intro U T hT
    rw [Opens.mem_grothendieckTopology]
    intro y hy
    obtain ⟨U₀, -, V₀, hV₀, hyV₀, f₀, f', hf₀, hf', hff⟩ :=
      exists_local_pullback_equation g hD' y ⊤ trivial
    refine ⟨V₀ ⊓ U, homOfLE inf_le_right, hT (homOfLE inf_le_right) ?_, ⟨hyV₀, hy⟩⟩
    have hVV₀ : V₀ ⊓ U ≤ V₀ := inf_le_left
    intro t
    have hmem : Mem D' (V₀ ⊓ U) (MMP.CartierDivisorSheaf.sectionVal t) :=
      (show ↥((MMP.CartierDivisor.sheafSubmodule D').obj (op (V₀ ⊓ U))) from t).2
    obtain ⟨a, ha⟩ := (mem_iff (U := V₀) (V := V₀ ⊓ U) hf' hVV₀ _).1 hmem
    let e₀ : Γ(MMP.CartierDivisor.sheaf D, U₀) :=
      (⟨(↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀)), mem_inv hf₀⟩ :
        ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op U₀)))
    let ε := (adj.unit.app (MMP.CartierDivisor.sheaf D)).app U₀ e₀
    refine ⟨a • ((Scheme.Modules.pullback g).obj
      (MMP.CartierDivisor.sheaf D)).presheaf.map
        (homOfLE (hVV₀.trans hV₀)).op ε, ?_⟩
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    rw [Scheme.Modules.Hom.app_smul]
    have nat := PresheafOfModules.naturality_apply ψ.val (homOfLE (hVV₀.trans hV₀)).op ε
    have h4 := nat.trans (congrArg
      ((MMP.CartierDivisor.sheaf D').val.map (homOfLE (hVV₀.trans hV₀)).op)
      (hψ U₀ e₀))
    have h3 : MMP.CartierDivisorSheaf.sectionVal
        (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (MMP.CartierDivisor.sheaf D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) =
        resK (hVV₀.trans hV₀) (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) := by
      have h5 := congrArg MMP.CartierDivisorSheaf.sectionVal h4
      refine h5.trans ?_
      exact congrArg (resK (hVV₀.trans hV₀)) (sectionVal_lambdaHom_app g hD' U₀ e₀)
    change toK (V₀ ⊓ U) a * MMP.CartierDivisorSheaf.sectionVal
      (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (MMP.CartierDivisor.sheaf D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) = _
    rw [h3, ← ha, ← resK_resK hVV₀ hV₀, resK_rho_inv g hV₀ hff]
  exact ⟨@asIso _ _ _ _ ψ (Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible ψ hinvpb
    inferInstance)⟩

end SheafPullback

/-! ### Numerical classes under base change -/

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)

omit [IsAlgClosed K] in
/-- The base change of a projective variety over an algebraically closed field is integral, and
the projection to the original is surjective, hence dominant. -/
private theorem isIntegral_and_isDominant_of_isPullback
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) : IsIntegral X ∧ IsDominant π := by
  have hv : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  haveI : IsIntegral X₀ := hv.toIsIntegral
  haveI : IrreducibleSpace X₀ := inferInstance
  haveI : IsReduced X₀ := inferInstance
  haveI : GeometricallyIrreducible s₀ :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k₀ X₀ s₀
  haveI : GeometricallyReduced s₀ := geometricallyReduced_of_isReduced s₀
  haveI : GeometricallyIntegral s₀ :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible s₀
  haveI : GeometricallyIntegral s := MorphismProperty.of_isPullback h inferInstance
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
    have : (algebraMap k₀ K).FaithfullyFlat := by
      rw [RingHom.faithfullyFlat_algebraMap_iff]; infer_instance
    exact ((flat_and_surjective_SpecMap_iff _).2 this).2
  haveI : Surjective π := MorphismProperty.of_isPullback h.flip hsurj
  exact ⟨GeometricallyIntegral.isIntegral_of_subsingleton s, inferInstance⟩

/-- For `q : Y ⟶ X` flat with `X` integral and `Y` locally Noetherian, every associated point of
`Y` lies over the generic point of `X`: on affine charts an associated prime of `Γ(Y, V)` is the
annihilator of some `b ≠ 0`, and flatness makes `b` torsion-free over `Γ(X, U)`, so the
contracted prime is zero. -/
private theorem map_eq_genericPoint_of_mem_schemeAssociatedPoints {Y X : Scheme.{u}} (q : Y ⟶ X)
    [Flat q] [IsIntegral X] [IsLocallyNoetherian Y] (y : Y)
    (hy : y ∈ Stacks.Divisors.schemeAssociatedPoints Y) :
    q y = genericPoint X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (q ⁻¹ᵁ U).isOpen
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  have : Nonempty U := ⟨⟨q y, hx⟩⟩
  let φ := (q.appLE U V hVU).hom
  let _ : Algebra Γ(X, U) Γ(Y, V) := φ.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, V) := q.flat_appLE hU hV hVU
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  have hp :=
    (AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      (SheafOfModules.unit Y.ringCatSheaf) V hV hyV).mpr hy
  change IsAssociatedPrimeStacks Γ(Y, V) Γ(Y, V) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal at hp
  obtain ⟨hprime, b, hb⟩ := hp
  have hb0 : b ≠ 0 := by
    intro hh
    apply hprime.one_notMem
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    simp [hh]
  have hpbot : (hU.primeIdealOf ⟨q y, hx⟩).asIdeal = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    have ha' : φ a ∈ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
      have hnat := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hyV
      rw [← hnat] at ha
      exact ha
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot] at ha'
    change φ a * b = 0 at ha'
    have hz : a • (b : Γ(Y, V)) = 0 := ha'
    exact (smul_eq_zero.mp hz).resolve_right hb0
  have hη : genericPoint X ∈ U :=
    (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr (by simpa using ‹Nonempty U›)
  have heq : hU.primeIdealOf ⟨q y, hx⟩ = hU.primeIdealOf ⟨genericPoint X, hη⟩ := by
    apply PrimeSpectrum.ext
    rw [hpbot, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  simpa only [hU.fromSpec_primeIdealOf] using congrArg hU.fromSpec heq

/-- Every Cartier divisor on `X₀` has a pull-back along the flat base change `π`. -/
private theorem exists_isPullback
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (D₀ : X₀.CartierDivisor) : ∃ D : X.CartierDivisor, MMP.Intersection.IsPullback π D₀ D := by
  have hv : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  have : IsIntegral X₀ := hv.toIsIntegral
  have hft : LocallyOfFiniteType s₀ := inferInstance
  have hg : Flat (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Flat π := MorphismProperty.of_isPullback h.flip hg
  have hfts : LocallyOfFiniteType s := MorphismProperty.of_isPullback h hft
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian s₀
  refine MMP.Intersection.exists_isPullback fun η hη => ?_
  rw [map_eq_genericPoint_of_mem_schemeAssociatedPoints π η hη]
  have : IsArtinianRing (X₀.presheaf.stalk (genericPoint X₀)) :=
    (inferInstance : IsArtinianRing X₀.functionField)
  exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing D₀ _

omit [IsAlgClosed K] in
/-- **Base change of a proper curve.** Every proper curve `C₀ ⊆ X₀` has a base change, a proper
curve `C ⊆ X` whose closure is `π⁻¹(C₀)`, and base change preserves intersection numbers: for
every Cartier divisor `E₀` on `X₀` with pull-back `E` along `π`, `(C · E) = (C₀ · E₀)`. -/
private theorem exists_properCurve_closure_eq_and_intersectionNumber_eq
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) :
    ∃ C : ProperCurve s, closure {C.point} = π.base ⁻¹' closure {C₀.point} ∧
      ∀ (E₀ : X₀.CartierDivisor) (E : X.CartierDivisor), MMP.Intersection.IsPullback π E₀ E →
        (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
          (C₀.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E₀) := by
  have : IsIntegral X₀ := hX₀.toIsVariety.toIsIntegral
  obtain ⟨_, _⟩ := isIntegral_and_isDominant_of_isPullback s₀ s π h hX₀
  obtain ⟨C, hcl, j, hc, hpbK⟩ := exists_properCurve_isPullback s₀ s π h C₀
  refine ⟨C, hcl, fun E₀ E hE => ?_⟩
  have e : (Scheme.Modules.pullback π).obj (MMP.CartierDivisor.sheaf E₀) ≅
      MMP.CartierDivisor.sheaf E := (nonempty_pullback_sheaf_iso π hE).some
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.intersectionNumber_ofCartier,
    OneCycle.cartierDegree, OneCycle.cartierDegree, OneCycle.degree_cycle,
    OneCycle.degree_cycle]
  norm_cast
  unfold ProperCurve.degree
  rw [← degreeOn_eq_of_iso K s C.ι C.dim_le e]
  exact degreeOn_baseChange s₀ s π C₀.ι C.ι j hc hpbK C₀.dim_le C.dim_le _

end BaseChange

section Transpose

variable {k₀ K : Type u} [Field k₀] [Field K] {X₀ X : Scheme.{u}}
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}

/-- On an integral scheme a real 1-cycle is numerically trivial if and only if its intersection
number with every `ℝ`-Cartier divisor vanishes. -/
private theorem mem_numericallyTrivial_iff_forall_intersectionNumber [IsIntegral X]
    (Z : OneCycle ℝ s) :
    Z ∈ OneCycle.numericallyTrivial s ↔ ∀ D : KCartierDivisor ℝ X, Z.intersectionNumber D = 0 := by
  refine ⟨fun hZ D => OneCycle.intersectionNumber_eq_zero_of_mem hZ D, fun hZ => ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero]
  refine numericalPairing_flip_injective s ?_
  rw [map_zero]
  exact Submodule.linearMap_qext _ (LinearMap.ext hZ)

/-- If a map `β` on proper curves and a map `p` on Cartier divisors preserve the intersection
numbers `(C · D)`, then so do their linear extensions to real 1-cycles and `ℝ`-Cartier divisors. -/
private theorem intersectionNumber_lmapDomain (p : X₀.CartierDivisor → X.CartierDivisor)
    (β : ProperCurve s₀ → ProperCurve s)
    (hβ : ∀ C₀ D₀, ((β C₀).cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ (p D₀)) =
      (C₀.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ D₀))
    (Z₀ : OneCycle ℝ s₀) (c₀ : KCartierDivisor ℝ X₀) :
    OneCycle.intersectionNumber (Finsupp.lmapDomain ℝ ℝ β Z₀) (Finsupp.lmapDomain ℝ ℝ p c₀) =
      Z₀.intersectionNumber c₀ := by
  have : (OneCycle.intersectionPairing (sX := s)).compl₁₂ (Finsupp.lmapDomain ℝ ℝ p)
      (Finsupp.lmapDomain ℝ ℝ β) = OneCycle.intersectionPairing := by
    ext D₀ C₀
    simpa [OneCycle.intersectionNumber, ProperCurve.cycle, KCartierDivisor.ofCartier] using
      hβ C₀ D₀
  exact LinearMap.congr_fun₂ this c₀ Z₀

/-- If an isomorphism `e : N¹(X₀)_ℝ ≃ N¹(X)_ℝ` sends the class of each Cartier divisor `D₀` to the
class of `p D₀`, then every `ℝ`-Cartier divisor on `X` is numerically equivalent to the image of
an `ℝ`-Cartier divisor on `X₀` under the linear extension of `p`. -/
private theorem exists_numericalDivisorClass_eq_lmapDomain
    (p : X₀.CartierDivisor → X.CartierDivisor)
    (e : NumericalDivisorClasses s₀ ≃ₗ[ℝ] NumericalDivisorClasses s)
    (he : ∀ D₀, e (numericalDivisorClass s₀ (KCartierDivisor.ofCartier ℝ D₀)) =
      numericalDivisorClass s (KCartierDivisor.ofCartier ℝ (p D₀)))
    (D : KCartierDivisor ℝ X) :
    ∃ c₀, numericalDivisorClass s D = numericalDivisorClass s (Finsupp.lmapDomain ℝ ℝ p c₀) := by
  have hcomp : e.toLinearMap ∘ₗ numericalDivisorClass s₀ =
      numericalDivisorClass s ∘ₗ Finsupp.lmapDomain ℝ ℝ p := by
    ext D₀
    simpa [KCartierDivisor.ofCartier] using he D₀
  obtain ⟨c₀, hc₀⟩ := (numericallyTrivialDivisors s₀).mkQ_surjective
    (e.symm (numericalDivisorClass s D))
  refine ⟨c₀, ?_⟩
  rw [← LinearMap.comp_apply (numericalDivisorClass s), ← hcomp]
  exact (congrArg e hc₀).trans (e.apply_symm_apply _) |>.symm

/-- **Transposes detect numerical triviality.** Let `Ψ` on real 1-cycles be the transpose of `Φ` on
`ℝ`-Cartier divisors under the intersection pairing, `(Ψ Z₀ · Φ c₀) = (Z₀ · c₀)`, and let every
`ℝ`-Cartier divisor on `X` be numerically equivalent to some `Φ c₀`. On integral schemes, `Ψ Z₀`
is then numerically trivial exactly when `Z₀` is. -/
private theorem map_mem_numericallyTrivial_iff [IsIntegral X₀] [IsIntegral X]
    (Φ : KCartierDivisor ℝ X₀ →ₗ[ℝ] KCartierDivisor ℝ X) (Ψ : OneCycle ℝ s₀ →ₗ[ℝ] OneCycle ℝ s)
    (hΨ : ∀ Z₀ c₀, (Ψ Z₀).intersectionNumber (Φ c₀) = Z₀.intersectionNumber c₀)
    (hΦ : ∀ D, ∃ c₀, numericalDivisorClass s D = numericalDivisorClass s (Φ c₀))
    (Z₀ : OneCycle ℝ s₀) :
    Ψ Z₀ ∈ OneCycle.numericallyTrivial s ↔ Z₀ ∈ OneCycle.numericallyTrivial s₀ := by
  simp only [mem_numericallyTrivial_iff_forall_intersectionNumber]
  refine ⟨fun hZ c₀ => hΨ Z₀ c₀ ▸ hZ (Φ c₀), fun hZ D => ?_⟩
  obtain ⟨c₀, hc₀⟩ := hΦ D
  have := congrArg (numericalPairing s · (OneCycle.numericalClass s (Ψ Z₀))) hc₀
  simp only [numericalPairing_apply] at this
  rw [this, hΨ, hZ]

/-- A linear map into `N₁(X)_ℝ` whose range contains the class of every proper curve is
surjective. -/
private theorem surjective_of_forall_numericalClass_mem_range {M : Type*} [AddCommGroup M]
    [Module ℝ M] (T : M →ₗ[ℝ] NumericalCurveClasses s)
    (hT : ∀ C : ProperCurve s, OneCycle.numericalClass s (C.cycle ℝ) ∈ LinearMap.range T) :
    Function.Surjective T := by
  intro z
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective s z
  suffices OneCycle.numericalClass s Z ∈ LinearMap.range T from this
  induction Z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | single C r =>
    rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul]
    exact Submodule.smul_mem _ r (hT C)

private theorem comp_numericalClass_eq_lmapDomain
    (T : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (β : ProperCurve s₀ → ProperCurve s)
    (hT : ∀ C₀, T (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) =
      OneCycle.numericalClass s ((β C₀).cycle ℝ)) :
    T ∘ₗ OneCycle.numericalClass s₀ = OneCycle.numericalClass s ∘ₗ Finsupp.lmapDomain ℝ ℝ β := by
  refine Finsupp.lhom_ext fun C₀ r => ?_
  simpa [ProperCurve.cycle, ← map_smul, Finsupp.smul_single] using congrArg (r • ·) (hT C₀)

/-- A linear map carrying the curve classes of `X₀` onto those of `X` carries `NE(X₀)` onto
`NE(X)`. -/
private theorem map_coneOfCurves_eq (T : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hT : T '' Set.range (fun C₀ : ProperCurve s₀ => OneCycle.numericalClass s₀ (C₀.cycle ℝ)) =
      Set.range fun C : ProperCurve s => OneCycle.numericalClass s (C.cycle ℝ)) :
    (coneOfCurves s₀).map T = coneOfCurves s := by
  unfold coneOfCurves PointedCone.map
  rw [Submodule.map_span]
  exact congrArg _ hT

end Transpose

section CurveBaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)

/-- A chosen base change of a proper curve `C₀` on `X₀`: a proper curve of `X` whose closure is
`π⁻¹(closure C₀)`. -/
private noncomputable def baseChangeProperCurve
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) : ProperCurve s :=
  (exists_properCurve_closure_eq_and_intersectionNumber_eq s₀ s π h hX₀ C₀).choose

private theorem closure_baseChangeProperCurve
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) :
    closure {(baseChangeProperCurve s₀ s π h hX₀ C₀).point} = π.base ⁻¹' closure {C₀.point} :=
  (exists_properCurve_closure_eq_and_intersectionNumber_eq s₀ s π h hX₀ C₀).choose_spec.1

private theorem intersectionNumber_baseChangeProperCurve
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀)
    (E₀ : X₀.CartierDivisor) (E : X.CartierDivisor) (hE : MMP.Intersection.IsPullback π E₀ E) :
    ((baseChangeProperCurve s₀ s π h hX₀ C₀).cycle ℝ).intersectionNumber
        (KCartierDivisor.ofCartier ℝ E) =
      (C₀.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E₀) :=
  (exists_properCurve_closure_eq_and_intersectionNumber_eq s₀ s π h hX₀ C₀).choose_spec.2 E₀ E hE

/-- The base change of `C₀` is the only proper curve of `X` with closure `π⁻¹(closure C₀)`. -/
private theorem baseChangeProperCurve_eq
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) (C : ProperCurve s)
    (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
    baseChangeProperCurve s₀ s π h hX₀ C₀ = C :=
  ProperCurve.ext (inseparable_iff_closure_eq.mpr
    ((closure_baseChangeProperCurve s₀ s π h hX₀ C₀).trans hC.symm)).eq

/-- Base extension of curves preserves and reflects numerical triviality of real 1-cycles. -/
private theorem lmapDomain_baseChangeProperCurve_mem_numericallyTrivial_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (Z₀ : OneCycle ℝ s₀) :
    Finsupp.lmapDomain ℝ ℝ (baseChangeProperCurve s₀ s π h hX₀) Z₀ ∈
        OneCycle.numericallyTrivial s ↔ Z₀ ∈ OneCycle.numericallyTrivial s₀ := by
  have : IsIntegral X₀ := hX₀.toIsVariety.toIsIntegral
  have : IsIntegral X := (isIntegral_and_isDominant_of_isPullback s₀ s π h hX₀).1
  choose p hp using exists_isPullback s₀ s π h hX₀
  exact map_mem_numericallyTrivial_iff _ _
    (intersectionNumber_lmapDomain p _ fun C₀ D₀ =>
      intersectionNumber_baseChangeProperCurve s₀ s π h hX₀ C₀ D₀ (p D₀) (hp D₀))
    (exists_numericalDivisorClass_eq_lmapDomain p (numericalDivisorClassesBaseChange s₀ s π h hX₀)
      fun D₀ => numericalDivisorClassesBaseChange_eq_of_isPullback s₀ s π h hX₀ D₀ (p D₀) (hp D₀))
    Z₀

/-- The linear map `N₁(X₀)_ℝ → N₁(X)_ℝ` induced by base extension of curves along `π`. -/
private noncomputable def numericalCurveClassesBaseChangeMap
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s :=
  (OneCycle.numericallyTrivial s₀).mapQ (OneCycle.numericallyTrivial s)
    (Finsupp.lmapDomain ℝ ℝ (baseChangeProperCurve s₀ s π h hX₀)) fun Z hZ =>
      (lmapDomain_baseChangeProperCurve_mem_numericallyTrivial_iff s₀ s π h hX₀ Z).2 hZ

private theorem numericalCurveClassesBaseChangeMap_numericalClass
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) :
    numericalCurveClassesBaseChangeMap s₀ s π h hX₀ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) =
      OneCycle.numericalClass s ((baseChangeProperCurve s₀ s π h hX₀ C₀).cycle ℝ) := by
  simp [numericalCurveClassesBaseChangeMap, OneCycle.numericalClass, ProperCurve.cycle]

private theorem bijective_numericalCurveClassesBaseChangeMap
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    Function.Bijective (numericalCurveClassesBaseChangeMap s₀ s π h hX₀) := by
  have hiff := lmapDomain_baseChangeProperCurve_mem_numericallyTrivial_iff s₀ s π h hX₀
  have hinj : Function.Injective (numericalCurveClassesBaseChangeMap s₀ s π h hX₀) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, numericalCurveClassesBaseChangeMap, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hiff Z).1 hx)
  refine ⟨hinj, surjective_of_forall_numericalClass_mem_range _ fun C => ?_⟩
  obtain ⟨C₀, C₀K, hcl, hdeg⟩ := exists_properCurve_degree_eq_of_isPullback s₀ s π h hX₀ C
  refine ⟨_, (numericalCurveClassesBaseChangeMap_numericalClass s₀ s π h hX₀ C₀).trans ?_⟩
  rw [baseChangeProperCurve_eq s₀ s π h hX₀ C₀ C₀K hcl, OneCycle.numericalClass_eq_iff]
  intro L _
  rw [OneCycle.degree_cycle, OneCycle.degree_cycle, hdeg L]

/-- The base-extension isomorphism `N₁(X₀)_ℝ ≃ₗ[ℝ] N₁(X)_ℝ` of numerical curve classes along an
algebraically closed base extension `X = X₀ ×_{k₀} K`, induced by sending each proper curve `C₀`
on `X₀` to its base change, the proper curve of `X` whose closure is `π⁻¹(closure C₀)`. -/
@[no_expose] public noncomputable def numericalCurveClassesBaseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    NumericalCurveClasses s₀ ≃ₗ[ℝ] NumericalCurveClasses s :=
  LinearEquiv.ofBijective (numericalCurveClassesBaseChangeMap s₀ s π h hX₀)
    (bijective_numericalCurveClassesBaseChangeMap s₀ s π h hX₀)

end CurveBaseChange

/-- **Numerical curve classes are unchanged by algebraically closed base extension.** For
algebraically closed fields `k₀ → K`, a projective variety `X₀` over `k₀` and a base change
`X = X₀ ×_{k₀} K` with projection `π`, the `ℝ`-linear isomorphism
`numericalCurveClassesBaseChange : N₁(X₀)_ℝ ≃ N₁(X)_ℝ` sends the class of every proper curve `C₀`
on `X₀` to the class of its base change, the proper curve `C` on `X` whose closure is
`π⁻¹(closure C₀)`. -/
@[mmp "lem_oai4_numerical_extension_c"]
public theorem numericalCurveClassesBaseChange_eq_of_isPullback
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C₀ : ProperCurve s₀) (C : ProperCurve s)
    (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
    numericalCurveClassesBaseChange s₀ s π h hX₀ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) =
      OneCycle.numericalClass s (C.cycle ℝ) := by
  rw [← baseChangeProperCurve_eq s₀ s π h hX₀ C₀ C hC, numericalCurveClassesBaseChange,
    LinearEquiv.ofBijective_apply, numericalCurveClassesBaseChangeMap_numericalClass]

/-! ### The numerical topology -/

section Topology

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

/-- The intersection form `z ↦ (z · D)` of an `ℝ`-Cartier divisor is continuous for the
numerical topology. -/
private theorem continuous_intersectionNumber (D : KCartierDivisor ℝ Y) :
    Continuous (NumericalCurveClasses.intersectionNumber (sX := sY) D) := by
  have h (D : KCartierDivisor ℝ Y) : NumericalCurveClasses.intersectionNumber D =
      numericalPairing sY (numericalDivisorClass sY D) :=
    Submodule.linearMap_qext _ rfl
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [h, map_zero, map_zero]
    exact continuous_const
  | add a b ha hb =>
    rw [h, map_add, map_add, ← h, ← h]
    exact ha.add hb
  | single E r =>
    rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, h, map_smul, map_smul, ← h]
    rw [show Finsupp.single E 1 = KCartierDivisor.ofCartier ℝ E from rfl,
      NumericalCurveClasses.intersectionNumber_ofCartier]
    exact (NumericalCurveClasses.continuous_degree sY _).const_smul r

/-- On an integral scheme, a map into `N₁(Y)_ℝ` is continuous for the numerical topology as soon
as its composites with the intersection forms of Cartier divisors are continuous. -/
private theorem continuous_of_forall_intersectionNumber [IsIntegral Y] {W : Type*}
    [TopologicalSpace W] (f : W → NumericalCurveClasses sY)
    (hf : ∀ E : Y.CartierDivisor,
      Continuous fun w => NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E)
        (f w)) :
    Continuous f := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun _ => continuous_induced_rng.2 ?_
  obtain ⟨E, ⟨e⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf L
  have hdeg : NumericalCurveClasses.degree sY L =
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) := by
    rw [NumericalCurveClasses.intersectionNumber_ofCartier]
    refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
    change OneCycle.degree ℝ sY L Z = OneCycle.degree ℝ sY _ Z
    rw [OneCycle.degree, OneCycle.degree]
    congr 2
    funext C
    exact congrArg _ (degreeOn_eq_of_iso k sY C.ι C.dim_le e)
  change Continuous fun w => NumericalCurveClasses.degree sY L (f w)
  simpa only [hdeg] using hf E

/-- Numerically equivalent `ℝ`-Cartier divisors have the same intersection form on `N₁`. -/
private theorem intersectionNumber_eq_of_numericalDivisorClass_eq {D D' : KCartierDivisor ℝ Y}
    (h : numericalDivisorClass sY D = numericalDivisorClass sY D') :
    NumericalCurveClasses.intersectionNumber (sX := sY) D =
      NumericalCurveClasses.intersectionNumber D' :=
  Submodule.linearMap_qext _ (LinearMap.ext fun Z =>
    congrArg (numericalPairing sY · (OneCycle.numericalClass sY Z)) h)

end Topology

section Homeomorph

variable {k₀ K : Type u} [Field k₀] [Field K] {X₀ X : Scheme.{u}}
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}

/-- **A transpose of divisor pull-back is a homeomorphism.** Let `e : N₁(X₀)_ℝ ≃ N₁(X)_ℝ` be
transpose to a map `Φ` on `ℝ`-Cartier divisors, `(Φ c₀ · e z) = (c₀ · z)`, and let every
`ℝ`-Cartier divisor on `X` be numerically equivalent to some `Φ c₀`. On integral schemes, `e` is
a homeomorphism for the numerical topologies. -/
private theorem isHomeomorph_of_intersectionNumber_transpose [IsIntegral X₀] [IsIntegral X]
    (e : NumericalCurveClasses s₀ ≃ₗ[ℝ] NumericalCurveClasses s)
    (Φ : KCartierDivisor ℝ X₀ → KCartierDivisor ℝ X)
    (he : ∀ c₀ z, NumericalCurveClasses.intersectionNumber (Φ c₀) (e z) =
      NumericalCurveClasses.intersectionNumber c₀ z)
    (hΦ : ∀ D, ∃ c₀, numericalDivisorClass s D = numericalDivisorClass s (Φ c₀)) :
    IsHomeomorph e := by
  have hfwd : Continuous e := continuous_of_forall_intersectionNumber s e fun E => by
    obtain ⟨c₀, hc₀⟩ := hΦ (KCartierDivisor.ofCartier ℝ E)
    simpa only [intersectionNumber_eq_of_numericalDivisorClass_eq s hc₀, he] using
      continuous_intersectionNumber s₀ c₀
  have hinv : Continuous e.symm := continuous_of_forall_intersectionNumber s₀ e.symm fun E₀ => by
    simpa only [← he, e.apply_symm_apply] using
      continuous_intersectionNumber s (Φ (KCartierDivisor.ofCartier ℝ E₀))
  exact (⟨e.toEquiv, hfwd, hinv⟩ : NumericalCurveClasses s₀ ≃ₜ NumericalCurveClasses s).isHomeomorph

end Homeomorph

/-- **Cones of curves are unchanged by algebraically closed base extension.** Take algebraically
closed fields `k₀ → K`, a projective variety `X₀` over `k₀`, and a base change
`X = X₀ ×_{k₀} K` with projection `π`. Let `φ : N₁(X₀)_ℝ → N₁(X)_ℝ` be the linear map induced
by base extension of curves, that is, `φ [C₀] = [C₀']` whenever `C₀'` is the proper curve of
`X` with closure `π⁻¹(closure C₀)`. Then `φ` maps `NE̅(X₀)` onto `NE̅(X)`. -/
@[mmp "lem_oai4_numerical_extension_d"]
public theorem map_closedConeOfCurves_eq_of_isPullback
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C₀' : ProperCurve s),
      closure {C₀'.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C₀'.cycle ℝ)) :
    (closedConeOfCurves s₀).map φ = closedConeOfCurves s := by
  have : IsIntegral X₀ := hX₀.toIsVariety.toIsIntegral
  have : IsIntegral X := (isIntegral_and_isDominant_of_isPullback s₀ s π h hX₀).1
  choose β hβc hβ using exists_properCurve_closure_eq_and_intersectionNumber_eq s₀ s π h hX₀
  choose p hp using exists_isPullback s₀ s π h hX₀
  let e := numericalCurveClassesBaseChange s₀ s π h hX₀
  have he := numericalCurveClassesBaseChange_eq_of_isPullback s₀ s π h hX₀
  let eD := numericalDivisorClassesBaseChange s₀ s π h hX₀
  have heD := numericalDivisorClassesBaseChange_eq_of_isPullback s₀ s π h hX₀
  have hΨ := comp_numericalClass_eq_lmapDomain e.toLinearMap β fun C₀ => he C₀ _ (hβc C₀)
  obtain rfl : φ = e.toLinearMap := Submodule.linearMap_qext _ <|
    (comp_numericalClass_eq_lmapDomain φ β fun C₀ => hφ C₀ _ (hβc C₀)).trans hΨ.symm
  have hH : IsHomeomorph e := isHomeomorph_of_intersectionNumber_transpose e
    (Finsupp.lmapDomain ℝ ℝ p) (fun c₀ z => by
      obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective s₀ z
      rw [show e (OneCycle.numericalClass s₀ Z) = _ from LinearMap.congr_fun hΨ Z,
        LinearMap.comp_apply, NumericalCurveClasses.intersectionNumber_numericalClass,
        NumericalCurveClasses.intersectionNumber_numericalClass,
        intersectionNumber_lmapDomain p β fun C₀ D₀ => hβ C₀ D₀ (p D₀) (hp D₀)])
    (exists_numericalDivisorClass_eq_lmapDomain p eD fun D₀ => heD D₀ (p D₀) (hp D₀))
  have hcone := map_coneOfCurves_eq e.toLinearMap <| by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨_, ⟨C₀, rfl⟩, rfl⟩
      exact ⟨β C₀, (he C₀ _ (hβc C₀)).symm⟩
    · rintro _ ⟨C, rfl⟩
      obtain ⟨C₀, C₀K, hcl, hdeg⟩ := exists_properCurve_degree_eq_of_isPullback s₀ s π h hX₀ C
      refine ⟨_, ⟨C₀, rfl⟩, (he C₀ C₀K hcl).trans ?_⟩
      rw [OneCycle.numericalClass_eq_iff]
      intro L _
      rw [OneCycle.degree_cycle, OneCycle.degree_cycle, hdeg L]
  apply SetLike.coe_injective
  rw [PointedCone.coe_map, coe_closedConeOfCurves, coe_closedConeOfCurves, ← hcone,
    PointedCone.coe_map]
  exact hH.image_closure _

/-! ### Contracted curve classes -/

/-- A projective variety over a field carries an ample invertible sheaf. -/
private theorem exists_isAmple_of_isProjectiveVariety {k : Type u} [Field k] {Z : Scheme.{u}}
    {t : Z ⟶ Spec (.of k)} (hZ : MMP.Mori.IsProjectiveVariety k t) :
    ∃ (H : Z.Modules) (_ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 H),
      Scheme.Modules.IsAmple Z H := by
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨H, hH, hHa⟩ :=
    AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism t M hMa hZ.isProjective
  exact ⟨H, hH, (Stacks.AmpleBridge.isAmple_iff_isAmple _ H).mp hHa⟩

/-- **Contracted curve classes are unchanged by algebraically closed base extension.** Take
algebraically closed fields `k₀ → K`, a morphism `f₀ : X₀ ⟶ Z₀` of projective varieties over
`k₀`, and base changes `X = X₀ ×_{k₀} K`, `Z = Z₀ ×_{k₀} K` with projections `π`, `πZ` and the
base-changed morphism `f : X ⟶ Z`. Let `φ : N₁(X₀)_ℝ → N₁(X)_ℝ` be the linear map induced by
base extension of curves: `φ [C₀] = [C]` whenever `C` is the proper curve of `X` with closure
`π⁻¹(closure C₀)`. Then `φ` is injective on the span of the classes of the curves contracted
by `f₀` and maps it onto the span of the classes of the curves contracted by `f`. -/
@[mmp "lem_oai4_numerical_extension_e"]
public theorem map_span_contractedCurveClasses_eq_of_isPullback
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X Z₀ Z : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (hX : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (t₀ : Z₀ ⟶ Spec (.of k₀)) (t : Z ⟶ Spec (.of K)) (πZ : Z ⟶ Z₀)
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s) (hfπ : f ≫ πZ = π ≫ f₀)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C.cycle ℝ)) :
    Set.InjOn φ (Submodule.span ℝ ((fun C : ProperCurve s₀ => OneCycle.numericalClass s₀
        (C.cycle ℝ)) '' {C | C.IsContractedBy f₀})) ∧
      (Submodule.span ℝ ((fun C : ProperCurve s₀ => OneCycle.numericalClass s₀ (C.cycle ℝ)) ''
          {C | C.IsContractedBy f₀})).map φ =
        Submodule.span ℝ ((fun C : ProperCurve s => OneCycle.numericalClass s (C.cycle ℝ)) ''
          {C | C.IsContractedBy f}) := by
  have hv₀ : AlgebraicGeometry.IsVariety k₀ t₀ := hZ₀.toIsVariety
  haveI : IsSeparated t := MorphismProperty.of_isPullback hZ hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t := MorphismProperty.of_isPullback hZ hv₀.toLocallyOfFiniteType
  haveI : IsSeparated t₀ := hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t₀ := hv₀.toLocallyOfFiniteType
  haveI : QuasiCompact t := MorphismProperty.of_isPullback hZ hv₀.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace t
  haveI : IsAffineHom πZ := MorphismProperty.of_isPullback hZ.flip inferInstance
  -- an ample invertible sheaf `H` on `Z₀`, whose pull-back `H_K` to `Z` is ample
  obtain ⟨H, _, hHa⟩ := exists_isAmple_of_isProjectiveVariety hZ₀
  have hHKa : Scheme.Modules.IsAmple Z ((Scheme.Modules.pullback πZ).obj H) :=
    Scheme.Modules.isAmple_pullback_of_isAffineHom πZ H hHa
  -- the degree of `f^* H_K ≅ π^* f₀^* H` on a base change is that of `f₀^* H`
  have hdegH {C₀ : ProperCurve s₀} {C : ProperCurve s}
      (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
      C.degree K ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H)) =
        C₀.degree k₀ ((Scheme.Modules.pullback f₀).obj H) := by
    have e : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H) ≅
        (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback f₀).obj H) :=
      (Scheme.Modules.pullbackComp f πZ).app H ≪≫ (Scheme.Modules.pullbackCongr hfπ).app H ≪≫
        ((Scheme.Modules.pullbackComp π f₀).app H).symm
    rw [degree_congr C e]
    exact degree_pullback_eq_of_closure_eq s₀ s π hX hC _
  refine ⟨(injective_of_map_numericalClass s₀ s π hX φ hφ).injOn, ?_⟩
  rw [Submodule.map_span]
  apply le_antisymm <;> rw [Submodule.span_le]
  · -- the base change of an `f₀`-contracted curve is `f`-contracted
    rintro _ ⟨_, ⟨C₀, hC₀, rfl⟩, rfl⟩
    obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π hX C₀
    refine Submodule.subset_span ⟨C, ?_, (hφ C₀ C hC).symm⟩
    refine isContractedBy_of_degree_pullback_eq_zero f hf _ hHKa C ?_
    rw [hdegH hC]
    exact ProperCurve.degree_pullback_eq_zero_of_isContractedBy f₀ hf₀ C₀ hC₀ H
  · -- an `f`-contracted curve has the class of the base change of an `f₀`-contracted curve
    rintro _ ⟨C, hC, rfl⟩
    obtain ⟨C₀, C₀K, hC₀K, hdeg⟩ :=
      MMP.Fourfold.exists_properCurve_degree_eq_of_isPullback s₀ s π hX hX₀ C
    have hC₀ : C₀.IsContractedBy f₀ := by
      refine isContractedBy_of_degree_pullback_eq_zero f₀ hf₀ H hHa C₀ ?_
      rw [← hdegH hC₀K, hdeg]
      exact ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf C hC _
    refine Submodule.subset_span ⟨_, ⟨C₀, hC₀, rfl⟩, ?_⟩
    rw [hφ C₀ C₀K hC₀K, OneCycle.numericalClass_eq_iff]
    intro L _
    rw [OneCycle.degree_cycle, OneCycle.degree_cycle, hdeg L]

/-! ### The flat family `C ×_{k₀} S ⟶ S` -/

section Spreading

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
  {X₀ X : Scheme.{u}} {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- A curve is contracted by `h ≫ g` with `g` injective exactly when it is contracted by `h`. -/
private theorem isContractedBy_comp_iff_of_injective {k : Type u} [Field k] {X Y W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (h : X ⟶ Y) {g : Y ⟶ W}
    (hg : Function.Injective g) : C.IsContractedBy (h ≫ g) ↔ C.IsContractedBy h := by
  simp only [ProperCurve.IsContractedBy, Scheme.Hom.comp_apply, hg.eq_iff]

/-- **Degrees are constant in the family `C ×_{k₀} S`.** Let `X_S = X₀ ×_{k₀} S` over a connected
`S`, let `j : X₀ ⟶ X_S` be the fibre over a `k₀`-point `x` of `S` and `ι : X ⟶ X_S` the fibre over
a `K`-point `η` of `S`. If `C' ⊆ X` is the base change of a proper curve `C ⊆ X₀`, then every
invertible sheaf `M` on `X_S` has the same degree on `C` (through `j`) and on `C'`
(through `ι`): both are fibres of the flat proper family `C ×_{k₀} S ⟶ S`. -/
private theorem degree_pullback_fibre_eq (C : ProperCurve s₀) (C' : ProperCurve s)
    (a : C'.scheme ⟶ C.scheme) (ha : C'.ι ≫ π = a ≫ C.ι)
    (hsq : IsPullback a (C'.ι ≫ s) (C.ι ≫ s₀) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {S : Scheme.{u}} [ConnectedSpace S] (σ : S ⟶ Spec (.of k₀)) (η : Spec (.of K) ⟶ S)
    (hη : η ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    {XS : Scheme.{u}} {p : XS ⟶ X₀} {q : XS ⟶ S} (hXS : IsPullback p q s₀ σ)
    (M : XS.Modules) [SheafOfModules.IsInvertible XS.presheaf XS.ringCatSheaf.2 M]
    {ι : X ⟶ XS} (hιp : ι ≫ p = π) (hιq : ι ≫ q = s ≫ η)
    {x : Spec (.of k₀) ⟶ S} (hx : x ≫ σ = 𝟙 _)
    {j : X₀ ⟶ XS} (hjp : j ≫ p = 𝟙 _) (hjq : j ≫ q = s₀ ≫ x) :
    C.degree k₀ ((Scheme.Modules.pullback j).obj M) =
      C'.degree K ((Scheme.Modules.pullback ι).obj M) := by
  set gC : C.scheme ⟶ Spec (.of k₀) := C.ι ≫ s₀ with hgC
  have hP : IsPullback (pullback.fst gC σ) (pullback.snd gC σ) gC σ :=
    IsPullback.of_hasPullback gC σ
  set fW := pullback.snd gC σ
  haveI : Flat fW := MorphismProperty.of_isPullback (P := @Flat) hP inferInstance
  haveI : IsProper fW := MorphismProperty.of_isPullback (P := @IsProper) hP inferInstance
  haveI : LocallyOfFinitePresentation gC :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation fW :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hP inferInstance
  set w : pullback gC σ ⟶ XS := hXS.lift (pullback.fst gC σ ≫ C.ι) fW
    (by rw [Category.assoc, ← hgC, pullback.condition])
  have hwp : w ≫ p = pullback.fst gC σ ≫ C.ι := hXS.lift_fst _ _ _
  have hwq : w ≫ q = fW := hXS.lift_snd _ _ _
  haveI : Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback w).obj M) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      _ _ _).mpr inferInstance
  -- the fibre over `x` is `C`
  set q₁ : C.scheme ⟶ pullback gC σ := pullback.lift (𝟙 _) (gC ≫ x)
    (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id])
  have hq₁f : q₁ ≫ pullback.fst gC σ = 𝟙 _ := pullback.lift_fst _ _ _
  have hq₁s : q₁ ≫ fW = gC ≫ x := pullback.lift_snd _ _ _
  have h₁ : IsPullback q₁ gC fW x := by
    refine IsPullback.of_right (h₁₂ := pullback.fst gC σ) (v₁₃ := gC) (h₂₂ := σ) ?_ hq₁s hP
    rw [hq₁f, hx]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hq₁w : q₁ ≫ w = C.ι ≫ j := hXS.hom_ext (by simp [hwp, reassoc_of% hq₁f, hjp])
    (by simp [hwq, hq₁s, hgC, hjq])
  -- the fibre over `η` is `C'`
  set q₂ : C'.scheme ⟶ pullback gC σ := pullback.lift a (C'.ι ≫ s ≫ η)
    (by simpa [hη, hgC] using hsq.w)
  have hq₂f : q₂ ≫ pullback.fst gC σ = a := pullback.lift_fst _ _ _
  have hq₂s : q₂ ≫ fW = (C'.ι ≫ s) ≫ η := by
    rw [Category.assoc]
    exact pullback.lift_snd _ _ _
  have h₂ : IsPullback q₂ (C'.ι ≫ s) fW η := by
    refine IsPullback.of_right (h₁₂ := pullback.fst gC σ) (v₁₃ := gC) (h₂₂ := σ) ?_ hq₂s hP
    rwa [hq₂f, hη]
  have hq₂w : q₂ ≫ w = C'.ι ≫ ι := hXS.hom_ext (by simp [hwp, reassoc_of% hq₂f, ← ha, hιp])
    (by simp [hwq, hq₂s, hιq])
  change invertibleCurveDegree k₀ gC C.dim_le _ = invertibleCurveDegree K (C'.ι ≫ s) C'.dim_le _
  rw [invertibleCurveDegree_pullback_pullback_eq gC C.dim_le hq₁w.symm M,
    invertibleCurveDegree_pullback_pullback_eq (C'.ι ≫ s) C'.dim_le hq₂w.symm M]
  exact invertibleCurveDegree_eq_of_isPullback fW _ x η q₁ gC q₂ (C'.ι ≫ s) h₁ h₂
    C.dim_le C'.dim_le

end Spreading

/-- **A spread contraction contracts exactly the given ray.** Let `k₀ → K` be algebraically
closed fields, `X₀` a normal projective variety over `k₀`, `X = X₀ ×_{k₀} K` with projection
`π`, and `φ : N₁(X₀)_ℝ → N₁(X)_ℝ` the base-extension map of curve classes. Let `R₀` be an
extremal ray of `NE̅(X₀)` and `f : X ⟶ Z` the contraction of `φ(R₀)`. Let `S` be an integral
`k₀`-scheme of finite type with a point `η : Spec K ⟶ S` over the generic point, `f_S` a
projective `S`-morphism from `X₀ ×_{k₀} S` to `Z_S`, and `H_S` an `S`-ample invertible sheaf on
`Z_S`, whose base changes along `η` are `f` and an ample sheaf on `Z`. Then for every
`k₀`-point `x` of `S`, the fibre `f_x : X₀ ⟶ Z_x` contracts a curve `C` of `X₀` if and only if
`[C] ∈ R₀`. -/
@[mmp "lem_oai4_c3_spread_contraction_exact_ray"]
public theorem IsContractionOfRay.isContractedBy_fibre_iff
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) [IsNormal X₀]
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C₀' : ProperCurve s),
      closure {C₀'.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C₀'.cycle ℝ))
    {R₀ : Set (NumericalCurveClasses s₀)}
    (hR₀ : IsExtremalRay ℝ (closedConeOfCurves s₀ : Set (NumericalCurveClasses s₀)) R₀)
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) (f : X ⟶ Z)
    (hf : IsContractionOfRay s sZ (φ '' R₀) f)
    {S : Scheme.{u}} [IsIntegral S] (σ : S ⟶ Spec (.of k₀)) [LocallyOfFiniteType σ]
    [QuasiCompact σ] (η : Spec (.of K) ⟶ S) [IsDominant η]
    (hη : η ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    {XS ZS : Scheme.{u}} (p : XS ⟶ X₀) (q : XS ⟶ S) (hXS : IsPullback p q s₀ σ)
    (t : ZS ⟶ S) (fS : XS ⟶ ZS) (hfS : fS ≫ t = q) (hfS_proj : IsProjectiveMorphism fS)
    (HS : ZS.Modules) [Stacks.Ample.IsInvertibleModule ZS HS] (hHS : IsRelativelyAmple t HS)
    (ι : X ⟶ XS) (hιp : ι ≫ p = π) (hιq : ι ≫ q = s ≫ η)
    (ιZ : Z ⟶ ZS) (hZ : IsPullback ιZ sZ t η) (hfι : f ≫ ιZ = ι ≫ fS)
    (hH : Stacks.Ample.IsAmple Z ((modulePullback ιZ.toLRSHom.toShHom).obj HS))
    (x : Spec (.of k₀) ⟶ S) (hx : x ≫ σ = 𝟙 _)
    (j : X₀ ⟶ XS) (hjp : j ≫ p = 𝟙 _) (hjq : j ≫ q = s₀ ≫ x)
    {Zx : Scheme.{u}} (tx : Zx ⟶ Spec (.of k₀)) (jZ : Zx ⟶ ZS) (hZx : IsPullback jZ tx t x)
    (fx : X₀ ⟶ Zx) (hfx : fx ≫ jZ = j ≫ fS) (hfx' : fx ≫ tx = s₀)
    (C : ProperCurve s₀) :
    C.IsContractedBy fx ↔ OneCycle.numericalClass s₀ (C.cycle ℝ) ∈ R₀ := by
  classical
  have hv₀ : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  haveI : IsSeparated s₀ := hv₀.toIsSeparated
  haveI : LocallyOfFiniteType s₀ := hv₀.toLocallyOfFiniteType
  have hvZ : AlgebraicGeometry.IsVariety K sZ := hf.isNormalVariety_target.1
  haveI : IsSeparated sZ := hvZ.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hvZ.toLocallyOfFiniteType
  haveI : SheafOfModules.IsInvertible ZS.presheaf ZS.ringCatSheaf.2 HS :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      ZS.presheaf _ _).mp ‹_›
  -- the base change `C'` of `C`, and the ray property of `f`
  obtain ⟨C', hC', a, ha, hsq⟩ := exists_properCurve_isPullback s₀ s π h C
  rw [← (injective_of_map_numericalClass s₀ s π h φ hφ).mem_set_image, hφ C C' hC',
    ← hf.isContractedBy_iff C']
  -- `f_x` contracts `C` exactly when `j ≫ f_S` does, `Z_x ⟶ Z_S` being a mono
  haveI : Mono x := (IsSplitMono.mk' ⟨σ, hx⟩).mono
  haveI : Mono jZ := IsPullback.mono_fst_of_mono hZx
  rw [← isContractedBy_comp_iff_of_injective C fx jZ.injective, hfx]
  -- the ample sheaf `H` on `Z`
  set H := (modulePullback ιZ.toLRSHom.toShHom).obj HS
  haveI : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 H :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      ιZ.toLRSHom.toShHom _ inferInstance
  have hHa : Scheme.Modules.IsAmple Z H :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hH
  haveI := MMP.Mori.isInvertible_pullback_obj f H
  -- the degrees at the two ends of the flat family `C ×_{k₀} S ⟶ S` agree
  have hdeg : C.degree k₀ ((Scheme.Modules.pullback (j ≫ fS)).obj HS) =
      C'.degree K ((Scheme.Modules.pullback f).obj H) := by
    rw [degree_congr (L' := (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback fS).obj HS))
        C ((Scheme.Modules.pullbackComp j fS).app HS).symm,
      degree_congr (L' := (Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback fS).obj HS))
        C' ((Scheme.Modules.pullback f).mapIso
        ((modulePullbackIsoSchemePullback ιZ).app HS) ≪≫
        (Scheme.Modules.pullbackComp f ιZ).app HS ≪≫ (Scheme.Modules.pullbackCongr hfι).app HS ≪≫
        ((Scheme.Modules.pullbackComp ι fS).app HS).symm)]
    exact degree_pullback_fibre_eq C C' a ha hsq σ η hη hXS _ hιp hιq hx hjp hjq
  constructor
  · intro hc
    refine isContractedBy_of_degree_pullback_eq_zero f hf.comp_eq H hHa C' ?_
    rw [← hdeg]
    exact degree_pullback_eq_zero_of_isContractedBy' _ C hc HS
  · intro hc
    by_contra hnc
    -- an affine `V ∋ x` over which `H_S` is ample
    obtain ⟨V, -, hxV, hampV⟩ := hHS (x (s₀ C.point))
    have hU : ∀ y ∈ closure ({C.point} : Set X₀), (j ≫ fS) y ∈ t ⁻¹ᵁ V := fun y _ => by
      change t ((j ≫ fS) y) ∈ V
      rwa [← Scheme.Hom.comp_apply, Category.assoc, hfS, hjq, Scheme.Hom.comp_apply,
        Subsingleton.elim (s₀ y) (s₀ C.point)]
    have hpos := degree_pullback_pos_of_not_isContractedBy (sY := t ≫ σ) (j ≫ fS)
      (by simp [reassoc_of% hfS, reassoc_of% hjq, hx]) C hnc HS (t ⁻¹ᵁ V) hU hampV
    rw [hdeg, ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf.comp_eq C' hc H] at hpos
    exact lt_irrefl _ hpos

end MMP.Fourfold
