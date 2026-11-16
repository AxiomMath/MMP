module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleIndependence
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.SmallModelFibres
public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelsModules
public import MMP.AlgebraicGeometry.MMP.Fourfold.EchoWeightedMonomialValuation
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Composite
public import MMP.AlgebraicGeometry.Resolution.Surface.FamilyBettiBound
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchMultiplicity
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleDatumCartierDescent
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep

/-!
# Degree independence of transferred divisors

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), `L_1, …, L_b` a
punctured-independent family of line bundles on the generic scheme fibre `F_{η_T}`
(`MMP.Fourfold.IsPuncturedIndependent`), `(Y_e, q, η', L̃_1, …, L̃_b)` a local étale datum for it
(`MMP.Fourfold.LocalEtaleDatum`), `g : Y' ⟶ Y_e` a projective small birational morphism with `Y'`
`ℚ`-factorial, and `D'_1, …, D'_b` transferred divisors
(`MMP.Fourfold.LocalEtaleDatum.transferredDivisor`). Then the degree vectors
`(D'_i · C)_C`, `C` running over the irreducible curve components of the fibre `g⁻¹(η')`,
counted over `κ(η') = K_T`, are linearly independent over `ℚ`.

## Main results

* `MMP.Fourfold.LocalEtaleDatum.linearIndependent_transferredDivisor_degree`: the degree vectors
  of the transferred divisors are linearly independent.

## Implementation notes

The curve components of `g⁻¹(η')_red` are the proper curves
(`MMP.Mori.ProperCurve`) of the scheme fibre `g⁻¹(η') ⟶ Spec κ(η')`; as `g` is small, this fibre
has dimension at most one, so its one-dimensional integral closed subschemes are exactly its
curve components. The vectors are functions of the curve, which is the same as vectors of
`ℚ^s` for the `s` components. The degree `D'_i · C` over `κ(η')` of the `ℚ`-Cartier divisor
`D'_i` is `(1 / m) · deg_C 𝒪_{Y'}(m D'_i)|_C`, with `m` the Cartier index of `D'_i`.
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold
  MMP.Fourfold.LocalEtaleDatum MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.OAI4LocalDegreeIndependence

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Yt] [IsNormal Yt]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    {b : ℕ} {L : Fin b → (genericFibre π T).Modules}

/-! ### Germs in higher direct images -/

section Germs

variable {X Y U : TopCat.{0}}

/-- The map of higher direct images induced by restriction of classes, on germs. -/
private theorem higherDirectImageGerm_comp_restriction (p : X ⟶ Y) (g : U ⟶ X) {j : U ⟶ Y}
    (h : g ≫ p = j) (q : ℕ) {V : Opens Y} (y : Y) (hy : y ∈ V) :
    higherDirectImageGerm p q y hy ≫ (TopCat.Presheaf.stalkFunctor _ y).map
        ((TopCat.Sheaf.forget _ Y).map (higherDirectImageRestriction p g h q)) =
      rationalCohomologyMap (preimageRestrict p g h V) q ≫ higherDirectImageGerm j q y hy := by
  unfold higherDirectImageGerm higherDirectImageRestriction
  erw [Category.assoc, ← Functor.map_comp, ← toSheafify_naturality, Functor.map_comp,
    ← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

end Germs

/-! ### Rational first Chern classes -/

section Lift

/-- A continuous map into `X^an` with values over an open `W ⊆ X` lifts to `W^an`. -/
private theorem exists_lift_analyticMap_ι {Z : TopCat.{0}} {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (W : X.Opens) (f : Z ⟶ analyticSpace sX)
    (hf : ∀ z, (f z).toScheme ∈ W) :
    ∃ κ : Z ⟶ analyticSpace (W.ι ≫ sX), κ ≫ analyticMap W.ι rfl = f := by
  have he := isOpenEmbedding_realize_ι (sX := sX) W
  have hr := range_realize_ι (sX := sX) W
  have hmem : ∀ z, f z ∈ Set.range (realize (sX := W.ι ≫ sX) W.ι rfl) := fun z ↦ by
    rw [hr]; exact hf z
  let φ : Z → Set.range (realize (sX := W.ι ≫ sX) W.ι rfl) := fun z ↦ ⟨f z, hmem z⟩
  have hφ : Continuous φ := f.hom.continuous.subtype_mk _
  refine ⟨TopCat.ofHom ⟨he.isEmbedding.toHomeomorph.symm ∘ φ,
    he.isEmbedding.toHomeomorph.symm.continuous.comp hφ⟩, ?_⟩
  refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
  change realize W.ι rfl (he.isEmbedding.toHomeomorph.symm (φ z)) = f z
  exact congrArg Subtype.val (he.isEmbedding.toHomeomorph.apply_symm_apply (φ z))

end Lift

section RationalChern

variable {X' X : Scheme.{0}}

/-- The rational first Chern class `c₁(M) ∈ H²(X^an; ℚ)` of an invertible module on a scheme
`X` over `ℂ`, with structure morphism `sX`. -/
private noncomputable def rationalChernClass (sX : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    rationalCohomology (analyticSpace sX) 2 :=
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M)

/-- Isomorphic invertible modules have the same rational Chern class. -/
private theorem rationalChernClass_eq_of_iso (sX : X ⟶ Spec (.of ℂ)) {M N : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) :
    rationalChernClass sX M = rationalChernClass sX N := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  unfold rationalChernClass
  rw [algebraicFirstChernClass_eq_of_iso e]

/-- Naturality of the rational first Chern class under pullback. -/
private theorem rationalChernClass_pullback (sX : X ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ))
    (f : X' ⟶ X) (hf : f ≫ sX = sX') (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj M)] :
    rationalChernClass sX' ((Scheme.Modules.pullback f).obj M) =
      (rationalCohomologyMap (analyticMap f hf) 2).hom (rationalChernClass sX M) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : X'.Over (Spec (.of ℂ)) := ⟨sX'⟩
  unfold rationalChernClass
  rw [algebraicFirstChernClass_pullback f (analyticMap f hf) (fun _ ↦ rfl) M]
  exact MMP.Fourfold.mapCoeff_rationalCohomologyMap _ _ _

/-- Additivity of the rational first Chern class. -/
private theorem rationalChernClass_sheafTensor (sX : X ⟶ Spec (.of ℂ)) (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj M).obj N)] :
    rationalChernClass sX
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj M).obj N) =
      rationalChernClass sX M + rationalChernClass sX N := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  unfold rationalChernClass
  rw [algebraicFirstChernClass_sheafTensor]
  exact map_add _ _ _

variable [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- The rational first Chern class `c₁(𝒪_X(A)) ∈ H²(X^an; ℚ)` of a Cartier divisor `A`. -/
private noncomputable def cartierChernClass (sX : X ⟶ Spec (.of ℂ))
    (A : Divisor.cartierSubgroup (X := X)) : rationalCohomology (analyticSpace sX) 2 :=
  haveI := A.2.isInvertibleModule_divisorialSheaf
  rationalChernClass sX (A : Divisor X).divisorialSheaf

private theorem cartierChernClass_add (sX : X ⟶ Spec (.of ℂ))
    (A B : Divisor.cartierSubgroup (X := X)) :
    cartierChernClass sX (A + B) = cartierChernClass sX A + cartierChernClass sX B := by
  haveI := A.2.isInvertibleModule_divisorialSheaf
  haveI := B.2.isInvertibleModule_divisorialSheaf
  haveI := (A + B).2.isInvertibleModule_divisorialSheaf
  haveI := A.2.isInvertibleModule_tensorSheaf B.2
  unfold cartierChernClass
  rw [← rationalChernClass_sheafTensor]
  exact (rationalChernClass_eq_of_iso sX (A.2.divisorialSheafTensorIso B.2)).symm

/-- `A ↦ c₁(𝒪_X(A))` is additive on Cartier divisors. -/
private noncomputable def cartierChernHom (sX : X ⟶ Spec (.of ℂ)) :
    Divisor.cartierSubgroup (X := X) →+ rationalCohomology (analyticSpace sX) 2 :=
  AddMonoidHom.mk' (cartierChernClass sX) (cartierChernClass_add sX)

end RationalChern

/-- Isomorphic invertible modules on `F_t` have the same rational Chern class. -/
private theorem pointFibreChernClass_eq_of_iso {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    {T : IrreducibleCloseds Y} (π : Yt ⟶ Y) (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) {M N : (pointFibre sY π To t).Modules}
    [SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
      (pointFibre sY π To t).ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
      (pointFibre sY π To t).ringCatSheaf.2 N] (e : M ≅ N) :
    pointFibreChernClass sY π To t M = pointFibreChernClass sY π To t N := by
  unfold pointFibreChernClass
  rw [algebraicFirstChernClass_eq_of_iso e]

/-- The restriction to the fibre `F_t` of a global rational Chern class on `Ỹ` is the rational
Chern class of the restricted bundle. -/
private theorem rationalCohomologyMap_pointFibre_rationalChernClass {Y Yt : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y} (π : Yt ⟶ Y)
    (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V) (M : Yt.Modules)
    [SheafOfModules.IsInvertible Yt.presheaf Yt.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
      (pointFibre sY π To t).ringCatSheaf.2
        ((Scheme.Modules.pullback (pointFibreFst sY π To t)).obj M)] :
    (rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom
      ((rationalCohomologyMap (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        preimageSpace (resolutionAnalyticMap sY π) V ⟶ analyticSpace (π ≫ sY)) 2).hom
          (rationalChernClass (π ≫ sY) M)) =
      pointFibreChernClass sY π To t
        ((Scheme.Modules.pullback (pointFibreFst sY π To t)).obj M) := by
  have hmap : pointFibreInclusion sY π To t hV ≫
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        preimageSpace (resolutionAnalyticMap sY π) V ⟶ analyticSpace (π ≫ sY)) =
      analyticMap (pointFibreFst sY π To t) (pointFibreFst_comp_structure sY π To t) :=
    ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  erw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hmap]
  exact (rationalChernClass_pullback (π ≫ sY) _ (pointFibreFst sY π To t)
    (pointFibreFst_comp_structure sY π To t) M).symm

/-- On `j⁻¹(W₂)`, for `W₂` an analytic open over a Zariski open `W` on which `𝒪(A)` is
trivialised along the section of `π`, the restricted class `c₁(𝒪(A))` vanishes. -/
private theorem rationalCohomologyMap_regular_cartierChernHom_eq_zero {Y Yt : Scheme.{0}}
    [IsLocallyNoetherian Yt] [IsNormal Yt] [CompactSpace Yt]
    (sY : Y ⟶ Spec (.of ℂ)) (π : Yt ⟶ Y) (hπ : IsBiregular π (smoothLocus sY))
    {V W₂ : Opens (analyticSpace sY)} (hW₂V : W₂ ≤ V) (W : Y.Opens)
    (hW₂ : ∀ y ∈ W₂, y.toScheme ∈ W) (A : Divisor.cartierSubgroup (X := Yt))
    (e : (Scheme.Modules.pullback (((smoothLocus sY).ι ⁻¹ᵁ W).ι ≫ regularSection sY hπ)).obj
        (A : Divisor Yt).divisorialSheaf ≅
      (Scheme.Modules.pullback (((smoothLocus sY).ι ⁻¹ᵁ W).ι ≫ regularSection sY hπ)).obj
        (0 : Divisor Yt).divisorialSheaf) :
    (rationalCohomologyMap (preimageInclusion (regularInclusion sY) hW₂V) 2).hom
      ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
        (analyticMap (sX := (smoothLocus sY).ι ≫ sY) (sY := π ≫ sY) (regularSection sY hπ)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hπ) V) 2).hom
        ((rationalCohomologyMap (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            preimageSpace (resolutionAnalyticMap sY π) V ⟶ analyticSpace (π ≫ sY)) 2).hom
          (cartierChernHom (π ≫ sY) A))) = 0 := by
  let W' : (smoothLocus sY : Scheme.{0}).Opens := (smoothLocus sY).ι ⁻¹ᵁ W
  let φW := W'.ι ≫ regularSection sY hπ
  have hφ : φW ≫ π ≫ sY = W'.ι ≫ (smoothLocus sY).ι ≫ sY := by
    simp only [φW, Category.assoc]
    rw [← Category.assoc (regularSection sY hπ), regularSection_comp]
  let ι₂ : preimageSpace (regularInclusion sY) W₂ ⟶ analyticSpace ((smoothLocus sY).ι ≫ sY) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨κ, hκ⟩ := exists_lift_analyticMap_ι W' ι₂ (fun z ↦ hW₂ _ z.2)
  have hcomp : (preimageInclusion (regularInclusion sY) hW₂V ≫
      preimageRestrict (resolutionAnalyticMap sY π)
        (analyticMap (sX := (smoothLocus sY).ι ≫ sY) (sY := π ≫ sY) (regularSection sY hπ)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hπ) V) ≫
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        preimageSpace (resolutionAnalyticMap sY π) V ⟶ analyticSpace (π ≫ sY)) =
      κ ≫ analyticMap φW hφ := by
    refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
    have hz : (κ z).hom ≫ W'.ι = z.1.hom :=
      congrArg ComplexPoints.hom (ConcreteCategory.congr_hom hκ z)
    apply ComplexPoints.ext
    change z.1.hom ≫ regularSection sY hπ = (κ z).hom ≫ W'.ι ≫ regularSection sY hπ
    rw [← Category.assoc, hz]
  have hmaps := congrArg (fun φ ↦ rationalCohomologyMap φ 2) hcomp
  simp only [rationalCohomologyMap_comp] at hmaps
  haveI := A.2.isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule _ (0 : Divisor Yt).divisorialSheaf :=
    Divisor.isCartier_zero.isInvertibleModule_divisorialSheaf
  have hφ0 :
      (rationalCohomologyMap (analyticMap φW hφ) 2).hom (cartierChernHom (π ≫ sY) A) = 0 := by
    change (rationalCohomologyMap (analyticMap φW hφ) 2).hom
      (rationalChernClass (π ≫ sY) (A : Divisor Yt).divisorialSheaf) = 0
    rw [← rationalChernClass_pullback (π ≫ sY) _ φW hφ, rationalChernClass_eq_of_iso _ e,
      rationalChernClass_pullback (π ≫ sY) _ φW hφ]
    have hz : rationalChernClass (π ≫ sY) (0 : Divisor Yt).divisorialSheaf = 0 :=
      (cartierChernHom (π ≫ sY)).map_zero
    rw [hz, map_zero]
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hmaps) (cartierChernHom (π ≫ sY) A)
  refine this.trans ?_
  change (rationalCohomologyMap κ 2).hom
    ((rationalCohomologyMap (analyticMap φW hφ) 2).hom (cartierChernHom (π ≫ sY) A)) = 0
  rw [hφ0]
  exact LinearMap.map_zero _

/-- **The punctured image of a trivialised class vanishes.** Let `π : Ỹ ⟶ Y` be an isomorphism
over the smooth locus `Y_reg`, `A` a Cartier divisor on `Ỹ`, and `W ⊆ Y` an open containing the
point `t`, such that `𝒪(A)` and `𝒪` become isomorphic on `W ∩ Y_reg` (pulled back along the
section of `π`). Then the image in `(R²j_* ℚ)_t` of the germ at `t` of `c₁(𝒪(A))` is zero. -/
private theorem localSystemRestrictionFibre_cartierChernClass_eq_zero {Y Yt : Scheme.{0}}
    [IsLocallyNoetherian Yt] [IsNormal Yt] [CompactSpace Yt]
    (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y} (π : Yt ⟶ Y)
    (hπ : IsBiregular π (smoothLocus sY)) (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (A : Divisor.cartierSubgroup (X := Yt)) (W : Y.Opens)
    (hW : (To.ι ≫ curveι T) t.toScheme ∈ W)
    (e : (Scheme.Modules.pullback (((smoothLocus sY).ι ⁻¹ᵁ W).ι ≫ regularSection sY hπ)).obj
        (A : Divisor Yt).divisorialSheaf ≅
      (Scheme.Modules.pullback (((smoothLocus sY).ι ⁻¹ᵁ W).ι ≫ regularSection sY hπ)).obj
        (0 : Divisor Yt).divisorialSheaf) :
    (localSystemRestrictionFibre sY hπ To t).hom
      ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2) t).hom
        ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom
          ((rationalCohomologyMap (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            preimageSpace (resolutionAnalyticMap sY π) V ⟶ analyticSpace (π ≫ sY)) 2).hom
              (cartierChernHom (π ≫ sY) A)))) = 0 := by
  let g := analyticMap (sX := (smoothLocus sY).ι ≫ sY) (sY := π ≫ sY) (regularSection sY hπ)
    (by rw [← Category.assoc, regularSection_comp])
  have hg : g ≫ resolutionAnalyticMap sY π = regularInclusion sY :=
    regularSection_analyticMap_comp sY hπ
  let inclV : preimageSpace (resolutionAnalyticMap sY π) V ⟶ analyticSpace (π ≫ sY) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let γV := (rationalCohomologyMap inclV 2).hom (cartierChernHom (π ≫ sY) A)
  let Wan : Opens (analyticSpace sY) :=
    ⟨{y | y.toScheme ∈ W}, isOpen_setOf_toScheme_mem W.isOpen⟩
  let W₂ := V ⊓ Wan
  have hW₂V : W₂ ≤ V := inf_le_left
  have hbW₂ : curveOpenInclusion sY To t ∈ W₂ := ⟨hV, hW⟩
  have key : (rationalCohomologyMap (preimageInclusion (regularInclusion sY) hW₂V) 2).hom
      ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π) g hg V) 2).hom
        γV) = 0 :=
    rationalCohomologyMap_regular_cartierChernHom_eq_zero sY π hπ hW₂V W
      (fun _ hy ↦ hy.2) A e
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (stalkToPullbackStalk_naturality (curveOpenInclusion sY To) (resolutionRestriction sY hπ 2) t))
    ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom γV)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (higherDirectImageGerm_comp_restriction (resolutionAnalyticMap sY π) g hg 2 _ hV)) γV
  have hz : ((TopCat.Presheaf.stalkFunctor _ _).map ((TopCat.Sheaf.forget _ _).map
      (resolutionRestriction sY hπ 2))).hom
        ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom γV) = 0 := by
    refine Eq.trans h2 ?_
    change (higherDirectImageGerm (regularInclusion sY) 2 _ hV).hom
      ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π) g hg V) 2).hom γV) = 0
    rw [← higherDirectImageGerm_res _ _ hW₂V _ hbW₂, key, map_zero]
  refine Eq.trans h1 ?_
  change (stalkToPullbackStalk (curveOpenInclusion sY To) (regularHigherDirectImage sY 2) t).hom
    (((TopCat.Presheaf.stalkFunctor _ _).map ((TopCat.Sheaf.forget _ _).map
      (resolutionRestriction sY hπ 2))).hom
        ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom γV)) = 0
  rw [hz]
  exact LinearMap.map_zero _

/-! ### Points of the curve -/

section CurvePoint

/-- A dense open `T° ⊆ T` of an irreducible closed subset of a scheme of finite type over `ℂ` has
a `ℂ`-point over any open neighbourhood of a point of `T`. -/
private theorem exists_complexPoint_curve_mem {Ye : Scheme.{0}} (sB : Ye ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sB] [QuasiCompact sB] {C : IrreducibleCloseds Ye} {η : Ye}
    (hη : η ∈ (C : Set Ye)) (To : (curveScheme C).Opens)
    (hTo : Dense (To : Set (curveScheme C))) (U : Ye.Opens) (hU : η ∈ U) :
    ∃ t : ComplexPoints (To.ι ≫ curveι C ≫ sB), (To.ι ≫ curveι C).base t.toScheme ∈ U := by
  obtain ⟨ξ, hξ⟩ : η ∈ Set.range (curveι C) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hη
  obtain ⟨ζ, hζU, hζT⟩ := hTo.inter_open_nonempty _ ((curveι C) ⁻¹ᵁ U).isOpen
    ⟨ξ, show (curveι C) ξ ∈ U by rw [hξ]; exact hU⟩
  haveI : CompactSpace (curveScheme C) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι C ≫ sB)
  haveI : IsLocallyNoetherian (curveScheme C) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι C ≫ sB)
  haveI : IsNoetherian (curveScheme C) := ⟨⟩
  haveI : CompactSpace (To : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (To : Set (curveScheme C)))
  haveI : QuasiCompact (To.ι ≫ curveι C ≫ sB) := inferInstance
  obtain ⟨x, hx, hxV⟩ := MMP.Fourfold.exists_complexPoint_mem (To.ι ≫ curveι C ≫ sB)
    (V := (To.ι ≫ curveι C) ⁻¹ᵁ U) ⟨⟨ζ, hζT⟩, hζU⟩
  exact ⟨⟨x, hx⟩, hxV⟩

end CurvePoint

/-- The combination `∑ n_i D̃_i` restricts, along the section of `π_e` over the smooth locus,
to a divisor whose sheaf is trivial near every point of a neighbourhood of `η'`. -/
private def IsRegularTrivial (E : LocalEtaleDatum sY T π L)
    (hπe : IsBiregular E.resolutionMap (smoothLocus (E.map ≫ sY)))
    (A : Divisor E.resolution) : Prop :=
  ∃ U : E.scheme.Opens, E.point ∈ U ∧ ∀ y ∈ U, ∃ W : E.scheme.Opens, y ∈ W ∧
    Nonempty ((Scheme.Modules.pullback (((smoothLocus (E.map ≫ sY)).ι ⁻¹ᵁ W).ι ≫
        regularSection (E.map ≫ sY) hπe)).obj A.divisorialSheaf ≅
      (Scheme.Modules.pullback (((smoothLocus (E.map ≫ sY)).ι ⁻¹ᵁ W).ι ≫
        regularSection (E.map ≫ sY) hπe)).obj (0 : Divisor E.resolution).divisorialSheaf)

/-- **(I)** If `∑ n_i D̃_i` is trivial on the smooth locus near `η'`, then all `n_i` vanish:
the punctured classes of the `L̃_i` are independent. -/
private theorem eq_zero_of_isRegularTrivial (hY : IsLocalSetting sY Θ T π)
    (hL : IsPuncturedIndependent sY hY.isBiregular L) (E : LocalEtaleDatum sY T π L)
    (D : Fin b → Divisor E.resolution) (hDc : ∀ i, (D i).IsCartier)
    (hDL : ∀ i, Nonempty ((D i).divisorialSheaf ≅ E.bundle i))
    (hπe : IsBiregular E.resolutionMap (smoothLocus (E.map ≫ sY))) (n : Fin b → ℤ)
    (H : IsRegularTrivial E hπe (∑ i, n i • D i)) : n = 0 := by
  classical
  have hqp := E.isQuasiProjectiveVariety
  have hπp : IsProjectiveMorphism π := hY.isResolution.2.2.2.1
  haveI : IsProper E.resolutionMap := isProper_of_isProjectiveMorphism _ (hπp.baseChange E.map)
  haveI : IsIntegral E.scheme := E.isQuasiProjectiveVariety.toIsVariety.toIsIntegral
  haveI : CompactSpace E.scheme := QuasiCompact.compactSpace_of_compactSpace (E.map ≫ sY)
  haveI : CompactSpace E.resolution := QuasiCompact.compactSpace_of_compactSpace E.resolutionMap
  obtain ⟨hπe', To, hTo, hall⟩ := exists_dense_linearIndependent_chernClass hY hL E
  obtain ⟨U, hU, hUW⟩ := H
  obtain ⟨t, ht⟩ : ∃ t : ComplexPoints (To.ι ≫ curveι E.curve ≫ E.map ≫ sY),
      (To.ι ≫ curveι E.curve).base t.toScheme ∈ U :=
    exists_complexPoint_curve_mem (E.map ≫ sY)
      (by rw [E.coe_curve]; exact subset_closure (Set.mem_singleton _)) To hTo U hU
  obtain ⟨W, hyW, ⟨e⟩⟩ := hUW _ ht
  obtain ⟨V, hV, α, hα, hLI⟩ := hall t
  let b₀ : ComplexPoints (E.map ≫ sY) := curveOpenInclusion (E.map ≫ sY) To t
  let A : Divisor.cartierSubgroup (X := E.resolution) :=
    ∑ i, n i • ⟨D i, Divisor.mem_cartierSubgroup.mpr (hDc i)⟩
  have hAc : ((A : Divisor.cartierSubgroup (X := E.resolution)) : Divisor E.resolution) =
      ∑ i, n i • D i := by
    simp only [A, AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul]
  let γ := cartierChernHom (E.resolutionMap ≫ E.map ≫ sY) A
  let inclV : preimageSpace (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap) V ⟶
      analyticSpace (E.resolutionMap ≫ E.map ≫ sY) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let γV := (rationalCohomologyMap inclV 2).hom γ
  let x := ∑ i, (n i : ℚ) • α i
  -- the difference `x - γ|_V` vanishes on the fibre `F_t`
  have hB : (rationalCohomologyMap
      (pointFibreInclusion (E.map ≫ sY) E.resolutionMap To t hV) 2).hom (x - γV) = 0 := by
    have hfib : ∀ i, (rationalCohomologyMap
        (pointFibreInclusion (E.map ≫ sY) E.resolutionMap To t hV) 2).hom
          ((rationalCohomologyMap inclV 2).hom
            (cartierChernClass (E.resolutionMap ≫ E.map ≫ sY)
              ⟨D i, Divisor.mem_cartierSubgroup.mpr (hDc i)⟩)) =
        (rationalCohomologyMap
          (pointFibreInclusion (E.map ≫ sY) E.resolutionMap To t hV) 2).hom (α i) := by
      intro i
      obtain ⟨hinv, hαi⟩ := hα i
      rw [hαi]
      haveI := (hDc i).isInvertibleModule_divisorialSheaf
      obtain ⟨ei⟩ := hDL i
      unfold cartierChernClass
      refine (rationalCohomologyMap_pointFibre_rationalChernClass (E.map ≫ sY) E.resolutionMap
        To t hV (D i).divisorialSheaf).trans ?_
      exact pointFibreChernClass_eq_of_iso _ _ _ _
        ((Scheme.Modules.pullback (pointFibreFst (E.map ≫ sY) E.resolutionMap To t)).mapIso ei)
    have hγ : γ = ∑ i, (n i : ℚ) • cartierChernClass (E.resolutionMap ≫ E.map ≫ sY)
        ⟨D i, Divisor.mem_cartierSubgroup.mpr (hDc i)⟩ := by
      change cartierChernHom _ A = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
      rfl
    rw [LinearMap.map_sub, sub_eq_zero]
    change _ = (rationalCohomologyMap
      (pointFibreInclusion (E.map ≫ sY) E.resolutionMap To t hV) 2).hom
        ((rationalCohomologyMap inclV 2).hom γ)
    rw [hγ, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, map_smul, hfib i]
  -- so it vanishes on a smaller tube, by the fibre comparison
  obtain ⟨W₁, hW₁V, hbW₁, hz⟩ : ∃ (W₁ : Opens (analyticSpace (E.map ≫ sY))) (h : W₁ ≤ V),
      b₀ ∈ W₁ ∧ (rationalCohomologyMap
        (preimageInclusion (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap) h) 2).hom
          (x - γV) = 0 :=
    (fibre_comparison E.resolutionMap (E.map ≫ sY) b₀
      (pointFibreFst (E.map ≫ sY) E.resolutionMap To t)
      (pointFibreSnd (E.map ≫ sY) E.resolutionMap To t) (IsPullback.of_hasPullback _ _) 2).2
      V hV (x - γV) hB
  have hgerm : (higherDirectImageGerm (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap)
      2 _ hV).hom x = (higherDirectImageGerm
        (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap) 2 _ hV).hom γV := by
    rw [← sub_eq_zero, ← map_sub, ← higherDirectImageGerm_res _ _ hW₁V _ hbW₁, hz, map_zero]
  -- the punctured image of `γ|_V` vanishes, `𝒪(∑ n_i D̃_i)` being trivial on `W ∩ (Y_e)_reg`
  have hE : (localSystemRestrictionFibre (E.map ≫ sY) hπe To t).hom
      ((stalkToPullbackStalk (curveOpenInclusion (E.map ≫ sY) To)
        (resolutionHigherDirectImage (E.map ≫ sY) E.resolutionMap 2) t).hom
        ((higherDirectImageGerm (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap)
          2 _ hV).hom γV)) = 0 :=
    localSystemRestrictionFibre_cartierChernClass_eq_zero (E.map ≫ sY) E.resolutionMap hπe To t hV
      A W hyW (by rw [hAc]; exact e)
  let F := higherDirectImageGerm (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap) 2 _ hV ≫
    stalkToPullbackStalk (curveOpenInclusion (E.map ≫ sY) To)
      (resolutionHigherDirectImage (E.map ≫ sY) E.resolutionMap 2) t ≫
    localSystemRestrictionFibre (E.map ≫ sY) hπe To t
  have hsum : ∑ i, (n i : ℚ) • F.hom (α i) = 0 := by
    simp_rw [← map_smul]
    rw [← map_sum]
    change F.hom x = 0
    simp only [F, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hgerm]
    exact hE
  funext i
  exact_mod_cast Fintype.linearIndependent_iff.mp hLI (fun i ↦ (n i : ℚ)) hsum i

/-- The degree `D'_i · C = deg_C 𝒪(m D'_i) / m` over `κ(η')` of the transferred divisor `D'_i` on a
curve `C` of the fibre `g⁻¹(η')`, `m` the Cartier index. -/
private noncomputable def fibreDegree (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (g : Y' ⟶ E.scheme)
    (hQ : IsQFactorial (g ≫ E.map ≫ sY)) (A : Divisor E.resolution)
    (C : ProperCurve (g.fiberToSpecResidueField E.point)) : ℚ :=
  let D' := Divisor.toQDivisor (E.transferredDivisor g A)
  let hD' := isQCartier_of_isQFactorial _ hQ D'
  haveI := (QDivisor.isCartierDivisor_cartierIndex_smul hD').isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  haveI : IsProper (C.ι ≫ g.fiberToSpecResidueField E.point) := C.isProperCurve.isProper
  ((degreeOn (E.scheme.residueField E.point) (g.fiberToSpecResidueField E.point) C.ι
      C.dim_le ((Scheme.Modules.pullback (g.fiberι E.point)).obj
        (QDivisor.isCartierDivisor_cartierIndex_smul hD').toDivisor.divisorialSheaf) : ℚ) /
    D'.cartierIndex hD')

/-! ### Degrees on the curves of the fibre `g⁻¹(η')` -/

section FibreDegree

variable (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y']
  [CompactSpace Y'] (g : Y' ⟶ E.scheme) (C : ProperCurve (g.fiberToSpecResidueField E.point))

/-- The degree over `κ(η')` of `𝒪(A)` on a curve `C` of the fibre `g⁻¹(η')`, for `A` Cartier. -/
private noncomputable def cartierFibreDegree (A : Divisor Y') (hA : A.IsCartier) : ℤ :=
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI : IsProper (C.ι ≫ g.fiberToSpecResidueField E.point) := C.isProperCurve.isProper
  degreeOn (E.scheme.residueField E.point) (g.fiberToSpecResidueField E.point) C.ι C.dim_le
    ((Scheme.Modules.pullback (g.fiberι E.point)).obj A.divisorialSheaf)

private theorem cartierFibreDegree_congr {A B : Divisor Y'} (h : A = B) (hA : A.IsCartier)
    (hB : B.IsCartier) : cartierFibreDegree E g C A hA = cartierFibreDegree E g C B hB := by
  subst h; rfl

private theorem cartierFibreDegree_add {A B : Divisor Y'} (hA : A.IsCartier) (hB : B.IsCartier) :
    cartierFibreDegree E g C (A + B) (hA.add hB) =
      cartierFibreDegree E g C A hA + cartierFibreDegree E g C B hB := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  haveI := (hA.add hB).isInvertibleModule_divisorialSheaf
  haveI := hA.isInvertibleModule_tensorSheaf hB
  haveI : IsProper (C.ι ≫ g.fiberToSpecResidueField E.point) := C.isProperCurve.isProper
  let φ := g.fiberι E.point
  haveI : SheafOfModules.IsInvertible (g.fiber E.point).presheaf (g.fiber E.point).ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(g.fiber E.point).toRingedSpace.presheaf,
        (g.fiber E.point).toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback φ).obj A.divisorialSheaf)).obj
            ((Scheme.Modules.pullback φ).obj B.divisorialSheaf)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible _ _ _ _
  unfold cartierFibreDegree
  exact (degreeOn_eq_of_iso _ _ _ _ ((Scheme.Modules.pullback φ).mapIso
      (hA.divisorialSheafTensorIso hB).symm ≪≫
    Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso φ _ _)).trans
    (degreeOn_tensorSheaf _ _ _ _ _ _)

/-- `A ↦ deg_C 𝒪(A)` is additive on Cartier divisors. -/
private noncomputable def cartierFibreDegreeHom : Divisor.cartierSubgroup (X := Y') →+ ℤ :=
  AddMonoidHom.mk' (fun A ↦ cartierFibreDegree E g C A A.2) fun A B ↦
    cartierFibreDegree_add E g C A.2 B.2

private theorem cartierFibreDegreeHom_apply (A : Divisor.cartierSubgroup (X := Y')) :
    cartierFibreDegreeHom E g C A = cartierFibreDegree E g C A A.2 := rfl

end FibreDegree

/-- **Fibre degrees of a combination.** If `∑ n_i (D'_i · C) = 0` on every curve `C` of the fibre
`g⁻¹(η')`, then `deg_C 𝒪(N) = 0` for every Cartier `N` that is a multiple `k ∑ n_i D'_i`. -/
private theorem cartierFibreDegree_eq_zero_of_fibreDegree (E : LocalEtaleDatum sY T π L)
    {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (g : Y' ⟶ E.scheme)
    (hQ : IsQFactorial (g ≫ E.map ≫ sY)) (D : Fin b → Divisor E.resolution) (n : Fin b → ℤ)
    (C : ProperCurve (g.fiberToSpecResidueField E.point))
    (hdeg : ∑ i, (n i : ℚ) * fibreDegree E g hQ (D i) C = 0) (k : ℤ) (N : Divisor Y')
    (hN : N.IsCartier) (hNk : N = k • ∑ i, n i • E.transferredDivisor g (D i)) :
    cartierFibreDegree E g C N hN = 0 := by
  classical
  let A : Fin b → Divisor Y' := fun i ↦ E.transferredDivisor g (D i)
  let hA : ∀ i, (Divisor.toQDivisor (A i)).IsQCartier := fun i ↦
    isQCartier_of_isQFactorial _ hQ (Divisor.toQDivisor (A i))
  let c : Fin b → ℕ := fun i ↦ (Divisor.toQDivisor (A i)).cartierIndex (hA i)
  have hc : ∀ i, 0 < c i := fun i ↦ QDivisor.cartierIndex_pos (hA i)
  let Nc : Fin b → Divisor Y' := fun i ↦
    (QDivisor.isCartierDivisor_cartierIndex_smul (hA i)).toDivisor
  have hNc : ∀ i, (Nc i).IsCartier := fun i ↦
    (QDivisor.isCartierDivisor_cartierIndex_smul (hA i)).isCartier_toDivisor
  have hNcA : ∀ i, Nc i = ((c i : ℕ) : ℤ) • A i := fun i ↦ by
    apply Divisor.toQDivisor_injective
    rw [(QDivisor.isCartierDivisor_cartierIndex_smul (hA i)).toQDivisor_toDivisor, map_zsmul]
  have hfib : ∀ i, fibreDegree E g hQ (D i) C =
      (cartierFibreDegree E g C (Nc i) (hNc i) : ℚ) / c i := fun i ↦ rfl
  let P : ℕ := ∏ i, c i
  have hP : 0 < P := Finset.prod_pos fun i _ ↦ hc i
  have hdvd : ∀ i, c i ∣ P := fun i ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let NcS : Fin b → Divisor.cartierSubgroup (X := Y') := fun i ↦
    ⟨Nc i, Divisor.mem_cartierSubgroup.mpr (hNc i)⟩
  let NS : Divisor.cartierSubgroup (X := Y') := ⟨N, Divisor.mem_cartierSubgroup.mpr hN⟩
  have hcomb : ((P : ℕ) : ℤ) • NS = ∑ i, (k * n i * ((P / c i : ℕ) : ℤ)) • NcS i := by
    apply Subtype.ext
    simp only [NS, NcS, AddSubgroup.coe_zsmul, AddSubgroup.val_finset_sum, hNcA, hNk,
      Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    have : ((P / c i : ℕ) : ℤ) * (c i : ℤ) = P := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvd i)]
    rw [mul_assoc, this]
    ring
  have hF := congrArg (cartierFibreDegreeHom E g C) hcomb
  rw [map_zsmul, map_sum] at hF
  simp only [map_zsmul, cartierFibreDegreeHom_apply, smul_eq_mul] at hF
  have hFq : (P : ℚ) * cartierFibreDegree E g C N hN =
      ∑ i, (k : ℚ) * P * ((n i : ℚ) * fibreDegree E g hQ (D i) C) := by
    have := congrArg (fun z : ℤ ↦ (z : ℚ)) hF
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hfib i]
    have hci : (c i : ℚ) ≠ 0 := by exact_mod_cast (hc i).ne'
    have : ((P / c i : ℕ) : ℚ) = (P : ℚ) / c i := by
      rw [Nat.cast_div (hdvd i) hci]
    rw [this]
    field_simp
    rfl
  rw [← Finset.mul_sum, hdeg, mul_zero] at hFq
  have hP' : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne'
  exact_mod_cast (mul_eq_zero.mp hFq).resolve_left hP'

/-! ### Restricting a local étale datum to an open neighbourhood of `η'` -/

section Restrict

variable (E : LocalEtaleDatum sY T π L) (U : E.scheme.Opens) (hU : E.point ∈ U)

/-- The elementary étale neighbourhood `(U, η')` of `(Y, η_T)`, for an open `U ∋ η'` of `Y_e`. -/
private noncomputable def restrictNeighborhood :
    ElementaryEtaleNeighborhood Y (localSettingGenericPoint T) :=
  ⟨{ scheme := U, point := ⟨E.point, hU⟩, toBase := U.ι ≫ E.map, map_point := E.map_point },
    by
      have : IsIso E.neighborhood.obj.residueFieldMap := E.isIso_residueFieldMap
      change IsIso ((Y.residueFieldCongr E.map_point).inv ≫
        (U.ι ≫ E.map).residueFieldMap ⟨E.point, hU⟩)
      erw [Scheme.residueFieldMap_comp]
      have h : IsIso ((Y.residueFieldCongr E.map_point).inv ≫
          E.map.residueFieldMap E.point) := E.isIso_residueFieldMap
      have hb : IsIso (E.map.residueFieldMap E.point) :=
        IsIso.of_isIso_comp_left (Y.residueFieldCongr E.map_point).inv _
      have hc : ∀ x : (U : Scheme.{0}), IsIso (U.ι.residueFieldMap x) := fun _ ↦ inferInstance
      exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hb (hc _))⟩

/-- The restriction to `U` of the base change `Ỹ ×_Y Y_e ⟶ Ỹ ×_Y Y_e`. -/
private noncomputable abbrev restrictResolutionMap :
    Limits.pullback π (restrictNeighborhood E U hU).obj.toBase ⟶ E.resolution :=
  Limits.pullback.map π (restrictNeighborhood E U hU).obj.toBase π E.map (𝟙 _) U.ι (𝟙 _)
    (by simp) (by rw [Category.comp_id]; rfl)

private theorem elementaryNeighborhoodSection_restrictNeighborhood :
    elementaryNeighborhoodSection (restrictNeighborhood E U hU) ≫ U.ι =
      elementaryNeighborhoodSection E.neighborhood := by
  have hc : ∀ x : (U : Scheme.{0}), IsIso (U.ι.residueFieldMap x) := fun _ ↦ inferInstance
  haveI := hc (restrictNeighborhood E U hU).obj.point
  have hE : IsIso E.neighborhood.obj.residueFieldMap := E.isIso_residueFieldMap
  have hR : IsIso (restrictNeighborhood E U hU).obj.residueFieldMap :=
    (restrictNeighborhood E U hU).property
  have hnew : (restrictNeighborhood E U hU).obj.residueFieldMap =
      E.neighborhood.obj.residueFieldMap ≫
        U.ι.residueFieldMap (restrictNeighborhood E U hU).obj.point := by
    change (Y.residueFieldCongr E.map_point).inv ≫ (U.ι ≫ E.map).residueFieldMap ⟨E.point, hU⟩ =
      ((Y.residueFieldCongr E.map_point).inv ≫ E.map.residueFieldMap E.point) ≫ _
    erw [Scheme.residueFieldMap_comp]
    exact (Category.assoc _ _ _).symm
  have hinv : U.ι.residueFieldMap (restrictNeighborhood E U hU).obj.point ≫
      @inv _ _ _ _ (restrictNeighborhood E U hU).obj.residueFieldMap hR =
      inv E.neighborhood.obj.residueFieldMap := by
    simp only [hnew]
    refine @IsIso.eq_inv_of_hom_inv_id _ _ _ _ _ hE _ ?_
    have hcomp : IsIso (E.neighborhood.obj.residueFieldMap ≫
        U.ι.residueFieldMap (restrictNeighborhood E U hU).obj.point) :=
      IsIso.comp_isIso' hE (hc _)
    exact (Category.assoc _ _ _).symm.trans (@IsIso.hom_inv_id _ _ _ _ _ hcomp)
  unfold elementaryNeighborhoodSection
  erw [Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι
      (restrictNeighborhood E U hU).obj.point,
    ← Category.assoc, ← Spec.map_comp, hinv]
  rfl

private theorem localEtaleFibreMap_restrictNeighborhood :
    localEtaleFibreMap π (restrictNeighborhood E U hU) ≫ restrictResolutionMap E U hU =
      localEtaleFibreMap π E.neighborhood := by
  apply Limits.pullback.hom_ext
  · erw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id, Limits.pullback.lift_fst,
      Category.comp_id, Limits.pullback.lift_fst, Category.comp_id]
  · erw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, Limits.pullback.lift_snd,
      Category.assoc, elementaryNeighborhoodSection_restrictNeighborhood, Limits.pullback.lift_snd]

/-- The restriction of a local étale datum to an open neighbourhood `U` of `η'`. -/
private noncomputable def restrictOpen : LocalEtaleDatum sY T π L where
  neighborhood := restrictNeighborhood E U hU
  isQuasiProjectiveVariety := by
    have hqp := E.isQuasiProjectiveVariety
    haveI : Nonempty (U : Scheme.{0}) := ⟨⟨E.point, hU⟩⟩
    haveI : IsIntegral E.scheme := E.isQuasiProjectiveVariety.toIsVariety.toIsIntegral
    haveI : IsIntegral (U : Scheme.{0}) := isIntegral_of_isOpenImmersion U.ι
    haveI : CompactSpace E.scheme := QuasiCompact.compactSpace_of_compactSpace (E.map ≫ sY)
    haveI : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian (E.map ≫ sY)
    haveI : IsNoetherian E.scheme := ⟨⟩
    haveI : CompactSpace (U : Scheme.{0}) :=
      isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set E.scheme))
    have hv : AlgebraicGeometry.IsVariety ℂ (U.ι ≫ E.map ≫ sY) := {}
    change IsQuasiProjectiveVariety ℂ ((U.ι ≫ E.map) ≫ sY)
    rw [Category.assoc]
    exact (isQuasiProjectiveVariety_iff ℂ _).mpr
      ⟨hv, IsQuasiProjective.comp U.ι (E.map ≫ sY) (isQuasiProjective_of_isImmersion U.ι)
        hqp.isQuasiProjective⟩
  isNormal := by haveI := E.isNormal; exact (inferInstance : IsNormal (U : Scheme.{0}))
  bundle i := (Scheme.Modules.pullback (restrictResolutionMap E U hU)).obj (E.bundle i)
  isInvertibleModule i :=
    Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf _ _ (h := E.isInvertibleModule i)
  restrict i := by
    obtain ⟨e⟩ := E.restrict i
    exact ⟨((Scheme.Modules.pullbackComp _ _).app _) ≪≫
      (Scheme.Modules.pullbackCongr (localEtaleFibreMap_restrictNeighborhood E U hU)).app _ ≪≫ e⟩

end Restrict

/-- An invertible module is isomorphic to the structure sheaf on a neighbourhood of every
point. -/
private theorem exists_pullback_ι_iso_unit {X : Scheme.{0}} (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : Scheme.{0}).ringCatSheaf) := by
  obtain ⟨I, Xi, hX, e⟩ :=
    (inferInstance : Stacks.SheafOfModules.Invertible.IsLocallyTrivial M).exists_trivializing_cover
  have hx : x ∈ ⨆ i, Xi i := by
    rw [(Opens.coversTop_iff X Xi).mp hX]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let W : X.Opens := Xi i
  exact ⟨W, hi, ⟨((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv W).app M).symm ≪≫
    (Scheme.Modules.overEquiv W).functor.mapIso (e i).some ≪≫
    TopologicalSpace.Opens.sheafOfModulesEquivOverUnit _ _⟩⟩

/-- The coefficient of `mapPrimeDivisors φ D` along a prime divisor `Q` whose only preimage
under `φ` is `P` is the coefficient of `D` along `P`. -/
private theorem coeff_mapPrimeDivisors_of_forall_eq_some_iff {X X' : Scheme.{0}}
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor X')}
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor X'}
    (h : ∀ F, φ F = some Q ↔ F = P) (D : Divisor X) :
    (DivisorWithCoeffs.mapPrimeDivisors φ D).coeff Q = D.coeff P := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; rfl
  | add D D' hD hD' =>
    rw [map_add, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hD, hD']
  | single F r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    by_cases hF : F = P
    · subst hF
      rw [(h F).mpr rfl]
      exact (DivisorWithCoeffs.coeff_single_self _ _).trans
        (DivisorWithCoeffs.coeff_single_self _ _).symm
    · rw [DivisorWithCoeffs.coeff_single_of_ne hF]
      cases hφ : φ F with
      | none => rfl
      | some F' =>
        have hne : F' ≠ Q := fun hQ ↦ hF ((h F).mp (hQ ▸ hφ))
        exact DivisorWithCoeffs.coeff_single_of_ne hne _

/-- An open immersion from an integral scheme sends its generic point outside the support of
every divisor. -/
private theorem map_componentGenericPoint_notMem_supp_of_isOpenImmersion {Z X : Scheme.{0}}
    [IsIntegral Z] (j : Z ⟶ X) [IsOpenImmersion j] (D : Divisor X)
    (C : irreducibleComponents Z) : j (componentGenericPoint Z C) ∉ D.supp := by
  intro hmem
  obtain ⟨P, -, hP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  have hmax : IsMax (componentGenericPoint Z C) := by
    rw [componentGenericPoint_eq_genericPoint]
    exact fun y _ ↦ (genericPoint_spec Z).specializes (Set.mem_univ y)
  have h0 : Order.coheight (j (componentGenericPoint Z C)) = 0 := by
    rw [coheight_eq_of_isOpenImmersion, Order.coheight_eq_zero]
    exact hmax
  have hsp : P.genericPoint ⤳ j (componentGenericPoint Z C) := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hP
  have hle := Order.coheight_anti (Scheme.le_iff_specializes.mpr hsp)
  rw [h0, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hle
  exact absurd hle (by norm_num)

/-- Over the smooth locus, `𝒪(A)` on `Ỹ_e` and `𝒪(A')` on `Y'` agree, for `A'` the transferred
divisor: both `π_e` and `g` are isomorphisms over `(Y_e)_reg`, under which the prime divisors
meeting it and their coefficients in `A` and `A'` correspond. -/
private theorem pullback_regularSection_divisorialSheaf_iso (E : LocalEtaleDatum sY T π L)
    [CompactSpace E.resolution]
    {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    (g : Y' ⟶ E.scheme) (hπe : IsBiregular E.resolutionMap (smoothLocus (E.map ≫ sY)))
    (hgR : IsBiregular g (smoothLocus (E.map ≫ sY))) (A : Divisor E.resolution)
    (hA : A.IsCartier) (hA' : (E.transferredDivisor g A).IsCartier) :
    Nonempty ((Scheme.Modules.pullback (regularSection (E.map ≫ sY) hπe)).obj
        A.divisorialSheaf ≅
      (Scheme.Modules.pullback (regularSection (E.map ≫ sY) hgR)).obj
        (E.transferredDivisor g A).divisorialSheaf) := by
  classical
  have hqp := E.isQuasiProjectiveVariety
  haveI := E.isNormal
  let R := smoothLocus (E.map ≫ sY)
  haveI : IsIntegral E.scheme := E.isQuasiProjectiveVariety.toIsVariety.toIsIntegral
  haveI : CompactSpace E.scheme := QuasiCompact.compactSpace_of_compactSpace (E.map ≫ sY)
  haveI : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian (E.map ≫ sY)
  haveI : IsNoetherian E.scheme := ⟨⟩
  haveI : CompactSpace (R : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (R : Set E.scheme))
  haveI : Nonempty (R : Scheme.{0}) := ⟨⟨genericPoint E.scheme, by
    change genericPoint E.scheme ∈ smoothLocus (E.map ≫ sY)
    rw [smoothLocus_eq_smoothLocus]
    exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField _⟩⟩
  haveI : IsIntegral (R : Scheme.{0}) := isIntegral_of_isOpenImmersion R.ι
  haveI : IsIso (E.resolutionMap ∣_ R) := hπe
  haveI : IsIso (g ∣_ R) := hgR
  let s := regularSection (E.map ≫ sY) hπe
  let σ := regularSection (E.map ≫ sY) hgR
  haveI : IsOpenImmersion s := by
    change IsOpenImmersion (inv (E.resolutionMap ∣_ R) ≫ (E.resolutionMap ⁻¹ᵁ R).ι)
    infer_instance
  haveI : IsOpenImmersion σ := by
    change IsOpenImmersion (inv (g ∣_ R) ≫ (g ⁻¹ᵁ R).ι)
    infer_instance
  have hs : s ≫ E.resolutionMap = R.ι := regularSection_comp _ hπe
  have hσ : σ ≫ g = R.ι := regularSection_comp _ hgR
  have hBs := map_componentGenericPoint_notMem_supp_of_isOpenImmersion s A
  have hBσ := map_componentGenericPoint_notMem_supp_of_isOpenImmersion σ
    (E.transferredDivisor g A)
  obtain ⟨e₁⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hA s hBs
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hA' σ hBσ
  suffices heq : A.pullback hA hBs = (E.transferredDivisor g A).pullback hA' hBσ from
    ⟨e₁.symm ≪≫ eqToIso (congrArg Divisor.divisorialSheaf heq) ≪≫ e₂⟩
  ext P
  have hco : ∀ {X : Scheme.{0}} (j : (R : Scheme.{0}) ⟶ X) [IsOpenImmersion j],
      Order.coheight (j P.genericPoint) = 1 := fun j _ ↦ by
    rw [coheight_eq_of_isOpenImmersion]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  let Q : MMP.Mori.PrimeDivisor E.resolution :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hco s)
  let Q' : MMP.Mori.PrimeDivisor Y' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hco σ)
  let Q₀ : MMP.Mori.PrimeDivisor E.scheme :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hco R.ι)
  have hQ : Q.genericPoint = s P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hQ' : Q'.genericPoint = σ P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hQ₀ : Q₀.genericPoint = R.ι P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  haveI : IsIso (s.stalkMap P.genericPoint) :=
    inferInstanceAs <| IsIso (s.toLRSHom.stalkMap P.genericPoint)
  haveI : IsIso (σ.stalkMap P.genericPoint) :=
    inferInstanceAs <| IsIso (σ.toLRSHom.stalkMap P.genericPoint)
  have hPR : R.ι P.genericPoint ∈ R := P.genericPoint.2
  have h₁ := MMP.Positivity.coeff_eq_of_isPullback P Q hQ.symm hA
    (Divisor.isPullback_pullback hA hBs)
  have h₂ := MMP.Positivity.coeff_eq_of_isPullback P Q' hQ'.symm hA'
    (Divisor.isPullback_pullback hA' hBσ)
  change (A.pullback hA hBs).coeff P = ((E.transferredDivisor g A).pullback hA' hBσ).coeff P
  rw [h₁, h₂]
  -- `g⁻¹_*` takes exactly `Q₀` to `Q'`
  have hgQ' : g Q'.genericPoint = Q₀.genericPoint := by
    rw [hQ', hQ₀, ← Scheme.Hom.comp_apply, hσ]
  have hinv : ∀ F, inverseTransformPrimeDivisor g F = some Q' ↔ F = Q₀ := by
    intro F
    constructor
    · intro hF
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hF).1.symm.trans hgQ')
    · rintro rfl
      refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hgQ' ?_
      rw [hgQ', hQ₀]
      exact le_biregularLocus hgR hPR
  -- `π_{e*}` takes exactly `Q` to `Q₀`
  haveI : IsSeparated (E.map ≫ sY) := inferInstance
  haveI : IsSeparated (E.scheme ↘ ⊤_ Scheme) := by
    rw [show (E.scheme ↘ ⊤_ Scheme) = (E.map ≫ sY) ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have htr : ∀ F, RationalMap.transformPrimeDivisor E.resolutionMap.toRationalMap F = some Q₀ ↔
      F = Q := by
    intro F
    rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff]
    constructor
    · intro hF
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [hQ₀] at hF
      have hmem : F.genericPoint ∈ E.resolutionMap ⁻¹ᵁ R := by
        change E.resolutionMap F.genericPoint ∈ R
        rw [hF]
        exact hPR
      let y : (E.resolutionMap ⁻¹ᵁ R : Scheme.{0}) := ⟨F.genericPoint, hmem⟩
      have hy : (E.resolutionMap ∣_ R) y = P.genericPoint := by
        apply R.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        exact hF
      change F.genericPoint = Q.genericPoint
      rw [hQ]
      change F.genericPoint = (E.resolutionMap ⁻¹ᵁ R).ι (inv (E.resolutionMap ∣_ R) P.genericPoint)
      rw [← hy, ← Scheme.Hom.comp_apply (E.resolutionMap ∣_ R),
        IsIso.hom_inv_id]
      rfl
    · rintro rfl
      rw [hQ, hQ₀, ← Scheme.Hom.comp_apply, hs]
  unfold transferredDivisor inverseTransformDivisor
  rw [coeff_mapPrimeDivisors_of_forall_eq_some_iff hinv]
  unfold RationalMap.transformDivisor
  rw [coeff_mapPrimeDivisors_of_forall_eq_some_iff htr]

/-- **(II) Comparison over the smooth locus.** Let `A` be a Cartier divisor on `Ỹ_e` whose
transferred divisor `A' = g⁻¹_* π_{e*} A` is Cartier, and suppose `𝒪(A')` is the pull-back of an
invertible sheaf `M` on a neighbourhood `U` of `η'`. Then `𝒪(A)` is trivial on the smooth locus
near every point of `U`: over `U ∩ (Y_e)_reg` both `π_e` and `g` are isomorphisms, under which
`A` and `A'` correspond, and `M` is locally trivial. -/
private theorem isRegularTrivial_of_isoPullback (hY : IsLocalSetting sY Θ T π)
    (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y']
    [CompactSpace Y'] (g : Y' ⟶ E.scheme) (D : Fin b → Divisor E.resolution)
    (hD : E.IsTransferSetting g D)
    (hπe : IsBiregular E.resolutionMap (smoothLocus (E.map ≫ sY))) (A : Divisor E.resolution)
    (hA : A.IsCartier) (hA' : (E.transferredDivisor g A).IsCartier) (U : E.scheme.Opens)
    (hU : E.point ∈ U) (M : (U : Scheme.{0}).Modules)
    (hM : Stacks.Ample.IsInvertibleModule _ M)
    (e : (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj (E.transferredDivisor g A).divisorialSheaf ≅
      (Scheme.Modules.pullback (g ∣_ U)).obj M) :
    IsRegularTrivial E hπe A := by
  have hgR : IsBiregular g (smoothLocus (E.map ≫ sY)) :=
    isBiregular_smoothLocus_of_isSmallMorphism _ _ g hD.isSmallMorphism hD.isProjectiveMorphism
  haveI : CompactSpace E.resolution := by
    have hqp := E.isQuasiProjectiveVariety
    have hπp : IsProjectiveMorphism π := hY.isResolution.2.2.2.1
    haveI : IsProper E.resolutionMap :=
      isProper_of_isProjectiveMorphism _ (hπp.baseChange E.map)
    haveI : IsIntegral E.scheme := E.isQuasiProjectiveVariety.toIsVariety.toIsIntegral
    haveI : CompactSpace E.scheme := QuasiCompact.compactSpace_of_compactSpace (E.map ≫ sY)
    exact QuasiCompact.compactSpace_of_compactSpace E.resolutionMap
  obtain ⟨eR⟩ := pullback_regularSection_divisorialSheaf_iso E g hπe hgR A hA hA'
  refine ⟨U, hU, fun y hy ↦ ?_⟩
  haveI := hM
  obtain ⟨W', hyW', ⟨eW⟩⟩ := exists_pullback_ι_iso_unit M ⟨y, hy⟩
  let R := smoothLocus (E.map ≫ sY)
  let W : E.scheme.Opens := U.ι ''ᵁ W'
  refine ⟨W, ⟨_, hyW', rfl⟩, ⟨?_⟩⟩
  let S : (R : Scheme.{0}).Opens := R.ι ⁻¹ᵁ W
  let σ := regularSection (E.map ≫ sY) hgR
  have hσ : σ ≫ g = R.ι := regularSection_comp _ hgR
  have hSW : ∀ s : (S : Scheme.{0}), R.ι (S.ι s) ∈ W := fun s ↦ s.2
  have hlr : Set.range (S.ι ≫ σ) ⊆ Set.range (g ⁻¹ᵁ U).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change g (σ (S.ι s)) ∈ U
    rw [← Scheme.Hom.comp_apply, hσ]
    obtain ⟨w, -, hw⟩ := hSW s
    rw [← hw]
    exact w.2
  let lam := IsOpenImmersion.lift (g ⁻¹ᵁ U).ι (S.ι ≫ σ) hlr
  have hlam : lam ≫ (g ⁻¹ᵁ U).ι = S.ι ≫ σ := IsOpenImmersion.lift_fac _ _ _
  have hνr : Set.range (lam ≫ (g ∣_ U)) ⊆ Set.range W'.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨w, hw, hwe⟩ := hSW s
    have h1 : U.ι ((lam ≫ (g ∣_ U)) s) = R.ι (S.ι s) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, morphismRestrict_ι, ← Category.assoc, hlam,
        Category.assoc, hσ]
      rfl
    have h2 : (lam ≫ (g ∣_ U)) s = w := U.ι.isOpenEmbedding.injective (h1.trans hwe.symm)
    rw [h2]
    exact hw
  let ν := IsOpenImmersion.lift W'.ι (lam ≫ (g ∣_ U)) hνr
  have hν : ν ≫ W'.ι = lam ≫ (g ∣_ U) := IsOpenImmersion.lift_fac _ _ _
  exact ((Scheme.Modules.pullbackComp S.ι _).app _).symm ≪≫
    (Scheme.Modules.pullback S.ι).mapIso eR ≪≫
    (Scheme.Modules.pullbackComp S.ι σ).app _ ≪≫
    (Scheme.Modules.pullbackCongr hlam.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp lam _).app _).symm ≪≫
    (Scheme.Modules.pullback lam).mapIso e ≪≫
    (Scheme.Modules.pullbackComp lam _).app _ ≪≫
    (Scheme.Modules.pullbackCongr hν.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp ν _).app _).symm ≪≫
    (Scheme.Modules.pullback ν).mapIso eW ≪≫
    Stacks.FundamentalGroup.pullbackUnitIso ν ≪≫
    (Stacks.FundamentalGroup.pullbackUnitIso _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (Divisor.divisorialSheafZeroIso).symm

/-- The curve `T' = closure {η'}` of a local étale datum is a curve: `κ(η') ≅ κ(η_T)` over `ℂ`,
`q` being étale with trivial residue field extension at `η'`, and `T` is a curve. -/
private theorem topologicalKrullDim_curveSubschemeAt_point (hY : IsLocalSetting sY Θ T π)
    (E : LocalEtaleDatum sY T π L) : topologicalKrullDim (curveSubschemeAt E.point) = 1 := by
  have hqp := E.isQuasiProjectiveVariety
  have hYv := hY.isProjectiveVariety
  haveI : LocallyOfFiniteType sY := inferInstance
  haveI : LocallyOfFiniteType (E.map ≫ sY) := hqp.toLocallyOfFiniteType
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq,
    topologicalKrullDim_closure_singleton_eq_trdeg ℂ E.scheme (E.map ≫ sY) E.point]
  have h3 := topologicalKrullDim_closure_singleton_eq_trdeg ℂ Y sY (E.map E.point)
  have hcl : closure ({E.map E.point} : Set Y) = T := by
    rw [E.map_point]
    exact (isGenericPoint_localSettingGenericPoint T).def
  rw [hcl, hY.topologicalKrullDim_curve] at h3
  rw [h3]
  letI : Algebra ℂ (Y.residueField (E.map E.point)) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sY.appTop ≫ Y.Γevaluation (E.map E.point)).hom.toAlgebra
  letI : Algebra ℂ (E.scheme.residueField E.point) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (E.map ≫ sY).appTop ≫
      E.scheme.Γevaluation E.point).hom.toAlgebra
  have hiso : IsIso (E.map.residueFieldMap E.point) := by
    have h : IsIso ((Y.residueFieldCongr E.map_point).inv ≫ E.map.residueFieldMap E.point) :=
      E.isIso_residueFieldMap
    exact IsIso.of_isIso_comp_left (Y.residueFieldCongr E.map_point).inv _
  let e : Y.residueField (E.map E.point) ≃ₐ[ℂ] E.scheme.residueField E.point :=
    { (asIso (E.map.residueFieldMap E.point)).commRingCatIsoToRingEquiv with
      commutes' := fun r ↦ by
        change (E.map.residueFieldMap E.point).hom
            (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sY.appTop ≫ Y.Γevaluation (E.map E.point)).hom r) =
          ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (E.map ≫ sY).appTop ≫
            E.scheme.Γevaluation E.point).hom r
        rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc,
          Scheme.Γevaluation_naturality, Scheme.Hom.comp_appTop, Category.assoc] }
  rw [e.trdeg_eq]

/-- **Relative numerical triviality near `η'`.** If `g` has curve fibres over `U₁ ∋ η'` and is an
isomorphism over `U₁ ∖ T'`, and the Cartier divisor `N` has degree zero on every curve of
`g⁻¹(η')`, then `N · C = 0` for every curve `C` contracted by `g` to a point of a smaller
neighbourhood `U₂` of `η'`. -/
private theorem exists_forall_intersectionNumber_eq_zero (hY : IsLocalSetting sY Θ T π)
    (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y']
    [CompactSpace Y'] (g : Y' ⟶ E.scheme) [QuasiCompact (g ≫ E.map ≫ sY)]
    (D : Fin b → Divisor E.resolution) (hD : E.IsTransferSetting g D) (U₁ : E.scheme.Opens)
    (hU₁ : E.point ∈ U₁)
    (hiso₁ : IsBiregular g (U₁ ⊓ ⟨(E.curve : Set E.scheme)ᶜ, E.curve.isClosed.isOpen_compl⟩))
    (hfib₁ : ∀ y ∈ U₁, topologicalKrullDim (g.base ⁻¹' {y}) ≤ 1) (N : Divisor Y')
    (hN : N.IsCartier) (hdegN : ∀ C, cartierFibreDegree E g C N hN = 0) :
    ∃ U₂ : E.scheme.Opens, U₂ ≤ U₁ ∧ E.point ∈ U₂ ∧
      ∀ C : ProperCurve (g ≫ E.map ≫ sY), C.IsContractedBy g → g C.point ∈ U₂ →
        (Divisor.toQDivisor N).intersectionNumber ℂ (g ≫ E.map ≫ sY) C.ι C.dim_le
          (QDivisor.isQCartier_toQDivisor hN) = 0 := by
  classical
  have hqp := E.isQuasiProjectiveVariety
  haveI : IsProper g := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism
  have hY' : MMP.Mori.IsVariety ℂ (g ≫ E.map ≫ sY) := hD.isSmallMorphism.isNormalVariety_source.1
  have hYe : MMP.Mori.IsVariety ℂ (E.map ≫ sY) := hD.isSmallMorphism.isNormalVariety_target.1
  have hfibη : topologicalKrullDim (g.fiber E.point) ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo E.point).isHomeomorph]
    exact hfib₁ E.point hU₁
  have hD' := QDivisor.isQCartier_toQDivisor hN
  refine intersectionNumber_eq_zero_of_degreeOn_fiber_eq_zero_of_isBiregular hY' hYe rfl hfibη U₁ hU₁
    hiso₁ hD' fun C ↦ ?_
  let c : ℤ := ((Divisor.toQDivisor N).cartierIndex hD' : ℕ)
  have hNc : (QDivisor.isCartierDivisor_cartierIndex_smul hD').toDivisor = c • N := by
    apply Divisor.toQDivisor_injective
    rw [(QDivisor.isCartierDivisor_cartierIndex_smul hD').toQDivisor_toDivisor, map_zsmul]
  have hz : cartierFibreDegree E g C _
      (QDivisor.isCartierDivisor_cartierIndex_smul hD').isCartier_toDivisor = 0 := by
    rw [cartierFibreDegree_congr E g C hNc _ (hN.zsmul c)]
    have h := map_zsmul (cartierFibreDegreeHom E g C) c ⟨N, Divisor.mem_cartierSubgroup.mpr hN⟩
    rw [cartierFibreDegreeHom_apply, cartierFibreDegreeHom_apply] at h
    refine h.trans ?_
    show c • cartierFibreDegree E g C N hN = 0
    rw [hdegN C, smul_zero]
  exact hz

/-- The fibres of `f ∣_ U` are those of `f` over the points of `U`. -/
private theorem topologicalKrullDim_fiber_morphismRestrict {X Z : Scheme.{0}} (f : X ⟶ Z)
    (U : Z.Opens) (y : (U : Scheme.{0})) :
    topologicalKrullDim ((f ∣_ U).fiber y) = topologicalKrullDim (f.base ⁻¹' {U.ι y}) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ ((f ∣_ U).fiberHomeo y).isHomeomorph]
  have hfx : ∀ x : (f ⁻¹ᵁ U : Scheme.{0}), (f ∣_ U) x = y ↔ f ((f ⁻¹ᵁ U).ι x) = U.ι y :=
    fun x ↦ by
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
      exact U.ι.isOpenEmbedding.injective.eq_iff.symm
  have h1 : Topology.IsEmbedding (fun x : ↥((f ∣_ U) ⁻¹' {y}) ↦ (f ⁻¹ᵁ U).ι x.1) :=
    (f ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hφ := h1.codRestrict (f.base ⁻¹' {U.ι y}) fun x ↦ (hfx x.1).mp x.2
  refine IsHomeomorph.topologicalKrullDim_eq _ ((isHomeomorph_iff_isEmbedding_surjective).mpr
    ⟨hφ, fun z ↦ ?_⟩)
  have hz : z.1 ∈ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    change f z.1 ∈ U
    rw [show f z.1 = U.ι y from z.2]
    exact y.2
  obtain ⟨w, hw⟩ := hz
  exact ⟨⟨w, (hfx w).mpr (by rw [hw]; exact z.2)⟩, Subtype.ext hw⟩

/-- The restriction `f ∣_ U` of a birational morphism of integral schemes over an open `U` with
nonempty preimage is birational: it is an open immersion on the trace of a nonempty open on which
`f` is one. -/
private theorem isBirationalMorphism_morphismRestrict {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {f : Y ⟶ X} (hf : IsBirationalMorphism f) (U : X.Opens)
    [Nonempty (f ⁻¹ᵁ U : Scheme.{0})] : IsBirationalMorphism (f ∣_ U) := by
  obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty (f ⁻¹ᵁ U : Scheme.{0})›
  haveI : Nonempty (U : Scheme.{0}) := ⟨⟨f y, hy⟩⟩
  haveI : IsIntegral (f ⁻¹ᵁ U : Scheme.{0}) := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  haveI : IsIntegral (U : Scheme.{0}) := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨W, hWne, hW⟩ := hf.exists_isOpenImmersion
  let S : (f ⁻¹ᵁ U : Scheme.{0}).Opens := (f ⁻¹ᵁ U).ι ⁻¹ᵁ W
  have hSne : (S : Set (f ⁻¹ᵁ U : Scheme.{0})).Nonempty := by
    obtain ⟨z, hzU, hzW⟩ := (W.isOpen.dense hWne).inter_open_nonempty _ (f ⁻¹ᵁ U).isOpen ⟨y, hy⟩
    exact ⟨⟨z, hzU⟩, hzW⟩
  have hrange : Set.range (S.ι ≫ (f ⁻¹ᵁ U).ι) ⊆ Set.range W.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let h := IsOpenImmersion.lift W.ι (S.ι ≫ (f ⁻¹ᵁ U).ι) hrange
  have hg : (S.ι ≫ f ∣_ U) ≫ U.ι = h ≫ W.ι ≫ f := by
    simp only [h, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc]
  haveI : IsOpenImmersion ((S.ι ≫ f ∣_ U) ≫ U.ι) := by rw [hg]; infer_instance
  haveI : IsOpenImmersion (S.ι ≫ f ∣_ U) := IsOpenImmersion.of_comp _ U.ι
  exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' (f ∣_ U) S hSne

/-- A Cartier divisor of degree zero on every curve contracted by `f` is numerically
`f`-trivial. -/
private theorem isNumericallyTrivialOver_of_degreeOn_eq_zero {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Z)
    (N : Divisor X) (hN : N.IsCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f → N.degreeOn ℂ sX C.ι C.dim_le hN = 0) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sX f (QDivisor.toRDivisor (Divisor.toQDivisor N)) := by
  have hR : QDivisor.toRDivisor (Divisor.toQDivisor N) =
      ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor N := by
    rw [QDivisor.toRDivisor_toQDivisor, Fin.sum_univ_one, one_smul]
  unfold MMP.Flips.IsNumericallyTrivialOver MMP.Flips.IsNumericallyEquivalentOver
  refine ⟨⟨1, fun _ ↦ 1, fun _ ↦ N, fun _ ↦ hN, hR.trans rfl⟩,
    ⟨0, finZeroElim, finZeroElim, finZeroElim, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ ↦ ?_⟩
  have hcan : MMP.Flips.IsRIntersectionNumber ℂ sX (QDivisor.toRDivisor (Divisor.toQDivisor N))
      (fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ ↦ N) C (N.degreeOn ℂ sX C.ι C.dim_le hN : ℝ) :=
    ⟨fun _ ↦ hN, fun _ ↦ N.degreeOn ℂ sX C.ι C.dim_le hN, hR,
      fun _ ↦ MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX C N hN, by simp⟩
  have hzero : MMP.Flips.IsRIntersectionNumber ℂ sX (0 : RDivisor X) (finZeroElim : Fin 0 → ℝ)
      (finZeroElim : Fin 0 → Divisor X) C 0 :=
    ⟨finZeroElim, finZeroElim, by simp, finZeroElim, by simp⟩
  have e₁ := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hcan
  have e₂ := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂ hzero
  rw [e₁, e₂, h C hC, Int.cast_zero]

/-- The restriction of a Cartier divisor to an open of the source has degree zero on the curves
contracted by `f ∣_ U`, if the divisor is numerically trivial on the curves contracted by `f` to
points of `U`: such a curve is a curve of `X` with the same intersection numbers. -/
private theorem degreeOn_restrictOpen_eq_zero {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [QuasiCompact sX] [IsSeparated sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (f : X ⟶ Z) (U : Z.Opens) [Nonempty (f ⁻¹ᵁ U : Scheme.{0})]
    (s₂ : (f ⁻¹ᵁ U : Scheme.{0}) ⟶ Spec (.of ℂ)) (hs₂ : s₂ = (f ⁻¹ᵁ U).ι ≫ sX) [QuasiCompact s₂]
    (N : Divisor X) (hN : N.IsCartier) (hN₂ : Divisor.IsCartier (N.restrictOpen (f ⁻¹ᵁ U)))
    (hnum : ∀ C : ProperCurve sX, C.IsContractedBy f → f C.point ∈ U →
      (Divisor.toQDivisor N).intersectionNumber ℂ sX C.ι C.dim_le
        (QDivisor.isQCartier_toQDivisor hN) = 0)
    (C : ProperCurve s₂) (hC : C.IsContractedBy (f ∣_ U)) :
    Divisor.degreeOn ℂ s₂ C.ι C.dim_le (N.restrictOpen (f ⁻¹ᵁ U)) hN₂ = 0 := by
  subst hs₂
  obtain ⟨v⟩ := ‹Nonempty (f ⁻¹ᵁ U : Scheme.{0})›
  haveI : IsIntegral (f ⁻¹ᵁ U : Scheme.{0}) := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  haveI : IsNoetherian X := ⟨⟩
  haveI : CompactSpace (f ⁻¹ᵁ U : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (f ⁻¹ᵁ U : Set X))
  haveI : IsDominant (f ⁻¹ᵁ U).ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact (f ⁻¹ᵁ U).isOpen.dense ⟨_, v.2⟩⟩
  obtain ⟨Γ, e, hΓ, he⟩ := MMP.Flips.exists_properCurve_of_opens sX (f ⁻¹ᵁ U) C
  have hres : (Divisor.toQDivisor N).restrictOpen (f ⁻¹ᵁ U) =
      Divisor.toQDivisor (N.restrictOpen (f ⁻¹ᵁ U)) := by
    ext P
    rfl
  have hLU : QDivisor.IsQCartier ((Divisor.toQDivisor N).restrictOpen (f ⁻¹ᵁ U)) :=
    hres ▸ QDivisor.isQCartier_toQDivisor hN₂
  have hI := MMP.Flips.intersectionNumber_restrictOpen_of_iso sX (f ⁻¹ᵁ U) (Divisor.toQDivisor N)
    (QDivisor.isQCartier_toQDivisor hN) hLU C Γ e he
  -- `Γ` is contracted by `f` to a point of `U`
  have hrange : closure ({Γ.point} : Set X) = (f ⁻¹ᵁ U).ι '' closure {C.point} := by
    rw [← ProperCurve.range_ι, ← ProperCurve.range_ι]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := e.hom.homeomorph.surjective y
      exact ⟨C.ι z, ⟨z, rfl⟩, by
        rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]
        rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨e.hom z, by rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]⟩
  have hfΓ : ∀ c : (f ⁻¹ᵁ U : Scheme.{0}), f ((f ⁻¹ᵁ U).ι c) = U.ι ((f ∣_ U) c) := fun c ↦ by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  have hΓc : Γ.IsContractedBy f := by
    intro x hx
    rw [hrange] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [hΓ, hfΓ, hfΓ, hC c hc]
  have hΓU : f Γ.point ∈ U := by
    rw [hΓ, hfΓ]
    exact ((f ∣_ U) C.point).2
  rw [hnum Γ hΓc hΓU] at hI
  have h1 := QDivisor.intersectionNumber_eq_of_smul ℂ ((f ⁻¹ᵁ U).ι ≫ sX) C.ι C.dim_le _ hLU
    one_pos (N.restrictOpen (f ⁻¹ᵁ U)) hN₂ (by rw [hres, Nat.cast_one, one_smul])
  rw [h1, Nat.cast_one, div_one] at hI
  exact_mod_cast hI

/-- **Cartier descent near `η'`.** If `g` has curve fibres over `U₂ ∋ η'` and the Cartier divisor
`N` is numerically trivial on the curves contracted to points of `U₂`, then over `U₂` the sheaf
`𝒪(N)` is the pull-back of an invertible sheaf on `U₂`: restrict the étale datum to `U₂` and `g`
to `g ∣_ U₂`, which is projective, birational and has curve fibres; `N|_{g⁻¹U₂}` is numerically
`g ∣_ U₂`-trivial, the curves of `g⁻¹U₂` being curves of `Y'` with the same intersection numbers;
apply the Cartier descent on the small model, and identify `𝒪(N|_{g⁻¹U₂})` with `𝒪(N)|_{g⁻¹U₂}`. -/
private theorem exists_isoPullback_of_forall_intersectionNumber_eq_zero
    (hY : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (g : Y' ⟶ E.scheme)
    [QuasiCompact (g ≫ E.map ≫ sY)] (D : Fin b → Divisor E.resolution)
    (hD : E.IsTransferSetting g D) (U₂ : E.scheme.Opens) (hU₂ : E.point ∈ U₂)
    (hfib₂ : ∀ y ∈ U₂, topologicalKrullDim (g.base ⁻¹' {y}) ≤ 1) (N : Divisor Y')
    (hN : N.IsCartier)
    (hnum : ∀ C : ProperCurve (g ≫ E.map ≫ sY), C.IsContractedBy g → g C.point ∈ U₂ →
      (Divisor.toQDivisor N).intersectionNumber ℂ (g ≫ E.map ≫ sY) C.ι C.dim_le
        (QDivisor.isQCartier_toQDivisor hN) = 0) :
    ∃ (M : (U₂ : Scheme.{0}).Modules) (_ : Stacks.Ample.IsInvertibleModule _ M),
      Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U₂).ι).obj N.divisorialSheaf ≅
        (Scheme.Modules.pullback (g ∣_ U₂)).obj M) := by
  classical
  have hqp := E.isQuasiProjectiveVariety
  haveI := hD.isSmallMorphism.isNormalVariety_source.1
  haveI : IsIntegral Y' := hD.isSmallMorphism.isNormalVariety_source.1.toIsIntegral
  haveI : IsIntegral E.scheme := E.isQuasiProjectiveVariety.toIsVariety.toIsIntegral
  have hb : IsBirationalMorphism g := hD.isSmallMorphism.isBirationalMorphism
  let E₂ := restrictOpen E U₂ hU₂
  let V : Y'.Opens := g ⁻¹ᵁ U₂
  let g₂ : (V : Scheme.{0}) ⟶ E₂.scheme := g ∣_ U₂
  haveI : Nonempty (V : Scheme.{0}) := by
    haveI := hb.isDominant
    obtain ⟨y, hy⟩ := g.denseRange.exists_mem_open U₂.isOpen ⟨E.point, hU₂⟩
    exact ⟨⟨y, hy⟩⟩
  haveI : IsNoetherian Y' := ⟨⟩
  haveI : CompactSpace (V : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (V : Set Y'))
  haveI : QuasiCompact (g₂ ≫ E₂.map ≫ sY) := by
    change QuasiCompact ((g ∣_ U₂) ≫ (U₂.ι ≫ E.map) ≫ sY)
    rw [← Category.assoc, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc]
    infer_instance
  have hg₂ : IsProjectiveMorphism g₂ := by
    change IsProjectiveMorphism (g ∣_ U₂)
    obtain ⟨m, i, hi, hif⟩ := hD.isProjectiveMorphism.baseChange U₂.ι
    exact ⟨m, (pullbackRestrictIsoRestrict g U₂).inv ≫ i, inferInstance, by
      rw [Category.assoc, hif]; rfl⟩
  have hb₂ : IsBirationalMorphism g₂ := isBirationalMorphism_morphismRestrict hb U₂
  have hfib₂' : ∀ y : E₂.scheme, topologicalKrullDim (g₂.fiber y) ≤ 1 := fun y ↦ by
    change topologicalKrullDim ((g ∣_ U₂).fiber y) ≤ 1
    rw [topologicalKrullDim_fiber_morphismRestrict g U₂ y]
    exact hfib₂ (U₂.ι y) y.2
  let N₂ : Divisor (V : Scheme.{0}) := N.restrictOpen V
  haveI : IsIntegral (V : Scheme.{0}) := isIntegral_of_isOpenImmersion V.ι
  haveI : IsDominant V.ι := ⟨by
    obtain ⟨v⟩ := ‹Nonempty (V : Scheme.{0})›
    rw [DenseRange, Scheme.Opens.range_ι]
    exact V.isOpen.dense ⟨_, v.2⟩⟩
  have hN₂ : N₂.IsCartier :=
    Divisor.IsPullback.isCartier (MMP.Flips.isPullback_restrictOpen V hN) hN
  haveI : IsSeparated (g ≫ E.map ≫ sY) := hD.isSmallMorphism.isNormalVariety_source.1.toIsSeparated
  have hs₂ : g₂ ≫ E₂.map ≫ sY = V.ι ≫ g ≫ E.map ≫ sY := by
    change (g ∣_ U₂) ≫ (U₂.ι ≫ E.map) ≫ sY = _
    rw [← Category.assoc, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc]
  have hnum₂ : MMP.Flips.IsNumericallyTrivialOver ℂ (g₂ ≫ E₂.map ≫ sY) g₂
      (QDivisor.toRDivisor (Divisor.toQDivisor N₂)) :=
    isNumericallyTrivialOver_of_degreeOn_eq_zero _ g₂ N₂ hN₂ fun C hC ↦
      degreeOn_restrictOpen_eq_zero (g ≫ E.map ≫ sY) g U₂ _ hs₂ N hN hN₂ hnum C hC
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    MMP.Fourfold.LocalEtaleDatum.exists_isInvertibleModule_divisorialSheaf_iso_pullback hY E₂ g₂ hg₂
    hb₂ hfib₂' (Divisor.toQDivisor N₂) (QDivisor.isQCartier_toQDivisor hN₂) hnum₂ 1 one_pos N₂ hN₂
    (by rw [Nat.cast_one, one_smul])
  exact ⟨M, hM, ⟨((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫
    (MMP.Mori.Divisor.divisorialSheafRestrictOpenIso N V).symm ≪≫ e⟩⟩

/-- **(III) Descent.** An integral relation `∑ n_i (D'_i · C) = 0` on the curves of `g⁻¹(η')`
makes a positive multiple `N = k ∑ n_i D'_i` Cartier and the pull-back of an invertible sheaf
near `η'`: shrink `Y_e` so that `g` has curve fibres and is an isomorphism off `T'`, make `N`
numerically `g`-trivial there, and apply the Cartier descent on the small model. -/
private theorem exists_isoPullback_of_fibreDegree (hY : IsLocalSetting sY Θ T π)
    (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y']
    [CompactSpace Y'] (g : Y' ⟶ E.scheme) (D : Fin b → Divisor E.resolution)
    (hD : E.IsTransferSetting g D) (hQ : IsQFactorial (g ≫ E.map ≫ sY)) (n : Fin b → ℤ)
    (hdeg : ∀ C, ∑ i, (n i : ℚ) * fibreDegree E g hQ (D i) C = 0) :
    ∃ k : ℕ, 0 < k ∧
      (E.transferredDivisor g (∑ i, (k * n i) • D i)).IsCartier ∧
      ∃ (U : E.scheme.Opens) (_ : E.point ∈ U) (M : (U : Scheme.{0}).Modules)
        (_ : Stacks.Ample.IsInvertibleModule _ M),
        Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj
            (E.transferredDivisor g (∑ i, (k * n i) • D i)).divisorialSheaf ≅
          (Scheme.Modules.pullback (g ∣_ U)).obj M) := by
  classical
  -- a positive multiple of `∑ n_i D'_i` is Cartier, `Y'` being `ℚ`-factorial
  obtain ⟨k, hk, hkC⟩ := hQ.2 (E.transferredDivisor g (∑ i, n i • D i))
  have hNk : E.transferredDivisor g (∑ i, (k * n i) • D i) =
      (k : ℤ) • E.transferredDivisor g (∑ i, n i • D i) := by
    simp only [transferredDivisor, map_sum, map_zsmul, Finset.smul_sum, mul_smul]
  refine ⟨k, hk, hNk ▸ hkC, ?_⟩
  -- shrink `Y_e` so that `g` has curve fibres and is an isomorphism off `T'`
  obtain ⟨U₁, hU₁, -, hiso₁, hfib₁⟩ :=
    exists_isBiregular_compl_curve_of_isSmallMorphism hY E g hD.isSmallMorphism
      hD.isProjectiveMorphism
  have hqp := E.isQuasiProjectiveVariety
  haveI : IsProper g := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism
  haveI : QuasiCompact (g ≫ E.map ≫ sY) := inferInstance
  set N := E.transferredDivisor g (∑ i, (k * n i) • D i) with hNdef
  have hNC : N.IsCartier := hNk ▸ hkC
  -- `N` has degree zero on the curves of `g⁻¹(η')`
  have hdegN : ∀ C, cartierFibreDegree E g C N hNC = 0 := fun C ↦
    cartierFibreDegree_eq_zero_of_fibreDegree E g hQ D n C (hdeg C) k N hNC (by
      simp only [hNdef, transferredDivisor, map_sum, map_zsmul, Finset.smul_sum, mul_smul])
  -- relative numerical triviality on a smaller neighbourhood, and descent there
  obtain ⟨U₂, hU₂₁, hU₂, hnum⟩ :=
    exists_forall_intersectionNumber_eq_zero hY E g D hD U₁ hU₁ hiso₁ hfib₁ N hNC hdegN
  obtain ⟨M, hM, hMe⟩ := exists_isoPullback_of_forall_intersectionNumber_eq_zero hY E g D hD U₂
    hU₂ (fun y hy ↦ hfib₁ y (hU₂₁ hy)) N hNC hnum
  exact ⟨U₂, hU₂, M, hM, hMe⟩

/-- **Integral degree independence.** An integral relation `∑ n_i (D'_i · C) = 0` on every curve
`C` of the fibre `g⁻¹(η')` is trivial: a positive multiple of `∑ n_i D'_i` descends near `η'`
(`exists_isoPullback_of_fibreDegree`), so `𝒪(k ∑ n_i D̃_i)` is trivial on the smooth locus near
`η'` (`isRegularTrivial_of_isoPullback`), which the étale independence of the punctured classes
forbids unless `k n = 0` (`eq_zero_of_isRegularTrivial`). -/
private theorem eq_zero_of_fibreDegree (hY : IsLocalSetting sY Θ T π)
    (hL : IsPuncturedIndependent sY hY.isBiregular L) (E : LocalEtaleDatum sY T π L)
    {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    (g : Y' ⟶ E.scheme) (D : Fin b → Divisor E.resolution) (hD : E.IsTransferSetting g D)
    (hQ : IsQFactorial (g ≫ E.map ≫ sY)) (n : Fin b → ℤ)
    (hdeg : ∀ C, ∑ i, (n i : ℚ) * fibreDegree E g hQ (D i) C = 0) : n = 0 := by
  have hπe := (exists_dense_linearIndependent_chernClass hY hL E).choose
  obtain ⟨k, hk, hN, U, hU, M, hM, ⟨e⟩⟩ :=
    exists_isoPullback_of_fibreDegree hY E g D hD hQ n hdeg
  have hA : (∑ j, (k * n j) • D j).IsCartier :=
    Divisor.cartierSubgroup.sum_mem fun j _ ↦
      Divisor.cartierSubgroup.zsmul_mem (Divisor.mem_cartierSubgroup.mpr (hD.isCartier j)) _
  have h0 := eq_zero_of_isRegularTrivial hY hL E D hD.isCartier hD.divisorialSheaf_iso hπe
    (fun j ↦ k * n j) (isRegularTrivial_of_isoPullback hY E g D hD hπe _ hA hN U hU M hM e)
  funext i
  have hki : (k : ℤ) * n i = 0 := congrFun h0 i
  exact (mul_eq_zero.mp hki).resolve_left (by exact_mod_cast hk.ne')

end MMP.OAI4LocalDegreeIndependence

namespace MMP.Fourfold.LocalEtaleDatum

/-- For a local setting `(Y, Θ, T, π)`, a punctured-independent family `L_1, …, L_b` on
`F_{η_T}`, a local étale datum `E` for it, a projective small birational morphism
`g : Y' ⟶ Y_e` with `Y'` `ℚ`-factorial, and Cartier divisors `D̃_i` on `Ỹ_e` with
`𝒪(D̃_i) ≅ L̃_i`, the vectors `(D'_i · C)_C` of degrees over `κ(η')` of the transferred divisors
`D'_i = E.transferredDivisor g (D̃ i)` on the curves `C` of the fibre `g⁻¹(η')` are linearly
independent over `ℚ`. -/
@[mmp "lem_oai4_local_degree_independence"]
public theorem linearIndependent_transferredDivisor_degree
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Yt] [IsNormal Yt]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ} {L : Fin b → (genericFibre π T).Modules}
    (hL : IsPuncturedIndependent sY hY.isBiregular L)
    (E : LocalEtaleDatum sY T π L)
    {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    (g : Y' ⟶ E.scheme) (D : Fin b → Divisor E.resolution) (hD : E.IsTransferSetting g D)
    (hQ : IsQFactorial (g ≫ E.map ≫ sY)) :
    LinearIndependent ℚ fun i (C : ProperCurve (g.fiberToSpecResidueField E.point)) ↦
      let D' := Divisor.toQDivisor (E.transferredDivisor g (D i))
      let hD' := isQCartier_of_isQFactorial _ hQ D'
      haveI := (QDivisor.isCartierDivisor_cartierIndex_smul hD').isCartier_toDivisor
        |>.isInvertibleModule_divisorialSheaf
      haveI : IsProper (C.ι ≫ g.fiberToSpecResidueField E.point) := C.isProperCurve.isProper
      ((degreeOn (E.scheme.residueField E.point) (g.fiberToSpecResidueField E.point) C.ι
          C.dim_le ((Scheme.Modules.pullback (g.fiberι E.point)).obj
            (QDivisor.isCartierDivisor_cartierIndex_smul hD').toDivisor.divisorialSheaf) : ℚ) /
        D'.cartierIndex hD') := by
  change LinearIndependent ℚ fun i C ↦
    MMP.OAI4LocalDegreeIndependence.fibreDegree E g hQ (D i) C
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ, Fintype.linearIndependent_iff]
  intro n hn i
  refine congrFun (MMP.OAI4LocalDegreeIndependence.eq_zero_of_fibreDegree
    hY hL E g D hD hQ n fun C ↦ ?_) i
  simpa [Finset.sum_apply, zsmul_eq_mul] using congrFun hn C

end MMP.Fourfold.LocalEtaleDatum
