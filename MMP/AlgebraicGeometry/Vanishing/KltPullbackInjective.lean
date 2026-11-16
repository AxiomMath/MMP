module

public import MMP.AlgebraicGeometry.Singularities.LogResolution.RoundUpPushforward
public import MMP.AlgebraicGeometry.Vanishing.KltLogResolutionDirectImage
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary

/-!
# Injectivity of pull-back on cohomology along a log resolution of a klt pair

Let `(X, Δ)` be a klt pair with `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective, and let `f : Y ⟶ X` be a projective log resolution of
`(X, Δ)`. For every Cartier divisor `D` on `X` (in particular `D = -rL` for a Cartier divisor `L`
and an integer `r`) the pull-back
`f^* : H^i(X, 𝒪_X(D)) ⟶ H^i(Y, f^*𝒪_X(D))` is injective for every `i`; here the target is
written as `H^i(X, Rf_* f^*𝒪_X(D))`, which is `H^i(Y, f^*𝒪_X(D))` by Leray.

With `B = B_f` the positive part of the discrepancy and `ℱ = 𝒪_Y(⌈B⌉) ⊗ f^*𝒪_X(D)`, the
projection formula together with `R^j f_* 𝒪_Y(⌈B⌉) = 0` for `j > 0`
(`MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_roundUp`) and
`f_* 𝒪_Y(⌈B⌉) = 𝒪_X` (`MMP.Mori.isIso_pushforward_structureSheafToDivisorialSheaf_roundUp`)
show that the Leray edge map `H^i(X, 𝒪_X(D)) ⟶ H^i(Y, ℱ)` is an isomorphism. It factors as
`f^*` followed by the map induced by `f^*𝒪_X(D) ⊆ ℱ`, so `f^*` is injective.

## Main results

* `MMP.Mori.injective_derivedCohomologyOverField_pullback_divisorialSheaf_of_isKltPair`: the
  pull-back `H^i(X, 𝒪_X(D)) ⟶ H^i(X, Rf_* f^*𝒪_X(D)) = H^i(Y, f^*𝒪_X(D))` is injective.

## Implementation notes

* `X` carries its structure morphism `sX : X ⟶ Spec k`. A projective log resolution is
  `MMP.Mori.IsLogResolution` of the `ℝ`-divisor underlying `Δ` together with
  `AlgebraicGeometry.IsProjective f`.
* `H^i(X, K)` for `i : ℤ` and `K ∈ D(𝒪_X)` is the `i`-th cohomology of
  `AlgebraicGeometry.derivedGlobalSectionsOver sX`, so that `H^i(X, ℱ)` is
  `Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree zero.
* The pull-back is the map `H^i(X, ℱ) ⟶ H^i(X, Rf_*(f^*ℱ))` induced by the unit
  `ℱ ⟶ f_* f^*ℱ` of `f^* ⊣ f_*` followed by the comparison `(f_* 𝒢)[0] ⟶ Rf_*(𝒢[0])` of the
  derived direct image `Stacks.Duality.derivedPushforward f` with the underived one. Its target
  is identified with `H^i(Y, f^*ℱ)` by the Leray isomorphism `RΓ(X, Rf_* -) ≅ RΓ(Y, -)`, which
  does not affect injectivity.
* The coefficients on `Y` are the module pull-back `f^*𝒪_X(D)` rather than `𝒪_Y(f^*D)`; the two
  are identified by the canonical isomorphism `f^*𝒪_X(D) ≅ 𝒪_Y(f^*D)`, which again does not
  affect injectivity.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Theorem 5.22.
-/

@[expose] public section

section

/-!
## Proof: Injectivity of pull-back on cohomology along a log resolution of a klt pair

Let `(X, Δ)` be a klt pair, `f : Y ⟶ X` a projective log resolution, `B = B_f` the positive part
of the discrepancy and `𝒪_X(D)` invertible. With `ℋ = 𝒪_Y(⌈B⌉) ⊗ f^*𝒪_X(D)` and
`ι : f^*𝒪_X(D) ⟶ ℋ` induced by `𝒪_Y ⊆ 𝒪_Y(⌈B⌉)`:

* the composite `𝒪_X(D) ⟶ f_* f^*𝒪_X(D) ⟶ f_* ℋ` is the twist by `𝒪_X(D)` of the isomorphism
  `𝒪_X ⟶ f_* 𝒪_Y(⌈B⌉)` followed by the projection formula, hence an isomorphism;
* `R^q f_* ℋ = R^q f_* 𝒪_Y(⌈B⌉) ⊗ 𝒪_X(D) = 0` for `q > 0`, so the comparison
  `(f_* ℋ)[0] ⟶ Rf_*(ℋ[0])` is an isomorphism.

By naturality of the comparison, the map `𝒪_X(D)[0] ⟶ Rf_*(f^*𝒪_X(D)[0])` followed by
`Rf_*(ι[0])` is an isomorphism, so the former is a split monomorphism in `D(𝒪_X)` and stays
injective after `H^i(X, -)`. This is the Leray edge-map argument of the source, read in the
derived category.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Theorem 5.22.
-/

namespace MMP.FourfoldProofs.Km5dKltPullbackInjectiveProof

open CategoryTheory CategoryTheory.Limits MMP.Mori
open AlgebraicGeometry hiding IsProjectiveVariety
open scoped Stacks.SmallDerivedModel

section ProjectionFormula

open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.AffineProjectionFormula
open scoped CategoryTheory.Prod

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf PresheafOfModules.tensorObj
  Stacks.SheafOfModules.Tensor.ringSheaf

/-- The unit `L ⟶ f_* f^* L` followed by `f_*` of `f^*L ≅ 𝒪_Z ⊗ f^*L ⟶ M ⊗ f^*L`, for a map
`j : 𝒪_Z ⟶ M`, is the twist by `L` of `𝒪_X ⟶ f_* 𝒪_Z ⟶ f_* M` followed by the projection
formula map `f_* M ⊗ L ⟶ f_*(M ⊗ f^* L)`. -/
private theorem unit_comp_pushforward_map_tensor_eq {X Z : RingedSpace.{0, 0}} (f : Z ⟶ X)
    (L : SheafOfModules.{0} (structureRingSheaf X)) (M : SheafOfModules.{0} (structureRingSheaf Z))
    (j : structureModule Z ⟶ M) :
    (pullbackAdjunction f).unit.app L ≫ (pushforwardFunctor f).map
        ((structureUnitor ((pullbackFunctor f).obj L)).inv ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
            Z.sheaf)).map (j ×ₘ 𝟙 ((pullbackFunctor f).obj L))) =
      (structureUnitor L).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
          X.sheaf)).map ((unitToPushforwardStructure f ≫ (pushforwardFunctor f).map j) ×ₘ 𝟙 L) ≫
        projectionFormulaMap f M L := by
  have h2 := projectionFormulaMap_natural f j (𝟙 L)
  rw [(pullbackFunctor f).map_id] at h2
  have h1' : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        X.sheaf)).map (unitToPushforwardStructure f ×ₘ 𝟙 L) ≫
        projectionFormulaMap f (structureModule Z) L =
      ((structureUnitor L).hom ≫ (pullbackAdjunction f).unit.app L) ≫
        ((pushforwardFunctor f).mapIso (structureUnitor ((pullbackFunctor f).obj L))).inv := by
    rw [Iso.eq_comp_inv, ← tensorSheaf_map_unitToPushforwardStructure_comp_projection f L]
    simp only [Functor.mapIso_hom, Category.assoc]
  have hsplit : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        X.sheaf)).map ((unitToPushforwardStructure f ≫ (pushforwardFunctor f).map j) ×ₘ 𝟙 L) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        X.sheaf)).map (unitToPushforwardStructure f ×ₘ 𝟙 L) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        X.sheaf)).map ((pushforwardFunctor f).map j ×ₘ 𝟙 L) := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg _ (CategoryTheory.Prod.hom_ext rfl (Category.comp_id (𝟙 L)).symm)
  rw [hsplit, Category.assoc, h2, ← Category.assoc _ (projectionFormulaMap f _ L), h1']
  simp only [Functor.mapIso_inv, Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]

/-- Let `f : Y ⟶ X` be a morphism of schemes, `N` an invertible `𝒪_X`-module and `j : 𝒪_Y ⟶ M`
a map of `𝒪_Y`-modules such that `𝒪_X ⟶ f_* 𝒪_Y ⟶ f_* M` is an isomorphism. Then the unit
`N ⟶ f_* f^* N` followed by `f_*` of `f^*N ≅ 𝒪_Y ⊗ f^*N ⟶ M ⊗ f^*N` is an isomorphism
`N ≅ f_*(M ⊗ f^* N)`. -/
private theorem isIso_unit_comp_pushforward_map_tensor {X Y : Scheme.{0}} (f : Y ⟶ X)
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] (M : Y.Modules)
    (j : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (hj : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward f).map j)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N ≫
      (Scheme.Modules.pushforward f).map
        ((structureUnitor ((Scheme.Modules.pullback f).obj N)).inv ≫
          (Stacks.ProjectionFormula.tensorRightInvertible Y
            ((Scheme.Modules.pullback f).obj N)).map j)) := by
  haveI : IsIso (unitToPushforwardStructure f.toLRSHom.toShHom ≫
      (pushforwardFunctor f.toLRSHom.toShHom).map j) := hj
  have k := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
    X.sheaf)).mapIso ((asIso (unitToPushforwardStructure f.toLRSHom.toShHom ≫
      (pushforwardFunctor f.toLRSHom.toShHom).map j)).prod (Iso.refl N))).isIso_hom
  exact (congrArg IsIso (unit_comp_pushforward_map_tensor_eq f.toLRSHom.toShHom N M j)).mpr
    (IsIso.comp_isIso' (structureUnitor N).isIso_inv (IsIso.comp_isIso' k
      (MMP.Resolution.Bridges.isIso_projectionFormulaMap_and_tmul f M N).1))

end ProjectionFormula

section HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

/-- For an invertible `𝒪_X`-module `N` and a morphism `f : Y ⟶ X`, a vanishing
`R^q f_* M = 0` gives `R^q f_*(M ⊗ f^* N) = 0`, by the projection formula
`R^q f_*(M ⊗ f^* N) ≅ R^q f_* M ⊗ N`. -/
private theorem isZero_rightDerived_tensorRightInvertible_pullback {X Y : Scheme.{0}}
    (f : Y ⟶ X) (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] (M : Y.Modules) (q : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj M)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible Y
        ((Scheme.Modules.pullback f).obj N)).obj M)) := by
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N :=
    Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule X N
  have h' : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj M) :=
    h.of_iso ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app M).symm
  have hT : IsZero ((Stacks.ProjectionFormula.tensorRightInvertible X N).obj
      (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj M)) :=
    (Stacks.ProjectionFormula.tensorRightInvertible X N).map_isZero h'
  exact (hT.of_iso (Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso f N M q))
    |>.of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app _)

end HigherDirectImage

/-- If `u ≫ F.map ι ≫ α.app Y` is an isomorphism for a natural transformation `α : F ⟶ G`, then
`u ≫ α.app X` is a split monomorphism, with retraction `G.map ι ≫ (u ≫ F.map ι ≫ α.app Y)⁻¹`. -/
private theorem isSplitMono_comp_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {A : D} {X Y : C} (u : A ⟶ F.obj X) (ι : X ⟶ Y)
    [IsIso (u ≫ F.map ι ≫ α.app Y)] : IsSplitMono (u ≫ α.app X) :=
  .mk' ⟨G.map ι ≫ inv (u ≫ F.map ι ≫ α.app Y), by
    simpa only [Category.assoc, α.naturality_assoc]
      using IsIso.hom_inv_id (u ≫ F.map ι ≫ α.app Y)⟩

section SingleUnit

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
  [Rw.CommShift ℤ] [Rw.IsTriangulated]
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [EnoughInjectives A] [PreservesFiniteLimits w]

/-- The comparison `w(X)[0] ⟶ Rw(X[0])` given by the unit `α` of a right derived functor of a
left exact `w` is an isomorphism at an object `X` with `Rⁿw(X) = 0` for `n > 0`. -/
private theorem isIso_mapSingleQhIso_inv_comp_unit_app (hGE : ∀ X : A,
      (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : ∀ n : ℕ, 0 < n → IsZero ((w.rightDerived n).obj X)) :
    IsIso ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app X ≫
      α.app ((HomotopyCategory.singleFunctor A 0).obj X) ≫
        Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app X)) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h₁ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj X))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    have := hGE X
    have h₂ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  · have := Stacks.DerivedFunctor.isIso_singleUnitHomology_app w Rw α hGE
      (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective w Rw α hres J hJ) X
    have e : (DerivedCategory.homologyFunctor B 0).map
        ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app X ≫
          α.app ((HomotopyCategory.singleFunctor A 0).obj X) ≫
            Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app X)) =
        (DerivedCategory.homologyFunctor B 0).map
            ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app X) ≫
          (Stacks.DerivedFunctor.singleUnitHomology w Rw α 0).app X ≫
            (DerivedCategory.homologyFunctor B 0).map
              (Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app X)) := by
      simp only [Functor.map_comp]
      rfl
    rw [e]
    infer_instance
  · have h₁ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj X))) :=
      DerivedCategory.isZero_of_isLE _ 0 n hn
    lift n to ℕ using hn.le
    have h₂ : IsZero ((DerivedCategory.homologyFunctor B (n : ℤ)).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X))) :=
      (hX n (by exact_mod_cast hn)).of_iso
        ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α hres n).app X)
    exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

end SingleUnit

/-- For an invertible `𝒪_X`-module `N` and an `𝒪_Y`-module `M` with `R^q f_* M = 0` for `q > 0`,
the comparison `(f_* ℋ)[0] ⟶ Rf_*(ℋ[0])` is an isomorphism at `ℋ = M ⊗ f^* N`. -/
private theorem isIso_comparison_tensorRightInvertible_pullback {X Y : Scheme.{0}} (f : Y ⟶ X)
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] (M : Y.Modules)
    (hvan : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj M)) :
    let H := (Stacks.ProjectionFormula.tensorRightInvertible Y
      ((Scheme.Modules.pullback f).obj N)).obj M
    IsIso ((Stacks.DerivedFunctor.mapSingleQhIso (Scheme.Modules.pushforward f) 0).inv.app H ≫
      ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
          ((HomotopyCategory.singleFunctor Y.Modules 0).obj H) ≫
      (Stacks.Duality.derivedPushforward f).map
        ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app H)) := by
  have : PreservesFiniteLimits (Scheme.Modules.pushforward f) :=
    have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.pushforward f) :=
      (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
    inferInstance
  exact isIso_mapSingleQhIso_inv_comp_unit_app (Scheme.Modules.pushforward f)
    (Stacks.Duality.derivedPushforward f) _
    (fun M => Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f)
      ((DerivedCategory.singleFunctor _ 0).obj M) 0)
    (fun K => ⟨(Stacks.Injectives.kInjectiveResolutionFunctor Y.Modules).obj K,
      (Stacks.Injectives.kInjectiveResolutionInclusion Y.Modules).app K, inferInstance,
      inferInstance⟩) _
    fun q hq => isZero_rightDerived_tensorRightInvertible_pullback f N _ q (hvan q hq)

end MMP.FourfoldProofs.Km5dKltPullbackInjectiveProof

end

section

public section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

open MMP.FourfoldProofs.Km5dKltPullbackInjectiveProof in
/-- Let `(X, Δ)` be a klt pair with `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective, and let `f : Y ⟶ X` be a projective log resolution of
`(X, Δ)`. Then for every Cartier divisor `D` on `X` and every `i`, the pull-back
`f^* : H^i(X, 𝒪_X(D)) ⟶ H^i(X, Rf_* f^*𝒪_X(D)) = H^i(Y, f^*𝒪_X(D))`, induced by the unit
`𝒪_X(D) ⟶ f_* f^*𝒪_X(D)` and the comparison `f_* ⟶ Rf_*`, is injective. -/
@[mmp "lem_km5d_klt_pullback_injective"]
public theorem injective_derivedCohomologyOverField_pullback_divisorialSheaf_of_isKltPair
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ)
    {Y : Scheme.{0}} (f : Y ⟶ X) (hres : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hproj : IsProjective f) (D : Divisor X) (hD : D.IsCartier) (i : ℤ) :
    let F := D.divisorialSheaf
    let G := (Scheme.Modules.pullback f).obj F
    -- the comparison `(f_* G)[0] ⟶ Rf_*(G[0])`
    let c : (DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pushforward f).obj G) ⟶
        (Stacks.Duality.derivedPushforward f).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj G) :=
      (Stacks.DerivedFunctor.mapSingleQhIso (Scheme.Modules.pushforward f) 0).inv.app G ≫
        ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
            ((HomotopyCategory.singleFunctor Y.Modules 0).obj G) ≫
        (Stacks.Duality.derivedPushforward f).map
          ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app G)
    Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).map
      ((derivedGlobalSectionsOver sX).map
        ((DerivedCategory.singleFunctor X.Modules 0).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) ≫ c))).hom := by
  intro F G c
  -- `Y` is a normal variety, and `B = B_f` exists
  have hYn : IsNormalVariety k (f ≫ sX) :=
    (hres.toIsSmoothResolution.isNormalVariety hklt.1.1).1
  haveI : IsLocallyNoetherian Y := hYn.1.isLocallyNoetherian
  haveI : IsNormal Y := hYn.2
  haveI : IsProper f := hres.isProper
  obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hklt.1.isPair hklt.1.2.1 f hYn
    hres.isBirationalMorphism
  have hB := hΔY.isDiscrepancyPositivePart hklt.1
  set B := (-ΔY).mapCoeffs (max · 0) (by simp)
  have hvan := isZero_rightDerived_pushforward_divisorialSheaf_roundUp sX hklt hΔ f hres hproj
    hYn hB
  obtain ⟨h0, hφ⟩ := isIso_pushforward_structureSheafToDivisorialSheaf_roundUp sX hΔ f hYn
    hres.isBirationalMorphism hB
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : Stacks.Ample.IsInvertibleModule X F := hD.isInvertibleModule_divisorialSheaf
  -- `ℋ = 𝒪_Y(⌈B⌉) ⊗ f^*𝒪_X(D)` and the inclusion `ι : f^*𝒪_X(D) ⟶ ℋ`
  let T := Stacks.ProjectionFormula.tensorRightInvertible Y G
  let ι : G ⟶ T.obj B.roundUp.divisorialSheaf :=
    (Stacks.AffineProjectionFormula.structureUnitor G).inv ≫
      T.map (Divisor.structureSheafToDivisorialSheaf h0)
  have hψ := isIso_unit_comp_pushforward_map_tensor f F B.roundUp.divisorialSheaf
    (Divisor.structureSheafToDivisorialSheaf h0) hφ
  -- the comparison `f_*(-)[0] ⟶ Rf_*(-[0])` is invertible at `ℋ`
  let su : Scheme.Modules.pushforward f ⋙ DerivedCategory.singleFunctor X.Modules 0 ⟶
      DerivedCategory.singleFunctor Y.Modules 0 ⋙ Stacks.Duality.derivedPushforward f :=
    (Stacks.DerivedFunctor.mapSingleQhIso (Scheme.Modules.pushforward f) 0).inv ≫
      Functor.whiskerLeft (HomotopyCategory.singleFunctor Y.Modules 0)
        ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))) ≫
      (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh Y.Modules 0)
        (Stacks.Duality.derivedPushforward f)).inv
  have hsu : IsIso (su.app (T.obj B.roundUp.divisorialSheaf)) :=
    isIso_comparison_tensorRightInvertible_pullback f F _ hvan
  -- the pull-back map is split mono in `D(𝒪_X)`
  haveI : IsIso ((DerivedCategory.singleFunctor X.Modules 0).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) ≫
      (Scheme.Modules.pushforward f ⋙ DerivedCategory.singleFunctor X.Modules 0).map ι ≫
        su.app (T.obj B.roundUp.divisorialSheaf)) := by
    rw [← Category.assoc, Functor.comp_map, ← Functor.map_comp]
    infer_instance
  have : IsSplitMono ((DerivedCategory.singleFunctor X.Modules 0).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) ≫ c) :=
    isSplitMono_comp_app su _ ι
  exact (ModuleCat.mono_iff_injective _).1 (IsSplitMono.mono
    ((derivedGlobalSectionsOver sX ⋙ DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).map _))

end MMP.Mori

end

end
