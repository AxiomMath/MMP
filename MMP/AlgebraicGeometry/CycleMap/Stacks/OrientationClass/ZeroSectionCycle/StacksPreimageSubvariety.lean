module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksComplex
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksPreimageSubvarietyGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.FlatComapDimension
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleReduced
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleBaseChange

/-!
# The restriction `E|_V = π⁻¹(V)` of a Stacks vector bundle to a subvariety

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, with vector bundle
`π : 𝐕(ℰ) ⟶ X` (`MMP.Modules.totalSpace`, `MMP.Modules.proj`), and `V` a subvariety of `X`. The
inverse image scheme `π⁻¹(V)` is integral: it is `𝐕(ℰ) ×_X V`, the vector bundle of the
pulled-back module `ℰ|_V` (`AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackIso`), an
affine-space bundle over the integral scheme `V`. It is therefore a subvariety `E|_V` of `𝐕(ℰ)`,
of dimension `dim V + r`, with projection `π_V : E|_V ⟶ V`.

## Main definitions

* `MMP.Modules.preimageSubvariety E r V`: the subvariety `π⁻¹(V) = E|_V` of `𝐕(ℰ)`.
* `MMP.Modules.preimageSubvarietyProj E r V`: the projection `π_V : E|_V ⟶ V`.

## Main results

* `MMP.Modules.isIntegral_comap_proj`: `π⁻¹(V)` is integral.
* `MMP.Modules.hasDim_preimageSubvariety`: `dim π⁻¹(V) = dim V + r`.
* `MMP.Modules.preimageSubvarietyProj_ι`: `π_V ≫ V.ι = ι ≫ π`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP.Intersection.Scheme (Subvariety)

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

include r

variable (V : Subvariety X)

/-- The inverse image `π⁻¹(V)` of a subvariety `V` of `X` in the vector bundle `𝐕(ℰ)` is
integral: it is `𝐕(ℰ) ×_X V ≅ 𝐕(ℰ|_V)`, an affine-space bundle over the integral scheme `V`. -/
theorem isIntegral_comap_proj : IsIntegral (V.ideal.comap (proj E)).subscheme := by
  haveI := V.isIntegral
  haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback V.ι E r
  haveI : IsIntegral (Scheme.Modules.vectorBundle V.toScheme
      ((Scheme.Modules.pullback V.ι).obj E)) :=
    Stacks.Chow.isIntegral_of_isAffineSpaceBundle _ r
      (Stacks.Chow.isAffineSpaceBundle_vectorBundleToBase _ r)
  haveI : Nonempty ↥(Limits.pullback (proj E) V.ι : Scheme.{0}) :=
    ⟨(Scheme.Modules.vectorBundlePullbackIso V.ι E).inv (Nonempty.some inferInstance)⟩
  haveI : IsIntegral (Limits.pullback (proj E) V.ι : Scheme.{0}) :=
    isIntegral_of_isOpenImmersion (Scheme.Modules.vectorBundlePullbackIso V.ι E).hom
  haveI : Nonempty (V.ideal.comap (proj E)).subscheme :=
    ⟨(V.ideal.comapIso (proj E)).inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion (V.ideal.comapIso (proj E)).hom

/-- **The subvariety `π⁻¹(V) = E|_V`** of the total space `𝐕(ℰ)`, for a subvariety `V` of the
base. -/
def preimageSubvariety : Subvariety (totalSpace E) :=
  ⟨V.ideal.comap (proj E), isIntegral_comap_proj E r V⟩

/-- The ideal sheaf of `π⁻¹(V)` is the inverse image under `π` of the ideal sheaf of `V`. -/
@[simp]
theorem ideal_preimageSubvariety :
    (preimageSubvariety E r V).ideal = V.ideal.comap (proj E) :=
  rfl

/-- The support of `π⁻¹(V)` is the inverse image of the support of `V`. -/
theorem coe_support_preimageSubvariety :
    ((preimageSubvariety E r V).support : Set (totalSpace E)) =
      proj E ⁻¹' (V.support : Set X) := by
  rw [Subvariety.support, ideal_preimageSubvariety, Scheme.IdealSheafData.support_comap]
  rfl

variable {E r V} in
/-- If `V` has dimension `k - r`, then `π⁻¹(V)` has dimension `k`. -/
theorem hasDim_preimageSubvariety (K : Type) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] {k : ℤ} (hV : V.HasDim (k - r)) :
    (preimageSubvariety E r V).HasDim k := by
  haveI := isIntegral_comap_proj E r V
  haveI := V.isIntegral
  haveI := locallyOfFiniteType_proj E r
  haveI := flat_proj E r
  have h := MMP.topologicalKrullDim_comap_eq_add_of_relativeDimension K (proj E) r
    (Stacks.Chow.relativeDimension_of_isAffineSpaceBundle (proj E) r (isAffineSpaceBundle_proj E r))
    V.ideal (V.ι ≫ X ↘ Spec (.of K))
  obtain ⟨n, hn, hd⟩ := hV
  refine ⟨n + r, by push_cast; omega, ?_⟩
  change topologicalKrullDim (V.ideal.comap (proj E)).subscheme = _
  rw [h]
  change topologicalKrullDim V.toScheme + _ = _
  rw [hd]
  norm_cast

/-! ### The projection `π_V : E|_V ⟶ V` -/

/-- The projection `π_V : E|_V ⟶ V` of `E|_V = π⁻¹(V)`: the second projection of
`𝐕(ℰ) ×_X V ≅ π⁻¹(V)`. -/
def preimageSubvarietyProj : (preimageSubvariety E r V).toScheme ⟶ V.toScheme :=
  (V.ideal.comapIso (proj E)).hom ≫ Limits.pullback.snd (proj E) V.ideal.subschemeι

/-- `π_V ≫ V.ι = ι ≫ π`. -/
@[reassoc]
lemma preimageSubvarietyProj_ι :
    preimageSubvarietyProj E r V ≫ V.ι = (preimageSubvariety E r V).ι ≫ proj E := by
  change ((V.ideal.comapIso (proj E)).hom ≫
      Limits.pullback.snd (proj E) V.ideal.subschemeι) ≫ V.ideal.subschemeι =
    (V.ideal.comap (proj E)).subschemeι ≫ proj E
  rw [Category.assoc, ← Limits.pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

variable [X.Over (Spec (.of ℂ))]

/-- The projection `π_V : E|_V ⟶ V` is a morphism over `Spec ℂ`. -/
instance isOver_preimageSubvarietyProj :
    (preimageSubvarietyProj E r V).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change preimageSubvarietyProj E r V ≫ V.ι ≫ X ↘ Spec (.of ℂ) =
      (preimageSubvariety E r V).ι ≫ totalSpace E ↘ Spec (.of ℂ)
    rw [preimageSubvarietyProj_ι_assoc]
    rfl⟩

/-- `π_V ≫ V.ι = ι ≫ π` on complex points. -/
lemma mapFun_preimageSubvarietyProj
    (p : UnderlyingSpace ℂ (preimageSubvariety E r V).toScheme) :
    mapFun V.ι (mapFun (preimageSubvarietyProj E r V) p) =
      mapFun (proj E) (mapFun (preimageSubvariety E r V).ι p) :=
  UnderlyingSpace.ext (by
    rw [toHom_mapFun, toHom_mapFun, toHom_mapFun, toHom_mapFun, Category.assoc,
      preimageSubvarietyProj_ι, Category.assoc])

end MMP.Modules
