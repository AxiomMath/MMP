module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.ContractedTail
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback

/-!
# The projection formula for degrees on proper curves

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes with `Y` separated and locally of
finite type over `k`, `L` an invertible sheaf on `Y` and `C ⊆ X` a proper curve. Then

`deg_C (f^* L) = deg_{f_* C} L`,

where `f_* C = [k(C) : k(f(C))] · f(C)` when the image `f(C)` is a curve and `f_* C = 0` when it
is a point. By linearity the same holds for every 1-cycle `Z` on `X`:
`(f^* L · Z) = (L · f_* Z)`.

For the blowup `π : Y' ⟶ Y` of a point of a smooth surface and a Cartier divisor `D` on `Y`
(with `L = 𝒪_Y(D)` and `π^* 𝒪_Y(D) = 𝒪_{Y'}(π^* D)`), this is `(π^* D · G) = (D · π_* G)` for
every proper curve `G ⊆ Y'`, and `(π^* D · F) = 0` for the exceptional curve `F`, which `π`
contracts to a point.

The proof follows the two cases. If `f` maps `C` to a point, `f^* L` is trivial on `C` and the
image is not a curve. Otherwise `C ⟶ f(C)` is a non-constant, hence finite and surjective,
morphism of proper curves, so `f(C)` is a proper curve, and the degree of a pulled-back
invertible sheaf is multiplied by the degree `[k(C) : k(f(C))]` of the morphism
([Stacks, Tag 0AYZ]); that degree is the residue degree of `f` at the generic point of `C`.

## Main results

* `MMP.Mori.ProperCurve.degree_pullback`: `deg_C (f^* L)` is `[k(C) : k(f(C))] · deg_{f(C)} L`
  if `f(C)` is a proper curve and `0` otherwise.
* `MMP.Mori.ProperCurve.degree_pullback_eq_degree_pushforward`: `deg_C (f^* L) = (L · f_* C)`.
* `MMP.Mori.OneCycle.degree_pullback_eq_degree_pushforward`: `(f^* L · Z) = (L · f_* Z)` for every
  1-cycle `Z`.
* `MMP.Mori.ProperCurve.degree_pullback_eq_zero_of_isContractedBy`: `deg_C (f^* L) = 0` when `f`
  contracts `C` to a point, and `MMP.Mori.ProperCurve.pushforward_cycle_eq_zero_of_isContractedBy`:
  then `f_* C = 0`.
* `MMP.Mori.Divisor.degreeOn_eq_degree_pushforward_of_iso`: `(D' · C) = (D · f_* C)` for Cartier
  divisors `D` on `Y` and `D'` on `X` with `𝒪_X(D') ≅ f^* 𝒪_Y(D)`.
* `MMP.Mori.Divisor.degreeOn_pullback_eq_degree_pushforward`: `(f^* D · C) = (D · f_* C)` for the
  pull-back `MMP.Mori.Divisor.pullback` of a Cartier divisor, `X` integral, and
  `MMP.Mori.Divisor.degreeOn_pullback_eq_zero_of_isContractedBy`: `(f^* D · F) = 0` on a
  contracted curve `F`.

## Implementation notes

The degree is the Euler-characteristic degree `MMP.Mori.ProperCurve.degree`,
`χ(C, L|_C) - χ(C, 𝒪_C)`, which is the intersection number `MMP.Mori.QDivisor.intersectionNumber`
of a Cartier divisor with a curve. The statement is made for an invertible sheaf `L` and its
pull-back `f^* L`, which is the invertible sheaf of the pull-back `f^* D` of a Cartier divisor
`D` with `L = 𝒪_Y(D)`. Nothing about the blowup is used beyond its being a morphism of
`k`-schemes into a separated scheme of finite type over `k`.

## References

* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
* [R. Hartshorne, *Algebraic geometry*, V.3.2], the case of a point blowup of a surface
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- The points of a proper curve `C ⊆ X` are those of the closure of its generic point. -/
theorem ProperCurve.range_ι {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    Set.range C.ι.base = closure ({C.point} : Set X) := by
  unfold ProperCurve.ι curveSubschemeAtι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The image of a proper curve `C ⊆ X` under a morphism `f : X ⟶ Y` into a separated
`k`-scheme is the closure of the image of its generic point. -/
theorem ProperCurve.range_ι_comp [IsSeparated sY] (f : X ⟶ Y) (C : ProperCurve (f ≫ sY)) :
    Set.range (C.ι ≫ f).base = closure ({f C.point} : Set Y) := by
  have : IsProper ((C.ι ≫ f) ≫ sY) := by rw [Category.assoc]; infer_instance
  have : IsProper (C.ι ≫ f) := IsProper.of_comp _ sY
  have hx : C.point ∈ Set.range C.ι.base := by rw [C.range_ι]; exact subset_closure rfl
  refine le_antisymm ?_ ((C.ι ≫ f).isClosedMap.isClosed_range.closure_subset_iff.2 ?_)
  · rintro _ ⟨c, rfl⟩
    have hc : C.ι.base c ∈ closure ({C.point} : Set X) := by rw [← C.range_ι]; exact ⟨c, rfl⟩
    have := image_closure_subset_closure_image (s := ({C.point} : Set X)) f.continuous
      ⟨_, hc, rfl⟩
    simpa using this
  · obtain ⟨c, hc⟩ := hx
    rintro _ rfl
    exact ⟨c, by simp [hc]⟩

/-- If a morphism `f : X ⟶ Y` into a separated `k`-scheme maps a proper curve `C ⊆ X` to a
point, then the image `f(C)` is not a proper curve. -/
theorem ProperCurve.not_isProperCurve_of_forall_eq [IsSeparated sY] (f : X ⟶ Y)
    (C : ProperCurve (f ≫ sY)) {y : Y} (hy : ∀ z, (C.ι ≫ f).base z = y) :
    ¬ IsProperCurve sY (f C.point) := by
  intro hD
  have hrange := C.range_ι_comp f
  have hsub : Subsingleton (curveSubschemeAt (f C.point)) := by
    refine ⟨fun a b => (curveSubschemeAtι (f C.point)).isClosedEmbedding.injective ?_⟩
    have hmem : ∀ d, (curveSubschemeAtι (f C.point)).base d ∈ Set.range (C.ι ≫ f).base := by
      intro d
      rw [hrange]
      have : (curveSubschemeAtι (f C.point)).base d ∈
          Set.range (curveSubschemeAtι (f C.point)).base := ⟨d, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    obtain ⟨c, hc⟩ := hmem a
    obtain ⟨c', hc'⟩ := hmem b
    rw [← hc, ← hc', hy, hy]
  exact Stacks.Chow.not_subsingleton_of_one_le_topologicalKrullDim
    hD.dim_eq.ge hsub

open Classical in
/-- **The degree of a pulled-back invertible sheaf on a proper curve.** Let `f : X ⟶ Y` be a
morphism of `k`-schemes, `Y` separated and locally of finite type over `k`, `L` an invertible
sheaf on `Y` and `C ⊆ X` a proper curve. If the image `f(C)` is a proper curve, then
`deg_C (f^* L) = [κ(C) : κ(f(C))] · deg_{f(C)} L`; otherwise `f(C)` is a point and
`deg_C (f^* L) = 0`. -/
theorem ProperCurve.degree_pullback [IsSeparated sY] [LocallyOfFiniteType sY]
    {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) (hf : f ≫ sY = sX) (C : ProperCurve sX)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    C.degree k ((Scheme.Modules.pullback f).obj L) =
      if h : IsProperCurve sY (f C.point) then
        (residueFieldDegree f C.point : ℤ) * (⟨f C.point, h⟩ : ProperCurve sY).degree k L
      else 0 := by
  subst hf
  have hP : IsProper ((C.ι ≫ f) ≫ sY) := by rw [Category.assoc]; infer_instance
  have hP' : IsProper (C.ι ≫ f) := IsProper.of_comp _ sY
  have hL : C.degree k ((Scheme.Modules.pullback f).obj L) =
      Mori.degreeOn k sY (C.ι ≫ f) C.dim_le L :=
    (Threefold.Resolution.degreeOn_comp k sY f C.ι C.dim_le L).symm
  rw [hL]
  by_cases hc : ∃ y, ∀ z, (C.ι ≫ f).base z = y
  · obtain ⟨y, hy⟩ := hc
    rw [dite_eq_right (C.not_isProperCurve_of_forall_eq f hy)]
    exact invertibleCurveDegree_pullback_eq_zero_of_forall_eq k _ C.dim_le (C.ι ≫ f) L y hy
  · set x := C.point
    let D := curveSubschemeAt (f.base x)
    let ιD : D ⟶ Y := curveSubschemeAtι (f.base x)
    let h : C.scheme ⟶ D := Stacks.Chow.integralComponentMap f x
    have hh : h ≫ ιD = C.ι ≫ f := Stacks.Chow.integralComponentMap_subschemeι f x
    have : IsIntegral D := Stacks.Chow.isIntegral_integralComponentAt (f.base x)
    have : IsProper (h ≫ ιD) := by rw [hh]; infer_instance
    have : IsProper h := IsProper.of_comp h ιD
    have hrangeD : Set.range ιD.base = closure ({f.base x} : Set Y) := by
      change Set.range (curveSubschemeAtι (f.base x)).base = _
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hsurj : Function.Surjective h.base := by
      intro d
      have hd : ιD.base d ∈ Set.range (C.ι ≫ f).base := by
        rw [C.range_ι_comp f, ← hrangeD]; exact ⟨d, rfl⟩
      obtain ⟨c, hc⟩ := hd
      refine ⟨c, ιD.isClosedEmbedding.injective ?_⟩
      rw [← hc, ← Scheme.Hom.comp_apply, hh]
    have : Surjective h := ⟨hsurj⟩
    have : UniversallyClosed (h ≫ ιD ≫ sY) := by
      rw [← Category.assoc, hh, Category.assoc]; infer_instance
    have : UniversallyClosed (ιD ≫ sY) := UniversallyClosed.of_comp_surjective h _
    have : IsProper (ιD ≫ sY) := ⟨⟩
    have hnc : ¬ ∃ y : D, ∀ z, h.base z = y := by
      rintro ⟨y, hy⟩
      exact hc ⟨ιD.base y, fun z => by rw [← hh, Scheme.Hom.comp_apply, hy]⟩
    have hdimD : topologicalKrullDim D = 1 := by
      refine le_antisymm ?_ ?_
      · rw [← C.dim_eq]
        exact topologicalKrullDim_le_of_surjective_of_isClosedMap h hsurj h.isClosedMap
      · refine Stacks.Curves.StableModel.one_le_topologicalKrullDim_of_not_subsingleton D ?_
        intro hsub
        exact hnc ⟨h.base (Classical.arbitrary _), fun z => Subsingleton.elim _ _⟩
    have hD : IsProperCurve sY (f.base x) := ⟨hdimD, inferInstance⟩
    rw [dite_eq_left hD]
    have : IsCurve k (C.ι ≫ f ≫ sY) :=
      { toIsIntegral := inferInstance
        toIsSeparated := inferInstance
        toLocallyOfFiniteType := inferInstance
        toQuasiCompact := inferInstance
        topologicalKrullDim_eq_one := C.dim_eq }
    have : IsCurve k (ιD ≫ sY) :=
      { toIsIntegral := inferInstance
        toIsSeparated := inferInstance
        toLocallyOfFiniteType := inferInstance
        toQuasiCompact := inferInstance
        topologicalKrullDim_eq_one := hdimD }
    have hcomp : h ≫ ιD ≫ sY = C.ι ≫ f ≫ sY := by rw [← Category.assoc, hh, Category.assoc]
    have key := invertibleCurveDegree_pullback_eq_degreeOver_mul k (C.ι ≫ f ≫ sY) (ιD ≫ sY) h
      hcomp hnc ((Scheme.Modules.pullback ιD).obj L)
    have hdeg : @degreeOver C.scheme D h _ _
        (locallyOfFiniteType_of_isCurve_comp k (C.ι ≫ f ≫ sY) (ιD ≫ sY) h hcomp)
        (isDominant_of_not_constant k (C.ι ≫ f ≫ sY) (ιD ≫ sY) h hnc) = residueFieldDegree f x := by
      unfold degreeOver
      exact Stacks.Chow.finrank_functionField_integralComponent f x
    have : IsProper ((h ≫ ιD) ≫ sY) := by rw [Category.assoc]; infer_instance
    have : IsProper (h ≫ ιD ≫ sY) := inferInstance
    rw [← Threefold.Resolution.degreeOn_eq_of_iso_comp k sY (h ≫ ιD) (C.ι ≫ f) C.dim_le C.dim_le
      (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp, hh]),
      Threefold.Resolution.degreeOn_comp k sY ιD h C.dim_le L,
      Mori.degreeOn_eq_invertibleCurveDegree,
      Threefold.Resolution.invertibleCurveDegree_congr k hcomp, key, hdeg]
    rfl

/-- The degree of an invertible sheaf on the push-forward `f_* C` of a proper curve is the degree
of its pull-back on `C`. -/
theorem OneCycle.degree_cyclePushforwardOfPoint [IsSeparated sY] [LocallyOfFiniteType sY]
    (A : Type*) [CommRing A] {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (C : ProperCurve sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    OneCycle.degree A sY L (cyclePushforwardOfPoint A sY f C.point) =
      (C.degree k ((Scheme.Modules.pullback f).obj L) : A) := by
  rw [C.degree_pullback f hf L, cyclePushforwardOfPoint]
  split_ifs with h
  · simp [OneCycle.degree]
  · simp

/-- **Projection formula for a proper curve**. Let `f : X ⟶ Y` be a morphism of `k`-schemes, `Y`
separated and locally of finite type over `k`, `L` an invertible sheaf on `Y` and `C ⊆ X` a
proper curve. Then `(f^* L · C) = (L · f_* C)`. -/
@[mmp "lem_mmp_threefold_surface_blowup_projection"]
theorem ProperCurve.degree_pullback_eq_degree_pushforward [IsSeparated sY]
    [LocallyOfFiniteType sY] {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (C : ProperCurve sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    C.degree k ((Scheme.Modules.pullback f).obj L) =
      OneCycle.degree ℤ sY L (OneCycle.pushforward ℤ sX sY f (C.cycle ℤ)) := by
  rw [OneCycle.pushforward_cycle, OneCycle.degree_cyclePushforwardOfPoint ℤ f hf C L,
    Int.cast_id]

/-- **Projection formula for 1-cycles.** Let `f : X ⟶ Y` be a morphism of `k`-schemes, `Y`
separated and locally of finite type over `k`, and `L` an invertible sheaf on `Y`. For every
1-cycle `Z` on `X` with coefficients in `A`, `(f^* L · Z) = (L · f_* Z)`. -/
@[mmp "lem_mmp_threefold_surface_blowup_projection"]
theorem OneCycle.degree_pullback_eq_degree_pushforward [IsSeparated sY] [LocallyOfFiniteType sY]
    (A : Type*) [CommRing A] {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (Z : OneCycle A sX) :
    OneCycle.degree A sX ((Scheme.Modules.pullback f).obj L) Z =
      OneCycle.degree A sY L (OneCycle.pushforward A sX sY f Z) := by
  rw [← LinearMap.comp_apply]
  refine LinearMap.congr_fun (Finsupp.lhom_ext fun C a => ?_) Z
  rw [LinearMap.comp_apply, OneCycle.pushforward, Finsupp.linearCombination_single,
    LinearMap.map_smul, OneCycle.degree_cyclePushforwardOfPoint A f hf C L, OneCycle.degree,
    Finsupp.linearCombination_single, smul_eq_mul]

/-- The push-forward of a proper curve contracted to a point is zero. -/
theorem ProperCurve.pushforward_cycle_eq_zero_of_isContractedBy [IsSeparated sY]
    (A : Type*) [Semiring A] {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    OneCycle.pushforward A sX sY f (C.cycle A) = 0 := by
  subst hf
  rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint, dite_eq_right]
  refine C.not_isProperCurve_of_forall_eq f (y := f.base C.point) fun z => hC _ ?_
  rw [← C.range_ι]
  exact ⟨z, rfl⟩

/-- **The pull-back of an invertible sheaf has degree zero on a contracted curve**: if `f`
contracts the proper curve `C` to a point, then `deg_C (f^* L) = 0`; e.g. `(π^* L · F) = 0` for
the exceptional curve `F` of a point blowup `π`. -/
@[mmp "lem_mmp_threefold_surface_blowup_projection"]
theorem ProperCurve.degree_pullback_eq_zero_of_isContractedBy [IsSeparated sY]
    [LocallyOfFiniteType sY] {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    C.degree k ((Scheme.Modules.pullback f).obj L) = 0 := by
  rw [C.degree_pullback_eq_degree_pushforward f hf L,
    C.pushforward_cycle_eq_zero_of_isContractedBy ℤ f hf hC, map_zero]

/-- **Projection formula for Cartier divisors.** Let `f : X ⟶ Y` be a morphism of normal locally
Noetherian `k`-schemes, quasi-compact over `k`, with `Y` separated and locally of finite type
over `k`. Let `D` be a Cartier divisor on `Y` and `D'` a Cartier divisor on `X` with
`𝒪_X(D') ≅ f^* 𝒪_Y(D)`, as for the pull-back `D' = f^* D`. Then `(D' · C) = (D · f_* C)` for
every proper curve `C ⊆ X`. -/
theorem Divisor.degreeOn_eq_degree_pushforward_of_iso [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {D : Divisor Y} (hD : D.IsCartier) {D' : Divisor X} (hD' : D'.IsCartier)
    (e : D'.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj D.divisorialSheaf)
    (C : ProperCurve sX) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := hD.isInvertibleModule_divisorialSheaf
    D'.degreeOn k sX C.ι C.dim_le hD' =
      OneCycle.degree ℤ sY D.divisorialSheaf (OneCycle.pushforward ℤ sX sY f (C.cycle ℤ)) := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hD.isInvertibleModule_divisorialSheaf
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hD'.isInvertibleModule_divisorialSheaf
  rw [← C.degree_pullback_eq_degree_pushforward f hf]
  exact degreeOn_eq_of_iso k sX C.ι C.dim_le e

/-- **Projection formula for the pull-back of a Cartier divisor.** Let `f : X ⟶ Y` be a morphism
of `k`-schemes, quasi-compact over `k`, with `X` integral, both locally Noetherian and normal, and
`Y` separated and locally of finite type over `k`. Let `D` be a Cartier divisor on `Y` with `f`
mapping the generic point of `X` outside `Supp D`. Then `(f^* D · C) = (D · f_* C)` for every
proper curve `C ⊆ X`. -/
@[mmp "lem_mmp_threefold_surface_blowup_projection"]
theorem Divisor.degreeOn_pullback_eq_degree_pushforward [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp)
    (C : ProperCurve sX) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := QuasiCompact.compactSpace_of_compactSpace sX
    haveI := hD.isInvertibleModule_divisorialSheaf
    (D.pullback hD hB).degreeOn k sX C.ι C.dim_le (hD.isCartier_pullback f hB) =
      OneCycle.degree ℤ sY D.divisorialSheaf (OneCycle.pushforward ℤ sX sY f (C.cycle ℤ)) := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨e⟩ := nonempty_divisorialSheaf_pullback_iso hD f hB
  exact degreeOn_eq_degree_pushforward_of_iso f hf hD (hD.isCartier_pullback f hB) e C

/-- **The pull-back of a Cartier divisor has degree zero on a contracted curve**: if `f`
contracts the proper curve `C` to a point, then `(f^* D · C) = 0`; e.g. `(π^* D · F) = 0` for
the exceptional curve `F` of a point blowup `π`. -/
@[mmp "lem_mmp_threefold_surface_blowup_projection"]
theorem Divisor.degreeOn_pullback_eq_zero_of_isContractedBy [IsSeparated sY]
    [LocallyOfFiniteType sY] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := QuasiCompact.compactSpace_of_compactSpace sX
    (D.pullback hD hB).degreeOn k sX C.ι C.dim_le (hD.isCartier_pullback f hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward f hf hD hB C,
    C.pushforward_cycle_eq_zero_of_isContractedBy ℤ f hf hC, map_zero]

end MMP.Mori
