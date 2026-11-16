/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.PicardTrivialOpenUFD.Basic
public import StacksFrontier.Topology.Dimension.KrullSeparation

/-!
# Degrees of line bundles under a map from a proper curve

Let `k` be a field, `C` a proper integral curve over `k`, `X` a separated `k`-scheme of finite
type and `φ : C ⟶ X` a `k`-morphism. Then `φ` is proper, so its image `φ(C)` is closed; with its
reduced induced structure it is the scheme-theoretic image `T` of `φ`, and `φ` factors as a
dominant (indeed surjective) morphism `h : C ⟶ T` followed by the closed immersion `T ⟶ X`.
The scheme `T` is proper over `k`, integral, of dimension at most one, so it is either a point or
a proper integral curve.

For an invertible `𝒪_X`-module `M`, with the degree `deg_C N = χ(C, N) - χ(C, 𝒪_C)`:

* if `T` is a point, then `deg_C φ^*M = 0`, since `M|_T` is trivial;
* otherwise `h` is a nonconstant morphism of proper curves and
  `deg_C φ^*M = [k(C) : k(T)] · deg_T (M|_T)` by [Stacks, Tag 0AYZ].

As a consequence, for a morphism `f : X ⟶ Y` of proper varieties over `k` with `Y` normal, an
irreducible closed curve `C ⊆ X` and a Cartier divisor `M` on `Y`, the intersection number
`(f^*M · C)` vanishes when `f(C)` is a point, and equals `deg(C → f(C)) · (M · f(C))` when `f(C)`
is a curve.

## Main results

* `MMP.Mori.range_eq_singleton_or_isCurve_image`: the image `T = φ(C)` is reduced with
  underlying set `φ(C)`, and it is a point or a proper integral curve.
* `MMP.Mori.degreeOn_eq_zero_of_range_eq_singleton`: `deg_C φ^*M = 0` when `φ(C)` is a point.
* `MMP.Mori.degreeOn_eq_degreeOver_mul`: `deg_C φ^*M = [k(C) : k(T)] · deg_T (M|_T)` otherwise.
* `MMP.Mori.finite_functionField_image`: in the second case `k(C)` is a finite extension of
  `k(T)`, so `[k(C) : k(T)]` is a genuine (positive) field degree.
* `MMP.Mori.degreeOn_pullback_divisorialSheaf_eq_zero` and
  `MMP.Mori.degreeOn_pullback_divisorialSheaf_eq_degreeOver_mul_intersectionNumber`: the two
  cases of `(f^*M · C)` for a morphism of proper varieties.

## Implementation notes

The reduced image `T` is the scheme-theoretic image `φ.image` of Mathlib, with the closed
immersion `φ.imageι : T ⟶ X` and the factorization `φ.toImage : C ⟶ T`; since `C` is reduced,
`φ.image` is the reduced induced structure on the closure of `φ(C)`
(`AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_range`), which is `φ(C)` because `φ`
is proper. The `k`-structure of `C` is the composite `φ ≫ s_X`, that of `T` is
`φ.imageι ≫ s_X`, and `M|_T` is the pullback of `M` along `φ.imageι`. The degree of an
invertible sheaf along a curve is `MMP.Mori.degreeOn`, which is `χ(N) - χ(𝒪)` of the pullback;
the field degree `[k(C) : k(T)]` is `AlgebraicGeometry.degreeOver φ.toImage`. "`φ(C)` is a point"
is `∃ x, Set.range φ = {x}`.

For a morphism `f : X ⟶ Y` which may contract `C` (so need not satisfy the condition under which
`f^*M` is defined as a Weil divisor), `(f^*M · C)` is the degree on `C` of the invertible sheaf
`f^* 𝒪_Y(M)`, as in [KM, Notation 0.4(5)]; the curve `C ⊆ X` is a closed immersion `i : C ⟶ X`
whose source is a curve. The divisor `M` lives on the normal scheme `Y`, as Weil and Cartier
divisors do throughout; `X` need not be normal.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
* [Stacks Project, Tag 0AH6](https://stacks.math.columbia.edu/tag/0AH6)
* [Stacks Project, Tag 056B](https://stacks.math.columbia.edu/tag/056B)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {C X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (φ : C ⟶ X)

/-! ### The reduced image of a proper morphism -/

/-- For `φ ≫ s_X` proper and `s_X` separated, the scheme-theoretic image of `φ` from a reduced
scheme has underlying set exactly `φ(C)`. -/
theorem range_imageι_eq_range [IsReduced C] [IsProper (φ ≫ sX)] [IsSeparated sX] :
    Set.range φ.imageι = Set.range φ := by
  have : IsProper φ := IsProper.of_comp φ sX
  change Set.range φ.ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, φ.support_ker_eq_closure_range,
    Closeds.coe_closure, φ.isClosedMap.isClosed_range.closure_eq]

/-- The scheme-theoretic image of a quasi-compact morphism from an integral scheme is integral. -/
instance isIntegral_image [IsIntegral C] [QuasiCompact φ] : IsIntegral φ.image := by
  have : IrreducibleSpace φ.image := by
    refine (irreducibleSpace_def _).mpr ?_
    rw [Set.top_eq_univ, ← φ.toImage.denseRange.closure_range]
    have himg := ((IrreducibleSpace.isIrreducible_univ C).image _
      φ.toImage.continuous.continuousOn).closure
    rwa [Set.image_univ] at himg
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The morphism to the scheme-theoretic image of a morphism locally of finite type is locally
of finite type. -/
instance locallyOfFiniteType_toImage [LocallyOfFiniteType φ] :
    LocallyOfFiniteType φ.toImage := by
  have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by simpa
  exact locallyOfFiniteType_of_comp φ.toImage φ.imageι

/-- The image of an integral scheme of finite type over `k` under a quasi-compact `k`-morphism
has dimension at most that of the source. -/
theorem topologicalKrullDim_image_le [IsIntegral C] [QuasiCompact φ] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType φ] : topologicalKrullDim φ.image ≤ topologicalKrullDim C := by
  set sT := φ.imageι ≫ sX
  have hT := toENat_trdeg_functionField (sX := sT)
  have hC := toENat_trdeg_functionField (sX := φ.toImage ≫ sT)
  rw [← hT, ← hC]
  let := functionFieldAlgebra sT
  let := functionFieldAlgebra (φ.toImage ≫ sT)
  let := functionFieldMapAlgebra φ.toImage
  have := isScalarTower_functionFieldMap sT φ.toImage
  have h := trdeg_add_eq k φ.image.functionField (A := C.functionField)
  rw [← h, map_add]
  exact WithBot.coe_le_coe.mpr le_self_add

/-- The image of a proper curve in a separated `k`-scheme of finite type has dimension at most
one. -/
theorem topologicalKrullDim_image_le_one [IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)]
    [IsSeparated sX] [LocallyOfFiniteType sX] :
    topologicalKrullDim φ.image ≤ 1 := by
  have : IsProper φ := IsProper.of_comp φ sX
  exact (topologicalKrullDim_image_le sX φ).trans
    (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sX)).le

/-- If `φ(C)` is not a point, the image of `φ` has a point other than its generic point. -/
theorem exists_ne_genericPoint_image [IsIntegral C] [IsProper (φ ≫ sX)] [IsSeparated sX]
    (hnc : ¬ ∃ x : X, Set.range φ = {x}) :
    haveI : IsProper φ := IsProper.of_comp φ sX
    ∃ t : φ.image, t ≠ genericPoint φ.image := by
  have : IsProper φ := IsProper.of_comp φ sX
  by_contra! h
  refine hnc ⟨φ.imageι (genericPoint φ.image), ?_⟩
  rw [← range_imageι_eq_range sX φ]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    rw [h t]; rfl
  · intro hx
    rw [hx]; exact ⟨_, rfl⟩

/-- If a proper curve `C` maps to a separated `k`-scheme of finite type with image `φ(C)` not a
point, then the reduced image of `φ` is a curve over `k`. -/
theorem isCurve_imageι_comp [IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)] [IsSeparated sX]
    [LocallyOfFiniteType sX] (hnc : ¬ ∃ x : X, Set.range φ = {x}) :
    IsCurve k (φ.imageι ≫ sX) := by
  have : IsProper φ := IsProper.of_comp φ sX
  have : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
  have : IsVariety k (φ.imageι ≫ sX) := IsVariety.mk
  refine ⟨le_antisymm (topologicalKrullDim_image_le_one sX φ) ?_⟩
  obtain ⟨t, ht⟩ := exists_ne_genericPoint_image sX φ hnc
  exact one_le_topologicalKrullDim_of_specializes_of_ne (genericPoint_specializes t) (Ne.symm ht)

/-- If `φ(C)` is a point, the image of `φ` has a single point. -/
theorem subsingleton_image [IsReduced C] [IsProper (φ ≫ sX)] [IsSeparated sX]
    (hpt : ∃ x : X, Set.range φ = {x}) : Subsingleton φ.image := by
  obtain ⟨x, hx⟩ := hpt
  have h : ∀ t : φ.image, φ.imageι t = x := fun t => by
    have : φ.imageι t ∈ Set.range φ := range_imageι_eq_range sX φ ▸ ⟨t, rfl⟩
    rwa [hx] at this
  exact ⟨fun a b => φ.imageι.isEmbedding.injective ((h a).trans (h b).symm)⟩

/-- **The reduced image of a proper curve is a point or a proper integral curve.** Let `C` be a
proper integral curve over `k` (with `k`-structure `φ ≫ s_X`), `X` separated and of finite type
over `k`, and `φ : C ⟶ X` a `k`-morphism. Its reduced image `T = φ.image` is a reduced closed
subscheme of `X` with underlying set `φ(C)`, and either `φ(C)` is a point or `T` is a proper
integral curve over `k`. -/
@[mmp "lem_mmp_foundation_proper_curve_projection",
  mmp "lem_mmp_foundation_km_curve_degree_projection"]
theorem range_eq_singleton_or_isCurve_image [IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)]
    [IsSeparated sX] [LocallyOfFiniteType sX] :
    IsReduced φ.image ∧ Set.range φ.imageι = Set.range φ ∧
      ((∃ x : X, Set.range φ = {x}) ∨
        (IsCurve k (φ.imageι ≫ sX) ∧ IsProper (φ.imageι ≫ sX))) := by
  refine ⟨inferInstance, range_imageι_eq_range sX φ, ?_⟩
  by_cases hpt : ∃ x : X, Set.range φ = {x}
  · exact Or.inl hpt
  · have : IsProper φ := IsProper.of_comp φ sX
    exact Or.inr ⟨isCurve_imageι_comp sX φ hpt, isProper_imageι_comp φ sX⟩

/-! ### Degrees -/

/-- On a scheme with a single point, every invertible module is isomorphic to the structure
sheaf. -/
theorem nonempty_iso_unit_of_subsingleton {T : Scheme.{u}} [Subsingleton T] (L : T.Modules)
    [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L] (t : T) :
    Nonempty (L ≅ SheafOfModules.unit T.ringCatSheaf) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over T L t
  have hU : U = ⊤ := by
    ext x; simp only [Opens.coe_top, Set.mem_univ, iff_true]
    rwa [Subsingleton.elim x t]
  subst hU
  have e' := Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit L ⊤ e
  let i := T.topIso
  exact ⟨Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoRestrictOfIso L i ≪≫
    (Scheme.Modules.restrictFunctor i.inv).mapIso e' ≪≫ Scheme.Modules.restrictUnitIso i.inv⟩

/-- **Degree zero over a point.** Let `C` be a proper integral curve over `k`, `X` separated over
`k`, `φ : C ⟶ X` a `k`-morphism and `M` an invertible `𝒪_X`-module. If `φ(C)` is a point, then
`deg_C φ^*M = χ(C, φ^*M) - χ(C, 𝒪_C) = 0`. -/
@[mmp "lem_mmp_foundation_proper_curve_projection",
  mmp "lem_mmp_foundation_km_curve_degree_projection"]
theorem degreeOn_eq_zero_of_range_eq_singleton [IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)]
    [IsSeparated sX] (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hpt : ∃ x : X, Set.range φ = {x}) :
    degreeOn k sX φ (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sX)).le M = 0 := by
  have := subsingleton_image sX φ hpt
  obtain ⟨e₁⟩ := nonempty_iso_unit_of_subsingleton ((Scheme.Modules.pullback φ.imageι).obj M)
    (φ.toImage (genericPoint C))
  exact invertibleCurveDegree_eq_zero_of_iso_unit k _ _ _
    ((Scheme.Modules.pullbackCongr φ.toImage_imageι.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp φ.toImage φ.imageι).app M).symm ≪≫
      (Scheme.Modules.pullback φ.toImage).mapIso e₁ ≪≫
      Stacks.PicardTrivialOpenUFD.pullbackUnitIso φ.toImage)

/-- If `φ(C)` is not a point, the morphism from `C` to the image of `φ` is not constant. -/
theorem not_exists_toImage_eq [Nonempty C] (hnc : ¬ ∃ x : X, Set.range φ = {x}) :
    ¬ ∃ y : φ.image, ∀ c : C, φ.toImage c = y := by
  rintro ⟨y, hy⟩
  refine hnc ⟨φ.imageι y, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · obtain ⟨c⟩ : Nonempty C := inferInstance
    exact ⟨c, by rw [← hy c, ← Scheme.Hom.comp_apply, φ.toImage_imageι]⟩
  · rintro _ ⟨c, rfl⟩
    rw [← hy c, ← Scheme.Hom.comp_apply, φ.toImage_imageι]

/-- **The projection formula for degrees from a proper curve.** Let `C` be a proper integral
curve over `k` (with `k`-structure `φ ≫ s_X`), `X` separated and of finite type over `k`,
`φ : C ⟶ X` a `k`-morphism and `M` an invertible `𝒪_X`-module. If `φ(C)` is not a point, then with
`T` the reduced image of `φ` (a proper integral curve,
`MMP.Mori.range_eq_singleton_or_isCurve_image`),
`deg_C φ^*M = [k(C) : k(T)] · deg_T (M|_T)`, both degrees being `χ(N) - χ(𝒪)`. -/
@[mmp "lem_mmp_foundation_proper_curve_projection",
  mmp "lem_mmp_foundation_km_curve_degree_projection"]
theorem degreeOn_eq_degreeOver_mul [IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)]
    [IsSeparated sX] [LocallyOfFiniteType sX] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hnc : ¬ ∃ x : X, Set.range φ = {x}) :
    haveI : IsProper φ := IsProper.of_comp φ sX
    haveI : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
    degreeOn k sX φ (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sX)).le M =
      (degreeOver φ.toImage : ℤ) *
        degreeOn k sX φ.imageι (topologicalKrullDim_image_le_one sX φ) M := by
  have : IsProper φ := IsProper.of_comp φ sX
  have : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
  have : IsCurve k (φ.imageι ≫ sX) := isCurve_imageι_comp sX φ hnc
  have hf : φ.toImage ≫ φ.imageι ≫ sX = φ ≫ sX := by simp
  have key := curveDegree_pullback_eq_degreeOver_mul k (φ ≫ sX) (φ.imageι ≫ sX) φ.toImage hf
    (not_exists_toImage_eq φ hnc) ((Scheme.Modules.pullback φ.imageι).obj M) 1
  let e : (Scheme.Modules.pullback φ).obj M ≅
      (Scheme.Modules.pullback φ.toImage).obj ((Scheme.Modules.pullback φ.imageι).obj M) :=
    (Scheme.Modules.pullbackCongr φ.toImage_imageι.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp φ.toImage φ.imageι).app M).symm
  rw [degreeOn, degreeOn, invertibleCurveDegree_eq_curveDegree_one,
    invertibleCurveDegree_eq_curveDegree_one, curveDegree_eq_of_iso k (φ ≫ sX) _ 1 e]
  exact key

/-- If `φ(C)` is not a point, the function field `k(C)` is a finite extension of the function
field `k(T)` of the reduced image `T` of `φ`. -/
theorem finite_functionField_image [IsCurve k (φ ≫ sX)] [IsProper (φ ≫ sX)]
    [IsSeparated sX] [LocallyOfFiniteType sX] (hnc : ¬ ∃ x : X, Set.range φ = {x}) :
    haveI : IsProper φ := IsProper.of_comp φ sX
    letI := functionFieldMapAlgebra φ.toImage
    Module.Finite φ.image.functionField C.functionField := by
  have : IsProper φ := IsProper.of_comp φ sX
  have : IsCurve k (φ.imageι ≫ sX) := isCurve_imageι_comp sX φ hnc
  exact finite_functionField_of_topologicalKrullDim_eq (φ.imageι ≫ sX) φ.toImage
    ((IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sX)).trans
      (IsCurve.topologicalKrullDim_eq_one (f := φ.imageι ≫ sX)).symm)

/-! ### Intersection numbers under a morphism of proper varieties -/

/-- The degree of an invertible sheaf on a proper curve depends on the structure morphism only
through its value. -/
theorem invertibleCurveDegree_congr_structure {Z : Scheme.{u}} {π π' : Z ⟶ Spec (.of k)}
    (h : π = π') [IsProper π] [IsProper π'] (hdim : topologicalKrullDim Z ≤ 1) (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    invertibleCurveDegree k π hdim L = invertibleCurveDegree k π' hdim L := by
  subst h; rfl

section Pullback

variable {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (f : X ⟶ Y) (i : C ⟶ X)

/-- `deg_C i^*(f^*N) = deg_C (i ≫ f)^*N` for a `k`-morphism `f : X ⟶ Y` and a curve
`i : C ⟶ X` proper over `k`. -/
theorem degreeOn_pullback_eq_degreeOn_comp (hf : f ≫ sY = sX) [IsProper (i ≫ sX)]
    [IsProper ((i ≫ f) ≫ sY)] (hdim : topologicalKrullDim C ≤ 1) (N : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N] :
    degreeOn k sX i hdim ((Scheme.Modules.pullback f).obj N) = degreeOn k sY (i ≫ f) hdim N := by
  let e : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj N) ≅
      (Scheme.Modules.pullback (i ≫ f)).obj N := (Scheme.Modules.pullbackComp i f).app N
  rw [degreeOn, degreeOn, invertibleCurveDegree_eq_of_iso k (i ≫ sX) hdim e]
  exact invertibleCurveDegree_congr_structure (by rw [Category.assoc, hf]) hdim _

variable [IsProperVariety k sX] [IsProperVariety k sY] [IsNormal Y] [IsClosedImmersion i]
  [IsCurve k (i ≫ sX)]

/-- **`(f^*M · C) = 0` when `f(C)` is a point.** Let `f : X ⟶ Y` be a morphism of proper
varieties over `k` with `Y` normal, `C ⊆ X` an irreducible closed curve and `M` a Cartier divisor
on `Y`. If `f(C)` is a point, then `(f^*M · C) = deg_C f^* 𝒪_Y(M) = 0`. -/
@[mmp "lem_mmp_foundation_km_curve_degree_projection"]
theorem degreeOn_pullback_divisorialSheaf_eq_zero (hf : f ≫ sY = sX)
    (M : Divisor Y) (hM : haveI := LocallyOfFiniteType.isLocallyNoetherian sY; M.IsCartier)
    (hpt : ∃ y : Y, Set.range (i ≫ f) = {y}) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := hM.isInvertibleModule_divisorialSheaf
    degreeOn k sX i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sX)).le
      ((Scheme.Modules.pullback f).obj M.divisorialSheaf) = 0 := by
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hM.isInvertibleModule_divisorialSheaf
  have h : (i ≫ f) ≫ sY = i ≫ sX := by rw [Category.assoc, hf]
  have : IsProper ((i ≫ f) ≫ sY) := h ▸ inferInstance
  have : IsCurve k ((i ≫ f) ≫ sY) := h ▸ inferInstance
  rw [degreeOn_pullback_eq_degreeOn_comp sX sY f i hf]
  exact degreeOn_eq_zero_of_range_eq_singleton sY (i ≫ f) _ hpt

/-- **`(f^*M · C) = deg(C → f(C)) · (M · f(C))` when `f(C)` is a curve.** Let `f : X ⟶ Y` be a
morphism of proper varieties over `k` with `Y` normal, `C ⊆ X` an irreducible closed curve and
`M` a Cartier divisor on `Y`. If the reduced image `f(C)` is a curve, then
`(f^*M · C) = deg_C f^* 𝒪_Y(M) = [k(C) : k(f(C))] · (M · f(C))`. -/
@[mmp "lem_mmp_foundation_km_curve_degree_projection"]
theorem degreeOn_pullback_divisorialSheaf_eq_degreeOver_mul_intersectionNumber
    (hf : f ≫ sY = sX) (M : Divisor Y)
    (hM : haveI := LocallyOfFiniteType.isLocallyNoetherian sY; M.IsCartier)
    (hcurve : IsCurve k ((i ≫ f).imageι ≫ sY)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := hM.isInvertibleModule_divisorialSheaf
    haveI : IsProper (f ≫ sY) := hf ▸ (inferInstance : IsProper sX)
    haveI : IsProper f := IsProper.of_comp f sY
    haveI : IsProper ((i ≫ f).imageι ≫ sY) := isProper_imageι_comp (i ≫ f) sY
    (degreeOn k sX i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sX)).le
        ((Scheme.Modules.pullback f).obj M.divisorialSheaf) : ℚ) =
      (degreeOver (i ≫ f).toImage : ℚ) *
        (Divisor.toQDivisor M).intersectionNumber k sY (i ≫ f).imageι
          hcurve.topologicalKrullDim_eq_one.le (QDivisor.isQCartier_toQDivisor hM) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hM.isInvertibleModule_divisorialSheaf
  have h : (i ≫ f) ≫ sY = i ≫ sX := by rw [Category.assoc, hf]
  have : IsProper ((i ≫ f) ≫ sY) := h ▸ inferInstance
  have : IsCurve k ((i ≫ f) ≫ sY) := h ▸ inferInstance
  have : IsProper (f ≫ sY) := hf ▸ (inferInstance : IsProper sX)
  have : IsProper f := IsProper.of_comp f sY
  have : IsProper ((i ≫ f).imageι ≫ sY) := isProper_imageι_comp (i ≫ f) sY
  have hnc : ¬ ∃ y : Y, Set.range (i ≫ f) = {y} := by
    intro hpt
    have := subsingleton_image sY (i ≫ f) hpt
    have h0 : topologicalKrullDim (i ≫ f).image ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hcurve.topologicalKrullDim_eq_one] at h0
    norm_num at h0
  rw [QDivisor.intersectionNumber_toQDivisor k sY _ _ M hM, Divisor.degreeOn,
    degreeOn_pullback_eq_degreeOn_comp sX sY f i hf,
    degreeOn_eq_degreeOver_mul sY (i ≫ f) _ hnc]
  push_cast
  rfl

end Pullback

end MMP.Mori
