/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.Properness
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.Topology.Dimension.NowhereDense
public import StacksFrontier.Topology.Dimension.KrullSeparation
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelGenusZero
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponent
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The exceptional locus of a resolution of a surface

Let `X` be a normal surface over a field `k` and `f : Y ⟶ X` a resolution: a proper birational
morphism with `Y` smooth over `k`. Let `S` be the set of points of `X` whose fibre is infinite.
By Zariski's main theorem `f` is an isomorphism over `X ∖ S`. Since `Y` is a surface, the closed
subset `f⁻¹(S) ⊊ Y` has dimension at most one, so a point of `f⁻¹(S)` which is not closed is the
generic point of an irreducible component of `f⁻¹(S)`; as `f⁻¹(S)` has finitely many components
and the fibres over `S` are infinite, every point of `S` is closed and `S` is finite. The
`f`-exceptional curves, the curves `C ⊆ Y` with `f(C)` a point, are then exactly the
one-dimensional irreducible components of `f⁻¹(S)`, and `f⁻¹(S)` is proper over `k`, lying over
finitely many closed points.

If `h : Y' ⟶ Y` is a further proper birational morphism from a smooth surface, `h ≫ f` is a
resolution of `X`. A curve `C ⊆ Y'` is contracted by `h ≫ f` exactly when either `h(C)` is a
point, or `h(C)` is an `f`-exceptional curve `E`; in the latter case `h` is an isomorphism over the
generic point of `E`, and `C` is the birational transform `h⁻¹_* E`.

## Main results

* `MMP.Mori.exists_finite_isIso_and_isExceptionalCurve_iff`: the exceptional locus of a
  resolution of a surface lies over a finite set of closed points, and the exceptional curves
  are the one-dimensional components of its preimage.
* `MMP.Mori.isSmoothResolution_comp_and_isExceptionalCurve_comp_iff`: the exceptional curves of
  a composite resolution `h ≫ f` are the transforms `h⁻¹_* Eᵢ` and the `h`-exceptional curves.
* `MMP.Mori.finite_and_isClosed_singleton_compl_finiteFibreLocus`: the points with infinite fibre
  of a proper birational morphism from a Noetherian integral scheme of dimension at most two onto
  a normal integral scheme form a finite set of closed points.
* `MMP.Mori.isCurveIn_inverseTransformIdeal`: the birational transform of a curve under such a
  morphism is a curve.
* `MMP.Mori.isBirationalMorphism_comp_of_isBirational`: composites of proper birational
  morphisms are birational.

## Implementation notes

A resolution is `MMP.Mori.IsSmoothResolution`, an `f`-exceptional curve is
`MMP.Mori.IsExceptionalCurve` (a curve, an integral closed subscheme of dimension one, with image
a point), and the birational transform `h⁻¹_* E` of a curve `E` is the reduced closed subscheme
`MMP.Mori.inverseTransformIdeal h E.support`. The surface `X` is a normal variety of dimension
two, as in KM Notation 4.1; normality is needed, since for a non-normal surface the
normalization may be a resolution which is not an isomorphism over a curve. That `Y` and `Y'` are
surfaces (integral, of dimension two) follows from birationality and is proved, not assumed.

The irreducible components of `f⁻¹(S)` are its maximal irreducible subsets. The closed
subscheme `f⁻¹(S)` is taken with its reduced structure, the vanishing ideal of the closed set
`f⁻¹(S)`. The set `S` produced is the set of points with infinite fibre,
`(MMP.Resolution.Bridges.finiteFibreLocus f)ᶜ`.

The list `E₁, …, E_r` of the `f`-exceptional curves, and likewise `F₁, …, F_s`, is encoded by the
predicate `MMP.Mori.IsExceptionalCurve`: the statement about the composite says that the
`(h ≫ f)`-exceptional curves are exactly the `h⁻¹_* E` and the `h`-exceptional curves, that the
`h⁻¹_* E` are not `h`-exceptional, and that `E ↦ h⁻¹_* E` is injective, so that the list
`h⁻¹_* E₁, …, h⁻¹_* E_r, F₁, …, F_s` has no repetitions.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Notation 4.1, 4.5, 4.7
* [R. Hartshorne, *Algebraic geometry*][Har77], II Ex. 3.22, III.11.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

open MMP.Resolution.Bridges (finiteFibreLocus isOpen_finiteFibreLocus_and_isIso)

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- A space of dimension at most two has no chain `a < b < c < d` of irreducible closed
subsets. -/
theorem false_of_lt_lt_lt_of_topologicalKrullDim_le_two (hdim : topologicalKrullDim T ≤ 2)
    {a b c d : IrreducibleCloseds T} (h1 : a < b) (h2 : b < c) (h3 : c < d) : False := by
  let p : LTSeries (IrreducibleCloseds T) :=
    RelSeries.fromListIsChain [a, b, c, d] (by simp)
      (by simp [h1, h2, h3])
  have hp : p.length = 3 := rfl
  have := Order.LTSeries.length_le_krullDim p
  rw [hp] at this
  have h' : ((3 : ℕ) : WithBot ℕ∞) ≤ 2 := this.trans hdim
  exact absurd h' (by decide)

/-- In an irreducible Noetherian space of dimension at most two, a proper closed subset has
dimension at most one. -/
theorem topologicalKrullDim_le_one_of_ne_univ [NoetherianSpace T] [IrreducibleSpace T]
    (hdim : topologicalKrullDim T ≤ 2) {W : Set T} (hW : IsClosed W) (hne : W ≠ Set.univ) :
    topologicalKrullDim W ≤ 1 := by
  have hnd : IsNowhereDense W := by
    rw [hW.isNowhereDense_iff, interior_eq_empty_iff_dense_compl]
    exact hW.isOpen_compl.dense (Set.nonempty_compl.mpr hne)
  have h2 := (hnd.topologicalKrullDim_add_one_le hW).trans hdim
  have h2' : topologicalKrullDim W + ((1 : ℕ) : WithBot ℕ∞) ≤
      ((1 : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h2
  exact_mod_cast ENat.WithBot.add_le_add_natCast_right_iff.mp h2'

/-- In a quasi-compact `T₀` space, a point which is not closed specializes to a closed point
different from it. -/
theorem exists_isClosed_singleton_specializes [T0Space T] [CompactSpace T] {e : T}
    (he : ¬ IsClosed ({e} : Set T)) : ∃ c, IsClosed ({c} : Set T) ∧ e ⤳ c ∧ e ≠ c := by
  obtain ⟨c, hc, hcl⟩ := isClosed_closure.exists_closed_singleton
    (S := closure ({e} : Set T)) ⟨e, subset_closure rfl⟩
  refine ⟨c, hcl, specializes_iff_mem_closure.mpr hc, ?_⟩
  rintro rfl
  exact he hcl

/-- In an irreducible Noetherian `T₀` space of dimension at most two, a proper closed subset
containing a nontrivial specialization `e ⤳ c` has dimension one. -/
theorem topologicalKrullDim_eq_one_of_ne_univ [NoetherianSpace T] [IrreducibleSpace T]
    [T0Space T] (hdim : topologicalKrullDim T ≤ 2) {W : Set T} (hW : IsClosed W)
    (hne : W ≠ Set.univ) {e c : T} (he : e ∈ W) (hc : c ∈ W) (hec : e ⤳ c) (hne' : e ≠ c) :
    topologicalKrullDim W = 1 := by
  refine le_antisymm (topologicalKrullDim_le_one_of_ne_univ hdim hW hne) ?_
  exact one_le_topologicalKrullDim_of_specializes_of_ne (x := (⟨e, he⟩ : W)) (y := ⟨c, hc⟩)
    ((subtype_specializes_iff _ _).mpr hec) (fun h ↦ hne' (congrArg Subtype.val h))

/-- In an irreducible quasi-compact `T₀` space of dimension at most two, the closure of a point
`e` which is not closed is a maximal proper irreducible closed subset: it equals every proper
irreducible closed subset containing `e`. -/
theorem closure_singleton_eq_of_not_isClosed [T0Space T] [CompactSpace T] [IrreducibleSpace T]
    (hdim : topologicalKrullDim T ≤ 2) {e : T} (he : ¬ IsClosed ({e} : Set T)) {B : Set T}
    (hB : IsIrreducible B) (hBc : IsClosed B) (heB : e ∈ B) (hBne : B ≠ Set.univ) :
    closure ({e} : Set T) = B := by
  obtain ⟨c, hcl, hec, hne⟩ := exists_isClosed_singleton_specializes he
  by_contra hEB
  let a : IrreducibleCloseds T := ⟨{c}, isIrreducible_singleton, hcl⟩
  let b : IrreducibleCloseds T := ⟨closure {e}, isIrreducible_singleton.closure, isClosed_closure⟩
  let c' : IrreducibleCloseds T := ⟨B, hB, hBc⟩
  let d : IrreducibleCloseds T := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  have hsub : closure ({e} : Set T) ⊆ B := closure_minimal (by simpa using heB) hBc
  refine false_of_lt_lt_lt_of_topologicalKrullDim_le_two hdim (a := a) (b := b) (c := c') (d := d)
    ?_ ?_ ?_
  · refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
    · obtain rfl : x = c := hx
      exact specializes_iff_mem_closure.mp hec
    · have : e ∈ (b : Set T) := subset_closure rfl
      rw [← h] at this
      exact hne this
  · exact lt_of_le_of_ne hsub fun h ↦ hEB (congrArg SetLike.coe h)
  · exact lt_of_le_of_ne (Set.subset_univ _) fun h ↦ hBne (congrArg SetLike.coe h)

end Topology

section Scheme

variable {X Y : Scheme.{u}}

/-- A closed subscheme which is reduced is cut out by the vanishing ideal of its support. -/
theorem vanishingIdeal_support_eq_self (I : X.IdealSheafData) [IsReduced I.subscheme] :
    Scheme.IdealSheafData.vanishingIdeal I.support = I :=
  MMP.Positivity.vanishingIdeal_support_of_isReduced I

/-- A closed subscheme has the dimension of its support. -/
theorem topologicalKrullDim_subscheme_eq (I : X.IdealSheafData) :
    topologicalKrullDim I.subscheme = topologicalKrullDim (I.support : Set X) := by
  rw [I.subschemeι.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    I.range_subschemeι]

/-- The support of an integral closed subscheme is irreducible. -/
theorem isIrreducible_support_of_isIntegral (I : X.IdealSheafData) [IsIntegral I.subscheme] :
    IsIrreducible (I.support : Set X) := by
  rw [← I.range_subschemeι, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ I.subschemeι.continuous.continuousOn

/-- The support of a curve has at least two points. -/
theorem IsCurveIn.not_subsingleton {C : X.IdealSheafData} (hC : IsCurveIn C) :
    ¬ (C.support : Set X).Subsingleton := by
  intro hs
  have h1 := hC.2
  rw [topologicalKrullDim_subscheme_eq] at h1
  have : Subsingleton (C.support : Set X) := hs.coe_sort
  have h0 := topologicalKrullDim_zero_of_discreteTopology (C.support : Set X)
  rw [h1] at h0
  exact absurd h0 (by decide)

/-- The support of a curve is the closure of a point which is not closed: its generic point. -/
theorem IsCurveIn.exists_isGenericPoint {C : X.IdealSheafData} (hC : IsCurveIn C) :
    ∃ e : X, closure ({e} : Set X) = C.support ∧ ¬ IsClosed ({e} : Set X) := by
  have := hC.1
  obtain ⟨e, he⟩ := QuasiSober.sober (isIrreducible_support_of_isIntegral C) C.support.isClosed
  refine ⟨e, he, fun hcl ↦ hC.not_subsingleton ?_⟩
  rw [← he.def, hcl.closure_eq]
  exact Set.subsingleton_singleton

/-- The restriction `f⁻¹(V) ⟶ V` of `f` agrees with `f` on points. -/
theorem ι_morphismRestrict_apply (f : X ⟶ Y) (V : Y.Opens) (z : (f ⁻¹ᵁ V).toScheme) :
    V.ι ((f ∣_ V) z) = f ((f ⁻¹ᵁ V).ι z) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- If `f` restricts to an isomorphism `f⁻¹(V) ⟶ V`, specializations between points of `V`
lift to specializations between their preimages. -/
theorem specializes_of_isIso_morphismRestrict (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    {a b : X} (ha : f a ∈ V) (hb : f b ∈ V) (hab : f a ⤳ f b) : a ⤳ b := by
  let za : (f ⁻¹ᵁ V).toScheme := ⟨a, show a ∈ f ⁻¹ᵁ V from ha⟩
  let zb : (f ⁻¹ᵁ V).toScheme := ⟨b, show b ∈ f ⁻¹ᵁ V from hb⟩
  have h1 : (f ∣_ V) za ⤳ (f ∣_ V) zb := by
    rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff, ι_morphismRestrict_apply,
      ι_morphismRestrict_apply]
    exact hab
  exact ((f ∣_ V).homeomorph.isInducing.specializes_iff.mp h1).map (f ⁻¹ᵁ V).ι.continuous

/-- On a scheme of dimension two, a curve is not the whole space. -/
theorem support_ne_univ_of_isCurveIn (hdimX : topologicalKrullDim X = 2)
    {E : X.IdealSheafData} (hE : IsCurveIn E) : (E.support : Set X) ≠ Set.univ := by
  intro h
  have h1 := hE.2
  rw [topologicalKrullDim_subscheme_eq, h,
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hdimX] at h1
  exact absurd h1 (by decide)

end Scheme

section Core

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNormal X] [IsLocallyNoetherian X]
  [CompactSpace Y] [NoetherianSpace Y] (f : Y ⟶ X) [IsProper f]

omit [IsNormal X] [CompactSpace Y] [NoetherianSpace Y] in
/-- A proper birational morphism of integral schemes maps the generic point to the generic
point. -/
theorem map_genericPoint_eq (hb : IsBirational f) : f (genericPoint Y) = genericPoint X := by
  change genericPoint Y ∈ f ⁻¹' {genericPoint X}
  rw [preimage_genericPoint f hb]
  rfl

omit [IsNormal X] [CompactSpace Y] [NoetherianSpace Y] in
/-- For a proper birational morphism `f : Y ⟶ X` of integral schemes, the generic point of `X`,
the image of the generic point of `Y`, has finite fibre. -/
theorem map_genericPoint_mem_finiteFibreLocus (hb : IsBirational f) :
    f (genericPoint Y) ∈ finiteFibreLocus f := by
  change (f ⁻¹' {f (genericPoint Y)}).Finite
  rw [map_genericPoint_eq f hb, preimage_genericPoint f hb]
  exact Set.finite_singleton _

omit [IsLocallyNoetherian X] [CompactSpace Y] [NoetherianSpace Y] in
/-- For a proper birational morphism onto a normal integral scheme, the set of points with
infinite fibre is closed. -/
theorem isClosed_compl_finiteFibreLocus (hb : IsBirational f) :
    IsClosed (finiteFibreLocus f)ᶜ := by
  obtain ⟨hU, -⟩ := (isOpen_finiteFibreLocus_and_isIso f hb).1 inferInstance
  exact hU.isClosed_compl

omit [IsNormal X] [NoetherianSpace Y] in
/-- Let `f : Y ⟶ X` be a proper birational morphism with `dim Y ≤ 2` and `S` the set of points
of `X` with infinite fibre. A point `y ∈ f⁻¹(S)` which is not closed is the generic point of
every irreducible closed subset of `f⁻¹(S)` containing it. -/
theorem closure_singleton_eq_of_subset_preimage (hb : IsBirational f)
    (hdim : topologicalKrullDim Y ≤ 2) {y : Y} (hy : ¬ IsClosed ({y} : Set Y)) {B : Set Y}
    (hB : IsIrreducible B) (hBc : IsClosed B) (hyB : y ∈ B)
    (hBS : B ⊆ f ⁻¹' (finiteFibreLocus f)ᶜ) : closure ({y} : Set Y) = B :=
  closure_singleton_eq_of_not_isClosed hdim hy hB hBc hyB fun h ↦
    hBS (h ▸ Set.mem_univ (genericPoint Y)) (map_genericPoint_mem_finiteFibreLocus f hb)

/-- Let `f : Y ⟶ X` be a proper birational morphism of integral schemes, `X` normal and locally
Noetherian, `Y` Noetherian of dimension at most two. Then the set `S` of points of `X` with
infinite fibre is a finite set of closed points. -/
theorem finite_and_isClosed_singleton_compl_finiteFibreLocus (hb : IsBirational f)
    (hdim : topologicalKrullDim Y ≤ 2) :
    (finiteFibreLocus f)ᶜ.Finite ∧ ∀ x ∈ (finiteFibreLocus f)ᶜ, IsClosed ({x} : Set X) := by
  set S := (finiteFibreLocus f)ᶜ
  have hT : IsClosed (f ⁻¹' S) := (isClosed_compl_finiteFibreLocus f hb).preimage f.continuous
  obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  set G : Set Y := ⋃ W ∈ Z, {y | IsGenericPoint y W}
  have hG : G.Finite := hZf.biUnion fun W _ ↦ Set.Subsingleton.finite
    fun a (ha : IsGenericPoint a W) b (hb : IsGenericPoint b W) ↦ ha.eq hb
  have hmem : ∀ y ∈ f ⁻¹' S, ∃ W ∈ Z, y ∈ W := by
    intro y hy
    rw [hZ] at hy
    simpa using hy
  have hWsub : ∀ W ∈ Z, W ⊆ f ⁻¹' S := fun W hW ↦ hZ ▸ Set.subset_sUnion_of_mem hW
  have hNC : ∀ y ∈ f ⁻¹' S, ¬ IsClosed ({y} : Set Y) → y ∈ G := by
    intro y hy hyc
    obtain ⟨W, hW, hyW⟩ := hmem y hy
    exact Set.mem_biUnion hW
      (closure_singleton_eq_of_subset_preimage f hb hdim hyc (hZirr W hW) (hZc W hW) hyW
        (hWsub W hW))
  have hclosed : ∀ x ∈ S, IsClosed ({x} : Set X) := by
    intro x hx
    by_contra hxc
    apply hx
    refine hG.subset fun y hy ↦ hNC y (show f y ∈ S from (show f y = x from hy) ▸ hx) ?_
    intro hyc
    apply hxc
    have h := f.isClosedMap _ hyc
    rwa [Set.image_singleton, show f y = x from hy] at h
  refine ⟨(hG.image f).subset fun x hx ↦ ?_, hclosed⟩
  obtain ⟨y, hy⟩ := (show (f ⁻¹' {x}).Infinite from hx).nonempty
  have hy' : f y = x := hy
  obtain ⟨W, hW, hyW⟩ := hmem y (show f y ∈ S from hy' ▸ hx)
  obtain ⟨g, hg⟩ := QuasiSober.sober (hZirr W hW) (hZc W hW)
  refine ⟨g, Set.mem_biUnion hW hg, ?_⟩
  have hgS : f g ∈ S := hWsub W hW hg.mem
  have hsp : f g ⤳ f y := (hg.specializes hyW).map f.continuous
  have hcl := specializes_iff_mem_closure.mp hsp
  rw [(hclosed _ hgS).closure_eq] at hcl
  exact (hcl : f y = f g).symm.trans hy'

/-- In the situation of `MMP.Mori.finite_and_isClosed_singleton_compl_finiteFibreLocus`, the
`f`-exceptional curves are exactly the curves whose support is an irreducible component of
`f⁻¹(S)`. -/
theorem isExceptionalCurve_iff_maximal (hb : IsBirational f)
    (hdim : topologicalKrullDim Y ≤ 2) (C : Y.IdealSheafData) :
    IsExceptionalCurve f C ↔ IsCurveIn C ∧
      Maximal (fun Z : Set Y ↦ IsIrreducible Z ∧ Z ⊆ f.base ⁻¹' (finiteFibreLocus f)ᶜ)
        (C.support : Set Y) := by
  set S := (finiteFibreLocus f)ᶜ
  have hT : IsClosed (f ⁻¹' S) := (isClosed_compl_finiteFibreLocus f hb).preimage f.continuous
  have hclosed := (finite_and_isClosed_singleton_compl_finiteFibreLocus f hb hdim).2
  constructor
  · rintro ⟨hC, x, hx⟩
    have := hC.1
    obtain ⟨e, he, hecl⟩ := hC.exists_isGenericPoint
    obtain ⟨c, -, hec, hne⟩ := exists_isClosed_singleton_specializes hecl
    have hcC : c ∈ (C.support : Set Y) := he ▸ specializes_iff_mem_closure.mp hec
    have heC : e ∈ (C.support : Set Y) := he ▸ subset_closure rfl
    have hfx : ∀ y ∈ (C.support : Set Y), f y = x := fun y hy ↦ hx.subset ⟨y, hy, rfl⟩
    have hxS : x ∈ S := by
      intro hxU
      obtain ⟨hU, hiso⟩ := (isOpen_finiteFibreLocus_and_isIso f hb).1 inferInstance
      have hfe : f e ∈ (⟨finiteFibreLocus f, hU⟩ : X.Opens) := by
        rw [hfx e heC]
        exact hxU
      exact hne (Stacks.Models.eq_of_isIso_morphismRestrict f _ hfe
        ((hfx e heC).trans (hfx c hcC).symm))
    have hsub : (C.support : Set Y) ⊆ f.base ⁻¹' S :=
      fun y hy ↦ show f y ∈ S from hfx y hy ▸ hxS
    refine ⟨hC, ⟨isIrreducible_support_of_isIntegral C, hsub⟩, fun W ⟨hW, hWS⟩ hCW ↦ ?_⟩
    have h := closure_singleton_eq_of_subset_preimage f hb hdim hecl hW.closure isClosed_closure
      (subset_closure (hCW heC)) (closure_minimal hWS hT)
    rw [he] at h
    exact h ▸ subset_closure
  · rintro ⟨hC, ⟨-, hsub⟩, -⟩
    obtain ⟨e, he, -⟩ := hC.exists_isGenericPoint
    have heC : e ∈ (C.support : Set Y) := he ▸ subset_closure rfl
    have hcl : IsClosed ({f e} : Set X) := hclosed _ (hsub heC)
    refine ⟨hC, f e, Set.Subset.antisymm ?_ ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [← he] at hy
      have h := specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hy).map
        f.continuous)
      rwa [hcl.closure_eq] at h
    · rintro _ rfl
      exact ⟨e, heC, rfl⟩

/-- In the situation of `MMP.Mori.finite_and_isClosed_singleton_compl_finiteFibreLocus`, the
one-dimensional irreducible components of `f⁻¹(S)` are exactly the supports of the
`f`-exceptional curves. -/
theorem maximal_and_topologicalKrullDim_eq_one_iff (hb : IsBirational f)
    (hdim : topologicalKrullDim Y ≤ 2) (W : Set Y) :
    (Maximal (fun Z : Set Y ↦ IsIrreducible Z ∧ Z ⊆ f.base ⁻¹' (finiteFibreLocus f)ᶜ) W ∧
        topologicalKrullDim W = 1) ↔
      ∃ C : Y.IdealSheafData, IsExceptionalCurve f C ∧ (C.support : Set Y) = W := by
  have hT : IsClosed (f ⁻¹' (finiteFibreLocus f)ᶜ) :=
    (isClosed_compl_finiteFibreLocus f hb).preimage f.continuous
  constructor
  · rintro ⟨hmax, hdim1⟩
    have hWc : IsClosed W :=
      closure_subset_iff_isClosed.mp
        (hmax.2 ⟨hmax.1.1.closure, closure_minimal hmax.1.2 hT⟩ subset_closure)
    set C := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩ with hCdef
    have hsupp : (C.support : Set Y) = W := by
      rw [hCdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have : IsIntegral C.subscheme :=
      StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible ⟨W, hWc⟩ hmax.1.1
    have hCc : IsCurveIn C := ⟨this, by rw [topologicalKrullDim_subscheme_eq, hsupp, hdim1]⟩
    exact ⟨C, (isExceptionalCurve_iff_maximal f hb hdim C).mpr ⟨hCc, hsupp ▸ hmax⟩, hsupp⟩
  · rintro ⟨C, hC, rfl⟩
    have h := (isExceptionalCurve_iff_maximal f hb hdim C).mp hC
    exact ⟨h.2, (topologicalKrullDim_subscheme_eq C).symm.trans h.1.2⟩

/-- In the situation of `MMP.Mori.finite_and_isClosed_singleton_compl_finiteFibreLocus`, `f` is
an isomorphism over a neighbourhood of every point of `X` which is not closed. -/
theorem mem_biregularLocus_of_not_isClosed (hb : IsBirational f)
    (hdim : topologicalKrullDim Y ≤ 2) {e : X} (he : ¬ IsClosed ({e} : Set X)) :
    e ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (isOpen_finiteFibreLocus_and_isIso f hb).1 inferInstance
  refine le_biregularLocus (f := f) (V := ⟨_, hU⟩) hiso ?_
  by_contra h
  exact he ((finite_and_isClosed_singleton_compl_finiteFibreLocus f hb hdim).2 e h)

/-- In the situation of `MMP.Mori.finite_and_isClosed_singleton_compl_finiteFibreLocus`, let `Z`
be the closure of a point `e` which is not closed. For the point `c` over `e`, the birational
transform `f⁻¹_*(Z)` is the closure of `c`. -/
theorem coe_inverseTransform_eq_closure (hb : IsBirational f)
    (hdim : topologicalKrullDim Y ≤ 2) {Z : Closeds X} {e : X}
    (he : closure ({e} : Set X) = Z) (hecl : ¬ IsClosed ({e} : Set X)) {c : Y} (hc : f c = e) :
    (inverseTransform f Z : Set Y) = closure {c} := by
  have heV := mem_biregularLocus_of_not_isClosed f hb hdim hecl
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hcmem : c ∈ f ⁻¹' ((Z : Set X) ∩ biregularLocus f) := by
    change f c ∈ (Z : Set X) ∩ biregularLocus f
    rw [hc]
    exact ⟨he ▸ subset_closure rfl, heV⟩
  rw [inverseTransform, Closeds.coe_closure]
  apply Set.Subset.antisymm
  · refine closure_minimal (fun y hy ↦ ?_) isClosed_closure
    have hsp : f c ⤳ f y := by
      rw [hc]
      exact specializes_iff_mem_closure.mpr (he ▸ hy.1)
    exact specializes_iff_mem_closure.mp
      (specializes_of_isIso_morphismRestrict f _ (hc ▸ heV) hy.2 hsp)
  · exact closure_minimal (Set.singleton_subset_iff.mpr (subset_closure hcmem)) isClosed_closure

/-- In the situation of `MMP.Mori.finite_and_isClosed_singleton_compl_finiteFibreLocus`, with
`dim X = 2`, the birational transform `f⁻¹_* E` of a curve `E ⊆ X` is a curve which `f` maps
onto `E`. -/
theorem isCurveIn_inverseTransformIdeal (hb : IsBirational f)
    (hdim : topologicalKrullDim Y ≤ 2) (hdimX : topologicalKrullDim X = 2)
    {E : X.IdealSheafData} (hE : IsCurveIn E) :
    IsCurveIn (inverseTransformIdeal f E.support) ∧
      f.base '' (inverseTransform f E.support : Set Y) = E.support := by
  obtain ⟨e, he, hecl⟩ := hE.exists_isGenericPoint
  have heV := mem_biregularLocus_of_not_isClosed f hb hdim hecl
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  obtain ⟨c, hc⟩ := AlgebraicGeometry.exists_eq_of_isIso_morphismRestrict f _ _ heV
  have hW := coe_inverseTransform_eq_closure f hb hdim he hecl hc
  have himage : f.base '' (inverseTransform f E.support : Set Y) = E.support := by
    rw [hW, ← IsClosedMap.closure_image_eq_of_continuous f.isClosedMap f.continuous,
      Set.image_singleton]
    exact hc ▸ he
  have hccl : ¬ IsClosed ({c} : Set Y) := fun h ↦ hecl (by
    have := f.isClosedMap _ h
    rwa [Set.image_singleton, hc] at this)
  obtain ⟨c', -, hcc', hne⟩ := exists_isClosed_singleton_specializes hccl
  have hWne : (inverseTransform f E.support : Set Y) ≠ Set.univ := by
    intro hu
    apply support_ne_univ_of_isCurveIn hdimX hE
    have hgen : genericPoint X ∈ (E.support : Set X) := by
      rw [← himage, hu]
      exact ⟨genericPoint Y, trivial, map_genericPoint_eq f hb⟩
    exact Set.eq_univ_of_forall fun x ↦
      ((genericPoint_spec X).specializes (Set.mem_univ x)).mem_closed E.support.isClosed hgen
  refine ⟨⟨?_, ?_⟩, himage⟩
  · rw [inverseTransformIdeal]
    refine StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ ?_
    rw [hW]
    exact isIrreducible_singleton.closure
  · rw [topologicalKrullDim_subscheme_eq, support_inverseTransformIdeal]
    refine topologicalKrullDim_eq_one_of_ne_univ hdim (inverseTransform f E.support).isClosed
      hWne (e := c) (c := c') (by rw [hW]; exact subset_closure rfl) ?_ hcc' hne
    rw [hW]
    exact specializes_iff_mem_closure.mp hcc'

end Core

section Proper

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType sX]

/-- A proper morphism `g : V ⟶ X` from a reduced scheme whose image is a closed point of a
scheme `X` locally of finite type over `k` is proper over `k`: it factors through
`Spec κ(x)`, which is finite over `k`. -/
theorem isProper_comp_of_range_subset_singleton {V : Scheme.{u}} [IsReduced V] (g : V ⟶ X)
    [IsProper g] {x : X} (hx : IsClosed ({x} : Set X)) (hg : Set.range g ⊆ {x}) :
    IsProper (g ≫ sX) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have H : (X.fromSpecResidueField x).ker ≤ g.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range g,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, Closeds.closure_le]
    intro y hy
    refine (X.fromSpecResidueField x).range_subset_ker_support ?_
    rw [Scheme.range_fromSpecResidueField]
    exact hg hy
  let l := IsClosedImmersion.lift (X.fromSpecResidueField x) g H
  have hl : l ≫ X.fromSpecResidueField x = g := IsClosedImmersion.lift_fac _ _ H
  have : IsProper (l ≫ X.fromSpecResidueField x) := by
    rw [hl]
    infer_instance
  have : IsProper l := IsProper.of_comp l (X.fromSpecResidueField x)
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [← hl, Category.assoc]
  infer_instance

/-- For a proper morphism `f : Y ⟶ X` to a scheme locally of finite type over `k` and a finite
set `S` of closed points of `X`, the closed subscheme `f⁻¹(S)` of `Y`, with its reduced
structure, is proper over `k`. -/
theorem isProper_subschemeι_comp_of_finite (f : Y ⟶ X) [IsProper f] {S : Set X}
    (hSf : S.Finite) (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (hT : IsClosed (f.base ⁻¹' S)) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' S, hT⟩).subschemeι ≫ f ≫ sX) := by
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' S, hT⟩ with hIdef
  set F : I.subscheme ⟶ X := I.subschemeι ≫ f with hFdef
  have hFS : ∀ z, F z ∈ S := by
    intro z
    have hz : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
    rw [I.range_subschemeι] at hz
    have hsupp : (I.support : Set Y) = f.base ⁻¹' S := by
      rw [hIdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rw [hsupp] at hz
    exact hz
  have hopen : ∀ x : S, IsOpen (F ⁻¹' {(x : X)}) := by
    intro x
    have hcl : IsClosed (⋃ y ∈ S \ {(x : X)}, ({y} : Set X)) :=
      hSf.sdiff.isClosed_biUnion fun y hy ↦ hS y hy.1
    have heq : F ⁻¹' {(x : X)} = (F ⁻¹' (⋃ y ∈ S \ {(x : X)}, ({y} : Set X)))ᶜ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_sdiff, exists_prop]
      constructor
      · rintro h ⟨y, ⟨-, hy⟩, rfl⟩
        exact hy h
      · intro h
        by_contra hne
        exact h ⟨F z, ⟨hFS z, hne⟩, rfl⟩
    rw [heq]
    exact (hcl.preimage F.continuous).isOpen_compl
  let O : S → I.subscheme.Opens := fun x ↦ ⟨F ⁻¹' {(x : X)}, hopen x⟩
  have : ∀ x, IsClosedImmersion (O x).ι := fun x ↦
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact (hS x x.2).preimage F.continuous)
  have : IsProper F := by
    rw [hFdef]
    infer_instance
  have : ∀ x : S, IsProper ((O x).ι ≫ I.subschemeι ≫ f ≫ sX) := by
    intro x
    have : IsProper ((O x).ι ≫ F) := inferInstance
    have h := isProper_comp_of_range_subset_singleton sX ((O x).ι ≫ F) (hS x x.2) (by
      rintro _ ⟨z, rfl⟩
      exact z.2)
    simpa [hFdef, Category.assoc] using h
  have : Finite S := hSf.to_subtype
  refine isProper_of_locallyFinite_open_closed_cover (I.subschemeι ≫ f ≫ sX) (fun x ↦ (O x).ι)
    (fun z ↦ ⟨⟨F z, hFS z⟩, ?_⟩) (locallyFinite_of_finite _) (locallyFinite_of_finite _)
  rw [Scheme.Opens.range_ι]
  rfl

end Proper

section Composite

variable {X Y Y' : Scheme.{u}}

/-- A composite of proper birational morphisms of integral schemes with normal locally Noetherian
targets is a birational morphism. -/
theorem isBirationalMorphism_comp_of_isBirational [IsIntegral X] [IsIntegral Y]
    [IsIntegral Y'] [IsNormal X] [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (h : Y' ⟶ Y) [IsProper f] [IsProper h] (hbf : IsBirational f)
    (hbh : IsBirational h) : IsBirationalMorphism (h ≫ f) := by
  obtain ⟨hUf, hisof⟩ := (isOpen_finiteFibreLocus_and_isIso f hbf).1 inferInstance
  obtain ⟨hUh, hisoh⟩ := (isOpen_finiteFibreLocus_and_isIso h hbh).1 inferInstance
  set Uf : X.Opens := ⟨_, hUf⟩
  set Uh : Y.Opens := ⟨_, hUh⟩
  have hcl : IsClosed (f.base '' (Uh : Set Y)ᶜ) := f.isClosedMap _ Uh.isOpen.isClosed_compl
  let W : X.Opens := Uf ⊓ ⟨_, hcl.isOpen_compl⟩
  have hηY : genericPoint Y ∈ Uh := by
    have := map_genericPoint_mem_finiteFibreLocus h hbh
    rwa [map_genericPoint_eq h hbh] at this
  have hηX : genericPoint X ∈ W := by
    refine ⟨?_, ?_⟩
    · have := map_genericPoint_mem_finiteFibreLocus f hbf
      rwa [map_genericPoint_eq f hbf] at this
    · rintro ⟨y, hy, hyη⟩
      have hy' : y ∈ f ⁻¹' {genericPoint X} := hyη
      rw [preimage_genericPoint f hbf] at hy'
      rw [hy'] at hy
      exact hy hηY
  have hWf : IsBiregular f W :=
    isBiregular_iff_le_biregularLocus.mpr (inf_le_left.trans (le_biregularLocus hisof))
  have hWh : IsBiregular h (f ⁻¹ᵁ W) := by
    refine isBiregular_iff_le_biregularLocus.mpr (le_trans ?_ (le_biregularLocus hisoh))
    intro y hy
    by_contra hyU
    exact hy.2 ⟨y, hyU, rfl⟩
  have hiso : IsIso ((h ≫ f) ∣_ W) := by
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hWh hWf
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (h ≫ f) ((h ≫ f) ⁻¹ᵁ W) W
    ⟨genericPoint Y', ?_⟩ ⟨_, hηX⟩ le_rfl ?_
  · change (h ≫ f) (genericPoint Y') ∈ W
    rw [Scheme.Hom.comp_apply, map_genericPoint_eq h hbh, map_genericPoint_eq f hbf]
    exact hηX
  · rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hiso

/-- The image of a set under `h ≫ f` is the image under `f` of its image under `h`. -/
theorem image_base_comp (f : Y ⟶ X) (h : Y' ⟶ Y) (Z : Set Y') :
    (h ≫ f).base '' Z = f.base '' (h.base '' Z) := by
  rw [← Set.image_comp]
  rfl

/-- For a proper birational morphism `f : Y ⟶ X` of integral schemes with `dim Y = 2`, a subset
of `Y` which `f` maps to a single point is not all of `Y`. -/
theorem ne_univ_of_image_eq_singleton [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsProper f] (hb : IsBirational f) (hdim : topologicalKrullDim Y = 2)
    {Z : Set Y} {x : X} (hZ : f.base '' Z = {x}) : Z ≠ Set.univ := by
  rintro rfl
  have hfib : (Set.univ : Set Y) ⊆ f ⁻¹' {x} := fun y _ ↦ hZ.subset ⟨y, Set.mem_univ y, rfl⟩
  have hxη : x = genericPoint X := by
    have := hfib (Set.mem_univ (genericPoint Y))
    rw [Set.mem_preimage, map_genericPoint_eq f hb] at this
    exact this.symm
  rw [hxη, preimage_genericPoint f hb] at hfib
  have : Subsingleton Y := ⟨fun a b ↦ (hfib (Set.mem_univ a)).trans (hfib (Set.mem_univ b)).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology Y
  rw [hdim] at h0
  exact absurd h0 (by decide)

/-- For a proper birational morphism `h : Y' ⟶ Y` of surfaces, the birational transform of an
`f`-exceptional curve is an `(h ≫ f)`-exceptional curve which is not `h`-exceptional. -/
theorem isExceptionalCurve_comp_inverseTransformIdeal [IsIntegral Y] [IsIntegral Y'] [IsNormal Y]
    [IsLocallyNoetherian Y] [NoetherianSpace Y'] (f : Y ⟶ X) (h : Y' ⟶ Y)
    [IsProper h] (hbh : IsBirational h) (hdY : topologicalKrullDim Y = 2)
    (hdY' : topologicalKrullDim Y' ≤ 2) {E : Y.IdealSheafData} (hE : IsExceptionalCurve f E) :
    IsExceptionalCurve (h ≫ f) (inverseTransformIdeal h E.support) ∧
      ¬ IsExceptionalCurve h (inverseTransformIdeal h E.support) := by
  obtain ⟨hE, x, hx⟩ := hE
  obtain ⟨hcurve, himE⟩ := isCurveIn_inverseTransformIdeal h hbh hdY' hdY hE
  refine ⟨⟨hcurve, x, ?_⟩, ?_⟩
  · rw [support_inverseTransformIdeal, image_base_comp, himE, hx]
  · rintro ⟨-, y, hy⟩
    rw [support_inverseTransformIdeal, himE] at hy
    exact hE.not_subsingleton (hy ▸ Set.subsingleton_singleton)

/-- For a proper birational morphism `h : Y' ⟶ Y` of surfaces, distinct curves on `Y` have
distinct birational transforms. -/
theorem eq_of_inverseTransformIdeal_eq [IsIntegral Y] [IsIntegral Y'] [IsNormal Y]
    [IsLocallyNoetherian Y] [NoetherianSpace Y'] (h : Y' ⟶ Y) [IsProper h]
    (hbh : IsBirational h) (hdY : topologicalKrullDim Y = 2) (hdY' : topologicalKrullDim Y' ≤ 2)
    {E E' : Y.IdealSheafData} (hE : IsCurveIn E) (hE' : IsCurveIn E')
    (heq : inverseTransformIdeal h E.support = inverseTransformIdeal h E'.support) : E = E' := by
  have h1 := (isCurveIn_inverseTransformIdeal h hbh hdY' hdY hE).2
  have h2 := (isCurveIn_inverseTransformIdeal h hbh hdY' hdY hE').2
  have hs : inverseTransform h E.support = inverseTransform h E'.support := by
    rw [← support_inverseTransformIdeal, heq, support_inverseTransformIdeal]
  rw [hs, h2] at h1
  have := hE.1
  have := hE'.1
  rw [← vanishingIdeal_support_eq_self E, ← vanishingIdeal_support_eq_self E']
  congr 1
  exact Closeds.ext h1.symm

/-- For proper birational morphisms `f : Y ⟶ X` and `h : Y' ⟶ Y` of surfaces, an
`(h ≫ f)`-exceptional curve is either `h`-exceptional or the birational transform of an
`f`-exceptional curve. -/
theorem exists_eq_inverseTransformIdeal_or_isExceptionalCurve [IsIntegral X] [IsIntegral Y]
    [IsIntegral Y'] [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [NoetherianSpace Y'] (f : Y ⟶ X) (h : Y' ⟶ Y)
    [IsProper f] [IsProper h] (hbf : IsBirational f) (hbh : IsBirational h)
    (hdY : topologicalKrullDim Y = 2) (hdY' : topologicalKrullDim Y' ≤ 2)
    {C : Y'.IdealSheafData} (hC : IsExceptionalCurve (h ≫ f) C) :
    (∃ E : Y.IdealSheafData, IsExceptionalCurve f E ∧ C = inverseTransformIdeal h E.support) ∨
      IsExceptionalCurve h C := by
  obtain ⟨hCc, x, hx⟩ := hC
  obtain ⟨c, hc, hccl⟩ := hCc.exists_isGenericPoint
  by_cases hsub : (h.base '' (C.support : Set Y')).Subsingleton
  · exact Or.inr ⟨hCc, h c, hsub.eq_singleton_of_mem ⟨c, hc ▸ subset_closure rfl, rfl⟩⟩
  left
  have hEcl : IsClosed (h.base '' (C.support : Set Y')) := h.isClosedMap _ C.support.isClosed
  have hEeq : h.base '' (C.support : Set Y') = closure {h c} := by
    rw [← hc, ← IsClosedMap.closure_image_eq_of_continuous h.isClosedMap h.continuous,
      Set.image_singleton]
  set E : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨_, hEcl⟩ with hEdef
  have hEsupp : (E.support : Set Y) = h.base '' (C.support : Set Y') := by
    rw [hEdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hhccl : ¬ IsClosed ({h c} : Set Y) := fun hcl ↦ hsub (by
    rw [hEeq, hcl.closure_eq]
    exact Set.subsingleton_singleton)
  obtain ⟨d, -, hcd, hne⟩ := exists_isClosed_singleton_specializes hhccl
  have hfE : f.base '' (E.support : Set Y) = {x} := by rw [hEsupp, ← image_base_comp, hx]
  have hEc : IsCurveIn E := by
    refine ⟨?_, ?_⟩
    · rw [hEdef]
      refine StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ ?_
      change IsIrreducible (h.base '' (C.support : Set Y'))
      rw [hEeq]
      exact isIrreducible_singleton.closure
    · rw [topologicalKrullDim_subscheme_eq]
      refine topologicalKrullDim_eq_one_of_ne_univ (le_of_eq hdY) E.support.isClosed
        (ne_univ_of_image_eq_singleton f hbf hdY hfE) (e := h c) (c := d) ?_ ?_ hcd hne
      · rw [hEsupp, hEeq]
        exact subset_closure rfl
      · rw [hEsupp, hEeq]
        exact specializes_iff_mem_closure.mp hcd
  refine ⟨E, ⟨hEc, x, hfE⟩, ?_⟩
  have hW := coe_inverseTransform_eq_closure h hbh hdY'
    (Z := E.support) (e := h c) (by rw [hEsupp, hEeq]) hhccl rfl
  have := hCc.1
  rw [inverseTransformIdeal, ← vanishingIdeal_support_eq_self C]
  congr 1
  exact Closeds.ext (hW.trans hc).symm

end Composite

section Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The source of a resolution is a normal scheme. -/
theorem IsSmoothResolution.isNormal {f : Y ⟶ X} (hf : IsSmoothResolution sX f) : IsNormal Y :=
  isNormal_of_isRegular Y (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hf.isSmoothScheme)

/-- The source of a resolution of an integral scheme is integral: it is normal, hence reduced,
and birational to the target, hence irreducible. -/
theorem IsSmoothResolution.isIntegral [IsIntegral X] {f : Y ⟶ X}
    (hf : IsSmoothResolution sX f) : IsIntegral Y := by
  have : IsNormal Y := hf.isNormal
  have : IsReduced Y := isReduced_of_isNormal Y
  obtain ⟨e, -⟩ := hf.isBirationalMorphism
  have : Nonempty e.target := e.dense_target.nonempty.to_subtype
  have : IsIntegral e.source.toScheme := IsIntegral.of_isIso e.iso.inv
  have hirr : IsIrreducible (e.source : Set Y) :=
    isIrreducible_iff_irreducibleSpace.mpr (inferInstanceAs (IrreducibleSpace e.source.toScheme))
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr (by
    rw [Set.top_eq_univ, ← e.dense_source.closure_eq]
    exact hirr.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- The source `Y` of a resolution `f : Y ⟶ X` of a normal variety is a normal variety of the
same dimension, and `f` is birational in the sense of [Stacks, Tag 01RO]. -/
theorem IsSmoothResolution.isNormalVariety (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    (hf : IsSmoothResolution sX f) :
    IsNormalVariety k (f ≫ sX) ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      IsBirational f := by
  have hXv := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsIntegral Y := hf.isIntegral
  have : IsProper f := hf.isProper
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : IsSeparated sX := hXv.toIsSeparated
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hvar : IsVariety k (f ≫ sX) := ⟨⟩
  have hbir := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf.isBirationalMorphism
  exact ⟨⟨hvar, hf.isNormal⟩, IsBirational.topologicalKrullDim_eq_of_isClosedMap hbir f.isClosedMap,
    hbir⟩

/-- **The exceptional locus of a resolution of a surface** (implicit in KM Notation 4.1). Let
`f : Y ⟶ X` be a resolution of a normal surface `X` over `k`. There is a finite set `S` of
closed points of `X` such that `f` restricts to an isomorphism `f⁻¹(X ∖ S) ⟶ X ∖ S`, the closed
subscheme `f⁻¹(S)` (reduced structure) is proper over `k`, and the `f`-exceptional curves are
exactly the one-dimensional irreducible components of `f⁻¹(S)`: a curve is `f`-exceptional if
and only if its support is an irreducible component of `f⁻¹(S)`, and a subset of `Y` is a
one-dimensional irreducible component of `f⁻¹(S)` if and only if it is the support of an
`f`-exceptional curve. -/
@[mmp "lem_km4a_resolution_exceptional_locus"]
theorem exists_finite_isIso_and_isExceptionalCurve_iff (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} (hf : IsSmoothResolution sX f) :
    ∃ S : Set X, S.Finite ∧ (∀ x ∈ S, IsClosed ({x} : Set X)) ∧
      (∃ hS : IsOpen Sᶜ, IsIso (f ∣_ ⟨Sᶜ, hS⟩)) ∧
      (∃ hT : IsClosed (f.base ⁻¹' S),
        IsProper ((Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' S, hT⟩).subschemeι ≫ f ≫ sX)) ∧
      (∀ C : Y.IdealSheafData, IsExceptionalCurve f C ↔
        IsCurveIn C ∧ Maximal (fun Z : Set Y ↦ IsIrreducible Z ∧ Z ⊆ f.base ⁻¹' S)
          (C.support : Set Y)) ∧
      ∀ W : Set Y, (Maximal (fun Z : Set Y ↦ IsIrreducible Z ∧ Z ⊆ f.base ⁻¹' S) W ∧
          topologicalKrullDim W = 1) ↔
        ∃ C : Y.IdealSheafData, IsExceptionalCurve f C ∧ (C.support : Set Y) = W := by
  obtain ⟨hYv, hdimY, hbir⟩ := hf.isNormalVariety hX
  have hXv := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsNormal X := hX.2
  have : IsIntegral Y := hf.isIntegral
  have : IsProper f := hf.isProper
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  have hdY : topologicalKrullDim Y ≤ 2 := by rw [hdimY, hdim]
  obtain ⟨hfin, hcl⟩ := finite_and_isClosed_singleton_compl_finiteFibreLocus f hbir hdY
  obtain ⟨hU, hiso⟩ := (isOpen_finiteFibreLocus_and_isIso f hbir).1 inferInstance
  refine ⟨(finiteFibreLocus f)ᶜ, hfin, hcl, ⟨by rwa [compl_compl], ?_⟩, ⟨?_, ?_⟩,
    isExceptionalCurve_iff_maximal f hbir hdY,
    maximal_and_topologicalKrullDim_eq_one_iff f hbir hdY⟩
  · have key : ∀ V : X.Opens, (V : Set X) = finiteFibreLocus f → IsIso (f ∣_ V) := by
      intro V hV
      obtain rfl : V = ⟨finiteFibreLocus f, hU⟩ := TopologicalSpace.Opens.ext hV
      exact hiso
    exact key _ (compl_compl _)
  · exact (isClosed_compl_finiteFibreLocus f hbir).preimage f.continuous
  · exact isProper_subschemeι_comp_of_finite sX f hfin hcl _

/-- **Exceptional curves of a composite resolution** (implicit in KM 4.5, 4.7). Let `f : Y ⟶ X`
be a resolution of a normal surface `X` over `k` and `h : Y' ⟶ Y` a proper birational morphism
from a smooth `k`-scheme `Y'` (a smooth surface). Then `h ≫ f` is a resolution of `X`, and its
exceptional curves are the birational transforms `h⁻¹_* E` of the `f`-exceptional curves `E`
together with the `h`-exceptional curves `F`: each `h⁻¹_* E` is an `(h ≫ f)`-exceptional curve
which is not `h`-exceptional, distinct `f`-exceptional curves have distinct transforms, and a
curve on `Y'` is `(h ≫ f)`-exceptional if and only if it is some `h⁻¹_* E` or `h`-exceptional. -/
@[mmp "lem_km4a_composite_exceptional_curves"]
theorem isSmoothResolution_comp_and_isExceptionalCurve_comp_iff (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} (hf : IsSmoothResolution sX f)
    {Y' : Scheme.{u}} {h : Y' ⟶ Y} (hh : IsSmoothResolution (f ≫ sX) h) :
    IsSmoothResolution sX (h ≫ f) ∧
      (∀ E : Y.IdealSheafData, IsExceptionalCurve f E →
        IsExceptionalCurve (h ≫ f) (inverseTransformIdeal h E.support) ∧
          ¬ IsExceptionalCurve h (inverseTransformIdeal h E.support)) ∧
      (∀ E E' : Y.IdealSheafData, IsExceptionalCurve f E → IsExceptionalCurve f E' →
        inverseTransformIdeal h E.support = inverseTransformIdeal h E'.support → E = E') ∧
      ∀ C : Y'.IdealSheafData, IsExceptionalCurve (h ≫ f) C ↔
        (∃ E : Y.IdealSheafData, IsExceptionalCurve f E ∧
          C = inverseTransformIdeal h E.support) ∨ IsExceptionalCurve h C := by
  obtain ⟨hYv, hdimY, hbf⟩ := hf.isNormalVariety hX
  obtain ⟨hY'v, hdimY', hbh⟩ := hh.isNormalVariety hYv
  have hXv := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsNormal X := hX.2
  have : IsIntegral Y := hf.isIntegral
  have : IsNormal Y := hf.isNormal
  have : IsIntegral Y' := hh.isIntegral
  have : IsProper f := hf.isProper
  have : IsProper h := hh.isProper
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : LocallyOfFiniteType (h ≫ f ≫ sX) := hY'v.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ f ≫ sX)
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (h ≫ f ≫ sX)
  have : IsNoetherian Y' := ⟨⟩
  have hdY : topologicalKrullDim Y = 2 := hdimY.trans hdim
  have hdY' : topologicalKrullDim Y' ≤ 2 := by rw [hdimY', hdY]
  have hres : IsSmoothResolution sX (h ≫ f) :=
    ⟨inferInstance, isBirationalMorphism_comp_of_isBirational f h hbf hbh,
      by rw [Category.assoc]; exact hh.isSmoothScheme⟩
  refine ⟨hres, fun E hE ↦ isExceptionalCurve_comp_inverseTransformIdeal f h hbh hdY hdY' hE,
    fun E E' hE hE' ↦ eq_of_inverseTransformIdeal_eq h hbh hdY hdY' hE.1 hE'.1, fun C ↦
      ⟨exists_eq_inverseTransformIdeal_or_isExceptionalCurve f h hbf hbh hdY hdY', ?_⟩⟩
  rintro (⟨E, hE, rfl⟩ | ⟨hCc, y, hy⟩)
  · exact (isExceptionalCurve_comp_inverseTransformIdeal f h hbh hdY hdY' hE).1
  · exact ⟨hCc, f y, by rw [image_base_comp, hy, Set.image_singleton]⟩

end Resolution

end MMP.Mori

