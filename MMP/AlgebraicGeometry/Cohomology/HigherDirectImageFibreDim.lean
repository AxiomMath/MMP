module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Basic
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Singularities.SNCGluing
import MMP.AlgebraicGeometry.MMP.Threefold.Basic
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity

/-!
# Higher direct images above the fibre dimension, and curves through two points

This file collects two foundational facts used throughout the minimal model program.

Let `f : X ⟶ Y` be a proper morphism of schemes, `y ∈ Y`, and `ℱ` a
coherent sheaf on an open neighbourhood `U` of the fibre `f⁻¹(y)`. If `r` is the dimension of
the fibre `X_y`, then the higher direct images `R^i f_* ℱ` vanish on a neighbourhood of `y` for
every `i > r`. The open `W = Y ∖ f(X ∖ U)` contains `y` and satisfies `f⁻¹(W) ⊆ U`, so over `W`
the morphism `U → Y` restricts to a proper morphism whose fibres embed in those of `f`. The
fibre dimension of `f` is bounded by `dim X_y` on a neighbourhood of `y` ([Stacks, Tag 02FZ]);
at every point of that neighbourhood the stalks of the higher direct images vanish above
`dim X_y` ([Stacks, Tag 0E7D]), and higher direct images commute with restriction to opens
([Stacks, Tag 01E5]).

Let `X` be a variety over a field `k` (in the sense of `MMP.Mori.IsVariety`: integral,
separated and of finite type over `k`; the field is arbitrary) with `dim X ≥ 1`. Any two
closed points `x`, `y` of `X`, possibly equal, lie on a curve `C ⊆ X`.

## Main results

* `MMP.Foundations.exists_isZero_restrict_rightDerived_pushforward_of_topologicalKrullDim_lt`:
  `R^i f_* ℱ` vanishes near `y` for `i > dim X_y`.
* `MMP.Mori.exists_isClosedImmersion_isCurve_of_mem_closedPoints`: a curve through two
  closed points.

## Implementation notes

The higher direct image `R^i f_* ℱ` of a sheaf `ℱ` on the open `U ⊆ X` is the `i`-th right
derived functor of `Scheme.Modules.pushforward (U.ι ≫ f)` applied to `ℱ`, and its restriction to
an open `V ⊆ Y` is `Scheme.Modules.restrictFunctor V.ι`. The fibre dimension is the topological
Krull dimension of `f.fiber y`, valued in `WithBot ℕ∞`; an empty fibre has dimension `⊥`, and
then every `R^i f_* ℱ`, including `i = 0`, vanishes near `y`, since `y` has a neighbourhood with
empty preimage in `U`.

A curve `C ⊆ X` is recorded as a closed immersion `i : C ⟶ X` such that `i ≫ f` satisfies
`MMP.Mori.IsCurve` (a variety of dimension one). `dim X ≥ 1` is written as
`1 ≤ topologicalKrullDim X`, and a closed point is an element of `closedPoints X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §1
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MMP.Foundations

private theorem isIso_morphismRestrict_ι_of_preimage_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : X.Opens) (W : Y.Opens) (hle : f ⁻¹ᵁ W ≤ V) : IsIso (V.ι ∣_ (f ⁻¹ᵁ W)) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  refine ⟨⟨⟨x.1, hle x.2⟩, x.2⟩, ?_⟩
  exact Subtype.ext
    (congrArg (fun h => h ⟨⟨x.1, hle x.2⟩, x.2⟩) (morphismRestrict_ι V.ι (f ⁻¹ᵁ W)))

private theorem isProper_morphismRestrict_comp_ι_of_preimage_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (V : X.Opens) (W : Y.Opens) (hle : f ⁻¹ᵁ W ≤ V) : IsProper ((V.ι ≫ f) ∣_ W) := by
  rw [morphismRestrict_comp]
  have := isIso_morphismRestrict_ι_of_preimage_le f V W hle
  exact MorphismProperty.RespectsIso.precomp (@IsProper) (V.ι ∣_ (f ⁻¹ᵁ W)) _
    (inferInstance : IsProper (f ∣_ W))

/-- Isomorphic sheaves of modules have isomorphic stalks, so one vanishes when the other does. -/
private theorem isZero_stalk_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) (y : Y)
    (h : IsZero (N.presheaf.stalk y)) : IsZero (M.presheaf.stalk y) :=
  (show IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} y).obj
      ((Scheme.Modules.toPresheaf Y).obj N)) from h).of_iso
    ((TopCat.Presheaf.stalkFunctor Ab.{u} y).mapIso ((Scheme.Modules.toPresheaf Y).mapIso e))

attribute [local instance 10000] HasDerivedCategory.standard in
open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E7D]**, in the indexing by `ℕ`: for proper `f` whose fibre over `y` has
dimension at most `d`, the stalk at `y` of `R^i f_* ℱ` vanishes for quasi-coherent `ℱ` and
every `i > d`. -/
private theorem isZero_stalk_rightDerived_of_topologicalKrullDim_fiber_le {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hd : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) (F : X.Modules)
    [F.IsQuasicoherent] (i : ℕ) (hi : d < i) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerived i).obj F).presheaf.stalk y) :=
  isZero_stalk_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i).app F) y
    (isZero_stalk_rightDerivedPlus_of_cohomology_vanishing f y d hd
      (cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le d) F i (by exact_mod_cast hi))

/-- The stalk at `y ∈ W` of `R^i g_* T` vanishes if the stalk at `y` of the higher direct image
along `g ∣_ W` of the restriction of `T` does. -/
private theorem isZero_stalk_rightDerived_of_restrict {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (y : Y) (hy : y ∈ W) (i : ℕ) (T : X.Modules)
    (h : IsZero ((((Scheme.Modules.pushforward (g ∣_ W)).rightDerived i).obj
      ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).obj T)).presheaf.stalk
      (⟨y, hy⟩ : W.toScheme))) :
    IsZero ((((Scheme.Modules.pushforward g).rightDerived i).obj T).presheaf.stalk y) := by
  set A := ((Scheme.Modules.pushforward g).rightDerived i).obj T
  have h1 : IsZero (((Scheme.Modules.restrictFunctor W.ι).obj A).presheaf.stalk
      (⟨y, hy⟩ : W.toScheme)) := isZero_stalk_of_iso
    ((AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme g W i).app
      T).symm _ h
  exact (show IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} (⟨y, hy⟩ : W.toScheme)).obj
      ((Scheme.Modules.toPresheaf W.toScheme).obj
        ((Scheme.Modules.restrictFunctor W.ι).obj A))) from h1).of_iso
    ((Scheme.Modules.restrictStalkNatIso W.ι ⟨y, hy⟩).app A).symm

/-- A sheaf of modules restricts to zero on an open `V` once its stalks at the points of `V`
vanish. -/
private theorem isZero_restrict_of_forall_isZero_stalk {Y : Scheme.{u}} (V : Y.Opens)
    (M : Y.Modules) (h : ∀ y ∈ V, IsZero (M.presheaf.stalk y)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M) := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun x => ?_
  have h1 : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} (V.ι x)).obj
      ((Scheme.Modules.toPresheaf Y).obj M)) := h _ x.2
  exact h1.of_iso ((Scheme.Modules.restrictStalkNatIso V.ι x).app M)

/-- The fibres of `(U.ι ≫ f) ∣_ W` have dimension at most that of the fibres of `f`. -/
private theorem topologicalKrullDim_fiber_morphismRestrict_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (W : Y.Opens) (z : W.toScheme) :
    topologicalKrullDim (((U.ι ≫ f) ∣_ W).fiber z) ≤ topologicalKrullDim (f.fiber (W.ι z)) := by
  set g' := (U.ι ≫ f) ∣_ W
  let e : (U.ι ≫ f) ⁻¹ᵁ W → X := fun x => U.ι ((((U.ι ≫ f) ⁻¹ᵁ W).ι) x)
  have he : Topology.IsInducing e :=
    (U.ι.isOpenEmbedding.isEmbedding.comp
      ((U.ι ≫ f) ⁻¹ᵁ W).ι.isOpenEmbedding.isEmbedding).isInducing
  have hfe : ∀ x, g' x = z → f (e x) = W.ι z := by
    rintro x rfl
    have h2 := congrArg (fun h => h x) (morphismRestrict_ι (U.ι ≫ f) W)
    simp only [Scheme.Hom.comp_apply] at h2
    exact h2.symm
  let h : (g' ⁻¹' {z}) → (f ⁻¹' {W.ι z}) := fun x => ⟨e x.1, hfe x.1 x.2⟩
  have hind : Topology.IsInducing h := .of_comp
    ((he.continuous.comp continuous_subtype_val).subtype_mk _) continuous_subtype_val
    (he.comp .subtypeVal)
  calc topologicalKrullDim (g'.fiber z)
      ≤ topologicalKrullDim (g' ⁻¹' {z}) := (g'.fiberHomeo z).isInducing.topologicalKrullDim_le
    _ ≤ topologicalKrullDim (f ⁻¹' {W.ι z}) := hind.topologicalKrullDim_le
    _ ≤ topologicalKrullDim (f.fiber (W.ι z)) :=
      (f.fiberHomeo (W.ι z)).symm.isInducing.topologicalKrullDim_le

/-- Over the complement of the image of the complement of `U`, the preimage under a universally
closed `f` lies in `U`; this open contains every `y` whose fibre lies in `U`. -/
private theorem exists_opens_mem_and_preimage_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] (y : Y) (U : X.Opens) (hU : ∀ x : X, f x = y → x ∈ U) :
    ∃ W : Y.Opens, y ∈ W ∧ f ⁻¹ᵁ W ≤ U := by
  refine ⟨⟨(f '' (U : Set X)ᶜ)ᶜ, (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩, ?_,
    fun x hx => by_contra fun h => hx ⟨x, h, rfl⟩⟩
  change y ∉ f '' _
  rintro ⟨x, hx, rfl⟩
  exact hx (hU x rfl)

/-- If the fibre of a universally closed `f` over `y` is empty, every higher direct image along
`U.ι ≫ f` vanishes on a neighbourhood of `y`. -/
private theorem exists_isZero_restrict_rightDerived_of_topologicalKrullDim_fiber_eq_bot
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f] (y : Y)
    (hbot : topologicalKrullDim (f.fiber y) = ⊥) (U : X.Opens) (F : U.toScheme.Modules) :
    ∃ V : Y.Opens, y ∈ V ∧ ∀ i : ℕ, IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (((Scheme.Modules.pushforward (U.ι ≫ f)).rightDerived i).obj F)) := by
  have hny : y ∉ Set.range f := by
    rintro ⟨x, rfl⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot_iff] at hbot
    exact hbot.false ⟨closure {(f.fiberHomeo (f x)).symm ⟨x, rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩
  let V : Y.Opens := ⟨(Set.range f)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  refine ⟨V, hny, fun i => ?_⟩
  have hz : IsZero ((Scheme.Modules.restrictFunctor ((U.ι ≫ f) ⁻¹ᵁ V).ι).obj F) :=
    AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun x => (x.2 ⟨U.ι x.1, rfl⟩).elim
  exact (Functor.map_isZero ((Scheme.Modules.pushforward ((U.ι ≫ f) ∣_ V)).rightDerived i)
    hz).of_iso ((AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme
      (U.ι ≫ f) V i).app F).symm

/-- **Higher direct images vanish above the fibre dimension.** Let `f : X ⟶ Y` be proper,
`y ∈ Y`, and `ℱ` a coherent sheaf on an open `U ⊆ X` containing the
fibre `f⁻¹(y)`. Then there is an open neighbourhood `V` of `y` such that
`(R^i f_* ℱ)|_V = 0` for every `i` exceeding the dimension of the fibre `X_y`. -/
@[mmp "lem_mmp_foundation_higher_direct_images_vanish_above_fibre_dimension"]
public theorem exists_isZero_restrict_rightDerived_pushforward_of_topologicalKrullDim_lt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y)
    (U : X.Opens) (hU : ∀ x : X, f x = y → x ∈ U) (F : U.toScheme.Modules) [F.IsCoherent] :
    ∃ V : Y.Opens, y ∈ V ∧ ∀ i : ℕ, topologicalKrullDim (f.fiber y) < i →
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
        (((Scheme.Modules.pushforward (U.ι ≫ f)).rightDerived i).obj F)) := by
  obtain ⟨W, hyW, hle⟩ := exists_opens_mem_and_preimage_le f y U hU
  set g := U.ι ≫ f
  have : IsProper (g ∣_ W) := isProper_morphismRestrict_comp_ι_of_preimage_le f U W hle
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have hstalk : ∀ y' (hy' : y' ∈ W) (d : ℕ),
      topologicalKrullDim (f.fiber y') ≤ (d : WithBot ℕ∞) → ∀ i : ℕ, d < i →
      IsZero ((((Scheme.Modules.pushforward g).rightDerived i).obj F).presheaf.stalk y') :=
    fun y' hy' d hd i hi => isZero_stalk_rightDerived_of_restrict g W y' hy' i F
      (isZero_stalk_rightDerived_of_topologicalKrullDim_fiber_le (g ∣_ W) ⟨y', hy'⟩ d
        ((topologicalKrullDim_fiber_morphismRestrict_le f U W _).trans hd) _ i hi)
  by_cases hbot : topologicalKrullDim (f.fiber y) = ⊥
  · obtain ⟨V, hyV, hV⟩ :=
      exists_isZero_restrict_rightDerived_of_topologicalKrullDim_fiber_eq_bot f y hbot U F
    exact ⟨V, hyV, fun i _ => hV i⟩
  · obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
    cases m using ENat.recTopCoe with
    | top =>
      refine ⟨⊤, trivial, fun i hi => ?_⟩
      rw [← hm] at hi
      exact (not_top_lt (by exact_mod_cast hi : (⊤ : ℕ∞) < i)).elim
    | coe d =>
      obtain ⟨W1, hyW1, -, -, -, -, -, hW1⟩ :=
        Stacks.AlgebraicGeometry.ProperFibreDimension.exists_affineOpen_fiberDimension_le f y d
          (by rw [← hm]; rfl)
      refine ⟨W ⊓ W1, ⟨hyW, hyW1⟩, fun i hi => ?_⟩
      rw [← hm] at hi
      exact isZero_restrict_of_forall_isZero_stalk _ _ fun y' hy' =>
        hstalk y' hy'.1 d (hW1 y' hy'.2) i (by exact_mod_cast hi)

end MMP.Foundations

namespace MMP.Mori

/-- On a variety `X` over a field `k` with `dim X ≥ 1`, any two closed points `x` and `y`
(possibly equal) lie on a curve: there is a closed immersion `i : C ⟶ X` such that `C` is a
curve over `k` via `i ≫ f` and `x`, `y` lie in the range of `i`. -/
@[mmp "lem_mmp_foundation_km1b_curve_two_points"]
public theorem exists_isClosedImmersion_isCurve_of_mem_closedPoints
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f]
    (hdim : 1 ≤ topologicalKrullDim X) {x y : X}
    (hx : x ∈ closedPoints X) (hy : y ∈ closedPoints X) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X),
      IsClosedImmersion i ∧ IsCurve k (i ≫ f) ∧ x ∈ Set.range i ∧ y ∈ Set.range i := by
  obtain ⟨C, i, hi, hC, hxi, hyi, -⟩ :=
    MMP.exists_isClosedImmersion_isCurve_and_isProper_of_isClosed_singleton f
      (zero_lt_one.trans_le hdim) hx hy
  exact ⟨C, i, hi, hC, hxi, hyi⟩

end MMP.Mori
