module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Variety.Basic

/-!
# The closure of the image of a subvariety

For a morphism `f : X ⟶ Y` and a subvariety `V` of `X`, the image subvariety
`W = \overline{f(V)}` (`MMP.Intersection.Scheme.Subvariety.image`, Fulton B.2.2) receives a
dominant morphism `V ⟶ W` through which `f|_V` factors, and it is the only subvariety of `Y` with
this property.

## Implementation notes

A subvariety is `MMP.Intersection.Scheme.Subvariety`, an integral closed subscheme given by its
ideal sheaf; `f|_V` is `V.ideal.subschemeι ≫ f`, and "factors through `W`" means
`g ≫ W.ideal.subschemeι = V.ideal.subschemeι ≫ f`. Dominance is Mathlib's `IsDominant`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution.Bridges

open MMP.Intersection.Scheme (Subvariety)

/-- The ideal sheaf of a reduced closed subscheme is the vanishing ideal of its support. -/
private lemma vanishingIdeal_support_eq_of_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : Scheme.IdealSheafData.vanishingIdeal I.support = I := by
  have h := Scheme.IdealSheafData.map_vanishingIdeal I.subschemeι ⊤
  rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at h
  rw [h]
  congr 1

private lemma isDominant_iff_support_eq_closure_image {X Y : Scheme.{u}} {f : X ⟶ Y}
    {V : Subvariety X} {W : Subvariety Y} {g : V.ideal.subscheme ⟶ W.ideal.subscheme}
    (h : g ≫ W.ideal.subschemeι = V.ideal.subschemeι ≫ f) :
    IsDominant g ↔ (W.ideal.support : Set Y) = closure (f '' V.support) := by
  have hr : Set.range (W.ideal.subschemeι ∘ g) = f '' V.support := by
    have : (W.ideal.subschemeι ∘ g) = f ∘ V.ideal.subschemeι := by
      funext x
      simpa [Scheme.Hom.comp_apply] using
        congrArg (fun k : V.ideal.subscheme ⟶ Y => k x) h
    rw [this, Set.range_comp, V.ideal.range_subschemeι]
    rfl
  have hcl : closure (Set.range g) = W.ideal.subschemeι ⁻¹' closure (f '' V.support) := by
    rw [W.ideal.subschemeι.isEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp, hr]
  have hsub : closure (f '' V.support) ⊆ (W.ideal.support : Set Y) :=
    hr ▸ closure_minimal ((Set.range_comp_subset_range _ _).trans
      W.ideal.range_subschemeι.subset) W.ideal.support.isClosed
  refine ⟨fun hd => hsub.antisymm' fun y hy => ?_, fun hd => ⟨?_⟩⟩
  · rw [← W.ideal.range_subschemeι] at hy
    obtain ⟨x, rfl⟩ := hy
    have hx : x ∈ closure (Set.range g) := by simp [hd.1.closure_range]
    rwa [hcl] at hx
  · rw [DenseRange, dense_iff_closure_eq, hcl, ← hd, Set.eq_univ_iff_forall]
    exact fun x => W.ideal.range_subschemeι.subset ⟨x, rfl⟩

/-- **The closure of the image of a subvariety.** Let `f : X ⟶ Y` be a morphism of schemes and
`V` a subvariety of `X`. Then `W = \overline{f(V)}` is a subvariety of `Y` (by construction of
`V.image f`), `f|_V` factors through a dominant morphism `V ⟶ W`, and `W` is the only subvariety
of `Y` through which `f|_V` factors by a dominant morphism. -/
@[mmp "lem_mmp_foundation_image_subvariety"]
theorem subvariety_image_factorization {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Subvariety X) :
    (∃ g : V.ideal.subscheme ⟶ (V.image f).ideal.subscheme,
        g ≫ (V.image f).ideal.subschemeι = V.ideal.subschemeι ≫ f ∧ IsDominant g) ∧
      ∀ (W : Subvariety Y) (g : V.ideal.subscheme ⟶ W.ideal.subscheme),
        g ≫ W.ideal.subschemeι = V.ideal.subschemeι ≫ f → IsDominant g → W = V.image f := by
  have hV : Scheme.IdealSheafData.vanishingIdeal V.ideal.support = V.ideal := by
    have := V.isIntegral
    exact vanishingIdeal_support_eq_of_isReduced V.ideal
  have hle : (V.image f).ideal ≤ V.ideal.map f := by
    have := Scheme.IdealSheafData.map_vanishingIdeal f V.ideal.support
    rw [hV] at this
    exact this.symm.le
  have hfac := Scheme.IdealSheafData.subschemeMap_subschemeι V.ideal (V.image f).ideal f hle
  refine ⟨⟨_, hfac, ?_⟩, fun W g hg hd => ?_⟩
  · rw [isDominant_iff_support_eq_closure_image hfac]
    rfl
  have hs := (isDominant_iff_support_eq_closure_image hg).1 hd
  have := W.isIntegral
  have : W.ideal = (V.image f).ideal := by
    rw [← vanishingIdeal_support_eq_of_isReduced W.ideal]
    exact congrArg _ (SetLike.coe_injective hs)
  cases W
  exact (Subvariety.mk.injEq _ _ _ _).mpr this

end MMP.Resolution.Bridges
