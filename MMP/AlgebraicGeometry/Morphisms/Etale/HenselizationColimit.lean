module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization

/-!
# The henselization as a colimit over affine pointed étale neighbourhoods

For a point `y` of a scheme `Y`, the henselization `𝒪_{Y,y}^h` is the filtered colimit of the
rings `𝒪(Y_e)` over the affine pointed étale neighbourhoods `(Y_e, y') ⟶ (Y, y)` with
`κ(y) ≅ κ(y')`.

## Main results

* `MMP.Resolution.Bridges.isFiltered_affineElementaryEtaleNeighborhood_and_isColimit`: the
  diagram of affine elementary étale neighbourhoods is filtered, and a henselization of
  `𝒪_{Y,y}` is the colimit of its global section rings, by a cocone over `𝒪_{Y,y}`.

## Implementation notes

* An elementary (pointed) étale neighbourhood is
  `AlgebraicGeometry.ElementaryEtaleNeighborhood S s`: an étale `V ⟶ S` with a point `v ↦ s` whose
  residue field map is an isomorphism. The affine ones form the full subcategory
  `MMP.Resolution.Bridges.AffineElementaryEtaleNeighborhood S s`.
* A henselization is `IsLocalRing.IsHenselization 𝒪_{S,s} κ(s) Rh`, and a leg
  `𝒪(V) ⟶ Rh` is over `𝒪_{S,s}` in the sense of `AlgebraicGeometry.IsOverStalk`: it factors
  through a local map `𝒪_{V,v} ⟶ Rh` over `𝒪_{S,s}`.
* The library result is `AlgebraicGeometry.isColimit_globalSections` (Stacks 05KS, 04HY), over all
  elementary étale neighbourhoods; the affine ones are cofinal.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace MMP.Resolution.Bridges

/-- The category of affine elementary étale neighbourhoods of a pointed scheme `(S, s)`. -/
abbrev AffineElementaryEtaleNeighborhood (S : Scheme.{u}) (s : S) :=
  ObjectProperty.FullSubcategory
    (fun U : ElementaryEtaleNeighborhood S s ↦ IsAffine U.obj.scheme)

/-- The diagram `(Y_e, y') ↦ 𝒪(Y_e)` of global section rings of the affine elementary étale
neighbourhoods. -/
noncomputable def affineGlobalSections (S : Scheme.{u}) (s : S) :
    (AffineElementaryEtaleNeighborhood S s)ᵒᵖ ⥤ CommRingCat.{u} :=
  (ObjectProperty.ι _).op ⋙ globalSections S s

private lemma exists_affine_elementary_hom {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    ∃ W : EtaleNeighborhood S s,
      W.IsElementary ∧ IsAffine W.scheme ∧ Nonempty (W ⟶ U) := by
  obtain ⟨O, hO, hu, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.scheme) (x := U.point)
      (U := ⊤) (by simp)
  let W : EtaleNeighborhood S s :=
    { scheme := O
      point := ⟨U.point, hu⟩
      toBase := O.ι ≫ U.toBase
      map_point := U.map_point }
  have hW : W.IsElementary := by
    change IsIso ((S.residueFieldCongr W.map_point).inv ≫
      W.toBase.residueFieldMap W.point)
    rw [Scheme.residueFieldMap_comp]
    change IsIso (((S.residueFieldCongr U.map_point).inv ≫
      U.toBase.residueFieldMap U.point) ≫ O.ι.residueFieldMap W.point)
    exact IsIso.comp_isIso' hU (inferInstance : IsIso (O.ι.residueFieldMap W.point))
  exact ⟨W, hW, hO, ⟨⟨O.ι, rfl, rfl⟩⟩⟩

/-- **The henselization from affine pointed étale neighbourhoods.** For a point `s` of a scheme
`S`, the affine elementary étale neighbourhoods of `(S, s)` form a filtered diagram, and a
henselization `Rh` of `𝒪_{S,s}` is the colimit of their global section rings, by a cocone whose
legs are over `𝒪_{S,s}`. -/
@[mmp "lem_mmp_foundation_henselization_pointed_etale_colimit"]
theorem isFiltered_affineElementaryEtaleNeighborhood_and_isColimit (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [IsLocalRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh] :
    IsFiltered (AffineElementaryEtaleNeighborhood S s)ᵒᵖ ∧
      ∃ ι : affineGlobalSections S s ⟶ (Functor.const _).obj (CommRingCat.of Rh),
        (∀ U : (AffineElementaryEtaleNeighborhood S s)ᵒᵖ,
          IsOverStalk S s Rh U.unop.obj (ι.app U).hom) ∧
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  let J : (AffineElementaryEtaleNeighborhood S s)ᵒᵖ ⥤ (ElementaryEtaleNeighborhood S s)ᵒᵖ :=
    (ObjectProperty.ι _).op
  have hex : ∀ X : (ElementaryEtaleNeighborhood S s)ᵒᵖ,
      ∃ Y : (AffineElementaryEtaleNeighborhood S s)ᵒᵖ, Nonempty (X ⟶ J.obj Y) := by
    intro X
    obtain ⟨W, hW, hA, ⟨f⟩⟩ := exists_affine_elementary_hom X.unop.obj X.unop.property
    exact ⟨op ⟨⟨W, hW⟩, hA⟩, ⟨(show (⟨W, hW⟩ : ElementaryEtaleNeighborhood S s) ⟶ X.unop from
      ⟨f⟩).op⟩⟩
  have : J.Final := Functor.final_of_exists_of_isFiltered_of_fullyFaithful J hex
  obtain ⟨ι, -, hover, -, ⟨hc⟩⟩ := isColimit_globalSections S s Rh
  exact ⟨IsFiltered.of_exists_of_isFiltered_of_fullyFaithful J hex, Functor.whiskerLeft J ι,
    fun U => hover (J.obj U), ⟨(Functor.Final.isColimitWhiskerEquiv J (Cocone.mk _ ι)).symm hc⟩⟩

end MMP.Resolution.Bridges
