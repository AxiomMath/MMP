module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Rational maps, birational maps and the exceptional set

Let `X` and `Y` be schemes. A *rational map* `f : X ⤏ Y` is an equivalence class of pairs
`(U, f_U)` with `U ⊆ X` a dense open subset and `f_U : U ⟶ Y` a morphism, two pairs being
equivalent when they agree on a dense open subset of `X` contained in both domains. Its
*domain of definition* is the union of the domains of all representatives. A rational map is
*birational* if some representative is an isomorphism of its domain onto a dense open
subscheme of `Y`, and a rational map `h : Y ⤏ X` is *an inverse* of `f` if it is represented
by the inverse of such a representative.

For a morphism `f : X ⟶ Y`, an open `V ⊆ Y` is *`f`-biregular* if `f ∣_ V : f⁻¹(V) ⟶ V` is an
isomorphism. The *exceptional set* of `f` is the complement of the preimage of the union of
all `f`-biregular opens.

## Main definitions

* `MMP.Mori.RationalMap`: rational maps, Mathlib's `AlgebraicGeometry.Scheme.RationalMap`.
* `MMP.Mori.RationalMap.IsMorphism`: a rational map is a morphism.
* `MMP.Mori.RationalMap.dom`, `MMP.Mori.RationalMap.DefinedAt`: the domain of definition.
* `MMP.Mori.RationalMap.IsBirational`, `MMP.Mori.IsBirationalMorphism`: birational maps and
  birational morphisms.
* `MMP.Mori.RationalMap.IsInverse`: `h` is an inverse of the birational map `f`.
* `MMP.Mori.IsBiregular`, `MMP.Mori.biregularLocus`, `MMP.Mori.exceptionalSet`: the
  exceptional set `Ex(f)` of a morphism.

## Main results

* `MMP.Mori.RationalMap.IsInverse.symm`: if `h` is an inverse of `f` then `f` is an inverse
  of `h`; in particular an inverse of a birational map is birational.
* `MMP.Mori.RationalMap.IsBirational.exists_isInverse`: a birational map has an inverse.
* `MMP.Mori.isBiregular_biregularLocus`: the union of all `f`-biregular opens is
  `f`-biregular.

## Implementation notes

The equivalence relation on representatives in Mathlib asks the two morphisms to agree on a
dense open subset of `X` contained in both domains; this is the same as agreeing on a dense
open subset of the intersection of the domains, since that intersection is itself dense open.

The exceptional set is recorded as a closed subset of `X`. Its reduced closed subscheme
structure is determined by the closed subset.

Uniqueness of the inverse of a birational map needs no hypotheses on `X`: it is
`MMP.Positivity.IsBirational.existsUnique_isInverse`.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Notation 0.4.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

variable {X Y : Scheme.{u}}

/-- A *rational map* `X ⤏ Y` between schemes: an equivalence class of morphisms `U ⟶ Y`
defined on dense open subsets `U ⊆ X`, two being equivalent when they agree on a dense open
subset of both domains. This is Mathlib's `AlgebraicGeometry.Scheme.RationalMap`. -/
abbrev RationalMap (X Y : Scheme.{u}) : Type u := Scheme.RationalMap X Y

namespace RationalMap

/-- A rational map *is a morphism* if it is the class of a morphism defined on all of `X`. -/
@[mmp "def_km0_rational_map"]
def IsMorphism (f : RationalMap X Y) : Prop :=
  ∃ g : X ⟶ Y, g.toRationalMap = f

/-- The rational map of a morphism is a morphism. -/
lemma isMorphism_toRationalMap (g : X ⟶ Y) : IsMorphism (X := X) g.toRationalMap :=
  ⟨g, rfl⟩

/-- The *domain of definition* of a rational map: the union of the domains of all its
representatives. -/
abbrev dom (f : RationalMap X Y) : X.Opens := Scheme.RationalMap.domain f

/-- A rational map is *defined at* `x` if `x` lies in its domain of definition. -/
abbrev DefinedAt (f : RationalMap X Y) (x : X) : Prop := x ∈ dom f

/-- A rational map is defined at `x` if and only if it has a representative whose domain
contains `x`. -/
lemma definedAt_iff {f : RationalMap X Y} {x : X} :
    DefinedAt f x ↔ ∃ g : X.PartialMap Y, x ∈ g.domain ∧ g.toRationalMap = f :=
  Scheme.RationalMap.mem_domain

/-- The domain of definition of a rational map is dense. -/
lemma dense_dom (f : RationalMap X Y) : Dense (dom f : Set X) :=
  Scheme.RationalMap.dense_domain f

/-- The domain of a partial map is contained in the domain of definition of its rational
map. -/
lemma le_dom (g : X.PartialMap Y) : g.domain ≤ dom (X := X) g.toRationalMap :=
  g.le_domain_toRationalMap

/-- The rational map of a morphism `X ⟶ Y` is defined on all of `X`. -/
lemma dom_toRationalMap_hom (g : X ⟶ Y) : dom (X := X) g.toRationalMap = ⊤ :=
  top_le_iff.mp (le_dom g.toPartialMap)

/-- A rational map is *birational* if it has a representative which is an isomorphism of its
(dense open) domain onto a dense open subscheme of `Y`. -/
@[mmp "def_km0_birational_map"]
def IsBirational (f : RationalMap X Y) : Prop :=
  ∃ e : X.PartialIso Y, e.toRationalMap = f

/-- The rational map of a partial isomorphism is birational. -/
lemma isBirational_toRationalMap (e : X.PartialIso Y) :
    IsBirational (X := X) e.toRationalMap :=
  ⟨e, rfl⟩

/-- The identity rational map of `X` is birational. -/
lemma isBirational_id : IsBirational (Scheme.RationalMap.id X) :=
  ⟨Scheme.PartialIso.refl X, by
    rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    exact ⟨⊤, dense_univ, le_rfl, le_rfl, by
      simp [Scheme.PartialMap.restrict, Scheme.PartialMap.id]
      rfl⟩⟩

/-- If there is a birational map `X ⤏ Y`, then `X` and `Y` are birational. -/
lemma IsBirational.birational {f : RationalMap X Y} (hf : IsBirational f) :
    Scheme.Birational X Y :=
  ⟨hf.choose⟩

/-- A rational map `h : Y ⤏ X` is *an inverse* of `f : X ⤏ Y` if there is a representative of
`f` which is an isomorphism of its domain onto a dense open `V ⊆ Y` whose inverse `V ⟶ X`
represents `h`. -/
@[mmp "def_km0_inverse_birational_map"]
def IsInverse (f : RationalMap X Y) (h : RationalMap Y X) : Prop :=
  ∃ e : X.PartialIso Y, e.toRationalMap = f ∧ e.symm.toRationalMap = h

namespace IsInverse

variable {f : RationalMap X Y} {h : RationalMap Y X}

/-- A rational map with an inverse is birational. -/
lemma isBirational (H : IsInverse f h) : IsBirational f :=
  let ⟨e, he, _⟩ := H; ⟨e, he⟩

/-- If `h` is an inverse of `f`, then `f` is an inverse of `h`. -/
lemma symm (H : IsInverse f h) : IsInverse h f :=
  let ⟨e, he, he'⟩ := H; ⟨e.symm, he', he⟩

/-- An inverse of a rational map is birational. -/
lemma isBirational_inverse (H : IsInverse f h) : IsBirational h :=
  H.symm.isBirational

end IsInverse

/-- `h` is an inverse of `f` if and only if `f` is an inverse of `h`. -/
lemma isInverse_comm {f : RationalMap X Y} {h : RationalMap Y X} :
    IsInverse f h ↔ IsInverse h f :=
  ⟨IsInverse.symm, IsInverse.symm⟩

/-- The rational map of the inverse of a partial isomorphism `e` is an inverse of the rational
map of `e`. -/
lemma isInverse_toRationalMap (e : X.PartialIso Y) :
    IsInverse (X := X) e.toRationalMap e.symm.toRationalMap :=
  ⟨e, rfl, rfl⟩

/-- A birational map has an inverse. -/
lemma IsBirational.exists_isInverse {f : RationalMap X Y} (hf : IsBirational f) :
    ∃ h : RationalMap Y X, IsInverse f h :=
  let ⟨e, he⟩ := hf; ⟨e.symm.toRationalMap, e, he, rfl⟩

/-- A rational map is birational if and only if it has an inverse. -/
lemma isBirational_iff_exists_isInverse {f : RationalMap X Y} :
    IsBirational f ↔ ∃ h : RationalMap Y X, IsInverse f h :=
  ⟨IsBirational.exists_isInverse, fun ⟨_, H⟩ ↦ H.isBirational⟩

/-- A chosen inverse of a birational map. -/
noncomputable def IsBirational.inverse {f : RationalMap X Y} (hf : IsBirational f) :
    RationalMap Y X :=
  hf.exists_isInverse.choose

/-- The chosen inverse `hf.inverse` is an inverse of `f`. -/
lemma IsBirational.isInverse_inverse {f : RationalMap X Y} (hf : IsBirational f) :
    IsInverse f hf.inverse :=
  hf.exists_isInverse.choose_spec

/-- The chosen inverse of a birational map is birational. -/
lemma IsBirational.isBirational_inverse {f : RationalMap X Y} (hf : IsBirational f) :
    IsBirational hf.inverse :=
  hf.isInverse_inverse.isBirational_inverse

/-- A birational map `f` is an inverse of its chosen inverse `hf.inverse`. -/
lemma IsBirational.isInverse_inverse_symm {f : RationalMap X Y} (hf : IsBirational f) :
    IsInverse hf.inverse f :=
  hf.isInverse_inverse.symm

end RationalMap

/-- A *birational morphism* is a morphism whose rational map is birational. -/
@[mmp "def_km0_birational_map"]
def IsBirationalMorphism (f : X ⟶ Y) : Prop :=
  RationalMap.IsBirational (X := X) f.toRationalMap

/-- An isomorphism is a birational morphism. -/
lemma isBirationalMorphism_of_isIso (f : X ⟶ Y) [IsIso f] : IsBirationalMorphism f := by
  refine ⟨Scheme.PartialIso.ofIso (asIso f), ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨⊤, dense_univ, le_rfl, le_rfl, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.PartialIso.ofIso, Iso.trans_hom, asIso_hom,
    Iso.symm_hom, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  rfl

/-- An open `V ⊆ Y` is *`f`-biregular* if `f` restricts to an isomorphism `f⁻¹(V) ⟶ V`. -/
@[mmp "def_km0_exceptional_set"]
def IsBiregular (f : X ⟶ Y) (V : Y.Opens) : Prop := IsIso (f ∣_ V)

/-- The union `V_f` of all `f`-biregular opens of `Y`. -/
@[mmp "def_km0_exceptional_set"]
def biregularLocus (f : X ⟶ Y) : Y.Opens := sSup {V | IsBiregular f V}

/-- The *exceptional set* `Ex(f) = X ∖ f⁻¹(V_f)` of a morphism `f : X ⟶ Y`, where `V_f` is the
union of all `f`-biregular opens of `Y`. -/
@[mmp "def_km0_exceptional_set"]
def exceptionalSet (f : X ⟶ Y) : TopologicalSpace.Closeds X :=
  (f ⁻¹ᵁ biregularLocus f).compl

/-- Every `f`-biregular open is contained in the union of all `f`-biregular opens. -/
lemma le_biregularLocus {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V) :
    V ≤ biregularLocus f :=
  le_sSup hV

/-- A point `x` lies in `Ex(f)` if and only if `f x` lies outside the union of all
`f`-biregular opens. -/
lemma mem_exceptionalSet {f : X ⟶ Y} {x : X} :
    x ∈ exceptionalSet f ↔ f x ∉ biregularLocus f :=
  Iff.rfl

/-- The exceptional set of a morphism is closed. -/
lemma isClosed_exceptionalSet (f : X ⟶ Y) : IsClosed (exceptionalSet f : Set X) :=
  (exceptionalSet f).isClosed

/-- The whole of `Y` is `f`-biregular if and only if `f` is an isomorphism. -/
lemma isBiregular_top_iff (f : X ⟶ Y) : IsBiregular f ⊤ ↔ IsIso f := by
  simpa [IsBiregular] using (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (f := f) (fun _ : Unit ↦ ⊤) (by simp)).symm

/-- The union of all `f`-biregular opens is `f`-biregular. -/
lemma isBiregular_biregularLocus (f : X ⟶ Y) : IsBiregular f (biregularLocus f) := by
  set W := biregularLocus f
  let U : {V : Y.Opens // IsBiregular f V} → W.toScheme.Opens := fun V ↦ W.ι ⁻¹ᵁ V.1
  have hU : iSup U = ⊤ := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨V, hV, hx⟩ := TopologicalSpace.Opens.mem_sSup.mp x.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  change MorphismProperty.isomorphisms Scheme (f ∣_ W)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun V ↦ ?_
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f W (U V) ≪≫ morphismRestrictEq f ?_)).mpr V.2
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
  exact le_biregularLocus V.2

/-- An open `V ⊆ Y` is `f`-biregular if and only if it is contained in the union of all
`f`-biregular opens. -/
lemma isBiregular_iff_le_biregularLocus {f : X ⟶ Y} {V : Y.Opens} :
    IsBiregular f V ↔ V ≤ biregularLocus f := by
  refine ⟨le_biregularLocus, fun hV ↦ ?_⟩
  have e := morphismRestrictRestrict f (biregularLocus f) ((biregularLocus f).ι ⁻¹ᵁ V)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hV] at e
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mp
    (IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (isBiregular_biregularLocus f) _)

/-- A surjective morphism has empty exceptional set if and only if it is an isomorphism. -/
lemma exceptionalSet_eq_bot_iff (f : X ⟶ Y) [Surjective f] :
    exceptionalSet f = ⊥ ↔ IsIso f := by
  rw [← isBiregular_top_iff, isBiregular_iff_le_biregularLocus, top_le_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    simpa using not_not.mp fun hx ↦ (h ▸ hx : x ∈ ((⊥ : TopologicalSpace.Closeds X) : Set X))
  · ext x
    simp [exceptionalSet, h]

end MMP.Mori
