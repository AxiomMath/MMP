module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Dimension under a flat morphism of relative dimension `r`

Let `p : P ⟶ Z` be a flat morphism locally of finite type of relative dimension `r` (Stacks 02NJ:
every nonempty fibre is equidimensional of dimension `r`) between irreducible schemes, with `Z`
locally of finite type over a field. Then `dim P = dim Z + r`: the generic point `ξ` of `P` lies
over the generic point of `Z` (flatness), its residue field has transcendence degree `r` over
that of the generic point of `Z`, and the dimension of an integral scheme locally of finite type
over a field is the delta-dimension of its generic point (Stacks 02JP).

For a closed subscheme `I` of `Y` and a flat `f : X ⟶ Y` of relative dimension `r`, the inverse
image `f⁻¹(I)` is the fibre product `X ×_Y I` (`Scheme.IdealSheafData.comapIso`), so the same
holds for `f⁻¹(I) ⟶ I`.

## Main results

* `MMP.topologicalKrullDim_eq_add_of_relativeDimension`: `dim P = dim Z + r`.
* `MMP.isPullback_comap_subschemeι`: `f⁻¹(I) = X ×_Y I`, as a pullback square.
* `MMP.topologicalKrullDim_comap_eq_add_of_relativeDimension`: `dim f⁻¹(I) = dim I + r`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace MMP

/-- **Dimension under a flat morphism of relative dimension `r`.** For a flat morphism
`p : P ⟶ Z`, locally of finite type, of relative dimension `r`, between irreducible schemes with
`Z` locally of finite type over a field, `dim P = dim Z + r`. -/
theorem topologicalKrullDim_eq_add_of_relativeDimension (K : Type u) [Field K] {P Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IrreducibleSpace Z]
    (p : P ⟶ Z) [Flat p] [LocallyOfFiniteType p] [IrreducibleSpace P] (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p r) :
    topologicalKrullDim P = topologicalKrullDim Z + r := by
  have hW : (Set.univ : Set P) ∈ irreducibleComponents P := by
    rw [irreducibleComponents_eq_singleton]; rfl
  let W : irreducibleComponents P := ⟨Set.univ, hW⟩
  have hξ := W.2.1.isGenericPoint_genericPoint isClosed_univ
  have h1 := topologicalKrullDim_closure_singleton_eq K (p ≫ s) W.2.1.genericPoint
  rw [hξ.def, (Homeomorph.Set.univ P).isHomeomorph.topologicalKrullDim_eq] at h1
  have h2 := topologicalKrullDim_closure_singleton_eq K s (genericPoint Z)
  rw [genericPoint_spec Z, (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq] at h2
  have hδ := relativeDimension_comp_eq_add_trdeg (fieldChowSituation K).dimensionFunction s p
    W.2.1.genericPoint
  rw [toNat_residueTrdeg_genericPoint p W r hp,
    map_genericPoint_irreducibleComponent_eq_genericPoint p W] at hδ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le
    (relativeDimension_fieldChowSituation_nonneg K s (genericPoint Z))
  rw [h1, h2, hδ, hn]
  norm_cast

/-- **The inverse image of a closed subscheme is a fibre product**: `f⁻¹(I) = X ×_Y I`, with
the inclusion `f⁻¹(I) ⟶ X` and `f⁻¹(I) ⟶ I` (`Scheme.IdealSheafData.comapIso`). -/
theorem isPullback_comap_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    IsPullback (I.comap f).subschemeι ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι) f
      I.subschemeι := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso f)
    (Scheme.IdealSheafData.comapIso_hom_fst I f) rfl
  rw [← Scheme.IdealSheafData.comapIso_hom_fst I f, Category.assoc, pullback.condition,
    Category.assoc]

/-- **The dimension of the inverse image under a flat morphism of relative dimension `r`.** For a
flat morphism `f : X ⟶ Y`, locally of finite type, of relative dimension `r`, and a closed
subscheme `I` of `Y` locally of finite type over a field, with `I` and `f⁻¹(I)` irreducible,
`dim f⁻¹(I) = dim I + r`. -/
theorem topologicalKrullDim_comap_eq_add_of_relativeDimension (K : Type u) [Field K]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (I : Y.IdealSheafData)
    (s : I.subscheme ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IrreducibleSpace I.subscheme]
    [IrreducibleSpace (I.comap f).subscheme] :
    topologicalKrullDim (I.comap f).subscheme = topologicalKrullDim I.subscheme + r := by
  have hsq := isPullback_comap_subschemeι f I
  have : Flat ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have : LocallyOfFiniteType ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι) :=
    MorphismProperty.of_isPullback hsq inferInstance
  exact topologicalKrullDim_eq_add_of_relativeDimension K s _ r
    (AlgebraicGeometry.RelativeDimension.of_isPullback hsq hf)

end MMP
