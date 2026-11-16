module

public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics

/-!
# Exceptional divisors lie in the exceptional set (KM 2.62–2.63)

An `f`-exceptional prime divisor of a morphism `f : Y → X` lies in the exceptional set `Ex(f)`.
KM state this for a birational morphism of normal varieties; neither hypothesis is used.

## Main results

* `MMP.Positivity.support_subset_exceptionalSet`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

variable {X : Scheme.{u}}

/-- **KM 2.62–2.63, exceptional divisors lie in the exceptional set.** Let `f : Y → X` be a
birational morphism of normal varieties and `E ⊆ Y` an `f`-exceptional prime divisor. Then
`E ⊆ Ex(f)`. Neither birationality nor normality is used. -/
@[mmp "lem_km2c_exceptional_divisor_in_exceptional_set"]
theorem support_subset_exceptionalSet {Y : Scheme.{u}} {f : Y ⟶ X} (E : MMP.Mori.PrimeDivisor Y)
    (hE : RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    E.support ⊆ (exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hyEx
  set η := E.genericPoint
  set V := biregularLocus f
  have hηV : η ∈ f ⁻¹ᵁ V := (specializes_iff_mem_closure.mpr
    (by rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])).mem_open (f ⁻¹ᵁ V).isOpen
      (not_not.mp hyEx)
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let q : (f ⁻¹ᵁ V).toScheme := ⟨η, hηV⟩
  have hcoh : Order.coheight (f η) = 1 := by
    have h1 : Order.coheight (((f ∣_ V) ≫ V.ι) q) = Order.coheight q :=
      Topology.IsOpenEmbedding.coheight_eq _ ((f ∣_ V) ≫ V.ι).isOpenEmbedding
    have h2 : Order.coheight ((f ⁻¹ᵁ V).ι q) = Order.coheight q :=
      Topology.IsOpenEmbedding.coheight_eq _ (f ⁻¹ᵁ V).ι.isOpenEmbedding
    have h3 : ((f ∣_ V) ≫ V.ι) q = f η := by
      rw [morphismRestrict_ι]
      rfl
    rw [← h3, h1, ← h2]
    exact E.coheight_genericPoint
  have hdef : RationalMap.DefinedAt (X := Y) f.toRationalMap η := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have hsub : (IrreducibleCloseds.closureSingleton (f η) : Set X) ⊆
      (RationalMap.transform (X := Y) f.toRationalMap E.idealSheaf.support : Set X) := by
    rw [IrreducibleCloseds.coe_closureSingleton]
    refine (Closeds.isClosed _).closure_subset_iff.mpr ?_
    rintro _ rfl
    refine RationalMap.image_subset_transform f.toPartialMap rfl _ ?_
    rw [image_toPartialMap_hom]
    refine ⟨η, ?_, rfl⟩
    change η ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hle := le_closedsCodimension_iff.mp ((RationalMap.isExceptional_iff.mp hE) hdef) _ hsub
  have hcodim : codimension (IrreducibleCloseds.closureSingleton (f η)) = Order.coheight (f η) := by
    have h : IrreducibleCloseds.closureSingleton (f η) = irreducibleSetEquivPoints.symm (f η) :=
      IrreducibleCloseds.ext (by
        rw [IrreducibleCloseds.coe_closureSingleton, coe_irreducibleEquivPoints_symm_apply])
    rw [codimension_eq_coheight, h]
    exact Order.coheight_orderIso irreducibleSetEquivPoints.symm (f η)
  rw [hcodim, hcoh] at hle
  exact absurd hle (by decide)

end MMP.Positivity
