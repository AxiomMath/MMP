module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Variety.SmoothVarietyConstructions
/-!
# Open subschemes of complex schemes (Fulton, §19.1)

An open subscheme `U` of a complex scheme `X` is a complex scheme. If `i : X → P` is a closed
imbedding into a smooth variety, `P' = P ∖ i(X ∖ U)` is open in `P`, a smooth variety when `U` is
non-empty (`MMP.isSmoothVariety_opens_ι`), and `U = i⁻¹(P')` is a closed subscheme of `P'`; an
empty `U` is a closed subscheme of `P` itself.

## Main results

* `MMP.isComplexScheme_opens`: an open subscheme of a complex scheme is a complex scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- **An open subscheme of a complex scheme is a complex scheme** (Fulton, §19.1), for any
structure over `Spec ℂ` making the inclusion a morphism over `Spec ℂ`. -/
instance isComplexScheme_opens {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    (U : X.Opens) [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] :
    IsComplexScheme U.toScheme where
  toLocallyOfFiniteType := by
    rw [← comp_over U.ι (Spec (.of ℂ))]
    infer_instance
  toQuasiCompact := by
    haveI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
    haveI : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of ℂ))).mp inferInstance
    haveI : IsNoetherian X := (isNoetherian_iff X).mpr ⟨inferInstance, inferInstance⟩
    rw [← comp_over U.ι (Spec (.of ℂ))]
    infer_instance
  exists_isClosedImmersion := by
    obtain ⟨P, _, _, i, hi, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
    by_cases hU : (U : Set X).Nonempty
    swap
    · have : IsEmpty U.toScheme := by
        rw [Set.not_nonempty_iff_eq_empty] at hU
        exact ⟨fun x ↦ (Set.eq_empty_iff_forall_notMem.1 hU) x.1 x.2⟩
      exact ⟨P, inferInstance, inferInstance, U.ι ≫ i, inferInstance, inferInstance⟩
    let P' : P.Opens := ⟨(i.base '' (U : Set X)ᶜ)ᶜ,
      (i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
    have hP' : i ⁻¹ᵁ P' = U := by
      ext x
      change i.base x ∉ i.base '' (U : Set X)ᶜ ↔ x ∈ U
      rw [i.isClosedEmbedding.injective.mem_set_image]
      exact not_not
    let : P'.toScheme.Over (Spec (.of ℂ)) := ⟨P'.ι ≫ P ↘ Spec (.of ℂ)⟩
    have : P'.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
    have hne : (P' : Set P).Nonempty := by
      obtain ⟨x, hx⟩ := hU
      refine ⟨i.base x, ?_⟩
      have hx' : x ∈ i ⁻¹ᵁ P' := by rw [hP']; exact hx
      exact hx'
    have : Nonempty P' := hne.to_subtype
    have : IsSmoothVariety ℂ (P'.toScheme ↘ Spec (.of ℂ)) :=
      isSmoothVariety_opens_ι ℂ (P ↘ Spec (.of ℂ)) P'
    refine ⟨P', inferInstance, inferInstance, (X.isoOfEq hP'.symm).hom ≫ (i ∣_ P'), ⟨?_⟩,
      inferInstance⟩
    change ((X.isoOfEq hP'.symm).hom ≫ (i ∣_ P')) ≫ P'.ι ≫ P ↘ Spec (.of ℂ) =
      U.toScheme ↘ Spec (.of ℂ)
    rw [Category.assoc, morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc, comp_over,
      comp_over]

end MMP
