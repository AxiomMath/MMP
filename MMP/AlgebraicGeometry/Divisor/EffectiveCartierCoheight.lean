module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension

/-!
# Components of an effective Cartier divisor have codimension one

Let `D` be an effective Cartier divisor on a locally noetherian scheme `X`, and let `z` be a point
of `D` with no proper generization in `D`, i.e. the generic point of an irreducible component of
`D`. Then `z` has coheight `1` in the specialization order of `X`.

This is [Stacks, Tag 0BCN] (2),
`AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor`, read off the coheight
and with the component given by its generic point in `X`.

## Main results

* `MMP.eq_of_specializes_of_mem_irreducibleComponents`: the generic point of an irreducible
  component has no proper generization.
* `MMP.coheight_eq_one_of_isEffectiveCartierDivisor_of_isLocallyNoetherian`: the statement on a
  locally noetherian scheme.
* `MMP.coheight_eq_one_of_isEffectiveCartierDivisor`: the same on a scheme locally of finite type
  over a field (Fulton, §1.7).
-/

public section

open AlgebraicGeometry Order

universe u

namespace MMP

/-- The generic point of an irreducible component has no proper generization. -/
theorem eq_of_specializes_of_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [T0Space X] {Z : Set X} (hZ : Z ∈ irreducibleComponents X) {ζ : X} (hζ : closure {ζ} = Z)
    {y : X} (h : y ⤳ ζ) : y = ζ := by
  have hsub : Z ⊆ closure {y} := hζ ▸ specializes_iff_closure_subset.mp h
  have hyZ : y ∈ Z := hZ.2 isIrreducible_singleton.closure hsub (subset_closure rfl)
  rw [← hζ] at hyZ
  exact (h.antisymm (specializes_iff_mem_closure.mpr hyZ)).eq

/-- **Codimension one** [Stacks, Tag 0BCN]. Let `D` be an effective Cartier divisor on a locally
noetherian scheme `X`. A point `z` of `D` with no proper generization in `D` (the generic point of
an irreducible component of `D`) has coheight `1` in the specialization order of `X`. -/
theorem coheight_eq_one_of_isEffectiveCartierDivisor_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {z : X} (hz : z ∈ D.support)
    (hmax : ∀ y ∈ D.support, y ⤳ z → y = z) : coheight z = 1 := by
  obtain ⟨ξ, rfl⟩ : z ∈ Set.range D.subschemeι := by rwa [D.range_subschemeι]
  have hinj := D.subschemeι.isClosedEmbedding.injective
  obtain ⟨W, hW, hξW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure {ξ}) isIrreducible_singleton.closure
  have hWgen := hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have hηξ : hW.1.genericPoint ⤳ ξ :=
    specializes_iff_mem_closure.mpr (by rw [hWgen.def]; exact hξW (subset_closure rfl))
  have hη : hW.1.genericPoint = ξ := by
    refine hinj (hmax _ ?_ (hηξ.map D.subschemeι.continuous))
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact ⟨_, rfl⟩
  have h := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD ξ
    ⟨⟨W, hW⟩, hη ▸ hWgen⟩
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- **Codimension one** (Fulton, §1.7). Let `X` be locally of finite type over a field and `D` an
effective Cartier divisor on `X`. A point `z` of `D` with no proper generization in `D` (the
generic point of an irreducible component of `D`) has coheight `1` in the specialization order
of `X`. -/
theorem coheight_eq_one_of_isEffectiveCartierDivisor (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))] {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {z : X} (hz : z ∈ D.support)
    (hmax : ∀ y ∈ D.support, y ⤳ z → y = z) : coheight z = 1 := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  exact coheight_eq_one_of_isEffectiveCartierDivisor_of_isLocallyNoetherian hD hz hmax

end MMP
