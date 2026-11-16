module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullback
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Additivity of the pull-back of Cartier divisors

For a morphism `f : X' ⟶ X` from an integral scheme, the pull-back of Cartier divisors
`MMP.CartierDivisor.pullback` is additive: `f^*(C + E) = f^*C + f^*E` whenever the three
pull-backs are defined.

## Main results

* `MMP.CartierDivisor.pullback_add`, `MMP.CartierDivisor.pullback_sub`: `f^*(C + E) = f^*C + f^*E`
  and `f^*(C - E) = f^*C - f^*E`.
* `MMP.CartierDivisor.genericPoint_notMem_cartierSupport`: on an integral scheme the generic
  point lies outside the support of every Cartier divisor.
* `MMP.CartierDivisor.not_range_subset_cartierSupport_of_surjective`: so `f^*D` is defined for
  every `D` when `f` is surjective onto an integral scheme.

## Implementation notes

`f^*C + f^*E` has the pulled-back local equations of `C + E`
(`MMP.CartierDivisor.eq_pullback_iff`): near a point, the product `g_C g_E` of local equations of
`C` and `E` is a local equation of `C + E`, whose germ at the image of the generic point is the
product of the germs, and any other local equation of `C + E` differs from it by a unit.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §2.3.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MMP.Intersection

namespace MMP.CartierDivisor

open CartierDivisorPullback

variable {X X' : Scheme.{u}}

/-- **The generic point of an integral scheme is outside every Cartier divisor**: a local
equation near the generic point is a rational function, which is a unit of `𝒪_X` on some
neighbourhood of the generic point. -/
theorem genericPoint_notMem_cartierSupport [IsIntegral X] (D : X.CartierDivisor) :
    genericPoint X ∉ cartierSupport D := by
  obtain ⟨U, hU, g, hg⟩ := exists_isLocalEquationOn D (genericPoint X)
  have hbij := MMP.CartierDivisorSheaf.ofFunctionField_bijective U ⟨_, hU⟩
  obtain ⟨r, hr⟩ := hbij.2 (g : X.totalQuotientSheaf.obj.obj (op U))
  obtain ⟨ri, hri⟩ := hbij.2 (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op U))
  have hrri : r * ri = 1 := hbij.1 (by rw [map_mul, hr, hri, Units.mul_inv, map_one])
  obtain ⟨V₁, hV₁, hη₁, s, hs⟩ := X.presheaf.exists_le_germ_eq (r : X.functionField) hU
  obtain ⟨V₂, hV₂, hη₂, t, ht⟩ := X.presheaf.exists_le_germ_eq (ri : X.functionField) hη₁
  have hst : X.presheaf.germ V₂ _ hη₂ (X.presheaf.map (homOfLE hV₂).op s * t) =
      X.presheaf.germ V₂ _ hη₂ 1 := by
    rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, hs, ht]
    exact hrri
  obtain ⟨W, hηW, iW, iW', hW⟩ := X.presheaf.germ_eq _ hη₂ hη₂ _ _ hst
  rw [map_mul, map_one] at hW
  set a := X.presheaf.map iW.op (X.presheaf.map (homOfLE hV₂).op s)
  set b := X.presheaf.map iW.op t
  let u : Γ(X, W)ˣ := ⟨a, b, hW, (mul_comm b a).trans hW⟩
  have hWU : W ≤ U := (leOfHom iW).trans (hV₂.trans hV₁)
  have hgu : resUnit (homOfLE hWU) g = Units.map (toTotalQuotient W).toMonoidHom u := by
    refine Units.ext ?_
    change X.totalQuotientSheaf.obj.map (homOfLE hWU).op (g : X.totalQuotientSheaf.obj.obj _) =
      toTotalQuotient W a
    have hga : X.presheaf.germ W _ hηW a = (r : X.functionField) := by
      simp only [a]
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hs]
    rw [CartierDivisorPullback.toTotalQuotient_eq_functionFieldToK a hηW hga, ← hr]
    exact MMP.CartierDivisorSheaf.resK_ofFunctionField hWU r
  refine (notMem_cartierSupport_iff (U := ⊤) trivial).2 ⟨W, hηW, le_top, ?_⟩
  rw [← isLocalEquationOn_resUnit (homOfLE hWU) hg, hgu, cartierClass_map_units]

/-- A Cartier divisor on an integral scheme does not contain the image of a surjective
morphism, so its pull-back along that morphism is defined. -/
theorem not_range_subset_cartierSupport_of_surjective [IsIntegral X] {f : X' ⟶ X}
    (hf : Function.Surjective f) (D : X.CartierDivisor) :
    ¬ Set.range f ⊆ cartierSupport D := fun h =>
  genericPoint_notMem_cartierSupport D (h (hf _))

variable [IsIntegral X'] (f : X' ⟶ X)

/-- **Additivity of the pull-back**: `f^*(C + E) = f^*C + f^*E`. -/
theorem pullback_add (C E : X.CartierDivisor)
    (hCE : ¬ Set.range f ⊆ cartierSupport (C + E)) (hC : ¬ Set.range f ⊆ cartierSupport C)
    (hE : ¬ Set.range f ⊆ cartierSupport E) :
    pullback f (C + E) hCE = pullback f C hC + pullback f E hE := by
  symm
  refine (eq_pullback_iff f (C + E) hCE _).2 fun U g hg hU a ha => ?_
  refine isLocalEquationOn_of_locally fun y hy => ?_
  obtain ⟨UC, hyC, gC, hgC⟩ := exists_isLocalEquationOn C (f y)
  obtain ⟨UE, hyE, gE, hgE⟩ := exists_isLocalEquationOn E (f y)
  set V := UC ⊓ UE
  have hηC : f (genericPoint X') ∈ UC := genericPoint_mem (V := f ⁻¹ᵁ UC) hyC
  have hηE : f (genericPoint X') ∈ UE := genericPoint_mem (V := f ⁻¹ᵁ UE) hyE
  have hηV : f (genericPoint X') ∈ V := ⟨hηC, hηE⟩
  obtain ⟨aC, haC⟩ := exists_isGermUnit_of_not_range_subset f C hC hgC hηC
  obtain ⟨aE, haE⟩ := exists_isGermUnit_of_not_range_subset f E hE hgE hηE
  have hgV : IsLocalEquationOn (C + E) V
      (resUnit (homOfLE inf_le_left) gC * resUnit (homOfLE inf_le_right) gE) :=
    MMP.CartierDivisorSheaf.isLocalEquation_mul (isLocalEquationOn_resUnit _ hgC)
      (isLocalEquationOn_resUnit _ hgE)
  have haV : IsGermUnit (resUnit (homOfLE inf_le_left) gC * resUnit (homOfLE inf_le_right) gE)
      hηV (aC * aE) := by
    unfold IsGermUnit at haC haE ⊢
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, haC, haE]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  obtain ⟨c, hc⟩ := exists_unit_mul_eq_pullback f hg hgV hU hηV ha haV
  refine ⟨f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V, homOfLE inf_le_left, ⟨hy, hyC, hyE⟩, ?_⟩
  rw [hc]
  refine IsLocalEquationOn.units_mul ?_ c
  rw [resUnit_ofFunctionField, pullbackGerm, map_mul, ← pullbackGerm, ← pullbackGerm,
    show ∀ r s : X'.functionFieldˣ, ofFunctionField (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (r * s) =
      ofFunctionField _ r * ofFunctionField _ s from fun r s => map_mul _ r s]
  refine MMP.CartierDivisorSheaf.isLocalEquation_mul ?_ ?_
  · rw [← resUnit_ofFunctionField (homOfLE (inf_le_right.trans (Scheme.Hom.preimage_mono f
      inf_le_left) : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ UC))]
    exact isLocalEquationOn_resUnit _ (isLocalEquationOn_pullback f C hC hgC hηC haC)
  · rw [← resUnit_ofFunctionField (homOfLE (inf_le_right.trans (Scheme.Hom.preimage_mono f
      inf_le_right) : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ UE))]
    exact isLocalEquationOn_resUnit _ (isLocalEquationOn_pullback f E hE hgE hηE haE)

/-- `f^*(A - B) = f^*A - f^*B`. -/
theorem pullback_sub (A B : X.CartierDivisor)
    (hAB : ¬ Set.range f ⊆ cartierSupport (A - B)) (hA : ¬ Set.range f ⊆ cartierSupport A)
    (hB : ¬ Set.range f ⊆ cartierSupport B) :
    pullback f (A - B) hAB = pullback f A hA - pullback f B hB := by
  have h := pullback_add f (A - B) B (by rwa [sub_add_cancel]) hAB hB
  simp only [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

end MMP.CartierDivisor
