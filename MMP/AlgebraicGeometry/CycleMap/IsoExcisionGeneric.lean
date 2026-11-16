module

public import Mathlib.Algebra.Exact.Basic
public import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction

/-!
# The five lemma of Fulton's Example 19.1.11(a), and closed subschemes of complex schemes

## Main results

* `MMP.bijective_of_exact_of_exact`: the five lemma in the form used for excision.
* `MMP.isComplexScheme_subscheme_of_isOver`: a closed subscheme of a complex scheme, with any
  structure over `ℂ` making its inclusion a morphism over `ℂ`, is a complex scheme.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.11.
-/

@[expose] public noncomputable section

namespace MMP

section algebra

variable {AY AX AU HY HX HU : Type*} [AddCommGroup AY] [AddCommGroup AX] [AddCommGroup AU]
  [AddCommGroup HY] [AddCommGroup HX] [AddCommGroup HU]

/-- **The five lemma, in the form of Fulton's Example 19.1.11(a).** Given a commutative diagram
`A_Y → A_X → A_U → 0` over `0 → H_Y → H_X → H_U`, both rows exact, with `cl_Y` and `cl_U`
bijective, `cl_X` is bijective. -/
theorem bijective_of_exact_of_exact {iA : AY →+ AX} {jA : AX →+ AU} {iH : HY →+ HX}
    {jH : HX →+ HU} {clY : AY →+ HY} {clX : AX →+ HX} {clU : AU →+ HU}
    (hcY : ∀ b, clX (iA b) = iH (clY b)) (hcU : ∀ a, jH (clX a) = clU (jA a))
    (hA : Function.Exact iA jA) (hjA : Function.Surjective jA) (hiH : Function.Injective iH)
    (hH : Function.Exact iH jH) (hY : Function.Bijective clY)
    (hU : Function.Bijective clU) : Function.Bijective clX := by
  refine ⟨(injective_iff_map_eq_zero clX).2 fun a ha ↦ ?_, fun h ↦ ?_⟩
  · have h1 : jA a = 0 := (injective_iff_map_eq_zero clU).1 hU.1 _ (by rw [← hcU, ha, map_zero])
    obtain ⟨b, rfl⟩ := (hA a).1 h1
    have h2 : clY b = 0 := (injective_iff_map_eq_zero iH).1 hiH _ (by rw [← hcY, ha])
    rw [(injective_iff_map_eq_zero clY).1 hY.1 _ h2, map_zero]
  · obtain ⟨u, hu⟩ := hU.2 (jH h)
    obtain ⟨a, rfl⟩ := hjA u
    obtain ⟨y, hy⟩ := (hH (h - clX a)).1 (by rw [map_sub, hcU, hu, sub_self])
    obtain ⟨b, rfl⟩ := hY.2 y
    exact ⟨a + iA b, by rw [map_add, hcY, hy, add_sub_cancel]⟩

end algebra

open AlgebraicGeometry CategoryTheory

/-- A closed subscheme of a complex scheme is a complex scheme. -/
instance isComplexScheme_subscheme_of_isOver {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X]
    (I : X.IdealSheafData) [I.subscheme.Over (Spec (.of ℂ))]
    [I.subschemeι.IsOver (Spec (.of ℂ))] : IsComplexScheme I.subscheme :=
  IsComplexScheme.of_isClosedImmersion I.subschemeι

end MMP
