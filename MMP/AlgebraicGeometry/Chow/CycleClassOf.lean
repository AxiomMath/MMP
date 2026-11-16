module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVariety
public import MMP.AlgebraicTopology.BorelMoore.Pushforward
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
/-!
# Cycle classes of proper morphisms from complex varieties (Fulton, §19.1)

For a proper morphism `i : V → X` over `ℂ` from a complex variety `V` of dimension `k`,
`MMP.IsCycleClassOf R i hk α` says that `α ∈ H_{2k} X` is `i_* c` for a fundamental class
`c ∈ H_{2k} V` of `V` (`MMP.IsVarietyFundamentalClass`). Once the fundamental class exists and is
unique, there is exactly one such `α`.

## Main definitions

* `MMP.IsCycleClassOf R i hk α`: `α = i_* c` for a fundamental class `c` of `V`.

## Main results

* `MMP.isCycleClassOf_pushforward`, `MMP.IsCycleClassOf.eq`, `MMP.isCycleClassOf_id_iff`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open MMP.UnderlyingSpace

namespace MMP

section General

variable (R : Type) [CommRing R] {V X : Scheme.{0}} [V.Over (Spec (.of ℂ))]
  [X.Over (Spec (.of ℂ))] [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))]
  [QuasiCompact (V ↘ Spec (.of ℂ))] [T2Space (UnderlyingSpace ℂ V)]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- For a proper morphism `i : V → X` over `ℂ` from a complex variety `V` of dimension `k`,
`α ∈ H_{2k} X` is `i_* c` for a fundamental class `c ∈ H_{2k} V` of `V` (Fulton, §19.1). -/
def IsCycleClassOf (i : V ⟶ X) [i.IsOver (Spec (.of ℂ))] [IsProper i] {k : ℕ}
    (hk : (k : WithBot ℕ∞) = topologicalKrullDim V)
    (α : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * k : ℕ)) :
    Prop :=
  ∃ c, IsVarietyFundamentalClass R hk c ∧
    borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) i))
      (isProperMap_map (K := ℂ) i) (2 * k : ℕ) c = α

variable {R}

/-- The push-forward of a fundamental class is a cycle class. -/
lemma isCycleClassOf_pushforward (i : V ⟶ X) [i.IsOver (Spec (.of ℂ))] [IsProper i] {k : ℕ}
    {hk : (k : WithBot ℕ∞) = topologicalKrullDim V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hc : IsVarietyFundamentalClass R hk c) :
    IsCycleClassOf R i hk (borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (map (K := ℂ) i)) (isProperMap_map (K := ℂ) i) (2 * k : ℕ) c) :=
  ⟨c, hc, rfl⟩

/-- The cycle class is unique when the fundamental class is. -/
lemma IsCycleClassOf.eq {i : V ⟶ X} [i.IsOver (Spec (.of ℂ))] [IsProper i] {k : ℕ}
    {hk : (k : WithBot ℕ∞) = topologicalKrullDim V}
    (huniq : ∀ c c', IsVarietyFundamentalClass R hk c → IsVarietyFundamentalClass R hk c' →
      c = c')
    {α β : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * k : ℕ)}
    (hα : IsCycleClassOf R i hk α) (hβ : IsCycleClassOf R i hk β) : α = β := by
  obtain ⟨c, hc, rfl⟩ := hα
  obtain ⟨c', hc', rfl⟩ := hβ
  rw [huniq c c' hc hc']

/-- `cl_V(V) = cl(V)`: for the identity of `V`, the cycle classes are the fundamental classes. -/
lemma isCycleClassOf_id_iff {k : ℕ}
    (hk : (k : WithBot ℕ∞) = topologicalKrullDim V)
    (α : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)) :
    IsCycleClassOf R (𝟙 V) hk α ↔ IsVarietyFundamentalClass R hk α := by
  have h : borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (map (K := ℂ) (𝟙 V))) (isProperMap_map (K := ℂ) (𝟙 V)) (2 * k : ℕ) = 𝟙 _ := by
    rw [← borelMooreHomology.pushforward_id R (ModuleCat.of R R) ((2 * k : ℕ) : ℤ)]
    congr 1
  simp only [IsCycleClassOf, h, ModuleCat.id_apply, exists_eq_right]

end General

end MMP
