module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Bijectivity from a decomposition into finitely many pieces

The algebra behind Fulton's Example 19.1.11(b) (disjoint unions): a homomorphism `cl : A → H`
compatible with decompositions `A = ∑_l inc_l(A_l)` and `H ≅ ⨁_l H_l` is bijective when every
piece `cl_l : A_l → H_l` is.

## Main results

* `MMP.bijective_of_sum_decomposition`, `MMP.subsingleton_of_sum_decomposition`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.11.
-/

@[expose] public section

namespace MMP

variable {ι : Type*} [Fintype ι] {A H : Type*} [AddCommGroup A] [AddCommGroup H]
  {Al Hl : ι → Type*} [∀ l, AddCommGroup (Al l)] [∀ l, AddCommGroup (Hl l)]

/-- Let `inc l : Al l → A` and `push l : Hl l → H` be families of homomorphisms with
`∑_l inc l` surjective and `∑_l push l` an isomorphism with inverse `(res l)_l`. If
`cl ∘ inc l = push l ∘ cll l` and every `cll l` is bijective, then `cl` is bijective. -/
theorem bijective_of_sum_decomposition {cl : A →+ H} {cll : ∀ l, Al l →+ Hl l}
    {inc : ∀ l, Al l →+ A} {push : ∀ l, Hl l →+ H} {res : ∀ l, H →+ Hl l}
    (hcomm : ∀ l a, cl (inc l a) = push l (cll l a))
    (hself : ∀ l x, res l (push l x) = x) (hne : ∀ l m, l ≠ m → ∀ x, res m (push l x) = 0)
    (hA : ∀ a, ∃ c : ∀ l, Al l, ∑ l, inc l (c l) = a)
    (hH : ∀ h, ∑ l, push l (res l h) = h)
    (hb : ∀ l, Function.Bijective (cll l)) : Function.Bijective cl := by
  refine ⟨(injective_iff_map_eq_zero cl).2 fun a ha ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := hA a
    have hc : ∀ m, c m = 0 := by
      intro m
      have := congrArg (res m) ha
      rw [map_sum, map_sum, Finset.sum_eq_single m (fun l _ hl ↦ by rw [hcomm, hne l m hl])
        (by simp), hcomm, hself, map_zero] at this
      exact (injective_iff_map_eq_zero _).1 (hb m).1 _ this
    simp [hc]
  · choose c hc using fun l ↦ (hb l).2 (res l h)
    exact ⟨∑ l, inc l (c l), by simp only [map_sum, hcomm, hc, hH]⟩

/-- If `h = ∑_l push l (res l h)` for every `h ∈ H` and every `Hl l` is trivial, so is `H`. -/
theorem subsingleton_of_sum_decomposition {push : ∀ l, Hl l →+ H} {res : ∀ l, H →+ Hl l}
    (hH : ∀ h, ∑ l, push l (res l h) = h) (hs : ∀ l, Subsingleton (Hl l)) : Subsingleton H := by
  refine ⟨fun a b ↦ ?_⟩
  rw [← hH a, ← hH b]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [Subsingleton.elim (res l a) (res l b)]

end MMP
