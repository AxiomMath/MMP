module

public import MMP.AlgebraicTopology.CapProduct.Restriction

/-!
# Chains of proper push-forwards in Borel–Moore homology

## Main results

* `MMP.pushforward_pushforward_apply_eq_pushforward_pushforward_pushforward_apply`: two chains of
  proper push-forwards, of two and of three maps, with the same composite agree.
-/

@[expose] public noncomputable section

open CategoryTheory
open MMP.borelMooreHomology

namespace MMP

variable {R : Type} [CommRing R]

/-- Two chains of proper push-forwards, of two and of three maps, with the same composite agree. -/
lemma pushforward_pushforward_apply_eq_pushforward_pushforward_pushforward_apply
    {A B D B' C' : TopCat.{0}} (f₁ : A ⟶ B) (f₂ : B ⟶ D) (g₁ : A ⟶ B') (g₂ : B' ⟶ C') (g₃ : C' ⟶ D)
    (hf₁ : IsProperMap f₁) (hf₂ : IsProperMap f₂) (hg₁ : IsProperMap g₁)
    (hg₂ : IsProperMap g₂) (hg₃ : IsProperMap g₃) (h : f₁ ≫ f₂ = g₁ ≫ g₂ ≫ g₃) (j : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) A j) :
    (pushforward R (ModuleCat.of R R) f₂ hf₂ j).hom
        ((pushforward R (ModuleCat.of R R) f₁ hf₁ j).hom a) =
      (pushforward R (ModuleCat.of R R) g₃ hg₃ j).hom
        ((pushforward R (ModuleCat.of R R) g₂ hg₂ j).hom
          ((pushforward R (ModuleCat.of R R) g₁ hg₁ j).hom a)) := by
  rw [pushforward_comp_apply R f₁ f₂ hf₁ hf₂ (hf₂.comp hf₁),
    pushforward_comp_apply R g₁ g₂ hg₁ hg₂ (hg₂.comp hg₁),
    pushforward_comp_apply R (g₁ ≫ g₂) g₃ (hg₂.comp hg₁) hg₃ (hg₃.comp (hg₂.comp hg₁))]
  exact pushforward_apply_congr R (by simpa only [Category.assoc] using h) _ _ j a

end MMP
