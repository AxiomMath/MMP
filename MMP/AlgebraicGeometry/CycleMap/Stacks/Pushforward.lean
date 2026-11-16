module

public import MMP.AlgebraicGeometry.Chow.CycleClassDescent
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# The cycle class map on Chow groups commutes with proper push-forward (Fulton, §19.1)

For a proper morphism `f : X → Y` of complex schemes and a class `a ∈ A_k(X)` of Stacks' Chow
group over `fieldChowSituation ℂ`, `cl_Y(f_* a) = f_* cl_X(a)` in `H_{2k}(Y(ℂ); R)`, where `f_*`
on the left is Stacks' proper push-forward on Chow groups (Stacks 0GU8). On representatives this
is `MMP.Chow.cycleClass_properPushforward`.

## Main results

* `MMP.Chow.chowCycleClass_properChowPushforward`: `cl_Y(f_* a) = f_* cl_X(a)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MMP.UnderlyingSpace Stacks.Chow

namespace MMP.Chow

variable (R : Type) [CommRing R] {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f]

/-- **The cycle class map on Chow groups commutes with proper push-forward** (Fulton, §19.1):
for a proper morphism `f : X → Y` of complex schemes and `a ∈ A_k(X)`,
`cl_Y(f_* a) = f_* cl_X(a)` in `H_{2k}(Y(ℂ); R)`. -/
theorem chowCycleClass_properChowPushforward {k : ℕ}
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _) k)
    (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    chowCycleClass (X := Y) R k
        (properChowPushforward (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
          (comp_over f _) k hfac a) =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * k : ℕ) (chowCycleClass (X := X) R k a) := by
  induction a using QuotientAddGroup.induction_on with
  | H α => exact cycleClass_properPushforward R f α

/-- `chowCycleClass_properChowPushforward` with Stacks 02S2 discharged
(`properPushforwardFactorsThroughRationalEquivalence_of_isProper`). -/
theorem chowCycleClass_properChowPushforward_of_isProper {k : ℕ}
    (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    chowCycleClass (X := Y) R k
        (properChowPushforward (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
          (comp_over f _) k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ f
            (comp_over f _) k) a) =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * k : ℕ) (chowCycleClass (X := X) R k a) :=
  chowCycleClass_properChowPushforward R f _ a

end MMP.Chow
