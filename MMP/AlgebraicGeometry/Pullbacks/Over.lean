module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The projections of a fibre product over a base

For schemes `V`, `W` over `S`, the fibre product `V ×_S W = pullback (V ↘ S) (W ↘ S)` is a
scheme over `S` through `pr₂ : V ×_S W → W` (Mathlib's instance). Both projections are then
morphisms over `S`, and `V ×_S W` is locally of finite type over `S` when `V` and `W` are.

## Main results

* `MMP.isOver_pullback_fst`, `MMP.isOver_pullback_snd`: the projections are morphisms over `S`.
* `MMP.locallyOfFiniteType_pullback_over`: `V ×_S W → S` is locally of finite type when
  `V → S` and `W → S` are.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace MMP

variable {S : Scheme.{u}} (V W : Scheme.{u}) [V.Over S] [W.Over S]

/-- The first projection `V ×_S W ⟶ V` is a morphism over `S`. -/
instance isOver_pullback_fst : (pullback.fst (V ↘ S) (W ↘ S)).IsOver S :=
  ⟨pullback.condition⟩

/-- The second projection `V ×_S W ⟶ W` is a morphism over `S`. -/
instance isOver_pullback_snd : (pullback.snd (V ↘ S) (W ↘ S)).IsOver S :=
  ⟨rfl⟩

/-- The fibre product `V ×_S W` is locally of finite type over `S` when `V` and `W` are. -/
instance locallyOfFiniteType_pullback_over [LocallyOfFiniteType (V ↘ S)]
    [LocallyOfFiniteType (W ↘ S)] :
    LocallyOfFiniteType (pullback (V ↘ S) (W ↘ S) ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd (V ↘ S) (W ↘ S) ≫ W ↘ S))

end MMP
