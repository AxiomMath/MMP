module

public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import MMP.AlgebraicGeometry.Chow.RationalCycles
public import MMP.AlgebraicGeometry.Divisor.Basic

/-!
# The cycle class of rational cycles on a complex scheme

Let `X` be a complex scheme and `C = Stacks.Chow.fieldChowSituation ℂ`. The cycle class map
`cl_X : Z_k(X) → H_{2k}(X; ℚ)` on Stacks' cycles of delta-dimension `k` (`MMP.Chow.cycleClass`)
extends `ℚ`-linearly to the rational cycles `Z_k(X)_ℚ = ℚ ⊗ Z_k(X)`
(`MMP.Chow.RationalCycleGroup`). It commutes with proper push-forward (Fulton, §19.1).

## Main definitions

* `MMP.Chow.rationalCycleClass`: the cycle class `Z_k(X)_ℚ →ₗ[ℚ] H_{2k}(X; ℚ)`.
* `MMP.Chow.primeDivisorCycle`, `MMP.Chow.divisorCycle`: the rational surface cycle of a
  (`ℚ`-)divisor whose components are surfaces.
* `MMP.Chow.divisorClass`: its class in `H_4(X; ℚ)`.

## Main results

* `MMP.Chow.rationalCycleClass_tmul`: on `q ⊗ c` it is `q • cl_X(c)`.
* `MMP.Chow.rationalCycleClass_rationalPointCycle`: the class of `[x]` is `cl_X(x)`.
* `MMP.Chow.rationalCycleClass_rationalProperPushforward`: `cl_Y(f_* α) = f_* cl_X(α)`.
* `MMP.Chow.divisorClass_single`: the class of a prime divisor `P` that is a surface is
  `cl_X(ξ_P)`, for `ξ_P` its generic point.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct MMP MMP.UnderlyingSpace Stacks.Chow

namespace MMP.Chow

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

variable (X) in
/-- **The cycle class of rational cycles**: the `ℚ`-linear extension
`Z_k(X)_ℚ → H_{2k}(X; ℚ)` of the cycle class map `MMP.Chow.cycleClass` (Fulton, §19.1). -/
def rationalCycleClass (k : ℕ) :
    RationalCycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →ₗ[ℚ] BMHomology ℚ X (2 * k) :=
  LinearMap.liftBaseChange ℚ (cycleClass ℚ k).toIntLinearMap

/-- The class of `q ⊗ c` is `q • cl_X(c)`. -/
@[simp]
theorem rationalCycleClass_tmul (k : ℕ) (q : ℚ)
    (c : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    rationalCycleClass X k (q ⊗ₜ c) = q • cycleClass ℚ k c :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The class of the rational prime cycle `[x]` is `cl_X(x)`. -/
theorem rationalCycleClass_rationalPointCycle {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    rationalCycleClass X k (rationalPointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx) =
      pointCycleClass ℚ x hx := by
  rw [rationalPointCycle, rationalCycleClass_tmul, one_smul, cycleClass_pointCycle]

variable [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
  [IsProper f]

/-- **The cycle class of rational cycles commutes with proper push-forward** (Fulton, §19.1):
`cl_Y(f_* α) = f_* cl_X(α)` in `H_{2k}(Y; ℚ)`. -/
theorem rationalCycleClass_rationalProperPushforward (k : ℕ)
    (α : RationalCycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    rationalCycleClass Y k (rationalProperPushforward (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
        (Y ↘ Spec (.of ℂ)) k f (comp_over f _) α) =
      borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * k : ℕ) (rationalCycleClass X k α) := by
  induction α using TensorProduct.induction_on with
  | zero => simp
  | tmul q c =>
    rw [rationalProperPushforward_tmul, rationalCycleClass_tmul, rationalCycleClass_tmul,
      map_smul, cycleClass_properPushforward]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-! ### Divisor cycles -/

section DivisorCycle

variable (X)

open Classical in
/-- The rational surface cycle `[P]` of a prime divisor `P`: the prime cycle of its generic point
when `P` has delta-dimension `2` (a prime divisor of a complex threefold is a surface), and `0`
otherwise. -/
def primeDivisorCycle (P : Mori.PrimeDivisor X) :
    RationalCycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) 2 :=
  if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
      P.genericPoint = 2 then
    rationalPointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) 2 P.genericPoint h
  else 0

/-- The rational surface cycle `∑ dᵢ [Pᵢ]` of a `ℚ`-divisor `∑ dᵢ Pᵢ`. -/
def divisorCycle :
    Mori.QDivisor X →ₗ[ℚ] RationalCycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) 2 :=
  Finsupp.linearCombination ℚ (primeDivisorCycle X)

/-- The class `[D] ∈ H_4(X; ℚ)` of a `ℚ`-divisor `D` all of whose components are surfaces. -/
def divisorClass : Mori.QDivisor X →ₗ[ℚ] BMHomology ℚ X 4 :=
  rationalCycleClass X 2 ∘ₗ divisorCycle X

variable {X}

/-- The rational surface cycle of the `ℚ`-divisor `q P` is `q • [P]`. -/
theorem divisorCycle_single (P : Mori.PrimeDivisor X) (q : ℚ) :
    divisorCycle X (Finsupp.single P q) = q • primeDivisorCycle X P := by
  rw [divisorCycle, Finsupp.linearCombination_single]

/-- The class of a prime divisor `P` of delta-dimension `2` is the cycle class `cl_X(ξ_P)` of its
generic point. -/
theorem divisorClass_single {P : Mori.PrimeDivisor X}
    (hP : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
      P.genericPoint = 2) :
    divisorClass X (Finsupp.single P 1) = pointCycleClass ℚ P.genericPoint hP := by
  rw [divisorClass, LinearMap.comp_apply, divisorCycle_single, one_smul, primeDivisorCycle,
    dif_pos hP]
  exact rationalCycleClass_rationalPointCycle (k := 2) P.genericPoint hP

end DivisorCycle

end MMP.Chow
