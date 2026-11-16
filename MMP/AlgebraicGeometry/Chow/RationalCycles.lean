module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage

/-!
# Rational cycles in Stacks' encoding

For a Chow situation `C` (Stacks 02QL) and a scheme `X` locally of finite type over its base,
the `ℚ`-vector space of rational `k`-cycles is `Z_k(X)_ℚ = ℚ ⊗ Z_k(X)`, where `Z_k(X)` is Stacks'
group of cycles of delta-dimension `k` (`Stacks.Chow.CycleGroup`, Tag 02QR). Proper pushforward of
rational cycles is the base change of Stacks' proper pushforward of cycles
(`Stacks.Chow.properPushforwardHom`, Tag 02R4); it is functorial (Tag 02R5).

## Main definitions

* `MMP.Chow.RationalCycleGroup C sX k`: the rational `k`-cycles `ℚ ⊗ Z_k(X)`.
* `MMP.Chow.rationalProperPushforward`: proper pushforward of rational `k`-cycles.
* `MMP.Chow.rationalPointCycle`: the rational prime cycle `[x]` of a point of delta-dimension `k`.
* `MMP.Chow.rationalCoeff`: the coefficient of a rational cycle at a point.

## Main results

* `MMP.Chow.rationalProperPushforward_comp`: functoriality.
* `MMP.Chow.rationalCoeff_rationalProperPushforward_tmul`: the coefficient formula of Tag 02R4.

## References

* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct Stacks.Chow

universe u

namespace MMP.Chow

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (k : ℤ)

/-- The `ℚ`-vector space `Z_k(X)_ℚ = ℚ ⊗ Z_k(X)` of rational `k`-cycles on `X`, where `Z_k(X)` is
Stacks' group of cycles of delta-dimension `k`. -/
abbrev RationalCycleGroup : Type u :=
  ℚ ⊗[ℤ] CycleGroup C sX k

/-- Proper pushforward `f_* : Z_k(X)_ℚ → Z_k(Y)_ℚ` of rational `k`-cycles: the base change to `ℚ`
of Stacks' proper pushforward of `k`-cycles (Tag 02R4). -/
def rationalProperPushforward (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) :
    RationalCycleGroup C sX k →ₗ[ℚ] RationalCycleGroup C sY k :=
  LinearMap.baseChange ℚ (properPushforwardHom C sX sY f hf k).toIntLinearMap

variable {C sX sY sZ k}

/-- On a pure tensor, rational pushforward is Stacks' pushforward of the cycle. -/
@[simp]
theorem rationalProperPushforward_tmul (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (q : ℚ)
    (c : CycleGroup C sX k) :
    rationalProperPushforward C sX sY k f hf (q ⊗ₜ c) = q ⊗ₜ properPushforward C sX sY f hf k c :=
  rfl

/-- **Stacks 02R5.** Rational proper pushforward is functorial. -/
theorem rationalProperPushforward_comp (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) :
    rationalProperPushforward C sY sZ k g hg ∘ₗ rationalProperPushforward C sX sY k f hf =
      rationalProperPushforward C sX sZ k (f ≫ g) (by rw [Category.assoc, hg, hf]) := by
  rw [rationalProperPushforward, rationalProperPushforward, rationalProperPushforward,
    ← LinearMap.baseChange_comp]
  congr 1
  exact LinearMap.ext fun c ↦ congrFun (properPushforward_comp C sX sY sZ f g hf hg k) c

/-- **Stacks 02R5.** Rational proper pushforward is functorial, read on a single cycle. -/
theorem rationalProperPushforward_rationalProperPushforward (f : X ⟶ Y) [IsProper f]
    (g : Y ⟶ Z) [IsProper g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
    (c : RationalCycleGroup C sX k) :
    rationalProperPushforward C sY sZ k g hg (rationalProperPushforward C sX sY k f hf c) =
      rationalProperPushforward C sX sZ k (f ≫ g) (by rw [Category.assoc, hg, hf]) c :=
  LinearMap.congr_fun (rationalProperPushforward_comp f g hf hg) c

variable (C sX k)

/-- The rational prime cycle `[x]` of a point `x` of delta-dimension `k`. -/
def rationalPointCycle (x : X) (hx : relativeDimension C.dimensionFunction sX x = k) :
    RationalCycleGroup C sX k :=
  (1 : ℚ) ⊗ₜ pointCycle C sX k x hx

/-- The coefficient of a rational `k`-cycle at a point `x`: the base change to `ℚ` of the
coefficient `c ↦ c(x)` of cycles. -/
def rationalCoeff (x : X) : RationalCycleGroup C sX k →ₗ[ℚ] ℚ :=
  (Algebra.TensorProduct.rid ℤ ℚ ℚ).toLinearMap ∘ₗ
    LinearMap.baseChange ℚ
      ({ toFun := fun c : CycleGroup C sX k ↦ c.1 x
         map_add' := fun _ _ ↦ rfl
         map_smul' := fun _ _ ↦ rfl } : CycleGroup C sX k →ₗ[ℤ] ℤ)

variable {C sX k}

/-- The coefficient of `q ⊗ c` at `x` is `q · c(x)`. -/
@[simp]
theorem rationalCoeff_tmul (x : X) (q : ℚ) (c : CycleGroup C sX k) :
    rationalCoeff C sX k x (q ⊗ₜ c) = q * (c.1 x : ℚ) := by
  simp [rationalCoeff, mul_comm, zsmul_eq_mul]
  exact Or.inl rfl

open Classical in
/-- The coefficient of the rational prime cycle of `x` is one at `x` and zero elsewhere. -/
theorem rationalCoeff_rationalPointCycle (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k) (y : X) :
    rationalCoeff C sX k y (rationalPointCycle C sX k x hx) = if y = x then 1 else 0 := by
  rw [rationalPointCycle, rationalCoeff_tmul, pointCycle_apply, one_mul]
  split_ifs <;> simp

/-- **Stacks 02R4.** The coefficient of the pushforward of `q ⊗ c` at `y` is the locally finite
sum of the coefficients of `c` above `y`, weighted by the residue-field degrees when the
delta-dimension is preserved. -/
theorem rationalCoeff_rationalProperPushforward_tmul (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (q : ℚ) (c : CycleGroup C sX k) (y : Y) :
    rationalCoeff C sY k y (rationalProperPushforward C sX sY k f hf (q ⊗ₜ c)) =
      q * ((∑ᶠ x ∈ f.base ⁻¹' {y}, c.1 x *
        (if relativeDimension C.dimensionFunction sX x =
            relativeDimension C.dimensionFunction sY (f.base x)
          then (f.residueDegree x : ℤ) else 0) : ℤ) : ℚ) := by
  rw [rationalProperPushforward_tmul, rationalCoeff_tmul, properPushforward_apply]

end MMP.Chow
