module

public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Elementary properties of formal transforms (Kollár, proofs of 3.100 and 3.111)

Along a blow-up sequence `(X_i, Z_i)` the formal transforms of an ideal sheaf `K ⊆ 𝒪_X` with
marking `μ` are `T_0(K, μ) = K` and `T_{i+1}(K, μ) = 𝒪_{X_{i+1}}(μF_{i+1})·π_i^*T_i(K, μ)`,
`F_{i+1} = π_i⁻¹(Z_i)` (`MMP.Resolution.ClosedBlowupSequence.formalTransform`). Since pullback
and multiplication by the invertible sheaves `𝒪(μF)` commute with sums and products, formal
transforms are additive in `K`, monotone in the marking, and multiplicative in the pair
`(K, μ)`.

## Main definitions

* `MMP.Resolution.FractionalIdealRep.kollarInstLE`, `…kollarInstAdd`, `…kollarInstMul`, and
  `MMP.Resolution.FractionalIdealRep.KollarEquiv`: inclusion, sum, product and equality of the
  fractional ideal sheaves `N·D⁻¹` represented by pairs `(N, D)`.

## Main statements

* `MMP.Resolution.Kollar.formalTransform_le_of_le_marking`: `μ ≤ μ' ⇒ T_i(K, μ) ⊆ T_i(K, μ')`.
* `MMP.Resolution.Kollar.formalTransform_sup`: `T_i(K₁ + K₂, μ) = T_i(K₁, μ) + T_i(K₂, μ)`.
* `MMP.Resolution.Kollar.formalTransform_mono`: `K₁ ⊆ K₂ ⇒ T_i(K₁, μ) ⊆ T_i(K₂, μ)`.
* `MMP.Resolution.Kollar.formalTransform_mul_add`:
  `T_i(K₁K₂, μ₁ + μ₂) = T_i(K₁, μ₁)·T_i(K₂, μ₂)`.

## Implementation notes

A fractional ideal sheaf `N·D⁻¹` with `D` invertible is recorded by the pair `(N, D)`
(`MMP.Resolution.FractionalIdealRep`). Since multiplication by an invertible ideal sheaf is an
order isomorphism on fractional ideal sheaves, `N₁D₁⁻¹ ⊆ N₂D₂⁻¹` exactly when
`N₁D₂ ⊆ N₂D₁`, and `N₁D₁⁻¹ = N₂D₂⁻¹` exactly when `N₁D₂ = N₂D₁`; the sum is
`(N₁D₂ + N₂D₁)(D₁D₂)⁻¹` and the product `N₁N₂(D₁D₂)⁻¹`. These are the relations and operations
on pairs used below. The product formula holds even as an equality of pairs.

Unwinding the recursion, `T_i(K, μ) = Π_i^*K · E_i^{-μ}` with `Π_i : X_i → X` the composite
and `E_i = ∏_{j ≤ i} (pullback of I_{F_j})`; all three statements follow from this. The source
works with smooth varieties and smooth centres; the proofs only use the definitions, so those
hypotheses are dropped.

## References

* [J. Kollár, *Lectures on resolution of singularities*, proofs of Thm. 3.100 and Thm. 3.111]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution

namespace FractionalIdealRep

variable {X : Scheme.{u}}

/-- Inclusion `N₁D₁⁻¹ ⊆ N₂D₂⁻¹` of fractional ideal sheaves, i.e. `N₁D₂ ⊆ N₂D₁`. -/
instance kollarInstLE : LE (FractionalIdealRep X) where
  le T T' := T.num * T'.den ≤ T'.num * T.den

/-- Equality `N₁D₁⁻¹ = N₂D₂⁻¹` of fractional ideal sheaves, i.e. `N₁D₂ = N₂D₁`. -/
def KollarEquiv (T T' : FractionalIdealRep X) : Prop :=
  T.num * T'.den = T'.num * T.den

/-- `N₁D₁⁻¹ = N₂D₂⁻¹` holds exactly when `N₁D₂ = N₂D₁`. -/
theorem kollarEquiv_iff (T T' : FractionalIdealRep X) :
    T.KollarEquiv T' ↔ T.num * T'.den = T'.num * T.den :=
  Iff.rfl

/-- The sum `N₁D₁⁻¹ + N₂D₂⁻¹ = (N₁D₂ + N₂D₁)(D₁D₂)⁻¹` of fractional ideal sheaves. -/
instance kollarInstAdd : Add (FractionalIdealRep X) where
  add T T' := ⟨T.num * T'.den + T'.num * T.den, T.den * T'.den⟩

/-- The product `N₁D₁⁻¹ · N₂D₂⁻¹ = N₁N₂(D₁D₂)⁻¹` of fractional ideal sheaves. -/
instance kollarInstMul : Mul (FractionalIdealRep X) where
  mul T T' := ⟨T.num * T'.num, T.den * T'.den⟩

/-- `N₁D₁⁻¹ ⊆ N₂D₂⁻¹` holds exactly when `N₁D₂ ⊆ N₂D₁`. -/
theorem le_def (T T' : FractionalIdealRep X) : T ≤ T' ↔ T.num * T'.den ≤ T'.num * T.den :=
  Iff.rfl

/-- The numerator of `(N₁, D₁) + (N₂, D₂)` is `N₁D₂ + N₂D₁`. -/
@[simp] theorem num_add (T T' : FractionalIdealRep X) :
    (T + T').num = T.num * T'.den + T'.num * T.den := rfl

/-- The denominator of `(N₁, D₁) + (N₂, D₂)` is `D₁D₂`. -/
@[simp] theorem den_add (T T' : FractionalIdealRep X) : (T + T').den = T.den * T'.den := rfl

/-- The numerator of `(N₁, D₁) · (N₂, D₂)` is `N₁N₂`. -/
@[simp] theorem num_mul (T T' : FractionalIdealRep X) : (T * T').num = T.num * T'.num := rfl

/-- The denominator of `(N₁, D₁) · (N₂, D₂)` is `D₁D₂`. -/
@[simp] theorem den_mul (T T' : FractionalIdealRep X) : (T * T').den = T.den * T'.den := rfl

end FractionalIdealRep

namespace Kollar

open ClosedBlowupSequence Scheme.IdealSheafData

/-- The product `E_r = ∏_j Π_{j,r}^* I_{F_j}` of the pullbacks to `X_r` of the exceptional
ideals `I_{F_{j+1}} = π_j^{-1} I_{Z_j}` of a blow-up sequence. -/
private def exceptionalProduct : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) →
    B.target.IdealSheafData
  | _, nil _ => ⊤
  | _, cons Z B => (Z.comap (blowUpToBase Z)).comap B.toBase * exceptionalProduct B

/-- Closed form of the recursion: the transform of `N·D⁻¹` is `Π^*N·(Π^*D·E^μ)⁻¹`. -/
private theorem formalTransformAux_eq {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (N D : X.IdealSheafData) (μ : ℕ) :
    B.formalTransformAux N D μ =
      ⟨N.comap B.toBase, D.comap B.toBase * exceptionalProduct B ^ μ⟩ := by
  induction B with
  | nil X =>
    change (⟨N, D⟩ : FractionalIdealRep X) = ⟨N.comap (𝟙 X), D.comap (𝟙 X) * ⊤ ^ μ⟩
    rw [comap_id, comap_id, ← one_eq_top, one_pow, mul_one]
  | cons Z B ih =>
    change B.formalTransformAux _ _ μ = (⟨N.comap (B.toBase ≫ blowUpToBase Z),
      D.comap (B.toBase ≫ blowUpToBase Z) *
        ((Z.comap (blowUpToBase Z)).comap B.toBase * exceptionalProduct B) ^ μ⟩ :
          FractionalIdealRep B.target)
    rw [ih, comap_comp, comap_comp, Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow,
      mul_pow, mul_assoc]

private theorem formalTransform_eq {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (K : X.IdealSheafData) (μ i : ℕ) :
    B.formalTransform K μ i =
      ⟨K.comap (B.truncate i).toBase, exceptionalProduct (B.truncate i) ^ μ⟩ := by
  rw [formalTransform, formalTransformAux_eq, comap_top, top_mul]

/-- Raising the marking enlarges the formal transform (Kollár, proofs of Thm. 3.100 and
Thm. 3.111): for `μ ≤ μ'`, `T_i(K, μ) ⊆ T_i(K, μ')`. -/
@[mmp "lem_kr3e_formal_transform_change_marking"]
theorem formalTransform_le_of_le_marking {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (K : X.IdealSheafData) {μ μ' : ℕ} (h : μ ≤ μ') (i : ℕ) :
    B.formalTransform K μ i ≤ B.formalTransform K μ' i := by
  rw [formalTransform_eq, formalTransform_eq, FractionalIdealRep.le_def]
  exact mul_le_mul_right (pow_le_pow_of_le_one bot_le le_top h) _

/-- Formal transforms are additive (Kollár, proofs of Thm. 3.100 and Thm. 3.111):
`T_i(K₁ + K₂, μ) = T_i(K₁, μ) + T_i(K₂, μ)` as fractional ideal sheaves. -/
@[mmp "lem_kr3e_formal_transform_sum"]
theorem formalTransform_sup {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (K₁ K₂ : X.IdealSheafData) (μ i : ℕ) :
    (B.formalTransform (K₁ ⊔ K₂) μ i).KollarEquiv
      (B.formalTransform K₁ μ i + B.formalTransform K₂ μ i) := by
  rw [formalTransform_eq, formalTransform_eq, formalTransform_eq,
    FractionalIdealRep.kollarEquiv_iff, FractionalIdealRep.num_add, FractionalIdealRep.den_add,
    comap_sup]
  simp only [← add_eq_sup]
  ring

/-- Formal transforms are monotone in the ideal (Kollár, proofs of Thm. 3.100 and Thm. 3.111):
`K₁ ⊆ K₂ ⇒ T_i(K₁, μ) ⊆ T_i(K₂, μ)`. -/
@[mmp "lem_kr3e_formal_transform_sum"]
theorem formalTransform_mono {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    {K₁ K₂ : X.IdealSheafData} (h : K₁ ≤ K₂) (μ i : ℕ) :
    B.formalTransform K₁ μ i ≤ B.formalTransform K₂ μ i := by
  rw [formalTransform_eq, formalTransform_eq, FractionalIdealRep.le_def]
  exact mul_le_mul_left (comap_mono _ h) _

/-- Formal transforms are multiplicative in the marked ideal (Kollár, proofs of Thm. 3.100 and
Thm. 3.111): `T_i(K₁K₂, μ₁ + μ₂) = T_i(K₁, μ₁)·T_i(K₂, μ₂)`; this holds already for the
representing pairs. -/
@[mmp "lem_kr3e_marked_transform_mul_add_mono"]
theorem formalTransform_mul_add {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (K₁ K₂ : X.IdealSheafData) (μ₁ μ₂ i : ℕ) :
    B.formalTransform (K₁ * K₂) (μ₁ + μ₂) i =
      B.formalTransform K₁ μ₁ i * B.formalTransform K₂ μ₂ i := by
  rw [formalTransform_eq, formalTransform_eq, formalTransform_eq, Stacks.IdealSheaf.comap_mul,
    pow_add]
  rfl

end Kollar

end MMP.Resolution
