module

public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform

/-!
# Log discrepancies, log canonical and dlt pairs

Let `Y` be a normal variety over `k` and `B` an `ℝ`-divisor on `Y` with `K_Y + B` `ℝ`-Cartier.
For a divisorial valuation `F` over `Y`, realized as a prime divisor on a normal variety `Y'`
with a proper birational morphism `g : Y' ⟶ Y`, the *log discrepancy* is
`a(F, Y, B) = 1 + coeff_F(K_{Y'} - g^*(K_Y + B))`, with `K_{Y'}` and `K_Y` chosen so that
`g_*K_{Y'} = K_Y` (Kollár–Mori 2.25). A pair `(X, Δ)` (normal, `Δ` an effective `ℚ`-divisor,
`K_X + Δ` `ℚ`-Cartier) is *log canonical* if every log discrepancy is `≥ 0`, and *dlt*
(Kollár–Mori 2.37) if it is lc, the coefficients of `Δ` are at most one, and there is a closed
`Z ⊆ X` with `X ∖ Z` smooth, `Δ|_{X ∖ Z}` of snc support, and `a(E, X, Δ) > 0` for every prime
divisor `E` over `X` with centre in `Z`.

## Main definitions

* `MMP.Intersection.IsLogDiscrepancy`: `a = a(F, Y, B)`.
* `MMP.Intersection.IsLogCanonicalPair`, `MMP.Intersection.IsDltPair`.

## Implementation notes

* **Canonical divisors chosen compatibly.** `K_Y = div(ω)` and `K_{Y'} = div(g^*ω)` for a
  nonzero rational top form `ω` on `Y` (`MMP.Mori.RationalPluriForms`), with `div(ω)` a canonical
  divisor (`MMP.Mori.Divisor.IsCanonicalDivisor`); then `coeff_F(K_{Y'}) = ord_F(g^*ω)`
  (`MMP.Mori.DivisorOver.ordPullback`) and `g_*K_{Y'} = K_Y` because `g^*` identifies the rational
  forms of `Y` and `Y'`. Every compatible choice is of this form (a canonical divisor of `Y'` is
  the divisor of a rational top form, and it is the pull-back of one on `Y`), so this is the
  source's choice.
* **`ℝ`-Cartier divisors and their pull-backs.** `K_Y + B` is `ℝ`-Cartier when it is a finite
  `ℝ`-linear combination `∑ rᵢ Cᵢ` of Cartier (locally principal) Weil divisors `Cᵢ`
  (`MMP.Mori.Divisor.IsCartier`); then `g^*(K_Y + B) = ∑ rᵢ g^*Cᵢ`, with `g^*Cᵢ` the pull-back of
  Cartier divisors `MMP.Mori.Divisor.IsPullback`. Both choices (of `ω` and of the representation)
  enter existentially; the value does not depend on them.
* The divisorial valuation `F` is a `MMP.Mori.DivisorOver` `(Y', g, F)` with `g` proper, as in
  the source. The source's base field has characteristic zero; the definition is stated over any
  field (a generalization). The forms have degree `n`, which `IsCanonicalDivisor` forces to be
  `dim Y`.
* "`a` is the log discrepancy" is a predicate on `a`, as `MMP.Mori.IsDiscrepancy` is for the
  discrepancy. "`A(v) ≥ 0` for every divisorial valuation `v`" reads: every log discrepancy of
  every divisor over `X` is `≥ 0`; likewise for `a(E, X, B) > 0` in the dlt condition.
* A *pair* `(X, Δ)` is `MMP.Mori.IsPair` (normal variety, `K_X + Δ` `ℚ`-Cartier) with `Δ`
  effective. Its log discrepancies are those of `Δ` regarded as an `ℝ`-divisor.
* **dlt.** `X ∖ Z` is the open subscheme `Zᶜ`; it is smooth when `MMP.Mori.IsSmoothScheme` holds
  for `Zᶜ ⟶ X ⟶ Spec k`. The restriction `B|_{X ∖ Z}` is the inverse transform of `B` along the
  open immersion `Zᶜ ⟶ X` (`MMP.Mori.inverseTransformDivisor`, whose prime divisors are the
  `P ∩ Zᶜ`), and "snc support" is Kollár–Mori's snc condition
  `MMP.Mori.DivisorWithCoeffs.IsSNC`, which depends only on the support. The centre of a divisor
  over `X` is `MMP.Mori.DivisorOver.center`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori (Divisor QDivisor RDivisor DivisorWithCoeffs DivisorOver)

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The log discrepancy** `a(F, Y, B)` (Kollár–Mori 2.25). For a normal variety `X` (over `k`
by `s_X`) of dimension `n`, an `ℝ`-divisor `B` and a divisor `(Y', g, F)` over `X` with `g`
proper, `a` is the log discrepancy if `a = 1 + coeff_F(K_{Y'} - g^*(K_X + B))`, where
`K_X = div(ω)` is the canonical divisor of a nonzero rational `n`-form `ω` and `K_{Y'} = div(g^*ω)`
(so `g_*K_{Y'} = K_X`), and `K_X + B = ∑ rᵢ Cᵢ` with `Cᵢ` Cartier, `g^*(K_X + B) = ∑ rᵢ g^*Cᵢ`. -/
@[mmp "def_shared_log_discrepancy"]
def IsLogDiscrepancy (n : ℕ) (B : RDivisor X) (D : DivisorOver k sX) (a : ℝ) : Prop :=
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  MMP.Mori.IsNormalVariety k sX ∧ IsProper D.f ∧
    ∃ ω : MMP.Mori.RationalPluriForms sX n 1, ω ≠ 0 ∧
      (∃ K : Divisor X, K.IsCanonicalDivisor sX n ∧ ∀ Γ, K.coeff Γ = Γ.ordForm ω) ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (C : Fin m → Divisor X) (C' : Fin m → Divisor D.Y),
        (∀ i, (C i).IsCartier) ∧
        (∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ) ∧
        (∀ i, ∃ hC, (C i).IsPullback D.f hC (C' i)) ∧
        a = 1 + (D.ordPullback ω : ℝ) - ∑ i, r i * (C' i).coeff D.E

/-- **Log canonical pairs.** A pair `(X, Δ)` of a normal variety and an effective `ℚ`-divisor
with `K_X + Δ` `ℚ`-Cartier is *log canonical* if `A_{X,Δ}(v) ≥ 0` for every divisorial valuation
`v` of `X`. -/
@[mmp "def_shared_log_canonical_pair"]
def IsLogCanonicalPair (Δ : QDivisor X) : Prop :=
  MMP.Mori.IsPair sX Δ ∧ (∀ P, 0 ≤ Δ.coeff P) ∧
    ∀ (n : ℕ) (D : DivisorOver k sX) (a : ℝ),
      IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor Δ) D a → 0 ≤ a

/-- **dlt pairs** (Kollár–Mori 2.37). A pair `(X, B)` is *dlt* if it is log canonical, the
coefficients of `B` are at most one, and there is a closed subset `Z ⊆ X` such that `X ∖ Z` is
smooth, `B|_{X ∖ Z}` has simple normal crossing support, and `a(E, X, B) > 0` for every prime
divisor `E` over `X` whose centre on `X` lies in `Z`. -/
@[mmp "def_shared_dlt_pair"]
def IsDltPair (B : QDivisor X) : Prop :=
  IsLogCanonicalPair sX B ∧ (∀ P, B.coeff P ≤ 1) ∧
    ∃ Z : Closeds X,
      MMP.Mori.IsSmoothScheme (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX) ∧
      DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX)
        (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : X.Opens)) B) ∧
      ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
        ∀ a : ℝ, IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) D a → 0 < a

end MMP.Intersection
