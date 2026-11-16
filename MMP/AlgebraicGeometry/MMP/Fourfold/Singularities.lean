module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy

/-!
# Singularities of pairs in the fourfold source

Klt pairs, real canonical and real terminal pairs (real boundaries with all coefficients in
`(0, 1)`), and the strata of the reduced boundary of a dlt pair, stated with the log discrepancy
`MMP.Intersection.IsLogDiscrepancy` of the shared foundations.

## Main definitions

* `MMP.Fourfold.RDivisor.IsRCartier`: `ℝ`-Cartier `ℝ`-divisors.
* `MMP.Fourfold.IsKltPair`: klt pairs.
* `MMP.Fourfold.IsRealCanonicalPair`, `MMP.Fourfold.IsRealTerminalPair`: real canonical and real
  terminal pairs with no coefficient one.
* `MMP.Fourfold.IsDltStratum`: the strata of `⌊B⌋` for a dlt pair `(X, B)`.
* `MMP.Fourfold.minimalLogDiscrepancy`: `mld_x(X, B)`.
* `MMP.Fourfold.hyperstandardSet`: hyperstandard coefficient sets.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- An `ℝ`-divisor `D` is *`ℝ`-Cartier* if it is a real linear combination `∑ rᵢ Cᵢ` of Cartier
divisors `Cᵢ`. -/
def RDivisor.IsRCartier (D : RDivisor X) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℝ) (C : Fin m → Divisor X), (∀ i, (C i).IsCartier) ∧
    ∀ Γ : MMP.Mori.PrimeDivisor X, D.coeff Γ = ∑ i, r i * (C i).coeff Γ

/-- A pair `(X, B)` (`MMP.Fourfold.IsPair`) is *klt* if `a(v; X, B) > 0` for every divisorial
valuation `v` of `k(X)`, realized as a divisor over `X`. -/
@[mmp "def_oai4_bg_klt_pair"]
def IsKltPair (B : QDivisor X) : Prop :=
  IsPair sX B ∧ ∀ (n : ℕ) (D : DivisorOver k sX) (a : ℝ),
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a → 0 < a

/-- A *real canonical pair with no coefficient one* `(X, B)`: `X` is a normal variety and
`B = ∑ bⱼ Bⱼ` an effective `ℝ`-divisor with all coefficients `0 < bⱼ < 1`, such that `K_X + B` is
`ℝ`-Cartier (for a canonical divisor `K_X`) and every exceptional divisor `E` over `X` has log
discrepancy `a(E, X, B) ≥ 1`. The empty boundary is allowed. -/
@[mmp "def_fourfold_real_canonical_pair"]
def IsRealCanonicalPair (B : RDivisor X) : Prop :=
  IsNormalVariety k sX ∧ (∀ P, B.coeff P ≠ 0 → 0 < B.coeff P ∧ B.coeff P < 1) ∧
    (∃ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n ∧
      RDivisor.IsRCartier (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + B)) ∧
    ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX n B E a → 1 ≤ a

/-- A real canonical pair with no coefficient one is *real terminal* if `a(E, X, B) > 1` for every
exceptional divisor `E` over `X`. -/
@[mmp "def_fourfold_real_terminal_pair"]
def IsRealTerminalPair (B : RDivisor X) : Prop :=
  IsRealCanonicalPair sX B ∧ ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional →
    MMP.Intersection.IsLogDiscrepancy sX n B E a → 1 < a

/-- For a dlt pair `(X, B)`, a *boundary stratum* is an irreducible component of a nonempty
intersection `⋂_{P ∈ J} P` of distinct prime components of `⌊B⌋` (the prime divisors with
coefficient one in `B`, since the coefficients of a dlt boundary are at most one). -/
@[mmp "def_mmp_dlt_strata"]
def IsDltStratum (B : QDivisor X) (S : Set X) : Prop :=
  MMP.Intersection.IsDltPair sX B ∧
    ∃ J : Finset (MMP.Mori.PrimeDivisor X), J.Nonempty ∧ (∀ P ∈ J, 1 ≤ B.coeff P) ∧
      (⋂ P ∈ J, (P.support : Set X)).Nonempty ∧
      Maximal (fun T : Set X => IsIrreducible T ∧ T ⊆ ⋂ P ∈ J, (P.support : Set X)) S

/-- The *minimal log discrepancy* `mld_x(X, B) = inf {a(v; X, B) : c_X(v) = V}` of a pair `(X, B)`
at a (not necessarily closed) point `x ∈ X` with closure `V`: the infimum, in `[-∞, ∞]`, of the
log discrepancies of the divisors over `X` whose centre on `X` is `V`. -/
@[mmp "def_oai4_bg_mld"]
def minimalLogDiscrepancy (B : QDivisor X) (x : X) : EReal :=
  sInf {t : EReal | ∃ (n : ℕ) (D : DivisorOver k sX) (a : ℝ),
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a ∧
      (D.center : Set X) = closure {x} ∧ t = a}

end MMP.Fourfold

namespace MMP.Fourfold

/-- The *hyperstandard set* of a finite set `I ⊆ (0, 1] ∩ ℚ` containing `1`: the numbers in
`[0, 1]` of the form `1 - 1/m + ∑_{b ∈ I} r_b b / m` with `m ≥ 1` and all `r_b` nonnegative
integers. The definition is made for every finite set `I` of rationals. -/
@[mmp "def_mmp_hyperstandard_coefficients"]
def hyperstandardSet (I : Finset ℚ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ m : ℕ, 1 ≤ m ∧ ∃ r : ℚ → ℕ,
    x = 1 - 1 / (m : ℝ) + ∑ b ∈ I, (r b : ℝ) * (b : ℝ) / (m : ℝ)}

end MMP.Fourfold
