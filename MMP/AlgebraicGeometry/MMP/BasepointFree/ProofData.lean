module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform

/-!
# The data of the basepoint-free, non-vanishing and rationality theorems

This file records the hypotheses and the auxiliary data of the proofs of the basepoint-free
theorem, the non-vanishing theorem and the rationality theorem of Kollár–Mori.

A *basepoint-free datum* `(X, Δ, D, a)` is a proper klt pair `(X, Δ)` with `Δ` effective, a nef
Cartier divisor `D` and `a > 0` with `aD - K_X - Δ` nef and big. For `m ≥ 0` with
`H⁰(X, mD) ≠ 0`, an *`m`-adapted resolution* is a log resolution `f : Y → X` with `Y` projective,
distinct prime divisors `F_j` of `Y` forming an snc divisor containing `Ex(f) ∪ f⁻¹(Supp Δ)`,
with `K_Y ≡ f^*(K_X + Δ) + ∑ a_j F_j`, rationals `0 < p_j < 1 + a_j` with
`f^*(aD - K_X - Δ) - ∑ p_j F_j` ample, and integers `r_j ≥ 0` with
`f^*|mD| = |L| + ∑ r_j F_j`, `|L|` basepoint free. A *tie-breaker* is a pair `(j', c)` such that
`-c r_j + a_j - p_j` attains its minimum `-1` exactly at `j = j'`; the *test boundary* is
`A = ∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j` and the *test divisor* is
`N(b, c) = b f^*D - K_Y + ∑_j (-c r_j + a_j - p_j) F_j`.

A *non-vanishing datum* `(X, D, G, a)` is a proper variety, a nef Cartier divisor `D`, a
`ℚ`-divisor `G` with `(X, -G)` klt and `a > 0` with `aD + G - K_X` nef and big; it has the
*non-vanishing property* if `H⁰(X, mD + ⌈G⌉) ≠ 0` for all large `m`. It is *smooth* if `X` is
smooth and projective, `Supp G` is an snc divisor and `aD + G - K_X` is ample. Adapted
resolutions, tie-breakers, test boundaries and test divisors are defined as for the
basepoint-free theorem, with a divisor `M ∼_ℚ qD + G - K_X` of high multiplicity at a point `x`.

A *rationality datum* `(X, Δ, a, H)` is a proper klt pair `(X, Δ)` with `Δ` effective and
`K_X + Δ` not nef, an integer `a > 0` with `a(K_X + Δ)` Cartier, and a nef and big Cartier
divisor `H`. Its *strip base loci* are `L(p, q) = Bs|pH + qa(K_X + Δ)|`; a closed subset `Z` is
a *stable base locus of the `(r, ε)`-strip* if `L(p, q) = Z` for all large `(p, q)` with
`0 < aq - rp < ε`, and `I(Z)` is the set of `(p, q)` with `0 < aq - rp < 1` and `L(p, q) = Z`.
For `(p, q)` with `p, q > 0` a `(p, q)`-adapted resolution, its tie-breaker `(j₀, c)`, the test
boundary `A'` and the test divisors `N(p', q') = f^*(p'H + q'a(K_X + Δ)) + A' - F_{j₀} - K_Y`
are defined in the same way.

## Main definitions

* `MMP.Mori.IsBasepointFreeDatum`, `MMP.Mori.IsBasepointFreeAdaptedResolution`,
  `MMP.Mori.IsBasepointFreeTieBreaker`: the data of the basepoint-free theorem.
* `MMP.Mori.IsNonvanishingDatum`, `MMP.Mori.HasNonvanishingProperty`,
  `MMP.Mori.IsSmoothNonvanishingDatum`, `MMP.Mori.IsNonvanishingAdaptedResolution`,
  `MMP.Mori.IsNonvanishingTieBreaker`: the data of the non-vanishing theorem.
* `MMP.Mori.IsRationalityDatum`, `MMP.Mori.stripBaseLocus`, `MMP.Mori.IsStableStripBaseLocus`,
  `MMP.Mori.stripIndexSet`, `MMP.Mori.IsStripAdaptedResolution`, `MMP.Mori.IsStripTieBreaker`,
  `MMP.Mori.IsStripTestDivisor`: the data of the rationality theorem.
* `MMP.Mori.tieBreakerBoundary`: the test boundary `∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j`, common
  to the three proofs.
* `MMP.Mori.IsTieBreakerTestDivisor`: the test divisor `N(b, c)` of the basepoint-free and of the
  non-vanishing theorem.

## Implementation notes

The finitely many prime divisors `F_j` of `Y` are an injective family `F : Fin s → PrimeDivisor Y`
(`Fin (s + 1)`, indexed from `0`, for the non-vanishing theorem), and `∑_j c_j F_j` is
`∑ j, Finsupp.single (F j) (c j)`.

As in `MMP.Mori.IsKltPair`, the canonical divisor `K` of `X` and the dimension `n` are explicit
arguments; the klt condition makes `K` a canonical divisor of dimension `n`, so `n = dim X`. The
canonical divisor `K_Y` of `Y` in a test divisor is an explicit argument, asserted to be a
canonical divisor of dimension `n`. The standing instances on `X` (integral, locally Noetherian,
normal, quasi-compact over `k`, compact) and on `Y` (locally Noetherian, normal, compact) are
consequences of the varieties being normal and proper, respectively smooth and projective.

Pull-backs are relational (`MMP.Mori.Divisor.IsPullback`, `MMP.Mori.QDivisor.IsPullback`):
"`f^*B` has property `P`" is encoded throughout as the existence of a pull-back `B'` of `B` along
`f` (with the condition that `f` maps no generic point of `Y` into `Supp B`) with property `P`.
For a `ℚ`-Cartier `B` the pull-back exists and is unique
(`MMP.Mori.QDivisor.IsQCartier.existsUnique_isPullback`).

The relation `K_Y ≡ f^*(K_X + Δ) + ∑ a_j F_j` is encoded, as in the source, by `-∑ a_j F_j` being
the crepant boundary of `(X, Δ)` on `Y` (`MMP.Mori.IsCrepantBoundary`), that is, `a_j` is the
discrepancy `a(F_j, X, Δ)` and every prime divisor of `Y` off the `F_j` has discrepancy `0`.

That the sections `f^*σ` of `𝒪_Y(f^*B)` vanish along `∑ r_j F_j` and that the `f^*σ / s` generate
`𝒪_Y(f^*B - ∑ r_j F_j)` is encoded by divisors of zeros: `f^*(σ)₀ ≥ ∑ r_j F_j` for every nonzero
section `σ` of `𝒪_X(B)`, and every point of `Y` lies outside `Supp(f^*(σ)₀ - ∑ r_j F_j)` for some
`σ` (a section of an invertible sheaf generates it at `y` exactly when its divisor of zeros
misses `y`). Likewise `H⁰(X, B) ≠ 0` is the existence of a nonzero section.

An integral divisor `qa(K_X + Δ)`, for `a(K_X + Δ)` with integral coefficients, is
`q ⌊a(K_X + Δ)⌋` (`MMP.Mori.stripDivisor`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorems 3.3,
  3.4, 3.5 and 3.15, and their proofs in 3.2, 3.4 and 3.5
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]

/-! ### Test boundaries and test divisors -/

section TestDivisor

variable {Y : Scheme.{u}} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The test boundary** of a tie-breaker `(j', c)` of an adapted resolution with prime divisors
`F_j` and rationals `a_j, p_j, r_j`: the `ℚ`-divisor `A = ∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j`
on `Y`. In the non-vanishing theorem the `a_j` are called `b_j`. -/
@[mmp "def_km3a_bpf_test_boundary", mmp "def_km3a_nonvanishing_test_boundary",
  mmp "def_km3b_strip_test_boundary"]
def tieBreakerBoundary (F : ι → PrimeDivisor Y) (r a p : ι → ℚ) (j' : ι) (c : ℚ) : QDivisor Y :=
  ∑ j ∈ Finset.univ.erase j', Finsupp.single (F j) (-c * r j + a j - p j)

omit [IsIntegral X] [CompactSpace X] [QuasiCompact sX] [DecidableEq ι] in
/-- **The test divisor** `N(b, c) = b f^*D - K_Y + ∑_j (-c r_j + a_j - p_j) F_j` on `Y`, for a
morphism `f : Y ⟶ X`, a divisor `D` on `X`, prime divisors `F_j` of `Y` and rationals
`a_j, p_j, r_j` (the `a_j` are the `b_j` of the non-vanishing theorem): `N` is the test divisor
if `K_Y` is a canonical divisor of `Y` of dimension `n` and `N = b D' - K_Y + ∑_j (…) F_j` for a
pull-back `D' = f^*D`. -/
@[mmp "def_km3a_bpf_test_divisor", mmp "def_km3a_nonvanishing_test_divisor"]
def IsTieBreakerTestDivisor (n : ℕ) (D : Divisor X) [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) (KY : Divisor Y) (F : ι → PrimeDivisor Y) (r a p : ι → ℚ)
    (b c : ℚ) (N : QDivisor Y) : Prop :=
  KY.IsCanonicalDivisor (f ≫ sX) n ∧
    ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
      (D' : Divisor Y), D.IsPullback f hB D' ∧
      N = b • Divisor.toQDivisor D' - Divisor.toQDivisor KY +
        ∑ j, Finsupp.single (F j) (-c * r j + a j - p j)

end TestDivisor

/-! ### The basepoint-free theorem -/

section BasepointFree

/-- **A basepoint-free datum** `(X, Δ, D, a)`: `X` is a proper normal variety over `k`, `(X, Δ)`
is a klt pair (with canonical divisor `K` of dimension `n`) with `Δ` effective, `D` is a nef
Cartier divisor on `X` and `a > 0` is a rational number such that the `ℚ`-divisor
`aD - K_X - Δ` is `ℚ`-Cartier, nef and big. -/
@[mmp "def_km3a_bpf_datum"]
structure IsBasepointFreeDatum (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (D : Divisor X)
    (a : ℚ) : Prop where
  isProperVariety : IsProperVariety k sX
  isKltPair : IsKltPair sX n K Δ
  isEffective : Δ.IsEffective
  /-- `D` is a Cartier divisor (also part of `Divisor.IsNef`). -/
  isCartier : D.IsCartier
  isNef : D.IsNef k sX
  pos : 0 < a
  /-- `aD - K_X - Δ` is `ℚ`-Cartier. -/
  isQCartier_sub : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsQCartier
  /-- `aD - K_X - Δ` is nef. -/
  isNef_sub : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsNef k sX
  /-- `aD - K_X - Δ` is big. -/
  isBig_sub : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsBig k sX

/-- **An `m`-adapted resolution** `(f; F_1, …, F_s; a_•; p_•; r_•)` of a basepoint-free datum
`(X, Δ, D, a)`, for an integer `m ≥ 0` with `H⁰(X, mD) ≠ 0`:
(i) `f : Y ⟶ X` is a log resolution of `(X, Δ)` with `Y` projective;
(ii) `F_1, …, F_s` are distinct prime divisors of `Y`, `∑_j F_j` is an snc divisor and
`Ex(f) ∪ f⁻¹(Supp Δ) ⊆ ⋃_j F_j`;
(iii) the crepant boundary of `(X, Δ)` on `Y` is `-∑_j a_j F_j`, i.e.
`K_Y ≡ f^*(K_X + Δ) + ∑_j a_j F_j`;
(iv) `0 < p_j < 1 + a_j` and `f^*(aD - K_X - Δ) - ∑_j p_j F_j` is ample (for a pull-back
`f^*(aD - K_X - Δ)`);
(v) `f^*(σ)₀ ≥ ∑_j r_j F_j` for every nonzero `σ ∈ H⁰(X, mD)`, and every `y ∈ Y` lies outside
`Supp (f^*(σ)₀ - ∑_j r_j F_j)` for some such `σ` (for pull-backs `f^*(σ)₀`). -/
@[mmp "def_km3a_bpf_adapted_resolution"]
structure IsBasepointFreeAdaptedResolution (n : ℕ) (K : Divisor X) (Δ : QDivisor X)
    (D : Divisor X) (a : ℚ) (m : ℕ) {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (f : Y ⟶ X) {s : ℕ} (F : Fin s → PrimeDivisor Y) (aj pj : Fin s → ℚ)
    (rj : Fin s → ℕ) : Prop extends IsBasepointFreeDatum sX n K Δ D a where
  exists_section_ne_zero : ∃ σ : (m • D).divisorialSubmodule ⊤, σ ≠ 0
  isLogResolution : IsLogResolution sX (QDivisor.toRDivisor Δ) f
  isProjectiveVariety : IsProjectiveVariety k (f ≫ sX)
  injective : Function.Injective F
  isSNC : DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ j, Finsupp.single (F j) (1 : ℤ))
  subset_iUnion : (exceptionalSet f : Set Y) ∪ f ⁻¹' (Δ.supp : Set X) ⊆ ⋃ j, (F j).support
  isCrepantBoundary : ∃ hY : IsNormalVariety k (f ≫ sX),
    IsCrepantBoundary sX n K Δ f hY isLogResolution.isBirationalMorphism
      (-∑ j, Finsupp.single (F j) (aj j))
  pos_p : ∀ j, 0 < pj j
  lt_one_add : ∀ j, pj j < 1 + aj j
  isAmple : ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).supp) (B' : QDivisor Y),
    (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsPullback f hB B' ∧
      (B' - ∑ j, Finsupp.single (F j) (pj j)).IsAmple
  le_zeroDivisor : ∀ (σ : (m • D).divisorialSubmodule ⊤) (hσ : σ ≠ 0),
    ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        ((m • D).zeroDivisor σ hσ).supp) (Z' : Divisor Y),
      ((m • D).zeroDivisor σ hσ).IsPullback f hB Z' ∧
        ∑ j, Finsupp.single (F j) (rj j : ℤ) ≤ Z'
  exists_notMem_supp : ∀ y : Y, ∃ (σ : (m • D).divisorialSubmodule ⊤) (hσ : σ ≠ 0)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        ((m • D).zeroDivisor σ hσ).supp) (Z' : Divisor Y),
      ((m • D).zeroDivisor σ hσ).IsPullback f hB Z' ∧
        y ∉ ((Z' - ∑ j, Finsupp.single (F j) (rj j : ℤ)).supp : Set Y)

/-- **A tie-breaker** `(j', c)` of an `m`-adapted resolution `(f; F_•; a_•; p_•; r_•)` of a
basepoint-free datum: `c > 0` is a rational number with `r_{j'} > 0`,
`-c r_{j'} + a_{j'} - p_{j'} = -1` and `-c r_j + a_j - p_j > -1` for every `j ≠ j'`, so that
`min_j (-c r_j + a_j - p_j) = -1` is attained only at `j'`. -/
@[mmp "def_km3a_bpf_tie_breaker"]
structure IsBasepointFreeTieBreaker (n : ℕ) (K : Divisor X) (Δ : QDivisor X)
    (D : Divisor X) (a : ℚ) (m : ℕ) {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (f : Y ⟶ X) {s : ℕ} (F : Fin s → PrimeDivisor Y) (aj pj : Fin s → ℚ)
    (rj : Fin s → ℕ) (j' : Fin s) (c : ℚ) : Prop
    extends IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj where
  pos_c : 0 < c
  pos_r : 0 < rj j'
  eq_neg_one : -c * rj j' + aj j' - pj j' = -1
  neg_one_lt : ∀ j, j ≠ j' → -1 < -c * rj j + aj j - pj j

end BasepointFree

/-! ### The non-vanishing theorem -/

section Nonvanishing

/-- **A non-vanishing datum** `(X, D, G, a)`: `X` is a proper variety over `k`, `D` is a nef
Cartier divisor on `X`, `G` is a `ℚ`-divisor such that `(X, -G)` is klt (with canonical divisor
`K` of dimension `n = dim X`; in particular `X` is normal), and `a > 0` is a rational number such
that `aD + G - K_X` is `ℚ`-Cartier, nef and big. Its dimension is `n`. -/
@[mmp "def_km3a_nonvanishing_datum"]
structure IsNonvanishingDatum (n : ℕ) (K : Divisor X) (D : Divisor X) (G : QDivisor X)
    (a : ℚ) : Prop where
  isProperVariety : IsProperVariety k sX
  /-- `D` is a Cartier divisor (also part of `Divisor.IsNef`). -/
  isCartier : D.IsCartier
  isNef : D.IsNef k sX
  isKltPair : IsKltPair sX n K (-G)
  pos : 0 < a
  /-- `aD + G - K_X` is `ℚ`-Cartier. -/
  isQCartier_add : (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K).IsQCartier
  /-- `aD + G - K_X` is nef. -/
  isNef_add : (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K).IsNef k sX
  /-- `aD + G - K_X` is big. -/
  isBig_add : (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K).IsBig k sX

omit [QuasiCompact sX] in
/-- **The non-vanishing property** of `(X, D, G)`, the conclusion of the non-vanishing theorem
for a non-vanishing datum `(X, D, G, a)`: there is `m₀` such that `H⁰(X, mD + ⌈G⌉) ≠ 0` for
every integer `m ≥ m₀`. -/
@[mmp "def_km3a_nonvanishing_property"]
def HasNonvanishingProperty (D : Divisor X) (G : QDivisor X) : Prop :=
  ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∃ σ : (m • D + G.roundUp).divisorialSubmodule ⊤, σ ≠ 0

/-- **A smooth non-vanishing datum**: a non-vanishing datum `(X, D, G, a)` such that `X` is
smooth and projective, `Supp G` is an snc divisor and `aD + G - K_X` is ample. -/
@[mmp "def_km3a_smooth_nonvanishing_datum"]
structure IsSmoothNonvanishingDatum (n : ℕ) (K : Divisor X) (D : Divisor X) (G : QDivisor X)
    (a : ℚ) : Prop extends IsNonvanishingDatum sX n K D G a where
  isSmoothScheme : IsSmoothScheme sX
  isProjectiveVariety : IsProjectiveVariety k sX
  isSNCSubset : IsSNCSubset sX G.supp
  /-- `aD + G - K_X` is ample. -/
  isAmple : (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K).IsAmple

/-- **An adapted resolution** `(x, q, e, M; f; F_0, …, F_s; b_•; p_•; r_•)` of a smooth
non-vanishing datum `(X, D, G, a)` of dimension `d = n ≥ 1`:
(i) `x ∈ X \ Supp G` is a closed point, `q ≥ a` and `e ≥ 1` are integers with `eG` integral,
and `M` is an effective `ℚ`-divisor with `eM` integral, `eM ∼ e(qD + G - K_X)` and
`mult_x M > 2d`;
(ii) `f : Y ⟶ X` is a log resolution of `(X, G + M)` with `Y` projective;
(iii) `F_0, …, F_s` are distinct prime divisors of `Y`, `∑_j F_j` is an snc divisor and
`Ex(f) ∪ f⁻¹(Supp (G + M)) ⊆ ⋃_j F_j`;
(iv) the crepant boundary of `(X, -G)` on `Y` is `-∑_j b_j F_j`, i.e.
`K_Y + f^*G ≡ f^*K_X + ∑_j b_j F_j`;
(v) `0 < p_j < 1 + b_j` for all `j` and `½ f^*(aD + G - K_X) - ∑_j p_j F_j` is ample (for a
pull-back `f^*(aD + G - K_X)`);
(vi) `r_j ≥ 0` and `f^*M = ∑_j r_j F_j`;
(vii) `b_0 ≤ d - 1` and `r_0 ≥ mult_x M`. -/
@[mmp "def_km3a_nonvanishing_adapted_resolution"]
structure IsNonvanishingAdaptedResolution (n : ℕ) (K : Divisor X) (D : Divisor X)
    (G : QDivisor X) (a : ℚ) (x : X) (q e : ℤ) (M : QDivisor X) {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) {s : ℕ}
    (F : Fin (s + 1) → PrimeDivisor Y) (b p r : Fin (s + 1) → ℚ) : Prop
    extends IsSmoothNonvanishingDatum sX n K D G a where
  one_le_dim : 1 ≤ n
  isClosed_point : IsClosed ({x} : Set X)
  notMem_supp : x ∉ (G.supp : Set X)
  le_q : a ≤ q
  one_le_e : 1 ≤ e
  isIntegral_smul : ∃ G' : Divisor X, Divisor.toQDivisor G' = e • G
  isEffective_M : M.IsEffective
  linearlyEquivalent : ∃ M' G' : Divisor X, Divisor.toQDivisor M' = e • M ∧
    Divisor.toQDivisor G' = e • G ∧ M'.LinearlyEquivalent ((e * q) • D + G' - e • K)
  multiplicityAt_gt : (2 * n : ℚ) < M.multiplicityAt x
  isLogResolution : IsLogResolution sX (QDivisor.toRDivisor (G + M)) f
  isProjectiveVariety_source : IsProjectiveVariety k (f ≫ sX)
  injective : Function.Injective F
  isSNC : DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ j, Finsupp.single (F j) (1 : ℤ))
  subset_iUnion : (exceptionalSet f : Set Y) ∪ f ⁻¹' ((G + M).supp : Set X) ⊆ ⋃ j, (F j).support
  isCrepantBoundary : ∃ hY : IsNormalVariety k (f ≫ sX),
    IsCrepantBoundary sX n K (-G) f hY isLogResolution.isBirationalMorphism
      (-∑ j, Finsupp.single (F j) (b j))
  pos_p : ∀ j, 0 < p j
  lt_one_add : ∀ j, p j < 1 + b j
  isAmple_half : ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K).supp) (B' : QDivisor Y),
    (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K).IsPullback f hB B' ∧
      ((1 / 2 : ℚ) • B' - ∑ j, Finsupp.single (F j) (p j)).IsAmple
  nonneg_r : ∀ j, 0 ≤ r j
  isPullback_M : ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp,
    M.IsPullback f hB (∑ j, Finsupp.single (F j) (r j))
  b_zero_le : b 0 ≤ (n : ℚ) - 1
  multiplicityAt_le : M.multiplicityAt x ≤ r 0

/-- **A tie-breaker** `(j', c)` of an adapted resolution
`(x, q, e, M; f; F_•; b_•; p_•; r_•)` of a smooth non-vanishing datum: `0 < c < ½` is a rational
number with `r_{j'} > 0`, `-c r_{j'} + b_{j'} - p_{j'} = -1` and `-c r_j + b_j - p_j > -1` for
every `j ≠ j'`. -/
@[mmp "def_km3a_nonvanishing_tie_breaker"]
structure IsNonvanishingTieBreaker (n : ℕ) (K : Divisor X) (D : Divisor X)
    (G : QDivisor X) (a : ℚ) (x : X) (q e : ℤ) (M : QDivisor X) {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) {s : ℕ}
    (F : Fin (s + 1) → PrimeDivisor Y) (b p r : Fin (s + 1) → ℚ) (j' : Fin (s + 1)) (c : ℚ) :
    Prop extends IsNonvanishingAdaptedResolution sX n K D G a x q e M f F b p r where
  pos_c : 0 < c
  lt_half : c < 1 / 2
  pos_r : 0 < r j'
  eq_neg_one : -c * r j' + b j' - p j' = -1
  neg_one_lt : ∀ j, j ≠ j' → -1 < -c * r j + b j - p j

end Nonvanishing

/-! ### The rationality theorem -/

section Rationality

/-- **A rationality datum** `(X, Δ, a, H)`: `X` is a proper normal variety over `k`, `(X, Δ)` is
a klt pair (with canonical divisor `K` of dimension `n = dim X`) with `Δ` effective such that
`K_X + Δ` is not nef, `a > 0` is an integer such that `a(K_X + Δ)` is Cartier (in particular has
integral coefficients), and `H` is a nef and big Cartier divisor on `X`. Its dimension is `n`. -/
@[mmp "def_km3b_rationality_datum"]
structure IsRationalityDatum (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (a : ℤ) (H : Divisor X) :
    Prop where
  isProperVariety : IsProperVariety k sX
  isKltPair : IsKltPair sX n K Δ
  isEffective : Δ.IsEffective
  not_isNef : ¬ (Divisor.toQDivisor K + Δ).IsNef k sX
  pos : 0 < a
  /-- `a(K_X + Δ)` is a Cartier divisor. -/
  isCartierDivisor : (a • (Divisor.toQDivisor K + Δ)).IsCartierDivisor
  /-- `H` is a Cartier divisor (also part of `Divisor.IsNef`). -/
  isCartier_H : H.IsCartier
  isNef_H : H.IsNef k sX
  isBig_H : H.IsBig k sX

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] in
/-- The divisor `pH + qa(K_X + Δ)`, where `a(K_X + Δ)` (integral for a rationality datum) is read
as the divisor `⌊a(K_X + Δ)⌋`. -/
def stripDivisor (K : Divisor X) (Δ : QDivisor X) (a : ℤ) (H : Divisor X) (p q : ℤ) :
    Divisor X :=
  p • H + q • (a • (Divisor.toQDivisor K + Δ)).roundDown

omit [QuasiCompact sX] in
/-- **The strip base locus** `L(p, q) ⊆ X` of a rationality datum `(X, Δ, a, H)` and
`(p, q) ∈ ℤ²`: the closed subset of the points at which every section of
`𝒪_X(pH + qa(K_X + Δ))` vanishes, the base locus `Bs|pH + qa(K_X + Δ)|` (with its reduced
structure); it is `X` when `H⁰(X, 𝒪_X(pH + qa(K_X + Δ))) = 0`. -/
@[mmp "def_km3b_strip_base_locus"]
def stripBaseLocus (K : Divisor X) (Δ : QDivisor X) (a : ℤ) (H : Divisor X) (p q : ℤ) :
    Closeds X :=
  (stripDivisor K Δ a H p q).baseLocus

omit [QuasiCompact sX] in
/-- **A stable base locus of the `(r, ε)`-strip**, for a rationality datum `(X, Δ, a, H)`,
`r ∈ ℝ` and `ε > 0`: a closed subset `Z ⊆ X` such that there is `N` with `L(p, q) = Z` for all
`(p, q) ∈ ℤ²` with `p, q ≥ N` and `0 < aq - rp < ε`. -/
@[mmp "def_km3b_stable_strip_base_locus"]
def IsStableStripBaseLocus (K : Divisor X) (Δ : QDivisor X) (a : ℤ) (H : Divisor X) (r ε : ℝ)
    (Z : Closeds X) : Prop :=
  ∃ N : ℤ, ∀ p q : ℤ, N ≤ p → N ≤ q → 0 < (a * q : ℝ) - r * p → (a * q : ℝ) - r * p < ε →
    stripBaseLocus K Δ a H p q = Z

omit [QuasiCompact sX] in
/-- **The index set** `I(Z) = {(p, q) ∈ ℤ² : 0 < aq - rp < 1, L(p, q) = Z}` of a closed subset
`Z ⊆ X`, for a rationality datum `(X, Δ, a, H)` and `r ∈ ℝ`. -/
@[mmp "def_km3b_strip_index_set"]
def stripIndexSet (K : Divisor X) (Δ : QDivisor X) (a : ℤ) (H : Divisor X) (r : ℝ)
    (Z : Closeds X) : Set (ℤ × ℤ) :=
  {pq | 0 < (a * pq.2 : ℝ) - r * pq.1 ∧ (a * pq.2 : ℝ) - r * pq.1 < 1 ∧
    stripBaseLocus K Δ a H pq.1 pq.2 = Z}

/-- **A `(p, q)`-adapted resolution** `(f; F_1, …, F_s; a_•; p_•; r_•)` of a rationality datum
`(X, Δ, a, H)`, for integers `p, q > 0`: `f : Y ⟶ X` is a log resolution of `(X, Δ)` with `Y`
projective, `F_1, …, F_s` are distinct prime divisors of `Y` with `F_1 + ⋯ + F_s` an snc divisor
containing every `f`-exceptional prime divisor and every component of `f⁻¹_* Δ`, and
(1) `K_Y = f^*(K_X + Δ) + ∑_j a_j F_j` (the crepant boundary of `(X, Δ)` on `Y` is
`-∑_j a_j F_j`) and `a_j > -1`;
(2) `p_j > 0` and `f^*(pH + (qa - 1)(K_X + Δ)) - ∑_j p_j F_j` is ample (for a pull-back
`f^*(pH + (qa - 1)(K_X + Δ))`);
(3) the integers `r_j ≥ 0` are such that for every section `σ` of `𝒪_X(pH + qa(K_X + Δ))`,
`f^*σ` vanishes along `∑_j r_j F_j`, and the `f^*σ / s` generate
`𝒪_Y(f^*(pH + qa(K_X + Δ)) - ∑_j r_j F_j)` at every point: `f^*(σ)₀ ≥ ∑_j r_j F_j` for every
nonzero `σ`, and every `y ∈ Y` lies outside `Supp (f^*(σ)₀ - ∑_j r_j F_j)` for some `σ`. -/
@[mmp "def_km3b_strip_adapted_resolution"]
structure IsStripAdaptedResolution (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (a : ℤ)
    (H : Divisor X) (p q : ℤ) {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (f : Y ⟶ X) {s : ℕ} (F : Fin s → PrimeDivisor Y) (aj pj : Fin s → ℚ)
    (rj : Fin s → ℕ) : Prop extends IsRationalityDatum sX n K Δ a H where
  pos_p : 0 < p
  pos_q : 0 < q
  isLogResolution : IsLogResolution sX (QDivisor.toRDivisor Δ) f
  isProjectiveVariety : IsProjectiveVariety k (f ≫ sX)
  injective : Function.Injective F
  isSNC : DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ j, Finsupp.single (F j) (1 : ℤ))
  mem_range_of_isExceptional : ∀ E : PrimeDivisor Y,
    RationalMap.IsExceptional f.toRationalMap E → E ∈ Set.range F
  mem_range_of_inverseTransform : ∀ E : PrimeDivisor Y,
    (inverseTransformDivisor f Δ).coeff E ≠ 0 → E ∈ Set.range F
  isCrepantBoundary : ∃ hY : IsNormalVariety k (f ≫ sX),
    IsCrepantBoundary sX n K Δ f hY isLogResolution.isBirationalMorphism
      (-∑ j, Finsupp.single (F j) (aj j))
  neg_one_lt : ∀ j, -1 < aj j
  pos_p' : ∀ j, 0 < pj j
  isAmple : ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (p • Divisor.toQDivisor H + (q * a - 1) • (Divisor.toQDivisor K + Δ)).supp)
      (B' : QDivisor Y),
    (p • Divisor.toQDivisor H + (q * a - 1) • (Divisor.toQDivisor K + Δ)).IsPullback f hB B' ∧
      (B' - ∑ j, Finsupp.single (F j) (pj j)).IsAmple
  le_zeroDivisor : ∀ (σ : (stripDivisor K Δ a H p q).divisorialSubmodule ⊤) (hσ : σ ≠ 0),
    ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        ((stripDivisor K Δ a H p q).zeroDivisor σ hσ).supp) (Z' : Divisor Y),
      ((stripDivisor K Δ a H p q).zeroDivisor σ hσ).IsPullback f hB Z' ∧
        ∑ j, Finsupp.single (F j) (rj j : ℤ) ≤ Z'
  exists_notMem_supp : ∀ y : Y,
    ∃ (σ : (stripDivisor K Δ a H p q).divisorialSubmodule ⊤) (hσ : σ ≠ 0)
      (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        ((stripDivisor K Δ a H p q).zeroDivisor σ hσ).supp) (Z' : Divisor Y),
      ((stripDivisor K Δ a H p q).zeroDivisor σ hσ).IsPullback f hB Z' ∧
        y ∉ ((Z' - ∑ j, Finsupp.single (F j) (rj j : ℤ)).supp : Set Y)

/-- **A tie-breaker** `(j₀, c)` of a `(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` of a
rationality datum: `p_j < 1 + a_j` for every `j`, `r_{j₀} > 0`,
`c = (1 + a_{j₀} - p_{j₀}) / r_{j₀}`, and `c < (1 + a_j - p_j) / r_j` for every `j ≠ j₀` with
`r_j > 0`. -/
@[mmp "def_km3b_strip_tie_breaker"]
structure IsStripTieBreaker (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (a : ℤ)
    (H : Divisor X) (p q : ℤ) {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (f : Y ⟶ X) {s : ℕ} (F : Fin s → PrimeDivisor Y) (aj pj : Fin s → ℚ)
    (rj : Fin s → ℕ) (j₀ : Fin s) (c : ℚ) : Prop
    extends IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj where
  lt_one_add : ∀ j, pj j < 1 + aj j
  pos_r : 0 < rj j₀
  eq_div : c = (1 + aj j₀ - pj j₀) / rj j₀
  lt_div : ∀ j, j ≠ j₀ → 0 < rj j → c < (1 + aj j - pj j) / rj j

omit [IsIntegral X] [CompactSpace X] [QuasiCompact sX] in
/-- **The test divisor** `N(p', q') = f^*(p'H + q'a(K_X + Δ)) + A' - F_{j₀} - K_Y` on `Y`, for a
tie-breaker `(j₀, c)` of a `(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` of a rationality
datum `(X, Δ, a, H)`, with `A'` the test boundary (`MMP.Mori.tieBreakerBoundary`) and
`(p', q') ∈ ℤ²`: `N` is the test divisor if `K_Y` is a canonical divisor of `Y` of dimension `n`
and `N = B' + A' - F_{j₀} - K_Y` for a pull-back `B' = f^*(p'H + q'a(K_X + Δ))`. -/
@[mmp "def_km3b_strip_test_divisor"]
def IsStripTestDivisor (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (a : ℤ) (H : Divisor X)
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) (KY : Divisor Y) {s : ℕ}
    (F : Fin s → PrimeDivisor Y) (aj pj : Fin s → ℚ) (rj : Fin s → ℕ) (j₀ : Fin s) (c : ℚ)
    (p' q' : ℤ) (N : QDivisor Y) : Prop :=
  KY.IsCanonicalDivisor (f ≫ sX) n ∧
    ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).supp)
      (B' : QDivisor Y),
      (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).IsPullback f hB B' ∧
      N = B' + tieBreakerBoundary F (fun j => (rj j : ℚ)) aj pj j₀ c -
        Finsupp.single (F j₀) 1 - Divisor.toQDivisor KY

end Rationality

end MMP.Mori
