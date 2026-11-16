module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import Mathlib.Data.EReal.Basic

/-!
# Discrepancies of divisors over a pair

Let `X` be a normal variety of dimension `n` over a field `k`, with canonical divisor `K_X`, and
let `Δ` be a `ℚ`-divisor on `X` such that `(X, Δ)` is a pair. For a divisor `(Y, f, E)` over `X`
(a birational morphism `f : Y ⟶ X` from a normal variety and a prime divisor `E ⊆ Y`), a rational
number `a` is *the discrepancy* `a(E, X, Δ)` of `E` if there are an integer `m > 0` such that
`m(K_X + Δ)` is Cartier, an open `U ⊆ X` containing `f(η_E)` and a rational `m`-canonical form
`τ` generating `𝒪_X(m(K_X + Δ))` on `U`, with `m · a = ord_E(f^*τ)`. For `Δ = 0` and `E`
exceptional this is the discrepancy `a(E, X)` of Kollár–Mori 2.22, with `τ` a local generator of
`𝒪_X(mK_X)`.

A `ℚ`-divisor `Δ_Y` on `Y` is *the crepant boundary* of `(X, Δ)` on `Y` if
`coeff_F(Δ_Y) = -a(F, X, Δ)` for every prime divisor `F` of `Y` (Kollár–Mori write
`K_Y ≡ f^*(K_X + Δ) + A` with `A = -Δ_Y`). The *discrepancy of the pair* is
`discrep(X, Δ) = inf {a(E, X, Δ) | E exceptional over X}`, with `inf ∅ = +∞`.

## Main definitions

* `MMP.Mori.pullbackRationalPluriForms`: the pull-back `f^*τ` of rational pluricanonical forms
  along a dominant morphism of integral schemes over `k`.
* `MMP.Mori.DivisorOver.ordPullback`: `ord_E(f^*τ)` for a divisor `(Y, f, E)` over `X`.
* `MMP.Mori.IsDiscrepancyNoBoundary`: `a = a(E, X)`, for `E` exceptional over `X`.
* `MMP.Mori.IsDiscrepancy`: `a = a(E, X, Δ)`.
* `MMP.Mori.IsCrepantBoundary`: `Δ_Y` is the crepant boundary of `(X, Δ)` on `Y`.
* `MMP.Mori.discrep`: `discrep(X, Δ)`, an extended real number.

## Main results

* `MMP.Mori.isDiscrepancyNoBoundary_iff`: for `Δ = 0` and `E` exceptional the two definitions
  agree.
* `MMP.Mori.IsDiscrepancy.isPair`: a `ℚ`-divisor admitting a discrepancy is the boundary of a
  pair.
* `MMP.Mori.discrep_le`, `MMP.Mori.le_discrep_iff`, `MMP.Mori.discrep_eq_top`: `discrep(X, Δ)`
  is the greatest lower bound of the discrepancies of exceptional divisors, and `+∞` when there
  are none.

## Implementation notes

Kollár and Mori fix a canonical divisor `K_X`. Here it is an explicit argument `K` of the
definitions, with its dimension `n`; the predicates assert that `X` is a normal variety and that
`K` is a canonical divisor of dimension `n` (`MMP.Mori.Divisor.IsCanonicalDivisor`), so they are
false for any other `K` or `n`, and the forms `τ` are of degree `n = dim X`. Only the condition
that `m(K + Δ)` be Cartier depends on `K`, and only through its linear equivalence class
(`MMP.Mori.Divisor.IsCartier.of_linearlyEquivalent`).

"`a` is the discrepancy" is a predicate on `a`. That the discrepancy is unique, when it exists,
needs that the order of a pull-back is multiplicative in the form and that two local generators
differ by a unit at `f(η_E)` (for which `X` normal is used); no value `a(E, X, Δ)` is chosen
here. Accordingly `Δ_Y` is the crepant boundary when `-coeff_F(Δ_Y)` *is the discrepancy* of
every prime divisor `F` of `Y`.

The infimum `discrep(X, Δ)` is taken in the extended reals `EReal`, a complete lattice. The
source takes it in `ℚ ∪ {±∞}`, which is not complete; whenever a set of rationals has an infimum
in `ℚ ∪ {±∞}`, it is its infimum in `EReal`, since a rational strictly between the two would be a
lower bound in `ℚ`. That the value lies in `ℚ ∪ {-∞, +∞}` is a theorem about pairs, not part of
the definition.

The pull-back of forms is `MMP.Mori.pullbackForms` along the extension of function fields
`AlgebraicGeometry.functionFieldMap f`, and the variety structure of `Y` is `f ≫ s_X`, as in
`MMP.Mori.DivisorOver`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.22, 2.25,
  2.26, 2.28
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

section Pullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
  [IsIntegral X] [IsIntegral Y] [IsDominant f]

/-- The algebra structure `k(X) → k(Y)` of the extension of function fields of a dominant
morphism `f : Y ⟶ X` of integral schemes. -/
@[instance_reducible]
def functionFieldMapAlgebra : Algebra X.functionField Y.functionField :=
  (functionFieldMap f).toAlgebra

/-- The extension of function fields of a dominant morphism `f : Y ⟶ X` of `k`-schemes is
`k`-linear, for the `k`-structure `f ≫ s_X` of `Y`. -/
theorem isScalarTower_functionFieldMap :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    IsScalarTower k X.functionField Y.functionField := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  refine IsScalarTower.of_algebraMap_eq' ?_
  have hs : f (genericPoint Y) ⤳ genericPoint X := by rw [map_genericPoint_of_isDominant f]
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
        Y.presheaf.germ ⊤ (genericPoint Y) (Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) (Opens.mem_top _)) ≫
        (X.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint Y)) := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    rfl
  exact congrArg CommRingCat.Hom.hom h

variable {d : ℕ} {m : ℤ}

/-- The pull-back `f^*τ ∈ ω^{⊗m}_{k(Y)}` of a rational `m`-canonical form `τ` on `X` along a
dominant morphism `f : Y ⟶ X` of integral schemes over `k`, `Y` having structure morphism
`f ≫ s_X`: the pull-back of forms along the extension of function fields `f^* : k(X) → k(Y)`. -/
def pullbackRationalPluriForms (τ : RationalPluriForms sX d m) :
    RationalPluriForms (f ≫ sX) d m :=
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sX f
  pullbackForms (K := X.functionField) (K' := Y.functionField) m τ

end Pullback

/-! ### The order of the pull-back of a form along a divisor over `X` -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

namespace DivisorOver

variable {sX} [IsIntegral X] {d : ℕ} {m : ℤ}

/-- The order `ord_E(f^*τ)` along `E` of the pull-back of a rational `m`-canonical form `τ` on
`X`, for a divisor `(Y, f, E)` over `X`. -/
def ordPullback (D : DivisorOver k sX) (τ : RationalPluriForms sX d m) : ℤ :=
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  D.E.ordForm (pullbackRationalPluriForms sX D.f τ)

end DivisorOver

/-! ### Discrepancies -/

section Discrepancy

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The discrepancy of an exceptional divisor, without boundary.** For a normal variety `X`
with canonical divisor `K` of dimension `n` and an exceptional divisor `(Y, f, E)` over `X`, a
rational number `a` is *the discrepancy* `a(E, X)` if there are an integer `m > 0` with `mK`
Cartier, an open `U ∋ f(η_E)` and a nonzero rational `m`-canonical form `σ` on `X` with
`ord_Γ(σ) = 0` for every prime divisor `Γ` meeting `U` (a local generator of `𝒪_X(mK_X)` on
`U`), such that `m · a = ord_E(f^*σ)`. -/
@[mmp "def_km2b_discrepancy_no_boundary"]
def IsDiscrepancyNoBoundary (n : ℕ) (K : Divisor X) (D : DivisorOver k sX) (a : ℚ) : Prop :=
  IsNormalVariety k sX ∧ K.IsCanonicalDivisor sX n ∧ D.IsExceptional ∧
    ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • K).IsCartier ∧
      ∃ U : X.Opens, D.f D.E.genericPoint ∈ U ∧
        ∃ σ : RationalPluriForms sX n m, σ ≠ 0 ∧
          (∀ Γ : PrimeDivisor X, (Γ.support ∩ U).Nonempty → Γ.ordForm σ = 0) ∧
          (m : ℚ) * a = D.ordPullback σ

/-- **The discrepancy of a divisor over a pair.** For a normal variety `X` with canonical divisor
`K` of dimension `n`, a `ℚ`-divisor `Δ` and a divisor `(Y, f, E)` over `X`, a rational number
`a` is *the discrepancy* `a(E, X, Δ)` if there are an integer `m > 0` with `m(K + Δ)` Cartier
(a divisor, Cartier), an open `U ∋ f(η_E)` and a form `τ` generating `𝒪_X(m(K + Δ))` on `U`,
such that `m · a = ord_E(f^*τ)`. -/
@[mmp "def_km2b_discrepancy"]
def IsDiscrepancy (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (D : DivisorOver k sX) (a : ℚ) :
    Prop :=
  IsNormalVariety k sX ∧ K.IsCanonicalDivisor sX n ∧
    ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor ∧
      ∃ U : X.Opens, D.f D.E.genericPoint ∈ U ∧
        ∃ τ : RationalPluriForms sX n m, GeneratesOn Δ m U τ ∧ (m : ℚ) * a = D.ordPullback τ

variable {sX}

/-- A pair `(X, Δ)` admitting a discrepancy is a pair. -/
theorem IsDiscrepancy.isPair {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX}
    {a : ℚ} (h : IsDiscrepancy sX n K Δ D a) : IsPair sX Δ := by
  obtain ⟨hX, hK, m, hm, hC, -⟩ := h
  exact ⟨hX, n, K, hK, m, by exact_mod_cast hm.ne', hC⟩

/-- **The discrepancy without boundary is the discrepancy for `Δ = 0`** of an exceptional
divisor. -/
@[mmp "def_km2b_discrepancy"]
theorem isDiscrepancyNoBoundary_iff {n : ℕ} {K : Divisor X} {D : DivisorOver k sX} {a : ℚ} :
    IsDiscrepancyNoBoundary sX n K D a ↔ D.IsExceptional ∧ IsDiscrepancy sX n K 0 D a := by
  have hC (m : ℕ) : ((m : ℤ) • (Divisor.toQDivisor K + 0)).IsCartierDivisor ↔
      ((m : ℤ) • K).IsCartier := by
    rw [add_zero, ← map_zsmul, QDivisor.isCartierDivisor_toQDivisor]
  have hG (m : ℕ) (U : X.Opens) (σ : RationalPluriForms sX n m) :
      GeneratesOn (0 : QDivisor X) m U σ ↔
        σ ≠ 0 ∧ ∀ Γ : PrimeDivisor X, (Γ.support ∩ U).Nonempty → Γ.ordForm σ = 0 := by
    simp [GeneratesOn]
  constructor
  · rintro ⟨hX, hK, hE, m, hm, hmK, U, hU, σ, hσ, hord, ha⟩
    exact ⟨hE, hX, hK, m, hm, (hC m).mpr hmK, U, hU, σ, (hG m U σ).mpr ⟨hσ, hord⟩, ha⟩
  · rintro ⟨hE, hX, hK, m, hm, hmK, U, hU, σ, hσ, ha⟩
    obtain ⟨hσ0, hord⟩ := (hG m U σ).mp hσ
    exact ⟨hX, hK, hE, m, hm, (hC m).mp hmK, U, hU, σ, hσ0, hord, ha⟩

end Discrepancy

/-! ### The crepant boundary -/

section CrepantBoundary

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The crepant boundary.** For a normal variety `X` with canonical divisor `K` of dimension
`n`, a `ℚ`-divisor `Δ` and a birational morphism `f : Y ⟶ X` from a normal variety `Y`, a
`ℚ`-divisor `Δ_Y` on `Y` is *the crepant boundary* of `(X, Δ)` on `Y` if
`-coeff_F(Δ_Y)` is the discrepancy `a(F, X, Δ)` of every prime divisor `F` of `Y`, regarded as the
divisor `(Y, f, F)` over `X`. -/
@[mmp "def_km2b_crepant_boundary"]
def IsCrepantBoundary (n : ℕ) (K : Divisor X) (Δ : QDivisor X) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (ΔY : QDivisor Y) : Prop :=
  ∀ F : PrimeDivisor Y,
    IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ (-ΔY.coeff F)

end CrepantBoundary

/-! ### The discrepancy of a pair -/

section Discrep

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The discrepancy of a pair** `(X, Δ)`, for a canonical divisor `K` of dimension `n`:
`discrep(X, Δ) = inf {a(E, X, Δ) | E exceptional over X} ∈ ℝ ∪ {±∞}`, the infimum of the
discrepancies of all exceptional divisors over `X`, with `inf ∅ = +∞`. -/
@[mmp "def_km2b_discrep"]
def discrep (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : EReal :=
  sInf {x : EReal | ∃ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional ∧
    IsDiscrepancy sX n K Δ D a ∧ x = ((a : ℝ) : EReal)}

variable {sX}

/-- The discrepancy of a pair is at most that of each exceptional divisor over `X`. -/
theorem discrep_le {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX} {a : ℚ}
    (hD : D.IsExceptional) (ha : IsDiscrepancy sX n K Δ D a) :
    discrep sX n K Δ ≤ ((a : ℝ) : EReal) :=
  sInf_le ⟨D, a, hD, ha, rfl⟩

/-- `discrep(X, Δ)` is the greatest lower bound of the discrepancies of exceptional divisors. -/
theorem le_discrep_iff {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {b : EReal} :
    b ≤ discrep sX n K Δ ↔ ∀ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional →
      IsDiscrepancy sX n K Δ D a → b ≤ ((a : ℝ) : EReal) := by
  refine le_sInf_iff.trans ⟨fun h D a hD ha => h _ ⟨D, a, hD, ha, rfl⟩, ?_⟩
  rintro h _ ⟨D, a, hD, ha, rfl⟩
  exact h D a hD ha

/-- If no exceptional divisor over `X` has a discrepancy, `discrep(X, Δ) = +∞`. -/
theorem discrep_eq_top {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : ∀ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional → ¬ IsDiscrepancy sX n K Δ D a) :
    discrep sX n K Δ = ⊤ :=
  top_le_iff.mp (le_discrep_iff.mpr fun D a hD ha => (h D a hD ha).elim)

end Discrep

end MMP.Mori
