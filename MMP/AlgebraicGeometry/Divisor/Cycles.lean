module

public import MMP.AlgebraicGeometry.Divisor.Coefficients
public import MMP.AlgebraicGeometry.Divisor.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Order.Round

/-!
# Cycles, Weil divisors and the cycle map (Lazarsfeld §1.1, §1.3, §9.1)

A `k`-cycle on a scheme `X` is a finite `ℤ`-linear combination of `k`-dimensional subvarieties;
when `X` has pure dimension `n` the Weil divisors are the `(n-1)`-cycles. A Cartier divisor `D`
has an order along every `(n-1)`-dimensional subvariety `V`, computed from a local equation
`a/b` at the generic point of `V` as `length(𝒪/a) - length(𝒪/b)`, and these orders form its
Weil divisor `[D]`.

Lazarsfeld's Weil `ℝ`-divisors on a normal variety (§9.1) are finite real combinations of prime
divisors; these are `MMP.Mori.RDivisor`, with coefficients
`MMP.Mori.DivisorWithCoeffs.coeff` and support `MMP.Mori.DivisorWithCoeffs.supp`, and the
round-down, fractional part and effectivity are defined here on them.

## Main definitions

* `MMP.Intersection.subvarietyDim`, `MMP.Intersection.Cycle`, `MMP.Intersection.Cycle.IsEffective`.
* `MMP.Intersection.IsPureDimensional`, `MMP.Intersection.WeilDivisor`.
* `MMP.Intersection.IsOrderAlong`, `MMP.Intersection.IsWeilDivisorOf`.
* `MMP.Intersection.WeilDivisorWithCoeffs`, `MMP.Intersection.WeilQDivisor`,
  `MMP.Intersection.CartierDivisorWithCoeffs.IsWeilDivisorOf`.
* `MMP.Intersection.WeilRDivisor.IsIntegral`, `MMP.Intersection.WeilRDivisor.IsRational`,
  `MMP.Intersection.WeilRDivisor.roundDown`, `MMP.Intersection.WeilRDivisor.fract`,
  `MMP.Intersection.WeilRDivisor.IsEffective`, `MMP.Intersection.WeilRDivisor.LE`.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry TensorProduct

namespace MMP.Intersection

variable {X : Scheme.{u}}

/-! ### Cycles -/

/-- The dimension of a subvariety: the dimension of the integral closed subscheme. -/
@[mmp "def_p01a_cycle"]
abbrev subvarietyDim (V : Scheme.Subvariety X) : WithBot ℕ∞ := Scheme.dimension V.ideal.subscheme

variable (X) in
/-- The group `Z_k(X)` of `k`-cycles: the free abelian group on the `k`-dimensional subvarieties
of `X`, i.e. finite `ℤ`-linear combinations `∑ nᵢ [Vᵢ]`. -/
@[mmp "def_p01a_cycle"]
abbrev Cycle (k : ℕ) := {V : Scheme.Subvariety X // subvarietyDim V = k} →₀ ℤ

/-- A cycle `∑ nᵢ [Vᵢ]` is *effective* if all `nᵢ ≥ 0`. -/
@[mmp "def_p01a_cycle"]
def Cycle.IsEffective {k : ℕ} (c : Cycle X k) : Prop := ∀ V, 0 ≤ c V

variable (X) in
/-- `X` has *pure dimension `n`*: every irreducible component has dimension `n`. -/
@[mmp "def_p01a_cycle"]
def IsPureDimensional (n : ℕ) : Prop :=
  ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = n

variable (X) in
/-- The `(n-1)`-dimensional subvarieties of `X`. -/
abbrev Codim1Subvariety (n : ℕ) := {V : Scheme.Subvariety X // subvarietyDim V + 1 = n}

variable (X) in
/-- Weil divisors with coefficients in `R` on a scheme of pure dimension `n`: finite
`R`-linear combinations of `(n-1)`-dimensional subvarieties. -/
@[mmp "def_p01a_cycle", mmp "def_p01a_weil_q_divisor"]
abbrev WeilDivisorWithCoeffs (R : Type*) [Zero R] (n : ℕ) := Codim1Subvariety X n →₀ R

variable (X) in
/-- `WDiv(X) = Z_{n-1}(X)`, the Weil divisors on a scheme of pure dimension `n`: the free
abelian group on the `(n-1)`-dimensional subvarieties. -/
@[mmp "def_p01a_cycle"]
abbrev WeilDivisor (n : ℕ) := WeilDivisorWithCoeffs X ℤ n

/-- For `d : WithBot ℕ∞` and `k : ℕ`, `d + 1 = k + 1` holds if and only if `d = k`. -/
theorem withBot_add_one_eq_natCast_succ_iff {d : WithBot ℕ∞} {k : ℕ} :
    d + 1 = ((k + 1 : ℕ) : WithBot ℕ∞) ↔ d = k := by
  induction d using WithBot.recBotCoe with
  | bot => exact ⟨fun h => absurd h WithBot.bot_ne_coe, fun h => absurd h WithBot.bot_ne_coe⟩
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) := by norm_cast
      rw [h1]
      exact ⟨fun h => absurd ((top_add (1 : ℕ∞)).symm.trans (WithBot.coe_injective h))
          (ENat.top_ne_natCast _),
        fun h => absurd (WithBot.coe_injective h) (by simp)⟩
    | coe e => exact_mod_cast Nat.add_right_cancel_iff

/-- For `n = k + 1`, `WDiv(X) = Z_k(X)`. -/
@[mmp "def_p01a_cycle"]
def weilDivisorEquivCycle (k : ℕ) : WeilDivisor X (k + 1) ≃+ Cycle X k :=
  Finsupp.domCongr (Equiv.subtypeEquivRight fun _ => withBot_add_one_eq_natCast_succ_iff)

/-- Evaluating `weilDivisorEquivCycle k w` at a `k`-dimensional subvariety `V` is evaluating `w`
at `V`. -/
@[simp]
theorem weilDivisorEquivCycle_apply (k : ℕ) (w : WeilDivisor X (k + 1))
    (V : {V : Scheme.Subvariety X // subvarietyDim V = k}) :
    weilDivisorEquivCycle k w V = w ⟨V.1, withBot_add_one_eq_natCast_succ_iff.mpr V.2⟩ := rfl

/-- Evaluating `(weilDivisorEquivCycle k).symm c` at an `(n-1)`-dimensional subvariety `V` is
evaluating `c` at `V`. -/
@[simp]
theorem weilDivisorEquivCycle_symm_apply (k : ℕ) (c : Cycle X k)
    (V : Codim1Subvariety X (k + 1)) :
    (weilDivisorEquivCycle k).symm c V = c ⟨V.1, withBot_add_one_eq_natCast_succ_iff.mp V.2⟩ :=
  rfl

/-! ### The order along a subvariety and the cycle map -/

/-- An integer `N` is *an order of `D` along `V`* (Lazarsfeld Rem. 1.1.4): there are
non-zero-divisors `a, b` of `𝒪_{X,v}`, `v` the generic point of `V`, with `a/b` a local
equation of `D` at `v` and `N = length(𝒪_{X,v}/a𝒪_{X,v}) - length(𝒪_{X,v}/b𝒪_{X,v})` (both
lengths finite). -/
@[mmp "def_p01a_order_along_subvariety"]
def IsOrderAlong (D : X.CartierDivisor) (V : Scheme.Subvariety X) (N : ℤ) : Prop :=
  ∃ a b : X.presheaf.stalk V.genericPoint,
    a ∈ nonZeroDivisors _ ∧ b ∈ nonZeroDivisors _ ∧
    (∃ g, IsLocalEquationAt D V.genericPoint g ∧ IsFraction g a b) ∧
    ∃ la lb : ℕ,
      Module.length (X.presheaf.stalk V.genericPoint)
          (X.presheaf.stalk V.genericPoint ⧸ Ideal.span {a}) = la ∧
      Module.length (X.presheaf.stalk V.genericPoint)
          (X.presheaf.stalk V.genericPoint ⧸ Ideal.span {b}) = lb ∧
      N = la - lb

/-- A function `w : V ↦ w_V` on the `(n-1)`-dimensional subvarieties is *the Weil divisor
`[D] = ∑ ord_V(D) [V]` of `D`* if every `w_V` is an order of `D` along `V`. -/
@[mmp "def_p01a_cartier_cycle_map"]
def IsWeilDivisorOf {n : ℕ} (D : X.CartierDivisor) (w : Codim1Subvariety X n → ℤ) : Prop :=
  ∀ V, IsOrderAlong D V.1 (w V)

variable (X) in
/-- `WDiv_ℚ(X) = WDiv(X) ⊗_ℤ ℚ`, the Weil `ℚ`-divisors (Lazarsfeld Rem. 1.3.8). -/
@[mmp "def_p01a_weil_q_divisor"]
abbrev WeilQDivisor (n : ℕ) := WeilDivisor X n ⊗[ℤ] ℚ

open scoped Classical in
/-- `WDiv(X) ⊗_ℤ R` is the group of finite `R`-linear combinations of `(n-1)`-dimensional
subvarieties. -/
@[mmp "def_p01a_weil_q_divisor"]
def weilDivisorTensorEquiv (R : Type*) [AddCommGroup R] (n : ℕ) :
    WeilDivisor X n ⊗[ℤ] R ≃ₗ[ℤ] WeilDivisorWithCoeffs X R n :=
  TensorProduct.finsuppScalarLeft ℤ R (Codim1Subvariety X n)

/-- `w ∈ WDiv(X) ⊗ R` is *the Weil divisor `[D]`* of `D = ∑ cᵢ Aᵢ` (relative to that
representation) if `w = ∑ cᵢ wᵢ` with `wᵢ` the Weil divisor of `Aᵢ`; for `R = ℚ` this is the
cycle map `Div_ℚ(X) → WDiv_ℚ(X)` (Lazarsfeld Rem. 1.3.8). -/
@[mmp "def_p01a_weil_q_divisor"]
def CartierDivisorWithCoeffs.IsWeilDivisorOf {R : Type*} [CommRing R] {n : ℕ}
    (D : CartierDivisorWithCoeffs R X) {m : ℕ} (c : Fin m → R) (A : Fin m → X.CartierDivisor)
    (w : WeilDivisor X n ⊗[ℤ] R) : Prop :=
  CartierDivisorWithCoeffs.IsRepresentation D c A ∧
    ∃ wᵢ : Fin m → WeilDivisor X n, (∀ i, MMP.Intersection.IsWeilDivisorOf (A i) (wᵢ i)) ∧
      w = ∑ i, wᵢ i ⊗ₜ c i

/-! ### Weil `ℝ`-divisors on a normal variety (Lazarsfeld §9.1.A) -/

attribute [mmp "def_p09a_weil_r_divisor"] MMP.Mori.RDivisor MMP.Mori.DivisorWithCoeffs.coeff
  MMP.Mori.DivisorWithCoeffs.supp MMP.Mori.Divisor.tensorEquiv MMP.Mori.QDivisor.toRDivisor
attribute [mmp "def_p09a_integral_weil_divisor", mmp "def_p09a_round_down"]
  MMP.Mori.Divisor.toRDivisor

namespace WeilRDivisor

/-- A Weil `ℝ`-divisor is *rational* (a Weil `ℚ`-divisor) if every coefficient `ord_P(D)` is
rational. -/
@[mmp "def_p09a_weil_r_divisor"]
def IsRational (D : MMP.Mori.RDivisor X) : Prop := ∀ P, ∃ q : ℚ, D.coeff P = q

/-- A Weil `ℝ`-divisor is *integral* if `ord_P(D) ∈ ℤ` for every prime divisor `P`. -/
@[mmp "def_p09a_integral_weil_divisor"]
def IsIntegral (D : MMP.Mori.RDivisor X) : Prop := ∀ P, ∃ n : ℤ, D.coeff P = n

/-- The *round-down* `⌊D⌋ = ∑ ⌊aᵢ⌋ Dᵢ` of a Weil `ℝ`-divisor. -/
@[mmp "def_p09a_round_down"]
def roundDown (D : MMP.Mori.RDivisor X) : MMP.Mori.Divisor X :=
  D.mapCoeffs (fun r => ⌊r⌋) (by simp)

/-- The coefficient of `⌊D⌋` at a prime divisor `P` is the floor of the coefficient of `D` at
`P`. -/
@[simp]
theorem coeff_roundDown (D : MMP.Mori.RDivisor X) (P : MMP.Mori.PrimeDivisor X) :
    (roundDown D).coeff P = ⌊D.coeff P⌋ := by
  simp [roundDown]

/-- A Weil `ℝ`-divisor is integral if and only if it lies in the image of `WDiv(X)` under
`Divisor.toRDivisor`. -/
@[mmp "def_p09a_integral_weil_divisor"]
theorem isIntegral_iff_mem_range (D : MMP.Mori.RDivisor X) :
    IsIntegral D ↔ D ∈ Set.range (MMP.Mori.Divisor.toRDivisor (X := X)) := by
  constructor
  · intro h
    refine ⟨roundDown D, ?_⟩
    ext P
    obtain ⟨n, hn⟩ := h P
    simp [hn]
  · rintro ⟨D', rfl⟩ P
    exact ⟨D'.coeff P, rfl⟩

/-- The *fractional part* `{D} = D - ⌊D⌋`. -/
@[mmp "def_p09a_fractional_part"]
def fract (D : MMP.Mori.RDivisor X) : MMP.Mori.RDivisor X :=
  D - MMP.Mori.Divisor.toRDivisor (roundDown D)

/-- A Weil `ℝ`-divisor is *effective*, `D ≽ 0`, if `ord_P(D) ≥ 0` for every prime divisor. -/
@[mmp "def_p09a_weil_divisor_effective_order"]
def IsEffective (D : MMP.Mori.RDivisor X) : Prop := ∀ P, 0 ≤ D.coeff P

/-- `D₁ ≼ D₂` if `D₂ - D₁ ≽ 0`. -/
@[mmp "def_p09a_weil_divisor_effective_order"]
def LE (D₁ D₂ : MMP.Mori.RDivisor X) : Prop := IsEffective (D₂ - D₁)

end WeilRDivisor

end MMP.Intersection
