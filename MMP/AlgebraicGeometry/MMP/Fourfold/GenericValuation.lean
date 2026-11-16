module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Echo

/-!
# Echo valuations and generic blowup valuations at a surface of a fourfold

Let `X` be a normal fourfold and `V ⊆ X` an irreducible closed surface such that `X` is smooth at
the generic point `η_V`. Then `𝒪_{X,η_V}` is a regular local ring of dimension two with maximal
ideal `𝔪_V`, and the *generic blowup valuation* `v_V` is the normalized divisorial valuation of
`k(X)` with `v_V(g) = max {n : g ∈ 𝔪_V^n}` for `0 ≠ g ∈ 𝒪_{X,η_V}`: the order along the
exceptional divisor of the blowup of `X` along `V`, near `η_V`.

Let `Y` be a normal fourfold with labels `S_1, …, S_m` and one-label smooth locus `Y°`
(`MMP.Fourfold.oneLabelSmoothLocus`), and `V ⊆ S_h` an irreducible closed surface with
`η_V ∈ Y°`. Then `𝒪_{Y,η_V}` is regular of dimension two with maximal ideal `𝔪`, and `S_h` has a
local equation `x` there. For `j ≥ 1`, a normalized divisorial valuation `ξ` of `k(Y)` is an
*echo of order `j` of `S_h` at `V`* if `c_Y(ξ) = V` and
`ξ(f) = max {n ≥ 0 : f ∈ ∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}}` for every nonzero `f ∈ 𝒪_{Y,η_V}`.

For a pair `(X, B)` and an irreducible closed subvariety `V ⊆ X` of codimension two, the
*generic minimal log discrepancy* `mld_{η_V}(X, B) = inf {a(ξ; X, B) : c_X(ξ) = V}` is the
minimal log discrepancy `MMP.Fourfold.minimalLogDiscrepancy` at the point `η_V`, whose closure is
`V`.

## Main definitions

* `MMP.Fourfold.IsSurfaceGenericBlowupValuation`: `v = v_V` for a surface `V` of a fourfold.
* `MMP.Fourfold.IsSurfaceEcho`: `ξ` is an echo of order `j` of `S_h` at a surface `V` of a
  fourfold.

## Main results

* `MMP.Fourfold.eq_of_forall_stalk_eq`: two valuations of `k(X)` agreeing on `𝒪_{X,x}` agree.
* `MMP.Fourfold.IsSurfaceGenericBlowupValuation.eq`: the generic blowup valuation is unique.
* `MMP.Fourfold.IsSurfaceEcho.eq`: an echo of order `j` of `S_h` at `V` is unique.
* `MMP.Fourfold.isSurfaceEcho_iff_forall`: the defining condition of an echo, stated for one
  local equation, holds for every local equation.

## Implementation notes

* A normal fourfold is a normal variety (`MMP.Mori.IsNormalVariety`) of dimension `4`, and an
  irreducible closed surface is an irreducible closed subset of dimension `2`, as for the
  threefold versions `MMP.Fourfold.IsEcho` and `MMP.Fourfold.IsGenericBlowupValuation`.
* "`X` is smooth at `η_V`" is the regularity of `𝒪_{X,η_V}`, as for the regular locus
  `AlgebraicGeometry.regularLocus`; over `ℂ`, the field of the source, the two agree. That
  `𝒪_{X,η_V}` has dimension two is a consequence in the source, not a condition.
* Valuations are Mathlib's multiplicative `Valuation k(X) ℤᵐ⁰`: `v(g) = M` reads
  `v g = exp (-M)`. That the maxima exist for nonzero elements is part of the conditions. A
  normalized divisorial valuation with centre `V` is `MMP.Intersection.IsCentre`; for the
  generic blowup valuation the centre is `V`, the centre of the exceptional divisor of the blowup
  along `V`. The base field is any field `k`.
* The echo condition is `MMP.Fourfold.IsEchoValue`, with the local equation `x` a generator of
  the stalk at `η_V` of the ideal sheaf of `S_h`, as in `MMP.Fourfold.IsEcho`.
* The generic minimal log discrepancy takes values in `EReal`, with the conventions of
  `MMP.Fourfold.minimalLogDiscrepancy`: the infimum is over the divisors over `X` with centre
  `V`, and the infimum of the empty set is `⊤`. The codimension-two condition on `V` restricts
  where the notion is used, not its value, so the node is registered on
  `MMP.Fourfold.minimalLogDiscrepancy` at `η_V`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Valuations determined on a local ring -/

section Stalk

variable {X : Scheme.{u}} [IsIntegral X]

/-- Two valuations of the function field `k(X)` of an integral scheme that agree on the image of
a stalk `𝒪_{X,x}` agree: `k(X)` is the fraction field of `𝒪_{X,x}`. -/
theorem eq_of_forall_stalk_eq {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (x : X)
    {v v' : Valuation X.functionField Γ}
    (h : ∀ g : X.presheaf.stalk x, v (algebraMap _ X.functionField g) =
      v' (algebraMap _ X.functionField g)) : v = v' := by
  ext z
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x) z
  rw [map_div₀, map_div₀, h, h]

end Stalk

/-! ### Generic blowup valuations of a surface -/

section GenericBlowup

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

/-- **The generic blowup valuation of a surface.** Let `X` be a normal fourfold over `k` and
`V ⊆ X` an irreducible closed surface such that `X` is smooth at its generic point `η_V`, that
is, `𝒪_{X,η_V}` is regular (of dimension two), with maximal ideal `𝔪_V`. A valuation `v` of
`k(X)` is the *generic blowup valuation* `v_V` if it is a normalized divisorial valuation with
centre `V` and `v(g) = max {n : g ∈ 𝔪_V^n}` for every nonzero `g ∈ 𝒪_{X,η_V}`: the order along
the exceptional divisor of the blowup of `X` along `V` near `η_V`. -/
@[mmp "def_oai4_generic_blowup_valuation"]
def IsSurfaceGenericBlowupValuation (V : IrreducibleCloseds X)
    (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) : Prop :=
  IsNormalVariety k sX ∧ topologicalKrullDim X = 4 ∧ topologicalKrullDim (V : Set X) = 2 ∧
    IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint) ∧
    MMP.Intersection.IsCentre k sX v V ∧
    ∀ g : X.presheaf.stalk V.isIrreducible.genericPoint, g ≠ 0 →
      ∃ M : ℕ, IsGreatest {n : ℕ | g ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk V.isIrreducible.genericPoint) ^ n} M ∧
        v (algebraMap _ X.functionField g) = WithZero.exp (-(M : ℤ))

variable {sX}

/-- The generic blowup valuation of a surface is unique. -/
theorem IsSurfaceGenericBlowupValuation.eq {V : IrreducibleCloseds X}
    {v v' : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (h : IsSurfaceGenericBlowupValuation sX V v)
    (h' : IsSurfaceGenericBlowupValuation sX V v') : v = v' := by
  refine eq_of_forall_stalk_eq V.isIrreducible.genericPoint fun g => ?_
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨M, hM, hv⟩ := h.2.2.2.2.2 g hg
  obtain ⟨M', hM', hv'⟩ := h'.2.2.2.2.2 g hg
  rw [hv, hv', hM.unique hM']

end GenericBlowup

/-! ### Echo valuations at a surface -/

section Echo

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]

/-- **Echo valuations at a surface.** Let `Y` be a normal fourfold over `k` with labels `L`
(distinct prime divisors) and one-label smooth locus `Y°`, let `S = S_h ∈ L`, let `V ⊆ S_h` be
an irreducible closed surface whose generic point `η_V` lies in `Y°`, and let `j ≥ 1`. A
normalized divisorial valuation `ξ` of `k(Y)` is an *echo of order `j` of `S_h` at `V`* if
`c_Y(ξ) = V` and, for a local equation `x` of `S_h` at `η_V` and every nonzero
`f ∈ 𝒪_{Y,η_V}` (maximal ideal `𝔪`),
`ξ(f) = max {n ≥ 0 : f ∈ ∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}}`.
The condition does not depend on the local equation (`MMP.Fourfold.isSurfaceEcho_iff_forall`). -/
@[mmp "def_oai4_echo_valuation"]
def IsSurfaceEcho (L : Finset (MMP.Mori.PrimeDivisor Y)) (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) (j : ℕ)
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))) : Prop :=
  IsNormalVariety k sY ∧ topologicalKrullDim Y = 4 ∧ S ∈ L ∧ (V : Set Y) ⊆ S.support ∧
    topologicalKrullDim (V : Set Y) = 2 ∧
    V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L ∧ 1 ≤ j ∧
    MMP.Intersection.IsCentre k sY ξ V ∧
    ∃ x : Y.presheaf.stalk V.isIrreducible.genericPoint,
      IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x} ∧
        IsEchoValue V x j ξ

variable {sY}

/-- The notion of echo at a surface does not depend on the local equation: the defining
condition then holds for every local equation of `S_h` at `η_V`. -/
theorem isSurfaceEcho_iff_forall {L : Finset (MMP.Mori.PrimeDivisor Y)}
    {S : MMP.Mori.PrimeDivisor Y} {V : IrreducibleCloseds Y} {j : ℕ}
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))} :
    IsSurfaceEcho sY L S V j ξ ↔
      IsNormalVariety k sY ∧ topologicalKrullDim Y = 4 ∧ S ∈ L ∧ (V : Set Y) ⊆ S.support ∧
        topologicalKrullDim (V : Set Y) = 2 ∧
        V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L ∧ 1 ≤ j ∧
        MMP.Intersection.IsCentre k sY ξ V ∧
        (∃ x : Y.presheaf.stalk V.isIrreducible.genericPoint,
          IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) ∧
        ∀ x : Y.presheaf.stalk V.isIrreducible.genericPoint,
          IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x} →
            IsEchoValue V x j ξ := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, x, hx, hξ⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, ⟨x, hx⟩, fun x' hx' =>
      isEchoValue_of_span_eq (hx.symm.trans hx') hξ⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, ⟨x, hx⟩, hξ⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, x, hx, hξ x hx⟩

/-- An echo of order `j` of `S_h` at a surface `V` is unique. -/
theorem IsSurfaceEcho.eq {L : Finset (MMP.Mori.PrimeDivisor Y)} {S : MMP.Mori.PrimeDivisor Y}
    {V : IrreducibleCloseds Y} {j : ℕ}
    {ξ ξ' : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (h : IsSurfaceEcho sY L S V j ξ) (h' : IsSurfaceEcho sY L S V j ξ') : ξ = ξ' := by
  obtain ⟨-, -, -, -, -, -, -, -, x, hx, hξ⟩ := h
  have hξ' := (isSurfaceEcho_iff_forall.mp h').2.2.2.2.2.2.2.2.2 x hx
  refine eq_of_forall_stalk_eq V.isIrreducible.genericPoint fun f => ?_
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨M, hM, hv⟩ := hξ f hf
  obtain ⟨M', hM', hv'⟩ := hξ' f hf
  rw [hv, hv', hM.unique hM']

end Echo

/- The generic minimal log discrepancy `mld_{η_V}(X, B)` at an irreducible closed subvariety `V`
of codimension two is the minimal log discrepancy `MMP.Fourfold.minimalLogDiscrepancy` at the
generic point `η_V`, whose closure is `V`: the infimum in `EReal` of `a(ξ; X, B)` over the
divisors over `X` with centre `V`, equal to `⊤` when there are none. -/
attribute [mmp "def_oai4_generic_mld"] MMP.Fourfold.minimalLogDiscrepancy

end MMP.Fourfold
