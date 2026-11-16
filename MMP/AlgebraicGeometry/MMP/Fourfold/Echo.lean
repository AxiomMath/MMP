module

public import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
public import StacksFrontier.AlgebraicGeometry.Properties.Regular

/-!
# The one-label smooth locus and echo valuations at a curve

Let `Y` be a normal variety and `S_1, …, S_m` distinct prime divisors on `Y`, the *labels*. The
*one-label smooth locus* is
`Y° = Y_reg ∖ (⋃_h Sing(S_h) ∪ ⋃_{h ≠ h'} (S_h ∩ S_{h'}))`,
where `Y_reg` is the regular locus of `Y` and `Sing(S_h)` the singular locus of `S_h`, with its
reduced (integral) scheme structure.

Let now `Y` be a normal threefold with labels `S_h`, and `V ⊆ S_h` an irreducible closed curve
whose generic point `η_V` lies in `Y°`. Then `𝒪_{Y,η_V}` is regular of dimension two with maximal
ideal `𝔪`, and `S_h` has a local equation `x` there, which is a regular parameter. For `j ≥ 1`, a
normalized divisorial valuation `ξ` of `k(Y)` is an *echo of order `j` of `S_h` at `V`* if
`c_Y(ξ) = V` and, for every nonzero `f ∈ 𝒪_{Y,η_V}`,
`ξ(f) = max {n ≥ 0 : f ∈ ∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}}`.
The ideals on the right depend only on the ideal `(x)`, so not on the local equation
(`MMP.Fourfold.echoIdeal_eq_of_span_eq`), and the notion depends only on `S_h`, `V` and `j`
(`MMP.Fourfold.isEcho_iff_forall`).

## Main definitions

* `MMP.Fourfold.oneLabelSmoothLocus`: the one-label smooth locus `Y°`.
* `MMP.Fourfold.echoIdeal`: the ideal `∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}`.
* `MMP.Fourfold.IsEcho`: `ξ` is an echo of order `j` of `S_h` at `V`.

## Main results

* `MMP.Fourfold.echoIdeal_eq_of_span_eq`: the ideals depend only on `(x)`.
* `MMP.Fourfold.echoIdeal_zero`, `MMP.Fourfold.echoIdeal_antitone`: the ideal at `n = 0` is the
  whole ring, and `n ↦ ∑_a x^a 𝔪^{max(n - ja, 0)}` is decreasing.
* `MMP.Fourfold.isEcho_iff_forall`: the defining condition, stated for one local equation, holds
  for every local equation.

## Implementation notes

* The labels are a finite set `L` of prime divisors, so they are distinct; `h ≠ h'` reads
  `S ≠ S'` for `S, S' ∈ L`. The one-label smooth locus is defined as a subset of `Y` for any
  scheme and any finite set of prime divisors; its openness, for a normal variety, is not part
  of the definition.
* `Y_reg` is the regular locus `AlgebraicGeometry.regularLocus` (points with regular local
  ring). `Sing(S_h)` is the image in `Y` of the singular locus `AlgebraicGeometry.singularLocus`
  of the integral closed subscheme `S_h` cut out by the ideal sheaf of the prime divisor.
* A normal threefold is a normal variety (`MMP.Mori.IsNormalVariety`) of dimension `3`, and an
  irreducible closed curve of `Y` is an irreducible closed subset of dimension `1`. These, and
  `S_h ∈ L`, `V ⊆ S_h`, `η_V ∈ Y°`, `j ≥ 1`, are part of the condition `MMP.Fourfold.IsEcho`.
  The regularity of `𝒪_{Y,η_V}`, its dimension and the fact that `x` is a regular parameter are
  consequences in the source, not conditions.
* A local equation of `S_h` at `η_V` is a generator `x` of the stalk at `η_V` of the ideal sheaf
  of `S_h`. The sum of ideals `∑_{a ≥ 0}` is the supremum `⨆ a`, and `max(n - ja, 0)` is the
  truncated subtraction `n - j * a` of natural numbers.
* Valuations are Mathlib's multiplicative `Valuation k(Y) ℤᵐ⁰`: `ξ(f) = M` reads
  `ξ f = exp (-M)`, as in `MMP.Fourfold.IsMonomialValuationOfWeight`. That the maximum exists for
  nonzero `f` is part of the condition. A normalized divisorial valuation with centre `V` is
  `MMP.Intersection.IsCentre`. The base field is any field `k`; the source takes `k = ℂ`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u v

namespace MMP.Fourfold

open MMP.Mori

/-! ### The one-label smooth locus -/

section OneLabelSmoothLocus

variable {Y : Scheme.{u}}

/-- The *one-label smooth locus* of a scheme `Y` (a normal variety in the source) with labels
`L`, a finite set of distinct prime divisors `S_h`:
`Y° = Y_reg ∖ (⋃_h Sing(S_h) ∪ ⋃_{h ≠ h'} (S_h ∩ S_{h'}))`, where `Y_reg` is the regular locus
of `Y` and `Sing(S_h)` is the singular locus of the integral closed subscheme `S_h`, regarded in
`Y`. -/
@[mmp "def_oai4_one_label_smooth_locus"]
def oneLabelSmoothLocus (L : Finset (MMP.Mori.PrimeDivisor Y)) : Set Y :=
  regularLocus Y \
    ((⋃ S ∈ L, S.idealSheaf.subschemeι '' singularLocus S.idealSheaf.subscheme) ∪
      ⋃ S ∈ L, ⋃ S' ∈ L, ⋃ (_ : S ≠ S'), S.support ∩ S'.support)

/-- A point `y` lies in the one-label smooth locus if and only if its local ring is regular, it
is not in the singular locus of any label, and it does not lie on two distinct labels. -/
theorem mem_oneLabelSmoothLocus_iff {L : Finset (MMP.Mori.PrimeDivisor Y)} {y : Y} :
    y ∈ oneLabelSmoothLocus L ↔ IsRegularLocalRing (Y.presheaf.stalk y) ∧
      (∀ S ∈ L, y ∉ S.idealSheaf.subschemeι '' singularLocus S.idealSheaf.subscheme) ∧
      ∀ S ∈ L, ∀ S' ∈ L, S ≠ S' → ¬ (y ∈ S.support ∧ y ∈ S'.support) := by
  simp only [oneLabelSmoothLocus, Set.mem_sdiff, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
    not_or, not_exists, exists_prop, not_and]
  rfl

/-- The one-label smooth locus lies in the regular locus. -/
theorem oneLabelSmoothLocus_subset_regularLocus (L : Finset (MMP.Mori.PrimeDivisor Y)) :
    oneLabelSmoothLocus L ⊆ regularLocus Y :=
  Set.sdiff_subset

/-- A point of the one-label smooth locus lies on at most one label. -/
theorem eq_of_mem_oneLabelSmoothLocus {L : Finset (MMP.Mori.PrimeDivisor Y)} {y : Y}
    (hy : y ∈ oneLabelSmoothLocus L) {S S' : MMP.Mori.PrimeDivisor Y} (hS : S ∈ L)
    (hS' : S' ∈ L) (hyS : y ∈ S.support) (hyS' : y ∈ S'.support) : S = S' := by
  by_contra h
  exact (mem_oneLabelSmoothLocus_iff.mp hy).2.2 S hS S' hS' h ⟨hyS, hyS'⟩

end OneLabelSmoothLocus

/-! ### Echo ideals -/

section EchoIdeal

variable {R : Type v} [CommSemiring R]

/-- The ideal `∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}` of `R`, for an element `x`, an ideal `𝔪`, a
weight `j` and `n ∈ ℕ`. -/
@[mmp "def_mmp_indexd_echo"]
def echoIdeal (x : R) (𝔪 : Ideal R) (j n : ℕ) : Ideal R :=
  ⨆ a : ℕ, Ideal.span {x ^ a} * 𝔪 ^ (n - j * a)

/-- The echo ideal is `∑_{a ≥ 0} (x)^a 𝔪^{max(n - ja, 0)}`, written with powers of the principal
ideal `(x)`. -/
theorem echoIdeal_eq_iSup_pow (x : R) (𝔪 : Ideal R) (j n : ℕ) :
    echoIdeal x 𝔪 j n = ⨆ a : ℕ, Ideal.span {x} ^ a * 𝔪 ^ (n - j * a) := by
  simp only [echoIdeal, Ideal.span_singleton_pow]

/-- The ideals `∑_a x^a 𝔪^{max(n - ja, 0)}` depend only on the principal ideal `(x)`: they do not
change when `x` is replaced by another generator of `(x)`, for instance a unit multiple. -/
theorem echoIdeal_eq_of_span_eq {x x' : R} (h : Ideal.span {x} = Ideal.span {x'})
    (𝔪 : Ideal R) (j n : ℕ) : echoIdeal x 𝔪 j n = echoIdeal x' 𝔪 j n := by
  rw [echoIdeal_eq_iSup_pow, echoIdeal_eq_iSup_pow, h]

/-- The echo ideal is unchanged when `x` is multiplied by a unit. -/
theorem echoIdeal_unit_mul (u : Rˣ) (x : R) (𝔪 : Ideal R) (j n : ℕ) :
    echoIdeal ((u : R) * x) 𝔪 j n = echoIdeal x 𝔪 j n :=
  echoIdeal_eq_of_span_eq (Ideal.span_singleton_mul_left_unit u.isUnit x) 𝔪 j n

/-- The echo ideal at `n = 0` is the whole ring. -/
@[simp] theorem echoIdeal_zero (x : R) (𝔪 : Ideal R) (j : ℕ) : echoIdeal x 𝔪 j 0 = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ (le_iSup _ 0))
  simp

/-- The echo ideal `∑_a x^a 𝔪^{max(n - ja, 0)}` is antitone in `n`. -/
theorem echoIdeal_antitone (x : R) (𝔪 : Ideal R) (j : ℕ) : Antitone (echoIdeal x 𝔪 j) :=
  fun _ _ h => iSup_mono fun _ =>
    Ideal.mul_mono_right (Ideal.pow_le_pow_right (Nat.sub_le_sub_right h _))

end EchoIdeal

/-! ### Echo valuations -/

section Echo

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]

/-- The defining condition of an echo of order `j` at `V` for a chosen element `x` of
`𝒪_{Y,η_V}`: for every nonzero `f ∈ 𝒪_{Y,η_V}`,
`ξ(f) = max {n ≥ 0 : f ∈ ∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}}`. -/
@[mmp "def_mmp_indexd_echo"]
def IsEchoValue (V : IrreducibleCloseds Y) (x : Y.presheaf.stalk V.isIrreducible.genericPoint)
    (j : ℕ) (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))) : Prop :=
  ∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
    ∃ M : ℕ, IsGreatest {n : ℕ | f ∈ echoIdeal x
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint)) j n} M ∧
      ξ (algebraMap _ Y.functionField f) = WithZero.exp (-(M : ℤ))

/-- The echo condition for `x` implies the echo condition for any `x'` with `(x) = (x')`. -/
theorem isEchoValue_of_span_eq {V : IrreducibleCloseds Y}
    {x x' : Y.presheaf.stalk V.isIrreducible.genericPoint} (h : Ideal.span {x} = Ideal.span {x'})
    {j : ℕ} {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hξ : IsEchoValue V x j ξ) : IsEchoValue V x' j ξ := by
  intro f hf
  obtain ⟨M, hM, hξM⟩ := hξ f hf
  refine ⟨M, ?_, hξM⟩
  simpa only [echoIdeal_eq_of_span_eq h] using hM

/-- **Echo valuations at a curve.** Let `Y` be a normal threefold over `k` with labels `L`
(distinct prime divisors) and one-label smooth locus `Y°`, let `S = S_h ∈ L`, let `V ⊆ S_h` be
an irreducible closed curve whose generic point `η_V` lies in `Y°`, and let `j ≥ 1`. A
normalized divisorial valuation `ξ` of `k(Y)` is an *echo of order `j` of `S_h` at `V`* if
`c_Y(ξ) = V` and, for a local equation `x` of `S_h` at `η_V` and every nonzero
`f ∈ 𝒪_{Y,η_V}` (maximal ideal `𝔪`),
`ξ(f) = max {n ≥ 0 : f ∈ ∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}}`.
The condition does not depend on the local equation (`MMP.Fourfold.isEcho_iff_forall`). -/
@[mmp "def_mmp_indexd_echo"]
def IsEcho (L : Finset (MMP.Mori.PrimeDivisor Y)) (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) (j : ℕ)
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))) : Prop :=
  IsNormalVariety k sY ∧ topologicalKrullDim Y = 3 ∧ S ∈ L ∧ (V : Set Y) ⊆ S.support ∧
    topologicalKrullDim (V : Set Y) = 1 ∧
    V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L ∧ 1 ≤ j ∧
    MMP.Intersection.IsCentre k sY ξ V ∧
    ∃ x : Y.presheaf.stalk V.isIrreducible.genericPoint,
      IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x} ∧
        IsEchoValue V x j ξ

variable {sY}

/-- The notion of echo does not depend on the local equation: the defining condition then
holds for every local equation of `S_h` at `η_V`. -/
theorem isEcho_iff_forall {L : Finset (MMP.Mori.PrimeDivisor Y)} {S : MMP.Mori.PrimeDivisor Y}
    {V : IrreducibleCloseds Y} {j : ℕ}
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))} :
    IsEcho sY L S V j ξ ↔
      IsNormalVariety k sY ∧ topologicalKrullDim Y = 3 ∧ S ∈ L ∧ (V : Set Y) ⊆ S.support ∧
        topologicalKrullDim (V : Set Y) = 1 ∧
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

end Echo

end MMP.Fourfold
