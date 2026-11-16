module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.MMP.Termination.Defs
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.Singularities.Surface.SingularPointMldBound
import MMP.AlgebraicGeometry.MMP.Flip.FlippedCurveDiscrepancy
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SzaboDifficultyFinite
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.NoFlippingCurveInDivisor
import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces
import MMP.AlgebraicGeometry.MMP.Flip.FlipPreservesCanonical
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.SzaboSetShrinks
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus

/-!
# Termination of canonical flips on threefolds without `ℚ`-factoriality

Let `X` be a threefold over a field `k` of characteristic zero and `D` an effective `ℚ`-divisor
on `X` such that `(X, D)` is canonical and `⌊D⌋ = 0`; `X` need not be `ℚ`-factorial. Then every
sequence of flips for `(X, D)` terminates. This is Szabó's version of the termination argument:
the difficulty is counted only along the curves not contained in the components of `D` already
handled, so the components of `D` never have to be removed from the flipping locus.

The argument has three steps.

* Let `φ⁺ : X⁺ ⟶ Z` be a `(K_X + D)`-flip of the small contraction `φ : X ⟶ Z`, with birational
  map `g`. A flipped curve `C ⊆ X⁺` has codimension two, the pair `(X⁺, g_* D)` is canonical, and
  every divisor `E` with centre `C` satisfies `a(E, X⁺, g_* D) > a(E, X, D) ≥ 0`. A normal variety
  all of whose discrepancies over a codimension-two point are positive is regular there, so
  `𝒪_{X⁺, η_C}` is regular.
* The sets `𝒮_t(X⁺, D⁺; B⁺)` map injectively into the sets `𝒮_t(X, D; B)`, by identifying the
  function fields over `k(Z)`, so Szabó's modified difficulty `d_{N,c}` does not increase under a
  flip. It drops strictly as soon as a flipped curve `C` satisfies `c = 0` or lies in a component
  of coefficient `≥ c`: the blow-up divisor `E_C`, along which `X⁺` is regular, has
  `a_ℓ(E_C, X⁺, D⁺) = 2 - mult_C D⁺` and smaller log discrepancy over `X`. Since a nonincreasing
  sequence of natural numbers drops only finitely often, eventually no flipped curve is of this
  kind.
* The coefficients of every `D_i` lie in the finite set of coefficients of `D`. By downward
  induction on `c` through this set, from some index on no flipping curve lies in a component of
  coefficient `> c`. For `c = 0` eventually no flip has a flipped curve at all, which is absurd,
  since `ρ(X_i/Z_i) = 1` and so `φ_i` is not an isomorphism.

## Main results

* `MMP.Flips.isRegularLocalRing_stalk_of_isFlippedCurveOf`: a flip of a canonical threefold is
  regular at the generic point of every flipped curve.
* `MMP.Flips.szaboDifficulty_flip_le`: Szabó's modified difficulty does not increase under a flip,
  and drops along a flipped curve of the right kind.
* `MMP.Flips.SequenceOfFlips.eventually_not_isFlippedCurveOf`: in a sequence of flips, eventually
  no flipped curve is of that kind.
* `MMP.Flips.SequenceOfFlips.terminates_of_isCanonicalPair`: sequences of canonical flips on
  threefolds terminate.

## Implementation notes

The regularity step is carried out on the generic surface along `C`, over the purely
transcendental extension `k(t)` of `k`, so no hypothesis on `k` beyond characteristic zero enters.
The difficulty of `(X⁺, D⁺; B⁺)` is formed with an arbitrary canonical divisor `K⁺` of `X⁺`; two
canonical divisors give the same log discrepancies, so it does not depend on this choice.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.9–4.14
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Flips

open MMP.Mori

/-! ### Discrepancies over a normal variety -/

section Discrepancy

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- Every proper divisor `E` over a normal variety `X` with canonical divisor `K` and a
`ℚ`-divisor `B` with `K + B` `ℚ`-Cartier has a discrepancy `a_ω(E, X, B)`, computed from a top
form `ω` with `div(ω) = K`. -/
private theorem exists_isQDiscrepancyWith (hXn : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X}
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) (E : ProperDivisorOver k sX) :
    ∃ (ω : RationalPluriForms sX n 1) (a : ℚ), IsQDiscrepancyWith sX n B ω E a := by
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI : QuasiCompact (E.f ≫ sX) := E.isNormalVariety.1.toQuasiCompact
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier E.f hKB
  exact ⟨ω, _, hXn, hK.topologicalKrullDim_eq, hω0, hKB, hB, _,
    MMP.Mori.QDivisor.isPullback_pullback hKB hB, rfl⟩

/-- The log discrepancy of an exceptional divisor does not depend on the canonical divisor used
to compute it: both are `1 + a_ω(E, X, D)` for any top form `ω`. -/
private theorem isLogDiscrepancy_of_isCanonicalDivisor (hX : IsNormalVariety k sX) {n : ℕ}
    {K₁ K₂ : Divisor X} {D : QDivisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
    (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
    (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier) {E : ProperDivisorOver k sX}
    (hE : E.IsExceptional) {b : ℝ}
    (hb : IsLogDiscrepancy sX n K₁ (QDivisor.toRDivisor D) E.valuation b) :
    IsLogDiscrepancy sX n K₂ (QDivisor.toRDivisor D) E.valuation b := by
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨ω, a', h'⟩ := exists_isQDiscrepancyWith hX hK₂ hD₂ E
  exact ⟨a', h'.isDiscrepancy hK₂ hD₂ hE, by rw [ha.eq (h'.isDiscrepancy hK₁ hD₁ hE)]⟩

/-- `𝒮_t(X, D; B)` does not depend on the canonical divisor. -/
private theorem smallLogDiscrepancySetOff_eq_of_isCanonicalDivisor (hX : IsNormalVariety k sX)
    {n : ℕ} {K₁ K₂ : Divisor X} {D : QDivisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
    (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
    (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier) (B : Closeds X) (t : ℚ) :
    smallLogDiscrepancySetOff sX n K₁ D hX hK₁ hD₁ B t =
      smallLogDiscrepancySetOff sX n K₂ D hX hK₂ hD₂ B t := by
  have key : ∀ {K₁ K₂ : Divisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
      (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
      (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier),
      smallLogDiscrepancySetOff sX n K₁ D hX hK₁ hD₁ B t ⊆
        smallLogDiscrepancySetOff sX n K₂ D hX hK₂ hD₂ B t := by
    rintro K₁ K₂ hK₁ hK₂ hD₁ hD₂ ν ⟨⟨hc, ⟨E, hE, rfl⟩, b, hb, hbt⟩, hoff⟩
    exact ⟨⟨hc, ⟨E, hE, rfl⟩, b,
      isLogDiscrepancy_of_isCanonicalDivisor hX hK₁ hK₂ hD₁ hD₂ hE hb, hbt⟩, hoff⟩
  exact (key hK₁ hK₂ hD₁ hD₂).antisymm (key hK₂ hK₁ hD₂ hD₁)

/-- Szabó's difficulty does not depend on the canonical divisor. -/
private theorem szaboDifficulty_eq_of_isCanonicalDivisor (hX : IsNormalVariety k sX)
    {n : ℕ} {K₁ K₂ : Divisor X} {D : QDivisor X} (hK₁ : K₁.IsCanonicalDivisor sX n)
    (hK₂ : K₂.IsCanonicalDivisor sX n) (hD₁ : (Divisor.toQDivisor K₁ + D).IsQCartier)
    (hD₂ : (Divisor.toQDivisor K₂ + D).IsQCartier) (B : Closeds X) (N : ℕ) (hN : 1 ≤ N)
    (c : ℚ) :
    szaboDifficulty sX n K₁ D hX hK₁ hD₁ B N hN c =
      szaboDifficulty sX n K₂ D hX hK₂ hD₂ B N hN c := by
  unfold szaboDifficulty
  simp_rw [smallLogDiscrepancySetOff_eq_of_isCanonicalDivisor hX hK₁ hK₂ hD₁ hD₂ B]

/-- A discrepancy `a(F, X, D)` of a divisor `F` of `k(X)` is computed on a proper divisor over
`X` with valuation `F`, on which `1 + a` is a log discrepancy. -/
private theorem exists_isLogDiscrepancy_of_isDiscrepancy {n : ℕ} {K : Divisor X}
    {D_X : RDivisor X} {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : MMP.Flips.IsDiscrepancy sX n K D_X F a) :
    ∃ E : ProperDivisorOver k sX, E.valuation = F ∧
      MMP.Intersection.IsLogDiscrepancy sX n D_X E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, rfl, hX, -, hω0, hLc, hL, L', hLpb, rfl⟩ := h
  refine ⟨E, hEF, hX, E.isProper, ω, hω0, ⟨_, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r, L,
    L', hLc, fun Γ => ?_, hLpb, by ring⟩
  have := congrArg (fun G : RDivisor X => G.coeff Γ) hL
  simp only [coeff_sum_smul_toRDivisor] at this
  rw [← this, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]

/-- A Kollár–Mori discrepancy depends only on the valuation of the divisor. -/
private theorem isDiscrepancy_of_valuation_eq (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {D D' : DivisorOver k sX} {a : ℚ}
    (ha : MMP.Mori.IsDiscrepancy sX n K Δ D a) (hv : D.valuation = D'.valuation) :
    MMP.Mori.IsDiscrepancy sX n K Δ D' a := by
  obtain ⟨-, hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := ha
  refine ⟨hX, hK, m, hm, hC, U,
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv ▸ hU, τ, hτ, ?_⟩
  rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
    hK.topologicalKrullDim_eq hv τ]

/-- Every exceptional divisor `E` over a canonical pair `(X, D)` has a discrepancy
`a(E, X, D) ≥ 0`. -/
private theorem exists_isDiscrepancy_nonneg_of_isCanonicalPair {n : ℕ} {K : Divisor X}
    {D : QDivisor X} (hD : IsCanonicalPair sX n K D)
    {E : ProperDivisorOver k sX} (hE : E.IsExceptional) :
    ∃ a : ℝ, 0 ≤ a ∧ MMP.Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation a := by
  obtain ⟨hXn, hK, -, hKD, hdisc⟩ := hD
  obtain ⟨ω, a, ha⟩ := exists_isQDiscrepancyWith hXn hK hKD E
  exact ⟨a, EReal.coe_nonneg.mp (hdisc.trans (sInf_le ⟨E, ω, a, hE, ha, rfl⟩)),
    ha.isDiscrepancy hK hKD hE⟩

end Discrepancy

/-! ### Flipped curves -/

/-- If `d + c = 3` with `d > 0`, then `c ≤ 2`. -/
private theorem le_two_of_add_eq_three {d : WithBot ℕ∞} {c : ℕ∞} (h : d + c = 3)
    (hd : 0 < d) : c ≤ 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    have h3 : e + c = 3 := WithBot.coe_injective h
    norm_cast at hd
    by_contra hc
    have h4 := add_le_add (Order.one_le_iff_pos.mpr hd) (Order.add_one_le_of_lt (not_le.mp hc))
    rw [h3] at h4
    exact absurd h4 (by decide)

/-- A dimension `d` with `d + 2 = 3` is `1`. -/
private theorem eq_one_of_add_two_eq_three {d : WithBot ℕ∞}
    (h : d + ((2 : ℕ∞) : WithBot ℕ∞) = 3) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have h3 : ((3 : ℕ∞) : WithBot ℕ∞) = 3 := rfl
      rw [← h3, ← WithBot.coe_add, WithBot.coe_inj] at h
      have : n + 2 = 3 := by exact_mod_cast h
      obtain rfl : n = 1 := by omega
      rfl

/-- A flipping curve `C` of a small contraction `φ⁺ : X⁺ ⟶ Z` of a threefold is an irreducible
closed subset of codimension two, whose generic point has coheight two and lies over a point of
`Z` of coheight three. -/
private theorem exists_irreducibleCloseds_of_isFlippingCurve {k : Type u} [Field k]
    {X' Z : Scheme.{u}} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φp : X' ⟶ Z}
    [IsIntegral X'] [LocallyOfFiniteType sX'] [IsIntegral Z] [LocallyOfFiniteType sZ]
    (hs : IsSmall k sZ sX' φp) (h3 : topologicalKrullDim X' = 3)
    {C : Set X'} (hC : IsFlippingCurve k sX' sZ φp C) :
    ∃ W : IrreducibleCloseds X', (W : Set X') = C ∧ IsGenericPoint W.isIrreducible.genericPoint C ∧
      codimension W = 2 ∧ Order.coheight W.isIrreducible.genericPoint = 2 ∧
      Order.coheight (φp W.isIrreducible.genericPoint) = 3 := by
  obtain ⟨-, -, -, -, z, hz, hCmax, hCdim⟩ := hC
  have hF : IsClosed {x : X' | φp x = z} := hz.preimage φp.continuous
  have hCcl : IsClosed C := closure_subset_iff_isClosed.mp
    (hCmax.2 ⟨hCmax.1.1.closure, closure_minimal hCmax.1.2 hF⟩ subset_closure)
  let W : IrreducibleCloseds X' := ⟨C, hCmax.1.1, hCcl⟩
  set ξ := W.isIrreducible.genericPoint
  have hξ : IsGenericPoint ξ C := by
    have h := W.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [W.isClosed.closure_eq] at h
  have hcod : codimension W = Order.coheight ξ := by
    have hEq : (irreducibleSetEquivPoints (α := X')).symm ξ = W := IrreducibleCloseds.ext hξ
    rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX' ξ
  rw [isGenericPoint_def.mp hξ, h3] at hd
  have hle := le_two_of_add_eq_three hd hCdim
  have hξz : φp ξ = z := hCmax.1.2 (hξ.mem)
  have hdz := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ z
  rw [hz.closure_eq, topologicalKrullDim_eq_zero_of_subsingleton, zero_add,
    ← hs.dim_eq, h3] at hdz
  have h3' : Order.coheight z = 3 :=
    WithBot.coe_injective (hdz.trans (WithBot.coe_ofNat 3).symm)
  obtain ⟨V, Wc, hV, hW, hVW, hρ⟩ := hs.exists_isIso
  have hξV : ξ ∈ V := by
    by_contra hξV
    let Vo : X'.Opens := V.compl
    let Wo : Z.Opens := Wc.compl
    let x' : Vo.toScheme := ⟨ξ, hξV⟩
    have e1 : Order.coheight (Vo.ι x') = Order.coheight x' :=
      Topology.IsOpenEmbedding.coheight_eq _ Vo.ι.isOpenEmbedding
    have e2 : Order.coheight ((φp.resLE Wo Vo hVW) x') = Order.coheight x' :=
      Topology.IsOpenEmbedding.coheight_eq _ (φp.resLE Wo Vo hVW).isOpenEmbedding
    have e3 : Order.coheight (Wo.ι ((φp.resLE Wo Vo hVW) x')) =
        Order.coheight ((φp.resLE Wo Vo hVW) x') :=
      Topology.IsOpenEmbedding.coheight_eq _ Wo.ι.isOpenEmbedding
    have e4 : Wo.ι ((φp.resLE Wo Vo hVW) x') = φp ξ := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
      rfl
    have hco : Order.coheight ξ = Order.coheight z := by
      rw [← hξz, ← e4, e3, e2, ← e1]
      rfl
    rw [hco, h3'] at hle
    exact absurd hle (by decide)
  have hge : 2 ≤ Order.coheight ξ := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV ξ hξV
  have h2 : Order.coheight ξ = 2 := le_antisymm hle hge
  exact ⟨W, rfl, hξ, hcod.trans h2, h2, hξz ▸ h3'⟩

/-- Over a small contraction `φ : X ⟶ Z` of a threefold, the closure of a point `x` of coheight
two lying over a point of coheight three of `Z` is a flipping curve of `φ`. -/
private theorem isFlippingCurve_closure_singleton {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ) (hX : topologicalKrullDim X = 3) {x : X}
    (hx : Order.coheight x = 2) (hφx : Order.coheight (φ x) = 3) :
    IsFlippingCurve k sX sZ φ (closure {x}) := by
  have hxEx : x ∈ MMP.Flips.exceptionalSet φ := by
    by_contra h
    have := MMP.Flips.coheight_map_of_notMem_exceptionalSet h
    rw [hφx, hx] at this
    exact absurd this (by decide)
  refine isFlippingCurve_of_subset_exceptionalSet hφ hX isIrreducible_singleton.closure
    isClosed_closure (eq_one_of_add_two_eq_three ?_)
    ((MMP.Flips.isClosed_exceptionalSet φ).closure_subset_iff.2 (Set.singleton_subset_iff.2 hxEx))
  simpa [hx, hX] using MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x

/-! ### Regularity along flipped curves -/

/-- **Positive discrepancies over a codimension-two point force regularity**, over any field of
characteristic zero. Let `X` be a normal variety over `k` with canonical divisor `K`, `B ≥ 0` a
`ℚ`-divisor with `K + B` `ℚ`-Cartier, and `W ⊆ X` an irreducible closed subset of codimension two.
If every exceptional divisor over `X` with centre `W` has positive discrepancy `a(D, X, B)`, then
`𝒪_{X,η_W}` is regular. -/
private theorem isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hpos : ∀ E : ProperDivisorOver k sX, E.IsExceptional → (E.center : Set X) = W →
      ∀ a : ℝ, MMP.Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) E.valuation a → 0 < a) :
    IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) := by
  classical
  have hP : IsPair sX B := ⟨hX, n, K, hK, hKB⟩
  have hPair : MMP.Fourfold.IsCharZeroPair sX B := ⟨inferInstance, hP, hB⟩
  set x := W.isIrreducible.genericPoint
  have hxW : closure {x} = (W : Set X) := W.isIrreducible.isGenericPoint_genericPoint_closure.trans
    W.isClosed.closure_eq
  have hcx : Order.coheight x = 2 := by
    have hEq : (irreducibleSetEquivPoints (α := X)).symm x = W := IrreducibleCloseds.ext hxW
    rw [← hW, codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have hdim := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hxW, hcx, hK.topologicalKrullDim_eq] at hdim
  obtain ⟨d, rfl, hWd⟩ : ∃ d : ℕ, n = d + 2 ∧ topologicalKrullDim (W : Set X) = d := by
    revert hdim
    induction topologicalKrullDim (W : Set X) using WithBot.recBotCoe with
    | bot => simp
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => intro h; norm_cast at h
      | coe m => exact fun h => ⟨m, by exact_mod_cast h.symm, rfl⟩
  obtain ⟨U, -, φ, -, -, S, ι, sS, -, _, _, _, _, hSa, hSft, hSnv, hSdim, p, hp, -, hgen,
    hiso, -, -, BS, hBS, hBS0, -, hbij, hlog⟩ :=
    MMP.Fourfold.exists_genericFibre_bijOn_valuation_center sX hPair hK.topologicalKrullDim_eq
      W hWd
  by_contra hreg
  have hsing : p ∉ smoothLocus sS := by
    intro hps
    apply hreg
    obtain ⟨V, hpV, hV⟩ := mem_smoothLocus_iff.mp hps
    have : Smooth (V.ι ≫ sS) := hV
    have hrV := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sS) ⟨p, hpV⟩
    have hrS : IsRegularLocalRing (S.presheaf.stalk p) :=
      IsRegularLocalRing.of_ringEquiv (V.stalkIso ⟨p, hpV⟩).commRingCatIsoToRingEquiv
    have hrU : IsRegularLocalRing ((U : Scheme).presheaf.stalk (ι p)) :=
      IsRegularLocalRing.of_ringEquiv (asIso (ι.stalkMap p)).symm.commRingCatIsoToRingEquiv
    have hrX : IsRegularLocalRing (X.presheaf.stalk (U.ι (ι p))) :=
      IsRegularLocalRing.of_ringEquiv (U.stalkIso (ι p)).commRingCatIsoToRingEquiv
    have hxe : U.ι (ι p) = x := hgen.eq hxW
    rwa [hxe] at hrX
  have : IsQuasiProjectiveVariety _ sS := by
    have : AlgebraicGeometry.IsVariety _ sS := hSnv.1
    exact ⟨Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom sS inferInstance⟩
  have : CharZero (FractionRing (MvPolynomial (Fin d) k)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (FractionRing (MvPolynomial (Fin d) k))).injective
  obtain ⟨D, hDproj, -, hDc, a, ha1, ha⟩ :=
    MMP.Threefold.exists_isLogDiscrepancy_le_one_of_notMem_smoothLocus sS hSdim
      ⟨inferInstance, hBS, hBS0⟩ hp hsing
  have hξ : D.valuation ∈ {ξ | ∃ D : DivisorOver (FractionRing (MvPolynomial (Fin d) k)) sS,
      D.valuation = ξ ∧ (D.center : Set S) = {p}} := ⟨D, rfl, hDc⟩
  obtain ⟨D₂, hD₂v, hD₂c⟩ := hbij.mapsTo hξ
  obtain ⟨n', D₁, hD₁p, hD₁v, hD₁⟩ :=
    (hlog _ hξ a).mp ⟨2, D, isProper_of_isProjectiveMorphism D.f hDproj, rfl, ha⟩
  have hD₁c : D₁.center = W :=
    (MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 (hD₁v.trans hD₂v.symm)).trans hD₂c
  let E : ProperDivisorOver k sX := ⟨D₁, hD₁p⟩
  have hEc : (E.center : Set X) = W := by
    rw [ProperDivisorOver.center_eq_toDivisorOver_center]
    exact congrArg (fun V : IrreducibleCloseds X => (V : Set X)) hD₁c
  have hEe : E.IsExceptional := by
    change topologicalKrullDim (E.center : Set X) + 2 ≤ topologicalKrullDim X
    rw [hEc, hWd, hK.topologicalKrullDim_eq]
    norm_cast
  obtain ⟨_, b, hb⟩ := exists_isQDiscrepancyWith hX hK hKB E
  replace hb := hb.isDiscrepancy hK hKB hEe
  obtain ⟨E₁, hE₁v, hlog₁⟩ := exists_isLogDiscrepancy_of_isDiscrepancy hb
  have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₁ hD₁ hE₁v
  have h2 := hpos E hEe hEc b hb
  linarith

/-- For birational `φ : X ⟶ Z` and `φp : X' ⟶ Z`, valuations of `k(X')` correspond injectively
to valuations of `k(X)` with the same restriction to `k(Z)`. -/
theorem exists_injective_comap_functionFieldMap_eq {X Z X' : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] [IsIntegral X'] {φ : X ⟶ Z} {φp : X' ⟶ Z} [IsDominant φ] [IsDominant φp]
    (hφ : Mori.IsBirationalMorphism φ) (hφp : Mori.IsBirationalMorphism φp) :
    ∃ F : Valuation X'.functionField ℤᵐ⁰ → Valuation X.functionField ℤᵐ⁰,
      Function.Injective F ∧
        ∀ ν', (F ν').comap (functionFieldMap φ) = ν'.comap (functionFieldMap φp) := by
  let eφ := RingEquiv.ofBijective (functionFieldMap φ) hφ.functionFieldMap_bijective
  have hF : ∀ ν' : Valuation X'.functionField ℤᵐ⁰,
      ((ν'.comap (functionFieldMap φp)).comap eφ.symm.toRingHom).comap (functionFieldMap φ) =
        ν'.comap (functionFieldMap φp) :=
    fun ν' => Valuation.ext fun t => by
      change ν' (functionFieldMap φp (eφ.symm (eφ t))) = _
      rw [RingEquiv.symm_apply_apply]
      rfl
  refine ⟨fun ν' => (ν'.comap (functionFieldMap φp)).comap eφ.symm.toRingHom,
    fun ν₁ ν₂ h => ?_, hF⟩
  have h' : ν₁.comap (functionFieldMap φp) = ν₂.comap (functionFieldMap φp) := by
    rw [← hF ν₁, ← hF ν₂]
    exact congrArg _ h
  ext x
  obtain ⟨y, rfl⟩ := hφp.functionFieldMap_bijective.2 x
  exact congrArg (fun v : Valuation Z.functionField ℤᵐ⁰ => v y) h'

/-- Every exceptional divisor over `X⁺` whose center is a flipped curve has positive discrepancy
with respect to `(X⁺, g_*D)`. -/
private theorem discrepancy_pos_of_isFlippedCurveOf {k : Type u} [Field k] [PerfectField k]
    {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX'] {n : ℕ} {K : Divisor X}
    {D : QDivisor X} (hD : MMP.Flips.IsCanonicalPair sX n K D) {φ : X ⟶ Z} {φp : X' ⟶ Z}
    {g : X.RationalMap X'} {C : Set X'}
    (hC : IsFlippedCurveOf k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g C)
    {E : ProperDivisorOver k sX'} (hE : E.IsExceptional) (hEC : (E.center : Set X') = C)
    {a : ℝ} (ha : MMP.Flips.IsDiscrepancy sX' n (MMP.Mori.RationalMap.transformDivisor g K)
      (QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor g D)) E.valuation a) :
    0 < a := by
  have hflip := hC.1
  have hφs : IsSmall k sZ sX φ := hflip.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hflip.isSmall
  have hZn : IsNormalVariety k sZ := hflip.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  haveI : IsDominant φ := hbφ.isDominant
  haveI : IsDominant φp := hbφp.isDominant
  obtain ⟨hX, hK, -, hKD, -⟩ := id hD
  obtain ⟨F, -, hF⟩ := exists_injective_comap_functionFieldMap_eq hbφ hbφp
  have hν := hF E.valuation
  obtain ⟨-, Ex, hExv, hExe⟩ := ((exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp
    hφs hφps).1 _ E.valuation hν).mpr ⟨ha.2.2.1, E, rfl, hE⟩
  obtain ⟨a₀, h0, ha₀⟩ := exists_isDiscrepancy_nonneg_of_isCanonicalPair hD hExe
  rw [hExv] at ha₀
  exact h0.trans_lt (hC.isDiscrepancy_lt hX hK hKD E hEC hν ha₀ ha)

/-- Let `(X, D)` be a canonical pair, `X` a threefold over a field of characteristic zero with
canonical divisor `K`, and `φ⁺ : X⁺ ⟶ Z` a flip of the small contraction `φ : X ⟶ Z` with respect
to `K_X + D` (so `-(K_X + D)` is `φ`-ample), with birational map `g`. If `C ⊆ X⁺` is a flipped
curve, then the local ring of `X⁺` at the generic point of `C` is regular. -/
@[mmp "lem_fa4_flipped_curve_smooth_generic_point"]
public theorem isRegularLocalRing_stalk_of_isFlippedCurveOf {k : Type} [Field k] [CharZero k]
    {X Z X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace X'] {K : Divisor X} {D : QDivisor X} (hD : IsCanonicalPair sX 3 K D)
    {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'} {C : Set X'}
    (hC : IsFlippedCurveOf k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g C)
    {ξ : X'} (hξ : IsGenericPoint ξ C) :
    IsRegularLocalRing (X'.presheaf.stalk ξ) := by
  obtain ⟨hflip, hcurve⟩ := id hC
  have hX'n : IsNormalVariety k sX' := hflip.isNormalVariety_flip
  have hZn : IsNormalVariety k sZ := hflip.isNormalVariety_target
  haveI : IsIntegral X' := hX'n.1.toIsIntegral
  haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  obtain ⟨-, hK', hD'eff, hKD', -⟩ := MMP.Flips.IsCanonicalPair.of_isFlip hD hflip
  obtain ⟨W, hWC, hgen, hW, -, -⟩ := exists_irreducibleCloseds_of_isFlippingCurve hflip.isSmall
    hK'.topologicalKrullDim_eq hcurve
  rw [hξ.eq hgen]
  refine isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos hX'n hK'
    hD'eff hKD' hW ?_
  intro E hE hEc a ha
  exact discrepancy_pos_of_isFlippedCurveOf hD hC hE (hEc.trans hWC) ha

/-! ### Centers of divisors over a small contraction -/

section Center

/-- If the valuation ring of `w` dominates the local ring of `X` at `x`, the valuation ring of
`w ∘ φ^*` dominates the local ring of `Z` at `φ(x)`, for a dominant `φ : X ⟶ Z`. -/
private theorem dominates_map {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] (φ : X ⟶ Z)
    [IsDominant φ] (w : Valuation X.functionField ℤᵐ⁰) {x : X}
    (h1 : ∀ a : X.presheaf.stalk x, w (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      w (algebraMap _ X.functionField a) < 1) :
    (∀ a : Z.presheaf.stalk (φ x),
      w.comap (functionFieldMap φ) (algebraMap _ Z.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk (φ x)),
      w.comap (functionFieldMap φ) (algebraMap _ Z.functionField a) < 1 := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h1 _
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))

/-- Divisors over `X` and `X'` whose valuations agree on `k(Z)` have centers over the same point
of the separated scheme `Z`. -/
private theorem map_eq_of_comap_eq {k : Type u} [Field k] {X X' Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (sZ : Z ⟶ Spec (.of k)) [IsSeparated sZ] (φ : X ⟶ Z)
    (φ' : X' ⟶ Z) [IsDominant φ] [IsDominant φ'] (E : DivisorOver k sX) (E' : DivisorOver k sX')
    (hv : E.valuation.comap (functionFieldMap φ) = E'.valuation.comap (functionFieldMap φ')) :
    φ (E.f E.E.genericPoint) = φ' (E'.f E'.E.genericPoint) := by
  obtain ⟨d1, d2⟩ := dominates_map φ E.valuation
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E _ rfl)
  obtain ⟨d1', d2'⟩ := dominates_map φ' E'.valuation
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E' _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E' _ rfl)
  rw [← hv] at d1' d2'
  exact MMP.Positivity.DivisorOver.eq_of_dominates sZ _ d1 d2 d1' d2'

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)}

/-- The center of a proper divisor over `X` is the closure of the point `f(η_E)`. -/
private theorem coe_center_eq_closure (E : ProperDivisorOver k sX) :
    (E.center : Set X) = closure {E.f E.E.genericPoint} := by
  rw [E.center_eq_toDivisorOver_center]
  exact E.toDivisorOver.center_eq_closure_genericPoint

/-- The codimension of the center of a proper divisor over `X` is the coheight of `f(η_E)`. -/
private theorem codimension_center (E : ProperDivisorOver k sX) :
    codimension E.center = Order.coheight (E.f E.E.genericPoint) := by
  rw [E.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center]

end Center

/-! ### Multiplicities along a curve -/

/-- The ideal of a prime divisor at a point of an integral scheme is nonzero. -/
private theorem stalkIdeal_ne_bot {X : Scheme} [IsIntegral X] (D : MMP.Mori.PrimeDivisor X)
    (x : X) : D.idealSheaf.stalkIdeal x ≠ ⊥ := by
  have hD : D.idealSheaf ≠ ⊥ := by
    intro h0
    have hsupp : D.support = Set.univ := by
      change ((D.idealSheaf.support : Set X)) = _
      rw [h0, Scheme.IdealSheafData.support_bot]; rfl
    have hgen : IsGenericPoint D.genericPoint (Set.univ : Set X) := by
      rw [← hsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
    have h1 := D.coheight_genericPoint
    have h2 : Order.coheight D.genericPoint = 0 := by
      rw [Order.coheight_eq_zero]
      intro b hb
      have hb' : b ⤳ D.genericPoint := hb
      have hbgen : IsGenericPoint b (Set.univ : Set X) := by
        refine (isGenericPoint_iff_specializes).mpr fun w => ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
        exact hb'.trans (hgen.specializes (Set.mem_univ w))
      exact (hbgen.eq hgen).symm ▸ le_rfl
    rw [h2] at h1
    exact absurd h1 (by decide)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hne := Stacks.IdealSheaf.ideal_ne_bot D.idealSheaf hD (U := ⟨V, hV⟩) hxV
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro h0
  have h1 := D.idealSheaf.germ_mem_stalkIdeal ⟨V, hV⟩ hxV hg
  rw [h0, Ideal.mem_bot] at h1
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact hg0 (germ_injective_of_isIntegral X x hxV (h1.trans (map_zero _).symm))

/-- A prime divisor through the generic point of `W` has finite positive multiplicity along `W`
(Krull's intersection theorem in the noetherian local ring at `η_W`). -/
private theorem one_le_toNat_multiplicityAlong {Y : Scheme} [IsIntegral Y]
    [IsLocallyNoetherian Y] (P : MMP.Mori.PrimeDivisor Y) (W : IrreducibleCloseds Y)
    (h : W.isIrreducible.genericPoint ∈ (P.support : Set Y)) :
    1 ≤ (P.multiplicityAlong W).toNat := by
  set R := Y.presheaf.stalk W.isIrreducible.genericPoint
  set I := P.idealSheaf.stalkIdeal W.isIrreducible.genericPoint
  have hI0 : I ≠ ⊥ := stalkIdeal_ne_bot P _
  have hIm : I ≤ IsLocalRing.maximalIdeal R :=
    P.idealSheaf.stalkIdeal_le_maximalIdeal_of_mem_support h
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ¬ I ≤ IsLocalRing.maximalIdeal R ^ s := by
    by_contra! hall
    apply hI0
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
    exact le_iInf hall
  have hle : P.multiplicityAlong W ≤ s := iSup₂_le fun t ht => by
    have : t < s := by
      by_contra! hst
      exact hs (ht.trans (Ideal.pow_le_pow_right hst))
    exact_mod_cast this.le
  have h1 : (1 : ℕ∞) ≤ P.multiplicityAlong W :=
    le_iSup₂_of_le (f := fun (s : ℕ) (_ : I ≤ IsLocalRing.maximalIdeal R ^ s) => (s : ℕ∞)) 1
      (by simpa using hIm) le_rfl
  have hne : P.multiplicityAlong W ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top s) hle
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at h1 ⊢
  rw [ENat.toNat_coe]
  exact_mod_cast h1

/-- The multiplicity `mult_W Δ = ∑_Γ Δ_Γ · mult_W Γ` of an effective `ℚ`-divisor along `W` is
nonnegative. -/
private theorem sum_mul_multiplicityAlong_nonneg {Y : Scheme} {Δ : QDivisor Y}
    (hΔ : ∀ Γ, 0 ≤ Δ.coeff Γ) (W : IrreducibleCloseds Y) :
    0 ≤ Δ.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) :=
  Finset.sum_nonneg fun Γ _ => mul_nonneg (hΔ Γ) (Nat.cast_nonneg _)

/-- If `W` lies in a prime divisor `Q` with `c ≤ Δ_Q`, for an effective `ℚ`-divisor `Δ` and
`c ≥ 0`, then `c ≤ mult_W Δ`. -/
private theorem le_sum_mul_multiplicityAlong {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    {Δ : QDivisor Y} (hΔ : ∀ Γ, 0 ≤ Δ.coeff Γ) (W : IrreducibleCloseds Y) {c : ℚ} (hc : 0 ≤ c)
    {Q : MMP.Mori.PrimeDivisor Y} (hcQ : c ≤ Δ.coeff Q)
    (hW : W.isIrreducible.genericPoint ∈ (Q.support : Set Y)) :
    c ≤ Δ.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) := by
  by_cases hQ : Q ∈ Δ.support
  · have h1 : (1 : ℚ) ≤ ((Q.multiplicityAlong W).toNat : ℚ) := by
      exact_mod_cast one_le_toNat_multiplicityAlong Q W hW
    calc c ≤ Δ.coeff Q * 1 := by rwa [mul_one]
      _ ≤ Δ Q * ((Q.multiplicityAlong W).toNat : ℚ) :=
          mul_le_mul_of_nonneg_left h1 (hc.trans hcQ)
      _ ≤ _ := Finset.single_le_sum (f := fun Γ => Δ Γ * ((Γ.multiplicityAlong W).toNat : ℚ))
          (fun Γ _ => mul_nonneg (hΔ Γ) (Nat.cast_nonneg _)) hQ
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hQ] at hcQ
    exact hcQ.trans (sum_mul_multiplicityAlong_nonneg hΔ W)

/-! ### Sums in `ℕ∞` -/

/-- Every family in `ℕ∞` is summable, with sum the supremum of its finite partial sums. -/
private theorem summable_enat {ι : Type*} (f : ι → ℕ∞) : Summable f :=
  (hasSum_of_isLUB _ (isLUB_iSup (f := fun s : Finset ι => ∑ i ∈ s, f i))).summable

/-- In `ℕ∞`, a pointwise inequality `f ≤ g` gives `∑ f ≤ ∑ g`. -/
private theorem tsum_le_tsum_enat {ι : Type*} {f g : ι → ℕ∞} (h : ∀ i, f i ≤ g i) :
    ∑' i, f i ≤ ∑' i, g i :=
  Summable.tsum_le_tsum h (summable_enat f) (summable_enat g)

/-- In `ℕ∞`, a pointwise inequality `f ≤ g` which is strict at one index gives a strict
inequality of sums, as soon as `∑ g` is finite. -/
private theorem tsum_lt_tsum_enat {ι : Type*} {f g : ι → ℕ∞} (h : ∀ i, f i ≤ g i) {i : ι}
    (hi : f i < g i) (hg : ∑' j, g j ≠ ⊤) : ∑' j, f j < ∑' j, g j := by
  classical
  rw [Summable.tsum_eq_add_tsum_ite' (f := g) i (summable_enat _)] at hg ⊢
  rw [Summable.tsum_eq_add_tsum_ite' (f := f) i (summable_enat _)]
  have hR : (∑' j, if j = i then 0 else f j) ≤ ∑' j, if j = i then 0 else g j :=
    tsum_le_tsum_enat fun j => by split_ifs <;> simp [h j]
  generalize (∑' j, if j = i then 0 else f j) = r at *
  generalize (∑' j, if j = i then 0 else g j) = s at *
  generalize f i = a at *
  generalize g i = b at *
  have hgi : b ≠ ⊤ := fun h' => hg (by rw [h', top_add])
  have hRg : s ≠ ⊤ := fun h' => hg (by rw [h', add_top])
  have hfi : a ≠ ⊤ := ne_top_of_lt hi
  have hRf : r ≠ ⊤ := ne_top_of_le_ne_top hRg hR
  lift a to ℕ using hfi
  lift b to ℕ using hgi
  lift r to ℕ using hRf
  lift s to ℕ using hRg
  norm_cast at hi hR ⊢
  omega

/-- Termwise injections `F : s_i ↪ t_i`, one of which misses a point, give
`∑ #s_i < ∑ #t_i` in `ℕ∞`, as soon as `∑ #t_i` is finite. -/
private theorem tsum_encard_lt_tsum_encard {ι α β : Type*} {s : ι → Set α} {t : ι → Set β}
    {F : α → β} (hF : Function.Injective F) (h : ∀ i, Set.MapsTo F (s i) (t i))
    (hfin : ∑' i, (t i).encard ≠ ⊤) {i : ι} {a : α} (ha : a ∉ s i) (hFa : F a ∈ t i) :
    ∑' i, (s i).encard < ∑' i, (t i).encard := by
  refine tsum_lt_tsum_enat (fun i => Set.encard_le_encard_of_injOn (h i) hF.injOn) (i := i) ?_ hfin
  have hsub : F '' s i ⊂ t i := Set.ssubset_iff_subset_ne.2 ⟨(h i).image_subset, fun he => ha <|
    by obtain ⟨b, hb, hba⟩ : F a ∈ F '' s i := he ▸ hFa; exact hF hba ▸ hb⟩
  have hfinS : (t i).Finite := Set.encard_ne_top_iff.mp
    (ne_top_of_le_ne_top hfin ((summable_enat fun i => (t i).encard).le_tsum i fun _ _ => zero_le'))
  rw [← hF.injOn.encard_image]
  exact (hfinS.subset hsub.subset).encard_lt_encard hsub

/-! ### Prime divisors under a flip -/

/-- If the transform of prime divisors under `g` is given by a bijection `e`, the transform of a
divisor has coefficient `D.coeff P` at `e P`. -/
private theorem coeff_transformDivisor_apply {X Y : Scheme} {R : Type*} [AddCommMonoid R]
    {g : X.RationalMap Y} (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor Y)
    (he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P))
    (D : DivisorWithCoeffs R X) (P : Mori.PrimeDivisor X) :
    (Mori.RationalMap.transformDivisor g D).coeff (e P) = D.coeff P := by
  have h : Mori.RationalMap.transformDivisor g D = Finsupp.mapDomain e D := by
    induction D using Finsupp.induction_linear with
    | zero => simp
    | add D D' h h' => rw [map_add, h, h', Finsupp.mapDomain_add]
    | single P r =>
      rw [Mori.RationalMap.transformDivisor_single_of_eq_some (he P), Finsupp.mapDomain_single]
  rw [h]
  exact Finsupp.mapDomain_apply_of_injective e.injective D P

section Flip

variable {k : Type} [Field k] [CharZero k] {X Z X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X'] [IsLocallyNoetherian X']
  [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX']

/-- Under a flip, the transform of prime divisors is a bijection. -/
private theorem exists_equiv_transformPrimeDivisor_eq {E : RDivisor X} {φ : X ⟶ Z}
    {φp : X' ⟶ Z} {g : X.RationalMap X'} (hφ : IsFlip k sX sZ sX' E φ φp g) :
    ∃ e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor X',
      ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P) := by
  have hφs : IsSmall k sZ sX φ := hφ.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hφ.isSmall
  haveI : IsIntegral Z := hφ.isNormalVariety_target.1.toIsIntegral
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  haveI : IsDominant φ := hbφ.isDominant
  haveI : IsDominant φp := hbφp.isDominant
  have he := (exceptional_hasNonemptyCenter_iff_of_isSmall _ _ sZ φ φp hφs hφps).2 g
    hφ.isModificationOf
  set e := primeDivisorEquivOfModification hφs hφps hφ.isModificationOf
  exact ⟨e, fun P => (he P).1⟩

/-- Under a flip, every prime divisor `Q` of `X⁺` is the transform of a prime divisor `P` of `X`,
and every divisor `g_* D` has coefficient `D.coeff P` at `Q`. -/
private theorem exists_transformPrimeDivisor_eq_and_coeff {E : RDivisor X} {φ : X ⟶ Z}
    {φp : X' ⟶ Z} {g : X.RationalMap X'} (hφ : IsFlip k sX sZ sX' E φ φp g)
    (Q : Mori.PrimeDivisor X') :
    ∃ P : Mori.PrimeDivisor X, Mori.RationalMap.transformPrimeDivisor g P = some Q ∧
      ∀ D : QDivisor X, (Mori.RationalMap.transformDivisor g D).coeff Q = D.coeff P := by
  obtain ⟨e, he⟩ := exists_equiv_transformPrimeDivisor_eq hφ
  refine ⟨e.symm Q, by simpa using he (e.symm Q), fun D => ?_⟩
  simpa using coeff_transformDivisor_apply e he D (e.symm Q)

/-- Under a flip of a canonical pair `(X, D)`, `(X⁺, g_* D)` is a canonical pair with respect to
any canonical divisor `K⁺` of `X⁺`. -/
private theorem isCanonicalPair_transformDivisor {K : Divisor X} {D : QDivisor X}
    {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'} (hD : Flips.IsCanonicalPair sX 3 K D)
    (hφ : IsFlip k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g)
    {K' : Divisor X'} (hK' : K'.IsCanonicalDivisor sX' 3) :
    Flips.IsCanonicalPair sX' 3 K' (Mori.RationalMap.transformDivisor g D) := by
  obtain ⟨hX', hK, hDeff, hKD, hdisc⟩ := hD.of_isFlip hφ
  exact ⟨hX', hK', hDeff, hKD.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX' hK hK'), hdisc⟩

/-- Szabó's difficulty depends on the divisor only, not on the proofs of its hypotheses. -/
private theorem szaboDifficulty_congr {K : Divisor X} {D₁ D₂ : QDivisor X} (h : D₁ = D₂)
    {hX : IsNormalVariety k sX} {hK : K.IsCanonicalDivisor sX 3}
    {hD₁ : (Divisor.toQDivisor K + D₁).IsQCartier} {hD₂ : (Divisor.toQDivisor K + D₂).IsQCartier}
    {B : Closeds X} {N : ℕ} {hN : 1 ≤ N} {c : ℚ} :
    szaboDifficulty sX 3 K D₁ hX hK hD₁ B N hN c =
      szaboDifficulty sX 3 K D₂ hX hK hD₂ B N hN c := by
  subst h
  rfl

end Flip

/-! ### Szabó's difficulty under one flip -/

/-- If `N Δ` is integral, then `N · Σ_Γ Δ_Γ mult_W Γ` is an integer. -/
theorem exists_int_eq_nat_mul_sum_mul_multiplicityAlong {Y : Scheme} {Δ : QDivisor Y} {N : ℕ}
    (hN : ∀ Γ, ∃ m : ℤ, (N : ℚ) * Δ.coeff Γ = m)
    (W : IrreducibleCloseds Y) :
    ∃ n : ℤ, (n : ℚ) = N * Δ.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) := by
  choose m hm using hN
  refine ⟨Δ.support.sum fun Γ => m Γ * ((Γ.multiplicityAlong W).toNat : ℤ), ?_⟩
  rw [Finsupp.sum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun Γ _ => ?_
  rw [← hm Γ, DivisorWithCoeffs.coeff_apply]
  ring

/-- Let `X` be a normal threefold with canonical divisor `K`, `Δ` a `ℚ`-divisor with `K + Δ`
`ℚ`-Cartier, and `C = W` a closed set of codimension two at whose generic point `X` is regular.
Then there is an exceptional proper divisor `E` over `X` (the blow-up divisor `E_C`, up to
valuation) with centre `C`, `f(η_E) = η_W` and `a(E, X, Δ) = 1 - Σ_Γ Δ_Γ mult_W Γ`. -/
theorem exists_isDiscrepancy_blowUp_eq_one_sub_sum_mul_multiplicityAlong {k : Type} [Field k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3) {Δ : QDivisor X}
    (hKΔ : (Divisor.toQDivisor K + Δ).IsQCartier) {W : IrreducibleCloseds X} {C : Set X}
    (hWC : IsGenericPoint W.isIrreducible.genericPoint C) (hW : codimension W = 2)
    (h2 : Order.coheight W.isIrreducible.genericPoint = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    ∃ (E : ProperDivisorOver k sX) (a : ℚ), E.f E.E.genericPoint = W.isIrreducible.genericPoint ∧
      (E.center : Set X) = C ∧ E.IsExceptional ∧
      MMP.Flips.IsDiscrepancy sX 3 K (QDivisor.toRDivisor Δ) E.valuation a ∧
      (a : ℝ) = 1 - ((Δ.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) : ℚ) : ℝ) := by
  set ξ := W.isIrreducible.genericPoint
  set μ : ℚ := Δ.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ)
  obtain ⟨D₀, j, hj, hjf, hD₀E⟩ :=
    (MMP.Flips.valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp_of_charZero
      sX hX W (by rw [hW]) hreg).1
  haveI := hj
  have hD₀ : MMP.Mori.IsDiscrepancy sX 3 K Δ D₀ (((2 : ℕ) : ℚ) - 1 - μ) :=
    MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero
      sX hX hK Δ hKΔ W (by rw [hW]; rfl) le_rfl hreg D₀ j hjf hD₀E
  obtain ⟨E, hEv⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D₀
  have hEξ : E.f E.E.genericPoint = ξ :=
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hEv).trans hD₀E
  have hEC : (E.center : Set X) = C := by
    rw [coe_center_eq_closure, hEξ]
    exact isGenericPoint_def.mp hWC
  have hEexc : E.IsExceptional := by
    have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX ξ
    rw [isGenericPoint_def.mp hWC, h2] at hd
    change topologicalKrullDim (E.center : Set X) + 2 ≤ topologicalKrullDim X
    rw [hEC, ← hd]
    rfl
  obtain ⟨ω, a, hq⟩ := exists_isQDiscrepancyWith hX hK hKΔ E
  have hdisc := hq.isDiscrepancy hK hKΔ hEexc
  obtain ⟨E', hE'v, hlog'⟩ := exists_isLogDiscrepancy_of_isDiscrepancy hdisc
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
    (isDiscrepancy_of_valuation_eq hX hD₀ hEv.symm) E.isProper
  refine ⟨E, a, hEξ, hEC, hEexc, hdisc, ?_⟩
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog' hlog hE'v
  push_cast at this
  linarith

/-- Let `(X, D)` be a canonical pair, `X` a threefold over a field of characteristic zero with
canonical divisor `K`, with `⌊D⌋ = 0`; let `N ≥ 1` with `N D` integral, `c ≥ 0` rational, and
`B = ⋃_{P ∈ S} P` a finite union of prime divisors containing every prime divisor `P` with
`D.coeff P > c`. Let `φ⁺ : X⁺ ⟶ Z` be a flip of `φ : X ⟶ Z` with respect to `K_X + D` with
birational map `g`, `D⁺ = g_* D`, `B⁺ = ⋃_{P ∈ S} g_* P`, and `K⁺` a canonical divisor of `X⁺`.
If no flipping curve of `φ` is contained in `B`, then `K_{X⁺} + D⁺` is `ℚ`-Cartier,
`d_{N,c}(X⁺, D⁺; B⁺) ≤ d_{N,c}(X, D; B) < ∞`, and the first inequality is strict as soon as some
flipped curve `C` satisfies `c = 0` or `C ⊆ g_* P` for a prime divisor `P` with `c ≤ D.coeff P`. -/
@[mmp "lem_fa4_szabo_difficulty_drops"]
public theorem szaboDifficulty_flip_le {k : Type} [Field k] [CharZero k]
    {X Z X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX']
    {K : Divisor X} {D : QDivisor X} (hD : IsCanonicalPair sX 3 K D)
    (hDfloor : DivisorWithCoeffs.roundDown D = 0)
    {N : ℕ} (hN : 1 ≤ N) (hND : ∀ P, ∃ m : ℤ, (N : ℚ) * D.coeff P = m)
    {c : ℚ} (hc : 0 ≤ c) {S : Finset (Mori.PrimeDivisor X)} {B : Closeds X}
    (hB : (B : Set X) = ⋃ P ∈ S, (P.support : Set X))
    (hBD : ∀ P : Mori.PrimeDivisor X, c < D.coeff P → (P.support : Set X) ⊆ B)
    {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hφ : IsFlip k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g)
    {B' : Closeds X'}
    (hB' : (B' : Set X') =
      ⋃ P ∈ S, ⋃ Q ∈ Mori.RationalMap.transformPrimeDivisor g P, (Q.support : Set X'))
    (hnc : ∀ C : Set X, IsFlippingCurve k sX sZ φ C → ¬ C ⊆ B)
    {K' : Divisor X'} (hK' : K'.IsCanonicalDivisor sX' 3) :
    ∃ hD' : (Divisor.toQDivisor K' + Mori.RationalMap.transformDivisor g D).IsQCartier,
      szaboDifficulty sX' 3 K' (Mori.RationalMap.transformDivisor g D)
          hφ.isNormalVariety_flip hK' hD' B' N hN c ≤
        szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c ∧
      szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c < ⊤ ∧
      ((∃ C : Set X', IsFlippedCurveOf k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D))
          φ φp g C ∧ (c = 0 ∨ ∃ P : Mori.PrimeDivisor X, c ≤ D.coeff P ∧
            ∃ Q ∈ Mori.RationalMap.transformPrimeDivisor g P, C ⊆ (Q.support : Set X'))) →
        szaboDifficulty sX' 3 K' (Mori.RationalMap.transformDivisor g D)
            hφ.isNormalVariety_flip hK' hD' B' N hN c <
          szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c) := by
  have hφs : IsSmall k sZ sX φ := hφ.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hφ.isSmall
  have hZn : IsNormalVariety k sZ := hφ.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  haveI : IsDominant φ := hbφ.isDominant
  haveI : IsDominant φp := hbφp.isDominant
  obtain ⟨hX, hK, -, hKD, -⟩ := id hD
  have hX'n : IsNormalVariety k sX' := hφ.isNormalVariety_flip
  obtain ⟨hKp, hKDp, hmain⟩ :=
    smallLogDiscrepancySetOff_subset_of_isFlip hX hK hKD hφ S B B' hB hB' hnc
  have hD' := hKDp.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'n hKp hK')
  refine ⟨hD', ?_⟩
  rw [szaboDifficulty_eq_of_isCanonicalDivisor hX'n hK' hKp hD' hKDp]
  obtain ⟨F, hFinj, hF⟩ := exists_injective_comap_functionFieldMap_eq hbφ hbφp
  let Sp : ℚ → Set (Valuation X'.functionField ℤᵐ⁰) := fun t =>
    smallLogDiscrepancySetOff sX' 3 (Mori.RationalMap.transformDivisor g K)
      (Mori.RationalMap.transformDivisor g D) hX'n hKp hKDp B' t
  let S₀ : ℚ → Set (Valuation X.functionField ℤᵐ⁰) := fun t =>
    smallLogDiscrepancySetOff sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B t
  have hmaps : ∀ t, Set.MapsTo F (Sp t) (S₀ t) := fun t ν' h => (hmain t ν' h).2 _ (hF ν')
  have hfin : szaboDifficulty sX 3 K D hD.1 hD.2.1 hD.2.2.2.1 B N hN c ≠ ⊤ :=
    hD.szaboDifficulty_ne_top_of_charZero hDfloor hN hc hBD
  unfold szaboDifficulty at hfin ⊢
  refine ⟨tsum_le_tsum_enat fun _ => Set.encard_le_encard_of_injOn (hmaps _) hFinj.injOn,
    hfin.lt_top, ?_⟩
  rintro ⟨C, hC, hcond⟩
  suffices hstrict : ∃ i : {i : ℤ // (N : ℚ) * c ≤ i}, ∃ ν', ν' ∉ Sp (2 - (i : ℚ) / N) ∧
      F ν' ∈ S₀ (2 - (i : ℚ) / N) by
    obtain ⟨i, ν', hν'S, hν'⟩ := hstrict
    exact tsum_encard_lt_tsum_encard hFinj (fun _ => hmaps _) hfin hν'S hν'
  obtain ⟨-, hCcurve⟩ := id hC
  have h3' : topologicalKrullDim X' = 3 := by exact_mod_cast hKp.topologicalKrullDim_eq
  obtain ⟨W, -, hξC, hW2, hξ2, hz3⟩ :=
    exists_irreducibleCloseds_of_isFlippingCurve hφps h3' hCcurve
  set ξ := W.isIrreducible.genericPoint
  have hreg : IsRegularLocalRing (X'.presheaf.stalk ξ) :=
    MMP.Flips.isRegularLocalRing_stalk_of_isFlippedCurveOf sX sZ sX' hD hC hξC
  set Dp := Mori.RationalMap.transformDivisor g D
  obtain ⟨E, a', hEξ, hEC, hEexc, hdisc', ha'⟩ :=
    exists_isDiscrepancy_blowUp_eq_one_sub_sum_mul_multiplicityAlong hX'n hKp hKDp hξC hW2 hξ2
      hreg
  obtain ⟨hνc, Ex, hExv, hExe⟩ := ((exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp
    hφs hφps).1 (F E.valuation) E.valuation (hF _)).mpr ⟨hdisc'.2.2.1, E, rfl, hEexc⟩
  obtain ⟨ω₀, a₀, hq₀⟩ := exists_isQDiscrepancyWith hX hK hKD Ex
  have hdisc₀ := hq₀.isDiscrepancy hK hKD hExe
  rw [hExv] at hdisc₀
  have hlt := hC.isDiscrepancy_lt hX hK hKD E hEC (hF _) hdisc₀ hdisc'
  obtain ⟨e, he⟩ := exists_equiv_transformPrimeDivisor_eq hφ
  have hcoeff : ∀ P, Dp.coeff (e P) = D.coeff P := coeff_transformDivisor_apply e he D
  have hDeffp := (MMP.Flips.IsCanonicalPair.of_isFlip hD hφ).2.2.1
  obtain ⟨kk, hkk⟩ := exists_int_eq_nat_mul_sum_mul_multiplicityAlong (Δ := Dp) (N := N)
    (fun Γ => by
      obtain ⟨m, hm⟩ := hND (e.symm Γ)
      exact ⟨m, by rwa [← e.apply_symm_apply Γ, hcoeff]⟩) W
  set μ : ℚ := Dp.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ)
  have hcμ : c ≤ μ := by
    rcases hcond with rfl | ⟨P, hcP, Q, hQ, hCQ⟩
    · exact sum_mul_multiplicityAlong_nonneg hDeffp W
    · obtain rfl : Q = e P := Option.some.inj (hQ.symm.trans (he P))
      exact le_sum_mul_multiplicityAlong hDeffp W hc (hcoeff P ▸ hcP) (hCQ hξC.mem)
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hkkc : (N : ℚ) * c ≤ kk := by
    rw [hkk]
    exact mul_le_mul_of_nonneg_left hcμ hN0.le
  have ht : (2 : ℚ) - (kk : ℚ) / N = 2 - μ := by
    rw [hkk]
    field_simp
  refine ⟨⟨kk, hkkc⟩, E.valuation, ?_, ?_⟩
  · -- `a_ℓ(E_C, X⁺, D⁺) = 2 - mult_C D⁺` is not small
    rintro ⟨⟨-, -, b, ⟨a'', ha'', rfl⟩, hbt⟩, -⟩
    have := ha''.eq hdisc'
    change (1 + a'' : ℝ) < ((2 - (kk : ℚ) / N : ℚ) : ℝ) at hbt
    rw [ht, this, ha'] at hbt
    push_cast at hbt
    linarith
  · refine ⟨⟨hνc, ⟨Ex, hExe, hExv⟩, 1 + (a₀ : ℝ), ⟨a₀, hdisc₀, rfl⟩, ?_⟩, ?_⟩
    · change (1 + a₀ : ℝ) < ((2 - (kk : ℚ) / N : ℚ) : ℝ)
      rw [ht]
      push_cast
      linarith
    · -- the center of `E_C` on `X` is not a curve contained in `B`
      intro E'' hE''v ⟨hcod, hsubB⟩
      have hξξ := map_eq_of_comap_eq sZ φ φp E''.toDivisorOver E.toDivisorOver (by
        change E''.valuation.comap _ = _
        rw [hE''v]
        exact hF _)
      rw [hEξ] at hξξ
      exact hnc _ (isFlippingCurve_closure_singleton hφs
        (by exact_mod_cast hK.topologicalKrullDim_eq) (codimension_center E'' ▸ hcod)
        (hξξ ▸ hz3)) (coe_center_eq_closure E'' ▸ hsubB)

/-! ### Szabó's difficulty along a sequence of flips -/

/-- A sequence in `ℕ∞`, finite at `i₀` and nonincreasing on the steps `i ≥ i₀` with `i + 1 < L`,
drops strictly only finitely often: from some `i₁ ≥ i₀` on, it never drops. -/
private theorem exists_forall_not_lt_of_le {f : ℕ → ℕ∞} {L : ℕ∞} {i₀ : ℕ} (hfin : f i₀ ≠ ⊤)
    (hle : ∀ i, i₀ ≤ i → ((i + 1 : ℕ) : ℕ∞) < L → f (i + 1) ≤ f i) :
    ∃ i₁, i₀ ≤ i₁ ∧ ∀ i, i₁ ≤ i → ((i + 1 : ℕ) : ℕ∞) < L → ¬ f (i + 1) < f i := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j : ℕ, ((j + 1 : ℕ) : ℕ∞) < L → (j : ℕ∞) < L := fun j hj =>
    lt_of_le_of_lt (Nat.cast_le.mpr j.le_succ) hj
  have hmono : ∀ i j, i₀ ≤ i → i ≤ j → (j : ℕ∞) < L → f j ≤ f i := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (hle j (hi.trans hij) hj).trans (ih (hstep j hj))
  -- after `m` strict drops the sequence has lost at least `m`
  have key : ∀ m : ℕ, ∃ i, i₀ ≤ i ∧ f i + m ≤ f i₀ := by
    intro m
    induction m with
    | zero => exact ⟨i₀, le_rfl, by simp⟩
    | succ m ih =>
      obtain ⟨i, hi, him⟩ := ih
      obtain ⟨j, hij, hj, hlt⟩ := hcon i hi
      refine ⟨j + 1, by omega, ?_⟩
      calc f (j + 1) + ((m + 1 : ℕ) : ℕ∞) = (f (j + 1) + 1) + m := by push_cast; ring
        _ ≤ f i + m := by gcongr; exact (Order.add_one_le_of_lt hlt).trans
                            (hmono i j hi hij (hstep j hj))
        _ ≤ f i₀ := him
  obtain ⟨i, -, hi⟩ := key ((f i₀).toNat + 1)
  have h := ENat.toNat_le_toNat (le_add_self.trans hi) hfin
  rw [ENat.toNat_coe] at h
  omega

/-- A `ℚ`-divisor has a common denominator: some `N ≥ 1` with `N D` integral. -/
private theorem exists_nat_mul_coeff_eq_int {X : Scheme} (D : QDivisor X) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ P, ∃ m : ℤ, (N : ℚ) * D.coeff P = m := by
  classical
  refine ⟨∏ P ∈ D.support, (D P).den,
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun P _ => (D P).den_nz),
    fun P => ?_⟩
  change ∃ m : ℤ, _ * D P = m
  by_cases hP : P ∈ D.support
  · obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem (fun P => (D P).den) hP
    refine ⟨a * (D P).num, ?_⟩
    rw [ha]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · exact ⟨0, by simp [Finsupp.notMem_support_iff.mp hP]⟩

/-- Along a sequence of flips of a canonical pair `(X, D)` with `⌊D⌋ = 0` and `N D` integral,
every model `(X_i, D_i)` is a canonical pair with `⌊D_i⌋ = 0` and `N D_i` integral, and the
components of `D_i` of coefficient `> c` lie in `T i`, if this holds for `i = 0` and `T (i + 1)`
is the set of transforms of the members of `T i`. -/
private theorem isCanonicalPair_and_roundDown_model {k : Type} [Field k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {K : Divisor X} {D : QDivisor X}
    (hD : IsCanonicalPair sX 3 K D) (hDfloor : DivisorWithCoeffs.roundDown D = 0) {N : ℕ}
    (hND : ∀ P, ∃ m : ℤ, (N : ℚ) * D.coeff P = m) {c : ℚ} (S : SequenceOfFlips sX 3 K D)
    (T : ∀ i, Finset (Mori.PrimeDivisor (S.model i).1))
    (hT0 : ∀ P : Mori.PrimeDivisor (S.model 0).1, c < (S.model 0).2.2.2.coeff P → P ∈ T 0)
    (hT : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ Q : Mori.PrimeDivisor (S.model (i + 1)).1,
      Q ∈ T (i + 1) ↔
        ∃ P ∈ T i, Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some Q)
    (i : ℕ) (hi : (i : ℕ∞) < S.length) [h₁ : IsIntegral (S.model i).1]
    [h₂ : IsLocallyNoetherian (S.model i).1] [h₃ : IsNormal (S.model i).1]
    [h₄ : CompactSpace (S.model i).1] [h₅ : LocallyOfFiniteType (S.model i).2.1] :
    Flips.IsCanonicalPair (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2 ∧
      DivisorWithCoeffs.roundDown (S.model i).2.2.2 = 0 ∧
      (∀ P, ∃ m : ℤ, (N : ℚ) * (S.model i).2.2.2.coeff P = m) ∧
      ∀ P, c < (S.model i).2.2.2.coeff P → P ∈ T i := by
  induction i generalizing h₁ h₂ h₃ h₄ h₅ with
  | zero =>
    have key : ∀ (M : FlipModel k) (_ : M = ⟨X, sX, K, D⟩) [IsIntegral M.1]
        [IsLocallyNoetherian M.1] [IsNormal M.1] [CompactSpace M.1] [LocallyOfFiniteType M.2.1],
        Flips.IsCanonicalPair M.2.1 3 M.2.2.1 M.2.2.2 ∧ DivisorWithCoeffs.roundDown M.2.2.2 = 0 ∧
          ∀ P, ∃ m : ℤ, (N : ℚ) * M.2.2.2.coeff P = m := by
      rintro M rfl _ _ _ _ _
      exact ⟨hD, hDfloor, hND⟩
    obtain ⟨h1, h2, h3⟩ := key (S.model 0) S.model_zero
    exact ⟨h1, h2, h3, hT0⟩
  | succ i ih =>
    have hi' : (i : ℕ∞) < S.length := (ENat.coe_lt_coe.2 i.lt_succ_self).trans hi
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := (S.isNormalVariety_model i hi').1.toIsIntegral
    haveI := (S.isNormalVariety_model i hi').1.toLocallyOfFiniteType
    obtain ⟨hcan, hfl, hNi, hTi⟩ := ih hi'
    have hflip := S.isFlip i hi
    have hcoeff := fun Q => exists_transformPrimeDivisor_eq_and_coeff hflip Q
    rw [S.transform_eq i hi]
    refine ⟨isCanonicalPair_transformDivisor hcan hflip (S.isCanonicalDivisor_model (i + 1) hi),
      ?_, ?_, ?_⟩
    · refine Finsupp.ext fun Q => ?_
      obtain ⟨P, -, hP⟩ := hcoeff Q
      have h := DivisorWithCoeffs.coeff_roundDown (S.model i).2.2.2 P
      rw [hfl, ← hP, ← DivisorWithCoeffs.coeff_roundDown] at h
      exact h.symm
    · intro Q
      obtain ⟨P, -, hP⟩ := hcoeff Q
      simpa only [hP] using hNi P
    · intro Q hQ
      obtain ⟨P, hPQ, hP⟩ := hcoeff Q
      rw [hP] at hQ
      exact (hT i hi Q).2 ⟨P, hTi P hQ, hPQ⟩

/-- Let `(X, D)` be a canonical pair, `X` a threefold over a field of characteristic zero with
canonical divisor `K`, with `⌊D⌋ = 0`, `c ≥ 0` rational and `S` a sequence of flips for `(X, D)`
with models `(X_i, D_i)`, contractions `φ_i`, flips `φ_i⁺` and birational maps `g_i`. Let `T i` be
finite sets of prime divisors of `X_i`, with `T 0` containing every prime divisor of coefficient
`> c` in `D_0 = D` and `T (i + 1)` the set of transforms under `g_i` of the members of `T i`, and
let `B_i = ⋃_{P ∈ T i} P`. If for every `i ≥ i₀` with `i + 1 < L` no flipping curve of `φ_i` lies
in `B_i`, then there is `i₁ ≥ i₀` such that for every `i ≥ i₁` with `i + 1 < L` no flipped curve
`C` of `φ_i⁺` satisfies `c = 0` or `C ⊆ Q` for a prime divisor `Q` of `X_{i+1}` with
`c ≤ D_{i+1}.coeff Q`. -/
@[mmp "lem_fa4_szabo_eventually_no_flipped_curve"]
public theorem SequenceOfFlips.eventually_not_isFlippedCurveOf {k : Type} [Field k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {D : QDivisor X} (hD : IsCanonicalPair sX 3 K D)
    (hDfloor : DivisorWithCoeffs.roundDown D = 0) {c : ℚ} (hc : 0 ≤ c)
    (S : SequenceOfFlips sX 3 K D)
    (T : ∀ i, Finset (Mori.PrimeDivisor (S.model i).1))
    (hT0 : ∀ P : Mori.PrimeDivisor (S.model 0).1, c < (S.model 0).2.2.2.coeff P → P ∈ T 0)
    (hT : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ Q : Mori.PrimeDivisor (S.model (i + 1)).1,
      Q ∈ T (i + 1) ↔
        ∃ P ∈ T i, Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some Q)
    {i₀ : ℕ} (hi₀ : (i₀ : ℕ∞) < S.length)
    (hnc : ∀ i : ℕ, i₀ ≤ i → ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ C : Set (S.model i).1,
      IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i) C →
        ¬ C ⊆ ⋃ P ∈ T i, (P.support : Set (S.model i).1)) :
    ∃ i₁, i₀ ≤ i₁ ∧ ∀ i : ℕ, i₁ ≤ i → ((i + 1 : ℕ) : ℕ∞) < S.length →
      ∀ C : Set (S.model (i + 1)).1,
        haveI := S.isLocallyNoetherian_model i
        haveI := S.isNormal_model i
        haveI := S.compactSpace_model i
        haveI := S.isLocallyNoetherian_model (i + 1)
        haveI := S.isNormal_model (i + 1)
        haveI := S.compactSpace_model (i + 1)
        IsFlippedCurveOf k (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
            (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2))
            (S.contraction i) (S.flip i) (S.flipMap i) C →
          ¬ (c = 0 ∨ ∃ Q : Mori.PrimeDivisor (S.model (i + 1)).1,
            c ≤ (S.model (i + 1)).2.2.2.coeff Q ∧ C ⊆ (Q.support : Set (S.model (i + 1)).1)) := by
  classical
  obtain ⟨N, hN, hND⟩ := exists_nat_mul_coeff_eq_int D
  have hlt : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length → (i : ℕ∞) < S.length := fun i hi =>
    lt_of_le_of_lt (Nat.cast_le.mpr i.le_succ) hi
  have hint : ∀ i : ℕ, (i : ℕ∞) < S.length → IsIntegral (S.model i).1 := fun i hi =>
    (S.isNormalVariety_model i hi).1.toIsIntegral
  have hlft : ∀ i : ℕ, (i : ℕ∞) < S.length → LocallyOfFiniteType (S.model i).2.1 := fun i hi =>
    (S.isNormalVariety_model i hi).1.toLocallyOfFiniteType
  have good := isCanonicalPair_and_roundDown_model hD hDfloor hND S T hT0 hT
  -- the closed sets `B_i` and the difficulties `n_i = d_{N,c}(X_i, D_i; B_i)`
  let B : ∀ i, Closeds (S.model i).1 := fun i =>
    ⟨⋃ P ∈ T i, (P.support : Set (S.model i).1),
      isClosed_biUnion_finset fun P _ => P.idealSheaf.support.isClosed⟩
  let f : ℕ → ℕ∞ := fun i =>
    if hi : (i : ℕ∞) < S.length then
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI := hint i hi
      haveI := hlft i hi
      szaboDifficulty (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2 (good i hi).1.1
        (good i hi).1.2.1 (good i hi).1.2.2.2.1 (B i) N hN c
    else 0
  have hstep : ∀ i, i₀ ≤ i → ((i + 1 : ℕ) : ℕ∞) < S.length →
      f (i + 1) ≤ f i ∧ f i < ⊤ ∧ ∀ C : Set (S.model (i + 1)).1,
        haveI := S.isLocallyNoetherian_model i
        haveI := S.isNormal_model i
        haveI := S.compactSpace_model i
        haveI := S.isLocallyNoetherian_model (i + 1)
        haveI := S.isNormal_model (i + 1)
        haveI := S.compactSpace_model (i + 1)
        IsFlippedCurveOf k (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
            (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2))
            (S.contraction i) (S.flip i) (S.flipMap i) C →
          (c = 0 ∨ ∃ Q : Mori.PrimeDivisor (S.model (i + 1)).1,
            c ≤ (S.model (i + 1)).2.2.2.coeff Q ∧ C ⊆ (Q.support : Set (S.model (i + 1)).1)) →
          f (i + 1) < f i := by
    intro i hii hi1
    have hi := hlt i hi1
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := hint i hi
    haveI := hlft i hi
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    haveI := hint (i + 1) hi1
    haveI := hlft (i + 1) hi1
    obtain ⟨hcan, hfl, hNi, hTi⟩ := good i hi
    have hflip := S.isFlip i hi1
    have hB' : ((B (i + 1) : Closeds _) : Set (S.model (i + 1)).1) = ⋃ P ∈ T i,
        ⋃ Q ∈ Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P,
          (Q.support : Set (S.model (i + 1)).1) := by
      ext x
      simp only [B, Closeds.coe_mk, Set.mem_iUnion, hT i hi1, exists_prop, Option.mem_def]
      exact ⟨fun ⟨Q, ⟨P, hP, hPQ⟩, hx⟩ => ⟨P, hP, Q, hPQ, hx⟩,
        fun ⟨P, hP, Q, hPQ, hx⟩ => ⟨Q, ⟨P, hP, hPQ⟩, hx⟩⟩
    obtain ⟨hD', hle, hfin, hstrict⟩ := Flips.szaboDifficulty_flip_le (S.model i).2.1
      (S.baseStr i) (S.model (i + 1)).2.1 hcan hfl hN hNi hc (S := T i) (B := B i) rfl
      (fun P hP => Set.subset_biUnion_of_mem (u := fun P => (P.support : Set (S.model i).1))
        (hTi P hP)) hflip hB' (hnc i hii hi1) (S.isCanonicalDivisor_model (i + 1) hi1)
    have hfi : f i = szaboDifficulty (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2
        hcan.1 hcan.2.1 hcan.2.2.2.1 (B i) N hN c := dif_pos hi
    have hfi1 : f (i + 1) = szaboDifficulty (S.model (i + 1)).2.1 3 (S.model (i + 1)).2.2.1
        (Mori.RationalMap.transformDivisor (S.flipMap i) (S.model i).2.2.2)
        hflip.isNormalVariety_flip (S.isCanonicalDivisor_model (i + 1) hi1) hD' (B (i + 1))
        N hN c := by
      rw [show f (i + 1) = _ from dif_pos hi1]
      exact szaboDifficulty_congr (S.transform_eq i hi1)
    rw [hfi, hfi1]
    refine ⟨hle, hfin, fun C hC hcond => hstrict ⟨C, hC, ?_⟩⟩
    rcases hcond with h0 | ⟨Q, hQc, hCQ⟩
    · exact Or.inl h0
    · obtain ⟨P, hPQ, hP⟩ := exists_transformPrimeDivisor_eq_and_coeff hflip Q
      rw [S.transform_eq i hi1, hP] at hQc
      exact Or.inr ⟨P, hQc, Q, hPQ, hCQ⟩
  by_cases h0 : ((i₀ + 1 : ℕ) : ℕ∞) < S.length
  · obtain ⟨i₁, hi₁, hnot⟩ := exists_forall_not_lt_of_le (hstep i₀ le_rfl h0).2.1.ne
      fun i hi hi1 => (hstep i hi hi1).1
    exact ⟨i₁, hi₁, fun i hi hi1 C hC hcond =>
      hnot i hi hi1 ((hstep i (hi₁.trans hi) hi1).2.2 C hC hcond)⟩
  · exact ⟨i₀, le_rfl, fun i hi hi1 => absurd
      (lt_of_le_of_lt (Nat.cast_le.mpr (by omega)) hi1) h0⟩

/-! ### The components of a `ℚ`-divisor above and at a given coefficient -/

/-- A flipping curve contained in a finite union of prime divisors lies in one of them. -/
private theorem exists_mem_subset_support_of_isFlippingCurve {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} {C : Set X}
    (hC : IsFlippingCurve k sX sZ φ C) {s : Finset (Mori.PrimeDivisor X)}
    (h : C ⊆ ⋃ P ∈ s, (P.support : Set X)) : ∃ P ∈ s, C ⊆ P.support := by
  obtain ⟨-, -, -, -, z, -, hmax, -⟩ := hC
  exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.exists_subset_of_isIrreducible
    (fun P _ => P.idealSheaf.support.isClosed) hmax.1.1 h

section Levels

variable {X Y : Scheme} (D : QDivisor X)

/-- The prime divisors along which `D` has coefficient `> c`. -/
private def componentsAbove (c : ℚ) : Finset (Mori.PrimeDivisor X) :=
  D.support.filter fun Q => c < D.coeff Q

private theorem mem_componentsAbove {c : ℚ} (hc : 0 ≤ c) {Q : Mori.PrimeDivisor X} :
    Q ∈ componentsAbove D c ↔ c < D.coeff Q := by
  simp only [componentsAbove, Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
  intro h h0
  rw [DivisorWithCoeffs.coeff_apply, h0] at h
  exact absurd h (not_lt.2 hc)

/-- The reduced divisor whose components are the prime divisors along which `D` has
coefficient `c`. -/
private noncomputable def levelDivisor (c : ℚ) : Divisor X :=
  ∑ Q ∈ D.support.filter (fun Q => D.coeff Q = c), Finsupp.single Q 1

private theorem coeff_levelDivisor {c : ℚ} (hc : c ≠ 0) (Q : Mori.PrimeDivisor X) :
    (levelDivisor D c).coeff Q = if D.coeff Q = c then 1 else 0 := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, levelDivisor, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter]
  by_cases h : D.coeff Q = c
  · have h' : Q ∈ D.support := by
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, h]
      exact hc
    rw [if_pos ⟨h', h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]

private theorem isReducedEffective_levelDivisor {c : ℚ} (hc : c ≠ 0) :
    MMP.Intersection.IsReducedEffective (levelDivisor D c) := by
  intro P
  rw [coeff_levelDivisor D hc]
  split_ifs <;> simp

private theorem coeff_eq_of_mem_support_levelDivisor {c : ℚ} (hc : c ≠ 0)
    {Q : Mori.PrimeDivisor X} (hQ : Q ∈ (levelDivisor D c).support) : D.coeff Q = c := by
  by_contra h
  exact Finsupp.mem_support_iff.mp hQ (by rw [← DivisorWithCoeffs.coeff_apply,
    coeff_levelDivisor D hc, if_neg h])

variable {g : X.RationalMap Y} (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor Y)
  (he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P))

include he

private theorem mem_componentsAbove_transformDivisor_iff {c : ℚ} (hc : 0 ≤ c)
    (Q : Mori.PrimeDivisor Y) :
    Q ∈ componentsAbove (Mori.RationalMap.transformDivisor g D) c ↔
      ∃ P ∈ componentsAbove D c, Mori.RationalMap.transformPrimeDivisor g P = some Q := by
  obtain ⟨Q, rfl⟩ := e.surjective Q
  rw [mem_componentsAbove _ hc, coeff_transformDivisor_apply e he]
  constructor
  · exact fun h => ⟨Q, (mem_componentsAbove _ hc).2 h, he Q⟩
  · rintro ⟨P, hP, hPQ⟩
    rw [he, Option.some_inj] at hPQ
    rw [← e.injective hPQ]
    exact (mem_componentsAbove _ hc).1 hP

private theorem levelDivisor_transformDivisor {c : ℚ} (hc : c ≠ 0) :
    levelDivisor (Mori.RationalMap.transformDivisor g D) c =
      Mori.RationalMap.transformDivisor g (levelDivisor D c) := by
  refine Finsupp.ext fun Q => ?_
  obtain ⟨P, rfl⟩ := e.surjective Q
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
    coeff_transformDivisor_apply e he, coeff_levelDivisor _ hc, coeff_levelDivisor _ hc,
    coeff_transformDivisor_apply e he]

end Levels

/-! ### Termination -/

/-- A morphism with relative Picard number one is not an isomorphism. -/
private theorem not_isIso_of_relativePicardNumber_eq_one {k : Type*} [Field k] {X Z : Scheme}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) (h : Flips.relativePicardNumber sX f = 1) : ¬ IsIso f := by
  intro hf
  have hC : ∀ C : ProperCurve sX, ¬ C.IsContractedBy f := by
    intro C hC
    have hcl : closure ({C.point} : Set X) = {C.point} :=
      subset_antisymm (fun x hx => f.isOpenEmbedding.injective (hC x hx)) subset_closure
    have hd := C.dim_eq
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hcl] at hd
    have h0 := topologicalKrullDim_zero_of_discreteTopology (({C.point} : Set X))
    rw [hd] at h0
    exact absurd h0 (by norm_num)
  have htop : relativeNumericallyTrivialDivisors sX f = ⊤ :=
    eq_top_iff.2 fun D _ => (mem_relativeNumericallyTrivialDivisors sX f).2
      fun C hc => absurd hc (hC C)
  haveI : Subsingleton (RelativeNumericalDivisorClasses sX f) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (Submodule.Quotient.eq _).2 (htop ▸ Submodule.mem_top)
  rw [Flips.relativePicardNumber, rank_subsingleton'] at h
  simp at h

section Sequence

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {K : Divisor X} {D : QDivisor X} (S : SequenceOfFlips sX 3 K D)

/-- The `i`-th flip of a sequence of flips identifies the prime divisors of `X_i` and
`X_{i+1}`. -/
private theorem exists_equiv_transformPrimeDivisor_flipMap {i : ℕ}
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    ∃ e : Mori.PrimeDivisor (S.model i).1 ≃ Mori.PrimeDivisor (S.model (i + 1)).1,
      ∀ P, Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some (e P) := by
  have hi' : (i : ℕ∞) < S.length := (ENat.coe_lt_coe.2 i.lt_succ_self).trans hi
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI := (S.isNormalVariety_model i hi').1.toIsIntegral
  haveI := (S.isNormalVariety_model i hi').1.toLocallyOfFiniteType
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI := S.compactSpace_model (i + 1)
  haveI := (S.isNormalVariety_model (i + 1) hi).1.toIsIntegral
  haveI := (S.isNormalVariety_model (i + 1) hi).1.toLocallyOfFiniteType
  exact exists_equiv_transformPrimeDivisor_eq (S.isFlip i hi)

/-- The flips preserve the coefficients of the boundary divisors. -/
private theorem coeff_model_succ {i : ℕ} (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (e : Mori.PrimeDivisor (S.model i).1 ≃ Mori.PrimeDivisor (S.model (i + 1)).1)
    (he : ∀ P, Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some (e P))
    (P : Mori.PrimeDivisor (S.model i).1) :
    (S.model (i + 1)).2.2.2.coeff (e P) = (S.model i).2.2.2.coeff P := by
  rw [S.transform_eq i hi]
  exact coeff_transformDivisor_apply e he _ P

/-- Every nonzero coefficient of `D_i` is a coefficient of `D_0`. -/
private theorem coeff_model_mem_image_coeff (i : ℕ) (hi : (i : ℕ∞) < S.length)
    (Q : Mori.PrimeDivisor (S.model i).1) (hQ : (S.model i).2.2.2.coeff Q ≠ 0) :
    (S.model i).2.2.2.coeff Q ∈ (S.model 0).2.2.2.support.image (S.model 0).2.2.2.coeff := by
  induction i with
  | zero =>
    exact Finset.mem_image_of_mem _
      (Finsupp.mem_support_iff.2 (by rwa [← DivisorWithCoeffs.coeff_apply]))
  | succ i ih =>
    obtain ⟨e, he⟩ := exists_equiv_transformPrimeDivisor_flipMap S hi
    obtain ⟨P, rfl⟩ := e.surjective Q
    rw [coeff_model_succ S hi e he] at hQ ⊢
    exact ih ((ENat.coe_lt_coe.2 i.lt_succ_self).trans hi) P hQ

private theorem mem_componentsAbove_model_succ_iff {c : ℚ} (hc : 0 ≤ c) {i : ℕ}
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) (Q : Mori.PrimeDivisor (S.model (i + 1)).1) :
    Q ∈ componentsAbove (S.model (i + 1)).2.2.2 c ↔
      ∃ P ∈ componentsAbove (S.model i).2.2.2 c,
        Mori.RationalMap.transformPrimeDivisor (S.flipMap i) P = some Q := by
  obtain ⟨e, he⟩ := exists_equiv_transformPrimeDivisor_flipMap S hi
  rw [S.transform_eq i hi]
  exact mem_componentsAbove_transformDivisor_iff _ e he hc Q

private theorem levelDivisor_model_succ {c : ℚ} (hc : c ≠ 0) {i : ℕ}
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    levelDivisor (S.model (i + 1)).2.2.2 c =
      Mori.RationalMap.transformDivisor (S.flipMap i) (levelDivisor (S.model i).2.2.2 c) := by
  obtain ⟨e, he⟩ := exists_equiv_transformPrimeDivisor_flipMap S hi
  rw [S.transform_eq i hi]
  exact levelDivisor_transformDivisor _ e he hc

/-- Every model of a sequence of flips of a canonical pair is a canonical pair. -/
private theorem isCanonicalPair_model (hD : Flips.IsCanonicalPair sX 3 K D) (i : ℕ)
    (hi : (i : ℕ∞) < S.length) [h₁ : IsIntegral (S.model i).1]
    [h₂ : IsLocallyNoetherian (S.model i).1] [h₃ : IsNormal (S.model i).1]
    [h₄ : CompactSpace (S.model i).1] [h₅ : LocallyOfFiniteType (S.model i).2.1] :
    Flips.IsCanonicalPair (S.model i).2.1 3 (S.model i).2.2.1 (S.model i).2.2.2 := by
  induction i generalizing h₁ h₂ h₃ h₄ h₅ with
  | zero =>
    have key : ∀ (M : FlipModel k) (_ : M = ⟨X, sX, K, D⟩) [IsIntegral M.1]
        [IsLocallyNoetherian M.1] [IsNormal M.1] [CompactSpace M.1] [LocallyOfFiniteType M.2.1],
        Flips.IsCanonicalPair M.2.1 3 M.2.2.1 M.2.2.2 := by
      rintro M rfl _ _ _ _ _
      exact hD
    exact key (S.model 0) S.model_zero
  | succ i ih =>
    have hi' : (i : ℕ∞) < S.length := (ENat.coe_lt_coe.2 i.lt_succ_self).trans hi
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := (S.isNormalVariety_model i hi').1.toIsIntegral
    haveI := (S.isNormalVariety_model i hi').1.toLocallyOfFiniteType
    rw [S.transform_eq i hi]
    exact isCanonicalPair_transformDivisor (ih hi') (S.isFlip i hi)
      (S.isCanonicalDivisor_model (i + 1) hi)

/-- Every flip `φ_i⁺` of a sequence of flips of a canonical pair has a flipped curve. -/
private theorem exists_isFlippedCurveOf (hD : Flips.IsCanonicalPair sX 3 K D) {i : ℕ}
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    ∃ C : Set (S.model (i + 1)).1,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI := S.isLocallyNoetherian_model (i + 1)
      haveI := S.isNormal_model (i + 1)
      haveI := S.compactSpace_model (i + 1)
      IsFlippedCurveOf k (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
        (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2))
        (S.contraction i) (S.flip i) (S.flipMap i) C := by
  have hi' : (i : ℕ∞) < S.length := (ENat.coe_lt_coe.2 i.lt_succ_self).trans hi
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI := (S.isNormalVariety_model i hi').1.toIsIntegral
  haveI := (S.isNormalVariety_model i hi').1.toLocallyOfFiniteType
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI := S.compactSpace_model (i + 1)
  have hE : logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2) =
      QDivisor.toRDivisor (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2) := by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    rfl
  have hflip := S.isFlip i hi
  rw [hE] at hflip
  obtain ⟨C, hC⟩ := IsFlip.exists_isFlippedCurveOf_of_not_isIso
    (isCanonicalPair_model S hD i hi').2.2.2.1 hflip
    (not_isIso_of_relativePicardNumber_eq_one _ _
      (S.isNegativeExtremalContraction i hi).relativePicardNumber_eq_one)
  rw [← hE] at hC
  exact ⟨C, hC⟩

/-- **Downward induction through the coefficients.** In an infinite sequence of flips of a
canonical pair `(X, D)` with `⌊D⌋ = 0`, for every `c ≥ 0`, from some index on no flipping curve
lies in a component of `D_i` of coefficient `> c`. -/
private theorem exists_forall_not_subset_componentsAbove (hD : Flips.IsCanonicalPair sX 3 K D)
    (hDfloor : DivisorWithCoeffs.roundDown D = 0) (hL : S.length = ⊤) {c : ℚ} (hc : 0 ≤ c) :
    ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ C : Set (S.model i).1,
      IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i) C →
        ¬ C ⊆ ⋃ P ∈ componentsAbove (S.model i).2.2.2 c, (P.support : Set (S.model i).1) := by
  classical
  have hlen : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hL ▸ ENat.coe_lt_top i
  -- the coefficients `V` of `D`
  let V : Finset ℚ := (S.model 0).2.2.2.support.image (S.model 0).2.2.2.coeff
  have hV : ∀ c : ℚ, 0 ≤ c → ∀ i (Q : Mori.PrimeDivisor (S.model i).1),
      c < (S.model i).2.2.2.coeff Q → (S.model i).2.2.2.coeff Q ∈ V.filter (c < ·) :=
    fun c hc i Q h =>
      Finset.mem_filter.2 ⟨coeff_model_mem_image_coeff S i (hlen i) Q (hc.trans_lt h).ne', h⟩
  obtain ⟨n, hn⟩ : ∃ n, (V.filter (c < ·)).card = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  by_cases hne : (V.filter (c < ·)).Nonempty
  swap
  · refine ⟨0, fun i _ _ C hC hCsub => hne ?_⟩
    obtain ⟨P, hP, -⟩ := exists_mem_subset_support_of_isFlippingCurve hC hCsub
    exact ⟨_, hV c hc i P ((mem_componentsAbove _ hc).1 hP)⟩
  -- `c'` is the least coefficient of `D` above `c`
  have hc'mem := Finset.min'_mem _ hne
  set c' := (V.filter (c < ·)).min' hne
  have hcc' : c < c' := (Finset.mem_filter.mp hc'mem).2
  have hc' : 0 ≤ c' := hc.trans hcc'.le
  have hc'0 : c' ≠ 0 := (hc.trans_lt hcc').ne'
  have hcard : (V.filter (c' < ·)).card < n := by
    rw [← hn]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).2
      ⟨c', hc'mem, by simp⟩)
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hcc'.trans hx.2⟩
  obtain ⟨i₀, hi₀⟩ := ih _ hcard hc' rfl
  -- eventually no flipped curve lies in a component of coefficient `≥ c'`
  obtain ⟨i₁, hi₁, hno⟩ := SequenceOfFlips.eventually_not_isFlippedCurveOf sX hD hDfloor hc' S
    (fun i => componentsAbove (S.model i).2.2.2 c') (fun P hP => (mem_componentsAbove _ hc').2 hP)
    (fun i hi => mem_componentsAbove_model_succ_iff S hc' hi) (hlen i₀) hi₀
  -- hence eventually no flipping curve lies in a component of coefficient `c'`
  obtain ⟨i₂, hi₂, hno₂⟩ := SequenceOfFlips.exists_forall_not_subset_supp_of_isFlippingCurve
    S hD.2.1.topologicalKrullDim_eq (fun i => levelDivisor (S.model i).2.2.2 c')
    (isReducedEffective_levelDivisor _ hc'0) (fun i hi => levelDivisor_model_succ S hc'0 hi) i₁
    (by
      intro i hi hi1 C hC hCsub
      rw [DivisorWithCoeffs.coe_supp] at hCsub
      obtain ⟨Q, hQ, hCQ⟩ := exists_mem_subset_support_of_isFlippingCurve hC.2 hCsub
      exact hno i hi hi1 C hC
        (Or.inr ⟨Q, (coeff_eq_of_mem_support_levelDivisor _ hc'0 hQ).ge, hCQ⟩))
  refine ⟨i₂, fun i hi hi1 C hC hCsub => ?_⟩
  obtain ⟨P, hP, hCP⟩ := exists_mem_subset_support_of_isFlippingCurve hC hCsub
  have hlt := (mem_componentsAbove _ hc).1 hP
  rcases (Finset.min'_le _ _ (hV c hc i P hlt) : c' ≤ _).lt_or_eq with h | h
  · exact hi₀ i (by omega) hi1 C hC (hCP.trans
      (Set.subset_biUnion_of_mem (u := fun P => (P.support : Set (S.model i).1))
        ((mem_componentsAbove _ hc').2 h)))
  · refine hno₂ i (by omega) hi1 C hC (hCP.trans (DivisorWithCoeffs.support_subset_supp ?_))
    rw [coeff_levelDivisor _ hc'0, if_pos h.symm]
    exact one_ne_zero

end Sequence

/-- Let `X` be a threefold over a field `k` of characteristic zero with canonical divisor `K`, and
`D` an effective `ℚ`-divisor on `X` such that `(X, D)` is a canonical pair and `⌊D⌋ = 0`. Then
every sequence of flips `S` for `(X, D)` terminates; `X` is not assumed `ℚ`-factorial. -/
@[mmp "thm_fa4_termination_canonical_flips_non_qfactorial"]
public theorem SequenceOfFlips.terminates_of_isCanonicalPair {k : Type} [Field k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {D : QDivisor X} (hD : IsCanonicalPair sX 3 K D)
    (hDfloor : DivisorWithCoeffs.roundDown D = 0)
    (S : SequenceOfFlips sX 3 K D) : S.Terminates := by
  by_contra hS
  have hL : S.length = ⊤ := not_lt_top_iff.mp hS
  have hlen : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hL ▸ ENat.coe_lt_top i
  -- with `c = 0`: eventually there is no flipped curve at all
  obtain ⟨i₀, hi₀⟩ := exists_forall_not_subset_componentsAbove S hD hDfloor hL le_rfl
  obtain ⟨i, -, hno⟩ := SequenceOfFlips.eventually_not_isFlippedCurveOf sX hD hDfloor le_rfl S
    (fun i => componentsAbove (S.model i).2.2.2 0) (fun P hP => (mem_componentsAbove _ le_rfl).2 hP)
    (fun i hi => mem_componentsAbove_model_succ_iff S le_rfl hi) (hlen i₀) hi₀
  obtain ⟨C, hC⟩ := exists_isFlippedCurveOf S hD (hlen (i + 1))
  exact hno i le_rfl (hlen _) C hC (Or.inl rfl)

end MMP.Flips

end
