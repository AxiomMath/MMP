module

public import MMP.AlgebraicGeometry.Vanishing.RelativeAmpleRoundUp
public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction

/-!
# Local vanishing for reduced-boundary adjoint ideals

Let `X` be a smooth variety over an algebraically closed field `k` of characteristic zero, `Δ` a
reduced snc divisor on `X`, `D` an effective `ℚ`-divisor containing no stratum of `Δ`, and
`μ : Y ⟶ X` a projective log resolution of `Δ + D` which is an isomorphism over the generic point
of every stratum of `Δ`. Let `Γ` be the reduced sum of the prime divisors of `Y` of log
discrepancy zero for `(X, Δ)` and write `K_Y + Γ = μ^*(K_X + Δ) + E`, so that the
reduced-boundary adjoint ideal (`MMP.Fourfold.IsReducedAdjointIdealOn`) is
`𝒥_{Δ,D} = μ_*𝒪_Y(E - ⌊μ^*D⌋)`. Then `Γ` is the strict transform `μ⁻¹_* Δ` of `Δ`, and for
every reduced divisor `T ≤ Γ` (a choice of components of `Γ`)
`R^i μ_* 𝒪_Y(E - ⌊μ^*D⌋ - T) = 0` for all `i > 0`; `T = 0` is the vanishing for the sheaf
defining `𝒥_{Δ,D}`.

## Main results

* `MMP.Fourfold.isZero_rightDerived_pushforward_adjointIdealSheaf`: the two assertions above.

## Implementation notes

* "`μ` is an isomorphism over the generic point of the stratum `S`" is stated as: `S` meets the
  biregular locus `MMP.Mori.biregularLocus μ`, the largest open of `X` over which `μ` is an
  isomorphism. A stratum is irreducible and closed, so an open meets it exactly when it contains
  its generic point.
* The strict transform of `Δ` is `MMP.Flips.birationalInverseTransform μ hμ Δ`, the birational
  transform of `Δ` under `μ⁻¹ : X ⤏ Y`.
* The data `Γ`, `E` and `F = μ^*D` of the adjoint ideal are given explicitly, with the defining
  properties `MMP.Fourfold.IsZeroLogDiscrepancyDivisor`,
  `MMP.Fourfold.IsAdjointDiscrepancyDivisor` and `MMP.Mori.QDivisor.IsPullback`, exactly as in
  `MMP.Fourfold.IsReducedAdjointIdealOn`; the scheme-theoretic properties of `Y` they need follow
  from `μ` being a log resolution.
* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero, the setting of the relative vanishing theorem
  `MMP.Fourfold.isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp` used in the
  proof. `R^i μ_*` is the `i`-th right derived functor of
  `AlgebraicGeometry.Scheme.Modules.pushforward μ`.
-/

@[expose] public section

section

/-!
## Proof: Local vanishing for reduced-boundary adjoint ideals

Let `X` be a smooth variety over an algebraically closed field of characteristic zero, `Δ` a
reduced snc divisor, `D` an effective `ℚ`-divisor containing no stratum of `Δ`, and
`μ : Y ⟶ X` a projective log resolution of `Δ + D` which is an isomorphism over the generic point
of every stratum of `Δ`. With `Γ` the reduced sum of the prime divisors of `Y` of log discrepancy
zero for `(X, Δ)` and `K_Y + Γ = μ^*(K_X + Δ) + E`, this file proves that `Γ = μ⁻¹_* Δ` and that
`R^i μ_* 𝒪_Y(E - ⌊μ^*D⌋ - T) = 0` for `i > 0` and every `0 ≤ T ≤ Γ`.

The first assertion comes from the log discrepancy formula over a reduced snc divisor: a divisor
over `X` has log discrepancy a natural number `l` with `codim Z ≤ l + #{components through Z}`,
`Z` its center. If the log discrepancy is zero, `Z` is a stratum of `Δ`, hence meets the locus
over which `μ` is an isomorphism, so the divisor is the strict transform of a component of `Δ`.

For the vanishing, let `F_x` be an effective exceptional `ℚ`-divisor with `-F_x` relatively ample
(`MMP.Mori.exists_isRelativelyAmple_neg_smul_of_isExceptional`) and `L = E - ⌊μ^*D⌋ - T`. With
`ε = 1/M` and `δ = N e / (q M)` for suitable integers,
`Λ = (1 - ε)(Γ - T) + {μ^*D} + δ F_x` has coefficients in `[0, 1)` and snc support, and
`B = L - K_Y - Λ = -μ^*(K_X + Δ + D) - δ F_x + ε (Γ - T)` is `μ`-ample, so that
`K_Y + ⌈B⌉ = L` and the relative vanishing theorem
`MMP.Fourfold.isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp` applies.

## Main results

* `MMP.Fourfold.isZero_rightDerived_pushforward_adjointIdealSheaf`: the two assertions above.

## Implementation notes

* The canonical divisors are `K_X = div(ω)` and `K_Y = div(μ^*ω)` for one nonzero rational top
  form `ω`, and `μ^*(K_X + Δ)` is the pull-back of the Cartier divisor `K_X + Δ`. The log
  discrepancy being unique (`MMP.Threefold.Bridges.IsLogDiscrepancy.unique`), the defining
  property of `E` gives `E = K_Y - μ^*(K_X + Δ) + Γ` coefficientwise.
* Openness of relative ampleness is used in the form: for an `f`-ample Cartier divisor `H` and
  any Cartier divisor `G`, `m H + G` is `f`-ample for some `m > 0`. Writing `δ F_x` and
  `ε (Γ - T)` with the common denominator `q M` makes `q M B` the sum of `N(-e F_x) + q(Γ - T)`
  and the pull-back of a Cartier divisor of `X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.31, 2.62,
  2.68
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.FourfoldProofs.FourfoldAdjointLocalVanishingProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Dimension and canonical divisors -/

section Canonical

variable {k : Type} [Field k] [PerfectField k]

omit [PerfectField k] in
/-- A non-empty compact scheme locally of finite type over a field has dimension a natural
number. -/
private theorem exists_topologicalKrullDim_eq_natCast {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [CompactSpace X] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have h2 : topologicalKrullDim X ≠ ⊥ := by
    rw [Ne, topologicalKrullDim, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  generalize topologicalKrullDim X = v at h1 h2
  induction v using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/-- A smooth variety of dimension `n` has a nonzero rational `n`-form whose divisor is a
canonical divisor. -/
private theorem exists_form_isCanonicalDivisor {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ (divisorOfForm ω).IsCanonicalDivisor sX n := by
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme
    sX hsm hn
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  exact ⟨ω, hω0, hK⟩

end Canonical

/-! ### The two log discrepancies -/

section Dictionary

open MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, ?_⟩, E, rfl⟩
  rfl

/-- A presentation of `div(ω) + B`, coefficientwise, is a presentation as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum_of_coeff {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X}
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ) :
    Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (C j) := by
  ext Γ
  have := h Γ
  change (Divisor.toRDivisor (divisorOfForm ω) + B).coeff Γ =
    (∑ j, r j • Divisor.toRDivisor (C j)).coeff Γ
  rw [coeff_sum_smul_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
    coeff_divisorOfForm]
  exact this

/-- Every presentation of `div(ω) + B` by Cartier divisors computes a discrepancy on every
proper model. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {B : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ a, IsDiscrepancyWith sX n B ω r L E a := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨(E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * ((L' j).coeff E.E : ℝ), hX, hn, hω0,
    hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- A log discrepancy `a` of a proper model `E` gives the discrepancy `a - 1` of its valuation,
computed with any canonical divisor `K` for which `K + B` is `ℝ`-Cartier. -/
private theorem isDiscrepancy_of_isLogDiscrepancy [PerfectField k] (hX : IsNormalVariety k sX)
    {n n' : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : IsCartierCombination (Divisor.toRDivisor K + B)) {E : ProperDivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n' B E.toDivisorOver a) :
    IsDiscrepancy sX n K B E.valuation (a - 1) := by
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨-, -, ω', hω0', ⟨K', hK', hK'ω⟩, m', r', C, C', hCc, hsum', hpb, ha⟩ := h
  obtain rfl : n = n' := by
    have h' := hK'.topologicalKrullDim_eq
    rw [hn] at h'
    exact_mod_cast h'
  have hw' : IsDiscrepancyWith sX n B ω' r' C E (a - 1) :=
    ⟨hX, hn, hω0', hCc, toRDivisor_add_eq_sum_of_coeff hsum', C', hpb, by linarith⟩
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum₁ : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum₁ E
  rw [← hc.eq hw' rfl]
  exact ⟨hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation E, E, ω, m, r, L, rfl, rfl, hc⟩

end Dictionary

/-! ### Log discrepancies over a reduced snc divisor -/

section ReducedSNC

open MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet

variable {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- On a smooth variety, `K + Δ` is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_add_of_isSmoothScheme (hsm : IsSmoothScheme sX)
    (K Δ : Divisor X) :
    IsCartierCombination (Divisor.toRDivisor K + Divisor.toRDivisor Δ) := by
  refine ⟨1, fun _ => 1, fun _ => K + Δ, fun _ => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _,
    ?_⟩
  ext P
  simp [DivisorWithCoeffs.coeff_mapCoeffs]

open Classical in
/-- **Log discrepancies over a reduced snc boundary.** Let `X` be a smooth variety over a perfect
field and `Δ` a reduced snc divisor. Every log discrepancy `b = a(ν, X, Δ)` of a divisor `ν` over
`X` is a natural number `l` with `codim_X Z ≤ l + #{components of Δ containing Z}`, `Z` the center
of `ν`; and `b = 0` when `ν` has the valuation of a component of `Δ`. -/
private theorem logDiscrepancy_reducedSNC (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {Δ : Divisor X} (hΔ : MMP.Fourfold.IsReducedSNC sX Δ) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (ν : ProperDivisorOver k sX) {n' : ℕ} {b : ℝ}
    (hb : MMP.Intersection.IsLogDiscrepancy sX n' (Divisor.toRDivisor Δ) ν.toDivisorOver b) :
    (∃ l : ℕ, b = l ∧ codimension ν.center ≤
      (l + (Δ.support.filter fun P => (ν.center : Set X) ⊆ P.support).card : ℕ∞)) ∧
    ∀ Q ∈ Δ.support, ν.valuation = Q.divisorialValuation → b = 0 := by
  classical
  have hd := isDiscrepancy_of_isLogDiscrepancy hX hK
    (isCartierCombination_add_of_isSmoothScheme hsm K Δ) hb
  have hl : MMP.Flips.IsLogDiscrepancy sX n K (Divisor.toRDivisor Δ) ν.valuation b :=
    ⟨b - 1, hd, by ring⟩
  have hBS : ∀ P, (Divisor.toRDivisor Δ).coeff P ≠ 0 → P ∈ Δ.support := fun P hP => by
    rw [Divisor.coeff_toRDivisor] at hP
    exact Finsupp.mem_support_iff.mpr (by exact_mod_cast hP)
  have h1 : ∀ P ∈ Δ.support, (Divisor.toRDivisor Δ).coeff P = 1 := fun P hP => by
    rw [Divisor.coeff_toRDivisor]
    rcases hΔ.1 P with h | h
    · exact absurd h (Finsupp.mem_support_iff.mp hP)
    · simp [h]
  obtain ⟨l, m, hbl, hcl, -, hcod, -⟩ :=
    exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor sX hX.1 hsm ⟨hΔ.1, hΔ.2.1, fun p _ => hΔ.2.2 p⟩
      hBS ν hl
  have hsum : ∑ P ∈ Δ.support, (m P : ℝ) * (1 - (Divisor.toRDivisor Δ).coeff P) = 0 :=
    Finset.sum_eq_zero fun P hP => by rw [h1 P hP]; ring
  rw [hsum, add_zero] at hbl
  refine ⟨⟨l, hbl, hcod⟩, fun Q hQ hν => ?_⟩
  have := hcl Q hQ b (hν ▸ hl)
  rw [this, h1 Q hQ, sub_self]

end ReducedSNC

/-! ### Centers of codimension at most the number of components through them -/

section Stratum

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

open Classical in
/-- Let `Δ` be an snc divisor and `z` a point of `X` such that `codim_X closure {z}` is at most the
number of components of `Δ` containing `closure {z}`. Then `closure {z}` is a stratum of `Δ`: an
irreducible set `T ⊋ closure {z}` inside these components would have a generic point `w` whose
local ring has a regular system of parameters containing a local equation of each of them, so
`codim w ≥ #components ≥ codim z > codim w`. -/
private theorem isSNCStratum_closure_singleton {Δ : Divisor X} (hΔ : DivisorWithCoeffs.IsSNC sX Δ)
    (z : X) (hz : Order.coheight z ≤
      ((Δ.support.filter fun P => closure {z} ⊆ (P.support : Set X)).card : ℕ∞)) :
    MMP.Fourfold.IsSNCStratum Δ (closure {z}) := by
  set J := Δ.support.filter fun P => closure {z} ⊆ (P.support : Set X) with hJ
  refine ⟨J, Finset.filter_subset _ _, ⟨isIrreducible_singleton.closure, ?_⟩, ?_⟩
  · exact Set.subset_iInter₂ fun E hE => (Finset.mem_filter.mp hE).2
  rintro T ⟨hT, hTJ⟩ hzT
  have hw := hT.isGenericPoint_genericPoint_closure
  set w := hT.genericPoint
  have hwJ : ∀ E ∈ J, w ∈ E.support := fun E hE => by
    have hsub : closure T ⊆ E.support :=
      closure_minimal (fun t ht => Set.mem_iInter₂.mp (hTJ ht) E hE) E.idealSheaf.support.isClosed
    exact hsub hw.mem
  have hwz : w ⤳ z := hw.specializes (subset_closure (hzT (subset_closure rfl)))
  obtain ⟨n, zz, j, hreg, hinj, -⟩ := hΔ.2 w
  have hcard : J.card ≤ n := by
    let g : J → {E : MMP.Mori.PrimeDivisor X // E ∈ Δ.support ∧ w ∈ E.support} :=
      fun E => ⟨E.1, Finset.filter_subset _ _ E.2, hwJ E.1 E.2⟩
    have hg : Function.Injective g := fun a b h =>
      Subtype.ext (congrArg (fun e => e.1) h : (g a).1 = (g b).1)
    simpa using Fintype.card_le_of_injective _ (hinj.comp hg)
  have hcw : Order.coheight w = n := by
    have h := hreg.2
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  by_cases hwz' : w = z
  · intro t ht
    rw [← hwz', hw.def]
    exact subset_closure ht
  · exfalso
    have hlt : z < w := lt_of_le_not_ge hwz fun h => hwz' (hwz.antisymm h).eq
    have h1 := Order.coheight_strictAnti hlt (by rw [hcw]; exact ENat.coe_lt_top n)
    rw [hcw] at h1
    have h2 : Order.coheight z ≤ n := hz.trans (by exact_mod_cast hcard)
    exact absurd (h1.trans_le h2) (lt_irrefl _)

end Stratum

/-! ### Prime divisors of log discrepancy zero -/

section Zero

open MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso {Y X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor Y) (Q : MMP.Mori.PrimeDivisor X)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- Outside `Ex(f)`, a prime divisor lies over a prime divisor with the same valuation. -/
private theorem exists_valuationOver_eq {Y X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (P : MMP.Mori.PrimeDivisor Y) (hP : P.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set Y)) :
    ∃ Γ : MMP.Mori.PrimeDivisor X, f P.genericPoint = Γ.genericPoint ∧
      P.valuationOver f = Γ.divisorialValuation := by
  have hb : f P.genericPoint ∈ MMP.Mori.biregularLocus f := not_not.mp hP
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm, ?_⟩
  have := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hb
  exact valuationOver_eq_of_isIso f P _
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm

variable {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

open Classical in
/-- **Divisors of log discrepancy zero.** Let `X` be a smooth variety, `Δ` a reduced snc divisor
and `ν = (Y, f, E)` a divisor over `X` such that `f` is an isomorphism over the generic point of
every stratum of `Δ`. Then `a(ν, X, Δ) = 0` exactly when `f(η_E)` lies in the biregular locus of
`f` and is the generic point of a component of `Δ`. -/
private theorem logDiscrepancy_eq_zero_iff (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {Δ : Divisor X} (hΔ : MMP.Fourfold.IsReducedSNC sX Δ) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (ν : ProperDivisorOver k sX)
    (hiso : ∀ S : Set X, MMP.Fourfold.IsSNCStratum Δ S →
      (S ∩ (biregularLocus ν.f : Set X)).Nonempty)
    {n' : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n' (Divisor.toRDivisor Δ) ν.toDivisorOver a) :
    a = 0 ↔ ν.f ν.E.genericPoint ∈ biregularLocus ν.f ∧
      ∃ Q ∈ Δ.support, ν.f ν.E.genericPoint = Q.genericPoint := by
  haveI := ν.isIntegral
  haveI := ν.isNormal
  haveI := ν.isLocallyNoetherian
  haveI := ν.isDominant
  obtain ⟨⟨l, hal, hcod⟩, hzero⟩ := logDiscrepancy_reducedSNC hX hsm hΔ hK ν ha
  set z := ν.f ν.E.genericPoint with hz
  have hc : (ν.center : Set X) = closure {z} := by
    rw [ν.center_eq_toDivisorOver_center]
    exact ν.toDivisorOver.center_eq_closure_genericPoint
  have hcodz : codimension ν.center = Order.coheight z := by
    rw [ν.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center]
  constructor
  · intro ha0
    have hl : l = 0 := by exact_mod_cast (hal.symm.trans ha0)
    subst hl
    simp only [hc, hcodz, Nat.cast_zero, zero_add] at hcod
    have hstr := isSNCStratum_closure_singleton hΔ.2 z (by exact_mod_cast hcod)
    obtain ⟨x, hxz, hxU⟩ := hiso _ hstr
    have hzU : z ∈ biregularLocus ν.f :=
      (specializes_iff_mem_closure.mpr hxz).mem_open (biregularLocus ν.f).isOpen hxU
    have hco : Order.coheight z = 1 := by
      rw [hz, MMP.Positivity.coheight_map_of_mem_biregularLocus ν.f hzU,
        ν.E.coheight_genericPoint]
    rw [hco] at hcod
    obtain ⟨Q, hQ⟩ := Finset.card_pos.mp (by exact_mod_cast hcod)
    obtain ⟨hQΔ, hzQ⟩ := Finset.mem_filter.mp hQ
    refine ⟨hzU, Q, hQΔ, ?_⟩
    have hgen := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hco
    have hmem : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hco).genericPoint ∈ Q.support := by
      rw [hgen]; exact hzQ (subset_closure rfl)
    rw [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hmem]
    exact hgen.symm
  · rintro ⟨hzU, Q, hQΔ, hzQ⟩
    obtain ⟨Γ, hΓ, hv⟩ := exists_valuationOver_eq ν.f ν.E (fun h => h hzU)
    obtain rfl : Γ = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hΓ.symm.trans hzQ)
    exact hzero Γ hQΔ hv

end Zero

/-! ### The strict transform -/

section StrictTransform

open MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet

/-- A partial isomorphism representing the rational map of `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{0}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A partial map representing the inverse of the rational map of `f` is a right inverse of `f`
on its domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{0}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- The transform of a prime divisor `P` under a rational map defined at its generic point is the
closure of the image of that generic point. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X)
    (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono
        (Set.singleton_subset_iff.mpr ⟨MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, hP⟩)
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · exact Set.singleton_subset_iff.mpr
      ⟨⟨P.genericPoint, hP⟩, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, rfl⟩

/-- A rational map defined at the generic point of `P` and sending it to the generic point of `E`
transforms `P` into `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties, the transform of a prime
divisor `P` of `X` under `f⁻¹` is the prime divisor `E` of `Y` with `f(η_E) = η_P`. -/
private theorem transformPrimeDivisor_inverse_eq_some {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor Y)
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsDominant f := hf.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (f ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  set g := MMP.Mori.RationalMap.IsBirational.inverse hf with hg_def
  have hdef : MMP.Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX f hY.1 hf
    have h2 := le_closedsCodimension_iff.mp hcodim
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom g).compl.isClosed)
    have h3 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
      rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
        (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
        Order.coheight_orderIso, P.coheight_genericPoint]
    rw [h3] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- **Valuative criterion at a divisor.** A proper birational morphism `f : Y ⟶ X` onto a normal
scheme is an isomorphism of local rings over the generic point of each prime divisor `Q` of `X`. -/
private theorem exists_primeDivisor_isIso_stalkMap {Y X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor X) :
    ∃ E : MMP.Mori.PrimeDivisor Y,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- A divisor whose prime divisors are never sent to `P` has coefficient zero along `P` after the
map. -/
private theorem mapPrimeDivisors_apply_eq_zero_of_forall_ne {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {P : MMP.Mori.PrimeDivisor Y} (h : ∀ E, φ E ≠ some P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D P = 0 := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hE : φ E with _ | E'
    · rfl
    · have hne : E' ≠ P := fun h' => h E (by rw [hE, h'])
      exact Finsupp.single_eq_of_ne hne.symm

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Over the biregular locus, the strict transform `f⁻¹_* D` has, along `P`, the coefficient of
`D` along the prime divisor of `X` whose generic point is `f(η_P)`. -/
private theorem coeff_birationalInverseTransform_of_mem (hX : IsNormalVariety k sX)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) {Y : Scheme.{0}} {f : Y ⟶ X}
    [IsProper f] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor Y)
    (Q : MMP.Mori.PrimeDivisor X) (hPQ : f P.genericPoint = Q.genericPoint) :
    (birationalInverseTransform f hf D).coeff P = D.coeff Q := by
  have htr := transformPrimeDivisor_inverse_eq_some hX f hY hf Q P hPQ
  have huniq : ∀ Q', MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hf) Q' = some P → Q' = Q := by
    intro Q' h'
    obtain ⟨P', hP', -⟩ := exists_primeDivisor_isIso_stalkMap f hf Q'
    have h'' := transformPrimeDivisor_inverse_eq_some hX f hY hf Q' P' hP'
    rw [h'] at h''
    obtain rfl := Option.some.inj h''
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP'.symm.trans hPQ)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr huniq D

/-- Off the biregular locus, the strict transform `f⁻¹_* D` has coefficient zero along `P`. -/
private theorem coeff_birationalInverseTransform_of_notMem (hX : IsNormalVariety k sX)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) {Y : Scheme.{0}} {f : Y ⟶ X}
    [IsProper f] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor Y)
    (hP : f P.genericPoint ∉ MMP.Mori.biregularLocus f) :
    (birationalInverseTransform f hf D).coeff P = 0 := by
  refine mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun Q hQ => hP ?_) D
  obtain ⟨P', hP', -⟩ := exists_primeDivisor_isIso_stalkMap f hf Q
  have h'' := transformPrimeDivisor_inverse_eq_some hX f hY hf Q P' hP'
  rw [hQ] at h''
  obtain rfl := Option.some.inj h''
  refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hX f hY.1 hf ?_
  rw [ringKrullDim_stalk_eq_coheight, hP', Q.coheight_genericPoint]
  rfl

end StrictTransform

/-! ### The log discrepancy computed with one top form -/

section OneForm

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- With `K_X = div(ω)`, `K_Y = div(μ^*ω)` and `C'` the pull-back of the Cartier divisor
`K_X + Δ`, `1 + coeff_P(K_Y - C')` is a log discrepancy `a(P, X, Δ)` of every prime divisor `P`
of `Y`. -/
private theorem isLogDiscrepancy_one_add_coeff (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n) (Δ : Divisor X) {Y : Scheme.{0}}
    (μ : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant μ]
    [CompactSpace Y] [LocallyOfFiniteType (μ ≫ sX)] [IsProper μ]
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ) {C' : Divisor Y}
    (hC' : ∃ hC, (divisorOfForm ω + Δ).IsPullback μ hC C') (P : MMP.Mori.PrimeDivisor Y) :
    MMP.Intersection.IsLogDiscrepancy sX n (Divisor.toRDivisor Δ) ⟨Y, μ, hY, hμ, P⟩
      (1 + ((divisorOfForm (pullbackRationalPluriForms sX μ ω)).coeff P : ℝ) - C'.coeff P) := by
  refine ⟨hX, inferInstance, ω, hω0, ⟨divisorOfForm ω, hK, fun Γ => rfl⟩, 1, fun _ => 1,
    fun _ => divisorOfForm ω + Δ, fun _ => C',
    fun _ => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _, fun Γ => ?_, fun _ => hC', ?_⟩
  · simp
  · simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, coeff_divisorOfForm]
    rfl

end OneForm

/-! ### Openness of relative ampleness -/

section Openness

open Stacks.Ample Stacks.RelativeVeryAmple

/-- A nonvanishing section of `G ⊗ P`, from a section of `G` nonvanishing at `x` and a section
of `P` whose nonvanishing locus is an affine open containing `x`. -/
private theorem exists_affine_nonvanishing_tensor {X : Scheme.{0}} (G P N : X.Modules)
    [IsInvertibleModule X G] [IsInvertibleModule X P] [IsInvertibleModule X N]
    (e : tensorModules X G P ≅ N)
    (t : G.sections) (s : Γ(P, ⊤)) (U : X.Opens)
    (hUs : (U : Set X) = nonvanishingLocus _ s) (hU : IsAffineOpen U) {x : X}
    (hxt : x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) _ t)
    (hxU : x ∈ U) :
    ∃ f : Γ(N, ⊤), x ∈ nonvanishingLocus _ f ∧
        IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen X _ f) := by
  set s₀ := Stacks.SheafOfModules.sectionsOfTop _ s
  set v := SheafOfModules.sectionsMap e.hom (tensorSections G _ t s₀)
  have h2 : ∀ z : X, z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) G t ↔
      z ∈ Stacks.NonvanishingOpen.nonvanishingOpen X G (t.eval (Opposite.op ⊤)) := fun z =>
    Set.ext_iff.1 (Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X G t) z
  have h1 : ∀ z : X, z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) _ s₀ ↔
      z ∈ U := fun z => by
    rw [Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop, ← hUs]
    rfl
  have hmem : ∀ z : X,
      z ∈ nonvanishingLocus N (v.eval (Opposite.op ⊤)) ↔
      z ∈ U ∧ z ∈ Stacks.NonvanishingOpen.nonvanishingOpen X G (t.eval (Opposite.op ⊤)) := by
    intro z
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval]
    exact (nonvanishingLocus_iso e (tensorSections G _ t s₀) z).trans
      ((tensorSections_nonvanishing_iff t s₀ z).trans (and_comm.trans (and_congr (h1 z) (h2 z))))
  refine ⟨v.eval (Opposite.op ⊤), (hmem x).2 ⟨hxU, (h2 x).1 hxt⟩, ?_⟩
  convert Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (M := G) (s := t.eval (Opposite.op ⊤)) hU using 1
  ext z
  exact hmem z

/-- `(M ⊗ L^{⊗ j}) ⊗ L^{⊗ k} ≅ M ⊗ L^{⊗ (j + k)}`. -/
private noncomputable def splitIso {X : Scheme.{0}} (L M : X.Modules) [IsInvertibleModule X L]
    (j k : ℕ) :
    tensorModules X (tensorModules X M (tensorPowModule X L (j : ℤ)))
      (tensorPowModule X L (k : ℤ)) ≅ tensorModules X M (tensorPowModule X L ((j + k : ℕ) : ℤ)) :=
  Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
    tensorModulesMapIso X (Iso.refl _)
      (tensorPowModuleAddIso X _ (j : ℤ) (k : ℤ) ≪≫ tensorPowModuleCongr X _ (by push_cast; ring))

/-- If `L` is ample and `M` is invertible, then `M ⊗ L^{⊗ m}` is ample for `m ≫ 0`. -/
private theorem eventually_isAmple_tensorModules_tensorPowModule {X : Scheme.{0}}
    (L M : X.Modules) [IsInvertibleModule X L] [IsInvertibleModule X M] (hL : IsAmple X L) :
    ∀ᶠ m : ℕ in Filter.atTop, IsAmple X (tensorModules X M (tensorPowModule X L (m : ℤ))) := by
  have : SheafOfModules.IsFiniteType.{0, 0, 0} M :=
    Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule M
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hL).2 M inferInstance inferInstance
  haveI : CompactSpace X := hL.1
  choose k hk s U hUs hxU hUaff using hL.2
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ ((U x : X.Opens) : Set X))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine Filter.eventually_atTop.2 ⟨T.sup k + n₀.toNat, fun m hm => ?_⟩
  refine Stacks.Ample.isAmple_of_forall_exists_affine_nonvanishingLocus _ fun x => ?_
  obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  have hsup : k y ≤ T.sup k := Finset.le_sup hyT
  obtain ⟨j, rfl⟩ : ∃ j, m = j + k y := ⟨m - k y, by omega⟩
  obtain ⟨σ, -⟩ := hn₀ j (by omega)
  set G := tensorModules X M (tensorPowModule X L (j : ℤ))
  haveI : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property G :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory X
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso X M
    (tensorPowModule X L (j : ℤ))
  haveI : @Epi (SheafOfModules.{0} X.ringCatSheaf) _ _ _ i.hom :=
    @IsIso.epi_of_iso _ _ _ _ i.hom i.isIso_hom
  obtain ⟨a, ha⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing G (σ.ofEpi i.hom) x
  exact exists_affine_nonvanishing_tensor G _ _ (splitIso L M j (k y)) _ (s y) (U y) (hUs y)
    (hUaff y) ha hxy

/-- The pull-back of `𝒪_Y(nH + F)` along `f : X ⟶ Y` is `f^*𝒪_Y(F) ⊗ (f^*𝒪_Y(H))^{⊗ n}`, for
Cartier divisors `H` and `F`. -/
private theorem nonempty_modulePullback_divisorialSheaf_nsmul_add_iso {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : X ⟶ Y) {H F : Divisor Y}
    (hH : H.IsCartier) (hF : F.IsCartier) (n : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    Nonempty ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
        (n • H + F).divisorialSheaf ≅
      tensorModules X ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
          F.divisorialSheaf)
        (tensorPowModule X ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
          H.divisorialSheaf) (n : ℤ))) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  set P := RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom
  induction n with
  | zero =>
    exact ⟨eqToIso (by rw [zero_smul, zero_add]) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor X _).symm ≪≫
      tensorModulesMapIso X (Iso.refl _) (tensorPowModuleZeroIso X _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [succ_nsmul, add_right_comm]) ≪≫
      P.mapIso (((hH.nsmul n).add hF).divisorialSheafTensorIso hH).symm ≪≫
      pullbackTensorModulesIso f _ _ ≪≫
      tensorModulesMapIso X e (tensorPowModuleOneIso X _).symm ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
      tensorModulesMapIso X (Iso.refl _)
        (tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫ tensorPowModuleCongr X _ (by push_cast; ring))⟩

/-- If `H` is a `g`-ample Cartier divisor and `F` is any Cartier divisor, then `mH + F` is
`g`-ample for some `m > 0`, provided the base is quasi-compact. -/
private theorem exists_isRelativelyAmple_nsmul_add {Y Z : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [CompactSpace Z] (g : Y ⟶ Z)
    {H F : Divisor Y}
    (hHc : H.IsCartier) (hHa : H.IsRelativelyAmple g hHc) (hF : F.IsCartier) :
    ∃ m : ℕ, 0 < m ∧ (m • H + F).IsRelativelyAmple g ((hHc.nsmul m).add hF) := by
  haveI := hHc.isInvertibleModule_divisorialSheaf
  haveI := hF.isInvertibleModule_divisorialSheaf
  choose V' hVa hzV hamp using hHa
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z : Z ↦ ((V' z : Z.Opens) : Set Z))
    (fun z ↦ (V' z).isOpen) (fun z _ ↦ Set.mem_iUnion.2 ⟨z, hzV z⟩)
  have hev : ∀ v ∈ T, ∀ᶠ m : ℕ in Filter.atTop,
      haveI := ((hHc.nsmul m).add hF).isInvertibleModule_divisorialSheaf
      IsAmple (g ⁻¹ᵁ V' v).toScheme
        ((RingedSpaceModuleAdjunction.modulePullback
          (g ⁻¹ᵁ V' v).ι.toLRSHom.toShHom).obj (m • H + F).divisorialSheaf) := by
    intro v _
    let W := (g ⁻¹ᵁ V' v).toScheme
    let P := RingedSpaceModuleAdjunction.modulePullback (g ⁻¹ᵁ V' v).ι.toLRSHom.toShHom
    haveI hPF : IsInvertibleModule W (P.obj F.divisorialSheaf) := inferInstance
    haveI hPH : IsInvertibleModule W (P.obj H.divisorialSheaf) := inferInstance
    filter_upwards [eventually_isAmple_tensorModules_tensorPowModule (P.obj H.divisorialSheaf)
      (P.obj F.divisorialSheaf) (hamp v)]
      with m hm
    haveI := ((hHc.nsmul m).add hF).isInvertibleModule_divisorialSheaf
    obtain ⟨e⟩ := nonempty_modulePullback_divisorialSheaf_nsmul_add_iso (g ⁻¹ᵁ V' v).ι hHc hF m
    exact (@isAmple_congr _ _ _ inferInstance
      (@Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules _ _ _ inferInstance
        (isInvertibleModule_tensorPowModule _ _ _)) e).2 hm
  obtain ⟨m, hm, hm0⟩ := (((Filter.eventually_all_finset T).2 hev).and
    (Filter.eventually_gt_atTop 0)).exists
  refine ⟨m, hm0, fun z => ?_⟩
  obtain ⟨v, hvT, hzv⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
  exact ⟨V' v, hVa v, hzv, hm v hvT⟩

end Openness

/-! ### Auxiliary facts on coefficients -/

section Coefficients

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]

/-- The coefficient along `H` of the pull-back of a Cartier divisor `C` vanishes when `C` has
coefficient zero along every prime divisor through `f(η_H)`. -/
private theorem coeff_isPullback_eq_zero_of_forall {C : Divisor X} (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : Divisor Y} (h : C.IsPullback f hC C') (H : MMP.Mori.PrimeDivisor Y)
    (h0 : ∀ Γ : MMP.Mori.PrimeDivisor X, f H.genericPoint ∈ Γ.support → C.coeff Γ = 0) :
    C'.coeff H = 0 := by
  set x := f H.genericPoint with hx
  obtain ⟨V, hV, φ, hφ⟩ := hCc x
  set Z0 := MMP.Mori.pointComponent x with hZ0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : MMP.Mori.RationalFunctions X) with hgdef
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ H hV Z0]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := f) H
    (fun _ : Unit => g) (fun _ => hg) (fun _ => 1) fun Γ hΓ => by
      have hZ : Γ.component = Z0 := Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
      have e := hφ Γ ⟨x, hΓ, hV⟩
      rw [h0 Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ] at e
      have e' : Scheme.ord g Γ.genericPoint = 0 := e.symm
      simp [e']
  simpa using key

end Coefficients

section Exceptional

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor over a normal variety is exceptional (in the sense of Kollár–Mori) if and only if
its center has codimension at least two. -/
private theorem divisorOver_isExceptional_iff_two_le_coheight (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

end Exceptional

/-! ### The divisor of log discrepancy zero is the strict transform -/

section ZeroDivisor

open MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet

variable {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- If `μ` is an isomorphism over the generic point of every stratum of the reduced snc divisor
`Δ`, the components of the divisor `Γ` of log discrepancy zero for `(X, Δ)` are the prime divisors
of `Y` lying, over the biregular locus of `μ`, over components of `Δ`. -/
private theorem coeff_eq_one_iff_of_isZeroLogDiscrepancyDivisor (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {Δ : Divisor X} (hΔ : MMP.Fourfold.IsReducedSNC sX Δ) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {Y : Scheme.{0}} (μ : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsDominant μ] [CompactSpace Y] [LocallyOfFiniteType (μ ≫ sX)] [IsProper μ]
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (hiso : ∀ S : Set X, MMP.Fourfold.IsSNCStratum Δ S →
      (S ∩ (biregularLocus μ : Set X)).Nonempty)
    {Γ : Divisor Y} (hΓ : MMP.Fourfold.IsZeroLogDiscrepancyDivisor sX μ hY hμ Δ Γ)
    (P : MMP.Mori.PrimeDivisor Y) :
    Γ.coeff P = 1 ↔ μ P.genericPoint ∈ biregularLocus μ ∧
      ∃ Q ∈ Δ.support, μ P.genericPoint = Q.genericPoint := by
  obtain ⟨C', hC'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant μ
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsm (divisorOfForm ω + Δ))
  have hzero := fun {n' : ℕ} {a : ℝ} =>
    logDiscrepancy_eq_zero_iff (n' := n') (a := a) hX hsm hΔ hK
      ⟨⟨Y, μ, hY, hμ, P⟩, inferInstance⟩ hiso
  have hA := isLogDiscrepancy_one_add_coeff hX hsm hω0 hK Δ μ hY hμ ⟨_, hC'⟩ P
  rw [hΓ.2 P]
  refine ⟨fun ⟨_, h⟩ => (hzero h).1 rfl, fun h => ⟨n, ?_⟩⟩
  rwa [(hzero hA).2 h] at hA

end ZeroDivisor

section StrictTransformEq

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Let `Δ` be a reduced divisor on `X` and `Γ` a reduced divisor on `Y` whose components are the
prime divisors of `Y` lying, over the biregular locus of `f`, over components of `Δ`. Then `Γ` is
the strict transform `f⁻¹_* Δ`. -/
private theorem eq_birationalInverseTransform_of_coeff_eq_one_iff (hX : IsNormalVariety k sX)
    {Δ : Divisor X} (hΔ : MMP.Intersection.IsReducedEffective Δ) {Y : Scheme.{0}} {f : Y ⟶ X}
    [IsProper f] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {Γ : Divisor Y}
    (hΓ : MMP.Intersection.IsReducedEffective Γ)
    (hΓ1 : ∀ P, Γ.coeff P = 1 ↔ f P.genericPoint ∈ MMP.Mori.biregularLocus f ∧
      ∃ Q ∈ Δ.support, f P.genericPoint = Q.genericPoint) :
    Γ = MMP.Flips.birationalInverseTransform f hf Δ := by
  refine DivisorWithCoeffs.ext' fun P => ?_
  by_cases hb : f P.genericPoint ∈ MMP.Mori.biregularLocus f
  · have hco : Order.coheight (f P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
    have hPQ : f P.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    rw [coeff_birationalInverseTransform_of_mem hX Δ hY hf P Q hPQ]
    have key : Γ.coeff P = 1 ↔ Δ.coeff Q ≠ 0 := by
      rw [hΓ1 P, hPQ]
      refine ⟨?_, fun h => ⟨hPQ ▸ hb, Q, Finsupp.mem_support_iff.mpr h, rfl⟩⟩
      rintro ⟨-, Q', hQ', h⟩
      obtain rfl := AlgebraicGeometry.PrimeDivisor.genericPoint_injective h
      exact Finsupp.mem_support_iff.mp hQ'
    rcases hΓ P with h | h <;> rcases hΔ Q with h' | h' <;> simp [h, h'] at key ⊢
  · rw [coeff_birationalInverseTransform_of_notMem hX Δ hY hf P hb]
    exact (hΓ P).resolve_right fun h => hb ((hΓ1 P).1 h).1

end StrictTransformEq

/-! ### Supports -/

section Supports

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]

/-- On a scheme where every Weil divisor is Cartier, the pull-back `f^*D` of a `ℚ`-divisor is
supported on the prime divisors lying over `Supp D`. -/
private theorem map_genericPoint_mem_supp_of_isPullback {D : QDivisor X}
    {hD : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp} {F : QDivisor Y}
    (hF : D.IsPullback f hD F) (hc : ∀ G : Divisor X, G.IsCartier) {P : MMP.Mori.PrimeDivisor Y}
    (hP : F.coeff P ≠ 0) : f P.genericPoint ∈ D.supp := by
  obtain ⟨q, hq, Dq, hDq⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor D
  obtain ⟨Dq', hDq', hDqpb⟩ := hF q hq Dq hDq (hc Dq)
  by_contra hns
  have h0 : Dq'.coeff P = 0 :=
    coeff_isPullback_eq_zero_of_forall (hc Dq) hDqpb P fun Γ hΓ => by
      have hD0 : D.coeff Γ = 0 := by
        by_contra h
        exact hns (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, h, hΓ⟩)
      have := congrArg (fun G : QDivisor X => G.coeff Γ) hDq
      simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, hD0, smul_zero] at this
      exact_mod_cast this
  have := congrArg (fun G : QDivisor Y => G.coeff P) hDq'
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, h0, Int.cast_zero] at this
  exact hP ((smul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast hq.ne'))

end Supports

/-- A divisor whose support contains no stratum of `Δ` has coefficient zero along every
component of `Δ`, a component being a stratum. -/
private theorem coeff_eq_zero_of_containsNoStratum {X : Scheme.{0}} {Δ : Divisor X}
    {D : QDivisor X} (hDΔ : MMP.Fourfold.ContainsNoStratum Δ D.supp)
    {Q : MMP.Mori.PrimeDivisor X} (hQ : Q ∈ Δ.support) : D.coeff Q = 0 := by
  by_contra h
  refine hDΔ Q.support ⟨{Q}, by simpa using hQ, ⟨?_, by simp⟩, fun T hT _ => ?_⟩ ?_
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  · simpa using hT.2
  · exact fun x hx => DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, h, hx⟩

/-- The support of `∑_{E ∈ s} E` is `s`. -/
private theorem support_sum_single {Y : Scheme.{0}} (s : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support = s := by
  classical
  ext P
  simp [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- A divisor supported on an snc divisor `S` of a smooth scheme is snc. -/
private theorem isSNC_of_genericPoint_mem {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (hsm : IsSmoothScheme sY)
    {S : Closeds Y} (hS : MMP.Mori.IsSNCSubset sY S) {R : Type*} [Zero R]
    (G : DivisorWithCoeffs R Y) (h : ∀ P, G.coeff P ≠ 0 → P.genericPoint ∈ (S : Set Y)) :
    G.IsSNC sY := by
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) sY hsm).of_support_subset
      fun P hP => absurd (h P (Finsupp.mem_support_iff.mp hP)) id
  · refine hsnc.of_support_subset fun P hP => ?_
    rw [support_sum_single]
    have h := h P (Finsupp.mem_support_iff.mp hP)
    rw [← hs] at h
    obtain ⟨Q, hQs, hPQ⟩ := Set.mem_iUnion₂.mp h
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPQ] at hQs

/-- Proof of `MMP.Fourfold.isZero_rightDerived_pushforward_adjointIdealSheaf`. -/
private theorem eq_inverseTransform_and_isZero_rightDerived
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (Δ : Divisor X) (hΔ : MMP.Fourfold.IsReducedSNC sX Δ)
    (D : QDivisor X) (hD0 : ∀ P, 0 ≤ D.coeff P) (hDΔ : MMP.Fourfold.ContainsNoStratum Δ D.supp)
    {Y : Scheme.{0}} (μ : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsDominant μ] (hlog : MMP.Fourfold.IsLogResolution sX (Divisor.toQDivisor Δ + D) μ)
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (hiso : ∀ S : Set X, MMP.Fourfold.IsSNCStratum Δ S →
      (S ∩ (biregularLocus μ : Set X)).Nonempty)
    (Γ E : Divisor Y) (hΓ : MMP.Fourfold.IsZeroLogDiscrepancyDivisor sX μ hY hμ Δ Γ)
    (hE : MMP.Fourfold.IsAdjointDiscrepancyDivisor sX μ hY hμ Δ Γ E)
    (hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp)
    (F : QDivisor Y) (hF : D.IsPullback μ hD F) :
    Γ = MMP.Flips.birationalInverseTransform μ hμ Δ ∧
      ∀ T : Divisor Y, 0 ≤ T → T ≤ Γ → ∀ i : ℕ, 0 < i →
        Limits.IsZero (((Scheme.Modules.pushforward μ).rightDerived i).obj
          (E - MMP.Intersection.WeilRDivisor.roundDown (QDivisor.toRDivisor F) -
            T).divisorialSheaf) := by
  classical
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsProper μ := hlog.isProper
  haveI : AlgebraicGeometry.IsVariety k (μ ≫ sX) := hY.1
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  obtain ⟨ω, hω0, hK⟩ := exists_form_isCanonicalDivisor hX hsm hn
  have hΓ1 := coeff_eq_one_iff_of_isZeroLogDiscrepancyDivisor hX hsm hΔ hω0 hK μ hY hμ hiso hΓ
  refine ⟨eq_birationalInverseTransform_of_coeff_eq_one_iff hX hΔ.1 hY hμ hΓ.1 hΓ1, ?_⟩
  intro T hT0 hTΓ i hi
  have hsmY : IsSmoothScheme (μ ≫ sX) := hlog.isSmoothScheme
  have hcartY : ∀ G : Divisor Y, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmY
  have hcartX : ∀ G : Divisor X, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  -- `K_Y + Γ = μ^*(K_X + Δ) + E`, coefficientwise, for `K_Y = div(μ^*ω)` and `C' = μ^*(K_X + Δ)`
  set C := divisorOfForm ω + Δ with hC
  obtain ⟨C', hC'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant μ (hcartX C)
  set KY := divisorOfForm (pullbackRationalPluriForms sX μ ω) with hKY
  have hEeq : ∀ P, E.coeff P = KY.coeff P - C'.coeff P + Γ.coeff P := fun P => by
    obtain ⟨n', a, ha, hEa⟩ := hE P
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
      (isLogDiscrepancy_one_add_coeff hX hsm hω0 hK Δ μ hY hμ ⟨_, hC'⟩ P)] at hEa
    have : (E.coeff P : ℝ) = ((KY.coeff P - C'.coeff P + Γ.coeff P : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  -- `K_Y` is a canonical divisor of `Y`
  have hKYc : KY.IsCanonicalDivisor (μ ≫ sX) n := by
    have hnY : topologicalKrullDim Y = n := by
      rw [← hn]
      exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (μ ≫ sX) hμ).symm
    have hσ0 : pullbackRationalPluriForms sX μ ω ≠ 0 :=
      MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' μ
        hμ.functionFieldMap_bijective
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) hω0
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (μ ≫ sX) hsmY hnY
    exact hK₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hσ0)
  -- an effective exceptional `F_x` with `-e F_x` Cartier and `μ`-ample
  obtain ⟨Fx, e, he, hFx0, hFxe, Dc, hDc, hDcF, hDca⟩ :=
    MMP.Mori.exists_isRelativelyAmple_neg_smul_of_isExceptional sX (μ ≫ sX)
      ⟨hX, fun G => ⟨1, one_pos, hcartX _⟩⟩ hY μ rfl hlog.isProjectiveMorphism hμ
  -- clearing the denominators of `D`
  obtain ⟨q, hq, Dq, hDq⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor D
  obtain ⟨Dq', hDq', hDqpb⟩ := hF q hq Dq hDq (hcartX Dq)
  -- `N(-e F_x) + q(Γ - T)` is `μ`-ample for some `N > 0`
  obtain ⟨N, hN, hNa⟩ := exists_isRelativelyAmple_nsmul_add μ hDc.neg hDca
    (hcartY ((q : ℤ) • (Γ - T)))
  have hnot : ∀ G : Divisor X, ∀ Z : irreducibleComponents Y,
      μ (componentGenericPoint Y Z) ∉ G.supp :=
    fun G => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp μ G
  have hDqc' : ∀ P, (Dq'.coeff P : ℚ) = q * F.coeff P := fun P => by
    simpa using congrArg (fun G : QDivisor Y => G.coeff P) hDq'
  have hDcc : ∀ P, (Dc.coeff P : ℚ) = e * Fx.coeff P := fun P => by
    simpa using congrArg (fun G : QDivisor Y => G.coeff P) hDcF
  -- along the components of `Γ`, `F` and `F_x` vanish
  have hFΓ : ∀ P, Γ.coeff P = 1 → F.coeff P = 0 := fun P hP => by
    by_contra hne
    obtain ⟨-, Q, hQ, hPQ⟩ := (hΓ1 P).1 hP
    obtain ⟨Q', hQ', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp
      (map_genericPoint_mem_supp_of_isPullback hF hcartX hne)
    rw [hPQ] at hmem
    obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hmem
    exact hQ' (coeff_eq_zero_of_containsNoStratum hDΔ hQ)
  have hexc : ∀ P, Fx.coeff P ≠ 0 → μ P.genericPoint ∉ biregularLocus μ := fun P h hb => by
    have hex := (divisorOver_isExceptional_iff_two_le_coheight hX ⟨Y, μ, hY, hμ, P⟩).1 (hFxe P h)
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus μ hb, P.coheight_genericPoint] at hex
    exact absurd hex (by decide)
  have hFxΓ : ∀ P, Γ.coeff P = 1 → Fx.coeff P = 0 := fun P hP =>
    not_not.mp fun h => hexc P h ((hΓ1 P).1 hP).1
  -- the choice of `ε = 1/M` and `δ = N e / (q M)`
  obtain ⟨M, hMbd, hM1⟩ := (((Filter.eventually_all_finset Fx.support).2 fun P _ =>
      (tendsto_const_div_atTop_nhds_zero_nat ((N * e : ℚ) / q * Fx.coeff P)).eventually
        (gt_mem_nhds (by linarith [Int.fract_lt_one (F.coeff P)] :
          (0 : ℚ) < 1 - Int.fract (F.coeff P)))).and
    (Filter.eventually_ge_atTop 1)).exists
  have hMpos : (0 : ℚ) < M := by exact_mod_cast hM1
  -- the `μ`-ample Cartier divisor `q M B`
  have hpbA : ((-(M : ℤ)) • ((q : ℤ) • C + Dq)).IsPullback μ (hnot _)
      ((-(M : ℤ)) • ((q : ℤ) • C' + Dq')) :=
    ((hC'.zsmul (hcartX C) (q : ℤ) (hnot _)).add ((hcartX C).zsmul _) (hcartX Dq) (hnot _)
      hDqpb).zsmul ((hcartX _).add (hcartX _)) (-(M : ℤ)) (hnot _)
  set Lam := N • (-Dc) + (q : ℤ) • (Γ - T) with hLam
  have hLamc : Lam.IsCartier := (hDc.neg.nsmul N).add (hcartY _)
  have hLa := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback μ hLamc hNa
    (hcartX _) hpbA (hcartY _)
  set Ltot := Lam + (-(M : ℤ)) • ((q : ℤ) • C' + Dq') with hLtot
  set B : QDivisor Y := ((q * M : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor Ltot with hB
  have hBamp : B.HasRelativelyAmpleMultiple μ := by
    refine ⟨q * M, Nat.mul_pos hq (by omega), Ltot, hLamc.add (hcartY _), ?_, hLa⟩
    refine DivisorWithCoeffs.ext' fun P => ?_
    have hqM : ((q * M : ℕ) : ℚ) ≠ 0 := by positivity
    simp only [hB, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      zsmul_eq_mul, Int.cast_natCast]
    field_simp
  -- the coefficients of `B`: `B = (L - K_Y) - Λ` with `Λ ∈ [0, 1)`
  set Λ : MMP.Mori.PrimeDivisor Y → ℚ := fun P => (1 - 1 / (M : ℚ)) * ((Γ - T).coeff P) +
    Int.fract (F.coeff P) + (N * e : ℚ) / (q * M) * Fx.coeff P with hΛ
  set z : MMP.Mori.PrimeDivisor Y → ℤ := fun P => -C'.coeff P + (Γ - T).coeff P -
    ⌊F.coeff P⌋ with hz
  have hBc : ∀ P, B.coeff P = z P - Λ P := fun P => by
    have hF := Int.floor_add_fract (F.coeff P)
    simp only [hB, hz, hΛ, hLtot, hLam, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_neg, smul_eq_mul, zsmul_eq_mul,
      nsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_sub,
      Nat.cast_mul]
    rw [hDcc P, hDqc' P]
    field_simp
    linear_combination ((q : ℚ) * M) * hF
  have hΓT : ∀ P, (Γ - T).coeff P = 0 ∨ ((Γ - T).coeff P = 1 ∧ Γ.coeff P = 1) := fun P => by
    have h0 : (0 : ℤ) ≤ T.coeff P := hT0 P
    have h1 : T.coeff P ≤ Γ.coeff P := hTΓ P
    rw [DivisorWithCoeffs.coeff_sub]
    rcases hΓ.1 P with h | h <;> rw [h] at h1 ⊢ <;> omega
  have hΛb : ∀ P, 0 ≤ Λ P ∧ Λ P < 1 := fun P => by
    have hFx : (0 : ℚ) ≤ Fx.coeff P := hFx0 P
    have hfr1 := Int.fract_lt_one (F.coeff P)
    have hinvM : 1 / (M : ℚ) ≤ 1 := by
      rw [div_le_one hMpos]; exact_mod_cast hM1
    have hinvM0 : (0 : ℚ) < 1 / (M : ℚ) := by positivity
    rcases hΓT P with h | ⟨h, hΓP⟩
    · simp only [hΛ, h, Int.cast_zero, mul_zero, zero_add]
      refine ⟨by positivity, ?_⟩
      by_cases hFxP : Fx.coeff P = 0
      · rwa [hFxP, mul_zero, add_zero]
      · have := hMbd P (Finsupp.mem_support_iff.mpr hFxP)
        have : (N * e : ℚ) / (q * M) * Fx.coeff P = (N * e : ℚ) / q * Fx.coeff P / M := by ring
        linarith
    · simp only [hΛ, h, Int.cast_one, mul_one, hFxΓ P hΓP, hFΓ P hΓP, Int.fract_zero, add_zero,
        mul_zero]
      constructor <;> linarith
  have hround : KY + B.roundUp =
      E - MMP.Intersection.WeilRDivisor.roundDown (QDivisor.toRDivisor F) - T := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    have h := hEeq P
    have hc : ⌈B.coeff P⌉ = z P := by
      rw [Int.ceil_eq_iff, hBc P]
      obtain ⟨h0, h1⟩ := hΛb P
      constructor <;> linarith
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp,
      DivisorWithCoeffs.coeff_sub, MMP.Intersection.WeilRDivisor.coeff_roundDown,
      QDivisor.coeff_toRDivisor, Rat.floor_cast, hc, hz] at h ⊢
    omega
  -- `{B}` is supported on the snc divisor `Ex(μ) ∪ μ⁻¹(Supp(Δ + D))`
  have hsuppS : ∀ x : X, (∃ Q : MMP.Mori.PrimeDivisor X,
      (Δ.coeff Q ≠ 0 ∨ D.coeff Q ≠ 0) ∧ x ∈ Q.support) →
      x ∈ (QDivisor.toRDivisor (Divisor.toQDivisor Δ + D)).supp := by
    rintro x ⟨Q, hQ, hxQ⟩
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, ?_, hxQ⟩
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    have hD := hD0 Q
    have hΔQ : (0 : ℚ) ≤ Δ.coeff Q := by rcases hΔ.1 Q with h | h <;> simp [h]
    have hpos : (0 : ℚ) < Δ.coeff Q + D.coeff Q := by
      rcases hQ with h | h
      · rw [(hΔ.1 Q).resolve_left h]; push_cast; linarith
      · exact add_pos_of_nonneg_of_pos hΔQ (lt_of_le_of_ne hD (Ne.symm h))
    exact_mod_cast hpos.ne'
  refine hround ▸
    MMP.Fourfold.isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp
      (μ ≫ sX) sX hsmY μ rfl hlog.isProjectiveMorphism hKYc B hBamp
      (isSNC_of_genericPoint_mem hsmY hlog.isSNCSubset _ fun P hP => ?_) i hi
  rw [DivisorWithCoeffs.coeff_fract, hBc P] at hP
  have hΛ0 : Λ P ≠ 0 := fun h => hP (by rw [h, sub_zero]; exact Int.fract_intCast _)
  rw [TopologicalSpace.Closeds.coe_sup, Set.mem_union]
  rcases hΓT P with hGT | ⟨-, hΓP⟩
  · by_cases hfr : Int.fract (F.coeff P) = 0
    · have hFxP : Fx.coeff P ≠ 0 := fun h => hΛ0 (by
        simp only [hΛ, hGT, hfr, h, Int.cast_zero, mul_zero, add_zero])
      exact Or.inl (MMP.Mori.mem_exceptionalSet.mpr (hexc P hFxP))
    · have hF0 : F.coeff P ≠ 0 := fun h => hfr (by rw [h, Int.fract_zero])
      obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp
        (map_genericPoint_mem_supp_of_isPullback hF hcartX hF0)
      exact Or.inr (hsuppS _ ⟨Q, Or.inr hQ, hxQ⟩)
  · obtain ⟨-, Q, hQ, hPQ⟩ := (hΓ1 P).1 hΓP
    refine Or.inr (hsuppS _ ⟨Q, Or.inl (Finsupp.mem_support_iff.mp hQ), ?_⟩)
    rw [hPQ]
    exact MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Q

end MMP.FourfoldProofs.FourfoldAdjointLocalVanishingProof

end

section

public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-- **Local vanishing for reduced-boundary adjoint ideals.** Let `X` be a smooth variety over an
algebraically closed field of characteristic zero, `Δ` a reduced snc divisor, `D` an effective
`ℚ`-divisor containing no stratum of `Δ`, and `μ : Y ⟶ X` a projective log resolution of `Δ + D`
that is an isomorphism over the generic point of every stratum of `Δ`. Let `Γ` be the reduced sum
of the prime divisors of `Y` of log discrepancy zero for `(X, Δ)`, `E` the divisor with
`K_Y + Γ = μ^*(K_X + Δ) + E`, and `F = μ^*D`. Then `Γ` is the strict transform of `Δ`, and for
every divisor `T` with `0 ≤ T ≤ Γ`, `R^i μ_* 𝒪_Y(E - ⌊F⌋ - T) = 0` for all `i > 0`. -/
@[mmp "lem_fourfold_adjoint_local_vanishing"]
public theorem isZero_rightDerived_pushforward_adjointIdealSheaf
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (Δ : Divisor X) (hΔ : IsReducedSNC sX Δ)
    (D : QDivisor X) (hD0 : ∀ P, 0 ≤ D.coeff P) (hDΔ : ContainsNoStratum Δ D.supp)
    {Y : Scheme.{0}} (μ : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsDominant μ] (hlog : IsLogResolution sX (Divisor.toQDivisor Δ + D) μ)
    (hY : IsNormalVariety k (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (hiso : ∀ S : Set X, IsSNCStratum Δ S → (S ∩ (biregularLocus μ : Set X)).Nonempty)
    (Γ E : Divisor Y) (hΓ : IsZeroLogDiscrepancyDivisor sX μ hY hμ Δ Γ)
    (hE : IsAdjointDiscrepancyDivisor sX μ hY hμ Δ Γ E)
    (hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp)
    (F : QDivisor Y) (hF : D.IsPullback μ hD F) :
    Γ = MMP.Flips.birationalInverseTransform μ hμ Δ ∧
      ∀ T : Divisor Y, 0 ≤ T → T ≤ Γ → ∀ i : ℕ, 0 < i →
        Limits.IsZero (((Scheme.Modules.pushforward μ).rightDerived i).obj
          (E - MMP.Intersection.WeilRDivisor.roundDown (QDivisor.toRDivisor F) -
            T).divisorialSheaf) :=
  MMP.FourfoldProofs.FourfoldAdjointLocalVanishingProof.eq_inverseTransform_and_isZero_rightDerived
    sX hX hsm Δ hΔ D hD0 hDΔ μ hlog hY hμ hiso Γ E hΓ hE hD F hF

end MMP.Fourfold

end

end
