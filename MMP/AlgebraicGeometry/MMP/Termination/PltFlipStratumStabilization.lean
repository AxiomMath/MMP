module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.RealPltAdjunction
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.MMP.Fourfold.StepBranchesUnitDrop
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.DltFloorComponentsNormal
import MMP.AlgebraicGeometry.Singularities.PltDifferentCoefficients
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.EffectiveResidueAdjunction
import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Singularities.DltDiscrepancy
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Divisor.GeneralMemberAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChain.FlipWeightsOutsideBadSet

/-!
# Stabilization of a retained stratum in a sequence of real plt fourfold flips

Let `(X_i, B_i)` be an infinite sequence of real plt flips of globally projective
`ℚ`-factorial complex fourfolds, `X_i ⟶ Z_i ⟵ X_{i+1}`, where each `B_{i+1}` is the strict
transform of `B_i`. Let `S_i ⊆ X_i` be a prime divisor of coefficient one in `B_i` retained by
every flip (`S_{i+1}` is the strict transform of `S_i`), and `(S_i, Δ_i)` its real adjunction
pair, `K_{S_i} + Δ_i = (K_{X_i} + B_i)|_{S_i}`. After finitely many steps the birational maps
`S_i ⤏ S_{i+1}` induced by the flips extract no prime divisor, and `Δ_i` and `Δ_{i+1}` have the
same coefficient at every prime divisor `P` of `S_i` and its transform on `S_{i+1}`.

## Main results

* `MMP.Fourfold.eventually_realPltFlip_stratum_divisors_stabilize`.

## Implementation notes

* A real plt pair `(X, B)` is a normal variety with an `ℝ`-divisor `B` whose coefficients lie in
  `[0, 1]`, `K_X + B` `ℝ`-Cartier, and `a(E; X, B) > 0` for every exceptional divisor `E`
  over `X`; this is `discrep(X, B) > -1`.
* The canonical divisors in the adjunction formula are fixed by forms, as in residue adjunction:
  `K_{X_i} = div(τ)` for a rational top form `τ` with `ord_{S_i} τ = -1`, and `K_{S_i} = div(ρ)`
  for its Poincaré residue `ρ = Res_{S_i} τ` (`MMP.Fourfold.IsPoincareResidue`). The restriction
  of the `ℝ`-Cartier divisor `K_{X_i} + B_i` to `S_i` is its pull-back along the closed immersion
  `S_i ⟶ X_i` (`MMP.Flips.IsRCartierPullback`), and `Δ_i` is pinned by
  `div(ρ) + Δ_i = (div(τ) + B_i)|_{S_i}` for every such `τ` and `ρ`, which determines it.
* The induced map `φ_i : S_i ⤏ S_{i+1}` is characterized as the birational map with
  `f_i⁺ ∘ φ_i = f_i` on `S_i`; it is unique, since `S_{i+1} ⟶ Z_i` is birational onto its
  image. A prime divisor `Q` of `S_{i+1}` is extracted if it is not the transform `φ_i(P)` of any
  prime divisor `P` of `S_i`, and a shared prime is a pair `(P, φ_i(P))`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.RealPltStratumDivisorsStabilize

open MMP.Mori MMP.Fourfold
open scoped WithZero

section Combinatorics

/-- If `m` holds at `i₀` and fails at `i₁ ≥ i₀`, there is a step `j ∈ [i₀, i₁)` at which `m`
holds and fails just after. -/
private theorem exists_drop {m : ℕ → Prop} {i₀ i₁ : ℕ} (h₀ : m i₀) (h₁ : ¬ m i₁)
    (hle : i₀ ≤ i₁) : ∃ j, i₀ ≤ j ∧ j < i₁ ∧ m j ∧ ¬ m (j + 1) := by
  induction i₁, hle using Nat.le_induction with
  | base => exact absurd h₀ h₁
  | succ n hn ih =>
    by_cases hm : m n
    · exact ⟨n, hn, Nat.lt_succ_self n, hm, h₁⟩
    · obtain ⟨j, hj, hjn, hmj, hmj'⟩ := ih hm
      exact ⟨j, hj, hjn.trans (Nat.lt_succ_self n), hmj, hmj'⟩

/-- **Stabilization along one valuation.** Let `m i` say that a valuation is a divisor at time
`i` and `a i` be its log discrepancy at time `i`, nondecreasing in `i`, strictly increasing at a
step where the divisor is contracted, and with `1 - a i` in a well-founded set whenever the
valuation is a divisor. Then eventually the valuation is never extracted and its log
discrepancy is constant across every step at whose end it is a divisor. -/
private theorem eventually_of_isWF_single {m : ℕ → Prop} {a : ℕ → ℝ} {W : Set ℝ} (hW : W.IsWF)
    (hmono : Monotone a) (hcoeff : ∀ i, m i → 1 - a i ∈ W)
    (hstrict : ∀ i, m i → ¬ m (i + 1) → a i < a (i + 1)) :
    ∃ N, ∀ i, N ≤ i → m (i + 1) → m i ∧ a i = a (i + 1) := by
  classical
  set E : Set ℕ := {i | m (i + 1) ∧ ¬ (m i ∧ a i = a (i + 1))} with hE
  -- at two bad times the log discrepancy at the end strictly increases
  have hinc : ∀ i ∈ E, ∀ i' ∈ E, i < i' → a (i + 1) < a (i' + 1) := by
    intro i hi i' hi' hii'
    by_cases hm : m i'
    · have hne : a i' ≠ a (i' + 1) := fun h => hi'.2 ⟨hm, h⟩
      have hlt : a i' < a (i' + 1) := lt_of_le_of_ne (hmono (Nat.le_succ i')) hne
      exact (hmono (Nat.succ_le_of_lt hii')).trans_lt hlt
    · have hle : i + 1 ≤ i' := Nat.succ_le_of_lt hii'
      obtain ⟨j, hj, hji, hmj, hmj'⟩ := exists_drop hi.1 hm hle
      exact ((hmono hj).trans_lt (hstrict j hmj hmj')).trans_le
        (hmono (Nat.succ_le_succ hji.le))
  have hfin : E.Finite := by
    by_contra hinf
    have hinf : E.Infinite := hinf
    have hmono' : StrictMono (Nat.nth (· ∈ E)) := Nat.nth_strictMono hinf
    have hmem : ∀ n, Nat.nth (· ∈ E) n ∈ E := Nat.nth_mem_of_infinite hinf
    refine (Set.isWF_iff_no_descending_seq.mp hW)
      (fun n => 1 - a (Nat.nth (· ∈ E) n + 1)) ?_ ?_
    · intro n n' hnn'
      have := hinc _ (hmem n) _ (hmem n') (hmono' hnn')
      simp only
      linarith
    · intro n
      exact hcoeff _ (hmem n).1
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun i hi hm => ?_⟩
  by_contra hbad
  have : i ∈ E := ⟨hm, hbad⟩
  have := hN this
  omega

/-- **Abstract stabilization of divisors and log discrepancies.** Let `mem i v` say that the
valuation `v` is a divisor of the `i`-th model and `A i v` be its log discrepancy there. Assume
log discrepancies are nondecreasing in `i`, strictly increasing at a step contracting `v`, at
most one with `1 - A i v` in a well-founded set `W` on divisors, and that only finitely many
valuations have `A 0 v < 1`, or are exceptional on the initial model with `A 0 v ≤ 1`. Then after
finitely many steps no valuation is extracted and log discrepancies of shared divisors agree. -/
theorem eventually_mem_and_eq_of_isWF {V : Type*} (mem : ℕ → V → Prop) (A : ℕ → V → ℝ)
    {W : Set ℝ} (hW : W.IsWF) (hmono : ∀ i v, A i v ≤ A (i + 1) v)
    (hle : ∀ i v, mem i v → A i v ≤ 1) (hcoeff : ∀ i v, mem i v → 1 - A i v ∈ W)
    (hstrict : ∀ i v, mem i v → ¬ mem (i + 1) v → A i v < A (i + 1) v)
    (hfin : {v | A 0 v < 1 ∨ (¬ mem 0 v ∧ A 0 v ≤ 1)}.Finite) :
    ∃ N, ∀ i, N ≤ i → ∀ v, mem (i + 1) v → mem i v ∧ A i v = A (i + 1) v := by
  classical
  have hmono' : ∀ v, Monotone fun i => A i v := fun v => monotone_nat_of_le_succ fun i =>
    hmono i v
  choose N hN using fun v : V =>
    eventually_of_isWF_single hW (hmono' v) (fun i => hcoeff i v) (fun i => hstrict i v)
  refine ⟨hfin.toFinset.sup N, fun i hi v hv => ?_⟩
  by_cases hvF : v ∈ {v | A 0 v < 1 ∨ (¬ mem 0 v ∧ A 0 v ≤ 1)}
  · exact hN v i ((Finset.le_sup (hfin.mem_toFinset.mpr hvF)).trans hi) hv
  · -- outside the finite set the log discrepancy is constantly one and `v` is never contracted
    simp only [Set.mem_setOf_eq, not_or, not_and, not_le, not_lt] at hvF
    obtain ⟨h1, h2⟩ := hvF
    have hA : ∀ j, j ≤ i + 1 → A j v = 1 := fun j hj =>
      le_antisymm (((hmono' v) hj).trans (hle _ _ hv)) (h1.trans ((hmono' v) (Nat.zero_le j)))
    have hm0 : mem 0 v := by
      by_contra h0
      have := h2 h0
      linarith [hA 0 (Nat.zero_le _)]
    have hmi : mem i v := by
      by_contra hmi
      obtain ⟨j, -, hji, hmj, hmj'⟩ := exists_drop (m := fun j => mem j v) hm0 hmi (Nat.zero_le i)
      have := hstrict j v hmj hmj'
      rw [hA j (by omega), hA (j + 1) (by omega)] at this
      exact lt_irrefl _ this
    exact ⟨hmi, by rw [hA i (by omega), hA (i + 1) le_rfl]⟩

end Combinatorics

section Algebra

/-- Two surjections of a local ring onto fields differ by a field isomorphism. -/
private theorem exists_ringEquiv_comp_eq {R K L : Type*} [CommRing R] [IsLocalRing R] [Field K]
    [Field L] (α : R →+* K) (β : R →+* L) (hα : Function.Surjective α)
    (hβ : Function.Surjective β) : ∃ ε : K ≃+* L, ∀ g, ε (α g) = β g := by
  have hker : RingHom.ker α = RingHom.ker β := by
    rw [IsLocalRing.ker_eq_maximalIdeal α hα, IsLocalRing.ker_eq_maximalIdeal β hβ]
  refine ⟨(RingHom.quotientKerEquivOfSurjective hα).symm.trans
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hβ)), fun g => ?_⟩
  have h1 : (RingHom.quotientKerEquivOfSurjective hα).symm (α g) = Ideal.Quotient.mk _ g := by
    rw [RingEquiv.symm_apply_eq]; rfl
  simp only [RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk]
  rfl

/-- In `WithBot ℕ∞`, if `d + b = n` and `d + c = n + 1` then `c = b + 1`. -/
private theorem withBot_add_cancel {d : WithBot ℕ∞} {b c : ℕ∞} (n : ℕ) (h1 : d + b = n)
    (h2 : d + c = n + 1) : c = b + 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe e =>
    have h1' : e + b = n := by exact_mod_cast h1
    have h2' : e + c = (n + 1 : ℕ) := by exact_mod_cast h2
    induction e using ENat.recTopCoe with
    | top => simp at h1'
    | coe m =>
      induction b using ENat.recTopCoe with
      | top => simp at h1'
      | coe b =>
        induction c using ENat.recTopCoe with
        | top => exact absurd h2'.symm (ENat.coe_ne_top _)
        | coe c => norm_cast at h1' h2' ⊢; omega

private theorem withBot_add_one_cancel {d : WithBot ℕ∞} (n : ℕ) (h : d + 1 = n + 1) : d = n :=
  (ENat.WithBot.add_natCast_cancel (c := 1)).mp (by simpa using h)

private theorem comap_comap_symm {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (w : Valuation L ℤᵐ⁰) : (w.comap e.toRingHom).comap e.symm.toRingHom = w := by
  ext x; simp [Valuation.comap_apply]

private theorem comap_injective {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    {w w' : Valuation L ℤᵐ⁰} (h : w.comap e.toRingHom = w'.comap e.toRingHom) : w = w' := by
  rw [← comap_comap_symm e w, h, comap_comap_symm]

end Algebra

section Geometry

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal {k : Type} [Field k] {Y : Scheme.{0}} (s : Y ⟶ Spec (.of k))
    [IsSeparated s] : IsSeparated (Y ↘ Limits.terminal Scheme) := by
  rw [show (Y ↘ Limits.terminal Scheme) = s ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- The log discrepancy `a(w; T, Δ)` of a valuation `w` of `k(T)`: its value at any divisor over
`T` realizing `w`, and `2` when `w` is realized by no divisor over `T` with a log discrepancy
(so that such valuations never count as low). -/
private noncomputable def logDiscrepancyFn {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (sT : T ⟶ Spec (.of ℂ)) (Δ : RDivisor T)
    (w : Valuation T.functionField ℤᵐ⁰) : ℝ :=
  open Classical in
  if h : ∃ (n : ℕ) (D : DivisorOver ℂ sT) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sT n Δ D a ∧ D.valuation = w then
    h.choose_spec.choose_spec.choose
  else 2

/-- The divisorial valuation `ord_P` of a prime divisor `P` of `T`. -/
private noncomputable abbrev dv {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (P : MMP.Mori.PrimeDivisor T) : Valuation T.functionField ℤᵐ⁰ :=
  MMP.Mori.PrimeDivisor.divisorialValuation P

/-- A canonical divisor of a normal variety is the divisor of a nonzero rational top form. -/
private theorem exists_divisorOfForm_eq' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K := by
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  exact ⟨ω, hω0, DivisorWithCoeffs.ext' hωK⟩

/-- If `K + Δ` is `ℝ`-Cartier and `K` is the divisor of a form `ω`, then `div ω + Δ` is a real
combination of Cartier divisors. -/
private theorem isCartierCombination_of_divisorOfForm_eq {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {n : ℕ} {ω : RationalPluriForms sX n 1} {K : Divisor X}
    {Δ : RDivisor X} (hω : divisorOfForm ω = K)
    (hc : RDivisor.IsRCartier (Divisor.toRDivisor K + Δ)) :
    MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + Δ) := by
  subst hω
  obtain ⟨m, r, C, hC, hsum⟩ := hc
  refine ⟨m, r, C, hC, ?_⟩
  have : Divisor.toRDivisor (divisorOfForm ω) + Δ = ∑ j, r j • Divisor.toRDivisor (C j) :=
    DivisorWithCoeffs.ext' fun Γ => by rw [MMP.Flips.coeff_sum_smul_toRDivisor, ← hsum Γ]
  simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using this

/-- On a normal variety on which `K + Δ` is `ℝ`-Cartier for a canonical divisor `K` of index `m`,
every divisor over it with a proper model has a log discrepancy at index `m`. -/
private theorem exists_isLogDiscrepancy_of_isRCartier {T : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] {sT : T ⟶ Spec (.of ℂ)}
    (hT : IsNormalVariety ℂ sT) {m : ℕ} {K : Divisor T} (hK : K.IsCanonicalDivisor sT m)
    {Δ : RDivisor T} (hc : RDivisor.IsRCartier (Divisor.toRDivisor K + Δ))
    (D : DivisorOver ℂ sT) (hD : IsProper D.f) :
    ∃ a, MMP.Intersection.IsLogDiscrepancy sT m Δ D a := by
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hω⟩ := exists_divisorOfForm_eq' hT hK
  exact MMP.Fourfold.exists_isLogDiscrepancy hT hω0 (by rw [hω]; exact hK)
    (isCartierCombination_of_divisorOfForm_eq hω hc) D hD

/-- The value of `logDiscrepancyFn` at the valuation of a divisor with a log discrepancy. -/
private theorem logDiscrepancyFn_eq {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] {sT : T ⟶ Spec (.of ℂ)} {Δ : RDivisor T} {n : ℕ} {D : DivisorOver ℂ sT} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sT n Δ D a) :
    logDiscrepancyFn sT Δ D.valuation = a := by
  have hex : ∃ (n : ℕ) (D' : DivisorOver ℂ sT) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sT n Δ D' a ∧ D'.valuation = D.valuation :=
    ⟨n, D, a, h, rfl⟩
  rw [logDiscrepancyFn, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec.choose_spec.choose_spec
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h1 h h2

/-- `logDiscrepancyFn` is either a log discrepancy of a divisor realizing the valuation, or `2`. -/
private theorem logDiscrepancyFn_cases {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (sT : T ⟶ Spec (.of ℂ)) (Δ : RDivisor T) (w : Valuation T.functionField ℤᵐ⁰) :
    (∃ (n : ℕ) (D : DivisorOver ℂ sT) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sT n Δ D a ∧
      D.valuation = w ∧ logDiscrepancyFn sT Δ w = a) ∨ logDiscrepancyFn sT Δ w = 2 := by
  by_cases hex : ∃ (n : ℕ) (D : DivisorOver ℂ sT) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sT n Δ D a ∧ D.valuation = w
  · obtain ⟨n, D, a, h, rfl⟩ := hex
    exact Or.inl ⟨n, D, a, h, rfl, logDiscrepancyFn_eq h⟩
  · right; rw [logDiscrepancyFn, dif_neg hex]

/-- A divisor over `X` with respect to one structure morphism is a divisor over `X` with respect
to any equal one. -/
private def castDivisorOver {k : Type} [Field k] {X : Scheme.{0}} {s s' : X ⟶ Spec (.of k)}
    (h : s = s') (D : DivisorOver k s) : DivisorOver k s' where
  Y := D.Y
  f := D.f
  isNormalVariety := h ▸ D.isNormalVariety
  isBirationalMorphism := D.isBirationalMorphism
  E := D.E

private theorem valuation_castDivisorOver {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') (D : DivisorOver k s) :
    (castDivisorOver h D).valuation = D.valuation := rfl

/-- The kernel of a quasi-compact morphism from a reduced scheme is the vanishing ideal of its
support. -/
private theorem ker_eq_vanishingIdeal_support_ker {Y W : Scheme.{0}} [IsReduced Y] (g : Y ⟶ W)
    [QuasiCompact g] : g.ker = Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
  have hrad : g.ker.radical = g.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- For quasi-compact morphisms from reduced schemes, a smaller image means a larger kernel; in
particular a morphism from a reduced scheme with image in that of a closed immersion `ι` from a
reduced scheme factors through `ι` (`AlgebraicGeometry.IsClosedImmersion.lift`). -/
private theorem ker_le_ker_of_range_subset {Y Y' W : Scheme.{0}} [IsReduced Y] [IsReduced Y']
    (ι : Y' ⟶ W) [QuasiCompact ι] (g : Y ⟶ W) [QuasiCompact g]
    (h : Set.range g.base ⊆ Set.range ι.base) : ι.ker ≤ g.ker := by
  rw [ker_eq_vanishingIdeal_support_ker ι, ker_eq_vanishingIdeal_support_ker g]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  change (g.ker.support : Set W) ⊆ ι.ker.support
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
  exact closure_mono h

/-- Two points with the same image in the biregular locus of a morphism coincide. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {X Y : Scheme.{0}} (g : X ⟶ Y) {x y : X}
    (hxy : g.base x = g.base y) (hx : g.base x ∈ MMP.Mori.biregularLocus g) : x = y := by
  set V := MMP.Mori.biregularLocus g
  have : IsIso (g ∣_ V) := MMP.Mori.isBiregular_biregularLocus g
  have hy : g.base y ∈ V := hxy ▸ hx
  let x' : (g ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let y' : (g ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have e : ∀ z : (g ⁻¹ᵁ V).toScheme, V.ι ((g ∣_ V) z) = g ((g ⁻¹ᵁ V).ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have key : (g ∣_ V) x' = (g ∣_ V) y' := by
    apply V.ι.isOpenEmbedding.injective
    rwa [e, e]
  exact congrArg Subtype.val ((g ∣_ V).isOpenEmbedding.injective key)

/-- **Strict transforms of prime divisors.** A proper birational morphism onto a normal integral
scheme is biregular at the generic point of every prime divisor `S`, so `S` has a strict transform
whose generic point maps to that of `S`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] (r : W ⟶ X) [IsProper r]
    (hr : MMP.Mori.IsBirationalMorphism r) (S : MMP.Mori.PrimeDivisor X) :
    ∃ PW : MMP.Mori.PrimeDivisor W, r.base PW.genericPoint = S.genericPoint := by
  obtain ⟨D', -, h⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some S
    (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal r hr
      S.coheight_genericPoint.le)
  exact ⟨D', h⟩

/-- The reduced strict transform of `S` maps into any integral closed subscheme `T` with
support `S`: the composite `P_W ⟶ W ⟶ X` lifts through `ι : T ⟶ X`. -/
private theorem exists_lift_subschemeι {X W T : Scheme.{0}} [IsIntegral T] (r : W ⟶ X)
    [QuasiCompact r] (ι : T ⟶ X) [IsClosedImmersion ι] (S : MMP.Mori.PrimeDivisor X)
    (hι : Set.range ι.base = (S.support : Set X)) (PW : MMP.Mori.PrimeDivisor W)
    (hPW : r.base PW.genericPoint = S.genericPoint) :
    haveI := PW.integral
    ∃ pT : PW.idealSheaf.subscheme ⟶ T, pT ≫ ι = PW.idealSheaf.subschemeι ≫ r := by
  haveI := PW.integral
  have hPW' : r.base (AlgebraicGeometry.PrimeDivisor.genericPoint PW) =
      AlgebraicGeometry.PrimeDivisor.genericPoint S := hPW
  have hrange : Set.range (PW.idealSheaf.subschemeι ≫ r).base ⊆ Set.range ι.base := by
    rw [hι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      PW.idealSheaf.range_subschemeι, AlgebraicGeometry.PrimeDivisor.support_eq_closure S]
    change r.base '' (PW.support : Set W) ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure PW]
    refine (image_closure_subset_closure_image r.base.hom.continuous).trans ?_
    rw [Set.image_singleton, hPW']
  exact ⟨IsClosedImmersion.lift ι (PW.idealSheaf.subschemeι ≫ r)
    (ker_le_ker_of_range_subset ι _ hrange), IsClosedImmersion.lift_fac _ _ _⟩

/-- **The strict transform maps birationally onto the stratum.** If `pT ≫ ι = jW ≫ r` for closed
immersions `ι`, `jW` of integral schemes and a proper `r` which is an isomorphism on stalks at
the image of the generic point of the source of `jW`, sent to that of `ι`, then `pT` is proper and
birational. -/
private theorem isProper_isBirationalMorphism_of_comp_eq {X W T TW : Scheme.{0}} [IsIntegral T]
    [IsIntegral TW] (r : W ⟶ X) [IsProper r] (ι : T ⟶ X) [IsClosedImmersion ι] (jW : TW ⟶ W)
    [IsClosedImmersion jW] (pT : TW ⟶ T) (h : pT ≫ ι = jW ≫ r)
    (hgen : r.base (jW.base (genericPoint TW)) = ι.base (genericPoint T))
    (hiso : IsIso (r.stalkMap (jW.base (genericPoint TW)))) :
    IsProper pT ∧ MMP.Mori.IsBirationalMorphism pT := by
  haveI : IsProper (pT ≫ ι) := by rw [h]; infer_instance
  haveI : IsProper pT := IsProper.of_comp pT ι
  have hpg : pT.base (genericPoint TW) = genericPoint T := by
    apply ι.isClosedEmbedding.injective
    change (pT ≫ ι).base _ = _
    rwa [h]
  haveI : IsDominant pT := by
    refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨_, hpg⟩) ?_⟩
    exact dense_iff_closure_eq.2 (by simpa using (genericPoint_spec T).def)
  haveI : Surjective pT := by
    have hr : Set.range pT.base = Set.univ :=
      pT.isClosedMap.isClosed_range.closure_eq.symm.trans pT.denseRange.closure_eq
    exact ⟨fun t => Set.eq_univ_iff_forall.mp hr t⟩
  refine ⟨inferInstance, MMP.Mori.isBirationalMorphism_of_bijective_functionFieldMap pT
    ⟨(functionFieldMap pT).injective, ?_⟩⟩
  have comp_surj : ∀ {A B C : CommRingCat} (u : A ⟶ B) (v : B ⟶ C), Function.Surjective u →
      Function.Surjective v → Function.Surjective (u ≫ v) := fun u v hu hv c => by
    obtain ⟨b, rfl⟩ := hv c; obtain ⟨a, rfl⟩ := hu b; exact ⟨a, rfl⟩
  have hs1 : Function.Surjective ((jW ≫ r).stalkMap (genericPoint TW)) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact comp_surj _ _ (ConcreteCategory.bijective_of_isIso (r.stalkMap _)).2
      (SurjectiveOnStalks.stalkMap_surjective jW _)
  have hs2 : Function.Surjective ((pT ≫ ι).stalkMap (genericPoint TW)) := by
    rw [Scheme.Hom.stalkMap_congr_hom (pT ≫ ι) (jW ≫ r) h]
    exact comp_surj _ _ (ConcreteCategory.bijective_of_isIso _).2 hs1
  have e := Scheme.Hom.stalkMap_comp pT ι (genericPoint TW)
  have hs3 : Function.Surjective (pT.stalkMap (genericPoint TW)) := by
    intro c
    obtain ⟨a, ha⟩ := hs2 c
    refine ⟨(ι.stalkMap _).hom a, ?_⟩
    rw [← ha, e]; rfl
  exact comp_surj _ _ (ConcreteCategory.bijective_of_isIso _).2 hs3

/-- An integral closed subscheme of a variety has a normal model: its normalization, a proper
birational morphism from a normal variety. -/
private theorem exists_normal_model {k : Type} [Field k] {TW Y : Scheme.{0}} [IsIntegral TW]
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] (j : TW ⟶ Y)
    [IsClosedImmersion j] :
    ∃ (N : Scheme.{0}) (ν : N ⟶ TW), IsProper ν ∧ MMP.Mori.IsBirationalMorphism ν ∧
      MMP.Mori.IsNormalVariety k (ν ≫ j ≫ sY) := by
  haveI : AlgebraicGeometry.IsVariety k (j ≫ sY) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨hvar, hnorm, hfin, -, hbir⟩, -⟩ := MMP.Threefold.normalization_spec (j ≫ sY)
  exact ⟨_, _, inferInstance, hbir, ⟨hvar, hnorm⟩⟩

/-- **Transfer of divisors across a common birational model.** Let `pT : T_W ⟶ T` and
`qT : T_W ⟶ T'` be proper birational morphisms of integral schemes over `k`, `T'` a normal
variety, and `ν : N ⟶ T_W` a proper birational morphism from a normal variety. Every divisor `D`
over `T` comes from a divisor `G` over `T_W`, and `G` induces a divisor `D'` over `T'` with proper
model: `ord_D = ord_G ∘ pT^*` and `ord_{D'} = ord_G ∘ qT^*`. -/
private theorem exists_divisorOver_transfer {k : Type} [Field k] {T T' TW N : Scheme.{0}}
    [IsIntegral T] [IsIntegral T'] [IsIntegral TW] {sT : T ⟶ Spec (.of k)}
    {sT' : T' ⟶ Spec (.of k)} {sW : TW ⟶ Spec (.of k)} (hT' : IsNormalVariety k sT')
    (pT : TW ⟶ T) (qT : TW ⟶ T') [IsProper pT] [IsProper qT] (hpb : IsBirationalMorphism pT)
    (hqb : IsBirationalMorphism qT) (hps : pT ≫ sT = sW) (hqs : qT ≫ sT' = sW) (ν : N ⟶ TW)
    [IsProper ν] (hν : IsBirationalMorphism ν) (hN : IsNormalVariety k (ν ≫ sW))
    (D : DivisorOver k sT) :
    ∃ (G : DivisorOver k sW) (D' : DivisorOver k sT'), IsProper D'.f ∧
      (haveI := hpb.isDominant; D.valuation = G.valuation.comap (functionFieldMap pT)) ∧
      (haveI := hqb.isDominant; D'.valuation = G.valuation.comap (functionFieldMap qT)) := by
  haveI : IsIntegral N := hN.1.toIsIntegral
  haveI : IsNormal T' := hT'.2
  haveI : LocallyOfFiniteType sT' := hT'.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T' := LocallyOfFiniteType.isLocallyNoetherian sT'
  haveI : QuasiCompact sT' := hT'.1.toQuasiCompact
  haveI : CompactSpace T' := QuasiCompact.compactSpace_of_compactSpace sT'
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  haveI := hν.isDominant
  have hs₁ : (ν ≫ pT) ≫ sT = ν ≫ sW := by rw [Category.assoc, hps]
  have hs₂ : (ν ≫ qT) ≫ sT' = ν ≫ sW := by rw [Category.assoc, hqs]
  have hN₁ : IsNormalVariety k ((ν ≫ pT) ≫ sT) := hs₁ ▸ hN
  have hN₂ : IsNormalVariety k ((ν ≫ qT) ≫ sT') := hs₂ ▸ hN
  obtain ⟨E, hE⟩ := MMP.Mori.exists_divisorOver_comap_eq hN₁
    (MMP.Mori.isBirationalMorphism_comp hν hpb) D
  obtain ⟨D', hD'⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hT'
    (MMP.Mori.compDivisorOver (ν ≫ qT) hN₂ (MMP.Mori.isBirationalMorphism_comp hν hqb)
      (castDivisorOver (hs₁.trans hs₂.symm) E))
  refine ⟨MMP.Mori.compDivisorOver ν hN hν (castDivisorOver hs₁ E), D'.toDivisorOver, D'.isProper,
    ?_, ?_⟩
  · rw [MMP.Mori.valuation_compDivisorOver, valuation_castDivisorOver, hE]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  · change D'.valuation = _
    rw [hD', MMP.Mori.valuation_compDivisorOver, MMP.Mori.valuation_compDivisorOver,
      valuation_castDivisorOver, valuation_castDivisorOver]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The generic point of an integral scheme mapping onto the support of a prime divisor `P` goes
to the generic point of `P`. -/
private theorem map_genericPoint_eq_genericPoint {Y W : Scheme.{0}} [IsIntegral W] (j : W ⟶ Y)
    (P : MMP.Mori.PrimeDivisor Y) (hj : Set.range j.base = (P.support : Set Y)) :
    j.base (genericPoint W) = P.genericPoint := by
  have h1 : closure {j.base (genericPoint W)} = closure {P.genericPoint} := by
    rw [← MMP.Flips.closure_range_eq_closure_genericPoint, hj,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure, closure_closure]
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- A closed immersion identifies the closure of a point with the closure of its image. -/
private theorem dim_closure_map_eq {T X : Scheme.{0}} (ι : T ⟶ X) [IsClosedImmersion ι] (t : T) :
    topologicalKrullDim (closure {ι.base t} : Set X) =
      topologicalKrullDim (closure {t} : Set T) := by
  have he := ι.isClosedEmbedding
  have himg : ι.base '' closure {t} = closure {ι.base t} := by
    rw [← he.closure_image_eq, Set.image_singleton]
  let g : (closure {t} : Set T) → (closure {ι.base t} : Set X) :=
    fun x => ⟨ι.base x, himg ▸ Set.mem_image_of_mem _ x.2⟩
  have hg : IsHomeomorph g := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨(he.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _, ?_⟩
    rintro ⟨y, hy⟩
    rw [← himg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (hg.topologicalKrullDim_eq g).symm

/-- Along a closed immersion of a variety of dimension `n` into one of dimension `n + 1`,
coheights go up by one. -/
private theorem coheight_map_of_isClosedImmersion {k : Type} [Field k] {T X : Scheme.{0}}
    [IsIntegral T] [IsIntegral X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (ι : T ⟶ X)
    [IsClosedImmersion ι] {n : ℕ} (hT : topologicalKrullDim T = n)
    (hX : topologicalKrullDim X = n + 1) (t : T) :
    Order.coheight (ι.base t) = Order.coheight t + 1 := by
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (ι.base t)
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sX) t
  rw [dim_closure_map_eq, hX] at h1
  rw [hT] at h2
  exact withBot_add_cancel n h2 h1

/-- An integral closed subscheme with the support of a prime divisor of an `(n + 1)`-dimensional
variety has dimension `n`. -/
private theorem topologicalKrullDim_eq_of_range_eq_support {k : Type} [Field k]
    {T X : Scheme.{0}} [IsIntegral T] [IsIntegral X] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (ι : T ⟶ X) [IsClosedImmersion ι] (S : MMP.Mori.PrimeDivisor X)
    (hι : Set.range ι.base = (S.support : Set X)) {n : ℕ} (hX : topologicalKrullDim X = n + 1) :
    topologicalKrullDim T = n := by
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (ι.base (genericPoint T))
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sX)
    (genericPoint T)
  have hc : Order.coheight (genericPoint T) = 0 :=
    Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z
  rw [hc] at h2
  simp only [WithBot.coe_zero, add_zero] at h2
  rw [dim_closure_map_eq, map_genericPoint_eq_genericPoint ι S hι, S.coheight_genericPoint, h2,
    hX] at h1
  exact withBot_add_one_cancel n (by exact_mod_cast h1)

/-- If the strict transform of `S` across `X ⟶ Z ⟵ X'` is `S'`, the generic points of `S` and
`S'` both map to the generic point of a prime divisor `E` of `Z`. -/
private theorem exists_genericPoint_eq_of_flipTransformPrimeDivisor {X Z X' : Scheme.{0}}
    [IsIntegral X] [IsIntegral X'] [IsSeparated (Z ↘ Limits.terminal Scheme)] {f : X ⟶ Z}
    {fp : X' ⟶ Z} {S : MMP.Mori.PrimeDivisor X} {S' : MMP.Mori.PrimeDivisor X'}
    (hS : flipTransformPrimeDivisor f fp S = some S') :
    ∃ E : MMP.Mori.PrimeDivisor Z, f.base S.genericPoint = E.genericPoint ∧
      fp.base S'.genericPoint = E.genericPoint := by
  unfold flipTransformPrimeDivisor at hS
  obtain ⟨E, hE, hE'⟩ := Option.bind_eq_some_iff.mp hS
  exact ⟨E, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f S E).mp hE,
    ((MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' fp E S').mp hE').2⟩

/-- If the strict transform of `S` across `X ⟶ Z ⟵ X'` is `S'`, integral schemes mapping onto
`S` and `S'` have generic points with the same image in `Z`. -/
private theorem map_genericPoint_eq_of_flipTransformPrimeDivisor {X Z X' T T' : Scheme.{0}}
    [IsIntegral X] [IsIntegral X'] [IsIntegral T] [IsIntegral T']
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {f : X ⟶ Z} {fp : X' ⟶ Z}
    {S : MMP.Mori.PrimeDivisor X} {S' : MMP.Mori.PrimeDivisor X'}
    (hS : flipTransformPrimeDivisor f fp S = some S') (ι : T ⟶ X) (ι' : T' ⟶ X')
    (hι : Set.range ι.base = (S.support : Set X))
    (hι' : Set.range ι'.base = (S'.support : Set X')) :
    (ι ≫ f).base (genericPoint T) = (ι' ≫ fp).base (genericPoint T') := by
  obtain ⟨E, h1, h2⟩ := exists_genericPoint_eq_of_flipTransformPrimeDivisor hS
  change f.base (ι.base _) = fp.base (ι'.base _)
  rw [map_genericPoint_eq_genericPoint ι S hι, map_genericPoint_eq_genericPoint ι' S' hι']
  exact h1.trans h2.symm

/-- The stalk map at `w` of `j ≫ h`, for a closed immersion `j`, is surjective when the stalk map
of `h` at `j(w)` is an isomorphism. -/
private theorem surjective_stalkMap_comp {Y W Z : Scheme.{0}} (h : Y ⟶ Z) (j : W ⟶ Y)
    [IsClosedImmersion j] (w : W) (hh : IsIso (h.stalkMap (j.base w))) :
    Function.Surjective ((j ≫ h).stalkMap w) := by
  rw [Scheme.Hom.stalkMap_comp]
  exact (SurjectiveOnStalks.stalkMap_surjective j w).comp
    (ConcreteCategory.bijective_of_isIso (h.stalkMap (j.base w))).2

/-- Let `ι : T ⟶ X`, `ι' : T' ⟶ X'` be closed immersions of integral schemes and `f : X ⟶ Z`,
`f' : X' ⟶ Z` morphisms which are isomorphisms on stalks at the images of the generic points,
which have the same image `z ∈ Z`. Then `k(T) ≅ k(T')` compatibly with the stalk maps
`𝒪_{Z,z} → k(T)` and `𝒪_{Z,z} → k(T')`. -/
private theorem exists_ringEquiv_stalkMap {X Z X' T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T']
    (f : X ⟶ Z) (fp : X' ⟶ Z) (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι]
    [IsClosedImmersion ι'] (hf : IsIso (f.stalkMap (ι.base (genericPoint T))))
    (hfp : IsIso (fp.stalkMap (ι'.base (genericPoint T'))))
    (hcorr : (ι ≫ f).base (genericPoint T) = (ι' ≫ fp).base (genericPoint T')) :
    ∃ ε : T.functionField ≃+* T'.functionField, ∀ g,
      ε ((ι ≫ f).stalkMap (genericPoint T) g) =
        ((ι' ≫ fp).stalkMap (genericPoint T')) ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom g) := by
  refine exists_ringEquiv_comp_eq ((ι ≫ f).stalkMap (genericPoint T)).hom
    (((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ (ι' ≫ fp).stalkMap (genericPoint T')).hom)
    (surjective_stalkMap_comp f ι _ hf) ?_
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (surjective_stalkMap_comp fp ι' _ hfp).comp
    (ConcreteCategory.bijective_of_isIso (Z.presheaf.stalkCongr (.of_eq hcorr)).hom).2

/-- A representative of a rational map `φ : T ⤏ T'` with `φ ∘ b = a` composes with `b` to `a`
on its domain, when the common target is separated. -/
private theorem hom_comp_eq_of_compHom_eq {T T' Z : Scheme.{0}} [IsReduced T]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] (a : T ⟶ Z) (b : T' ⟶ Z) (g : T.PartialMap T')
    (h : g.toRationalMap.compHom b = a.toRationalMap) : g.hom ≫ b = g.domain.ι ≫ a := by
  rw [← Scheme.RationalMap.compHom_toRationalMap] at h
  exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h)

/-- A representative of a birational map sends the generic point to the generic point. -/
private theorem hom_genericPoint_eq_of_partialIso {T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T']
    [IsSeparated (T' ↘ Limits.terminal Scheme)] (e : T.PartialIso T') (g : T.PartialMap T')
    (hg : g.toRationalMap = e.toRationalMap) (hx : genericPoint T ∈ g.domain) :
    g.hom ⟨genericPoint T, hx⟩ = genericPoint T' := by
  have hxe : genericPoint T ∈ e.source :=
    ((genericPoint_spec T).mem_open_set_iff e.source.2).2 (by simpa using e.dense_source.nonempty)
  rw [MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq (g' := e.toPartialMap) hg hx hxe]
  haveI : Nonempty e.source := ⟨⟨_, hxe⟩⟩
  have h1 : (⟨genericPoint T, hxe⟩ : e.source) = genericPoint e.source := by
    apply e.source.ι.isOpenEmbedding.injective
    rw [genericPoint_eq_of_isOpenImmersion e.source.ι]; rfl
  change (e.iso.hom ≫ e.target.ι) (⟨genericPoint T, hxe⟩ : e.source) = _
  rw [h1]
  exact genericPoint_eq_of_isOpenImmersion (e.iso.hom ≫ e.target.ι)

/-- Stalk maps of two factorizations `gh ≫ b = j ≫ a` agree at a point. -/
private theorem stalkMap_comp_eq_of_comp_eq {T T' Z U : Scheme.{0}} (a : T ⟶ Z) (b : T' ⟶ Z)
    (j : U ⟶ T) (gh : U ⟶ T') (hcomm : gh ≫ b = j ≫ a) (u : U) (t : T) (t' : T')
    (ht : t = j u) (ht' : t' = gh u) (hcorr : a.base t = b.base t') :
    (Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ b.stalkMap t' ≫
        (T'.presheaf.stalkCongr (.of_eq ht')).hom ≫ gh.stalkMap u =
      a.stalkMap t ≫ (T.presheaf.stalkCongr (.of_eq ht)).hom ≫ j.stalkMap u := by
  subst ht ht'
  have h1 := Scheme.Hom.stalkMap_congr_hom (gh ≫ b) (j ≫ a) hcomm u
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h1
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at h1 ⊢
  rw [h1]
  have key : ∀ {z₁ z₂ : Z} (p : z₁ ⤳ z₂) (q : z₂ ⤳ z₁) {W : CommRingCat}
      (h : Z.presheaf.stalk z₂ ⟶ W),
      Z.presheaf.stalkSpecializes p ≫ Z.presheaf.stalkSpecializes q ≫ h = h := by
    intro z₁ z₂ p q W h
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact key _ _ _

/-- If `gh ≫ b = j ≫ a` and `ε : k(T) ≅ k(T')` is compatible with the stalk maps of `a` and `b`
at the generic points, then `gh^* ∘ ε = j^*` on function fields. -/
private theorem functionFieldMap_ringEquiv_apply {T T' Z U : Scheme.{0}} [IsIntegral T]
    [IsIntegral T'] [IsIntegral U] (a : T ⟶ Z) (b : T' ⟶ Z) (j : U ⟶ T) [IsDominant j]
    (gh : U ⟶ T') [IsDominant gh] (hcomm : gh ≫ b = j ≫ a)
    (hcorr : a.base (genericPoint T) = b.base (genericPoint T'))
    (ha : Function.Surjective (a.stalkMap (genericPoint T)))
    (ε : T.functionField ≃+* T'.functionField)
    (hε : ∀ g, ε ((a.stalkMap (genericPoint T)) g) =
      (b.stalkMap (genericPoint T')) ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom g))
    (x : T.functionField) : functionFieldMap gh (ε x) = functionFieldMap j x := by
  obtain ⟨h, rfl⟩ := ha x
  rw [hε]
  have := stalkMap_comp_eq_of_comp_eq a b j gh hcomm (genericPoint U) (genericPoint T)
    (genericPoint T') (map_genericPoint_of_isDominant j).symm
    (map_genericPoint_of_isDominant gh).symm hcorr
  exact congrArg (fun φ => φ.hom h) this

/-- If `gh^* ∘ ε = j^*` on function fields for the inclusion `j : U ⟶ T` of an open, then
`ε⁻¹` maps the local ring of `T'` at `gh(x)` into that of `T` at `x`, and the maximal ideal into
the maximal ideal. -/
private theorem exists_algebraMap_eq_ringEquiv_symm {T T' : Scheme.{0}} [IsIntegral T]
    [IsIntegral T'] (U : T.Opens) [IsIntegral U] (gh : U.toScheme ⟶ T') [IsDominant gh]
    [IsDominant U.ι] (ε : T.functionField ≃+* T'.functionField)
    (hε : ∀ x, functionFieldMap gh (ε x) = functionFieldMap U.ι x)
    (x : U.toScheme) (a : T'.presheaf.stalk (gh x)) :
    ∃ a' : T.presheaf.stalk (U.ι x), ε.symm (algebraMap _ T'.functionField a) = algebraMap _ _ a' ∧
      (a ∈ IsLocalRing.maximalIdeal _ → a' ∈ IsLocalRing.maximalIdeal _) := by
  let c := (gh.stalkMap x).hom a
  let a' : T.presheaf.stalk (U.ι x) := (inv (U.ι.stalkMap x)).hom c
  have hc : (U.ι.stalkMap x).hom a' = c := by
    change (inv (U.ι.stalkMap x) ≫ U.ι.stalkMap x).hom c = c
    rw [IsIso.inv_hom_id]; rfl
  refine ⟨a', ?_, fun ha => ?_⟩
  · apply (functionFieldMap U.ι).injective
    rw [← hε, RingEquiv.apply_symm_apply, MMP.Mori.functionFieldMap_algebraMap_stalk gh x a,
      MMP.Mori.functionFieldMap_algebraMap_stalk U.ι x a', hc]
  · have hcm : c ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit (gh.stalkMap x).hom _ hu)
    refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_
    have := hu.map (U.ι.stalkMap x).hom
    rw [hc] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 hcm this

/-- **Equal valuations and generic points.** In the situation of
`exists_algebraMap_eq_ringEquiv_symm`, with `T'` separated, `gh` sends the generic point of a
prime divisor `P` of `T` (lying in `U`) to that of a prime divisor `Q` of `T'` exactly when
`ord_Q ∘ ε = ord_P`. -/
private theorem map_genericPoint_eq_iff_comap_eq {k : Type} [Field k] {T T' : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsIntegral T'] [IsLocallyNoetherian T']
    [IsNormal T'] (sT' : T' ⟶ Spec (.of k)) [IsSeparated sT']
    (U : T.Opens) [IsIntegral U] (gh : U.toScheme ⟶ T') [IsDominant gh] [IsDominant U.ι]
    (ε : T.functionField ≃+* T'.functionField)
    (hε : ∀ x, functionFieldMap gh (ε x) = functionFieldMap U.ι x)
    (P : MMP.Mori.PrimeDivisor T) (hP : P.genericPoint ∈ U) (Q : MMP.Mori.PrimeDivisor T') :
    gh (⟨P.genericPoint, hP⟩ : U.toScheme) = Q.genericPoint ↔ (dv Q).comap ε.toRingHom = dv P := by
  have := P.isDiscreteValuationRing_localRing
  have := Q.isDiscreteValuationRing_localRing
  let x : U.toScheme := ⟨P.genericPoint, hP⟩
  let w := (dv P).comap ε.symm.toRingHom
  have hw1 : ∀ a : T'.presheaf.stalk (gh x), w (algebraMap _ _ a) ≤ 1 := fun a => by
    obtain ⟨a', h1, -⟩ := exists_algebraMap_eq_ringEquiv_symm U gh ε hε x a
    change dv P (ε.symm _) ≤ 1
    rw [h1]
    exact (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff P _).2 ⟨a', rfl⟩
  have hw2 : ∀ a ∈ IsLocalRing.maximalIdeal (T'.presheaf.stalk (gh x)),
      w (algebraMap _ _ a) < 1 := fun a ha => by
    obtain ⟨a', h1, h2⟩ := exists_algebraMap_eq_ringEquiv_symm U gh ε hε x a
    change dv P (ε.symm _) < 1
    rw [h1]
    exact (MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff P a').2 (h2 ha)
  have hw3 : ∃ g, w g = WithZero.exp (-1) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    refine ⟨ε (algebraMap _ _ ϖ), ?_⟩
    change dv P (ε.symm (ε _)) = _
    rw [RingEquiv.symm_apply_apply,
      MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_of_irreducible P hϖ]
  have hQ1 : ∀ a : Q.localRing, dv Q (algebraMap _ _ a) ≤ 1 := fun a =>
    (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff Q _).2 ⟨a, rfl⟩
  have hQ2 : ∀ a ∈ IsLocalRing.maximalIdeal Q.localRing, dv Q (algebraMap _ _ a) < 1 :=
    fun a ha => (MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff Q a).2 ha
  have hQ3 : ∃ g, dv Q g = WithZero.exp (-1) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Q.localRing
    exact ⟨_, MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_of_irreducible Q hϖ⟩
  have hiff : (dv Q).comap ε.toRingHom = dv P ↔ dv Q = w := by
    constructor
    · intro h; ext g
      show _ = dv P (ε.symm g)
      rw [← h]; simp [Valuation.comap_apply]
    · intro h; rw [h]; ext g; simp [w, Valuation.comap_apply]
  rw [hiff]
  constructor
  · intro h
    have key1 : ∀ y : T', y = Q.genericPoint →
        (∀ a : T'.presheaf.stalk y, w (algebraMap _ _ a) ≤ 1) →
        ∀ a : T'.presheaf.stalk Q.genericPoint, w (algebraMap _ _ a) ≤ 1 := by
      rintro y rfl h; exact h
    have key2 : ∀ y : T', y = Q.genericPoint →
        (∀ a ∈ IsLocalRing.maximalIdeal (T'.presheaf.stalk y), w (algebraMap _ _ a) < 1) →
        ∀ a ∈ IsLocalRing.maximalIdeal (T'.presheaf.stalk Q.genericPoint),
          w (algebraMap _ _ a) < 1 := by
      rintro y rfl h; exact h
    exact MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := Q.localRing)
      hQ1 hQ2 hQ3 (key1 _ h hw1) (key2 _ h hw2) hw3
  · intro h
    exact MMP.Positivity.DivisorOver.eq_of_dominates sT' w hw1 hw2 (h ▸ hQ1) (h ▸ hQ2)

/-- **Transforms of prime divisors and valuations.** Let `φ : T ⤏ T'` be a birational map of normal
integral schemes, `T'` separated, with `b ∘ φ = a` for morphisms `a : T ⟶ Z`, `b : T' ⟶ Z`
into a separated `Z`, `b` proper, sending the generic points to the same point `z`. If the stalk
map `𝒪_{Z,z} → k(T)` is onto and `ε : k(T) ≅ k(T')` is compatible with the stalk maps, then
`φ_* P = Q` exactly when `ord_Q ∘ ε = ord_P`. -/
private theorem transformPrimeDivisor_eq_some_iff_comap {k : Type} [Field k] {T T' Z : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsIntegral T'] [IsLocallyNoetherian T']
    [IsNormal T'] (sT' : T' ⟶ Spec (.of k)) [IsSeparated sT']
    [IsSeparated (Z ↘ Limits.terminal Scheme)] (a : T ⟶ Z) (b : T' ⟶ Z) [IsProper b]
    (hcorr : a.base (genericPoint T) = b.base (genericPoint T'))
    (ha : Function.Surjective (a.stalkMap (genericPoint T)))
    (ε : T.functionField ≃+* T'.functionField)
    (hε : ∀ g, ε ((a.stalkMap (genericPoint T)) g) =
      (b.stalkMap (genericPoint T')) ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom g))
    (φ : T.RationalMap T') (hφb : MMP.Mori.RationalMap.IsBirational φ)
    (hφ : φ.compHom b = a.toRationalMap) (P : MMP.Mori.PrimeDivisor T)
    (Q : MMP.Mori.PrimeDivisor T') :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ↔ (dv Q).comap ε.toRingHom = dv P := by
  have hPdom : P.genericPoint ∈ φ.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one a b φ hφ P.coheight_genericPoint.le
  obtain ⟨g, hgP, hg⟩ := Scheme.RationalMap.mem_domain.mp hPdom
  haveI := isSeparated_terminal sT'
  have hcomm := hom_comp_eq_of_compHom_eq a b g (by rw [hg]; exact hφ)
  obtain ⟨e, he⟩ := hφb
  have hgen : genericPoint T ∈ g.domain :=
    ((genericPoint_spec T).mem_open_set_iff g.domain.2).2 ⟨_, trivial, hgP⟩
  have hgη := hom_genericPoint_eq_of_partialIso e g (hg.trans he.symm) hgen
  haveI : Nonempty g.domain := ⟨⟨_, hgP⟩⟩
  haveI : IsDominant g.domain.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant g.hom := by
    refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨_, hgη⟩) ?_⟩
    exact dense_iff_closure_eq.2 (by simpa using (genericPoint_spec T').def)
  have hε' := functionFieldMap_ringEquiv_apply a b g.domain.ι g.hom hcomm hcorr ha ε hε
  rw [← map_genericPoint_eq_iff_comap_eq sT' g.domain g.hom ε hε' P hgP Q]
  constructor
  · intro h
    exact (MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g hg hgP).symm
  · intro h
    exact MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g hg hgP h.symm

/-- The valuation of the divisor `(T, 𝟙, Q)` over `T` is `ord_Q`. -/
private theorem valuation_ofPrimeDivisor_eq_dv {T : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] {sT : T ⟶ Spec (.of ℂ)} (hT : IsNormalVariety ℂ sT)
    (Q : MMP.Mori.PrimeDivisor T) : (DivisorOver.ofPrimeDivisor ℂ hT Q).valuation = dv Q :=
  Valuation.ext fun φ => by
    change Q.divisorialValuation (functionFieldMap (𝟙 T) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]

/-- A divisor over a normal variety which is not exceptional has the valuation `ord_Q` of a prime
divisor `Q`. -/
private theorem exists_dv_eq_of_not_isExceptional {T : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] {sT : T ⟶ Spec (.of ℂ)} (hT : IsNormalVariety ℂ sT)
    {D : DivisorOver ℂ sT} (hD : ¬ D.IsExceptional) : ∃ Q, D.valuation = dv Q := by
  obtain ⟨Q, hQ⟩ := MMP.Fourfold.exists_valuation_eq_of_not_isExceptional hT hD
  exact ⟨Q, hQ.trans (valuation_ofPrimeDivisor_eq_dv hT Q)⟩

/-- **Adjunction on the strata.** Each different `Δ_i` is effective and `(T_i, Δ_i)` is a klt
pair: `T_i` is a normal variety, `K_{T_i} + Δ_i` is `ℝ`-Cartier for a canonical divisor, and
every log discrepancy is positive. -/
private theorem adjunction_strata
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) :
    (Δ i).IsEffective ∧ IsNormalVariety ℂ (ι i ≫ sX i) ∧
      (∃ (m : ℕ) (K : Divisor (T i)), K.IsCanonicalDivisor (ι i ≫ sX i) m ∧
        RDivisor.IsRCartier (Divisor.toRDivisor K + Δ i)) ∧
      ∀ (m : ℕ) (E : DivisorOver ℂ (ι i ≫ sX i)) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy (ι i ≫ sX i) m (Δ i) E a → 0 < a := by
  have hXv := (hflip i).isNegativeExtremalContraction.isNormalVariety_source
  haveI : LocallyOfFiniteType (sX i) := hXv.1.toLocallyOfFiniteType
  have hsum : Finsupp.single (S i) (1 : ℝ) + (B i - Finsupp.single (S i) 1) = B i := by abel
  have hcoeff : ∀ Q, (B i - Finsupp.single (S i) 1).coeff Q =
      (B i).coeff Q - DivisorWithCoeffs.coeff (Finsupp.single (S i) (1 : ℝ)) Q := fun Q =>
    DivisorWithCoeffs.coeff_sub _ _ _
  obtain ⟨-, _, -, hall⟩ := exists_isNormal_isRCartierPullback_isPoincareResidue (sX i) (hQ i)
    (n := 3) (by rw [hdim i]; norm_num) (S i) (B i - Finsupp.single (S i) 1)
    (fun Q => by
      rw [hcoeff]
      by_cases hQ : Q = S i
      · subst hQ; rw [DivisorWithCoeffs.coeff_single_self, hSB]; norm_num
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hQ), sub_zero]; exact (hplt i).1 Q)
    (by rw [hcoeff, DivisorWithCoeffs.coeff_single_self, hSB, sub_self])
    (by
      obtain ⟨m, hm⟩ := hK i
      refine ⟨m, K i, hm, ?_⟩
      rw [add_assoc, hsum]; exact (hplt i).2.1)
    (by rw [hsum]; exact (hplt i).2.2) (ι i) (hι i)
  obtain ⟨heff, hklt, -⟩ := hall (Δ i) fun τ hτ hτS ρ hρ => by
    rw [add_assoc, hsum]; exact hΔ i τ hτ hτS ρ hρ
  exact ⟨heff, hklt⟩

/-- **Adjunction on one stratum.** The different `Δ_i` is effective and the log discrepancy of a
prime divisor `P` of `T_i` is `1 - coeff_P Δ_i`. -/
private theorem logDiscrepancyFn_dv
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) (P : MMP.Mori.PrimeDivisor (T i)) :
    logDiscrepancyFn (ι i ≫ sX i) (Δ i) (dv P) = 1 - (Δ i).coeff P ∧ 0 ≤ (Δ i).coeff P := by
  obtain ⟨heff, hXT, ⟨m, KT, hKT, hKTc⟩, -⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ
      hdim hflip hplt S hS hSB T ι Δ hι hΔ i
  haveI : LocallyOfFiniteType (ι i ≫ sX i) := hXT.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hω⟩ := exists_divisorOfForm_eq' hXT hKT
  have hd := MMP.Flips.isDiscrepancy_divisorialValuation hXT ω hω0 (by rw [hω]; exact hKT)
    (isCartierCombination_of_divisorOfForm_eq hω hKTc) P
  have h := MMP.Fourfold.isLogDiscrepancy_of_isDiscrepancy hd (DivisorOver.ofPrimeDivisor ℂ hXT P)
    (inferInstanceAs (IsProper (𝟙 (T i)))) (valuation_ofPrimeDivisor_eq_dv hXT P)
  refine ⟨?_, heff P⟩
  have := logDiscrepancyFn_eq h
  rw [valuation_ofPrimeDivisor_eq_dv] at this
  rw [this]; ring

/-- **Affine lines in hyperstandard sets.** Let `I ⊂ (0, 1)` be finite and `x, z < 1`. If, for
every `c ∈ (1/2, 1) ∖ I`, the value `(1 - c) x + c z` lies in the hyperstandard set of
`I ∪ {c}`, then `z` lies in the hyperstandard set of `I`: only finitely many hyperstandard data
occur, so two values of `c` share them, and comparing the two identities shows that `c` enters
with multiplicity zero. -/
private theorem mem_of_forall_insert {I : Finset ℝ} (hI : ∀ b ∈ I, b ∈ Set.Ioo (0 : ℝ) 1)
    {x z : ℝ} (hx : x < 1) (hz : z < 1)
    (h : ∀ c ∈ Set.Ioo (1 / 2 : ℝ) 1, c ∉ I → ∃ m : ℕ, 1 ≤ m ∧ ∃ n : ℝ → ℕ,
      ∑ b ∈ insert c I, (n b : ℝ) * b < 1 ∧
        (1 - c) * x + c * z = 1 - (1 - ∑ b ∈ insert c I, (n b : ℝ) * b) / m) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ n : ℝ → ℕ, ∑ b ∈ I, (n b : ℝ) * b < 1 ∧
      z = 1 - (1 - ∑ b ∈ I, (n b : ℝ) * b) / m := by
  classical
  choose! m hm n hn hfc using h
  set D : Set ℝ := Set.Ioo (1 / 2 : ℝ) 1 \ (I : Set ℝ)
  have hDinf : D.Infinite := (Set.Ioo_infinite (by norm_num)).diff I.finite_toSet
  set u := max x z
  have hu : u < 1 := max_lt hx hz
  set M : ℕ := ⌊1 / (1 - u)⌋₊
  set N : ℕ := ⌈∑ b ∈ I, 1 / b⌉₊
  have hnn : ∀ c ∈ D, ∀ b ∈ insert c I, 0 ≤ (n c b : ℝ) * b := by
    intro c hc b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hc.1.1])
    · exact mul_nonneg (Nat.cast_nonneg _) (hI b hb).1.le
  have hterm : ∀ c ∈ D, ∀ b ∈ insert c I, (n c b : ℝ) * b < 1 := fun c hc b hb =>
    (Finset.single_le_sum (hnn c hc) hb).trans_lt (hn c hc.1 hc.2)
  -- the hyperstandard data of `c`, in a finite set
  let π : ℝ → ℕ × ℕ × (I → ℕ) := fun c => (m c, n c c, fun b => n c b)
  have hmaps : Set.MapsTo π D
      ((Finset.range (M + 1) ×ˢ Finset.range 2 ×ˢ
        Fintype.piFinset fun _ : I => Finset.range (N + 1) : Finset _) : Set _) := by
    intro c hc
    have hσ0 : 0 ≤ ∑ b ∈ insert c I, (n c b : ℝ) * b := Finset.sum_nonneg (hnn c hc)
    have hmpos : (0 : ℝ) < m c := by exact_mod_cast hm c hc.1 hc.2
    have hf : (1 - c) * x + c * z ≤ u := by
      have := hc.1.1; have := hc.1.2
      nlinarith [le_max_left x z, le_max_right x z]
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Fintype.mem_piFinset, π]
    refine ⟨?_, ?_, fun b => ?_⟩
    · rw [Nat.lt_succ_iff]
      apply Nat.le_floor
      rw [le_div_iff₀ (by linarith)]
      have e := hfc c hc.1 hc.2
      have : (1 - ∑ b ∈ insert c I, (n c b : ℝ) * b) / m c ≥ 1 - u := by linarith
      rw [ge_iff_le, le_div_iff₀ hmpos] at this
      nlinarith
    · have := hterm c hc c (Finset.mem_insert_self _ _)
      have h2 : (n c c : ℝ) < 2 := by
        by_contra hcon; rw [not_lt] at hcon; nlinarith [hc.1.1]
      exact_mod_cast h2
    · rw [Nat.lt_succ_iff]
      have hb := hI b b.2
      have h1 := hterm c hc b (Finset.mem_insert_of_mem b.2)
      have h2 : (n c b : ℝ) < 1 / b := by rw [lt_div_iff₀ hb.1]; exact h1
      have h3 : 1 / (b : ℝ) ≤ ∑ b ∈ I, 1 / b :=
        Finset.single_le_sum (f := fun b : ℝ => 1 / b)
          (fun b hb => (one_div_pos.mpr (hI b hb).1).le) b.2
      have : (n c b : ℝ) ≤ N := (h2.trans_le h3).le.trans (Nat.le_ceil _)
      exact_mod_cast this
  -- two values of `c` with the same data
  obtain ⟨c, hc, c', hc', hne, heq⟩ :=
    hDinf.exists_ne_map_eq_of_mapsTo hmaps (Finset.finite_toSet _)
  simp only [π, Prod.mk.injEq] at heq
  obtain ⟨hmm, hkk, hnb⟩ := heq
  have hs : ∑ b ∈ I, (n c b : ℝ) * b = ∑ b ∈ I, (n c' b : ℝ) * b :=
    Finset.sum_congr rfl fun b hb => by rw [congrFun hnb ⟨b, hb⟩]
  have hσ := hn c hc.1 hc.2
  have e1 := hfc c hc.1 hc.2
  have e2 := hfc c' hc'.1 hc'.2
  rw [Finset.sum_insert hc.2] at e1 hσ
  rw [Finset.sum_insert hc'.2, ← hs, ← hmm, ← hkk] at e2
  have hmpos : (0 : ℝ) < m c := by exact_mod_cast hm c hc.1 hc.2
  have hs0 : 0 ≤ ∑ b ∈ I, (n c b : ℝ) * b :=
    Finset.sum_nonneg fun b hb => hnn c hc b (Finset.mem_insert_of_mem hb)
  set s := ∑ b ∈ I, (n c b : ℝ) * b
  set k : ℝ := ((n c c : ℕ) : ℝ) with hkdef
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  set mm : ℝ := ((m c : ℕ) : ℝ)
  have e1' : mm * ((1 - c) * x + c * z) = mm - 1 + k * c + s := by
    rw [e1]; field_simp; ring
  have e2' : mm * ((1 - c') * x + c' * z) = mm - 1 + k * c' + s := by
    rw [e2]; field_simp; ring
  have hzx : mm * (z - x) = k := by
    have : (c - c') * (mm * (z - x)) = (c - c') * k := by linear_combination e1' - e2'
    exact mul_left_cancel₀ (sub_ne_zero.mpr hne) this
  have hxv : mm * x = mm - 1 + s := by linear_combination e1' - c * hzx
  have hzv : mm * z = mm - 1 + s + k := by linear_combination hxv + hzx
  -- `z < 1` forces the multiplicity of `c` to vanish
  have hk : n c c = 0 := by
    by_contra hk
    have : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  have hk' : k = 0 := by simp [k, hk]
  refine ⟨m c, hm c hc.1 hc.2, n c, by nlinarith [hc.1.1], ?_⟩
  rw [hk', add_zero] at hzv
  show z = 1 - (1 - s) / mm
  have : z = (mm - 1 + s) / mm := by rw [eq_div_iff hmpos.ne']; linarith
  rw [this]; field_simp; ring

/-- **Lowering a real boundary keeps the log discrepancies of exceptional divisors positive.** On
a `ℚ`-factorial variety, if `B ≤ Δ` coefficientwise, then `a(E; X, Δ) ≤ a(E; X, B)` for every
divisor `E` over `X`: the difference is the multiplicity along `E` of the pull-back of the
effective `ℝ`-Cartier divisor `Δ - B`. -/
private theorem isLogDiscrepancy_le_of_le {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X]
    [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsQFactorial sX) {Δ B : RDivisor X}
    (hle : ∀ P, B.coeff P ≤ Δ.coeff P) {n n' : ℕ} {E : DivisorOver ℂ sX} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n B E a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sX n' Δ E a') : a' ≤ a := by
  classical
  obtain ⟨hXn, hprop, ω, hω, hKω, m, r, L, L', hL, hsum, hpb, rfl⟩ := ha
  obtain ⟨m₂, s, M, hM, hMsum⟩ := hX.isRCartier (Δ - B)
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose M' hM' using fun j => (hM j).exists_isPullback
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j))
  have hMpb : ∀ j, ∃ h, (M j).IsPullback E.f h (M' j) := fun j =>
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j), hM' j⟩
  have hb : MMP.Intersection.IsLogDiscrepancy sX n Δ E _ := ⟨hXn, hprop, ω, hω, hKω, m + m₂,
    Fin.append r s, Fin.append L M, Fin.append L' M',
    Fin.addCases (fun i => by simpa using hL i) (fun j => by simpa using hM j),
    fun Γ => ?_, Fin.addCases (fun i => by simpa using hpb i)
      (fun j => by simpa using hMpb j), rfl⟩
  · rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha' hb, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have heff := (isEffective_of_isRCartierPullback E.f ⟨m₂, s, M, hM, hMsum⟩
      fun P => sub_nonneg.mpr (hle P)).2
      (∑ j, s j • Divisor.toRDivisor (M' j))
      ⟨m₂, s, M, M', hM, by ext P; rw [hMsum P, MMP.Flips.coeff_sum_smul_toRDivisor], hMpb, rfl⟩
    have hE := heff E.E
    rw [show (∑ j, s j • Divisor.toRDivisor (M' j)) E.E =
      (∑ j, s j • Divisor.toRDivisor (M' j)).coeff E.E from rfl,
      MMP.Flips.coeff_sum_smul_toRDivisor] at hE
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hE
    linarith
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h1 := hsum Γ
    have h2 := hMsum Γ
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 h2 ⊢
    linarith

/-- **Lowering a real plt boundary.** If every exceptional divisor over the `ℚ`-factorial `X`
has positive log discrepancy for `Δ`, the same holds for every `ℝ`-divisor `B ≤ Δ`. -/
private theorem pos_of_isLogDiscrepancy_of_le {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hQ : IsQFactorial sX) {Δ B : RDivisor X} (hle : ∀ P, B.coeff P ≤ Δ.coeff P)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m Δ E a → 0 < a)
    (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ) (hE : E.IsExceptional)
    (ha : MMP.Intersection.IsLogDiscrepancy sX m B E a) : 0 < a := by
  obtain ⟨-, hprop, -, -, ⟨K, hK, -⟩, -⟩ := id ha
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hQ.1 hK
  have hdivω : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨a', ha'⟩ := MMP.Fourfold.exists_isLogDiscrepancy hQ.1 hω0 (hdivω ▸ hK)
    (isCartierCombination_of_divisorOfForm_eq hdivω (hQ.isRCartier _)) E hprop
  have := hplt m E a' hE ha'
  have := isLogDiscrepancy_le_of_le hQ hle ha ha'
  linarith

/-- **Coefficients of the different, with reduced components off `S`.** Let `(X, P + Δ)` be real
plt with every coefficient of `Δ` equal to `0`, to `1`, or in a finite set `I ⊂ (0, 1)`, and let
`Δ_S` be its different on `S = P` with `coeff_{Q'} Δ_S < 1`. Then `coeff_{Q'} Δ_S` lies in the
hyperstandard set of `I`. For `c ∈ [0, 1]` lower the coefficient-one components of `Δ` to `c`;
the result `Δ_c` is real plt, and `(1 - c) Δ_{S,0} + c Δ_S` is its different. Its coefficient at
`Q'` is affine in `c` and, for `c ∈ (1/2, 1) ∖ I`, hyperstandard for `I ∪ {c}`; two values of `c`
with the same hyperstandard data force the coefficient-one components to contribute nothing. -/
private theorem coeff_mem_hyperstandard {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hQ : IsQFactorial sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (P : MMP.Mori.PrimeDivisor X) (Δ : RDivisor X)
    (hΔ : ∀ Q, 0 ≤ Δ.coeff Q ∧ Δ.coeff Q ≤ 1) (hΔP : Δ.coeff P = 0)
    (hK : ∃ (m : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX m)
    (hplt : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) E a → 0 < a)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [IsNormal T] (hj : Set.range j.base = (P.support : Set X))
    (I : Finset ℝ) (hI : ∀ b ∈ I, b ∈ Set.Ioo (0 : ℝ) 1)
    (hcoeff : ∀ Q, Δ.coeff Q = 0 ∨ Δ.coeff Q = 1 ∨ Δ.coeff Q ∈ I)
    (ΔS : RDivisor T)
    (hΔS : ∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
        MMP.Flips.IsRCartierPullback j
          (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
          (Divisor.toRDivisor (divisorOfForm ρ) + ΔS))
    (Q' : MMP.Mori.PrimeDivisor T) (hlt : ΔS.coeff Q' < 1) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : ℝ → ℕ, ∑ b ∈ I, (c b : ℝ) * b < 1 ∧
      ΔS.coeff Q' = 1 - (1 - ∑ b ∈ I, (c b : ℝ) * b) / m := by
  classical
  -- the boundary with its coefficient-one components lowered to `c`
  let g : ℝ → ℝ → ℝ := fun c x => if x = 1 then c else x
  have hg0 : ∀ c, g c 0 = 0 := fun c => if_neg zero_ne_one
  let Δc : ℝ → RDivisor X := fun c => Δ.mapCoeffs (g c) (hg0 c)
  have hΔc : ∀ c Q, (Δc c).coeff Q = g c (Δ.coeff Q) := fun c Q =>
    DivisorWithCoeffs.coeff_mapCoeffs _ _ _ _
  obtain ⟨mK, K, hKc⟩ := hK
  -- the hypotheses of real plt adjunction for `Δ_c`, `0 ≤ c ≤ 1`
  have hbd : ∀ c, 0 ≤ c → c ≤ 1 → ∀ Q, 0 ≤ (Δc c).coeff Q ∧ (Δc c).coeff Q ≤ 1 := by
    intro c hc0 hc1 Q
    rw [hΔc]
    simp only [g]
    split_ifs
    · exact ⟨hc0, hc1⟩
    · exact hΔ Q
  have hcP : ∀ c, (Δc c).coeff P = 0 := fun c => by rw [hΔc, hΔP, hg0]
  have hcart : ∀ c, ∃ (m : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX m ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + Finsupp.single P 1 + Δc c) :=
    fun c => ⟨mK, K, hKc, hQ.isRCartier _⟩
  have hpltc : ∀ c, c ≤ 1 → ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δc c) E a → 0 < a := by
    intro c hc1
    refine pos_of_isLogDiscrepancy_of_le hQ (fun R => ?_) hplt
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hΔc]
    simp only [g]
    split_ifs with h
    · rw [h]; linarith
    · exact le_rfl
  -- `c = 0`
  obtain ⟨-, _, ⟨ΔS₀, hΔS₀⟩, hall₀⟩ :=
    MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue sX hQ hdim P (Δc 0)
      (hbd 0 le_rfl zero_le_one) (hcP 0) (hcart 0) (hpltc 0 zero_le_one) j hj
  obtain ⟨-, -, hco₀, -, -⟩ := hall₀ ΔS₀ hΔS₀
  obtain ⟨m₀, hm₀, c₀, hc₀, hx⟩ := hco₀ I hI (fun Q hQpos => by
    rw [hΔc] at hQpos ⊢
    simp only [g] at hQpos ⊢
    split_ifs at hQpos ⊢ with h
    · exact absurd hQpos (lt_irrefl 0)
    · rcases hcoeff Q with h0 | h1 | hI'
      · rw [h0] at hQpos; exact absurd hQpos (lt_irrefl 0)
      · exact absurd h1 h
      · exact hI') Q'
  set x := ΔS₀.coeff Q'
  have hx1 : x < 1 := by
    rw [hx]
    have : 0 < (1 - ∑ b ∈ I, (c₀ b : ℝ) * b) / m₀ :=
      div_pos (by linarith) (by exact_mod_cast hm₀)
    linarith
  -- `1/2 < c < 1`, `c ∉ I`
  refine mem_of_forall_insert hI hx1 hlt fun c hc hcI => ?_
  have hc0 : 0 ≤ c := by linarith [hc.1]
  have hc1 : c ≤ 1 := hc.2.le
  obtain ⟨-, _, -, hall⟩ :=
    MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue sX hQ hdim P (Δc c)
      (hbd c hc0 hc1) (hcP c) (hcart c) (hpltc c hc1) j hj
  have hΔSc : ∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
        MMP.Flips.IsRCartierPullback j
          (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δc c)
          (Divisor.toRDivisor (divisorOfForm ρ) + ((1 - c) • ΔS₀ + c • ΔS)) := by
    intro τ hτ hτP ρ hρ
    have h := MMP.Fourfold.isRCartierPullback_add
      (MMP.Fourfold.isRCartierPullback_smul (1 - c) (hΔS₀ τ hτ hτP ρ hρ))
      (MMP.Fourfold.isRCartierPullback_smul c (hΔS τ hτ hτP ρ hρ))
    convert h using 1
    · refine DivisorWithCoeffs.ext' fun Γ => ?_
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul, hΔc]
      simp only [g]
      split_ifs with h1
      · rw [h1]; ring
      · ring
    · refine DivisorWithCoeffs.ext' fun Γ => ?_
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      ring
  obtain ⟨-, -, hco, -, -⟩ := hall _ hΔSc
  obtain ⟨m, hm, n', hn', heq⟩ := hco (insert c I)
    (fun b hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨by linarith [hc.1], hc.2⟩
      · exact hI b hb)
    (fun Q hQpos => by
      rw [hΔc] at hQpos ⊢
      simp only [g] at hQpos ⊢
      split_ifs at hQpos ⊢ with h
      · exact Finset.mem_insert_self _ _
      · rcases hcoeff Q with h0 | h1 | hI'
        · rw [h0] at hQpos; exact absurd hQpos (lt_irrefl 0)
        · exact absurd h1 h
        · exact Finset.mem_insert_of_mem hI') Q'
  refine ⟨m, hm, n', hn', ?_⟩
  rw [← heq, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul]

/-- A partial map `φ` on prime divisors whose fibre over `F` has at most one element sends a
divisor `D` to one whose coefficient at `F` is `0` or a coefficient of `D`. -/
private theorem mapPrimeDivisors_apply_eq_zero_or {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (D : DivisorWithCoeffs R X) (F : MMP.Mori.PrimeDivisor Y)
    (h : ∀ E E', φ E = some F → φ E' = some F → E = E') :
    DivisorWithCoeffs.mapPrimeDivisors φ D F = 0 ∨
      ∃ E, DivisorWithCoeffs.mapPrimeDivisors φ D F = D E := by
  by_cases hE : ∃ E, φ E = some F
  · obtain ⟨E, hE⟩ := hE
    exact Or.inr ⟨E, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hE
      (fun E' hE' => h E' E hE' hE) D⟩
  · simp only [not_exists] at hE
    exact Or.inl (MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne hE D)

/-- **Coefficients of a strict transform across a real flip**: every coefficient of
`(f⁺)⁻¹_* f_* D` is `0` or a coefficient of `D`, since prime divisors correspond injectively
through the biregular loci of `f` and `f⁺` at codimension-one points of `Z`. -/
private theorem coeff_flipTransform_eq_zero_or {X Z X' : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {B' : RDivisor X'} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) (D : RDivisor X)
    (Q : MMP.Mori.PrimeDivisor X') :
    (flipTransform f fp D).coeff Q = 0 ∨ ∃ E, (flipTransform f fp D).coeff Q = D.coeff E := by
  have hZ := hstep.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI := isSeparated_terminal sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hstep.isProjectiveMorphism
  have hψ : ∀ E E', MMP.Mori.inverseTransformPrimeDivisor fp E = some Q →
      MMP.Mori.inverseTransformPrimeDivisor fp E' = some Q → E = E' := by
    intro E E' h h'
    have h1 := ((MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' fp E Q).mp h).2
    have h2 := ((MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' fp E' Q).mp h').2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.symm.trans h2)
  have hχ : ∀ (E' : MMP.Mori.PrimeDivisor Z) (E E'' : MMP.Mori.PrimeDivisor X),
      MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap E = some E' →
      MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap E'' = some E' →
      E = E'' := by
    intro E' E E'' h h'
    have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E E').mp h
    have h2 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E'' E').mp h'
    have hb : E'.genericPoint ∈ MMP.Mori.biregularLocus f :=
      MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f
        hstep.isBirationalMorphism E'.coheight_genericPoint.le
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_mem_biregularLocus f (h1.trans h2.symm) (by rw [h1]; exact hb))
  simp only [DivisorWithCoeffs.coeff_apply, flipTransform, AddMonoidHom.coe_comp,
    Function.comp_apply, MMP.Mori.inverseTransformDivisor]
  rcases mapPrimeDivisors_apply_eq_zero_or _ (MMP.Mori.RationalMap.transformDivisor
    (X := X) f.toRationalMap D) Q hψ with h | ⟨E', hE'⟩
  · exact Or.inl h
  · rw [hE']
    rcases mapPrimeDivisors_apply_eq_zero_or _ D E' (hχ E') with h | ⟨E, hE⟩
    · exact Or.inl h
    · exact Or.inr ⟨E, hE⟩

/-- **The coefficients of the differents satisfy the DCC**: they lie in one well-founded set. -/
private theorem exists_isWF_coeff
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i)) :
    ∃ W : Set ℝ, W.IsWF ∧ ∀ i P, (Δ i).coeff P ∈ W := by
  classical
  -- the coefficients of `B_0` in `(0, 1)`
  set I₀ : Finset ℝ := ((B 0).support.image fun P => (B 0).coeff P).filter
    fun b => b ∈ Set.Ioo (0 : ℝ) 1
  have hI₀ : ∀ b ∈ I₀, b ∈ Set.Ioo (0 : ℝ) 1 := fun b hb => (Finset.mem_filter.mp hb).2
  -- every coefficient of every `B_i` is `0`, `1` or in `I₀`
  have hBc : ∀ i Q, (B i).coeff Q = 0 ∨ (B i).coeff Q = 1 ∨ (B i).coeff Q ∈ I₀ := by
    intro i
    induction i with
    | zero =>
      intro Q
      by_cases h0 : (B 0).coeff Q = 0
      · exact Or.inl h0
      by_cases h1 : (B 0).coeff Q = 1
      · exact Or.inr (Or.inl h1)
      refine Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨Q, ?_, rfl⟩,
        lt_of_le_of_ne ((hplt 0).1 Q).1 (Ne.symm h0), lt_of_le_of_ne ((hplt 0).1 Q).2 h1⟩))
      exact Finsupp.mem_support_iff.mpr h0
    | succ i ih =>
      intro Q
      rw [(hflip i).eq_flipTransform]
      rcases coeff_flipTransform_eq_zero_or (hflip i) (B i) Q with h | ⟨E, hE⟩
      · exact Or.inl h
      · rw [hE]; exact ih E
  have hsum : ∀ j, Finsupp.single (S j) (1 : ℝ) + (B j - Finsupp.single (S j) 1) = B j :=
    fun j => by abel
  have hdim' : ∀ j, topologicalKrullDim (X j) = ((3 : ℕ) : WithBot ℕ∞) + 1 := fun j => by
    rw [hdim j]; norm_num
  have hcoeffs : ∀ j Q, (B j - Finsupp.single (S j) 1).coeff Q =
      (B j).coeff Q - DivisorWithCoeffs.coeff (Finsupp.single (S j) (1 : ℝ)) Q := fun j Q =>
    DivisorWithCoeffs.coeff_sub _ _ _
  have hbounds : ∀ j Q, 0 ≤ (B j - Finsupp.single (S j) 1).coeff Q ∧
      (B j - Finsupp.single (S j) 1).coeff Q ≤ 1 := by
    intro j Q
    rw [hcoeffs]
    by_cases hQS : Q = S j
    · subst hQS; rw [DivisorWithCoeffs.coeff_single_self, hSB]; norm_num
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hQS), sub_zero]; exact (hplt j).1 Q
  have hzero : ∀ j, (B j - Finsupp.single (S j) 1).coeff (S j) = 0 := fun j => by
    rw [hcoeffs, DivisorWithCoeffs.coeff_single_self, hSB, sub_self]
  have hXv : ∀ j, IsNormalVariety ℂ (sX j) := fun j =>
    (hflip j).isNegativeExtremalContraction.isNormalVariety_source
  haveI : ∀ j, LocallyOfFiniteType (sX j) := fun j => (hXv j).1.toLocallyOfFiniteType
  -- the hyperstandard set of `I₀` is well founded
  obtain ⟨hWF, -⟩ := MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue (sX 0)
    (hQ 0) (hdim' 0) (S 0) (B 0 - Finsupp.single (S 0) 1) (hbounds 0) (hzero 0)
    (by
      obtain ⟨m, hm⟩ := hK 0
      exact ⟨m, K 0, hm, by rw [add_assoc, hsum]; exact (hplt 0).2.1⟩)
    (by rw [hsum]; exact (hplt 0).2.2) (ι 0) (hι 0)
  refine ⟨_, hWF I₀ hI₀, fun i P => ?_⟩
  -- the coefficient is `< 1`, since `(T_i, Δ_i)` is klt
  obtain ⟨-, -, -, hkltT⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S
    hS hSB T ι Δ hι hΔ i
  have hdv := logDiscrepancyFn_dv X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB T ι Δ
    hι hΔ i
  have hlt : (Δ i).coeff P < 1 := by
    rcases logDiscrepancyFn_cases (ι i ≫ sX i) (Δ i) (dv P) with ⟨n, D, a, ha, -, hv⟩ | h2
    · have := hkltT n D a ha
      linarith [(hdv P).1]
    · linarith [(hdv P).1, (hdv P).2]
  exact coeff_mem_hyperstandard (sX i) (hQ i) (hdim' i) (S i) (B i - Finsupp.single (S i) 1)
    (hbounds i) (hzero i) (hK i |>.imp fun m hm => ⟨K i, hm⟩)
    (by rw [hsum]; exact (hplt i).2.2) (ι i) (hι i) I₀ hI₀
    (fun Q => by
      rw [hcoeffs]
      by_cases hQS : Q = S i
      · subst hQS; rw [DivisorWithCoeffs.coeff_single_self, hSB, sub_self]; exact Or.inl rfl
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hQS), sub_zero]; exact hBc i Q)
    (Δ i) (fun τ hτ hτS ρ hρ => by rw [add_assoc, hsum]; exact hΔ i τ hτ hτS ρ hρ) P hlt

/-- **Low log discrepancies on the initial stratum are finite**: only finitely many valuations
have `a(w; T_0, Δ_0) < 1`, or are not divisors of `T_0` and have `a(w; T_0, Δ_0) ≤ 1`. -/
private theorem finite_logDiscrepancyFn_le_one
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i)) :
    {w : Valuation (T 0).functionField ℤᵐ⁰ | logDiscrepancyFn (ι 0 ≫ sX 0) (Δ 0) w < 1 ∨
      ((∀ P, dv P ≠ w) ∧ logDiscrepancyFn (ι 0 ≫ sX 0) (Δ 0) w ≤ 1)}.Finite := by
  classical
  obtain ⟨heff, hXT, ⟨m, KT, hKT, hKTc⟩, hkltT⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ
      hdim hflip hplt S hS hSB T ι Δ hι hΔ 0
  have hdv := logDiscrepancyFn_dv X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB T ι Δ
      hι hΔ 0
  -- the different has coefficients `< 1`
  have hlt : ∀ P, (Δ 0).coeff P < 1 := by
    intro P
    rcases logDiscrepancyFn_cases (ι 0 ≫ sX 0) (Δ 0) (dv P) with ⟨n, D, a, ha, -, hv⟩ | h2
    · have := hkltT n D a ha
      linarith [(hdv P).1]
    · linarith [(hdv P).1, (hdv P).2]
  have hklt : IsRealKltPair (ι 0 ≫ sX 0) (Δ 0) := by
    refine ⟨hXT, hlt, ⟨m, KT, hKT, ?_⟩, hkltT⟩
    rwa [show Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero KT = Divisor.toRDivisor KT from
      (MMP.Flips.toRDivisor_eq_mapCoeffs KT).symm]
  refine ((IsRealKltPair.finite_setOf_isLogDiscrepancy_le_one hklt).union
    (((Δ 0).support.finite_toSet).image dv)).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  rcases logDiscrepancyFn_cases (ι 0 ≫ sX 0) (Δ 0) w with ⟨n, D, a, ha, rfl, hv⟩ | h2
  · rw [hv] at hw
    by_cases hD : D.IsExceptional
    · exact Or.inl ⟨n, D, a, hD, rfl, ha, by rcases hw with hw | hw <;> [linarith; exact hw.2]⟩
    · obtain ⟨Q, hQ⟩ := exists_dv_eq_of_not_isExceptional hXT hD
      rcases hw with hw | ⟨hw, -⟩
      · refine Or.inr ⟨Q, ?_, hQ.symm⟩
        have h1 := (hdv Q).1
        rw [← hQ, hv] at h1
        have : (Δ 0).coeff Q ≠ 0 := by intro h; rw [h] at h1; linarith
        exact Finsupp.mem_support_iff.mpr this
      · exact absurd hQ.symm (hw Q)
  · rw [h2] at hw
    rcases hw with hw | ⟨-, hw⟩ <;> norm_num at hw

/-- **Ambient comparison on a common model of a real flip.** Let `p : W ⟶ X`, `q : W ⟶ X⁺` be
dominant morphisms from a normal integral scheme with `p ≫ f = q ≫ f⁺`. For every prime divisor
`E` of `W`, the log discrepancy of `ord_E` over `(X, B)` is at most that over `(X⁺, B⁺)`. -/
private theorem isLogDiscrepancy_le_of_comp_eq {X Z X' W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Z] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z}
    {fp : X' ⟶ Z} (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m, K.IsCanonicalDivisor sX m) (p : W ⟶ X) (q : W ⟶ X') [IsDominant p] [IsDominant q]
    (hpq : p ≫ f = q ≫ fp) (E : MMP.Mori.PrimeDivisor W) (m : ℕ) (D : DivisorOver ℂ sX)
    (D' : DivisorOver ℂ sX') (a a' : ℝ) (hD : D.valuation = E.valuationOver p)
    (hD' : D'.valuation = E.valuationOver q)
    (ha : MMP.Intersection.IsLogDiscrepancy sX m B D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sX' m B' D' a') : a ≤ a' := by
  haveI := hstep.isBirationalMorphism.isDominant
  haveI := hstep.isBirationalMorphism_flip.isDominant
  obtain ⟨E0, hE0p, hval, -, hcmp⟩ := hstep.exists_isLogDiscrepancy_le hK D' ha'.2.1
  -- a log discrepancy of `E0`, computed with the form of `ha`
  obtain ⟨hX, -, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m₀, r, C, C', hC, hsum, -, -⟩ := id ha
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hdiv : divisorOfForm ω = K₀ := DivisorWithCoeffs.ext' fun Γ => by
    rw [coeff_divisorOfForm, hK₀ω]
  have hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B) := by
    refine ⟨m₀, r, C, hC, ?_⟩
    have : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (C j) :=
      DivisorWithCoeffs.ext' fun Γ => by
        rw [MMP.Flips.coeff_sum_smul_toRDivisor, ← hsum Γ, DivisorWithCoeffs.coeff_add,
          Divisor.coeff_toRDivisor, coeff_divisorOfForm]
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using this
  obtain ⟨a0, ha0⟩ := MMP.Fourfold.exists_isLogDiscrepancy hX hω0 (by rw [hdiv]; exact hK₀) hKB
    E0 hE0p
  -- `E0` and `D` have the same valuation
  have hfb := hstep.isBirationalMorphism.functionFieldMap_bijective
  have hv : E0.valuation = D.valuation := by
    have h1 : E0.valuation.comap (functionFieldMap f) = D.valuation.comap (functionFieldMap f) := by
      rw [hval, hD, hD']
      ext t
      simp only [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply]
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
      congr 2
      exact MMP.Positivity.DivisorOver.functionFieldMap_congr hpq.symm
    ext t
    obtain ⟨t', rfl⟩ := hfb.2 t
    exact congrArg (fun w => w t') h1
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha0 hv.symm
  rw [this]
  exact (hcmp m m a0 a' ha0 ha').1

/-- **The strict transform of a retained divisor on a common model of a real flip.** If
`(f⁺)⁻¹_* f_* S = S⁺` and `r : W ⟶ X`, `q : W ⟶ X⁺` are proper birational over `Z`, `S` has a
strict transform `P_W` on `W` whose generic point maps to those of `S` and `S⁺`. -/
private theorem exists_primeDivisor_strictTransform {X Z X' W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral W] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X}
    {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) {S : MMP.Mori.PrimeDivisor X}
    {S' : MMP.Mori.PrimeDivisor X'} (hS : flipTransformPrimeDivisor f fp S = some S')
    (r : W ⟶ X) (q : W ⟶ X') [IsProper r] (hrb : IsBirationalMorphism r) (hc : r ≫ f = q ≫ fp) :
    ∃ PW : MMP.Mori.PrimeDivisor W, r.base PW.genericPoint = S.genericPoint ∧
      q.base PW.genericPoint = S'.genericPoint := by
  have hZ := hstep.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI := isSeparated_terminal sZ
  haveI : IsProper fp := isProper_of_isProjectiveMorphism fp hstep.isProjectiveMorphism_flip
  obtain ⟨PW, hPW⟩ := exists_primeDivisor_map_genericPoint_eq r hrb S
  refine ⟨PW, hPW, ?_⟩
  -- `q(η_{P_W}) = η_{S⁺}`: both map to the generic point of the transform of `S` on `Z`
  obtain ⟨E, h1, h2⟩ := exists_genericPoint_eq_of_flipTransformPrimeDivisor hS
  have hb' : E.genericPoint ∈ MMP.Mori.biregularLocus fp :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp
      hstep.isBirationalMorphism_flip E.coheight_genericPoint.le
  have key : fp.base (q.base PW.genericPoint) = fp.base S'.genericPoint := by
    rw [h2]
    change (q ≫ fp).base PW.genericPoint = _
    rw [← hc]
    change f.base (r.base PW.genericPoint) = _
    rw [hPW, h1]
  exact eq_of_map_eq_of_mem_biregularLocus fp key (by rw [key, h2]; exact hb')

/-- **A common model of a flip with the strict transform of the stratum.** There is a normal
integral `W` with proper birational morphisms `r : W ⟶ X_i`, `q : W ⟶ X_{i+1}` over `Z_i`, and a
prime divisor `P_W` of `W` whose generic point maps to those of `S_i` and `S_{i+1}`. -/
private theorem exists_flip_commonModel
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (r : W ⟶ X i) (q : W ⟶ X (i + 1)),
      r ≫ sX i = q ≫ sX (i + 1) ∧ IsProper r ∧ IsProper q ∧ IsBirationalMorphism r ∧
      IsBirationalMorphism q ∧ r ≫ f i = q ≫ fp i ∧ IsNormalVariety ℂ (r ≫ sX i) ∧
      ∃ PW : MMP.Mori.PrimeDivisor W, r.base PW.genericPoint = (S i).genericPoint ∧
        q.base PW.genericPoint = (S (i + 1)).genericPoint := by
  have hZ := (hflip i).isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral (Z i) := hZ.1.toIsIntegral
  haveI : IsNormal (Z i) := hZ.2
  haveI : AlgebraicGeometry.IsVariety ℂ (sZ i) := hZ.1
  haveI : LocallyOfFiniteType (sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (Z i) := LocallyOfFiniteType.isLocallyNoetherian (sZ i)
  have hfs : f i ≫ sZ i = sX i := (hflip i).isSmall.comp_eq
  have hfps : fp i ≫ sZ i = sX (i + 1) := (hflip i).isSmall_flip.comp_eq
  have hX0 : IsNormalVariety ℂ (f i ≫ sZ i) := by
    rw [hfs]; exact (hflip i).isNegativeExtremalContraction.isNormalVariety_source
  have hX1 : IsNormalVariety ℂ (fp i ≫ sZ i) := by
    rw [hfps]; exact ⟨(hflip i).isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper (f i) := isProper_of_isProjectiveMorphism (f i) (hflip i).isProjectiveMorphism
  haveI : IsProper (fp i) := isProper_of_isProjectiveMorphism (fp i)
    (hflip i).isProjectiveMorphism_flip
  obtain ⟨W, r, q, hW, -, hc, hrP, hrb, hqP, hqb⟩ := MMP.Fourfold.exists_common_model_over (sZ i)
    (f i) (fp i) (hflip i).isBirationalMorphism (hflip i).isBirationalMorphism_flip hX0 hX1
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (q ≫ fp i ≫ sZ i) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (q ≫ fp i ≫ sZ i)
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hrP
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqP
  have hs : r ≫ sX i = q ≫ sX (i + 1) := by
    rw [← hfs, ← hfps, ← Category.assoc, hc, Category.assoc]
  have hWv : IsNormalVariety ℂ (r ≫ sX i) := by rw [hs, ← hfps]; exact hW
  obtain ⟨PW, hPW, hPW'⟩ := exists_primeDivisor_strictTransform (hflip i) (hS i) r q hrb hc
  exact ⟨W, inferInstance, inferInstance, inferInstance, r, q, hs, inferInstance, inferInstance,
    hrb, hqb, hc, hWv, PW, hPW, hPW'⟩

/-- **Monotonicity of log discrepancies on the strata** (the monotonicity clause of
`MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue` for one flip): on a common
model `W` of `X_i` and `X_{i+1}` on which the ambient log discrepancies do not decrease, the log
discrepancies of `(T_i, Δ_i)` and `(T_{i+1}, Δ_{i+1})` along every divisor over the strict
transform of `S` compare in the same way. -/
private theorem adjunction_monotone_strata
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) {W TW : Scheme.{0}} (p : W ⟶ X i) (q : W ⟶ X (i + 1)) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsDominant p] [IsDominant q]
    (hs : p ≫ sX i = q ≫ sX (i + 1)) (hpP : IsProper p) (hqP : IsProper q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hamb : ∀ (E : MMP.Mori.PrimeDivisor W) (m : ℕ) (D : DivisorOver ℂ (sX i))
      (D' : DivisorOver ℂ (sX (i + 1))) (a a' : ℝ), D.valuation = E.valuationOver p →
      D'.valuation = E.valuationOver q → MMP.Intersection.IsLogDiscrepancy (sX i) m (B i) D a →
      MMP.Intersection.IsLogDiscrepancy (sX (i + 1)) m (B (i + 1)) D' a' → a ≤ a')
    (PW : MMP.Mori.PrimeDivisor W) (hPWp : p.base PW.genericPoint = (S i).genericPoint)
    (hPWq : q.base PW.genericPoint = (S (i + 1)).genericPoint)
    (jW : TW ⟶ W) [IsClosedImmersion jW] [IsIntegral TW]
    (hjW : Set.range jW.base = (PW.support : Set W))
    (pT : TW ⟶ T i) (qT : TW ⟶ T (i + 1)) [IsDominant pT] [IsDominant qT]
    (hpT : pT ≫ ι i = jW ≫ p) (hqT : qT ≫ ι (i + 1) = jW ≫ q)
    (G : DivisorOver ℂ (jW ≫ p ≫ sX i)) (D : DivisorOver ℂ (ι i ≫ sX i))
    (D' : DivisorOver ℂ (ι (i + 1) ≫ sX (i + 1)))
    (hD : D.valuation = G.valuation.comap (functionFieldMap pT))
    (hD' : D'.valuation = G.valuation.comap (functionFieldMap qT))
    (m : ℕ) (a a' : ℝ) (ha : MMP.Intersection.IsLogDiscrepancy (ι i ≫ sX i) m (Δ i) D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy (ι (i + 1) ≫ sX (i + 1)) m (Δ (i + 1)) D' a') :
    a ≤ a' := by
  have hXv := (hflip i).isNegativeExtremalContraction.isNormalVariety_source
  haveI : LocallyOfFiniteType (sX i) := hXv.1.toLocallyOfFiniteType
  have hXv' : IsNormalVariety ℂ (sX (i + 1)) := ⟨(hflip i).isSmall_flip.isVariety_source,
    inferInstance⟩
  haveI : LocallyOfFiniteType (sX (i + 1)) := hXv'.1.toLocallyOfFiniteType
  have hsum : ∀ j, Finsupp.single (S j) (1 : ℝ) + (B j - Finsupp.single (S j) 1) = B j :=
    fun j => by abel
  have hbounds : ∀ j, ∀ Q, 0 ≤ (B j - Finsupp.single (S j) 1).coeff Q ∧
      (B j - Finsupp.single (S j) 1).coeff Q ≤ 1 := by
    intro j Q
    rw [DivisorWithCoeffs.coeff_sub]
    by_cases hQ : Q = S j
    · subst hQ; rw [DivisorWithCoeffs.coeff_single_self, hSB]; norm_num
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hQ), sub_zero]; exact (hplt j).1 Q
  have hzero : ∀ j, (B j - Finsupp.single (S j) 1).coeff (S j) = 0 := fun j => by
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hSB, sub_self]
  have hcart : ∀ j, ∃ (m : ℕ) (K : Divisor (X j)), K.IsCanonicalDivisor (sX j) m ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + Finsupp.single (S j) 1 +
        (B j - Finsupp.single (S j) 1)) := fun j => by
    obtain ⟨m, hm⟩ := hK j
    exact ⟨m, K j, hm, by rw [add_assoc, hsum]; exact (hplt j).2.1⟩
  have hdim' : ∀ j, topologicalKrullDim (X j) = ((3 : ℕ) : WithBot ℕ∞) + 1 := fun j => by
    rw [hdim j]; norm_num
  obtain ⟨-, _, -, hall⟩ := exists_isNormal_isRCartierPullback_isPoincareResidue (sX i) (hQ i)
    (hdim' i) (S i) (B i - Finsupp.single (S i) 1) (hbounds i) (hzero i) (hcart i)
    (by rw [hsum]; exact (hplt i).2.2) (ι i) (hι i)
  obtain ⟨-, -, -, -, hmono⟩ := hall (Δ i) fun τ hτ hτS ρ hρ => by
    rw [add_assoc, hsum]; exact hΔ i τ hτ hτS ρ hρ
  exact hmono (sX (i + 1)) (hQ (i + 1)) (hdim' (i + 1)) (S (i + 1))
    (B (i + 1) - Finsupp.single (S (i + 1)) 1) (hbounds (i + 1)) (hzero (i + 1))
    (hcart (i + 1)) (by rw [hsum]; exact (hplt (i + 1)).2.2) (ι (i + 1)) (hι (i + 1))
    (Δ (i + 1)) (fun τ hτ hτS ρ hρ => by rw [add_assoc, hsum]; exact hΔ (i + 1) τ hτ hτS ρ hρ)
    p q hs hpP hqP hpb hqb
    (fun E m D D' a a' h1 h2 h3 h4 => hamb E m D D' a a' h1 h2 (by rwa [hsum] at h3)
      (by rwa [hsum] at h4))
    PW hPWp hPWq jW hjW pT qT hpT hqT G D D' hD hD' m a a' ha ha'

/-- **Divisors over the common biregular locus are not contracted.** Let `ι : T ⟶ X`,
`ι' : T' ⟶ X'` be closed immersions onto the supports of prime divisors `S`, `S'`, with `f : X ⟶ Z`
and `f⁺ : X' ⟶ Z` mapping their generic points to the same point of the biregular locus of `f⁺`.
A prime divisor `P` of `T` whose image in `Z` lies in the biregular loci of both `f` and `f⁺` is
matched by a prime divisor `Q` of `T'` with `ord_Q ∘ ε = ord_P`. -/
private theorem exists_dv_comap_eq_of_mem_biregularLocus {k : Type} [Field k]
    {X X' Z T T' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [IsIntegral T'] [IsLocallyNoetherian T']
    [IsNormal T'] (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] [IsSeparated sX'] [IsSeparated (Z ↘ Limits.terminal Scheme)]
    (f : X ⟶ Z) (fp : X' ⟶ Z) (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι]
    [IsClosedImmersion ι'] (S' : MMP.Mori.PrimeDivisor X')
    (hι' : Set.range ι'.base = (S'.support : Set X')) {n : ℕ} (hT : topologicalKrullDim T = n)
    (hX : topologicalKrullDim X = n + 1) (hT' : topologicalKrullDim T' = n)
    (hX' : topologicalKrullDim X' = n + 1)
    (hη : fp.base S'.genericPoint = (ι ≫ f).base (genericPoint T))
    (hηV : (ι ≫ f).base (genericPoint T) ∈ MMP.Mori.biregularLocus fp)
    (hcorr : (ι ≫ f).base (genericPoint T) = (ι' ≫ fp).base (genericPoint T'))
    (ha : Function.Surjective ((ι ≫ f).stalkMap (genericPoint T)))
    (ε : T.functionField ≃+* T'.functionField)
    (hε : ∀ g, ε (((ι ≫ f).stalkMap (genericPoint T)) g) =
      ((ι' ≫ fp).stalkMap (genericPoint T')) ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom g))
    [TopologicalSpace.NoetherianSpace T] (P : MMP.Mori.PrimeDivisor T)
    (hz : (ι ≫ f).base P.genericPoint ∈ MMP.Mori.biregularLocus f)
    (hz' : (ι ≫ f).base P.genericPoint ∈ MMP.Mori.biregularLocus fp) :
    ∃ Q : MMP.Mori.PrimeDivisor T', (dv Q).comap ε.toRingHom = dv P := by
  set V := MMP.Mori.biregularLocus fp
  haveI : IsIso (fp ∣_ V) := MMP.Mori.isBiregular_biregularLocus fp
  set U : T.Opens := (ι ≫ f) ⁻¹ᵁ V with hUdef
  have hPU : P.genericPoint ∈ U := hz'
  haveI : Nonempty U := ⟨⟨_, hPU⟩⟩
  have hgen : genericPoint T ∈ U := ((genericPoint_spec T).mem_open_set_iff U.2).2 ⟨_, trivial, hPU⟩
  -- the morphism `U ⟶ X'` through the inverse of `f⁺` over its biregular locus
  let m : U.toScheme ⟶ X' := ((ι ≫ f) ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι
  have hm : m ≫ fp = U.ι ≫ (ι ≫ f) := by
    change (((ι ≫ f) ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι) ≫ fp = _
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι fp V, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  have hmap : ∀ u : U.toScheme, fp.base (m.base u) = (ι ≫ f).base u.1 := fun u => by
    change (m ≫ fp).base u = _
    rw [hm]; rfl
  let u0 : U.toScheme := ⟨genericPoint T, hgen⟩
  have hm0 : m.base u0 = S'.genericPoint :=
    eq_of_map_eq_of_mem_biregularLocus fp (by rw [hmap, hη]) (by rw [hmap]; exact hηV)
  haveI : TopologicalSpace.NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set T)
  have hrange : Set.range m.base ⊆ Set.range ι'.base := by
    rintro _ ⟨u, rfl⟩
    have h1 : u0 ⤳ u :=
      (U.ι.isOpenEmbedding.isInducing.specializes_iff).mp (genericPoint_specializes u.1)
    have h2 := h1.map m.base.hom.continuous
    rw [hm0] at h2
    rw [hι', AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp h2
  let gh : U.toScheme ⟶ T' := IsClosedImmersion.lift ι' m (ker_le_ker_of_range_subset ι' m hrange)
  have hgh : gh ≫ ι' = m := IsClosedImmersion.lift_fac _ _ _
  have hcomm : gh ≫ (ι' ≫ fp) = U.ι ≫ (ι ≫ f) := by rw [← Category.assoc, hgh, hm]
  -- `gh` is dominant
  have hgh0 : gh.base u0 = genericPoint T' := by
    apply ι'.isClosedEmbedding.injective
    change (gh ≫ ι').base u0 = _
    rw [hgh, hm0, map_genericPoint_eq_genericPoint ι' S' hι']
  haveI : IsDominant gh := by
    refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨_, hgh0⟩) ?_⟩
    exact dense_iff_closure_eq.2 (by simpa using (genericPoint_spec T').def)
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have hε' := functionFieldMap_ringEquiv_apply (ι ≫ f) (ι' ≫ fp) U.ι gh hcomm hcorr ha ε hε
  -- the image of `η_P` has coheight one
  let pP : U.toScheme := ⟨P.genericPoint, hPU⟩
  let t' := gh.base pP
  have hc1 : Order.coheight (ι.base P.genericPoint) = Order.coheight P.genericPoint + 1 :=
    coheight_map_of_isClosedImmersion sX ι hT hX _
  have hc2 : Order.coheight (ι'.base t') = Order.coheight t' + 1 :=
    coheight_map_of_isClosedImmersion sX' ι' hT' hX' _
  have hxt : ι'.base t' = m.base pP := by
    change (gh ≫ ι').base _ = _; rw [hgh]
  have hc3 : Order.coheight (fp.base (ι'.base t')) = Order.coheight (ι'.base t') :=
    MMP.Positivity.coheight_map_of_mem_biregularLocus fp (by rw [hxt, hmap pP]; exact hz')
  have hc4 : Order.coheight (f.base (ι.base P.genericPoint)) = Order.coheight
      (ι.base P.genericPoint) :=
    MMP.Positivity.coheight_map_of_mem_biregularLocus f hz
  have hfx : fp.base (ι'.base t') = f.base (ι.base P.genericPoint) := by
    rw [hxt, hmap pP]; rfl
  have hco : Order.coheight t' = 1 := by
    rw [P.coheight_genericPoint] at hc1
    have h := (show Order.coheight t' + 1 = 1 + 1 by rw [← hc2, ← hc3, hfx, hc4, hc1])
    generalize Order.coheight t' = c at h ⊢
    induction c using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : (⊤ : ℕ∞) = ((2 : ℕ) : ℕ∞) := by rw [← top_add 1, h]; rfl
      exact ENat.top_ne_coe 2 h2
    | coe c =>
      have : c + 1 = 1 + 1 := by exact_mod_cast h
      obtain rfl : c = 1 := by omega
      rfl
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne t' hco, ?_⟩
  exact (map_genericPoint_eq_iff_comap_eq (ι' ≫ sX') U gh ε hε' P hPU _).mp
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne t' hco).symm

/-- **The flips are isomorphisms at the generic points of the strata.** If the strict transform
of `S` across a real flip `X ⟶ Z ⟵ X⁺` is `S⁺`, the generic points of `S` and `S⁺` map to the
generic point of a prime divisor of the normal variety `Z`, which lies in the biregular loci of
both proper birational morphisms `f` and `f⁺`. -/
private theorem isIso_stalkMap_flip_genericPoint {X Z X' T T' : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral T] [IsIntegral T']
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) {S : MMP.Mori.PrimeDivisor X}
    {S' : MMP.Mori.PrimeDivisor X'} (hS : flipTransformPrimeDivisor f fp S = some S')
    (ι : T ⟶ X) (ι' : T' ⟶ X') (hι : Set.range ι.base = (S.support : Set X))
    (hι' : Set.range ι'.base = (S'.support : Set X')) :
    IsIso (f.stalkMap (ι.base (genericPoint T))) ∧
      IsIso (fp.stalkMap (ι'.base (genericPoint T'))) := by
  have hZ := hstep.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI := isSeparated_terminal sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hstep.isProjectiveMorphism
  haveI : IsProper fp := isProper_of_isProjectiveMorphism fp hstep.isProjectiveMorphism_flip
  obtain ⟨E, h1, h2⟩ := exists_genericPoint_eq_of_flipTransformPrimeDivisor hS
  refine ⟨MMP.isIso_stalkMap_of_mem_biregularLocus f ?_,
    MMP.isIso_stalkMap_of_mem_biregularLocus fp ?_⟩
  · rw [map_genericPoint_eq_genericPoint ι S hι, h1]
    exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f
      hstep.isBirationalMorphism E.coheight_genericPoint.le
  · rw [map_genericPoint_eq_genericPoint ι' S' hι', h2]
    exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp
      hstep.isBirationalMorphism_flip E.coheight_genericPoint.le

/-- **The identification of function fields across a flip.** With `z` the common image in `Z`
of the generic points of `T` and `T⁺`, the stalk maps `𝒪_{Z, z} → k(T)` and `𝒪_{Z, z} → k(T⁺)`
differ by a field isomorphism `ε`, and every induced birational map `φ : T ⤏ T⁺` sends `P` to `Q`
exactly when `ord_Q ∘ ε = ord_P`. -/
private theorem exists_stepEquiv_compat {X Z X' T T' : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T'] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X}
    {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) {S : MMP.Mori.PrimeDivisor X}
    {S' : MMP.Mori.PrimeDivisor X'} (hS : flipTransformPrimeDivisor f fp S = some S')
    (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι] [IsClosedImmersion ι']
    (hι : Set.range ι.base = (S.support : Set X)) (hι' : Set.range ι'.base = (S'.support : Set X'))
    (hcorr : (ι ≫ f).base (genericPoint T) = (ι' ≫ fp).base (genericPoint T')) :
    ∃ ε : T.functionField ≃+* T'.functionField,
      (∀ g, ε ((ι ≫ f).stalkMap (genericPoint T) g) =
        ((ι' ≫ fp).stalkMap (genericPoint T')) ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom g)) ∧
      ∀ φ : T.RationalMap T', MMP.Mori.RationalMap.IsBirational φ →
        φ.compHom (ι' ≫ fp) = (ι ≫ f).toRationalMap →
        ∀ P Q, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ↔
          (dv Q).comap ε.toRingHom = dv P := by
  obtain ⟨h1, h2⟩ := isIso_stalkMap_flip_genericPoint hstep hS ι ι' hι hι'
  obtain ⟨ε, hε⟩ := exists_ringEquiv_stalkMap f fp ι ι' h1 h2 hcorr
  refine ⟨ε, hε, fun φ hφb hφ P Q => ?_⟩
  haveI : IsSeparated sX' := hstep.isSmall_flip.isVariety_source.toIsSeparated
  haveI : IsSeparated sZ :=
    hstep.isNegativeExtremalContraction.isNormalVariety_target.1.toIsSeparated
  haveI := isSeparated_terminal sZ
  haveI : IsProper fp := isProper_of_isProjectiveMorphism fp hstep.isProjectiveMorphism_flip
  exact transformPrimeDivisor_eq_some_iff_comap (ι' ≫ sX') (ι ≫ f) (ι' ≫ fp) hcorr
    (surjective_stalkMap_comp f ι _ h1) ε hε φ hφb hφ P Q

/-- **Log discrepancies on the strata do not decrease across a flip.** -/
private theorem logDiscrepancyFn_le_comap
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) (hcorr : (ι i ≫ f i).base (genericPoint (T i)) =
      (ι (i + 1) ≫ fp i).base (genericPoint (T (i + 1))))
    (ε : (T i).functionField ≃+* (T (i + 1)).functionField)
    (hε : (∀ g, ε ((ι i ≫ f i).stalkMap (genericPoint (T i)) g) =
        ((ι (i + 1) ≫ fp i).stalkMap (genericPoint (T (i + 1))))
          (((Z i).presheaf.stalkCongr (.of_eq hcorr)).hom g)))
    (w : Valuation (T i).functionField ℤᵐ⁰) :
    logDiscrepancyFn (ι i ≫ sX i) (Δ i) w ≤
      logDiscrepancyFn (ι (i + 1) ≫ sX (i + 1)) (Δ (i + 1)) (w.comap ε.symm.toRingHom) := by
  classical
  -- the two strata, with their klt structures
  obtain ⟨-, hT0, ⟨m0, K0, hK0, hK0c⟩, -⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ hdim
      hflip hplt S hS hSB T ι Δ hι hΔ i
  obtain ⟨-, hT1, ⟨m1, K1, hK1, hK1c⟩, -⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ hdim
      hflip hplt S hS hSB T ι Δ hι hΔ (i + 1)
  haveI : LocallyOfFiniteType (ι i ≫ sX i) := hT0.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι (i + 1) ≫ sX (i + 1)) := hT1.1.toLocallyOfFiniteType
  have hZ := (hflip i).isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral (Z i) := hZ.1.toIsIntegral
  -- the common model, the strict transform of `S` and its maps to the strata
  obtain ⟨W, _, _, _, r, q, hs, hrP, hqP, hrb, hqb, hc, hWv, PW, hPWr, hPWq⟩ :=
    exists_flip_commonModel X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB T ι Δ hι hΔ i
  haveI := hrP
  haveI := hqP
  haveI := hrb.isDominant
  haveI := hqb.isDominant
  haveI := PW.integral
  haveI : AlgebraicGeometry.IsVariety ℂ (r ≫ sX i) := hWv.1
  set TW := PW.idealSheaf.subscheme
  set jW := PW.idealSheaf.subschemeι
  have hjW : Set.range jW.base = (PW.support : Set W) := PW.idealSheaf.range_subschemeι
  obtain ⟨pT, hpT⟩ := exists_lift_subschemeι r (ι i) (S i) (hι i) PW hPWr
  obtain ⟨qT, hqT⟩ := exists_lift_subschemeι q (ι (i + 1)) (S (i + 1)) (hι (i + 1)) PW hPWq
  have hjg : jW.base (genericPoint TW) = PW.genericPoint := map_genericPoint_eq_genericPoint jW
      PW hjW
  have hXn : IsNormalVariety ℂ (sX i) :=
      (hflip i).isNegativeExtremalContraction.isNormalVariety_source
  have hXn' : IsNormalVariety ℂ (sX (i + 1)) := ⟨(hflip i).isSmall_flip.isVariety_source,
    inferInstance⟩
  have hisor : IsIso (r.stalkMap (jW.base (genericPoint TW))) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus r (by
      rw [hjg, hPWr]
      exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal r hrb
        (S i).coheight_genericPoint.le)
  have hisoq : IsIso (q.stalkMap (jW.base (genericPoint TW))) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus q (by
      rw [hjg, hPWq]
      exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hqb
        (S (i + 1)).coheight_genericPoint.le)
  obtain ⟨hpTP, hpTb⟩ := isProper_isBirationalMorphism_of_comp_eq r (ι i) jW pT hpT
    (by rw [hjg, hPWr, map_genericPoint_eq_genericPoint (ι i) (S i) (hι i)]) hisor
  obtain ⟨hqTP, hqTb⟩ := isProper_isBirationalMorphism_of_comp_eq q (ι (i + 1)) jW qT hqT
    (by rw [hjg, hPWq, map_genericPoint_eq_genericPoint (ι (i + 1)) (S (i + 1)) (hι (i + 1))])
    hisoq
  haveI := hpTP
  haveI := hqTP
  haveI := hpTb.isDominant
  haveI := hqTb.isDominant
  -- structure morphisms
  have hpTs : pT ≫ (ι i ≫ sX i) = jW ≫ r ≫ sX i := by
    rw [← Category.assoc, hpT, Category.assoc]
  have hqTs : qT ≫ (ι (i + 1) ≫ sX (i + 1)) = jW ≫ r ≫ sX i := by
    rw [← Category.assoc, hqT, Category.assoc, ← hs]
  -- a normal model of `T_W`
  obtain ⟨N, ν, hνP, hνb, hN⟩ := exists_normal_model (r ≫ sX i) jW
  haveI := hνP
  -- `qT^* ∘ ε = pT^*`
  obtain ⟨h1, -⟩ := isIso_stalkMap_flip_genericPoint (hflip i) (hS i) (ι i) (ι (i + 1)) (hι i)
    (hι (i + 1))
  have hcomm : qT ≫ (ι (i + 1) ≫ fp i) = pT ≫ (ι i ≫ f i) := by
    rw [← Category.assoc, hqT, Category.assoc, ← hc, ← Category.assoc, ← hpT, Category.assoc]
  have hcompat := functionFieldMap_ringEquiv_apply (ι i ≫ f i) (ι (i + 1) ≫ fp i) pT qT hcomm
    hcorr (surjective_stalkMap_comp (f i) (ι i) _ h1) ε hε
  have hshift : ∀ G : DivisorOver ℂ (jW ≫ r ≫ sX i),
      G.valuation.comap (functionFieldMap qT) =
        (G.valuation.comap (functionFieldMap pT)).comap ε.symm.toRingHom := by
    intro G; ext x
    simp only [Valuation.comap_apply]
    rw [← hcompat]
    simp
  -- the ambient comparison on `W`
  have hamb : ∀ (E : MMP.Mori.PrimeDivisor W) (m : ℕ) (D : DivisorOver ℂ (sX i))
      (D' : DivisorOver ℂ (sX (i + 1))) (a a' : ℝ), D.valuation = E.valuationOver r →
      D'.valuation = E.valuationOver q →
      MMP.Intersection.IsLogDiscrepancy (sX i) m (B i) D a →
      MMP.Intersection.IsLogDiscrepancy (sX (i + 1)) m (B (i + 1)) D' a' → a ≤ a' :=
    fun E m D D' a a' h1 h2 h3 h4 =>
      isLogDiscrepancy_le_of_comp_eq (hflip i) (hK i) r q hc E m D D' a a' h1 h2 h3 h4
  -- `T_i`, `T_W`, `T_{i+1}` have the same dimension
  haveI : AlgebraicGeometry.IsVariety ℂ (jW ≫ r ≫ sX i) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (ι i ≫ sX i) := hT0.1
  haveI : AlgebraicGeometry.IsVariety ℂ (ι (i + 1) ≫ sX (i + 1)) := hT1.1
  have hd0 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι i ≫ sX i)
    (jW ≫ r ≫ sX i) hpTb
  have hd1 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
    (ι (i + 1) ≫ sX (i + 1)) (jW ≫ r ≫ sX i) hqTb
  by_cases hex : ∃ (n : ℕ) (D : DivisorOver ℂ (ι i ≫ sX i)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (ι i ≫ sX i) n (Δ i) D a ∧ D.valuation = w
  · obtain ⟨n, D, a, ha, rfl⟩ := hex
    rw [logDiscrepancyFn_eq ha]
    obtain ⟨G, D', hD'p, hDG, hD'G⟩ := exists_divisorOver_transfer hT1 pT qT hpTb hqTb hpTs hqTs
      ν hνb hN D
    -- a log discrepancy of `D'` at the index of `D`
    have hn : (m1 : WithBot ℕ∞) = n := by
      rw [← hK1.topologicalKrullDim_eq, hd1, ← hd0,
        MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha]
    obtain rfl : m1 = n := by exact_mod_cast hn
    obtain ⟨a', ha'⟩ := exists_isLogDiscrepancy_of_isRCartier hT1 hK1 hK1c D' hD'p
    have hle := adjunction_monotone_strata X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB
        T ι Δ hι hΔ i r q hs hrP hqP hrb hqb hamb PW hPWr hPWq jW hjW
      pT qT hpT hqT G D D' hDG hD'G m1 a a' ha ha'
    have hD'w : D'.valuation = D.valuation.comap ε.symm.toRingHom := by rw [hD'G, hDG, hshift]
    rw [← hD'w, logDiscrepancyFn_eq ha']
    exact hle
  · rw [logDiscrepancyFn, dif_neg hex]
    by_cases hex' : ∃ (n : ℕ) (D' : DivisorOver ℂ (ι (i + 1) ≫ sX (i + 1))) (a' : ℝ),
        MMP.Intersection.IsLogDiscrepancy (ι (i + 1) ≫ sX (i + 1)) n (Δ (i + 1)) D' a' ∧
          D'.valuation = w.comap ε.symm.toRingHom
    · exfalso
      obtain ⟨n, D', a', -, hD'w⟩ := hex'
      obtain ⟨G, D, hDp, hD'G, hDG⟩ := exists_divisorOver_transfer hT0 qT pT hqTb hpTb hqTs hpTs
        ν hνb hN D'
      obtain ⟨a, ha⟩ := exists_isLogDiscrepancy_of_isRCartier hT0 hK0 hK0c D hDp
      refine hex ⟨m0, D, a, ha, ?_⟩
      rw [hDG]
      have h2 := hshift G
      rw [← hD'G, hD'w] at h2
      ext x
      have := congrArg (fun v : Valuation _ ℤᵐ⁰ => v (ε x)) h2
      simpa [Valuation.comap_apply] using this.symm
    · rw [logDiscrepancyFn, dif_neg hex']

/-- **A divisor contracted on the next stratum lies over the flipping locus**: if no prime
divisor of `T_{i+1}` has the valuation of `P`, the image of `P` in `Z_i` lies outside the common
biregular locus of `f_i` and `f_i⁺`. -/
private theorem notMem_biregularLocus_of_forall_ne
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) (hcorr : (ι i ≫ f i).base (genericPoint (T i)) =
      (ι (i + 1) ≫ fp i).base (genericPoint (T (i + 1))))
    (ε : (T i).functionField ≃+* (T (i + 1)).functionField)
    (hε : (∀ g, ε ((ι i ≫ f i).stalkMap (genericPoint (T i)) g) =
        ((ι (i + 1) ≫ fp i).stalkMap (genericPoint (T (i + 1))))
          (((Z i).presheaf.stalkCongr (.of_eq hcorr)).hom g)))
    (P : MMP.Mori.PrimeDivisor (T i)) (hP : ∀ Q, (dv Q).comap ε.toRingHom ≠ dv P) :
    ¬ ((ι i ≫ f i).base P.genericPoint ∈ MMP.Mori.biregularLocus (f i) ∧
      (ι i ≫ f i).base P.genericPoint ∈ MMP.Mori.biregularLocus (fp i)) := by
  rintro ⟨hz, hz'⟩
  obtain ⟨-, hT0, -, -⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS
      hSB T ι Δ hι hΔ i
  have hXv := (hflip i).isNegativeExtremalContraction.isNormalVariety_source
  have hXv' : IsNormalVariety ℂ (sX (i + 1)) := ⟨(hflip i).isSmall_flip.isVariety_source,
    inferInstance⟩
  haveI : LocallyOfFiniteType (sX i) := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX (i + 1)) := hXv'.1.toLocallyOfFiniteType
  haveI : IsSeparated (sX (i + 1)) := hXv'.1.toIsSeparated
  have hZ := (hflip i).isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral (Z i) := hZ.1.toIsIntegral
  haveI : IsNormal (Z i) := hZ.2
  haveI : LocallyOfFiniteType (sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (Z i) := LocallyOfFiniteType.isLocallyNoetherian (sZ i)
  haveI : IsSeparated (sZ i) := hZ.1.toIsSeparated
  haveI := isSeparated_terminal (sZ i)
  haveI : IsProper (f i) := isProper_of_isProjectiveMorphism (f i) (hflip i).isProjectiveMorphism
  haveI : IsProper (fp i) := isProper_of_isProjectiveMorphism (fp i)
    (hflip i).isProjectiveMorphism_flip
  haveI : LocallyOfFiniteType (ι i ≫ sX i) := hT0.1.toLocallyOfFiniteType
  haveI : QuasiCompact (ι i ≫ sX i) := hT0.1.toQuasiCompact
  haveI : IsNoetherian (T i) :=
    AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType (ι i ≫ sX i)
  have hd : ∀ j, topologicalKrullDim (X j) = ((3 : ℕ) : WithBot ℕ∞) + 1 := fun j => by
    rw [hdim j]; norm_num
  have hdT := topologicalKrullDim_eq_of_range_eq_support (sX i) (ι i) (S i) (hι i) (hd i)
  have hdT' := topologicalKrullDim_eq_of_range_eq_support (sX (i + 1)) (ι (i + 1)) (S (i + 1))
    (hι (i + 1)) (hd (i + 1))
  obtain ⟨E, h1, h2⟩ := exists_genericPoint_eq_of_flipTransformPrimeDivisor (hS i)
  have hη : (fp i).base (S (i + 1)).genericPoint = (ι i ≫ f i).base (genericPoint (T i)) := by
    rw [h2]
    change _ = (f i).base ((ι i).base _)
    rw [map_genericPoint_eq_genericPoint (ι i) (S i) (hι i), h1]
  have hηV : (ι i ≫ f i).base (genericPoint (T i)) ∈ MMP.Mori.biregularLocus (fp i) := by
    rw [← hη, h2]
    exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal (fp i)
      (hflip i).isBirationalMorphism_flip E.coheight_genericPoint.le
  obtain ⟨hi1, -⟩ := isIso_stalkMap_flip_genericPoint (hflip i) (hS i) (ι i) (ι (i + 1)) (hι i)
    (hι (i + 1))
  obtain ⟨Q, hQ⟩ := exists_dv_comap_eq_of_mem_biregularLocus (sX i) (sX (i + 1)) (f i) (fp i)
    (ι i) (ι (i + 1)) (S (i + 1)) (hι (i + 1)) hdT (hd i) hdT' (hd (i + 1)) hη hηV hcorr
    (surjective_stalkMap_comp (f i) (ι i) _ hi1) ε hε P hz hz'
  exact hP Q hQ

/-! ### Strict monotonicity of adjunction along nonpositive diagrams -/

section StrictAdjunction

open MMP MMP.CyclicChartDifferent

private theorem false_of_isEmpty_primeDivisor {S : Scheme.{0}} {sS : S ⟶ Spec (.of ℂ)}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] (hS : IsNormalVariety ℂ sS)
    (h : IsEmpty (Mori.PrimeDivisor S)) (D : DivisorOver ℂ sS) : False := by
  haveI := hS.1
  haveI := D.isNormalVariety.1
  haveI := D.isIntegral
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (D.f ≫ sS)
    D.isBirationalMorphism
  have hd := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg sS
  have hd0 : (letI := functionFieldAlgebra sS; (Algebra.trdeg ℂ S.functionField).toNat) = 0 := by
    by_contra hne
    exact h.false (MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hd hne).some
  have hY : topologicalKrullDim D.Y = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [← hdim, hd, hd0]
  let _ : PartialOrder D.Y := specializationOrder D.Y
  have hk : Order.krullDim D.Y = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [← hY]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := D.Y))).symm
  have := Order.coheight_le_krullDim D.E.genericPoint
  rw [hk, D.E.coheight_genericPoint] at this
  exact absurd this (by decide)

/-! ### Effective pull-backs along arbitrary morphisms -/

section EffectivePullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem notMem_supp_sum_zsmul (f : Y ⟶ X) {m : ℕ} (n : Fin m → ℤ) {L : Fin m → Divisor X}
    (hB : ∀ j, ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (L j).supp)
    (s : Finset (Fin m)) :
    ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (∑ j ∈ s, n j • L j).supp := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro Z h
    rwa [Finset.sum_empty, DivisorWithCoeffs.supp_zero] at h
  | insert j s hj ih =>
    intro Z h
    rw [Finset.sum_insert hj] at h
    rcases DivisorWithCoeffs.supp_add_le _ _ h with h | h
    · obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
      rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hE
      exact hB j Z (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, right_ne_zero_of_mul hE, hmem⟩)
    · exact ih Z h

/-- `f^*(∑ nⱼ Lⱼ) = ∑ nⱼ f^*Lⱼ` for Cartier divisors `Lⱼ` which can be pulled back along `f`. -/
private theorem isPullback_sum_zsmul' [CompactSpace Y] (f : Y ⟶ X) {m : ℕ} (n : Fin m → ℤ)
    {L : Fin m → Divisor X} {L' : Fin m → Divisor Y} (hL : ∀ j, (L j).IsCartier)
    (hB : ∀ j, ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (L j).supp)
    (hp : ∀ j, (L j).IsPullback f (hB j) (L' j)) (s : Finset (Fin m)) :
    (∑ j ∈ s, n j • L j).IsPullback f (notMem_supp_sum_zsmul f n hB s) (∑ j ∈ s, n j • L' j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Divisor.isPullback_zero _
  | insert j s hj ih =>
    have key := Divisor.IsPullback.add ((hL j).zsmul _) (MMP.Fourfold.isCartier_sum_zsmul n hL s)
      (by have := notMem_supp_sum_zsmul f n hB (insert j s); rwa [Finset.sum_insert hj] at this)
      ((hp j).zsmul (hL j) (n j) (fun Z hZ => hB j Z (by
        obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
        rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hE
        exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, right_ne_zero_of_mul hE, hmem⟩))) ih
    convert key using 1 <;> simp only [Finset.sum_insert hj]

/-- **Effective `ℝ`-Cartier divisors pull back to effective divisors**, along any morphism from
a normal scheme for which the pull-back is defined: an effective `∑ rⱼ Lⱼ` is a nonnegative
combination of effective integral combinations of the `Lⱼ`, whose local equations are
regular. -/
private theorem coeff_nonneg_of_isRCartierPullback' [CompactSpace Y] (h : Y ⟶ X)
    {L : RDivisor X} {G : RDivisor Y} (hG : MMP.Flips.IsRCartierPullback h L G)
    (hL : ∀ P, 0 ≤ L.coeff P) (Γ : Mori.PrimeDivisor Y) : 0 ≤ G.coeff Γ := by
  classical
  obtain ⟨m, r, C, C', hC, hLeq, hp, rfl⟩ := hG
  choose hB hp' using hp
  rw [MMP.Flips.coeff_sum_smul_toRDivisor]
  have hcomm : ∑ j, r j * ((C' j).coeff Γ : ℝ) = ∑ j, ((C' j).coeff Γ : ℝ) * r j :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hcomm]
  refine MMP.Fourfold.sum_mul_nonneg_of_forall_int (ι := Mori.PrimeDivisor X)
    (fun P j => (C j).coeff P) (fun j => (C' j).coeff Γ) r ?_ ?_ ?_
  · have hfS : (⋃ j : Fin m, ((C j).support : Set (Mori.PrimeDivisor X))).Finite :=
      Set.finite_iUnion fun j => (C j).support.finite_toSet
    refine hfS.subset fun P hP => ?_
    obtain ⟨j, hj⟩ : ∃ j, (C j).coeff P ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hP (funext hcon)
    exact Set.mem_iUnion.2 ⟨j, Finsupp.mem_support_iff.mpr hj⟩
  · intro nn hn
    have hBV : ∀ P : Mori.PrimeDivisor X, (P.support ∩ (⊤ : X.Opens)).Nonempty →
        0 ≤ (∑ j, nn j • C j).coeff P := fun P _ => by
      rw [MMP.Fourfold.coeff_sum_zsmul]
      simpa [mul_comm] using hn P
    have := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn
      (MMP.Fourfold.isCartier_sum_zsmul nn hC Finset.univ) hBV
      (isPullback_sum_zsmul' h nn hC hB hp' Finset.univ) Γ
      ⟨Γ.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support Γ, trivial⟩
    rw [MMP.Fourfold.coeff_sum_zsmul] at this
    simpa [mul_comm] using this
  · intro P
    have := hL P
    rw [hLeq, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    simpa [mul_comm] using this

end EffectivePullback

section Monotonicity

/-- **The strict transform of `S` is birational to `S`.** If `p : W ⟶ X` is an isomorphism of
local rings at the generic point of `T_W ⊆ W`, and `p_T : T_W ⟶ T` is the restriction of `p` to
integral closed subschemes, then `p_T^* : k(T) → k(T_W)` is bijective. -/
private theorem functionFieldMap_bijective_of_comp_eq {X W T TW : Scheme.{0}} [IsIntegral T]
    [IsIntegral TW] (p : W ⟶ X) (j : T ⟶ X) (jW : TW ⟶ W) [IsClosedImmersion jW]
    (pT : TW ⟶ T) [IsDominant pT] (hpT : pT ≫ j = jW ≫ p)
    [IsIso (p.stalkMap (jW (genericPoint TW)))] :
    Function.Bijective (functionFieldMap pT) := by
  refine ⟨(functionFieldMap pT).injective, fun y => ?_⟩
  obtain ⟨b, hb⟩ := SurjectiveOnStalks.stalkMap_surjective jW (genericPoint TW) y
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (p.stalkMap (jW (genericPoint TW)))).2 b
  have key : ∀ c : X.presheaf.stalk ((jW ≫ p) (genericPoint TW)),
      ∃ a : T.presheaf.stalk (pT (genericPoint TW)),
        (pT.stalkMap (genericPoint TW)).hom a = ((jW ≫ p).stalkMap (genericPoint TW)).hom c := by
    rw [← hpT]
    intro c
    exact ⟨(j.stalkMap (pT (genericPoint TW))).hom c, by rw [Scheme.Hom.stalkMap_comp]; rfl⟩
  obtain ⟨a, ha⟩ := key c
  refine ⟨algebraMap _ T.functionField a, ?_⟩
  rwa [MMP.Mori.functionFieldMap_algebraMap_stalk, ha, Scheme.Hom.stalkMap_comp,
    MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint]

/-! ### Changing the structure morphism of forms -/

section Cast

variable {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]

/-- The order of a form does not see a change of the structure morphism. -/
private theorem ordForm_cast [IsLocallyNoetherian Y] {s₁ s₂ : Y ⟶ Spec (.of k)} (h : s₁ = s₂)
    {d : ℕ} {m : ℤ} (ρ : RationalPluriForms s₁ d m) (E : Mori.PrimeDivisor Y) :
    E.ordForm (cast (congrArg (fun s => RationalPluriForms s d m) h) ρ) = E.ordForm ρ := by
  subst h; rfl

/-- Pull-back of forms commutes with a change of the structure morphism. -/
private theorem pullbackRationalPluriForms_cast {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ Y)
    [IsDominant f] {s₁ s₂ : Y ⟶ Spec (.of k)} (h : s₁ = s₂) {d : ℕ} {m : ℤ}
    (ρ : RationalPluriForms s₁ d m) :
    pullbackRationalPluriForms s₂ f (cast (congrArg (fun s => RationalPluriForms s d m) h) ρ) =
      cast (congrArg (fun s => RationalPluriForms (f ≫ s) d m) h)
        (pullbackRationalPluriForms s₁ f ρ) := by
  subst h; rfl

/-- Poincaré residues do not see a change of the structure morphism. -/
private theorem isPoincareResidue_cast [IsLocallyNoetherian Y] {T : Scheme.{0}} [IsIntegral T]
    {s₁ s₂ : Y ⟶ Spec (.of k)}
    (h : s₁ = s₂) (j : T ⟶ Y) {n m : ℕ} {τ : RationalPluriForms s₁ (n + 1) m}
    {ρ : RationalPluriForms (j ≫ s₁) n m} (hr : IsPoincareResidue s₁ j n m τ ρ) :
    IsPoincareResidue s₂ j n m (cast (congrArg (fun s => RationalPluriForms s (n + 1) m) h) τ)
      (cast (congrArg (fun s => RationalPluriForms (j ≫ s) n m) h) ρ) := by
  subst h; exact hr

end Cast

/-- The restriction `p_T : T_W ⟶ T` of a proper morphism to integral closed subschemes, which is
a local isomorphism at the generic point of `T_W`, is birational. -/
private theorem isBirationalMorphism_of_comp_eq {X W T TW : Scheme.{0}} [IsIntegral T]
    [IsIntegral TW] (p : W ⟶ X) [IsProper p] (j : T ⟶ X) [IsClosedImmersion j] (jW : TW ⟶ W)
    [IsClosedImmersion jW] (pT : TW ⟶ T) [IsDominant pT] (hpT : pT ≫ j = jW ≫ p)
    [IsIso (p.stalkMap (jW (genericPoint TW)))] : IsBirationalMorphism pT := by
  haveI : IsProper (pT ≫ j) := hpT ▸ inferInstance
  haveI : IsProper pT := IsProper.of_comp pT j
  exact MMP.Mori.isBirationalMorphism_of_bijective_functionFieldMap pT
    (functionFieldMap_bijective_of_comp_eq p j jW pT hpT)

/-! ### Cartier divisors along the strict transform -/

section StrictTransform

variable {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
  [IsLocallyNoetherian W] [IsNormal W]

/-- Pull-backs of a Cartier divisor along equal morphisms agree. -/
private theorem isPullback_eq_of_eq [CompactSpace W] {f₁ f₂ : W ⟶ X} (hf : f₁ = f₂) {C : Divisor X}
    (hC : C.IsCartier)
    {hB₁ : ∀ Z : irreducibleComponents W, f₁ (componentGenericPoint W Z) ∉ C.supp}
    {hB₂ : ∀ Z : irreducibleComponents W, f₂ (componentGenericPoint W Z) ∉ C.supp}
    {C₁ C₂ : Divisor W} (h₁ : C.IsPullback f₁ hB₁ C₁) (h₂ : C.IsPullback f₂ hB₂ C₂) : C₁ = C₂ := by
  subst hf
  exact (Divisor.IsPullback.pullback_eq hC h₁).symm.trans (Divisor.IsPullback.pullback_eq hC h₂)

/-- If `p : W ⟶ X` maps the generic point of a prime divisor `P_W` to that of `P` and is a local
isomorphism there, the pull-back of a Cartier divisor `C` not containing `P` does not contain
`P_W`. -/
private theorem genericPoint_notMem_supp_of_isPullback (p : W ⟶ X) [IsDominant p]
    (P : Mori.PrimeDivisor X) (PW : Mori.PrimeDivisor W) (hpPW : p PW.genericPoint = P.genericPoint)
    [IsIso (p.stalkMap PW.genericPoint)] {C : Divisor X} (hC : C.IsCartier) (hCP : C.coeff P = 0)
    {hB : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ C.supp}
    {C' : Divisor W} (h : C.IsPullback p hB C') : PW.genericPoint ∉ C'.supp := by
  intro hm
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
  obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E PW hmem
  apply hE
  obtain ⟨U, hU, φ, hφ⟩ := hC P.genericPoint
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ E (hpPW ▸ hU)
    (MMP.Mori.pointComponent P.genericPoint), MMP.Positivity.ord_functionFieldMap_of_isIso p E
        P hpPW]
  have h2 := hφ P ((P.genericPoint_mem_iff U).mp hU)
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h2
  have hZ : P.component = MMP.Mori.pointComponent P.genericPoint := Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  rw [hZ, hCP] at h2
  exact_mod_cast h2.symm

end StrictTransform

/-- **The log discrepancy on another model.** A log discrepancy of `(T, B)` along `D` is computed,
with any top form `ω` and any presentation of `K_T + B` by Cartier divisors, on every model `D₁` of
the same valuation, proper or not. -/
private theorem isLogDiscrepancy_eq_of_valuation_eq {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T]
    {d m : ℕ} {B : RDivisor T} {D : DivisorOver ℂ sT} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sT m B D a)
    {ω : RationalPluriForms sT d 1} (hω0 : ω ≠ 0)
    (hK : ∃ K : Divisor T, K.IsCanonicalDivisor sT d ∧ ∀ Γ, K.coeff Γ = Γ.ordForm ω)
    {k : ℕ} (r : Fin k → ℝ) (C : Fin k → Divisor T) (hC : ∀ i, (C i).IsCartier)
    (hsum : ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ)
    (D₁ : DivisorOver ℂ sT) (hv : D₁.valuation = D.valuation) (C₁ : Fin k → Divisor D₁.Y)
    (hC₁ : haveI := D₁.isLocallyNoetherian; haveI := D₁.isNormal
      ∀ i, ∃ h, (C i).IsPullback D₁.f h (C₁ i)) :
    a = 1 + D₁.ordPullback ω - ∑ i, r i * (C₁ i).coeff D₁.E := by
  obtain ⟨hT, hprop, -⟩ := id ha
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := D₁.isIntegral
  haveI := D₁.isLocallyNoetherian
  haveI := D₁.isNormal
  haveI := D₁.isDominant
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC i)
  have hb : MMP.Intersection.IsLogDiscrepancy sT d B D
      (1 + D.ordPullback ω - ∑ i, r i * (C' i).coeff D.E) :=
    ⟨hT, hprop, ω, hω0, hK, k, r, C, C', hC, hsum, fun i => ⟨_, hC' i⟩, rfl⟩
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha hb]
  obtain ⟨K, hKc, -⟩ := hK
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hT
    hKc.topologicalKrullDim_eq hv.symm ω]
  have hcen := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hT hv
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  obtain ⟨h₁, hp₁⟩ := hC₁ i
  obtain ⟨U, hU, φ, hφ⟩ := hC i (D.f D.E.genericPoint)
  let Z := MMP.Mori.pointComponent (D.f D.E.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hC' i) hφ D.E hU Z,
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hp₁ hφ D₁.E (hcen ▸ hU) Z]
  have hne : MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions T) ≠ 0 :=
    ((φ.isUnit.map _).ne_zero)
  exact MMP.Threefold.Bridges.ord_functionFieldMap_eq_of_valuationOver_eq D₁.E D.E hv hne

/-- **One side of a nonpositive diagram.** Let `p : W ⟶ X` be proper birational, `P_W ⊆ W` a prime
divisor over `S = P` with closed subscheme `T_W` and `p_T : T_W ⟶ T`, and `τ_W` a top form on `W`
with a simple pole along `P_W` and residue `ρ_W`. Then `K_X + S + Δ` has a presentation whose
pull-back to `W` is a combination `∑ rᵢ Cᵢ` of Cartier divisors not containing `P_W`, computing the
log discrepancies over `X` of the prime divisors of `W` with the form `τ_W`, and computing on the
model of any divisor `G` over `T_W` the log discrepancy of `(T, Δ_S)` along `G` with the form
`ρ_W`. -/
private theorem exists_side_data
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (P : Mori.PrimeDivisor X) (Δ : RDivisor X)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [IsNormal T] (hj : Set.range j.base = (P.support : Set X))
    (ΔS : RDivisor T)
    (hΔS : ∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS))
    {W TW : Scheme.{0}} (p : W ⟶ X) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsDominant p] [IsProper p] (hpb : IsBirationalMorphism p)
    (sW : W ⟶ Spec (.of ℂ)) (hsW : p ≫ sX = sW)
    (PW : Mori.PrimeDivisor W) (hpPW : p PW.genericPoint = P.genericPoint)
    (jW : TW ⟶ W) [IsClosedImmersion jW] [IsIntegral TW]
    (hjW : Set.range jW.base = (PW.support : Set W))
    (pT : TW ⟶ T) [IsDominant pT] (hpT : pT ≫ j = jW ≫ p)
    (τW : RationalPluriForms sW (n + 1) 1) (hτW : PW.ordForm τW = -1)
    (ρW : RationalPluriForms (jW ≫ sW) n 1) (hρW : IsPoincareResidue sW jW n 1 τW ρW)
    (G : DivisorOver ℂ (jW ≫ sW)) (D : DivisorOver ℂ (j ≫ sX))
    (hD : D.valuation = G.valuation.comap (functionFieldMap pT))
    (m : ℕ) (a : ℝ) (ha : MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m ΔS D a) :
    ∃ (k : ℕ) (r : Fin k → ℝ) (C : Fin k → Divisor W), (∀ i, (C i).IsCartier) ∧
      (∀ i, PW.genericPoint ∉ (C i).supp) ∧
      (∀ E : Mori.PrimeDivisor W, ∃ DW : DivisorOver ℂ sX, DW.valuation = E.valuationOver p ∧
        MMP.Intersection.IsLogDiscrepancy sX (n + 1) (Finsupp.single P 1 + Δ) DW
          (1 + E.ordForm τW - ∑ i, r i * (C i).coeff E)) ∧
      haveI := G.isLocallyNoetherian
      haveI := G.isNormal
      ∃ (C' : Fin k → Divisor G.Y), (∀ i, ∃ h, (C i).IsPullback (G.f ≫ jW) h (C' i)) ∧
        a = 1 + G.ordPullback ρW - ∑ i, r i * (C' i).coeff G.E := by
  classical
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  have hWv : IsNormalVariety ℂ (p ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType sW := hsW ▸ hWv.1.toLocallyOfFiniteType
  have hTv : IsNormalVariety ℂ (j ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType (j ≫ sX) := hTv.1.toLocallyOfFiniteType
  have hjT := Aux.map_genericPoint_eq j P hj
  have hjWT := Aux.map_genericPoint_eq jW PW hjW
  haveI : IsIso (p.stalkMap PW.genericPoint) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb hpPW
  haveI : IsIso (p.stalkMap (jW (genericPoint TW))) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb (by rw [hjWT, hpPW])
  have hpTbij := functionFieldMap_bijective_of_comp_eq p j jW pT hpT
  have hpTb := isBirationalMorphism_of_comp_eq p j jW pT hpT
  have hpbij := hpb.functionFieldMap_bijective
  have hd : (letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat) = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (letI := functionFieldAlgebra (j ≫ sX);
      (Algebra.trdeg ℂ T.functionField).toNat) = n := by
    have := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  have hdimT : topologicalKrullDim T = n := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (j ≫ sX), hdT]
  -- the form `τ` on `X` with `p^*τ = τ_W`
  obtain ⟨τ, hτp⟩ := MMP.Mori.exists_pullbackRationalPluriForms_eq (sZ := sX) p hpbij hd
    (cast (congrArg (fun s => RationalPluriForms s (n + 1) (1 : ℤ)) hsW.symm) τW)
  have hτ : P.ordForm τ = -1 := by
    rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpbij hd PW P hpPW τ, hτp,
      ordForm_cast hsW.symm, hτW]
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [PrimeDivisor.ordForm_zero] at hτ
    norm_num at hτ
  -- its residue `ρ` along `T`
  have hT0 : Nonempty (Mori.PrimeDivisor T) := by
    by_contra h
    exact false_of_isEmpty_primeDivisor hTv (not_nonempty_iff.mp h) D
  obtain ⟨σ, hσ0, hσ, ρσ, hρσ, -⟩ :=
    MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX hX hdim j hTv P hj hT0.some
  obtain ⟨b, -, hρ⟩ := MMP.Fourfold.IsPoincareResidue.exists_unit_smul hdim P hjT hσ0 hτ0
    (hσ.trans hτ.symm) hρσ
  set ρ := (j.stalkMap (genericPoint T)).hom ((b⁻¹ : (X.presheaf.stalk _)ˣ) : _) • ρσ with hρdef
  have hρ0 : ρ ≠ 0 := Aux.isPoincareResidue_ne_zero sX hX hdim j hTv P hj τ hτ0 hτ ρ hρ hT0.some
  -- canonical divisors
  obtain ⟨K₁, hK₁⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (j ≫ sX) hTv hdimT
  have hKρ : (divisorOfForm ρ).IsCanonicalDivisor (j ≫ sX) n :=
    hK₁.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hTv hK₁ hρ0)
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX hX (n := n + 1)
    (by rw [hdim]; norm_cast)
  have hKτ : (divisorOfForm τ).IsCanonicalDivisor sX (n + 1) :=
    hK₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK₀ hτ0)
  -- a presentation of `K_X + S + Δ` restricting to `K_S + Δ_S`
  obtain ⟨k, r, C, CT, hC, hL, hCT, hG⟩ := hΔS τ hτ0 hτ ρ hρ
  have hCTc : ∀ i, (CT i).IsCartier := fun i => (hCT i).2.isCartier (hC i)
  have hCP : ∀ i, (C i).coeff P = 0 := fun i => by
    obtain ⟨hB, -⟩ := hCT i
    by_contra hne
    refine hB (MMP.Mori.pointComponent (genericPoint T))
      (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, ?_⟩)
    rw [componentGenericPoint_eq_genericPoint, hjT]
    exact MMP.Flips.primeDivisor_genericPoint_mem_support P
  choose CW hCW using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant p (hC i)
  have hCWc : ∀ i, (CW i).IsCartier := fun i => (hCW i).isCartier (hC i)
  have hCWP : ∀ i, PW.genericPoint ∉ (CW i).supp := fun i =>
    genericPoint_notMem_supp_of_isPullback p P PW hpPW (hC i) (hCP i) (hCW i)
  have hsumX : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm τ : ℝ) +
      (Finsupp.single P 1 + Δ : RDivisor X).coeff Γ = ∑ i, r i * ((C i).coeff Γ : ℝ) := by
    intro Γ
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hL
    simp only [MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this]
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]
    ring
  have hsumT : ∀ Γ : Mori.PrimeDivisor T, (Γ.ordForm ρ : ℝ) + ΔS.coeff Γ =
      ∑ i, r i * ((CT i).coeff Γ : ℝ) := by
    intro Γ
    have := congrArg (fun D : RDivisor T => D.coeff Γ) hG
    simp only [MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]
  refine ⟨k, r, CW, hCWc, hCWP, fun E => ⟨⟨W, p, hWv, hpb, E⟩, rfl, ?_⟩, ?_⟩
  · -- the log discrepancy over `X` of a prime divisor of `W`
    have hb : MMP.Intersection.IsLogDiscrepancy sX (n + 1) (Finsupp.single P 1 + Δ)
        ⟨W, p, hWv, hpb, E⟩ (1 + (DivisorOver.ordPullback ⟨W, p, hWv, hpb, E⟩ τ : ℝ) -
          ∑ i, r i * ((CW i).coeff E : ℝ)) :=
      ⟨hX, inferInstance, τ, hτ0, ⟨divisorOfForm τ, hKτ, fun Γ => rfl⟩, k, r, C, CW, hC, hsumX,
        fun i => ⟨_, hCW i⟩, rfl⟩
    have hord : (DivisorOver.ordPullback ⟨W, p, hWv, hpb, E⟩ τ : ℤ) = E.ordForm τW := by
      change E.ordForm (pullbackRationalPluriForms sX p τ) = _
      rw [hτp, ordForm_cast hsW.symm]
    rwa [hord] at hb
  · -- the log discrepancy over `S`, on the model of `G`
    haveI := G.isIntegral
    haveI := G.isNormal
    haveI := G.isLocallyNoetherian
    haveI := G.isDominant
    haveI : QuasiCompact (G.f ≫ jW ≫ sW) := G.isNormalVariety.1.toQuasiCompact
    haveI : CompactSpace G.Y := QuasiCompact.compactSpace_of_compactSpace (G.f ≫ jW ≫ sW)
    have hTW : pT ≫ j ≫ sX = jW ≫ sW := by rw [← hsW, reassoc_of% hpT]
    have hcomp : (G.f ≫ pT) ≫ j ≫ sX = G.f ≫ jW ≫ sW := by rw [Category.assoc, hTW]
    let GT : DivisorOver ℂ (j ≫ sX) :=
      ⟨G.Y, G.f ≫ pT, hcomp ▸ G.isNormalVariety,
        MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp G.isBirationalMorphism hpTb, G.E⟩
    have hGT : GT.valuation = D.valuation := by
      rw [hD]
      refine Valuation.ext fun t => ?_
      change G.E.divisorialValuation (functionFieldMap (G.f ≫ pT) t) =
        G.E.divisorialValuation (functionFieldMap G.f (functionFieldMap pT t))
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    choose C₁ hC₁ using fun i =>
      MMP.Threefold.Bridges.exists_isPullback_of_isDominant (G.f ≫ pT) (hCTc i)
    have ha1 := isLogDiscrepancy_eq_of_valuation_eq ha hρ0 ⟨divisorOfForm ρ, hKρ, fun Γ => rfl⟩ r
      CT hCTc hsumT GT hGT C₁ (fun i => ⟨_, hC₁ i⟩)
    -- the pull-backs of the `C_i` to the model of `G`
    have hgen : ∀ i, ∀ Z : irreducibleComponents G.Y,
        (G.f ≫ jW) (componentGenericPoint G.Y Z) ∉ (CW i).supp := fun i Z => by
      rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply,
        map_genericPoint_of_isDominant, hjWT]
      exact hCWP i
    choose C₂ hC₂ using fun i => (hCWc i).exists_isPullback (hgen i)
    have hC₁₂ : ∀ i, C₁ i = C₂ i := fun i => by
      obtain ⟨hB, hpbT⟩ := hCT i
      have hPnot : P.genericPoint ∉ (C i).supp := by
        have := hB (MMP.Mori.pointComponent (genericPoint T))
        rwa [componentGenericPoint_eq_genericPoint, hjT] at this
      have h1 := MMP.ProgramBaseChange.divisor_isPullback_comp (e := (G.f ≫ pT) ≫ j) rfl hpbT
          (hC₁ i) (fun Z => by
          rw [componentGenericPoint_eq_genericPoint]
          show j (pT (G.f (genericPoint G.Y))) ∉ _
          rw [map_genericPoint_of_isDominant G.f, map_genericPoint_of_isDominant pT, hjT]
          exact hPnot)
      have h2 := MMP.ProgramBaseChange.divisor_isPullback_comp (e := (G.f ≫ jW) ≫ p) rfl (hCW i)
          (hC₂ i) (fun Z => by
          rw [componentGenericPoint_eq_genericPoint]
          show p (jW (G.f (genericPoint G.Y))) ∉ _
          rw [map_genericPoint_of_isDominant G.f, hjWT, hpPW]
          exact hPnot)
      exact isPullback_eq_of_eq (by simp only [Category.assoc, hpT]) (hC i) h1 h2
    refine ⟨C₂, fun i => ⟨_, hC₂ i⟩, ?_⟩
    rw [ha1]
    simp only [hC₁₂]
    congr 2
    -- the order of the pulled-back residue: `ρ_W = p_T^*ρ`
    have hres := MMP.Fourfold.isPoincareResidue_pullback p j jW pT sX hpbij hpTbij hpT P hjT PW
      hjWT hd hdT hρ
    have hres' := isPoincareResidue_cast hsW jW hres
    rw [hτp] at hres'
    simp only [cast_cast, cast_eq] at hres'
    have huniq := MMP.Fourfold.IsPoincareResidue.unique_of_isClosedImmersion PW hjWT hρW hres'
    haveI : LocallyOfFiniteType (pT ≫ j ≫ sX) := hTW ▸ inferInstance
    have key : GT.ordPullback ρ = G.ordPullback ρW := by
      show (G.E.ordForm (pullbackRationalPluriForms (j ≫ sX) (G.f ≫ pT) ρ) : ℤ) =
        G.E.ordForm (pullbackRationalPluriForms (jW ≫ sW) G.f ρW)
      rw [huniq, ← MMP.Flips.pullbackRationalPluriForms_comp pT G.f hpTbij
        G.isBirationalMorphism.functionFieldMap_bijective hdT ρ,
        pullbackRationalPluriForms_cast G.f hTW, ordForm_cast (congrArg (G.f ≫ ·) hTW)]
      rfl
    exact congrArg _ key
/-- **Strict monotonicity of adjunction along a nonpositive diagram.** In the situation of
monotonicity along a nonpositive diagram, suppose moreover that the centre on `W` of the divisor
`G` over `T_W` lies on a Cartier prime divisor `E` of `W` along which the ambient log discrepancy
strictly increases. Then `a(G; T, Δ_S) < a(G; T', Δ_{S'})`: the difference is the coefficient
along `G` of the pull-back of `F = p^*(K_X + S + Δ) - q^*(K_{X'} + S' + Δ')`, and `F - ε E` is
effective for `ε = mult_E F > 0`, while the pull-back of `E` has coefficient at least one along
`G`. -/
private theorem isLogDiscrepancy_lt_of_nonpositive_diagram
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (P : Mori.PrimeDivisor X) (Δ : RDivisor X)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [IsNormal T] (hj : Set.range j.base = (P.support : Set X)) (ΔS : RDivisor T)
    (hΔS : ∀ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 → P.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P 1 + Δ)
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS))
    {X' T' W TW : Scheme.{0}} (sX' : X' ⟶ Spec (.of ℂ)) [IsIntegral X'] [IsNormal X']
    [IsLocallyNoetherian X'] [CompactSpace X'] [LocallyOfFiniteType sX']
    (hX' : IsNormalVariety ℂ sX') (hdim' : topologicalKrullDim X' = n + 1)
    (P' : Mori.PrimeDivisor X') (Δ' : RDivisor X')
    (j' : T' ⟶ X') [IsClosedImmersion j'] [IsIntegral T'] [IsLocallyNoetherian T']
    [CompactSpace T'] [IsNormal T'] (hj' : Set.range j'.base = (P'.support : Set X'))
    (ΔS' : RDivisor T')
    (hΔS' : ∀ τ : RationalPluriForms sX' (n + 1) 1, τ ≠ 0 → P'.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (j' ≫ sX') n 1, IsPoincareResidue sX' j' n 1 τ ρ →
          MMP.Flips.IsRCartierPullback j'
            (Divisor.toRDivisor (divisorOfForm τ) + Finsupp.single P' 1 + Δ')
            (Divisor.toRDivisor (divisorOfForm ρ) + ΔS'))
    (p : W ⟶ X) (q : W ⟶ X') [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsDominant p] [IsDominant q] (hpq : p ≫ sX = q ≫ sX') (hpP : IsProper p) (hqP : IsProper q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hle : ∀ (E : Mori.PrimeDivisor W) (m : ℕ) (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX')
      (a a' : ℝ), D.valuation = E.valuationOver p → D'.valuation = E.valuationOver q →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) D a →
      MMP.Intersection.IsLogDiscrepancy sX' m (Finsupp.single P' 1 + Δ') D' a' → a ≤ a')
    (PW : Mori.PrimeDivisor W) (hpPW : p PW.genericPoint = P.genericPoint)
    (hqPW : q PW.genericPoint = P'.genericPoint)
    (jW : TW ⟶ W) [IsClosedImmersion jW] [IsIntegral TW]
    (hjW : Set.range jW.base = (PW.support : Set W))
    (pT : TW ⟶ T) (qT : TW ⟶ T') [IsDominant pT] [IsDominant qT]
    (hpT : pT ≫ j = jW ≫ p) (hqT : qT ≫ j' = jW ≫ q)
    (G : DivisorOver ℂ (jW ≫ p ≫ sX)) (D : DivisorOver ℂ (j ≫ sX))
    (D' : DivisorOver ℂ (j' ≫ sX'))
    (hD : D.valuation = G.valuation.comap (functionFieldMap pT))
    (hD' : D'.valuation = G.valuation.comap (functionFieldMap qT))
    (m : ℕ) (a a' : ℝ) (ha : MMP.Intersection.IsLogDiscrepancy (j ≫ sX) m ΔS D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy (j' ≫ sX') m ΔS' D' a')
    (E : Mori.PrimeDivisor W) (hEC : Divisor.IsCartier (Finsupp.single E 1 : Divisor W))
    (hcE : (G.f ≫ jW).base G.E.genericPoint ∈ (E.support : Set W))
    (hlt : ∀ (m : ℕ) (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX') (a a' : ℝ),
      D.valuation = E.valuationOver p → D'.valuation = E.valuationOver q →
      MMP.Intersection.IsLogDiscrepancy sX m (Finsupp.single P 1 + Δ) D a →
      MMP.Intersection.IsLogDiscrepancy sX' m (Finsupp.single P' 1 + Δ') D' a' → a < a') :
    a < a' := by
  classical
  haveI := hpP
  haveI := hqP
  have hWv : IsNormalVariety ℂ (p ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.1.toLocallyOfFiniteType
  have hTv : IsNormalVariety ℂ (j ≫ sX) := by
    haveI := hX.1
    exact ⟨⟨⟩, inferInstance⟩
  haveI : LocallyOfFiniteType (j ≫ sX) := hTv.1.toLocallyOfFiniteType
  have hjT := Aux.map_genericPoint_eq j P hj
  have hjWT := Aux.map_genericPoint_eq jW PW hjW
  haveI : IsIso (p.stalkMap PW.genericPoint) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb hpPW
  haveI : IsIso (p.stalkMap (jW (genericPoint TW))) :=
    MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb (by rw [hjWT, hpPW])
  have hpTbij := functionFieldMap_bijective_of_comp_eq p j jW pT hpT
  have hpbij := hpb.functionFieldMap_bijective
  have hd : (letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat) = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (letI := functionFieldAlgebra (j ≫ sX);
      (Algebra.trdeg ℂ T.functionField).toNat) = n := by
    have := Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  -- the common form `τ_W = p^*τ₀` on `W` and its residue along `T_W`
  have hT0 : Nonempty (Mori.PrimeDivisor T) := by
    by_contra h
    exact false_of_isEmpty_primeDivisor hTv (not_nonempty_iff.mp h) D
  obtain ⟨τ₀, -, hτ₀, ρ₀, hρ₀, -⟩ :=
    MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX hX hdim j hTv P hj hT0.some
  have hτW : PW.ordForm (pullbackRationalPluriForms sX p τ₀) = -1 := by
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpbij hd PW P hpPW, hτ₀]
  have hρW := MMP.Fourfold.isPoincareResidue_pullback p j jW pT sX hpbij hpTbij hpT P hjT PW
    hjWT hd hdT hρ₀
  -- the two sides
  obtain ⟨k, r, C, hCc, hCP, hCW, C₂, hC₂, ha₂⟩ := exists_side_data sX hX hdim P Δ j hj ΔS hΔS p
    hpb (p ≫ sX) rfl PW hpPW jW hjW pT hpT _ hτW _ hρW G D hD m a ha
  obtain ⟨k', r', C', hCc', hCP', hCW', C₂', hC₂', ha₂'⟩ := exists_side_data sX' hX' hdim' P' Δ' j'
    hj' ΔS' hΔS' q hqb (p ≫ sX) hpq.symm PW hqPW jW hjW qT hqT _ hτW _ hρW G D' hD' m a' ha'
  -- `F = p^*(K_X + S + Δ) - q^*(K_{X'} + S' + Δ')` is effective on `W`
  have hF : ∀ E : Mori.PrimeDivisor W, 0 ≤ (∑ i, r i • Divisor.toRDivisor (C i) +
      ∑ i, (-r' i) • Divisor.toRDivisor (C' i) : RDivisor W).coeff E := by
    intro E
    obtain ⟨DW, hDWv, hDW⟩ := hCW E
    obtain ⟨DW', hDWv', hDW'⟩ := hCW' E
    have := hle E (n + 1) DW DW' _ _ hDWv hDWv' hDW hDW'
    rw [DivisorWithCoeffs.coeff_add, MMP.Flips.coeff_sum_smul_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor]
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith
  -- its pull-back to the model of `G` is effective
  haveI := G.isIntegral
  haveI := G.isNormal
  haveI := G.isLocallyNoetherian
  haveI : QuasiCompact (G.f ≫ jW ≫ p ≫ sX) := G.isNormalVariety.1.toQuasiCompact
  haveI : CompactSpace G.Y := QuasiCompact.compactSpace_of_compactSpace (G.f ≫ jW ≫ p ≫ sX)
  have hpbF : MMP.Flips.IsRCartierPullback (G.f ≫ jW)
      (∑ i, r i • Divisor.toRDivisor (C i) + ∑ i, (-r' i) • Divisor.toRDivisor (C' i))
      (∑ i, r i • Divisor.toRDivisor (C₂ i) + ∑ i, (-r' i) • Divisor.toRDivisor (C₂' i)) := by
    refine MMP.Fourfold.isRCartierPullback_add
      (MMP.Fourfold.isRCartierPullback_sum _ _ _ fun i _ => ?_)
      (MMP.Fourfold.isRCartierPullback_sum _ _ _ fun i _ => ?_)
    · obtain ⟨hB, hp⟩ := hC₂ i
      exact MMP.Fourfold.isRCartierPullback_smul _
        (MMP.Fourfold.isRCartierPullback_toRDivisor (hCc i) hB hp)
    · obtain ⟨hB, hp⟩ := hC₂' i
      exact MMP.Fourfold.isRCartierPullback_smul _
        (MMP.Fourfold.isRCartierPullback_toRDivisor (hCc' i) hB hp)
  set FW : RDivisor W := ∑ i, r i • Divisor.toRDivisor (C i) +
    ∑ i, (-r' i) • Divisor.toRDivisor (C' i) with hFW
  set FG : RDivisor G.Y := ∑ i, r i • Divisor.toRDivisor (C₂ i) +
    ∑ i, (-r' i) • Divisor.toRDivisor (C₂' i) with hFG
  -- `F` has positive coefficient `ε` along `E`
  have hεpos : 0 < FW.coeff E := by
    obtain ⟨DW, hDWv, hDW⟩ := hCW E
    obtain ⟨DW', hDWv', hDW'⟩ := hCW' E
    have := hlt (n + 1) DW DW' _ _ hDWv hDWv' hDW hDW'
    rw [hFW, DivisorWithCoeffs.coeff_add, MMP.Flips.coeff_sum_smul_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor]
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith
  set ε := FW.coeff E with hεdef
  -- `F` does not contain `P_W`, so `E ≠ P_W`
  have hCPW : ∀ (Γ : Divisor W), PW.genericPoint ∉ Γ.supp → Γ.coeff PW = 0 := fun Γ hΓ => by
    by_contra hne
    exact hΓ (DivisorWithCoeffs.mem_supp_iff.mpr
      ⟨PW, hne, MMP.Flips.primeDivisor_genericPoint_mem_support PW⟩)
  have hFPW : FW.coeff PW = 0 := by
    rw [hFW, DivisorWithCoeffs.coeff_add, MMP.Flips.coeff_sum_smul_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor]
    simp [hCPW _ (hCP _), hCPW _ (hCP' _)]
  have hEPW : E ≠ PW := by
    rintro rfl
    rw [← hεdef] at hFPW
    linarith
  -- the pull-back of `E` to the model of `G`
  haveI := G.isDominant
  have hgenE : ∀ Z : irreducibleComponents G.Y,
      (G.f ≫ jW) (componentGenericPoint G.Y Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor W) := by
    intro Z hZ
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant, hjWT] at hZ
    obtain ⟨E'', hE'', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    have hE''E : E'' = E := by
      by_contra hne
      exact hE'' (DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hne) _)
    subst hE''E
    exact hEPW (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E'' PW hmem)
  obtain ⟨E₂, hE₂⟩ := hEC.exists_isPullback hgenE
  have hEeff : DivisorWithCoeffs.IsEffective (Finsupp.single E 1 : Divisor W) := by
    intro Γ
    by_cases hΓ : Γ = E
    · rw [hΓ, DivisorWithCoeffs.coeff_single_self]; norm_num
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hΓ)]
  have hcE' : (G.f ≫ jW).base G.E.genericPoint ∈
      (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor W) : Set W) :=
    DivisorWithCoeffs.mem_supp_iff.mpr
        ⟨E, by rw [DivisorWithCoeffs.coeff_single_self]; norm_num, hcE⟩
  have hmem := MMP.Flips.preimage_supp_subset_supp_of_isPullback hEC hEeff hE₂ hcE'
  obtain ⟨E'', hE'', hmemE''⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E'' G.E hmemE''
  have hpbE := MMP.Fourfold.isRCartierPullback_toRDivisor hEC hgenE hE₂
  have hE₂0 := coeff_nonneg_of_isRCartierPullback' (G.f ≫ jW) hpbE
    (fun Γ => by rw [Divisor.coeff_toRDivisor]; exact_mod_cast hEeff Γ) G.E
  rw [Divisor.coeff_toRDivisor] at hE₂0
  have hE₂1 : (1 : ℝ) ≤ (E₂.coeff G.E : ℝ) := by
    have h0 : (0 : ℤ) ≤ E₂.coeff G.E := by exact_mod_cast hE₂0
    have h1 : (1 : ℤ) ≤ E₂.coeff G.E := by
      rcases h0.lt_or_eq with h | h
      · exact h
      · exact absurd h.symm hE''
    exact_mod_cast h1
  -- `F - ε E` is effective, and so is its pull-back
  have hF' : ∀ Γ : Mori.PrimeDivisor W,
      0 ≤ (FW + (-ε) • Divisor.toRDivisor (Finsupp.single E 1 : Divisor W)).coeff Γ := by
    intro Γ
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    by_cases hΓ : Γ = E
    · rw [hΓ, DivisorWithCoeffs.coeff_single_self, ← hεdef]; simp
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hΓ)]
      simpa using hF Γ
  have hpbF' := MMP.Fourfold.isRCartierPullback_add hpbF
    (MMP.Fourfold.isRCartierPullback_smul (-ε) hpbE)
  have hE := coeff_nonneg_of_isRCartierPullback' (G.f ≫ jW) hpbF' hF' G.E
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul, hFG, DivisorWithCoeffs.coeff_add, MMP.Flips.coeff_sum_smul_toRDivisor,
    MMP.Flips.coeff_sum_smul_toRDivisor] at hE
  simp only [neg_mul, Finset.sum_neg_distrib] at hE
  rw [ha₂, ha₂']
  nlinarith

end Monotonicity

end StrictAdjunction

/-- **Log discrepancies strictly increase at a contracted divisor of the stratum.** -/
private theorem logDiscrepancyFn_lt_comap
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) (hcorr : (ι i ≫ f i).base (genericPoint (T i)) =
      (ι (i + 1) ≫ fp i).base (genericPoint (T (i + 1))))
    (ε : (T i).functionField ≃+* (T (i + 1)).functionField)
    (hε : (∀ g, ε ((ι i ≫ f i).stalkMap (genericPoint (T i)) g) =
        ((ι (i + 1) ≫ fp i).stalkMap (genericPoint (T (i + 1))))
          (((Z i).presheaf.stalkCongr (.of_eq hcorr)).hom g)))
    (P : MMP.Mori.PrimeDivisor (T i)) (hP : ∀ Q, (dv Q).comap ε.toRingHom ≠ dv P) :
    logDiscrepancyFn (ι i ≫ sX i) (Δ i) (dv P) <
      logDiscrepancyFn (ι (i + 1) ≫ sX (i + 1)) (Δ (i + 1)) ((dv P).comap ε.symm.toRingHom) := by
  classical
  -- the image of `η_P` in `Z_i` lies outside the common biregular locus of the flip
  have hz := notMem_biregularLocus_of_forall_ne X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S
    hS hSB T ι Δ hι hΔ i hcorr ε hε P hP
  -- the two strata, with their klt structures
  obtain ⟨-, hT0, -, -⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS
    hSB T ι Δ hι hΔ i
  obtain ⟨-, hT1, ⟨m1, K1, hK1, hK1c⟩, -⟩ := adjunction_strata X sX K B Z sZ f fp hK hproj hQ
    hdim hflip hplt S hS hSB T ι Δ hι hΔ (i + 1)
  haveI : LocallyOfFiniteType (ι i ≫ sX i) := hT0.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι (i + 1) ≫ sX (i + 1)) := hT1.1.toLocallyOfFiniteType
  have hZ := (hflip i).isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral (Z i) := hZ.1.toIsIntegral
  have hXn : IsNormalVariety ℂ (sX i) :=
    (hflip i).isNegativeExtremalContraction.isNormalVariety_source
  haveI : LocallyOfFiniteType (sX i) := hXn.1.toLocallyOfFiniteType
  haveI : IsSeparated (sX i) := hXn.1.toIsSeparated
  haveI : QuasiCompact (sX i) := hXn.1.toQuasiCompact
  -- a smooth common model on which every point over the non-isomorphism locus of the flip lies
  -- on a prime divisor with strictly larger log discrepancy over `X_{i+1}`
  obtain ⟨W, _, _, _, r, q, hrb, hqb, hrP, hqP, hc, hWsm, hsupp⟩ :=
    (hflip i).exists_commonModel_lt_of_notMem_biregularLocus (hK i)
  haveI := hrb.isDominant
  haveI := hqb.isDominant
  haveI := hrP
  haveI := hqP
  have hs : r ≫ sX i = q ≫ sX (i + 1) := by
    rw [← (hflip i).isSmall.comp_eq, ← (hflip i).isSmall_flip.comp_eq, ← Category.assoc, hc,
      Category.assoc]
  haveI : AlgebraicGeometry.IsVariety ℂ (r ≫ sX i) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  -- the strict transform of `S` on `W` and its maps to the strata
  obtain ⟨PW, hPWr, hPWq⟩ := exists_primeDivisor_strictTransform (hflip i) (hS i) r q hrb hc
  haveI := PW.integral
  set TW := PW.idealSheaf.subscheme
  set jW := PW.idealSheaf.subschemeι
  have hjW : Set.range jW.base = (PW.support : Set W) := PW.idealSheaf.range_subschemeι
  obtain ⟨pT, hpT⟩ := exists_lift_subschemeι r (ι i) (S i) (hι i) PW hPWr
  obtain ⟨qT, hqT⟩ := exists_lift_subschemeι q (ι (i + 1)) (S (i + 1)) (hι (i + 1)) PW hPWq
  have hjg : jW.base (genericPoint TW) = PW.genericPoint :=
    map_genericPoint_eq_genericPoint jW PW hjW
  have hisor : IsIso (r.stalkMap (jW.base (genericPoint TW))) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus r (by
      rw [hjg, hPWr]
      exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal r hrb
        (S i).coheight_genericPoint.le)
  have hisoq : IsIso (q.stalkMap (jW.base (genericPoint TW))) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus q (by
      rw [hjg, hPWq]
      exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hqb
        (S (i + 1)).coheight_genericPoint.le)
  obtain ⟨hpTP, hpTb⟩ := isProper_isBirationalMorphism_of_comp_eq r (ι i) jW pT hpT
    (by rw [hjg, hPWr, map_genericPoint_eq_genericPoint (ι i) (S i) (hι i)]) hisor
  obtain ⟨hqTP, hqTb⟩ := isProper_isBirationalMorphism_of_comp_eq q (ι (i + 1)) jW qT hqT
    (by rw [hjg, hPWq, map_genericPoint_eq_genericPoint (ι (i + 1)) (S (i + 1)) (hι (i + 1))])
    hisoq
  haveI := hpTP
  haveI := hqTP
  haveI := hpTb.isDominant
  haveI := hqTb.isDominant
  have hpTs : pT ≫ (ι i ≫ sX i) = jW ≫ r ≫ sX i := by
    rw [← Category.assoc, hpT, Category.assoc]
  have hqTs : qT ≫ (ι (i + 1) ≫ sX (i + 1)) = jW ≫ r ≫ sX i := by
    rw [← Category.assoc, hqT, Category.assoc, ← hs]
  obtain ⟨N, ν, hνP, hνb, hN⟩ := exists_normal_model (r ≫ sX i) jW
  haveI := hνP
  -- `qT^* ∘ ε = pT^*`
  obtain ⟨h1, -⟩ := isIso_stalkMap_flip_genericPoint (hflip i) (hS i) (ι i) (ι (i + 1)) (hι i)
    (hι (i + 1))
  have hcomm : qT ≫ (ι (i + 1) ≫ fp i) = pT ≫ (ι i ≫ f i) := by
    rw [← Category.assoc, hqT, Category.assoc, ← hc, ← Category.assoc, ← hpT, Category.assoc]
  have hcompat := functionFieldMap_ringEquiv_apply (ι i ≫ f i) (ι (i + 1) ≫ fp i) pT qT hcomm
    hcorr (surjective_stalkMap_comp (f i) (ι i) _ h1) ε hε
  have hshift : ∀ G : DivisorOver ℂ (jW ≫ r ≫ sX i),
      G.valuation.comap (functionFieldMap qT) =
        (G.valuation.comap (functionFieldMap pT)).comap ε.symm.toRingHom := by
    intro G; ext x
    simp only [Valuation.comap_apply]
    rw [← hcompat]
    simp
  -- `T_i`, `T_W`, `T_{i+1}` have the same dimension
  haveI : AlgebraicGeometry.IsVariety ℂ (jW ≫ r ≫ sX i) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (ι i ≫ sX i) := hT0.1
  haveI : AlgebraicGeometry.IsVariety ℂ (ι (i + 1) ≫ sX (i + 1)) := hT1.1
  have hd0 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι i ≫ sX i)
    (jW ≫ r ≫ sX i) hpTb
  have hd1 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
    (ι (i + 1) ≫ sX (i + 1)) (jW ≫ r ≫ sX i) hqTb
  -- a divisor over `T_i` with the valuation of `P`, and its log discrepancy `1 - coeff_P Δ_i`
  have hdv := logDiscrepancyFn_dv X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB T ι Δ
    hι hΔ i P
  rcases logDiscrepancyFn_cases (ι i ≫ sX i) (Δ i) (dv P) with ⟨n, D, a, ha, hDv, hval⟩ | h2
  swap
  · exfalso; linarith [hdv.1, hdv.2]
  rw [hval]
  obtain ⟨G, D', hD'p, hDG, hD'G⟩ := exists_divisorOver_transfer hT1 pT qT hpTb hqTb hpTs hqTs
    ν hνb hN D
  have hn : (m1 : WithBot ℕ∞) = n := by
    rw [← hK1.topologicalKrullDim_eq, hd1, ← hd0,
      MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha]
  obtain rfl : m1 = n := by exact_mod_cast hn
  obtain ⟨a', ha'⟩ := exists_isLogDiscrepancy_of_isRCartier hT1 hK1 hK1c D' hD'p
  -- the centre of `G` on `W` lies over the image of `η_P` in `Z_i`
  haveI := G.isIntegral
  haveI := G.isLocallyNoetherian
  haveI := G.isNormal
  let Dp : DivisorOver ℂ (ι i ≫ sX i) :=
    { Y := G.Y
      f := G.f ≫ pT
      isNormalVariety := by rw [Category.assoc, hpTs]; exact G.isNormalVariety
      isBirationalMorphism := MMP.Mori.isBirationalMorphism_comp G.isBirationalMorphism hpTb
      E := G.E }
  have hDpv : Dp.valuation = D.valuation := by
    rw [hDG]
    haveI := G.isDominant
    ext t
    change G.E.divisorialValuation (functionFieldMap (G.f ≫ pT) t) =
      G.E.divisorialValuation (functionFieldMap G.f (functionFieldMap pT t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hDP : D.f D.E.genericPoint = P.genericPoint := by
    have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hT0.1
      (D := D) (D' := DivisorOver.ofPrimeDivisor ℂ hT0 P)
      (by rw [hDv, valuation_ofPrimeDivisor_eq_dv])
    exact this
  have hcen : (r ≫ f i).base ((G.f ≫ jW).base G.E.genericPoint) =
      (ι i ≫ f i).base P.genericPoint := by
    have e1 : (G.f ≫ jW) ≫ r ≫ f i = (G.f ≫ pT) ≫ ι i ≫ f i := by
      simp only [Category.assoc]; rw [← Category.assoc pT, hpT, Category.assoc]
    have e2 := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hT0.1 hDpv
    change ((G.f ≫ jW) ≫ r ≫ f i).base G.E.genericPoint = _
    rw [e1, Scheme.Hom.comp_apply]
    change (ι i ≫ f i).base (Dp.f Dp.E.genericPoint) = _
    rw [e2, hDP]
  obtain ⟨E, hcE, hE⟩ := hsupp _ (by rw [hcen]; exact not_and_or.mp hz)
  -- the strict comparison of adjunction along `E`
  have hXn' : IsNormalVariety ℂ (sX (i + 1)) := ⟨(hflip i).isSmall_flip.isVariety_source,
    inferInstance⟩
  haveI : LocallyOfFiniteType (sX (i + 1)) := hXn'.1.toLocallyOfFiniteType
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace r
  have hsum : ∀ j, Finsupp.single (S j) (1 : ℝ) + (B j - Finsupp.single (S j) 1) = B j :=
    fun j => by abel
  have hdim' : ∀ j, topologicalKrullDim (X j) = ((3 : ℕ) : WithBot ℕ∞) + 1 := fun j => by
    rw [hdim j]; norm_num
  have hlt : a < a' := by
    refine isLogDiscrepancy_lt_of_nonpositive_diagram (sX i) hXn (hdim' i) (S i)
      (B i - Finsupp.single (S i) 1) (ι i) (hι i) (Δ i)
      (fun τ hτ hτS ρ hρ => by rw [add_assoc, hsum]; exact hΔ i τ hτ hτS ρ hρ)
      (sX (i + 1)) hXn' (hdim' (i + 1)) (S (i + 1)) (B (i + 1) - Finsupp.single (S (i + 1)) 1)
      (ι (i + 1)) (hι (i + 1)) (Δ (i + 1))
      (fun τ hτ hτS ρ hρ => by rw [add_assoc, hsum]; exact hΔ (i + 1) τ hτ hτS ρ hρ)
      r q hs hrP hqP hrb hqb
      (fun E' m D D' a a' h1 h2 h3 h4 => isLogDiscrepancy_le_of_comp_eq (hflip i) (hK i) r q hc
        E' m D D' a a' h1 h2 (by rwa [hsum] at h3) (by rwa [hsum] at h4))
      PW hPWr hPWq jW hjW pT qT hpT hqT G D D' hDG hD'G m1 a a' ha ha' E
      (MMP.Fourfold.isCartier_of_isSmoothScheme hWsm _) hcE
      (fun m D D' a a' h1 h2 h3 h4 => hE m D D' a a' h1 h2 (by rwa [hsum] at h3)
        (by rwa [hsum] at h4))
  have hD'w : D'.valuation = (dv P).comap ε.symm.toRingHom := by
    rw [hD'G, hshift, ← hDG, hDv]
  rw [← hD'w, logDiscrepancyFn_eq ha']
  exact hlt

/-- **One flip on the strata.** The flip identifies `k(T_i)` with `k(T_{i+1})` by a field
isomorphism `ε` under which every induced birational map `φ : T_i ⤏ T_{i+1}` sends `P` to `Q`
exactly when `ord_Q ∘ ε = ord_P`; log discrepancies do not decrease, and strictly increase at a
divisor of `T_i` which is not a divisor of `T_{i+1}`. -/
private theorem exists_stepEquiv
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i))
    (i : ℕ) :
    ∃ ε : (T i).functionField ≃+* (T (i + 1)).functionField,
      (∀ φ : (T i).RationalMap (T (i + 1)), MMP.Mori.RationalMap.IsBirational φ →
        φ.compHom (ι (i + 1) ≫ fp i) = (ι i ≫ f i).toRationalMap →
        ∀ P Q, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ↔
          (dv Q).comap ε.toRingHom = dv P) ∧
      (∀ w, logDiscrepancyFn (ι i ≫ sX i) (Δ i) w ≤
        logDiscrepancyFn (ι (i + 1) ≫ sX (i + 1)) (Δ (i + 1)) (w.comap ε.symm.toRingHom)) ∧
      ∀ P, (∀ Q, (dv Q).comap ε.toRingHom ≠ dv P) →
        logDiscrepancyFn (ι i ≫ sX i) (Δ i) (dv P) <
          logDiscrepancyFn (ι (i + 1) ≫ sX (i + 1)) (Δ (i + 1))
              ((dv P).comap ε.symm.toRingHom) := by
  haveI : IsSeparated (sZ i) :=
    (hflip i).isNegativeExtremalContraction.isNormalVariety_target.1.toIsSeparated
  haveI := isSeparated_terminal (sZ i)
  have hcorr := map_genericPoint_eq_of_flipTransformPrimeDivisor (hS i) (ι i) (ι (i + 1)) (hι i)
    (hι (i + 1))
  obtain ⟨ε, hε, htr⟩ := exists_stepEquiv_compat (hflip i) (hS i) (ι i) (ι (i + 1))
    (hι i) (hι (i + 1)) hcorr
  exact ⟨ε, htr, logDiscrepancyFn_le_comap X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB
      T ι Δ hι hΔ i hcorr ε hε,
    fun P hP => logDiscrepancyFn_lt_comap X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB T
        ι Δ hι hΔ i hcorr ε hε P hP⟩

/-- The identifications `k(T_0) ≅ k(T_i)` composed from the one-step identifications. -/
private noncomputable def chainEquiv {T : ℕ → Scheme.{0}} [∀ i, IsIntegral (T i)]
    (ε : ∀ i, (T i).functionField ≃+* (T (i + 1)).functionField) :
    ∀ i, (T 0).functionField ≃+* (T i).functionField
  | 0 => RingEquiv.refl _
  | i + 1 => (chainEquiv ε i).trans (ε i)

/-- The geometric inputs: prime divisors of the strata `T_i` define valuations `val i P` of one
function field, with log discrepancies `A i v` satisfying the hypotheses of
`eventually_mem_and_eq_of_isWF`, and the induced maps `φ : T_i ⤏ T_{i+1}` send `P` to `Q`
exactly when `val i P = val (i + 1) Q`. -/
private theorem exists_stratumValuations
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i)) :
    ∃ (V : Type) (val : ∀ i, MMP.Mori.PrimeDivisor (T i) → V) (A : ℕ → V → ℝ) (W : Set ℝ),
      W.IsWF ∧
      (∀ i P, A i (val i P) = 1 - (Δ i).coeff P) ∧
      (∀ i v, A i v ≤ A (i + 1) v) ∧
      (∀ i v, (∃ P, val i P = v) → A i v ≤ 1) ∧
      (∀ i v, (∃ P, val i P = v) → 1 - A i v ∈ W) ∧
      (∀ i v, (∃ P, val i P = v) → ¬ (∃ Q, val (i + 1) Q = v) → A i v < A (i + 1) v) ∧
      {v | A 0 v < 1 ∨ (¬ (∃ P, val 0 P = v) ∧ A 0 v ≤ 1)}.Finite ∧
      ∀ i (φ : (T i).RationalMap (T (i + 1))), MMP.Mori.RationalMap.IsBirational φ →
        φ.compHom (ι (i + 1) ≫ fp i) = (ι i ≫ f i).toRationalMap →
        ∀ P Q, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q ↔
          val (i + 1) Q = val i P := by
  choose ε htr hmono hstrict using exists_stepEquiv X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt
      S hS hSB T ι Δ hι hΔ
  have hdv := logDiscrepancyFn_dv X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB T ι
      Δ hι hΔ
  obtain ⟨W, hW, hWc⟩ := exists_isWF_coeff X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS hSB
      T ι Δ hι hΔ
  have hfin := finite_logDiscrepancyFn_le_one X sX K B Z sZ f fp hK hproj hQ hdim hflip hplt S hS
      hSB T ι Δ hι hΔ
  let e := chainEquiv ε
  let val : ∀ i, MMP.Mori.PrimeDivisor (T i) → Valuation (T 0).functionField ℤᵐ⁰ :=
    fun i P => (dv P).comap (e i).toRingHom
  let A : ℕ → Valuation (T 0).functionField ℤᵐ⁰ → ℝ :=
    fun i v => logDiscrepancyFn (ι i ≫ sX i) (Δ i) (v.comap (e i).symm.toRingHom)
  have hA : ∀ i P, A i (val i P) = 1 - (Δ i).coeff P := fun i P => by
    simpa only [A, val, comap_comap_symm] using (hdv i P).1
  have hval : ∀ i P Q, val (i + 1) Q = val i P ↔ (dv Q).comap (ε i).toRingHom = dv P := by
    refine fun i P Q => ⟨fun h => comap_injective (e i) h, fun h => ?_⟩
    change (dv Q).comap ((e i).trans (ε i)).toRingHom = (dv P).comap (e i).toRingHom
    rw [← h]
    rfl
  have he0 : ∀ v : Valuation (T 0).functionField ℤᵐ⁰, v.comap (e 0).symm.toRingHom = v := by
    intro v; ext x; rfl
  have hcomp : ∀ i (v : Valuation (T 0).functionField ℤᵐ⁰), v.comap (e (i + 1)).symm.toRingHom =
      (v.comap (e i).symm.toRingHom).comap (ε i).symm.toRingHom := fun i v => by ext x; rfl
  refine ⟨Valuation (T 0).functionField ℤᵐ⁰, val, A, W, hW, hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v
    have := hmono i (v.comap (e i).symm.toRingHom)
    simp only [A]; rw [hcomp]; exact this
  · rintro i v ⟨P, rfl⟩
    rw [hA]; linarith [(hdv i P).2]
  · rintro i v ⟨P, rfl⟩
    rw [hA, sub_sub_cancel]; exact hWc i P
  · rintro i v ⟨P, rfl⟩ hQ
    have hQ' : ∀ Q, (dv Q).comap (ε i).toRingHom ≠ dv P := fun Q h =>
      hQ ⟨Q, (hval i P Q).mpr h⟩
    have := hstrict i P hQ'
    simp only [A, val]; rw [hcomp, comap_comap_symm]; exact this
  · refine (hfin.preimage (f := fun v => v.comap (e 0).symm.toRingHom) ?_).subset ?_
    · intro v _ v' _ h; simpa only [he0] using h
    · intro v hv
      simp only [Set.mem_setOf_eq, he0] at hv ⊢
      rcases hv with hv | ⟨hv, hv'⟩
      · exact Or.inl hv
      · refine Or.inr ⟨fun P hP => hv ⟨P, ?_⟩, hv'⟩
        simp only [val, ← hP]; ext x; rfl
  · intro i φ hφ hcomp P Q
    rw [htr i φ hφ hcomp P Q, hval]

end Geometry

end MMP.RealPltStratumDivisorsStabilize

namespace MMP.Fourfold

open MMP.Mori

/-- **Prime extraction and different coefficients stabilize in a sequence of real plt flips.**
Let `X_i ⟶ Z_i ⟵ X_{i+1}` be an infinite sequence of real flips of globally projective
`ℚ`-factorial complex fourfolds `(X_i, B_i)` with canonical divisors `K_i`, each pair being plt,
`B_{i+1}` the strict transform of `B_i` (`MMP.Fourfold.IsRealFlipStep`). Let `S_i` be prime
divisors of coefficient one in `B_i` with `S_{i+1}` the strict transform of `S_i`, and
`ι_i : T_i ⟶ X_i` normal closed subschemes with support `S_i` carrying the real adjunction
boundaries `Δ_i`: `div(ρ) + Δ_i = (div(τ) + B_i)|_{T_i}` for every rational top form `τ` on `X_i`
with `ord_{S_i} τ = -1` and Poincaré residue `ρ` of `τ` along `T_i`. Then there is `N` such that
for every `i ≥ N` and the birational map `φ : T_i ⤏ T_{i+1}` induced by the flip, `φ` extracts no
prime divisor, and the coefficients of `Δ_i` at `P` and of `Δ_{i+1}` at `φ(P)` agree. -/
@[mmp "lem_fourfold_real_plt_stratum_divisors_stabilize"]
public theorem eventually_realPltFlip_stratum_divisors_stabilize
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (hSB : ∀ i, (B i).coeff (S i) = 1)
    (T : ℕ → Scheme.{0}) [∀ i, IsIntegral (T i)] [∀ i, IsLocallyNoetherian (T i)]
    [∀ i, CompactSpace (T i)] [∀ i, IsNormal (T i)] (ι : ∀ i, T i ⟶ X i)
    [∀ i, IsClosedImmersion (ι i)]
    (Δ : ∀ i, RDivisor (T i))
    (hι : ∀ i, Set.range (ι i).base = ((S i).support : Set (X i)))
    (hΔ : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι i ≫ sX i) 3 1, IsPoincareResidue (sX i) (ι i) 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback (ι i) (Divisor.toRDivisor (divisorOfForm τ) + B i)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ i)) :
    ∃ N : ℕ, ∀ i, N ≤ i → ∀ φ : (T i).RationalMap (T (i + 1)),
      MMP.Mori.RationalMap.IsBirational φ →
      φ.compHom (ι (i + 1) ≫ fp i) = (ι i ≫ f i).toRationalMap →
      (∀ Q : MMP.Mori.PrimeDivisor (T (i + 1)),
        ∃ P : MMP.Mori.PrimeDivisor (T i),
          MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q) ∧
      ∀ (P : MMP.Mori.PrimeDivisor (T i)) (Q : MMP.Mori.PrimeDivisor (T (i + 1))),
        MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q →
          (Δ i).coeff P = (Δ (i + 1)).coeff Q := by
  obtain ⟨V, val, A, W, hW, hval, hmono, hle, hcoeff, hstrict, hfin, htr⟩ :=
    MMP.RealPltStratumDivisorsStabilize.exists_stratumValuations X sX K B Z sZ f fp hK hproj hQ
      hdim hflip hplt S hS hSB T ι Δ hι hΔ
  obtain ⟨N, hN⟩ := MMP.RealPltStratumDivisorsStabilize.eventually_mem_and_eq_of_isWF
    (fun i v => ∃ P, val i P = v) A hW hmono hle hcoeff hstrict hfin
  refine ⟨N, fun i hi φ hφ hcomp => ⟨fun Q => ?_, fun P Q hPQ => ?_⟩⟩
  · obtain ⟨⟨P, hP⟩, -⟩ := hN i hi (val (i + 1) Q) ⟨Q, rfl⟩
    exact ⟨P, (htr i φ hφ hcomp P Q).mpr hP.symm⟩
  · have hv := (htr i φ hφ hcomp P Q).mp hPQ
    obtain ⟨-, hA⟩ := hN i hi (val (i + 1) Q) ⟨Q, rfl⟩
    rw [hv, hval, ← hv, hval] at hA
    linarith

end MMP.Fourfold
