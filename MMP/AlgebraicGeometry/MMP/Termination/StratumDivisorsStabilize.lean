module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumAvoidsFlip
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.MMP.Termination.StrataEventuallyBirational
import MMP.AlgebraicGeometry.MMP.Termination.StratumDifficultyFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumDiscrepancyMonotone
import MMP.AlgebraicGeometry.MMP.Termination.StratumDiscrepancyStrict
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.Adjunction.HyperstandardStratumCoefficients
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal

/-!
# Divisors on corresponding dlt strata stabilize along a sequence of flips

Along a sequence of flips of projective dlt pairs, take corresponding adjunction pairs on a
stratum of dimension at most `d` whose lower-dimensional boundary strata miss the flipping loci.
After finitely many steps no prime divisor of the stratum is contracted, and corresponding prime
divisors have equal coefficients
(`MMP.Fourfold.exists_forall_ge_isStratumAdjunctionPair_coeff_eq`).
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Fourfold

namespace MMP.Fourfold.StratumDivisorsStabilize

/-! ### Measures that drop finitely often -/

/-- Along a sequence, a measure in a well-founded order that never increases from `N` on and
drops strictly at every index where `p` holds: then `p` fails from some index on. -/
private theorem exists_forall_ge_not_of_lt {β : Type*} [Preorder β] [WellFoundedLT β]
    (μ : ℕ → β) (p : ℕ → Prop) {N : ℕ} (hle : ∀ i ≥ N, μ (i + 1) ≤ μ i)
    (hlt : ∀ i ≥ N, p i → μ (i + 1) < μ i) : ∃ M, ∀ i ≥ M, ¬ p i := by
  have hmono : ∀ M ≥ N, ∀ i ≥ M, μ i ≤ μ M := by
    intro M hM i hi
    induction i, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hle j (hM.trans hj)).trans ih
  suffices H : ∀ b : β, ∀ M ≥ N, μ M = b → ∃ M', ∀ i ≥ M', ¬ p i from H _ N le_rfl rfl
  intro b
  induction b using WellFoundedLT.induction with
  | _ b ih =>
    intro M hM hb
    by_contra h
    push Not at h
    obtain ⟨i, hi, hpi⟩ := h M
    have hlt' : μ (i + 1) < b := hb ▸ (hlt i (hM.trans hi) hpi).trans_le (hmono M hM i hi)
    obtain ⟨M', hM'⟩ := ih _ hlt' (i + 1) (by omega) rfl
    obtain ⟨j, hj, hpj⟩ := h M'
    exact hM' j hj hpj

/-- The rank of `x` in `D`: the number of elements of `D` at most `x`. -/
private noncomputable def coeffRank (D : Set ℚ) (x : ℚ) : ℕ := {y ∈ D | y ≤ x}.ncard

private theorem coeffRank_mono {D : Set ℚ} (hD : ∀ x < 1, {y ∈ D | y ≤ x}.Finite) {x y : ℚ}
    (hxy : x ≤ y) (hy : y < 1) : coeffRank D x ≤ coeffRank D y :=
  Set.ncard_le_ncard (fun _ hz => ⟨hz.1, hz.2.trans hxy⟩) (hD y hy)

private theorem coeffRank_lt {D : Set ℚ} (hD : ∀ x < 1, {y ∈ D | y ≤ x}.Finite) {x y : ℚ}
    (hxy : x < y) (hyD : y ∈ D) (hy : y < 1) : coeffRank D x < coeffRank D y :=
  Set.ncard_lt_ncard ⟨fun _ hz => ⟨hz.1, hz.2.trans hxy.le⟩,
    fun h => (not_le.2 hxy) (h ⟨hyD, le_rfl⟩).2⟩ (hD y hy)

private theorem coeffRank_pos {D : Set ℚ} (hD : ∀ x < 1, {y ∈ D | y ≤ x}.Finite) {y : ℚ}
    (hyD : y ∈ D) (hy : y < 1) : 0 < coeffRank D y :=
  (Set.ncard_pos (hD y hy)).2 ⟨y, hyD, le_rfl⟩

open Classical in
/-- The measure of a coefficient function: the number of coefficients equal to one, then the sum
of the ranks of the nonzero coefficients below one. -/
private noncomputable def coeffMeasure {α : Type*} (D : Set ℚ) (c : α →₀ ℚ) : ℕ ×ₗ ℕ :=
  toLex ((c.support.filter (fun P => c P = 1)).card,
    ∑ P ∈ c.support.filter (fun P => c P < 1), coeffRank D (c P))

open Classical in
/-- **Counting the floors.** If every coefficient-one element of `c'` corresponds to a
coefficient-one element of `c`, the correspondence being injective, then `c'` has at most as many
coefficients equal to one as `c`, and when the numbers agree every coefficient-one element of `c`
corresponds to a coefficient-one element of `c'`. -/
private theorem card_filter_eq_one_le_and {α α' : Type*} (c : α →₀ ℚ) (c' : α' →₀ ℚ)
    (R : α → α' → Prop) (hr : ∀ P P' Q', R P P' → R P Q' → P' = Q')
    (hex : ∀ P', c' P' = 1 → ∃ P, c P = 1 ∧ R P P') :
    (c'.support.filter (fun P' => c' P' = 1)).card ≤ (c.support.filter (fun P => c P = 1)).card ∧
      ((c'.support.filter (fun P' => c' P' = 1)).card =
          (c.support.filter (fun P => c P = 1)).card →
        ∀ P, c P = 1 → ∃ P', c' P' = 1 ∧ R P P') := by
  set O := c.support.filter (fun P => c P = 1) with hO
  set O' := c'.support.filter (fun P' => c' P' = 1) with hO'
  have hmem : ∀ P', P' ∈ O' ↔ c' P' = 1 := fun P' => by
    rw [hO', Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ one_ne_zero, h⟩⟩
  have hmemO : ∀ P, P ∈ O ↔ c P = 1 := fun P => by
    rw [hO, Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ one_ne_zero, h⟩⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · have hO'e : O' = ∅ := Finset.eq_empty_of_forall_notMem fun P' hP' =>
      hα.elim (hex P' ((hmem P').1 hP')).choose
    refine ⟨by simp [hO'e], fun _ P => hα.elim P⟩
  let g : α' → α := fun P' => if h : c' P' = 1 then (hex P' h).choose else Classical.arbitrary α
  have hg : ∀ P' ∈ O', c (g P') = 1 ∧ R (g P') P' := fun P' hP' => by
    have h := (hmem P').1 hP'
    simp only [g, dif_pos h]
    exact (hex P' h).choose_spec
  have hgO : ∀ P' ∈ O', g P' ∈ O := fun P' hP' => (hmemO _).2 (hg P' hP').1
  have hginj : Set.InjOn g O' := fun P' hP' Q' hQ' h =>
    hr _ _ _ (hg P' hP').2 (h ▸ (hg Q' hQ').2)
  refine ⟨Finset.card_le_card_of_injOn g hgO hginj, fun heq P hP => ?_⟩
  have himO : O'.image g = O :=
    Finset.eq_of_subset_of_card_le (fun P hP => by
        obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
        exact hgO P' hP')
      (by rw [Finset.card_image_of_injOn hginj]; exact heq.ge)
  obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 (himO ▸ (hmemO P).2 hP)
  exact ⟨P', (hmem P').1 hP', (hg P' hP').2⟩

open Classical in
private theorem coeffMeasure_le_and {α α' : Type*} {D : Set ℚ} (hD1 : ∀ x ∈ D, x ≤ 1)
    (hD : ∀ x < 1, {y ∈ D | y ≤ x}.Finite) (c : α →₀ ℚ) (c' : α' →₀ ℚ) (R : α → α' → Prop)
    (hmem : ∀ P, c P ∈ D) (hnn : ∀ P, 0 ≤ c P) (hnn' : ∀ P', 0 ≤ c' P')
    (hl : ∀ P Q P', R P P' → R Q P' → P = Q) (hr : ∀ P P' Q', R P P' → R P Q' → P' = Q')
    (hle : ∀ P P', R P P' → c' P' ≤ c P) (hex : ∀ P', c' P' ≠ 0 → ∃ P, R P P') :
    coeffMeasure D c' ≤ coeffMeasure D c ∧
      ((∃ P P', R P P' ∧ c' P' ≠ c P) → coeffMeasure D c' < coeffMeasure D c) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · have hc' : c' = 0 := by
      ext P'
      by_contra h
      exact hα.elim (hex P' h).choose
    refine ⟨?_, fun ⟨P, _, _⟩ => hα.elim P⟩
    simp only [coeffMeasure, hc', Finsupp.support_zero, Finset.filter_empty, Finset.card_empty,
      Finset.sum_empty]
    exact Prod.Lex.toLex_le_toLex.2 (by
      rcases Nat.eq_zero_or_pos (c.support.filter (fun P => c P = 1)).card with h | h
      · exact Or.inr ⟨h.symm, Nat.zero_le _⟩
      · exact Or.inl h)
  -- the partner map on the support of `c'`
  let g : α' → α := fun P' => if h : c' P' ≠ 0 then (hex P' h).choose else Classical.arbitrary α
  have hg : ∀ P' ∈ c'.support, R (g P') P' := fun P' hP' => by
    have h : c' P' ≠ 0 := Finsupp.mem_support_iff.1 hP'
    simp only [g, dif_pos h]
    exact (hex P' h).choose_spec
  have hgle : ∀ P' ∈ c'.support, c' P' ≤ c (g P') := fun P' hP' => hle _ _ (hg P' hP')
  have hgA : ∀ P' ∈ c'.support, g P' ∈ c.support := fun P' hP' => by
    refine Finsupp.mem_support_iff.2 (ne_of_gt ?_)
    exact lt_of_lt_of_le (lt_of_le_of_ne (hnn' P') (Ne.symm (Finsupp.mem_support_iff.1 hP')))
      (hgle P' hP')
  have hginj : Set.InjOn g c'.support := fun P' hP' Q' hQ' h =>
    hr _ _ _ (hg P' hP') (h ▸ hg Q' hQ')
  have hfl := card_filter_eq_one_le_and c c' R hr fun P' h1 => by
    obtain ⟨P, hP⟩ := hex P' (h1 ▸ one_ne_zero)
    exact ⟨P, le_antisymm (hD1 _ (hmem P)) (h1 ▸ hle P P' hP), hP⟩
  set O := c.support.filter (fun P => c P = 1) with hO
  set L := c.support.filter (fun P => c P < 1) with hL
  set O' := c'.support.filter (fun P => c' P = 1) with hO'
  set L' := c'.support.filter (fun P => c' P < 1) with hL'
  have hL'A : ∀ P' ∈ L', P' ∈ c'.support := fun P' h => (Finset.mem_filter.1 h).1
  have hm : ∀ {a b a' b' : ℕ}, a' < a → toLex (a', b') < toLex (a, b) :=
    fun h => Prod.Lex.toLex_lt_toLex.2 (Or.inl h)
  rcases lt_or_eq_of_le hfl.1 with hlt | heq
  · exact ⟨(hm hlt).le, fun _ => hm hlt⟩
  -- the coefficient-one components correspond, so a partner of a coefficient below one is below
  -- one
  have hlt1 : ∀ P P', R P P' → c' P' < 1 → c P < 1 := fun P P' hPP' h1 =>
    lt_of_le_of_ne (hD1 _ (hmem P)) fun h => by
      obtain ⟨Q', hQ'1, hQ'⟩ := hfl.2 heq P h
      rw [hr _ _ _ hPP' hQ'] at h1
      exact h1.ne hQ'1
  have hgL : ∀ P' ∈ L', g P' ∈ L := fun P' hP' => by
    obtain ⟨hA, h1⟩ := Finset.mem_filter.1 hP'
    exact Finset.mem_filter.2 ⟨hgA P' hA, hlt1 _ _ (hg P' hA) h1⟩
  have hLinj : Set.InjOn g L' := hginj.mono fun P' h => hL'A P' h
  have hrank : ∀ P' ∈ L', coeffRank D (c' P') ≤ coeffRank D (c (g P')) := fun P' hP' =>
    coeffRank_mono hD (hgle P' (hL'A P' hP')) (Finset.mem_filter.1 (hgL P' hP')).2
  have hsub : L'.image g ⊆ L := fun P hP => by
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
    exact hgL P' hP'
  have hs1 : ∑ P' ∈ L', coeffRank D (c' P') ≤ ∑ P' ∈ L', coeffRank D (c (g P')) :=
    Finset.sum_le_sum hrank
  have hs2 : ∑ P' ∈ L', coeffRank D (c (g P')) = ∑ P ∈ L'.image g, coeffRank D (c P) :=
    (Finset.sum_image (f := fun P => coeffRank D (c P)) fun _ hx _ hy h => hLinj hx hy h).symm
  have hs3 : ∑ P ∈ L'.image g, coeffRank D (c P) ≤ ∑ P ∈ L, coeffRank D (c P) :=
    Finset.sum_le_sum_of_subset hsub
  have hfst : ∀ {b b' : ℕ}, b' ≤ b → toLex (O'.card, b') ≤ toLex (O.card, b) :=
    fun h => Prod.Lex.toLex_le_toLex.2 (Or.inr ⟨heq, h⟩)
  have hfst' : ∀ {b b' : ℕ}, b' < b → toLex (O'.card, b') < toLex (O.card, b) :=
    fun h => Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨heq, h⟩)
  refine ⟨hfst (hs1.trans (hs2.le.trans hs3)), ?_⟩
  rintro ⟨P, P', hPP', hne⟩
  have hlt : c' P' < c P := lt_of_le_of_ne (hle P P' hPP') hne
  have hPA : P ∈ c.support :=
    Finsupp.mem_support_iff.2 (ne_of_gt (lt_of_le_of_lt (hnn' P') hlt))
  have hP1 : c P < 1 := hlt1 P P' hPP' (hlt.trans_le (hD1 _ (hmem P)))
  have hPL : P ∈ L := Finset.mem_filter.2 ⟨hPA, hP1⟩
  refine hfst' ?_
  by_cases h0 : c' P' = 0
  · -- `P` disappears from the support
    have hnot : P ∉ L'.image g := fun hP => by
      obtain ⟨Q', hQ', hQ'g⟩ := Finset.mem_image.1 hP
      obtain rfl := hr _ _ _ hPP' (hQ'g ▸ hg Q' (hL'A Q' hQ'))
      exact Finsupp.mem_support_iff.1 (hL'A _ hQ') h0
    have hs3' : ∑ P ∈ L'.image g, coeffRank D (c P) < ∑ P ∈ L, coeffRank D (c P) :=
      Finset.sum_lt_sum_of_subset hsub hPL hnot (coeffRank_pos hD (hmem P) hP1)
        (fun _ _ _ => Nat.zero_le _)
    exact lt_of_le_of_lt (hs1.trans hs2.le) hs3'
  · -- `P'` is the partner of `P` and its rank drops
    have hP'A : P' ∈ c'.support := Finsupp.mem_support_iff.2 h0
    have hP'L : P' ∈ L' := Finset.mem_filter.2 ⟨hP'A, hlt.trans hP1⟩
    have hgP : g P' = P := hl _ _ _ (hg P' hP'A) hPP'
    have hs1' : ∑ P' ∈ L', coeffRank D (c' P') < ∑ P' ∈ L', coeffRank D (c (g P')) :=
      Finset.sum_lt_sum hrank ⟨P', hP'L, hgP ▸ coeffRank_lt hD hlt (hmem P) hP1⟩
    exact lt_of_lt_of_le hs1' (hs2.le.trans hs3)

/-- **Stabilization of coefficients.** -/
private theorem exists_forall_ge_coeff_eq {α : ℕ → Type*} (c : ∀ i, α i →₀ ℚ)
    (R : ∀ i, α i → α (i + 1) → Prop) {D : Set ℚ} (hD1 : ∀ x ∈ D, x ≤ 1)
    (hD : ∀ x < 1, {y ∈ D | y ≤ x}.Finite) (hmem : ∀ i P, c i P ∈ D)
    (hnn : ∀ i P, 0 ≤ c i P) {N : ℕ}
    (hl : ∀ i ≥ N, ∀ P Q P', R i P P' → R i Q P' → P = Q)
    (hr : ∀ i ≥ N, ∀ P P' Q', R i P P' → R i P Q' → P' = Q')
    (hle : ∀ i ≥ N, ∀ P P', R i P P' → c (i + 1) P' ≤ c i P)
    (hex : ∀ i ≥ N, ∀ P', c (i + 1) P' ≠ 0 → ∃ P, R i P P') :
    ∃ M, ∀ i ≥ M, ∀ P P', R i P P' → c (i + 1) P' = c i P := by
  have key := fun i (hi : i ≥ N) => coeffMeasure_le_and hD1 hD (c i) (c (i + 1)) (R i)
    (hmem i) (hnn i) (hnn (i + 1)) (hl i hi) (hr i hi) (hle i hi) (hex i hi)
  obtain ⟨M, hM⟩ := exists_forall_ge_not_of_lt (fun i => coeffMeasure D (c i))
    (fun i => ∃ P P', R i P P' ∧ c (i + 1) P' ≠ c i P) (N := N) (fun i hi => (key i hi).1)
    (fun i hi => (key i hi).2)
  exact ⟨M, fun i hi P P' hPP' => of_not_not fun h => hM i hi ⟨P, P', hPP', h⟩⟩

/-! ### The coefficient set -/

open Classical in
/-- The coefficient of `E` in the linear extension of a partial map `φ` of prime divisors is the
sum of the coefficients of the components that `φ` sends to `E`. -/
private theorem mapPrimeDivisors_apply_eq_sum {X Y : Scheme.{0}}
    (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)) (D : DivisorWithCoeffs ℚ X)
    (E : Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.mapPrimeDivisors φ D E = ∑ P ∈ D.support.filter (fun P => φ P = some E), D P := by
  classical
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.finset_sum_apply,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  rcases h : φ P with _ | E'
  · simp
  · by_cases hE : E' = E
    · subst hE
      simp
    · simp [Finsupp.single_apply, hE]

/-- If every coefficient of `D` is a sum of weights over a set `τ E ⊆ s`, these sets being pairwise
disjoint, the same holds for the linear extension of a partial map of prime divisors. -/
private theorem exists_eq_sum_mapPrimeDivisors {ι : Type*} {X Y : Scheme.{0}} (w : ι → ℚ)
    (s : Finset ι) (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)) (D : DivisorWithCoeffs ℚ X)
    (τ : Mori.PrimeDivisor X → Finset ι) (hτs : ∀ E, τ E ⊆ s)
    (hτ : ∀ E E', E ≠ E' → Disjoint (τ E) (τ E')) (hD : ∀ E, D E = ∑ j ∈ τ E, w j) :
    ∃ τ' : Mori.PrimeDivisor Y → Finset ι, (∀ E, τ' E ⊆ s) ∧
      (∀ E E', E ≠ E' → Disjoint (τ' E) (τ' E')) ∧
      ∀ E, DivisorWithCoeffs.mapPrimeDivisors φ D E = ∑ j ∈ τ' E, w j := by
  classical
  refine ⟨fun E => (D.support.filter (fun P => φ P = some E)).biUnion τ, fun E => ?_,
    fun E E' hne => ?_, fun E => ?_⟩
  · exact Finset.biUnion_subset.2 fun P _ => hτs P
  · rw [Finset.disjoint_biUnion_left]
    intro P hP
    rw [Finset.disjoint_biUnion_right]
    intro Q hQ
    refine hτ P Q fun hPQ => hne ?_
    subst hPQ
    exact Option.some_injective _ ((Finset.mem_filter.1 hP).2.symm.trans (Finset.mem_filter.1 hQ).2)
  · rw [mapPrimeDivisors_apply_eq_sum, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun P _ => hD P
    · exact fun P _ Q _ hPQ => hτ P Q hPQ

open Classical in
/-- Along a sequence of birational transforms `B_{i+1} = (f_i⁺)⁻¹_* f_{i*} B_i` of divisors with
coefficients in `[0, 1]`, there is a finite set `I ⊆ (0, 1]` containing `1` and every nonzero
coefficient of every `B_i`: the sums in `(0, 1]` of coefficients of `B_0`. -/
private theorem exists_finset_coeff_mem {X Z : ℕ → Scheme.{0}} {f : ∀ i, X i ⟶ Z i}
    {fp : ∀ i, X (i + 1) ⟶ Z i} {B : ∀ i, QDivisor (X i)}
    (hB01 : ∀ i P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1)
    (hBflip : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i)) :
    ∃ I : Finset ℚ, (∀ b ∈ I, 0 < b ∧ b ≤ 1) ∧ (1 : ℚ) ∈ I ∧
      ∀ i P, (B i).coeff P ≠ 0 → (B i).coeff P ∈ I := by
  have hrep : ∀ i, ∃ τ : Mori.PrimeDivisor (X i) → Finset (Mori.PrimeDivisor (X 0)),
      (∀ E, τ E ⊆ (B 0).support) ∧ (∀ E E', E ≠ E' → Disjoint (τ E) (τ E')) ∧
        ∀ E, B i E = ∑ j ∈ τ E, B 0 j := by
    intro i
    induction i with
    | zero =>
      refine ⟨fun E => if E ∈ (B 0).support then {E} else ∅, fun E => ?_, fun E E' hne => ?_,
        fun E => ?_⟩
      · beta_reduce
        split_ifs with h
        · exact Finset.singleton_subset_iff.2 h
        · exact Finset.empty_subset _
      · beta_reduce
        split_ifs <;> simp [hne]
      · beta_reduce
        split_ifs with h
        · simp
        · simpa using h
    | succ i ih =>
      obtain ⟨τ, hτs, hτ, hτB⟩ := ih
      obtain ⟨τ₁, hτ₁s, hτ₁, hτ₁B⟩ := exists_eq_sum_mapPrimeDivisors (B 0) (B 0).support
        (RationalMap.transformPrimeDivisor (X := X i) (f i).toRationalMap) (B i) τ hτs hτ hτB
      obtain ⟨τ₂, hτ₂s, hτ₂, hτ₂B⟩ := exists_eq_sum_mapPrimeDivisors (B 0) (B 0).support
        (inverseTransformPrimeDivisor (fp i)) _ τ₁ hτ₁s hτ₁ hτ₁B
      exact ⟨τ₂, hτ₂s, hτ₂, fun E => by rw [hBflip i]; exact hτ₂B E⟩
  refine ⟨insert 1 (((B 0).support.powerset.image fun T => ∑ j ∈ T, B 0 j).filter
    fun s => 0 < s ∧ s ≤ 1), fun b hb => ?_, Finset.mem_insert_self _ _, fun i P hP => ?_⟩
  · rcases Finset.mem_insert.1 hb with rfl | hb
    · norm_num
    · exact (Finset.mem_filter.1 hb).2
  · obtain ⟨τ, hτs, -, hτB⟩ := hrep i
    refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨?_, lt_of_le_of_ne (hB01 i P).1
      (Ne.symm hP), (hB01 i P).2⟩)
    exact Finset.mem_image.2 ⟨τ P, Finset.mem_powerset.2 (hτs P), (hτB P).symm⟩

/-- The numbers of the hyperstandard set `D(I)` below a bound `c < 1` are finitely many. -/
private theorem finite_setOf_mem_hyperstandardSet_lt {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b)
    {c : ℝ} (hc : c < 1) : {x | x ∈ hyperstandardSet I ∧ x < c}.Finite := by
  have hfin := MMP.Flips.finite_setOf_standardCoefficient_le (I := I) (fun i => ((i : ℚ) : ℝ))
    (fun i => by exact_mod_cast hI i i.2) (sub_pos.mpr hc)
  refine (hfin.image fun p : ℕ+ × (I → ℕ) =>
    ((p.1 : ℝ) - 1) / p.1 + ∑ i, (p.2 i : ℝ) * ((i : ℚ) : ℝ) / p.1).subset ?_
  rintro x ⟨⟨-, m, hm, r, rfl⟩, hx⟩
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have key : 1 - 1 / (m : ℝ) + ∑ b ∈ I, (r b : ℝ) * (b : ℝ) / (m : ℝ) =
      (((⟨m, hm⟩ : ℕ+) : ℝ) - 1) / ((⟨m, hm⟩ : ℕ+) : ℝ) +
        ∑ i : I, ((fun i : I => r i) i : ℝ) * ((i : ℚ) : ℝ) / ((⟨m, hm⟩ : ℕ+) : ℝ) := by
    simp only [PNat.mk_coe]
    rw [Finset.sum_coe_sort I (fun b => (r b : ℝ) * (b : ℝ) / (m : ℝ))]
    congr 1
    field_simp
  refine ⟨(⟨m, hm⟩, fun i => r i), ?_, key.symm⟩
  change (((⟨m, hm⟩ : ℕ+) : ℝ) - 1) / ((⟨m, hm⟩ : ℕ+) : ℝ) +
        ∑ i : I, ((fun i : I => r i) i : ℝ) * ((i : ℚ) : ℝ) / ((⟨m, hm⟩ : ℕ+) : ℝ) ≤ 1 - (1 - c)
  rw [← key]
  linarith

/-- The rational numbers of `D(I)` at most a bound `x < 1` are finitely many. -/
private theorem finite_setOf_mem_hyperstandardSet_le {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b)
    {x : ℚ} (hx : x < 1) :
    {y ∈ {y : ℚ | ((y : ℚ) : ℝ) ∈ hyperstandardSet I} | y ≤ x}.Finite := by
  have hfin := finite_setOf_mem_hyperstandardSet_lt hI (c := ((x + 1) / 2 : ℚ))
    (by push_cast; linarith [show ((x : ℚ) : ℝ) < 1 by exact_mod_cast hx])
  refine (hfin.preimage (Rat.cast_injective.injOn)).subset fun y ⟨hy, hyx⟩ => ⟨hy, ?_⟩
  exact_mod_cast (by linarith : y < (x + 1) / 2)

/-! ### Flag strata of a dlt pair -/

section FlagAdjunctionAux

variable {k : Type} [Field k]

/-- The terminal morphism of a separated `k`-scheme is separated. -/
private theorem isSeparated_toTerminal {X : Scheme.{0}} {s : X ⟶ Spec (.of k)}
    [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  have : (X ↘ ⊤_ Scheme) = s ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

/-- **The rational top `m`-forms of a variety form a line.** -/
private theorem exists_eq_smul_of_ne_zero [PerfectField k] {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {σ : RationalPluriForms sX d m} (hσ : σ ≠ 0) (σ' : RationalPluriForms sX d m) :
    ∃ c : X.functionField, σ' = c • σ := by
  letI := functionFieldAlgebra sX
  haveI := essFiniteType_functionField (sX := sX)
  have hK : Module.finrank X.functionField Ω[X.functionField⁄k] = d :=
    (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans hd
  have h1 : Module.finrank X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]) = 1 := by
    rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
  let b1 : Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]) :=
    (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique _ _)
  let B : Module.Basis Unit X.functionField (RationalPluriForms sX d m) := ZTensorPower.basis b1 m
  have hB : Module.finrank X.functionField (RationalPluriForms sX d m) = 1 := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_unit]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' σ hσ).mp hB σ'
  exact ⟨c, hc.symm⟩

end FlagAdjunctionAux

section FlagAdjunction

variable {k : Type} [Field k]

/-- Changing a top form by a nonzero rational function keeps `m(div σ + B)` Cartier. -/
private theorem isCartierDivisor_smul_divisorOfForm_add [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) {σ : RationalPluriForms sX d 1}
    (hσ : σ ≠ 0) {B : QDivisor X} {m : ℕ}
    (hC : ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {c : X.functionField} (hc : c ≠ 0) :
    ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm (c • σ)) + B)).IsCartierDivisor := by
  obtain ⟨D, hD, hDc⟩ := hC
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hc
  refine ⟨D + (m : ℤ) • principalDivisor φ, ?_, hDc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩
  ext Γ
  have h1 := congrArg (fun G : QDivisor X => G.coeff Γ) hD
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, zsmul_eq_mul] at h1 ⊢
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hd hc hσ, coeff_principalDivisor, hφ Γ]
  push_cast
  linear_combination h1

/-- An adjunction step drops the dimension by one. -/
private theorem IsAdjunctionStep.topologicalKrullDim_eq [CharZero k] {M T : Scheme.{0}}
    {sM : M ⟶ Spec (.of k)} [IsIntegral M] [IsNormal M] [IsLocallyNoetherian M]
    [LocallyOfFiniteType sM] {n : ℕ} (hdim : topologicalKrullDim M = n + 1)
    {B : QDivisor M} {j : T ⟶ M} {BT : QDivisor T} (hj : IsAdjunctionStep sM B j BT)
    [IsIntegral T] : topologicalKrullDim T = n := by
  haveI : LocallyOfFiniteType (j ≫ sM) := hj.1.1.toLocallyOfFiniteType
  have h1 := hj.trdeg_add_one
  have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ sM)
  have h3 := topologicalKrullDim_eq_toNat_trdeg sM
  rw [hdim] at h3
  have h6 : n + 1 = (letI := functionFieldAlgebra sM; (Algebra.trdeg k M.functionField).toNat) := by
    exact_mod_cast h3
  have h7 : (letI := functionFieldAlgebra (j ≫ sM); (Algebra.trdeg k T.functionField).toNat) =
      n := by omega
  rw [h2, h7]

/-- **One adjunction step for local generators.** -/
private theorem adjunctionStep_generatesOn [CharZero k] {M T : Scheme.{0}} {sM : M ⟶ Spec (.of k)}
    [IsIntegral M] [IsNormal M] [IsLocallyNoetherian M] [CompactSpace M] [LocallyOfFiniteType sM]
    (hM : IsNormalVariety k sM) {n : ℕ} (hdim : topologicalKrullDim M = n + 1) (hn : n ≠ 0)
    {B : QDivisor M} {j : T ⟶ M} {BT : QDivisor T} (hj : IsAdjunctionStep sM B j BT)
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T]
    {m : ℕ} (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sM (n + 1) 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {V : M.Opens} {ρ : RationalPluriForms sM (n + 1) m} (hρ : GeneratesOn B m V ρ)
    (hV : ((j ⁻¹ᵁ V : T.Opens) : Set T).Nonempty) :
    haveI : LocallyOfFiniteType (j ≫ sM) := hj.1.1.toLocallyOfFiniteType
    (∃ ρ' : RationalPluriForms (j ≫ sM) n m, IsPoincareResidue sM j n m ρ ρ') ∧
      (∀ ρ' : RationalPluriForms (j ≫ sM) n m, IsPoincareResidue sM j n m ρ ρ' →
        GeneratesOn BT m (j ⁻¹ᵁ V) ρ') ∧
      ∀ σ' : RationalPluriForms (j ≫ sM) n 1, σ' ≠ 0 →
        ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ') + BT)).IsCartierDivisor := by
  haveI : LocallyOfFiniteType (j ≫ sM) := hj.1.1.toLocallyOfFiniteType
  obtain ⟨hTv, P, -, hPr, hjc, -⟩ := id hj
  haveI := hjc
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
  have hdT : topologicalKrullDim T = n := IsAdjunctionStep.topologicalKrullDim_eq hdim hj
  have hdM' : topologicalKrullDim M = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sM) hdM'
  have hdT' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sM) hdT
  obtain ⟨Q₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdT hn
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sM hM hdim j hTv P hPr Q₀
  obtain ⟨DM, hDM, hDMc⟩ := hC σ hσ0
  have hσQ : (Divisor.toQDivisor (divisorOfForm σ) + B).IsQCartier :=
    ⟨((N + 1 : ℕ) : ℤ), by exact_mod_cast (Nat.succ_pos N).ne', DM, hDM, hDMc⟩
  obtain ⟨hgen, hpull⟩ := IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue hj
    hdim P hPr σ hσ0 hσP ρσ hρσ hσQ
  set B' : QDivisor M := B - Finsupp.single P 1 with hB'
  have hBB' : Divisor.toQDivisor (divisorOfForm σ) + Finsupp.single P 1 + B' =
      Divisor.toQDivisor (divisorOfForm σ) + B := by rw [hB']; abel
  have key : ∀ L : QDivisor M, L = Divisor.toQDivisor (divisorOfForm σ) + B →
      ∃ hg, L.IsPullback j hg (Divisor.toQDivisor (divisorOfForm ρσ) + BT) := by
    rintro L rfl; exact ⟨hgen, hpull⟩
  obtain ⟨hgen', hpull'⟩ := key _ hBB'
  have hDM' : Divisor.toQDivisor DM = ((N + 1 : ℕ) : ℤ) •
      (Divisor.toQDivisor (divisorOfForm σ) + Finsupp.single P 1 + B') := by rw [hBB', hDM]
  have hPB : Finsupp.single P 1 + B' = B := by rw [hB']; abel
  -- the local comparison with the generators of `exists_generatesOn_isPoincareResidue`
  have hloc : ∀ x : T, j x ∈ V → ∃ U : M.Opens, j x ∈ U ∧
      ∃ ρ'' : RationalPluriForms (j ≫ sM) n ((N + 1 : ℕ) : ℤ),
        GeneratesOn BT (N + 1) (j ⁻¹ᵁ U) ρ'' ∧ ∃ r : M.presheaf.stalk (j x), IsUnit r ∧
          IsPoincareResidue sM j n (N + 1) ρ ((j.stalkMap (genericPoint T)).hom
            ((M.presheaf.stalkSpecializes
              ((genericPoint_specializes x).map j.base.hom.continuous)).hom r) • ρ'') := by
    intro x hxV
    obtain ⟨U, hxU, τ', hτ', ρ'', hres, hρ''⟩ :=
      MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sM hdim j hTv hdT P hPr B' σ
        hσ0 ρσ hρσ hρσ0 BT hgen' hpull' N DM hDM' hDMc x
    rw [hPB] at hτ'
    obtain ⟨c, hc⟩ := exists_eq_smul_of_ne_zero hd hτ'.1 ρ
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hρ.1 hc
    have hord : ∀ Γ : Mori.PrimeDivisor M, j x ∈ Γ.support → M.ord c Γ.genericPoint = 0 := by
      intro Γ hΓ
      have h1 := hρ.2 Γ ⟨j x, hΓ, hxV⟩
      have h2 := hτ'.2 Γ ⟨j x, hΓ, hxU⟩
      rw [hc, Γ.ordForm_smul_of_topologicalKrullDim_eq hdM' hc0 hτ'.1] at h1
      push_cast at h1 h2
      have : ((M.ord c Γ.genericPoint : ℤ) : ℚ) = 0 := by linarith
      exact_mod_cast this
    obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
      (j x) hc0 fun Γ hΓ => (hord Γ hΓ).ge
    obtain ⟨r', hr'⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
      (j x) (inv_ne_zero hc0) fun Γ hΓ => by
        have h := Scheme.ord_mul (x := Γ.genericPoint) hc0 (inv_ne_zero hc0)
        rw [mul_inv_cancel₀ hc0, MMP.CyclicChartDifferent.Aux.ord_one', hord Γ hΓ] at h
        omega
    have hru : IsUnit r := IsUnit.of_mul_eq_one r' (IsFractionRing.injective _ M.functionField
      (by rw [map_mul, hr, hr', mul_inv_cancel₀ hc0, map_one]))
    refine ⟨U, hxU, ρ'', hρ'', r, hru, ?_⟩
    have h := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hres ((M.presheaf.stalkSpecializes
      ((genericPoint_specializes x).map j.base.hom.continuous)).hom r)
    rwa [MMP.Mori.algebraMap_stalkSpecializes, hr, ← hc] at h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hV
    obtain ⟨U, -, ρ'', -, r, -, hres⟩ := hloc x hx
    exact ⟨_, hres⟩
  · intro ρ' hρ'
    refine ⟨?_, fun Q hQ => ?_⟩
    · obtain ⟨x, hx⟩ := hV
      obtain ⟨U, hxU, ρ'', hρ'', r, hr, hres⟩ := hloc x hx
      rw [IsPoincareResidue.unique hj hρ' hres]
      exact smul_ne_zero (((hr.map _).map _).ne_zero) hρ''.1
    · obtain ⟨x, hxQ, hxV⟩ := hQ
      obtain ⟨U, hxU, ρ'', hρ'', r, hr, hres⟩ := hloc x hxV
      rw [IsPoincareResidue.unique hj hρ' hres]
      have hQx : Q.genericPoint ⤳ x := by
        have : x ∈ Q.support := hxQ
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
        exact specializes_iff_mem_closure.mpr this
      have hQx' : j Q.genericPoint ⤳ j x := hQx.map j.base.hom.continuous
      have hTQ : genericPoint T ⤳ Q.genericPoint := genericPoint_specializes _
      set r₁ := (M.presheaf.stalkSpecializes hQx').hom r
      have hunit : IsUnit ((j.stalkMap Q.genericPoint).hom r₁) := (hr.map _).map _
      have ha : (j.stalkMap (genericPoint T)).hom ((M.presheaf.stalkSpecializes
          ((genericPoint_specializes x).map j.base.hom.continuous)).hom r) =
          algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom r₁) := by
        have e1 : (M.presheaf.stalkSpecializes
            ((genericPoint_specializes x).map j.base.hom.continuous)).hom r =
            (M.presheaf.stalkSpecializes (j.base.hom.map_specializes hTQ)).hom r₁ := by
          change _ = (M.presheaf.stalkSpecializes hQx' ≫
            M.presheaf.stalkSpecializes (j.base.hom.map_specializes hTQ)).hom r
          rw [TopCat.Presheaf.stalkSpecializes_comp]
        rw [e1]
        exact Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hTQ r₁
      have ha0 : (j.stalkMap (genericPoint T)).hom ((M.presheaf.stalkSpecializes
          ((genericPoint_specializes x).map j.base.hom.continuous)).hom r) ≠ 0 := by
        rw [ha]; exact (hunit.map _).ne_zero
      rw [Q.ordForm_smul_of_topologicalKrullDim_eq hdT ha0 hρ''.1, ha,
        Q.ord_algebraMap_of_isUnit hunit]
      have := hρ''.2 Q ⟨x, hxQ, hxU⟩
      push_cast at this ⊢
      linarith
  · intro σ' hσ'
    obtain ⟨D', hD', hp⟩ := hpull (N + 1) (Nat.succ_pos N) DM hDM hDMc
    obtain ⟨c, rfl⟩ := exists_eq_smul_of_ne_zero hdT' hρσ0 σ'
    have hc0 : c ≠ 0 := by rintro rfl; exact hσ' (zero_smul _ _)
    exact isCartierDivisor_smul_divisorOfForm_add hdT hρσ0 ⟨D', hD', hp.isCartier hDMc⟩ hc0

/-- Transport of `GeneratesOn` along an equality of structure morphisms. -/
private theorem generatesOn_of_heq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {s s' : X ⟶ Spec (.of k)} (h : s' = s) {d m : ℕ} {B : QDivisor X} {U : X.Opens}
    {ρ : RationalPluriForms s' d m} {τ : RationalPluriForms s d m} (hρ : HEq ρ τ)
    (hτ : GeneratesOn B m U τ) : GeneratesOn B m U ρ := by
  subst h
  rw [eq_of_heq hρ]
  exact hτ

/-- Transport of the Cartier condition on adjoints along an equality of structure morphisms. -/
private theorem isCartierDivisor_of_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {s s' : X ⟶ Spec (.of k)} [LocallyOfFiniteType s] [LocallyOfFiniteType s']
    (h : s' = s) {d m : ℕ} {B : QDivisor X}
    (hC : ∀ σ : RationalPluriForms s d 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor) :
    ∀ σ : RationalPluriForms s' d 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor := by
  subst h
  exact hC

/-- The final stratum of a flag on a compact scheme is compact. -/
private theorem compactSpace_of_stratumAdjunctionData {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X} {S : Scheme.{0}} {ι : S ⟶ X}
    {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) : CompactSpace S :=
  haveI := F.isClosedImmersion
  ι.isClosedEmbedding.compactSpace

/-- **Adjunction for local generators along a flag.** -/
private theorem flag_generatesOn [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    {B : QDivisor X} {n m : ℕ} (hn : topologicalKrullDim X = n)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    (hm : 0 < m) {U : X.Opens} {τ : RationalPluriForms sX n m} (hτ : GeneratesOn B m U τ)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ}, e + F.length = n → e ≠ 0 → ((ι ⁻¹ᵁ U : S.Opens) : Set S).Nonempty →
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    topologicalKrullDim S = e ∧
      (∀ σ : RationalPluriForms (ι ≫ sX) e 1, σ ≠ 0 →
        ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BS)).IsCartierDivisor) ∧
      (∃ ρ : RationalPluriForms (ι ≫ sX) e m, IsIteratedResidue sX B τ F e ρ) ∧
      ∀ ρ : RationalPluriForms (ι ≫ sX) e m, IsIteratedResidue sX B τ F e ρ →
        GeneratesOn BS m (ι ⁻¹ᵁ U) ρ := by
  induction F with
  | refl h =>
    intro e he _ _
    simp only [StratumAdjunctionData.length, add_zero] at he
    subst he
    refine ⟨hn, isCartierDivisor_of_eq (Category.id_comp sX) hC,
      ⟨_, IsIteratedResidue.refl h⟩, fun ρ hρ => ?_⟩
    obtain ⟨-, hρτ⟩ := hρ.rec'
    exact (generatesOn_of_heq (Category.id_comp sX) hρτ hτ).mono fun x hx => hx
  | @step S T ι BS F j BT hj ih =>
    intro e he he0 hU
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : IsNormal T := hj.1.2
    haveI : IsClosedImmersion j := by obtain ⟨-, -, -, -, h, -⟩ := hj; exact h
    haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
    have he' : (e + 1) + F.length = n := by
      simp only [StratumAdjunctionData.length] at he; omega
    have hU' : ((ι ⁻¹ᵁ U : S.Opens) : Set S).Nonempty := by
      obtain ⟨x, hx⟩ := hU
      exact ⟨j x, hx⟩
    obtain ⟨hdS, hCS, ⟨ρ₀, hρ₀⟩, hgen⟩ := ih he' (Nat.succ_ne_zero e) hU'
    have hdS' : topologicalKrullDim S = (e : WithBot ℕ∞) + 1 := by rw [hdS]; norm_cast
    have hV : ((j ⁻¹ᵁ (ι ⁻¹ᵁ U) : T.Opens) : Set T).Nonempty := hU
    obtain ⟨⟨ρ', hρ'⟩, hgen', hCT⟩ := adjunctionStep_generatesOn F.isNormalVariety hdS' he0 hj hm
      hCS (hgen ρ₀ hρ₀) hV
    haveI : LocallyOfFiniteType ((j ≫ ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    refine ⟨?_, isCartierDivisor_of_eq (Category.assoc j ι sX) hCT,
      ⟨_, IsIteratedResidue.step hρ₀ hρ'⟩, fun ρ hρ => ?_⟩
    · exact IsAdjunctionStep.topologicalKrullDim_eq hdS' hj
    · obtain ⟨σ₀, hσ₀, σ', hσ', hρσ⟩ := hρ.rec'
      have h1 := IsIteratedResidue.unique (IsIteratedResidue.of_rec F hσ₀) hρ₀
      subst h1
      have h2 := hgen' _ hσ'
      exact (generatesOn_of_heq (Category.assoc j ι sX) hρσ h2).mono fun x hx => hx

/-- Casting a rational pluriform along an equality of structure morphisms commutes with scalar
multiplication. -/
private theorem cast_smul_rationalPluriForms {X : Scheme.{0}} [IsIntegral X] {s s' : X ⟶ Spec (.of k)}
    (hs : s = s') {d : ℕ} {m : ℤ}
    (e : RationalPluriForms s d m = RationalPluriForms s' d m) (c : X.functionField)
    (τ : RationalPluriForms s d m) : cast e (c • τ) = c • cast e τ := by
  subst hs
  rfl

/-- **Iterated residues are linear over functions regular along the stratum**:
`Res_F(r τ) = r̄ Res_F(τ)` for `r` in the local ring at the generic point of the final stratum. -/
private theorem IsIteratedResidue.algebraMap_smul {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {n m : ℕ}
    {τ : RationalPluriForms sX n m} {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    [IsIntegral S] {F : StratumAdjunctionData sX B ι BS} {e : ℕ}
    {ρ : RationalPluriForms (ι ≫ sX) e m} (h : IsIteratedResidue sX B τ F e ρ) :
    ∀ r : X.presheaf.stalk (ι (genericPoint S)),
      IsIteratedResidue sX B (algebraMap _ X.functionField r • τ) F e
        ((ι.stalkMap (genericPoint S)).hom r • ρ) := by
  induction h with
  | refl hp =>
    intro r
    have h1 := IsIteratedResidue.refl (τ := algebraMap _ X.functionField r • τ) hp
    rw [cast_smul_rationalPluriForms (Category.id_comp sX).symm] at h1
    convert h1 using 2
    rw [Scheme.Hom.stalkMap_id]
    change r = (X.presheaf.stalkSpecializes (specializes_refl _)).hom r
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  | @step S T ι BS _ _ _ F j BT hj e ρ ρ' hF hr ih =>
    intro r
    have hsp : genericPoint S ⤳ j (genericPoint T) := genericPoint_specializes _
    have h1 := ih ((X.presheaf.stalkSpecializes (ι.base.hom.map_specializes hsp)).hom r)
    have e1 : algebraMap (X.presheaf.stalk (ι (genericPoint S))) X.functionField
        ((X.presheaf.stalkSpecializes (ι.base.hom.map_specializes hsp)).hom r) =
        algebraMap _ X.functionField r := MMP.Mori.algebraMap_stalkSpecializes _ r
    have e2 : (ι.stalkMap (genericPoint S)).hom
        ((X.presheaf.stalkSpecializes (ι.base.hom.map_specializes hsp)).hom r) =
        algebraMap (S.presheaf.stalk (j (genericPoint T))) S.functionField
          ((ι.stalkMap (j (genericPoint T))).hom r) :=
      Scheme.Hom.stalkSpecializes_stalkMap_apply ι _ _ hsp r
    rw [e1, e2] at h1
    have h2 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hr
      ((ι.stalkMap (j (genericPoint T))).hom r)
    have h3 := IsIteratedResidue.step (hj := hj) h1 h2
    rw [cast_smul_rationalPluriForms (Category.assoc j ι sX).symm] at h3
    convert h3 using 2
    rw [Scheme.Hom.stalkMap_comp]
    rfl

/-- Moving a divisor over `X` along an equality of structure morphisms. -/
private theorem exists_divisorOver_of_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {s s' : X ⟶ Spec (.of k)} (h : s = s') {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (G : DivisorOver k s) {a : ℚ} (ha : IsDiscrepancy s n K B G a) :
    ∃ G' : DivisorOver k s', (G.IsExceptional → G'.IsExceptional) ∧
      G'.f G'.E.genericPoint = G.f G.E.genericPoint ∧ IsDiscrepancy s' n K B G' a := by
  subst h
  exact ⟨G, id, rfl, ha⟩

/-- The Cartier condition along a flag, from a generator on `X` near the stratum. -/
private theorem isCartierDivisor_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {B : QDivisor X} {n m : ℕ} (hn : topologicalKrullDim X = n) (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS)
    {e : ℕ} (he : e + F.length = n) (he0 : e ≠ 0) :
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    topologicalKrullDim S = e ∧ ∀ σ : RationalPluriForms (ι ≫ sX) e 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BS)).IsCartierDivisor := by
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX hX hn
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK₀
  have hdivω : divisorOfForm ω = K₀ := Finsupp.ext hωK
  have hCK : ((m : ℤ) • (Divisor.toQDivisor K₀ + B)).IsCartierDivisor := hdivω ▸ hC ω hω0
  have hPX : Mori.IsPair sX B := ⟨hX, n, K₀, hK₀, ⟨m, by exact_mod_cast hm.ne', hCK⟩⟩
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  obtain ⟨-, U₀, hU₀, τ₀, hτ₀⟩ := MMP.Positivity.IsPair.exists_generatesOn hPX hK₀ hCK (ι x₀)
  obtain ⟨hdS, hCS, -, -⟩ := flag_generatesOn hn hC hm hτ₀ F he he0 ⟨x₀, hU₀⟩
  exact ⟨hdS, hCS⟩

/-- **The boundaries along a flag on an effective pair are effective.** -/
private theorem nonneg_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {B : QDivisor X} (hB0 : ∀ Q, 0 ≤ B.coeff Q) {n m : ℕ} (hn : topologicalKrullDim X = n)
    (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ}, e + F.length = n → ∀ Q, 0 ≤ BS.coeff Q := by
  induction F with
  | refl h => intro e _ Q; exact hB0 Q
  | @step S T ι BS F j BT hj ih =>
    intro e he Q
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : IsNormal T := hj.1.2
    have he' : (e + 1) + F.length = n := by
      simp only [StratumAdjunctionData.length] at he; omega
    have hBS0 := ih he'
    obtain ⟨hdS, hCS⟩ :=
      isCartierDivisor_of_stratumAdjunctionData hX hn hm hC F he' (Nat.succ_ne_zero e)
    have hdS' : topologicalKrullDim S = (e : WithBot ℕ∞) + 1 := by rw [hdS]; norm_cast
    obtain ⟨hTv, P, hP1, hPr, hjc, -⟩ := id hj
    haveI := hjc
    haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
    set B₀ : QDivisor S := BS - Finsupp.single P 1 with hB₀
    have hB₀P : Finsupp.single P 1 + B₀ = BS := by rw [hB₀]; abel
    obtain ⟨hB0', hBP⟩ := hj.sub_single_nonneg hBS0 hPr
    have hB0 : B₀.IsEffective := hB0'
    obtain ⟨τ, hτ0, hτP, -, ρ, hρ, -, -⟩ :=
      MMP.Fourfold.exists_form_of_residue_order (ι ≫ sX) F.isNormalVariety hdS' j hTv P hPr Q
    have hDQ : (Divisor.toQDivisor (divisorOfForm τ) + BS).IsQCartier :=
      ⟨m, by exact_mod_cast hm.ne', hCS τ hτ0⟩
    obtain ⟨hgen, hpull⟩ := IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue hj
      hdS' P hPr τ hτ0 hτP ρ hρ hDQ
    have hBB : Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B₀ =
        Divisor.toQDivisor (divisorOfForm τ) + BS := by rw [add_assoc, hB₀P]
    have key : ∀ L : QDivisor S, L = Divisor.toQDivisor (divisorOfForm τ) + BS →
        ∃ hg, L.IsPullback j hg (Divisor.toQDivisor (divisorOfForm ρ) + BT) := by
      rintro L rfl; exact ⟨hgen, hpull⟩
    obtain ⟨hgen', hpull'⟩ := key _ hBB
    exact coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero (ι ≫ sX)
      F.isNormalVariety hdS' j hTv P hPr B₀ hB0 hBP τ hτ0 hτP ρ hρ (by rwa [hBB]) BT
      hgen' hpull' Q

/-- **Forward adjunction along a flag.** A divisor over the final stratum `S` of a flag on `X`
gives a divisor over `X`, exceptional unless the flag and the divisor are trivial, with the image
of the same centre and the same discrepancy. -/
private theorem exists_isDiscrepancy_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {B : QDivisor X} (hB0 : ∀ Q, 0 ≤ B.coeff Q) {n m : ℕ} (hn : topologicalKrullDim X = n)
    (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ}, e + F.length = n → e ≠ 0 →
    ∀ [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
      (KS : Divisor S), KS.IsCanonicalDivisor (ι ≫ sX) e →
    ∀ (G : DivisorOver k (ι ≫ sX)) (a : ℚ), IsDiscrepancy (ι ≫ sX) e KS BS G a →
    ∃ (K : Divisor X) (E : DivisorOver k sX), K.IsCanonicalDivisor sX n ∧
      (G.IsExceptional ∨ F.length ≠ 0 → E.IsExceptional) ∧
      ι (G.f G.E.genericPoint) = E.f E.E.genericPoint ∧ IsDiscrepancy sX n K B E a := by
  induction F with
  | refl h =>
    intro e he _ _ _ _ KS hKS G a ha
    simp only [StratumAdjunctionData.length, add_zero] at he
    subst he
    obtain ⟨G', hG'e, hG'c, hG'a⟩ := exists_divisorOver_of_eq (Category.id_comp sX) G ha
    refine ⟨KS, G', (Category.id_comp sX) ▸ hKS, fun h' => ?_, ?_, hG'a⟩
    · rcases h' with h' | h'
      · exact hG'e h'
      · exact absurd rfl h'
    · rw [hG'c]; rfl
  | @step S T ι BS F j BT hj ih =>
    intro e he he0 _ _ _ KT hKT G a ha
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : IsNormal T := hj.1.2
    haveI : IsClosedImmersion j := by obtain ⟨-, -, -, -, h, -⟩ := hj; exact h
    haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
    haveI : LocallyOfFiniteType (j ≫ ι ≫ sX) := hj.1.1.toLocallyOfFiniteType
    have he' : (e + 1) + F.length = n := by
      simp only [StratumAdjunctionData.length] at he; omega
    have hdS : topologicalKrullDim S = ((e + 1 : ℕ) : WithBot ℕ∞) := by
      have h1 := topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX)
      have h2 := StratumAdjunctionData.dim_add_length hn F h1
      rw [h1]; congr 1; omega
    have hdS' : topologicalKrullDim S = (e : WithBot ℕ∞) + 1 := by rw [hdS]; norm_cast
    obtain ⟨-, hCS⟩ :=
      isCartierDivisor_of_stratumAdjunctionData hX hn hm hC F he' (Nat.succ_ne_zero e)
    have hBS0 := nonneg_of_stratumAdjunctionData hX hB0 hn hm hC F he'
    -- a canonical divisor on `S`, and the pair `(S, B_S)`
    obtain ⟨KS, hKS⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (ι ≫ sX)
      F.isNormalVariety hdS
    obtain ⟨ωS, hωS0, hωSK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq
      F.isNormalVariety hKS
    have hdivωS : divisorOfForm ωS = KS := Finsupp.ext hωSK
    have hCKS : ((m : ℤ) • (Divisor.toQDivisor KS + BS)).IsCartierDivisor :=
      hdivωS ▸ hCS ωS hωS0
    have hPS : Mori.IsPair (ι ≫ sX) BS :=
      ⟨F.isNormalVariety, e + 1, KS, hKS, ⟨m, by exact_mod_cast hm.ne', hCKS⟩⟩
    -- the adjunction step `T ⊂ S`
    obtain ⟨hTv, P, hP1, hPr, hjc, -⟩ := id hj
    set B₀ : QDivisor S := BS - Finsupp.single P 1 with hB₀
    have hB₀P : Finsupp.single P 1 + B₀ = BS := by rw [hB₀]; abel
    obtain ⟨hB0, hBP⟩ := hj.sub_single_nonneg hBS0 hPr
    have hD : ∃ m' : ℕ, 0 < m' ∧ ((m' : ℤ) • (Divisor.toQDivisor KS +
        (Finsupp.single P 1 + B₀))).IsCartierDivisor :=
      ⟨m, hm, by rwa [hB₀P]⟩
    have hBSloc : ∃ m' : ℕ, 0 < m' ∧ ∀ x : T, ∃ U : S.Opens, j.base x ∈ U ∧
        ∃ τ : RationalPluriForms (ι ≫ sX) (e + 1) m',
          GeneratesOn (Finsupp.single P 1 + B₀) m' U τ ∧
          ∃ ρ : RationalPluriForms (j ≫ ι ≫ sX) e m',
            IsPoincareResidue (ι ≫ sX) j e m' τ ρ ∧ GeneratesOn BT m' (j ⁻¹ᵁ U) ρ := by
      refine ⟨m, hm, fun x => ?_⟩
      obtain ⟨-, U, hxU, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hPS hKS hCKS (j x)
      obtain ⟨⟨ρ, hρ⟩, hgen, -⟩ :=
        adjunctionStep_generatesOn F.isNormalVariety hdS' he0 hj hm hCS hτ ⟨x, hxU⟩
      exact ⟨U, hxU, τ, by rwa [hB₀P], ρ, hρ, hgen ρ hρ⟩
    -- forward adjunction along the step, then along the shorter flag
    obtain ⟨G', hG'e, hG'c, hG'a⟩ := exists_divisorOver_of_eq (Category.assoc j ι sX) G ha
    have hKT' : KT.IsCanonicalDivisor (j ≫ ι ≫ sX) e := (Category.assoc j ι sX) ▸ hKT
    obtain ⟨E₁, hE₁, hcen₁, hiff⟩ := exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue
      (ι ≫ sX) F.isNormalVariety e KS hKS P j hj.1 hPr KT hKT' B₀ hB0 hBP hD BT hBSloc G'
    have ha₁ : IsDiscrepancy (ι ≫ sX) (e + 1) KS BS E₁ a := by
      have := (hiff a).mp hG'a
      rwa [hB₀P] at this
    obtain ⟨K, E, hK, hEe, hcen, hEa⟩ := ih he' (Nat.succ_ne_zero e) KS hKS E₁ a ha₁
    refine ⟨K, E, hK, fun _ => hEe (Or.inl hE₁), ?_, hEa⟩
    rw [← hcen]
    change ι (j (G.f G.E.genericPoint)) = ι (E₁.f E₁.E.genericPoint)
    rw [← hG'c]
    exact congrArg ι hcen₁

/-- On an integral scheme locally of finite type over `k` of dimension `n`, every point has
coheight at most `n`. -/
private theorem coheight_le_of_topologicalKrullDim_eq {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] [LocallyOfFiniteType sY] {n : ℕ} (hn : topologicalKrullDim Y = n) (y : Y) :
    Order.coheight y ≤ n := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y
  rw [hn] at h
  have hnn : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure {y} : Set Y) := by
    have : Nonempty (TopologicalSpace.IrreducibleCloseds (closure {y} : Set Y)) :=
      ⟨⟨closure {⟨y, subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  have h1 : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    rw [← h]; exact le_add_of_nonneg_left hnn
  exact_mod_cast h1

/-- A divisor over a normal variety is exceptional exactly when its center has codimension at
least two; the two directions used here. -/
private theorem two_le_coheight_iff_isExceptional {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sX)
  rw [DivisorOver.IsExceptional, MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hmem : D.f D.E.genericPoint ∈
      (Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) : Set X) := by
    refine subset_closure ⟨D.E.genericPoint, ?_, rfl⟩
    change D.E.genericPoint ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  refine ⟨fun h => h _ hmem, fun h y hy => h.trans (Order.coheight_anti ?_)⟩
  have h1 : D.f '' (D.E.idealSheaf.support : Set D.Y) ⊆ closure {D.f D.E.genericPoint} := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ D.E.support := hw
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hw'
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hw').map D.f.base.hom.continuous)
  exact specializes_iff_mem_closure.mpr (closure_minimal h1 isClosed_closure hy)

/-- A point of an open `U` lies on a prime divisor of `U` exactly when its image lies on the
prime divisor of `X` it extends to. -/
private theorem mem_support_primeDivisorMap_iff {X : Scheme.{0}} (U : X.Opens)
    (G : Mori.PrimeDivisor U.toScheme) (y : U.toScheme) :
    U.ι y ∈ (OpenWeilRestriction.primeDivisorMap U.ι G).support ↔ y ∈ G.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure,
    ← specializes_iff_mem_closure, OpenWeilRestriction.genericPoint_primeDivisorMap]
  exact U.ι.isOpenEmbedding.isInducing.specializes_iff

/-- **The final stratum of a flag of length at least two on a dlt pair is a dlt stratum.**
Forward adjunction along the flag turns the step divisor, of discrepancy `≤ -1` on the
penultimate stratum, into an exceptional divisor over `X` with center `x = ι(η_S)` and
discrepancy `≤ -1`. By dlt, `x` lies in the snc open `U`, and the snc bound forces exactly
`codim x` components of `⌊B⌋` through `x`; they cut out `S` near `x`. -/
private theorem isDltStratum_range_step [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) {S T : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) {j : T ⟶ S} {BT : QDivisor T}
    (hj : IsAdjunctionStep (ι ≫ sX) BS j BT) (hF : F.length ≠ 0) :
    IsDltStratum sX B (Set.range (j ≫ ι).base) := by
  classical
  obtain ⟨⟨hP, hnn, -⟩, -, -⟩ := id hB
  obtain ⟨hX, n, K, hK, hQ⟩ := hP
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  obtain ⟨m, hm, hCK⟩ := hQ.exists_pos
  have hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor := by
    intro σ hσ
    obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
    have hdivω : divisorOfForm ω = K := Finsupp.ext hωK
    obtain ⟨c, rfl⟩ := exists_eq_smul_of_ne_zero
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0 σ
    have hc : c ≠ 0 := by rintro rfl; exact hσ (zero_smul _ _)
    exact isCartierDivisor_smul_divisorOfForm_add hn hω0 (by rwa [hdivω]) hc
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
  haveI : IsNormal S := F.isNormalVariety.2
  haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
  haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
  haveI : IsClosedImmersion ι := F.isClosedImmersion
  obtain ⟨e, hdS, he⟩ : ∃ e : ℕ, topologicalKrullDim S = e ∧ e + F.length = n :=
    ⟨_, topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX), StratumAdjunctionData.dim_add_length hn F
      (topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX))⟩
  obtain ⟨hTv, P, hP1, hPr, hjc, -⟩ := id hj
  have he0 : e ≠ 0 := by
    rintro rfl
    have := coheight_le_of_topologicalKrullDim_eq (ι ≫ sX) hdS P.genericPoint
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)
  obtain ⟨-, hCS⟩ := isCartierDivisor_of_stratumAdjunctionData hX hn hm hC F he he0
  obtain ⟨KS, hKS⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (ι ≫ sX)
    F.isNormalVariety hdS
  obtain ⟨ωS, hωS0, hωSK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq
    F.isNormalVariety hKS
  have hdivωS : divisorOfForm ωS = KS := Finsupp.ext hωSK
  have hCKS : ((m : ℤ) • (Divisor.toQDivisor KS + BS)).IsCartierDivisor := hdivωS ▸ hCS ωS hωS0
  have hPS : IsPairWith (ι ≫ sX) e KS BS :=
    ⟨F.isNormalVariety, hKS, m, by exact_mod_cast hm.ne', hCKS⟩
  -- the step divisor `P`, as a divisor over `S`, has discrepancy `-coeff_P B_S ≤ -1`
  set G := DivisorOver.ofPrimeDivisor k F.isNormalVariety P with hG
  have hGc : G.f G.E.genericPoint = P.genericPoint := rfl
  have hGex : ¬ G.IsExceptional := by
    rw [two_le_coheight_iff_isExceptional F.isNormalVariety, hGc, P.coheight_genericPoint]
    decide
  obtain ⟨D, hDc, hDa⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPS G hGex
  have hDP : D = P := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hDc,
      DivisorOver.center_eq_closure_genericPoint, hGc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have ha : -BS.coeff D ≤ -1 := by rw [hDP]; linarith
  -- forward adjunction along the flag
  obtain ⟨K', E, hK', hEex, hcen, hEa⟩ :=
    exists_isDiscrepancy_of_stratumAdjunctionData hX hnn hn hm hC F he he0 KS hKS G _ hDa
  have hEexc : E.IsExceptional := hEex (Or.inr hF)
  have hx2 : 2 ≤ Order.coheight (E.f E.E.genericPoint) :=
    (two_le_coheight_iff_isExceptional hX E).mp hEexc
  -- the open `U` of the dlt condition contains the center `x`
  obtain ⟨hPw, hcoeff, U, hUsm, hsnc, hZ⟩ :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK' B).mp hB
  have hxU : E.f E.E.genericPoint ∈ U := by
    by_contra hxU
    have hsub : (E.center : Set X) ⊆ (U : Set X)ᶜ := by
      rw [DivisorOver.center_eq_closure_genericPoint]
      exact closure_minimal (Set.singleton_subset_iff.mpr hxU) U.isOpen.isClosed_compl
    have := hZ E _ hsub hEa
    linarith
  have hEU : ((E.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl, hxU⟩
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨hY, hf, E', hE', -, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPw E U hEU
  set E'' : DivisorOver k (U.ι ≫ sX) := ⟨_, E.f ∣_ U, hY, hf, E'⟩ with hE''
  have hE''c : U.ι (E''.f E''.E.genericPoint) = E.f E.E.genericPoint := by
    change U.ι ((E.f ∣_ U) E'.genericPoint) = _
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE']
    exact congrArg E.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ E').symm
  have hcU : Order.coheight (E''.f E''.E.genericPoint) = Order.coheight (E.f E.E.genericPoint) := by
    rw [← hE''c]; exact (coheight_eq_of_isOpenImmersion U.ι).symm
  have hPU := hPw.restrictOpen U
  have hE''ex : E''.IsExceptional :=
    (two_le_coheight_iff_isExceptional hPU.1 E'').mpr (by rwa [hcU])
  have hE''a := (hiff _).mp hEa
  have hUsm' : IsSmoothScheme (U.ι ≫ sX) := by
    rw [isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro y _
    have h := hUsm y.2
    rw [smoothLocus_eq_smoothLocus] at h
    exact h
  have hsnc' : DivisorWithCoeffs.IsSNC (U.ι ≫ sX)
      (∑ E ∈ (B.restrictOpen U).support, Finsupp.single E (1 : ℤ)) :=
    hsnc.of_support_subset <| Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr
      fun E hE => Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hE)
  obtain ⟨c, Tc, hc, hT, hc2, hcard, hTS, hTx, hle⟩ := MMP.Mori.le_isDiscrepancy_of_isSNC hPU.1
    hUsm' hPU.2.1 le_rfl hsnc' (fun E _ => (hcoeff _).2) E'' hE''ex hE''a
  -- every component through the center has coefficient one, and there are `c` of them
  have hnnT : ∀ G ∈ Tc, 0 ≤ 1 - (B.restrictOpen U).coeff G := fun G _ => by
    have := (hcoeff (OpenWeilRestriction.primeDivisorMap U.ι G)).2
    change (0 : ℚ) ≤ 1 - B.coeff (OpenWeilRestriction.primeDivisorMap U.ι G)
    linarith
  have hsum0 := Finset.sum_nonneg hnnT
  have hcardq : (Tc.card : ℚ) ≤ c := by exact_mod_cast hcard
  have hsum : ∑ G ∈ Tc, (1 - (B.restrictOpen U).coeff G) = 0 := by linarith
  have hcT : Tc.card = c := by exact_mod_cast (by linarith : (Tc.card : ℚ) = c)
  have hT1 : ∀ G ∈ Tc, B.coeff (OpenWeilRestriction.primeDivisorMap U.ι G) = 1 := fun G hG => by
    have := (Finset.sum_eq_zero_iff_of_nonneg hnnT).mp hsum G hG
    have h' : (B.restrictOpen U).coeff G = 1 := by linarith
    exact h'
  -- the center `x` and the range of the stratum
  set x := E.f E.E.genericPoint with hx
  have hxP : x = ι P.genericPoint := hcen.symm
  have hrange : Set.range (j ≫ ι).base = closure {x} := by
    have h1 : Set.range (j ≫ ι).base = ι.base '' Set.range j.base := by
      ext y
      exact ⟨fun ⟨t, h⟩ => ⟨j t, ⟨t, rfl⟩, h⟩, fun ⟨_, ⟨t, rfl⟩, h⟩ => ⟨t, h⟩⟩
    rw [h1, hPr, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hxP]
  have hcl : ∀ Q : Mori.PrimeDivisor X, IsClosed (Q.support : Set X) := fun Q => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hxmem : ∀ G ∈ Tc, x ∈ (OpenWeilRestriction.primeDivisorMap U.ι G).support :=
    fun G hG => by
      rw [← hE''c]
      exact (mem_support_primeDivisorMap_iff U G _).mpr (hTx G hG)
  refine ⟨hB, Tc.image (OpenWeilRestriction.primeDivisorMap U.ι), ?_, ?_, ?_, ?_⟩
  · rw [Finset.image_nonempty, ← Finset.card_pos, hcT]; omega
  · intro P' hP'
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hP'
    rw [hT1 G hG]
  · refine ⟨x, Set.mem_iInter₂.mpr fun P' hP' => ?_⟩
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hP'
    exact hxmem G hG
  · rw [hrange]
    refine ⟨⟨isIrreducible_singleton.closure, fun y hy => Set.mem_iInter₂.mpr fun P' hP' => ?_⟩,
      fun T' hT' hsub => ?_⟩
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hP'
      exact closure_minimal (Set.singleton_subset_iff.mpr (hxmem G hG))
        (hcl _) hy
    · obtain ⟨hT'irr, hT'sub⟩ := hT'
      have hy := hT'irr.isGenericPoint_genericPoint_closure
      set y := hT'irr.genericPoint
      have hxT' : x ∈ T' := hsub (subset_closure rfl)
      have hyx : y ⤳ x := hy.specializes (subset_closure hxT')
      have hyU : y ∈ U := hyx.mem_open U.isOpen hxU
      have hyJ : ∀ G ∈ Tc, (⟨y, hyU⟩ : U.toScheme) ∈ G.support := fun G hG => by
        refine (mem_support_primeDivisorMap_iff U G _).mp ?_
        have h1 : T' ⊆ (OpenWeilRestriction.primeDivisorMap U.ι G).support := fun z hz =>
          Set.mem_iInter₂.mp (hT'sub hz) _ (Finset.mem_image_of_mem _ hG)
        exact closure_minimal h1 (hcl _) hy.mem
      -- `y` lies on `c` components of an snc divisor, so it has coheight at least `c`
      obtain ⟨N, z, jj, hz, hjj, -⟩ := MMP.Mori.exists_at_of_isSNC hsnc' ⟨y, hyU⟩
      have hcN : Tc.card ≤ N := by
        have h := Fintype.card_le_of_injective
          (fun G : Tc => jj ⟨G.1, hTS G.2, hyJ G.1 G.2⟩)
          (fun a b hab => by
            have h := hjj hab
            simp only [Subtype.mk.injEq] at h
            exact Subtype.ext h)
        simpa using h
      have hcy : (c : ℕ∞) ≤ Order.coheight y := by
        have h := ringKrullDim_stalk_eq_coheight (X := U.toScheme) ⟨y, hyU⟩
        rw [hz.2] at h
        have h2 := coheight_eq_of_isOpenImmersion (x := (⟨y, hyU⟩ : U.toScheme)) U.ι
        have h3 : (N : ℕ∞) = Order.coheight (U.ι ⟨y, hyU⟩) := by rw [h2]; exact_mod_cast h
        change (c : ℕ∞) ≤ Order.coheight (U.ι ⟨y, hyU⟩)
        rw [← h3]
        exact_mod_cast hcT ▸ hcN
      have hcx : Order.coheight x = c := by rw [← hcU, ← hc]
      have hyeq : y = x := by
        by_contra hne
        have hlt : x < y := lt_of_le_not_ge hyx fun h => hne (hyx.antisymm h).eq
        have hfin : Order.coheight y ≠ ⊤ :=
          ne_top_of_le_ne_top (by simp) (coheight_le_of_topologicalKrullDim_eq sX hn y)
        have := Order.coheight_strictAnti hlt (lt_top_iff_ne_top.mpr hfin)
        rw [hcx] at this
        exact absurd hcy (not_le.mpr this)
      rw [hyeq] at hy
      exact fun w hw => (isGenericPoint_def.mp hy) ▸ subset_closure hw

end FlagAdjunction

/-! ### The final stratum of a flag on a dlt pair -/

section Flag

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)} {B : QDivisor X}

/-- A prime divisor with coefficient at least one in the boundary of a dlt pair is a dlt
stratum. -/
private theorem isDltStratum_support (hB : MMP.Intersection.IsDltPair sX B)
    (P : Mori.PrimeDivisor X) (hP : 1 ≤ B.coeff P) : IsDltStratum sX B (P.support : Set X) := by
  have hinter : (⋂ Q ∈ ({P} : Finset (Mori.PrimeDivisor X)), (Q.support : Set X)) =
      (P.support : Set X) := by simp
  refine ⟨hB, {P}, Finset.singleton_nonempty P, by simpa using hP, ?_, ?_⟩
  · rw [hinter]
    exact ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  · rw [hinter]
    refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure

/-- **The final stratum of a flag of positive length on a dlt pair is a dlt stratum.** -/
private theorem isDltStratum_range_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    (hB : MMP.Intersection.IsDltPair sX B) {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) (hF : 0 < F.length) :
    IsDltStratum sX B (Set.range ι.base) := by
  cases F with
  | refl h => simp [StratumAdjunctionData.length] at hF
  | step F₀ j BT hj =>
    by_cases h0 : F₀.length = 0
    · cases F₀ with
      | refl h =>
        obtain ⟨-, P, hP1, hPr, -⟩ := hj
        have hr : Set.range (j ≫ 𝟙 X).base = (P.support : Set X) := by
          rwa [Category.comp_id]
        rw [hr]
        exact isDltStratum_support hB P hP1
      | step => simp [StratumAdjunctionData.length] at h0
    · exact isDltStratum_range_step hB F₀ hj h0

/-- The generic point of the final stratum of a flag on a dlt pair lies outside the exceptional
set of a small morphism, provided no dlt stratum lies in that exceptional set. -/
private theorem genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData [IsAlgClosed k]
    [CharZero k] {Z : Scheme.{0}} {f : X ⟶ Z} (h2 : 2 ≤ closedsCodimension (exceptionalSet f))
    (hB : MMP.Intersection.IsDltPair sX B)
    (hstrata : ∀ T : Set X, IsDltStratum sX B T → ¬ T ⊆ (exceptionalSet f : Set X))
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    ι (genericPoint S) ∉ (exceptionalSet f : Set X) := by
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  intro hmem
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · cases F with
    | refl h =>
      have h2x := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 hmem
      have hmaxX : IsMax ((𝟙 X : X ⟶ X) (genericPoint X)) := fun z _ ↦ genericPoint_specializes z
      rw [Order.coheight_eq_zero.mpr hmaxX] at h2x
      exact absurd h2x (by decide)
    | step => simp [StratumAdjunctionData.length] at h0
  · refine hstrata _ (isDltStratum_range_of_stratumAdjunctionData hB F hpos) ?_
    rintro _ ⟨s, rfl⟩
    have hsp : ι (genericPoint S) ⤳ ι s := (genericPoint_specializes s).map ι.base.hom.continuous
    exact hsp.mem_closed (exceptionalSet f).isClosed hmem

end Flag

/-! ### Consequences for flags -/

section FlagFacts

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}

/-- **The pairs along a flag of a dlt pair are dlt.** Each step is adjunction to a prime divisor
of coefficient one, which is a boundary stratum, so dlt adjunction applies step by step. -/
private theorem isDltPair_of_stratumAdjunctionData (hB : MMP.Intersection.IsDltPair sX B)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    MMP.Intersection.IsDltPair (ι ≫ sX) BS := by
  induction F with
  | refl h => simpa using hB
  | @step S T ι BS F j BT h ih =>
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsIntegral T := h.1.1.toIsIntegral
    haveI : IsNormal T := h.1.2
    haveI : IsLocallyNoetherian T := by
      have := h.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    have h' : IsAdjunctionStep (𝟙 S ≫ ι ≫ sX) BS j BT := by rwa [Category.id_comp]
    obtain ⟨-, P, hP, hrange, -⟩ := h
    let F' : StratumAdjunctionData (ι ≫ sX) BS (j ≫ 𝟙 S) BT := .step (.refl ih.1.1) j BT h'
    simpa using (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
      (isDltStratum_support ih P hP)).1.2 F' (by simpa using hrange)

/-- **Concatenation of flags.** A flag of `(X, B)` ending at `(S, B_S)` followed by a flag of
`(S, B_S)` is a flag of `(X, B)`, whose length is the sum of the lengths. -/
private theorem exists_length_eq_append {S : Scheme.{0}} [IsLocallyNoetherian S] [IsNormal S]
    {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) {T : Scheme.{0}}
    {j : T ⟶ S} {BT : QDivisor T} (G : StratumAdjunctionData (ι ≫ sX) BS j BT) :
    ∃ F' : StratumAdjunctionData sX B (j ≫ ι) BT, F'.length = F.length + G.length := by
  induction G with
  | refl h =>
    rw [Category.id_comp]
    exact ⟨F, rfl⟩
  | @step S₀ T₀ j₀ BS₀ G₀ j' BT' h ih =>
    obtain ⟨F₀, hF₀⟩ := ih
    have h' : IsAdjunctionStep ((j₀ ≫ ι) ≫ sX) BS₀ j' BT' := by rwa [Category.assoc]
    rw [Category.assoc]
    exact ⟨.step F₀ j' BT' h', by simp [StratumAdjunctionData.length, hF₀]; omega⟩

/-- Under the hypotheses of `genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData` the
stalk map `𝒪_{Z, y} ⟶ k(S)` at the generic point of the stratum is surjective: `f` is an
isomorphism there and `ι` is a closed immersion. -/
private theorem surjective_stalkMap_genericPoint {Z : Scheme.{0}} {f : X ⟶ Z}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (hB : MMP.Intersection.IsDltPair sX B)
    (hstrata : ∀ T : Set X, IsDltStratum sX B T → ¬ T ⊆ (exceptionalSet f : Set X))
    {S : Scheme.{0}} [IsIntegral S] {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) :
    Function.Surjective ((ι ≫ f).stalkMap (genericPoint S)).hom := by
  have := F.isClosedImmersion
  have hx := genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData h2 hB hstrata F
  rw [SetLike.mem_coe, mem_exceptionalSet, not_not] at hx
  have := isIso_stalkMap_of_mem_biregularLocus f hx
  rw [Scheme.Hom.stalkMap_comp]
  exact (ι.stalkMap_surjective _).comp
    (ConcreteCategory.bijective_of_isIso (f.stalkMap (ι (genericPoint S)))).2

end FlagFacts

open scoped WithZero in
/-- Valuations of a field which agree through a surjective ring map are equal. -/
private theorem valuation_eq_of_comap_eq {A K : Type*} [CommRing A] [Field K] {s : A →+* K}
    (hs : Function.Surjective s) {v w : Valuation K ℤᵐ⁰} (h : v.comap s = w.comap s) : v = w := by
  ext x
  obtain ⟨a, rfl⟩ := hs x
  exact DFunLike.congr_fun h a

/-- Prime divisors of a normal variety with the same valuation are equal. -/
private theorem eq_of_valuation_ofPrimeDivisor_eq {k : Type} [Field k] {S : Scheme.{0}}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of k)}
    (hS : IsNormalVariety k sS) {P Q : Mori.PrimeDivisor S}
    (h : (DivisorOver.ofPrimeDivisor k hS P).valuation =
      (DivisorOver.ofPrimeDivisor k hS Q).valuation) : P = Q :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hS h)

/-! ### Flips in the two senses -/

/-- A `(K + B)`-flip in the sense of `MMP.Fourfold.IsFlipOf` is a `(K + B)`-flip in the sense of
`MMP.Mori.IsFlip`. -/
private theorem isFlip_of_isFlipOf {k : Type} [Field k] {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace X'] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hK : K.IsCanonicalDivisor sX n) (h : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp) :
    Mori.IsFlip sX sZ sX' K B f fp := by
  have hc := h.isContraction
  have hs := h.isSmallMorphism
  have hsp := h.isSmallMorphism_flip
  have htr : Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B =
      flipTransform f fp (Divisor.toQDivisor K + B) := by
    rw [map_add, MMP.Mori.flipTransform_toQDivisor]
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := hc.isNormalVariety_source
          isNormalVariety_target := hc.isNormalVariety_target
          comp_eq := hc.comp_eq
          isCanonicalDivisor := ⟨n, hK⟩
          isQCartier := h.isQCartier
          isProper := hs.isProper
          isBirationalMorphism := hs.isBirationalMorphism
          two_le_codimension := hs.two_le_codimension
          hasRelativelyAmpleMultiple := h.hasRelativelyAmpleMultiple }
      isNormalVariety := hsp.isNormalVariety_source
      comp_eq := hsp.comp_eq
      isProper := hsp.isProper
      isBirationalMorphism := hsp.isBirationalMorphism
      isQCartier := htr ▸ h.isQCartier_flip
      hasRelativelyAmpleMultiple := htr ▸ h.hasRelativelyAmpleMultiple_flip
      two_le_codimension := hsp.two_le_codimension }

/-- In `WithBot ℕ∞`, `a + 1 ≤ d` for a natural number `d` gives `a < d`. -/
private theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {d : ℕ} (h : a + 1 ≤ d) : a < d := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by
        rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) from rfl]
        exact not_le.mpr (WithBot.coe_lt_coe.mpr (ENat.coe_lt_top d)))
    | coe n =>
      have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ d := by exact_mod_cast h
      exact_mod_cast (show n < d by exact_mod_cast this)

/-! ### Prime divisors over the common image -/

/-- A morphism from a reduced scheme whose image lies in the image of a closed immersion factors
through it. -/
private theorem exists_lift_of_range_subset {X Y S : Scheme.{0}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (g : Y ⟶ X) [QuasiCompact g] [IsReduced Y] (hg : Set.range g ⊆ Set.range ι) :
    ∃ l : Y ⟶ S, l ≫ ι = g := by
  have hrad : g.ker.radical = g.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    rw [RingHom.mem_ker]
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  have hsupp : g.ker.support ≤ ι.ker.support := by
    show (g.ker.support : Set X) ⊆ ι.ker.support
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
    exact closure_mono hg
  have H : ι.ker ≤ g.ker :=
    calc ι.ker ≤ ι.ker.radical := Scheme.IdealSheafData.le_radical _
      _ = Scheme.IdealSheafData.vanishingIdeal ι.ker.support :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
      _ ≤ Scheme.IdealSheafData.vanishingIdeal g.ker.support :=
        Scheme.IdealSheafData.vanishingIdeal_antimono hsupp
      _ = g.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
      _ = g.ker := hrad
  exact ⟨IsClosedImmersion.lift ι g H, IsClosedImmersion.lift_fac _ _ _⟩

/-- The closure of a point of a scheme, with its reduced structure, is an integral closed
subscheme whose generic point lies over the given point. -/
private theorem exists_isIntegral_closure_singleton {W : Scheme.{0}} (w₀ : W) :
    ∃ (F : Scheme.{0}) (h : F ⟶ W) (_ : IsIntegral F) (_ : IsClosedImmersion h),
      Set.range h = closure {w₀} ∧ h (genericPoint F) = w₀ := by
  set Z : Closeds W := ⟨closure {w₀}, isClosed_closure⟩
  have hZ : IsIrreducible (Z : Set W) := isIrreducible_singleton.closure
  haveI := MMP.Fourfold.isIntegral_subscheme_vanishingIdeal Z hZ
  have hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = closure {w₀} := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨_, (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι, inferInstance, inferInstance,
    hr, ?_⟩
  have h1 := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal Z).subscheme).image
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base.hom.continuous
  rw [Set.image_univ, hr, closure_closure] at h1
  exact h1.eq isGenericPoint_closure

/-- The stalk map at the generic point of a composite, read through the extension of function
fields of the first factor. -/
private theorem stalkMap_comp_genericPoint_apply {S T Z : Scheme.{0}} [IsIntegral S]
    [IsIntegral T] (g : S ⟶ T) [IsDominant g] (h : T ⟶ Z)
    (a : Z.presheaf.stalk ((g ≫ h) (genericPoint S))) :
    ((g ≫ h).stalkMap (genericPoint S)).hom a =
      functionFieldMap g (algebraMap (T.presheaf.stalk (g (genericPoint S))) T.functionField
        ((h.stalkMap (g (genericPoint S))).hom a)) := by
  rw [functionFieldMap_algebraMap_stalk g (genericPoint S), Scheme.Hom.stalkMap_comp]
  simp only [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Germs at equal points have equal images in the function field. -/
private theorem algebraMap_stalkMap_congr {T Z : Scheme.{0}} [IsIntegral T] (h : T ⟶ Z)
    {t₁ t₂ : T} (ht : t₁ = t₂) (hz : h t₁ = h t₂) (a : Z.presheaf.stalk (h t₁)) :
    algebraMap (T.presheaf.stalk t₁) T.functionField ((h.stalkMap t₁).hom a) =
      algebraMap (T.presheaf.stalk t₂) T.functionField
        ((h.stalkMap t₂).hom ((Z.presheaf.stalkCongr (.of_eq hz)).hom.hom a)) := by
  subst ht
  simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]

/-- Cancellation in `dim closure {x} + coheight x = dim X`: a larger finite first summand has a
smaller second summand. -/
private theorem coheight_le_of_add_eq {a b : WithBot ℕ∞} {c d : ℕ∞}
    (h : a + c = b + d) (hba : b ≤ a) (ha : a ≠ ⊤) (ha' : a ≠ ⊥) : c ≤ d := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha'
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd rfl ha
    | coe m =>
      induction b using WithBot.recBotCoe with
      | bot =>
        exfalso
        rw [WithBot.bot_add] at h
        exact WithBot.coe_ne_bot (by rwa [← WithBot.coe_add] at h)
      | coe b =>
        rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
        have hb : b ≤ m := by exact_mod_cast hba
        induction d using ENat.recTopCoe with
        | top => exact le_top
        | coe d =>
          induction b using ENat.recTopCoe with
          | top => exact absurd (top_le_iff.mp hb) (ENat.natCast_ne_top m)
          | coe b =>
            induction c using ENat.recTopCoe with
            | top => exact absurd h (by rw [add_top]; exact (WithTop.add_ne_top.mpr
                ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top _⟩).symm)
            | coe c =>
              have h' : m + c = b + d := by exact_mod_cast h
              have hb' : b ≤ m := by exact_mod_cast hb
              exact_mod_cast (show c ≤ d by omega)

/-- A closed embedding preserves the dimension of the closure of a point. -/
private theorem topologicalKrullDim_closure_image {T T' : Type*} [TopologicalSpace T]
    [TopologicalSpace T'] {e : T → T'} (he : Topology.IsClosedEmbedding e) (t : T) :
    topologicalKrullDim (closure {e t} : Set T') = topologicalKrullDim (closure {t} : Set T) := by
  rw [← Set.image_singleton, he.closure_image_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (he.isEmbedding.homeomorphImage (closure {t})).isHomeomorph).symm

/-- Divisors over `X`, `X'` whose valuations agree on `k(Y)` have the same center on `Y`. -/
private theorem map_genericPoint_eq_of_valuation_comap_eq {k : Type} [Field k]
    {X X' Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [IsIntegral X] [IsIntegral X'] [IsIntegral Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) [IsDominant f] [IsDominant f'] (D : DivisorOver k sX)
    (D' : DivisorOver k sX')
    (h : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f')) :
    f (D.f D.E.genericPoint) = f' (D'.f D'.E.genericPoint) := by
  have dom : ∀ {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)} [IsIntegral W] (g : W ⟶ Y) [IsDominant g]
      (E : DivisorOver k sW),
      (∀ a : Y.presheaf.stalk (g (E.f E.E.genericPoint)),
        E.valuation.comap (functionFieldMap g) (algebraMap _ Y.functionField a) ≤ 1) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g (E.f E.E.genericPoint))),
        E.valuation.comap (functionFieldMap g) (algebraMap _ Y.functionField a) < 1) := by
    intro W sW _ g _ E
    refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E _ rfl _
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E _ rfl _ ?_
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu ↦
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
  obtain ⟨h1, h2⟩ := dom f D
  obtain ⟨h1', h2'⟩ := dom f' D'
  rw [← h] at h1' h2'
  exact MMP.Positivity.DivisorOver.eq_of_dominates sY _ h1 h2 h1' h2'

section CommonImage

variable {k : Type} [Field k] {S S' Z : Scheme.{0}}
  [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S']
  [IsNormal S'] {sS : S ⟶ Spec (.of k)} {sS' : S' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
  (hS : IsNormalVariety k sS) (hS' : IsNormalVariety k sS')
  (ψ : S ⟶ Z) (ψ' : S' ⟶ Z) [IsProper ψ] [QuasiCompact ψ']
  (hψ : ψ ≫ sZ = sS) (hψ' : ψ' ≫ sZ = sS')
  (hy : ψ (genericPoint S) = ψ' (genericPoint S'))
  (hs : Function.Surjective (ψ.stalkMap (genericPoint S)).hom)
  (hs' : Function.Surjective (ψ'.stalkMap (genericPoint S')).hom)

include hS hS' hψ hψ' hy hs hs'

/-- **The common image.** For proper `ψ : S ⟶ Z` and quasi-compact `ψ' : S' ⟶ Z` from normal
varieties, sending the generic points to the same point `y` with surjective stalk maps there, the
closure `T` of `y` with its reduced structure is an integral closed subscheme through which `ψ`
and `ψ'` factor by birational morphisms, the first one proper. -/
private theorem exists_commonImage :
    ∃ (T : Scheme.{0}) (h : T ⟶ Z) (g : S ⟶ T) (g' : S' ⟶ T) (_ : IsIntegral T)
      (_ : IsClosedImmersion h) (_ : IsProper g),
      g ≫ h = ψ ∧ g' ≫ h = ψ' ∧ IsBirationalMorphism g ∧ IsBirationalMorphism g' ∧
        g (genericPoint S) = genericPoint T ∧ g' (genericPoint S') = genericPoint T := by
  obtain ⟨T, h, hTi, hTc, hTr, hTg⟩ := exists_isIntegral_closure_singleton (ψ (genericPoint S))
  have hrange : ∀ {W : Scheme.{0}} [IrreducibleSpace W] (φ : W ⟶ Z),
      φ (genericPoint W) = ψ (genericPoint S) → Set.range φ ⊆ Set.range h := by
    intro W _ φ hφ
    rintro _ ⟨w, rfl⟩
    rw [hTr, ← hφ]
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes w).map φ.base.hom.continuous)
  obtain ⟨g, hg⟩ := exists_lift_of_range_subset h ψ (hrange ψ rfl)
  obtain ⟨g', hg'⟩ := exists_lift_of_range_subset h ψ' (hrange ψ' hy.symm)
  subst hg hg'
  have hgη : g (genericPoint S) = genericPoint T :=
    h.isClosedEmbedding.injective (by rw [hTg]; rfl)
  have hg'η : g' (genericPoint S') = genericPoint T :=
    h.isClosedEmbedding.injective (by rw [hTg]; exact hy.symm)
  have hdom : ∀ {W : Scheme.{0}} [IrreducibleSpace W] (φ : W ⟶ T),
      φ (genericPoint W) = genericPoint T → IsDominant φ := by
    intro W _ φ hφ
    refine ⟨Dense.mono (Set.singleton_subset_iff.mpr ⟨_, hφ⟩) ?_⟩
    rw [dense_iff_closure_eq]
    exact genericPoint_spec T
  haveI := hdom g hgη
  haveI := hdom g' hg'η
  haveI : IsProper g := IsProper.of_comp g h
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g h
  have hsurj : ∀ {W : Scheme.{0}} [IsIntegral W] (φ : W ⟶ T) [IsDominant φ],
      Function.Surjective ((φ ≫ h).stalkMap (genericPoint W)).hom →
        Function.Surjective (functionFieldMap φ) := by
    intro W _ φ _ hφ u
    obtain ⟨a, rfl⟩ := hφ u
    exact ⟨_, (stalkMap_comp_genericPoint_apply φ h a).symm⟩
  have hgb : IsBirationalMorphism g :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational g
      (isBirational_of_surjective_functionFieldMap g (hsurj g hs))
  haveI : LocallyOfFiniteType ((g' ≫ h) ≫ sZ) := by
    rw [hψ']; exact hS'.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType g' := by
    haveI : LocallyOfFiniteType (g' ≫ h) := locallyOfFiniteType_of_comp _ sZ
    exact locallyOfFiniteType_of_comp g' h
  have hg'b : IsBirationalMorphism g' :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational g'
      (isBirational_of_surjective_functionFieldMap g' (hsurj g' hs'))
  exact ⟨T, h, g, g', hTi, hTc, inferInstance, rfl, rfl, hgb, hg'b, hgη, hg'η⟩

/-- **Divisors over `S'` are divisors over `S`**, read on `𝒪_{Z, y}`: every divisor `D'` over
`S'` has the valuation of a divisor `D` over `S` on `𝒪_{Z, y}`, and their centres have the same
image in `Z`. -/
private theorem exists_divisorOver_valuation_comap_stalkMap_eq (D' : DivisorOver k sS') :
    ∃ D : DivisorOver k sS,
      D.valuation.comap (ψ.stalkMap (genericPoint S)).hom =
        D'.valuation.comap
          ((Z.presheaf.stalkCongr (.of_eq hy)).hom ≫ ψ'.stalkMap (genericPoint S')).hom ∧
      ψ (D.f D.E.genericPoint) = ψ' (D'.f D'.E.genericPoint) := by
  obtain ⟨T, h, g, g', hTi, hTc, hgp, hg, hg', hgb, hg'b, hgη, hg'η⟩ :=
    exists_commonImage hS hS' ψ ψ' hψ hψ' hy hs hs'
  subst hg hg'
  haveI := hgb.isDominant
  haveI := hg'b.isDominant
  have e : g ≫ h ≫ sZ = sS := by rwa [← Category.assoc]
  have e' : g' ≫ h ≫ sZ = sS' := by rwa [← Category.assoc]
  have hX : IsNormalVariety k (g ≫ h ≫ sZ) := by rwa [e]
  let D'' : DivisorOver k (g' ≫ h ≫ sZ) :=
    ⟨D'.Y, D'.f, by rw [e']; exact D'.isNormalVariety, D'.isBirationalMorphism, D'.E⟩
  obtain ⟨D, hD⟩ := MMP.Mori.exists_divisorOver_valuation_comap_eq (sY := h ≫ sZ) hX hgb hg'b D''
  let D₀ : DivisorOver k sS :=
    ⟨D.Y, D.f, by rw [← e]; exact D.isNormalVariety, D.isBirationalMorphism, D.E⟩
  have hc : g (D.f D.E.genericPoint) = g' (D'.f D'.E.genericPoint) :=
    map_genericPoint_eq_of_valuation_comap_eq (h ≫ sZ) g g' D D'' hD
  refine ⟨D₀, ?_, by
    change h (g (D.f D.E.genericPoint)) = h (g' (D'.f D'.E.genericPoint))
    rw [hc]⟩
  ext a
  have e1 := stalkMap_comp_genericPoint_apply g h a
  have e2 := stalkMap_comp_genericPoint_apply g' h ((Z.presheaf.stalkCongr (.of_eq hy)).hom.hom a)
  have e3 := algebraMap_stalkMap_congr h (hgη.trans hg'η.symm) hy a
  have e4 := DFunLike.congr_fun hD (algebraMap (T.presheaf.stalk (g (genericPoint S)))
    T.functionField ((h.stalkMap (g (genericPoint S))).hom a))
  simp only [Valuation.comap_apply] at e4
  simp only [Valuation.comap_apply, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e1, e2]
  refine e4.trans ?_
  exact congrArg (fun u => D'.valuation (functionFieldMap g' u)) e3

/-- **A divisor not contracted to the common image is a divisor on both sides.** A prime divisor
`P'` of `S'` whose image in `Z` has closure of dimension at least `dim P'` has, on `𝒪_{Z, y}`, the
valuation of a prime divisor `P` of `S`. -/
private theorem exists_valuation_comap_eq_of_not_lt (P' : Mori.PrimeDivisor S')
    (hP' : ¬ topologicalKrullDim (closure {ψ' P'.genericPoint} : Set Z) <
      topologicalKrullDim (closure {P'.genericPoint} : Set S')) :
    ∃ P : Mori.PrimeDivisor S,
      (DivisorOver.ofPrimeDivisor k hS P).valuation.comap (ψ.stalkMap (genericPoint S)).hom =
        (DivisorOver.ofPrimeDivisor k hS' P').valuation.comap
          ((Z.presheaf.stalkCongr (.of_eq hy)).hom ≫ ψ'.stalkMap (genericPoint S')).hom := by
  obtain ⟨D, hD, hDc⟩ := exists_divisorOver_valuation_comap_stalkMap_eq hS hS' ψ ψ' hψ hψ' hy hs
    hs' (DivisorOver.ofPrimeDivisor k hS' P')
  obtain ⟨P, hP⟩ : ∃ P : Mori.PrimeDivisor S,
      D.valuation = (DivisorOver.ofPrimeDivisor k hS P).valuation := by
    by_contra hne
    push Not at hne
    have h2 := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hS D).mpr hne
    rw [MMP.Positivity.DivisorOver.codimension_center] at h2
    obtain ⟨T, h, g, g', hTi, hTc, hgp, hg, hg', hgb, hg'b, hgη, hg'η⟩ :=
      exists_commonImage hS hS' ψ ψ' hψ hψ' hy hs hs'
    subst hg hg'
    have hc : g (D.f D.E.genericPoint) = g' P'.genericPoint :=
      h.isClosedEmbedding.injective hDc
    have : LocallyOfFiniteType sZ := inferInstance
    haveI : MMP.Mori.IsVariety k (h ≫ sZ) := ⟨⟩
    haveI : MMP.Mori.IsVariety k sS := hS.1
    haveI : MMP.Mori.IsVariety k sS' := hS'.1
    have hdim : topologicalKrullDim T = topologicalKrullDim S :=
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (h ≫ sZ) sS hgb
    have hdim' : topologicalKrullDim T = topologicalKrullDim S' :=
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (h ≫ sZ) sS' hg'b
    have hmap := MMP.Flips.coheight_le_coheight_map (h ≫ sZ) sS ‹_› ‹_› g
      (by rw [← Category.assoc]; exact hψ) hdim.symm (D.f D.E.genericPoint)
    have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (h ≫ sZ)
    have : LocallyOfFiniteType sS' := hS'.1.toLocallyOfFiniteType
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (h ≫ sZ)
      (g' P'.genericPoint)
    have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS' P'.genericPoint
    rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h3
    have hcl := topologicalKrullDim_closure_image h.isClosedEmbedding (g' P'.genericPoint)
    have hle : topologicalKrullDim (closure {P'.genericPoint} : Set S') ≤
        topologicalKrullDim (closure {g' P'.genericPoint} : Set T) := by
      rw [← hcl]; exact not_lt.mp hP'
    have hne : topologicalKrullDim (closure {g' P'.genericPoint} : Set T) ≠ ⊥ := by
      rw [topologicalKrullDim_closure_singleton_eq_trdeg k T (h ≫ sZ)]
      exact WithBot.coe_ne_bot
    have hnt : topologicalKrullDim (closure {g' P'.genericPoint} : Set T) ≠ ⊤ := by
      intro htop
      have := topologicalKrullDim_ne_top_of_locallyOfFiniteType k (h ≫ sZ)
      rw [← h1, htop] at this
      exact this (by rw [show (⊤ : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) from rfl,
        ← WithBot.coe_add, top_add])
    have hct : Order.coheight (g' P'.genericPoint) ≤ 1 :=
      coheight_le_of_add_eq (h1.trans (hdim'.trans h3.symm)) hle hnt hne
    have := h2.trans (hmap.trans (hc ▸ hct))
    exact absurd this (by decide)
  exact ⟨P, hP ▸ hD⟩

end CommonImage

/-! ### Counting along a correspondence -/

/-- A set `B` each of whose elements is in correspondence with an element of `A`, the
correspondence being injective, has at most as many elements as `A`. -/
private theorem encard_le_of_forall_exists {α β : Type*} {A : Set α} {B : Set β}
    (R : α → β → Prop) (hR : ∀ b ∈ B, ∃ a ∈ A, R a b)
    (hinj : ∀ a b b', R a b → R a b' → b = b') : B.encard ≤ A.encard := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · simp
  haveI : Nonempty α := ⟨(hR b₀ hb₀).choose⟩
  choose! g hgA hgR using hR
  exact Set.encard_le_encard_of_injOn (fun b hb => hgA b hb)
    (fun b hb b' hb' h => hinj _ _ _ (hgR b hb) (h ▸ hgR b' hb'))

/-- The same, strictly, if `A` is finite and some element of `A` corresponds to no element of
`B`. -/
private theorem encard_lt_of_forall_exists {α β : Type*} {A : Set α} {B : Set β}
    (R : α → β → Prop) (hR : ∀ b ∈ B, ∃ a ∈ A, R a b)
    (hinj : ∀ a b b', R a b → R a b' → b = b') {a₀ : α} (ha₀ : a₀ ∈ A)
    (h₀ : ∀ b ∈ B, ¬ R a₀ b) (hA : A.encard ≠ ⊤) : B.encard < A.encard := by
  haveI : Nonempty α := ⟨a₀⟩
  choose! g hgA hgR using hR
  have h1 : B.encard ≤ (A \ {a₀}).encard :=
    Set.encard_le_encard_of_injOn
      (fun b hb => ⟨hgA b hb, fun h => h₀ b hb (by rw [← Set.mem_singleton_iff.mp h]; exact hgR b hb)⟩)
      (fun b hb b' hb' h => hinj _ _ _ (hgR b hb) (h ▸ hgR b' hb'))
  have h2 := Set.encard_diff_singleton_add_one ha₀
  have h3 : (A \ {a₀}).encard ≠ ⊤ := fun h => hA (by rw [← h2, h, top_add])
  calc B.encard ≤ (A \ {a₀}).encard := h1
    _ < (A \ {a₀}).encard + 1 := (ENat.lt_add_one_iff h3).mpr le_rfl
    _ = A.encard := h2

/-- Every family in `ℕ∞` is summable. -/
private theorem summable_enat {ι : Type*} (φ : ι → ℕ∞) : Summable φ :=
  (hasSum_of_isLUB _ (isLUB_sSup _)).summable

/-- A sum in `ℕ∞` of a pointwise smaller family, strictly smaller at one index, is strictly
smaller when the larger sum is finite. -/
private theorem tsum_lt_tsum_of_lt {ι : Type*} {φ ψ : ι → ℕ∞} (hle : ∀ i, φ i ≤ ψ i) {i : ι}
    (hlt : φ i < ψ i) (hψ : ∑' j, ψ j ≠ ⊤) : ∑' j, φ j < ∑' j, ψ j := by
  classical
  have eφ := Summable.tsum_eq_add_tsum_ite' (f := φ) i (summable_enat _)
  have eψ := Summable.tsum_eq_add_tsum_ite' (f := ψ) i (summable_enat _)
  rw [eψ] at hψ
  rw [eφ, eψ]
  have h1 : ∑' j, (if j = i then 0 else φ j) ≤ ∑' j, (if j = i then 0 else ψ j) :=
    Summable.tsum_le_tsum (fun j => by split_ifs <;> simp [hle j]) (summable_enat _)
      (summable_enat _)
  have h2 : ∑' j, (if j = i then 0 else ψ j) ≠ ⊤ := fun h => hψ (by rw [h, add_top])
  calc φ i + ∑' j, (if j = i then 0 else φ j) ≤ φ i + ∑' j, (if j = i then 0 else ψ j) :=
        add_le_add_right h1 _
    _ < ψ i + ∑' j, (if j = i then 0 else ψ j) := (ENat.add_lt_add_iff_right h2).mpr hlt

/-- A point of the support of `⌊B⌋`, for `B` with coefficients in `[0, 1]`, lies on a prime
divisor of coefficient one. -/
private theorem exists_coeff_eq_one_of_mem_supp_roundDown {S : Scheme.{0}} {BS : QDivisor S}
    (h0 : ∀ P, 0 ≤ BS.coeff P) (h1 : ∀ P, BS.coeff P ≤ 1) {x : S}
    (hx : x ∈ (DivisorWithCoeffs.roundDown BS).supp) :
    ∃ Q : Mori.PrimeDivisor S, BS.coeff Q = 1 ∧ x ∈ (Q.support : Set S) := by
  obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  refine ⟨Q, ?_, hxQ⟩
  rw [DivisorWithCoeffs.coeff_roundDown] at hQ
  refine le_antisymm (h1 Q) (not_lt.mp fun hlt => hQ ?_)
  exact Int.floor_eq_zero_iff.mpr ⟨h0 Q, hlt⟩

/-- The support of a prime divisor of coefficient one lies in the support of `⌊B⌋`. -/
private theorem support_subset_supp_roundDown {S : Scheme.{0}} {BS : QDivisor S}
    {Q : Mori.PrimeDivisor S} (hQ : BS.coeff Q = 1) :
    (Q.support : Set S) ⊆ (DivisorWithCoeffs.roundDown BS).supp := fun x hx =>
  DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, by rw [DivisorWithCoeffs.coeff_roundDown, hQ]; simp, hx⟩

/-- Over the biregular locus a morphism is injective. -/
private theorem eq_of_apply_eq_of_mem_biregularLocus {X Y : Scheme.{0}} (g : X ⟶ Y) {x y : X}
    (hx : g x ∈ biregularLocus g) (hxy : g x = g y) : x = y := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hy : g y ∈ biregularLocus g := hxy ▸ hx
  let a : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨x, hx⟩
  let b : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨y, hy⟩
  have hab : ((g ∣_ biregularLocus g) ≫ (biregularLocus g).ι) a =
      ((g ∣_ biregularLocus g) ≫ (biregularLocus g).ι) b := by
    rw [morphismRestrict_ι]; exact hxy
  have := ((g ∣_ biregularLocus g) ≫ (biregularLocus g).ι).isOpenEmbedding.injective hab
  exact congrArg Subtype.val this

/-! ### A contracted divisor maps outside the biregular locus -/

section Contracted

variable {k : Type} [Field k]

/-- Cancellation in `WithBot ℕ∞` of a finite summand. -/
private theorem eq_of_add_eq_add_of_ne_top {a b : WithBot ℕ∞} {c : ℕ∞} (hc : c ≠ ⊤)
    (h : a + c = b + c) : a = b := by
  induction c using ENat.recTopCoe with
  | top => exact absurd rfl hc
  | coe c =>
    induction a using WithBot.recBotCoe with
    | bot =>
      induction b using WithBot.recBotCoe with
      | bot => rfl
      | coe b =>
        rw [WithBot.bot_add, ← WithBot.coe_add] at h
        exact absurd h.symm WithBot.coe_ne_bot
    | coe a =>
      induction b using WithBot.recBotCoe with
      | bot =>
        rw [WithBot.bot_add, ← WithBot.coe_add] at h
        exact absurd h WithBot.coe_ne_bot
      | coe b =>
        rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
        exact congrArg _ (WithTop.add_right_cancel (ENat.coe_ne_top c) h)

/-- **A point over the biregular locus has a closure of the same dimension as its image.** For a
birational morphism `g : X ⟶ Y` of varieties and a point `x` with `g x` in the biregular locus,
`dim closure {g x} = dim closure {x}`. -/
private theorem topologicalKrullDim_closure_map_of_mem_biregularLocus {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (hX : AlgebraicGeometry.IsVariety k sX)
    (hY : AlgebraicGeometry.IsVariety k sY)
    {g : X ⟶ Y} (hg : IsBirationalMorphism g) {x : X} (hx : g x ∈ biregularLocus g) :
    topologicalKrullDim (closure {g x} : Set Y) = topologicalKrullDim (closure {x} : Set X) := by
  have := hX.toIsIntegral
  have := hY.toIsIntegral
  have := hX.toLocallyOfFiniteType
  have := hY.toLocallyOfFiniteType
  have hdim : topologicalKrullDim Y = topologicalKrullDim X :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := k) sY sX hg
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (g x)
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus g hx] at h2
  have := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hne : topologicalKrullDim (closure {x} : Set X) ≠ ⊥ := by
    rw [topologicalKrullDim_closure_singleton_eq_trdeg k X sX]
    exact WithBot.coe_ne_bot
  have hc : Order.coheight x ≠ ⊤ := by
    intro htop
    have := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
    rw [← h1, htop] at this
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hne
    exact this (by rw [← ha, ← WithBot.coe_add, add_top]; rfl)
  exact eq_of_add_eq_add_of_ne_top hc (h2.trans (hdim.trans h1.symm))

/-- **A divisor of a stratum contracted by the flip maps outside the biregular locus.** Let
`g : X ⟶ Y` be a birational morphism of varieties and `ι : S ⟶ X` a closed immersion. If the
closure of the image `g (ι η_P)` of the generic point of a prime divisor `P` of `S` has smaller
dimension than `P`, then `g (ι η_P)` is not in the biregular locus of `g`. -/
private theorem map_notMem_biregularLocus_of_topologicalKrullDim_lt {X Y S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (hX : AlgebraicGeometry.IsVariety k sX)
    (hY : AlgebraicGeometry.IsVariety k sY) {g : X ⟶ Y} (hg : IsBirationalMorphism g)
    (ι : S ⟶ X) [IsClosedImmersion ι] (p : S)
    (hp : topologicalKrullDim (closure {(ι ≫ g).base p} : Set Y) <
      topologicalKrullDim (closure {p} : Set S)) :
    g (ι p) ∉ biregularLocus g := by
  intro hmem
  have h := topologicalKrullDim_closure_map_of_mem_biregularLocus hX hY hg hmem
  rw [topologicalKrullDim_closure_image ι.isClosedEmbedding] at h
  rw [Scheme.Hom.comp_base, TopCat.comp_app, h] at hp
  exact lt_irrefl _ hp

end Contracted

/-! ### One flip of a corresponding pair of strata -/

section Step

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X X' Z : Scheme.{0}}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  {f : X ⟶ Z} {fp : X' ⟶ Z} {n : ℕ} {K : Divisor X} {B : QDivisor X} {B' : QDivisor X'}
  (hX : Mori.IsProjectiveVariety k sX) (hX' : Mori.IsProjectiveVariety k sX')
  (hB : MMP.Intersection.IsDltPair sX B) (hB' : MMP.Intersection.IsDltPair sX' B')
  (hK : K.IsCanonicalDivisor sX n)
  (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
  (hBflip : B' = flipTransform f fp B)
  (hstrata : ∀ T : Set X, IsDltStratum sX B T → ¬ T ⊆ (exceptionalSet f : Set X))
  (hstrata' : ∀ T : Set X', IsDltStratum sX' B' T → ¬ T ⊆ (exceptionalSet fp : Set X'))
  {d : ℕ}
  (hlow : ∀ T : Set X, IsDltStratum sX B T → topologicalKrullDim T < d →
    Disjoint T (exceptionalSet f : Set X))
  (hlow' : ∀ T' : Set X', IsDltStratum sX' B' T' → topologicalKrullDim T' < d →
    Disjoint T' (exceptionalSet fp : Set X'))
  {S S' : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
  {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
  (hS : IsStratumAdjunctionPair sX B ι BS) (hS' : IsStratumAdjunctionPair sX' B' ι' BS')
  (hdim : topologicalKrullDim S ≤ d) (hdim' : topologicalKrullDim S' ≤ d)
  (hcorr : (ι ≫ f).base (genericPoint S) = (ι' ≫ fp).base (genericPoint S'))

/-- A prime divisor `P` of `S` and a prime divisor `P'` of `S'` are the same divisor of
`k(S) ≅ k(S')`: their valuations agree on `𝒪_{Z, y}`, `y` the common image of the generic
points. -/
private abbrev IsSameDivisor (P : Mori.PrimeDivisor S) (P' : Mori.PrimeDivisor S') : Prop :=
  (DivisorOver.ofPrimeDivisor k hS.some.isNormalVariety P).valuation.comap
      ((ι ≫ f).stalkMap (genericPoint S)).hom =
    (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P').valuation.comap
      (((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
        (ι' ≫ fp).stalkMap (genericPoint S')).hom)

/-- `P'` is contracted by `S' ⟶ Z`: the closure of its image has smaller dimension. -/
private abbrev IsContractedDivisor (P' : Mori.PrimeDivisor S') : Prop :=
  topologicalKrullDim (closure {(ι' ≫ fp).base P'.genericPoint} : Set Z) <
    topologicalKrullDim (closure {P'.genericPoint} : Set S')

include hB hflip hstrata hS in
/-- `𝒪_{Z, y} → k(S)` is surjective: `f` is an isomorphism at the generic point of `S`. -/
private theorem surjective_stalkMap_left :
    Function.Surjective ((ι ≫ f).stalkMap (genericPoint S)).hom :=
  surjective_stalkMap_genericPoint hflip.isSmallMorphism.two_le_codimension hB hstrata hS.some

include hB' hflip hstrata' hS' in
/-- `𝒪_{Z, y} → k(S')`, read through `𝒪_{Z, (ι ≫ f) η_S} = 𝒪_{Z, (ι' ≫ f⁺) η_{S'}}`, is
surjective: `f⁺` is an isomorphism at the generic point of `S'`. -/
private theorem surjective_stalkMap_right :
    Function.Surjective (((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
      (ι' ≫ fp).stalkMap (genericPoint S')).hom) := by
  rw [CommRingCat.hom_comp]
  exact (surjective_stalkMap_genericPoint hflip.isSmallMorphism_flip.two_le_codimension hB'
    hstrata' hS'.some).comp (ConcreteCategory.bijective_of_isIso _).2

include hX hX' hB hB' hK hflip hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr

/-- **The floor of `B_{S'}` avoids the flipped locus.** A prime divisor `Q'` of `S'` with
coefficient one in `B_{S'}` is a lower boundary stratum of `(X', B')`, so it misses the
exceptional set of `f⁺`. -/
private theorem map_notMem_exceptionalSet_of_coeff_eq_one {Q' : Mori.PrimeDivisor S'}
    (hQ' : BS'.coeff Q' = 1) {q : S'} (hq : q ∈ (Q'.support : Set S')) :
    ι' q ∉ (exceptionalSet fp : Set X') := by
  subst hBflip
  have hd := isDltPair_of_stratumAdjunctionData hB' hS'.some
  obtain ⟨⟨⟨TQ, jQ, BTQ, hr, ⟨G⟩⟩, -⟩, -⟩ :=
    IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair (isDltStratum_support hd Q' hQ'.ge)
  have hG : G.length ≠ 0 := by
    intro h0
    cases G with
    | refl h =>
      exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support Q'
        (hr ▸ ⟨genericPoint S', rfl⟩)
    | step => simp [StratumAdjunctionData.length] at h0
  obtain ⟨F', hF'⟩ := exists_length_eq_append hS'.some G
  have hdimT : topologicalKrullDim TQ < d := by
    haveI := G.isClosedImmersion
    haveI := hS'.some.isNormalVariety.1.toLocallyOfFiniteType
    have e1 : topologicalKrullDim TQ = topologicalKrullDim (Set.range jQ.base) :=
      IsHomeomorph.topologicalKrullDim_eq _ jQ.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
    have e2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι' ≫ sX')
      Q'.genericPoint
    rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at e2
    rw [hr, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at e1
    refine lt_of_add_one_le_natCast ?_
    rw [e1]
    exact_mod_cast e2.le.trans hdim'
  have hrange := isDltStratum_range_of_stratumAdjunctionData hB' F' (by omega)
  have hdimR : topologicalKrullDim (Set.range (jQ ≫ ι').base) < d := by
    haveI := hS'.some.isClosedImmersion
    haveI := G.isClosedImmersion
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (jQ ≫ ι').isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph]
    exact hdimT
  have hav := hlow' _ hrange hdimR
  rw [← hr] at hq
  obtain ⟨t, rfl⟩ := hq
  exact Set.disjoint_left.mp hav ⟨t, rfl⟩

/-- **Divisors over `S'` are divisors over `S`**, on `𝒪_{Z, y}`, with centres over the same point
of `Z`. -/
private theorem exists_divisorOver_valuation_comap_eq_of_divisorOver
    (D' : DivisorOver k (ι' ≫ sX')) :
    ∃ D : DivisorOver k (ι ≫ sX),
      D.valuation.comap ((ι ≫ f).stalkMap (genericPoint S)).hom =
        D'.valuation.comap ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
          (ι' ≫ fp).stalkMap (genericPoint S')).hom ∧
      (ι ≫ f) (D.f D.E.genericPoint) = (ι' ≫ fp) (D'.f D'.E.genericPoint) := by
  have hc := hflip.isContraction
  have hZ := hc.isNormalVariety_target
  haveI := hZ.1.toIsSeparated
  haveI := hZ.1.toLocallyOfFiniteType
  haveI := hZ.1.toQuasiCompact
  haveI := hS.some.isClosedImmersion
  haveI := hS'.some.isClosedImmersion
  haveI : IsProper f := hflip.isSmallMorphism.isProper
  haveI : IsProper fp := hflip.isSmallMorphism_flip.isProper
  exact exists_divisorOver_valuation_comap_stalkMap_eq hS.some.isNormalVariety
    hS'.some.isNormalVariety (ι ≫ f) (ι' ≫ fp) (by rw [Category.assoc, hc.comp_eq])
    (by rw [Category.assoc, hflip.isSmallMorphism_flip.comp_eq]) hcorr
    (surjective_stalkMap_left hB hflip hstrata hS)
    (surjective_stalkMap_genericPoint hflip.isSmallMorphism_flip.two_le_codimension hB'
      hstrata' hS'.some) D'

/-- The same prime divisor on both sides has its generic points over the same point of `Z`. -/
private theorem map_genericPoint_eq_of_isSameDivisor {Q : Mori.PrimeDivisor S}
    {Q' : Mori.PrimeDivisor S'} (h : IsSameDivisor hS hS' hcorr Q Q') :
    (ι ≫ f) Q.genericPoint = (ι' ≫ fp) Q'.genericPoint := by
  obtain ⟨D, hDv, hDc⟩ := exists_divisorOver_valuation_comap_eq_of_divisorOver hX hX' hB hB' hK
    hflip hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr
    (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety Q')
  have hv : D.valuation = (DivisorOver.ofPrimeDivisor k hS.some.isNormalVariety Q).valuation :=
    valuation_eq_of_comap_eq (surjective_stalkMap_left hB hflip hstrata hS) (hDv.trans h.symm)
  have hη := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq
    hS.some.isNormalVariety hv
  exact (congrArg (ι ≫ f).base hη.symm).trans hDc

/-- **Points of the floor correspond to points of the floor.** If `c ∈ ⌊B_S⌋` and `c' ∈ S'` lie
over the same point of `Z`, and every component of `⌊B_S⌋` is the same divisor as a component
of `⌊B_{S'}⌋`, then `c'` lies on a component of `⌊B_{S'}⌋`: the components of `⌊B_{S'}⌋` lie in
the isomorphism locus of `f⁺`. -/
private theorem exists_mem_support_of_mem_supp_roundDown
    (hfloor : ∀ Q : Mori.PrimeDivisor S, BS.coeff Q = 1 →
      ∃ Q' : Mori.PrimeDivisor S', BS'.coeff Q' = 1 ∧ IsSameDivisor hS hS' hcorr Q Q')
    {c : S} {c' : S'} (hc : (ι ≫ f) c = (ι' ≫ fp) c')
    (hx : c ∈ (DivisorWithCoeffs.roundDown BS).supp) :
    ∃ Q' : Mori.PrimeDivisor S', BS'.coeff Q' = 1 ∧ c' ∈ (Q'.support : Set S') := by
  have hd := isDltPair_of_stratumAdjunctionData hB hS.some
  obtain ⟨Q, hQ1, hcQ⟩ :=
    exists_coeff_eq_one_of_mem_supp_roundDown hd.1.2.1 hd.2.1 hx
  obtain ⟨Q', hQ'1, hQQ'⟩ := hfloor Q hQ1
  refine ⟨Q', hQ'1, ?_⟩
  have hη := map_genericPoint_eq_of_isSameDivisor hX hX' hB hB' hK hflip hBflip hstrata hstrata'
    hlow hlow' hS hS' hdim hdim' hcorr hQQ'
  haveI := hS'.some.isClosedImmersion
  haveI : IsProper fp := hflip.isSmallMorphism_flip.isProper
  have hcl : IsClosed (Q'.support : Set S') := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hz : (ι ≫ f) c ∈ (ι' ≫ fp).base '' (Q'.support : Set S') := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hcQ
    have h1 : (ι ≫ f) c ∈ closure {(ι ≫ f) Q.genericPoint} :=
      specializes_iff_mem_closure.mp (hcQ.map (ι ≫ f).base.hom.continuous)
    rw [hη] at h1
    refine closure_minimal ?_ ((ι' ≫ fp).isClosedMap _ hcl) h1
    rw [Set.singleton_subset_iff]
    exact ⟨Q'.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, rfl⟩
  obtain ⟨r', hr', hr'z⟩ := hz
  have hex := map_notMem_exceptionalSet_of_coeff_eq_one hX hX' hB hB' hK hflip hBflip hstrata
    hstrata' hlow hlow' hS hS' hdim hdim' hcorr hQ'1 hr'
  rw [SetLike.mem_coe, mem_exceptionalSet, not_not] at hex
  have h2 : ι' r' = ι' c' := eq_of_apply_eq_of_mem_biregularLocus fp hex (hr'z.trans hc)
  rw [← ι'.isClosedEmbedding.injective h2]
  exact hr'

/-- A prime divisor of `S'` whose generic point lies over the isomorphism locus of `f⁺` is not
contracted. -/
private theorem not_isContractedDivisor_of_notMem_exceptionalSet {P' : Mori.PrimeDivisor S'}
    (hP' : ι' P'.genericPoint ∉ (exceptionalSet fp : Set X')) :
    ¬ IsContractedDivisor (fp := fp) (ι' := ι') P' := by
  intro hc
  haveI := hS'.some.isClosedImmersion
  rw [SetLike.mem_coe, mem_exceptionalSet, not_not] at hP'
  exact map_notMem_biregularLocus_of_topologicalKrullDim_lt
    hflip.isSmallMorphism_flip.isNormalVariety_source.1
    hflip.isSmallMorphism.isNormalVariety_target.1 hflip.isSmallMorphism_flip.isBirationalMorphism
    ι' P'.genericPoint hc hP'

open scoped WithZero in
/-- **Counted valuations of `S'` are counted on `S`.** A divisorial valuation of `k(S')` counted at
the threshold `α` by the difficulty of `(S', B_{S'})` is, on `𝒪_{Z, y}`, a divisorial valuation of
`k(S)` counted at `α` by the difficulty of `(S, B_S)`. -/
private theorem exists_mem_difficultValuations
    (hfloor : ∀ Q : Mori.PrimeDivisor S, BS.coeff Q = 1 →
      ∃ Q' : Mori.PrimeDivisor S', BS'.coeff Q' = 1 ∧ IsSameDivisor hS hS' hcorr Q Q')
    (α : ℝ) {v' : Valuation S'.functionField ℤᵐ⁰}
    (hv' : v' ∈ difficultValuations (ι' ≫ sX') BS' α) :
    ∃ w ∈ difficultValuations (ι ≫ sX) BS α,
      w.comap ((ι ≫ f).stalkMap (genericPoint S)).hom =
        v'.comap ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
          (ι' ≫ fp).stalkMap (genericPoint S')).hom := by
  obtain ⟨E', rfl, ⟨n, K', a, ha, hlt⟩, hcen⟩ := hv'
  obtain ⟨D, hDv, hDc⟩ := exists_divisorOver_valuation_comap_eq_of_divisorOver hX hX' hB hB' hK
    hflip hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr E'
  refine ⟨D.valuation, ⟨D, rfl, ?_, ?_⟩, hDv⟩
  · have hd := isDltPair_of_stratumAdjunctionData hB hS.some
    obtain ⟨-, n₀, K₀, hK₀, -⟩ := hd.1.1
    obtain ⟨aD, haD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hd.1.1 hK₀ D
    have hle : aD ≤ a := by
      subst hBflip
      exact MMP.Mori.IsFlip.isDiscrepancy_le_of_isStratumAdjunctionPair hX hX' hB hB'
        (isFlip_of_isFlipOf hK hflip) hstrata hstrata' hS hS' hcorr D E' hDv haD ha
    exact ⟨n₀, K₀, aD, haD, lt_of_le_of_lt (by exact_mod_cast hle) hlt⟩
  · intro hsub
    apply hcen
    have hx : D.f D.E.genericPoint ∈ (DivisorWithCoeffs.roundDown BS).supp := by
      apply hsub
      rw [D.center_eq_closure_genericPoint]
      exact subset_closure rfl
    obtain ⟨Q', hQ'1, hQ'⟩ := exists_mem_support_of_mem_supp_roundDown hX hX' hB hB' hK hflip
      hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr hfloor hDc hx
    rw [E'.center_eq_closure_genericPoint]
    refine (closure_minimal (Set.singleton_subset_iff.mpr hQ') ?_).trans
      (support_subset_supp_roundDown hQ'1)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure

open scoped WithZero in
/-- **The difficulty does not increase, and drops along a contracted divisor.** The flip is an
isomorphism near the fixed lower strata, hence near `⌊B_S⌋` and `⌊B_{S'}⌋`
(`MMP.Fourfold.IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair`), so a divisorial
valuation has its centre in the reduced boundary on one side exactly when it does on the other;
off the reduced boundary each summand of the difficulty does not increase by the discrepancy
comparison, and a prime divisor of `S'` contracted to `Z`, of coefficient `α ∈ D(I)`, is counted at
`α` on `S` (`MMP.Mori.IsFlip.isDiscrepancy_lt_of_isStratumAdjunctionPair`) but not on `S'`. -/
private theorem difficulty_le_and_lt
    (hfloor : ∀ Q : Mori.PrimeDivisor S, BS.coeff Q = 1 →
      ∃ Q' : Mori.PrimeDivisor S', BS'.coeff Q' = 1 ∧ IsSameDivisor hS hS' hcorr Q Q')
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1)
    (hI1 : (1 : ℚ) ∈ I) (hBI : ∀ P, B.coeff P ≠ 0 → B.coeff P ∈ I)
    (hBI' : ∀ P, B'.coeff P ≠ 0 → B'.coeff P ∈ I) :
    hS'.some.difficulty I ≤ hS.some.difficulty I ∧
      ((∃ P' : Mori.PrimeDivisor S', IsContractedDivisor (fp := fp) (ι' := ι') P') →
        hS'.some.difficulty I < hS.some.difficulty I) := by
  -- the correspondence of valuations through `𝒪_{Z, y}`
  let R : Valuation S.functionField ℤᵐ⁰ → Valuation S'.functionField ℤᵐ⁰ → Prop := fun w v' =>
    w.comap ((ι ≫ f).stalkMap (genericPoint S)).hom =
      v'.comap ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
        (ι' ≫ fp).stalkMap (genericPoint S')).hom
  have hinj : ∀ w v₁ v₂, R w v₁ → R w v₂ → v₁ = v₂ := fun w v₁ v₂ h1 h2 =>
    valuation_eq_of_comap_eq (surjective_stalkMap_right hB' hflip hstrata' hS' hcorr)
      (h1.symm.trans h2)
  have hpt : ∀ α : hyperstandardSet I,
      (difficultValuations (ι' ≫ sX') BS' α).encard ≤
        (difficultValuations (ι ≫ sX) BS α).encard := fun α =>
    encard_le_of_forall_exists R (fun v' hv' => exists_mem_difficultValuations hX hX' hB hB' hK
      hflip hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr hfloor α hv') hinj
  change adjunctionPairDifficulty (ι' ≫ sX') I BS' ≤ adjunctionPairDifficulty (ι ≫ sX) I BS ∧
    ((∃ P' : Mori.PrimeDivisor S', IsContractedDivisor (fp := fp) (ι' := ι') P') →
      adjunctionPairDifficulty (ι' ≫ sX') I BS' < adjunctionPairDifficulty (ι ≫ sX) I BS)
  refine ⟨Summable.tsum_le_tsum hpt (summable_enat _) (summable_enat _), ?_⟩
  rintro ⟨P', hP'⟩
  -- the threshold `α`, the coefficient of `P'`
  have hα := IsStratumAdjunctionPair.coeff_mem_hyperstandardSet hB' hX' hI hI1 hBI' hS' P'
  let α : hyperstandardSet I := ⟨_, hα⟩
  obtain ⟨D, hDv, hDc⟩ := exists_divisorOver_valuation_comap_eq_of_divisorOver hX hX' hB hB' hK
    hflip hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr
    (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P')
  have hd := isDltPair_of_stratumAdjunctionData hB hS.some
  have hd' := isDltPair_of_stratumAdjunctionData hB' hS'.some
  -- `v(D)` is counted on `S` at `α`
  have hmem : D.valuation ∈ difficultValuations (ι ≫ sX) BS α := by
    refine ⟨D, rfl, ?_, ?_⟩
    · obtain ⟨-, n₀, K₀, hK₀, -⟩ := hd.1.1
      obtain ⟨aD, haD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hd.1.1 hK₀ D
      obtain ⟨-, n₁, K₁, hK₁, -⟩ := hd'.1.1
      obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hd'.1.1 hK₁
        (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P')
      have hlt : aD < a' := by
        subst hBflip
        exact IsFlip.isDiscrepancy_lt_of_isStratumAdjunctionPair hX hX' hB hB'
          (isFlip_of_isFlipOf hK hflip) hstrata hstrata' hS hS' hcorr P' hP' D hDv haD ha'
      rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor _ ha'] at hlt
      exact ⟨n₀, K₀, aD, haD, by change (aD : ℝ) < -((BS'.coeff P' : ℚ) : ℝ); exact_mod_cast hlt⟩
    · intro hsub
      have hx : D.f D.E.genericPoint ∈ (DivisorWithCoeffs.roundDown BS).supp := by
        apply hsub
        rw [D.center_eq_closure_genericPoint]
        exact subset_closure rfl
      obtain ⟨Q', hQ'1, hQ'⟩ := exists_mem_support_of_mem_supp_roundDown hX hX' hB hB' hK hflip
        hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr hfloor hDc hx
      exact not_isContractedDivisor_of_notMem_exceptionalSet hX hX' hB hB' hK hflip hBflip
        hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr
        (map_notMem_exceptionalSet_of_coeff_eq_one hX hX' hB hB' hK hflip hBflip hstrata
          hstrata' hlow hlow' hS hS' hdim hdim' hcorr hQ'1 hQ') hP'
  -- and it corresponds to no valuation counted on `S'` at `α`
  have hnot : ∀ v' ∈ difficultValuations (ι' ≫ sX') BS' α, ¬ R D.valuation v' := by
    rintro v' ⟨E', rfl, ⟨n, K', a, ha, hlt⟩, -⟩ hR
    have hE' : E'.valuation = (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P').valuation :=
      hinj _ _ _ hR hDv
    obtain ⟨hNV, hK', m, hm, hC, -⟩ := id ha
    have hpair : IsPairWith (ι' ≫ sX') n K' BS' :=
      ⟨hNV, hK', m, by exact_mod_cast hm.ne', hC⟩
    obtain ⟨a₁, ha₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hK'
      (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P')
    have h1 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hpair hE' ha ha₁
    rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor _ ha₁] at h1
    change (a : ℝ) < -((BS'.coeff P' : ℚ) : ℝ) at hlt
    rw [h1] at hlt
    push_cast at hlt
    exact lt_irrefl _ hlt
  -- the difficulty of `S` is finite
  have hfin := StratumAdjunctionData.difficulty_ne_top hB hI hI1 hBI hS.some
  change adjunctionPairDifficulty (ι ≫ sX) I BS ≠ ⊤ at hfin
  have hfinα : (difficultValuations (ι ≫ sX) BS α).encard ≠ ⊤ := fun h => hfin
    (top_le_iff.mp (h ▸ (show (difficultValuations (ι ≫ sX) BS α).encard ≤
      adjunctionPairDifficulty (ι ≫ sX) I BS from (summable_enat fun β : hyperstandardSet I =>
        (difficultValuations (ι ≫ sX) BS β).encard).le_tsum α (fun _ _ => zero_le))))
  exact tsum_lt_tsum_of_lt hpt (i := α)
    (encard_lt_of_forall_exists R (fun v' hv' => exists_mem_difficultValuations hX hX' hB hB' hK
      hflip hBflip hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr hfloor α hv') hinj hmem
      hnot hfinα) hfin

/-- A prime divisor of `S'` is the same divisor as at most one prime divisor of `S`: the stalk
map `𝒪_{Z, y} → k(S)` is surjective, since `f` is an isomorphism at the generic point of `S`. -/
private theorem isSameDivisor_left_unique {P Q : Mori.PrimeDivisor S}
    {P' : Mori.PrimeDivisor S'} (hP : IsSameDivisor hS hS' hcorr P P')
    (hQ : IsSameDivisor hS hS' hcorr Q P') : P = Q :=
  eq_of_valuation_ofPrimeDivisor_eq hS.some.isNormalVariety (valuation_eq_of_comap_eq
    (surjective_stalkMap_left hB hflip hstrata hS) (hP.trans hQ.symm))

/-- A prime divisor of `S` is the same divisor as at most one prime divisor of `S'`. -/
private theorem isSameDivisor_right_unique {P : Mori.PrimeDivisor S}
    {P' Q' : Mori.PrimeDivisor S'} (hP : IsSameDivisor hS hS' hcorr P P')
    (hQ : IsSameDivisor hS hS' hcorr P Q') : P' = Q' :=
  eq_of_valuation_ofPrimeDivisor_eq hS'.some.isNormalVariety (valuation_eq_of_comap_eq
    (surjective_stalkMap_right hB' hflip hstrata' hS' hcorr) (hP.symm.trans hQ))

/-- **Coefficients do not increase.** For the same divisor `P ⊂ S`, `P' ⊂ S'`, the discrepancy
comparison `a(P, S, B_S) ≤ a(P', S', B_{S'})` reads `coeff_{P'} B_{S'} ≤ coeff_P B_S`. -/
private theorem coeff_le_of_isSameDivisor {P : Mori.PrimeDivisor S}
    {P' : Mori.PrimeDivisor S'} (h : IsSameDivisor hS hS' hcorr P P') :
    BS'.coeff P' ≤ BS.coeff P := by
  subst hBflip
  have hd := isDltPair_of_stratumAdjunctionData hB hS.some
  have hd' := isDltPair_of_stratumAdjunctionData hB' hS'.some
  obtain ⟨-, n₀, K₀, hK₀, -⟩ := hd.1.1
  obtain ⟨-, n₁, K₁, hK₁, -⟩ := hd'.1.1
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hd.1.1 hK₀
    (DivisorOver.ofPrimeDivisor k hS.some.isNormalVariety P)
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hd'.1.1 hK₁
    (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P')
  have hle := MMP.Mori.IsFlip.isDiscrepancy_le_of_isStratumAdjunctionPair hX hX' hB hB'
    (isFlip_of_isFlipOf hK hflip)
    hstrata hstrata' hS hS' hcorr _ _ h ha ha'
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor _ ha,
    IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor _ ha'] at hle
  linarith

/-- **A prime divisor of `S'` that `S' ⟶ Z` does not contract is a prime divisor of `S`.** -/
private theorem exists_isSameDivisor_of_not_isContractedDivisor {P' : Mori.PrimeDivisor S'}
    (hP' : ¬ IsContractedDivisor (fp := fp) (ι' := ι') P') :
    ∃ P : Mori.PrimeDivisor S, IsSameDivisor hS hS' hcorr P P' := by
  have hc := hflip.isContraction
  have hZ := hc.isNormalVariety_target
  haveI := hZ.1.toIsSeparated
  haveI := hZ.1.toLocallyOfFiniteType
  haveI := hZ.1.toQuasiCompact
  haveI := hS.some.isClosedImmersion
  haveI := hS'.some.isClosedImmersion
  haveI : IsProper f := hflip.isSmallMorphism.isProper
  haveI : IsProper fp := hflip.isSmallMorphism_flip.isProper
  exact exists_valuation_comap_eq_of_not_lt hS.some.isNormalVariety hS'.some.isNormalVariety
    (ι ≫ f) (ι' ≫ fp) (by rw [Category.assoc, hc.comp_eq])
    (by rw [Category.assoc, hflip.isSmallMorphism_flip.comp_eq]) hcorr
    (surjective_stalkMap_left hB hflip hstrata hS)
    (surjective_stalkMap_genericPoint hflip.isSmallMorphism_flip.two_le_codimension hB'
      hstrata' hS'.some) P' hP'

/-- **Components of `⌊B_{S'}⌋` are components of `⌊B_S⌋`.** A prime divisor of coefficient one in
`B_{S'}` lies in the isomorphism locus of `f⁺`, so it is not contracted; it is the same divisor
as a prime divisor of `S`, whose coefficient is at least, hence equal to, one. -/
private theorem exists_isSameDivisor_coeff_eq_one {R' : Mori.PrimeDivisor S'}
    (hR' : BS'.coeff R' = 1) :
    ∃ R : Mori.PrimeDivisor S, BS.coeff R = 1 ∧ IsSameDivisor hS hS' hcorr R R' := by
  have hnot := not_isContractedDivisor_of_notMem_exceptionalSet hX hX' hB hB' hK hflip hBflip
    hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr
    (map_notMem_exceptionalSet_of_coeff_eq_one hX hX' hB hB' hK hflip hBflip hstrata hstrata'
      hlow hlow' hS hS' hdim hdim' hcorr hR' (q := R'.genericPoint)
      (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl))
  obtain ⟨R, hR⟩ := exists_isSameDivisor_of_not_isContractedDivisor hX hX' hB hB' hK hflip hBflip
    hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr hnot
  have hle := coeff_le_of_isSameDivisor hX hX' hB hB' hK hflip hBflip hstrata hstrata' hlow hlow'
    hS hS' hdim hdim' hcorr hR
  have hd := isDltPair_of_stratumAdjunctionData hB hS.some
  exact ⟨R, le_antisymm (hd.2.1 R) (hR' ▸ hle), hR⟩

/-- **One flip of a corresponding pair of strata.** The correspondence `IsSameDivisor` is
injective both ways and coefficients do not increase along it. A prime divisor of `S'` that
`S' ⟶ Z` does not contract, and a component of `⌊B_{S'}⌋`, have partners on `S`. Once every
component of `⌊B_S⌋` has a partner in `⌊B_{S'}⌋`, the difficulty does not increase, and it drops
when `S' ⟶ Z` contracts a prime divisor. -/
private theorem flip_step {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) (hI1 : (1 : ℚ) ∈ I)
    (hBI : ∀ P, B.coeff P ≠ 0 → B.coeff P ∈ I) (hBI' : ∀ P, B'.coeff P ≠ 0 → B'.coeff P ∈ I) :
    (∀ P Q P', IsSameDivisor hS hS' hcorr P P' → IsSameDivisor hS hS' hcorr Q P' → P = Q) ∧
    (∀ P P' Q', IsSameDivisor hS hS' hcorr P P' → IsSameDivisor hS hS' hcorr P Q' → P' = Q') ∧
    (∀ P P', IsSameDivisor hS hS' hcorr P P' → BS'.coeff P' ≤ BS.coeff P) ∧
    (∀ P', ¬ IsContractedDivisor (fp := fp) (ι' := ι') P' →
      ∃ P, IsSameDivisor hS hS' hcorr P P') ∧
    (∀ P', BS'.coeff P' = 1 → ∃ P, BS.coeff P = 1 ∧ IsSameDivisor hS hS' hcorr P P') ∧
    ((∀ P, BS.coeff P = 1 → ∃ P', BS'.coeff P' = 1 ∧ IsSameDivisor hS hS' hcorr P P') →
      hS'.some.difficulty I ≤ hS.some.difficulty I ∧
        ((∃ P', IsContractedDivisor (fp := fp) (ι' := ι') P') →
          hS'.some.difficulty I < hS.some.difficulty I)) :=
  ⟨fun _ _ _ => isSameDivisor_left_unique hX hX' hB hB' hK hflip hBflip hstrata hstrata' hlow
      hlow' hS hS' hdim hdim' hcorr,
    fun _ _ _ => isSameDivisor_right_unique hX hX' hB hB' hK hflip hBflip hstrata hstrata' hlow
      hlow' hS hS' hdim hdim' hcorr,
    fun _ _ => coeff_le_of_isSameDivisor hX hX' hB hB' hK hflip hBflip hstrata hstrata' hlow
      hlow' hS hS' hdim hdim' hcorr,
    fun _ => exists_isSameDivisor_of_not_isContractedDivisor hX hX' hB hB' hK hflip hBflip
      hstrata hstrata' hlow hlow' hS hS' hdim hdim' hcorr,
    fun _ => exists_isSameDivisor_coeff_eq_one hX hX' hB hB' hK hflip hBflip hstrata hstrata'
      hlow hlow' hS hS' hdim hdim' hcorr,
    fun hfloor => difficulty_le_and_lt hX hX' hB hB' hK hflip hBflip hstrata hstrata' hlow hlow'
      hS hS' hdim hdim' hcorr hfloor hI hI1 hBI hBI'⟩

end Step

/-- **Stabilization of the divisorial part on strata.** Let `fp i : X (i + 1) ⟶ Z i` be a
`(K_i + B_i)`-flip (`MMP.Fourfold.IsFlipOf`) of `f i : X i ⟶ Z i` for every `i`, between
projective dlt pairs (`MMP.Intersection.IsDltPair`) with `K i` canonical and
`B (i + 1) = (fp i)⁻¹_* (f i)_* (B i)`. Suppose every adjunction pair on a boundary stratum of
dimension `< d` of `(X i, B i)` (`MMP.Fourfold.IsDltStratum`) is disjoint from the exceptional
set of `f i`, and every boundary stratum of dimension `< d` of `(X (i + 1), B (i + 1))` is
disjoint from that of `fp i`. Let
`(S i, BS i)`, `ι i : S i ⟶ X i`, be adjunction pairs (`MMP.Fourfold.IsStratumAdjunctionPair`)
of dimension at most `d` whose generic points have the same image in `Z i` as that of
`S (i + 1)`. Then there is `N` such that for every `i ≥ N`: no prime divisor `P` of `S (i + 1)` is
contracted by `ι (i + 1) ≫ fp i`, and prime divisors `P` of `S i` and `P'` of `S (i + 1)` with the
same valuation on `𝒪_{Z i, y}` have the same coefficient in `BS i` and in `BS (i + 1)`. -/
@[mmp "lem_mmp_stratum_divisors_stabilize"]
public theorem _root_.MMP.Fourfold.exists_forall_ge_isStratumAdjunctionPair_coeff_eq {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : ℕ → Scheme.{0}}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    [∀ i, CompactSpace (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of k)} {sZ : ∀ i, Z i ⟶ Spec (.of k)}
    {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i}
    {n : ℕ} {K : ∀ i, Divisor (X i)} {B : ∀ i, QDivisor (X i)}
    (hX : ∀ i, Mori.IsProjectiveVariety k (sX i))
    (hB : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i))
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) n)
    (hflip : ∀ i,
      IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hBflip : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i))
    {d : ℕ}
    (hlow : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T → topologicalKrullDim T < d →
      Disjoint T (exceptionalSet (f i) : Set (X i)))
    (hlow' : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      topologicalKrullDim T' < d → Disjoint T' (exceptionalSet (fp i) : Set (X (i + 1))))
    {S : ℕ → Scheme.{0}} [∀ i, IsIntegral (S i)] [∀ i, IsLocallyNoetherian (S i)]
    [∀ i, IsNormal (S i)]
    {ι : ∀ i, S i ⟶ X i} {BS : ∀ i, QDivisor (S i)}
    (hS : ∀ i, IsStratumAdjunctionPair (sX i) (B i) (ι i) (BS i))
    (hdim : ∀ i, topologicalKrullDim (S i) ≤ d)
    (hcorr : ∀ i,
      (ι i ≫ f i).base (genericPoint (S i)) = (ι (i + 1) ≫ fp i).base (genericPoint (S (i + 1)))) :
    ∃ N : ℕ, ∀ i ≥ N,
      (∀ P : Mori.PrimeDivisor (S (i + 1)),
        ¬ topologicalKrullDim (closure {(ι (i + 1) ≫ fp i).base P.genericPoint} : Set (Z i)) <
          topologicalKrullDim (closure {P.genericPoint} : Set (S (i + 1)))) ∧
      (∀ (P : Mori.PrimeDivisor (S i)) (P' : Mori.PrimeDivisor (S (i + 1))),
        (DivisorOver.ofPrimeDivisor k (hS i).some.isNormalVariety P).valuation.comap
            ((ι i ≫ f i).stalkMap (genericPoint (S i))).hom =
          (DivisorOver.ofPrimeDivisor k (hS (i + 1)).some.isNormalVariety P').valuation.comap
            (((Z i).presheaf.stalkCongr (.of_eq (hcorr i))).hom ≫
              (ι (i + 1) ≫ fp i).stalkMap (genericPoint (S (i + 1)))).hom →
        (BS i).coeff P = (BS (i + 1)).coeff P') := by
  classical
  obtain ⟨I, hI, hI1, hBI⟩ := exists_finset_coeff_mem (f := f) (fp := fp)
    (fun i P => ⟨(hB i).1.2.1 P, (hB i).2.1 P⟩) hBflip
  obtain ⟨N₀, hN₀⟩ := exists_forall_ge_not_subset_exceptionalSet_of_isDltStratum (L := ⊤)
    (hX 0) (hB 0) (fun i _ => hK i) (fun i _ => hflip i) (fun i _ => hBflip i)
  have step := fun i (hi : i ≥ N₀) => flip_step (hX i) (hX (i + 1)) (hB i) (hB (i + 1)) (hK i)
    (hflip i) (hBflip i) (hN₀ i hi (WithTop.coe_lt_top _)).1
    (hN₀ i hi (WithTop.coe_lt_top _)).2.1 (hlow i) (hlow' i) (hS i) (hS (i + 1)) (hdim i)
    (hdim (i + 1)) (hcorr i) hI hI1 (hBI i) (hBI (i + 1))
  have hfl := fun i (hi : i ≥ N₀) => card_filter_eq_one_le_and (BS i) (BS (i + 1))
    (fun P P' => IsSameDivisor (hS i) (hS (i + 1)) (hcorr i) P P') (step i hi).2.1
    (step i hi).2.2.2.2.1
  obtain ⟨N₀', hN₀'⟩ := exists_forall_ge_not_of_lt
    (fun i => ((BS i).support.filter (fun P => BS i P = 1)).card)
    (fun i => ((BS (i + 1)).support.filter (fun P => BS (i + 1) P = 1)).card <
      ((BS i).support.filter (fun P => BS i P = 1)).card) (N := N₀)
    (fun i hi => (hfl i hi).1) (fun i _ h => h)
  have hfin : ∀ i, (hS i).some.difficulty I ≠ ⊤ := fun i =>
    StratumAdjunctionData.difficulty_ne_top (hB i) hI hI1 (hBI i) (hS i).some
  have hstep := fun i (hi : i ≥ max N₀ N₀') => (step i (le_of_max_le_left hi)).2.2.2.2.2
    ((hfl i (le_of_max_le_left hi)).2 (le_antisymm (hfl i (le_of_max_le_left hi)).1
      (not_lt.mp (hN₀' i (le_of_max_le_right hi)))))
  obtain ⟨N₁, hN₁⟩ := exists_forall_ge_not_of_lt (fun i => ((hS i).some.difficulty I).toNat)
    (fun i => ∃ P : Mori.PrimeDivisor (S (i + 1)),
      topologicalKrullDim (closure {(ι (i + 1) ≫ fp i).base P.genericPoint} : Set (Z i)) <
        topologicalKrullDim (closure {P.genericPoint} : Set (S (i + 1)))) (N := max N₀ N₀')
    (fun i hi => ENat.toNat_le_toNat (hstep i hi).1 (hfin i))
    (fun i hi hP => by
      have hlt := (hstep i hi).2 hP
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (hfin i)
      obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (hfin (i + 1))
      simp only [← ha, ← hb, ENat.toNat_coe] at hlt ⊢
      exact_mod_cast hlt)
  have hmem : ∀ i P, (BS i) P ∈ {y : ℚ | ((y : ℚ) : ℝ) ∈ hyperstandardSet I} := fun i P =>
    IsStratumAdjunctionPair.coeff_mem_hyperstandardSet (hB i) (hX i) hI hI1 (hBI i) (hS i) P
  obtain ⟨N₂, hN₂⟩ := exists_forall_ge_coeff_eq BS
    (fun i P P' => IsSameDivisor (hS i) (hS (i + 1)) (hcorr i) P P')
    (D := {y : ℚ | ((y : ℚ) : ℝ) ∈ hyperstandardSet I})
    (fun x hx => by exact_mod_cast hx.1.2)
    (fun x hx => finite_setOf_mem_hyperstandardSet_le (fun b hb => (hI b hb).1) hx)
    hmem (fun i P => by exact_mod_cast (hmem i P).1.1) (N := max N₀ N₁)
    (fun i hi => (step i (le_of_max_le_left hi)).1)
    (fun i hi => (step i (le_of_max_le_left hi)).2.1)
    (fun i hi => (step i (le_of_max_le_left hi)).2.2.1)
    (fun i hi P' _ => (step i (le_of_max_le_left hi)).2.2.2.1 P' fun hc =>
      hN₁ i (le_of_max_le_right hi) ⟨P', hc⟩)
  exact ⟨max N₁ N₂, fun i hi => ⟨fun P hP => hN₁ i (le_of_max_le_left hi) ⟨P, hP⟩,
    fun P P' h => (hN₂ i (le_of_max_le_right hi) P P' h).symm⟩⟩

end MMP.Fourfold.StratumDivisorsStabilize
