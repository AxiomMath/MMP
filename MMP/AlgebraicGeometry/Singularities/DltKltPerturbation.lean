module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Singularities.DltLogResolutionCriterion
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison

/-!
# Klt and dlt pairs under perturbation of the boundary

Three results on klt and dlt pairs over an algebraically closed field of characteristic zero
(Kollár–Mori 2.35, 2.41, 2.43).

If `(X, Δ)` is klt and `Δ'` is an effective `ℚ`-Cartier `ℚ`-divisor, then `(X, Δ + εΔ')` is klt
for every small rational `ε ≥ 0`: near `ε = 0` the discrepancy is a minimum of finitely many affine
functions of `ε` (`MMP.Mori.exists_discrep_add_smul_eq_inf'`).

A dlt pair `(X, Δ)` is klt exactly when `⌊Δ⌋ = 0`. Over the closed set `Z` of the dlt criterion
(`MMP.Mori.isDltPair_iff_exists_isLogResolution`) the discrepancies are `≥ -1 + δ`; over the
smooth snc locus `X \ Z` they are bounded below by the coefficients of `Δ` and by the discrepancy
of the restricted snc pair.

If `(X, Δ)` is dlt on a quasi-projective variety, `H` is ample Cartier and `0 ≤ Δ₁ ≤ Δ`, a general
member `D` of `|mΔ₁ + m'H|` (Bertini on the smooth snc locus), divided by `m`, gives a pair
`(X, Δ - εΔ₁ + εD)` that is dlt for small rational `ε > 0`.

## Main results

* `MMP.Mori.IsKltPair.exists_forall_isKltPair_add_smul`: klt is preserved under adding a small
  multiple of an effective `ℚ`-Cartier `ℚ`-divisor.
* `MMP.Mori.IsDltPair.isKltPair_iff_roundDown_eq_zero`: a dlt pair is klt iff `⌊Δ⌋ = 0`.
* `MMP.Mori.IsDltPair.exists_forall_isDltPair_sub_smul_add_smul`: perturbing a dlt pair by an
  ample divisor.

## Implementation notes

Thresholds `ε₀` are rational. In the perturbation result the linear equivalence `mD ∼ mΔ₁ + m'H`
is between integral divisors `E = mD` and `E₁ = mΔ₁`, and "no component of `D` is a component of
`⌊Δ⌋`" is the disjointness of the supports of `D` and `⌊Δ⌋`. Bertini's theorem enters through
`MMP.Mori.exists_polynomial_zeroDivisor_eq_sum_isSNC`, on the smooth snc locus. Each result's
auxiliary lemmas live in a namespace `Proof_<tag>` named after its label, opened only for
that result.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  Corollary 2.35(2), Propositions 2.41 and 2.43
-/

@[expose] public section

universe u

namespace Proof_lem_km2b_klt_add_small_multiple

open CategoryTheory AlgebraicGeometry MMP.Mori Filter Topology

/-- On a scheme of dimension `≤ 1` no divisor over `X` is exceptional. -/
private theorem not_isExceptional_of_topologicalKrullDim_le_one {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : n ≤ 1)
    (D : DivisorOver k sX) : ¬ D.IsExceptional := by
  intro h
  have hdef : RationalMap.DefinedAt (X := D.Y) D.f.toRationalMap D.E.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp h) hdef
  have hmem : D.f D.E.genericPoint ∈
      (RationalMap.transform (X := D.Y) D.f.toRationalMap D.E.idealSheaf.support : Set X) := by
    refine RationalMap.image_subset_transform D.f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨_, ?_, rfl⟩
    change D.E.genericPoint ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hc := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) _ hmem
  have hle : (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) ≤ n := by
    rw [← hdim, ← MMP.Flips.codimension_closureSingleton]
    exact Order.coheight_le_krullDim _
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (1 : ℕ) := (WithBot.coe_le_coe.mpr hc).trans
    (hle.trans (by exact_mod_cast hn))
  exact absurd this (by decide)

/-- `-1 < q` in `EReal` exactly when `-1 < q` in `ℚ`. -/
private theorem neg_one_lt_coe_iff (q : ℚ) : (-1 : EReal) < ((q : ℝ) : EReal) ↔ -1 < q := by
  rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp, EReal.coe_lt_coe_iff]
  norm_cast

/-- A minimum of finitely many affine maps `ℚ → ℚ` that is `> -1` at `0` stays `> -1` near `0`. -/
private theorem eventually_neg_one_lt_inf' {L : Finset (ℚ →ᵃ[ℚ] ℚ)} (hL : L.Nonempty)
    (h0 : -1 < L.inf' hL fun ℓ => ℓ 0) : ∀ᶠ ε in 𝓝 (0 : ℚ), -1 < L.inf' hL fun ℓ => ℓ ε :=
  continuousAt_const.eventually_lt
    (Continuous.finset_inf'_apply (f := fun ℓ : ℚ →ᵃ[ℚ] ℚ => ⇑ℓ) hL
      fun ℓ _ => by rw [ℓ.decomp]; fun_prop).continuousAt h0

/-- If every coefficient of `Δ` is `< 1`, so is every coefficient of `Δ + εΔ'` for `ε` near `0`. -/
private theorem eventually_coeff_add_smul_lt_one {X : Scheme.{u}} {Δ Δ' : QDivisor X}
    (hr : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P < 1) :
    ∀ᶠ ε in 𝓝 (0 : ℚ), ∀ P : MMP.Mori.PrimeDivisor X, (Δ + ε • Δ').coeff P < 1 := by
  have := (Filter.eventually_all_finset Δ'.support).2 fun P _ =>
    (show ContinuousAt (fun ε : ℚ => Δ P + ε * Δ' P) 0 by fun_prop).eventually_lt
      continuousAt_const (by simpa [DivisorWithCoeffs.coeff_apply] using hr P)
  filter_upwards [this] with ε hε P
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hP' : P ∈ Δ'.support
  · exact hε P hP'
  · rw [Finsupp.notMem_support_iff.mp hP', mul_zero, add_zero]
    simpa [DivisorWithCoeffs.coeff_apply] using hr P

/-- **The discrepancy stays `> -1`.** If `(X, Δ)` is a pair with `discrep(X, Δ) > -1` and every
coefficient of `Δ` is `< 1`, and `Δ'` is `ℚ`-Cartier, then `discrep(X, Δ + εΔ') > -1` for all
`ε ≥ 0` near `0`. -/
private theorem eventually_neg_one_lt_discrep_add_smul {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ Δ' : QDivisor X}
    (hP : IsPairWith sX n K Δ) (hd : -1 < discrep sX n K Δ)
    (hr : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P < 1) (hΔ'q : Δ'.IsQCartier) :
    ∀ᶠ ε in 𝓝 (0 : ℚ), 0 ≤ ε → -1 < discrep sX n K (Δ + ε • Δ') := by
  rcases le_or_gt 2 n with hn | hn
  · obtain ⟨ε₁, hε₁, L, hL, h0, hεL⟩ := exists_discrep_add_smul_eq_inf' hP hn hd
      (fun P => (hr P).le) hΔ'q (fun P hP1 => absurd hP1 (hr P).ne)
    rw [h0, neg_one_lt_coe_iff] at hd
    filter_upwards [eventually_neg_one_lt_inf' hL hd, eventually_lt_nhds hε₁] with ε hε hεε₁ hε0
    rwa [hεL ε hε0 hεε₁, neg_one_lt_coe_iff]
  · refine Filter.Eventually.of_forall fun ε _ => ?_
    rw [discrep_eq_top fun D a hD _ =>
      not_isExceptional_of_topologicalKrullDim_le_one hP.2.1.topologicalKrullDim_eq (by omega) D hD]
    exact EReal.coe_lt_top (-1)

end Proof_lem_km2b_klt_add_small_multiple

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry Filter Topology Proof_lem_km2b_klt_add_small_multiple

/-- **Klt is open under adding a small multiple** (Kollár–Mori 2.35(2)). Let `(X, Δ)` be a klt
pair, with canonical divisor `K` of dimension `n`, over an algebraically closed field of
characteristic zero, and let `Δ'` be an effective `ℚ`-Cartier `ℚ`-divisor. Then there is a
rational `ε₀ > 0` such that `(X, Δ + εΔ')` is klt for every rational `0 ≤ ε < ε₀`. -/
@[mmp "lem_km2b_klt_add_small_multiple"]
public theorem IsKltPair.exists_forall_isKltPair_add_smul {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : IsKltPair sX n K Δ) {Δ' : QDivisor X} (hΔ' : Δ'.IsEffective) (hΔ'q : Δ'.IsQCartier) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 ≤ ε → ε < ε₀ → IsKltPair sX n K (Δ + ε • Δ') := by
  obtain ⟨hP, hd, hr⟩ := h
  rw [roundDown_nonpos_iff] at hr
  obtain ⟨ε₀, hε₀, hs⟩ := exists_Ico_subset_of_mem_nhds
    ((eventually_coeff_add_smul_lt_one (Δ' := Δ') hr).and
      (eventually_neg_one_lt_discrep_add_smul hP hd hr hΔ'q)) ⟨1, one_pos⟩
  refine ⟨ε₀, hε₀, fun ε h0 hε => ⟨⟨hP.1, hP.2.1, ?_⟩, (hs ⟨h0, hε⟩).2 h0,
    roundDown_nonpos_iff.mpr (hs ⟨h0, hε⟩).1⟩⟩
  rw [← add_assoc]
  exact hP.2.2.add (MMP.Flips.QDivisor.IsQCartier.qsmul hΔ'q ε)

end MMP.Mori

namespace Proof_prop_km2b_dlt_klt_iff_round_down_zero

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

/-- A divisor over `X` that is not exceptional has discrepancy `-coeff_P(Δ)` for some prime
divisor `P` of `X`. -/
private theorem exists_eq_neg_coeff_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX}
    (hD : ¬ D.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) :
    ∃ P : MMP.Mori.PrimeDivisor X, a = -Δ.coeff P := by
  obtain ⟨hX, hK, m, hm, -, V, hV, τ, hτ, hmτ⟩ := ha
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hPV : (P.support ∩ (V : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hx ▸ hV⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 P hPV
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  refine ⟨P, ?_⟩
  apply mul_left_cancel₀ hm0
  linear_combination hmτ + e

/-- A `ℚ`-divisor with every coefficient `< 1` has all its coefficients bounded by one `c < 1`. -/
private theorem exists_lt_one_forall_coeff_le {X : Scheme.{u}} {Δ : QDivisor X}
    (hΔ : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P < 1) :
    ∃ c : ℚ, c < 1 ∧ ∀ P, Δ.coeff P ≤ c := by
  classical
  set T : Finset ℚ := insert 0 (Δ.support.image Δ.coeff)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.max' hT, ?_, fun P => T.le_max' _ ?_⟩
  · obtain h | h := Finset.mem_insert.mp (T.max'_mem hT)
    · rw [h]; norm_num
    · obtain ⟨P, -, hP⟩ := Finset.mem_image.mp h
      exact hP ▸ hΔ P
  · by_cases hP : P ∈ Δ.support
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP)
    · rw [show Δ.coeff P = 0 from Finsupp.notMem_support_iff.mp hP]
      exact Finset.mem_insert_self _ _

/-- **The discrepancy of a divisor meeting the snc locus.** Let `U ⊆ X` be an open subset of the
smooth locus on which `Δ|_U` is snc, and let `c < 1` bound every coefficient of `Δ`. A divisor over
`X` whose center meets `U`, with discrepancy `a`, has `a ≥ -c`, or `a ≥ discrep(U, Δ|_U)` where
the latter is `> -1`. -/
private theorem neg_le_or_discrep_restrictOpen_le {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsPairWith sX n K Δ)
    {U : X.Opens} [Nonempty U] (hsm : U ≤ smoothLocus sX)
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX)) {c : ℚ} (hc1 : c < 1)
    (hc : ∀ P, Δ.coeff P ≤ c) {D : DivisorOver k sX} (hDU : ((D.center : Set X) ∩ U).Nonempty)
    {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) :
    -c ≤ a ∨ (-1 < discrep (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) ∧
      discrep (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) ≤ ((a : ℝ) : EReal)) := by
  obtain ⟨hY, hf, E', -, -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hΔ D U hDU
  have ha' := (hiff a).mp ha
  by_cases hE : (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)).IsExceptional
  · refine Or.inr ⟨(isKltPair_of_isSNC (U.ι ≫ sX) ha'.1 (isSmoothScheme_ι_of_le_smoothLocus hsm)
      ha'.2.1 hsnc fun P => ?_).2.1, discrep_le hE ha'⟩
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact (hc _).trans_lt hc1
  · obtain ⟨P, rfl⟩ := exists_eq_neg_coeff_of_not_isExceptional hE ha'
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact Or.inl (neg_le_neg (hc _))

end Proof_prop_km2b_dlt_klt_iff_round_down_zero

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Proof_prop_km2b_dlt_klt_iff_round_down_zero

/-- **Dlt versus klt** (Kollár–Mori, Proposition 2.41). Let `(X, Δ)` be a dlt pair, with
canonical divisor `K` of dimension `n`, over an algebraically closed field of characteristic
zero. Then `(X, Δ)` is klt if and only if `⌊Δ⌋ = 0`. -/
@[mmp "prop_km2b_dlt_klt_iff_round_down_zero"]
public theorem IsDltPair.isKltPair_iff_roundDown_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : IsDltPair sX n K Δ) : IsKltPair sX n K Δ ↔ Δ.roundDown = 0 := by
  refine ⟨fun hk => DivisorWithCoeffs.ext' fun P => ?_, fun h0 => ?_⟩
  · rw [DivisorWithCoeffs.coeff_roundDown]
    exact Int.floor_eq_zero_iff.mpr ⟨(h.2.1 P).1, roundDown_nonpos_iff.mp hk.2.2 P⟩
  · refine ⟨h.1, ?_, h0.le⟩
    obtain ⟨Z, hZ, hsm, hsnc, Y, f, hf, hZY, hS, hG⟩ :=
      (isDltPair_iff_exists_isLogResolution h.1 h.2.1).mp h
    obtain ⟨δ, hδ, hδZ⟩ :=
      exists_pos_forall_le_discrepancy_of_isLogResolution h.1 h.2.1 hZ hsm hsnc hf hZY hS hG
    obtain ⟨c, hc1, hc⟩ := exists_lt_one_forall_coeff_le (roundDown_nonpos_iff.mp h0.le)
    set U : X.Opens := Z.compl
    have : Nonempty U := by
      obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp fun e => hZ (Closeds.ext e)
      exact ⟨⟨x, hx⟩⟩
    set dU := discrep (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)
    obtain ⟨b, hb1, hbδ, hbc⟩ : ∃ b : ℚ, -1 < b ∧ b ≤ -1 + δ ∧ b ≤ -c :=
      ⟨min (-1 + δ) (-c), lt_min (by linarith) (by linarith), min_le_left _ _, min_le_right _ _⟩
    have hb : (-1 : EReal) < ((b : ℝ) : EReal) := by
      simpa using EReal.coe_lt_coe_iff.mpr (by exact_mod_cast hb1 : ((-1 : ℚ) : ℝ) < b)
    have key : ∀ (D : DivisorOver k sX) (a : ℚ), IsDiscrepancy sX n K Δ D a →
        ((b : ℝ) : EReal) ≤ ((a : ℝ) : EReal) ∨ (-1 < dU ∧ dU ≤ ((a : ℝ) : EReal)) := by
      intro D a ha
      by_cases hDZ : (D.center : Set X) ⊆ Z
      · exact Or.inl (by exact_mod_cast hbδ.trans (hδZ D a hDZ ha))
      obtain ⟨x, hx, hxZ⟩ := Set.not_subset.mp hDZ
      exact (neg_le_or_discrep_restrictOpen_le h.1 hsm hsnc hc1 hc ⟨x, hx, hxZ⟩ ha).imp_left
        fun h1 => by exact_mod_cast hbc.trans h1
    by_cases hdU : -1 < dU
    · refine (lt_min hb hdU).trans_le (le_discrep_iff.mpr fun D a _ ha => ?_)
      exact (key D a ha).elim inf_le_left.trans fun h1 => inf_le_right.trans h1.2
    · refine hb.trans_le (le_discrep_iff.mpr fun D a _ ha => ?_)
      exact (key D a ha).resolve_right fun h1 => hdU h1.1

end MMP.Mori

namespace Proof_prop_km2b_dlt_perturbation_dlt

open CategoryTheory TopologicalSpace MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor

/-! ### Clearing denominators -/

/-- Some positive multiple of a `ℚ`-divisor is integral. -/
private theorem exists_toQDivisor_eq_smul {X : Scheme.{u}} (Δ₁ : QDivisor X) :
    ∃ m : ℕ, 0 < m ∧ ∃ E₁ : Divisor X, Divisor.toQDivisor E₁ = (m : ℚ) • Δ₁ := by
  classical
  set m : ℕ := ∏ P ∈ Δ₁.support, (Δ₁ P).den
  have hm0 : 0 < m := Finset.prod_pos fun P _ => (Δ₁ P).den_pos
  have hint : ∀ P, ∃ z : ℤ, (z : ℚ) = (m : ℚ) * Δ₁ P := by
    intro P
    by_cases hP : P ∈ Δ₁.support
    · obtain ⟨c, hc⟩ : (Δ₁ P).den ∣ m := Finset.dvd_prod_of_mem _ hP
      refine ⟨c * (Δ₁ P).num, ?_⟩
      rw [hc]
      push_cast
      rw [← Rat.mul_den_eq_num (Δ₁ P)]
      ring
    · rw [Finsupp.notMem_support_iff.mp hP]
      exact ⟨0, by simp⟩
  choose z hz using hint
  refine ⟨m, hm0, Finsupp.onFinset Δ₁.support z fun P hP => ?_, ?_⟩
  · exact Finsupp.mem_support_iff.mpr fun h0 => hP (by simpa [h0] using hz P)
  · ext P
    change ((Finsupp.onFinset _ z _ P : ℤ) : ℚ) = _
    rw [Finsupp.onFinset_apply, hz]
    rfl

/-- Finitely many positive rationals have a common positive lower bound. -/
private theorem exists_pos_forall_le {α : Type*} (s : Finset α) (b : α → ℚ)
    (hb : ∀ a ∈ s, 0 < b a) : ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ ∀ a ∈ s, c ≤ b a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc, hc1, hcs⟩ := ih fun x hx => hb x (Finset.mem_insert_of_mem hx)
    refine ⟨min c (b a), lt_min hc (hb a (Finset.mem_insert_self a s)),
      (min_le_left _ _).trans hc1, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcs x hx)

/-! ### Finite sums of global sections -/

/-- The reduced divisor `∑_{F ∈ S} F` has support `S`. -/
private theorem support_sum_single {Y : Scheme.{u}} (S : Finset (PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- A prime divisor contains its generic point. -/
private theorem genericPoint_mem_support {Y : Scheme.{u}} (F : PrimeDivisor Y) :
    F.genericPoint ∈ F.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- A general linear combination of finitely many sections, one of them nonzero, is nonzero:
the coefficient vectors `c` with `∑ cᵢ sᵢ = 0` form a proper subspace of `kⁱ`, contained in the
kernel of a linear form `ℓ` with `ℓ(e_j) ≠ 0`. -/
private theorem exists_polynomial_sum_smul_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤) (j : ι)
    (hj : s j ≠ 0) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0 := by
  classical
  let p : Submodule k (ι → k) :=
    { carrier := {c | ∑ i, scalarsToGlobalSections k sX (c i) • s i = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at *
        rw [← Finset.smul_sum, hc, smul_zero] }
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    apply hj
    have : ∑ i, scalarsToGlobalSections k sX ((Pi.single j 1 : ι → k) i) • s i = 0 := h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp),
      Pi.single_eq_same, map_one, one_smul] at this
  obtain ⟨ℓ, hℓ, hp⟩ := Submodule.exists_le_ker_of_notMem hjp
  let Q : MvPolynomial ι k :=
    ∑ i, MvPolynomial.C (ℓ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c Q = ℓ c := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ ℓ c]
    simp [Q, MvPolynomial.eval_sum, mul_comm]
  refine ⟨Q, fun h => hℓ (by rw [← heval, h, map_zero]), fun c hc h0 => hc ?_⟩
  rw [heval]
  exact hp (show c ∈ p from h0)

/-! ### Global generation on the smooth open -/

section GlobalGeneration

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

omit [IsIntegral X] [CompactSpace X] in
/-- The stalk of `𝒪_X(D)` at `x` is torsion free along the germ of the frame `ψ⁻¹` given by a
local equation `ψ` of `D` near `x`. -/
private theorem eq_zero_of_smul_germ_invSection_eq_zero {D : Divisor X} {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) {x : X} (hx : x ∈ W)
    {r : TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x}
    (h0 : r • (TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf W x hx).hom hψ.invSection =
      0) :
    r = 0 := by
  set b : Γ(D.divisorialSheaf, W) := hψ.invSection
  have hgen := hψ.isLocalGenerator_invSection
  set G := TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf W x hx
  obtain ⟨V, hVW, hxV, a, ha⟩ := TopCat.Presheaf.exists_le_germ_eq _ r hx
  have e1 := PresheafOfModules.germ_ringCat_smul D.divisorialSheaf.val x V hxV a
    (D.divisorialSheaf.val.presheaf.map (homOfLE hVW).op b)
  have e2 := TopCat.Presheaf.germ_res_apply D.divisorialSheaf.val.presheaf (homOfLE hVW) x hxV b
  rw [ha, e2] at e1
  have e3 : r • G.hom b = (TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf V x hxV).hom 0 := by
    rw [h0, map_zero]
  obtain ⟨W', hxW', i1, i2, he⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV _ _ (e1.trans e3)
  have hle : W' ≤ W := i1.le.trans hVW
  rw [map_zero] at he
  have he2 := (PresheafOfModules.map_smul D.divisorialSheaf.val i1.op a _).symm.trans he
  have ha0 : X.presheaf.map i1.op a = 0 := by
    refine (hgen W' hle).1 ?_
    change _ • _ = (0 : Γ(X, W')) • _
    rw [zero_smul]
    exact he2
  exact ha.symm.trans ((TopCat.Presheaf.germ_res_apply _ i1 x hxW' a).symm.trans
    ((congrArg (TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj W' x hxW').hom
      ha0).trans (map_zero _)))

/-- If a global section `t` of `𝒪_X(D)` is `g ψ⁻¹` on `W` for a local equation `ψ` of `D` on `W`,
and `g` is a unit at `x`, then `t ≠ 0` and the divisor of zeros of `t` misses `x`. -/
private theorem exists_ne_zero_notMem_supp_zeroDivisor {D : Divisor X} {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) (t : D.divisorialSubmodule ⊤)
    {g : Γ(X, W)}
    (hval : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W),
      t.1 ⟨Z, trivial⟩ =
        (X.presheaf.germ W _ hZ).hom g * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z)
    {x : X} (hxg : x ∈ X.basicOpen g) :
    ∃ ht : t ≠ 0, x ∉ (D.zeroDivisor t ht).supp := by
  have hunit : ∀ y (hy : y ∈ X.basicOpen g),
      IsUnit ((X.presheaf.germ W y (X.basicOpen_le _ hy)).hom g) := fun y hy =>
    (X.mem_basicOpen g y (X.basicOpen_le _ hy)).mp hy
  have hZ₀ : componentGenericPoint X (pointComponent x) ∈ X.basicOpen g :=
    ((isGenericPoint_componentGenericPoint X _).specializes
      (mem_pointComponent x)).mem_open (X.basicOpen _).isOpen hxg
  have hi : t ≠ 0 := by
    intro h0
    have h2 := hval (pointComponent x) (X.basicOpen_le _ hZ₀)
    rw [h0] at h2
    have h3 : IsUnit ((X.presheaf.germ W _ (X.basicOpen_le _ hZ₀)).hom g *
        ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) (pointComponent x)) :=
      (hunit _ hZ₀).mul ((Pi.isUnit_iff.mp (ψ⁻¹).isUnit) _)
    rw [← h2] at h3
    exact not_isUnit_zero h3
  refine ⟨hi, fun hxs => ?_⟩
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxs
  apply hE
  have hηE : E.genericPoint ∈ X.basicOpen g := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    exact (specializes_iff_mem_closure.mpr hxE).mem_open (X.basicOpen _).isOpen hxg
  have hηW : E.genericPoint ∈ W := X.basicOpen_le _ hηE
  have hZ : componentGenericPoint X E.component ∈ W :=
    E.specializes_genericPoint.mem_open W.isOpen hηW
  set u := (Divisor.isUnit_sectionToRationalFunctions hi).unit
  have hv := congrArg E.valuation (hval E.component hZ)
  have hgerm : (X.presheaf.germ W _ hZ).hom g =
      E.toComponent.hom ((X.presheaf.germ W _ hηW).hom g) := by
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hηW E.specializes_genericPoint]
    rfl
  rw [map_mul, hgerm, E.valuation_toComponent_of_isUnit (hunit _ hηE), one_mul,
    PrimeDivisor.valuation_component, PrimeDivisor.ord_inv,
    ← hψ E ⟨E.genericPoint, genericPoint_mem_support E, hηW⟩] at hv
  have hv' : E.valuation ((u : RationalFunctions X) E.component) =
      WithZero.exp (-D.coeff E) := hv
  rw [PrimeDivisor.valuation_component] at hv'
  have hv'' := WithZero.exp_injective hv'
  have hc : (D.zeroDivisor _ hi).coeff E = (principalDivisor u).coeff E + D.coeff E := rfl
  refine hc.trans ?_
  rw [coeff_principalDivisor]
  omega

/-- **A generating family has a member whose divisor of zeros misses a point where the divisor
is Cartier.** If the global sections `sᵢ` generate `𝒪_X(D)` and `ψ` is a local equation of `D`
near `x`, write `sᵢ = gᵢ ψ⁻¹` near `x`; since the germs of the `sᵢ` span the stalk, some `gᵢ` is a
unit at `x`, and then `(sᵢ)₀ = div(gᵢ)` misses `x`. -/
private theorem exists_notMem_supp_zeroDivisor {D : Divisor X}
    (σ : D.divisorialSheaf.GeneratingSections) [Finite σ.I] {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) {x : X} (hx : x ∈ W) :
    ∃ i, ∃ hi : ((σ.s i).eval (Opposite.op ⊤) : D.divisorialSubmodule ⊤) ≠ 0,
      x ∉ (D.zeroDivisor _ hi).supp := by
  classical
  have hspan := (AlgebraicGeometry.generates_iff_stalkwise_generates _ _ σ.s).mp σ.epi x
  have hfin : Finite σ.I := inferInstance
  revert hspan hfin
  obtain ⟨I, s, -⟩ := σ
  intro hspan hfin
  haveI := Fintype.ofFinite I
  dsimp only at hspan ⊢
  set b : Γ(D.divisorialSheaf, W) := hψ.invSection with hb
  have hgen := hψ.isLocalGenerator_invSection
  have hs : ∀ i, ∃ g : Γ(X, W), g • D.divisorialSheaf.presheaf.map (homOfLE (le_refl W)).op b =
      D.divisorialSheaf.presheaf.map (homOfLE le_top).op ((s i).eval (Opposite.op ⊤)) :=
    fun i => (hgen W le_rfl).2 _
  choose g hg using hs
  have hbW : D.divisorialSheaf.presheaf.map (homOfLE (le_refl W)).op b = b := by
    rw [show (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) from rfl, CategoryTheory.Functor.map_id]
    rfl
  rw [hbW] at hg
  set G := TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf W x hx
  have hmem : G b ∈
      Submodule.span (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)
        (Set.range fun i => (TopCat.Presheaf.Γgerm D.divisorialSheaf.val.presheaf x).hom
          ((s i).eval (Opposite.op ⊤))) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  have hgerm : ∀ i, (TopCat.Presheaf.Γgerm D.divisorialSheaf.val.presheaf x).hom
      ((s i).eval (Opposite.op ⊤)) = G.hom (g i • b) := by
    intro i
    rw [hg i]
    exact (TopCat.Presheaf.germ_res_apply _ (homOfLE le_top) x hx _).symm
  have hsm : ∀ i, G.hom (g i • b) = (TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj
      W x hx).hom (g i) • G.hom b := fun i =>
    PresheafOfModules.germ_ringCat_smul D.divisorialSheaf.val x W hx (g i) b
  simp only [hgerm, hsm, smul_smul, ← Finset.sum_smul] at hc
  set RG := TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj W x hx
  set r := ∑ i, c i * RG.hom (g i)
  have hr1 : r = 1 := by
    have h0 : (1 - r) • G.hom b = 0 := by rw [sub_smul, one_smul, hc, sub_self]
    exact (sub_eq_zero.mp (eq_zero_of_smul_germ_invSection_eq_zero hψ hx h0)).symm
  obtain ⟨i, -, hu⟩ : ∃ i ∈ Finset.univ, IsUnit ((X.presheaf.germ W x hx).hom (g i)) := by
    have hge : ∀ i, SemilinearStalk.commStalkRingEquiv X.presheaf x (RG.hom (g i)) =
        (X.presheaf.germ W x hx).hom (g i) := fun i =>
      SemilinearStalk.commStalkRingEquiv_germ X.presheaf x W hx (g i)
    set e := SemilinearStalk.commStalkRingEquiv X.presheaf x
    have h1 : ∑ i, e (c i) * (X.presheaf.germ W x hx).hom (g i) = 1 := by
      have h3 : e r = ∑ i, e (c i * RG.hom (g i)) := map_sum e _ _
      have h4 : ∀ i, e (c i * RG.hom (g i)) = e (c i) * (X.presheaf.germ W x hx).hom (g i) :=
        fun i => (map_mul e _ _).trans (congrArg _ (hge i))
      simp only [h4] at h3
      exact h3.symm.trans ((congrArg e hr1).trans (map_one e))
    obtain ⟨i, hi, hu⟩ := IsLocalRing.exists_of_isUnit_sum (h1 ▸ isUnit_one)
    exact ⟨i, hi, isUnit_of_mul_isUnit_right hu⟩
  refine ⟨i, exists_ne_zero_notMem_supp_zeroDivisor hψ ((s i).eval (Opposite.op ⊤))
    (fun Z hZ => ?_) ((X.mem_basicOpen (g i) x hx).mpr hu)⟩
  have := congrArg (fun m : D.divisorialSubmodule W => m.1 ⟨Z, hZ⟩) (hg i)
  simp only [Submodule.coe_smul, rationalFunctions_smul_apply] at this
  exact this.symm

/-- `𝒪_X(nL) ≅ 𝒪_X(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {L : Divisor X} (hL : L.IsCartier) (n : ℕ)
    (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule X L.divisorialSheaf (n : ℤ)) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso X _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso X _).symm

/-- **Serre generation for `𝒪_X(E + m'H)`** ([Stacks, Tag 01Q3]). For an ample Cartier divisor
`H` on a variety and any divisor `E`, for some `m' > 0` the sheaf `𝒪_X(E + m'H)` is generated by
finitely many global sections: `𝒪_X(E)` is coherent, so `𝒪_X(E) ⊗ 𝒪_X(H)^{⊗ m'}` is globally
generated for `m' ≫ 0`, and multiplication `𝒪_X(E) ⊗ 𝒪_X(m'H) ⟶ 𝒪_X(E + m'H)` is an
isomorphism. -/
private theorem exists_generatingSections {k : Type u} [Field k] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) {H : Divisor X} (hH : H.IsCartier) (hHa : H.IsAmple hH)
    (E : Divisor X) :
    ∃ m' : ℕ, 0 < m' ∧ ∃ σ : (E + m' • H).divisorialSheaf.GeneratingSections, Finite σ.I := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  have hcoh := MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul sX hX E
  haveI := (hcoh H).1
  have hqc := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    E.divisorialSheaf
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hHa).2 E.divisorialSheaf hqc.1 hqc.2
  set n : ℕ := max n₀.toNat 1 with hn
  obtain ⟨σ, hσ⟩ := hn₀ (n : ℤ) (by omega)
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory X
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso X E.divisorialSheaf
    (Stacks.Ample.tensorPowModule X H.divisorialSheaf (n : ℤ))
  obtain ⟨e⟩ := nonempty_divisorialSheaf_nsmul_iso hH n (le_max_right _ _)
  let pI := i ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl _) e.symm ≪≫
    @asIso _ _ _ _ (E.divisorialSheafTensorMul (n • H)) ((hcoh (n • H)).2.2 (hH.nsmul n))
  let p := pI.hom
  haveI : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ p :=
    @IsIso.epi_of_iso _ _ _ _ p inferInstance
  exact ⟨n, by omega, σ.ofEpi p, hσ⟩

omit [CompactSpace X] in
/-- A divisor whose restriction to an open `V` is Cartier has a local equation near every point
of `V`: a local equation of `D|_V` on `W ⊆ V` is one of `D` on `W`, since the prime divisors of
`X` meeting `W` are the closures of those of `V` meeting `W`, with the same local rings. -/
private theorem exists_isLocalEquation_of_isCartier_restrictOpen {D : Divisor X}
    {V : X.Opens} (h : Divisor.IsCartier (D.restrictOpen V)) {x : X} (hx : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation W φ := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hx⟩)
  obtain ⟨W, hxW, φ', hφ'⟩ := h ⟨x, hx⟩
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units φ'
  obtain ⟨g, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤
    ⟨⟨x, hx⟩, trivial⟩).2 g'
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (g := g)
    (fun h0 => hg' (by rw [h0, map_zero]))
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hxW, rfl⟩, φ, fun E hE => ?_⟩
  have hEW : E.genericPoint ∈ V.ι ''ᵁ W := (E.genericPoint_mem_iff _).2 hE
  obtain ⟨y, hyW, hy⟩ := hEW
  obtain ⟨E₀, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι E).2 ⟨y, hy⟩
  have hgp : V.ι E₀.genericPoint = V.ι y :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm.trans hy.symm
  have hE₀ : (E₀.support ∩ (W : Set V)).Nonempty := by
    rw [← PrimeDivisor.genericPoint_mem_iff]
    have : E₀.genericPoint = y := V.ι.isOpenEmbedding.injective hgp
    change E₀.genericPoint ∈ W
    rw [this]
    exact hyW
  have h1 := hφ' E₀ hE₀
  rw [DivisorWithCoeffs.coeff_restrictOpen] at h1
  rw [h1, hφg', hφ, MMP.Positivity.ord_functionFieldMap_of_isIso V.ι E₀ _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

omit [CompactSpace X] in
/-- Every divisor has a local equation near a smooth point. -/
private theorem exists_isLocalEquation_of_mem_smoothLocus {k : Type u} [Field k]
    {s : X ⟶ Spec (.of k)} (D : Divisor X) {x : X}
    (hx : x ∈ smoothLocus s) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation W φ :=
  exists_isLocalEquation_of_isCartier_restrictOpen
    (MMP.Fourfold.isCartier_of_isSmoothScheme (isSmoothScheme_ι_of_le_smoothLocus le_rfl) _) hx

end GlobalGeneration

/-- **Serre generation on the smooth locus.** For an ample Cartier divisor `H` and any divisor
`E₁` on a quasi-projective normal variety, some `𝒪_X(E₁ + m'H)`, `m' > 0`, has finitely many
global sections such that every point `x` of an open `U` contained in the smooth locus lies off
the divisor of zeros of one of them. -/
private theorem exists_sections {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety k sX) {H : Divisor X} (hH : H.IsCartier)
    (hHa : H.IsAmple hH) (E₁ : Divisor X) (U : X.Opens) (hU : U ≤ smoothLocus sX) :
    ∃ m' : ℕ, 0 < m' ∧ ∃ (N : ℕ) (t : Fin (N + 1) → (E₁ + m' • H).divisorialSubmodule ⊤),
      ∀ x ∈ U, ∃ i, ∃ hi : t i ≠ 0, x ∉ ((E₁ + m' • H).zeroDivisor (t i) hi).supp := by
  obtain ⟨m', hm', σ, hσ⟩ := exists_generatingSections hX.1 hH hHa E₁
  haveI := Fintype.ofFinite σ.I
  refine ⟨m', hm', ?_⟩
  by_cases hI : Nonempty σ.I
  · obtain ⟨N, hN⟩ : ∃ N, Fintype.card σ.I = N + 1 :=
      Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
    let e : σ.I ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hN
    refine ⟨N, fun j => (σ.s (e.symm j)).eval (Opposite.op ⊤), fun x hx => ?_⟩
    obtain ⟨W, hxW, φ, hφ⟩ := exists_isLocalEquation_of_mem_smoothLocus (E₁ + m' • H) (hU hx)
    obtain ⟨i, hi⟩ := exists_notMem_supp_zeroDivisor σ hφ hxW
    have key : ∀ j, j = i → ∃ hj : ((σ.s j).eval (Opposite.op ⊤) :
        (E₁ + m' • H).divisorialSubmodule ⊤) ≠ 0,
          x ∉ ((E₁ + m' • H).zeroDivisor _ hj).supp := by
      rintro j rfl
      exact hi
    exact ⟨e i, key _ (e.symm_apply_apply i)⟩
  · refine ⟨0, fun _ => 0, fun x hx => ?_⟩
    obtain ⟨W, hxW, φ, hφ⟩ := exists_isLocalEquation_of_mem_smoothLocus (E₁ + m' • H) (hU hx)
    obtain ⟨i, -⟩ := exists_notMem_supp_zeroDivisor σ hφ hxW
    exact absurd ⟨i⟩ hI

/-! ### Restricting sections to an open subscheme -/

section RestrictOpen

open Opposite

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

section DivisorialRestrict

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext (by
    have h1 := Z.1.2; have h2 := Z'.1.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, -⟩ := h
  exact ((genericPoint_spec U.toScheme).specializes trivial).mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

/-- Orders along a prime divisor `E'` of `U` and along its closure in `X` agree on restricted
rational functions. -/
private theorem ordGE_restrictRF_iff (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) (n : ℤ)
    (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
    (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty) :
    E'.OrdGE n (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
      MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E') n
        (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
          (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
  rw [ordGE_iff_evFF, ordGE_iff_evFF, evFF_restrictRF U V ψ _
      ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
    divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective]
  rfl

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact ordGE_restrictRF_iff U V ψ _ E' hE' hP
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨x, hx, hxe⟩ => by
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx⟩
  refine ⟨fun h P hP => ?_, fun h E' hE' =>
    (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))⟩
  have hPU : P.genericPoint ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
    rw [← hx]
    exact x.2
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
  exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction to the open subscheme `U` of a global section of `𝒪_X(D)`, a global section
of `𝒪_U(D|_U)`. -/
private noncomputable def restrictSection (D : Divisor X) (t : D.divisorialSubmodule ⊤) :
    Divisor.divisorialSubmodule (D.restrictOpen U) ⊤ :=
  ⟨restrictRF U ⊤ ((rationalFunctionsPresheaf X).map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op t.1),
    (isDivisorialSection_restrictRF_iff U D ⊤ _).2 fun E h =>
      t.2 E (let ⟨y, hy, _⟩ := h; ⟨y, hy, trivial⟩)⟩

private theorem genericPoint_mem_image_top (Z : irreducibleComponents X) :
    componentGenericPoint X Z ∈ U.ι ''ᵁ ⊤ := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
  exact ⟨_, trivial, rfl⟩

private theorem restrictSection_injective (D : Divisor X) :
    Function.Injective (restrictSection U D) := fun _ _ h =>
  Subtype.ext <| funext fun Z =>
    congrFun (restrictRF_injective U ⊤ (congrArg Subtype.val h))
      ⟨Z.1, genericPoint_mem_image_top U Z.1⟩

private theorem restrictSection_zero (D : Divisor X) : restrictSection U D 0 = 0 :=
  Subtype.ext (restrictRF_zero U ⊤)

private theorem restrictSection_add (D : Divisor X) (t t' : D.divisorialSubmodule ⊤) :
    restrictSection U D (t + t') = restrictSection U D t + restrictSection U D t' :=
  Subtype.ext (restrictRF_add U ⊤ _ _)

private theorem restrictSection_smul (D : Divisor X) (r : Γ(X, ⊤)) (t : D.divisorialSubmodule ⊤) :
    restrictSection U D (r • t) = U.ι.appTop r • restrictSection U D t := by
  apply Subtype.ext
  change restrictRF U ⊤ ((rationalFunctionsPresheaf X).map _ (r • t.1)) =
    U.ι.appTop r • restrictRF U ⊤ _
  rw [rationalFunctionsPresheaf_map_smul, ← restrictRF_smul]
  congr 2
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
  change _ = (Scheme.Hom.app U.ι ⊤) r
  rw [Scheme.Opens.ι_app]
  rfl

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [Nonempty U] [IsDominant U.ι] in
/-- For a unit `φ` of `K(Y)`, `v_E(φ) ≥ n` exactly when `n ≤ ord_E φ`. -/
private theorem ordGE_iff_le_ord {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (φ : (RationalFunctions Y)ˣ) (n : ℤ) :
    E.OrdGE n ((φ : RationalFunctions Y) E.component) ↔ n ≤ E.ord φ := by
  have h0 : (φ : RationalFunctions Y) E.component ≠ 0 := ((Pi.isUnit_iff.mp φ.isUnit) _).ne_zero
  rw [MMP.Mori.PrimeDivisor.OrdGE, PrimeDivisor.valuation_component, WithZero.exp_le_exp]
  simp [h0]

/-- The divisor of zeros of the restriction of a section to `U` is the restriction of its
divisor of zeros. -/
private theorem coeff_zeroDivisor_restrictSection [CompactSpace X] [CompactSpace U]
    (D : Divisor X) (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (ht' : restrictSection U D t ≠ 0)
    (W : MMP.Mori.PrimeDivisor U.toScheme) :
    (Divisor.zeroDivisor (D.restrictOpen U) (restrictSection U D t) ht').coeff W =
      (D.zeroDivisor t ht).coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := by
  set u := (Divisor.isUnit_sectionToRationalFunctions ht).unit
  set u' := (Divisor.isUnit_sectionToRationalFunctions ht').unit
  have hc : (Divisor.zeroDivisor (D.restrictOpen U) _ ht').coeff W =
      W.ord u' + D.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := by
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    rfl
  have hc' : (D.zeroDivisor t ht).coeff (OpenWeilRestriction.primeDivisorMap U.ι W) =
      MMP.Mori.PrimeDivisor.ord (OpenWeilRestriction.primeDivisorMap U.ι W) u +
        D.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := by
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  rw [hc, hc']
  congr 1
  have hE' : (W.support ∩ ⊤).Nonempty := ⟨W.genericPoint, genericPoint_mem_support W, trivial⟩
  have hP : ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ U.ι ''ᵁ ⊤).Nonempty := by
    refine ⟨_, genericPoint_mem_support (OpenWeilRestriction.primeDivisorMap U.ι W), ?_⟩
    rw [show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι W) =
      U.ι W.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    exact ⟨_, trivial, rfl⟩
  have key : ∀ n, n ≤ W.ord u' ↔
      n ≤ MMP.Mori.PrimeDivisor.ord (OpenWeilRestriction.primeDivisorMap U.ι W) u :=
    fun n => by
      rw [← ordGE_iff_le_ord, ← ordGE_iff_le_ord]
      exact ordGE_restrictRF_iff U ⊤ _ n W hE' hP
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [Nonempty U] [IsDominant U.ι] in
/-- The closure in `X` of a prime divisor `W` of `U` contains the image of `W`. -/
private theorem mem_support_primeDivisorMap (W : MMP.Mori.PrimeDivisor U.toScheme)
    {y : U.toScheme} (hy : y ∈ W.support) :
    U.ι y ∈ (OpenWeilRestriction.primeDivisorMap U.ι W).support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hy ⊢
  rw [show (OpenWeilRestriction.primeDivisorMap U.ι W).genericPoint = U.ι W.genericPoint
    from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
  exact hy.map U.ι.continuous

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [Nonempty U] [IsDominant U.ι] in
/-- The closure in `X` of a prime divisor of `U` meets `U`. -/
private theorem support_primeDivisorMap_inter_nonempty (W : MMP.Mori.PrimeDivisor U.toScheme) :
    ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ U).Nonempty :=
  ⟨_, mem_support_primeDivisorMap U W (genericPoint_mem_support W), (W.genericPoint).2⟩

/-- Restriction to `U` sends a nonzero section to a nonzero section. -/
private theorem restrictSection_ne_zero (D : Divisor X) {t : D.divisorialSubmodule ⊤}
    (ht : t ≠ 0) : restrictSection U D t ≠ 0 :=
  fun h => ht (restrictSection_injective U D (h.trans (restrictSection_zero U D).symm))

/-- If at every point of `U` some `tᵢ` has divisor of zeros missing it, the same holds for the
restrictions of the `tᵢ` to `U`. -/
private theorem exists_notMem_supp_zeroDivisor_restrictSection [CompactSpace X] [CompactSpace U]
    (M : Divisor X) {ι : Type*} (t : ι → M.divisorialSubmodule ⊤)
    (ht : ∀ x ∈ U, ∃ i, ∃ hi : t i ≠ 0, x ∉ (M.zeroDivisor (t i) hi).supp) (y : U.toScheme) :
    ∃ (i : ι) (hi : restrictSection U M (t i) ≠ 0),
      y ∉ (Divisor.zeroDivisor (M.restrictOpen U) (restrictSection U M (t i)) hi).supp := by
  obtain ⟨i, hi, hy⟩ := ht (U.ι y) y.2
  refine ⟨i, restrictSection_ne_zero U M hi, fun hyy => hy ?_⟩
  obtain ⟨W, hW, hyW⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyy
  rw [coeff_zeroDivisor_restrictSection U M (t i) hi] at hW
  exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨_, hW, mem_support_primeDivisorMap U W hyW⟩

/-- Restriction to `U` commutes with `k`-linear combinations of global sections. -/
private theorem restrictSection_sum_smul {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (M : Divisor X) {ι : Type*} [Fintype ι] (c : ι → k) (t : ι → M.divisorialSubmodule ⊤) :
    restrictSection U M (∑ i, scalarsToGlobalSections k sX (c i) • t i) =
      ∑ i, scalarsToGlobalSections k (U.ι ≫ sX) (c i) • restrictSection U M (t i) := by
  let ρ : M.divisorialSubmodule ⊤ →+ Divisor.divisorialSubmodule (M.restrictOpen U) ⊤ :=
    { toFun := restrictSection U M
      map_zero' := restrictSection_zero U M
      map_add' := restrictSection_add U M }
  change ρ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change restrictSection U M _ = _
  rw [restrictSection_smul]
  congr 1

end DivisorialRestrict

end RestrictOpen

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] :
    IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisor of zeros depends only on the section. -/
private theorem zeroDivisor_congr {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (D : Divisor Y) {σ σ' : D.divisorialSubmodule ⊤}
    (h : σ = σ') (hσ : σ ≠ 0) (hσ' : σ' ≠ 0) : D.zeroDivisor σ hσ = D.zeroDivisor σ' hσ' := by
  subst h
  rfl

/-- Two nonzero polynomials over an infinite field have a common point where neither vanishes. -/
private theorem exists_eval_ne_zero_and_eval_ne_zero {k : Type*} [Field k] [Infinite k]
    {σ : Type*} {Q Q' : MvPolynomial σ k} (hQ : Q ≠ 0) (hQ' : Q' ≠ 0) :
    ∃ c : σ → k, MvPolynomial.eval c Q ≠ 0 ∧ MvPolynomial.eval c Q' ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : σ → k, MvPolynomial.eval c (Q * Q') ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hQ hQ' (MvPolynomial.funext fun c => by simpa using h c)
  rw [map_mul] at hc
  exact ⟨c, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc⟩

/-! ### Bertini on the smooth open -/

/-- **A general member of a free linear system on the smooth open.** Let `U` be a nonempty open
of a normal variety contained in the smooth locus, on which `G` is snc, and let `M` be a divisor
with finitely many global sections of `𝒪_X(M)`, one of which does not vanish at any given point
of `U`. Then some nonzero section `τ` has divisor of zeros `(τ)₀` sharing no component meeting
`U` with `G`, and every divisor whose components meeting `U` are components of `G` or of `(τ)₀`
is snc on `U`. -/
private theorem exists_member {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety k sX) (U : X.Opens) (hUne : (U : Set X).Nonempty)
    (hU : U ≤ smoothLocus sX) (G : QDivisor X) (hG : (G.restrictOpen U).IsSNC (U.ι ≫ sX))
    (M : Divisor X) {N : ℕ} (t : Fin (N + 1) → M.divisorialSubmodule ⊤)
    (ht : ∀ x ∈ U, ∃ i, ∃ hi : t i ≠ 0, x ∉ (M.zeroDivisor (t i) hi).supp) :
    ∃ (τ : M.divisorialSubmodule ⊤) (hτ : τ ≠ 0),
      (∀ P : PrimeDivisor X, (P.support ∩ U).Nonempty → (M.zeroDivisor τ hτ).coeff P ≠ 0 →
        G.coeff P = 0) ∧
      ∀ B : QDivisor X, (∀ P : PrimeDivisor X, (P.support ∩ U).Nonempty → B.coeff P ≠ 0 →
          G.coeff P ≠ 0 ∨ (M.zeroDivisor τ hτ).coeff P ≠ 0) →
        (B.restrictOpen U).IsSNC (U.ι ≫ sX) := by
  classical
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : Nonempty U := hUne.to_subtype
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hUne)
  have hUv : IsNormalVariety k (U.ι ≫ sX) := isNormalVariety_ι hX U
  have hUs : IsSmoothScheme (U.ι ≫ sX) := isSmoothScheme_ι_of_le_smoothLocus hU
  haveI : IsLocallyNoetherian U.toScheme := hUv.isLocallyNoetherian
  haveI : IsNormal U.toScheme := hUv.isNormal
  haveI : IsIntegral U.toScheme := hUv.isIntegral
  haveI : CompactSpace U.toScheme := by
    haveI : QuasiCompact (U.ι ≫ sX) := hUv.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ sX⟩
  haveI : IsSmoothVariety k (U.toScheme ↘ Spec (.of k)) :=
    (isSmoothVariety_iff k _).mpr ⟨hUv.1, hUs.smooth⟩
  set MU : Divisor U.toScheme := M.restrictOpen U with hMUdef
  have hMU : Divisor.IsCartier MU := MMP.Fourfold.isCartier_of_isSmoothScheme hUs MU
  set tU := fun i => restrictSection U M (t i) with htUdef
  have htU : ∀ y : U.toScheme, ∃ (i : Fin (N + 1)) (hi : tU i ≠ 0),
      y ∉ (Divisor.zeroDivisor MU (tU i) hi).supp :=
    exists_notMem_supp_zeroDivisor_restrictSection U M t ht
  set S := (G.restrictOpen U).support with hSdef
  have hS : DivisorWithCoeffs.IsSNC (U.toScheme ↘ Spec (.of k))
      (∑ E ∈ S, Finsupp.single E (1 : ℤ)) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq (by rw [support_sum_single])).mp hG
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_zeroDivisor_eq_sum_isSNC (k := k) MU hMU tU htU S hS
  obtain ⟨j, hj, -⟩ := htU (Classical.arbitrary U.toScheme)
  obtain ⟨Q', hQ'0, hQ'⟩ := exists_polynomial_sum_smul_ne_zero (U.toScheme ↘ Spec (.of k)) tU j hj
  obtain ⟨c, hc, hc'⟩ := exists_eval_ne_zero_and_eval_ne_zero hQ0 hQ'0
  have hτU := hQ' c hc'
  set τ := ∑ i, scalarsToGlobalSections k sX (c i) • t i
  have hρ : restrictSection U M τ =
      ∑ i, scalarsToGlobalSections k (U.toScheme ↘ Spec (.of k)) (c i) • tU i :=
    restrictSection_sum_smul U sX M c t
  have hτ : τ ≠ 0 := fun h => hτU (by rw [← hρ, h, restrictSection_zero])
  obtain ⟨T, hTeq, hTS, hsnc, -⟩ := hQ c hc hτU
  have hT : ∀ W, (Divisor.zeroDivisor MU _ hτU).coeff W ≠ 0 → W ∈ T := fun W hW => by
    rw [← support_sum_single T, Finsupp.mem_support_iff]
    rwa [hTeq] at hW
  have hcoeff : ∀ W, (M.zeroDivisor τ hτ).coeff (OpenWeilRestriction.primeDivisorMap U.ι W) =
      (Divisor.zeroDivisor MU _ hτU).coeff W := by
    intro W
    rw [← coeff_zeroDivisor_restrictSection U M τ hτ (restrictSection_ne_zero U M hτ),
      zeroDivisor_congr _ hρ]
  refine ⟨τ, hτ, fun P hP hP0 => ?_, fun B hB => ?_⟩
  · obtain ⟨W, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι P).2 (by
      rw [Scheme.Opens.range_ι]
      exact (P.genericPoint_mem_iff U).2 hP)
    rw [hcoeff] at hP0
    have hWS : W ∉ S := Finset.disjoint_left.mp hTS (hT W hP0)
    rwa [hSdef, Finsupp.notMem_support_iff] at hWS
  · refine hsnc.of_support_subset fun W hW => ?_
    rw [support_sum_single, Finset.mem_union]
    rw [Finsupp.mem_support_iff] at hW
    rcases hB _ (support_primeDivisorMap_inter_nonempty U W) hW with h | h
    · exact Or.inr (Finsupp.mem_support_iff.mpr h)
    · exact Or.inl (hT W (by rwa [← hcoeff]))

/-! ### The perturbed pair is dlt -/

/-- For `0 ≤ b ≤ a`, `0 ≤ d` and `0 < ε < 1`, `a + ε (d - b)` vanishes exactly when `a + d`
does. -/
theorem add_mul_sub_eq_zero_iff {a b d ε : ℚ} (hb : 0 ≤ b) (hba : b ≤ a) (hd : 0 ≤ d)
    (hε : 0 < ε) (hε1 : ε < 1) : a + ε * (d - b) = 0 ↔ a + d = 0 := by
  constructor
  · intro h0
    have ha : a = 0 := by nlinarith
    have hd0 : d = 0 := by nlinarith
    linarith
  · intro h0
    have ha : a = 0 := by linarith
    have hd0 : d = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha, hd0, hb0]

/-- For `0 ≤ b ≤ a ≤ 1`, `0 ≤ d`, `0 < ε < 1` and `ε d < 1 - a` when `d > 0`, the number
`a + ε (d - b)` lies in `[0, 1]`. -/
theorem add_mul_sub_mem_Icc {a b d ε : ℚ} (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) (hd : 0 ≤ d)
    (hε : 0 < ε) (hε1 : ε < 1) (hεd : 0 < d → ε * d < 1 - a) :
    0 ≤ a + ε * (d - b) ∧ a + ε * (d - b) ≤ 1 := by
  refine ⟨by nlinarith, ?_⟩
  rcases hd.eq_or_lt with rfl | hd0
  · nlinarith
  · nlinarith [hεd hd0]

/-- For `0 ≤ Δ₁ ≤ Δ`, `0 ≤ D` and `0 < ε < 1`, the divisor `Δ + ε (D - Δ₁)` vanishes along `P`
exactly when `Δ + D` does. -/
theorem coeff_add_smul_sub_eq_zero_iff {X : Scheme.{u}} {Δ Δ₁ D : QDivisor X}
    (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective) (hD : D.IsEffective) {ε : ℚ}
    (hε : 0 < ε) (hε1 : ε < 1) (P : PrimeDivisor X) :
    (Δ + ε • (D - Δ₁)).coeff P = 0 ↔ (Δ + D).coeff P = 0 := by
  have h := DivisorWithCoeffs.coeff_sub Δ Δ₁ P ▸ hΔΔ₁ P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_sub, smul_eq_mul]
  exact add_mul_sub_eq_zero_iff (hΔ₁ P) (by linarith) (hD P) hε hε1

/-- For `0 ≤ Δ₁ ≤ Δ`, `0 ≤ D` and `0 < ε < 1`, the divisor `Δ + ε (D - Δ₁)` has the same support
as `Δ + D`. -/
theorem supp_add_smul_sub {X : Scheme.{u}} {Δ Δ₁ D : QDivisor X}
    (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective) (hD : D.IsEffective) {ε : ℚ}
    (hε : 0 < ε) (hε1 : ε < 1) : (Δ + ε • (D - Δ₁)).supp = (Δ + D).supp := by
  have hs : (Δ + ε • (D - Δ₁)).support = (Δ + D).support := Finset.ext fun P => by
    simp only [Finsupp.mem_support_iff]
    exact not_congr (coeff_add_smul_sub_eq_zero_iff hΔ₁ hΔΔ₁ hD hε hε1 P)
  rw [DivisorWithCoeffs.supp, DivisorWithCoeffs.supp, hs]

/-- **Small perturbations keep exceptional discrepancies over `Z` above `-1`.** If every
discrepancy of `(X, Δ)` along a divisor with centre in the closed set `Z` is `> -1` and `B` is
`ℚ`-Cartier, then for a birational `f : Y → X` and all small `ε > 0` the discrepancies of
`(X, Δ + εB)` along the prime divisors of `Y` lying over `Z` are still `> -1`: only the finitely
many divisors along which `f^*B ≠ 0` move. -/
private theorem exists_pos_forall_neg_one_lt_isDiscrepancy_add_smul {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ B : QDivisor X}
    (hP : IsPairWith sX n K Δ) (hq : B.IsQCartier) {Z : Set X} (hZ : IsClosed Z)
    (hdisc : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ Z →
      IsDiscrepancy sX n K Δ D a → -1 < a)
    {R : RDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X} (hf : IsLogResolution sX R f) :
    ∃ c₁ : ℚ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ ε : ℚ, 0 < ε → ε < c₁ →
      ∀ (hY : IsNormalVariety k (f ≫ sX)) (G : PrimeDivisor Y), G.support ⊆ f ⁻¹' Z →
        ∀ a : ℚ, IsDiscrepancy sX n K (Δ + ε • B) ⟨Y, f, hY, hf.isBirationalMorphism, G⟩ a →
          -1 < a := by
  by_cases hY : IsNormalVariety k (f ≫ sX)
  · haveI := hY.isIntegral
    haveI := hY.isNormal
    haveI := hY.isLocallyNoetherian
    haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
    haveI : IsDominant f := hf.isBirationalMorphism.isDominant
    have hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ B.supp := by
      intro W
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
      exact MMP.Fourfold.genericPoint_notMem_supp B
    obtain ⟨B', hB'⟩ := (hq.existsUnique_isPullback hB).exists
    let EG : PrimeDivisor Y → DivisorOver k sX := fun G =>
      ⟨Y, f, hY, hf.isBirationalMorphism, G⟩
    have hform : ∀ (G : PrimeDivisor Y) (t a : ℚ),
        IsDiscrepancy sX n K (Δ + t • B) (EG G) (a - t * B'.coeff G) ↔
          IsDiscrepancy sX n K Δ (EG G) a := fun G =>
      ((hP.isDiscrepancy_add_smul_iff hq (EG G)).2.2 B' hB').2
    choose a₀ ha₀ using fun G =>
      MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1 (EG G)
    let s := B'.support.filter (fun G => 0 < B'.coeff G ∧ -1 < a₀ G)
    obtain ⟨c₁, hc₁, hc₁1, hc₁b⟩ := exists_pos_forall_le s
      (fun G => (a₀ G + 1) / B'.coeff G) fun G hG => by
        rw [Finset.mem_filter] at hG
        exact div_pos (by linarith [hG.2.2]) hG.2.1
    refine ⟨c₁, hc₁, hc₁1, fun ε hε hεc hY' G hG a ha => ?_⟩
    have hcen : ((EG G).center : Set X) ⊆ Z := by
      rw [DivisorOver.coe_center]
      exact closure_minimal (Set.image_subset_iff.mpr hG) hZ
    have ha' : IsDiscrepancy sX n K Δ (EG G) (a + ε * B'.coeff G) :=
      (hform G ε _).mp (by rwa [add_sub_cancel_right])
    have h1 := hdisc _ _ hcen ha'
    by_cases hc : 0 < B'.coeff G
    · have heq' : a₀ G = a + ε * B'.coeff G := (ha₀ G).eq ha'
      have hGs : G ∈ s := by
        rw [Finset.mem_filter, Finsupp.mem_support_iff]
        exact ⟨hc.ne', hc, heq' ▸ h1⟩
      have h3 : ε < (a₀ G + 1) / B'.coeff G := lt_of_lt_of_le hεc (hc₁b G hGs)
      rw [lt_div_iff₀ hc] at h3
      linarith
    · push Not at hc
      nlinarith
  · exact ⟨1, one_pos, le_rfl, fun ε _ _ hY' => absurd hY' hY⟩

/-- The complement of a nonempty open is not the whole space. -/
private theorem compl_ne_top_of_nonempty {X : Scheme.{u}} {U : X.Opens}
    (hU : (U : Set X).Nonempty) : U.compl ≠ ⊤ := fun h => by
  obtain ⟨x, hx⟩ := hU
  exact (show x ∈ (U.compl : Set X) by simp [h]) hx

/-- **The perturbed pair is dlt for small `ε`.** Let `(X, Δ)` be dlt with the open `U` of its
definition, `Δ₁` and `D` effective with `Δ - Δ₁` effective, `D - Δ₁` `ℚ`-Cartier, `D` having no
component along which `Δ` has coefficient `1`, and `Supp (Δ + D)` snc on `U`. Then
`(X, Δ - εΔ₁ + εD)` is dlt for every small rational `ε > 0`. -/
private theorem exists_forall_isDltPair {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (h : IsDltPair sX n K Δ) {U : X.Opens}
    (hUne : (U : Set X).Nonempty) (hUsm : U ≤ smoothLocus sX)
    (hdisc : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a)
    {Δ₁ D : QDivisor X} (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective)
    (hD : D.IsEffective) (hDlt : ∀ P, D.coeff P ≠ 0 → Δ.coeff P < 1)
    (hsnc : ((Δ + D).restrictOpen U).IsSNC (U.ι ≫ sX)) (hq : (D - Δ₁).IsQCartier) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ → IsDltPair sX n K (Δ - ε • Δ₁ + ε • D) := by
  classical
  have hP := h.1
  have hX : IsNormalVariety k sX := hP.1
  set Δ'' := D - Δ₁ with hΔ''
  have heq : ∀ ε : ℚ, Δ - ε • Δ₁ + ε • D = Δ + ε • Δ'' := fun ε => by
    rw [hΔ'', smul_sub]
    abel
  have hcε : ∀ ε : ℚ, (Δ + ε • Δ'').coeff = fun P => Δ.coeff P + ε * (D.coeff P - Δ₁.coeff P) :=
    fun ε => funext fun P => by
      simp [hΔ'', DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  have hb : ∀ P, 0 ≤ Δ₁.coeff P ∧ Δ₁.coeff P ≤ Δ.coeff P := fun P =>
    ⟨hΔ₁ P, by linarith [DivisorWithCoeffs.coeff_sub Δ Δ₁ P ▸ hΔΔ₁ P]⟩
  let Z : Closeds X := U.compl
  have hZU : (Z.compl : X.Opens) = U := Opens.compl_compl U
  have hZ : Z ≠ ⊤ := compl_ne_top_of_nonempty hUne
  obtain ⟨Y, f, hf, hpure, hsncY⟩ := exists_isLogResolution_isPureCodimOne_preimage sX hX
    (QDivisor.toRDivisor (Δ + D)) Z hZ
  rw [QDivisor.supp_toRDivisor] at hsncY
  obtain ⟨c₂, hc₂, hc₂1, hc₂b⟩ := exists_pos_forall_le D.support
    (fun P => (1 - Δ.coeff P) / D.coeff P) fun P hP => by
      have hP' : D.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
      exact div_pos (sub_pos.mpr (hDlt P hP')) (lt_of_le_of_ne (hD P) (Ne.symm hP'))
  obtain ⟨c₁, hc₁, hc₁1, hc₁b⟩ :=
    exists_pos_forall_neg_one_lt_isDiscrepancy_add_smul hP hq Z.isClosed hdisc hf
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun ε hε hεlt => ?_⟩
  have hεc₁ : ε < c₁ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεc₂ : ε < c₂ := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hε1 : ε < 1 := lt_of_lt_of_le hεc₁ hc₁1
  rw [heq ε]
  have hPε : IsPairWith sX n K (Δ + ε • Δ'') :=
    ⟨hX, hP.2.1, by rw [← add_assoc]; exact hP.2.2.add (MMP.Flips.QDivisor.IsQCartier.qsmul hq ε)⟩
  have hcoeffε : ∀ P, 0 ≤ (Δ + ε • Δ'').coeff P ∧ (Δ + ε • Δ'').coeff P ≤ 1 := fun P => by
    rw [hcε]
    refine add_mul_sub_mem_Icc (hb P).1 (hb P).2 (h.2.1 P).2 (hD P) hε hε1 fun hDP => ?_
    have h5 := lt_of_lt_of_le hεc₂ (hc₂b P (Finsupp.mem_support_iff.mpr hDP.ne'))
    rwa [lt_div_iff₀ hDP] at h5
  refine (isDltPair_iff_exists_isLogResolution hPε hcoeffε).mpr
    ⟨Z, hZ, hZU ▸ hUsm, ?_, Y, f, ?_, hpure, ?_, hc₁b ε hε hεc₁⟩
  · rw [hZU]
    refine (DivisorWithCoeffs.isSNC_iff_of_support_eq (Finset.ext fun W => ?_)).mp hsnc
    simp only [Finsupp.mem_support_iff]
    exact not_congr (coeff_add_smul_sub_eq_zero_iff hΔ₁ hΔΔ₁ hD hε hε1 _).symm
  · have hs : (QDivisor.toRDivisor (Δ + ε • Δ'')).supp = (QDivisor.toRDivisor (Δ + D)).supp := by
      rw [QDivisor.supp_toRDivisor, QDivisor.supp_toRDivisor, supp_add_smul_sub hΔ₁ hΔΔ₁ hD hε hε1]
    exact ⟨hf.toIsSmoothResolution, hf.isPureCodimOne_exceptionalSet, by
      rw [hs]
      exact hf.isSNCSubset⟩
  · rwa [supp_add_smul_sub hΔ₁ hΔΔ₁ hD hε hε1]

/-- If every discrepancy of the dlt pair `(X, Δ)` along a divisor with centre off `U` is `> -1`,
then `Δ` has coefficient `< 1` along every prime divisor not meeting `U`. -/
private theorem coeff_lt_one_of_not_nonempty_inter {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (h : IsDltPair sX n K Δ)
    {U : X.Opens} (hdisc : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a)
    {P : PrimeDivisor X} (hPU : ¬(P.support ∩ U).Nonempty) : Δ.coeff P < 1 := by
  have hX : IsNormalVariety k sX := h.1.1
  have hc : ((DivisorOver.ofPrimeDivisor k hX P).center : Set X) ⊆ (U : Set X)ᶜ := by
    rw [DivisorOver.coe_center]
    refine closure_minimal ?_ U.isOpen.isClosed_compl
    rintro _ ⟨y, hy, rfl⟩ hyU
    exact hPU ⟨y, hy, hyU⟩
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1
    (DivisorOver.ofPrimeDivisor k hX P)
  have h1 := hdisc _ a hc ha
  rw [ha.eq_neg_coeff_of_ofPrimeDivisor hX] at h1
  linarith

end Proof_prop_km2b_dlt_perturbation_dlt

/-! ### The main argument -/

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry TopologicalSpace Proof_prop_km2b_dlt_perturbation_dlt

/-- **Perturbing a dlt pair by an ample divisor** (Kollár–Mori 2.43). Let `(X, Δ)` be a dlt
pair, with canonical divisor `K` of dimension `n`, on a quasi-projective variety over an
algebraically closed field of characteristic zero, let `H` be an ample Cartier divisor, and let
`Δ₁` be an effective `ℚ`-divisor (not necessarily `ℚ`-Cartier) with `Δ - Δ₁` effective. Then
there are integers `m, m' > 0`, an effective `ℚ`-divisor `D` with `mD ∼ mΔ₁ + m'H` (both sides
integral) sharing no component with `⌊Δ⌋`, and a rational `ε₀ > 0` such that
`(X, Δ - εΔ₁ + εD)` is dlt for every rational `0 < ε < ε₀`. -/
@[mmp "prop_km2b_dlt_perturbation_dlt"]
public theorem IsDltPair.exists_forall_isDltPair_sub_smul_add_smul {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsDltPair sX n K Δ) (hqp : IsQuasiProjective sX)
    {H : Divisor X} (hH : H.IsCartier) (hHa : H.IsAmple hH)
    {Δ₁ : QDivisor X} (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective) :
    ∃ m m' : ℕ, 0 < m ∧ 0 < m' ∧ ∃ D : QDivisor X, D.IsEffective ∧
      (∃ E E₁ : Divisor X, Divisor.toQDivisor E = (m : ℚ) • D ∧
        Divisor.toQDivisor E₁ = (m : ℚ) • Δ₁ ∧ E.LinearlyEquivalent (E₁ + m' • H)) ∧
      Disjoint D.support Δ.roundDown.support ∧
      ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ →
        IsDltPair sX n K (Δ - ε • Δ₁ + ε • D) := by
  have hX : IsNormalVariety k sX := h.1.1
  obtain ⟨U, hUne, hUsm, hUsnc, hdisc, -⟩ := MMP.Threefold.Mori.IsDltPair.exists_open_nonempty h
  obtain ⟨m, hm, E₁, hE₁⟩ := exists_toQDivisor_eq_smul Δ₁
  obtain ⟨m', hm', N, t, ht⟩ := exists_sections hX hH hHa E₁ U hUsm
  obtain ⟨τ, hτ, hτΔ, hτsnc⟩ := exists_member hX U hUne hUsm Δ hUsnc (E₁ + m' • H) t ht
  set D' := (E₁ + m' • H).zeroDivisor τ hτ with hD'
  set D : QDivisor X := (m : ℚ)⁻¹ • Divisor.toQDivisor D' with hD
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hD'eff : ∀ P, 0 ≤ D'.coeff P := Divisor.zeroDivisor_nonneg _ τ hτ
  have hDcoeff : ∀ P, D.coeff P = (m : ℚ)⁻¹ * D'.coeff P := fun P => by
    simp [D, smul_eq_mul]
  have hDeff : D.IsEffective := fun P => by
    rw [hDcoeff]
    exact mul_nonneg (by positivity) (by exact_mod_cast hD'eff P)
  have hmD : Divisor.toQDivisor D' = (m : ℚ) • D := by
    rw [hD, smul_smul, mul_inv_cancel₀ hmQ, one_smul]
  set u := (Divisor.isUnit_sectionToRationalFunctions hτ).unit with hu
  have hlin : D'.LinearlyEquivalent (E₁ + m' • H) :=
    ⟨u, by rw [hD', Divisor.zeroDivisor_eq, add_sub_cancel_right]⟩
  have hkey : (m : ℤ) • (D - Δ₁) = Divisor.toQDivisor (principalDivisor u + m' • H) := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_sub, ← hmD, ← hE₁, hD',
      Divisor.zeroDivisor_eq, ← hu]
    simp only [map_add]
    abel
  have hDlt : ∀ P, D.coeff P ≠ 0 → Δ.coeff P < 1 := fun P hP => by
    by_cases hPU : (P.support ∩ U).Nonempty
    · rw [hτΔ P hPU fun h0 => hP (by simp [hDcoeff, h0])]
      exact zero_lt_one
    · exact coeff_lt_one_of_not_nonempty_inter h hdisc hPU
  refine ⟨m, m', hm, hm', D, hDeff, ⟨D', E₁, hmD, hE₁, hlin⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro P hPD hPΔ
    have h2 : Δ.roundDown.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hPΔ
    rw [DivisorWithCoeffs.coeff_roundDown] at h2
    exact h2 (Int.floor_eq_zero_iff.mpr ⟨(h.2.1 P).1, hDlt P (Finsupp.mem_support_iff.mp hPD)⟩)
  · refine exists_forall_isDltPair h hUne hUsm hdisc hΔ₁ hΔΔ₁ hDeff hDlt ?_ ?_
    · refine hτsnc _ fun P _ hP => ?_
      by_contra hc
      push Not at hc
      apply hP
      rw [DivisorWithCoeffs.coeff_add, hc.1, hDcoeff, hc.2]
      simp
    · exact ⟨m, by exact_mod_cast hm.ne', _, hkey.symm,
        (Divisor.isCartier_principalDivisor _).add (hH.nsmul m')⟩

end MMP.Mori

end
