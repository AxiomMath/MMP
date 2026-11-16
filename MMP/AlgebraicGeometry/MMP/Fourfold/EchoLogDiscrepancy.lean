module

public import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation

/-!
# Log discrepancies of echoes and of generic blowup valuations

Let `(Y, Θ)` be a pair on a normal threefold `Y` with labels `S_1, …, S_m`, with
`Θ = ∑_h b_h S_h` and `0 ≤ b_h < 1`. An echo `ξ` of order `j` of a label `S_h` at a curve
`V ⊆ S_h` is the weighted monomial valuation `v_{x,t;j}` for a local equation `x` of `S_h` at
`η_V` and any completion `t` of `x` to a regular system of parameters
(`MMP.Fourfold.isEcho_tfae_isMonomialValuationOfWeight_isWeightedMonomialValuation`). Since
`ξ(x) = j` and no other label passes through `η_V`, its log discrepancy is
`a(ξ; Y, Θ) = 1 + j (1 - b_h)`.

Let `(X, B)` be a pair on a normal complex threefold, `B = ∑ₕ bₕ Bₕ` with prime divisors `Bₕ`,
and let `V ⊆ X` be an irreducible closed curve such that `X` is smooth at its generic point
`η_V`. Let `mₕ = mult_{η_V} Bₕ` (zero when `V ⊄ Bₕ`). The generic blowup valuation `v_V`, the
`𝔪_V`-adic order of `𝒪_{X,η_V}`, is the monomial valuation `v_{x,t;1}` for a regular system of
parameters `(x, t)` of `𝒪_{X,η_V}`. It is therefore a normalized divisorial valuation of `ℂ(X)`
with centre `V`, exceptional over `X` since `V` has codimension two, and its log discrepancy is
`a(v_V; X, B) = 2 - ∑ₕ mₕ bₕ`, because `v_V` of a local equation of `Bₕ` is `mₕ`.

## Main results

* `MMP.Fourfold.IsEcho.hasLogDiscrepancy`: `a(ξ; Y, Θ) = 1 + j (1 - b_h)` for an echo `ξ` of
  order `j` of `S_h`.
* `MMP.Fourfold.IsGenericBlowupValuation.hasLogDiscrepancy`: `v_V` is a normalized,
  exceptional divisorial valuation with centre `V`, and `a(v_V; X, B) = 2 - ∑ₕ mₕ bₕ`.

## Implementation notes

* "`Θ = ∑_h b_h S_h`" is the condition that every component of `Θ` is a label; the
  coefficient `b_h` is `Θ.coeff S_h`, read in `ℝ`.
* The generic blowup valuation is the predicate `MMP.Fourfold.IsGenericBlowupValuation`, which
  carries the standing hypotheses (normal complex threefold, `V` a curve, `𝒪_{X,η_V}` regular).
* The sum `∑ₕ mₕ bₕ` is `MMP.Mori.DivisorWithCoeffs.multiplicityAt B η_V`, the multiplicity of
  the `ℚ`-divisor `B` at `η_V`.
* Values of log discrepancies are expressed through `MMP.Fourfold.HasLogDiscrepancy`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open scoped WithZero

namespace MMP.Fourfold

section Echo

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The first member of a regular system of parameters `(x, t)` of a Noetherian local ring is
not in `𝔪²`. -/
private theorem notMem_maximalIdeal_sq {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {x t : A} (h : MMP.Mori.IsRegularSystemOfParameters ![x, t]) :
    x ∉ maximalIdeal A ^ 2 := by
  intro hx
  obtain ⟨hspan, hdim⟩ := h
  rw [show Set.range ![x, t] = {x, t} by ext; simp [Fin.exists_fin_two, eq_comm, or_comm]]
    at hspan
  have ht : t ∈ maximalIdeal A := hspan ▸ Ideal.subset_span (by simp)
  -- By Nakayama, `𝔪 = (t) + 𝔪²` forces `𝔪 = (t)`, so `dim A = ht 𝔪 ≤ 1` by Krull.
  have hle : maximalIdeal A ≤ Ideal.span {t} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) <| by
        conv_lhs => rw [← hspan]
        rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, smul_eq_mul,
          ← pow_two]
        exact ⟨Ideal.mem_sup_right hx, Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)⟩
  have h1 : (maximalIdeal A).height ≤ 1 :=
    le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr ht) ▸
      Ideal.height_span_singleton_le_one ((mem_maximalIdeal t).mp ht)
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [hdim] at h2
  have : ((maximalIdeal A).height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  rw [h2] at this
  exact absurd this (by decide)

/-- If `x ∈ 𝔪 ∖ 𝔪²` and `j ≥ 1`, then `j` is the largest `n` with
`x ∈ ∑_a x^a 𝔪^{max(n - ja, 0)}`. -/
private theorem isGreatest_echoIdeal {A : Type*} [CommRing A] {x : A} {𝔪 : Ideal A}
    (hx𝔪 : x ∈ 𝔪) (hx : x ∉ 𝔪 ^ 2) {j : ℕ} (hj : 1 ≤ j) :
    IsGreatest {n : ℕ | x ∈ echoIdeal x 𝔪 j n} j := by
  refine ⟨?_, fun n hn => ?_⟩
  · refine Ideal.mem_iSup_of_mem 1 ?_
    simpa using Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (Submodule.mem_top (x := 1))
  · by_contra! hlt
    have hle : echoIdeal x 𝔪 j (j + 1) ≤ 𝔪 ^ 2 := iSup_le fun a => by
      rcases a with _ | _ | a
      · simpa using Ideal.pow_le_pow_right (by omega)
      · rw [show j + 1 - j * (0 + 1) = 1 by omega, pow_one, pow_one, pow_two]
        exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hx𝔪)
      · refine Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
        rw [show a + 1 + 1 = 2 + a by omega, pow_add]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx𝔪 2)
    exact hx (hle (echoIdeal_antitone x 𝔪 j hlt hn))

/-- **Log discrepancy of an echo.** Let `(Y, Θ)` be a pair on a normal threefold with labels `L`,
`Θ` supported on `L` with coefficients `< 1`. If `ξ` is an echo of order `j` of the label `S`
at a curve `V`, then `a(ξ; Y, Θ) = 1 + j (1 - Θ(S))`. -/
@[mmp "lem_mmp_indexd_echo_log_discrepancy"]
public theorem IsEcho.hasLogDiscrepancy {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {L : Finset (MMP.Mori.PrimeDivisor Y)} {S : MMP.Mori.PrimeDivisor Y} {V : IrreducibleCloseds Y}
    {j : ℕ} {ξ : Valuation Y.functionField ℤᵐ⁰} {Θ : MMP.Mori.QDivisor Y}
    (hξ : IsEcho sY L S V j ξ) (hΘ : IsPair sY Θ) (hsupp : Θ.support ⊆ L)
    (hlt : ∀ S' ∈ L, Θ.coeff S' < 1) :
    HasLogDiscrepancy sY Θ ξ (1 + j * (1 - (Θ.coeff S : ℝ))) := by
  classical
  obtain ⟨hY, hdim, hS, hVS, hV, hη, hj, hC, x, hx, hecho⟩ := id hξ
  haveI := hΘ.isAlgClosed
  obtain ⟨⟨t, ht, U, hηU, hU1, hU2, xU, tU, hxU, htU, SU, LU, Z, h1, h2, h3, h4, h5, h6, h7⟩,
    hall⟩ := isEcho_tfae_isMonomialValuationOfWeight_isWeightedMonomialValuation sY L S V j
      hY hdim hS hVS hV hη hj x hx
  obtain ⟨D, hD, hv, -⟩ := hC
  have hmono : IsWeightedMonomialValuation sY V x t j ξ :=
    ((hall t ht U hηU hU1 hU2 xU tU hxU htU SU LU Z h1 h2 h3 h4 h5 h6 h7 ξ ⟨D, hD, hv⟩).out
      1 3).mp hξ
  have hηS : V.isIrreducible.genericPoint ∈ S.support :=
    hVS (V.isClosed.closure_subset V.isIrreducible.isGenericPoint_genericPoint_closure.mem)
  have hd := hmono.hasLogDiscrepancy hΘ (fun S' => if S' = S then x else 1) (fun S' hS' => by
    split_ifs with h
    · subst h; exact hx
    · rw [Ideal.span_singleton_one]
      refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).mpr fun hη' => h ?_
      exact eq_of_mem_oneLabelSmoothLocus hη (hsupp hS') hS hη' hηS)
  convert hd using 1
  have hx2 := notMem_maximalIdeal_sq ht
  obtain ⟨M, hM, hξM⟩ := hecho x fun h => hx2 (h ▸ zero_mem _)
  obtain rfl : M = j :=
    hM.unique (isGreatest_echoIdeal (ht.1 ▸ Ideal.subset_span ⟨0, rfl⟩) hx2 hj)
  rw [Finset.sum_eq_single S]
  · rw [if_pos rfl, hξM, WithZero.log_exp]
    push_cast
    ring
  · simp +contextual
  · intro h
    rw [Finsupp.notMem_support_iff] at h
    simp [MMP.Mori.DivisorWithCoeffs.coeff_apply, h]

end Echo

section GenericBlowup

/-- In `WithBot ℕ∞`, `1 + c = 3` forces `c = 2`. -/
private theorem eq_two_of_one_add_eq_three {c : ℕ∞}
    (h : (1 : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : c = 2 := by
  have h' : (1 + c : ℕ∞) = 3 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n =>
    have : 1 + n = 3 := by exact_mod_cast h'
    norm_cast
    omega

/-- The generic point of a curve on a threefold has coheight two. -/
private theorem coheight_genericPoint_eq_two {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] {V : IrreducibleCloseds X} {v : Valuation X.functionField ℤᵐ⁰}
    (hv : IsGenericBlowupValuation sX V v) : Order.coheight V.isIrreducible.genericPoint = 2 := by
  have : LocallyOfFiniteType sX := hv.1.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    V.isIrreducible.genericPoint
  rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hv.2.2.1, hv.2.1] at h
  exact eq_two_of_one_add_eq_three h

/-- At a point with regular local ring, every prime divisor has a local equation: its stalk
ideal is principal, generated by a nonzero element. -/
private theorem exists_stalk_idealSheaf_eq_span {X : Scheme.{0}} [IsIntegral X] {η : X}
    [IsRegularLocalRing (X.presheaf.stalk η)] (S : MMP.Mori.PrimeDivisor X) :
    ∃ g : X.presheaf.stalk η, g ≠ 0 ∧ IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} := by
  have : IsDomain (X.presheaf.stalk η) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (X.presheaf.stalk η) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  by_cases hS : η ∈ S.support
  · obtain ⟨q, -, hq, hh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    refine ⟨g, ?_, hq.trans hg⟩
    rintro rfl
    exact q.asIdeal.ne_bot_of_height_eq_one hh (by rw [hg, Ideal.span_singleton_eq_bot])
  · exact ⟨1, one_ne_zero, (MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hS).trans
      Ideal.span_singleton_one.symm⟩

/-- The weight-one monomial valuation of a local equation of a prime divisor `S` at `η_V` is the
multiplicity of `S` at `η_V`. -/
private theorem neg_log_eq_multiplicityAt {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] {V : IrreducibleCloseds X} {x t : X.presheaf.stalk V.isIrreducible.genericPoint}
    {v : Valuation X.functionField ℤᵐ⁰} (hw : IsWeightedMonomialValuation sX V x t 1 v)
    (S : MMP.Mori.PrimeDivisor X) {g : X.presheaf.stalk V.isIrreducible.genericPoint}
    (hg0 : g ≠ 0) (hg : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint =
      Ideal.span {g}) :
    -WithZero.log (v (algebraMap _ X.functionField g)) =
      ((S.multiplicityAt V.isIrreducible.genericPoint).toNat : ℤ) := by
  obtain ⟨M, hM, hvM⟩ := hw.2.2.2.2.2 g hg0
  have hmult : S.multiplicityAt V.isIrreducible.genericPoint = M := by
    rw [MMP.Mori.PrimeDivisor.multiplicityAt_eq_localMultiplicity S (g := g)
      (by rwa [Scheme.IdealSheafData.stalkIdeal_eq_stalk]), ← hM,
      monomialValuation_one_eq_iSup hw.2.2.2.1]
    rfl
  simp [hvM, hmult]

/-- **Log discrepancy of the generic blowup valuation.** Let `(X, B)` be a pair on a normal
complex threefold and `v = v_V` the generic blowup valuation of an irreducible curve `V` at whose
generic point `X` is smooth. Then `v` is a normalized divisorial valuation of `ℂ(X)` with centre
`V`, exceptional over `X`, and `a(v; X, B) = 2 - mult_{η_V} B = 2 - ∑ₕ bₕ mult_{η_V} Bₕ`. -/
@[mmp "lem_mmp_indexd_generic_blowup_discrepancy"]
public theorem IsGenericBlowupValuation.hasLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {V : IrreducibleCloseds X} {v : Valuation X.functionField ℤᵐ⁰}
    (hv : IsGenericBlowupValuation sX V v) (hB : IsPair sX B) :
    MMP.Intersection.IsNormalizedDivisorialValuation ℂ sX v ∧
      MMP.Intersection.IsCentre ℂ sX v V ∧
      MMP.Intersection.IsExceptionalValuation ℂ sX v ∧
      HasLogDiscrepancy sX B v
        (2 - ((MMP.Mori.DivisorWithCoeffs.multiplicityAt B V.isIrreducible.genericPoint : ℚ) :
          ℝ)) := by
  have : IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint) := hv.2.2.2.1
  have hcoh := coheight_genericPoint_eq_two hv
  have hcodim : codimension V = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
  obtain ⟨n, z, hz⟩ :=
    MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk V.isIrreducible.genericPoint)
  obtain rfl : n = 2 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hcoh] at h
    exact_mod_cast h.symm
  have hz' : MMP.Mori.IsRegularSystemOfParameters ![z 0, z 1] := by
    convert hz using 1
    ext i
    fin_cases i <;> rfl
  have hw : IsWeightedMonomialValuation sX V (z 0) (z 1) 1 v :=
    (isGenericBlowupValuation_iff_isWeightedMonomialValuation hv.2.1 hv.2.2.1 hcodim hz').mp hv
  obtain ⟨hdiv, hcen⟩ := hw.isNormalizedDivisorialValuation_and_isCentre
  choose f hf0 hf using exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint)
  refine ⟨hdiv, hcen, ?_, ?_⟩
  · obtain ⟨D, hD, hvD, hVD⟩ := hcen
    exact ⟨D, hD, hvD, by rw [← hVD, hcodim]⟩
  convert hw.hasLogDiscrepancy hB f (fun S _ => hf S) using 1
  rw [MMP.Mori.DivisorWithCoeffs.multiplicityAt, Finsupp.sum]
  push_cast
  congr 1
  · norm_num
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Int.cast_neg, neg_log_eq_multiplicityAt hw S (hf0 S) (hf S), nsmul_eq_mul, mul_comm]
  push_cast
  rfl

end GenericBlowup

end MMP.Fourfold
