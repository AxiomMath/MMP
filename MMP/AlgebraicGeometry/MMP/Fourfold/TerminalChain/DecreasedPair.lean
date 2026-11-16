module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionTerminal
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyRestrictOpen

/-!
# Decreased pairs and the terminality of a terminal chain

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfolds with stable
low-discrepancy set `I_∞`, and let `(p_i, Θ_i)`, `p_i : Y_i ⟶ X_i`, be a crepant junction of
`(X_i, B_i)` extracting a finite set `I` of valuations, with divisors `E_{i,s}`. Write
`Θ_i' = (p_i)⁻¹_* B_i + ∑_{s ∈ I} (1 - a_{i+1}(s)) E_{i,s}` for the decreased boundary.

* Decreasing the coefficients raises log discrepancies: `a(ξ; Y_i, Θ_i') ≥ a(ξ; Y_i, Θ_i)` for
  every divisorial valuation `ξ` of `k(Y_i)`. Indeed
  `Θ_i - Θ_i' = ∑_s (a_{i+1}(s) - a_i(s)) E_{i,s}` is effective, since log discrepancies do not
  decrease along a step diagram, and `ℚ`-Cartier, since `Y_i` is `ℚ`-factorial.
* If `I = I_∞`, the decreased pair `(Y_i, Θ_i')` is terminal. Indeed `0 < a_{i+1}(s) ≤ 1` since
  `(X_{i+1}, B_{i+1})` is klt and `I_∞ = I_{i+1}`, so `Θ_i'` is effective; `(Y_i, Θ_i)` is
  terminal since `I_∞ = I(X_i, B_i)`; and decreasing the coefficients raises every log
  discrepancy.
* Every model `(M, Θ^M)` of a terminal chain `(p_i, Θ_i)_{i ≥ 0}` (a junction `(Y_i, Θ_i)`, or a
  model `(V_k, Θ_k)` of the `i`-th bridge, among them the decreased pair `(Y_i, Θ_i')`) is a
  terminal pair, and `M` is a `ℚ`-factorial projective complex variety of dimension `4`.
  Terminality passes along each step of a bridge, every contraction of a terminal bridge being
  small: for a step `(X⁻, B⁻) → Z ← (X⁺, B⁺)` and a divisor `F` over `X⁺`, the negativity lemma
  on a common smooth model gives `a(F; X⁻, B⁻) ≤ a(F; X⁺, B⁺)`, and `F` is exceptional over
  `X⁻` when it is exceptional over `X⁺`.
* Let `i₁` be an index such that for every `j ≥ i₁` every irreducible surface `V ⊆ W_j⁻` has
  `mld_{η_V}(X_j, B_j) > 1`. If `s ∈ I_∞` and the centre `c_{X_i}(s)` has codimension two for
  some `i ≥ i₁`, then the label `E_{0,s}` is fixed: its coefficients at the junctions are
  eventually constant. By induction on `j ≥ i`, the centre `V = c_{X_j}(s)` has codimension two
  and `a_j(s) = a_i(s)`: since `mld_{η_V}(X_j, B_j) ≤ a_j(s) ≤ 1`, `V ⊄ W_j⁻`, so the generic
  point of `V` lies over the open of `Z_j` over which `f_j` and `f_j⁺` are isomorphisms, and log
  discrepancies are local at the centre and invariant under isomorphisms of pairs.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.IsDecreasedBoundary.le_of_isValuationLogDiscrepancy`:
  the log discrepancies of the decreased pair dominate those of the junction.
* `MMP.Fourfold.StabilizedSmallKltTail.IsDecreasedBoundary.isKltTerminalPair`: the decreased
  pair `(Y_i, Θ_i')` is terminal.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isKltTerminalPair_modelBoundary`: every
  model of a terminal chain is a terminal `ℚ`-factorial projective fourfold pair.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isFixedLabel_E_of_codimension_eq_two`: an
  extracted label whose centre is eventually a surface is fixed.

## Implementation notes

* Log discrepancies of valuations are the predicate `MMP.Fourfold.IsValuationLogDiscrepancy`, so
  the first inequality is stated for every value `a` of `a(ξ; Y_i, Θ_i)` and every value `a'`
  of `a(ξ; Y_i, Θ_i')`. A valuation having such a value is realized by a divisor over `Y_i`,
  hence is a normalized divisorial valuation.
* `I_∞` is extracted at the junction `Y_0` as the finite set `C.I 0` of valuations of `k(X_0)`,
  equal to `I_∞` by `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.coe_I`; the label
  `E_{0,s}` is `(C.junction 0).E s`.
* The valuation `s` of `k(X_0)` is carried to `k(X_i)` by
  `MMP.Fourfold.StepSequence.Corresponds`, and its centre on `X_i` is
  `MMP.Intersection.IsCentre`; codimension is `codimension`, the coheight in the irreducible
  closed subsets.
* An irreducible surface `V ⊆ W_j⁻` is an irreducible closed subset of `X_j` of topological Krull
  dimension `2` contained in `MMP.Fourfold.StepSequence.badLocusMinusAt`, and `η_V` is its
  generic point.
* The general lemmas on curves, prime divisors, negativity, common models and finite programs
  that these proofs share with the bridge results are in
  `MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas`, in the namespace
  `MMP.Fourfold.Oai4C1`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold.StabilizedSmallKltTail

open MMP.Mori MMP.Fourfold.Oai4C1

/-! ### Decreasing the coefficients raises log discrepancies -/

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips TopologicalSpace

namespace Negativity

open MMP.Fourfold.Oai4C1.Negativity

/-- The birational transform of an effective divisor is effective: it keeps or drops each
coefficient. -/
private theorem isEffective_transformDivisor {X Y : Scheme.{u}} {f : RationalMap X Y}
    {D : QDivisor X} (hD : D.IsEffective) :
    (RationalMap.transformDivisor (X := X) f D).IsEffective := by
  classical
  rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
  refine Finset.sum_induction _ DivisorWithCoeffs.IsEffective
    (fun _ _ => DivisorWithCoeffs.IsEffective.add)
    DivisorWithCoeffs.isEffective_zero fun P _ => ?_
  rw [RationalMap.transformDivisor_single]
  rcases f.transformPrimeDivisor P with _ | E
  · exact DivisorWithCoeffs.isEffective_zero
  · intro E'
    simp only [Option.elim_some]
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    split_ifs
    · exact hD P
    · exact le_rfl

private theorem isEffective_iff_isEffective_transformDivisor :
    ∀ (k : Type u) [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (hB : B.IsQCartier) (hnef : (-B).IsRelativelyNef sZ h),
    B.IsEffective ↔
      (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective := by
  intro k _ Y Z sY sZ _ _ _ hY hZ h hh _ hhb B hB hnef
  refine ⟨isEffective_transformDivisor, fun heff E => ?_⟩
  have := isEffective_of_isRelativelyNef_neg k sY sZ hY hZ h hh hhb (B := B.toRDivisor)
    (by simpa using
      MMP.Fourfold.Oai4C1.Negativity.isRelativelyNef_toRDivisor (k := k) hnef)
    (fun P hP => by
      rw [QDivisor.coeff_toRDivisor]
      exact_mod_cast coeff_nonneg_of_not_isExceptionalPrimeDivisor hY h (hh ▸ hZ) hhb heff P hP) E
  rw [QDivisor.coeff_toRDivisor] at this
  exact_mod_cast this

end Negativity

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips
open scoped WithZero

namespace CommonModel

open MMP.Fourfold.Oai4C1.CommonModel

/-! ### Strict transforms of prime divisors -/

private theorem exists_isSmoothScheme_common_model_of_hasNonemptyCenter :
    ∀ {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sS] [IsNormal S]
    {ι : Type*} [Finite ι] {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, IsProper (f i)] (hfb : ∀ i, IsBirationalMorphism (f i))
    (hX : ∀ i, IsNormalVariety k (f i ≫ sS))
    {κ : Type*} [Finite κ] (v : κ → Valuation S.functionField ℤᵐ⁰)
    (hv : ∀ j, HasNonemptyCenter k sS (v j)),
    ∃ (W : Scheme.{u}) (w : W ⟶ S) (hW : IsNormalVariety k (w ≫ sS))
      (hwb : IsBirationalMorphism w) (g : ∀ i, W ⟶ X i),
      IsSmoothScheme (w ≫ sS) ∧ IsProjectiveMorphism w ∧
      (∀ i, g i ≫ f i = w ∧ IsProjectiveMorphism (g i) ∧ IsBirationalMorphism (g i)) ∧
      (∀ j, ∃ E : MMP.Mori.PrimeDivisor W,
        (⟨W, w, hW, hwb, E⟩ : DivisorOver k sS).valuation = v j) ∧
      (AlgebraicGeometry.IsProjectiveVariety k sS →
        AlgebraicGeometry.IsProjectiveVariety k (w ≫ sS)) := by
  intro k _ _ S sS _ _ ι _ X f _ hfb hX κ _ v hv
  choose D hD using fun j => (hv j).2
  let Y : ι ⊕ κ → Scheme.{u} := fun s => Sum.rec X (fun j => (D j).Y) s
  let F : ∀ s, Y s ⟶ S := fun s => match s with
    | .inl i => f i
    | .inr j => (D j).f
  haveI hFp : ∀ s, IsProper (F s) := fun s => match s with
    | .inl i => inferInstanceAs (IsProper (f i))
    | .inr j => (D j).isProper
  have hFb : ∀ s, IsBirationalMorphism (F s) := fun s => match s with
    | .inl i => hfb i
    | .inr j => (D j).isBirationalMorphism
  have hY : ∀ s, IsNormalVariety k (F s ≫ sS) := fun s => match s with
    | .inl i => hX i
    | .inr j => (D j).isNormalVariety
  obtain ⟨M, m, h, hM, hmp, hmb, hmh⟩ :=
    @exists_common_model k _ S sS ⟨inferInstance, inferInstance⟩ (ι ⊕ κ) _ Y F hFp hFb hY
  haveI := hmp
  haveI : AlgebraicGeometry.IsVariety k (m ≫ sS) := hM.1
  haveI : IsIntegral M := hM.1.toIsIntegral
  obtain ⟨W, p, n, i, hi, hip, hWv, hWs, hpp, hpb⟩ := exists_isImmersion_isSmoothScheme (m ≫ sS)
  haveI := hpp
  haveI := hi
  have hW : IsNormalVariety k ((p ≫ m) ≫ sS) := by
    rw [Category.assoc]
    exact ⟨hWv, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2⟩
  have hwb : IsBirationalMorphism (p ≫ m) := isBirationalMorphism_comp hpb hmb
  have hwp : IsProjectiveMorphism (p ≫ m) :=
    isProjectiveMorphism_of_isImmersion i (p ≫ m) sS (by rw [hip, Category.assoc])
  have hgs : ∀ s, IsProper (p ≫ h s) := fun s =>
    MorphismProperty.comp_mem @IsProper p (h s) hpp (hmh s).2.1
  refine ⟨W, p ≫ m, hW, hwb, fun i => p ≫ h (.inl i), by rwa [Category.assoc], hwp,
    fun i' => ⟨?_, ?_, isBirationalMorphism_comp hpb (hmh (.inl i')).2.2⟩, fun j => ?_, ?_⟩
  · rw [Category.assoc]; exact congrArg (p ≫ ·) (hmh (.inl i')).1
  · haveI := hgs (.inl i')
    haveI : IsSeparated (f i' ≫ sS) := (hX i').1.toIsSeparated
    exact isProjectiveMorphism_of_isImmersion i (p ≫ h (.inl i')) (f i' ≫ sS)
      (by rw [hip, ← (hmh (.inl i')).1]; simp only [Category.assoc]; rfl)
  · haveI := hgs (.inr j)
    rw [← hD j]
    exact exists_primeDivisor_valuation_eq (D j).toDivisorOver _ hW hwb _
      (isBirationalMorphism_comp hpb (hmh (.inr j)).2.2)
      (by rw [Category.assoc, (hmh (.inr j)).1])
  · intro hSp
    exact (AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨hW.1, hwp.comp hSp.isProjective⟩

end CommonModel

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Positivity

namespace Comparison

open MMP.Fourfold.Oai4C1.BridgeComparison

/-! ### Changing the boundary by an effective `ℚ`-Cartier divisor -/

/-- **Lowering the boundary raises log discrepancies.** If `a = a(F, X, Θ)` and `G` is an
effective `ℚ`-Cartier divisor, then `a(F, X, Θ - G) = a + ord_F(g^* G)` with `ord_F(g^* G) ≥ 0`:
with `N G = L` Cartier, the presentation of `K_X + Θ` by Cartier divisors extends to one of
`K_X + Θ - G` by adding `L` with coefficient `-1/N`. -/
private theorem exists_isLogDiscrepancy_sub {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {n : ℕ} {Θ G : QDivisor X} (hG : 0 ≤ G) (hGq : G.IsQCartier) {D : DivisorOver k sX}
    {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Θ) D a) :
    ∃ c : ℝ, 0 ≤ c ∧
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor (Θ - G)) D (a + c) := by
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  obtain ⟨hX, hp, ω, hω0, hK, m, r, C, C', hC, hsum, hpb, rfl⟩ := ha
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  obtain ⟨N, hN, L, hL, hLc⟩ := hGq.exists_pos
  obtain ⟨L', hL'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant (f := D.f) hLc
  have hLG : ∀ Γ : MMP.Mori.PrimeDivisor X, ((L.coeff Γ : ℤ) : ℚ) = N * G Γ := fun Γ => by
    have h1 := congrArg (fun H : QDivisor X => H Γ) hL
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    exact h1
  have hL'0 : 0 ≤ L'.coeff D.E :=
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hLc (V := ⊤)
      (fun P _ => by
        have h := hLG P
        have : (0 : ℚ) ≤ N * G P := mul_nonneg (by positivity) (hG P)
        exact_mod_cast h ▸ this) hL' D.E
      ⟨D.E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support D.E, trivial⟩
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(L'.coeff D.E : ℝ) / N, by positivity, hX, hp, ω, hω0, hK, m + 1,
    Fin.cons (-(N : ℝ)⁻¹) r, Fin.cons L C, Fin.cons L' C', ?_, ?_, ?_, ?_⟩
  · exact Fin.cases hLc hC
  · intro Γ
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hsum Γ]
    have h' : ((L.coeff Γ : ℤ) : ℝ) = (N : ℝ) * ((G Γ : ℚ) : ℝ) := by exact_mod_cast hLG Γ
    have h'' : (N : ℝ)⁻¹ * ((L.coeff Γ : ℤ) : ℝ) = ((G Γ : ℚ) : ℝ) := by
      rw [h']
      field_simp
    simp only [map_sub, Finsupp.sub_apply, QDivisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_apply, Rat.cast_sub] at *
    have hGR : (QDivisor.toRDivisor G) Γ = ((G Γ : ℚ) : ℝ) := rfl
    linear_combination h'' - hGR
  · exact Fin.cases ⟨_, hL'⟩ hpb
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    field_simp
    ring

/-! ### Log discrepancies along a step of the tail -/

/-- **Log discrepancies do not decrease along a step of a stabilized small klt tail.** If `η'`
is the valuation of `k(X_{i+1})` transported from `η`, then `a(η; X_i, B_i) ≤ a(η'; X_{i+1},
B_{i+1})`. On a common smooth model `W` of a divisor realizing `η` and of `X_{i+1}` over `Z_i`,
with `u : W ⟶ X_i`, `r : W ⟶ X_{i+1}` and a compatible canonical divisor `K_W`, the divisor
`u^*(K_i + B_i) - r^*(K_{i+1} + B_{i+1})` has vanishing push-forward to `X_{i+1}` (the step
being small on both sides) and its negative is `r`-nef (`-(K_i + B_i)` is `f_i`-ample), so it
is effective by the negativity lemma; its coefficient along the prime divisor of `η` is
`a(η'; X_{i+1}, B_{i+1}) - a(η; X_i, B_i)`. -/
private theorem le_of_isTransportedValuation {T : StabilizedSmallKltTail} {i : ℕ}
    {η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    {η' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hη : T.IsTransportedValuation i η η') {a a' : ℝ}
    (ha : T.IsLogDiscrepancyAt i η a) (ha' : T.IsLogDiscrepancyAt (i + 1) η' a') : a ≤ a' := by
  have hSi := T.isFourfoldStepDiagram i
  have hZ := hSi.isNormalVariety_target
  have hZp := hSi.isProjectiveVariety_target
  have hXi := hSi.isNormalVariety_minus
  have hX1 := hSi.isNormalVariety_plus
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  have hbf := hfs.isBirationalMorphism
  have hbfp := hfps.isBirationalMorphism
  haveI : IsIntegral (T.Z i) := hZ.1.toIsIntegral
  haveI : IsNormal (T.Z i) := hZ.2
  haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  haveI : IsSeparated (T.sZ i) := hZ.1.toIsSeparated
  haveI : IsSeparated (T.sX i) := hXi.1.toIsSeparated
  haveI : IsSeparated (T.sX (i + 1)) := hX1.1.toIsSeparated
  haveI : LocallyOfFiniteType (T.sX i) := hXi.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (T.sX (i + 1)) := hX1.1.toLocallyOfFiniteType
  haveI : QuasiCompact (T.sX (i + 1)) := hX1.1.toQuasiCompact
  haveI : IsProper (T.f i) := hfs.isProper
  haveI : IsProper (T.fp i) := hfps.isProper
  haveI := hbf.isDominant
  haveI := hbfp.isDominant
  obtain ⟨n, D, hDp, hDv, hDlog⟩ := ha
  obtain ⟨n', D', -, hD'v, hD'log⟩ := ha'
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := hDp
  have hDn : IsNormalVariety ℂ ((D.f ≫ T.f i) ≫ T.sZ i) := by
    rw [Category.assoc, hSi.comp_eq_minus]; exact D.isNormalVariety
  have hDb : IsBirationalMorphism (D.f ≫ T.f i) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
      D.isBirationalMorphism hbf
  -- a smooth projective `W` over `Z_i` with birational morphisms to `D.Y` and to `X_{i+1}`
  let Xs : Option Unit → Scheme.{0} := fun o => o.elim (T.X (i + 1)) fun _ => D.Y
  let fs : ∀ o, Xs o ⟶ T.Z i := fun o => match o with
    | none => T.fp i
    | some _ => D.f ≫ T.f i
  haveI : ∀ o, IsProper (fs o) := fun o => match o with
    | none => (inferInstance : IsProper (T.fp i))
    | some _ => (inferInstance : IsProper (D.f ≫ T.f i))
  haveI : AlgebraicGeometry.IsVariety ℂ (T.sZ i) := hZ.1
  obtain ⟨W, w, hWn, hwb, gW, hWs, -, hgW, -, hWp⟩ :=
    CommonModel.exists_isSmoothScheme_common_model_of_hasNonemptyCenter (k := ℂ) (T.sZ i) fs
      (fun o => match o with
        | none => hbfp
        | some _ => hDb)
      (fun o => match o with
        | none => by
          change IsNormalVariety ℂ (T.fp i ≫ T.sZ i)
          rw [hSi.comp_eq_plus]
          exact hX1
        | some _ => by
          change IsNormalVariety ℂ ((D.f ≫ T.f i) ≫ T.sZ i)
          exact hDn)
      (κ := Empty) (fun j => j.elim) (fun j => j.elim)
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ T.sZ i) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ T.sZ i)
  haveI : QuasiCompact (w ≫ T.sZ i) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ T.sZ i)
  have hWp' : MMP.Mori.IsProjectiveVariety ℂ (w ≫ T.sZ i) := hWp hZp
  haveI : IsProper (w ≫ T.sZ i) := isProper_of_isProjectiveMorphism _ hWp'.isProjective
  haveI := hwb.isDominant
  let q : W ⟶ D.Y := gW (some ())
  let r : W ⟶ T.X (i + 1) := gW none
  have hq : q ≫ D.f ≫ T.f i = w := (hgW (some ())).1
  have hqb : IsBirationalMorphism q := (hgW (some ())).2.2
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ (hgW (some ())).2.1
  have hr : r ≫ T.fp i = w := (hgW none).1
  have hrb : IsBirationalMorphism r := (hgW none).2.2
  haveI : IsProper r := isProper_of_isProjectiveMorphism _ (hgW none).2.1
  haveI := hqb.isDominant
  haveI := hrb.isDominant
  set u : W ⟶ T.X i := q ≫ D.f with hudef
  have hub : IsBirationalMorphism u :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
      hqb D.isBirationalMorphism
  haveI : IsProper u := by rw [hudef]; infer_instance
  haveI := hub.isDominant
  have hcomp : r ≫ T.fp i = u ≫ T.f i := by rw [hr, ← hq, hudef, Category.assoc]
  have hus : u ≫ T.sX i = w ≫ T.sZ i := by
    rw [← hSi.comp_eq_minus, ← Category.assoc, ← hcomp, hr]
  have hrs : r ≫ T.sX (i + 1) = w ≫ T.sZ i := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, hr]
  have hWnu : IsNormalVariety ℂ (u ≫ T.sX i) := by rwa [hus]
  have hWnr : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := by rwa [hrs]
  haveI : LocallyOfFiniteType (u ≫ T.sX i) := hWnu.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (r ≫ T.sX (i + 1)) := hWnr.1.toLocallyOfFiniteType
  haveI : QuasiCompact (r ≫ T.sX (i + 1)) := hWnr.1.toQuasiCompact
  -- canonical divisors: `K_W` with `u_* K_W = K_i`, and `K' = r_* K_W` on `X_{i+1}`
  have hdimW : topologicalKrullDim W = ((4 : ℕ) : WithBot ℕ∞) := by
    haveI : MMP.Mori.IsVariety ℂ (w ≫ T.sZ i) := hWn.1
    haveI : MMP.Mori.IsVariety ℂ (T.sX (i + 1)) := hX1.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (T.sX (i + 1))
      (w ≫ T.sZ i) hrb, hSi.dim_plus]
    rfl
  haveI : MMP.Mori.IsVariety ℂ (w ≫ T.sZ i) := hWn.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (w ≫ T.sZ i) hWs hdimW
  have hTKi := isCanonicalDivisor_K (T := T) i
  have hTK1 := isCanonicalDivisor_K (T := T) (i + 1)
  obtain ⟨KW, hKW, hKWu⟩ := Main.exists_isCanonicalDivisor_transformDivisor_eq hXi hWnu hub
    hTKi (K₀ := K₀) (by rwa [hus])
  have hKWr : KW.IsCanonicalDivisor (r ≫ T.sX (i + 1)) 4 := by rwa [hrs, ← hus]
  have hK'c := Main.isCanonicalDivisor_transformDivisor hX1 hWnr hrb hTK1 hKWr
  set K' : Divisor (T.X (i + 1)) := RationalMap.transformDivisor (X := W) r.toRationalMap KW
    with hK'def
  have hlin : (T.K (i + 1)).LinearlyEquivalent K' :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (T.sX (i + 1)) hX1 hTK1 hK'c
  have hXQ : (Divisor.toQDivisor K' + T.B (i + 1)).IsQCartier :=
    (T.isFourfoldStepDiagram (i + 1)).isQCartier_minus.add_of_linearlyEquivalent hlin
  have hXiQ : (Divisor.toQDivisor (T.K i) + T.B i).IsQCartier := hSi.isQCartier_minus
  -- the pull-backs `A = u^*(K_i + B_i)` and `R = r^*(K' + B_{i+1})`
  have hA₀ : ∀ Z : irreducibleComponents W,
      u (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (T.K i) + T.B i).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K' + T.B (i + 1)).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hA := QDivisor.isPullback_pullback hXiQ hA₀
  have hR := QDivisor.isPullback_pullback hXQ hR₀
  set A := (Divisor.toQDivisor (T.K i) + T.B i).pullback hXiQ hA₀
  set R := (Divisor.toQDivisor K' + T.B (i + 1)).pullback hXQ hR₀
  haveI := isSeparated_toTerminal_of_isNormalVariety hX1
  haveI := isSeparated_toTerminal_of_isNormalVariety hXi
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsSeparated u := IsSeparated.of_comp u (T.sX i)
  haveI : IsSeparated r := IsSeparated.of_comp r (T.sX (i + 1))
  -- `r_*(A - R) = 0`: both steps are small, so the coefficients agree along non-exceptional
  -- prime divisors
  have hpush : RationalMap.transformDivisor (X := W) r.toRationalMap (A - R) = 0 := by
    rw [RationalMap.transformDivisor]
    refine mapPrimeDivisors_eq_zero_of_forall _ fun P P₁ hP₁ => ?_
    have hrP : r P.genericPoint = P₁.genericPoint :=
      (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff r P P₁).mp hP₁
    have hV₁ := map_genericPoint_mem_biregularLocus hfps.two_le_codimension P₁
    have hζ : Order.coheight (T.fp i P₁.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hV₁, P₁.coheight_genericPoint]
    set Q : MMP.Mori.PrimeDivisor (T.Z i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
    have hQ : T.fp i P₁.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
    have hzQ : T.f i (u P.genericPoint) = Q.genericPoint := by
      have := congrArg (fun g : W ⟶ T.Z i => g P.genericPoint) hcomp
      simp only [Scheme.Hom.comp_apply] at this
      rw [← this, hrP, hQ]
    obtain ⟨P₀, hP₀, -⟩ := exists_primeDivisor_of_map_eq_genericPoint hbf hzQ
    have huP : u P.genericPoint = P₀.genericPoint := hP₀.symm
    have hfP₀ : T.f i P₀.genericPoint = Q.genericPoint := by rwa [hP₀]
    haveI := isIso_stalkMap_of_map_eq_genericPoint hub huP
    haveI := isIso_stalkMap_of_map_eq_genericPoint hrb hrP
    rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor P P₀ huP hXiQ hA,
      coeff_eq_of_isPullback_qDivisor P P₁ hrP hXQ hR]
    change ((T.K i P₀ : ℤ) : ℚ) + T.B i P₀ - (((K' P₁ : ℤ) : ℚ) + T.B (i + 1) P₁) = 0
    rw [← hKWu, hK'def, transformDivisor_apply_of_map_genericPoint hub huP KW,
      transformDivisor_apply_of_map_genericPoint hrb hrP KW, T.B_eq i]
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [inverseTransformDivisor_apply_of_map_genericPoint hQ (hQ ▸ hV₁),
      transformDivisor_apply_of_map_genericPoint hbf hfP₀, sub_self]
  -- `-(A - R)` is `r`-nef: `R` is trivial on `r`-contracted curves and `-A` is nonnegative on
  -- them, as `-(K_i + B_i)` is `f_i`-ample
  have hnef' := isRelativelyNef_neg_sub_of_isPullback (sW := r ≫ T.sX (i + 1)) (q := r) (r := u)
    rfl (hus.trans hrs.symm) hcomp (isQCartier_neg hXQ) (isQCartier_neg hXiQ)
    hSi.hasRelativelyAmpleMultiple_minus
    (isPullback_neg hR
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _))
    (isPullback_neg hA
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _))
  have hnef : (-(A - R)).IsRelativelyNef (r ≫ T.sX (i + 1)) r := by
    have e : -(-R - -A) = -(A - R) := by abel
    rwa [e] at hnef'
  -- the negativity lemma: `A - R ≥ 0`
  have heff := (Negativity.isEffective_iff_isEffective_transformDivisor ℂ (T.sX (i + 1))
    (r ≫ T.sX (i + 1)) hX1
    hWnr r rfl hrb
    (by rw [sub_eq_add_neg]; exact (hA.isQCartier hXiQ).add (isQCartier_neg (hR.isQCartier hXQ)))
    hnef).2 ((congrArg (·.IsEffective) hpush).mpr DivisorWithCoeffs.isEffective_zero)
  -- the prime divisor `P` of `W` over `D.E`, which realizes `η` and `η'`
  have hDn' : IsNormalVariety ℂ (D.f ≫ T.sX i) := D.isNormalVariety
  have hWnq : IsNormalVariety ℂ (q ≫ D.f ≫ T.sX i) := by
    rwa [← Category.assoc]
  obtain ⟨P, hqP, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hDn' hWnq hqb D.E
  haveI := hiso
  have hv : D.valuation = (⟨W, u, hWnu, hub, P⟩ : DivisorOver ℂ (T.sX i)).valuation := by
    refine Valuation.ext fun t => ?_
    change D.E.divisorialValuation (functionFieldMap D.f t) =
      P.divisorialValuation (functionFieldMap u t)
    rw [← functionFieldMap_comp_apply q D.f (c := u) rfl]
    exact (congrArg (fun v => v (functionFieldMap D.f t))
      (valuationOver_eq_of_isIso q P D.E hqP)).symm
  have hv' : D'.valuation = (⟨W, r, hWnr, hrb, P⟩ : DivisorOver ℂ (T.sX (i + 1))).valuation := by
    rw [hD'v]
    refine valuation_eq_of_comap_eq hbfp.functionFieldMap_bijective.2 (hη.trans ?_)
    rw [← hDv, hv]
    refine Valuation.ext fun t => ?_
    rw [Valuation.comap_apply, Valuation.comap_apply]
    change P.divisorialValuation (functionFieldMap u (functionFieldMap (T.f i) t)) =
      P.divisorialValuation (functionFieldMap r (functionFieldMap (T.fp i) t))
    rw [functionFieldMap_comp_apply u (T.f i) (c := w) (by rw [← hcomp, hr]),
      functionFieldMap_comp_apply r (T.fp i) (c := w) hr]
  -- reading the coefficients of `A` and `R` along `P`
  have hAP := coeff_isPullback_eq_of_isLogDiscrepancy hXi hTKi hXiQ hub hWnu hKW hKWu hA P
    hDlog hv
  have hRP := coeff_isPullback_eq_of_isLogDiscrepancy hX1 hK'c hXQ hrb hWnr hKWr rfl hR P
    hD'log hv'
  have h0 : 0 ≤ (A - R) P := heff P
  rw [Finsupp.sub_apply] at h0
  have h0' : (0 : ℝ) ≤ ((A P : ℚ) : ℝ) - ((R P : ℚ) : ℝ) := by exact_mod_cast h0
  linarith

end Comparison

end

/-- **Decreasing the coefficients raises log discrepancies.** For a crepant junction
`J = (p_i, Θ_i)` of `(X_i, B_i)` in a stabilized small klt tail and its decreased boundary `Θ'`,
`a(ξ; Y_i, Θ_i) ≤ a(ξ; Y_i, Θ')` for every valuation `ξ` of `k(Y_i)`. -/
@[mmp "lem_oai4_c1_decrease_discrepancy"]
public theorem IsDecreasedBoundary.le_of_isValuationLogDiscrepancy {T : StabilizedSmallKltTail}
    {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : MMP.Mori.QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {ξ : Valuation J.Y.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy J.sY J.Θ ξ a)
    (ha' : IsValuationLogDiscrepancy J.sY Θ' ξ a') : a ≤ a' := by
  classical
  obtain ⟨b, hb, hΘ⟩ := J.Θ_eq
  obtain ⟨b', hb', hΘ'eq⟩ := hΘ'
  set G : QDivisor J.Y := ∑ s : I, Finsupp.single (J.E s) (b' s - b s) with hGdef
  have hbb : ∀ s : I, b s ≤ b' s := fun s => by
    obtain ⟨s', hs', hs'a⟩ := hb' s
    exact_mod_cast Comparison.le_of_isTransportedValuation hs' (hb s) hs'a
  have hG : 0 ≤ G := fun P => by
    rw [hGdef, Finsupp.finset_sum_apply]
    refine Finset.sum_nonneg fun s _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact sub_nonneg.mpr (hbb s)
    · exact le_rfl
  have hΘG : Θ' = J.Θ - G := by
    rw [hΘ'eq, hΘ, hGdef, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finsupp.single_sub]
    congr 1
    ring
  subst hΘG
  obtain ⟨n, D, -, hDv, hDlog⟩ := ha
  obtain ⟨n', D', -, hD'v, hD'log⟩ := ha'
  obtain ⟨c, hc, hlog⟩ := Comparison.exists_isLogDiscrepancy_sub hG
    (isQCartier_of_isQFactorial J.sY J.isQFactorial G) hDlog
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog hD'log
    (hDv.trans hD'v.symm)
  linarith

/-! ### The decreased pair is terminal -/

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace DecreasedPair

/-- The inverse transform of an effective divisor is effective. -/
private theorem inverseTransformDivisor_nonneg {X Y : Scheme.{0}} (g : Y ⟶ X) {D : QDivisor X}
    (hD : 0 ≤ D) : 0 ≤ inverseTransformDivisor g D := by
  classical
  rw [inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply,
    Finsupp.sum]
  refine Finset.sum_nonneg fun P _ => ?_
  cases inverseTransformPrimeDivisor g P with
  | none => exact le_rfl
  | some E => exact Finsupp.single_nonneg.mpr (hD P)

/-- A pair whose log discrepancies each dominate one of a terminal pair on the same variety is
terminal. -/
private theorem isKltTerminalPair_of_forall_exists_le {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {Θ Θ' : QDivisor X}
    (hΘ : IsKltTerminalPair sX Θ) (hΘ' : MMP.Fourfold.IsPair sX Θ')
    (hle : ∀ (n : ℕ) (D : DivisorOver ℂ sX) (a' : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Θ') D a' →
        ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Θ) D a ∧ a ≤ a') :
    IsKltTerminalPair sX Θ' := by
  refine ⟨⟨hΘ', fun n D a' ha' => ?_⟩, fun n D a' hE ha' => ?_⟩ <;>
    obtain ⟨a, ha, hle⟩ := hle n D a' ha'
  exacts [(hΘ.1.2 n D a ha).trans_le hle, (hΘ.2 n D a hE ha).trans_le hle]

/-- For `s ∈ I_∞ = I_{i+1}`, the log discrepancy `a_{i+1}(s)` is at most `1`. -/
private theorem logDiscrepancy_le_one {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i) {s : I}
    {s' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))} {a : ℚ}
    (hs' : T.IsTransportedValuation i s s') (ha : T.IsLogDiscrepancyAt (i + 1) s' a) : a ≤ 1 := by
  obtain ⟨ξ, hξ, hc⟩ : s.1 ∈ T.stableLowDiscrepancySetAt i := hI ▸ s.2
  have hmem : s' ∈ T.lowDiscrepancySetAt (i + 1) := by
    rw [T.isStabilizedSmallKltTail.lowDiscrepancySetAt_eq (i + 1)]
    exact ⟨ξ, hξ, s, hc, hs'⟩
  obtain ⟨-, b, ⟨n', D', -, hv', hl'⟩, hb1⟩ := hmem
  obtain ⟨n, D, -, hv, hl⟩ := ha
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl hl' (hv.trans hv'.symm)
  exact_mod_cast (this ▸ hb1 : ((a : ℚ) : ℝ) ≤ 1)

/-- The decreased boundary `Θ_i'` of a junction extracting `I_∞` is effective. -/
private theorem nonneg_of_isDecreasedBoundary {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i)
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : MMP.Mori.QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') : 0 ≤ Θ' := by
  obtain ⟨a, ha, rfl⟩ := hΘ'
  refine add_nonneg (inverseTransformDivisor_nonneg J.p J.isKltPair.1.nonneg)
    (Finset.sum_nonneg fun s _ => Finsupp.single_nonneg.mpr ?_)
  obtain ⟨s', hs', has'⟩ := ha s
  linarith [logDiscrepancy_le_one hI hs' has']

/-- Every log discrepancy of `(Y_i, Θ_i')` dominates that of `(Y_i, Θ_i)` at the same divisor. -/
private theorem exists_isLogDiscrepancy_le_of_isDecreasedBoundary {T : StabilizedSmallKltTail}
    {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : MMP.Mori.QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') (hΘ : MMP.Mori.IsPair J.sY J.Θ) (n : ℕ)
    (D : DivisorOver ℂ J.sY) (a' : ℝ)
    (ha' : MMP.Intersection.IsLogDiscrepancy J.sY n (QDivisor.toRDivisor Θ') D a') :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy J.sY n (QDivisor.toRDivisor J.Θ) D a ∧
      a ≤ a' := by
  have ⟨_, n₀, K, hK, _⟩ := hΘ
  have hp : IsProper D.f := ha'.2.1
  obtain rfl : n₀ = n := by
    exact_mod_cast hK.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha')
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ hK D
  have ha := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp
  exact ⟨_, ha, hΘ'.le_of_isValuationLogDiscrepancy ⟨n₀, D, hp, rfl, ha⟩
    ⟨n₀, D, hp, rfl, ha'⟩⟩

end DecreasedPair

end

open DecreasedPair in
/-- **The decreased pair is terminal.** For a stabilized small klt tail `T`, a crepant junction
`J = (p_i, Θ_i)` of `(X_i, B_i)` extracting the stable low-discrepancy set `I_∞`, and the
decreased boundary `Θ'` of `J`, the pair `(Y_i, Θ')` is terminal. -/
@[mmp "lem_oai4_c1_decrease_terminal"]
public theorem IsDecreasedBoundary.isKltTerminalPair {T : StabilizedSmallKltTail}
    {i : ℕ} {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i)
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : MMP.Mori.QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') :
    IsKltTerminalPair J.sY Θ' := by
  obtain ⟨hterm, -⟩ := J.isKltTerminalPair_of_coe_eq_lowDiscrepancySet
    (hI.trans (T.isStabilizedSmallKltTail.lowDiscrepancySetAt_eq i).symm)
  obtain ⟨hX, n₀, K, hK, -⟩ := hterm.1.1.isPair
  refine isKltTerminalPair_of_forall_exists_le hterm
    ⟨inferInstance, inferInstance, ⟨hX, n₀, K, hK, isQCartier_of_isQFactorial _ J.isQFactorial _⟩,
      fun P => nonneg_of_isDecreasedBoundary hI hΘ' P⟩
    (exists_isLogDiscrepancy_le_of_isDecreasedBoundary hΘ' hterm.1.1.isPair)

end MMP.Fourfold.StabilizedSmallKltTail

namespace MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

open TopologicalSpace MMP.Mori MMP.Fourfold.Oai4C1

/-! ### All models of a terminal chain are terminal -/

namespace ModelTerminal

open MMP.Fourfold.Oai4C1.Negativity MMP.Fourfold.Oai4C1.CommonModel
  MMP.Fourfold.Oai4C1.StepChain MMP.Fourfold.Oai4C1.ProgramComparison
  MMP.Fourfold.Oai4C1.BridgeComparison MMP.Fourfold.Oai4C1.Main

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips
open scoped WithZero

/-! ### Strict transforms of prime divisors -/

/-- **A smooth common model with projective maps.** Over a field of characteristic zero, two
proper birational morphisms `f₁ : X₁ ⟶ S`, `f₂ : X₂ ⟶ S` from normal varieties are dominated by
a smooth variety `W ⟶ S` through projective birational morphisms `g₁ : W ⟶ X₁`, `g₂ : W ⟶ X₂`,
and `W` is quasi-projective: it is immersed in some `ℙⁿ_k` over `k`. -/
private theorem exists_isSmoothScheme_common_model {k : Type u} [Field k] [CharZero k]
    {S X₁ X₂ : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (f₁ : X₁ ⟶ S) [IsProper f₁]
    (hf₁ : IsBirationalMorphism f₁) (hX₁ : IsNormalVariety k (f₁ ≫ sS)) (f₂ : X₂ ⟶ S)
    [IsProper f₂] (hf₂ : IsBirationalMorphism f₂) (hX₂ : IsNormalVariety k (f₂ ≫ sS)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ S) (g₁ : W ⟶ X₁) (g₂ : W ⟶ X₂),
      IsNormalVariety k (w ≫ sS) ∧ IsSmoothScheme (w ≫ sS) ∧
      (∃ (n : ℕ) (i : W ⟶ projectiveSpaceOver n (Spec (.of k))), IsImmersion i ∧
        i ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = w ≫ sS) ∧
      g₁ ≫ f₁ = w ∧ g₂ ≫ f₂ = w ∧ IsProjectiveMorphism g₁ ∧ IsProjectiveMorphism g₂ ∧
      IsBirationalMorphism g₁ ∧ IsBirationalMorphism g₂ := by
  obtain ⟨Z, h₁, h₂, hZ, hh₁, hh₂, hb₁, hb₂, hc⟩ :=
    exists_common_model_two sS f₁ hf₁ hX₁ f₂ hf₂ hX₂
  haveI : AlgebraicGeometry.IsVariety k (h₁ ≫ f₁ ≫ sS) := hZ.1
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  obtain ⟨W, p, n, i, hi, hip, hWv, hWs, hpp, hpb⟩ :=
    exists_isImmersion_isSmoothScheme (h₁ ≫ f₁ ≫ sS)
  haveI : IsSeparated (f₁ ≫ sS) := hX₁.1.toIsSeparated
  haveI : IsSeparated (f₂ ≫ sS) := hX₂.1.toIsSeparated
  refine ⟨W, p ≫ h₁ ≫ f₁, p ≫ h₁, p ≫ h₂, ?_, by simpa using hWs, ⟨n, i, hi, by simp [hip]⟩,
    Category.assoc _ _ _,
    by rw [Category.assoc, hc],
    isProjectiveMorphism_of_isImmersion i (p ≫ h₁) (f₁ ≫ sS) (by simp [hip]),
    isProjectiveMorphism_of_isImmersion i (p ≫ h₂) (f₂ ≫ sS) (by simp [hip, reassoc_of% hc]),
    isBirationalMorphism_comp hpb hb₁, isBirationalMorphism_comp hpb hb₂⟩
  simp only [Category.assoc]
  exact ⟨hWv, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2⟩

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Positivity
  RingedSpaceModuleAdjunction

/-- **The log discrepancy read on a model.** Let `(X, B)` be a normal variety with canonical
divisor `K` and `K + B` `ℚ`-Cartier, and `r : W ⟶ X` a proper birational morphism from a normal
variety with canonical divisor `K_W`, `r_* K_W = K`, and `R = r^*(K + B)`. Then the divisor
`(W, r, P)` over `X` has log discrepancy `1 + coeff_P (K_W - R)`. -/
private theorem isLogDiscrepancy_of_isPullback {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {d : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX d)
    {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier) {r : W ⟶ X} [IsProper r]
    (hr : IsBirationalMorphism r) (hW : IsNormalVariety ℂ (r ≫ sX))
    [LocallyOfFiniteType (r ≫ sX)] {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (r ≫ sX) d)
    (hKX : RationalMap.transformDivisor (X := W) r.toRationalMap KW = K)
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + B).supp}
    {R : QDivisor W} (hR : (Divisor.toQDivisor K + B).IsPullback r hR₀ R)
    (P : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sX d (QDivisor.toRDivisor B)
      (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) (1 + KW P - R P) := by
  haveI := hr.isDominant
  obtain ⟨ω, hω0, hωK, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hW hr hK hKW hKX
  obtain ⟨m, hm, L, hL, hLc⟩ := hKB.exists_pos
  obtain ⟨L', hL'q, hLp⟩ := hR m hm L hL hLc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨hX, inferInstance, ω, hω0, ⟨K, hK, fun Γ => by rw [← hωK]; rfl⟩, 1,
    fun _ => ((m : ℝ)⁻¹), fun _ => L, fun _ => L', fun _ => hLc, fun Γ => ?_,
    fun _ => ⟨_, hLp⟩, ?_⟩
  · have h1 := congrArg (fun G : QDivisor X => G Γ) hL
    have h2 : Γ.ordForm ω = K Γ := by rw [← hωK]; rfl
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast, Finsupp.add_apply] at h1
    change ((L Γ : ℤ) : ℚ) = m * (((K Γ : ℤ) : ℚ) + B Γ) at h1
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      QDivisor.coeff_toRDivisor, h2]
    change (((K Γ : ℤ) : ℝ)) + ((B Γ : ℚ) : ℝ) = (m : ℝ)⁻¹ * ((L Γ : ℤ) : ℝ)
    have h3 : ((L Γ : ℤ) : ℝ) = (m : ℝ) * (((K Γ : ℤ) : ℝ) + ((B Γ : ℚ) : ℝ)) := by
      exact_mod_cast h1
    rw [h3]
    field_simp
  · have h1 := congrArg (fun G : QDivisor W => G P) hL'q
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    change ((L' P : ℤ) : ℚ) = m * R P at h1
    have h2 : DivisorOver.ordPullback (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) ω = KW P := by
      rw [← hωW]; rfl
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, h2]
    change 1 + ((KW P : ℤ) : ℝ) - ((R P : ℚ) : ℝ) =
      1 + ((KW P : ℤ) : ℝ) - (m : ℝ)⁻¹ * ((L' P : ℤ) : ℝ)
    have h3 : ((L' P : ℤ) : ℝ) = (m : ℝ) * ((R P : ℚ) : ℝ) := by exact_mod_cast h1
    rw [h3]
    field_simp

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

/-! ### Exceptional divisors and the generic point -/

/-- A point outside the exceptional set of `f` has the same coheight as its image. -/
private theorem coheight_map_of_notMem_exceptionalSet {X Y : Scheme.{0}} {f : X ⟶ Y} {x : X}
    (hx : x ∉ (exceptionalSet f : Set X)) : Order.coheight (f x) = Order.coheight x := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let q : (f ⁻¹ᵁ V).toScheme := ⟨x, not_not.mp hx⟩
  have h1 : Order.coheight (((f ∣_ V) ≫ V.ι) q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ ((f ∣_ V) ≫ V.ι).isOpenEmbedding
  have h2 : Order.coheight ((f ⁻¹ᵁ V).ι q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ (f ⁻¹ᵁ V).ι.isOpenEmbedding
  have h3 : ((f ∣_ V) ≫ V.ι) q = f x := by rw [morphismRestrict_ι]; rfl
  rw [← h3, h1, ← h2]
  rfl

/-- If the exceptional set of `f` has codimension at least two, it misses the generic point of
every prime divisor. -/
private theorem genericPoint_notMem_exceptionalSet {X Y : Scheme.{0}} {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∉ (exceptionalSet f : Set X) := fun h => by
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- A divisor over a normal variety is exceptional exactly when the image of the generic point of
its divisor has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := isSeparated_toTerminal_of_isNormalVariety hX
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- The generic point of an irreducible scheme has coheight zero. -/
private theorem coheight_genericPoint (X : Scheme.{0}) [IrreducibleSpace X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.mpr fun y _ => (Scheme.le_iff_specializes).mpr (genericPoint_specializes y)

/-- A point of coheight zero of an irreducible scheme is its generic point. -/
private theorem eq_genericPoint_of_coheight_eq_zero {X : Scheme.{0}} [IrreducibleSpace X] {x : X}
    (h : Order.coheight x = 0) : x = genericPoint X := by
  have h' := Order.coheight_eq_zero.mp h ((Scheme.le_iff_specializes).mpr
    (genericPoint_specializes x))
  exact ((genericPoint_specializes x).antisymm ((Scheme.le_iff_specializes).mp h')).eq.symm

/-- **A small step creates no divisor.** In a step diagram `X⁻ → Z ← X⁺` with `f⁻` small, a
point `x ∈ X⁻` lying under the same point of `Z` as a point `y ∈ X⁺` of codimension at least two
has codimension at least two: were `x` of codimension `≤ 1`, its image would be the generic point
of `Z` or of a prime divisor of `Z`, and so would `y`, `f⁺` being birational. -/
private theorem two_le_coheight_of_map_eq {Xm Xp Z : Scheme.{0}} [IsIntegral Xm]
    [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hS : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hsm : IsSmallMorphism sXm sZ fm)
    {x : Xm} {y : Xp} (h : fp y = fm x) (hy : 2 ≤ Order.coheight y) : 2 ≤ Order.coheight x := by
  have hZ := hS.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated fp := hS.isProper_plus.toIsSeparated
  have hbfp := hS.isBirationalMorphism_plus
  haveI := hS.isBirationalMorphism_minus.isDominant
  haveI := hbfp.isDominant
  by_contra! hlt
  obtain h0 | h1 : Order.coheight x = 0 ∨ Order.coheight x = 1 := by
    lift Order.coheight x to ℕ using ne_top_of_lt hlt with c
    have : c < 2 := by exact_mod_cast hlt
    interval_cases c <;> simp
  · -- `x` is the generic point of `X⁻`, so `y` is the generic point of `X⁺`
    have hy0 : y = genericPoint Xp :=
      eq_of_map_eq_of_valuationRing hbfp.functionFieldMap_bijective
        (by rw [h, eq_genericPoint_of_coheight_eq_zero h0, map_genericPoint_of_isDominant])
        (map_genericPoint_of_isDominant fp)
    rw [hy0, coheight_genericPoint] at hy
    exact absurd hy (by decide)
  · -- `x` is the generic point of a prime divisor, whose image in `Z` is a prime divisor
    set P₀ : MMP.Mori.PrimeDivisor Xm := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
    have hP₀ : P₀.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1
    have hζ : Order.coheight (fm P₀.genericPoint) = 1 := by
      rw [coheight_map_of_notMem_exceptionalSet
        (genericPoint_notMem_exceptionalSet hsm.two_le_codimension P₀), P₀.coheight_genericPoint]
    obtain ⟨P₁, hP₁, -⟩ := exists_primeDivisor_of_map_eq_genericPoint hbfp (x := y)
      (D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ)
      (by
        rw [h, ← hP₀]
        exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm)
    rw [← hP₁, P₁.coheight_genericPoint] at hy
    exact absurd hy (by decide)

/-! ### Log discrepancies across a step -/

/-- **Log discrepancies do not decrease across a step.** For a step diagram
`(X⁻, B⁻) → Z ← (X⁺, B⁺)` and a divisor `F` over `X⁺` with log discrepancy `a'` over
`(X⁺, B⁺)`, there is a divisor over `X⁻` with the same valuation and log discrepancy
`a ≤ a'` over `(X⁻, B⁻)`; it is exceptional over `X⁻` when `F` is exceptional over `X⁺` and
`f⁻` is small. -/
private theorem exists_isLogDiscrepancy_le {Xm Xp Z : Scheme.{0}} [IsIntegral Xm]
    [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hS : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) {n : ℕ} {D' : DivisorOver ℂ sXp} {a' : ℝ}
    (ha' : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) D' a') :
    ∃ (D : DivisorOver ℂ sXm) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sXm 4 (QDivisor.toRDivisor B) D a ∧ a ≤ a' ∧
        (IsSmallMorphism sXm sZ fm → D'.IsExceptional → D.IsExceptional) := by
  have hZ := hS.isNormalVariety_target
  have hXm := hS.isNormalVariety_minus
  have hXp := hS.isNormalVariety_plus
  have hfps := hS.isSmallMorphism_plus
  have hbf := hS.isBirationalMorphism_minus
  have hbfp := hfps.isBirationalMorphism
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsSeparated sXm := hXm.1.toIsSeparated
  haveI : IsSeparated sXp := hXp.1.toIsSeparated
  haveI : LocallyOfFiniteType sXm := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sXp := hXp.1.toLocallyOfFiniteType
  haveI : QuasiCompact sXm := hXm.1.toQuasiCompact
  haveI : QuasiCompact sXp := hXp.1.toQuasiCompact
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_minus
  haveI : IsProper fp := hfps.isProper
  haveI := hbf.isDominant
  haveI := hbfp.isDominant
  haveI := D'.isIntegral
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  haveI := D'.isDominant
  haveI : IsProper D'.f := ha'.2.1
  have hD'n : IsNormalVariety ℂ (D'.f ≫ sXp) := D'.isNormalVariety
  have hDn : IsNormalVariety ℂ ((D'.f ≫ fp) ≫ sZ) := by
    rwa [Category.assoc, hS.comp_eq_plus]
  have hDb : IsBirationalMorphism (D'.f ≫ fp) :=
    isBirationalMorphism_comp D'.isBirationalMorphism hbfp
  -- a smooth `W` over `Z` with birational morphisms to `D'.Y` and to `X⁻`
  obtain ⟨W, w, q, u, hWn, hWs, ⟨N, ι, hι, hιs⟩, hq, hu, hqp, hup, hqb, hub⟩ :=
    exists_isSmoothScheme_common_model sZ (D'.f ≫ fp) hDb hDn fm hbf
      (by rwa [hS.comp_eq_minus])
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : QuasiCompact (w ≫ sZ) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hqp
  haveI : IsProper u := isProper_of_isProjectiveMorphism _ hup
  haveI := hqb.isDominant
  haveI := hub.isDominant
  set r : W ⟶ Xp := q ≫ D'.f with hrdef
  have hrb : IsBirationalMorphism r := isBirationalMorphism_comp hqb D'.isBirationalMorphism
  haveI : IsProper r := by rw [hrdef]; infer_instance
  haveI := hrb.isDominant
  have hcomp : r ≫ fp = u ≫ fm := by rw [hrdef, Category.assoc, hq, hu]
  have hus : u ≫ sXm = w ≫ sZ := by rw [← hS.comp_eq_minus, ← Category.assoc, hu]
  have hrs : r ≫ sXp = w ≫ sZ := by
    rw [← hS.comp_eq_plus, ← Category.assoc, hcomp, Category.assoc, hS.comp_eq_minus, hus]
  have hWnu : IsNormalVariety ℂ (u ≫ sXm) := by rwa [hus]
  have hWnr : IsNormalVariety ℂ (r ≫ sXp) := by rwa [hrs]
  haveI : LocallyOfFiniteType (u ≫ sXm) := hWnu.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (r ≫ sXp) := hWnr.1.toLocallyOfFiniteType
  haveI : QuasiCompact (r ≫ sXp) := hWnr.1.toQuasiCompact
  -- canonical divisors: `K_W` with `u_* K_W = K`, and `K' = r_* K_W` on `X⁺`
  obtain ⟨d, hK⟩ := hS.isCanonicalDivisor
  obtain rfl : d = 4 := by
    have h4 := hK.topologicalKrullDim_eq
    rw [hS.dim_minus] at h4
    exact_mod_cast h4.symm
  have hdimW : topologicalKrullDim W = ((4 : ℕ) : WithBot ℕ∞) := by
    haveI : MMP.Mori.IsVariety ℂ (u ≫ sXm) := hWnu.1
    haveI : MMP.Mori.IsVariety ℂ sXm := hXm.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sXm
      (u ≫ sXm) hub, hS.dim_minus]
    rfl
  haveI : MMP.Mori.IsVariety ℂ (w ≫ sZ) := hWn.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (w ≫ sZ) hWs hdimW
  obtain ⟨KW, hKW, hKWu⟩ := exists_isCanonicalDivisor_transformDivisor_eq hXm hWnu hub
    hK (K₀ := K₀) (by rwa [hus])
  have hKWr : KW.IsCanonicalDivisor (r ≫ sXp) 4 := by rwa [hrs, ← hus]
  obtain ⟨-, -, ⟨K₁, hK₁, -⟩, -⟩ := ha'.2.2
  obtain rfl : n = 4 := by
    have h4 := hK₁.topologicalKrullDim_eq
    rw [hS.dim_plus] at h4
    exact_mod_cast h4.symm
  have hK'c := isCanonicalDivisor_transformDivisor hXp hWnr hrb hK₁ hKWr
  set K' : Divisor Xp := RationalMap.transformDivisor (X := W) r.toRationalMap KW with hK'def
  haveI := isSeparated_toTerminal_of_isNormalVariety hXp
  haveI := isSeparated_toTerminal_of_isNormalVariety hXm
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsSeparated u := IsSeparated.of_comp u sXm
  haveI : IsSeparated r := IsSeparated.of_comp r sXp
  -- prime divisors of `W` over prime divisors of `X⁺` lie over prime divisors of `X⁻`
  have hcorr : ∀ (P : MMP.Mori.PrimeDivisor W) (P₁ : MMP.Mori.PrimeDivisor Xp),
      r P.genericPoint = P₁.genericPoint → ∃ P₀ : MMP.Mori.PrimeDivisor Xm,
        u P.genericPoint = P₀.genericPoint ∧ ∀ {R : Type} [AddCommMonoid R]
          (D : DivisorWithCoeffs R Xm), flipTransform fm fp D P₁ = D P₀ := by
    intro P P₁ hrP
    refine Oai4C1.StepChain.exists_eq_genericPoint_flipTransform_apply hS P₁ (u P.genericPoint) ?_
    rw [← hrP, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]
  have hK'eq : K' = flipTransform fm fp K := by
    refine Finsupp.ext fun P₁ => ?_
    obtain ⟨P, hrP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXp hWnr hrb P₁
    obtain ⟨P₀, huP, hfl⟩ := hcorr P P₁ hrP
    rw [hfl, ← hKWu, hK'def, transformDivisor_apply_of_map_genericPoint hrb hrP KW,
      transformDivisor_apply_of_map_genericPoint hub huP KW]
  have hXQ : (Divisor.toQDivisor K' + flipTransform fm fp B).IsQCartier := by
    rw [hK'eq]; exact hS.isQCartier_plus
  have hXmQ : (Divisor.toQDivisor K + B).IsQCartier := hS.isQCartier_minus
  -- the pull-backs `A = u^*(K + B⁻)` and `R = r^*(K' + B⁺)`
  have hA₀ : ∀ Z : irreducibleComponents W,
      u (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + B).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K' + flipTransform fm fp B).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hA := QDivisor.isPullback_pullback hXmQ hA₀
  have hR := QDivisor.isPullback_pullback hXQ hR₀
  set A := (Divisor.toQDivisor K + B).pullback hXmQ hA₀
  set R := (Divisor.toQDivisor K' + flipTransform fm fp B).pullback hXQ hR₀
  -- `A - R` is `r`-exceptional
  have hexc : ∀ P P₁, RationalMap.transformPrimeDivisor (X := W) r.toRationalMap P = some P₁ →
      (A - R) P = 0 := by
    intro P P₁ hP₁
    have hrP : r P.genericPoint = P₁.genericPoint :=
      (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff r P P₁).mp hP₁
    obtain ⟨P₀, huP, hfl⟩ := hcorr P P₁ hrP
    haveI := isIso_stalkMap_of_map_eq_genericPoint hub huP
    haveI := isIso_stalkMap_of_map_eq_genericPoint hrb hrP
    rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor P P₀ huP hXmQ hA,
      coeff_eq_of_isPullback_qDivisor P P₁ hrP hXQ hR]
    change ((K P₀ : ℤ) : ℚ) + B P₀ - (((K' P₁ : ℤ) : ℚ) + flipTransform fm fp B P₁) = 0
    rw [hK'eq, hfl K, hfl B, sub_self]
  -- `-(A - R)` is `r`-nef, as `-(K + B⁻)` is `f⁻`-ample and `K' + B⁺` is `f⁺`-ample
  have hnef := isRelativelyNef_neg_pullback_sub_pullback hS hK'eq rfl (w ≫ sZ) hus hrs
    hcomp.symm hA hR (hA.isQCartier hXmQ) (hR.isQCartier hXQ)
  -- the negativity lemma: `A - R ≥ 0`
  have h0 : RationalMap.transformDivisor (X := W) r.toRationalMap (A - R).toRDivisor = 0 := by
    rw [RationalMap.transformDivisor]
    refine mapPrimeDivisors_eq_zero_of_forall _ fun P P₁ hP₁ => ?_
    rw [← DivisorWithCoeffs.coeff_apply, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
      hexc P P₁ hP₁, Rat.cast_zero]
  have hnefR : MMP.Flips.IsRelativelyNef ℂ (w ≫ sZ) r (-(A - R).toRDivisor) := by
    simpa using MMP.Fourfold.Oai4C1.Negativity.isRelativelyNef_toRDivisor (k := ℂ) hnef
  have heff := MMP.Flips.isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor ℂ sXp
    (w ≫ sZ) hXp hWn r hrs (isProjectiveMorphism_of_isImmersion ι r sXp (hιs.trans hrs.symm)) hrb
    (by simpa using isCartierCombination_neg (isCartierCombination_of_isRelativelyNef hnefR))
    hnefR (DivisorWithCoeffs.isEffective_iff_nonneg.mpr h0.ge)
  -- the prime divisor `P` of `W` over `D'.E`
  have hWnq : IsNormalVariety ℂ (q ≫ D'.f ≫ sXp) := by
    rwa [← Category.assoc]
  obtain ⟨P, hqP, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hD'n hWnq hqb D'.E
  haveI := hiso
  have hv' : D'.valuation = (⟨W, r, hWnr, hrb, P⟩ : DivisorOver ℂ sXp).valuation := by
    refine Valuation.ext fun t => ?_
    change D'.E.divisorialValuation (functionFieldMap D'.f t) =
      P.divisorialValuation (functionFieldMap r t)
    rw [← functionFieldMap_comp_apply q D'.f (c := r) rfl]
    exact (congrArg (fun v => v (functionFieldMap D'.f t))
      (valuationOver_eq_of_isIso q P D'.E hqP)).symm
  have hRP := coeff_isPullback_eq_of_isLogDiscrepancy hXp hK'c hXQ hrb hWnr hKWr rfl hR P
    ha' hv'
  refine ⟨⟨W, u, hWnu, hub, P⟩, 1 + KW P - A P,
    isLogDiscrepancy_of_isPullback hXm hK hXmQ hub hWnu hKW hKWu hA P, ?_, ?_⟩
  · have h0 := heff P
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply,
      Rat.cast_sub] at h0
    linarith
  · intro hsm hE'
    rw [isExceptional_iff_two_le_coheight hXp] at hE'
    rw [isExceptional_iff_two_le_coheight hXm]
    refine two_le_coheight_of_map_eq hS hsm (y := r P.genericPoint) ?_ ?_
    · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]
    · rwa [hrdef, Scheme.Hom.comp_apply, hqP]

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail

/-- **Terminality is preserved by a small step.** For a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`
with `f⁻` small and `(X⁻, B⁻)` terminal, a pair `(X⁺, B⁺)` is terminal: every log discrepancy over
`(X⁺, B⁺)` dominates one over `(X⁻, B⁻)`, of a divisor which is exceptional over `X⁻` when it is
over `X⁺`. -/
private theorem isKltTerminalPair_flipTransform {Xm Xp Z : Scheme.{0}}
    [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] {sXm : Xm ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hS : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hsm : IsSmallMorphism sXm sZ fm) (hB : IsKltTerminalPair sXm B)
    (hpair : MMP.Fourfold.IsPair sXp (flipTransform fm fp B)) :
    IsKltTerminalPair sXp (flipTransform fm fp B) := by
  refine ⟨⟨hpair, fun n D' a' ha' => ?_⟩, fun n D' a' hE ha' => ?_⟩
  · obtain ⟨D, a, hD, hle, -⟩ := exists_isLogDiscrepancy_le hS ha'
    exact (hB.1.2 4 D a hD).trans_le hle
  · obtain ⟨D, a, hD, hle, hexc⟩ := exists_isLogDiscrepancy_le hS ha'
    exact (hB.2 4 D a (hexc hsm hE) hD).trans_le hle

/-- The source `(V_k, Θ_k)` of the `k`-th step of a finite relative program is a pair. -/
private theorem isPair_boundary {V Z : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} {K : Divisor V} {Θ : QDivisor V}
    (P : RelativeFourfoldProgram sV sZ π K Θ) {k : ℕ} (hk : k < P.m) :
    MMP.Fourfold.IsPair (P.modelStructure k) (P.boundary k) where
  isAlgClosed := inferInstance
  charZero := inferInstance
  isPair := ⟨(P.isFourfoldStepDiagram k hk).isNormalVariety_minus,
    (P.isFourfoldStepDiagram k hk).isCanonicalDivisor.choose, P.canonical k,
    (P.isFourfoldStepDiagram k hk).isCanonicalDivisor.choose_spec,
    (P.isFourfoldStepDiagram k hk).isQCartier_minus⟩
  nonneg := (P.isFourfoldStepDiagram k hk).nonneg

variable {T : StabilizedSmallKltTail}

/-- The models `(V_k, Θ_k)`, `k < m`, of the bridge of a terminal chain are terminal: `(V_0, Θ_0)`
is the decreased pair, and each step is a flip with `g_k` small. -/
private theorem isKltTerminalPair_bridge (C : TerminalChain T) (i : ℕ) :
    ∀ k (hk : k < (C.bridge i).P.m),
      IsKltTerminalPair ((C.bridge i).P.modelStructure k) ((C.bridge i).P.boundary k)
  | 0, _ => (C.bridge i).isDecreasedBoundary.isKltTerminalPair (C.bridge i).coe_source
  | k + 1, hk => by
    have hk' : k < (C.bridge i).P.m := by omega
    rw [(C.bridge i).P.boundary_succ_eq_flipTransform hk']
    refine isKltTerminalPair_flipTransform ((C.bridge i).P.isFourfoldStepDiagram k hk')
      ((C.bridge i).isSmallMorphism k hk') (isKltTerminalPair_bridge C i k hk') ?_
    have h := isPair_boundary (C.bridge i).P hk
    rw [(C.bridge i).P.boundary_succ_eq_flipTransform hk'] at h
    exact h

end

end ModelTerminal

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section

variable {T : StabilizedSmallKltTail}

open ModelTerminal in
/-- **All models of a terminal chain are terminal.** Every model `(M, Θ^M)` of a terminal chain
`C`, namely `M = C.model x` with boundary `C.modelBoundary x`, is a terminal pair
(`MMP.Fourfold.IsKltTerminalPair`), and `M` is a `ℚ`-factorial (`MMP.Fourfold.IsQFactorial`)
projective complex variety of dimension `4`. -/
@[mmp "prop_oai4_terminal_chain_c"]
public theorem isKltTerminalPair_modelBoundary (C : TerminalChain T) (x : C.ModelIndex) :
    IsKltTerminalPair (C.modelStructure x) (C.modelBoundary x) ∧
      IsQFactorial (C.modelStructure x) ∧
      MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x) ∧
      topologicalKrullDim (C.model x) = 4 := by
  rcases x with ⟨i, _ | ⟨k, hk⟩⟩
  · exact ⟨((C.junction i).isKltTerminalPair_of_coe_eq_lowDiscrepancySet
      ((C.coe_I i).trans (T.isStabilizedSmallKltTail.lowDiscrepancySetAt_eq i).symm)).1,
      (C.junction i).isQFactorial, (C.junction i).isProjectiveVariety, (C.junction i).dim_eq⟩
  · exact ⟨isKltTerminalPair_bridge C i k hk, (C.bridge i).P.isQFactorial k hk.le,
      ((C.bridge i).P.isFourfoldStepDiagram k hk).isProjectiveVariety_minus,
      ((C.bridge i).P.isFourfoldStepDiagram k hk).dim_minus⟩

end

/-! ### An extracted label with a surface centre is fixed -/

namespace FixedLabel

open MMP.Fourfold.Oai4C1.CommonModel

open MMP.Mori MMP.Fourfold

/-! ### Pull-backs along composites -/

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X U : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [IsIntegral U]
    (hX : IsNormalVariety ℂ sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

section Iso

variable {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- The divisor `(Y, f ≫ g, E)` over `W`, for a divisor `(Y, f, E)` over `V` and a dominant open
immersion `g : V ⟶ W`. -/
private noncomputable def compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) : DivisorOver ℂ sW where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    have := D.isNormalVariety
    rwa [Category.assoc, hs]
  isBirationalMorphism := by
    haveI := D.isIntegral
    exact isBirationalMorphism_comp D.isBirationalMorphism
      (isBirationalMorphism_of_isOpenImmersion g ⊤ dense_univ)
  E := D.E

/-- The valuation of `(Y, f ≫ g, E)` is that of `(Y, f, E)` carried along `g`. -/
private theorem valuation_compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) :
    (compOpen g hs D).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := (compOpen g hs D).isDominant
  refine Valuation.ext fun t => ?_
  change D.E.valuationOver (D.f ≫ g) t = D.E.valuationOver D.f (functionFieldMap g t)
  rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- **Log discrepancies are invariant under isomorphisms of pairs.** Let `φ : V ≅ W` be an
isomorphism of normal varieties over `ℂ`, `B'` a `ℚ`-divisor on `W` and `B` the divisor on `V`
with `coeff_Γ B = coeff_{φ(Γ)} B'`. If `(Y, f, E)` is a divisor over `V` and `(Y', f', E')` one
over `W` with the corresponding valuation, then `a(E, V, B) = a(E', W, B')`. -/
private theorem eq_of_isLogDiscrepancy_of_iso [CompactSpace V] (φ : V ≅ W)
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : φ.hom ≫ sW = sV) {B : QDivisor V}
    {B' : QDivisor W}
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap φ.hom Γ))
    {n n' : ℕ} {D : DivisorOver ℂ sV} {D' : DivisorOver ℂ sW} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sV n (QDivisor.toRDivisor B) D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sW n' (QDivisor.toRDivisor B') D' a')
    (hv : D'.valuation = D.valuation.comap (functionFieldMap φ.hom)) : a = a' := by
  subst hs
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp : IsProper D.f := ha.2.1
  obtain ⟨hW, -, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, -, hCc, hdec, -, -⟩ := id ha'
  obtain ⟨hV, -, -, -, ⟨K₀, hK₀, -⟩, -⟩ := id ha
  have hnn : n = n' := by
    have h1 := hK₀.topologicalKrullDim_eq
    have h2 := hK'.topologicalKrullDim_eq
    rw [(Scheme.homeoOfIso φ).isHomeomorph.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm.trans h2
  subst hnn
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (φ.hom ≫ sW) := hV.1.toLocallyOfFiniteType
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  have hbφ : IsBirationalMorphism φ.hom := isBirationalMorphism_of_isIso _
  have hbij : Function.Bijective (functionFieldMap φ.hom) := hbφ.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sW)
    hK'.topologicalKrullDim_eq
  -- the pull-backs `L_i = φ^* C_i` and `M_i = f^* L_i`
  choose L hL using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant φ.hom (hCc i)
  have hLc : ∀ i, (L i).IsCartier := fun i => (hL i).isCartier (hCc i)
  choose M hM using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hLc i)
  set Dφ := compOpen φ.hom rfl D
  haveI : IsDominant (D.f ≫ φ.hom) := Dφ.isDominant
  have hpφ : IsProper Dφ.f := by
    change IsProper (D.f ≫ φ.hom)
    infer_instance
  have hord : D.ordPullback (pullbackRationalPluriForms sW φ.hom ω) = Dφ.ordPullback ω := by
    change D.E.ordForm (pullbackRationalPluriForms (φ.hom ≫ sW) D.f
      (pullbackRationalPluriForms sW φ.hom ω)) =
        D.E.ordForm (pullbackRationalPluriForms sW (D.f ≫ φ.hom) ω)
    rw [pullbackRationalPluriForms_comp φ.hom D.f hbij
      (IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism) hd ω]
    rfl
  have h1 : MMP.Intersection.IsLogDiscrepancy sW n (QDivisor.toRDivisor B') Dφ
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) :=
    ⟨hW, hpφ, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, M, hCc, hdec, fun i => ⟨_, isPullback_comp
      (hL i) (hM i) (fun Z =>
      MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ φ.hom) (C i) Z)⟩, rfl⟩
  have e1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha' h1
    (hv.trans (valuation_compOpen φ.hom rfl D).symm)
  -- the same data, pulled back to `V`
  have hne : pullbackRationalPluriForms sW φ.hom ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hW hbφ hK'.topologicalKrullDim_eq hω
  have hcan : (divisorOfForm (pullbackRationalPluriForms sW φ.hom ω)).IsCanonicalDivisor
      (φ.hom ≫ sW) n := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₀ hne
    rw [one_smul] at this
    exact hK₀.of_linearlyEquivalent this
  have hdec2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      ((Γ.ordForm (pullbackRationalPluriForms sW φ.hom ω) : ℤ) : ℝ) +
        (QDivisor.toRDivisor B).coeff Γ = ∑ i, r i * ((L i).coeff Γ : ℝ) := by
    intro Γ
    set Γ' := OpenWeilRestriction.primeDivisorMap φ.hom Γ
    have hΓ : φ.hom Γ.genericPoint = Γ'.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso φ.hom hbij hd Γ Γ' hΓ ω,
      QDivisor.coeff_toRDivisor, hB Γ]
    simp_rw [MMP.Positivity.coeff_eq_of_isPullback Γ Γ' hΓ (hCc _) (hL _)]
    have := hdec Γ'
    rwa [QDivisor.coeff_toRDivisor] at this
  have h2 : MMP.Intersection.IsLogDiscrepancy (φ.hom ≫ sW) n (QDivisor.toRDivisor B) D
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) := by
    refine ⟨hV, hp, _, hne, ⟨_, hcan, fun Γ => coeff_divisorOfForm _ Γ⟩, m, r, L, M, hLc,
      hdec2, fun i => ⟨_, hM i⟩, ?_⟩
    rw [hord]
    rfl
  exact (MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h2).trans e1.symm

end Iso

/-! ### One step of the tail over the common biregular locus -/

/-- An open subscheme `U` lies in the biregular locus of its inclusion. -/
private theorem isIso_ι_restrict_self {X : Scheme.{0}} (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    refine ⟨fun y => ?_⟩
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

/-- The inverse transform along the inclusion of an open subscheme `U` has, at a prime divisor
`Γ` of `U`, the coefficient of the prime divisor of `X` through `Γ`. -/
private theorem inverseTransformDivisor_ι_apply {X : Scheme.{0}} {R : Type*} [AddCommMonoid R]
    (U : X.Opens) (B : DivisorWithCoeffs R X) (Γ : MMP.Mori.PrimeDivisor U.toScheme) :
    inverseTransformDivisor U.ι B Γ = B (OpenWeilRestriction.primeDivisorMap U.ι Γ) :=
  inverseTransformDivisor_apply_of_map_genericPoint
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
    (le_biregularLocus (isIso_ι_restrict_self U)
      (by
        show (OpenWeilRestriction.primeDivisorMap U.ι Γ).genericPoint ∈ U
        rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
        exact (Γ.genericPoint).2)) B

/-- A valuation of `K` is the pull-back of a valuation of `L` along a bijection `K → L`. -/
private theorem exists_comap_eq {K L : Type*} [Field K] [Field L] {e : K →+* L}
    (he : Function.Bijective e) (v : Valuation K (WithZero (Multiplicative ℤ))) :
    ∃ w : Valuation L (WithZero (Multiplicative ℤ)), w.comap e = v := by
  let E := RingEquiv.ofBijective e he
  refine ⟨v.comap E.symm.toRingHom, Valuation.ext fun t => ?_⟩
  change v (E.symm (e t)) = v t
  rw [show e t = E t from rfl, RingEquiv.symm_apply_apply]

section Step

variable (T : StabilizedSmallKltTail) (j : ℕ)

/-- The open `W_j⁻ᶜ = f_j⁻¹(U_j)` of `X_j`, `U_j` the common biregular locus of `f_j`, `f_j⁺`. -/
private abbrev vm : (T.X j).Opens := T.f j ⁻¹ᵁ commonBiregularLocus (T.f j) (T.fp j)

/-- The open `W_j⁺ᶜ = (f_j⁺)⁻¹(U_j)` of `X_{j+1}`. -/
private abbrev vp : (T.X (j + 1)).Opens := T.fp j ⁻¹ᵁ commonBiregularLocus (T.f j) (T.fp j)

/-- The isomorphism `f_j⁻¹(U_j) ≅ U_j`. -/
private noncomputable def isoMinus :
    (vm T j).toScheme ≅ (commonBiregularLocus (T.f j) (T.fp j)).toScheme :=
  @asIso _ _ _ _ (T.f j ∣_ _) (isBiregular_commonBiregularLocus_left _ _)

/-- The isomorphism `(f_j⁺)⁻¹(U_j) ≅ U_j`. -/
private noncomputable def isoPlus :
    (vp T j).toScheme ≅ (commonBiregularLocus (T.f j) (T.fp j)).toScheme :=
  @asIso _ _ _ _ (T.fp j ∣_ _) (isBiregular_commonBiregularLocus_right _ _)

private theorem isoMinus_hom : (isoMinus T j).hom = T.f j ∣_ _ := rfl

private theorem isoPlus_hom : (isoPlus T j).hom = T.fp j ∣_ _ := rfl

/-- The isomorphism `f_j⁻¹(U_j) ≅ U_j ≅ (f_j⁺)⁻¹(U_j)`. -/
private noncomputable def stepIso : (vm T j).toScheme ≅ (vp T j).toScheme :=
  isoMinus T j ≪≫ (isoPlus T j).symm

private theorem stepIso_hom_comp :
    (stepIso T j).hom ≫ (vp T j).ι ≫ T.fp j = (vm T j).ι ≫ T.f j := by
  simp only [stepIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← morphismRestrict_ι, ← isoPlus_hom, Iso.inv_hom_id_assoc, isoMinus_hom,
    morphismRestrict_ι]

private theorem stepIso_hom_comp_sX :
    (stepIso T j).hom ≫ (vp T j).ι ≫ T.sX (j + 1) = (vm T j).ι ≫ T.sX j := by
  rw [← (T.isFourfoldStepDiagram j).comp_eq_plus, ← (T.isFourfoldStepDiagram j).comp_eq_minus]
  simp only [← Category.assoc] at *
  rw [Category.assoc (stepIso T j).hom, stepIso_hom_comp]

private theorem stepIso_hom_apply (x : (vm T j).toScheme) :
    T.fp j ((vp T j).ι ((stepIso T j).hom x)) = T.f j ((vm T j).ι x) := by
  have := congrArg (fun g => g x) (stepIso_hom_comp T j)
  simpa only [Scheme.Hom.comp_apply] using this

/-- `B_j` and `B_{j+1}` agree on `f_j⁻¹(U_j) ≅ (f_j⁺)⁻¹(U_j)`. -/
private theorem coeff_inverseTransformDivisor_stepIso
    (Γ : MMP.Mori.PrimeDivisor (vm T j).toScheme) :
    (inverseTransformDivisor (vm T j).ι (T.B j)).coeff Γ =
      (inverseTransformDivisor (vp T j).ι (T.B (j + 1))).coeff
        (OpenWeilRestriction.primeDivisorMap (stepIso T j).hom Γ) := by
  have hSi := T.isFourfoldStepDiagram j
  have hZ := hSi.isNormalVariety_target
  have hfs : IsSmallMorphism (T.sX j) (T.sZ j) (T.f j) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero j (Nat.zero_le j)
  have hbf := hfs.isBirationalMorphism
  haveI : IsIntegral (T.Z j) := hZ.1.toIsIntegral
  haveI : IsNormal (T.Z j) := hZ.2
  haveI : LocallyOfFiniteType (T.sZ j) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (T.Z j) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ j)
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsSeparated (T.sX j) := hSi.isNormalVariety_minus.1.toIsSeparated
  haveI : IsSeparated (T.f j ≫ T.sZ j) := by rw [hSi.comp_eq_minus]; infer_instance
  haveI : IsSeparated (T.f j) := IsSeparated.of_comp (T.f j) (T.sZ j)
  set φ := stepIso T j
  set Γ' := OpenWeilRestriction.primeDivisorMap φ.hom Γ
  set Γ₁ := OpenWeilRestriction.primeDivisorMap (vm T j).ι Γ
  set Γ₂ := OpenWeilRestriction.primeDivisorMap (vp T j).ι Γ'
  have h₁ : Γ₁.genericPoint = (vm T j).ι Γ.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  have h' : Γ'.genericPoint = φ.hom Γ.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  have h₂ : Γ₂.genericPoint = (vp T j).ι (φ.hom Γ.genericPoint) := by
    rw [← h']; exact OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  have hU : T.fp j Γ₂.genericPoint ∈ commonBiregularLocus (T.f j) (T.fp j) := by
    rw [h₂]; exact (φ.hom Γ.genericPoint).2
  have hζ : Order.coheight (T.fp j Γ₂.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hU.2, Γ₂.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor (T.Z j) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : T.fp j Γ₂.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  have hfQ : T.f j Γ₁.genericPoint = Q.genericPoint := by
    rw [← hQ, h₁, h₂, stepIso_hom_apply]
  change inverseTransformDivisor (vm T j).ι (T.B j) Γ =
    inverseTransformDivisor (vp T j).ι (T.B (j + 1)) Γ'
  rw [inverseTransformDivisor_ι_apply, inverseTransformDivisor_ι_apply, T.B_eq j]
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [inverseTransformDivisor_apply_of_map_genericPoint hQ (hQ ▸ hU.2),
    transformDivisor_apply_of_map_genericPoint hbf hfQ]

/-- **One step over the common biregular locus.** Let `η` be a valuation of `k(X_j)` with centre
`Z` meeting `f_j⁻¹(U_j)`, `η'` the corresponding valuation of `k(X_{j+1})`, and `a = a_j(η)`,
`a' = a_{j+1}(η')`. Then `a' = a`, and the centre of `η'` on `X_{j+1}` has the codimension of
`Z`: both are read off on `f_j⁻¹(U_j) ≅ (f_j⁺)⁻¹(U_j)`. -/
private theorem step {T : StabilizedSmallKltTail} {j : ℕ}
    {η : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    {η' : Valuation (T.X (j + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hη' : T.IsTransportedValuation j η η')
    {Z : IrreducibleCloseds (T.X j)} (hZ : MMP.Intersection.IsCentre ℂ (T.sX j) η Z)
    (hZU : ((Z : Set (T.X j)) ∩ vm T j).Nonempty)
    {a a' : ℝ} (ha : T.IsLogDiscrepancyAt j η a) (ha' : T.IsLogDiscrepancyAt (j + 1) η' a') :
    a = a' ∧ ∃ Z' : IrreducibleCloseds (T.X (j + 1)),
      MMP.Intersection.IsCentre ℂ (T.sX (j + 1)) η' Z' ∧ codimension Z' = codimension Z := by
  obtain ⟨D₀, hp₀, hv₀, rfl⟩ := hZ
  have hSi := T.isFourfoldStepDiagram j
  have hXm := hSi.isNormalVariety_minus
  have hXp := hSi.isNormalVariety_plus
  set φ := stepIso T j
  have hmem : D₀.f D₀.E.genericPoint ∈ vm T j := by
    obtain ⟨x, hx, hxU⟩ := hZU
    rw [SetLike.mem_coe, ← SetLike.mem_coe, D₀.center_eq_closure_genericPoint,
      mem_closure_iff] at hx
    obtain ⟨y, hyU, hy⟩ := hx _ (vm T j).isOpen hxU
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hyU
  set y₀ : (vm T j).toScheme := ⟨_, hmem⟩
  haveI : Nonempty (vm T j) := ⟨y₀⟩
  haveI : Nonempty (vp T j) := ⟨φ.hom y₀⟩
  haveI : IsNoetherian (T.X j) := {}
  haveI : CompactSpace (vm T j) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  haveI : IsDominant (vm T j).ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant (vp T j).ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant φ.hom := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant (φ.hom ≫ (vp T j).ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have hbm := (isBirationalMorphism_of_isOpenImmersion (vm T j).ι ⊤ dense_univ)
  have hbp := (isBirationalMorphism_of_isOpenImmersion (vp T j).ι ⊤ dense_univ)
  have hfs : IsSmallMorphism (T.sX j) (T.sZ j) (T.f j) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero j (Nat.zero_le j)
  have hbfp := hSi.isSmallMorphism_plus.isBirationalMorphism
  obtain ⟨ξm, hξm⟩ := exists_comap_eq hbm.functionFieldMap_bijective η
  obtain ⟨ξp, hξp⟩ := exists_comap_eq hbp.functionFieldMap_bijective η'
  -- `ξp` corresponds to `ξm` under `φ`
  have hcomp : ∀ t, functionFieldMap φ.hom (functionFieldMap (vp T j).ι
      (functionFieldMap (T.fp j) t)) =
        functionFieldMap (vm T j).ι (functionFieldMap (T.f j) t) := by
    intro t
    rw [functionFieldMap_comp_apply (vp T j).ι (T.fp j) rfl,
      functionFieldMap_comp_apply φ.hom ((vp T j).ι ≫ T.fp j) rfl,
      functionFieldMap_comp_apply (vm T j).ι (T.f j) rfl,
      MMP.Positivity.DivisorOver.functionFieldMap_congr (stepIso_hom_comp T j)]
  have hφv : ξp = ξm.comap (functionFieldMap φ.hom) := by
    refine valuation_eq_of_comap_eq hbp.functionFieldMap_bijective.2 ?_
    rw [hξp]
    refine valuation_eq_of_comap_eq hbfp.functionFieldMap_bijective.2 ?_
    rw [hη']
    refine Valuation.ext fun t => ?_
    simp only [Valuation.comap_apply]
    rw [hcomp, ← hξm]
    rfl
  have hφv' : (ξm.comap (functionFieldMap φ.hom)).comap (functionFieldMap (vp T j).ι) =
      ξm.comap (functionFieldMap (φ.hom ≫ (vp T j).ι)) := by
    refine Valuation.ext fun t => ?_
    simp only [Valuation.comap_apply]
    rw [functionFieldMap_comp_apply φ.hom (vp T j).ι rfl]
  -- restriction to `f_j⁻¹(U_j)`
  have hP : MMP.Fourfold.IsPair (T.sX j) (T.B j) := (T.isStabilizedSmallKltTail.isKlt j).1
  have hres := (isValuationLogDiscrepancy_restrict_iff (T.sX j) hP ⟨D₀, hp₀, hv₀⟩
    ⟨D₀, hp₀, hv₀, rfl⟩ (vm T j) (Set.inter_comm _ _ ▸ hZU) hξm a).mpr ha
  obtain ⟨n, Dm, -, hvm, hlm⟩ := hres
  -- the centres
  have hs : (φ.hom ≫ (vp T j).ι) ≫ T.sX (j + 1) = (vm T j).ι ≫ T.sX j := by
    rw [Category.assoc]; exact stepIso_hom_comp_sX T j
  set Dd := compOpen (φ.hom ≫ (vp T j).ι) hs Dm
  have hDd : Dd.valuation = η' := by
    rw [valuation_compOpen, hvm, ← hφv', ← hφv, hξp]
  set Dm₁ := compOpen (vm T j).ι rfl Dm
  have hDm₁ : Dm₁.valuation = D₀.valuation := by
    rw [valuation_compOpen, hvm, hξm, hv₀]
  have hc₀ : Dm₁.f Dm₁.E.genericPoint = D₀.f D₀.E.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXm hDm₁
  obtain ⟨n', Dp, hpp, hvp, hlp⟩ := ha'
  have hcp : Dp.f Dp.E.genericPoint = Dd.f Dd.E.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXp (hvp.trans hDd.symm)
  have hcp' : Dp.f Dp.E.genericPoint = (vp T j).ι (φ.hom (Dm.f Dm.E.genericPoint)) := by
    rw [hcp]; rfl
  have hc₀' : (vm T j).ι (Dm.f Dm.E.genericPoint) = D₀.f D₀.E.genericPoint := hc₀
  refine ⟨?_, Dp.center, ⟨Dp, hpp, hvp.symm, rfl⟩, ?_⟩
  · -- restriction to `(f_j⁺)⁻¹(U_j)` and comparison along `φ`
    have hP' : MMP.Fourfold.IsPair (T.sX (j + 1)) (T.B (j + 1)) :=
      (T.isStabilizedSmallKltTail.isKlt (j + 1)).1
    have hmeet : (((vp T j : (T.X (j + 1)).Opens) : Set (T.X (j + 1))) ∩
        (Dp.center : Set (T.X (j + 1)))).Nonempty := by
      refine ⟨Dp.f Dp.E.genericPoint, ?_, ?_⟩
      · rw [hcp']; exact (φ.hom (Dm.f Dm.E.genericPoint)).2
      · rw [Dp.center_eq_closure_genericPoint]; exact subset_closure rfl
    have hres' := (isValuationLogDiscrepancy_restrict_iff (T.sX (j + 1)) hP' ⟨Dp, hpp, hvp.symm⟩
      ⟨Dp, hpp, hvp.symm, rfl⟩ (vp T j) hmeet hξp a').mpr ⟨n', Dp, hpp, hvp, hlp⟩
    obtain ⟨n'', Dq, -, hvq, hlq⟩ := hres'
    exact eq_of_isLogDiscrepancy_of_iso φ (stepIso_hom_comp_sX T j)
      (coeff_inverseTransformDivisor_stepIso T j) hlm hlq (by rw [hvq, hvm, hφv])
  · rw [MMP.Positivity.DivisorOver.codimension_center,
      MMP.Positivity.DivisorOver.codimension_center,
      hcp', coheight_eq_of_isOpenImmersion, coheight_eq_of_isOpenImmersion, ← hc₀']
    exact (coheight_eq_of_isOpenImmersion (vm T j).ι).symm

end Step

section Tail

variable {T : StabilizedSmallKltTail}

/-- The valuation of `k(X_j)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))} :
    ∀ {j : ℕ} {η₁ η₂ : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))},
      T.Corresponds j ξ η₁ → T.Corresponds j ξ η₂ → η₁ = η₂
  | 0, _, _, h₁, h₂ => h₁.trans h₂.symm
  | j + 1, _, _, ⟨ζ₁, h₁, t₁⟩, ⟨ζ₂, h₂, t₂⟩ => by
    obtain rfl := corresponds_unique h₁ h₂
    have hb := (T.isFourfoldStepDiagram j).isSmallMorphism_plus.isBirationalMorphism
    exact valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (t₁.trans t₂.symm)

/-- The log discrepancy of a valuation over a pair is unique. -/
private theorem isLogDiscrepancyAt_unique {j : ℕ}
    {η : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (ha : T.IsLogDiscrepancyAt j η a) (ha' : T.IsLogDiscrepancyAt j η a') : a = a' := by
  obtain ⟨n, D, -, hv, hl⟩ := ha
  obtain ⟨n', D', -, hv', hl'⟩ := ha'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl hl' (hv.trans hv'.symm)

/-- An irreducible closed subset of codimension two of a fourfold is a surface. -/
private theorem topologicalKrullDim_eq_two {j : ℕ} (Z : IrreducibleCloseds (T.X j))
    (hZ : codimension Z = 2) : topologicalKrullDim (Z : Set (T.X j)) = 2 := by
  have hSi := T.isFourfoldStepDiagram j
  have hX := hSi.isNormalVariety_minus
  haveI : LocallyOfFiniteType (T.sX j) := hX.1.toLocallyOfFiniteType
  let _ : (T.X j).Over (Spec (.of ℂ)) := ⟨T.sX j⟩
  haveI : LocallyOfFiniteType (T.X j ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (T.sX j))
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim ℂ
    (MMP.Intersection.Scheme.Subvariety.ofPoint Z.isIrreducible.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint,
    ← MMP.Flips.codimension_eq_coheight_genericPoint, hZ] at h
  have hcl : closure {Z.isIrreducible.genericPoint} = (Z : Set (T.X j)) := by
    rw [Z.isIrreducible.isGenericPoint_genericPoint_closure.def, Z.isClosed.closure_eq]
  change topologicalKrullDim (closure {Z.isIrreducible.genericPoint} : Set (T.X j)) +
    ((2 : ℕ∞) : WithBot ℕ∞) = topologicalKrullDim (T.X j) at h
  rw [hcl, hSi.dim_minus] at h
  induction hd : topologicalKrullDim (Z : Set (T.X j)) using WithBot.recBotCoe with
  | bot => rw [hd] at h; simp at h
  | coe d =>
    rw [hd, ← WithBot.coe_add] at h
    have h' : d + 2 = 4 := WithBot.coe_injective h
    have : d = 2 := by
      induction d using ENat.recTopCoe with
      | top => simp at h'
      | coe d => norm_cast at h' ⊢; omega
    rw [this]; rfl

/-- The minimal log discrepancy at the generic point of the centre of `η` is at most `a_j(η)`. -/
private theorem minimalLogDiscrepancy_le {j : ℕ}
    {η : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    {Z : IrreducibleCloseds (T.X j)} (hZ : MMP.Intersection.IsCentre ℂ (T.sX j) η Z) {a : ℝ}
    (ha : T.IsLogDiscrepancyAt j η a) :
    minimalLogDiscrepancy (T.sX j) (T.B j) Z.isIrreducible.genericPoint ≤ a := by
  obtain ⟨D₀, -, hv₀, rfl⟩ := hZ
  obtain ⟨n, D, -, hv, hl⟩ := ha
  have hX := (T.isFourfoldStepDiagram j).isNormalVariety_minus
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX
    (hv.trans hv₀)
  refine sInf_le ⟨n, D, a, hl, ?_, rfl⟩
  rw [D.center_eq_closure_genericPoint, hc, ← D₀.center_eq_closure_genericPoint,
    D₀.center.isIrreducible.isGenericPoint_genericPoint_closure.def, D₀.center.isClosed.closure_eq]

/-- A closed set not contained in `W_j⁻` meets `f_j⁻¹(U_j)`. -/
private theorem inter_vm_nonempty {j : ℕ} {Z : Set (T.X j)}
    (h : ¬ Z ⊆ T.badLocusMinusAt j) : (Z ∩ vm T j).Nonempty := by
  rw [Set.not_subset] at h
  obtain ⟨x, hx, hxW⟩ := h
  refine ⟨x, hx, ?_⟩
  rw [StepSequence.badLocusMinusAt, SetLike.mem_coe, ← SetLike.mem_coe, coe_badLocusMinus,
    Set.mem_preimage, coe_badLocusBase, Set.mem_compl_iff, not_not] at hxW
  exact hxW

end Tail

section Junction

variable {T : StabilizedSmallKltTail}

/-- No prime divisor of `X_i` has strict transform the exceptional divisor `E_s` of a junction. -/
private theorem inverseTransformDivisor_apply_E_eq_zero {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction (T.sX i) (T.B i) I) (s : I) :
    inverseTransformDivisor J.p (T.B i) (J.E s) = 0 := by
  refine mapPrimeDivisors_apply_eq_zero (fun Q' hQ' => ?_) _
  obtain ⟨D', -, hsD', h2⟩ := (J.subset_lowDiscrepancySet (Finset.mem_coe.mpr s.2)).1
  let DE : DivisorOver ℂ (T.sX i) :=
    ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, J.E s⟩
  have hv : DE.valuation = D'.valuation := (J.valuation_eq s).trans hsD'
  rw [MMP.Positivity.DivisorOver.codimension_center,
    ← MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq J.isKltPair.1.isPair.1.1 hv]
    at h2
  change 2 ≤ Order.coheight (J.p (J.E s).genericPoint) at h2
  rw [(MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ').1,
    Q'.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The coefficient of `Θ = p⁻¹_* B + ∑ (1 - a_s) E_s` along `E_s` is `1 - a_s`. -/
private theorem coeff_Θ_E {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction (T.sX i) (T.B i) I) {a : I → ℚ}
    (hΘ : J.Θ = inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    (s : I) : J.Θ.coeff (J.E s) = 1 - a s := by
  classical
  rw [hΘ, DivisorWithCoeffs.coeff, Finsupp.add_apply, Finsupp.finset_sum_apply,
    inverseTransformDivisor_apply_E_eq_zero J s, zero_add,
    Finset.sum_eq_single s (fun t _ hts => Finsupp.single_eq_of_ne
      (J.injective.ne hts.symm)) (by simp)]
  simp

end Junction

/-! ### The label is fixed -/

/-- **The centre of a stable valuation stays a surface off the bad loci.** Suppose every
irreducible surface `V ⊆ W_j⁻`, `j ≥ i₁`, has `mld_{η_V}(X_j, B_j) > 1`, and let `ξ ∈ I_∞` have,
on `X_i` with `i ≥ i₁`, a centre of codimension two and log discrepancy `a`. Then for every
`j ≥ i` the valuation corresponding to `ξ` on `X_j` again has a centre of codimension two and
log discrepancy `a`. -/
private theorem exists_centre_codimension_eq_two_of_le {T : StabilizedSmallKltTail} {i₁ : ℕ}
    (hmld : ∀ j ≥ i₁, ∀ V : IrreducibleCloseds (T.X j),
      topologicalKrullDim (V : Set (T.X j)) = 2 → (V : Set (T.X j)) ⊆ T.badLocusMinusAt j →
        1 < minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint)
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    (hξ : ξ ∈ T.stableLowDiscrepancySet) {i : ℕ} (hi : i₁ ≤ i)
    {η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    (hη : T.Corresponds i ξ η) {Z : IrreducibleCloseds (T.X i)}
    (hZ : MMP.Intersection.IsCentre ℂ (T.sX i) η Z) (hcodim : codimension Z = 2) {a : ℝ}
    (ha : T.IsLogDiscrepancyAt i η a) (j : ℕ) (hj : i ≤ j) :
    ∃ η' : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ)),
      T.Corresponds j ξ η' ∧ (∃ Z' : IrreducibleCloseds (T.X j),
        MMP.Intersection.IsCentre ℂ (T.sX j) η' Z' ∧ codimension Z' = 2) ∧
          T.IsLogDiscrepancyAt j η' a := by
  induction j, hj using Nat.le_induction with
  | base => exact ⟨η, hη, ⟨Z, hZ, hcodim⟩, ha⟩
  | succ j hj ih =>
    obtain ⟨η', hη', ⟨Z', hZ', hcod'⟩, ha⟩ := ih
    -- `mld_{η_{Z'}} ≤ a ≤ 1` keeps the surface `Z'` out of `W_j⁻`
    have hnot : ¬ (Z' : Set (T.X j)) ⊆ T.badLocusMinusAt j := fun hsub => by
      obtain ⟨ζ, ⟨-, b, hb, hb1⟩, hζ⟩ := hξ j
      obtain rfl := corresponds_unique hζ hη'
      have h1 := (hmld j (hi.trans hj) Z' (topologicalKrullDim_eq_two Z' hcod') hsub).trans_le
        (minimalLogDiscrepancy_le hZ' hb)
      have : (1 : ℝ) < b := by exact_mod_cast h1
      linarith
    obtain ⟨θ, ⟨-, a', ha', -⟩, hθ⟩ := hξ (j + 1)
    obtain ⟨ζ', hζ', htr⟩ := id hθ
    obtain rfl := corresponds_unique hζ' hη'
    obtain ⟨rfl, Z'', hZ'', hcod''⟩ := step htr hZ' (inter_vm_nonempty hnot) ha ha'
    exact ⟨θ, hθ, ⟨Z'', hZ'', hcod''.trans hcod'⟩, ha'⟩

/-- The valuations extracted at the junction `Y_0` lie in `I_∞`. -/
private theorem coe_mem_stableLowDiscrepancySet {T : StabilizedSmallKltTail}
    (C : TerminalChain T) (s : C.I 0) : s.1 ∈ T.stableLowDiscrepancySet := by
  have h := s.2
  rw [← Finset.mem_coe, C.coe_I 0] at h
  obtain ⟨ξ, hξ, rfl⟩ := h
  exact hξ

/-- At a junction `Y_j` at which the valuation `η` corresponding to `s ∈ I_∞` has log
discrepancy `a`, the label `E_{0,s}` has coefficient `1 - a`. -/
private theorem exists_isJunctionLabelCoefficient {T : StabilizedSmallKltTail}
    (C : TerminalChain T) (s : C.I 0) {j : ℕ}
    {η : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    (hη : T.Corresponds j s.1 η) {a : ℝ} (ha : T.IsLogDiscrepancyAt j η a) :
    ∃ q : ℚ, (q : ℝ) = 1 - a ∧
      C.IsJunctionLabelCoefficient ⟨(C.junction 0).E s, C.isLabel_E s⟩ j q := by
  have hmem : η ∈ (C.I j : Set _) := by
    rw [C.coe_I j]
    exact ⟨s.1, coe_mem_stableLowDiscrepancySet C s, hη⟩
  set t : C.I j := ⟨η, hmem⟩
  obtain ⟨aJ, haJ, hΘ⟩ := (C.junction j).Θ_eq
  have hcentre : C.IsLabelCentre ⟨(C.junction 0).E s, C.isLabel_E s⟩ ⟨j, none⟩
      ((C.junction j).E t) :=
    ⟨η, by rw [labelValuation_E]; exact hη, (C.junction j).valuation_eq t⟩
  have hcoeff := isLabelCoefficient_of_isLabelCentre hcentre
  rw [show (C.modelBoundary ⟨j, none⟩).coeff ((C.junction j).E t) = 1 - aJ t from
    coeff_Θ_E (C.junction j) hΘ t] at hcoeff
  exact ⟨1 - aJ t, by push_cast; rw [isLogDiscrepancyAt_unique (haJ t) ha], hcoeff⟩

end FixedLabel

section

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

open FixedLabel in
/-- An extracted label `E_{0,s}`, `s ∈ I_∞`, of a terminal chain is fixed if, for some `i ≥ i₁`,
the centre on `X_i` of (the valuation of `k(X_i)` corresponding to) `s` has codimension two,
where `i₁` is such that every irreducible surface `V ⊆ W_j⁻`, `j ≥ i₁`, has
`mld_{η_V}(X_j, B_j) > 1`. -/
@[mmp "lem_oai4_c1_extracted_label_codim_two_fixed"]
public theorem isFixedLabel_E_of_codimension_eq_two {i₁ : ℕ}
    (hmld : ∀ j ≥ i₁, ∀ V : IrreducibleCloseds (T.X j),
      topologicalKrullDim (V : Set (T.X j)) = 2 → (V : Set (T.X j)) ⊆ T.badLocusMinusAt j →
        1 < minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint)
    (s : C.I 0) {i : ℕ} (hi : i₁ ≤ i)
    {η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    (hη : T.Corresponds i s.1 η) {Z : IrreducibleCloseds (T.X i)}
    (hZ : MMP.Intersection.IsCentre ℂ (T.sX i) η Z) (hcodim : codimension Z = 2) :
    C.IsFixedLabel ⟨(C.junction 0).E s, C.isLabel_E s⟩ := by
  have hs := coe_mem_stableLowDiscrepancySet C s
  obtain ⟨η₀, ⟨-, a, ha, -⟩, hη₀⟩ := hs i
  obtain rfl := corresponds_unique hη₀ hη
  -- the coefficient `1 - a_j(s)` of `E_{0,s}` at the junctions is constant for `j ≥ i`
  obtain ⟨q, hq, -⟩ := exists_isJunctionLabelCoefficient C s hη₀ ha
  refine ⟨q, i, fun j hj => ?_⟩
  obtain ⟨η', hη', -, ha'⟩ :=
    exists_centre_codimension_eq_two_of_le hmld hs hi hη₀ hZ hcodim ha j hj
  obtain ⟨q', hq', hcoeff⟩ := exists_isJunctionLabelCoefficient C s hη' ha'
  rwa [show q' = q by exact_mod_cast hq'.trans hq.symm] at hcoeff

end

end

end MMP.Fourfold.StabilizedSmallKltTail.TerminalChain
