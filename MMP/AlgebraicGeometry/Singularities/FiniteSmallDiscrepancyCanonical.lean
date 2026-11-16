module

public import MMP.AlgebraicGeometry.MMP.Fourfold.CanonicalDifficulty
import MMP.AlgebraicGeometry.Singularities.LogResolution.KltPairCondition
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

/-!
# Finitely many small log discrepancies of a real canonical pair

Let `(X, B)` be a real canonical pair with no coefficient one, `B = ∑ⱼ bⱼ Bⱼ`, over an
algebraically closed field of characteristic zero, and let `d = max ({0} ∪ {bⱼ})`. Then only
finitely many exceptional divisorial valuations `E` with center on `X` have log discrepancy
`a(E, X, B) < 2 - d`; that is, the set `𝓔_{2 - d}(X, B)` is finite.

The pair is klt. Take a log resolution `f : Y ⟶ X` whose exceptional set is the union of the
`f`-exceptional prime divisors and whose configuration `H₁, …, H_s` (the `f`-exceptional prime
divisors and the strict transforms of the components of `B`) satisfies `a(H_k) + a(H_l) ≥ 2`
whenever `H_k ≠ H_l` meet. Write the crepant boundary as `Λ = ∑ (1 - a(H_k)) H_k`. A valuation
`E` outside the finite set of valuations of the `f`-exceptional prime divisors, with
`a(E, X, B) < 2 - d ≤ 2`, has a center of codimension at least two on `Y`, so the snc estimate
places it in exactly one `H_k`, with `1 - a(H_k) > 0` and `a(E, X, B) ≥ 1 + a(H_k)`. Canonicity
rules out an exceptional `H_k`, so `H_k` is the strict transform of a component `Bⱼ` and
`a(E, X, B) ≥ 2 - bⱼ ≥ 2 - d`, a contradiction.

## Main results

* `MMP.Fourfold.IsRealCanonicalPair.finite_logDiscrepancyLtSet_two_sub_realThresholdMax`:
  `𝓔_{2 - d}(X, B)` is finite.

## Implementation notes

The source works over `ℂ`; the statement is made over an algebraically closed field of
characteristic zero, where log resolutions exist. The set `𝓔_u(X, B)` is
`MMP.Fourfold.logDiscrepancyLtSet`, a set of valuations of `k(X)`, so finiteness counts
valuations rather than models of them, and `d` is `MMP.Fourfold.realThresholdMax`.

The resolution with the pair condition is
`MMP.Flips.IsKawamataLogTerminal.exists_isLogResolution_two_le_logDiscrepancy_add`. The
computation runs with the discrepancy `MMP.Flips.IsDiscrepancy` of a fixed canonical divisor; the
log discrepancy `MMP.Intersection.IsLogDiscrepancy` of the statement is translated to it through
`MMP.Flips.IsDiscrepancyWith.eq`, which compares values computed with different rational top
forms and presentations. The snc estimate on `Y` is
`MMP.Flips.codimension_center_eq_two_of_logDiscrepancy_lt_two`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Flips
open MMP.Mori hiding IsLogResolution exceptionalSet
open scoped WithZero

universe u

namespace MMP.Fourfold

/-! ### Exceptional divisors and the codimension of their centers -/

/-- If `d + c = n`, then `d + 2 ≤ n` exactly when `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, ← h, ← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe,
      add_comm d, add_comm d]
    exact ENat.add_le_add_iff_right fun hd => by simp [hd] at h

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- A divisor over `X` is exceptional exactly when its center has codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : ProperDivisorOver k sX) :
    E.IsExceptional ↔ 2 ≤ Order.coheight (E.f E.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [E.center_eq_toDivisorOver_center, E.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (E.f E.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-! ### Divisors over a proper birational model -/

/-- The valuation of a prime divisor `P` of `X`, viewed as a divisor over `X`, is `ord_P`. -/
private theorem valuation_ofPrimeDivisor [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation :=
  Valuation.ext fun φ => by
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [functionFieldMap_id_apply]

/-- A divisor over a normal variety which is not exceptional has the valuation of a prime divisor
of the variety. -/
private theorem exists_primeDivisor_divisorialValuation_eq_of_not_isExceptional
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) (D : DivisorOver k sX)
    (hD : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.valuation = P.divisorialValuation := by
  obtain ⟨P, hP⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  exact ⟨P, hP.trans (valuation_ofPrimeDivisor hX P)⟩

/-- **Valuative criterion.** For a proper dominant morphism `f : Y ⟶ X` of integral schemes, a
valuation `ξ` of `k(Y)` whose restriction along `f^*` is nonnegative on the local ring at `z ∈ X`
dominates the local ring of a point of `Y`. -/
private theorem exists_valuation_dominates_stalk_of_isProper {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] {f : Y ⟶ X} [IsProper f] [IsDominant f] (z : X)
    (ξ : Valuation Y.functionField ℤᵐ⁰)
    (hξ : ∀ b : X.presheaf.stalk z, ξ (functionFieldMap f (algebraMap _ X.functionField b)) ≤ 1) :
    ∃ x : Y, (∀ a : Y.presheaf.stalk x, ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk z →+* R :=
    ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (hξ b)
  have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h := ‹IsProper f›
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := R
      K := Y.functionField
      i₁ := Y.fromSpecStalk (genericPoint Y)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk f,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
      Y.fromSpecStalk (genericPoint Y) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
      Y.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : Y.presheaf.stalk x,
      algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]
    exact (g.hom a).2
  · rw [hga]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- For a proper birational morphism `f : Y ⟶ X` from a normal variety, every divisor `D` over
`X` has the valuation of a divisor `E` over `Y`, read on `k(X)` through `f^*`. -/
private theorem exists_properDivisorOver_comap_eq {Y : Scheme.{u}} [IsIntegral Y] {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsProper f]
    (D : ProperDivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ E : ProperDivisorOver k (f ≫ sX), E.valuation.comap (functionFieldMap f) = D.valuation := by
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    exact congrArg D.valuation (e.symm_apply_apply t)
  obtain ⟨x, h1, h2⟩ :=
    exists_valuation_dominates_stalk_of_isProper (D.f D.E.genericPoint) ξ fun b =>
      (congrArg (fun v => v (algebraMap _ X.functionField b)) hξ).trans_le
        (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver
          (D.f D.E.genericPoint) rfl _)
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  exact ⟨D', by rw [hv, hξ]⟩

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

/-! ### Discrepancies and log discrepancies -/

section Dictionary

variable [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A presentation of `div(ω) + B`, coefficientwise, is a presentation as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum_of_coeff {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X}
    (h : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ) :
    Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (C j) := by
  ext Γ
  change (Divisor.toRDivisor (divisorOfForm ω) + B).coeff Γ =
    (∑ j, r j • Divisor.toRDivisor (C j)).coeff Γ
  rw [coeff_sum_smul_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
    coeff_divisorOfForm]
  exact h Γ

/-- A datum computing the discrepancy `a_ω(E, B)`, with `div(ω)` a canonical divisor, computes
the log discrepancy `1 + a_ω(E, B)`. -/
private theorem isLogDiscrepancy_one_add_of_isDiscrepancyWith {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {a : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n B ω r L E a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hX, -, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω0, ⟨divisorOfForm ω, hK, fun Γ => rfl⟩, m, r, L, L', hLc,
    fun Γ => ?_, hpb, by ring⟩
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] using congrArg (fun D : RDivisor X => D.coeff Γ) hsum

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

/-- A discrepancy computed with a fixed canonical divisor `K` gives the log discrepancy of any
proper model of the valuation. -/
private theorem isLogDiscrepancy_of_isDiscrepancy [PerfectField k] {n : ℕ} {K : Divisor X}
    {B : RDivisor X} {E : ProperDivisorOver k sX} {a : ℝ}
    (h : IsDiscrepancy sX n K B E.valuation a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E', ω, m, r, L, hv, rfl, hw⟩ := h
  obtain ⟨hX, hn, hω0, hLc, hsum, -⟩ := id hw
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum E
  obtain rfl := hc.eq hw hv.symm
  exact isLogDiscrepancy_one_add_of_isDiscrepancyWith hK hc

/-- A log discrepancy `a` of a proper model `E` gives the discrepancy `a - 1` of its valuation,
computed with any canonical divisor `K` for which `K + B` is `ℝ`-Cartier. -/
private theorem isDiscrepancy_of_isLogDiscrepancy [PerfectField k] (hX : IsNormalVariety k sX)
    {n n' : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : IsCartierCombination (Divisor.toRDivisor K + B)) {E : ProperDivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n' B E.toDivisorOver a) :
    IsDiscrepancy sX n K B E.valuation (a - 1) := by
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨-, -, ω', hω0', ⟨K', hK', hK'ω⟩, m', r', C, C', hCc, hsum', hpb, ha⟩ := h
  obtain rfl : n = n' := by exact_mod_cast hn.symm.trans hK'.topologicalKrullDim_eq
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

/-! ### The crepant boundary and klt -/

/-- **The crepant boundary of a smooth model.** Let `f : Y ⟶ X` be a proper birational morphism
from a smooth variety, `ω` a rational top form with `div ω` canonical, and `D_Y` the crepant
boundary, `div(f^*ω) + D_Y = f^*(div ω + D)`. Then `div(f^*ω)` is canonical on `Y`, and every prime
divisor `R` of `Y` has discrepancy `-coeff_R D_Y` over `(X, D)`. -/
private theorem isCanonicalDivisor_and_isDiscrepancy_valuationOver_of_isRCartierPullback
    [CharZero k] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {D : RDivisor X} (hX : IsNormalVariety k sX) {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D)) {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsProper f]
    [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX))
    (hsm : IsSmoothScheme (f ≫ sX)) (hf : IsBirationalMorphism f) {DY : RDivisor Y}
    (hDY : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + DY)) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n ∧
      ∀ R : Mori.PrimeDivisor Y,
        IsDiscrepancy sX n (divisorOfForm ω) D (R.valuationOver f) (-DY.coeff R) := by
  have hn := hK.topologicalKrullDim_eq
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hnY : topologicalKrullDim Y = n := hn ▸
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hf).symm
  have hσ0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
    hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hnY
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n :=
    hK₀.of_linearlyEquivalent <| by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hσ0
  have hKDY : IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + DY) := by
    obtain ⟨m', r', L', L'', hLc, -, hpb, heq⟩ := hDY
    refine ⟨m', r', L'', fun j => (hpb j).2.isCartier (hLc j), ?_⟩
    rw [heq]
    simp only [toRDivisor_eq_mapCoeffs]
  refine ⟨hKY, fun R => ?_⟩
  let ER : ProperDivisorOver k (f ≫ sX) :=
    ⟨DivisorOver.ofPrimeDivisor k hY R, (inferInstance : IsProper (𝟙 Y))⟩
  have hER : ER.valuation = R.divisorialValuation := valuation_ofPrimeDivisor hY R
  have h1 := isDiscrepancy_divisorialValuation hY _ hσ0 hKY hKDY R
  rw [← hER] at h1
  have h2 := (isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD f hY hf hDY hKY ER _).mpr h1
  rwa [hER] at h2

/-- A real canonical pair with no coefficient one is klt for some canonical divisor `K` and
dimension `n`. -/
private theorem IsRealCanonicalPair.exists_isKawamataLogTerminal [PerfectField k]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {B : RDivisor X} (hB : IsRealCanonicalPair sX B) :
    ∃ (n : ℕ) (K : Divisor X), IsKawamataLogTerminal sX n K B := by
  obtain ⟨hX, hcoef, ⟨n, K, hK, ⟨m, r, C, hCc, hC⟩⟩, hcan⟩ := hB
  have hcoef' : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P < 1 := fun P => by
    by_cases h0 : B.coeff P = 0
    · simp [h0]
    · exact ⟨(hcoef P h0).1.le, (hcoef P h0).2⟩
  have hKD : IsCartierCombination (Divisor.toRDivisor K + B) := by
    refine ⟨m, r, C, hCc, ?_⟩
    have h : Divisor.toRDivisor K + B = ∑ j, r j • Divisor.toRDivisor (C j) := by
      ext Γ
      change (Divisor.toRDivisor K + B).coeff Γ = (∑ j, r j • Divisor.toRDivisor (C j)).coeff Γ
      rw [Flips.coeff_sum_smul_toRDivisor, ← hC Γ, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
      rfl
    simpa only [toRDivisor_eq_mapCoeffs] using h
  refine ⟨n, K, ⟨hX, fun P => ⟨(hcoef' P).1, (hcoef' P).2.le⟩⟩, hK, hKD, ?_⟩
  rintro F - b ⟨c, hc, rfl⟩
  obtain ⟨-, -, -, E', -, -, -, -, rfl, -, -⟩ := id hc
  by_cases hE' : E'.toDivisorOver.IsExceptional
  · have := hcan n _ _ hE' (isLogDiscrepancy_of_isDiscrepancy hc)
    linarith
  · obtain ⟨P, hP⟩ := exists_primeDivisor_divisorialValuation_eq_of_not_isExceptional hX _ hE'
    have hcP := (show E'.valuation = P.divisorialValuation from hP) ▸ hc
    rw [hcP.eq_neg_coeff]
    linarith [(hcoef' P).2]

/-- The crepant boundary `D_Y = f^*(div ω + B) - div(f^*ω)` of a proper birational model is
supported on the strict transform of `B` and the `f`-exceptional prime divisors. -/
private theorem coeff_ne_zero_or_isExceptionalPrimeDivisor_of_crepantBoundary [PerfectField k]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} {B : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsProper f]
    [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {GP : RDivisor Y}
    (hGP : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + B) GP)
    (P : Mori.PrimeDivisor Y)
    (hP :
      (GP - Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω))).coeff P ≠ 0) :
    (birationalInverseTransform f hf B).coeff P ≠ 0 ∨ IsExceptionalPrimeDivisor sX f P := by
  classical
  obtain ⟨Ex, aE, GP', hEx', hGP', -, hform⟩ := discrepancy_formula hX B ω hω0 hK hKD f hY hf
  have hGG : GP' = GP := IsRCartierPullback.eq f hGP' hGP
  by_cases hex : IsExceptionalPrimeDivisor sX f P
  · exact Or.inr hex
  · left
    have hPEx : P ∉ Ex := fun h => hex ((hEx' P).mp h)
    have h := DFunLike.congr_fun hform P
    simp only [Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.single_apply, Finset.sum_ite_eq', hPEx, if_false, add_zero, hGG] at h
    rw [DivisorWithCoeffs.coeff_apply] at hP ⊢
    rw [Finsupp.sub_apply, ← h] at hP
    simpa using hP

/-- A divisor `E_Y` over `Y` whose valuation on `k(X)` is that of an exceptional divisor over `X`,
but not that of an `f`-exceptional prime divisor of `Y`, has center of codimension at least two
on `Y`. -/
private theorem two_le_codimension_center_of_comap_eq [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {f : Y ⟶ X} [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (EY : ProperDivisorOver k (f ≫ sX)) (E : ProperDivisorOver k sX)
    (hEY : haveI : IsDominant f := hf.isDominant
      EY.valuation.comap (functionFieldMap f) = E.valuation)
    (hE : E.IsExceptional)
    (hν : ∀ P, IsExceptionalPrimeDivisor sX f P →
      (ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ inferInstance : ProperDivisorOver k sX).valuation ≠
        E.valuation) :
    2 ≤ codimension EY.center := by
  have : IsDominant f := hf.isDominant
  rw [EY.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center]
  by_contra hlt
  have hne : ¬ EY.toDivisorOver.IsExceptional := fun hM =>
    hlt ((MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hY _).mp hM)
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_divisorialValuation_eq_of_not_isExceptional hY _ hne
  have hνQ : (ProperDivisorOver.mk ⟨Y, f, hY, hf, Q⟩ inferInstance :
      ProperDivisorOver k sX).valuation = E.valuation := by
    rw [← hEY]
    ext g
    change Q.divisorialValuation (functionFieldMap f g) =
      EY.toDivisorOver.valuation (functionFieldMap f g)
    rw [hQ]
  by_cases hQex : IsExceptionalPrimeDivisor sX f Q
  · exact hν Q hQex hνQ
  · refine hQex ⟨hY, hf, inferInstance, ?_⟩
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_of_valuation_eq hX.1 (D' := E) hνQ]
    exact hE

/-- Over a real canonical pair `(X, B)`, a divisor over `X` with discrepancy `-c < 0` satisfies
`c ≤ d = max ({0} ∪ {bⱼ})`. -/
private theorem IsRealCanonicalPair.le_realThresholdMax_of_isDiscrepancy [PerfectField k]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {B : RDivisor X} (hB : IsRealCanonicalPair sX B) {n : ℕ}
    {K : Divisor X} (E : ProperDivisorOver k sX) {c : ℝ}
    (h : IsDiscrepancy sX n K B E.valuation (-c)) (hc : 0 < c) : c ≤ realThresholdMax B := by
  have hne : ¬ E.toDivisorOver.IsExceptional := fun hM => by
    have := hB.2.2.2 n _ _ hM (isLogDiscrepancy_of_isDiscrepancy h)
    linarith
  obtain ⟨P, hP⟩ := exists_primeDivisor_divisorialValuation_eq_of_not_isExceptional hB.1 _ hne
  have hcP : c = B.coeff P := by
    have := ((show E.valuation = P.divisorialValuation from hP) ▸ h).eq_neg_coeff
    linarith
  have hPsupp : P ∈ B.support := by
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hcP]
    exact hc.ne'
  have := le_realThresholdMax_of_mem_support B hPsupp
  linarith

/-- On a proper birational model `f : Y ⟶ X` from a smooth variety on which the crepant boundary
`D_Y` is supported on an snc divisor and satisfies the pair condition, an exceptional divisor over
a real canonical pair `(X, B)` with log discrepancy `< 2 - d` has the valuation of an
`f`-exceptional prime divisor of `Y`. -/
private theorem IsRealCanonicalPair.exists_isExceptionalPrimeDivisor_valuation_eq [CharZero k]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {B : RDivisor X} (hB : IsRealCanonicalPair sX B) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsProper f]
    [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX))
    (hsm : IsSmoothScheme (f ≫ sX)) (hf : IsBirationalMorphism f) {DY : RDivisor Y}
    (hDY : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + B)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + DY))
    {G : Divisor Y} (hG : IsSNCDivisor (f ≫ sX) G) (hDG : ∀ P, DY.coeff P ≠ 0 → P ∈ G.support)
    (hD1 : ∀ P, DY.coeff P < 1)
    (hpair : ∀ P ∈ G.support, ∀ Q ∈ G.support, P ≠ Q →
      ((P.support : Set Y) ∩ Q.support).Nonempty → 2 ≤ (1 - DY.coeff P) + (1 - DY.coeff Q))
    (E : ProperDivisorOver k sX) (hE : E.IsExceptional) {b : ℝ}
    (hb : IsDiscrepancy sX n (divisorOfForm ω) B E.valuation (b - 1))
    (hlt : b < 2 - realThresholdMax B) :
    ∃ P, IsExceptionalPrimeDivisor sX f P ∧
      (ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ inferInstance : ProperDivisorOver k sX).valuation =
        E.valuation := by
  obtain ⟨hKY, hprime⟩ :=
    isCanonicalDivisor_and_isDiscrepancy_valuationOver_of_isRCartierPullback hB.1 hω0 hK hKD hY
      hsm hf hDY
  obtain ⟨EY, hEY⟩ := exists_properDivisorOver_comap_eq hY hf E
  have haY := (isDiscrepancy_comap_functionFieldMap_iff hB.1 hω0 hK hKD f hY hf hDY hKY EY
    (b - 1)).mp (by rwa [hEY])
  by_contra hν
  obtain ⟨-, PY, -, -, -, hpos, hle⟩ :=
    codimension_center_eq_two_of_logDiscrepancy_lt_two (f ≫ sX) hY.1 hsm hG hDG
      (fun P _ => (hD1 P).le) hpair EY
      (two_le_codimension_center_of_comap_eq hB.1 hY hf EY E hEY hE fun P hP h => hν ⟨P, hP, h⟩)
      ⟨b - 1, haY, rfl⟩ (by linarith [zero_le_realThresholdMax B])
  have hF1 : IsDiscrepancy sX n (divisorOfForm ω) B
      (ProperDivisorOver.mk ⟨Y, f, hY, hf, PY⟩ inferInstance : ProperDivisorOver k sX).valuation
      (-DY.coeff PY) := hprime PY
  linarith [hB.le_realThresholdMax_of_isDiscrepancy _ hF1 hpos]

/-! ### Finiteness -/

variable [IsAlgClosed k] [CharZero k] [IsLocallyNoetherian X] [IsNormal X]

/-- For a real canonical pair `(X, B)` with no coefficient one and `d = max ({0} ∪ {bⱼ})`, only
finitely many exceptional divisorial valuations with center on `X` have log discrepancy
`a(E, X, B) < 2 - d`. -/
@[mmp "lem_fourfold_real_canonical_small_finite"]
public theorem IsRealCanonicalPair.finite_logDiscrepancyLtSet_two_sub_realThresholdMax
    {B : RDivisor X} (hB : IsRealCanonicalPair sX B) :
    (logDiscrepancyLtSet sX B (2 - realThresholdMax B)).Finite := by
  classical
  haveI : LocallyOfFiniteType sX := hB.1.1.toLocallyOfFiniteType
  haveI : CompactSpace X := hB.1.1.toQuasiCompact.compactSpace_of_compactSpace
  obtain ⟨n, K, hklt⟩ := hB.exists_isKawamataLogTerminal
  obtain ⟨hlv, hK, hKD, -⟩ := id hklt
  have hX : IsNormalVariety k sX := hlv.isNormalVariety
  obtain ⟨Y, f, hlog, -, hpair⟩ := hklt.exists_isLogResolution_two_le_logDiscrepancy_add
  obtain ⟨-, hYvar, hYsm, hfp, hfb, G, hG01, hGiff, hGsnc⟩ := id hlog
  haveI : IsIntegral Y := hYvar.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hYvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : Smooth (f ≫ sX) := hYsm.smooth
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal Y := AlgebraicGeometry.isNormal_of_smooth (f ≫ sX)
  haveI : CompactSpace Y := hYvar.toQuasiCompact.compactSpace_of_compactSpace
  haveI := hfp
  haveI : IsDominant f := hfb.isDominant
  have hY : IsNormalVariety k (f ≫ sX) := ⟨hYvar, inferInstance⟩
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨GP, hGP, -⟩ := existsUnique_isRCartierPullback f hKD
  set DY : RDivisor Y :=
    GP - Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) with hDYdef
  have hDY : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + B)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + DY) := by
    rwa [hDYdef, add_sub_cancel]
  let toX : Mori.PrimeDivisor Y → ProperDivisorOver k sX := fun P =>
    ProperDivisorOver.mk ⟨Y, f, hY, hfb, P⟩ hfp
  have hF1 : ∀ P : Mori.PrimeDivisor Y,
      IsDiscrepancy sX n (divisorOfForm ω) B (toX P).valuation (-DY.coeff P) :=
    (isCanonicalDivisor_and_isDiscrepancy_valuationOver_of_isRCartierPullback hX hω0 hK hKD hY
      hYsm hfb hDY).2
  have hF3 : ∀ P, DY.coeff P < 1 := fun P => by
    linarith [hklt.2.2.2 _ (hasNonemptyCenter_valuation (toX P)) _ ⟨_, hF1 P, rfl⟩]
  have hGmem : ∀ P, P ∈ G.support ↔ G.coeff P = 1 := fun P => by
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
    rcases hG01 P with h0 | h1 <;> simp [*]
  have hpairY : ∀ P ∈ G.support, ∀ Q ∈ G.support, P ≠ Q →
      ((P.support : Set Y) ∩ Q.support).Nonempty → 2 ≤ (1 - DY.coeff P) + (1 - DY.coeff Q) :=
    fun P hP Q hQ hPQ hmeet => hpair hY hfb hfp P Q hPQ ((hGiff P).mp ((hGmem P).mp hP)).symm
      ((hGiff Q).mp ((hGmem Q).mp hQ)).symm hmeet _ _ ⟨_, hF1 P, by ring⟩ ⟨_, hF1 Q, by ring⟩
  refine (G.support.finite_toSet.image fun P => (toX P).valuation).subset ?_
  rintro ν ⟨n', E, b, hEex, rfl, hb, hlt⟩
  let E₀ : ProperDivisorOver k sX := ⟨E, hb.2.1⟩
  obtain ⟨P, hP, hPE⟩ := hB.exists_isExceptionalPrimeDivisor_valuation_eq hω0 hK hKD hY hYsm
    hfb hDY hGsnc (fun P hP => (hGmem P).mpr ((hGiff P).mpr
      (coeff_ne_zero_or_isExceptionalPrimeDivisor_of_crepantBoundary hX hω0 hK hKD hY hfb hGP P
        hP)))
    hF3 hpairY E₀ ((isExceptional_iff_two_le_coheight hK.topologicalKrullDim_eq E₀).mpr
      ((MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX E).mp hEex))
    (isDiscrepancy_of_isLogDiscrepancy hX hK hKD (E := E₀) hb) hlt
  exact ⟨P, (hGmem P).mpr ((hGiff P).mpr (Or.inr hP)), hPE⟩

end MMP.Fourfold
