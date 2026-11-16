module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.LowDiscrepancySetStabilizes
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity

/-!
# A uniform discrepancy margin on a stabilized small klt tail

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfold step diagrams.
Then there are integers `q, r ≥ 1` such that `q` clears the denominator of every coefficient of
every boundary `B_i`, and every log discrepancy `a(ξ; X_i, B_i)` of a normalized divisorial
valuation `ξ` of `k(X_i)` is at least `δ = 1 / r`, for every `i`. Since the positive side of the
`i`-th step diagram is the model `X_{i+1}`, this covers both sides of every step. Moreover the
low-discrepancy sets `I_i = I(X_i, B_i)` all have the same finite cardinality `N = |I_∞|`.

The proof: choose `r ≥ 1` with `r (K_{X_0} + B_0)` Cartier. Every log discrepancy
`a(ξ; X_0, B_0)` is `1` plus `1/r` times an integer (the order of the pull-back of a local
generator of `𝒪(r (K_{X_0} + B_0))`), so it lies in `(1/r) ℤ`; being positive (klt), it is at
least `1/r`. By the comparison of discrepancies along a step diagram (Kollár–Mori 3.38, from the
negativity lemma), `a(ξ; X_i, B_i) ≤ a(ξ; X_{i+1}, B_{i+1})` for every divisorial valuation `ξ`
of the common function field, so the bound `1/r` holds at every stage. The boundaries
`B_{i+1} = (f_i⁺)⁻¹_* (f_i)_* B_i` are birational transforms, so one integer `q` clearing the
denominators of `B_0` clears those of every `B_i`. Finally the identifications `k(X_0) ≅ k(X_i)`
make `I_i` the bijective image of the finite set `I_∞`.

## Main results

* `MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail.exists_uniform_discrepancy_margin`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.38, 3.39
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19
-/

@[expose] public section

universe u

namespace MMP.Fourfold

section CurveSec

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_exists_forall_base_eq_of_isCurveNormalization (C : ProperCurve sX)
    {C' : Scheme.{u}} {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_exists_forall_base_eq_of_isCurveNormalization C hν
    ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_exists_forall_base_eq_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

end Intersection

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]
      exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

end CurveSec

section Km2aSec

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips TopologicalSpace

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- **`ℚ`-nefness is `ℝ`-nefness.** A `ℚ`-Cartier `ℚ`-divisor which is nef over `Y` is, as an
`ℝ`-divisor, `ℝ`-Cartier and nef over `Y`. -/
private theorem QDivisor.IsRelativelyNef.isRelativelyNef_toRDivisor [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{u}} {f : X ⟶ Y} {D : QDivisor X}
    (h : QDivisor.IsRelativelyNef sX f D) :
    MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D) := by
  obtain ⟨hD, hh⟩ := h
  set N := D.cartierIndex hD
  have hNpos : (0 : ℚ) < N := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set L : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hLc : L.IsCartier := (D.cartierIndexSMul hD).2
  have hLD : ∀ P, (L.coeff P : ℚ) = N * D.coeff P := fun P => by
    have := congrArg (fun G : QDivisor X => G.coeff P) (QDivisor.toQDivisor_cartierIndexSMul D hD)
    simpa [zsmul_eq_mul] using this
  refine ⟨1, fun _ => ((1 / N : ℚ) : ℝ), fun _ => L, fun _ => hLc, ?_, fun C hC x hx => ?_⟩
  · ext P
    rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor, smul_eq_mul, ← Rat.cast_intCast, hLD P]
    push_cast
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hNpos.ne']
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    have key := hh C hC
    rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
      Finsupp.sum_single_index (by simp)] at key
    simp only [smul_eq_mul, mul_one] at key
    rw [Fin.sum_univ_one, eq_degreeOn_of_isCartierIntersectionNumber (hd 0)]
    exact (by exact_mod_cast key :
      (0 : ℝ) ≤ ((1 / N : ℚ) : ℝ) * (L.degreeOn k sX C.ι C.dim_le hLc : ℝ))

end Intersection

/-- The negative of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} (h : IsCartierCombination D) : IsCartierCombination (-D) := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  exact ⟨m, -r, L, hL, by simp [neg_smul, Finset.sum_neg_distrib]⟩

/-- The zero divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_zero {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] :
    IsCartierCombination (0 : RDivisor X) :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩

/-- A prime divisor `P` of `Z` whose image `h(η_P)` has coheight at least two in `Y` is
exceptional over `Y`. -/
private theorem isExceptionalPrimeDivisor_of_two_le_coheight {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) (h : Z ⟶ Y)
    (hZ : IsNormalVariety k (h ≫ sY)) [IsProper h] (hhb : IsBirationalMorphism h)
    (P : MMP.Mori.PrimeDivisor Z) (h2 : 2 ≤ Order.coheight (h P.genericPoint)) :
    IsExceptionalPrimeDivisor sY h P := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨n, hYdim⟩ := exists_topologicalKrullDim_eq_natCast sY
  refine ⟨hZ, hhb, inferInstance, ?_⟩
  unfold ProperDivisorOver.IsExceptional
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hYdim]
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (h P.genericPoint)
  rw [hYdim] at hd
  exact (withBot_add_two_le_iff hd).mpr h2

/-- If `h_* B` is effective, then `B` has a nonnegative coefficient along every prime divisor `P`
of `Z` not exceptional over `Y`: such a `P` is the strict transform of the prime divisor `h(P)`,
whose coefficient in `h_* B` is that of `P` in `B`. -/
private theorem coeff_nonneg_of_not_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) (h : Z ⟶ Y)
    (hZ : IsNormalVariety k (h ≫ sY)) [IsProper h] (hhb : IsBirationalMorphism h) {B : QDivisor Z}
    (heff : (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective)
    (P : MMP.Mori.PrimeDivisor Z) (hP : ¬ IsExceptionalPrimeDivisor sY h P) :
    0 ≤ B.coeff P := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsDominant h := hhb.isDominant
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNormal Y := hY.2
  have : IsNormal Z := hZ.2
  have hbij := hhb.functionFieldMap_bijective
  have hle : Order.coheight (h P.genericPoint) ≤ 1 := by
    by_contra hlt
    exact hP (isExceptionalPrimeDivisor_of_two_le_coheight hY h hZ hhb P
      (Order.add_one_le_of_lt (not_le.mp hlt)))
  haveI : ValuationRing (Y.presheaf.stalk (h P.genericPoint)) := by
    rcases lt_or_eq_of_le hle with h0 | h1
    · have hmax : IsMax (h P.genericPoint) :=
        Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
      have hgy : h P.genericPoint = genericPoint Y :=
        Specializes.antisymm (hmax (genericPoint_specializes _))
          (genericPoint_specializes _) |>.eq
      rw [hgy]
      change ValuationRing Y.functionField
      infer_instance
    · set Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
      have hQ : Q.genericPoint = h P.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1
      have := Q.isDiscreteValuationRing_localRing
      rw [← hQ]
      infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing h hbij P.genericPoint
  have hco : Order.coheight (h P.genericPoint) = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv
      (asIso (h.stalkMap P.genericPoint)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      P.coheight_genericPoint] at h1
    exact_mod_cast h1
  set Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = h P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  obtain ⟨E, hE, hiso, hcoeff⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hZ hhb Q
  have hEP : E = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap h hbij (x₁ := P.genericPoint) (x₂ := E.genericPoint)
      (hE.trans hQ)).symm
  have := heff Q
  rwa [DivisorWithCoeffs.coeff_apply, hcoeff B, hEP] at this

/-- **The negativity lemma for `ℝ`-divisors.** Let `h : Z ⟶ Y` be a proper birational morphism of
normal varieties and `B` an `ℝ`-divisor on `Z` with `-B` nef over `Y`. If the coefficient of `B`
along every prime divisor not exceptional over `Y` is nonnegative, then `B` is effective. -/
private theorem isEffective_of_isRelativelyNef_neg (k : Type u) [Field k] {Y Z : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z]
    [IsNormal Z] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ) (h : Z ⟶ Y)
    (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h) {B : RDivisor Z}
    (hnef : MMP.Flips.IsRelativelyNef k sZ h (-B))
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Z, ¬ IsExceptionalPrimeDivisor sY h P → 0 ≤ B.coeff P) :
    B.IsEffective := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNormal Y := hY.2
  have hMc : IsCartierCombination (-B) := by
    obtain ⟨m, r, L, hL, hD, -⟩ := hnef
    exact ⟨m, r, L, hL, hD⟩
  refine isEffective_of_isNumericallyEquivalentOver_pullback k sY sZ hY hZ h hh hhb
    (L := 0) (L' := 0) isCartierCombination_zero
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
    hMc hnef (by simpa using isCartierCombination_neg hMc) hBG ?_
  rw [neg_add_cancel]
  exact ⟨isCartierCombination_zero, isCartierCombination_zero, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂
    h₁ h₂ => (IsRIntersectionNumber.eq_and_linear k sZ C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩

/-- **Negativity lemma for `ℚ`-divisors.** For a proper birational morphism `h : Z ⟶ Y` of
normal varieties and a `ℚ`-divisor `B` on `Z` with `-B` nef over `Y`, if `h_* B` is effective then
so is `B`. -/
private theorem isEffective_of_isEffective_transformDivisor (k : Type u) [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (hnef : (-B).IsRelativelyNef sZ h)
    (heff : (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective) :
    B.IsEffective := fun E => by
  have := isEffective_of_isRelativelyNef_neg k sY sZ hY hZ h hh hhb (B := B.toRDivisor)
    (by simpa using QDivisor.IsRelativelyNef.isRelativelyNef_toRDivisor (k := k) hnef)
    (fun P hP => by
      rw [QDivisor.coeff_toRDivisor]
      exact_mod_cast coeff_nonneg_of_not_isExceptionalPrimeDivisor hY h (hh ▸ hZ) hhb heff P hP) E
  rw [QDivisor.coeff_toRDivisor] at this
  exact_mod_cast this

end Km2aSec

section CmpSec

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori
open scoped WithZero

/-- A birational morphism `f : X ⟶ Y` restricts to an isomorphism of a dense open of `X` onto a
dense open of `Y`, under which it is the inclusion of that open. -/
private theorem exists_partialIso_isOver {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) : ∃ e : X.PartialIso Y, e.IsOver f (𝟙 Y) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨W, hW, hWl, hWr, heq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at heq
  have hWl' : W ≤ e.source := hWl
  refine ⟨e.restrictSource W hW hWl', ?_⟩
  have h1 : (Scheme.Opens.isoOfLE hWl').inv ≫ (e.source.ι ⁻¹ᵁ W).ι = X.homOfLE hWl' := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  have h2 : X.homOfLE hWr ≫ X.topIso.hom = W.ι := by
    simp only [Scheme.topIso_hom]
    exact Scheme.homOfLE_ι X hWr
  change ((Scheme.Opens.isoOfLE hWl').inv ≫ (e.iso.hom.isoImage (e.source.ι ⁻¹ᵁ W)).hom ≫
    (e.target.ι.isoImage (e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W)).hom) ≫
    (e.target.ι ''ᵁ e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W).ι ≫ 𝟙 Y = W.ι ≫ f
  rw [Category.comp_id, Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι,
    Scheme.Hom.isoImage_hom_ι_assoc, ← Category.assoc, h1]
  exact heq.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) h2))

/-- For birational morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y`, the birational map
`φ = f'⁻¹ ∘ f : X ⇢ X'` satisfies `f' ∘ φ = f`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : RationalMap X X', φ.IsBirational ∧ φ.compHom f' = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := exists_partialIso_isOver hf
  obtain ⟨e₂, h₂⟩ := exists_partialIso_isOver hf'
  set e := e₁.trans e₂.symm
  have h : e.IsOver f f' := h₁.trans h₂.symm
  refine ⟨e.toRationalMap, RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨e.source, e.dense_source, le_rfl,
    le_top, ?_⟩
  change X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, h]
  simp

/-- An exceptional prime divisor of a rational map has no birational transform. -/
private theorem transformPrimeDivisor_eq_none_of_isExceptional {X Y : Scheme.{u}}
    {φ : RationalMap X Y} {E : PrimeDivisor X} (h : φ.IsExceptional E) :
    φ.transformPrimeDivisor E = none := by
  rcases hQ : φ.transformPrimeDivisor E with _ | Q
  · rfl
  exfalso
  have hdef := (RationalMap.transformPrimeDivisor_eq_some_iff.mp hQ).1
  have hsupp := RationalMap.support_transformPrimeDivisor hQ
  rcases h with h | ⟨-, h⟩
  · exact h hdef
  have hmem : Q.genericPoint ∈ (φ.transform E.idealSheaf.support : Set Y) := by
    rw [← hsupp]
    exact MMP.Flips.primeDivisor_genericPoint_mem_support Q
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h Q.genericPoint hmem
  rw [Q.coheight_genericPoint] at this
  norm_num at this

/-- The birational transform of a divisor supported on exceptional prime divisors vanishes. -/
private theorem transformDivisor_eq_zero_of_forall_not_isExceptional {X Y : Scheme.{u}}
    {φ : RationalMap X Y} {G : QDivisor X}
    (hG : ∀ P : PrimeDivisor X, ¬ φ.IsExceptional P → G.coeff P = 0) :
    φ.transformDivisor G = 0 := by
  classical
  rw [← Finsupp.sum_single G, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun P hP => RationalMap.transformDivisor_single_of_eq_none
    (transformPrimeDivisor_eq_none_of_isExceptional ?_) _
  by_contra h
  exact Finsupp.mem_support_iff.mp hP (hG P h)

/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m, hm, by rw [smul_neg]; exact h.neg⟩

/-- A valuation of `k(X')` is determined by its restriction to `k(Y)` along a birational
morphism `f' : X' ⟶ Y`. -/
private theorem valuation_eq_of_comap_eq {X' Y : Scheme.{u}} [IsIntegral X'] [IsIntegral Y]
    {f' : X' ⟶ Y} (hf' : IsBirationalMorphism f') [IsDominant f']
    {v w : Valuation X'.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap f') = w.comap (functionFieldMap f')) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hf'.functionFieldMap_bijective.2 t
    exact congrArg (fun u => u s) h

/-- Around a commutative square `g ≫ f = g' ≫ f'` of dominant morphisms of integral schemes, a
valuation of `k(Z)` restricts to the same valuation of `k(Y)` along either side. -/
private theorem comap_comap_functionFieldMap_eq {Z X X' Y : Scheme.{u}} [IsIntegral Z]
    [IsIntegral X] [IsIntegral X'] [IsIntegral Y] {g : Z ⟶ X} {f : X ⟶ Y} {g' : Z ⟶ X'}
    {f' : X' ⟶ Y} [IsDominant g] [IsDominant f] [IsDominant g'] [IsDominant f']
    (h : g ≫ f = g' ≫ f') {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation Z.functionField Γ) :
    (v.comap (functionFieldMap g)).comap (functionFieldMap f) =
      (v.comap (functionFieldMap g')).comap (functionFieldMap f') :=
  Valuation.ext fun t => by
    simp only [Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr h]

/-- **Negativity for exceptional divisors.** Let `h : Z ⟶ Y` be a proper birational morphism of
normal varieties and `H` an `h`-nef `ℚ`-divisor on `Z` supported on `h`-exceptional prime
divisors. Then `-H` is effective. -/
private theorem isEffective_neg_of_isRelativelyNef_of_coeff_eq_zero (k : Type u) [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h) {H : QDivisor Z}
    (hnef : H.IsRelativelyNef sZ h)
    (hexc : ∀ F : PrimeDivisor Z, ¬ RationalMap.IsExceptional (X := Z) h.toRationalMap F →
      H.coeff F = 0) :
    (-H).IsEffective :=
  isEffective_of_isEffective_transformDivisor k sY sZ hY hZ h
    hh hhb (by rwa [neg_neg]) <| by
      rw [map_neg, transformDivisor_eq_zero_of_forall_not_isExceptional hexc, neg_zero]
      exact DivisorWithCoeffs.isEffective_zero

/-- **Comparison of discrepancies** (Kollár–Mori 3.38). Let `f : X ⟶ Y`, `f' : X' ⟶ Y` be proper
birational morphisms of normal varieties with `f_*Δ = f'_*Δ'`, `-(K_X + Δ)` `f`-nef and
`K_{X'} + Δ'` `f'`-nef. If divisors `D` over `X` and `D'` over `X'` induce the same valuation of
`k(Y)`, then `a(D, X, Δ) ≤ a(D', X', Δ')`. -/
private theorem le_of_isDiscrepancy {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f']
    (hfs : f ≫ sY = sX) (hfs' : f' ≫ sY = sX')
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : IsDominant f := hf.isDominant
      haveI : IsDominant f' := hf'.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f'))
    {a a' : ℚ} (ha : IsDiscrepancy sX n KX Δ D a) (ha' : IsDiscrepancy sX' n KX' Δ' D' a') :
    a ≤ a' := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant f' := hf'.isDominant
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq hf hf'
  obtain ⟨Z, g, g', hZ, hg, hgp, hg'p, hg', -, hcomm, P, hP⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX hX' f f' φ
      hφ hφS D
  haveI := hgp
  haveI := hg'p
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  have hZ' : IsNormalVariety k (g' ≫ sX') := by
    rwa [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  obtain ⟨⟨ΔZ, hΔZ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha.isPair hK g hZ hg
  obtain ⟨⟨ΔZ', hΔZ', -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary ha'.isPair hK' g' hZ' hg'
  obtain ⟨hHnef, hHexc⟩ := isRelativelyNef_of_isDiscrepancy_sub hX hX' hY hfs hfs' hf hf' hK hK'
    hΔ hN hN' hZ hg hg' hcomm (ΔZ' - ΔZ) fun F b b' hb hb' => by
      have e1 := (hΔZ F).eq hb
      have e2 := (hΔZ' F).eq hb'
      change ΔZ'.coeff F - ΔZ.coeff F = b - b'
      linarith
  have hP0 : (0 : ℚ) ≤ -(ΔZ'.coeff P - ΔZ.coeff P) :=
    DivisorWithCoeffs.isEffective_iff_nonneg.mp
      (isEffective_neg_of_isRelativelyNef_of_coeff_eq_zero k sY (g ≫ sX) hY hZ (g ≫ f)
        (by rw [Category.assoc, hfs]) (isBirationalMorphism_comp_of_isBirational f g
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)) hHnef hHexc) P
  have hv' : D'.valuation = (⟨Z, g', hZ', hg', P⟩ : DivisorOver k sX').valuation := by
    refine valuation_eq_of_comap_eq hf' (hv.symm.trans ?_)
    rw [← hP]
    exact comap_comap_functionFieldMap_eq hcomm P.divisorialValuation
  have e1 : a = -ΔZ.coeff P := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
    ⟨hX, hK, by simpa only [neg_neg] using isQCartier_neg hN.1⟩ hP.symm ha (hΔZ P)
  have e2 : a' = -ΔZ'.coeff P :=
    MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq ⟨hX', hK', hN'.1⟩ hv' ha' (hΔZ' P)
  linarith

end CmpSec

section FlipSec

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-nef. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sX f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have hq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hq fun C hC => ?_
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hq hm L hL hLD]
  exact div_nonneg (by exact_mod_cast
    (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC).le) m.cast_nonneg

/-- For a proper birational morphism `g : X' ⟶ Y` onto a normal variety with exceptional set of
codimension at least two, `g_* g⁻¹_* B = B` for every divisor `B` on `Y`. -/
private theorem transformDivisor_inverseTransformDivisor {k : Type u} [Field k]
    {X' Y : Scheme.{u}} [IsLocallyNoetherian X'] [IsNormal X'] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) {g : X' ⟶ Y}
    (hX' : IsNormalVariety k (g ≫ sY)) [IsProper g] (hg : IsBirationalMorphism g)
    (h2 : 2 ≤ closedsCodimension (exceptionalSet g)) {R : Type*} [AddCommMonoid R]
    (B : DivisorWithCoeffs R Y) :
    RationalMap.transformDivisor (X := X') g.toRationalMap (inverseTransformDivisor g B) = B := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsIntegral X' := hX'.1.toIsIntegral
  have : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  have : IsDominant g := hg.isDominant
  refine Finsupp.ext fun Q => ?_
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX' hg Q
  rw [htr]
  have hQV : g E.genericPoint ∈ biregularLocus g := by
    rw [hEQ]
    exact MMP.Positivity.mem_biregularLocus_of_coheight_le_one g hg.functionFieldMap_bijective h2
      Q.coheight_genericPoint.le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hEQ hQV)
    (fun Q' hQ' => ?_) B
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hQ').1.symm.trans hEQ)

end FlipSec

section Main

open CategoryTheory MMP.Mori MMP.Fourfold.StepSequence
open AlgebraicGeometry hiding PrimeDivisor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Coefficients of birational transforms -/

/-- A map of divisors sending each `r P` to `r E` for some prime divisor `E`, or to `0`, keeps
a divisor whose coefficients become integral after multiplication by `q` with that property. -/
private theorem exists_int_mul_coeff_map {X Y : Scheme.{u}} (F : QDivisor X →+ QDivisor Y)
    (hF : ∀ (P : PrimeDivisor X) (r : ℚ),
      (∃ E, F (Finsupp.single P r) = Finsupp.single E r) ∨ F (Finsupp.single P r) = 0)
    (q : ℚ) {D : QDivisor X} (hD : ∀ P, ∃ z : ℤ, q * D.coeff P = z) (E : PrimeDivisor Y) :
    ∃ z : ℤ, q * (F D).coeff E = z := by
  classical
  have hterm : ∀ P, ∃ w : ℤ, q * (F (Finsupp.single P (D P))).coeff E = w := fun P => by
    obtain ⟨z, hz⟩ := hD P
    rcases hF P (D P) with ⟨E', hE'⟩ | h0
    · rw [hE', DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs
      · exact ⟨z, by rw [← hz, DivisorWithCoeffs.coeff_apply]⟩
      · exact ⟨0, by simp⟩
    · exact ⟨0, by rw [h0]; simp [DivisorWithCoeffs.coeff_apply]⟩
  choose w hw using hterm
  refine ⟨∑ P ∈ D.support, w P, ?_⟩
  have hsum : F D = ∑ P ∈ D.support, F (Finsupp.single P (D P)) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum, map_sum]
  rw [hsum, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [← hw P, DivisorWithCoeffs.coeff_apply]

/-- The birational transform of `r P` is `r E` for a prime divisor `E`, or `0`. -/
private theorem transformDivisor_single_cases {X Y : Scheme.{u}} (φ : RationalMap X Y)
    (P : PrimeDivisor X) (r : ℚ) :
    (∃ E, RationalMap.transformDivisor (R := ℚ) φ (Finsupp.single P r) = Finsupp.single E r) ∨
      RationalMap.transformDivisor (R := ℚ) φ (Finsupp.single P r) = 0 := by
  rcases h : φ.transformPrimeDivisor P with _ | E
  · exact Or.inr (RationalMap.transformDivisor_single_of_eq_none h r)
  · exact Or.inl ⟨E, RationalMap.transformDivisor_single_of_eq_some h r⟩

/-- The inverse transform of `r P` is `r E` for a prime divisor `E`, or `0`. -/
private theorem inverseTransformDivisor_single_cases {X Y : Scheme.{u}} (g : Y ⟶ X)
    (P : PrimeDivisor X) (r : ℚ) :
    (∃ E, inverseTransformDivisor (R := ℚ) g (Finsupp.single P r) = Finsupp.single E r) ∨
      inverseTransformDivisor (R := ℚ) g (Finsupp.single P r) = 0 := by
  rcases h : inverseTransformPrimeDivisor g P with _ | E
  · exact Or.inr (inverseTransformDivisor_single_of_eq_none h r)
  · exact Or.inl ⟨E, inverseTransformDivisor_single_of_eq_some h r⟩

/-- The integer `q` clearing the denominators of `B_0` clears those of every `B_i`. -/
private theorem exists_int_mul_coeff_B (S : StepSequence) (q : ℚ)
    (h0 : ∀ P, ∃ z : ℤ, q * (S.B 0).coeff P = z) :
    ∀ (i : ℕ) (P : PrimeDivisor (S.X i)), ∃ z : ℤ, q * (S.B i).coeff P = z
  | 0 => h0
  | i + 1 => by
    rw [S.B_eq i]
    exact exists_int_mul_coeff_map _ (inverseTransformDivisor_single_cases (S.fp i)) q
      (exists_int_mul_coeff_map _ (transformDivisor_single_cases (S.f i).toRationalMap) q
        (exists_int_mul_coeff_B S q h0 i))

/-- A positive integer clearing the denominators of a `ℚ`-divisor. -/
private theorem exists_int_mul_coeff {X : Scheme.{u}} (D : QDivisor X) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ P, ∃ z : ℤ, (q : ℚ) * D.coeff P = z := by
  classical
  refine ⟨∏ P ∈ D.support, (D P).den, Nat.one_le_iff_ne_zero.2
    (Finset.prod_ne_zero_iff.2 fun P _ => (D P).den_nz), fun P => ?_⟩
  by_cases hP : P ∈ D.support
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun P => (D P).den) hP
    refine ⟨c * (D P).num, ?_⟩
    rw [hc, DivisorWithCoeffs.coeff_apply]
    push_cast
    rw [mul_comm ((D P).den : ℚ) c, mul_assoc, mul_comm ((D P).den : ℚ), Rat.mul_den_eq_num]
  · refine ⟨0, ?_⟩
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.1 hP]
    simp

/-! ### The discrepancy margin -/

/-- The canonical divisor `K_i` of a step sequence has dimension four. -/
private theorem isCanonicalDivisor_K (S : StepSequence) (i : ℕ) :
    (S.K i).IsCanonicalDivisor (S.sX i) 4 := by
  obtain ⟨m, hm⟩ := (S.isFourfoldStepDiagram i).isCanonicalDivisor
  have h := hm.topologicalKrullDim_eq
  rw [(S.isFourfoldStepDiagram i).dim_minus] at h
  obtain rfl : m = 4 := by exact_mod_cast h.symm
  exact hm

/-- Every log discrepancy over `X_i` is taken in dimension four. -/
private theorem eq_four_of_isLogDiscrepancy (S : StepSequence) (i : ℕ) {n : ℕ}
    {B : RDivisor (S.X i)} {D : DivisorOver ℂ (S.sX i)} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy (S.sX i) n B D a) : n = 4 := by
  have e := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  rw [(S.isFourfoldStepDiagram i).dim_minus] at e
  exact_mod_cast e.symm

/-- **The base case.** If `m (K_0 + B_0)` is Cartier, every log discrepancy of the klt pair
`(X_0, B_0)` is a positive element of `(1/m) ℤ`, hence at least `1/m`. -/
private theorem one_div_le_of_isLogDiscrepancy_zero (S : StepSequence)
    (hklt : IsKltPair (S.sX 0) (S.B 0)) {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor (S.K 0) + S.B 0)).IsCartierDivisor) {n : ℕ}
    {D : DivisorOver ℂ (S.sX 0)} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy (S.sX 0) n (QDivisor.toRDivisor (S.B 0)) D a) :
    (1 : ℝ) / m ≤ a := by
  have hpos := hklt.2 n D a ha
  obtain rfl := eq_four_of_isLogDiscrepancy S 0 ha
  obtain ⟨-, U, hU, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hklt.1.isPair
    (isCanonicalDivisor_K S 0) hC (D.f D.E.genericPoint)
  have hd : IsDiscrepancy (S.sX 0) 4 (S.K 0) (S.B 0) D ((D.ordPullback τ : ℚ) / m) :=
    ⟨hklt.1.isPair.1, isCanonicalDivisor_K S 0, m, hm, hC, U, hU, τ, hτ, by
      field_simp⟩
  obtain rfl := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hd ha
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast at hpos ⊢
  rw [one_add_div hm'.ne'] at hpos ⊢
  have h1 : (0 : ℤ) < m + D.ordPullback τ := by
    exact_mod_cast (div_pos_iff_of_pos_right hm').mp hpos
  gcongr
  exact_mod_cast (show (1 : ℤ) ≤ m + D.ordPullback τ by omega)

/-- **The step comparison.** Every log discrepancy `a(D', X_{i+1}, B_{i+1})` dominates the log
discrepancy `a(D, X_i, B_i)` of a divisor `D` over `X_i` with the same valuation. -/
private theorem exists_isLogDiscrepancy_le_succ (S : StepSequence) (i : ℕ)
    (hklt : IsKltPair (S.sX i) (S.B i)) (hklt' : IsKltPair (S.sX (i + 1)) (S.B (i + 1)))
    {n : ℕ} {D' : DivisorOver ℂ (S.sX (i + 1))} {a' : ℝ}
    (ha' : MMP.Intersection.IsLogDiscrepancy (S.sX (i + 1)) n
      (QDivisor.toRDivisor (S.B (i + 1))) D' a') :
    ∃ (D : DivisorOver ℂ (S.sX i)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (S.sX i) n (QDivisor.toRDivisor (S.B i)) D a ∧
        a ≤ a' := by
  have h := S.isFourfoldStepDiagram i
  obtain rfl := eq_four_of_isLogDiscrepancy S (i + 1) ha'
  have hX := h.isNormalVariety_minus
  have hX' := h.isNormalVariety_plus
  have hY := h.isNormalVariety_target
  haveI : IsProper (S.f i) := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_minus
  haveI : IsProper (S.fp i) := h.isProper_plus
  haveI : QuasiCompact (S.sX i) := hX.1.toQuasiCompact
  haveI : QuasiCompact (S.sX (i + 1)) := hX'.1.toQuasiCompact
  have hf := h.isBirationalMorphism_minus
  have hf' := h.isBirationalMorphism_plus
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq hf' hf
  obtain ⟨Z, g, g', hZ, hg, hgp, hg'p, hg', -, hcomm, P, hP⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX' hX
      (S.fp i) (S.f i) φ hφ hφS D'
  have hZ' : IsNormalVariety ℂ (g' ≫ S.sX i) := by
    rwa [← h.comp_eq_minus, ← Category.assoc, ← hcomm, Category.assoc, h.comp_eq_plus]
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g ≫ S.sX (i + 1))
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  let D : DivisorOver ℂ (S.sX i) := ⟨Z, g', hZ', hg', P⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hklt.1.isPair
    (isCanonicalDivisor_K S i) D
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hklt'.1.isPair
    (isCanonicalDivisor_K S (i + 1)) D'
  refine ⟨D, 1 + (c : ℝ), MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hg'p,
    ?_⟩
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc' ha']
  have hΔ : RationalMap.transformDivisor (X := S.X i) (S.f i).toRationalMap (S.B i) =
      RationalMap.transformDivisor (X := S.X (i + 1)) (S.fp i).toRationalMap (S.B (i + 1)) := by
    rw [S.B_eq i]
    exact (transformDivisor_inverseTransformDivisor hY (h.comp_eq_plus ▸ hX') hf'
      h.isSmallMorphism_plus.two_le_codimension _).symm
  have hN' := h.hasRelativelyAmpleMultiple_plus
  rw [← S.K_eq, ← S.B_eq] at hN'
  have hv : D.valuation.comap (functionFieldMap (S.f i)) =
      D'.valuation.comap (functionFieldMap (S.fp i)) := by
    rw [← hP]
    exact (comap_comap_functionFieldMap_eq hcomm P.divisorialValuation).symm
  have hle := le_of_isDiscrepancy hX hX' hY h.comp_eq_minus h.comp_eq_plus hf hf'
    (isCanonicalDivisor_K S i) (isCanonicalDivisor_K S (i + 1)) hΔ
    (isRelativelyNef_of_hasRelativelyAmpleMultiple h.hasRelativelyAmpleMultiple_minus)
    (isRelativelyNef_of_hasRelativelyAmpleMultiple hN') D D' hv hc hc'
  linarith [show (c : ℝ) ≤ c' by exact_mod_cast hle]

/-- The bound `1/m` on the log discrepancies of `(X_0, B_0)` propagates to every stage. -/
private theorem one_div_le_of_isLogDiscrepancy (S : StepSequence) (hklt : S.IsKlt) (m : ℕ)
    (h0 : ∀ (n : ℕ) (D : DivisorOver ℂ (S.sX 0)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (S.sX 0) n (QDivisor.toRDivisor (S.B 0)) D a →
        (1 : ℝ) / m ≤ a) :
    ∀ (i n : ℕ) (D : DivisorOver ℂ (S.sX i)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (S.sX i) n (QDivisor.toRDivisor (S.B i)) D a →
        (1 : ℝ) / m ≤ a
  | 0 => h0
  | i + 1 => fun n D' a' ha' => by
    obtain ⟨D, a, ha, hle⟩ := exists_isLogDiscrepancy_le_succ S i (hklt i) (hklt (i + 1)) ha'
    exact (one_div_le_of_isLogDiscrepancy S hklt m h0 i n D a ha).trans hle

/-! ### The identification of the low-discrepancy sets -/

/-- The valuation of `k(X_i)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem Corresponds.unique (S : StepSequence) :
    ∀ (i : ℕ) {ξ : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
      {η η' : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))},
      S.Corresponds i ξ η → S.Corresponds i ξ η' → η = η'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨ζ, hζ, hη⟩, ⟨ζ', hζ', hη'⟩ => by
    obtain rfl := Corresponds.unique S i hζ hζ'
    exact valuation_eq_of_comap_eq (S.isFourfoldStepDiagram i).isBirationalMorphism_plus
      (hη.trans hη'.symm)

/-- Distinct valuations of `k(X_0)` correspond to distinct valuations of `k(X_i)`. -/
private theorem Corresponds.injective (S : StepSequence) :
    ∀ (i : ℕ) {ξ ξ' : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
      {η : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))},
      S.Corresponds i ξ η → S.Corresponds i ξ' η → ξ = ξ'
  | 0, _, _, _, h, h' => h.symm.trans h'
  | i + 1, _, _, _, ⟨ζ, hζ, hη⟩, ⟨ζ', hζ', hη'⟩ => by
    have : ζ = ζ' := valuation_eq_of_comap_eq
      (S.isFourfoldStepDiagram i).isBirationalMorphism_minus (hη.symm.trans hη')
    subst this
    exact Corresponds.injective S i hζ hζ'

/-- `I_i`, the image of `I_∞` under the identification `k(X_0) ≅ k(X_i)`, has the cardinality
of `I_∞`. -/
private theorem encard_lowDiscrepancySetAt (S : StepSequence) (hS : S.IsStabilizedSmallKltTail)
    (i : ℕ) : (S.lowDiscrepancySetAt i).encard = S.stableLowDiscrepancySet.encard := by
  rw [hS.lowDiscrepancySetAt_eq i]
  have hex : ∀ ξ ∈ S.stableLowDiscrepancySet, ∃ η, S.Corresponds i ξ η := fun ξ hξ => by
    obtain ⟨η, -, hη⟩ := hξ i
    exact ⟨η, hη⟩
  choose F hF using hex
  refine (Set.encard_congr (Equiv.ofBijective
    (fun ξ : S.stableLowDiscrepancySet => (⟨F ξ.1 ξ.2, ξ.1, ξ.2, hF ξ.1 ξ.2⟩ :
      {η | ∃ ξ ∈ S.stableLowDiscrepancySet, S.Corresponds i ξ η})) ⟨?_, ?_⟩)).symm
  · rintro ⟨ξ, hξ⟩ ⟨ξ', hξ'⟩ hh
    have hh' : F ξ hξ = F ξ' hξ' := congrArg Subtype.val hh
    exact Subtype.ext (Corresponds.injective S i (hF ξ hξ) (hh' ▸ hF ξ' hξ'))
  · rintro ⟨η, ξ, hξ, hη⟩
    exact ⟨⟨ξ, hξ⟩, Subtype.ext (Corresponds.unique S i (hF ξ hξ) hη)⟩

end Main

end MMP.Fourfold

namespace MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **A uniform discrepancy margin on a stabilized small klt tail.** For a stabilized small klt
tail `S` there are integers `q, r ≥ 1` such that `q • B_i` has integral coefficients for every
`i`, every log discrepancy `a(ξ; X_i, B_i)` is at least `1 / r` for every `i`, and every
low-discrepancy set `I_i` has the same finite cardinality `N`, that of the stable
low-discrepancy set `I_∞`. -/
@[mmp "lem_mmp_fourfold_tail_uniform_discrepancy_margin"]
public theorem exists_uniform_discrepancy_margin {S : StepSequence}
    (hS : S.IsStabilizedSmallKltTail) :
    ∃ q r : ℕ, 1 ≤ q ∧ 1 ≤ r ∧
      (∀ (i : ℕ) (P : MMP.Mori.PrimeDivisor (S.X i)), ∃ z : ℤ, (q : ℚ) * (S.B i).coeff P = z) ∧
      (∀ (i : ℕ) (ξ : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))) (a : ℝ),
        S.IsLogDiscrepancyAt i ξ a → (1 : ℝ) / r ≤ a) ∧
      ∃ N : ℕ, S.stableLowDiscrepancySet.encard = N ∧
        ∀ i : ℕ, (S.lowDiscrepancySetAt i).encard = N := by
  obtain ⟨q, hq, hq0⟩ := exists_int_mul_coeff (S.B 0)
  obtain ⟨r, hr, hC⟩ := (S.isFourfoldStepDiagram 0).isQCartier_minus.exists_pos
  have hfin := (finite_stableLowDiscrepancySet_and_exists_lowDiscrepancySetAt_eq S
    hS.isSmallFrom_zero hS.isKlt).1
  refine ⟨q, r, hq, hr, exists_int_mul_coeff_B S q hq0, fun i ξ a ha => ?_,
    hfin.toFinset.card, hfin.encard_eq_coe_toFinset_card, fun i => ?_⟩
  · obtain ⟨n, D, -, -, ha⟩ := ha
    exact one_div_le_of_isLogDiscrepancy S hS.isKlt r
      (fun n D a ha => one_div_le_of_isLogDiscrepancy_zero S (hS.isKlt 0) hr hC ha) i n D a ha
  · rw [encard_lowDiscrepancySetAt S hS i, hfin.encard_eq_coe_toFinset_card]

end MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail

end
