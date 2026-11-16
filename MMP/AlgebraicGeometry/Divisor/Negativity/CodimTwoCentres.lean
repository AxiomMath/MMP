module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization

/-!
# Log resolutions and the negativity lemma (Kollár–Mori 0.4, 2.40, 3.39)

Over a field `k` of characteristic `0`, every pair `(X, D)` of a normal variety and an
`ℝ`-divisor has a log resolution, obtained by principalizing the ideal of `Supp D`; principalizing
`I_Z · I_{Supp D}` for a closed subset `Z ⊊ X` gives moreover a log resolution `f` with `f⁻¹(Z)`
of pure codimension one and `Ex(f) ∪ f⁻¹(Supp D) ∪ f⁻¹(Z)` an snc divisor.

For a proper birational morphism `h : Z ⟶ Y` of normal varieties over `k` and a `ℚ`-Cartier
`ℚ`-divisor `B` on `Z` with `-B` `h`-nef, `B` is effective if and only if `h_* B` is (negativity
lemma), and, when the varieties have dimension `n ≥ 3` and `Y` is affine, every prime divisor of
`Z` over a codimension-two centre has nonnegative coefficient in `B` once `h_* B` is effective.

## Main results

* `MMP.Mori.exists_isLogResolution`: existence of log resolutions.
* `MMP.Mori.QDivisor.coeff_nonneg_of_isRelativelyNef_neg_of_codimension_eq_two`: negativity on
  codimension-two centres.
* `MMP.Mori.QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg`: the
  negativity lemma.
* `MMP.Mori.exists_isLogResolution_isPureCodimOne_preimage`: log resolutions which also resolve a
  closed subset.

## Implementation notes

The resolutions come from
`MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap` (resolution
with principalization of a nonzero ideal sheaf). The negativity statements reduce to the
`ℝ`-divisor form `MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback` through
`QDivisor.toRDivisor`; `h_*` is `MMP.Mori.RationalMap.transformDivisor h.toRationalMap`. The
auxiliary lemmas of each proof live in the namespace `Proof_<tag>` of its card.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 0.4(10), 2.40,
  3.39
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Flips MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-- Let `X` be a normal variety over a field `k` of characteristic zero and `D` an `ℝ`-divisor on
`X`. Then `(X, D)` has a log resolution `g : Y ⟶ X`. -/
@[mmp "lem_km0_log_resolution_exists"]
public theorem exists_isLogResolution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : RDivisor X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), IsLogResolution sX D g := by
  haveI : IsIntegral X := hX.1.toIsIntegral
  have hI : D.suppIdeal ≠ ⊥ := fun h ↦ MMP.Fourfold.genericPoint_notMem_supp D <| by
    rw [← SetLike.mem_coe, ← D.coe_support_suppIdeal, h]
    simp
  obtain ⟨Y, f, -, hproj, hbir, hsm, -, -, hsnc, hpure⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap sX hX.1 _ hI
  refine ⟨Y, f, ⟨⟨IsProjective.isProper hproj, hbir, hsm⟩, hpure, ?_⟩⟩
  convert hsnc using 2
  rw [Scheme.IdealSheafData.support_comap]
  congr 1

end MMP.Mori

namespace Proof_lem_km2a_negativity_lemma

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
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
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

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
  have hc2 := isCurve_ι (k := k) C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

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
private theorem isRelativelyNef_toRDivisor_of_isRelativelyNef [QuasiCompact sX]
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

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
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
      (IrreducibleCloseds.closureSingleton (genericPoint X))).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

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

/-- If `h_* B` is effective, every prime divisor `P` of `Z` that is not exceptional over `Y` has
nonnegative coefficient in `B`. -/
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

end Proof_lem_km2a_negativity_lemma

namespace MMP.Mori

open Proof_lem_km2a_negativity_lemma

/-- **Negativity lemma.** Let `h : Z ⟶ Y` be a proper birational morphism of normal varieties
over `k` and `B` a `ℚ`-Cartier `ℚ`-divisor on `Z` with `-B` `h`-nef. Then `B` is effective if
and only if its pushforward `h_* B` is effective. -/
@[mmp "lem_km2a_negativity_lemma"]
public theorem QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg
    (k : Type u) [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (_hB : B.IsQCartier) (hnef : (-B).IsRelativelyNef sZ h) :
    B.IsEffective ↔
      (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective := by
  refine ⟨isEffective_transformDivisor, fun heff E => ?_⟩
  have := isEffective_of_isRelativelyNef_neg k sY sZ hY hZ h hh hhb (B := B.toRDivisor)
    (by simpa using isRelativelyNef_toRDivisor_of_isRelativelyNef (k := k) hnef) (fun P hP => by
      rw [QDivisor.coeff_toRDivisor]
      exact_mod_cast coeff_nonneg_of_not_isExceptionalPrimeDivisor hY h (hh ▸ hZ) hhb heff P hP) E
  rw [QDivisor.coeff_toRDivisor] at this
  exact_mod_cast this

/-- **Negativity on codimension-two centres.** Let `h : Z ⟶ Y` be a proper birational morphism
of normal varieties of dimension `n ≥ 3` over `k`, with `Y` affine, and `B` a `ℚ`-Cartier
`ℚ`-divisor on `Z` with `-B` `h`-nef and `h_* B` effective. Then every prime divisor `E` of `Z`
whose image `h(E)` has codimension two in `Y` has nonnegative coefficient in `B`. -/
@[mmp "lem_km2a_negativity_codim_two_components"]
public theorem QDivisor.coeff_nonneg_of_isRelativelyNef_neg_of_codimension_eq_two
    (k : Type u) [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ) [IsAffine Y]
    {n : ℕ} (_hn : 3 ≤ n) (_hYdim : topologicalKrullDim Y = n)
    (_hZdim : topologicalKrullDim Z = n)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (hB : B.IsQCartier) (hnef : (-B).IsRelativelyNef sZ h)
    (heff : (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective)
    (E : PrimeDivisor Z)
    (_hE : codimension (IrreducibleCloseds.closureSingleton (h.base E.genericPoint)) = 2) :
    0 ≤ B.coeff E :=
  (QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg k sY sZ hY hZ h
    hh hhb hB hnef).2 heff E

end MMP.Mori

namespace Proof_lem_km2b_dlt_log_resolution_exists

/-- The union of two closed subsets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_sup {T : Type*} [TopologicalSpace T] {A B : Closeds T}
    (hA : IsPureCodimOne A) (hB : IsPureCodimOne B) : IsPureCodimOne (A ⊔ B) := by
  intro W hW
  have hsub : (W : Set T) ⊆ (A : Set T) ∪ B := hW.1
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp W.isIrreducible.isPreirreducible)
    _ _ A.isClosed B.isClosed hsub with h | h
  · exact hA W ⟨h, fun W' hW' hle ↦ hW.2 (hW'.trans Set.subset_union_left) hle⟩
  · exact hB W ⟨h, fun W' hW' hle ↦ hW.2 (hW'.trans Set.subset_union_right) hle⟩

/-- The support of an effective Cartier divisor on a scheme locally of finite type over a field
is of pure codimension one. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {D : Y.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : IsPureCodimOne D.support := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by rw [hWη]; exact subset_closure rfl
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hD (hW.1 hηW)
    fun y hy hyη => ?_
  have hle : W ≤ e.symm y := by
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    exact hyη
  have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ D.support := by
    change closure {y} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed
  have heq : e.symm y = W := le_antisymm (hW.2 hsub hle) hle
  rw [← heq, e.apply_symm_apply]

section SNC

/-- The preimage in a subspace `C` of a preirreducible subset of `C` is preirreducible. -/
private theorem isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private theorem exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  refine ⟨W, ⟨closure_minimal (Subtype.coe_image_subset C t) hC, fun W' hW'C hWW' y hy ↦ ?_⟩,
    fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have ht := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rwa [← ht]
  exact subset_closure ⟨_, this, rfl⟩

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private theorem coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]
  rfl

private theorem codimension_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    codimension (primeIrr E) = 1 := E.codimension_one

private theorem exists_mem_le_primeIrr_of_subset_biUnion_support {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)}
    (W : IrreducibleCloseds X) (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) :
    ∃ E ∈ s, W ≤ primeIrr E := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]
      exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨E, hE, fun x hx ↦ by
    rw [← SetLike.mem_coe, coe_primeIrr]
    exact hWz hx⟩

/-- A closed subset of pure codimension one of an snc divisor is an snc divisor. -/
private theorem isSNCSubset_of_le {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {S C : Closeds X}
    (hS : IsSNCSubset sX S) (hC : IsPureCodimOne C) (hCS : C ≤ S) : IsSNCSubset sX C := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact Or.inl (le_bot_iff.mp hCS)
  right
  refine ⟨s.filter (fun E ↦ E.support ⊆ C), ?_, ?_⟩
  · refine subset_antisymm (Set.iUnion₂_subset fun E hE ↦ (Finset.mem_filter.mp hE).2)
      fun x hx ↦ ?_
    obtain ⟨W, hW, hxW⟩ := exists_maximal_ge C.isClosed
      (IrreducibleCloseds.closureSingleton x) (by
        change closure {x} ⊆ (C : Set X)
        exact closure_minimal (by simpa using hx) C.isClosed)
    obtain ⟨E, hE, hWE⟩ := exists_mem_le_primeIrr_of_subset_biUnion_support W (hs ▸ hW.1.trans hCS)
    have hWE' : W = primeIrr E := by
      by_contra hne
      have := Order.coheight_add_one_le (lt_of_le_of_ne hWE hne)
      rw [← codimension_eq_coheight, ← codimension_eq_coheight, codimension_primeIrr,
        hC W hW] at this
      exact absurd this (by decide)
    refine Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hE, ?_⟩, ?_⟩
    · rw [← coe_primeIrr, ← hWE']
      exact hW.1
    · rw [← coe_primeIrr, ← hWE']
      exact hxW (subset_closure rfl)
  · refine hsnc.of_support_subset ?_
    intro E hE
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hE ⊢
    simp only [Finsupp.single_apply] at hE ⊢
    rw [Finset.sum_ite_eq'] at hE ⊢
    split_ifs at hE with h1
    · rw [if_pos (Finset.mem_filter.mp h1).1]
      exact one_ne_zero
    · exact absurd rfl hE

end SNC

end Proof_lem_km2b_dlt_log_resolution_exists

namespace MMP.Mori

open Proof_lem_km2b_dlt_log_resolution_exists

/-- Let `X` be a normal variety over a field `k` of characteristic zero, `D` an `ℝ`-divisor on
`X` and `Z ⊊ X` a closed subset. Then there is a log resolution `f : Y ⟶ X` of `(X, D)` such that
`f⁻¹(Z)` is empty or of pure codimension one and `Ex(f) ∪ f⁻¹(Supp D) ∪ f⁻¹(Z)` is an snc
divisor. -/
@[mmp "lem_km2b_dlt_log_resolution_exists"]
public theorem exists_isLogResolution_isPureCodimOne_preimage {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : RDivisor X)
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX D f ∧
      IsPureCodimOne (Z.preimage f.continuous) ∧
      IsSNCSubset (f ≫ sX)
        (exceptionalSet f ⊔ D.supp.preimage f.continuous ⊔ Z.preimage f.continuous) := by
  obtain ⟨hXv, -⟩ := hX
  haveI : IsIntegral X := hXv.toIsIntegral
  set IZ := Scheme.IdealSheafData.vanishingIdeal Z
  set IS := Scheme.IdealSheafData.vanishingIdeal D.supp
  have hsupp : (IZ * IS).support = Z ⊔ D.supp := by
    rw [Scheme.IdealSheafData.support_mul]
    rfl
  have hI : IZ * IS ≠ ⊥ := by
    intro h
    have hξ : genericPoint X ∈ (IZ * IS).support := by
      rw [h, Scheme.IdealSheafData.support_bot]
      trivial
    rw [hsupp] at hξ
    rcases hξ with h1 | h2
    · refine hZ (Closeds.ext (Set.eq_univ_of_univ_subset ?_))
      rw [← (genericPoint_spec X).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) Z.isClosed
    · exact MMP.Fourfold.genericPoint_notMem_supp D h2
  obtain ⟨Y, f, hYv, hproj, hbir, hsm, -, hcart, hsnc, hpure⟩ :=
    exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap sX hXv (IZ * IS) hI
  rw [comap_mul] at hcart
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have hZp : IsPureCodimOne (Z.preimage f.continuous) := by
    have := isPureCodimOne_support_of_isEffectiveCartierDivisor (f ≫ sX)
      (isEffectiveCartierDivisor_left_of_mul _ _ hcart)
    rwa [Scheme.IdealSheafData.support_comap] at this
  have hSp : IsPureCodimOne (D.supp.preimage f.continuous) := by
    have := isPureCodimOne_support_of_isEffectiveCartierDivisor (f ≫ sX)
      (isEffectiveCartierDivisor_right_of_mul _ _ hcart)
    rwa [Scheme.IdealSheafData.support_comap] at this
  have hsupY : ((IZ * IS).comap f).support =
      Z.preimage f.continuous ⊔ D.supp.preimage f.continuous := by
    rw [Scheme.IdealSheafData.support_comap, hsupp]
    rfl
  rw [hsupY] at hsnc
  refine ⟨Y, f, ⟨⟨hproj.isProper, hbir, hsm⟩, hpure, ?_⟩, hZp, ?_⟩
  · exact isSNCSubset_of_le hsnc (isPureCodimOne_sup hpure hSp)
      (sup_le_sup_left le_sup_right _)
  · rwa [sup_assoc, sup_comm (D.supp.preimage f.continuous)]

end MMP.Mori

end
