module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialQFactorial

/-!
# Divisorial contractions preserve klt pairs

Let `(X, Δ)` be a klt pair, with `X` a `ℚ`-factorial projective variety over an algebraically
closed field of characteristic zero, `R` a `(K_X + Δ)`-negative extremal ray of `NE̅(X)` and
`f : X → Y` a divisorial contraction of `R`. If `Δ` is effective, or if `K_Y + f_*Δ` is
`ℚ`-Cartier, then `K_Y + f_*Δ` is `ℚ`-Cartier and `(Y, f_*Δ)` is klt.

Without one of these two assumptions the conclusion fails: on the ruled surface
`ℙ_B(𝒪_B ⊕ L)` over an elliptic curve `B` with `Δ = -π^*G₀` for a suitable reduced `G₀`,
`(X, Δ)` is terminal, the negative section spans a `(K_X + Δ)`-negative ray, and its contraction
`f` has `K_Y + f_*Δ` not `ℚ`-Cartier.

When `Δ` is effective, `K_Y + f_*Δ` is `ℚ`-Cartier because `Y` is `ℚ`-factorial
(`MMP.Mori.isQFactorial_of_isDivisorialContraction`). The divisor `-(K_X + Δ)` is `f`-ample,
hence `f`-nef. A divisor `F` exceptional over `Y` is, read on `k(X) = k(Y)`, a divisor over `X`,
and `a(F, Y, f_*Δ) ≥ a(F, X, Δ)` by the negativity comparison
`MMP.Mori.isDiscrepancy_le_transformDivisor_of_isRelativelyNef`. If `F` is exceptional over `X`
then `a(F, X, Δ) ≥ discrep(X, Δ)`; otherwise `F` has the valuation of a prime divisor `P` of `X`
and `a(F, X, Δ) = -coeff_P Δ ≥ -c`, where `c < 1` bounds the coefficients of `Δ`. Hence
`discrep(Y, f_*Δ) ≥ min(discrep(X, Δ), -c) > -1`; the coefficients of `f_*Δ` are coefficients
of `Δ`, so they are `< 1`.

## Main results

* `MMP.Mori.IsDivisorialContraction.isKltPair_transformDivisor`: divisorial contractions of
  `(K_X + Δ)`-negative extremal rays preserve klt pairs.

## Implementation notes

The canonical divisor of `Y` is the transform `f_* K_X` of the canonical divisor `K_X` of `X`
(`MMP.Mori.RationalMap.transformDivisor` along `f` regarded as a rational map), and the
boundary is `f_* Δ`; both are cut out by the same rational top form, so the discrepancies on `X`
and on `Y` are compared with compatible canonical divisors. The pair property of `(X, Δ)` is
part of `MMP.Mori.IsKltPair`, and that of `(Y, f_*Δ)` is part of the conclusion.

Kollár–Mori bound `a(F, Y, f_*Δ)` for `F` with centre the exceptional divisor `E` by the strict
inequality `a(F, Y, f_*Δ) > a(E, X, Δ)`. The non-strict comparison suffices, since already
`a(E, X, Δ) = -coeff_E Δ > -1`, and the uniform bound `c` makes the infimum strictly `> -1`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Corollary 3.43(1).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

namespace MMP.Mori

/-! ### Relative nefness -/

section RelativelyNef

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-nef. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {k : Type} [Field k]
    {X Y : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sX f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have hq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩
  refine ⟨hq, fun C hC => ?_⟩
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)]
  set F : Divisor X := (D.cartierIndexSMul hq : Divisor X)
  have hFc : F.IsCartier := (D.cartierIndexSMul hq).2
  set N := D.cartierIndex hq
  have hLpos : 0 < L.degreeOn k sX C.ι C.dim_le hL := by
    have := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC
  have hFL : m • F = N • L := by
    apply Divisor.toQDivisor_injective
    rw [map_nsmul, map_nsmul, QDivisor.toQDivisor_cartierIndexSMul, hLD, ← natCast_zsmul,
      ← natCast_zsmul, smul_smul, smul_smul, mul_comm]
  have key : (m : ℤ) * F.degreeOn k sX C.ι C.dim_le hFc =
      N * L.degreeOn k sX C.ι C.dim_le hL := by
    rw [← Divisor.degreeOn_nsmul', ← Divisor.degreeOn_nsmul', Divisor.degreeOn_congr hFL]
  have hFpos : 0 ≤ F.degreeOn k sX C.ι C.dim_le hFc :=
    nonneg_of_mul_nonneg_right (a := (m : ℤ)) (by rw [key]; positivity) (by exact_mod_cast hm)
  exact mul_nonneg (by positivity) (by exact_mod_cast hFpos)

end RelativelyNef

/-! ### The canonical divisor of `Y` -/

section Canonical

variable {k : Type} [Field k] [PerfectField k] {X Y : Scheme.{0}}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]

omit [CompactSpace X] in
/-- The push-forward of a canonical divisor along a proper birational morphism of normal varieties
over a perfect field is a canonical divisor: if `K_X = div(ω)` and `ω = f^*τ`, then
`f_* K_X = div(τ)`. -/
private theorem isCanonicalDivisor_transformDivisor (hY : IsNormalVariety k sY) {f : X ⟶ Y}
    [LocallyOfFiniteType (f ≫ sY)] (hX : IsNormalVariety k (f ≫ sY)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor (f ≫ sY) n) :
    Divisor.IsCanonicalDivisor sY n (RationalMap.transformDivisor (X := X) f.toRationalMap K) := by
  have hbij := hf.functionFieldMap_bijective
  have hnY : topologicalKrullDim Y = n := by
    rw [← toENat_trdeg_functionField (sX := sY), trdeg_functionField_eq_of_bijective sY f hbij,
      toENat_trdeg_functionField (sX := f ≫ sY)]
    exact hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hnY
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sY hY hnY
  obtain ⟨ω₁, hω₁0, hω₁⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sY n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sY f τ = ω₁ := by
    change pullbackForms (K := Y.functionField) (K' := X.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  have hτ0 : τ ≠ 0 := fun h0 => hω₁0 (by
    rw [← hpull, h0]
    change pullbackForms (K := Y.functionField) (K' := X.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp)
  have hdiv : divisorOfForm τ = RationalMap.transformDivisor (X := X) f.toRationalMap K := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨E, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf P
    rw [htr]
    change P.ordForm τ = K.coeff E
    rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, hpull,
      hω₁]
  rw [← hdiv]
  exact hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hτ0)

end Canonical

/-! ### Divisors over `Y` and over `X` -/

section DivisorsOver

/-- If a divisor `D` over `X` and a divisor `D'` over the separated `Y` satisfy
`v(D) ∘ f^* = v(D')`, then `f` maps the centre of `D` on `X` to the centre of `D'` on `Y`:
`f (D.f η_E) = D'.f η_{E'}`. -/
private theorem map_genericPoint_eq_of_valuation_comap_eq {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] (f : X ⟶ Y) [IsDominant f]
    (D : DivisorOver k sX) (D' : DivisorOver k sY)
    (hv : D.valuation.comap (functionFieldMap f) = D'.valuation) :
    f (D.f D.E.genericPoint) = D'.f D'.E.genericPoint := by
  refine MMP.Positivity.DivisorOver.eq_of_dominates sY D'.valuation (fun a => ?_) (fun a ha => ?_)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl) <;>
  rw [← hv, Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _
      ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu))

/-- **Valuative criterion for a proper dominant morphism.** If `f : X ⟶ Y` is proper and the
pullback of a valuation `ξ` of `k(X)` is integral on the local ring of a point `z` of `Y`, then `ξ`
dominates the local ring of some point of `X`. -/
private theorem exists_valuation_dominates_of_isProper {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] [IsProper f] (ξ : Valuation X.functionField ℤᵐ⁰)
    (z : Y) (hw : ∀ b : Y.presheaf.stalk z,
      ξ (functionFieldMap f (algebraMap _ Y.functionField b)) ≤ 1) :
    ∃ x : X, (∀ a : X.presheaf.stalk x, ξ (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        ξ (algebraMap _ X.functionField a) < 1 := by
  let R := ξ.valuationSubring
  let φ : Y.presheaf.stalk z →+* R :=
    ((functionFieldMap f).comp (algebraMap (Y.presheaf.stalk z) Y.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (hw b)
  have hgen : genericPoint Y ⤳ z := (genericPoint_spec Y).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : @IsProper _ _ f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk f,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
      X.fromSpecStalk (genericPoint X) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      X.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : X.presheaf.stalk x,
      algebraMap _ X.functionField a = ((g.hom a : R) : X.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]
    exact (g.hom a).2
  · rw [hga]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- **Divisors over `Y` are divisors over `X`.** Let `f : X ⟶ Y` be a proper birational morphism
from a normal variety. Every divisor `D'` over `Y` has, read on `k(Y)`, the valuation of a divisor
`D` over `X`. -/
private theorem exists_divisorOver_valuation_comap_eq {k : Type} [Field k]
    {X Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {f : X ⟶ Y}
    (hX : IsNormalVariety k (f ≫ sY)) (hf : IsBirationalMorphism f) [IsProper f]
    (D' : DivisorOver k sY) :
    haveI : IsIntegral X := hX.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    ∃ D : DivisorOver k (f ≫ sY), D.valuation.comap (functionFieldMap f) = D'.valuation := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have hbX := hf.functionFieldMap_bijective
  let e : Y.functionField ≃+* X.functionField := RingEquiv.ofBijective (functionFieldMap f) hbX
  set ξY : Valuation Y.functionField ℤᵐ⁰ := D'.valuation with hξY
  let ξ : Valuation X.functionField ℤᵐ⁰ := ξY.comap (e.symm : X.functionField →+* Y.functionField)
  have hξ : ξ.comap (functionFieldMap f) = ξY := by
    ext t
    change ξY (e.symm (functionFieldMap f t)) = ξY t
    rw [show e.symm (functionFieldMap f t) = t from e.symm_apply_apply t]
  have hz1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl
  obtain ⟨x, h1, h2⟩ := exists_valuation_dominates_of_isProper f ξ (D'.f D'.E.genericPoint)
    fun b => (congrArg (fun v => v (algebraMap _ Y.functionField b)) hξ).trans_le (hz1 b)
  -- `ξ` is a divisor of `k(X)`: `ord_E` on `D'.Y`, along `k(X) ≅ k(Y) ≅ k(D'.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sY) := hX.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sY) ξ := by
    have := D'.isIntegral
    have := D'.isNormal
    have := D'.isLocallyNoetherian
    have := D'.isDominant
    refine ⟨D'.Y, D'.f ≫ sY, D'.isNormalVariety, D'.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sY
    let := MMP.Mori.functionFieldAlgebra (f ≫ sY)
    let := MMP.Mori.functionFieldAlgebra (D'.f ≫ sY)
    let eX := MMP.Mori.functionFieldAlgEquiv sY f hbX
    let eY := MMP.Mori.functionFieldAlgEquiv sY D'.f
      D'.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eX.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbX.2 t
    have h1 : eX.symm (functionFieldMap f s) = s := eX.symm_apply_apply s
    change ξY (e.symm (functionFieldMap f s)) =
      D'.E.divisorialValuation (eY (eX.symm (functionFieldMap f s)))
    rw [h1, show e.symm (functionFieldMap f s) = s from e.symm_apply_apply s]
    rfl
  obtain ⟨D, -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sY) hdiv x h1 h2
  refine ⟨D.toDivisorOver, ?_⟩
  change D.valuation.comap _ = _
  rw [hv, hξ]

/-- A prime divisor `E` of `W` is exceptional for a morphism `g : W ⟶ Z` exactly when the point
`g(η_E)` has coheight at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight {W Z : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] (g : W ⟶ Z) (E : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) g.toRationalMap E ↔
      2 ≤ Order.coheight (g E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hsub : g '' (E.idealSheaf.support : Set W) ⊆ closure {g E.genericPoint} := by
    rintro _ ⟨e, he, rfl⟩
    have hηe : E.genericPoint ⤳ e := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
    exact specializes_iff_mem_closure.mp (hηe.map g.continuous)
  refine ⟨fun h => h _ (subset_closure ⟨E.genericPoint, ?_, rfl⟩), fun h x hx => ?_⟩
  · change E.genericPoint ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
    exact subset_closure rfl
  · have hx' : g E.genericPoint ⤳ x := specializes_iff_mem_closure.mpr
      (closure_minimal hsub isClosed_closure hx)
    exact h.trans (Order.coheight_anti (show x ≤ g E.genericPoint from hx'))

end DivisorsOver

/-! ### Discrepancies over `X` -/

section DiscrepanciesOverX

/-- The coefficients of a `ℚ`-divisor that are all `< 1` are bounded by a single `c < 1`. -/
private theorem exists_coeff_le_of_coeff_lt_one {X : Scheme.{0}} {Δ : QDivisor X}
    (h : ∀ P, Δ.coeff P < 1) : ∃ c < 1, ∀ P, Δ.coeff P ≤ c := by
  classical
  refine ⟨(insert 0 (Δ.support.image Δ.coeff)).max' (Finset.insert_nonempty _ _), ?_,
    fun P => Finset.le_max' _ _ ?_⟩
  · simp only [Finset.max'_lt_iff, Finset.mem_insert, Finset.mem_image]
    rintro _ (rfl | ⟨P, -, rfl⟩)
    exacts [one_pos, h P]
  · by_cases hP : P ∈ Δ.support
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP)
    · rw [show Δ.coeff P = 0 from Finsupp.notMem_support_iff.mp hP]
      exact Finset.mem_insert_self _ _

/-- If every coefficient of `Δ` is at most `c`, every divisor over `X` has discrepancy at least
`min(discrep(X, Δ), -c)`. -/
private theorem min_discrep_le_of_isDiscrepancy {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hΔ : IsPairWith sX n K Δ) {c : ℚ} (hc : ∀ P, Δ.coeff P ≤ c) {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) :
    min (discrep sX n K Δ) (((-c : ℚ) : ℝ) : EReal) ≤ ((a : ℝ) : EReal) := by
  by_cases hD : D.IsExceptional
  · exact (min_le_left _ _).trans (discrep_le hD ha)
  refine (min_le_right _ _).trans (EReal.coe_le_coe_iff.mpr ?_)
  obtain ⟨P, hP⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hΔ.1 D hD
  obtain ⟨aP, haP⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΔ.isPair hΔ.2.1
    (DivisorOver.ofPrimeDivisor k hΔ.1 P)
  rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hΔ hP ha haP,
    haP.eq_neg_coeff_of_ofPrimeDivisor]
  exact_mod_cast neg_le_neg (hc P)

/-- **Discrepancy of the push-forward.** For a proper birational morphism `f : X ⟶ Y` of normal
varieties with `-(K_X + Δ)` `f`-nef and `K_Y + f_*Δ` `ℚ`-Cartier, if `discrep(X, Δ) > -1` and
every coefficient of `Δ` is `< 1`, then `discrep(Y, f_*Δ) > -1`. -/
private theorem neg_one_lt_discrep_transformDivisor {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sY] [IsSeparated sY] [IsSeparated (Y ↘ Limits.terminal Scheme)] {f : X ⟶ Y}
    [QuasiCompact (f ≫ sY)] [IsProper f] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hpw : IsPairWith (f ≫ sY) n K Δ) (hYv : IsNormalVariety k sY)
    (hXv : IsNormalVariety k (f ≫ sY)) (hfb : IsBirationalMorphism f)
    (hKY : Divisor.IsCanonicalDivisor sY n (RationalMap.transformDivisor f.toRationalMap K))
    (hN : QDivisor.IsRelativelyNef (f ≫ sY) f (-(Divisor.toQDivisor K + Δ)))
    (hQY : (Divisor.toQDivisor (RationalMap.transformDivisor f.toRationalMap K) +
      RationalMap.transformDivisor f.toRationalMap Δ).IsQCartier)
    (hdisc : -1 < discrep (f ≫ sY) n K Δ) (hround : ∀ P, Δ.coeff P < 1) :
    -1 < discrep sY n (RationalMap.transformDivisor f.toRationalMap K)
      (RationalMap.transformDivisor f.toRationalMap Δ) := by
  have : IsDominant f := hfb.isDominant
  have hK := hpw.2.1
  obtain ⟨c, hc1, hcP⟩ := exists_coeff_le_of_coeff_lt_one hround
  refine (lt_min (c := (((-c : ℚ) : ℝ) : EReal)) hdisc ?_).trans_le
    (le_discrep_iff.mpr fun D' a' hD' ha' => ?_)
  · simpa using EReal.coe_lt_coe_iff.mpr
      (show (-1 : ℝ) < ((-c : ℚ) : ℝ) by exact_mod_cast neg_lt_neg hc1)
  obtain ⟨D, hv⟩ := exists_divisorOver_valuation_comap_eq hXv hfb D'
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpw.isPair hK D
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E := by
    rw [isExceptional_toRationalMap_iff_two_le_coheight, Scheme.Hom.comp_apply,
      map_genericPoint_eq_of_valuation_comap_eq f D D' hv]
    exact (isExceptional_toRationalMap_iff_two_le_coheight D'.f D'.E).mp hD'
  exact (min_discrep_le_of_isDiscrepancy hpw hcP ha).trans <| EReal.coe_le_coe_iff.mpr <| by
    exact_mod_cast isDiscrepancy_le_transformDivisor_of_isRelativelyNef hpw.isPair hYv rfl hfb
      hK hKY hN hQY D D' hv hE ha ha'

end DiscrepanciesOverX

/-- **Divisorial contractions preserve klt** (KM, Corollary 3.43(1)). Let `X` be a `ℚ`-factorial
projective variety over an algebraically closed field `k` of characteristic zero, `K` a
canonical divisor of `X` of dimension `n` and `Δ` a `ℚ`-divisor with `(X, Δ)` klt. Let `R` be a
`(K + Δ)`-negative extremal ray of `NE̅(X)` and `f : X ⟶ Y` a divisorial contraction of `R`.
If `Δ` is effective or `f_*K + f_*Δ` is `ℚ`-Cartier, then `(Y, f_*Δ)`, with canonical divisor
`f_*K`, is a klt pair; in particular `f_*K + f_*Δ` is `ℚ`-Cartier. -/
@[mmp "thm_km3c_divisorial_contraction_preserves_klt"]
public theorem IsDivisorialContraction.isKltPair_transformDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Y}
    (hQ : MMP.Fourfold.IsQFactorial sX)
    (hR : MMP.Fourfold.IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R)
    (hf : IsDivisorialContraction k sX sY R f)
    (hΔ : 0 ≤ Δ ∨ (Divisor.toQDivisor (RationalMap.transformDivisor f.toRationalMap K) +
      RationalMap.transformDivisor f.toRationalMap Δ).IsQCartier)
    (hklt : IsKltPair sX n K Δ) :
    IsKltPair sY n (RationalMap.transformDivisor f.toRationalMap K)
      (RationalMap.transformDivisor f.toRationalMap Δ) := by
  have hFace := hf.isContractionOfFace
  have hXp := hFace.isProjectiveVariety_source
  have hYp := hFace.isProjectiveVariety_target
  have hfs := hFace.comp_eq
  have hXv := hf.isNormalVariety
  have hfb := hf.isBirationalMorphism
  have hYv : IsNormalVariety k sY := ⟨hYp.toIsVariety, inferInstance⟩
  have : IsProper f := (IsProjective.of_comp f sY (by
    rw [hfs]
    exact ((isProjectiveVariety_iff_isProjective' k sX).mp hXp).2)).isProper
  obtain ⟨hQX, hRay, hneg⟩ := hR
  -- `-(K_X + Δ)` is `f`-ample
  have hA := hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sY hXv hXp hYp ⟨n, hklt.1.2.1⟩
    hQX hRay (fun v hv hv0 => by
      simpa [MMP.Fourfold.QDivisor.curveForm, Finsupp.sum] using hneg v hv hv0) f hfs
    (fun C hC => (hFace.isContractedBy_iff C).mp hC)
  -- `K_Y + f_*Δ` is `ℚ`-Cartier
  have hQY : (Divisor.toQDivisor (RationalMap.transformDivisor f.toRationalMap K) +
      RationalMap.transformDivisor f.toRationalMap Δ).IsQCartier := by
    rcases hΔ with h | h
    · exact MMP.Fourfold.isQCartier_of_isQFactorial sY
        (isQFactorial_of_isDivisorialContraction hQ hklt
          (DivisorWithCoeffs.isEffective_iff_nonneg.mpr h) hneg hf) _
    · exact h
  subst hfs
  have : QuasiCompact (f ≫ sY) := hXv.1.toQuasiCompact
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : IsDominant f := hfb.isDominant
  have : QuasiCompact sY := hYv.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sY) := hXv.1.toLocallyOfFiniteType
  have : IsSeparated (Y ↘ Limits.terminal Scheme) := by
    rw [show (Y ↘ Limits.terminal Scheme) = sY ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨hpw, hdisc, hround⟩ := hklt
  have hKY := isCanonicalDivisor_transformDivisor hYv hXv hfb hpw.2.1
  have hN := isRelativelyNef_of_hasRelativelyAmpleMultiple (sX := f ≫ sY) hA
  rw [roundDown_nonpos_iff] at hround
  refine ⟨⟨hYv, hKY, hQY⟩,
    neg_one_lt_discrep_transformDivisor hpw hYv hXv hfb hKY hN hQY hdisc hround,
    roundDown_nonpos_iff.mpr fun Q => ?_⟩
  obtain ⟨E, -, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hYv hXv hfb Q
  change (RationalMap.transformDivisor (X := X) f.toRationalMap Δ) Q < 1
  rw [htr]
  exact hround E

end MMP.Mori
