module

public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport

/-!
# Lowering boundaries: dlt, lc and klt pairs on fourfold models

Three facts about changing the boundary of a pair, used in the fourfold programme.

**Lowering the boundary of a dlt pair.** If `(X, Δ)` is dlt and `0 ≤ Δ' ≤ Δ` with `Δ - Δ'`
`ℚ`-Cartier, then `(X, Δ')` is dlt. Write `m(Δ - Δ') = G` with `G` an effective Cartier divisor;
a log discrepancy of a divisor `E` over `X` with respect to `Δ'` exceeds the one with respect to
`Δ` by `(1/m) coeff_E(f^*G) ≥ 0`, so the lc condition and the positivity of log discrepancies over
the closed set `Z` both pass from `Δ` to `Δ'`.

**Log canonicity is tested on one log resolution.** Let `(X, B)` be a pair, `π : W ⟶ X` a log
resolution and `B_W` the crepant pull-back, `K_W + B_W = π^*(K_X + B)`. Then `(X, B)` is log
canonical if and only if every coefficient of `B_W` is at most one. A divisorial valuation over
`X` has a centre on `W` (`π` is proper), and its log discrepancy is computed on `(W, B_W)` by
crepant invariance. The support of `B_W` lies in the snc divisor `Ex(π) ∪ π⁻¹(Supp B)`, where the
discrepancy formula for snc pairs gives discrepancies `≥ -1`.

**Removing the reduced boundary while preserving a nef-model comparison.** Let `X` be a smooth
projective variety, `(X, B)` an effective lc pair with snc support, and `A ≤ B` an effective ample
`ℚ`-divisor with no component in `⌊B⌋`. Given a nef log birational model `(Y, B_Y)` of `(X, B)`,
there are effective klt boundaries `Δ ∼_ℝ B` on `X` and `Δ_Y` on `Y` with the same
common-resolution comparison `p^*(K_X + Δ) - q^*(K_Y + Δ_Y) = p^*(K_X + B) - q^*(K_Y + B_Y)`.
We take `Δ = B + c div f` for small `c > 0`, where `div f = (τ)₀ - n D_A - ⌊B⌋` for a Cartier
multiple `D_A` of `A` and a general section `τ` of the globally generated `𝒪_X(n D_A + ⌊B⌋)`
(Serre, Bertini), and `Δ_Y = B_Y + c div f_Y` for the function `f_Y` corresponding to `f` under
`k(Y) ≅ k(X)`. The pull-backs of `div f` and `div f_Y` agree on every common resolution, so the
comparison is unchanged; since it is effective, `(Y, Δ_Y)` inherits klt from `(X, Δ)`. Along a
contracted prime divisor where the comparison vanishes, `0 < a(E; Y, Δ_Y) = a(E; X, Δ) ≤ 1`.

## Main results

* `MMP.Intersection.IsDltPair.of_le`: lowering the boundary of a dlt pair.
* `MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one`: lc is tested on a log resolution.
* `MMP.Fourfold.neg_one_lt_of_isDiscrepancy_of_isSNC`: discrepancies of an snc boundary with
  coefficients `< 1` exceed `-1`; with `MMP.Fourfold.exists_isSNC_superset_support` and
  `MMP.Fourfold.exists_divisorOver_valuation_eq_comap` this tests klt on a log resolution.
* `MMP.Fourfold.exists_isRealKltPair_comparison_eq_of_isNefLogBirationalModel`: klt
  perturbation of a nef log birational model.

## Implementation notes

* The comparison of log discrepancies in `MMP.Intersection.IsDltPair.of_le` is carried out
  directly on `MMP.Intersection.IsLogDiscrepancy`, so it holds over an arbitrary base field.
* In the klt perturbation, `Δ ∼_ℝ B` is spelled out: `Δ - B` is a real linear combination of
  principal divisors. The comparison is preserved on every common resolution comparing the
  adjoints of `(X, B)` and `(Y, B_Y)` (`MMP.Fourfold.IsLogComparisonResolution`), with the same
  morphisms and canonical divisors.
* The general ample representative of `A + e ⌊B⌋` in the source is replaced by the principal
  divisor `c div f` above, scaled by a small real `c > 0`. This needs neither ampleness of
  `A + e ⌊B⌋` nor reducedness of the general member, and it makes the target coefficients at the
  new prime divisors of `Y` positive without computing their orders: only finitely many prime
  divisors of `Y` meet `div f_Y`. The klt property of the real snc boundary is reduced to the
  rational case by comparison with `q ∑ E` for a rational `q < 1`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 2.31, 2.32,
  2.39(1), 5.17
* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori (QDivisor DivisorWithCoeffs DivisorOver)

/-- **Lowering the boundary raises log discrepancies.** If `0 ≤ Δ - Δ'` is `ℚ`-Cartier, every
log discrepancy `a'` of `D` with respect to `Δ'` bounds a log discrepancy `a` of `D` with respect
to `Δ`. -/
private theorem exists_isLogDiscrepancy_le {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Δ Δ' : QDivisor X} (hle : Δ' ≤ Δ) (hq : (Δ - Δ').IsQCartier)
    {n : ℕ} {D : DivisorOver k sX} {a' : ℝ}
    (ha' : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ') D a') :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D a ∧ a ≤ a' := by
  obtain ⟨m₁, hm₁, G, hGE, hGc⟩ := hq.exists_pos
  have hG (P) : (G.coeff P : ℚ) = m₁ * (Δ.coeff P - Δ'.coeff P) := by
    simpa using congrArg (fun F : QDivisor X => F.coeff P) hGE
  have hG0 (P) : 0 ≤ G.coeff P := by
    have : (0 : ℚ) ≤ G.coeff P := hG P ▸ by
      have := hle P; exact mul_nonneg (by first | positivity | exact hm₁.le) (sub_nonneg.mpr this)
    exact_mod_cast this
  obtain ⟨hX, hp, ω, hω, hK, m, r, C, C', hC, hsum, hpb, ha⟩ := ha'
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D.isNormalVariety.1
  have : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨G', hG'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hGc
  have hG'0 : (0 : ℝ) ≤ G'.coeff D.E := by
    exact_mod_cast MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hGc
      (fun P _ => hG0 P) hG' D.E ((D.E.genericPoint_mem_iff _).mp trivial)
  refine ⟨a' - (m₁ : ℝ)⁻¹ * G'.coeff D.E, ⟨hX, hp, ω, hω, hK, m + 1,
    Fin.cons (m₁ : ℝ)⁻¹ r, Fin.cons G C, Fin.cons G' C', Fin.cases (by simpa using hGc) hC,
    fun Γ => ?_, Fin.cases ⟨MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f G, hG'⟩
      hpb, ?_⟩, by linarith [show 0 ≤ (m₁ : ℝ)⁻¹ * G'.coeff D.E by positivity]⟩
  · have hGΓ : (G.coeff Γ : ℝ) = m₁ * ((Δ.coeff Γ : ℝ) - Δ'.coeff Γ) := by
      exact_mod_cast hG Γ
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← hsum Γ,
      QDivisor.coeff_toRDivisor, hGΓ]
    field_simp
    ring
  · rw [ha, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring

/-- For effective `D ≤ D'`, the components of the image of `D` under the linear extension of a
partial map on prime divisors are among those of the image of `D'`. -/
private theorem support_mapPrimeDivisors_subset {X Y : Scheme.{u}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) {D D' : QDivisor X}
    (hD : 0 ≤ D) (hDD' : D ≤ D') :
    (DivisorWithCoeffs.mapPrimeDivisors φ D : QDivisor Y).support ⊆
      (DivisorWithCoeffs.mapPrimeDivisors φ D' : QDivisor Y).support := by
  intro W hW
  rw [Finsupp.mem_support_iff] at hW ⊢
  have h1 := DivisorWithCoeffs.mapPrimeDivisors_nonneg φ hD W
  have h2 := DivisorWithCoeffs.mapPrimeDivisors_nonneg φ (sub_nonneg.mpr hDD') W
  simp only [map_sub, Finsupp.sub_apply, Finsupp.coe_zero, Pi.zero_apply, sub_nonneg] at h1 h2
  exact (lt_of_lt_of_le (lt_of_le_of_ne h1 (Ne.symm hW)) h2).ne'

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **Lowering the boundary of a dlt pair.** If `(X, Δ)` is dlt and `0 ≤ Δ' ≤ Δ` with `Δ - Δ'`
`ℚ`-Cartier, then `(X, Δ')` is dlt. -/
@[mmp "lem_fourfold_dlt_lower_boundary"]
public theorem IsDltPair.of_le {Δ Δ' : QDivisor X} (hΔ : IsDltPair sX Δ) (h0 : 0 ≤ Δ')
    (hle : Δ' ≤ Δ) (hq : (Δ - Δ').IsQCartier) : IsDltPair sX Δ' := by
  obtain ⟨⟨⟨hX, n₀, K, hK, hKq⟩, -, hlc⟩, hc1, Z, hZs, hsnc, hdisc⟩ := hΔ
  obtain ⟨m, hm, hc⟩ := hq
  refine ⟨⟨⟨hX, n₀, K, hK, ?_⟩, h0, fun n D a ha => ?_⟩, fun P => (hle P).trans (hc1 P), Z, hZs,
    hsnc.of_support_subset (support_mapPrimeDivisors_subset _ h0 hle), fun n D hD a ha => ?_⟩
  · convert hKq.add ⟨m, hm, by rw [smul_neg]; exact hc.neg⟩ using 1
    abel
  · obtain ⟨b, hb, hba⟩ := exists_isLogDiscrepancy_le hle ⟨m, hm, hc⟩ ha
    exact (hlc n D b hb).trans hba
  · obtain ⟨b, hb, hba⟩ := exists_isLogDiscrepancy_le hle ⟨m, hm, hc⟩ ha
    exact (hdisc n D hD b hb).trans_le hba

end MMP.Intersection

namespace MMP.Fourfold

section LogResolutionTest

open MMP.Mori TopologicalSpace

private theorem support_sum_single {Y : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- **The centre of a divisorial valuation on a proper model.** Let `π : W ⟶ X` be a proper
dominant morphism of integral schemes and `D` a divisor over `X`. A valuation `ξ` of `k(W)`
restricting to `ord_D` on `k(X)` dominates the local ring of some point of `W`. -/
private theorem exists_dominated_point {k : Type u} [Field k] {X W : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] {sX : X ⟶ Spec (.of k)} (π : W ⟶ X) [IsDominant π] (hπ : IsProper π)
    (D : DivisorOver k sX) (ξ : Valuation W.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap π) = D.valuation) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  have hw : ∀ b : X.presheaf.stalk y,
      ξ (functionFieldMap π (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) := by
    intro b
    simpa only [Valuation.comap_apply] using
      congrArg (fun v => v (algebraMap _ X.functionField b)) h
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk y →+* R :=
    ((functionFieldMap π).comp (algebraMap (X.presheaf.stalk y) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence π := by
    have h : @IsProper _ _ π := hπ
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq π :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk y
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk π,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- **Divisorial valuations over `X` are realized over a proper birational model.** For a proper
dominant morphism `π : W ⟶ X` of integral schemes inducing an isomorphism of function fields, with
`W` a normal variety, every divisor `D` over `X` has the valuation `ord_{D'} ∘ π^*` of some divisor
`D'` over `W`. -/
public theorem exists_divisorOver_valuation_eq_comap {k : Type u} [Field k] {X W : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] {sX : X ⟶ Spec (.of k)} (π : W ⟶ X) [IsDominant π]
    (hπ : IsProper π) (hbij : Function.Bijective (functionFieldMap π))
    (hW : IsNormalVariety k (π ≫ sX)) (D : DivisorOver k sX) :
    ∃ D' : DivisorOver k (π ≫ sX), D.valuation = D'.valuation.comap (functionFieldMap π) := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (π ≫ sX)
  let eπ := functionFieldAlgEquiv sX π hbij
  let ξ := D.valuation.comap (eπ.symm : W.functionField →+* X.functionField)
  have hξ : ξ.comap (functionFieldMap π) = D.valuation := by
    ext t
    change D.valuation (eπ.symm (eπ t)) = D.valuation t
    rw [eπ.symm_apply_apply]
  obtain ⟨x, h1, h2⟩ := exists_dominated_point π hπ D ξ hξ
  haveI : AlgebraicGeometry.IsVariety k (π ≫ sX) := hW.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (π ≫ sX) ξ := by
    haveI := D.isIntegral
    haveI := D.isNormal
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    letI := functionFieldAlgebra (D.f ≫ sX)
    let eD := functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eπ.symm.trans eD, ?_⟩
    ext t
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (π ≫ sX) hdiv x h1 h2
  refine ⟨D'.toDivisorOver, ?_⟩
  rw [← hξ, ← hv]

/-- An exceptional divisor over an integral scheme of dimension `n` forces `2 ≤ n`: its centre
has codimension at least two. -/
private theorem two_le_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} (hX : topologicalKrullDim X = n) (D : DivisorOver k sX)
    (hE : D.IsExceptional) : 2 ≤ n := by
  set η := D.E.genericPoint
  have hdef : RationalMap.DefinedAt (X := D.Y) D.f.toRationalMap η := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have hsub : (IrreducibleCloseds.closureSingleton (D.f η) : Set X) ⊆
      (RationalMap.transform (X := D.Y) D.f.toRationalMap D.E.idealSheaf.support : Set X) := by
    rw [IrreducibleCloseds.coe_closureSingleton]
    refine (Closeds.isClosed _).closure_subset_iff.mpr ?_
    rintro _ rfl
    refine RationalMap.image_subset_transform D.f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨η, ?_, rfl⟩
    exact MMP.Flips.primeDivisor_genericPoint_mem_support D.E
  have hle := le_closedsCodimension_iff.mp ((RationalMap.isExceptional_iff.mp hE) hdef) _ hsub
  have hcodim : codimension (IrreducibleCloseds.closureSingleton (D.f η)) =
      Order.coheight (D.f η) := by
    have h : IrreducibleCloseds.closureSingleton (D.f η) =
        irreducibleSetEquivPoints.symm (D.f η) :=
      IrreducibleCloseds.ext (by
        rw [IrreducibleCloseds.coe_closureSingleton, coe_irreducibleEquivPoints_symm_apply])
    rw [codimension_eq_coheight, h]
    exact Order.coheight_orderIso irreducibleSetEquivPoints.symm (D.f η)
  rw [hcodim] at hle
  have hc : (Order.coheight (D.f η) : WithBot ℕ∞) ≤ n := by
    rw [← hX, topologicalKrullDim,
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (X : Type u)))]
    exact Order.coheight_le_krullDim _
  exact_mod_cast (WithBot.coe_le_coe.mpr hle).trans hc

/-- A variety of dimension `n` that has a divisor over it has `n ≠ 0`. -/
public theorem ne_zero_of_topologicalKrullDim_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sX] {n : ℕ}
    (hX : topologicalKrullDim X = n) (D : DivisorOver k sX) : n ≠ 0 := by
  rintro rfl
  have := D.isIntegral
  haveI : AlgebraicGeometry.IsVariety k (D.f ≫ sX) := D.isNormalVariety.1
  let _ : PartialOrder D.Y := specializationOrder D.Y
  have h1 : Order.krullDim D.Y = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [← hX, MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (D.f ≫ sX)
      D.isBirationalMorphism]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := D.Y))).symm
  have h2 := Order.coheight_le_krullDim D.E.genericPoint
  rw [D.E.coheight_genericPoint, h1] at h2
  exact absurd h2 (by decide)

/-- **The support of the crepant pull-back.** For a log resolution `π : W ⟶ X` of `(X, B)`, every
prime divisor `F` of `W` along which `B_W` has nonzero coefficient lies in
`Ex(π) ∪ π⁻¹(Supp B)`. -/
public theorem support_subset_of_coeff_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) {B : QDivisor X} {π : W ⟶ X} (hW : IsNormalVariety k (π ≫ sX))
    (hbir : IsBirationalMorphism π) {n : ℕ} {K : Divisor X} {BW : QDivisor W}
    (hBW : IsCrepantBoundary sX n K B π hW hbir BW) (F : MMP.Mori.PrimeDivisor W)
    (hF : BW.coeff F ≠ 0) :
    F.support ⊆ ((exceptionalSet π ⊔ (QDivisor.toRDivisor B).supp.preimage π.continuous :
      Closeds W) : Set W) := by
  rw [Closeds.coe_sup]
  by_cases hE : (⟨W, π, hW, hbir, F⟩ : DivisorOver k sX).IsExceptional
  · exact (MMP.Positivity.support_subset_exceptionalSet F hE).trans Set.subset_union_left
  obtain ⟨m, hm, hC, -⟩ := (hBW F).2.2
  obtain ⟨P, hPc, hPd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
    ⟨hX, (hBW F).2.1, ⟨m, by exact_mod_cast hm.ne', hC⟩⟩ _ hE
  have hBP : (QDivisor.toRDivisor B).coeff P ≠ 0 := by
    rw [QDivisor.coeff_toRDivisor, Rat.cast_ne_zero]
    exact fun h => hF (by linarith [(hBW F).eq hPd])
  have hη : π F.genericPoint ∈ (P.support : Set X) := by
    rw [← hPc, DivisorOver.center_eq_closure_genericPoint]
    exact subset_closure rfl
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine Set.Subset.trans ?_ Set.subset_union_right
  exact ((Closeds.isClosed
    ((QDivisor.toRDivisor B).supp.preimage π.continuous)).closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr (DivisorWithCoeffs.support_subset_supp hBP hη)))

/-- **An snc divisor carrying the crepant pull-back.** For a log resolution `π : W ⟶ X` of
`(X, B)`, the support of `B_W` lies in a finite set `S` of prime divisors of `W` with `∑_{E ∈ S} E`
snc, namely the components of `Ex(π) ∪ π⁻¹(Supp B)`. -/
public theorem exists_isSNC_superset_support {k : Type u} [Field k] [PerfectField k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) {B : QDivisor X} {π : W ⟶ X}
    (hπ : MMP.Fourfold.IsLogResolution sX B π) (hW : IsNormalVariety k (π ≫ sX)) {n : ℕ}
    {K : Divisor X} {BW : QDivisor W}
    (hBW : IsCrepantBoundary sX n K B π hW hπ.isBirationalMorphism BW) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor W), BW.support ⊆ S ∧
      DivisorWithCoeffs.IsSNC (π ≫ sX) (∑ E ∈ S, Finsupp.single E (1 : ℤ)) := by
  have hsupp := support_subset_of_coeff_ne_zero hX hW hπ.isBirationalMorphism hBW
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  rcases hπ.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · refine ⟨∅, fun F hF => ?_, by simpa using
      DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hπ.isSmoothScheme⟩
    have h1 := hsupp F (by simpa [DivisorWithCoeffs.coeff_apply] using hF)
    rw [h] at h1
    exact (h1 (MMP.Flips.primeDivisor_genericPoint_mem_support F)).elim
  · refine ⟨s, fun F hF => ?_, hsnc⟩
    have h1 := hsupp F (by simpa [DivisorWithCoeffs.coeff_apply] using hF)
    rw [← hs] at h1
    obtain ⟨E, hE, hηE⟩ :=
      Set.mem_iUnion₂.mp (h1 (MMP.Flips.primeDivisor_genericPoint_mem_support F))
    rwa [MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hηE]

/-- **Subboundaries with snc support have discrepancies at least `-1`.** Let `W` be a smooth
variety of dimension `n` with canonical divisor `K`, and `Δ` a `ℚ`-divisor with every coefficient
at most one, supported on a finite set `S` of prime divisors with `∑_{E ∈ S} E` snc. Then every
divisor over `W` has discrepancy `a(D, W, Δ) ≥ -1`. -/
private theorem neg_one_le_of_isDiscrepancy_of_isSNC {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} (hW : IsNormalVariety k sW) (hsm : IsSmoothScheme sW) {n : ℕ}
    (hn : topologicalKrullDim W = n) {K : Divisor W} (hK : K.IsCanonicalDivisor sW n)
    {Δ : QDivisor W} (S : Finset (MMP.Mori.PrimeDivisor W)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sW (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (hle : ∀ E, Δ.coeff E ≤ 1) {D : DivisorOver k sW} {a : ℚ}
    (ha : IsDiscrepancy sW n K Δ D a) : -1 ≤ a := by
  by_cases hD : D.IsExceptional
  · have h := discrep_le hD ha
    rw [discrep_eq_of_isSNC sW hW hsm (two_le_of_isExceptional hn D hD) hK S hS hsnc
      fun E _ => hle E] at h
    have h1 : (((-1 : ℚ) : ℝ) : EReal) ≤ ((a : ℝ) : EReal) := by
      refine le_trans (le_inf (le_inf
        (le_iInf₂ fun E _ => le_iInf₂ fun F _ => le_iInf₂ fun _ _ => ?_)
        (le_iInf₂ fun E _ => ?_)) (by exact_mod_cast (by norm_num : (-1 : ℝ) ≤ 1))) h
      all_goals rw [EReal.coe_le_coe_iff, Rat.cast_le]
      · linarith [hle E, hle F]
      · linarith [hle E]
    exact_mod_cast EReal.coe_le_coe_iff.mp h1
  · obtain ⟨P, -, hP⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hW, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩ D hD
    linarith [ha.eq hP, hle P]

/-- **Subboundaries with snc support and coefficients `< 1` have discrepancies `> -1`.** Let `W`
be a smooth variety with canonical divisor `K`, and `Δ` a `ℚ`-divisor with every coefficient less
than one, supported on a finite set `S` of prime divisors with `∑_{E ∈ S} E` snc. Then every
divisor over `W` has discrepancy `a(D, W, Δ) > -1`. -/
public theorem neg_one_lt_of_isDiscrepancy_of_isSNC {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} (hW : IsNormalVariety k sW) (hsm : IsSmoothScheme sW) {n : ℕ}
    {K : Divisor W} (hK : K.IsCanonicalDivisor sW n) {Δ : QDivisor W}
    (S : Finset (MMP.Mori.PrimeDivisor W)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sW (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (hlt : ∀ E, Δ.coeff E < 1) {D : DivisorOver k sW} {a : ℚ}
    (ha : IsDiscrepancy sW n K Δ D a) : -1 < a := by
  classical
  by_cases hD : D.IsExceptional
  · have hklt := isKltPair_of_isSNC sW hW hsm hK
      (hsnc.of_support_subset (by rw [support_sum_single]; exact hS)) hlt
    exact_mod_cast EReal.coe_lt_coe_iff.mp (hklt.2.1.trans_le (discrep_le hD ha))
  · obtain ⟨P, -, hP⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hW, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩ D hD
    linarith [ha.eq hP, hlt P]

end LogResolutionTest

section

open MMP.Mori (Divisor QDivisor)

variable {k : Type u} [Field k] {X W : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **Log canonicity is tested on one log resolution.** Let `(X, B)` be a pair, `π : W ⟶ X` a
log resolution of `(X, B)` and `B_W` the crepant pull-back of `(X, B)` on `W`. Then `(X, B)` is
log canonical if and only if every coefficient of `B_W` is at most one. -/
@[mmp "lem_fourfold_lc_log_resolution_test"]
public theorem isLogCanonicalPair_iff_forall_coeff_le_one {B : QDivisor X} (hB : IsPair sX B)
    {π : W ⟶ X} (hπ : IsLogResolution sX B π) (hW : MMP.Mori.IsNormalVariety k (π ≫ sX))
    {n : ℕ} {K : Divisor X} {BW : QDivisor W}
    (hBW : MMP.Mori.IsCrepantBoundary sX n K B π hW hπ.isBirationalMorphism BW) :
    MMP.Intersection.IsLogCanonicalPair sX B ↔ ∀ F, BW.coeff F ≤ 1 := by
  haveI : IsAlgClosed k := hB.isAlgClosed
  haveI : CharZero k := hB.charZero
  have hP : MMP.Mori.IsPair sX B := hB.isPair
  have hbir : MMP.Mori.IsBirationalMorphism π := hπ.isBirationalMorphism
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hW.2
  haveI : IsDominant π := hbir.isDominant
  haveI : AlgebraicGeometry.IsVariety k sX := hP.1.1
  haveI : AlgebraicGeometry.IsVariety k (π ≫ sX) := hW.1
  haveI : CompactSpace W := hW.1.toQuasiCompact.compactSpace_of_compactSpace
  refine ⟨fun hlc F => ?_, fun hle => ⟨hP, hB.nonneg, fun n' D a ha => ?_⟩⟩
  · have h0 := hlc.2.2 n _ _
      (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hBW F) hπ.isProper)
    have h1 : ((BW.coeff F : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
    exact_mod_cast h1
  -- `n' = dim X = dim W` is positive, and `n' = n`
  have hdimX : topologicalKrullDim X = n' :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  have hdimW : topologicalKrullDim W = n' :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX) hbir).symm.trans
      hdimX
  obtain ⟨F₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimW
    (ne_zero_of_topologicalKrullDim_eq hdimX D)
  have hK : K.IsCanonicalDivisor sX n := (hBW F₀).2.1
  obtain rfl : n = n' := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hdimX
  -- `a = 1 + c` for the discrepancy `c = a(D, X, B) = a(D', W, B_W)`
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  obtain ⟨KW, hKW⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sX) hπ.isSmoothScheme hdimW
  obtain ⟨-, hcr⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP π hW hbir hK hKW
    (Or.inl hBW)
  obtain ⟨D', hD'⟩ :=
    exists_divisorOver_valuation_eq_comap π hπ.isProper hbir.functionFieldMap_bijective hW D
  obtain ⟨S, hS, hsnc⟩ := exists_isSNC_superset_support hP.1 hπ hW hBW
  have h : (-1 : ℝ) ≤ c := by
    exact_mod_cast neg_one_le_of_isDiscrepancy_of_isSNC hW hπ.isSmoothScheme hdimW hKW S hS hsnc
      hle ((hcr D' D hD' c).2 hc)
  linarith

end

section KltPerturbation

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori

/-! ### Real snc pairs with coefficients less than one are klt -/

section RealSNC

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A log discrepancy of a klt pair with rational boundary is positive. -/
private theorem pos_of_isLogDiscrepancy_of_isKltPair (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K Δ) {n' : ℕ}
    {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor Δ) D a) : 0 < a := by
  have hP : MMP.Mori.IsPair sX Δ := hklt.1.isPair
  have hK : K.IsCanonicalDivisor sX n := hklt.1.2.1
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  by_cases hE : D.IsExceptional
  · obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
    rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
    have h1 := hklt.2.1.trans_le (discrep_le hE hc)
    have h2 : (-1 : ℝ) < c := by exact_mod_cast (EReal.coe_lt_coe_iff.mp h1)
    linarith
  · obtain ⟨P, hv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
      (DivisorOver.ofPrimeDivisor k hX P)
    have hb := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (show IsProper (𝟙 X) from inferInstance)
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb hv,
      IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX hc]
    have h1 : Δ.coeff P < 1 := roundDown_nonpos_iff.mp hklt.2.2 P
    have : (0 : ℚ) < 1 + -Δ.coeff P := by linarith
    exact_mod_cast this

/-- The log discrepancy of a prime divisor `P` of `X` with respect to an `ℝ`-divisor `B` with
`K + B` `ℝ`-Cartier is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor [CompactSpace X] (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor k hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have hC'P : ∀ i, (C' i).coeff P = (C i).coeff P := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl (hC i) (hC' i)
  have hord : (DivisorOver.ofPrimeDivisor k hX P).ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P ω
  have hsumΓ : ∀ Γ, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, hsumΓ, fun i => ⟨_, hC' i⟩, ?_⟩
  change 1 - B.coeff P = 1 + ((DivisorOver.ofPrimeDivisor k hX P).ordPullback ω : ℝ) -
    ∑ i, r i * ((C' i).coeff P : ℝ)
  simp_rw [hC'P, hord]
  rw [← hsumΓ P]
  ring

open Classical in
/-- Sums over the prime divisors of a finite set, written through `Fin`. -/
private theorem sum_equivFin_mul_single (S : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (Γ : MMP.Mori.PrimeDivisor X) :
    ∑ i : Fin S.card, c (S.equivFin.symm i) *
        (((Finsupp.single (S.equivFin.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ) =
      if Γ ∈ S then c Γ else 0 := by
  rw [Equiv.sum_comp S.equivFin.symm (fun x : S => c x *
    (((Finsupp.single (x : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ))]
  rw [Finset.sum_coe_sort S (fun x => c x * (((Finsupp.single x (1 : ℤ)) Γ : ℤ) : ℝ))]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single Γ]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h'
      exact absurd h h'
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : b ≠ Γ := fun h' => h (h' ▸ hb)
    simp [this]

/-- A real function below `1` is bounded on a finite set by a rational number below `1`. -/
private theorem exists_rat_lt_one_forall_lt {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h1 : ∀ P, f P < 1) : ∃ q : ℚ, (q : ℝ) < 1 ∧ ∀ P ∈ S, f P < q := by
  classical
  obtain ⟨t, ht1, ht⟩ : ∃ t : ℝ, t < 1 ∧ ∀ P ∈ S, f P ≤ t := by
    refine ⟨(insert 0 (S.image f)).max' (Finset.insert_nonempty _ _), ?_, fun P hP =>
      Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP))⟩
    refine (Finset.max'_lt_iff _ _).mpr fun y hy => ?_
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact one_pos
    · obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hy
      exact h1 P
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn ht1
  exact ⟨q, hq1, fun P hP => (ht P hP).trans_lt hq0⟩

open Classical in
/-- The coefficients of `q ∑_{E ∈ S} E`. -/
private theorem coeff_sum_single_rat (S : Finset (MMP.Mori.PrimeDivisor X)) (q : ℚ)
    (Γ : MMP.Mori.PrimeDivisor X) :
    (∑ E ∈ S, Finsupp.single E q : QDivisor X).coeff Γ = if Γ ∈ S then q else 0 := by
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- On a smooth variety, the rational boundary `q ∑_{E ∈ S} E` with `∑_{E ∈ S} E` simple normal
crossing and `q < 1` is klt. -/
private theorem isKltPair_sum_single_of_isSNC (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (S : Finset (MMP.Mori.PrimeDivisor X))
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) {q : ℚ}
    (hq1 : q < 1) : MMP.Mori.IsKltPair sX n K (∑ E ∈ S, Finsupp.single E q : QDivisor X) := by
  classical
  have hsncq : (∑ E ∈ S, Finsupp.single E q : QDivisor X).IsSNC sX :=
    hsnc.of_support_subset fun E hE => by
      rw [support_sum_single]
      by_contra h
      exact (Finsupp.mem_support_iff.mp hE)
        (by rw [← DivisorWithCoeffs.coeff_apply, coeff_sum_single_rat, if_neg h])
  refine MMP.Mori.isKltPair_of_isSNC sX hX hsm hK hsncq fun E => ?_
  rw [coeff_sum_single_rat]
  split_ifs
  · exact hq1
  · exact zero_lt_one

/-- **Real snc pairs are klt.** On a smooth variety `X` over an algebraically closed field of
characteristic zero, an effective `ℝ`-divisor `Δ` whose support lies in a finite set `S` of prime
divisors with `∑_{E ∈ S} E` simple normal crossing, and whose coefficients are less than one, is
a klt boundary. -/
private theorem isRealKltPair_of_isSNC (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {Δ : RDivisor X}
    (S : Finset (MMP.Mori.PrimeDivisor X)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (h0 : ∀ P, 0 ≤ Δ.coeff P) (h1 : ∀ P, Δ.coeff P < 1) : IsRealKltPair sX Δ := by
  classical
  have hΔS : ∀ Γ, Γ ∉ S → Δ.coeff Γ = 0 := fun Γ hΓ =>
    Finsupp.notMem_support_iff.mp fun h => hΓ (hS h)
  -- the presentation `K + ∑_{E ∈ S} c_E E` by Cartier divisors
  let e : Fin S.card → MMP.Mori.PrimeDivisor X := fun i => S.equivFin.symm i
  let C : Fin (S.card + 1) → Divisor X :=
    Fin.cons K (fun i => (Finsupp.single (e i) (1 : ℤ) : Divisor X))
  have hC : ∀ i, (C i).IsCartier := fun i => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  let r : (MMP.Mori.PrimeDivisor X → ℝ) → Fin (S.card + 1) → ℝ :=
    fun c => Fin.cons 1 (fun i => c (e i))
  have hpres : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Γ : MMP.Mori.PrimeDivisor X),
      ∑ i, r c i * ((C i).coeff Γ : ℝ) = K.coeff Γ + if Γ ∈ S then c Γ else 0 := by
    intro c Γ
    rw [Fin.sum_univ_succ]
    simp only [r, C, Fin.cons_zero, Fin.cons_succ, one_mul, DivisorWithCoeffs.coeff_apply]
    rw [sum_equivFin_mul_single S c Γ]
  refine ⟨hX, h1, ⟨n, K, hK, S.card + 1, r Δ.coeff, C, hC, fun Γ => ?_⟩, ?_⟩
  · rw [hpres]
    change ((K.coeff Γ : ℤ) : ℝ) + Δ.coeff Γ = _
    split_ifs with h
    · rfl
    · rw [hΔS Γ h]
  intro n' D a ha
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  have hf : IsProper D.f := ha.2.1
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC i)
  -- the log discrepancy of a boundary supported in `S`, through this presentation
  have hb : ∀ B : RDivisor X, (∀ Γ, Γ ∉ S → B.coeff Γ = 0) →
      MMP.Intersection.IsLogDiscrepancy sX n' B D
        (1 + (D.ordPullback ω : ℝ) - ∑ i, r B.coeff i * ((C' i).coeff D.E : ℝ)) := by
    intro B hB
    refine ⟨hX, hf, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, S.card + 1, r B.coeff, C, C', hC,
      fun Γ => ?_, fun i => ⟨_, hC' i⟩, rfl⟩
    rw [hpres, hω Γ]
    split_ifs with h
    · rfl
    · rw [hB Γ h]
  have haΔ := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha (hb Δ hΔS)
  -- a rational `q < 1` above every coefficient of `Δ`
  obtain ⟨q, hq1, hqt⟩ := exists_rat_lt_one_forall_lt S Δ.coeff h1
  let Δq : QDivisor X := ∑ E ∈ S, Finsupp.single E (q : ℚ)
  have hΔq : ∀ Γ, Δq.coeff Γ = if Γ ∈ S then (q : ℚ) else 0 := coeff_sum_single_rat S q
  have hΔqR : ∀ Γ, Γ ∉ S → (QDivisor.toRDivisor Δq).coeff Γ = 0 := fun Γ hΓ => by
    rw [QDivisor.coeff_toRDivisor, hΔq, if_neg hΓ, Rat.cast_zero]
  have hklt := isKltPair_sum_single_of_isSNC hX hsm hK S hsnc (q := q) (by exact_mod_cast hq1)
  have hposq := pos_of_isLogDiscrepancy_of_isKltPair hX hklt (hb _ hΔqR)
  -- comparison of the two log discrepancies
  rw [haΔ]
  refine lt_of_lt_of_le hposq ?_
  rw [sub_le_sub_iff_left, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [r, Fin.cons_zero, Fin.cons_succ]
  refine add_le_add_right (Finset.sum_le_sum fun i _ => ?_) _
  have hc0 : (0 : ℝ) ≤ ((C' i.succ).coeff D.E : ℝ) := by
    have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hC i.succ)
      (V := ⊤) (fun P _ => ?_) (hC' i.succ) D.E ((D.E.genericPoint_mem_iff _).mp trivial)
    · exact_mod_cast hnn
    · simp only [C, Fin.cons_succ, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> norm_num
  have hle : Δ.coeff (e i) ≤ ((QDivisor.toRDivisor Δq).coeff (e i)) := by
    rw [QDivisor.coeff_toRDivisor, hΔq, if_pos (S.equivFin.symm i).2]
    exact (hqt _ (S.equivFin.symm i).2).le
  exact mul_le_mul_of_nonneg_right hle hc0

end RealSNC

/-! ### Zero schemes of sections of divisorial sheaves -/

section Bertini

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

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance isInvertible_of_isInvertibleModule {Y : Scheme.{u}} (L : Y.Modules)
    [h : Stacks.Ample.IsInvertibleModule Y L] :
    SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L := h

section ZeroScheme

/-- A frame `b` of `𝒪_Y(D)` over `V`, on which `D` has the local equation `φ`, has order
`-d_E` along every prime divisor `E` with generic point in `V`. -/
private theorem valuation_frame_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {D : Divisor Y} {V : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : D.IsLocalEquation V φ)
    (b : D.divisorialSubmodule V) (r : Γ(Y, V)) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.genericPoint ∈ V) (hZ : componentGenericPoint Y E.component ∈ V)
    (hr : ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) E.component =
      (Y.presheaf.germ V _ hZ).hom r * b.1 ⟨E.component, hZ⟩) :
    E.valuation (b.1 ⟨E.component, hZ⟩) = WithZero.exp (-D.coeff E) := by
  have hEV : (E.support ∩ V).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, hE⟩
  have hv := congrArg E.valuation hr
  rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, ← hφ E hEV, map_mul] at hv
  have hne : (Y.presheaf.germ V _ hZ).hom r ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hv
    exact WithZero.coe_ne_zero hv
  have hgerm : (Y.presheaf.germ V _ hZ).hom r =
      E.toComponent.hom ((Y.presheaf.germ V _ hE).hom r) := by
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hE E.specializes_genericPoint]
    rfl
  have hne' : (Y.presheaf.germ V _ hE).hom r ≠ 0 := by
    intro h0
    apply hne
    rw [hgerm, h0, map_zero]
  have h1 : 1 ≤ E.valuation ((Y.presheaf.germ V _ hZ).hom r) := by
    rw [hgerm]
    exact E.one_le_valuation_toComponent hne'
  have hb0 : b.1 ⟨E.component, hZ⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hv
    exact WithZero.coe_ne_zero hv
  refine le_antisymm ?_ ?_
  · rw [hv]
    exact le_mul_of_one_le_left' h1
  · exact ((b.2 E hEV).resolve_left hb0)

/-- **The zero scheme of a section of `𝒪_Y(D)` near a point.** Around every point there is an
affine open `V` on which the ideal of `Z(t)` is generated by a function `a`, and the coefficient
of every prime divisor `E` with generic point in `V` in the divisor of zeros `(t)₀` is the order
of `a` along `E`. -/
private theorem exists_affine_zeroScheme_ideal_eq_span {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (x : Y) :
    ∃ (V : Y.affineOpens) (_ : x ∈ (V : Y.Opens)) (a : Γ(Y, V))
      (ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
        (Y.presheaf.germ V _ hZ).hom a ≠ 0),
      (zeroScheme Y D.divisorialSheaf t).ideal V = Ideal.span {a} ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, E.genericPoint ∈ (V : Y.Opens) →
        (D.zeroDivisor t ht).coeff E =
          E.ord (MMP.Threefold.Resolution.sectionUnit a ha) := by
  obtain ⟨W, hxW, φ, hφ⟩ := hD x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  obtain ⟨g, hxg, hgU, ⟨e⟩⟩ := exists_basicOpen_linearEquiv D.divisorialSheaf ⟨U, hU⟩ x hxU
  let V : Y.affineOpens := ⟨Y.basicOpen g, hU.basicOpen g⟩
  have hVW : (V : Y.Opens) ≤ W := hgU.trans hUW
  set tV := D.divisorialSheaf.presheaf.map (homOfLE (le_top : (V : Y.Opens) ≤ ⊤)).op t
  set a : Γ(Y, V) := e tV with ha_def
  set b : D.divisorialSubmodule V := e.symm 1
  have htV : (tV : D.divisorialSubmodule V) = a • b := by
    change tV = a • e.symm 1
    rw [← map_smul e.symm a 1, smul_eq_mul, mul_one, ha_def, e.symm_apply_apply]
  set u := (Divisor.isUnit_sectionToRationalFunctions ht).unit
  -- the value of `t` at a component through `V`
  have hval : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (u : RationalFunctions Y) Z = (Y.presheaf.germ V _ hZ).hom a * b.1 ⟨Z, hZ⟩ := by
    intro Z hZ
    have := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨Z, hZ⟩) htV
    simp only [Submodule.coe_smul, rationalFunctions_smul_apply] at this
    exact this
  have ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (Y.presheaf.germ V _ hZ).hom a ≠ 0 := by
    intro Z hZ h0
    have hu := (Pi.isUnit_iff.mp u.isUnit) Z
    rw [hval Z hZ, h0, zero_mul] at hu
    exact not_isUnit_zero hu
  refine ⟨V, hxg, a, ha, zeroScheme_ideal_of_trivialization Y D.divisorialSheaf t V e a rfl,
    fun E hE => ?_⟩
  set hZ := E.specializes_genericPoint.mem_open (V : Y.Opens).isOpen hE
  -- the frame `b` has order `-d_E`
  have hr : (hφ.mono hVW).invSection = e (hφ.mono hVW).invSection • e.symm 1 := by
    rw [← map_smul e.symm _ 1, smul_eq_mul, mul_one, e.symm_apply_apply]
  have hr' := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨E.component, hZ⟩) hr
  simp only [Divisor.IsLocalEquation.invSection_apply, Submodule.coe_smul,
    rationalFunctions_smul_apply] at hr'
  have hb := valuation_frame_eq (hφ.mono hVW) b _ E hE hZ hr'
  have hv := congrArg E.valuation (hval E.component hZ)
  rw [PrimeDivisor.valuation_component, map_mul, hb,
    ← MMP.Threefold.Resolution.sectionUnit_apply a ha E.component hZ,
    PrimeDivisor.valuation_component, ← WithZero.exp_add] at hv
  have hv' := WithZero.exp_injective hv
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  change E.ord u + _ = _
  omega

/-- Off the zero scheme of `t`, a prime divisor has coefficient `0` in `(t)₀`. -/
private theorem coeff_zeroDivisor_eq_zero_of_notMem {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.genericPoint ∉ (zeroScheme Y D.divisorialSheaf t).supportSet) :
    (D.zeroDivisor t ht).coeff E = 0 := by
  obtain ⟨V, hxV, a, ha, hI, hc⟩ :=
    exists_affine_zeroScheme_ideal_eq_span D hD t ht E.genericPoint
  rw [hc E hxV]
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hxV, hI, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hE
  exact MMP.Threefold.Resolution.ord_sectionUnit_eq_zero a ha E hxV
    ((Y.mem_basicOpen a _ hxV).mp hE)

end ZeroScheme

section Projective

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **A dense open of `ℙᴺ_k` contains the general points.** For a dense open `U ⊆ ℙᴺ_k` there is
a nonzero (homogeneous) polynomial `Q` with `[c] ∈ U` whenever `Q(c) ≠ 0`: `U` contains a basic
open `D₊(f)`, and a homogeneous component of `f` not vanishing at a point of `D₊(f)` will do. -/
private theorem exists_polynomial_dualPoint_mem {k : Type u} [Field k] {N : ℕ}
    (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens)
    (hU : Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0),
      MvPolynomial.eval c Q ≠ 0 → MMP.Threefold.Bridges.dualPoint c hc ∈ U := by
  classical
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).exists_subset_of_mem_open hp U.isOpen
  have hpf' : f ∉ (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      from p).asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp hpf
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d f ∉
      (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        from p).asHomogeneousIdeal := by
    by_contra h
    push Not at h
    apply hpf'
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => h i
  have hQ0 : MvPolynomial.homogeneousComponent d f ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  refine ⟨_, hQ0, fun c hc hcQ => hfU ?_⟩
  refine (ProjectiveSpectrum.mem_basicOpen _ f
    (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) from
      MMP.Threefold.Bridges.dualPoint c hc)).mpr fun hf => hcQ ?_
  change f ∈ ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal at hf
  have hcore := (HomogeneousIdeal.isHomogeneous ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))).mem_iff.mp hf d
  have hdec : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f d :
      MvPolynomial (Fin (N + 1)) k)) = MvPolynomial.homogeneousComponent d f :=
    MvPolynomial.decomposition.decompose'_apply f d
  rw [hdec] at hcore
  exact RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le _ _ hcore)

end Projective

/-! ### Bertini's theorem in Weil-divisor form -/

section WeilBertini

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

attribute [local instance] globalSectionsModule

open Classical in
/-- **Bertini's theorem for snc divisors, in Weil-divisor form.** On a smooth variety `Y` over an
algebraically closed field of characteristic zero, let `D` be a Cartier divisor and
`t₀, …, t_N` global sections of `𝒪_Y(D)` such that every point lies in the nonvanishing open of
some combination of them, and let `∑_{E ∈ S} E` be snc. Then some nonzero section `τ` has its
divisor of zeros supported on a finite set `T` of prime divisors disjoint from `S` with
`∑_{E ∈ T ∪ S} E` snc. -/
private theorem exists_zeroDivisor_support_subset_isSNC {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [IsSmoothVariety k (Y ↘ Spec (.of k))] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier) {N : ℕ}
    (s : Fin (N + 1) → Γ(D.divisorialSheaf, ⊤))
    (hs' : haveI := hD.isInvertibleModule_divisorialSheaf
      ∀ y : Y, ∃ i, y ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf (s i))
    (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    ∃ (τ : D.divisorialSubmodule ⊤) (hτ : τ ≠ 0) (T : Finset (MMP.Mori.PrimeDivisor Y)),
      (∀ E, (D.zeroDivisor τ hτ).coeff E ≠ 0 → E ∈ T) ∧ Disjoint T S ∧
      DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) := by
  haveI hL := hD.isInvertibleModule_divisorialSheaf
  haveI : TopologicalSpace.NoetherianSpace Y :=
    MMP.Resolution.Aux.noetherianSpace_of_finiteType (Y ↘ Spec (.of k))
  have hs : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s c) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, hy⟩ := hs' y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single i 1, ?_⟩
    have h1 : MMP.Threefold.Bridges.systemSection (k := k) s (Pi.single i 1) = s i := by
      rw [MMP.Threefold.Bridges.systemSection_apply,
        Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp only [Pi.single_eq_same]
      exact one_smul k _
    rw [h1]
    exact hy
  obtain ⟨U, hU, hUc⟩ := MMP.Threefold.Bridges.exists_dense_open_isSNC_zeroScheme_add s hs _ hS
  obtain ⟨Q₁, hQ₁0, hQ₁⟩ := exists_polynomial_dualPoint_mem U hU
  -- some member of the system is nonzero
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨c₀, hc₀⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hs.symm ▸ trivial : y ∈ ⨆ c : Fin (N + 1) → k,
    Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s c))
  have hne : (MMP.Threefold.Bridges.systemSection s c₀ : D.divisorialSubmodule ⊤) ≠ 0 := by
    intro h0
    have h0' : MMP.Threefold.Bridges.systemSection s c₀ = 0 := h0
    rw [h0'] at hc₀
    change y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf 0 at hc₀
    rw [Stacks.Ample.nonvanishingLocus_zero] at hc₀
    exact hc₀
  have hsys : ∀ c : Fin (N + 1) → k, (MMP.Threefold.Bridges.systemSection (k := k) s c :
      D.divisorialSubmodule ⊤) = ∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) •
        (s i : D.divisorialSubmodule ⊤) := by
    intro c
    rw [MMP.Threefold.Bridges.systemSection_apply]
    rfl
  obtain ⟨j, hj⟩ : ∃ j, (s j : D.divisorialSubmodule ⊤) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [hsys]
    exact Finset.sum_eq_zero fun i _ => by rw [h i, smul_zero]
  obtain ⟨Q₂, hQ₂0, hQ₂⟩ := exists_polynomial_sum_smul_ne_zero (Y ↘ Spec (.of k))
    (fun i => (s i : D.divisorialSubmodule ⊤)) j hj
  obtain ⟨c, hc⟩ : ∃ c : Fin (N + 1) → k, MvPolynomial.eval c (Q₁ * Q₂) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hQ₁0 hQ₂0 (MvPolynomial.funext fun c => by rw [h c, map_zero])
  rw [map_mul] at hc
  have hτ : (MMP.Threefold.Bridges.systemSection (k := k) s c : D.divisorialSubmodule ⊤) ≠ 0 := by
    rw [hsys]
    exact hQ₂ c (right_ne_zero_of_mul hc)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hτ (by rw [hsys]; simp)
  obtain ⟨-, T, hTcomp, hTS, hsnc⟩ := hUc c hc0 (hQ₁ c hc0 (left_ne_zero_of_mul hc))
  rw [support_sum_single] at hTS hsnc
  refine ⟨_, hτ, T, fun E hE => ?_, hTS, hsnc⟩
  by_contra hET
  apply hE
  by_cases hEZ : E.genericPoint ∈ (zeroScheme Y D.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection (k := k) s c)).supportSet
  · exfalso
    obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf
      (zeroScheme Y D.divisorialSheaf
        (MMP.Threefold.Bridges.systemSection (k := k) s c)).support.isClosed
    obtain ⟨W, hW, hEW⟩ := Set.mem_sUnion.mp (hcov hEZ)
    obtain ⟨E', hE'T, hE'W⟩ := (hTcomp W).mp hW
    exact hET (by
      rwa [MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support (E := E) (E' := E') (hE'W ▸ hEW)])
  · exact coeff_zeroDivisor_eq_zero_of_notMem D hD _ hτ E hEZ

end WeilBertini

end Bertini

/-! ### Global generation of `𝒪_X(n A + F)` -/

section GlobalGeneration

open Stacks.Ample Stacks.RelativeVeryAmple

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- `𝒪_X(n H + F) ≅ 𝒪_X(F) ⊗ 𝒪_X(H)^{⊗ n}` for Cartier divisors `H` and `F`. -/
private theorem nonempty_divisorialSheaf_nsmul_add_iso {H F : Divisor X} (hH : H.IsCartier)
    (hF : F.IsCartier) (n : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    Nonempty ((n • H + F).divisorialSheaf ≅
      tensorModules X F.divisorialSheaf (tensorPowModule X H.divisorialSheaf (n : ℤ))) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  induction n with
  | zero =>
    exact ⟨eqToIso (by rw [zero_smul, zero_add]) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor X _).symm ≪≫
      tensorModulesMapIso X (Iso.refl _) (tensorPowModuleZeroIso X _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [succ_nsmul, add_right_comm]) ≪≫
      (((hH.nsmul n).add hF).divisorialSheafTensorIso hH).symm ≪≫
      tensorModulesMapIso X e (tensorPowModuleOneIso X _).symm ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
      tensorModulesMapIso X (Iso.refl _)
        (tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫ tensorPowModuleCongr X _ (by push_cast; ring))⟩

/-- **Serre generation for `𝒪_X(n H + F)`.** If `𝒪_X(H)` is ample and `F` is Cartier, then for
some `n` finitely many global sections `s₀, …, s_N` of `𝒪_X(n H + F)` have nonvanishing opens
covering `X`. -/
private theorem exists_forall_mem_nonvanishingOpen [IsIntegral X] {H F : Divisor X}
    (hH : H.IsCartier) (hF : F.IsCartier)
    (hamp : haveI := hH.isInvertibleModule_divisorialSheaf
      Stacks.Ample.IsAmple X H.divisorialSheaf) :
    ∃ (n N : ℕ) (s : Fin (N + 1) → Γ((n • H + F).divisorialSheaf, ⊤)),
      haveI := ((hH.nsmul n).add hF).isInvertibleModule_divisorialSheaf
      ∀ x : X, ∃ i, x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X (n • H + F).divisorialSheaf
        (s i) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  haveI := hF.isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsFiniteType.{u, u, u} F.divisorialSheaf :=
    Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hamp).2 F.divisorialSheaf inferInstance inferInstance
  set n : ℕ := n₀.toNat
  obtain ⟨σ, hσ⟩ := hn₀ (n : ℤ) (by omega)
  haveI := ((hH.nsmul n).add hF).isInvertibleModule_divisorialSheaf
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory X
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso X F.divisorialSheaf
    (tensorPowModule X H.divisorialSheaf (n : ℤ))
  obtain ⟨e⟩ := nonempty_divisorialSheaf_nsmul_add_iso hH hF n
  let p := i.hom ≫ e.inv
  haveI : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ p :=
    @IsIso.epi_of_iso _ _ _ _ p inferInstance
  let σ' := σ.ofEpi p
  haveI : Finite σ'.I := hσ
  haveI : Fintype σ'.I := Fintype.ofFinite _
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨i₀, -⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ σ' x₀
  have hcard : 0 < Fintype.card σ'.I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  let eI : σ'.I ≃ Fin (Fintype.card σ'.I - 1 + 1) :=
    Fintype.equivFinOfCardEq (by omega)
  refine ⟨n, Fintype.card σ'.I - 1, fun j => (σ'.s (eI.symm j)).eval (Opposite.op ⊤),
    fun x => ?_⟩
  obtain ⟨j, hj⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ σ' x
  refine ⟨eI j, ?_⟩
  have hx : x ∈ (Stacks.SheafOfModules.nonvanishingOpen _ (σ'.s j) : Set X) := hj
  rw [Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X _ (σ'.s j)] at hx
  simp only [Equiv.symm_apply_apply]
  exact hx

end GlobalGeneration

/-! ### Lowering the reduced boundary by a general member -/

section LowerBoundary

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

open Classical in
/-- **A principal divisor lowering the reduced boundary.** Let `X` be a smooth variety over an
algebraically closed field of characteristic zero, `B` an `ℝ`-divisor with snc support, and `A`
an effective ample `ℚ`-divisor with `A ≤ B` and no component in `⌊B⌋`. There is a rational
function `f` whose divisor is negative along every component of `B` with coefficient one,
nonnegative off the support of `B`, and supported on `T ∪ Supp B` for a finite set `T` of prime
divisors with `∑_{E ∈ T ∪ Supp B} E` snc: `div f = (τ)₀ - (n D_A + ⌊B⌋)` for `D_A` a Cartier
multiple of `A` and `τ` a general section of `𝒪_X(n D_A + ⌊B⌋)`, globally generated for some
`n` by Serre's theorem. -/
private theorem exists_unit_principalDivisor (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {B : RDivisor X} (hBsnc : DivisorWithCoeffs.IsSNC sX B)
    (A : QDivisor X) (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAB : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P) (hAfloor : ∀ P, A.coeff P ≠ 0 → B.coeff P < 1) :
    ∃ (f : (RationalFunctions X)ˣ) (T : Finset (MMP.Mori.PrimeDivisor X)),
      (∀ P, B.coeff P = 1 → (principalDivisor f).coeff P < 0) ∧
      (∀ P, B.coeff P = 0 → 0 ≤ (principalDivisor f).coeff P) ∧
      (∀ P, (principalDivisor f).coeff P ≠ 0 → P ∈ T ∪ B.support) ∧
      DivisorWithCoeffs.IsSNC sX (∑ E ∈ T ∪ B.support, Finsupp.single E (1 : ℤ)) := by
  obtain ⟨m, hm, DA, hDA, hDAc, hamp⟩ := hA
  let S : Divisor X :=
    ∑ P ∈ B.support.filter (fun P => B.coeff P = 1), Finsupp.single P (1 : ℤ)
  have hSc : S.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm S
  obtain ⟨n, N, s, hs⟩ := exists_forall_mem_nonvanishingOpen hDAc hSc hamp
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI : IsSmoothVariety k (X ↘ Spec (.of k)) :=
    (isSmoothVariety_iff k _).mpr ⟨hX.1, hsm.smooth⟩
  have hMc : (n • DA + S).IsCartier := (hDAc.nsmul n).add hSc
  have hS : DivisorWithCoeffs.IsSNC (X ↘ Spec (.of k))
      (∑ E ∈ B.support, Finsupp.single E (1 : ℤ)) :=
    hBsnc.of_support_subset (by rw [support_sum_single])
  obtain ⟨τ, hτ, T, hT, hTS, hsnc⟩ :=
    exists_zeroDivisor_support_subset_isSNC (k := k) (n • DA + S) hMc s hs B.support hS
  set f := (Divisor.isUnit_sectionToRationalFunctions hτ).unit
  have hzero : ∀ P, ((n • DA + S).zeroDivisor τ hτ).coeff P =
      (principalDivisor f).coeff P + (n • DA + S).coeff P :=
    fun P => rfl
  have hznn : ∀ P, 0 ≤ ((n • DA + S).zeroDivisor τ hτ).coeff P := fun P =>
    Divisor.zeroDivisor_nonneg (n • DA + S) τ hτ P
  have hDAP : ∀ P, ((DA.coeff P : ℤ) : ℚ) = m * A.coeff P := fun P => by
    simpa using congrArg (fun G : QDivisor X => G.coeff P) hDA
  have hSP : ∀ P, S.coeff P = if B.coeff P = 1 then 1 else 0 := fun P => by
    by_cases h : B.coeff P = 1
    · rw [if_pos h]
      rw [DivisorWithCoeffs.coeff_apply] at h
      simp only [S, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply,
        Finset.sum_ite_eq']
      rw [if_pos]
      exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [h]; exact one_ne_zero), h⟩
    · rw [if_neg h]
      rw [DivisorWithCoeffs.coeff_apply] at h
      simp only [S, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply,
        Finset.sum_ite_eq']
      rw [if_neg]
      exact fun h' => h (Finset.mem_filter.mp h').2
  have hMP : ∀ P, (n • DA + S).coeff P = n * DA.coeff P + S.coeff P := fun P => by
    simp [DivisorWithCoeffs.coeff_apply]
  -- the coefficient of `D_A` vanishes where `A` does
  have hDA0 : ∀ P, A.coeff P = 0 → DA.coeff P = 0 := fun P hP => by
    have := hDAP P
    rw [hP, mul_zero] at this
    exact_mod_cast this
  refine ⟨f, T, fun P hP => ?_, fun P hP => ?_, fun P hP => ?_, hsnc⟩
  · -- along a reduced component the divisor of zeros vanishes and `M` has coefficient one
    have hPB : P ∈ B.support := Finsupp.mem_support_iff.mpr (by
      rw [← DivisorWithCoeffs.coeff_apply, hP]; exact one_ne_zero)
    have hPT : P ∉ T := fun h => Finset.disjoint_left.mp hTS h hPB
    have hz : ((n • DA + S).zeroDivisor τ hτ).coeff P = 0 := by
      by_contra h
      exact hPT (hT P h)
    have hA0P : A.coeff P = 0 := by
      by_contra h
      exact absurd (hAfloor P h) (by rw [hP]; exact lt_irrefl 1)
    have := hzero P
    rw [hz, hMP, hDA0 P hA0P, hSP, if_pos hP] at this
    omega
  · have hA0P : A.coeff P = 0 := le_antisymm (by exact_mod_cast (hAB P).trans hP.le) (hA0 P)
    have h1 : B.coeff P ≠ 1 := by rw [hP]; exact zero_ne_one
    have := hzero P
    rw [hMP, hDA0 P hA0P, hSP, if_neg h1] at this
    have := hznn P
    omega
  · by_cases hPB : P ∈ B.support
    · exact Finset.mem_union_right _ hPB
    · have hB0 : B.coeff P = 0 := by
        rw [DivisorWithCoeffs.coeff_apply]; exact Finsupp.notMem_support_iff.mp hPB
      have hA0P : A.coeff P = 0 :=
        le_antisymm (by exact_mod_cast (hAB P).trans hB0.le) (hA0 P)
      have h1 : B.coeff P ≠ 1 := by rw [hB0]; exact zero_ne_one
      have := hzero P
      rw [hMP, hDA0 P hA0P, hSP, if_neg h1] at this
      refine Finset.mem_union_left _ (hT P ?_)
      omega

/-- `b + c d → b` as `c → 0⁺`. -/
private theorem tendsto_add_mul (b d : ℝ) :
    Filter.Tendsto (fun c : ℝ => b + c * d) (nhdsWithin 0 (Set.Ioi 0)) (nhds b) :=
  ((continuous_const.add (continuous_id.mul continuous_const)).tendsto' 0 b (by simp)).mono_left
    nhdsWithin_le_nhds

/-- For small `c > 0`, `b + c d ≥ 0` when `b ≥ 0` and `d ≥ 0` in case `b = 0`. -/
private theorem eventually_nonneg_add_mul {b d : ℝ} (hb : 0 ≤ b) (hd : b = 0 → 0 ≤ d) :
    ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ b + c * d := by
  rcases hb.lt_or_eq with h | h
  · exact ((tendsto_add_mul b d).eventually_const_lt h).mono fun c hc => hc.le
  · filter_upwards [self_mem_nhdsWithin] with c (hc : 0 < c)
    rw [← h, zero_add]
    exact mul_nonneg hc.le (hd h.symm)

/-- For small `c > 0`, `b + c d < 1` when `b ≤ 1` and `d < 0` in case `b = 1`. -/
private theorem eventually_add_mul_lt_one {b d : ℝ} (hb : b ≤ 1) (hd : b = 1 → d < 0) :
    ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0), b + c * d < 1 := by
  rcases hb.lt_or_eq with h | h
  · exact (tendsto_add_mul b d).eventually_lt_const h
  · filter_upwards [self_mem_nhdsWithin] with c (hc : 0 < c)
    nlinarith [hd h]

/-- The coefficients of `B + c div f`. -/
private theorem coeff_add_smul_principalDivisor (B : RDivisor X) (c : ℝ)
    (f : (RationalFunctions X)ˣ) (P : MMP.Mori.PrimeDivisor X) :
    (B + c • Divisor.toRDivisor (principalDivisor f)).coeff P =
      B.coeff P + c * ((principalDivisor f).coeff P : ℝ) := by
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]

open Classical in
/-- **The lowered boundary is klt.** In the situation of
`exists_unit_principalDivisor`, for every sufficiently small `c > 0` the `ℝ`-divisor
`B + c div f` is an effective klt boundary: it has snc support in `T ∪ Supp B`, and its
coefficients lie in `[0, 1)`, those of the components of `⌊B⌋` being lowered below one. -/
private theorem eventually_isRealKltPair_add_smul (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P) (hB1 : ∀ P, B.coeff P ≤ 1)
    (f : (RationalFunctions X)ˣ) (T : Finset (MMP.Mori.PrimeDivisor X))
    (hf1 : ∀ P, B.coeff P = 1 → (principalDivisor f).coeff P < 0)
    (hf0 : ∀ P, B.coeff P = 0 → 0 ≤ (principalDivisor f).coeff P)
    (hfT : ∀ P, (principalDivisor f).coeff P ≠ 0 → P ∈ T ∪ B.support)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ T ∪ B.support, Finsupp.single E (1 : ℤ))) :
    ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∀ P, 0 ≤ (B + c • Divisor.toRDivisor (principalDivisor f)).coeff P) ∧
      IsRealKltPair sX (B + c • Divisor.toRDivisor (principalDivisor f)) := by
  have hP : ∀ P, ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ B.coeff P + c * ((principalDivisor f).coeff P : ℝ) ∧
        B.coeff P + c * ((principalDivisor f).coeff P : ℝ) < 1 := fun P =>
    (eventually_nonneg_add_mul (hB0 P) fun h => by exact_mod_cast hf0 P h).and
      (eventually_add_mul_lt_one (hB1 P) fun h => by exact_mod_cast hf1 P h)
  have hall := (Filter.eventually_all_finset (T ∪ B.support)).mpr fun P _ => hP P
  filter_upwards [hall] with c hc
  have hout : ∀ P, P ∉ T ∪ B.support →
      B.coeff P + c * ((principalDivisor f).coeff P : ℝ) = 0 := fun P hP' => by
    have hB : B.coeff P = 0 := by
      rw [DivisorWithCoeffs.coeff_apply]
      exact Finsupp.notMem_support_iff.mp fun h => hP' (Finset.mem_union_right _ h)
    have hdP : ((principalDivisor f).coeff P : ℝ) = 0 := by
      by_contra h
      exact hP' (hfT P (by exact_mod_cast h))
    rw [hB, hdP, mul_zero, add_zero]
  have h0 : ∀ P, 0 ≤ (B + c • Divisor.toRDivisor (principalDivisor f)).coeff P := fun P => by
    rw [coeff_add_smul_principalDivisor]
    by_cases hPF : P ∈ T ∪ B.support
    · exact (hc P hPF).1
    · exact (hout P hPF).ge
  have h1 : ∀ P, (B + c • Divisor.toRDivisor (principalDivisor f)).coeff P < 1 := fun P => by
    rw [coeff_add_smul_principalDivisor]
    by_cases hPF : P ∈ T ∪ B.support
    · exact (hc P hPF).2
    · rw [hout P hPF]
      exact one_pos
  refine ⟨h0, isRealKltPair_of_isSNC hX hsm hK (T ∪ B.support) (fun P hP' => ?_) hsnc h0 h1⟩
  by_contra hPF
  apply Finsupp.mem_support_iff.mp hP'
  rw [← DivisorWithCoeffs.coeff_apply, coeff_add_smul_principalDivisor]
  exact hout P hPF

end LowerBoundary

/-! ### Transporting a rational function along the birational map -/

section Transport

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- If a dominant morphism `a : A ⟶ X` of integral schemes is lifted, over the domain `U` of a
partial map `g : X ⇢ Y`, by `p' : A ⟶ Y` (`p' = g ∘ a` on `a⁻¹ U`), then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  have hx : genericPoint X ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  have hA : genericPoint A ∈ a ⁻¹ᵁ g.domain := by
    change a (genericPoint A) ∈ g.domain
    rw [map_genericPoint_of_isDominant]
    exact hx
  rw [partialMap_fromFunctionField_eq g hx]
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint A) hA ≫ (a ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk a
  rw [← Category.assoc, c1, Category.assoc, ← hcomm, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p := by
    refine h1.trans ?_
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of `φ : X ⤏ Y` (with `h` inverse to `p`
and `q = φ ∘ h`), `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField_of_isInverse {X Y W : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y)
    (h : X.RationalMap W) [IsDominant p] (hinv : RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨e, he1, he2⟩ := hinv
  rw [← hcomp, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_symm p e he1]

/-- A ring map `θ : k(Y) → k(X)` inducing `m : Spec k(X) ⟶ Y` at the generic point satisfies
`p^* ∘ θ = q^*` for every pair `p : A ⟶ X`, `q : A ⟶ Y` along which `m` is `q`. -/
private theorem functionFieldMap_comp_eq_of_specMap {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral A] (m : Spec X.functionField ⟶ Y)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m)
    (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p] [IsDominant q]
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    (functionFieldMap p).comp θ = functionFieldMap q := by
  have key : Spec.map (CommRingCat.ofHom ((functionFieldMap p).comp θ)) ≫
      Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom (functionFieldMap q)) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hθ, hA,
      functionFieldMap_fromSpecStalk q]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp key))

/-- A ring map inducing `m : Spec k(X) ⟶ Y`, read off a pair `p : A ⟶ X`, `q : A ⟶ Y` of
morphisms inducing isomorphisms of function fields along which `m` is `q`. -/
private theorem exists_ringHom_of_specMap {X Y A : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral A] (m : Spec X.functionField ⟶ Y) (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p]
    [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hq : Function.Bijective (functionFieldMap q))
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, Function.Bijective θ ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q :=
    RingHom.ext fun s => ep.apply_symm_apply _
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  refine ⟨θ, ep.symm.bijective.comp hq, ?_⟩
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hA, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
  exact functionFieldMap_fromSpecStalk q

/-- **The comparison of function fields on every common resolution.** If
`θ : k(Y) → k(X)` induces `φ` at the generic point, then `p^* ∘ θ = q^*` on every common
resolution `p : W ⟶ X`, `q : W ⟶ Y` of `φ`. -/
private theorem functionFieldMap_comp_eq {X Y W : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral W] (φ : X.RationalMap Y) (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) [IsDominant p] [IsDominant q]
    (hinv : RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ) :
    (functionFieldMap p).comp θ = functionFieldMap q :=
  functionFieldMap_comp_eq_of_specMap _ θ hθ p q
    (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp)

/-- **Inverse birational maps induce inverse maps of function fields.** If `θ` induces `φ` and
`θ'` induces `ψ` at the generic points, and `ψ` is inverse to `φ`, then `θ' ∘ θ = id`. -/
private theorem comp_eq_id_of_isInverse {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {φ : X.RationalMap Y} {ψ : Y.RationalMap X} (hinv : MMP.Mori.RationalMap.IsInverse φ ψ)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (θ' : X.functionField →+* Y.functionField)
    (hθ' : Spec.map (CommRingCat.ofHom θ') ≫ X.fromSpecStalk (genericPoint X) =
      ψ.fromFunctionField) :
    θ'.comp θ = RingHom.id _ := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hy : genericPoint Y ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have hφ : φ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hx]
    rfl
  have hψ : ψ.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint Y) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hy]
    rfl
  have c1 : Spec.map (CommRingCat.ofHom θ') ≫ e.source.fromSpecStalkOfMem (genericPoint X) hx =
      e.target.fromSpecStalkOfMem (genericPoint Y) hy ≫ e.iso.inv := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hθ', hψ,
      Category.assoc]
  have key : Spec.map (CommRingCat.ofHom (θ'.comp θ)) ≫ Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hθ, hφ, ← Category.assoc, c1,
      Category.assoc, Iso.inv_hom_id_assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    change _ = Spec.map (𝟙 _) ≫ _
    rw [Spec.map_id, Category.id_comp]
  have := Spec.map_injective ((cancel_mono _).mp key)
  exact congrArg CommRingCat.Hom.hom this

/-- Every nonzero element of the function field of an integral scheme is the value at the
generic point of a unit of `K(X)`. -/
private theorem exists_unit_evalFF_eq {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (Z : irreducibleComponents X) {t : X.functionField} (ht : t ≠ 0) :
    ∃ u : (RationalFunctions X)ˣ,
      MMP.Threefold.Mori.Helpers.evalFF Z (u : RationalFunctions X) = t := by
  classical
  haveI := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  have hgen : componentGenericPoint X Z = genericPoint X :=
    MMP.Fourfold.componentGenericPoint_eq_genericPoint Z
  have hsp : genericPoint X ⤳ componentGenericPoint X Z :=
    (genericPoint_spec X).specializes trivial
  have hbij : Function.Bijective (X.presheaf.stalkSpecializes hsp).hom := by
    revert hsp
    rw [hgen]
    intro hsp
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Function.bijective_id
  obtain ⟨a, ha⟩ := hbij.2 t
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact ht ha.symm
  let r : RationalFunctions X := Function.update 1 Z a
  have hrZ : r Z = a := Function.update_self _ _ _
  have hr : IsUnit r := by
    refine Pi.isUnit_iff.mpr fun Z' => ?_
    obtain rfl : Z = Z' := Subsingleton.elim _ _
    rw [hrZ]
    exact isUnit_of_ne_zero_stalk Z ha0
  refine ⟨hr.unit, ?_⟩
  change (X.presheaf.stalkSpecializes hsp).hom ((hr.unit : RationalFunctions X) Z) = t
  rw [hr.unit_spec, hrZ, ha]

/-- **Pull-backs of corresponding principal divisors agree.** If `θ : k(Y) → k(X)` induces `φ`
and sends the value of `f_Y` to that of `f`, then on every common resolution `p : W ⟶ X`,
`q : W ⟶ Y` of `φ` the pull-backs `p^* div f` and `q^* div f_Y` are equal. -/
private theorem isPullback_principalDivisor_eq {X Y W : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral W] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsLocallyNoetherian W] [IsNormal W]
    (φ : X.RationalMap Y) (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (f : (RationalFunctions X)ˣ) (fY : (RationalFunctions Y)ˣ) (Zx : irreducibleComponents X)
    (Zy : irreducibleComponents Y)
    (hf : θ (MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y)) =
      MMP.Threefold.Mori.Helpers.evalFF Zx (f : RationalFunctions X))
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) [IsDominant p] [IsDominant q]
    (hinv : RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ)
    {Lp Lq : Divisor W}
    (hLp : (principalDivisor f).IsPullback p
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p _) Lp)
    (hLq : (principalDivisor fY).IsPullback q
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp q _) Lq) :
    Lp = Lq := by
  refine Finsupp.ext fun E => ?_
  change Lp.coeff E = Lq.coeff E
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hLp
      (Divisor.isLocalEquation_principalDivisor f ⊤) E trivial Zx,
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hLq
      (Divisor.isLocalEquation_principalDivisor fY ⊤) E trivial Zy,
    ← functionFieldMap_comp_eq φ θ hθ p q h hinv hcomp, RingHom.comp_apply, hf]

end Transport

/-! ### Strict transforms on a common resolution -/

section StrictTransform

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
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

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      exact MMP.Flips.primeDivisor_genericPoint_mem_support P
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
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply]
    exact MMP.Flips.primeDivisor_genericPoint_mem_support P

private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- **The strict transform on a resolution.** Let `p : W ⟶ X` be a proper birational morphism
of normal varieties with inverse `h`, and `P` a prime divisor of `X`. Then `h` is defined at the
codimension-one point `η_P` (properness of `p`) by some `h'`, and `h'(η_P)` is the generic point
of a prime divisor `E` of `W` with `p(η_E) = η_P`, along which `p` induces an isomorphism of local
rings. -/
private theorem exists_strictTransform {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (p : W ⟶ X)
    (h : X.RationalMap W) [IsProper p] (hWnp : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hinv : RationalMap.IsInverse p.toRationalMap h)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ (E : MMP.Mori.PrimeDivisor W) (h' : X.PartialMap W) (hP : P.genericPoint ∈ h'.domain),
      h'.toRationalMap = h ∧ E.genericPoint = h'.hom ⟨P.genericPoint, hP⟩ ∧
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) := by
  have := hX.1
  have := hWnp.1
  have : IsDominant p := hpb.isDominant
  have := isSeparated_toTerminal sX
  have : IsSeparated p := IsSeparated.of_comp p sX
  obtain ⟨E, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hWnp hpb P
  obtain ⟨e, he1, he2⟩ := id hinv
  have hhp : h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
    rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨h', hh'P, hh'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhp
      P.coheight_genericPoint.le)
  have hpw : p (h'.hom ⟨P.genericPoint, hh'P⟩) = P.genericPoint :=
    apply_hom_eq_of_isInverse p e he1 h' (hh'.trans he2.symm) hh'P
  haveI : ValuationRing (X.presheaf.stalk P.genericPoint) := by
    haveI := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  haveI : ValuationRing (X.presheaf.stalk (p E.genericPoint)) := by rw [heq]; infer_instance
  haveI : ValuationRing (X.presheaf.stalk (p (h'.hom ⟨P.genericPoint, hh'P⟩))) := by
    rw [hpw]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing p hpb.functionFieldMap_bijective
    (h'.hom ⟨P.genericPoint, hh'P⟩)
  exact ⟨E, h', hh'P, hh', MMP.Positivity.eq_of_isIso_stalkMap p hpb.functionFieldMap_bijective
    (hpw.trans heq.symm), heq, hiso⟩

/-- **Strict transforms on a common resolution.** Let `p : W ⟶ X`, `q : W ⟶ Y` be proper
birational morphisms of normal varieties with `q ∘ p⁻¹ = φ`. If the birational transform of a
prime divisor `P` of `X` under `φ` is the prime divisor `F` of `Y`, then the strict transform `E`
of `P` on `W` maps generically onto both, by isomorphisms of local rings: `p(η_E) = η_P` and
`q(η_E) = η_F`. -/
private theorem exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some {k : Type u}
    [Field k] {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) {φ : X.RationalMap Y}
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) [IsProper p] [IsProper q]
    (hWnp : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hinv : RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (hPF : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F) :
    ∃ E : MMP.Mori.PrimeDivisor W, p E.genericPoint = P.genericPoint ∧
      IsIso (p.stalkMap E.genericPoint) ∧ q E.genericPoint = F.genericPoint ∧
      IsIso (q.stalkMap E.genericPoint) := by
  have := hY.1
  have : IsDominant q := hqb.isDominant
  have := isSeparated_toTerminal sY
  obtain ⟨E, h', hh'P, hh', hwE, heq, hiso⟩ := exists_strictTransform hX p h hWnp hpb hinv P
  -- `q ∘ h'` represents `φ`, so `q(η_E) = η_F`
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hPF
  obtain ⟨g', hg'P, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hqE : q E.genericPoint = F.genericPoint := by
    rw [hwE, genericPoint_eq_of_transformPrimeDivisor_eq_some hPF g' hg' hg'P]
    have hrat : (h'.compHom q).toRationalMap = g'.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap, hh', hcomp, hg']
    exact MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hrat hh'P hg'P
  haveI : ValuationRing (Y.presheaf.stalk F.genericPoint) := by
    haveI := F.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing F.localRing)
  haveI : ValuationRing (Y.presheaf.stalk (q E.genericPoint)) := by rw [hqE]; infer_instance
  exact ⟨E, heq, hiso, hqE,
    MMP.Positivity.isIso_stalkMap_of_valuationRing q hqb.functionFieldMap_bijective _⟩

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
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

/-- **The inverse of a resolution sends a prime divisor to its strict transform.** For a proper
birational morphism `p : W ⟶ X` of normal varieties with inverse `h`, the birational transform
under `h` of a prime divisor `P` of `X` is the prime divisor `E` of `W` with `p(η_E) = η_P`, along
which `p` induces an isomorphism of local rings. -/
private theorem exists_transformPrimeDivisor_eq_some_of_isInverse {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) (p : W ⟶ X) (h : X.RationalMap W) [IsProper p]
    (hWnp : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (hinv : RationalMap.IsInverse p.toRationalMap h) (P : MMP.Mori.PrimeDivisor X) :
    ∃ E : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor h P = some E ∧
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) := by
  have := hX.1
  have := hWnp.1
  have := isSeparated_toTerminal (p ≫ sX)
  obtain ⟨E, h', hh'P, hh', hwE, heq, hiso⟩ := exists_strictTransform hX p h hWnp hpb hinv P
  exact ⟨E, transformPrimeDivisor_eq_some_of_genericPoint_eq h' hh' hh'P hwE, heq, hiso⟩

/-- Along a prime divisor `E` of `Y` with `f(η_E) = η_P` at which `f` induces an isomorphism of
local rings, the valuation `ord_E ∘ f^*` is `ord_P`. -/
private theorem divisorialValuation_comap_functionFieldMap_eq {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] :
    E.divisorialValuation.comap (functionFieldMap f) = P.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq t]

end StrictTransform

/-! ### Pull-backs of `ℝ`-Cartier divisors -/

section PullbackAlgebra

open MMP.Flips

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

private theorem isRCartierPullback_of_isPullback {f : Y ⟶ X} {L : Divisor X} (hL : L.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp}
    {L' : Divisor Y} (h : L.IsPullback f hB L') :
    IsRCartierPullback f (Divisor.toRDivisor L) (Divisor.toRDivisor L') :=
  ⟨1, fun _ => 1, fun _ => L, fun _ => L', fun _ => hL, by simp, fun _ => ⟨hB, h⟩, by simp⟩

end PullbackAlgebra

section CrepantInputs

open MMP.Flips
open scoped WithZero

/-! ### Log discrepancies and discrepancies -/

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A discrepancy computed with a form whose divisor is canonical gives the log discrepancy
`1 + a`. -/
private theorem isLogDiscrepancy_of_isDiscrepancyWith {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {b : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n D ω r L E b) :
    MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + b) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r,
    L, L', hLc, fun Γ => ?_, hpb, by ring⟩
  have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    MMP.Flips.coeff_sum_smul_toRDivisor] using this

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ b, IsDiscrepancyWith sX n D ω r L E b := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := E.isProper
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

end Discrepancy

/-! ### Changing the structure morphism -/

section StructureMorphism

variable {k : Type u} [Field k] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
  [IsNormal W] [CompactSpace W]

private theorem isDiscrepancy_of_eq {s s' : W ⟶ Spec (.of k)} (h : s = s')
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] {n : ℕ} {K : Divisor W} {D : RDivisor W}
    {v : Valuation W.functionField ℤᵐ⁰} {a : ℝ} (ha : MMP.Flips.IsDiscrepancy s n K D v a) :
    MMP.Flips.IsDiscrepancy s' n K D v a := by
  subst h
  exact ha

omit [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] in
private theorem exists_properDivisorOver_of_eq {s s' : W ⟶ Spec (.of k)} (h : s = s')
    (E : ProperDivisorOver k s) : ∃ E' : ProperDivisorOver k s', E'.valuation = E.valuation := by
  subst h
  exact ⟨E, rfl⟩

end StructureMorphism

/-! ### Lifting a divisor over `M` to a proper model `W ⟶ M` -/

section Lift

variable {k : Type u} [Field k] {M W : Scheme.{u}} [IsIntegral M] [IsIntegral W]
  {sM : M ⟶ Spec (.of k)}

variable [IsLocallyNoetherian M] [IsNormal M] [IsLocallyNoetherian W] [IsNormal W]

/-- **Lifting a divisor over `M` along a proper birational morphism.** Every divisor `D` over `M`
with proper model has the valuation `ord_E ∘ q^*` of a divisor `E` over `W`, for `q : W ⟶ M`
proper birational with `W` a variety. -/
private theorem exists_properDivisorOver_comap_eq (q : W ⟶ M) [IsProper q]
    (hq : IsBirationalMorphism q) [AlgebraicGeometry.IsVariety k (q ≫ sM)]
    (D : ProperDivisorOver k sM) :
    haveI := hq.isDominant
    ∃ E : ProperDivisorOver k (q ≫ sM),
      E.valuation.comap (functionFieldMap q) = D.valuation := by
  haveI := hq.isDominant
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hbq := hq.functionFieldMap_bijective
  let eq := RingEquiv.ofBijective (functionFieldMap q) hbq
  let ξ : Valuation W.functionField ℤᵐ⁰ := D.valuation.comap eq.symm.toRingHom
  have hξ : ξ.comap (functionFieldMap q) = D.valuation := by
    ext a
    change D.valuation (eq.symm (functionFieldMap q a)) = D.valuation a
    rw [show functionFieldMap q a = eq a from rfl, RingEquiv.symm_apply_apply]
  obtain ⟨x, hle, hlt⟩ := exists_dominated_point q ‹_› D.toDivisorOver ξ hξ
  have hdiv : IsDivisorOfFunctionField k (q ≫ sM) ξ := by
    refine ⟨D.Y, D.f ≫ sM, D.isNormalVariety, D.E, ?_⟩
    letI := functionFieldAlgebra sM
    letI := functionFieldAlgebra (q ≫ sM)
    letI := functionFieldAlgebra (D.f ≫ sM)
    let eP := functionFieldAlgEquiv sM q hbq
    let eY := functionFieldAlgEquiv sM D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbq.2 t
    change D.valuation (eq.symm (functionFieldMap q s)) =
      D.E.divisorialValuation (eY (eP.symm (functionFieldMap q s)))
    have h1 : eP.symm (functionFieldMap q s) = s := eP.symm_apply_apply s
    rw [h1, show functionFieldMap q s = eq s from rfl, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨E, -, hv, -⟩ := exists_properDivisorOver_isProjective_of_dominates (q ≫ sM) hdiv x hle hlt
  exact ⟨E, by rw [hv, hξ]⟩

end Lift

/-! ### Compatible forms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

open MMP.Positivity in
/-- For a proper birational morphism `f : Y → X` of normal varieties of dimension `n` and a
canonical divisor `K_Y` of `Y`, there is a nonzero rational top form `ω` on `X` with
`div_Y(f^*ω) = K_Y` and `div_X(ω) = f_* K_Y`. -/
private theorem exists_divisorOfForm_eq_transformDivisor (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} (hn : topologicalKrullDim X = n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      divisorOfForm ω = RationalMap.transformDivisor (X := Y) f.toRationalMap KY ∧
      divisorOfForm (pullbackRationalPluriForms sX f ω) = KY := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hY hKY
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sX f τ = ω₁ := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  refine ⟨τ, fun h0 => hω₁0 ?_, Finsupp.ext fun P => ?_, Finsupp.ext fun Γ => ?_⟩
  · rw [← hpull, h0]
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp
  · obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [htr]
    change P.ordForm τ = KY.coeff E
    rw [← ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, hpull, hω₁]
  · change Γ.ordForm _ = KY.coeff Γ
    rw [hpull, hω₁]

end Forms

/-! ### Comparison of log discrepancies along a common resolution -/

section Comparison

variable {k : Type u} [Field k] [PerfectField k]

/-- **Adding an effective `ℝ`-Cartier divisor lowers discrepancies.** If `a` is the discrepancy
of a valuation `v` with respect to `D` and `D' ≥ 0` is `ℝ`-Cartier, the discrepancy with respect
to `D + D'` is some `a' ≤ a`. -/
private theorem exists_le_isDiscrepancy_add {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [LocallyOfFiniteType sW] {n : ℕ} {K : Divisor W} {D : RDivisor W}
    {v : Valuation W.functionField ℤᵐ⁰} {a : ℝ} (h : IsDiscrepancy sW n K D v a)
    {D' : RDivisor W} (hD' : RDivisor.IsRCartier D') (h0 : 0 ≤ D') :
    ∃ a', a' ≤ a ∧ IsDiscrepancy sW n K (D + D') v a' := by
  obtain ⟨hK, ⟨m, r, L, hL, hKD⟩, hc, E₀, ω₀, m₀, r₀, L₀, hE₀, hdiv₀, hw₀⟩ := h
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := hw₀
  obtain ⟨m', r', C, hC, hD'eq⟩ := hD'
  have hD'eq' : D' = ∑ j, r' j • Divisor.toRDivisor (C j) := by
    ext Γ
    exact (hD'eq Γ).trans (MMP.Flips.coeff_sum_smul_toRDivisor r' C Γ).symm
  haveI := E₀.isIntegral
  haveI := E₀.isNormal
  haveI := E₀.isLocallyNoetherian
  haveI := E₀.isDominant
  haveI := E₀.isProper
  haveI : CompactSpace E₀.Y := QuasiCompact.compactSpace_of_compactSpace E₀.f
  choose C' hC' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E₀.f (hC j)
  have hG : IsRCartierPullback E₀.f D' (∑ j, r' j • Divisor.toRDivisor (C' j)) :=
    ⟨m', r', C, C', hC, hD'eq', fun j => ⟨_, hC' j⟩, rfl⟩
  have hG0 := (MMP.Fourfold.isEffective_of_isRCartierPullback E₀.f
    ⟨m', r', C, hC, hD'eq⟩ h0).2 _ hG
  have hnn : (0 : ℝ) ≤ ∑ j, r' j * ((C' j).coeff E₀.E : ℝ) := by
    have := hG0 E₀.E
    change (0 : ℝ) ≤ DivisorWithCoeffs.coeff (∑ j, r' j • Divisor.toRDivisor (C' j)) E₀.E at this
    rwa [MMP.Flips.coeff_sum_smul_toRDivisor] at this
  refine ⟨(E₀.toDivisorOver.ordPullback ω₀ : ℝ) - ∑ j, r₀ j * (L' j).coeff E₀.E -
    ∑ j, r' j * ((C' j).coeff E₀.E : ℝ), by linarith, hK, ⟨m + m', Fin.append r r',
      Fin.append L C, Fin.addCases (by simpa using hL) (by simpa using hC), ?_⟩, hc, E₀, ω₀,
      m₀ + m', Fin.append r₀ r', Fin.append L₀ C, hE₀, hdiv₀, hX, hn, hω,
      Fin.addCases (by simpa using hLc) (by simpa using hC), ?_, Fin.append L' C',
      Fin.addCases (by simpa using hpb) (by simpa using fun j =>
        (⟨_, hC' j⟩ : ∃ hB, (C j).IsPullback E₀.f hB (C' j))), ?_⟩
  · rw [← add_assoc, hKD, hD'eq', Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, MMP.Flips.toRDivisor_eq_mapCoeffs]
  · rw [← add_assoc, hsum, hD'eq', Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

variable {X M W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sM : M ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
  [LocallyOfFiniteType sM] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **Comparison of log discrepancies along a common resolution.** Let `p : W ⟶ X` and
`q : W ⟶ M` be proper birational morphisms of normal varieties of dimension `n`, with rational
top forms `ω_X`, `ω_M` whose canonical divisors pull back to the same `K_W`. If
`G_X = p^*(K_X + D_X)` and `G_M = q^*(K_M + D_M)` differ by an effective `ℝ`-Cartier divisor
`G_X - G_M ≥ 0`, then every log discrepancy of `(M, D_M)` is at least one of `(X, D_X)`; in
particular if all log discrepancies of `(X, D_X)` are positive, so are those of `(M, D_M)`. -/
private theorem logDiscrepancy_pos_of_crepant_le {p : W ⟶ X} {q : W ⟶ M} [IsProper p]
    [IsProper q] [IsDominant p] [IsDominant q] [LocallyOfFiniteType (p ≫ sX)]
    [LocallyOfFiniteType (q ≫ sM)] [AlgebraicGeometry.IsVariety k (q ≫ sM)]
    (hXn : IsNormalVariety k sX) (hMn : IsNormalVariety k sM)
    (hWnp : IsNormalVariety k (p ≫ sX)) (hWnq : IsNormalVariety k (q ≫ sM))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hss : q ≫ sM = p ≫ sX)
    {n : ℕ} (hdM : topologicalKrullDim M = n)
    {ωX : RationalPluriForms sX n 1} (hωX0 : ωX ≠ 0)
    (hKXc : (divisorOfForm ωX).IsCanonicalDivisor sX n)
    {ωM : RationalPluriForms sM n 1} (hωM0 : ωM ≠ 0)
    (hKMc : (divisorOfForm ωM).IsCanonicalDivisor sM n)
    {KW : Divisor W} (hKWp : KW.IsCanonicalDivisor (p ≫ sX) n)
    (hKWq : KW.IsCanonicalDivisor (q ≫ sM) n)
    (hωXW : divisorOfForm (pullbackRationalPluriForms sX p ωX) = KW)
    (hωMW : divisorOfForm (pullbackRationalPluriForms sM q ωM) = KW)
    {DX : RDivisor X} {DM : RDivisor M} {GX GM : RDivisor W}
    (hGp : MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + DX) GX)
    (hGq : MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωM) + DM) GM)
    (hRC : RDivisor.IsRCartier (GX - GM)) (hle : 0 ≤ GX - GM)
    (hkltX : ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX d DX E a → 0 < a)
    (d : ℕ) (E : DivisorOver k sM) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sM d DM E a) : 0 < a := by
  obtain rfl : d = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans hdM
  let EP : MMP.Flips.ProperDivisorOver k sM := ⟨E, ha.2.1⟩
  obtain ⟨mM, rM, LM, -, hLMc, hLMsum, -, -⟩ := id hGq
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hMn hdM hωM0 hLMc hLMsum EP
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
    (isLogDiscrepancy_of_isDiscrepancyWith hKMc hb)]
  have hKDM : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωM) + DM) :=
    ⟨mM, rM, LM, hLMc, by rw [hLMsum]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨E', hE'⟩ := exists_properDivisorOver_comap_eq q hqb EP
  have hDYq : MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωM) + DM)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sM q ωM)) +
        (GM - Divisor.toRDivisor KW)) := by
    rw [hωMW, add_sub_cancel]
    exact hGq
  have h1 := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hMn hωM0 hKMc hKDM q hWnq hqb
    hDYq (by rw [hωMW]; exact hKWq) E' b).mp (by
      rw [hE']
      exact ⟨hKMc, hKDM, hasNonemptyCenter_valuation EP, EP, ωM, mM, rM, LM, rfl, rfl, hb⟩)
  rw [hωMW] at h1
  -- lowering the boundary on `W` from `G_M - K_W` to `G_X - K_W`
  obtain ⟨b', hb'b, h2⟩ := exists_le_isDiscrepancy_add h1 hRC hle
  have hGsum : GM - Divisor.toRDivisor KW + (GX - GM) = GX - Divisor.toRDivisor KW := by abel
  rw [hGsum] at h2
  obtain ⟨E'', hE''⟩ := exists_properDivisorOver_of_eq hss E'
  obtain ⟨mX, rX, LX, -, hLXc, hLXsum, -, -⟩ := id hGp
  have hKDX : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + DX) :=
    ⟨mX, rX, LX, hLXc, by rw [hLXsum]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hDYp : MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + DX)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX)) +
        (GX - Divisor.toRDivisor KW)) := by
    rw [hωXW, add_sub_cancel]
    exact hGp
  obtain ⟨-, -, -, E₀, ω₀, m₀, r₀, L₀, -, hdiv₀, hw₀⟩ :=
    (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hXn hωX0 hKXc hKDX p hWnp hpb hDYp
      (by rw [hωXW]; exact hKWp) E'' b').mpr (by rw [hωXW, hE'']; exact isDiscrepancy_of_eq hss h2)
  have := hkltX _ E₀.toDivisorOver (1 + b')
    (isLogDiscrepancy_of_isDiscrepancyWith (by rw [hdiv₀]; exact hKXc) hw₀)
  linarith

omit [PerfectField k] in
open Classical in
/-- On a smooth variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isSmoothScheme {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (hsm : IsSmoothScheme sZ)
    (D : RDivisor Z) : RDivisor.IsRCartier D := by
  refine ⟨D.support.card, fun i => D.coeff (D.support.equivFin.symm i),
    fun i => Finsupp.single (D.support.equivFin.symm i : MMP.Mori.PrimeDivisor Z) (1 : ℤ),
    fun i => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _, fun Γ => ?_⟩
  simp only [DivisorWithCoeffs.coeff_apply]
  rw [sum_equivFin_mul_single D.support (⇑D) Γ]
  split_ifs with h
  · rfl
  · exact Finsupp.notMem_support_iff.mp h

end Comparison

end CrepantInputs

/-! ### Birational transforms of effective divisors -/

section TransformEffective

variable {X Y : Scheme.{u}}

open Classical in
/-- The coefficient of `F` in the birational transform of `D`: the sum of the coefficients of the
prime divisors mapping onto `F`. -/
private theorem mapPrimeDivisors_apply_eq_sum
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : RDivisor X)
    (F : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.mapPrimeDivisors φ D F =
      ∑ P ∈ D.support, if φ P = some F then D P else 0 := by
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun P _ => ?_
  rcases hP : φ P with _ | E
  · rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_none hP]
    simp
  · rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_some hP, Finsupp.single_apply]
    by_cases hEF : E = F
    · simp [hEF]
    · simp [hEF]

/-- The birational transform of an effective `ℝ`-divisor is effective, and its coefficient along
`F` is at least that of every prime divisor mapping onto `F`. -/
private theorem le_mapPrimeDivisors_apply
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) {D : RDivisor X}
    (hD : ∀ P, 0 ≤ D.coeff P) (F : MMP.Mori.PrimeDivisor Y) :
    0 ≤ DivisorWithCoeffs.mapPrimeDivisors φ D F ∧
      ∀ P, φ P = some F → D.coeff P ≤ DivisorWithCoeffs.mapPrimeDivisors φ D F := by
  classical
  rw [mapPrimeDivisors_apply_eq_sum]
  have hnn : ∀ P ∈ D.support, 0 ≤ if φ P = some F then D P else 0 := fun P _ => by
    split_ifs
    · exact hD P
    · exact le_rfl
  refine ⟨Finset.sum_nonneg hnn, fun P hP => ?_⟩
  by_cases hPs : P ∈ D.support
  · have := Finset.single_le_sum hnn hPs
    rw [if_pos hP] at this
    exact this
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hPs]
    exact Finset.sum_nonneg hnn

end TransformEffective

/-! ### Log discrepancies on a nef log birational model -/

section NefModel

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
private theorem isNormalVariety_comp_left {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY) :
    IsNormalVariety k (p ≫ sX) := by
  rw [hR.comp_eq_left]
  exact ⟨hR.isVariety, inferInstance⟩

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
private theorem isNormalVariety_comp_right {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY) :
    IsNormalVariety k (q ≫ sY) := by
  rw [hR.comp_eq_right]
  exact ⟨hR.isVariety, inferInstance⟩

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
private theorem compactSpace_of_isLogComparisonResolution {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY) : CompactSpace W := by
  have := hR.isVariety
  exact QuasiCompact.compactSpace_of_compactSpace sW

/-- **One rational top form on each side of a common resolution.** On a common resolution
`p : W ⟶ X`, `q : W ⟶ Y` comparing canonical divisors `K_X` and `K_Y`, the varieties have the
same dimension `n`, and there are a canonical divisor `K_W` of `W` and nonzero rational top forms
`ω_X`, `ω_Y` with `div ω_X = K_X`, `div ω_Y = K_Y` and `div(p^*ω_X) = K_W = div(q^*ω_Y)`. -/
private theorem exists_rationalPluriForms_of_isLogComparisonResolution {W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [CompactSpace Y]
    [LocallyOfFiniteType sY] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y} {KX : Divisor X}
    {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W} [IsProper p] [IsProper q] [IsDominant p]
    [IsDominant q] [LocallyOfFiniteType (p ≫ sX)] [LocallyOfFiniteType (q ≫ sY)]
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY) {n nY : ℕ}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor sY nY) :
    nY = n ∧ ∃ KW : Divisor W, KW.IsCanonicalDivisor (p ≫ sX) n ∧
      KW.IsCanonicalDivisor (q ≫ sY) n ∧
      (∃ ωX : RationalPluriForms sX n 1, ωX ≠ 0 ∧ divisorOfForm ωX = KX ∧
        divisorOfForm (pullbackRationalPluriForms sX p ωX) = KW) ∧
      ∃ ωY : RationalPluriForms sY n 1, ωY ≠ 0 ∧ divisorOfForm ωY = KY ∧
        divisorOfForm (pullbackRationalPluriForms sY q ωY) = KW := by
  have hWnp := isNormalVariety_comp_left hR
  have hWnq := isNormalVariety_comp_right hR
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  obtain ⟨nW, KW, hKW, hKWX, hKWY⟩ := hR.exists_canonicalDivisor
  have hdimX := hKX.topologicalKrullDim_eq
  have := hXn.1
  have := hYn.1
  have := hWnp.1
  have := hWnq.1
  have hdimW : topologicalKrullDim W = topologicalKrullDim X :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm
  have hdimY : topologicalKrullDim W = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (q ≫ sY) hqb).symm
  obtain rfl : nW = n := by
    exact_mod_cast hKW.topologicalKrullDim_eq.symm.trans (hdimW.trans hdimX)
  have hKWp : KW.IsCanonicalDivisor (p ≫ sX) nW := by rw [hR.comp_eq_left]; exact hKW
  have hKWq : KW.IsCanonicalDivisor (q ≫ sY) nW := by rw [hR.comp_eq_right]; exact hKW
  have hdM : topologicalKrullDim Y = nW := hdimY.symm.trans hKW.topologicalKrullDim_eq
  obtain ⟨ωX, hωX0, hωX, hωXW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hXn hWnp hpb hdimX hKWp
  obtain ⟨ωY, hωY0, hωY, hωYW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hYn hWnq hqb hdM hKWq
  exact ⟨by exact_mod_cast hKY.topologicalKrullDim_eq.symm.trans hdM, KW, hKWp, hKWq,
    ⟨ωX, hωX0, hωX.trans hKWX, hωXW⟩, ωY, hωY0, hωY.trans hKWY, hωYW⟩

/-- **Klt descends along an effective comparison.** If a common resolution compares the adjoints
of `(X, Δ)` and `(Y, Δ_Y)` with `p^*(K_X + Δ) - q^*(K_Y + Δ_Y)` effective, then every log
discrepancy of `(Y, Δ_Y)` is positive as soon as every log discrepancy of `(X, Δ)` is. -/
private theorem isLogDiscrepancy_pos_of_isLogComparisonResolution {W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)}
    {φ : X.RationalMap Y} {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y}
    {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY) {n nY : ℕ}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor sY nY)
    (hkltX : ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX d Δ E a → 0 < a) :
    ∀ (d : ℕ) (E : DivisorOver k sY) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sY d ΔY E a → 0 < a := by
  have hWnp := isNormalVariety_comp_left hR
  have hWnq := isNormalVariety_comp_right hR
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : LocallyOfFiniteType (p ≫ sX) := hWnp.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (q ≫ sY) := hWnq.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k (q ≫ sY) := hWnq.1
  have : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  have := hYn.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have := compactSpace_of_isLogComparisonResolution hR
  obtain ⟨rfl, KW, hKWp, hKWq, ⟨ωX, hωX0, hωX, hωXW⟩, ωY, hωY0, hωY, hωYW⟩ :=
    exists_rationalPluriForms_of_isLogComparisonResolution hR hXn hYn hKX hKY
  have hGp := hR.isRCartierPullback_left
  have hGq := hR.isRCartierPullback_right
  rw [MMP.Flips.logCanonicalDivisor, ← hωX] at hGp
  rw [MMP.Flips.logCanonicalDivisor, ← hωY] at hGq
  exact logDiscrepancy_pos_of_crepant_le hXn hYn hWnp hWnq hpb hqb
    (hR.comp_eq_right.trans hR.comp_eq_left.symm) hKY.topologicalKrullDim_eq hωX0
    (by rw [hωX]; exact hKX) hωY0 (by rw [hωY]; exact hKY) hKWp hKWq hωXW hωYW hGp hGq
    (isRCartier_of_isSmoothScheme hR.isSmoothScheme _) hR.effective hkltX

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
/-- **Adding corresponding principal divisors keeps the comparison.** If `θ : k(Y) → k(X)`
induces `φ` and sends the value of `f_Y` to that of `f`, then on every common resolution
comparing the adjoints of `(X, B)` and `(Y, B_Y)`, the pull-backs of `c div f` and `c div f_Y` are
one and the same divisor `c L`, so the resolution compares the adjoints of `(X, B + c div f)` and
`(Y, B_Y + c div f_Y)` with the same comparison divisor. -/
private theorem exists_isLogComparisonResolution_add_smul [CompactSpace X] [CompactSpace Y]
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y} {KX : Divisor X} {B : RDivisor X}
    {KY : Divisor Y} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W}
    {GX GY : RDivisor W} (hR : IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (f : (RationalFunctions X)ˣ) (fY : (RationalFunctions Y)ˣ) (Zx : irreducibleComponents X)
    (Zy : irreducibleComponents Y)
    (hf : θ (MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y)) =
      MMP.Threefold.Mori.Helpers.evalFF Zx (f : RationalFunctions X)) (c : ℝ) :
    ∃ L : Divisor W, IsLogComparisonResolution sX sY sW φ KX
      (B + c • Divisor.toRDivisor (principalDivisor f)) KY
      (BY + c • Divisor.toRDivisor (principalDivisor fY)) p q h
      (GX + c • Divisor.toRDivisor L) (GY + c • Divisor.toRDivisor L) := by
  have : IsDominant p := hR.isBirationalMorphism_left.isDominant
  have : IsDominant q := hR.isBirationalMorphism_right.isDominant
  have := compactSpace_of_isLogComparisonResolution hR
  have hφp := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p (principalDivisor f)
  have hφq := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp q (principalDivisor fY)
  have hLp := Divisor.isPullback_principalDivisor f hφp
  have hLq := Divisor.isPullback_principalDivisor fY hφq
  have hLL := isPullback_principalDivisor_eq φ θ hθ f fY Zx Zy hf p q h hR.isInverse
    hR.compHom_eq hLp hLq
  refine ⟨principalDivisor (pullbackRationalFunction p f hφp), ⟨hR.isVariety, hR.isSmoothScheme,
    hR.comp_eq_left, hR.comp_eq_right,
    hR.isProjectiveMorphism_left, hR.isProjectiveMorphism_right, hR.isBirationalMorphism_left,
    hR.isBirationalMorphism_right, hR.isInverse, hR.compHom_eq, hR.exists_canonicalDivisor, ?_, ?_,
    ?_, ?_⟩⟩
  · have := isRCartierPullback_add hR.isRCartierPullback_left (isRCartierPullback_smul c
      (isRCartierPullback_of_isPullback (Divisor.isCartier_principalDivisor f) hLp))
    rwa [MMP.Flips.logCanonicalDivisor, ← add_assoc]
  · have := isRCartierPullback_add hR.isRCartierPullback_right (isRCartierPullback_smul c
      (isRCartierPullback_of_isPullback (Divisor.isCartier_principalDivisor fY) hLq))
    rw [← hLL] at this
    rwa [MMP.Flips.logCanonicalDivisor, ← add_assoc]
  · intro P
    rw [add_sub_add_right_eq_sub]
    exact hR.effective P
  · intro P hP
    rw [add_sub_add_right_eq_sub] at hP
    exact hR.isExceptional P hP

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
/-- **Orders at a birational transform.** If `θ : k(Y) → k(X)` induces `φ` and sends the value of
`f_Y` to that of `f`, and `φ_* P = F`, then `ord_F f_Y = ord_P f`: on a common resolution both
are the order of the common pull-back along the common strict transform. -/
private theorem coeff_principalDivisor_eq_of_transformPrimeDivisor_eq_some [CompactSpace X]
    [CompactSpace Y] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y} {KX : Divisor X} {B : RDivisor X}
    {KY : Divisor Y} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W}
    {GX GY : RDivisor W} (hR : IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (f : (RationalFunctions X)ˣ) (fY : (RationalFunctions Y)ˣ) (Zx : irreducibleComponents X)
    (Zy : irreducibleComponents Y)
    (hf : θ (MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y)) =
      MMP.Threefold.Mori.Helpers.evalFF Zx (f : RationalFunctions X))
    {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (hPF : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F) :
    (principalDivisor fY).coeff F = (principalDivisor f).coeff P := by
  have hWnp := isNormalVariety_comp_left hR
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have : IsDominant p := hR.isBirationalMorphism_left.isDominant
  have : IsDominant q := hR.isBirationalMorphism_right.isDominant
  have := compactSpace_of_isLogComparisonResolution hR
  obtain ⟨E, hpE, hisoP, hqE, hisoQ⟩ :=
    exists_primeDivisor_apply_eq_of_transformPrimeDivisor_eq_some hXn hYn p q h hWnp
      hR.isBirationalMorphism_left hR.isBirationalMorphism_right hR.isInverse hR.compHom_eq hPF
  have hφp := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p (principalDivisor f)
  have hφq := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp q (principalDivisor fY)
  have hLp := Divisor.isPullback_principalDivisor f hφp
  have hLq := Divisor.isPullback_principalDivisor fY hφq
  have hLL := isPullback_principalDivisor_eq φ θ hθ f fY Zx Zy hf p q h hR.isInverse
    hR.compHom_eq hLp hLq
  have h1 := MMP.Positivity.coeff_eq_of_isPullback (f := p) E P hpE
    (Divisor.isCartier_principalDivisor f) hLp
  have h2 := MMP.Positivity.coeff_eq_of_isPullback (f := q) E F hqE
    (Divisor.isCartier_principalDivisor fY) hLq
  rw [← h1, ← h2, hLL]

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
/-- **The valuation of a divisor realizing `P` through the inverse map.** If `ψ` is inverse to
`φ`, `θ` induces `φ`, and the divisor `E_Y` over `Y` realizes the prime divisor `P` of `X` through
`ψ`, then the valuation of `E_Y` on `k(Y)` is `ord_P ∘ θ`. -/
private theorem valuation_eq_comap_of_isRealizedOver {φ : X.RationalMap Y}
    {ψ : Y.RationalMap X} (hinv : MMP.Mori.RationalMap.IsInverse φ ψ)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (P : MMP.Mori.PrimeDivisor X) (EY : MMP.Flips.ProperDivisorOver k sY)
    (hEY : MMP.Flips.IsRealizedOver sY ψ P EY) :
    EY.toDivisorOver.valuation = P.divisorialValuation.comap θ := by
  obtain ⟨g, pE, hpE, hg, hcomm, hval⟩ := hEY
  haveI := EY.isIntegral
  haveI := EY.isNormal
  haveI := EY.isLocallyNoetherian
  haveI := EY.isDominant
  haveI := hpE.isDominant
  have hA : Spec.map (CommRingCat.ofHom (functionFieldMap EY.f)) ≫ ψ.fromFunctionField =
      EY.Y.fromSpecStalk (genericPoint EY.Y) ≫ pE := by
    rw [← hg]
    exact specMap_functionFieldMap_fromFunctionField EY.f g pE hcomm
  obtain ⟨θ', -, hθ'⟩ := exists_ringHom_of_specMap ψ.fromFunctionField EY.f pE
    EY.isBirationalMorphism.functionFieldMap_bijective hpE.functionFieldMap_bijective hA
  have h1 := functionFieldMap_comp_eq_of_specMap ψ.fromFunctionField θ' hθ' EY.f pE hA
  have h2 := comp_eq_id_of_isInverse hinv θ hθ θ' hθ'
  have h3 : (functionFieldMap pE).comp θ = functionFieldMap EY.f := by
    rw [← h1, RingHom.comp_assoc, h2, RingHom.comp_id]
  refine Valuation.ext fun t => ?_
  change EY.E.divisorialValuation (functionFieldMap EY.f t) = P.divisorialValuation (θ t)
  rw [← hval, Valuation.comap_apply, ← RingHom.comp_apply, h3]

/-- **Equal log discrepancies where the comparison vanishes.** On a common resolution comparing
the adjoints of `(X, Δ)` and `(Y, Δ_Y)`, let `E'` be the strict transform of a prime divisor `P` of
`X` along which the comparison `p^*(K_X + Δ) - q^*(K_Y + Δ_Y)` vanishes, and let `E_Y` be a divisor
over `Y` realizing `P` through the inverse `ψ` of `φ`. Then `a(E_Y; Y, Δ_Y) = a(P; X, Δ)`: both
equal `1 + coeff_{E'}(K_W) - coeff_{E'}(p^*(K_X + Δ))`. -/
private theorem logDiscrepancy_eq_of_coeff_sub_eq_zero {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {ψ : Y.RationalMap X} {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y}
    {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY) {n nY : ℕ}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor sY nY)
    (hψ : MMP.Mori.RationalMap.IsInverse φ ψ)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (P : MMP.Mori.PrimeDivisor X) (E' : MMP.Mori.PrimeDivisor W)
    (hpE' : p E'.genericPoint = P.genericPoint) [IsIso (p.stalkMap E'.genericPoint)]
    (h0 : (GX - GY).coeff E' = 0) (EY : MMP.Flips.ProperDivisorOver k sY)
    (hEY : MMP.Flips.IsRealizedOver sY ψ P EY) {d d' : ℕ} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX d Δ (DivisorOver.ofPrimeDivisor k hXn P) a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sY d' ΔY EY.toDivisorOver a') : a' = a := by
  have hWnp := isNormalVariety_comp_left hR
  have hWnq := isNormalVariety_comp_right hR
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : LocallyOfFiniteType (p ≫ sX) := hWnp.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (q ≫ sY) := hWnq.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  have := hYn.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have := compactSpace_of_isLogComparisonResolution hR
  obtain ⟨rfl, KW, -, -, ⟨ωX, hωX0, hωX, hωXW⟩, ωY, hωY0, hωY, hωYW⟩ :=
    exists_rationalPluriForms_of_isLogComparisonResolution hR hXn hYn hKX hKY
  -- the two divisors over `X` and `Y` given by `E'`
  let DX : DivisorOver k sX := ⟨W, p, hWnp, hpb, E'⟩
  let DY : DivisorOver k sY := ⟨W, q, hWnq, hqb, E'⟩
  have hvX : (DivisorOver.ofPrimeDivisor k hXn P).valuation = DX.valuation := by
    refine Valuation.ext fun t => ?_
    change P.divisorialValuation (functionFieldMap (𝟙 X) t) =
      E'.divisorialValuation (functionFieldMap p t)
    rw [MMP.Mori.functionFieldMap_id_apply, ← Valuation.comap_apply (functionFieldMap p),
      divisorialValuation_comap_functionFieldMap_eq p E' P hpE']
  have hvY : EY.toDivisorOver.valuation = DY.valuation := by
    rw [valuation_eq_comap_of_isRealizedOver hψ θ hθ P EY hEY]
    refine Valuation.ext fun t => ?_
    change P.divisorialValuation (θ t) = E'.divisorialValuation (functionFieldMap q t)
    rw [← functionFieldMap_comp_eq φ θ hθ p q h hR.isInverse hR.compHom_eq, RingHom.comp_apply,
      ← Valuation.comap_apply (functionFieldMap p),
      divisorialValuation_comap_functionFieldMap_eq p E' P hpE']
  -- the log discrepancies of `DX` and `DY`
  have hlog : ∀ {M : Scheme.{u}} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M]
      [CompactSpace M] {sM : M ⟶ Spec (.of k)} [LocallyOfFiniteType sM] {KM : Divisor M}
      {ΔM : RDivisor M} {f : W ⟶ M} [IsProper f] [IsDominant f] {G : RDivisor W} {e : ℕ}
      (hMn : IsNormalVariety k sM) (hKM : KM.IsCanonicalDivisor sM e)
      (hWnf : IsNormalVariety k (f ≫ sM)) (hfb : IsBirationalMorphism f)
      (ω : RationalPluriForms sM e 1), ω ≠ 0 → divisorOfForm ω = KM →
      divisorOfForm (pullbackRationalPluriForms sM f ω) = KW →
      MMP.Flips.IsRCartierPullback f (MMP.Flips.logCanonicalDivisor KM ΔM) G →
      MMP.Intersection.IsLogDiscrepancy sM e ΔM ⟨W, f, hWnf, hfb, E'⟩
        (1 + (KW.coeff E' : ℝ) - G.coeff E') := by
    intro M _ _ _ _ sM _ KM ΔM f _ _ G e hMn hKM hWnf hfb ω hω0 hωK hωW hG
    obtain ⟨m, r, L, L', hLc, hD, hpbL, rfl⟩ := hG
    refine ⟨hMn, inferInstanceAs (IsProper f), ω, hω0, ⟨KM, hKM, fun Γ => by
      rw [← hωK]; exact coeff_divisorOfForm ω Γ⟩, m, r, L, L', hLc, fun Γ => ?_, hpbL, ?_⟩
    · have := congrArg (fun D : RDivisor M => D.coeff Γ) hD
      simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
        Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
      rw [← this, ← hωK, coeff_divisorOfForm]
    · rw [MMP.Flips.coeff_sum_smul_toRDivisor, ← hωW, coeff_divisorOfForm]
      rfl
  have hGp := hR.isRCartierPullback_left
  have hGq := hR.isRCartierPullback_right
  have hDX := hlog hXn (by rw [← hωX] at hKX ⊢; exact hKX) hWnp hpb ωX hωX0 hωX hωXW hGp
  have hDY := hlog hYn hKY hWnq hqb ωY hωY0 hωY hωYW hGq
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hDX hvX,
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha' hDY hvY]
  have : GX.coeff E' = GY.coeff E' := by
    rw [DivisorWithCoeffs.coeff_sub] at h0
    linarith
  rw [this]

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
open Classical in
/-- **The transported lowering is effective near zero.** If `θ : k(Y) → k(X)` induces `φ` and
sends the value of `f_Y` to that of `f`, `B_Y` is the transform of `B` plus the inverse-exceptional
primes, and `f` has no pole along a prime with coefficient zero in `B`, then `B_Y + c · div f_Y` is
effective for all small `c > 0`. -/
private theorem eventually_coeff_nonneg_add_smul_principalDivisor [CompactSpace X]
    [CompactSpace Y] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y} {KX : Divisor X} {B : RDivisor X}
    {KY : Divisor Y} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W}
    {GX GY : RDivisor W} (hR : IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (f : (RationalFunctions X)ˣ) (fY : (RationalFunctions Y)ˣ) (Zx : irreducibleComponents X)
    (Zy : irreducibleComponents Y)
    (hf : θ (MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y)) =
      MMP.Threefold.Mori.Helpers.evalFF Zx (f : RationalFunctions X))
    (hB0 : ∀ P, 0 ≤ B.coeff P) (hBY0 : ∀ F, 0 ≤ BY.coeff F)
    (hBY : ∀ F : MMP.Mori.PrimeDivisor Y,
      BY.coeff F = (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hf0 : ∀ P, B.coeff P = 0 → 0 ≤ (principalDivisor f).coeff P) :
    ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ F, 0 ≤ (BY + c • Divisor.toRDivisor (principalDivisor fY)).coeff F := by
  have hF : ∀ F, ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ BY.coeff F + c * ((principalDivisor fY).coeff F : ℝ) := by
    intro F
    -- a prime with coefficient zero in `B_Y` is the transform of a prime with coefficient
    -- zero in `B`, along which `f` has no pole
    refine eventually_nonneg_add_mul (hBY0 F) fun heq => ?_
    norm_cast
    have hcb := hBY F
    rw [heq] at hcb
    have hle := le_mapPrimeDivisors_apply
      (MMP.Mori.RationalMap.transformPrimeDivisor φ) hB0 F
    have hT0 : 0 ≤ ((MMP.Mori.RationalMap.transformDivisor φ) B).coeff F := hle.1
    by_cases hie : MMP.Flips.RationalMap.IsInverseExceptional φ F
    · rw [if_pos hie] at hcb
      linarith
    · rw [if_neg hie, add_zero] at hcb
      obtain ⟨P, hPF⟩ : ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F := by
        by_contra hne
        push Not at hne
        exact hie hne
      have hBP : B.coeff P = 0 := by
        have h2 : B.coeff P ≤ ((MMP.Mori.RationalMap.transformDivisor φ) B).coeff F :=
          hle.2 P hPF
        exact le_antisymm (by linarith) (hB0 P)
      rw [coeff_principalDivisor_eq_of_transformPrimeDivisor_eq_some hR hXn hYn θ hθ f fY
        Zx Zy hf hPF]
      exact hf0 P hBP
  have hall := (Filter.eventually_all_finset (principalDivisor fY).support).mpr fun F _ => hF F
  filter_upwards [hall] with c hc F
  rw [coeff_add_smul_principalDivisor]
  by_cases hFs : F ∈ (principalDivisor fY).support
  · exact hc F hFs
  · have : (principalDivisor fY).coeff F = 0 := Finsupp.notMem_support_iff.mp hFs
    rw [this, Int.cast_zero, mul_zero, add_zero]
    exact hBY0 F

end NefModel

/-- Let `X` be a smooth projective variety over an algebraically closed field of characteristic
zero, and `(X, B)` an effective lc pair with `B` of simple normal crossing support, such that
`A ≤ B` for an effective ample `ℚ`-divisor `A` none of whose components has coefficient one in
`B`. If `(Y/Z, B_Y)` with `φ : X ⤏ Y` is a nef log birational model of `(X/Z, B)`
(`MMP.Fourfold.IsNefLogBirationalModel`), there are an effective klt boundary `Δ ∼_ℝ B` on `X` and
an effective klt boundary `Δ_Y` on `Y` such that on every common resolution `p : W ⟶ X`,
`q : W ⟶ Y` comparing the adjoints of `(X, B)` and `(Y, B_Y)` the comparison of the adjoints of
`(X, Δ)` and `(Y, Δ_Y)` is the same divisor. Consequently, for every prime divisor `E` of `X`
contracted by `φ` along whose strict transform the comparison vanishes,
`0 < a(E; Y, Δ_Y) = a(E; X, Δ) ≤ 1`. -/
@[mmp "lem_fourfold_theta_klt_perturbation"]
public theorem exists_isRealKltPair_comparison_eq_of_isNefLogBirationalModel
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X} {B : RDivisor X} {KY : Divisor Y}
    {BY : RDivisor Y} {φ : X.RationalMap Y}
    (hXsm : MMP.Mori.IsSmoothScheme sX) (hXproj : MMP.Mori.IsProjectiveVariety k sX)
    (hBlc : IsRealLcPair sX B) (hBsnc : DivisorWithCoeffs.IsSNC sX B)
    (A : QDivisor X) (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAB : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P) (hAfloor : ∀ P, A.coeff P ≠ 0 → B.coeff P < 1)
    (hY : IsNefLogBirationalModel sX sY sZ π πY KX B KY BY φ) :
    ∃ (Δ : RDivisor X) (ΔY : RDivisor Y),
      (∀ P, 0 ≤ Δ.coeff P) ∧ IsRealKltPair sX Δ ∧
      (∃ (m : ℕ) (r : Fin m → ℝ) (f : Fin m → (RationalFunctions X)ˣ),
        ∀ P, Δ.coeff P = B.coeff P + ∑ i, r i * ((principalDivisor (f i)).coeff P : ℝ)) ∧
      (∀ P, 0 ≤ ΔY.coeff P) ∧ IsRealKltPair sY ΔY ∧
      (∀ (W : Scheme.{u}) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
          (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
          (GX GY : RDivisor W),
        IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY →
        ∃ GX' GY' : RDivisor W,
          IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX' GY' ∧
            GX' - GY' = GX - GY) ∧
      ∀ E : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.IsExceptional φ E →
        (∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
            (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
            (GX GY : RDivisor W),
          IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY ∧
            ∀ E' : MMP.Mori.PrimeDivisor W,
              MMP.Mori.RationalMap.transformPrimeDivisor h E = some E' →
                (GX - GY).coeff E' = 0) →
        ∀ (ψ : Y.RationalMap X), MMP.Mori.RationalMap.IsInverse φ ψ →
        ∀ (EY : MMP.Flips.ProperDivisorOver k sY), MMP.Flips.IsRealizedOver sY ψ E EY →
        ∀ (n : ℕ) (a a' : ℝ),
          MMP.Intersection.IsLogDiscrepancy sX n Δ
            (DivisorOver.ofPrimeDivisor k hY.isRealLcPair.1 E) a →
          MMP.Intersection.IsLogDiscrepancy sY n ΔY EY.toDivisorOver a' →
          0 < a' ∧ a' = a ∧ a ≤ 1 := by
  classical
  have hXn : IsNormalVariety k sX := hBlc.1
  have hYn : IsNormalVariety k sY := hY.isNormalVariety_model
  have : CompactSpace Y := by
    have := hYn.1
    exact QuasiCompact.compactSpace_of_compactSpace sY
  have : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  obtain ⟨n, hKX⟩ := hY.isCanonicalDivisor
  obtain ⟨nY, hKY⟩ := hY.isCanonicalDivisor_model
  have hB0 : ∀ P, 0 ≤ B.coeff P := hBlc.2.1
  -- the coefficients of `B` are at most one
  have hB1 : ∀ P, B.coeff P ≤ 1 := by
    intro P
    obtain ⟨n₁, K₁, hK₁, hRC₁⟩ := hBlc.2.2.1
    have := hBlc.2.2.2 n₁ _ _ (isLogDiscrepancy_ofPrimeDivisor hXn hK₁ hRC₁ P)
    linarith
  -- lowering `⌊B⌋` by a general member of a free linear system
  obtain ⟨f, T, hf1, hf0, hfT, hsnc⟩ :=
    exists_unit_principalDivisor hXn hXsm hBsnc A hA hA0 hAB hAfloor
  have hevX := eventually_isRealKltPair_add_smul hXn hXsm hKX hB0 hB1 f T hf1 hf0 hfT hsnc
  -- the map of function fields induced by `φ`, and the transport `f_Y` of `f`
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, GX₀, GY₀, hR₀⟩ := hY.exists_resolution
  have : IsDominant p₀ := hR₀.isBirationalMorphism_left.isDominant
  have : IsDominant q₀ := hR₀.isBirationalMorphism_right.isDominant
  obtain ⟨θ, hθbij, hθ⟩ := exists_ringHom_of_specMap _ p₀ q₀
    hR₀.isBirationalMorphism_left.functionFieldMap_bijective
    hR₀.isBirationalMorphism_right.functionFieldMap_bijective
    (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p₀ q₀ h₀ hR₀.isInverse
      hR₀.compHom_eq)
  set Zx := MMP.Mori.pointComponent (genericPoint X)
  set Zy := MMP.Mori.pointComponent (genericPoint Y)
  obtain ⟨t, ht⟩ := hθbij.2 (MMP.Threefold.Mori.Helpers.evalFF Zx (f : RationalFunctions X))
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact (f.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Zx)).ne_zero ht.symm
  obtain ⟨fY, hfY⟩ := exists_unit_evalFF_eq Zy ht0
  have hf : θ (MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y)) =
      MMP.Threefold.Mori.Helpers.evalFF Zx (f : RationalFunctions X) := by
    rw [hfY, ht]
  -- the lowered boundary on `Y` is effective for small `c`
  have hBY0 : ∀ F, 0 ≤ BY.coeff F := hY.isRealDltPair.1.2.1
  have hevY := eventually_coeff_nonneg_add_smul_principalDivisor hR₀ hXn hYn θ hθ f fY Zx Zy hf
    hB0 hBY0 hY.coeff_boundary hf0
  obtain ⟨c, ⟨⟨hΔ0, hΔklt⟩, hΔY0⟩, -⟩ := ((hevX.and hevY).and self_mem_nhdsWithin).exists
  -- the comparison on the given resolution, and klt on `Y`
  obtain ⟨L₀, hR₀'⟩ := exists_isLogComparisonResolution_add_smul hR₀ θ hθ f fY Zx Zy hf c
  have hkltY := isLogDiscrepancy_pos_of_isLogComparisonResolution hR₀' hXn hYn hKX hKY
    hΔklt.2.2.2
  have hRCY : RDivisor.IsRCartier (Divisor.toRDivisor KY +
      (BY + c • Divisor.toRDivisor (principalDivisor fY))) := by
    obtain ⟨m, r, L, -, hLc, hD, -, -⟩ := hR₀'.isRCartierPullback_right
    refine ⟨m, r, L, hLc, fun Γ => ?_⟩
    rw [← MMP.Flips.coeff_sum_smul_toRDivisor, ← hD]
    rfl
  have hRCX : RDivisor.IsRCartier (Divisor.toRDivisor KX +
      (B + c • Divisor.toRDivisor (principalDivisor f))) :=
    isRCartier_of_isSmoothScheme hXsm _
  refine ⟨B + c • Divisor.toRDivisor (principalDivisor f),
    BY + c • Divisor.toRDivisor (principalDivisor fY), hΔ0, hΔklt,
    ⟨1, fun _ => c, fun _ => f, fun P => ?_⟩, hΔY0, ⟨hYn, fun F => ?_, ⟨nY, KY, hKY, ?_⟩, hkltY⟩,
    fun W _ _ _ sW p q h GX GY hR => ?_, ?_⟩
  · rw [coeff_add_smul_principalDivisor, Fin.sum_univ_one]
  · have := hkltY nY _ _ (isLogDiscrepancy_ofPrimeDivisor hYn hKY hRCY F)
    linarith
  · exact hRCY
  · obtain ⟨L, hRL⟩ := exists_isLogComparisonResolution_add_smul hR θ hθ f fY Zx Zy hf c
    exact ⟨_, _, hRL, add_sub_add_right_eq_sub _ _ _⟩
  · intro E hE hex ψ hψ EY hEY d a a' ha ha'
    obtain ⟨W, _, _, _, sW, p, q, h, GX, GY, hR, hzero⟩ := hex
    obtain ⟨L, hRL⟩ := exists_isLogComparisonResolution_add_smul hR θ hθ f fY Zx Zy hf c
    have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
    obtain ⟨E', hE'tr, hpE', hiso⟩ := exists_transformPrimeDivisor_eq_some_of_isInverse hXn p h
      (isNormalVariety_comp_left hR) hR.isBirationalMorphism_left hR.isInverse E
    have h0 : ((GX + c • Divisor.toRDivisor L) - (GY + c • Divisor.toRDivisor L)).coeff E' = 0 := by
      rw [add_sub_add_right_eq_sub]
      exact hzero E' hE'tr
    have haa' := logDiscrepancy_eq_of_coeff_sub_eq_zero hRL hXn hYn hKX hKY hψ θ hθ E E' hpE' h0
      EY hEY ha ha'
    have ha1 := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
      (isLogDiscrepancy_ofPrimeDivisor hXn hKX hRCX E)
    refine ⟨hkltY _ _ _ ha', haa', ?_⟩
    rw [ha1]
    linarith [hΔ0 E]

end KltPerturbation

end MMP.Fourfold
