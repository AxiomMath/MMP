module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SncStrata.ZeroPlaceExtraction
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.BlowupSequence
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre

/-!
# An ample plt reference for a floor component of a log minimal model

Let `X` be a smooth projective variety and `(X, B + C)` an snc dlt pair with real boundary, where
`B, C ≥ 0`, no component of `C` lies in `⌊B⌋`, and `B ≥ A` for an effective ample `ℚ`-divisor
`A` with no component in `⌊B⌋`. Let `0 < t < 1` and let `(Y, B_Y + t C_Y)` be a nef log
birational model of `(X, B + t C)`: `Y` is projective and `ℚ`-factorial, the pair is dlt,
`C_Y = φ_* C`, `B_Y` is `φ_* B` plus every prime of `Y` exceptional over `X` with coefficient
one, and the comparison of adjoints on a common resolution is effective. Suppose every new prime
of `Y` has log discrepancy zero over `(X, B)`.

Then every component `E` of `⌊B_Y⌋` has a *plt reference*: a smooth projective variety `W`
with a birational morphism `p : W ⟶ X`, an effective plt boundary `B'` on `W` whose only
reduced component is the prime `E_W` of `W` with transform `E`, and an effective ample
`ℚ`-divisor `A' ≤ B'` not containing `E_W`, together with a plt boundary `B'_Y` on `Y` with
`K_Y + B'_Y ∼_ℚ K_Y + B_Y`, whose only reduced component is `E`, which contains the transform
of `A'`, and for which `(Y, B'_Y + t C_Y)` is plt. Every prime extracted by `W ⤏ Y` has order
zero on `A'`, and `E_W`, a component of an snc divisor, is normal.
When `E` is the transform of a component of `⌊B⌋`, one may take `W = X`.

For a new prime `E`, `W` is obtained by stratum blow-ups of `⌊B⌋` extracting `E`; the boundary
`B'` is the crepant boundary lowered by `p^*A + δ F` and raised by a general member
`A' ∼_ℚ p^*A + δ F`, where `F` is relatively ample and vanishes, among the floor components,
exactly at `E`. Then `B'_Y = B_Y + div_ℚ(f)` for the rational principal divisor
`div_ℚ(f) = B' - B_W`.

## Main results

* `MMP.Fourfold.exists_pltReference_of_isNefLogBirationalModel`

## Implementation notes

* A pair `(V, Δ)` with real boundary is plt when it is lc (`MMP.Fourfold.IsRealLcPair`) and every
  exceptional divisor over `V` has positive log discrepancy (`MMP.Intersection.IsLogDiscrepancy`);
  this is the real form of `MMP.Mori.IsPltPair`.
* `K_Y + B'_Y ∼_ℚ K_Y + B_Y` is stated as `m (B'_Y - B_Y) = div(f)` for an integer `m > 0` and a
  unit `f` of `k(Y)`, which is `ℚ`-linear equivalence and implies `ℝ`-linear equivalence.
* The map `W ⤏ Y` is a birational map `ψ` with `ψ = φ ∘ p`, pinned on function fields:
  `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `ψ` at the generic point of `W`. "`W = X`" is
  `p` an isomorphism.
* A prime `G` of `Y` extracted by `ψ` has order zero on the effective `ℚ`-Cartier divisor `A'`
  when the centre on `W` of every divisor over `W` realizing `G` is not contained in `Supp A'`.
  It is also stated pointwise: every partial map `Y ⇢ W` representing `ψ⁻¹` and defined at `η_G`
  sends `η_G` off `Supp A'`.
* The model is a `MMP.Fourfold.IsNefLogBirationalModel`; a `MMP.Fourfold.IsRealLogMinimalModel`
  is one.
* `k` is algebraically closed of characteristic zero; the source works over `ℂ`.

## References

* The proof builds `p : W ⟶ X` and a relatively ample `F` on `W` vanishing at the strict
  transform `E_W` and positive along the other primes over `⌊B⌋`, then a general member
  `Z ∼ n m (p^*A + δ F)` avoiding the centres on `W` of the primes extracted by `W ⤏ Y`. With
  `c = 1/s` small and `Z - n m (p^*A + δ F) = div f`, `B' = B_W + c div f`, `A' = c Z` and
  `B'_Y = B_Y + c div f`. Effectivity of `B'_Y` follows from `c` small (finitely many primes meet
  `div f`), and the bound `< 1` off `E` from the comparison of log discrepancies on a common
  resolution. Transforms of prime divisors under `W ⤏ Y` are computed through valuations.
-/

namespace MMP.Fourfold.PltReference

open CategoryTheory AlgebraicGeometry MMP.Fourfold
open MMP.Threefold.Resolution (eq_of_genericPoint_mem_support)
open MMP.Positivity (PrimeDivisor.genericPoint_mem_support')

universe u

section LogResolutionTest

open MMP.Mori TopologicalSpace

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
    change η ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
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
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ n := (WithBot.coe_le_coe.mpr hle).trans hc
  exact_mod_cast this

end LogResolutionTest

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

omit [IsAlgClosed k] [CharZero k] in
/-- The log discrepancy of a prime divisor `P` of `X` with respect to an `ℝ`-divisor `B` with
`K + B` `ℝ`-Cartier is `1 - coeff_P B`. -/
public theorem isLogDiscrepancy_ofPrimeDivisor [PerfectField k] [CompactSpace X]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B))
    (P : MMP.Mori.PrimeDivisor X) :
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
    · exact fun b _ hb => by simp [hb]
    · exact fun h' => absurd h h'
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : b ≠ Γ := fun h' => h (h' ▸ hb)
    simp [this]

/-- A real function below one on a finite set is bounded there by some `t < 1`. -/
theorem exists_lt_one_forall_le {α : Type*} (S : Finset α) (f : α → ℝ)
    (h : ∀ P ∈ S, f P < 1) : ∃ t < 1, ∀ P ∈ S, f P ≤ t := by
  classical
  refine ⟨(insert 0 (S.image f)).max' (Finset.insert_nonempty _ _),
    (Finset.max'_lt_iff _ _).mpr fun y hy => ?_, fun P hP =>
      Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP))⟩
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact one_pos
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hy
    exact h P hP

/-- A real function below one on a finite set is bounded there by a positive rational `q < 1`. -/
theorem exists_rat_pos_lt_one_forall_le {α : Type*} (S : Finset α) (f : α → ℝ)
    (h : ∀ P ∈ S, f P < 1) : ∃ q : ℚ, (0 : ℝ) < q ∧ (q : ℝ) < 1 ∧ ∀ P ∈ S, f P ≤ q := by
  obtain ⟨t, ht1, ht⟩ := exists_lt_one_forall_le S f h
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (max_lt ht1 one_pos : max t 0 < 1)
  exact ⟨q, (le_max_right _ _).trans_lt hq0, hq1,
    fun P hP => (ht P hP).trans ((le_max_left _ _).trans_lt hq0).le⟩

omit [IsAlgClosed k] in
/-- On a smooth variety, raising the coefficients of a boundary supported on a finite set `S` of
prime divisors lowers its log discrepancies. -/
private theorem exists_isLogDiscrepancy_le_of_coeff_le (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (S : Finset (MMP.Mori.PrimeDivisor X)) {B B' : RDivisor X}
    (hB : ∀ Γ, Γ ∉ S → B.coeff Γ = 0) (hB' : ∀ Γ, Γ ∉ S → B'.coeff Γ = 0)
    (hle : ∀ P ∈ S, B.coeff P ≤ B'.coeff P) {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ a', MMP.Intersection.IsLogDiscrepancy sX n B' D a' ∧ a' ≤ a := by
  classical
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  have hf : IsProper D.f := ha.2.1
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
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
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC i)
  -- the log discrepancy of a boundary supported in `S`, through this presentation
  have hb : ∀ B : RDivisor X, (∀ Γ, Γ ∉ S → B.coeff Γ = 0) →
      MMP.Intersection.IsLogDiscrepancy sX n B D
        (1 + (D.ordPullback ω : ℝ) - ∑ i, r B.coeff i * ((C' i).coeff D.E : ℝ)) := by
    intro B hB
    refine ⟨hX, hf, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, S.card + 1, r B.coeff, C, C', hC,
      fun Γ => ?_, fun i => ⟨_, hC' i⟩, rfl⟩
    rw [hpres, hω Γ]
    split_ifs with h
    · rfl
    · rw [hB Γ h]
  refine ⟨_, hb B' hB', ?_⟩
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha (hb B hB), sub_le_sub_iff_left,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [r, Fin.cons_zero, Fin.cons_succ]
  refine add_le_add_right (Finset.sum_le_sum fun i _ => ?_) _
  have hc0 : (0 : ℝ) ≤ ((C' i.succ).coeff D.E : ℝ) := by
    have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hC i.succ)
      (V := ⊤) (fun P _ => ?_) (hC' i.succ) D.E ((D.E.genericPoint_mem_iff _).mp trivial)
    · exact_mod_cast hnn
    · simp only [C, Fin.cons_succ, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> norm_num
  exact mul_le_mul_of_nonneg_right (hle _ (S.equivFin.symm i).2) hc0

/-- **Real snc pairs are klt.** On a smooth variety `X` over an algebraically closed field of
characteristic zero, an effective `ℝ`-divisor `Δ` whose support lies in a finite set `S` of prime
divisors with `∑_{E ∈ S} E` simple normal crossing, and whose coefficients are less than one, is
a klt boundary. The log discrepancies of `Δ` dominate those of the rational snc boundary
`q ∑_{E ∈ S} E`, for a rational `q < 1` above every coefficient of `Δ`. -/
private theorem isRealKltPair_of_isSNC (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {Δ : RDivisor X}
    (S : Finset (MMP.Mori.PrimeDivisor X)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (h0 : ∀ P, 0 ≤ Δ.coeff P) (h1 : ∀ P, Δ.coeff P < 1) : IsRealKltPair sX Δ := by
  classical
  have hΔS : ∀ Γ, Γ ∉ S → Δ.coeff Γ = 0 := fun Γ hΓ => by
    by_contra h
    exact hΓ (hS (Finsupp.mem_support_iff.mpr h))
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
  obtain ⟨q, -, hq1, hq⟩ := exists_rat_pos_lt_one_forall_le S Δ.coeff fun P _ => h1 P
  let Δq : QDivisor X := ∑ E ∈ S, Finsupp.single E (q : ℚ)
  have hΔq : ∀ Γ, Δq.coeff Γ = if Γ ∈ S then (q : ℚ) else 0 := fun Γ => by
    simp only [Δq, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hΔqR : ∀ Γ, Γ ∉ S → (QDivisor.toRDivisor Δq).coeff Γ = 0 := fun Γ hΓ => by
    rw [QDivisor.coeff_toRDivisor, hΔq, if_neg hΓ, Rat.cast_zero]
  -- the rational snc boundary `q ∑_{E ∈ S} E` is klt
  have hsuppS : ∀ E ∈ S, E ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support := fun E hE => by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq', if_pos hE]
    exact one_ne_zero
  have hsncq : Δq.IsSNC sX := hsnc.of_support_subset fun E hE => by
    refine hsuppS E ?_
    by_contra h
    exact (Finsupp.mem_support_iff.mp hE) (by rw [← DivisorWithCoeffs.coeff_apply, hΔq, if_neg h])
  have hklt := MMP.Mori.isKltPair_of_isSNC sX hX hsm hK hsncq fun E => by
    rw [hΔq]
    split_ifs
    · exact_mod_cast hq1
    · exact zero_lt_one
  obtain ⟨a', ha', hle⟩ := exists_isLogDiscrepancy_le_of_coeff_le hX hsm hK S hΔS hΔqR
    (fun P hP => by
      rw [QDivisor.coeff_toRDivisor, hΔq, if_pos hP]
      exact hq P hP) ha
  exact (pos_of_isLogDiscrepancy_of_isKltPair hX hklt ha').trans_le hle

end RealSNC

/-- An invertible module in the sense of `Stacks.Ample.IsInvertibleModule` is invertible as a
sheaf of modules. -/
local instance isInvertible_of_isInvertibleModule {Y : Scheme.{u}} (L : Y.Modules)
    [h : Stacks.Ample.IsInvertibleModule Y L] :
    SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L := h

/-! ### Zero schemes of sections of divisorial sheaves -/

section Bertini

private theorem support_sum_single {Y : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

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
    ⟨E.genericPoint, PrimeDivisor.genericPoint_mem_support' E, hE⟩
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
  have hne' : (Y.presheaf.germ V _ hE).hom r ≠ 0 :=
    fun h0 => hne (by rw [hgerm, h0, map_zero])
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
    (hU : Dense (U : Set
      (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)))) :
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
  have h := Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X _ (σ'.s j)
  have hx : x ∈ (Stacks.SheafOfModules.nonvanishingOpen _ (σ'.s j) : Set X) := hj
  rw [h] at hx
  simp only [Equiv.symm_apply_apply]
  exact hx

end GlobalGeneration

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
      W.fromSpecStalk (genericPoint W) ≫ p :=
    h1.trans (Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _)
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

/-- A ring map `θ : k(Y) → k(X)` inducing `φ` at the generic point, read off one common
resolution. -/
private theorem exists_ringHom_specMap_eq {X Y W : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral W] (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
    [IsDominant p] [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hq : Function.Bijective (functionFieldMap q))
    (hinv : RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ) :
    ∃ θ : Y.functionField →+* X.functionField, Function.Bijective θ ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
        φ.fromFunctionField :=
  exists_ringHom_of_specMap _ p q hp hq
    (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp)

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
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

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
    by_cases hEF : E = F <;> simp [hEF]

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
    rwa [if_pos hP] at this
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
  have hKWp : KW.IsCanonicalDivisor (p ≫ sX) nW := by rwa [hR.comp_eq_left]
  have hKWq : KW.IsCanonicalDivisor (q ≫ sY) nW := by rwa [hR.comp_eq_right]
  have hdM : topologicalKrullDim Y = nW := hdimY.symm.trans hKW.topologicalKrullDim_eq
  obtain ⟨ωX, hωX0, hωX, hωXW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hXn hWnp hpb hdimX hKWp
  obtain ⟨ωY, hωY0, hωY, hωYW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hYn hWnq hqb hdM hKWq
  exact ⟨by exact_mod_cast hKY.topologicalKrullDim_eq.symm.trans hdM, KW, hKWp, hKWq,
    ⟨ωX, hωX0, hωX.trans hKWX, hωXW⟩, ωY, hωY0, hωY.trans hKWY, hωYW⟩

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

end NefModel

/-! ### Real snc pairs with a single reduced component are plt -/

section RealSNCPlt

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

open Classical in
/-- **Real snc pairs with one reduced component are plt.** On a smooth variety `X` over an
algebraically closed field of characteristic zero, let `Δ` be an effective `ℝ`-divisor supported
on a finite set `S` of prime divisors with `∑_{E ∈ S} E` snc, with `coeff_{E₀} Δ ≤ 1` for one
`E₀ ∈ S` and every other coefficient less than one. Then every log discrepancy `a(D; X, Δ)` is
nonnegative, and it vanishes only for the valuation of `E₀`. For exceptional `D` the log
discrepancies of `Δ` dominate those of the rational snc boundary `E₀ + q ∑_{E ∈ S, E ≠ E₀} E`,
for a rational `q < 1` above every other coefficient of `Δ`, whose discrepancy is at least `-q`
by the snc formula. -/
private theorem isLogDiscrepancy_nonneg_of_isSNC (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : RDivisor X} (S : Finset (MMP.Mori.PrimeDivisor X)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (h0 : ∀ P, 0 ≤ Δ.coeff P) (E₀ : MMP.Mori.PrimeDivisor X) (hE₀S : E₀ ∈ S)
    (hE₀ : Δ.coeff E₀ ≤ 1) (h1 : ∀ P, P ≠ E₀ → Δ.coeff P < 1)
    {n' : ℕ} {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n' Δ D a) :
    0 ≤ a ∧ (a = 0 → D.valuation = (DivisorOver.ofPrimeDivisor k hX E₀).valuation) := by
  have hΔS : ∀ Γ, Γ ∉ S → Δ.coeff Γ = 0 := fun Γ hΓ => by
    by_contra h
    exact hΓ (hS (Finsupp.mem_support_iff.mpr h))
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  have : CompactSpace X := by
    have := hX.1
    exact QuasiCompact.compactSpace_of_compactSpace sX
  by_cases hD : D.IsExceptional
  swap
  · obtain ⟨P, hv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
    have hb := isLogDiscrepancy_ofPrimeDivisor hX hK (B := Δ) (isRCartier_of_isSmoothScheme hsm _) P
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb hv]
    by_cases hP : P = E₀
    · subst hP
      exact ⟨by linarith, fun _ => hv⟩
    · have := h1 P hP
      exact ⟨by linarith, fun h => absurd h (by linarith)⟩
  suffices hpos : 0 < a from ⟨hpos.le, fun h => absurd h hpos.ne'⟩
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨q, hq0', hq1, ht⟩ := exists_rat_pos_lt_one_forall_le (S.erase E₀) Δ.coeff
    fun P hP => h1 P (Finset.mem_erase.mp hP).1
  let Δq : QDivisor X := ∑ E ∈ S, Finsupp.single E (if E = E₀ then (1 : ℚ) else q)
  have hΔq : ∀ Γ, Δq.coeff Γ = if Γ ∈ S then (if Γ = E₀ then (1 : ℚ) else q) else 0 := fun Γ => by
    simp only [Δq, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hΔqR : ∀ Γ, Γ ∉ S → (QDivisor.toRDivisor Δq).coeff Γ = 0 := fun Γ hΓ => by
    rw [QDivisor.coeff_toRDivisor, hΔq, if_neg hΓ, Rat.cast_zero]
  have hsuppq : Δq.support ⊆ S := fun E hE => by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hE) (by rw [← DivisorWithCoeffs.coeff_apply, hΔq, if_neg h])
  have hq1' : (q : ℚ) < 1 := by exact_mod_cast hq1
  have hq0'' : (0 : ℚ) < q := by exact_mod_cast hq0'
  have hcoeffq : ∀ E ∈ S, Δq.coeff E ≤ 1 := fun E hE => by
    rw [hΔq, if_pos hE]
    split_ifs
    · exact le_rfl
    · exact hq1'.le
  obtain ⟨a', ha', hle⟩ := exists_isLogDiscrepancy_le_of_coeff_le hX hsm hK S hΔS hΔqR
    (fun P hP => by
      rw [QDivisor.coeff_toRDivisor, hΔq, if_pos hP]
      split_ifs with h
      · simp only [h, Rat.cast_one]
        exact hE₀
      · exact ht P (Finset.mem_erase.mpr ⟨h, hP⟩)) ha
  -- the discrepancy of `D` with respect to `Δq` is at least `-q`
  have hP : MMP.Mori.IsPair sX Δq :=
    ⟨hX, n', K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  have h2 : 2 ≤ n' := two_le_of_isExceptional hK.topologicalKrullDim_eq D hD
  have hdisc := MMP.Mori.discrep_le hD hc
  rw [MMP.Mori.discrep_eq_of_isSNC sX hX hsm h2 hK S hsuppq hsnc hcoeffq] at hdisc
  have hbound : (((-q : ℚ) : ℝ) : EReal) ≤ ((c : ℝ) : EReal) := by
    refine le_trans (le_inf (le_inf
      (le_iInf₂ fun E hE => le_iInf₂ fun F hF => le_iInf₂ fun hEF _ => ?_)
      (le_iInf₂ fun E hE => ?_)) ?_) hdisc
    · rw [EReal.coe_le_coe_iff, Rat.cast_le, hΔq, hΔq, if_pos hE, if_pos hF]
      split_ifs with h₁ h₂ h₂
      · exact absurd (h₁.trans h₂.symm) hEF
      · linarith
      · linarith
      · linarith
    · rw [EReal.coe_le_coe_iff, Rat.cast_le]
      linarith [hcoeffq E hE]
    · exact_mod_cast (show ((-q : ℚ) : ℝ) ≤ 1 by push_cast; linarith)
  have hc' : ((-q : ℚ) : ℝ) ≤ (c : ℝ) := EReal.coe_le_coe_iff.mp hbound
  have hlogq := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha'
  push_cast at hc'
  linarith

end RealSNCPlt

/-! ### Transfer of log discrepancies along a comparison, with valuations -/

section Transfer

open MMP.Flips
open scoped WithZero

variable {k : Type u} [Field k] [PerfectField k]
variable {X M W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sM : M ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
  [LocallyOfFiniteType sM] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **Comparison of log discrepancies along a common resolution, valuation by valuation.** In the
situation of a common resolution `p : W ⟶ X`, `q : W ⟶ M` with `G_X = p^*(K_X + D_X)`,
`G_M = q^*(K_M + D_M)` and `G_X - G_M ≥ 0`, every log discrepancy `a` of a divisor `E` over
`(M, D_M)` bounds from above a log discrepancy `b` over `(X, D_X)` of a divisor `E₀` over `X` with
the same valuation: both are `ord_w` read through `q^*` and `p^*` for one valuation `w` of
`k(W)`. -/
private theorem exists_isLogDiscrepancy_le_of_crepant_le {p : W ⟶ X} {q : W ⟶ M} [IsProper p]
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
    (d : ℕ) (E : DivisorOver k sM) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sM d DM E a) :
    ∃ (E₀ : ProperDivisorOver k sX) (b : ℝ) (w : Valuation W.functionField ℤᵐ⁰),
      MMP.Intersection.IsLogDiscrepancy sX d DX E₀.toDivisorOver b ∧ b ≤ a ∧
      E.valuation = w.comap (functionFieldMap q) ∧
      E₀.valuation = w.comap (functionFieldMap p) := by
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
    rwa [hωMW, add_sub_cancel]
  have h1 := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hMn hωM0 hKMc hKDM q hWnq hqb
    hDYq (by rwa [hωMW]) E' b).mp (by
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
    rwa [hωXW, add_sub_cancel]
  obtain ⟨-, -, -, E₀, ω₀, m₀, r₀, L₀, hE₀, hdiv₀, hw₀⟩ :=
    (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hXn hωX0 hKXc hKDX p hWnp hpb hDYp
      (by rwa [hωXW]) E'' b').mpr (by rw [hωXW, hE'']; exact isDiscrepancy_of_eq hss h2)
  refine ⟨E₀, 1 + b', E'.valuation,
    isLogDiscrepancy_of_isDiscrepancyWith (by rwa [hdiv₀]) hw₀, by linarith,
    hE'.symm, by rw [hE₀, hE'']⟩

/-- **Log discrepancies along a crepant pull-back, valuation by valuation.** For a proper
birational morphism `p : W ⟶ X` of normal varieties and the crepant pull-back
`K_W + D_W = p^*(K_X + D_X)` (with `K_W = div(p^*ω)`), every log discrepancy `b` of a divisor
`E₀` over `(X, D_X)` is the log discrepancy over `(W, D_W)` of a divisor `E₁` over `W` with
`ord_{E₁} ∘ p^* = ord_{E₀}`. -/
private theorem exists_isLogDiscrepancy_of_crepant (hXn : IsNormalVariety k sX) {n : ℕ}
    (hdX : topologicalKrullDim X = n) {ωX : RationalPluriForms sX n 1} (hωX0 : ωX ≠ 0)
    (hKXc : (divisorOfForm ωX).IsCanonicalDivisor sX n) (p : W ⟶ X) [IsProper p]
    (hWn : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    [LocallyOfFiniteType (p ≫ sX)] [AlgebraicGeometry.IsVariety k (p ≫ sX)]
    {DX : RDivisor X} {DW : RDivisor W}
    (hDW : haveI : IsDominant p := hpb.isDominant
      MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + DX)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX)) + DW))
    (hKW : haveI : IsDominant p := hpb.isDominant
      (divisorOfForm (pullbackRationalPluriForms sX p ωX)).IsCanonicalDivisor (p ≫ sX) n)
    (d : ℕ) (E₀ : ProperDivisorOver k sX) (b : ℝ)
    (hb : MMP.Intersection.IsLogDiscrepancy sX d DX E₀.toDivisorOver b) :
    haveI : IsDominant p := hpb.isDominant
    ∃ E₁ : ProperDivisorOver k (p ≫ sX), E₁.valuation.comap (functionFieldMap p) = E₀.valuation ∧
      MMP.Intersection.IsLogDiscrepancy (p ≫ sX) d DW E₁.toDivisorOver b := by
  haveI : IsDominant p := hpb.isDominant
  obtain rfl : d = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hb).symm.trans hdX
  obtain ⟨m, r, L, L', hLc, hsumX, hpbL, hsumW⟩ := id hDW
  obtain ⟨b₀, hb₀⟩ := exists_isDiscrepancyWith hXn hdX hωX0 hLc hsumX E₀
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique hb
    (isLogDiscrepancy_of_isDiscrepancyWith hKXc hb₀)]
  have hKDX : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + DX) :=
    ⟨m, r, L, hLc, by rw [hsumX]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨E', hE'⟩ := exists_properDivisorOver_comap_eq p hpb E₀
  have h1 := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hXn hωX0 hKXc hKDX p hWn hpb
    hDW hKW E' b₀).mp (by
      rw [hE']
      exact ⟨hKXc, hKDX, hasNonemptyCenter_valuation E₀, E₀, ωX, m, r, L, rfl, rfl, hb₀⟩)
  obtain ⟨-, -, -, E₂, ω₂, m₂, r₂, L₂, hE₂, hdiv₂, hw₂⟩ := h1
  exact ⟨E₂, by rw [hE₂, hE'], isLogDiscrepancy_of_isDiscrepancyWith (by rwa [hdiv₂]) hw₂⟩

end Transfer

/-! ### Transforms of prime divisors under a rational map, through valuations -/

section CenterTransform

open MMP.Mori

set_option backward.isDefEq.respectTransparency.types false in
/-- The closed point of `Spec 𝒪_{W,x}` maps to `g(x)` under a partial map `g` defined at `x`. -/
private theorem fromSpecStalkOfMem_closedPoint {W Y : Scheme.{u}} (g : W.PartialMap Y) {x : W}
    (hx : x ∈ g.domain) :
    g.fromSpecStalkOfMem hx (IsLocalRing.closedPoint (W.presheaf.stalk x)) = g.hom ⟨x, hx⟩ := by
  change g.hom (g.domain.fromSpecStalkOfMem x hx (IsLocalRing.closedPoint _)) = _
  congr 1
  apply g.domain.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- At a point `x` of the domain of a partial map `g : W ⇢ Y` inducing `θ : k(Y) → k(W)` at the
generic point, `θ` restricted to the local ring of `Y` at the image of `x` is the local map to
`𝒪_{W,x}` followed by `𝒪_{W,x} → k(W)`. -/
private theorem stalkClosedPointTo_comp_stalkSpecializes_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] (g : W.PartialMap Y) (θ : Y.functionField →+* W.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = g.fromFunctionField)
    {x : W} (hx : x ∈ g.domain) :
    Scheme.stalkClosedPointTo (g.fromSpecStalkOfMem hx) ≫
        W.presheaf.stalkSpecializes (genericPoint_specializes x) =
      Y.presheaf.stalkSpecializes (genericPoint_specializes _) ≫ CommRingCat.ofHom θ := by
  have hη : genericPoint W ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  apply Spec.map_injective
  rw [← cancel_mono (Y.fromSpecStalk _)]
  have h2 : Spec.map (W.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
      g.domain.fromSpecStalkOfMem x hx = g.domain.fromSpecStalkOfMem (genericPoint W) hη := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Spec.map_comp,
    Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  refine Eq.trans ?_ hθ.symm
  change Spec.map _ ≫ g.domain.fromSpecStalkOfMem x hx ≫ g.hom = _
  rw [← Category.assoc, h2]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **The valuation of a prime divisor dominates the local ring at its image.** If a partial map
`g : W ⇢ Y` induces `θ : k(Y) → k(W)` and is defined at the generic point of a prime divisor `P`
of `W`, then `ord_P ∘ θ` is at most one on `𝒪_{Y, g(η_P)}` and less than one on its maximal
ideal. -/
private theorem divisorialValuation_comap_dominates {W Y : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] (g : W.PartialMap Y)
    (θ : Y.functionField →+* W.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = g.fromFunctionField)
    (P : MMP.Mori.PrimeDivisor W) (hP : P.genericPoint ∈ g.domain) :
    (∀ a : Y.presheaf.stalk (g.hom ⟨P.genericPoint, hP⟩),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.hom ⟨P.genericPoint, hP⟩)),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) < 1 := by
  have key := stalkClosedPointTo_comp_stalkSpecializes_eq g θ hθ hP
  have hval : ∀ a : Y.presheaf.stalk
      (g.fromSpecStalkOfMem hP (IsLocalRing.closedPoint (W.presheaf.stalk P.genericPoint))),
      θ (algebraMap _ Y.functionField a) = algebraMap P.localRing W.functionField
        ((Scheme.stalkClosedPointTo (g.fromSpecStalkOfMem hP)).hom a) := fun a => by
    have := congrArg (fun φ => φ.hom a) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  have hdom : (∀ a : Y.presheaf.stalk
      (g.fromSpecStalkOfMem hP (IsLocalRing.closedPoint (W.presheaf.stalk P.genericPoint))),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk
      (g.fromSpecStalkOfMem hP (IsLocalRing.closedPoint (W.presheaf.stalk P.genericPoint)))),
      (P.divisorialValuation.comap θ) (algebraMap _ Y.functionField a) < 1 := by
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · rw [Valuation.comap_apply, hval, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
      exact ⟨_, rfl⟩
    · rw [Valuation.comap_apply, hval]
      refine (P.divisorialValuation_algebraMap_lt_one_iff _).2 ?_
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
  rw [fromSpecStalkOfMem_closedPoint g hP] at hdom
  exact hdom

/-- **Transforms of prime divisors through valuations.** Let `ψ : W ⤏ Y` be a rational map of
normal integral schemes, `Y` separated over a field, inducing the surjection
`θ : k(Y) → k(W)` at the generic point, and defined at the generic point of a prime divisor `P` of
`W`. Then `ψ_* P = G` if and only if `ord_P ∘ θ = ord_G`: both say that `ord_P ∘ θ` dominates
`𝒪_{Y, η_G}`. -/
private theorem transformPrimeDivisor_eq_some_iff_comap_eq {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated sY]
    (ψ : W.RationalMap Y) (θ : Y.functionField →+* W.functionField)
    (hθs : Function.Surjective θ)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = ψ.fromFunctionField)
    (P : MMP.Mori.PrimeDivisor W) (hP : P.genericPoint ∈ ψ.domain) (G : MMP.Mori.PrimeDivisor Y) :
    RationalMap.transformPrimeDivisor ψ P = some G ↔
      P.divisorialValuation.comap θ = G.divisorialValuation := by
  have := isSeparated_toTerminal sY
  obtain ⟨g, hgP, hg⟩ := Scheme.RationalMap.mem_domain.mp hP
  have hθg : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
      g.fromFunctionField := by
    rw [hθ, ← hg, Scheme.RationalMap.fromFunctionField_toRationalMap]
  obtain ⟨hD1, hD2⟩ := divisorialValuation_comap_dominates g θ hθg P hgP
  haveI := G.isDiscreteValuationRing_localRing
  have hG1 : ∀ a : G.localRing, G.divisorialValuation (algebraMap _ Y.functionField a) ≤ 1 :=
    fun a => (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).2 ⟨a, rfl⟩
  have hG2 : ∀ a ∈ IsLocalRing.maximalIdeal G.localRing,
      G.divisorialValuation (algebraMap _ Y.functionField a) < 1 :=
    fun a ha => (G.divisorialValuation_algebraMap_lt_one_iff a).2 ha
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hy : G.genericPoint = g.hom ⟨P.genericPoint, hgP⟩ :=
      genericPoint_eq_of_transformPrimeDivisor_eq_some h g hg hgP
    haveI := P.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    obtain ⟨ϖ', hϖ'⟩ := hθs (algebraMap P.localRing W.functionField ϖ)
    obtain ⟨ϖG, hϖG⟩ := IsDiscreteValuationRing.exists_irreducible G.localRing
    rw [← hy] at hD1 hD2
    exact MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := G.localRing)
      hD1 hD2
      ⟨ϖ', by rw [Valuation.comap_apply, hϖ', P.divisorialValuation_algebraMap_of_irreducible hϖ]⟩
      hG1 hG2 ⟨_, G.divisorialValuation_algebraMap_of_irreducible hϖG⟩
  · refine transformPrimeDivisor_eq_some_of_genericPoint_eq g hg hgP ?_
    rw [h] at hD1 hD2
    exact MMP.Positivity.DivisorOver.eq_of_dominates sY G.divisorialValuation hG1 hG2 hD1 hD2

end CenterTransform

/-! ### Relative ampleness of Cartier divisors -/

section RelAmple

open MMP.Mori MMP.Resolution TopologicalSpace

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open. -/
private theorem stacks_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : MMP.Mori.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- `𝒪_Y(mA) ≅ 𝒪_Y(A)^{⊗ m}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {V : Scheme.{u}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- **[Stacks, Tag 0C4K] for Cartier divisors.** Let `f : X ⟶ Y` and `g : Y ⟶ S` be
quasi-compact, `S` quasi-compact, `L` an `f`-ample Cartier divisor on `X` and `M` a `g`-ample
Cartier divisor on `Y` with pull-back `M' = f^*M`. Then `L + nM'` is `(f ≫ g)`-ample for all
large `n`. -/
public theorem exists_isRelativelyAmple_add_nsmul {X Y S : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace S]
    (f : X ⟶ Y) (g : Y ⟶ S) [QuasiCompact f] [QuasiCompact g]
    {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    {M : Divisor Y} (hM : M.IsCartier) (hMg : M.IsRelativelyAmple g hM)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ M.supp}
    {M' : Divisor X} (hM' : M.IsPullback f hB M') :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (L + n • M').IsRelativelyAmple (f ≫ g) (hL.add ((hM'.isCartier hM).nsmul n)) := by
  have hM'c := hM'.isCartier hM
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := hM.isInvertibleModule_divisorialSheaf
  haveI := hM'c.isInvertibleModule_divisorialSheaf
  obtain ⟨n₀, hn₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp f g _ _
    (stacks_of_isRelativelyAmple f _ hLf) (stacks_of_isRelativelyAmple g _ hMg)
  refine ⟨n₀, fun n hn => ?_⟩
  haveI := (hL.add (hM'c.nsmul n)).isInvertibleModule_divisorialSheaf
  have eB : (modulePullback f.toLRSHom.toShHom).obj M.divisorialSheaf ≅ M'.divisorialSheaf :=
    modulePullbackIso f _ ≪≫ (hM'.divisorialSheafIso (hBc := hM)).symm
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule f L.divisorialSheaf
      M.divisorialSheaf n ≅ (L + n • M').divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl _)
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f _ n ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso X _ _ eB n ≪≫
          (divisorialSheafNsmulIso hM'c n).symm) ≪≫
      hL.divisorialSheafTensorIso (hM'c.nsmul n)
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn₀ n hn))

/-- If `φ = (a, b) : W ⟶ X ×_S Y` is affine, `L` is `f`-ample and `N` is `g`-ample, then
`a^* L ⊗ b^* N` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_tensorModules_of_isAffineHom {S X Y W : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    [IsAffineHom (Limits.pullback.lift a b h)] (L : X.Modules) (N : Y.Modules)
    [IsInvertibleModule X L] [IsInvertibleModule Y N]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (a ≫ f)
      (tensorModules W ((modulePullback a.toLRSHom.toShHom).obj L)
        ((modulePullback b.toLRSHom.toShHom).obj N)) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (Limits.pullback.lift a b h) (Limits.pullback.fst f g ≫ f) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor f g L N hL hN)
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso f g
    (Limits.pullback.lift a b h) L N
  simp only [Limits.pullback.lift_fst, Limits.pullback.lift_snd] at e
  rw [← Category.assoc, Limits.pullback.lift_fst] at h1
  exact (isRelativelyAmple_congr _ _ _ e).mp h1

/-- For a quasi-compact separated morphism `f`, the sum of two `f`-ample Cartier divisors is
`f`-ample: `𝒪(A + B) ≅ Δ^*(𝒪(A) ⊠ 𝒪(B))` and the diagonal of `f` is affine. -/
private theorem isRelativelyAmple_add {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {A B : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    (hB : B.IsCartier) (hBf : B.IsRelativelyAmple f hB) :
    (A + B).IsRelativelyAmple f (hA.add hB) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  haveI := (hA.add hB).isInvertibleModule_divisorialSheaf
  haveI : IsAffineHom (Limits.pullback.lift (𝟙 X) (𝟙 X) (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f)) :=
    show IsAffineHom (Limits.pullback.diagonal f) from inferInstance
  have h := isRelativelyAmple_tensorModules_of_isAffineHom (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f) _ _
    (stacks_of_isRelativelyAmple f _ hAf) (stacks_of_isRelativelyAmple f _ hBf)
  rw [Category.id_comp] at h
  refine MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ ?_).mp h)
  exact tensorModulesMapIso X (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _)
    (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _) ≪≫
    hA.divisorialSheafTensorIso hB

/-- For a quasi-compact separated morphism `f`, every positive multiple of an `f`-ample Cartier
divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    (n : ℕ) (hn : 0 < n) : (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simpa using hLf
    · convert isRelativelyAmple_add _ (ih hn') _ hLf using 2
      rw [succ_nsmul]

/-- Relative ampleness of a Cartier divisor does not depend on the proof that it is Cartier, and
is transported along equalities of divisors. -/
private theorem isRelativelyAmple_of_eq {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} {A B : Divisor X}
    (hAB : A = B) (hA : A.IsCartier) (hB : B.IsCartier) (hAf : A.IsRelativelyAmple f hA) :
    B.IsRelativelyAmple f hB := by
  subst hAB
  exact hAf

/-- Every Cartier divisor is ample relative to an isomorphism. -/
private theorem isRelativelyAmple_of_isIso {X Y : Scheme.{u}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {L : Divisor X}
    (hL : L.IsCartier) : L.IsRelativelyAmple e hL := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  refine ⟨V, hV, hyV, ?_⟩
  haveI : IsAffine (e ⁻¹ᵁ V) := hV.preimage e
  haveI : CompactSpace (e ⁻¹ᵁ V) := inferInstance
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ V).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- Relative ampleness depends only on the isomorphism class of the invertible sheaf. -/
private theorem isRelativelyAmple_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : MMP.Mori.IsRelativelyAmple f L) : MMP.Mori.IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp

end RelAmple

section AmpleFinal

open MMP.Mori

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **Ampleness of `p^*A + δF`.** If `F` is `p`-ample and `A` is ample on `X`, then `A' + δF` is
ample for every sufficiently small rational `δ > 0`, where `A' = p^*A`. -/
private theorem exists_hasRelativelyAmpleMultiple_add_smul (hX : MMP.Mori.IsProjectiveVariety k sX)
    (p : W ⟶ X) (hpv : AlgebraicGeometry.IsVariety k (p ≫ sX)) [IsProper p] {F : QDivisor W}
    (hF : F.HasRelativelyAmpleMultiple p) (A : QDivisor X) (hA : A.HasRelativelyAmpleMultiple sX)
    (hA0 : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ A.supp)
    (A' : QDivisor W) (hA' : QDivisor.IsPullback p A hA0 A') :
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
      (A' + δ • F).HasRelativelyAmpleMultiple (p ≫ sX) := by
  haveI : IsSeparated (p ≫ sX) := hpv.toIsSeparated
  haveI : QuasiCompact (p ≫ sX) := hpv.toQuasiCompact
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  obtain ⟨m, hm, L, hLc, hLF, hLa⟩ := hF
  obtain ⟨c, hc, M, hMc, hMA, hMa⟩ := hA
  obtain ⟨M', hM'A, hM'⟩ := hA' c hc M hMA hMc
  obtain ⟨n₀, hn₀⟩ := exists_isRelativelyAmple_add_nsmul p sX hLc hLa hMc hMa hM'
  have hM'c := hM'.isCartier hMc
  set n₁ := max n₀ 1 with hn₁
  have hn₁1 : 1 ≤ n₁ := le_max_right _ _
  have hK : ∀ j : ℕ, n₁ ≤ j → (L + j • M').IsRelativelyAmple (p ≫ sX)
      (hLc.add (hM'c.nsmul j)) := fun j hj => hn₀ j ((le_max_left _ _).trans hj)
  refine ⟨(m : ℚ) / (c * n₁), by positivity, fun δ hδ hδ₀ => ?_⟩
  -- `δ = a / b`
  set a : ℕ := δ.num.toNat with ha
  set b : ℕ := δ.den with hb
  have hnum : (δ.num : ℚ) = a := by
    rw [ha]; exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hδ.le)).symm
  have hδab : δ = (a : ℚ) / b := by rw [← hnum, hb, Rat.num_div_den]
  have hb0 : 0 < b := δ.den_pos
  have ha0 : 0 < a := by
    have : (0 : ℚ) < a := by
      rw [← hnum]; exact_mod_cast Rat.num_pos.mpr hδ
    exact_mod_cast this
  set s : ℕ := a * c with hs
  set r : ℕ := b * m with hr
  have hs0 : 0 < s := Nat.mul_pos ha0 hc
  have hsr : s * n₁ ≤ r := by
    have h1 : (a : ℚ) / b < m / (c * n₁) := hδab ▸ hδ₀
    have hbq : (0 : ℚ) < b := by exact_mod_cast hb0
    have hcq : (0 : ℚ) < c * n₁ := by
      have : (1 : ℚ) ≤ n₁ := by exact_mod_cast hn₁1
      have : (0 : ℚ) < c := by exact_mod_cast hc
      positivity
    rw [div_lt_div_iff₀ hbq hcq] at h1
    have : ((a * c * n₁ : ℕ) : ℚ) < (b * m : ℕ) := by push_cast; linarith
    have := (Nat.cast_lt.mp this).le
    simpa [hs, hr, mul_comm, mul_assoc, mul_left_comm] using this
  set j := r / s with hj
  set ρ := r % s with hρ
  have hjn : n₁ ≤ j := (Nat.le_div_iff_mul_le hs0).mpr (by rwa [mul_comm])
  have hrj : r = s * j + ρ := (Nat.div_add_mod r s).symm
  have hρs : ρ < s := Nat.mod_lt _ hs0
  -- the integral divisor `s L + r M' = (s - ρ)(L + j M') + ρ (L + (j + 1) M')`
  have hD : s • L + r • M' = (s - ρ) • (L + j • M') + ρ • (L + (j + 1) • M') := by
    rw [hrj]
    ext E
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, nsmul_eq_mul]
    push_cast [Nat.cast_sub hρs.le]
    ring
  have hDc : (s • L + r • M').IsCartier := (hLc.nsmul s).add (hM'c.nsmul r)
  have hamp : (s • L + r • M').IsRelativelyAmple (p ≫ sX) hDc := by
    have hK1 := hK j hjn
    have hK2 := hK (j + 1) (hjn.trans (Nat.le_succ j))
    rcases Nat.eq_zero_or_pos ρ with h0 | hρ0
    · refine isRelativelyAmple_of_eq ?_ _ _ (isRelativelyAmple_nsmul _ hK1 s hs0)
      rw [hD, h0, Nat.sub_zero, zero_smul, add_zero]
    · refine isRelativelyAmple_of_eq hD.symm _ _ (isRelativelyAmple_add _
        (isRelativelyAmple_nsmul _ hK1 (s - ρ) (Nat.sub_pos_of_lt hρs)) _
        (isRelativelyAmple_nsmul _ hK2 ρ hρ0))
  refine ⟨b * m * c, Nat.mul_pos (Nat.mul_pos hb0 hm) hc, s • L + r • M', hDc, ?_, hamp⟩
  -- the coefficients
  rw [map_add, map_nsmul, map_nsmul, hLF, hM'A]
  ext E
  simp only [DivisorWithCoeffs.coeff_add, smul_eq_mul, hδab]
  change (s : ℚ) * ((m : ℤ) * F E) + (r : ℚ) * ((c : ℤ) * A' E) =
    ((b * m * c : ℕ) : ℤ) * (A' E + (a : ℚ) / b * F E)
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  push_cast [hs, hr]
  field_simp
  ring

end AmpleFinal

/-! ### Bertini's theorem with finitely many points avoided -/

section BertiniAvoid

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

attribute [local instance] globalSectionsModule

open Classical in
/-- **Bertini's theorem for snc divisors avoiding finitely many points.** On a smooth variety
`Y` over an algebraically closed field of characteristic zero, let `D` be a Cartier divisor whose
sheaf is generated by global sections `t₀, …, t_N`, let `∑_{E ∈ S} E` be snc and let `Ξ` be a
finite set of points of `Y`. Then some nonzero section `τ` has its divisor of zeros supported on
a finite set `T` of prime divisors disjoint from `S` with `∑_{E ∈ T ∪ S} E` snc, and no component
of its divisor of zeros passes through a point of `Ξ`: the general member of the system avoids
each point, a nonempty open condition on `ℙᴺ`. -/
private theorem exists_zeroDivisor_support_subset_isSNC_avoid {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [IsSmoothVariety k (Y ↘ Spec (.of k))] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (hYv : MMP.Mori.IsVariety k (Y ↘ Spec (.of k))) (D : Divisor Y)
    (hD : D.IsCartier) {N : ℕ}
    (s : Fin (N + 1) → Γ(D.divisorialSheaf, ⊤))
    (hs' : haveI := hD.isInvertibleModule_divisorialSheaf
      ∀ y : Y, ∃ i, y ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf (s i))
    (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (Ξ : Finset Y) :
    ∃ (τ : D.divisorialSubmodule ⊤) (hτ : τ ≠ 0) (T : Finset (MMP.Mori.PrimeDivisor Y)),
      (∀ E, (D.zeroDivisor τ hτ).coeff E ≠ 0 → E ∈ T) ∧ Disjoint T S ∧
      DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) ∧
      ∀ ξ ∈ Ξ, ∀ E : MMP.Mori.PrimeDivisor Y, ξ ∈ E.support →
        (D.zeroDivisor τ hτ).coeff E = 0 := by
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
  obtain ⟨-, U₃, hU₃, hU₃c⟩ :=
    MMP.Threefold.Bridges.exists_dense_open_inter_nonvanishingOpen_nonempty hYv s hs
      (fun ξ : Ξ => closure {ξ.1}) (fun _ => isClosed_closure)
      (fun _ => isIrreducible_singleton.closure)
  obtain ⟨Q₃, hQ₃0, hQ₃⟩ := exists_polynomial_dualPoint_mem U₃ hU₃
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
  obtain ⟨c, hc⟩ : ∃ c : Fin (N + 1) → k, MvPolynomial.eval c (Q₁ * Q₂ * Q₃) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero (mul_ne_zero hQ₁0 hQ₂0) hQ₃0
      (MvPolynomial.funext fun c => by rw [h c, map_zero])
  rw [map_mul, map_mul] at hc
  have hτ : (MMP.Threefold.Bridges.systemSection (k := k) s c : D.divisorialSubmodule ⊤) ≠ 0 := by
    rw [hsys]
    exact hQ₂ c (right_ne_zero_of_mul (left_ne_zero_of_mul hc))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hsys]
    simp
  obtain ⟨-, T, hTcomp, hTS, hsnc⟩ := hUc c hc0
    (hQ₁ c hc0 (left_ne_zero_of_mul (left_ne_zero_of_mul hc)))
  have hav := hU₃c c hc0 (hQ₃ c hc0 (right_ne_zero_of_mul hc))
  rw [support_sum_single] at hTS hsnc
  refine ⟨_, hτ, T, fun E hE => ?_, hTS, hsnc, fun ξ hξ E hξE => ?_⟩
  · by_contra hET
    apply hE
    by_cases hEZ : E.genericPoint ∈ (zeroScheme Y D.divisorialSheaf
        (MMP.Threefold.Bridges.systemSection (k := k) s c)).supportSet
    · exfalso
      obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf
        (zeroScheme Y D.divisorialSheaf
          (MMP.Threefold.Bridges.systemSection (k := k) s c)).support.isClosed
      obtain ⟨W, hW, hEW⟩ := Set.mem_sUnion.mp (hcov hEZ)
      obtain ⟨E', hE'T, hE'W⟩ := (hTcomp W).mp hW
      exact hET (by rwa [← eq_of_genericPoint_mem_support (P := E') (E := E) (hE'W ▸ hEW)])
    · exact coeff_zeroDivisor_eq_zero_of_notMem D hD _ hτ E hEZ
  · -- the member does not vanish at `ξ`, hence not at the generic point of `E`
    obtain ⟨z, hzξ, hzO⟩ := hav ⟨ξ, hξ⟩
    have hξO : ξ ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf
        (MMP.Threefold.Bridges.systemSection s c) :=
      (specializes_iff_mem_closure.mpr hzξ).mem_open (TopologicalSpace.Opens.isOpen _) hzO
    have hEO : E.genericPoint ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf
        (MMP.Threefold.Bridges.systemSection s c) :=
      (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hξE).mem_open
        (TopologicalSpace.Opens.isOpen _) hξO
    exact coeff_zeroDivisor_eq_zero_of_notMem D hD _ hτ E
      (AlgebraicGeometry.notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen _ _ hEO)

end BertiniAvoid

/-! ### A general member of a multiple of an ample divisor -/

section GeneralMember

open MMP.Mori

/-- Over the spectrum of a field, relative ampleness is ampleness. -/
private theorem isAmple_of_isRelativelyAmple_spec {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : MMP.Mori.IsRelativelyAmple s N) : Stacks.Ample.IsAmple X N := by
  obtain ⟨V, -, hyV, hA⟩ := h (IsLocalRing.closedPoint _)
  have hV : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => by
    rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]; exact hyV)
  subst hV
  have : IsIso (s ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback _ N hA

open Classical in
/-- **A general member of a multiple of an ample divisor.** On a smooth projective variety `W`
over an algebraically closed field of characteristic zero, let `L` be an ample Cartier divisor,
`∑_{E ∈ S} E` an snc divisor and `Ξ` a finite set of points. For some `n > 0` there are an
effective divisor `Z = (n L) + div f` and a finite set `T` of prime divisors, disjoint from `S`,
carrying `Z`, with `∑_{E ∈ T ∪ S} E` snc, such that no component of `Z` passes through a point of
`Ξ`; moreover `Z` is ample. -/
private theorem exists_generalMember {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (hWv : MMP.Mori.IsProjectiveVariety k sW)
    (hWs : IsSmoothScheme sW) {L : Divisor W} (hL : L.IsCartier) (hLa : L.IsRelativelyAmple sW hL)
    (S : Finset (MMP.Mori.PrimeDivisor W))
    (hS : DivisorWithCoeffs.IsSNC sW (∑ E ∈ S, Finsupp.single E (1 : ℤ))) (Ξ : Finset W) :
    ∃ (n : ℕ) (f : (RationalFunctions W)ˣ) (Z : Divisor W) (T : Finset (MMP.Mori.PrimeDivisor W)),
      0 < n ∧ principalDivisor f = Z - n • L ∧ 0 ≤ Z ∧ (∀ E, Z.coeff E ≠ 0 → E ∈ T) ∧
      Disjoint T S ∧ DivisorWithCoeffs.IsSNC sW (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) ∧
      (∀ ξ ∈ Ξ, ∀ E : MMP.Mori.PrimeDivisor W, ξ ∈ E.support → Z.coeff E = 0) ∧
      ∃ hZ : Z.IsCartier, Z.IsRelativelyAmple sW hZ := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  have hWvar : AlgebraicGeometry.IsVariety k sW := hWv.toIsVariety
  haveI : IsSeparated sW := hWvar.toIsSeparated
  haveI : QuasiCompact sW := hWvar.toQuasiCompact
  have hamp := isAmple_of_isRelativelyAmple_spec sW L.divisorialSheaf hLa
  obtain ⟨n, N, s, hs⟩ := exists_forall_mem_nonvanishingOpen hL hL hamp
  letI : W.Over (Spec (.of k)) := ⟨sW⟩
  haveI : IsSmoothVariety k (W ↘ Spec (.of k)) :=
    (isSmoothVariety_iff k _).mpr ⟨hWvar, (isSmoothScheme_iff sW).mp hWs⟩
  have hMc : (n • L + L).IsCartier := (hL.nsmul n).add hL
  obtain ⟨τ, hτ, T, hT, hTS, hsnc, hav⟩ :=
    exists_zeroDivisor_support_subset_isSNC_avoid (k := k) hWvar (n • L + L) hMc s hs S hS Ξ
  set Z := (n • L + L).zeroDivisor τ hτ with hZdef
  set f := (Divisor.isUnit_sectionToRationalFunctions hτ).unit
  have hnL : n • L + L = (n + 1) • L := (succ_nsmul L n).symm
  have hZf : principalDivisor f = Z - (n + 1) • L := by
    rw [hZdef, Divisor.zeroDivisor_eq, ← hnL]
    abel
  have hZc : Z.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hWs Z
  refine ⟨n + 1, f, Z, T, Nat.succ_pos n, hZf, Divisor.zeroDivisor_nonneg _ τ hτ, hT, hTS, hsnc,
    hav, hZc, ?_⟩
  have h1 : ((n + 1) • L).IsRelativelyAmple sW (hL.nsmul (n + 1)) :=
    isRelativelyAmple_nsmul hL hLa (n + 1) (Nat.succ_pos n)
  have hlin : Z.LinearlyEquivalent ((n + 1) • L) := ⟨f, hZf.symm⟩
  haveI := hZc.isInvertibleModule_divisorialSheaf
  haveI := (hL.nsmul (n + 1)).isInvertibleModule_divisorialSheaf
  exact isRelativelyAmple_of_iso sW hlin.divisorialSheafIso.symm h1

end GeneralMember

/-! ### Coefficients on a birational model -/

section ModelCoefficients

open MMP.Mori
open scoped WithZero

/-- A prime divisor of `W` that is not `p`-exceptional maps generically onto a prime divisor of
`X`, along which `p` induces an isomorphism of local rings. -/
private theorem exists_eq_genericPoint_of_not_isExceptional {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hXn : IsNormalVariety k sX) (p : W ⟶ X) (hWn : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (P : MMP.Mori.PrimeDivisor W)
    (hP : ¬ RationalMap.IsExceptional (X := W) p.toRationalMap P) :
    ∃ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint ∧
      IsIso (p.stalkMap P.genericPoint) := by
  have hD : ¬ (⟨W, p, hWn, hpb, P⟩ : DivisorOver k sX).IsExceptional := hP
  obtain ⟨Q, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXn _ hD
  have hx := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXn.1 hv
  refine ⟨Q, hx, ?_⟩
  haveI : IsDominant p := hpb.isDominant
  haveI : ValuationRing (X.presheaf.stalk (p P.genericPoint)) := by
    haveI := Q.isDiscreteValuationRing_localRing
    have : ValuationRing (X.presheaf.stalk Q.genericPoint) :=
      inferInstanceAs (ValuationRing Q.localRing)
    change ValuationRing (X.presheaf.stalk (p P.genericPoint))
    rwa [show p P.genericPoint = Q.genericPoint from hx]
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing p hpb.functionFieldMap_bijective _

/-- The coefficient of an `ℝ`-Cartier pull-back at a strict transform is the coefficient
downstairs. -/
private theorem coeff_isRCartierPullback_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D : RDivisor X}
    {G : RDivisor Y} (h : MMP.Flips.IsRCartierPullback f D G) (E : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] : G.coeff E = D.coeff P := by
  obtain ⟨m, r, L, L', hLc, rfl, hpb, rfl⟩ := h
  rw [MMP.Flips.coeff_sum_smul_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨hB, hL'⟩ := hpb j
  rw [MMP.Positivity.coeff_eq_of_isPullback E P heq (hLc j) hL']

/-- The coefficient of the pull-back of a `ℚ`-Cartier `ℚ`-divisor at a strict transform is the
coefficient downstairs. -/
private theorem coeff_isQPullback_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X}
    (hAq : A.IsQCartier)
    {hA : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {A' : QDivisor Y} (h : A.IsPullback f hA A') (E : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] : A'.coeff E = A.coeff P := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hc := MMP.Positivity.coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor Y => G.coeff E) hD'
  have h2 := congrArg (fun G : QDivisor X => G.coeff P) hD₀
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1 h2
  have hm0 : ((A.cartierIndex hAq : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hc] at h1
  exact mul_left_cancel₀ hm0 (h1.symm.trans h2)

/-- **The log discrepancy of a prime divisor of a model.** For a proper birational
`f : W ⟶ M` of normal varieties, a rational top form `ω ≠ 0` with `div ω = K_M` canonical, and
`G = f^*(K_M + Δ_M)`, the prime divisor `E'` of `W` has log discrepancy
`1 + coeff_{E'} div(f^*ω) - coeff_{E'} G` over `(M, Δ_M)`. -/
private theorem isLogDiscrepancy_of_isRCartierPullback {k : Type u} [Field k]
    {M W : Scheme.{u}} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
    {sM : M ⟶ Spec (.of k)} [LocallyOfFiniteType sM] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {KM : Divisor M} {ΔM : RDivisor M} {f : W ⟶ M} [IsProper f]
    [IsDominant f]
    {G : RDivisor W} {e : ℕ} (hMn : IsNormalVariety k sM) (hKM : KM.IsCanonicalDivisor sM e)
    (hWnf : IsNormalVariety k (f ≫ sM)) (hfb : IsBirationalMorphism f)
    (ω : RationalPluriForms sM e 1) (hω0 : ω ≠ 0) (hωK : divisorOfForm ω = KM)
    (hG : MMP.Flips.IsRCartierPullback f (MMP.Flips.logCanonicalDivisor KM ΔM) G)
    (E' : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sM e ΔM ⟨W, f, hWnf, hfb, E'⟩
      (1 + ((divisorOfForm (pullbackRationalPluriForms sM f ω)).coeff E' : ℝ) - G.coeff E') := by
  obtain ⟨m, r, L, L', hLc, hD, hpbL, rfl⟩ := hG
  refine ⟨hMn, inferInstanceAs (IsProper f), ω, hω0, ⟨KM, hKM, fun Γ => by
    rw [← hωK]; exact coeff_divisorOfForm ω Γ⟩, m, r, L, L', hLc, fun Γ => ?_, hpbL, ?_⟩
  · have := congrArg (fun D : RDivisor M => D.coeff Γ) hD
    simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, ← hωK, coeff_divisorOfForm]
  · rw [MMP.Flips.coeff_sum_smul_toRDivisor, coeff_divisorOfForm]
    rfl

/-- On a smooth variety every `ℝ`-divisor has an `ℝ`-Cartier pull-back along a dominant
morphism. -/
private theorem exists_isRCartierPullback_of_isSmoothScheme {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hsm : IsSmoothScheme sX) (f : W ⟶ X) [IsDominant f] (D : RDivisor X) :
    ∃ G : RDivisor W, MMP.Flips.IsRCartierPullback f D G := by
  obtain ⟨m, r, L, hLc, hD⟩ := isRCartier_of_isSmoothScheme hsm D
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant f (hLc j)
  refine ⟨_, m, r, L, L', hLc, ?_, fun j => ⟨_, hL' j⟩, rfl⟩
  ext Γ
  exact (hD Γ).trans (MMP.Flips.coeff_sum_smul_toRDivisor r L Γ).symm

/-- Orders of a function along prime divisors whose valuations correspond. -/
private theorem ord_eq_of_comap_eq {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (θ : Y.functionField →+* X.functionField) (P : MMP.Mori.PrimeDivisor X)
    (G : MMP.Mori.PrimeDivisor Y) (h : P.divisorialValuation.comap θ = G.divisorialValuation)
    {g : Y.functionField} (hg : g ≠ 0) :
    X.ord (θ g) P.genericPoint = Y.ord g G.genericPoint := by
  have h1 := congrArg (fun v : Valuation Y.functionField ℤᵐ⁰ => v g) h
  simp only [Valuation.comap_apply] at h1
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero θ).mpr hg),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg] at h1
  exact neg_inj.mp (WithZero.exp_injective h1)

/-- A divisor over `X` with the valuation of a prime divisor is not exceptional. -/
private theorem not_isExceptional_of_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) (P : MMP.Mori.PrimeDivisor X)
    (h : D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation) : ¬ D.IsExceptional := by
  intro hD
  have hx := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 h
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI := isSeparated_toTerminal sX
  have := D.isLocallyNoetherian
  have := D.isNormal
  have h2 := (MMP.Positivity.isExceptional_toRationalMap_iff D.E).mp hD
  have hmem : D.f D.E.genericPoint ∈ TopologicalSpace.Closeds.closure
      (D.f '' (D.E.idealSheaf.support : Set D.Y)) := by
    refine subset_closure ⟨D.E.genericPoint, ?_, rfl⟩
    exact PrimeDivisor.genericPoint_mem_support' D.E
  have hsub : ((irreducibleSetEquivPoints (α := X)).symm (D.f D.E.genericPoint) : Set X) ⊆
      TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) :=
    (TopologicalSpace.Closeds.isClosed _).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hmem)
  have h3 := le_closedsCodimension_iff.mp h2 _ hsub
  rw [codimension_eq_coheight, Order.coheight_orderIso] at h3
  change 2 ≤ Order.coheight (D.f D.E.genericPoint) at h3
  rw [show D.f D.E.genericPoint = P.genericPoint from hx, P.coheight_genericPoint] at h3
  exact absurd h3 (by decide)

/-- A real pair whose log discrepancies are nonnegative and vanish only at the valuation of a prime
divisor `P` is log canonical, with positive log discrepancy at every exceptional divisor. -/
private theorem isRealLcPair_and_pos_of_isLogDiscrepancy {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {B : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) {m : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX m)
    (hRC : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X)
    (h : ∀ (d : ℕ) (D : DivisorOver k sX) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX d B D a →
      0 ≤ a ∧ (a = 0 → D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation)) :
    IsRealLcPair sX B ∧ ∀ (d : ℕ) (D : DivisorOver k sX), D.IsExceptional → ∀ a : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX d B D a → 0 < a :=
  ⟨⟨hX, hB, ⟨m, K, hK, hRC⟩, fun d D a ha => (h d D a ha).1⟩, fun d D hD a ha =>
    lt_of_le_of_ne (h d D a ha).1 fun h' =>
      not_isExceptional_of_valuation_eq hX D P ((h d D a ha).2 h'.symm) hD⟩

end ModelCoefficients

/-! ### Prime divisors in snc closed subsets -/

section SNCHelpers

open MMP MMP.Mori MMP.Resolution TopologicalSpace

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

private theorem primeDivisor_eq_of_support_eq {X : Scheme.{u}} {P Q : Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- A prime divisor whose generic point lies in a closed set is contained in it. -/
private theorem support_subset_of_genericPoint_mem {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {C : Set X} (hC : IsClosed C) (h : P.genericPoint ∈ C) : (P.support : Set X) ⊆ C := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hC

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {T : Closeds X} (hT : (T : Set X) = P.support) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal T := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (Closeds.ext hT.symm)

/-- An irreducible component of a closed subset of pure codimension one is the closure of a
point of coheight one. -/
private theorem exists_coheight_eq_one_of_mem_componentsOf {S : Set Y} (hSc : IsClosed S)
    (hS : MMP.Mori.IsPureCodimOne (⟨S, hSc⟩ : Closeds Y)) {V : Set Y}
    (hV : V ∈ componentsOf S) : ∃ ξ : Y, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hSc hV
  refine ⟨ξ, hξ, ?_⟩
  rw [← MMP.Flips.codimension_closureSingleton]
  apply hS
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ S
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rwa [hξ])
    change (W' : Set Y) ⊆ closure {ξ}
    rwa [← hξ]

/-- The support of a prime divisor contained in an snc closed subset `S` is an irreducible
component of `S`. -/
private theorem support_mem_componentsOf [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) {P : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ S) :
    (P.support : Set Y) ∈ componentsOf S := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
  · exfalso
    have := hP (PrimeDivisor.genericPoint_mem_support' P)
    rwa [hempty] at this
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (PrimeDivisor.genericPoint_mem_support' P))
    obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure hW
    have hsp : ξ ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hWξ ▸ hηW)
    have hξη : ξ = P.genericPoint := by
      by_contra hne
      have hlt : P.genericPoint < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq
      have := Order.coheight_strictAnti hlt
      rw [hξ1, P.coheight_genericPoint] at this
      exact lt_irrefl _ (this (by simp))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {P.genericPoint} ∈ _
    rw [← hξη, ← hWξ]
    exact hW

/-- Only finitely many prime divisors are contained in an snc closed subset. -/
private theorem finite_setOf_support_subset [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) :
    {P : Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ S}.Finite := by
  refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hS.1).1.subset ?_)
    fun P _ Q _ h => primeDivisor_eq_of_support_eq h
  rintro - ⟨P, hP, rfl⟩
  exact support_mem_componentsOf hS hP

/-- **A reduced divisor whose components lie in an snc closed subset is snc.** -/
private theorem isSNC_sum_single_of_support_subset [LocallyOfFiniteType sY] [NoetherianSpace Y]
    [IsLocallyNoetherian Y] (hsm : IsSmoothScheme sY) {S : Set Y} (hS : IsSNCClosedSubset sY S)
    (s : Finset (Mori.PrimeDivisor Y)) (hs : ∀ P ∈ s, (P.support : Set Y) ⊆ S) :
    (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY := by
  classical
  have hc : ∀ P ∈ s, (P.support : Set Y) ∈ componentsOf S := fun P hP =>
    support_mem_componentsOf hS (hs P hP)
  obtain ⟨hSc, hempty | ⟨-, -, hfam⟩⟩ := id hS
  · have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem fun P hP => by
      have := hs P hP (PrimeDivisor.genericPoint_mem_support' P)
      rwa [hempty] at this
    subst hs0
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  have hG := support_sum_single s
  have hideal : ∀ P (hP : P ∈ s),
      P.idealSheaf = componentsFamily S ⟨(P.support : Set Y), hc P hP⟩ := fun P hP =>
    idealSheaf_eq_vanishingIdeal P (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hSc (hc P hP)).closure_eq])
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [hG] at hP
    rw [hideal P hP]
    exact (hfam.1 _).2.2
  · obtain ⟨m, z, c, hz, hcI, hcinj⟩ := hfam.2 x
    have hs' : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        P.1 ∈ s := fun P => hG.subset P.2.1
    have hmem : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        x ∈ (componentsFamily S ⟨(P.1.support : Set Y), hc P.1 (hs' P)⟩).support := fun P => by
      rw [← SetLike.mem_coe, coe_support_componentsFamily hSc]
      exact P.2.2
    refine ⟨m, z, fun P => c ⟨_, hmem P⟩, hz, fun P Q h => ?_, fun P => ?_⟩
    · have h1 := congrArg (fun V => (V.1.1 : Set Y)) (hcinj h)
      exact Subtype.ext (primeDivisor_eq_of_support_eq h1)
    · rw [hideal P.1 (hs' P)]
      exact hcI ⟨_, hmem P⟩

end SNCHelpers

/-! ### The reference model -/

section Reference

open MMP.Mori
open scoped WithZero

/-- The support `⋃_{coeff_D B = 1} D` of the reduced part `⌊B⌋` of an `ℝ`-divisor. -/
private def floorSet {X : Scheme.{u}} (B : RDivisor X) : Set X :=
  {x | ∃ D : MMP.Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support}

/-- A *reference model* of an snc pair `(X, B + C)` with ample `A ≤ B` for a prime divisor `E_W`:
a smooth projective birational model `p : W ⟶ X` all of whose exceptional prime divisors are
zero places of `(X, B)` lying over `⌊B⌋`, on which the total transform of `Supp(B + C)` is snc,
`p^*A` has no exceptional component, `E_W` lies over `⌊B⌋`, and an effective `F` supported over
`⌊B⌋`, positive along every prime divisor over `⌊B⌋` except `E_W`, makes `p^*A + δF` ample for
small `δ > 0`. -/
private structure IsReferenceModel {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (B C : RDivisor X) (A : QDivisor X) (n : ℕ)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ X) (EW : MMP.Mori.PrimeDivisor W) (F : QDivisor W) : Prop where
  projective : MMP.Mori.IsProjectiveVariety k (p ≫ sX)
  smooth : MMP.Mori.IsSmoothScheme (p ≫ sX)
  normal : IsNormalVariety k (p ≫ sX)
  proper : IsProper p
  birational : IsBirationalMorphism p
  logDiscrepancy_eq_zero : ∀ P : MMP.Mori.PrimeDivisor W,
    RationalMap.IsExceptional (X := W) p.toRationalMap P →
      MMP.Intersection.IsLogDiscrepancy sX n B ⟨W, p, normal, birational, P⟩ 0
  mem_floorSet : ∀ P : MMP.Mori.PrimeDivisor W,
    RationalMap.IsExceptional (X := W) p.toRationalMap P → p P.genericPoint ∈ floorSet B
  mem_floorSet_EW : p EW.genericPoint ∈ floorSet B
  isSNCClosedSubset : MMP.Resolution.IsSNCClosedSubset (p ≫ sX) (p ⁻¹' ((B + C).supp : Set X))
  coeff_pullback : ∀ (hA0 : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ A.supp)
    (A' : QDivisor W), QDivisor.IsPullback p A hA0 A' → ∀ P : MMP.Mori.PrimeDivisor W,
      RationalMap.IsExceptional (X := W) p.toRationalMap P → A'.coeff P = 0
  F_nonneg : 0 ≤ F
  F_EW : F.coeff EW = 0
  F_supp : ∀ P : MMP.Mori.PrimeDivisor W, F.coeff P ≠ 0 → (P.support : Set W) ⊆ p ⁻¹' floorSet B
  F_pos : ∀ P : MMP.Mori.PrimeDivisor W, P ≠ EW → (P.support : Set W) ⊆ p ⁻¹' floorSet B →
    0 < F.coeff P
  F_ample : ∀ (hA0 : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ A.supp)
    (A' : QDivisor W), QDivisor.IsPullback p A hA0 A' →
      ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
        (A' + δ • F).HasRelativelyAmpleMultiple (p ≫ sX)

/-- The valuation of a prime divisor regarded as a divisor over `X` is its divisorial valuation. -/
private theorem valuation_ofPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation := by
  ext g
  change P.divisorialValuation (functionFieldMap (𝟙 X) g) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

/-- Prime divisors of a normal variety are determined by their divisorial valuations. -/
private theorem primeDivisor_eq_of_divisorialValuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {P Q : MMP.Mori.PrimeDivisor X}
    (h : P.divisorialValuation = Q.divisorialValuation) : P = Q := by
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1
    (D := DivisorOver.ofPrimeDivisor k hX P) (D' := DivisorOver.ofPrimeDivisor k hX Q)
    (by rw [valuation_ofPrimeDivisor, valuation_ofPrimeDivisor, h])
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

/-- Valuations agreeing after a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ₀ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommGroupWithZero Γ₀] {θ : K →+* L} (hθ : Function.Surjective θ)
    {v w : Valuation L Γ₀} (h : v.comap θ = w.comap θ) : v = w := by
  ext x
  obtain ⟨y, rfl⟩ := hθ x
  exact congrArg (fun u : Valuation K Γ₀ => u y) h

end Reference

end KltPerturbation

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The divisor of a nonzero top form on a smooth variety is canonical. -/
private theorem isCanonicalDivisor_divisorOfForm_of_isSmoothScheme {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (hXs : IsSmoothScheme sX) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {n : ℕ} (hn : topologicalKrullDim X = n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n := by
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  obtain ⟨K, hK⟩ := @exists_isCanonicalDivisor_of_isSmoothScheme _ _ _ _ _ k _ _ hX hXs n hn
  exact hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul ⟨hX, inferInstance⟩ hK hτ

open scoped WithZero in
/-- **Log discrepancies over the target of a comparison, through a crepant model.** Let a
common resolution compare the adjoints of `(X, Δ_X)` and `(Y, Δ_Y)` with effective comparison,
and let `p : W ⟶ X` carry the crepant pull-back `K_W + Δ_W = p^*(K_X + Δ_X)`. If every log
discrepancy of `(W, Δ_W)` is nonnegative and vanishes only at the valuation `w₀`, then every log
discrepancy of `(Y, Δ_Y)` is nonnegative and vanishes only at the valuation `w₀` read on `k(Y)`. -/
private theorem logDiscrepancy_nonneg_of_isLogComparisonResolution_of_crepant {k : Type u}
    [Field k] [PerfectField k] {X Y V W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {φ : X.RationalMap Y} {KX : Divisor X} {KY : Divisor Y} {ΔX : RDivisor X} {ΔY : RDivisor Y}
    {p₀ : V ⟶ X} {q₀ : V ⟶ Y} {h₀ : X.RationalMap V} {GX GY : RDivisor V}
    (hR : IsLogComparisonResolution sX sY sV φ KX ΔX KY ΔY p₀ q₀ h₀ GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY) {n nY : ℕ}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor sY nY)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (p : W ⟶ X) [IsProper p] (hWn : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    {ωX : RationalPluriForms sX n 1} (hωX0 : ωX ≠ 0) (hωX : divisorOfForm ωX = KX)
    {ΔW : RDivisor W}
    (hDW : haveI : IsDominant p := hpb.isDominant
      MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + ΔX)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX)) + ΔW))
    (hKW : haveI : IsDominant p := hpb.isDominant
      (divisorOfForm (pullbackRationalPluriForms sX p ωX)).IsCanonicalDivisor (p ≫ sX) n)
    (w₀ : Valuation W.functionField ℤᵐ⁰)
    (hW : ∀ (d : ℕ) (D' : DivisorOver k (p ≫ sX)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (p ≫ sX) d ΔW D' a → 0 ≤ a ∧ (a = 0 → D'.valuation = w₀))
    (d : ℕ) (D : DivisorOver k sY) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sY d ΔY D a) :
    haveI : IsDominant p := hpb.isDominant
    0 ≤ a ∧ (a = 0 → D.valuation = (w₀.comap (functionFieldMap p)).comap θ) := by
  haveI : IsDominant p := hpb.isDominant
  have hWnp := isNormalVariety_comp_left hR
  have hWnq := isNormalVariety_comp_right hR
  have := isProper_of_isProjectiveMorphism p₀ hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q₀ hR.isProjectiveMorphism_right
  have hpb₀ := hR.isBirationalMorphism_left
  have hqb₀ := hR.isBirationalMorphism_right
  have : IsDominant p₀ := hpb₀.isDominant
  have : IsDominant q₀ := hqb₀.isDominant
  have : LocallyOfFiniteType (p₀ ≫ sX) := hWnp.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (q₀ ≫ sY) := hWnq.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k (q₀ ≫ sY) := hWnq.1
  have : LocallyOfFiniteType (p ≫ sX) := hWn.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k (p ≫ sX) := hWn.1
  have := compactSpace_of_isLogComparisonResolution hR
  obtain ⟨rfl, KV, hKVp, hKVq, ⟨ωX', hωX'0, hωX', hωX'V⟩, ωY, hωY0, hωY, hωYV⟩ :=
    exists_rationalPluriForms_of_isLogComparisonResolution hR hXn hYn hKX hKY
  have hGp := hR.isRCartierPullback_left
  have hGq := hR.isRCartierPullback_right
  rw [MMP.Flips.logCanonicalDivisor, ← hωX'] at hGp
  rw [MMP.Flips.logCanonicalDivisor, ← hωY] at hGq
  obtain ⟨E₀, b, w, hb, hba, hDw, hE₀w⟩ := exists_isLogDiscrepancy_le_of_crepant_le hXn hYn hWnp
    hWnq hpb₀ hqb₀ (hR.comp_eq_right.trans hR.comp_eq_left.symm) hKY.topologicalKrullDim_eq hωX'0
    (by rwa [hωX']) hωY0 (by rwa [hωY]) hKVp hKVq hωX'V hωYV hGp hGq
    (isRCartier_of_isSmoothScheme hR.isSmoothScheme _) hR.effective d D a ha
  obtain ⟨E₁, hE₁, hb₁⟩ := exists_isLogDiscrepancy_of_crepant hXn hKX.topologicalKrullDim_eq hωX0
    (by rwa [hωX]) p hWn hpb hDW hKW d E₀ b hb
  obtain ⟨hb0, hbw⟩ := hW d E₁.toDivisorOver b hb₁
  refine ⟨hb0.trans hba, fun ha0 => ?_⟩
  have hb00 : b = 0 := le_antisymm (ha0 ▸ hba) hb0
  have h1 : E₁.valuation = w₀ := hbw hb00
  have hθp := functionFieldMap_comp_eq φ θ hθ p₀ q₀ h₀ hR.isInverse hR.compHom_eq
  rw [hDw, ← hθp]
  have h2 : E₀.valuation = w₀.comap (functionFieldMap p) := by
    rw [← hE₁]
    exact congrArg (fun v => v.comap (functionFieldMap p)) h1
  rw [← h2, hE₀w]
  rfl

open Classical in
/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isQFactorial {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hQ : MMP.Fourfold.IsQFactorial sY) (D : RDivisor Y) : RDivisor.IsRCartier D := by
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor Y => hQ.2 (Finsupp.single P 1)
  refine ⟨D.support.card, fun i => D (D.support.equivFin.symm i) /
      ((m (D.support.equivFin.symm i) : ℕ) : ℝ),
    fun i => ((m (D.support.equivFin.symm i) : ℕ) : ℤ) •
      (Finsupp.single (D.support.equivFin.symm i : MMP.Mori.PrimeDivisor Y) (1 : ℤ) : Divisor Y),
    fun i => hmC _, fun Γ => ?_⟩
  have hterm : ∀ i : Fin D.support.card, D (D.support.equivFin.symm i) /
      ((m (D.support.equivFin.symm i) : ℕ) : ℝ) *
      ((DivisorWithCoeffs.coeff (((m (D.support.equivFin.symm i) : ℕ) : ℤ) •
        (Finsupp.single (D.support.equivFin.symm i : MMP.Mori.PrimeDivisor Y) (1 : ℤ) :
          Divisor Y)) Γ : ℤ) : ℝ) =
      D (D.support.equivFin.symm i) *
        (((Finsupp.single (D.support.equivFin.symm i : MMP.Mori.PrimeDivisor Y) (1 : ℤ)) Γ : ℤ) :
          ℝ) := by
    intro i
    have hm0 : ((m (D.support.equivFin.symm i) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hm _).ne'
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_apply, smul_eq_mul, Int.cast_mul,
      Int.cast_natCast]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, sum_equivFin_mul_single D.support (⇑D) Γ,
    DivisorWithCoeffs.coeff_apply]
  split_ifs with h
  · rfl
  · exact Finsupp.notMem_support_iff.mp h

/-- **Adding an effective `ℝ`-Cartier divisor lowers log discrepancies.** If `a` is a log
discrepancy of `D` over `(X, Δ)` and `D' ≥ 0` is `ℝ`-Cartier, then some log discrepancy of `D`
over `(X, Δ + D')` is at most `a`. -/
private theorem exists_isLogDiscrepancy_le_add {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Δ D' : RDivisor X} (hD' : RDivisor.IsRCartier D') (h0 : ∀ P, 0 ≤ D'.coeff P)
    {n : ℕ} {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n Δ D a) :
    ∃ a' : ℝ, a' ≤ a ∧ MMP.Intersection.IsLogDiscrepancy sX n (Δ + D') D a' := by
  obtain ⟨hX, hp, ω, hω, hK, m, r, C, C', hC, hsum, hpb, rfl⟩ := ha
  obtain ⟨m', r', L, hL, hD'eq⟩ := id hD'
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D.isNormalVariety.1
  have : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hL j)
  have hD'eq' : D' = ∑ j, r' j • Divisor.toRDivisor (L j) := by
    ext Γ
    exact (hD'eq Γ).trans (MMP.Flips.coeff_sum_smul_toRDivisor r' L Γ).symm
  have hG : MMP.Flips.IsRCartierPullback D.f D' (∑ j, r' j • Divisor.toRDivisor (L' j)) :=
    ⟨m', r', L, L', hL, hD'eq', fun j => ⟨_, hL' j⟩, rfl⟩
  have hG0 := (MMP.Fourfold.isEffective_of_isRCartierPullback D.f hD' h0).2 _ hG
  have hnn : (0 : ℝ) ≤ ∑ j, r' j * ((L' j).coeff D.E : ℝ) := by
    have := hG0 D.E
    change (0 : ℝ) ≤ DivisorWithCoeffs.coeff (∑ j, r' j • Divisor.toRDivisor (L' j)) D.E at this
    rwa [MMP.Flips.coeff_sum_smul_toRDivisor] at this
  refine ⟨_, ?_, hX, hp, ω, hω, hK, m + m', Fin.append r r', Fin.append C L, Fin.append C' L',
    Fin.addCases (by simpa using hC) (by simpa using hL), fun Γ => ?_,
    Fin.addCases (by simpa using hpb) (by simpa using fun j =>
      (⟨_, hL' j⟩ : ∃ hB, (L j).IsPullback D.f hB (L' j))), rfl⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    linarith
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [DivisorWithCoeffs.coeff_add, ← add_assoc, hsum Γ, hD'eq Γ]

open Classical in
/-- **Avoided centres.** Let `ψ : W ⤏ Y` induce the surjection `θψ : k(Y) → k(W)`, let `Ξ`
collect, for each prime divisor `G` in a finite set `S`, the centre on `W` of one divisor over `W`
realizing `G` through `ψ` (when there is one), and let `Ξ` contain these points, none on a
component of `A'`. Then for `G ∈ S` the centre of every divisor realizing `G` is not contained in
`Supp A'`: all such divisors have the same valuation, hence the same centre. -/
private theorem not_center_subset_of_isRealizedOver {k : Type u} [Field k] {W Y : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (hWn : IsNormalVariety k sW) (ψ : W.RationalMap Y)
    (θψ : Y.functionField →+* W.functionField) (hθψs : Function.Surjective θψ)
    (hθψ : Spec.map (CommRingCat.ofHom θψ) ≫ Y.fromSpecStalk (genericPoint Y) =
      ψ.fromFunctionField)
    (A' : QDivisor W) (Ξ : Finset W) (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hΞ : S.image (fun G => if h : ∃ D : MMP.Flips.ProperDivisorOver k sW,
      MMP.Flips.IsRealizedOver sW ψ G D then h.choose.f h.choose.E.genericPoint
      else genericPoint W) ⊆ Ξ)
    (hav : ∀ ξ ∈ Ξ, ∀ P : MMP.Mori.PrimeDivisor W, ξ ∈ P.support → A'.coeff P = 0)
    (G : MMP.Mori.PrimeDivisor Y) (hG : G ∈ S) (D : MMP.Flips.ProperDivisorOver k sW)
    (hD : MMP.Flips.IsRealizedOver sW ψ G D) : ¬ (D.center : Set W) ⊆ A'.supp := by
  intro hsub
  have hval : ∀ D' : MMP.Flips.ProperDivisorOver k sW, MMP.Flips.IsRealizedOver sW ψ G D' →
      D'.valuation.comap θψ = G.divisorialValuation := by
    rintro D' ⟨g, pD, hpD, hg, hcomm, hvalG⟩
    haveI := D'.isIntegral
    haveI := D'.isNormal
    haveI := D'.isLocallyNoetherian
    haveI := D'.isDominant
    haveI := hpD.isDominant
    have hA : Spec.map (CommRingCat.ofHom (functionFieldMap D'.f)) ≫ ψ.fromFunctionField =
        D'.Y.fromSpecStalk (genericPoint D'.Y) ≫ pD := by
      rw [← hg]
      exact specMap_functionFieldMap_fromFunctionField D'.f g pD hcomm
    have h1 := functionFieldMap_comp_eq_of_specMap ψ.fromFunctionField θψ hθψ D'.f pD hA
    rw [← hvalG, ← h1]
    rfl
  have hex : ∃ D' : MMP.Flips.ProperDivisorOver k sW, MMP.Flips.IsRealizedOver sW ψ G D' :=
    ⟨D, hD⟩
  have hξ : hex.choose.f hex.choose.E.genericPoint ∈ Ξ :=
    hΞ (Finset.mem_image.mpr ⟨G, hG, dif_pos hex⟩)
  have hcen : D.f D.E.genericPoint = hex.choose.f hex.choose.E.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hWn.1
      (D := D.toDivisorOver) (D' := hex.choose.toDivisorOver)
      (valuation_eq_of_comap_eq hθψs ((hval D hD).trans (hval _ hex.choose_spec).symm))
  have hmem : D.f D.E.genericPoint ∈ (D.center : Set W) := by
    rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center]
    exact (MMP.Mori.DivisorOver.isGenericPoint_center D.toDivisorOver).mem
  obtain ⟨P, hP, hξP⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hsub hmem)
  rw [hcen] at hξP
  exact hP (hav _ hξ P hξP)

/-! ### Boundaries changed along finitely many prime divisors -/

namespace BoundaryCopy

open MMP MMP.Mori MMP.Resolution MMP.Fourfold

section Boundary

open scoped Classical

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The support of an snc divisor is an snc closed subset. -/
private theorem isSNCClosedSubset_supp {B : RDivisor X} (hB : B.IsSNC sX) :
    MMP.Resolution.IsSNCClosedSubset sX B.supp := by
  have hTs : (∑ P ∈ B.support, Finsupp.single P (1 : ℤ) : Divisor X).support = B.support :=
    support_sum_single _
  have hT := (DivisorWithCoeffs.isSNC_iff_of_support_eq hTs).mpr hB
  have h := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hT
  rw [hTs] at h
  rwa [DivisorWithCoeffs.coe_supp]

/-- The coefficient along `E` of the pull-back of a Cartier divisor `C` vanishes when `C` has
coefficient zero along every prime divisor through the centre of `E`. -/
private theorem coeff_isPullback_eq_zero_of_forall {D : DivisorOver k sX} {C : Divisor X}
    (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y Z) ∉ C.supp}
    {C' : Divisor D.Y} (h : haveI := D.isLocallyNoetherian; haveI := D.isNormal
      haveI := D.isDominant; C.IsPullback D.f hC C')
    (h0 : ∀ Γ : Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support → C.coeff Γ = 0) :
    C'.coeff D.E = 0 := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  set x := D.f D.E.genericPoint with hx
  obtain ⟨V, hV, φ, hφ⟩ := hCc x
  set Z0 := MMP.Mori.pointComponent x with hZ0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : MMP.Mori.RationalFunctions X) with hgdef
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ D.E hV Z0]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E
    (fun _ : Unit => g) (fun _ => hg) (fun _ => 1) fun Γ hΓ => by
      have hZ : Γ.component = Z0 := Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
      have e := hφ Γ ⟨x, hΓ, hV⟩
      rw [h0 Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ] at e
      have e' : Scheme.ord g Γ.genericPoint = 0 := e.symm
      simp [e']
  simpa using key

/-- **Changing the boundary by finitely many prime divisors.** On a smooth `X`, if `a` is the log
discrepancy of `E` over `(X, B)` and `B' = B + ∑_{P ∈ s} w_P P`, then
`a - ∑_{P ∈ s} w_P · coeff_E(f^*P)` is the log discrepancy of `E` over `(X, B')`. -/
private theorem exists_isLogDiscrepancy_of_coeff_eq (hsm : IsSmoothScheme sX) {n : ℕ}
    {B B' : RDivisor X} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) (s : Finset (Mori.PrimeDivisor X))
    (w : Mori.PrimeDivisor X → ℝ) (hB' : ∀ Γ, B'.coeff Γ = B.coeff Γ + if Γ ∈ s then w Γ else 0) :
    ∃ e : Mori.PrimeDivisor X → ℤ,
      (∀ P ∈ s, ∃ hC C', (haveI := D.isLocallyNoetherian; haveI := D.isNormal
        haveI := D.isDominant
        Divisor.IsPullback D.f (Finsupp.single P (1 : ℤ) : Divisor X) hC C') ∧
          C'.coeff D.E = e P) ∧
      MMP.Intersection.IsLogDiscrepancy sX n B' D (a - ∑ P ∈ s, w P * e P) := by
  obtain ⟨hX, hf, ω, hω0, hK, m, r, C, C', hCc, hsum, hpb, rfl⟩ := h
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  have hP : ∀ P : Mori.PrimeDivisor X, ∃ P' : Divisor D.Y,
      Divisor.IsPullback D.f (Finsupp.single P (1 : ℤ) : Divisor X)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _) P' :=
    fun P => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _)
  choose P' hP' using hP
  set σ := s.equivFin.symm with hσ
  have hsumσ : ∀ F : Mori.PrimeDivisor X → ℝ, ∑ i, F (σ i).1 = ∑ P ∈ s, F P := fun F => by
    rw [Equiv.sum_comp σ (fun x : s => F x.1), Finset.sum_coe_sort s F]
  refine ⟨fun P => (P' P).coeff D.E, fun P _ => ⟨_, P' P, hP' P, rfl⟩, ?_⟩
  refine ⟨hX, hf, ω, hω0, hK, m + s.card, Fin.append r (fun i => w (σ i).1),
    Fin.append C (fun i => Finsupp.single (σ i).1 1), Fin.append C' (fun i => P' (σ i).1),
    fun i => ?_, fun Γ => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hCc i
    · rw [Fin.append_right]; exact MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hB', ← add_assoc, hsum Γ,
      hsumσ (fun P => w P *
        ((DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ) : Divisor X) Γ : ℤ) : ℝ))]
    congr 1
    have : ∀ P, w P * ((DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ) : Divisor X) Γ : ℤ) : ℝ) =
        if P = Γ then w Γ else 0 := fun P => by
      by_cases hP : P = Γ
      · subst hP; simp [DivisorWithCoeffs.coeff_single_self]
      · simp [DivisorWithCoeffs.coeff_single_of_ne hP, hP]
    simp_rw [this]
    rw [Finset.sum_ite_eq']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact hpb i
    · simp only [Fin.append_right]
      exact ⟨MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _, hP' (σ i).1⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hsumσ (fun P => w P * ((P' P).coeff D.E : ℝ))]
    ring

end Boundary

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        exact ENat.top_ne_natCast n (WithBot.coe_injective h)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have e1 : (((d : ℕ∞) : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞)) ↔ d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le]
        rw [e1]
        refine ⟨fun _ => by exact_mod_cast (show 2 ≤ c by omega), fun h2 => ?_⟩
        have : 2 ≤ c := by exact_mod_cast h2
        omega

private theorem properDivisorOver_isExceptional_iff {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : MMP.Flips.ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

end BoundaryCopy

/-! ### Realizing and placing the zero places -/

section ZeroPlaces

open MMP.Mori
open scoped WithZero

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if they
agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq' {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (U : W.Opens) (hU : genericPoint W ∈ U)
    {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  let P₁ : W.PartialMap Y := ⟨U, hd, f⟩
  let P₂ : W.PartialMap Y := ⟨U, hd, g⟩
  have heqv : P₁.equiv P₂ := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁ P₂ hU hU H
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) (f := P₁) (g := P₂)
    hd le_rfl le_rfl).mp heqv
  rwa [Scheme.PartialMap.restrict_id_hom, Scheme.PartialMap.restrict_id_hom] at this

/-- **Realizing a prime divisor of the model on the resolution.** On a common resolution
`p : V ⟶ X`, `q : V ⟶ Y` of `φ`, the strict transform `G_V` of a prime divisor `G` of `Y`,
regarded as a divisor over `X`, realizes `G` through `φ`. -/
private theorem isRealizedOver_of_isLogComparisonResolution {k : Type u} [Field k]
    {X Y V : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [IsSeparated sY]
    {φ : X.RationalMap Y} {KX : Divisor X} {ΔX : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y}
    {p : V ⟶ X} {q : V ⟶ Y} {h : X.RationalMap V} {GX GY : RDivisor V}
    (hR : IsLogComparisonResolution sX sY sV φ KX ΔX KY ΔY p q h GX GY) [IsProper p]
    (hWnp : IsNormalVariety k (p ≫ sX)) (G : MMP.Mori.PrimeDivisor Y)
    (GV : MMP.Mori.PrimeDivisor V) (heq : q GV.genericPoint = G.genericPoint)
    [IsIso (q.stalkMap GV.genericPoint)] :
    MMP.Flips.IsRealizedOver sX φ G
      (⟨⟨V, p, hWnp, hR.isBirationalMorphism_left, GV⟩, ‹IsProper p›⟩ :
        MMP.Flips.ProperDivisorOver k sX) := by
  have := isSeparated_toTerminal sY
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  obtain ⟨g, hg⟩ := Scheme.RationalMap.exists_rep φ
  refine ⟨g, q, hqb, hg, ?_, divisorialValuation_comap_functionFieldMap_eq q GV G heq⟩
  have hx : genericPoint X ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  have hA : genericPoint V ∈ p ⁻¹ᵁ g.domain := by
    change p (genericPoint V) ∈ g.domain
    rw [map_genericPoint_of_isDominant]
    exact hx
  refine hom_eq_of_fromSpecStalkOfMem_eq' _ hA ?_
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (p ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint V) hA ≫ (p ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk p
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc, ← c1,
    Category.assoc, ← partialMap_fromFunctionField_eq g hx,
    ← Scheme.RationalMap.fromFunctionField_toRationalMap, hg]
  exact (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hR.isInverse
    hR.compHom_eq).symm

/-- A rational map commuting with the structure morphisms at the generic point is a rational
map over `Spec k`. -/
private theorem compHom_eq_toRationalMap_of_fromFunctionField_comp {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X]
    (φ : X.RationalMap Y)
    (hφk : φ.fromFunctionField ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    φ.compHom sY = sX.toRationalMap := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom,
    Scheme.RationalMap.fromFunctionField_toRationalMap, hφk]
  exact (Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap _ _).symm

/-- The birational map to a nef log birational model commutes with the structure morphisms at
the generic point. -/
private theorem fromFunctionField_comp_eq_of_isNefLogBirationalModel {k : Type u} [Field k]
    {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {π : X ⟶ Z} {πY : Y ⟶ Z}
    {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {φ : X.RationalMap Y}
    (hY : IsNefLogBirationalModel sX sY sZ π πY KX Δ KY ΔY φ) :
    φ.fromFunctionField ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX := by
  have h1 := congrArg Scheme.RationalMap.fromFunctionField hY.isOver
  have h2 : π.toPartialMap.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ π :=
    Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap π _
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom,
    Scheme.RationalMap.fromFunctionField_toRationalMap, h2] at h1
  rw [← hY.comp_eq_model, ← Category.assoc, h1, Category.assoc, hY.comp_eq]

/-- Transforms of prime divisors under a rational map over `Spec k` to a proper separated `Y`
are determined by valuations. -/
private theorem transformPrimeDivisor_eq_some_iff_of_comp_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated sY] [IsProper sY] (φ : X.RationalMap Y) (θ : Y.functionField →+* X.functionField)
    (hθs : Function.Surjective θ)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (hφk : φ.fromFunctionField ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX)
    (P : MMP.Mori.PrimeDivisor X) (G : MMP.Mori.PrimeDivisor Y) :
    RationalMap.transformPrimeDivisor φ P = some G ↔
      P.divisorialValuation.comap θ = G.divisorialValuation :=
  transformPrimeDivisor_eq_some_iff_comap_eq (sY := sY) φ θ hθs hθ P
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one sX sY φ
      (compHom_eq_toRationalMap_of_fromFunctionField_comp φ hφk) P.coheight_genericPoint.le) G

open Classical in
/-- **Zero places of an snc boundary lie over its reduced part.** On a smooth variety, a divisor
over `X` of log discrepancy zero over an effective snc boundary `B` with coefficients at most one
has its centre on `⌊B⌋`: otherwise removing `⌊B⌋` does not change its log discrepancy, while the
remaining boundary is klt. -/
private theorem mem_floorSet_of_isLogDiscrepancy_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (hXn : IsNormalVariety k sX) (hXs : IsSmoothScheme sX) {B : RDivisor X}
    (hB0 : ∀ P, 0 ≤ B.coeff P) (hB1 : ∀ P, B.coeff P ≤ 1) (hBsnc : B.IsSNC sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (D : DivisorOver k sX)
    (h0 : MMP.Intersection.IsLogDiscrepancy sX n B D 0) :
    D.f D.E.genericPoint ∈ floorSet B := by
  by_contra hx
  set s := B.support.filter (fun P => B.coeff P = 1) with hs
  set B' : RDivisor X := B - ∑ P ∈ s, Finsupp.single P (1 : ℝ) with hB'def
  have hsum1 : ∀ Γ, (∑ P ∈ s, Finsupp.single P (1 : ℝ)) Γ = if Γ ∈ s then 1 else 0 := fun Γ => by
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hB'coeff : ∀ Γ, B'.coeff Γ = B.coeff Γ + if Γ ∈ s then (-1 : ℝ) else 0 := fun Γ => by
    rw [hB'def, DivisorWithCoeffs.coeff_sub]
    change B.coeff Γ - (∑ P ∈ s, Finsupp.single P (1 : ℝ)) Γ = _
    rw [hsum1]
    split_ifs <;> ring
  obtain ⟨e, he, hlog⟩ :=
    BoundaryCopy.exists_isLogDiscrepancy_of_coeff_eq hXs h0 s (fun _ => -1) hB'coeff
  have he0 : ∀ P ∈ s, e P = 0 := by
    intro P hP
    obtain ⟨hC, C', hpb, hC'⟩ := he P hP
    rw [← hC']
    refine BoundaryCopy.coeff_isPullback_eq_zero_of_forall
      (MMP.Fourfold.isCartier_of_isSmoothScheme hXs _) hpb fun Γ hΓ => ?_
    have hΓP : Γ ≠ P := fun h => hx ⟨P, (Finset.mem_filter.mp hP).2, h ▸ hΓ⟩
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, if_neg (Ne.symm hΓP)]
  have hsum : ∑ P ∈ s, (fun _ => (-1 : ℝ)) P * (e P : ℝ) = 0 :=
    Finset.sum_eq_zero fun P hP => by
      rw [he0 P hP]
      simp
  rw [hsum, sub_zero] at hlog
  have hmem : ∀ P, P ∉ s → B.coeff P < 1 := fun P hP => by
    refine lt_of_le_of_ne (hB1 P) fun h1 => hP ?_
    refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, h1⟩
    rw [← DivisorWithCoeffs.coeff_apply, h1]
    exact one_ne_zero
  have hklt := isRealKltPair_of_isSNC hXn hXs hK (Δ := B') B.support (fun P hP => by
      by_contra hPB
      apply Finsupp.mem_support_iff.mp hP
      have hBP : B.coeff P = 0 := Finsupp.notMem_support_iff.mp hPB
      have hPs : P ∉ s := fun h => hPB (Finset.mem_filter.mp h).1
      rw [← DivisorWithCoeffs.coeff_apply, hB'coeff, hBP, if_neg hPs, add_zero])
    (hBsnc.of_support_subset (by rw [support_sum_single]))
    (fun P => by
      rw [hB'coeff]
      split_ifs with h
      · rw [(Finset.mem_filter.mp h).2]
        norm_num
      · linarith [hB0 P])
    (fun P => by
      rw [hB'coeff]
      split_ifs with h
      · rw [(Finset.mem_filter.mp h).2]
        norm_num
      · linarith [hmem P h])
  exact lt_irrefl _ (hklt.2.2.2 n D 0 hlog)

end ZeroPlaces

/-! ### The two reference models -/

section ReferenceModels

open MMP.Mori

open Classical in
/-- **The reference model `W = X`** for a component `S` of `⌊B⌋`, with `F = ⌊B⌋ - S`. -/
private theorem exists_isReferenceModel_id {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hXs : IsSmoothScheme sX) {B C : RDivisor X} {A : QDivisor X} (hsnc : (B + C).IsSNC sX)
    (hA : A.HasRelativelyAmpleMultiple sX) (n : ℕ) (S : MMP.Mori.PrimeDivisor X)
    (hBS : B.coeff S = 1) :
    ∃ F : QDivisor X, IsReferenceModel sX B C A n (𝟙 X) S F := by
  have hXn : IsNormalVariety k sX := ⟨hXp.toIsVariety, inferInstance⟩
  have hnexc : ∀ P : MMP.Mori.PrimeDivisor X,
      ¬ RationalMap.IsExceptional (X := X) (Scheme.Hom.toRationalMap (𝟙 X)) P := fun P =>
    not_isExceptional_of_valuation_eq hXn (DivisorOver.ofPrimeDivisor k hXn P) P rfl
  set s := (B.support.filter fun P => B.coeff P = 1).erase S with hs
  set Fz : Divisor X := ∑ P ∈ s, Finsupp.single P (1 : ℤ) with hFz
  have hFzcoeff : ∀ P, Fz.coeff P = if P ∈ s then 1 else 0 := fun P => by
    rw [hFz, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hmems : ∀ P, P ∈ s ↔ B.coeff P = 1 ∧ P ≠ S := fun P => by
    rw [hs, Finset.mem_erase, Finset.mem_filter, Finsupp.mem_support_iff]
    refine ⟨fun ⟨h1, _, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, ?_, h2⟩⟩
    rw [← DivisorWithCoeffs.coeff_apply, h2]
    exact one_ne_zero
  set F : QDivisor X := Divisor.toQDivisor Fz with hFdef
  have hFcoeff : ∀ P, F.coeff P = if P ∈ s then 1 else 0 := fun P => by
    rw [hFdef, Divisor.coeff_toQDivisor, hFzcoeff]
    split_ifs <;> simp
  have hFzc : Fz.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hXs Fz
  have hFrel : F.HasRelativelyAmpleMultiple (𝟙 X) :=
    ⟨1, one_pos, Fz, hFzc, by rw [hFdef, Nat.cast_one, one_smul],
      isRelativelyAmple_of_isIso (𝟙 X) hFzc⟩
  have hsupp_floor : ∀ P : MMP.Mori.PrimeDivisor X, B.coeff P = 1 →
      (P.support : Set X) ⊆ (𝟙 X) ⁻¹' floorSet B := fun P hP x hx => ⟨P, hP, hx⟩
  refine ⟨F, ⟨by rwa [Category.id_comp], by rwa [Category.id_comp],
    by rwa [Category.id_comp], inferInstance, isBirationalMorphism_of_isIso _,
    fun P hP => absurd hP (hnexc P), fun P hP => absurd hP (hnexc P),
    ⟨S, hBS, PrimeDivisor.genericPoint_mem_support' S⟩, ?_,
    fun _ _ _ P hP => absurd hP (hnexc P), ?_, ?_, ?_, ?_,
    ?_⟩⟩
  · rw [Category.id_comp]
    exact BoundaryCopy.isSNCClosedSubset_supp hsnc
  · intro P
    change 0 ≤ F.coeff P
    rw [hFcoeff]
    split_ifs <;> norm_num
  · rw [hFcoeff, if_neg fun h => ((hmems S).mp h).2 rfl]
  · intro P hP
    rw [hFcoeff] at hP
    split_ifs at hP with h
    · exact hsupp_floor P ((hmems P).mp h).1
    · exact absurd rfl hP
  · intro P hPS hPf
    obtain ⟨D, hD1, hD⟩ := hPf (PrimeDivisor.genericPoint_mem_support' P)
    have hPD : P = D := (eq_of_genericPoint_mem_support hD).symm
    rw [hFcoeff, if_pos ((hmems P).mpr ⟨hPD ▸ hD1, hPS⟩)]
    exact one_pos
  · intro hA0 A' hA'
    exact exists_hasRelativelyAmpleMultiple_add_smul hXp (𝟙 X)
      (by rw [Category.id_comp]; exact hXp.toIsVariety) hFrel A hA hA0 A' hA'

/-- **The reference model of a zero place** `D` of `(X, B)`: stratum blow-ups extracting `D`. -/
private theorem exists_isReferenceModel_of_isLogDiscrepancy_eq_zero {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hXs : IsSmoothScheme sX) {B C : RDivisor X}
    {A : QDivisor X} (hsnc : (B + C).IsSNC sX) (hB : ∀ P, 0 ≤ B.coeff P)
    (hC : ∀ P, 0 ≤ C.coeff P) (hB1 : ∀ P, B.coeff P ≤ 1) (hBsnc : B.IsSNC sX)
    (hA : A.HasRelativelyAmpleMultiple sX) (hA₀ : 0 ≤ A) (hAB : A.toRDivisor ≤ B)
    (hAfl : ∀ P, A.coeff P ≠ 0 → B.coeff P < 1) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (D : MMP.Flips.ProperDivisorOver k sX)
    (hD : D.IsExceptional) (hD0 : MMP.Intersection.IsLogDiscrepancy sX n B D.toDivisorOver 0) :
    ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (p : W ⟶ X) (EW : MMP.Mori.PrimeDivisor W) (F : QDivisor W)
      (hRM : IsReferenceModel sX B C A n p EW F),
      haveI : IsDominant p := hRM.birational.isDominant
      EW.divisorialValuation.comap (functionFieldMap p) = D.valuation := by
  have hXn : IsNormalVariety k sX := ⟨hXp.toIsVariety, inferInstance⟩
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  obtain ⟨W, _, _, _, _, p, hN, hb, EW, hproj, hsm, hstrat, hval, hzeroW, hsncW, hApull⟩ :=
    MMP.Fourfold.exists_stratumBlowups_valuation_eq_of_isLogDiscrepancy_eq_zero sX hXp hXs B
      hB hB1 hBsnc D hD n hD0
  haveI : IsProper (p ≫ sX) := isProper_of_isProjectiveMorphism _ hproj.isProjective
  haveI : IsProper p := IsProper.of_comp p sX
  have hEWexc : RationalMap.IsExceptional (X := W) p.toRationalMap EW := by
    by_contra h
    obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXn
      (⟨W, p, hN, hb, EW⟩ : DivisorOver k sX) h
    haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
    exact ((MMP.Positivity.DivisorOver.two_le_codimension_center_iff hXn D.toDivisorOver).mp
      (by
        rw [MMP.Positivity.DivisorOver.codimension_center]
        exact (BoundaryCopy.properDivisorOver_isExceptional_iff hK.topologicalKrullDim_eq D).mp hD))
      Q (hval.symm.trans hQ)
  have hfloor : ∀ P : MMP.Mori.PrimeDivisor W,
      RationalMap.IsExceptional (X := W) p.toRationalMap P → p P.genericPoint ∈ floorSet B :=
    fun P hP => mem_floorSet_of_isLogDiscrepancy_eq_zero hXn hXs hB hB1 hBsnc hK
      ⟨W, p, hN, hb, P⟩ (hzeroW P hP)
  obtain ⟨F, hF0, hFrel, hFEW, hFsupp, hFpos, hFample⟩ :=
    MMP.Fourfold.exists_hasRelativelyAmpleMultiple_coeff_eq_zero_of_stratumBlowups sX hXp hXs B
      hB hB1 hBsnc p EW hEWexc hstrat
  have hBsupp : ((B.supp : Set X)) ⊆ ((B + C).supp : Set X) := fun x hx => by
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, fun h => hP ?_, hxP⟩
    rw [DivisorWithCoeffs.coeff_add] at h
    linarith [hB P, hC P]
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, p, EW, F,
    ⟨hproj, hsm, hN, inferInstance, hb, hzeroW, hfloor, hfloor EW hEWexc,
      hsncW _ hBsupp (BoundaryCopy.isSNCClosedSubset_supp hsnc),
      fun hA0 A' hA' P hP => hApull A hA₀ hAB (MMP.Fourfold.isQCartier_of_isSmoothScheme hXs A)
        hAfl hA0 A' hA' P hP, hF0, hFEW, hFsupp, hFpos, fun hA0 A' hA' => hFample A hA hA0 A' hA'⟩,
    hval⟩

end ReferenceModels

open Classical in
/-- **Avoided images under the inverse.** Let `Ξ` contain, for each prime divisor `G` in a finite
set `S`, the image of `η_G` under one partial map `Y ⇢ W` representing `ψ⁻¹` and defined at `η_G`
(when there is one), and let no component of `A'` pass through a point of `Ξ`. Then for `G ∈ S`
every partial map representing `ψ⁻¹` and defined at `η_G` sends `η_G` off `Supp A'`: all such
maps agree at `η_G`. -/
private theorem apply_notMem_supp_of_partialMap {W Y : Scheme.{u}} [IrreducibleSpace W]
    [IsReduced Y] [IsSeparated (W ↘ ⊤_ Scheme)] (ψ : W.RationalMap Y) (A' : QDivisor W)
    (Ξ : Finset W) (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hΞ : S.image (fun G => if h : ∃ q : Y.PartialMap W, (∃ e : W.PartialIso Y,
      e.toRationalMap = ψ ∧ e.symm.toRationalMap = q.toRationalMap) ∧
        G.genericPoint ∈ q.domain then h.choose.hom ⟨G.genericPoint, h.choose_spec.2⟩
      else genericPoint W) ⊆ Ξ)
    (hav : ∀ ξ ∈ Ξ, ∀ P : MMP.Mori.PrimeDivisor W, ξ ∈ P.support → A'.coeff P = 0)
    (G : MMP.Mori.PrimeDivisor Y) (hG : G ∈ S) (q : Y.PartialMap W)
    (hq : ∃ e : W.PartialIso Y, e.toRationalMap = ψ ∧ e.symm.toRationalMap = q.toRationalMap)
    (hGq : G.genericPoint ∈ q.domain) : q.hom ⟨G.genericPoint, hGq⟩ ∉ (A'.supp : Set W) := by
  have hex : ∃ q : Y.PartialMap W, (∃ e : W.PartialIso Y, e.toRationalMap = ψ ∧
      e.symm.toRationalMap = q.toRationalMap) ∧ G.genericPoint ∈ q.domain := ⟨q, hq, hGq⟩
  have hξ := hΞ (Finset.mem_image.mpr ⟨G, hG, dif_pos hex⟩)
  obtain ⟨e, he, heq⟩ := hq
  obtain ⟨e₀, he₀, he₀q⟩ := hex.choose_spec.1
  have hrat : hex.choose.toRationalMap = q.toRationalMap := by
    rw [← he₀q, ← heq, MMP.Positivity.PartialIso.symm_toRationalMap_eq (he₀.trans he.symm)]
  rw [MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hrat _ hGq] at hξ
  intro hmem
  obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  exact hP (hav _ hξ P hxP)

/-- If `0 ≤ a ≤ b < 1`, `0 ≤ γ`, `b + γ ≤ 1`, `0 < c N < 1` and `t < 1`, then `0 ≤ b - c N a`
and `b - c N a + t γ < 1`. -/
private theorem sub_mul_nonneg_and_add_mul_lt_one {b a γ cR N t : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hb1 : b < 1) (hγ0 : 0 ≤ γ) (hbγ : b + γ ≤ 1) (hcR : 0 < cR) (hN : 0 < N) (hcN : cR * N < 1)
    (ht1 : t < 1) :
    0 ≤ b - cR * N * a ∧ b - cR * N * a + t * γ < 1 := by
  have h1 : cR * N * a ≤ a := mul_le_of_le_one_left ha0 hcN.le
  have h2 : 0 ≤ cR * N * a := by positivity
  refine ⟨by linarith, ?_⟩
  rcases eq_or_lt_of_le hγ0 with h | h
  · rw [← h, mul_zero]
    linarith
  · have h3 : t * γ < γ := mul_lt_of_lt_one_left h ht1
    linarith

/-- For `0 < b`, eventually `1 / s * a < b` as the natural number `s` grows. -/
private theorem eventually_one_div_mul_lt (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ s : ℕ in Filter.atTop, (1 / (s : ℝ)) * a < b :=
  Filter.Tendsto.eventually_lt_const (by rwa [zero_mul])
    (tendsto_one_div_atTop_nhds_zero_nat.mul_const a)

open Classical in
/-- **The plt reference, given a reference model.** -/
private theorem exists_pltReference_of_isReferenceModel
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X} {KY : Divisor Y}
    {B C : RDivisor X} {A : QDivisor X} {t : ℝ}
    (hdlt : IsRealDltPair sX (B + C))
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hCB : ∀ P, C.coeff P ≠ 0 → B.coeff P < 1)
    (hA : A.HasRelativelyAmpleMultiple sX) (hA₀ : 0 ≤ A) (hAB : A.toRDivisor ≤ B)
    (hAfl : ∀ P, A.coeff P ≠ 0 → B.coeff P < 1)
    (ht : 0 < t) (ht₁ : t < 1)
    {φ : X.RationalMap Y} {BY : RDivisor Y}
    (hBY : ∀ F : MMP.Mori.PrimeDivisor Y,
      BY.coeff F = (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hY : IsNefLogBirationalModel sX sY sZ π πY KX (B + t • C) KY
      (BY + t • MMP.Mori.RationalMap.transformDivisor φ C) φ)
    (E : MMP.Mori.PrimeDivisor Y) (hE : BY.coeff E = 1)
    (θ : Y.functionField →+* X.functionField) (hθbij : Function.Bijective θ)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    {n : ℕ} (hKX : KX.IsCanonicalDivisor sX n)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ X) (EW : MMP.Mori.PrimeDivisor W) (F : QDivisor W)
    (hRM : IsReferenceModel sX B C A n p EW F)
    (hEW : haveI : IsDominant p := hRM.birational.isDominant
      (EW.divisorialValuation.comap (functionFieldMap p)).comap θ = E.divisorialValuation)
    (hiso : ¬ MMP.Flips.RationalMap.IsInverseExceptional φ E → IsIso p) :
        ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : CompactSpace W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of k)) (_ : LocallyOfFiniteType sW) (p : W ⟶ X)
      (hp : IsBirationalMorphism p) (ψ : W.RationalMap Y) (EW : MMP.Mori.PrimeDivisor W)
      (B' : RDivisor W) (A' : QDivisor W) (BY' : RDivisor Y),
      MMP.Mori.IsProjectiveVariety k sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sX = sW ∧
      (haveI := hp.isDominant;
        Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
          ψ.fromFunctionField) ∧
      (¬ MMP.Flips.RationalMap.IsInverseExceptional φ E → IsIso p) ∧
      MMP.Mori.RationalMap.transformPrimeDivisor ψ EW = some E ∧
      (IsRealLcPair sW B' ∧ ∀ (n : ℕ) (D : MMP.Mori.DivisorOver k sW), D.IsExceptional →
        ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sW n B' D a → 0 < a) ∧
      B'.coeff EW = 1 ∧ (∀ P, P ≠ EW → B'.coeff P < 1) ∧
      A'.HasRelativelyAmpleMultiple sW ∧ 0 ≤ A' ∧ A'.toRDivisor ≤ B' ∧ A'.coeff EW = 0 ∧
      (∃ (m : ℕ) (f : (RationalFunctions Y)ˣ), 0 < m ∧
        (m : ℝ) • (BY' - BY) = Divisor.toRDivisor (principalDivisor f)) ∧
      (IsRealLcPair sY BY' ∧ ∀ (n : ℕ) (D : MMP.Mori.DivisorOver k sY), D.IsExceptional →
        ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sY n BY' D a → 0 < a) ∧
      BY'.coeff E = 1 ∧ (∀ F, F ≠ E → BY'.coeff F < 1) ∧
      MMP.Mori.RationalMap.transformDivisor ψ A'.toRDivisor ≤ BY' ∧
      (IsRealLcPair sY (BY' + t • MMP.Mori.RationalMap.transformDivisor φ C) ∧
        ∀ (n : ℕ) (D : MMP.Mori.DivisorOver k sY), D.IsExceptional → ∀ a : ℝ,
          MMP.Intersection.IsLogDiscrepancy sY n
            (BY' + t • MMP.Mori.RationalMap.transformDivisor φ C) D a → 0 < a) ∧
      (∀ G : MMP.Mori.PrimeDivisor Y, MMP.Flips.RationalMap.IsInverseExceptional ψ G →
        ∀ D : MMP.Flips.ProperDivisorOver k sW, MMP.Flips.IsRealizedOver sW ψ G D →
          ¬ (D.center : Set W) ⊆ A'.supp) ∧
      IsNormal EW.idealSheaf.subscheme ∧
      ∀ G : MMP.Mori.PrimeDivisor Y, MMP.Flips.RationalMap.IsInverseExceptional ψ G →
        ∀ q : Y.PartialMap W, (∃ e : W.PartialIso Y, e.toRationalMap = ψ ∧
          e.symm.toRationalMap = q.toRationalMap) →
          ∀ hG : G.genericPoint ∈ q.domain, q.hom ⟨G.genericPoint, hG⟩ ∉ (A'.supp : Set W) := by
  -- the varieties
  have hXn : IsNormalVariety k sX := ⟨hXp.toIsVariety, inferInstance⟩
  have hYn : IsNormalVariety k sY := hY.isNormalVariety_model
  have hYp := hY.isProjectiveVariety_model
  haveI : AlgebraicGeometry.IsVariety k sY := hYn.1
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hYp.isProjective
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  have hWn := hRM.normal
  have hpb := hRM.birational
  haveI := hRM.proper
  haveI : IsDominant p := hpb.isDominant
  haveI : LocallyOfFiniteType (p ≫ sX) := hWn.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k (p ≫ sX) := hWn.1
  have hdimX : topologicalKrullDim X = n := hKX.topologicalKrullDim_eq
  have hdimW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm.trans
      hdimX
  -- `φ` and `p` over `k`
  have hφk := fromFunctionField_comp_eq_of_isNefLogBirationalModel hY
  have hm : (Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField) ≫ sY =
      W.fromSpecStalk (genericPoint W) ≫ p ≫ sX := by
    rw [Category.assoc, hφk, ← Category.assoc, functionFieldMap_fromSpecStalk p, Category.assoc]
  -- the map `ψ : W ⤏ Y`
  set ψ : W.RationalMap Y := Scheme.RationalMap.ofFunctionField (p ≫ sX) sY _ hm with hψdef
  have hψff : ψ.fromFunctionField =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField :=
    Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  set θψ : Y.functionField →+* W.functionField := (functionFieldMap p).comp θ with hθψdef
  have hθψ : Spec.map (CommRingCat.ofHom θψ) ≫ Y.fromSpecStalk (genericPoint Y) =
      ψ.fromFunctionField := by
    rw [hψff, hθψdef, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hθ]
  have hθψb : Function.Bijective θψ := hpb.functionFieldMap_bijective.comp hθbij
  have hψtr : ∀ (P : MMP.Mori.PrimeDivisor W) (G : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor ψ P = some G ↔
        P.divisorialValuation.comap θψ = G.divisorialValuation :=
    transformPrimeDivisor_eq_some_iff_of_comp_eq ψ θψ hθψb.2 hθψ (by rwa [hψff])
  have hφtr : ∀ (Q : MMP.Mori.PrimeDivisor X) (G : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor φ Q = some G ↔
        Q.divisorialValuation.comap θ = G.divisorialValuation :=
    transformPrimeDivisor_eq_some_iff_of_comp_eq φ θ hθbij.2 hθ hφk
  -- `ψ_* E_W = E`
  have hEWE : RationalMap.transformPrimeDivisor ψ EW = some E := by
    refine (hψtr EW E).2 ?_
    rw [← hEW]
    rfl
  -- at most one prime divisor of `W` maps onto a given one of `Y`
  have hψinj : ∀ (P P' : MMP.Mori.PrimeDivisor W) (G : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor ψ P = some G →
        RationalMap.transformPrimeDivisor ψ P' = some G → P = P' := fun P P' G h h' =>
    primeDivisor_eq_of_divisorialValuation_eq hWn (valuation_eq_of_comap_eq hθψb.2
      (((hψtr P G).1 h).trans ((hψtr P' G).1 h').symm))
  -- the canonical divisors
  obtain ⟨ωX, hωX0, hωXc⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hKX
  have hωX : divisorOfForm ωX = KX :=
    Finsupp.ext fun Γ => show (divisorOfForm ωX).coeff Γ = KX.coeff Γ from
      (coeff_divisorOfForm ωX Γ).trans (hωXc Γ)
  set KW : Divisor W := divisorOfForm (pullbackRationalPluriForms sX p ωX) with hKWdef
  have hpω0 : pullbackRationalPluriForms sX p ωX ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
      hpb.functionFieldMap_bijective
      (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdimX) hωX0
  have hKW : KW.IsCanonicalDivisor (p ≫ sX) n :=
    isCanonicalDivisor_divisorOfForm_of_isSmoothScheme hWn.1 hRM.smooth hdimW hpω0
  -- pull-backs of `K_X + B` and of `C`
  obtain ⟨GB, hGB⟩ := exists_isRCartierPullback_of_isSmoothScheme hXs p
    (MMP.Flips.logCanonicalDivisor KX B)
  obtain ⟨GC, hGC⟩ := exists_isRCartierPullback_of_isSmoothScheme hXs p C
  -- the pull-back of `A`
  have hAq : A.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hXs A
  have hA0W : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ A.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p A
  set AW : QDivisor W := QDivisor.pullback A hAq hA0W with hAWdef
  have hAW : QDivisor.IsPullback p A hA0W AW := QDivisor.isPullback_pullback hAq hA0W
  -- the ample divisor `m₀ (p^*A + δ F)`
  obtain ⟨δ₀, hδ₀, hδamp⟩ := hRM.F_ample hA0W AW hAW
  set δ : ℚ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨m₀, hm₀, L, hLc, hLeq, hLa⟩ := hδamp δ hδ (by linarith)
  -- the snc divisor on `W` carrying the total transform of `Supp (B + C)`
  haveI : TopologicalSpace.NoetherianSpace W :=
    MMP.Resolution.Aux.noetherianSpace_of_finiteType (p ≫ sX)
  set SW : Finset (MMP.Mori.PrimeDivisor W) :=
    (finite_setOf_support_subset hRM.isSNCClosedSubset).toFinset with hSWdef
  have hSWmem : ∀ P, P ∈ SW ↔ (P.support : Set W) ⊆ p ⁻¹' ((B + C).supp : Set X) := fun P => by
    rw [hSWdef, Set.Finite.mem_toFinset]
    rfl
  have hSW : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ E ∈ SW, Finsupp.single E (1 : ℤ)) :=
    isSNC_sum_single_of_support_subset hRM.smooth hRM.isSNCClosedSubset SW
      fun P hP => (hSWmem P).1 hP
  -- the points to avoid: centres on `W` of the prime divisors of `Y` extracted by `ψ`, and their
  -- images under the inverse of `ψ`
  set Ξ : Finset W := BY.support.image (fun G =>
    if h : ∃ D : MMP.Flips.ProperDivisorOver k (p ≫ sX),
      MMP.Flips.IsRealizedOver (p ≫ sX) ψ G D then h.choose.f h.choose.E.genericPoint
      else genericPoint W) ∪ BY.support.image (fun G =>
    if h : ∃ q : Y.PartialMap W, (∃ e : W.PartialIso Y, e.toRationalMap = ψ ∧
      e.symm.toRationalMap = q.toRationalMap) ∧ G.genericPoint ∈ q.domain then
      h.choose.hom ⟨G.genericPoint, h.choose_spec.2⟩ else genericPoint W) with hΞdef
  -- a general member `Z ∼ n₁ L`
  obtain ⟨n₁, fW, Zd, T, hn₁, hfW, hZ0, hZT, hTS, hsncT, hZav, hZc, hZa⟩ :=
    exists_generalMember hRM.projective hRM.smooth hLc hLa SW hSW Ξ
  -- the function `f` on `X` and `f_Y` on `Y`
  set Zx := MMP.Mori.pointComponent (genericPoint X)
  set Zw := MMP.Mori.pointComponent (genericPoint W)
  set Zy := MMP.Mori.pointComponent (genericPoint Y)
  obtain ⟨t₀, ht₀⟩ := hpb.functionFieldMap_bijective.2
    (MMP.Threefold.Mori.Helpers.evalFF Zw (fW : RationalFunctions W))
  have ht₀0 : t₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht₀
    exact (fW.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Zw)).ne_zero ht₀.symm
  obtain ⟨fX, hfX⟩ := exists_unit_evalFF_eq Zx ht₀0
  obtain ⟨t₁, hθt₁⟩ := hθbij.2 (MMP.Threefold.Mori.Helpers.evalFF Zx (fX : RationalFunctions X))
  have ht₁0 : t₁ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hθt₁
    exact (fX.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Zx)).ne_zero hθt₁.symm
  obtain ⟨fY, hfY⟩ := exists_unit_evalFF_eq Zy ht₁0
  have hfXY : θ (MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y)) =
      MMP.Threefold.Mori.Helpers.evalFF Zx (fX : RationalFunctions X) := by
    rw [hfY, hθt₁]
  have hfWY : θψ (MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y)) =
      MMP.Threefold.Mori.Helpers.evalFF Zw (fW : RationalFunctions W) := by
    rw [hθψdef, RingHom.comp_apply, hfXY, hfX, ht₀]
  /- Coefficients on `W`. -/
  have hd : (letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n) :=
    MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdimX
  have hfloor_supp : ∀ x ∈ floorSet B, x ∈ ((B + C).supp : Set X) := by
    rintro x ⟨D, hD1, hxD⟩
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨D, ?_, hxD⟩
    rw [DivisorWithCoeffs.coeff_add, hD1]
    linarith [hC D]
  have hpre_closed : IsClosed (p ⁻¹' ((B + C).supp : Set X)) :=
    (TopologicalSpace.Closeds.isClosed _).preimage p.continuous
  have hmemSW_of : ∀ P : MMP.Mori.PrimeDivisor W,
      p P.genericPoint ∈ ((B + C).supp : Set X) → P ∈ SW := fun P h =>
    (hSWmem P).2 (support_subset_of_genericPoint_mem P hpre_closed h)
  have hexcSW : ∀ P : MMP.Mori.PrimeDivisor W,
      RationalMap.IsExceptional (X := W) p.toRationalMap P → P ∈ SW := fun P hP =>
    hmemSW_of P (hfloor_supp _ (hRM.mem_floorSet P hP))
  have hEWSW : EW ∈ SW := hmemSW_of EW (hfloor_supp _ hRM.mem_floorSet_EW)
  have hFSW : ∀ P : MMP.Mori.PrimeDivisor W, F.coeff P ≠ 0 → P ∈ SW := fun P hP =>
    (hSWmem P).2 ((hRM.F_supp P hP).trans fun x hx => hfloor_supp _ hx)
  have hsub_floor : ∀ (P : MMP.Mori.PrimeDivisor W) (D : MMP.Mori.PrimeDivisor X),
      B.coeff D = 1 → p P.genericPoint ∈ D.support → (P.support : Set W) ⊆ p ⁻¹' floorSet B :=
    fun P D hD h => (support_subset_of_genericPoint_mem P
      ((TopologicalSpace.Closeds.isClosed _).preimage p.continuous) h).trans fun x hx => ⟨D, hD, hx⟩
  -- coefficients at strict transforms
  have hKWn : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → IsIso (p.stalkMap P.genericPoint) →
        KW.coeff P = KX.coeff Q := by
    intro P Q heq hiso
    rw [hKWdef, coeff_divisorOfForm, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p
      hpb.functionFieldMap_bijective hd P Q heq ωX, ← hωX, coeff_divisorOfForm]
  have hGBn : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → IsIso (p.stalkMap P.genericPoint) →
        GB.coeff P - KW.coeff P = B.coeff Q := by
    intro P Q heq hiso
    rw [coeff_isRCartierPullback_eq hGB P Q heq, hKWn P Q heq hiso, MMP.Flips.logCanonicalDivisor,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
    ring
  have hGCn : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → IsIso (p.stalkMap P.genericPoint) →
        GC.coeff P = C.coeff Q := fun P Q heq hiso => coeff_isRCartierPullback_eq hGC P Q heq
  have hAWn : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → IsIso (p.stalkMap P.genericPoint) →
        AW.coeff P = A.coeff Q := fun P Q heq hiso => coeff_isQPullback_eq hAq hAW P Q heq
  -- coefficients at exceptional prime divisors
  have hGBe : ∀ P : MMP.Mori.PrimeDivisor W,
      RationalMap.IsExceptional (X := W) p.toRationalMap P → GB.coeff P - KW.coeff P = 1 := by
    intro P hP
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hRM.logDiscrepancy_eq_zero P hP)
      (isLogDiscrepancy_of_isRCartierPullback hXn hKX hWn hpb ωX hωX0 hωX hGB P)
    linarith
  have hGBC : MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KX (B + C))
      (GB + GC) := by
    have := isRCartierPullback_add hGB hGC
    rwa [MMP.Flips.logCanonicalDivisor, ← add_assoc] at *
  have hGC0 : 0 ≤ GC := (MMP.Fourfold.isEffective_of_isRCartierPullback p
    (isRCartier_of_isSmoothScheme hXs C) hC).2 GC hGC
  have hGCe : ∀ P : MMP.Mori.PrimeDivisor W,
      RationalMap.IsExceptional (X := W) p.toRationalMap P → GC.coeff P = 0 := by
    intro P hP
    have h1 := hdlt.1.2.2.2 n _ _
      (isLogDiscrepancy_of_isRCartierPullback hXn hKX hWn hpb ωX hωX0 hωX hGBC P)
    have h2 := hGBe P hP
    have h3 : 0 ≤ GC.coeff P := hGC0 P
    rw [DivisorWithCoeffs.coeff_add] at h1
    linarith
  have hAWe : ∀ P : MMP.Mori.PrimeDivisor W,
      RationalMap.IsExceptional (X := W) p.toRationalMap P → AW.coeff P = 0 :=
    hRM.coeff_pullback hA0W AW hAW
  have hLcoeff : ∀ P : MMP.Mori.PrimeDivisor W,
      ((L.coeff P : ℤ) : ℚ) = m₀ * (AW.coeff P + δ * F.coeff P) := by
    intro P
    have := congrArg (fun G : QDivisor W => G.coeff P) hLeq
    simp [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul] at this
    rw [this]
    ring
  have hLcoeffR : ∀ P : MMP.Mori.PrimeDivisor W, ((L.coeff P : ℤ) : ℝ) =
      (m₀ : ℝ) * (((AW.coeff P : ℚ) : ℝ) + (δ : ℝ) * ((F.coeff P : ℚ) : ℝ)) := fun P => by
    exact_mod_cast hLcoeff P
  have hfWcoeff : ∀ P : MMP.Mori.PrimeDivisor W,
      (((principalDivisor fW).coeff P : ℤ) : ℝ) = (Zd.coeff P : ℝ) - n₁ * (L.coeff P : ℝ) := by
    intro P
    have := congrArg (fun G : Divisor W => G.coeff P) hfW
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul] at this
    rw [this, nsmul_eq_mul]
    push_cast
    ring
  /- The small rational number `c = 1/s`. -/
  obtain ⟨s, hs0, hs1, hs2, hs3, hs4⟩ : ∃ s : ℕ, 0 < s ∧
      (1 / (s : ℝ)) * ((n₁ : ℝ) * m₀) < 1 ∧
      (∀ P ∈ F.support, (1 / (s : ℝ)) * ((n₁ : ℝ) * m₀ * (δ : ℝ) * ((F.coeff P : ℚ) : ℝ)) < 1) ∧
      (∀ P ∈ Zd.support, (1 / (s : ℝ)) * (Zd.coeff P : ℝ) < 1) ∧
      (∀ G ∈ (principalDivisor fY).support, 0 < BY.coeff G →
        (1 / (s : ℝ)) * (-((principalDivisor fY).coeff G : ℝ)) < BY.coeff G) := by
    have h0 := Filter.eventually_gt_atTop 0
    have h1 := eventually_one_div_mul_lt ((n₁ : ℝ) * m₀) one_pos
    have h2 := (Filter.eventually_all_finset F.support).2 fun P _ =>
      eventually_one_div_mul_lt ((n₁ : ℝ) * m₀ * (δ : ℝ) * ((F.coeff P : ℚ) : ℝ)) one_pos
    have h3 := (Filter.eventually_all_finset Zd.support).2 fun P _ =>
      eventually_one_div_mul_lt (Zd.coeff P : ℝ) one_pos
    have h4 : ∀ᶠ s : ℕ in Filter.atTop, ∀ G ∈ (principalDivisor fY).support,
        0 < BY.coeff G → (1 / (s : ℝ)) * (-((principalDivisor fY).coeff G : ℝ)) < BY.coeff G :=
      (Filter.eventually_all_finset (principalDivisor fY).support).2 fun G _ => by
      by_cases hG : 0 < BY.coeff G
      · exact (eventually_one_div_mul_lt (-((principalDivisor fY).coeff G : ℝ)) hG).mono
          fun s hs _ => hs
      · exact Filter.Eventually.of_forall fun s h => absurd h hG
    exact (h0.and (h1.and (h2.and (h3.and h4)))).exists
  set c : ℚ := 1 / (s : ℚ) with hcdef
  set cR : ℝ := (c : ℝ) with hcRdef
  have hcR : cR = 1 / (s : ℝ) := by
    rw [hcRdef, hcdef]
    push_cast
    rfl
  have hcR0 : 0 < cR := by rw [hcR]; positivity
  /- The boundaries. -/
  set BW' : RDivisor W :=
    (GB - Divisor.toRDivisor KW) + cR • Divisor.toRDivisor (principalDivisor fW)
    with hBW'def
  set ΔW : RDivisor W := BW' + t • GC with hΔWdef
  set A' : QDivisor W := c • Divisor.toQDivisor Zd with hA'def
  set BY' : RDivisor Y := BY + cR • Divisor.toRDivisor (principalDivisor fY) with hBY'def
  have hBW'coeff : ∀ P : MMP.Mori.PrimeDivisor W, BW'.coeff P =
      (GB.coeff P - KW.coeff P) + cR * ((Zd.coeff P : ℝ) - n₁ * (L.coeff P : ℝ)) := by
    intro P
    rw [hBW'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, smul_eq_mul,
      hfWcoeff]
  have hZoff : ∀ P, P ∈ SW → Zd.coeff P = 0 := fun P hP => by
    by_contra h
    exact Finset.disjoint_left.mp hTS (hZT P h) hP
  have hZdEW : Zd.coeff EW = 0 := hZoff EW hEWSW
  /- The coefficients of `B'` and `C_W` on `W`. -/
  have key : ∀ P : MMP.Mori.PrimeDivisor W,
      (Zd.coeff P ≠ 0 → BW'.coeff P = cR * Zd.coeff P ∧ GC.coeff P = 0 ∧
        (((MMP.Mori.principalDivisor fW).coeff P : ℤ) : ℝ) = Zd.coeff P) ∧
      (Zd.coeff P = 0 → P = EW → BW'.coeff P = 1 ∧ GC.coeff P = 0) ∧
      (Zd.coeff P = 0 → P ≠ EW → 0 ≤ BW'.coeff P ∧ BW'.coeff P + t * GC.coeff P < 1) ∧
      (P ∉ SW → Zd.coeff P = 0 → BW'.coeff P = 0 ∧ GC.coeff P = 0) := by
    intro P
    have hLP := hLcoeffR P
    have hn₁0 : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
    have hm₀0 : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
    have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    -- the computation along a prime divisor over `⌊B⌋`, other than `E_W`
    have hfloorP : ∀ (hPF : (P.support : Set W) ⊆ p ⁻¹' floorSet B) (hPSW : P ∈ SW)
        (hBW : BW'.coeff P = 1 - cR * ((n₁ : ℝ) * m₀ * (δ : ℝ) * ((F.coeff P : ℚ) : ℝ)))
        (hGC : GC.coeff P = 0),
        (Zd.coeff P ≠ 0 → BW'.coeff P = cR * Zd.coeff P ∧ GC.coeff P = 0 ∧
          (((MMP.Mori.principalDivisor fW).coeff P : ℤ) : ℝ) = Zd.coeff P) ∧
        (Zd.coeff P = 0 → P = EW → BW'.coeff P = 1 ∧ GC.coeff P = 0) ∧
        (Zd.coeff P = 0 → P ≠ EW → 0 ≤ BW'.coeff P ∧ BW'.coeff P + t * GC.coeff P < 1) ∧
        (P ∉ SW → Zd.coeff P = 0 → BW'.coeff P = 0 ∧ GC.coeff P = 0) := by
      intro hPF hPSW hBW hGC
      have hZP : Zd.coeff P = 0 := hZoff P hPSW
      refine ⟨fun h => absurd hZP h, fun _ hPE => ⟨?_, hGC⟩, fun _ hPE => ?_,
        fun h => absurd hPSW h⟩
      · rw [hBW, hPE, hRM.F_EW]
        simp
      · have hF : 0 < F.coeff P := hRM.F_pos P hPE hPF
        have hFs : P ∈ F.support := Finsupp.mem_support_iff.mpr hF.ne'
        have h2 := hs2 P hFs
        have hF' : (0 : ℝ) < ((F.coeff P : ℚ) : ℝ) := by exact_mod_cast hF
        have hpos : 0 < (n₁ : ℝ) * m₀ * (δ : ℝ) * ((F.coeff P : ℚ) : ℝ) := by positivity
        rw [hBW, hGC, hcR]
        refine ⟨by linarith, ?_⟩
        have : 0 < 1 / (s : ℝ) * ((n₁ : ℝ) * m₀ * (δ : ℝ) * ((F.coeff P : ℚ) : ℝ)) := by
          have : (0 : ℝ) < 1 / (s : ℝ) := by positivity
          positivity
        linarith
    by_cases hPe : RationalMap.IsExceptional (X := W) p.toRationalMap P
    · -- an exceptional prime divisor
      have hPSW := hexcSW P hPe
      have hZP : Zd.coeff P = 0 := hZoff P hPSW
      rw [hAWe P hPe] at hLP
      obtain ⟨D, hD1, hD⟩ := hRM.mem_floorSet P hPe
      refine hfloorP (hsub_floor P D hD1 hD) hPSW ?_ (hGCe P hPe)
      rw [hBW'coeff, hGBe P hPe, hZP, hLP]
      push_cast
      ring
    · obtain ⟨Q, hPQ, hiso⟩ := exists_eq_genericPoint_of_not_isExceptional hXn p hWn hpb P hPe
      have h1 := hGBn P Q hPQ hiso
      have h2 := hGCn P Q hPQ hiso
      have h3 := hAWn P Q hPQ hiso
      have hQs : p P.genericPoint ∈ Q.support := hPQ ▸ PrimeDivisor.genericPoint_mem_support' Q
      by_cases hBQ : B.coeff Q = 1
      · -- a prime divisor over `⌊B⌋`
        have hAQ : A.coeff Q = 0 := by
          by_contra h
          exact (hAfl Q h).ne hBQ
        have hCQ : C.coeff Q = 0 := by
          by_contra h
          exact (hCB Q h).ne hBQ
        have hPSW : P ∈ SW := hmemSW_of P (hfloor_supp _ ⟨Q, hBQ, hQs⟩)
        have hZP : Zd.coeff P = 0 := hZoff P hPSW
        rw [h3, hAQ] at hLP
        refine hfloorP (hsub_floor P Q hBQ hQs) hPSW ?_ (by rw [h2, hCQ])
        rw [hBW'coeff, h1, hBQ, hZP, hLP]
        push_cast
        ring
      · -- a prime divisor off `⌊B⌋`
        have hBC1 : (B + C).coeff Q ≤ 1 := hdlt.2.1 Q
        rw [DivisorWithCoeffs.coeff_add] at hBC1
        have hBQ1 : B.coeff Q < 1 := lt_of_le_of_ne (by linarith [hC Q]) hBQ
        have hFP : F.coeff P = 0 := by
          by_contra hF
          obtain ⟨D, hD1, hD⟩ := hRM.F_supp P hF (PrimeDivisor.genericPoint_mem_support' P)
          rw [hPQ] at hD
          rw [(eq_of_genericPoint_mem_support hD).symm] at hBQ
          exact hBQ hD1
        rw [h3, hFP] at hLP
        have hAB' : ((A.coeff Q : ℚ) : ℝ) ≤ B.coeff Q := by
          have := hAB Q
          change (QDivisor.toRDivisor A).coeff Q ≤ B.coeff Q at this
          rwa [QDivisor.coeff_toRDivisor] at this
        have hA0' : (0 : ℝ) ≤ ((A.coeff Q : ℚ) : ℝ) := by exact_mod_cast hA₀ Q
        have hBW : BW'.coeff P =
            B.coeff Q + cR * ((Zd.coeff P : ℝ) - n₁ * m₀ * (A.coeff Q : ℝ)) := by
          rw [hBW'coeff, h1, hLP]
          push_cast
          ring
        -- if `P` is not over `Supp (B + C)`, everything vanishes but `Z`
        have hoff : P ∉ SW → B.coeff Q = 0 ∧ C.coeff Q = 0 ∧ A.coeff Q = 0 := by
          intro hPSW
          have hBC0 : (B + C).coeff Q = 0 := by
            by_contra h
            exact hPSW (hmemSW_of P (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, h, hQs⟩))
          rw [DivisorWithCoeffs.coeff_add] at hBC0
          have hB0 : B.coeff Q = 0 := by linarith [hB Q, hC Q]
          refine ⟨hB0, by linarith [hB Q, hC Q], ?_⟩
          have : ((A.coeff Q : ℚ) : ℝ) = 0 := le_antisymm (hB0 ▸ hAB') hA0'
          exact_mod_cast this
        refine ⟨fun hZ => ?_, fun hZ hPE => ?_, fun hZ _ => ?_, fun hPSW hZ => ?_⟩
        · have hPSW : P ∉ SW := Finset.disjoint_left.mp hTS (hZT P hZ)
          obtain ⟨hB0, hC0, hA0⟩ := hoff hPSW
          refine ⟨?_, by rw [h2, hC0], ?_⟩
          · rw [hBW, hB0, hA0]
            push_cast
            ring
          · rw [hfWcoeff P, hLP, hA0]
            push_cast
            ring
        · exfalso
          obtain ⟨D, hD1, hD⟩ := hRM.mem_floorSet_EW
          rw [← hPE, hPQ] at hD
          rw [(eq_of_genericPoint_mem_support hD).symm] at hBQ
          exact hBQ hD1
        · have hc1 : cR * ((n₁ : ℝ) * m₀) < 1 := by rwa [hcR]
          have hBW0 : BW'.coeff P = B.coeff Q - cR * ((n₁ : ℝ) * m₀) * ((A.coeff Q : ℚ) : ℝ) := by
            rw [hBW, hZ]
            push_cast
            ring
          rw [hBW0, h2]
          exact sub_mul_nonneg_and_add_mul_lt_one hA0' hAB' hBQ1 (hC Q) hBC1 hcR0
            (by positivity) hc1 ht₁
        · obtain ⟨hB0, hC0, hA0⟩ := hoff hPSW
          rw [hBW, hB0, hA0, hZ, h2, hC0]
          simp
  /- Consequences on `W`. -/
  have hBW0 : ∀ P, 0 ≤ BW'.coeff P := fun P => by
    by_cases hZ : Zd.coeff P = 0
    · by_cases hPE : P = EW
      · rw [((key P).2.1 hZ hPE).1]
        exact zero_le_one
      · exact ((key P).2.2.1 hZ hPE).1
    · rw [((key P).1 hZ).1]
      exact mul_nonneg hcR0.le (by exact_mod_cast hZ0 P)
  have hBWEW : BW'.coeff EW = 1 := ((key EW).2.1 hZdEW rfl).1
  have hGCEW : GC.coeff EW = 0 := ((key EW).2.1 hZdEW rfl).2
  have hZlt : ∀ P, Zd.coeff P ≠ 0 → cR * Zd.coeff P < 1 := fun P hZ => by
    rw [hcR]
    exact hs3 P (Finsupp.mem_support_iff.mpr hZ)
  have hΔW1 : ∀ P, P ≠ EW → BW'.coeff P + t * GC.coeff P < 1 := fun P hPE => by
    by_cases hZ : Zd.coeff P = 0
    · exact ((key P).2.2.1 hZ hPE).2
    · rw [((key P).1 hZ).1, ((key P).1 hZ).2.1, mul_zero, add_zero]
      exact hZlt P hZ
  have hBW1 : ∀ P, P ≠ EW → BW'.coeff P < 1 := fun P hPE => by
    have h1 := hΔW1 P hPE
    have h0 : 0 ≤ t * GC.coeff P := mul_nonneg ht.le (hGC0 P)
    linarith
  have hsuppW : ∀ P, P ∉ T ∪ SW → BW'.coeff P = 0 ∧ GC.coeff P = 0 := fun P hP => by
    have hPT : P ∉ T := fun h => hP (Finset.mem_union_left _ h)
    have hPSW : P ∉ SW := fun h => hP (Finset.mem_union_right _ h)
    have hZ : Zd.coeff P = 0 := by
      by_contra h
      exact hPT (hZT P h)
    exact (key P).2.2.2 hPSW hZ
  have hEWTS : EW ∈ T ∪ SW := Finset.mem_union_right _ hEWSW
  have hΔWcoeff : ∀ P, ΔW.coeff P = BW'.coeff P + t * GC.coeff P := fun P => by
    rw [hΔWdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  -- plt on `W`
  have hpltW : ∀ D : RDivisor W, (∀ P, 0 ≤ D.coeff P) → (∀ P, P ∉ T ∪ SW → D.coeff P = 0) →
      D.coeff EW ≤ 1 → (∀ P, P ≠ EW → D.coeff P < 1) → ∀ (d : ℕ) (D' : DivisorOver k (p ≫ sX))
        (a : ℝ), MMP.Intersection.IsLogDiscrepancy (p ≫ sX) d D D' a →
          0 ≤ a ∧ (a = 0 → D'.valuation = (DivisorOver.ofPrimeDivisor k hWn EW).valuation) := by
    intro D hD0 hDS hDEW hD1 d D' a ha
    refine isLogDiscrepancy_nonneg_of_isSNC hWn hRM.smooth hKW (T ∪ SW) (fun P hP => ?_) hsncT
      hD0 EW hEWTS hDEW hD1 ha
    by_contra h
    exact (Finsupp.mem_support_iff.mp hP) (hDS P h)
  have hpltBW := hpltW BW' hBW0 (fun P hP => (hsuppW P hP).1) hBWEW.le hBW1
  have hΔW0 : ∀ P, 0 ≤ ΔW.coeff P := fun P => by
    rw [hΔWcoeff]
    exact add_nonneg (hBW0 P) (mul_nonneg ht.le (hGC0 P))
  have hΔWS : ∀ P, P ∉ T ∪ SW → ΔW.coeff P = 0 := fun P hP => by
    rw [hΔWcoeff, (hsuppW P hP).1, (hsuppW P hP).2]
    ring
  have hΔWEW : ΔW.coeff EW = 1 := by
    rw [hΔWcoeff, hBWEW, hGCEW]
    ring
  have hpltΔW := hpltW ΔW hΔW0 hΔWS hΔWEW.le (fun P hPE => by rw [hΔWcoeff]; exact hΔW1 P hPE)
  /- The comparison on a common resolution of `X` and `Y`, shifted by `c div f`. -/
  obtain ⟨V, _, _, _, sV, p₀, q₀, h₀, GX₀, GY₀, hR₀⟩ := hY.exists_resolution
  obtain ⟨nY, hKY⟩ := hY.isCanonicalDivisor_model
  obtain ⟨L₀, hR'⟩ := exists_isLogComparisonResolution_add_smul hR₀ θ hθ fX fY Zx Zy hfXY cR
  set CY : RDivisor Y := MMP.Mori.RationalMap.transformDivisor φ C with hCYdef
  have hΔY : (BY + t • CY) + cR • Divisor.toRDivisor (principalDivisor fY) = BY' + t • CY := by
    rw [hBY'def]
    abel
  rw [hΔY] at hR'
  -- the crepant pull-back to `W`
  haveI := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := W)
  have hφp := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p (principalDivisor fX)
  have hLp := Divisor.isPullback_principalDivisor fX hφp
  have hpf : principalDivisor (pullbackRationalFunction p fX hφp) = principalDivisor fW := by
    refine Finsupp.ext fun P => ?_
    change (MMP.Mori.principalDivisor _).coeff P = (MMP.Mori.principalDivisor fW).coeff P
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hLp
      (Divisor.isLocalEquation_principalDivisor fX ⊤) P trivial Zx, hfX, ht₀,
      coeff_principalDivisor, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
      show P.component = Zw from Subsingleton.elim _ _]
  have hprin : MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (principalDivisor fX))
      (Divisor.toRDivisor (principalDivisor fW)) :=
    isRCartierPullback_of_isPullback (Divisor.isCartier_principalDivisor fX) (hpf ▸ hLp)
  have hDW : MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) +
      ((B + t • C) + cR • Divisor.toRDivisor (principalDivisor fX)))
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX)) + ΔW) := by
    have h := isRCartierPullback_add hGB (isRCartierPullback_add (isRCartierPullback_smul t hGC)
      (isRCartierPullback_smul cR hprin))
    convert h using 1
    · rw [MMP.Flips.logCanonicalDivisor, hωX]
      abel
    · rw [hΔWdef, hBW'def, ← hKWdef]
      abel
  -- log discrepancies over `Y`
  have hEval :
      ((DivisorOver.ofPrimeDivisor k hWn EW).valuation.comap (functionFieldMap p)).comap θ =
      (DivisorOver.ofPrimeDivisor k hYn E).valuation := by
    rw [valuation_ofPrimeDivisor, valuation_ofPrimeDivisor, ← hEW]
  have hY0 : ∀ (d : ℕ) (D : DivisorOver k sY) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sY d (BY' + t • CY) D a →
        0 ≤ a ∧ (a = 0 → D.valuation = (DivisorOver.ofPrimeDivisor k hYn E).valuation) := by
    intro d D a ha
    have h := logDiscrepancy_nonneg_of_isLogComparisonResolution_of_crepant hR' hXn hYn hKX hKY θ
      hθ p hWn hpb hωX0 hωX hDW hKW _ hpltΔW d D a ha
    exact ⟨h.1, fun h0 => (h.2 h0).trans hEval⟩
  /- Coefficients on `Y`. -/
  have hBY0 : ∀ G, 0 ≤ BY.coeff G := fun G => by
    rw [hBY G]
    have := (le_mapPrimeDivisors_apply (MMP.Mori.RationalMap.transformPrimeDivisor φ) hB G).1
    change 0 ≤ (MMP.Mori.RationalMap.transformDivisor φ B).coeff G at this
    split_ifs <;> linarith
  have hCY0 : ∀ G, 0 ≤ CY.coeff G := fun G =>
    (le_mapPrimeDivisors_apply (MMP.Mori.RationalMap.transformPrimeDivisor φ) hC G).1
  haveI := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := Y)
  have hordψ : ∀ (P : MMP.Mori.PrimeDivisor W) (G : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor ψ P = some G →
        (MMP.Mori.principalDivisor fY).coeff G = (MMP.Mori.principalDivisor fW).coeff P := by
    intro P G hPG
    have hne : MMP.Threefold.Mori.Helpers.evalFF Zy (fY : RationalFunctions Y) ≠ 0 :=
      (fY.isUnit.map _).ne_zero
    have h := ord_eq_of_comap_eq θψ P G ((hψtr P G).1 hPG) hne
    rw [hfWY] at h
    rw [coeff_principalDivisor, coeff_principalDivisor,
      MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
      show G.component = Zy from Subsingleton.elim _ _,
      show P.component = Zw from Subsingleton.elim _ _]
    exact h.symm
  have hBY'coeff : ∀ G, BY'.coeff G =
      BY.coeff G + cR * (((MMP.Mori.principalDivisor fY).coeff G : ℤ) : ℝ) := fun G => by
    rw [hBY'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toRDivisor, smul_eq_mul]
  -- `B'_Y` along `E`
  have hGBKWEW : GB.coeff EW - KW.coeff EW = 1 := by
    by_cases hex : RationalMap.IsExceptional (X := W) p.toRationalMap EW
    · exact hGBe EW hex
    · obtain ⟨Q, hQ, hisoQ⟩ := exists_eq_genericPoint_of_not_isExceptional hXn p hWn hpb EW hex
      obtain ⟨D, hD1, hD⟩ := hRM.mem_floorSet_EW
      rw [hQ] at hD
      rw [hGBn EW Q hQ hisoQ, (eq_of_genericPoint_mem_support hD).symm, hD1]
  have hfWEW : (((MMP.Mori.principalDivisor fW).coeff EW : ℤ) : ℝ) = 0 := by
    have h1 := hBW'coeff EW
    rw [hBWEW, hGBKWEW, ← hfWcoeff] at h1
    have h2 : cR * (((MMP.Mori.principalDivisor fW).coeff EW : ℤ) : ℝ) = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_left hcR0.ne'
  have hBY'E : BY'.coeff E = 1 := by
    rw [hBY'coeff, hE, hordψ EW E hEWE, hfWEW, mul_zero, add_zero]
  -- `B'_Y` is effective
  have hBY'0 : ∀ G, 0 ≤ BY'.coeff G := fun G => by
    rw [hBY'coeff]
    by_cases hGs : G ∈ (MMP.Mori.principalDivisor fY).support
    · rcases (hBY0 G).lt_or_eq with hpos | hzero'
      · have := hs4 G hGs hpos
        rw [hcR]
        linarith
      · have hnotnew : ¬ MMP.Flips.RationalMap.IsInverseExceptional φ G := fun hnew => by
          have h3 := hBY G
          rw [if_pos hnew] at h3
          have h2 := (le_mapPrimeDivisors_apply
            (MMP.Mori.RationalMap.transformPrimeDivisor φ) hB G).1
          change 0 ≤ (MMP.Mori.RationalMap.transformDivisor φ B).coeff G at h2
          linarith
        obtain ⟨Q, hQG⟩ : ∃ Q, MMP.Mori.RationalMap.transformPrimeDivisor φ Q = some G := by
          by_contra h
          push Not at h
          exact hnotnew h
        have hBQ : B.coeff Q = 0 := by
          have h2 := (le_mapPrimeDivisors_apply
            (MMP.Mori.RationalMap.transformPrimeDivisor φ) hB G).2 Q hQG
          have h3 := hBY G
          rw [if_neg hnotnew, add_zero] at h3
          change B.coeff Q ≤ (MMP.Mori.RationalMap.transformDivisor φ B).coeff G at h2
          exact le_antisymm (by linarith) (hB Q)
        have hord := coeff_principalDivisor_eq_of_transformPrimeDivisor_eq_some hR₀ hXn hYn θ hθ
          fX fY Zx Zy hfXY hQG
        obtain ⟨QW, hQW, hisoQ, -⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWn hpb Q
        have h4 := coeff_isRCartierPullback_eq hprin QW Q hQW
        rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor] at h4
        have hAQ : A.coeff Q = 0 := by
          have h5 := hAB Q
          change (QDivisor.toRDivisor A).coeff Q ≤ B.coeff Q at h5
          rw [QDivisor.coeff_toRDivisor, hBQ] at h5
          exact le_antisymm (by exact_mod_cast h5) (hA₀ Q)
        have hFQ : F.coeff QW = 0 := by
          by_contra hF
          obtain ⟨D, hD1, hD⟩ := hRM.F_supp QW hF (PrimeDivisor.genericPoint_mem_support' QW)
          rw [hQW] at hD
          rw [(eq_of_genericPoint_mem_support hD).symm, hD1] at hBQ
          exact one_ne_zero hBQ
        have hLQ := hLcoeffR QW
        rw [hAWn QW Q hQW hisoQ, hAQ, hFQ] at hLQ
        have h6 := hfWcoeff QW
        rw [hLQ] at h6
        rw [← hzero', hord, ← h4, h6]
        push_cast
        have : (0 : ℝ) ≤ (Zd.coeff QW : ℝ) := by exact_mod_cast hZ0 QW
        linarith only [mul_nonneg hcR0.le this]
    · have h0 : (MMP.Mori.principalDivisor fY).coeff G = 0 := Finsupp.notMem_support_iff.mp hGs
      rw [h0, Int.cast_zero, mul_zero, add_zero]
      exact hBY0 G
  -- `B'_Y < 1` off `E`
  have hRCY : ∀ D : RDivisor Y, RDivisor.IsRCartier D := isRCartier_of_isQFactorial hY.isQFactorial
  have hBY'1 : ∀ G, G ≠ E → BY'.coeff G < 1 := fun G hGE => by
    have hb := isLogDiscrepancy_ofPrimeDivisor hYn hKY (B := BY' + t • CY) (hRCY _) G
    obtain ⟨h0, h1⟩ := hY0 _ _ _ hb
    have hne : 1 - (BY' + t • CY).coeff G ≠ 0 := fun h => hGE
      (primeDivisor_eq_of_divisorialValuation_eq hYn (by
        rw [← valuation_ofPrimeDivisor hYn G, ← valuation_ofPrimeDivisor hYn E]
        exact h1 h))
    have hlt := lt_of_le_of_ne h0 (Ne.symm hne)
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hlt
    have := mul_nonneg ht.le (hCY0 G)
    linarith
  -- `ψ_* A' ≤ B'_Y`
  have hA'coeff : ∀ P, A'.coeff P = c * (Zd.coeff P : ℚ) := fun P => by
    rw [hA'def, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
  have hA'coeffR : ∀ P, (QDivisor.toRDivisor A').coeff P = cR * (Zd.coeff P : ℝ) := fun P => by
    rw [QDivisor.coeff_toRDivisor, hA'coeff, Rat.cast_mul, Rat.cast_intCast]
  have hψA' : MMP.Mori.RationalMap.transformDivisor ψ (QDivisor.toRDivisor A') ≤ BY' := by
    intro G
    change DivisorWithCoeffs.mapPrimeDivisors (MMP.Mori.RationalMap.transformPrimeDivisor ψ)
      (QDivisor.toRDivisor A') G ≤ BY' G
    rw [mapPrimeDivisors_apply_eq_sum]
    by_cases hex : ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some G ∧ Zd.coeff P ≠ 0
    · obtain ⟨P₀, hP₀G, hP₀Z⟩ := hex
      have hterm : ∀ P, (if MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some G then
          (QDivisor.toRDivisor A') P else 0) = if P = P₀ then cR * (Zd.coeff P₀ : ℝ) else 0 := by
        intro P
        by_cases hP : P = P₀
        · subst hP
          rw [if_pos hP₀G, if_pos rfl]
          exact hA'coeffR P
        · rw [if_neg hP]
          split_ifs with h
          · exact absurd (hψinj P P₀ G h hP₀G) hP
          · rfl
      rw [Finset.sum_congr rfl fun P _ => hterm P, Finset.sum_ite_eq']
      change _ ≤ BY'.coeff G
      rw [hBY'coeff, hordψ P₀ G hP₀G, ((key P₀).1 hP₀Z).2.2]
      have hZnn : (0 : ℝ) ≤ (Zd.coeff P₀ : ℝ) := by exact_mod_cast hZ0 P₀
      have := hBY0 G
      have := mul_nonneg hcR0.le hZnn
      split_ifs <;> linarith
    · push Not at hex
      rw [Finset.sum_eq_zero]
      · exact hBY'0 G
      · intro P _
        split_ifs with h
        · change (QDivisor.toRDivisor A').coeff P = 0
          rw [hA'coeffR, hex P h, Int.cast_zero, mul_zero]
        · rfl
  -- `B'_Y` is plt
  have hBY'lc : ∀ (d : ℕ) (D : DivisorOver k sY) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sY d BY' D a →
        0 ≤ a ∧ (a = 0 → D.valuation = (DivisorOver.ofPrimeDivisor k hYn E).valuation) := by
    intro d D a ha
    obtain ⟨a', ha'a, ha'⟩ := exists_isLogDiscrepancy_le_add (hRCY (t • CY))
      (fun P => by
        rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
        exact mul_nonneg ht.le (hCY0 P)) ha
    obtain ⟨h0, h1⟩ := hY0 d D a' ha'
    exact ⟨h0.trans ha'a, fun h => h1 (le_antisymm (h ▸ ha'a) h0)⟩
  -- the primes extracted by `ψ` are new over `X`, hence components of `B_Y`
  have hnew : ∀ G, MMP.Flips.RationalMap.IsInverseExceptional ψ G → G ∈ BY.support := by
    intro G hG
    have hGnew : MMP.Flips.RationalMap.IsInverseExceptional φ G := fun Q hQG => by
      obtain ⟨QW, hQW, hisoQ, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWn hpb Q
      haveI := hisoQ
      refine hG QW ((hψtr QW G).2 ?_)
      rw [← (hφtr Q G).1 hQG, ← divisorialValuation_comap_functionFieldMap_eq p QW Q hQW]
      rfl
    rw [Finsupp.mem_support_iff]
    have h3 := hBY G
    rw [if_pos hGnew] at h3
    have h2 := (le_mapPrimeDivisors_apply (MMP.Mori.RationalMap.transformPrimeDivisor φ) hB G).1
    change 0 ≤ (MMP.Mori.RationalMap.transformDivisor φ B).coeff G at h2
    intro h0
    change BY.coeff G = 0 at h0
    linarith
  have hA'av : ∀ ξ ∈ Ξ, ∀ P : MMP.Mori.PrimeDivisor W, ξ ∈ P.support → A'.coeff P = 0 :=
    fun ξ hξ P hξP => by rw [hA'coeff, hZav ξ hξ P hξP, Int.cast_zero, mul_zero]
  -- `E_W` is a component of an snc divisor, hence smooth
  have hEWn : IsNormal EW.idealSheaf.subscheme :=
    haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _
      (hSW.1 EW (by rwa [support_sum_single]))
    isNormal_of_smooth_over_field (EW.idealSheaf.subschemeι ≫ p ≫ sX)
  haveI : IsSeparated (p ≫ sX) := hWn.1.toIsSeparated
  haveI := isSeparated_toTerminal (p ≫ sX)
  /- The conclusion. -/
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, p ≫ sX, inferInstance, p,
    hpb, ψ, EW, BW', A', BY', hRM.projective, hRM.smooth, rfl, hψff.symm, hiso, hEWE,
    isRealLcPair_and_pos_of_isLogDiscrepancy hWn hBW0 hKW
      (isRCartier_of_isSmoothScheme hRM.smooth _) EW hpltBW,
    hBWEW, hBW1, ⟨s, hs0, Zd, hZc, ?_, hZa⟩, ?_, ?_, ?_, ⟨s, fY, hs0, ?_⟩,
    isRealLcPair_and_pos_of_isLogDiscrepancy hYn hBY'0 hKY (hRCY _) E hBY'lc, hBY'E, hBY'1, hψA',
    isRealLcPair_and_pos_of_isLogDiscrepancy hYn ?_ hKY (hRCY _) E hY0, fun G hG D hD =>
    not_center_subset_of_isRealizedOver hWn ψ θψ hθψb.2 hθψ A' Ξ BY.support
      Finset.subset_union_left hA'av G (hnew G hG) D hD, hEWn,
    fun G hG q hq hGq => apply_notMem_supp_of_partialMap ψ A' Ξ BY.support
      Finset.subset_union_right hA'av G (hnew G hG) q hq hGq⟩
  · rw [hA'def, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, hcdef, Int.cast_natCast,
      mul_one_div_cancel (by exact_mod_cast hs0.ne' : (s : ℚ) ≠ 0), one_smul]
  · intro P
    change 0 ≤ A'.coeff P
    rw [hA'coeff]
    exact mul_nonneg (by rw [hcdef]; positivity) (by exact_mod_cast hZ0 P)
  · intro P
    change (QDivisor.toRDivisor A').coeff P ≤ BW'.coeff P
    rw [hA'coeffR]
    by_cases hZ : Zd.coeff P = 0
    · rw [hZ, Int.cast_zero, mul_zero]
      exact hBW0 P
    · rw [((key P).1 hZ).1]
  · rw [hA'coeff, hZdEW, Int.cast_zero, mul_zero]
  · rw [hBY'def, add_sub_cancel_left, smul_smul, hcR,
      mul_one_div_cancel (by exact_mod_cast hs0.ne' : (s : ℝ) ≠ 0), one_smul]
  · intro P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    exact add_nonneg (hBY'0 P) (mul_nonneg ht.le (hCY0 P))

end MMP.Fourfold.PltReference

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori PltReference

open Classical in
/-- **An ample plt reference for a floor component of a log minimal model.** Let `X` be a smooth
projective variety over an algebraically closed field of characteristic zero and `(X, B + C)`
an snc dlt pair, `B, C ≥ 0`, no component of `C` in `⌊B⌋`, and `A ≤ B` an effective ample
`ℚ`-divisor with no component in `⌊B⌋`. Let `0 < t < 1` and `φ : X ⤏ Y` a nef log birational
model of `(X, B + t C)` with boundary `B_Y + t φ_* C`, where `B_Y` is `φ_* B` plus the new primes
with coefficient one, all of log discrepancy zero over `(X, B)`. For every component `E` of
`⌊B_Y⌋` there are a smooth projective `W` with a birational morphism `p : W ⟶ X` (an isomorphism
if `E` is not new) and `ψ = φ ∘ p : W ⤏ Y`, an effective plt boundary `B'` on `W` with unique
reduced component `E_W`, `ψ_* E_W = E`, an effective ample `ℚ`-divisor `A' ≤ B'` not containing
`E_W`, and a plt boundary `B'_Y ∼_ℚ B_Y` with unique reduced component `E`, `ψ_* A' ≤ B'_Y`, and
`(Y, B'_Y + t φ_* C)` plt; every prime extracted by `ψ` has order zero on `A'`. Moreover `E_W` is
normal, and every representative of `ψ⁻¹` defined at the generic point of an extracted prime sends
it off `Supp A'`. -/
@[mmp "lem_fourfold_extracted_zero_place_plt_reference"]
public theorem exists_pltReference_of_isNefLogBirationalModel
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X} {KY : Divisor Y}
    {B C : RDivisor X} {A : QDivisor X} {t : ℝ}
    (hdlt : IsRealDltPair sX (B + C)) (hsnc : (B + C).IsSNC sX)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hCB : ∀ P, C.coeff P ≠ 0 → B.coeff P < 1)
    (hA : A.HasRelativelyAmpleMultiple sX) (hA₀ : 0 ≤ A) (hAB : A.toRDivisor ≤ B)
    (hAfl : ∀ P, A.coeff P ≠ 0 → B.coeff P < 1)
    (ht : 0 < t) (ht₁ : t < 1)
    {φ : X.RationalMap Y} {BY : RDivisor Y}
    (hBY : ∀ F : MMP.Mori.PrimeDivisor Y,
      BY.coeff F = (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hY : IsNefLogBirationalModel sX sY sZ π πY KX (B + t • C) KY
      (BY + t • MMP.Mori.RationalMap.transformDivisor φ C) φ)
    (hzero : ∀ F : MMP.Mori.PrimeDivisor Y, MMP.Flips.RationalMap.IsInverseExceptional φ F →
      ∀ (D : MMP.Flips.ProperDivisorOver k sX), MMP.Flips.IsRealizedOver sX φ F D →
        ∀ (n : ℕ) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n B D.toDivisorOver a → a = 0)
    (E : MMP.Mori.PrimeDivisor Y) (hE : BY.coeff E = 1) :
    ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : CompactSpace W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of k)) (_ : LocallyOfFiniteType sW) (p : W ⟶ X)
      (hp : IsBirationalMorphism p) (ψ : W.RationalMap Y) (EW : MMP.Mori.PrimeDivisor W)
      (B' : RDivisor W) (A' : QDivisor W) (BY' : RDivisor Y),
      -- the reference `W` and the maps
      MMP.Mori.IsProjectiveVariety k sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sX = sW ∧
      (haveI := hp.isDominant;
        Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
          ψ.fromFunctionField) ∧
      (¬ MMP.Flips.RationalMap.IsInverseExceptional φ E → IsIso p) ∧
      MMP.Mori.RationalMap.transformPrimeDivisor ψ EW = some E ∧
      -- the plt boundary `B'` on `W` with unique reduced component `E_W`
      (IsRealLcPair sW B' ∧ ∀ (n : ℕ) (D : MMP.Mori.DivisorOver k sW), D.IsExceptional →
        ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sW n B' D a → 0 < a) ∧
      B'.coeff EW = 1 ∧ (∀ P, P ≠ EW → B'.coeff P < 1) ∧
      -- the rational ample component `A'`
      A'.HasRelativelyAmpleMultiple sW ∧ 0 ≤ A' ∧ A'.toRDivisor ≤ B' ∧ A'.coeff EW = 0 ∧
      -- the plt boundary `B'_Y` on `Y`
      (∃ (m : ℕ) (f : (RationalFunctions Y)ˣ), 0 < m ∧
        (m : ℝ) • (BY' - BY) = Divisor.toRDivisor (principalDivisor f)) ∧
      (IsRealLcPair sY BY' ∧ ∀ (n : ℕ) (D : MMP.Mori.DivisorOver k sY), D.IsExceptional →
        ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sY n BY' D a → 0 < a) ∧
      BY'.coeff E = 1 ∧ (∀ F, F ≠ E → BY'.coeff F < 1) ∧
      MMP.Mori.RationalMap.transformDivisor ψ A'.toRDivisor ≤ BY' ∧
      (IsRealLcPair sY (BY' + t • MMP.Mori.RationalMap.transformDivisor φ C) ∧
        ∀ (n : ℕ) (D : MMP.Mori.DivisorOver k sY), D.IsExceptional → ∀ a : ℝ,
          MMP.Intersection.IsLogDiscrepancy sY n
            (BY' + t • MMP.Mori.RationalMap.transformDivisor φ C) D a → 0 < a) ∧
      -- the primes extracted by `ψ` have order zero on `A'`
      (∀ G : MMP.Mori.PrimeDivisor Y, MMP.Flips.RationalMap.IsInverseExceptional ψ G →
        ∀ D : MMP.Flips.ProperDivisorOver k sW, MMP.Flips.IsRealizedOver sW ψ G D →
          ¬ (D.center : Set W) ⊆ A'.supp) ∧
      IsNormal EW.idealSheaf.subscheme ∧
      ∀ G : MMP.Mori.PrimeDivisor Y, MMP.Flips.RationalMap.IsInverseExceptional ψ G →
        ∀ q : Y.PartialMap W, (∃ e : W.PartialIso Y, e.toRationalMap = ψ ∧
          e.symm.toRationalMap = q.toRationalMap) →
          ∀ hG : G.genericPoint ∈ q.domain, q.hom ⟨G.genericPoint, hG⟩ ∉ (A'.supp : Set W) := by
  have hXn : IsNormalVariety k sX := ⟨hXp.toIsVariety, inferInstance⟩
  have hYn : IsNormalVariety k sY := hY.isNormalVariety_model
  have hYp := hY.isProjectiveVariety_model
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hYp.isProjective
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  obtain ⟨n, hKX⟩ := hY.isCanonicalDivisor
  obtain ⟨V, _, _, _, sV, p₀, q₀, h₀, GX₀, GY₀, hR₀⟩ := hY.exists_resolution
  have hpb₀ := hR₀.isBirationalMorphism_left
  have hqb₀ := hR₀.isBirationalMorphism_right
  haveI : IsDominant p₀ := hpb₀.isDominant
  haveI : IsDominant q₀ := hqb₀.isDominant
  obtain ⟨θ, hθbij, hθ⟩ := exists_ringHom_specMap_eq φ p₀ q₀ h₀ hpb₀.functionFieldMap_bijective
    hqb₀.functionFieldMap_bijective hR₀.isInverse hR₀.compHom_eq
  have hφk := fromFunctionField_comp_eq_of_isNefLogBirationalModel hY
  have hφtr : ∀ (P : MMP.Mori.PrimeDivisor X) (G : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor φ P = some G ↔
        P.divisorialValuation.comap θ = G.divisorialValuation := fun P G =>
    transformPrimeDivisor_eq_some_iff_of_comp_eq φ θ hθbij.2 hθ hφk P G
  have hB1 : ∀ P, B.coeff P ≤ 1 := fun P => by
    have := hdlt.2.1 P
    rw [DivisorWithCoeffs.coeff_add] at this
    linarith [hC P]
  have hBsupp : B.support ⊆ (B + C).support := fun P hP => by
    rw [Finsupp.mem_support_iff] at hP ⊢
    intro h
    apply hP
    have h' : (B + C).coeff P = 0 := h
    rw [DivisorWithCoeffs.coeff_add] at h'
    have : B.coeff P = 0 := by linarith [hB P, hC P]
    exact this
  have hBsnc : B.IsSNC sX := hsnc.of_support_subset hBsupp
  by_cases hnew : MMP.Flips.RationalMap.IsInverseExceptional φ E
  · -- a new prime divisor: realize it on the resolution and extract it
    have hWnp := isNormalVariety_comp_left hR₀
    have hWnq := isNormalVariety_comp_right hR₀
    haveI := isProper_of_isProjectiveMorphism p₀ hR₀.isProjectiveMorphism_left
    haveI := isProper_of_isProjectiveMorphism q₀ hR₀.isProjectiveMorphism_right
    obtain ⟨EV, hEV, hisoEV, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYn hWnq hqb₀ E
    set D : MMP.Flips.ProperDivisorOver k sX := ⟨⟨V, p₀, hWnp, hpb₀, EV⟩, inferInstance⟩ with hDdef
    have hDv : D.valuation.comap θ = E.divisorialValuation := by
      have h1 := functionFieldMap_comp_eq φ θ hθ p₀ q₀ h₀ hR₀.isInverse hR₀.compHom_eq
      rw [← divisorialValuation_comap_functionFieldMap_eq q₀ EV E hEV, ← h1]
      rfl
    have hDexc : D.IsExceptional := by
      refine (BoundaryCopy.properDivisorOver_isExceptional_iff hKX.topologicalKrullDim_eq D).mpr ?_
      rw [← MMP.Positivity.DivisorOver.codimension_center]
      refine (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hXn
        D.toDivisorOver).mpr fun Q hQ => hnew Q ((hφtr Q E).mpr ?_)
      rw [← valuation_ofPrimeDivisor hXn Q, ← hQ]
      exact hDv
    have hreal : MMP.Flips.IsRealizedOver sX φ E D :=
      isRealizedOver_of_isLogComparisonResolution hR₀ hWnp E EV hEV
    obtain ⟨ωX, hωX0, hωXc⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hKX
    have hωX : divisorOfForm ωX = KX :=
      Finsupp.ext fun Γ => show (divisorOfForm ωX).coeff Γ = KX.coeff Γ from
        (coeff_divisorOfForm ωX Γ).trans (hωXc Γ)
    obtain ⟨mB, rB, LB, hLBc, hLBsum⟩ :=
      isRCartier_of_isSmoothScheme hXs (Divisor.toRDivisor KX + B)
    have hsum' : Divisor.toRDivisor (divisorOfForm ωX) + B =
        ∑ j, rB j • Divisor.toRDivisor (LB j) := by
      ext Γ
      rw [hωX]
      exact (hLBsum Γ).trans (MMP.Flips.coeff_sum_smul_toRDivisor rB LB Γ).symm
    obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hXn hKX.topologicalKrullDim_eq hωX0 hLBc hsum' D
    have hlog := isLogDiscrepancy_of_isDiscrepancyWith (by rwa [hωX]) hb
    have h0 := hzero E hnew D hreal n _ hlog
    rw [h0] at hlog
    obtain ⟨W, _, _, _, _, p, EW, F, hRM, hEWv⟩ :=
      exists_isReferenceModel_of_isLogDiscrepancy_eq_zero hXp hXs hsnc hB hC hB1 hBsnc hA hA₀ hAB
        hAfl hKX D hDexc hlog
    exact exists_pltReference_of_isReferenceModel hXp hXs hdlt hB hC hCB hA hA₀ hAB hAfl ht
      ht₁ hBY hY E hE θ hθbij hθ hKX p EW F hRM (by rwa [hEWv])
      (fun h => absurd hnew h)
  · -- the transform of a component of `⌊B⌋`: `W = X`
    obtain ⟨S, hSE⟩ : ∃ S, RationalMap.transformPrimeDivisor φ S = some E := by
      by_contra h
      push Not at h
      exact hnew h
    have hBS : B.coeff S = 1 := by
      have h1 := hBY E
      rw [if_neg hnew, add_zero, hE] at h1
      change 1 = DivisorWithCoeffs.mapPrimeDivisors (RationalMap.transformPrimeDivisor φ) B E at h1
      rw [mapPrimeDivisors_apply_eq_sum, Finset.sum_eq_single S] at h1
      · rw [if_pos hSE] at h1
        exact h1.symm
      · intro P _ hPS
        rw [if_neg]
        intro hP
        exact hPS (primeDivisor_eq_of_divisorialValuation_eq hXn (valuation_eq_of_comap_eq
          hθbij.2 (((hφtr P E).1 hP).trans ((hφtr S E).1 hSE).symm)))
      · intro hS
        rw [if_pos hSE]
        exact Finsupp.notMem_support_iff.mp hS
    obtain ⟨F, hRM⟩ := exists_isReferenceModel_id hXp hXs hsnc hA n S hBS (C := C)
    have hEW : (S.divisorialValuation.comap (functionFieldMap (𝟙 X))).comap θ =
        E.divisorialValuation := by
      rw [show S.divisorialValuation.comap (functionFieldMap (𝟙 X)) = S.divisorialValuation from
        Valuation.ext fun g => by rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_id_apply]]
      exact (hφtr S E).1 hSE
    exact exists_pltReference_of_isReferenceModel hXp hXs hdlt hB hC hCB hA hA₀ hAB hAfl ht
      ht₁ hBY hY E hE θ hθbij hθ hKX (𝟙 X) S F hRM hEW (fun _ => inferInstance)

end MMP.Fourfold

end
