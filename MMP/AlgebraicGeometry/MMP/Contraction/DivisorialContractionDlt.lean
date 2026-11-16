module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import MMP.AlgebraicGeometry.MMP.Contraction.DltContractionQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Divisorial contractions preserve dlt pairs

Let `(X, Δ)` be a dlt pair, with `X` a `ℚ`-factorial projective variety over an algebraically
closed field of characteristic zero, `R` a `(K_X + Δ)`-negative extremal ray of `NE̅(X)` and
`g : X → X'` a divisorial contraction of `R`. Then `(X', g_*Δ)` is a dlt pair. This is the
divisorial half of the statement that the dlt condition is preserved by the steps of the
minimal model program.

## Main results

* `MMP.Mori.IsDivisorialContraction.isDltPair_transformDivisor`: divisorial contractions of
  `(K_X + Δ)`-negative extremal rays preserve dlt pairs.
* `MMP.Mori.IsDltPair.isDltPair_transformDivisor_of_hasRelativelyAmpleMultiple`: the transform
  of a dlt pair along a proper birational morphism with `-(K + Δ)` relatively ample is dlt.
* `MMP.Mori.IsPairWith.isPairWith_transformDivisor`: the transform of a pair onto a
  `ℚ`-factorial variety is a pair.

## Implementation notes

The canonical divisor of `X'` is the transform `g_* K_X` of the canonical divisor `K_X` of `X`
(`MMP.Mori.RationalMap.transformDivisor` along `g` regarded as a rational map), and the
boundary is `g_* Δ`; both are cut out by the same rational top form, so discrepancies on `X`
and on `X'` are computed with compatible canonical divisors. That `K_{X'} + g_*Δ` is
`ℚ`-Cartier is part of the conclusion (`MMP.Mori.IsDltPair` contains the pair condition).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Corollary 3.44.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

universe u

/-- The closure of the image of a prime divisor `E ⊆ W` under `g` is the closure of the image of
its generic point. -/
private theorem closure_image_support_eq {W T : Scheme.{u}} (g : W ⟶ T)
    (E : MMP.Mori.PrimeDivisor W) :
    closure (g '' (E.idealSheaf.support : Set W)) = closure {g E.genericPoint} := by
  change closure (g '' E.support) = closure {g E.genericPoint}
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine le_antisymm ?_ (closure_mono ?_)
  · exact closure_minimal (image_closure_subset_closure_image g.continuous |>.trans
      (by rw [Set.image_singleton])) isClosed_closure
  · exact Set.singleton_subset_iff.mpr ⟨E.genericPoint, subset_closure rfl, rfl⟩

/-- Two prime divisors `E ⊆ W`, `E' ⊆ W'` whose generic points have the same image in a
separated normal scheme `T` are exceptional for `g : W ⟶ T`, resp. `g' : W' ⟶ T`, together. -/
private theorem isExceptional_iff_of_apply_eq {W W' T : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian W'] [IsNormal W']
    [IsLocallyNoetherian T] [IsNormal T] [IsSeparated (T ↘ ⊤_ Scheme)] (g : W ⟶ T)
    (g' : W' ⟶ T) (E : MMP.Mori.PrimeDivisor W) (E' : MMP.Mori.PrimeDivisor W')
    (h : g E.genericPoint = g' E'.genericPoint) :
    RationalMap.IsExceptional (X := W) g.toRationalMap E ↔
      RationalMap.IsExceptional (X := W') g'.toRationalMap E' := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Positivity.isExceptional_toRationalMap_iff]
  have : Closeds.closure (g '' (E.idealSheaf.support : Set W)) =
      Closeds.closure (g' '' (E'.idealSheaf.support : Set W')) := by
    ext1
    simp only [Closeds.coe_closure]
    rw [closure_image_support_eq, closure_image_support_eq, h]
  rw [this]

/-- For an lc pair whose boundary has coefficients at most `1`, every discrepancy is at least
`-1`. -/
theorem IsLcPair.neg_one_le_of_isDiscrepancy {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hlc : IsLcPair sX n K Δ) (hΔ : ∀ P, DivisorWithCoeffs.coeff Δ P ≤ 1)
    {D : DivisorOver k sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  by_cases hDE : D.IsExceptional
  · have h2 : ((-1 : ℝ) : EReal) ≤ ((a : ℝ) : EReal) := by
      simpa using hlc.2.trans (discrep_le hDE ha)
    exact_mod_cast EReal.coe_le_coe_iff.mp h2
  · obtain ⟨P, hP⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hlc.1.1 D hDE
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1.isPair hlc.1.2.1
      (DivisorOver.ofPrimeDivisor k hlc.1.1 P)
    rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hlc.1 hP ha hb,
      hb.eq_neg_coeff_of_ofPrimeDivisor hlc.1.1]
    linarith [hΔ P]

/-- The centre of a divisor over `X` whose generic point lies outside an open `U` misses `U`. -/
theorem DivisorOver.center_subset_compl {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) {U : X.Opens}
    (hD : D.f D.E.genericPoint ∉ U) : (D.center : Set X) ⊆ (U : Set X)ᶜ := by
  rw [D.center_eq_closure_genericPoint]
  exact closure_minimal (Set.singleton_subset_iff.mpr hD) U.isOpen.isClosed_compl

/-- For a proper birational morphism `g : X ⟶ X'` of normal varieties, the coefficient of `g_* Δ`
at a prime divisor `P'` of `X'` is the coefficient of `Δ` at any prime divisor `P` of `X` with
`g(η_P) = η_{P'}`. -/
theorem transformDivisor_apply_eq_of_apply_genericPoint_eq {k : Type} [Field k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] {sX' : X' ⟶ Spec (.of k)} (hX'v : IsNormalVariety k sX') {g : X ⟶ X'}
    (hXv' : IsNormalVariety k (g ≫ sX')) [IsProper g] (hgb : IsBirationalMorphism g)
    (Δ : QDivisor X) {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP : g P.genericPoint = P'.genericPoint) :
    RationalMap.transformDivisor g.toRationalMap Δ P' = Δ P := by
  obtain ⟨P₀, h0, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX'v hXv' hgb P'
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hP' := MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus g hgb P'
  rw [htr]
  congr 1
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (Stacks.Models.eq_of_isIso_morphismRestrict g _ (h0 ▸ hP') (h0.trans hPP.symm))

/-- Let `(X, Δ)` be an lc pair with boundary coefficients at most `1` and `g : X ⟶ X'` a proper
birational morphism with `-(K + Δ)` `g`-ample, and let `U ⊆ X` be an open such that every divisor
over `X` with centre in `X \ U` has discrepancy `> -1`. Then a divisor `D'` exceptional over `X'`,
such that no point `z ∈ U` maps into the biregular locus of `g` onto the generic point of the
centre of `D'`, has discrepancy `> -1` with respect to `(X', g_* Δ)`. -/
theorem IsLcPair.neg_one_lt_of_isExceptional_of_hasRelativelyAmpleMultiple {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X']
    [IsNormal X'] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [QuasiCompact sX]
    [QuasiCompact sX'] [IsSeparated sX'] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {g : X ⟶ X'}
    [IsProper g] [IsSeparated (X' ↘ ⊤_ Scheme)]
    (hlc : IsLcPair sX n K Δ) (hΔ : ∀ P, DivisorWithCoeffs.coeff Δ P ≤ 1)
    (hX'v : IsNormalVariety k sX') (hXv' : IsNormalVariety k (g ≫ sX')) (hgs : g ≫ sX' = sX)
    (hgb : IsBirationalMorphism g)
    (hpair' : IsPairWith sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ))
    (hA : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple g) (U : X.Opens)
    (hZ : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a)
    {D' : DivisorOver k sX'} {a' : ℚ} (hE' : D'.IsExceptional)
    (ha' : IsDiscrepancy sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ) D' a')
    (hU : ∀ z : X, g z ∈ biregularLocus g → g z = D'.f D'.E.genericPoint → z ∉ U) :
    -1 < a' := by
  have : IsDominant g := hgb.isDominant
  have hN := isRelativelyNef_of_hasRelativelyAmpleMultiple (sX := sX) hA
  obtain ⟨D₀, hv₀⟩ := MMP.Mori.exists_divisorOver_valuation_comap_eq (sY := sX') hXv' hgb
    (isBirationalMorphism_of_isIso (𝟙 X'))
    ⟨D'.Y, D'.f, by rw [Category.id_comp]; exact D'.isNormalVariety, D'.isBirationalMorphism,
      D'.E⟩
  let D : DivisorOver k sX :=
    ⟨D₀.Y, D₀.f, by rw [← hgs]; exact D₀.isNormalVariety, D₀.isBirationalMorphism, D₀.E⟩
  have hv : D.valuation.comap (functionFieldMap g) = D'.valuation := by
    refine hv₀.trans ?_
    ext t
    rw [Valuation.comap_apply, functionFieldMap_id_apply]
    rfl
  have hxx' : g (D.f D.E.genericPoint) = D'.f D'.E.genericPoint :=
    map_genericPoint_eq_of_valuation_comap_eq sX' g (𝟙 X') D D' (by
      rw [hv]; ext t; rw [Valuation.comap_apply, functionFieldMap_id_apply])
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have hEY : RationalMap.IsExceptional (X := D.Y) (D.f ≫ g).toRationalMap D.E :=
    (isExceptional_iff_of_apply_eq (D.f ≫ g) D'.f D.E D'.E hxx').mpr hE'
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1.isPair hlc.1.2.1 D
  by_cases hgV : g (D.f D.E.genericPoint) ∈ biregularLocus g
  · exact (hZ D a (D.center_subset_compl (hU _ hgV hxx')) ha).trans_le
      (isDiscrepancy_le_transformDivisor_of_isRelativelyNef hlc.1.isPair hX'v hgs hgb hlc.1.2.1
        hpair'.2.1 hN hpair'.2.2 D D' hv hEY ha ha')
  · have hc : (D'.center : Set X') ⊆ g '' (exceptionalSet g : Set X) := by
      rw [D'.center_eq_closure_genericPoint]
      refine closure_minimal (Set.singleton_subset_iff.mpr
        ⟨_, mem_exceptionalSet.mpr hgV, hxx'⟩) ?_
      exact g.isClosedMap _ (isClosed_exceptionalSet g)
    exact (hlc.neg_one_le_of_isDiscrepancy hΔ ha).trans_lt
      (isDiscrepancy_lt_transformDivisor_of_hasRelativelyAmpleMultiple hlc.1.isPair hX'v hgs hgb
        hlc.1.2.1 hpair'.2.1 hN hpair'.2.2 hA D D' hv hc ha ha')

/-- Let `g : X ⟶ X'` be such that the coefficient of `g_* Δ` at `P'` equals the coefficient of `Δ`
at `P` whenever `g(η_P) = η_{P'}`, and let `j : S ⟶ X'` be an open immersion from an open
`S ⊆ U` that agrees with `g` on `S`. If `Δ|_U` is snc, then so is `(g_* Δ)|_{j(S)}`. -/
theorem isSNC_restrictOpen_opensRange_transformDivisor {k : Type} [Field k]
    {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {g : X ⟶ X'} (Δ : QDivisor X)
    (hΔ : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      g P.genericPoint = P'.genericPoint →
        RationalMap.transformDivisor g.toRationalMap Δ P' = Δ P)
    {U S : X.Opens} (hSU : S ≤ U) (j : S.toScheme ⟶ X') [IsOpenImmersion j]
    (hjs : j ≫ sX' = S.ι ≫ sX) (hjapp : ∀ s : S.toScheme, j s = g (S.ι s))
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX)) :
    ((RationalMap.transformDivisor g.toRationalMap Δ).restrictOpen j.opensRange).IsSNC
      (j.opensRange.ι ≫ sX') := by
  have hrange : Set.range j.opensRange.ι = Set.range j := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
  refine DivisorWithCoeffs.IsSNC.comapDomain_of_range_subset sX' j.opensRange.ι j hrange.le _ ?_
  have hcomap : Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j)
      (RationalMap.transformDivisor g.toRationalMap Δ)
        (OpenWeilRestriction.primeDivisorMap_injective j).injOn =
      Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap S.ι) Δ
        (OpenWeilRestriction.primeDivisorMap_injective S.ι).injOn := by
    refine Finsupp.ext fun E => ?_
    rw [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply]
    refine hΔ _ _ ?_
    have e1 : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap S.ι E) =
        S.ι E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
    have e2 : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap j E) =
        j E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
    rw [e1, e2, hjapp]
  rw [hcomap, hjs]
  have hSU' : Set.range S.ι ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact fun x hx => hSU hx
  exact DivisorWithCoeffs.IsSNC.comapDomain_of_range_subset sX S.ι U.ι hSU' Δ hsnc

/-- Let `(X, Δ)` be a pair, `g : X ⟶ X'` a proper birational morphism with `(X', g_* Δ)` a pair,
and `U ⊆ X` an open such that every divisor over `X` with centre in `X \ U` has discrepancy
`> -1`. Then a non-exceptional divisor `D'` over `X'`, such that no point `z ∈ U` maps into the
biregular locus of `g` onto the generic point of the centre of `D'`, has discrepancy `> -1` with
respect to `(X', g_* Δ)`. -/
theorem IsPairWith.neg_one_lt_of_not_isExceptional_of_isBirationalMorphism {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X']
    [IsNormal X'] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [QuasiCompact sX'] [IsSeparated sX'] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {g : X ⟶ X'}
    [IsProper g] (hpair : IsPairWith sX n K Δ)
    (hpair' : IsPairWith sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ))
    (hXv' : IsNormalVariety k (g ≫ sX')) (hgb : IsBirationalMorphism g) (U : X.Opens)
    (hZ : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a)
    {D' : DivisorOver k sX'} {a' : ℚ} (hE' : ¬ D'.IsExceptional)
    (ha' : IsDiscrepancy sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ) D' a')
    (hU : ∀ z : X, g z ∈ biregularLocus g → g z = D'.f D'.E.genericPoint → z ∉ U) :
    -1 < a' := by
  obtain ⟨P', hP'⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hpair'.1 D' hE'
  have hx'P' : D'.f D'.E.genericPoint = P'.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hpair'.1 hP'
  obtain ⟨b', hb'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair'.isPair hpair'.2.1
    (DivisorOver.ofPrimeDivisor k hpair'.1 P')
  obtain ⟨P, hP, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hpair'.1 hXv' hgb P'
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hpair.2.1
    (DivisorOver.ofPrimeDivisor k hpair.1 P)
  rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hpair' hP' ha' hb',
    hb'.eq_neg_coeff_of_ofPrimeDivisor hpair'.1,
    show (RationalMap.transformDivisor g.toRationalMap Δ).coeff P' = Δ.coeff P from
      transformDivisor_apply_eq_of_apply_genericPoint_eq hpair'.1 hXv' hgb Δ hP,
    ← hb.eq_neg_coeff_of_ofPrimeDivisor hpair.1]
  exact hZ _ b (DivisorOver.center_subset_compl _ (hU P.genericPoint
    (hP ▸ MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus g hgb P') (hP.trans hx'P'.symm))) hb

/-- For a proper birational morphism `g : X ⟶ X'` of normal varieties onto a `ℚ`-factorial
variety, the transform `(X', g_* Δ)` of a pair `(X, Δ)`, with canonical divisor `g_* K`, is a
pair. -/
theorem IsPairWith.isPairWith_transformDivisor {k : Type} [Field k] [PerfectField k]
    {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [QuasiCompact sX'] [LocallyOfFiniteType sX']
    [IsSeparated sX'] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {g : X ⟶ X'} [IsProper g]
    [LocallyOfFiniteType (g ≫ sX')] (hpair : IsPairWith sX n K Δ)
    (hX'v : IsNormalVariety k sX') (hXv' : IsNormalVariety k (g ≫ sX')) (hgs : g ≫ sX' = sX)
    (hgb : IsBirationalMorphism g) (hX'Q : MMP.Fourfold.IsQFactorial sX') :
    IsPairWith sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ) := by
  have : IsDominant g := hgb.isDominant
  have hK := hpair.2.1
  have hKg : K.IsCanonicalDivisor (g ≫ sX') n := by rwa [hgs]
  have hdimX' : topologicalKrullDim X' = n := by
    have : MMP.Mori.IsVariety k sX' := hX'v.1
    have : MMP.Mori.IsVariety k (g ≫ sX') := hXv'.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (g ≫ sX') hgb]
    exact hK.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX' hX'v hdimX'
  exact ⟨hX'v, MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hX'v hXv' hgb hK₀ hKg,
    MMP.Fourfold.isQCartier_of_isQFactorial sX' hX'Q _⟩

/-- Let `(X, Δ)` be a dlt pair and `g : X ⟶ X'` a proper birational morphism of normal varieties
with `-(K + Δ)` `g`-ample and `(X', g_* Δ)` a pair. Then `(X', g_* Δ)`, with canonical divisor
`g_* K`, is a dlt pair. -/
theorem IsDltPair.isDltPair_transformDivisor_of_hasRelativelyAmpleMultiple {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X']
    [IsNormal X'] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [QuasiCompact sX]
    [QuasiCompact sX'] [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] [IsSeparated sX']
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {g : X ⟶ X'} [IsProper g]
    [IsSeparated (X' ↘ ⊤_ Scheme)] (hdlt : IsDltPair sX n K Δ)
    (hX'v : IsNormalVariety k sX') (hXv' : IsNormalVariety k (g ≫ sX')) (hgs : g ≫ sX' = sX)
    (hgb : IsBirationalMorphism g)
    (hpair' : IsPairWith sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ))
    (hA : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple g) :
    IsDltPair sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ) := by
  have hlc := hdlt.isLcPair
  obtain ⟨hpair, hcoeff, U, hUsm, hsnc, hZ⟩ := hdlt
  set V := biregularLocus g
  have : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  have hΔP : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      g P.genericPoint = P'.genericPoint →
        RationalMap.transformDivisor g.toRationalMap Δ P' = Δ P := fun _ _ =>
    transformDivisor_apply_eq_of_apply_genericPoint_eq hX'v hXv' hgb Δ
  set S : X.Opens := U ⊓ g ⁻¹ᵁ V
  let j : S.toScheme ⟶ X' := X.homOfLE (inf_le_right : S ≤ g ⁻¹ᵁ V) ≫ (g ∣_ V) ≫ V.ι
  have hj : j ≫ 𝟙 X' = S.ι ≫ g := by
    simp only [j, Category.comp_id]
    rw [morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  have hjs : j ≫ sX' = S.ι ≫ sX := by
    rw [← hgs, ← Category.assoc, ← hj, Category.comp_id]
  have hjapp : ∀ s : S.toScheme, j s = g (S.ι s) := fun s =>
    congrArg (fun f => f.base s) hj
  refine ⟨hpair', fun P' => ?_, j.opensRange, ?_,
    isSNC_restrictOpen_opensRange_transformDivisor Δ hΔP inf_le_left j hjs hjapp hsnc, ?_⟩
  · obtain ⟨P, hP, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX'v hXv' hgb P'
    change 0 ≤ RationalMap.transformDivisor g.toRationalMap Δ P' ∧
      RationalMap.transformDivisor g.toRationalMap Δ P' ≤ 1
    rw [hΔP P P' hP]
    exact hcoeff P
  · rintro _ ⟨s, rfl⟩
    have hs : S.ι s ∈ smoothLocus sX := hUsm s.2.1
    rw [smoothLocus_eq_smoothLocus] at hs ⊢
    exact (mem_smoothLocus_iff_of_comp_eq S.ι j sX sX' hjs s).2 hs
  · intro D' a' hcen ha'
    have hx'mem : D'.f D'.E.genericPoint ∈ (D'.center : Set X') := by
      rw [D'.center_eq_closure_genericPoint]
      exact subset_closure rfl
    have hnotU : ∀ z : X, g z ∈ V → g z = D'.f D'.E.genericPoint → z ∉ U :=
      fun z hzV hzx hzU => hcen hx'mem ⟨⟨z, hzU, hzV⟩, (hjapp _).trans hzx⟩
    by_cases hE' : D'.IsExceptional
    · exact hlc.neg_one_lt_of_isExceptional_of_hasRelativelyAmpleMultiple (fun P => (hcoeff P).2)
        hX'v hXv' hgs hgb hpair' hA U hZ hE' ha' hnotU
    · exact hpair.neg_one_lt_of_not_isExceptional_of_isBirationalMorphism hpair' hXv' hgb U hZ hE'
        ha' hnotU

/-- **Divisorial contractions preserve dlt** (KM, Corollary 3.44, divisorial case). Let `X` be a
`ℚ`-factorial projective variety over an algebraically closed field `k` of characteristic zero,
`K` a canonical divisor of `X` of dimension `n` and `Δ` a `ℚ`-divisor with `(X, Δ)` dlt. Let `R`
be a `(K + Δ)`-negative extremal ray of `NE̅(X)` and `g : X ⟶ X'` a divisorial contraction of
`R`. Then `(X', g_*Δ)`, with canonical divisor `g_*K`, is a dlt pair. -/
@[mmp "thm_km3c_dlt_preserved_divisorial"]
theorem IsDivisorialContraction.isDltPair_transformDivisor {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {g : X ⟶ X'} (hQ : MMP.Fourfold.IsQFactorial sX)
    (hR : MMP.Fourfold.IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R)
    (hg : IsDivisorialContraction k sX sX' R g) (hdlt : IsDltPair sX n K Δ) :
    IsDltPair sX' n (RationalMap.transformDivisor g.toRationalMap K)
      (RationalMap.transformDivisor g.toRationalMap Δ) := by
  have hC := hg.isContractionOfFace
  have hXv : IsNormalVariety k sX := hg.isNormalVariety
  have hXp := hC.isProjectiveVariety_source
  have hX'p := hC.isProjectiveVariety_target
  have hgs : g ≫ sX' = sX := hC.comp_eq
  have hgb := hg.isBirationalMorphism
  have : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  have : AlgebraicGeometry.IsProjectiveVariety k sX' := hX'p
  have hX'v : IsNormalVariety k sX' := ⟨hX'p.toIsVariety, inferInstance⟩
  have hXv' : IsNormalVariety k (g ≫ sX') := by rwa [hgs]
  have : QuasiCompact sX := hXp.toIsVariety.toQuasiCompact
  have : QuasiCompact sX' := hX'p.toIsVariety.toQuasiCompact
  have : LocallyOfFiniteType sX := hXp.toIsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'p.toIsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX') := by rw [hgs]; infer_instance
  have : IsSeparated sX' := hX'p.toIsVariety.toIsSeparated
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have : IsProper (g ≫ sX') := by rw [hgs]; infer_instance
  have : IsProper g := IsProper.of_comp g sX'
  have : IsSeparated (X' ↘ ⊤_ Scheme) := by
    rw [show (X' ↘ ⊤_ Scheme) = sX' ≫ Limits.terminal.from (Spec (.of k)) from
      Subsingleton.elim _ _]
    infer_instance
  obtain ⟨hq, hRay, hneg⟩ := hR
  have hX'Q := isQFactorial_of_isDltPair_of_isDivisorialContraction_or_isFiberTypeContraction
    hQ hdlt ⟨hRay.1, hRay.1.2.2.1, hneg⟩ (Or.inl hg)
  have hpair' := hdlt.1.isPairWith_transformDivisor hX'v hXv' hgs hgb hX'Q
  refine hdlt.isDltPair_transformDivisor_of_hasRelativelyAmpleMultiple hX'v hXv' hgs hgb hpair' ?_
  exact hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sX' hXv hXp hX'p ⟨n, hdlt.1.2.1⟩ hq
    hRay (fun v hv hv0 => by
      simpa [MMP.Fourfold.QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using
        hneg v hv hv0) g hgs (fun C hCg => (hC.isContractedBy_iff C).mp hCg)

end MMP.Mori

end
