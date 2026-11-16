module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.FloorProgramInputs
public import MMP.AlgebraicGeometry.MMP.MinimalModel.SpecifiedExtraction
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties

/-!
# Extraction of specified low-discrepancy valuations over a projective klt fourfold

Let `(X, Δ)` be a klt pair, with `Δ` an effective `ℚ`-divisor, on a normal projective complex
fourfold, and let `I` be a finite set of normalized divisorial valuations of `k(X)`, exceptional
over `X`, with log discrepancy `a(s; X, Δ) ≤ 1`. Then there is a projective birational morphism
`p : V ⟶ X` from a `ℚ`-factorial normal projective fourfold whose exceptional prime divisors are
exactly the centres of the valuations in `I`, and the crepant boundary `Δ_V` of `(X, Δ)` on `V`,
`K_V + Δ_V = p^*(K_X + Δ)`, is effective and klt. For `I = ∅` the morphism `p` is small: it is a
small `ℚ`-factorialization of `X`.

## Main results

* `MMP.Fourfold.exists_fourfoldCrepantJunction_of_isKltPair`: the extraction, as a crepant
  junction `MMP.Fourfold.FourfoldCrepantJunction` whose boundary is effective, klt and the crepant
  boundary of `(X, Δ)`.

## Implementation notes

The extraction is packaged as a `MMP.Fourfold.FourfoldCrepantJunction`, which records the
projective birational morphism `p`, the `ℚ`-factoriality and projectivity of `V`, the bijection
`s ↦ E_s = c_V(s)` from `I` onto the `p`-exceptional prime divisors and the coefficient
`1 - a(s; X, Δ)` of `Δ_V` at `E_s`. Crepancy is stated with `MMP.Mori.IsCrepantBoundary`, for
every canonical divisor of `X`. The effectivity of `Δ`, part of the convention that the boundary
of a pair is effective, is a separate hypothesis because `MMP.Fourfold.IsKltPair` does not
contain it.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
-/

@[expose] public section

section

namespace Proof_thm_fourfold_projective_specified_extraction_4

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A prime divisor `P` of `X` whose generic point is sent by `f : X ⟶ Y` to the generic point of
a prime divisor of `Y` is not `f`-exceptional. -/
private theorem not_isExceptional_of_map_genericPoint {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {f : X ⟶ Y} {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Y} (h : f P.genericPoint = Q.genericPoint) :
    ¬ RationalMap.IsExceptional (X := X) f.toRationalMap P := by
  intro hex
  have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    ((MMP.Positivity.isExceptional_toRationalMap_iff (f := f) P).mp hex) _ <|
      subset_closure ⟨P.genericPoint, by
        change P.genericPoint ∈ P.support
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl, h⟩
  rw [Q.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The inverse transform `p⁻¹_* Δ` has coefficient `0` along a `p`-exceptional prime divisor. -/
private theorem inverseTransformDivisor_apply_eq_zero_of_isExceptional {V X : Scheme.{0}}
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian X] [IsNormal X]
    [IsSeparated (X ↘ Limits.terminal Scheme)] {p : V ⟶ X} (Δ : QDivisor X)
    {F : MMP.Mori.PrimeDivisor V} (hF : RationalMap.IsExceptional (X := V) p.toRationalMap F) :
    inverseTransformDivisor p Δ F = 0 :=
  MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun _ hQ =>
    not_isExceptional_of_map_genericPoint
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1
      hF) Δ

/-- **Crepant boundaries agree with the inverse transform off the exceptional locus.** If
`K_V + Δ_V = p^*(K_X + Δ)` for a proper birational `p : V ⟶ X`, then along every prime divisor `F`
of `V` that is not exceptional over `X`, with image the prime divisor `Q` of `X`, the coefficient
of `Δ_V` is that of `Δ`, which is also the coefficient of `p⁻¹_* Δ`. -/
private theorem exists_coeff_eq_of_not_isExceptional {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X ↘ Limits.terminal Scheme)]
    {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X} (hpair : MMP.Mori.IsPair sX Δ) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {V : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] {p : V ⟶ X} [IsProper p]
    (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p) {ΔV : QDivisor V}
    (hcrep : IsCrepantBoundary sX n K Δ p hV hp ΔV) {F : MMP.Mori.PrimeDivisor V}
    (hF : ¬ (⟨V, p, hV, hp, F⟩ : DivisorOver ℂ sX).IsExceptional) :
    ∃ Q : MMP.Mori.PrimeDivisor X, ΔV F = Δ Q ∧ inverseTransformDivisor p Δ F = Δ Q := by
  obtain ⟨Q, hQ⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hpair.1 _ hF
  have hcen : p F.genericPoint = Q.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hpair.1.1 hQ
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK (DivisorOver.ofPrimeDivisor ℂ hpair.1 Q)
  have h1 := ha.eq_neg_coeff_of_ofPrimeDivisor hpair.1
  have h2 := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hQ hcen
    (hcrep F) ha
  refine ⟨Q, show ΔV.coeff F = Δ.coeff Q by linarith, ?_⟩
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hcen
      (hcen ▸ MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal p hp
        Q.coheight_genericPoint.le))
    (fun _ hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ').1.symm.trans hcen)) Δ

private theorem solution
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {Δ : QDivisor X} (hΔ : 0 ≤ Δ) (hklt : IsKltPair sX Δ)
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) ⊆ lowDiscrepancySet sX Δ) :
    ∃ J : FourfoldCrepantJunction sX Δ I,
      0 ≤ J.Θ ∧ IsKltPair J.sY J.Θ ∧
        ∀ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n →
          IsCrepantBoundary sX n K Δ J.p J.isQFactorial.1 J.isBirationalMorphism J.Θ := by
  obtain ⟨V, _, _, _, p, hp, hV, E, ΔV, hpp, hval, hinj, hexc, hkltV, hcrep, hlog⟩ :=
    projectiveFloorProgramInputs_four.exists_crepant_extraction sX hX (by rw [hdim]; rfl) hklt I
      (fun s hs => by
        obtain ⟨hex, a, ha, ha1⟩ := hI hs
        refine ⟨hex, a, ha, ?_, ha1⟩
        obtain ⟨n, D, -, -, hD⟩ := ha
        exact hklt.2 n D a hD)
  have hn : ∀ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n → n = 4 := fun n K hK => by
    exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hdim
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hV.1.1
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hpp
  haveI : IsSeparated (X ↘ Limits.terminal Scheme) := by
    haveI : IsSeparated sX := hX.toIsSeparated
    rw [Subsingleton.elim (X ↘ Limits.terminal Scheme)
      (sX ≫ Limits.terminal.from (Spec (.of ℂ)))]
    infer_instance
  obtain ⟨-, n₀, K₀, hK₀, -⟩ := id hklt.1.isPair
  obtain rfl := hn n₀ K₀ hK₀
  have hcoeff_ne : ∀ F, F ∉ Set.range E →
      ∃ Q : MMP.Mori.PrimeDivisor X, ΔV F = Δ Q ∧ inverseTransformDivisor p Δ F = Δ Q :=
    fun F hF => exists_coeff_eq_of_not_isExceptional hklt.1.isPair hK₀ hV.1 hp (hcrep K₀ hK₀)
      fun h => hF ((hexc F).mp h)
  /- `0 ≤ ΔV (E s)`, since `1 - ΔV (E s)` is the log discrepancy `a(s) ≤ 1` -/
  have hle : ∀ s : I, 0 ≤ ΔV (E s) := fun s => by
    obtain ⟨-, a, ⟨n', D', -, hD', h'⟩, ha1⟩ := hI s.2
    obtain ⟨n, D, -, hD, h⟩ := hlog s
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hD.trans hD'.symm)
    exact_mod_cast (show (0 : ℝ) ≤ (ΔV.coeff (E s) : ℝ) by linarith)
  have hΘ : ΔV = inverseTransformDivisor p Δ + ∑ s : I, Finsupp.single (E s) (ΔV (E s)) := by
    classical
    refine Finsupp.ext fun F => ?_
    rw [Finsupp.add_apply, Finsupp.finset_sum_apply]
    by_cases hF : F ∈ Set.range E
    · obtain ⟨s, rfl⟩ := hF
      rw [inverseTransformDivisor_apply_eq_zero_of_isExceptional Δ ((hexc (E s)).mpr ⟨s, rfl⟩),
        zero_add, Finset.sum_eq_single s (fun t _ hts => Finsupp.single_eq_of_ne
        fun h => hts (hinj h).symm) (by simp), Finsupp.single_eq_same]
    · obtain ⟨Q, h1, h2⟩ := hcoeff_ne F hF
      rw [h2, h1, Finset.sum_eq_zero fun t _ => Finsupp.single_eq_of_ne fun ht => hF ⟨t, ht.symm⟩,
        add_zero]
  let J : FourfoldCrepantJunction sX Δ I :=
    { Y := V
      p := p
      E := E
      Θ := ΔV
      isProjectiveVariety_base := hX
      dim_base := hdim
      isKltPair := hklt
      subset_lowDiscrepancySet := hI
      isProjectiveVariety :=
        (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hV.1.1, hpp.comp hX.isProjective⟩
      isQFactorial := hV
      dim_eq :=
        (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp).symm.trans
          hdim
      isProjectiveMorphism := hpp
      isBirationalMorphism := hp
      valuation_eq := hval
      injective := hinj
      isExceptional_iff := hexc
      Θ_eq := ⟨fun s => 1 - ΔV (E s), fun s => by push_cast; exact hlog s, by
        simpa only [sub_sub_cancel] using hΘ⟩ }
  refine ⟨J, fun F => ?_, hkltV, fun n K hK => ?_⟩
  · by_cases hF : F ∈ Set.range E
    · obtain ⟨s, rfl⟩ := hF
      exact hle s
    · obtain ⟨Q, h1, -⟩ := hcoeff_ne F hF
      exact h1 ▸ hΔ Q
  · obtain rfl := hn n K hK
    exact hcrep K hK

end Proof_thm_fourfold_projective_specified_extraction_4

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Extraction of specified low-discrepancy valuations over a projective klt fourfold.** Let
`(X, Δ)` be a klt pair with `Δ` effective on a normal projective complex fourfold, and `I` a
finite set of normalized divisorial valuations exceptional over `X` with `a(s; X, Δ) ≤ 1`. Then
there is a crepant junction `(p : V ⟶ X, Δ_V)` of `(X, Δ)` extracting `I`: `p` is projective
birational, `V` is `ℚ`-factorial and its `p`-exceptional prime divisors are exactly the centres
of the valuations in `I`; moreover `Δ_V` is effective, `(V, Δ_V)` is klt, and
`K_V + Δ_V = p^*(K_X + Δ)`. -/
@[mmp "thm_fourfold_projective_specified_extraction_4"]
public theorem exists_fourfoldCrepantJunction_of_isKltPair
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {Δ : QDivisor X} (hΔ : 0 ≤ Δ) (hklt : IsKltPair sX Δ)
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) ⊆ lowDiscrepancySet sX Δ) :
    ∃ J : FourfoldCrepantJunction sX Δ I,
      0 ≤ J.Θ ∧ IsKltPair J.sY J.Θ ∧
        ∀ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n →
          IsCrepantBoundary sX n K Δ J.p J.isQFactorial.1 J.isBirationalMorphism J.Θ :=
            by revert X sX hX hdim Δ hΔ hklt I hI; first | exact Proof_thm_fourfold_projective_specified_extraction_4.solution | exact Proof_thm_fourfold_projective_specified_extraction_4.solution _ | exact Proof_thm_fourfold_projective_specified_extraction_4.solution _ _ | exact Proof_thm_fourfold_projective_specified_extraction_4.solution _ _ _ | exact Proof_thm_fourfold_projective_specified_extraction_4.solution _ _ _ _

end MMP.Fourfold

