module

public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel

/-!
# The end of a dlt bridge is a crepant dlt lift

Let `(X, B) → Z ← (X⁺, B⁺)` be a permitted step (`MMP.Fourfold.IsPermittedStep`) of projective
lc fourfold pairs over `ℂ` whose contraction `f : X ⟶ Z` is small, with `D⁺ = K_{X⁺} + B⁺`. Let
`p : (U, Δ) ⟶ (X, B)` be a crepant dlt lift (`MMP.Fourfold.IsCrepantDltLift`) and
`(U^k, Δ^k)_{0 ≤ k ≤ m}` an elementary dlt program over `Z` from `(U, Δ)` with `h₀ = f ∘ p`
(`MMP.Fourfold.RelativeElementaryDltProgram`). If `p' : U^m ⟶ X⁺` is a projective birational
morphism over `Z` (`f⁺ ∘ p' = h_m`) with `K_{U^m} + Δ^m = p'^* D⁺`, then
`p' : (U^m, Δ^m) ⟶ (X⁺, B⁺)` is a crepant dlt lift.

The pair `(U^m, Δ^m)` is projective `ℚ`-factorial dlt, and crepant over `X⁺`; it remains to see
`Δ^m = p'⁻¹_* B⁺ + Exc(p')_red`. An elementary program extracts no divisor, so a `p'`-exceptional
prime divisor of `U^m` is the transform of a prime divisor of `U`, which, `f` and `f⁺` being
small, is `p`-exceptional and so has coefficient one in `Δ`, kept along the program.

## Main results

* `MMP.Fourfold.IsCrepantDltLift.of_relativeElementaryDltProgram`: the end `p'` of the program
  is a crepant dlt lift of `(X⁺, B⁺)`.

## Implementation notes

The models of the program are `U^k = modelSeq U P.Y k`, with structure morphisms
`modelStr (p ≫ s_X) P.sY k`, boundaries `divisorSeq Δ P.ΔY k`, and `m = P.n.toNat`. As in
`MMP.Fourfold.IsPermittedStep`, the canonical divisor of `X⁺` is `(f⁺)⁻¹_* f_* K` and
`B⁺ = (f⁺)⁻¹_* f_* B`. The identity `K_{U^m} + Δ^m = p'^* D⁺` is the statement that `Δ^m` is the
crepant boundary of `(X⁺, B⁺)` on `U^m` (`MMP.Mori.IsCrepantBoundary`), the convention of
`MMP.Fourfold.IsCrepantDltLift`; the morphism `p'` is a morphism over `ℂ` and over `Z`, the
latter spelled `p' ≫ f⁺ = modelMap (p ≫ f) P.hY m`, i.e. `f⁺ ∘ p' = h_m`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- An integral locally Noetherian scheme of positive dimension has a prime divisor: the local
ring at a point specializing from the generic point is not a field, and a minimal prime over a
nonzero element of its maximal ideal has height one by Krull's principal ideal theorem. -/
private theorem nonempty_primeDivisor_of_pos {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (h : 0 < topologicalKrullDim Y) :
    Nonempty (MMP.Mori.PrimeDivisor Y) := by
  obtain ⟨Z₁, Z₂, hlt⟩ := Order.krullDim_pos_iff.mp h
  obtain ⟨x, hx⟩ := Z₁.isIrreducible.nonempty
  have hne : genericPoint Y ≠ x := by
    rintro rfl
    apply hlt.not_ge
    intro z _
    have : genericPoint Y ⤳ z := genericPoint_specializes z
    exact Z₁.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
      (specializes_iff_mem_closure.mp this)
  obtain ⟨q, hq⟩ : genericPoint Y ∈ Set.range (Y.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
  have hm : IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ≠ ⊥ := by
    intro hm
    apply hne
    have h1 : q.asIdeal ≤ IsLocalRing.maximalIdeal _ := IsLocalRing.le_maximalIdeal q.2.ne_top
    rw [hm, le_bot_iff] at h1
    have hqc : q = IsLocalRing.closedPoint (Y.presheaf.stalk x) :=
      PrimeSpectrum.ext (h1.trans hm.symm)
    rw [← hq, hqc, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨r, hr, -⟩ := Ideal.exists_minimalPrimes_le
    (J := IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    ((Ideal.span_singleton_le_iff_mem _).mpr ha)
  have hrp : r.IsPrime := hr.1.1
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ r hr
  have h0 : r.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff]
    intro h0
    have : r = ⊥ := le_bot_iff.mp (h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)
    have hmem := hr.1.2 (Ideal.mem_span_singleton_self a)
    rw [this] at hmem
    exact ha0 hmem
  have : r.height = 1 := by
    revert h0 h1; generalize r.height = t; intro h1 h0
    cases t using ENat.recTopCoe with
    | top => simp at h1
    | coe t => norm_cast at *; omega
  obtain ⟨E, -⟩ := MMP.Mori.exists_primeDivisor_isLocalization ⟨r, hrp⟩ this
  exact ⟨E⟩

/-- A small morphism `f : X ⟶ Z` maps the generic point of every prime divisor of `X` to the
generic point of a prime divisor of `Z`: as `Ex(f)` has codimension at least two, `f` is an
isomorphism over a neighbourhood of `f(η_P)`, which therefore has coheight one. -/
private theorem exists_primeDivisor_map_genericPoint_eq_of_isSmallMorphism {k : Type u}
    [Field k] {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z}
    (hf : IsSmallMorphism sX sZ f) (P : MMP.Mori.PrimeDivisor X) :
    ∃ Q : MMP.Mori.PrimeDivisor Z, f P.genericPoint = Q.genericPoint := by
  have hx : f P.genericPoint ∈ MMP.Mori.biregularLocus f := by
    by_contra h
    have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hf.two_le_codimension
      (MMP.Mori.mem_exceptionalSet.mpr h)
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hcoh : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hx, P.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩

/-- **The inductive step.** Along the step `(U^j, Δ^j) ⇢ (U^{j+1}, Δ^{j+1})` of an elementary
program over `Z`, a prime divisor `F'` of `U^{j+1}` whose image in `Z` is not the generic point
of a prime divisor of `Z` is the strict transform of a prime divisor `F` of `U^j` with the same
image in `Z`, and `coeff_{F'} Δ^{j+1} = coeff_F Δ^j`: the program extracts no divisor and keeps
the coefficients of strict transforms. -/
private theorem coeff_succ_eq_one_of_forall_ne {X Z U : Scheme.{0}}
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {p : U ⟶ X} {Δ : QDivisor U} {KU : Divisor U}
    (P : RelativeElementaryDltProgram (p ≫ sX) KU Δ (p ≫ f)) (j : ℕ)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ P.n)
    (ih : ∀ F : MMP.Mori.PrimeDivisor (modelSeq U P.Y j),
      (∀ Q : MMP.Mori.PrimeDivisor Z, modelMap (p ≫ f) P.hY j F.genericPoint ≠ Q.genericPoint) →
        (divisorSeq Δ P.ΔY j).coeff F = 1)
    (F : MMP.Mori.PrimeDivisor (P.Y j))
    (hF : ∀ Q : MMP.Mori.PrimeDivisor Z, P.hY j F.genericPoint ≠ Q.genericPoint) :
    (P.ΔY j).coeff F = 1 := by
  have hlt : (j : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self j) hj
  have S := P.isProjectiveElementaryDltStep j hlt
  have hc := S.isContractionOfRay
  have hV := hc.isNormalVariety_target
  have : IsIntegral (P.V j) := hV.1.toIsIntegral
  have : IsNormal (P.V j) := hV.2
  have : LocallyOfFiniteType (P.sV j) := hV.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian (P.V j) := LocallyOfFiniteType.isLocallyNoetherian (P.sV j)
  have := MMP.Mori.IsVariety.isSeparated_terminal hV.1
  have : IsProper (P.f j) := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  have hg := S.isBirationalMorphism
  have : IsDominant (P.f j) := hg.isDominant
  -- `f_j⁺` is an isomorphism over the image of `η_F`
  have hreg : P.fp j F.genericPoint ∈ biregularLocus (P.fp j) := by
    rcases S.flip_or_divisorial with ⟨-, hfl⟩ | ⟨-, hiso⟩
    · have hs := hfl.isSmallMorphism_flip
      by_contra h
      have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hs.two_le_codimension
        (MMP.Mori.mem_exceptionalSet.mpr h)
      rw [F.coheight_genericPoint] at this
      exact absurd this (by decide)
    · rw [top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff _).mpr hiso))]
      trivial
  have hcoh : Order.coheight (P.fp j F.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hreg, F.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor (P.V j) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hQ : P.fp j F.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm
  -- the prime divisor `F₀` of `U^j` over `Q`
  have := Q.isDiscreteValuationRing_localRing
  obtain ⟨x, hx, hiso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing (P.f j)
    hg.functionFieldMap_bijective Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso ((P.f j).stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  obtain ⟨F₀, hF₀x⟩ : ∃ F₀ : MMP.Mori.PrimeDivisor (modelSeq U P.Y j), F₀.genericPoint = x :=
    ⟨_, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco⟩
  have hF₀ : P.f j F₀.genericPoint = Q.genericPoint := by rw [hF₀x]; exact hx
  -- the coefficient of the strict transform
  have hcoeff : (P.ΔY j).coeff F = (divisorSeq Δ P.ΔY j).coeff F₀ := by
    change (P.ΔY j) F = (divisorSeq Δ P.ΔY j) F₀
    rw [S.eq_flipTransform]
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ
        (hQ ▸ hQ ▸ hreg))
      (fun Q' hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hQ').1.symm.trans hQ)))]
    rw [RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ F₀ Q).mpr hF₀)
      (fun E' hE' => ?_)]
    have hE'Q := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ E' Q).mp hE'
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have : ValuationRing ((P.V j).presheaf.stalk (P.f j F₀.genericPoint)) := by
      rw [hF₀]; infer_instance
    have : ValuationRing ((P.V j).presheaf.stalk (P.f j E'.genericPoint)) := by
      rw [hE'Q]; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing _ hg.functionFieldMap_bijective
      F₀.genericPoint
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing _ hg.functionFieldMap_bijective
      E'.genericPoint
    exact (MMP.Positivity.eq_of_isIso_stalkMap _ hg.functionFieldMap_bijective
      (hE'Q.trans hF₀.symm)).symm
  rw [hcoeff]
  refine ih F₀ fun QZ hQZ => hF QZ ?_
  rw [P.hY_eq j hlt, Scheme.Hom.comp_apply, hQ, ← hF₀, ← Scheme.Hom.comp_apply, P.comp_hV j hlt]
  exact hQZ

/-- The base case: a prime divisor `F` of `U` whose image in `Z` is not the generic point of a
prime divisor of `Z` is `p`-exceptional (as `f` is small), so has coefficient one in `Δ`. -/
private theorem coeff_zero_eq_one_of_forall_ne {X Z U : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    {p : U ⟶ X} {Δ : QDivisor U} (hp : IsCrepantDltLift sX K B p Δ)
    (F : MMP.Mori.PrimeDivisor U)
    (hF : ∀ Q : MMP.Mori.PrimeDivisor Z, (p ≫ f) F.genericPoint ≠ Q.genericPoint) :
    Δ.coeff F = 1 := by
  obtain ⟨E, hE, hΔ⟩ := hp.boundary_eq
  have hsub : F.support ⊆ MMP.Intersection.exceptionalLocus p := by
    by_contra hn
    obtain ⟨P₀, hP₀, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hn
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmallMorphism hf P₀
    exact hF Q (by rw [Scheme.Hom.comp_apply, ← hP₀, hQ])
  have : IsProper p := isProper_of_isProjectiveMorphism p hp.isProjectiveMorphism
  rw [hΔ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hE F, if_pos hsub,
    coeff_birationalInverseTransform_eq_zero_of_subset hf.isNormalVariety_source
      hp.isQFactorial.1.1 hp.isBirationalMorphism B F hsub]
  simp

/-- Along an elementary program over `Z` from a crepant dlt lift `p : (U, Δ) ⟶ (X, B)` of a pair
whose contraction `f : X ⟶ Z` is small, every prime divisor of a model `U^j` whose image in `Z`
is not the generic point of a prime divisor of `Z` has coefficient one in `Δ^j`. -/
private theorem coeff_eq_one_of_forall_ne {X Z U : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    {p : U ⟶ X} {Δ : QDivisor U} (hp : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (P : RelativeElementaryDltProgram (p ≫ sX) KU Δ (p ≫ f)) :
    ∀ j : ℕ, (j : ℕ∞) ≤ P.n → ∀ F : MMP.Mori.PrimeDivisor (modelSeq U P.Y j),
      (∀ Q : MMP.Mori.PrimeDivisor Z, modelMap (p ≫ f) P.hY j F.genericPoint ≠ Q.genericPoint) →
        (divisorSeq Δ P.ΔY j).coeff F = 1
  | 0, _, F, hF => coeff_zero_eq_one_of_forall_ne hf hp F hF
  | j + 1, hj, F, hF =>
    coeff_succ_eq_one_of_forall_ne P j hj
      (coeff_eq_one_of_forall_ne hf hp P j (le_trans (by exact_mod_cast Nat.le_succ j) hj)) F hF

/-- The key step: a `p'`-exceptional prime divisor `F` of `U^m` has coefficient one in `Δ^m`.
As `f⁺` is small, `f⁺` is an isomorphism over the generic point of every prime divisor of `Z`,
so the image of `F` in `Z` is not such a generic point (else `p'(η_F)` would be the generic
point of a prime divisor of `X⁺`, and `F` would not be `p'`-exceptional); conclude by
`coeff_eq_one_of_forall_ne`. -/
private theorem coeff_eq_one_of_subset {X X' Z U : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hs : IsSmallMorphism sX' sZ fp) (hf : IsSmallMorphism sX sZ f)
    {p : U ⟶ X} {Δ : QDivisor U} (hp : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (P : RelativeElementaryDltProgram (p ≫ sX) KU Δ (p ≫ f))
    (p' : modelSeq U P.Y P.n.toNat ⟶ X')
    (hp'Z : p' ≫ fp = modelMap (p ≫ f) P.hY P.n.toNat)
    [IsProper p'] (hp' : IsBirationalMorphism p')
    (hX' : IsNormalVariety ℂ sX') (hY : MMP.Mori.IsVariety ℂ (p' ≫ sX'))
    (F : MMP.Mori.PrimeDivisor (modelSeq U P.Y P.n.toNat))
    (hF : F.support ⊆ MMP.Intersection.exceptionalLocus p') :
    (divisorSeq Δ P.ΔY P.n.toNat).coeff F = 1 := by
  refine coeff_eq_one_of_forall_ne hf hp P _ (ENat.coe_toNat_le_self _) F fun Q hQ => ?_
  have hZ := hs.isNormalVariety_target
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsIntegral X' := hX'.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsProper fp := hs.isProper
  have : IsDominant fp := hs.isBirationalMorphism.isDominant
  have hreg := MMP.Positivity.mem_biregularLocus_of_coheight_le_one fp
    hs.isBirationalMorphism.functionFieldMap_bijective hs.two_le_codimension
    (y := Q.genericPoint) (by rw [Q.coheight_genericPoint])
  rw [← hQ, ← hp'Z, Scheme.Hom.comp_apply] at hreg
  have hcoh : Order.coheight (p' F.genericPoint) = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hreg, ← Scheme.Hom.comp_apply,
      hp'Z, hQ, Q.coheight_genericPoint]
  exact map_genericPoint_ne_of_subset_exceptionalLocus hX' hY hp' hF
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh)
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm

/-- For a permitted step `(X, B) → Z ← (X⁺, B⁺)` of projective lc fourfold pairs over `ℂ` with
small contraction `f`, a crepant dlt lift `p : (U, Δ) ⟶ (X, B)`, and an elementary dlt program
`P` over `Z` from `(U, Δ)` with `h₀ = p ≫ f`, ending at `(U^m, Δ^m)`: every projective birational
morphism `p' : U^m ⟶ X⁺` over `ℂ` and over `Z` along which `Δ^m` is the crepant boundary of
`(X⁺, B⁺)` is a crepant dlt lift of `(X⁺, B⁺)` with boundary `Δ^m`. -/
@[mmp "lem_oai4_c3_dlt_bridge_end_is_lift"]
public theorem IsCrepantDltLift.of_relativeElementaryDltProgram
    {X X' Z U : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hstep : IsPermittedStep sX sZ sX' K B R f fp)
    (hdim : topologicalKrullDim X = 4) (hdim' : topologicalKrullDim X' = 4)
    (hf : IsSmallMorphism sX sZ f)
    {p : U ⟶ X} {Δ : QDivisor U} (hp : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (P : RelativeElementaryDltProgram (p ≫ sX) KU Δ (p ≫ f))
    (p' : modelSeq U P.Y P.n.toNat ⟶ X')
    (hp'ℂ : p' ≫ sX' = modelStr (p ≫ sX) P.sY P.n.toNat)
    (hp'Z : p' ≫ fp = modelMap (p ≫ f) P.hY P.n.toNat)
    (hp'proj : IsProjectiveMorphism p') (hp' : IsBirationalMorphism p')
    (hY : IsNormalVariety ℂ (p' ≫ sX'))
    (hcrep : ∃ n : ℕ, IsCrepantBoundary sX' n (flipTransform f fp K) (flipTransform f fp B) p'
      hY hp' (divisorSeq Δ P.ΔY P.n.toNat)) :
    IsCrepantDltLift sX' (flipTransform f fp K) (flipTransform f fp B) p'
      (divisorSeq Δ P.ΔY P.n.toNat) := by
  have hm := P.isProjectiveQFactorialDltPair P.n.toNat (ENat.coe_toNat_le_self _)
  rw [← hp'ℂ] at hm
  have : MMP.Mori.IsVariety ℂ (p' ≫ sX') := hm.isQFactorial.1.1
  have : MMP.Mori.IsVariety ℂ sX' := hstep.isProjectiveVariety_step.toIsVariety
  have hdimU : 0 < topologicalKrullDim (modelSeq U P.Y P.n.toNat) := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (p' ≫ sX') hp',
      hdim']
    decide
  obtain ⟨F₀⟩ := nonempty_primeDivisor_of_pos hdimU
  refine ⟨hstep.isProjectiveVariety_step, hstep.isLogCanonicalPair_step, ?_, hp'proj, hp',
    hm.isQFactorial, ?_, hm.isDltPair, hcrep⟩
  · obtain ⟨n, hn⟩ := hcrep
    exact ⟨n, (hn F₀).2.1⟩
  · have : IsProper p' := isProper_of_isProjectiveMorphism p' hp'proj
    obtain ⟨n, hn⟩ := hcrep
    have hX' : IsNormalVariety ℂ sX' := (hn F₀).1
    obtain ⟨E, hE⟩ := MMP.Intersection.exists_isExceptionalDivisorSum hp'
    refine ⟨E, hE, DivisorWithCoeffs.ext' fun F => ?_⟩
    rw [coeff_birationalInverseTransform_add_exceptionalDivisorSum hX' hm.isQFactorial.1.1 hp' _ hE]
    split_ifs with hF
    · exact coeff_eq_one_of_subset hstep.isSmallMorphism_step hf hp P p' hp'Z hp' hX'
        hm.isQFactorial.1.1 F hF
    · exact coeff_eq_of_not_subset_of_isCrepantBoundary (μ := p') hn F hF

end MMP.Fourfold
