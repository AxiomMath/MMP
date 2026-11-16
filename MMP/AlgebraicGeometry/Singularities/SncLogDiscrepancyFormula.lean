module
public import MMP.Attr
public import Mathlib
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicTopology.PoincareDualityGoodCover
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
public import MMP.AlgebraicGeometry.Resolution.SmoothCentreBlowup
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Resolution.Blowup
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
public import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Resolution.ZariskiSequenceBasic
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
public import MMP.AlgebraicGeometry.Morphisms.ChowLemma
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Resolution.Blowup.ProjectiveBirationalIsBlowup
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Log discrepancies over snc divisors, and the blowup package

Let `Y` be a smooth variety over a perfect field `k`, `S = B₁ + ⋯ + B_m` a reduced snc divisor on
`Y`, and `ν` a divisor over `Y` with center `Z`. This file computes the log discrepancies of `ν`
over boundaries supported on `S` (Flips and Abundance 4.12.1).

* For the reduced boundary `S` itself, `a_ℓ(ν, Y, S)` is a natural number `k` with
  `k ≥ codim_Y Z - s`, where `s` is the number of components `Bᵢ` containing `Z`. The proof
  blows up the center of `ν` repeatedly: on an affine open `U` on which `Z ∩ U` is smooth and
  which misses the components of `S` not through `Z`, the blow-up `π : Y' ⟶ U` of `Z ∩ U` with
  exceptional divisor `F` satisfies `π^*(K + S|_U) = K_{Y'} + S' - (c - s) F` for
  `S' = π⁻¹_* S|_U + F`, so `a_ℓ(ν, Y, S) = a_ℓ(ν, Y', S') + (c - s) ν(F)` with `ν(F) ≥ 1`. The
  process ends when the center becomes a divisor, where `a_ℓ = 1 - coeff`.
* For `B = ∑ bᵢ Bᵢ` with arbitrary real `bᵢ`, the discrepancy is affine in the boundary, so
  `a_ℓ(ν, Y, B) = l + ∑ nᵢ (1 - bᵢ)` with `l = a_ℓ(ν, Y, S)` and `nᵢ = ν(Bᵢ)`, the order along `ν`
  of a local equation of `Bᵢ`; here `nᵢ ≥ 1` exactly when `Z ⊆ Bᵢ`.
* If moreover every `bᵢ ≤ 1`, `(1 - bᵢ) + (1 - bⱼ) ≥ 2` whenever `Bᵢ ≠ Bⱼ` meet, `codim Z ≥ 2`
  and `a_ℓ(ν, Y, B) < 2`, then `codim Z = 2`, exactly one component `B_{i₀}` contains `Z`,
  `b_{i₀} > 0` and `a_ℓ(ν, Y, B) ≥ 2 - b_{i₀}`.

The last part of the file is independent of the rest: five standard facts about the blowup
`π : blowUp J ⟶ X` of a complex variety `X` in a nonzero ideal sheaf `J`: its universal
property, strict transforms of integral closed subschemes, the presentation of projective
birational morphisms onto a quasi-projective `X` as blowups, the extension of ideal sheaves from
open subschemes, and Chow's lemma.

## Main results

* `MMP.Flips.exists_logDiscrepancy_eq_natCast_of_isSNCDivisor`: `a_ℓ(ν, Y, S) = k` for some
  `k : ℕ` with `codim_Y Z ≤ k + s`.
* `MMP.Flips.exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor`: the formula
  `a_ℓ(ν, Y, B) = l + ∑ nᵢ (1 - bᵢ)`, with the bounds on `l` and the `nᵢ`.
* `MMP.Flips.codimension_center_eq_two_of_logDiscrepancy_lt_two`: centers of divisors with log
  discrepancy `< 2`.
* `MMP.blowUp_universal_strictTransform_presentation_extension_chow`: the blowup package.

## Implementation notes

The reduced divisor `B₁ + ⋯ + B_m` is a `Divisor` `S` with `MMP.Flips.IsSNCDivisor`, which forces
every coefficient to be `0` or `1`; its components are the members of `S.support`. A boundary `B`
is an `ℝ`-divisor with support in that of `S`, and `bᵢ = B.coeff Bᵢ`. The log discrepancy is the
relation `MMP.Flips.IsLogDiscrepancy`, so each statement is asserted for every value it relates to
`ν`, and `ν` is a `MMP.Flips.ProperDivisorOver`, with center `ν.center`. Inequalities between
integers `k ≥ 0` are recorded by taking `k : ℕ`, and the bounds are stated in `ℕ∞`.

The base field is any perfect field rather than `ℂ`: over an imperfect field the order of a top
form along a divisor that is not smooth over the base is not the geometric one, and the bound of
4.12.1 fails. Source 4.12.1.3 also asserts that `ν` is the blow-up of the generic point of `Z`;
that is false (blowing up a point on a line `B₁ ⊂ 𝔸²` with `B = ¾ B₁` and then the point where the
exceptional curve meets the strict transform of `B₁` gives log discrepancy `3/2`), and is omitted.

The induction on blow-ups runs along
`MMP.Flips.hasNonemptyCenter_and_exists_coheight_eq_one_of_blowUp`, which guarantees that the
sequence of blow-ups of the centers of `ν` reaches a model on which the center is a divisor; a
counterexample to the bound would produce an infinite such sequence.

For the blowup package, an `AlgebraicGeometry.Scheme.IdealSheafData` is quasi-coherent by
construction, hence coherent on the noetherian `X`. The ideal `J · 𝒪_Y` of `g : Y ⟶ X` is
`J.comap g`, "invertible" is `Stacks.Divisors.IsEffectiveCartierDivisor`, a closed subvariety is an
integral scheme with a closed immersion into `X`, and birationality is
`MMP.Mori.IsBirationalMorphism`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.1
* [Kollár–Mori, *Birational geometry of algebraic varieties*]
* [Hartshorne, *Algebraic Geometry*, II.7.14, II.7.15, II.7.17]
* [Stacks Project, Tag 0806]
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP.Mori MMP.Resolution
open scoped WithZero

/-! ### Log discrepancies over a reduced snc divisor -/

open Classical in
/-- The bound when the centre of `ν` is a prime divisor `P`: then `a_ℓ(ν, Y, S) = 1 - coeff_P S`.
-/
private theorem exists_logDiscrepancy_eq_natCast_of_codimension_center_le_one {k : Type u}
    [Field k] [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    (hY : MMP.Mori.IsVariety k sY) {S : Divisor Y} (hS : IsSNCDivisor sY S)
    (ν : ProperDivisorOver k sY) {d : ℕ} {K : Divisor Y} {b : ℝ}
    (hb : IsLogDiscrepancy sY d K (Divisor.toRDivisor S) ν.valuation b)
    (hcod : codimension ν.center ≤ 1) :
    ∃ m : ℕ, b = m ∧ codimension ν.center ≤
      (m + (S.support.filter fun P => (ν.center : Set Y) ⊆ P.support).card : ℕ∞) := by
  have hX : IsNormalVariety k sY := ⟨hY, inferInstance⟩
  obtain ⟨P, hP⟩ : ∃ P : MMP.Mori.PrimeDivisor Y, ν.toDivisorOver.valuation =
      (DivisorOver.ofPrimeDivisor k hX P).valuation := by
    by_contra h
    push Not at h
    have h2 := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX ν.toDivisorOver).2 h
    rw [← ν.center_eq_toDivisorOver_center] at h2
    exact absurd hcod (not_le.2 (lt_of_lt_of_le (by norm_num) h2))
  have hval : (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation :=
    Valuation.ext fun g => by
      change P.divisorialValuation (functionFieldMap (𝟙 Y) g) = _
      rw [functionFieldMap_id_apply]
  have hP' : ν.valuation = P.divisorialValuation := hP.trans hval
  have hgen : ν.f ν.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY (D := ν.toDivisorOver)
      (D' := DivisorOver.ofPrimeDivisor k hX P) hP
  have hc : (ν.center : Set Y) = P.support := by
    rw [ν.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.center_eq_closureSingleton]
    rw [hgen, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rfl
  obtain ⟨a, ha, rfl⟩ := hb
  rw [hP'] at ha
  have hcoef := IsDiscrepancy.eq_neg_coeff ha
  have hcoef' : a = -(S.coeff P : ℝ) := by simpa using hcoef
  rcases hS.1 P with h0 | h1
  · refine ⟨1, ?_, ?_⟩
    · rw [hcoef', h0]; simp
    · refine hcod.trans ?_
      simp
  · refine ⟨0, ?_, ?_⟩
    · rw [hcoef', h1]; simp
    · refine hcod.trans ?_
      have hmem : P ∈ S.support.filter fun P => (ν.center : Set Y) ⊆ P.support := by
        simp only [Finset.mem_filter]
        refine ⟨?_, hc.le⟩
        have h1' : S P = 1 := h1
        simp [Finsupp.mem_support_iff, h1']
      have : 1 ≤ (S.support.filter fun P => (ν.center : Set Y) ⊆ P.support).card :=
        Finset.card_pos.2 ⟨P, hmem⟩
      simpa using (Nat.one_le_cast.2 this : (1 : ℕ∞) ≤ _)

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, ?_⟩, E, rfl⟩
  rfl

/-- The inverse image of the reduced subscheme on a closed set along an open immersion is the
reduced subscheme on the inverse image. -/
private theorem comap_vanishingIdeal_of_isOpenImmersion {V X : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap j =
      Scheme.IdealSheafData.vanishingIdeal ⟨j ⁻¹' Z, Z.isClosed.preimage j.continuous⟩ := by
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap j).support =
      ⟨j ⁻¹' Z, Z.isClosed.preimage j.continuous⟩ := by
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.support_comap]
    change j ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set X) = _
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsReduced (Limits.pullback j (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    isReduced_of_isOpenImmersion (Limits.pullback.snd _ _)
  have : IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).comap j).subscheme :=
    isReduced_of_isOpenImmersion ((Scheme.IdealSheafData.vanishingIdeal Z).comapIso j).hom
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism followed by the inclusion of a nonempty open is birational. -/
private theorem isBirationalMorphism_comp_ι {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (U : X.Opens) [Nonempty U] (f : Y ⟶ U) (hf : IsBirationalMorphism f) :
    IsBirationalMorphism (f ≫ U.ι) := by
  have : IsDominant f := hf.isDominant
  have : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  obtain ⟨W, hWne, hW⟩ := hf.exists_isOpenImmersion
  have : IsOpenImmersion (W.ι ≫ f ≫ U.ι) := by
    rw [← Category.assoc]; infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ U.ι) W (W.isOpen.dense hWne)

section PullbackComp

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]

/-- The only irreducible component of an irreducible space is the whole space. -/
private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 := by
  rw [W.2.eq_of_le (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _)]
  trivial

/-- Pull-back of Cartier divisors along a composite: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
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
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent
    (pointComponent ((g ≫ f) z)) _)
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
      (mem_irreducibleComponent (pointComponent ((g ≫ f) z)) _)
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

end PullbackComp

/-- On a smooth variety over a perfect field the divisor of a nonzero rational top form is a
canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (hXs : IsSmoothScheme sX)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    (divisorOfForm τ).IsCanonicalDivisor sX n := by
  have := hX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hXs hn
  exact hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul ⟨hX, inferInstance⟩ hK hτ

/-- A point of an open subscheme of a scheme locally of finite type over a field which is closed in
the open subscheme is closed in the scheme. -/
private theorem isClosed_singleton_ι {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (U : X.Opens) {x : (U : Scheme.{u})}
    (hx : IsClosed ({x} : Set (U : Scheme.{u}))) : IsClosed ({U.ι x} : Set X) := by
  have := LocallyOfFiniteType.jacobsonSpace sX
  refine isClosed_singleton_of_isLocallyClosed_singleton ?_
  have h1 : ({U.ι x} : Set X) = U.ι '' {x} := by simp
  rw [h1]
  exact (hx.isLocallyClosed).image U.ι.isOpenEmbedding.toIsInducing
    U.ι.isOpenEmbedding.isOpen_range.isLocallyClosed

/-- The restriction of a (reduced) snc divisor to an open subscheme is snc. -/
private theorem isSNCDivisor_restrictOpen {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {S : Divisor X} (hS : IsSNCDivisor sX S) (U : X.Opens) :
    IsSNCDivisor (U.ι ≫ sX) (S.restrictOpen U) := by
  refine ⟨fun E => hS.1 _, fun E hE => ?_, fun p hp => ?_⟩
  · have hE' : OpenWeilRestriction.primeDivisorMap U.ι E ∈ S.support := by
      rw [Finsupp.mem_support_iff] at hE ⊢
      exact hE
    have hsm := hS.2.1 _ hE'
    have : LocallyOfFinitePresentation
        ((OpenWeilRestriction.primeDivisorMap U.ι E).idealSheaf.subschemeι ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType
        (f := (OpenWeilRestriction.primeDivisorMap U.ι E).idealSheaf.subschemeι ≫ sX)).mpr
        inferInstance
    refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sX
      (OpenWeilRestriction.primeDivisorMap U.ι E).idealSheaf E.idealSheaf
      (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι E)).mpr ?_
    intro z _
    have h1 : z ∈ smoothLocus
        ((OpenWeilRestriction.primeDivisorMap U.ι E).idealSheaf.subschemeι ≫ sX) := by
      rw [hsm]; trivial
    rwa [smoothLocus_eq_smoothLocus] at h1
  · exact (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι S p).mpr
      (hS.2.2 _ (isClosed_singleton_ι sX U hp))

/-- The pull-back of a Cartier divisor along the inclusion of a nonempty open subscheme is its
restriction. -/
private theorem isPullback_ι_restrictOpen {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (U : X.Opens) [Nonempty U] [CompactSpace U] {D : Divisor X} (hD : D.IsCartier) :
    haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
    D.IsPullback U.ι (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp U.ι D)
      (D.restrictOpen U) := by
  have : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  obtain ⟨D', hD'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant U.ι hD
  convert hD'
  ext W
  obtain ⟨V, hV, φ, hφ⟩ := hD (U.ι W.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hD' hφ W hV
    (MMP.Mori.pointComponent (U.ι W.genericPoint)),
    MMP.Positivity.ord_functionFieldMap_of_isIso U.ι W (OpenWeilRestriction.primeDivisorMap U.ι W)
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]
  rw [DivisorWithCoeffs.coeff_restrictOpen]
  set P : MMP.Mori.PrimeDivisor X := OpenWeilRestriction.primeDivisorMap U.ι W
  have hPV : P.genericPoint ∈ V := by
    convert hV using 1
    exact OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W
  rw [hφ P ((P.genericPoint_mem_iff V).mp hPV), MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  have hZ : P.component = MMP.Mori.pointComponent (U.ι W.genericPoint) := Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  rw [hZ]

/-- The divisor of the restriction of a rational top form to a nonempty open subscheme is the
restriction of its divisor. -/
private theorem divisorOfForm_pullback_ι {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (U : X.Opens) [Nonempty U] [CompactSpace U] {n : ℕ}
    (hn : topologicalKrullDim X = n) (ω : RationalPluriForms sX n 1) :
    haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
    divisorOfForm (pullbackRationalPluriForms sX U.ι ω) = (divisorOfForm ω).restrictOpen U := by
  have : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij : Function.Bijective (functionFieldMap U.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
      ⟨Classical.arbitrary _, trivial⟩
  ext W
  rw [DivisorWithCoeffs.coeff_restrictOpen, coeff_divisorOfForm, coeff_divisorOfForm]
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso U.ι hbij hd W _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm ω

/-- **Regular parameters adapted to a regular quotient.** Let `R` be a regular local ring with a
regular system of parameters `z`, `I` a prime ideal with `R / I` regular, and `z_{j(1)}, …,
z_{j(s)}` distinct parameters lying in `I`. Then `I` has height `c ≥ s` and there is a regular
system of parameters `x` whose first `s` members are the `z_{j(i)}` and whose first `c` members
generate `I`. -/
private theorem exists_isRegularSystemOfParameters_adapted {R : Type*} [CommRing R]
    [IsRegularLocalRing R]
    {N : ℕ} {z : Fin N → R} (hz : IsRegularSystemOfParameters z) {s : ℕ} (j : Fin s → Fin N)
    (hj : Function.Injective j) (I : Ideal R) [I.IsPrime] (hI : IsRegularLocalRing (R ⧸ I))
    (hzI : ∀ i, z (j i) ∈ I) :
    ∃ (c : ℕ) (x : Fin N → R), IsRegularSystemOfParameters x ∧ s ≤ c ∧ I.height = c ∧
      (∀ i : Fin s, ∃ l : Fin N, (l : ℕ) = i ∧ x l = z (j i)) ∧
      Ideal.span (x '' {l | (l : ℕ) < c}) = I := by
  classical
  set y : Fin s → R := z ∘ j with hy
  set J := Ideal.span (Set.range y) with hJ
  have hsN : s ≤ N := by simpa using Fintype.card_le_of_injective j hj
  -- `R / (y)` is regular of dimension `N - s`
  obtain ⟨hreg, hdimJ, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image
    hz (Finset.univ.image j)
  have hJeq : Ideal.span (z '' ((Finset.univ.image j : Finset (Fin N)) : Set (Fin N))) = J := by
    rw [hJ]; congr 1; ext a; simp [hy]
  rw [hJeq, Finset.card_image_of_injective _ hj, Finset.card_univ, Fintype.card_fin] at hdimJ
  rw [hJeq] at hreg
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hzI i)
  set R' := R ⧸ J
  have hIne : J ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hcomap : ∀ K : Ideal R, J ≤ K →
      (K.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = K := fun K hK => by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hK]
  set I' := I.map (Ideal.Quotient.mk J)
  let e : R' ⧸ I' ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE hJI
  have hI' : IsRegularLocalRing (R' ⧸ I') := IsRegularLocalRing.of_ringEquiv e.symm
  obtain ⟨k', h', hh'I, hk'dim⟩ :=
    MMP.Flips.ResolutionInputs.exists_fin_span_eq_of_isRegularLocalRing_quotient I' hI'
  obtain ⟨m', t, htt⟩ := (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff
    h').mp ⟨by rw [hh'I]; exact hI', by rw [hh'I]; exact hk'dim⟩
  have hdimR' : ringKrullDim R' = (k' + m' : ℕ) := htt.2
  have hNsum : N = s + (k' + m') := by
    rw [hdimJ] at hdimR'
    have : N - s = k' + m' := by exact_mod_cast hdimR'
    omega
  -- the height of `I`
  have hCM :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2
  have hRI := hCM.ringKrullDim_eq_height_add_ringKrullDim_quotient I
  have hdimRI : ringKrullDim (R ⧸ I) = (m' : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    rw [hdimR'] at hk'dim
    have hfin : ringKrullDim (R' ⧸ I') ≠ ⊤ := by
      have := hI'
      exact ringKrullDim_ne_top
    have hbot : ringKrullDim (R' ⧸ I') ≠ ⊥ := ringKrullDim_ne_bot
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (R' ⧸ I') = d := by
      induction h : ringKrullDim (R' ⧸ I') using WithBot.recBotCoe with
      | bot => exact absurd h hbot
      | coe a =>
        induction a using ENat.recTopCoe with
        | top => exact absurd h hfin
        | coe d => exact ⟨d, rfl⟩
    rw [hd] at hk'dim ⊢
    have : d + k' = k' + m' := by exact_mod_cast hk'dim
    exact_mod_cast (by omega : d = m')
  have hheight : I.height = (s + k' : ℕ) := by
    rw [hz.2, hdimRI, hNsum] at hRI
    have hfin : I.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
    obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, I.height = h0 := ⟨I.height.toNat, (ENat.natCast_toNat hfin).symm⟩
    rw [hh0] at hRI ⊢
    have : s + (k' + m') = h0 + m' := by exact_mod_cast hRI
    exact_mod_cast (by omega : h0 = s + k')
  -- lifts
  choose x' hx' using fun i => Ideal.Quotient.mk_surjective (I := J) (h' i)
  choose w hw using fun l => Ideal.Quotient.mk_surjective (I := J) (t l)
  have hmapx' : (Ideal.span (Set.range x')).map (Ideal.Quotient.mk J) =
      Ideal.span (Set.range h') := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact hx' i
  have hmapw : (Ideal.span (Set.range w)).map (Ideal.Quotient.mk J) =
      Ideal.span (Set.range t) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext l
    exact hw l
  have hmapJ : J.map (Ideal.Quotient.mk J) = ⊥ := Ideal.map_quotient_self J
  set X : Fin (s + (k' + m')) → R := Fin.append y (Fin.append x' w) with hX
  have hspanX : Ideal.span (Set.range X) =
      J ⊔ (Ideal.span (Set.range x') ⊔ Ideal.span (Set.range w)) := by
    rw [hX, MMP.Flips.ResolutionInputs.span_range_append,
      MMP.Flips.ResolutionInputs.span_range_append]
  have hXrsop : IsRegularSystemOfParameters X := by
    refine ⟨?_, ?_⟩
    · have hJK : J ≤ Ideal.span (Set.range X) := by rw [hspanX]; exact le_sup_left
      rw [← hcomap _ hJK, ← hcomap _ (IsLocalRing.le_maximalIdeal hIne),
        IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← htt.1]
      congr 1
      rw [hspanX, Ideal.map_sup, Ideal.map_sup, hmapJ, bot_sup_eq, hmapx', hmapw,
        MMP.Flips.ResolutionInputs.span_range_append]
    · rw [hz.2, ← hNsum]
  have hIX : Ideal.span (Set.range (Fin.append y x')) = I := by
    have hJK : J ≤ Ideal.span (Set.range (Fin.append y x')) := by
      rw [MMP.Flips.ResolutionInputs.span_range_append]
      exact le_sup_left
    rw [← hcomap _ hJK, ← hcomap _ hJI]
    congr 1
    rw [MMP.Flips.ResolutionInputs.span_range_append, Ideal.map_sup, hmapJ, bot_sup_eq, hmapx',
      hh'I]
  -- reindex
  let σ : Fin N ≃ Fin (s + (k' + m')) := finCongr hNsum
  refine ⟨s + k', X ∘ σ, ⟨?_, ?_⟩, by omega, hheight, fun i => ⟨⟨i, by omega⟩, rfl, ?_⟩, ?_⟩
  · rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ, hXrsop.1]
  · rw [hz.2]
  · change Fin.append y (Fin.append x' w) (Fin.cast hNsum ⟨i, _⟩) = z (j i)
    rw [show (Fin.cast hNsum ⟨i, by omega⟩ : Fin (s + (k' + m'))) = Fin.castAdd _ i from rfl,
      Fin.append_left, hy]
    rfl
  · rw [← hIX, Set.image_comp]
    congr 1
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      simp only [Set.mem_image, Set.mem_ofPred_eq] at hb
      obtain ⟨l, hl, rfl⟩ := hb
      change Fin.append y (Fin.append x' w) (Fin.cast hNsum l) ∈ _
      by_cases h1 : (l : ℕ) < s
      · rw [show (Fin.cast hNsum l : Fin (s + (k' + m'))) = Fin.castAdd _ ⟨l, h1⟩ from rfl,
          Fin.append_left]
        exact ⟨Fin.castAdd _ ⟨l, h1⟩, by rw [Fin.append_left]⟩
      · have h2 : (l : ℕ) - s < k' := by omega
        rw [show (Fin.cast hNsum l : Fin (s + (k' + m'))) =
            Fin.natAdd s (Fin.castAdd m' ⟨l - s, h2⟩) from Fin.ext (by simp; omega),
          Fin.append_right, Fin.append_left]
        exact ⟨Fin.natAdd s ⟨l - s, h2⟩, by rw [Fin.append_right]⟩
    · rintro ⟨b, rfl⟩
      induction b using Fin.addCases with
      | left i =>
        refine ⟨Fin.castAdd _ i, ⟨⟨i, by omega⟩, by simp; omega, Fin.ext rfl⟩, ?_⟩
        rw [hX, Fin.append_left, Fin.append_left]
      | right i =>
        refine ⟨Fin.natAdd s (Fin.castAdd m' i),
          ⟨⟨s + i, by omega⟩, by simp, Fin.ext rfl⟩, ?_⟩
        rw [hX, Fin.append_right, Fin.append_left, Fin.append_right]

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

open Classical in
/-- **One step of the induction, on the level of discrepancies.** Let `β : Y' ⟶ Y` be a morphism
of normal varieties inducing an isomorphism of function fields, `Y'` smooth, and suppose that for
every form `ω` with `div ω = K` the pull-back of the Cartier divisor `K + S` is
`div(β^*ω) + S' - e F`. If `E'` is a divisor over `Y'` whose centre lies in `F` and which is a
divisor over `Y` through `β`, a discrepancy `a = a(ord_{E'}, Y, S)` is `a' + e μ` for a
discrepancy `a' = a(ord_{E'}, Y', S')` and an integer `μ ≥ 1` (the multiplicity of `F` along
`ord_{E'}`). -/
private theorem isDiscrepancy_of_isPullback {k : Type u} [Field k] [PerfectField k]
    {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] (β : Y' ⟶ Y) [IsDominant β] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] [CompactSpace Y'] [LocallyOfFiniteType (β ≫ sY)] {sY' : Y' ⟶ Spec (.of k)}
    (hsY : β ≫ sY = sY') [LocallyOfFiniteType sY']
    (hY' : MMP.Mori.IsVariety k sY') (hY's : IsSmoothScheme sY')
    (hβ : Function.Bijective (functionFieldMap β)) {n : ℕ} (hn' : topologicalKrullDim Y' = n)
    {K S : Divisor Y} (hKS : (K + S).IsCartier) (S' : Divisor Y') (F : MMP.Mori.PrimeDivisor Y')
    (e : ℤ)
    (hpb : ∀ ω : RationalPluriForms sY n 1, ω ≠ 0 → divisorOfForm ω = K →
      (K + S).IsPullback β (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp β _)
        (divisorOfForm (pullbackRationalPluriForms sY β ω) + S' - e • Finsupp.single F 1))
    (E' : ProperDivisorOver k sY') (hE'β : IsBirationalMorphism (E'.f ≫ β))
    (hE'F : E'.f E'.E.genericPoint ∈ F.support) {a : ℝ}
    (ha : IsDiscrepancy sY n K (Divisor.toRDivisor S)
      (E'.valuation.comap (functionFieldMap β)) a) :
    ∃ (K' : Divisor Y') (a' : ℝ) (μ : ℕ),
      IsDiscrepancy sY' n K' (Divisor.toRDivisor S') E'.valuation a' ∧ 1 ≤ μ ∧
        a = a' + e * μ := by
  subst hsY
  obtain ⟨hK, -, -, E, ω, m, r, L, hEν, hωK, hX, hn, hω0, hLc, hsum, L', hpbL, rfl⟩ := ha
  have hpbω := hpb ω hω0 hωK
  have := E'.isIntegral
  have := E'.isNormal
  have := E'.isLocallyNoetherian
  have := E'.isDominant
  have := E'.isProper
  have : CompactSpace E'.Y := QuasiCompact.compactSpace_of_compactSpace E'.f
  have hcart : ∀ D : Divisor Y', D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hY's
  have hEβnv : IsNormalVariety k ((E'.f ≫ β) ≫ sY) := by
    have h := E'.isNormalVariety
    rwa [← Category.assoc] at h
  let Eβ : DivisorOver k sY := ⟨E'.Y, E'.f ≫ β, hEβnv, hE'β, E'.E⟩
  have hv : E.toDivisorOver.valuation = Eβ.valuation := by
    change E.valuation = _
    rw [hEν]
    ext t
    change E'.E.divisorialValuation (functionFieldMap E'.f (functionFieldMap β t)) =
      E'.E.divisorialValuation (functionFieldMap (E'.f ≫ β) t)
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  obtain ⟨G, hG⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant (E'.f ≫ β) hKS
  have hco : ∀ {p : ℕ} {ρ : Fin p → ℝ} {M : Fin p → Divisor Y} {τ : RationalPluriForms sY n 1},
      Divisor.toRDivisor (divisorOfForm τ) + Divisor.toRDivisor S =
        ∑ j, ρ j • Divisor.toRDivisor (M j) →
      ∀ Γ : MMP.Mori.PrimeDivisor Y, (Γ.ordForm τ : ℝ) + (Divisor.toRDivisor S).coeff Γ =
        ∑ j, ρ j * (M j).coeff Γ := by
    intro p ρ M τ hs Γ
    have := congrArg (fun D : RDivisor Y => D.coeff Γ) hs
    simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      coeff_sum_smul_toRDivisor] using this
  have hsum₂ : ∀ Γ : MMP.Mori.PrimeDivisor Y, (Γ.ordForm ω : ℝ) +
      (Divisor.toRDivisor S).coeff Γ =
        ∑ j : Fin 1, (fun _ => (1 : ℝ)) j * ((fun _ => K + S) j).coeff Γ := by
    intro Γ
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, Int.cast_add]
    rw [← hωK, coeff_divisorOfForm]
  have key := ordPullback_sub_sum_eq_of_valuation_eq hX hn hv hω0 hω0 hLc
    (fun _ : Fin 1 => hKS) (hco hsum) hsum₂ L' (fun _ => G) hpbL (fun _ => ⟨_, hG⟩)
  set ω' := pullbackRationalPluriForms sY β ω with hω'
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hn
  have hω'0 : ω' ≠ 0 := pullbackRationalPluriForms_ne_zero β hβ hd hω0
  have hord : Eβ.ordPullback ω = E'.toDivisorOver.ordPullback ω' := by
    change E'.E.ordForm (pullbackRationalPluriForms sY (E'.f ≫ β) ω) =
      E'.E.ordForm (pullbackRationalPluriForms (β ≫ sY) E'.f ω')
    rw [hω', pullbackRationalPluriForms_comp β E'.f hβ
      E'.isBirationalMorphism.functionFieldMap_bijective hd ω]
    rfl
  set K' := divisorOfForm ω' with hK'
  obtain ⟨M, hM⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant E'.f (hcart (K' + S'))
  obtain ⟨Fp, hFp⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant E'.f
    (hcart (Finsupp.single F 1))
  have hG₀ : (K' + S' - e • Finsupp.single F 1).IsPullback E'.f
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E'.f _) (M + (-e) • Fp) := by
    have h1 := hFp.zsmul (hcart _) (-e)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E'.f _)
    have h2 := hM.add (hcart _) (hcart _)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E'.f _) h1
    exact Divisor.IsPullback.of_eq (by rw [neg_smul, ← sub_eq_add_neg]) h2
  have hcomp := isPullback_comp hpbω hG₀
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (E'.f ≫ β) _)
  have hGeq : G = M + (-e) • Fp := hG.eq hKS hcomp
  -- the multiplicity of `F`
  have hFp1 : 1 ≤ Fp.coeff E'.E := by
    have hmem : E'.f E'.E.genericPoint ∈
        DivisorWithCoeffs.supp (Finsupp.single F (1 : ℤ) : Divisor Y') :=
      DivisorWithCoeffs.mem_supp_iff.mpr ⟨F, by simp [DivisorWithCoeffs.coeff], hE'F⟩
    have hsupp := MMP.Flips.preimage_supp_subset_supp_of_isPullback (hcart _)
      (fun P => by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> norm_num) hFp hmem
    obtain ⟨E'', hE''0, hE''⟩ := DivisorWithCoeffs.mem_supp_iff.mp hsupp
    obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E'' E'.E hE''
    have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hcart _) (V := ⊤)
      (fun P _ => by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> norm_num) hFp E'.E
      ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support E'.E, trivial⟩
    omega
  refine ⟨K', (E'.toDivisorOver.ordPullback ω' : ℝ) - M.coeff E'.E, (Fp.coeff E'.E).toNat,
    ⟨isCanonicalDivisor_divisorOfForm hY' hY's hn' hω'0,
      ⟨1, fun _ => 1, fun _ => K' + S', fun _ => hcart _,
        by simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]; rw [← map_add]; rfl⟩,
      hasNonemptyCenter_valuation E', E', ω', 1, fun _ => 1, fun _ => K' + S', rfl, rfl,
      ⟨⟨hY', inferInstance⟩, hn', hω'0, fun _ => hcart _,
        by simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, map_add, hK'],
        fun _ => M,
        fun _ => ⟨_, hM⟩, by simp⟩⟩, by omega, ?_⟩
  have hcast : (((Fp.coeff E'.E).toNat : ℕ) : ℝ) = (Fp.coeff E'.E : ℝ) := by
    rw [show ((Fp.coeff E'.E).toNat : ℝ) = (((Fp.coeff E'.E).toNat : ℤ) : ℝ) from rfl,
      Int.toNat_of_nonneg (by omega)]
  rw [hcast]
  change (E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * ((L' j).coeff E.E : ℝ) = _
  rw [key, hord, hGeq]
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  push_cast
  ring

/-- **The centre is smooth near its generic point, away from the other boundary components.**
For an irreducible closed `Z` of a scheme locally of finite type over a perfect field and a
divisor `S`, there is an affine open `U` containing the generic point of `Z`, disjoint from the
components of `S` not containing `Z`, on which the reduced subscheme `Z ∩ U` is smooth. -/
private theorem exists_affineOpen_smooth_centre {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [LocallyOfFiniteType sY] (S : Divisor Y)
    (Z : IrreducibleCloseds Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ Z.isIrreducible.genericPoint ∈ U ∧
      (∀ Q ∈ S.support, ¬ (Z : Set Y) ⊆ Q.support → Disjoint (U : Set Y) Q.support) ∧
      IsSmoothScheme ((Scheme.IdealSheafData.vanishingIdeal
        ⟨U.ι ⁻¹' (Z : Set Y), Z.isClosed.preimage U.ι.continuous⟩).subschemeι ≫ U.ι ≫ sY) := by
  classical
  set η := Z.isIrreducible.genericPoint with hη
  have hηZ : IsGenericPoint η (Z : Set Y) :=
    Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed
  set T := Scheme.IdealSheafData.vanishingIdeal (⟨Z, Z.isClosed⟩ : Closeds Y) with hT
  have : IsIntegral T.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ Z.isIrreducible
  have : IsLocallyNoetherian T.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (T.subschemeι ≫ sY)
  have hgen := MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus'
    (f := T.subschemeι ≫ sY)
  set Sm := MMP.Mori.smoothLocus (T.subschemeι ≫ sY)
  have hTsupp : (T.support : Set Y) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hιg : T.subschemeι (genericPoint T.subscheme) = η := by
    have h1 := MMP.Resolution.closure_subschemeι_genericPoint T
    rw [hTsupp] at h1
    exact IsGenericPoint.eq (h := h1) hηZ
  set C : Set Y := T.subschemeι '' (Sm : Set T.subscheme)ᶜ
  have hC : IsClosed C := T.subschemeι.isClosedEmbedding.isClosedMap _ Sm.isOpen.isClosed_compl
  have hηC : η ∉ C := by
    rintro ⟨x, hx, hxη⟩
    rw [← hιg] at hxη
    exact hx (T.subschemeι.isClosedEmbedding.injective hxη ▸ hgen)
  set FS := S.support.filter fun Q => ¬ (Z : Set Y) ⊆ Q.support
  set Bad : Set Y := C ∪ ⋃ Q ∈ FS, (Q.support : Set Y)
  have hBad : IsClosed Bad := hC.union (FS.finite_toSet.isClosed_biUnion fun Q _ =>
    Q.idealSheaf.support.isClosed)
  have hηBad : η ∉ Bad := by
    rintro (h | h)
    · exact hηC h
    · obtain ⟨Q, hQ, hηQ⟩ := Set.mem_iUnion₂.mp h
      refine (Finset.mem_filter.mp hQ).2 ?_
      rw [← hηZ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηQ) Q.idealSheaf.support.isClosed
  obtain ⟨U, hU, hηU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⟨Badᶜ, hBad.isOpen_compl⟩ : Y.Opens)) hηBad
  refine ⟨U, hU, hηU, fun Q hQ hZQ => Set.disjoint_left.mpr fun x hxU hxQ =>
    hUW hxU (Or.inr (Set.mem_iUnion₂.mpr ⟨Q, Finset.mem_filter.mpr ⟨hQ, hZQ⟩, hxQ⟩)), ?_⟩
  have hJ := comap_vanishingIdeal_of_isOpenImmersion U.ι (⟨Z, Z.isClosed⟩ : Closeds Y)
  have : LocallyOfFinitePresentation (T.subschemeι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := T.subschemeι ≫ sY)).mpr
      inferInstance
  refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sY T _ hJ).mpr ?_
  intro z hz
  rw [← smoothLocus_eq_smoothLocus]
  by_contra hzS
  obtain ⟨u, hu⟩ := hz
  have : T.subschemeι z ∈ Bad := Or.inl ⟨z, hzS, rfl⟩
  rw [← hu] at this
  exact hUW u.2 this

/-- The coheight of a closed point of an integral scheme locally of finite type over a field is
the dimension of the scheme. -/
private theorem coheight_eq_of_isClosed {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ} (hn : topologicalKrullDim X = n) {z : X}
    (hz : IsClosed ({z} : Set X)) : (Order.coheight z : WithBot ℕ∞) = n := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX z
  have : Nonempty (IrreducibleCloseds ({z} : Set X)) :=
    ⟨IrreducibleCloseds.closureSingleton (⟨z, rfl⟩ : ({z} : Set X))⟩
  have h0 : topologicalKrullDim ({z} : Set X) = 0 :=
    le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg
  rw [hz.closure_eq, h0, zero_add, hn] at h
  exact h

open Classical in
/-- The coefficients of a sum of distinct prime divisors with coefficient one. -/
private theorem coeff_sum_single {X : Scheme.{u}} {s : ℕ} {B : Fin s → MMP.Mori.PrimeDivisor X}
    (hB : Function.Injective B) (W : MMP.Mori.PrimeDivisor X) :
    (∑ i, Finsupp.single (B i) (1 : ℤ) : Divisor X).coeff W = if W ∈ Set.range B then 1 else 0 := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases h : W ∈ Set.range B
  · rw [ite_eq_left h]
    obtain ⟨i, rfl⟩ := h
    simp [hB.eq_iff]
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h' => h ⟨j, h'⟩

/-- **Adapted coordinates at the closed points of a smooth centre.** Let `X` be a smooth variety
of dimension `n`, `B₁ + ⋯ + B_s` an snc divisor and `Z = V(I)` a smooth irreducible closed
subscheme of codimension `c` contained in every `Bᵢ`. At every closed point `z ∈ Z` there is a
regular system of parameters `x₁, …, xₙ` of `𝒪_{X,z}` with `Bᵢ = (xᵢ = 0)` and
`Z = (x₁ = ⋯ = x_c = 0)`. -/
private theorem exists_adapted_coordinates {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    {n : ℕ} (hn : topologicalKrullDim X = n) (I : X.IdealSheafData)
    (hIsm : IsSmoothScheme (I.subschemeι ≫ sX)) (hirr : IsIrreducible (I.support : Set X))
    {c : ℕ} (hc : (c : ℕ∞) = codimension
      (⟨(I.support : Set X), hirr, I.support.isClosed⟩ : IrreducibleCloseds X))
    {s : ℕ} (B : Fin s → MMP.Mori.PrimeDivisor X) (hB : Function.Injective B)
    (hsnc : IsSNCDivisor sX (∑ i, Finsupp.single (B i) 1))
    (hIB : ∀ i, (I.support : Set X) ⊆ (B i).support) :
    ∀ z ∈ (I.support : Set X), IsClosed ({z} : Set X) →
      ∃ x : Fin n → X.presheaf.stalk z, MMP.Mori.IsRegularSystemOfParameters x ∧
        (∀ i : Fin s, ∃ j : Fin n, (j : ℕ) = i ∧
          IdealSheafData.stalk (B i).idealSheaf z = Ideal.span {x j}) ∧
        IdealSheafData.stalk I z = Ideal.span (x '' {j | (j : ℕ) < c}) := by
  classical
  intro z hzI hz
  have := MMP.Resolution.isIntegral_subscheme_of_isIrreducible sX I hIsm hirr
  obtain ⟨N, z', jj, hz', hjj, hjjE⟩ := hsnc.2.2 z hz
  have hmem : ∀ i, B i ∈ (∑ i, Finsupp.single (B i) (1 : ℤ) : Divisor X).support ∧
      z ∈ (B i).support := fun i => ⟨by
        rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, coeff_sum_single hB,
          ite_eq_left ⟨i, rfl⟩]
        exact one_ne_zero, hIB i hzI⟩
  set j' : Fin s → Fin N := fun i => jj ⟨B i, hmem i⟩
  have hj' : Function.Injective j' := fun i i' h =>
    hB (congrArg Subtype.val (hjj h))
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz'
  obtain ⟨z₀, rfl⟩ : ∃ z₀, I.subschemeι z₀ = z := by
    rw [← I.range_subschemeι] at hzI; exact hzI
  have hker := Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk I z₀
  have : (IdealSheafData.stalk I (I.subschemeι z₀)).IsPrime := by
    rw [← hker]; exact RingHom.ker_isPrime _
  have hreg := MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk sX I hIsm hzI
  have hzI' : ∀ i, z' (j' i) ∈ IdealSheafData.stalk I (I.subschemeι z₀) := by
    intro i
    have hle : (B i).idealSheaf ≤ I := by
      have := (B i).integral
      calc (B i).idealSheaf
          = Scheme.IdealSheafData.vanishingIdeal (B i).idealSheaf.support :=
            Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
        _ ≤ Scheme.IdealSheafData.vanishingIdeal I.support :=
            Scheme.IdealSheafData.vanishingIdeal_antimono fun x hx => hIB i hx
        _ = I := (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl).symm
    refine MMP.Resolution.stalk_le_stalk_of_le hle _ ?_
    rw [hjjE ⟨B i, hmem i⟩]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c', x, hx, -, hheight, hxi, hspan⟩ :=
    exists_isRegularSystemOfParameters_adapted hz' j' hj' _ hreg hzI'
  have hcc : c' = c := by
    have h1 := MMP.Threefold.Resolution.height_ker_stalkMap_subschemeι_eq_codimension I hirr z₀
    rw [hker, hheight, ← hc] at h1
    exact_mod_cast h1
  subst hcc
  have hNn : N = n := by
    have h1 := hz'.2
    rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isClosed sX hn hz] at h1
    exact_mod_cast h1.symm
  subst hNn
  refine ⟨x, hx, fun i => ?_, hspan.symm⟩
  obtain ⟨l, hl, hxl⟩ := hxi i
  exact ⟨l, hl, by rw [hjjE ⟨B i, hmem i⟩, hxl]⟩

open Classical in
/-- **The components through the centre, restricted to an open.** If the open `U` contains the
generic point of `Z` and misses the components of the reduced divisor `S` not containing `Z`, then
`S|_U` is the sum of the distinct prime divisors `Q|_U`, `Q` running over the components of `S`
containing `Z`, and each of them contains `Z ∩ U`. -/
private theorem exists_restrictOpen_eq_sum {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (S : Divisor Y) (hS01 : ∀ E, S.coeff E = 0 ∨ S.coeff E = 1)
    (Z : IrreducibleCloseds Y) (U : Y.Opens) (hηU : Z.isIrreducible.genericPoint ∈ U)
    (hdisj : ∀ Q ∈ S.support, ¬ (Z : Set Y) ⊆ Q.support → Disjoint (U : Set Y) Q.support) :
    ∃ (s : ℕ) (B : Fin s → MMP.Mori.PrimeDivisor U),
      s = (S.support.filter fun Q => (Z : Set Y) ⊆ Q.support).card ∧
      Function.Injective B ∧ S.restrictOpen U = ∑ i, Finsupp.single (B i) 1 ∧
      ∀ i, U.ι ⁻¹' (Z : Set Y) ⊆ (B i).support := by
  set FS := S.support.filter fun Q => (Z : Set Y) ⊆ Q.support with hFS
  set η := Z.isIrreducible.genericPoint
  have hηZ : η ∈ (Z : Set Y) := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hgen : ∀ Q : FS, (Q.1 : MMP.Mori.PrimeDivisor Y).genericPoint ∈ U := by
    intro Q
    have h1 : η ∈ (Q.1 : MMP.Mori.PrimeDivisor Y).support :=
      (Finset.mem_filter.mp Q.2).2 hηZ
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
    exact (specializes_iff_mem_closure.mpr h1).mem_open U.isOpen hηU
  choose BQ hBQ using fun Q : FS => MMP.Threefold.Resolution.exists_primeDivisorMap_eq U Q.1
    (hgen Q)
  let e := FS.equivFin
  have hinj : Function.Injective fun i => BQ (e.symm i) := fun i i' h => by
    have := congrArg (OpenWeilRestriction.primeDivisorMap U.ι) h
    simp only [hBQ] at this
    exact e.symm.injective (Subtype.ext this)
  refine ⟨_, fun i => BQ (e.symm i), rfl, hinj, ?_, fun i u hu => ?_⟩
  · ext W
    rw [DivisorWithCoeffs.coeff_restrictOpen, coeff_sum_single hinj]
    by_cases hW : W ∈ Set.range fun i => BQ (e.symm i)
    · rw [ite_eq_left hW]
      obtain ⟨i, rfl⟩ := hW
      rw [hBQ]
      have hmem := (Finset.mem_filter.mp (e.symm i).2).1
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hmem
      exact (hS01 _).resolve_left hmem
    · rw [ite_eq_right hW]
      by_contra h0
      set Q := OpenWeilRestriction.primeDivisorMap U.ι W
      have hQS : Q ∈ S.support := by
        rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
      have hQZ : (Z : Set Y) ⊆ (Q : MMP.Mori.PrimeDivisor Y).support := by
        by_contra hZQ
        refine Set.disjoint_left.mp (hdisj Q hQS hZQ) (W.genericPoint).2 ?_
        have : (Q : MMP.Mori.PrimeDivisor Y).genericPoint = U.ι W.genericPoint :=
          OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W
        change U.ι W.genericPoint ∈ _
        rw [← this]
        exact MMP.Flips.primeDivisor_genericPoint_mem_support _
      refine hW ⟨e ⟨Q, Finset.mem_filter.mpr ⟨hQS, hQZ⟩⟩, ?_⟩
      apply OpenWeilRestriction.primeDivisorMap_injective U.ι
      simp only [Equiv.symm_apply_apply, hBQ]
      rfl
  · have h1 : U.ι u ∈ ((e.symm i).1 : MMP.Mori.PrimeDivisor Y).support :=
      (Finset.mem_filter.mp (e.symm i).2).2 hu
    rw [← hBQ] at h1
    exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι _ u).mp h1

/-- Pull-backs of finite sums of Cartier divisors. -/
private theorem isPullback_sum {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y)
    (hB : ∀ (D : Divisor Y) (Z : irreducibleComponents X), f (componentGenericPoint X Z) ∉ D.supp)
    {ι : Type*} (t : Finset ι) (D : ι → Divisor Y) (G : ι → Divisor X)
    (hD : ∀ i, (D i).IsCartier) (h : ∀ i, (D i).IsPullback f (hB _) (G i)) :
    (∑ i ∈ t, D i).IsPullback f (hB _) (∑ i ∈ t, G i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Divisor.isPullback_zero (f := f) (hB _)
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add (hD a) (Finset.sum_induction _ Divisor.IsCartier
      (fun _ _ h1 h2 => h1.add h2) (Divisor.isCartier_zero) fun i _ => hD i) (hB _) ih

/-- Adding a member of a regular system of parameters strictly enlarges the ideal. -/
private theorem span_image_lt_span_image_insert {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {n : ℕ} {z : Fin n → R} (hz : IsRegularSystemOfParameters z)
    {J : Finset (Fin n)} {b : Fin n} (hb : b ∉ J) :
    Ideal.span (z '' (J : Set (Fin n))) <
      Ideal.span (z '' ((insert b J : Finset _) : Set (Fin n))) := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  refine lt_of_le_of_ne (Ideal.span_mono (Set.image_mono (by simp))) fun h => ?_
  obtain ⟨_, h1, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  obtain ⟨_, h2, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz (insert b J)
  rw [← h] at h2
  rw [h1, Finset.card_insert_of_notMem hb] at h2
  have hle : (insert b J).card ≤ n := by
    simpa using Finset.card_le_univ (insert b J)
  rw [Finset.card_insert_of_notMem hb] at hle
  have : n - J.card = n - (J.card + 1) := by exact_mod_cast h2
  omega

/-- The prime of `𝒪_{X,x}` cut out by `J` members of a regular system of parameters has coheight
at least `#J`. -/
private theorem card_le_coheight_closure_coordPrime {X : Scheme.{u}} [IsLocallyNoetherian X] {x : X}
    {n : ℕ} {z : Fin n → X.presheaf.stalk x} (hz : IsRegularSystemOfParameters z)
    (J : Finset (Fin n)) :
    (J.card : ℕ∞) ≤ Order.coheight (IrreducibleCloseds.closureSingleton
      (X.fromSpecStalk x (coordPrime hz J))) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert b J hb ih =>
    have hlt : IrreducibleCloseds.closureSingleton (X.fromSpecStalk x (coordPrime hz (insert b J)))
        < IrreducibleCloseds.closureSingleton (X.fromSpecStalk x (coordPrime hz J)) :=
      closure_fromSpecStalk_ssubset (span_image_lt_span_image_insert hz hb)
    have := Order.coheight_add_one_le hlt
    rw [Finset.card_insert_of_notMem hb]
    push_cast
    calc (J.card : ℕ∞) + 1 ≤ _ + 1 := by gcongr
      _ ≤ _ := this

open Classical in
/-- At most `codim Z` components of an snc divisor contain `Z`. -/
private theorem card_le_codimension_of_isSNCDivisor {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [CompactSpace Y]
    {S : Divisor Y} (hS : IsSNCDivisor sY S) (Z : IrreducibleCloseds Y) :
    ((S.support.filter fun Q => (Z : Set Y) ⊆ Q.support).card : ℕ∞) ≤ codimension Z := by
  obtain ⟨p, hpZ, hp⟩ := Z.isClosed.exists_closed_singleton Z.isIrreducible.nonempty
  obtain ⟨n, z, j, hz, hj, hjE⟩ := hS.2.2 p hp
  set F := S.support.filter fun Q => (Z : Set Y) ⊆ Q.support with hF
  have hmem : ∀ Q ∈ F, Q ∈ S.support ∧ p ∈ Q.support := fun Q hQ =>
    ⟨(Finset.mem_filter.1 hQ).1, (Finset.mem_filter.1 hQ).2 hpZ⟩
  let g : F → Fin n := fun Q => j ⟨Q.1, hmem Q.1 Q.2⟩
  have hg : Function.Injective g := fun Q Q' h => by
    have := congrArg Subtype.val (hj h)
    exact Subtype.ext this
  set T : Finset (Fin n) := F.attach.image g
  have hT : T.card = F.card := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_attach]
  have hηp : Z.isIrreducible.genericPoint ⤳ p :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).specializes hpZ
  obtain ⟨q, hq⟩ := exists_fromSpecStalk_eq_of_specializes hηp
  have hle : (coordPrime hz T).asIdeal ≤ q.asIdeal := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hl
    have h1 : Y.fromSpecStalk p q ∈ (Q.1.idealSheaf.support : Set Y) := by
      rw [hq]
      exact (Finset.mem_filter.1 Q.2).2
        (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
    have h2 := (fromSpecStalk_mem_support_iff_stalk_le _ p q).1 h1
    rw [hjE ⟨Q.1, hmem Q.1 Q.2⟩] at h2
    exact h2 (Ideal.subset_span rfl)
  have hZle : Z ≤ IrreducibleCloseds.closureSingleton (Y.fromSpecStalk p (coordPrime hz T)) := by
    intro y hy
    have hcl : (Z : Set Y) = closure {Z.isIrreducible.genericPoint} :=
      (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).symm
    have hy' : y ∈ (Z : Set Y) := hy
    rw [hcl] at hy'
    change y ∈ closure {_}
    refine closure_minimal (Set.singleton_subset_iff.2 ?_) isClosed_closure hy'
    rw [← hq]
    exact (fromSpecStalk_mem_closure_iff p _ q).2 hle
  rw [← hT, codimension_eq_coheight]
  exact (card_le_coheight_closure_coordPrime hz T).trans (Order.coheight_anti hZle)

section Induction

/-- A problem: a smooth variety with a reduced snc divisor and a divisor of its function field with
nonempty center. -/
private structure Prob (k : Type u) [Field k] : Type (u + 1) where
  Y : Scheme.{u}
  sY : Y ⟶ Spec (.of k)
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  [isNormal : IsNormal Y]
  [compactSpace : CompactSpace Y]
  [locallyOfFiniteType : LocallyOfFiniteType sY]
  hY : MMP.Mori.IsVariety k sY
  hsm : IsSmoothScheme sY
  S : Divisor Y
  hS : IsSNCDivisor sY S
  ν : Valuation Y.functionField ℤᵐ⁰
  hν : HasNonemptyCenter k sY ν

attribute [local instance] Prob.isIntegral Prob.isLocallyNoetherian Prob.isNormal Prob.compactSpace
  Prob.locallyOfFiniteType

variable {k : Type u} [Field k]

open Classical in
/-- The conclusion of the bound for a problem. -/
private def Prob.Good [PerfectField k] (P : Prob k) : Prop :=
  ∀ D : ProperDivisorOver k P.sY, D.valuation = P.ν → ∀ {n : ℕ} {K : Divisor P.Y} {b : ℝ},
    IsLogDiscrepancy P.sY n K (Divisor.toRDivisor P.S) P.ν b →
    ∃ m : ℕ, b = m ∧ codimension D.center ≤
      (m + (P.S.support.filter fun Q => (D.center : Set P.Y) ⊆ Q.support).card : ℕ∞)

/-- The centre of `P.ν` has codimension at most one. -/
private def Prob.Shallow (P : Prob k) : Prop :=
  ∃ D : ProperDivisorOver k P.sY, D.valuation = P.ν ∧ codimension D.center ≤ 1

/-- One step of the sequence of blow-ups of the centre of `ν`, in the form of
`hasNonemptyCenter_and_exists_coheight_eq_one_of_blowUp`. -/
private structure Step (P : Prob k) where
  U : P.Y.Opens
  I : (U : Scheme.{u}).IdealSheafData
  target : Prob k
  hY : target.Y = blowUp I
  hs : target.sY = (eqToHom hY ≫ blowUpToBase I ≫ U.ι) ≫ P.sY
  [isDominant : IsDominant (eqToHom hY ≫ blowUpToBase I ≫ U.ι)]
  hν : (target.ν).comap (functionFieldMap (eqToHom hY ≫ blowUpToBase I ≫ U.ι)) = P.ν
  hcen : ∀ D : ProperDivisorOver k P.sY, D.valuation = P.ν →
    (∀ z : P.Y, IsGenericPoint z (D.center : Set P.Y) → z ∈ U) ∧
      I = Scheme.IdealSheafData.vanishingIdeal
        ⟨U.ι ⁻¹' (D.center : Set P.Y), D.center.isClosed.preimage U.ι.continuous⟩ ∧
      IsSmoothScheme (I.subschemeι ≫ U.ι ≫ P.sY)

attribute [local instance] Step.isDominant

open Classical in
/-- The one-step identity along a step: every log discrepancy `b = a_ℓ(ν, Y, S)` is
`b' + (c - s) μ` for a log discrepancy `b' = a_ℓ(ν, Y', S')` on the target, an integer `μ ≥ 1`,
`c` the codimension of the centre and `s ≤ c` the number of components of `S` through it. -/
private def Step.Descends [PerfectField k] {P : Prob k} (st : Step P) : Prop :=
  ∀ D : ProperDivisorOver k P.sY, D.valuation = P.ν →
      ∀ {n : ℕ} {K : Divisor P.Y} {b : ℝ},
      IsLogDiscrepancy P.sY n K (Divisor.toRDivisor P.S) P.ν b →
      ∃ (n' : ℕ) (K' : Divisor st.target.Y) (b' : ℝ) (μ c s : ℕ),
        IsLogDiscrepancy st.target.sY n' K' (Divisor.toRDivisor st.target.S) st.target.ν b' ∧
        1 ≤ μ ∧ codimension D.center = c ∧
        s = (P.S.support.filter fun Q => (D.center : Set P.Y) ⊆ Q.support).card ∧ s ≤ c ∧
        b = b' + ((c : ℝ) - s) * μ

open Classical in
/-- The step of the induction at a problem whose centre has codimension `≥ 2`: the blow-up of the
centre on a suitable open, with the one-step identity
`a_ℓ(ν, Y, S) = a_ℓ(ν, Y', S') + (c - s) ν(F)` and `ν(F) ≥ 1`. -/
private theorem Prob.exists_step_descends [PerfectField k] (P : Prob k)
    (hdeep : ∀ D : ProperDivisorOver k P.sY, D.valuation = P.ν → 2 ≤ codimension D.center) :
    ∃ st : Step P, st.Descends := by
  obtain ⟨D₀, hD₀⟩ := P.hν.2
  set Z := D₀.center with hZ
  set η := Z.isIrreducible.genericPoint with hη
  have hηZ : IsGenericPoint η (Z : Set P.Y) :=
    Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed
  have hcenD : ∀ D : ProperDivisorOver k P.sY, D.valuation = P.ν → D.center = Z := fun D hD =>
    ProperDivisorOver.center_eq_of_valuation_eq P.hY (hD.trans hD₀.symm)
  obtain ⟨U, hUa, hηU, hdisj, hJsm⟩ := exists_affineOpen_smooth_centre P.sY P.S Z
  set J := Scheme.IdealSheafData.vanishingIdeal
    ⟨U.ι ⁻¹' (Z : Set P.Y), Z.isClosed.preimage U.ι.continuous⟩ with hJ
  have : Nonempty U := ⟨⟨η, hηU⟩⟩
  have : IsAffine U := hUa
  have : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  have := P.hY
  -- dimensions
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim P.Y = n := by
    have : Nonempty (IrreducibleCloseds P.Y) := ⟨IrreducibleCloseds.closureSingleton η⟩
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim P.Y := Order.krullDim_nonneg
    have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k P.sY
    induction h : topologicalKrullDim P.Y using WithBot.recBotCoe with
    | bot => rw [h] at h0; exact absurd h0 (by simp)
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h htop
      | coe d => exact ⟨d, rfl⟩
  have hnU : topologicalKrullDim U = n := by
    rw [← hn]
    exact (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k P.Y P.sY _ U.isOpen
      ⟨η, hηU⟩).symm
  have : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  have hUvar : MMP.Mori.IsVariety k (U.ι ≫ P.sY) := {}
  have : Smooth P.sY := MMP.Threefold.Resolution.smooth_of_isSmoothScheme P.hsm
  have hUsm : IsSmoothScheme (U.ι ≫ P.sY) := MMP.Resolution.isSmoothScheme_of_smooth _
  have hJsupp : (J.support : Set U) = U.ι ⁻¹' (Z : Set P.Y) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hηJ : (⟨η, hηU⟩ : (U : Scheme.{u})) ∈ (J.support : Set U) := by
    rw [hJsupp]; exact hηZ.mem
  have hirr : IsIrreducible (J.support : Set U) := by
    rw [hJsupp]
    exact ⟨⟨⟨η, hηU⟩, hηZ.mem⟩, Z.isIrreducible.isPreirreducible.preimage U.ι.isOpenEmbedding⟩
  have hle : ((codimension Z : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [codimension_eq_coheight]
    have := Order.coheight_le_krullDim Z
    exact this.trans (le_of_eq hn)
  have hle' : codimension Z ≤ (n : ℕ∞) := WithBot.coe_le_coe.mp hle
  obtain ⟨c, hcZ⟩ : ∃ c : ℕ, codimension Z = c := by
    induction h : codimension Z using ENat.recTopCoe with
    | top =>
      rw [h, top_le_iff] at hle'
      exact absurd hle' (by exact_mod_cast ENat.natCast_ne_top n)
    | coe d => exact ⟨d, rfl⟩
  have hcJ : (c : ℕ∞) = codimension
      (⟨(J.support : Set U), hirr, J.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [← hcZ, MMP.Flips.codimension_eq_coheight_genericPoint,
      MMP.Flips.codimension_eq_coheight_genericPoint]
    set ηU : (U : Scheme.{u}) := ⟨η, hηU⟩ with hηUdef
    have hcl : closure ({ηU} : Set (U : Scheme.{u})) = U.ι ⁻¹' (Z : Set P.Y) := by
      rw [U.ι.isOpenEmbedding.toIsInducing.closure_eq_preimage_closure_image,
        Set.image_singleton]
      change U.ι ⁻¹' closure {η} = _
      rw [hηZ.def]
    have hgen : IsGenericPoint ηU (J.support : Set U) := by
      unfold IsGenericPoint; rw [hJsupp]; exact hcl
    have h1 := hgen.eq (hirr.isGenericPoint_genericPoint J.support.isClosed)
    rw [← h1, ← coheight_eq_of_isOpenImmersion U.ι]
    rfl
  have hc2 : 2 ≤ c := by
    have := hdeep D₀ hD₀
    rw [← hZ, hcZ] at this
    exact_mod_cast this
  obtain ⟨s, B, hs, hBinj, hSU, hZB⟩ := exists_restrictOpen_eq_sum P.S P.hS.1 Z U hηU hdisj
  have hsncU : IsSNCDivisor (U.ι ≫ P.sY) (∑ i, Finsupp.single (B i) 1) := by
    have := isSNCDivisor_restrictOpen P.sY P.hS U
    rwa [hSU] at this
  have hBsm : ∀ i, IsSmoothScheme ((B i).idealSheaf.subschemeι ≫ U.ι ≫ P.sY) := fun i =>
    hsncU.2.1 (B i) (by
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, coeff_sum_single hBinj,
        ite_eq_left ⟨i, rfl⟩]
      exact one_ne_zero)
  have hsc : s ≤ c := by
    have := card_le_codimension_of_isSNCDivisor P.sY P.hS Z
    rw [hcZ, ← hs] at this
    exact_mod_cast this
  have hcoord := exists_adapted_coordinates (U.ι ≫ P.sY) hnU J hJsm hirr hcJ B hBinj hsncU
    (fun i => hJsupp ▸ hZB i)
  have hsb : IsSmoothBlowup (U.ι ≫ P.sY) J := ⟨hUsm, hJsm⟩
  obtain ⟨hSm', F, hF, hpbB, hsncT⟩ :=
    ResolutionInputs.smooth_blowUp_and_isSNCDivisor_birationalInverseTransform_add_exceptional
      (U.ι ≫ P.sY) hUvar hnU J hsb hirr hcJ hc2 hsc B hBinj hBsm hsncU hcoord
  obtain ⟨hvar', -, hproj, hbir, -, -, F', hF', hform⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (U.ι ≫ P.sY) hUvar hnU J hsb hirr hcJ hc2
  obtain rfl : F = F' := by
    have h := hF.trans hF'.symm
    cases F'; cases F; cases h; rfl
  have hc1 : 1 ≤ codimension
      (⟨(J.support : Set U), hirr, J.support.isClosed⟩ : IrreducibleCloseds U) :=
    hcJ ▸ by exact_mod_cast (by omega : 1 ≤ c)
  set π := blowUpToBase J with hπ
  have := MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension J hirr hc1
  have : IsDominant π := hbir.isDominant
  have : Smooth (π ≫ U.ι ≫ P.sY) := hSm'
  have : IsLocallyNoetherian (blowUp J) := isLocallyNoetherian_of_smooth (π ≫ U.ι ≫ P.sY)
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have : IsNormal (blowUp J) := AlgebraicGeometry.isNormal_of_smooth (π ≫ U.ι ≫ P.sY)
  have := hvar'
  have : CompactSpace (blowUp J) := QuasiCompact.compactSpace_of_compactSpace (π ≫ U.ι ≫ P.sY)
  have : IsProper π := inferInstance
  -- the divisor `D₀` restricted to `U`
  have hcart : ∀ D : Divisor P.Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme P.hsm
  have hcartU : ∀ D : Divisor U, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hUsm
  have hsm' : IsSmoothScheme (π ≫ U.ι ≫ P.sY) := MMP.Resolution.isSmoothScheme_of_smooth _
  have hcart' : ∀ D : Divisor (blowUp J), D.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm'
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme P.sY P.hsm hn
  have hpair : MMP.Mori.IsPairWith P.sY n K₀ (Divisor.toQDivisor P.S) :=
    ⟨⟨P.hY, inferInstance⟩, hK₀, by
      rw [← map_add]; exact QDivisor.isQCartier_toQDivisor (hcart _)⟩
  have hDc : ((D₀.toDivisorOver.center : Set P.Y) ∩ U).Nonempty :=
    ⟨η, by rw [← D₀.center_eq_toDivisorOver_center]; exact hηZ.mem, hηU⟩
  obtain ⟨hYU, hfU, EU', -, hvalU, -⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hpair D₀.toDivisorOver U hDc
  have := D₀.isProper
  let EU : ProperDivisorOver k (U.ι ≫ P.sY) := ⟨⟨_, D₀.f ∣_ U, hYU, hfU, EU'⟩, inferInstance⟩
  have hEU : EU.valuation.comap (functionFieldMap U.ι) = P.ν := hvalU.symm.trans hD₀
  -- a divisor over the blow-up realizing `ν`
  obtain ⟨E', hE'v, -, hb', -, -⟩ :=
    MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hUvar π hvar' hbir EU
  have := E'.isIntegral
  set β := π ≫ U.ι with hβ
  have hβbir : IsBirationalMorphism β := isBirationalMorphism_comp_ι U π hbir
  have : IsDominant β := hβbir.isDominant
  have hβbij := hβbir.functionFieldMap_bijective
  have hνβ : E'.valuation.comap (functionFieldMap β) = P.ν := by
    rw [← hEU, ← hE'v]
    ext t
    change E'.valuation (functionFieldMap β t) = E'.valuation (functionFieldMap π
      (functionFieldMap U.ι t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hE'β : IsBirationalMorphism (E'.f ≫ β) := by
    have := isBirationalMorphism_comp_ι U (E'.f ≫ π) hb'
    rwa [Category.assoc] at this
  have hE'F : E'.f E'.E.genericPoint ∈ F.support := by
    have := E'.isNormal
    have := E'.isLocallyNoetherian
    have := E'.isDominant
    have hnv : IsNormalVariety k ((E'.f ≫ β) ≫ P.sY) := by
      have h := E'.isNormalVariety
      rw [hβ, Category.assoc, Category.assoc]
      exact h
    let Eβ : DivisorOver k P.sY := ⟨E'.Y, E'.f ≫ β, hnv, hE'β, E'.E⟩
    have hv : Eβ.valuation = D₀.toDivisorOver.valuation := by
      change _ = D₀.valuation
      rw [hD₀, ← hνβ]
      ext t
      change E'.E.divisorialValuation (functionFieldMap (E'.f ≫ β) t) =
        E'.E.divisorialValuation (functionFieldMap E'.f (functionFieldMap β t))
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq
      ⟨P.hY, inferInstance⟩ hv
    change E'.f E'.E.genericPoint ∈ (F.idealSheaf.support : Set (blowUp J))
    rw [hF]
    change E'.f E'.E.genericPoint ∈ ((J.comap π).support : Set (blowUp J))
    rw [Scheme.IdealSheafData.support_comap]
    change π (E'.f E'.E.genericPoint) ∈ (J.support : Set U)
    rw [hJsupp]
    change (E'.f ≫ β) E'.E.genericPoint ∈ (Z : Set P.Y)
    erw [hc]
    exact ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support _, rfl⟩
  -- the target problem and the step
  set T := birationalInverseTransform (R := ℤ) π hbir with hT
  let tgt : Prob k :=
    { Y := blowUp J
      sY := π ≫ U.ι ≫ P.sY
      hY := hvar'
      hsm := hsm'
      S := T (∑ i, Finsupp.single (B i) 1) + Finsupp.single F 1
      hS := hsncT
      ν := E'.valuation
      hν := hasNonemptyCenter_valuation E' }
  have hβeq : eqToHom (rfl : tgt.Y = blowUp J) ≫ blowUpToBase J ≫ U.ι = β := by
    rw [eqToHom_refl, Category.id_comp]
  let st : Step P :=
    { U := U
      I := J
      target := tgt
      hY := rfl
      hs := by rw [hβeq]; rfl
      isDominant := by rw [hβeq]; infer_instance
      hν := by
        rw [MMP.Positivity.DivisorOver.functionFieldMap_congr hβeq]
        exact hνβ
      hcen := fun D hD => by
        rw [hcenD D hD]
        exact ⟨fun z hz => (hz.eq hηZ) ▸ hηU, rfl, hJsm⟩ }
  refine ⟨st, fun D hD n' K b hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hb
  obtain rfl : n' = n := by
    have h := ha.1.topologicalKrullDim_eq
    rw [hn] at h
    exact_mod_cast h.symm
  rw [← hνβ] at ha
  have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := P.sY) hn
  have hbijι : Function.Bijective (functionFieldMap U.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary _, trivial⟩
  have hpb : ∀ ω : RationalPluriForms P.sY n' 1, ω ≠ 0 → divisorOfForm ω = K →
      (K + P.S).IsPullback β (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp β _)
        (divisorOfForm (pullbackRationalPluriForms P.sY β ω) +
          (T (∑ i, Finsupp.single (B i) 1) + Finsupp.single F 1) -
          ((c : ℤ) - s) • Finsupp.single F 1) := by
    intro ω hω0 hωK
    set ωU := pullbackRationalPluriForms P.sY U.ι ω with hωU
    have hωU0 : ωU ≠ 0 := pullbackRationalPluriForms_ne_zero U.ι hbijι hdY hω0
    have h1 := isPullback_ι_restrictOpen U (hcart (K + P.S))
    have hres : (K + P.S).restrictOpen U =
        divisorOfForm ωU + ∑ i, Finsupp.single (B i) 1 := by
      rw [← hSU, hωU, divisorOfForm_pullback_ι U hn ω, hωK]
      ext W
      simp [DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.coeff_add]
    rw [hres] at h1
    have h2a : (divisorOfForm ωU).IsPullback π
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp π _)
        (divisorOfForm (pullbackRationalPluriForms (U.ι ≫ P.sY) π ωU) -
          ((c : ℤ) - 1) • Finsupp.single F 1) := by
      have hpp := Divisor.isPullback_pullback (hcartU (divisorOfForm ωU))
        (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant π _)
      convert hpp using 1
      rw [hform ωU hωU0]
      abel
    have h2b : Divisor.IsPullback π (∑ i, Finsupp.single (B i) (1 : ℤ) : Divisor U)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp π _)
        (∑ i, (T (Finsupp.single (B i) 1) + Finsupp.single F 1)) :=
      isPullback_sum π
        (fun D Z => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp π D Z)
        Finset.univ _ _ (fun _ => hcartU _) (fun i => (hpbB i).choose_spec)
    have h2 := h2a.add (hcartU _) (hcartU _)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp π _) h2b
    have h3 := isPullback_comp h1 h2
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp β _)
    have hcomp : pullbackRationalPluriForms (U.ι ≫ P.sY) π ωU =
        pullbackRationalPluriForms P.sY β ω :=
      pullbackRationalPluriForms_comp U.ι π hbijι hbir.functionFieldMap_bijective hdY ω
    have hdiv : divisorOfForm (pullbackRationalPluriForms (U.ι ≫ P.sY) π ωU) =
        divisorOfForm (pullbackRationalPluriForms P.sY β ω) := by
      rw [hcomp]; rfl
    convert h3 using 1
    rw [hdiv, Finset.sum_add_distrib, ← map_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← natCast_zsmul]
    rw [sub_smul, sub_smul, one_smul]
    abel
  obtain ⟨K', a', μ, ha', hμ, haeq⟩ := isDiscrepancy_of_isPullback β (sY' := tgt.sY) rfl hvar'
    hsm' hβbij (MMP.Threefold.Resolution.topologicalKrullDim_blowUp (U.ι ≫ P.sY) J hsb hirr hc1
      hnU) (hcart (K + P.S)) _ F ((c : ℤ) - s) hpb E' hE'β hE'F ha
  refine ⟨n', K', 1 + a', μ, c, s, ⟨a', ha', rfl⟩, hμ, by rw [hcenD D hD, hcZ],
    by rw [hcenD D hD, hs], hsc, ?_⟩
  rw [haeq]
  push_cast
  ring

open Classical in
/-- The arithmetic of the induction step. -/
private theorem Prob.good_of_step [PerfectField k] (P : Prob k) (st : Step P)
    (hst : st.Descends)
    (hT : st.target.Good) : P.Good := by
  intro D hD n K b hb
  obtain ⟨n', K', b', μ, c, s, hb', hμ, hc, hs, hsc, hbeq⟩ := hst D hD hb
  obtain ⟨D', hD'⟩ := st.target.hν.2
  obtain ⟨m', hm', -⟩ := hT D' hD' hb'
  refine ⟨m' + (c - s) * μ, ?_, ?_⟩
  · rw [hbeq, hm']
    push_cast [Nat.cast_sub hsc]
    ring
  · rw [hc, ← hs]
    have : c ≤ m' + (c - s) * μ + s := by
      have : c - s ≤ (c - s) * μ := Nat.le_mul_of_pos_right _ hμ
      omega
    exact_mod_cast this

/-- A problem whose centre has codimension at most one satisfies the bound. -/
private theorem Prob.good_of_shallow [PerfectField k] (P : Prob k) (h : P.Shallow) : P.Good := by
  intro D hD n K b hb
  obtain ⟨D0, hD0, hc0⟩ := h
  have hcen : D.center = D0.center :=
    ProperDivisorOver.center_eq_of_valuation_eq P.hY (hD.trans hD0.symm)
  exact exists_logDiscrepancy_eq_natCast_of_codimension_center_le_one P.sY P.hY P.hS D
    (by rw [hD]; exact hb) (hcen ▸ hc0)

/-- A problem for which the bound fails has a centre of codimension `≥ 2`. -/
private theorem Prob.deep_of_not_good [PerfectField k] {P : Prob k} (h : ¬ P.Good) :
    ∀ D : ProperDivisorOver k P.sY, D.valuation = P.ν → 2 ≤ codimension D.center := by
  intro D hD
  by_contra h2
  exact h (P.good_of_shallow ⟨D, hD, Order.le_of_lt_add_one (not_le.1 h2)⟩)

/-- The step of the induction at a problem for which the bound fails. -/
private noncomputable def badStep [PerfectField k] (P : {P : Prob k // ¬ P.Good}) : Step P.1 :=
  (Prob.exists_step_descends P.1 (Prob.deep_of_not_good P.2)).choose

private theorem not_good_badStep_target [PerfectField k] (P : {P : Prob k // ¬ P.Good}) :
    ¬ (badStep P).target.Good := fun hT =>
  P.2 (Prob.good_of_step P.1 (badStep P)
    (Prob.exists_step_descends P.1 (Prob.deep_of_not_good P.2)).choose_spec hT)

/-- The sequence of blow-ups starting at a problem for which the bound fails. -/
private noncomputable def badChain [PerfectField k] (P₀ : {P : Prob k // ¬ P.Good}) :
    ℕ → {P : Prob k // ¬ P.Good}
  | 0 => P₀
  | r + 1 => ⟨(badStep (badChain P₀ r)).target, not_good_badStep_target (badChain P₀ r)⟩

private theorem Prob.good [PerfectField k] (P₀ : Prob k) : P₀.Good := by
  by_contra h₀
  set C := badChain ⟨P₀, h₀⟩ with hC
  have hY : ∀ r, (C (r + 1)).1.Y = blowUp (badStep (C r)).I := fun r => (badStep (C r)).hY
  have : ∀ r, IsDominant (eqToHom (hY r) ≫ blowUpToBase (badStep (C r)).I ≫
      (badStep (C r)).U.ι) := fun r => (badStep (C r)).isDominant
  have key := hasNonemptyCenter_and_exists_coheight_eq_one_of_blowUp (k := k)
    (fun r => (C r).1.Y) (fun r => (C r).1.sY)
    (fun r => (C r).1.hY) (fun r => (C r).1.hsm) (fun r => (C r).1.ν)
    (C 0).1.hν (fun r => (badStep (C r)).U) (fun r => (badStep (C r)).I)
    hY (fun r => eqToHom (hY r) ≫ blowUpToBase (badStep (C r)).I ≫ (badStep (C r)).U.ι)
    (fun r => rfl) (fun r => (badStep (C r)).hs)
    (fun r => (badStep (C r)).hν) (fun r => (badStep (C r)).hcen)
  obtain ⟨-, r0, D0, hD0, z, hz, hcoh⟩ := key
  refine (C r0).2 ((C r0).1.good_of_shallow ⟨D0, hD0, ?_⟩)
  have hzeq : z = D0.center.isIrreducible.genericPoint :=
    hz.eq (D0.center.isIrreducible.isGenericPoint_genericPoint D0.center.isClosed)
  rw [MMP.Flips.codimension_eq_coheight_genericPoint, ← hzeq, hcoh]

end Induction

open Classical in
/-- **Log discrepancies over a reduced snc divisor.** Let `Y` be a smooth variety over a perfect
field `k`, `S` a (reduced) snc divisor on `Y` and `ν` a divisor over `Y` with center `Z`. Then
every log discrepancy `a_ℓ(ν, Y, S)` is a natural number `k` with `codim_Y Z ≤ k + s`, where
`s` is the number of components of `S` containing `Z`. -/
@[mmp "lem_fa2_snc_reduced_log_discrepancy_bound"]
public theorem exists_logDiscrepancy_eq_natCast_of_isSNCDivisor {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) {S : Divisor Y}
    (hS : IsSNCDivisor sY S) (ν : ProperDivisorOver k sY) {d : ℕ} {K : Divisor Y} {b : ℝ}
    (hb : IsLogDiscrepancy sY d K (Divisor.toRDivisor S) ν.valuation b) :
    ∃ m : ℕ, b = m ∧ codimension ν.center ≤
      (m + (S.support.filter fun P => (ν.center : Set Y) ⊆ P.support).card : ℕ∞) :=
  Prob.good ⟨Y, sY, hY, hsm, S, hS, ν.valuation, hasNonemptyCenter_valuation ν⟩ ν rfl hb

/-! ### The log discrepancy formula over an snc divisor -/

section Formula

/-- A section `g` generating the ideal of a prime divisor `P` on an affine open `U ∋ x` is a
non-unit at `x` exactly when `x ∈ P`. -/
private lemma mem_support_iff_not_isUnit_germ {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X)
    (U : X.affineOpens) (g : Γ(X, U)) (hg : P.idealSheaf.ideal U = Ideal.span {g}) {x : X}
    (hx : x ∈ (U : X.Opens)) :
    x ∈ P.support ↔ ¬ IsUnit (X.presheaf.germ U x hx g) := by
  change x ∈ P.idealSheaf.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, hg, Scheme.mem_zeroLocus_iff,
    ← Scheme.mem_basicOpen X g x hx]
  refine ⟨fun h => h g (Ideal.subset_span rfl), fun h f hf => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rw [Scheme.basicOpen_mul]
  exact fun h' => h h'.2

/-- The algebra map from the local ring at `x` to the function field sends the germ of `g` at
`x` to its germ at the generic point. -/
private lemma algebraMap_germ {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (g : Γ(X, U)) {x : X}
    (hx : x ∈ U) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx g) =
      X.presheaf.germ U (genericPoint X) (((genericPoint_spec X).specializes trivial).mem_open
        U.isOpen hx) g := by
  change (X.presheaf.germ U x hx ≫ X.presheaf.stalkSpecializes _).hom g = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

/-- A reduced divisor `S` and an `ℝ`-divisor `B` supported on `S` satisfy
`S - B = ∑ᵢ (1 - bᵢ) Bᵢ`, the sum running over the components `Bᵢ` of `S` enumerated by `e`. -/
private lemma toRDivisor_sub_eq_sum_smul {X : Scheme.{u}} {S : Divisor X}
    (hS : ∀ P, S.coeff P = 0 ∨ S.coeff P = 1) {B : RDivisor X}
    (hBS : ∀ P, B.coeff P ≠ 0 → P ∈ S.support) {m : ℕ} (e : S.support ≃ Fin m) :
    Divisor.toRDivisor S - B = ∑ j, (1 - B.coeff (e.symm j)) •
      Divisor.toRDivisor (Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor X) 1) := by
  ext Γ
  rw [MMP.Flips.coeff_sum_smul_toRDivisor, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toRDivisor,
    Equiv.sum_comp e.symm (fun P : S.support => (1 - B.coeff P) *
      ((DivisorWithCoeffs.coeff (Finsupp.single (P : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ)),
    Finset.sum_coe_sort S.support (fun P => (1 - B.coeff P) *
      ((DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ)) Γ : ℤ) : ℝ))]
  by_cases hΓ : Γ ∈ S.support
  · rw [Finset.sum_eq_single Γ (fun P _ hP => by
      rw [DivisorWithCoeffs.coeff_single_of_ne hP]; simp) (absurd hΓ),
      DivisorWithCoeffs.coeff_single_self, (hS Γ).resolve_left (Finsupp.mem_support_iff.mp hΓ)]
    simp
  · rw [Finset.sum_eq_zero (fun P hP => by
      rw [DivisorWithCoeffs.coeff_single_of_ne (by rintro rfl; exact hΓ hP)]; simp),
      show S.coeff Γ = 0 from Finsupp.notMem_support_iff.mp hΓ, not_not.mp (mt (hBS Γ) hΓ)]
    simp

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y]

/-- **The order along `ν` of a local equation of a prime divisor.** Let `P` be a prime divisor of
`Y` whose ideal is generated by `g` on an affine open `U` containing the generic point `x` of the
center of a divisor `ν` over `Y`, `φ` the corresponding local equation of `P`, and `M` the
pull-back of `P` to the model of `ν`. Then the coefficient of the divisor of `ν` in `M` is
nonnegative, and it vanishes exactly when `x ∉ P`. -/
private lemma coeff_isPullback_nonneg_and_eq_zero_iff (ν : ProperDivisorOver k sY)
    (P : MMP.Mori.PrimeDivisor Y) (U : Y.affineOpens) (g : Γ(Y, U))
    (φ : (MMP.Mori.RationalFunctions Y)ˣ)
    (hφg : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (U : Y.Opens)),
      (φ : MMP.Mori.RationalFunctions Y) Z = Y.presheaf.germ U _ hZ g)
    (hφ : Divisor.IsLocalEquation (Finsupp.single P 1) U φ)
    (hg : P.idealSheaf.ideal U = Ideal.span {g})
    (hxU : ν.f ν.E.genericPoint ∈ (U : Y.Opens))
    (M : Divisor ν.Y)
    (hM : haveI := ν.isLocallyNoetherian; haveI := ν.isNormal; haveI := ν.isIntegral
      haveI := ν.isDominant
      ∃ hC, MMP.Mori.Divisor.IsPullback (f := ν.f) (Finsupp.single P 1 : Divisor Y) hC M) :
    0 ≤ M.coeff ν.E ∧ (M.coeff ν.E = 0 ↔ ν.f ν.E.genericPoint ∉ P.support) := by
  have := ν.isLocallyNoetherian
  have := ν.isNormal
  have := ν.isIntegral
  have := ν.isDominant
  obtain ⟨_, hM⟩ := hM
  set x := ν.f ν.E.genericPoint with hx
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact ⟨⟨_, rfl⟩⟩
  have hcoef := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM hφ ν.E hxU Z
  set t := algebraMap (Y.presheaf.stalk x) Y.functionField (Y.presheaf.germ U x hxU g) with ht
  have hZU : componentGenericPoint Y Z ∈ (U : Y.Opens) := by
    rw [MMP.Threefold.Mori.CanonUniq.componentGenericPoint_eq]
    exact ((genericPoint_spec Y).specializes trivial).mem_open U.1.isOpen hxU
  have hev : MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions Y) = t := by
    rw [ht, algebraMap_germ]
    unfold MMP.Threefold.Mori.Helpers.evalFF
    simp only [RingHom.comp_apply, MMP.Mori.RationalFunctions.component, Pi.evalRingHom_apply]
    rw [hφg Z hZU]
    change (Y.presheaf.germ U _ hZU ≫ Y.presheaf.stalkSpecializes _).hom g = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have ht0 : t ≠ 0 := by
    rw [← hev]; exact ((φ.isUnit.map _).ne_zero)
  set h := functionFieldMap ν.f t with hh
  have hh0 : h ≠ 0 := (map_ne_zero _).mpr ht0
  rw [hev, ← hh] at hcoef
  have hval : ν.valuation t = WithZero.exp (-ν.Y.ord h ν.E.genericPoint) := by
    rw [← MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord ν.E hh0]
    rfl
  have hle := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one ν.toDivisorOver x rfl
    (Y.presheaf.germ U x hxU g)
  rw [← ht] at hle
  change ν.valuation t ≤ 1 at hle
  rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  rw [hcoef]
  refine ⟨by omega, ?_⟩
  rw [mem_support_iff_not_isUnit_germ P U g hg hxU, not_not]
  constructor
  · intro h0
    by_contra hu
    have hlt := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one ν.toDivisorOver x rfl
      (Y.presheaf.germ U x hxU g) ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    rw [← ht] at hlt
    change ν.valuation t < 1 at hlt
    rw [hval, h0, neg_zero, WithZero.exp_zero] at hlt
    exact lt_irrefl _ hlt
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have hle' := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one ν.toDivisorOver x rfl
      (↑u⁻¹ : Y.presheaf.stalk x)
    change ν.valuation _ ≤ 1 at hle'
    have hmul : ν.valuation t * ν.valuation (algebraMap _ Y.functionField
        (↑u⁻¹ : Y.presheaf.stalk x)) = 1 := by
      rw [← map_mul, ht, ← hu, ← map_mul, Units.mul_inv, map_one, map_one]
    have h1 : 1 ≤ ν.valuation t := hmul ▸ mul_le_of_le_one_right' hle'
    rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The center of `ν` lies in a prime divisor `P` exactly when its generic point does. -/
private lemma center_subset_iff (ν : ProperDivisorOver k sY) (P : MMP.Mori.PrimeDivisor Y) :
    (ν.center : Set Y) ⊆ P.support ↔ ν.f ν.E.genericPoint ∈ P.support := by
  rw [ProperDivisorOver.coe_center]
  constructor
  · intro h
    refine h ⟨_, ?_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  · rintro hx _ ⟨y, hy, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
    exact ((specializes_iff_mem_closure.mpr hy).map ν.f.continuous).mem_closed
      P.idealSheaf.support.isClosed hx

end Formula

/-- A filter of `s` on which `n` never vanishes has at most `∑ i ∈ s, n i` elements. -/
private lemma card_filter_le_sum_of_ne_zero {ι : Type*} {s : Finset ι} {p : ι → Prop}
    [DecidablePred p] {n : ι → ℕ} (h : ∀ i ∈ s, p i → n i ≠ 0) :
    (s.filter p).card ≤ ∑ i ∈ s, n i := by
  rw [Finset.card_eq_sum_ones]
  refine (Finset.sum_le_sum fun i hi => ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  have := h i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  omega

open Classical in
/-- **Log discrepancies over an snc divisor (FA 4.12.1.1).** Let `Y` be a smooth variety over a
perfect field `k`, `S` an snc divisor on `Y` with components `Bᵢ` (the members of `S.support`), and
`B` an `ℝ`-divisor with `Supp B ⊆ Supp S`, so that `B = ∑ bᵢ Bᵢ` with `bᵢ = B.coeff Bᵢ`. Let `ν` be
a divisor over `Y` with center `Z`, and let `b` be a log discrepancy `a_ℓ(ν, Y, B)`. Then there
are `l : ℕ` and `n : PrimeDivisor Y → ℕ` such that
* `b = l + ∑ᵢ nᵢ (1 - bᵢ)`,
* every log discrepancy `a_ℓ(ord_{Bᵢ}, Y, B)` equals `1 - bᵢ`,
* `nᵢ = 0` if and only if `Z ⊄ Bᵢ`,
* `codim_Y Z ≤ l + #{i : Z ⊆ Bᵢ}` and `codim_Y Z ≤ l + ∑ᵢ nᵢ`. -/
@[mmp "lem_fa2_snc_log_discrepancy_formula"]
public theorem exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) {S : Divisor Y}
    (hS : IsSNCDivisor sY S) {B : RDivisor Y} (hBS : ∀ P, B.coeff P ≠ 0 → P ∈ S.support)
    (ν : ProperDivisorOver k sY) {d : ℕ} {K : Divisor Y} {b : ℝ}
    (hb : IsLogDiscrepancy sY d K B ν.valuation b) :
    ∃ (l : ℕ) (n : Mori.PrimeDivisor Y → ℕ),
      b = l + ∑ P ∈ S.support, (n P : ℝ) * (1 - B.coeff P) ∧
      (∀ P ∈ S.support, ∀ c : ℝ,
        IsLogDiscrepancy sY d K B P.divisorialValuation c → c = 1 - B.coeff P) ∧
      (∀ P ∈ S.support, n P = 0 ↔ ¬ (ν.center : Set Y) ⊆ P.support) ∧
      codimension ν.center ≤
        (l + (S.support.filter fun P => (ν.center : Set Y) ⊆ P.support).card : ℕ∞) ∧
      codimension ν.center ≤ (l + ∑ P ∈ S.support, n P : ℕ∞) := by
  have : Smooth sY := MMP.Mori.IsSmoothScheme.smooth hsm
  have : AlgebraicGeometry.IsVariety k sY := hY
  have : IsSmoothVariety k sY := ⟨⟩
  obtain ⟨hcart, hloc, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  have := ν.isLocallyNoetherian
  have := ν.isNormal
  have := ν.isIntegral
  have := ν.isDominant
  have : IsProper ν.f := ν.isProper
  have : CompactSpace ν.Y := QuasiCompact.compactSpace_of_compactSpace ν.f
  choose U hxU g φ hφg hφ hg using fun P => hloc P (ν.f ν.E.genericPoint)
  choose M hM using fun P : MMP.Mori.PrimeDivisor Y =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant ν.f (hcart (Finsupp.single P 1))
  have hn := fun P => coeff_isPullback_nonneg_and_eq_zero_iff ν P (U P) (g P) (φ P) (hφg P)
    (hφ P) (hg P) (hxU P) (M P) ⟨_, hM P⟩
  let n : MMP.Mori.PrimeDivisor Y → ℕ := fun P => ((M P).coeff ν.E).toNat
  have hnM : ∀ P, ((n P : ℕ) : ℤ) = (M P).coeff ν.E := fun P => Int.toNat_of_nonneg (hn P).1
  have hn0 : ∀ P, n P = 0 ↔ ¬ (ν.center : Set Y) ⊆ P.support := fun P => by
    rw [center_subset_iff, ← (hn P).2, ← hnM]
    omega
  obtain ⟨a, ha, rfl⟩ := hb
  let e := S.support.equivFin
  let r : Fin S.support.card → ℝ := fun j => 1 - B.coeff (e.symm j)
  let L : Fin S.support.card → Divisor Y := fun j => Finsupp.single (e.symm j : _) 1
  have hsumFin : ∀ F : MMP.Mori.PrimeDivisor Y → ℝ,
      ∑ j, F (e.symm j) = ∑ P ∈ S.support, F P := fun F => by
    rw [← Finset.sum_coe_sort S.support]
    exact Equiv.sum_comp e.symm (fun P => F P)
  have hpres := toRDivisor_sub_eq_sum_smul hS.1 hBS e
  have hμ : IsMultiplicityAlong sY (Divisor.toRDivisor S - B) r L ν.valuation ν
      (∑ j, r j * (M (e.symm j)).coeff ν.E) :=
    ⟨⟨hY, inferInstance⟩, ha.2.2.1, rfl, fun j => hcart _, hpres, fun j => M (e.symm j),
      fun j => ⟨_, hM _⟩, rfl⟩
  have hlog : IsLogDiscrepancy sY d K (Divisor.toRDivisor S) ν.valuation
      (1 + a - ∑ j, r j * (M (e.symm j)).coeff ν.E) :=
    ⟨_, IsDiscrepancy.sub_of_isMultiplicityAlong ha hμ, by ring⟩
  obtain ⟨l, hl, hcod⟩ :=
    MMP.Flips.exists_logDiscrepancy_eq_natCast_of_isSNCDivisor sY hY hsm hS ν hlog
  have hμn : ∑ j, r j * ((M (e.symm j)).coeff ν.E : ℝ) =
      ∑ P ∈ S.support, (n P : ℝ) * (1 - B.coeff P) := by
    rw [← hsumFin (fun P => (n P : ℝ) * (1 - B.coeff P))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hnM]
    push_cast
    ring
  refine ⟨l, n, by linarith, ?_, fun P _ => hn0 P, hcod, ?_⟩
  · rintro P - c ⟨a', ha', rfl⟩
    rw [IsDiscrepancy.eq_neg_coeff ha']
    ring
  · exact hcod.trans (by exact_mod_cast Nat.add_le_add_left (card_filter_le_sum_of_ne_zero
      fun P _ hP => (hn0 P).not.mpr (not_not.mpr hP)) l)

/-! ### Centers of divisors with small log discrepancy -/

/-- Dropping the summands outside `U` and the multiplicities `nᵢ ≥ 1` on `U` only lowers a sum
`∑ nᵢ cᵢ` of nonnegative terms. -/
private lemma sum_le_sum_natCast_mul {ι : Type*} {s U : Finset ι} (hU : U ⊆ s) {c : ι → ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) {n : ι → ℕ} (hn : ∀ i ∈ U, n i ≠ 0) :
    ∑ i ∈ U, c i ≤ ∑ i ∈ s, (n i : ℝ) * c i :=
  calc ∑ i ∈ U, c i ≤ ∑ i ∈ U, (n i : ℝ) * c i := Finset.sum_le_sum fun i hi =>
        le_mul_of_one_le_left (hc i (hU hi)) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (hn i hi))
    _ ≤ ∑ i ∈ s, (n i : ℝ) * c i := Finset.sum_le_sum_of_subset_of_nonneg hU fun i hi _ =>
        mul_nonneg (Nat.cast_nonneg _) (hc i hi)

/-- **Small log discrepancies over an snc boundary (FA 4.12.1.3).** Let `Y` be a smooth variety
over a perfect field `k`, `S` an snc divisor on `Y` with components `Bᵢ` (the members of
`S.support`), and `B` an `ℝ`-divisor with `Supp B ⊆ Supp S`, `bᵢ = B.coeff Bᵢ ≤ 1` for all `i`, and
`(1 - bᵢ) + (1 - bⱼ) ≥ 2` whenever `Bᵢ ≠ Bⱼ` meet. Let `ν` be a divisor over `Y` whose center `W`
has codimension at least `2`, and let `b < 2` be a log discrepancy `a_ℓ(ν, Y, B)`. Then
`codim_Y W = 2`, and there is a unique component `B_{i₀}` containing `W`; moreover `b_{i₀} > 0`
and `2 - b_{i₀} ≤ b`. -/
@[mmp "lem_fa2_snc_small_log_discrepancy_center"]
public theorem codimension_center_eq_two_of_logDiscrepancy_lt_two {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) {S : Divisor Y}
    (hS : IsSNCDivisor sY S) {B : RDivisor Y} (hBS : ∀ P, B.coeff P ≠ 0 → P ∈ S.support)
    (hb1 : ∀ P ∈ S.support, B.coeff P ≤ 1)
    (hpair : ∀ P ∈ S.support, ∀ Q ∈ S.support, P ≠ Q →
      ((P.support : Set Y) ∩ Q.support).Nonempty → 2 ≤ (1 - B.coeff P) + (1 - B.coeff Q))
    (ν : ProperDivisorOver k sY) (hcodim : 2 ≤ codimension ν.center)
    {d : ℕ} {K : Divisor Y} {b : ℝ} (hb : IsLogDiscrepancy sY d K B ν.valuation b)
    (hlt : b < 2) :
    codimension ν.center = 2 ∧
      ∃ P ∈ S.support, (ν.center : Set Y) ⊆ P.support ∧
        (∀ Q ∈ S.support, (ν.center : Set Y) ⊆ Q.support → Q = P) ∧
        0 < B.coeff P ∧ 2 - B.coeff P ≤ b := by
  classical
  obtain ⟨l, n, rfl, -, hn, hc, -⟩ :=
    exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor sY hY hsm hS hBS ν hb
  set T := S.support.filter fun P => (ν.center : Set Y) ⊆ P.support
  have hTS : T ⊆ S.support := Finset.filter_subset _ _
  -- `a_ℓ ≥ l + ∑_{P ∈ U} (1 - b_P)` for every set `U` of components through the center
  have key : ∀ U ⊆ T, (l : ℝ) + ∑ P ∈ U, (1 - B.coeff P) ≤
      l + ∑ P ∈ S.support, (n P : ℝ) * (1 - B.coeff P) := fun U hU =>
    add_le_add_right (sum_le_sum_natCast_mul (hU.trans hTS) (fun P hP => sub_nonneg.2 (hb1 P hP))
      fun P hP h0 => (hn P (hTS (hU hP))).1 h0 (Finset.mem_filter.1 (hU hP)).2) _
  have h2 : 2 ≤ l + T.card := by exact_mod_cast hcodim.trans hc
  obtain h | h | h : T.card = 0 ∨ T.card = 1 ∨ 2 ≤ T.card := by omega
  · -- no component contains the center: `a_ℓ ≥ l ≥ 2`
    have := key ∅ (Finset.empty_subset _)
    simp only [Finset.sum_empty, add_zero] at this
    have : (2 : ℝ) ≤ l := by exact_mod_cast (h ▸ h2 : 2 ≤ l + 0)
    linarith
  · -- exactly one component `P` contains the center
    obtain ⟨P, hTP⟩ := Finset.card_eq_one.1 h
    have hPT : P ∈ T := hTP ▸ Finset.mem_singleton_self P
    obtain ⟨hPS, hWP⟩ := Finset.mem_filter.1 hPT
    have hbP := key {P} (hTP ▸ subset_rfl)
    rw [Finset.sum_singleton] at hbP
    have hl : l = 1 := by
      have : (l : ℝ) < 2 := by linarith [sub_nonneg.2 (hb1 P hPS)]
      have : l < 2 := by exact_mod_cast this
      omega
    subst hl
    refine ⟨le_antisymm (by simpa [h, one_add_one_eq_two] using hc) hcodim, P, hPS, hWP,
      fun Q hQ hWQ => Finset.mem_singleton.1 (hTP ▸ Finset.mem_filter.2 ⟨hQ, hWQ⟩), ?_, ?_⟩ <;>
    · push_cast at hbP hlt ⊢; linarith
  · -- two components `P ≠ Q` contain the center, so they meet: `a_ℓ ≥ 2`
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := Finset.one_lt_card.1 h
    obtain ⟨hPS, hWP⟩ := Finset.mem_filter.1 hP
    obtain ⟨hQS, hWQ⟩ := Finset.mem_filter.1 hQ
    obtain ⟨x, hx⟩ := ν.center.isIrreducible.nonempty
    have := key {P, Q} (Finset.insert_subset hP (Finset.singleton_subset_iff.2 hQ))
    rw [Finset.sum_pair hPQ] at this
    linarith [hpair P hPS Q hQS hPQ ⟨x, hWP hx, hWQ hx⟩, (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]

end MMP.Flips

/-! ### The blowup package -/

namespace MMP

open AlgebraicGeometry CategoryTheory

/-- An ideal sheaf on an open subscheme `U` of `X` is the restriction of the kernel of the
composite `Z₀ ⟶ U ⟶ X`, when this composite is quasi-compact. -/
private lemma comap_ker_subschemeι_comp_ι {X : Scheme.{0}} (U : X.Opens)
    (J₀ : (U : Scheme.{0}).IdealSheafData) [QuasiCompact (J₀.subschemeι ≫ U.ι)] :
    (J₀.subschemeι ≫ U.ι).ker.comap U.ι = J₀ := by
  have hpb : IsPullback J₀.subschemeι (𝟙 _) U.ι (J₀.subschemeι ≫ U.ι) := by
    simpa using (IsPullback.of_vert_isIso (fst := J₀.subschemeι) (snd := 𝟙 _) (f := 𝟙 _)
      (g := J₀.subschemeι) ⟨by simp⟩).paste_horiz (IsKernelPair.id_of_mono U.ι)
  refine Scheme.IdealSheafData.ext (funext fun W ↦ ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    ← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _ hpb,
    Scheme.IdealSheafData.ker_subschemeι]

/-- A birational morphism of integral schemes in the sense of `AlgebraicGeometry.IsBirational`,
locally of finite type, is birational in the sense of `MMP.Mori.IsBirationalMorphism`. -/
private lemma isBirationalMorphism_of_isBirational {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    Mori.IsBirationalMorphism f := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _ |>.to_subtype
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _ |>.to_subtype
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- **The blowup package for varieties.** Let `X` be a complex variety and `J ≠ ⊥` an ideal
sheaf on `X`. Then: (1) every `g : Y ⟶ X` with `J.comap g` effective Cartier factors uniquely
through `blowUpToBase J`; (2) for an integral closed subscheme `j : V ⟶ X` with
`V ⊄ V(J)`, the canonical lift `MMP.Resolution.canonicalLift j J : blowUp (J.comap j) ⟶ blowUp J`
is a closed immersion over `j` whose image is the closure of `π⁻¹(V ∖ V(J))`, with the reduced
structure; (3) if `X` is quasi-projective, every projective birational `p : T ⟶ X` from a
variety is isomorphic over `X` to `blowUpToBase J'` for some `J' ≠ ⊥`; (4) every ideal sheaf on
an open `U ⊆ X` is the restriction of one on `X`; (5) every proper birational `p : T ⟶ X` from a
variety is dominated by a proper birational `q : T₁ ⟶ T` from a variety with `q ≫ p`
projective. -/
@[mmp "lem_mmp_foundation_fa17_full_blowup_ideal_package"]
public theorem blowUp_universal_strictTransform_presentation_extension_chow
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsVariety ℂ sX]
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) :
    -- (1) universal property
    (∀ {Y : Scheme.{0}} (g : Y ⟶ X), Stacks.Divisors.IsEffectiveCartierDivisor (J.comap g) →
      ∃! h : Y ⟶ blowUp J, h ≫ blowUpToBase J = g) ∧
    -- (2) strict transforms
    (∀ {V : Scheme.{0}} (j : V ⟶ X) [IsClosedImmersion j] [IsIntegral V],
      ¬ Set.range j ⊆ (J.support : Set X) →
        IsClosedImmersion (MMP.Resolution.canonicalLift j J) ∧
        MMP.Resolution.canonicalLift j J ≫ blowUpToBase J = blowUpToBase (J.comap j) ≫ j ∧
        Set.range (MMP.Resolution.canonicalLift j J) =
          closure (blowUpToBase J ⁻¹' (Set.range j \ (J.support : Set X))) ∧
        (MMP.Resolution.canonicalLift j J).ker = Scheme.IdealSheafData.vanishingIdeal
          (.closure (blowUpToBase J ⁻¹' (Set.range j \ (J.support : Set X))))) ∧
    -- (3) projective birational morphisms onto a quasi-projective `X` are blowups
    (IsQuasiProjectiveVariety ℂ sX → ∀ {T : Scheme.{0}} (p : T ⟶ X), IsVariety ℂ (p ≫ sX) →
      IsProjectiveMorphism p → Mori.IsBirationalMorphism p →
        ∃ J' : X.IdealSheafData, J' ≠ ⊥ ∧
          ∃ e : T ≅ blowUp J', e.hom ≫ blowUpToBase J' = p) ∧
    -- (4) extension of ideal sheaves from an open subscheme
    (∀ (U : X.Opens) (J₀ : (U : Scheme.{0}).IdealSheafData),
      ∃ J₁ : X.IdealSheafData, J₁.comap U.ι = J₀) ∧
    -- (5) Chow's lemma
    (∀ {T : Scheme.{0}} (p : T ⟶ X), IsVariety ℂ (p ≫ sX) → IsProper p →
      Mori.IsBirationalMorphism p →
        ∃ (T₁ : Scheme.{0}) (q : T₁ ⟶ T), IsVariety ℂ (q ≫ p ≫ sX) ∧ IsProper q ∧
          Mori.IsBirationalMorphism q ∧ IsProjectiveMorphism (q ≫ p)) := by
  refine ⟨fun g hg ↦ ⟨blowUpLift J g hg, blowUpLift_comp J g hg,
      fun h hh ↦ blowUpLift_unique J g hg h hh⟩, ?_, ?_, ?_, ?_⟩
  · intro V j _ _ hV
    exact ⟨Resolution.Bridges.isClosedImmersion_canonicalLift j J,
      Resolution.canonicalLift_comp_blowUpToBase j J,
      Resolution.Bridges.range_canonicalLift_eq_closure_and_ker_eq_vanishingIdeal j J hV⟩
  · intro hqp T p hT hp hb
    have : IsIntegral T := IsVariety.toIsIntegral (k := ℂ) (f := p ≫ sX)
    obtain ⟨J', hJ', -, e, he⟩ := exists_blowUp_iso_of_isProjective_of_isBirational sX p
      hp.isProjective (Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
    exact ⟨J', hJ', e, he⟩
  · intro U J₀
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    exact ⟨_, comap_ker_subschemeι_comp_ι U J₀⟩
  · intro T p hT _ _
    obtain ⟨T₁, q, hT₁, hq, -, hqb, hqp⟩ :=
      (Resolution.Bridges.exists_isProjectiveMorphism_isBirational_chowModification ℂ).1
        hT inferInstance p rfl inferInstance
    have hqP : IsProper q := hq.isProjective.isProper
    have : IsIntegral T₁ := IsVariety.toIsIntegral (k := ℂ) (f := q ≫ p ≫ sX)
    have : IsIntegral T := IsVariety.toIsIntegral (k := ℂ) (f := p ≫ sX)
    exact ⟨T₁, q, hT₁, hqP, isBirationalMorphism_of_isBirational q hqb, hqp⟩

end MMP
