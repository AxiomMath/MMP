module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainLabel
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence

/-!
# Exceptional valuations and boundaries along a stabilized small klt tail

This file collects four comparisons of divisors and valuations across the step diagrams
`(X⁻, B⁻) → Z ← (X⁺, B⁺)` of a stabilized small klt tail of fourfolds and its terminal chains.

Two small morphisms `f : X ⟶ Z`, `f' : X' ⟶ Z` of normal varieties identify `k(X)` and `k(X')`
through `k(Z)`, and a valuation is exceptional over `X` exactly when the corresponding
valuation is exceptional over `X'`: for either morphism, a normalized divisorial valuation has
a prime divisor as its centre on the source exactly when its centre on `Z` is a prime divisor.
In a step diagram `f⁺` is always small, so when `f⁻` is small too, `X⁻` and `X⁺` have the same
exceptional valuations. When `f⁻` is not small, its exceptional locus contains a prime divisor
`E` of `X⁻` whose image in `Z` has codimension at least two, and `ord_E` is exceptional over
`X⁺`.

Let `p_i : Y_i ⟶ X_i` be a crepant junction of the tail extracting the stable set `I_∞`, with
decreased boundary `Θ_i'`, and let `q : W ⟶ Y_i`, `r : W ⟶ X_{i+1}` be birational morphisms
from a smooth projective variety, compatible with `(f_i⁺)⁻¹ ∘ f_i ∘ p_i`. Then
`E = q^*(K_{Y_i} + Θ_i') - r^*(K_{X_{i+1}} + B_{i+1})` is `r`-exceptional. At a prime `P_W`
of `W` with `r_* P_W = P₁` a prime divisor of `X_{i+1}`, every morphism of the diagram is a
local isomorphism at the generic points over `f_i⁺(P₁)`, so the coefficients of the two
pull-backs at `P_W` agree.

Finally, for a terminal chain with labels `S_h`, the boundary of every model `(M, Θ^M)` is
carried by the centres of the labels with the label coefficients: `Θ^M = ∑_h b_h^M S_h^M`.

## Main results

* `MMP.Fourfold.IsSmallMorphism.isExceptionalValuation_iff`: valuations of `k(X)` and `k(X')`
  agreeing on `k(Z)` are exceptional over `X` and over `X'` together.
* `MMP.Fourfold.IsFourfoldStepDiagram.exists_isExceptionalValuation_of_not_isSmallMorphism`:
  if `f⁻` is not small, some prime divisor `E` of `X⁻` has `ord_E` exceptional over `X⁺`.
* `MMP.Fourfold.StabilizedSmallKltTail.transformDivisor_sub_eq_zero_of_isDecreasedBoundary`:
  `r_*(q^*(K_{Y_i} + Θ_i') - r^*(K_{X_{i+1}} + B_{i+1})) = 0`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.coeff_modelBoundary_eq_finsum`: the
  coefficient of `Θ^M` at a prime divisor `P` of `M` is the sum of the label coefficients
  `b_h^M` over the labels `S_h` with `S_h^M = P`.

## Implementation notes

* A valuation of the common function field `k(Z)` is represented on `X` and on `X'` by a
  valuation of `k(X)` or `k(X')` whose restriction along `functionFieldMap` is that valuation,
  as in `MMP.Fourfold.valuationsOver`; `ord_E` is `MMP.Mori.PrimeDivisor.valuationOver E f⁻`.
* The compatibility `r = (f_i⁺)⁻¹ ∘ f_i ∘ p_i ∘ q` is stated as `q ≫ p_i ≫ f_i = r ≫ f_i⁺`. The
  canonical divisors are chosen compatibly, all cut out by one rational top form: a divisor
  `K_W` of `W` with `q_* K_W = K_{Y_i}` and `r_* K_W = K_{X_{i+1}}`. Without such a choice the
  identity, an equality of divisors rather than of classes, does not hold. The pull-backs are
  `ℝ`-divisors characterised by `MMP.Flips.IsRCartierPullback`.
* The centre `S_h^M` is a relation
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`) and the label coefficient
  a predicate (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCoefficient`), so
  `Θ^M = ∑_h b_h^M S_h^M` is stated coefficientwise, for any family `b` of label coefficients.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Divisors over a proper model -/

/-- Valuations agreeing after restriction along a bijective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L : Type*} [Field K] [Field L] {σ : K →+* L}
    (hσ : Function.Bijective σ) {v w : Valuation L (WithZero (Multiplicative ℤ))}
    (h : v.comap σ = w.comap σ) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hσ.2 t
    exact congrArg (fun u => u s) h

/-- A valuation `ξ'` of `k(X')` restricting on `k(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `k(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `k(X') ≅ k(Z) ≅ k(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq {X X' Z : Scheme.{u}}
    {k : Type u} [Field k] [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of k)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (D : MMP.Mori.DivisorOver k (g ≫ sZ))
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField k (g' ≫ sZ) ξ' := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hY : MMP.Mori.IsNormalVariety k ((D.f ≫ g) ≫ sZ) := by
    rw [Category.assoc]; exact D.isNormalVariety
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  let := MMP.Mori.functionFieldAlgebra sZ
  let := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  let := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) =
    D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {X X' Z : Scheme.{u}}
    {k : Type u} [Field k] [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] (hgp' : IsProper g')
    (D : MMP.Mori.DivisorOver k sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ x : X', (∀ a : X'.presheaf.stalk x, ξ' (algebraMap _ X'.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
        ξ' (algebraMap _ X'.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  set z := g y
  have hw : ∀ b : Z.presheaf.stalk z,
      ξ' (functionFieldMap g' (algebraMap _ Z.functionField b)) =
        D.valuation (algebraMap _ X.functionField ((g.stalkMap y).hom b)) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ Z.functionField b)) h
    simp only [Valuation.comap_apply] at this
    rw [this, functionFieldMap_algebraMap_stalk g y b]
  let R := ξ'.valuationSubring
  let φ : Z.presheaf.stalk z →+* R :=
    ((functionFieldMap g').comp (algebraMap (Z.presheaf.stalk z) Z.functionField)).codRestrict R
      fun b => (ξ'.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hex : ValuativeCriterion.Existence g' := by
    have h : @IsProper _ _ g' := hgp'
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g' :=
    { R := R
      K := X'.functionField
      i₁ := X'.fromSpecStalk (genericPoint X')
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk g',
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X'.functionField)) ≫ l =
      X'.fromSpecStalk (genericPoint X') := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X' ⤳ x := (genericPoint_spec X').specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R X'.functionField) =
      X'.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X'.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : X'.presheaf.stalk x,
      algebraMap _ X'.functionField a = ((f.hom a : R) : X'.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- Over a proper birational model `X' ⟶ Z`, a valuation `ξ'` of `k(X')` restricting on `k(Z)`
to the valuation of a divisor over another model `X ⟶ Z` is realized by a proper divisor over
`X'`. -/
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq {X X' Z : Scheme.{u}}
    {k : Type u} [Field k] [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    (hX' : MMP.Mori.IsNormalVariety k sX') (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g]
    [IsDominant g'] (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (hgp' : IsProper g') (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX')
    (D : MMP.Mori.DivisorOver k sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : MMP.Mori.DivisorOver k sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' hgp' D ξ' h
  have : AlgebraicGeometry.IsVariety k sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField k sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

/-- The divisor over `W` attached to a prime divisor `R` of `W` has valuation `ord_R`. -/
private theorem valuation_ofPrimeDivisor {k : Type u} [Field k] {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)}
    (hW : MMP.Mori.IsNormalVariety k sW) (R : MMP.Mori.PrimeDivisor W) :
    (MMP.Mori.DivisorOver.ofPrimeDivisor k hW R).valuation = R.divisorialValuation := by
  ext g
  change R.divisorialValuation (functionFieldMap (𝟙 W) g) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

/-! ### Small morphisms -/

section SmallMorphism

variable {k : Type u} [Field k] {X X' Z : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  {f : X ⟶ Z} {f' : X' ⟶ Z}

/-- **Prime divisors correspond across small morphisms.** If `f : X ⟶ Z` and `f' : X' ⟶ Z` are
small, the image in `Z` of the generic point of a prime divisor `P'` of `X'` is the generic point
of a prime divisor `Q` of `Z`, and so is the image of the generic point of some prime divisor `P`
of `X`. Smallness of `f'` puts `η_{P'}` in the biregular locus, so `f' η_{P'}` has coheight one;
smallness of `f` puts that point in the biregular locus of `f`, where the surjective `f` has a
coheight-one preimage. -/
private theorem exists_primeDivisor_map_genericPoint_eq
    (hf : IsSmallMorphism sX sZ f) (hf' : IsSmallMorphism sX' sZ f')
    (P' : MMP.Mori.PrimeDivisor X') :
    ∃ (Q : MMP.Mori.PrimeDivisor Z) (P : MMP.Mori.PrimeDivisor X),
      f P.genericPoint = Q.genericPoint ∧ f' P'.genericPoint = Q.genericPoint := by
  have := hf.isNormalVariety_target.1.toIsIntegral
  have := hf.isBirationalMorphism.isDominant
  have : IsNormal Z := hf.isNormalVariety_target.2
  have : IsLocallyNoetherian Z :=
    have := hf.isNormalVariety_target.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sZ
  have := hf.isProper
  have := hf'.isProper
  have hP'm : f' P'.genericPoint ∈ biregularLocus f' := by
    by_contra hn
    have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hf'.two_le_codimension
      (show P'.genericPoint ∈ exceptionalSet f' from hn)
    rw [P'.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hz : Order.coheight (f' P'.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f' hP'm, P'.coheight_genericPoint]
  have hQp : f' P'.genericPoint ∈ biregularLocus f :=
    MMP.Positivity.mem_biregularLocus_of_coheight_le_one f
      hf.isBirationalMorphism.functionFieldMap_bijective hf.two_le_codimension hz.le
  have hsurj : Function.Surjective f := by
    refine Set.range_eq_univ.1 ?_
    rw [← f.isClosedMap.isClosed_range.closure_eq, f.denseRange.closure_eq]
  obtain ⟨x, hx⟩ := hsurj (f' P'.genericPoint)
  have hxc : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hx ▸ hQp), hx, hz]
  refine ⟨.ofCoheightOne _ hz, .ofCoheightOne _ hxc, ?_, ?_⟩ <;>
    simp only [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hx]

/-- If `v'` is the valuation of a prime divisor of `X'`, then `v` is that of a prime divisor
of `X`: both restrict on `k(Z)` to `ord_Q` for a prime divisor `Q` of `Z`. -/
private theorem exists_primeDivisor_valuation_eq
    (hf : IsSmallMorphism sX sZ f) (hf' : IsSmallMorphism sX' sZ f')
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation X'.functionField (WithZero (Multiplicative ℤ))}
    (hv : haveI := hf.isNormalVariety_target.1.toIsIntegral
      haveI := hf.isBirationalMorphism.isDominant
      haveI := hf'.isBirationalMorphism.isDominant
      v.comap (functionFieldMap f) = v'.comap (functionFieldMap f'))
    (P' : MMP.Mori.PrimeDivisor X')
    (hP' : v' = (MMP.Mori.DivisorOver.ofPrimeDivisor k hf'.isNormalVariety_source P').valuation) :
    ∃ P : MMP.Mori.PrimeDivisor X,
      v = (MMP.Mori.DivisorOver.ofPrimeDivisor k hf.isNormalVariety_source P).valuation := by
  have := hf.isNormalVariety_target.1.toIsIntegral
  have := hf.isBirationalMorphism.isDominant
  have := hf'.isBirationalMorphism.isDominant
  have : IsNormal Z := hf.isNormalVariety_target.2
  have : IsLocallyNoetherian Z :=
    have := hf.isNormalVariety_target.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨Q, P, hP, hQ⟩ := exists_primeDivisor_map_genericPoint_eq hf hf' P'
  refine ⟨P, valuation_eq_of_comap_eq hf.isBirationalMorphism.functionFieldMap_bijective ?_⟩
  rw [hv, hP', valuation_ofPrimeDivisor, valuation_ofPrimeDivisor]
  exact (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hf.isNormalVariety_target
    ⟨X', f', hf'.comp_eq ▸ hf'.isNormalVariety_source, hf'.isBirationalMorphism, P'⟩ Q hQ).trans
    (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hf.isNormalVariety_target
      ⟨X, f, hf.comp_eq ▸ hf.isNormalVariety_source, hf.isBirationalMorphism, P⟩ Q hP).symm

/-- One implication of `IsSmallMorphism.isExceptionalValuation_iff`: exceptionality over `X`
passes to `X'`. -/
private theorem isExceptionalValuation_of
    (hf : IsSmallMorphism sX sZ f) (hf' : IsSmallMorphism sX' sZ f')
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation X'.functionField (WithZero (Multiplicative ℤ))}
    (hv : haveI := hf.isNormalVariety_target.1.toIsIntegral
      haveI := hf.isBirationalMorphism.isDominant
      haveI := hf'.isBirationalMorphism.isDominant
      v.comap (functionFieldMap f) = v'.comap (functionFieldMap f'))
    (h : MMP.Intersection.IsExceptionalValuation k sX v) :
    MMP.Intersection.IsExceptionalValuation k sX' v' := by
  have := hf.isNormalVariety_target.1.toIsIntegral
  have := hf.isBirationalMorphism.isDominant
  have := hf'.isBirationalMorphism.isDominant
  obtain ⟨D, -, rfl, h2⟩ := h
  obtain ⟨D', hD', rfl⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq
    hf'.isNormalVariety_source f f' hf.isBirationalMorphism hf'.isBirationalMorphism
    hf'.isProper hf.comp_eq hf'.comp_eq D v' hv.symm
  refine ⟨D', hD', rfl, (MMP.Positivity.DivisorOver.two_le_codimension_center_iff
    hf'.isNormalVariety_source D').2 fun P' hP' => ?_⟩
  obtain ⟨P, hP⟩ := exists_primeDivisor_valuation_eq hf hf' hv P' hP'
  exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff
    hf.isNormalVariety_source D).1 h2 P hP

/-- Let `f : X ⟶ Z` and `f' : X' ⟶ Z` be small morphisms. A valuation `v` of `k(X)` and a
valuation `v'` of `k(X')` with the same restriction to `k(Z)` are either both exceptional, `v`
over `X` and `v'` over `X'`, or both not. -/
@[mmp "lem_oai4_c1_small_step_same_exceptional"]
public theorem IsSmallMorphism.isExceptionalValuation_iff
    (hf : IsSmallMorphism sX sZ f) (hf' : IsSmallMorphism sX' sZ f')
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation X'.functionField (WithZero (Multiplicative ℤ))}
    (hv : haveI := hf.isNormalVariety_target.1.toIsIntegral
      haveI := hf.isBirationalMorphism.isDominant
      haveI := hf'.isBirationalMorphism.isDominant
      v.comap (functionFieldMap f) = v'.comap (functionFieldMap f')) :
    MMP.Intersection.IsExceptionalValuation k sX v ↔
      MMP.Intersection.IsExceptionalValuation k sX' v' :=
  ⟨isExceptionalValuation_of hf hf' hv, isExceptionalValuation_of hf' hf hv.symm⟩

end SmallMorphism

/-! ### Step diagrams with a non-small `f⁻` -/

section NotSmall

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- Over a point `y` of codimension one of `Z` lies at most one point of `X⁻` of codimension
one: both define divisorial valuations of `k(Z) = k(X⁻)` dominating the discrete valuation ring
`𝒪_{Z,y}`, hence equal to `ord_y`, and a valuation has at most one centre on `X⁻`. -/
private theorem eq_of_coheight_eq_one
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) {x₁ x₂ : Xm}
    (h₁ : Order.coheight x₁ = 1) (h₂ : Order.coheight x₂ = 1) (he : fm x₁ = fm x₂)
    (hy : Order.coheight (fm x₂) = 1) : x₁ = x₂ := by
  haveI := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  let P₁ : MMP.Mori.PrimeDivisor Xm := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x₁ h₁
  let P₂ : MMP.Mori.PrimeDivisor Xm := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x₂ h₂
  let Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (fm x₂) hy
  have hnZ : IsNormalVariety ℂ (fm ≫ sZ) := h.comp_eq_minus ▸ h.isNormalVariety_minus
  let D₁ : MMP.Mori.DivisorOver ℂ sZ :=
    ⟨Xm, fm, hnZ, h.isBirationalMorphism_minus, P₁⟩
  let D₂ : MMP.Mori.DivisorOver ℂ sZ :=
    ⟨Xm, fm, hnZ, h.isBirationalMorphism_minus, P₂⟩
  have hv₁ := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq
    h.isNormalVariety_target D₁ Q (by
      simp [D₁, P₁, Q, MMP.Mori.PrimeDivisor.genericPoint,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, he])
  have hv₂ := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq
    h.isNormalVariety_target D₂ Q (by
      simp [D₂, P₂, Q, MMP.Mori.PrimeDivisor.genericPoint,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne])
  let F₁ := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus P₁
  let F₂ := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus P₂
  have hF : F₁.valuation = F₂.valuation := by
    ext g
    obtain ⟨g', rfl⟩ := h.isBirationalMorphism_minus.functionFieldMap_bijective.2 g
    have := DFunLike.congr_fun (hv₁.trans hv₂.symm) g'
    change P₁.divisorialValuation (functionFieldMap (𝟙 Xm) (functionFieldMap fm g')) =
      P₂.divisorialValuation (functionFieldMap (𝟙 Xm) (functionFieldMap fm g'))
    rwa [MMP.Mori.functionFieldMap_id_apply]
  have h' : P₁.genericPoint = P₂.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq h.isNormalVariety_minus.1 hF
  simpa [F₁, F₂, P₁, P₂, MMP.Mori.PrimeDivisor.genericPoint,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] using h'

/-- A point of coheight at most one not over the generic point of the target of a dominant
morphism has coheight one. -/
private theorem coheight_eq_one_of_map_ne_genericPoint {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] {p : X} (hp : Order.coheight p ≤ 1)
    (hpg : f p ≠ genericPoint Y) : Order.coheight p = 1 := by
  refine le_antisymm hp (ENat.one_le_iff_ne_zero.mpr fun h0 => hpg ?_)
  have hmax : IsMax p := Order.coheight_eq_zero.mp h0
  have hgp : p = genericPoint X :=
    (Specializes.antisymm (hmax (genericPoint_specializes p)) (genericPoint_specializes p)).eq
  rw [hgp]
  exact MMP.Positivity.map_genericPoint_eq_of_isDominant f

/-- (A) A non-small `f⁻` contracts a prime divisor `E` to a subset of codimension `≥ 2`. -/
private theorem exists_primeDivisor_two_le_codimension_image
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hfm : ¬ IsSmallMorphism sXm sZ fm) :
    ∃ E : MMP.Mori.PrimeDivisor Xm, ∀ W : IrreducibleCloseds Z,
      (W : Set Z) = closure {fm E.genericPoint} → 2 ≤ codimension W := by
  haveI := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI : IsNormal Z := h.isNormalVariety_target.2
  haveI := h.isNormalVariety_target.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_minus
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    h.isBirationalMorphism_minus
  have hcod : ¬ 2 ≤ MMP.Mori.closedsCodimension (exceptionalSet fm) := fun h2 =>
    hfm ⟨h.isNormalVariety_minus, h.isNormalVariety_target, h.comp_eq_minus, inferInstance,
      h.isBirationalMorphism_minus, h2⟩
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at hcod
  push Not at hcod
  obtain ⟨x, hxE, hx2⟩ := hcod
  have hfin : ∀ y : Z, (fm ⁻¹' {y}).Finite → y ∈ biregularLocus fm := fun y hy => by
    obtain ⟨hU, hiso⟩ :=
      (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso fm hb).1 inferInstance
    exact le_biregularLocus hiso hy
  have hgen : fm x ≠ genericPoint Z := by
    intro hg
    refine mem_exceptionalSet.mp hxE (hfin _ ?_)
    rw [hg, preimage_genericPoint fm hb]
    exact Set.finite_singleton _
  have hx1 : Order.coheight x = 1 :=
    coheight_eq_one_of_map_ne_genericPoint fm
      (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using hx2)) hgen
  have hdim : topologicalKrullDim Xm = topologicalKrullDim Z :=
    haveI := h.isNormalVariety_minus.1
    haveI := h.isNormalVariety_target.1
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sXm
      h.isBirationalMorphism_minus).symm
  have hmono : ∀ p : Xm, Order.coheight p ≤ Order.coheight (fm p) :=
    MMP.Flips.coheight_le_coheight_map sZ sXm h.isNormalVariety_target.1
      h.isNormalVariety_minus.1 fm h.comp_eq_minus hdim
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1, fun W hW => ?_⟩
  have hW' : W = (irreducibleSetEquivPoints (α := Z)).symm (fm x) := by
    apply IrreducibleCloseds.ext
    rw [hW]
    simp [MMP.Mori.PrimeDivisor.genericPoint,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  rw [hW', codimension_eq_coheight, Order.coheight_orderIso]
  by_contra! hlt
  have hy1 : Order.coheight (fm x) = 1 :=
    le_antisymm (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using hlt)) (hx1 ▸ hmono x)
  refine mem_exceptionalSet.mp hxE (hfin _ ((Set.finite_singleton x).subset fun p hp => ?_))
  have hp : fm p = fm x := hp
  have hp1 : Order.coheight p = 1 :=
    coheight_eq_one_of_map_ne_genericPoint fm (hy1 ▸ hp ▸ hmono p) (hp ▸ hgen)
  exact eq_of_coheight_eq_one h hp1 hx1 hp hy1

/-- (B) `ord_E` is realised by a divisor over `X⁺` with proper structure morphism. -/
private theorem exists_divisorOver_valuation_comap_eq
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (E : MMP.Mori.PrimeDivisor Xm) :
    haveI := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isBirationalMorphism_plus.isDominant
    ∃ D : DivisorOver ℂ sXp, IsProper D.f ∧
      D.valuation.comap (functionFieldMap fp) = E.valuationOver fm := by
  haveI := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  have hbp := h.isBirationalMorphism_plus.functionFieldMap_bijective
  let e : Z.functionField ≃+* Xp.functionField := RingEquiv.ofBijective (functionFieldMap fp) hbp
  let D₀ := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus E
  let ξ' : Valuation Xp.functionField (WithZero (Multiplicative ℤ)) :=
    (E.valuationOver fm).comap (e.symm : Xp.functionField →+* Z.functionField)
  have hξ : ξ'.comap (functionFieldMap fp) = E.valuationOver fm := by
    ext g
    change E.valuationOver fm (e.symm (e g)) = _
    rw [RingEquiv.symm_apply_apply]
  obtain ⟨D', hD', hv⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq
    h.isNormalVariety_plus fm fp h.isBirationalMorphism_minus h.isBirationalMorphism_plus
    h.isProper_plus h.comp_eq_minus h.comp_eq_plus D₀ ξ' (by
      rw [hξ]
      ext g
      change E.divisorialValuation (functionFieldMap fm g) =
        E.divisorialValuation (functionFieldMap (𝟙 Xm) (functionFieldMap fm g))
      rw [MMP.Mori.functionFieldMap_id_apply])
  exact ⟨D', hD', hv ▸ hξ⟩

/-- (C) Since `f⁺` is small, a divisor over `X⁺` whose valuation has centre of codimension
`≥ 2` on `Z` has centre of codimension `≥ 2` on `X⁺`. -/
private theorem two_le_codimension_center
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (E : MMP.Mori.PrimeDivisor Xm)
    (hE : ∀ W : IrreducibleCloseds Z,
      (W : Set Z) = closure {fm E.genericPoint} → 2 ≤ codimension W)
    (D : DivisorOver ℂ sXp) (hD : IsProper D.f) :
    haveI := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isBirationalMorphism_plus.isDominant
    D.valuation.comap (functionFieldMap fp) = E.valuationOver fm → 2 ≤ codimension D.center := by
  intro hv
  haveI := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : IsNormal Z := h.isNormalVariety_target.2
  haveI := h.isNormalVariety_target.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fp := h.isProper_plus
  let DZ : MMP.Mori.DivisorOver ℂ sZ :=
    { Y := D.Y
      f := D.f ≫ fp
      isNormalVariety := by rw [Category.assoc, h.comp_eq_plus]; exact D.isNormalVariety
      isBirationalMorphism := MMP.Mori.isBirationalMorphism_comp_of_isBirational fp D.f
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          h.isBirationalMorphism_plus)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
      E := D.E }
  let EZ : MMP.Mori.DivisorOver ℂ sZ :=
    { Y := Xm
      f := fm
      isNormalVariety := h.comp_eq_minus ▸ h.isNormalVariety_minus
      isBirationalMorphism := h.isBirationalMorphism_minus
      E := E }
  have hval : DZ.valuation = EZ.valuation := by
    ext g
    change D.E.divisorialValuation (functionFieldMap (D.f ≫ fp) g) =
      E.divisorialValuation (functionFieldMap fm g)
    rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    exact DFunLike.congr_fun hv g
  have hpt : fp (D.f D.E.genericPoint) = fm E.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq
      h.isNormalVariety_target.1 hval
  rw [MMP.Positivity.DivisorOver.codimension_center]
  by_contra! hlt
  have hx : fp (D.f D.E.genericPoint) ∈ biregularLocus fp := by
    by_contra hx
    exact (MMP.Positivity.two_le_coheight_of_mem_exceptionalSet
      h.isSmallMorphism_plus.two_le_codimension (mem_exceptionalSet.mpr hx)).not_gt hlt
  have h2 := hE ((irreducibleSetEquivPoints (α := Z)).symm (fm E.genericPoint)) rfl
  rw [codimension_eq_coheight, Order.coheight_orderIso, ← hpt,
    MMP.Positivity.coheight_map_of_mem_biregularLocus fp hx] at h2
  exact h2.not_gt hlt

/-- In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` in which `f⁻` is not small, there is a prime
divisor `E` of `X⁻` whose valuation `ord_E` is exceptional over `X⁺`: it agrees, as a valuation
of `k(Z)`, with a valuation `v` of `k(X⁺)` that is exceptional over `X⁺`. -/
@[mmp "lem_oai4_c1_not_small_loses_divisor"]
public theorem IsFourfoldStepDiagram.exists_isExceptionalValuation_of_not_isSmallMorphism
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hfm : ¬ IsSmallMorphism sXm sZ fm) :
    ∃ (E : MMP.Mori.PrimeDivisor Xm) (v : Valuation Xp.functionField (WithZero (Multiplicative ℤ))),
      MMP.Intersection.IsExceptionalValuation ℂ sXp v ∧
      haveI := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      v.comap (functionFieldMap fp) = E.valuationOver fm := by
  obtain ⟨E, hE⟩ := exists_primeDivisor_two_le_codimension_image h hfm
  obtain ⟨D, hD, hv⟩ := exists_divisorOver_valuation_comap_eq h E
  exact ⟨E, D.valuation, ⟨D, hD, rfl, two_le_codimension_center h E hE D hD hv⟩, hv⟩

end NotSmall

/-! ### Coefficients across a step of the tail -/

/-- A divisor whose coefficients vanish at every prime on which `φ` is defined is sent to `0` by
the linear extension of `φ`. -/
private theorem mapPrimeDivisors_eq_zero_of_forall {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} (h : ∀ P, φ P ≠ none → D P = 0) :
    DivisorWithCoeffs.mapPrimeDivisors φ D = 0 := by
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply]
  refine Finset.sum_eq_zero fun P hP ↦ ?_
  by_cases hφ : φ P = none
  · simp only [hφ]; rfl
  · exact absurd (h P hφ) (Finsupp.mem_support_iff.mp hP)

/-- A separated birational morphism is injective over a point whose local ring is a valuation
ring. -/
private theorem eq_of_map_eq_of_valuationRing {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {f : X ⟶ Y} [IsSeparated f] [IsDominant f] (hμ : Function.Bijective (functionFieldMap f))
    {y : Y} [ValuationRing (Y.presheaf.stalk y)] {x₁ x₂ : X} (h₁ : f x₁ = y) (h₂ : f x₂ = y) :
    x₁ = x₂ := by
  subst h₁
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₁
  have : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hμ h₂

/-- A point over the generic point of a prime divisor of a normal scheme, under a birational
morphism, is the generic point of a prime divisor, and the morphism is a local isomorphism
there. -/
private theorem exists_primeDivisor_of_map_eq_genericPoint {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) {x : X} {D : MMP.Mori.PrimeDivisor Y}
    (hx : f x = D.genericPoint) :
    ∃ E : MMP.Mori.PrimeDivisor X, E.genericPoint = x ∧ IsIso (f.stalkMap x) := by
  have := D.isDiscreteValuationRing_localRing
  have := hf.isDominant
  have : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective x
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      D.coheight_genericPoint] at h
    exact_mod_cast h.symm
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco, hiso⟩

/-- Two partial maps on prime divisors with the same fibre over `A`, resp. `B`, give the same
coefficient at `A`, resp. `B`, in the linear extension. -/
private theorem mapPrimeDivisors_apply_eq_of_iff {X Y Y' : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {ψ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y')}
    {A : MMP.Mori.PrimeDivisor Y} {B : MMP.Mori.PrimeDivisor Y'}
    (h : ∀ E, φ E = some A ↔ ψ E = some B) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D A = DivisorWithCoeffs.mapPrimeDivisors ψ D B := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, hD, hD']
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    have hE := h E
    rcases hφ : φ E with _ | A' <;> rcases hψ : ψ E with _ | B' <;>
      simp only [hφ, hψ, reduceCtorEq, false_iff, iff_false, Option.some.injEq] at hE <;>
      simp only [Option.elim_none, Option.elim_some, Finsupp.coe_zero, Pi.zero_apply,
        Finsupp.single_apply]
    · simp [hE]
    · simp [hE]
    · by_cases hA : A' = A
      · simp [hA, hE.mp hA]
      · have hB : ¬ B' = B := fun hB => hA (hE.mpr hB)
        simp [hA, hB]

/-- Over the biregular locus, a morphism reflects specialization. -/
private theorem specializes_of_map_specializes {X Y : Scheme.{0}} {f : X ⟶ Y} {x y : X}
    (hx : f x ∈ biregularLocus f) (hy : f y ∈ biregularLocus f) (h : f x ⤳ f y) : x ⤳ y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by rw [morphismRestrict_ι]; rfl
  have hpq : p ⤳ q := by
    rwa [← ((f ∣_ V) ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
  exact hpq.map (f ⁻¹ᵁ V).ι.continuous

/-- If the exceptional set of `f` has codimension at least two, `f` is biregular over the image
of the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {X Y : Scheme.{0}} {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f := by
  by_contra h
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 (x := P.genericPoint) h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal_support {X : Scheme.{0}}
    (D : MMP.Mori.PrimeDivisor X) :
    D.idealSheaf = Scheme.IdealSheafData.vanishingIdeal D.idealSheaf.support := by
  have := D.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl

/-- A point lies on a prime divisor exactly when it is a specialization of its generic point. -/
private theorem mem_support_iff_specializes {X : Scheme.{0}} (D : MMP.Mori.PrimeDivisor X)
    (x : X) :
    x ∈ D.support ↔ D.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, specializes_iff_mem_closure]

/-- Over the biregular locus, the inverse transform of `Q` is the prime divisor through the
point over `η_Q`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of {X Y : Scheme.{0}} {f : X ⟶ Y}
    (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (hPQ : f P.genericPoint = Q.genericPoint) (hV : Q.genericPoint ∈ biregularLocus f) :
    inverseTransformPrimeDivisor f Q = some P := by
  have hset : (inverseTransform f Q.idealSheaf.support : Set X) = P.support := by
    rw [inverseTransform, Closeds.coe_closure]
    refine le_antisymm (closure_minimal ?_ ?_) ?_
    · rintro y ⟨hyQ, hyV⟩
      have h1 : f P.genericPoint ⤳ f y := hPQ ▸ (mem_support_iff_specializes Q _).mp hyQ
      exact (mem_support_iff_specializes P y).mpr (specializes_of_map_specializes (hPQ ▸ hV) hyV h1)
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal (Set.singleton_subset_iff.mpr (subset_closure ?_)) isClosed_closure
      refine ⟨?_, ?_⟩
      · change f P.genericPoint ∈ Q.support
        rw [hPQ]; exact (mem_support_iff_specializes Q _).mpr specializes_rfl
      · change f P.genericPoint ∈ biregularLocus f
        rwa [hPQ]
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨Q.genericPoint,
    (mem_support_iff_specializes Q _).mpr specializes_rfl, hV⟩, ?_⟩
  rw [inverseTransformIdeal, idealSheaf_eq_vanishingIdeal_support P]
  congr 1
  ext1
  exact hset.symm

/-- For a surjective `f`, `P` is the inverse transform of at most one prime divisor `Q`. -/
private theorem eq_of_inverseTransformPrimeDivisor_eq_some {X Y : Scheme.{0}} {f : X ⟶ Y}
    (hs : Function.Surjective f) {P : MMP.Mori.PrimeDivisor X} {Q Q' : MMP.Mori.PrimeDivisor Y}
    (hPQ : f P.genericPoint = Q.genericPoint) (h : inverseTransformPrimeDivisor f Q' = some P) :
    Q' = Q := by
  obtain ⟨⟨z, hzQ, hzV⟩, hI⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp h
  have hset : P.support = closure (f ⁻¹' ((Q'.support : Set Y) ∩ biregularLocus f)) := by
    have := congrArg (fun I ↦ (I.support : Set X)) hI
    simp only [inverseTransformIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    rw [AlgebraicGeometry.PrimeDivisor.support, this, inverseTransform, Closeds.coe_closure]
  have hQ'cl : IsClosed (Q'.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have h1 : Q.genericPoint ∈ Q'.support := by
    have hP : P.genericPoint ∈ closure (f ⁻¹' ((Q'.support : Set Y) ∩ biregularLocus f)) :=
      hset ▸ (mem_support_iff_specializes P _).mpr specializes_rfl
    have := image_closure_subset_closure_image f.continuous ⟨_, hP, rfl⟩
    rw [hPQ] at this
    refine closure_minimal ?_ hQ'cl this
    rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
    exact hy
  have h2 : Q'.genericPoint ∈ Q.support := by
    have hgV : Q'.genericPoint ∈ biregularLocus f :=
      ((mem_support_iff_specializes Q' z).mp hzQ).mem_open (biregularLocus f).isOpen hzV
    obtain ⟨y, hy⟩ := hs Q'.genericPoint
    have hyP : y ∈ P.support := by
      rw [hset]
      refine subset_closure ⟨?_, ?_⟩
      · rw [hy]; exact (mem_support_iff_specializes Q' _).mpr specializes_rfl
      · change f y ∈ biregularLocus f
        rwa [hy]
    rw [← hy, mem_support_iff_specializes, ← hPQ]
    exact ((mem_support_iff_specializes P y).mp hyP).map f.continuous
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (((mem_support_iff_specializes Q' _).mp h1).antisymm
      ((mem_support_iff_specializes Q _).mp h2)).eq

/-- The coefficient of `P` in the strict transform `(f⁺)⁻¹_* f⁻_* D` is that of `P⁻` in `D`,
when `f⁻(η_{P⁻}) = η_Q = f⁺(η_P)`, the local ring at `η_Q` is a valuation ring, `f⁻` is separated
birational, `f⁺` surjective and biregular over `η_Q`. -/
private theorem flipTransform_apply_of_map_genericPoint {Xm Xp Z : Scheme.{0}}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsIntegral Xm] [IsIntegral Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] [IsSeparated fm] [IsDominant fm]
    (hbm : Function.Bijective (functionFieldMap fm))
    (hs : Function.Surjective fp) {P : MMP.Mori.PrimeDivisor Xm} {Pp : MMP.Mori.PrimeDivisor Xp}
    {Q : MMP.Mori.PrimeDivisor Z} [ValuationRing (Z.presheaf.stalk Q.genericPoint)]
    (hPQ : fm P.genericPoint = Q.genericPoint) (hPpQ : fp Pp.genericPoint = Q.genericPoint)
    (hV : Q.genericPoint ∈ biregularLocus fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D Pp = D P := by
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (inverseTransformPrimeDivisor_eq_some_of Pp Q hPpQ hV)
    (fun _ hQ' => eq_of_inverseTransformPrimeDivisor_eq_some hs hPpQ hQ'),
    RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm P Q).mpr hPQ)
    (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_map_eq_of_valuationRing hbm
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm E' Q).mp hE') hPQ)]

/-- A projective birational morphism `p : Y ⟶ X` of complex varieties onto a normal variety is
an isomorphism over the generic point of every prime divisor of `X`. -/
private theorem genericPoint_mem_biregularLocus {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hX : AlgebraicGeometry.IsVariety ℂ sX) (hY : AlgebraicGeometry.IsVariety ℂ sY)
    (p : Y ⟶ X) (hp : p ≫ sX = sY) [IsProper p] (hb : MMP.Mori.IsBirationalMorphism p)
    (D : MMP.Mori.PrimeDivisor X) : D.genericPoint ∈ biregularLocus p := by
  obtain ⟨⟨hO, hiso⟩, -, -⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq
    ℂ hY hX p hp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  refine le_biregularLocus (V := ⟨_, hO⟩) hiso ?_
  have := D.isDiscreteValuationRing_localRing
  have := hb.isDominant
  exact Set.Subsingleton.finite fun x₁ h₁ x₂ h₂ =>
    eq_of_map_eq_of_valuationRing (y := D.genericPoint) hb.functionFieldMap_bijective h₁ h₂

/-- A complex variety is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal_of_isVariety {X : Scheme.{0}}
    {s : X ⟶ Spec (.of ℂ)} (h : AlgebraicGeometry.IsVariety ℂ s) :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = s ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- A prime of the source of a crepant junction lying over a prime divisor of the base is not
one of the extracted divisors `E_s`. -/
private theorem junction_E_ne_of_map_genericPoint {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction sX B I) {PY : MMP.Mori.PrimeDivisor J.Y}
    {P₀ : MMP.Mori.PrimeDivisor X} (hpPY : J.p PY.genericPoint = P₀.genericPoint) (s : I) :
    J.E s ≠ PY := by
  intro hs
  have := isSeparated_toTerminal_of_isVariety J.isProjectiveVariety_base.toIsVariety
  have hex := (J.isExceptional_iff PY).mpr ⟨s, hs⟩
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hex
  have hmem : J.p PY.genericPoint ∈
      (Closeds.closure (J.p '' (PY.idealSheaf.support : Set J.Y)) : Set X) := by
    rw [Closeds.coe_closure]
    exact subset_closure
      ⟨PY.genericPoint, (mem_support_iff_specializes PY _).mpr specializes_rfl, rfl⟩
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hex _ hmem
  rw [hpPY, P₀.coheight_genericPoint] at this
  exact absurd this (by decide)

namespace StabilizedSmallKltTail

/-- The coefficient of a decreased boundary `Θ'` at a prime `P_Y` of `Y_i` over a prime divisor
`P₀` of `X_i` is the coefficient of `B_i` at `P₀`. -/
private theorem decreasedBoundary_apply_of_map_genericPoint {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {PY : MMP.Mori.PrimeDivisor J.Y}
    {P₀ : MMP.Mori.PrimeDivisor (T.X i)} (hpPY : J.p PY.genericPoint = P₀.genericPoint) :
    Θ' PY = T.B i P₀ := by
  classical
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have := J.isBirationalMorphism.isDominant
  obtain ⟨a, -, rfl⟩ := hΘ'
  rw [Finsupp.add_apply, Finsupp.finsetSum_apply, Finset.sum_eq_zero fun s _ => by
    simp [junction_E_ne_of_map_genericPoint J hpPY s], add_zero]
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (inverseTransformPrimeDivisor_eq_some_of PY P₀ hpPY
      (genericPoint_mem_biregularLocus (T.isFourfoldStepDiagram i).isNormalVariety_minus.1
        J.isProjectiveVariety.toIsVariety J.p rfl J.isBirationalMorphism P₀))
    (fun _ hQ' => eq_of_inverseTransformPrimeDivisor_eq_some J.p.surjective hpPY hQ') _

/-- In a commutative square of separated dominant morphisms with bijective function-field maps,
a point of `W` lies over `y_Y` exactly when it lies over `y₁`, if both lie over a point `z` of `Z`
with valuation-ring stalk and `y_Y` lies over a point `y₀` with valuation-ring stalk. -/
private theorem map_eq_iff_of_comp_eq {W Y X₀ X₁ Z : Scheme.{0}} [IsIntegral Y] [IsIntegral X₀]
    [IsIntegral X₁] [IsIntegral Z] {q : W ⟶ Y} {p : Y ⟶ X₀} {f : X₀ ⟶ Z} {r : W ⟶ X₁}
    {fp : X₁ ⟶ Z} [IsSeparated p] [IsDominant p] [IsSeparated f] [IsDominant f]
    [IsSeparated fp] [IsDominant fp] (hp : Function.Bijective (functionFieldMap p))
    (hf : Function.Bijective (functionFieldMap f)) (hfp : Function.Bijective (functionFieldMap fp))
    (hcomp : ∀ x, f (p (q x)) = fp (r x)) {yY : Y} {y₀ : X₀} {y₁ : X₁} {z : Z}
    [ValuationRing (Z.presheaf.stalk z)] [ValuationRing (X₀.presheaf.stalk y₀)]
    (h₁ : fp y₁ = z) (h₀ : f y₀ = z) (hY : p yY = y₀) (w : W) : q w = yY ↔ r w = y₁ :=
  ⟨fun hw => eq_of_map_eq_of_valuationRing hfp (y := z) (by rw [← hcomp, hw, hY, h₀]) h₁,
    fun hw => eq_of_map_eq_of_valuationRing hp (y := y₀)
      (eq_of_map_eq_of_valuationRing hf (y := z) (by rw [hcomp, hw, h₁]) h₀) hY⟩

/-- **The coefficient computation.** At a prime `P_W` of `W` with `r_* P_W = P₁` a prime of
`X_{i+1}`, let `Q = f_i⁺(P₁)`, `P₀` the prime of `X_i` over `Q` and `P_Y` the prime of `Y_i` over
`P₀`. All four maps are local isomorphisms there, and
`coeff_{P_W} G_Y = coeff_{P_Y} K_Y + coeff_{P₀} B_i = coeff_{P₁}(K_{i+1} + B_{i+1}) =
coeff_{P_W} G_X`. -/
private theorem coeff_sub_eq_zero_of_transformPrimeDivisor_ne_none
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)} (hq : IsBirationalMorphism q)
    (hr : IsBirationalMorphism r) (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    {KW : Divisor W} {KY : Divisor J.Y}
    (hKY : RationalMap.transformDivisor q.toRationalMap KW = KY)
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = T.K (i + 1))
    {GY GX : RDivisor W}
    (hGY : MMP.Flips.IsRCartierPullback q
      (MMP.Flips.logCanonicalDivisor KY (QDivisor.toRDivisor Θ')) GY)
    (hGX : MMP.Flips.IsRCartierPullback r
      (MMP.Flips.logCanonicalDivisor (T.K (i + 1)) (QDivisor.toRDivisor (T.B (i + 1)))) GX)
    (P : MMP.Mori.PrimeDivisor W)
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor r.toRationalMap P ≠ none) :
    (GY - GX) P = 0 := by
  have hD := T.isFourfoldStepDiagram i
  have hZ := hD.isNormalVariety_target
  have : IsNormal (T.Z i) := hZ.2
  have : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  have : IsProper (T.f i) :=
    IsSmallMorphism.isProper (T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le _))
  have : IsProper (T.fp i) := hD.isSmallMorphism_plus.isProper
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have := isSeparated_toTerminal_of_isVariety hZ.1
  have := isSeparated_toTerminal_of_isVariety hD.isNormalVariety_plus.1
  have := isSeparated_toTerminal_of_isVariety hD.isNormalVariety_minus.1
  have := isSeparated_toTerminal_of_isVariety J.isProjectiveVariety.toIsVariety
  have hbf := hD.isBirationalMorphism_minus
  have hbp := J.isBirationalMorphism
  have := hbp.isDominant
  obtain ⟨P₁, hrP⟩ := Option.ne_none_iff_exists'.mp hP
  rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff] at hrP
  have hV₁ := map_genericPoint_mem_biregularLocus hD.isSmallMorphism_plus.two_le_codimension P₁
  have hζ : Order.coheight (T.fp i P₁.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hV₁, P₁.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor (T.Z i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : T.fp i P₁.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  have := Q.isDiscreteValuationRing_localRing
  have hcompE : ∀ x : W, T.f i (J.p (q x)) = T.fp i (r x) := fun x => by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : W ⟶ T.Z i => g x) hcomp
  have hzQ : T.f i (J.p (q P.genericPoint)) = Q.genericPoint := by rw [hcompE, hrP, hQ]
  obtain ⟨P₀, hP₀, -⟩ := exists_primeDivisor_of_map_eq_genericPoint hbf hzQ
  obtain ⟨PY, hPY, -⟩ := exists_primeDivisor_of_map_eq_genericPoint hbp hP₀.symm
  obtain ⟨-, -, _⟩ := exists_primeDivisor_of_map_eq_genericPoint hq hPY.symm
  obtain ⟨-, -, _⟩ := exists_primeDivisor_of_map_eq_genericPoint hr hrP
  have hfP₀ : T.f i P₀.genericPoint = Q.genericPoint := by rwa [hP₀]
  have hpPY : J.p PY.genericPoint = P₀.genericPoint := by rw [hPY, hP₀]
  have := P₀.isDiscreteValuationRing_localRing
  have hK : KY PY = T.K (i + 1) P₁ := by
    rw [← hKY, ← hKX]
    refine mapPrimeDivisors_apply_eq_of_iff (fun E => ?_) KW
    simp only [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff]
    exact map_eq_iff_of_comp_eq hbp.functionFieldMap_bijective hbf.functionFieldMap_bijective
      hD.isBirationalMorphism_plus.functionFieldMap_bijective hcompE hQ hfP₀ hpPY E.genericPoint
  have hB : T.B (i + 1) P₁ = T.B i P₀ := by
    rw [T.B_eq i]
    exact flipTransform_apply_of_map_genericPoint hbf.functionFieldMap_bijective
      (T.fp i).surjective hfP₀ hQ (hQ ▸ hV₁) (T.B i)
  have hY : GY P = _ := coeff_eq_of_isRCartierPullback P PY hPY.symm hGY
  have hX : GX P = _ := coeff_eq_of_isRCartierPullback P P₁ hrP hGX
  rw [Finsupp.sub_apply, hY, hX, sub_eq_zero]
  change ((KY PY : ℤ) : ℝ) + ((Θ' PY : ℚ) : ℝ) =
    ((T.K (i + 1) P₁ : ℤ) : ℝ) + ((T.B (i + 1) P₁ : ℚ) : ℝ)
  rw [hK, decreasedBoundary_apply_of_map_genericPoint hΘ' hpPY, hB]

/-- In a stabilized small klt tail, let `Θ'` be the decreased boundary of a crepant junction
`p_i : Y_i ⟶ X_i` extracting `I_∞`, and let `q : W ⟶ Y_i`, `r : W ⟶ X_{i+1}` be birational
morphisms from a smooth projective variety with `q ≫ p_i ≫ f_i = r ≫ f_i⁺`. Let `K_W` be a
divisor of `W` with `q_* K_W = K_Y` and `r_* K_W = K_{i+1}`, and let `G_Y`, `G_X` be the
pull-backs `q^*(K_Y + Θ')`, `r^*(K_{i+1} + B_{i+1})`. Then `r_*(G_Y - G_X) = 0`. -/
@[mmp "lem_oai4_c1_bridge_comparison_exceptional"]
public theorem transformDivisor_sub_eq_zero_of_isDecreasedBoundary
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i)
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW) [Smooth sW]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)} (hq : IsBirationalMorphism q)
    (hr : IsBirationalMorphism r) (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    {KW : Divisor W} {KY : Divisor J.Y}
    (hKY : RationalMap.transformDivisor q.toRationalMap KW = KY)
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = T.K (i + 1))
    {GY GX : RDivisor W}
    (hGY : MMP.Flips.IsRCartierPullback q
      (MMP.Flips.logCanonicalDivisor KY (QDivisor.toRDivisor Θ')) GY)
    (hGX : MMP.Flips.IsRCartierPullback r
      (MMP.Flips.logCanonicalDivisor (T.K (i + 1)) (QDivisor.toRDivisor (T.B (i + 1)))) GX) :
    RationalMap.transformDivisor r.toRationalMap (GY - GX) = 0 :=
  mapPrimeDivisors_eq_zero_of_forall fun P hP ↦
    coeff_sub_eq_zero_of_transformPrimeDivisor_ne_none hΘ' hq hr hcomp hKY hKX hGY hGX P hP

/-! ### The boundaries of a terminal chain -/

namespace TerminalChain

/-! ### Supports of transforms of divisors -/

/-- A prime divisor `P` with nonzero coefficient in `φ_* D` is `φ(Q)` for a prime divisor `Q`
with nonzero coefficient in `D`. -/
private theorem exists_of_mapPrimeDivisors_apply_ne_zero {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (D : DivisorWithCoeffs R X) (P : MMP.Mori.PrimeDivisor Y)
    (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) : ∃ Q, D Q ≠ 0 ∧ φ Q = some P := by
  classical
  by_contra hne
  push Not at hne
  refine h ?_
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [map_finsuppSum, Finsupp.sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  cases hφ : φ Q with
  | none => rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_none hφ]; rfl
  | some E =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_some hφ, Finsupp.single_apply, if_neg]
    rintro rfl
    exact hne Q (Finsupp.mem_support_iff.mp hQ) hφ

/-- If a birational morphism `f : X ⟶ Y` onto a normal scheme maps the generic point of a prime
divisor `E` to that of a prime divisor `Q`, then `ord_E`, read in `k(Y)`, is `ord_Q`. -/
private theorem valuationOver_eq_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) (E : MMP.Mori.PrimeDivisor X)
    (Q : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = Q.genericPoint) :
    haveI := hf.isDominant
    E.valuationOver f = Q.divisorialValuation := by
  have := hf.isDominant
  have := Q.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (f E.genericPoint)) := by rw [heq]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
    E.genericPoint
  refine Valuation.ext fun t => ?_
  rw [PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- A prime divisor `P` with nonzero coefficient in `g⁻¹_* D`, for a birational morphism `g`
onto a normal scheme, is the strict transform of a component `Q` of `D`, and `ord_P = ord_Q`. -/
private theorem exists_of_inverseTransformDivisor_apply_ne_zero {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {g : X ⟶ Y} (hg : IsBirationalMorphism g) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) (P : MMP.Mori.PrimeDivisor X)
    (h : inverseTransformDivisor g D P ≠ 0) :
    haveI := hg.isDominant
    ∃ Q, D Q ≠ 0 ∧ P.valuationOver g = Q.divisorialValuation := by
  obtain ⟨Q, hQ, hP⟩ := exists_of_mapPrimeDivisors_apply_ne_zero _ D P h
  exact ⟨Q, hQ, valuationOver_eq_of_map_genericPoint hg P Q
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP).1⟩

/-- A prime divisor `P` with nonzero coefficient in the strict transform `(f⁺)⁻¹_* f_* D` across
birational morphisms `f : X⁻ ⟶ Z ⟵ X⁺ : f⁺` onto a separated normal scheme comes from a
component `P⁻` of `D` with `ord_{P⁻} = ord_P` as valuations of `k(Z)`. -/
private theorem exists_of_flipTransform_apply_ne_zero {Xm Xp Z : Scheme.{u}} [IsIntegral Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsSeparated (Z ↘ Limits.terminal Scheme)]
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hfm : IsBirationalMorphism fm) (hfp : IsBirationalMorphism fp)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) (P : MMP.Mori.PrimeDivisor Xp)
    (h : flipTransform fm fp D P ≠ 0) :
    haveI := hfm.isDominant
    haveI := hfp.isDominant
    ∃ Pm, D Pm ≠ 0 ∧ Pm.valuationOver fm = P.valuationOver fp := by
  have := hfm.isDominant
  have := hfp.isDominant
  obtain ⟨Q, hQ, hPQ⟩ := exists_of_inverseTransformDivisor_apply_ne_zero hfp _ P h
  obtain ⟨Pm, hPm, hPmQ⟩ := exists_of_mapPrimeDivisors_apply_ne_zero _ D Q hQ
  refine ⟨Pm, hPm, ?_⟩
  rw [hPQ]
  exact valuationOver_eq_of_map_genericPoint hfm Pm Q
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm Q).mp hPmQ)

/-- Functoriality of the pullback of rational functions along dominant morphisms of integral
schemes. -/
private theorem functionFieldMap_comp_apply {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  obtain ⟨s, rfl⟩ := MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint
    ((a ≫ b) (genericPoint A)) (map_genericPoint_of_isDominant (a ≫ b)) t
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk (a ≫ b) (genericPoint A) s]
  erw [MMP.Mori.functionFieldMap_algebraMap_stalk b (a (genericPoint A)) s,
    MMP.Mori.functionFieldMap_algebraMap_stalk a (genericPoint A)]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- Restriction of `ord_Q` along a composite `f ≫ g` is restriction along `f`, then along `g`. -/
private theorem valuationOver_comp {A B C : Scheme.{u}} [IsIntegral A] [IsLocallyNoetherian A]
    [IsNormal A] [IsIntegral B] [IsIntegral C] (Q : MMP.Mori.PrimeDivisor A) (f : A ⟶ B)
    (g : B ⟶ C) [IsDominant f] [IsDominant g] {c : A ⟶ C} [IsDominant c] (hc : f ≫ g = c) :
    Q.valuationOver c = (Q.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [MMP.Mori.PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  rw [functionFieldMap_comp_apply f g hc]

/-! ### Junctions -/

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- A divisor `p⁻¹_* B + ∑_s c(s) E_s` on a crepant junction is supported on the strict
transforms of the components of `B`, whose valuations are those of the components, and on the
`E_s`. -/
private theorem junction_support (J : FourfoldCrepantJunction sX B I) (c : I → ℚ)
    (P : MMP.Mori.PrimeDivisor J.Y)
    (h : (inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (c s)) P ≠ 0) :
    haveI := J.isBirationalMorphism.isDominant
    (∃ Γ : MMP.Mori.PrimeDivisor X, B Γ ≠ 0 ∧ P.valuationOver J.p = Γ.divisorialValuation) ∨
      ∃ s, P = J.E s := by
  classical
  by_cases hs : ∃ s, P = J.E s
  · exact Or.inr hs
  refine Or.inl (exists_of_inverseTransformDivisor_apply_ne_zero J.isBirationalMorphism B P ?_)
  have h0 : (∑ s : I, Finsupp.single (J.E s) (c s)) P = 0 := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact hs ⟨s, rfl⟩
  rwa [Finsupp.add_apply, h0, add_zero] at h

/-- Every prime divisor `Γ` of the base `X` of a crepant junction `p : Y ⟶ X` has a strict
transform on `Y`: `p` is an isomorphism over the generic point of `Γ`. -/
private theorem exists_inverseTransformPrimeDivisor (J : FourfoldCrepantJunction sX B I)
    (Γ : MMP.Mori.PrimeDivisor X) :
    ∃ S, inverseTransformPrimeDivisor J.p Γ = some S ∧ J.p S.genericPoint = Γ.genericPoint := by
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  exact MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some Γ
    (genericPoint_mem_biregularLocus J.isProjectiveVariety_base.toIsVariety
      J.isProjectiveVariety.toIsVariety J.p rfl J.isBirationalMorphism Γ)

end Junction

/-! ### Components of the boundaries along the chain -/

variable {T : StabilizedSmallKltTail}

/-- Every component of `B_i` corresponds to a component of `B_0`: `B_{i+1}` is the strict
transform `(f_i⁺)⁻¹_* (f_i)_* B_i`. -/
private theorem exists_corresponds_of_coeff_ne_zero : ∀ (i : ℕ) (Γ : MMP.Mori.PrimeDivisor (T.X i)),
    T.B i Γ ≠ 0 → ∃ Γ₀ : MMP.Mori.PrimeDivisor (T.X 0), T.B 0 Γ₀ ≠ 0 ∧
      T.Corresponds i Γ₀.divisorialValuation Γ.divisorialValuation
  | 0, Γ, h => ⟨Γ, h, rfl⟩
  | i + 1, Γ, h => by
    have hd := T.isFourfoldStepDiagram i
    have hZ := hd.isNormalVariety_target
    have : IsNormal (T.Z i) := hZ.2
    have : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
    have : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
    have := isSeparated_toTerminal_of_isVariety hZ.1
    rw [T.B_eq i] at h
    obtain ⟨Γm, hΓm, hv⟩ := exists_of_flipTransform_apply_ne_zero hd.isBirationalMorphism_minus
      hd.isBirationalMorphism_plus _ Γ h
    obtain ⟨Γ₀, h₀, hc⟩ := exists_corresponds_of_coeff_ne_zero i Γm hΓm
    exact ⟨Γ₀, h₀, _, hc, hv.symm⟩

/-- A component `Γ` of `B_0` gives a label, its strict transform on `Y_0`, with `ord_Γ` as its
valuation. -/
private theorem exists_label_of_coeff_ne_zero (C : TerminalChain T)
    {Γ : MMP.Mori.PrimeDivisor (T.X 0)} (hΓ : T.B 0 Γ ≠ 0) :
    ∃ S : C.Label, labelValuation S = Γ.divisorialValuation := by
  obtain ⟨S, hS, hη⟩ := exists_inverseTransformPrimeDivisor (C.junction 0) Γ
  exact ⟨⟨S, C.isLabel_of_inverseTransformPrimeDivisor_eq_some hΓ hS⟩,
    valuationOver_eq_of_map_genericPoint (C.junction 0).isBirationalMorphism S Γ hη⟩

/-- A valuation `s ∈ I_i` corresponds to the valuation of a label `E_{0,s'}`. -/
private theorem exists_label_of_mem_I (C : TerminalChain T) {i : ℕ} (s : C.I i) :
    ∃ S : C.Label, T.Corresponds i (labelValuation S) s.1 := by
  obtain ⟨ξ, hξ, hc⟩ : s.1 ∈ T.stableLowDiscrepancySetAt i := C.coe_I i ▸ s.2
  have h0 : ξ ∈ (C.I 0 : Set _) := by
    rw [C.coe_I 0]
    exact ⟨ξ, hξ, rfl⟩
  exact ⟨⟨_, C.isLabel_E ⟨ξ, h0⟩⟩, by rwa [labelValuation_E]⟩

/-- On a junction `Y_i`, a component of a divisor `p_i⁻¹_* B_i + ∑_s c(s) E_{i,s}` is the centre
of a label. -/
private theorem exists_isLabelCentre_junction (C : TerminalChain T) (i : ℕ) (c : C.I i → ℚ)
    (P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩))
    (h : (inverseTransformDivisor (C.junction i).p (T.B i) +
      ∑ s : C.I i, Finsupp.single ((C.junction i).E s) (c s)) P ≠ 0) :
    ∃ S : C.Label, C.IsLabelCentre S ⟨i, none⟩ P := by
  rcases junction_support (C.junction i) c P h with ⟨Γ, hΓ, hP⟩ | ⟨s, hs⟩
  · obtain ⟨Γ₀, h₀, hc⟩ := exists_corresponds_of_coeff_ne_zero i Γ hΓ
    obtain ⟨S, hS⟩ := exists_label_of_coeff_ne_zero C h₀
    exact ⟨S, _, hS ▸ hc, hP⟩
  · obtain ⟨S, hS⟩ := exists_label_of_mem_I C s
    refine ⟨S, _, hS, ?_⟩
    change MMP.Mori.PrimeDivisor (C.junction i).Y at P
    subst hs
    exact (C.junction i).valuation_eq s

/-- Every `π_k : V_k ⟶ Z_i`, `k ≤ m`, of the programme of a bridge is dominant. -/
private theorem isDominant_toBase (C : TerminalChain T) (i : ℕ) :
    ∀ k ≤ (C.bridge i).P.m, IsDominant ((C.bridge i).P.toBase k)
  | 0, _ => by
    have := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    have := (C.junction i).isBirationalMorphism.isDominant
    exact (inferInstance : IsDominant ((C.junction i).p ≫ T.f i))
  | k + 1, hk => by
    have hk' : k < (C.bridge i).P.m := hk
    have hd := (C.bridge i).P.isFourfoldStepDiagram k hk'
    have := hd.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) :=
      (C.bridge i).P.modelMap_eq k hk' ▸ isDominant_toBase C i k hk'.le
    have : IsDominant ((C.bridge i).P.h k) := IsDominant.of_comp ((C.bridge i).P.g k) _
    show IsDominant ((C.bridge i).P.πY k)
    rw [(C.bridge i).P.πY_eq k hk']
    infer_instance

/-- Along the programme of a bridge, a component of `Θ_k` on `V_k` has the valuation of `k(Z_i)`
of a component of the decreased boundary `Θ_0 = Θ_i'` on `V_0 = Y_i`: each `Θ_{k+1}` is the strict
transform `(g_k⁺)⁻¹_* (g_k)_* Θ_k`. -/
private theorem bridge_support (C : TerminalChain T) (i : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ (C.bridge i).P.m) (P : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k)),
      (C.bridge i).P.boundary k P ≠ 0 →
      haveI := isDominant_toBase C i k hk
      haveI := isDominant_toBase C i 0 (Nat.zero_le _)
      ∃ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model 0), (C.bridge i).P.boundary 0 Q ≠ 0 ∧
        P.valuationOver ((C.bridge i).P.toBase k) = Q.valuationOver ((C.bridge i).P.toBase 0)
  | 0, _, P, h => ⟨P, h, rfl⟩
  | k + 1, hk, P, h => by
    have hk' : k < (C.bridge i).P.m := hk
    have hd := (C.bridge i).P.isFourfoldStepDiagram k hk'
    have hTk := hd.isNormalVariety_target
    have : IsIntegral ((C.bridge i).P.T k) := hTk.1.toIsIntegral
    have : IsNormal ((C.bridge i).P.T k) := hTk.2
    have : LocallyOfFiniteType ((C.bridge i).P.sT k) := hTk.1.toLocallyOfFiniteType
    have : IsLocallyNoetherian ((C.bridge i).P.T k) :=
      LocallyOfFiniteType.isLocallyNoetherian ((C.bridge i).P.sT k)
    have := isSeparated_toTerminal_of_isVariety hTk.1
    rw [(C.bridge i).P.boundary_succ_eq_flipTransform hk'] at h
    obtain ⟨Pm, hPm, hv⟩ := exists_of_flipTransform_apply_ne_zero hd.isBirationalMorphism_minus
      hd.isBirationalMorphism_plus _ P h
    obtain ⟨Q, hQ, hQv⟩ := bridge_support C i k hk'.le Pm hPm
    refine ⟨Q, hQ, ?_⟩
    have := hd.isBirationalMorphism_minus.isDominant
    have : IsDominant (X := (C.bridge i).P.model (k + 1)) ((C.bridge i).P.gp k) :=
      hd.isBirationalMorphism_plus.isDominant
    have := isDominant_toBase C i k hk'.le
    have hdom := isDominant_toBase C i (k + 1) hk
    have hπ : (C.bridge i).P.toBase (k + 1) = (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.πY_eq k hk'
    have hπ' : (C.bridge i).P.toBase k = (C.bridge i).P.g k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.modelMap_eq k hk'
    have : IsDominant ((C.bridge i).P.h k) := by
      have : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := hπ ▸ hdom
      exact IsDominant.of_comp ((C.bridge i).P.gp k) _
    rw [← hQv, valuationOver_comp P _ _ hπ.symm, valuationOver_comp Pm _ _ hπ'.symm]
    exact congrArg (Valuation.comap _) hv.symm

/-- The support of `Θ^M` lies in the union of the centres `S_h^M` of the labels: a prime
divisor of `M` that is the centre of no label has coefficient `0` in `Θ^M`. -/
private theorem coeff_modelBoundary_eq_zero_of_forall_not_isLabelCentre (C : TerminalChain T)
    (x : C.ModelIndex) (P : MMP.Mori.PrimeDivisor (C.model x))
    (hP : ∀ S : C.Label, ¬ C.IsLabelCentre S x P) : (C.modelBoundary x).coeff P = 0 := by
  by_contra h
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨a, -, hΘ⟩ := (C.junction i).Θ_eq
    change (C.junction i).Θ P ≠ 0 at h
    rw [hΘ] at h
    obtain ⟨S, hS⟩ := exists_isLabelCentre_junction C i _ P h
    exact hP S hS
  · obtain ⟨Q, hQ, hv⟩ := bridge_support C i k k.2.le P h
    obtain ⟨a, -, hΘ⟩ := (C.bridge i).isDecreasedBoundary
    change (C.bridge i).Θ' Q ≠ 0 at hQ
    rw [hΘ] at hQ
    obtain ⟨S, w, hw, hQw⟩ := exists_isLabelCentre_junction C i _ Q hQ
    refine hP S ⟨w, hw, isDominant_toBase C i k k.2.le, ?_⟩
    have : IsDominant (X := (C.bridge i).P.model 0) (C.junction i).p :=
      (C.junction i).isBirationalMorphism.isDominant
    have := isDominant_toBase C i 0 (Nat.zero_le _)
    subst hQw
    rw [hv]
    exact valuationOver_comp (A := (C.bridge i).P.model 0) Q _ _ rfl

/-- The centre relation of a label is the centre map of the bijection
`primeDivisorEquivModel`. -/
private theorem exists_equiv_isLabelCentre_iff (C : TerminalChain T) (x : C.ModelIndex) :
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x),
      ∀ (S : C.Label) (P : MMP.Mori.PrimeDivisor (C.model x)),
        C.IsLabelCentre S x P ↔ e S.1 = P := by
  have he := TerminalChain.isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C x
  rcases x with ⟨i, _ | k⟩ <;> exact ⟨_, fun S P => he S.1 P⟩

/-- A label has at most one centre on a model. -/
private theorem eq_of_isLabelCentre {C : TerminalChain T} {x : C.ModelIndex} {S : C.Label}
    {P P' : MMP.Mori.PrimeDivisor (C.model x)} (h : C.IsLabelCentre S x P)
    (h' : C.IsLabelCentre S x P') : P = P' := by
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff C x
  exact ((he S P).1 h).symm.trans ((he S P').1 h')

/-- A prime divisor of a model is the centre of at most one label. -/
private theorem label_eq_of_isLabelCentre {C : TerminalChain T} {x : C.ModelIndex}
    {S S' : C.Label} {P : MMP.Mori.PrimeDivisor (C.model x)} (h : C.IsLabelCentre S x P)
    (h' : C.IsLabelCentre S' x P) : S = S' := by
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff C x
  exact Subtype.ext (e.injective (((he S P).1 h).trans ((he S' P).1 h').symm))

/-- **The labels carry the boundary.** For every model `(M, Θ^M)` of a terminal chain and every
family `b` of label coefficients `b_h^M` at `M`, `Θ^M = ∑_h b_h^M S_h^M`: the coefficient of
`Θ^M` at each prime divisor `P` of `M` is the sum of `b_h^M` over the labels `S_h` whose centre
`S_h^M` on `M` is `P`. -/
@[mmp "lem_oai4_c1_labels_support"]
public theorem coeff_modelBoundary_eq_finsum (C : TerminalChain T) (x : C.ModelIndex)
    (b : C.Label → ℚ) (hb : ∀ S, C.IsLabelCoefficient S x (b S))
    (P : MMP.Mori.PrimeDivisor (C.model x)) :
    (C.modelBoundary x).coeff P = ∑ᶠ (S : C.Label) (_ : C.IsLabelCentre S x P), b S := by
  classical
  by_cases h : ∃ S : C.Label, C.IsLabelCentre S x P
  · obtain ⟨S, hS⟩ := h
    rw [finsum_eq_single _ S fun S' hne => by
        rw [finsum_eq_if, if_neg fun h' => hne (label_eq_of_isLabelCentre h' hS)],
      finsum_eq_if, if_pos hS]
    rcases hb S with ⟨P', hP', hc⟩ | ⟨hn, _⟩
    · exact eq_of_isLabelCentre hS hP' ▸ hc
    · exact absurd hS (hn P)
  · push Not at h
    rw [coeff_modelBoundary_eq_zero_of_forall_not_isLabelCentre C x P h]
    exact (finsum_eq_zero_of_forall_eq_zero fun S => by rw [finsum_eq_if, if_neg (h S)]).symm

end TerminalChain

end StabilizedSmallKltTail

end MMP.Fourfold
