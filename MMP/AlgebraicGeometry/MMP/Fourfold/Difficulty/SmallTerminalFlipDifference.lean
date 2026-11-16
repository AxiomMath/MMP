module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FourfoldDefs
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SmallTerminalFlipBadSetFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.StepBranchesUnitDrop
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
import MMP.AlgebraicGeometry.MMP.Fourfold.NormalizationCycleRank
import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.SurfaceEchoLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
import MMP.AlgebraicGeometry.Normalization.IntegralScheme
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Difficulty change under a small terminal flip

Let `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` be a small terminal flip of a bridge of a prepared chain of fourfolds,
written as a step diagram `Y⁻ → Z ← Y⁺`, with weighted bad set `𝒜₀`. Away from the bad loci the
flip is an isomorphism, so the centres, branch numbers, default echo weights and weights of all
valuations outside `𝒜₀` match on both sides, and the change in the normalized label ranks is
cancelled by the change in the bad branch counts. Hence
`𝒟(Y⁻, Θ⁻) - 𝒟(Y⁺, Θ⁺) = ∑_{v ∈ 𝒜₀} (w_v(Y⁻, Θ⁻) - w_v(Y⁺, Θ⁺))`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.difficulty_sub_eq_finsum_flipBadSet`:
  the difference of the difficulties across a small terminal flip is the sum over the weighted
  bad set of the weight differences.

## Implementation notes

* A valuation `v` of `ℂ(Y⁻)` is identified with the valuation `v⁺` of `ℂ(Y⁺)` having the same
  restriction to `ℂ(Z)`, as in
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.flipBadSet`.
* Weights (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`) and
  difficulties (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`) are
  predicates on their values; the equality is stated for all values satisfying them. The sum is
  a `finsum` over `𝒜₀`, which is a finite set.
-/

@[expose] public section

section

universe u

namespace Proof_lem_oai4_c3_flip_difference

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold
  MMP.Fourfold.StabilizedSmallKltTail MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Label centres, label defaults and weights are unique -/

section Unique

variable {T : StabilizedSmallKltTail}

/-- On every model of a terminal chain, the centre relation of the labels is the centre map of a
bijection of prime divisors. -/
private theorem exists_equiv_isLabelCentre_iff (C : TerminalChain T) (x : C.ModelIndex) :
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x),
      ∀ (S : C.Label) (P : MMP.Mori.PrimeDivisor (C.model x)),
        C.IsLabelCentre S x P ↔ e S.1 = P := by
  have he := TerminalChain.isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C x
  rcases x with ⟨i, _ | k⟩ <;> exact ⟨_, fun S P => he S.1 P⟩

/-- Every label has a centre on every model of a terminal chain. -/
private theorem exists_isLabelCentre (C : TerminalChain T) (S : C.Label) (x : C.ModelIndex) :
    ∃ P, C.IsLabelCentre S x P := by
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff C x
  exact ⟨e S.1, (he S _).2 rfl⟩

/-- A label has at most one centre on a model of a terminal chain. -/
private theorem isLabelCentre_unique {C : TerminalChain T} {S : C.Label} {x : C.ModelIndex}
    {P P' : MMP.Mori.PrimeDivisor (C.model x)} (h : C.IsLabelCentre S x P)
    (h' : C.IsLabelCentre S x P') : P = P' := by
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff C x
  exact ((he S P).1 h).symm.trans ((he S P').1 h')

/-- The coefficient of a label on a model is unique. -/
private theorem isLabelCoefficient_unique {C : TerminalChain T} {S : C.Label} {x : C.ModelIndex}
    {b b' : ℚ} (h : C.IsLabelCoefficient S x b) (h' : C.IsLabelCoefficient S x b') : b = b' := by
  rcases h with ⟨P, hP, rfl⟩ | ⟨hn, rfl⟩ <;> rcases h' with ⟨P', hP', rfl⟩ | ⟨hn', rfl⟩
  · rw [isLabelCentre_unique hP hP']
  · exact absurd hP (hn' P)
  · exact absurd hP' (hn P')
  · rfl

/-- The default echo weight of a label on a model is unique. -/
private theorem isLabelDefault_unique {C : TerminalChain T} {N : ℕ} {S : C.Label}
    {x : C.ModelIndex} {d d' : ℕ} (h : C.IsLabelDefault N S x d)
    (h' : C.IsLabelDefault N S x d') : d = d' := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  rw [isLabelCoefficient_unique hb hb']

/-- The weight of a valuation on a model is unique. -/
private theorem isValuationWeight_unique {C : TerminalChain T} {N : ℕ} {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {n n' : ℕ}
    (h : C.IsValuationWeight N x v n) (h' : C.IsValuationWeight N x v n') : n = n' := by
  obtain ⟨-, a, ⟨m, D, -, hD, ha⟩, rfl⟩ := h
  obtain ⟨-, a', ⟨m', D', -, hD', ha'⟩, rfl⟩ := h'
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hD.trans hD'.symm)]

end Unique

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

namespace Flip

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

section DivisorOverModel

universe v

/-- A valuation `ξ'` of `k(X')` restricting on `k(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `k(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `k(X') ≅ k(Z) ≅ k(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq {X X' Z : Scheme.{v}}
    {k : Type v} [Field k] [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
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
private theorem exists_dominated_point_of_comap_eq {X X' Z : Scheme.{v}}
    {k : Type v} [Field k] [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
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
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq {X X' Z : Scheme.{v}}
    {k : Type v} [Field k] [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
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

end DivisorOverModel

section Setting

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
  [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]

/-- Two proper birational morphisms `f⁻ : X⁻ ⟶ Z ⟵ X⁺ : f⁺` of normal varieties over `ℂ` to a
normal variety. -/
private structure IsBirationalPair (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z) : Prop where
  isNormalVariety_minus : MMP.Mori.IsNormalVariety ℂ sXm
  isNormalVariety_plus : MMP.Mori.IsNormalVariety ℂ sXp
  isNormalVariety_target : MMP.Mori.IsNormalVariety ℂ sZ
  comp_eq_minus : fm ≫ sZ = sXm
  comp_eq_plus : fp ≫ sZ = sXp
  isProper_minus : IsProper fm
  isProper_plus : IsProper fp
  isBirationalMorphism_minus : IsBirationalMorphism fm
  isBirationalMorphism_plus : IsBirationalMorphism fp

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

private theorem IsBirationalPair.symm (h : IsBirationalPair sXm sZ sXp fm fp) :
    IsBirationalPair sXp sZ sXm fp fm :=
  ⟨h.isNormalVariety_plus, h.isNormalVariety_minus, h.isNormalVariety_target, h.comp_eq_plus,
    h.comp_eq_minus, h.isProper_plus, h.isProper_minus, h.isBirationalMorphism_plus,
    h.isBirationalMorphism_minus⟩

/-- A divisor `(W, h, E)` over `X`, with `h` proper, seen over `X'` through a proper birational
morphism `g : X ⟶ X'` over `ℂ`: the divisor `(W, g ∘ h, E)`. -/
private noncomputable def compProper {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) : DivisorOver ℂ sX' where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    rw [Category.assoc, hs]
    exact D.isNormalVariety
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := hD
    exact isBirationalMorphism_comp_of_isBirational g D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

private theorem valuation_compProper {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) :
    haveI := hg.isDominant
    (compProper g hg hs D hD).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := hg.isDominant
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- **The centres of corresponding valuations lie over the same point.** If `v⁺` is the valuation
of `k(X⁺)` with the same restriction to `k(Z)` as a valuation `v` of `k(X⁻)` with centre
`c_{X⁻}(v) = closure {x}`, then `v⁺` has a centre `closure {x⁺}` with `f⁺(x⁺) = f⁻(x)`. -/
private theorem exists_isCentre_of_comap_eq (h : IsBirationalPair sXm sZ sXp fm fp)
    [IsDominant fm] [IsDominant fp]
    {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))} {Zc : IrreducibleCloseds Xm}
    (hZ : MMP.Intersection.IsCentre ℂ sXm v Zc)
    {v' : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hv : v'.comap (functionFieldMap fp) = v.comap (functionFieldMap fm)) :
    ∃ (Zc' : IrreducibleCloseds Xp) (x : Xm) (x' : Xp), MMP.Intersection.IsCentre ℂ sXp v' Zc' ∧
      (Zc : Set Xm) = closure {x} ∧ (Zc' : Set Xp) = closure {x'} ∧ fp x' = fm x := by
  obtain ⟨D, hDp, rfl, rfl⟩ := hZ
  haveI := h.isProper_minus
  haveI := h.isProper_plus
  haveI : IsNormal Z := h.isNormalVariety_target.2
  haveI : IsLocallyNoetherian Z :=
    have := h.isNormalVariety_target.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨D', hD'p, hD'v⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq
    h.isNormalVariety_plus fm fp h.isBirationalMorphism_minus h.isBirationalMorphism_plus
    h.isProper_plus h.comp_eq_minus h.comp_eq_plus D v' (by rw [hv])
  refine ⟨D'.center, D.f D.E.genericPoint, D'.f D'.E.genericPoint,
    ⟨D', hD'p, hD'v.symm, rfl⟩, D.center_eq_closure_genericPoint,
    D'.center_eq_closure_genericPoint, ?_⟩
  have h1 := valuation_compProper fm h.isBirationalMorphism_minus h.comp_eq_minus D hDp
  have h2 := valuation_compProper fp h.isBirationalMorphism_plus h.comp_eq_plus D' hD'p
  exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq
    h.isNormalVariety_target.1
    (D := compProper fp h.isBirationalMorphism_plus h.comp_eq_plus D' hD'p)
    (D' := compProper fm h.isBirationalMorphism_minus h.comp_eq_minus D hDp)
    (by rw [h1, h2, hD'v, hv])

/-- The valuation of `k(X⁺)` corresponding to a valuation of `k(X⁻)` across
`k(X⁻) ≅ k(Z) ≅ k(X⁺)`. -/
private noncomputable def transport (h : IsBirationalPair sXm sZ sXp fm fp) [IsDominant fm]
    [IsDominant fp] (v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))) :
    Valuation Xp.functionField (WithZero (Multiplicative ℤ)) :=
  v.comap ((RingEquiv.ofBijective _
    h.isBirationalMorphism_minus.functionFieldMap_bijective).toRingHom.comp
    (RingEquiv.ofBijective _ h.isBirationalMorphism_plus.functionFieldMap_bijective).symm.toRingHom)

private theorem comap_transport (h : IsBirationalPair sXm sZ sXp fm fp) [IsDominant fm]
    [IsDominant fp] (v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))) :
    (transport h v).comap (functionFieldMap fp) = v.comap (functionFieldMap fm) := by
  ext t
  simp only [transport, Valuation.comap_apply, RingHom.coe_comp, Function.comp_apply]
  congr 1
  change functionFieldMap fm ((RingEquiv.ofBijective _
    h.isBirationalMorphism_plus.functionFieldMap_bijective).symm
      ((RingEquiv.ofBijective _ h.isBirationalMorphism_plus.functionFieldMap_bijective) t)) = _
  rw [RingEquiv.symm_apply_apply]

private theorem eq_transport_of_comap_eq (h : IsBirationalPair sXm sZ sXp fm fp) [IsDominant fm]
    [IsDominant fp] {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hv : v'.comap (functionFieldMap fp) = v.comap (functionFieldMap fm)) : v' = transport h v :=
  valuation_eq_of_comap_eq h.isBirationalMorphism_plus.functionFieldMap_bijective.2
    (hv.trans (comap_transport h v).symm)

private theorem transport_symm_transport (h : IsBirationalPair sXm sZ sXp fm fp) [IsDominant fm]
    [IsDominant fp] (v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))) :
    transport h.symm (transport h v) = v :=
  (eq_transport_of_comap_eq h.symm (comap_transport h v).symm).symm

end Setting

/-! ### Points over the common biregular locus -/

section Biregular

variable {X Y : Scheme.{0}}

/-- A morphism is injective over an open `V` over which it is an isomorphism. -/
private theorem eq_of_map_eq_of_isBiregular {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V)
    {x y : X} (hx : f x ∈ V) (hxy : f x = f y) : x = y := by
  have : IsIso (f ∣_ V) := hV
  have hy : f y ∈ V := hxy ▸ hx
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by
    rw [morphismRestrict_ι]
    rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by
    rw [morphismRestrict_ι]
    rfl
  exact congrArg Subtype.val
    (((f ∣_ V) ≫ V.ι).isOpenEmbedding.injective (hp.trans (hxy.trans hq.symm)))

/-- A morphism preserves the coheight of points over an open over which it is an isomorphism. -/
private theorem coheight_map_of_isBiregular {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V)
    {x : X} (hx : f x ∈ V) : Order.coheight (f x) = Order.coheight x :=
  MMP.Positivity.coheight_map_of_mem_biregularLocus f (le_biregularLocus hV hx)

/-- A morphism is surjective over an open over which it is an isomorphism. -/
private theorem exists_map_eq_of_isBiregular {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V)
    {z : Y} (hz : z ∈ V) : ∃ x, f x = z := by
  have : IsIso (f ∣_ V) := hV
  obtain ⟨p, rfl⟩ : z ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hz
  let q : (f ⁻¹ᵁ V).toScheme := (inv (f ∣_ V)) p
  have hq : (f ∣_ V) q = p := by
    change (inv (f ∣_ V) ≫ (f ∣_ V)) p = p
    rw [IsIso.inv_hom_id]
    rfl
  refine ⟨(f ⁻¹ᵁ V).ι q, ?_⟩
  have h3 : ((f ∣_ V) ≫ V.ι) q = f ((f ⁻¹ᵁ V).ι q) := by rw [morphismRestrict_ι]; rfl
  rw [← h3, Scheme.Hom.comp_apply, hq]

end Biregular

end Flip

namespace Flip

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold
  MMP.Fourfold.StabilizedSmallKltTail MMP.Fourfold.StabilizedSmallKltTail.TerminalChain
  MMP.Fourfold.StabilizedSmallKltTail.PreparedChain MMP.Mori
open Order

section Biregular

open MMP.Mori MMP.Fourfold

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over every point
with finite fibre. -/
private theorem mem_biregularLocus_of_finite {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hb : IsBirationalMorphism f) {z : Z}
    (hz : (f ⁻¹' {z}).Finite) : z ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hz

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over the generic
point of every prime divisor: the local ring there is a discrete valuation ring, so the fibre is
a single point. -/
private theorem genericPoint_mem_biregularLocus_of_primeDivisor {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor Y) :
    P.genericPoint ∈ biregularLocus f :=
  haveI := hf.isDominant
  haveI := P.isDiscreteValuationRing_localRing
  mem_biregularLocus_of_finite f hf (Set.Subsingleton.finite fun _ ha _ hb =>
    eq_of_map_eq_of_valuationRing hf.functionFieldMap_bijective ha hb)

/-- A proper birational morphism onto a normal variety is an isomorphism over every point of
codimension one. -/
private theorem mem_biregularLocus_of_coheight_eq_one {X Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral X] (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hb : IsBirationalMorphism f) {z : Z} (hz : Order.coheight z = 1) : z ∈ biregularLocus f := by
  haveI := hZ.1.toIsIntegral
  haveI := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  rw [← AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hz]
  exact genericPoint_mem_biregularLocus_of_primeDivisor f hb _

/-- A morphism whose exceptional set has codimension at least two is biregular over the generic
point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus_of_two_le {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : AlgebraicGeometry.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f :=
  not_not.mp fun hc => by
    have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 (mem_exceptionalSet.mpr hc)
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
    exact absurd this (by decide)

/-- If the exceptional set of `f` has codimension at least two, then `f` and every proper
birational `g` onto the same normal variety are isomorphisms over the image of the generic point
of a prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {X Y Z : Scheme.{0}} [IsIntegral Y]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f))
    (g : Y ⟶ Z) [IsProper g] (hb : IsBirationalMorphism g)
    (P : AlgebraicGeometry.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f ∧ f P.genericPoint ∈ biregularLocus g := by
  have h1 := map_genericPoint_mem_biregularLocus_of_two_le h2 P
  refine ⟨h1, mem_biregularLocus_of_coheight_eq_one hZ g hb ?_⟩
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f h1,
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]

/-- Precomposing with an isomorphism does not shrink the biregular locus. -/
private theorem biregularLocus_le_biregularLocus_comp {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus f ≤ biregularLocus (φ ≫ f) :=
  sSup_le fun V hV => le_biregularLocus (by
    have : IsIso (f ∣_ V) := hV
    change IsIso ((φ ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    have h2 : IsIso (φ ∣_ (f ⁻¹ᵁ V)) := by infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)

/-- Precomposing with an isomorphism does not change the biregular locus. -/
private theorem biregularLocus_comp_of_isIso {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus (φ ≫ f) = biregularLocus f := by
  refine le_antisymm ?_ (biregularLocus_le_biregularLocus_comp φ f)
  have := biregularLocus_le_biregularLocus_comp (inv φ) (φ ≫ f)
  rwa [IsIso.inv_hom_id_assoc] at this

end Biregular

section BadLocus

open MMP.Mori

/-- A small morphism onto a normal scheme is an isomorphism over the points of codimension at
most one: every point outside its biregular locus has coheight at least two. -/
private theorem two_le_coheight_of_notMem_biregularLocus {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {g : X ⟶ Z} (hg : IsSmallMorphism sX sZ g) {z : Z}
    (hz : z ∉ biregularLocus g) : 2 ≤ coheight z := by
  haveI := hg.isProper
  haveI := hg.isBirationalMorphism.isDominant
  by_contra h
  exact hz (MMP.Positivity.mem_biregularLocus_of_coheight_le_one g
    hg.isBirationalMorphism.functionFieldMap_bijective hg.two_le_codimension
    (Order.le_of_lt_add_one (not_le.mp h)))

/-- A point `y` of `X` mapping into a set of points of coheight at least two under `φ ≫ g`, with
`φ` an isomorphism and `g` of exceptional set of codimension at least two, has coheight at least
two. -/
private theorem two_le_coheight_of_comp_mem {A X Z : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (g : X ⟶ Z) (hg : 2 ≤ closedsCodimension (exceptionalSet g)) {T : Set Z}
    (hT : ∀ z ∈ T, 2 ≤ coheight z) {y : A} (hy : (φ ≫ g) y ∈ T) : 2 ≤ coheight y := by
  rw [← Topology.IsOpenEmbedding.coheight_eq _ φ.isOpenEmbedding]
  by_cases hb : g (φ y) ∈ biregularLocus g
  · rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g hb]
    exact hT _ hy
  · exact MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hg (mem_exceptionalSet.mpr hb)

/-- **The bad locus of the base has codimension at least two.** For small morphisms
`f⁻ : X⁻ ⟶ Z` and `g : X⁺ ⟶ Z` onto a normal scheme and `f⁺ = φ ≫ g` with `φ` an isomorphism,
every point of `Σ = Z ∖ U` has coheight at least two. -/
private theorem two_le_coheight_of_mem_badLocusBase {Xm Xp A Z : Scheme.{0}} [IsIntegral Xm]
    [IsIntegral Xp] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {fm : Xm ⟶ Z}
    {g : Xp ⟶ Z} (hm : IsSmallMorphism sXm sZ fm) (hp : IsSmallMorphism sXp sZ g)
    (φ : A ⟶ Xp) [IsIso φ] {z : Z} (hz : z ∈ (badLocusBase fm (φ ≫ g) : Set Z)) :
    2 ≤ coheight z := by
  rw [coe_badLocusBase, Set.mem_compl_iff, commonBiregularLocus] at hz
  by_cases h1 : z ∈ biregularLocus fm
  · refine two_le_coheight_of_notMem_biregularLocus hp fun h2 => hz ⟨h1, ?_⟩
    exact biregularLocus_le_biregularLocus_comp φ g h2
  · exact two_le_coheight_of_notMem_biregularLocus hm h1

end BadLocus

section Chain

open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a programme
is compatible with their structure morphisms. -/
private theorem eqToHom_comp_modelStr {V : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (sY : ∀ k, Y k ⟶ Spec (.of ℂ)) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V Y) h) ≫ modelStr sV sY b = modelStr sV sY a := by
  subst h
  simp

/-- The morphism `V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge of a terminal chain is
proper and birational, lies over `ℂ`, and is an isomorphism over the image of the generic point of
every prime divisor, as is `g_k : V_k ⟶ T_k`. -/
private theorem flipTargetMapOf_properties {T : StabilizedSmallKltTail} (C : TerminalChain T)
    (i : ℕ)
    (k : Fin (C.bridge i).P.m) (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) :
    IsProper (C.flipTargetMapOf i k d) ∧ IsBirationalMorphism (C.flipTargetMapOf i k d) ∧
      C.flipTargetMapOf i k d ≫ (C.bridge i).P.sT k = C.modelStructure (C.flipTargetOf i k d) ∧
      ∀ P : AlgebraicGeometry.PrimeDivisor (C.model (C.flipTargetOf i k d)),
        C.flipTargetMapOf i k d P.genericPoint ∈
          commonBiregularLocus ((C.bridge i).P.g k) (C.flipTargetMapOf i k d) := by
  have hD := (C.bridge i).P.isFourfoldStepDiagram k k.2
  have hZ := hD.isNormalVariety_target
  haveI := C.isIntegral_flipBase i k
  haveI : IsNormal ((C.bridge i).P.T k) := hZ.2
  haveI : LocallyOfFiniteType ((C.bridge i).P.sT k) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian ((C.bridge i).P.T k) :=
    LocallyOfFiniteType.isLocallyNoetherian ((C.bridge i).P.sT k)
  haveI : IsProper ((C.bridge i).P.g k) :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper ((C.bridge i).P.gp k) := hD.isSmallMorphism_plus.isProper
  have hsp := hD.isSmallMorphism_plus
  have key : ∀ x : (C.bridge i).P.Y k, Order.coheight x = 1 →
      (C.bridge i).P.gp k x ∈ commonBiregularLocus ((C.bridge i).P.g k) ((C.bridge i).P.gp k) :=
    fun x hx => by
      have h := map_genericPoint_mem_biregularLocus hZ ((C.bridge i).P.gp k)
        hsp.two_le_codimension ((C.bridge i).P.g k) hD.isBirationalMorphism_minus
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx)
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at h
      exact ⟨h.2, h.1⟩
  cases d with
  | isTrue h =>
    exact ⟨hsp.isProper, hsp.isBirationalMorphism, hD.comp_eq_plus, fun P =>
      key _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)⟩
  | isFalse h =>
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)
    change IsProper (ψ.hom ≫ (C.bridge i).P.gp k) ∧
      IsBirationalMorphism (ψ.hom ≫ (C.bridge i).P.gp k) ∧
      (ψ.hom ≫ (C.bridge i).P.gp k) ≫ (C.bridge i).P.sT k =
        (C.junction (i + 1)).p ≫ T.sX (i + 1) ∧
      ∀ P : AlgebraicGeometry.PrimeDivisor (C.junction (i + 1)).Y,
        (ψ.hom ≫ (C.bridge i).P.gp k) P.genericPoint ∈
          commonBiregularLocus ((C.bridge i).P.g k) (ψ.hom ≫ (C.bridge i).P.gp k)
    refine ⟨inferInstance, ?_, ?_, fun P => ?_⟩
    · exact isBirationalMorphism_comp_of_isBirational _ _
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hsp.isBirationalMorphism)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso ψ.hom))
    · rw [Category.assoc, hD.comp_eq_plus]
      change ((C.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)) ≫
        modelStr (C.junction i).sY (C.bridge i).P.sY (k.1 + 1) = (C.junction (i + 1)).sY
      rw [Category.assoc, eqToHom_comp_modelStr _ _ hmk]
      exact (Iso.inv_comp_eq _).2 (C.bridge i).comp_sY.symm
    · have hx : ψ.hom P.genericPoint ∈ biregularLocus ψ.hom :=
        le_biregularLocus (V := ⊤) (inferInstance : IsIso (ψ.hom ∣_ ⊤)) trivial
      have h1 := key (ψ.hom P.genericPoint) (by
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus ψ.hom hx,
          AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
      change (C.bridge i).P.gp k (ψ.hom P.genericPoint) ∈ biregularLocus ((C.bridge i).P.g k) ⊓
        biregularLocus (ψ.hom ≫ (C.bridge i).P.gp k)
      rw [biregularLocus_comp_of_isIso]
      exact h1

end Chain

section ChainBadLocus

/-- The morphism `Y⁺ ⟶ T_k` of a flip of a bridge is `g_k⁺` precomposed with an
isomorphism. -/
private theorem exists_isIso_flipTargetMap_eq {T : StabilizedSmallKltTail} (C : TerminalChain T)
    (i : ℕ)
    (k : Fin (C.bridge i).P.m) :
    ∃ (φ : C.model (C.flipTarget i k) ⟶ (C.bridge i).P.Y k) (_ : IsIso φ),
      C.flipTargetMap i k = φ ≫ (C.bridge i).P.gp k := by
  unfold TerminalChain.flipTarget TerminalChain.flipTargetMap
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h => exact ⟨𝟙 ((C.bridge i).P.Y k), IsIso.id _, (Category.id_comp _).symm⟩
  | isFalse h =>
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y)
        (by omega : (C.bridge i).P.m = k.1 + 1))
    exact ⟨ψ.hom, ψ.isIso_hom, (Category.assoc _ _ _).symm⟩

/-- **The bad loci of a flip move have codimension at least two.** Both maps of the step
diagram `Y⁻ → Z ← Y⁺` of a flip move of a prepared chain are small onto a normal base, so every
point of the bad loci `W⁻ ⊆ Y⁻` and `W⁺ ⊆ Y⁺` has coheight at least two. -/
private theorem two_le_coheight_of_mem_badLoci {T : StabilizedSmallKltTail} (Q : PreparedChain T)
    (μ : Q.FlipMove) :
    (∀ y ∈ (μ.badLocusSource : Set (Q.chain.model μ.source.1)), 2 ≤ coheight y) ∧
      ∀ y ∈ (μ.badLocusTarget : Set (Q.chain.model μ.target.1)), 2 ≤ coheight y := by
  have hD := (Q.chain.bridge μ.1.1).P.isFourfoldStepDiagram μ.1.2 μ.1.2.2
  have hsm : IsSmallMorphism _ _ μ.sourceMap := (Q.chain.bridge μ.1.1).isSmallMorphism μ.1.2 μ.1.2.2
  have hsp := hD.isSmallMorphism_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsNormal μ.base := hZ.2
  haveI : LocallyOfFiniteType ((Q.chain.bridge μ.1.1).P.sT μ.1.2) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian μ.base :=
    LocallyOfFiniteType.isLocallyNoetherian ((Q.chain.bridge μ.1.1).P.sT μ.1.2)
  obtain ⟨φ, hφ, hft⟩ := exists_isIso_flipTargetMap_eq Q.chain μ.1.1 μ.1.2
  have hft' : μ.targetMap = φ ≫ (Q.chain.bridge μ.1.1).P.gp μ.1.2 := hft
  have hbase : ∀ z ∈ (badLocusBase μ.sourceMap μ.targetMap : Set μ.base), 2 ≤ coheight z :=
    fun z hz => two_le_coheight_of_mem_badLocusBase hsm hsp φ (hft' ▸ hz)
  exact ⟨fun y hy => two_le_coheight_of_comp_mem (𝟙 _) μ.sourceMap hsm.two_le_codimension hbase
      (by rw [Category.id_comp]; exact hy),
    fun y hy => two_le_coheight_of_comp_mem φ _ hsp.two_le_codimension hbase
      (by rw [← hft']; exact hy)⟩

end ChainBadLocus

end Flip

namespace Iso

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

section IsoBlock

/-! ### Valuations of prime divisors -/

/-- The image of a prime divisor under an isomorphism. -/
private noncomputable def mapOfIso {V W : Scheme.{0}} (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor W :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e.hom Q.genericPoint) (by
    rw [coheight_eq_of_isOpenImmersion e.hom]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)

private theorem genericPoint_mapOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) : (mapOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- Transport of prime divisors along an isomorphism. -/
private noncomputable def primeDivisorEquivOfIso {V W : Scheme.{0}} (e : V ≅ W) :
    MMP.Mori.PrimeDivisor V ≃ MMP.Mori.PrimeDivisor W where
  toFun := mapOfIso e
  invFun := mapOfIso e.symm
  left_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e.symm (mapOfIso e Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp
  right_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e (mapOfIso e.symm Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp

/-! ### Prime divisors and normalizations along an isomorphism -/

section IsoDivisors

variable {V W : Scheme.{0}}

/-- An isomorphism carries the closure of a point to the closure of its image. -/
private theorem image_closure_singleton (e : V ≅ W) (x : V) :
    e.hom.base '' closure ({x} : Set V) = closure {e.hom x} := by
  have := (Scheme.homeoOfIso e).image_closure ({x} : Set V)
  rwa [Set.image_singleton] at this

private theorem inv_hom_apply (e : V ≅ W) (x : W) : e.hom (e.inv x) = x := by
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

/-- Along an isomorphism `e`, the image of a preimage under `e.hom ≫ g` is the preimage
under `g`. -/
private theorem image_preimage_comp {Z : Scheme.{0}} (e : V ≅ W) (g : W ⟶ Z) (s : Set Z) :
    e.hom.base '' ((e.hom ≫ g).base ⁻¹' s) = g.base ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hy
    refine ⟨e.inv y, ?_, inv_hom_apply e y⟩
    rw [Set.mem_preimage, Scheme.Hom.comp_apply, inv_hom_apply]
    exact hy

/-- The support of a transported prime divisor is the image of the support. -/
private theorem support_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    (primeDivisorEquivOfIso e P).support = e.hom.base '' P.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure, image_closure_singleton]
  exact congrArg (fun x => closure {x}) (genericPoint_mapOfIso e P)

private theorem primeDivisorEquivOfIso_symm_apply (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    primeDivisorEquivOfIso e.symm (primeDivisorEquivOfIso e P) = P :=
  (primeDivisorEquivOfIso e).left_inv P

/-- The ideal sheaf of a transported prime divisor is the image of the ideal sheaf. -/
private theorem idealSheaf_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    P.idealSheaf.map e.hom = (primeDivisorEquivOfIso e P).idealSheaf := by
  have := P.integral
  have := (primeDivisorEquivOfIso e P).integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme P.idealSheaf _ rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      (primeDivisorEquivOfIso e P).idealSheaf _ rfl, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  change closure (e.hom.base '' P.support) = (primeDivisorEquivOfIso e P).support
  rw [support_primeDivisorEquivOfIso]
  exact ((Scheme.homeoOfIso e).isClosedMap _ P.idealSheaf.support.isClosed).closure_eq

/-- The closed subschemes of a prime divisor and of its transport are isomorphic. -/
private noncomputable def subschemeIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    P.idealSheaf.subscheme ≅ (primeDivisorEquivOfIso e P).idealSheaf.subscheme where
  hom := P.idealSheaf.subschemeMap (primeDivisorEquivOfIso e P).idealSheaf e.hom
    (idealSheaf_primeDivisorEquivOfIso e P).ge
  inv := (primeDivisorEquivOfIso e P).idealSheaf.subschemeMap P.idealSheaf e.inv (by
    have h := idealSheaf_primeDivisorEquivOfIso e.symm (primeDivisorEquivOfIso e P)
    rw [primeDivisorEquivOfIso_symm_apply] at h
    exact h.ge)
  hom_inv_id := by
    rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp
  inv_hom_id := by
    rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp

private theorem subschemeIso_hom_ι (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    (subschemeIso e P).hom ≫ (primeDivisorEquivOfIso e P).idealSheaf.subschemeι =
      P.idealSheaf.subschemeι ≫ e.hom :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ (idealSheaf_primeDivisorEquivOfIso e P).ge

/-- Isomorphic schemes have isomorphic normalizations, compatibly with the normalization
morphisms. -/
private theorem exists_iso_normalizationScheme_of_iso {X X' : Scheme}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hX' : ∀ U : X'.Opens, IsCompact (U : Set X') → (irreducibleComponents U).Finite)
    (e : X ≅ X') :
    ∃ E : X.normalizationScheme hX ≅ X'.normalizationScheme hX',
      E.hom ≫ X'.normalization hX' = X.normalization hX ≫ e.hom := by
  have hgen : ∀ {Y Y' : Scheme} (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite) (e : Y ≅ Y') (η : genericPoints (Y.normalizationScheme hY)),
      (Y.normalization hY ≫ e.hom) η.1 ∈ genericPoints Y' := fun hY e η =>
    genericPoints_image_of_generalizingMap _ (Scheme.homeoOfIso e).isOpenEmbedding.generalizingMap
      (Scheme.normalization_mem_genericPoints _ hY η.2)
  have := X.isNormal_normalizationScheme hX
  have := X'.isNormal_normalizationScheme hX'
  obtain ⟨a, ha, -⟩ := Scheme.existsUnique_lift_normalization hX' _ (hgen hX e)
  obtain ⟨b, hb, -⟩ := Scheme.existsUnique_lift_normalization hX _ (hgen hX' e.symm)
  obtain ⟨g, -, hu⟩ := Scheme.existsUnique_lift_normalization hX (X.normalization hX)
    (fun η => Scheme.normalization_mem_genericPoints _ hX η.2)
  obtain ⟨g', -, hu'⟩ := Scheme.existsUnique_lift_normalization hX' (X'.normalization hX')
    (fun η => Scheme.normalization_mem_genericPoints _ hX' η.2)
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [hu (a ≫ b) (by dsimp only; rw [Category.assoc, hb, ← Category.assoc, ha]; simp),
      hu (𝟙 _) (by dsimp only; simp)]
  · rw [hu' (b ≫ a) (by dsimp only; rw [Category.assoc, ha, ← Category.assoc, hb]; simp),
      hu' (𝟙 _) (by dsimp only; simp)]

/-- The normalizations of a prime divisor and of its transport are isomorphic over the
isomorphism. -/
private theorem exists_iso_primeDivisorNormalizationScheme (e : V ≅ W)
    (P : MMP.Mori.PrimeDivisor V) :
    ∃ E : primeDivisorNormalizationScheme P ≅
        primeDivisorNormalizationScheme (primeDivisorEquivOfIso e P),
      E.hom ≫ primeDivisorNormalization (primeDivisorEquivOfIso e P) =
        primeDivisorNormalization P ≫ e.hom := by
  have := P.integral
  have := (primeDivisorEquivOfIso e P).integral
  obtain ⟨E, hE⟩ := exists_iso_normalizationScheme_of_iso
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) (subschemeIso e P)
  refine ⟨E, ?_⟩
  change E.hom ≫ (Scheme.normalization _ _ ≫ Scheme.IdealSheafData.subschemeι _) =
    (Scheme.normalization _ _ ≫ Scheme.IdealSheafData.subschemeι _) ≫ e.hom
  rw [← Category.assoc, hE, Category.assoc, subschemeIso_hom_ι, Category.assoc]

/-- **Branches through an isomorphism.** An isomorphism `e : V ≅ W` identifies the prime
divisors of the normalizations of `P` and of its transport `e(P)`, and the image in `W` of a
branch of `e(P)` is the `e`-image of the image in `V` of the corresponding branch of `P`. So the
branches whose images satisfy conditions `C'` on `W` and `C` on `V`, matched under `e`, are equally
many. -/
private theorem ncard_branch_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V)
    (C : Set V → Prop) (C' : Set W → Prop) (hC : ∀ A, C' (e.hom.base '' A) ↔ C A) :
    {R' : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme (primeDivisorEquivOfIso e P)) |
        C' (primeDivisorNormalization (primeDivisorEquivOfIso e P) '' R'.support)}.ncard =
      {R : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
        C (primeDivisorNormalization P '' R.support)}.ncard := by
  obtain ⟨E, hE⟩ := exists_iso_primeDivisorNormalizationScheme e P
  have key : ∀ R : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P),
      primeDivisorNormalization (primeDivisorEquivOfIso e P) ''
          (primeDivisorEquivOfIso E R).support =
        e.hom.base '' (primeDivisorNormalization P '' R.support) := by
    intro R
    rw [support_primeDivisorEquivOfIso, Set.image_image, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    simpa using congrArg (fun f => f.base x) hE
  rw [← Set.ncard_image_of_injective _ (primeDivisorEquivOfIso E).injective]
  congr 1
  ext R'
  obtain ⟨R, rfl⟩ := (primeDivisorEquivOfIso E).surjective R'
  simp only [Set.mem_setOf_eq, Set.mem_image, (primeDivisorEquivOfIso E).injective.eq_iff,
    exists_eq_right, key, hC]

/-- **Branch numbers are invariant under isomorphism.** -/
private theorem branchNumber_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V)
    (Z : Set V) :
    branchNumber (primeDivisorEquivOfIso e P) (e.hom.base '' Z) = branchNumber P Z :=
  ncard_branch_primeDivisorEquivOfIso e P (· = Z) (· = e.hom.base '' Z) fun _ =>
    (Set.image_injective.mpr (Scheme.homeoOfIso e).injective).eq_iff

/-- **Bad branch counts are invariant under isomorphism.** -/
private theorem badBranchCount_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V)
    (Z : Set V) :
    badBranchCount (primeDivisorEquivOfIso e P) (e.hom.base '' Z) = badBranchCount P Z :=
  ncard_branch_primeDivisorEquivOfIso e P (· ⊆ Z) (· ⊆ e.hom.base '' Z) fun _ =>
    Set.image_subset_image_iff (Scheme.homeoOfIso e).injective

/-- **Divisor cycle ranks are invariant under isomorphism over `ℂ`.** -/
private theorem divisorCycleRank_eq_of_iso {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [X'.Over (Spec (.of ℂ))] [MMP.IsComplexScheme X]
    [MMP.IsComplexScheme X'] (E : X ≅ X')
    (hE : E.hom ≫ (X' ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ)) :
    MMP.Analytic.divisorCycleRank X = MMP.Analytic.divisorCycleRank X' :=
  (MMP.Analytic.cycleRank_eq_of_iso E hE).2.2.2 2

end IsoDivisors

/-! ### Finite sums -/

/-- A finsum over `s` whose support in `s` lies in a finite set `t` is a sum over `t`. -/
private theorem natCast_finsum_mem_eq_sum {α : Type*} {f : α → ℕ} {s : Set α} (t : Finset α)
    (h : s ∩ Function.support f ⊆ t) [DecidablePred (· ∈ s)] :
    ((∑ᶠ a ∈ s, f a : ℕ) : ℤ) = ∑ a ∈ t, if a ∈ s then (f a : ℤ) else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (by rwa [Set.support_indicator]),
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- `natCast_finsum_mem_eq_sum` for a sum over the values satisfying a predicate. -/
private theorem natCast_finsum_eq_sum {α : Type*} {f : α → ℕ} {P : α → Prop} (t : Finset α)
    (h : ∀ a, P a → f a ≠ 0 → a ∈ t) [DecidablePred P] :
    ((∑ᶠ (a) (_ : P a), f a : ℕ) : ℤ) = ∑ a ∈ t, if P a then (f a : ℤ) else 0 :=
  natCast_finsum_mem_eq_sum (s := {a | P a}) t fun a ⟨ha, hne⟩ => h a ha hne

/-- A sum over the values satisfying `P` is a sum along an injection `g` whose image is the set
of values satisfying `P`. -/
private theorem finsum_eq_finsum_comp_of_injective {α β M : Type*} [AddCommMonoid M]
    {f : β → M} {P : β → Prop} {R : α → Prop} {g : α → β} (hg : Function.Injective g)
    (h : ∀ b, P b ↔ ∃ a, R a ∧ g a = b) :
    ∑ᶠ (b) (_ : P b), f b = ∑ᶠ (a) (_ : R a), f (g a) := by
  have hs : {b | P b} = g '' {a | R a} := Set.ext h
  have := finsum_mem_image (f := f) (s := {a | R a}) hg.injOn
  rwa [← hs] at this

end IsoBlock

end Iso

namespace Flip

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

section Transport2

/-- The strict transform along `φ ≫ g`, for an isomorphism `φ`, is the transport along `φ` of
the strict transform along `g`. -/
private theorem flipTransformPrimeDivisor_iso_comp {Xm V A Z : Scheme.{0}} (fm : Xm ⟶ Z)
    (g : V ⟶ Z) (φ : A ≅ V) {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor A}
    (h : flipTransformPrimeDivisor fm (φ.hom ≫ g) S = some S') :
    flipTransformPrimeDivisor fm g S = some (Iso.primeDivisorEquivOfIso φ S') := by
  unfold flipTransformPrimeDivisor at h ⊢
  obtain ⟨Q, hQ, hQ'⟩ := Option.bind_eq_some_iff.mp h
  rw [hQ, Option.bind_some]
  obtain ⟨hne, hI⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp hQ'
  have hV : biregularLocus (φ.hom ≫ g) = biregularLocus g := biregularLocus_comp_of_isIso φ.hom g
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨hV ▸ hne, ?_⟩
  rw [← Iso.idealSheaf_primeDivisorEquivOfIso, hI, inverseTransformIdeal, inverseTransformIdeal,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  change closure (φ.hom.base '' (inverseTransform (φ.hom ≫ g) Q.idealSheaf.support : Set A)) =
    (inverseTransform g Q.idealSheaf.support : Set V)
  rw [inverseTransform, inverseTransform, Closeds.coe_closure, Closeds.coe_closure, hV]
  change closure ((Scheme.homeoOfIso φ) '' closure _) = _
  rw [(Scheme.homeoOfIso φ).image_closure, closure_closure]
  congr 1
  exact Iso.image_preimage_comp φ g _

/-- The normalization of a prime divisor of a scheme locally of finite type over a field is
finite. -/
private theorem isFinite_primeDivisorNormalization {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) :
    IsFinite (primeDivisorNormalization S) := by
  have := S.integral
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType S.idealSheaf.subscheme
      (S.idealSheaf.subschemeι ≫ sY) _
  infer_instance

/-- Under a closed map, the image of the support of a prime divisor is the closure of the image
of its generic point. -/
private theorem image_support_eq_closure {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : IsClosedMap f)
    (P : MMP.Mori.PrimeDivisor X) : f '' P.support = closure {f P.genericPoint} := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← hf.closure_image_eq_of_continuous f.continuous, Set.image_singleton]

/-- For a closed map `ν`, the branch number of `S` along `closure {x}` counts the prime divisors
whose generic point maps to `x`. -/
private theorem branchNumber_eq_ncard {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) (x : Y) :
    branchNumber S (closure {x}) =
      {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
        primeDivisorNormalization S P.genericPoint = x}.ncard := by
  have := isFinite_primeDivisorNormalization sY S
  unfold branchNumber
  congr 1
  ext P
  simp only [Set.mem_setOf_eq]
  rw [image_support_eq_closure _ (primeDivisorNormalization S).isClosedMap]
  exact ⟨fun h => (inseparable_iff_closure_eq.mpr h).eq, fun h => h ▸ rfl⟩

end Transport2

end Flip

namespace Flip

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

section Correspondence

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
  [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- **Centres off the bad loci.** Over an open `U` of `Z` over which both `f⁻` and `f⁺` are
isomorphisms, a valuation has centre `closure {x}`, `f⁻(x) ∈ U`, exactly when the transported
valuation has centre `closure {x'}`, for the point `x'` with `f⁺(x') = f⁻(x)`. -/
private theorem isCentre_closure_iff (h : IsBirationalPair sXm sZ sXp fm fp)
    [IsDominant fm] [IsDominant fp] {U : Z.Opens} (hUm : IsBiregular fm U)
    (hUp : IsBiregular fp U) {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {x : Xm} (hx : fm x ∈ U) {x' : Xp} (hx' : fp x' = fm x) :
    (∃ Zc : IrreducibleCloseds Xm, MMP.Intersection.IsCentre ℂ sXm v Zc ∧
        (Zc : Set Xm) = closure {x}) ↔
      ∃ Zc' : IrreducibleCloseds Xp, MMP.Intersection.IsCentre ℂ sXp (transport h v) Zc' ∧
        (Zc' : Set Xp) = closure {x'} := by
  constructor
  · rintro ⟨Zc, hZ, hZx⟩
    obtain ⟨Zc', y, y', hZ', hZy, hZ'y', hyy⟩ := exists_isCentre_of_comap_eq h hZ
      (comap_transport h v)
    have hxy : y = x := (inseparable_iff_closure_eq.mpr (hZy.symm.trans hZx)).eq
    subst hxy
    have : y' = x' := eq_of_map_eq_of_isBiregular hUp (hyy ▸ hx) (hyy.trans hx'.symm)
    exact ⟨Zc', hZ', this ▸ hZ'y'⟩
  · rintro ⟨Zc', hZ', hZ'x'⟩
    obtain ⟨Zc, y', y, hZ, hZy', hZy, hyy⟩ := exists_isCentre_of_comap_eq h.symm hZ'
      (comap_transport h.symm _)
    rw [transport_symm_transport] at hZ
    have hxy : y' = x' := (inseparable_iff_closure_eq.mpr (hZy'.symm.trans hZ'x')).eq
    subst hxy
    have : x = y := eq_of_map_eq_of_isBiregular hUm hx (hx'.symm.trans hyy.symm)
    exact ⟨Zc, hZ, this ▸ hZy⟩

/-- A valuation has centre `V = closure {x}`, `f⁻(x) ∈ U`, iff its transport has centre
`V' = closure {x'}`, where `f⁺(x') = f⁻(x)`. -/
private theorem isCentre_iff_isCentre_transport (h : IsBirationalPair sXm sZ sXp fm fp)
    [IsDominant fm] [IsDominant fp] {U : Z.Opens} (hUm : IsBiregular fm U)
    (hUp : IsBiregular fp U) {x : Xm} (hx : fm x ∈ U) {x' : Xp} (hx' : fp x' = fm x)
    {V : IrreducibleCloseds Xm} {V' : IrreducibleCloseds Xp} (hV : (V : Set Xm) = closure {x})
    (hV' : (V' : Set Xp) = closure {x'})
    (v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))) :
    MMP.Intersection.IsCentre ℂ sXm v V ↔ MMP.Intersection.IsCentre ℂ sXp (transport h v) V' := by
  have key := isCentre_closure_iff h hUm hUp (v := v) hx hx'
  constructor
  · intro hc
    obtain ⟨Zc', hZ', hZ'y'⟩ := key.1 ⟨V, hc, hV⟩
    rwa [show Zc' = V' from IrreducibleCloseds.ext (hZ'y'.trans hV'.symm)] at hZ'
  · intro hc
    obtain ⟨Zc, hZ, hZy⟩ := key.2 ⟨V', hc, hV'⟩
    rwa [show Zc = V from IrreducibleCloseds.ext (hZy.trans hV.symm)] at hZ

end Correspondence

end Flip

namespace Flip

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

section IsoComp

variable {Xm V Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {g : V ⟶ Z}

omit [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral V]
  [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] in
/-- Precomposing `f⁺` with an isomorphism does not change the common biregular locus. -/
private theorem commonBiregularLocus_iso_comp {A : Scheme.{0}} (φ : A ≅ V) :
    commonBiregularLocus fm (φ.hom ≫ g) = commonBiregularLocus fm g := by
  unfold commonBiregularLocus
  rw [biregularLocus_comp_of_isIso]

/-- **The rank difference for `f⁺` precomposed with an isomorphism.** -/
private theorem divisorCycleRank_sub_eq_of_iso_comp
    (hdiag : IsFourfoldStepDiagram sXm sZ sV K B fm g) (hsmall : IsSmallMorphism sXm sZ fm)
    {A : Scheme.{0}} (φ : A ≅ V) {sA : A ⟶ Spec (.of ℂ)} (hsA : φ.hom ≫ sV = sA)
    (hA : MMP.Mori.IsProjectiveVariety ℂ sA) {fp : A ⟶ Z} (hfp : fp = φ.hom ≫ g)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor A}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') {r r' : ℕ}
    (hr : letI := primeDivisorNormalizationOver sXm S
      haveI := isComplexScheme_primeDivisorNormalizationScheme sXm hdiag.isProjectiveVariety_minus S
      r = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S))
    (hr' : letI := primeDivisorNormalizationOver sA S'
      haveI := isComplexScheme_primeDivisorNormalizationScheme sA hA S'
      r' = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S')) :
    (r : ℤ) - r' = (badBranchCount S (badLocusMinus fm fp) : ℤ) -
      badBranchCount S' (badLocusPlus fm fp) := by
  subst hfp hsA
  have hS'' := flipTransformPrimeDivisor_iso_comp fm g φ hS'
  have h0 := hdiag.divisorCycleRank_sub_divisorCycleRank_eq hsmall hS''
  obtain ⟨E, hE⟩ := Iso.exists_iso_primeDivisorNormalizationScheme φ S'
  letI := primeDivisorNormalizationOver (φ.hom ≫ sV) S'
  letI := primeDivisorNormalizationOver sV (Iso.primeDivisorEquivOfIso φ S')
  haveI := isComplexScheme_primeDivisorNormalizationScheme (φ.hom ≫ sV) hA S'
  haveI := isComplexScheme_primeDivisorNormalizationScheme sV hdiag.isProjectiveVariety_plus
    (Iso.primeDivisorEquivOfIso φ S')
  have hbr : MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S') =
      MMP.Analytic.divisorCycleRank
        (primeDivisorNormalizationScheme (Iso.primeDivisorEquivOfIso φ S')) :=
    Iso.divisorCycleRank_eq_of_iso E (by
      change E.hom ≫ (primeDivisorNormalization _ ≫ sV) = primeDivisorNormalization S' ≫ φ.hom ≫ sV
      rw [← Category.assoc, hE, Category.assoc])
  have hm : badLocusMinus fm (φ.hom ≫ g) = badLocusMinus fm g := by
    unfold badLocusMinus
    rw [commonBiregularLocus_iso_comp]
  have hpimg : φ.hom.base '' (badLocusPlus fm (φ.hom ≫ g) : Set A) =
      (badLocusPlus fm g : Set V) := by
    rw [coe_badLocusPlus, coe_badLocusPlus, coe_badLocusBase, coe_badLocusBase,
      commonBiregularLocus_iso_comp]
    exact Iso.image_preimage_comp φ g _
  have hbad := Iso.badBranchCount_primeDivisorEquivOfIso φ S' (badLocusPlus fm (φ.hom ≫ g) : Set A)
  rw [hpimg] at hbad
  rw [hr, hr', hbr, hm, ← hbad]
  exact h0

end IsoComp

end Flip

namespace Flip

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

section Extra

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
  [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- **Centres in the bad loci.** A valuation centred in `(f⁻)⁻¹(Z ∖ U)` transports to a
valuation centred in `(f⁺)⁻¹(Z ∖ U)`. -/
private theorem transport_isCentredIn (h : IsBirationalPair sXm sZ sXp fm fp)
    [IsDominant fm] [IsDominant fp] {U : Z.Opens}
    {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    (hv : ∃ Zc : IrreducibleCloseds Xm, MMP.Intersection.IsCentre ℂ sXm v Zc ∧
      (Zc : Set Xm) ⊆ fm ⁻¹' (U : Set Z)ᶜ) :
    ∃ Zc' : IrreducibleCloseds Xp, MMP.Intersection.IsCentre ℂ sXp (transport h v) Zc' ∧
      (Zc' : Set Xp) ⊆ fp ⁻¹' (U : Set Z)ᶜ := by
  obtain ⟨Zc, hZ, hZW⟩ := hv
  obtain ⟨Zc', x, x', hZ', hZx, hZ'x', hxx⟩ := exists_isCentre_of_comap_eq h hZ
    (comap_transport h v)
  have hx : fm x ∉ U := hZW (hZx ▸ subset_closure rfl)
  refine ⟨Zc', hZ', ?_⟩
  rw [hZ'x', (U.isOpen.isClosed_compl.preimage fp.continuous).closure_subset_iff,
    Set.singleton_subset_iff]
  change fp x' ∉ U
  rw [hxx]
  exact hx

end Extra

end Flip

/-! ### Codimensions and dimensions of closures of points -/

section Dimension

/-- The codimension of the closure of a point is the coheight of the point. -/
private theorem codimension_eq_coheight_of_eq_closure {X : Scheme.{0}} {W : IrreducibleCloseds X}
    {x : X} (h : (W : Set X) = closure {x}) : codimension W = Order.coheight x := by
  have hEq : (irreducibleSetEquivPoints (α := X)).symm x = W := IrreducibleCloseds.ext h.symm
  rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]

/-- On a fourfold, the closure of a point of coheight `c` has dimension `4 - c`, in the form
`dim + c = 4`. -/
private theorem topologicalKrullDim_closure_add_coheight {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 4) (x : X) :
    topologicalKrullDim (closure {x} : Set X) + Order.coheight x = 4 := by
  rw [MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x, hdim]

/-- Dimension arithmetic: `d + c = 4` with `c = 2` forces `d = 2`, and conversely. -/
private theorem eq_two_iff_of_add_eq_four {d : WithBot ℕ∞} {c : ℕ∞} (h : d + c = 4) :
    d = 2 ↔ c = 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    norm_cast at h ⊢
    induction e using ENat.recTopCoe <;> induction c using ENat.recTopCoe <;> simp_all <;>
      norm_cast at * <;> omega

end Dimension

/-- A divisorial valuation has at most one centre. -/
private theorem isCentre_unique {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    (hX : MMP.Mori.IsVariety ℂ sY) {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    {V V' : IrreducibleCloseds Y} (hV : MMP.Intersection.IsCentre ℂ sY ξ V)
    (hV' : MMP.Intersection.IsCentre ℂ sY ξ V') : V = V' := by
  obtain ⟨D, -, hD, rfl⟩ := hV
  obtain ⟨D', -, hD', rfl⟩ := hV'
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX (hD.symm.trans hD')

/-! ### Brackets vanish at almost every surface -/

namespace Bracket

open MMP.Mori IsLocalRing
open scoped WithZero

/-- In `WithBot ℕ∞`, `d + 1 = n + 1` forces `d = n`. -/
private theorem eq_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (h : d + 1 = ((n + 1 : ℕ) : ℕ∞)) :
    d = (n : ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact (WithBot.bot_ne_coe h).elim
  | coe e =>
    norm_cast at h ⊢
    induction e using ENat.recTopCoe <;> simp_all <;> norm_cast at * <;> omega

/-- Dimension arithmetic: `2 + c = 3` forces `c = 1`. -/
private theorem eq_one_of_two_add_eq_three {c : ℕ∞} (h : (2 : WithBot ℕ∞) + c = 3) : c = 1 := by
  norm_cast at h
  induction c using ENat.recTopCoe <;> simp_all <;> norm_cast at * <;> omega

/-- The coefficients of the boundary of a klt pair are `< 1`. -/
private theorem coeff_lt_one_of_isKltPair {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Θ : QDivisor X} (hΘ : IsKltPair sX Θ) (P : MMP.Mori.PrimeDivisor X) :
    Θ.coeff P < 1 := by
  obtain ⟨hX, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f := by
    change IsProper (𝟙 X); infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- The default echo weight of a nonpositive coefficient vanishes. -/
private theorem defaultWeight_of_nonpos (N : ℕ) {b : ℝ} (hb : b ≤ 0) : defaultWeight N b = 0 := by
  rw [defaultWeight]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [finsum_eq_if]
  split_ifs with hj
  · apply difficultyWeight_of_nonpos
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  · rfl

/-- A log discrepancy over a proper model is a log discrepancy. -/
private theorem IsValuationLogDiscrepancy.hasLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sX B v a) : HasLogDiscrepancy sX B v a := by
  obtain ⟨n, D, -, hv, ha⟩ := h
  exact ⟨n, D, hv, ha⟩

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : HasLogDiscrepancy sX B v a) (h' : HasLogDiscrepancy sX B v a') : a = a' := by
  obtain ⟨n, D, hv, ha⟩ := h
  obtain ⟨n', D', hv', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hv.trans hv'.symm)

/-- **Regularity in codimension two.** On a terminal pair on a `ℚ`-factorial normal variety over
`ℂ`, the local ring at every point of coheight at most two is regular. -/
private theorem isRegularLocalRing_stalk_of_coheight_le_two {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : IsKltTerminalPair sY Θ) (hQ : IsQFactorial sY) {y : Y} (hy : Order.coheight y ≤ 2) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨-, n, K, hK, -⟩ := id hΘ.1.1.isPair
  obtain ⟨-, hsing⟩ :=
    IsKltTerminalPair.isTerminalVariety_and_three_le_closedsCodimension_singularLocus hΘ
      (isQCartier_of_isQFactorial sY hQ Θ) hK (isQCartier_of_isQFactorial sY hQ _)
  have hy' : y ∈ smoothLocus sY := by
    by_contra hns
    let e := irreducibleSetEquivPoints (α := Y)
    have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ (singularLocus sY : Set Y) := by
      change closure {y} ⊆ _
      exact (singularLocus sY).isClosed.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hns)
    have h3 := le_closedsCodimension_iff.1 hsing _ hsub
    rw [codimension_eq_coheight_of_eq_closure (rfl : ((e.symm y : IrreducibleCloseds Y) :
      Set Y) = closure {y})] at h3
    exact absurd (h3.trans hy) (by decide)
  obtain ⟨U, hyU, hU⟩ := mem_smoothLocus_iff.mp hy'
  have : Smooth (U.ι ≫ sY) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sY) ⟨y, hyU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv

/-! ### Valuations from additive valuations -/

/-- The order-reversing monoid map `WithTop ℤ → ℤᵐ⁰`, `n ↦ exp (-n)`, `⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private lemma expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private lemma expNeg_top : expNeg ⊤ = 0 := rfl

private lemma expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private lemma expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg_top]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R ℤᵐ⁰ where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg_top]
  map_one' := by simp [← WithTop.coe_zero, expNeg_coe]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

private lemma valuationOfAddValuation_apply {R : Type*} [Ring R]
    (V : AddValuation R (WithTop ℤ)) (z : R) :
    valuationOfAddValuation V z = expNeg (V z) := rfl

/-! ### Echo ideals in a two-dimensional regular local ring -/

/-- A pair `(x, y)` is a regular system of parameters iff it spans `𝔪` and `dim A = 2`. -/
private lemma isRegularSystemOfParameters_pair_iff {A : Type*} [CommRing A] [IsLocalRing A]
    {x y : A} :
    IsRegularSystemOfParameters ![x, y] ↔
      Ideal.span {x, y} = maximalIdeal A ∧ ringKrullDim A = 2 := by
  rw [isRegularSystemOfParameters_iff, Matrix.range_cons, Matrix.range_cons,
    Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl

private lemma isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : IsRegularSystemOfParameters ![x, y]) :
    IsRegularSystemOfParameters ![y, x] := by
  rw [isRegularSystemOfParameters_pair_iff, Set.pair_comm]
  exact isRegularSystemOfParameters_pair_iff.1 hxy

/-- A point whose local ring has a regular system of parameters of length two is the generic
point of a closed subset of codimension two. -/
private lemma codimension_eq_two {X : Scheme.{u}} (Z : IrreducibleCloseds X)
    {x t : X.presheaf.stalk Z.isIrreducible.genericPoint}
    (ht : IsRegularSystemOfParameters ![x, t]) : codimension Z = 2 :=
  WithBot.coe_injective (by rw [codimension_eq_ringKrullDim_stalk_genericPoint, ht.2]; rfl)

/-- A local equation of a prime divisor at a point of it is a nonzero element of the maximal
ideal. -/
private theorem mem_maximalIdeal_and_ne_zero_of_stalk_eq_span {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hy : y ∈ E.support) {a : Y.presheaf.stalk y}
    (ha : IdealSheafData.stalk E.idealSheaf y = Ideal.span {a}) :
    a ∈ maximalIdeal (Y.presheaf.stalk y) ∧ a ≠ 0 := by
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hy
  refine ⟨(mem_maximalIdeal _).2 fun hu => ?_, ?_⟩
  · exact (IdealSheafData.stalk_eq_top_iff_notMem_support E.idealSheaf y).1
      (by rw [ha, Ideal.span_singleton_eq_top]; exact hu) hy
  · rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hqh (by rw [← hq, ha, Ideal.span_singleton_eq_bot])

/-- The generic point of a surface in a fourfold has coheight two. -/
private theorem coheight_genericPoint_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {V : IrreducibleCloseds Y}
    (hY : IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 4) (hV : topologicalKrullDim (V : Set Y) = 2) :
    Order.coheight V.isIrreducible.genericPoint = 2 := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [V.isIrreducible.closure_genericPoint V.isClosed, hV, hdim] at h
  exact (add_right_inj_of_ne_top (by decide)).mp (WithBot.coe_inj.mp h :
    2 + Order.coheight V.isIrreducible.genericPoint = 2 + 2)

/-- The local ring of a normal fourfold at the generic point of a surface has dimension two. -/
private theorem ringKrullDim_stalk_genericPoint_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {V : IrreducibleCloseds Y}
    (hY : IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 4) (hV : topologicalKrullDim (V : Set Y) = 2) :
    ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, coheight_genericPoint_eq_two hY hdim hV]
  rfl

/-! ### Existence of echoes -/

/-- **A valuation of log discrepancy below two at a surface in a boundary component.** Let `(Y, Θ)`
be a pair on a normal fourfold, `V` an irreducible surface at whose generic point `Y` is regular,
and `P` a component of `Θ` containing `V`. The `𝔪_V`-adic order (the monomial valuation of
weights `(1, 1)` in a regular system of parameters at `η_V`) is a normalized divisorial valuation
with centre `V` and log discrepancy at most `2 - Θ(P)`. -/
private theorem exists_isCentre_hasLogDiscrepancy_le {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : MMP.Fourfold.IsPair sY Θ) (hY : IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 4) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 2)
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {P : MMP.Mori.PrimeDivisor Y} (hVP : (V : Set Y) ⊆ P.support) (hP : 0 < Θ.coeff P) :
    ∃ v : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sY v V ∧
        ∃ a : ℝ, a ≤ 2 - (Θ.coeff P : ℝ) ∧ HasLogDiscrepancy sY Θ v a := by
  classical
  set η := V.isIrreducible.genericPoint with hη
  have hdimR := ringKrullDim_stalk_genericPoint_eq_two hY hdim hV
  -- a regular system of parameters at `η_V`
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal (Y.presheaf.stalk η)).fg_of_isNoetherianRing
  have h2 : (maximalIdeal (Y.presheaf.stalk η)).spanFinrank = 2 := by
    have := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := Y.presheaf.stalk η)).trans hdimR
    exact_mod_cast this
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (hs.trans h2)
  have hab : Ideal.span {a, b} = maximalIdeal (Y.presheaf.stalk η) := by simpa using hspan
  have ht : IsRegularSystemOfParameters ![a, b] :=
    isRegularSystemOfParameters_pair_iff.2 ⟨hab, hdimR⟩
  -- the monomial valuation of weights `(1, 1)`
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap ht) (le_refl 1)
  have hvalW : ∀ f : Y.presheaf.stalk η, f ≠ 0 →
      ∃ M : ℕ, MMP.Resolution.monomialValuation b a 1 f = M ∧
        valuationOfAddValuation W (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have hv : IsWeightedMonomialValuation sY V a b 1 (valuationOfAddValuation W) :=
    ⟨hY, codimension_eq_two V ht, inferInstance, ht, le_rfl, hvalW⟩
  -- local equations of the components of `Θ`
  have hηP : η ∈ P.support := hVP (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  have hgen : ∀ S : MMP.Mori.PrimeDivisor Y, ∃ g : Y.presheaf.stalk η,
      IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} ∧ g ≠ 0 := by
    intro S
    by_cases hS : η ∈ S.support
    · haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk η)
      haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk η)
      obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
      obtain ⟨g, hgq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
      have hg := hq.trans hgq
      exact ⟨g, hg, (mem_maximalIdeal_and_ne_zero_of_stalk_eq_span S hS hg).2⟩
    · refine ⟨1, ?_, one_ne_zero⟩
      rw [Ideal.span_singleton_one]
      exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).mpr hS
  choose f hf hf0 using hgen
  have hd := hv.hasLogDiscrepancy hΘ f fun S _ => hf S
  refine ⟨_, hv.isNormalizedDivisorialValuation_and_isCentre.2, _, ?_, hd⟩
  -- the estimate
  have hM : ∀ S, ∃ M : ℕ, (-WithZero.log (valuationOfAddValuation W
      (algebraMap _ Y.functionField (f S))) : ℤ) = M ∧
        (η ∈ S.support → 1 ≤ M) := by
    intro S
    obtain ⟨M, hMv, hMw⟩ := hvalW (f S) (hf0 S)
    refine ⟨M, by rw [hMw, WithZero.log_exp, neg_neg], fun hS => ?_⟩
    have hmem : f S ∈ MMP.Resolution.monomialIdeal b a 1 1 := by
      rw [MMP.Fourfold.monomialIdeal_one_eq_pow, pow_one, Set.pair_comm, hab]
      exact (mem_maximalIdeal_and_ne_zero_of_stalk_eq_span S hS (hf S)).1
    have h1 : (1 : ℕ∞) ≤ MMP.Resolution.monomialValuation b a 1 (f S) :=
      le_iSup₂_of_le (f := fun (ν : ℕ) (_ : f S ∈ MMP.Resolution.monomialIdeal b a 1 ν) =>
        (ν : ℕ∞)) 1 hmem (by norm_num)
    rw [hMv] at h1
    exact_mod_cast h1
  have hnn : ∀ S ∈ Θ.support, 0 ≤ (Θ.coeff S : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f S))) : ℤ) :
        ℝ) := by
    intro S _
    obtain ⟨M, hMe, -⟩ := hM S
    rw [hMe]
    exact mul_nonneg (by exact_mod_cast hΘ.nonneg S) (by positivity)
  have hPmem : P ∈ Θ.support := Finsupp.mem_support_iff.mpr hP.ne'
  have hle := Finset.single_le_sum hnn hPmem
  obtain ⟨MP, hMPe, hMP1⟩ := hM P
  have hPterm : (Θ.coeff P : ℝ) ≤ (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) :
        ℝ) := by
    rw [hMPe]
    have : (1 : ℝ) ≤ (MP : ℝ) := by exact_mod_cast hMP1 hηP
    have hc : (0 : ℝ) ≤ Θ.coeff P := by exact_mod_cast hP.le
    push_cast
    nlinarith
  rw [Nat.cast_one]
  linarith

/-- **Branch number one at a regular point.** Let `S` be a prime divisor of a fourfold `Y`
and `V ⊆ S` an irreducible closed surface at whose generic point `S` is regular. Then exactly one
prime divisor of the normalization `S^ν` maps onto `V`: `r_{V} = 1`. -/
private theorem branchNumber_eq_one {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsVariety ℂ sY] (hdim : topologicalKrullDim Y = 4)
    (S : MMP.Mori.PrimeDivisor Y)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 2)
    (hVS : (V : Set Y) ⊆ S.support)
    (hreg : V.isIrreducible.genericPoint ∉
      S.idealSheaf.subschemeι '' AlgebraicGeometry.singularLocus S.idealSheaf.subscheme) :
    branchNumber S V = 1 := by
  classical
  haveI : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety ℂ sY).toIsIntegral
  haveI := S.integral
  haveI hvarS : AlgebraicGeometry.IsVariety ℂ (S.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨-, -, hfinν, hsurj, -⟩, ⟨U, hU, hiso⟩, -⟩ :=
    MMP.Threefold.normalization_spec (S.idealSheaf.subschemeι ≫ sY)
  set ν := S.idealSheaf.subscheme.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral
      S.idealSheaf.subscheme) with hν
  set ι := S.idealSheaf.subschemeι with hι
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  -- the point `s` of `S` over `η_V`
  obtain ⟨s, hs⟩ : V.isIrreducible.genericPoint ∈ Set.range ι := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
    exact hVS hgen.mem
  have hsreg : IsRegularLocalRing (S.idealSheaf.subscheme.presheaf.stalk s) := by
    by_contra h
    exact hreg ⟨s, h, hs⟩
  have hsU : s ∈ U := by
    rw [← SetLike.mem_coe, hU]
    haveI := IsRegularLocalRing.isDomain (S.idealSheaf.subscheme.presheaf.stalk s)
    haveI := IsRegularLocalRing.uniqueFactorizationMonoid
      (S.idealSheaf.subscheme.presheaf.stalk s)
    exact (inferInstance : IsIntegrallyClosed (S.idealSheaf.subscheme.presheaf.stalk s))
  -- `S` is a threefold and `closure {s}` a surface, so `s` has coheight one in `S`
  have hdimS : topologicalKrullDim S.idealSheaf.subscheme = 3 := by
    have hdP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY S.genericPoint
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at hdP
    let e := ι.isClosedEmbedding.isEmbedding.toHomeomorph
    let e' := e.trans (Homeomorph.setCongr (Scheme.IdealSheafData.range_subschemeι S.idealSheaf))
    exact (IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph).trans
      (eq_of_add_one_eq (n := 3) hdP)
  have hdimCs : topologicalKrullDim (closure ({s} : Set S.idealSheaf.subscheme)) = 2 := by
    rw [← hV]
    have hemb : Topology.IsEmbedding
        (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) :=
      ι.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hrange : Set.range (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) =
        (V : Set Y) := by
      rw [show (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) = ι ∘ Subtype.val
        from rfl, Set.range_comp, Subtype.range_coe,
        ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hs, hgen.def]
    let e := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  have hcohs : Order.coheight s = 1 := by
    have hdS := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (S.idealSheaf.subschemeι ≫ sY) s
    rw [hdimS, hdimCs] at hdS
    exact eq_one_of_two_add_eq_three hdS
  -- over `U` the normalization is an isomorphism
  haveI := hsurj
  haveI := hiso
  haveI := hfinν
  obtain ⟨z₀, hz₀⟩ := ν.surjective s
  have hcomm : ∀ p, U.ι ((ν ∣_ U) p) = ν ((ν ⁻¹ᵁ U).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hlift : ∀ z, ν z = s → ∃ p, (ν ⁻¹ᵁ U).ι p = z := fun z hz => by
    change z ∈ Set.range (ν ⁻¹ᵁ U).ι
    rw [Scheme.Opens.range_ι]
    change ν z ∈ U
    rw [hz]
    exact hsU
  obtain ⟨p₀, hp₀⟩ := hlift z₀ hz₀
  have huniq : ∀ z, ν z = s → z = z₀ := by
    intro z hz
    obtain ⟨p, hp⟩ := hlift z hz
    have h1 : U.ι ((ν ∣_ U) p) = U.ι ((ν ∣_ U) p₀) := by rw [hcomm, hcomm, hp, hp₀, hz, hz₀]
    have h2 := (ν ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective h1)
    rw [← hp, ← hp₀, h2]
  have hcoh0 : Order.coheight z₀ = 1 := by
    calc Order.coheight z₀ = Order.coheight ((ν ⁻¹ᵁ U).ι p₀) := by rw [hp₀]
      _ = Order.coheight p₀ := coheight_eq_of_isOpenImmersion _
      _ = Order.coheight ((ν ∣_ U) p₀) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight (U.ι ((ν ∣_ U) p₀)) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight s := by rw [hcomm, hp₀, hz₀]
      _ = 1 := hcohs
  -- the images of prime divisors of `S^ν`
  have hfun : ⇑(ν ≫ ι) = ⇑ι ∘ ⇑ν := funext fun _ => rfl
  have hcl : IsClosedMap (ν ≫ ι) := by
    rw [hfun]
    exact ι.isClosedEmbedding.isClosedMap.comp ν.isClosedMap
  have himg : ∀ Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)),
      (ν ≫ ι) '' Q.support = closure {ι (ν Q.genericPoint)} := by
    intro Q
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← hcl.closure_image_eq_of_continuous (ν ≫ ι).continuous, Set.image_singleton]
    rfl
  have hset : {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)} =
        {AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0} := by
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [himg]
    constructor
    · intro hQ
      have hQη : ι (ν Q.genericPoint) = V.isIrreducible.genericPoint :=
        (inseparable_iff_closure_eq.mpr (hQ.trans hgen.def.symm)).eq
      have hνQ : ν Q.genericPoint = s := ι.isClosedEmbedding.injective (hQη.trans hs.symm)
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      exact huniq _ hνQ
    · rintro rfl
      have hg0 : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0) = z₀ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [hg0, hz₀, hs, hgen.def]
  change {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)}.ncard = 1
  rw [hset, Set.ncard_singleton]

end Bracket

/-! ### The difficulty seen from a closed set of a model -/

namespace Side

open MMP.Mori

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T) (x : Q.ModelIndex)

/-- `v` has a centre of codimension at least three on the model indexed by `x`. -/
private abbrev IsDeepCentred
    (v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))) : Prop :=
  ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
    MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧ 3 ≤ codimension Z

/-- `v` has a centre contained in `W` on the model indexed by `x`. -/
private abbrev IsCentredIn (W : Set (Q.chain.model x.1))
    (v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))) : Prop :=
  ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
    MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
      (Z : Set (Q.chain.model x.1)) ⊆ W

/-- A model of a prepared chain is a normal projective fourfold over `ℂ`. -/
private theorem model_facts :
    MMP.Mori.IsNormalVariety ℂ (Q.chain.modelStructure x.1) ∧
      LocallyOfFiniteType (Q.chain.modelStructure x.1) ∧
      IsProper (Q.chain.modelStructure x.1) ∧ topologicalKrullDim (Q.chain.model x.1) = 4 := by
  obtain ⟨hΘ, -, hY, hdim⟩ := TerminalChain.isKltTerminalPair_modelBoundary Q.chain x.1
  exact ⟨hΘ.1.1.isPair.1, hY.toIsVariety.toLocallyOfFiniteType,
    isProper_of_isProjectiveMorphism _ hY.isProjective, hdim⟩

variable {Q x}

/-- **Centres inside a set of points of coheight at least two.** On a model, a valuation whose
centre lies in a set of points of coheight at least two has as centre either an irreducible
closed set of codimension at least three, or a surface of that set, and not both. -/
private theorem isCentredIn_cases {W : Set (Q.chain.model x.1)}
    (hWc : ∀ y ∈ W, 2 ≤ Order.coheight y)
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsCentredIn Q x W v) :
    (IsDeepCentred Q x v ∧ ∀ V : IrreducibleCloseds (Q.chain.model x.1),
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 →
          ¬ MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V) ∨
      ∃ V : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 ∧
        (V : Set (Q.chain.model x.1)) ⊆ W ∧ ¬ IsDeepCentred Q x v ∧
        ∀ V', MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V' → V' = V := by
  obtain ⟨hnv, hlft, -, hdim⟩ := model_facts Q x
  have hvar := hnv.1
  haveI := hvar.toIsIntegral
  obtain ⟨Z, hZ, hZW⟩ := hv
  obtain ⟨D, -, -, rfl⟩ := id hZ
  have hZz := D.center_eq_closure_genericPoint
  set y := D.f D.E.genericPoint
  have hyW : y ∈ W := hZW (hZz ▸ subset_closure rfl)
  have hcod : codimension D.center = Order.coheight y :=
    codimension_eq_coheight_of_eq_closure hZz
  haveI := hlft
  have hsum := topologicalKrullDim_closure_add_coheight (Q.chain.modelStructure x.1) hdim y
  by_cases h3 : 3 ≤ Order.coheight y
  · refine Or.inl ⟨⟨D.center, hZ, hcod ▸ h3⟩, fun V hV hV' => ?_⟩
    obtain rfl := isCentre_unique hvar hZ hV'
    rw [hZz] at hV
    have := (eq_two_iff_of_add_eq_four hsum).1 hV
    rw [this] at h3
    exact absurd h3 (by decide)
  · have h2 : Order.coheight y = 2 := by
      have := hWc y hyW
      generalize Order.coheight y = c at this h3 ⊢
      induction c using ENat.recTopCoe with
      | top => exact absurd le_top h3
      | coe c => norm_cast at this h3 ⊢; omega
    refine Or.inr ⟨D.center, hZ, ?_, hZW, fun ⟨Z', hZ', h3'⟩ => ?_,
      fun V' hV' => isCentre_unique hvar hV' hZ⟩
    · rw [hZz]; exact (eq_two_iff_of_add_eq_four hsum).2 h2
    · obtain rfl := isCentre_unique hvar hZ hZ'
      rw [hcod, h2] at h3'
      exact absurd h3' (by decide)

/-- A valuation centred in a set of points of coheight at least two has a weight: its centre
has codimension at least three or is a surface, and the difficulty data give weights at
both. -/
private theorem exists_isValuationWeight_of_isCentredIn {W : Set (Q.chain.model x.1)}
    (hWc : ∀ y ∈ W, 2 ≤ Order.coheight y)
    {w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ}
    {β : IrreducibleCloseds (Q.chain.model x.1) → ℤ}
    (hw : ∀ v, IsDeepCentred Q x v → Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (hβ : ∀ V : IrreducibleCloseds (Q.chain.model x.1),
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 → Q.IsSurfaceBracket x V (β V))
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsCentredIn Q x W v) : ∃ n, Q.chain.IsValuationWeight Q.scale x.1 v n := by
  rcases isCentredIn_cases hWc hv with ⟨hp, -⟩ | ⟨V, hcV, hV, -, -, -⟩
  · exact ⟨_, hw v hp⟩
  · obtain ⟨wβ, -, -, hwβ, -, -, -⟩ := hβ V hV
    exact ⟨_, hwβ v hcV⟩

/-- **Finitely many weighted deep valuations.** On a model of a prepared chain, only finitely
many valuations with centre of codimension at least three have nonzero weight. -/
private theorem finite_setOf_isDeepCentred_weight :
    {v | IsDeepCentred Q x v ∧
      ∃ n, Q.chain.IsValuationWeight Q.scale x.1 v n ∧ n ≠ 0}.Finite := by
  obtain ⟨hΘ, hQf, hY, hdim⟩ := TerminalChain.isKltTerminalPair_modelBoundary Q.chain x.1
  have hnv : MMP.Mori.IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hΘ.1.1.isPair.1
  haveI := hnv.1.toIsIntegral
  haveI := hnv.2
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (Q.chain.model x.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (Q.chain.modelStructure x.1)
  have hN := Q.isAdmissibleScale.pos
  refine (IsKltTerminalPair.finite_setOf_three_le_codimension_centre hY hQf hdim hΘ
    (L := (Q.chain.modelBoundary x.1).support) subset_rfl).subset ?_
  rintro v ⟨hdeep, n, ⟨hexc, a, ha, rfl⟩, hne⟩
  refine ⟨hexc, ⟨a, ?_, ?_⟩, hdeep⟩
  · by_contra h
    exact hne ((difficultyWeight_eq_zero_iff hN).2 (by linarith [not_lt.mp h]))
  · obtain ⟨m, D, -, hD, hm⟩ := ha
    exact ⟨m, D, hD, hm⟩

/-- **Brackets vanish at almost every surface.** On a model of a prepared chain, the bracket
`β_V` vanishes at all but finitely many irreducible surfaces `V`. -/
private theorem finite_setOf_isSurfaceBracket_ne_zero :
    {V : IrreducibleCloseds (Q.chain.model x.1) |
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 ∧
        ∃ β, Q.IsSurfaceBracket x V β ∧ β ≠ 0}.Finite := by
  classical
  haveI : Finite Q.chain.Label := Q.chain.finite_label
  letI : Fintype Q.chain.Label := Fintype.ofFinite _
  obtain ⟨hΘ, hQf, hY, hdim⟩ := TerminalChain.isKltTerminalPair_modelBoundary Q.chain x.1
  have hnv : MMP.Mori.IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hΘ.1.1.isPair.1
  haveI := hnv.1.toIsIntegral
  haveI := hnv.2
  haveI : AlgebraicGeometry.IsVariety ℂ (Q.chain.modelStructure x.1) := hnv.1
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (Q.chain.model x.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (Q.chain.modelStructure x.1)
  have hN := Q.isAdmissibleScale.pos
  set Θ := Q.chain.modelBoundary x.1 with hΘdef
  -- the label centres
  choose c hc using fun S => exists_isLabelCentre Q.chain S x.1
  have hcinj : Function.Injective c := by
    obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff Q.chain x.1
    intro S S' h
    have h1 := (he S (c S)).1 (hc S)
    have h2 := (he S' (c S')).1 (hc S')
    exact Subtype.ext (e.injective (h1.trans (h.trans h2.symm)))
  set L : Finset (MMP.Mori.PrimeDivisor (Q.chain.model x.1)) := Finset.univ.image c with hL
  have hcL : ∀ S, c S ∈ L := fun S => Finset.mem_image_of_mem c (Finset.mem_univ S)
  have hsupp : Θ.support ⊆ L := by
    intro P hP
    have hne : Θ.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
    rw [TerminalChain.coeff_modelBoundary_eq_finsum Q.chain x.1 (fun S => Θ.coeff (c S))
      (fun S => TerminalChain.isLabelCoefficient_of_isLabelCentre (hc S)) P] at hne
    obtain ⟨S, hS⟩ : ∃ S, Q.chain.IsLabelCentre S x.1 P := by
      by_contra h
      push Not at h
      exact hne (finsum_eq_zero_of_forall_eq_zero fun S => by rw [finsum_eq_if, if_neg (h S)])
    rw [isLabelCentre_unique hS (hc S)]
    exact hcL S
  have hlt : ∀ P ∈ L, Θ.coeff P < 1 := fun P _ => Bracket.coeff_lt_one_of_isKltPair hΘ.1 P
  obtain ⟨𝒮, -, h𝒮⟩ := IsKltTerminalPair.exists_finset_forall_isSurfaceEcho hY hQf hdim hΘ hsupp
  refine 𝒮.finite_toSet.subset ?_
  rintro V ⟨hV, β, ⟨wβ, r, d, hwβ, hr, hd, rfl⟩, hne⟩
  by_contra hV𝒮
  apply hne
  have hηV : V.isIrreducible.genericPoint ∈ (V : Set (Q.chain.model x.1)) :=
    (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  have hrS : ∀ S, r S = branchNumber (c S) (V : Set (Q.chain.model x.1)) := fun S => by
    rcases hr S with ⟨P, hP, hrP⟩ | ⟨hn, -⟩
    · rw [hrP, isLabelCentre_unique hP (hc S)]
    · exact absurd (hc S) (hn _)
  have hdS : ∀ S, d S = defaultWeight Q.scale ((Θ.coeff (c S) : ℚ) : ℝ) := fun S =>
    isLabelDefault_unique (hd S) ⟨_, TerminalChain.isLabelCoefficient_of_isLabelCentre (hc S), rfl⟩
  have hwa : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V → ∀ a,
      HasLogDiscrepancy (Q.chain.modelStructure x.1) Θ v a →
        wβ v = difficultyWeight Q.scale (2 - a) := by
    intro v hv a ha
    obtain ⟨-, a', ha', h⟩ := hwβ v hv
    rw [h, Bracket.HasLogDiscrepancy.unique
      (Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha') ha]
  by_cases hcase : ∃ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧ wβ v ≠ 0
  · -- some valuation at `V` has positive weight: `V` carries the echoes of a single label
    obtain ⟨v₀, hv₀, hw₀⟩ := hcase
    obtain ⟨-, a₀, ha₀, hw₀eq⟩ := hwβ v₀ hv₀
    have ha₀2 : a₀ < 2 := by
      by_contra h
      exact hw₀ (hw₀eq.trans ((difficultyWeight_eq_zero_iff hN).2 (by linarith [not_lt.mp h])))
    obtain ⟨S₀, j₀, hecho₀, -⟩ := h𝒮 V hV hV𝒮 v₀ hv₀ a₀ ha₀2
      (Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha₀)
    obtain ⟨-, -, hS₀L, hVS₀, -, hη, -, -, -⟩ := hecho₀
    obtain ⟨h₀, -, rfl⟩ := Finset.mem_image.mp hS₀L
    set b : ℝ := ((Θ.coeff (c h₀) : ℚ) : ℝ) with hbdef
    have hb1 : b < 1 := by rw [hbdef]; exact_mod_cast hlt _ hS₀L
    -- the label terms
    have hlab : (∑ᶠ S, r S * d S) = d h₀ := by
      rw [finsum_eq_single _ h₀ (fun S hS => ?_)]
      · rw [hrS, Bracket.branchNumber_eq_one (sY := Q.chain.modelStructure x.1) hdim (c h₀) hV hVS₀
          ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 _ hS₀L), one_mul]
      · rw [hrS, branchNumber_eq_zero_of_not_subset, zero_mul]
        intro hVS
        exact hS (hcinj (eq_of_mem_oneLabelSmoothLocus hη (hcL S) hS₀L (hVS hηV) (hVS₀ hηV)))
    -- the echoes of `S_{h₀}` at `V`
    have hex : ∀ j : ℕ, 1 ≤ j → ∃ ξ, IsSurfaceEcho (Q.chain.modelStructure x.1) L (c h₀) V j ξ :=
      fun j hj => exists_isSurfaceEcho hnv hdim hS₀L hVS₀ hV hη hj
    let ξ : ℕ → Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) :=
      fun j => if hj : 1 ≤ j then (hex j hj).choose else 1
    have hξ : ∀ j (hj : 1 ≤ j), IsSurfaceEcho (Q.chain.modelStructure x.1) L (c h₀) V j (ξ j) :=
      fun j hj => by simp only [ξ, dif_pos hj]; exact (hex j hj).choose_spec
    have hξa : ∀ j (hj : 1 ≤ j), HasLogDiscrepancy (Q.chain.modelStructure x.1) Θ (ξ j)
        (1 + j * (1 - b)) := fun j hj => (hξ j hj).hasLogDiscrepancy hΘ.1.1 hsupp hlt
    have hξc : ∀ j (hj : 1 ≤ j), MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) (ξ j) V :=
      fun j hj => (hξ j hj).2.2.2.2.2.2.2.1
    have hξw : ∀ j (hj : 1 ≤ j), wβ (ξ j) = difficultyWeight Q.scale (1 - j * (1 - b)) :=
      fun j hj => by rw [hwa _ (hξc j hj) _ (hξa j hj)]; congr 1; ring
    have hval : (∑ᶠ (v) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V),
        wβ v) = defaultWeight Q.scale b := by
      rw [defaultWeight]
      change ∑ᶠ v ∈ {v | MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V}, wβ v =
        ∑ᶠ j ∈ {j : ℕ | 1 ≤ j}, difficultyWeight Q.scale (1 - j * (1 - b))
      rw [← finsum_mem_inter_support, ← finsum_mem_inter_support (s := {j : ℕ | 1 ≤ j})]
      symm
      refine finsum_mem_eq_of_bijOn ξ ⟨fun j hj' => ?_, fun j₁ h₁' j₂ h₂' h12 => ?_,
        fun v hv' => ?_⟩ fun j hj' => (hξw j hj'.1).symm
      · obtain ⟨hj, hjne⟩ := hj'
        refine ⟨hξc j hj, ?_⟩
        change wβ (ξ j) ≠ 0
        rw [hξw j hj]
        exact hjne
      · have h₁ : 1 ≤ j₁ := h₁'.1
        have h₂ : 1 ≤ j₂ := h₂'.1
        have ha₁ := hξa j₁ h₁
        rw [h12] at ha₁
        have := Bracket.HasLogDiscrepancy.unique ha₁ (hξa j₂ h₂)
        have hpos : 0 < 1 - b := by linarith
        have : (j₁ : ℝ) = j₂ :=
          mul_right_cancel₀ hpos.ne' (by linarith : (j₁ : ℝ) * (1 - b) = j₂ * (1 - b))
        exact_mod_cast this
      · obtain ⟨hv, hvne⟩ := hv'
        obtain ⟨-, a, ha, hwv⟩ := hwβ v hv
        have ha2 : a < 2 := by
          by_contra h
          exact hvne (hwv.trans ((difficultyWeight_eq_zero_iff hN).2 (by linarith [not_lt.mp h])))
        obtain ⟨S, j, hecho, -⟩ := h𝒮 V hV hV𝒮 v hv a ha2
          (Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha)
        obtain ⟨-, -, hSL, hVS, -, -, hj, -, -⟩ := id hecho
        obtain rfl : S = c h₀ := eq_of_mem_oneLabelSmoothLocus hη hSL hS₀L (hVS hηV) (hVS₀ hηV)
        have hvj : v = ξ j := hecho.eq (hξ j hj)
        refine ⟨j, ⟨hj, ?_⟩, hvj.symm⟩
        change difficultyWeight Q.scale (1 - j * (1 - b)) ≠ 0
        rw [← hξw j hj, ← hvj]
        exact hvne
    rw [hlab, hval, hdS, hbdef, sub_self]
  · -- no valuation at `V` has positive weight: no label of positive coefficient contains `V`
    push Not at hcase
    have h1 : (∑ᶠ (v) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V),
        wβ v) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun v => by
        rw [finsum_eq_if]
        split_ifs with h
        · exact hcase v h
        · rfl
    have h2 : (∑ᶠ S, r S * d S) = 0 := finsum_eq_zero_of_forall_eq_zero fun S => by
      by_cases hVS : (V : Set (Q.chain.model x.1)) ⊆ (c S).support
      · rw [hdS S]
        by_cases hb : ((Θ.coeff (c S) : ℚ) : ℝ) ≤ 0
        · rw [Bracket.defaultWeight_of_nonpos _ hb, mul_zero]
        · exfalso
          push Not at hb
          haveI := Bracket.isRegularLocalRing_stalk_of_coheight_le_two hΘ hQf
            (Bracket.coheight_genericPoint_eq_two hnv hdim hV).le
          obtain ⟨v, hv, a, ha, hla⟩ := Bracket.exists_isCentre_hasLogDiscrepancy_le hΘ.1.1 hnv
            hdim hV hVS (by exact_mod_cast hb)
          refine absurd (hcase v hv) ?_
          rw [hwa v hv a hla]
          intro h0
          rw [difficultyWeight_eq_zero_iff hN] at h0
          linarith
      · rw [hrS, branchNumber_eq_zero_of_not_subset hVS, zero_mul]
    rw [h1, h2]
    rfl

/-- The branch terms over the finitely many surfaces of `W` are the bad branch counts. -/
private theorem sum_mul_sum_branchNumber_eq [Fintype Q.chain.Label] {W : Set (Q.chain.model x.1)}
    (hGfin : {V : IrreducibleCloseds (Q.chain.model x.1) |
      (V : Set (Q.chain.model x.1)) ⊆ W ∧
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2}.Finite)
    (c : Q.chain.Label → MMP.Mori.PrimeDivisor (Q.chain.model x.1)) {d d₀ b : Q.chain.Label → ℕ}
    (hd : ∀ S, d S = d₀ S)
    (hb : ∀ S, b S = ∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
      (_ : (V : Set (Q.chain.model x.1)) ⊆ W ∧
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2), branchNumber (c S) V) :
    ∑ S, (d S : ℤ) * ∑ V ∈ hGfin.toFinset, (branchNumber (c S) V : ℤ) =
      ∑ S, (d₀ S : ℤ) * b S := by
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hd S, hb S, show (∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
      (_ : (V : Set (Q.chain.model x.1)) ⊆ W ∧
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2), branchNumber (c S) V) =
      ∑ V ∈ hGfin.toFinset, branchNumber (c S) V from
    finsum_mem_eq_finite_toFinset_sum _ hGfin, Nat.cast_sum]

open Classical in
/-- **The difficulty seen from a closed set.** On a model `(Y, Θ)` of a prepared chain, let `W`
be a set of points of coheight at least two, containing finitely many surfaces, and `𝔉` a finite
set of valuations, all centred in `W`, containing every valuation centred in `W` of positive
weight, with weights `ω`. Then the deep sum and the bracket sum of the difficulty are the deep
sum over the valuations not centred in `W`, plus the brackets at the surfaces not in `W`, plus
`∑_{v ∈ 𝔉} ω_v`, minus `∑_h d_h ∑_{V ⊆ W} r_{V,h}`. -/
private theorem deepSum_add_bracketSum_eq [Fintype Q.chain.Label] (W : Set (Q.chain.model x.1))
    (hWc : ∀ y ∈ W, 2 ≤ Order.coheight y)
    (hGfin : {V : IrreducibleCloseds (Q.chain.model x.1) |
      (V : Set (Q.chain.model x.1)) ⊆ W ∧
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2}.Finite)
    (𝔉 : Finset (Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))))
    (ω : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hω : ∀ v ∈ 𝔉, Q.chain.IsValuationWeight Q.scale x.1 v (ω v))
    (h𝔉 : ∀ v ∈ 𝔉, IsCentredIn Q x W v)
    (hmem : ∀ v n, IsCentredIn Q x W v → Q.chain.IsValuationWeight Q.scale x.1 v n → n ≠ 0 →
      v ∈ 𝔉)
    (c : Q.chain.Label → MMP.Mori.PrimeDivisor (Q.chain.model x.1))
    (hc : ∀ S, Q.chain.IsLabelCentre S x.1 (c S))
    (w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (β : IrreducibleCloseds (Q.chain.model x.1) → ℤ) (d : Q.chain.Label → ℕ)
    (hw : ∀ v, IsDeepCentred Q x v → Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (hβ : ∀ V : IrreducibleCloseds (Q.chain.model x.1),
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 → Q.IsSurfaceBracket x V (β V))
    (hd : ∀ S, Q.chain.IsLabelDefault Q.scale S x.1 (d S)) :
    ((∑ᶠ (v) (_ : IsDeepCentred Q x v), w v : ℕ) : ℤ) +
        ∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
          (_ : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2), β V =
      ((∑ᶠ (v) (_ : IsDeepCentred Q x v ∧ ¬ IsCentredIn Q x W v), w v : ℕ) : ℤ) +
        ∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
          (_ : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 ∧
            ¬ (V : Set (Q.chain.model x.1)) ⊆ W), β V + ∑ v ∈ 𝔉, (ω v : ℤ) -
        ∑ S, (d S : ℤ) * ∑ V ∈ hGfin.toFinset, (branchNumber (c S) V : ℤ) := by
  set G := hGfin.toFinset with hG
  have hmemG : ∀ {V}, V ∈ G ↔ ((V : Set (Q.chain.model x.1)) ⊆ W ∧
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2) := fun {V} => hGfin.mem_toFinset
  -- the deep sum
  have hpts : ((∑ᶠ (v) (_ : IsDeepCentred Q x v), w v : ℕ) : ℤ) =
      ((∑ᶠ (v) (_ : IsDeepCentred Q x v ∧ ¬ IsCentredIn Q x W v), w v : ℕ) : ℤ) +
        ∑ v ∈ 𝔉, if IsDeepCentred Q x v then (ω v : ℤ) else 0 := by
    have hfin : ({v | IsDeepCentred Q x v} ∩ Function.support w).Finite := by
      refine (finite_setOf_isDeepCentred_weight (Q := Q) (x := x)).subset fun v ⟨hv, hne⟩ => ?_
      exact ⟨hv, w v, hw v hv, hne⟩
    have hsplit := finsum_mem_inter_add_sdiff' {v | IsCentredIn Q x W v} hfin
    have hin : ((∑ᶠ v ∈ {v | IsDeepCentred Q x v} ∩ {v | IsCentredIn Q x W v}, w v : ℕ) : ℤ) =
        ∑ v ∈ 𝔉, if IsDeepCentred Q x v then (ω v : ℤ) else 0 := by
      rw [Iso.natCast_finsum_mem_eq_sum 𝔉 ?_]
      · refine Finset.sum_congr rfl fun v hv => ?_
        by_cases hp : IsDeepCentred Q x v
        · rw [if_pos (show v ∈ {v | IsDeepCentred Q x v} ∩ {v | IsCentredIn Q x W v} from
            ⟨hp, h𝔉 v hv⟩), if_pos hp, isValuationWeight_unique (hw v hp) (hω v hv)]
        · rw [if_neg (show v ∉ {v | IsDeepCentred Q x v} ∩ {v | IsCentredIn Q x W v} from
            fun h => hp h.1), if_neg hp]
      · rintro v ⟨⟨hp, hb⟩, hne⟩
        exact hmem v (w v) hb (hw v hp) hne
    rw [show (∑ᶠ (v) (_ : IsDeepCentred Q x v), w v) =
      ∑ᶠ v ∈ {v | IsDeepCentred Q x v}, w v from rfl, ← hsplit, Nat.cast_add, hin, add_comm]
    rfl
  -- the brackets at the surfaces of `W`
  have hbrW : ∀ V ∈ G, β V = (∑ v ∈ 𝔉, if MMP.Intersection.IsCentre ℂ
        (Q.chain.modelStructure x.1) v V then (ω v : ℤ) else 0) -
      ∑ S, (d S : ℤ) * (branchNumber (c S) V : ℤ) := by
    intro V hV
    obtain ⟨wβ, r, dβ, hwβ, hr, hdβ, hβeq⟩ := hβ V (hmemG.1 hV).2
    rw [hβeq]
    congr 1
    · rw [Iso.natCast_finsum_eq_sum 𝔉 ?_]
      · refine Finset.sum_congr rfl fun v hv => ?_
        by_cases hcv : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V
        · rw [if_pos hcv, if_pos hcv, isValuationWeight_unique (hwβ v hcv) (hω v hv)]
        · rw [if_neg hcv, if_neg hcv]
      · intro v hcv hne
        exact hmem v (wβ v) ⟨V, hcv, (hmemG.1 hV).1⟩ (hwβ v hcv) hne
    · rw [finsum_eq_sum_of_fintype, Nat.cast_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      rcases hr S with ⟨P, hP, hrP⟩ | ⟨hn, -⟩
      · rw [isLabelCentre_unique hP (hc S)] at hrP
        rw [hrP, isLabelDefault_unique (hdβ S) (hd S), Nat.cast_mul, mul_comm]
      · exact absurd (hc S) (hn _)
  -- the bracket sum
  have hbr : ∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
        (_ : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2), β V =
      ∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
          (_ : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 ∧
            ¬ (V : Set (Q.chain.model x.1)) ⊆ W), β V +
      ∑ V ∈ G, ((∑ v ∈ 𝔉, if MMP.Intersection.IsCentre ℂ
        (Q.chain.modelStructure x.1) v V then (ω v : ℤ) else 0) -
        ∑ S, (d S : ℤ) * (branchNumber (c S) V : ℤ)) := by
    have hfin : ({V : IrreducibleCloseds (Q.chain.model x.1) |
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2} ∩ Function.support β).Finite :=
      (finite_setOf_isSurfaceBracket_ne_zero (Q := Q) (x := x)).subset fun V ⟨hV, hne⟩ =>
        ⟨hV, β V, hβ V hV, hne⟩
    have hsplit := finsum_mem_inter_add_sdiff'
      {V : IrreducibleCloseds (Q.chain.model x.1) | (V : Set (Q.chain.model x.1)) ⊆ W} hfin
    have e1 : (∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
        (_ : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2), β V) =
        ∑ᶠ V ∈ {V : IrreducibleCloseds (Q.chain.model x.1) |
          topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2}, β V := rfl
    have e2 : (∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
          (_ : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 ∧
            ¬ (V : Set (Q.chain.model x.1)) ⊆ W), β V) =
        ∑ᶠ V ∈ {V : IrreducibleCloseds (Q.chain.model x.1) |
          topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2} \
            {V | (V : Set (Q.chain.model x.1)) ⊆ W}, β V := rfl
    have e3 : (∑ᶠ V ∈ {V : IrreducibleCloseds (Q.chain.model x.1) |
          topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2} ∩
            {V | (V : Set (Q.chain.model x.1)) ⊆ W}, β V) = ∑ V ∈ G, β V := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (hGfin.subset fun V hV => ⟨hV.2, hV.1⟩)]
      exact Finset.sum_congr (Finset.ext fun V => by
        simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, hG]
        exact and_comm) fun _ _ => rfl
    rw [e1, e2, ← hsplit, e3, add_comm, Finset.sum_congr rfl hbrW]
  -- every valuation of `𝔉` has exactly one centre among the deep ones and the surfaces of `W`
  have hdec : ∀ v ∈ 𝔉, (ω v : ℤ) = (if IsDeepCentred Q x v then (ω v : ℤ) else 0) +
      ∑ V ∈ G, if MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V then
        (ω v : ℤ) else 0 := by
    intro v hv
    rcases isCentredIn_cases hWc (h𝔉 v hv) with ⟨hp, hnc⟩ | ⟨V₀, hc₀, hV₀, hV₀W, hnp, huniq⟩
    · rw [if_pos hp, Finset.sum_eq_zero fun V hV => if_neg (hnc V (hmemG.1 hV).2), add_zero]
    · rw [if_neg hnp, zero_add, Finset.sum_eq_single V₀ (fun V _ hne => if_neg fun h =>
        hne (huniq V h)) (fun h => absurd (hmemG.2 ⟨hV₀W, hV₀⟩) h), if_pos hc₀]
  have e1 : ∑ v ∈ 𝔉, (ω v : ℤ) = (∑ v ∈ 𝔉, if IsDeepCentred Q x v then (ω v : ℤ) else 0) +
      ∑ V ∈ G, ∑ v ∈ 𝔉, if MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V then
        (ω v : ℤ) else 0 := by
    rw [Finset.sum_congr rfl hdec, Finset.sum_add_distrib, Finset.sum_comm (s := 𝔉)]
  have e2 : ∑ V ∈ G, ((∑ v ∈ 𝔉, if MMP.Intersection.IsCentre ℂ
        (Q.chain.modelStructure x.1) v V then (ω v : ℤ) else 0) -
        ∑ S, (d S : ℤ) * (branchNumber (c S) V : ℤ)) =
      (∑ V ∈ G, ∑ v ∈ 𝔉, if MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V then
        (ω v : ℤ) else 0) -
        ∑ S, (d S : ℤ) * ∑ V ∈ G, (branchNumber (c S) V : ℤ) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [hpts, hbr, e2, e1]
  ring

end Side

/-! ### Labels across a flip -/

namespace LabelTransform

open MMP.Mori

section StrictTransform

variable {X Y : Scheme.{u}}

/-- The valuation of a prime divisor seen through a composite. -/
private theorem valuationOver_comp {Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (P : MMP.Mori.PrimeDivisor X) (a : X ⟶ Y)
    (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    P.valuationOver (a ≫ b) = (P.valuationOver a).comap (functionFieldMap b) :=
  Valuation.ext fun t => by
    simp only [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The valuation of a prime divisor through equal dominant morphisms. -/
private theorem valuationOver_congr [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] (P : MMP.Mori.PrimeDivisor X) {a b : X ⟶ Y} [IsDominant a] [IsDominant b]
    (h : a = b) : P.valuationOver a = P.valuationOver b := by
  subst h; rfl

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- A proper birational morphism onto a normal scheme is an isomorphism of local rings over the
generic point of each prime divisor `Q` of the target. -/
private theorem exists_primeDivisor_isIso_stalkMap [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : MMP.Mori.IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ E : MMP.Mori.PrimeDivisor X,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

end StrictTransform

/-- **The strict transform across a step diagram.** Let `X⁻ → Z ← X⁺` be a step diagram whose
morphism `f⁻` is small, and let `f : A ⟶ Z` be `f⁺` precomposed with an isomorphism
`φ : A ⟶ X⁺`. Every prime divisor `S` of `X⁻` has a strict transform `S⁺ = f⁻¹_* f⁻_* S` on `A`,
and `ord_{S⁺} = ord_S` as valuations of `k(Z)`. -/
private theorem exists_flipTransformPrimeDivisor_eq_some {Xm Xp Z A : Scheme.{0}}
    [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : MMP.Mori.Divisor Xm} {B : MMP.Mori.QDivisor Xm}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hsm : IsSmallMorphism sXm sZ fm) (f : A ⟶ Z) (φ : A ⟶ Xp) [IsIso φ] (hf : f = φ ≫ fp)
    (S : MMP.Mori.PrimeDivisor Xm) :
    haveI := hD.isNormalVariety_target.1.toIsIntegral
    haveI := hD.isBirationalMorphism_minus.isDominant
    ∃ (S' : MMP.Mori.PrimeDivisor A) (_ : IsDominant f),
      flipTransformPrimeDivisor fm f S = some S' ∧ S'.valuationOver f = S.valuationOver fm := by
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    have := hZ.1
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI : IsProper fp := hD.isProper_plus
  subst hf
  -- `ζ = f⁻(η_S)` has codimension one, and is the generic point of a prime divisor `Q` of `Z`
  have hζ : Order.coheight (fm S.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fm
      (Flip.map_genericPoint_mem_biregularLocus_of_two_le hsm.two_le_codimension S),
      S.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : fm S.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Z.presheaf.stalk (fm S.genericPoint)) := by rw [hQ]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fm hbm.functionFieldMap_bijective
    S.genericPoint
  -- the prime divisor of `X⁺` over `Q`, carried to `A`
  obtain ⟨P, hPQ, hPiso⟩ := exists_primeDivisor_isIso_stalkMap fp hbp Q
  have hφ : φ (inv φ P.genericPoint) = P.genericPoint := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have hy : Order.coheight (inv φ P.genericPoint) = 1 := by
    rw [← Topology.IsOpenEmbedding.coheight_eq _ φ.isOpenEmbedding, hφ, P.coheight_genericPoint]
  set S' : MMP.Mori.PrimeDivisor A := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hy
  have hS' : S'.genericPoint = inv φ P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy
  have hS'Q : (φ ≫ fp) S'.genericPoint = Q.genericPoint := by
    rw [Scheme.Hom.comp_apply, hS', hφ, hPQ]
  have hfpiso : IsIso (fp.stalkMap (φ S'.genericPoint)) := by
    rw [hS', hφ]; exact hPiso
  haveI : IsIso ((φ ≫ fp).stalkMap S'.genericPoint) := by
    rw [Scheme.Hom.stalkMap_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hfpiso inferInstance
  refine ⟨S', inferInstance, ?_, ?_⟩
  · unfold flipTransformPrimeDivisor
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm S Q).mpr hQ,
      Option.bind_some]
    refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      hS'Q ?_
    rw [hS'Q, ← hPQ]
    exact Flip.biregularLocus_le_biregularLocus_comp φ fp
      (Flip.map_genericPoint_mem_biregularLocus_of_two_le
        hD.isSmallMorphism_plus.two_le_codimension P)
  · rw [valuationOver_eq_of_isIso _ S' Q hS'Q, valuationOver_eq_of_isIso _ S Q hQ]

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a relative
program is compatible with the morphisms `π_a`, `π_b` to the base. -/
private theorem eqToHom_comp_toBase {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {π : V ⟶ Z} {K : MMP.Mori.Divisor V} {Θ : MMP.Mori.QDivisor V}
    (P : RelativeFourfoldProgram sV sZ π K Θ) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V P.Y) h) ≫ P.toBase b = P.toBase a := by
  subst h
  simp

open StabilizedSmallKltTail in
/-- **Labels across a flip of a bridge.** For the `k`-th flip `V_k → T_k ← V_{k+1}` of the `i`-th
bridge of a terminal chain and the centre `S⁻` of a label on `V_k`, the strict transform of `S⁻`
on the model reached by the flip is a prime divisor, and it is the centre of the label there. -/
private theorem exists_flipTransformPrimeDivisor_isLabelCentre {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) (i : ℕ) (k : Fin (C.bridge i).P.m) {S : C.Label}
    {Sm : MMP.Mori.PrimeDivisor (C.model ⟨i, some k⟩)} (hm : C.IsLabelCentre S ⟨i, some k⟩ Sm) :
    ∃ Sp : MMP.Mori.PrimeDivisor (C.model (C.flipTarget i k)),
      flipTransformPrimeDivisor ((C.bridge i).P.g k) (C.flipTargetMap i k) Sm = some Sp ∧
        C.IsLabelCentre S (C.flipTarget i k) Sp := by
  have hD := (C.bridge i).P.isFourfoldStepDiagram k k.2
  have hsm := (C.bridge i).isSmallMorphism k k.2
  haveI := hD.isNormalVariety_target.1.toIsIntegral
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hD.isBirationalMorphism_plus.isDominant
  obtain ⟨w, hw, hdom, hSm⟩ := hm
  have heq := (C.bridge i).P.modelMap_eq k k.2
  have hpeq := (C.bridge i).P.πY_eq k k.2
  haveI : IsDominant ((C.bridge i).P.h k) := by
    have : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := heq ▸ hdom
    exact IsDominant.of_comp ((C.bridge i).P.g k) _
  have key : ∀ {A : Scheme.{0}} [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A]
      (f : A ⟶ (C.bridge i).P.T k) (φ : A ⟶ (C.bridge i).P.Y k) [IsIso φ]
      (_ : f = φ ≫ (C.bridge i).P.gp k),
      ∃ (Sp : MMP.Mori.PrimeDivisor A) (_ : IsDominant f),
        flipTransformPrimeDivisor ((C.bridge i).P.g k) f Sm = some Sp ∧
          Sp.valuationOver (f ≫ (C.bridge i).P.h k) = w.comap (functionFieldMap (T.f i)) := by
    intro A _ _ _ f φ _ hf
    obtain ⟨Sp, hd, hfl, hv⟩ := exists_flipTransformPrimeDivisor_eq_some hD hsm f φ hf Sm
    refine ⟨Sp, hd, hfl, ?_⟩
    rw [valuationOver_comp, hv]
    exact (valuationOver_comp (X := (C.bridge i).P.model k) Sm _ _).symm.trans
      ((valuationOver_congr (X := (C.bridge i).P.model k) Sm heq.symm).trans hSm)
  unfold TerminalChain.flipTarget TerminalChain.flipTargetMap
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h =>
    obtain ⟨Sp, hd, hfl, hv⟩ :=
      key ((C.bridge i).P.gp k) (𝟙 _) (Category.id_comp _).symm
    have hd1 : IsDominant ((C.bridge i).P.toBase ((⟨k.1 + 1, h⟩ : Fin _) : ℕ)) := by
      change IsDominant ((C.bridge i).P.πY k); rw [hpeq]; infer_instance
    refine ⟨Sp, hfl, w, hw, hd1, ?_⟩
    rw [← hv]
    exact @valuationOver_congr _ _ _ _ _ _ Sp _ _ hd1 _ hpeq
  | isFalse h =>
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    let φ : C.model (C.flipTargetOf i k (isFalse h)) ≅ (C.bridge i).P.Y k :=
      (C.bridge i).e.symm ≪≫ eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)
    obtain ⟨Sp, hd, hfl, hv⟩ := key (C.flipTargetMapOf i k (isFalse h)) φ.hom
      (Category.assoc _ _ _).symm
    haveI : IsDominant (X := C.model (C.flipTargetOf i k (isFalse h))) (C.junction (i + 1)).p :=
      (C.junction (i + 1)).isBirationalMorphism.isDominant
    refine ⟨Sp, hfl, Sp.valuationOver (C.junction (i + 1)).p, ⟨w, hw, ?_⟩, rfl⟩
    have hfp := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
    haveI : IsDominant (X := C.model (C.flipTargetOf i k (isFalse h)))
        ((C.junction (i + 1)).p ≫ T.fp i) :=
      ⟨hfp.denseRange.comp (C.junction (i + 1)).isBirationalMorphism.isDominant.denseRange
        (Scheme.Hom.continuous _)⟩
    have heq2 : ((C.junction (i + 1)).p ≫ T.fp i : C.model (C.flipTargetOf i k (isFalse h)) ⟶ _) =
        C.flipTargetMapOf i k (isFalse h) ≫ (C.bridge i).P.h k := by
      change _ = ((C.bridge i).e.inv ≫ eqToHom _ ≫ (C.bridge i).P.gp k) ≫ (C.bridge i).P.h k
      rw [Category.assoc, Category.assoc, ← hpeq]
      change _ = (C.bridge i).e.inv ≫ eqToHom _ ≫ (C.bridge i).P.toBase (k.1 + 1)
      rw [eqToHom_comp_toBase, (C.bridge i).toBase_end_eq, Iso.inv_hom_id_assoc]
      exacts [rfl, hmk]
    exact (valuationOver_comp (X := C.model (C.flipTargetOf i k (isFalse h))) Sp
      (C.junction (i + 1)).p (T.fp i)).symm.trans ((valuationOver_congr Sp heq2).trans hv)

end LabelTransform

/-! ### Deep centres and surfaces off the bad loci -/

namespace Flip

open MMP.Mori

section FourfoldCorrespondence

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
  [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- **Deep centres off the bad loci.** A valuation with centre of codimension at least three,
not centred in `(f⁻)⁻¹(Z ∖ U)`, transports to a valuation with centre of codimension at least
three, not centred in `(f⁺)⁻¹(Z ∖ U)`. -/
private theorem transport_isDeepCentred (h : IsBirationalPair sXm sZ sXp fm fp)
    [IsDominant fm] [IsDominant fp] {U : Z.Opens} (hUm : IsBiregular fm U)
    (hUp : IsBiregular fp U) {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    (hdeep : ∃ Zc : IrreducibleCloseds Xm, MMP.Intersection.IsCentre ℂ sXm v Zc ∧
      3 ≤ codimension Zc)
    (hgood : ¬ ∃ Zc : IrreducibleCloseds Xm, MMP.Intersection.IsCentre ℂ sXm v Zc ∧
      (Zc : Set Xm) ⊆ fm ⁻¹' (U : Set Z)ᶜ) :
    (∃ Zc' : IrreducibleCloseds Xp, MMP.Intersection.IsCentre ℂ sXp (transport h v) Zc' ∧
      3 ≤ codimension Zc') ∧
      ¬ ∃ Zc' : IrreducibleCloseds Xp, MMP.Intersection.IsCentre ℂ sXp (transport h v) Zc' ∧
        (Zc' : Set Xp) ⊆ fp ⁻¹' (U : Set Z)ᶜ := by
  obtain ⟨Zc, hZ, h3⟩ := hdeep
  obtain ⟨Zc', x, x', hZ', hZx, hZ'x', hxx⟩ := exists_isCentre_of_comap_eq h hZ
    (comap_transport h v)
  have hU : fm x ∈ U := by
    by_contra hn
    refine hgood ⟨Zc, hZ, ?_⟩
    rw [hZx, (U.isOpen.isClosed_compl.preimage fm.continuous).closure_subset_iff,
      Set.singleton_subset_iff]
    exact hn
  have hU' : fp x' ∈ U := hxx ▸ hU
  refine ⟨⟨Zc', hZ', ?_⟩, ?_⟩
  · rw [codimension_eq_coheight_of_eq_closure hZ'x', ← coheight_map_of_isBiregular hUp hU', hxx,
      coheight_map_of_isBiregular hUm hU, ← codimension_eq_coheight_of_eq_closure hZx]
    exact h3
  · rintro ⟨Zc'', hZ'', hZ''W⟩
    obtain rfl := isCentre_unique h.isNormalVariety_plus.1 hZ' hZ''
    exact hZ''W (hZ'x' ▸ subset_closure rfl) hU'

/-- **Sums over the surfaces off the bad loci.** Over an open `U` over which `f⁻` and `f⁺` are
isomorphisms, sums over the irreducible surfaces of the fourfolds `X⁻` and `X⁺` not contained in
the preimages of `Z ∖ U` agree, for summands which agree at corresponding surfaces. -/
private theorem finsum_surface_eq {M : Type*} [AddCommMonoid M] [LocallyOfFiniteType sXm]
    [LocallyOfFiniteType sXp] {U : Z.Opens} (hUm : IsBiregular fm U) (hUp : IsBiregular fp U)
    (hdimm : topologicalKrullDim Xm = 4) (hdimp : topologicalKrullDim Xp = 4)
    (F : IrreducibleCloseds Xm → M) (G : IrreducibleCloseds Xp → M)
    (hFG : ∀ (V : IrreducibleCloseds Xm) (V' : IrreducibleCloseds Xp) (y : Xm) (y' : Xp),
      (V : Set Xm) = closure {y} → (V' : Set Xp) = closure {y'} → fm y ∈ U → fp y' = fm y →
        topologicalKrullDim (V : Set Xm) = 2 → topologicalKrullDim (V' : Set Xp) = 2 →
          F V = G V') :
    ∑ᶠ (V : IrreducibleCloseds Xm) (_ : topologicalKrullDim (V : Set Xm) = 2 ∧
        ¬ (V : Set Xm) ⊆ fm ⁻¹' (U : Set Z)ᶜ), F V =
      ∑ᶠ (V' : IrreducibleCloseds Xp) (_ : topologicalKrullDim (V' : Set Xp) = 2 ∧
        ¬ (V' : Set Xp) ⊆ fp ⁻¹' (U : Set Z)ᶜ), G V' := by
  classical
  let eM := irreducibleSetEquivPoints (α := Xm)
  let eP := irreducibleSetEquivPoints (α := Xp)
  have hgM : ∀ V : IrreducibleCloseds Xm, (V : Set Xm) = closure {eM V} := fun V => by
    conv_lhs => rw [← eM.symm_apply_apply V]
    rfl
  have hgP : ∀ V : IrreducibleCloseds Xp, (V : Set Xp) = closure {eP V} := fun V => by
    conv_lhs => rw [← eP.symm_apply_apply V]
    rfl
  have hCm : IsClosed (fm ⁻¹' (U : Set Z)ᶜ) := U.isOpen.isClosed_compl.preimage fm.continuous
  have hCp : IsClosed (fp ⁻¹' (U : Set Z)ᶜ) := U.isOpen.isClosed_compl.preimage fp.continuous
  have hsubM : ∀ V : IrreducibleCloseds Xm, (V : Set Xm) ⊆ fm ⁻¹' (U : Set Z)ᶜ ↔ fm (eM V) ∉ U :=
    fun V => by rw [hgM V, hCm.closure_subset_iff, Set.singleton_subset_iff]; rfl
  have hsubP : ∀ V : IrreducibleCloseds Xp, (V : Set Xp) ⊆ fp ⁻¹' (U : Set Z)ᶜ ↔ fp (eP V) ∉ U :=
    fun V => by rw [hgP V, hCp.closure_subset_iff, Set.singleton_subset_iff]; rfl
  have hdM : ∀ y : Xm, topologicalKrullDim (closure {y} : Set Xm) = 2 ↔ Order.coheight y = 2 :=
    fun y => eq_two_iff_of_add_eq_four (topologicalKrullDim_closure_add_coheight sXm hdimm y)
  have hdP : ∀ y : Xp, topologicalKrullDim (closure {y} : Set Xp) = 2 ↔ Order.coheight y = 2 :=
    fun y => eq_two_iff_of_add_eq_four (topologicalKrullDim_closure_add_coheight sXp hdimp y)
  let σ : Xm → Xp := fun y => Classical.epsilon fun y' => fp y' = fm y
  have hσ : ∀ y, fm y ∈ U → fp (σ y) = fm y := fun y hy =>
    Classical.epsilon_spec (exists_map_eq_of_isBiregular hUp hy)
  let E : IrreducibleCloseds Xm → IrreducibleCloseds Xp := fun V => eP.symm (σ (eM V))
  have hE : ∀ V, eP (E V) = σ (eM V) := fun V => eP.apply_symm_apply _
  have hEc : ∀ V, ((E V : IrreducibleCloseds Xp) : Set Xp) = closure {σ (eM V)} := fun V => rfl
  have hcoh : ∀ y, fm y ∈ U → Order.coheight (σ y) = Order.coheight y := fun y hy => by
    rw [← coheight_map_of_isBiregular hUp ((hσ y hy).symm ▸ hy), hσ y hy,
      coheight_map_of_isBiregular hUm hy]
  change ∑ᶠ V ∈ {V : IrreducibleCloseds Xm | topologicalKrullDim (V : Set Xm) = 2 ∧
      ¬ (V : Set Xm) ⊆ fm ⁻¹' (U : Set Z)ᶜ}, F V =
    ∑ᶠ V' ∈ {V' : IrreducibleCloseds Xp | topologicalKrullDim (V' : Set Xp) = 2 ∧
      ¬ (V' : Set Xp) ⊆ fp ⁻¹' (U : Set Z)ᶜ}, G V'
  refine finsum_mem_eq_of_bijOn E ⟨fun V hV => ?_, fun V₁ h₁ V₂ h₂ h12 => ?_, fun V' hV' => ?_⟩
    fun V hV => ?_
  · obtain ⟨hV2, hVU⟩ := hV
    have hy : fm (eM V) ∈ U := not_not.mp fun h => hVU ((hsubM V).2 h)
    refine ⟨?_, fun h => (hsubP (E V)).1 h (by rw [hE, hσ _ hy]; exact hy)⟩
    rw [hEc, hdP, hcoh _ hy, ← hdM, ← hgM]
    exact hV2
  · have hy₁ : fm (eM V₁) ∈ U := not_not.mp fun h => h₁.2 ((hsubM V₁).2 h)
    have hy₂ : fm (eM V₂) ∈ U := not_not.mp fun h => h₂.2 ((hsubM V₂).2 h)
    have hσ12 : σ (eM V₁) = σ (eM V₂) := by rw [← hE, ← hE, h12]
    have h' : fm (eM V₁) = fm (eM V₂) := by rw [← hσ _ hy₁, ← hσ _ hy₂, hσ12]
    exact eM.injective (eq_of_map_eq_of_isBiregular hUm hy₁ h')
  · obtain ⟨hV'2, hV'U⟩ := hV'
    have hy' : fp (eP V') ∈ U := not_not.mp fun h => hV'U ((hsubP V').2 h)
    obtain ⟨y, hyy⟩ := exists_map_eq_of_isBiregular hUm hy'
    have hy : fm y ∈ U := hyy ▸ hy'
    have hσy : σ y = eP V' :=
      eq_of_map_eq_of_isBiregular hUp ((hσ y hy).symm ▸ hy) ((hσ y hy).trans hyy)
    have hcy : Order.coheight y = 2 := by
      rw [← hcoh y hy, hσy, ← hdP, ← hgP]
      exact hV'2
    refine ⟨eM.symm y, ⟨?_, fun h => (hsubM _).1 h (by rw [eM.apply_symm_apply]; exact hy)⟩, ?_⟩
    · change topologicalKrullDim (closure {y} : Set Xm) = 2
      exact (hdM y).2 hcy
    · change eP.symm (σ (eM (eM.symm y))) = V'
      rw [eM.apply_symm_apply, hσy, eP.symm_apply_apply]
  · have hy : fm (eM V) ∈ U := not_not.mp fun h => hV.2 ((hsubM V).2 h)
    refine hFG V (E V) (eM V) (σ (eM V)) (hgM V) (hEc V) hy (hσ _ hy) hV.1 ?_
    rw [hEc, hdP, hcoh _ hy, ← hdM, ← hgM]
    exact hV.1

end FourfoldCorrespondence

end Flip

/-! ### Surfaces of a closed set of codimension two, and branch numbers off the bad loci -/

namespace Flip

open MMP.Mori

section FiniteSurfaces

variable {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [LocallyOfFiniteType sY]

/-- **Finitely many surfaces in a closed set of codimension two.** On a fourfold `Y` of finite
type over `ℂ`, a closed subset `W` all of whose points have coheight at least two contains only
finitely many irreducible surfaces: each is an irreducible component of `W`. -/
private theorem finite_setOf_surface_subset [IsProper sY] (hY : topologicalKrullDim Y = 4)
    {W : Set Y} (hW : IsClosed W) (h2 : ∀ y ∈ W, 2 ≤ Order.coheight y) :
    {V : IrreducibleCloseds Y | (V : Set Y) ⊆ W ∧
      topologicalKrullDim (V : Set Y) = 2}.Finite := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨S, hSf, hSc, hSi, hWS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hW
  refine (hSf.preimage (f := fun V : IrreducibleCloseds Y => (V : Set Y))
    SetLike.coe_injective.injOn).subset fun V ⟨hVW, hV2⟩ => ?_
  change (V : Set Y) ∈ S
  let e := irreducibleSetEquivPoints (α := Y)
  have hgV : (V : Set Y) = closure {e V} := by
    conv_lhs => rw [← e.symm_apply_apply V]
    rfl
  obtain ⟨t, htS, hVt⟩ : ∃ t ∈ S, (V : Set Y) ⊆ t := by
    classical
    have hfin : S = (hSf.toFinset : Set (Set Y)) := hSf.coe_toFinset.symm
    obtain ⟨t, ht, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp V.isIrreducible)
      hSf.toFinset (fun t ht => hSc t (hSf.mem_toFinset.mp ht)) (by rw [← hfin, ← hWS]; exact hVW)
    exact ⟨t, hSf.mem_toFinset.mp ht, hsub⟩
  have hgen := (hSi t htS).isGenericPoint_genericPoint_closure
  rw [(hSc t htS).closure_eq] at hgen
  have hspec : (hSi t htS).genericPoint ⤳ e V := hgen.specializes (hVt (hgV ▸ subset_closure rfl))
  have hmem : (hSi t htS).genericPoint ∈ W := hWS ▸ Set.mem_sUnion_of_mem hgen.mem htS
  have hc2 : Order.coheight (e V) = 2 := by
    have := topologicalKrullDim_closure_add_coheight sY hY (e V)
    rw [← hgV] at this
    exact (eq_two_iff_of_add_eq_four this).1 hV2
  by_cases hne : (hSi t htS).genericPoint = e V
  · have : (V : Set Y) = t := by
      rw [hgV, ← hne]
      exact hgen.def
    exact this ▸ htS
  · have hlt : e V < (hSi t htS).genericPoint :=
      lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hspec) fun h =>
        hne (hspec.antisymm (Scheme.le_iff_specializes.mp h)).eq
    have h3 := Order.coheight_add_one_le hlt
    rw [hc2] at h3
    exact absurd ((add_le_add (h2 _ hmem) le_rfl).trans h3 : (2 : ℕ∞) + 1 ≤ 2) (by decide)

end FiniteSurfaces

section BranchNumber

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- A morphism biregular over an open `O` identifies the prime divisors of its source whose
generic point maps into a subset `A ⊆ O` with the prime divisors of its target whose generic
point lies in `A`. -/
private theorem ncard_primeDivisor_map_mem_eq {N T : Scheme.{0}} (σ : N ⟶ T) {O : T.Opens}
    (hO : IsBiregular σ O) {A : Set T} (hA : A ⊆ O) :
    {P : AlgebraicGeometry.PrimeDivisor N | σ P.genericPoint ∈ A}.ncard =
      {Q : AlgebraicGeometry.PrimeDivisor T | Q.genericPoint ∈ A}.ncard := by
  refine Set.ncard_congr (fun P hP => AlgebraicGeometry.PrimeDivisor.ofCoheightOne
      (σ P.genericPoint) (by
        rw [coheight_map_of_isBiregular hO (hA hP)]
        exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P))
    (fun P hP => ?_) (fun P₁ P₂ h₁ h₂ h => ?_) (fun Q hQ => ?_)
  · change AlgebraicGeometry.PrimeDivisor.genericPoint _ ∈ A
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hP
  · have h' := congrArg AlgebraicGeometry.PrimeDivisor.genericPoint h
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at h'
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_isBiregular hO (hA h₁) h')
  · obtain ⟨p, hp⟩ := exists_map_eq_of_isBiregular hO (hA hQ)
    have hc : Order.coheight p = 1 := by
      rw [← coheight_map_of_isBiregular hO (hp ▸ hA hQ), hp,
        AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne p hc, ?_,
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_⟩
    · change σ (AlgebraicGeometry.PrimeDivisor.genericPoint _) ∈ A
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hp]
      exact hQ
    · rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hp]

/-- **Branch numbers over a biregular open.** Let `f : X ⟶ Z` be biregular over an open `U`, `S` a
prime divisor of `X` and `V` a prime divisor of `Z`, and `σ : S^ν ⟶ V^ν` a proper birational
morphism of the normalizations over `f`. For a point `x` with `f(x) ∈ U`, the branch number of
`S` along `closure {x}` is the number of prime divisors of `V^ν` over `f(x)`. -/
private theorem branchNumber_eq_ncard_of_comp_eq {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (f : X ⟶ Z) {U : Z.Opens} (hU : IsBiregular f U)
    (S : MMP.Mori.PrimeDivisor X) (V : MMP.Mori.PrimeDivisor Z)
    (σ : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme V) [IsProper σ]
    (hσb : IsBirationalMorphism σ)
    (hσ : σ ≫ primeDivisorNormalization V = primeDivisorNormalization S ≫ f) {x : X}
    (hx : f x ∈ U) :
    branchNumber S (closure {x}) =
      {Q : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme V) |
        primeDivisorNormalization V Q.genericPoint = f x}.ncard := by
  have := isFinite_primeDivisorNormalization sX S
  haveI : IsIntegral (primeDivisorNormalizationScheme S) := by
    haveI := S.integral
    exact Scheme.isIntegral_normalizationScheme _
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  haveI : IsIntegral (primeDivisorNormalizationScheme V) := by
    haveI := V.integral
    exact Scheme.isIntegral_normalizationScheme _
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  haveI : IsNormal (primeDivisorNormalizationScheme V) := by
    haveI := V.integral
    exact Scheme.isNormal_normalizationScheme _
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hσa : ∀ p, primeDivisorNormalization V (σ p) = f (primeDivisorNormalization S p) :=
    fun p => by rw [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply]
  have hA : primeDivisorNormalization V ⁻¹' {f x} ⊆ (biregularLocus σ : Set _) := by
    intro q hq
    refine mem_biregularLocus_of_finite σ hσb
      (((primeDivisorNormalization S).finite_preimage_singleton x).subset fun p hp => ?_)
    have h1 : f (primeDivisorNormalization S p) = f x := by
      rw [← hσa, show σ p = q from hp]; exact hq
    exact (eq_of_map_eq_of_isBiregular hU hx h1.symm).symm
  rw [branchNumber_eq_ncard sX S x]
  have hset : {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S P.genericPoint = x} =
      {P | σ P.genericPoint ∈ primeDivisorNormalization V ⁻¹' {f x}} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, hσa]
    exact ⟨fun h => h ▸ rfl, fun h => (eq_of_map_eq_of_isBiregular hU hx h.symm).symm⟩
  rw [hset, ncard_primeDivisor_map_mem_eq σ (MMP.Mori.isBiregular_biregularLocus σ) hA]
  rfl

/-- The image `f⁻(S)` of a prime divisor `S` with a strict transform is a prime divisor `V` of
`Z`. -/
private theorem exists_primeDivisor_support_eq_image {Xm Xp Z : Scheme.{0}} [IsReduced Xm]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm]
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') :
    ∃ V : MMP.Mori.PrimeDivisor Z, (V.support : Set Z) = fm '' S.support := by
  unfold flipTransformPrimeDivisor at hS'
  obtain ⟨E, hE, -⟩ := Option.bind_eq_some_iff.mp hS'
  have hη := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm S E).mp hE
  refine ⟨E, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure S,
    ← fm.isClosedMap.closure_image_eq_of_continuous fm.continuous, Set.image_singleton, hη]

/-- **Branch numbers off the bad locus.** For a fourfold step diagram `X⁻ → Z ← X⁺` with both
maps small, a prime divisor `S` of `X⁻` with strict transform `S'`, and corresponding points
`x`, `x'` over the common biregular locus, the branch numbers of `S` along `closure {x}` and of
`S'` along `closure {x'}` agree. -/
private theorem branchNumber_eq_of_isFourfoldStepDiagram
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hdiag : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') {x : Xm}
    (hx : fm x ∈ commonBiregularLocus fm fp) {x' : Xp} (hx' : fp x' = fm x) :
    branchNumber S (closure {x}) = branchNumber S' (closure {x'}) := by
  have hZ := hdiag.isNormalVariety_target
  haveI : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    have := hZ.1
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  haveI : LocallyOfFiniteType sXm := hdiag.isNormalVariety_minus.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sXp := hdiag.isNormalVariety_plus.1.toLocallyOfFiniteType
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hdiag.isProjectiveMorphism_minus
  obtain ⟨V, hV⟩ := exists_primeDivisor_support_eq_image hS'
  obtain ⟨⟨σm, hσmp, hσmb, hσm⟩, ⟨σp, hσpp, hσpb, hσp⟩⟩ :=
    hdiag.exists_normalization_comp_eq hsmall hS' hV
  haveI : IsProper σm := isProper_of_isProjectiveMorphism _ hσmp
  haveI : IsProper σp := isProper_of_isProjectiveMorphism _ hσpp
  rw [branchNumber_eq_ncard_of_comp_eq (sX := sXm) fm (isBiregular_commonBiregularLocus_left fm fp)
      S V σm hσmb hσm hx,
    branchNumber_eq_ncard_of_comp_eq (sX := sXp) fp (isBiregular_commonBiregularLocus_right fm fp)
      S' V σp hσpb hσp (hx' ▸ hx), hx']

variable {V : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]

/-- `branchNumber_eq_of_isFourfoldStepDiagram` for `f⁺` precomposed with an isomorphism. -/
private theorem branchNumber_eq_of_iso_comp {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {g : V ⟶ Z}
    (hdiag : IsFourfoldStepDiagram sXm sZ sV K B fm g)
    (hsmall : IsSmallMorphism sXm sZ fm) {A : Scheme.{0}} (φ : A ≅ V) {fp : A ⟶ Z}
    (hfp : fp = φ.hom ≫ g) {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor A}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') {x : Xm}
    (hx : fm x ∈ commonBiregularLocus fm fp) {x' : A} (hx' : fp x' = fm x) :
    branchNumber S (closure {x}) = branchNumber S' (closure {x'}) := by
  subst hfp
  rw [commonBiregularLocus_iso_comp] at hx
  rw [branchNumber_eq_of_isFourfoldStepDiagram hdiag hsmall
    (flipTransformPrimeDivisor_iso_comp fm g φ hS') hx (x' := φ.hom x')
    (by rw [← Scheme.Hom.comp_apply]; exact hx'), ← Iso.image_closure_singleton,
    Iso.branchNumber_primeDivisorEquivOfIso]

end BranchNumber

end Flip

/-- The bad locus `W⁻` of a flip is the preimage of the complement of the common biregular
locus. -/
private theorem coe_badLocusSource {T : StabilizedSmallKltTail} {Q : PreparedChain T}
    (μ : Q.FlipMove) : (μ.badLocusSource : Set (Q.chain.model μ.source.1)) =
      μ.sourceMap ⁻¹' (commonBiregularLocus μ.sourceMap μ.targetMap : Set μ.base)ᶜ := by
  change ((badLocusMinus μ.sourceMap μ.targetMap : Closeds (Q.chain.model μ.source.1)) :
    Set (Q.chain.model μ.source.1)) = _
  rw [coe_badLocusMinus, coe_badLocusBase]

/-- The bad locus `W⁺` of a flip is the preimage of the complement of the common biregular
locus. -/
private theorem coe_badLocusTarget {T : StabilizedSmallKltTail} {Q : PreparedChain T}
    (μ : Q.FlipMove) : (μ.badLocusTarget : Set (Q.chain.model μ.target.1)) =
      μ.targetMap ⁻¹' (commonBiregularLocus μ.sourceMap μ.targetMap : Set μ.base)ᶜ := by
  change ((badLocusPlus μ.sourceMap μ.targetMap : Closeds (Q.chain.model μ.target.1)) :
    Set (Q.chain.model μ.target.1)) = _
  rw [coe_badLocusPlus, coe_badLocusBase]

open MMP.Mori in
private theorem solution {T : StabilizedSmallKltTail} (Q : PreparedChain T) (μ : Q.FlipMove)
    (D D' : ℤ)
    (hD : Q.IsDifficulty μ.source D) (hD' : Q.IsDifficulty μ.target D')
    (w w' : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v ∈ Q.flipBadSet μ, Q.chain.IsValuationWeight Q.scale μ.source.1 v (w v))
    (hw' : ∀ v ∈ Q.flipBadSet μ,
      ∃ v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) ∧
          Q.chain.IsValuationWeight Q.scale μ.target.1 v' (w' v)) :
    D - D' = ∑ᶠ v ∈ Q.flipBadSet μ, ((w v : ℤ) - w' v) := by
  classical
  haveI : Finite Q.chain.Label := Q.chain.finite_label
  letI : Fintype Q.chain.Label := Fintype.ofFinite _
  -- the step diagram of the flip, and the target as `V_{k+1}` up to isomorphism
  have hdiag := (Q.chain.bridge μ.1.1).P.isFourfoldStepDiagram μ.1.2 μ.1.2.2
  have hsm : IsSmallMorphism (Q.chain.modelStructure μ.source.1)
      ((Q.chain.bridge μ.1.1).P.sT μ.1.2) μ.sourceMap :=
    (Q.chain.bridge μ.1.1).isSmallMorphism μ.1.2 μ.1.2.2
  obtain ⟨φ, hφ, hft⟩ := Flip.exists_isIso_flipTargetMap_eq Q.chain μ.1.1 μ.1.2
  have hfp : μ.targetMap = (asIso φ).hom ≫ (Q.chain.bridge μ.1.1).P.gp μ.1.2 := hft
  obtain ⟨hpp, hbp, hcp, -⟩ := Flip.flipTargetMapOf_properties Q.chain μ.1.1 μ.1.2 inferInstance
  haveI : IsProper μ.targetMap := hpp
  haveI : IsProper μ.sourceMap :=
    isProper_of_isProjectiveMorphism _ hdiag.isProjectiveMorphism_minus
  have hcp' : μ.targetMap ≫ (Q.chain.bridge μ.1.1).P.sT μ.1.2 =
      Q.chain.modelStructure μ.target.1 := hcp
  have hsA : (asIso φ).hom ≫ (Q.chain.bridge μ.1.1).P.sY μ.1.2 =
      Q.chain.modelStructure μ.target.1 := by
    have h1 : (asIso φ).hom ≫ (Q.chain.bridge μ.1.1).P.gp μ.1.2 ≫
        (Q.chain.bridge μ.1.1).P.sT μ.1.2 = Q.chain.modelStructure μ.target.1 := by
      rw [← Category.assoc]
      exact hfp ▸ hcp'
    rw [← h1, hdiag.comp_eq_plus]
  obtain ⟨hnvm, hlftm, hprm, hdimm⟩ := Side.model_facts Q μ.source
  obtain ⟨hnvp, hlftp, hprp, hdimp⟩ := Side.model_facts Q μ.target
  haveI := hlftm
  haveI := hlftp
  haveI := hprm
  haveI := hprp
  have hprojp := (TerminalChain.isKltTerminalPair_modelBoundary Q.chain μ.target.1).2.2.1
  have hpair : Flip.IsBirationalPair (Q.chain.modelStructure μ.source.1)
      ((Q.chain.bridge μ.1.1).P.sT μ.1.2) (Q.chain.modelStructure μ.target.1) μ.sourceMap
      μ.targetMap :=
    ⟨hnvm, hnvp, hdiag.isNormalVariety_target, hdiag.comp_eq_minus, hcp', inferInstance, hpp,
      hdiag.isBirationalMorphism_minus, hbp⟩
  -- the common biregular locus and the bad loci
  set U := commonBiregularLocus μ.sourceMap μ.targetMap with hU
  have hUm : IsBiregular μ.sourceMap U := isBiregular_commonBiregularLocus_left _ _
  have hUp : IsBiregular μ.targetMap U := isBiregular_commonBiregularLocus_right _ _
  have hWm : (μ.badLocusSource : Set (Q.chain.model μ.source.1)) =
      μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ := coe_badLocusSource μ
  have hWp : (μ.badLocusTarget : Set (Q.chain.model μ.target.1)) =
      μ.targetMap ⁻¹' (U : Set μ.base)ᶜ := coe_badLocusTarget μ
  have hWmc : IsClosed (μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ) :=
    U.isOpen.isClosed_compl.preimage μ.sourceMap.continuous
  have hWpc : IsClosed (μ.targetMap ⁻¹' (U : Set μ.base)ᶜ) :=
    U.isOpen.isClosed_compl.preimage μ.targetMap.continuous
  obtain ⟨hcohm, hcohp⟩ := Flip.two_le_coheight_of_mem_badLoci Q μ
  rw [hWm] at hcohm
  rw [hWp] at hcohp
  have hGm := Flip.finite_setOf_surface_subset (Q.chain.modelStructure μ.source.1) hdimm hWmc
    hcohm
  have hGp := Flip.finite_setOf_surface_subset (Q.chain.modelStructure μ.target.1) hdimp hWpc
    hcohp
  have hclm : ∀ (V : IrreducibleCloseds (Q.chain.model μ.source.1)) (y),
      (V : Set (Q.chain.model μ.source.1)) = closure {y} →
        ((V : Set _) ⊆ μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ ↔ μ.sourceMap y ∉ U) :=
    fun V y hV => by rw [hV, hWmc.closure_subset_iff, Set.singleton_subset_iff]; rfl
  -- the labels: centres, strict transforms, defaults, bad branch counts
  choose cm hcm using fun S => exists_isLabelCentre Q.chain S μ.source.1
  have hcpex : ∀ S, ∃ Sp : MMP.Mori.PrimeDivisor (Q.chain.model μ.target.1),
      flipTransformPrimeDivisor μ.sourceMap μ.targetMap (cm S) = some Sp ∧
        Q.chain.IsLabelCentre S μ.target.1 Sp := fun S =>
    LabelTransform.exists_flipTransformPrimeDivisor_isLabelCentre Q.chain μ.1.1 μ.1.2 (hcm S)
  choose cp hcpT hcpl using hcpex
  have hbb := fun S => FlipMove.badBranchCount_eq_finsum_branchNumber μ S (hcm S)
    (rm := fun V => branchNumber (cm S) (V : Set (Q.chain.model μ.source.1)))
    (rp := fun V => branchNumber (cp S) (V : Set (Q.chain.model μ.target.1)))
    (fun V => Or.inl ⟨_, hcm S, rfl⟩) (fun V => Or.inl ⟨_, hcpl S, rfl⟩)
  have hbbp : ∀ S, badBranchCount (cp S) (μ.badLocusTarget : Set (Q.chain.model μ.target.1)) =
      ∑ᶠ (V : IrreducibleCloseds (Q.chain.model μ.target.1))
        (_ : (V : Set (Q.chain.model μ.target.1)) ⊆ μ.badLocusTarget ∧
          topologicalKrullDim (V : Set (Q.chain.model μ.target.1)) = 2),
        branchNumber (cp S) V := fun S => by
    obtain ⟨Sp, hSp, hb⟩ := (hbb S).2
    obtain rfl : Sp = cp S := Option.some_injective _ (hSp.symm.trans (hcpT S))
    exact hb
  choose d₀ hd₀ using Q.isLabelDefault_const
  -- transport of valuations
  have hΦΨ : ∀ v, (Flip.transport hpair.symm) ((Flip.transport hpair) v) = v :=
    Flip.transport_symm_transport hpair
  have hΨΦ : ∀ v', (Flip.transport hpair) ((Flip.transport hpair.symm) v') = v' :=
    Flip.transport_symm_transport hpair.symm
  have hΨinj : Function.Injective (Flip.transport hpair) :=
    Function.LeftInverse.injective (Flip.transport_symm_transport hpair)
  -- the two difficulties
  obtain ⟨wm', βm, dm, ρm, hwm', hβm, hdm, hρm, rfl⟩ := hD
  obtain ⟨wp', βp, dp, ρp, hwp', hβp, hdp, hρp, rfl⟩ := hD'
  have hdm₀ : ∀ S, dm S = d₀ S := fun S => isLabelDefault_unique (hdm S) (hd₀ S _ μ.source.2)
  have hdp₀ : ∀ S, dp S = d₀ S := fun S => isLabelDefault_unique (hdp S) (hd₀ S _ μ.target.2)
  -- weights of valuations centred in the bad loci
  have hwtm := fun v => Side.exists_isValuationWeight_of_isCentredIn (v := v) hcohm hwm' hβm
  have hwtp := fun v' => Side.exists_isValuationWeight_of_isCentredIn (v := v') hcohp hwp' hβp
  -- the weighted bad set
  have hA₀ := Q.finite_flipBadSet μ
  have hmem𝔉 : ∀ {v}, v ∈ hA₀.toFinset ↔ v ∈ Q.flipBadSet μ := fun {v} => hA₀.mem_toFinset
  have hWmC : ∀ {v}, Side.IsCentredIn Q μ.source μ.badLocusSource v →
      Side.IsCentredIn Q μ.source (μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ) v := by
    rintro v ⟨Z, hZ, hZW⟩
    exact ⟨Z, hZ, hWm ▸ hZW⟩
  have hA₀W : ∀ v ∈ Q.flipBadSet μ,
      Side.IsCentredIn Q μ.source (μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ) v := fun v hv => hWmC hv.1
  have hw'' : ∀ v ∈ Q.flipBadSet μ,
      Q.chain.IsValuationWeight Q.scale μ.target.1 (Flip.transport hpair v) (w' v) := by
    intro v hv
    obtain ⟨v', hv', hwv'⟩ := hw' v hv
    rwa [← Flip.eq_transport_of_comap_eq hpair hv']
  have hSm := Side.deepSum_add_bracketSum_eq (Q := Q) (x := μ.source)
    (μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ) hcohm hGm hA₀.toFinset w
    (fun v hv => hw v (hmem𝔉.1 hv)) (fun v hv => hA₀W v (hmem𝔉.1 hv))
    (fun v n hc hn hne => by
      refine hmem𝔉.2 ⟨hWmC hc, (Flip.transport hpair) v, Flip.comap_transport hpair v, ?_⟩
      obtain ⟨n', hn'⟩ := hwtp ((Flip.transport hpair) v) (Flip.transport_isCentredIn hpair hc)
      exact ⟨n, n', hn, hn', by omega⟩)
    cm hcm wm' βm dm hwm' hβm hdm
  have hSp := Side.deepSum_add_bracketSum_eq (Q := Q) (x := μ.target)
    (μ.targetMap ⁻¹' (U : Set μ.base)ᶜ) hcohp hGp (hA₀.toFinset.image (Flip.transport hpair))
    (fun v' => w' ((Flip.transport hpair.symm) v'))
    (fun v' hv' => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
      rw [hΦΨ]
      exact hw'' v (hmem𝔉.1 hv))
    (fun v' hv' => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
      exact Flip.transport_isCentredIn hpair (hA₀W v (hmem𝔉.1 hv)))
    (fun v' n hc hn hne => by
      refine Finset.mem_image.2 ⟨(Flip.transport hpair.symm) v', hmem𝔉.2 ?_, hΨΦ v'⟩
      have hc' := Flip.transport_isCentredIn hpair.symm hc
      obtain ⟨n', hn'⟩ := hwtm ((Flip.transport hpair.symm) v') hc'
      refine ⟨hWmC hc', v', ?_, n', n, hn', hn, by omega⟩
      have := Flip.comap_transport hpair ((Flip.transport hpair.symm) v')
      rwa [hΨΦ] at this)
    cp hcpl wp' βp dp hwp' hβp hdp
  -- the deep sums off the bad loci agree
  have X1 : ((∑ᶠ (v) (_ : Side.IsDeepCentred Q μ.source v ∧
        ¬ Side.IsCentredIn Q μ.source (μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ) v), wm' v : ℕ) : ℤ) =
      ((∑ᶠ (v') (_ : Side.IsDeepCentred Q μ.target v' ∧
        ¬ Side.IsCentredIn Q μ.target (μ.targetMap ⁻¹' (U : Set μ.base)ᶜ) v'), wp' v' : ℕ) :
          ℤ) := by
    congr 1
    rw [Iso.finsum_eq_finsum_comp_of_injective (f := wp') hΨinj
      (R := fun v => Side.IsDeepCentred Q μ.source v ∧
        ¬ Side.IsCentredIn Q μ.source (μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ) v) ?_]
    · refine finsum_congr fun v => finsum_congr fun hv => ?_
      have h2 := Flip.transport_isDeepCentred hpair hUm hUp hv.1 hv.2
      exact ((Q.isValuationWeight_target_iff_of_notMem_flipBadSet μ
        (fun hA => hv.2 (hA₀W v hA)) (Flip.comap_transport hpair v) (hwm' v hv.1) _).1
        (hwp' _ h2.1)).symm
    · intro v'
      constructor
      · intro hv'
        exact ⟨Flip.transport hpair.symm v',
          Flip.transport_isDeepCentred hpair.symm hUp hUm hv'.1 hv'.2, hΨΦ v'⟩
      · rintro ⟨v, hv, rfl⟩
        exact Flip.transport_isDeepCentred hpair hUm hUp hv.1 hv.2
  -- the brackets off the bad loci agree
  have BE : ∀ (V : IrreducibleCloseds (Q.chain.model μ.source.1))
      (V' : IrreducibleCloseds (Q.chain.model μ.target.1)) (y) (y'),
      (V : Set (Q.chain.model μ.source.1)) = closure {y} →
      (V' : Set (Q.chain.model μ.target.1)) = closure {y'} → μ.sourceMap y ∈ U →
      μ.targetMap y' = μ.sourceMap y →
      topologicalKrullDim (V : Set (Q.chain.model μ.source.1)) = 2 →
      topologicalKrullDim (V' : Set (Q.chain.model μ.target.1)) = 2 → βm V = βp V' := by
    intro V V' y y' hVy hV'y' hy hyy hV2 hV'2
    have hy' : μ.targetMap y' ∈ U := hyy ▸ hy
    obtain ⟨wβ, r, dβ, hwβ, hr, hdβ, hβeq⟩ := hβm V hV2
    obtain ⟨wβ', r', dβ', hwβ', hr', hdβ', hβeq'⟩ := hβp V' hV'2
    have hcen := Flip.isCentre_iff_isCentre_transport hpair hUm hUp hy hyy hVy hV'y'
    have hv : (∑ᶠ (v) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v V),
          wβ v) =
        ∑ᶠ (v') (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.target.1) v' V'),
          wβ' v' := by
      rw [Iso.finsum_eq_finsum_comp_of_injective (f := wβ') hΨinj
        (R := fun v => MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v V) ?_]
      · refine finsum_congr fun v => finsum_congr fun hv => ?_
        have hv' := (hcen v).1 hv
        refine ((Q.isValuationWeight_target_iff_of_notMem_flipBadSet μ (fun hA => ?_)
          (Flip.comap_transport hpair v) (hwβ v hv) _).1 (hwβ' _ hv')).symm
        obtain ⟨Z, hZ, hZW⟩ := hA₀W v hA
        obtain rfl := isCentre_unique hnvm.1 hZ hv
        exact (hclm Z y hVy).1 hZW hy
      · intro v'
        constructor
        · intro h'
          refine ⟨_, (hcen _).2 ?_, hΨΦ v'⟩
          rwa [hΨΦ]
        · rintro ⟨v, hv, rfl⟩
          exact (hcen v).1 hv
    have hl : (∑ᶠ S, r S * dβ S) = ∑ᶠ S, r' S * dβ' S := finsum_congr fun S => by
      have hrS : r S = branchNumber (cm S) (V : Set _) := by
        rcases hr S with ⟨P, hP, hrP⟩ | ⟨hn, -⟩
        · rw [hrP, isLabelCentre_unique hP (hcm S)]
        · exact absurd (hcm S) (hn _)
      have hrS' : r' S = branchNumber (cp S) (V' : Set _) := by
        rcases hr' S with ⟨P, hP, hrP⟩ | ⟨hn, -⟩
        · rw [hrP, isLabelCentre_unique hP (hcpl S)]
        · exact absurd (hcpl S) (hn _)
      rw [hrS, hrS', isLabelDefault_unique (hdβ S) (hd₀ S _ μ.source.2),
        isLabelDefault_unique (hdβ' S) (hd₀ S _ μ.target.2), hVy, hV'y']
      exact congrArg (· * d₀ S)
        (Flip.branchNumber_eq_of_iso_comp hdiag hsm (asIso φ) hfp (hcpT S) hy hyy)
    rw [hβeq, hβeq', hv, hl]
  have X2 : (∑ᶠ (V : IrreducibleCloseds (Q.chain.model μ.source.1))
        (_ : topologicalKrullDim (V : Set (Q.chain.model μ.source.1)) = 2 ∧
          ¬ (V : Set (Q.chain.model μ.source.1)) ⊆ μ.sourceMap ⁻¹' (U : Set μ.base)ᶜ), βm V) =
      ∑ᶠ (V' : IrreducibleCloseds (Q.chain.model μ.target.1))
        (_ : topologicalKrullDim (V' : Set (Q.chain.model μ.target.1)) = 2 ∧
          ¬ (V' : Set (Q.chain.model μ.target.1)) ⊆ μ.targetMap ⁻¹' (U : Set μ.base)ᶜ),
        βp V' :=
    Flip.finsum_surface_eq (sXm := Q.chain.modelStructure μ.source.1)
      (sXp := Q.chain.modelStructure μ.target.1) hUm hUp hdimm hdimp βm βp BE
  -- the weights of the weighted bad set on `Y⁺`
  have X3 : ∑ v' ∈ hA₀.toFinset.image (Flip.transport hpair),
      (w' (Flip.transport hpair.symm v') : ℤ) = ∑ v ∈ hA₀.toFinset, (w' v : ℤ) := by
    rw [Finset.sum_image (fun a _ b _ h => hΨinj h)]
    exact Finset.sum_congr rfl fun v _ => by rw [hΦΨ]
  -- the branch numbers along the surfaces of the bad loci
  have X4m : ∑ S, (dm S : ℤ) * ∑ V ∈ hGm.toFinset, (branchNumber (cm S) V : ℤ) =
      ∑ S, (d₀ S : ℤ) * badBranchCount (cm S) μ.badLocusSource :=
    Side.sum_mul_sum_branchNumber_eq hGm cm hdm₀ fun S => by rw [(hbb S).1, hWm]
  have X4p : ∑ S, (dp S : ℤ) * ∑ V ∈ hGp.toFinset, (branchNumber (cp S) V : ℤ) =
      ∑ S, (d₀ S : ℤ) * badBranchCount (cp S) μ.badLocusTarget :=
    Side.sum_mul_sum_branchNumber_eq hGp cp hdp₀ fun S => by rw [hbbp S, hWp]
  -- the label terms
  have X5 : ((∑ᶠ S, dm S * ρm S : ℕ) : ℤ) - ((∑ᶠ S, dp S * ρp S : ℕ) : ℤ) =
      ∑ S, (d₀ S : ℤ) * badBranchCount (cm S) μ.badLocusSource -
        ∑ S, (d₀ S : ℤ) * badBranchCount (cp S) μ.badLocusTarget := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum, Nat.cast_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rcases hρm S with ⟨P, hP, hcx, hρP⟩ | ⟨hn, -⟩
    swap
    · exact absurd (hcm S) (hn _)
    rcases hρp S with ⟨P', hP', hcx', hρP'⟩ | ⟨hn', -⟩
    swap
    · exact absurd (hcpl S) (hn' _)
    obtain rfl := isLabelCentre_unique hP (hcm S)
    obtain rfl := isLabelCentre_unique hP' (hcpl S)
    have := Flip.divisorCycleRank_sub_eq_of_iso_comp hdiag hsm (asIso φ) hsA hprojp hfp (hcpT S)
      hρP hρP'
    rw [Nat.cast_mul, Nat.cast_mul, hdm₀, hdp₀, ← mul_sub, ← mul_sub, this]
    rfl
  -- the weighted bad set
  have X6 : ∑ᶠ v ∈ Q.flipBadSet μ, ((w v : ℤ) - w' v) =
      ∑ v ∈ hA₀.toFinset, (w v : ℤ) - ∑ v ∈ hA₀.toFinset, (w' v : ℤ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hA₀, Finset.sum_sub_distrib]
  linear_combination hSm - hSp + X1 + X2 - X3 - X4m + X4p + X5 - X6

end Proof_lem_oai4_c3_flip_difference

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- On a prepared chain, let `μ` be a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)`, written as a
step diagram `Y⁻ → Z ← Y⁺`, with weighted bad set
`𝒜₀ = MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.flipBadSet Q μ`. Then
`𝒟(Y⁻, Θ⁻) - 𝒟(Y⁺, Θ⁺) = ∑_{v ∈ 𝒜₀} (w_v(Y⁻, Θ⁻) - w_v(Y⁺, Θ⁺))`, where `w_v(Y⁺, Θ⁺)` is the
weight of the valuation of `ℂ(Y⁺)` with the same restriction to `ℂ(Z)` as `v`. -/
@[mmp "lem_oai4_c3_flip_difference"]
public theorem difficulty_sub_eq_finsum_flipBadSet (μ : Q.FlipMove) (D D' : ℤ)
    (hD : Q.IsDifficulty μ.source D) (hD' : Q.IsDifficulty μ.target D')
    (w w' : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v ∈ Q.flipBadSet μ, Q.chain.IsValuationWeight Q.scale μ.source.1 v (w v))
    (hw' : ∀ v ∈ Q.flipBadSet μ,
      ∃ v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) ∧
          Q.chain.IsValuationWeight Q.scale μ.target.1 v' (w' v)) :
    D - D' = ∑ᶠ v ∈ Q.flipBadSet μ, ((w v : ℤ) - w' v) :=
  Proof_lem_oai4_c3_flip_difference.solution Q μ D D' hD hD' w w' hw hw'

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
