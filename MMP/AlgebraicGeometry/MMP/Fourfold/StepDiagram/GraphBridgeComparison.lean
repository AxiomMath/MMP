module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChain
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorEffective
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# The graph comparison and the bridge upper bound of the threefold index chain

Two discrepancy comparisons of the threefold index chain (*Projective lc fourfolds*, the index
chain). For a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with normalized graph `(G, u, v)`
and graph divisor `H = u^* D⁻ - v^* D⁺`, every normalized divisorial valuation `ξ` of the common
function field satisfies `a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H) ≥ 0`. For a stabilized tail, a crepant
junction `(p_i, Θ_i)` of `(X_i, B_i)` extracting `I(X_i, B_i)`, its decreased boundary `Θ_i'` and a
finite relative threefold programme over `Z_i` from `(Y_i, Θ_i')`, every model `(V_k, Θ_k)` lies
below the next downstairs pair: `a(ξ; V_k, Θ_k) ≤ a(ξ; X_{i+1}, B_{i+1})`, with equality on the
prime divisors of `V_k`.

## Main results

* `MMP.Fourfold.IsThreefoldGraphDivisor.exists_sub_eq_coeff_pullback`: the comparison
  `a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H) ≥ 0`.
* `MMP.Fourfold.StabilizedTail.IsDecreasedBoundary.le_of_isValuationLogDiscrepancy`: the models
  of a bridge programme lie below `(X_{i+1}, B_{i+1})`, with equality on their prime divisors.

## Implementation notes

* Each result's auxiliary lemmas live in a namespace under `MMP.Fourfold.StepDiagram`
  (`ProofLemIndexcGraph`, `ProofLemIndexcBridgeUpperBound`),
  opened only for that result.
* For the graph comparison, `ξ` is a valuation of `k(G)`, its restrictions `ξ ∘ u^*`, `ξ ∘ v^*` to
  `k(X⁻)`, `k(X⁺)` are the valuations compared, and `ξ(H)` is the coefficient `coeff_E(w^* H)` for
  every proper realization `(W, w, E)` of `ξ` over `G`. Log discrepancies are predicates on values.
* For the bridge bound, the canonical divisor of `V_k` used on a common model `W` is `q_* K_W`,
  which differs from the programme's `K_k` by a principal divisor; log discrepancies do not depend
  on this choice. The dominance of `π_k : V_k ⟶ Z_i` is part of the conclusion.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4], the threefold index chain
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StepDiagram.ProofLemIndexcGraph

open MMP.Mori MMP.Fourfold

/-! ### Divisors over a composite -/

section Comp

variable {X G : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral G] [IsLocallyNoetherian G] [IsNormal G] {sX : X ⟶ Spec (.of ℂ)}

/-- The divisor `(W, f ∘ w, E)` over `X` of a proper divisor `(W, w, E)` over `G`, for a proper
birational `f : G ⟶ X` (the structure morphism of `G` being `f ≫ s_X`). -/
private def compOver (f : G ⟶ X) [IsProper f] (hf : IsBirationalMorphism f)
    {s : G ⟶ Spec (.of ℂ)} (hs : f ≫ sX = s) (D : DivisorOver ℂ s) (hD : IsProper D.f) :
    DivisorOver ℂ sX where
  Y := D.Y
  f := D.f ≫ f
  isNormalVariety := by
    have h := D.isNormalVariety
    rw [Category.assoc, hs]
    exact h
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := hD
    exact isBirationalMorphism_comp_of_isBirational f D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

private theorem compOver_isProper (f : G ⟶ X) [IsProper f] (hf : IsBirationalMorphism f)
    {s : G ⟶ Spec (.of ℂ)} (hs : f ≫ sX = s) (D : DivisorOver ℂ s) (hD : IsProper D.f) :
    IsProper (compOver f hf hs D hD).f := by
  haveI := hD
  change IsProper (D.f ≫ f)
  infer_instance

/-- The valuation of the composite divisor over `X` is `ord_E ∘ f^*`. -/
private theorem compOver_valuation (f : G ⟶ X) [IsProper f] (hf : IsBirationalMorphism f)
    {s : G ⟶ Spec (.of ℂ)} (hs : f ≫ sX = s) (D : DivisorOver ℂ s) (hD : IsProper D.f) :
    haveI : IsDominant f := hf.isDominant
    (compOver f hf hs D hD).valuation = D.valuation.comap (functionFieldMap f) := by
  haveI : IsDominant f := hf.isDominant
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI : IsDominant (D.f ≫ f) := (compOver f hf hs D hD).isDominant
  ext a
  change D.E.divisorialValuation _ = D.E.divisorialValuation _
  congr 1
  exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f f a).symm

end Comp

/-! ### Generic helpers -/

section Helpers

universe u

/-- A scheme separated over `Spec ℂ` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {Y : Scheme.{0}} (s : Y ⟶ Spec (.of ℂ)) [IsSeparated s] :
    IsSeparated (Y ↘ Limits.terminal Scheme) := by
  rw [show (Y ↘ Limits.terminal Scheme) = s ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- If `f(P) = Q` for prime divisors `P`, `Q`, then `f(η_P) = η_Q`. -/
private theorem map_genericPoint_eq_of_image_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (h : f '' (P.support : Set X) = Q.support) : f P.genericPoint = Q.genericPoint := by
  have hP : P.genericPoint ∈ (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hQ : Q.genericPoint ∈ (Q.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have h1 : f P.genericPoint ∈ (Q.support : Set Y) := h ▸ ⟨_, hP, rfl⟩
  rw [← h] at hQ
  obtain ⟨x, hx, hxQ⟩ := hQ
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hx h1
  have h2 : f P.genericPoint ⤳ Q.genericPoint := hxQ ▸ hx.map f.continuous
  exact (h2.antisymm h1).eq

/-- Two points of `X` over the generic point of a prime divisor `Q` of the normal scheme `Y` are
equal, for `f : X ⟶ Y` separated, dominant and birational. -/
private theorem eq_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (Q : MMP.Mori.PrimeDivisor Y) {x₁ x₂ : X}
    (h₁ : f x₁ = Q.genericPoint) (h₂ : f x₂ = Q.genericPoint) : x₁ = x₂ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x₁)) := by rw [h₁]; infer_instance
  haveI : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- A birational morphism induces an isomorphism of local rings at a point over the generic point
of a prime divisor. -/
private theorem isIso_stalkMap_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (P : MMP.Mori.PrimeDivisor Y) {x : X}
    (hx : f x = P.genericPoint) : IsIso (f.stalkMap x) := by
  have := P.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

/-- **The inverse transform over the biregular locus.** If `f(η_P) = η_Q` lies in the biregular
locus of `f`, then `f⁻¹_* Q = P`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus {X Y : Scheme.{u}}
    {f : X ⟶ Y} (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (he : f P.genericPoint = Q.genericPoint) (hQ : Q.genericPoint ∈ biregularLocus f) :
    inverseTransformPrimeDivisor f Q = some P := by
  have hQmem : Q.genericPoint ∈ (Q.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  rw [inverseTransformPrimeDivisor_eq_some_iff]
  refine ⟨⟨Q.genericPoint, hQmem, hQ⟩, ?_⟩
  have := P.integral
  rw [inverseTransformIdeal]
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  ext1
  change (P.support : Set X) = closure (f ⁻¹' ((Q.support : Set Y) ∩ biregularLocus f))
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine le_antisymm (closure_mono ?_) (closure_minimal ?_ isClosed_closure)
  · rintro _ rfl
    exact ⟨he ▸ hQmem, he ▸ hQ⟩
  · rintro x ⟨hxQ, hxV⟩
    have hPV : f P.genericPoint ∈ V := he ▸ hQ
    let x' : (f ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
    let p' : (f ⁻¹ᵁ V).toScheme := ⟨P.genericPoint, hPV⟩
    have hι : ∀ z : (f ⁻¹ᵁ V).toScheme, V.ι ((f ∣_ V) z) = f z.1 := fun z => by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]; rfl
    have h1 : V.ι ((f ∣_ V) p') ⤳ V.ι ((f ∣_ V) x') := by
      rw [hι, hι]
      change f P.genericPoint ⤳ f x
      rw [he, specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hxQ
    rw [V.ι.isOpenEmbedding.isInducing.specializes_iff,
      (f ∣_ V).isOpenEmbedding.isInducing.specializes_iff] at h1
    have h2 := h1.map (f ⁻¹ᵁ V).ι.continuous
    rw [← specializes_iff_mem_closure]
    exact h2

/-- Only `Q` has inverse transform `P`, when `f(η_P) = η_Q`. -/
private theorem eq_of_inverseTransformPrimeDivisor_eq_some {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : MMP.Mori.PrimeDivisor X) (Q Q' : MMP.Mori.PrimeDivisor Y)
    (he : f P.genericPoint = Q.genericPoint) (h : inverseTransformPrimeDivisor f Q' = some P) :
    Q' = Q := by
  have hs := support_inverseTransformPrimeDivisor h
  have hP : P.genericPoint ∈ (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  rw [hs] at hP
  have hcl : IsClosed (f ⁻¹' (Q'.support : Set Y)) :=
    (Q'.idealSheaf.support.isClosed).preimage f.continuous
  have hsub : (inverseTransform f Q'.idealSheaf.support : Set X) ⊆ f ⁻¹' (Q'.support : Set Y) :=
    closure_minimal (fun z hz => hz.1) hcl
  have hQ' : Q.genericPoint ∈ (Q'.support : Set Y) := he ▸ hsub hP
  have := Q'.eq_genericPoint_of_mem_support hQ' Q.coheight_genericPoint
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this.symm

/-- **Coefficients of the strict transform.** If `f(η_{P⁻}) = f⁺(η_P) = η_Q` with `f⁺` an
isomorphism over `η_Q`, the coefficient of `P` in `(f⁺)⁻¹_* f_* D` is that of `P⁻` in `D`. -/
private theorem flipTransform_apply_eq {Xm Xp Z : Scheme.{u}} [IsIntegral Xm] [IsReduced Xm]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsSeparated fm]
    [IsDominant fm] (hfm : Function.Bijective (functionFieldMap fm))
    (Pm : MMP.Mori.PrimeDivisor Xm) (P : MMP.Mori.PrimeDivisor Xp) (Q : MMP.Mori.PrimeDivisor Z)
    (hm : fm Pm.genericPoint = Q.genericPoint) (hp : fp P.genericPoint = Q.genericPoint)
    (hQ : Q.genericPoint ∈ biregularLocus fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D P = D Pm := by
  change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm) fm.toRationalMap D) P
    = D Pm
  rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus P Q hp hQ)
      (fun Q' hQ' => eq_of_inverseTransformPrimeDivisor_eq_some P Q Q' hp hQ'),
    RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm Q).mpr hm)]
  intro Pm' h'
  have h'' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm' Q).mp h'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_genericPoint fm hfm Q h'' hm)

section PullbackComp

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]

private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 := by
  rw [W.2.eq_of_le (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _)]
  trivial

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
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

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (D : DivisorOver ℂ (g ≫ sZ)) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField ℂ (g' ≫ sZ) ξ' := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hY : IsNormalVariety ℂ ((D.f ≫ g) ≫ sZ) := by
    rw [Category.assoc]; exact D.isNormalVariety
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  letI := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] [IsProper g']
    (D : DivisorOver k sX) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
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
    have h : IsProper g' := inferInstance
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

/-- Over a proper birational model `X' ⟶ Z` of a normal variety, a valuation `ξ'` of `ℂ(X')`
restricting on `ℂ(Z)` to the valuation of a divisor over another model `X ⟶ Z` is realized by a
proper divisor over `X'`. -/
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX' : IsNormalVariety ℂ sX') (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') [IsProper g']
    (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX') (D : DivisorOver ℂ sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : DivisorOver ℂ sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' D ξ' h
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField ℂ sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

end Helpers

/-! ### Log discrepancies read from a Cartier presentation -/

section LogDiscrepancy

/-- **The log discrepancy from a Cartier presentation.** Let `X` be a normal variety with a
canonical divisor `K = div(ω)`, `B` a `ℚ`-divisor and `L = m(K + B)` Cartier, `m > 0`. For a
proper divisor `(W, g, E)` over `X` and the pull-back `L' = g^*L`, the log discrepancy of `E` is
`1 + ord_E(g^*ω) - (1/m) coeff_E L'`. -/
private theorem isLogDiscrepancy_of_isPullback {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) {d : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX d)
    {ω : RationalPluriForms sX d 1} (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    {B : QDivisor X} {m : ℕ} {L : Divisor X}
    (hL : Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B)) (hm : 0 < m)
    (hLc : L.IsCartier) (D : DivisorOver ℂ sX) (hDp : IsProper D.f) {L' : Divisor D.Y}
    (hLp : haveI := D.isLocallyNoetherian; haveI := D.isNormal; ∃ hC, L.IsPullback D.f hC L') :
    MMP.Intersection.IsLogDiscrepancy sX d (QDivisor.toRDivisor B) D
      (1 + (D.ordPullback ω : ℝ) - (m : ℝ)⁻¹ * (L'.coeff D.E : ℝ)) := by
  refine ⟨hX, hDp, ω, hω0, ⟨K, hK, fun Γ => (hωK Γ).symm⟩, 1, fun _ => ((m : ℝ)⁻¹),
    fun _ => L, fun _ => L', fun _ => hLc, fun Γ => ?_, fun _ => hLp, ?_⟩
  · have h1 := congrArg (fun G : QDivisor X => G Γ) hL
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast, Finsupp.add_apply] at h1
    change ((L Γ : ℤ) : ℚ) = m * (((K Γ : ℤ) : ℚ) + B Γ) at h1
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      QDivisor.coeff_toRDivisor, hωK]
    change (((K Γ : ℤ) : ℝ)) + ((B Γ : ℚ) : ℝ) = (m : ℝ)⁻¹ * ((L Γ : ℤ) : ℝ)
    have h3 : ((L Γ : ℤ) : ℝ) = (m : ℝ) * (((K Γ : ℤ) : ℝ) + ((B Γ : ℚ) : ℝ)) := mod_cast h1
    have hm0 : (m : ℝ) ≠ 0 := mod_cast hm.ne'
    rw [h3]
    field_simp
  · simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]

/-- The log discrepancy of a valuation is unique. -/
private theorem IsValuationLogDiscrepancy.unique {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : IsValuationLogDiscrepancy sX B ξ a)
    (h' : IsValuationLogDiscrepancy sX B ξ a') : a = a' := by
  obtain ⟨n, D, -, hv, h⟩ := h
  obtain ⟨n', D', -, hv', h'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hv.trans hv'.symm)

end LogDiscrepancy

/-! ### Rational top forms along the step diagram -/

section Forms

variable {k : Type} [Field k] [PerfectField k]

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [LocallyOfFiniteType sX] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  have hpull : pullbackRationalPluriForms sX f τ =
      pullbackFormsAlong (K' := Y.functionField) hω m τ := pullbackForms_eq hω m τ
  rw [hpull]
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    ((ZTensorPower.basis _ m).ne_zero ())

/-- **Every rational top form descends along a birational morphism**: a nonzero rational
`n`-form `ω` on `Y` is `f^*τ` for a nonzero rational `n`-form `τ` on `X`. -/
private theorem exists_pullbackRationalPluriForms_eq {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [LocallyOfFiniteType sX] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (hbij : Function.Bijective (functionFieldMap f)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (ω : RationalPluriForms (f ≫ sX) n 1) (hω0 : ω ≠ 0) :
    ∃ τ : RationalPluriForms sX n 1, τ ≠ 0 ∧ pullbackRationalPluriForms sX f τ = ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 ()
  have hτ : pullbackRationalPluriForms sX f τ = ω := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 τ = ω
    rw [pullbackForms_eq hω₀, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω
    rw [hg]
    exact basis_unit_repr_smul _ ω
  refine ⟨τ, fun h0 => hω0 ?_, hτ⟩
  rw [← hτ, h0]
  change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp

/-- The order along `P` of the pull-back of a form along a morphism depends only on the
morphism. -/
private theorem ordForm_pullbackRationalPluriForms_congr {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    {g g' : Y ⟶ X} (e : g = g') [IsDominant g] [IsDominant g'] {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sX d m) (P : MMP.Mori.PrimeDivisor Y) :
    P.ordForm (pullbackRationalPluriForms sX g τ) =
      P.ordForm (pullbackRationalPluriForms sX g' τ) := by
  subst e
  rfl

end Forms

/-! ### The canonical divisor of `X⁺` -/

section StepDiagram

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]

/-- **The canonical divisor of `X⁺` is cut out by the same form.** If `K⁻ = div(f⁻^*τ)` for a
rational top form `τ` on `Z`, then `K⁺ = (f⁺)⁻¹_* f⁻_* K⁻ = div(f⁺^*τ)`: every prime divisor
`P` of `X⁺` lies over a prime divisor `Q` of `Z` over which `f⁻` and `f⁺` are isomorphisms. -/
private theorem ordForm_pullbackRationalPluriForms_plus {sZ : Z ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sZ] [IsSeparated (Z ↘ Limits.terminal Scheme)]
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsSeparated fm]
    [IsDominant fm] [IsDominant fp]
    (h : IsThreefoldStepDiagram (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    (τ : RationalPluriForms sZ n 1)
    (hK : ∀ Γ : MMP.Mori.PrimeDivisor Xm,
      Γ.ordForm (pullbackRationalPluriForms sZ fm τ) = K.coeff Γ)
    (P : MMP.Mori.PrimeDivisor Xp) :
    P.ordForm (pullbackRationalPluriForms sZ fp τ) = (flipTransform fm fp K).coeff P := by
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective
  have hfp := h.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨Pm, Q, -, hQm, hQp, hQ, -, -⟩ := h.exists_primeDivisor_valuationOver_eq P
  have hm := map_genericPoint_eq_of_image_eq fm Pm Q hQm
  have hp := map_genericPoint_eq_of_image_eq fp P Q hQp
  haveI := isIso_stalkMap_of_map_eq_genericPoint fm hfm Q hm
  haveI := isIso_stalkMap_of_map_eq_genericPoint fp hfp Q hp
  rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp hfp hd P Q hp τ,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fm hfm hd Pm Q hm τ, hK,
    DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    flipTransform_apply_eq hfm Pm P Q hm hp hQ.2]

end StepDiagram

/-! ### Effective pull-backs -/

section Effective

/-- The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective. -/
private theorem coeff_nonneg_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    (hB0 : 0 ≤ B) (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor X) :
    0 ≤ B'.coeff E := by
  obtain ⟨m, hm, L, hL, hLc⟩ := hBq.exists_pos
  obtain ⟨L', hL'q, hL'⟩ := h m hm L hL hLc
  have hm0 : (0 : ℚ) < m := mod_cast hm
  have hLP : ∀ P : MMP.Mori.PrimeDivisor Y, 0 ≤ L.coeff P := by
    intro P
    have h1 := congrArg (fun G : QDivisor Y => G P) hL
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    change ((L P : ℤ) : ℚ) = m * B P at h1
    have h2 : (0 : ℚ) ≤ ((L P : ℤ) : ℚ) := by rw [h1]; exact mul_nonneg hm0.le (hB0 P)
    exact_mod_cast h2
  have hE : 0 ≤ L'.coeff E :=
    coeff_nonneg_of_isPullback_of_isEffectiveOn hLc (V := ⊤) (fun P _ => hLP P) hL' E
      ((E.genericPoint_mem_iff (f ⁻¹ᵁ ⊤)).mp trivial)
  have h1 := congrArg (fun G : QDivisor X => G E) hL'q
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
  change ((L' E : ℤ) : ℚ) = m * B' E at h1
  have h2 : (0 : ℚ) ≤ m * B' E := by rw [← h1]; exact_mod_cast hE
  exact (mul_nonneg_iff_of_pos_left hm0).mp h2

end Effective

/-! ### The comparison on a model over the graph -/

section Graph

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]
  {sZ : Z ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
  {u : G ⟶ Xm} {v : G ⟶ Xp} {H : QDivisor G}

/-- With `Λ₁ = m₁ H⁻` and `Λ₂ = m₂ H⁺`, the divisor `m₂ Λ₁ - m₁ Λ₂` is `m₁ m₂ (H⁻ - H⁺)`. -/
private theorem toQDivisor_zsmul_add_neg_zsmul {m₁ m₂ : ℕ} {Λ₁ Λ₂ : Divisor G}
    {Hm Hp : QDivisor G} (h₁ : Divisor.toQDivisor Λ₁ = (m₁ : ℤ) • Hm)
    (h₂ : Divisor.toQDivisor Λ₂ = (m₂ : ℤ) • Hp) :
    Divisor.toQDivisor ((m₂ : ℤ) • Λ₁ + (-(m₁ : ℤ)) • Λ₂) = ((m₁ * m₂ : ℕ) : ℤ) • (Hm - Hp) := by
  rw [map_add, map_zsmul, map_zsmul, h₁, h₂, smul_smul, smul_smul, smul_sub]
  push_cast
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2 <;> ring

/-- The graph divisor is `ℚ`-Cartier: with `m^± D^± = L^±` Cartier, `m⁻ m⁺ H` is the Cartier
divisor `m⁺ u^* L⁻ - m⁻ v^* L⁺`. -/
private theorem isQCartier_of_isThreefoldGraphDivisor {sXm : Xm ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H) :
    H.IsQCartier := by
  have hD := h.isThreefoldStepDiagram
  obtain ⟨m₁, hm₁, L₁, hL₁, hL₁c⟩ := hD.isQCartier_minus.exists_pos
  obtain ⟨m₂, hm₂, L₂, hL₂, hL₂c⟩ := hD.isQCartier_plus.exists_pos
  obtain ⟨Hm, Hp, _hm, _hp, hHm, hHp, rfl⟩ := h.exists_pullback
  obtain ⟨Λ₁, hΛ₁q, hΛ₁⟩ := hHm m₁ hm₁ L₁ hL₁ hL₁c
  obtain ⟨Λ₂, hΛ₂q, hΛ₂⟩ := hHp m₂ hm₂ L₂ hL₂ hL₂c
  exact ⟨((m₁ * m₂ : ℕ) : ℤ), by positivity, (m₂ : ℤ) • Λ₁ + (-(m₁ : ℤ)) • Λ₂,
    toQDivisor_zsmul_add_neg_zsmul hΛ₁q hΛ₂q,
    ((hΛ₁.isCartier hL₁c).zsmul _).add ((hΛ₂.isCartier hL₂c).zsmul _)⟩

private theorem sub_sub_eq_of_mul_sub_mul_eq {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    {a b : ℤ} {o c : ℝ} (e : (m₂ : ℝ) * (a : ℝ) - (m₁ : ℝ) * (b : ℝ) = ((m₁ : ℝ) * m₂) * c) :
    (1 + o - (m₂ : ℝ)⁻¹ * (b : ℝ)) - (1 + o - (m₁ : ℝ)⁻¹ * (a : ℝ)) = c := by
  have hm₁0 : (m₁ : ℝ) ≠ 0 := mod_cast hm₁.ne'
  have hm₂0 : (m₂ : ℝ) ≠ 0 := mod_cast hm₂.ne'
  field_simp
  linear_combination e

/-- **The comparison of log discrepancies on a model over the graph.** For a proper divisor
`(W, w, E)` over `G` and the pull-back `H' = w^*H`, the valuation `ord_E` has log discrepancies
`a⁻` over `(X⁻, B⁻)` and `a⁺` over `(X⁺, B⁺)`, and `a⁺ - a⁻ = coeff_E H'`. -/
private theorem exists_isValuationLogDiscrepancy_sub_eq
    (h : IsThreefoldGraphDivisor (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp u v H)
    (D : DivisorOver ℂ (u ≫ fm ≫ sZ)) (hDp : IsProper D.f)
    (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
    (H' : QDivisor D.Y)
    (hH' : haveI := D.isLocallyNoetherian; haveI := D.isNormal; H.IsPullback D.f hH H') :
    haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
    haveI := h.isNormalizedGraph.isBirationalMorphism_plus.isDominant
    ∃ am ap : ℝ,
      IsValuationLogDiscrepancy (fm ≫ sZ) B (D.valuation.comap (functionFieldMap u)) am ∧
      IsValuationLogDiscrepancy (fp ≫ sZ) (flipTransform fm fp B)
        (D.valuation.comap (functionFieldMap v)) ap ∧
      ap - am = (H'.coeff D.E : ℝ) := by
  have hD := h.isThreefoldStepDiagram
  have hG := h.isNormalizedGraph
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hZ.1
  haveI := hD.isNormalVariety_minus.1
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hD.isNormalVariety_minus.1.toLocallyOfFiniteType
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isSmallMorphism_plus.isProper
  haveI : IsFinite (Limits.pullback.lift u v hG.comp_eq) := hG.isFinite
  haveI : IsProper v := by
    rw [← Limits.pullback.lift_snd u v hG.comp_eq]
    infer_instance
  haveI : IsProper u := by
    rw [← Limits.pullback.lift_fst u v hG.comp_eq]
    infer_instance
  haveI := isSeparated_toTerminal sZ
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := hDp
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace v
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  have hfm := hD.isBirationalMorphism_minus.functionFieldMap_bijective
  have hfp := hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective
  -- the dimension `n` and the forms `ω⁻ = f⁻^*τ`, `ω⁺ = f⁺^*τ`
  obtain ⟨n, hK⟩ := hD.isCanonicalDivisor
  obtain ⟨n', hKp⟩ := hD.isCanonicalDivisor_plus
  have hn : topologicalKrullDim Xm = n := hK.topologicalKrullDim_eq
  have hnn' : n' = n := mod_cast hKp.topologicalKrullDim_eq.symm.trans (hD.dim_plus.trans
    (hD.dim_minus.symm.trans hn))
  subst hnn'
  have hnZ : topologicalKrullDim Z = n' :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (fm ≫ sZ)
      hD.isBirationalMorphism_minus).trans hn
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq
    hD.isNormalVariety_minus hK
  obtain ⟨τ, hτ0, hτ⟩ := exists_pullbackRationalPluriForms_eq fm hfm hd ω hω0
  subst hτ
  have hωp0 := pullbackRationalPluriForms_ne_zero fp hfp hd hτ0
  have hωp := ordForm_pullbackRationalPluriForms_plus hD hd τ hω
  -- Cartier presentations of `D⁻`, `D⁺` and their pull-backs
  obtain ⟨m₁, hm₁, L₁, hL₁, hL₁c⟩ := hD.isQCartier_minus.exists_pos
  obtain ⟨m₂, hm₂, L₂, hL₂, hL₂c⟩ := hD.isQCartier_plus.exists_pos
  obtain ⟨Hm, Hp, _hm, _hp, hHm, hHp, rfl⟩ := h.exists_pullback
  obtain ⟨Λ₁, hΛ₁q, hΛ₁⟩ := hHm m₁ hm₁ L₁ hL₁ hL₁c
  obtain ⟨Λ₂, hΛ₂q, hΛ₂⟩ := hHp m₂ hm₂ L₂ hL₂ hL₂c
  have hΛ₁c := hΛ₁.isCartier hL₁c
  have hΛ₂c := hΛ₂.isCartier hL₂c
  obtain ⟨Λ₁', hΛ₁'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hΛ₁c
  obtain ⟨Λ₂', hΛ₂'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hΛ₂c
  -- the two divisors `(W, u w, E)` over `X⁻` and `(W, v w, E)` over `X⁺`
  have hs : v ≫ fp ≫ sZ = u ≫ fm ≫ sZ := by
    rw [← Category.assoc, ← hG.comp_eq, Category.assoc]
  set Dm := compOver u hG.isBirationalMorphism_minus rfl D hDp with hDm
  set Dp := compOver v hG.isBirationalMorphism_plus hs D hDp with hDp'
  haveI : IsDominant (D.f ≫ u) := Dm.isDominant
  haveI : IsDominant (D.f ≫ v) := Dp.isDominant
  have hL₁' : ∃ hC, L₁.IsPullback (D.f ≫ u) hC Λ₁' :=
    ⟨_, isPullback_comp hΛ₁ hΛ₁'
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ u) L₁)⟩
  have hL₂' : ∃ hC, L₂.IsPullback (D.f ≫ v) hC Λ₂' :=
    ⟨_, isPullback_comp hΛ₂ hΛ₂'
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ v) L₂)⟩
  have ham := isLogDiscrepancy_of_isPullback hD.isNormalVariety_minus hK hω0 hω hL₁ hm₁ hL₁c
    Dm (compOver_isProper _ _ _ _ _) hL₁'
  have hap := isLogDiscrepancy_of_isPullback hD.isNormalVariety_plus hKp hωp0
    hωp hL₂ hm₂ hL₂c Dp (compOver_isProper _ _ _ _ _) hL₂'
  refine ⟨_, _, ⟨n', Dm, compOver_isProper _ _ _ _ _, compOver_valuation _ _ _ _ _, ham⟩,
    ⟨n', Dp, compOver_isProper _ _ _ _ _, compOver_valuation _ _ _ _ _, hap⟩, ?_⟩
  -- the orders of the two pulled-back forms agree
  have hord : (Dp.ordPullback (pullbackRationalPluriForms sZ fp τ) : ℤ) =
      Dm.ordPullback (pullbackRationalPluriForms sZ fm τ) := by
    change D.E.ordForm (pullbackRationalPluriForms (fp ≫ sZ) (D.f ≫ v)
        (pullbackRationalPluriForms sZ fp τ)) =
      D.E.ordForm (pullbackRationalPluriForms (fm ≫ sZ) (D.f ≫ u)
        (pullbackRationalPluriForms sZ fm τ))
    rw [MMP.Flips.pullbackRationalPluriForms_comp fp (D.f ≫ v) hfp
        (show IsBirationalMorphism (D.f ≫ v) from
          Dp.isBirationalMorphism).functionFieldMap_bijective hd τ,
      MMP.Flips.pullbackRationalPluriForms_comp fm (D.f ≫ u) hfm
        (show IsBirationalMorphism (D.f ≫ u) from
          Dm.isBirationalMorphism).functionFieldMap_bijective hd τ]
    haveI : IsDominant ((D.f ≫ v) ≫ fp) := inferInstance
    haveI : IsDominant ((D.f ≫ u) ≫ fm) := inferInstance
    exact ordForm_pullbackRationalPluriForms_congr
      (by rw [Category.assoc, Category.assoc, hG.comp_eq]) τ D.E
  -- the coefficient of `E` in `w^*H`
  have hM : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  set C : Divisor G := (m₂ : ℤ) • Λ₁ + (-(m₁ : ℤ)) • Λ₂
  have hCc : C.IsCartier := (hΛ₁c.zsmul _).add (hΛ₂c.zsmul _)
  have hCq : Divisor.toQDivisor C = ((m₁ * m₂ : ℕ) : ℤ) • (Hm - Hp) :=
    toQDivisor_zsmul_add_neg_zsmul hΛ₁q hΛ₂q
  obtain ⟨D', hD'q, hD'⟩ := hH' (m₁ * m₂) hM C hCq hCc
  have hpb : C.IsPullback D.f
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f C)
      ((m₂ : ℤ) • Λ₁' + (-(m₁ : ℤ)) • Λ₂') :=
    Divisor.IsPullback.add (hΛ₁c.zsmul _) (hΛ₂c.zsmul _) _
      (hΛ₁'.zsmul hΛ₁c _
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _))
      (hΛ₂'.zsmul hΛ₂c _
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _))
  have hD'eq := hD'.eq hCc hpb
  have e1 := congrArg (fun G : QDivisor D.Y => G D.E) hD'q
  simp only [Finsupp.smul_apply, zsmul_eq_mul] at e1
  change ((D' D.E : ℤ) : ℚ) = ((m₁ * m₂ : ℕ) : ℤ) * H' D.E at e1
  rw [hD'eq] at e1
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at e1
  have e2 : ((m₂ : ℝ) * (Λ₁' D.E : ℝ) - (m₁ : ℝ) * (Λ₂' D.E : ℝ)) =
      ((m₁ : ℝ) * m₂) * ((H' D.E : ℚ) : ℝ) := by
    have e1' : ((((m₂ : ℤ) * Λ₁' D.E + -(m₁ : ℤ) * Λ₂' D.E : ℤ) : ℚ) : ℝ) =
        ((((m₁ * m₂ : ℕ) : ℤ) * H' D.E : ℚ) : ℝ) := by rw [e1]
    push_cast at e1'
    linear_combination e1'
  change (1 + (Dp.ordPullback (pullbackRationalPluriForms sZ fp τ) : ℝ) -
      (m₂ : ℝ)⁻¹ * ((Λ₂' D.E : ℤ) : ℝ)) -
    (1 + (Dm.ordPullback (pullbackRationalPluriForms sZ fm τ) : ℝ) -
      (m₁ : ℝ)⁻¹ * ((Λ₁' D.E : ℤ) : ℝ)) = ((H' D.E : ℚ) : ℝ)
  rw [hord]
  exact sub_sub_eq_of_mul_sub_mul_eq hm₁ hm₂ e2

end Graph

end MMP.Fourfold.StepDiagram.ProofLemIndexcGraph

namespace MMP.Fourfold

open MMP.Mori
open MMP.Fourfold.StepDiagram.ProofLemIndexcGraph

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]

/-- **Discrepancy comparison for threefold step diagrams.** For a threefold step diagram
`(X⁻, B⁻) → Z ← (X⁺, B⁺)` with normalized graph `(G, u, v)` and graph divisor `H`, and a
valuation `ξ` of `k(G)` whose restriction `ξ ∘ u^*` to `k(X⁻)` is a normalized divisorial
valuation, there is `c = ξ(H) ≥ 0`: `c = coeff_E(w^* H)` for every realization `ξ = ord_E` of
`ξ` on a proper birational `w : W ⟶ G` (and one exists), both log discrepancies
`a(ξ ∘ u^*; X⁻, B⁻)` and `a(ξ ∘ v^*; X⁺, B⁺)` exist, and any two such values satisfy
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = c`. -/
@[mmp "lem_mmp_indexc_graph"]
public theorem IsThreefoldGraphDivisor.exists_sub_eq_coeff_pullback
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H)
    (ξ : Valuation G.functionField (WithZero (Multiplicative ℤ)))
    (hξ : haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sXm (ξ.comap (functionFieldMap u))) :
    haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
    haveI := h.isNormalizedGraph.isBirationalMorphism_plus.isDominant
    ∃ c : ℚ, 0 ≤ c ∧
      (∃ (D : DivisorOver ℂ (u ≫ sXm)), IsProper D.f ∧ D.valuation = ξ ∧
        haveI := D.isLocallyNoetherian
        haveI := D.isNormal
        ∃ (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
          (H' : QDivisor D.Y), H.IsPullback D.f hH H' ∧ H'.coeff D.E = c) ∧
      (∀ D : DivisorOver ℂ (u ≫ sXm), IsProper D.f → D.valuation = ξ →
        haveI := D.isLocallyNoetherian
        haveI := D.isNormal
        ∀ (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
          (H' : QDivisor D.Y), H.IsPullback D.f hH H' → H'.coeff D.E = c) ∧
      (∃ a : ℝ, IsValuationLogDiscrepancy sXm B (ξ.comap (functionFieldMap u)) a) ∧
      (∃ a : ℝ, IsValuationLogDiscrepancy sXp (flipTransform fm fp B)
        (ξ.comap (functionFieldMap v)) a) ∧
      ∀ am ap : ℝ, IsValuationLogDiscrepancy sXm B (ξ.comap (functionFieldMap u)) am →
        IsValuationLogDiscrepancy sXp (flipTransform fm fp B) (ξ.comap (functionFieldMap v)) ap →
          ap - am = c := by
  have hD := h.isThreefoldStepDiagram
  have hG := h.isNormalizedGraph
  obtain rfl := hD.comp_eq_minus
  obtain rfl := hD.comp_eq_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hD.isNormalVariety_minus.1
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isSmallMorphism_plus.isProper
  haveI : IsFinite (Limits.pullback.lift u v hG.comp_eq) := hG.isFinite
  haveI : IsProper u := by
    rw [← Limits.pullback.lift_fst u v hG.comp_eq]
    infer_instance
  haveI : IsProper v := by
    rw [← Limits.pullback.lift_snd u v hG.comp_eq]
    infer_instance
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace v
  have hufm : IsBirationalMorphism (u ≫ fm) :=
    isBirationalMorphism_comp_of_isBirational fm u
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hD.isBirationalMorphism_minus)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_minus)
  haveI := hufm.isDominant
  have hGv : IsNormalVariety ℂ (u ≫ fm ≫ sZ) := ⟨⟨⟩, inferInstance⟩
  -- a proper realization `(W, w, E)` of `ξ` over `G`
  obtain ⟨D₁, -, hD₁v⟩ := hξ
  obtain ⟨D₀, hD₀p, hD₀v⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq hGv fm (u ≫ fm)
    hD.isBirationalMorphism_minus hufm rfl (Category.assoc _ _ _) D₁ ξ (by
      ext t
      simp only [Valuation.comap_apply]
      rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply u fm t, ← hD₁v]
      rfl)
  have hHq := isQCartier_of_isThreefoldGraphDivisor h
  have hH0 := IsThreefoldGraphDivisor.nonneg h
  haveI := D₀.isIntegral
  haveI := D₀.isNormal
  haveI := D₀.isLocallyNoetherian
  haveI := D₀.isDominant
  haveI := hD₀p
  haveI : CompactSpace D₀.Y := QuasiCompact.compactSpace_of_compactSpace D₀.f
  have hH₀ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' D₀.f H
  set H₀ := H.pullback hHq hH₀
  have hH₀p := QDivisor.isPullback_pullback hHq hH₀
  obtain ⟨am₀, ap₀, ham₀, hap₀, hdiff₀⟩ :=
    exists_isValuationLogDiscrepancy_sub_eq h D₀ hD₀p hH₀ H₀ hH₀p
  rw [hD₀v] at ham₀ hap₀
  refine ⟨H₀.coeff D₀.E, coeff_nonneg_of_isPullback hH0 hHq hH₀p D₀.E,
    ⟨D₀, hD₀p, hD₀v, hH₀, H₀, hH₀p, rfl⟩, fun D hDp hDv hH H' hH' => ?_, ⟨am₀, ham₀⟩,
    ⟨ap₀, hap₀⟩, fun am ap ham hap => ?_⟩
  · obtain ⟨am, ap, ham, hap, hdiff⟩ := exists_isValuationLogDiscrepancy_sub_eq h D hDp hH H' hH'
    rw [hDv] at ham hap
    rw [IsValuationLogDiscrepancy.unique ham ham₀, IsValuationLogDiscrepancy.unique hap hap₀,
      hdiff₀] at hdiff
    exact_mod_cast hdiff.symm
  · rw [IsValuationLogDiscrepancy.unique ham ham₀, IsValuationLogDiscrepancy.unique hap hap₀,
      hdiff₀]

end MMP.Fourfold

namespace MMP.Fourfold.StepDiagram.ProofLemIndexcBridgeUpperBound

open MMP.Mori MMP.Fourfold

open MMP.Fourfold.StabilizedTail

section Helpers

variable {X Y : Scheme.{0}}

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- Let `E ⊆ X`, `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `𝒪_{Y,P} ≅ 𝒪_{X,E}`. The
coefficient of `E` in the pull-back of a `ℚ`-Cartier `ℚ`-divisor `B` is the coefficient of `P`
in `B`. -/
private theorem coeff_eq_of_isPullback_qDivisor [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {B : QDivisor Y} (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (hB' : B.IsPullback f hB B') : B' E = B P := by
  have hm := QDivisor.cartierIndex_pos hBq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hBq
  obtain ⟨D', hD', hp⟩ := hB' _ hm D₀ hD₀ hD₀c
  have hc := MMP.Positivity.coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  refine mul_left_cancel₀ (mod_cast hm.ne') (h1.symm.trans (Eq.trans ?_ h2))
  exact congrArg (fun z : ℤ => (z : ℚ)) hc

/-- The transform `φ_* D` vanishes when every component of `D` with a transform has
coefficient zero. -/
private theorem mapPrimeDivisors_eq_zero_of_forall {R : Type*} [AddCommMonoid R]
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    (D : DivisorWithCoeffs R X) (h : ∀ E P, φ E = some P → D E = 0) :
    DivisorWithCoeffs.mapPrimeDivisors φ D = 0 := by
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply]
  refine Finset.sum_eq_zero fun E _ => ?_
  rcases hE : φ E with _ | P
  · simp [hE]
  · simp [h E P hE]

/-- Along a separated birational morphism onto a normal scheme, the transform of a divisor has,
at a prime divisor `Q`, the coefficient of the prime divisor `P` over it. -/
private theorem transformDivisor_apply_of_map_genericPoint [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (Y ↘ Limits.terminal Scheme)]
    {f : X ⟶ Y} [IsSeparated f] (hf : IsBirationalMorphism f) {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Y} (h : f P.genericPoint = Q.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (X := X) f.toRationalMap D Q = D P :=
  have := hf.isDominant
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr h)
    (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      ProofLemIndexcGraph.eq_of_map_eq_genericPoint f hf.functionFieldMap_bijective Q
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E' Q).mp hE') h) D

/-- Pull-backs of rational functions compose along dominant morphisms of integral schemes. -/
private theorem functionFieldMap_comp_apply {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  exact MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b t

/-- Along `a ≫ b = c`, the pull-back of rational functions by `c` is that by `b` followed by
that by `a`. -/
private theorem coe_functionFieldMap_eq_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) :
    ⇑(functionFieldMap c) = ⇑(functionFieldMap a) ∘ ⇑(functionFieldMap b) :=
  funext fun t => (functionFieldMap_comp_apply a b hc t).symm

/-- Valuations with the same pull-back along a surjective ring map are equal. -/
private theorem valuation_eq_of_comap_eq {K L Γ₀ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ₀] {e : K →+* L} (he : Function.Surjective e)
    {v w : Valuation L Γ₀} (h : v.comap e = w.comap e) : v = w := by
  refine Valuation.ext fun x => ?_
  obtain ⟨y, rfl⟩ := he x
  exact congrArg (fun u : Valuation K Γ₀ => u y) h

end Helpers

/-! ### Intersection numbers of pull-backs -/

section Intersection

variable {W V T : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
  [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sW : W ⟶ Spec (.of ℂ)}
  [QuasiCompact sW] {sV : V ⟶ Spec (.of ℂ)} [IsSeparated sV] [LocallyOfFiniteType sV]

/-- The pull-back of a `g`-ample Cartier divisor along `u` has nonnegative degree on every proper
curve contracted by `u ≫ g`. -/
private theorem degreeOn_nonneg_of_isPullback (u : W ⟶ V) (hu : u ≫ sV = sW) [IsProper u]
    {g : V ⟶ T} {L : Divisor V} (hL : L.IsCartier) (hamp : L.IsRelativelyAmple g hL)
    {hB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ L.supp}
    {L' : Divisor W} (hp : L.IsPullback u hB L') (C : ProperCurve sW)
    (hC : C.IsContractedBy (u ≫ g)) :
    0 ≤ L'.degreeOn ℂ sW C.ι C.dim_le (hp.isCartier hL) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := (hp.isCartier hL).isInvertibleModule_divisorialSheaf
  rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ sW C.ι C.dim_le (hp.divisorialSheafIso (hBc := hL))]
  change 0 ≤ C.degree ℂ ((Scheme.Modules.pullback u).obj L.divisorialSheaf)
  rw [C.degree_pullback u hu]
  split_ifs with h
  · refine mul_nonneg (Nat.cast_nonneg _) (le_of_lt ?_)
    refine MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g _ hamp
      (⟨u C.point, h⟩ : ProperCurve sV) fun y hy => ?_
    have hcl : IsClosed (u '' closure {C.point}) := u.isClosedMap _ isClosed_closure
    have hsub : ({u C.point} : Set V) ⊆ u '' closure {C.point} :=
      Set.singleton_subset_iff.mpr ⟨C.point, subset_closure rfl, rfl⟩
    obtain ⟨x, hx, rfl⟩ := closure_minimal hsub hcl hy
    simpa only [Scheme.Hom.comp_apply] using hC x hx
  · exact le_rfl

/-- The pull-back of a `ℚ`-divisor with a `g`-ample multiple along `u` has nonnegative
intersection number with every proper curve contracted by `u ≫ g`. -/
private theorem intersectionNumber_nonneg_of_isPullback (u : W ⟶ V) (hu : u ≫ sV = sW)
    [IsProper u] {g : V ⟶ T} {D : QDivisor V} (hD : D.HasRelativelyAmpleMultiple g)
    {hB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ D.supp}
    {P : QDivisor W} (hp : D.IsPullback u hB P) (hPq : P.IsQCartier) (C : ProperCurve sW)
    (hC : C.IsContractedBy (u ≫ g)) :
    0 ≤ P.intersectionNumber ℂ sW C.ι C.dim_le hPq := by
  obtain ⟨m, hm, L, hL, hLq, hamp⟩ := hD
  obtain ⟨L', hL'q, hp'⟩ := hp m hm L hLq hL
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sW C.ι C.dim_le P hPq hm L' (hp'.isCartier hL)
    hL'q]
  exact div_nonneg (mod_cast degreeOn_nonneg_of_isPullback u hu hL hamp hp' C hC)
    (Nat.cast_nonneg _)

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor has intersection number zero with a curve
contracted by the morphism. -/
private theorem intersectionNumber_isPullback_eq_zero (u : W ⟶ V) (hu : u ≫ sV = sW)
    [QuasiCompact sV] {L : QDivisor V} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ L.supp}
    {L' : QDivisor W} (h : L.IsPullback u hB L') (Γ : ProperCurve sW) (hΓ : Γ.IsContractedBy u) :
    L'.intersectionNumber ℂ sW Γ.ι Γ.dim_le (h.isQCartier hL) = 0 := by
  obtain ⟨D, D', hDc, hDB, -, hD', hp⟩ := h.exists_cartierIndex hL
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sW Γ.ι _ _ _ (QDivisor.cartierIndex_pos hL) D'
    (hp.isCartier hDc) hD']
  obtain rfl := hp.eq hDc (Divisor.isPullback_pullback hDc hDB)
  rw [Divisor.degreeOn_pullback_eq_zero_of_isContractedBy u hu hDc hDB Γ hΓ]
  simp

end Intersection

/-! ### The log discrepancy read on a model -/

/-- **The log discrepancy on a model with compatible canonical divisors.** Let `(X, B)` be a
normal variety with canonical divisor `K` and `K + B` `ℚ`-Cartier, `r : W ⟶ X` a proper
birational morphism from a normal variety with canonical divisor `K_W`, `r_* K_W = K`, and
`R = r^*(K + B)`. If a divisor over `X` with log discrepancy `a` has the valuation of a prime
divisor `P` of `W`, then `coeff_P R = coeff_P K_W + 1 - a`, that is,
`a = 1 + coeff_P (K_W - r^*(K + B))`. -/
private theorem coeff_isPullback_eq_of_isLogDiscrepancy {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {d : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX d)
    {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier) {r : W ⟶ X} [IsProper r]
    (hr : IsBirationalMorphism r) (hW : IsNormalVariety ℂ (r ≫ sX))
    [LocallyOfFiniteType (r ≫ sX)] {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (r ≫ sX) d)
    (hKX : RationalMap.transformDivisor (X := W) r.toRationalMap KW = K)
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + B).supp}
    {R : QDivisor W} (hR : (Divisor.toQDivisor K + B).IsPullback r hR₀ R)
    (P : MMP.Mori.PrimeDivisor W) {n : ℕ} {D : DivisorOver ℂ sX} {a : ℝ}
    (hD : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a)
    (hv : D.valuation = (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX).valuation) :
    (R P : ℝ) = (KW P : ℝ) + 1 - a := by
  haveI := hr.isDominant
  obtain ⟨ω, hω0, hωK, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hW hr hK hKW hKX
  obtain ⟨m, hm, L, hL, hLc⟩ := hKB.exists_pos
  obtain ⟨L', hL'q, hLp⟩ := hR m hm L hL hLc
  have hmR : (m : ℝ) ≠ 0 := mod_cast hm.ne'
  have hlog : MMP.Intersection.IsLogDiscrepancy sX d (QDivisor.toRDivisor B)
      (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) (1 + KW P - R P) := by
    refine ⟨hX, inferInstance, ω, hω0, ⟨K, hK, fun Γ => by rw [← hωK]; rfl⟩, 1,
      fun _ => ((m : ℝ)⁻¹), fun _ => L, fun _ => L', fun _ => hLc, fun Γ => ?_,
      fun _ => ⟨_, hLp⟩, ?_⟩
    · have h1 := congrArg (fun G : QDivisor X => G Γ) hL
      have h2 : Γ.ordForm ω = K Γ := by rw [← hωK]; rfl
      simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast, Finsupp.add_apply] at h1
      change ((L Γ : ℤ) : ℚ) = m * (((K Γ : ℤ) : ℚ) + B Γ) at h1
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
        QDivisor.coeff_toRDivisor, h2]
      change (((K Γ : ℤ) : ℝ)) + ((B Γ : ℚ) : ℝ) = (m : ℝ)⁻¹ * ((L Γ : ℤ) : ℝ)
      have h3 : ((L Γ : ℤ) : ℝ) = (m : ℝ) * (((K Γ : ℤ) : ℝ) + ((B Γ : ℚ) : ℝ)) := by
        exact_mod_cast h1
      rw [h3]
      field_simp
    · have h1 := congrArg (fun G : QDivisor W => G P) hL'q
      simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
      change ((L' P : ℤ) : ℚ) = m * R P at h1
      have h2 : DivisorOver.ordPullback (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) ω = KW P := by
        rw [← hωW]; rfl
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, h2]
      change 1 + ((KW P : ℤ) : ℝ) - ((R P : ℚ) : ℝ) =
        1 + ((KW P : ℤ) : ℝ) - (m : ℝ)⁻¹ * ((L' P : ℤ) : ℝ)
      have h3 : ((L' P : ℤ) : ℝ) = (m : ℝ) * ((R P : ℚ) : ℝ) := mod_cast h1
      rw [h3]
      field_simp
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hlog hv
  linarith

/-- The `ℚ`-Cartier property passes from `D` to `-D`. -/
private theorem isQCartier_neg {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m, hm, by rw [smul_neg]; exact h.neg⟩

/-- If `P = u^* D`, then `-P = u^*(-D)`. -/
private theorem isPullback_neg {W V : Scheme.{0}} [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian V] [IsNormal V] {u : W ⟶ V} {D : QDivisor V}
    {hB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ D.supp}
    {P : QDivisor W} (hp : D.IsPullback u hB P)
    (hB' : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉ (-D).supp) :
    (-D).IsPullback u hB' (-P) := by
  intro m hm L hLq hL
  have hq : Divisor.toQDivisor ((-1 : ℤ) • L) = (m : ℤ) • D := by
    rw [map_zsmul, hLq, smul_smul, smul_neg]
    simp
  obtain ⟨L', hL'q, hp'⟩ := hp m hm _ hq (hL.zsmul _)
  have hm' : (m : ℤ) ≠ 0 := mod_cast hm.ne'
  have hsupp : ∀ Z : irreducibleComponents W,
      u (componentGenericPoint W Z) ∉ ((-1 : ℤ) • ((-1 : ℤ) • L)).supp := fun Z hZ => hB Z (by
    rwa [← Divisor.supp_toQDivisor, map_zsmul, hq, QDivisor.supp_zsmul (by norm_num),
      QDivisor.supp_zsmul hm'] at hZ)
  refine ⟨(-1 : ℤ) • L', by rw [map_zsmul, hL'q, smul_smul, smul_neg]; simp, ?_⟩
  exact (hp'.zsmul (hL.zsmul _) (-1) hsupp).of_eq (by rw [smul_smul]; simp)

/-- **`-E` is relatively nef.** Let `q : W ⟶ Y`, `r : W ⟶ V` be proper morphisms with
`q ≫ h = r ≫ g`, `D_Y` a `ℚ`-Cartier `ℚ`-divisor on `Y` and `D_V` a `ℚ`-divisor on `V` with a
`g`-ample multiple. Then `r^* D_V - q^* D_Y` is `q`-nef: on a curve contracted by `q`, `q^* D_Y`
has degree zero, and `r^* D_V` has nonnegative degree, the curve being contracted by `r ≫ g`. -/
private theorem isRelativelyNef_neg_sub_of_isPullback {W V Y T : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sW : W ⟶ Spec (.of ℂ)}
    [QuasiCompact sW] {sV : V ⟶ Spec (.of ℂ)} [IsSeparated sV] [LocallyOfFiniteType sV]
    {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    {q : W ⟶ Y} [IsDominant q] (hq : q ≫ sY = sW) {r : W ⟶ V} [IsProper r] (hr : r ≫ sV = sW)
    {h : Y ⟶ T} {g : V ⟶ T} (hcomp : q ≫ h = r ≫ g) {DY : QDivisor Y} (hDY : DY.IsQCartier)
    {DV : QDivisor V} (hDV : DV.IsQCartier) (hamp : DV.HasRelativelyAmpleMultiple g)
    {hA₀ : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ DY.supp}
    {hR₀ : ∀ Z : irreducibleComponents W, r (componentGenericPoint W Z) ∉ DV.supp}
    {A R : QDivisor W} (hA : DY.IsPullback q hA₀ A) (hR : DV.IsPullback r hR₀ R) :
    (-(A - R)).IsRelativelyNef sW q := by
  have hRq := hR.isQCartier hDV
  have hnAq := isQCartier_neg (hA.isQCartier hDY)
  rw [show -(A - R) = R + -A by abel]
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW (hRq.add hnAq) fun C hC => ?_
  rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hRq hnAq]
  refine add_nonneg (intersectionNumber_nonneg_of_isPullback r hr hamp hR hRq C fun x hx => ?_)
    (intersectionNumber_isPullback_eq_zero q hq (isQCartier_neg hDY) (isPullback_neg hA
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _)) C hC).ge
  rw [← hcomp]
  simp only [Scheme.Hom.comp_apply, hC x hx]

/-! ### Valuations, birational morphisms and divisors over a variety -/

section Birational

/-- The valuation `v_E` along a composite `a ≫ b` is `v_E` along `a`, restricted along `b`. -/
private theorem valuationOver_comp {A B C : Scheme.{0}} [IsIntegral A] [IsLocallyNoetherian A]
    [IsNormal A] [IsIntegral B] [IsIntegral C] (E : MMP.Mori.PrimeDivisor A) (a : A ⟶ B)
    (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C} [IsDominant c] (hc : a ≫ b = c) :
    E.valuationOver c = (E.valuationOver a).comap (functionFieldMap b) := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply, PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
    functionFieldMap_comp_apply a b hc]

/-- A dominant morphism of integral schemes inducing an isomorphism of function fields is
birational in the sense of [Stacks, Tag 01RO]. -/
private theorem isBirational_of_bijective {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] (hbij : Function.Bijective (functionFieldMap f)) :
    IsBirational f := by
  have hη : f (genericPoint X) = genericPoint Z := map_genericPoint_of_isDominant f
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hη]
    exact Set.bijOn_singleton.mpr rfl
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    have : IsIso ((Z.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
        f.stalkMap (genericPoint X)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    exact IsIso.of_isIso_comp_left (Z.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom _

/-- A proper dominant morphism of integral schemes onto a normal locally Noetherian scheme,
inducing an isomorphism of function fields, is a birational morphism. -/
private theorem isBirationalMorphism_of_bijective {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] [IsNormal X] [IsNormal Z] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (f : X ⟶ Z) [IsProper f] [IsDominant f] (hbij : Function.Bijective (functionFieldMap f)) :
    IsBirationalMorphism f := by
  have h := isBirationalMorphism_comp_of_isBirational f (𝟙 X) (isBirational_of_bijective f hbij)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      (isBirationalMorphism_of_isIso (𝟙 X)))
  rwa [Category.id_comp] at h

/-- The valuation `ord_E` of a divisor `(W, g, E)` over `X` is a divisor of `k(X)`. -/
private theorem isDivisorOfFunctionField_valuation {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] (D : MMP.Mori.DivisorOver ℂ sX) :
    MMP.Flips.IsDivisorOfFunctionField ℂ sX D.valuation := by
  have := D.isIntegral
  have := D.isDominant
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra D.f
  have := MMP.Mori.isScalarTower_functionFieldMap sX D.f
  exact ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom ℂ X.functionField D.Y.functionField)
    D.isBirationalMorphism.functionFieldMap_bijective, rfl⟩

/-- The divisor `(X, 𝟙, P)` over `X` has valuation `ord_P`. -/
private theorem valuation_ofPrimeDivisor {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor ℂ hX P).valuation = P.divisorialValuation := by
  ext g
  change P.divisorialValuation (functionFieldMap (𝟙 X) g) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

end Birational

/-! ### Rational top forms and canonical divisors -/

section Forms

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [CompactSpace Y]

/-- Along a proper birational morphism `f : Y ⟶ X` of normal varieties of dimension `n`, the
push-forward of `div_Y(f^*ω)` is `div_X(ω)`. -/
private theorem transformDivisor_divisorOfForm_pullback (hX : IsNormalVariety ℂ sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety ℂ (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} (hn : topologicalKrullDim X = n)
    (ω : RationalPluriForms sX n 1) :
    RationalMap.transformDivisor (X := Y) f.toRationalMap
      (divisorOfForm (pullbackRationalPluriForms sX f ω)) = divisorOfForm ω := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
  rw [htr]
  change E.ordForm _ = P.ordForm ω
  rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq ω]

/-- For a proper birational morphism `f : Y → X` of normal varieties of dimension `n` and a
canonical divisor `K_Y` of `Y`, there is a nonzero rational top form `ω` on `X` with
`div_X(ω) = f_* K_Y`. -/
private theorem exists_divisorOfForm_eq_transformDivisor (hX : IsNormalVariety ℂ sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety ℂ (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} (hn : topologicalKrullDim X = n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      divisorOfForm ω = RationalMap.transformDivisor (X := Y) f.toRationalMap KY := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω₁, hω₁0, hω₁⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY hKY
  obtain ⟨τ, hτ0, hpull⟩ :=
    ProofLemIndexcGraph.exists_pullbackRationalPluriForms_eq f hbij hd ω₁ hω₁0
  have hdiv : divisorOfForm (pullbackRationalPluriForms sX f τ) = KY :=
    Finsupp.ext fun Γ => by
      change Γ.ordForm _ = KY.coeff Γ
      rw [hpull, hω₁]
  refine ⟨τ, hτ0, ?_⟩
  rw [← hdiv, transformDivisor_divisorOfForm_pullback hX hY hf hn]

/-- On a normal variety with a canonical divisor, the divisor of a nonzero rational top form is
a canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm (hX : IsNormalVariety ℂ sX) {d : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX d) {τ : RationalPluriForms sX d 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX d :=
  hK.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ)

end Forms

/-! ### Log discrepancies of valuations -/

section LogDiscrepancy

/-- The log discrepancy of a prime divisor `P` of a normal variety `X`, regarded as a divisor
over `X` on the identity model, with respect to a pair `(X, B)` is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : MMP.Mori.Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : MMP.Mori.QDivisor X}
    (hKB : (MMP.Mori.Divisor.toQDivisor K + B).IsQCartier) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (DivisorOver.ofPrimeDivisor ℂ hX P) (1 - (B.coeff P : ℝ)) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, hm, M, hM, hMc⟩ := hKB.exists_pos
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) hMc
  have hm0 : (m : ℝ) ≠ 0 := mod_cast hm.ne'
  have hMΓ : ∀ Γ, (M.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
    have h' : (M.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
      simp at this
      linear_combination this
    exact_mod_cast h'
  have hM'P : M'.coeff P = M.coeff P :=
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl hMc hM'
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, 1,
    fun _ => 1 / (m : ℝ), fun _ => M, fun _ => M', fun _ => hMc, fun Γ => ?_,
    fun _ => ⟨_, hM'⟩, ?_⟩
  · rw [QDivisor.coeff_toRDivisor, Fin.sum_univ_one, hMΓ, hω Γ]
    field_simp
  · rw [Fin.sum_univ_one, DivisorOver.ordPullback_ofPrimeDivisor hX hn P ω]
    change 1 - (B.coeff P : ℝ) = 1 + (P.ordForm ω : ℝ) - 1 / (m : ℝ) * (M'.coeff P : ℝ)
    rw [hM'P, hMΓ, hω P]
    field_simp
    ring

/-- The log discrepancy `a(ord_P; X, B)` of a prime divisor `P` of a normal variety with a
canonical divisor `K` and `K + B` `ℚ`-Cartier is `1 - coeff_P B`. -/
private theorem isValuationLogDiscrepancy_divisorialValuation {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : MMP.Mori.Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : MMP.Mori.QDivisor X}
    (hKB : (MMP.Mori.Divisor.toQDivisor K + B).IsQCartier) (P : MMP.Mori.PrimeDivisor X) :
    IsValuationLogDiscrepancy sX B P.divisorialValuation (1 - (B.coeff P : ℝ)) :=
  ⟨n, DivisorOver.ofPrimeDivisor ℂ hX P, (inferInstance : IsProper (𝟙 X)),
    valuation_ofPrimeDivisor hX P, isLogDiscrepancy_ofPrimeDivisor hX hK hKB P⟩

end LogDiscrepancy

/-! ### The comparison of log discrepancies -/

section Comparison

/-- A valuation of `k(X)` with a log discrepancy over `(X, B)` restricts, along a proper
birational morphism `f : X ⟶ Z` to a normal variety, to a divisor of `k(Z)` with nonempty centre
on `Z`: the divisor `(Y, g, E)` over `X` carrying it is the divisor `(Y, g ≫ f, E)` over `Z`. -/
private theorem hasNonemptyCenter_comap_of_isValuationLogDiscrepancy {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z} [IsProper f]
    (hf : f ≫ sZ = sX) (hfb : IsBirationalMorphism f) {B : QDivisor X}
    {ξ' : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a' : ℝ}
    (ha' : IsValuationLogDiscrepancy sX B ξ' a') :
    haveI := hfb.isDominant
    MMP.Flips.HasNonemptyCenter ℂ sZ (ξ'.comap (functionFieldMap f)) := by
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨n', D', hD'p, hD'v, -⟩ := ha'
  haveI := D'.isIntegral
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  haveI := D'.isDominant
  haveI := hD'p
  have hb : IsBirationalMorphism (D'.f ≫ f) :=
    isBirationalMorphism_comp_of_isBirational f D'.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D'.isBirationalMorphism)
  let DZ : MMP.Flips.ProperDivisorOver ℂ sZ :=
    ⟨⟨D'.Y, D'.f ≫ f, by rw [Category.assoc, hf]; exact D'.isNormalVariety, hb, D'.E⟩,
      inferInstance⟩
  have hDZ : DZ.valuation = ξ'.comap (functionFieldMap f) := by
    rw [← hD'v]
    exact valuationOver_comp D'.E D'.f f rfl
  exact ⟨hDZ ▸ isDivisorOfFunctionField_valuation DZ.toDivisorOver, DZ, hDZ⟩

/-- **Log discrepancies below an ample model.** Let `π : V ⟶ Z` and `f : X ⟶ Z` be proper
birational morphisms of normal complex varieties, `V` `ℚ`-factorial with canonical divisor `K_V`
and boundary `Θ`, and `X` with canonical divisor `K_X` and boundary `B` such that `K_X + B` is
`ℚ`-Cartier with an `f`-ample multiple. Suppose that for every prime divisor `Q` of `V` the
valuation of `k(X)` corresponding to `ord_Q` has log discrepancy `1 - coeff_Q Θ` over `(X, B)`.
Then `a(ξ; V, Θ) ≤ a(ξ'; X, B)` whenever `ξ` and `ξ'` have the same restriction to `k(Z)`.

On a smooth common model `W` (`q : W ⟶ V`, `r : W ⟶ X`) on which `ξ` is a prime divisor,
`G = q^*(K_V + Θ) - r^*(K_X + B)` has `q_* G = 0` by the hypothesis on prime divisors and `-G`
is `q`-nef as `K_X + B` is `f`-ample; the negativity lemma gives `G ≥ 0`, and the coefficient of
`G` at the divisor carrying `ξ` is `a(ξ'; X, B) - a(ξ; V, Θ)`. -/
private theorem le_of_comap_eq_of_forall_primeDivisor {V X Z : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] {sV : V ⟶ Spec (.of ℂ)}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ)
    (hV : IsNormalVariety ℂ sV) (hVQ : IsQFactorial sV) (hX : IsNormalVariety ℂ sX)
    {π : V ⟶ Z} [IsProper π] (hπ : π ≫ sZ = sV) (hπb : IsBirationalMorphism π)
    {f : X ⟶ Z} [IsProper f] (hf : f ≫ sZ = sX) (hfb : IsBirationalMorphism f)
    {n : ℕ} {KV : Divisor V} (hKV : KV.IsCanonicalDivisor sV n) (Θ : QDivisor V)
    {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n) {B : QDivisor X}
    (hXQ : (Divisor.toQDivisor KX + B).IsQCartier)
    (hamp : (Divisor.toQDivisor KX + B).HasRelativelyAmpleMultiple f)
    (hprime : ∀ Q : MMP.Mori.PrimeDivisor V,
      haveI := hπb.isDominant
      haveI := hfb.isDominant
      ∃ s : Valuation X.functionField (WithZero (Multiplicative ℤ)),
        s.comap (functionFieldMap f) = Q.valuationOver π ∧
          IsValuationLogDiscrepancy sX B s (1 - (Θ.coeff Q : ℝ)))
    (ξ : Valuation V.functionField (WithZero (Multiplicative ℤ)))
    (ξ' : Valuation X.functionField (WithZero (Multiplicative ℤ)))
    (hcomap : haveI := hπb.isDominant
      haveI := hfb.isDominant
      ξ.comap (functionFieldMap π) = ξ'.comap (functionFieldMap f))
    {a a' : ℝ} (ha : IsValuationLogDiscrepancy sV Θ ξ a)
    (ha' : IsValuationLogDiscrepancy sX B ξ' a') : a ≤ a' := by
  haveI := hπb.isDominant
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsSeparated sV := hV.1.toIsSeparated
  haveI : QuasiCompact sV := hV.1.toQuasiCompact
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hcenter := hasNonemptyCenter_comap_of_isValuationLogDiscrepancy hZ hf hfb ha'
  -- a smooth common model `W` on which `ξ` is a prime divisor
  let F : ∀ b : Bool, cond b V X ⟶ Z := fun b => Bool.rec (motive := fun b => cond b V X ⟶ Z) f π b
  haveI hFp : ∀ b, IsProper (F b) := fun b => by
    cases b
    · exact (inferInstance : IsProper f)
    · exact (inferInstance : IsProper π)
  obtain ⟨W, w, hW, hwb, g, hWs, -, hg, hE, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sZ F
      (fun b => by cases b; exacts [hfb, hπb])
      (fun b => by
        cases b
        · change IsNormalVariety ℂ (f ≫ sZ)
          rwa [hf]
        · change IsNormalVariety ℂ (π ≫ sZ)
          rwa [hπ])
      (fun _ : Unit => ξ'.comap (functionFieldMap f)) (fun _ => hcenter)
  obtain ⟨q, hqπ, hqproj, hqb⟩ : ∃ q : W ⟶ V,
      q ≫ π = w ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism q := ⟨g true, hg true⟩
  obtain ⟨r, hrf, hrproj, hrb⟩ : ∃ r : W ⟶ X,
      r ≫ f = w ∧ IsProjectiveMorphism r ∧ IsBirationalMorphism r := ⟨g false, hg false⟩
  obtain ⟨E, hEv⟩ := hE ()
  clear hg hE g F hFp
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hW.1.toLocallyOfFiniteType
  haveI : QuasiCompact (w ≫ sZ) := hW.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqproj
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hrproj
  haveI := hqb.isDominant
  haveI := hrb.isDominant
  haveI := hwb.isDominant
  haveI := hX.1
  have hqs : q ≫ sV = w ≫ sZ := by rw [← hqπ, Category.assoc, hπ]
  have hrs : r ≫ sX = w ≫ sZ := by rw [← hrf, Category.assoc, hf]
  have hWq : IsNormalVariety ℂ (q ≫ sV) := hqs ▸ hW
  have hWr : IsNormalVariety ℂ (r ≫ sX) := hrs ▸ hW
  haveI : LocallyOfFiniteType (q ≫ sV) := hWq.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (r ≫ sX) := hWr.1.toLocallyOfFiniteType
  haveI := hWr.1
  -- `ξ` and `ξ'` are the valuation of `E` through `q` and `r`
  have hEw : E.valuationOver w = ξ'.comap (functionFieldMap f) := hEv
  have hEq : E.valuationOver q = ξ :=
    valuation_eq_of_comap_eq hπb.functionFieldMap_bijective.2
      (((valuationOver_comp E q π hqπ).symm.trans hEw).trans hcomap.symm)
  have hEr : E.valuationOver r = ξ' :=
    valuation_eq_of_comap_eq hfb.functionFieldMap_bijective.2
      ((valuationOver_comp E r f hrf).symm.trans hEw)
  -- compatible canonical divisors: `K_W = div(r^* ω)` with `div ω = K_X`, `K_V' = q_* K_W`
  have hdimW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (r ≫ sX) hrb).symm.trans
      hKX.topologicalKrullDim_eq
  obtain ⟨ωX, hωX0, hωX⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hKX
  have hdivX : divisorOfForm ωX = KX := Finsupp.ext hωX
  have hKW : (divisorOfForm (pullbackRationalPluriForms sX r ωX)).IsCanonicalDivisor
      (r ≫ sX) n := by
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (r ≫ sX)
      (hrs ▸ hWs) hdimW
    exact isCanonicalDivisor_divisorOfForm hWr hK₀
      (ProofLemIndexcGraph.pullbackRationalPluriForms_ne_zero r hrb.functionFieldMap_bijective
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
          hKX.topologicalKrullDim_eq) hωX0)
  set KW := divisorOfForm (pullbackRationalPluriForms sX r ωX) with hKW_def
  have hKWX : RationalMap.transformDivisor (X := W) r.toRationalMap KW = KX :=
    (transformDivisor_divisorOfForm_pullback hX hWr hrb hKX.topologicalKrullDim_eq ωX).trans
      hdivX
  have hKWq : KW.IsCanonicalDivisor (q ≫ sV) n := by rwa [hqs, ← hrs]
  obtain ⟨ωV, hωV0, hωV⟩ :=
    exists_divisorOfForm_eq_transformDivisor hV hWq hqb hKV.topologicalKrullDim_eq hKWq
  set KV' : Divisor V := RationalMap.transformDivisor (X := W) q.toRationalMap KW with hKV'_def
  have hKV' : KV'.IsCanonicalDivisor sV n := hωV ▸ isCanonicalDivisor_divisorOfForm hV hKV hωV0
  -- the pull-backs `A = q^*(K_V' + Θ)` and `R = r^*(K_X + B)`
  have hVQ' : (Divisor.toQDivisor KV' + Θ).IsQCartier := isQCartier_of_isQFactorial sV hVQ _
  have hA₀ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q
    (Divisor.toQDivisor KV' + Θ)
  have hR₀ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' r
    (Divisor.toQDivisor KX + B)
  have hA := QDivisor.isPullback_pullback hVQ' hA₀
  have hR := QDivisor.isPullback_pullback hXQ hR₀
  set A := (Divisor.toQDivisor KV' + Θ).pullback hVQ' hA₀
  set R := (Divisor.toQDivisor KX + B).pullback hXQ hR₀
  -- `q_* (A - R) = 0`
  have hpush : RationalMap.transformDivisor (X := W) q.toRationalMap (A - R) = 0 := by
    haveI := hV.1
    haveI := ProofLemIndexcGraph.isSeparated_toTerminal sV
    rw [RationalMap.transformDivisor]
    refine mapPrimeDivisors_eq_zero_of_forall _ fun PW Q hPQ => ?_
    have hPQ' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q PW Q).mp hPQ
    haveI := ProofLemIndexcGraph.isIso_stalkMap_of_map_eq_genericPoint q
      hqb.functionFieldMap_bijective Q hPQ'
    rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor PW Q hPQ' hVQ' hA]
    change ((KV' Q : ℤ) : ℚ) + Θ Q - R PW = 0
    rw [hKV'_def, transformDivisor_apply_of_map_genericPoint hqb hPQ' KW, sub_eq_zero]
    obtain ⟨s, hs, n₂, D₂, -, hD₂v, hD₂log⟩ := hprime Q
    have hsr : s = PW.valuationOver r := by
      refine valuation_eq_of_comap_eq hfb.functionFieldMap_bijective.2 ?_
      rw [hs, ← valuationOver_comp PW r f hrf, valuationOver_comp PW q π hqπ,
        valuationOver_eq_of_isIso q PW Q hPQ']
      rfl
    have h := coeff_isPullback_eq_of_isLogDiscrepancy hX hKX hXQ hrb hWr hKW hKWX hR PW
      hD₂log (hD₂v.trans hsr)
    exact_mod_cast (show ((((KW PW : ℤ) : ℚ) + Θ Q : ℚ) : ℝ) = ((R PW : ℚ) : ℝ) by
      push_cast
      rw [h, DivisorWithCoeffs.coeff_apply]
      ring)
  -- `-(A - R)` is `q`-nef
  have hnef := isRelativelyNef_neg_sub_of_isPullback hqs hrs (hqπ.trans hrf.symm) hVQ' hXQ hamp
    hA hR
  -- the negativity lemma
  have hEff := QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ sV
    (w ≫ sZ) hV hW q hqs hqb
    (by rw [sub_eq_add_neg]; exact (hA.isQCartier hVQ').add (isQCartier_neg (hR.isQCartier hXQ)))
    hnef ((congrArg (·.IsEffective) hpush).mpr DivisorWithCoeffs.isEffective_zero)
  have hE0 : (0 : ℚ) ≤ (A - R) E := DivisorWithCoeffs.isEffective_iff_nonneg.mp hEff E
  rw [Finsupp.sub_apply] at hE0
  -- the coefficients at `E`
  obtain ⟨n₁, D, -, hDv, hDlog⟩ := ha
  obtain ⟨n₂, D', -, hD'v, hD'log⟩ := ha'
  have hAE := coeff_isPullback_eq_of_isLogDiscrepancy hV hKV' hVQ' hqb hWq hKWq rfl hA E hDlog
    (hDv.trans hEq.symm)
  have hRE := coeff_isPullback_eq_of_isLogDiscrepancy hX hKX hXQ hrb hWr hKW hKWX hR E hD'log
    (hD'v.trans hEr.symm)
  have : ((R E : ℚ) : ℝ) ≤ ((A E : ℚ) : ℝ) := mod_cast sub_nonneg.mp hE0
  linarith

end Comparison

/-! ### Steps over a base -/

section Step

variable {Xm Xp Tk Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsIntegral Z] {sXm : Xm ⟶ Spec (.of ℂ)} {sT : Tk ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {g : Xm ⟶ Tk} {gp : Xp ⟶ Tk}

/-- Let `X⁻ → T ← X⁺` be a threefold step diagram over `Z` by `h : T ⟶ Z`. If `π⁻ = h ∘ g` is
dominant and induces an isomorphism of function fields, so does `π⁺ = h ∘ g⁺`. -/
private theorem isDominant_and_bijective_of_isThreefoldStepDiagram
    (hs : IsThreefoldStepDiagram sXm sT sXp K B g gp) (h : Tk ⟶ Z) {πm : Xm ⟶ Z}
    {πp : Xp ⟶ Z} (hm : g ≫ h = πm) (hp : gp ≫ h = πp) [IsDominant πm]
    (hb : Function.Bijective (functionFieldMap πm)) :
    ∃ _ : IsDominant πp, Function.Bijective (functionFieldMap πp) := by
  haveI := hs.isNormalVariety_target.1.toIsIntegral
  haveI := hs.isBirationalMorphism_minus.isDominant
  haveI := hs.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI : IsDominant (g ≫ h) := by rw [hm]; infer_instance
  haveI : IsDominant h := IsDominant.of_comp g h
  rw [coe_functionFieldMap_eq_comp g h hm] at hb
  have hbh := (Function.Bijective.of_comp_iff'
    hs.isBirationalMorphism_minus.functionFieldMap_bijective _).mp hb
  haveI : IsDominant πp := by rw [← hp]; infer_instance
  refine ⟨inferInstance, ?_⟩
  rw [coe_functionFieldMap_eq_comp gp h hp]
  exact hs.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.comp hbh

/-- Let `(X⁻, B) → T ← X⁺` be a threefold step diagram over `Z` by `h : T ⟶ Z`, with
`π^± = h ∘ g^±` dominant. Every prime divisor `Q` of `X⁺` has the valuation over `Z` of a prime
divisor `P⁻` of `X⁻`, and `coeff_Q B⁺ = coeff_{P⁻} B`. -/
private theorem exists_primeDivisor_valuationOver_eq_of_isThreefoldStepDiagram
    (hs : IsThreefoldStepDiagram sXm sT sXp K B g gp) (h : Tk ⟶ Z) {πm : Xm ⟶ Z}
    {πp : Xp ⟶ Z} [IsDominant πm] [IsDominant πp] (hm : g ≫ h = πm) (hp : gp ≫ h = πp)
    (Q : MMP.Mori.PrimeDivisor Xp) :
    ∃ Pm : MMP.Mori.PrimeDivisor Xm, Pm.valuationOver πm = Q.valuationOver πp ∧
      (flipTransform g gp B).coeff Q = B.coeff Pm := by
  haveI := hs.isNormalVariety_target.1.toIsIntegral
  haveI := hs.isBirationalMorphism_minus.isDominant
  haveI := hs.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI : IsDominant (g ≫ h) := by rw [hm]; infer_instance
  haveI : IsDominant h := IsDominant.of_comp g h
  obtain ⟨Pm, -, hv, -, -, -, hc, -⟩ := hs.exists_primeDivisor_valuationOver_eq Q
  refine ⟨Pm, ?_, hc⟩
  rw [valuationOver_comp Pm g h hm, valuationOver_comp Q gp h hp, hv]

end Step

/-! ### The models of a finite relative programme -/

section Program

variable {T : StabilizedTail} {i : ℕ}
  {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y} {K : Divisor J.Y}
  (P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ')

/-- Every model `V_k`, `k ≤ m`, of a finite relative programme is a normal projective threefold
with canonical divisor `K_k`, and `π_k : V_k ⟶ Z` is a morphism over `ℂ`. -/
private theorem model_facts {k : ℕ} (hk : k ≤ P.m) :
    IsNormalVariety ℂ (modelStr (J.p ≫ T.sX i) P.sY k) ∧
      MMP.Mori.IsProjectiveVariety ℂ (modelStr (J.p ≫ T.sX i) P.sY k) ∧
      Divisor.IsCanonicalDivisor (modelStr (J.p ≫ T.sX i) P.sY k) 3 (divisorSeq K P.KY k) ∧
      modelMap (J.p ≫ T.f i) P.πY k ≫ T.sZ i = modelStr (J.p ≫ T.sX i) P.sY k := by
  cases k with
  | zero =>
    refine ⟨(P.isQFactorial 0 hk).1, P.isProjectiveVariety, ?_, P.comp_eq⟩
    obtain ⟨n, hn⟩ := P.isCanonicalDivisor
    have h3 := hn.topologicalKrullDim_eq
    rw [P.dim_eq] at h3
    obtain rfl : n = 3 := mod_cast h3.symm
    exact hn
  | succ k =>
    have hs := P.isThreefoldStepDiagram k (by omega)
    refine ⟨hs.isNormalVariety_plus, hs.isProjectiveVariety_plus, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := hs.isCanonicalDivisor_plus
      rw [← P.KY_eq k (by omega)] at hn
      have h3 := hn.topologicalKrullDim_eq
      rw [hs.dim_plus] at h3
      obtain rfl : n = 3 := mod_cast h3.symm
      exact hn
    · change P.πY k ≫ T.sZ i = P.sY k
      rw [P.πY_eq k (by omega), Category.assoc, P.comp_eq_base k (by omega), hs.comp_eq_plus]

/-- The morphisms `π_k : V_k ⟶ Z`, `k ≤ m`, are dominant and induce isomorphisms of function
fields: `π₀ = f_i ∘ p_i` does, and `π_{k+1} = h_k ∘ g_k⁺` with `h_k ∘ g_k = π_k`. -/
private theorem isDominant_and_bijective [IsIntegral (T.Z i)] {k : ℕ} (hk : k ≤ P.m) :
    ∃ _ : IsDominant (modelMap (J.p ≫ T.f i) P.πY k),
      Function.Bijective (functionFieldMap (modelMap (J.p ≫ T.f i) P.πY k)) := by
  induction k with
  | zero =>
    haveI := J.isBirationalMorphism.isDominant
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    refine ⟨(inferInstance : IsDominant (J.p ≫ T.f i)), ?_⟩
    change Function.Bijective ⇑(functionFieldMap (J.p ≫ T.f i))
    rw [coe_functionFieldMap_eq_comp J.p (T.f i) rfl]
    exact J.isBirationalMorphism.functionFieldMap_bijective.comp
      (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective
  | succ k ih =>
    obtain ⟨hd, hb⟩ := ih (by omega)
    exact isDominant_and_bijective_of_isThreefoldStepDiagram (Xp := modelSeq J.Y P.Y (k + 1))
      (P.isThreefoldStepDiagram k (by omega)) (P.h k) (P.modelMap_eq k (by omega)).symm
      (P.πY_eq k (by omega)).symm hb

/-- The morphisms `π_k : V_k ⟶ Z`, `k ≤ m`, are dominant. -/
theorem isDominant_modelMap [IsIntegral (T.Z i)] {k : ℕ} (hk : k ≤ P.m) :
    IsDominant (modelMap (J.p ≫ T.f i) P.πY k) :=
  (isDominant_and_bijective P hk).1

/-- **The centres on `Y_i` of the prime divisors of the models.** For a prime divisor `Q` of a
model `V_k`, `k ≤ m`, there is a prime divisor `P₀` of `V₀ = Y_i` with `ord_{P₀} = ord_Q` as
valuations of `k(Z)` and `coeff_Q Θ_k = coeff_{P₀} Θ_i'`: no step of the programme extracts a
divisor. -/
private theorem exists_primeDivisor_valuationOver_eq_coeff [IsIntegral (T.Z i)] [IsDominant J.p]
    [IsDominant (T.f i)] {k : ℕ} (hk : k ≤ P.m) (Q : MMP.Mori.PrimeDivisor (modelSeq J.Y P.Y k)) :
    haveI := isDominant_modelMap P hk
    ∃ P₀ : MMP.Mori.PrimeDivisor J.Y,
      P₀.valuationOver (J.p ≫ T.f i) = Q.valuationOver (modelMap (J.p ≫ T.f i) P.πY k) ∧
        (P.boundary k).coeff Q = Θ'.coeff P₀ := by
  induction k with
  | zero => exact ⟨Q, rfl, rfl⟩
  | succ k ih =>
    haveI := isDominant_modelMap P (Nat.le_of_succ_le hk)
    haveI := isDominant_modelMap P hk
    obtain ⟨Pm, hv, hc⟩ :=
      exists_primeDivisor_valuationOver_eq_of_isThreefoldStepDiagram
        (Xp := modelSeq J.Y P.Y (k + 1)) (πm := modelMap (J.p ≫ T.f i) P.πY k)
        (πp := modelMap (J.p ≫ T.f i) P.πY (k + 1)) (P.isThreefoldStepDiagram k (by omega)) (P.h k)
        (P.modelMap_eq k (by omega)).symm (P.πY_eq k (by omega)).symm Q
    obtain ⟨P₀, h₀, hc₀⟩ := ih (by omega) Pm
    refine ⟨P₀, h₀.trans hv, ?_⟩
    rw [P.boundary_succ_eq_flipTransform (by omega)]
    exact hc.trans hc₀

/-- **The equality on the prime divisors of the models.** For a prime divisor `Q` of a model
`V_k`, `k ≤ m`, the valuation of `k(X_{i+1})` corresponding to `ord_Q` has log discrepancy
`1 - coeff_Q Θ_k` over `(X_{i+1}, B_{i+1})`. -/
private theorem exists_isValuationLogDiscrepancy_one_sub_coeff [IsIntegral (T.Z i)]
    [IsDominant (T.fp i)]
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i)) (hΘ' : IsDecreasedBoundary J Θ')
    {k : ℕ} (hk : k ≤ P.m) (Q : MMP.Mori.PrimeDivisor (modelSeq J.Y P.Y k)) :
    haveI := isDominant_modelMap P hk
    ∃ s : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)),
      s.comap (functionFieldMap (T.fp i)) = Q.valuationOver (modelMap (J.p ≫ T.f i) P.πY k) ∧
        IsValuationLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) s
          (1 - ((P.boundary k).coeff Q : ℝ)) := by
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := J.isBirationalMorphism.isDominant
  haveI := isDominant_modelMap P hk
  obtain ⟨P₀, hv, hc⟩ := exists_primeDivisor_valuationOver_eq_coeff P hk Q
  obtain ⟨s, hs, hlog, -⟩ := hΘ'.isValuationLogDiscrepancy_one_sub_coeff hI P₀
  refine ⟨s, ?_, by rwa [hc]⟩
  rw [← hv]
  unfold IsTransportedValuation at hs
  rw [hs]
  exact (valuationOver_comp P₀ J.p (T.f i) rfl).symm

end Program

end MMP.Fourfold.StepDiagram.ProofLemIndexcBridgeUpperBound

namespace MMP.Fourfold.StabilizedTail

open MMP.Mori
open MMP.Fourfold.StepDiagram.ProofLemIndexcBridgeUpperBound

variable {T : StabilizedTail} {i : ℕ}

/-- **Models of a bridge programme lie below the next downstairs pair.** Let `J = (p_i, Θ_i)` be a
crepant junction of `(X_i, B_i)` extracting `I(X_i, B_i)`, `Θ'` its decreased boundary, and `P` a
finite relative threefold programme over `Z_i` by `π₀ = p_i ≫ f_i` from `(Y_i, Θ')`. For every
model `(V_k, Θ_k)`, `k ≤ m`, the morphism `π_k : V_k ⟶ Z_i` is dominant, and

* for valuations `ξ` of `ℂ(V_k)` and `ξ'` of `ℂ(X_{i+1})` with the same restriction to `ℂ(Z_i)`,
  `a(ξ; V_k, Θ_k) ≤ a(ξ'; X_{i+1}, B_{i+1})`;
* for a prime divisor `Q` of `V_k` and `ξ'` restricting to `ord_Q` on `ℂ(Z_i)`, the log
  discrepancy `a(ξ'; X_{i+1}, B_{i+1})` is that of `ord_Q` over `(V_k, Θ_k)`. -/
@[mmp "lem_mmp_indexc_bridge_upper_bound"]
public theorem IsDecreasedBoundary.le_of_isValuationLogDiscrepancy
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {K : Divisor J.Y}
    (P : RelativeThreefoldProgram (J.p ≫ T.sX i) (T.sZ i) (J.p ≫ T.f i) K Θ')
    {k : ℕ} (hk : k ≤ P.m) :
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ _ : IsDominant (modelMap (J.p ≫ T.f i) P.πY k),
      (∀ (ξ : Valuation (modelSeq J.Y P.Y k).functionField (WithZero (Multiplicative ℤ)))
          (ξ' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))),
          ξ.comap (functionFieldMap (modelMap (J.p ≫ T.f i) P.πY k)) =
            ξ'.comap (functionFieldMap (T.fp i)) →
          ∀ a a' : ℝ,
            IsValuationLogDiscrepancy (modelStr (J.p ≫ T.sX i) P.sY k) (P.boundary k) ξ a →
            IsValuationLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) ξ' a' → a ≤ a') ∧
      (∀ (Q : MMP.Mori.PrimeDivisor (modelSeq J.Y P.Y k))
          (ξ' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))),
          Q.valuationOver (modelMap (J.p ≫ T.f i) P.πY k) =
            ξ'.comap (functionFieldMap (T.fp i)) →
          ∀ a' : ℝ, IsValuationLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) ξ' a' →
            IsValuationLogDiscrepancy (modelStr (J.p ≫ T.sX i) P.sY k) (P.boundary k)
              Q.divisorialValuation a') := by
  have hSi := T.isThreefoldStepDiagram i
  have hSi1 := T.isThreefoldStepDiagram (i + 1)
  haveI := hSi.isNormalVariety_target.1.toIsIntegral
  haveI := hSi.isSmallMorphism_plus.isBirationalMorphism.isDominant
  obtain ⟨hd, hbij⟩ := isDominant_and_bijective P hk
  obtain ⟨hVn, hVp, hKV, hπs⟩ := model_facts P hk
  have hZ := hSi.isNormalVariety_target
  have hfps := hSi.isSmallMorphism_plus
  have hfb := hfps.isBirationalMorphism
  have hVQ := P.isQFactorial k hk
  have hprime := exists_isValuationLogDiscrepancy_one_sub_coeff P hI hΘ' hk
  refine ⟨hd, fun ξ ξ' hcomap a a' ha ha' => ?_, fun Q ξ' hQ a' ha' => ?_⟩
  · haveI : IsNormal (T.Z i) := hZ.2
    haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
    haveI : IsSeparated (T.sZ i) := hZ.1.toIsSeparated
    haveI : IsProper (modelStr (J.p ≫ T.sX i) P.sY k) :=
      isProper_of_isProjectiveMorphism _ hVp.isProjective
    haveI : IsProper (modelMap (J.p ≫ T.f i) P.πY k ≫ T.sZ i) := hπs ▸ inferInstance
    haveI : IsProper (modelMap (J.p ≫ T.f i) P.πY k) := IsProper.of_comp _ (T.sZ i)
    haveI : IsProper (T.fp i) := hfps.isProper
    obtain ⟨n, hKX⟩ := hSi1.isCanonicalDivisor
    obtain rfl : n = 3 := by
      have h3 := hKX.topologicalKrullDim_eq
      rw [hSi1.dim_minus] at h3
      exact_mod_cast h3.symm
    have hamp : (Divisor.toQDivisor (T.K (i + 1)) + T.B (i + 1)).HasRelativelyAmpleMultiple
        (T.fp i) := by
      rw [T.K_eq i, T.B_eq i]
      exact hSi.hasRelativelyAmpleMultiple_plus
    exact le_of_comap_eq_of_forall_primeDivisor hZ hVn hVQ hSi.isNormalVariety_plus hπs
      (isBirationalMorphism_of_bijective _ hbij) hSi.comp_eq_plus hfb hKV (P.boundary k) hKX
      hSi1.isQCartier_minus hamp hprime ξ ξ' hcomap ha ha'
  · obtain ⟨s, hs, hlog⟩ := hprime Q
    obtain rfl : s = ξ' := valuation_eq_of_comap_eq hfb.functionFieldMap_bijective.2 (hs.trans hQ)
    rw [StepDiagram.ProofLemIndexcGraph.IsValuationLogDiscrepancy.unique ha' hlog]
    exact isValuationLogDiscrepancy_divisorialValuation hVn hKV
      (isQCartier_of_isQFactorial _ hVQ
        (Divisor.toQDivisor (divisorSeq K P.KY k) + P.boundary k)) Q

end MMP.Fourfold.StabilizedTail

end
