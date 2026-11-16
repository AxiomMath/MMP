module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.BracketsCofinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.WeightSupportFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.ChowForm.Defs
import MMP.AlgebraicGeometry.ChowForm.CoreSkeleton
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# The difficulty change under a coefficient decrease

Let `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` be a coefficient-decrease move of a prepared chain, `i ≥ i₀`:
the passage from the junction `(Y_i, Θ_i)` to the decreased pair `(Y_i, Θ_i')` on the same
variety. There is a finite set `F` of normalized divisorial valuations of `ℂ(Y_i)` exceptional
over `Y_i` such that `w_v(Y_i, Θ_i) = w_v(Y_i, Θ_i')` for every exceptional `v ∉ F`, and
`𝒟(Y_i, Θ_i) - 𝒟(Y_i, Θ_i') = ∑_{v ∈ F} (w_v(Y_i, Θ_i) - w_v(Y_i, Θ_i'))`.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.exists_finite_isDifficulty_sub_eq_finsum`: the
  statement.

## Implementation notes

* The decreased pair is a model `y` of the prepared chain, identified with `Y_i` by an
  isomorphism `φ : Y_y ≅ Y_i`. When the `i`-th bridge has a model, `0 < m_i`, the decreased pair
  is the model `(i, some 0)`, whose variety is `Y_i` itself, and `φ` is the identity. When
  `m_i = 0`, the decreased pair `(V_0, Θ_0) = (Y_i, Θ_i')` is the end of the bridge, the junction
  `(i + 1, none)`, and `φ` is the inverse of the identification `e : V_{m_i} ≅ Y_{i+1}` of the
  bridge. Both cases are coefficient-decrease moves of the chain.
* Valuations are valuations of `ℂ(Y_i)`; a valuation `v` of `ℂ(Y_i)` is weighed on the decreased
  pair through the valuation `v'` of `ℂ(Y_y)` with `v'.comap φ^* = v`, where `φ^*` is the
  isomorphism of function fields induced by `φ`.
* Weights and difficulties are the predicates
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight` and
  `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty` at the fixed admissible scale; the
  statement holds for every choice of values these predicates admit.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedTail.PreparedChain

open MMP.Mori

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Valuations of prime divisors -/

/-- Valuations with the same pull-back along a surjective ring map are equal. -/
private theorem comap_injective_of_surjective {A B Γ : Type*} [Ring A] [Ring B]
    [LinearOrderedCommMonoidWithZero Γ] {φ : A →+* B} (hφ : Function.Surjective φ) :
    Function.Injective (fun v : Valuation B Γ => v.comap φ) := by
  intro v v' h
  ext b
  obtain ⟨a, rfl⟩ := hφ b
  exact congrArg (fun u : Valuation A Γ => u a) h

/-- `ord_P` regarded through a composite is `ord_P` regarded through the first map, restricted
along the second. -/
private theorem valuationOver_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (P : MMP.Mori.PrimeDivisor X) (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsDominant f] [IsDominant g] [IsDominant (f ≫ g)] :
    P.valuationOver (f ≫ g) = (P.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- `valuationOver` only depends on the morphism. -/
private theorem valuationOver_congr {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] (P : MMP.Mori.PrimeDivisor X) {f g : X ⟶ Y} [IsDominant f]
    [IsDominant g] (h : f = g) : P.valuationOver f = P.valuationOver g := by
  subst h
  rfl

/-- On a normal variety, a prime divisor is determined by its valuation seen through a dominant
morphism inducing a surjection of function fields. -/
private theorem eq_of_valuationOver_eq {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (f : X ⟶ Y)
    [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    {P P' : MMP.Mori.PrimeDivisor X} (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have h1 : P.divisorialValuation = P'.divisorialValuation := comap_injective_of_surjective hf h
  have h2 : (DivisorOver.ofPrimeDivisor ℂ hX P).valuation =
      (DivisorOver.ofPrimeDivisor ℂ hX P').valuation := by
    ext g
    change P.divisorialValuation (functionFieldMap (𝟙 X) g) =
      P'.divisorialValuation (functionFieldMap (𝟙 X) g)
    rw [MMP.Mori.functionFieldMap_id_apply, h1]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 h2)

/-- Transport of prime divisors along an isomorphism. -/
private noncomputable def primeDivisorEquivOfIso {V W : Scheme.{0}} (e : V ≅ W) :
    MMP.Mori.PrimeDivisor V ≃ MMP.Mori.PrimeDivisor W where
  toFun := OpenWeilRestriction.primeDivisorMap e.hom
  invFun := OpenWeilRestriction.primeDivisorMap e.symm.hom
  left_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (OpenWeilRestriction.primeDivisorMap e.symm.hom
      (OpenWeilRestriction.primeDivisorMap e.hom Q)).genericPoint = _
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
      OpenWeilRestriction.genericPoint_primeDivisorMap, ← Scheme.Hom.comp_apply]
    simp
  right_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (OpenWeilRestriction.primeDivisorMap e.hom
      (OpenWeilRestriction.primeDivisorMap e.symm.hom Q)).genericPoint = _
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
      OpenWeilRestriction.genericPoint_primeDivisorMap, ← Scheme.Hom.comp_apply]
    simp

/-- Transport along an isomorphism preserves the divisorial valuation. -/
private theorem divisorialValuation_primeDivisorEquivOfIso {V W : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (e : V ≅ W) [IsDominant e.hom] (Q : MMP.Mori.PrimeDivisor V) :
    Q.divisorialValuation.comap (functionFieldMap e.hom) =
      (primeDivisorEquivOfIso e Q).divisorialValuation := by
  ext g
  rw [Valuation.comap_apply]
  by_cases hg : g = 0
  · simp [hg]
  have hg' : functionFieldMap e.hom g ≠ 0 := (map_ne_zero _).mpr hg
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso e.hom Q (primeDivisorEquivOfIso e Q)
      (OpenWeilRestriction.genericPoint_primeDivisorMap e.hom Q).symm]

/-- `ord_Q` regarded through `e ≫ b`, for an isomorphism `e`, is `ord` of the transported prime
divisor regarded through `b`. -/
private theorem valuationOver_iso_comp {V W Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Z] (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) (b : W ⟶ Z) [IsDominant b]
    [IsDominant e.hom] [IsDominant (e.hom ≫ b)] :
    Q.valuationOver (e.hom ≫ b) = (primeDivisorEquivOfIso e Q).valuationOver b := by
  rw [valuationOver_comp, PrimeDivisor.valuationOver, divisorialValuation_primeDivisorEquivOfIso]
  rfl

/-- The inverse transform along an isomorphism has, at `P`, the coefficient at the image of
`P`. -/
private theorem coeff_inverseTransformDivisor_iso {V W : Scheme.{0}} (e : V ≅ W)
    (D : MMP.Mori.QDivisor W) (P : MMP.Mori.PrimeDivisor V) :
    (inverseTransformDivisor e.hom D).coeff P = D.coeff (primeDivisorEquivOfIso e P) := by
  have htop : biregularLocus e.hom = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff e.hom).mpr inferInstance))
  exact MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint
    (OpenWeilRestriction.genericPoint_primeDivisorMap e.hom P).symm (by rw [htop]; trivial) D

/-! ### Label centres on the decreased pair -/

/-- Transported valuations are unique: the identifications `k(X_j) ≅ k(Z_j) ≅ k(X_{j+1})` are
isomorphisms. -/
private theorem isTransportedValuationFrom_unique {T : StabilizedTail} : ∀ {i : ℕ}
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨_, hu, huw⟩, ⟨_, hu', huw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique hu hu'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hbir := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
    exact comap_injective_of_surjective hbir.functionFieldMap_bijective.2 (huw.trans huw'.symm)

section LabelCentre

variable {T : StabilizedTail} (C : StabilizedTail.TerminalChain T)

/-- A label has at most one centre on a junction. -/
private theorem eq_of_isLabelCentre_none {S : C.Label} {i : ℕ}
    (hX : IsNormalVariety ℂ ((C.junction i).p ≫ T.sX i))
    {P P' : MMP.Mori.PrimeDivisor (C.junction i).Y}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S ⟨i, none⟩ P') : P = P' := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hP⟩ := h
  obtain ⟨w', hw', hP'⟩ := h'
  obtain rfl := isTransportedValuationFrom_unique hw hw'
  exact eq_of_valuationOver_eq hX _ (C.junction i).isBirationalMorphism.functionFieldMap_bijective.2
    (hP.trans hP'.symm)

/-- The centre of a label on a junction `Y_i` is its centre on the first model `V_0 = Y_i` of the
`i`-th bridge. -/
private theorem isLabelCentre_some_zero {S : C.Label} {i : ℕ} (hm : 0 < (C.bridge i).P.m)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨w, hw, (inferInstance : IsDominant ((C.junction i).p ≫ T.f i)), ?_⟩
  change P.valuationOver ((C.junction i).p ≫ T.f i) = _
  rw [valuationOver_comp, hP]

/-- A label has at most one centre on the first model of a bridge. -/
private theorem eq_of_isLabelCentre_some_zero {S : C.Label} {i : ℕ} (hm : 0 < (C.bridge i).P.m)
    (hX : IsNormalVariety ℂ ((C.junction i).p ≫ T.sX i))
    {P P' : MMP.Mori.PrimeDivisor (C.junction i).Y}
    (h : C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P) (h' : C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P') :
    P = P' := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  obtain ⟨w, hw, _, hP⟩ := h
  obtain ⟨w', hw', _, hP'⟩ := h'
  obtain rfl := isTransportedValuationFrom_unique hw hw'
  have hb : IsBirationalMorphism ((C.junction i).p ≫ T.f i) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp (C.junction i).isBirationalMorphism
      (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
  exact eq_of_valuationOver_eq hX ((C.junction i).p ≫ T.f i) hb.functionFieldMap_bijective.2
    (hP.trans hP'.symm)

/-- Through the identification `e : Y_i ≅ Y_{i+1}` of a bridge with no step, the centre of a
label on `Y_i` is carried to its centre on `Y_{i+1}`. -/
private theorem isLabelCentre_succ_of_iso {S : C.Label} {i : ℕ}
    (e : (C.junction i).Y ≅ (C.junction (i + 1)).Y)
    (hπ : (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i + 1, none⟩ (primeDivisorEquivOfIso e P) := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI : IsDominant e.hom := (isBirationalMorphism_of_isIso e.hom).isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨_, ⟨w, hw, ?_⟩, rfl⟩
  change ((primeDivisorEquivOfIso e P).valuationOver (C.junction (i + 1)).p).comap
    (functionFieldMap (T.fp i)) = w.comap (functionFieldMap (T.f i))
  rw [← valuationOver_comp, ← valuationOver_iso_comp, ← hP, ← valuationOver_comp]
  exact valuationOver_congr _ (by rw [hπ])

end LabelCentre

/-! ### Log discrepancies along an isomorphism -/

section IsoTransport

open MMP.Fourfold.Oai4C1.CommonModel

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
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
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
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
      (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
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

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X U : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [IsIntegral U]
    (hX : IsNormalVariety ℂ sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

variable {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- The divisor `(Y, f ≫ g, E)` over `W`, for a divisor `(Y, f, E)` over `V` and a dominant open
immersion `g : V ⟶ W`. -/
private noncomputable def compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) : DivisorOver ℂ sW where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    have := D.isNormalVariety
    rwa [Category.assoc, hs]
  isBirationalMorphism := by
    haveI := D.isIntegral
    exact isBirationalMorphism_comp D.isBirationalMorphism
      (isBirationalMorphism_of_isOpenImmersion g ⊤ dense_univ)
  E := D.E

/-- The valuation of `(Y, f ≫ g, E)` is that of `(Y, f, E)` carried along `g`. -/
private theorem valuation_compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) :
    (compOpen g hs D).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := (compOpen g hs D).isDominant
  refine Valuation.ext fun t => ?_
  change D.E.valuationOver (D.f ≫ g) t = D.E.valuationOver D.f (functionFieldMap g t)
  rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- **Log discrepancies are invariant under isomorphisms of pairs.** Let `φ : V ≅ W` be an
isomorphism of normal varieties over `ℂ`, `B'` a `ℚ`-divisor on `W` and `B` the divisor on `V`
with `coeff_Γ B = coeff_{φ(Γ)} B'`. If `(Y, f, E)` is a divisor over `V` and `(Y', f', E')` one
over `W` with the corresponding valuation, then `a(E, V, B) = a(E', W, B')`. -/
private theorem eq_of_isLogDiscrepancy_of_iso [CompactSpace V] (φ : V ≅ W)
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : φ.hom ≫ sW = sV) {B : QDivisor V}
    {B' : QDivisor W}
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap φ.hom Γ))
    {n n' : ℕ} {D : DivisorOver ℂ sV} {D' : DivisorOver ℂ sW} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sV n (QDivisor.toRDivisor B) D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sW n' (QDivisor.toRDivisor B') D' a')
    (hv : D'.valuation = D.valuation.comap (functionFieldMap φ.hom)) : a = a' := by
  subst hs
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp : IsProper D.f := ha.2.1
  obtain ⟨hW, -, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, -, hCc, hdec, -, -⟩ := id ha'
  obtain ⟨hV, -, -, -, ⟨K₀, hK₀, -⟩, -⟩ := id ha
  have hnn : n = n' := by
    have h1 := hK₀.topologicalKrullDim_eq
    have h2 := hK'.topologicalKrullDim_eq
    rw [(Scheme.homeoOfIso φ).isHomeomorph.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm.trans h2
  subst hnn
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (φ.hom ≫ sW) := hV.1.toLocallyOfFiniteType
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  have hbφ : IsBirationalMorphism φ.hom := isBirationalMorphism_of_isIso _
  have hbij : Function.Bijective (functionFieldMap φ.hom) := hbφ.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sW)
    hK'.topologicalKrullDim_eq
  -- the pull-backs `L_i = φ^* C_i` and `M_i = f^* L_i`
  choose L hL using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant φ.hom (hCc i)
  have hLc : ∀ i, (L i).IsCartier := fun i => (hL i).isCartier (hCc i)
  choose M hM using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hLc i)
  set Dφ := compOpen φ.hom rfl D
  haveI : IsDominant (D.f ≫ φ.hom) := Dφ.isDominant
  have hpφ : IsProper Dφ.f := by
    change IsProper (D.f ≫ φ.hom)
    infer_instance
  have hord : D.ordPullback (pullbackRationalPluriForms sW φ.hom ω) = Dφ.ordPullback ω := by
    change D.E.ordForm (pullbackRationalPluriForms (φ.hom ≫ sW) D.f
      (pullbackRationalPluriForms sW φ.hom ω)) =
        D.E.ordForm (pullbackRationalPluriForms sW (D.f ≫ φ.hom) ω)
    rw [pullbackRationalPluriForms_comp φ.hom D.f hbij
      (IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism) hd ω]
    rfl
  have h1 : MMP.Intersection.IsLogDiscrepancy sW n (QDivisor.toRDivisor B') Dφ
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) :=
    ⟨hW, hpφ, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, M, hCc, hdec, fun i => ⟨_, isPullback_comp
      (hL i) (hM i) (fun Z =>
      MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ φ.hom) (C i) Z)⟩, rfl⟩
  have e1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha' h1
    (hv.trans (valuation_compOpen φ.hom rfl D).symm)
  -- the same data, pulled back to `V`
  have hne : pullbackRationalPluriForms sW φ.hom ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hW hbφ hK'.topologicalKrullDim_eq hω
  have hcan : (divisorOfForm (pullbackRationalPluriForms sW φ.hom ω)).IsCanonicalDivisor
      (φ.hom ≫ sW) n := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₀ hne
    rw [one_smul] at this
    exact hK₀.of_linearlyEquivalent this
  have hdec2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      ((Γ.ordForm (pullbackRationalPluriForms sW φ.hom ω) : ℤ) : ℝ) +
        (QDivisor.toRDivisor B).coeff Γ = ∑ i, r i * ((L i).coeff Γ : ℝ) := by
    intro Γ
    set Γ' := OpenWeilRestriction.primeDivisorMap φ.hom Γ
    have hΓ : φ.hom Γ.genericPoint = Γ'.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso φ.hom hbij hd Γ Γ' hΓ ω,
      QDivisor.coeff_toRDivisor, hB Γ]
    simp_rw [MMP.Positivity.coeff_eq_of_isPullback Γ Γ' hΓ (hCc _) (hL _)]
    have := hdec Γ'
    rwa [QDivisor.coeff_toRDivisor] at this
  have h2 : MMP.Intersection.IsLogDiscrepancy (φ.hom ≫ sW) n (QDivisor.toRDivisor B) D
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) := by
    refine ⟨hV, hp, _, hne, ⟨_, hcan, fun Γ => coeff_divisorOfForm _ Γ⟩, m, r, L, M, hLc,
      hdec2, fun i => ⟨_, hM i⟩, ?_⟩
    rw [hord]
    rfl
  exact (MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h2).trans e1.symm

end IsoTransport

/-- An isomorphism carries the closure of a point to the closure of its image. -/
private theorem image_closure_singleton {V W : Scheme.{0}} (e : V ≅ W) (x : V) :
    e.hom.base '' closure ({x} : Set V) = closure {e.hom x} := by
  have := (Scheme.homeoOfIso e).image_closure ({x} : Set V)
  rwa [Set.image_singleton] at this

/-! ### Transport along an isomorphism of normal varieties -/

section Transport

variable {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- Transporting a valuation along `e` and back along `e⁻¹` gives it back. -/
private theorem comap_inv_comap_hom (e : V ≅ W)
    (v : Valuation V.functionField (WithZero (Multiplicative ℤ))) :
    (v.comap (functionFieldMap e.hom)).comap (functionFieldMap e.inv) = v := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr (e.hom_inv_id),
    MMP.Mori.functionFieldMap_id_apply]

/-- The centre of a transported valuation is the image of the centre. -/
private theorem isCentre_comap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    (hs : e.hom ≫ sW = sV) {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    {Z : IrreducibleCloseds V} (h : MMP.Intersection.IsCentre ℂ sV v Z) :
    ∃ Z' : IrreducibleCloseds W, MMP.Intersection.IsCentre ℂ sW
      (v.comap (functionFieldMap e.hom)) Z' ∧ (Z' : Set W) = e.hom.base '' Z := by
  obtain ⟨D, hp, rfl, rfl⟩ := h
  refine ⟨(compOpen e.hom hs D).center,
    ⟨compOpen e.hom hs D, ?_, (valuation_compOpen e.hom hs D).symm, rfl⟩, ?_⟩
  · change IsProper (D.f ≫ e.hom)
    infer_instance
  · rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
      MMP.Positivity.DivisorOver.center_eq_closureSingleton]
    change closure {(D.f ≫ e.hom) D.E.genericPoint} = e.hom.base '' closure {D.f D.E.genericPoint}
    rw [Scheme.Hom.comp_apply]
    exact (image_closure_singleton e _).symm

/-- A transported exceptional valuation is exceptional. -/
private theorem isExceptionalValuation_comap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV)
    {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sV v) :
    MMP.Intersection.IsExceptionalValuation ℂ sW (v.comap (functionFieldMap e.hom)) := by
  obtain ⟨D, hp, rfl, hc⟩ := h
  refine ⟨compOpen e.hom hs D, ?_, (valuation_compOpen e.hom hs D).symm, ?_⟩
  · change IsProper (D.f ≫ e.hom)
    infer_instance
  · rw [MMP.Positivity.DivisorOver.codimension_center] at hc ⊢
    change 2 ≤ Order.coheight ((D.f ≫ e.hom) D.E.genericPoint)
    rwa [Scheme.Hom.comp_apply, Topology.IsOpenEmbedding.coheight_eq _ e.hom.isOpenEmbedding]

/-- Log discrepancies are carried along an isomorphism of pairs. -/
private theorem isValuationLogDiscrepancy_comap [CompactSpace V] (e : V ≅ W)
    {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) {B : QDivisor V}
    {B' : QDivisor W} (hB : ∀ Γ, B.coeff Γ = B'.coeff (primeDivisorEquivOfIso e Γ))
    (hB' : MMP.Mori.IsPair sW B') {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sV B v a) :
    IsValuationLogDiscrepancy sW B' (v.comap (functionFieldMap e.hom)) a := by
  obtain ⟨n, D, hp, rfl, ha⟩ := h
  obtain ⟨-, n₀, K, hK, -⟩ := id hB'
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp' : IsProper (compOpen e.hom hs D).f := by
    change IsProper (D.f ≫ e.hom)
    infer_instance
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB' hK (compOpen e.hom hs D)
  have ha' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp'
  have hB2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap e.hom Γ) := fun Γ => by
    have hΓ : primeDivisorEquivOfIso e Γ = OpenWeilRestriction.primeDivisorMap e.hom Γ :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((OpenWeilRestriction.genericPoint_primeDivisorMap e.hom Γ).trans
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm)
    rw [hB Γ, hΓ]
  have hac := eq_of_isLogDiscrepancy_of_iso e hs hB2 ha ha' (valuation_compOpen e.hom hs D)
  exact ⟨n₀, compOpen e.hom hs D, hp', valuation_compOpen e.hom hs D, hac ▸ ha'⟩

end Transport

/-! ### Curves, prime divisors and normalizations along an isomorphism -/

section IsoCurves

variable {V W : Scheme.{0}}

/-- The image of a proper curve under an isomorphism over `ℂ`. -/
private noncomputable def properCurveMap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) (γ : ProperCurve sV) : ProperCurve sW :=
  ⟨e.hom γ.point,
    MMP.Chow.DeterminantCurveForm.isProperCurve_iso e sV sW hs γ.point γ.isProperCurve⟩

private theorem closure_properCurveMap_point (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) (γ : ProperCurve sV) :
    closure {(properCurveMap e hs γ).point} = e.hom.base '' closure {γ.point} :=
  (image_closure_singleton e γ.point).symm

/-- Proper curves correspond along an isomorphism over `ℂ`. -/
private noncomputable def properCurveEquiv (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) : ProperCurve sV ≃ ProperCurve sW where
  toFun := properCurveMap e hs
  invFun := properCurveMap e.symm ((Iso.inv_comp_eq e).2 hs.symm)
  left_inv γ := ProperCurve.ext (Scheme.hom_inv_apply e γ.point)
  right_inv γ := ProperCurve.ext (Scheme.inv_hom_apply e γ.point)

/-- The support of a transported prime divisor is the image of the support. -/
private theorem support_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    (primeDivisorEquivOfIso e P).support = e.hom.base '' P.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure, image_closure_singleton]
  exact congrArg (fun x => closure {x}) (OpenWeilRestriction.genericPoint_primeDivisorMap e.hom P)

private theorem primeDivisorEquivOfIso_symm_apply_apply (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
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
    rw [primeDivisorEquivOfIso_symm_apply_apply] at h
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

/-- **Branch numbers are invariant under isomorphism.** -/
private theorem branchNumber_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V)
    (Z : Set V) :
    branchNumber (primeDivisorEquivOfIso e P) (e.hom.base '' Z) = branchNumber P Z := by
  obtain ⟨E, hE⟩ := exists_iso_primeDivisorNormalizationScheme e P
  have key : ∀ R : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P),
      primeDivisorNormalization (primeDivisorEquivOfIso e P) ''
          (primeDivisorEquivOfIso E R).support =
        e.hom.base '' (primeDivisorNormalization P '' R.support) := by
    intro R
    rw [support_primeDivisorEquivOfIso, Set.image_image, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    simpa using congrArg (fun f => f.base x) hE
  have hinj : Function.Injective (Set.image e.hom.base) :=
    Set.image_injective.mpr (Scheme.homeoOfIso e).injective
  unfold branchNumber
  rw [← Set.ncard_image_of_injective _ (primeDivisorEquivOfIso E).injective]
  congr 1
  ext R'
  constructor
  · intro h
    refine ⟨(primeDivisorEquivOfIso E).symm R', hinj ?_, Equiv.apply_symm_apply _ _⟩
    rwa [← key, Equiv.apply_symm_apply]
  · rintro ⟨R, hR, rfl⟩
    change _ = _
    rw [key]
    exact congrArg _ hR

/-- **Boxed ranks are invariant under isomorphism over `ℂ`.** -/
private theorem boxedSurfaceRank_eq_of_iso {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [X'.Over (Spec (.of ℂ))] [MMP.IsComplexScheme X]
    [MMP.IsComplexScheme X'] (E : X ≅ X')
    (hE : E.hom ≫ (X' ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ)) :
    boxedSurfaceRank X = boxedSurfaceRank X' := by
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1)).Over
      (Spec (.of ℂ)) := ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1⟩
  haveI := MMP.Fourfold.isComplexScheme_projectiveSpace 1 rfl
  let G : CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) ≅
      CategoryTheory.Limits.pullback (X' ↘ Spec (.of ℂ))
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) :=
    asIso (Limits.pullback.map _ _ _ _ E.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hE])
      (by rw [Category.comp_id, Category.id_comp]))
  have hG : G.hom ≫ (Limits.pullback.snd _ _ ≫
        Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) =
      Limits.pullback.snd _ _ ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1 := by
    simp only [G, asIso_hom, Limits.pullback.map, Limits.pullback.lift_snd_assoc,
      Category.comp_id]
  haveI : MMP.IsComplexScheme (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1)) :=
    MMP.Chow.isComplexScheme_pullback X _
  haveI : MMP.IsComplexScheme (CategoryTheory.Limits.pullback (X' ↘ Spec (.of ℂ))
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1)) :=
    MMP.Chow.isComplexScheme_pullback X' _
  exact (MMP.Analytic.cycleRank_eq_of_iso G hG).2.2.2 2

end IsoCurves

/-! ### Centres of exceptional valuations on a threefold -/

/-- The closure of the generic point of a proper curve, as a subspace of `X`, has dimension
one: it is the image of the closed embedding `C ⟶ X`. -/
private theorem topologicalKrullDim_closure_point {k : Type*} [Field k] {X : Scheme}
    {sX : X ⟶ Spec (.of k)} (C : MMP.Mori.ProperCurve sX) :
    topologicalKrullDim (closure {C.point} : Set X) = 1 := by
  have hr : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

section Centres

variable {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}

/-- The centre of a valuation on a variety is unique. -/
private theorem isCentre_unique (hX : MMP.Mori.IsVariety ℂ sX)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {Z Z' : IrreducibleCloseds X}
    (h : MMP.Intersection.IsCentre ℂ sX v Z) (h' : MMP.Intersection.IsCentre ℂ sX v Z') :
    Z = Z' := by
  obtain ⟨D, -, rfl, rfl⟩ := h
  obtain ⟨D', -, hv, rfl⟩ := h'
  rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
    MMP.Positivity.DivisorOver.center_eq_closureSingleton,
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX hv]

/-- **Exceptional centres on a threefold.** An exceptional valuation of a proper threefold over
`ℂ` has a centre, and the centre is a closed point or a proper curve. -/
private theorem exists_isCentre_of_isExceptionalValuation [IsProper sX]
    (hdim : topologicalKrullDim X = 3)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sX v) :
    ∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre ℂ sX v Z ∧
      ((∃ p : X, (Z : Set X) = {p}) ∨ ∃ γ : ProperCurve sX, (Z : Set X) = closure {γ.point}) := by
  obtain ⟨D, hp, rfl, hc⟩ := h
  refine ⟨D.center, ⟨D, hp, rfl, rfl⟩, ?_⟩
  rw [MMP.Positivity.DivisorOver.codimension_center] at hc
  rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton]
  set z := D.f D.E.genericPoint
  have hK : Order.krullDim X = 3 := by
    rw [← hdim]
    exact (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  have hno : ∀ w₁ w₂ : X, z ⤳ w₁ → w₁ ⤳ w₂ → z ≠ w₁ → w₁ ≠ w₂ → False := by
    intro w₁ w₂ h1 h2 h3 h4
    have l1 : w₁ < z := lt_of_le_not_ge (show w₁ ≤ z from h1)
      fun h => h3 (h1.antisymm (show w₁ ⤳ z from h)).eq
    have l2 : w₂ < w₁ := lt_of_le_not_ge (show w₂ ≤ w₁ from h2)
      fun h => h4 (h2.antisymm (show w₂ ⤳ w₁ from h)).eq
    have e1 := Order.height_add_one_le l2
    have hht : (2 : ℕ∞) ≤ Order.height z :=
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.height w₂ + 1 + 1 := by
          gcongr
          exact zero_le
        _ ≤ Order.height w₁ + 1 := by gcongr
        _ ≤ Order.height z := Order.height_add_one_le l1
    have hk := Order.height_add_coheight_le_krullDim z
    rw [hK] at hk
    have hk' : Order.height z + Order.coheight z ≤ 3 := by
      have : ((Order.height z + Order.coheight z : ℕ∞) : WithBot ℕ∞) ≤ ((3 : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        exact hk
      exact WithBot.coe_le_coe.mp this
    exact absurd ((add_le_add hht hc).trans hk') (by decide)
  rcases MMP.Chow.DeterminantCurveForm.isClosed_or_isProperCurve sX z hno with hcl | hpc
  · exact Or.inl ⟨z, hcl.closure_eq⟩
  · exact Or.inr ⟨⟨z, hpc⟩, rfl⟩

/-- A point centre and a curve centre of the same valuation cannot both occur. -/
private theorem not_isCentre_singleton_and_closure (hX : MMP.Mori.IsVariety ℂ sX)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {Z Z' : IrreducibleCloseds X}
    {p : X} (γ : ProperCurve sX) (h : MMP.Intersection.IsCentre ℂ sX v Z) (hZ : (Z : Set X) = {p})
    (h' : MMP.Intersection.IsCentre ℂ sX v Z') (hZ' : (Z' : Set X) = closure {γ.point}) :
    False := by
  obtain rfl := isCentre_unique hX h h'
  have h1 := topologicalKrullDim_closure_point γ
  rw [← hZ', hZ, topologicalKrullDim_eq_zero_of_discreteTopology_nonempty] at h1
  exact absurd h1 (by decide)

/-- Two curve centres of the same valuation are the same curve. -/
private theorem eq_of_isCentre_closure (hX : MMP.Mori.IsVariety ℂ sX)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {Z Z' : IrreducibleCloseds X}
    {γ γ' : ProperCurve sX} (h : MMP.Intersection.IsCentre ℂ sX v Z)
    (hZ : (Z : Set X) = closure {γ.point}) (h' : MMP.Intersection.IsCentre ℂ sX v Z')
    (hZ' : (Z' : Set X) = closure {γ'.point}) : γ = γ' := by
  obtain rfl := isCentre_unique hX h h'
  exact ProperCurve.ext (inseparable_iff_closure_eq.mpr (hZ.symm.trans hZ')).eq

/-- A valuation centred at a point or along one of the curves of `t` has exactly one such
centre, so an integer splits as the corresponding sum of indicator terms. -/
private theorem eq_ite_add_sum_ite_of_isCentre (hX : MMP.Mori.IsVariety ℂ sX)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {pt : Prop} [Decidable pt]
    {cen : ProperCurve sX → Prop} [DecidablePred cen]
    (hpt : pt → ∃ (Z : IrreducibleCloseds X) (p : X),
      MMP.Intersection.IsCentre ℂ sX v Z ∧ (Z : Set X) = {p})
    (hcen : ∀ γ, cen γ → ∃ Z : IrreducibleCloseds X,
      MMP.Intersection.IsCentre ℂ sX v Z ∧ (Z : Set X) = closure {γ.point})
    {t : Finset (ProperCurve sX)} (h : pt ∨ ∃ γ ∈ t, cen γ) (x : ℤ) :
    x = (if pt then x else 0) + ∑ γ ∈ t, if cen γ then x else 0 := by
  rcases h with hp | ⟨γ₀, hγ₀, hc₀⟩
  · rw [if_pos hp, Finset.sum_eq_zero, add_zero]
    intro γ _
    rw [if_neg]
    intro hcγ
    obtain ⟨Z, p, hZ, hZp⟩ := hpt hp
    obtain ⟨Z', hZ', hZ'γ⟩ := hcen γ hcγ
    exact not_isCentre_singleton_and_closure hX γ hZ hZp hZ' hZ'γ
  · have hnp : ¬ pt := fun hp => by
      obtain ⟨Z, p, hZ, hZp⟩ := hpt hp
      obtain ⟨Z', hZ', hZ'γ⟩ := hcen γ₀ hc₀
      exact not_isCentre_singleton_and_closure hX γ₀ hZ hZp hZ' hZ'γ
    rw [if_neg hnp, zero_add, Finset.sum_eq_single_of_mem γ₀ hγ₀, if_pos hc₀]
    intro γ _ hne
    rw [if_neg]
    intro hcγ
    obtain ⟨Z, hZ, hZγ⟩ := hcen γ hcγ
    obtain ⟨Z', hZ', hZ'γ⟩ := hcen γ₀ hc₀
    exact hne (eq_of_isCentre_closure hX hZ hZγ hZ' hZ'γ)

end Centres

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

/-! ### The difference of difficulties -/

/-- The log discrepancy of a valuation is unique. -/
private theorem isValuationLogDiscrepancy_unique {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a b : ℝ}
    (ha : IsValuationLogDiscrepancy sX B v a) (hb : IsValuationLogDiscrepancy sX B v b) :
    a = b := by
  obtain ⟨n, D, -, hv, ha⟩ := ha
  obtain ⟨n', D', -, hv', hb⟩ := hb
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb (hv.trans hv'.symm)

/-- The weight of a valuation on a model of the chain is unique. -/
private theorem isValuationWeight_unique {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    {z : Q.chain.ModelIndex}
    {v : Valuation (Q.chain.model z).functionField (WithZero (Multiplicative ℤ))} {w₁ w₂ : ℕ}
    (h₁ : Q.chain.IsValuationWeight Q.scale z v w₁)
    (h₂ : Q.chain.IsValuationWeight Q.scale z v w₂) : w₁ = w₂ := by
  obtain ⟨-, a, ha, rfl⟩ := h₁
  obtain ⟨-, b, hb, rfl⟩ := h₂
  rw [isValuationLogDiscrepancy_unique ha hb]

/-- The default of a label on a model whose label centres are unique is unique. -/
private theorem isLabelDefault_unique {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    {z : Q.chain.ModelIndex}
    (hz : ∀ S {P P' : MMP.Mori.PrimeDivisor (Q.chain.model z)},
      Q.chain.IsLabelCentre S z P → Q.chain.IsLabelCentre S z P' → P = P')
    {S} {a b : ℕ} (ha : Q.chain.IsLabelDefault Q.scale S z a)
    (hb : Q.chain.IsLabelDefault Q.scale S z b) : a = b := by
  obtain ⟨c₁, ⟨P, hP, rfl⟩, rfl⟩ := ha
  obtain ⟨c₂, ⟨P', hP', rfl⟩, rfl⟩ := hb
  rw [hz S hP hP']

/-- **The difficulty change under a coefficient decrease**, for a decreased pair `V` identified
with `Y_i` by an isomorphism `φ : V ≅ Y_i` over `ℂ` that carries the boundary of `V` to `Θ_i'` and
the label centres of `V` to those of `Y_i`. -/
private theorem exists_finite_isDifficulty_sub_eq_finsum_of_iso {T : StabilizedTail}
    (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) (y : Q.ModelIndex) (φ : Q.chain.model y.1 ≅ Q.chain.model ⟨i, none⟩)
    (hs : φ.hom ≫ Q.chain.modelStructure ⟨i, none⟩ = Q.chain.modelStructure y.1)
    (hB : ∀ Γ, (Q.chain.modelBoundary y.1).coeff Γ =
      (Q.chain.bridge i).Θ'.coeff (primeDivisorEquivOfIso φ Γ))
    (hpair : MMP.Mori.IsPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ')
    (hc : ∀ S P, Q.chain.IsLabelCentre S y.1 P →
      Q.chain.IsLabelCentre S ⟨i, none⟩ (primeDivisorEquivOfIso φ P)) :
    ∃ F : Set (Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ))),
      F.Finite ∧
      (∀ v ∈ F, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v) ∧
      (∀ v ∉ F, ∀ v' : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap φ.hom) = v →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
          Q.chain.IsValuationWeight Q.scale y.1 v' w' → w = w') ∧
      ∀ (D D' : ℤ), Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D → Q.IsDifficulty y D' →
        ∀ w w' : Valuation (Q.chain.model ⟨i, none⟩).functionField
            (WithZero (Multiplicative ℤ)) → ℕ,
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) →
          (∀ v ∈ F, ∀ v' : Valuation (Q.chain.model y.1).functionField
              (WithZero (Multiplicative ℤ)),
            v'.comap (functionFieldMap φ.hom) = v →
              Q.chain.IsValuationWeight Q.scale y.1 v' (w' v)) →
          D - D' = ∑ᶠ (v) (_ : v ∈ F), ((w v : ℤ) - w' v) := by
  classical
  -- transport of valuations
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Valuation (Q.chain.model y.1).functionField
      (WithZero (Multiplicative ℤ)) →
      Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)),
      ∀ v', Φ v' = v'.comap (functionFieldMap φ.hom) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ)) →
      Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ)),
      ∀ v, Ψ v = v.comap (functionFieldMap φ.inv) := ⟨_, fun _ => rfl⟩
  have hΨΦ : ∀ v', Ψ (Φ v') = v' := fun v' => by rw [hΨ, hΦ]; exact comap_inv_comap_hom φ v'
  have hΦΨ : ∀ v, Φ (Ψ v) = v := fun v => by rw [hΦ, hΨ]; exact comap_inv_comap_hom φ.symm v
  have hΨinj : Function.Injective Ψ := fun a b h => by rw [← hΦΨ a, h, hΦΨ]
  have hs' : φ.inv ≫ Q.chain.modelStructure y.1 = Q.chain.modelStructure ⟨i, none⟩ :=
    (Iso.inv_comp_eq φ).2 hs.symm
  -- the two models
  obtain ⟨hΘx, hprojx, -, hdimx, -, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  obtain ⟨-, hprojy, -, -, -, -⟩ := Q.echoSetting_model y
  haveI : CompactSpace (Q.chain.model y.1) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (Q.chain.modelStructure y.1) := hprojy
    exact QuasiCompact.compactSpace_of_compactSpace (Q.chain.modelStructure y.1)
  have hnvW : IsNormalVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hΘx.1.1.isPair.1
  have hvarW : MMP.Mori.IsVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hnvW.1
  haveI : IsProper (Q.chain.modelStructure ⟨i, none⟩) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hprojx
    infer_instance
  -- weights
  have hwt : ∀ v' w', Q.chain.IsValuationWeight Q.scale y.1 v' w' →
      MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) (Φ v') ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
          (Q.chain.bridge i).Θ' (Φ v') a ∧ w' = difficultyWeight Q.scale (2 - a) := by
    rintro v' w' ⟨hex, a, ha, rfl⟩
    rw [hΦ]
    exact ⟨isExceptionalValuation_comap φ hs hex, a,
      isValuationLogDiscrepancy_comap φ hs hB hpair ha, rfl⟩
  -- centres
  have hptV : ∀ {v' : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model y.1)} {p : Q.chain.model y.1},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) v' Z →
        (Z : Set (Q.chain.model y.1)) = {p} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) (Φ v') Z' ∧
            (Z' : Set (Q.chain.model ⟨i, none⟩)) = {φ.hom p} := by
    intro v' Z p h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ hs h
    exact ⟨Z', hΦ v' ▸ h', by rw [hZ', hZ, Set.image_singleton]⟩
  have hptW : ∀ {v : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)} {p : Q.chain.model ⟨i, none⟩},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z →
        (Z : Set (Q.chain.model ⟨i, none⟩)) = {p} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model y.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) (Ψ v) Z' ∧
            (Z' : Set (Q.chain.model y.1)) = {φ.inv p} := by
    intro v Z p h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ.symm hs' h
    exact ⟨Z', hΨ v ▸ h', by rw [hZ', hZ, Set.image_singleton]; rfl⟩
  have hcenV : ∀ {v' : Valuation (Q.chain.model y.1).functionField
      (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model y.1)} {γ' : ProperCurve (Q.chain.modelStructure y.1)},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) v' Z →
        (Z : Set (Q.chain.model y.1)) = closure {γ'.point} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) (Φ v') Z' ∧
            (Z' : Set (Q.chain.model ⟨i, none⟩)) =
              closure {(properCurveEquiv φ hs γ').point} := by
    intro v' Z γ' h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ hs h
    exact ⟨Z', hΦ v' ▸ h', by
      rw [hZ', hZ]
      exact (closure_properCurveMap_point φ hs γ').symm⟩
  have hcenW : ∀ {v : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)}
      {γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩)},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z →
        (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model y.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) (Ψ v) Z' ∧
            (Z' : Set (Q.chain.model y.1)) =
              closure {((properCurveEquiv φ hs).symm γ).point} := by
    intro v Z γ h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ.symm hs' h
    exact ⟨Z', hΨ v ▸ h', by
      rw [hZ', hZ]
      exact (closure_properCurveMap_point φ.symm hs' γ).symm⟩
  -- the curves along which weights are unchanged
  obtain ⟨𝓔, h𝓔, hE⟩ := Q.exists_finite_isValuationWeight_eq hi
  -- point and curve centres
  obtain ⟨pt, hpt⟩ : ∃ pt : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ)) → Prop, ∀ v, pt v ↔
        ∃ (Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)) (p : Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {p} := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨cen, hcen⟩ : ∃ cen : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) →
      Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → Prop,
      ∀ γ v, cen γ v ↔ ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point} := ⟨_, fun _ _ => Iff.rfl⟩
  -- the finite set `F`
  obtain ⟨F, hF⟩ : ∃ F : Set (Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))), ∀ v, v ∈ F ↔
        MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
          (pt v ∨ ∃ γ ∈ 𝓔, cen γ v) ∧
          ((∃ w, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w ∧ w ≠ 0) ∨
            ∃ w', Q.chain.IsValuationWeight Q.scale y.1 (Ψ v) w' ∧ w' ≠ 0) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hFfin : F.Finite := by
    have hA := Q.finite_setOf_isCentre_singleton ⟨⟨i, none⟩, hi⟩
    have hA' := Q.finite_setOf_isCentre_singleton y
    refine (((hA.union (h𝓔.biUnion fun γ _ =>
      Q.finite_setOf_isCentre_closure ⟨⟨i, none⟩, hi⟩ γ)).union
        ((hA'.image Φ).union (h𝓔.biUnion fun γ _ =>
          (Q.finite_setOf_isCentre_closure y ((properCurveEquiv φ hs).symm γ)).image Φ)))).subset ?_
    intro v hv
    obtain ⟨-, hc, ⟨w, hw, hw0⟩ | ⟨w', hw', hw0⟩⟩ := (hF v).1 hv
    · rcases hc with hp | ⟨γ, hγ, hc⟩
      · exact Or.inl (Or.inl ⟨(hpt v).1 hp, w, hw, hw0⟩)
      · exact Or.inl (Or.inr (Set.mem_biUnion hγ ⟨(hcen γ v).1 hc, w, hw, hw0⟩))
    · rcases hc with hp | ⟨γ, hγ, hc⟩
      · obtain ⟨Z, p, hZ, hp⟩ := (hpt v).1 hp
        obtain ⟨Z', h', hZ'⟩ := hptW hZ hp
        exact Or.inr (Or.inl ⟨Ψ v, ⟨⟨Z', _, h', hZ'⟩, w', hw', hw0⟩, hΦΨ v⟩)
      · obtain ⟨Z, hZ, hZγ⟩ := (hcen γ v).1 hc
        obtain ⟨Z', h', hZ'⟩ := hcenW hZ hZγ
        exact Or.inr (Or.inr (Set.mem_biUnion hγ ⟨Ψ v, ⟨⟨Z', h', hZ'⟩, w', hw', hw0⟩, hΦΨ v⟩))
  refine ⟨F, hFfin, fun v hv => ((hF v).1 hv).1, ?_, ?_⟩
  · intro v hvF v' hv' w w' hw hw'
    rw [← hΦ] at hv'
    subst hv'
    by_contra hne
    have hW : (∃ w, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ (Φ v') w ∧ w ≠ 0) ∨
        ∃ w', Q.chain.IsValuationWeight Q.scale y.1 (Ψ (Φ v')) w' ∧ w' ≠ 0 := by
      by_cases hw0 : w = 0
      · exact Or.inr ⟨w', by rwa [hΨΦ], by omega⟩
      · exact Or.inl ⟨w, hw, hw0⟩
    obtain ⟨Z, hZ, ⟨p, hp⟩ | ⟨γ, hγ⟩⟩ := exists_isCentre_of_isExceptionalValuation hdimx hw.1
    · exact hvF ((hF _).2 ⟨hw.1, Or.inl ((hpt _).2 ⟨Z, p, hZ, hp⟩), hW⟩)
    · by_cases hγ𝓔 : γ ∈ 𝓔
      · exact hvF ((hF _).2 ⟨hw.1, Or.inr ⟨γ, hγ𝓔, (hcen _ _).2 ⟨Z, hZ, hγ⟩⟩, hW⟩)
      · exact hne (hE γ hγ𝓔 (Φ v') ⟨Z, hZ, hγ⟩ w w' hw (hwt v' w' hw')).symm
  · intro D D' hD hD' w w' hw hw'
    have hw'' : ∀ v ∈ F, Q.chain.IsValuationWeight Q.scale y.1 (Ψ v) (w' v) :=
      fun v hv => hw' v hv (Ψ v) ((hΦ _).symm.trans (hΦΨ v))
    obtain ⟨wD, β, d, ρ, hwD, hβ, hd, hρ, rfl⟩ := hD
    obtain ⟨wD', β', d', ρ', hwD', hβ', hd', hρ', rfl⟩ := hD'
    set 𝔉 := hFfin.toFinset with h𝔉
    have hmem𝔉 : ∀ {v}, v ∈ 𝔉 ↔ v ∈ F := fun {v} => hFfin.mem_toFinset
    set Ψc := properCurveEquiv φ hs
    -- centres of labels and defaults
    have hcenx : ∀ S {P P' : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩)},
        Q.chain.IsLabelCentre S ⟨i, none⟩ P → Q.chain.IsLabelCentre S ⟨i, none⟩ P' → P = P' :=
      fun S P P' h h' => eq_of_isLabelCentre_none Q.chain hnvW h h'
    have hceny : ∀ S {P P' : MMP.Mori.PrimeDivisor (Q.chain.model y.1)},
        Q.chain.IsLabelCentre S y.1 P → Q.chain.IsLabelCentre S y.1 P' → P = P' :=
      fun S P P' h h' => (primeDivisorEquivOfIso φ).injective (hcenx S (hc S P h) (hc S P' h'))
    choose d₀ hd₀ using Q.isLabelDefault_const
    have hdx : ∀ S {a : ℕ}, Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ a → a = d₀ S :=
      fun S a h => isLabelDefault_unique Q hcenx h (hd₀ S ⟨i, none⟩ hi)
    have hdy : ∀ S {a : ℕ}, Q.chain.IsLabelDefault Q.scale S y.1 a → a = d₀ S :=
      fun S a h => isLabelDefault_unique Q hceny h (hd₀ S y.1 y.2)
    -- the label terms
    have hlab : ((∑ᶠ S, d S * ρ S : ℕ) : ℤ) = ((∑ᶠ S, d' S * ρ' S : ℕ) : ℤ) := by
      congr 1
      refine finsum_congr fun S => ?_
      rw [hdx S (hd S), hdy S (hd' S)]
      congr 1
      obtain ⟨P, hP, hρP⟩ := hρ S
      obtain ⟨P', hP', hρP'⟩ := hρ' S
      obtain rfl := hcenx S (hc S P' hP') hP
      dsimp only at hρP hρP'
      rw [hρP, hρP']
      obtain ⟨E, hE⟩ := exists_iso_primeDivisorNormalizationScheme φ P'
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure y.1) P'
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure ⟨i, none⟩)
        (primeDivisorEquivOfIso φ P')
      haveI := Q.chain.isComplexScheme_primeDivisorNormalizationScheme_model y.1 P'
      haveI := Q.chain.isComplexScheme_primeDivisorNormalizationScheme_model ⟨i, none⟩
        (primeDivisorEquivOfIso φ P')
      exact (boxedSurfaceRank_eq_of_iso E (by
        change E.hom ≫ (primeDivisorNormalization _ ≫ _) = primeDivisorNormalization P' ≫ _
        rw [← Category.assoc, hE, Category.assoc, hs])).symm
    -- the point sums
    have hpts : ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            ∃ p : Q.chain.model ⟨i, none⟩, IsClosed ({p} : Set (Q.chain.model ⟨i, none⟩)) ∧
              (Z : Set (Q.chain.model ⟨i, none⟩)) = {p}), wD v : ℕ) : ℤ) -
        ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model y.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) v Z ∧
            ∃ p : Q.chain.model y.1, IsClosed ({p} : Set (Q.chain.model y.1)) ∧
              (Z : Set (Q.chain.model y.1)) = {p}), wD' v : ℕ) : ℤ) =
        ∑ v ∈ 𝔉, if pt v then ((w v : ℤ) - w' v) else 0 := by
      rw [natCast_finsum_eq_sum 𝔉 ?_, natCast_finsum_eq_sum (𝔉.image Ψ) ?_,
        Finset.sum_image (fun a _ b _ h => hΨinj h), ← Finset.sum_sub_distrib]
      · refine Finset.sum_congr rfl fun v hv => ?_
        have hvF := hmem𝔉.1 hv
        by_cases hp : pt v
        · obtain ⟨Z, p, hZ, hZp⟩ := (hpt v).1 hp
          obtain ⟨Z', hZ', hZ'p⟩ := hptW hZ hZp
          have h1 : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
                ∃ p : Q.chain.model ⟨i, none⟩, IsClosed ({p} : Set (Q.chain.model ⟨i, none⟩)) ∧
                  (Z : Set (Q.chain.model ⟨i, none⟩)) = {p} :=
            ⟨Z, hZ, p, hZp ▸ Z.isClosed, hZp⟩
          have h2 : ∃ Z : IrreducibleCloseds (Q.chain.model y.1),
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) (Ψ v) Z ∧
                ∃ p : Q.chain.model y.1, IsClosed ({p} : Set (Q.chain.model y.1)) ∧
                  (Z : Set (Q.chain.model y.1)) = {p} :=
            ⟨Z', hZ', _, hZ'p ▸ Z'.isClosed, hZ'p⟩
          rw [if_pos h1, if_pos h2, if_pos hp, isValuationWeight_unique Q (hwD v h1) (hw v hvF),
            isValuationWeight_unique Q (hwD' (Ψ v) h2) (hw'' v hvF)]
        · rw [if_neg, if_neg, if_neg hp, sub_zero]
          · rintro ⟨Z', hZ', p', -, hZ'p⟩
            obtain ⟨Z, hZ, hZp⟩ := hptV hZ' hZ'p
            exact hp ((hpt v).2 ⟨Z, _, hΦΨ v ▸ hZ, hZp⟩)
          · rintro ⟨Z, hZ, p, -, hZp⟩
            exact hp ((hpt v).2 ⟨Z, p, hZ, hZp⟩)
      · rintro v' hv' hne
        obtain ⟨Z', hZ', p', -, hZ'p⟩ := id hv'
        obtain ⟨Z, hZ, hZp⟩ := hptV hZ' hZ'p
        exact Finset.mem_image.2 ⟨Φ v', hmem𝔉.2 ((hF _).2 ⟨(hwt v' _ (hwD' v' hv')).1,
          Or.inl ((hpt _).2 ⟨Z, _, hZ, hZp⟩),
          Or.inr ⟨wD' v', by rw [hΨΦ]; exact hwD' v' hv', hne⟩⟩), hΨΦ v'⟩
      · rintro v hv hne
        obtain ⟨Z, hZ, p, -, hZp⟩ := id hv
        exact hmem𝔉.2 ((hF v).2 ⟨(hwD v hv).1, Or.inl ((hpt v).2 ⟨Z, p, hZ, hZp⟩),
          Or.inl ⟨wD v, hwD v hv, hne⟩⟩)
    -- the brackets
    have hbr : ∑ᶠ γ, β γ - ∑ᶠ γ', β' γ' =
        ∑ γ ∈ h𝓔.toFinset, ∑ v ∈ 𝔉, if cen γ v then ((w v : ℤ) - w' v) else 0 := by
      have hkey : ∀ γ, β γ - β' (Ψc.symm γ) =
          if γ ∈ 𝓔 then ∑ v ∈ 𝔉, (if cen γ v then ((w v : ℤ) - w' v) else 0) else 0 := by
        intro γ
        obtain ⟨wβ, r, dβ, hwβ, hr, hdβ, hβeq⟩ := hβ γ
        obtain ⟨wβ', r', dβ', hwβ', hr', hdβ', hβeq'⟩ := hβ' (Ψc.symm γ)
        have hclos : closure {γ.point} = φ.hom.base '' closure {(Ψc.symm γ).point} := by
          change _ = φ.hom.base '' closure {(properCurveMap φ.symm hs' γ).point}
          rw [closure_properCurveMap_point, Set.image_image]
          change _ = (fun x => φ.hom (φ.inv x)) '' _
          simp_rw [Scheme.inv_hom_apply, Set.image_id']
        have hrd : (∑ᶠ S, r S * dβ S : ℕ) = ∑ᶠ S, r' S * dβ' S := by
          refine finsum_congr fun S => ?_
          rw [hdx S (hdβ S), hdy S (hdβ' S)]
          congr 1
          obtain ⟨P, hP, hrP⟩ := hr S
          obtain ⟨P', hP', hrP'⟩ := hr' S
          obtain rfl := hcenx S (hc S P' hP') hP
          rw [hrP, hrP', hclos, branchNumber_primeDivisorEquivOfIso]
        rw [hβeq, hβeq', hrd, sub_sub_sub_cancel_right]
        split_ifs with hγ
        · rw [natCast_finsum_eq_sum 𝔉 ?_, natCast_finsum_eq_sum (𝔉.image Ψ) ?_,
            Finset.sum_image (fun a _ b _ h => hΨinj h), ← Finset.sum_sub_distrib]
          · refine Finset.sum_congr rfl fun v hv => ?_
            have hvF := hmem𝔉.1 hv
            by_cases hcv : cen γ v
            · obtain ⟨Z, hZ, hZγ⟩ := (hcen γ v).1 hcv
              obtain ⟨Z', hZ', hZ'γ⟩ := hcenW hZ hZγ
              rw [if_pos ⟨Z, hZ, hZγ⟩, if_pos ⟨Z', hZ', hZ'γ⟩, if_pos hcv,
                isValuationWeight_unique Q (hwβ v ⟨Z, hZ, hZγ⟩) (hw v hvF),
                isValuationWeight_unique Q (hwβ' (Ψ v) ⟨Z', hZ', hZ'γ⟩) (hw'' v hvF)]
            · rw [if_neg (fun h => hcv ((hcen γ v).2 h)), if_neg, if_neg hcv, sub_zero]
              rintro ⟨Z', hZ', hZ'γ⟩
              obtain ⟨Z, hZ, hZγ⟩ := hcenV hZ' hZ'γ
              rw [hΦΨ] at hZ
              rw [Equiv.apply_symm_apply] at hZγ
              exact hcv ((hcen γ v).2 ⟨Z, hZ, hZγ⟩)
          · rintro v' hv' hne
            obtain ⟨Z', hZ', hZ'γ⟩ := id hv'
            obtain ⟨Z, hZ, hZγ⟩ := hcenV hZ' hZ'γ
            rw [Equiv.apply_symm_apply] at hZγ
            exact Finset.mem_image.2 ⟨Φ v', hmem𝔉.2 ((hF _).2 ⟨(hwt v' _ (hwβ' v' hv')).1,
              Or.inr ⟨γ, hγ, (hcen _ _).2 ⟨Z, hZ, hZγ⟩⟩,
              Or.inr ⟨wβ' v', by rw [hΨΦ]; exact hwβ' v' hv', hne⟩⟩), hΨΦ v'⟩
          · rintro v hv hne
            exact hmem𝔉.2 ((hF v).2 ⟨(hwβ v hv).1, Or.inr ⟨γ, hγ, (hcen γ v).2 hv⟩,
              Or.inl ⟨wβ v, hwβ v hv, hne⟩⟩)
        · rw [finsum_eq_finsum_comp_of_injective (f := wβ') (R := fun v =>
              ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
                MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
                  (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point}) hΨinj ?_, sub_eq_zero]
          · congr 1
            refine finsum_congr fun v => finsum_congr fun hv => ?_
            obtain ⟨Z, hZ, hZγ⟩ := hv
            obtain ⟨Z', hZ', hZ'γ⟩ := hcenW hZ hZγ
            have h1 := hwt (Ψ v) _ (hwβ' (Ψ v) ⟨Z', hZ', hZ'γ⟩)
            rw [hΦΨ] at h1
            exact (hE γ hγ v ⟨Z, hZ, hZγ⟩ _ _ (hwβ v ⟨Z, hZ, hZγ⟩) h1).symm
          · intro v'
            constructor
            · rintro ⟨Z', hZ', hZ'γ⟩
              obtain ⟨Z, hZ, hZγ⟩ := hcenV hZ' hZ'γ
              rw [Equiv.apply_symm_apply] at hZγ
              exact ⟨Φ v', ⟨Z, hZ, hZγ⟩, hΨΦ v'⟩
            · rintro ⟨v, ⟨Z, hZ, hZγ⟩, rfl⟩
              exact hcenW hZ hZγ
      have hfin1 : (Function.support β).Finite :=
        (Q.finite_setOf_isCurveBracket_ne_zero ⟨⟨i, none⟩, hi⟩).1.subset
          fun γ hγ => ⟨β γ, hβ γ, hγ⟩
      have hfin2 : (Function.support fun γ => β' (Ψc.symm γ)).Finite :=
        ((Q.finite_setOf_isCurveBracket_ne_zero y).1.image Ψc).subset
          fun γ hγ => ⟨Ψc.symm γ, ⟨β' _, hβ' _, hγ⟩, Ψc.apply_symm_apply γ⟩
      rw [← finsum_comp_equiv Ψc.symm, ← finsum_sub_distrib hfin1 hfin2,
        finsum_eq_sum_of_support_subset _ (s := h𝓔.toFinset) ?_]
      · refine Finset.sum_congr rfl fun γ hγ => ?_
        rw [hkey γ, if_pos (h𝓔.mem_toFinset.1 hγ)]
      · intro γ hγ
        rw [h𝓔.coe_toFinset]
        by_contra hγ𝓔
        exact hγ ((hkey γ).trans (if_neg hγ𝓔))
    -- every valuation of `F` has exactly one centre among the points and the curves of `𝓔`
    have hdec : ∀ v ∈ 𝔉, ((w v : ℤ) - w' v) = (if pt v then ((w v : ℤ) - w' v) else 0) +
        ∑ γ ∈ h𝓔.toFinset, if cen γ v then ((w v : ℤ) - w' v) else 0 := by
      intro v hv
      obtain ⟨-, hc, -⟩ := (hF v).1 (hmem𝔉.1 hv)
      exact eq_ite_add_sum_ite_of_isCentre hvarW (hpt v).1 (fun γ => (hcen γ v).1)
        (hc.imp_right fun ⟨γ, hγ, h⟩ => ⟨γ, h𝓔.mem_toFinset.2 hγ, h⟩) _
    rw [finsum_mem_eq_finite_toFinset_sum _ hFfin, ← h𝔉, Finset.sum_congr rfl hdec,
      Finset.sum_add_distrib, Finset.sum_comm (s := 𝔉)]
    linear_combination hpts + hbr + hlab

/-- Along a bridge with no step, the decreased pair `(Y_i, Θ_i')` is identified with the next
junction `(Y_{i+1}, Θ_{i+1})` by the identification `φ⁻¹` of the end of the bridge. -/
private theorem decreased_of_m_eq_zero {T : StabilizedTail} (C : StabilizedTail.TerminalChain T)
    (i : ℕ) (h : (C.bridge i).P.m = 0) (φ : (C.junction (i + 1)).Y ≅ (C.junction i).Y)
    (hφ : φ.hom = (C.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) h)) :
    (C.bridge i).Θ' = inverseTransformDivisor φ.inv (C.junction (i + 1)).Θ ∧
      (C.junction i).p ≫ T.f i = φ.inv ≫ (C.junction (i + 1)).p ≫ T.fp i := by
  have key : ∀ (m : ℕ) (hm : m = 0)
      (e : modelSeq (C.junction i).Y (C.bridge i).P.Y m ≅ (C.junction (i + 1)).Y)
      (φ : (C.junction (i + 1)).Y ≅ (C.junction i).Y),
      φ.hom = e.inv ≫ eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm) →
      (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
      modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY m =
        e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i →
      (C.bridge i).Θ' = inverseTransformDivisor φ.inv (C.junction (i + 1)).Θ ∧
        (C.junction i).p ≫ T.f i = φ.inv ≫ (C.junction (i + 1)).p ≫ T.fp i := by
    rintro m rfl e φ hφ hb hπ
    let e' : (C.junction i).Y ≅ (C.junction (i + 1)).Y := e
    obtain rfl : φ = e'.symm := Iso.ext (by rwa [eqToHom_refl, Category.comp_id] at hφ)
    exact ⟨hb, hπ⟩
  exact key _ h (C.bridge i).e φ hφ (C.bridge i).boundary_eq (C.bridge i).modelMap_eq

/-- The transport data of a coefficient-decrease move along a bridge with no step. -/
private theorem transport_of_m_eq_zero {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) (h : (Q.chain.bridge i).P.m = 0)
    (φ : (Q.chain.junction (i + 1)).Y ≅ (Q.chain.junction i).Y)
    (hφ : φ.hom = (Q.chain.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h)) :
    φ.hom ≫ ((Q.chain.junction i).p ≫ T.sX i) = (Q.chain.junction (i + 1)).p ≫ T.sX (i + 1) ∧
      (∀ Γ : MMP.Mori.PrimeDivisor (Q.chain.junction (i + 1)).Y,
        (Q.chain.junction (i + 1)).Θ.coeff Γ =
          (Q.chain.bridge i).Θ'.coeff (primeDivisorEquivOfIso φ Γ)) ∧
      ∀ S (P : MMP.Mori.PrimeDivisor (Q.chain.junction (i + 1)).Y),
        Q.chain.IsLabelCentre S ⟨i + 1, none⟩ P →
          Q.chain.IsLabelCentre S ⟨i, none⟩ (primeDivisorEquivOfIso φ P) := by
  obtain ⟨hΘ, hπ⟩ := decreased_of_m_eq_zero Q.chain i h φ hφ
  obtain ⟨-, -, -, -, ⟨c, -, hcc, -, -⟩, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  obtain ⟨hΘ1, -, -, -, -, -⟩ := Q.echoSetting_model ⟨⟨i + 1, none⟩, Nat.le_succ_of_le hi⟩
  have hnv1 : IsNormalVariety ℂ ((Q.chain.junction (i + 1)).p ≫ T.sX (i + 1)) :=
    hΘ1.1.1.isPair.1
  refine ⟨?_, fun Γ => ?_, fun S P hP => ?_⟩
  · have h1 := congrArg (· ≫ T.sZ i) hπ
    simp only [Category.assoc] at h1
    rw [(T.isThreefoldStepDiagram i).comp_eq_minus,
      (T.isThreefoldStepDiagram i).comp_eq_plus] at h1
    rw [h1, Iso.hom_inv_id_assoc]
  · exact ((congrArg (fun D => D.coeff (primeDivisorEquivOfIso φ Γ)) hΘ).trans
      ((coeff_inverseTransformDivisor_iso φ.symm _ _).trans
        (congrArg _ (primeDivisorEquivOfIso_symm_apply_apply φ Γ)))).symm
  · have h2 : P = primeDivisorEquivOfIso φ.symm (c S) :=
      eq_of_isLabelCentre_none Q.chain hnv1 hP
        (isLabelCentre_succ_of_iso Q.chain φ.symm hπ (hcc S))
    have h3 : primeDivisorEquivOfIso φ (primeDivisorEquivOfIso φ.symm (c S)) = c S :=
      (primeDivisorEquivOfIso φ.symm).left_inv (c S)
    rw [h2, h3]
    exact hcc S

end Helpers

/-- **The difficulty change under a coefficient decrease.** Let `i ≥ i₀` index a junction
`(Y_i, Θ_i)` of a prepared chain, and let the model `y` with the identification `φ : Y_y ≅ Y_i`
be its decreased pair `(Y_i, Θ_i')`: the model `(i, some 0)` with `φ` the identity when
`0 < m_i`, and the next junction `(i + 1, none)` with `φ` induced by the inverse of the
identification `e : V_{m_i} ≅ Y_{i+1}` of the bridge when `m_i = 0`. There is a finite set `F`
of valuations of `ℂ(Y_i)` exceptional over `Y_i` such that every weight
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`) of a valuation `v ∉ F` for
`Θ_i` equals every weight of `v` for `Θ_i'`, and for difficulties `D = 𝒟(Y_i, Θ_i)` and
`D' = 𝒟(Y_i, Θ_i')` (`MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`) and weights
`w v = w_v(Y_i, Θ_i)`, `w' v = w_v(Y_i, Θ_i')` on `F`,
`D - D' = ∑_{v ∈ F} (w v - w' v)`. -/
@[mmp "lem_mmp_indexd_coefficient_move_difference"]
public theorem exists_finite_isDifficulty_sub_eq_finsum {T : StabilizedTail}
    (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i) (y : Q.ModelIndex)
    (φ : Q.chain.model y.1 ≅ Q.chain.model ⟨i, none⟩)
    (hφ : (∃ (h : 0 < (Q.chain.bridge i).P.m) (hy : y.1 = ⟨i, some ⟨0, h⟩⟩),
        φ.hom = eqToHom ((congrArg Q.chain.model hy).trans
          (rfl : Q.chain.model ⟨i, some ⟨0, h⟩⟩ = Q.chain.model ⟨i, none⟩))) ∨
      (∃ (h : (Q.chain.bridge i).P.m = 0) (hy : y.1 = ⟨i + 1, none⟩),
        φ.hom = eqToHom (congrArg Q.chain.model hy) ≫ (Q.chain.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h))) :
    ∃ F : Set (Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ))),
      F.Finite ∧
      (∀ v ∈ F, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v) ∧
      (∀ v ∉ F, ∀ v' : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap φ.hom) = v →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
          Q.chain.IsValuationWeight Q.scale y.1 v' w' → w = w') ∧
      ∀ (D D' : ℤ), Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D → Q.IsDifficulty y D' →
        ∀ w w' : Valuation (Q.chain.model ⟨i, none⟩).functionField
            (WithZero (Multiplicative ℤ)) → ℕ,
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) →
          (∀ v ∈ F, ∀ v' : Valuation (Q.chain.model y.1).functionField
              (WithZero (Multiplicative ℤ)),
            v'.comap (functionFieldMap φ.hom) = v →
              Q.chain.IsValuationWeight Q.scale y.1 v' (w' v)) →
          D - D' = ∑ᶠ (v) (_ : v ∈ F), ((w v : ℤ) - w' v) := by
  obtain ⟨hΘx, -, -, -, ⟨c, -, hcc, -, -⟩, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  have hnvW : IsNormalVariety ℂ ((Q.chain.junction i).p ≫ T.sX i) := hΘx.1.1.isPair.1
  have hpair : MMP.Mori.IsPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ' :=
    (Q.chain.bridge i).P.isKltPair.1.isPair
  rcases hφ with ⟨h, hy, hφeq⟩ | ⟨h, hy, hφeq⟩
  · obtain ⟨p, hφ'⟩ : ∃ p : Q.chain.model y.1 = Q.chain.model ⟨i, none⟩, φ.hom = eqToHom p :=
      ⟨_, hφeq⟩
    clear hφeq
    obtain ⟨y, hy0⟩ := y
    change y = _ at hy
    subst hy
    have hφ1 : φ.hom = 𝟙 (Q.chain.junction i).Y := hφ'.trans (eqToHom_refl _ _)
    have hφid : ∀ x, φ.hom x = x := fun x => (congrArg (fun f => f.base x) hφ1).trans rfl
    have hequiv : ∀ Γ, primeDivisorEquivOfIso φ Γ = Γ := fun Γ =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((OpenWeilRestriction.genericPoint_primeDivisorMap φ.hom Γ).trans (hφid _))
    refine exists_finite_isDifficulty_sub_eq_finsum_of_iso Q hi ⟨_, hy0⟩ φ ?_
      (fun Γ => by rw [hequiv]; rfl) hpair fun S P hP => ?_
    · exact (congrArg (· ≫ Q.chain.modelStructure ⟨i, none⟩) hφ1).trans (Category.id_comp _)
    · rw [hequiv, eq_of_isLabelCentre_some_zero Q.chain h hnvW hP
        (isLabelCentre_some_zero Q.chain h (hcc S))]
      exact hcc S
  · obtain ⟨p, hφ'⟩ : ∃ p : Q.chain.model y.1 = Q.chain.model ⟨i + 1, none⟩,
        φ.hom = eqToHom p ≫ (Q.chain.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h) :=
      ⟨_, hφeq⟩
    clear hφeq
    obtain ⟨y, hy0⟩ := y
    change y = _ at hy
    subst hy
    rw [eqToHom_refl, Category.id_comp] at hφ'
    obtain ⟨hs, hB, hc⟩ := transport_of_m_eq_zero Q hi h φ hφ'
    exact exists_finite_isDifficulty_sub_eq_finsum_of_iso Q hi ⟨_, hy0⟩ φ hs hB hpair hc

end MMP.Fourfold.StabilizedTail.PreparedChain

end
