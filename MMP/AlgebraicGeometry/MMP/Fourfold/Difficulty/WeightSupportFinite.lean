module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.Singularities.TerminalThreefoldEchoCentres
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison

/-!
# Weighted valuations with a curve or point centre on a prepared chain

Let `(Y, Θ)` be a model of a prepared chain. A valuation `v` of `ℂ(Y)` with nonzero weight
`w_v = w(2 - a(v; Y, Θ))` has `a(v; Y, Θ) < 2`, since the weight of a nonpositive number is zero.
A model is a terminal pair on a projective `ℚ`-factorial complex threefold, so only finitely many
normalized divisorial valuations whose centre is a fixed irreducible closed curve, or a closed
point, have nonzero weight. This makes the sums of the bracket
`MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket` genuinely finite.

For a coefficient-decrease move `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` of the chain, both pairs are terminal
pairs on the same threefold, supported on the label centres `S_h`, with coefficients `b_h` and
`b_h'` in `[0, 1)`. Off finitely many curves, every valuation `v` with centre a curve `C` and
positive weight for one of the two pairs is an echo of order `j ≥ 1` of the unique label `S_h`
through `C`, so `a(v; Y_i, Θ_i) = 1 + j(1 - b_h)` and `a(v; Y_i, Θ_i') = 1 + j(1 - b_h')`. The
defaults `d(b_h) = ∑_{j ≥ 1} w(1 - j(1 - b_h))` and `d(b_h')` agree, since defaults are constant
on a prepared chain; the summands are monotone in the coefficient, so they agree term by term,
and the two weights of `v` are equal.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.finite_setOf_isCentre_closure`: finitely many
  valuations centred at a fixed curve have nonzero weight.
* `MMP.Fourfold.StabilizedTail.PreparedChain.finite_setOf_isCentre_singleton`: finitely many
  valuations centred at a closed point have nonzero weight.
* `MMP.Fourfold.StabilizedTail.PreparedChain.exists_finite_isValuationWeight_eq`: off a finite
  set of curves, a coefficient-decrease move leaves the weights of curve-centred valuations
  unchanged.

## Implementation notes

* An irreducible closed curve of the projective variety `Y` is recorded as a proper curve
  `MMP.Mori.ProperCurve` by its generic point `γ.point`, and `v` has centre `C` when
  `MMP.Intersection.IsCentre` holds for an irreducible closed set equal to `closure {γ.point}`;
  "`v` has a closed point as centre" reads: the centre is an irreducible closed set equal to a
  singleton `{y}`. `MMP.Intersection.IsCentre` already makes `v` a normalized divisorial
  valuation.
* The weight is the predicate `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight` at
  the fixed admissible scale of the prepared chain; "`w_v ≠ 0`" reads: `v` has some weight
  `w ≠ 0`. Only valuations exceptional over `Y` carry a weight.
* The coefficient-decrease move at the junction `i` goes from `(Y_i, Θ_i)` to `(Y_i, Θ_i')`, with
  `Θ_i'` the decreased boundary of the `i`-th terminal bridge. When the bridge has a model the
  pair `(Y_i, Θ_i')` is the model `(i, some 0)` of the chain; when it has none, it is the end of
  the bridge, identified with the next junction by the isomorphism of the bridge. The statement
  is made on `(Y_i, Θ_i')` itself, so it covers both moves. The weight of `v` for `Θ_i'` is
  spelled out as the body of `IsValuationWeight` with boundary `Θ_i'`, and
  "`w_v(Y, Θ') = w_v(Y, Θ)`" reads: any weight of `v` for `Θ_i'` equals any weight for `Θ_i`.
* The source compares the two pairs through the monotonicity of weights along moves. Here the
  comparison is symmetric: a valuation of positive weight for either pair is an echo, and its
  log discrepancies for both pairs are given by the echo formula, so no inequality between the
  coefficients is needed; equality of the defaults alone forces the weights of every order `j`
  to agree.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

namespace MMP.Fourfold.StabilizedTail.PreparedChain

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

/-- **Finitely many weighted valuations at a curve.** On a model `(Y, Θ)` of a prepared chain,
for an irreducible closed curve `C ⊆ Y` with generic point `γ.point`, the normalized divisorial
valuations `v` of `ℂ(Y)` with centre `C` whose weight `w_v`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`, at the fixed admissible scale) is
nonzero form a finite set. -/
@[mmp "lem_mmp_indexd_curve_support_finite"]
public theorem finite_setOf_isCentre_closure {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1)) :
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) |
      (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
            (Z : Set (Q.chain.model x.1)) = closure {γ.point}) ∧
        ∃ w : ℕ, Q.chain.IsValuationWeight Q.scale x.1 v w ∧ w ≠ 0}.Finite := by
  obtain ⟨hΘ, hY, hQ, hdim, -⟩ := Q.echoSetting_model x
  let V : IrreducibleCloseds (Q.chain.model x.1) :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  refine (MMP.Fourfold.finite_setOf_isCentre _ hY hQ hdim hΘ
    (L := (Q.chain.modelBoundary x.1).support) subset_rfl V
    (topologicalKrullDim_closure_point γ)).subset ?_
  rintro v ⟨⟨Z, hc, hZ⟩, w, ⟨-, a, ⟨n, D, -, hDv, hD⟩, rfl⟩, hw⟩
  obtain rfl : Z = V := IrreducibleCloseds.ext hZ
  exact ⟨hc, a, lt_of_not_ge fun ha =>
    hw (MMP.Fourfold.difficultyWeight_of_nonpos (sub_nonpos.mpr ha)), n, D, hDv, hD⟩

/-- **Finitely many weighted point valuations.** On a model `(Y, Θ)` of a prepared chain, the
normalized divisorial valuations `v` of `ℂ(Y)` whose centre on `Y` is a closed point and whose
weight `w_v` (`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`, at the fixed
admissible scale) is nonzero form a finite set. -/
@[mmp "lem_mmp_indexd_point_support_finite"]
public theorem finite_setOf_isCentre_singleton {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) :
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) |
      (∃ (Z : IrreducibleCloseds (Q.chain.model x.1)) (y : Q.chain.model x.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
            (Z : Set (Q.chain.model x.1)) = {y}) ∧
        ∃ w : ℕ, Q.chain.IsValuationWeight Q.scale x.1 v w ∧ w ≠ 0}.Finite := by
  obtain ⟨hΘ, hY, hQ, hdim, -⟩ := Q.echoSetting_model x
  refine (MMP.Fourfold.finite_setOf_isCentre_singleton _ hY hQ hdim hΘ
    (L := (Q.chain.modelBoundary x.1).support) subset_rfl).subset ?_
  rintro v ⟨hc, w, ⟨-, a, ⟨n, D, -, hDv, hD⟩, rfl⟩, hw⟩
  exact ⟨hc, a, lt_of_not_ge fun ha ↦ hw (MMP.Fourfold.difficultyWeight_of_nonpos
    (sub_nonpos.2 ha)), n, D, hDv, hD⟩

/-! ### Weights of the orders of a default -/

/-- If the defaults `d(b)` and `d(b')` agree, for `b, b' < 1`, then so do the weights
`w(1 - j(1 - b))` and `w(1 - j(1 - b'))` of every order `j ≥ 1`. -/
private theorem difficultyWeight_eq_of_defaultWeight_eq {N : ℕ} {b b' : ℝ} (hb : b < 1)
    (hb' : b' < 1) (hd : defaultWeight N b = defaultWeight N b') {j : ℕ} (hj : 1 ≤ j) :
    difficultyWeight N (1 - j * (1 - b)) = difficultyWeight N (1 - j * (1 - b')) := by
  wlog hle : b' ≤ b generalizing b b'
  · exact (this hb' hb hd.symm (le_of_not_ge hle)).symm
  have hfin := (finite_support_difficultyWeight N hb).union (finite_support_difficultyWeight N hb')
  set s := hfin.toFinset
  let F : ℝ → ℕ → ℕ := fun c j => if 1 ≤ j then difficultyWeight N (1 - j * (1 - c)) else 0
  have key : ∀ c, (Function.support fun j : ℕ => difficultyWeight N (1 - j * (1 - c))) ⊆ s →
      defaultWeight N c = ∑ j ∈ s, F c j := by
    intro c hc
    rw [defaultWeight, finsum_eq_sum_of_support_subset _ (s := s) ?_]
    · exact Finset.sum_congr rfl fun j _ => finsum_eq_if
    · intro j hj
      rw [Function.mem_support, finsum_eq_if] at hj
      split_ifs at hj with h1
      · exact hc hj
      · exact absurd rfl hj
  have h1 := key b (by rw [hfin.coe_toFinset]; exact Set.subset_union_left)
  have h2 := key b' (by rw [hfin.coe_toFinset]; exact Set.subset_union_right)
  have hle' : ∀ j ∈ s, F b' j ≤ F b j := fun j _ => by
    simp only [F]
    split_ifs
    · exact difficultyWeight_mono N
        (sub_le_sub_left (mul_le_mul_of_nonneg_left (by linarith) j.cast_nonneg) 1)
    · exact le_rfl
  have heq := (Finset.sum_eq_sum_iff_of_le hle').mp (by rw [← h1, ← h2, hd])
  by_cases hj' : j ∈ s
  · have := heq j hj'
    simp only [F, if_pos hj] at this
    exact this.symm
  · have : j ∉ (Function.support fun j : ℕ => difficultyWeight N (1 - j * (1 - b))) ∪
        (Function.support fun j : ℕ => difficultyWeight N (1 - j * (1 - b'))) :=
      fun h => hj' (hfin.mem_toFinset.mpr h)
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at this
    rw [this.1, this.2]

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
  · subst hg; simp
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
    exact comap_injective_of_surjective
      ((T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
        |>.functionFieldMap_bijective.2) (huw.trans huw'.symm)

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

/-- When the `i`-th bridge has no step, its end identifies the decreased pair `(Y_i, Θ_i')` with
the next junction `(Y_{i+1}, Θ_{i+1})`. -/
private theorem exists_iso_of_m_eq_zero {i : ℕ} (hm : (C.bridge i).P.m = 0) :
    ∃ e : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
      (C.bridge i).Θ' = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ ∧
      (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
  have key : ∀ (m : ℕ) (e : modelSeq (C.junction i).Y (C.bridge i).P.Y m ≅ (C.junction (i + 1)).Y),
      (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
      modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY m =
        e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i → m = 0 →
      ∃ e : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
        (C.bridge i).Θ' = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ ∧
        (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
    rintro m e hb hπ rfl
    exact ⟨e, hb, hπ⟩
  exact key _ (C.bridge i).e (C.bridge i).boundary_eq (C.bridge i).modelMap_eq hm

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
    ⟨hW, hpφ, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, M, hCc, hdec, fun i => ⟨_,
      MMP.Fourfold.Oai4C1.TwoEnds.divisor_isPullback_comp (hL i) (hM i) (fun Z =>
      MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ φ.hom) (C i) Z)⟩, rfl⟩
  have e1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha' h1
    (hv.trans (valuation_compOpen φ.hom rfl D).symm)
  -- the same data, pulled back to `V`
  have hne : pullbackRationalPluriForms sW φ.hom ω ≠ 0 :=
    MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero φ.hom hbij hd hω
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

/-- A divisor over a normal variety is exceptional exactly when the image of the generic point of
its divisor has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hX
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- `(Y, f ≫ e, E)` is exceptional over `W` when `(Y, f, E)` is exceptional over `V`, for an
isomorphism `e : V ≅ W`. -/
private theorem isExceptional_compOpen (e : V ≅ W) {sW : W ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) (hV : IsNormalVariety ℂ sV)
    (hW : IsNormalVariety ℂ sW) {D : DivisorOver ℂ sV} (hD : D.IsExceptional) :
    (compOpen e.hom hs D).IsExceptional := by
  rw [isExceptional_iff_two_le_coheight hW]
  rw [isExceptional_iff_two_le_coheight hV] at hD
  change 2 ≤ Order.coheight ((D.f ≫ e.hom) D.E.genericPoint)
  rwa [Scheme.Hom.comp_apply, Topology.IsOpenEmbedding.coheight_eq _ e.hom.isOpenEmbedding]

/-- **Terminality is invariant under isomorphisms of pairs.** -/
private theorem isKltTerminalPair_of_iso [CompactSpace V] (e : V ≅ W) {sW : W ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) {B : QDivisor V} {B' : QDivisor W}
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor V, B.coeff Γ = B'.coeff (primeDivisorEquivOfIso e Γ))
    (hklt : IsKltPair sV B) (hB' : IsKltTerminalPair sW B') : IsKltTerminalPair sV B := by
  refine ⟨hklt, fun n D a hD ha => ?_⟩
  have hV : IsNormalVariety ℂ sV := hklt.1.isPair.1
  have hW : IsNormalVariety ℂ sW := hB'.1.1.isPair.1
  obtain ⟨-, n₀, K, hK, -⟩ := hB'.1.1.isPair
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp : IsProper D.f := ha.2.1
  have hp' : IsProper (compOpen e.hom hs D).f := by
    change IsProper (D.f ≫ e.hom)
    infer_instance
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB'.1.1.isPair hK
    (compOpen e.hom hs D)
  have ha' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp'
  rw [eq_of_isLogDiscrepancy_of_iso e hs hB ha ha' (valuation_compOpen e.hom hs D)]
  exact hB'.2 n₀ _ _ (isExceptional_compOpen e hs hV hW hD) ha'

end IsoTransport

/-! ### The decreased pair -/

/-- The decreased pair `(Y_i, Θ_i')` of a prepared chain, `i ≥ i₀`, is terminal, supported on
the label centres `c S` of the junction `Y_i`, with coefficients in `[0, 1)` there, and every
default `d(b_h)` of the junction agrees with `d(b_h')` of the decreased pair. -/
private theorem echoSetting_decreased {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i)
    (c : Q.chain.Label → MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩))
    (hc : ∀ S, Q.chain.IsLabelCentre S ⟨i, none⟩ (c S)) :
    IsKltTerminalPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ' ∧
      (∀ P, (Q.chain.bridge i).Θ'.coeff P ≠ 0 → P ∈ Set.range c) ∧
      ∀ S, 0 ≤ (Q.chain.bridge i).Θ'.coeff (c S) ∧ (Q.chain.bridge i).Θ'.coeff (c S) < 1 ∧
        defaultWeight Q.scale ((Q.chain.modelBoundary ⟨i, none⟩).coeff (c S) : ℝ) =
          defaultWeight Q.scale ((Q.chain.bridge i).Θ'.coeff (c S) : ℝ) := by
  classical
  obtain ⟨hΘ, -, -, -, -, -⟩ := StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i, none⟩, hi⟩
  have hX : IsNormalVariety ℂ ((Q.chain.junction i).p ≫ T.sX i) := hΘ.1.1.isPair.1
  have hd0 : ∀ S d, Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ d →
      d = defaultWeight Q.scale ((Q.chain.modelBoundary ⟨i, none⟩).coeff (c S) : ℝ) := by
    rintro S d ⟨b, ⟨P, hP, rfl⟩, rfl⟩
    rw [eq_of_isLabelCentre_none Q.chain hX hP (hc S)]
  by_cases hm : 0 < (Q.chain.bridge i).P.m
  · obtain ⟨hΘy, -, -, -, ⟨c', -, hc'c, hc'supp, hc'coeff⟩, -⟩ :=
      StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i, some ⟨0, hm⟩⟩, hi⟩
    have hcc' : ∀ S, c' S = c S := fun S =>
      eq_of_isLabelCentre_some_zero Q.chain hm hX (hc'c S)
        (isLabelCentre_some_zero Q.chain hm (hc S))
    refine ⟨hΘy, fun P hP => ?_, fun S => ?_⟩
    · obtain ⟨S, hS⟩ := hc'supp P hP
      exact ⟨S, (hcc' S).symm.trans hS⟩
    · obtain ⟨h0, h1⟩ := hc'coeff S
      rw [hcc' S] at h0 h1
      refine ⟨h0, h1, ?_⟩
      obtain ⟨d, hd⟩ := Q.isLabelDefault_const S
      rw [← hd0 S d (hd ⟨i, none⟩ hi)]
      obtain ⟨b, ⟨P, hP, rfl⟩, rfl⟩ := hd ⟨i, some ⟨0, hm⟩⟩ hi
      rw [eq_of_isLabelCentre_some_zero Q.chain hm hX hP
        (isLabelCentre_some_zero Q.chain hm (hc S))]
      rfl
  · have hm0 : (Q.chain.bridge i).P.m = 0 := by omega
    obtain ⟨e, hΘe, hπ⟩ := exists_iso_of_m_eq_zero Q.chain hm0
    obtain ⟨hΘ1, -, -, -, ⟨c1, -, hc1c, hc1supp, hc1coeff⟩, -⟩ :=
      StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i + 1, none⟩, Nat.le_succ_of_le hi⟩
    have hX1 : IsNormalVariety ℂ ((Q.chain.junction (i + 1)).p ≫ T.sX (i + 1)) :=
      hΘ1.1.1.isPair.1
    have hs : e.hom ≫ (Q.chain.junction (i + 1)).p ≫ T.sX (i + 1) =
        (Q.chain.junction i).p ≫ T.sX i := by
      have h1 := congrArg (· ≫ T.sZ i) hπ
      simp only [Category.assoc] at h1
      rw [(T.isThreefoldStepDiagram i).comp_eq_minus,
        (T.isThreefoldStepDiagram i).comp_eq_plus] at h1
      exact h1.symm
    have hcoeff : ∀ P, (Q.chain.bridge i).Θ'.coeff P =
        (Q.chain.junction (i + 1)).Θ.coeff (primeDivisorEquivOfIso e P) := fun P => by
      rw [hΘe]
      exact coeff_inverseTransformDivisor_iso e _ P
    have hc1 : ∀ S, primeDivisorEquivOfIso e (c S) = c1 S := fun S =>
      eq_of_isLabelCentre_none Q.chain hX1 (isLabelCentre_succ_of_iso Q.chain e hπ (hc S)) (hc1c S)
    refine ⟨isKltTerminalPair_of_iso e hs hcoeff (Q.chain.bridge i).P.isKltPair hΘ1,
      fun P hP => ?_, fun S => ?_⟩
    · rw [hcoeff] at hP
      obtain ⟨S, hS⟩ := hc1supp _ hP
      exact ⟨S, (primeDivisorEquivOfIso e).injective ((hc1 S).trans hS)⟩
    · rw [hcoeff (c S), hc1 S]
      refine ⟨(hc1coeff S).1, (hc1coeff S).2, ?_⟩
      obtain ⟨d, hd⟩ := Q.isLabelDefault_const S
      rw [← hd0 S d (hd ⟨i, none⟩ hi)]
      obtain ⟨b, ⟨P, hP, rfl⟩, rfl⟩ := hd ⟨i + 1, none⟩ (Nat.le_succ_of_le hi)
      rw [eq_of_isLabelCentre_none Q.chain hX1 hP (hc1c S)]
      rfl

/-! ### Log discrepancies of valuations -/

/-- A valuation with a log discrepancy over a proper model has that log discrepancy. -/
private theorem IsValuationLogDiscrepancy.hasLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sX B v a) : HasLogDiscrepancy sX B v a := by
  obtain ⟨n, D, -, hv, ha⟩ := h
  exact ⟨n, D, hv, ha⟩

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : HasLogDiscrepancy sX B v a) (h' : HasLogDiscrepancy sX B v a') : a = a' := by
  obtain ⟨n, D, hv, ha⟩ := h
  obtain ⟨n', D', hv', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hv.trans hv'.symm)

/-- **Weights at generic curves are unchanged by a coefficient decrease.** Let `i ≥ i₀` index a
junction `(Y_i, Θ_i)` of a prepared chain, and let `Θ_i'` be the decreased boundary of the
`i`-th bridge. There is a finite set `𝓔` of irreducible closed curves of `Y_i` such that for
every curve `C ∉ 𝓔` and every normalized divisorial valuation `v` of `ℂ(Y_i)` with centre `C`,
the weight `w(2 - a(v; Y_i, Θ_i'))` of `v` for `Θ_i'` equals its weight for `Θ_i`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`, at the fixed admissible
scale). -/
@[mmp "lem_mmp_indexd_coefficient_move_echo_unchanged"]
public theorem exists_finite_isValuationWeight_eq {T : StabilizedTail} (Q : PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) :
    ∃ 𝓔 : Set (MMP.Mori.ProperCurve (Q.chain.modelStructure ⟨i, none⟩)), 𝓔.Finite ∧
      ∀ γ ∉ 𝓔,
        ∀ v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)),
          (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
                (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point}) →
          ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
            (MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
              ∃ a : ℝ, IsValuationLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
                  (Q.chain.bridge i).Θ' v a ∧ w' = difficultyWeight Q.scale (2 - a)) →
            w' = w := by
  classical
  set Y := Q.chain.model ⟨i, none⟩
  set sY := Q.chain.modelStructure ⟨i, none⟩
  set Θ := Q.chain.modelBoundary ⟨i, none⟩
  set Θ' := (Q.chain.bridge i).Θ'
  obtain ⟨hΘ, hY, hQ, hdim, ⟨c, -, hcc, hcsupp, hccoeff⟩, -⟩ :=
    StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i, none⟩, hi⟩
  obtain ⟨hΘ', hcsupp', hccoeff'⟩ := echoSetting_decreased Q hi c hcc
  have : Finite Q.chain.Label := StabilizedTail.TerminalChain.finite_label Q.chain
  set L : Finset (MMP.Mori.PrimeDivisor Y) := (Set.finite_range c).toFinset
  have hmemL : ∀ S ∈ L, ∃ h, c h = S := fun S hS => (Set.finite_range c).mem_toFinset.mp hS
  have hsupp : Θ.support ⊆ L := fun P hP =>
    (Set.finite_range c).mem_toFinset.mpr (hcsupp P (Finsupp.mem_support_iff.mp hP))
  have hsupp' : Θ'.support ⊆ L := fun P hP =>
    (Set.finite_range c).mem_toFinset.mpr (hcsupp' P (Finsupp.mem_support_iff.mp hP))
  have hlt : ∀ S ∈ L, Θ.coeff S < 1 := fun S hS => by
    obtain ⟨h, rfl⟩ := hmemL S hS
    exact (hccoeff h).2
  have hlt' : ∀ S ∈ L, Θ'.coeff S < 1 := fun S hS => by
    obtain ⟨h, rfl⟩ := hmemL S hS
    exact (hccoeff' h).2.1
  obtain ⟨𝒮, h𝒮, -, h𝒮gen⟩ :=
    exists_finite_forall_isEcho_of_isCentre sY hY hQ hdim hΘ hsupp
  obtain ⟨𝒮', h𝒮', -, h𝒮gen'⟩ :=
    exists_finite_forall_isEcho_of_isCentre sY hY hQ hdim hΘ' hsupp'
  refine ⟨{γ | ∃ Z ∈ 𝒮 ∪ 𝒮', (Z : Set Y) = closure {γ.point}}, ?_, ?_⟩
  · refine ((h𝒮.union h𝒮').biUnion fun Z _ =>
      (?_ : Set.Subsingleton {γ : MMP.Mori.ProperCurve sY |
        (Z : Set Y) = closure {γ.point}}).finite).subset ?_
    · rintro ⟨p, hp⟩ (h : (Z : Set Y) = closure {p}) ⟨p', hp'⟩ (h' : (Z : Set Y) = closure {p'})
      obtain rfl : p = p' := (inseparable_iff_closure_eq.mpr (h.symm.trans h')).eq
      rfl
    · rintro γ ⟨Z, hZ, h⟩
      exact Set.mem_biUnion hZ h
  · rintro γ hγ v ⟨Z, hcen, hZ⟩ w w' ⟨-, a, ha, rfl⟩ ⟨-, a', ha', rfl⟩
    have hZ𝒮 : Z ∉ 𝒮 ∪ 𝒮' := fun h => hγ ⟨Z, h, hZ⟩
    have hZdim : topologicalKrullDim (Z : Set Y) = 1 := hZ ▸ topologicalKrullDim_closure_point γ
    have hla := IsValuationLogDiscrepancy.hasLogDiscrepancy ha
    have hla' := IsValuationLogDiscrepancy.hasLogDiscrepancy ha'
    -- an echo has the same weight for both boundaries
    have hecho : ∀ (S : MMP.Mori.PrimeDivisor Y) (j : ℕ), S ∈ L → 1 ≤ j →
        IsEcho sY L S Z j v →
        difficultyWeight Q.scale (2 - a') = difficultyWeight Q.scale (2 - a) := by
      intro S j hS hj he
      obtain ⟨h, rfl⟩ := hmemL S hS
      have e1 := HasLogDiscrepancy.unique hla (he.hasLogDiscrepancy hΘ.1.1 hsupp hlt)
      have e2 := HasLogDiscrepancy.unique hla' (he.hasLogDiscrepancy hΘ'.1.1 hsupp' hlt')
      have hsub : ∀ x : ℝ, (2 : ℝ) - (1 + (j : ℝ) * (1 - x)) = 1 - j * (1 - x) :=
        fun x => by ring
      rw [e1, e2, hsub, hsub]
      exact (difficultyWeight_eq_of_defaultWeight_eq
        (by exact_mod_cast (hccoeff h).2) (by exact_mod_cast (hccoeff' h).2.1)
        (hccoeff' h).2.2 hj).symm
    by_cases h2 : a < 2
    · obtain ⟨-, S, hS, -, -, j, hj, he, -⟩ :=
        h𝒮gen Z hZdim (fun h => hZ𝒮 (Or.inl h)) v hcen ⟨a, h2, hla⟩
      exact hecho S j hS hj he
    by_cases h2' : a' < 2
    · obtain ⟨-, S, hS, -, -, j, hj, he, -⟩ :=
        h𝒮gen' Z hZdim (fun h => hZ𝒮 (Or.inr h)) v hcen ⟨a', h2', hla'⟩
      exact hecho S j hS hj he
    rw [difficultyWeight_of_nonpos (by linarith), difficultyWeight_of_nonpos (by linarith)]

end MMP.Fourfold.StabilizedTail.PreparedChain

end
