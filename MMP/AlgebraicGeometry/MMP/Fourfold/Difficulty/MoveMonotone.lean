module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FlipDifference
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainWeightMonotone
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.CoefficientMove
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.DivisorOver

/-!
# Monotonicity of the difficulty along the moves of a prepared chain

Let `(Y, Θ) ⤏ (Y', Θ')` be a move of a prepared chain: a coefficient decrease
`(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` or a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge. Then the
difficulty does not increase, `𝒟(Y', Θ') ≤ 𝒟(Y, Θ)`.

For a coefficient decrease, the difference `𝒟(Y, Θ) - 𝒟(Y', Θ')` is a finite sum of weight
differences `w_v(Y_i, Θ_i) - w_v(Y_i, Θ_i')`
(`MMP.Fourfold.StabilizedTail.PreparedChain.exists_finite_isDifficulty_sub_eq_finsum`); for a
flip it is a finite sum of weight differences over the weighted bad set
(`MMP.Fourfold.StabilizedTail.PreparedChain.sub_eq_finsum_of_isDifficulty_of_flipMove`). Every
summand is nonnegative since weights do not increase along a move
(`MMP.Fourfold.StabilizedTail.PreparedChain.le_of_isValuationWeight_of_move`).

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.difficulty_le_of_move`: the difficulty does not
  increase along a move.

## Implementation notes

The models of the prepared chain are indexed by
`MMP.Fourfold.StabilizedTail.PreparedChain.ModelIndex`, and a move from the model `x` to the
model `x'` is one of three kinds:

* the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` from the junction `(i, none)` to the model
  `(i, some 0)` of the `i`-th bridge, when the bridge has at least one flip;
* the coefficient decrease of a bridge without flips, from the junction `(i, none)` to the next
  junction `(i + 1, none)`, the decreased pair being `(Y_{i+1}, Θ_{i+1})` through the
  identification `e : Y_i = V_0 ≅ Y_{i+1}` of the bridge;
* a small terminal flip move `μ` (`MMP.Fourfold.StabilizedTail.PreparedChain.FlipMove`), from
  `μ.source` to `μ.target`.

Difficulties are the predicate `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty` on their
values, so the statement compares any two values of it.
-/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedTail

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedTail.PreparedChain

variable {T : StabilizedTail}

/-! ### Valuations along an isomorphism -/

section Transport

open MMP.Fourfold.Oai4C1.CommonModel

variable {V W : Scheme.{0}} [IsIntegral V] [IsIntegral W]

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

/-- Transporting a valuation along `e` and back along `e⁻¹` gives it back. -/
private theorem comap_inv_comap_hom (e : V ≅ W)
    (v : Valuation V.functionField (WithZero (Multiplicative ℤ))) :
    (v.comap (functionFieldMap e.hom)).comap (functionFieldMap e.inv) = v := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr e.hom_inv_id,
    MMP.Mori.functionFieldMap_id_apply]

/-- A valuation transported along an isomorphism over `ℂ` is exceptional when the valuation
is. -/
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

end Transport

/-! ### Weights -/

/-- Every valuation exceptional over a model of a prepared chain has a weight there. -/
private theorem exists_isValuationWeight (Q : PreparedChain T) (x : Q.ModelIndex)
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))}
    (hv : MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure x.1) v) :
    ∃ w, Q.chain.IsValuationWeight Q.scale x.1 v w := by
  obtain ⟨hΘ, -⟩ := Q.echoSetting_model x
  have hpair := hΘ.1.1.isPair
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨D, hDp, rfl, -⟩ := id hv
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK D
  exact ⟨_, hv, _, ⟨n, D, hDp, rfl,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp⟩, rfl⟩

/-! ### Coefficient decreases -/

/-- Along a bridge with no step, the identification `Y_{i+1} ≅ Y_i` of the end of the bridge is a
morphism over `ℂ`. -/
private theorem inv_comp_modelStructure_of_m_eq_zero (C : TerminalChain T) (i : ℕ)
    (h : (C.bridge i).P.m = 0) :
    (eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) h)).inv ≫ (C.bridge i).e.hom ≫
      (C.junction (i + 1)).p ≫ T.sX (i + 1) = (C.junction i).p ≫ T.sX i := by
  have key : ∀ (m : ℕ) (hm : m = 0)
      (e : modelSeq (C.junction i).Y (C.bridge i).P.Y m ≅ (C.junction (i + 1)).Y),
      modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY m =
        e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i →
      (eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm)).inv ≫ e.hom ≫
        (C.junction (i + 1)).p ≫ T.sX (i + 1) = (C.junction i).p ≫ T.sX i := by
    rintro m rfl e hπ
    let e' : (C.junction i).Y ≅ (C.junction (i + 1)).Y := e
    have hπ' : (C.junction i).p ≫ T.f i = e'.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := hπ
    have h1 := congrArg (· ≫ T.sZ i) hπ'
    simp only [Category.assoc] at h1
    rw [(T.isThreefoldStepDiagram i).comp_eq_minus,
      (T.isThreefoldStepDiagram i).comp_eq_plus] at h1
    rw [eqToIso_refl, Iso.refl_inv, Category.id_comp]
    exact h1.symm
  exact key _ h (C.bridge i).e (C.bridge i).modelMap_eq

/-- **The difficulty does not increase under a coefficient decrease** `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')`,
with the decreased pair the model `y` identified with `Y_i` by `φ`, provided weights do not
increase along the move. -/
private theorem le_of_isDifficulty_of_coefficientMove (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) (y : Q.ModelIndex) (φ : Q.chain.model y.1 ≅ Q.chain.model ⟨i, none⟩)
    (hφ : (∃ (h : 0 < (Q.chain.bridge i).P.m) (hy : y.1 = ⟨i, some ⟨0, h⟩⟩),
        φ.hom = eqToHom ((congrArg Q.chain.model hy).trans
          (rfl : Q.chain.model ⟨i, some ⟨0, h⟩⟩ = Q.chain.model ⟨i, none⟩))) ∨
      (∃ (h : (Q.chain.bridge i).P.m = 0) (hy : y.1 = ⟨i + 1, none⟩),
        φ.hom = eqToHom (congrArg Q.chain.model hy) ≫ (Q.chain.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h)))
    (hs : φ.inv ≫ Q.chain.modelStructure y.1 = Q.chain.modelStructure ⟨i, none⟩)
    (hmono : ∀ (v : Valuation (Q.chain.model ⟨i, none⟩).functionField
        (WithZero (Multiplicative ℤ))) (w w' : ℕ),
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
        Q.chain.IsValuationWeight Q.scale y.1 (v.comap (functionFieldMap φ.inv)) w' → w' ≤ w)
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D) (hD' : Q.IsDifficulty y D') :
    D' ≤ D := by
  classical
  obtain ⟨F, -, hFex, -, hdiff⟩ := exists_finite_isDifficulty_sub_eq_finsum Q hi y φ hφ
  choose! w hw using fun v hv => exists_isValuationWeight Q ⟨⟨i, none⟩, hi⟩ (hFex v hv)
  choose! w' hw' using fun v hv =>
    exists_isValuationWeight Q y (isExceptionalValuation_comap φ.symm hs (hFex v hv))
  have h := hdiff D D' hD hD' w w' hw fun v hv v' hv' => by
    subst hv'
    simpa only [Iso.symm_hom, comap_inv_comap_hom] using hw' _ hv
  have hnn : 0 ≤ ∑ᶠ (v) (_ : v ∈ F), ((w v : ℤ) - w' v) :=
    finsum_nonneg fun v => finsum_nonneg fun hv =>
      sub_nonneg.2 (by exact_mod_cast hmono v _ _ (hw v hv) (hw' v hv))
  linarith

/-! ### Flips -/

/-- Pulling back valuations along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {A B Γ : Type*} [Ring A] [Ring B]
    [LinearOrderedCommMonoidWithZero Γ] {f : A →+* B} (hf : Function.Surjective f)
    {v w : Valuation B Γ} (h : v.comap f = w.comap f) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hf t
    exact congrArg (fun u : Valuation A Γ => u s) h

/-- The morphism `Y⁺ ⟶ T_k` of a flip of a bridge is `g_k⁺` precomposed with an
isomorphism. -/
private theorem exists_isIso_flipTargetMap_eq (C : TerminalChain T) (i : ℕ)
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

open MMP.Fourfold.Oai4C1.CommonModel in
/-- The extension of function fields `ℂ(Z) → ℂ(Y⁺)` of the target map of a flip move is
surjective. -/
private theorem functionFieldMap_targetMap_surjective (Q : PreparedChain T)
    (μ : Q.FlipMove) : Function.Surjective (functionFieldMap μ.targetMap) := by
  have hb := ((Q.chain.bridge μ.1.1).P.isThreefoldStepDiagram μ.1.2
    μ.1.2.2).isSmallMorphism_plus.isBirationalMorphism
  obtain ⟨φ, hφ, hft⟩ := exists_isIso_flipTargetMap_eq Q.chain μ.1.1 μ.1.2
  have hb' : IsBirationalMorphism μ.targetMap := by
    change IsBirationalMorphism (Q.chain.flipTargetMap _ _)
    rw [hft]
    exact isBirationalMorphism_comp (isBirationalMorphism_of_isOpenImmersion φ ⊤ dense_univ) hb
  exact hb'.functionFieldMap_bijective.2

/-- **The difficulty does not increase under a small terminal flip** `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)`: the
difference is a sum of weight differences over the weighted bad set, each nonnegative. -/
private theorem le_of_isDifficulty_of_flipMove (Q : PreparedChain T) (μ : Q.FlipMove) {D D' : ℤ}
    (hD : Q.IsDifficulty μ.source D) (hD' : Q.IsDifficulty μ.target D') : D' ≤ D := by
  classical
  have hmem : ∀ v ∈ Q.flipBadSet μ, ∃ (v' : Valuation (Q.chain.model μ.target.1).functionField
      (WithZero (Multiplicative ℤ))) (w w' : ℕ),
      v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) ∧
        Q.chain.IsValuationWeight Q.scale μ.source.1 v w ∧
          Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' := by
    rintro v ⟨-, v', hv', w, w', hw, hw', -⟩
    exact ⟨v', w, w', hv', hw, hw'⟩
  choose! v' wm wp hv' hwm hwp using hmem
  have h := sub_eq_finsum_of_isDifficulty_of_flipMove Q μ hD hD' hwm fun v hv u hu => by
    obtain rfl : u = v' v := comap_injective_of_surjective
      (functionFieldMap_targetMap_surjective Q μ) (hu.trans (hv' v hv).symm)
    exact hwp v hv
  have hnn : 0 ≤ ∑ᶠ v ∈ Q.flipBadSet μ, ((wm v : ℤ) - wp v) :=
    finsum_nonneg fun v => finsum_nonneg fun hv => sub_nonneg.2 (by
      exact_mod_cast (le_of_isValuationWeight_of_move Q).2.2 μ v (v' v) (wm v) (wp v)
        (hv' v hv) (hwm v hv) (hwp v hv))
  linarith

/-- The difficulty does not increase along a move of a prepared chain: if `x ⤏ x'` is a
coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` (inside a bridge with flips, or onto the next
junction when the bridge has none) or a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)`, then
`𝒟(Y', Θ') ≤ 𝒟(Y, Θ)`. -/
@[mmp "prop_mmp_indexd_monotone"]
public theorem difficulty_le_of_move (Q : PreparedChain T) {x x' : Q.ModelIndex}
    (hmove :
      (∃ (i : ℕ) (hi : Q.start ≤ i) (h : 0 < (Q.chain.bridge i).P.m),
        x = ⟨⟨i, none⟩, hi⟩ ∧ x' = ⟨⟨i, some ⟨0, h⟩⟩, hi⟩) ∨
      (∃ (i : ℕ) (hi : Q.start ≤ i) (_ : (Q.chain.bridge i).P.m = 0),
        x = ⟨⟨i, none⟩, hi⟩ ∧ x' = ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩) ∨
      (∃ μ : Q.FlipMove, x = μ.source ∧ x' = μ.target))
    {D D' : ℤ} (hD : Q.IsDifficulty x D) (hD' : Q.IsDifficulty x' D') : D' ≤ D := by
  rcases hmove with ⟨i, hi, h, rfl, rfl⟩ | ⟨i, hi, h, rfl, rfl⟩ | ⟨μ, rfl, rfl⟩
  · refine le_of_isDifficulty_of_coefficientMove Q hi ⟨⟨i, some ⟨0, h⟩⟩, hi⟩
      (Iso.refl _) (Or.inl ⟨h, rfl, rfl⟩) (Category.id_comp _) (fun v w w' hw hw' => ?_) hD hD'
    refine (le_of_isValuationWeight_of_move Q).1 i hi h v w w' hw ?_
    obtain ⟨u, hu, hwu⟩ : ∃ u, u = v.comap (functionFieldMap
        (Iso.refl (Q.chain.model ⟨i, none⟩)).inv) ∧
          Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨0, h⟩⟩ u w' := ⟨_, rfl, hw'⟩
    obtain rfl : u = v := by
      subst hu
      ext t
      exact congrArg v (MMP.Mori.functionFieldMap_id_apply t)
    exact hwu
  · let φ : Q.chain.model ⟨i + 1, none⟩ ≅ Q.chain.model ⟨i, none⟩ := (Q.chain.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h)
    exact le_of_isDifficulty_of_coefficientMove Q hi ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ φ
      (Or.inr ⟨h, rfl, by rw [eqToHom_refl, Category.id_comp]; rfl⟩)
      (inv_comp_modelStructure_of_m_eq_zero Q.chain i h)
      (fun v w w' hw hw' => (le_of_isValuationWeight_of_move Q).2.1 i hi h v _ w w' rfl hw hw')
      hD hD'
  · exact le_of_isDifficulty_of_flipMove Q μ hD hD'

end MMP.Fourfold.StabilizedTail.PreparedChain
