module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes
public import MMP.AlgebraicGeometry.MMP.Fourfold.SurfaceEchoLogDiscrepancy

/-!
# Weights at surfaces are unchanged by a coefficient decrease

Let `Q` be a prepared chain over a stabilized small klt tail of complex fourfolds, with its fixed
admissible scale `N`, and let `i ≥ i₀` index one of its bridges. The coefficient-decrease move of
that bridge replaces the junction `(Y_i, Θ_i)` by the decreased pair `(Y_i, Θ_i')`. Away from
finitely many irreducible surfaces `V ⊆ Y_i`, every normalized divisorial valuation `v` of
`ℂ(Y_i)` with centre `c_{Y_i}(v) = V` has the same weight `w_v(Y_i, Θ_i') = w_v(Y_i, Θ_i)`.

## Main results

* `PreparedChain.exists_finite_forall_isValuationWeight_iff_decreasedBoundary`: outside a finite
  set of surfaces, the weights for `Θ_i` and for `Θ_i'` agree.

## Implementation notes

* The decreased boundary is the field
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge.Θ'` of the `i`-th bridge, on the same
  variety `Y_i` as the junction; the move is
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge.isCoefficientDecrease`. This covers every
  bridge, including one with no flips, where the decreased pair is identified with the next
  junction.
* Weights are a predicate on their values. For `Θ_i` it is
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight` at the junction; for
  `Θ_i'` it is written out in the same form: `v` is exceptional over `Y_i`, and `w = w(2 - a)`
  for a log discrepancy `a = a(v; Y_i, Θ_i')`. Equality of weights is that the two predicates
  hold for the same `w`.
* An irreducible surface is an irreducible closed subset `V` with `topologicalKrullDim V = 2`,
  and `v` has centre `V` when `MMP.Intersection.IsCentre` holds.
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.FourfoldProofs.Oai4C3CoefficientMoveEchoUnchangedProof

open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail

/-! ### Weights of echoes -/

/-- Two finitely supported functions `g ≤ f` with the same sum are equal. -/
private theorem eq_of_le_of_finsum_eq {g f : ℕ → ℕ} (hf : (Function.support f).Finite)
    (hle : g ≤ f) (h : ∑ᶠ j, g j = ∑ᶠ j, f j) : g = f := by
  have hg : Function.support g ⊆ hf.toFinset := fun j hj =>
    hf.mem_toFinset.2 fun h0 => hj (Nat.eq_zero_of_le_zero (h0 ▸ hle j))
  rw [finsum_eq_sum_of_support_subset g hg, finsum_eq_sum_of_support_subset f hf.coe_toFinset.ge,
    Finset.sum_eq_sum_iff_of_le fun j _ => hle j] at h
  funext j
  by_cases hj : j ∈ hf.toFinset
  · exact h j hj
  · have h0 : f j = 0 := by simpa using hj
    exact h0 ▸ Nat.eq_zero_of_le_zero (h0 ▸ hle j)

/-- If two defaults `d(b) = d(b')` agree for `b' ≤ b < 1`, then every term
`w(1 - j(1 - b))` of the sum is unchanged: the terms for `b'` are no larger, and the sums agree. -/
private theorem difficultyWeight_eq_of_defaultWeight_eq {N : ℕ} {b b' : ℝ} (hb : b < 1)
    (hbb : b' ≤ b) (h : defaultWeight N b = defaultWeight N b') {j : ℕ} (hj : 1 ≤ j) :
    difficultyWeight N (1 - j * (1 - b')) = difficultyWeight N (1 - j * (1 - b)) := by
  have hle (j : ℕ) : difficultyWeight N (1 - j * (1 - b')) ≤
      difficultyWeight N (1 - j * (1 - b)) :=
    difficultyWeight_mono N (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have := congrFun (eq_of_le_of_finsum_eq
    (g := fun j => if 1 ≤ j then difficultyWeight N (1 - j * (1 - b')) else 0)
    (f := fun j => if 1 ≤ j then difficultyWeight N (1 - j * (1 - b)) else 0)
    ((finite_support_difficultyWeight N hb).subset fun j hj => by
      by_cases h1 : 1 ≤ j <;> simp_all)
    (fun j => by dsimp only; split_ifs <;> simp [hle])
    (by simpa only [defaultWeight, finsum_eq_if] using h.symm)) j
  simpa [hj] using this

/-- The weights `w(2 - a)` of the log discrepancies `a = 1 + j(1 - b) ≤ a' = 1 + j(1 - b')` of
an echo for two coefficients `0 ≤ b'`, `b < 1` agree when `b = 0` or the defaults
`d(b) = d(b')` agree. -/
private theorem difficultyWeight_echo_eq {N j : ℕ} {b b' : ℝ} (hj : 1 ≤ j) (hb : b < 1)
    (hb' : 0 ≤ b') (hle : 1 + j * (1 - b) ≤ 1 + j * (1 - b'))
    (h : b ≠ 0 → defaultWeight N b = defaultWeight N b') :
    difficultyWeight N (2 - (1 + j * (1 - b))) = difficultyWeight N (2 - (1 + j * (1 - b'))) := by
  have hbb : b' ≤ b := by
    have : (0 : ℝ) < j := by exact_mod_cast hj
    nlinarith
  rw [show 2 - (1 + j * (1 - b)) = 1 - j * (1 - b) by ring,
    show 2 - (1 + j * (1 - b')) = 1 - j * (1 - b') by ring]
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [le_antisymm hbb hb']
  · exact (difficultyWeight_eq_of_defaultWeight_eq hb hbb (h hb0) hj).symm

/-! ### Log discrepancies on one variety -/

section LogDiscrepancy

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- A log discrepancy realized on a proper divisor over `X` is a log discrepancy. -/
private theorem hasLogDiscrepancy_of_isValuationLogDiscrepancy {Θ : QDivisor X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (h : IsValuationLogDiscrepancy sX Θ v a) : HasLogDiscrepancy sX Θ v a := by
  obtain ⟨n, D, -, hD, hl⟩ := h
  exact ⟨n, D, hD, hl⟩

/-- The log discrepancy of a valuation with respect to a pair is unique. -/
private theorem hasLogDiscrepancy_unique {Θ : QDivisor X} (hP : MMP.Mori.IsPair sX Θ)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (h : HasLogDiscrepancy sX Θ v a) (h' : HasLogDiscrepancy sX Θ v a') : a = a' := by
  obtain ⟨n, E, hEv, hE⟩ := h
  obtain ⟨n', E', hEv', hE'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hP hE hE'
    (hEv.trans hEv'.symm)

/-- A valuation with a log discrepancy for one boundary has one for every pair on `X`: it is
realized by a proper divisor over `X`, and every such divisor has a discrepancy over a pair. -/
private theorem exists_isValuationLogDiscrepancy {Θ Θ' : QDivisor X}
    (hΘ' : MMP.Mori.IsPair sX Θ') {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sX Θ v a) :
    ∃ a', IsValuationLogDiscrepancy sX Θ' v a' := by
  obtain ⟨-, D, hp, hDv, -⟩ := h
  have ⟨_, n₀, K, hK, _⟩ := hΘ'
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ' hK D
  exact ⟨_, n₀, D, hp, hDv,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp⟩

/-- The coefficients of the boundary of a klt pair are `< 1`: the log discrepancy of a prime
divisor `P` of `X` is `1 - Θ_P`, which is positive. -/
private theorem coeff_lt_one_of_isKltPair {Θ : QDivisor X} (hΘ : IsKltPair sX Θ)
    (P : MMP.Mori.PrimeDivisor X) : Θ.coeff P < 1 := by
  obtain ⟨hX, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f := by
    change IsProper (𝟙 X)
    infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

end LogDiscrepancy

/-! ### Prime divisors, valuations and isomorphisms -/

section Valuations

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
    [IsNormal X] [IsIntegral Y] (P : MMP.Mori.PrimeDivisor X) {f g : X ⟶ Y} [hf : IsDominant f]
    [hg : IsDominant g] (h : f = g) : P.valuationOver f = P.valuationOver g := by
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

/-- The image of a prime divisor under an isomorphism. -/
private noncomputable def mapOfIso {V W : Scheme.{0}} (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor W :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e.hom Q.genericPoint) (by
    rw [coheight_eq_of_isOpenImmersion e.hom]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)

private theorem genericPoint_mapOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) : (mapOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- `ord_Q` regarded through `e ≫ b`, for an isomorphism `e`, is `ord` of the transported prime
divisor regarded through `b`. -/
private theorem valuationOver_iso_comp {V W Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Z] (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) (b : W ⟶ Z) [IsDominant b]
    [IsDominant e.hom] [IsDominant (e.hom ≫ b)] :
    Q.valuationOver (e.hom ≫ b) = (mapOfIso e Q).valuationOver b := by
  rw [valuationOver_comp, PrimeDivisor.valuationOver]
  congr 1
  ext g
  rw [Valuation.comap_apply]
  by_cases hg : g = 0
  · subst hg
    simp
  have hg' : functionFieldMap e.hom g ≠ 0 := (map_ne_zero _).mpr hg
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso e.hom Q (mapOfIso e Q)
      (genericPoint_mapOfIso e Q).symm]

/-- The inverse transform along an isomorphism has, at `P`, the coefficient at the image of
`P`. -/
private theorem coeff_inverseTransformDivisor_iso {V W : Scheme.{0}} (e : V ≅ W)
    (D : MMP.Mori.QDivisor W) (P : MMP.Mori.PrimeDivisor V) :
    (inverseTransformDivisor e.hom D).coeff P = D.coeff (mapOfIso e P) := by
  have htop : biregularLocus e.hom = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff e.hom).mpr inferInstance))
  exact MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint
    (genericPoint_mapOfIso e P).symm (by rw [htop]; trivial) D

end Valuations

/-! ### Label centres on the junction and on the decreased pair -/

section LabelCentre

variable {T : StabilizedSmallKltTail}

/-- Corresponding valuations are unique: the identifications `k(X_j) ≅ k(Z_j) ≅ k(X_{j+1})` are
isomorphisms. -/
private theorem corresponds_unique : ∀ {i : ℕ}
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.Corresponds i ξ w → T.Corresponds i ξ w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨_, hu, huw⟩, ⟨_, hu', huw'⟩ => by
    obtain rfl := corresponds_unique hu hu'
    exact comap_injective_of_surjective
      (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.functionFieldMap_bijective.2
      (huw.trans huw'.symm)

variable (C : TerminalChain T)

/-- A label has at most one centre on a junction. -/
private theorem eq_of_isLabelCentre_none {S : C.Label} {i : ℕ}
    (hX : IsNormalVariety ℂ (C.junction i).sY)
    {P P' : MMP.Mori.PrimeDivisor (C.junction i).Y}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S ⟨i, none⟩ P') : P = P' := by
  have := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hP⟩ := h
  obtain ⟨w', hw', hP'⟩ := h'
  obtain rfl := corresponds_unique hw hw'
  exact eq_of_valuationOver_eq hX _ (C.junction i).isBirationalMorphism.functionFieldMap_bijective.2
    (hP.trans hP'.symm)

/-- The centre of a label on a junction `Y_i` is its centre on the first model `V_0 = Y_i` of the
`i`-th bridge. -/
private theorem isLabelCentre_some_zero {S : C.Label} {i : ℕ} (hm : 0 < (C.bridge i).P.m)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P := by
  have := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨w, hw, (inferInstance : IsDominant ((C.junction i).p ≫ T.f i)), ?_⟩
  change P.valuationOver ((C.junction i).p ≫ T.f i) = _
  rw [valuationOver_comp, hP]

/-- A label has at most one centre on the first model of a bridge. -/
private theorem eq_of_isLabelCentre_some_zero {S : C.Label} {i : ℕ} (hm : 0 < (C.bridge i).P.m)
    (hX : IsNormalVariety ℂ (C.junction i).sY)
    {P P' : MMP.Mori.PrimeDivisor (C.junction i).Y}
    (h : C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P) (h' : C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P') :
    P = P' := by
  have := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, _, hP⟩ := h
  obtain ⟨w', hw', _, hP'⟩ := h'
  obtain rfl := corresponds_unique hw hw'
  have hb : IsBirationalMorphism ((C.junction i).p ≫ T.f i) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp (C.junction i).isBirationalMorphism
      (T.isFourfoldStepDiagram i).isBirationalMorphism_minus
  exact eq_of_valuationOver_eq hX ((C.junction i).p ≫ T.f i) hb.functionFieldMap_bijective.2
    (hP.trans hP'.symm)

/-- Through an identification `φ : Y_i ≅ Y_{i+1}` over `Z_i`, the centre of a label on `Y_i` is
carried to its centre on `Y_{i+1}`. -/
private theorem isLabelCentre_succ_of_iso {S : C.Label} {i : ℕ}
    (φ : (C.junction i).Y ≅ (C.junction (i + 1)).Y)
    (hπ : (C.junction i).p ≫ T.f i = φ.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i + 1, none⟩ (mapOfIso φ P) := by
  have := (C.junction i).isBirationalMorphism.isDominant
  have := (C.junction (i + 1)).isBirationalMorphism.isDominant
  have : IsDominant φ.hom := (isBirationalMorphism_of_isIso φ.hom).isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨_, ⟨w, hw, ?_⟩, rfl⟩
  change ((mapOfIso φ P).valuationOver (C.junction (i + 1)).p).comap
    (functionFieldMap (T.fp i)) = w.comap (functionFieldMap (T.f i))
  rw [← valuationOver_comp, ← valuationOver_iso_comp, ← hP, ← valuationOver_comp]
  exact valuationOver_congr _ (by rw [hπ])

/-- Along a bridge with no step, the decreased pair `(Y_i, Θ_i')` is identified with the next
junction `(Y_{i+1}, Θ_{i+1})` over `Z_i`. -/
private theorem exists_iso_of_m_eq_zero (i : ℕ) (h : (C.bridge i).P.m = 0) :
    ∃ φ : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
      (C.bridge i).Θ' = inverseTransformDivisor φ.hom (C.junction (i + 1)).Θ ∧
        (C.junction i).p ≫ T.f i = φ.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
  have key : ∀ (m : ℕ) (_ : m = 0) (e : (C.bridge i).P.model m ≅ (C.junction (i + 1)).Y),
      (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
      (C.bridge i).P.toBase m = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i →
      ∃ φ : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
        (C.bridge i).Θ' = inverseTransformDivisor φ.hom (C.junction (i + 1)).Θ ∧
          (C.junction i).p ≫ T.f i = φ.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
    rintro m rfl e hb hπ
    exact ⟨e, hb, hπ⟩
  exact key _ h (C.bridge i).e (C.bridge i).endBoundary_eq (C.bridge i).toBase_end_eq

end LabelCentre

/-- **Defaults across the coefficient decrease.** On a prepared chain, for a prime divisor `P`
of the junction `Y_i`, `i ≥ i₀`, in the support of `Θ_i`, the defaults `d(b)` of its
coefficients in `Θ_i` and in the decreased boundary `Θ_i'` agree: `P` is the centre of a label
`S_h` on `Y_i` and on the model following `Y_i`, whose default `d_h` is constant. -/
private theorem defaultWeight_coeff_eq {T : StabilizedSmallKltTail} (Q : PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) {P : MMP.Mori.PrimeDivisor (Q.chain.junction i).Y}
    (hP : (Q.chain.junction i).Θ.coeff P ≠ 0) :
    defaultWeight Q.scale ((Q.chain.junction i).Θ.coeff P) =
      defaultWeight Q.scale ((Q.chain.bridge i).Θ'.coeff P) := by
  obtain ⟨-, -, -, hΘ, -, hlab, -⟩ := Q.isKltTerminalPair_modelBoundary ⟨⟨i, none⟩, hi⟩
  obtain ⟨S, hS⟩ := hlab P hP
  obtain ⟨d, hd⟩ := Q.isLabelDefault_const S
  have hX : IsNormalVariety ℂ (Q.chain.junction i).sY := hΘ.1.1.isPair.1
  have hdef : ∀ (x : Q.chain.ModelIndex) (_ : Q.start ≤ x.1)
      (P' : MMP.Mori.PrimeDivisor (Q.chain.model x)), Q.chain.IsLabelCentre S x P' →
      (∀ P'', Q.chain.IsLabelCentre S x P'' → P'' = P') →
      d = defaultWeight Q.scale ((Q.chain.modelBoundary x).coeff P') := by
    intro x hx P' hP' huniq
    obtain ⟨b, hb, rfl⟩ := hd x hx
    rcases hb with ⟨P'', hP'', rfl⟩ | ⟨hno, -⟩
    · rw [huniq P'' hP'']
    · exact absurd hP' (hno P')
  refine (hdef ⟨i, none⟩ hi P hS fun P'' h =>
    eq_of_isLabelCentre_none Q.chain hX h hS).symm.trans ?_
  by_cases hm : 0 < (Q.chain.bridge i).P.m
  · have hS1 := isLabelCentre_some_zero Q.chain hm hS
    exact hdef ⟨i, some ⟨0, hm⟩⟩ hi P hS1 fun P'' h =>
      eq_of_isLabelCentre_some_zero Q.chain hm hX h hS1
  · obtain ⟨φ, hΘ', hπ⟩ := exists_iso_of_m_eq_zero Q.chain i (by omega)
    obtain ⟨-, -, -, hΘ1, -, -, -⟩ :=
      Q.isKltTerminalPair_modelBoundary ⟨⟨i + 1, none⟩, hi.trans (Nat.le_succ i)⟩
    have hX1 : IsNormalVariety ℂ (Q.chain.junction (i + 1)).sY := hΘ1.1.1.isPair.1
    have hS1 := isLabelCentre_succ_of_iso Q.chain φ hπ hS
    refine (hdef ⟨i + 1, none⟩ (hi.trans (Nat.le_succ i)) _ hS1 fun P'' h =>
      eq_of_isLabelCentre_none Q.chain hX1 h hS1).trans ?_
    change defaultWeight Q.scale ((Q.chain.junction (i + 1)).Θ.coeff (mapOfIso φ P)) = _
    rw [hΘ', coeff_inverseTransformDivisor_iso]

end MMP.FourfoldProofs.Oai4C3CoefficientMoveEchoUnchangedProof

end

section

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

open MMP.FourfoldProofs.Oai4C3CoefficientMoveEchoUnchangedProof MMP.Mori MMP.Fourfold in
/-- On a prepared chain, for the coefficient-decrease move `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` of the
`i`-th bridge, there is a finite set `E` of irreducible closed subsets of `Y_i` such that for
every irreducible surface `V ∉ E` and every normalized divisorial valuation `v` of `ℂ(Y_i)` with
centre `c_{Y_i}(v) = V`, the weights agree: `w_v(Y_i, Θ_i') = w_v(Y_i, Θ_i)`. -/
@[mmp "lem_oai4_c3_coefficient_move_echo_unchanged"]
public theorem exists_finite_forall_isValuationWeight_iff_decreasedBoundary
    {T : StabilizedSmallKltTail} (Q : PreparedChain T) (i : ℕ) (hi : Q.start ≤ i) :
    ∃ E : Set (IrreducibleCloseds (Q.chain.junction i).Y), E.Finite ∧
      ∀ V : IrreducibleCloseds (Q.chain.junction i).Y, V ∉ E →
        topologicalKrullDim (V : Set (Q.chain.junction i).Y) = 2 →
        ∀ v : Valuation (Q.chain.junction i).Y.functionField (WithZero (Multiplicative ℤ)),
          MMP.Intersection.IsCentre ℂ (Q.chain.junction i).sY v V →
          ∀ w : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w ↔
            (MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.junction i).sY v ∧
              ∃ a : ℝ, IsValuationLogDiscrepancy (Q.chain.junction i).sY
                (Q.chain.bridge i).Θ' v a ∧ w = difficultyWeight Q.scale (2 - a)) := by
  obtain ⟨hproj, hQ, hdim, hΘ, -, -, -⟩ := Q.isKltTerminalPair_modelBoundary ⟨⟨i, none⟩, hi⟩
  replace hproj : MMP.Mori.IsProjectiveVariety ℂ (Q.chain.junction i).sY := hproj
  replace hQ : IsQFactorial (Q.chain.junction i).sY := hQ
  replace hdim : topologicalKrullDim (Q.chain.junction i).Y = 4 := hdim
  replace hΘ : IsKltTerminalPair (Q.chain.junction i).sY (Q.chain.junction i).Θ := hΘ
  have hΘ' : IsKltTerminalPair (Q.chain.junction i).sY (Q.chain.bridge i).Θ' :=
    (Q.chain.bridge i).isDecreasedBoundary.isKltTerminalPair (Q.chain.bridge i).coe_source
  classical
  set L := (Q.chain.junction i).Θ.support ∪ (Q.chain.bridge i).Θ'.support with hL
  obtain ⟨𝒮, -, h𝒮⟩ := IsKltTerminalPair.exists_finset_forall_isSurfaceEcho hproj hQ hdim hΘ
    (L := L) Finset.subset_union_left
  refine ⟨↑𝒮, 𝒮.finite_toSet, fun V hV𝒮 hV v hcen w => ?_⟩
  have key : ∀ a a' : ℝ,
      IsValuationLogDiscrepancy (Q.chain.junction i).sY (Q.chain.junction i).Θ v a →
      IsValuationLogDiscrepancy (Q.chain.junction i).sY (Q.chain.bridge i).Θ' v a' →
      difficultyWeight Q.scale (2 - a) = difficultyWeight Q.scale (2 - a') := by
    intro a a' ha ha'
    have hle := (Q.chain.bridge i).isDecreasedBoundary.le_of_isValuationLogDiscrepancy ha ha'
    by_cases ha2 : a < 2
    · obtain ⟨S, j, hecho, rfl⟩ := h𝒮 V hV (by simpa using hV𝒮) v hcen a ha2
        (hasLogDiscrepancy_of_isValuationLogDiscrepancy ha)
      obtain rfl := hasLogDiscrepancy_unique hΘ'.1.1.isPair
        (hasLogDiscrepancy_of_isValuationLogDiscrepancy ha')
        (hecho.hasLogDiscrepancy hΘ'.1.1 Finset.subset_union_right
          fun S' _ => coeff_lt_one_of_isKltPair hΘ'.1 S')
      exact difficultyWeight_echo_eq hecho.2.2.2.2.2.2.1
        (by exact_mod_cast coeff_lt_one_of_isKltPair hΘ.1 S)
        (by exact_mod_cast hΘ'.1.1.nonneg S) hle
        fun h0 => defaultWeight_coeff_eq Q hi (Rat.cast_ne_zero.mp h0)
    · rw [difficultyWeight_of_nonpos (by linarith), difficultyWeight_of_nonpos (by linarith)]
  constructor
  · rintro ⟨hexc, a, ha, rfl⟩
    obtain ⟨a', ha'⟩ := exists_isValuationLogDiscrepancy hΘ'.1.1.isPair ha
    exact ⟨hexc, a', ha', key a a' ha ha'⟩
  · rintro ⟨hexc, a', ha', rfl⟩
    obtain ⟨a, ha⟩ := exists_isValuationLogDiscrepancy hΘ.1.1.isPair ha'
    exact ⟨hexc, a, ha, (key a a' ha ha').symm⟩

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

end
