module

public import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram

/-!
# The unit-drop valuation stays exceptional through the bridge

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail with a terminal chain, and let
`V ⊆ W_i⁺ ⊆ X_{i+1}` be an irreducible curve in the positive-side bad locus of the `i`-th step
such that `X_{i+1}` is smooth at `η_V` and `mld_{η_V}(X_{i+1}, B_{i+1}) > 1`. Then the generic
blowup valuation `v_V` of `ℂ(X_{i+1})` is exceptional over every model of the chain from the
junction `Y_i` to the junction `Y_{i+1}` inclusive: over `Y_i`, over every model `V_k` of the
`i`-th bridge (the first of which is the decreased pair on `Y_i`), and over `Y_{i+1}`.

## Main results

* `MMP.Fourfold.StabilizedTail.TerminalChain.isExceptionalValuation_of_isGenericBlowupValuation`

## Implementation notes

All models of the chain from `Y_i` to `Y_{i+1}` are birational over `Z_i`: `Y_i` by
`f_i ∘ p_i`, the model `V_k` of the `i`-th bridge by its structure morphism `π_k` to `Z_i`, and
`Y_{i+1}` by `f_i⁺ ∘ p_{i+1}`. A valuation `u` of the function field of a model is *the*
valuation `v_V` when the restrictions of `u` and `v_V` to `ℂ(Z_i)` agree. The morphisms `π_k`
are dominant, derived from the dominance of `π_0 = f_i ∘ p_i` (`isDominant_modelMap_bridge`).

Write `w` for the restriction of `v_V` to `ℂ(Z_i)`. Over a normal model `M` with a proper morphism
`g : M ⟶ Z_i` inducing an isomorphism of function fields, a valuation `u` of `ℂ(M)` restricting
to `w` is the valuation of a proper divisor over `M`, and it is exceptional over `M` as soon as
no prime divisor `P` of `M` has `ord_P = w` on `ℂ(Z_i)`. That no prime divisor of `X_i` or of
`X_{i+1}` has valuation `w` follows from `v_V` being exceptional over `X_{i+1}` and from the
small step `X_i ⟶ Z_i ⟵ X_{i+1}` extracting no divisor; that no element of `I(X_i, B_i)` or of
`I(X_{i+1}, B_{i+1})` restricts to `w` follows from `a(v_V; X_{i+1}, B_{i+1}) > 1` and the
stabilization `I(X_i, B_i) = I(X_{i+1}, B_{i+1})`. A prime divisor of a junction `Y_j` is either
exceptional, then the centre of an element of `I(X_j, B_j)`, or not, then its valuation is that
of a prime divisor of `X_j`; so no prime divisor of `Y_i` or `Y_{i+1}` has valuation `w`. Each
flip of the bridge extracts no divisor, so by induction no prime divisor of any model `V_k` has
valuation `w`.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedTail.TerminalChain

/-! ### Divisors over a model birational over a common base -/

/-- The function field map of a composite is the composite of the function field maps. -/
private theorem coe_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] :
    ⇑(functionFieldMap (a ≫ b)) = functionFieldMap a ∘ functionFieldMap b :=
  funext fun t => (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b t).symm

/-- The function field map of a composite is bijective when both factors' are. -/
private theorem bijective_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    (ha : Function.Bijective (functionFieldMap a))
    (hb : Function.Bijective (functionFieldMap b)) :
    Function.Bijective (functionFieldMap (a ≫ b)) := by
  rw [coe_functionFieldMap_comp]
  exact ha.comp hb

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : Function.Bijective (functionFieldMap g))
    (hg' : Function.Bijective (functionFieldMap g'))
    (D : DivisorOver ℂ (g ≫ sZ)) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField ℂ (g' ≫ sZ) ξ' := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hY : IsNormalVariety ℂ ((D.f ≫ g) ≫ sZ) := by
    rw [Category.assoc]
    exact D.isNormalVariety
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  letI := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g)
    (bijective_functionFieldMap_comp D.f g D.isBirationalMorphism.functionFieldMap_bijective hg)
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [show eP.symm (functionFieldMap g' s) = s from eP.symm_apply_apply s, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` is centred at some point of `X'`: it is `≤ 1` on the stalk and
`< 1` on its maximal ideal. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] [hgp' : IsProper g']
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
    rw [IsProper.eq_valuativeCriterion] at hgp'
    exact hgp'.1.1.1.existence
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
    [IsProper g'] (hg : Function.Bijective (functionFieldMap g))
    (hg' : Function.Bijective (functionFieldMap g'))
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

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension_center {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (D : DivisorOver ℂ sY) : D.IsExceptional ↔ 2 ≤ codimension D.center := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sY := hY.1.toIsSeparated
  have hsep : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set Y), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc]
  change 2 ≤ closedsCodimension (T := Y) ⟨(D.center : Set Y), D.center.isClosed⟩ ↔ _
  rw [closedsCodimension_coe]

/-! ### Valuations of prime divisors on `ℂ(Z)` -/

private theorem valuationOver_comp {Y X Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral X] [IsIntegral Z] (P : MMP.Mori.PrimeDivisor Y) (f : Y ⟶ X) (g : X ⟶ Z)
    [IsDominant f] [IsDominant g] :
    P.valuationOver (f ≫ g) = (P.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

private theorem valuationOver_congr {Y X : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral X] (P : MMP.Mori.PrimeDivisor Y) {f f' : Y ⟶ X} [IsDominant f]
    [IsDominant f'] (h : f = f') : P.valuationOver f = P.valuationOver f' := by
  subst h
  rfl

private theorem valuation_comap_injective_of_surjective {K L Γ₀ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ₀] {φ : K →+* L} (hφ : Function.Surjective φ)
    {u u' : Valuation L Γ₀}
    (h : u.comap φ = u'.comap φ) : u = u' := by
  ext x
  obtain ⟨y, rfl⟩ := hφ x
  simpa using congrArg (fun w => w y) h

private theorem ofPrimeDivisor_valuation_comap {M Z : Scheme.{0}} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [IsIntegral Z] {sM : M ⟶ Spec (.of ℂ)}
    (hM : IsNormalVariety ℂ sM) (P : MMP.Mori.PrimeDivisor M) (g : M ⟶ Z) [IsDominant g] :
    (DivisorOver.ofPrimeDivisor ℂ hM P).valuation.comap (functionFieldMap g) =
      P.valuationOver g := by
  change (P.valuationOver (𝟙 M)).comap _ = _
  rw [← valuationOver_comp, valuationOver_congr P (Category.id_comp g)]

/-- Over a normal model `g : M ⟶ Z`, proper and inducing an isomorphism of function fields, a
valuation `u` of `ℂ(M)` restricting on `ℂ(Z)` to the valuation of a divisor over another such
model is exceptional over `M` when no prime divisor of `M` has that valuation on `ℂ(Z)`. -/
private theorem isExceptionalValuation_of_forall_valuationOver_ne
    {M X Z : Scheme.{0}} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [IsIntegral X]
    [IsIntegral Z] {sM : M ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hM : IsNormalVariety ℂ sM) (g : M ⟶ Z) (q : X ⟶ Z) [IsDominant g] [IsDominant q]
    [IsProper g] (hg : Function.Bijective (functionFieldMap g))
    (hq : Function.Bijective (functionFieldMap q))
    (hc : q ≫ sZ = sX) (hc' : g ≫ sZ = sM) (D : DivisorOver ℂ sX)
    (u : Valuation M.functionField (WithZero (Multiplicative ℤ)))
    (h : u.comap (functionFieldMap g) = D.valuation.comap (functionFieldMap q))
    (hP : ∀ P : MMP.Mori.PrimeDivisor M,
      P.valuationOver g ≠ D.valuation.comap (functionFieldMap q)) :
    MMP.Intersection.IsExceptionalValuation ℂ sM u := by
  obtain ⟨D', hD'p, hD'⟩ :=
    exists_properDivisorOver_valuation_eq_of_comap_eq hM q g hq hg hc hc' D u h
  refine ⟨D', hD'p, hD'.symm, ?_⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hM]
  intro P hPu
  apply hP P
  rw [← h, ← hD', hPu, ofPrimeDivisor_valuation_comap]

/-! ### The low-discrepancy set and junctions -/

/-- A valuation with centre `V` is not in `I(X, B)` when `mld_{η_V}(X, B) > 1`. -/
private theorem notMem_lowDiscrepancySet {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {B : QDivisor X} {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hc : MMP.Intersection.IsCentre ℂ sX v V)
    (hmld : 1 < minimalLogDiscrepancy sX B V.isIrreducible.genericPoint) :
    v ∉ lowDiscrepancySet sX B := by
  rintro ⟨-, a, ⟨n, D, -, hDv, hD⟩, ha⟩
  obtain ⟨D₁, -, hv1, hV⟩ := hc
  have hcen : (D.center : Set X) = closure {V.isIrreducible.genericPoint} := by
    rw [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 (hDv.trans hv1), ← hV]
    exact (IsIrreducible.isGenericPoint_genericPoint V.isIrreducible V.isClosed).def.symm
  have hle : minimalLogDiscrepancy sX B V.isIrreducible.genericPoint ≤ (a : EReal) :=
    sInf_le ⟨n, D, a, hD, hcen, rfl⟩
  have h1 : ((1 : ℝ) : EReal) < (a : EReal) := hmld.trans_le hle
  exact absurd ha (not_le.2 (EReal.coe_lt_coe_iff.1 h1))

/-- No prime divisor of a junction `p : Y ⟶ X` has valuation `w` on `ℂ(Z)` when no element of
the extracted set and no prime divisor of `X` has. -/
private theorem valuationOver_ne_of_crepantJunction {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)}
    {B : QDivisor X} {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (J : CrepantJunction sX B I) (hX : IsNormalVariety ℂ sX) (q : X ⟶ Z) [IsDominant q]
    [IsDominant J.p]
    (w : Valuation Z.functionField (WithZero (Multiplicative ℤ)))
    (hI : ∀ s ∈ I, s.comap (functionFieldMap q) ≠ w)
    (hQ : ∀ Q : MMP.Mori.PrimeDivisor X, Q.valuationOver q ≠ w) (P : MMP.Mori.PrimeDivisor J.Y) :
    P.valuationOver (J.p ≫ q) ≠ w := by
  rw [valuationOver_comp]
  by_cases hP : RationalMap.IsExceptional (X := J.Y) J.p.toRationalMap P
  · obtain ⟨s, rfl⟩ := (J.isExceptional_iff P).1 hP
    rw [show (J.E s).valuationOver J.p = s from J.valuation_eq s]
    exact hI s s.2
  · let D : DivisorOver ℂ sX := ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, P⟩
    have hD : ¬ 2 ≤ codimension D.center := fun h2 =>
      hP ((isExceptional_iff_two_le_codimension_center hX D).2 h2)
    rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hD
    push Not at hD
    obtain ⟨Q, hQe⟩ := hD
    rw [show P.valuationOver J.p = (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation from hQe,
      ofPrimeDivisor_valuation_comap]
    exact hQ Q

/-! ### The bridge -/

/-- The morphisms `π_k : V_k ⟶ Z_i` of the models of the `i`-th bridge, `k < m_i`, are dominant
when `π_0 = f_i ∘ p_i` is. -/
public theorem isDominant_modelMap_bridge {T : StabilizedTail} (C : TerminalChain T) (i : ℕ)
    [IsDominant ((C.junction i).p ≫ T.f i)] :
    ∀ k < (C.bridge i).P.m,
      IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact (inferInstance : IsDominant ((C.junction i).p ≫ T.f i))
  | succ k ih =>
    intro hk
    have hdom := ih (by omega)
    rw [(C.bridge i).P.modelMap_eq k (by omega)] at hdom
    have hh : IsDominant ((C.bridge i).P.h k) := IsDominant.of_comp ((C.bridge i).P.g k) _
    have hgp : IsDominant ((C.bridge i).P.gp k) :=
      ((C.bridge i).P.isThreefoldStepDiagram k
        (by omega)).isSmallMorphism_plus.isBirationalMorphism.isDominant
    rw [(C.bridge i).P.modelMap_succ_eq (by omega)]
    exact (IsDominant.comp_iff ((C.bridge i).P.gp k) ((C.bridge i).P.h k)).2 hh

/-- No prime divisor of a model `V_k` of the `i`-th bridge has valuation `w` on `ℂ(Z_i)` when no
prime divisor of `Y_i = V_0` has; the morphisms `π_k` are dominant and induce isomorphisms of
function fields. -/
private theorem bijective_functionFieldMap_and_valuationOver_ne_bridge {T : StabilizedTail}
    (C : TerminalChain T) (i : ℕ) [IsIntegral (T.Z i)] [IsDominant ((C.junction i).p ≫ T.f i)]
    (w : Valuation (T.Z i).functionField (WithZero (Multiplicative ℤ)))
    (hbij : Function.Bijective (functionFieldMap ((C.junction i).p ≫ T.f i)))
    (H0 : ∀ P : MMP.Mori.PrimeDivisor (C.junction i).Y,
      P.valuationOver ((C.junction i).p ≫ T.f i) ≠ w) :
    ∀ k < (C.bridge i).P.m,
      ∃ _ : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k),
      Function.Bijective
          (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) ∧
      ∀ P : MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y k),
        P.valuationOver (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) ≠ w := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨‹_›, hbij, H0⟩
  | succ k ih =>
    intro hk
    obtain ⟨hdom, hbk, ihk⟩ := ih (by omega)
    have hD := (C.bridge i).P.isThreefoldStepDiagram k (by omega)
    haveI := hD.isNormalVariety_target.1.toIsIntegral
    haveI := hD.isBirationalMorphism_minus.isDominant
    haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hmk := (C.bridge i).P.modelMap_eq k (by omega)
    haveI : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := by
      rw [← hmk]
      exact hdom
    haveI : IsDominant ((C.bridge i).P.h k) :=
      AlgebraicGeometry.IsDominant.of_comp ((C.bridge i).P.g k) ((C.bridge i).P.h k)
    have hπ : (C.bridge i).P.πY k = (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.πY_eq k (by omega)
    haveI hdk : IsDominant ((C.bridge i).P.πY k) := by
      rw [hπ]
      infer_instance
    have hbh : Function.Bijective (functionFieldMap ((C.bridge i).P.h k)) := by
      refine (Function.Bijective.of_comp_iff'
        hD.isBirationalMorphism_minus.functionFieldMap_bijective _).1 ?_
      rw [← coe_functionFieldMap_comp, ← MMP.Positivity.DivisorOver.functionFieldMap_congr hmk]
      exact hbk
    refine ⟨hdk, ?_, fun P => ?_⟩
    · change Function.Bijective (functionFieldMap ((C.bridge i).P.πY k))
      rw [MMP.Positivity.DivisorOver.functionFieldMap_congr hπ]
      exact bijective_functionFieldMap_comp _ _
        hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective hbh
    · haveI : IsProper ((C.bridge i).P.g k) :=
        isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
      obtain ⟨Pm, -, hPm, -⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism
        hD.isNormalVariety_target hD.isBirationalMorphism_minus hD.isSmallMorphism_plus P
      intro hP
      apply ihk Pm
      rwa [valuationOver_congr Pm hmk, valuationOver_comp, hPm,
        ← valuationOver_comp (Y := (C.bridge i).P.Y k) P,
        ← valuationOver_congr (Y := (C.bridge i).P.Y k) P hπ]

variable {T : StabilizedTail} (C : TerminalChain T)

/-- No prime divisor of the junctions `Y_i` and `Y_{i+1}` has valuation `w = v_V|_{ℂ(Z_i)}` on
`ℂ(Z_i)`, when `mld_{η_V}(X_{i+1}, B_{i+1}) > 1`. -/
private theorem valuationOver_junction_ne (i : ℕ) (V : IrreducibleCloseds (T.X (i + 1)))
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsGenericBlowupValuation (T.sX (i + 1)) V v) :
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
    (∀ P : MMP.Mori.PrimeDivisor (C.junction i).Y,
      P.valuationOver ((C.junction i).p ≫ T.f i) ≠ v.comap (functionFieldMap (T.fp i))) ∧
    ∀ P : MMP.Mori.PrimeDivisor (C.junction (i + 1)).Y,
      P.valuationOver ((C.junction (i + 1)).p ≫ T.fp i) ≠ v.comap (functionFieldMap (T.fp i)) := by
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  have hS := T.isThreefoldStepDiagram i
  have hX1 : IsNormalVariety ℂ (T.sX (i + 1)) := hS.isNormalVariety_plus
  obtain ⟨-, hcen, hexc, -⟩ := hv.hasLogDiscrepancy (T.isKltPair (i + 1)).1
  have hfp := hS.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective
  have hI1 : ∀ s ∈ lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1)),
      s.comap (functionFieldMap (T.fp i)) ≠ v.comap (functionFieldMap (T.fp i)) :=
    fun s hs he => notMem_lowDiscrepancySet hX1 hcen hmld
      (valuation_comap_injective_of_surjective hfp.2 he ▸ hs)
  have hQ1 : ∀ Q : MMP.Mori.PrimeDivisor (T.X (i + 1)),
      Q.valuationOver (T.fp i) ≠ v.comap (functionFieldMap (T.fp i)) := by
    intro Q hQ
    rw [← ofPrimeDivisor_valuation_comap hX1] at hQ
    obtain ⟨D, -, hD, h2⟩ := valuation_comap_injective_of_surjective hfp.2 hQ ▸ hexc
    exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX1 D).1 h2 Q hD.symm
  have hI0 : ∀ s ∈ lowDiscrepancySet (T.sX i) (T.B i),
      s.comap (functionFieldMap (T.f i)) ≠ v.comap (functionFieldMap (T.fp i)) := by
    intro s hs he
    obtain ⟨s', hs', hs'e⟩ : s.comap (functionFieldMap (T.f i)) ∈
        valuationsOver (T.fp i) (lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1))) :=
      T.lowDiscrepancySet_eq i ▸ ⟨s, hs, rfl⟩
    exact hI1 s' hs' (hs'e.trans he)
  have hQ0 : ∀ Q : MMP.Mori.PrimeDivisor (T.X i),
      Q.valuationOver (T.f i) ≠ v.comap (functionFieldMap (T.fp i)) := by
    intro Q hQ
    haveI : IsProper (T.fp i) := isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_plus
    obtain ⟨Pm, -, hPm, -⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism
      hS.isNormalVariety_target hS.isSmallMorphism_plus.isBirationalMorphism
      (T.isSmallMorphism i) Q
    exact hQ1 Pm (hPm.trans hQ)
  exact ⟨valuationOver_ne_of_crepantJunction (C.junction i) hS.isNormalVariety_minus (T.f i) _
      (fun s hs => hI0 s (by rwa [← C.coe_I i])) hQ0,
    valuationOver_ne_of_crepantJunction (C.junction (i + 1)) hX1 (T.fp i) _
      (fun s hs => hI1 s (by rwa [← C.coe_I (i + 1)])) hQ1⟩

/-- **The unit-drop valuation stays exceptional through the bridge.** Let `C` be a terminal chain
over a stabilized tail `T`, let `V ⊆ X_{i+1}` be an irreducible curve contained in the
positive-side bad locus `W_i⁺` of the `i`-th step, at whose generic point `η_V` the threefold
`X_{i+1}` is smooth, with `mld_{η_V}(X_{i+1}, B_{i+1}) > 1`, and let `v = v_V` be its generic
blowup valuation. Then `v` is exceptional over `Y_i`, over every model `V_k` of the `i`-th
terminal bridge, and over `Y_{i+1}`: every valuation of the function field of such a model
agreeing with `v` on `ℂ(Z_i)` is exceptional over that model. -/
@[mmp "lem_mmp_indexd_unit_drop_exceptional"]
public theorem isExceptionalValuation_of_isGenericBlowupValuation (i : ℕ)
    (V : IrreducibleCloseds (T.X (i + 1)))
    (hVW : (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i)
    (hV : topologicalKrullDim (V : Set (T.X (i + 1))) = 1)
    (hreg : IsRegularLocalRing ((T.X (i + 1)).presheaf.stalk V.isIrreducible.genericPoint))
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsGenericBlowupValuation (T.sX (i + 1)) V v) :
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
    (∀ u : Valuation (C.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)),
        u.comap (functionFieldMap ((C.junction i).p ≫ T.f i)) =
          v.comap (functionFieldMap (T.fp i)) →
        MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure ⟨i, none⟩) u) ∧
    (∀ k : Fin (C.bridge i).P.m,
        haveI := isDominant_modelMap_bridge C i k.1 k.2
        ∀ u : Valuation (C.model ⟨i, some k⟩).functionField (WithZero (Multiplicative ℤ)),
        u.comap
            (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) =
          v.comap (functionFieldMap (T.fp i)) →
        MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure ⟨i, some k⟩) u) ∧
    (∀ u : Valuation (C.model ⟨i + 1, none⟩).functionField (WithZero (Multiplicative ℤ)),
        u.comap (functionFieldMap ((C.junction (i + 1)).p ≫ T.fp i)) =
          v.comap (functionFieldMap (T.fp i)) →
        MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure ⟨i + 1, none⟩) u) := by
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  have hS := T.isThreefoldStepDiagram i
  obtain ⟨⟨D₀, -, hD₀⟩, -⟩ := hv.hasLogDiscrepancy (T.isKltPair (i + 1)).1
  have hfp := hS.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨hY0, hY1⟩ := valuationOver_junction_ne C i V hmld hv
  have hjb0 := bijective_functionFieldMap_comp (C.junction i).p (T.f i)
    (C.junction i).isBirationalMorphism.functionFieldMap_bijective
    hS.isBirationalMorphism_minus.functionFieldMap_bijective
  have hjb1 := bijective_functionFieldMap_comp (C.junction (i + 1)).p (T.fp i)
    (C.junction (i + 1)).isBirationalMorphism.functionFieldMap_bijective hfp
  have hfpc : T.fp i ≫ T.sZ i = T.sX (i + 1) := hS.comp_eq_plus
  haveI : IsSeparated (T.sZ i) := hS.isProjectiveVariety_target.toIsSeparated
  refine ⟨fun u hu => ?_, fun k u hu => ?_, fun u hu => ?_⟩
  · haveI : IsProper (C.junction i).p :=
      isProper_of_isProjectiveMorphism _ (C.junction i).isProjectiveMorphism
    haveI : IsProper (T.f i) := isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_minus
    refine isExceptionalValuation_of_forall_valuationOver_ne
      (sZ := T.sZ i) (g := (C.junction i).p ≫ T.f i)
      ⟨(C.junction i).isProjectiveVariety.toIsVariety, inferInstance⟩ (T.fp i) hjb0
      hfp hfpc ?_ D₀ u (by rwa [← hD₀]) (by rwa [← hD₀])
    change _ = (C.junction i).p ≫ T.sX i
    rw [Category.assoc, hS.comp_eq_minus]
  · obtain ⟨_, hbk, hne⟩ := bijective_functionFieldMap_and_valuationOver_ne_bridge C i
      (v.comap (functionFieldMap (T.fp i))) hjb0 hY0 k.1 k.2
    have hD := (C.bridge i).P.isThreefoldStepDiagram k.1 k.2
    have hmk := (C.bridge i).P.modelMap_eq k.1 k.2
    haveI : IsProper ((C.bridge i).P.g k.1) :=
      isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
    haveI : IsProper ((C.bridge i).P.sT k.1) :=
      isProper_of_isProjectiveMorphism _ hD.isProjectiveVariety_target.isProjective
    haveI : IsProper ((C.bridge i).P.h k.1 ≫ T.sZ i) := by
      rw [(C.bridge i).P.comp_eq_base k.1 k.2]
      infer_instance
    haveI : IsProper ((C.bridge i).P.h k.1) := IsProper.of_comp _ (T.sZ i)
    haveI : IsProper (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) := by
      rw [hmk]
      infer_instance
    refine isExceptionalValuation_of_forall_valuationOver_ne
      (sZ := T.sZ i) (g := modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)
      hD.isNormalVariety_minus (T.fp i) hbk hfp hfpc ?_ D₀ u
      (by rwa [← hD₀]) (by rwa [← hD₀])
    change _ = modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k.1
    rw [hmk, Category.assoc, (C.bridge i).P.comp_eq_base k.1 k.2, hD.comp_eq_minus]
  · haveI : IsProper (C.junction (i + 1)).p :=
      isProper_of_isProjectiveMorphism _ (C.junction (i + 1)).isProjectiveMorphism
    haveI : IsProper (T.fp i) := isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_plus
    refine isExceptionalValuation_of_forall_valuationOver_ne
      (sZ := T.sZ i) (g := (C.junction (i + 1)).p ≫ T.fp i)
      ⟨(C.junction (i + 1)).isProjectiveVariety.toIsVariety, inferInstance⟩ (T.fp i) hjb1
      hfp hfpc ?_ D₀ u (by rwa [← hD₀]) (by rwa [← hD₀])
    change _ = (C.junction (i + 1)).p ≫ T.sX (i + 1)
    rw [Category.assoc, hfpc]

end MMP.Fourfold.StabilizedTail.TerminalChain
