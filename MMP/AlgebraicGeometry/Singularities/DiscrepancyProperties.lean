/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Basic
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Centers, pull-backs of `ℝ`-Cartier divisors and discrepancies in *Flips and abundance*

Properties of the notions of FA (1.6.2) and §2 (`MMP.Foundations.Flips.Basic`,
`MMP.Foundations.Flips.Discrepancy`):

* a valuation ring of the function field of a separated integral scheme has at most one center,
  and the center `f(E)` of a divisor over a variety depends only on `ord_E` (FA (1.6.2));
* a map over `Z` to a scheme proper over `Z` is a morphism in codimension one, in particular the
  inverse of a proper birational morphism to a normal variety (FA 2.4.1);
* presentations of an `ℝ`-Cartier divisor are unique in `Ca(X) ⊗ ℝ`, and its pull-back exists and
  is unique (FA 2.2.2, 2.5.1);
* the discrepancy does not depend on the choices made (FA 2.5.2), and `a(ord_P, D_X) = -c(P)` for
  a prime divisor `P` of `X` (FA 2.5.4);
* the discrepancy formula `K_Y + f⁻¹_*(D_X) = f^*(K_X + D_X) + ∑ a(E_i, D_X) E_i` (FA 2.5.1).

## Main results

* `MMP.Flips.eq_of_isLocal_le_valuationSubring`,
  `MMP.Flips.ProperDivisorOver.center_eq_of_valuation_eq`
* `MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver`,
  `MMP.Flips.RationalMap.isMorphismInCodimOne_inverse`
* `MMP.Flips.sum_tmul_eq_of_sum_smul_eq`, `MMP.Flips.existsUnique_isRCartierPullback`,
  `MMP.Flips.isRCartierPullback_of_zsmul_eq`
* `MMP.Flips.IsDiscrepancyWith.eq`, `MMP.Flips.IsDiscrepancy.eq`,
  `MMP.Flips.isDiscrepancy_divisorialValuation`, `MMP.Flips.IsDiscrepancy.eq_neg_coeff`
* `MMP.Flips.discrepancy_formula`

## Implementation notes

FA works over `ℂ`. The statements about discrepancies assume the base field `k` perfect, so that
`Ω^n_{k(X)/k}` has the expected rank and orders of forms along divisors over `X` depend only on
the valuation, as in `MMP.Mori.DivisorOver.exists_ordPullback_eq`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (1.6.2), 2.2.2,
  2.4.1, 2.5.1, 2.5.2, 2.5.4
-/

@[expose] public noncomputable section

universe u

/-! ### Centers of valuations -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

/-- A point `z` whose local ring is locally dominated by a valuation ring `R ⊆ k(X)` gives a
morphism `Spec R ⟶ X` extending the generic point and sending the closed point to `z`. -/
theorem exists_spec_valuationSubring_hom_of_le {X : Scheme.{u}} [IsIntegral X]
    (R : ValuationSubring X.functionField) (z : X)
    (h : ∀ a : X.presheaf.stalk z, algebraMap _ X.functionField a ∈ R)
    (hl : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z),
      algebraMap _ X.functionField a ∈ R.nonunits) :
    ∃ l : Spec (.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) ∧
      l (IsLocalRing.closedPoint R) = z := by
  let φ : X.presheaf.stalk z →+* R :=
    (algebraMap (X.presheaf.stalk z) X.functionField).codRestrict R h
  have hφ : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hnu := hl a ((IsLocalRing.mem_maximalIdeal _).2 hna)
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hnu
    obtain ⟨hmem, hmax⟩ := hnu
    exact hmax ha
  have hy : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z, ?_, ?_⟩
  · have hc : CommRingCat.ofHom φ ≫
        CommRingCat.ofHom (algebraMap R X.functionField) =
        X.presheaf.stalkSpecializes hy := by
      ext a
      rfl
    rw [← Spec.map_comp_assoc, hc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  · change X.fromSpecStalk z (Spec.map (CommRingCat.ofHom φ)
      (IsLocalRing.closedPoint R)) = z
    have : IsLocalHom (CommRingCat.ofHom φ).hom := hφ
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- **Uniqueness of a centre on a separated variety.** Let `X` be an integral scheme separated
over a field `k` and `R ⊆ k(X)` a valuation ring of the function field. There is at most one point
`x ∈ X` such that `𝒪_{X,x} ⊆ k(X)` lands in `R` and the inclusion `𝒪_{X,x} ⊆ R` is local (the
maximal ideal of `𝒪_{X,x}` lands in the maximal ideal `R.nonunits` of `R`). -/
@[mmp "lem_mmp_threefold_valuation_centre_unique"]
theorem eq_of_isLocal_le_valuationSubring {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] (R : ValuationSubring X.functionField) {x x' : X}
    (h : ∀ a : X.presheaf.stalk x, algebraMap _ X.functionField a ∈ R)
    (hl : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      algebraMap _ X.functionField a ∈ R.nonunits)
    (h' : ∀ a : X.presheaf.stalk x', algebraMap _ X.functionField a ∈ R)
    (hl' : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x'),
      algebraMap _ X.functionField a ∈ R.nonunits) :
    x = x' := by
  obtain ⟨l, hl0, hlx⟩ := exists_spec_valuationSubring_hom_of_le R x h hl
  obtain ⟨l', hl0', hlx'⟩ := exists_spec_valuationSubring_hom_of_le R x' h' hl'
  let α := CommRingCat.ofHom (algebraMap R X.functionField)
  have key : ∀ g g' : Spec (.of R) ⟶ Spec (.of k),
      Spec.map α ≫ g = Spec.map α ≫ g' → g = g' := by
    intro g g' hg
    obtain ⟨p, rfl⟩ : ∃ p, Spec.map p = g := ⟨_, Spec.map_preimage g⟩
    obtain ⟨p', rfl⟩ : ∃ p, Spec.map p = g' := ⟨_, Spec.map_preimage g'⟩
    rw [← Spec.map_comp, ← Spec.map_comp] at hg
    congr 1
    ext c
    exact congrArg (fun q => q.hom c) (Spec.map_injective hg)
  have hll : l' ≫ sX = l ≫ sX := key _ _ (by rw [← Category.assoc, ← Category.assoc, hl0, hl0'])
  let S : ValuativeCommSq sX :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := l ≫ sX
      commSq := ⟨by rw [← hl0, Category.assoc]⟩ }
  have hS := IsSeparated.valuativeCriterion sX S
  let L : S.commSq.LiftStruct := ⟨l, hl0, rfl⟩
  let L' : S.commSq.LiftStruct := ⟨l', hl0', hll⟩
  have hLL := congrArg CommSq.LiftStruct.l (Subsingleton.elim L L')
  rw [← hlx, ← hlx']
  exact congrArg (fun m : Spec (.of R) ⟶ X => m (IsLocalRing.closedPoint R)) hLL

namespace ProperDivisorOver

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- **FA (1.6.2): the center depends only on the valuation.** Divisors `(Y, f, E)` and
`(Y', f', E')` over a variety `X` with `ord_E = ord_{E'}` as valuations of `k(X)` have the same
center `f(E) = f'(E')`. -/
@[mmp "lem_fa1a_center_independent_of_model"]
theorem center_eq_of_valuation_eq (hX : Mori.IsVariety k sX) {D D' : ProperDivisorOver k sX}
    (h : D.valuation = D'.valuation) : D.center = D'.center := by
  rw [center_eq_toDivisorOver_center, center_eq_toDivisorOver_center]
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX h

end ProperDivisorOver

end MMP.Flips

/-! ### Maps over a proper base are morphisms in codimension one -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips.RationalMap

variable {k : Type u} [Field k]

/-- Restricting a partial map from `Spec 𝒪_{X,x}` along a generization `y ⤳ x` gives its
restriction to `Spec 𝒪_{X,y}`. -/
theorem fromSpecStalkOfMem_specializes {X Y : Scheme.{u}} (g : X.PartialMap Y) {x y : X}
    (h : y ⤳ x) (hx : x ∈ g.domain) (hy : y ∈ g.domain) :
    g.fromSpecStalkOfMem hy =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ g.fromSpecStalkOfMem hx := by
  simp only [Scheme.PartialMap.fromSpecStalkOfMem, ← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- `Spec K(X) ⟶ Y ⟶ Z` along `φ.compHom q` is `φ` followed by `q`. -/
theorem fromFunctionField_compHom {X Y Z : Scheme.{u}} [IsIntegral X] (φ : X.RationalMap Y)
    (q : Y ⟶ Z) : (φ.compHom q).fromFunctionField = φ.fromFunctionField ≫ q := by
  obtain ⟨g, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap]
  exact Scheme.PartialMap.fromSpecStalkOfMem_compHom _ _ _ _

/-- The rational map of a morphism `p` restricts on `Spec K(X)` to `Spec K(X) ⟶ X ⟶ Y`. -/
theorem fromFunctionField_hom {X Y : Scheme.{u}} [IsIntegral X] (p : X ⟶ Y) :
    p.toRationalMap.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ p :=
  Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap _ _

/-- **Valuative extension of a map over a proper base.** Let `X` be integral, `q : Y ⟶ Z`
proper and `φ : X ⤏ Y` a rational map with `q ∘ φ = p`. Then `φ` is defined at every point `x`
whose local ring is a valuation ring: the valuative criterion lifts `Spec 𝒪_{X,x} ⟶ Z` to `Y`
extending `φ` at the generic point, and the lift spreads out to an open neighbourhood of `x`. -/
theorem mem_domain_of_valuationRing {X Y Z : Scheme.{u}} [IsIntegral X] (p : X ⟶ Z) (q : Y ⟶ Z)
    [IsProper q] (φ : X.RationalMap Y) (hφ : φ.compHom q = p.toRationalMap) (x : X)
    [ValuationRing (X.presheaf.stalk x)] : x ∈ φ.domain := by
  have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence q := by
    have h : @IsProper _ _ q := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  have hsq0 : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen
  have htop : φ.fromFunctionField ≫ q = X.fromSpecStalk (genericPoint X) ≫ p := by
    rw [← fromFunctionField_compHom, hφ, fromFunctionField_hom]
  let S : ValuativeCommSq q :=
    { R := X.presheaf.stalk x
      domain := inferInstance
      K := X.functionField
      i₁ := φ.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ p
      commSq := ⟨by rw [htop, ← hsq0, Category.assoc]⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hex S).exists_lift
  have hl₂' : l ≫ q = X.fromSpecStalk x ≫ p := hl₂
  let g := Scheme.PartialMap.ofFromSpecStalk p q l hl₂'
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk p q l hl₂'
  have hgφ : g.toRationalMap = φ := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
    change g.fromSpecStalkOfMem _ = _
    rw [fromSpecStalkOfMem_specializes g hgen hxg,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hl₁
  exact Scheme.RationalMap.mem_domain.mpr ⟨g, hxg, hgφ⟩

/-- On a locally Noetherian normal integral scheme, a rational map `φ : X ⤏ Y` over `Z` with
`q : Y ⟶ Z` proper is defined at every point of codimension `≤ 1`. -/
theorem mem_domain_of_coheight_le_one {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (p : X ⟶ Z) (q : Y ⟶ Z) [IsProper q] (φ : X.RationalMap Y)
    (hφ : φ.compHom q = p.toRationalMap) {x : X} (hx : Order.coheight x ≤ 1) :
    x ∈ φ.domain := by
  rcases lt_or_eq_of_le hx with h | h
  · have hmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h)
    have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    have hx' : x ⤳ genericPoint X := hmax (show x ≤ genericPoint X from hgen)
    have hgx : genericPoint X = x := (hgen.antisymm hx').eq
    rw [← hgx]
    exact (genericPoint_specializes _).mem_open φ.domain.2 φ.dense_domain.nonempty.choose_spec
  · have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h]
      rfl
    have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
        ringKrullDim (X.presheaf.stalk x) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal x, hdim⟩
    obtain ⟨_, _⟩ := ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
    exact mem_domain_of_valuationRing p q φ hφ x

/-- **A map to a proper variety over `Z` is a morphism in codimension one** (implicit in FA
Def. 2.4.1 and 2.21). Let `X` be a normal variety, `p : X ⟶ Z` a morphism, `q : Y ⟶ Z` a proper
morphism (of varieties, in the source; this is not needed) and `φ : X ⤏ Y` a map over `Z`. Then
`φ` is a morphism in codimension one:
the complement of its domain of definition has codimension `≥ 2`. -/
@[mmp "lem_fa2_birational_inverse_morphism_codim_one"]
theorem isMorphismInCodimOne_of_isOver {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : Mori.IsNormalVariety k sX) (p : X ⟶ Z) (q : Y ⟶ Z) [IsProper q]
    (φ : X.RationalMap Y) (hφ : IsOver p q φ) : IsMorphismInCodimOne φ := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  exact two_le_closedsCodimension_compl (Mori.RationalMap.dom φ).2
    fun _ hx ↦ mem_domain_of_coheight_le_one p q φ hφ hx

/-- **FA 2.4.1, "when `f = g⁻¹`".** For a proper birational morphism `g : Y ⟶ X` of varieties with
`X` normal, the inverse `g⁻¹ : X ⤏ Y` is a morphism in codimension one. -/
@[mmp "lem_fa2_birational_inverse_morphism_codim_one"]
theorem isMorphismInCodimOne_inverse {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : Mori.IsNormalVariety k sX) (g : Y ⟶ X) (hY : Mori.IsVariety k (g ≫ sX)) [IsProper g]
    (hg : Mori.IsBirationalMorphism g) :
    IsMorphismInCodimOne (Mori.RationalMap.IsBirational.inverse hg) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sX]; infer_instance⟩
  obtain ⟨e, he, hinv⟩ := hg.isInverse_inverse
  have key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ g := by
    obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
    have hWl' : W ≤ e.source := hWl
    have : IsDominant (Y.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
    refine ext_of_isDominant (Y.homOfLE hWl') ?_
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    refine hEq.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc Y (show W ≤ ⊤ from hWr) g
  have hover : IsOver (𝟙 X) g (Mori.RationalMap.IsBirational.inverse hg) := by
    rw [IsOver, ← hinv]
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
    change X.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ g = X.homOfLE _ ≫ X.topIso.hom ≫ 𝟙 X
    rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]
    simp
  exact isMorphismInCodimOne_of_isOver hX (𝟙 X) g _ hover

end MMP.Flips.RationalMap

/-! ### Presentations and pull-backs of `ℝ`-Cartier divisors -/

open CategoryTheory AlgebraicGeometry TopologicalSpace TensorProduct

namespace MMP.Flips

open MMP.Mori

section Helpers

variable {X : Scheme.{u}}

/-- For an additive map `g : G → Div(X)`, the additive map `G ⊗_ℤ ℝ → Div(X)_ℝ`,
`c ⊗ r ↦ r • g(c)`, through `MMP.Mori.Divisor.tensorEquiv`. -/
def rDivisorTensorMap {G : Type*} [AddCommGroup G] (g : G →+ Divisor X) :
    G ⊗[ℤ] ℝ →+ RDivisor X :=
  (Divisor.tensorEquiv ℝ X).toAddMonoidHom.comp (g.toIntLinearMap.rTensor ℝ).toAddMonoidHom

/-- `rDivisorTensorMap g` sends `c ⊗ r` to `r • g(c)`. -/
theorem rDivisorTensorMap_tmul {G : Type*} [AddCommGroup G] (g : G →+ Divisor X) (c : G)
    (r : ℝ) : rDivisorTensorMap g (c ⊗ₜ r) = r • Divisor.toRDivisor (g c) := by
  classical
  ext E
  change (Divisor.tensorEquiv ℝ X (g c ⊗ₜ r)).coeff E = _
  rw [Divisor.coeff_tensorEquiv_tmul, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    zsmul_eq_mul, smul_eq_mul, mul_comm]

/-- `Ca(X) ⊗ ℝ → Div(X)_ℝ` is injective (`ℝ` is flat over `ℤ`). -/
theorem rDivisorTensorMap_cartierSubgroup_injective [IsLocallyNoetherian X] [IsNormal X] :
    Function.Injective (rDivisorTensorMap (Divisor.cartierSubgroup (X := X)).subtype) :=
  (Divisor.tensorEquiv ℝ X).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)

/-- The `ℝ`-divisor of an integral divisor `D` is `D` with its coefficients cast to `ℝ`. -/
theorem toRDivisor_eq_mapCoeffs (D : Divisor X) :
    Divisor.toRDivisor D = D.mapCoeffs (Int.cast : ℤ → ℝ) Int.cast_zero := by
  ext E
  rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_mapCoeffs]

/-- A dominant morphism from an irreducible scheme maps the generic point outside the support of
every divisor (condition `(∗)` of `MMP.Mori.Divisor.IsPullback`). -/
theorem map_componentGenericPoint_notMem_supp_of_isDominant {Y : Scheme.{u}}
    [IrreducibleSpace Y] (f : Y ⟶ X) [IsDominant f] (D : Divisor X)
    (Z : irreducibleComponents Y) : f (componentGenericPoint Y Z) ∉ D.supp := by
  intro h
  obtain ⟨E, -, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  have hZ : (Z.1 : Set Y) = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using Z.2
  have hgen : IsGenericPoint (componentGenericPoint Y Z) Set.univ := by
    have := isGenericPoint_componentGenericPoint Y Z
    rwa [hZ] at this
  have hfgen : closure {f (componentGenericPoint Y Z)} = Set.univ := by
    have := (hgen.image f.continuous).def
    rwa [Set.image_univ, f.denseRange.closure_range] at this
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
  have hall : ∀ y : X, y ≤ E.genericPoint := fun y => by
    refine specializes_iff_mem_closure.mpr ?_
    have hcl : closure {f (componentGenericPoint Y Z)} ⊆ closure {E.genericPoint} :=
      closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
    refine hcl ?_
    rw [hfgen]
    trivial
  have hmax : IsMax E.genericPoint := fun y _ => hall y
  have h0 := Order.coheight_eq_zero.mpr hmax
  rw [E.coheight_genericPoint] at h0
  exact one_ne_zero h0

end Helpers

section Presentation

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- **Presentations of `ℝ`-Cartier divisors are unique in `Ca(X) ⊗ ℝ`** (implicit in FA 2.2.2 and
2.5.1). Let `X` be a normal scheme and `Ca(X)` its group of Cartier divisors
(`MMP.Mori.Divisor.cartierSubgroup`). If Cartier divisors `L₁, …, L_m, M₁, …, M_p` and reals
`r_j, s_k` satisfy `∑ r_j L_j = ∑ s_k M_k` as `ℝ`-divisors, then
`∑ L_j ⊗ r_j = ∑ M_k ⊗ s_k` in `Ca(X) ⊗_ℤ ℝ`. -/
@[mmp "lem_fa2_r_cartier_presentation_unique"]
theorem sum_tmul_eq_of_sum_smul_eq {m p : ℕ} (L : Fin m → Divisor.cartierSubgroup (X := X))
    (r : Fin m → ℝ) (M : Fin p → Divisor.cartierSubgroup (X := X)) (s : Fin p → ℝ)
    (h : ∑ j, r j • Divisor.toRDivisor (L j : Divisor X) =
      ∑ k, s k • Divisor.toRDivisor (M k : Divisor X)) :
    ∑ j, (L j ⊗ₜ[ℤ] r j) = ∑ k, (M k ⊗ₜ[ℤ] s k) := by
  apply rDivisorTensorMap_cartierSubgroup_injective
  simpa only [map_sum, rDivisorTensorMap_tmul, AddSubgroup.coe_subtype] using h

end Presentation

section Pullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y] [CompactSpace Y]

/-- The pull-back `L ↦ f^*L` along a dominant morphism, as an additive map `Ca(X) → Div(Y)`. -/
def cartierPullbackHom (f : Y ⟶ X) [IsDominant f] :
    Divisor.cartierSubgroup (X := X) →+ Divisor Y where
  toFun L := (L : Divisor X).pullback L.2
    (map_componentGenericPoint_notMem_supp_of_isDominant f (L : Divisor X))
  map_zero' := Divisor.IsPullback.pullback_eq Divisor.isCartier_zero (Divisor.isPullback_zero _)
  map_add' L₁ L₂ := Divisor.IsPullback.pullback_eq (L₁ + L₂).2
    (Divisor.IsPullback.add L₁.2 L₂.2 _ (Divisor.isPullback_pullback _ _)
      (Divisor.isPullback_pullback _ _))

omit [IsIntegral X] in
/-- `cartierPullbackHom f` sends a Cartier divisor `L` to any pull-back `L'` of `L` along `f`. -/
theorem cartierPullbackHom_apply (f : Y ⟶ X) [IsDominant f] {L : Divisor X} (hL : L.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp} {L' : Divisor Y}
    (h : L.IsPullback f hB L') : cartierPullbackHom f ⟨L, hL⟩ = L' :=
  Divisor.IsPullback.pullback_eq hL h

omit [IsIntegral X] in
/-- Every pull-back of `D = ∑ r_j L_j` is `∑ r_j f^*L_j`, the image of `∑ L_j ⊗ r_j`. -/
theorem IsRCartierPullback.eq_rDivisorTensorMap (f : Y ⟶ X) [IsDominant f] {D : RDivisor X}
    {G : RDivisor Y} (hG : IsRCartierPullback f D G) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor.cartierSubgroup (X := X)),
      D = ∑ j, r j • Divisor.toRDivisor (L j : Divisor X) ∧
      G = rDivisorTensorMap (cartierPullbackHom f) (∑ j, L j ⊗ₜ[ℤ] r j) := by
  obtain ⟨m, r, L, L', hL, rfl, hL', rfl⟩ := hG
  refine ⟨m, r, fun j => ⟨L j, hL j⟩, rfl, ?_⟩
  simp only [map_sum, rDivisorTensorMap_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨hB, hp⟩ := hL' j
  rw [cartierPullbackHom_apply f (hL j) hp]

omit [IsIntegral X] in
/-- **Uniqueness of the pull-back of an `ℝ`-Cartier divisor** along a dominant morphism. -/
theorem IsRCartierPullback.eq (f : Y ⟶ X) [IsDominant f] {D : RDivisor X} {G₁ G₂ : RDivisor Y}
    (h₁ : IsRCartierPullback f D G₁) (h₂ : IsRCartierPullback f D G₂) : G₁ = G₂ := by
  obtain ⟨m, r, L, hD₁, rfl⟩ := h₁.eq_rDivisorTensorMap f
  obtain ⟨p, s, M, hD₂, rfl⟩ := h₂.eq_rDivisorTensorMap f
  rw [sum_tmul_eq_of_sum_smul_eq L r M s (hD₁.symm.trans hD₂)]

omit [IsIntegral X] in
/-- **FA 2.5.1: the pull-back of an `ℝ`-Cartier divisor exists and is unique.** Let
`f : Y ⟶ X` be a dominant morphism of normal integral schemes (normal varieties, in the source),
`Y` quasi-compact, and `D` an
`ℝ`-Cartier divisor on `X`. Then `D` has exactly one pull-back `f^*D`
(`MMP.Flips.IsRCartierPullback`). -/
@[mmp "lem_fa2_r_cartier_pullback_unique"]
theorem existsUnique_isRCartierPullback (f : Y ⟶ X) [IsDominant f] {D : RDivisor X}
    (hD : IsCartierCombination D) : ∃! G : RDivisor Y, IsRCartierPullback f D G := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  have hG : IsRCartierPullback f (∑ j, r j • Divisor.toRDivisor (L j)) (∑ j, r j •
      Divisor.toRDivisor
        ((L j).pullback (hL j) (map_componentGenericPoint_notMem_supp_of_isDominant f (L j)))) :=
    ⟨m, r, L, _, hL, by simp only [toRDivisor_eq_mapCoeffs],
      fun j => ⟨_, Divisor.isPullback_pullback (hL j) _⟩, rfl⟩
  exact ⟨_, hG, fun G h => IsRCartierPullback.eq f h hG⟩

omit [IsIntegral X] [IsIntegral Y] [CompactSpace Y] in
/-- **FA 2.5.1, `ℚ`-divisors.** If `D` is a `ℚ`-divisor on `X` and `mD = L` is an integral
Cartier divisor (`m > 0`) with pull-back `f^*L = L'`, then `f^*D = (1/m) f^*(mD)`: the
`ℝ`-divisor `(1/m) L'` is the pull-back of `D`. -/
@[mmp "lem_fa2_r_cartier_pullback_unique"]
theorem isRCartierPullback_of_zsmul_eq (f : Y ⟶ X) [IsDominant f] {D : QDivisor X} {m : ℕ}
    (hm : 0 < m) {L : Divisor X} (hL : L.IsCartier)
    (hmD : (m : ℤ) • D = Divisor.toQDivisor L) {L' : Divisor Y}
    (hL' : ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp,
      L.IsPullback f hB L') :
    IsRCartierPullback f (QDivisor.toRDivisor D) ((1 / (m : ℝ)) • Divisor.toRDivisor L') := by
  obtain ⟨hB, hp⟩ := hL'
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => L, fun _ => L', fun _ => hL, ?_, fun _ => ⟨hB, hp⟩,
    by rw [Fin.sum_univ_one]⟩
  rw [Fin.sum_univ_one]
  ext E
  have h := congrArg (fun G : QDivisor X => G.coeff E) hmD
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
    Int.cast_natCast] at h
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h' : ((D.coeff E : ℚ) : ℝ) * m = (L.coeff E : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at this
    linarith
  field_simp
  linarith

end Pullback

end MMP.Flips

/-! ### Discrepancies do not depend on the choices -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] in
/-- The coefficient of an `ℝ`-combination `∑ r_j L_j` of divisors along a prime divisor. -/
theorem coeff_sum_smul_toRDivisor {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (Γ : Mori.PrimeDivisor X) :
    (∑ j, r j • Divisor.toRDivisor (L j)).coeff Γ = ∑ j, r j * ((L j).coeff Γ : ℝ) := by
  simp only [DivisorWithCoeffs.coeff, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => congrArg _ (Divisor.coeff_toRDivisor (L j) Γ)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
omit [CompactSpace X] [LocallyOfFiniteType sX] in
/-- **The discrepancy computed with choices depends only on the valuation.** For divisors `D`,
`D'` over `X` with the same valuation, nonzero rational top forms `ω`, `ω'` and presentations
`div(ω) + B = ∑ r_i C_i`, `div(ω') + B = ∑ r₂_j C₂_j` by Cartier divisors (coefficientwise), with
pull-backs `C'_i`, `C₂'_j`, the numbers `ord_D(f^*ω) - ∑ r_i coeff_D(C'_i)` and
`ord_{D'}(f'^*ω') - ∑ r₂_j coeff_{D'}(C₂'_j)` coincide. (The argument of
`MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq`.) -/
theorem ordPullback_sub_sum_eq_of_valuation_eq [PerfectField k] (hX : IsNormalVariety k sX)
    {n : ℕ} (hn : topologicalKrullDim X = n) {B : RDivisor X} {D D' : DivisorOver k sX}
    (hv : D.valuation = D'.valuation) {ω ω' : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hω0' : ω' ≠ 0) {m m₂ : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X} {r₂ : Fin m₂ → ℝ}
    {C₂ : Fin m₂ → Divisor X} (hCc : ∀ i, (C i).IsCartier) (hCc₂ : ∀ j, (C₂ j).IsCartier)
    (hsum : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ)
    (hsum₂ : ∀ Γ : Mori.PrimeDivisor X,
      (Γ.ordForm ω' : ℝ) + B.coeff Γ = ∑ j, r₂ j * (C₂ j).coeff Γ)
    (C' : Fin m → Divisor D.Y) (C₂' : Fin m₂ → Divisor D'.Y)
    (hpb : haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      ∀ i, ∃ hC, (C i).IsPullback D.f hC (C' i))
    (hpb₂ : haveI := D'.isLocallyNoetherian
      haveI := D'.isNormal
      ∀ j, ∃ hC, (C₂ j).IsPullback D'.f hC (C₂' j)) :
    (D.ordPullback ω : ℝ) - ∑ i, r i * (C' i).coeff D.E =
      (D'.ordPullback ω' : ℝ) - ∑ j, r₂ j * (C₂' j).coeff D'.E := by
  classical
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  let := MMP.Mori.functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hX hn
  have hcen := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hv
  have hω' := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv ω'
  set x := D.f D.E.genericPoint with hx
  choose V hV φ hφ using fun i => hCc i x
  choose V₂ hV₂ φ₂ hφ₂ using fun j => hCc₂ j x
  let Z0 := MMP.Mori.pointComponent x
  let g : Fin m → X.functionField := fun i =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ i : MMP.Mori.RationalFunctions X))
  let g₂ : Fin m₂ → X.functionField := fun j =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ₂ j : MMP.Mori.RationalFunctions X))
  have hg : ∀ i, g i ≠ 0 := fun i => ((φ i).isUnit.map _).ne_zero
  have hg₂ : ∀ j, g₂ j ≠ 0 := fun j => ((φ₂ j).isUnit.map _).ne_zero
  set cω := (MMP.Mori.ZTensorPower.basis β 1).repr ω () with hcω
  set cω' := (MMP.Mori.ZTensorPower.basis β 1).repr ω' () with hcω'
  have hcω0 : cω ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω0
  have hcω0' : cω' ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω0'
  let G : Option (Option (Fin m ⊕ Fin m₂)) → X.functionField := fun j =>
    Option.elim j cω fun j => Option.elim j cω' fun j => Sum.elim g g₂ j
  let w : Option (Option (Fin m ⊕ Fin m₂)) → ℝ := fun j =>
    Option.elim j 1 fun j => Option.elim j (-1) fun j => Sum.elim (fun i => -r i) r₂ j
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | i | j)
    exacts [hcω0, hcω0', hg i, hg₂ j]
  have hZ : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.component = Z0 := fun Γ => Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  have hgΓ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (i : Fin m), x ∈ Γ.support →
      X.ord (g i) Γ.genericPoint = (C i).coeff Γ := by
    intro Γ i hΓ
    rw [hφ i Γ ⟨x, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have hgΓ₂ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (j : Fin m₂), x ∈ Γ.support →
      X.ord (g₂ j) Γ.genericPoint = (C₂ j).coeff Γ := by
    intro Γ j hΓ
    rw [hφ₂ j Γ ⟨x, hΓ, hV₂ j⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E G hG w
    fun Γ hΓ => by
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd β
    have e1 : (Γ.ordForm ω : ℝ) = X.ord cω Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω hω0)
    have e2 : (Γ.ordForm ω' : ℝ) = X.ord cω' Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω' hω0')
    simp only [Fintype.sum_option, Fintype.sum_sum_type, G, w, Option.elim, Sum.elim_inl,
      Sum.elim_inr]
    simp_rw [hgΓ Γ _ hΓ, hgΓ₂ Γ _ hΓ]
    have e5 : ∑ i, ((C i).coeff Γ : ℝ) * -r i = -∑ i, r i * ((C i).coeff Γ : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e6 : ∑ j, ((C₂ j).coeff Γ : ℝ) * r₂ j = ∑ j, r₂ j * ((C₂ j).coeff Γ : ℝ) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e5, e6]
    linear_combination hsum Γ - hsum₂ Γ - e1 + e2
  have hcoeff : ∀ i, ((C' i).coeff D.E : ℝ) =
      D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint := by
    intro i
    obtain ⟨hC, hCp⟩ := hpb i
    exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCp (hφ i) D.E (hV i) Z0
  have hcoeff₂ : ∀ j, ((C₂' j).coeff D'.E : ℝ) =
      D.Y.ord (functionFieldMap D.f (g₂ j)) D.E.genericPoint := by
    intro j
    obtain ⟨hC, hCp⟩ := hpb₂ j
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCp (hφ₂ j) D'.E (hcen ▸ hV₂ j) Z0,
      MMP.Threefold.Bridges.ord_functionFieldMap_eq_of_valuationOver_eq D.E D'.E hv (hg₂ j)]
  have h1 : (D.ordPullback ω : ℝ) =
      D.Y.ord (functionFieldMap D.f cω) D.E.genericPoint + N := by
    exact_mod_cast (by simpa using hN 1 ω hω0)
  have h2 : (D'.ordPullback ω' : ℝ) =
      D.Y.ord (functionFieldMap D.f cω') D.E.genericPoint + N := by
    rw [← hω']
    exact_mod_cast (by simpa using hN 1 ω' hω0')
  simp only [Fintype.sum_option, Fintype.sum_sum_type, G, w, Option.elim, Sum.elim_inl,
    Sum.elim_inr] at key
  simp_rw [hcoeff, hcoeff₂]
  have e5 : ∑ i, (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) * -r i =
      -∑ i, r i * (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e6 : ∑ j, (D.Y.ord (functionFieldMap D.f (g₂ j)) D.E.genericPoint : ℝ) * r₂ j =
      ∑ j, r₂ j * (D.Y.ord (functionFieldMap D.f (g₂ j)) D.E.genericPoint : ℝ) :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e5, e6] at key
  linear_combination h1 - h2 + key

/-- **FA Def.-Prop. 2.5.2: the discrepancy does not depend on the choices made.** Let `X` be a
normal variety of dimension `n` over a perfect field `k` and `D_X` an `ℝ`-divisor on `X`. Let
`(Y, f, E)` and `(Y', f', E')` be divisors over `X` with `ord_E = ord_{E'}`, and let `ω, ω'` be
nonzero rational `n`-forms with `div_X(ω) + D_X` and `div_X(ω') + D_X` `ℝ`-Cartier, each with a
chosen presentation `∑ r_j L_j`, `∑ r'_j L'_j`. Then `a_ω(E, D_X)`, computed on `(Y, f, E)`,
equals `a_{ω'}(E', D_X)`, computed on `(Y', f', E')`. -/
@[mmp "lem_fa2_discrepancy_well_defined"]
theorem IsDiscrepancyWith.eq [PerfectField k] {n : ℕ} {D_X : RDivisor X}
    {ω ω' : RationalPluriForms sX n 1} {m m' : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {r' : Fin m' → ℝ} {L' : Fin m' → Divisor X} {E E' : ProperDivisorOver k sX} {a a' : ℝ}
    (h : IsDiscrepancyWith sX n D_X ω r L E a) (h' : IsDiscrepancyWith sX n D_X ω' r' L' E' a')
    (hE : E.valuation = E'.valuation) : a = a' := by
  obtain ⟨hX, hn, hω0, hLc, hsum, C', hpb, rfl⟩ := h
  obtain ⟨-, -, hω0', hLc', hsum', C₂', hpb', rfl⟩ := h'
  have hco : ∀ {p : ℕ} {ρ : Fin p → ℝ} {M : Fin p → Divisor X} {τ : RationalPluriForms sX n 1},
      Divisor.toRDivisor (divisorOfForm τ) + D_X = ∑ j, ρ j • Divisor.toRDivisor (M j) →
      ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm τ : ℝ) + D_X.coeff Γ = ∑ j, ρ j * (M j).coeff Γ := by
    intro p ρ M τ hs Γ
    simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      coeff_sum_smul_toRDivisor] using congrArg (fun D : RDivisor X => D.coeff Γ) hs
  exact ordPullback_sub_sum_eq_of_valuation_eq hX hn hE hω0 hω0' hLc hLc' (hco hsum)
    (hco hsum') C' C₂' hpb hpb'

/-- **FA 2.5.2, the general discrepancy is well defined**: `a(F, D_X)` has at most one value. -/
@[mmp "lem_fa2_discrepancy_well_defined"]
theorem IsDiscrepancy.eq [PerfectField k] {n : ℕ} {K : Divisor X} {D_X : RDivisor X}
    {F : Valuation X.functionField ℤᵐ⁰} {a a' : ℝ}
    (h : IsDiscrepancy sX n K D_X F a) (h' : IsDiscrepancy sX n K D_X F a') : a = a' := by
  obtain ⟨-, -, -, E, ω, m, r, L, hEF, -, hw⟩ := h
  obtain ⟨-, -, -, E', ω', m', r', L', hEF', -, hw'⟩ := h'
  exact hw.eq hw' (hEF.trans hEF'.symm)

/-- **FA 2.5.4, `a(P, D_X) = -c(P)`.** Let `X` be a normal variety of dimension `n` over a perfect
field, `ω ≠ 0` a rational `n`-form whose divisor `K_X = div_X(ω)` is a canonical divisor, and
`D_X` an `ℝ`-divisor with `K_X + D_X` `ℝ`-Cartier. For a prime divisor `P` of `X` with coefficient
`c(P)` in `D_X`, the discrepancy of `ord_P` is `a(ord_P, D_X) = -c(P)`. -/
@[mmp "lem_fa2_discrepancy_nonexceptional"]
theorem isDiscrepancy_divisorialValuation [PerfectField k] (hX : IsNormalVariety k sX) {n : ℕ}
    {D_X : RDivisor X} (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D_X))
    (P : Mori.PrimeDivisor X) :
    IsDiscrepancy sX n (divisorOfForm ω) D_X P.divisorialValuation (-D_X.coeff P) := by
  have hn := hK.topologicalKrullDim_eq
  let E : ProperDivisorOver k sX :=
    ⟨DivisorOver.ofPrimeDivisor k hX P, (inferInstance : IsProper (𝟙 X))⟩
  have hval : E.valuation = P.divisorialValuation := Valuation.ext fun g => by
    change P.divisorialValuation (functionFieldMap (𝟙 X) g) = _
    rw [functionFieldMap_id_apply]
  obtain ⟨m, r, L, hLc, hsum⟩ := hKD
  have hsum' : Divisor.toRDivisor (divisorOfForm ω) + D_X =
      ∑ j, r j • Divisor.toRDivisor (L j) := hsum
  refine ⟨hK, ⟨m, r, L, hLc, hsum⟩,
    ⟨⟨X, sX, hX, P, letI := functionFieldAlgebra sX; AlgEquiv.refl, Valuation.ext fun g => rfl⟩,
    E, hval⟩, E, ω, m, r, L, hval, rfl, hX, hn, hω, hLc, hsum', ?_⟩
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := inferInstanceAs (CompactSpace X)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  refine ⟨L', fun j => ⟨_, hL' j⟩, ?_⟩
  have hco : ∀ j, ((L' j).coeff E.E : ℝ) = (L j).coeff P := by
    intro j
    obtain ⟨U, hU, φ, hφ⟩ := hLc j P.genericPoint
    have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hL' j) hφ E.E hU
      (MMP.Mori.pointComponent P.genericPoint)
    have h2 := hφ P ((P.genericPoint_mem_iff U).mp hU)
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h2
    have hZ : P.component = MMP.Mori.pointComponent P.genericPoint := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hZ] at h2
    change (L' j).coeff P = X.ord (functionFieldMap (𝟙 X) _) P.genericPoint at h1
    rw [functionFieldMap_id_apply] at h1
    exact_mod_cast h1.trans h2.symm
  have hord : E.toDivisorOver.ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P ω
  have hP := congrArg (fun D : RDivisor X => D.coeff P) hsum'
  simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] at hP
  simp_rw [hco, hord]
  linarith

/-- **FA 2.5.4**: any value of the discrepancy `a(ord_P, D_X)` of a prime divisor `P` of `X` is
`-c(P)`. -/
@[mmp "lem_fa2_discrepancy_nonexceptional"]
theorem IsDiscrepancy.eq_neg_coeff [PerfectField k] {n : ℕ} {K : Divisor X} {D_X : RDivisor X}
    {P : Mori.PrimeDivisor X} {a : ℝ} (h : IsDiscrepancy sX n K D_X P.divisorialValuation a) :
    a = -D_X.coeff P := by
  obtain ⟨hK, hKD, -, E, ω, m, r, L, -, rfl, hw⟩ := id h
  exact h.eq (isDiscrepancy_divisorialValuation hw.1 ω hw.2.2.1 hK hKD P)

end Discrepancy

end MMP.Flips

namespace MMP.Flips

open MMP.Mori

/-! ### The discrepancy formula -/

private theorem topologicalKrullDim_closure_singleton_add_coheight {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (x : Y) :
    topologicalKrullDim (closure {x} : Set Y) + Order.coheight x = topologicalKrullDim Y := by
  let _ : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint x)
  rwa [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint] at h

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        exact ENat.top_ne_natCast n (WithBot.coe_injective h)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have e1 : (((d : ℕ∞) : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞)) ↔ d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le]
        rw [e1]
        constructor
        · intro h2
          exact_mod_cast (show 2 ≤ c by omega)
        · intro h2
          have : 2 ≤ c := by exact_mod_cast h2
          omega

private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If a representative `g'` of `φ : X ⤏ Y` is defined at the generic point of a prime divisor `P`
of `X`, the strict transform of `P` under `φ` is the closure of `g'(η_P)`. -/
theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If the strict transform of a prime divisor `P` under `φ` is the prime divisor `E`, then the
generic point of `E` is the image of `η_P` under any representative of `φ` defined there. -/
theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- Converse of `genericPoint_eq_of_transformPrimeDivisor_eq_some`: if a representative `g'` of
`φ : X ⤏ Y` defined at `η_P` sends it to the generic point of the prime divisor `E`, then the
strict transform of `P` under `φ` is `E`. -/
theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- The coefficient of `P` in the linear extension of a partial map `φ` on prime divisors is `0`
when no prime divisor is sent to `P`. -/
theorem mapPrimeDivisors_apply_eq_zero_of_forall_ne {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor Y} (h : ∀ E, φ E ≠ some P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D P = 0 := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hE : φ E with _ | E'
    · rfl
    · have hne : E' ≠ P := fun he => h E (by rw [hE, he])
      exact Finsupp.single_eq_of_ne' hne

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
theorem map_genericPoint_eq_of_transformPrimeDivisor_inverse {X Y : Scheme.{u}} [IsReduced X]
    [IsReduced Y] [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, if `f` sends the
generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`, then the strict
transform of `P` under `f⁻¹` is `E`. -/
theorem transformPrimeDivisor_inverse_of_map_genericPoint_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (f ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : Mori.RationalMap.DefinedAt (Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom (Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- The prime divisors of `Y` exceptional over `X` for a birational morphism `f : Y ⟶ X` are
finitely many: their generic points lie outside an open subset on which `f` is an open
immersion. -/
theorem finite_isExceptionalPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (hf : IsBirationalMorphism f) :
    {E : Mori.PrimeDivisor Y | IsExceptionalPrimeDivisor sX f E}.Finite := by
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  obtain ⟨e, he, -⟩ := hf.isInverse_inverse
  obtain ⟨y₀⟩ : Nonempty e.source := (e.dense_source.nonempty).to_subtype
  have hη : genericPoint Y ∈ e.source :=
    ((genericPoint_spec Y).mem_open_set_iff e.source.isOpen).mpr ⟨y₀.1, trivial, y₀.2⟩
  refine Set.Finite.of_finite_image
    ((MMP.Mori.finite_coheight_eq_one_mem_closure_notMem (genericPoint Y) e.source hη).subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨E, hE, rfl⟩
  refine ⟨by rw [(genericPoint_spec Y).def]; trivial, fun hmem => ?_, E.coheight_genericPoint⟩
  obtain ⟨hY, hf', hp, hE⟩ : IsExceptionalPrimeDivisor sX f E := hE
  have hE' : 2 ≤ Order.coheight (f E.genericPoint) :=
    (isExceptional_iff_two_le_coheight hn (ProperDivisorOver.mk ⟨Y, f, hY, hf', E⟩ hp)).mp hE
  let u : e.source.toScheme := ⟨E.genericPoint, hmem⟩
  have h1 : f E.genericPoint = (e.iso.hom ≫ e.target.ι) u := by
    rw [← source_ι_comp_eq_of_toRationalMap_eq f e he, Scheme.Hom.comp_apply]
    rfl
  have h2 : Order.coheight (f E.genericPoint) = 1 := by
    rw [h1, coheight_eq_of_isOpenImmersion, ← E.coheight_genericPoint,
      ← coheight_eq_of_isOpenImmersion e.source.ι]
    rfl
  rw [h2] at hE'
  exact absurd hE' (by decide)

/-- A prime divisor `E` of `Y` which is not exceptional over `X` for a proper birational morphism
`f : Y ⟶ X` lies over a prime divisor `P` of `X`, with `ord_E = ord_P`. -/
theorem exists_primeDivisor_of_not_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {E : Mori.PrimeDivisor Y}
    (hE : ¬ IsExceptionalPrimeDivisor sX f E) :
    ∃ P : Mori.PrimeDivisor X, f E.genericPoint = P.genericPoint ∧
      (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ inferInstance).valuation =
        P.divisorialValuation := by
  have hc : ¬ 2 ≤ codimension (ProperDivisorOver.mk (sX := sX) ⟨Y, f, hY, hf, E⟩
      inferInstance).toDivisorOver.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    exact fun h => hE ⟨hY, hf, inferInstance, (isExceptional_iff_two_le_coheight hn _).mpr h⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hc
  simp only [not_forall, not_not] at hc
  obtain ⟨P, hv⟩ := hc
  refine ⟨P, MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv, ?_⟩
  change (ProperDivisorOver.mk (sX := sX) ⟨Y, f, hY, hf, E⟩
    inferInstance).toDivisorOver.valuation = _
  rw [hv]
  ext φ
  change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

/-- For a birational morphism `f : Y ⟶ X` from a normal variety, the valuation `ord_E` of a prime
divisor `E` of `Y` is a divisor of the function field `k(X)`. -/
theorem isDivisorOfFunctionField_valuation_mk {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X)
    [IsProper f] (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : Mori.PrimeDivisor Y) :
    IsDivisorOfFunctionField k sX
      (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ inferInstance).valuation := by
  have : IsDominant f := hf.isDominant
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  exact ⟨Y, f ≫ sX, hY, E, AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom k X.functionField Y.functionField) hf.functionFieldMap_bijective, rfl⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **FA Def.-Prop. 2.5.1, the discrepancy formula.** Let `X` be a normal variety of dimension `n`
over a perfect field, `D_X` an `ℝ`-divisor on `X`, `ω ≠ 0` a rational `n`-form with
`K_X = div_X(ω)` a canonical divisor and `K_X + D_X` `ℝ`-Cartier, and `f : Y ⟶ X` a proper
birational morphism from a normal variety `Y`; put `K_Y = div_Y(f^*ω)`. Then the prime divisors
`E` of `Y` exceptional over `X` are finitely many, `E₁, …, E_k`, and
`K_Y + f⁻¹_*(D_X) = f^*(K_X + D_X) + ∑ a(E_i, D_X) E_i`, where `f^*(K_X + D_X)` is the pull-back
of the `ℝ`-Cartier divisor `K_X + D_X` and `a(E_i, D_X)` the discrepancy of `ord_{E_i}`. -/
@[mmp "lem_fa2_discrepancy_formula"]
theorem discrepancy_formula [PerfectField k] (hX : IsNormalVariety k sX) {n : ℕ}
    (D_X : RDivisor X) (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D_X))
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType (f ≫ sX)] :
    ∃ (Ex : Finset (Mori.PrimeDivisor Y)) (a : Mori.PrimeDivisor Y → ℝ) (G : RDivisor Y),
      (∀ E, E ∈ Ex ↔ IsExceptionalPrimeDivisor sX f E) ∧
      IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D_X) G ∧
      (∀ E ∈ Ex, IsDiscrepancy sX n (divisorOfForm ω) D_X
        (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ inferInstance).valuation (a E)) ∧
      haveI : IsDominant f := hf.isDominant
      Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) +
          birationalInverseTransform f hf D_X =
        G + ∑ E ∈ Ex, Finsupp.single E (a E) := by
  classical
  have : IsDominant f := hf.isDominant
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (f ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  let DE : Mori.PrimeDivisor Y → ProperDivisorOver k sX := fun E =>
    ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ inferInstance
  have hexc : ∀ E, IsExceptionalPrimeDivisor sX f E ↔ 2 ≤ Order.coheight (f E.genericPoint) :=
    fun E => ⟨fun ⟨_, _, _, h⟩ => (isExceptional_iff_two_le_coheight hn (DE E)).mp h,
      fun h => ⟨hY, hf, inferInstance, (isExceptional_iff_two_le_coheight hn (DE E)).mpr h⟩⟩
  have hfin := finite_isExceptionalPrimeDivisor (sX := sX) hn f hf
  obtain ⟨G, hG, -⟩ := existsUnique_isRCartierPullback f hKD
  obtain ⟨m, r, L, L', hLc, hL, hLpb, hGdef⟩ := id hG
  let a : Mori.PrimeDivisor Y → ℝ := fun E =>
    ((DE E).toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * ((L' j).coeff E : ℝ)
  have hdisc : ∀ E, IsDiscrepancy sX n (divisorOfForm ω) D_X (DE E).valuation (a E) :=
    fun E => ⟨hK, hKD, ⟨isDivisorOfFunctionField_valuation_mk f hY hf E, DE E, rfl⟩, DE E, ω, m,
      r, L, rfl, rfl, hX, hn, hω, hLc, hL, L', hLpb, rfl⟩
  refine ⟨hfin.toFinset, a, G, fun E => by rw [Set.Finite.mem_toFinset]; rfl, hG,
    fun E _ => hdisc E, ?_⟩
  refine Finsupp.ext fun E => ?_
  have hKE : (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω))) E =
      ((DE E).toDivisorOver.ordPullback ω : ℝ) := rfl
  have hGE : G E = ∑ j, r j * ((L' j).coeff E : ℝ) := by
    rw [hGdef, Finsupp.finsetSum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rfl
  have hsum : (∑ E' ∈ hfin.toFinset, Finsupp.single E' (a E')) E =
      if IsExceptionalPrimeDivisor sX f E then a E else 0 := by
    rw [Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp only [Set.Finite.mem_toFinset]
    rfl
  rw [Finsupp.add_apply, Finsupp.add_apply, hKE, hGE, hsum]
  by_cases hE : IsExceptionalPrimeDivisor sX f E
  · simp only [hE, ↓reduceIte]
    have h0 : (birationalInverseTransform f hf D_X) E = 0 := by
      refine mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP => ?_) D_X
      rw [hexc, map_genericPoint_eq_of_transformPrimeDivisor_inverse hf hP,
        P.coheight_genericPoint] at hE
      exact absurd hE (by decide)
    rw [h0]
    simp only [a]
    ring
  · simp only [hE, ↓reduceIte]
    obtain ⟨P, hP, hv⟩ := exists_primeDivisor_of_not_isExceptionalPrimeDivisor hX hn f hY hf hE
    have h1 : (birationalInverseTransform f hf D_X) E = D_X P :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
        (transformPrimeDivisor_inverse_of_map_genericPoint_eq hX f hY.1 hf hP)
        (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          ((map_genericPoint_eq_of_transformPrimeDivisor_inverse hf hP').symm.trans hP)) D_X
    have h2 := hdisc E
    rw [hv] at h2
    have h3 := IsDiscrepancy.eq_neg_coeff h2
    rw [h1]
    simp only [a] at h3
    have h4 : D_X.coeff P = D_X P := rfl
    linarith

end MMP.Flips
