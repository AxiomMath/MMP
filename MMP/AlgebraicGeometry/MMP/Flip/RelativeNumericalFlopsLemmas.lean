/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk

/-!
# Auxiliary results for the miscellaneous definitions of *Flips and abundance*

## Main results

* `MMP.Flips.topologicalKrullDim_le_of_specializes_imp_eq`: a continuous map from a quasi-sober
  space to a `T₀` space that is injective on every specialization `a ⤳ b` does not decrease
  the Krull dimension.
* `MMP.Flips.exists_map_componentGenericPoint_eq_of_isFinite_of_isDominant`: a finite dominant
  morphism of pure-dimensional schemes of finite type over a field maps generic points of
  irreducible components to generic points.
* `MMP.Flips.supp_eq_preimage_supp_of_isPullback`: the support of the pull-back of an effective
  Cartier divisor is the preimage of its support.
* `MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range`: the dimension of the source is the
  dimension of the generic fibre plus that of the closure of the image.
* `MMP.Flips.isNormalVariety_fiber_genericPoint`: the generic fibre of a morphism of varieties
  with normal source is a normal variety.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

universe u

namespace MMP.Flips

/-- A continuous map `f : X → Y` from a quasi-sober space to a `T₀` space such that `a ⤳ b` and
`f a = f b` imply `a = b` satisfies `dim X ≤ dim Y`. -/
theorem topologicalKrullDim_le_of_specializes_imp_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober X] [T0Space Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ ⦃a b : X⦄, a ⤳ b → f a = f b → a = b) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  let g : IrreducibleCloseds X → IrreducibleCloseds Y := fun T =>
    ⟨closure (f '' T), (T.isIrreducible.image f hf.continuousOn).closure, isClosed_closure⟩
  have hg : StrictMono g := by
    intro T₁ T₂ hlt
    refine lt_of_le_of_ne (closure_mono (Set.image_mono hlt.le)) fun heq => hlt.ne ?_
    have hξ₁ := T₁.isIrreducible.isGenericPoint_genericPoint T₁.isClosed
    have hξ₂ := T₂.isIrreducible.isGenericPoint_genericPoint T₂.isClosed
    have hi₁ := hξ₁.image hf
    have hi₂ := hξ₂.image hf
    have hcl : closure (f '' T₁) = closure (f '' T₂) :=
      congrArg (fun T : IrreducibleCloseds Y => (T : Set Y)) heq
    rw [← hcl] at hi₂
    have := h (hξ₂.specializes (hlt.le hξ₁.mem)) (hi₁.eq hi₂).symm
    ext x
    rw [← hξ₁.def, ← hξ₂.def, this]
  exact Order.krullDim_le_of_strictMono g hg

/-- A locally quasi-finite morphism (for instance a finite one) has no specializations inside a
fibre: if `a ⤳ b` and `p a = p b`, then `a = b`. -/
theorem eq_of_specializes_of_locallyQuasiFinite {X X' : Scheme.{u}} (p : X' ⟶ X)
    [LocallyQuasiFinite p] {a b : X'} (hab : a ⤳ b) (heq : p.base a = p.base b) : a = b := by
  have := (p.isDiscrete_preimage_singleton (p.base b)).to_subtype
  have h : (⟨a, heq⟩ : ↥(p.base ⁻¹' {p.base b})) ⤳ ⟨b, rfl⟩ :=
    (subtype_specializes_iff _ _).mpr hab
  have := specializes_iff_forall_open.mp h {⟨b, rfl⟩} (isOpen_discrete _) rfl
  exact congrArg Subtype.val this

/-- **A finite dominant morphism of pure-dimensional schemes of finite type over a field maps
generic points of irreducible components to generic points** (the aside of FA 16.3.5). -/
theorem exists_map_componentGenericPoint_eq_of_isFinite_of_isDominant (k : Type u) [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (p : X' ⟶ X)
    [IsFinite p] [IsDominant p]
    (hX : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = topologicalKrullDim X)
    (hX' : ∀ Z ∈ irreducibleComponents X', topologicalKrullDim Z = topologicalKrullDim X')
    (Z' : irreducibleComponents X') : ∃ Z : irreducibleComponents X,
      p.base (componentGenericPoint X' Z') = componentGenericPoint X Z := by
  set y := p.base (componentGenericPoint X' Z')
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  refine ⟨Z, ?_⟩
  have hZcl : IsClosed Z.1 := isClosed_of_mem_irreducibleComponents _ Z.2
  have hyZ : closure {y} ⊆ Z.1 :=
    hZcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
  have hZ'cl : IsClosed Z'.1 := isClosed_of_mem_irreducibleComponents _ Z'.2
  -- `dim Z' ≤ dim \overline{\{y\}}`
  have hmaps : Set.MapsTo p.base Z'.1 (closure {y}) := by
    intro x hx
    rw [← (isGenericPoint_componentGenericPoint X' Z').def] at hx
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hx).map p.base.hom.continuous)
  have h1 : topologicalKrullDim Z'.1 ≤ topologicalKrullDim (closure {y} : Set X) := by
    have : QuasiSober Z'.1 := hZ'cl.isClosedEmbedding_subtypeVal.quasiSober
    refine topologicalKrullDim_le_of_specializes_imp_eq
      (f := hmaps.restrict) (p.base.hom.continuous.restrict hmaps) ?_
    intro a b hab heq
    exact Subtype.ext (eq_of_specializes_of_locallyQuasiFinite p
      ((subtype_specializes_iff _ _).mp hab) (congrArg Subtype.val heq))
  -- `dim X' = dim X`
  have : Surjective p := ⟨fun x => by
    have hx := (isDominant_iff p).mp ‹IsDominant p› x
    rwa [p.isClosedMap.isClosed_range.closure_eq] at hx⟩
  have hdim : topologicalKrullDim X' = topologicalKrullDim X :=
    topologicalKrullDim_eq_of_isIntegralHom_of_surjective p
  -- `dim Z` is finite
  have hZgen := isGenericPoint_componentGenericPoint X Z
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim Z.1 = n := by
    rw [← hZgen.def]
    exact ⟨_, Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX _⟩
  by_contra hne
  have hss : closure {y} ⊂ Z.1 := hyZ.ssubset_of_ne fun h => hne (hZgen.eq h).symm
  have h2 : topologicalKrullDim (closure {y} : Set X) < n := by
    rw [topologicalKrullDim, Order.krullDim_lt_coe_iff]
    intro l
    have := _root_.succ_le_topologicalKrullDim_of_ssubset isClosed_closure Z.2.1 hss l
    rw [hn] at this
    exact_mod_cast Nat.lt_of_succ_le (by exact_mod_cast this)
  have h3 : topologicalKrullDim Z'.1 = n := by
    rw [hX' _ Z'.2, hdim, ← hX _ Z.2, hn]
  exact absurd (h3 ▸ h1) (not_le.mpr h2)

/-! ### The support of the pull-back of a Cartier divisor -/

section PullbackSupport

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

/-- A local equation `φ` on `U` of an effective divisor is regular on `U`: at `y ∈ U` on the
component `W`, `φ_W` is the image of an element of `𝒪_{Y,y}`. -/
theorem exists_stalk_eq_of_isLocalEquation_of_isEffective {B : Divisor Y}
    (hBe : DivisorWithCoeffs.IsEffective B)
    {U : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ) {y : Y} (hyU : y ∈ U)
    {W : irreducibleComponents Y} (hy : y ∈ W.1) :
    ∃ r : Y.presheaf.stalk y,
      (stalkToRationalFunctions Y hy).hom r = (φ : RationalFunctions Y) W := by
  let ψ : ToType ((rationalFunctionsPresheaf Y).obj (Opposite.op U)) :=
    fun Z => (φ : RationalFunctions Y) Z.1
  have hψ : Divisor.IsDivisorialSection (0 : Divisor Y) U ψ := by
    intro E hE
    refine Or.inr ?_
    change WithZero.exp (-(0 : ℤ)) ≤ E.valuation ((φ : RationalFunctions Y) E.component)
    rw [E.valuation_component, neg_zero, WithZero.exp_le_exp, ← hφ E hE]
    exact hBe E
  exact hψ.exists_stalk_eq hyU hy

/-- If `y ∈ U ∩ Supp B` for a local equation `φ` of `B` on `U`, then an element of `𝒪_{Y,y}` with
image `φ_W` is not a unit. -/
theorem not_isUnit_of_isLocalEquation_of_mem_supp {B : Divisor Y} {U : Y.Opens}
    {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ) {y : Y} (hyU : y ∈ U)
    (hyB : y ∈ B.supp) {W : irreducibleComponents Y} (hy : y ∈ W.1) {r : Y.presheaf.stalk y}
    (hr : (stalkToRationalFunctions Y hy).hom r = (φ : RationalFunctions Y) W) : ¬ IsUnit r := by
  intro hunit
  obtain ⟨E, hE0, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyB
  have hspec : E.genericPoint ⤳ y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact specializes_iff_mem_closure.mpr hyE
  obtain rfl : W = E.component :=
    eq_of_mem_irreducibleComponents hy (E.support_subset_component hyE)
  refine hE0 ?_
  rw [hφ E ⟨y, hyE, hyU⟩]
  refine E.ord_eq_zero_of_isUnit (hunit.map (Y.presheaf.stalkSpecializes hspec).hom) ?_
  rw [E.toComponent_stalkSpecializes hspec hy, hr]

variable [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}

/-- **The pull-back of an effective Cartier divisor has support at least `f⁻¹(Supp B)`.** -/
theorem preimage_supp_subset_supp_of_isPullback {B : Divisor Y} (hBc : B.IsCartier)
    (hBe : DivisorWithCoeffs.IsEffective B)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') :
    f.base ⁻¹' (B.supp : Set Y) ⊆ B'.supp := by
  intro x hx
  by_contra hxB'
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f x)
  obtain ⟨Z, hxZ⟩ : ∃ Z : irreducibleComponents X, x ∈ Z.1 :=
    ⟨pointComponent x, mem_pointComponent x⟩
  have hZspec : componentGenericPoint X Z ⤳ x :=
    (isGenericPoint_componentGenericPoint X Z).specializes hxZ
  have hsp' : f (componentGenericPoint X Z) ⤳ f x := f.base.hom.map_specializes hZspec
  set W := pointComponent (f (componentGenericPoint X Z))
  have hW : f (componentGenericPoint X Z) ∈ W.1 := mem_pointComponent _
  have hfxW : f x ∈ W.1 := hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  have hZU : f (componentGenericPoint X Z) ∈ U := hsp'.mem_open U.isOpen hU
  obtain ⟨r, hr⟩ := exists_stalk_eq_of_isLocalEquation_of_isEffective hBe hφ hU hfxW
  have hrnu := not_isUnit_of_isLocalEquation_of_mem_supp hφ hU hx hfxW hr
  -- the unit `f^*φ` of the component `Z`, extended by `1` to a unit of `K(X)`
  set u := pullbackComponent f hB hφ Z hZU with hu
  let ψ : (RationalFunctions X)ˣ :=
    (RationalFunctions.unitsEquiv X).symm (Function.update 1 Z u)
  have hψZ : (ψ : RationalFunctions X) Z = u := by
    simp [ψ, RationalFunctions.unitsEquiv]
  have hord : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → E.ord ψ = 0 := by
    intro E hxE
    have hcoeff : B'.coeff E = 0 := by
      by_contra hne
      exact hxB' (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)
    obtain rfl : Z = E.component :=
      eq_of_mem_irreducibleComponents hxZ (E.support_subset_component hxE)
    rw [h U φ hφ E ⟨x, hxE, hU⟩] at hcoeff
    rw [Mori.PrimeDivisor.ord_eq_ordUnit]
    convert hcoeff using 2
    exact Units.ext hψZ
  obtain ⟨c, hc⟩ := exists_unit_stalk_of_forall_ord_eq_zero hxZ ψ hord
  rw [hψZ] at hc
  obtain ⟨a', ha'⟩ := hφ.exists_unit_stalk hZU (hB Z) hW
  have hra : (Y.presheaf.stalkSpecializes hsp').hom r = a' := by
    apply stalkToRationalFunctions_injective hW
    rw [ha', ← hr]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  have hu' : (u : X.presheaf.stalk (componentGenericPoint X Z)) =
      (stalkToRationalFunctions X hxZ).hom ((f.stalkMap x).hom r) := by
    rw [hu, pullbackComponent_eq hB hφ hZU hW a' ha']
    change (f.stalkMap (componentGenericPoint X Z)).hom
      (a' : Y.presheaf.stalk (f (componentGenericPoint X Z))) = _
    rw [← hra, Scheme.Hom.stalkSpecializes_stalkMap_apply]
    rfl
  have hcr : (c : X.presheaf.stalk x) = (f.stalkMap x).hom r :=
    stalkToRationalFunctions_injective hxZ (hc.trans hu')
  exact hrnu ((isUnit_map_iff (f.stalkMap x).hom r).mp (hcr ▸ c.isUnit))

/-- **The support of the pull-back of a Cartier divisor lies over its support.** -/
theorem supp_subset_preimage_supp_of_isPullback {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') :
    (B'.supp : Set X) ⊆ f.base ⁻¹' (B.supp : Set Y) := by
  intro x hx
  obtain ⟨E, hE0, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  have hEx : E.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    exact specializes_iff_mem_closure.mpr hxE
  refine (f.base.hom.map_specializes hEx).mem_closed (B.isClosed_supp) ?_
  by_contra hnot
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  have hsp : componentGenericPoint X E.component ⤳ E.genericPoint := E.specializes_genericPoint
  have hsp' : f (componentGenericPoint X E.component) ⤳ f E.genericPoint :=
    f.base.hom.map_specializes hsp
  set W := pointComponent (f (componentGenericPoint X E.component))
  have hW : f (componentGenericPoint X E.component) ∈ W.1 := mem_pointComponent _
  have hyW : f E.genericPoint ∈ W.1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hU hnot hyW
  let c' : (Y.presheaf.stalk (f (componentGenericPoint X E.component)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes hsp').hom.toMonoidHom a
  have hc' : (stalkToRationalFunctions Y hW).hom c' = (φ : RationalFunctions Y) W := by
    rw [← ha]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom
        a.val = (Y.presheaf.stalkSpecializes _).hom a.val
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  refine hE0 ?_
  rw [h U φ hφ E hE, pullbackComponent_eq hB hφ _ hW c' hc']
  refine E.ordUnit_eq_zero_of_isUnit ((a.isUnit).map (f.stalkMap E.genericPoint).hom) ?_
  change (X.presheaf.stalkSpecializes _).hom ((f.stalkMap E.genericPoint).hom
    a.val) = (f.stalkMap _).hom ((Y.presheaf.stalkSpecializes hsp').hom a.val)
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]

/-- **`Supp f^*B = f⁻¹(Supp B)`** for an effective Cartier divisor `B` and its pull-back. -/
theorem supp_eq_preimage_supp_of_isPullback {B : Divisor Y} (hBc : B.IsCartier)
    (hBe : DivisorWithCoeffs.IsEffective B)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') :
    (B'.supp : Set X) = f.base ⁻¹' (B.supp : Set Y) :=
  subset_antisymm (supp_subset_preimage_supp_of_isPullback hBc h)
    (preimage_supp_subset_supp_of_isPullback hBc hBe h)

end PullbackSupport

/-! ### The generic fibre -/

section GenericFiber

variable {X Z : Scheme.{u}} (h : X ⟶ Z)

/-- The closure of the image of a morphism from an irreducible scheme is the closure of the image
of the generic point. -/
theorem closure_range_eq_closure_genericPoint [IrreducibleSpace X] :
    closure (Set.range h.base) = closure {h.base (genericPoint X)} := by
  refine subset_antisymm (closure_minimal ?_ isClosed_closure)
    (closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩))
  rintro _ ⟨x, rfl⟩
  exact specializes_iff_mem_closure.mp
    ((genericPoint_specializes x).map h.base.hom.continuous)

/-- The dimension of the generic fibre `X_η` (`η = h(ξ_X)`) of a morphism locally of finite type
from an irreducible scheme is the transcendence degree of `κ(ξ_X)` over `κ(η)`. -/
theorem topologicalKrullDim_fiber_genericPoint [IrreducibleSpace X] [LocallyOfFiniteType h] :
    topologicalKrullDim (h.fiber (h.base (genericPoint X))) =
      (residueFieldTranscendenceDegree h (genericPoint X) : WithBot ℕ∞) := by
  have _ : IrreducibleSpace (h.fiber (h.base (genericPoint X))) :=
    h.irreducibleSpace_fiber_genericPoint
  rw [topologicalKrullDim_eq_trdeg_residueField (Z.residueField (h.base (genericPoint X)))
      (h.fiber (h.base (genericPoint X))) (h.fiberToSpecResidueField (h.base (genericPoint X)))
      (h.asFiber (genericPoint X)) h.isGenericPoint_asFiber_genericPoint,
    h.trdeg_residueField_fiber (genericPoint X)]
  rfl

/-- **The dimension of the generic fibre** (the aside of FA 17.4.2). For a morphism `h : X ⟶ Z`
of `k`-schemes locally of finite type, `X` irreducible, with `η = h(ξ_X)` the generic point of
`h(X)`: `dim X = dim X_η + dim \overline{h(X)}` (Stacks 0A21). -/
theorem topologicalKrullDim_eq_fiber_add_closure_range (k : Type u) [Field k]
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (hc : h ≫ sZ = sX) [IrreducibleSpace X]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] :
    topologicalKrullDim X = topologicalKrullDim (h.fiber (h.base (genericPoint X))) +
      topologicalKrullDim (closure (Set.range h.base)) := by
  subst hc
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h sZ
  rw [topologicalKrullDim_fiber_genericPoint, closure_range_eq_closure_genericPoint,
    topologicalKrullDim_closure_singleton_eq_trdeg k Z sZ,
    topologicalKrullDim_eq_trdeg_residueField k X (h ≫ sZ) (genericPoint X)
      (Set.top_eq_univ (α := X) ▸ genericPoint_spec X), residueFieldTranscendenceDegree]
  set ξ := genericPoint X
  set η := h.base ξ
  let A1 : Algebra k (Z.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sZ.appTop ≫ Z.Γevaluation η).hom.toAlgebra
  let A2 : Algebra k (X.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (h ≫ sZ).appTop ≫ X.Γevaluation ξ).hom.toAlgebra
  let A3 : Algebra (Z.residueField η) (X.residueField ξ) := (h.residueFieldMap ξ).hom.toAlgebra
  have : IsScalarTower k (Z.residueField η) (X.residueField ξ) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ (h ≫ sZ).appTop ≫ X.Γevaluation ξ).hom a =
      (h.residueFieldMap ξ).hom
        (((Scheme.ΓSpecIso (.of k)).inv ≫ sZ.appTop ≫ Z.Γevaluation η).hom a)
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (Scheme.Γevaluation_naturality_apply h ξ _).symm
  rw [← trdeg_add_eq k (Z.residueField η) (A := X.residueField ξ), map_add, add_comm,
    WithBot.coe_add]

/-- **The dimension of the generic fibre**, as a natural number (the aside of FA 17.4.2): if
`dim X = a` and `dim \overline{h(X)} = b`, then `dim X_η = a - b`. -/
theorem topologicalKrullDim_fiber_genericPoint_eq_sub (k : Type u) [Field k]
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (hc : h ≫ sZ = sX) [IrreducibleSpace X]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] {a b : ℕ}
    (ha : topologicalKrullDim X = a) (hb : topologicalKrullDim (closure (Set.range h.base)) = b) :
    topologicalKrullDim (h.fiber (h.base (genericPoint X))) = ((a - b : ℕ) : WithBot ℕ∞) := by
  have hsum := topologicalKrullDim_eq_fiber_add_closure_range h k sX sZ hc
  subst hc
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h sZ
  rw [topologicalKrullDim_fiber_genericPoint] at hsum ⊢
  rw [ha, hb] at hsum
  generalize residueFieldTranscendenceDegree h (genericPoint X) = t at hsum ⊢
  induction t using ENat.recTopCoe with
  | top =>
    exfalso
    have : ((a : ℕ∞) : WithBot ℕ∞) = ((⊤ + (b : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
      rwa [WithBot.coe_add]
    rw [top_add] at this
    exact ENat.natCast_ne_top a (WithBot.coe_injective this)
  | coe n =>
    have : a = n + b := by exact_mod_cast hsum
    rw [this, Nat.add_sub_cancel]
    rfl

/-- A generization map between stalks at two equal points reflects units. -/
theorem isUnit_of_isUnit_stalkSpecializes {T : Scheme.{u}} {a b : T} (hab : b = a) (e : a ⤳ b)
    {r : T.presheaf.stalk b} (hr : IsUnit ((T.presheaf.stalkSpecializes e).hom r)) : IsUnit r := by
  subst hab
  rwa [TopCat.Presheaf.stalkSpecializes_refl] at hr

/-- For `X` integral and `x` in the generic fibre of `h` (`h(x) = h(ξ_X)`), the maximal ideal of
`𝒪_{Z,h(x)}` maps to `0` in `𝒪_{X,x}`. -/
theorem map_maximalIdeal_stalkMap_eq_bot [IsIntegral X] (x : X)
    (hx : h.base x = h.base (genericPoint X)) :
    Ideal.map (h.stalkMap x).hom (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h.base x))) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro m hm
  rw [RingHom.mem_ker]
  have hsp : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_zero]
  change (X.presheaf.stalkSpecializes hsp).hom ((h.stalkMap x).hom m) = 0
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  let : Field (X.presheaf.stalk (genericPoint X)) := (inferInstance : Field X.functionField)
  by_contra hne
  have hu : IsUnit ((h.stalkMap (genericPoint X)).hom
      ((Z.presheaf.stalkSpecializes (h.base.hom.map_specializes hsp)).hom m)) := by
    refine ⟨⟨_, _⁻¹, mul_inv_cancel₀ hne, inv_mul_cancel₀ hne⟩, rfl⟩
  exact (IsLocalRing.mem_maximalIdeal _).mp hm
    (isUnit_of_isUnit_stalkSpecializes hx _ (isUnit_of_map_unit _ _ hu))

/-- If at every point `x` over `y` the maximal ideal of `𝒪_{Z,y}` maps to `0` in `𝒪_{X,x}`, then
the fibre `X_y` has the local rings of `X`: the stalk maps of `X_y ⟶ X` are isomorphisms (the
local ring of the fibre is `𝒪_{X,x}/𝔪_y𝒪_{X,x}`). -/
theorem isIso_stalkMap_fiberι_of_map_eq_bot (y : Z)
    (hmap : ∀ x : X, h.base x = y →
      Ideal.map (h.stalkMap x).hom (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h.base x))) = ⊥)
    (p : h.fiber y) : IsIso ((h.fiberι y).stalkMap p) := by
  have key : ∀ (x : X) (hx : h.base x = y), h.fiberι y p = x →
      IsIso ((h.fiberι y).stalkMap p) := by
    intro x hx hp
    subst hx
    obtain rfl : p = h.asFiber x := (h.fiberHomeo (h.base x)).injective (Subtype.ext (by
      rw [Scheme.Hom.fiberHomeo_apply, hp, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]))
    let e : X.presheaf.stalk x ≃+* (h.fiber (h.base x)).presheaf.stalk (h.asFiber x) :=
      (RingEquiv.quotientBot _).symm.trans
        ((Ideal.quotEquivOfEq (hmap x rfl).symm).trans (quotientStalkEquivFiberStalk h x))
    have hc : Function.Bijective
        ((X.presheaf.stalkCongr (.of_eq (h.fiberι_asFiber x).symm)).hom) :=
      ConcreteCategory.bijective_of_isIso _
    refine (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Function.Bijective.of_comp_iff _ hc).mp ?_)
    have he : (((h.fiberι (h.base x)).stalkMap (h.asFiber x)).hom ∘
        (X.presheaf.stalkCongr (.of_eq (h.fiberι_asFiber x).symm)).hom) = e :=
      funext fun b => (quotientStalkEquivFiberStalk_mk h x b).symm
    rw [he]
    exact e.bijective
  exact key _ (show h.fiberι y p ∈ h.base ⁻¹' {y} from h.range_fiberι y ▸ ⟨p, rfl⟩) rfl

/-- The generic fibre of a morphism from an integral scheme has the local rings of the source. -/
theorem isIso_stalkMap_fiberι_genericPoint [IsIntegral X]
    (p : h.fiber (h.base (genericPoint X))) :
    IsIso ((h.fiberι (h.base (genericPoint X))).stalkMap p) :=
  isIso_stalkMap_fiberι_of_map_eq_bot h _ (map_maximalIdeal_stalkMap_eq_bot h) p

/-- **The generic fibre of a morphism from a normal integral scheme is normal.** -/
theorem isNormal_fiber_genericPoint [IsIntegral X] [IsNormal X] :
    IsNormal (h.fiber (h.base (genericPoint X))) where
  stalk_isDomain p := by
    have := isIso_stalkMap_fiberι_genericPoint h p
    exact Function.Injective.isDomain _
      (asIso ((h.fiberι _).stalkMap p)).commRingCatIsoToRingEquiv.symm.injective
  stalk_normal p := by
    have := isIso_stalkMap_fiberι_genericPoint h p
    have := IsNormal.stalk_normal (X := X) ((h.fiberι _) p)
    exact IsIntegrallyClosed.of_equiv
      (asIso ((h.fiberι _).stalkMap p)).commRingCatIsoToRingEquiv

/-- **The generic fibre of a morphism from an integral scheme is integral.** -/
theorem isIntegral_fiber_genericPoint [IsIntegral X] :
    IsIntegral (h.fiber (h.base (genericPoint X))) := by
  have (p : h.fiber (h.base (genericPoint X))) :
      IsReduced ((h.fiber (h.base (genericPoint X))).presheaf.stalk p) := by
    have := isIso_stalkMap_fiberι_genericPoint h p
    exact isReduced_of_injective _
      (asIso ((h.fiberι _).stalkMap p)).commRingCatIsoToRingEquiv.symm.injective
  have : IsReduced (h.fiber (h.base (genericPoint X))) := isReduced_of_isReduced_stalk _
  have := h.irreducibleSpace_fiber_genericPoint
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The generic fibre is a normal variety** (the aside of FA 17.4.2): for a morphism `h : X ⟶ Z`
of varieties over `k` with `X` normal, the generic fibre `X_η` (`η = h(ξ_X)`, the generic point of
`h(X)`) is a normal variety over `κ(η)`. -/
theorem isNormalVariety_fiber_genericPoint (k : Type u) [Field k] (sX : X ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) (hZ : Mori.IsVariety k sZ)
    (hc : h ≫ sZ = sX) [IsNormal X] :
    Mori.IsNormalVariety (Z.residueField (h.base (genericPoint X)))
      (h.fiberToSpecResidueField (h.base (genericPoint X))) := by
  subst hc
  have := hX.toQuasiCompact
  have := hX.toLocallyOfFiniteType
  have := hX.toIsSeparated
  have := hX.toIsIntegral
  have := hZ.toIsSeparated
  have := hZ.toLocallyOfFiniteType
  have : IsSeparated h :=
    MorphismProperty.of_postcomp (W := @IsSeparated) (W' := ⊤) h sZ trivial inferInstance
  have : QuasiCompact h :=
    MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) h sZ
      inferInstance inferInstance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h sZ
  have := isIntegral_fiber_genericPoint h
  have : IsSeparated (h.fiberToSpecResidueField (h.base (genericPoint X))) :=
    show IsSeparated (Limits.pullback.snd _ _) from inferInstance
  have : LocallyOfFiniteType (h.fiberToSpecResidueField (h.base (genericPoint X))) :=
    show LocallyOfFiniteType (Limits.pullback.snd _ _) from inferInstance
  have : QuasiCompact (h.fiberToSpecResidueField (h.base (genericPoint X))) :=
    show QuasiCompact (Limits.pullback.snd _ _) from inferInstance
  exact ⟨AlgebraicGeometry.IsVariety.mk, isNormal_fiber_genericPoint h⟩

end GenericFiber

end MMP.Flips
