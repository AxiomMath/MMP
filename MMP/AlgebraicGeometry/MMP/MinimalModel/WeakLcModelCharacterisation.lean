module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.MinimalModel.WeakLcModelCoefficients
import MMP.AlgebraicGeometry.Morphisms.Birational.ModificationCodimOne

/-!
# An intrinsic characterisation of weak log canonical models of a morphism

Let `f : (X, D_X) ⟶ Z` and `g : Y ⟶ Z` be proper morphisms of normal varieties, with `(X, D_X)` a
log variety and `K_X + D_X` `ℝ`-Cartier, and let `φ : X ⤏ Y` be a modification of `f` into `g`.
Let `D_Y` be a boundary on `Y` with `K_Y + D_Y` `ℝ`-Cartier. Then `D_Y = D_{𝓕,Y}` for an
admissible `𝓕` making `g : (Y, D_Y) ⟶ Z` a weak log canonical model of `f` with respect to `𝓕`
if and only if

* `g : (Y, D_Y) ⟶ Z` is a relative weak log canonical model;
* `a(B, D_Y) ≥ a(B, D_X)` for every divisor `B` of `k(X) = k(Y)` with nonempty center on `X`;
* `a(ord_E, D_Y) = max {-1, a(ord_E, D_X)}` for every prime divisor `E` of `Y`.

The condition on the right does not mention `𝓕`: it characterises weak log canonical models by
discrepancies alone.

## Main results

* `MMP.Flips.IsModificationOf.exists_isWeakLogCanonicalModelOf_iff`.

## Implementation notes

The function fields `k(X)` and `k(Y)` are identified through `φ`. In the second condition a
divisor `B` is a valuation `w` of `k(W)` on a common model `(W, p, q)` of `φ`
(`MMP.Flips.IsCommonModel`), seen on `X` as `w ∘ p^*` and on `Y` as `w ∘ q^*`; the condition is
asked of every common model. In the third condition `ord_E` is seen on `X` through any divisor
over `X` realizing `E` through `φ` (`MMP.Flips.IsRealizedOver`).

The third condition is asked of every prime divisor of `Y`, not only of the `g`-exceptional
ones: with `X = Y = Z` a smooth surface, `f = g = φ = 𝟙`, `D_X` a smooth curve `C` and
`D_Y = 0`, the first two conditions hold and `Y` has no `g`-exceptional divisors, but
`D_{𝓕,Y} = C ≠ D_Y`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.21.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

universe u

namespace MMP.Flips

/-! ### Function fields along rational maps -/

/-- The generic point of an irreducible scheme lies in every dense open. -/
private theorem genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : genericPoint X ∈ U :=
  haveI := IrreducibleSpace.toNonempty (X := X)
  (genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec

/-- `Spec k(X) ⟶ Y` along a partial map factors through its domain. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- A dominant map sends the generic point into every dense open. -/
private theorem genericPoint_mem_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    genericPoint A ∈ a ⁻¹ᵁ U := by
  change a (genericPoint A) ∈ U
  rw [map_genericPoint_of_isDominant]
  exact genericPoint_mem_of_dense hU

/-- For a dominant `a : A ⟶ X` and an open `U ∋ η_X`, `Spec k(A) ⟶ Spec k(X) ⟶ U` is
`Spec k(A) ⟶ a⁻¹ U ⟶ U`. -/
private theorem specMap_functionFieldMap_fromSpecStalkOfMem {A X : Scheme.{u}} [IsIntegral A]
    [IsIntegral X] (a : A ⟶ X) [IsDominant a] (U : X.Opens) (hx : genericPoint X ∈ U)
    (hA : genericPoint A ∈ a ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ U.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ U).fromSpecStalkOfMem (genericPoint A) hA ≫ (a ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact functionFieldMap_fromSpecStalk a

/-- If `p' = g ∘ a` on `a⁻¹(dom g)` for a dominant `a : A ⟶ X`, then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` along `g` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  have hx : genericPoint X ∈ g.domain := genericPoint_mem_of_dense g.dense_domain
  rw [partialMap_fromFunctionField_eq g hx, ← Category.assoc,
    specMap_functionFieldMap_fromSpecStalkOfMem a _ hx (genericPoint_mem_preimage a g.dense_domain),
    Category.assoc, ← hcomm,
    ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if
they agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (U : W.Opens) (hU : genericPoint W ∈ U) {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  let P₁ : W.PartialMap Y := ⟨U, hd, f⟩
  let P₂ : W.PartialMap Y := ⟨U, hd, g⟩
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) (f := P₁) (g := P₂)
    hd le_rfl le_rfl).mp (Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁ P₂ hU hU H)
  rwa [Scheme.PartialMap.restrict_id_hom, Scheme.PartialMap.restrict_id_hom] at this

/-- If `θ` induces `φ` at the generic points and `ψ` is inverse to `φ`, then
`Spec k(X) ⟶ Spec k(Y) ⟶ X` along `θ` and `ψ` is the canonical map. -/
private theorem specMap_comp_fromFunctionField_of_isInverse {X M : Scheme.{u}} [IsIntegral X]
    [IsIntegral M] {φ : X.RationalMap M} {ψ : M.RationalMap X}
    (hinv : Mori.RationalMap.IsInverse φ ψ) (θ : M.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ M.fromSpecStalk (genericPoint M) =
      φ.fromFunctionField) :
    Spec.map (CommRingCat.ofHom θ) ≫ ψ.fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source := genericPoint_mem_of_dense e.dense_source
  have hy : genericPoint M ∈ e.target := genericPoint_mem_of_dense e.dense_target
  have hφ : φ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hx]
    rfl
  have hψ : ψ.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint M) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hy]
    rfl
  have c1 : Spec.map (CommRingCat.ofHom θ) ≫ e.target.fromSpecStalkOfMem (genericPoint M) hy =
      e.source.fromSpecStalkOfMem (genericPoint X) hx ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hθ, hφ,
      Category.assoc]
  rw [hψ, ← Category.assoc, c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Conversely, if `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`, then for some
representative `φ₀` of `φ`, `φ₀ ∘ p` and `q` agree as rational maps `W ⤏ Y`. -/
private theorem exists_partialMap_toRationalMap_eq_of_specMap_fromFunctionField_eq
    {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X)
    [IsDominant p] (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap := by
  obtain ⟨φ₀, rfl⟩ := φ.exists_rep
  have hx := genericPoint_mem_of_dense φ₀.dense_domain
  have hW := genericPoint_mem_preimage p φ₀.dense_domain
  have hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W) := (p ⁻¹ᵁ φ₀.domain).isOpen.dense ⟨_, hW⟩
  refine ⟨φ₀, rfl, hd, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  have hW' : genericPoint W ∈ (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
      (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).domain := hW
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap, partialMap_fromFunctionField_eq _ hW',
    MMP.Flips.RationalMap.fromFunctionField_hom, ← H,
    Scheme.RationalMap.fromFunctionField_toRationalMap, partialMap_fromFunctionField_eq _ hx]
  change (p ⁻¹ᵁ φ₀.domain).fromSpecStalkOfMem (genericPoint W) hW ≫
    p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono φ₀.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk p).symm

/-- A ring map `θ : k(Y) → k(X)` inducing `φ : X ⤏ Y` at the generic points, and a partial map
`g'` representing `φ`: if `p^* ∘ θ = q^*` for dominant `p : W ⟶ X` and `q : W ⟶ Y`, then
`q = g' ∘ p` on `p⁻¹(dom g')`. -/
private theorem preimage_ι_comp_eq {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    [IsIntegral Y] [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (p : W ⟶ X) (q : W ⟶ Y)
    [IsDominant p] [IsDominant q] (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
      φ.fromFunctionField)
    (hpq : (functionFieldMap p).comp θ = functionFieldMap q) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) :
    (p ⁻¹ᵁ g'.domain).ι ≫ q = (p ∣_ g'.domain) ≫ g'.hom := by
  have hx : genericPoint X ∈ g'.domain := genericPoint_mem_of_dense g'.dense_domain
  have hA := genericPoint_mem_preimage p g'.dense_domain
  refine hom_eq_of_fromSpecStalkOfMem_eq _ hA ?_
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc,
    ← specMap_functionFieldMap_fromSpecStalkOfMem p _ hx hA,
    Category.assoc, ← partialMap_fromFunctionField_eq g' hx,
    ← Scheme.RationalMap.fromFunctionField_toRationalMap, hg', ← hθ, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hpq]
  exact (functionFieldMap_fromSpecStalk q).symm

/-- **The identification of function fields by a common model.** If `p : W ⟶ X` and
`q : W ⟶ Y` induce isomorphisms of function fields and `φ ∘ p = q` at the generic point, then
some bijective `θ : k(Y) → k(X)` (namely `(p^*)⁻¹ ∘ q^*`) satisfies `p^* ∘ θ = q^*` and induces
`φ`. -/
private theorem exists_ringHom_functionField {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    [IsIntegral Y] {φ : X.RationalMap Y} (p : W ⟶ X) (q : W ⟶ Y) [IsDominant p] [IsDominant q]
    (hp : Function.Bijective (functionFieldMap p)) (hq : Function.Bijective (functionFieldMap q))
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, Function.Bijective θ ∧
      (functionFieldMap p).comp θ = functionFieldMap q ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
        φ.fromFunctionField := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  have hpq : (functionFieldMap p).comp (ep.symm.toRingHom.comp (functionFieldMap q)) =
      functionFieldMap q := RingHom.ext fun s => ep.apply_symm_apply _
  refine ⟨_, ep.symm.bijective.comp hq, hpq, ?_⟩
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), H, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hpq]
  exact functionFieldMap_fromSpecStalk q

/-! ### Valuations -/

/-- Pulling back valuations along a surjective ring map is injective. -/
private theorem valuation_comap_injective {R S Γ₀ : Type*} [Ring R] [Ring S]
    [LinearOrderedCommMonoidWithZero Γ₀] {θ : R →+* S} (hθ : Function.Surjective θ) :
    Function.Injective fun v : Valuation S Γ₀ => v.comap θ := fun v v' h =>
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hθ t
    exact congrArg (fun w : Valuation R Γ₀ => w s) h

/-- On a normal variety, a prime divisor is determined by its valuation. -/
private theorem primeDivisor_eq_of_divisorialValuation_eq {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : Mori.IsNormalVariety k sX) {P P' : Mori.PrimeDivisor X}
    (h : P.divisorialValuation = P'.divisorialValuation) : P = P' := by
  have hv : ∀ P : Mori.PrimeDivisor X,
      (Mori.DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation :=
    fun P => Valuation.ext fun t => by
      change P.divisorialValuation (functionFieldMap (𝟙 X) t) = _
      rw [Mori.functionFieldMap_id_apply]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq
      (D := Mori.DivisorOver.ofPrimeDivisor k hX P)
      (D' := Mori.DivisorOver.ofPrimeDivisor k hX P') hX.1 (by rw [hv, hv, h]))

/-- Along a prime divisor `E` with `f(η_E) = η_P` at which `f` induces an isomorphism of local
rings, `ord_E ∘ f^* = ord_P`. -/
private theorem divisorialValuation_comap_functionFieldMap_eq {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] :
    E.divisorialValuation.comap (functionFieldMap f) = P.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  by_cases ht : t = 0
  · simp [ht]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq t]

/-- **Realized divisors carry `ord_F`.** Let `θ : k(Y) → k(X)` induce `φ : X ⤏ Y` at the generic
points. If a divisor `B` over `X` realizes the prime divisor `F` of `Y` through `φ`, then
`ord_B ∘ θ = ord_F`. -/
private theorem comap_valuation_eq_of_isRealizedOver {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {φ : X.RationalMap Y} (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
      φ.fromFunctionField)
    {F : Mori.PrimeDivisor Y} {B : ProperDivisorOver k sX} (hB : IsRealizedOver sX φ F B) :
    B.valuation.comap θ = F.divisorialValuation := by
  obtain ⟨g₀, pB, hpB, hg₀, hcE, hval⟩ := hB
  have := B.isIntegral
  have := B.isNormal
  have := B.isLocallyNoetherian
  have := B.isDominant
  have := hpB.isDominant
  have hA := specMap_functionFieldMap_fromFunctionField B.f g₀ pB hcE
  rw [← Scheme.RationalMap.fromFunctionField_toRationalMap, hg₀, ← hθ,
    ← functionFieldMap_fromSpecStalk pB, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp] at hA
  have h2 : (functionFieldMap B.f).comp θ = functionFieldMap pB :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp hA))
  rw [← hval]
  refine Valuation.ext fun t => ?_
  change B.E.divisorialValuation (functionFieldMap B.f (θ t)) =
    B.E.divisorialValuation (functionFieldMap pB t)
  rw [← h2, RingHom.comp_apply]

/-- **The transform of a prime divisor carries its valuation.** Let `p : W ⟶ X`, `q : W ⟶ Y` be
dominant, `q` inducing an isomorphism of function fields, and `θ : k(Y) → k(X)` induce `φ` with
`p^* ∘ θ = q^*`. If `φ_* Q = E` and the prime divisor `Q_W` of `W` lies over `η_Q` with
`𝒪_{X,Q} ≅ 𝒪_{W,Q_W}`, then `ord_Q ∘ θ = ord_E`. -/
private theorem comap_divisorialValuation_eq_of_transformPrimeDivisor_eq_some
    {W X Y : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (p : W ⟶ X) (q : W ⟶ Y)
    [IsDominant p] [IsDominant q] (hq : Function.Bijective (functionFieldMap q))
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
      φ.fromFunctionField)
    (hpq : (functionFieldMap p).comp θ = functionFieldMap q) {Q : Mori.PrimeDivisor X}
    (QW : Mori.PrimeDivisor W) (hQW : p QW.genericPoint = Q.genericPoint)
    [IsIso (p.stalkMap QW.genericPoint)] {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor φ Q = some E) :
    Q.divisorialValuation.comap θ = E.divisorialValuation := by
  obtain ⟨hdef, -⟩ := Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  have hE := genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP
  have hagree := preimage_ι_comp_eq p q θ hθ hpq g' hg'
  have hmem : QW.genericPoint ∈ p ⁻¹ᵁ g'.domain :=
    show p QW.genericPoint ∈ g'.domain from hQW ▸ hP
  have hqQ : q QW.genericPoint = E.genericPoint := by
    let x : (p ⁻¹ᵁ g'.domain).toScheme := ⟨QW.genericPoint, hmem⟩
    have h1 : q ((p ⁻¹ᵁ g'.domain).ι x) = g'.hom ((p ∣_ g'.domain) x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hagree]
    have h2 : (p ∣_ g'.domain) x = ⟨Q.genericPoint, hP⟩ :=
      Subtype.ext ((morphismRestrict_base_coe p g'.domain x).trans hQW)
    rw [h2] at h1
    exact h1.trans hE.symm
  have := E.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q QW.genericPoint)) := hqQ ▸ inferInstance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing q hq QW.genericPoint
  rw [← divisorialValuation_comap_functionFieldMap_eq q QW E hqQ,
    ← divisorialValuation_comap_functionFieldMap_eq p QW Q hQW, ← hpq, Valuation.comap_comp]

/-- **Non-exceptional primes are read off through `θ`.** Let `p : W ⟶ X`, `q : W ⟶ Y` be
dominant, `p` proper and birational, `q` inducing an isomorphism of function fields, and
`θ : k(Y) ≅ k(X)` induce `φ` with `p^* ∘ θ = q^*`. A prime divisor
`E` of `Y` that is not `φ⁻¹`-exceptional is `φ_* Q` for a prime `Q` of `X` such that every
divisor over `X` realizing `E` has valuation `ord_Q`, and the coefficient of `E` in `φ_* D` is
the coefficient of `Q` in `D`. -/
private theorem exists_valuation_eq_and_coeff_eq {k : Type u} [Field k] {W X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)]
    (hX : Mori.IsNormalVariety k sX) {φ : X.RationalMap Y} (p : W ⟶ X) (q : W ⟶ Y)
    [IsProper p] [IsDominant p] [IsDominant q] (hW : Mori.IsNormalVariety k (p ≫ sX))
    (hp : Mori.IsBirationalMorphism p) (hq : Function.Bijective (functionFieldMap q))
    (θ : Y.functionField →+* X.functionField) (hθb : Function.Bijective θ)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
      φ.fromFunctionField)
    (hpq : (functionFieldMap p).comp θ = functionFieldMap q) {E : Mori.PrimeDivisor Y}
    (hE : ¬ RationalMap.IsInverseExceptional φ E) :
    ∃ Q : Mori.PrimeDivisor X, Mori.RationalMap.transformPrimeDivisor φ Q = some E ∧
      (∀ B : ProperDivisorOver k sX, IsRealizedOver sX φ E B →
        B.valuation = Q.divisorialValuation) ∧
      ∀ D : Mori.RDivisor X, (Mori.RationalMap.transformDivisor φ D).coeff E = D.coeff Q := by
  have hQ : ∀ Q, Mori.RationalMap.transformPrimeDivisor φ Q = some E →
      Q.divisorialValuation.comap θ = E.divisorialValuation := fun Q h => by
    obtain ⟨QW, h1, h2, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hW hp Q
    exact comap_divisorialValuation_eq_of_transformPrimeDivisor_eq_some p q hq θ hθ hpq QW h1 h
  obtain ⟨Q, hQE⟩ := not_forall_not.mp hE
  have hinj := valuation_comap_injective (R := Y.functionField) (Γ₀ := ℤᵐ⁰) hθb.2
  refine ⟨Q, hQE, fun B hB => hinj ((comap_valuation_eq_of_isRealizedOver θ hθ hB).trans
    (hQ Q hQE).symm), fun D => MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hQE
    (fun Q' h' => primeDivisor_eq_of_divisorialValuation_eq hX
      (hinj ((hQ Q' h').trans (hQ Q hQE).symm))) D⟩

/-- Let `θ : k(Y) ≅ k(X)` induce a birational map `φ`. A divisor over `Y` realizing the prime
divisor `P` of `X` through `φ⁻¹` has valuation `ord_P ∘ θ`. -/
private theorem valuation_eq_comap_of_isRealizedOver_inverse {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] {φ : X.RationalMap Y} (hφ : Mori.RationalMap.IsBirational φ)
    (θ : Y.functionField →+* X.functionField) (hθb : Function.Bijective θ)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) =
      φ.fromFunctionField)
    {P : Mori.PrimeDivisor X} {E : ProperDivisorOver k sY}
    (hE : IsRealizedOver sY hφ.inverse P E) :
    E.valuation = P.divisorialValuation.comap θ := by
  let eθ := RingEquiv.ofBijective θ hθb
  have hθ'θ : eθ.symm.toRingHom.comp θ = RingHom.id _ :=
    RingHom.ext eθ.symm_apply_apply
  have hθ' : Spec.map (CommRingCat.ofHom eθ.symm.toRingHom) ≫
      X.fromSpecStalk (genericPoint X) = hφ.inverse.fromFunctionField := by
    rw [← specMap_comp_fromFunctionField_of_isInverse hφ.isInverse_inverse θ hθ,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ'θ,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rw [← comap_valuation_eq_of_isRealizedOver _ hθ' hE, ← Valuation.comap_comp, hθ'θ,
    Valuation.comap_id]

open MMP.Mori in
/-- On a normal variety over a perfect field, `a(ord_P, D) = -coeff_P(D)` for every canonical
divisor `K` with `K + D` `ℝ`-Cartier. -/
private theorem isDiscrepancy_neg_coeff {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    {D : RDivisor X} (hK : K.IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor K + D)) (P : Mori.PrimeDivisor X) :
    IsDiscrepancy sX n K D P.divisorialValuation (-D.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' fun Γ => by
    rw [coeff_divisorOfForm, hω]
  exact MMP.Flips.isDiscrepancy_divisorialValuation hX ω hω0 hK hKD P

open Classical in
/-- The coefficient of `E` in `∑_{F ∈ Fs} c_F F` is `c_E` if `E ∈ Fs` and `0` otherwise. -/
private theorem coeff_sum_single {Y : Scheme.{u}} (Fs : Finset (Mori.PrimeDivisor Y))
    (c : Mori.PrimeDivisor Y → ℝ) (E : Mori.PrimeDivisor Y) :
    (∑ F ∈ Fs, Finsupp.single F (c F) : Mori.RDivisor Y).coeff E = if E ∈ Fs then c E else 0 := by
  change (∑ F ∈ Fs, Finsupp.single F (c F)) E = _
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- **FA 2.21.5, corrected.** Let `f : X ⟶ Z` and `g : Y ⟶ Z` be proper morphisms of normal
varieties over a field `k` of characteristic zero, `φ : X ⤏ Y` a modification of `f` into `g`,
`(X, D_X)` a log variety with canonical divisor `K_X` (of dimension `n`) and `K_X + D_X`
`ℝ`-Cartier, `K_Y` a canonical divisor of `Y`, and `D_Y` a boundary on `Y` with `K_Y + D_Y`
`ℝ`-Cartier. Then `g : (Y, D_Y) ⟶ Z` is a weak log canonical model of `f : (X, D_X) ⟶ Z` with
respect to some admissible `𝓕 = c` with `D_Y = D_{𝓕,Y}` (`MMP.Flips.IsWeakLogCanonicalModelOf`)
if and only if
* `g : (Y, D_Y) ⟶ Z` is a relative weak log canonical model
  (`MMP.Flips.IsRelativeWeakLogCanonicalModel`);
* for every common model `(W, p, q)` of `φ` and every valuation `w` of `k(W)` such that
  `B = w ∘ p^*` has nonempty center on `X`, the divisor `w ∘ q^*` has nonempty center on `Y` and
  `a(B, D_Y) ≥ a(B, D_X)`;
* for every prime divisor `E` of `Y` and every divisor over `X` realizing `E` through `φ`,
  `a(ord_E, D_Y) = max {-1, a(ord_E, D_X)}`. -/
@[mmp "lem_fa2_weak_lc_model_invariant_characterisation"]
public theorem IsModificationOf.exists_isWeakLogCanonicalModelOf_iff {k : Type u} [Field k]
    [CharZero k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X}
    {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {D_Y : Mori.RDivisor Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} {φ : X.RationalMap Y} [IsProper f] [IsProper g] (hX : IsLogVariety k sX D_X)
    (hY : Mori.IsNormalVariety k sY) (hZ : Mori.IsVariety k sZ) (hfs : f ≫ sZ = sX)
    (hgs : g ≫ sZ = sY) (hφ : IsModificationOf f g φ)
    (hKX : K_X.IsCanonicalDivisor sX n)
    (hKXD : IsCartierCombination (Mori.Divisor.toRDivisor K_X + D_X))
    (hKY : K_Y.IsCanonicalDivisor sY n) (hDY : IsBoundary D_Y)
    (hKYD : IsCartierCombination (Mori.Divisor.toRDivisor K_Y + D_Y)) :
    (∃ c : Mori.PrimeDivisor Y → ℝ, IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c D_Y) ↔
      IsRelativeWeakLogCanonicalModel sY n K_Y D_Y g ∧
      (∀ (W : Scheme.{u}) (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y)
          (hW : IsCommonModel k sX sY sZ sW f g φ p q),
        haveI : IsIntegral W := hW.isNormalVariety.1.toIsIntegral
        haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
        haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
        ∀ w : Valuation W.functionField ℤᵐ⁰,
          HasNonemptyCenter k sX (w.comap (functionFieldMap p)) →
            HasNonemptyCenter k sY (w.comap (functionFieldMap q)) ∧
              ∀ a a' : ℝ, IsDiscrepancy sY n K_Y D_Y (w.comap (functionFieldMap q)) a →
                IsDiscrepancy sX n K_X D_X (w.comap (functionFieldMap p)) a' → a' ≤ a) ∧
      ∀ (E : Mori.PrimeDivisor Y) (B : ProperDivisorOver k sX), IsRealizedOver sX φ E B →
        ∀ a a' : ℝ, IsDiscrepancy sY n K_Y D_Y E.divisorialValuation a →
          IsDiscrepancy sX n K_X D_X B.valuation a' → a = max (-1) a' := by
  have hXn := hX.isNormalVariety
  obtain ⟨hcod, -, hfin, hreal⟩ := IsModificationOf.isMorphismInCodimOne_and_exists_isRealizedOver
    sX sY sZ hXn hY hZ f g hfs hgs φ hφ
  /- a smooth common model `(W, p, q)` and the identification `θ : k(Y) ≅ k(X)` -/
  obtain ⟨W, p, q, hWv, hWs, hpP, hqP, hpb, hqb, ⟨ψ, hinv, hψq⟩, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model sX sY sZ hXn hY hZ f g hfs hgs φ hφ
  have : IsIntegral W := hWv.toIsIntegral
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have hWn : Mori.IsNormalVariety k (p ≫ sX) := ⟨hWv, inferInstance⟩
  have : IsSeparated sY := hY.1.toIsSeparated
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = sY ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
    rw [← hψq, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
      specMap_comp_fromFunctionField_of_isInverse hinv _ ((functionFieldMap_fromSpecStalk p).trans
        (MMP.Flips.RationalMap.fromFunctionField_hom p).symm)]
  obtain ⟨θ, hθb, hpq, hθ⟩ := exists_ringHom_functionField p q hpb.functionFieldMap_bijective
    hqb.functionFieldMap_bijective KF
  have hmatch := fun E => exists_valuation_eq_and_coeff_eq (E := E) hXn p q hWn hpb
    hqb.functionFieldMap_bijective θ hθb hθ hpq
  have hdY := isDiscrepancy_neg_coeff hY hKY hKYD
  have hle1 : ∀ Q, D_X.coeff Q ≤ 1 := fun Q => (hX.isBoundary Q).2
  constructor
  · /- (⇒) -/
    rintro ⟨c, hM⟩
    obtain ⟨-, -, -, hFB, hKG, hRel, -⟩ := id hM
    refine ⟨hRel, fun W' sW' p' q' hW' w hw => hM.isDiscrepancy_le hW' hw w rfl rfl, ?_⟩
    intro E B hBE a a' ha ha'
    by_cases hE : RationalMap.IsInverseExceptional φ E
    · rw [ha.eq (IsFBirationalTransform.isDiscrepancy_divisorialValuation hFB hKY hKG hE),
        IsWeakLogCanonicalModelOf.eq_min_of_isInverseExceptional hZ hfs hgs hM hE hBE ha',
        ← max_neg_neg, neg_neg]
    · obtain ⟨Q, -, hBQ, hcoeff⟩ := hmatch E hE
      rw [hBQ B hBE] at ha'
      obtain ⟨-, -, -, -, -, -, Fs, hFs, -, -, hG⟩ := hFB
      have hcY : D_Y.coeff E = D_X.coeff Q := by
        rw [hG, Mori.DivisorWithCoeffs.coeff_add, hcoeff, coeff_sum_single,
          if_neg (fun h => hE ((hFs E).1 h)), add_zero]
      rw [ha.eq_neg_coeff, hcY, ha'.eq_neg_coeff, max_eq_right (by linarith [hle1 Q])]
  · /- (⇐) -/
    rintro ⟨h1, h2, h3⟩
    refine ⟨D_Y.coeff, inferInstance, inferInstance, hφ,
      ⟨hXn, hY, hφ.1, hcod, hKX, hKXD, hfin.toFinset, fun F => hfin.mem_toFinset,
        fun F _ => hreal F, fun F _ => ⟨(hDY F).2, fun E a hE ha => ?_⟩, ?_⟩, hKYD, h1, ?_⟩
    · have key := h3 F E hE _ a (hdY F) ha
      rcases max_choice (-1) a with h | h <;> rw [h] at key
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
    · refine Mori.DivisorWithCoeffs.ext' fun E => ?_
      rw [Mori.DivisorWithCoeffs.coeff_add, coeff_sum_single]
      by_cases hE : RationalMap.IsInverseExceptional φ E
      · rw [show (Mori.RationalMap.transformDivisor φ D_X).coeff E = 0 from
            mapPrimeDivisors_apply_eq_zero_of_forall_ne hE D_X,
          if_pos (hfin.mem_toFinset.2 hE), zero_add]
      · obtain ⟨Q, -, hBQ, hcoeff⟩ := hmatch E hE
        obtain ⟨B, hBE⟩ := hreal E
        have key := h3 E B hBE _ _ (hdY E)
          (by rw [hBQ B hBE]; exact isDiscrepancy_neg_coeff hXn hKX hKXD Q)
        rw [max_eq_right (by linarith [hle1 Q])] at key
        rw [hcoeff, if_neg (fun h => hE (hfin.mem_toFinset.1 h)), add_zero]
        linarith
    · intro hφ' P _ E a a' hE ha ha'
      obtain ⟨PW, hPW1, hPW2, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWn hpb P
      have hwp := divisorialValuation_comap_functionFieldMap_eq p PW P hPW1
      have hwq : PW.divisorialValuation.comap (functionFieldMap q) = E.valuation := by
        rw [valuation_eq_comap_of_isRealizedOver_inverse hφ' θ hθb hθ hE, ← hwp, ← hpq,
          Valuation.comap_comp]
      have hW : IsCommonModel k sX sY sZ (p ≫ sX) f g φ p q :=
        { isVariety_X := hXn.1
          isVariety_Y := hY.1
          isVariety_Z := hZ
          comp_f := hfs
          comp_g := hgs
          isProper_f := inferInstance
          isProper_g := inferInstance
          isModificationOf := hφ
          isNormalVariety := hWn
          comp_p := rfl
          comp_q := by rw [← hgs, ← hfs, ← Category.assoc, ← hcomm, Category.assoc]
          isProper_p := hpP
          isProper_q := hqP
          isBirationalMorphism_p := hpb
          isBirationalMorphism_q := hqb
          comp_eq :=
            exists_partialMap_toRationalMap_eq_of_specMap_fromFunctionField_eq φ p q KF }
      exact (h2 W (p ≫ sX) p q hW PW.divisorialValuation (by rw [hwp]; exact ha'.2.2.1)).2 a a'
        (by rwa [hwq]) (by rwa [hwp])

end MMP.Flips
