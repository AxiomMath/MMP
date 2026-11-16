module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# A modification over a base is a morphism in codimension one both ways

Let `f : X ⟶ Z` and `g : Y ⟶ Z` be proper morphisms of normal varieties over a field `k` of
characteristic zero, and `φ : X ⤏ Y` a modification of `f` into `g`
(`MMP.Flips.IsModificationOf`). Then `φ` and every inverse `φ⁻¹ : Y ⤏ X` are morphisms in
codimension one, only finitely many prime divisors of `Y` are `φ⁻¹`-exceptional, and every
prime divisor `F` of `Y` is realized through `φ` by a divisor over `X`, so that `ord_F`, a
divisor of `k(X) = k(Y)`, has nonempty center on `X`. These are the hypotheses on `φ` of the
`𝓕`-birational transform `MMP.Flips.IsFBirationalTransform`.

## Main results

* `MMP.Flips.IsModificationOf.isMorphismInCodimOne_and_exists_isRealizedOver`.

## Implementation notes

The inverse of `φ` is quantified over: the statement is made for every rational map
`ψ : Y ⤏ X` that is an inverse of `φ` (`MMP.Mori.RationalMap.IsInverse`), rather than for a
chosen one. That `ord_F` has nonempty center on `X` is expressed by a divisor `E` over `X`
realizing `F` through `φ` (`MMP.Flips.IsRealizedOver`), the form in which
`MMP.Flips.IsFBirationalTransform` uses it.

Proof outline. Let `f : X ⟶ Z`, `g : Y ⟶ Z` be proper morphisms of normal varieties over a field of
characteristic zero and `φ : X ⤏ Y` a modification of `f` into `g`. Both `φ` and its inverses
are maps over `Z` to proper targets, hence morphisms in codimension one; the `φ⁻¹`-exceptional
primes are finitely many; and every prime divisor `F` of `Y` is realized through `φ` by its
strict transform on a smooth common model `p : W ⟶ X`, `q : W ⟶ Y`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.7, 2.21
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Proof_lem_fa2_modification_over_base_transform_defined

open MMP MMP.Flips

/-- The generic point of an irreducible scheme lies in every dense open. -/
private theorem genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : genericPoint X ∈ U :=
  haveI := IrreducibleSpace.toNonempty (X := X)
  (genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec

/-- The point `Spec k(X) ⟶ Y` of a morphism is `Spec k(X) ⟶ X ⟶ Y`. -/
private theorem fromFunctionField_toRationalMap_hom {X Y : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Y) : f.toRationalMap.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ f :=
  Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap f _

/-- The point `Spec k(X) ⟶ Y` of a partial map defined at the generic point. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if
they agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {U : W.Opens} (hU : genericPoint W ∈ U) {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  let P₁ : W.PartialMap Y := ⟨U, hd, f⟩
  let P₂ : W.PartialMap Y := ⟨U, hd, g⟩
  have heqv : P₁.equiv P₂ := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁ P₂ hU hU H
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) (f := P₁) (g := P₂)
    hd le_rfl le_rfl).mp heqv
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

/-- On a common model `p : W ⟶ X`, `q : W ⟶ Y` of `φ : X ⤏ Y` (with `h` inverse to `p` and
`q = φ ∘ h`), `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField_of_isInverse {X Y W : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y)
    (h : X.RationalMap W) [IsDominant p] (hinv : Mori.RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  rw [← hcomp, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_comp_fromFunctionField_of_isInverse hinv _
      ((functionFieldMap_fromSpecStalk p).trans (fromFunctionField_toRationalMap_hom p).symm)]

/-- A ring isomorphism `θ : k(Y) → k(X)` inducing `m : Spec k(X) ⟶ Y`, read off a pair
`p : A ⟶ X`, `q : A ⟶ Y` inducing isomorphisms of function fields along which `m` is `q`. -/
private theorem exists_ringHom_of_specMap {X Y A : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral A] {m : Spec X.functionField ⟶ Y} (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p]
    [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hq : Function.Bijective (functionFieldMap q))
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, Function.Bijective θ ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q :=
    RingHom.ext fun s => ep.apply_symm_apply _
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  refine ⟨θ, ep.symm.bijective.comp hq, ?_⟩
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hA, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
  exact functionFieldMap_fromSpecStalk q

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
  · rw [ht, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq t]

/-- An inverse of a birational map over `Z` is a map over `Z`: if `g ∘ φ = f` and `ψ` is an
inverse of `φ`, then `f ∘ ψ = g`. The function fields are identified through a common model
`p : W ⟶ X`, `q : W ⟶ Y` of `φ`. -/
private theorem isOver_of_isInverse {X Y Z W : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral W] {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    (hφ : RationalMap.IsOver f g φ) (p : W ⟶ X) (q : W ⟶ Y) [IsDominant p] [IsDominant q]
    (hp : Function.Bijective (functionFieldMap p)) (hq : Function.Bijective (functionFieldMap q))
    (h : X.RationalMap W) (hinv : Mori.RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) {ψ : Y.RationalMap X} (hψ : Mori.RationalMap.IsInverse φ ψ) :
    RationalMap.IsOver g f ψ := by
  obtain ⟨θ, hθb, hθ⟩ := exists_ringHom_of_specMap p q hp hq
    (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp)
  have hψθ := specMap_comp_fromFunctionField_of_isInverse hψ θ hθ
  have : IsIso (CommRingCat.ofHom θ) := (ConcreteCategory.isIso_iff_bijective _).mpr hθb
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom, fromFunctionField_toRationalMap_hom,
    ← cancel_epi (Spec.map (CommRingCat.ofHom θ)), ← Category.assoc, hψθ,
    ← fromFunctionField_toRationalMap_hom, ← hφ,
    MMP.Flips.RationalMap.fromFunctionField_compHom, ← hθ, Category.assoc]

/-- **The strict transform on a common model realizes a prime divisor.** Let `p : W ⟶ X`,
`q : W ⟶ Y` be proper birational morphisms from a normal variety `W` with `q = φ ∘ p` (some
inverse `h` of `p` has `h.compHom q = φ`). The strict transform `F'` on `W` of a prime divisor
`F` of `Y` makes `(W, p, F')` a divisor over `X` realizing `F` through `φ`. -/
private theorem exists_isRealizedOver_of_isInverse {k : Type u} [Field k] {X Y W : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : Mori.IsNormalVariety k sY) (φ : X.RationalMap Y)
    (p : W ⟶ X) (q : W ⟶ Y) (hWp : Mori.IsNormalVariety k (p ≫ sX)) (hpq : p ≫ sX = q ≫ sY)
    [IsProper p] [IsProper q] (hpb : Mori.IsBirationalMorphism p)
    (hqb : Mori.IsBirationalMorphism q) (h : X.RationalMap W)
    (hinv : Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ)
    (F : Mori.PrimeDivisor Y) : ∃ E : ProperDivisorOver k sX, IsRealizedOver sX φ F E := by
  have hWq : Mori.IsNormalVariety k (q ≫ sY) := hpq ▸ hWp
  have : IsIntegral W := hWp.1.toIsIntegral
  have : IsNormal W := hWp.2
  have : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  obtain ⟨FW, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hWq hqb F
  refine ⟨⟨⟨W, p, hWp, hpb, FW⟩, ‹_›⟩, ?_⟩
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : IsSeparated sY := hY.1.toIsSeparated
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = sY ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨g', hg'⟩ := φ.exists_rep
  refine ⟨g', q, hqb, hg', ?_, divisorialValuation_comap_functionFieldMap_eq q FW F heq⟩
  have hx : genericPoint X ∈ g'.domain := genericPoint_mem_of_dense g'.dense_domain
  have hA : genericPoint W ∈ p ⁻¹ᵁ g'.domain := by
    change p (genericPoint W) ∈ g'.domain
    rw [map_genericPoint_of_isDominant]
    exact hx
  refine hom_eq_of_fromSpecStalkOfMem_eq hA ?_
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      g'.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (p ⁻¹ᵁ g'.domain).fromSpecStalkOfMem (genericPoint W) hA ≫ (p ∣_ g'.domain) := by
    rw [← cancel_mono g'.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk p
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc, ← c1,
    Category.assoc, ← partialMap_fromFunctionField_eq g' hx,
    ← Scheme.RationalMap.fromFunctionField_toRationalMap, hg']
  exact (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp).symm

end Proof_lem_fa2_modification_over_base_transform_defined

namespace MMP.Flips

open Proof_lem_fa2_modification_over_base_transform_defined

/-- **FA 2.7, 2.21.** Let `f : X ⟶ Z` and `g : Y ⟶ Z` be proper morphisms of normal varieties
over a field `k` of characteristic zero and `φ : X ⤏ Y` a modification of `f` into `g`. Then
`φ` is a morphism in codimension one, so is every inverse `ψ : Y ⤏ X` of `φ`, only finitely
many prime divisors of `Y` are `φ⁻¹`-exceptional, and every prime divisor `F` of `Y` is realized
through `φ` by a divisor `E` over `X` (so `ord_F` has nonempty center on `X`). -/
@[mmp "lem_fa2_modification_over_base_transform_defined"]
public theorem IsModificationOf.isMorphismInCodimOne_and_exists_isRealizedOver {k : Type u}
    [Field k] [CharZero k] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (hX : Mori.IsNormalVariety k sX)
    (hY : Mori.IsNormalVariety k sY) (hZ : Mori.IsVariety k sZ) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY) [IsProper f] [IsProper g]
    (φ : X.RationalMap Y) (hφ : IsModificationOf f g φ) :
    RationalMap.IsMorphismInCodimOne φ ∧
      (∀ ψ : Y.RationalMap X, Mori.RationalMap.IsInverse φ ψ →
        RationalMap.IsMorphismInCodimOne ψ) ∧
      {F : Mori.PrimeDivisor Y | RationalMap.IsInverseExceptional φ F}.Finite ∧
      haveI := hX.1.toIsIntegral
      haveI := hX.2
      haveI := hX.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      haveI : QuasiCompact sX := hX.1.toQuasiCompact
      haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
      haveI := hY.1.toIsIntegral
      haveI := hY.2
      haveI := hY.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      ∀ F : Mori.PrimeDivisor Y, ∃ E : ProperDivisorOver k sX, IsRealizedOver sX φ F E := by
  have h1 : RationalMap.IsMorphismInCodimOne φ :=
    RationalMap.isMorphismInCodimOne_of_isOver hX f g φ hφ.2
  obtain ⟨W, p, q, hWv, hWs, _, _, hpb, hqb, ⟨h, hinv, hcomp⟩, hpq⟩ :=
    IsModificationOf.exists_smooth_common_model sX sY sZ hX hY hZ f g hfs hgs φ hφ
  have := hX.1.toIsIntegral
  have := hY.1.toIsIntegral
  have : IsIntegral W := hWv.toIsIntegral
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  refine ⟨h1, fun ψ hψ ↦ RationalMap.isMorphismInCodimOne_of_isOver hY g f ψ
    (isOver_of_isInverse hφ.2 p q hpb.functionFieldMap_bijective hqb.functionFieldMap_bijective
      h hinv hcomp hψ), (RationalMap.finite_setOf_isInverseExceptional hX hY φ hφ.1 h1).1, ?_⟩
  have := hX.2
  have := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := hY.2
  have := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact exists_isRealizedOver_of_isInverse sX hY φ p q
    ⟨hWv, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2⟩
    (by rw [← hfs, ← hgs, ← Category.assoc, hpq, Category.assoc]) hpb hqb h hinv hcomp

end MMP.Flips
