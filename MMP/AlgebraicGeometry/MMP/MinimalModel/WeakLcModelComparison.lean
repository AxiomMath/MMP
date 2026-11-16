module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.Negativity.FibreSupport
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.EffectiveIdealSheaf
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero

/-!
# Comparing two weak log canonical models of a morphism

Let `X`, `Y₁`, `Y₂`, `Z` be varieties over a field of characteristic zero, and let
`g₁ : (Y₁, D₁) ⟶ Z` and `g₂ : (Y₂, D₂) ⟶ Z` be weak log canonical models of the same
`f : (X, D_X) ⟶ Z`, through the modifications `φ₁ : X ⤏ Y₁` and `φ₂ : X ⤏ Y₂`, with respect to
admissible coefficient families `𝓕₁` and `𝓕₂`. Let `ψ = φ₂ ∘ φ₁⁻¹ : Y₁ ⤏ Y₂`. Then
`g₂ : (Y₂, D₂) ⟶ Z` is a weak log canonical model of `g₁ : (Y₁, D₁) ⟶ Z` through `ψ`, with
respect to some admissible coefficient family `𝓕'` on the `ψ⁻¹`-exceptional prime divisors
of `Y₂`.

## Main results

* `MMP.Flips.IsWeakLogCanonicalModelOf.exists_isWeakLogCanonicalModelOf_trans`.
* `MMP.Flips.IsRelativelyNef.comp_of_isRCartierPullback`: the pull-back of a relatively nef divisor
  along a proper morphism is nef over the base.

## Proof

For every prime divisor `P` of `Y₁`, `a(ord_P, D₁) ≤ a(ord_P, D₂)`. If `P` is
`φ₁⁻¹`-exceptional, its coefficient is forced, so `a(ord_P, D₁) = max {-1, a(ord_P, D_X)}`; both
terms are bounded by `a(ord_P, D₂)`, the first since `(Y₂, D₂)` is lc and the second by FA 2.23.3
for `g₂`. Otherwise `P = φ₁_* Q` and `a(ord_P, D₁) = a(ord_Q, D_X) ≤ a(ord_Q, D₂)`. By symmetry
the same holds with `Y₁`, `Y₂` exchanged, so `D₂` agrees with `ψ_* D₁` off the
`ψ⁻¹`-exceptional primes `F`, and the coefficients `c'_F = coeff_F(D₂)` are admissible.

FA 2.23.3 (`a(B, D_{𝓕,Y}) ≥ a(B, D_X)` for a weak log canonical model) is proved on a common
model by the negativity lemma, after correcting the two canonical divisors by the principal
divisor of the quotient of the two rational top forms, which is numerically trivial.

## Implementation notes

The birational map `ψ = φ₂ ∘ φ₁⁻¹` is described through isomorphisms of dense opens: if
`e₁ : X.PartialIso Y₁` and `e₂ : X.PartialIso Y₂` represent `φ₁` and `φ₂`, then `ψ` is the
rational map of `e₁.symm.trans e₂`. This rational map does not depend on the representatives.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.21.5,
  2.23, 2.24.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Flips.WeakLCModelsCompare

/-! ### Rational maps at the generic point -/

section GenericPoint

open MMP MMP.Flips

/-- The generic point of an irreducible scheme lies in every dense open. -/
private theorem genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : genericPoint X ∈ U :=
  haveI := IrreducibleSpace.toNonempty (X := X)
  (genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec

/-- The generic point of `A` lies over every dense open of `X`, for `a : A ⟶ X` dominant. -/
private theorem genericPoint_mem_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    genericPoint A ∈ a ⁻¹ᵁ U := by
  change a (genericPoint A) ∈ U
  rw [map_genericPoint_of_isDominant]
  exact genericPoint_mem_of_dense hU

/-- The point `Spec k(X) ⟶ Y` of a partial map defined at the generic point. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if
they agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (U : W.Opens) (hU : genericPoint W ∈ U)
    {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme)
    (f := ⟨U, hd, f⟩) (g := ⟨U, hd, g⟩) hd le_rfl le_rfl).mp
    (Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ hU hU H)
  rwa [Scheme.PartialMap.restrict_id_hom, Scheme.PartialMap.restrict_id_hom] at this

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
  have hA := genericPoint_mem_preimage a g.dense_domain
  rw [partialMap_fromFunctionField_eq g hx, ← Category.assoc,
    specMap_functionFieldMap_fromSpecStalkOfMem a _ hx hA, Category.assoc, ← hcomm,
    ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

/-- **A morphism agreeing with a rational map at the generic point agrees with each of its
representatives.** Let `a : W ⟶ X` be dominant, `b : W ⟶ Y`, and `χ : X ⤏ Y` with
`χ ∘ a = b` at the generic point of `W`. Then for every representative `g` of `χ`,
`b = g ∘ a` on `a⁻¹(dom g)`. -/
private theorem preimage_ι_comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] (a : W ⟶ X) [IsDominant a]
    (b : W ⟶ Y) (χ : X.RationalMap Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ χ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ b)
    (g : X.PartialMap Y) (hg : g.toRationalMap = χ) :
    (a ⁻¹ᵁ g.domain).ι ≫ b = (a ∣_ g.domain) ≫ g.hom := by
  have hx : genericPoint X ∈ g.domain := genericPoint_mem_of_dense g.dense_domain
  have hA := genericPoint_mem_preimage a g.dense_domain
  refine hom_eq_of_fromSpecStalkOfMem_eq _ hA ?_
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc,
    ← specMap_functionFieldMap_fromSpecStalkOfMem a _ hx hA, Category.assoc,
    ← partialMap_fromFunctionField_eq g hx, ← Scheme.RationalMap.fromFunctionField_toRationalMap,
    hg]
  exact H.symm

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

/-- The composite `p⁻¹(dom φ₀) ⟶ dom φ₀ ⟶ Y` is, at the generic point, `Spec k(W) ⟶ Spec k(X)`
followed by `φ₀`. -/
private theorem fromFunctionField_resLE_comp {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    (p : W ⟶ X) [IsDominant p] (φ₀ : X.PartialMap Y)
    (hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W)) :
    (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
      (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ₀.fromFunctionField := by
  have hx : genericPoint X ∈ φ₀.domain := genericPoint_mem_of_dense φ₀.dense_domain
  have hW : genericPoint W ∈ p ⁻¹ᵁ φ₀.domain := genericPoint_mem_of_dense hd
  rw [partialMap_fromFunctionField_eq _ hW, partialMap_fromFunctionField_eq _ hx]
  change (p ⁻¹ᵁ φ₀.domain).fromSpecStalkOfMem (genericPoint W) hW ≫
    p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono φ₀.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk p).symm

/-- **A common model, at the generic point.** If `q = φ ∘ p` as maps for a dominant `p`, then
`Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_fromFunctionField_eq_of_comp_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨φ₀, rfl, hd, heq⟩ := H
  have h1 := congrArg Scheme.RationalMap.fromFunctionField heq
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_resLE_comp,
    MMP.Flips.RationalMap.fromFunctionField_hom] at h1

/-- Conversely, if `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`, then
`q = φ ∘ p` as maps. -/
private theorem comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap := by
  obtain ⟨φ₀, rfl⟩ := φ.exists_rep
  have hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W) :=
    (p ⁻¹ᵁ φ₀.domain).isOpen.dense ⟨_, genericPoint_mem_preimage p φ₀.dense_domain⟩
  refine ⟨φ₀, rfl, hd, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_resLE_comp,
    MMP.Flips.RationalMap.fromFunctionField_hom]

/-- **The identification of function fields by a common model.** If `p : A ⟶ X` and
`q : A ⟶ Y` induce isomorphisms of function fields and `m ∘ p = q` at the generic point for a
point `m : Spec k(X) ⟶ Y`, then `θ := (p^*)⁻¹ ∘ q^* : k(Y) ≅ k(X)` satisfies `p^* ∘ θ = q^*` and
induces `m`. -/
private theorem exists_ringHom_of_specMap {X Y A : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral A] (m : Spec X.functionField ⟶ Y) (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p]
    [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hq : Function.Bijective (functionFieldMap q))
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, Function.Bijective θ ∧
      (functionFieldMap p).comp θ = functionFieldMap q ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  have hpq : (functionFieldMap p).comp (ep.symm.toRingHom.comp (functionFieldMap q)) =
      functionFieldMap q := RingHom.ext fun s => ep.apply_symm_apply _
  refine ⟨_, ep.symm.bijective.comp hq, hpq, ?_⟩
  haveI : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hA, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hpq]
  exact functionFieldMap_fromSpecStalk q

/-- Along a prime divisor `E` with `f(η_E) = η_P` at which `f` induces an isomorphism of local
rings, `ord_E ∘ f^* = ord_P`. -/
private theorem divisorialValuation_comap_functionFieldMap_eq {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (f : Y ⟶ X) [IsDominant f] (E : Mori.PrimeDivisor Y)
    (P : Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] :
    E.divisorialValuation.comap (functionFieldMap f) = P.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq t]

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- The valuation of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    Mori.functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩,
    E, rfl⟩

private theorem valuation_comap_injective {R S : Type*} [Ring R] [Ring S] {θ : R →+* S}
    (hθ : Function.Surjective θ) :
    Function.Injective fun v : Valuation S (WithZero (Multiplicative ℤ)) => v.comap θ :=
  fun v v' h =>
    Valuation.ext fun t => by
      obtain ⟨s, rfl⟩ := hθ t
      exact congrArg (fun w : Valuation R (WithZero (Multiplicative ℤ)) => w s) h

end GenericPoint

namespace CommonModel

open CategoryTheory.Limits

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A morphism `f : Γ ⟶ Y` of irreducible schemes is birational when its composite with an open
immersion from a nonempty scheme is an open immersion. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {O Γ Y : Scheme.{u}}
    [IrreducibleSpace Γ] [IrreducibleSpace Y] [Nonempty O] (j : O ⟶ Γ) [IsOpenImmersion j]
    (f : Γ ⟶ Y) [IsOpenImmersion (j ≫ f)] : MMP.Mori.IsBirationalMorphism f := by
  have hle : j.opensRange ≤ f ⁻¹ᵁ (j ≫ f).opensRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨o⟩ := ‹Nonempty O›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f j.opensRange (j ≫ f).opensRange
    ⟨j o, o, rfl⟩ ⟨(j ≫ f) o, o, rfl⟩ hle ?_
  have e : (Scheme.Hom.isoOpensRange j).hom ≫ f.resLE _ _ hle =
      (Scheme.Hom.isoOpensRange (j ≫ f)).hom := by
    rw [← cancel_mono (j ≫ f).opensRange.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have h : f.resLE _ _ hle =
      (Scheme.Hom.isoOpensRange j).inv ≫ (Scheme.Hom.isoOpensRange (j ≫ f)).hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- Let `p : W ⟶ X` and `q : W ⟶ Y` be morphisms from an irreducible scheme to an irreducible
scheme `X`, and `A ⊆ W` a nonempty open on which `p` is an open immersion. If on `A` the map `q`
agrees with `h ∘ p` for a morphism `h : B ⟶ Y` on a dense open `B ⊆ X`, then `p` has a rational
inverse `ψ` with `q ∘ ψ = h` as rational maps. -/
private theorem exists_isInverse_compHom_eq {W X Y : Scheme.{u}} [IrreducibleSpace W]
    [IrreducibleSpace X] (p : W ⟶ X) (q : W ⟶ Y) (A : W.Opens) (hA : (A : Set W).Nonempty)
    [IsOpenImmersion (A.ι ≫ p)] (B : X.Opens) (hB : Dense (B : Set X)) (h : B.toScheme ⟶ Y)
    (l : A.toScheme ⟶ B) (hl₁ : l ≫ B.ι = A.ι ≫ p) (hl₂ : l ≫ h = A.ι ≫ q) :
    ∃ ψ : X.RationalMap W, MMP.Mori.RationalMap.IsInverse p.toRationalMap ψ ∧
      ψ.compHom q = (Scheme.PartialMap.mk B hB h).toRationalMap := by
  let R := (A.ι ≫ p).opensRange
  obtain ⟨a, ha⟩ := hA
  have hR : (R : Set X).Nonempty := ⟨(A.ι ≫ p) ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩
  let e : W.PartialIso X :=
    { source := A
      dense_source := A.isOpen.dense ⟨a, ha⟩
      target := R
      dense_target := R.isOpen.dense hR
      iso := Scheme.Hom.isoOpensRange (A.ι ≫ p) }
  have he : e.toRationalMap = p.toRationalMap := by
    rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨A, A.isOpen.dense ⟨a, ha⟩, le_rfl, le_top, ?_⟩
    change W.homOfLE le_rfl ≫ (Scheme.Hom.isoOpensRange (A.ι ≫ p)).hom ≫
        (A.ι ≫ p).opensRange.ι = W.homOfLE (le_top : A ≤ ⊤) ≫ W.topIso.hom ≫ p
    rw [Scheme.Hom.isoOpensRange_hom_ι, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc,
      Scheme.homOfLE_ι_assoc]
  refine ⟨e.symm.toRationalMap, ⟨e, he, rfl⟩, ?_⟩
  have hRle : R ≤ B := by
    rintro _ ⟨x, rfl⟩
    rw [← hl₁]
    exact (l x).2
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨R, R.isOpen.dense hR, le_rfl, hRle, ?_⟩
  have key : e.iso.inv ≫ l = X.homOfLE hRle := by
    rw [← cancel_mono B.ι, Category.assoc, hl₁, Scheme.homOfLE_ι]
    change (Scheme.Hom.isoOpensRange (A.ι ≫ p)).inv ≫ A.ι ≫ p = (A.ι ≫ p).opensRange.ι
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  change X.homOfLE le_rfl ≫ (e.iso.inv ≫ A.ι) ≫ q = X.homOfLE hRle ≫ h
  rw [Scheme.homOfLE_rfl, Category.id_comp, ← key, Category.assoc, Category.assoc, hl₂]

/-- A modification `φ` of `f` into `g` is, on a dense open `O ⊆ X`, an open immersion
`h : O ⟶ Y` over `Z`: `h ≫ g = O ↪ X ≫ f`. -/
private theorem exists_isOpenImmersion_of_isModificationOf {X Y Z : Scheme.{u}} {f : X ⟶ Z}
    {g : Y ⟶ Z} {φ : X.RationalMap Y} (hφ : MMP.Flips.IsModificationOf f g φ) :
    ∃ (O : X.Opens) (hO : Dense (O : Set X)) (h : O.toScheme ⟶ Y), IsOpenImmersion h ∧
      (Scheme.PartialMap.mk O hO h).toRationalMap = φ ∧ h ≫ g = O.ι ≫ f := by
  obtain ⟨⟨e, he⟩, hover⟩ := hφ
  rw [MMP.Flips.RationalMap.IsOver, ← he, Scheme.PartialIso.toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hover
  obtain ⟨O, hO, hOe, hOt, hOeq⟩ := hover
  replace hOe : O ≤ e.source := hOe
  refine ⟨O, hO, X.homOfLE hOe ≫ e.iso.hom ≫ e.target.ι, inferInstance, ?_, ?_⟩
  · rw [← he, Scheme.PartialIso.toRationalMap,
      ← Scheme.PartialMap.restrict_toRationalMap e.toPartialMap O hO hOe]
    rfl
  · simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom_hom,
      Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom] at hOeq
    have h2 : X.homOfLE hOe ≫ e.iso.hom ≫ e.target.ι ≫ g =
        X.homOfLE (le_top : O ≤ ⊤) ≫ (⊤ : X.Opens).ι ≫ f := hOeq
    rw [Scheme.homOfLE_ι_assoc] at h2
    simpa only [Category.assoc] using h2

/-- A birational morphism `r : W ⟶ Γ` onto an irreducible scheme maps some nonempty open
`A ⊆ W` isomorphically onto an open of any given nonempty open subscheme `j : O ⟶ Γ`. -/
private theorem exists_isOpenImmersion_lift {W Γ O : Scheme.{u}} [Nonempty W]
    [IrreducibleSpace Γ] [Nonempty O] {r : W ⟶ Γ} (hr : MMP.Mori.IsBirationalMorphism r)
    (j : O ⟶ Γ) [IsOpenImmersion j] :
    ∃ (A : W.Opens) (m : A.toScheme ⟶ O), (A : Set W).Nonempty ∧ IsOpenImmersion m ∧
      m ≫ j = A.ι ≫ r := by
  obtain ⟨W₀, ⟨w, hw⟩, h₀⟩ := hr.exists_isOpenImmersion
  obtain ⟨o⟩ := ‹Nonempty O›
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := nonempty_preirreducible_inter (W₀.ι ≫ r).opensRange.isOpen
    j.opensRange.isOpen ⟨(W₀.ι ≫ r) ⟨w, hw⟩, ⟨w, hw⟩, rfl⟩ ⟨j o, o, rfl⟩
  let A : W.Opens := W₀ ⊓ r ⁻¹ᵁ j.opensRange
  have : IsOpenImmersion (A.ι ≫ r) := by
    rw [← Scheme.homOfLE_ι W (inf_le_left : A ≤ W₀), Category.assoc]
    infer_instance
  let m := IsOpenImmersion.lift j (A.ι ≫ r) (by rintro _ ⟨a, rfl⟩; exact a.2.2)
  have hm : m ≫ j = A.ι ≫ r := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (m ≫ j) := by rw [hm]; infer_instance
  exact ⟨A, m, ⟨x.1, x.2, hx⟩, .of_comp m j, hm⟩

private theorem main {k : Type u} [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Mori.IsNormalVariety k sX) (hY : MMP.Mori.IsNormalVariety k sY) (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsProper f] [IsProper g] (φ : X.RationalMap Y)
    (hφ : MMP.Flips.IsModificationOf f g φ) :
    ∃ (W : Scheme.{u}) (p : W ⟶ X) (q : W ⟶ Y),
      MMP.Mori.IsVariety k (p ≫ sX) ∧ MMP.Mori.IsSmoothScheme (p ≫ sX) ∧
        IsProper p ∧ IsProper q ∧
        MMP.Mori.IsBirationalMorphism p ∧ MMP.Mori.IsBirationalMorphism q ∧
        (∃ ψ : X.RationalMap W, MMP.Mori.RationalMap.IsInverse p.toRationalMap ψ ∧
          ψ.compHom q = φ) ∧
        p ≫ f = q ≫ g := by
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sY := hY.1
  have : IsIntegral X := IsVariety.toIsIntegral (k := k) (f := sX)
  have : IsIntegral Y := IsVariety.toIsIntegral (k := k) (f := sY)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  /- Step 1: an open `O ⊆ X` on which `φ` is an open immersion `h` with `h ≫ g = f`. -/
  obtain ⟨O, hO, h, _, hPφ, hcomm⟩ := exists_isOpenImmersion_of_isModificationOf hφ
  have : Nonempty O := hO.nonempty.to_subtype
  /- Step 2: the closure `Γ ⊆ X ×_Z Y` of the graph of `h`. -/
  let s : O.toScheme ⟶ pullback f g := pullback.lift O.ι h hcomm.symm
  have : IsImmersion s := by
    have : IsImmersion (s ≫ pullback.fst f g) := by rw [pullback.lift_fst]; infer_instance
    exact IsImmersion.of_comp s (pullback.fst _ _)
  have : TopologicalSpace.NoetherianSpace O := TopologicalSpace.NoetherianSpace.set (O : Set X)
  have : QuasiCompact s := quasiCompact_of_noetherianSpace_source s
  have : IsOpenImmersion s.toImage := isOpenImmersion_toImage s (.inl inferInstance)
  let p₁ : s.image ⟶ X := s.imageι ≫ pullback.fst f g
  let p₂ : s.image ⟶ Y := s.imageι ≫ pullback.snd f g
  let sΓ : s.image ⟶ Spec (.of k) := p₁ ≫ sX
  have hΓ : AlgebraicGeometry.IsVariety k sΓ := by
    simpa only [sΓ, p₁, Category.assoc] using
      Scheme.Hom.isVariety_image k s (pullback.fst f g ≫ sX)
  have : IsProper p₁ := by dsimp only [p₁]; infer_instance
  have : IsProper p₂ := by dsimp only [p₂]; infer_instance
  /- Step 3: a resolution `r : W ⟶ Γ`. -/
  obtain ⟨W, r, hW, hr, hbr, hsm, -, -⟩ := MMP.Resolution.exists_isStrongResolution sΓ hΓ
  have : IsProper r := hr.isProper
  have : IsIntegral W := hW.toIsIntegral
  have : IsIntegral s.image := hΓ.toIsIntegral
  /- Step 4: a nonempty open `A ⊆ W` mapped by `r` isomorphically into the graph of `h`. -/
  obtain ⟨A, m, hA, _, hm⟩ := exists_isOpenImmersion_lift hbr s.toImage
  have : Nonempty A := hA.to_subtype
  have hm₁ : m ≫ O.ι = A.ι ≫ r ≫ p₁ := by
    rw [← reassoc_of% hm, ← Category.assoc s.toImage, Scheme.Hom.toImage_imageι,
      pullback.lift_fst]
  have hm₂ : m ≫ h = A.ι ≫ r ≫ p₂ := by
    rw [← reassoc_of% hm, ← Category.assoc s.toImage, Scheme.Hom.toImage_imageι,
      pullback.lift_snd]
  have : IsOpenImmersion (A.ι ≫ r ≫ p₁) := by rw [← hm₁]; infer_instance
  have : IsOpenImmersion (A.ι ≫ r ≫ p₂) := by rw [← hm₂]; infer_instance
  /- Step 5: the common model `p = r ≫ p₁`, `q = r ≫ p₂`. -/
  obtain ⟨ψ, hψ, hψq⟩ := exists_isInverse_compHom_eq (r ≫ p₁) (r ≫ p₂) A hA O hO h m hm₁ hm₂
  have hassoc : (r ≫ p₁) ≫ sX = r ≫ sΓ := by simp only [sΓ, Category.assoc]
  refine ⟨W, r ≫ p₁, r ≫ p₂, hassoc ▸ hW, hassoc ▸ hsm, inferInstance, inferInstance,
    hψ.isBirational, isBirationalMorphism_of_isOpenImmersion_comp A.ι (r ≫ p₂),
    ⟨ψ, hψ, hψq.trans hPφ⟩, ?_⟩
  simp only [p₁, p₂, Category.assoc, pullback.condition]

end

end CommonModel

namespace NonExceptional

open scoped WithZero

open MMP MMP.Flips MMP.Mori MMP.Threefold.Mori.Helpers

section CommonModel

/-- **A common model maps points compatibly.** If `q = φ ∘ p` at the generic point of `W`, then
for every representative `g` of `φ` defined at `x = p(w)`, `q(w) = g(x)`. -/
private theorem apply_eq_hom_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (g : X.PartialMap Y) (hg : g.toRationalMap = φ) {w : W} {x : X} (hx : x ∈ g.domain)
    (hp : p w = x) : q w = g.hom ⟨x, hx⟩ := by
  let w' : (p ⁻¹ᵁ g.domain).toScheme := ⟨w, show p w ∈ g.domain from hp ▸ hx⟩
  calc q w = ((p ⁻¹ᵁ g.domain).ι ≫ q) w' := rfl
    _ = g.hom ((p ∣_ g.domain) w') := by
      rw [preimage_ι_comp_eq_of_specMap_fromFunctionField_eq p q φ H g hg]
      rfl
    _ = g.hom ⟨x, hx⟩ :=
      congrArg g.hom (Subtype.ext ((morphismRestrict_base_coe p g.domain w').trans hp))

/-- **Strict transforms on a common model.** If `q = φ ∘ p` at the generic point of `W` and
`φ_*Q = Q'`, then every point of `W` over `η_Q` lies over `η_{Q'}`. -/
private theorem apply_eq_genericPoint_of_transformPrimeDivisor_eq_some {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {Q : Mori.PrimeDivisor X} {Q' : Mori.PrimeDivisor Y}
    (hT : Mori.RationalMap.transformPrimeDivisor φ Q = some Q') {w : W}
    (hp : p w = Q.genericPoint) : q w = Q'.genericPoint := by
  obtain ⟨g, hQg, hg⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hT).1
  exact (apply_eq_hom_of_specMap_fromFunctionField_eq H g hg hQg hp).trans
    (genericPoint_eq_of_transformPrimeDivisor_eq_some hT g hg hQg).symm

/-- The stalk of `Y` at the generic point of a prime divisor is a valuation ring. -/
private theorem valuationRing_stalk_of_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (Q : Mori.PrimeDivisor Y) {y : Y}
    (h : y = Q.genericPoint) : ValuationRing (Y.presheaf.stalk y) := by
  have := Q.isDiscreteValuationRing_localRing
  subst h
  infer_instance

/-- A birational morphism mapping `w` to the generic point of a prime divisor is a local
isomorphism at `w`. -/
private theorem isIso_stalkMap_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w : W}
    (h : q w = Q.genericPoint) : IsIso (q.stalkMap w) :=
  have := valuationRing_stalk_of_eq_genericPoint Q h
  MMP.Positivity.isIso_stalkMap_of_valuationRing q hq w

/-- A separated birational morphism has at most one point over the generic point of a prime
divisor. -/
private theorem eq_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsSeparated q] [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w₁ w₂ : W}
    (h₁ : q w₁ = Q.genericPoint) (h₂ : q w₂ = Q.genericPoint) : w₁ = w₂ :=
  have := valuationRing_stalk_of_eq_genericPoint Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₂
  MMP.Positivity.eq_of_isIso_stalkMap q hq (h₂.trans h₁.symm)

end CommonModel

private theorem main : ∀ {k : Type u}
    [Field k] [PerfectField k] {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [QuasiCompact sY]
    {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    (P : Mori.PrimeDivisor W),
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hW.comp_p ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_p, E := P, isProper := hW.isProper_p }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hW.comp_q ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_q, E := P, isProper := hW.isProper_q }
    ¬ EX.IsExceptional →
      ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
        IsDiscrepancy sX n K_X D_X EX.valuation a' → a' ≤ a := by
  intro k _ _ X Y Z W sX sY sZ sW _ _ _ _ _ _ _ _ _ _ _ n K_X D_X K_Y f g φ c G hM p q hW P EX EY
    hEX a a' ha ha'
  obtain ⟨-, -, -, hFB, -, -, hexc⟩ := hM
  obtain ⟨hXn, hYn, hφb, -, -, -, Fs, hFs, -, -, hG⟩ := hFB
  have hWn : IsNormalVariety k sW := hW.isNormalVariety
  have : IsIntegral W := hWn.1.toIsIntegral
  have : IsNormal W := hWn.2
  have : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have hpb := hW.isBirationalMorphism_p
  have hqb := hW.isBirationalMorphism_q
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : IsProper p := hW.isProper_p
  have : IsProper q := hW.isProper_q
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have : IsSeparated sX := hXn.1.toIsSeparated
  have : IsSeparated sY := hYn.1.toIsSeparated
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal sY
  -- `Q = p(P)` is a prime divisor of `X` with `ord_P = ord_Q`.
  obtain ⟨Q, -, hpQ, -, hEXv⟩ :=
    ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hXn EX hEX
  change p P.genericPoint = Q.genericPoint at hpQ
  rw [hEXv] at ha'
  have KF := specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  rcases hT : Mori.RationalMap.transformPrimeDivisor φ Q with _ | Q'
  · -- `φ_*Q = 0`: the inequality is part of the definition of a weak log canonical model.
    obtain ⟨θ, -, hθq, hθ⟩ := exists_ringHom_of_specMap _ p q hpbij hqbij KF
    have hψθ := specMap_comp_fromFunctionField_of_isInverse hφb.isInverse_inverse θ hθ
    have KF' : Spec.map (CommRingCat.ofHom (functionFieldMap q)) ≫
        hφb.inverse.fromFunctionField = W.fromSpecStalk (genericPoint W) ≫ p := by
      rw [← hθq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψθ]
      exact functionFieldMap_fromSpecStalk p
    obtain ⟨g', hg'⟩ := hφb.inverse.exists_rep
    exact hexc hφb Q hT EY a a' ⟨g', p, hpb, hg',
      preimage_ι_comp_eq_of_specMap_fromFunctionField_eq q p _ KF' g' hg', hEXv⟩ ha ha'
  · -- `φ_*Q = Q'`: both discrepancies are `-coeff_Q(D_X)`.
    have himg {Q₁ : Mori.PrimeDivisor X}
        (hT₁ : Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q')
        {w : W} (hw : p w = Q₁.genericPoint) : q w = Q'.genericPoint :=
      apply_eq_genericPoint_of_transformPrimeDivisor_eq_some KF hT₁ hw
    have hqP := himg hT hpQ
    have : IsIso (q.stalkMap P.genericPoint) :=
      isIso_stalkMap_of_apply_eq_genericPoint q hqbij Q' hqP
    rw [show EY.valuation = Q'.divisorialValuation from
      divisorialValuation_comap_functionFieldMap_eq q P Q' hqP] at ha
    -- `Q` is the only prime divisor of `X` with `φ_*Q = Q'`.
    have huniq : ∀ Q₁, Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q' → Q₁ = Q := by
      intro Q₁ hT₁
      obtain ⟨P₁, hp₁, -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn
          (hW.comp_p ▸ hWn) hpb Q₁
      have heq := eq_of_apply_eq_genericPoint q hqbij Q' hqP (himg hT₁ hp₁)
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hp₁.symm.trans (heq ▸ hpQ))
    have hQ'Fs : Q' ∉ Fs := fun h => (hFs Q').mp h Q hT
    have hcoef : G.coeff Q' = D_X.coeff Q := by
      rw [hG]
      change (Mori.RationalMap.transformDivisor φ D_X + ∑ F ∈ Fs, Finsupp.single F (c F)) Q' =
        D_X Q
      rw [Finsupp.add_apply, Finsupp.finset_sum_apply,
        Finset.sum_eq_zero fun F hF =>
          Finsupp.single_eq_of_ne' fun h : F = Q' => hQ'Fs (h ▸ hF),
        add_zero]
      exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hT huniq D_X
    have h1 := ha.eq_neg_coeff
    have h2 := ha'.eq_neg_coeff
    linarith

end NonExceptional

namespace DiscrepancyGe

open MMP MMP.Flips
open scoped WithZero

open TopologicalSpace MMP.Mori

/-! ### Intersection numbers, pull-backs and rational top forms -/

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve, of dimension at most one, is a curve over `k`. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

end Intersection

/-- **Projection formula** for a pull-back `L₁ = h^*D` of a Cartier divisor `D` along
`h : Y' ⟶ Y`: on a proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`L₁ · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- A divisor `L₁` given as a pull-back along `h` has degree zero on a proper curve whose image is
not a proper curve. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (hnc : ¬ IsProperCurve sY (h C'.point)) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc = 0 := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hnc, map_zero]

/-- **Pull-backs of relatively nef divisors are nef over the base.** Let `q : W ⟶ Y` be proper,
`g : Y ⟶ Z`, `N` a `g`-nef `ℝ`-Cartier divisor on `Y` and `G = q^*N`. Then `G · C' ≥ 0` for every
proper curve `C' ⊆ W` contracted by `q ≫ g`, for every presentation of `G`. -/
public theorem _root_.MMP.Flips.IsRelativelyNef.nonneg_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {h : W ⟶ Z}
    (hqg : q ≫ g = h) {N : RDivisor Y} (hN : IsRelativelyNef k sY g N) {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (hC' : C'.IsContractedBy h) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k sW G r L C' x) : 0 ≤ x := by
  subst hq hqg
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, hNpres, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL₀ j) (hpb j).2]
    exact (hL₀ j).isCartier_pullback q (hpb j).1
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx hx0]
  by_cases hc : IsProperCurve sY (q C'.point)
  · -- `q(C')` is a curve `C`, contracted by `g`
    obtain ⟨C, hCq⟩ : ∃ C : ProperCurve sY, C.point = q C'.point := ⟨⟨_, hc⟩, rfl⟩
    have hCg : C.IsContractedBy g := by
      intro y hy
      rw [hCq] at hy
      have hsub : closure ({q C'.point} : Set Y) ⊆ q '' closure ({C'.point} : Set W) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
          (q.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      rw [hCq]
      simpa only [Scheme.Hom.comp_apply] using hC' z hz
    obtain ⟨m', r', L', hL', hpres, hall⟩ := hN
    have hy := isRIntersectionNumber_sum_degreeOn k sY C r' L' hL'
    have hy0 := isRIntersectionNumber_sum_degreeOn k sY C r₀ L₀ hL₀
    rw [← hpres] at hy
    rw [← hNpres] at hy0
    have heq := (IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hy0 hy
    have hnn := hall C hCg _ hy
    have hdeg : ∀ j, ((L₁ j).degreeOn k (q ≫ sY) C'.ι C'.dim_le (hL₁ j) : ℝ) =
        (residueFieldDegree q C'.point : ℝ) * (L₀ j).degreeOn k sY C.ι C.dim_le (hL₀ j) :=
      fun j => by
        rw [degreeOn_eq_mul_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' C hCq]
        push_cast
        ring
    simp only [hdeg, mul_left_comm (r₀ _), ← Finset.mul_sum]
    exact mul_nonneg (Nat.cast_nonneg _) (heq ▸ hnn)
  · -- `q(C')` is a point
    simp [fun j => degreeOn_eq_zero_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' hc]

/-- **Pull-backs of relatively nef divisors are nef over the base**, bundled. Let `q : W ⟶ Y` be
proper, `g : Y ⟶ Z`, `N` a `g`-nef `ℝ`-Cartier divisor on `Y` and `G = q^*N`. Then `G` is nef over
`Z` along `q ≫ g`, presented by the pulled-back Cartier divisors. -/
public theorem _root_.MMP.Flips.IsRelativelyNef.comp_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {h : W ⟶ Z}
    (hqg : q ≫ g = h) {N : RDivisor Y} (hN : IsRelativelyNef k sY g N) {G : RDivisor W}
    (hG : IsRCartierPullback q N G) : IsRelativelyNef k sW h G := by
  obtain ⟨m, r, L, L₁, hL, -, hpb, hGL⟩ := id hG
  refine ⟨m, r, L₁, fun j => ?_, hGL, fun C hC x hx =>
    hN.nonneg_of_isRCartierPullback q hq g hqg hG C hC hx⟩
  rw [← Divisor.IsPullback.pullback_eq (hL j) (hpb j).2]
  exact (hL j).isCartier_pullback q (hpb j).1

/-- A pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {N : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f N G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  refine ⟨m, r, L', fun j => ?_, by simp only [toRDivisor_eq_mapCoeffs]⟩
  rw [← Divisor.IsPullback.pullback_eq (hL j) (hpb j).2]
  exact (hL j).isCartier_pullback f (hpb j).1

/-- The difference of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_sub {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D - D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r (fun j => -r' j), Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The sum of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_add {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D + D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add]

/-- A Cartier divisor `L₀` linearly equivalent to `0` is `ℝ`-Cartier, with intersection number `0`
with every proper curve, for every presentation. -/
private theorem eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {L₀ : Divisor X} (hc : L₀.IsCartier) (h : L₀.LinearlyEquivalent 0)
    (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX (Divisor.toRDivisor L₀) r L C x) : x = 0 := by
  have h1 := isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 1 => (1 : ℝ)) (fun _ => L₀)
    (fun _ => hc)
  have e : ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor L₀ = Divisor.toRDivisor L₀ := by simp
  rw [e] at h1
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h1]
  simp [MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hc h]

/-- Two nonzero rational top forms on a normal variety of dimension `n` over a perfect field have
linearly equivalent divisors. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ τ' : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr τ' () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ'
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 τ' hτ'
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ, Scheme.ord_mul he (inv_ne_zero hc),
    ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm, coeff_divisorOfForm, e1, e2]
  ring

/-- The divisors of two nonzero rational top forms on a normal variety `X`, for two equal
structure morphisms, are linearly equivalent. -/
private theorem linearlyEquivalent_divisorOfForm_of_eq {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {s₁ s₂ : X ⟶ Spec (.of k)} (e : s₁ = s₂) [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (hX : IsNormalVariety k s₂) {n : ℕ} (hn : topologicalKrullDim X = n)
    {τ : RationalPluriForms s₁ n 1} {τ' : RationalPluriForms s₂ n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  subst e
  exact linearlyEquivalent_divisorOfForm hX hn hτ hτ'

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- The valuation of `E` over `C` through `a ≫ b` is that over `B` through `a`, restricted along
`b^*`. -/
private theorem comap_valuationOver {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] [IsLocallyNoetherian A] [IsNormal A] (E : MMP.Mori.PrimeDivisor A) (a : A ⟶ B)
    (b : B ⟶ C)
    [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    (E.valuationOver a).comap (functionFieldMap b) = E.valuationOver (a ≫ b) := by
  ext t
  change E.divisorialValuation (functionFieldMap a (functionFieldMap b t)) =
    E.divisorialValuation (functionFieldMap (a ≫ b) t)
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-! ### Weak log canonical models -/

section CommonModel

/-- The generic-point form of `q = φ ∘ p` is stable under precomposition with a dominant
`h : W' ⟶ W`. -/
private theorem specMap_fromFunctionField_comp {W' W X Y : Scheme.{u}} [IsIntegral W']
    [IsIntegral W] [IsIntegral X] (φ : X.RationalMap Y) (h : W' ⟶ W) (p : W ⟶ X) (q : W ⟶ Y)
    [IsDominant h] [IsDominant p]
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    Spec.map (CommRingCat.ofHom (functionFieldMap (h ≫ p))) ≫ φ.fromFunctionField =
      W'.fromSpecStalk (genericPoint W') ≫ h ≫ q := by
  have e : functionFieldMap (h ≫ p) = (functionFieldMap h).comp (functionFieldMap p) :=
    RingHom.ext fun t =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply h p t).symm
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, H, ← Category.assoc,
    functionFieldMap_fromSpecStalk h, Category.assoc]

/-- **A common model lies over the base.** If `q = φ ∘ p` at the generic point of `W` and
`g ∘ φ = f`, then `p ≫ f = q ≫ g`, for `W` reduced and `Z` separated. -/
private theorem comp_eq_comp_of_specMap_fromFunctionField_eq {W X Y Z : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Z ↘ ⊤_ Scheme)] {φ : X.RationalMap Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hφ : φ.compHom g = f.toRationalMap) (p : W ⟶ X) [IsDominant p]
    (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    p ≫ f = q ≫ g := by
  have h1 : (p ≫ f).toRationalMap = (q ≫ g).toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom,
      ← Category.assoc, ← functionFieldMap_fromSpecStalk p, Category.assoc,
      ← MMP.Flips.RationalMap.fromFunctionField_hom f, ← hφ,
      MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc, H, Category.assoc]
  obtain ⟨U, hU, hUl, hUr, e⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h1
  have : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  have : Z.IsSeparated := ⟨‹_›⟩
  refine ext_of_isDominant (ι := U.ι) ?_
  simp only [Scheme.PartialMap.restrict_hom, Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom,
    Category.assoc] at e
  exact (Scheme.homOfLE_ι_assoc W hUl _).symm.trans (e.trans (Scheme.homOfLE_ι_assoc W hUr _))

end CommonModel

/-- **Composing a common model with a model of it.** If `(W, p, q)` is a common model of `φ` and
`h : W' ⟶ W` is a proper birational morphism from a normal variety, then `(W', h ≫ p, h ≫ q)` is a
common model of `φ`. -/
private theorem isCommonModel_comp {k : Type u} [Field k] {X Y Z W W' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q) (h : W' ⟶ W)
    [IsProper h] (hh : IsBirationalMorphism h) (hW' : IsNormalVariety k (h ≫ sW)) :
    IsCommonModel k sX sY sZ (h ≫ sW) f g φ (h ≫ p) (h ≫ q) := by
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsIntegral W' := hW'.1.toIsIntegral
  haveI := hW.isProper_p
  haveI := hW.isProper_q
  haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
  haveI : IsDominant h := hh.isDominant
  have hhB := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hh
  have KF := specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  exact
    { isVariety_X := hW.isVariety_X
      isVariety_Y := hW.isVariety_Y
      isVariety_Z := hW.isVariety_Z
      comp_f := hW.comp_f
      comp_g := hW.comp_g
      isProper_f := hW.isProper_f
      isProper_g := hW.isProper_g
      isModificationOf := hW.isModificationOf
      isNormalVariety := hW'
      comp_p := by rw [Category.assoc, hW.comp_p]
      comp_q := by rw [Category.assoc, hW.comp_q]
      isProper_p := inferInstance
      isProper_q := inferInstance
      isBirationalMorphism_p := isBirationalMorphism_comp_of_isBirational p h
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          hW.isBirationalMorphism_p) hhB
      isBirationalMorphism_q := isBirationalMorphism_comp_of_isBirational q h
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          hW.isBirationalMorphism_q) hhB
      comp_eq := comp_eq_of_specMap_fromFunctionField_eq φ (h ≫ p) (h ≫ q)
        (specMap_fromFunctionField_comp φ h p q KF) }

/-- Numerical equivalence over a base is reflexive on `ℝ`-Cartier divisors. -/
private theorem isNumericallyEquivalentOver_self {k : Type u} [Field k] {W X : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    {p : W ⟶ X} {D : RDivisor W} (hD : IsCartierCombination D) :
    IsNumericallyEquivalentOver k sW p D D :=
  ⟨hD, hD, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ hx₁ hx₂ =>
    (IsRIntersectionNumber.eq_and_linear k _ C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ hx₁ hx₂⟩

/-- **Nefness of `q^*A_Y - N` over `X`.** Let `p : W ⟶ X`, `q : W ⟶ Y` with `p ≫ f = q ≫ g`. If
`A_Y` is `g`-nef and `N` is an `ℝ`-Cartier divisor on `W` with `N · C = 0` for every proper curve
`C`, then `q^*A_Y - N` is `p`-nef. -/
private theorem isRelativelyNef_sub_of_isRCartierPullback_of_comp_eq {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (p : W ⟶ X) (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (f : X ⟶ Z)
    (g : Y ⟶ Z) (hcomm : p ≫ f = q ≫ g) {A_Y : RDivisor Y} (hAY : IsRelativelyNef k sY g A_Y)
    {G_Y : RDivisor W} (hGY : IsRCartierPullback q A_Y G_Y) {N : RDivisor W}
    (hNc : IsCartierCombination N)
    (hN0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW N r L C x → x = 0) :
    IsRelativelyNef k sW p (G_Y - N) := by
  obtain ⟨m, r, L, hL, hpres⟩ :=
    isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY) hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C hC x hx => ?_⟩
  obtain ⟨mY, rY, LY, hLY, hYpres⟩ := isCartierCombination_of_isRCartierPullback hGY
  obtain ⟨mN, rN, LN, hLN, hNpres⟩ := hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hYpres hNpres
  have hY := isRIntersectionNumber_sum_degreeOn k sW C rY LY hLY
  have hN := isRIntersectionNumber_sum_degreeOn k sW C rN LN hLN
  rw [← hYpres] at hY
  rw [← hNpres] at hN
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hY hN
  have e : (1 : ℝ) • G_Y + (-1 : ℝ) • N = G_Y - N := by
    simp only [one_smul, neg_one_smul]
    abel
  rw [e] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx hsum]
  have hC' : C.IsContractedBy (q ≫ g) := fun z hz => by
    rw [← hcomm, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]
  have h1 := hAY.nonneg_of_isRCartierPullback q hq g rfl hGY C hC' hY
  rw [hN0 C hN]
  linarith

/-- **FA 2.23.3 on a common model.** For a weak log canonical model `g : (Y, D_{𝓕,Y}) ⟶ Z` of
`f : (X, D_X) ⟶ Z`, a common model `(W, p, q)` of `φ` and any prime divisor `P` of `W`,
`a(ord_P, D_{𝓕,Y}) ≥ a(ord_P, D_X)`. -/
public theorem isDiscrepancy_le_of_isCommonModel {k : Type u}
    [Field k] [PerfectField k] {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    (P₀ : Mori.PrimeDivisor W) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hW.comp_p ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_p, E := P₀, isProper := hW.isProper_p }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hW.comp_q ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_q, E := P₀, isProper := hW.isProper_q }
    ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
      IsDiscrepancy sX n K_X D_X EX.valuation a' → a' ≤ a := by
  intro EX EY a a' ha ha'
  obtain ⟨-, -, -, ⟨hXn, hYn, -⟩, -, ⟨-, -, hAY⟩, -⟩ := id hM
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hWn.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hpb := hW.isBirationalMorphism_p
  have hqb := hW.isBirationalMorphism_q
  haveI := hW.isProper_p
  haveI := hW.isProper_q
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  haveI := hYn.1.toQuasiCompact
  haveI := hW.isVariety_Z.toIsSeparated
  haveI := isSeparated_toTerminal sZ
  have hWp : IsNormalVariety k (p ≫ sX) := hW.comp_p ▸ hWn
  have hWq : IsNormalVariety k (q ≫ sY) := hW.comp_q ▸ hWn
  have KF := specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  have hcomm : p ≫ f = q ≫ g :=
    comp_eq_comp_of_specMap_fromFunctionField_eq hW.isModificationOf.2 p q KF
  -- the forms `ω_X`, `ω_Y` with `K_X = div ω_X`, `K_Y = div ω_Y` used in the discrepancies
  obtain ⟨hKXc, hBXc, -, _EX, ωX, _mX, _rX, _LX, -, hωXK, hwX⟩ := id ha'
  obtain ⟨hKYc, hBYc, -, _EY, ωY, _mY, _rY, _LY, -, hωYK, hwY⟩ := id ha
  subst hωXK hωYK
  have hn : topologicalKrullDim X = n := hKXc.topologicalKrullDim_eq
  have htrX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have htrY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
    hKYc.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← toENat_trdeg_functionField (sX := p ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX p hpb.functionFieldMap_bijective,
      toENat_trdeg_functionField (sX := sX), hn]
  have hpω := pullbackRationalPluriForms_ne_zero p hpb.functionFieldMap_bijective htrX hwX.2.2.1
  have hqω := pullbackRationalPluriForms_ne_zero q hqb.functionFieldMap_bijective htrY hwY.2.2.1
  -- `L₁ = div_W(q^*ω_Y) - div_W(p^*ω_X)` is principal
  obtain ⟨L₁, hL₁_def⟩ : ∃ L₁ : Divisor W,
      L₁ = divisorOfForm (pullbackRationalPluriForms sY q ωY) -
        divisorOfForm (pullbackRationalPluriForms sX p ωX) := ⟨_, rfl⟩
  have hL₁ : L₁.LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm_of_eq
      (hW.comp_q.trans hW.comp_p.symm) hWp hnW hqω hpω
    exact ⟨φ, by rwa [sub_zero, hL₁_def]⟩
  have hL₁c : L₁.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hL₁ Divisor.isCartier_zero
  -- `p^*(K_X + D_X) - q^*(K_Y + G) + L₁ = ∑ (a_Y(P) - a_X(P)) P`
  obtain ⟨G_X, hGX, -⟩ := existsUnique_isRCartierPullback p hBXc
  obtain ⟨G_Y, hGY, -⟩ := existsUnique_isRCartierPullback q hBYc
  -- `a(P, D_X) = ord_P(p^*ω_X) - coeff_P(G_X)` and likewise over `Y`
  set dX := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX))
  set dY := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY))
  have haX : ∀ P, IsDiscrepancy sX n (divisorOfForm ωX) D_X
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance).valuation
      (dX.coeff P - G_X.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hXn ωX hwX.2.2.1 hKXc hBXc p hWp hpb hGX P
  have haY : ∀ P, IsDiscrepancy sY n (divisorOfForm ωY) G
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance).valuation
      (dY.coeff P - G_Y.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hYn ωY hwY.2.2.1 hKYc hBYc q hWq hqb hGY P
  have hcoeff : ∀ P, (G_X - G_Y + Divisor.toRDivisor L₁).coeff P =
      (dY.coeff P - G_Y.coeff P) - (dX.coeff P - G_X.coeff P) := by
    intro P
    rw [hL₁_def, map_sub]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  -- `M = q^*(K_Y + G) - L₁` is `p`-nef
  have hL₁r : IsCartierCombination (Divisor.toRDivisor L₁) :=
    ⟨1, fun _ => 1, fun _ => L₁, fun _ => hL₁c, by simp [← toRDivisor_eq_mapCoeffs]⟩
  have hMnef : IsRelativelyNef k sW p (G_Y - Divisor.toRDivisor L₁) :=
    isRelativelyNef_sub_of_isRCartierPullback_of_comp_eq p q hW.comp_q f g hcomm hAY hGY hL₁r
      fun C _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁c hL₁ C hx
  -- the coefficients along prime divisors not exceptional over `X` are nonnegative
  have hBG : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sX p P →
      0 ≤ (G_X - G_Y + Divisor.toRDivisor L₁).coeff P := by
    intro P hP
    rw [hcoeff P, sub_nonneg]
    exact NonExceptional.main hM hW P
      (fun h => hP ⟨hWp, hpb, inferInstance, h⟩) _ _ (haY P) (haX P)
  have hMc := isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY) hL₁r
  have hBc := isCartierCombination_add (isCartierCombination_sub
    (isCartierCombination_of_isRCartierPullback hGX)
    (isCartierCombination_of_isRCartierPullback hGY)) hL₁r
  have hnum : IsNumericallyEquivalentOver k sW p G_X
      ((G_Y - Divisor.toRDivisor L₁) + (G_X - G_Y + Divisor.toRDivisor L₁)) := by
    rw [sub_add_add_cancel, add_sub_cancel]
    exact isNumericallyEquivalentOver_self (isCartierCombination_of_isRCartierPullback hGX)
  -- the negativity lemma
  have hB := isEffective_of_isNumericallyEquivalentOver_pullback k sX sW hXn hWn p hW.comp_p hpb
    hBXc hGX hMc hMnef hBc hBG hnum P₀
  rw [hcoeff P₀, sub_nonneg] at hB
  rwa [ha.eq (haY P₀), ha'.eq (haX P₀)]

/-- **FA 2.23.3, the comparison of discrepancies.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log
canonical model of `f : (X, D_X) ⟶ Z` with respect to `𝓕` (`MMP.Flips.IsWeakLogCanonicalModelOf`,
with `G = D_{𝓕,Y}`), through the modification `φ : X ⤏ Y`, over a field of characteristic zero.
Let `B` be a divisor of `k(X) = k(Y)` with nonempty center on `X`. Here `B` is a valuation `v`
of `k(X)` and a valuation `v'` of `k(Y)`, both induced by one valuation `w` of `k(W)` on a common
model `(W, p, q)` of `φ`. Then `B` has nonempty center on `Y` and `a(B, D_{𝓕,Y}) ≥ a(B, D_X)`. -/
private theorem IsWeakLogCanonicalModelOf.isDiscrepancy_le {k : Type u} [Field k] [CharZero k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℕ}
    {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    {v : Valuation X.functionField ℤᵐ⁰} (hv : HasNonemptyCenter k sX v)
    {v' : Valuation Y.functionField ℤᵐ⁰} :
    haveI : IsIntegral W := hW.isNormalVariety.1.toIsIntegral
    haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
    haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
    ∀ w : Valuation W.functionField ℤᵐ⁰, w.comap (functionFieldMap p) = v →
      w.comap (functionFieldMap q) = v' →
      HasNonemptyCenter k sY v' ∧
        ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G v' a → IsDiscrepancy sX n K_X D_X v a' → a' ≤ a := by
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have hpb := hW.isBirationalMorphism_p
  haveI := hW.isProper_p
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
  intro w hwp hwq
  -- `B` is a prime divisor `E` of a model `h : W' ⟶ W`
  obtain ⟨-, D, rfl⟩ := hv
  obtain ⟨D₁, hD₁, -⟩ := ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq
    hW.isVariety_X p (hW.comp_p ▸ hWn.1) hpb D
  have hw : D₁.valuation = w :=
    valuation_comap_injective hpb.functionFieldMap_bijective.2 (hD₁.trans hwp.symm)
  haveI := D₁.isIntegral
  haveI := D₁.isNormal
  haveI := D₁.isLocallyNoetherian
  haveI := D₁.isDominant
  haveI := D₁.isProper
  have hW'n : IsNormalVariety k (D₁.f ≫ sW) := by
    rw [← hW.comp_p]
    exact D₁.isNormalVariety
  have hW' := isCommonModel_comp hW D₁.f D₁.isBirationalMorphism hW'n
  have key := isDiscrepancy_le_of_isCommonModel hM hW' D₁.E
  haveI : IsDominant (D₁.f ≫ p) := inferInstance
  haveI : IsDominant (D₁.f ≫ q) := inferInstance
  -- the valuations of `E` over `X` and over `Y` are `v` and `v'`
  have hEX : (D₁.E.valuationOver (D₁.f ≫ p)) = D.valuation := by
    rwa [← comap_valuationOver]
  have hEY : (D₁.E.valuationOver (D₁.f ≫ q)) = v' := by
    rw [← comap_valuationOver, ← hwq]
    exact congrArg (fun u => u.comap (functionFieldMap q)) hw
  refine ⟨?_, fun a a' ha ha' => key a a' ?_ ?_⟩
  · rw [← hEY]
    exact hasNonemptyCenter_valuation
      { Y := D₁.Y, f := D₁.f ≫ q, isNormalVariety := hW'.comp_q ▸ hW'.isNormalVariety,
        isBirationalMorphism := hW'.isBirationalMorphism_q, E := D₁.E,
        isProper := hW'.isProper_q }
  · rwa [← hEY] at ha
  · rwa [← hEX] at ha'

end DiscrepancyGe

namespace Modification

open MMP MMP.Flips

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
      ((functionFieldMap_fromSpecStalk p).trans
        (MMP.Flips.RationalMap.fromFunctionField_hom p).symm)]

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
  obtain ⟨θ, hθb, -, hθ⟩ := exists_ringHom_of_specMap _ p q hp hq
    (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp)
  have hψθ := specMap_comp_fromFunctionField_of_isInverse hψ θ hθ
  have : IsIso (CommRingCat.ofHom θ) := (ConcreteCategory.isIso_iff_bijective _).mpr hθb
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom, MMP.Flips.RationalMap.fromFunctionField_hom,
    ← cancel_epi (Spec.map (CommRingCat.ofHom θ)), ← Category.assoc, hψθ,
    ← MMP.Flips.RationalMap.fromFunctionField_hom, ← hφ,
    MMP.Flips.RationalMap.fromFunctionField_compHom, ← hθ, Category.assoc]

/-- **The strict transform on a common model realizes a prime divisor.** Let `p : W ⟶ X`,
`q : W ⟶ Y` be proper birational morphisms from a normal variety `W` with `q = φ ∘ p` (some
inverse `h` of `p` has `h.compHom q = φ`). The strict transform `F'` on `W` of a prime divisor
`F` of `Y` makes `(W, p, F')` a divisor over `X` realizing `F` through `φ`. -/
private theorem exists_isRealizedOver_of_isInverse {k : Type u} [Field k] {X Y W : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
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
  have := isSeparated_toTerminal sY
  obtain ⟨g', hg'⟩ := φ.exists_rep
  exact ⟨g', q, hqb, hg', preimage_ι_comp_eq_of_specMap_fromFunctionField_eq p q φ
    (specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp) g' hg',
    divisorialValuation_comap_functionFieldMap_eq q FW F heq⟩

private theorem main : ∀ {k : Type u}
    [Field k] [CharZero k] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (hX : Mori.IsNormalVariety k sX)
    (hY : Mori.IsNormalVariety k sY) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY) [IsProper f] [IsProper g]
    (φ : X.RationalMap Y) (hφ : IsModificationOf f g φ),
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
  intro k _ _ X Y Z sX sY sZ hX hY f g hfs hgs _ _ φ hφ
  have h1 : RationalMap.IsMorphismInCodimOne φ :=
    RationalMap.isMorphismInCodimOne_of_isOver hX f g φ hφ.2
  obtain ⟨W, p, q, hWv, hWs, _, _, hpb, hqb, ⟨h, hinv, hcomp⟩, hpq⟩ :=
    CommonModel.main sX sY hX hY f g φ hφ
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
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have := hY.2
  have := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact exists_isRealizedOver_of_isInverse sX hY φ p q
    ⟨hWv, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2⟩
    (by rw [← hfs, ← hgs, ← Category.assoc, hpq, Category.assoc]) hpb hqb h hinv hcomp

end Modification

namespace CoefficientsForced

open MMP MMP.Flips

/-- Two models `p : W ⟶ X`, `a : A ⟶ X` of the same rational map `m : Spec k(X) ⟶ Y`, on which
prime divisors `F_W` and `E` both give the valuation `ord_F` of `k(Y)`, give the same valuation
of `k(X)`. -/
private theorem valuationOver_eq_of_specMap_comp {X Y W A : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral W] [IsIntegral A] [IsLocallyNoetherian W] [IsLocallyNoetherian A]
    [IsNormal W] [IsNormal A] [IsNormal Y] [IsLocallyNoetherian Y]
    (m : Spec X.functionField ⟶ Y) (p : W ⟶ X) (q : W ⟶ Y) (a : A ⟶ X) (pA : A ⟶ Y)
    [IsDominant p] [IsDominant q] [IsDominant a] [IsDominant pA]
    (hp : Function.Bijective (functionFieldMap p)) (hq : Function.Bijective (functionFieldMap q))
    (hW : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ pA)
    (FW : Mori.PrimeDivisor W) (E : Mori.PrimeDivisor A) (F : Mori.PrimeDivisor Y)
    (hFW : FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation)
    (hE : E.divisorialValuation.comap (functionFieldMap pA) = F.divisorialValuation) :
    FW.valuationOver p = E.valuationOver a := by
  obtain ⟨θ, hθb, hθ', hm⟩ := exists_ringHom_of_specMap m p q hp hq hW
  have hθA : (functionFieldMap a).comp θ = functionFieldMap pA := by
    have h := hA
    rw [← hm, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← functionFieldMap_fromSpecStalk pA] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp h))
  refine Valuation.ext fun t => ?_
  obtain ⟨s, rfl⟩ := hθb.2 t
  rw [Mori.PrimeDivisor.valuationOver_apply, Mori.PrimeDivisor.valuationOver_apply,
    ← RingHom.comp_apply (functionFieldMap p) θ, hθ',
    ← RingHom.comp_apply (functionFieldMap a) θ, hθA, ← Valuation.comap_apply, hFW, ← hE,
    Valuation.comap_apply]

/-- **Discrepancies of a realized divisor do not decrease on a weak log canonical model.** If a
divisor `E` over `X` realizes the prime divisor `F` of `Y` through `φ`, then
`a(E, D_X) ≤ a(ord_F, D_{𝓕,Y})`. The two valuations are identified on a smooth common model
`(W, p, q)` of `φ` by the strict transform of `F`. -/
public theorem isDiscrepancy_le_of_isRealizedOver {k : Type u} [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    {sZ : Z ⟶ Spec (.of k)} (hZ : Mori.IsVariety k sZ) (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {F : Mori.PrimeDivisor Y} {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E)
    {a b : ℝ} (hb : IsDiscrepancy sY n K_Y G F.divisorialValuation b)
    (ha : IsDiscrepancy sX n K_X D_X E.valuation a) : a ≤ b := by
  obtain ⟨hfP, hgP, hmod, ⟨hXn, hYn, -⟩, -⟩ := id hM
  haveI := hfP
  haveI := hgP
  obtain ⟨W, p, q, hWv, hWs, hpP, hqP, hpb, hqb, ⟨ψ, hinv, hψq⟩, hcomm⟩ :=
    CommonModel.main sX sY hXn hYn f g φ hmod
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).1
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWn : Mori.IsNormalVariety k (p ≫ sX) := ⟨hWv, inferInstance⟩
  have hqs : q ≫ sY = p ≫ sX := by rw [← hgs, ← hfs, ← Category.assoc, ← hcomm, Category.assoc]
  have KF := Modification.specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q ψ hinv hψq
  have hW : IsCommonModel k sX sY sZ (p ≫ sX) f g φ p q :=
    { isVariety_X := hXn.1
      isVariety_Y := hYn.1
      isVariety_Z := hZ
      comp_f := hfs
      comp_g := hgs
      isProper_f := hfP
      isProper_g := hgP
      isModificationOf := hmod
      isNormalVariety := hWn
      comp_p := rfl
      comp_q := hqs
      isProper_p := hpP
      isProper_q := hqP
      isBirationalMorphism_p := hpb
      isBirationalMorphism_q := hqb
      comp_eq := comp_eq_of_specMap_fromFunctionField_eq φ p q KF }
  -- the strict transform `F_W` of `F` on `W` carries `ord_F` through `q` and `E` through `p`
  obtain ⟨FW, hFWeq, hFWiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYn (hqs ▸ hWn) hqb F
  have hFW := divisorialValuation_comap_functionFieldMap_eq q FW F hFWeq
  obtain ⟨g₀, pE, hpE, hg₀, hcE, hval⟩ := hE
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := hpE.isDominant
  have hA : Spec.map (CommRingCat.ofHom (functionFieldMap E.f)) ≫ φ.fromFunctionField =
      E.Y.fromSpecStalk (genericPoint E.Y) ≫ pE :=
    hg₀ ▸ specMap_functionFieldMap_fromFunctionField E.f g₀ pE hcE
  have hv := valuationOver_eq_of_specMap_comp φ.fromFunctionField p q E.f pE
    hpb.functionFieldMap_bijective hqb.functionFieldMap_bijective KF hA FW E.E F hFW hval
  exact (DiscrepancyGe.IsWeakLogCanonicalModelOf.isDiscrepancy_le hM hW
    (hasNonemptyCenter_valuation E) FW.divisorialValuation hv hFW).2 b a hb ha

private theorem main : ∀ {k : Type u} [Field k]
    [CharZero k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    {sZ : Z ⟶ Spec (.of k)} (hZ : Mori.IsVariety k sZ) (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {F : Mori.PrimeDivisor Y} (hF : RationalMap.IsInverseExceptional φ F)
    {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E) {a : ℝ}
    (ha : IsDiscrepancy sX n K_X D_X E.valuation a),
    c F = min 1 (-a) := by
  intro k _ _ X Y Z sX sY _ _ _ _ _ _ _ _ _ _ _ n K_X D_X K_Y f g φ c G sZ hZ hfs hgs hM F hF
    E hE a ha
  obtain ⟨-, -, -, hFB, hKG, hRel, -⟩ := id hM
  obtain ⟨-, -, -, -, -, -, _, hFs, -, hc, -⟩ := id hFB
  obtain ⟨hc1, hcmin⟩ := hc F ((hFs F).2 hF)
  -- `a(ord_F, D_{𝓕,Y}) = -c F ≥ a(ord_F, D_X) = a`
  have hle := isDiscrepancy_le_of_isRealizedOver hZ hfs hgs hM hE
    (IsFBirationalTransform.isDiscrepancy_divisorialValuation hFB hRel.2.1.2.1 hKG hF) ha
  exact le_antisymm (le_min hc1 (by linarith)) (hcmin E a hE ha)

end CoefficientsForced

namespace Transport

open MMP MMP.Flips
open scoped WithZero

/-! ### Valuations -/

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
  haveI := B.isIntegral
  haveI := B.isNormal
  haveI := B.isLocallyNoetherian
  haveI := B.isDominant
  haveI := hpB.isDominant
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
dominant, `q` birational, and `θ : k(Y) → k(X)` induce `φ` with `p^* ∘ θ = q^*`. If
`φ_* Q = E` and the prime divisor `Q_W` of `W` lies over `η_Q` with `𝒪_{X,Q} ≅ 𝒪_{W,Q_W}`, then
`ord_Q ∘ θ = ord_E`. -/
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
  have hagree := preimage_ι_comp_eq_of_specMap_fromFunctionField_eq p q φ (by
    rw [← hθ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hpq]
    exact functionFieldMap_fromSpecStalk q) g' hg'
  have hmem : QW.genericPoint ∈ p ⁻¹ᵁ g'.domain := by
    change p QW.genericPoint ∈ g'.domain
    rwa [hQW]
  have hqQ : q QW.genericPoint = E.genericPoint := by
    let x : (p ⁻¹ᵁ g'.domain).toScheme := ⟨QW.genericPoint, hmem⟩
    have h1 : q ((p ⁻¹ᵁ g'.domain).ι x) = g'.hom ((p ∣_ g'.domain) x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hagree]
    have h2 : (p ∣_ g'.domain) x = ⟨Q.genericPoint, hP⟩ :=
      Subtype.ext ((morphismRestrict_base_coe p g'.domain x).trans hQW)
    rw [h2] at h1
    exact h1.trans hE.symm
  have := E.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q QW.genericPoint)) := by rw [hqQ]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing q hq QW.genericPoint
  rw [← divisorialValuation_comap_functionFieldMap_eq q QW E hqQ,
    ← divisorialValuation_comap_functionFieldMap_eq p QW Q hQW, ← hpq, Valuation.comap_comp]

/-- **Non-exceptional primes are read off through `θ`.** Let `p : W ⟶ X`, `q : W ⟶ Y` be
birational, `p` proper, and `θ : k(Y) ≅ k(X)` induce `φ` with `p^* ∘ θ = q^*`. A prime divisor
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
  have hinj := valuation_comap_injective (R := Y.functionField) hθb.2
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
public theorem isDiscrepancy_neg_coeff {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
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
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

end Transport

/-! ### The composite `ψ = φ₂ ∘ φ₁⁻¹` at the generic points -/

namespace Composite

private theorem fromSpecStalkOfMem_homOfLE {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (x : X)
    (hx : x ∈ U) :
    U.fromSpecStalkOfMem x hx ≫ X.homOfLE h = V.fromSpecStalkOfMem x (h hx) := by
  rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]

private theorem restrictSource_hom {X Y : Scheme.{u}} (f : X.PartialIso Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.source) :
    (f.restrictSource U hU hU').iso.hom ≫ (f.restrictSource U hU hU').target.ι =
      X.homOfLE (show (f.restrictSource U hU hU').source ≤ f.source from hU') ≫ f.iso.hom ≫
        f.target.ι := by
  have h : (Scheme.Opens.isoOfLE hU').inv ≫ (f.source.ι ⁻¹ᵁ U).ι = X.homOfLE hU' := by
    rw [← cancel_mono f.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  simp [Scheme.PartialIso.restrictSource]
  rw [← Category.assoc, h]

/-- The rational map `e₁⁻¹ ∘ e₂` composed at the generic point with `θ₁ : k(Y₁) → k(X)` inducing
`e₁` is `e₂`. -/
private theorem specMap_comp_fromFunctionField_symm_trans {X Y₁ Y₂ : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y₁] (e₁ : X.PartialIso Y₁) (e₂ : X.PartialIso Y₂)
    (θ₁ : Y₁.functionField →+* X.functionField)
    (hθ₁ : Spec.map (CommRingCat.ofHom θ₁) ≫ Y₁.fromSpecStalk (genericPoint Y₁) =
      e₁.toRationalMap.fromFunctionField) :
    Spec.map (CommRingCat.ofHom θ₁) ≫ (e₁.symm.trans e₂).toRationalMap.fromFunctionField =
      e₂.toRationalMap.fromFunctionField := by
  have hW : Dense ((e₁.source ⊓ e₂.source : X.Opens) : Set X) :=
    e₁.dense_source.inter_of_isOpen_right e₂.dense_source e₂.source.2
  let a := e₁.restrictSource (e₁.source ⊓ e₂.source) hW inf_le_left
  let b := e₂.restrictSource (e₁.source ⊓ e₂.source) hW inf_le_right
  have hab : a.source = b.source := rfl
  have hη : genericPoint X ∈ a.source := genericPoint_mem_of_dense a.dense_source
  have hηT : genericPoint Y₁ ∈ a.target := genericPoint_mem_of_dense a.dense_target
  have hηe₁ : genericPoint X ∈ e₁.source := genericPoint_mem_of_dense e₁.dense_source
  have hηe₂ : genericPoint X ∈ e₂.source := genericPoint_mem_of_dense e₂.dense_source
  have hζ : Spec.map (CommRingCat.ofHom θ₁) ≫ a.target.fromSpecStalkOfMem (genericPoint Y₁) hηT =
      a.source.fromSpecStalkOfMem (genericPoint X) hη ≫ a.iso.hom := by
    refine (cancel_mono a.target.ι).mp ?_
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hθ₁, Category.assoc,
      restrictSource_hom, ← Category.assoc, fromSpecStalkOfMem_homOfLE]
    rfl
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap]
  change Spec.map (CommRingCat.ofHom θ₁) ≫ a.target.fromSpecStalkOfMem (genericPoint Y₁) hηT ≫
    (a.iso.inv ≫ (X.isoOfEq hab).hom ≫ b.iso.hom) ≫ b.target.ι =
      e₂.source.fromSpecStalkOfMem (genericPoint X) hηe₂ ≫ e₂.iso.hom ≫ e₂.target.ι
  rw [← Category.assoc, hζ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    Category.assoc, restrictSource_hom, Scheme.isoOfEq_hom, Scheme.homOfLE_homOfLE_assoc,
    ← Category.assoc, fromSpecStalkOfMem_homOfLE]

end Composite

/-! ### Comparing the two models -/

open MMP MMP.Flips
open scoped WithZero

/-- Every valuation of `R` is pulled back from one of `S` along a bijective ring map `R → S`. -/
private theorem exists_comap_eq {R S : Type*} [Ring R] [Ring S] {θ : R →+* S}
    (hθ : Function.Bijective θ) (u : Valuation R ℤᵐ⁰) :
    ∃ v : Valuation S ℤᵐ⁰, v.comap θ = u := by
  let e := RingEquiv.ofBijective θ hθ
  refine ⟨u.comap e.symm.toRingHom, Valuation.ext fun t => ?_⟩
  change u (e.symm (θ t)) = u t
  rw [show θ t = e t from rfl, e.symm_apply_apply]

/-- On a normal variety over a perfect field, with `K` canonical and `K + D` `ℝ`-Cartier, every
divisor over `X` has a discrepancy `a(E, D)`. -/
private theorem exists_isDiscrepancy {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : Mori.IsNormalVariety k sX) {n : ℕ} {K : Mori.Divisor X}
    {D : Mori.RDivisor X} (hK : K.IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Mori.Divisor.toRDivisor K + D)) (B : ProperDivisorOver k sX) :
    ∃ b : ℝ, IsDiscrepancy sX n K D B.valuation b := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : Mori.divisorOfForm ω = K := Mori.DivisorWithCoeffs.ext' fun Γ => by
    rw [Mori.coeff_divisorOfForm, hω]
  obtain ⟨m, r, L, hLc, hsum⟩ := hKD
  have hsum' : Mori.Divisor.toRDivisor (Mori.divisorOfForm ω) + D =
      ∑ j, r j • Mori.Divisor.toRDivisor (L j) := hsum
  have := B.isIntegral
  have := B.isLocallyNoetherian
  have := B.isNormal
  have := B.isDominant
  have : CompactSpace B.Y := by
    have := B.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (B.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant B.f (hLc j)
  exact ⟨_, hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation B, B, ω, m, r, L,
    rfl, rfl, hX, hK.topologicalKrullDim_eq, hω0, hLc, hsum', L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- **A common model identifies the function fields.** For a modification `φ : X ⤏ Y` of
`f` into `g`, there is an isomorphism `θ : k(Y) ≅ k(X)` inducing `φ` at the generic points such
that every prime divisor `E` of `Y` which is not `φ⁻¹`-exceptional is `φ_* Q` with
`ord_Q ∘ θ = ord_E`, and a common model `(W, p, q)` of `φ` on which every valuation `v` of `k(X)`
and `v ∘ θ` of `k(Y)` come from one valuation of `k(W)`. -/
public theorem _root_.MMP.Flips.IsModificationOf.exists_ringHom_functionField
    {k : Type u} [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : Mori.IsNormalVariety k sX) (hY : Mori.IsNormalVariety k sY) (hZ : Mori.IsVariety k sZ)
    {f : X ⟶ Z} {g : Y ⟶ Z} (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY) [IsProper f] [IsProper g]
    {φ : X.RationalMap Y} (hφ : IsModificationOf f g φ) :
    ∃ θ : Y.functionField →+* X.functionField, Function.Bijective θ ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField ∧
      (∀ E : Mori.PrimeDivisor Y, ¬ RationalMap.IsInverseExceptional φ E →
        ∃ Q : Mori.PrimeDivisor X, Mori.RationalMap.transformPrimeDivisor φ Q = some E ∧
          Q.divisorialValuation.comap θ = E.divisorialValuation ∧
          ∀ D : Mori.RDivisor X, (Mori.RationalMap.transformDivisor φ D).coeff E = D.coeff Q) ∧
      ∃ (W : Scheme.{u}) (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y)
        (hW : IsCommonModel k sX sY sZ sW f g φ p q),
        haveI : IsIntegral W := hW.isNormalVariety.1.toIsIntegral
        haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
        haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
        ∀ v : Valuation X.functionField ℤᵐ⁰, ∃ w : Valuation W.functionField ℤᵐ⁰,
          w.comap (functionFieldMap p) = v ∧ w.comap (functionFieldMap q) = v.comap θ := by
  obtain ⟨W, p, q, hWv, hWs, hpP, hqP, hpb, hqb, ⟨ψ, hinv, hψq⟩, hcomm⟩ :=
    CommonModel.main sX sY hX hY f g φ hφ
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).1
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWn : Mori.IsNormalVariety k (p ≫ sX) := ⟨hWv, inferInstance⟩
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI := isSeparated_toTerminal sY
  have KF := Modification.specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q ψ hinv hψq
  obtain ⟨θ, hθb, hpq, hθ⟩ := exists_ringHom_of_specMap _ p q
    hpb.functionFieldMap_bijective hqb.functionFieldMap_bijective KF
  have hW : IsCommonModel k sX sY sZ (p ≫ sX) f g φ p q :=
    { isVariety_X := hX.1
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
      comp_eq := comp_eq_of_specMap_fromFunctionField_eq φ p q KF }
  refine ⟨θ, hθb, hθ, fun E hE => ?_, W, p ≫ sX, p, q, hW, fun v => ?_⟩
  · obtain ⟨Q, hQE, -, hcoeff⟩ := Transport.exists_valuation_eq_and_coeff_eq hX p q hWn hpb
      hqb.functionFieldMap_bijective θ hθb hθ hpq hE
    obtain ⟨QW, h1, h2, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hWn hpb Q
    exact ⟨Q, hQE, Transport.comap_divisorialValuation_eq_of_transformPrimeDivisor_eq_some p q
      hqb.functionFieldMap_bijective θ hθ hpq QW h1 hQE, hcoeff⟩
  · obtain ⟨w, hw⟩ := exists_comap_eq hpb.functionFieldMap_bijective v
    refine ⟨w, hw, ?_⟩
    rw [← hpq, Valuation.comap_comp, hw]

/-- **The comparison of discrepancies along a prime divisor of the first model.** Let
`g : (Y, D) ⟶ Z` and `g' : (Y', D') ⟶ Z` be weak log canonical models of `f : (X, D_X) ⟶ Z`
through `φ` and `φ'`, identified with `X` at the function fields by `θ` and `θ'`. For a prime
divisor `P` of `Y` and the valuation `v` of `k(X)` with `v ∘ θ = ord_P`,
`a(ord_P, D) ≤ a(v ∘ θ', D')`: if `P` is `φ⁻¹`-exceptional, `a(ord_P, D) = -c_P =
max {-1, a(v, D_X)}`, and `a(v ∘ θ', D') ≥ -1` as `(Y', D')` is lc and `≥ a(v, D_X)` by FA 2.23.3
for `g'`; otherwise `P = φ_* Q`, `v = ord_Q` and `a(ord_P, D) = -coeff_Q(D_X) = a(ord_Q, D_X)`. -/
private theorem le_isDiscrepancy_of_comap_eq {k : Type u} [Field k] [CharZero k]
    {X Y Y' Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sY' : Y' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    [LocallyOfFiniteType sY'] [QuasiCompact sY']
    (hZ : Mori.IsVariety k sZ) {f : X ⟶ Z} {g : Y ⟶ Z} {g' : Y' ⟶ Z} (hfZ : f ≫ sZ = sX)
    (hgZ : g ≫ sZ = sY) {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K : Mori.Divisor Y} {K' : Mori.Divisor Y'} {φ : X.RationalMap Y} {φ' : X.RationalMap Y'}
    {c : Mori.PrimeDivisor Y → ℝ} {c' : Mori.PrimeDivisor Y' → ℝ}
    {D : Mori.RDivisor Y} {D' : Mori.RDivisor Y'}
    (h : IsWeakLogCanonicalModelOf sY sX n K_X D_X K f g φ c D)
    (h' : IsWeakLogCanonicalModelOf sY' sX n K_X D_X K' f g' φ' c' D')
    {θ : Y.functionField →+* X.functionField} (hθb : Function.Bijective θ)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = φ.fromFunctionField)
    (hmatch : ∀ E : Mori.PrimeDivisor Y, ¬ RationalMap.IsInverseExceptional φ E →
      ∃ Q : Mori.PrimeDivisor X, Mori.RationalMap.transformPrimeDivisor φ Q = some E ∧
        Q.divisorialValuation.comap θ = E.divisorialValuation ∧
        ∀ D : Mori.RDivisor X, (Mori.RationalMap.transformDivisor φ D).coeff E = D.coeff Q)
    {θ' : Y'.functionField →+* X.functionField}
    (hge : ∀ v : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX v → ∀ a b : ℝ,
      IsDiscrepancy sY' n K' D' (v.comap θ') a → IsDiscrepancy sX n K_X D_X v b → b ≤ a)
    (P : Mori.PrimeDivisor Y) (v : Valuation X.functionField ℤᵐ⁰)
    (hv : v.comap θ = P.divisorialValuation) {a a' : ℝ}
    (ha : IsDiscrepancy sY' n K' D' (v.comap θ') a)
    (ha' : IsDiscrepancy sY n K D P.divisorialValuation a') : a' ≤ a := by
  obtain ⟨-, -, -, hFB, hKD, hRel, -⟩ := id h
  obtain ⟨hXn, -, -, -, hKX, hKXD, Fs, hFs, hreal, -, hG⟩ := id hFB
  have hlc := h'.2.2.2.2.2.1.2.1
  have hinj := valuation_comap_injective (R := Y.functionField) hθb.2
  by_cases hP : RationalMap.IsInverseExceptional φ P
  · obtain ⟨B, hB⟩ := hreal P ((hFs P).2 hP)
    obtain rfl : v = B.valuation :=
      hinj (hv.trans (Transport.comap_valuation_eq_of_isRealizedOver θ hθ hB).symm)
    obtain ⟨b, hb⟩ := exists_isDiscrepancy hXn hKX hKXD B
    have hcP := CoefficientsForced.main hZ hfZ hgZ h hP hB hb
    have ha'' := ha'.eq
      (IsFBirationalTransform.isDiscrepancy_divisorialValuation hFB hRel.2.1.2.1 hKD hP)
    have h1 : -1 ≤ a := hlc.2.2.2 _ ha.2.2.1 a ha
    have h2 : b ≤ a := hge _ hb.2.2.1 a b ha hb
    rw [ha'', hcP]
    have : -a ≤ min 1 (-b) := le_min (by linarith) (by linarith)
    linarith
  · obtain ⟨Q, hQE, hQv, hcoeff⟩ := hmatch P hP
    obtain rfl : v = Q.divisorialValuation := hinj (hv.trans hQv.symm)
    have hb := Transport.isDiscrepancy_neg_coeff hXn hKX hKXD Q
    have hDP : D.coeff P = D_X.coeff Q := by
      rw [hG, Mori.DivisorWithCoeffs.coeff_add, hcoeff, Transport.coeff_sum_single,
        if_neg (fun h => hP ((hFs P).1 h)), add_zero]
    rw [ha'.eq_neg_coeff, hDP]
    exact hge _ hb.2.2.1 a _ ha hb

end MMP.Flips.WeakLCModelsCompare

namespace MMP.Flips

open scoped WithZero

open WeakLCModelsCompare in
/-- **FA 2.24.2.** Let `X`, `Y₁`, `Y₂`, `Z` be varieties over a field `k` of characteristic zero
and `f`, `g₁`, `g₂` morphisms over `k`. Let `g₁ : (Y₁, D₁) ⟶ Z` and `g₂ : (Y₂, D₂) ⟶ Z` be weak
log canonical models of `f : (X, D_X) ⟶ Z` (`MMP.Flips.IsWeakLogCanonicalModelOf`) through
`φ₁ : X ⤏ Y₁` and `φ₂ : X ⤏ Y₂`, with respect to the coefficient families `c₁` and `c₂`. Let
`ψ : Y₁ ⤏ Y₂` be `φ₂ ∘ φ₁⁻¹`, that is, the rational map of `e₁.symm.trans e₂` for partial
isomorphisms `e₁`, `e₂` representing `φ₁`, `φ₂`. Then, for some admissible coefficient family `c'`
on `Y₂`, `g₂ : (Y₂, D₂) ⟶ Z` is a weak log canonical model of `g₁ : (Y₁, D₁) ⟶ Z` through `ψ`
with respect to `c'`, namely `c'_F = coeff_F(D₂)`. -/
@[mmp "lem_fa2_weak_lc_models_compare"]
public theorem IsWeakLogCanonicalModelOf.exists_isWeakLogCanonicalModelOf_trans
    {k : Type u} [Field k] [CharZero k] {X Y₁ Y₂ Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY₁ : Y₁ ⟶ Spec (.of k)} {sY₂ : Y₂ ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y₁] [IsLocallyNoetherian Y₁] [IsNormal Y₁] [CompactSpace Y₁]
    [LocallyOfFiniteType sY₁] [QuasiCompact sY₁]
    [IsIntegral Y₂] [IsLocallyNoetherian Y₂] [IsNormal Y₂] [CompactSpace Y₂]
    [LocallyOfFiniteType sY₂] [QuasiCompact sY₂]
    (hX : Mori.IsVariety k sX) (hY₁ : Mori.IsVariety k sY₁) (hY₂ : Mori.IsVariety k sY₂)
    (hZ : Mori.IsVariety k sZ)
    {f : X ⟶ Z} {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z} (hfZ : f ≫ sZ = sX) (hg₁Z : g₁ ≫ sZ = sY₁)
    (hg₂Z : g₂ ≫ sZ = sY₂) {n : ℕ}
    {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K₁ : Mori.Divisor Y₁} {K₂ : Mori.Divisor Y₂}
    {φ₁ : X.RationalMap Y₁} {φ₂ : X.RationalMap Y₂}
    {c₁ : Mori.PrimeDivisor Y₁ → ℝ} {c₂ : Mori.PrimeDivisor Y₂ → ℝ}
    {D₁ : Mori.RDivisor Y₁} {D₂ : Mori.RDivisor Y₂}
    (h₁ : IsWeakLogCanonicalModelOf sY₁ sX n K_X D_X K₁ f g₁ φ₁ c₁ D₁)
    (h₂ : IsWeakLogCanonicalModelOf sY₂ sX n K_X D_X K₂ f g₂ φ₂ c₂ D₂)
    {ψ : Y₁.RationalMap Y₂}
    (hψ : ∃ (e₁ : X.PartialIso Y₁) (e₂ : X.PartialIso Y₂), e₁.toRationalMap = φ₁ ∧
      e₂.toRationalMap = φ₂ ∧ (e₁.symm.trans e₂).toRationalMap = ψ) :
    ∃ c' : Mori.PrimeDivisor Y₂ → ℝ,
      IsWeakLogCanonicalModelOf sY₂ sY₁ n K₁ D₁ K₂ g₁ g₂ ψ c' D₂ := by
  obtain ⟨e₁, e₂, he₁, he₂, hψe⟩ := hψ
  obtain ⟨hf, hg₁, hmod₁, hFB₁, hKD₁, hRel₁, -⟩ := id h₁
  obtain ⟨-, hg₂, hmod₂, hFB₂, hKD₂, hRel₂, -⟩ := id h₂
  haveI := hf
  haveI := hg₁
  haveI := hg₂
  have hXn := hFB₁.1
  have hY₁n := hFB₁.2.1
  have hY₂n := hFB₂.2.1
  have hKY₁ := hRel₁.2.1.2.1
  have hKY₂ := hRel₂.2.1.2.1
  obtain ⟨θ₁, hθ₁b, hθ₁, hmatch₁, W₁, sW₁, p₁, q₁, hW₁, hw₁⟩ :=
    IsModificationOf.exists_ringHom_functionField hXn hY₁n hZ hfZ hg₁Z hmod₁
  obtain ⟨θ₂, hθ₂b, hθ₂, hmatch₂, W₂, sW₂, p₂, q₂, hW₂, hw₂⟩ :=
    IsModificationOf.exists_ringHom_functionField hXn hY₂n hZ hfZ hg₂Z hmod₂
  have hge₁ : ∀ v : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX v → ∀ a b : ℝ,
      IsDiscrepancy sY₁ n K₁ D₁ (v.comap θ₁) a → IsDiscrepancy sX n K_X D_X v b → b ≤ a :=
    fun v hv => by
      obtain ⟨w, hwp, hwq⟩ := hw₁ v
      exact (DiscrepancyGe.IsWeakLogCanonicalModelOf.isDiscrepancy_le h₁ hW₁ hv w hwp hwq).2
  have hge₂ : ∀ v : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX v → ∀ a b : ℝ,
      IsDiscrepancy sY₂ n K₂ D₂ (v.comap θ₂) a → IsDiscrepancy sX n K_X D_X v b → b ≤ a :=
    fun v hv => by
      obtain ⟨w, hwp, hwq⟩ := hw₂ v
      exact (DiscrepancyGe.IsWeakLogCanonicalModelOf.isDiscrepancy_le h₂ hW₂ hv w hwp hwq).2
  /- `ψ` is a modification of `g₁` into `g₂` -/
  have hψ₁ : Spec.map (CommRingCat.ofHom θ₁) ≫ ψ.fromFunctionField = φ₂.fromFunctionField := by
    rw [← hψe, ← he₂]
    exact Composite.specMap_comp_fromFunctionField_symm_trans e₁ e₂ θ₁ (he₁ ▸ hθ₁)
  haveI : IsIso (CommRingCat.ofHom θ₁) := (ConcreteCategory.isIso_iff_bijective _).mpr hθ₁b
  have hover : RationalMap.IsOver g₁ g₂ ψ := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [MMP.Flips.RationalMap.fromFunctionField_compHom,
      MMP.Flips.RationalMap.fromFunctionField_hom, ← cancel_epi (Spec.map (CommRingCat.ofHom θ₁)),
      ← Category.assoc, hψ₁, ← Category.assoc, hθ₁,
      ← MMP.Flips.RationalMap.fromFunctionField_compHom,
      ← MMP.Flips.RationalMap.fromFunctionField_compHom, hmod₁.2, hmod₂.2]
  have hmodψ : IsModificationOf g₁ g₂ ψ := ⟨⟨_, hψe⟩, hover⟩
  obtain ⟨hcodψ, -, hfinψ, hrealψ⟩ :=
    Modification.main sY₁ sY₂ sZ hY₁n hY₂n g₁ g₂ hg₁Z hg₂Z ψ hmodψ
  obtain ⟨θψ, hθψb, hθψ, hmatchψ, -⟩ :=
    IsModificationOf.exists_ringHom_functionField hY₁n hY₂n hZ hg₁Z hg₂Z hmodψ
  have hθ₂ψ : θ₁.comp θψ = θ₂ := by
    have H : Spec.map (CommRingCat.ofHom (θ₁.comp θψ)) ≫ Y₂.fromSpecStalk (genericPoint Y₂) =
        Spec.map (CommRingCat.ofHom θ₂) ≫ Y₂.fromSpecStalk (genericPoint Y₂) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hθψ, hψ₁, hθ₂]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp H))
  /- valuations of `k(Y₁)` and their transports -/
  have hlift : ∀ u : Valuation Y₁.functionField ℤᵐ⁰, ∃ v : Valuation X.functionField ℤᵐ⁰,
      v.comap θ₁ = u ∧ v.comap θ₂ = u.comap θψ := fun u => by
    obtain ⟨v, hv⟩ := exists_comap_eq hθ₁b u
    exact ⟨v, hv, by rw [← hθ₂ψ, Valuation.comap_comp, hv]⟩
  have hdY₁ := Transport.isDiscrepancy_neg_coeff hY₁n hKY₁ hKD₁
  have hdY₂ := Transport.isDiscrepancy_neg_coeff hY₂n hKY₂ hKD₂
  refine ⟨D₂.coeff, hg₁, hg₂, hmodψ, ⟨hY₁n, hY₂n, hmodψ.1, hcodψ, hKY₁, hKD₁,
    hfinψ.toFinset, fun F => hfinψ.mem_toFinset, fun F _ => hrealψ F,
    fun F _ => ⟨(hRel₂.2.1.1.isBoundary F).2, fun E a hE ha => ?_⟩, ?_⟩, hKD₂, hRel₂, ?_⟩
  · -- admissibility: `a(ord_F, D₂) ≤ a(E, D₁)`
    obtain ⟨v, hv₁, hv₂⟩ := hlift E.valuation
    rw [Transport.comap_valuation_eq_of_isRealizedOver θψ hθψ hE] at hv₂
    have key := le_isDiscrepancy_of_comap_eq hZ hfZ hg₂Z h₂ h₁ hθ₂b hθ₂ hmatch₂ hge₁ F v hv₂
      (hv₁ ▸ ha) (hdY₂ F)
    exact (min_le_right _ _).trans (by linarith)
  · -- `D₂ = ψ_* D₁ + ∑ c'_F F`
    refine Mori.DivisorWithCoeffs.ext' fun F => ?_
    rw [Mori.DivisorWithCoeffs.coeff_add, Transport.coeff_sum_single]
    by_cases hF : RationalMap.IsInverseExceptional ψ F
    · rw [show (Mori.RationalMap.transformDivisor ψ D₁).coeff F = 0 from
          mapPrimeDivisors_apply_eq_zero_of_forall_ne hF D₁,
        if_pos (hfinψ.mem_toFinset.2 hF), zero_add]
    · obtain ⟨P, -, hPF, hcoeff⟩ := hmatchψ F hF
      rw [hcoeff, if_neg (fun h => hF (hfinψ.mem_toFinset.1 h)), add_zero]
      obtain ⟨v, hv₁, hv₂⟩ := hlift P.divisorialValuation
      rw [hPF] at hv₂
      have k₁ := le_isDiscrepancy_of_comap_eq hZ hfZ hg₁Z h₁ h₂ hθ₁b hθ₁ hmatch₁ hge₂ P v hv₁
        (hv₂ ▸ hdY₂ F) (hdY₁ P)
      have k₂ := le_isDiscrepancy_of_comap_eq hZ hfZ hg₂Z h₂ h₁ hθ₂b hθ₂ hmatch₂ hge₁ F v hv₂
        (hv₁ ▸ hdY₁ P) (hdY₂ F)
      linarith
  · -- the discrepancy inequality along the `ψ`-exceptional primes of `Y₁`
    intro hψ' P _ E a a' hE ha ha'
    obtain ⟨v, hv₁, hv₂⟩ := hlift P.divisorialValuation
    rw [← Transport.valuation_eq_comap_of_isRealizedOver_inverse hψ' θψ hθψb hθψ hE] at hv₂
    exact le_isDiscrepancy_of_comap_eq hZ hfZ hg₁Z h₁ h₂ hθ₁b hθ₁ hmatch₁ hge₂ P v hv₁
      (hv₂ ▸ ha) ha'

end MMP.Flips

end
