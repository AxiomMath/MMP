module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.MMP.MinimalModel.LogMinimalModelComparison
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelAdjointAmple
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Discrepancy comparison with the ample model

Let `(M, B_M, q, V, B_V)` be an ample-model datum of a birational contraction `f : X ⟶ Z` of a
projective lc fourfold pair `(X, B)`, and let `a : W ⟶ X`, `b : W ⟶ V` be birational morphisms
from a smooth projective variety, compatible with `q ∘ φ : X ⤏ V`. Then
`a^*(K_X + B) = b^*(K_V + B_V) + E` with `E ≥ 0` exceptional over `V`.

A smooth projective `W'` with projective birational `g₁ : W' ⟶ W`, `g₂ : W' ⟶ M` and
`g₁ ≫ b = g₂ ≫ q` dominates both `W` and `M`. On `W'` the comparison of adjoints of the log
minimal model `(M, B_M)` gives `(g₁ ≫ a)^*(K_X + B) = g₂^*(K_M + B_M) + F` with `F ≥ 0`
exceptional over `M`, and `K_M + B_M = q^*(K_V + B_V)`. The coefficient of `F` along the strict
transform `P'` of a prime divisor `P` of `W` is the coefficient of `E` along `P`, since `g₁` is a
local isomorphism at `η_{P'}`; a divisor exceptional over `M` is exceptional over `V`, because the
proper birational `q` is an isomorphism in codimension one over the normal `V`.

## Main results

* `MMP.Fourfold.IsAmpleModelDatum.nonneg_sub_and_isExceptionalPrimeDivisor`: `G_X - G_V ≥ 0`
  for the pull-backs `G_X = a^*(K_X + B)`, `G_V = b^*(K_V + B_V)`, and every prime divisor in its
  support is exceptional over `V`.

## Implementation notes

* The auxiliary lemmas live in the namespace `Proof_lem_oai4_c3_ample_model_comparison`, opened
  only for the main result.
* The canonical divisors are compatible on `W` but not on `W'`: a canonical divisor `K_{W'}`
  with `g₂_* K_{W'} = K_M` pushes forward to `K_W + div ρ` on `W`. Twisting `K_X`, `K_V` and both
  pull-backs by the principal divisors `div ρ_X`, `div ρ_V` with `a^* ρ_X = b^* ρ_V = ρ` leaves
  `G_X - G_V` unchanged and makes all canonical divisors compatible with `K_{W'}`.
* Coefficients of pull-backs along dominant morphisms of integral schemes are orders of the
  pulled-back local equations in the function field; the comparison of coefficients along
  `P'` and `P` is done in these terms, without a general composition law for pull-backs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_oai4_c3_ample_model_comparison

open MMP.Mori MMP.Fourfold

/-! ### Birational morphisms and rational maps -/

section RationalMap

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have heq : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE (inf_le_left : U ≤ U₁) ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by
      rw [heq]
      infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U (U.2.dense hne)

/-- Two morphisms into `M` which agree after `q` agree, if their common composite lands in an
open `O` over which `q` is an isomorphism. -/
private theorem eq_of_comp_eq_of_isIso_morphismRestrict {T M V : Scheme.{u}} (q : M ⟶ V)
    (O : V.Opens) [IsIso (q ∣_ O)] {x₁ x₂ : T ⟶ M} (h : x₁ ≫ q = x₂ ≫ q)
    (hr : Set.range ⇑(x₁ ≫ q) ⊆ (O : Set V)) : x₁ = x₂ := by
  have h₁ : Set.range x₁ ⊆ Set.range (q ⁻¹ᵁ O).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hr ⟨t, rfl⟩
  have h₂ : Set.range x₂ ⊆ Set.range (q ⁻¹ᵁ O).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    have := hr ⟨t, rfl⟩
    rwa [h] at this
  let y₁ := IsOpenImmersion.lift (q ⁻¹ᵁ O).ι x₁ h₁
  let y₂ := IsOpenImmersion.lift (q ⁻¹ᵁ O).ι x₂ h₂
  have e₁ : y₁ ≫ (q ⁻¹ᵁ O).ι = x₁ := IsOpenImmersion.lift_fac _ _ _
  have e₂ : y₂ ≫ (q ⁻¹ᵁ O).ι = x₂ := IsOpenImmersion.lift_fac _ _ _
  have : y₁ ≫ (q ∣_ O) = y₂ ≫ (q ∣_ O) := by
    rw [← cancel_mono O.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, e₁, ← Category.assoc, e₂, h]
  rw [← e₁, ← e₂, (cancel_mono (q ∣_ O)).mp this]

/-- The generic point of the normal target of a proper birational morphism of varieties lies in
the biregular locus. -/
private theorem genericPoint_mem_biregularLocus {k : Type u} [Field k] {M V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (q : M ⟶ V) (hV : MMP.Mori.IsVariety k sV)
    (hM : MMP.Mori.IsVariety k (q ≫ sV)) [IsIntegral V] [IsNormal V] [IsProper q]
    (hq : IsBirationalMorphism q) : genericPoint V ∈ biregularLocus q := by
  by_contra hη
  have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sV q (hY := hV) (hX := hM) hq)
    (genericPoint V) hη
  rw [Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec V).specializes trivial] at h2
  exact absurd h2 (by decide)

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p :=
    h1.trans (Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _)
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- **Compatibility on a higher model.** If `ψ` is inverse to `a : W ⟶ X` with
`b ∘ ψ = q ∘ φ`, and `g₁ : W' ⟶ W`, `g₂ : W' ⟶ M` satisfy `g₁ ≫ b = g₂ ≫ q`, then the inverse
`ψ'` of `g₁ ≫ a` satisfies `g₂ ∘ ψ' = φ`, provided `q` is an isomorphism over an open containing
the generic point of `V`. -/
private theorem compHom_eq_of_isInverse {X W W' M V : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    [IsIntegral W'] [IsIntegral M] [IsIntegral V] (a : W ⟶ X) (b : W ⟶ V) (g₁ : W' ⟶ W)
    (g₂ : W' ⟶ M) (q : M ⟶ V) [IsDominant a] [IsDominant g₁] [IsDominant g₂] [IsDominant q]
    (O : V.Opens) [IsIso (q ∣_ O)] (hO : genericPoint V ∈ O)
    (hcomm : g₁ ≫ b = g₂ ≫ q) {ψ : X.RationalMap W}
    (hψ : RationalMap.IsInverse a.toRationalMap ψ) {φ : X.RationalMap M}
    (hφ : ψ.compHom b = φ.compHom q) {ψ' : X.RationalMap W'}
    (hψ' : RationalMap.IsInverse (g₁ ≫ a).toRationalMap ψ')
    (hbij : Function.Bijective (functionFieldMap (g₁ ≫ a))) :
    ψ'.compHom g₂ = φ := by
  obtain ⟨e', he'1, he'2⟩ := hψ'
  obtain ⟨e, he1, he2⟩ := hψ
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom]
  haveI : IsIso (CommRingCat.ofHom (functionFieldMap (g₁ ≫ a))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap (g₁ ≫ a)))),
    ← Category.assoc, ← he'2, specMap_functionFieldMap_fromFunctionField_symm (g₁ ≫ a) e' he'1]
  have hsplit : Spec.map (CommRingCat.ofHom (functionFieldMap (g₁ ≫ a))) =
      Spec.map (CommRingCat.ofHom (functionFieldMap g₁)) ≫
        Spec.map (CommRingCat.ofHom (functionFieldMap a)) := by
    rw [← Spec.map_comp]
    congr 1
    ext t
    exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g₁ a t).symm
  refine eq_of_comp_eq_of_isIso_morphismRestrict q O ?_ ?_
  · rw [Category.assoc, Category.assoc, ← MMP.Flips.RationalMap.fromFunctionField_compHom, ← hφ,
      MMP.Flips.RationalMap.fromFunctionField_compHom, hsplit, ← he2, Category.assoc,
      ← Category.assoc (Spec.map _) (e.symm.toRationalMap.fromFunctionField),
      specMap_functionFieldMap_fromFunctionField_symm a e he1]
    rw [← Category.assoc (Spec.map _) (W.fromSpecStalk _) b, functionFieldMap_fromSpecStalk g₁,
      Category.assoc, hcomm]
  · rintro _ ⟨t, rfl⟩
    have ht : W'.fromSpecStalk (genericPoint W') t = genericPoint W' := by
      rw [Subsingleton.elim t (IsLocalRing.closedPoint (W'.presheaf.stalk (genericPoint W'))),
        Scheme.fromSpecStalk_closedPoint]
    change q (g₂ (W'.fromSpecStalk (genericPoint W') t)) ∈ O
    rwa [ht, map_genericPoint_of_isDominant g₂, map_genericPoint_of_isDominant q]

end RationalMap

/-! ### Pull-backs along dominant morphisms of integral schemes -/

section Pullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- The pull-back `f^* φ` of a unit of `K(X)` is `φ` pulled back along `k(X) → k(Y)`. -/
private theorem evalFF_pullbackRationalFunction (f : Y ⟶ X) [IsDominant f]
    (φ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z, f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp)
    (Z : irreducibleComponents Y) (Z' : irreducibleComponents X) :
    MMP.Threefold.Mori.Helpers.evalFF Z (pullbackRationalFunction f φ hφ : RationalFunctions Y) =
      functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF Z' (φ : RationalFunctions X)) := by
  have hfY : f (componentGenericPoint Y Z) = genericPoint X := by
    rw [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  have hsp : f (componentGenericPoint Y Z) ⤳ componentGenericPoint X Z' := by
    rw [hfY]
    exact genericPoint_specializes _
  have hW : f (componentGenericPoint Y Z) ∈ Z'.1 := by
    have hZ : Z'.1 = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using Z'.2
    rw [hZ]
    trivial
  set v : (X.presheaf.stalk (componentGenericPoint X Z'))ˣ := RationalFunctions.unitsEquiv X φ Z'
  let a : (X.presheaf.stalk (f (componentGenericPoint Y Z)))ˣ :=
    Units.map (X.presheaf.stalkSpecializes hsp).hom.toMonoidHom v
  have ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) Z' := by
    change (X.presheaf.stalkSpecializes hsp ≫ X.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hpc := pullbackComponent_eq hφ (Divisor.isLocalEquation_principalDivisor φ ⊤) (Z := Z)
    trivial hW a ha
  have hY' : genericPoint Y ⤳ componentGenericPoint Y Z := genericPoint_specializes _
  have hgen : f (genericPoint Y) ⤳ componentGenericPoint X Z' := by
    rw [map_genericPoint_of_isDominant]
    exact genericPoint_specializes _
  have lhs : MMP.Threefold.Mori.Helpers.evalFF Z
      (pullbackRationalFunction f φ hφ : RationalFunctions Y) =
      (f.stalkMap (genericPoint Y)).hom
        ((X.presheaf.stalkSpecializes hgen).hom ((φ : RationalFunctions X) Z')) := by
    change (Y.presheaf.stalkSpecializes _).hom
      ((pullbackComponent f hφ (Divisor.isLocalEquation_principalDivisor φ ⊤) Z trivial :
        Y.presheaf.stalk (componentGenericPoint Y Z))) = _
    rw [hpc]
    change (Y.presheaf.stalkSpecializes hY').hom ((f.stalkMap (componentGenericPoint Y Z)).hom
      ((X.presheaf.stalkSpecializes hsp).hom ((φ : RationalFunctions X) Z'))) = _
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
    congr 1
    change (X.presheaf.stalkSpecializes hsp ≫ X.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  rw [lhs]
  have h₁ : f (genericPoint Y) ⤳ genericPoint X := by rw [map_genericPoint_of_isDominant]
  have h₂ : genericPoint X ⤳ componentGenericPoint X Z' := genericPoint_specializes _
  change _ = (f.stalkMap (genericPoint Y)).hom ((X.presheaf.stalkSpecializes h₁).hom
    ((X.presheaf.stalkSpecializes h₂).hom ((φ : RationalFunctions X) Z')))
  congr 1
  change _ = (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom _
  rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- The pull-back of a divisor with a local equation `φ` on `U` has the local equation `f^* φ`
on `f⁻¹ U`. -/
private theorem isLocalEquation_pullbackRationalFunction {f : Y ⟶ X} {D : Divisor X}
    {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp} {D' : Divisor Y}
    (hD' : D.IsPullback f hB D') {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφU : D.IsLocalEquation U φ)
    (hφ : ∀ Z, f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp) :
    D'.IsLocalEquation (f ⁻¹ᵁ U) (pullbackRationalFunction f φ hφ) := by
  intro E hE
  have hE' : (E.support ∩ f ⁻¹ᵁ (⊤ : X.Opens)).Nonempty := by
    obtain ⟨x, hx, -⟩ := hE
    exact ⟨x, hx, trivial⟩
  rw [hD' U φ hφU E hE]
  have hpr := Divisor.isPullback_principalDivisor φ hφ ⊤ φ
    (Divisor.isLocalEquation_principalDivisor φ ⊤) E hE'
  rw [coeff_principalDivisor] at hpr
  rw [hpr]
  have hW := mem_pointComponent (f (componentGenericPoint Y E.component))
  obtain ⟨a, ha⟩ := hφU.exists_unit_stalk (E.map_componentGenericPoint_mem f hE) (hB _) hW
  rw [pullbackComponent_eq hB hφU _ hW a ha, pullbackComponent_eq hφ _ _ hW a ha]

/-- The pull-back of a Cartier divisor along a dominant morphism of integral schemes is
Cartier. -/
private theorem isCartier_of_isPullback {f : Y ⟶ X} [IsDominant f] {D : Divisor X}
    (hD : D.IsCartier) {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp} {D' : Divisor Y}
    (hD' : D.IsPullback f hB D') : D'.IsCartier := by
  intro y
  obtain ⟨U, hU, φ, hφU⟩ := hD (f y)
  exact ⟨f ⁻¹ᵁ U, hU, _, isLocalEquation_pullbackRationalFunction hD' hφU
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _)⟩

/-- **Coefficients of a `ℚ`-pull-back.** If `D₀ = mD` is Cartier with a local equation `φ` on
`U ∋ f(η_E)`, then `m · coeff_E (f^* D) = v_E(f^* φ)`. -/
private theorem mul_coeff_eq_ord_of_isPullback {f : Y ⟶ X} [IsDominant f] {D : QDivisor X}
    {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp} {G : QDivisor Y}
    (hG : D.IsPullback f hB G) {m : ℕ} (hm : 0 < m) {D₀ : Divisor X}
    (hD₀ : Divisor.toQDivisor D₀ = (m : ℤ) • D) (hD₀c : D₀.IsCartier) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : D₀.IsLocalEquation U φ) (E : MMP.Mori.PrimeDivisor Y)
    (hE : f E.genericPoint ∈ U) (Z : irreducibleComponents X) :
    (m : ℚ) * G.coeff E = (Y.ord (functionFieldMap f
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))) E.genericPoint : ℚ) := by
  obtain ⟨D', hD', hp⟩ := hG m hm D₀ hD₀ hD₀c
  have h := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hp hφ E hE Z
  have h1 := congrArg (fun G : QDivisor Y => G.coeff E) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at h1
  rw [← h1, h]

/-- **Coefficients along a strict transform.** Let `g : Y' ⟶ Y` be a local isomorphism at the
generic point of a prime divisor `E'` of `Y'` lying over the prime divisor `E` of `Y`, and let
`G = f^* D`, where `D₀ = mD` is Cartier with a local equation `φ` near `f(η_E)`. A `ℚ`-divisor `G'`
on `Y'` with `m · coeff_{E'} G' = v_{E'}(g^* f^* φ)` has the coefficient of `G` along `E`. -/
private theorem coeff_eq_of_mul_coeff_eq_ord {Y' : Scheme.{u}} [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] (g : Y' ⟶ Y) [IsDominant g]
    {E' : MMP.Mori.PrimeDivisor Y'} {E : MMP.Mori.PrimeDivisor Y}
    (hE' : g E'.genericPoint = E.genericPoint) [IsIso (g.stalkMap E'.genericPoint)]
    {f : Y ⟶ X} [IsDominant f] {D : QDivisor X}
    {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp} {G : QDivisor Y}
    (hG : D.IsPullback f hB G) {m : ℕ} (hm : 0 < m) {D₀ : Divisor X}
    (hD₀ : Divisor.toQDivisor D₀ = (m : ℤ) • D) (hD₀c : D₀.IsCartier) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : D₀.IsLocalEquation U φ) (hE : f E.genericPoint ∈ U)
    (Z : irreducibleComponents X) {G' : QDivisor Y'}
    (hG' : (m : ℚ) * G'.coeff E' = (Y'.ord (functionFieldMap g (functionFieldMap f
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X)))) E'.genericPoint : ℚ)) :
    G'.coeff E' = G.coeff E := by
  rw [MMP.Positivity.ord_functionFieldMap_of_isIso g E' E hE',
    ← mul_coeff_eq_ord_of_isPullback hG hm hD₀ hD₀c hφ E hE Z] at hG'
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne') hG'

/-- A `ℚ`-divisor with a Cartier multiple `nB` pulling back to `nB'` is `ℚ`-Cartier with
pull-back `B'`. -/
private theorem isQCartier_and_isPullback_of_zsmul {f : Y ⟶ X} {B : QDivisor X}
    {B' : QDivisor Y} {n : ℕ} (hn : 0 < n) {T : Divisor X}
    (hTB : Divisor.toQDivisor T = (n : ℤ) • B) (hTc : T.IsCartier) {D' : Divisor Y}
    {hT : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ T.supp}
    (hTp : T.IsPullback f hT D') (hD' : Divisor.toQDivisor D' = (n : ℤ) • B') :
    B.IsQCartier ∧ ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp,
      B.IsPullback f hB B' := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQC : B.IsQCartier := ⟨n, hn', T, hTB, hTc⟩
  have hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp := fun Z hZ =>
    hT Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hn' hTB])
  refine ⟨hQC, hB, ?_⟩
  have hG := QDivisor.isPullback_pullback hQC hB
  obtain ⟨D'', hD'', hp⟩ := hG n hn T hTB hTc
  rw [hp.eq hTc hTp, hD'] at hD''
  have : B.pullback hQC hB = B' := by
    ext P
    have := congrArg (fun G : QDivisor Y => G.coeff P) hD''
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    exact (mul_left_cancel₀ (by exact_mod_cast hn') this).symm
  exact this ▸ hG

/-- **Twisting a pull-back by a principal divisor.** `f^*(D + div φ) = f^* D + div (f^* φ)`. -/
private theorem isPullback_add_principalDivisor {f : Y ⟶ X} [IsDominant f] {D : QDivisor X}
    (hDq : D.IsQCartier) {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp} {G : QDivisor Y}
    (hG : D.IsPullback f hB G) (φ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z, f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp) :
    ∃ hB' : ∀ Z, f (componentGenericPoint Y Z) ∉
        (D + Divisor.toQDivisor (principalDivisor φ)).supp,
      (D + Divisor.toQDivisor (principalDivisor φ)).IsPullback f hB'
        (G + Divisor.toQDivisor (principalDivisor (pullbackRationalFunction f φ hφ))) := by
  have hm := QDivisor.cartierIndex_pos hDq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDq
  obtain ⟨D₀', hD₀', hp⟩ := hG _ hm D₀ hD₀ hD₀c
  have hsupp : ∀ (C : Divisor X) (Z : irreducibleComponents Y),
      f (componentGenericPoint Y Z) ∉ C.supp := fun C Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f C Z
  have hc := Divisor.isCartier_principalDivisor φ
  have hpφ := (Divisor.isPullback_principalDivisor φ hφ).zsmul hc
    ((D.cartierIndex hDq : ℕ) : ℤ) (hsupp _)
  have hsum := hp.add hD₀c (hc.zsmul _) (hsupp _) hpφ
  exact (isQCartier_and_isPullback_of_zsmul hm
    (B := D + Divisor.toQDivisor (principalDivisor φ))
    (by rw [map_add, map_zsmul, hD₀, smul_add]) (hD₀c.add (hc.zsmul _)) hsum
    (by rw [map_add, map_zsmul, hD₀', smul_add])).2

/-- If `D₀ = m • D` for an integral divisor `D₀`, then `D = m⁻¹ • D₀` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_inv_smul {D : QDivisor X} {D₀ : Divisor X} {m : ℕ}
    (hm : (m : ℝ) ≠ 0) (h : Divisor.toQDivisor D₀ = (m : ℤ) • D) :
    QDivisor.toRDivisor D = (m : ℝ)⁻¹ • Divisor.toRDivisor D₀ := by
  ext P
  have := congrArg (fun T : QDivisor X => T.coeff P) h
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at this
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [show ((D₀.coeff P : ℤ) : ℝ) = (((D₀.coeff P : ℤ) : ℚ) : ℝ) by push_cast; rfl, this]
  push_cast
  field_simp

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor along a dominant morphism is `ℚ`-Cartier. -/
private theorem isQCartier_of_isPullback {f : Y ⟶ X} [IsDominant f] {D : QDivisor X}
    (hD : D.IsQCartier) {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp} {G : QDivisor Y}
    (hG : D.IsPullback f hB G) : G.IsQCartier := by
  have hm := QDivisor.cartierIndex_pos hD
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hD
  obtain ⟨D₀', hD₀', hp⟩ := hG _ hm D₀ hD₀ hD₀c
  exact ⟨_, by exact_mod_cast hm.ne', D₀', hD₀', isCartier_of_isPullback hD₀c hp⟩

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is an `ℝ`-Cartier pull-back. -/
private theorem isRCartierPullback_of_isPullback {f : Y ⟶ X} {D : QDivisor X}
    (hDq : D.IsQCartier) {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp} {G : QDivisor Y}
    (hG : D.IsPullback f hB G) :
    MMP.Flips.IsRCartierPullback f (QDivisor.toRDivisor D) (QDivisor.toRDivisor G) := by
  have hm := QDivisor.cartierIndex_pos hDq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDq
  obtain ⟨D₀', hD₀', hp⟩ := hG _ hm D₀ hD₀ hD₀c
  have hmR : ((D.cartierIndex hDq : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => ((D.cartierIndex hDq : ℕ) : ℝ)⁻¹, fun _ => D₀, fun _ => D₀',
    fun _ => hD₀c, ?_, fun _ => ⟨_, hp⟩, ?_⟩
  · rw [Fin.sum_univ_one]
    exact toRDivisor_eq_inv_smul hmR hD₀
  · rw [Fin.sum_univ_one]
    exact toRDivisor_eq_inv_smul hmR hD₀'

/-- On an integral scheme every nonzero rational function is the value of a unit of `K(X)` at
the generic point. -/
private theorem exists_units_evalFF_eq {g : X.functionField} (hg : g ≠ 0) :
    ∃ φ : (RationalFunctions X)ˣ, ∀ Z : irreducibleComponents X,
      MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X) = g := by
  have hmem : ∀ Z : irreducibleComponents X, genericPoint X ∈ Z.1 := fun Z =>
    Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _) trivial
  let j : ∀ Z : irreducibleComponents X,
      X.functionField →+* X.presheaf.stalk (componentGenericPoint X Z) := fun Z =>
    (X.presheaf.stalkSpecializes
      ((isGenericPoint_componentGenericPoint X Z).specializes (hmem Z))).hom
  refine ⟨Units.map (RingHom.pi j).toMonoidHom (Units.mk0 g hg), fun Z => ?_⟩
  change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom g = g
  rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Every unit of `K(Y)` is, up to its divisor, the pull-back of a unit of `K(X)` along a
birational `f`. -/
private theorem exists_principalDivisor_pullbackRationalFunction_eq (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (ρ : (RationalFunctions Y)ˣ) :
    ∃ (φ : (RationalFunctions X)ˣ)
      (hφ : ∀ Z, f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp),
      principalDivisor (pullbackRationalFunction f φ hφ) = principalDivisor ρ := by
  have Z₀ : irreducibleComponents Y := pointComponent (genericPoint Y)
  have hsubY : Subsingleton (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  set r := MMP.Threefold.Mori.Helpers.evalFF Z₀ (ρ : RationalFunctions Y)
  have hr : r ≠ 0 := (ρ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z₀)).ne_zero
  obtain ⟨rX, hrX⟩ := hf.2 r
  have hrX0 : rX ≠ 0 := fun h0 => hr (by rw [← hrX, h0, map_zero])
  obtain ⟨φ, hφe⟩ := exists_units_evalFF_eq hrX0
  have hφ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f
    (principalDivisor φ)
  refine ⟨φ, hφ, ?_⟩
  ext E
  rw [coeff_principalDivisor, coeff_principalDivisor, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    evalFF_pullbackRationalFunction f φ hφ _ (pointComponent (genericPoint X)),
    hφe, hrX, Subsingleton.elim E.component Z₀]

/-- Coefficients of a pull-back along `g ≫ f` at a prime divisor `E'` at whose generic point `g`
is a local isomorphism are those of the pull-back along `f` at the image `E`. -/
private theorem coeff_isPullback_comp_eq {Y' : Scheme.{u}} [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (g : Y' ⟶ Y) (f : Y ⟶ X)
    [IsDominant g] [IsDominant f] {E' : MMP.Mori.PrimeDivisor Y'} {E : MMP.Mori.PrimeDivisor Y}
    (hE' : g E'.genericPoint = E.genericPoint) [IsIso (g.stalkMap E'.genericPoint)]
    {D D' : QDivisor X} (hDq : D.IsQCartier) (hD : D' = D)
    {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D'.supp} {G : QDivisor Y}
    (hG : D'.IsPullback f hB G) {hB' : ∀ Z, (g ≫ f) (componentGenericPoint Y' Z) ∉ D.supp}
    {G' : QDivisor Y'} (hG' : D.IsPullback (g ≫ f) hB' G') :
    G'.coeff E' = G.coeff E := by
  subst hD
  have hm := QDivisor.cartierIndex_pos hDq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDq
  obtain ⟨U, hU, φ, hφ⟩ := hD₀c (f E.genericPoint)
  refine coeff_eq_of_mul_coeff_eq_ord g hE' hG hm hD₀ hD₀c hφ hU
    (pointComponent (genericPoint X)) ?_
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f]
  refine mul_coeff_eq_ord_of_isPullback hG' hm hD₀ hD₀c hφ E' ?_ _
  rwa [Scheme.Hom.comp_apply, hE']

/-- Coefficients of a pull-back along `g ≫ f = g' ≫ q` at a prime divisor `E'` at whose generic
point `g` is a local isomorphism, computed through the pull-back along `q`, are those of the
pull-back along `f` at the image `E`. -/
private theorem coeff_isPullback_comp_eq_of_isPullback {Y' M : Scheme.{u}} [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] (g : Y' ⟶ Y) (f : Y ⟶ X)
    (g' : Y' ⟶ M) (q : M ⟶ X) [IsDominant g] [IsDominant f] [IsDominant g'] [IsDominant q]
    (hcomm : g ≫ f = g' ≫ q) {E' : MMP.Mori.PrimeDivisor Y'} {E : MMP.Mori.PrimeDivisor Y}
    (hE' : g E'.genericPoint = E.genericPoint) [IsIso (g.stalkMap E'.genericPoint)]
    {D D' : QDivisor X} (hDq : D.IsQCartier) (hD : D' = D)
    {hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D'.supp} {G : QDivisor Y}
    (hG : D'.IsPullback f hB G) {hq : ∀ Z, q (componentGenericPoint M Z) ∉ D.supp}
    {N : QDivisor M} (hN : D.IsPullback q hq N)
    {hB' : ∀ Z, g' (componentGenericPoint Y' Z) ∉ N.supp} {G' : QDivisor Y'}
    (hG' : N.IsPullback g' hB' G') :
    G'.coeff E' = G.coeff E := by
  subst hD
  have hm := QDivisor.cartierIndex_pos hDq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDq
  obtain ⟨U, hU, φ, hφ⟩ := hD₀c (f E.genericPoint)
  obtain ⟨D₀', hD₀', hp⟩ := hN _ hm D₀ hD₀ hD₀c
  have hφq : ∀ Z, q (componentGenericPoint M Z) ∉ (principalDivisor φ).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q _
  refine coeff_eq_of_mul_coeff_eq_ord g hE' hG hm hD₀ hD₀c hφ hU
    (pointComponent (genericPoint X)) ?_
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f,
    MMP.Positivity.DivisorOver.functionFieldMap_congr hcomm,
    ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g' q,
    ← evalFF_pullbackRationalFunction q φ hφq (pointComponent (genericPoint M))
      (pointComponent (genericPoint X))]
  refine mul_coeff_eq_ord_of_isPullback hG' hm hD₀' (isCartier_of_isPullback hD₀c hp)
    (isLocalEquation_pullbackRationalFunction hp hφ hφq) E' ?_ _
  change (g' ≫ q) E'.genericPoint ∈ U
  rwa [← hcomm, Scheme.Hom.comp_apply, hE']

end Pullback

/-! ### Birational transforms along composites -/

/-- Birational transforms along proper birational morphisms of normal varieties compose. -/
private theorem transformDivisor_comp {k : Type u} [Field k] {X Y Y' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsLocallyNoetherian Y'] [IsNormal Y'] (hX : IsNormalVariety k sX)
    (f : Y ⟶ X) (g : Y' ⟶ Y) [IsProper f] [IsProper g] (hY : IsNormalVariety k (f ≫ sX))
    (hY' : IsNormalVariety k (g ≫ f ≫ sX)) (hf : IsBirationalMorphism f)
    (hg : IsBirationalMorphism g) {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Y') :
    RationalMap.transformDivisor (X := Y') (g ≫ f).toRationalMap D =
      RationalMap.transformDivisor (X := Y) f.toRationalMap
        (RationalMap.transformDivisor (X := Y') g.toRationalMap D) := by
  haveI : IsIntegral X := hX.1.toIsIntegral
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsIntegral Y' := hY'.1.toIsIntegral
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  haveI := hf.isDominant
  haveI := hg.isDominant
  have hbij : Function.Bijective (functionFieldMap (g ≫ f)) := by
    have h := hg.functionFieldMap_bijective.comp hf.functionFieldMap_bijective
    convert h using 1
    ext t
    exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f t).symm
  refine Finsupp.ext fun Γ => ?_
  obtain ⟨E, hE, -, htrE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf Γ
  obtain ⟨E', hE', -, htrE'⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hY' hg E
  rw [htrE, htrE']
  have hE'Γ : (g ≫ f) E'.genericPoint = Γ.genericPoint := by
    rw [Scheme.Hom.comp_apply, hE', hE]
  have := Γ.isDiscreteValuationRing_localRing
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (g ≫ f) E' Γ).mpr hE'Γ)
    (fun E'' hE'' => ?_) D
  have hE''Γ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ E'' Γ).mp hE''
  have : ValuationRing (X.presheaf.stalk ((g ≫ f) E''.genericPoint)) := by
    rw [hE''Γ]
    infer_instance
  have : ValuationRing (X.presheaf.stalk ((g ≫ f) E'.genericPoint)) := by
    rw [hE'Γ]
    infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing (g ≫ f) hbij E''.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing (g ≫ f) hbij E'.genericPoint
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap (g ≫ f) hbij (x₁ := E'.genericPoint)
      (x₂ := E''.genericPoint) (hE''Γ.trans hE'Γ.symm)).symm

/-! ### Canonical divisors on a smooth model -/

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) (g : Y ⟶ X) [IsIntegral Y] [IsDominant g]
    (hg : IsBirationalMorphism g) {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX g τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd)
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := (pullbackForms_eq hω m τ).symm.trans h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **The divisor of a nonzero top form on a smooth variety is canonical.** -/
private theorem isCanonicalDivisor_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (hXs : IsSmoothScheme sX) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {n : ℕ} (hn : topologicalKrullDim X = n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n := by
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  obtain ⟨K, hK⟩ := @exists_isCanonicalDivisor_of_isSmoothScheme _ _ _ _ _ k _ _ hX hXs n hn
  exact hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul ⟨hX, inferInstance⟩ hK hτ

/-- **A canonical divisor lifts to a smooth model.** For a proper birational morphism
`f : Y' ⟶ Y` from a smooth variety to a normal variety over a perfect field and a canonical
divisor `K` of `Y`, some canonical divisor `K'` of `Y'` has `f_* K' = K`. -/
private theorem exists_isCanonicalDivisor_transformDivisor_eq {k : Type u} [Field k]
    [PerfectField k] {Y Y' : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (hY : IsNormalVariety k sY)
    (f : Y' ⟶ Y) [IsProper f] (hY' : IsNormalVariety k (f ≫ sY))
    (hs : IsSmoothScheme (f ≫ sY)) (hf : IsBirationalMorphism f) {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) :
    ∃ K' : Divisor Y', K'.IsCanonicalDivisor (f ≫ sY) n ∧
      RationalMap.transformDivisor (X := Y') f.toRationalMap K' = K := by
  obtain ⟨ω, hω0, hω⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus
      hY (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hY) hK
  haveI : LocallyOfFiniteType (f ≫ sY) := hY'.1.toLocallyOfFiniteType
  haveI := hf.isDominant
  haveI : AlgebraicGeometry.IsVariety k sY := hY.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sY) := hY'.1
  have hdim : topologicalKrullDim Y' = n := by
    rw [← hK.topologicalKrullDim_eq]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (f ≫ sY) hf).symm
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
    hK.topologicalKrullDim_eq
  refine ⟨divisorOfForm (pullbackRationalPluriForms sY f ω),
    isCanonicalDivisor_divisorOfForm hY'.1 hs hdim
      (pullbackRationalPluriForms_ne_zero sY hK.topologicalKrullDim_eq f hf hω0), ?_⟩
  refine Finsupp.ext fun Γ => ?_
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hY' hf Γ
  rw [htr]
  change E.ordForm (pullbackRationalPluriForms sY f ω) = K.coeff Γ
  rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hf.functionFieldMap_bijective hd
    E Γ heq ω, hω Γ]

/-! ### Exceptional divisors -/

/-- In `WithBot ℕ∞`, `d + c = n` gives `d + 2 ≤ n ↔ 2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    have h' : d + c = n := by exact_mod_cast h
    have hd : d ≠ ⊤ := by
      rintro rfl
      simp at h'
    rw [show ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← h',
      ← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe]
    exact ENat.add_le_add_iff_left hd

/-- A divisor over a variety of dimension `n` is exceptional iff the generic point of its centre
has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : MMP.Flips.ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- **Exceptional over `M` is exceptional over `V`.** If `P'` on `W'` is exceptional over `M`
for `g₂`, `g₁(η_{P'}) = η_P` and `g₁ ≫ b = g₂ ≫ q` with `q : M ⟶ V` proper birational onto a
normal variety, then `P` is exceptional over `V` for `b`. -/
private theorem isExceptionalPrimeDivisor_of_comp {k : Type u} [Field k] {W W' M V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V]
    [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] (hV : IsNormalVariety k sV) (q : M ⟶ V) [IsProper q]
    (hM : IsNormalVariety k (q ≫ sV)) (hq : IsBirationalMorphism q) (b : W ⟶ V) [IsProper b]
    (hW : IsNormalVariety k (b ≫ sV)) (hb : IsBirationalMorphism b) (g₁ : W' ⟶ W)
    (g₂ : W' ⟶ M) (hcomm : g₁ ≫ b = g₂ ≫ q) (P' : MMP.Mori.PrimeDivisor W')
    (P : MMP.Mori.PrimeDivisor W) (hP : g₁ P'.genericPoint = P.genericPoint) {n : ℕ}
    (hnM : topologicalKrullDim M = n)
    (hex : MMP.Flips.IsExceptionalPrimeDivisor (q ≫ sV) g₂ P') :
    MMP.Flips.IsExceptionalPrimeDivisor sV b P := by
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sV) := hM.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k sV := hV.1
  haveI : AlgebraicGeometry.IsVariety k (q ≫ sV) := hM.1
  have hnV : topologicalKrullDim V = n := by
    rw [← hnM]
    exact MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (q ≫ sV) hq
  obtain ⟨hY, hf, hp, hE⟩ := hex
  have hE' : 2 ≤ Order.coheight (g₂ P'.genericPoint) :=
    (isExceptional_iff_two_le_coheight (sX := q ≫ sV) hnM
      (MMP.Flips.ProperDivisorOver.mk ⟨W', g₂, hY, hf, P'⟩ hp)).mp hE
  have hbP : b P.genericPoint = q (g₂ P'.genericPoint) := by
    rw [← hP, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have h2 : 2 ≤ Order.coheight (b P.genericPoint) := by
    rw [hbP]
    by_cases hx : q (g₂ P'.genericPoint) ∈ biregularLocus q
    · rwa [MMP.Positivity.coheight_map_of_mem_biregularLocus q hx]
    · exact MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
        (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sV q (hY := hV.1) (hX := hM.1)
          hq) _ hx
  exact ⟨hW, hb, inferInstance, (isExceptional_iff_two_le_coheight (sX := sV) hnV
    (MMP.Flips.ProperDivisorOver.mk ⟨W, b, hW, hb, P⟩ inferInstance)).mpr h2⟩

/-! ### The comparison -/

/-- `K + B` as an `ℝ`-divisor is the log canonical divisor of `K` and `B`. -/
private theorem logCanonicalDivisor_toRDivisor {T : Scheme.{u}} (KT : Divisor T)
    (BT : QDivisor T) :
    MMP.Flips.logCanonicalDivisor KT (QDivisor.toRDivisor BT) =
      QDivisor.toRDivisor (Divisor.toQDivisor KT + BT) := by
  rw [MMP.Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- Two proper birational morphisms onto a normal variety over a field of characteristic zero are
dominated by a common smooth model, projective and birational over both. -/
private theorem exists_isSmoothScheme_comp_eq {k : Type u} [Field k] [CharZero k]
    {V W M : Scheme.{u}} (sV : V ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sV] [IsNormal V]
    (q : M ⟶ V) (b : W ⟶ V) [IsProper q] [IsProper b] (hq : IsBirationalMorphism q)
    (hb : IsBirationalMorphism b) (hM : IsNormalVariety k (q ≫ sV))
    (hW : IsNormalVariety k (b ≫ sV)) :
    ∃ (W' : Scheme.{u}) (w : W' ⟶ V) (g₁ : W' ⟶ W) (g₂ : W' ⟶ M),
      IsNormalVariety k (w ≫ sV) ∧ IsSmoothScheme (w ≫ sV) ∧ IsProjectiveMorphism w ∧
      g₁ ≫ b = w ∧ IsProjectiveMorphism g₁ ∧ IsBirationalMorphism g₁ ∧
      g₂ ≫ q = w ∧ IsProjectiveMorphism g₂ ∧ IsBirationalMorphism g₂ := by
  let Xf : Bool → Scheme.{u} := fun i => Bool.rec M W i
  let ff : ∀ i, Xf i ⟶ V := fun i => Bool.rec (motive := fun i => Xf i ⟶ V) q b i
  obtain ⟨W', w, hW'n, -, g, hW's, hwp, hg, -, -⟩ :=
    @MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq k _ _ V
      sV _ _ Bool _ Xf ff (fun i => by cases i <;> assumption)
      (fun i => by cases i; exacts [hq, hb]) (fun i => by cases i; exacts [hM, hW])
      Empty _ Empty.elim (fun j => j.elim)
  obtain ⟨h₁, h₁p, h₁b⟩ := hg true
  obtain ⟨h₂, h₂p, h₂b⟩ := hg false
  exact ⟨W', w, g true, g false, hW'n, hW's, hwp, h₁, h₁p, h₁b, h₂, h₂p, h₂b⟩

/-- If the coefficients of `G_X - G_V` on `W` are those of `G - G'` on `W'` along strict
transforms, and `G - G' ≥ 0` with support where `E` holds, then `G_X - G_V ≥ 0` and every prime
divisor in its support has a strict transform where `E` holds. -/
private theorem nonneg_sub_and_forall_of_coeff_eq {W W' : Scheme.{u}} (g : W' ⟶ W)
    {GX GV : QDivisor W} {G G' : QDivisor W'} {E : MMP.Mori.PrimeDivisor W' → Prop}
    (key : ∀ P : MMP.Mori.PrimeDivisor W, ∃ P' : MMP.Mori.PrimeDivisor W',
      g P'.genericPoint = P.genericPoint ∧ (GX - GV).coeff P = (G - G').coeff P')
    (hnn : 0 ≤ QDivisor.toRDivisor G - QDivisor.toRDivisor G')
    (hE : ∀ P', (QDivisor.toRDivisor G - QDivisor.toRDivisor G').coeff P' ≠ 0 → E P') :
    0 ≤ GX - GV ∧ ∀ P, (GX - GV).coeff P ≠ 0 →
      ∃ P' : MMP.Mori.PrimeDivisor W', g P'.genericPoint = P.genericPoint ∧ E P' := by
  refine ⟨fun P => ?_, fun P hP => ?_⟩
  · obtain ⟨P', -, hc⟩ := key P
    have h0 : (0 : ℝ) ≤ (QDivisor.toRDivisor G - QDivisor.toRDivisor G').coeff P' := hnn P'
    rw [DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor] at h0
    change (0 : ℚ) ≤ (GX - GV).coeff P
    rw [hc, DivisorWithCoeffs.coeff_sub]
    exact_mod_cast h0
  · obtain ⟨P', hP', hc⟩ := key P
    refine ⟨P', hP', hE P' ?_⟩
    rw [hc, DivisorWithCoeffs.coeff_sub] at hP
    rw [DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
    exact_mod_cast hP

end Proof_lem_oai4_c3_ample_model_comparison

namespace MMP.Fourfold

open Proof_lem_oai4_c3_ample_model_comparison

open MMP.Mori

variable {X Z M V W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
  [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- **Discrepancy comparison with the ample model.** Let `(M, B_M, q, V, B_V)` be an ample-model
datum of a birational contraction `f : X ⟶ Z` of a projective lc fourfold pair `(X, B)` with
canonical divisor `K_X`, and let `a : W ⟶ X`, `b : W ⟶ V` be birational morphisms over `ℂ` from
a smooth projective variety `W`, compatible with the birational map `q ∘ φ : X ⤏ V`. Let `K_V`
be a canonical divisor of `V` such that `K_X = a_* K_W` and `K_V = b_* K_W` for a canonical
divisor `K_W` of `W`. If `G_X = a^*(K_X + B)` and `G_V = b^*(K_V + B_V)`, then `G_X - G_V` is
effective and every prime divisor of `W` in its support is exceptional over `V`. -/
@[mmp "lem_oai4_c3_ample_model_comparison"]
public theorem IsAmpleModelDatum.nonneg_sub_and_isExceptionalPrimeDivisor
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV)
    {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWs : MMP.Mori.IsSmoothScheme sW)
    {a : W ⟶ X} {b : W ⟶ V} (ha : a ≫ sX = sW) (hb : b ≫ p ≫ sZ = sW)
    (hab : IsBirationalMorphism a) (hbb : IsBirationalMorphism b)
    {ψ : X.RationalMap W} (hψ : MMP.Mori.RationalMap.IsInverse a.toRationalMap ψ)
    (hφ : ψ.compHom b = φ.compHom q) {KV : Divisor V}
    (hKW : ∃ (n : ℕ) (KW : Divisor W), KW.IsCanonicalDivisor sW n ∧
      MMP.Mori.RationalMap.transformDivisor a.toRationalMap KW = K ∧
      MMP.Mori.RationalMap.transformDivisor b.toRationalMap KW = KV)
    {GX GV : QDivisor W}
    (hGX : ∃ hB : ∀ T : irreducibleComponents W,
        a (componentGenericPoint W T) ∉ (Divisor.toQDivisor K + B).supp,
      (Divisor.toQDivisor K + B).IsPullback a hB GX)
    (hGV : ∃ hB : ∀ T : irreducibleComponents W,
        b (componentGenericPoint W T) ∉ (Divisor.toQDivisor KV + BV).supp,
      (Divisor.toQDivisor KV + BV).IsPullback b hB GV) :
    0 ≤ GX - GV ∧
      ∀ P, (GX - GV).coeff P ≠ 0 → MMP.Flips.IsExceptionalPrimeDivisor (p ≫ sZ) b P := by
  obtain ⟨hqp, hVi, hVn, hMn, hqP, hqb⟩ := h.isProper_and_isBirationalMorphism
  have hlm := h.isGoodLogMinimalModel.toIsLogMinimalModel
  have hsM : q ≫ p ≫ sZ = sM := by
    rw [← Category.assoc, hqp]
    exact hlm.comp_eq_model
  haveI : IsNormal Z := h.isContraction.isNormalVariety_target.2
  have hXn : IsNormalVariety ℂ sX := hlm.isNormalVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXn.1
  have hMn' : IsNormalVariety ℂ sM := hsM ▸ hMn
  haveI : LocallyOfFiniteType sM := hMn'.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ sW := hW.toIsVariety
  have hWn : IsNormalVariety ℂ sW := ⟨inferInstance, inferInstance⟩
  haveI : IsProper sW := isProper_of_isProjectiveMorphism sW hW.isProjective
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sZ) := hVn.1
  haveI : IsProper b := by
    haveI : IsProper (b ≫ p ≫ sZ) := by
      rw [hb]
      infer_instance
    exact IsProper.of_comp b (p ≫ sZ)
  haveI : IsProper a := by
    haveI : IsProper (a ≫ sX) := by
      rw [ha]
      infer_instance
    exact IsProper.of_comp a sX
  haveI := hab.isDominant
  haveI := hbb.isDominant
  haveI := hqb.isDominant
  have hbW : IsNormalVariety ℂ (b ≫ p ≫ sZ) := by rwa [hb]
  obtain ⟨W', w, g₁, g₂, hW'n, hW's, hwp, hg₁, hg₁p, hg₁b, hg₂, hg₂p, hg₂b⟩ :=
    exists_isSmoothScheme_comp_eq (p ≫ sZ) q b hqb hbb hMn hbW
  haveI : IsIntegral W' := hW'n.1.toIsIntegral
  haveI : IsNormal W' := hW'n.2
  haveI : LocallyOfFiniteType (w ≫ p ≫ sZ) := hW'n.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (w ≫ p ≫ sZ)
  haveI : IsProper w := isProper_of_isProjectiveMorphism w hwp
  haveI : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace w
  haveI : IsProper g₁ := isProper_of_isProjectiveMorphism _ hg₁p
  haveI : IsProper g₂ := isProper_of_isProjectiveMorphism _ hg₂p
  haveI := hg₁b.isDominant
  haveI := hg₂b.isDominant
  have hcomm : g₁ ≫ b = g₂ ≫ q := hg₁.trans hg₂.symm
  have hsW'₂ : g₂ ≫ sM = w ≫ p ≫ sZ := by rw [← hsM, ← Category.assoc, hg₂]
  have hsW'₁ : g₁ ≫ sW = w ≫ p ≫ sZ := by rw [← hb, ← Category.assoc, hg₁]
  have hW'nM : IsNormalVariety ℂ (g₂ ≫ sM) := by rwa [hsW'₂]
  have hW'sM : IsSmoothScheme (g₂ ≫ sM) := by rwa [hsW'₂]
  have hW'nW : IsNormalVariety ℂ (g₁ ≫ sW) := by rwa [hsW'₁]
  have hW'sW : IsSmoothScheme (g₁ ≫ sW) := by rwa [hsW'₁]
  set F : W' ⟶ X := g₁ ≫ a with hFdef
  have hFb : IsBirationalMorphism F := isBirationalMorphism_comp hg₁b hab
  haveI : IsDominant F := hFb.isDominant
  haveI : IsProper F := by
    rw [hFdef]
    infer_instance
  obtain ⟨ψ', hψ'⟩ := RationalMap.IsBirational.exists_isInverse hFb
  have hO := genericPoint_mem_biregularLocus (p ≫ sZ) q hVn.1 hMn.1 hqb
  haveI : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
  have hφ' : ψ'.compHom g₂ = φ := compHom_eq_of_isInverse a b g₁ g₂ q (biregularLocus q) hO
    hcomm hψ hφ hψ' hFb.functionFieldMap_bijective
  obtain ⟨n, hKMc⟩ := hlm.isCanonicalDivisor
  obtain ⟨KW', hKW'c, hKW'M⟩ :=
    exists_isCanonicalDivisor_transformDivisor_eq hMn' g₂ hW'nM hW'sM hg₂b hKMc
  obtain ⟨nW, KW, hKWc, hKa, hKb⟩ := hKW
  obtain ⟨KW₁, hKW₁c, hKW₁W⟩ :=
    exists_isCanonicalDivisor_transformDivisor_eq hWn g₁ hW'nW hW'sW hg₁b hKWc
  have hKW₁c' : KW₁.IsCanonicalDivisor (g₂ ≫ sM) nW := by rwa [hsW'₂, ← hsW'₁]
  obtain ⟨c, hc⟩ :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (g₂ ≫ sM) hW'nM hKW'c hKW₁c'
  obtain ⟨ρ, hρ, hρc⟩ :=
    exists_principalDivisor_pullbackRationalFunction_eq g₁ hg₁b.functionFieldMap_bijective c
  have hg₁KW' : RationalMap.transformDivisor (X := W') g₁.toRationalMap KW' =
      KW + principalDivisor ρ := by
    have : KW' = KW₁ + principalDivisor (pullbackRationalFunction g₁ ρ hρ) := by
      rw [hρc, ← hc]
      abel
    rw [this, map_add, hKW₁W,
      MMP.Positivity.transformDivisor_principalDivisor_pullback hWn hW'nW hg₁b ρ hρ]
  have haW : IsNormalVariety ℂ (a ≫ sX) := by rwa [ha]
  obtain ⟨ρX, hρX, hρXe⟩ :=
    exists_principalDivisor_pullbackRationalFunction_eq a hab.functionFieldMap_bijective ρ
  obtain ⟨ρV, hρV, hρVe⟩ :=
    exists_principalDivisor_pullbackRationalFunction_eq b hbb.functionFieldMap_bijective ρ
  set K₂ : Divisor X := K + principalDivisor ρX with hK₂def
  set KV₂ : Divisor V := KV + principalDivisor ρV with hKV₂def
  have hK₂ : RationalMap.transformDivisor (X := W') F.toRationalMap KW' = K₂ := by
    rw [hFdef, transformDivisor_comp hXn a g₁ haW (by rwa [ha]) hab hg₁b, hg₁KW',
      map_add, hKa, ← hρXe,
      MMP.Positivity.transformDivisor_principalDivisor_pullback hXn haW hab ρX hρX]
  have hKV₂ : RationalMap.transformDivisor (X := M) q.toRationalMap KM = KV₂ := by
    rw [← hKW'M, ← transformDivisor_comp hVn q g₂ hMn (by rwa [← Category.assoc, hg₂])
      hqb hg₂b, ← hcomm, transformDivisor_comp hVn b g₁ hbW
      (by rwa [← Category.assoc, hg₁]) hbb hg₁b, hg₁KW', map_add, hKb, ← hρVe,
      MMP.Positivity.transformDivisor_principalDivisor_pullback hVn hbW hbb ρV hρV]
  obtain ⟨hDV₂q, hqB, hqpull⟩ := h.isPullback_logCanonicalDivisor hKV₂
  have hDq : (Divisor.toQDivisor K + B).IsQCartier := by
    obtain ⟨-, n₀, K₀, hK₀, hQ⟩ := hlm.isLogCanonicalPair.1
    obtain ⟨nK, hKc⟩ := h.isCanonicalDivisor
    exact hQ.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXn hK₀ hKc)
  have hD₂q : (Divisor.toQDivisor K₂ + B).IsQCartier :=
    hDq.add_of_linearlyEquivalent ⟨ρX⁻¹, by
      rw [hK₂def, MMP.Mori.principalDivisor_inv]; abel⟩
  have hDVq : (Divisor.toQDivisor KV + BV).IsQCartier :=
    hDV₂q.add_of_linearlyEquivalent ⟨ρV, by rw [hKV₂def]; abel⟩
  obtain ⟨hBa, hGXa⟩ := hGX
  obtain ⟨hBb, hGVb⟩ := hGV
  obtain ⟨hBa₂, hGX₂⟩ := isPullback_add_principalDivisor hDq hGXa ρX hρX
  obtain ⟨hBb₂, hGV₂⟩ := isPullback_add_principalDivisor hDVq hGVb ρV hρV
  rw [hρXe] at hGX₂
  rw [hρVe] at hGV₂
  have hD₂ : Divisor.toQDivisor K + B + Divisor.toQDivisor (principalDivisor ρX) =
      Divisor.toQDivisor K₂ + B := by rw [hK₂def, map_add]; abel
  have hDV₂ : Divisor.toQDivisor KV + BV + Divisor.toQDivisor (principalDivisor ρV) =
      Divisor.toQDivisor KV₂ + BV := by rw [hKV₂def, map_add]; abel
  set D₂ := Divisor.toQDivisor K₂ + B
  set N := Divisor.toQDivisor KM + BM
  have hNq : N.IsQCartier := isQCartier_of_isPullback hDV₂q hqpull
  have hBF : ∀ Z, F (componentGenericPoint W' Z) ∉ D₂.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' F D₂
  have hBg₂ : ∀ Z, g₂ (componentGenericPoint W' Z) ∉ N.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g₂ N
  set GXF := D₂.pullback hD₂q hBF
  set GMQ := N.pullback hNq hBg₂
  have hGXF : D₂.IsPullback F hBF GXF := QDivisor.isPullback_pullback hD₂q hBF
  have hGMQ : N.IsPullback g₂ hBg₂ GMQ := QDivisor.isPullback_pullback hNq hBg₂
  have hpX : F ≫ sX = g₂ ≫ sM := by rw [hFdef, Category.assoc, ha, hsW'₁, hsW'₂]
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  have hFp : IsProjectiveMorphism F :=
    hg₁p.comp (IsProjectiveMorphism.of_comp a sX (by rw [ha]; exact hW.isProjective))
  obtain ⟨hnn, hexc⟩ := IsLogMinimalModel.nonneg_sub_and_isExceptionalPrimeDivisor
    h.isProjectiveVariety h.isProjectiveVariety_target hlm (sW := g₂ ≫ sM) hW'nM.1 hW'sM
    hpX rfl hFp hg₂p hFb hg₂b hψ' hφ' ⟨n, KW', hKW'c, hK₂, hKW'M⟩
    (GX := QDivisor.toRDivisor GXF) (GM := QDivisor.toRDivisor GMQ)
    (by rw [logCanonicalDivisor_toRDivisor]; exact isRCartierPullback_of_isPullback hD₂q hGXF)
    (by rw [logCanonicalDivisor_toRDivisor]; exact isRCartierPullback_of_isPullback hNq hGMQ)
  have key : ∀ P : MMP.Mori.PrimeDivisor W, ∃ P' : MMP.Mori.PrimeDivisor W',
      g₁ P'.genericPoint = P.genericPoint ∧ (GX - GV).coeff P = (GXF - GMQ).coeff P' := by
    intro P
    obtain ⟨P', hP', hiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hWn hW'nW hg₁b P
    refine ⟨P', hP', ?_⟩
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub,
      coeff_isPullback_comp_eq g₁ a hP' hD₂q hD₂ hGX₂ hGXF,
      coeff_isPullback_comp_eq_of_isPullback g₁ b g₂ q hcomm hP' hDV₂q hDV₂ hGV₂ hqpull hGMQ,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add]
    ring
  obtain ⟨hnn', hexc'⟩ := nonneg_sub_and_forall_of_coeff_eq g₁ key hnn hexc
  refine ⟨hnn', fun P hP => ?_⟩
  obtain ⟨P', hP', hex⟩ := hexc' P hP
  rw [← hsM] at hex
  exact isExceptionalPrimeDivisor_of_comp hVn q hMn hqb b hbW hbb g₁ g₂ hcomm P' P hP'
    hKMc.topologicalKrullDim_eq hex

end MMP.Fourfold

end
