module

public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
public import MMP.Algebra.Category.ModuleCat.Ext.GenericBaseChange

/-!
# A small birational model is crepant

Let `g : Y' ⟶ Y` be a small proper birational morphism of normal varieties over a field `k`
(`MMP.Fourfold.IsSmallMorphism`: `Ex(g)` has codimension at least two in `Y'`), and let `K` be a
canonical divisor of `Y` which is `ℚ`-Cartier. Then the pull-back `g^*K` is a canonical divisor
of `Y'`: there is a canonical divisor `K'` of `Y'` with `K' = g^*K` as `ℚ`-divisors. In
particular `g^*K` is integral.

Indeed `g` is an isomorphism `g⁻¹(V) ≅ V` over an open `V ⊆ Y` whose preimage has complement of
codimension at least two in `Y'`; there `K'` and `g^*K` agree, and two `ℚ`-divisors on a normal
variety which agree off a closed subset of codimension at least two are equal.

## Main results

* `MMP.Fourfold.IsSmallMorphism.exists_isCanonicalDivisor_eq_pullback`: `K_{Y'} = g^*K_Y`.

## Implementation notes

Canonical divisors (`MMP.Mori.Divisor.IsCanonicalDivisor`) are only determined up to linear
equivalence; the equality `K_{Y'} = g^*K_Y` of the source, for compatible choices of canonical
divisors, is the statement that `g^*K` is itself a canonical divisor of `Y'`. The pull-back is
`MMP.Mori.QDivisor.pullback` of the `ℚ`-Cartier `ℚ`-divisor `K`. Projectivity of `g` is not
needed: properness, which is part of `MMP.Fourfold.IsSmallMorphism`, suffices.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.22, 2.25
-/

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open Opposite MMP MMP.Mori MMP.Positivity

section Coeff

variable {Y' Y : Scheme.{u}} [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

private theorem ordUnit_eq_ord (E : MMP.Mori.PrimeDivisor Y')
    (u : (Y'.presheaf.stalk (componentGenericPoint Y' E.component))ˣ) :
    E.ordUnit u = Y'.ord ((componentToFunctionField E.component).hom u)
      E.genericPoint := by
  have hsub : Subsingleton (irreducibleComponents Y') := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let ψ : (RationalFunctions Y')ˣ := (RationalFunctions.unitsEquiv Y').symm
    fun Z => (Subsingleton.elim E.component Z) ▸ u
  have h1 : Units.map (RationalFunctions.component Y' E.component).toMonoidHom ψ = u :=
    congrFun ((RationalFunctions.unitsEquiv Y').apply_symm_apply
      (fun Z => (Subsingleton.elim E.component Z) ▸ u)) E.component
  rw [← h1, ← PrimeDivisor.ord_eq_ordUnit, ord_eq_ord_componentToFunctionField]
  rfl

private theorem key_stalk (g : Y' ⟶ Y) [IsDominant g] (Z : irreducibleComponents Y')
    (W : irreducibleComponents Y)
    (hW : g (componentGenericPoint Y' Z) ∈ W.1)
    (a : Y.presheaf.stalk (g (componentGenericPoint Y' Z))) :
    (componentToFunctionField Z).hom ((g.stalkMap (componentGenericPoint Y' Z)).hom a) =
      functionFieldMap g ((componentToFunctionField W).hom
        ((stalkToRationalFunctions Y hW).hom a)) := by
  unfold functionFieldMap
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [show (componentToFunctionField Z) = Y'.presheaf.stalkSpecializes _ from rfl,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  congr 1
  simp only [TopCat.Presheaf.stalkCongr_hom, stalkToRationalFunctions]
  change _ = (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom
    ((Y.presheaf.stalkSpecializes _).hom a))
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]
  erw [TopCat.Presheaf.stalkSpecializes_comp_apply]

private theorem coeff_eq_of_isPullback {g : Y' ⟶ Y} [IsDominant g] {B : Divisor Y}
    (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', g (componentGenericPoint Y' Z) ∉ B.supp}
    {B' : Divisor Y'} (h : B.IsPullback g hB B') (E : MMP.Mori.PrimeDivisor Y')
    (P : MMP.Mori.PrimeDivisor Y) (heq : g E.genericPoint = P.genericPoint)
    [IsIso (g.stalkMap E.genericPoint)] : B'.coeff E = B.coeff P := by
  obtain ⟨U, hyU, φ, hφ⟩ := hBc P.genericPoint
  have hPU : (P.support ∩ (U : Set Y)).Nonempty :=
    ⟨P.genericPoint, PrimeDivisor.genericPoint_mem_support' P, hyU⟩
  have hE : (E.support ∩ ((g ⁻¹ᵁ U : Y'.Opens) : Set Y')).Nonempty :=
    ⟨E.genericPoint, PrimeDivisor.genericPoint_mem_support' E, by
      change g E.genericPoint ∈ U
      rwa [heq]⟩
  rw [h U φ hφ E hE, hφ P hPU]
  have hZ := E.map_componentGenericPoint_mem g hE
  have hW := mem_pointComponent (g (componentGenericPoint Y' E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZ (hB _) hW
  rw [pullbackComponent_eq hB hφ hZ hW a ha, ordUnit_eq_ord,
    ord_eq_ord_componentToFunctionField]
  have hsub : Subsingleton (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hPW : P.component = pointComponent (g (componentGenericPoint Y' E.component)) :=
    Subsingleton.elim _ _
  rw [hPW, ← ha]
  change Scheme.ord ((componentToFunctionField E.component).hom
    ((g.stalkMap (componentGenericPoint Y' E.component)).hom ↑a)) E.genericPoint = _
  rw [key_stalk g E.component _ hW]
  exact ord_functionFieldMap_of_isIso g E P heq _

private theorem coeff_pullback_eq [CompactSpace Y'] {g : Y' ⟶ Y} [IsDominant g] {K : Divisor Y}
    (hKq : (Divisor.toQDivisor K).IsQCartier)
    (hB : ∀ Z : irreducibleComponents Y',
      g (componentGenericPoint Y' Z) ∉ (Divisor.toQDivisor K).supp)
    (E : MMP.Mori.PrimeDivisor Y') (P : MMP.Mori.PrimeDivisor Y)
    (heq : g E.genericPoint = P.genericPoint) [IsIso (g.stalkMap E.genericPoint)] :
    (QDivisor.pullback (f := g) (Divisor.toQDivisor K) hKq hB).coeff E = (K.coeff P : ℚ) := by
  set m₀ := (Divisor.toQDivisor K).cartierIndex hKq
  have hm₀ : 0 < m₀ := QDivisor.cartierIndex_pos hKq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hKq
  obtain ⟨D', hD', hp⟩ := QDivisor.isPullback_pullback hKq hB m₀ hm₀ D₀ hD₀ hD₀c
  have h2 := congrArg (fun G : QDivisor Y' => G.coeff E) hD'
  have h3 := congrArg (fun G : QDivisor Y => G.coeff P) hD₀
  simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Divisor.coeff_toQDivisor] at h2 h3
  refine mul_left_cancel₀ (show ((m₀ : ℤ) : ℚ) ≠ 0 by exact_mod_cast hm₀.ne') ?_
  rw [← h2, coeff_eq_of_isPullback hD₀c hp E P heq, h3]

end Coeff

section Biregular

variable {Y' Y : Scheme.{u}}

/-- An open immersion from a nonempty scheme into an irreducible one is dominant. -/
private theorem isDominant_of_isOpenImmersion' {A Z : Scheme.{u}} (f : A ⟶ Z)
    [IsOpenImmersion f] [Nonempty A] [IrreducibleSpace Z] : IsDominant f :=
  ⟨IsOpen.dense f.isOpenEmbedding.isOpen_range (Set.range_nonempty _)⟩

private theorem isOpenImmersion_ι_comp (g : Y' ⟶ Y) :
    IsOpenImmersion ((g ⁻¹ᵁ biregularLocus g).ι ≫ g) := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  rw [← morphismRestrict_ι g (biregularLocus g)]
  infer_instance

private theorem isIso_stalkMap_of_mem (g : Y' ⟶ Y) {x : Y'} (hx : g x ∈ biregularLocus g) :
    IsIso (g.stalkMap x) := by
  have := isOpenImmersion_ι_comp g
  let x' : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨x, hx⟩
  have h := IsOpenImmersion.instIsIsoCommRingCatStalkMap ((g ⁻¹ᵁ biregularLocus g).ι ≫ g) x'
  rw [Scheme.Hom.stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap _) _
    (IsOpenImmersion.instIsIsoCommRingCatStalkMap (g ⁻¹ᵁ biregularLocus g).ι x') h

private theorem map_genericPoint_mem_biregularLocus {k : Type u} [Field k] {sY' : Y' ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {g : Y' ⟶ Y} (hg : IsSmallMorphism sY' sY g)
    (E : MMP.Mori.PrimeDivisor Y') : g E.genericPoint ∈ biregularLocus g := by
  have h := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hg.two_le_codimension
  by_contra hx
  have := h E.genericPoint hx
  rw [E.coheight_genericPoint] at this
  exact absurd this (by decide)

private theorem coheight_map_eq (g : Y' ⟶ Y) {x : Y'} (hx : g x ∈ biregularLocus g) :
    Order.coheight (g x) = Order.coheight x := by
  have := isOpenImmersion_ι_comp g
  let x' : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨x, hx⟩
  exact (coheight_eq_of_isOpenImmersion (x := x') ((g ⁻¹ᵁ biregularLocus g).ι ≫ g)).trans
    (coheight_eq_of_isOpenImmersion (x := x') (g ⁻¹ᵁ biregularLocus g).ι).symm

private theorem exists_primeDivisor_map (g : Y' ⟶ Y) {x : Y'} (hx : g x ∈ biregularLocus g)
    (hc : Order.coheight x = 1) : ∃ P : MMP.Mori.PrimeDivisor Y, g x = P.genericPoint :=
  ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne (g x) ((coheight_map_eq g hx).trans hc),
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩

private theorem genericPoint_map_mem_biregularLocus {k : Type u} [Field k]
    {sY' : Y' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {g : Y' ⟶ Y}
    (hg : IsSmallMorphism sY' sY g) [IrreducibleSpace Y'] :
    g (genericPoint Y') ∈ biregularLocus g := by
  have h := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hg.two_le_codimension
  by_contra hx
  have := h (genericPoint Y') hx
  have h0 : Order.coheight (genericPoint Y') = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => genericPoint_specializes b
  rw [h0] at this
  exact absurd this (by decide)

end Biregular

section Restrict

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : Mori.PrimeDivisor V) :
    Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- The restriction `D|_A` of a divisor along an open immersion `j : A ⟶ X`. -/
private noncomputable def restrictAlong {A : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (D : Divisor X) : Divisor A :=
  Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) D
    (OpenWeilRestriction.primeDivisorMap_injective j).injOn

private theorem coeff_restrictAlong {A : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (D : Divisor X) (W : Mori.PrimeDivisor A) :
    (restrictAlong j D).coeff W = D.coeff (OpenWeilRestriction.primeDivisorMap j W) := rfl

private theorem functionFieldMap_bijective_j {A : Scheme.{u}} [IsIntegral A] (j : A ⟶ X)
    [IsOpenImmersion j] [IsDominant j] [Nonempty A] : Function.Bijective (functionFieldMap j) :=
  functionFieldMap_bijective_of_isOpenImmersion j ⊤ ⟨Classical.arbitrary A, trivial⟩

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable {A : Scheme.{u}} [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A] (j : A ⟶ X)
  [IsOpenImmersion j] [IsDominant j] [Nonempty A]

private theorem genericPoint_mem_of_index {V : A.Opens}
    (Z : {Z : irreducibleComponents A // componentGenericPoint A Z ∈ V}) :
    genericPoint A ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : A.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ j ''ᵁ V}) :
    genericPoint A ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint A ⤳ x := (genericPoint_spec A).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The irreducible component `X` of the integral scheme `X`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : A.Opens} (h : genericPoint A ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ j ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant j]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : A.Opens} (h : genericPoint A ∈ V) :
    {Z : irreducibleComponents A // componentGenericPoint A Z ∈ V} :=
  ⟨topComponent A, by rw [componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : A.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf A).obj (op V)) :=
  fun Z => (A.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap j (evFF ψ (indexX j (genericPoint_mem_of_index Z))))

private theorem evFF_restrictRF (V : A.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V))))
    (Z : {Z : irreducibleComponents A // componentGenericPoint A Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ j ''ᵁ V}) :
    evFF (restrictRF j V ψ) Z = functionFieldMap j (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : A.Opens) :
    Function.Injective (restrictRF j V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX j Z'
  have h1 := congrArg (fun φ => evFF φ (indexU hV)) h
  simp only [evFF_restrictRF j V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap j).injective h1)

private theorem restrictRF_surjective (V : A.Opens) :
    Function.Surjective (restrictRF j V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap j) (functionFieldMap_bijective_j j)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU (genericPoint_mem_of_indexX j Z')))), ?_⟩
  funext Z
  change (A.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap j ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (A.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : A.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    Divisor.IsDivisorialSection (restrictAlong j D) V (restrictRF j V ψ) ↔
      D.IsDivisorialSection (j ''ᵁ V) ψ := by
  have key : ∀ (E' : Mori.PrimeDivisor A) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap j E').support ∩ j ''ᵁ V).Nonempty),
      E'.OrdGE (-(restrictAlong j D).coeff E')
          (restrictRF j V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap j E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap j E'))
          (ψ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap j E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF j V ψ _ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap j E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap j).injective,
      coeff_restrictAlong]
    rfl
  have hmem : ∀ E' : Mori.PrimeDivisor A, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap j E').support ∩ j ''ᵁ V).Nonempty := by
    intro E'
    rw [← Mori.PrimeDivisor.genericPoint_mem_iff, ← Mori.PrimeDivisor.genericPoint_mem_iff,
      show Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap j E') =
        j E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [j.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range j.base := by
      obtain ⟨x, -, hx⟩ := (Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      exact ⟨x, hx⟩
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : A.Opens) (r : Γ(A, V))
    (h₁ : genericPoint X ∈ j ''ᵁ V) (h₂ : genericPoint A ∈ V) :
    functionFieldMap j (X.presheaf.germ (j ''ᵁ V) (genericPoint X) h₁
      ((j.appIso V).inv r)) = A.presheaf.germ V (genericPoint A) h₂ r := by
  have h₃ : j (genericPoint A) ∈ j ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (j.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : A.Opens) (r : Γ(A, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    restrictRF j V ((j.appIso V).inv r • ψ) = r • restrictRF j V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv j V r _
    (genericPoint_mem_of_index Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : A.Opens) : restrictRF j V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : A.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    restrictRF j V (ψ₁ + ψ₂) = restrictRF j V ψ₁ + restrictRF j V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict j ⟶ Divisor.divisorialSheaf (restrictAlong j D) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF j V.unop (ψ : D.divisorialSubmodule (j ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff j D V.unop _).2
              (ψ : D.divisorialSubmodule (j ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (restrictAlong j D) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero j V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add j V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul j V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom j D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (j ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF j V ψ₁.1 = restrictRF j V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective j V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective j V (φ : Divisor.divisorialSubmodule (restrictAlong j D) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff j D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (restrictAlong j D) V).2)⟩ :
        D.divisorialSubmodule (j ''ᵁ V)), Subtype.ext hψ⟩

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictAlong_iso (D : Divisor X) :
    Nonempty (Divisor.divisorialSheaf (restrictAlong j D) ≅ D.divisorialSheaf.restrict j) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom j D)).symm⟩

end DivisorialRestrict

end Restrict

section Extend

variable {Z A : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
  [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A] (h : A ⟶ Z) [IsOpenImmersion h]
  [IsDominant h] [Nonempty A] [CompactSpace A] [CompactSpace Z]

/-- Linear equivalence descends across codimension two: if every prime divisor of `Z` has its
generic point in the image of `h`, two divisors of `Z` which are linearly equivalent on `A` are
linearly equivalent. -/
private theorem linearlyEquivalent_of_restrictAlong
    (hbig : ∀ E : MMP.Mori.PrimeDivisor Z, E.genericPoint ∈ Set.range h)
    {D₁ D₂ : Divisor Z}
    (hlin : (restrictAlong h D₁).LinearlyEquivalent (restrictAlong h D₂)) :
    D₁.LinearlyEquivalent D₂ := by
  obtain ⟨φ, hφ⟩ := hlin
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq_of_units φ
  obtain ⟨g0, rfl⟩ := (functionFieldMap_bijective_j h).2 g
  obtain ⟨ψ, hψ⟩ := exists_units_of_ne_zero (X := Z) (g := g0) (by
    rintro rfl
    exact hg0 (map_zero _))
  refine ⟨ψ, ?_⟩
  ext E
  obtain ⟨W, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff h E).2 (hbig E)
  have := congrArg (fun G : Divisor A => G.coeff W) hφ
  simp only [DivisorWithCoeffs.coeff_sub, coeff_restrictAlong, coeff_principalDivisor] at this
  change D₁.coeff _ - D₂.coeff _ = _
  rw [this, coeff_principalDivisor, hψ, hg]
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap h W.genericPoint
  exact ord_functionFieldMap_of_isIso h W _
    (OpenWeilRestriction.genericPoint_primeDivisorMap h W).symm g0

omit [CompactSpace A] [CompactSpace Z] in
private theorem restrictAlong_comp {B : Scheme.{u}} [IsIntegral B] [IsLocallyNoetherian B]
    [IsNormal B] (j : B ⟶ A) [IsOpenImmersion j] (D : Divisor Z) (i : A ⟶ Z)
    [IsOpenImmersion i] [IsDominant i] [IsDominant j] [IsOpenImmersion (j ≫ i)] :
    restrictAlong (j ≫ i) D = restrictAlong j (restrictAlong i D) := by
  refine Finsupp.ext fun W => ?_
  change D.coeff _ = D.coeff _
  congr 1
  refine PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    OpenWeilRestriction.genericPoint_primeDivisorMap,
    OpenWeilRestriction.genericPoint_primeDivisorMap]
  rfl

end Extend

section ExtendIso

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The extension of an isomorphism across codimension two, via linear equivalence.** -/
private theorem nonempty_restrict_iso_of_restrictAlong (S : X.Opens) [Nonempty S]
    [CompactSpace S] {A : Scheme.{u}} [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A]
    [Nonempty A] [CompactSpace A] (h : A ⟶ S.toScheme) [IsOpenImmersion h] [IsDominant h]
    (hbig : ∀ E : MMP.Mori.PrimeDivisor S.toScheme, E.genericPoint ∈ Set.range h)
    (K' : Divisor X) (D : Divisor S.toScheme) (M : S.toScheme.Modules)
    (e1 : D.divisorialSheaf ≅ M)
    (e2 : (restrictAlong (h ≫ S.ι) K').divisorialSheaf ≅ M.restrict h) :
    Nonempty (K'.divisorialSheaf.restrict S.ι ≅ M) := by
  have := isDominant_of_isOpenImmersion' S.ι
  obtain ⟨eR⟩ := nonempty_divisorialSheaf_restrictAlong_iso h D
  obtain ⟨eS⟩ := nonempty_divisorialSheaf_restrictAlong_iso S.ι K'
  have hK : restrictAlong (h ≫ S.ι) K' = restrictAlong h (restrictAlong S.ι K') :=
    restrictAlong_comp h K' S.ι
  have e3 : (restrictAlong h (restrictAlong S.ι K')).divisorialSheaf ≅
      (restrictAlong h D).divisorialSheaf :=
    eqToIso (by rw [← hK]) ≪≫ e2 ≪≫ (Scheme.Modules.restrictFunctor h).mapIso e1.symm ≪≫ eR.symm
  have hlin := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso e3
  have hlin' := linearlyEquivalent_of_restrictAlong h hbig hlin
  exact ⟨eS.symm ≪≫ hlin'.divisorialSheafIso ≪≫ e1⟩

end ExtendIso

section OpenVariety

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι
    (h : IsNormalVariety k sX) (V : X.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ sX) := by
  have := h.1
  have := h.2
  have : IsIntegral X := h.1.toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_opens_eq' (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have := hX.1
  have : IsIntegral X := hX.1.toIsIntegral
  have hbij : Function.Bijective (functionFieldMap U.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary U, trivial⟩
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- On a nonempty open subscheme of a normal variety, smooth over `k`, the module of relative
`n`-forms is divisorial. -/
private theorem exists_divisorialSheaf_iso_relativeDifferentialForms
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (S : X.Opens)
    [Nonempty S] (hS : Smooth (S.ι ≫ sX)) :
    ∃ D : Divisor S.toScheme,
      Nonempty (D.divisorialSheaf ≅ Scheme.Hom.relativeDifferentialForms (S.ι ≫ sX) n) := by
  have hSv := isNormalVariety_ι hX S
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsDominant S.ι := isDominant_of_isOpenImmersion' S.ι
  have hSd : topologicalKrullDim S.toScheme = n := (topologicalKrullDim_opens_eq' hX S).trans hn
  have : AlgebraicGeometry.IsVariety k (S.ι ≫ sX) := hSv.1
  have : IsIntegral S.toScheme := hSv.1.toIsIntegral
  have : CompactSpace S.toScheme := QuasiCompact.compactSpace_of_compactSpace (S.ι ≫ sX)
  have : SmoothOfRelativeDimension n (S.ι ≫ sX) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety (S.ι ≫ sX) n hSd
  have hinv := Stacks.Discriminant.isInvertible_relativeDifferentialForms (S.ι ≫ sX) n
  have hM := Stacks.SheafOfModules.isInvertible_of_tensorInvertible
    (X := S.toScheme.toRingedSpace) (Scheme.Hom.relativeDifferentialForms (S.ι ≫ sX) n) (h := hinv)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible S.toScheme.sheaf.obj
      S.toScheme.ringCatSheaf.property (Scheme.Hom.relativeDifferentialForms (S.ι ≫ sX) n) :=
    hM.toAlgebraicGeometry
  exact exists_divisorialSheaf_iso_of_isInvertible _

/-- Relative differential forms restrict along an open immersion. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso' {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- An open immersion smooth over the base lands in the smooth locus. -/
private theorem range_subset_smoothLocus {k : Type u} [Field k] {Y B : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (j : B ⟶ Y) [IsOpenImmersion j] (hs : Smooth (j ≫ sY)) :
    Set.range j ⊆ Set.range (smoothLocus sY).ι := by
  let V := j.opensRange
  have e : j.isoOpensRange.inv ≫ j = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sY) := by
    rw [← e, Category.assoc]
    infer_instance
  have hle := le_smoothLocus sY hV
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact hle ⟨x, rfl⟩

end OpenVariety

section KIso

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {sY : Y ⟶ Spec (.of k)}

/-- **A canonical divisor restricts to the canonical sheaf along a smooth open immersion.** -/
private theorem nonempty_restrictAlong_iso_relativeDifferentialForms {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) {B : Scheme.{u}} [IsIntegral B] [IsLocallyNoetherian B]
    [IsNormal B] [Nonempty B] (j : B ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    {p' : B ⟶ Spec (.of k)} (hp : j ≫ sY = p') (hs : Smooth (p')) :
    Nonempty ((restrictAlong j K).divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  subst hp
  obtain ⟨eR⟩ := nonempty_divisorialSheaf_restrictAlong_iso j K
  let S := smoothLocus sY
  let ψ : B ⟶ S.toScheme := IsOpenImmersion.lift S.ι j (range_subset_smoothLocus j hs)
  have hψ : ψ ≫ S.ι = j := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso' ψ (S.ι ≫ sY)
    (j ≫ sY) (by rw [← Category.assoc, hψ]) n
  exact ⟨eR ≪≫ (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

end KIso

section Main

variable {k : Type u} [Field k] {Y' Y : Scheme.{u}}
  {sY' : Y' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
  [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
  [IsLocallyNoetherian Y] [IsNormal Y]

private theorem notMem_supp {g : Y' ⟶ Y} (hg : IsSmallMorphism sY' sY g) {K : Divisor Y}
    (hKq : (Divisor.toQDivisor K).IsQCartier) :
    ∀ Z : irreducibleComponents Y',
      g (componentGenericPoint Y' Z) ∉ (Divisor.toQDivisor K).supp := by
  have : IsIntegral Y' := hg.isNormalVariety_source.1.toIsIntegral
  have : IsIntegral Y := hg.isNormalVariety_target.1.toIsIntegral
  have : IsDominant g := hg.isBirationalMorphism.isDominant
  exact map_componentGenericPoint_notMem_supp_of_isQCartier g hKq

private theorem exists_toQDivisor_eq_pullback {g : Y' ⟶ Y} (hg : IsSmallMorphism sY' sY g)
    {K : Divisor Y} (hKq : (Divisor.toQDivisor K).IsQCartier) :
    ∃ K' : Divisor Y', Divisor.toQDivisor K' =
      QDivisor.pullback (f := g) (Divisor.toQDivisor K) hKq (notMem_supp hg hKq) := by
  have : IsIntegral Y' := hg.isNormalVariety_source.1.toIsIntegral
  have : IsIntegral Y := hg.isNormalVariety_target.1.toIsIntegral
  have : IsDominant g := hg.isBirationalMorphism.isDominant
  set B := QDivisor.pullback (f := g) (Divisor.toQDivisor K) hKq (notMem_supp hg hKq) with hBdef
  have hint : ∀ E : MMP.Mori.PrimeDivisor Y', ∃ n : ℤ, B.coeff E = n := by
    intro E
    have hx := map_genericPoint_mem_biregularLocus hg E
    obtain ⟨P, hP⟩ := exists_primeDivisor_map g hx E.coheight_genericPoint
    have := isIso_stalkMap_of_mem g hx
    exact ⟨K.coeff P, coeff_pullback_eq hKq _ E P hP⟩
  choose n hn using hint
  refine ⟨Finsupp.onFinset B.support n fun E hE => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff]
    change B.coeff E ≠ 0
    rw [hn E]
    exact_mod_cast hE
  · refine Finsupp.ext fun E => ?_
    change (Divisor.toQDivisor _).coeff E = B.coeff E
    rw [Divisor.coeff_toQDivisor, hn E]
    rfl

private theorem nonempty_iso_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (M N : X.Modules) :
    Nonempty (M ≅ N) := by
  have : IsIso (0 : M ⟶ N) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    have := Module.subsingleton Γ(X, U) Γ(M, U)
    have := Module.subsingleton Γ(X, U) Γ(N, U)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  exact ⟨asIso (0 : M ⟶ N)⟩

private theorem compactSpace_opens' {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
    (S : Y.Opens) : CompactSpace S := by
  have : IsNoetherian Y := {}
  exact TopologicalSpace.NoetherianSpace.compactSpace (S : Set Y)

private theorem topologicalKrullDim_eq {g : Y' ⟶ Y} (hg : IsSmallMorphism sY' sY g) {n : ℕ}
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n) : topologicalKrullDim Y' = n := by
  have := hg.isNormalVariety_source.1
  have := hg.isNormalVariety_target.1
  rw [← hK.topologicalKrullDim_eq]
  exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY sY'
    hg.isBirationalMorphism).symm

/-- **`g^*K` agrees with `K` over the biregular locus.** Along an open immersion `j : B ⟶ Y'`
landing in `g⁻¹(V)`, `V` the biregular locus of `g`, the restriction of `g^*K` is the restriction
of `K` along `j ≫ g`. -/
private theorem restrictAlong_eq_restrictAlong_comp [IsIntegral Y'] [IsIntegral Y] {g : Y' ⟶ Y}
    (hg : IsSmallMorphism sY' sY g) {K : Divisor Y} (hKq : (Divisor.toQDivisor K).IsQCartier)
    {K' : Divisor Y'}
    (hK' : Divisor.toQDivisor K' =
      QDivisor.pullback (f := g) (Divisor.toQDivisor K) hKq (notMem_supp hg hKq))
    {B : Scheme.{u}} (j : B ⟶ Y') [IsOpenImmersion j] [IsOpenImmersion (j ≫ g)]
    (hj : ∀ x, g (j x) ∈ biregularLocus g) :
    restrictAlong j K' = restrictAlong (j ≫ g) K := by
  have : IsDominant g := hg.isBirationalMorphism.isDominant
  refine Finsupp.ext fun W => ?_
  change K'.coeff _ = K.coeff _
  have hEη : Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap j W) =
      j W.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  have hPη : Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap (j ≫ g) W) =
      (j ≫ g) W.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  have := isIso_stalkMap_of_mem g (hEη ▸ hj W.genericPoint)
  have h2 := congrArg (fun G : QDivisor Y' => G.coeff (OpenWeilRestriction.primeDivisorMap j W))
    hK'
  simp only [Divisor.coeff_toQDivisor] at h2
  exact_mod_cast h2.trans (coeff_pullback_eq hKq (notMem_supp hg hKq) _ _
    (by rw [hEη, hPη]; rfl))

private theorem nonempty_divisorialSheaf_restrict_iso {g : Y' ⟶ Y}
    (hg : IsSmallMorphism sY' sY g) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    (hKq : (Divisor.toQDivisor K).IsQCartier) {K' : Divisor Y'}
    (hK' : Divisor.toQDivisor K' =
      QDivisor.pullback (f := g) (Divisor.toQDivisor K) hKq (notMem_supp hg hKq)) :
    Nonempty (K'.divisorialSheaf.restrict (smoothLocus sY').ι ≅ canonicalSheaf sY' n) := by
  have hY'v : IsNormalVariety k sY' := hg.isNormalVariety_source
  have hYv : IsNormalVariety k sY := hg.isNormalVariety_target
  have : IsIntegral Y' := hY'v.1.toIsIntegral
  have : IsIntegral Y := hYv.1.toIsIntegral
  have : IsDominant g := hg.isBirationalMorphism.isDominant
  have hn : topologicalKrullDim Y' = n := topologicalKrullDim_eq hg hK
  by_cases hne : Nonempty (smoothLocus sY' : Y'.Opens)
  · have hsmooth : Smooth ((smoothLocus sY').ι ≫ sY') := by
      have : LocallyOfFiniteType sY' := hY'v.1.toLocallyOfFiniteType
      have : LocallyOfFinitePresentation sY' :=
        LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
      rw [smoothLocus_eq_smoothLocus]
      rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
        Scheme.Opens.ι_preimage_self]
    set S' := smoothLocus sY' with hS'
    obtain ⟨D, ⟨e1⟩⟩ := exists_divisorialSheaf_iso_relativeDifferentialForms hY'v hn S' hsmooth
    let U' : Y'.Opens := g ⁻¹ᵁ biregularLocus g
    let A : Y'.Opens := S' ⊓ U'
    have hAS : A ≤ S' := inf_le_left
    have hAU : A ≤ U' := inf_le_right
    have hηS : genericPoint Y' ∈ S' := by
      obtain ⟨x⟩ := hne
      exact ((genericPoint_spec Y').mem_open_set_iff S'.isOpen).mpr ⟨x.1, trivial, x.2⟩
    have hηU : genericPoint Y' ∈ U' := genericPoint_map_mem_biregularLocus hg
    have : Nonempty A := ⟨⟨genericPoint Y', hηS, hηU⟩⟩
    let h : A.toScheme ⟶ S'.toScheme := Y'.homOfLE hAS
    have hh : h ≫ S'.ι = A.ι := Scheme.homOfLE_ι _ _
    have : IsDominant h := isDominant_of_isOpenImmersion' h
    have hjY : IsOpenImmersion ((h ≫ S'.ι) ≫ g) := by
      have := isOpenImmersion_ι_comp g
      have e : (h ≫ S'.ι) ≫ g = Y'.homOfLE hAU ≫ ((g ⁻¹ᵁ biregularLocus g).ι ≫ g) := by
        rw [hh, ← Scheme.homOfLE_ι Y' hAU, Category.assoc]
      rw [e]
      infer_instance
    have : IsDominant ((h ≫ S'.ι) ≫ g) := isDominant_of_isOpenImmersion' _
    have hs : Smooth (h ≫ S'.ι ≫ sY') := by
      have : Smooth (S'.ι ≫ sY') := hsmooth
      infer_instance
    obtain ⟨eK⟩ := nonempty_restrictAlong_iso_relativeDifferentialForms hK
      ((h ≫ S'.ι) ≫ g) (p' := h ≫ S'.ι ≫ sY')
      (by rw [Category.assoc, Category.assoc, hg.comp_eq]) hs
    have hdiv := restrictAlong_eq_restrictAlong_comp hg hKq hK' (h ≫ S'.ι)
      fun x => by rw [hh]; exact x.2.2
    have e2 : (restrictAlong (h ≫ S'.ι) K').divisorialSheaf ≅
        (Scheme.Hom.relativeDifferentialForms (S'.ι ≫ sY') n).restrict h :=
      eqToIso (by rw [hdiv]) ≪≫ eK ≪≫
        (nonempty_restrict_relativeDifferentialForms_iso' h (S'.ι ≫ sY') (h ≫ S'.ι ≫ sY')
          rfl n).some.symm
    have hbig : ∀ E : MMP.Mori.PrimeDivisor S'.toScheme, E.genericPoint ∈ Set.range h := by
      intro E
      have hE := map_genericPoint_mem_biregularLocus hg
        (OpenWeilRestriction.primeDivisorMap S'.ι E)
      have hgp : (OpenWeilRestriction.primeDivisorMap S'.ι E).genericPoint =
          S'.ι E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
      have hE' : g (S'.ι E.genericPoint) ∈ biregularLocus g := hgp ▸ hE
      exact ⟨⟨S'.ι E.genericPoint, E.genericPoint.2, hE'⟩,
        Subtype.ext (by simp [h, Scheme.homOfLE_apply]; rfl)⟩
    have : CompactSpace S' := compactSpace_opens' S'
    have : CompactSpace A := compactSpace_opens' A
    exact nonempty_restrict_iso_of_restrictAlong S' h hbig K' D _ e1 e2
  · have : IsEmpty (smoothLocus sY').toScheme := not_nonempty_iff.mp hne
    exact nonempty_iso_of_isEmpty _ _

end Main

section

variable {k : Type u} [Field k] {Y' Y : Scheme.{u}}
  {sY' : Y' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
  [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
  [IsLocallyNoetherian Y] [IsNormal Y]

/-- **A small birational model is crepant.** If `g : Y' ⟶ Y` is a small proper birational
morphism of normal varieties over `k` and `K` is a `ℚ`-Cartier canonical divisor of `Y`, then the
pull-back `g^*K` is a canonical divisor of `Y'`: `K_{Y'} = g^*K_Y`. -/
@[mmp "lem_oai4_c2_small_model_crepant"]
public theorem IsSmallMorphism.exists_isCanonicalDivisor_eq_pullback {g : Y' ⟶ Y}
    (hg : IsSmallMorphism sY' sY g) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    (hKq : (Divisor.toQDivisor K).IsQCartier) :
    ∃ K' : Divisor Y', K'.IsCanonicalDivisor sY' n ∧
      Divisor.toQDivisor K' = QDivisor.pullback (f := g) (Divisor.toQDivisor K) hKq
        (by
          haveI : IsIntegral Y' := hg.isNormalVariety_source.1.toIsIntegral
          haveI : IsIntegral Y := hg.isNormalVariety_target.1.toIsIntegral
          haveI : IsDominant g := hg.isBirationalMorphism.isDominant
          exact map_componentGenericPoint_notMem_supp_of_isQCartier g hKq) := by
  obtain ⟨K', hK'⟩ := exists_toQDivisor_eq_pullback hg hKq
  exact ⟨K', ⟨topologicalKrullDim_eq hg hK, nonempty_divisorialSheaf_restrict_iso hg hK hKq hK'⟩,
    hK'⟩

end

end MMP.Fourfold

/-!
## The unit-drop valuation stays exceptional through a terminal bridge

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail, `i ≥ 0`, and
`V ⊆ W_i⁺ ⊆ X_{i+1}` an irreducible surface in the positive-side bad locus of the `i`-th step,
with `X_{i+1}` smooth at `η_V` and `mld_{η_V}(X_{i+1}, B_{i+1}) > 1`. Then the generic blowup
valuation `v_V` of `k(X_{i+1})` is exceptional over every model of a terminal bridge from a
crepant junction `Y_i` of `(X_i, B_i)` to a crepant junction `Y_{i+1}` of `(X_{i+1}, B_{i+1})`:
over `Y_i = V_0`, over every model `V_k` of the relative program of the bridge, and over
`Y_{i+1}`.

### Main results

* `TerminalBridge.isExceptionalValuation_of_isSurfaceGenericBlowupValuation`: `v_V` is
  exceptional over every model of the bridge.

### Implementation notes

All models of the bridge lie over `Z_i` by birational morphisms, so a valuation of `k(X_{i+1})`
is carried to a valuation of the function field of a model `M` by asking that the two have the
same restriction to `k(Z_i)`, through `f_i⁺ : X_{i+1} ⟶ Z_i` and through the morphism `M ⟶ Z_i`
(`π_k` for the model `V_k` of the program, `f_i⁺ ∘ p_{i+1}` for `Y_{i+1}`). Since the maps of
function fields are isomorphisms, this valuation exists and is unique; the statement asserts
exceptionality for every valuation so related.
-/

namespace MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge

open TopologicalSpace MMP.Positivity.DivisorOver
open scoped WithZero

set_option backward.isDefEq.respectTransparency false in
/-- A birational morphism followed by an isomorphism is birational. -/
private theorem isBirationalMorphism_comp_hom {X Y Z : Scheme} {f : X ⟶ Y} (e : Y ≅ Z)
    (hf : MMP.Mori.IsBirationalMorphism f) : MMP.Mori.IsBirationalMorphism (f ≫ e.hom) := by
  obtain ⟨e0, he0⟩ := hf
  have hd : Dense ((e.inv ⁻¹ᵁ e0.target : Z.Opens) : Set Z) :=
    e0.dense_target.preimage e.inv.isOpenEmbedding.isOpenMap
  refine ⟨⟨e0.source, e0.dense_source, e.inv ⁻¹ᵁ e0.target, hd,
    e0.iso ≪≫ (e.inv.preimageIso e0.target).symm⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap] at he0 ⊢
  rw [Scheme.PartialMap.toRationalMap_eq_iff] at he0 ⊢
  obtain ⟨U, hU, h1, h2, h3⟩ := he0
  refine ⟨U, hU, h1, h2, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at h3 ⊢
  have key : (e.inv.preimageIso e0.target).inv ≫ (e.inv ⁻¹ᵁ e0.target).ι =
      e0.target.ι ≫ e.hom := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.Hom.preimageIso_hom_ι, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, key]
  simp only [← Category.assoc] at h3 ⊢
  rw [h3]

/-- Exceptionality of a normalized divisorial valuation is invariant under an isomorphism
`e : M ≅ N` of varieties over `k`: if `w` is exceptional over `M`, then its transport
`w ∘ e^*` to `k(N)` is exceptional over `N`. -/
private theorem isExceptionalValuation_comap_functionFieldMap_hom {k : Type*} [Field k]
    {M N : Scheme} [IsIntegral M] [IsIntegral N] {sM : M ⟶ Spec (.of k)}
    {sN : N ⟶ Spec (.of k)} (e : M ≅ N) (he : e.hom ≫ sN = sM)
    {w : Valuation M.functionField (WithZero (Multiplicative ℤ))}
    (hw : MMP.Intersection.IsExceptionalValuation k sM w) :
    MMP.Intersection.IsExceptionalValuation k sN (w.comap (functionFieldMap e.hom)) := by
  obtain ⟨D, hp, rfl, hc⟩ := hw
  let D' : MMP.Mori.DivisorOver k sN :=
    { Y := D.Y, f := D.f ≫ e.hom
      isNormalVariety := by rw [Category.assoc, he]; exact D.isNormalVariety
      isBirationalMorphism := isBirationalMorphism_comp_hom e D.isBirationalMorphism
      E := D.E }
  refine ⟨D', ?_, ?_, ?_⟩
  · change IsProper (D.f ≫ e.hom)
    infer_instance
  · have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    ext g
    change D.E.valuationOver D.f (functionFieldMap e.hom g) = D.E.valuationOver (D.f ≫ e.hom) g
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  · let h := Scheme.homeoOfIso e
    have hmap : ∀ A : IrreducibleCloseds M,
        (IrreducibleCloseds.map e.hom e.hom.continuous A : Set N) = h '' A := fun A => by
      rw [IrreducibleCloseds.coe_map]
      exact (h.isClosedMap _ A.isClosed).closure_eq
    have hcen : D'.center = IrreducibleCloseds.map e.hom e.hom.continuous D.center := by
      ext1
      rw [hmap, MMP.Mori.DivisorOver.coe_center, MMP.Mori.DivisorOver.coe_center,
        h.image_closure]
      change closure ((D.f ≫ e.hom) '' _) = _
      congr 1
      ext x
      simp [h]
      rfl
    rw [hcen]
    refine hc.trans (Order.coheight_le_coheight_apply_of_strictMono _ (fun A B hAB => ?_) _)
    rw [← SetLike.coe_ssubset_coe, hmap, hmap]
    exact h.injective.image_strictMono (SetLike.coe_ssubset_coe.mpr hAB)

/-- Outside the exceptional locus `Ex(g)` of a morphism, `g` preserves coheights. -/
private theorem coheight_map_of_notMem_exceptionalSet' {M N : Scheme.{0}} (g : M ⟶ N) {y : M}
    (hy : y ∉ (MMP.Mori.exceptionalSet g : Set M)) : Order.coheight (g y) = Order.coheight y := by
  have hmem : y ∈ g ⁻¹ᵁ MMP.Mori.biregularLocus g := by
    by_contra h
    exact hy h
  refine MMP.Flips.coheight_map_of_notMem_exceptionalSet ?_
  rintro hn
  apply hn
  refine ⟨g ⁻¹ᵁ MMP.Mori.biregularLocus g, hmem, ?_⟩
  have : IsIso (g ∣_ MMP.Mori.biregularLocus g) := MMP.Mori.isBiregular_biregularLocus g
  have h2 : (g ⁻¹ᵁ MMP.Mori.biregularLocus g).ι ≫ g =
      (g ∣_ MMP.Mori.biregularLocus g) ≫ (MMP.Mori.biregularLocus g).ι :=
    (morphismRestrict_ι g _).symm
  rw [h2]
  infer_instance

section General

variable {M N : Scheme.{0}} [IsIntegral M] [IsIntegral N] {sM : M ⟶ Spec (.of ℂ)}
  {sN : N ⟶ Spec (.of ℂ)}

/-- The composite of proper birational morphisms of normal varieties is birational. -/
private theorem isBirationalMorphism_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] {sA : A ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    (hA : MMP.Mori.IsNormalVariety ℂ sA) (hB : MMP.Mori.IsNormalVariety ℂ sB) (f : A ⟶ B)
    [IsProper f] (hf : MMP.Mori.IsBirationalMorphism f) (h : C ⟶ A) [IsProper h]
    (hh : MMP.Mori.IsBirationalMorphism h) : MMP.Mori.IsBirationalMorphism (h ≫ f) := by
  have := hA.1.toLocallyOfFiniteType
  have := hB.1.toLocallyOfFiniteType
  have := hA.2
  have := hB.2
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian sB
  exact MMP.Mori.isBirationalMorphism_comp_of_isBirational f h
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hh)

/-- Pushing a proper divisor over `M` forward along a proper birational morphism `g : M ⟶ N`. -/
private theorem exists_divisorOver_comp (hM : MMP.Mori.IsNormalVariety ℂ sM)
    (hN : MMP.Mori.IsNormalVariety ℂ sN) (g : M ⟶ N) (hg : g ≫ sN = sM) [IsProper g] [IsDominant g]
    (hb : MMP.Mori.IsBirationalMorphism g) (D : MMP.Mori.DivisorOver ℂ sM) (hD : IsProper D.f) :
    ∃ D' : MMP.Mori.DivisorOver ℂ sN, IsProper D'.f ∧
      D'.f D'.E.genericPoint = g (D.f D.E.genericPoint) ∧
      D'.valuation = D.valuation.comap (functionFieldMap g) := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := hM.1.toLocallyOfFiniteType
  have := hN.1.toLocallyOfFiniteType
  have := hM.2
  have := hN.2
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian sN
  have hbD := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism
  have hbg := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb
  have hcomp : MMP.Mori.IsBirationalMorphism (D.f ≫ g) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational g D.f hbg hbD
  have hs : (D.f ≫ g) ≫ sN = D.f ≫ sM := by rw [Category.assoc, hg]
  refine ⟨⟨D.Y, D.f ≫ g, by rw [hs]; exact D.isNormalVariety, hcomp, D.E⟩, ?_, rfl, ?_⟩
  · change IsProper (D.f ≫ g)
    infer_instance
  · have : IsDominant (D.f ≫ g) := hcomp.isDominant
    ext x
    change D.E.valuationOver (D.f ≫ g) x = D.E.valuationOver D.f (functionFieldMap g x)
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
      functionFieldMap_functionFieldMap_apply]

/-- A valuation exceptional over `M` pushes forward to a valuation exceptional over `N`. -/
private theorem isExceptionalValuation_comap (hM : MMP.Mori.IsNormalVariety ℂ sM)
    (hN : MMP.Mori.IsNormalVariety ℂ sN) (g : M ⟶ N) (hg : g ≫ sN = sM) [IsProper g]
    [IsDominant g] (hb : MMP.Mori.IsBirationalMorphism g)
    (hdim : topologicalKrullDim M = topologicalKrullDim N)
    {w : Valuation M.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sM w) :
    MMP.Intersection.IsExceptionalValuation ℂ sN (w.comap (functionFieldMap g)) := by
  obtain ⟨D, hp, rfl, hc⟩ := h
  obtain ⟨D', hp', hη, hv⟩ := exists_divisorOver_comp hM hN g hg hb D hp
  refine ⟨D', hp', hv.symm, ?_⟩
  rw [MMP.Positivity.DivisorOver.codimension_center, hη]
  rw [MMP.Positivity.DivisorOver.codimension_center] at hc
  exact hc.trans (MMP.Flips.coheight_le_coheight_map sN sM hN.1 hM.1 g hg hdim _)

/-- **Small morphisms preserve non-exceptionality.** -/
private theorem isExceptionalValuation_of_comap (hM : MMP.Mori.IsNormalVariety ℂ sM)
    (hN : MMP.Mori.IsNormalVariety ℂ sN) (g : M ⟶ N) (hg : g ≫ sN = sM) [IsProper g]
    [IsDominant g] (hb : MMP.Mori.IsBirationalMorphism g)
    (hex : 2 ≤ MMP.Mori.closedsCodimension (MMP.Mori.exceptionalSet g))
    {w : Valuation M.functionField (WithZero (Multiplicative ℤ))}
    (hD : MMP.Intersection.IsNormalizedDivisorialValuation ℂ sM w)
    (h : MMP.Intersection.IsExceptionalValuation ℂ sN (w.comap (functionFieldMap g))) :
    MMP.Intersection.IsExceptionalValuation ℂ sM w := by
  obtain ⟨D, hp, rfl⟩ := hD
  refine ⟨D, hp, rfl, ?_⟩
  obtain ⟨D', hp', hη, hv⟩ := exists_divisorOver_comp hM hN g hg hb D hp
  obtain ⟨D'', hp'', hv'', hc⟩ := h
  have hηη : D'.f D'.E.genericPoint = D''.f D''.E.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hN.1 (hv.trans hv'')
  rw [MMP.Positivity.DivisorOver.codimension_center] at hc ⊢
  rw [← hηη, hη] at hc
  have hex' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hex
  by_contra hlt
  have hy : D.f D.E.genericPoint ∉ (MMP.Mori.exceptionalSet g : Set M) := fun hmem =>
    hlt (hex' _ hmem)
  rw [coheight_map_of_notMem_exceptionalSet' g hy] at hc
  exact hlt hc

end General

/-- The residue field of a valuation trivial on `k` is a `k`-algebra. -/
@[instance_reducible] private noncomputable def residueAlgebra {k K : Type u} [Field k]
    [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) (hk : ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1) :
    Algebra k (IsLocalRing.ResidueField v.valuationSubring) :=
  ((IsLocalRing.residue v.valuationSubring).comp
    ((algebraMap k K).codRestrict v.valuationSubring fun c => by
      by_cases hc : c = 0
      · simp [hc]
      · exact (Valuation.mem_valuationSubring_iff _ _).2 (hk c hc).le :
      k →+* v.valuationSubring)).toAlgebra

/-- The residue field of the valuation ring of `v` is the residue field of any local ring `A`
whose image in `K` (up to `φ`) is the valuation ring. -/
private theorem trdeg_residueField_valuationSubring {k K K' A : Type u} [Field k] [Field K]
    [Field K'] [CommRing A] [IsLocalRing A] [Algebra k K] [Algebra k K'] [Algebra k A]
    [Algebra A K'] [IsScalarTower k A K'] (φ : K ≃ₐ[k] K')
    (hι : Function.Injective (algebraMap A K')) (v : Valuation K ℤᵐ⁰)
    (hv : ∀ x, v x ≤ 1 ↔ φ x ∈ (algebraMap A K').range)
    (hk : ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1) :
    letI := residueAlgebra v hk
    Algebra.trdeg k (IsLocalRing.ResidueField v.valuationSubring) =
      Algebra.trdeg k (IsLocalRing.ResidueField A) := by
  let := residueAlgebra v hk
  have hmem : ∀ a : A, φ.symm (algebraMap A K' a) ∈ v.valuationSubring := fun a => by
    rw [Valuation.mem_valuationSubring_iff, hv, AlgEquiv.apply_symm_apply]
    exact ⟨a, rfl⟩
  let ψ : A →+* v.valuationSubring :=
    { toFun := fun a => ⟨φ.symm (algebraMap A K' a), hmem a⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun a b h => hι (φ.symm.injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := (hv x).1 ((Valuation.mem_valuationSubring_iff _ _).1 hx)
    refine ⟨a, Subtype.ext ?_⟩
    change φ.symm (algebraMap A K' a) = x
    rw [ha, AlgEquiv.symm_apply_apply]
  let e := RingEquiv.ofBijective ψ hψ
  let E : IsLocalRing.ResidueField A ≃ₐ[k] IsLocalRing.ResidueField v.valuationSubring :=
    AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv e) (fun c => by
      rw [IsLocalRing.ResidueField.mapEquiv_apply,
        show algebraMap k (IsLocalRing.ResidueField A) c =
          IsLocalRing.residue A (algebraMap k A c) from rfl,
        IsLocalRing.ResidueField.map_residue]
      refine congrArg (IsLocalRing.residue v.valuationSubring) (Subtype.ext ?_)
      change φ.symm (algebraMap A K' (algebraMap k A c)) = algebraMap k K c
      rw [← IsScalarTower.algebraMap_apply]
      exact φ.symm.commutes c)
  exact E.symm.trdeg_eq

/-- `trdeg κ(E) + 1 = trdeg k(Y)` for a prime divisor `E` of a variety. -/
private theorem trdeg_residueField_genericPoint_add_one {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (hY : MMP.Mori.IsVariety k sY)
    (E : MMP.Mori.PrimeDivisor Y) :
    letI := MMP.Mori.stalkAlgebra sY E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sY
    Algebra.trdeg k (IsLocalRing.ResidueField E.localRing) + 1 =
      Algebra.trdeg k Y.functionField := by
  let := MMP.Mori.stalkAlgebra sY E.genericPoint
  let := MMP.Mori.functionFieldAlgebra sY
  have := hY.toLocallyOfFiniteType
  have h1 := topologicalKrullDim_closure_singleton_eq_trdeg k Y sY E.genericPoint
  have h2 := MMP.Mori.toENat_trdeg_functionField (sX := sY)
  have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY E.genericPoint
  rw [PrimeDivisor.coheight_genericPoint, h1, ← h2] at h3
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hfin := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY
  have h4 : Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField E.localRing)) + 1 =
      Cardinal.toENat (Algebra.trdeg k Y.functionField) := mod_cast h3
  have hK : Cardinal.toENat (Algebra.trdeg k Y.functionField) ≠ ⊤ := fun h => hfin (by
    rw [← h2, h]; rfl)
  have hK' := Cardinal.toENat_lt_top.1 hK.lt_top
  have hκ : Algebra.trdeg k (IsLocalRing.ResidueField E.localRing) + 1 < Cardinal.aleph0 := by
    rw [← Cardinal.toENat_lt_top, map_add, map_one, h4]
    exact hK.lt_top
  exact Cardinal.toENat_injOn hκ.le hK'.le (by rw [map_add, map_one, h4])

/-- A valuation which is at most `1` on a ring `O` is `1` on its units. -/
private theorem map_algebraMap_unit_eq_one {O K Γ : Type*} [CommRing O] [Field K] [Algebra O K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (h1 : ∀ a : O, v (algebraMap O K a) ≤ 1)
    (u : Oˣ) : v (algebraMap O K u) = 1 := by
  refine le_antisymm (h1 _) ?_
  have h3 : v (algebraMap O K ↑u) * v (algebraMap O K ↑u⁻¹) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  calc (1 : Γ) = _ := h3.symm
    _ ≤ v (algebraMap O K ↑u) * 1 := by gcongr; exact h1 _
    _ = _ := mul_one _

/-- The valuation `v` of `K` is surjective, trivial on `k`, and its residue field has
transcendence degree `trdeg_k K - 1`. -/
private def IsMaxRes {K : Type} [Field K] [Algebra ℂ K] (v : Valuation K ℤᵐ⁰) : Prop :=
  Function.Surjective v ∧ ∃ hk : ∀ c : ℂ, c ≠ 0 → v (algebraMap ℂ K c) = 1,
    letI := residueAlgebra v hk
    Algebra.trdeg ℂ (IsLocalRing.ResidueField v.valuationSubring) + 1 = Algebra.trdeg ℂ K

/-- The valuation of a divisor over a variety is surjective, trivial on `ℂ` and has residue
transcendence degree `trdeg - 1`. -/
private theorem isMaxRes_valuation {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}
    (D : MMP.Mori.DivisorOver ℂ sX) :
    letI := MMP.Mori.functionFieldAlgebra sX
    IsMaxRes D.valuation := by
  let := MMP.Mori.functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hbij := D.isBirationalMorphism.functionFieldMap_bijective
  let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
  let := MMP.Mori.stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  have hY : MMP.Mori.IsVariety ℂ (D.f ≫ sX) := D.isNormalVariety.1
  have hst := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  let φ := MMP.Mori.functionFieldAlgEquiv sX D.f hbij
  have hφ : ∀ x, φ x = functionFieldMap D.f x := fun x => rfl
  have hv : ∀ x, D.valuation x = D.E.divisorialValuation (φ x) := fun x => by
    rw [hφ]; exact MMP.Mori.PrimeDivisor.valuationOver_apply _ _ _
  have hle : ∀ x, D.valuation x ≤ 1 ↔ φ x ∈ (algebraMap D.E.localRing D.Y.functionField).range :=
    fun x => by rw [hv]; exact D.E.divisorialValuation_le_one_iff _
  have hk : ∀ c : ℂ, c ≠ 0 → D.valuation (algebraMap ℂ X.functionField c) = 1 := by
    intro c hc
    rw [hv, φ.commutes, IsScalarTower.algebraMap_apply ℂ D.E.localRing D.Y.functionField]
    have hu : IsUnit (algebraMap ℂ D.E.localRing c) := (IsUnit.mk0 c hc).map _
    have := map_algebraMap_unit_eq_one D.E.divisorialValuation
      (fun a => (D.E.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩) hu.unit
    simpa using this
  refine ⟨?_, hk, ?_⟩
  · obtain ⟨g, hg⟩ := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one D
    intro a
    induction a using WithZero.recZeroCoe with
    | zero => exact ⟨0, map_zero _⟩
    | coe m =>
      refine ⟨g ^ (-(Multiplicative.toAdd m)), ?_⟩
      rw [map_zpow₀, hg, ← WithZero.exp_zsmul]
      have : (↑m : ℤᵐ⁰) = WithZero.exp (Multiplicative.toAdd m) := rfl
      rw [this]
      congr 1
      simp
  · have hres := trdeg_residueField_valuationSubring φ (IsFractionRing.injective D.E.localRing
      D.Y.functionField) D.valuation hle hk
    rw [hres, trdeg_residueField_genericPoint_add_one hY D.E,
      MMP.Mori.trdeg_functionField_eq_of_bijective sX D.f hbij]

/-- `IsMaxRes` is invariant under an isomorphism of `ℂ`-algebras carrying one valuation to the
other. -/
private theorem IsMaxRes.of_equiv {K K' : Type} [Field K] [Field K'] [Algebra ℂ K]
    [Algebra ℂ K'] (σ : K ≃ₐ[ℂ] K') {v : Valuation K ℤᵐ⁰} {w : Valuation K' ℤᵐ⁰}
    (h : ∀ x, w (σ x) = v x) (hv : IsMaxRes v) : IsMaxRes w := by
  obtain ⟨hsurj, hk, htr⟩ := hv
  have hk' : ∀ c : ℂ, c ≠ 0 → w (algebraMap ℂ K' c) = 1 := fun c hc => by
    rw [← σ.commutes, h]; exact hk c hc
  refine ⟨fun a => ?_, hk', ?_⟩
  · obtain ⟨x, hx⟩ := hsurj a
    exact ⟨σ x, by rw [h, hx]⟩
  · let := residueAlgebra v hk
    let := residueAlgebra w hk'
    have hmem : ∀ a : v.valuationSubring, σ a ∈ w.valuationSubring := fun a => by
      rw [Valuation.mem_valuationSubring_iff, h]
      exact (Valuation.mem_valuationSubring_iff _ _).1 a.2
    let ψ : v.valuationSubring →+* w.valuationSubring :=
      { toFun := fun a => ⟨σ a, hmem a⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp
        map_zero' := by ext; simp
        map_add' := by intro a b; ext; simp }
    have hψ : Function.Bijective ψ := by
      refine ⟨fun a b hab => Subtype.ext (σ.injective (congrArg Subtype.val hab)), ?_⟩
      rintro ⟨y, hy⟩
      refine ⟨⟨σ.symm y, ?_⟩, Subtype.ext (by simp [ψ])⟩
      rw [Valuation.mem_valuationSubring_iff, ← h, AlgEquiv.apply_symm_apply]
      exact (Valuation.mem_valuationSubring_iff _ _).1 hy
    let e := RingEquiv.ofBijective ψ hψ
    let E : IsLocalRing.ResidueField v.valuationSubring ≃ₐ[ℂ]
        IsLocalRing.ResidueField w.valuationSubring :=
      AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv e) (fun c => by
        change IsLocalRing.ResidueField.mapEquiv e (IsLocalRing.residue _ _) =
          IsLocalRing.residue _ _
        rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
        refine congrArg (IsLocalRing.residue w.valuationSubring) (Subtype.ext ?_)
        exact σ.commutes c)
    rwa [← E.trdeg_eq, ← σ.trdeg_eq]

/-- **Realizing a transported divisorial valuation on a proper birational model.** Let `D₀` be a
divisor over `X'`, `fp : X' ⟶ Z` and `π : M ⟶ Z` birational morphisms of varieties with `π`
proper. Every valuation `w` of `k(M)` which agrees with the valuation of `D₀` on `k(Z)` is the
valuation of a divisor over `M` with proper morphism. -/
private theorem exists_divisorOver_of_comap_eq {M X' Z : Scheme.{0}} [IsIntegral M]
    [IsIntegral X'] [IsIntegral Z] {sM : M ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsVariety ℂ sZ) (hM : MMP.Mori.IsVariety ℂ sM)
    (hX' : MMP.Mori.IsVariety ℂ sX') (π : M ⟶ Z) (hπ : π ≫ sZ = sM) [IsProper π]
    [IsDominant π] (hπb : Function.Bijective (functionFieldMap π)) (fp : X' ⟶ Z)
    (hfp : fp ≫ sZ = sX') [IsDominant fp] (hfpb : MMP.Mori.IsBirationalMorphism fp)
    (D0 : MMP.Mori.DivisorOver ℂ sX') (w : Valuation M.functionField ℤᵐ⁰)
    (hw : w.comap (functionFieldMap π) = D0.valuation.comap (functionFieldMap fp)) :
    ∃ D : MMP.Mori.DivisorOver ℂ sM, IsProper D.f ∧ D.valuation = w := by
  subst hπ hfp
  have hb1 := hfpb.functionFieldMap_bijective
  have hb2 := hπb
  let := MMP.Mori.functionFieldAlgebra sZ
  let := MMP.Mori.functionFieldAlgebra (fp ≫ sZ)
  let := MMP.Mori.functionFieldAlgebra (π ≫ sZ)
  let σ : X'.functionField ≃ₐ[ℂ] M.functionField :=
    (MMP.Mori.functionFieldAlgEquiv sZ fp hb1).symm.trans
      (MMP.Mori.functionFieldAlgEquiv sZ π hb2)
  have hσ : ∀ x, w (σ x) = D0.valuation x := by
    intro x
    obtain ⟨z, rfl⟩ := hb1.2 x
    have hz : σ (functionFieldMap fp z) = functionFieldMap π z := by
      change (MMP.Mori.functionFieldAlgEquiv sZ π hb2)
        ((MMP.Mori.functionFieldAlgEquiv sZ fp hb1).symm
          ((MMP.Mori.functionFieldAlgEquiv sZ fp hb1) z)) = _
      rw [AlgEquiv.symm_apply_apply]
      rfl
    rw [hz]
    exact congrArg (fun u => u z) hw
  have hmax := IsMaxRes.of_equiv σ hσ (isMaxRes_valuation D0)
  obtain ⟨hsurj, hk, htr⟩ := hmax
  have := D0.isIntegral
  have := D0.isNormal
  have := D0.isLocallyNoetherian
  have := D0.isDominant
  have hcomp : ∀ a : Z.presheaf.stalk (fp (D0.f D0.E.genericPoint)),
      w (functionFieldMap π (algebraMap _ Z.functionField a)) =
        D0.valuation (algebraMap _ X'.functionField
          ((fp.stalkMap (D0.f D0.E.genericPoint)).hom a)) := fun a => by
    have h1 := congrArg (fun u => u (algebraMap _ Z.functionField a)) hw
    simp only [Valuation.comap_apply] at h1
    rw [h1, MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hle1 : ∀ a : Z.presheaf.stalk (fp (D0.f D0.E.genericPoint)),
      w (functionFieldMap π (algebraMap _ Z.functionField a)) ≤ 1 := fun a => by
    rw [hcomp]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D0 _ rfl _
  have hlt1 : ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk (fp (D0.f D0.E.genericPoint))),
      w (functionFieldMap π (algebraMap _ Z.functionField a)) < 1 := fun a ha => by
    rw [hcomp]
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D0 _ rfl _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
  obtain ⟨x₁, -, hx1, hx2⟩ := MMP.Mori.exists_map_eq_and_dominates_of_isProper hZ π hM
    w.valuationSubring (fun c => by
      rw [Valuation.mem_valuationSubring_iff]
      by_cases hc : c = 0
      · simp [hc]
      · exact (hk c hc).le) _
    (fun a => by
      rw [ValuationSubring.valuation_le_one_iff, Valuation.mem_valuationSubring_iff]
      exact hle1 a)
    (fun a ha => by
      rw [← (Valuation.isEquiv_valuation_valuationSubring w).lt_one_iff_lt_one]
      exact hlt1 a ha)
  refine MMP.Mori.DivisorOver.exists_isProper_valuation_eq_of_trdeg_residueField hM w hsurj hk
    htr x₁ (fun a => ?_) (fun a ha => ?_)
  · have := hx1 a
    rwa [ValuationSubring.valuation_le_one_iff, Valuation.mem_valuationSubring_iff] at this
  · have := hx2 a ha
    rwa [← (Valuation.isEquiv_valuation_valuationSubring w).lt_one_iff_lt_one] at this

section Lift

variable {A B : Scheme.{0}} [IsIntegral A] [IsIntegral B] (g : A ⟶ B) [IsDominant g]

/-- The function-field map of a dominant morphism factoring as `g ≫ h` is the composite of the
function-field maps of `h` and `g`. -/
private theorem functionFieldMap_apply_of_eq_comp {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] {a : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z} [IsDominant a] [IsDominant g]
    [IsDominant h] (e : a = g ≫ h) (t : Z.functionField) :
    functionFieldMap a t = functionFieldMap g (functionFieldMap h t) := by
  subst e
  exact (functionFieldMap_functionFieldMap_apply ..).symm

/-- A valuation of `k(A)` is determined by its restriction to `k(B)`, `g` birational. -/
private theorem valuation_eq_of_comap_eq (hg : Function.Bijective (functionFieldMap g))
    {w w' : Valuation A.functionField ℤᵐ⁰}
    (h : w.comap (functionFieldMap g) = w'.comap (functionFieldMap g)) : w = w' := by
  ext x
  obtain ⟨y, rfl⟩ := hg.2 x
  exact congrArg (fun u => u y) h

/-- A valuation of `k(B)` lifts to a valuation of `k(A)`, `g` birational. -/
private theorem exists_comap_eq (hg : Function.Bijective (functionFieldMap g))
    (u : Valuation B.functionField ℤᵐ⁰) :
    ∃ w : Valuation A.functionField ℤᵐ⁰, w.comap (functionFieldMap g) = u := by
  refine ⟨u.comap (RingEquiv.ofBijective (functionFieldMap g) hg).symm.toRingHom, ?_⟩
  ext y
  have : (RingEquiv.ofBijective (functionFieldMap g) hg).symm (functionFieldMap g y) = y :=
    (RingEquiv.ofBijective (functionFieldMap g) hg).symm_apply_apply y
  simp [Valuation.comap_apply, this]

end Lift

/-- A valuation of `k(X_i)` in the extracted set `I` is not transported to a valuation of
`k(X_{i+1})` with centre `V` of minimal log discrepancy greater than one. -/
private theorem false_of_isTransportedValuation {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I}
    {J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
    (β : TerminalBridge i J J')
    {V : IrreducibleCloseds (T.X (i + 1))}
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (D0 : MMP.Mori.DivisorOver ℂ (T.sX (i + 1))) (hD0 : D0.valuation = v) (hcV : D0.center = V)
    {s : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))} (hs : s ∈ I)
    (ht : T.IsTransportedValuation i s v) : False := by
  have hs' : s ∈ T.stableLowDiscrepancySetAt i := by
    rwa [← β.coe_source]
  obtain ⟨ξ, hξ, hcorr⟩ := hs'
  have hv_corr : T.Corresponds (i + 1) ξ v := ⟨s, hcorr, ht⟩
  have hlow : v ∈ T.lowDiscrepancySetAt (i + 1) := by
    rw [T.isStabilizedSmallKltTail.lowDiscrepancySetAt_eq (i + 1)]
    exact ⟨ξ, hξ, hv_corr⟩
  obtain ⟨-, a, ⟨n, D', hp', hv', hla⟩, ha⟩ := hlow
  have hX := (T.isFourfoldStepDiagram i).isNormalVariety_plus.1
  have hc : D'.center = V := by
    rw [← hcV]
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX (hv'.trans hD0.symm)
  have hclosure : closure {V.isIrreducible.genericPoint} = (V : Set (T.X (i + 1))) :=
    IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed
  have hle : minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint ≤
      (a : EReal) :=
    sInf_le ⟨n, D', a, hla, by rw [hclosure, hc], rfl⟩
  have : (a : EReal) ≤ 1 := mod_cast ha
  exact absurd (hmld.trans_le (hle.trans this)) (lt_irrefl _)

/-- `v` has centre `V` of codimension two on `X_{i+1}`: it is exceptional there. -/
private theorem isExceptionalValuation_surface {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsVariety ℂ sX) {V : IrreducibleCloseds X}
    {v : Valuation X.functionField ℤᵐ⁰} (h4 : topologicalKrullDim X = 4)
    (h2 : topologicalKrullDim (V : Set X) = 2) (hc : MMP.Intersection.IsCentre ℂ sX v V) :
    MMP.Intersection.IsExceptionalValuation ℂ sX v := by
  obtain ⟨D, hp, hv, hVD⟩ := hc
  refine ⟨D, hp, hv, ?_⟩
  have := hX.toLocallyOfFiniteType
  rw [MMP.Positivity.DivisorOver.codimension_center]
  have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  have hcl : (closure {D.f D.E.genericPoint} : Set X) = (V : Set X) := by
    rw [← D.center_eq_closure_genericPoint, hVD]
  rw [hcl, h2, h4] at h3
  induction hco : Order.coheight (D.f D.E.genericPoint) using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    rw [hco] at h3
    have h5 : ((2 + n : ℕ∞) : WithBot ℕ∞) = ((4 : ℕ∞) : WithBot ℕ∞) := by
      rwa [WithBot.coe_add]
    have h6 : (2 + n : ℕ∞) = 4 := WithBot.coe_injective h5
    have h7 : (2 + n : ℕ) = 4 := mod_cast h6
    exact_mod_cast (by omega : 2 ≤ n)

/-- A prime divisor whose image has coheight at least two is exceptional. -/
private theorem isExceptional_of_two_le_coheight {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)]
    (f : X ⟶ Y) (E : MMP.Mori.PrimeDivisor X) (h : 2 ≤ Order.coheight (f E.genericPoint)) :
    MMP.Mori.RationalMap.IsExceptional (X := X) f.toRationalMap E := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  have h1 : (E.idealSheaf.support : Set X) = closure {E.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure E
  have h2 : x ∈ closure {f E.genericPoint} := by
    have := image_closure_subset_closure_image (f := f) f.continuous (s := {E.genericPoint})
    rw [Closeds.coe_closure, h1] at hx
    have hx' : x ∈ closure (f '' {E.genericPoint}) := closure_minimal this isClosed_closure hx
    rwa [Set.image_singleton] at hx'
  refine h.trans ?_
  exact Order.coheight_anti (α := Y) (a := x) (b := f E.genericPoint)
    (specializes_iff_mem_closure.2 h2)

/-- The base case: the models `V_0 = Y_i`. -/
private theorem base_exceptional
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I}
    {J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
    (β : TerminalBridge i J J')
    {V : IrreducibleCloseds (T.X (i + 1))}
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation (T.sX (i + 1)) V v)
    [IsDominant (J.p ≫ T.f i)]
    (w : Valuation J.Y.functionField (WithZero (Multiplicative ℤ)))
    (hw : w.comap (functionFieldMap (J.p ≫ T.f i)) = v.comap (functionFieldMap (T.fp i))) :
    MMP.Intersection.IsExceptionalValuation ℂ J.sY w := by
  have Sd := T.isFourfoldStepDiagram i
  have hfsm : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfpsm := T.isSmallMorphism_fp i
  obtain ⟨D0, hp0, hv0, hc0⟩ := hv.2.2.2.2.1
  have hexX' : MMP.Intersection.IsExceptionalValuation ℂ (T.sX (i + 1)) v :=
    isExceptionalValuation_surface Sd.isNormalVariety_plus.1 hv.2.1 hv.2.2.1 hv.2.2.2.2.1
  have := hfpsm.isProper
  have := Sd.isNormalVariety_plus.1
  have := Sd.isNormalVariety_target.1
  have := Sd.isNormalVariety_minus.1
  have hdimfp : topologicalKrullDim (T.X (i + 1)) = topologicalKrullDim (T.Z i) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (T.sZ i)
      (T.sX (i + 1)) hfpsm.isBirationalMorphism).symm
  have hexZ : MMP.Intersection.IsExceptionalValuation ℂ (T.sZ i)
      (v.comap (functionFieldMap (T.fp i))) :=
    isExceptionalValuation_comap Sd.isNormalVariety_plus Sd.isNormalVariety_target (T.fp i)
      Sd.comp_eq_plus hfpsm.isBirationalMorphism hdimfp hexX'
  have := hfsm.isProper
  have := J.isBirationalMorphism.isDominant
  set wX : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)) :=
    w.comap (functionFieldMap J.p) with hwXdef
  have hwX : wX.comap (functionFieldMap (T.f i)) = v.comap (functionFieldMap (T.fp i)) := by
    rw [← hw]
    ext x
    simp only [hwXdef, Valuation.comap_apply]
    rw [functionFieldMap_functionFieldMap_apply]
  obtain ⟨DX, hpX, hDX⟩ := exists_divisorOver_of_comap_eq Sd.isNormalVariety_target.1
    Sd.isNormalVariety_minus.1 Sd.isNormalVariety_plus.1 (T.f i) Sd.comp_eq_minus
    hfsm.isBirationalMorphism.functionFieldMap_bijective (T.fp i) Sd.comp_eq_plus
    hfpsm.isBirationalMorphism D0 wX
    (by rw [hwX, hv0])
  have hexXi : MMP.Intersection.IsExceptionalValuation ℂ (T.sX i) wX :=
    isExceptionalValuation_of_comap Sd.isNormalVariety_minus Sd.isNormalVariety_target (T.f i)
      Sd.comp_eq_minus hfsm.isBirationalMorphism hfsm.two_le_codimension
      ⟨DX, hpX, hDX.symm⟩ (by rw [hwX]; exact hexZ)
  have hYn : MMP.Mori.IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have : IsProper J.p := isProper_of_isProjectiveMorphism J.p J.isProjectiveMorphism
  have := hYn.1
  obtain ⟨DY, hpY, hDY⟩ := exists_divisorOver_of_comap_eq Sd.isNormalVariety_target.1 hYn.1
    Sd.isNormalVariety_plus.1 (J.p ≫ T.f i)
    (by rw [Category.assoc, Sd.comp_eq_minus])
    (isBirationalMorphism_comp Sd.isNormalVariety_minus Sd.isNormalVariety_target (T.f i)
      hfsm.isBirationalMorphism J.p J.isBirationalMorphism).functionFieldMap_bijective (T.fp i)
    Sd.comp_eq_plus
    hfpsm.isBirationalMorphism D0 w (by rw [hw, hv0])
  refine ⟨DY, hpY, hDY.symm, ?_⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hYn]
  intro P hP
  have hwP : ∀ g, w g = P.divisorialValuation g := fun g => by
    have := congrArg (fun u => u g) hP
    rw [hDY] at this
    rw [this]
    change P.divisorialValuation (functionFieldMap (𝟙 _) g) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  let DP : MMP.Mori.DivisorOver ℂ (T.sX i) :=
    ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, P⟩
  have hDP : DP.valuation = wX := by
    ext x
    change P.valuationOver J.p x = w (functionFieldMap J.p x)
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, hwP]
  by_cases hex : MMP.Mori.RationalMap.IsExceptional (X := J.Y) J.p.toRationalMap P
  · obtain ⟨s, hsP⟩ := (J.isExceptional_iff P).1 hex
    have hs : (s : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))) = wX := by
      rw [← J.valuation_eq s, ← hDP]
      subst hsP
      rfl
    refine false_of_isTransportedValuation β hmld D0 hv0.symm hc0.symm s.2 ?_
    rw [StepSequence.IsTransportedValuation, ← hwX, hs]
  · obtain ⟨DX', hpX', hvX', hcX'⟩ := hexXi
    have heq := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq
      Sd.isNormalVariety_minus.1 (D := DP) (D' := DX') (hDP.trans hvX')
    rw [MMP.Positivity.DivisorOver.codimension_center, ← heq] at hcX'
    have : IsSeparated (T.sX i) := Sd.isNormalVariety_minus.1.toIsSeparated
    have hsep : IsSeparated (T.X i ↘ ⊤_ Scheme) := by
      rw [show (T.X i ↘ ⊤_ Scheme) = T.sX i ≫ Limits.terminal.from (Spec (.of ℂ)) from
        Subsingleton.elim _ _]
      infer_instance
    exact hex (isExceptional_of_two_le_coheight J.p P hcX')

/-- **Exceptionality is transported along a flip** `V ⟶ T ⟵ W` of small morphisms. -/
private theorem exceptional_of_flip {V W Tt Z : Scheme.{0}} [IsIntegral V] [IsIntegral W]
    [IsIntegral Tt] [IsIntegral Z] {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    {sT : Tt ⟶ Spec (.of ℂ)} (g : V ⟶ Tt) (gp : W ⟶ Tt) (h : Tt ⟶ Z) [IsDominant h]
    (hh : Function.Bijective (functionFieldMap h))
    (hg : IsSmallMorphism sV sT g) (hgp : IsSmallMorphism sW sT gp)
    {wV : Valuation V.functionField ℤᵐ⁰} {wW : Valuation W.functionField ℤᵐ⁰}
    [IsDominant g] [IsDominant gp]
    (hcompat : (wV.comap (functionFieldMap g)).comap (functionFieldMap h) =
      (wW.comap (functionFieldMap gp)).comap (functionFieldMap h))
    (hexV : MMP.Intersection.IsExceptionalValuation ℂ sV wV)
    (hD : MMP.Intersection.IsNormalizedDivisorialValuation ℂ sW wW) :
    MMP.Intersection.IsExceptionalValuation ℂ sW wW := by
  have heq := valuation_eq_of_comap_eq h hh hcompat
  have := hg.isProper
  have := hgp.isProper
  have := hg.isNormalVariety_source.1
  have := hg.isNormalVariety_target.1
  have := hgp.isNormalVariety_source.1
  have hdim1 : topologicalKrullDim V = topologicalKrullDim Tt :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT sV
      hg.isBirationalMorphism).symm
  have h1 := isExceptionalValuation_comap hg.isNormalVariety_source hg.isNormalVariety_target g
    hg.comp_eq hg.isBirationalMorphism hdim1 hexV
  rw [heq] at h1
  exact isExceptionalValuation_of_comap hgp.isNormalVariety_source hgp.isNormalVariety_target gp
    hgp.comp_eq hgp.isBirationalMorphism hgp.two_le_codimension hD h1

/-- The models `V_k`, `k ≤ m`, of the program of the bridge (with `V_0 = Y_i`). -/
private theorem models_exceptional
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I}
    {J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
    (β : TerminalBridge i J J')
    {V : IrreducibleCloseds (T.X (i + 1))}
    (_hV : (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i)
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation (T.sX (i + 1)) V v) :
    ∀ k ≤ β.P.m, ∃ _ : IsDominant (β.P.toBase k),
      ∀ v' : Valuation (β.P.model k).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap (β.P.toBase k)) = v.comap (functionFieldMap (T.fp i)) →
          MMP.Intersection.IsExceptionalValuation ℂ (β.P.modelStructure k) v' := by
  have Sd := T.isFourfoldStepDiagram i
  obtain ⟨D0, hp0, hv0, hc0⟩ := hv.2.2.2.2.1
  have key : ∀ k, k ≤ β.P.m → ∃ hd : IsDominant (β.P.toBase k),
      Function.Bijective (functionFieldMap (β.P.toBase k)) ∧ IsProper (β.P.toBase k) ∧
      ∀ v' : Valuation (β.P.model k).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap (β.P.toBase k)) = v.comap (functionFieldMap (T.fp i)) →
          MMP.Intersection.IsExceptionalValuation ℂ (β.P.modelStructure k) v' := by
    intro k
    induction k with
    | zero =>
      intro _
      have hfsm : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
        T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
      have := hfsm.isProper
      have : IsProper J.p := isProper_of_isProjectiveMorphism J.p J.isProjectiveMorphism
      have := J.isBirationalMorphism.isDominant
      have hb := isBirationalMorphism_comp Sd.isNormalVariety_minus Sd.isNormalVariety_target
        (T.f i) hfsm.isBirationalMorphism J.p J.isBirationalMorphism
      have : IsDominant (J.p ≫ T.f i) := hb.isDominant
      refine ⟨inferInstanceAs (IsDominant (J.p ≫ T.f i)), hb.functionFieldMap_bijective,
        inferInstanceAs (IsProper (J.p ≫ T.f i)), fun w hw => ?_⟩
      exact base_exceptional β hmld hv w hw
    | succ k ih =>
      intro hk
      have hk' : k < β.P.m := hk
      obtain ⟨hd, hbij, hprop, hexc⟩ := ih (Nat.le_of_succ_le hk)
      have Sk := β.P.isFourfoldStepDiagram k hk'
      have hgs : IsSmallMorphism (β.P.modelStructure k) (β.P.sT k) (β.P.g k) :=
        β.isSmallMorphism k hk'
      have hgps : IsSmallMorphism (β.P.sY k) (β.P.sT k) (β.P.gp k) := Sk.isSmallMorphism_plus
      have := Sk.isNormalVariety_target.1.toIsIntegral
      have hm1 : β.P.toBase k = β.P.g k ≫ β.P.h k := β.P.modelMap_eq k hk'
      have hm2 : β.P.toBase (k + 1) = β.P.gp k ≫ β.P.h k := β.P.πY_eq k hk'
      have : IsDominant (β.P.g k) := hgs.isBirationalMorphism.isDominant
      have : IsDominant (β.P.gp k) := hgps.isBirationalMorphism.isDominant
      have hbg := hgs.isBirationalMorphism.functionFieldMap_bijective
      have hbgp := hgps.isBirationalMorphism.functionFieldMap_bijective
      have : IsDominant (β.P.g k ≫ β.P.h k) := hm1 ▸ hd
      have := IsDominant.of_comp (β.P.g k) (β.P.h k)
      have hcomp1 := functionFieldMap_apply_of_eq_comp hm1
      have hbh : Function.Bijective (functionFieldMap (β.P.h k)) :=
        (Function.Bijective.of_comp_iff' hbg _).1 (by rwa [Function.comp_def, ← funext hcomp1])
      -- `β.P.model (k + 1)` and `β.P.Y k` agree only up to unfolding, hence the explicit `@`.
      have hdomc : @IsDominant (β.P.model (k + 1)) (T.Z i) (β.P.gp k ≫ β.P.h k) :=
        (inferInstance : IsDominant (β.P.gp k ≫ β.P.h k))
      have hdom2 : IsDominant (β.P.toBase (k + 1)) := by
        rw [hm2]
        exact hdomc
      have hcomp2 : ∀ t, functionFieldMap (β.P.toBase (k + 1)) t =
          functionFieldMap (β.P.gp k) (functionFieldMap (β.P.h k) t) := fun t => by
        rw [functionFieldMap_functionFieldMap_apply]
        exact congrFun (congrArg DFunLike.coe (@functionFieldMap_congr (β.P.model (k + 1))
          (T.Z i) _ _ (β.P.toBase (k + 1)) (β.P.gp k ≫ β.P.h k) hdom2 hdomc hm2)) t
      have hbij2 : Function.Bijective (functionFieldMap (β.P.toBase (k + 1))) := by
        rw [funext hcomp2]; exact hbgp.comp hbh
      have hprop2 : IsProper (β.P.toBase (k + 1)) := by
        rw [hm2]
        exact MorphismProperty.comp_mem _ _ _ hgps.isProper
          (isProper_of_isProjectiveMorphism _ (β.P.isProjectiveMorphism_base k hk'))
      refine ⟨hdom2, hbij2, hprop2, fun v' hv' => ?_⟩
      obtain ⟨wk, hwk⟩ := exists_comap_eq (β.P.g k) hbg (v'.comap (functionFieldMap (β.P.gp k)))
      have hcompat_k : wk.comap (functionFieldMap (β.P.toBase k)) =
          v.comap (functionFieldMap (T.fp i)) := by
        rw [← hv']
        ext t
        simp only [Valuation.comap_apply]
        rw [hcomp1, hcomp2]
        exact congrArg (fun u => u (functionFieldMap (β.P.h k) t)) hwk
      have hexk := hexc wk hcompat_k
      have hfpsm := T.isSmallMorphism_fp i
      have hπ : β.P.toBase (k + 1) ≫ T.sZ i = β.P.sY k := by
        rw [hm2]
        calc (β.P.gp k ≫ β.P.h k) ≫ T.sZ i = β.P.gp k ≫ (β.P.h k ≫ T.sZ i) := Category.assoc _ _ _
          _ = β.P.gp k ≫ β.P.sT k := by rw [β.P.comp_eq_base k hk']
          _ = β.P.sY k := Sk.comp_eq_plus
      obtain ⟨DY, hpY, hDY⟩ := exists_divisorOver_of_comap_eq (M := β.P.model (k + 1))
        (sM := β.P.modelStructure (k + 1)) Sd.isNormalVariety_target.1
        hgps.isNormalVariety_source.1 Sd.isNormalVariety_plus.1 (β.P.toBase (k + 1)) hπ hbij2
        (T.fp i) Sd.comp_eq_plus hfpsm.isBirationalMorphism D0 v' (by rw [hv', hv0])
      exact exceptional_of_flip (β.P.g k) (β.P.gp k) (β.P.h k) hbh hgs hgps
        (by rw [hwk]) hexk ⟨DY, hpY, hDY.symm⟩
  intro k hk
  obtain ⟨hd, -, -, h⟩ := key k hk
  exact ⟨hd, h⟩

/-- The end junction `Y_{i+1}` of the bridge. -/
private theorem target_exceptional
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I}
    {J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
    (β : TerminalBridge i J J')
    {V : IrreducibleCloseds (T.X (i + 1))}
    (hV : (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i)
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation (T.sX (i + 1)) V v) :
    haveI := J'.isBirationalMorphism.isDominant
    ∀ v' : Valuation J'.Y.functionField (WithZero (Multiplicative ℤ)),
      v'.comap (functionFieldMap (J'.p ≫ T.fp i)) = v.comap (functionFieldMap (T.fp i)) →
        MMP.Intersection.IsExceptionalValuation ℂ J'.sY v' := by
  have := J'.isBirationalMorphism.isDominant
  intro v' hv'
  obtain ⟨_, H⟩ := models_exceptional β hV hmld hv β.P.m le_rfl
  have hw := H (v'.comap (functionFieldMap β.e.inv)) (by
    ext t
    simp only [Valuation.comap_apply]
    rw [functionFieldMap_congr β.toBase_end_eq, ← functionFieldMap_functionFieldMap_apply,
      functionFieldMap_functionFieldMap_apply β.e.inv, functionFieldMap_congr β.e.inv_hom_id,
      MMP.Mori.functionFieldMap_id_apply, ← Valuation.comap_apply, hv', Valuation.comap_apply])
  have := isExceptionalValuation_comap_functionFieldMap_hom β.e β.comp_sY hw
  convert this using 1
  ext y
  simp only [Valuation.comap_apply]
  rw [functionFieldMap_functionFieldMap_apply β.e.inv, functionFieldMap_congr β.e.inv_hom_id,
    MMP.Mori.functionFieldMap_id_apply]

/-- Let `T` be a stabilized small klt tail, `β` a terminal bridge from a crepant junction
`p_i : Y_i ⟶ X_i` to a crepant junction `p_{i+1} : Y_{i+1} ⟶ X_{i+1}`, `V` an irreducible
closed subset of `X_{i+1}` contained in the bad locus `W_i⁺` with
`mld_{η_V}(X_{i+1}, B_{i+1}) > 1`, and `v` the generic blowup valuation of the surface `V`
(`MMP.Fourfold.IsSurfaceGenericBlowupValuation`). Then `v` is exceptional over every model of
the bridge: over each model `V_k`, `k ≤ m`, of its relative program (with `V_0 = Y_i`) and over
`Y_{i+1}`, in the sense that every valuation of the function field of the model with the same
restriction to `k(Z_i)` as `v` is exceptional (`MMP.Intersection.IsExceptionalValuation`). -/
@[mmp "lem_oai4_c3_unit_drop_exceptional"]
public theorem isExceptionalValuation_of_isSurfaceGenericBlowupValuation
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I}
    {J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
    (β : TerminalBridge i J J')
    {V : IrreducibleCloseds (T.X (i + 1))}
    (hV : (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i)
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation (T.sX (i + 1)) V v) :
    (∀ k ≤ β.P.m, ∃ _ : IsDominant (β.P.toBase k),
      ∀ v' : Valuation (β.P.model k).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap (β.P.toBase k)) = v.comap (functionFieldMap (T.fp i)) →
          MMP.Intersection.IsExceptionalValuation ℂ (β.P.modelStructure k) v') ∧
    haveI := J'.isBirationalMorphism.isDominant
    ∀ v' : Valuation J'.Y.functionField (WithZero (Multiplicative ℤ)),
      v'.comap (functionFieldMap (J'.p ≫ T.fp i)) = v.comap (functionFieldMap (T.fp i)) →
        MMP.Intersection.IsExceptionalValuation ℂ J'.sY v' :=
  ⟨models_exceptional β hV hmld hv, target_exceptional β hV hmld hv⟩

end MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge
