module

public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical

/-!
# Discrepancies are local

Let `(X, Δ)` be a pair over a field `k`, with canonical divisor `K` of dimension `n`, let
`U ⊆ X` be open and let `(Y, f, E)` be a divisor over `X` whose center meets `U`. Then `f(η_E)`
lies in `U`, so `η_E ∈ f⁻¹(U)` and `E ∩ f⁻¹(U)` is a prime divisor `E_U` of the normal variety
`f⁻¹(U)`, with the same generic point and local ring. Hence `(f⁻¹(U), f|_{f⁻¹(U)}, E_U)` is a
divisor over `U` with the same valuation as `E`, and the discrepancies agree:
`a(E, X, Δ) = a(E_U, U, Δ|_U)`, where `U` has canonical divisor `K|_U`.

Conversely, a divisor `(Y, f, E)` over a nonempty open `U` is the divisor `(Y, f, E)` over `X`,
exceptional exactly when it is exceptional over `U`, since both say that `f(η_E)` has codimension
at least two. So `discrep(X, Δ) ≤ discrep(U, Δ|_U)`, and terminal, canonical, plt, klt and lc pairs
restrict to pairs of the same kind on every nonempty open subscheme. More generally, for nonempty
opens `V ⊆ U ⊆ X`, `discrep(U, Δ|_U) ≤ discrep(V, Δ|_V)`, so a pair of each kind on `U` restricts
to one on `V`.

## Main results

* `MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff`
* `MMP.Mori.isBirationalMorphism_morphismRestrict`: the restriction of a birational morphism of
  integral schemes over an open set with nonempty preimage is birational
* `MMP.Mori.IsNormalVariety.restrictOpen`, `MMP.Mori.Divisor.IsCanonicalDivisor.restrictOpen`:
  a nonempty open subscheme of a normal variety is a normal variety, and the restriction of a
  canonical divisor to it is canonical
* `MMP.Mori.IsPairWith.exists_isDiscrepancy_of_restrictOpen`: an exceptional divisor over a
  nonempty open `U ⊆ X` is an exceptional divisor over `X` with the same discrepancy
* `MMP.Mori.IsPairWith.restrictOpen`, `MMP.Mori.discrep_le_discrep_restrictOpen`,
  `MMP.Mori.discrep_restrictOpen_le_discrep_restrictOpen`
* `MMP.Mori.IsTerminalPair.restrictOpen`, `MMP.Mori.IsCanonicalPair.restrictOpen`,
  `MMP.Mori.IsPltPair.restrictOpen`, `MMP.Mori.IsKltPair.restrictOpen`,
  `MMP.Mori.IsLcPair.restrictOpen`, and their analogues `MMP.Mori.IsPltPair.mono_opens` etc. for
  opens `V ⊆ U`

## Implementation notes

The restricted divisor is `(f⁻¹ᵁ U, f ∣_ U, E_U)`, where `E_U` is the prime divisor of `f⁻¹ᵁ U`
carried to `E` by `AlgebraicGeometry.OpenWeilRestriction.primeDivisorMap`, which determines it.
Its valuation is a valuation of `k(U)`; it agrees with `v_E` through the identification
`k(X) ≅ k(U)` given by `AlgebraicGeometry.functionFieldMap` of the inclusion `U ⟶ X`. The
discrepancy is the predicate `MMP.Mori.IsDiscrepancy` on its value, so the equality of
discrepancies is stated as: a rational number is the discrepancy of `E` over `(X, Δ)` if and only
if it is the discrepancy of `E_U` over `(U, Δ|_U)`. The field `k` is assumed perfect, which makes
the discrepancy unique (`MMP.Mori.IsDiscrepancy.eq`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.29–2.31
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.Mori.DivisorOver

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- `f(η_E)` lies in every open set meeting the center of `E`. -/
private theorem map_genericPoint_mem (D : DivisorOver k sX) {U : X.Opens}
    (hU : ((D.center : Set X) ∩ U).Nonempty) : D.f D.E.genericPoint ∈ U := by
  obtain ⟨x, hx, hxU⟩ := hU
  rw [D.center_eq_closure_genericPoint, mem_closure_iff] at hx
  obtain ⟨y, hyU, rfl⟩ := hx U U.isOpen hxU
  exact hyU

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- `E ∩ f⁻¹(U)` has the generic point of `E`. -/
private theorem ι_genericPoint_eq (D : DivisorOver k sX) (U : X.Opens)
    (E' : Mori.PrimeDivisor (D.f ⁻¹ᵁ U).toScheme)
    (hE' : OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E) :
    (D.f ⁻¹ᵁ U).ι E'.genericPoint = D.E.genericPoint := by
  rw [← hE']
  exact (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
theorem _root_.MMP.Mori.IsNormalVariety.restrictOpen {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The restriction `f ∣_ U` of a birational morphism of integral schemes over an open set
`U` whose preimage is nonempty is birational. -/
theorem _root_.MMP.Mori.isBirationalMorphism_morphismRestrict {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] {f : Y ⟶ X} (hf : IsBirationalMorphism f) (U : X.Opens)
    [Nonempty (f ⁻¹ᵁ U)] : IsBirationalMorphism (f ∣_ U) := by
  obtain ⟨W, hWne, hW⟩ := hf.exists_isOpenImmersion
  let S : (f ⁻¹ᵁ U).toScheme.Opens := (f ⁻¹ᵁ U).ι ⁻¹ᵁ W
  have hSne : (S : Set (f ⁻¹ᵁ U)).Nonempty := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty (f ⁻¹ᵁ U)›
    obtain ⟨z, hzU, hzW⟩ :=
      (W.isOpen.dense hWne).inter_open_nonempty _ (f ⁻¹ᵁ U).isOpen ⟨y, hy⟩
    exact ⟨⟨z, hzU⟩, hzW⟩
  have hS : Dense (S : Set (f ⁻¹ᵁ U)) := S.isOpen.dense hSne
  have : Nonempty S := hSne.to_subtype
  have hrange : Set.range (S.ι ≫ (f ⁻¹ᵁ U).ι) ⊆ Set.range W.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let h := IsOpenImmersion.lift W.ι (S.ι ≫ (f ⁻¹ᵁ U).ι) hrange
  let g : S.toScheme ⟶ U := S.ι ≫ (f ∣_ U)
  have hg : g ≫ U.ι = h ≫ W.ι ≫ f := by
    simp only [g, h, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc]
  have : IsOpenImmersion (g ≫ U.ι) := by
    rw [hg]
    infer_instance
  have : IsOpenImmersion g := IsOpenImmersion.of_comp g U.ι
  have : IsDominant g := by
    have : Nonempty U := ⟨g (Classical.arbitrary S)⟩
    exact ⟨IsOpen.dense (X := U.toScheme) g.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)⟩
  have hd : Dense (g.opensRange : Set U) := g.denseRange
  have hgdef : g = S.ι ≫ f ∣_ U := rfl
  clear_value g
  refine ⟨⟨S, hS, g.opensRange, hd, g.isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨S, hS, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι, hgdef, Scheme.topIso_hom]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.homOfLE_ι_assoc _ _ _).symm

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
  rw [Valuation.comap_apply, Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).2 hg),
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- `E` and `E ∩ f⁻¹(U)` have the same valuation. -/
private theorem valuation_eq_comap (D : DivisorOver k sX) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] (hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX))
    (hf : IsBirationalMorphism (D.f ∣_ U)) (E' : Mori.PrimeDivisor (D.f ⁻¹ᵁ U).toScheme)
    (hE' : OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E) :
    D.valuation =
      (DivisorOver.valuation (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX))).comap
        (functionFieldMap U.ι) := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := hY.isIntegral
  have := hY.isNormal
  have := hY.isLocallyNoetherian
  have : IsDominant (D.f ∣_ U) := hf.isDominant
  have := isDominant_opens_ι (D.f ⁻¹ᵁ U)
  ext g
  change D.E.divisorialValuation (functionFieldMap D.f g) =
    E'.divisorialValuation (functionFieldMap (D.f ∣_ U) (functionFieldMap U.ι g))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr (morphismRestrict_ι D.f U),
    ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, ← hE',
    divisorialValuation_primeDivisorMap]
  rfl

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

/-- On an integral scheme the generic point of every irreducible component is the generic
point. -/
private theorem componentGenericPoint_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z = genericPoint Y := by
  have h1 := isGenericPoint_componentGenericPoint Y Z
  rw [eq_univ_of_irreducibleComponents Z] at h1
  exact h1.eq (genericPoint_spec Y)

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
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
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

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) := by
  rw [Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation, evFF,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, -⟩ := h
  exact ((genericPoint_spec U.toScheme).specializes trivial).mem_open V.isOpen hx

/-- The irreducible component `X` of the integral scheme `X`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF,
      evFF_restrictRF U V ψ _ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← Mori.PrimeDivisor.genericPoint_mem_iff, ← Mori.PrimeDivisor.genericPoint_mem_iff,
      show Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · exact Subtype.ext (restrictRF_injective U V (congrArg Subtype.val h))
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- The smooth locus of an open subscheme `U ⊆ X` lies in the smooth locus of `X`. -/
private theorem range_smoothLocus_subset (U : X.Opens) :
    Set.range ((smoothLocus (U.ι ≫ sX)).ι ≫ U.ι) ⊆ Set.range (smoothLocus sX).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 x.2
  let V := (W.ι ≫ U.ι).opensRange
  have e : (W.ι ≫ U.ι).isoOpensRange.inv ≫ (W.ι ≫ U.ι) = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sX) := by
    rw [← e, Category.assoc, Category.assoc]
    infer_instance
  exact le_smoothLocus sX hV ⟨⟨x.1, hxW⟩, rfl⟩

/-- On the smooth locus of a nonempty open subscheme `U`, the divisorial sheaf of `K|_U` is the
canonical sheaf when that of `K` is on the smooth locus of `X`. -/
private theorem nonempty_restrict_smoothLocus_iso {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U] [IsDominant U.ι] :
    Nonempty ((Divisor.divisorialSheaf (K.restrictOpen U)).restrict (smoothLocus (U.ι ≫ sX)).ι ≅
      canonicalSheaf (U.ι ≫ sX) n) := by
  have := isIso_divisorialSheafRestrictHom U K
  let e₀ := (asIso (divisorialSheafRestrictHom U K)).symm
  let T := smoothLocus (U.ι ≫ sX)
  let S := smoothLocus sX
  let ψ : T.toScheme ⟶ S := IsOpenImmersion.lift S.ι (T.ι ≫ U.ι) (range_smoothLocus_subset U)
  have hψ : ψ ≫ S.ι = T.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso ψ (S.ι ≫ sX)
    (T.ι ≫ U.ι ≫ sX) (by rw [← Category.assoc, hψ, Category.assoc]) n
  exact ⟨(Scheme.Modules.restrictFunctor T.ι).mapIso e₀ ≪≫
    (Scheme.Modules.restrictFunctorComp T.ι U.ι).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

/-- The restriction of a canonical divisor to a nonempty open subscheme is canonical. -/
theorem _root_.MMP.Mori.Divisor.IsCanonicalDivisor.restrictOpen {n : ℕ} {K : Divisor X}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U] :
    Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (K.restrictOpen U) :=
  have := isDominant_opens_ι U
  ⟨(topologicalKrullDim_opens_eq hX U).trans hK.1, nonempty_restrict_smoothLocus_iso hK U⟩

/-- The closure in `X` of a prime divisor of `U` meeting `U ∩ V` meets `V`. -/
private theorem primeDivisorMap_support_inter_nonempty (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] {V : X.Opens} (W : Mori.PrimeDivisor U.toScheme)
    (hW : (W.support ∩ U.ι ⁻¹ᵁ V).Nonempty) :
    ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ V).Nonempty := by
  rw [← Mori.PrimeDivisor.genericPoint_mem_iff]
  exact (congrArg (· ∈ V) (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W)).mpr
    ((W.genericPoint_mem_iff _).2 hW)

/-- The restriction of a Cartier divisor to a dense open subscheme is Cartier: a local equation
`φ` of `D` on `V` gives the local equation `φ|_U` of `D|_U` on `U ∩ V`, since the closure in `X`
of a prime divisor of `U` has the same local ring. -/
private theorem isCartier_restrictOpen {D : Divisor X} (h : D.IsCartier) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : Divisor.IsCartier (D.restrictOpen U) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := h (U.ι x)
  obtain ⟨g, hg, hφg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap U.ι)).2 hg)
  refine ⟨U.ι ⁻¹ᵁ V, hxV, φ', fun W hW => ?_⟩
  rw [DivisorWithCoeffs.coeff_restrictOpen, hφ _ (primeDivisorMap_support_inter_nonempty U W hW),
    hφg, hφ',
    MMP.Positivity.ord_functionFieldMap_of_isIso U.ι W _
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- The restriction of a Cartier `ℚ`-divisor of the form `m(K + Δ)` is Cartier. -/
private theorem isCartierDivisor_smul_restrictOpen {K : Divisor X} {Δ : QDivisor X} {m : ℕ}
    (h : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    ((m : ℤ) • (Divisor.toQDivisor (K.restrictOpen U) + Δ.restrictOpen U)).IsCartierDivisor := by
  obtain ⟨D', hD', hC⟩ := h
  refine ⟨D'.restrictOpen U, ?_, isCartier_restrictOpen hC U⟩
  ext W
  simpa using congrArg
    (fun E => DivisorWithCoeffs.coeff E (OpenWeilRestriction.primeDivisorMap U.ι W)) hD'

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero [PerfectField k] [LocallyOfFiniteType sX]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- A form generating `𝒪_X(m(K + Δ))` on `V` restricts to a form generating
`𝒪_U(m(K|_U + Δ|_U))` on `U ∩ V`: a prime divisor of `U` and its closure in `X` have the same
local ring, so the orders of the form along them agree. -/
private theorem generatesOn_pullback_ι [PerfectField k] {n m : ℕ} {Δ : QDivisor X}
    (hX : IsNormalVariety k sX) (hn : topologicalKrullDim X = n) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] {V : X.Opens} {τ : RationalPluriForms sX n m}
    (hτ : GeneratesOn Δ m V τ) :
    GeneratesOn (Δ.restrictOpen U) m (U.ι ⁻¹ᵁ V) (pullbackRationalPluriForms sX U.ι τ) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := functionFieldMap_opens_ι_bijective U
  refine ⟨pullbackRationalPluriForms_ne_zero U.ι hbij hd hτ.1, fun W hW => ?_⟩
  rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso U.ι hbij hd W
    (OpenWeilRestriction.primeDivisorMap U.ι W)
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm τ,
    DivisorWithCoeffs.coeff_restrictOpen]
  exact hτ.2 _ (primeDivisorMap_support_inter_nonempty U W hW)

/-- Pulling a form back along `a : A ⟶ X` and then along `c : Z ⟶ A` is pulling it back along
`φ = c ≫ a`, when both induce isomorphisms of function fields; in particular the orders along a
prime divisor of `Z` agree. -/
private theorem ordForm_pullback_pullback [PerfectField k] [LocallyOfFiniteType sX]
    {A Z : Scheme.{u}} [IsIntegral A] [IsIntegral Z] [IsLocallyNoetherian Z]
    (a : A ⟶ X) (c : Z ⟶ A) [IsDominant a] [IsDominant c] [LocallyOfFiniteType (a ≫ sX)]
    (φ : Z ⟶ X) [IsDominant φ]
    (h : c ≫ a = φ) (hbija : Function.Bijective (functionFieldMap a))
    (hbijc : Function.Bijective (functionFieldMap c)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (E : Mori.PrimeDivisor Z) {m : ℤ} (τ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms (a ≫ sX) c (pullbackRationalPluriForms sX a τ)) =
      E.ordForm (pullbackRationalPluriForms sX φ τ) := by
  subst h
  have key : pullbackRationalPluriForms (a ≫ sX) c (pullbackRationalPluriForms sX a τ) =
      pullbackRationalPluriForms sX (c ≫ a) τ := by
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (a ≫ sX)
    let := functionFieldAlgebra (c ≫ a ≫ sX)
    let := functionFieldMapAlgebra a
    let := functionFieldMapAlgebra c
    let := functionFieldMapAlgebra (c ≫ a)
    have := isScalarTower_functionFieldMap sX a
    have := isScalarTower_functionFieldMap (a ≫ sX) c
    have : IsScalarTower k X.functionField Z.functionField :=
      isScalarTower_functionFieldMap sX (c ≫ a)
    have : IsScalarTower X.functionField A.functionField Z.functionField :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply c a x).symm
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX a hbija hd
    have hdA : (Algebra.trdeg k A.functionField).toNat = d := by
      rwa [← trdeg_functionField_eq_of_bijective sX a hbija]
    obtain ⟨ω₁, hω₁⟩ := exists_isPullbackGenerator_of_bijective (a ≫ sX) c hbijc hdA
    exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω
      (MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₁ hω.2.1 hω.2.2) τ
  exact congrArg E.ordForm key

/-- The pull-back of a form along `U ⊆ X` has the same order along `E ∩ f⁻¹(U)` as the form
along `E`. -/
private theorem ordPullback_pullback_ι [PerfectField k] {n m : ℕ} (hX : IsNormalVariety k sX)
    (hn : topologicalKrullDim X = n) (D : DivisorOver k sX)
    (U : X.Opens) [Nonempty U] [IsDominant U.ι] (hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX))
    (hf : IsBirationalMorphism (D.f ∣_ U)) (E' : Mori.PrimeDivisor (D.f ⁻¹ᵁ U).toScheme)
    (hE' : OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E)
    (τ : RationalPluriForms sX n m) :
    (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)).ordPullback
        (pullbackRationalPluriForms sX U.ι τ) = D.ordPullback τ := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := hY.isIntegral
  have := hY.isLocallyNoetherian
  have := hY.isNormal
  have : IsDominant (D.f ∣_ U) := hf.isDominant
  have := isDominant_opens_ι (D.f ⁻¹ᵁ U)
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbijf := D.isBirationalMorphism.functionFieldMap_bijective
  have hbijW := functionFieldMap_opens_ι_bijective (D.f ⁻¹ᵁ U)
  have hdY : letI := functionFieldAlgebra (D.f ≫ sX)
      (Algebra.trdeg k D.Y.functionField).toNat = n := by
    rwa [← trdeg_functionField_eq_of_bijective sX D.f hbijf]
  change E'.ordForm (pullbackRationalPluriForms (U.ι ≫ sX) (D.f ∣_ U)
      (pullbackRationalPluriForms sX U.ι τ)) = D.E.ordForm (pullbackRationalPluriForms sX D.f τ)
  rw [ordForm_pullback_pullback U.ι (D.f ∣_ U) ((D.f ⁻¹ᵁ U).ι ≫ D.f) (morphismRestrict_ι D.f U)
      (functionFieldMap_opens_ι_bijective U) hf.functionFieldMap_bijective hd,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso (D.f ⁻¹ᵁ U).ι hbijW hdY E' D.E
      (ι_genericPoint_eq D U E' hE') (pullbackRationalPluriForms sX D.f τ),
    ordForm_pullback_pullback D.f (D.f ⁻¹ᵁ U).ι _ rfl hbijf hbijW hd]

/-- A discrepancy of `E` over `(X, Δ)` is a discrepancy of `E ∩ f⁻¹(U)` over `(U, Δ|_U)`. -/
private theorem isDiscrepancy_restrict [PerfectField k] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (D : DivisorOver k sX) (U : X.Opens) [Nonempty U] [IsDominant U.ι]
    (hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX))
    (hf : IsBirationalMorphism (D.f ∣_ U)) (E' : Mori.PrimeDivisor (D.f ⁻¹ᵁ U).toScheme)
    (hE' : OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E)
    {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) :
    IsDiscrepancy (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)
      ⟨_, D.f ∣_ U, hY, hf, E'⟩ a := by
  obtain ⟨hX, hK, m, hm, hC, V, hV, τ, hτ, hτa⟩ := ha
  refine ⟨hX.restrictOpen U, hK.restrictOpen hX U, m, hm,
    isCartierDivisor_smul_restrictOpen hC U, U.ι ⁻¹ᵁ V, ?_, _,
    generatesOn_pullback_ι hX hK.1 U hτ,
    by rwa [ordPullback_pullback_ι hX hK.1 D U hY hf E' hE' τ]⟩
  change U.ι ((D.f ∣_ U) E'.genericPoint) ∈ V
  rwa [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
    ι_genericPoint_eq D U E' hE']

/-- **Discrepancies are local.** Let `(X, Δ)` be a pair with canonical divisor `K` of dimension
`n` over a perfect field, `U ⊆ X` open, and `(Y, f, E)` a divisor over `X` whose center meets
`U`. Then `(f⁻¹(U), f ∣_ U, E_U)` is a divisor over `U`, where `E_U` is the prime divisor
`E ∩ f⁻¹(U)` of `f⁻¹(U)`, characterised by having the same generic point as `E`. It has the same
valuation as `E`, and `a` is the discrepancy `a(E, X, Δ)` if and only if it is the discrepancy
`a(E_U, U, Δ|_U)`, for the canonical divisor `K|_U` of `U`. -/
@[mmp "lem_km2b_discrepancy_local"]
theorem exists_restrict_isDiscrepancy_iff [PerfectField k] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hΔ : IsPairWith sX n K Δ) (D : DivisorOver k sX) (U : X.Opens)
    (hU : ((D.center : Set X) ∩ U).Nonempty) :
    haveI : Nonempty U := ⟨⟨hU.choose, hU.choose_spec.2⟩⟩
    haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨hU.choose, hU.choose_spec.2⟩)
    ∃ (hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX))
      (hf : IsBirationalMorphism (D.f ∣_ U)) (E' : PrimeDivisor (D.f ⁻¹ᵁ U).toScheme),
      OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E ∧
      D.valuation =
        (DivisorOver.valuation (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX))).comap
          (functionFieldMap U.ι) ∧
      ∀ a : ℚ, IsDiscrepancy sX n K Δ D a ↔
        IsDiscrepancy (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)
          ⟨_, D.f ∣_ U, hY, hf, E'⟩ a := by
  have hη := map_genericPoint_mem D hU
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  haveI := isDominant_opens_ι U
  haveI : Nonempty (D.f ⁻¹ᵁ U) := ⟨⟨_, hη⟩⟩
  have := D.isIntegral
  have hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    exact D.isNormalVariety.restrictOpen _
  have hf := isBirationalMorphism_morphismRestrict D.isBirationalMorphism U
  obtain ⟨E', hE'⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff (D.f ⁻¹ᵁ U).ι D.E).2
    (by rwa [Scheme.Opens.range_ι])
  refine ⟨hY, hf, E', hE', valuation_eq_comap D U hY hf E' hE', fun a => ⟨fun ha =>
    isDiscrepancy_restrict D U hY hf E' hE' ha, fun ha => ?_⟩⟩
  obtain ⟨a₀, ha₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΔ.isPair hΔ.2.1 D
  rwa [ha.eq (isDiscrepancy_restrict D U hY hf E' hE' ha₀)]

end MMP.Mori.DivisorOver

/-! ### Singularities of pairs restrict to open subschemes -/

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- A birational morphism from an irreducible scheme to an open subscheme `U` of the integral
scheme `X` is birational as a morphism to `X`. -/
private theorem isBirationalMorphism_comp_ι {Y : Scheme.{u}} [IrreducibleSpace Y]
    (U : X.Opens) {g : Y ⟶ U} (hg : IsBirationalMorphism g) : IsBirationalMorphism (g ≫ U.ι) := by
  have : Nonempty Y := (IrreducibleSpace.isIrreducible_univ Y).nonempty.to_subtype.map Subtype.val
  obtain ⟨W, hWne, hW⟩ := hg.exists_isOpenImmersion
  have : Nonempty W := hWne.to_subtype
  have hd : Dense (((W.ι ≫ g) ≫ U.ι).opensRange : Set X) :=
    ((W.ι ≫ g) ≫ U.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  refine ⟨⟨W, W.isOpen.dense hWne, _, hd, ((W.ι ≫ g) ≫ U.ι).isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨W, W.isOpen.dense hWne, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι, Scheme.topIso_hom,
    Category.assoc]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.homOfLE_ι_assoc _ _ _).symm

/-- A divisor `(Y, f, E)` over a normal variety `X` is exceptional exactly when `f(η_E)` has
coheight at least two, that is, when its center has codimension at least two. -/
private theorem DivisorOver.isExceptional_iff_two_le_coheight (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) : D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) from
      Subsingleton.elim _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    ← MMP.Positivity.DivisorOver.codimension_center]
  have hc : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ :=
    TopologicalSpace.Closeds.ext <| by
      rw [TopologicalSpace.Closeds.coe_closure]; exact D.coe_center.symm
  rw [hc, closedsCodimension_coe]

/-- The restriction `(U, Δ|_U)` of a pair to a nonempty open subscheme, with canonical divisor
`K|_U`, is a pair. -/
theorem IsPairWith.restrictOpen (h : IsPairWith sX n K Δ) (U : X.Opens) [Nonempty U] :
    IsPairWith (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) := by
  have := DivisorOver.isDominant_opens_ι U
  obtain ⟨m, hm, hC⟩ := h.2.2.exists_pos
  exact ⟨h.1.restrictOpen U, h.2.1.restrictOpen h.1 U, m, by exact_mod_cast hm.ne',
    DivisorOver.isCartierDivisor_smul_restrictOpen hC U⟩

/-- **A divisor over an open subscheme is a divisor over `X`.** An exceptional divisor
`(Y, f, E)` over a nonempty open `U ⊆ X` with discrepancy `a` over `(U, Δ|_U)` gives the
exceptional divisor `(Y, f ≫ ι_U, E)` over `X`, which sends `η_E` to `ι_U(f(η_E))`, whose center
meets `U` and whose discrepancy over `(X, Δ)` is `a`. -/
theorem IsPairWith.exists_isDiscrepancy_of_restrictOpen [PerfectField k]
    (h : IsPairWith sX n K Δ) (U : X.Opens) [Nonempty U] {D : DivisorOver k (U.ι ≫ sX)} {a : ℚ}
    (hD : D.IsExceptional)
    (ha : IsDiscrepancy (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) D a) :
    ∃ D₁ : DivisorOver k sX, D₁.IsExceptional ∧
      D₁.f D₁.E.genericPoint = U.ι (D.f D.E.genericPoint) ∧
      ((D₁.center : Set X) ∩ U).Nonempty ∧ IsDiscrepancy sX n K Δ D₁ a := by
  have := DivisorOver.isDominant_opens_ι U
  have := D.isIntegral
  let D₁ : DivisorOver k sX := ⟨D.Y, D.f ≫ U.ι, by rw [Category.assoc]; exact D.isNormalVariety,
    isBirationalMorphism_comp_ι U D.isBirationalMorphism, D.E⟩
  have hcen : ((D₁.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D₁.center_eq_closure_genericPoint]; exact subset_closure rfl,
      (D.f D.E.genericPoint).2⟩
  have hE₁ : D₁.IsExceptional := by
    rw [DivisorOver.isExceptional_iff_two_le_coheight h.1]
    rw [DivisorOver.isExceptional_iff_two_le_coheight (h.restrictOpen U).1] at hD
    change 2 ≤ Order.coheight (U.ι (D.f D.E.genericPoint))
    rwa [coheight_eq_of_isOpenImmersion]
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.isPair h.2.1 D₁
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff h D₁ U hcen
  have hv : (⟨_, D₁.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)).valuation = D.valuation := by
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    ext t
    obtain ⟨s, rfl⟩ := (DivisorOver.functionFieldMap_opens_ι_bijective U).2 t
    refine (congrArg (· s) hval).symm.trans ?_
    change D.E.divisorialValuation (functionFieldMap (D.f ≫ U.ι) s) =
      D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap U.ι s))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hba := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq (h.restrictOpen U).1 hv)
    ((hiff b).1 hb) ha
  exact ⟨D₁, hE₁, rfl, hcen, hba ▸ hb⟩

/-- The discrepancy of an exceptional divisor `(Y, f, E)` over `X` whose center meets a nonempty
open `U` bounds `discrep(U, Δ|_U)`: its restriction `(f⁻¹(U), f ∣_ U, E_U)` to `U`
(`MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff`) has the same discrepancy, and it is
exceptional since the open immersion `ι_U` keeps the coheight of `f(η_E)`. -/
private theorem discrep_restrictOpen_le [PerfectField k] (h : IsPairWith sX n K Δ)
    (U : X.Opens) [Nonempty U] {D : DivisorOver k sX} {b : ℚ} (hD : D.IsExceptional)
    (hcen : ((D.center : Set X) ∩ U).Nonempty) (hb : IsDiscrepancy sX n K Δ D b) :
    discrep (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) ≤ ((b : ℝ) : EReal) := by
  obtain ⟨hY, hf, E', hE', -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff h D U hcen
  refine discrep_le ?_ ((hiff b).1 hb)
  rw [DivisorOver.isExceptional_iff_two_le_coheight (h.restrictOpen U).1,
    ← coheight_eq_of_isOpenImmersion U.ι]
  rw [DivisorOver.isExceptional_iff_two_le_coheight h.1] at hD
  change 2 ≤ Order.coheight (U.ι ((D.f ∣_ U) E'.genericPoint))
  rwa [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
    DivisorOver.ι_genericPoint_eq D U E' hE']

/-- **The discrepancy does not decrease on an open subscheme**: for a pair `(X, Δ)` over a
perfect field and a nonempty open `U ⊆ X`, `discrep(X, Δ) ≤ discrep(U, Δ|_U)`. -/
theorem discrep_le_discrep_restrictOpen [PerfectField k] (h : IsPairWith sX n K Δ) (U : X.Opens)
    [Nonempty U] :
    discrep sX n K Δ ≤ discrep (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) :=
  le_discrep_iff.mpr fun _ _ hD ha =>
    let ⟨_, hE₁, _, _, hb⟩ := h.exists_isDiscrepancy_of_restrictOpen U hD ha
    discrep_le hE₁ hb

/-- **The discrepancy does not decrease on a smaller open subscheme**: for a pair `(X, Δ)` over a
perfect field and nonempty opens `V ⊆ U ⊆ X`, `discrep(U, Δ|_U) ≤ discrep(V, Δ|_V)`. -/
theorem discrep_restrictOpen_le_discrep_restrictOpen [PerfectField k] (h : IsPairWith sX n K Δ)
    {U V : X.Opens} (hVU : V ≤ U) [Nonempty U] [Nonempty V] :
    discrep (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) ≤
      discrep (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) := by
  refine le_discrep_iff.mpr fun _ _ hD ha => ?_
  obtain ⟨_, hE₁, -, hcen, hb⟩ := h.exists_isDiscrepancy_of_restrictOpen V hD ha
  exact discrep_restrictOpen_le h U hE₁ (hcen.mono (Set.inter_subset_inter_right _ hVU)) hb

variable [PerfectField k] (U : X.Opens) [Nonempty U]

/-- A terminal pair restricts to a terminal pair on a nonempty open subscheme. -/
theorem IsTerminalPair.restrictOpen (h : IsTerminalPair sX n K Δ) :
    IsTerminalPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) :=
  ⟨h.1.restrictOpen U, h.2.trans_le (discrep_le_discrep_restrictOpen h.1 U)⟩

/-- A canonical pair restricts to a canonical pair on a nonempty open subscheme. -/
theorem IsCanonicalPair.restrictOpen (h : IsCanonicalPair sX n K Δ) :
    IsCanonicalPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) :=
  ⟨h.1.restrictOpen U, h.2.trans (discrep_le_discrep_restrictOpen h.1 U)⟩

/-- A plt pair restricts to a plt pair on a nonempty open subscheme. -/
theorem IsPltPair.restrictOpen (h : IsPltPair sX n K Δ) :
    IsPltPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) :=
  ⟨h.1.restrictOpen U, h.2.trans_le (discrep_le_discrep_restrictOpen h.1 U)⟩

/-- A klt pair restricts to a klt pair on a nonempty open subscheme. -/
theorem IsKltPair.restrictOpen (h : IsKltPair sX n K Δ) :
    IsKltPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) :=
  ⟨h.1.restrictOpen U, h.2.1.trans_le (discrep_le_discrep_restrictOpen h.1 U),
    roundDown_nonpos_iff.mpr fun _ => roundDown_nonpos_iff.mp h.2.2 _⟩

/-- An lc pair restricts to an lc pair on a nonempty open subscheme. -/
theorem IsLcPair.restrictOpen (h : IsLcPair sX n K Δ) :
    IsLcPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) :=
  ⟨h.1.restrictOpen U, h.2.trans (discrep_le_discrep_restrictOpen h.1 U)⟩

variable {U} {V : X.Opens} [Nonempty V]

/-- A terminal pair on an open subscheme `U` restricts to a terminal pair on every nonempty open
`V ⊆ U`. -/
theorem IsTerminalPair.mono_opens (h : IsPairWith sX n K Δ) (hVU : V ≤ U)
    (hU : IsTerminalPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)) :
    IsTerminalPair (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) :=
  ⟨h.restrictOpen V, hU.2.trans_le (discrep_restrictOpen_le_discrep_restrictOpen h hVU)⟩

/-- A canonical pair on an open subscheme `U` restricts to a canonical pair on every nonempty
open `V ⊆ U`. -/
theorem IsCanonicalPair.mono_opens (h : IsPairWith sX n K Δ) (hVU : V ≤ U)
    (hU : IsCanonicalPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)) :
    IsCanonicalPair (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) :=
  ⟨h.restrictOpen V, hU.2.trans (discrep_restrictOpen_le_discrep_restrictOpen h hVU)⟩

/-- A plt pair on an open subscheme `U` restricts to a plt pair on every nonempty open
`V ⊆ U`. -/
theorem IsPltPair.mono_opens (h : IsPairWith sX n K Δ) (hVU : V ≤ U)
    (hU : IsPltPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)) :
    IsPltPair (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) :=
  ⟨h.restrictOpen V, hU.2.trans_le (discrep_restrictOpen_le_discrep_restrictOpen h hVU)⟩

/-- A klt pair on an open subscheme `U` restricts to a klt pair on every nonempty open
`V ⊆ U`. -/
theorem IsKltPair.mono_opens (h : IsPairWith sX n K Δ) (hVU : V ≤ U)
    (hU : IsKltPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)) :
    IsKltPair (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) :=
  ⟨h.restrictOpen V, hU.2.1.trans_le (discrep_restrictOpen_le_discrep_restrictOpen h hVU),
    roundDown_nonpos_iff.mpr fun W => by
      obtain ⟨W', hW'⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι
        (OpenWeilRestriction.primeDivisorMap V.ι W)).2 (by
          rw [OpenWeilRestriction.genericPoint_primeDivisorMap, Scheme.Opens.range_ι]
          exact hVU W.genericPoint.2)
      have := roundDown_nonpos_iff.mp hU.2.2 W'
      rwa [DivisorWithCoeffs.coeff_restrictOpen, hW'] at this⟩

/-- An lc pair on an open subscheme `U` restricts to an lc pair on every nonempty open
`V ⊆ U`. -/
theorem IsLcPair.mono_opens (h : IsPairWith sX n K Δ) (hVU : V ≤ U)
    (hU : IsLcPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)) :
    IsLcPair (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) :=
  ⟨h.restrictOpen V, hU.2.trans (discrep_restrictOpen_le_discrep_restrictOpen h hVU)⟩

end MMP.Mori
