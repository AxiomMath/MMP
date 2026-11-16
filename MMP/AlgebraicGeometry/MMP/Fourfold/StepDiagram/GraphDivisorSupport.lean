module
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
public import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.ChainComparison
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus

/-!
# Graph divisors of step diagrams and relatively ample ends

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a step diagram of fourfolds with normalized graph `(G, u, v)`
and graph divisor `H = u^* D⁻ - v^* D⁺`, where `D^± = K_{X^±} + B^±`. For a valuation `ξ` of
`k(G)` whose restriction to `k(X⁻)` is a normalized divisorial valuation,
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H) ≥ 0`, and the support of `H` is the preimage `g⁻¹(Σ)` of the
bad locus `Σ` of the diagram under `g = u ≫ f⁻`.

Separately, if `π_j : V_j ⟶ Z` are projective morphisms of normal projective varieties, `D₁` is
`π₁`-nef, `D₂` is `π₂`-ample, and `q_j : W ⟶ V_j` are birational morphisms from a smooth
projective `W` over `Z` with `q₁^* D₁ + F₁ = q₂^* D₂ + F₂` for effective `q_j`-exceptional `F_j`,
then `q₂ = q₁ ≫ h` for a morphism `h : V₁ ⟶ V₂` over `Z` with `D₁ = h^* D₂`.

## Main results

* `MMP.Fourfold.IsGraphDivisor.exists_sub_eq_coeff_pullback`: the discrepancy comparison
  `a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H) ≥ 0`.
* `MMP.Fourfold.IsGraphDivisor.coe_supp_eq_preimage_badLocusBase`: `Supp H = g⁻¹(Σ)`.
* `MMP.Fourfold.exists_comp_eq_and_isPullback_of_add_eq_add_of_hasRelativelyAmpleMultiple`:
  a relatively ample end is a morphic image.

## Implementation notes

The discrepancy comparison realizes `ξ = ord_E` on a normal `W` proper birational over `G`, writes
`K⁻ = div(f⁻^* τ)` and `K⁺ = div(f⁺^* τ)` for a rational top form `τ` on `Z`, and compares the two
log discrepancies along `E` with the common form on `W`. The support computation uses that `H`
vanishes over the common biregular locus and that every closed point of `g⁻¹(Σ)` lies on a curve
contracted by `g`, on which `H` is positive. The morphic-image statement follows from the sibling
`MMP.Fourfold.eq_of_isPullback_of_add_eq_add_of_isRelativelyNef` (`q₁^* D₁ = q₂^* D₂`), the
projection formula and rigidity. The auxiliary lemmas live in the namespaces `Proof_<tag>`.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4], the graph divisor of a step diagram
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.39
-/

@[expose] public section

universe u

namespace Proof_lem_oai4_graph

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori MMP.Fourfold
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section CanonicalDivisorExistence

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq [LocallyOfFiniteType sX] (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- In an irreducible space every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (Z : irreducibleComponents T) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))

private theorem componentIndex_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes_component {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem component_specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes_component Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := componentIndex_eq Z Z'
  rfl

private theorem stalkSpecializes_genericPoint_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective
      (Y.presheaf.stalkSpecializes (genericPoint_specializes_component Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (component_specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes_component E.component)).hom
        s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation]
  exact or_congr ((injective_iff_map_eq_zero' _).1
    (stalkSpecializes_genericPoint_injective E.component) _).symm Iff.rfl

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, -⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
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
  exact stalkSpecializes_genericPoint_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (component_specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes_component _)).hom
      ((X.presheaf.stalkSpecializes (component_specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
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
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  refine ⟨fun h P hP => ?_, fun h E' hE' =>
    (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))⟩
  have hPU : P.genericPoint ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
    rw [← hx]
    exact x.2
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
  exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))

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
immersion, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms (ψ ≫ p) n) := by
  have hc : ψ ≫ p = (ψ ≫ p) ≫ 𝟙 S := (Category.comp_id _).symm
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p (ψ ≫ p) (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p (ψ ≫ p) (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq (sX := sS) T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  let e₀ := (@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom T KS)).symm
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

section Helpers

variable {X Y : Scheme.{u}}

/-- A morphism whose exceptional set has codimension at least two is biregular over the image
of the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f :=
  not_not.mp fun h => by
    have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 h
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)

end Helpers

/-- The first projection `u` of a normalized graph of `f⁻` and a proper `f⁺` is proper. -/
private theorem isProper_minus_of_isNormalizedGraph {Xm Xp Z G : Scheme.{u}} {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp} (hG : IsNormalizedGraph fm fp u v) [IsProper fp] :
    IsProper u := by
  haveI := hG.isFinite
  rw [← Limits.pullback.lift_fst u v hG.comp_eq]
  infer_instance

/-- The second projection `v` of a normalized graph of a proper `f⁻` and `f⁺` is proper. -/
private theorem isProper_plus_of_isNormalizedGraph {Xm Xp Z G : Scheme.{u}} {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp} (hG : IsNormalizedGraph fm fp u v) [IsProper fm] :
    IsProper v := by
  haveI := hG.isFinite
  rw [← Limits.pullback.lift_snd u v hG.comp_eq]
  infer_instance

section ValuationLift

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
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
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  letI := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] (hgp' : IsProper g')
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
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hgp' : IsProper g')
    (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX') (D : DivisorOver ℂ sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : DivisorOver ℂ sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' hgp' D ξ' h
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField ℂ sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

end ValuationLift

private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 :=
  (eq_univ_of_irreducibleComponents W).symm ▸ Set.mem_univ t

/-- **Pull-back of divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ
/-- If `m • (div ω + Δ)` is the integral divisor `D`, then `ord_Γ ω + coeff_Γ Δ = m⁻¹ coeff_Γ D`:
the coefficients of the `ℝ`-divisor `K + Δ` read off from a Cartier multiple. -/
private theorem ordForm_add_coeff_eq {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] {d : ℕ}
    (ω : RationalPluriForms sZ d 1) (Δ : QDivisor Z)
    {m₀ : ℕ} (hm₀ : 0 < m₀) {D : Divisor Z}
    (hD : Divisor.toQDivisor D = (m₀ : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + Δ))
    (Γ : MMP.Mori.PrimeDivisor Z) :
    (Γ.ordForm ω : ℝ) + (QDivisor.toRDivisor Δ).coeff Γ =
      ∑ _i : Fin 1, (m₀ : ℝ)⁻¹ * (D.coeff Γ : ℝ) := by
  have hc := congrArg (fun G : QDivisor Z => G.coeff Γ) hD
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, zsmul_eq_mul, Int.cast_natCast, coeff_divisorOfForm] at hc
  have hR : (D.coeff Γ : ℝ) = m₀ * (Γ.ordForm ω + (Δ.coeff Γ : ℝ)) := by exact_mod_cast hc
  have hm₀R : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  simp only [Finset.univ_unique, Finset.sum_singleton, QDivisor.coeff_toRDivisor, hR]
  field_simp

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
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

/-! ### Rational top forms -/

section Forms

/-- Forms pulled back along equal morphisms have the same order along a prime divisor. -/
private theorem ordForm_pullbackRationalPluriForms_congr {W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)} {g g' : W ⟶ Z}
    [IsDominant g] [IsDominant g'] (hg : g = g') (E : MMP.Mori.PrimeDivisor W) {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sZ d m) :
    E.ordForm (pullbackRationalPluriForms sZ g τ) =
      E.ordForm (pullbackRationalPluriForms sZ g' τ) := by
  subst hg
  rfl

/-- **Rational top forms descend along a birational morphism.** If `f : X ⟶ Z` induces an
isomorphism of function fields, every rational top form on `X` is the pull-back `f^* τ` of a
rational top form `τ` on `Z`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    (ω : RationalPluriForms (f ≫ sZ) n 1) :
    ∃ τ : RationalPluriForms sZ n 1, pullbackRationalPluriForms sZ f τ = ω := by
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  refine ⟨g • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := Z.functionField) (K' := X.functionField) 1 _ = ω
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = ω
  rw [hg]
  exact basis_unit_repr_smul _ ω

end Forms

/-! ### Prime and canonical divisors across a step -/

section StepDiagram

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- **A step extracts no divisor.** In a step diagram, a prime divisor `P` of `X⁺` and a prime
divisor `P⁻` of `X⁻` lie over the same prime divisor `Q` of `Z`, and every strict transform
`(f⁺)⁻¹_* f⁻_* D` has at `P` the coefficient of `D` at `P⁻`. -/
private theorem exists_flipTransform_apply_eq (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (P : MMP.Mori.PrimeDivisor Xp) :
    ∃ (Pm : MMP.Mori.PrimeDivisor Xm) (Q : MMP.Mori.PrimeDivisor Z),
      fm Pm.genericPoint = Q.genericPoint ∧ fp P.genericPoint = Q.genericPoint ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm),
        flipTransform fm fp D P = D Pm := by
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hZ
  have hbm := hD.isBirationalMorphism_minus
  haveI := hbm.isDominant
  haveI := hD.isBirationalMorphism_plus.isDominant
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hbm
    hD.isSmallMorphism_plus P
  have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  have := Q.isDiscreteValuationRing_localRing
  exact ⟨Pm, Q, hPmQ', hPQ', fun D => flipTransform_apply_of_map_genericPoint
    hbm.functionFieldMap_bijective fp.surjective hPmQ' hPQ'
    (hPQ' ▸ map_genericPoint_mem_biregularLocus hD.isSmallMorphism_plus.two_le_codimension P) D⟩

/-- **The canonical divisor of `X⁺`.** In a step diagram over `Z` with `K = div(f⁻^* τ)` for a
rational top form `τ` on `Z`, the strict transform `K⁺ = (f⁺)⁻¹_* f⁻_* K` is `div(f⁺^* τ)`. -/
private theorem divisorOfForm_eq_flipTransform [IsIntegral Z]
    (hD : IsFourfoldStepDiagram (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType (fp ≫ sZ)] [IsDominant fm] [IsDominant fp]
    (τ : RationalPluriForms sZ n 1)
    (hK : ∀ Γ, Γ.ordForm (pullbackRationalPluriForms sZ fm τ) = K.coeff Γ) :
    divisorOfForm (pullbackRationalPluriForms sZ fp τ) = flipTransform fm fp K := by
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isBirationalMorphism_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  refine Finsupp.ext fun P => ?_
  obtain ⟨Pm, Q, hPm, hP, hfl⟩ := exists_flipTransform_apply_eq hD P
  have := Q.isDiscreteValuationRing_localRing
  have : ValuationRing (Z.presheaf.stalk (fp P.genericPoint)) := by rw [hP]; infer_instance
  have : ValuationRing (Z.presheaf.stalk (fm Pm.genericPoint)) := by rw [hPm]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hbp.functionFieldMap_bijective
    P.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing fm hbm.functionFieldMap_bijective
    Pm.genericPoint
  change P.ordForm (pullbackRationalPluriForms sZ fp τ) = flipTransform fm fp K P
  rw [hfl K, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp
      hbp.functionFieldMap_bijective hd P Q hP τ,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fm
      hbm.functionFieldMap_bijective hd Pm Q hPm τ, hK Pm]
  rfl

end StepDiagram

/-! ### Log discrepancies from Cartier multiples -/

section LogDiscrepancy

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The log discrepancy of a valuation is unique. -/
private theorem isValuationLogDiscrepancy_eq {B : QDivisor X}
    {ξ : Valuation X.functionField ℤᵐ⁰} {a a' : ℝ} (h : IsValuationLogDiscrepancy sX B ξ a)
    (h' : IsValuationLogDiscrepancy sX B ξ a') : a = a' := by
  obtain ⟨n, D, -, hv, h⟩ := h
  obtain ⟨n', D', -, hv', h'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hv.trans hv'.symm)

/-- **The log discrepancy from a Cartier multiple.** Let `div(ω)` be a canonical divisor of a
normal variety `X` with `m (div(ω) + B) = C` a Cartier divisor, and `(Y, f, E)` a divisor over `X`
with `f` proper and `f^* C = L`. Then `a(E, X, B) = 1 + ord_E(f^* ω) - m⁻¹ coeff_E L`. -/
private theorem isLogDiscrepancy_of_isPullback [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n) {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {C : Divisor X}
    (hC : Divisor.toQDivisor C = (m : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + B))
    (hCc : C.IsCartier) {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    [IsProper f] (hY : IsNormalVariety ℂ (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : MMP.Mori.PrimeDivisor Y)
    {hB : ∀ T : irreducibleComponents Y, f (componentGenericPoint Y T) ∉ C.supp}
    {L : Divisor Y} (hL : C.IsPullback f hB L) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) ⟨Y, f, hY, hf, E⟩
      (1 + ((⟨Y, f, hY, hf, E⟩ : DivisorOver ℂ sX).ordPullback ω : ℝ) -
        (m : ℝ)⁻¹ * (L.coeff E : ℝ)) :=
  ⟨hX, ‹IsProper f›, ω, hω, ⟨_, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, 1, fun _ => (m : ℝ)⁻¹,
    fun _ => C, fun _ => L, fun _ => hCc, fun Γ => ordForm_add_coeff_eq ω B hm hC Γ,
    fun _ => ⟨_, hL⟩, by simp⟩

end LogDiscrepancy

/-- **The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective.** With `m` the Cartier
index of `A`, `m f^*A` is the pull-back of the effective Cartier divisor `mA`, whose local
equations are regular (algebraic Hartogs), so their pull-backs have nonnegative order. -/
private theorem nonneg_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) : 0 ≤ B := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hmq : (0 : ℚ) < (A.cartierIndex hAq : ℚ) := by exact_mod_cast hm
  have hD₀n : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ (⊤ : X.Opens)).Nonempty →
      0 ≤ D₀.coeff P := by
    intro P _
    have h2 : (D₀ P : ℚ) = A.cartierIndex hAq * A P :=
      (by simpa using congrArg (· P) hD₀ :
        Divisor.toQDivisor D₀ P = A.cartierIndex hAq * A P)
    exact_mod_cast h2 ▸ mul_nonneg hmq.le (hA P)
  intro E
  have hE : (E.support ∩ f ⁻¹ᵁ (⊤ : X.Opens)).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  have h0 := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hD₀c hD₀n hp E hE
  have h1 : (D' E : ℚ) = A.cartierIndex hAq * B E :=
    (by simpa using congrArg (· E) hD' :
      Divisor.toQDivisor D' E = A.cartierIndex hAq * B E)
  have h0' : (0 : ℚ) ≤ (D' E : ℚ) := by exact_mod_cast h0
  exact nonneg_of_mul_nonneg_right (h1 ▸ h0') hmq

/-! ### The comparison -/

section Comparison

/-- `m₁ Λ⁻ - m₀ Λ⁺` is the integral divisor `m₀ m₁ (H⁻ - H⁺)` when `Λ⁻ = m₀ H⁻`, `Λ⁺ = m₁ H⁺`. -/
private theorem toQDivisor_zsmul_add_neg_zsmul {Y : Scheme.{0}} {Lu Lv : Divisor Y}
    {Hm Hp : QDivisor Y} {m₀ m₁ : ℕ} (hLu : Divisor.toQDivisor Lu = (m₀ : ℤ) • Hm)
    (hLv : Divisor.toQDivisor Lv = (m₁ : ℤ) • Hp) :
    Divisor.toQDivisor ((m₁ : ℤ) • Lu + (-(m₀ : ℤ)) • Lv) = ((m₀ * m₁ : ℕ) : ℤ) • (Hm - Hp) := by
  rw [map_add, map_zsmul, map_zsmul, hLu, hLv, smul_smul, smul_smul, smul_sub]
  push_cast
  rw [neg_mul, neg_smul, mul_comm (m₁ : ℤ) m₀, ← sub_eq_add_neg]

/-- A divisor `(W, w, E)` over `G`, seen over `X` through a birational `g : G ⟶ X`, has
valuation `ord_E` read on `k(X)` through `g`. -/
private theorem valuation_mk_comp {X G : Scheme.{0}} [IsIntegral X] [IsIntegral G]
    {s : X ⟶ Spec (.of ℂ)} {t : G ⟶ Spec (.of ℂ)} (g : G ⟶ X) [IsDominant g]
    (D : DivisorOver ℂ t)
    (hW : IsNormalVariety ℂ ((D.f ≫ g) ≫ s)) (hb : IsBirationalMorphism (D.f ≫ g)) :
    (⟨D.Y, D.f ≫ g, hW, hb, D.E⟩ : DivisorOver ℂ s).valuation =
      D.valuation.comap (functionFieldMap g) := by
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero {S T : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ))
    (g : T ⟶ S) [IsIntegral S] [IsIntegral T] [IsDominant g] {d : ℕ} :
    pullbackRationalPluriForms sS g (0 : RationalPluriForms sS d 1) = 0 := by
  letI := functionFieldAlgebra sS
  letI := functionFieldAlgebra (g ≫ sS)
  letI := functionFieldMapAlgebra g
  haveI := isScalarTower_functionFieldMap sS g
  change pullbackForms (K := S.functionField) (K' := T.functionField) 1 0 = 0
  rw [pullbackForms]
  split_ifs
  · rw [pullbackFormsAlong]
    simp
  · rfl

/-- From `m₀ m₁ c = m₁ a - m₀ b` with `m₀, m₁ ≠ 0`:
`(1 + t - m₁⁻¹ b) - (1 + t - m₀⁻¹ a) = c`. -/
private theorem one_add_sub_sub_one_add_sub_eq {t a b c m₀ m₁ : ℝ} (hm₀ : m₀ ≠ 0)
    (hm₁ : m₁ ≠ 0) (h : m₀ * m₁ * c = m₁ * a - m₀ * b) :
    1 + t - m₁⁻¹ * b - (1 + t - m₀⁻¹ * a) = c := by
  field_simp
  linear_combination -h

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
  {H : QDivisor G}

/-- The graph divisor is `ℚ`-Cartier: `m₀ m₁ H = m₁ u^*(m₀ D⁻) - m₀ v^*(m₁ D⁺)`. -/
private theorem isQCartier_of_isGraphDivisor (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) :
    H.IsQCartier := by
  have hD := h.isFourfoldStepDiagram
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, rfl⟩ := h.exists_pullback
  obtain ⟨m₀, hm₀, DX, hDX, hDXc⟩ := hD.isQCartier_minus.exists_pos
  obtain ⟨m₁, hm₁, DXp, hDXp, hDXpc⟩ := hD.isQCartier_plus.exists_pos
  obtain ⟨Lu, hLu, hLupb⟩ := hHm m₀ hm₀ DX hDX hDXc
  obtain ⟨Lv, hLv, hLvpb⟩ := hHp m₁ hm₁ DXp hDXp hDXpc
  exact ⟨((m₀ * m₁ : ℕ) : ℤ), by exact_mod_cast (Nat.mul_pos hm₀ hm₁).ne', _,
    toQDivisor_zsmul_add_neg_zsmul hLu hLv,
    ((hLupb.isCartier hDXc).zsmul _).add ((hLvpb.isCartier hDXpc).zsmul _)⟩

/-- **The canonical divisors of a step diagram from one form.** There is a rational top form `τ`
on `Z` with `K = div(f⁻^* τ)` and `K⁺ = div(f⁺^* τ)`, both canonical divisors. -/
private theorem exists_canonical_forms [IsIntegral Z] [LocallyOfFiniteType sZ]
    [LocallyOfFiniteType (fm ≫ sZ)] [LocallyOfFiniteType (fp ≫ sZ)] [IsDominant fm]
    [IsDominant fp] (hD : IsFourfoldStepDiagram (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp) :
    ∃ (n : ℕ) (_ : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
      (τ : RationalPluriForms sZ n 1),
      pullbackRationalPluriForms sZ fm τ ≠ 0 ∧ pullbackRationalPluriForms sZ fp τ ≠ 0 ∧
      divisorOfForm (pullbackRationalPluriForms sZ fm τ) = K ∧
      divisorOfForm (pullbackRationalPluriForms sZ fp τ) = flipTransform fm fp K ∧
      (divisorOfForm (pullbackRationalPluriForms sZ fm τ)).IsCanonicalDivisor (fm ≫ sZ) n ∧
      (divisorOfForm (pullbackRationalPluriForms sZ fp τ)).IsCanonicalDivisor (fp ≫ sZ) n := by
  have hZ := hD.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  have hXm := hD.isNormalVariety_minus
  have hXp := hD.isNormalVariety_plus
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZ) := hXp.1
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isBirationalMorphism_plus
  obtain ⟨n, hK⟩ := hD.isCanonicalDivisor
  have hnm : topologicalKrullDim Xm = n := hK.topologicalKrullDim_eq
  have hnZ : topologicalKrullDim Z = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (fm ≫ sZ) hbm).trans hnm
  have hnp : topologicalKrullDim Xp = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (fp ≫ sZ) hbp).symm.trans
      hnZ
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXm hK
  obtain ⟨τ, rfl⟩ := exists_pullbackRationalPluriForms_eq fm hbm.functionFieldMap_bijective hd ω
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact hω0 (pullbackRationalPluriForms_zero sZ fm)
  have hωp0 : pullbackRationalPluriForms sZ fp τ ≠ 0 :=
    pullbackRationalPluriForms_ne_zero fp hbp.functionFieldMap_bijective hd hτ0
  have hdivm : divisorOfForm (pullbackRationalPluriForms sZ fm τ) = K :=
    Finsupp.ext hω
  have hdivp := divisorOfForm_eq_flipTransform hD hd τ hω
  have hKm : (divisorOfForm (pullbackRationalPluriForms sZ fm τ)).IsCanonicalDivisor
      (fm ≫ sZ) n := hdivm ▸ hK
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor (fp ≫ sZ) hXp hnp
  have hKp : (divisorOfForm (pullbackRationalPluriForms sZ fp τ)).IsCanonicalDivisor
      (fp ≫ sZ) n := hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXp hK₀ hωp0)
  exact ⟨n, hd, τ, hω0, hωp0, hdivm, hdivp, hKm, hKp⟩

/-- A proper divisor `(W, w, E)` over `G` followed by a proper birational `g : G ⟶ X` gives a
birational `w ≫ g`. -/
private theorem isBirationalMorphism_comp_divisorOver {X Y : Scheme.{0}} [IsIntegral X]
    [IsNormal X] [IsLocallyNoetherian X] [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
    {t : Y ⟶ Spec (.of ℂ)} (D : DivisorOver ℂ t) [IsProper D.f] (g : Y ⟶ X) [IsProper g]
    (hg : IsBirationalMorphism g) : IsBirationalMorphism (D.f ≫ g) :=
  haveI := D.isIntegral
  MMP.Mori.isBirationalMorphism_comp_of_isBirational g D.f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)

/-- If `D''` is the pull-back along `g` of `m₁ L - m₀ L'` and `D'' = m₀ m₁ H'`, then along any
prime divisor `E`, `m₀ m₁ coeff_E H' = m₁ coeff_E (g^* L) - m₀ coeff_E (g^* L')`. -/
private theorem coeff_mul_eq_of_isPullback {W : Scheme.{0}} [IsIntegral W] [IsNormal W]
    [IsLocallyNoetherian W] (g : W ⟶ G) [IsDominant g] {Lu Lv : Divisor G}
    (hLuc : Lu.IsCartier) (hLvc : Lv.IsCartier) {Lw Lvw : Divisor W}
    (hLw : Lu.IsPullback g (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g _) Lw)
    (hLvw : Lv.IsPullback g (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g _) Lvw)
    {m₀ m₁ : ℕ} {H' : QDivisor W} {D'' : Divisor W}
    (hD'' : Divisor.toQDivisor D'' = ((m₀ * m₁ : ℕ) : ℤ) • H')
    {hB : ∀ T : irreducibleComponents W,
      g (componentGenericPoint W T) ∉ ((m₁ : ℤ) • Lu + (-(m₀ : ℤ)) • Lv).supp}
    (hD''pb : ((m₁ : ℤ) • Lu + (-(m₀ : ℤ)) • Lv).IsPullback g hB D'') (E : PrimeDivisor W) :
    ((m₀ : ℚ) * m₁) * H'.coeff E = m₁ * Lw.coeff E - m₀ * Lvw.coeff E := by
  have hCHpb := Divisor.IsPullback.add (hLuc.zsmul (m₁ : ℤ)) (hLvc.zsmul (-(m₀ : ℤ))) hB
    (hLw.zsmul hLuc _ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g _))
    (hLvw.zsmul hLvc _ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g _))
  have := congrArg (fun F : QDivisor W => F.coeff E) hD''
  simp only [hD''pb.eq ((hLuc.zsmul _).add (hLvc.zsmul _)) hCHpb, Divisor.coeff_toQDivisor,
    DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul] at this
  push_cast at this
  linarith

/-- **The log discrepancy of a divisor over the graph, from one form.** Let `X` be a normal
variety birational over `Z` through `f`, with `div(f^* τ)` canonical and `m (div(f^* τ) + B) = C`
Cartier, and `g : G ⟶ X` proper birational. For a proper divisor `(W, w, E)` over `G` with
`(wg)^* C = L`, the valuation `ord_E ∘ g^*` has log discrepancy
`1 + ord_E((wgf)^* τ) - m⁻¹ coeff_E L` over `(X, B)`. -/
private theorem isValuationLogDiscrepancy_comap [IsIntegral Z] [LocallyOfFiniteType sZ]
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {f : X ⟶ Z} [IsDominant f] [LocallyOfFiniteType (f ≫ sZ)] (hX : IsNormalVariety ℂ (f ≫ sZ))
    (hf : IsBirationalMorphism f) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    {τ : RationalPluriForms sZ n 1} (hω : pullbackRationalPluriForms sZ f τ ≠ 0)
    (hK : (divisorOfForm (pullbackRationalPluriForms sZ f τ)).IsCanonicalDivisor (f ≫ sZ) n)
    {B : QDivisor X} {m : ℕ} (hm : 0 < m) {C : Divisor X}
    (hC : Divisor.toQDivisor C =
      (m : ℤ) • (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sZ f τ)) + B))
    (hCc : C.IsCartier) (g : G ⟶ X) [IsProper g] [IsDominant g] (hg : IsBirationalMorphism g)
    {t : G ⟶ Spec (.of ℂ)} (D : DivisorOver ℂ t) [IsProper D.f]
    (hW : IsNormalVariety ℂ ((D.f ≫ g) ≫ f ≫ sZ)) {Lg : Divisor G}
    {hB : ∀ T : irreducibleComponents G, g (componentGenericPoint G T) ∉ C.supp}
    (hLg : C.IsPullback g hB Lg) {Lw : Divisor D.Y}
    {hB' : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ Lg.supp}
    (hLw : haveI := D.isLocallyNoetherian; haveI := D.isNormal; Lg.IsPullback D.f hB' Lw) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    IsValuationLogDiscrepancy (f ≫ sZ) B (D.valuation.comap (functionFieldMap g))
      (1 + (D.E.ordForm (pullbackRationalPluriForms sZ ((D.f ≫ g) ≫ f) τ) : ℝ) -
        (m : ℝ)⁻¹ * (Lw.coeff D.E : ℝ)) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  have hb := isBirationalMorphism_comp_divisorOver D g hg
  haveI := hb.isDominant
  refine ⟨n, _, inferInstance, valuation_mk_comp g D hW hb, ?_⟩
  rw [← pullbackRationalPluriForms_comp f (D.f ≫ g) hf.functionFieldMap_bijective
    hb.functionFieldMap_bijective hd]
  exact isLogDiscrepancy_of_isPullback hX hω hK hm hC hCc (D.f ≫ g) hW hb D.E
    (isPullback_comp hLg hLw
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ g) C))

/-- **The comparison of log discrepancies on a model over the graph.** For a proper divisor
`(W, w, E)` over `G` and the pull-back `H' = w^*H`, the valuation `ord_E` has log discrepancies
`a⁻` over `(X⁻, B⁻)` and `a⁺` over `(X⁺, B⁺)`, and `a⁺ - a⁻ = coeff_E H'`: both are computed
with the one form `(uw)^* (f⁻)^* τ = (vw)^* (f⁺)^* τ`, so they differ by the coefficient along
`E` of `(uw)^* D⁻ - (vw)^* D⁺ = w^* H`. -/
private theorem exists_isValuationLogDiscrepancy_sub_eq
    (h : IsGraphDivisor (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp u v H)
    (D : DivisorOver ℂ (u ≫ fm ≫ sZ)) (hDp : IsProper D.f)
    (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
    (H' : QDivisor D.Y)
    (hH' : haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      H.IsPullback D.f hH H') :
    haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
    haveI := h.isNormalizedGraph.isBirationalMorphism_plus.isDominant
    ∃ am ap : ℝ,
      IsValuationLogDiscrepancy (fm ≫ sZ) B (D.valuation.comap (functionFieldMap u)) am ∧
      IsValuationLogDiscrepancy (fp ≫ sZ) (flipTransform fm fp B)
        (D.valuation.comap (functionFieldMap v)) ap ∧
      ap - am = (H'.coeff D.E : ℝ) := by
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hD.isNormalVariety_minus.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hD.isNormalVariety_plus.1.toLocallyOfFiniteType
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  haveI := isProper_minus_of_isNormalizedGraph hG
  haveI := isProper_plus_of_isNormalizedGraph hG
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hD.isBirationalMorphism_plus.isDominant
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace u
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, hHeq⟩ := h.exists_pullback
  obtain ⟨n, hd, τ, hω0, hωp0, hdivm, hdivp, hKm, hKp⟩ := exists_canonical_forms hD
  -- Cartier multiples of `D^±` and their pull-backs to `G`
  obtain ⟨m₀, hm₀, DX, hDX, hDXc⟩ := hD.isQCartier_minus.exists_pos
  obtain ⟨m₁, hm₁, DXp, hDXp, hDXpc⟩ := hD.isQCartier_plus.exists_pos
  obtain ⟨Lu, hLu, hLupb⟩ := hHm m₀ hm₀ DX hDX hDXc
  obtain ⟨Lv, hLv, hLvpb⟩ := hHp m₁ hm₁ DXp hDXp hDXpc
  have hLuc := hLupb.isCartier hDXc
  have hLvc := hLvpb.isCartier hDXpc
  rw [← hdivm] at hDX
  rw [← hdivp] at hDXp
  have hCH := toQDivisor_zsmul_add_neg_zsmul hLu hLv
  rw [← hHeq] at hCH
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : IsProper D.f := hDp
  haveI : CompactSpace D.Y :=
    (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  -- `W = D.Y` as a divisor over `X⁻` and over `X⁺`
  have hWm : IsNormalVariety ℂ ((D.f ≫ u) ≫ fm ≫ sZ) := by
    rw [Category.assoc]
    exact D.isNormalVariety
  have hWp : IsNormalVariety ℂ ((D.f ≫ v) ≫ fp ≫ sZ) := by
    rw [Category.assoc, ← Category.assoc v, ← hG.comp_eq, Category.assoc]
    exact D.isNormalVariety
  -- the pull-backs of the Cartier multiples to `W`
  obtain ⟨Lw, hLw⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hLuc
  obtain ⟨Lvw, hLvw⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hLvc
  -- the pull-back of `(m₀ m₁) H`
  obtain ⟨D'', hD'', hD''pb⟩ :=
    hH' _ (Nat.mul_pos hm₀ hm₁) _ hCH ((hLuc.zsmul (m₁ : ℤ)).add (hLvc.zsmul (-(m₀ : ℤ))))
  refine ⟨_, _, isValuationLogDiscrepancy_comap hD.isNormalVariety_minus
    hD.isBirationalMorphism_minus hd hω0 hKm hm₀ hDX hDXc u hG.isBirationalMorphism_minus D hWm
    hLupb hLw, isValuationLogDiscrepancy_comap hD.isNormalVariety_plus
    hD.isBirationalMorphism_plus hd hωp0 hKp hm₁ hDXp hDXpc v hG.isBirationalMorphism_plus D hWp
    hLvpb hLvw, ?_⟩
  rw [ordForm_pullbackRationalPluriForms_congr (g := (D.f ≫ v) ≫ fp) (g' := (D.f ≫ u) ≫ fm)
    (by rw [Category.assoc, Category.assoc, hG.comp_eq]) D.E τ]
  exact one_add_sub_sub_one_add_sub_eq (by exact_mod_cast hm₀.ne') (by exact_mod_cast hm₁.ne')
    (by exact_mod_cast coeff_mul_eq_of_isPullback D.f hLuc hLvc hLw hLvw hD'' hD''pb D.E)

end Comparison

end Proof_lem_oai4_graph

section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry hiding PrimeDivisor
open MMP.Mori MMP.Fourfold
open scoped WithZero
open Proof_lem_oai4_graph

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]

/-- **Discrepancy comparison for step diagrams.** For a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`
with normalized graph `(G, u, v)` and graph divisor `H`, and a valuation `ξ` of `k(G)` whose
restriction `ξ ∘ u^*` to `k(X⁻)` is a normalized divisorial valuation, there is `c = ξ(H) ≥ 0`:
`c = coeff_E(w^* H)` for every realization `ξ = ord_E` of `ξ` on a proper birational
`w : W ⟶ G` (and one exists), both log discrepancies `a(ξ ∘ u^*; X⁻, B⁻)` and
`a(ξ ∘ v^*; X⁺, B⁺)` exist, and any two such values satisfy
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = c`. -/
@[mmp "lem_oai4_graph"]
public theorem IsGraphDivisor.exists_sub_eq_coeff_pullback
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H)
    (ξ : Valuation G.functionField (WithZero (Multiplicative ℤ)))
    (hξ : haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sXm (ξ.comap (functionFieldMap u))) :
    haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
    haveI := h.isNormalizedGraph.isBirationalMorphism_plus.isDominant
    ∃ c : ℚ, 0 ≤ c ∧
      (∃ (D : DivisorOver ℂ (u ≫ sXm)), IsProper D.f ∧ D.valuation = ξ ∧
        haveI := D.isLocallyNoetherian
        haveI := D.isNormal
        ∃ (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
          (H' : QDivisor D.Y), H.IsPullback D.f hH H' ∧ H'.coeff D.E = c) ∧
      (∀ D : DivisorOver ℂ (u ≫ sXm), IsProper D.f → D.valuation = ξ →
        haveI := D.isLocallyNoetherian
        haveI := D.isNormal
        ∀ (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
          (H' : QDivisor D.Y), H.IsPullback D.f hH H' → H'.coeff D.E = c) ∧
      (∃ a : ℝ, IsValuationLogDiscrepancy sXm B (ξ.comap (functionFieldMap u)) a) ∧
      (∃ a : ℝ, IsValuationLogDiscrepancy sXp (flipTransform fm fp B)
        (ξ.comap (functionFieldMap v)) a) ∧
      ∀ am ap : ℝ, IsValuationLogDiscrepancy sXm B (ξ.comap (functionFieldMap u)) am →
        IsValuationLogDiscrepancy sXp (flipTransform fm fp B) (ξ.comap (functionFieldMap v)) ap →
          ap - am = c := by
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  have hHq := isQCartier_of_isGraphDivisor h
  have hH0 : 0 ≤ H := IsGraphDivisor.nonneg h
  have e₁ := hD.comp_eq_minus
  have e₂ := hD.comp_eq_plus
  subst e₁ e₂
  have hXm := hD.isNormalVariety_minus
  haveI := hXm.1
  haveI : IsProper fp := hD.isProper_plus
  haveI := isProper_minus_of_isNormalizedGraph hG
  have hbu := hG.isBirationalMorphism_minus
  haveI := hbu.isDominant
  have hGu : IsNormalVariety ℂ (u ≫ fm ≫ sZ) :=
    ⟨(isVariety_iff ℂ (u ≫ fm ≫ sZ)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  -- a realization of `ξ` over `G`
  obtain ⟨D₁, -, hv₁⟩ := hξ
  obtain ⟨D₀, hD₀p, rfl⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq hGu (𝟙 Xm) u
    (isBirationalMorphism_of_isIso _) hbu inferInstance (Category.id_comp _) rfl D₁ ξ (by
      rw [hv₁]
      ext t
      simp [MMP.Mori.functionFieldMap_id_apply])
  haveI := D₀.isIntegral
  haveI := D₀.isNormal
  haveI := D₀.isLocallyNoetherian
  haveI := D₀.isDominant
  haveI : CompactSpace D₀.Y :=
    (D₀.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hH₀ : ∀ T : irreducibleComponents D₀.Y, D₀.f (componentGenericPoint D₀.Y T) ∉ H.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' D₀.f H
  have hH₀pb := QDivisor.isPullback_pullback hHq hH₀
  obtain ⟨am₀, ap₀, ham₀, hap₀, hdiff₀⟩ :=
    exists_isValuationLogDiscrepancy_sub_eq h D₀ hD₀p hH₀ _ hH₀pb
  refine ⟨(H.pullback hHq hH₀).coeff D₀.E, nonneg_of_isPullback hH0 hHq hH₀pb D₀.E,
    ⟨D₀, hD₀p, rfl, hH₀, _, hH₀pb, rfl⟩, ?_, ⟨am₀, ham₀⟩, ⟨ap₀, hap₀⟩, ?_⟩
  · intro D hDp hDv hH' H' hpb
    obtain ⟨am, ap, ham, hap, hdiff⟩ := exists_isValuationLogDiscrepancy_sub_eq h D hDp hH' H' hpb
    rw [hDv] at ham hap
    rw [isValuationLogDiscrepancy_eq ham ham₀, isValuationLogDiscrepancy_eq hap hap₀,
      hdiff₀] at hdiff
    exact_mod_cast hdiff.symm
  · intro am ap ham hap
    rw [isValuationLogDiscrepancy_eq ham ham₀, isValuationLogDiscrepancy_eq hap hap₀, hdiff₀]

end MMP.Fourfold

end

namespace Proof_lem_oai4_c1_graph_support

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MMP.Mori MMP.Fourfold

/-- Over an open `W` on which `f₁` is an isomorphism, two points of `X₁ ×_S X₂` lying over
`f₁⁻¹ W` with the same image in `X₂` are equal: there the fibre product is an open subscheme of
`X₂`. -/
private theorem eq_of_snd_eq_of_isIso_morphismRestrict {X₁ X₂ S : Scheme.{0}} (f₁ : X₁ ⟶ S)
    (f₂ : X₂ ⟶ S) (W : S.Opens) [IsIso (f₁ ∣_ W)] {p q : ↑(pullback f₁ f₂)}
    (hp : pullback.fst f₁ f₂ p ∈ f₁ ⁻¹ᵁ W) (hq : pullback.fst f₁ f₂ q ∈ f₁ ⁻¹ᵁ W)
    (h : pullback.snd f₁ f₂ p = pullback.snd f₁ f₂ q) : p = q := by
  set j := (f₁ ⁻¹ᵁ W).ι ≫ f₁
  haveI : IsOpenImmersion j := by
    rw [show j = (f₁ ∣_ W) ≫ W.ι from (morphismRestrict_ι f₁ W).symm]
    infer_instance
  let m := pullback.map j f₂ f₁ f₂ (f₁ ⁻¹ᵁ W).ι (𝟙 _) (𝟙 _) (by simp [j]) (by simp)
  have hrange : ∀ r : ↑(pullback f₁ f₂), pullback.fst f₁ f₂ r ∈ f₁ ⁻¹ᵁ W → r ∈ Set.range m := by
    intro r hr
    rw [Scheme.Pullback.range_map]
    exact ⟨by rwa [Scheme.Opens.range_ι], ⟨pullback.snd f₁ f₂ r, rfl⟩⟩
  have hsnd : ∀ r', pullback.snd f₁ f₂ (m r') = pullback.snd j f₂ r' := fun r' => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id]
  obtain ⟨p', rfl⟩ := hrange p hp
  obtain ⟨q', rfl⟩ := hrange q hq
  rw [hsnd, hsnd] at h
  rw [(pullback.snd j f₂).isOpenEmbedding.injective h]

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_mem_biregularLocus {X Y : Scheme.{0}} (f : X ⟶ Y) {a b : X}
    (ha : f a ∈ biregularLocus f) (hab : f a = f b) : a = b := by
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let a' : (f ⁻¹ᵁ V).toScheme := ⟨a, ha⟩
  let b' : (f ⁻¹ᵁ V).toScheme := ⟨b, by change f b ∈ V; rw [← hab]; exact ha⟩
  have hι : ∀ z : (f ⁻¹ᵁ V).toScheme, V.ι ((f ∣_ V) z) = f ((f ⁻¹ᵁ V).ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have h1 : (f ∣_ V) a' = (f ∣_ V) b' := V.ι.isOpenEmbedding.injective (by
    rw [hι, hι]
    exact hab)
  exact congrArg (f ⁻¹ᵁ V).ι ((f ∣_ V).isOpenEmbedding.injective h1)

/-- In a Noetherian quasi-sober space, a closed point `y` of a closed connected set `F` with
another point has a proper generization inside `F`. -/
private theorem exists_specializes_ne_of_isConnected {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {F : Set X} (hF : IsClosed F) (hFc : IsPreconnected F)
    {y : X} (hy : y ∈ F) (hyc : IsClosed ({y} : Set X)) {y' : X} (hy' : y' ∈ F) (hne : y' ≠ y) :
    ∃ η ∈ F, η ⤳ y ∧ η ≠ y := by
  by_contra! hcon
  obtain ⟨S, hSfin, hScl, hSirr, hFeq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  set T := ⋃₀ {t ∈ S | y ∉ t}
  have hTcl : IsClosed T :=
    (hSfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hScl t ht.1
  have hyT : y ∉ T := by
    rintro ⟨t, ⟨-, hyt⟩, hy⟩
    exact hyt hy
  have hcover : F ⊆ {y} ∪ T := by
    intro p hp
    rw [hFeq] at hp
    obtain ⟨t, htS, hpt⟩ := hp
    by_cases hyt : y ∈ t
    · obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hSirr t htS) (hScl t htS)
      have hζF : ζ ∈ F := hFeq ▸ Set.subset_sUnion_of_mem htS hζ.mem
      have hζy : ζ = y := hcon ζ hζF (hζ.specializes hyt)
      have : t = {y} := by rw [← hζ.def, hζy, hyc.closure_eq]
      exact Or.inl (this ▸ hpt)
    · exact Or.inr ⟨t, ⟨htS, hyt⟩, hpt⟩
  have hdisj : F ∩ ({y} ∩ T) = ∅ := by
    rw [Set.singleton_inter_eq_empty.mpr hyT, Set.inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hFc _ _ hyc hTcl hcover hdisj with h | h
  · exact hne (h hy')
  · exact hyT (h hy)

/-- The two sides of the commutative square of a normalized graph, on points. -/
private theorem apply_apply_eq {Xm Xp Z G : Scheme.{0}} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    {u : G ⟶ Xm} {v : G ⟶ Xp} (hG : IsNormalizedGraph fm fp u v) (x : G) :
    fm (u x) = fp (v x) := by
  rw [← Scheme.Hom.comp_apply, hG.comp_eq, Scheme.Hom.comp_apply]

/-- Over the locus `U` where `f⁻` and `f⁺` are both isomorphisms, the graph divisor vanishes: a
prime divisor `E` of `G` whose generic point maps into `U` has `coeff_E H = 0`. The fibres of `v`
over `(f⁺)⁻¹ U` are finite, so `v` is an isomorphism near `v(E)`, which is then a prime divisor of
`X⁺`; and `v_* H = 0`. -/
private theorem graphDivisor_apply_eq_zero_of_mem_commonBiregularLocus
    {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) [IsProper v]
    (E : AlgebraicGeometry.PrimeDivisor G)
    (hEU : (u ≫ fm) E.genericPoint ∈ commonBiregularLocus fm fp) : H E = 0 := by
  have hG := h.isNormalizedGraph
  haveI : IsFinite (pullback.lift u v hG.comp_eq) := hG.isFinite
  haveI : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  set y := v E.genericPoint
  have hfst : ∀ b : G, v b = y →
      pullback.fst fm fp (pullback.lift u v hG.comp_eq b) ∈ fm ⁻¹ᵁ commonBiregularLocus fm fp :=
    fun b hb => by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
      change fm (u b) ∈ commonBiregularLocus fm fp
      rw [apply_apply_eq hG, hb, ← apply_apply_eq hG]
      exact hEU
  -- the fibre of `v` over `y` is finite, as `G ⟶ X⁻ ×_Z X⁺` is finite and the fibre product is
  -- an open subscheme of `X⁺` over `(f⁺)⁻¹ U`
  have hfin : (v ⁻¹' {y}).Finite :=
    ((pullback.lift u v hG.comp_eq).finite_preimage_singleton
      (pullback.lift u v hG.comp_eq E.genericPoint)).subset fun a (ha : v a = y) =>
      eq_of_snd_eq_of_isIso_morphismRestrict fm fp _ (hfst a ha) (hfst _ rfl) <| by
        rw [← Scheme.Hom.comp_apply, pullback.lift_snd, ← Scheme.Hom.comp_apply,
          pullback.lift_snd]
        exact ha
  have hyV : y ∈ biregularLocus v := by
    obtain ⟨hO, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso v
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
        hG.isBirationalMorphism_plus)).1 inferInstance
    exact le_biregularLocus (V := ⟨_, hO⟩) hiso hfin
  have hcoh : Order.coheight y = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus v hyV]
    exact E.coheight_genericPoint
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcoh
  have hvE : v E.genericPoint = P.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
  haveI := h.isFourfoldStepDiagram.isNormalVariety_plus.1
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety
    h.isFourfoldStepDiagram.isNormalVariety_plus
  have h0 := congrArg (fun D : QDivisor Xp => D P) h.transformDivisor_eq_zero
  rw [Finsupp.zero_apply, RationalMap.transformDivisor,
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff v E P).mpr hvE)] at h0
  · exact h0
  · intro E' hE'
    have hvE' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff v E' P).mp hE'
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_mem_biregularLocus v (by rw [hvE']; convert hyV using 1; exact hvE.symm)
        (hvE'.trans hvE.symm))

/-! ### Relatively ample divisors on contracted curves -/

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple has positive intersection number with every
proper curve contracted by `f`. -/
private theorem intersectionNumber_pos_of_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (ha : D.HasRelativelyAmpleMultiple f) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := ha
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hD hm L hL hLD]
  have := hL.isInvertibleModule_divisorialSheaf
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
    L.divisorialSheaf hamp C hC
  have : 0 < L.degreeOn k sX C.ι C.dim_le hL := hpos
  positivity

/-- **Negativity on contracted curves.** Every proper curve `C ⊆ G` contracted by `g` lies in
`Supp H`: otherwise `H · C ≥ 0` as `H ≥ 0`, whereas `H · C < 0` as `-H` is `g`-ample. -/
private theorem point_mem_supp_graphDivisor_of_isContractedBy
    {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsLocallyNoetherian G] [IsNormal G] [CompactSpace G]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) (sG : G ⟶ Spec (.of ℂ))
    (C : ProperCurve sG) (hC : C.IsContractedBy (u ≫ fm)) : C.point ∈ H.supp := by
  by_contra hCS
  obtain ⟨m, hm, L, hLc, hL, -⟩ := h.hasRelativelyAmpleMultiple_neg
  have hHnq : (-H).IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hL, hLc⟩
  have hHq : H.IsQCartier :=
    ⟨-(m : ℤ), by simpa using hm.ne', L, by rw [hL, smul_neg, neg_smul], hLc⟩
  have hnn := (MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff (k := ℂ) sG H hHq
    h.nonneg C hCS).1
  have hpos := intersectionNumber_pos_of_hasRelativelyAmpleMultiple sG hHnq
    h.hasRelativelyAmpleMultiple_neg C hC
  have hq1 : ((-1 : ℚ) • H).IsQCartier := by rwa [neg_one_smul]
  have hneg := MMP.Fourfold.intersectionNumber_smul sG C.ι C.dim_le H hHq (-1) hq1
  rw [← MMP.Fourfold.intersectionNumber_congr sG C.ι C.dim_le hHnq hq1 (neg_one_smul ℚ H).symm]
    at hneg
  linarith

/-- If `g = f' ∘ w` with `w` surjective and the fibre of `f'` over `g(y)` has two points, then so
does the fibre of `g`. -/
private theorem exists_ne_mem_fibre {G X' Z : Type*} {w : G → X'} {f' : X' → Z}
    (hw : Function.Surjective w) {y : G} (hnt : (f' ⁻¹' {f' (w y)}).Nontrivial) :
    ∃ y' ∈ (f' ∘ w) ⁻¹' {f' (w y)}, y' ≠ y := by
  obtain ⟨a, ha, hne⟩ := hnt.exists_ne (w y)
  obtain ⟨a', rfl⟩ := hw a
  exact ⟨a', ha, fun h => hne (h ▸ rfl)⟩

/-- A subspace of positive Krull dimension has two points. -/
private theorem nontrivial_of_topologicalKrullDim_pos {X : Type*} [TopologicalSpace X]
    {s : Set X} (h : 0 < topologicalKrullDim s) : s.Nontrivial := by
  by_contra hs
  rw [Set.not_nontrivial_iff] at hs
  haveI : Subsingleton s := hs.coe_sort
  haveI : DiscreteTopology s := Subsingleton.discreteTopology
  exact (topologicalKrullDim_zero_of_discreteTopology s).not_gt h

end Proof_lem_oai4_c1_graph_support

section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MMP.Mori MMP.Fourfold
open Proof_lem_oai4_c1_graph_support

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- **The support of the graph divisor.** For a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with
normalized graph `(G, u, v)` and graph divisor `H`, the support of `H` is the preimage
`g⁻¹(Σ)` of the bad locus `Σ = badLocusBase fm fp` under `g = u ≫ f⁻`. -/
@[mmp "lem_oai4_c1_graph_support"]
public theorem IsGraphDivisor.coe_supp_eq_preimage_badLocusBase
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) :
    (H.supp : Set G) = (u ≫ fm).base ⁻¹' (badLocusBase fm fp : Set Z) := by
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI := hG.isIntegral
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z :=
    haveI := hZ.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  haveI := Proof_lem_oai4_graph.isProper_plus_of_isNormalizedGraph hG
  haveI := Proof_lem_oai4_graph.isProper_minus_of_isNormalizedGraph hG
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace v
  set g := u ≫ fm
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff] at hx
    obtain ⟨E, hE, hxE⟩ := hx
    rw [Set.mem_preimage, coe_badLocusBase, Set.mem_compl_iff]
    intro hxU
    have hηx : E.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hxE
    refine hE ?_
    rw [DivisorWithCoeffs.coeff_apply]
    exact graphDivisor_apply_eq_zero_of_mem_commonBiregularLocus h E
      ((hηx.map g.continuous).mem_open (commonBiregularLocus fm fp).isOpen hxU)
  · haveI := hD.isNormalVariety_plus.1
    haveI : IsProper sXp :=
      isProper_of_isProjectiveMorphism _ hD.isProjectiveVariety_plus.isProjective
    set sG := v ≫ sXp
    haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace sG
    haveI : IsNoetherian G := {}
    have hTcl : IsClosed (g ⁻¹' (badLocusBase fm fp : Set Z)) :=
      (badLocusBase fm fp).isClosed.preimage g.continuous
    -- closed points are dense in the closed set `g⁻¹(Σ)`
    rw [← closure_inter_closedPoints hTcl]
    refine closure_minimal ?_ H.supp.isClosed
    rintro y ⟨hyB, hyc⟩
    rw [mem_closedPoints_iff] at hyc
    have hz : IsClosed ({g y} : Set Z) := by
      simpa [Set.image_singleton] using g.isClosedMap _ hyc
    set F := g ⁻¹' {g y}
    have hFcl : IsClosed F := hz.preimage g.continuous
    -- the fibre `F` has a second point, since it maps onto a positive-dimensional fibre
    obtain ⟨y', hy'F, hne⟩ : ∃ y' ∈ F, y' ≠ y := by
      haveI := hG.isBirationalMorphism_minus.isDominant
      haveI := hG.isBirationalMorphism_plus.isDominant
      rcases hD.pos_dim_fibre_of_mem_badLocusBase hz hyB with hp | hp
      · exact exists_ne_mem_fibre u.surjective
          (nontrivial_of_topologicalKrullDim_pos hp)
      · have hgy : g y = fp (v y) := apply_apply_eq hG y
        obtain ⟨y', hy', hne⟩ := exists_ne_mem_fibre v.surjective
          (nontrivial_of_topologicalKrullDim_pos (hgy ▸ hp))
        refine ⟨y', ?_, hne⟩
        exact (apply_apply_eq hG y').trans (hy'.trans hgy.symm)
    have hconn : _root_.IsConnected F :=
      (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sG sZ ⟨⟩ hZ g
        (MMP.Mori.isBirationalMorphism_comp_of_isBirational fm u
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
            hD.isBirationalMorphism_minus)
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
            hG.isBirationalMorphism_minus))).2 (g y)
    obtain ⟨η, hηF, hηy, hηne⟩ :=
      exists_specializes_ne_of_isConnected hFcl hconn.isPreconnected rfl hyc hy'F hne
    obtain ⟨c, hηc, hcy, -, hcurve⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sG hηy
      hyc hyc rfl hηne
    have hcF : c ∈ F := hηc.mem_closed hFcl hηF
    exact hcy.mem_closed H.supp.isClosed <|
      point_mem_supp_graphDivisor_of_isContractedBy h sG ⟨c, hcurve⟩ fun x hx =>
        ((specializes_iff_mem_closure.mpr hx).mem_closed hFcl hcF).trans hcF.symm

end MMP.Fourfold

end

namespace Proof_lem_oai4_two_ends

open CategoryTheory AlgebraicGeometry MMP.Mori Topology TopologicalSpace

/-! ### Degrees of pulled-back divisors on curves -/

section Pullback

variable {k : Type u} [Field k] {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]

/-- A proper curve which is not contracted by `u` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (u : V ⟶ T) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t} := by
  rintro ⟨t, ht⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨y, rfl⟩ := hx
  have h1 : (Γ.ι ≫ u) y ∈ Set.range (Γ.ι ≫ u) := ⟨y, rfl⟩
  have h2 : (Γ.ι ≫ u) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ u) := ⟨_, rfl⟩
  rw [ht] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- The image of a proper curve not contracted by `u` is a proper curve. -/
private theorem isProperCurve_map (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : IsProperCurve sT (u Γ.point) := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hpt := not_exists_range_eq_singleton u Γ h
  have hcurve := isCurve_imageι_comp sT φ hpt
  have hker := Γ.ker_comp u
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (u Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (u Γ.point) ≫ sT) := by
    have h1 : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    change IsProper (φ.ker.subschemeι ≫ sT) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- If `u ≫ π` contracts a curve `Γ` that `u` does not contract, then `π` contracts the image
curve `u(Γ)`. -/
private theorem isContractedBy_map {S : Scheme.{u}} (u : V ⟶ T) (hu : u ≫ sT = sV) (π : T ⟶ S)
    (Γ : ProperCurve sV) (h : ¬ Γ.IsContractedBy u) (hΓ : Γ.IsContractedBy (u ≫ π)) :
    (⟨u Γ.point, isProperCurve_map u hu Γ h⟩ : ProperCurve sT).IsContractedBy π := by
  intro y hy
  change y ∈ closure {u Γ.point} at hy
  rw [← ProperCurve.range_comp u hu Γ] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : Γ.ι x ∈ closure {Γ.point} := Γ.range_ι ▸ ⟨x, rfl⟩
  have h1 := hΓ _ hx
  simp only [Scheme.Hom.comp_apply] at h1 ⊢
  exact h1

variable [QuasiCompact sV] [QuasiCompact sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian T] [IsNormal T]

/-- The pull-back of a Cartier divisor has degree zero on a contracted curve. -/
private theorem degreeOn_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy u hu hD hB Γ hΓ

/-- **Projection formula.** On a curve `Γ` not contracted by `u`, with image the proper curve
`Γ'`, `deg_Γ u^*D = [k(Γ) : k(Γ')] · deg_{Γ'} D`. -/
private theorem degreeOn_isPullback_eq_mul (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) =
      (residueFieldDegree u Γ.point : ℤ) * D.degreeOn k sT Γ'.ι Γ'.dim_le hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward u hu hD hB Γ, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hΓ' ▸ Γ'.isProperCurve)]
  obtain ⟨pt, hpt⟩ := Γ'
  simp only at hΓ'
  subst hΓ'
  simp [OneCycle.degree, Finsupp.linearCombination_single, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor has intersection number zero with a contracted
curve. -/
private theorem intersectionNumber_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV)
    {L : QDivisor T} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hB L') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    L'.intersectionNumber k sV Γ.ι Γ.dim_le (h.isQCartier hL) = 0 := by
  obtain ⟨D, D', hDc, hDB, -, hD', hp⟩ := h.exists_cartierIndex hL
  rw [QDivisor.intersectionNumber_eq_of_smul k sV Γ.ι _ _ _ (QDivisor.cartierIndex_pos hL) D'
    (hp.isCartier hDc) hD', degreeOn_isPullback_eq_zero u hu hDc hp Γ hΓ]
  simp

/-- **Projection formula** for `ℚ`-Cartier `ℚ`-divisors:
`(u^*L · Γ) = [k(Γ) : k(Γ')] · (L · Γ')` for the image curve `Γ'` of `Γ`. -/
private theorem intersectionNumber_isPullback_eq_mul (u : V ⟶ T) (hu : u ≫ sT = sV)
    {L : QDivisor T} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hB L') (Γ : ProperCurve sV) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    L'.intersectionNumber k sV Γ.ι Γ.dim_le (h.isQCartier hL) =
      (residueFieldDegree u Γ.point : ℚ) * L.intersectionNumber k sT Γ'.ι Γ'.dim_le hL := by
  obtain ⟨D, D', hDc, hDB, hD, hD', hp⟩ := h.exists_cartierIndex hL
  rw [QDivisor.intersectionNumber_eq_of_smul k sV Γ.ι _ _ _ (QDivisor.cartierIndex_pos hL) D'
    (hp.isCartier hDc) hD', QDivisor.intersectionNumber_eq_of_smul k sT Γ'.ι _ _ _
    (QDivisor.cartierIndex_pos hL) D hDc hD, degreeOn_isPullback_eq_mul u hu hDc hp Γ Γ' hΓ']
  push_cast
  ring

/-- A morphism over `k` which is non-constant on a proper curve has positive residue degree at
the generic point of the curve: `k(C)` is a finite extension of the function field of the image
curve. -/
private theorem residueFieldDegree_pos_of_not_constant (u : V ⟶ T) (hu : u ≫ sT = sV)
    (Γ : ProperCurve sV) (hnc : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t}) :
    0 < residueFieldDegree u Γ.point := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

end Pullback

/-! ### Curves contracted by one end are contracted by the other -/

/-- **Contracted curves.** Let `u_j : V ⟶ T_j` be morphisms over `k` with `u₁ ≫ π₁ = u₂ ≫ π₂`,
and let `A` be both `u₁^* L₁` and `u₂^* L₂`, where `L₂` is positive on every proper curve
contracted by `π₂`. Then `u₂` contracts every proper curve that `u₁` contracts: otherwise the
image curve is contracted by `π₂`, and the projection formula makes `0 = (A · C)` a positive
multiple of `(L₂ · u₂(C)) > 0`. -/
private theorem isContractedBy_of_isPullback_eq {k : Type u} [Field k] {V T₁ T₂ S : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {s₁ : T₁ ⟶ Spec (.of k)} {s₂ : T₂ ⟶ Spec (.of k)}
    [QuasiCompact sV] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsSeparated s₁] [LocallyOfFiniteType s₁] [QuasiCompact s₁] [IsLocallyNoetherian T₁]
    [IsNormal T₁] [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [IsLocallyNoetherian T₂] [IsNormal T₂]
    {u₁ : V ⟶ T₁} {u₂ : V ⟶ T₂} (hu₁ : u₁ ≫ s₁ = sV) (hu₂ : u₂ ≫ s₂ = sV)
    {π₁ : T₁ ⟶ S} {π₂ : T₂ ⟶ S} (hcomp : u₁ ≫ π₁ = u₂ ≫ π₂)
    {L₁ : QDivisor T₁} {L₂ : QDivisor T₂} (hL₁ : L₁.IsQCartier) (hL₂ : L₂.IsQCartier)
    (hpos : ∀ Γ : ProperCurve s₂, Γ.IsContractedBy π₂ →
      0 < L₂.intersectionNumber k s₂ Γ.ι Γ.dim_le hL₂)
    {hB₁ : ∀ Z : irreducibleComponents V, u₁ (componentGenericPoint V Z) ∉ L₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents V, u₂ (componentGenericPoint V Z) ∉ L₂.supp}
    {A : QDivisor V} (h₁ : L₁.IsPullback u₁ hB₁ A) (h₂ : L₂.IsPullback u₂ hB₂ A)
    (C : ProperCurve sV) (hC : C.IsContractedBy u₁) : C.IsContractedBy u₂ := by
  by_contra hc
  have hC₂ : C.IsContractedBy (u₂ ≫ π₂) := by
    rw [← hcomp]
    intro x hx
    simp only [Scheme.Hom.comp_apply, hC x hx]
  have h0 := intersectionNumber_isPullback_eq_zero u₁ hu₁ hL₁ h₁ C hC
  rw [intersectionNumber_isPullback_eq_mul u₂ hu₂ hL₂ h₂ C ⟨_, isProperCurve_map u₂ hu₂ C hc⟩
    rfl] at h0
  have h3 := residueFieldDegree_pos_of_not_constant u₂ hu₂ C (not_exists_range_eq_singleton u₂ C hc)
  have := mul_pos (show (0 : ℚ) < residueFieldDegree u₂ C.point by exact_mod_cast h3)
    (hpos _ (isContractedBy_map u₂ hu₂ π₂ C hc hC₂))
  linarith

/-! ### Pull-backs along a composite -/

/-- Pull-back of `ℚ`-divisors along a dominant composite `q ≫ p` from an irreducible scheme to
an integral one is the composite of the pull-backs. -/
private theorem qDivisor_isPullback_comp
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IrreducibleSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (p : Y ⟶ X) (q : Z ⟶ Y) [IsDominant (q ≫ p)]
    {M : QDivisor X} {MY : QDivisor Y} {MZ : QDivisor Z}
    {hM : ∀ C : irreducibleComponents Y, p (componentGenericPoint Y C) ∉ M.supp}
    {hMY : ∀ C : irreducibleComponents Z, q (componentGenericPoint Z C) ∉ MY.supp}
    (h₁ : M.IsPullback p hM MY) (h₂ : MY.IsPullback q hMY MZ) :
    ∃ hM' : ∀ C : irreducibleComponents Z, (q ≫ p) (componentGenericPoint Z C) ∉ M.supp,
      M.IsPullback (q ≫ p) hM' MZ := by
  refine ⟨MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ M,
    fun m hm D hD hDc => ?_⟩
  obtain ⟨D', hD', hpb⟩ := h₁ m hm D hD hDc
  obtain ⟨D'', hD'', hpb'⟩ := h₂ m hm D' hD' (hpb.isCartier hDc)
  exact ⟨D'', hD'', Proof_lem_oai4_graph.isPullback_comp hpb hpb' _⟩

/-! ### Morphisms constant on connected fibres -/

section Fibres

variable {k : Type u} [Field k] {U V Z : Scheme.{u}} {sU : U ⟶ Spec (.of k)} [IsProper sU]
  [IsLocallyNoetherian U] {g : U ⟶ V} {h : U ⟶ Z}
  (hcurve : ∀ C : ProperCurve sU, C.IsContractedBy g → C.IsContractedBy h)
  (hgc : IsClosedMap g) (hhc : IsClosedMap h)

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h y = h p` for every closed point `p` of `{y}⁻`. -/
private theorem apply_eq_of_specializes {w : V} {y p : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hyp : y ⤳ p) (hp : IsClosed ({p} : Set U)) :
    h y = h p := by
  by_contra hne
  have hZ : IsClosed (h ⁻¹' {h p}) := by
    simpa only [Set.image_singleton] using (hhc _ hp).preimage h.continuous
  obtain ⟨c, hyc, hcp, hcZ, hc⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sU hyp hp hZ
    rfl hne
  have hcy : closure ({c} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyc))
      isClosed_closure
  have hgC : (⟨c, hc⟩ : ProperCurve sU).IsContractedBy g := fun x hx => by
    have h1 := hy (hcy hx)
    have h2 := hy (hcy (subset_closure rfl))
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  have := hcurve _ hgC p (specializes_iff_mem_closure.mp hcp)
  exact hcZ this.symm

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h` is constant on `{y}⁻`. -/
private theorem apply_eq_of_mem_closure [CompactSpace U] {w : V} {y x : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hx : x ∈ closure ({y} : Set U)) : h x = h y := by
  obtain ⟨p, hp, hpc⟩ := (isClosed_closure (s := ({x} : Set U))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hxy : closure ({x} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure
  rw [apply_eq_of_specializes hcurve hhc (hxy.trans hy) (specializes_iff_mem_closure.mpr hp) hpc,
    apply_eq_of_specializes hcurve hhc hy (specializes_iff_mem_closure.mpr (hxy hp)) hpc]

include hcurve hgc hhc in
/-- Two closed points in the same fibre of `g` have the same image under `h`, when the fibres of
`g` are connected. -/
private theorem apply_eq_of_isClosed [CompactSpace U] [NoetherianSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v})) {p q : U}
    (hp : IsClosed ({p} : Set U)) (hpq : g p = g q) : h p = h q := by
  classical
  have hw : IsClosed ({g p} : Set V) := by
    have := hgc _ hp
    rwa [Set.image_singleton] at this
  set F := g ⁻¹' {g p}
  have hF : IsClosed F := hw.preimage g.continuous
  obtain ⟨S, hS, hFS⟩ := NoetherianSpace.exists_finset_irreducible ⟨F, hF⟩
  have hFS' : F = ⋃ t ∈ S, (t : Set U) := by
    have := congrArg (fun T : Closeds U => (T : Set U)) hFS
    rwa [Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
  have hgen : ∀ t ∈ S, ∃ y : U, closure {y} = (t : Set U) := fun t ht =>
    QuasiSober.sober (hS ⟨t, ht⟩) t.isClosed
  haveI : Nonempty U := ⟨p⟩
  choose! η hη using hgen
  have htF : ∀ t ∈ S, closure {η t} ⊆ F := fun t ht => by
    rw [hη t ht, hFS']
    exact Set.subset_biUnion_of_mem (u := fun t : Closeds U => (t : Set U)) ht
  let vals : Set Z := (fun t => h (η t)) '' (S : Set (Closeds U))
  have hvals : vals.Finite := S.finite_toSet.image _
  have hvalc : ∀ z ∈ vals, IsClosed ({z} : Set Z) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨p', hp', hp'c⟩ := (isClosed_closure (s := ({η t} : Set U))).exists_closed_singleton
      ⟨η t, subset_closure rfl⟩
    have := hhc _ hp'c
    rwa [Set.image_singleton, apply_eq_of_mem_closure hcurve hhc (htF t ht) hp'] at this
  have hcover : F ⊆ h ⁻¹' {h p} ∪ h ⁻¹' (⋃ z ∈ vals \ {h p}, {z}) := by
    intro x hx
    rw [hFS'] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    have hxη : h x = h (η t) :=
      apply_eq_of_mem_closure hcurve hhc (htF t ht) ((hη t ht).symm ▸ hxt)
    by_cases hxp : h x = h p
    · exact Or.inl hxp
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨h x, ⟨⟨t, ht, hxη.symm⟩, hxp⟩, rfl⟩)
  have hu : IsClosed (h ⁻¹' {h p}) := by
    simpa only [Set.image_singleton] using (hhc _ hp).preimage h.continuous
  have hv : IsClosed (h ⁻¹' (⋃ z ∈ vals \ {h p}, {z})) :=
    ((hvals.diff).isClosed_biUnion fun z hz => hvalc z hz.1).preimage h.continuous
  have hdisj : F ∩ (h ⁻¹' {h p} ∩ h ⁻¹' (⋃ z ∈ vals \ {h p}, {z})) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - hx ⟨z, ⟨-, hz⟩, rfl⟩
    exact hz hx
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hconn (g p)) _ _ hu hv hcover hdisj
    with hsub | hsub
  · exact (hsub (show q ∈ F from hpq.symm)).symm
  · have := hsub (show p ∈ F from rfl)
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff] at this
    obtain ⟨z, ⟨-, hz⟩, rfl⟩ := this
    exact absurd rfl hz

include hcurve hgc hhc in
/-- `h` is constant on every fibre of `g`, when the fibres of `g` are connected. -/
private theorem apply_eq_of_apply_eq [CompactSpace U] [NoetherianSpace U] [JacobsonSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v})) {x x' : U} (hxx : g x = g x') :
    h x = h x' := by
  suffices H : ∀ x x' : U, g x = g x' → h x ⤳ h x' from
    (H x x' hxx).antisymm (H x' x hxx.symm) |>.eq
  intro x x' hxx
  by_contra hn
  have hC : IsClosed (h ⁻¹' closure {h x}) := isClosed_closure.preimage h.continuous
  have hx'O : x' ∈ (h ⁻¹' closure {h x})ᶜ := fun H => hn (specializes_iff_mem_closure.mpr H)
  have hx' : x' ∈ closure (closure {x'} ∩ closedPoints U) := by
    rw [JacobsonSpace.closure_inter_closedPoints isClosed_closure]
    exact subset_closure rfl
  obtain ⟨p, hpO, hpx', hpc⟩ := mem_closure_iff.mp hx' _ hC.isOpen_compl hx'O
  rw [mem_closedPoints_iff] at hpc
  have hgp : g p ∈ g '' closure {x} := by
    have hsub : closure {g x} ⊆ g '' closure {x} :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)
        (hgc _ isClosed_closure)
    refine hsub (specializes_iff_mem_closure.mp ?_)
    rw [hxx]
    exact (specializes_iff_mem_closure.mpr hpx').map g.continuous
  obtain ⟨q₀, hq₀, hgq₀⟩ := hgp
  have hwc : IsClosed ({g p} : Set V) := by
    have := hgc _ hpc
    rwa [Set.image_singleton] at this
  obtain ⟨q, ⟨hqx, hgq⟩, hqc⟩ := (isClosed_closure.inter (hwc.preimage g.continuous) :
    IsClosed (closure {x} ∩ g ⁻¹' {g p})).exists_closed_singleton ⟨q₀, hq₀, hgq₀⟩
  have hpq : h q = h p := apply_eq_of_isClosed hcurve hgc hhc hconn hqc hgq
  have hqC : h q ∈ closure {h x} :=
    specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hqx).map h.continuous)
  exact hpO (show h p ∈ closure {h x} from hpq ▸ hqC)

end Fibres

end Proof_lem_oai4_two_ends

section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry MMP.Mori Topology TopologicalSpace
open Proof_lem_oai4_two_ends

/-- **A relatively ample end is a morphic image.** Let `π_j : V_j ⟶ Z` (`j = 1, 2`) be projective
morphisms of normal projective varieties over `k`, `D₁` a `π₁`-nef and `D₂` a `π₂`-ample
`ℚ`-Cartier `ℚ`-divisor, and `q_j : W ⟶ V_j` birational morphisms from a smooth projective
variety `W` with `q₁ ≫ π₁ = q₂ ≫ π₂`. Let `A_j = q_j^* D_j`. If `A₁ + F₁ = A₂ + F₂` for effective
`ℚ`-divisors `F_j` on `W` with `q_{j*} F_j = 0`, then there is a morphism `h : V₁ ⟶ V₂` over `Z`
with `q₁ ≫ h = q₂` and `D₁ = h^* D₂`. -/
@[mmp "lem_oai4_two_ends"]
public theorem exists_comp_eq_and_isPullback_of_add_eq_add_of_hasRelativelyAmpleMultiple
    (k : Type u) [Field k] {Z V₁ V₂ W : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (sV₁ : V₁ ⟶ Spec (.of k)) (sV₂ : V₂ ⟶ Spec (.of k))
    [QuasiCompact sV₁] [IsLocallyNoetherian V₁] [IsNormal V₁]
    [CompactSpace V₂] [IsLocallyNoetherian V₂] [IsNormal V₂]
    [IsLocallyNoetherian W] [IsNormal W]
    (hZ : IsNormalVariety k sZ) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    (hV₁ : IsNormalVariety k sV₁) (hV₁p : MMP.Mori.IsProjectiveVariety k sV₁)
    (hV₂ : IsNormalVariety k sV₂) (hV₂p : MMP.Mori.IsProjectiveVariety k sV₂)
    (π₁ : V₁ ⟶ Z) (π₂ : V₂ ⟶ Z) (hπ₁ : IsProjectiveMorphism π₁) (hπ₂ : IsProjectiveMorphism π₂)
    (hsπ₁ : π₁ ≫ sZ = sV₁) (hsπ₂ : π₂ ≫ sZ = sV₂)
    {D₁ : QDivisor V₁} {D₂ : QDivisor V₂} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (hn₁ : D₁.IsRelativelyNef sV₁ π₁) (ha₂ : D₂.HasRelativelyAmpleMultiple π₂)
    (q₁ : W ⟶ V₁) (q₂ : W ⟶ V₂)
    (hWp : MMP.Mori.IsProjectiveVariety k (q₁ ≫ sV₁)) (hWs : IsSmoothScheme (q₁ ≫ sV₁))
    (hq₁ : IsBirationalMorphism q₁) (hq₂ : IsBirationalMorphism q₂)
    (hsq : q₁ ≫ sV₁ = q₂ ≫ sV₂) (hcomp : q₁ ≫ π₁ = q₂ ≫ π₂)
    {A₁ A₂ : QDivisor W}
    (hA₁₀ : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉ D₁.supp)
    (hA₂₀ : ∀ T : irreducibleComponents W, q₂ (componentGenericPoint W T) ∉ D₂.supp)
    (hA₁ : D₁.IsPullback q₁ hA₁₀ A₁) (hA₂ : D₂.IsPullback q₂ hA₂₀ A₂)
    {F₁ F₂ : QDivisor W} (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (hF₁₀ : RationalMap.transformDivisor (X := W) q₁.toRationalMap F₁ = 0)
    (hF₂₀ : RationalMap.transformDivisor (X := W) q₂.toRationalMap F₂ = 0)
    (heq : A₁ + F₁ = A₂ + F₂) :
    ∃ h : V₁ ⟶ V₂, q₁ ≫ h = q₂ ∧ h ≫ π₂ = π₁ ∧
      ∃ hD : ∀ T : irreducibleComponents V₁, h (componentGenericPoint V₁ T) ∉ D₂.supp,
        D₂.IsPullback h hD D₁ := by
  haveI : AlgebraicGeometry.IsVariety k sV₁ := hV₁.1
  haveI : AlgebraicGeometry.IsVariety k sV₂ := hV₂.1
  haveI : AlgebraicGeometry.IsProjectiveVariety k (q₁ ≫ sV₁) := hWp
  haveI : IsIntegral W := hWp.toIsVariety.toIsIntegral
  haveI : IsIntegral V₁ := hV₁.1.toIsIntegral
  haveI : IsIntegral V₂ := hV₂.1.toIsIntegral
  have hW : IsNormalVariety k (q₁ ≫ sV₁) := ⟨hWp.toIsVariety, inferInstance⟩
  haveI : IsProper (q₁ ≫ sV₁) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  haveI : IsProper q₁ := IsProper.of_comp q₁ sV₁
  haveI : IsProper (q₂ ≫ sV₂) := hsq ▸ inferInstance
  haveI : IsProper q₂ := IsProper.of_comp q₂ sV₂
  haveI : CompactSpace V₁ := QuasiCompact.compactSpace_of_compactSpace sV₁
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q₁ ≫ sV₁)
  -- `D₂` is positive on curves contracted by `π₂`, hence `π₂`-nef, so `q₁^* D₁ = q₂^* D₂`
  have hpos : ∀ Γ : ProperCurve sV₂, Γ.IsContractedBy π₂ →
      0 < D₂.intersectionNumber k sV₂ Γ.ι Γ.dim_le hD₂ := fun Γ hΓ =>
    Proof_lem_oai4_c1_graph_support.intersectionNumber_pos_of_hasRelativelyAmpleMultiple sV₂ hD₂
      ha₂ Γ hΓ
  have hn₂ : D₂.IsRelativelyNef sV₂ π₂ :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV₂ hD₂ fun Γ hΓ =>
      (hpos Γ hΓ).le
  have hA : A₁ = A₂ := MMP.Fourfold.eq_of_isPullback_of_add_eq_add_of_isRelativelyNef k sZ sV₁
    sV₂ hZ hZp hV₁ hV₁p hV₂ hV₂p π₁ π₂ hπ₁ hπ₂ hsπ₁ hsπ₂ hD₁ hD₂ hn₁ hn₂ q₁ q₂ hWp hWs hq₁ hq₂
    hsq hcomp hA₁₀ hA₂₀ hA₁ hA₂ hF₁ hF₂ hF₁₀ hF₂₀ heq
  -- `q₂` contracts every curve that `q₁` contracts
  have hcurve := isContractedBy_of_isPullback_eq rfl hsq.symm hcomp hD₁ hD₂ hpos
    (hA ▸ hA₁) hA₂
  -- `q₂` is constant on the connected fibres of `q₁`, and rigidity gives `h`
  haveI : IsNoetherian W := (isNoetherian_iff W).mpr ⟨inferInstance, inferInstance⟩
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (q₁ ≫ sV₁)
  obtain ⟨hiso, hconn⟩ := MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (q₁ ≫ sV₁) sV₁ hWp.toIsVariety hV₁ q₁ hq₁
  haveI : IsIso q₁.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ q₁.c fun U => hiso U.unop
  obtain ⟨h, hh, -⟩ := MMP.existsUnique_comp_eq_of_isIso_c q₁ q₂ fun x x' hxx =>
    apply_eq_of_apply_eq hcurve q₁.isClosedMap q₂.isClosedMap
      (fun v => (hconn v).isPreconnected) hxx
  have hπ : h ≫ π₂ = π₁ := by
    obtain ⟨g, -, hg⟩ := MMP.existsUnique_comp_eq_of_isIso_c q₁ (q₁ ≫ π₁) fun x x' hxx => by
      simp only [Scheme.Hom.comp_apply, hxx]
    rw [hg (h ≫ π₂) (show q₁ ≫ h ≫ π₂ = _ by rw [← Category.assoc, hh, hcomp]), hg π₁ rfl]
  subst hh
  -- `D₁ = q_{1*} q₁^* D₁ = q_{1*} q₁^* h^* D₂ = h^* D₂`
  haveI : IsDominant (q₁ ≫ h) := hq₂.isDominant
  haveI : IsDominant q₁ := hq₁.isDominant
  haveI : IsDominant h := IsDominant.of_comp q₁ h
  have hD : ∀ T : irreducibleComponents V₁, h (componentGenericPoint V₁ T) ∉ D₂.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h D₂
  have hB := QDivisor.isPullback_pullback (f := h) hD₂ hD
  have hBq := hB.isQCartier hD₂
  have hgen : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉
      (D₂.pullback hD₂ hD).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q₁ _
  have hB' := QDivisor.isPullback_pullback hBq hgen
  obtain ⟨hM', hcompB⟩ := qDivisor_isPullback_comp h q₁ hB hB'
  have hB'A : (D₂.pullback hD₂ hD).pullback hBq hgen = A₂ :=
    (hD₂.existsUnique_isPullback hM').unique hcompB hA₂
  have e1 := MMP.Positivity.transformDivisor_of_isPullback hV₁ hW hq₁ hBq hgen hB'
  have e2 := MMP.Positivity.transformDivisor_of_isPullback hV₁ hW hq₁ hD₁ hA₁₀ hA₁
  have hBD : D₂.pullback hD₂ hD = D₁ := by rw [← e1, ← e2, hB'A, hA]
  exact ⟨h, rfl, hπ, hD, hBD ▸ hB⟩

end MMP.Fourfold

end

end
