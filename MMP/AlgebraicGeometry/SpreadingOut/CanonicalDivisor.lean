module

public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelProperties
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# Canonical divisors and crepant boundaries through local equations

For an integral normal variety `X` over a field, the divisorial sheaf of a divisor restricts to
the divisorial sheaf of its restriction to a dense open subscheme. Together with the divisor of a
nonzero rational top form this gives a canonical divisor of `X` whenever the sheaf of top
differential forms is invertible on an open subscheme whose complement has codimension at least
two. The second part computes discrepancies through local equations: if `m (K + Δ)` has a local
equation `φ`, then the discrepancy along a prime divisor of a birational model is read off from
the order of the pull-back of `φ` and the order of the pulled-back top form, and a family of
such local equations covering the exceptional divisors determines the crepant boundary.

## Main results

* `MMP.Mori.Divisor.divisorialSheafRestrictOpenIso`: `𝒪_U(D|_U) ≅ 𝒪_X(D)|_U` for a nonempty
  open subscheme `U` of a normal integral scheme.
* `MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety`: a normal variety over a perfect field
  has a canonical divisor.
* `MMP.Spreading.linearlyEquivalent_topFormDivisor`: the divisor of a nonzero rational top form
  is linearly equivalent to every canonical divisor.
* `MMP.Spreading.isDiscrepancy_of_linearlyEquivalent`: discrepancies are unchanged when the
  canonical divisor is replaced by a linearly equivalent one.
* `MMP.Spreading.isCrepantBoundary_of_localEquations`: the crepant boundary from local
  equations.
* `MMP.Spreading.ord_eq_of_isDiscrepancy`: the order of a pulled-back local equation along a
  prime divisor, from the discrepancy.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace MMP.Spreading

noncomputable section

namespace CanonExist

open MMP.Mori

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

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

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem gp_specializes_aux {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_gp_aux {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

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
  (Y.presheaf.stalkSpecializes (gp_specializes_aux Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective_aux {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (gp_specializes_aux Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_gp_aux Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (gp_specializes_aux E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (gp_specializes_aux E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (gp_specializes_aux E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective_aux E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

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
  exact ((genericPoint_spec U.toScheme).specializes trivial).mem_open V.isOpen hx

/-- The irreducible component `X` of the integral scheme `X`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_gp_aux Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective_aux Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_gp_aux Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_gp_aux Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (gp_specializes_aux _)).hom
      ((X.presheaf.stalkSpecializes (specializes_gp_aux _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_gp_aux Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

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
    rw [ordGE_iff_evFF, ordGE_iff_evFF, evFF_restrictRF U V ψ _
        ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
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
  refine ⟨fun h P hP => ?_,
    fun h E' hE' => (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))⟩
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
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to a nonempty open subscheme is
the restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
public def _root_.MMP.Mori.Divisor.divisorialSheafRestrictOpenIso (D : Divisor X) (U : X.Opens)
    [Nonempty U] :
    Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι :=
  haveI := isDominant_opens_ι U
  (@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm

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

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
public theorem _root_.MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety {K : Type u}
    [Field K] [PerfectField K] {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] (hS : IsNormalVariety K sS)
    {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := isDominant_opens_ι T
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : IsIntegral T := inferInstance
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  let e₀ := Divisor.divisorialSheafRestrictOpenIso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

/-- A nonzero rational top form is nonzero as a `1`-canonical form. -/
private theorem toPluriForms_ne_zero {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {ω : RationalTopForms sX n} (hω : ω ≠ 0) :
    ω.toPluriForms sX ≠ 0 := by
  letI := functionFieldAlgebra sX
  intro h
  apply hω
  have h' : (PiTensorProduct.tprod X.functionField
      fun _ : Fin 1 => (ω : ⋀[X.functionField]^n Ω[X.functionField⁄k])) = 0 := h
  have h'' := congrArg (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) h'
  rwa [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h''

/-- The divisor of a nonzero rational top form is linearly equivalent to every canonical
divisor. -/
public theorem linearlyEquivalent_topFormDivisor {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {ω : RationalTopForms sX n} (hω : ω ≠ 0) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) : (topFormDivisor sX ω).LinearlyEquivalent K := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  obtain ⟨ω₀, hω₀0, hω₀⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hω0 := toPluriForms_ne_zero hω
  set c := (ZTensorPower.basis b 1).repr (ω.toPluriForms sX) () with hc_def
  set c₀ := (ZTensorPower.basis b 1).repr ω₀ () with hc₀_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hc₀ : c₀ ≠ 0 := repr_ne_zero_of_ne_zero b hω₀0
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero hc (inv_ne_zero hc₀))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 _ hω0
  have e2 := hN 1 ω₀ hω₀0
  rw [← hc_def] at e1
  rw [← hc₀_def, hω₀ Γ] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul hc (inv_ne_zero hc₀), ← zpow_neg_one, ord_zpow _ hc₀, coeff_topFormDivisor]
  omega

/-- **The divisor of a nonzero rational top form is a canonical divisor** of a normal variety over
a perfect field. -/
public theorem isCanonicalDivisor_topFormDivisor {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {ω : RationalTopForms sX n} (hω : ω ≠ 0) :
    (topFormDivisor sX ω).IsCanonicalDivisor sX n := by
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX hX hn
  exact hK.of_linearlyEquivalent (linearlyEquivalent_topFormDivisor hX hn hω hK)

end CanonExist

section CrepantCriterion

open MMP.Mori

/-- **The discrepancy computed by a local equation.** Let `ω ≠ 0` be a rational top form of a
normal variety `Z` of dimension `n` over a perfect field, `D = m(div ω + Δ)` a Cartier divisor with
local equation `φ` on an open `U`, and `μ : W ⟶ Z` birational from a normal variety. For a prime
divisor `F` of `W` with `μ(η_F) ∈ U`, the discrepancy of `F` over `(Z, Δ)` with respect to `div ω`
is `(v_F(μ^*φ⁻¹) + m ord_F(μ^*ω)) / m`. -/
private theorem isDiscrepancy_of_localEquation {k : Type u} [Field k] [PerfectField k]
    {Z W : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [LocallyOfFiniteType sZ] (hZ : IsNormalVariety k sZ) {n : ℕ} (hn : topologicalKrullDim Z = n)
    {μ : W ⟶ Z} (hW : IsNormalVariety k (μ ≫ sZ)) (hμ : IsBirationalMorphism μ)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (hnW : topologicalKrullDim W = n)
    {Δ : QDivisor Z} {ω : RationalTopForms sZ n} (hω : ω ≠ 0) {m : ℕ} (hm : 0 < m)
    {D : Divisor Z} (hD : Divisor.toQDivisor D = (m : ℤ) •
        (Divisor.toQDivisor (topFormDivisor sZ ω) + Δ))
    (hDc : D.IsCartier) {U : Z.Opens} {φ : Z.functionField} (hφ : φ ≠ 0)
    (hloc : ∀ Γ : Mori.PrimeDivisor Z, (Γ.support ∩ U).Nonempty → D.coeff Γ = Z.ord φ
        Γ.genericPoint)
    (F : Mori.PrimeDivisor W) (hF : μ F.genericPoint ∈ U) :
    haveI := hμ.isDominant
    IsDiscrepancy sZ n (topFormDivisor sZ ω) Δ ⟨W, μ, hW, hμ, F⟩
      (((W.ord (functionFieldMap μ φ⁻¹) F.genericPoint : ℤ) : ℚ) / m +
        (F.ordForm (pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ)) : ℚ)) := by
  haveI := hμ.isDominant
  letI := functionFieldAlgebra sZ
  have : LocallyOfFiniteType (μ ≫ sZ) := hW.1.toLocallyOfFiniteType
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hφi : φ⁻¹ ≠ 0 := inv_ne_zero hφ
  let τ : RationalPluriForms sZ n m := φ⁻¹ • MMP.Fourfold.formPow
    (ω : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) m
  obtain ⟨B⟩ := MMP.Fourfold.exists_basis_topForms (sX := sZ) hn
  let b := basisOfSpanSingleton (span_singleton_eq_top_of_basis_unit B hω) hω
  have hb : b () = ω := basisOfSpanSingleton_apply _ _ _
  have hne : (φ⁻¹ • MMP.Fourfold.formPow (b ()) m : Mori.PluriForms k Z.functionField n m) ≠ 0 := by
    intro h0
    have := MMP.Fourfold.repr_smul_formPow b m φ⁻¹
    rw [h0] at this
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, zero_eq_inv] at this
    exact hφ this.symm
  have hτ0 : τ ≠ 0 := by rwa [hb] at hne
  have hcoeff : ∀ Γ : Mori.PrimeDivisor Z, (D.coeff Γ : ℚ) =
      m * ((Γ.ordForm (ω.toPluriForms sZ) : ℚ) + Δ.coeff Γ) := by
    intro Γ
    have := congrArg (fun G : QDivisor Z => G.coeff Γ) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_topFormDivisor] at this
    rw [this, zsmul_eq_mul]
    push_cast
    ring
  refine ⟨hZ, CanonExist.isCanonicalDivisor_topFormDivisor hZ hn hω, m, hm, ⟨D, hD, hDc⟩, U,
    hF, τ, ⟨hτ0, fun Γ hΓ => ?_⟩, ?_⟩
  · have e := ordForm_smul_formPow hn Γ ω hω hφi m
    change Γ.ordForm τ = _ at e
    rw [e, ← zpow_neg_one, MMP.Mori.ord_zpow _ hφ, ← hloc Γ hΓ]
    push_cast
    rw [hcoeff Γ]
    ring
  · have e := ordForm_pullback_smul_formPow sZ μ hμ.functionFieldMap_bijective hn hnW F ω hω
      hφi m
    change (m : ℚ) * _ = ((F.ordForm (pullbackRationalPluriForms sZ μ τ) : ℤ) : ℚ)
    change _ = (((F.ordForm (pullbackRationalPluriForms sZ μ (d := n) (m := m)
      (φ⁻¹ • MMP.Fourfold.formPow (ω : ⋀[Z.functionField]^n Ω[Z.functionField⁄k]) m))) : ℤ) : ℚ)
    rw [e]
    push_cast
    field_simp

/-- Discrepancies are unchanged when the canonical divisor is replaced by a linearly equivalent
one. -/
public theorem isDiscrepancy_of_linearlyEquivalent {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {n : ℕ} {K K' : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX} {a : ℚ}
    (h : IsDiscrepancy sX n K Δ D a) (hKK' : K'.LinearlyEquivalent K) :
    IsDiscrepancy sX n K' Δ D a := by
  obtain ⟨hX, hK, m, hm, ⟨C, hC, hCc⟩, U, hU, τ, hτ, ha⟩ := h
  obtain ⟨φ, hφ⟩ := hKK'
  refine ⟨hX, hK.of_linearlyEquivalent ⟨φ, hφ⟩, m, hm, ⟨C + (m : ℤ) • principalDivisor φ, ?_,
    hCc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩, U, hU, τ, hτ, ha⟩
  have hK' : K' = K + principalDivisor φ := by
    rw [← hφ]
    abel
  rw [map_add, map_zsmul, hC, hK', map_add, smul_add, smul_add, smul_add]
  abel

/-- **The crepant boundary from local equations.** Let `ω ≠ 0` be a rational top form of a normal
variety `Z` of dimension `n` over a perfect field, `D = m(div ω + Δ)` a Cartier divisor and
`μ : W ⟶ Z` birational from a normal variety of dimension `n`. If every prime divisor `F` of `W`
has, near `μ(η_F)`, a local equation `φ` of `D` with `v_F(μ^*φ) = m (ord_F(μ^*ω) + coeff_F Δ_W)`,
then `Δ_W` is the crepant boundary of `(Z, Δ)` for the canonical divisor `div ω`. -/
public theorem isCrepantBoundary_of_localEquations {k : Type u} [Field k] [PerfectField k]
    {Z W : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] [LocallyOfFiniteType sZ] (hZ : IsNormalVariety k sZ) {n : ℕ}
    (hn : topologicalKrullDim Z = n) {μ : W ⟶ Z} (hW : IsNormalVariety k (μ ≫ sZ))
    (hμ : IsBirationalMorphism μ) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hnW : topologicalKrullDim W = n) {Δ : QDivisor Z} {ΔW : QDivisor W}
    {ω : RationalTopForms sZ n} (hω : ω ≠ 0) {m : ℕ} (hm : 0 < m) {D : Divisor Z}
    (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor (topFormDivisor sZ ω) + Δ))
    (hDc : D.IsCartier)
    (H : ∀ F : Mori.PrimeDivisor W, ∃ (U : Z.Opens) (φ : Z.functionField), φ ≠ 0 ∧
      μ F.genericPoint ∈ U ∧
      (∀ Γ : Mori.PrimeDivisor Z, (Γ.support ∩ U).Nonempty → D.coeff Γ = Z.ord φ Γ.genericPoint) ∧
      haveI := hμ.isDominant
      (W.ord (functionFieldMap μ φ) F.genericPoint : ℚ) =
        m * ((F.ordForm (pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ)) : ℚ) + ΔW.coeff F)) :
    IsCrepantBoundary sZ n (topFormDivisor sZ ω) Δ μ hW hμ ΔW := by
  haveI := hμ.isDominant
  intro F
  obtain ⟨U, φ, hφ, hF, hloc, hord⟩ := H F
  have h := isDiscrepancy_of_localEquation hZ hn hW hμ hnW hω hm hD hDc hφ hloc F hF
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hφ' : functionFieldMap μ φ ≠ 0 := (map_ne_zero _).mpr hφ
  convert h using 1
  rw [map_inv₀, ← zpow_neg_one, MMP.Mori.ord_zpow _ hφ']
  push_cast
  rw [hord]
  field_simp
  ring

/-- **Discrepancies over `K` from local equations.** If `F` has discrepancy `a` over `(Z, Δ)` with
respect to a canonical divisor `K₀`, and `φ` is a local equation of `D = m(div ω + Δ)` near
`μ(η_F)`, then `v_F(μ^*φ) = m (ord_F(μ^*ω) - a)`. -/
public theorem ord_eq_of_isDiscrepancy {k : Type u} [Field k] [PerfectField k]
    {Z W : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] [LocallyOfFiniteType sZ] (hZ : IsNormalVariety k sZ) {n : ℕ}
    (hn : topologicalKrullDim Z = n) {μ : W ⟶ Z} (hW : IsNormalVariety k (μ ≫ sZ))
    (hμ : IsBirationalMorphism μ) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hnW : topologicalKrullDim W = n) {Δ : QDivisor Z} {K₀ : Divisor Z}
    (hK₀ : K₀.IsCanonicalDivisor sZ n)
    {ω : RationalTopForms sZ n} (hω : ω ≠ 0) {m : ℕ} (hm : 0 < m) {D : Divisor Z}
    (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor (topFormDivisor sZ ω) + Δ))
    (hDc : D.IsCartier) {U : Z.Opens} {φ : Z.functionField} (hφ : φ ≠ 0)
    (hloc : ∀ Γ : Mori.PrimeDivisor Z, (Γ.support ∩ U).Nonempty → D.coeff Γ = Z.ord φ
        Γ.genericPoint)
    (F : Mori.PrimeDivisor W) (hF : μ F.genericPoint ∈ U) {a : ℚ}
    (ha : IsDiscrepancy sZ n K₀ Δ ⟨W, μ, hW, hμ, F⟩ a) :
    haveI := hμ.isDominant
    (W.ord (functionFieldMap μ φ) F.genericPoint : ℚ) =
      m * ((F.ordForm (pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ)) : ℚ) - a) := by
  haveI := hμ.isDominant
  have h := isDiscrepancy_of_localEquation hZ hn hW hμ hnW hω hm hD hDc hφ hloc F hF
  have ha' := isDiscrepancy_of_linearlyEquivalent ha
    (CanonExist.linearlyEquivalent_topFormDivisor hZ hn hω hK₀)
  have e := MMP.Mori.IsDiscrepancy.eq ha' h
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hφ' : functionFieldMap μ φ ≠ 0 := (map_ne_zero _).mpr hφ
  rw [e, map_inv₀, ← zpow_neg_one, MMP.Mori.ord_zpow _ hφ']
  push_cast
  field_simp
  ring

end CrepantCriterion

end

end MMP.Spreading
