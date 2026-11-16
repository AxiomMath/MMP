module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.Morphisms.ProductWithLine
import MMP.AlgebraicGeometry.Divisor.ProductLineQFactorial
import MMP.Analysis.Complex.CauchyOsgoodLaurent
import MMP.AlgebraicGeometry.Resolution.SncComplementResolution
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.DivisorialValuationFiniteRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite

/-!
# Log discrepancies along étale maps, and products of terminal varieties with `ℙ¹`

This file proves two comparisons of log discrepancies under maps that do not change the local
geometry along divisors.

*Étale maps.* Let `q : Y_e ⟶ Y_0` be a dominant étale morphism of normal varieties over a field
`k` of characteristic zero, with `K_{Y_0}` `ℚ`-Cartier. An étale morphism is flat and locally
quasi-finite, so it preserves coheights: it sends the generic point of a prime divisor `Γ'` of
`Y_e` to the generic point of a prime divisor `Γ` of `Y_0`, and `𝒪_{Y_0,Γ} ⟶ 𝒪_{Y_e,Γ'}` is a
formally unramified extension of discrete valuation rings, so `v_{Γ'} ∘ q^* = v_Γ`. The tame
order formula `ord_{E'}(ι^*ω) = e · ord_E(ω) + (e - 1)` for an extension of discrete valuations
of ramification index `e`, here with `e = 1`, gives `div(q^*ω) = q^* div(ω)`; with
`K_{Y_0} = div ω` this canonical divisor of `Y_e` is `q^* K_{Y_0}`, which is `ℚ`-Cartier. For a
normalized divisorial valuation `w` of `k(Y_e)`, the restriction `w|_{k(Y_0)}` is `ord_E` for a
prime divisor `E` of a smooth model over `Y_0` (the centre of `w` on the base change of that model
is unramified over `E`), and the same tame formula on the local rings of divisors realizing `w`
and its restriction shows that `a(w; Y_e, 0) = a(w|_{k(Y_0)}; Y_0, 0)`.

*Products with the projective line.* Let `Y` be a terminal complex variety and `P = Y × ℙ¹`. A top
form `ω` on `Y` gives the product form `dz ∧ pr^*ω` on `P`, for the coordinate `z` of an affine
chart of `ℙ¹`; its divisor `K_P` is a canonical divisor of `P` that agrees with `pr^*K_Y` over the
chart, so `mK_P` is Cartier when `mK_Y` is. Log discrepancies over `P` are read on `W × ℙ¹` for a
strong resolution `μ : W ⟶ Y`, which is an isomorphism over the smooth locus of `Y`. The prime
divisors of `W × ℙ¹` are the products `E × ℙ¹` and the divisors dominating `W`; only the products
with `E` exceptional over `Y` are exceptional over `P`, and for those
`a(E × ℙ¹; P, 0) = a(E; Y, 0) > 1`.

## Main results

* `MMP.Intersection.isLogDiscrepancy_iff_of_etale`: along a dominant étale morphism `q` of normal
  varieties, `K_{Y_e}` is `ℚ`-Cartier, the restriction of a normalized divisorial valuation is
  normalized divisorial, and the two log discrepancies agree.
* `MMP.Fourfold.IsTerminalVariety.pullback_projectiveLine`: `Y × ℙ¹` is a terminal variety when
  `Y` is.

## Implementation notes

* `Y_e` lies over `k` through `q ≫ s₀`, so that `q` is a morphism over `k`, and "`Y_0` is
  `ℚ`-Gorenstein" is `MMP.Mori.IsPair s₀ 0`. The restriction `w|_{k(Y_0)}` is
  `w.comap (functionFieldMap q)`. Log discrepancies are predicates on values for a divisor
  realizing a valuation (`MMP.Intersection.IsLogDiscrepancy`), so the equality of log
  discrepancies is stated for any divisors with proper structure maps realizing `w` and its
  restriction. The base is any field of characteristic zero rather than `ℂ`.
* The comparison of log discrepancies along `q` is made on arbitrary models realizing the two
  valuations rather than on a base change `W ×_{Y_0} Y_e`; the log discrepancy depends only on the
  valuation, so the computations agree.
* `ℙ¹_ℂ` is `AlgebraicGeometry.projectiveLine ℂ` and `Y × ℙ¹` is the fibre product over `Spec ℂ`,
  structured over `ℂ` by `pr₁ ≫ s_Y`. Terminality is `MMP.Fourfold.IsTerminalVariety`, which
  contains that some canonical divisor is `ℚ`-Cartier; since canonical divisors are linearly
  equivalent, every canonical divisor of `Y × ℙ¹`, in particular `pr₁^* K_Y + pr₂^* K_{ℙ¹}`, is
  then `ℚ`-Cartier. The integrality and normality of `Y × ℙ¹` are part of the conclusion.
* Terminality of `Y × ℙ¹` is checked on the smooth model `W × ℙ¹` rather than on a log resolution
  of `P`: a divisor over `P` is realized on a smooth model over `W × ℙ¹`, where
  `K_{W × ℙ¹} - (μ × id)^*K_P` is anti-effective.
* Both proofs need a canonical divisor on a normal variety over a perfect field; it is built on
  the smooth locus and closed up, in `MMP.Mori.CanonicalDivisorExistence`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Proposition 5.20
-/

universe u

namespace MMP.Mori.CanonicalDivisorExistence

open CategoryTheory AlgebraicGeometry Limits MMP.Mori MMP.Fourfold

section CanonicalDivisorExistence

open Opposite TopologicalSpace

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
  (Y.presheaf.stalkSpecializes
    (genericPoint_specializes (componentGenericPoint Y Z.1))).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective
      (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z))).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes
        (genericPoint_specializes (componentGenericPoint Y E.component))).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes
          (genericPoint_specializes (componentGenericPoint Y E.component))).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes
            (genericPoint_specializes (componentGenericPoint Y E.component))).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

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
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [componentGenericPoint_eq_genericPoint]; exact h⟩

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
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
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

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι :=
    Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
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
  let e₀ := (@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom T KS)).symm
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

end MMP.Mori.CanonicalDivisorExistence

/-! ## Log discrepancies along étale maps -/

namespace Proof_lem_oai4_c2_etale_discrepancy

open CategoryTheory MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor IsVariety
open MMP.Mori.CanonicalDivisorExistence

/-! ### Discrete valuation rings -/

section Algebra

open IsLocalRing KaehlerDifferential TensorProduct

/-- A field map `ι : K₁ → K₂` carrying the image of `A₁` into that of `A₂` restricts to a ring
map `A₁ → A₂`, for `A₂ ⊆ K₂` (a fraction ring). -/
private theorem exists_ringHom_of_range {K₁ K₂ A₁ A₂ : Type*} [Field K₁] [Field K₂] [CommRing A₁]
    [CommRing A₂] [Algebra A₁ K₁] [Algebra A₂ K₂] [IsFractionRing A₂ K₂] (ι : K₁ →+* K₂)
    (h : ∀ a₁ : A₁, ∃ a₂ : A₂, algebraMap A₂ K₂ a₂ = ι (algebraMap A₁ K₁ a₁)) :
    ∃ φ : A₁ →+* A₂, ∀ a, algebraMap A₂ K₂ (φ a) = ι (algebraMap A₁ K₁ a) := by
  choose φ hφ using h
  have inj : Function.Injective (algebraMap A₂ K₂) := IsFractionRing.injective A₂ K₂
  exact ⟨{ toFun := φ
           map_one' := inj (by rw [hφ]; simp)
           map_mul' := fun a b => inj (by rw [hφ]; simp [hφ])
           map_zero' := inj (by rw [hφ]; simp)
           map_add' := fun a b => inj (by rw [hφ]; simp [hφ]) }, hφ⟩

open Polynomial in
/-- **The residue extension of an algebraic extension of valuation rings is algebraic.** Let
`A → B` be a local homomorphism from a discrete valuation ring `A` to a local domain `B`, with
fraction fields `K` of `A` and `L ⊇ B`, compatibly with an algebraic extension `K → L`. Then
`κ(B)` is algebraic over `κ(A)`: an algebraic equation of `b ∈ B` over `A`, divided by its
content, has a unit coefficient, and reduces to a nonzero equation of `b̄` over `κ(A)`. -/
private theorem isAlgebraic_residueField_of_isAlgebraic {A B K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hBL : Function.Injective (algebraMap B L))
    (hcomp : ∀ a, algebraMap B L (algebraMap A B a) = algebraMap K L (algebraMap A K a)) :
    Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := by
  classical
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := A)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply hAL
    rw [IsScalarTower.algebraMap_apply A B L, hxy, ← IsScalarTower.algebraMap_apply]
  refine ⟨fun y => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp0, hpb⟩ : IsAlgebraic A (algebraMap B L b) :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  have hp : aeval b p = 0 := hBL (by rw [map_zero, ← aeval_algebraMap_apply]; exact hpb)
  set q := p.primPart
  have hq : aeval b q = 0 := by
    have h1 := hp
    rw [p.eq_C_content_mul_primPart, map_mul, aeval_C] at h1
    refine (mul_eq_zero.mp h1).resolve_left ?_
    rw [map_eq_zero_iff _ hAB]
    exact (content_eq_zero_iff).not.mpr hp0
  have hqprim := p.isPrimitive_primPart
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hex : ∃ j, q.coeff j ∉ maximalIdeal A := by
    by_contra hcon
    push Not at hcon
    have hdvd : C ϖ ∣ q := by
      rw [C_dvd_iff_dvd_coeff]
      intro j
      have := hcon j
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.mem_span_singleton] at this
      exact this
    exact hϖ.not_isUnit (hqprim ϖ hdvd)
  obtain ⟨j, hj⟩ := hex
  refine ⟨q.map (residue A), fun h0 => hj ?_, ?_⟩
  · have := congrArg (fun r => r.coeff j) h0
    simp only [coeff_map, coeff_zero] at this
    exact (residue_eq_zero_iff _).mp this
  · have key : ∀ x : A, algebraMap (ResidueField A) (ResidueField B) (residue A x) =
        residue B (algebraMap A B x) := fun x => rfl
    rw [aeval_def, eval₂_map]
    have : (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) =
        (residue B).comp (algebraMap A B) := RingHom.ext key
    rw [this, ← hom_eval₂, ← aeval_def, hq, map_zero]

/-- If `f` is onto modulo `x₀` (its kernel lies in `R ∙ x₀`) and the `f (y i)` span, then `x₀` and
the `y i` span. -/
private theorem span_cons_eq_top_of_ker_le {R V Q : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup Q] [Module R Q] (f : V →ₗ[R] Q) (x₀ : V)
    (hker : LinearMap.ker f ≤ R ∙ x₀)
    {r : ℕ} (y : Fin r → V) (hy : Submodule.span R (Set.range (f ∘ y)) = ⊤) :
    Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : f v ∈ (Submodule.span R (Set.range y)).map f := by
    rw [Submodule.map_span, ← Set.range_comp, hy]; trivial
  obtain ⟨w, hw, hfw⟩ := hv
  have hsub : Submodule.span R (Set.range y) ≤
      Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
  have h0 : R ∙ x₀ ≤ Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ rfl; exact ⟨0, by simp⟩)
  have : v - w ∈ LinearMap.ker f := by simp [hfw]
  have := h0 (hker this)
  simpa using Submodule.add_mem _ this (hsub hw)

/-- The wedge of a spanning family of `n` vectors generates the `n`-th exterior power. -/
private theorem span_singleton_ιMulti_eq_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (v : Fin n → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R n v} = ⊤ := by
  refine eq_top_iff.mpr ((exteriorPower.ιMulti_span_of_span R n M hv).symm.le.trans ?_)
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have : ∀ i, ∃ j, v j = a i := fun i => ha (Set.mem_range_self i)
  choose g hg using this
  have ha' : a = v ∘ g := funext fun i => (hg i).symm
  subst ha'
  by_cases hinj : Function.Injective g
  · let σ := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj)
    have : v ∘ g = v ∘ σ := rfl
    rw [this, AlternatingMap.map_perm]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    rw [AlternatingMap.map_eq_zero_of_eq _ _ (show (v ∘ g) i = (v ∘ g) j by simp [hij]) hne]
    exact Submodule.zero_mem _

/-- Changing the first vector by an element of the span of the others, and scaling it, scales the
wedge. -/
private theorem ιMulti_cons_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : ℕ} (y : Fin r → M) {x x' : M} (c : R) (hx : x - c • x' ∈ Submodule.span R (Set.range y)) :
    exteriorPower.ιMulti R (r + 1) (Fin.cons x y) =
      c • exteriorPower.ιMulti R (r + 1) (Fin.cons x' y) := by
  let L : M →ₗ[R] ⋀[R]^(r + 1) M :=
    (exteriorPower.ιMulti R (r + 1)).toMultilinearMap.toLinearMap (Fin.cons 0 y) 0
  have hL : ∀ z, L z = exteriorPower.ιMulti R (r + 1) (Fin.cons z y) := fun z => by
    simp [L, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]
  have hker : Submodule.span R (Set.range y) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hL]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ) (by simp)
      (Fin.succ_ne_zero i).symm
  have := hker hx
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  rw [← hL, ← hL, this]

/-- For a local ring with principal maximal ideal `(π)`, the kernel of
`κ ⊗ Ω_{R/k} → Ω_{κ/k}` is spanned by `1 ⊗ dπ`. -/
private theorem ker_mapBaseChange_le {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    LinearMap.ker (mapBaseChange k R (ResidueField R)) ≤
      (ResidueField R) ∙ ((1 : ResidueField R) ⊗ₜ[R] D k R π) := by
  intro y hy
  obtain ⟨z, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange k R _ (residue_surjective) y).mp hy
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ z
  have hx' : x ∈ maximalIdeal R := by
    rwa [← ker_residue]
  rw [hπ] at hx'
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  rw [kerCotangentToTensor_toCotangent, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
    ← algebraMap_smul (ResidueField R) π, ← algebraMap_smul (ResidueField R) a]
  have : algebraMap R (ResidueField R) π = 0 := by
    rw [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq, ker_residue, hπ]
    exact Ideal.mem_span_singleton_self π
  rw [this, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- If `R` and its residue field are formally smooth over `k`, then `1 ⊗ dπ ≠ 0` in
`κ ⊗ Ω_{R/k}` for `π ∈ 𝔪 \ 𝔪²`. -/
private theorem tmul_D_ne_zero {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (ResidueField R)]
    {π : R} (hπ : π ∈ maximalIdeal R) (hπ2 : π ∉ maximalIdeal R ^ 2) :
    ((1 : ResidueField R) ⊗ₜ[R] D k R π) ≠ 0 := by
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := R)
    (A := ResidueField R) residue_surjective).mp inferInstance
  intro h0
  have hmem : π ∈ RingHom.ker (algebraMap R (ResidueField R)) := by
    rwa [IsLocalRing.ResidueField.algebraMap_eq, ker_residue]
  have h1 : kerCotangentToTensor k R (ResidueField R)
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent ⟨π, hmem⟩) = 0 := by
    rwa [kerCotangentToTensor_toCotangent]
  have h2 := congrArg l h1
  rw [← LinearMap.comp_apply, hl, LinearMap.id_apply, map_zero, Ideal.toCotangent_eq_zero] at h2
  apply hπ2
  have : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, ker_residue]
  rwa [← this]

/-- Nakayama for a free module of rank `r`: `r` vectors spanning `κ ⊗ M` span `M`. -/
private theorem span_eq_top_of_span_tmul {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Free R M] {r : ℕ} (hr : Module.finrank R M = r)
    (v : Fin r → M)
    (hv : Submodule.span (ResidueField R) (Set.range fun i => (1 : ResidueField R) ⊗ₜ[R] v i) = ⊤) :
    Submodule.span R (Set.range v) = ⊤ := by
  have hfr : Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) = r := by
    rw [Module.finrank_baseChange, hr]
  let b := basisOfTopLeSpanOfCardEqFinrank _ hv.ge (by simp [hfr])
  exact span_eq_top_of_tmul_eq_basis v b (fun i => by simp [b])

/-- **The tame computation.** For a local extension `A → B` of discrete valuation rings over a
field `k` of characteristic zero, with `Ω_{A/k}` and `Ω_{B/k}` free of rank `n` and separable
residue extension, if `t ↦ a s^e` for uniformizers `t`, `s` and a unit `a`, then some generators
of the top forms satisfy `h^* σ_A = w s^{e-1} σ_B` for a unit `w`. -/
private theorem exists_topFormsMap_eq_unit_mul_pow_smul {k A B : Type*} [Field k] [CharZero k]
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (ResidueField A)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] [Module.Free B Ω[B⁄k]] [Module.Finite B Ω[B⁄k]]
    {n : ℕ} (hA : Module.finrank A Ω[A⁄k] = n) (hB : Module.finrank B Ω[B⁄k] = n)
    {t : A} (ht : Irreducible t) {s : B} (hs : Irreducible s) {a : Bˣ} {e : ℕ}
    (he : algebraMap A B t = a * s ^ e) :
    ∃ σA : ⋀[A]^n Ω[A⁄k], Submodule.span A {σA} = ⊤ ∧
      ∃ σB : ⋀[B]^n Ω[B⁄k], Submodule.span B {σB} = ⊤ ∧
        ∃ w : Bˣ, topFormsMap k A B n σA = ((w : B) * s ^ (e - 1)) • σB := by
  classical
  have htm : t ∈ maximalIdeal A := (mem_maximalIdeal t).mpr ht.not_isUnit
  have hmA : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have hmB : maximalIdeal B = Ideal.span {s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs
  have ht2 : t ∉ maximalIdeal A ^ 2 := by
    rw [hmA, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have : t * (1 - t * c) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · exact ht.ne_zero h
    · exact ht.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, by linear_combination -h⟩)
  have hx₀ := tmul_D_ne_zero (k := k) htm ht2
  have hV : Module.finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) = n := by
    rw [Module.finrank_baseChange, hA]
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, Module.finrank_zero_iff] at hV
    exact hx₀ (Subsingleton.elim _ _)
  let fA := mapBaseChange k A (ResidueField A)
  have hfA : Function.Surjective fA := mapBaseChange_surjective k A _ residue_surjective
  have hfx₀ : fA ((1 : ResidueField A) ⊗ₜ[A] D k A t) = 0 := by
    simp [fA, mapBaseChange_tmul, (residue_eq_zero_iff t).mpr htm]
  have hkerA : LinearMap.ker fA = ResidueField A ∙ ((1 : ResidueField A) ⊗ₜ[A] D k A t) :=
    le_antisymm (ker_mapBaseChange_le hmA)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hfx₀)
  have hQ : Module.finrank (ResidueField A) Ω[ResidueField A⁄k] = r := by
    have h := LinearMap.finrank_range_add_finrank_ker fA
    rw [LinearMap.range_eq_top.mpr hfA, finrank_top, hkerA, finrank_span_singleton hx₀, hV] at h
    omega
  have : Module.Finite (ResidueField A) Ω[ResidueField A⁄k] := Module.Finite.of_surjective fA hfA
  have hspanQ : Submodule.span (ResidueField A)
      (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x)) = ⊤ := by
    refine eq_top_iff.mpr ((span_range_derivation k (ResidueField A)).symm.le.trans
      (Submodule.span_mono ?_))
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨x, rfl⟩
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (ResidueField A)
    (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x))
  let bb := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspanQ])
  have : Finite b := Module.Finite.finite_basis bb
  have : Fintype b := Fintype.ofFinite b
  let eqv : Fin r ≃ b :=
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis bb, hQ])).symm
  have hu : ∀ i, ∃ x : A, D k (ResidueField A) (algebraMap A (ResidueField A) x) = (eqv i).1 :=
    fun i => hbs (eqv i).2
  choose u hu using hu
  let bQ : Module.Basis (Fin r) (ResidueField A) Ω[ResidueField A⁄k] := bb.reindex eqv.symm
  have hbQ : ∀ i, bQ i = D k (ResidueField A) (algebraMap A (ResidueField A) (u i)) := fun i => by
    simp only [bQ, bb, Module.Basis.reindex_apply, Module.Basis.mk_apply, Equiv.symm_symm]
    exact (hu i).symm
  have hu' : Submodule.span (ResidueField A)
      (Set.range (fA ∘ fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (u i))) = ⊤ := by
    rw [← bQ.span_eq]; congr 1; ext x
    simp [fA, mapBaseChange_tmul, hbQ]
  have hVspan := span_cons_eq_top_of_ker_le fA _ hkerA.le _ hu'
  set vA : Fin (r + 1) → Ω[A⁄k] := Fin.cons (D k A t) fun i => D k A (u i) with hvA_def
  have hvA : Submodule.span A (Set.range vA) = ⊤ := by
    refine span_eq_top_of_span_tmul hA vA ?_
    have : (fun i => (1 : ResidueField A) ⊗ₜ[A] vA i) =
        Fin.cons ((1 : ResidueField A) ⊗ₜ[A] D k A t) fun i => 1 ⊗ₜ[A] D k A (u i) := by
      funext i; cases i using Fin.cases <;> simp [vA]
    rwa [this]
  -- the side of `B`
  have : Algebra.FormallyEtale (ResidueField A) (ResidueField B) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  let fB := mapBaseChange k B (ResidueField B)
  let bQ' := (KaehlerDifferential.isBaseChange_of_formallyEtale k (ResidueField A)
    (ResidueField B)).basis bQ
  have hu'B : Submodule.span (ResidueField B)
      (Set.range (fB ∘ fun i => (1 : ResidueField B) ⊗ₜ[B] D k B (algebraMap A B (u i)))) = ⊤ := by
    rw [← bQ'.span_eq]; congr 1; ext x
    simp [fB, bQ', mapBaseChange_tmul, hbQ, IsBaseChange.basis_apply]
  have hWspan := span_cons_eq_top_of_ker_le fB _ (ker_mapBaseChange_le (k := k) hmB) _ hu'B
  set vB : Fin (r + 1) → Ω[B⁄k] := Fin.cons (D k B s) fun i => D k B (algebraMap A B (u i))
    with hvB_def
  have hvB : Submodule.span B (Set.range vB) = ⊤ := by
    refine span_eq_top_of_span_tmul hB vB ?_
    have : (fun i => (1 : ResidueField B) ⊗ₜ[B] vB i) =
        Fin.cons ((1 : ResidueField B) ⊗ₜ[B] D k B s)
          fun i => 1 ⊗ₜ[B] D k B (algebraMap A B (u i)) := by
      funext i; cases i using Fin.cases <;> simp [vB]
    rwa [this]
  refine ⟨_, span_singleton_ιMulti_eq_top vA hvA, _, span_singleton_ιMulti_eq_top vB hvB, ?_⟩
  rw [topFormsMap_ιMulti]
  have hcomp : (fun i => KaehlerDifferential.map k k A B (vA i)) =
      Fin.cons (D k B (algebraMap A B t)) fun i => D k B (algebraMap A B (u i)) := by
    funext i; cases i using Fin.cases <;> simp [vA]
  rw [hcomp]
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, pow_zero, mul_one] at he
    exact ht.not_isUnit ((isUnit_map_iff (algebraMap A B) t).mp (he ▸ a.isUnit))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp
    (hvB ▸ Submodule.mem_top : D k B (a : B) ∈ Submodule.span B (Set.range vB))
  have hsm : s * c 0 ∈ maximalIdeal B :=
    Ideal.mul_mem_right _ _ ((mem_maximalIdeal s).mpr hs.not_isUnit)
  have hek : IsUnit ((e + 1 : ℕ) : B) := by
    have : ((e + 1 : ℕ) : B) = algebraMap k B ((e + 1 : ℕ) : k) := by simp
    rw [this]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e))).map _
  have hw : IsUnit ((a : B) * ((e + 1 : ℕ) : B) + s * c 0) := by
    by_contra h
    have := (maximalIdeal B).sub_mem ((mem_maximalIdeal _).mpr h) hsm
    rw [add_sub_cancel_right, mem_maximalIdeal] at this
    exact this (a.isUnit.mul hek)
  refine ⟨hw.unit, ?_⟩
  rw [IsUnit.unit_spec, Nat.add_sub_cancel]
  apply ιMulti_cons_eq_smul
  rw [he, Derivation.leibniz, Derivation.leibniz_pow, ← hc, Fin.sum_univ_succ]
  have hv0 : vB 0 = D k B s := rfl
  have hvs : ∀ i, vB i.succ = D k B (algebraMap A B (u i)) := fun i => rfl
  simp only [hv0, hvs, Nat.add_sub_cancel]
  have : (a : B) • ((e + 1) • s ^ e • D k B s) +
      s ^ (e + 1) • (c 0 • D k B s + ∑ i : Fin r, c i.succ • D k B (algebraMap A B (u i))) -
      ((↑a * ((e + 1 : ℕ) : B) + s * c 0) * s ^ e) • D k B s =
      s ^ (e + 1) • ∑ i : Fin r, c i.succ • D k B (algebraMap A B (u i)) := by
    rw [← Nat.cast_smul_eq_nsmul B]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end Algebra

/-- Pulling a form back along `A → K → K'` agrees with pulling it back along `A → B → K'` when
the two composites `A → K'` agree. -/
private theorem topFormsMap_topFormsMap_eq {k A B K K' : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Field K] [Field K'] [Algebra k A] [Algebra k B] [Algebra k K] [Algebra k K']
    [Algebra A B] [Algebra A K] [Algebra B K'] [Algebra K K'] [IsScalarTower k A B]
    [IsScalarTower k A K] [IsScalarTower k B K'] [IsScalarTower k K K']
    (hφ : ∀ x : A, algebraMap B K' (algebraMap A B x) = algebraMap K K' (algebraMap A K x))
    {n : ℕ} (σ : ⋀[A]^n Ω[A⁄k]) :
    topFormsMap k K K' n (topFormsMap k A K n σ) =
      topFormsMap k B K' n (topFormsMap k A B n σ) := by
  have hΩ : ∀ y : Ω[A⁄k], KaehlerDifferential.map k k K K' (KaehlerDifferential.map k k A K y) =
      KaehlerDifferential.map k k B K' (KaehlerDifferential.map k k A B y) := by
    intro y
    have hy : y ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp [hφ]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul a x _ hx =>
      have e1 : KaehlerDifferential.map k k A K (a • x) =
          algebraMap A K a • KaehlerDifferential.map k k A K x := by
        rw [map_smul, algebraMap_smul]
      have e2 : KaehlerDifferential.map k k A B (a • x) =
          algebraMap A B a • KaehlerDifferential.map k k A B x := by
        rw [map_smul, algebraMap_smul]
      rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
        ← algebraMap_smul K' (algebraMap A B a), hφ]
  have hs : σ ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    simp only [topFormsMap_ιMulti, hΩ]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    have e1 : topFormsMap k A K n (a • x) = algebraMap A K a • topFormsMap k A K n x := by
      rw [map_smul, algebraMap_smul]
    have e2 : topFormsMap k A B n (a • x) = algebraMap A B a • topFormsMap k A B n x := by
      rw [map_smul, algebraMap_smul]
    rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
      ← algebraMap_smul K' (algebraMap A B a), hφ]

/-- The order along a prime divisor of `u ϖ^n`, for a unit `u` and a uniformizer `ϖ`, is `n`. -/
private theorem ord_algebraMap_unit_mul_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : PrimeDivisor Y) {ϖ : E.localRing} (hϖ : Irreducible ϖ)
    (w : E.localRingˣ) (n : ℕ) :
    Y.ord (algebraMap E.localRing Y.functionField (w * ϖ ^ n)) E.genericPoint = n := by
  have := E.isDiscreteValuationRing_localRing
  have hϖ0 : algebraMap E.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have h1 : Y.ord (algebraMap E.localRing Y.functionField ϖ) E.genericPoint = 1 := by
    have := E.divisorialValuation_algebraMap_of_irreducible hϖ
    rw [E.divisorialValuation_eq_exp_neg_ord hϖ0] at this
    have := WithZero.exp_injective this
    omega
  have hw0 : algebraMap E.localRing Y.functionField w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr w.ne_zero
  rw [map_mul, map_pow, Scheme.ord_mul hw0 (pow_ne_zero _ hϖ0),
    E.ord_algebraMap_of_isUnit w.isUnit, ← zpow_natCast, ord_zpow _ hϖ0, h1]
  ring

/-- If one valuation is the `e`-th power of another along a ring map, then `e ≠ 0`: at `0` the
relation reads `0 = 0 ^ e`. -/
private theorem ne_zero_of_valuation_eq_pow {K K' Γ : Type*} [Field K] [Field K']
    [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {v' : Valuation K' Γ} {ι : K →+* K'}
    {e : ℕ} (he : ∀ g, v' (ι g) = v g ^ e) : e ≠ 0 := by
  rintro rfl
  simpa using he 0

/-- If `v_{E'}(x') = v_E(x) ^ e` for nonzero rational functions `x`, `x'`, then
`ord_{E'}(x') = e · ord_E(x)`. -/
private theorem ord_eq_mul_of_divisorialValuation_eq_pow {Y Y' : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') {x : Y.functionField} {x' : Y'.functionField}
    {e : ℕ} (h : E'.divisorialValuation x' = E.divisorialValuation x ^ e) (hx : x ≠ 0)
    (hx' : x' ≠ 0) : Y'.ord x' E'.genericPoint = e * Y.ord x E.genericPoint := by
  rw [E'.divisorialValuation_eq_exp_neg_ord hx', E.divisorialValuation_eq_exp_neg_ord hx,
    ← WithZero.exp_nsmul, WithZero.exp_inj, smul_neg, nsmul_eq_mul] at h
  linear_combination -h

/-! ### Function fields and forms -/

section Forms

/-- A dominant, locally quasi-finite morphism of integral schemes, locally of finite type,
induces a finite extension of function fields: the generic point of the source is the only point
over the generic point of the target. -/
private theorem finite_functionField {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (h : Y ⟶ X)
    [IsDominant h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    letI := functionFieldMapAlgebra h
    Module.Finite X.functionField Y.functionField := by
  have hgen : ∀ x : Y, h x = genericPoint X → x = genericPoint Y := fun x hx => by
    have hsp := genericPoint_specializes x
    have h₀ : h (genericPoint Y) = genericPoint X :=
      ((hx ▸ hsp.map h.continuous).antisymm (genericPoint_specializes _)).eq
    exact (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite h hsp (h₀.trans hx.symm)).symm
  have H := (trdeg_functionField_eq_zero_iff_finite h).mp
    (trdeg_functionField_eq_zero_of_eq_genericPoint h hgen)
  convert H using 3
  exact congrArg RingHom.toAlgebra (dominantFunctionFieldMap_eq_functionFieldMap h).symm

/-- The pull-back of a nonzero form along a pull-back generator is nonzero. -/
private theorem pullbackForms_ne_zero {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) {m : ℤ} {τ : PluriForms k K d m}
    (hτ : τ ≠ 0) : pullbackForms (K' := K') m τ ≠ 0 := by
  intro h0
  have h1 := repr_pullbackFormsAlong hω m τ
  rw [← pullbackForms_eq hω m τ, h0] at h1
  simp only [map_zero, Finsupp.zero_apply] at h1
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap K K').injective).mp h1.symm)

/-- The pull-back `ι^*τ` of rational `m`-canonical forms along a `k`-embedding
`ι : k(Y) → k(Y')` of function fields. -/
private noncomputable def pullbackAlong {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k)) [IsIntegral Y] [IsIntegral Y']
    (ι : Y.functionField →+* Y'.functionField)
    (hι : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      ∀ c : k, algebraMap k Y'.functionField c = ι (algebraMap k Y.functionField c))
    {d : ℕ} {m : ℤ} (τ : RationalPluriForms sY d m) : RationalPluriForms sY' d m :=
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sY'
  letI := ι.toAlgebra
  haveI : IsScalarTower k Y.functionField Y'.functionField := IsScalarTower.of_algebraMap_eq hι
  pullbackForms (K := Y.functionField) (K' := Y'.functionField) m τ

/-- **The tame canonical-order formula along an extension of discrete valuations.** Let `Y`,
`Y'` be normal varieties of dimension `n` over a field `k` of characteristic zero, `ι` a
`k`-embedding `k(Y) → k(Y')` of their function fields, and `E`, `E'` prime divisors with
`v_{E'} ∘ ι = v_E ^ e`. Then every nonzero rational `m`-canonical form `τ` of `Y` satisfies
`ord_{E'}(ι^* τ) = e · ord_E(τ) + m (e - 1)`. -/
private theorem ordForm_pullbackAlong_eq {k : Type u} [Field k] [CharZero k]
    {Y Y' : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k))
    [IsIntegral Y] [IsIntegral Y'] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
    [IsNormal Y] [IsNormal Y'] (hY : IsNormalVariety k sY) (hY' : IsNormalVariety k sY')
    {n : ℕ} (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n)
    (hd' : letI := functionFieldAlgebra sY'; (Algebra.trdeg k Y'.functionField).toNat = n)
    (htr : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      Algebra.trdeg k Y.functionField = Algebra.trdeg k Y'.functionField)
    (ι : Y.functionField →+* Y'.functionField)
    (hι : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      ∀ c : k, algebraMap k Y'.functionField c = ι (algebraMap k Y.functionField c))
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') {e : ℕ}
    (he : ∀ g, E'.divisorialValuation (ι g) = E.divisorialValuation g ^ e)
    {m : ℤ} {τ : RationalPluriForms sY n m} (hτ : τ ≠ 0) :
    E'.ordForm (pullbackAlong sY sY' ι hι τ) = e * E.ordForm τ + m * (e - 1) := by
  classical
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sY'
  letI := ι.toAlgebra
  haveI : IsScalarTower k Y.functionField Y'.functionField := IsScalarTower.of_algebraMap_eq hι
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sY' := hY'.1.toLocallyOfFiniteType
  haveI := essFiniteType_functionField (sX := sY)
  haveI : Algebra.IsAlgebraic Y.functionField Y'.functionField := isAlgebraic_of_trdeg_eq k htr
  letI := stalkAlgebra sY E.genericPoint
  letI := stalkAlgebra sY' E'.genericPoint
  haveI := isScalarTower_stalk_functionField sY E.genericPoint
  haveI := isScalarTower_stalk_functionField sY' E'.genericPoint
  haveI := E.isDiscreteValuationRing_localRing
  haveI := E'.isDiscreteValuationRing_localRing
  obtain ⟨_, _⟩ := E.formallySmooth_localRing (sX := sY)
  obtain ⟨_, _⟩ := E.free_kaehlerDifferential_localRing (sX := sY)
  obtain ⟨_, _⟩ := E'.free_kaehlerDifferential_localRing (sX := sY')
  have hrkA := (E.finrank_kaehlerDifferential_localRing (sX := sY)).trans hd
  have hrkB := (E'.finrank_kaehlerDifferential_localRing (sX := sY')).trans hd'
  have he0 : e ≠ 0 := ne_zero_of_valuation_eq_pow he
  have hord : ∀ g : Y.functionField, g ≠ 0 →
      Y'.ord (algebraMap Y.functionField Y'.functionField g) E'.genericPoint =
        e * Y.ord g E.genericPoint := fun g hg =>
    ord_eq_mul_of_divisorialValuation_eq_pow E E' (he g) hg ((map_ne_zero _).mpr hg)
  -- the local extension `𝒪_{Y,E} → 𝒪_{Y',E'}`
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range (A₁ := E.localRing) (A₂ := E'.localRing)
    (algebraMap Y.functionField Y'.functionField) fun a => by
      have h1 : E.divisorialValuation (algebraMap E.localRing Y.functionField a) ≤ 1 :=
        (E.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
      have h2 : E'.divisorialValuation (algebraMap Y.functionField Y'.functionField
          (algebraMap E.localRing Y.functionField a)) ≤ 1 := by
        change E'.divisorialValuation (ι _) ≤ 1
        rw [he]
        exact (pow_le_one_iff he0).mpr h1
      obtain ⟨b, hb⟩ := (E'.divisorialValuation_le_one_iff _).mp h2
      exact ⟨b, hb⟩
  letI : Algebra E.localRing E'.localRing := φ.toAlgebra
  have hφ' : ∀ x : E.localRing, algebraMap E'.localRing Y'.functionField
      (algebraMap E.localRing E'.localRing x) =
        algebraMap Y.functionField Y'.functionField (algebraMap E.localRing Y.functionField x) :=
    hφ
  haveI : IsScalarTower k E.localRing E'.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c =>
      IsFractionRing.injective E'.localRing Y'.functionField ?_
    rw [hφ', ← IsScalarTower.algebraMap_apply k E.localRing Y.functionField,
      ← IsScalarTower.algebraMap_apply k Y.functionField Y'.functionField,
      ← IsScalarTower.algebraMap_apply k E'.localRing Y'.functionField]
  haveI : IsLocalHom (algebraMap E.localRing E'.localRing) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : E.divisorialValuation (algebraMap E.localRing Y.functionField a) < 1 :=
      (E.divisorialValuation_algebraMap_lt_one_iff a).mpr
        ((IsLocalRing.mem_maximalIdeal a).mpr hna)
    have h2 : E'.divisorialValuation (algebraMap E'.localRing Y'.functionField
        (algebraMap E.localRing E'.localRing a)) < 1 := by
      rw [hφ']
      change E'.divisorialValuation (ι _) < 1
      rw [he]
      exact (pow_lt_one_iff he0).mpr h1
    exact (IsLocalRing.mem_maximalIdeal _).mp
      ((E'.divisorialValuation_algebraMap_lt_one_iff _).mp h2) ha
  haveI : Algebra.FormallySmooth k (IsLocalRing.ResidueField E.localRing) := by
    haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField E.localRing) :=
      Algebra.EssFiniteType.comp k E.localRing _
    exact Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField E.localRing)
      (IsLocalRing.ResidueField E'.localRing) :=
    isAlgebraic_residueField_of_isAlgebraic (K := Y.functionField) (L := Y'.functionField)
      (IsFractionRing.injective _ _) hφ'
  haveI : CharZero (IsLocalRing.ResidueField E.localRing) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField E.localRing)
      (IsLocalRing.ResidueField E'.localRing) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- uniformizers and the ramification index
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible E'.localRing
  have hϖ1 : Y.ord (algebraMap E.localRing Y.functionField ϖ) E.genericPoint = 1 := by
    simpa using ord_algebraMap_unit_mul_pow E hϖ 1 1
  have hϖ0 : algebraMap E.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hφϖ : algebraMap E.localRing E'.localRing ϖ ≠ 0 := by
    intro h0
    have := hφ' ϖ
    rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (RingHom.injective _)] at this
    exact hϖ0 this
  obtain ⟨e₀, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ hs
  have he₀ : e₀ = e := by
    have h1 := hord _ hϖ0
    rw [← hφ', ha, ord_algebraMap_unit_mul_pow E' hs, hϖ1, mul_one] at h1
    exact_mod_cast h1
  -- the top forms
  obtain ⟨σA, hσA, σB, hσB, w, hw⟩ :=
    exists_topFormsMap_eq_unit_mul_pow_smul (k := k) hrkA hrkB hϖ hs ha
  have h0A := E.topFormsMap_ne_zero (sX := sY) hd hσA
  have h0B := E'.topFormsMap_ne_zero (sX := sY') hd' hσB
  rw [E.ordForm_eq τ hσA h0A, E'.ordForm_eq _ hσB h0B]
  set c : Y'.functionField := algebraMap E'.localRing Y'.functionField (w * s ^ (e₀ - 1))
    with hc_def
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (mul_ne_zero w.ne_zero (pow_ne_zero _ hs.ne_zero))
  have hcomp : topFormsMap k Y.functionField Y'.functionField n
      (topFormsMap k E.localRing Y.functionField n σA) =
      c • topFormsMap k E'.localRing Y'.functionField n σB := by
    rw [topFormsMap_topFormsMap_eq hφ', hw, map_smul, algebraMap_smul]
  have hωA : IsPullbackGenerator Y'.functionField
      (topFormsMap k E.localRing Y.functionField n σA) :=
    ⟨span_singleton_topFormsMap (nonZeroDivisors _) hσA, by
      rw [hcomp, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc),
        span_singleton_topFormsMap (nonZeroDivisors _) hσB], by
      rw [hcomp]; exact smul_ne_zero hc h0B⟩
  have hpb : pullbackAlong sY sY' ι hι τ = pullbackFormsAlong hωA m τ := pullbackForms_eq hωA m τ
  rw [hpb]
  have hb : basisOfSpanSingleton hωA.2.1 hωA.2.2 () =
      c • topFormsBasis E'.localRing hσB h0B () := by
    simp [hcomp]
  have key := ZTensorPower.basis_repr_of_eq_smul hb m (pullbackFormsAlong hωA m τ)
  have hr := repr_pullbackFormsAlong hωA m τ
  have hfB : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA m τ) =
      c ^ m * algebraMap Y.functionField Y'.functionField
        (formCoeff E.localRing hσA h0A τ) := by
    have h1 : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA m τ) =
        c ^ m * (ZTensorPower.basis (basisOfSpanSingleton hωA.2.1 hωA.2.2) m).repr
          (pullbackFormsAlong hωA m τ) () := by
      unfold formCoeff
      rw [key, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero m hc), one_mul]
    rw [h1, hr]
    rfl
  have hf : formCoeff E.localRing hσA h0A τ ≠ 0 := fun h0 =>
    hτ ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  rw [hfB, Scheme.ord_mul (zpow_ne_zero _ hc) ((map_ne_zero _).mpr hf), MMP.Mori.ord_zpow _ hc,
    hord _ hf, hc_def, ord_algebraMap_unit_mul_pow E' hs, he₀,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr he0)]
  push_cast
  ring

end Forms

/-! ### Centres and pull-backs of Cartier divisors -/

section Centre

/-- **The centre upstairs lies over the centre downstairs.** If `D'` is a divisor over `Y` and
`D` one over a variety `X`, with `v_{D'} ∘ h^* = v_D ^ e` for `e ≠ 0`, then `h` maps the centre
of `D'` on `Y` to the centre of `D` on `X`: the local ring of `X` at `h(c_Y(v_{D'}))` is dominated
by `v_D`, and centres are unique on a separated scheme. -/
private theorem map_center_eq_of_valuation_eq_pow {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant h]
    (hX : MMP.Mori.IsVariety k sX) {D : DivisorOver k sX} {D' : DivisorOver k (h ≫ sX)}
    {e : ℕ} (he0 : e ≠ 0)
    (he : ∀ g, D'.valuation (functionFieldMap h g) = D.valuation g ^ e) :
    h (D'.f D'.E.genericPoint) = D.f D.E.genericPoint := by
  haveI := hX.toIsSeparated
  refine (MMP.Positivity.DivisorOver.eq_of_dominates sX D.valuation (x := D.f D.E.genericPoint)
    (x' := h (D'.f D'.E.genericPoint))
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl) (fun a => ?_)
    (fun a ha => ?_)).symm
  · have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl
      ((h.stalkMap (D'.f D'.E.genericPoint)).hom a)
    rw [← functionFieldMap_algebraMap_stalk, he] at h1
    exact (pow_le_one_iff he0).mp h1
  · have hmem : (h.stalkMap (D'.f D'.E.genericPoint)).hom a ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
    have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl _ hmem
    rw [← functionFieldMap_algebraMap_stalk, he] at h1
    exact (pow_lt_one_iff he0).mp h1

/-- **The coefficient of an iterated pull-back.** Let `C` be a Cartier divisor on `X`, `C₁` its
pull-back along `h : Y ⟶ X` and `C₂` the pull-back of `C₁` along `f : Y' ⟶ Y`. If `φ` is a local
equation of `C` on an open `U` containing `h(f(η_E))`, then `coeff_E(C₂) = v_E(f^* h^* φ)`: a
local equation of `C₁` near `f(η_E)` and `h^* φ` have the same order along every prime divisor
through `f(η_E)`, so by algebraic Hartogs their pull-backs have the same order along `E`. -/
private theorem coeff_isPullback_isPullback_eq {X Y Y' : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] {h : Y ⟶ X} [IsDominant h]
    {f : Y' ⟶ Y} [IsDominant f] {C : Divisor X} (hCc : C.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ C.supp}
    {C₁ : Divisor Y} (h₁ : C.IsPullback h hB C₁)
    {hB₁ : ∀ Z : irreducibleComponents Y', f (componentGenericPoint Y' Z) ∉ C₁.supp}
    {C₂ : Divisor Y'} (h₂ : C₁.IsPullback f hB₁ C₂) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : PrimeDivisor Y')
    (hU : h (f E.genericPoint) ∈ U) (Z : irreducibleComponents X) :
    C₂.coeff E = Y'.ord (functionFieldMap f (functionFieldMap h
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X)))) E.genericPoint := by
  classical
  obtain ⟨W, hW, ψ, hψ⟩ := (h₁.isCartier hCc) (f E.genericPoint)
  let Z₁ := pointComponent (f E.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h₂ hψ E hW Z₁]
  set g₁ := MMP.Threefold.Mori.Helpers.evalFF Z₁ (ψ : RationalFunctions Y) with hg₁_def
  set g := functionFieldMap h (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))
    with hg_def
  have hg₁ : g₁ ≠ 0 := (ψ.isUnit.map _).ne_zero
  have hg : g ≠ 0 := (map_ne_zero _).mpr (φ.isUnit.map _).ne_zero
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := f) E ![g₁, g]
    (by intro j; fin_cases j; exacts [hg₁, hg]) ![1, -1] fun Γ hΓ => by
      have hZ : Γ.component = Z₁ := Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := Y)) _ _
      have e1 : Y.ord g₁ Γ.genericPoint = C₁.coeff Γ := by
        rw [hψ Γ ⟨_, hΓ, hW⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
      have hΓU : h Γ.genericPoint ∈ U :=
        (Γ.genericPoint_mem_iff (h ⁻¹ᵁ U)).mpr ⟨f E.genericPoint, hΓ, hU⟩
      have e2 : Y.ord g Γ.genericPoint = C₁.coeff Γ :=
        (MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h₁ hφ Γ hΓU Z).symm
      simp [Fin.sum_univ_two, e1, e2]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    mul_one, mul_neg] at key
  have : ((Y'.ord (functionFieldMap f g₁) E.genericPoint : ℤ) : ℝ) =
      (Y'.ord (functionFieldMap f g) E.genericPoint : ℝ) := by linarith
  exact_mod_cast this

end Centre

/-! ### Function fields of the same transcendence degree -/

section TrDeg

/-- A dominant, locally quasi-finite morphism of integral `k`-schemes, locally of finite type,
preserves the transcendence degree of the function field, since `k(Y)` is finite over `k(X)`. -/
private theorem trdeg_functionField_eq_of_locallyQuasiFinite {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    [IsDominant h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (h ≫ sX)
    Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (h ≫ sX)
  letI := functionFieldMapAlgebra h
  haveI := isScalarTower_functionFieldMap sX h
  haveI := finite_functionField h
  haveI : Algebra.IsAlgebraic X.functionField Y.functionField := Algebra.IsAlgebraic.of_finite _ _
  have h1 := trdeg_add_eq k X.functionField (A := Y.functionField)
  rwa [(trdeg_eq_zero_iff (R := X.functionField) (A := Y.functionField)).mpr inferInstance,
    add_zero] at h1

/-- Integral schemes of finite type over a field whose function fields have the same
transcendence degree have the same dimension. -/
private theorem topologicalKrullDim_eq_of_trdeg_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType (h ≫ sX)]
    (htr : letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (h ≫ sX)
      Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (h ≫ sX)
  have htr' : Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := htr
  rw [← toENat_trdeg_functionField (sX := h ≫ sX), ← htr', toENat_trdeg_functionField (sX := sX)]

end TrDeg

/-! ### Étale morphisms and prime divisors -/

section Etale

open IsLocalRing

/-- **Unramified extensions of a discrete valuation ring.** Let `A → B` be a local,
formally unramified, essentially finite type homomorphism of local rings, with `A` a discrete
valuation ring and `B` a Noetherian domain. If a uniformizer `ϖ` of `A` does not vanish in `B`,
then `B` is a discrete valuation ring with uniformizer the image of `ϖ`. -/
private lemma isDiscreteValuationRing_of_formallyUnramified {A B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : algebraMap A B ϖ ≠ 0) :
    IsDiscreteValuationRing B ∧ Irreducible (algebraMap A B ϖ) := by
  have hmax : maximalIdeal B = Ideal.span {algebraMap A B ϖ} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField B := by
    rwa [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 5 1).1 (⟨⟨_, hmax⟩⟩ : (maximalIdeal B).IsPrincipal)
  exact ⟨this, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax⟩

/-- The local ring of a normal locally Noetherian integral scheme at the generic point of a
prime divisor `E` is a discrete valuation ring, with a uniformizer of `ord_E`-value `exp (-1)`. -/
private lemma exists_irreducible_divisorialValuation_eq {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    IsDiscreteValuationRing (X.presheaf.stalk z) ∧ ∃ ϖ : X.presheaf.stalk z, Irreducible ϖ ∧
      E.divisorialValuation (algebraMap _ X.functionField ϖ) = WithZero.exp (-1) := by
  subst hz
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  exact ⟨this, ϖ, hϖ, E.divisorialValuation_algebraMap_of_irreducible hϖ⟩

/-- `ord_E` is centred at the generic point of `E`: it is `≤ 1` on `𝒪_{X,E}` and `< 1` on its
maximal ideal. -/
private lemma divisorialValuation_centre {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    (∀ a : X.presheaf.stalk z, E.divisorialValuation (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (X.presheaf.stalk z),
        E.divisorialValuation (algebraMap _ X.functionField a) < 1 := by
  subst hz
  exact ⟨fun a => (E.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩,
    fun a ha => (E.divisorialValuation_algebraMap_lt_one_iff a).2 ha⟩

/-- **Flat, locally quasi-finite morphisms preserve coheights.** Such a morphism is strictly
monotone for the specialization order (distinct points of a fibre are not specializations of
one another) and generizations lift along it. -/
private theorem coheight_apply_eq {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [LocallyQuasiFinite h] (y : Y) : Order.coheight (h y) = Order.coheight y := by
  refine (Order.coheight_eq_of_strictMono (⇑h) (fun a b hab => ?_) (fun a b hab => ?_) y).symm
  · have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hba.map h.continuous)) fun hle => ?_
    have heq : h b = h a :=
      ((hba.map h.continuous).antisymm (Scheme.le_iff_specializes.mp hle)).eq
    exact hab.ne (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite h hba heq).symm
  · obtain ⟨a', ha', rfl⟩ := Flat.generalizingMap h (Scheme.le_iff_specializes.mp hab.le)
    refine ⟨a', lt_of_le_not_ge (Scheme.le_iff_specializes.mpr ha') fun hle => ?_, rfl⟩
    have heq : a' = a := (ha'.antisymm (Scheme.le_iff_specializes.mp hle)).eq
    rw [heq] at hab
    exact lt_irrefl _ hab

/-- **Prime divisors along an étale morphism.** Let `h : Y ⟶ X` be a dominant étale morphism of
normal locally Noetherian integral schemes and `Γ'` a prime divisor of `Y`. Then `h(η_{Γ'})` is
the generic point of a prime divisor `Γ` of `X`, and `v_{Γ'} ∘ h^* = v_Γ`: the local ring
`𝒪_{X,Γ} ⟶ 𝒪_{Y,Γ'}` is formally unramified, so a uniformizer of `𝒪_{X,Γ}` stays one. -/
private theorem exists_primeDivisor_divisorialValuation_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (h : Y ⟶ X) [Etale h] [IsDominant h] (Γ' : PrimeDivisor Y) :
    ∃ Γ : PrimeDivisor X, Γ.genericPoint = h Γ'.genericPoint ∧
      ∀ g, Γ'.divisorialValuation (functionFieldMap h g) = Γ.divisorialValuation g := by
  have hco : Order.coheight (h Γ'.genericPoint) = 1 :=
    (coheight_apply_eq h _).trans Γ'.coheight_genericPoint
  let Γ : PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hΓ : Γ.genericPoint = h Γ'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨Γ, hΓ, fun g => ?_⟩
  obtain ⟨hAdvr, ϖ, hϖ, hϖv⟩ := exists_irreducible_divisorialValuation_eq Γ hΓ.symm
  let φ := (h.stalkMap Γ'.genericPoint).hom
  letI : Algebra (X.presheaf.stalk (h Γ'.genericPoint)) (Y.presheaf.stalk Γ'.genericPoint) :=
    φ.toAlgebra
  have : Algebra.FormallyUnramified (X.presheaf.stalk (h Γ'.genericPoint))
      (Y.presheaf.stalk Γ'.genericPoint) :=
    AlgebraicGeometry.FormallyUnramified.stalkMap (f := h) _
  have : Algebra.EssFiniteType (X.presheaf.stalk (h Γ'.genericPoint))
      (Y.presheaf.stalk Γ'.genericPoint) :=
    LocallyOfFiniteType.stalkMap (f := h) _
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h Γ'.genericPoint))
      (Y.presheaf.stalk Γ'.genericPoint)) := inferInstanceAs (IsLocalHom φ)
  have hφϖ : φ ϖ ≠ 0 := by
    intro h0
    have := MMP.Mori.functionFieldMap_algebraMap_stalk h Γ'.genericPoint ϖ
    rw [show (h.stalkMap Γ'.genericPoint).hom ϖ = 0 from h0, map_zero,
      map_eq_zero_iff _ (RingHom.injective _),
      map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this
    exact hϖ.ne_zero this
  obtain ⟨-, hirr⟩ : _ ∧ Irreducible (φ ϖ) :=
    isDiscreteValuationRing_of_formallyUnramified hϖ hφϖ
  obtain ⟨hv1, hv2⟩ := divisorialValuation_centre Γ hΓ.symm
  have hw : Γ'.divisorialValuation.comap (functionFieldMap h) = Γ.divisorialValuation := by
    refine MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing
      (R := X.presheaf.stalk (h Γ'.genericPoint)) (fun a => ?_) (fun a ha => ?_)
      ⟨algebraMap _ X.functionField ϖ, ?_⟩ hv1 hv2 ⟨_, hϖv⟩
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact (Γ'.divisorialValuation_le_one_iff _).2 ⟨_, rfl⟩
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact (Γ'.divisorialValuation_algebraMap_lt_one_iff _).2 (map_nonunit φ a ha)
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact Γ'.divisorialValuation_algebraMap_of_irreducible hirr
  exact congrArg (fun v => v g) hw

end Etale

/-! ### The restriction of the valuation -/

section Restriction

/-- **The restriction of `w` is a normalized divisorial valuation.** By the restriction lemma,
`w|_{k(Y_0)} = v ^ e` with `v = ord_E` normalized divisorial; on a smooth model `W` projective
and birational over `Y_0` carrying `v` as a prime divisor `E`, the centre of `w` on
`W ×_{Y_0} Y_e` is a prime divisor over `E` along which `e = 1`. -/
private theorem isNormalizedDivisorialValuation_comap {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : IsNormalVariety k s₀) (hₑ : IsNormalVariety k (q ≫ s₀))
    (w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ)))
    (hw : MMP.Intersection.IsNormalizedDivisorialValuation k (q ≫ s₀) w) :
    MMP.Intersection.IsNormalizedDivisorialValuation k s₀ (w.comap (functionFieldMap q)) := by
  obtain ⟨D', hD'p, rfl⟩ := hw
  haveI : AlgebraicGeometry.IsVariety k s₀ := h₀.1
  haveI : IsNormal Y₀ := h₀.2
  haveI : AlgebraicGeometry.IsVariety k (q ≫ s₀) := hₑ.1
  haveI : IsNormal Yₑ := hₑ.2
  -- the restriction is `v ^ e` for a normalized divisorial valuation `v`
  obtain ⟨v, ⟨F, hFp, hFv⟩, e, he, hve⟩ :=
    MMP.Fourfold.exists_isNormalizedDivisorialValuation_comap_eq_pow k s₀ q h₀.1 hₑ.1 D'.valuation
      ⟨D', hD'p, rfl⟩
  -- `v` has a nonempty centre on `Y₀`
  have hvc : MMP.Flips.HasNonemptyCenter k s₀ v := by
    haveI := F.isIntegral
    haveI := F.isNormal
    haveI := F.isLocallyNoetherian
    haveI := F.isDominant
    subst hFv
    exact ⟨⟨F.Y, F.f ≫ s₀, F.isNormalVariety, F.E,
      MMP.Mori.functionFieldAlgEquiv s₀ F.f F.isBirationalMorphism.functionFieldMap_bijective, rfl⟩,
      ⟨F, hFp⟩, rfl⟩
  -- a smooth projective model `μ : W ⟶ Y₀` carrying `v` as a prime divisor `E`
  haveI : ∀ i : Empty, IsProper ((fun i => i.elim : ∀ i : Empty, Empty.elim i ⟶ Y₀) i) :=
    fun i => i.elim
  obtain ⟨W, μ, hW, hμb, -, hWsm, hμp, -, hE, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (S := Y₀) s₀
      (ι := Empty) (X := Empty.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (κ := Unit) (fun _ => v) (fun _ => hvc)
  obtain ⟨E, hEv⟩ := hE ()
  haveI : AlgebraicGeometry.IsVariety k (μ ≫ s₀) := hW.1
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (μ ≫ s₀)
  haveI : Smooth (μ ≫ s₀) := hWsm.smooth
  haveI : IsDominant μ := hμb.isDominant
  haveI : IsLocallyNoetherian Y₀ :=
    haveI := h₀.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian s₀
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  haveI : IsNoetherian Y₀ := {}
  haveI : IsProper μ := isProper_of_isProjectiveMorphism μ hμp
  obtain ⟨U, hU, hμU⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμb)
  -- `e = 1`
  obtain ⟨-, -, -, -, E', -, -, he1⟩ :=
    MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_etale q rfl μ rfl hμp U hU hμU E
      D'.valuation ⟨D', hD'p, rfl⟩ e he (fun g => by rw [hve g, ← hEv]; rfl)
  subst he1
  have hres : D'.valuation.comap (functionFieldMap q) = v := by
    ext g; simpa using hve g
  exact ⟨F, hFp, hres.trans hFv⟩

end Restriction

private theorem ordPullback_pullbackRationalPluriForms_eq {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {h : Y ⟶ X} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsDominant h]
    (htr : letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (h ≫ sX)
      Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField)
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (h ≫ sX))
    {n : ℕ} (hn : topologicalKrullDim X = n) {D : DivisorOver k sX}
    {D' : DivisorOver k (h ≫ sX)} {e : ℕ}
    (he : ∀ g, D'.valuation (functionFieldMap h g) = D.valuation g ^ e)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) :
    D'.ordPullback (pullbackRationalPluriForms sX h ω) = e * D.ordPullback ω + (e - 1) := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (h ≫ sX)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sX h
  have htrXY : Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := htr
  have hdimY : topologicalKrullDim Y = n := (topologicalKrullDim_eq_of_trdeg_eq sX h htr).trans hn
  have hdX : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hn
  have hdY : (Algebra.trdeg k Y.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimY
  obtain ⟨ωg, hωg⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX h hn hdimY
  have he0 : e ≠ 0 := ne_zero_of_valuation_eq_pow he
  let := functionFieldAlgebra (D.f ≫ sX)
  let := functionFieldAlgebra (D'.f ≫ h ≫ sX)
  let := functionFieldMapAlgebra D.f
  let := functionFieldMapAlgebra D'.f
  have := isScalarTower_functionFieldMap sX D.f
  have := isScalarTower_functionFieldMap (h ≫ sX) D'.f
  have hb1 := D.isBirationalMorphism.functionFieldMap_bijective
  have hb2 := D'.isBirationalMorphism.functionFieldMap_bijective
  let eD := RingEquiv.ofBijective (functionFieldMap D.f) hb1
  let ι : D.Y.functionField →+* D'.Y.functionField :=
    (functionFieldMap D'.f).comp ((functionFieldMap h).comp eD.symm.toRingHom)
  have hι1 : ∀ g, ι (functionFieldMap D.f g) = functionFieldMap D'.f (functionFieldMap h g) :=
    fun g => by
      simp only [ι, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      congr 2
      exact eD.symm_apply_apply g
  have hkY' : ∀ c : k, algebraMap k D'.Y.functionField c =
      functionFieldMap D'.f (functionFieldMap h (algebraMap k X.functionField c)) := fun c =>
    (IsScalarTower.algebraMap_apply k Y.functionField D'.Y.functionField c).trans
      (congrArg (functionFieldMap D'.f)
        (IsScalarTower.algebraMap_apply k X.functionField Y.functionField c))
  have hι0 : ∀ c : k, algebraMap k D'.Y.functionField c =
      ι (algebraMap k D.Y.functionField c) := fun c => by
    rw [hkY', show algebraMap k D.Y.functionField c =
        functionFieldMap D.f (algebraMap k X.functionField c) from
      IsScalarTower.algebraMap_apply k X.functionField D.Y.functionField c, hι1]
  have htr' : Algebra.trdeg k D.Y.functionField = Algebra.trdeg k D'.Y.functionField := by
    rw [← trdeg_functionField_eq_of_bijective sX D.f hb1, htrXY,
      trdeg_functionField_eq_of_bijective (h ≫ sX) D'.f hb2]
  have hdX' : (Algebra.trdeg k D.Y.functionField).toNat = n := by
    rwa [← trdeg_functionField_eq_of_bijective sX D.f hb1]
  have hdY' : (Algebra.trdeg k D'.Y.functionField).toNat = n := by
    rwa [← htr']
  have hval : ∀ g, D'.E.divisorialValuation (ι g) = D.E.divisorialValuation g ^ e := by
    intro g
    obtain ⟨g₀, rfl⟩ := hb1.2 g
    rw [hι1]
    exact he g₀
  -- the two factorizations of `k(X) → k(D'.Y)`
  letI := ι.toAlgebra
  haveI : IsScalarTower k D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hι0
  letI : Algebra X.functionField D'.Y.functionField :=
    ((functionFieldMap D'.f).comp (functionFieldMap h)).toAlgebra
  haveI : IsScalarTower X.functionField Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower X.functionField D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun g => (hι1 g).symm
  haveI : IsScalarTower k X.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hkY'
  have := essFiniteType_functionField (sX := D.f ≫ sX)
  obtain ⟨ω₂, hω₂⟩ := exists_isPullbackGenerator_of_bijective (h ≫ sX) D'.f hb2 hdY
  obtain ⟨ω₃, hω₃⟩ := exists_isPullbackGenerator_of_bijective sX D.f hb1 hdX
  obtain ⟨ω₄, hω₄⟩ := exists_isPullbackGenerator (k := k) (K := D.Y.functionField)
    (K' := D'.Y.functionField) htr' hdX'
  have hg1 : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k X.functionField Y.functionField n ωg) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₂ hωg.2.1 hωg.2.2
  have hg2 : IsPullbackGenerator D.Y.functionField ωg :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₃ hωg.1 hωg.ne_zero
  have hg3 : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k X.functionField D.Y.functionField n ωg) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₄ hg2.2.1 hg2.2.2
  have c1 := MMP.Threefold.Mori.Helpers.pullbackForms_comp (K := X.functionField)
    (K' := Y.functionField) (K'' := D'.Y.functionField) (m := 1) hωg hg1 ω
  have c2 := MMP.Threefold.Mori.Helpers.pullbackForms_comp (K := X.functionField)
    (K' := D.Y.functionField) (K'' := D'.Y.functionField) (m := 1) hg2 hg3 ω
  have hforms : pullbackRationalPluriForms (h ≫ sX) D'.f (pullbackRationalPluriForms sX h ω) =
      pullbackAlong (D.f ≫ sX) (D'.f ≫ h ≫ sX) ι hι0 (pullbackRationalPluriForms sX D.f ω) :=
    c1.trans c2.symm
  have hτ : pullbackRationalPluriForms sX D.f ω ≠ 0 := pullbackForms_ne_zero hg2 hω
  have key := ordForm_pullbackAlong_eq (D.f ≫ sX) (D'.f ≫ h ≫ sX) D.isNormalVariety
    D'.isNormalVariety hdX' hdY' htr' ι hι0 D.E D'.E hval hτ
  have hP : D'.ordPullback (pullbackRationalPluriForms sX h ω) =
      D'.E.ordForm (pullbackAlong (D.f ≫ sX) (D'.f ≫ h ≫ sX) ι hι0
        (pullbackRationalPluriForms sX D.f ω)) :=
    congrArg D'.E.ordForm hforms
  rw [hP, key, one_mul]
  rfl

/-- The coefficients of an integral divisor `M` with `M = m (K + B)` as `ℚ`-divisors. -/
private theorem coeff_eq_of_toQDivisor_eq_smul {X : Scheme.{u}} {M K : Divisor X}
    {B : QDivisor X} {m : ℕ} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B))
    (Γ : PrimeDivisor X) : (M.coeff Γ : ℝ) = m * ((K.coeff Γ : ℝ) + (B.coeff Γ : ℝ)) := by
  have h1 := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul, Int.cast_natCast] at h1
  exact_mod_cast h1

/-- Pulling a scalar out of a weighted sum. -/
private theorem sum_mul_mul_eq_mul_sum {ι : Type*} [Fintype ι] (x r : ι → ℝ) (c : ℝ) :
    ∑ i, x i * (c * r i) = c * ∑ i, r i * x i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Log discrepancies along a pull-back of the same transcendence degree.** Let `h : Y ⟶ X`
be a dominant morphism of normal varieties over a field of characteristic zero with
`trdeg k(Y) = trdeg k(X)`, `K_X = div ω`, `K_Y = div h^*ω`, `B_X`, `B_Y` with `K_X + B_X`
`ℚ`-Cartier and `K_Y + B_Y = h^*(K_X + B_X)`, and divisors `D` over `X`, `D'` over `Y` with
`v_{D'} ∘ h^* = v_D ^ e`. If `a` is the log discrepancy of `D` with respect to `(X, B_X)`, then
`e · a` is that of `D'` with respect to `(Y, B_Y)`. -/
private theorem isLogDiscrepancy_mul_of_valuation_eq_pow {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant h]
    (htr : letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (h ≫ sX)
      Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField)
    (hY : MMP.Mori.IsNormalVariety k (h ≫ sX)) {n : ℕ}
    {ω : MMP.Mori.RationalPluriForms sX n 1} (hω : ω ≠ 0)
    {KX : Divisor X} (hKX : ∀ Γ, KX.coeff Γ = Γ.ordForm ω)
    {KY : Divisor Y}
    (hKY : ∀ Γ, KY.coeff Γ = Γ.ordForm (MMP.Mori.pullbackRationalPluriForms sX h ω))
    {BX : QDivisor X} {BY : QDivisor Y}
    (hq : (Divisor.toQDivisor KX + BX).IsQCartier)
    (hpull : ∃ hB, (Divisor.toQDivisor KX + BX).IsPullback h hB (Divisor.toQDivisor KY + BY))
    {D : DivisorOver k sX}
    {D' : DivisorOver k (h ≫ sX)} (hD' : IsProper D'.f)
    {e : ℕ} (he : ∀ g : X.functionField, D'.valuation (functionFieldMap h g) = D.valuation g ^ e)
    {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor BX) D a) :
    MMP.Intersection.IsLogDiscrepancy (h ≫ sX) n (QDivisor.toRDivisor BY) D' (e * a) := by
  classical
  obtain ⟨hX, -, ω₀, hω₀, ⟨K₀, hK₀, -⟩, m, r, C, C', hCc, hsum, hpb, rfl⟩ := ha
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  have : CompactSpace Y := by
    have := hY.1
    exact QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  have : CompactSpace D'.Y := by
    have := D'.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D'.f ≫ h ≫ sX)
  have hn : topologicalKrullDim X = n := hK₀.topologicalKrullDim_eq
  have hdimY : topologicalKrullDim Y = n := (topologicalKrullDim_eq_of_trdeg_eq sX h htr).trans hn
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (h ≫ sX)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sX h
  have hdX : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hn
  have hdY : (Algebra.trdeg k Y.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimY
  -- the pull-back of forms along `h`
  obtain ⟨ωg, hωg⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX h hn hdimY
  set b := basisOfSpanSingleton hωg.1 hωg.ne_zero
  set b' := basisOfSpanSingleton hωg.2.1 hωg.2.2
  have hrepr : ∀ τ : RationalPluriForms sX n 1,
      (ZTensorPower.basis b' 1).repr (pullbackRationalPluriForms sX h τ) () =
        functionFieldMap h ((ZTensorPower.basis b 1).repr τ ()) := fun τ => by
    rw [show pullbackRationalPluriForms sX h τ = pullbackFormsAlong hωg 1 τ from
      pullbackForms_eq hωg 1 τ]
    exact repr_pullbackFormsAlong hωg 1 τ
  have hω₀' : pullbackRationalPluriForms sX h ω₀ ≠ 0 := pullbackForms_ne_zero hωg hω₀
  have hω' : pullbackRationalPluriForms sX h ω ≠ 0 := pullbackForms_ne_zero hωg hω
  -- the canonical divisor of `Y`
  obtain ⟨KY₀, hKY₀⟩ := exists_isCanonicalDivisor (h ≫ sX) hY hdimY
  have hKcan : (divisorOfForm (pullbackRationalPluriForms sX h ω₀)).IsCanonicalDivisor (h ≫ sX) n :=
    hKY₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hKY₀ hω₀')
  -- the pull-backs of the Cartier divisors `Cᵢ` to `Y` and to `D'.Y`
  have hB₁ : ∀ i, ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ (C i).supp :=
    fun i => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp h (C i)
  let C₁ : Fin m → Divisor Y := fun i => (C i).pullback (hCc i) (hB₁ i)
  have hC₁pb : ∀ i, (C i).IsPullback h (hB₁ i) (C₁ i) := fun i =>
    Divisor.isPullback_pullback (hCc i) (hB₁ i)
  have hC₁c : ∀ i, (C₁ i).IsCartier := fun i => (hC₁pb i).isCartier (hCc i)
  have hB₂ : ∀ i, ∀ Z : irreducibleComponents D'.Y,
      D'.f (componentGenericPoint D'.Y Z) ∉ (C₁ i).supp :=
    fun i => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f (C₁ i)
  let C₂ : Fin m → Divisor D'.Y := fun i => (C₁ i).pullback (hC₁c i) (hB₂ i)
  have hC₂pb : ∀ i, (C₁ i).IsPullback D'.f (hB₂ i) (C₂ i) := fun i =>
    Divisor.isPullback_pullback (hC₁c i) (hB₂ i)
  -- the Cartier multiple of `K_X + B_X` and its pull-back
  obtain ⟨m₀, hm₀, M, hM, hMc⟩ := hq.exists_pos
  obtain ⟨hB, hP⟩ := hpull
  obtain ⟨M', hM', hMpb⟩ := hP m₀ hm₀ M hM hMc
  have hm₀' : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  refine ⟨hY, hD', pullbackRationalPluriForms sX h ω₀, hω₀',
    ⟨_, hKcan, fun Γ => coeff_divisorOfForm _ Γ⟩, m, r, C₁, C₂, hC₁c, fun Γ' => ?_,
    fun i => ⟨_, hC₂pb i⟩, ?_⟩
  · -- `K_Y + B_Y` in terms of the pulled-back Cartier divisors, along `Γ'`
    rw [QDivisor.coeff_toRDivisor]
    choose V hV φ hφ using fun i => hCc i (h Γ'.genericPoint)
    obtain ⟨U₀, hU₀, μ, hμ⟩ := hMc (h Γ'.genericPoint)
    let Z0 := pointComponent (h Γ'.genericPoint)
    let g : Fin m → X.functionField := fun i =>
      MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ i : RationalFunctions X))
    let gμ : X.functionField := MMP.Threefold.Mori.Helpers.evalFF Z0 ((μ : RationalFunctions X))
    set cω₀ := (ZTensorPower.basis b 1).repr ω₀ () with hcω₀
    set cω := (ZTensorPower.basis b 1).repr ω () with hcω
    have hg : ∀ i, g i ≠ 0 := fun i => ((φ i).isUnit.map _).ne_zero
    have hgμ : gμ ≠ 0 := (μ.isUnit.map _).ne_zero
    have hcω₀0 : cω₀ ≠ 0 := repr_ne_zero_of_ne_zero b hω₀
    have hcω0 : cω ≠ 0 := repr_ne_zero_of_ne_zero b hω
    let G : Option (Option (Option (Fin m))) → X.functionField := fun j =>
      Option.elim j gμ fun j => Option.elim j cω₀ fun j => Option.elim j cω g
    let w : Option (Option (Option (Fin m))) → ℝ := fun j =>
      Option.elim j 1 fun j => Option.elim j (m₀ : ℝ) fun j =>
        Option.elim j (-(m₀ : ℝ)) fun i => -(m₀ : ℝ) * r i
    have hG : ∀ j, G j ≠ 0 := by
      rintro (_ | _ | _ | i)
      exacts [hgμ, hcω₀0, hcω0, hg i]
    have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := h) Γ' G hG w
      fun Γ hΓ => by
        obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hdX b
        have hZ : Γ.component = Z0 := Subsingleton.elim
          (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
        have eg : ∀ i, X.ord (g i) Γ.genericPoint = (C i).coeff Γ := fun i => by
          rw [hφ i Γ ⟨_, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
        have eμ : X.ord gμ Γ.genericPoint = M.coeff Γ := by
          rw [hμ Γ ⟨_, hΓ, hU₀⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
        have e1 : (Γ.ordForm ω₀ : ℝ) = X.ord cω₀ Γ.genericPoint + NΓ := by
          exact_mod_cast (by simpa using hNΓ 1 ω₀ hω₀)
        have e2 : (Γ.ordForm ω : ℝ) = X.ord cω Γ.genericPoint + NΓ := by
          exact_mod_cast (by simpa using hNΓ 1 ω hω)
        have e3 := hsum Γ
        rw [QDivisor.coeff_toRDivisor] at e3
        have e4 := coeff_eq_of_toQDivisor_eq_smul hM Γ
        have e5 : (KX.coeff Γ : ℝ) = Γ.ordForm ω := by exact_mod_cast hKX Γ
        simp only [Fintype.sum_option, G, w, Option.elim]
        simp_rw [eg, eμ]
        rw [sum_mul_mul_eq_mul_sum]
        linear_combination e4 - (m₀ : ℝ) * e1 + (m₀ : ℝ) * e2 + (m₀ : ℝ) * e3 + (m₀ : ℝ) * e5
    simp only [Fintype.sum_option, G, w, Option.elim] at key
    obtain ⟨N', hN'⟩ := Γ'.exists_ordForm_eq_ord_add_mul hdY b'
    have f1 : (Γ'.ordForm (pullbackRationalPluriForms sX h ω₀) : ℝ) =
        Y.ord (functionFieldMap h cω₀) Γ'.genericPoint + N' := by
      have := hN' 1 _ hω₀'
      rw [hrepr] at this
      exact_mod_cast (by simpa using this)
    have f2 : (KY.coeff Γ' : ℝ) = Y.ord (functionFieldMap h cω) Γ'.genericPoint + N' := by
      have := hN' 1 _ hω'
      rw [hrepr] at this
      rw [hKY Γ']
      exact_mod_cast (by simpa using this)
    have f3 := coeff_eq_of_toQDivisor_eq_smul hM' Γ'
    have f4 : (M'.coeff Γ' : ℝ) = Y.ord (functionFieldMap h gμ) Γ'.genericPoint := by
      exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hMpb hμ Γ' hU₀ Z0
    have f5 : ∀ i, ((C₁ i).coeff Γ' : ℝ) = Y.ord (functionFieldMap h (g i)) Γ'.genericPoint :=
      fun i => by
        exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hC₁pb i) (hφ i) Γ'
          (hV i) Z0
    simp_rw [f5]
    rw [sum_mul_mul_eq_mul_sum] at key
    apply mul_left_cancel₀ hm₀'
    linear_combination key + (m₀ : ℝ) * f1 - (m₀ : ℝ) * f2 - f3 + f4
  · -- the value of the log discrepancy
    have he0 : e ≠ 0 := ne_zero_of_valuation_eq_pow he
    have hcen := map_center_eq_of_valuation_eq_pow h hX.1 he0 he
    have hordc : ∀ g : X.functionField, g ≠ 0 →
        D'.Y.ord (functionFieldMap D'.f (functionFieldMap h g)) D'.E.genericPoint =
          e * D.Y.ord (functionFieldMap D.f g) D.E.genericPoint := fun g hg =>
      ord_eq_mul_of_divisorialValuation_eq_pow D.E D'.E (he g) ((map_ne_zero _).mpr hg)
        ((map_ne_zero _).mpr ((map_ne_zero _).mpr hg))
    choose Vx hVx φx hφx using fun i => hCc i (D.f D.E.genericPoint)
    let Zx := pointComponent (D.f D.E.genericPoint)
    have hcoef : ∀ i, ((C₂ i).coeff D'.E : ℝ) = e * ((C' i).coeff D.E : ℝ) := by
      intro i
      obtain ⟨_, hCp⟩ := hpb i
      have hgx : MMP.Threefold.Mori.Helpers.evalFF Zx ((φx i : RationalFunctions X)) ≠ 0 :=
        ((φx i).isUnit.map _).ne_zero
      rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCp (hφx i) D.E (hVx i) Zx,
        coeff_isPullback_isPullback_eq (hCc i) (hC₁pb i) (hC₂pb i) (hφx i) D'.E
          (by rw [hcen]; exact hVx i) Zx, hordc _ hgx]
      push_cast
      ring
    have htame : (D'.ordPullback (pullbackRationalPluriForms sX h ω₀) : ℝ) =
        e * (D.ordPullback ω₀ : ℝ) + (e - 1) := by
      exact_mod_cast ordPullback_pullbackRationalPluriForms_eq htr hX hY hn he hω₀
    simp_rw [htame, hcoef, mul_left_comm (r _), ← Finset.mul_sum]
    ring

/-! ### The étale comparison -/

/-- **Orders of forms along an étale morphism.** Let `q : Yₑ ⟶ Y₀` be a dominant étale morphism
of normal varieties over a field of characteristic zero, and `Γ'`, `Γ` prime divisors of `Yₑ`,
`Y₀` with `v_{Γ'} ∘ q^* = v_Γ`. Then `ord_{Γ'}(q^*ω) = ord_Γ(ω)` for every nonzero rational top
form `ω` of `Y₀`: this is the tame formula with ramification index one. -/
private theorem ordForm_pullbackRationalPluriForms_of_etale {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsLocallyNoetherian Y₀] [IsNormal Y₀]
    [IsIntegral Yₑ] [IsLocallyNoetherian Yₑ] [IsNormal Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : IsNormalVariety k s₀) (hₑ : IsNormalVariety k (q ≫ s₀)) {n : ℕ}
    (hn : topologicalKrullDim Y₀ = n) {ω : RationalPluriForms s₀ n 1} (hω : ω ≠ 0)
    {Γ' : PrimeDivisor Yₑ} {Γ : PrimeDivisor Y₀}
    (hval : ∀ g, Γ'.divisorialValuation (functionFieldMap q g) = Γ.divisorialValuation g) :
    Γ'.ordForm (pullbackRationalPluriForms s₀ q ω) = Γ.ordForm ω := by
  haveI : LocallyOfFiniteType s₀ := h₀.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ s₀) := hₑ.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q s₀
  have htr := trdeg_functionField_eq_of_locallyQuasiFinite s₀ q
  have hdimₑ := (topologicalKrullDim_eq_of_trdeg_eq s₀ q htr).trans hn
  letI := functionFieldAlgebra s₀
  letI := functionFieldAlgebra (q ≫ s₀)
  letI := functionFieldMapAlgebra q
  haveI := isScalarTower_functionFieldMap s₀ q
  refine (ordForm_pullbackAlong_eq s₀ (q ≫ s₀) h₀ hₑ
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimₑ) htr (functionFieldMap q)
    (IsScalarTower.algebraMap_apply k Y₀.functionField Yₑ.functionField) Γ Γ' (e := 1)
    (by simpa using hval) hω).trans ?_
  simp

/-- **The canonical divisor along an étale morphism.** Let `q : Yₑ ⟶ Y₀` be a dominant étale
morphism of normal varieties over a field of characteristic zero and `K_{Y₀} = div ω`. Then
`div(q^*ω)` is the pull-back of `K_{Y₀}`: the pull-back of a Cartier multiple `M = m K_{Y₀}` has,
along a prime divisor `Γ'` over `Γ`, the coefficient `ord_Γ(M) = m ord_Γ(ω) = m ord_{Γ'}(q^*ω)`. -/
private theorem isPullback_divisorOfForm_pullbackRationalPluriForms {k : Type u} [Field k]
    [CharZero k] {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsLocallyNoetherian Y₀] [IsNormal Y₀]
    [IsIntegral Yₑ] [IsLocallyNoetherian Yₑ] [IsNormal Yₑ] [CompactSpace Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q] [LocallyOfFiniteType (q ≫ s₀)]
    (h₀ : IsNormalVariety k s₀) (hₑ : IsNormalVariety k (q ≫ s₀)) {n : ℕ}
    (hn : topologicalKrullDim Y₀ = n) {ω : RationalPluriForms s₀ n 1} (hω0 : ω ≠ 0)
    {K₀ : Divisor Y₀} (hω : ∀ Γ, Γ.ordForm ω = K₀.coeff Γ) :
    ∃ hB, (Divisor.toQDivisor K₀ + 0).IsPullback q hB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms s₀ q ω)) + 0) := by
  refine ⟨fun Z hZ => ?_, fun m hm M hM hMc => ?_⟩
  · rw [← QDivisor.supp_eq_of_toQDivisor_eq (D := K₀) (m := 1) one_ne_zero (by simp)] at hZ
    exact MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp q K₀ Z hZ
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant q hMc
  refine ⟨M', ?_, hM'⟩
  suffices M' = (m : ℤ) • divisorOfForm (pullbackRationalPluriForms s₀ q ω) by
    rw [this, add_zero, map_zsmul]
  refine DivisorWithCoeffs.ext' fun Γ' => ?_
  obtain ⟨Γ, hΓ, hval⟩ := exists_primeDivisor_divisorialValuation_eq q Γ'
  obtain ⟨U, hU, φ, hφ⟩ := hMc (q Γ'.genericPoint)
  have hg : MMP.Threefold.Mori.Helpers.evalFF Γ.component (φ : RationalFunctions Y₀) ≠ 0 :=
    (φ.isUnit.map _).ne_zero
  have hMK : (M.coeff Γ : ℝ) = m * K₀.coeff Γ := by
    simpa using coeff_eq_of_toQDivisor_eq_smul hM Γ
  have hMΓ : M.coeff Γ = Y₀.ord (MMP.Threefold.Mori.Helpers.evalFF Γ.component
      (φ : RationalFunctions Y₀)) Γ.genericPoint := by
    rw [hφ Γ ((Γ.genericPoint_mem_iff U).mp (hΓ ▸ hU)),
      MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, coeff_divisorOfForm,
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM' hφ Γ' hU Γ.component,
    ord_eq_mul_of_divisorialValuation_eq_pow Γ Γ' (e := 1) (by rw [pow_one]; exact hval _) hg
      ((map_ne_zero _).mpr hg), ← hMΓ,
    ordForm_pullbackRationalPluriForms_of_etale s₀ q h₀ hₑ hn hω0 hval, hω Γ]
  push_cast
  rw [one_mul]
  exact_mod_cast hMK

end Proof_lem_oai4_c2_etale_discrepancy

namespace MMP.Intersection

open CategoryTheory AlgebraicGeometry

/-- **Log discrepancies along étale maps.** Let `q : Y_e ⟶ Y_0` be a dominant étale morphism of
normal varieties over a field `k` of characteristic zero, with `K_{Y_0}` `ℚ`-Cartier, and `w` a
normalized divisorial valuation of `k(Y_e)`. Then `K_{Y_e}` is `ℚ`-Cartier, the restriction
`v = w|_{k(Y_0)}` is a normalized divisorial valuation of `k(Y_0)`, and for divisors `D_e` over
`Y_e` and `D_0` over `Y_0` (with proper structure maps) realizing `w` and `v`, the log
discrepancies agree: `a(D_e; Y_e, 0) = a(D_0; Y_0, 0)`. -/
@[mmp "lem_oai4_c2_etale_discrepancy"]
public theorem isLogDiscrepancy_iff_of_etale {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsLocallyNoetherian Y₀] [IsNormal Y₀]
    [IsIntegral Yₑ] [IsLocallyNoetherian Yₑ] [IsNormal Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : MMP.Mori.IsPair s₀ (0 : MMP.Mori.QDivisor Y₀))
    (hₑ : MMP.Mori.IsNormalVariety k (q ≫ s₀))
    (w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ)))
    (hw : IsNormalizedDivisorialValuation k (q ≫ s₀) w) :
    MMP.Mori.IsPair (q ≫ s₀) (0 : MMP.Mori.QDivisor Yₑ) ∧
      IsNormalizedDivisorialValuation k s₀ (w.comap (functionFieldMap q)) ∧
      ∀ (Dₑ : MMP.Mori.DivisorOver k (q ≫ s₀)) (D₀ : MMP.Mori.DivisorOver k s₀),
        IsProper Dₑ.f → IsProper D₀.f → Dₑ.valuation = w →
          D₀.valuation = w.comap (functionFieldMap q) →
          ∀ (n : ℕ) (a : ℝ), IsLogDiscrepancy (q ≫ s₀) n 0 Dₑ a ↔
            IsLogDiscrepancy s₀ n 0 D₀ a := by
  open MMP.Mori Proof_lem_oai4_c2_etale_discrepancy MMP.Mori.CanonicalDivisorExistence in
  · have hX₀ : MMP.Mori.IsNormalVariety k s₀ := h₀.1
    obtain ⟨n₀, K₀, hK₀, hQ₀⟩ := h₀.2
    haveI : LocallyOfFiniteType s₀ := hX₀.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (q ≫ s₀) := hₑ.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q s₀
    haveI : CompactSpace Yₑ := haveI := hₑ.1; QuasiCompact.compactSpace_of_compactSpace (q ≫ s₀)
    have hn₀ : topologicalKrullDim Y₀ = n₀ := hK₀.topologicalKrullDim_eq
    have htr := trdeg_functionField_eq_of_locallyQuasiFinite s₀ q
    have hdimₑ : topologicalKrullDim Yₑ = n₀ :=
      (topologicalKrullDim_eq_of_trdeg_eq s₀ q htr).trans hn₀
    -- `K_{Y₀} = div ω`, and `K_{Yₑ} = div q^*ω = q^* K_{Y₀}`
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX₀ hK₀
    have hω' : pullbackRationalPluriForms s₀ q ω ≠ 0 := by
      letI := functionFieldAlgebra s₀
      letI := functionFieldAlgebra (q ≫ s₀)
      letI := functionFieldMapAlgebra q
      haveI := isScalarTower_functionFieldMap s₀ q
      obtain ⟨ωg, hωg⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq s₀ q hn₀ hdimₑ
      exact pullbackForms_ne_zero hωg hω0
    obtain ⟨KY₀, hKY₀⟩ := exists_isCanonicalDivisor (q ≫ s₀) hₑ hdimₑ
    have hKcan : (divisorOfForm (pullbackRationalPluriForms s₀ q ω)).IsCanonicalDivisor
        (q ≫ s₀) n₀ :=
      hKY₀.of_linearlyEquivalent (by
        simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hₑ hKY₀ hω')
    obtain ⟨hB, hpull⟩ :=
      isPullback_divisorOfForm_pullbackRationalPluriForms s₀ q hX₀ hₑ hn₀ hω0 hω
    have hQₑ : (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms s₀ q ω)) +
        0).IsQCartier := by
      obtain ⟨m, hm, M, hM, hMc⟩ := hQ₀.exists_pos
      obtain ⟨M', hM', hMpb⟩ := hpull m hm M hM hMc
      exact ⟨m, by exact_mod_cast hm.ne', M', hM', hMpb.isCartier hMc⟩
    refine ⟨⟨hₑ, n₀, _, hKcan, hQₑ⟩, isNormalizedDivisorialValuation_comap s₀ q hX₀ hₑ w hw, ?_⟩
    -- the log discrepancies agree
    intro Dₑ D₀ hDₑp hD₀p hDₑv hD₀v n a
    have htransport : ∀ b : ℝ, MMP.Intersection.IsLogDiscrepancy s₀ n₀ 0 D₀ b →
        MMP.Intersection.IsLogDiscrepancy (q ≫ s₀) n₀ 0 Dₑ b := fun b hb => by
      simpa using isLogDiscrepancy_mul_of_valuation_eq_pow s₀ q htr hₑ hω0 (KX := K₀)
        (fun Γ => (hω Γ).symm) (fun Γ' => coeff_divisorOfForm _ Γ') (BX := 0) (BY := 0) hQ₀
        ⟨hB, hpull⟩ hDₑp (e := 1) (fun g => by rw [pow_one, hDₑv, hD₀v]; rfl)
        (by simpa using hb)
    constructor
    · intro ha
      obtain rfl : n = n₀ := by
        exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
          hdimₑ
      obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h₀ hK₀ D₀
      have hb : MMP.Intersection.IsLogDiscrepancy s₀ n 0 D₀ (1 + c) := by
        simpa using MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hD₀p
      rwa [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha (htransport _ hb)]
    · intro ha
      obtain rfl : n = n₀ := by
        exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
          hn₀
      exact htransport a ha

end MMP.Intersection

/-! ## The product of a terminal variety with the projective line -/

namespace Proof_lem_mmp_indexb_product_terminal

open CategoryTheory AlgebraicGeometry Limits MMP.Mori

section ProductForms

open scoped TensorProduct
open Order

namespace OrderOfVanishing

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  [IsLocallyNoetherian Y]

/-- The order of a unit of a local ring at a point of coheight one is zero. -/
private theorem ord_algebraMap_of_isUnit {x : X} (hx : coheight x = 1) {a : X.presheaf.stalk x}
    (ha : IsUnit a) : X.ord (algebraMap _ X.functionField a) x = 0 := by
  have hne : algebraMap _ X.functionField a ≠ 0 := (ha.map _).ne_zero
  rw [Scheme.ord_eq_iff hx hne, ofAdd_zero]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  exact Ring.ordFrac_of_isUnit ha

/-- The order of a uniformizer of a discrete valuation ring stalk is one. -/
private theorem ord_algebraMap_of_irreducible {x : X} (hx : coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {ϖ : X.presheaf.stalk x} (hϖ : Irreducible ϖ) :
    X.ord (algebraMap _ X.functionField ϖ) x = 1 := by
  have hne : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  rw [Scheme.ord_eq_iff hx hne]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  exact Ring.ordFrac_irreducible hϖ

/-- **Orders under a morphism that is unramified at a point.** Let `f : Y ⟶ X` be dominant, `y`
a point of coheight one with `f(y)` of coheight one, both local rings discrete valuation rings,
and suppose the stalk map carries uniformizers to uniformizers. Then
`ord_y(f^* c) = ord_{f(y)}(c)` for every nonzero `c ∈ k(X)`. -/
private theorem ord_functionFieldMap_eq (f : Y ⟶ X) [IsDominant f] {y : Y} (hy : coheight y = 1)
    (hfy : coheight (f y) = 1) [IsDiscreteValuationRing (X.presheaf.stalk (f y))]
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (hirr : ∀ ϖ, Irreducible ϖ → Irreducible ((f.stalkMap y).hom ϖ)) {c : X.functionField}
    (hc : c ≠ 0) : Y.ord (functionFieldMap f c) y = X.ord c (f y) := by
  have hne : ∀ {Z : Scheme.{u}} [IsIntegral Z] {z : Z} {r : Z.presheaf.stalk z}, r ≠ 0 →
      algebraMap _ Z.functionField r ≠ 0 := fun hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hr
  have hpow : ∀ {Z : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z] (z : Z)
      {g : Z.functionField}, g ≠ 0 → ∀ m : ℕ, Z.ord (g ^ m) z = m * Z.ord g z := by
    intro Z _ _ z g hg m
    rw [← zpow_natCast, MMP.Mori.ord_zpow _ hg]
  have key : ∀ a : X.presheaf.stalk (f y), a ≠ 0 →
      Y.ord (functionFieldMap f (algebraMap _ X.functionField a)) y =
        X.ord (algebraMap _ X.functionField a) (f y) := by
    intro a ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk (f y))
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have hϖ' := hirr ϖ hϖ
    have hu' : IsUnit ((f.stalkMap y).hom u) := u.isUnit.map _
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    simp only [map_mul, map_pow]
    rw [Scheme.ord_mul (hne hu'.ne_zero) (pow_ne_zero _ (hne hϖ'.ne_zero)),
      Scheme.ord_mul (hne u.isUnit.ne_zero) (pow_ne_zero _ (hne hϖ.ne_zero)),
      ord_algebraMap_of_isUnit hy hu', ord_algebraMap_of_isUnit hfy u.isUnit,
      hpow _ (hne hϖ'.ne_zero), hpow _ (hne hϖ.ne_zero), ord_algebraMap_of_irreducible hy hϖ',
      ord_algebraMap_of_irreducible hfy hϖ]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (X.presheaf.stalk (f y)) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hc
  have hab : algebraMap _ X.functionField a =
      (algebraMap _ X.functionField a / algebraMap _ X.functionField b) *
        algebraMap _ X.functionField b := by
    rw [div_mul_cancel₀ _ (hne hb0)]
  have e1 := key a ha0
  have e2 := key b hb0
  rw [hab, map_mul, Scheme.ord_mul ((map_ne_zero _).mpr hc) ((map_ne_zero _).mpr (hne hb0)),
    Scheme.ord_mul hc (hne hb0)] at e1
  linarith

end OrderOfVanishing

namespace ExteriorForms

section Wedge

variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Left multiplication by `w ∈ M` in the exterior algebra, `⋀^n M → ⋀^{n+1} M`. -/
private noncomputable def wedgeLeft (n : ℕ) (w : M) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M where
  toFun x := ⟨ExteriorAlgebra.ι R w * x, by
    rw [ExteriorAlgebra.exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) x.2⟩
  map_add' x y := Subtype.ext (by simp [mul_add])
  map_smul' c x := Subtype.ext (by simp)

private theorem wedgeLeft_ιMulti (n : ℕ) (w : M) (v : Fin n → M) :
    wedgeLeft R n w (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti R (n + 1) (Fin.cons w v) := by
  apply Subtype.ext
  simp only [wedgeLeft, LinearMap.coe_mk, AddHom.coe_mk, exteriorPower.ιMulti_apply_coe]
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp [Matrix.vecTail]

end Wedge

section Generator

variable {k O O' : Type*} [CommRing k] [CommRing O] [CommRing O'] [Algebra k O] [Algebra k O']
  [Algebra O O'] [IsScalarTower k O O']

/-- **A generator of the top forms of an extension by one variable.** If `Ω_{O/k}` is spanned by
`n` elements and `Ω_{O'/k}` by the image of `Ω_{O/k}` together with `dz`, then for a generator
`σ` of `Ω^n_{O/k}`, `dz ∧ σ` generates `Ω^{n+1}_{O'/k}`. -/
private theorem span_singleton_wedgeLeft_topFormsMap_eq_top {n : ℕ} {e : Fin n → Ω[O⁄k]}
    (he : Submodule.span O (Set.range e) = ⊤) (z : O')
    (hspan : Submodule.span O' (Set.range (KaehlerDifferential.map k k O O') ∪
      {KaehlerDifferential.D k O' z}) = ⊤)
    {σ : ⋀[O]^n Ω[O⁄k]} (hσ : Submodule.span O {σ} = ⊤) :
    Submodule.span O' {(wedgeLeft O' n (KaehlerDifferential.D k O' z)
      (topFormsMap k O O' n σ))} = ⊤ := by
  set v : Fin (n + 1) → Ω[O'⁄k] :=
    Fin.cons (KaehlerDifferential.D k O' z) (fun i => KaehlerDifferential.map k k O O' (e i))
  have hv : Submodule.span O' (Set.range v) = ⊤ := by
    refine eq_top_iff.mpr (hspan.symm.le.trans (Submodule.span_le.mpr ?_))
    rintro _ (⟨w, rfl⟩ | h)
    · have hw : w ∈ Submodule.span O (Set.range e) := he ▸ Submodule.mem_top
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨i.succ, by simp [v]⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx =>
        rw [map_smul, ← algebraMap_smul O']
        exact Submodule.smul_mem _ _ hx
    · rw [Set.mem_singleton_iff] at h
      exact Submodule.subset_span ⟨0, by simp [v, h]⟩
  have h1 := Proof_lem_oai4_c2_etale_discrepancy.span_singleton_ιMulti_eq_top _ hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hσ ▸ Submodule.mem_top (x := exteriorPower.ιMulti O n e))
  have hιv : exteriorPower.ιMulti O' (n + 1) v = algebraMap O O' c •
      wedgeLeft O' n (KaehlerDifferential.D k O' z) (topFormsMap k O O' n σ) := by
    rw [← map_smul, algebraMap_smul, ← map_smul, hc, topFormsMap_ιMulti, wedgeLeft_ιMulti]
  refine eq_top_iff.mpr (h1.symm.le.trans (Submodule.span_le.mpr ?_))
  rintro _ rfl
  rw [SetLike.mem_coe, hιv]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Generator

section Compat

variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C] [Algebra k A]
  [Algebra k B] [Algebra k C] [Algebra A B] [IsScalarTower k A B]

/-- The top forms of `A` are spanned by the wedges of differentials of elements. -/
private theorem span_ιMulti_D (n : ℕ) :
    Submodule.span A (Set.range fun a : Fin n → A =>
      exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (a i))) = ⊤ := by
  refine eq_top_iff.mpr ((exteriorPower.ιMulti_span_of_span A n (M := Ω[A⁄k])
    (KaehlerDifferential.span_range_derivation k A)).symm.le.trans (Submodule.span_mono ?_))
  rintro - ⟨v, hv, rfl⟩
  have : ∀ i, ∃ a : A, KaehlerDifferential.D k A a = v i := fun i => hv (Set.mem_range_self i)
  choose a ha using this
  exact ⟨a, by simp only [ha]⟩

/-- `topFormsMap` commutes with `dz ∧ -`. -/
private theorem topFormsMap_wedgeLeft_D (n : ℕ) (a : A) (x : ⋀[A]^n Ω[A⁄k]) :
    topFormsMap k A B (n + 1) (wedgeLeft A n (KaehlerDifferential.D k A a) x) =
      wedgeLeft B n (KaehlerDifferential.D k B (algebraMap A B a)) (topFormsMap k A B n x) := by
  have hx : x ∈ Submodule.span A (Set.range fun a : Fin n → A =>
      exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (a i))) :=
    (span_ιMulti_D (k := k) (A := A) n) ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [wedgeLeft_ιMulti, topFormsMap_ιMulti, topFormsMap_ιMulti, wedgeLeft_ιMulti]
    congr 1
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [KaehlerDifferential.map_D]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
    rw [LinearMap.map_smul (wedgeLeft A n _), LinearMap.map_smul (topFormsMap k A B (n + 1)), hx,
      LinearMap.map_smul (topFormsMap k A B n), ← algebraMap_smul B c (topFormsMap k A B n x),
      LinearMap.map_smul, algebraMap_smul]

variable [Algebra B C] [Algebra A C] [IsScalarTower k B C] [IsScalarTower k A C]
  [IsScalarTower A B C]

/-- `topFormsMap` along a tower is the composite. -/
private theorem topFormsMap_topFormsMap (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    topFormsMap k B C n (topFormsMap k A B n x) = topFormsMap k A C n x := by
  have hx : x ∈ Submodule.span A (Set.range fun a : Fin n → A =>
      exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (a i))) :=
    (span_ιMulti_D (k := k) (A := A) n) ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    simp only [topFormsMap_ιMulti, KaehlerDifferential.map_D,
      ← IsScalarTower.algebraMap_apply]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
    rw [LinearMap.map_smul (topFormsMap k A B n), ← algebraMap_smul B c (topFormsMap k A B n x),
      LinearMap.map_smul (topFormsMap k B C n), hx, LinearMap.map_smul (topFormsMap k A C n),
      ← algebraMap_smul C c (topFormsMap k A C n x), ← algebraMap_smul C (algebraMap A B c),
      ← IsScalarTower.algebraMap_apply]

end Compat

section Repr

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

/-- The `1`-fold tensor power `v^{⊗1}` of a vector. -/
private noncomputable def tprodOne (v : L) : ZTensorPower K L 1 :=
  PiTensorProduct.tprod K fun _ : Fin 1 => v

/-- The coordinate of `v^{⊗1}` along `b^{⊗1}` is that of `v` along `b`. -/
private theorem repr_basis_one_tprod (b : Module.Basis Unit K L) (v : L) :
    (ZTensorPower.basis b 1).repr (tprodOne v) () = b.repr v () := by
  set c := b.repr v ()
  have hv : v = c • b () := (basis_unit_repr_smul b v).symm
  have h2 : (PiTensorProduct.tprod K (fun _ : Fin 1 => v)) =
      c • PiTensorProduct.tprod K (fun _ : Fin 1 => b ()) := by
    rw [hv]
    simpa using (PiTensorProduct.tprod K).map_smul_univ (fun _ : Fin 1 => c) (fun _ => b ())
  have h3 : (ZTensorPower.basis b (.ofNat 1) () : ZTensorPower K L (.ofNat 1)) =
      PiTensorProduct.tprod K (fun _ : Fin 1 => b ()) := ZTensorPower.basis_ofNat b 1
  change (ZTensorPower.basis b (.ofNat 1)).repr (PiTensorProduct.tprod K (fun _ : Fin 1 => v)) ()
    = c
  rw [h2, ← h3]
  exact (by simp : ((ZTensorPower.basis b (.ofNat 1)).repr
    (c • (ZTensorPower.basis b (.ofNat 1) ()))) () = c)

end Repr

end ExteriorForms

namespace ProductLine

section Charts

variable {k : Type u} [Field k]

/-- The coordinate `T` of an affine chart `j : 𝔸¹ ⟶ ℙ¹`, a section of `ℙ¹` over the chart. -/
private noncomputable def chartCoord (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j] : Γ(projectiveLine k, j.opensRange) :=
  (Spec.preimage (IsOpenImmersion.isoOfRangeEq (isAffineOpen_opensRange j).fromSpec j
    (by rw [IsAffineOpen.range_fromSpec]; rfl)).hom).hom Polynomial.X

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **Charts of `X × ℙ¹`.** For an affine open `U` of `X` and an affine chart `j` of `ℙ¹`, the open
`V = pr⁻¹ U ∩ q⁻¹ (j 𝔸¹)` of `X × ℙ¹` is affine, with `Γ(V) ≅ Γ(U)[T]` compatibly with `pr`, the
variable `T` being the pull-back of the coordinate of the chart. -/
private theorem exists_chart (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ (V : (pullback sX (projectiveLine k ↘ Spec (.of k))).Opens) (hV : IsAffineOpen V)
      (hVU : V ≤ pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ U)
      (hVj : V ≤ pullback.snd sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ j.opensRange),
      pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ U ⊓
          pullback.snd sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ j.opensRange ≤ V ∧
      ∃ e : Polynomial Γ(X, U) ≃+* Γ(pullback sX (projectiveLine k ↘ Spec (.of k)), V),
        (∀ a, e (Polynomial.C a) =
          ((pullback.fst sX (projectiveLine k ↘ Spec (.of k))).appLE U V hVU).hom a) ∧
        e Polynomial.X =
          ((pullback.snd sX (projectiveLine k ↘ Spec (.of k))).appLE j.opensRange V hVj).hom
            (chartCoord j) := by
  set sL := projectiveLine k ↘ Spec (.of k)
  set A := Γ(X, U)
  set ψ : CommRingCat.of k ⟶ A := Spec.preimage (hU.fromSpec ≫ sX)
  have hψ : Spec.map ψ = hU.fromSpec ≫ sX := Spec.map_preimage _
  letI : Algebra k A := ψ.hom.toAlgebra
  have hψ' : CommRingCat.ofHom (algebraMap k A) = ψ := rfl
  have hC : CommRingCat.ofHom (algebraMap k (Polynomial k)) =
      CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) := by
    rw [Polynomial.algebraMap_eq]
  let Ψ₀ : pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) ⟶ pullback sX sL :=
    pullback.map _ _ _ _ hU.fromSpec j (𝟙 _) (by rw [hψ', hψ, Category.comp_id])
      (by rw [hC, ← hjs, Category.comp_id])
  have hΨ₀ : IsOpenImmersion Ψ₀ :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs
      (IsOpenImmersion hU.fromSpec)) inferInstance (by rw [hψ', hψ]) (by rw [hC, ← hjs])
  let σ : A ⊗[k] Polynomial k →+* Polynomial A := (polyEquivTensor k A).symm.toRingEquiv.toRingHom
  have hσ : IsIso (Spec.map (CommRingCat.ofHom σ)) :=
    inferInstanceAs (IsIso (Spec.map ((polyEquivTensor k A).symm.toRingEquiv.toCommRingCatIso.hom)))
  let Ψ : Spec (.of (Polynomial A)) ⟶ pullback sX sL :=
    Spec.map (CommRingCat.ofHom σ) ≫ (pullbackSpecIso k A (Polynomial k)).inv ≫ Ψ₀
  have hΨpr : Ψ ≫ pullback.fst sX sL =
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ hU.fromSpec := by
    simp only [Ψ, Ψ₀, Category.assoc, pullback.lift_fst]
    rw [pullbackSpecIso_inv_fst_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext a : 2
    change (polyEquivTensor k A).symm (a ⊗ₜ 1) = Polynomial.C a
    rw [AlgEquiv.symm_apply_eq]
    simp [polyEquivTensor_apply]
  have hΨq : Ψ ≫ pullback.snd sX sL =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k A))) ≫ j := by
    simp only [Ψ, Ψ₀, Category.assoc, pullback.lift_snd]
    rw [pullbackSpecIso_inv_snd_assoc, ← Spec.map_comp_assoc]
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    change (polyEquivTensor k A).symm (1 ⊗ₜ p) = Polynomial.map (algebraMap k A) p
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
  have hrange : Set.range Ψ = Set.range Ψ₀ := by
    have h1 : Function.Surjective (Spec.map (CommRingCat.ofHom σ) ≫
        (pullbackSpecIso k A (Polynomial k)).inv) :=
      (inferInstance : Surjective (Spec.map (CommRingCat.ofHom σ) ≫
        (pullbackSpecIso k A (Polynomial k)).inv)).surj
    simp only [Ψ, ← Category.assoc]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, h1.range_eq, Set.image_univ]
  have hrange' : Set.range Ψ = pullback.fst sX sL ⁻¹' (U : Set X) ∩
      pullback.snd sX sL ⁻¹' Set.range j := by
    rw [hrange, Scheme.Pullback.range_map, hU.range_fromSpec]
  set V := Ψ.opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange Ψ
  have hVU : V ≤ pullback.fst sX sL ⁻¹ᵁ U := fun x hx => by
    have : x ∈ Set.range Ψ := hx
    rw [hrange'] at this
    exact this.1
  have hVj : V ≤ pullback.snd sX sL ⁻¹ᵁ j.opensRange := fun x hx => by
    have : x ∈ Set.range Ψ := hx
    rw [hrange'] at this
    exact this.2
  have hle : pullback.fst sX sL ⁻¹ᵁ U ⊓ pullback.snd sX sL ⁻¹ᵁ j.opensRange ≤ V := by
    intro x hx
    change x ∈ Set.range Ψ
    rw [hrange']
    exact hx
  refine ⟨V, hV, hVU, hVj, hle, ?_⟩
  let ι := IsOpenImmersion.isoOfRangeEq hV.fromSpec Ψ (by rw [hV.range_fromSpec]; rfl)
  have hι : ι.hom ≫ Ψ = hV.fromSpec := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let g : CommRingCat.of (Polynomial A) ⟶ Γ(pullback sX sL, V) := Spec.preimage ι.hom
  let g' : Γ(pullback sX sL, V) ⟶ CommRingCat.of (Polynomial A) := Spec.preimage ι.inv
  have hgg' : g ≫ g' = 𝟙 _ := Spec.map_injective (by simp [g, g'])
  have hg'g : g' ≫ g = 𝟙 _ := Spec.map_injective (by simp [g, g'])
  refine ⟨(⟨g, g', hgg', hg'g⟩ : CommRingCat.of (Polynomial A) ≅ _).commRingCatIsoToRingEquiv,
    fun a => ?_, ?_⟩
  · have key : Spec.map ((pullback.fst sX sL).appLE U V hVU) =
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A) ≫ g) := by
      rw [← cancel_mono hU.fromSpec, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hV, Spec.map_comp,
        Category.assoc, ← hΨpr, ← hι, Category.assoc]
      simp [g]
    have := Spec.map_injective key
    rw [this]
    rfl
  · set hj := isAffineOpen_opensRange j
    let ιj := IsOpenImmersion.isoOfRangeEq hj.fromSpec j
      (by rw [IsAffineOpen.range_fromSpec]; rfl)
    have hιj : ιj.hom ≫ j = hj.fromSpec := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    let gj : CommRingCat.of (Polynomial k) ⟶ Γ(projectiveLine k, j.opensRange) :=
      Spec.preimage ιj.hom
    let gj' : Γ(projectiveLine k, j.opensRange) ⟶ CommRingCat.of (Polynomial k) :=
      Spec.preimage ιj.inv
    have key : Spec.map ((pullback.snd sX sL).appLE j.opensRange V hVj) =
        Spec.map (gj' ≫ CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k A)) ≫ g) := by
      rw [← cancel_mono hj.fromSpec, IsAffineOpen.SpecMap_appLE_fromSpec _ hj hV, ← hι,
        Category.assoc, hΨq, ← hιj]
      simp [g, gj']
    have := Spec.map_injective key
    change _ = ((pullback.snd sX sL).appLE j.opensRange V hVj).hom (gj.hom Polynomial.X)
    rw [this]
    change g.hom Polynomial.X = g.hom
        ((CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k A))).hom
      ((gj ≫ gj').hom Polynomial.X))
    have hgj2 : gj ≫ gj' = 𝟙 _ := Spec.map_injective (by simp [gj, gj'])
    rw [hgj2]
    simp

/-- The germ of a restricted pull-back is the image of the germ under the stalk map. -/
private theorem germ_appLE_apply {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (e : V ≤ f ⁻¹ᵁ U) {y : Y} (hy : y ∈ V) (hfy : f y ∈ U) (a : Γ(Z, U)) :
    (Y.presheaf.germ V y hy).hom ((f.appLE U V e).hom a) =
      (f.stalkMap y).hom ((Z.presheaf.germ U (f y) hfy).hom a) := by
  have h : Z.presheaf.germ U (f y) hfy ≫ f.stalkMap y =
      f.appLE U V e ≫ Y.presheaf.germ V y hy := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  exact (congrArg (fun φ => φ.hom a) h).symm

/-- **Differentials at a point of `X × ℙ¹`.** At a point `x` of `X × ℙ¹` over an affine chart `j`
of `ℙ¹`, the differentials `Ω_{𝒪_{X×ℙ¹,x}/k}` are spanned by the image of `Ω_{𝒪_{X,pr x}/k}` and
the differential of the coordinate of the chart. -/
private theorem span_kaehler_stalk (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    (x : ↥(pullback sX (projectiveLine k ↘ Spec (.of k))))
    (hxj : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) x ∈ j.opensRange) :
    letI := stalkAlgebra sX (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x)
    letI := stalkAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) x
    letI := ((pullback.fst sX (projectiveLine k ↘ Spec (.of k))).stalkMap x).hom.toAlgebra
    haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sX
      (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) x
    Submodule.span ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
      (Set.range (KaehlerDifferential.map k k
        (X.presheaf.stalk (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x))
        ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)) ∪
      {(KaehlerDifferential.D k _ (((pullback.snd sX (projectiveLine k ↘ Spec (.of k))).stalkMap
        x).hom (((projectiveLine k).presheaf.germ j.opensRange _ hxj).hom (chartCoord j))))}) =
      ⊤ := by
  let := stalkAlgebra sX (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x)
  let := stalkAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) x
  let := ((pullback.fst sX (projectiveLine k ↘ Spec (.of k))).stalkMap x).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX
    (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) x
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hVU, hVj, hle, e, he1, he2⟩ := exists_chart sX j hjs hU
  have hxV : x ∈ V := hle ⟨hxU, hxj⟩
  let := (pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  let := sectionAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) V
  have := isScalarTower_section_stalk (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)
    V ⟨x, hxV⟩
  have hgen : ∀ r : Γ(pullback sX (projectiveLine k ↘ Spec (.of k)), V),
      KaehlerDifferential.map k k Γ(pullback sX (projectiveLine k ↘ Spec (.of k)), V)
        ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
        (KaehlerDifferential.D k _ r) ∈ Submodule.span
          ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
          (Set.range (KaehlerDifferential.map k k
            (X.presheaf.stalk (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x))
            ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)) ∪
          {(KaehlerDifferential.D k _ (((pullback.snd sX (projectiveLine k ↘ Spec (.of k))).stalkMap
            x).hom (((projectiveLine k).presheaf.germ j.opensRange _ hxj).hom
              (chartCoord j))))}) := by
    intro r
    obtain ⟨p, rfl⟩ := e.surjective r
    induction p using Polynomial.induction_on with
    | C a =>
      rw [he1, KaehlerDifferential.map_D]
      refine Submodule.subset_span (Or.inl ⟨KaehlerDifferential.D k _
        ((X.presheaf.germ U _ hxU).hom a), ?_⟩)
      rw [KaehlerDifferential.map_D]
      congr 1
      exact (germ_appLE_apply _ hVU hxV hxU a).symm
    | add p p' hp hp' =>
      rw [map_add, map_add, map_add]
      exact add_mem hp hp'
    | monomial n a h =>
      have : Polynomial.C a * Polynomial.X ^ (n + 1) =
          (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [this, map_mul, Derivation.leibniz, map_add, map_smul, map_smul]
      refine add_mem (Submodule.smul_of_tower_mem _ _ ?_) (Submodule.smul_of_tower_mem _ _ h)
      rw [he2, KaehlerDifferential.map_D]
      refine Submodule.subset_span (Or.inr ?_)
      rw [Set.mem_singleton_iff]
      congr 1
      exact germ_appLE_apply _ hVj hxV hxj _
  have htop := KaehlerDifferential.span_range_map_derivation_of_isLocalization k
    Γ(pullback sX (projectiveLine k ↘ Spec (.of k)), V)
    ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  refine eq_top_iff.mpr (htop.symm.le.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨r, rfl⟩
  exact hgen r

end Charts

section ProductForm

open ExteriorForms

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The coordinate of the chart `j` of `ℙ¹`, as a rational function on `ℙ¹`. -/
private noncomputable def chartRat (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j]
    [IsIntegral (projectiveLine k)] : (projectiveLine k).functionField :=
  haveI : Nonempty j.opensRange := ⟨⟨_, Set.mem_range_self (Nonempty.some inferInstance)⟩⟩
  ((projectiveLine k).germToFunctionField j.opensRange).hom (chartCoord j)

/-- The coordinate of the chart `j` of `ℙ¹`, pulled back to a rational function on `X × ℙ¹`. -/
private noncomputable def chartFun (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j]
    [IsIntegral (projectiveLine k)] [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] :
    (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField :=
  functionFieldMap (pullback.snd sX (projectiveLine k ↘ Spec (.of k))) (chartRat j)

/-- The `1`-canonical form `ω^{⊗1}` of a top form `ω` on `X`. -/
private noncomputable def tprodForm [IsIntegral X] {n : ℕ}
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    RationalPluriForms sX n 1 :=
  letI := functionFieldAlgebra sX
  tprodOne ω

variable [IsIntegral X] [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
  (s : pullback sX (projectiveLine k ↘ Spec (.of k)) ⟶ Spec (.of k))
  (hs : s = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)

include hs in
/-- The extension `k(X) → k(X × ℙ¹)` is `k`-linear for the structure morphism `s = pr ≫ s_X`. -/
private theorem isScalarTower_functionFieldMap_fst :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra s
    letI := functionFieldMapAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))
    IsScalarTower k X.functionField
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField := by
  subst hs
  exact isScalarTower_functionFieldMap sX _

/-- **The product form** `dz ∧ pr^*ω` on `X × ℙ¹`, for a top form `ω` on `X` and the coordinate
`z` of a chart of `ℙ¹`; `s = pr ≫ s_X` is the structure morphism of `X × ℙ¹`. -/
private noncomputable def prodForm (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j]
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] (n : ℕ)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    RationalPluriForms s (n + 1) 1 :=
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra s
  letI := functionFieldMapAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))
  haveI := isScalarTower_functionFieldMap_fst sX s hs
  tprodOne (wedgeLeft _ n (KaehlerDifferential.D k _ (chartFun sX j))
    (topFormsMap k X.functionField _ n ω))

end ProductForm

section ProductFormOrder

open ExteriorForms

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
  (s : pullback sX (projectiveLine k ↘ Spec (.of k)) ⟶ Spec (.of k))
  (hs : s = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)

include hs in
/-- **The product form at a point.** At a point `x` of `X × ℙ¹` over the chart `j`, with `σ` a
generator of the top forms of `𝒪_{X,y}`, `y = pr x`, whose differentials are spanned by `n`
elements, `dz ∧ pr^*σ` generates the top forms of `𝒪_{X×ℙ¹,x}`, and
`dz ∧ pr^*(c σ) = pr^*c · (dz ∧ pr^*σ)` in `k(X × ℙ¹)`. -/
private theorem exists_generator_prodForm (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j] (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] {n : ℕ}
    (x : ↥(pullback sX (projectiveLine k ↘ Spec (.of k))))
    (hx : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) x ∈ j.opensRange) (y : X)
    (hy : pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x = y)
    {e : Fin n → (letI := stalkAlgebra sX y; Ω[X.presheaf.stalk y⁄k])}
    (he : Submodule.span (X.presheaf.stalk y) (Set.range e) = ⊤)
    {σ : letI := stalkAlgebra sX y; ⋀[X.presheaf.stalk y]^n Ω[X.presheaf.stalk y⁄k]}
    (hσ : Submodule.span (X.presheaf.stalk y) {σ} = ⊤) :
    letI := stalkAlgebra s x
    letI := functionFieldAlgebra s
    haveI := isScalarTower_stalk_functionField s x
    ∃ σ' : ⋀[(pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x]^(n + 1)
        Ω[(pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x⁄k],
      Submodule.span ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x) {σ'} = ⊤ ∧
        ∀ c : X.functionField,
        prodForm sX s hs j n
          (letI := stalkAlgebra sX y; letI := functionFieldAlgebra sX;
            haveI := isScalarTower_stalk_functionField sX y;
            c • topFormsMap k _ X.functionField n σ) =
          tprodOne ((functionFieldMap (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) c) •
              topFormsMap k _ (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField
                (n + 1) σ') := by
  subst hs hy
  let pr := pullback.fst sX (projectiveLine k ↘ Spec (.of k))
  let q := pullback.snd sX (projectiveLine k ↘ Spec (.of k))
  let := stalkAlgebra sX (pr x)
  let := stalkAlgebra (pr ≫ sX) x
  let := (pr.stalkMap x).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX pr x
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (pr ≫ sX)
  let := functionFieldMapAlgebra pr
  have := isScalarTower_functionFieldMap sX pr
  have := isScalarTower_stalk_functionField sX (pr x)
  have := isScalarTower_stalk_functionField (pr ≫ sX) x
  let : Algebra (X.presheaf.stalk (pr x))
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField :=
    ((algebraMap X.functionField (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).comp
      (algebraMap (X.presheaf.stalk (pr x)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (pr x)) X.functionField
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk (pr x))
      ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField :=
    IsScalarTower.of_algebraMap_eq fun a => functionFieldMap_algebraMap_stalk pr x a
  have : IsScalarTower k (X.presheaf.stalk (pr x))
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField
          (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField,
        IsScalarTower.algebraMap_apply k (X.presheaf.stalk (pr x)) X.functionField]
      rfl
  obtain ⟨zx, hzx⟩ : ∃ z : (pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x,
      z = (q.stalkMap x).hom
        (((projectiveLine k).presheaf.germ j.opensRange _ hx).hom (chartCoord j)) := ⟨_, rfl⟩
  have hz : algebraMap _ (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField zx =
      chartFun sX j := by
    rw [hzx, ← functionFieldMap_algebraMap_stalk]
    haveI : Nonempty j.opensRange := ⟨⟨_, hx⟩⟩
    exact congrArg _ (Scheme.algebraMap_germ_eq_germToFunctionField (projectiveLine k) hx
      (chartCoord j))
  have hspan := span_kaehler_stalk sX j hjs x hx
  rw [← hzx] at hspan
  refine ⟨_, span_singleton_wedgeLeft_topFormsMap_eq_top he zx hspan hσ, fun c => ?_⟩
  have e1 := topFormsMap_wedgeLeft_D (k := k)
    (A := (pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
    (B := (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField) n zx
    (topFormsMap k (X.presheaf.stalk (pr x)) _ n σ)
  have e2 := topFormsMap_topFormsMap (k := k) (A := X.presheaf.stalk (pr x))
    (B := (pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
    (C := (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField) n σ
  have e3 := topFormsMap_topFormsMap (k := k) (A := X.presheaf.stalk (pr x))
    (B := X.functionField)
    (C := (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField) n σ
  have hT := e1.trans ((congrArg (fun z => wedgeLeft
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField n (KaehlerDifferential.D k _ z)
      (topFormsMap k ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)
        (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField n
        (topFormsMap k (X.presheaf.stalk (pr x)) _ n σ))) hz).trans
    (congrArg (wedgeLeft (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField n
      (KaehlerDifferential.D k _ (chartFun sX j))) (e2.trans e3.symm)))
  have e4 : topFormsMap k X.functionField
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField
      n (c • topFormsMap k (X.presheaf.stalk (pr x)) X.functionField n σ) =
      functionFieldMap pr c • topFormsMap k X.functionField _ n
        (topFormsMap k (X.presheaf.stalk (pr x)) X.functionField n σ) :=
    ((topFormsMap k X.functionField
        (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField n).map_smul c _).trans
      (algebraMap_smul (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField c _).symm
  have e5 : wedgeLeft _ n (KaehlerDifferential.D k _ (chartFun sX j))
      (topFormsMap k X.functionField (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField
        n (c • topFormsMap k (X.presheaf.stalk (pr x)) X.functionField n σ)) =
      functionFieldMap pr c • wedgeLeft _ n (KaehlerDifferential.D k _ (chartFun sX j))
        (topFormsMap k X.functionField _ n
          (topFormsMap k (X.presheaf.stalk (pr x)) X.functionField n σ)) :=
    (congrArg (wedgeLeft (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField n
      (KaehlerDifferential.D k _ (chartFun sX j))) e4).trans
      ((wedgeLeft (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField n
        (KaehlerDifferential.D k _ (chartFun sX j))).map_smul (functionFieldMap pr c) _)
  exact (congrArg tprodOne e5).trans
    (congrArg (fun w => tprodOne (functionFieldMap pr c • w)) hT.symm)

variable [IsLocallyNoetherian (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback sX (projectiveLine k ↘ Spec (.of k)))] [LocallyOfFiniteType s]

include hs in
/-- **The order of a product form.** Let `G` be a prime divisor of `X × ℙ¹` whose generic point
lies over the chart `j` of `ℙ¹`, `σ` a generator of the top forms of `𝒪_{X,y}`, `y = pr η_G`,
whose differentials are spanned by `n` elements, and `c ∈ k(X)`. Then
`ord_G(dz ∧ pr^*(c σ)) = ord_G(pr^* c)`. -/
private theorem ordForm_prodForm (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] {n : ℕ}
    (hd : letI := functionFieldAlgebra s
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (G : MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))))
    (hG : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint ∈ j.opensRange)
    (y : X) (hy : pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint = y)
    {e : Fin n → (letI := stalkAlgebra sX y; Ω[X.presheaf.stalk y⁄k])}
    (he : Submodule.span (X.presheaf.stalk y) (Set.range e) = ⊤)
    {σ : letI := stalkAlgebra sX y; ⋀[X.presheaf.stalk y]^n Ω[X.presheaf.stalk y⁄k]}
    (hσ : Submodule.span (X.presheaf.stalk y) {σ} = ⊤) (c : X.functionField) :
    G.ordForm (sX := s) (prodForm sX s hs j n
      (letI := stalkAlgebra sX y; letI := functionFieldAlgebra sX;
        haveI := isScalarTower_stalk_functionField sX y;
        c • topFormsMap k _ X.functionField n σ)) =
      (pullback sX (projectiveLine k ↘ Spec (.of k))).ord
        (functionFieldMap (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) c)
          G.genericPoint := by
  let := stalkAlgebra s G.genericPoint
  let := functionFieldAlgebra s
  have := isScalarTower_stalk_functionField s G.genericPoint
  obtain ⟨σ', hσ', hτ⟩ := exists_generator_prodForm sX s hs j hjs G.genericPoint hG y hy he hσ
  have h0 := G.topFormsMap_ne_zero (sX := s) hd hσ'
  rw [G.ordForm_eq _ hσ' h0, hτ c]
  unfold formCoeff
  rw [repr_basis_one_tprod, ← topFormsBasis_apply hσ' h0 (), LinearEquiv.map_smul,
    Module.Basis.repr_self]
  simp

end ProductFormOrder

section ProductDivisors

variable {k : Type u} [Field k]

/-! ### Local algebra of `A[X]` -/

/-- The extension of a prime of `A` to an `A`-algebra isomorphic to `A[X]` is prime. -/
private theorem isPrime_map_of_polyEquiv {A R : Type*} [CommRing A] [CommRing R] (α : A →+* R)
    (e : Polynomial A ≃+* R) (he : ∀ a, e (Polynomial.C a) = α a) (𝔭 : Ideal A) [𝔭.IsPrime] :
    (Ideal.map α 𝔭).IsPrime := by
  have : α = (e : Polynomial A →+* R).comp Polynomial.C := by ext a; exact (he a).symm
  rw [this, ← Ideal.map_map]
  exact Ideal.map_isPrime_of_equiv e

/-- The structure map `A → R` of an `A`-algebra isomorphic to `A[X]` is injective. -/
private theorem injective_of_polyEquiv {A R : Type*} [CommRing A] [CommRing R] (α : A →+* R)
    (e : Polynomial A ≃+* R) (he : ∀ a, e (Polynomial.C a) = α a) : Function.Injective α := by
  have : (α : A → R) = e ∘ Polynomial.C := by ext a; exact (he a).symm
  rw [this]
  exact e.injective.comp Polynomial.C_injective

-- The `overlappingInstances` linter fails to synthesize on these `[IsDomain Γ(X, V)]` binders.
set_option linter.overlappingInstances false in
/-- If `𝔭 Γ(V)` is prime for the prime `𝔭` of `f(x)`, the stalk map at `x` carries uniformizers
of the discrete valuation ring `𝒪_{Y,f(x)}` to uniformizers of `𝒪_{X,x}`. -/
private theorem irreducible_stalkMap {X Y : Scheme} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {x : X}
    (hx : x ∈ V) [IsDomain Γ(X, V)]
    (hprime : (Ideal.map (f.appLE U V hVU).hom
      (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal).IsPrime)
    (hinj : Function.Injective (f.appLE U V hVU).hom)
    [IsDomain (Y.presheaf.stalk (f x))] [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {ϖ : Y.presheaf.stalk (f x)} (hϖ : Irreducible ϖ) : Irreducible ((f.stalkMap x).hom ϖ) := by
  have hfx : f x ∈ U := hVU hx
  let := Y.presheaf.algebra_section_stalk ⟨f x, hfx⟩
  have hlocY := hU.isLocalization_stalk ⟨f x, hfx⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hlocX := hV.isLocalization_stalk ⟨x, hx⟩
  set 𝔭 := (hU.primeIdealOf ⟨f x, hfx⟩).asIdeal
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  set α := (f.appLE U V hVU).hom
  have hcomp : (f.stalkMap x).hom.comp (algebraMap Γ(Y, U) (Y.presheaf.stalk (f x))) =
      (algebraMap Γ(X, V) (X.presheaf.stalk x)).comp α := by
    ext a
    exact (germ_appLE_apply f hVU hx hfx a).symm
  have hJP : Ideal.map α 𝔭 ≤ P := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx
    have h' : Ideal.comap α P = 𝔭 := congrArg PrimeSpectrum.asIdeal h
    rw [← h']
    exact Ideal.map_comap_le
  have h𝔭 : 𝔭 ≠ ⊥ := by
    intro h
    have hm := IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 (Y.presheaf.stalk (f x))
    rw [h, Ideal.map_bot] at hm
    exact IsDiscreteValuationRing.not_a_field _ hm.symm
  have hJ0 : Ideal.map α 𝔭 ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  have hinjX : Function.Injective (algebraMap Γ(X, V) (X.presheaf.stalk x)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)
  have hprimeX : (Ideal.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) (Ideal.map α 𝔭)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ _ hprime
      (by
        rw [Set.disjoint_left]
        intro a ha ha'
        exact ha (hJP ha'))
  have hne : Ideal.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) (Ideal.map α 𝔭) ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinjX]
  have hmax : Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 (Y.presheaf.stalk (f x)), Ideal.map_map,
      hcomp, ← Ideal.map_map]
    exact IsLocalRing.eq_maximalIdeal (hprimeX.isMaximal hne)
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ ⊢
  rw [← hmax, hϖ, Ideal.map_span, Set.image_singleton]

/-- Every point of `ℙ¹` lies in one of its two standard charts. -/
private theorem exists_projectiveLine_chart (z : projectiveLine k) :
    ∃ (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) (_ : IsOpenImmersion j),
      j ≫ (projectiveLine k ↘ Spec (.of k)) =
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) ∧ z ∈ j.opensRange := by
  obtain ⟨i, y, hy⟩ := (projectiveLineGluingData k).ι_jointly_surjective z
  obtain ⟨⟨_ | _⟩⟩ := i
  · exact ⟨projectiveLineXChart k, inferInstance, projectiveLineXChart_comp_structureMorphism k,
      ⟨y, hy⟩⟩
  · exact ⟨projectiveLineYChart k, inferInstance, projectiveLineYChart_comp_structureMorphism k,
      ⟨y, hy⟩⟩

/-- `ℙ¹` is a line in the sense of `MMP.Fourfold.product_line_basic`: it is `ℙ¹` itself. -/
private theorem projectiveLine_isLine :
    (∃ e : projectiveLine k ≅ projectiveLine k,
      e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = projectiveLine k ↘ Spec (.of k)) ∨
      ∃ e : projectiveLine k ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) =
          projectiveLine k ↘ Spec (.of k) :=
  Or.inl ⟨Iso.refl _, Category.id_comp _⟩

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

-- The `overlappingInstances` linter fails to synthesize on the `IsDomain` instances below.
set_option linter.overlappingInstances false in
/-- **Uniformizers stay uniformizers along `pr : X × ℙ¹ ⟶ X`** at a point `x` with discrete
valuation rings `𝒪_{X,pr x}` and `𝒪_{X × ℙ¹,x}`. -/
private theorem irreducible_stalkMap_fst
    [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
    (x : ↥(pullback sX (projectiveLine k ↘ Spec (.of k))))
    [IsDomain (X.presheaf.stalk (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x))]
    [IsDiscreteValuationRing
      (X.presheaf.stalk (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x))]
    [IsDomain ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)]
    [IsDiscreteValuationRing ((pullback sX (projectiveLine k ↘ Spec (.of k))).presheaf.stalk x)]
    {ϖ : X.presheaf.stalk (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x)}
    (hϖ : Irreducible ϖ) :
    Irreducible (((pullback.fst sX (projectiveLine k ↘ Spec (.of k))).stalkMap x).hom ϖ) := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨j, hj, hjs, hxj⟩ :=
    exists_projectiveLine_chart (pullback.snd sX (projectiveLine k ↘ Spec (.of k)) x)
  obtain ⟨V, hV, hVU, hVj, hle, e, he1, -⟩ := exists_chart sX j hjs hU
  have hxV : x ∈ V := hle ⟨hxU, hxj⟩
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact irreducible_stalkMap _ hU hV hVU hxV (isPrime_map_of_polyEquiv _ e he1 _)
    (injective_of_polyEquiv _ e he1) hϖ

/-! ### Prime divisors of `X × ℙ¹` -/

/-- A point whose closure has dense image maps to the generic point. -/
private theorem eq_genericPoint_of_dense {X' Y' : Scheme.{u}} [IsIntegral Y'] (f : X' ⟶ Y') {z : X'}
    (hz : Dense (f '' closure {z})) : f z = genericPoint Y' := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y')
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hz.closure_eq]
  refine closure_minimal ?_ isClosed_closure
  refine (image_closure_subset_closure_image f.continuous).trans ?_
  rw [Set.image_singleton]

/-- On a locally Noetherian normal scheme a prime divisor is determined by its support. -/
private theorem eq_of_support_eq {X' : Scheme.{u}} [IsLocallyNoetherian X'] [IsNormal X']
    {E E' : MMP.Mori.PrimeDivisor X'} (h : E.support = E'.support) : E = E' := by
  refine (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E ?_).symm
  rw [← h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- If `E = f⁻¹(Γ)` for a surjective `f`, then `f` maps `η_E` to `η_Γ`. -/
private theorem genericPoint_eq_of_support_eq_preimage {X' Y' : Scheme.{u}} (f : X' ⟶ Y')
    (hf : Function.Surjective f) {E : MMP.Mori.PrimeDivisor X'} {Γ : MMP.Mori.PrimeDivisor Y'}
    (h : E.support = f ⁻¹' Γ.support) : Γ.genericPoint = f E.genericPoint := by
  have hEη : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  refine IsGenericPoint.eq (S := Γ.support) ?_ ?_
  · exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure Γ).symm
  · refine subset_antisymm (closure_minimal ?_ Γ.idealSheaf.support.isClosed) ?_
    · rw [Set.singleton_subset_iff]
      exact (h ▸ hEη : E.genericPoint ∈ f ⁻¹' Γ.support)
    · rw [← hf.image_preimage Γ.support, ← h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine (image_closure_subset_closure_image f.continuous).trans ?_
      rw [Set.image_singleton]

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsLocallyNoetherian (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback sX (projectiveLine k ↘ Spec (.of k)))]

/-- **The prime divisors of `X × ℙ¹`.** The prime divisors `Γ × ℙ¹ = pr⁻¹(Γ)`, with
`pr(η_{Γ × ℙ¹}) = η_Γ`; every other prime divisor dominates `X`. -/
private theorem exists_preimagePrimeDivisor (hX : IsNormalVariety k sX) :
    ∃ ι : MMP.Mori.PrimeDivisor X →
        MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))),
      (∀ Γ, (ι Γ).support = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹' Γ.support) ∧
      (∀ E Γ, E.support = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹' Γ.support →
        E = ι Γ) ∧
      (∀ E ∉ Set.range ι,
        pullback.fst sX (projectiveLine k ↘ Spec (.of k)) E.genericPoint = genericPoint X) ∧
      ∀ Γ, Γ.genericPoint =
        pullback.fst sX (projectiveLine k ↘ Spec (.of k)) (ι Γ).genericPoint := by
  obtain ⟨⟨-, hsurj, -, -, -, -⟩, -⟩ := 
    MMP.Fourfold.product_line_basic sX _ hX (projectiveLine_isLine (k := k))
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  obtain ⟨_, _, _, hLd⟩ := MMP.Fourfold.smooth_geometricallyIrreducible_isVariety_dim_line _
    (projectiveLine_isLine (k := k))
  have hcl := MMP.primeDivisor_pullback_eq_preimage_or_dense_of_smooth sX
    (projectiveLine k ↘ Spec (.of k)) hLd
  have hs : Function.Surjective (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) := hsurj.surj
  choose ι hι using hcl.1
  have hιeq : ∀ (E : MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))))
      (Γ : MMP.Mori.PrimeDivisor X),
      E.support = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹' Γ.support → E = ι Γ :=
    fun E Γ h => eq_of_support_eq (h.trans (hι Γ).symm)
  refine ⟨ι, hι, hιeq, fun E hE => ?_, fun Γ => genericPoint_eq_of_support_eq_preimage _ hs (hι Γ)⟩
  rcases hcl.2 E with ⟨Γ, -, hEΓ⟩ | hd
  · exact absurd ⟨Γ, (hιeq E Γ hEΓ).symm⟩ hE
  · refine eq_genericPoint_of_dense _ ?_
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hd

omit [IsLocallyNoetherian (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback sX (projectiveLine k ↘ Spec (.of k)))] in
/-- A prime divisor `Γ × ℙ¹` dominates `ℙ¹`. -/
private theorem snd_genericPoint_eq_of_support_eq_preimage (hX : IsNormalVariety k sX)
    (Γ : MMP.Mori.PrimeDivisor X)
    (G : MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))))
    (hG : G.support = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹' Γ.support) :
    pullback.snd sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint =
      genericPoint (projectiveLine k) := by
  haveI : IsIntegral (projectiveLine k) :=
    (MMP.Fourfold.smooth_geometricallyIrreducible_isVariety_dim_line _
      (projectiveLine_isLine (k := k))).2.2.1.toIsIntegral
  refine eq_genericPoint_of_dense _ ?_
  rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hG]
  have hall : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) ''
      (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹' Γ.support) = Set.univ := by
    refine Set.eq_univ_of_forall fun l => ?_
    have hηΓ : Γ.genericPoint ∈ Γ.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := sX)
      (g := projectiveLine k ↘ Spec (.of k)) Γ.genericPoint l (Subsingleton.elim _ _)
    exact ⟨p, by rw [Set.mem_preimage, hp1]; exact hηΓ, hp2⟩
  rw [hall]
  exact dense_univ

variable [PerfectField k]

/-- **Orders of pulled-back functions along `Γ × ℙ¹`**: `ord_{Γ × ℙ¹}(pr^* c) = ord_Γ(c)`. -/
private theorem ord_functionFieldMap_fst_of_genericPoint_eq
    [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
    (G : MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))))
    (Γ : MMP.Mori.PrimeDivisor X)
    (hGΓ : Γ.genericPoint = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint)
    {c : X.functionField} (hc : c ≠ 0) :
    (pullback sX (projectiveLine k ↘ Spec (.of k))).ord
      (functionFieldMap (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) c) G.genericPoint =
      X.ord c Γ.genericPoint := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk
      (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint)) :=
    hGΓ ▸ Γ.isDiscreteValuationRing_localRing
  haveI := G.isDiscreteValuationRing_localRing
  rw [OrderOfVanishing.ord_functionFieldMap_eq _ G.coheight_genericPoint
    (hGΓ ▸ Γ.coheight_genericPoint) (fun ϖ hϖ => irreducible_stalkMap_fst sX _ hϖ) hc, ← hGΓ]

/-- **Orders of pulled-back functions along a dominating prime divisor** vanish. -/
private theorem ord_functionFieldMap_fst_of_genericPoint_eq_genericPoint
    [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
    (G : MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))))
    (hG : pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint = genericPoint X)
    {c : X.functionField} (hc : c ≠ 0) :
    (pullback sX (projectiveLine k ↘ Spec (.of k))).ord
      (functionFieldMap (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) c) G.genericPoint =
      0 := by
  obtain ⟨a, ha⟩ := MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint _ hG c
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk
      (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint)) X.functionField) :=
    IsFractionRing.injective _ _
  have hu : IsUnit a := by
    obtain ⟨b, hb⟩ := MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint _
      hG c⁻¹
    refine isUnit_iff_exists_inv.mpr ⟨b, hinj ?_⟩
    rw [map_mul, ha, hb, mul_inv_cancel₀ hc, map_one]
  rw [← ha, MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact OrderOfVanishing.ord_algebraMap_of_isUnit G.coheight_genericPoint (hu.map _)

end ProductDivisors

section ProductFormDivisors

open ExteriorForms

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

omit [PerfectField k] in
/-- A top form of a stalk with spanning differentials, as a multiple of a generator. -/
private theorem eq_smul_topFormsMap_of_span_eq_top [IsIntegral X] (y : X)
    {n : ℕ} {σ : letI := stalkAlgebra sX y; ⋀[X.presheaf.stalk y]^n Ω[X.presheaf.stalk y⁄k]}
    (hσ : Submodule.span _ {σ} = ⊤)
    (h0 : letI := stalkAlgebra sX y
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX y
      topFormsMap k (X.presheaf.stalk y) X.functionField n σ ≠ 0)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    letI := stalkAlgebra sX y
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX y
    ω = (topFormsBasis (X.presheaf.stalk y) hσ h0).repr ω () •
      topFormsMap k (X.presheaf.stalk y) X.functionField n σ := by
  let := stalkAlgebra sX y
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX y
  rw [← topFormsBasis_apply hσ h0 ()]
  exact (basis_unit_repr_smul _ ω).symm

variable [IsIntegral X] [LocallyOfFiniteType sX]

/-- On a variety with `trdeg_k k(X) = n`, at a point `y` with `y = η_X`, `Ω_{𝒪_{X,y}/k}` is
spanned by `n` elements and the line `Ω^n_{𝒪_{X,y}/k}` has a generator with nonzero image. -/
private theorem exists_generator_genericPoint {n : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (y : X) (hy : y = genericPoint X) :
    letI := stalkAlgebra sX y
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX y
    ∃ (e : Fin n → Ω[X.presheaf.stalk y⁄k])
      (σ : ⋀[X.presheaf.stalk y]^n Ω[X.presheaf.stalk y⁄k]),
      Submodule.span (X.presheaf.stalk y) (Set.range e) = ⊤ ∧
        Submodule.span (X.presheaf.stalk y) {σ} = ⊤ ∧
        topFormsMap k (X.presheaf.stalk y) X.functionField n σ ≠ 0 := by
  let := stalkAlgebra sX y
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX y
  have hsurj := MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint y hy
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk y) X.functionField) :=
    IsFractionRing.injective _ _
  let eA : X.presheaf.stalk y ≃ₐ[k] X.functionField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k _ _) ⟨hinj, hsurj⟩
  have hF : IsField (X.presheaf.stalk y) :=
    MulEquiv.isField (Field.toIsField X.functionField) eA.toMulEquiv
  letI : Field (X.presheaf.stalk y) := hF.toField
  have := essFiniteType_functionField (sX := sX)
  haveI : Algebra.EssFiniteType k (X.presheaf.stalk y) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eA).mpr inferInstance
  have htr : (Algebra.trdeg k (X.presheaf.stalk y)).toNat = n := by
    rwa [eA.trdeg_eq]
  have hK : Module.finrank (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄k] = n :=
    (finrank_kaehlerDifferential_eq_trdeg k _).trans htr
  have : FiniteDimensional (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k _).1
  obtain ⟨σ, hσ, h0⟩ := exists_topForms_generator_of_free (K := X.functionField) hK
  exact ⟨Module.finBasisOfFinrankEq _ _ hK, σ, (Module.finBasisOfFinrankEq _ _ hK).span_eq, hσ, h0⟩

variable [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsLocallyNoetherian (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
  (s : pullback sX (projectiveLine k ↘ Spec (.of k)) ⟶ Spec (.of k))
  (hs : s = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) [LocallyOfFiniteType s]

include hs in
/-- **The product form along `Γ × ℙ¹`**: `ord_{Γ × ℙ¹}(dz ∧ pr^*ω) = ord_Γ(ω)`. -/
private theorem ordForm_prodForm_of_support_eq (hX : IsNormalVariety k sX)
    (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] {n : ℕ}
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (hd : letI := functionFieldAlgebra s
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (Γ : MMP.Mori.PrimeDivisor X)
    (G : MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))))
    (hGΓ : G.support = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹' Γ.support)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    G.ordForm (sX := s) (prodForm sX s hs j n ω) =
      Γ.ordForm (tprodForm sX ω) := by
  obtain ⟨⟨-, hsurj, -, -, -, -⟩, -⟩ := 
    MMP.Fourfold.product_line_basic sX _ hX (projectiveLine_isLine (k := k))
  have hgen := genericPoint_eq_of_support_eq_preimage _ hsurj.surj hGΓ
  have hGj : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint ∈ j.opensRange := by
    rw [snd_genericPoint_eq_of_support_eq_preimage sX hX Γ G hGΓ]
    exact ((genericPoint_spec (projectiveLine k)).mem_open_set_iff j.opensRange.isOpen).mpr
      ⟨_, Set.mem_univ _, Set.mem_range_self (Nonempty.some inferInstance)⟩
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  obtain ⟨_, _⟩ := Γ.free_kaehlerDifferential_localRing (sX := sX)
  have hrank := Γ.finrank_kaehlerDifferential_localRing.trans hdX
  obtain ⟨σ, hσ, h0⟩ := Γ.exists_topForms_generator hdX
  have hω := eq_smul_topFormsMap_of_span_eq_top sX Γ.genericPoint hσ h0 ω
  set c := (topFormsBasis Γ.localRing hσ h0).repr ω ()
  rw [hω, ordForm_prodForm sX s hs j hjs hd G hGj Γ.genericPoint hgen.symm
    (Module.finBasisOfFinrankEq _ _ hrank).span_eq hσ c, Γ.ordForm_eq _ hσ h0]
  unfold formCoeff tprodForm
  rw [repr_basis_one_tprod, ← hω]
  change _ = X.ord c Γ.genericPoint
  by_cases hc : c = 0
  · rw [hc]; simp
  · exact ord_functionFieldMap_fst_of_genericPoint_eq sX G Γ hgen hc

include hs in
/-- **The product form along a dominating prime divisor** over the chart `j` has order `0`. -/
private theorem ordForm_prodForm_of_genericPoint_eq
    (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] {n : ℕ}
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (hd : letI := functionFieldAlgebra s
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (G : MMP.Mori.PrimeDivisor (pullback sX (projectiveLine k ↘ Spec (.of k))))
    (hG0 : pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint = genericPoint X)
    (hGj : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint ∈ j.opensRange)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    G.ordForm (sX := s) (prodForm sX s hs j n ω) = 0 := by
  let := stalkAlgebra sX (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX
    (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint)
  obtain ⟨e, σ, he, hσ, h0⟩ := exists_generator_genericPoint sX hdX _ hG0
  have hω := eq_smul_topFormsMap_of_span_eq_top sX _ hσ h0 ω
  obtain ⟨c, hc⟩ : ∃ c, c = (topFormsBasis (X.presheaf.stalk
      (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint)) hσ h0).repr ω () :=
    ⟨_, rfl⟩
  rw [← hc] at hω
  rw [hω, ordForm_prodForm sX s hs j hjs hd G hGj _ rfl he hσ c]
  by_cases hc0 : c = 0
  · rw [hc0]; simp
  · exact ord_functionFieldMap_fst_of_genericPoint_eq_genericPoint sX G hG0 hc0

end ProductFormDivisors

section Functoriality

open ExteriorForms

/-- **Pull-back of a `1`-fold tensor** along a pull-back generator: `u^*(v^{⊗1}) = (u^*v)^{⊗1}`. -/
private theorem pullbackForms_tprod {k K K' : Type*} [CommRing k] [Field K] [Field K'] [Algebra k K]
    [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ} {ω₀ : ⋀[K]^d Ω[K⁄k]}
    (hω : IsPullbackGenerator K' ω₀) (v : ⋀[K]^d Ω[K⁄k]) :
    pullbackForms (K' := K') 1 (tprodOne v) = tprodOne (topFormsMap k K K' d v) := by
  rw [pullbackForms_eq hω, pullbackFormsAlong, repr_basis_one_tprod]
  set b := basisOfSpanSingleton hω.1 hω.ne_zero
  set b' := basisOfSpanSingleton hω.2.1 hω.2.2
  have hv : v = b.repr v () • ω₀ := by
    conv_lhs => rw [← basis_unit_repr_smul b v]
    simp [b]
  have h4 : (PiTensorProduct.tprod K' fun _ : Fin 1 => topFormsMap k K K' d v) =
      algebraMap K K' (b.repr v ()) • PiTensorProduct.tprod K' (fun _ : Fin 1 => b' ()) := by
    conv_lhs => rw [hv, map_smul, ← algebraMap_smul K']
    simpa [b'] using (PiTensorProduct.tprod K').map_smul_univ
      (fun _ : Fin 1 => algebraMap K K' (b.repr v ())) (fun _ => topFormsMap k K K' d ω₀)
  have h3 := ZTensorPower.basis_ofNat b' 1
  change algebraMap K K' (b.repr v ()) • (ZTensorPower.basis b' (.ofNat 1) () :
    PiTensorProduct K' fun _ : Fin 1 => (⋀[K']^d Ω[K'⁄k])) =
    PiTensorProduct.tprod K' fun _ : Fin 1 => topFormsMap k K K' d v
  rw [h3, h4]
  rfl

/-- The morphism `μ × id : W × ℙ¹ ⟶ X × ℙ¹`. -/
private noncomputable abbrev prodMap {k : Type u} [Field k] {X W : Scheme.{u}}
    (sX : X ⟶ Spec (.of k))
    (μ : W ⟶ X) :
    pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) ⟶
      pullback sX (projectiveLine k ↘ Spec (.of k)) :=
  pullback.map (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) sX (projectiveLine k ↘ Spec (.of k))
    μ (𝟙 _) (𝟙 _) (by simp) (by simp)

variable {k : Type u} [Field k] [PerfectField k] {X W : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsIntegral W] (μ : W ⟶ X) [IsDominant μ]
  [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsIntegral (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (prodMap sX μ)]
  [IsIntegral (projectiveLine k)] [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.snd (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]

/-- The square `W × ℙ¹ ⟶ X × ℙ¹ ⟶ X` of `μ × id`. -/
private theorem map_comp_fst_eq :
    prodMap sX μ ≫ pullback.fst sX (projectiveLine k ↘ Spec (.of k)) =
      pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) ≫ μ := by
  simp

/-- **Product forms are compatible with `μ × id`**: `(μ × id)^*(dz ∧ pr^*ω) = dz ∧ pr^*(μ^*ω)`. -/
private theorem pullbackRationalPluriForms_prodForm
    [LocallyOfFiniteType (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)]
    (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j]
    (hμ' : Function.Bijective (functionFieldMap (prodMap sX μ)))
    {n : ℕ}
    (hd : letI := functionFieldAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    pullbackRationalPluriForms (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)
        (prodMap sX μ)
            (prodForm sX (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) rfl j n ω) =
      prodForm (μ ≫ sX) (prodMap sX μ ≫ pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)
        (by rw [← Category.assoc, map_comp_fst_eq, Category.assoc]) j n
        (letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (μ ≫ sX);
          letI := functionFieldMapAlgebra μ; haveI := isScalarTower_functionFieldMap sX μ;
          topFormsMap k X.functionField W.functionField n ω) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra ((pullback.fst sX (projectiveLine k ↘ Spec (.of k))) ≫ sX)
  let := functionFieldMapAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))
  have := isScalarTower_functionFieldMap sX (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))
  let := functionFieldAlgebra
      ((prodMap sX μ) ≫ (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) ≫ sX)
  let := functionFieldMapAlgebra (prodMap sX μ)
  have := isScalarTower_functionFieldMap
      ((pullback.fst sX (projectiveLine k ↘ Spec (.of k))) ≫ sX) (prodMap sX μ)
  let := functionFieldAlgebra (μ ≫ sX)
  let := functionFieldMapAlgebra μ
  have := isScalarTower_functionFieldMap sX μ
  let := functionFieldMapAlgebra (pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))
  have hsq : (prodMap sX μ) ≫ (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) =
      (pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))) ≫ μ := map_comp_fst_eq sX μ
  have hs : (prodMap sX μ) ≫ (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) ≫ sX =
      (pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))) ≫ μ ≫ sX := by
    rw [← Category.assoc, hsq, Category.assoc]
  have := isScalarTower_functionFieldMap_fst (μ ≫ sX)
      ((prodMap sX μ) ≫ (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) ≫ sX) hs
  haveI : IsDominant ((prodMap sX μ) ≫ (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))) := by
    rw [hsq]; infer_instance
  let : Algebra X.functionField
      (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField :=
      (functionFieldMap
        ((prodMap sX μ) ≫ (pullback.fst sX (projectiveLine k ↘ Spec (.of k))))).toAlgebra
  have t1 : IsScalarTower X.functionField
      (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField
      (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply (prodMap sX μ)
          (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) a).symm
  have t2 : IsScalarTower X.functionField W.functionField
      (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change functionFieldMap
          ((prodMap sX μ) ≫ (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))) a =
          functionFieldMap (pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))
            (functionFieldMap μ a)
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hsq]
  have t3 : IsScalarTower k X.functionField
      (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k
          (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField
          (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField,
        IsScalarTower.algebraMap_apply k X.functionField
            (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField]
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply (prodMap sX μ)
          (pullback.fst sX (projectiveLine k ↘ Spec (.of k))) _)
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective
      ((pullback.fst sX (projectiveLine k ↘ Spec (.of k))) ≫ sX) (prodMap sX μ) hμ' hd
  change pullbackForms (K := (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField)
      (K' := (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField) 1
    (prodForm sX _ rfl j n ω) = _
  simp only [prodForm]
  rw [pullbackForms_tprod hω₀]
  congr 1
  have hz : algebraMap (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField
      (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField (chartFun sX j) =
      chartFun (μ ≫ sX) j := by
    change functionFieldMap (prodMap sX μ) (functionFieldMap _ (chartRat j)) =
        functionFieldMap _ (chartRat j)
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    exact congrFun
        (congrArg DFunLike.coe (MMP.Positivity.DivisorOver.functionFieldMap_congr (by simp))) _
  have e1 := topFormsMap_wedgeLeft_D (k := k)
    (A := (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField)
    (B := (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField) n (chartFun sX j)
    (topFormsMap k X.functionField _ n ω)
  have e2 := topFormsMap_topFormsMap (k := k) (A := X.functionField)
    (B := (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField)
    (C := (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField) n ω
  have e3 := topFormsMap_topFormsMap (k := k) (A := X.functionField) (B := W.functionField)
    (C := (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField) n ω
  exact e1.trans ((congrArg (fun z => wedgeLeft
      (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField n
      (KaehlerDifferential.D k _ z)
      (topFormsMap k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField
        (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField n
        (topFormsMap k X.functionField _ n ω))) hz).trans
    (congrArg (wedgeLeft (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField n
      (KaehlerDifferential.D k _ (chartFun (μ ≫ sX) j))) (e2.trans e3.symm)))

end Functoriality

section LocalEquations

open ExteriorForms

/-- On an integral scheme every nonzero rational function is the value at the generic point of a
unit of the ring of rational functions. -/
private theorem exists_units_evalFF_eq {Z : Scheme.{u}} [IsIntegral Z] {g : Z.functionField}
    (hg : g ≠ 0) :
    ∃ φ : (RationalFunctions Z)ˣ, ∀ C : irreducibleComponents Z,
      MMP.Threefold.Mori.Helpers.evalFF C (φ : RationalFunctions Z) = g := by
  have hmem : ∀ C : irreducibleComponents Z, genericPoint Z ∈ C.1 := fun C =>
    C.2.2 (IrreducibleSpace.isIrreducible_univ Z) (Set.subset_univ _) trivial
  let j : ∀ C : irreducibleComponents Z,
      Z.functionField →+* Z.presheaf.stalk (componentGenericPoint Z C) := fun C =>
    (Z.presheaf.stalkSpecializes
      ((isGenericPoint_componentGenericPoint Z C).specializes (hmem C))).hom
  refine ⟨Units.map (RingHom.pi j).toMonoidHom (Units.mk0 g hg), fun C => ?_⟩
  change (Z.presheaf.stalkSpecializes _ ≫ Z.presheaf.stalkSpecializes _).hom g = g
  rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- `v^{⊗1} ≠ 0` for `v ≠ 0`. -/
private theorem tprodOne_ne_zero {K L : Type*} [Field K] [AddCommGroup L] [Module K L] {v : L}
    (hv : v ≠ 0) : tprodOne (K := K) v ≠ 0 := by
  intro h
  apply hv
  have h' : (PiTensorProduct.tprod K fun _ : Fin 1 => v) = 0 := h
  have := congrArg (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => L)
    (0 : Fin 1)) h'
  rwa [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at this

variable {k : Type u} [Field k]

/-- The generic point of `ℙ¹` lies in every chart. -/
private theorem genericPoint_mem_opensRange [IsIntegral (projectiveLine k)]
    (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j] :
    genericPoint (projectiveLine k) ∈ j.opensRange :=
  ((genericPoint_spec (projectiveLine k)).mem_open_set_iff j.opensRange.2).mpr
    ⟨j (Nonempty.some inferInstance), trivial, ⟨_, rfl⟩⟩

variable [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsLocallyNoetherian (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
  (s : pullback sX (projectiveLine k ↘ Spec (.of k)) ⟶ Spec (.of k))
  (hs : s = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) [LocallyOfFiniteType s]
  [LocallyOfFiniteType sX]

include hs in
/-- **The product form is nonzero** for a nonzero top form `ω`. -/
private theorem prodForm_ne_zero (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] {n : ℕ}
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (hd : letI := functionFieldAlgebra s
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k])
    (hω : ω ≠ 0) : prodForm sX s hs j n ω ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, y = genericPoint X := ⟨_, rfl⟩
  let := stalkAlgebra sX y
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX y
  obtain ⟨e, σ, he, hσ, h0⟩ := exists_generator_genericPoint sX hdX y hy
  have hω' := eq_smul_topFormsMap_of_span_eq_top sX _ hσ h0 ω
  obtain ⟨c, hc⟩ : ∃ c, c = (topFormsBasis (X.presheaf.stalk y) hσ h0).repr ω () :=
    ⟨_, rfl⟩
  rw [← hc] at hω'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hω (hω'.trans (zero_smul _ _))
  obtain ⟨x, hx'⟩ : ∃ x : (pullback sX (projectiveLine k ↘ Spec (.of k)) : Scheme.{u}),
      x = genericPoint _ := ⟨_, rfl⟩
  have hx : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) x ∈ j.opensRange := by
    rw [hx', map_genericPoint_of_isDominant]
    exact genericPoint_mem_opensRange j
  have hyx : pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x = y := by
    rw [hx', hy]
    exact map_genericPoint_of_isDominant _
  obtain ⟨σ', hσ', hprod⟩ := exists_generator_prodForm sX s hs j hjs x hx y hyx he hσ
  rw [hω', hprod c]
  refine tprodOne_ne_zero (smul_ne_zero ((map_ne_zero _).mpr hc0) ?_)
  let := stalkAlgebra s x
  let := functionFieldAlgebra s
  have := isScalarTower_stalk_functionField s x
  obtain ⟨-, σ'', -, -, h0''⟩ := exists_generator_genericPoint s hd x hx'
  have hmem : σ'' ∈ Submodule.span _ {σ'} := hσ' ▸ Submodule.mem_top
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  intro h
  apply h0''
  rw [LinearMap.map_smul_of_tower, h, smul_zero]

include hs in
/-- **Local equations of the canonical divisor of `X × ℙ¹`.** Let `K` be the divisor of the top
form `ω` on `X` and `K_P` the divisor of the product form `dz ∧ pr^*ω` on `X × ℙ¹`, for the
coordinate `z` of a chart `j`. If `φ` is a local equation of `mK` on `U`, then `pr^*φ` is a local
equation of `mK_P` on `pr⁻¹(U) ∩ q⁻¹(j)`. -/
private theorem isLocalEquation_prodForm (hX : IsNormalVariety k sX)
    (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))] {n : ℕ}
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (hd : letI := functionFieldAlgebra s
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k])
    {K : Divisor X} (hK : ∀ Γ, K.coeff Γ = Γ.ordForm (tprodForm sX ω))
    {KP : Divisor (pullback sX (projectiveLine k ↘ Spec (.of k)))}
    (hKP : ∀ G, KP.coeff G = G.ordForm (sX := s) (prodForm sX s hs j n ω)) (m : ℤ)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : (m • K).IsLocalEquation U φ)
    {φ' : (RationalFunctions (pullback sX (projectiveLine k ↘ Spec (.of k))))ˣ}
    (hφ' : ∀ C C', MMP.Threefold.Mori.Helpers.evalFF C (φ' : RationalFunctions _) =
      functionFieldMap (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))
        (MMP.Threefold.Mori.Helpers.evalFF C' (φ : RationalFunctions X))) :
    (m • KP).IsLocalEquation (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ U ⊓
      pullback.snd sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ j.opensRange) φ' := by
  intro G ⟨x, hxG, hxU⟩
  obtain ⟨ι, hι, -, hhor, hgen⟩ := exists_preimagePrimeDivisor sX hX
  rw [DivisorWithCoeffs.coeff_smul, hKP, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  by_cases hG : G ∈ Set.range ι
  · obtain ⟨Γ, rfl⟩ := hG
    have hΓU : (Γ.support ∩ U).Nonempty :=
      ⟨_, (hι Γ ▸ hxG : x ∈ pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹' Γ.support),
        hxU.1⟩
    have h1 := hφ Γ hΓU
    rw [DivisorWithCoeffs.coeff_smul, hK, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h1
    have hc : MMP.Threefold.Mori.Helpers.evalFF Γ.component (φ : RationalFunctions X) ≠ 0 :=
      (φ.isUnit.map _).ne_zero
    rw [ordForm_prodForm_of_support_eq sX s hs hX j hjs hdX hd Γ (ι Γ) (hι Γ) ω,
      hφ' _ Γ.component, ord_functionFieldMap_fst_of_genericPoint_eq sX (ι Γ) Γ (hgen Γ) hc]
    exact h1
  · have h0 := hhor G hG
    have hGj : pullback.snd sX (projectiveLine k ↘ Spec (.of k)) G.genericPoint ∈ j.opensRange :=
      (G.genericPoint_mem_iff (pullback.snd sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ
        j.opensRange)).mpr ⟨x, hxG, hxU.2⟩
    obtain ⟨C'⟩ : Nonempty (irreducibleComponents X) := ⟨pointComponent (genericPoint X)⟩
    have hc : MMP.Threefold.Mori.Helpers.evalFF C' (φ : RationalFunctions X) ≠ 0 :=
      (φ.isUnit.map _).ne_zero
    rw [ordForm_prodForm_of_genericPoint_eq sX s hs j hjs hdX hd G h0 hGj ω, hφ' _ C',
      ord_functionFieldMap_fst_of_genericPoint_eq_genericPoint sX G h0 hc, smul_zero]

end LocalEquations

section ProductCanonical

open ExteriorForms

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsLocallyNoetherian (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
  (s : pullback sX (projectiveLine k ↘ Spec (.of k)) ⟶ Spec (.of k))
  (hs : s = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) [LocallyOfFiniteType s]
  [LocallyOfFiniteType sX]
  [CompactSpace (pullback sX (projectiveLine k ↘ Spec (.of k)) : Scheme.{u})]

include hs in
/-- **`mK_{X × ℙ¹}` is Cartier when `mK_X` is**, for the canonical divisors cut out by a top form
`ω` on `X` and the product form `dz ∧ pr^*ω`. -/
private theorem isCartier_zsmul_divisorOfForm_prodForm (hX : IsNormalVariety k sX)
    (hP : IsNormalVariety k s) {K₀ : Divisor (pullback sX (projectiveLine k ↘ Spec (.of k)))}
    {n : ℕ} (hK₀ : K₀.IsCanonicalDivisor s (n + 1))
    (j₀ : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j₀]
    (hjs₀ : j₀ ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    [IsIntegral (projectiveLine k)]
    [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))]
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (hd : letI := functionFieldAlgebra s
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k])
    (hω : ω ≠ 0) {K : Divisor X} (hK : ∀ Γ, K.coeff Γ = Γ.ordForm (tprodForm sX ω)) (m : ℤ)
    (hKc : (m • K).IsCartier) :
    (m • divisorOfForm (prodForm sX s hs j₀ n ω)).IsCartier := by
  haveI := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  intro x
  obtain ⟨j, _, hjs, hxj⟩ :=
    exists_projectiveLine_chart (k := k) (pullback.snd sX (projectiveLine k ↘ Spec (.of k)) x)
  obtain ⟨U, hU, φ, hφ⟩ := hKc (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) x)
  obtain ⟨C₀⟩ : Nonempty (irreducibleComponents X) := ⟨pointComponent (genericPoint X)⟩
  have hc : MMP.Threefold.Mori.Helpers.evalFF C₀ (φ : RationalFunctions X) ≠ 0 :=
    (φ.isUnit.map _).ne_zero
  obtain ⟨φ', hφ'⟩ := exists_units_evalFF_eq ((map_ne_zero
    (functionFieldMap (pullback.fst sX (projectiveLine k ↘ Spec (.of k))))).mpr hc)
  have hloc := isLocalEquation_prodForm sX s hs hX j hjs hdX hd ω hK
    (KP := divisorOfForm (prodForm sX s hs j n ω)) (fun G => coeff_divisorOfForm _ G) m hφ
    (φ' := φ') (fun C C' => by rw [hφ' C, Subsingleton.elim C' C₀])
  have h₁ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hP hK₀
    (prodForm_ne_zero sX s hs j₀ hjs₀ hdX hd ω hω)
  have h₂ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hP hK₀
    (prodForm_ne_zero sX s hs j hjs hdX hd ω hω)
  obtain ⟨ψ, hψ⟩ := h₁.trans h₂.symm
  have heq : m • divisorOfForm (prodForm sX s hs j₀ n ω) =
      m • divisorOfForm (prodForm sX s hs j n ω) + m • principalDivisor ψ := by
    rw [← smul_add, ← hψ, add_sub_cancel]
  refine ⟨pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ U ⊓
    pullback.snd sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ j.opensRange, ⟨hU, hxj⟩,
    φ' * ψ ^ m, ?_⟩
  rw [heq]
  exact hloc.add ((Divisor.isLocalEquation_principalDivisor ψ _).zsmul m)

end ProductCanonical

section ProductModel

open ExteriorForms

variable {k : Type u} [Field k] [PerfectField k] {X W : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (μ : W ⟶ X) [IsDominant μ]
  [IsIntegral (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsLocallyNoetherian (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback sX (projectiveLine k ↘ Spec (.of k)))]
  [IsIntegral (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]
  [IsLocallyNoetherian (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]
  [IsNormal (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (prodMap sX μ)]
  [IsIntegral (projectiveLine k)] [IsDominant (pullback.snd sX (projectiveLine k ↘ Spec (.of k)))]
  [IsDominant (pullback.snd (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))]

/-- **Pull-back of a `1`-canonical form** along a birational `μ`: `μ^*(ω^{⊗1}) = (μ^*ω)^{⊗1}`. -/
private theorem pullbackRationalPluriForms_tprodForm [LocallyOfFiniteType sX]
    (hμ : Function.Bijective (functionFieldMap μ)) {n : ℕ}
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    pullbackRationalPluriForms sX μ (tprodForm sX ω) =
      tprodForm (μ ≫ sX) (letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (μ ≫ sX);
          letI := functionFieldMapAlgebra μ; haveI := isScalarTower_functionFieldMap sX μ;
          topFormsMap k X.functionField W.functionField n ω) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (μ ≫ sX)
  let := functionFieldMapAlgebra μ
  have := isScalarTower_functionFieldMap sX μ
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX μ hμ hdX
  change pullbackForms (K := X.functionField) (K' := W.functionField) 1 (tprodForm sX ω) = _
  exact pullbackForms_tprod hω₀ ω

/-- **The order of a pulled-back product form along `E × ℙ¹`**: for `F = pr⁻¹(E)` on `W × ℙ¹`,
`ord_F((μ × id)^*(dz ∧ pr^*ω)) = ord_E(μ^*ω)`. -/
private theorem ordForm_pullback_prodForm [LocallyOfFiniteType sX]
    [LocallyOfFiniteType (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)]
    (hW : IsNormalVariety k (μ ≫ sX))
    (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    (hμ : Function.Bijective (functionFieldMap μ))
    (hμ' : Function.Bijective (functionFieldMap (prodMap sX μ))) {n : ℕ}
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (hd : letI := functionFieldAlgebra (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (hdW : letI := functionFieldAlgebra (μ ≫ sX); (Algebra.trdeg k W.functionField).toNat = n)
    (s' : pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) ⟶ Spec (.of k))
    (hs' : s' = prodMap sX μ ≫ pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)
    (hdW' : letI := functionFieldAlgebra s'
      (Algebra.trdeg k (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k])
    (E : MMP.Mori.PrimeDivisor W)
    (F : MMP.Mori.PrimeDivisor (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))))
    (hFE : F.support = pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) ⁻¹' E.support) :
    F.ordForm (pullbackRationalPluriForms (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX)
        (prodMap sX μ) (prodForm sX (pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) rfl
          j n ω)) =
      E.ordForm (pullbackRationalPluriForms sX μ (tprodForm sX ω)) := by
  subst hs'
  have hs' : prodMap sX μ ≫ pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX =
      pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) ≫ μ ≫ sX := by
    rw [← Category.assoc, map_comp_fst_eq, Category.assoc]
  haveI : LocallyOfFiniteType (μ ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType
      (prodMap sX μ ≫ pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) := by
    rw [hs']; infer_instance
  rw [pullbackRationalPluriForms_prodForm sX μ j hμ' hd ω,
    ordForm_prodForm_of_support_eq (μ ≫ sX) _ hs' hW j hjs hdW hdW' E F hFE,
    pullbackRationalPluriForms_tprodForm sX μ hμ hdX ω]

/-- **Coefficients of pulled-back canonical divisors along `E × ℙ¹`.** With `K` and `K_P` the
divisors of `ω` and of the product form `dz ∧ pr^*ω`, the coefficient of `(μ × id)^*(mK_P)` along
a prime divisor `F` of `W × ℙ¹` over `E` and over the chart `j` is that of `μ^*(mK)` along
`E`. -/
private theorem coeff_isPullback_prodMap (hX : IsNormalVariety k sX)
    (s : pullback sX (projectiveLine k ↘ Spec (.of k)) ⟶ Spec (.of k))
    (hs : s = pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ≫ sX) [LocallyOfFiniteType s]
    [LocallyOfFiniteType sX]
    (j : Spec (.of (Polynomial k)) ⟶ projectiveLine k) [IsOpenImmersion j]
    (hjs : j ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) {n : ℕ}
    (hdX : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (hd : letI := functionFieldAlgebra s
      (Algebra.trdeg k (pullback sX (projectiveLine k ↘ Spec (.of k))).functionField).toNat =
        n + 1)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k])
    {K : Divisor X} (hK : ∀ Γ, K.coeff Γ = Γ.ordForm (tprodForm sX ω))
    {KP : Divisor (pullback sX (projectiveLine k ↘ Spec (.of k)))}
    (hKP : ∀ G, KP.coeff G = G.ordForm (sX := s) (prodForm sX s hs j n ω)) (m : ℤ)
    (hKc : (m • K).IsCartier) {CW : Divisor W}
    {hCW0 : ∀ Z : irreducibleComponents W, μ (componentGenericPoint W Z) ∉ (m • K).supp}
    (hCW : (m • K).IsPullback μ hCW0 CW)
    {CP : Divisor (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)))}
    {hCP0 : ∀ Z : irreducibleComponents
        (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) : Scheme.{u}),
      prodMap sX μ (componentGenericPoint _ Z) ∉ (m • KP).supp}
    (hCP : (m • KP).IsPullback (prodMap sX μ) hCP0 CP) (E : MMP.Mori.PrimeDivisor W)
    (F : MMP.Mori.PrimeDivisor (pullback (μ ≫ sX) (projectiveLine k ↘ Spec (.of k))))
    (hEF : E.genericPoint =
      pullback.fst (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) F.genericPoint)
    (hFj : pullback.snd (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) F.genericPoint ∈
      j.opensRange) :
    CP.coeff F = CW.coeff E := by
  haveI := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  obtain ⟨U, hU, φ, hφ⟩ := hKc (μ E.genericPoint)
  obtain ⟨C₀⟩ : Nonempty (irreducibleComponents X) := ⟨pointComponent (genericPoint X)⟩
  obtain ⟨C₁⟩ : Nonempty (irreducibleComponents
      (pullback sX (projectiveLine k ↘ Spec (.of k)) : Scheme.{u})) :=
    ⟨pointComponent (genericPoint _)⟩
  have hc : MMP.Threefold.Mori.Helpers.evalFF C₀ (φ : RationalFunctions X) ≠ 0 :=
    (φ.isUnit.map _).ne_zero
  obtain ⟨φ', hφ'⟩ := exists_units_evalFF_eq ((map_ne_zero
    (functionFieldMap (pullback.fst sX (projectiveLine k ↘ Spec (.of k))))).mpr hc)
  have hloc := isLocalEquation_prodForm sX s hs hX j hjs hdX hd ω hK hKP m hφ
    (φ' := φ') (fun C C' => by rw [hφ' C, Subsingleton.elim C' C₀])
  have hsq := map_comp_fst_eq sX μ
  have hsnd : prodMap sX μ ≫ pullback.snd sX (projectiveLine k ↘ Spec (.of k)) =
      pullback.snd (μ ≫ sX) (projectiveLine k ↘ Spec (.of k)) := by simp [prodMap]
  have hmem : prodMap sX μ F.genericPoint ∈
      pullback.fst sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ U ⊓
        pullback.snd sX (projectiveLine k ↘ Spec (.of k)) ⁻¹ᵁ j.opensRange := by
    refine ⟨?_, ?_⟩
    · change pullback.fst sX (projectiveLine k ↘ Spec (.of k)) (prodMap sX μ F.genericPoint) ∈ U
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, ← hEF]
      exact hU
    · change pullback.snd sX (projectiveLine k ↘ Spec (.of k)) (prodMap sX μ F.genericPoint) ∈
        j.opensRange
      rw [← Scheme.Hom.comp_apply, hsnd]
      exact hFj
  haveI : IsDominant (prodMap sX μ ≫ pullback.fst sX (projectiveLine k ↘ Spec (.of k))) := by
    rw [hsq]; infer_instance
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCP hloc F hmem C₁, hφ' C₁,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr hsq,
    ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    ord_functionFieldMap_fst_of_genericPoint_eq (μ ≫ sX) F E hEF ((map_ne_zero _).mpr hc),
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCW hφ E hU C₀]

end ProductModel

end ProductLine

end ProductForms

open MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Generalities on log discrepancies -/

section General

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor `(Y, f, E)` over a separated normal scheme `X` is exceptional if and only if
`f(η_E)` has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight [IsSeparated (X ↘ ⊤_ Scheme)]
    (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hc : ((TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) :
      TopologicalSpace.Closeds X) : Set X) = closure {D.f D.E.genericPoint} :=
    D.center_eq_closure_genericPoint
  rw [hc]
  exact ⟨fun h => h _ (subset_closure rfl),
    fun h x hx => h.trans (Order.coheight_anti (specializes_iff_mem_closure.mpr hx))⟩

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {s : X ⟶ Spec (.of k)} (hs : IsSeparated s) :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Over a variety, being exceptional depends only on the valuation. -/
private theorem isExceptional_iff_of_valuation_eq (hX : IsNormalVariety k sX)
    {D D' : DivisorOver k sX} (hv : D.valuation = D'.valuation) :
    D.IsExceptional ↔ D'.IsExceptional := by
  haveI := isSeparated_toTerminal (hX.1.toIsSeparated)
  rw [isExceptional_iff_two_le_coheight, isExceptional_iff_two_le_coheight,
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv]

variable [PerfectField k]

/-- **Divisors that are not exceptional have log discrepancy one** over a pair `(X, 0)`: such a
divisor has the valuation of a prime divisor `P` of `X`, whose discrepancy is `-coeff_P 0 = 0`. -/
private theorem eq_one_of_not_isExceptional (hP : MMP.Mori.IsPair sX 0)
    {D : DivisorOver k sX} (hD : ¬ D.IsExceptional) {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n 0 D a) : a = 1 := by
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hP.1 D hD
  obtain ⟨-, n₀, K, hK, -⟩ := id hP
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (DivisorOver.ofPrimeDivisor k hP.1 P)
  have hc0 := MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hP.1 hc
  have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 X) from inferInstance)
  rw [map_zero] at h1
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha h1 hv, hc0]
  simp

end General

section Smooth

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A smooth variety `X` with canonical divisor of index `n` makes `(X, 0)` a pair. -/
private theorem isPair_zero_of_isSmoothScheme (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n) :
    ∃ K : Divisor X, K.IsCanonicalDivisor sX n ∧ MMP.Mori.IsPair sX 0 := by
  haveI := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  refine ⟨K, hK, hX, n, K, hK, ?_⟩
  rw [add_zero]
  exact MMP.Mori.QDivisor.isQCartier_toQDivisor (MMP.Fourfold.isCartier_of_isSmoothScheme hsm K)

/-- **Log discrepancies over a smooth variety.** If `X` is smooth, every log discrepancy of
`(X, 0)` is at least one, and at least two for an exceptional divisor over `X`. -/
private theorem one_le_logDiscrepancy_of_isSmoothScheme (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {D : DivisorOver k sX} {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n 0 D a) : 1 ≤ a ∧ (D.IsExceptional → 2 ≤ a) := by
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  obtain ⟨K, hK, hP⟩ := isPair_zero_of_isSmoothScheme hX hsm hn
  by_cases hD : D.IsExceptional
  · obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
    have ha' : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor 0) D a := by
      rwa [map_zero]
    have hac := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha'
    haveI := isSeparated_toTerminal (hX.1.toIsSeparated)
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    have h2n : 2 ≤ n := by
      have h2 := (isExceptional_iff_two_le_coheight D).mp hD
      have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
        (D.f D.E.genericPoint)
      rw [hn] at h
      have h0 : (0 : WithBot ℕ∞) ≤
          topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) := by
        have : Nonempty (TopologicalSpace.IrreducibleCloseds
            (closure {D.f D.E.genericPoint} : Set X)) :=
          ⟨TopologicalSpace.IrreducibleCloseds.closureSingleton ⟨_, subset_closure rfl⟩⟩
        exact Order.krullDim_nonneg
      have h2' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
        rw [← h]
        calc ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) :=
              WithBot.coe_le_coe.mpr h2
          _ ≤ _ := le_add_of_nonneg_left h0
      exact_mod_cast h2'
    haveI : LocallyOfFinitePresentation sX :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
    have hdisc := MMP.Mori.discrep_eq_of_isSNC sX hX hsm h2n hK (Δ := 0) ∅ (by simp)
      (by simpa using MMP.Mori.DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sX hsm) (by simp)
    have hle := MMP.Mori.discrep_le hD hc
    simp only [Finset.notMem_empty, iInf_false, iInf_top, top_inf_eq] at hdisc
    rw [hdisc] at hle
    have h1c : (1 : ℝ) ≤ c := by exact_mod_cast EReal.coe_le_coe_iff.mp hle
    exact ⟨by linarith, fun _ => by linarith⟩
  · have := eq_one_of_not_isExceptional hP hD ha
    exact ⟨this.ge, fun h => absurd h hD⟩

end Smooth

/-! ### Reading terminality on a smooth model -/

section Model

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The valuation of `(Y, g ∘ μ, E)` over `X` is that of `(Y, g, E)` over `W`, restricted along
`μ^* : k(X) → k(W)`. -/
private theorem valuation_mk_comp {W : Scheme.{u}} [IsIntegral W] (μ : W ⟶ X) [IsDominant μ]
    (D : DivisorOver k (μ ≫ sX)) (h₁ : IsNormalVariety k ((D.f ≫ μ) ≫ sX))
    (h₂ : IsBirationalMorphism (D.f ≫ μ)) :
    (⟨D.Y, D.f ≫ μ, h₁, h₂, D.E⟩ : DivisorOver k sX).valuation =
      D.valuation.comap (functionFieldMap μ) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : IsDominant (D.f ≫ μ) := h₂.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ μ) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap μ t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The valuation of a prime divisor `F` of `W` over `W`, restricted along `μ^*`, is the
valuation of `(W, μ, F)` over `X`. -/
private theorem valuation_ofPrimeDivisor_comap {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (μ : W ⟶ X) (hW : IsNormalVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (F : MMP.Mori.PrimeDivisor W) :
    haveI : IsDominant μ := hμ.isDominant
    (DivisorOver.ofPrimeDivisor k hW F).valuation.comap (functionFieldMap μ) =
      (⟨W, μ, hW, hμ, F⟩ : DivisorOver k sX).valuation := by
  haveI : IsDominant μ := hμ.isDominant
  ext t
  change F.divisorialValuation (functionFieldMap (𝟙 W) (functionFieldMap μ t)) =
    F.divisorialValuation (functionFieldMap μ t)
  rw [MMP.Mori.functionFieldMap_id_apply]

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {Y Z : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Z] [IsNormal Z] {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X}
    {L' : Divisor Y} {L'' : Divisor Z}
    {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  have mem_irr : ∀ (W : irreducibleComponents X) (t : X), t ∈ W.1 := fun W t => by
    rw [W.2.eq_of_le (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)]
    trivial
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irr
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
      (mem_irr (pointComponent ((g ≫ f) z)) _)
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

variable [PerfectField k]

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero [LocallyOfFiniteType sX] {Y : Scheme.{u}}
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f))
    {d : ℕ} (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
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

/-- **The divisor of a nonzero top form on a smooth variety is canonical.** -/
private theorem isCanonicalDivisor_divisorOfForm_of_isSmoothScheme [CompactSpace X]
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) [LocallyOfFiniteType sX]
    {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    (divisorOfForm τ).IsCanonicalDivisor sX n := by
  haveI := hX.1
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  exact hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ

/-- **Adding an effective `ℝ`-divisor on a smooth variety does not increase a log
discrepancy.** -/
private theorem exists_isLogDiscrepancy_add_le_of_nonneg (hsm : IsSmoothScheme sX) {n : ℕ}
    {D : DivisorOver k sX} (Δ : RDivisor X) (hΔ : ∀ P, 0 ≤ Δ.coeff P) {B : RDivisor X} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ a' : ℝ, a' ≤ a ∧ MMP.Intersection.IsLogDiscrepancy sX n (B + Δ) D a' := by
  classical
  suffices H : ∀ Δ : MMP.Mori.PrimeDivisor X →₀ ℝ, (∀ P, 0 ≤ Δ P) → ∀ (B : RDivisor X) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n B D a → ∃ a' : ℝ, a' ≤ a ∧
        MMP.Intersection.IsLogDiscrepancy sX n (B + (show RDivisor X from Δ)) D a' from
    H Δ hΔ B a h
  intro Δ
  refine Finsupp.induction Δ ?_ ?_
  · intro _ B a h
    exact ⟨a, le_rfl, by simpa using h⟩
  · intro P c f hP hc ih hnn B a h
    have hc0 : 0 ≤ c := by
      have := hnn P
      rwa [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hP,
        add_zero] at this
    have hf0 : ∀ Q, 0 ≤ f Q := fun Q => by
      have := hnn Q
      by_cases hQ : P = Q
      · subst hQ; rw [Finsupp.notMem_support_iff.mp hP]
      · simpa [Finsupp.single_apply, hQ] using this
    obtain ⟨a₁, ha₁, h₁⟩ := MMP.Fourfold.exists_isLogDiscrepancy_add_single_le hsm h P hc0
    obtain ⟨a₂, ha₂, h₂⟩ := ih hf0 _ a₁ h₁
    refine ⟨a₂, ha₂.trans ha₁, ?_⟩
    have : (B + (show RDivisor X from Finsupp.single P c + f)) =
        B + Finsupp.single P c + (show RDivisor X from f) := by
      rw [add_assoc]
    rw [this]
    exact h₂

/-- **Terminality is read on a smooth model.** Let `(X, 0)` be a pair and `μ : W ⟶ X` a proper
birational morphism from a smooth variety such that every prime divisor `F` of `W` has
`a(F; X, 0) ≥ 1`, with strict inequality when `F` is exceptional over `X`. Then every divisor
over `X` has log discrepancy `≥ 1`, and `> 1` when it is exceptional over `X`.

The valuation of a divisor over `X` is carried by a prime divisor of a smooth model `W''` over
`W`. Writing `K_W + Δ_W = μ^*K_X` with the canonical divisors cut out by one rational top form,
`-Δ_W` is effective by hypothesis and the log discrepancy over `(X, 0)` is the one over
`(W, Δ_W)`; it is at least the log discrepancy over `(W, 0)`, which is `≥ 1`, and `≥ 2` unless
the valuation is that of a prime divisor `F` of `W`. -/
private theorem logDiscrepancy_bounds_of_smoothModel [CharZero k] (hP : MMP.Mori.IsPair sX 0)
    {W : Scheme.{u}} (μ : W ⟶ X) [IsProper μ] (hW : IsNormalVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (hsm : IsSmoothScheme (μ ≫ sX))
    (hF : ∀ (F : MMP.Mori.PrimeDivisor W) (n : ℕ) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n 0 ⟨W, μ, hW, hμ, F⟩ a →
        1 ≤ a ∧ ((⟨W, μ, hW, hμ, F⟩ : DivisorOver k sX).IsExceptional → 1 < a))
    (D : DivisorOver k sX) {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n 0 D a) :
    1 ≤ a ∧ (D.IsExceptional → 1 < a) := by
  classical
  have hX := hP.1
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (μ ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  haveI : IsDominant μ := hμ.isDominant
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k (μ ≫ sX) := hW.1
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hnW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (μ ≫ sX) hμ).symm.trans hn
  -- the valuation of `D` has a centre on `X`
  have hDp : IsProper D.f := ha.2.1
  have hv : MMP.Flips.HasNonemptyCenter k sX D.valuation := by
    haveI := D.isIntegral
    haveI := D.isNormal
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    refine ⟨⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E,
      functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective, ?_⟩,
      ⟨D, hDp⟩, rfl⟩
    rfl
  -- a smooth model `W''` over `W` carrying the valuation of `D`
  obtain ⟨W'', w, hW'', hwb, g, hsm'', -, hg, hE, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sX
      (ι := Unit) (fun _ => μ) (fun _ => hμ) (fun _ => hW) (κ := Unit) (fun _ => D.valuation)
      (fun _ => hv)
  obtain ⟨hgμ, hgp, hgb⟩ := hg ()
  obtain ⟨E'', hE''⟩ := hE ()
  subst hgμ
  haveI : IsIntegral W'' := hW''.1.toIsIntegral
  haveI : IsNormal W'' := hW''.2
  haveI : AlgebraicGeometry.IsVariety k ((g () ≫ μ) ≫ sX) := hW''.1
  haveI : LocallyOfFiniteType ((g () ≫ μ) ≫ sX) := hW''.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W'' := LocallyOfFiniteType.isLocallyNoetherian ((g () ≫ μ) ≫ sX)
  haveI : CompactSpace W'' := QuasiCompact.compactSpace_of_compactSpace ((g () ≫ μ) ≫ sX)
  haveI : IsDominant (g ()) := hgb.isDominant
  haveI : IsProper (g ()) := isProper_of_isProjectiveMorphism (g ()) hgp
  haveI : IsDominant (g () ≫ μ) := hwb.isDominant
  have hW''' : IsNormalVariety k (g () ≫ μ ≫ sX) := by simpa using hW''
  -- the data of the log discrepancy of `D`
  obtain ⟨-, -, ω, hω0, ⟨K, hK, hKω⟩, m, r, C, C', hCc, hrel, hpb, ha_eq⟩ := id ha
  choose CW hCW using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant μ (hCc i)
  have hCWc : ∀ i, (CW i).IsCartier := fun i => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  choose C'' hC'' using fun i =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant (g ()) (hCWc i)
  set ωW := pullbackRationalPluriForms sX μ ω with hωW
  have hωW0 : ωW ≠ 0 := pullbackRationalPluriForms_ne_zero μ hμ.functionFieldMap_bijective hd hω0
  -- the log discrepancy of the model of `D` on `W''`
  set D'' : DivisorOver k sX := ⟨W'', g () ≫ μ, hW'', hwb, E''⟩ with hD''
  set a'' : ℝ := 1 + (D''.ordPullback ω : ℝ) - ∑ i, r i * (C'' i).coeff E'' with ha''
  have h'' : MMP.Intersection.IsLogDiscrepancy sX n 0 D'' a'' :=
    ⟨hX, inferInstanceAs (IsProper (g () ≫ μ)), ω, hω0, ⟨K, hK, hKω⟩, m, r, C, C'', hCc, hrel,
      fun i => ⟨_, isPullback_comp (hCW i) (hC'' i)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (g () ≫ μ) (C i))⟩, rfl⟩
  have haa : a = a'' := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha h''
    hE''.symm
  -- the same log discrepancy over `(W, Δ_W)`
  set DW : DivisorOver k (μ ≫ sX) := ⟨W'', g (), hW''', hgb, E''⟩ with hDW
  set ΔW : RDivisor W := ∑ i, r i • Divisor.toRDivisor (CW i) -
    Divisor.toRDivisor (divisorOfForm ωW) with hΔW
  have hΔWc : ∀ Γ, ΔW.coeff Γ = ∑ i, r i * ((CW i).coeff Γ : ℝ) - (Γ.ordForm ωW : ℝ) := by
    intro Γ
    rw [hΔW, DivisorWithCoeffs.coeff_sub]
    congr 1
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hKW := isCanonicalDivisor_divisorOfForm_of_isSmoothScheme hW hsm hnW hωW0
  have hWd : MMP.Intersection.IsLogDiscrepancy (μ ≫ sX) n ΔW DW a'' := by
    refine ⟨hW, inferInstanceAs (IsProper (g ())), ωW, hωW0, ⟨divisorOfForm ωW, hKW,
      fun Γ => rfl⟩, m, r, CW, C'', hCWc, fun Γ => by rw [hΔWc]; ring, fun i => ⟨_, hC'' i⟩, ?_⟩
    rw [ha'']
    congr 2
    change (E''.ordForm (pullbackRationalPluriForms sX (g () ≫ μ) ω) : ℝ) =
      E''.ordForm (pullbackRationalPluriForms (μ ≫ sX) (g ()) ωW)
    rw [hωW, MMP.Flips.pullbackRationalPluriForms_comp μ (g ()) hμ.functionFieldMap_bijective
      hgb.functionFieldMap_bijective hd ω]
    all_goals rfl
  -- the log discrepancies of the prime divisors of `W`
  have hFW : ∀ F : MMP.Mori.PrimeDivisor W, MMP.Intersection.IsLogDiscrepancy sX n 0
      ⟨W, μ, hW, hμ, F⟩ (1 + (F.ordForm ωW : ℝ) - ∑ i, r i * (CW i).coeff F) := fun F =>
    ⟨hX, inferInstance, ω, hω0, ⟨K, hK, hKω⟩, m, r, C, CW, hCc, hrel, fun i => ⟨_, hCW i⟩, rfl⟩
  have hΔneg : ∀ F, 0 ≤ (-ΔW).coeff F := by
    intro F
    have := (hF F n _ (hFW F)).1
    rw [DivisorWithCoeffs.coeff_neg, hΔWc]
    linarith
  obtain ⟨a₃, ha₃, h₃⟩ := exists_isLogDiscrepancy_add_le_of_nonneg hsm (-ΔW) hΔneg hWd
  rw [add_neg_cancel] at h₃
  obtain ⟨h₃1, h₃2⟩ := one_le_logDiscrepancy_of_isSmoothScheme hW hsm h₃
  refine ⟨by linarith, fun hDexc => ?_⟩
  by_cases hDW' : DW.IsExceptional
  · linarith [h₃2 hDW']
  obtain ⟨F, hvF⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hW DW hDW'
  have hval : D.valuation = (⟨W, μ, hW, hμ, F⟩ : DivisorOver k sX).valuation := by
    rw [← hE'', ← valuation_ofPrimeDivisor_comap μ hW hμ F, ← hvF]
    exact valuation_mk_comp μ DW hW'' hwb
  have haF := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha (hFW F) hval
  have hexc := (isExceptional_iff_of_valuation_eq hX hval).mp hDexc
  rw [haF]
  exact (hF F n _ (hFW F)).2 hexc

end Model

/-! ### The product with the projective line -/

section Product

open ProductLine MMP.Mori.CanonicalDivisorExistence

/-- `μ × id_L` is the base change of `μ` along the projection `Y × L ⟶ Y`. -/
private theorem isPullback_map_fst {k : Type u} [Field k] {Y L Y₁ : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (q : Y₁ ⟶ Y) :
    IsPullback (pullback.map (q ≫ sY) sL sY sL q (𝟙 L) (𝟙 _) (by simp) (by simp))
      (pullback.fst (q ≫ sY) sL) (pullback.fst sY sL) q := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback sY sL).flip
  simpa using (IsPullback.of_hasPullback (q ≫ sY) sL).flip

/-- A morphism of irreducible schemes which is an open immersion on a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_ι_comp {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (U : X.Opens)
    (hU : (U : Set X).Nonempty) [IsOpenImmersion (U.ι ≫ f)] : IsBirationalMorphism f := by
  have hle : U ≤ f ⁻¹ᵁ (U.ι ≫ f).opensRange := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hoi : IsOpenImmersion (f.resLE (U.ι ≫ f).opensRange U hle) := by
    have : IsOpenImmersion (f.resLE (U.ι ≫ f).opensRange U hle ≫ ((U.ι ≫ f).opensRange).ι) := by
      rw [Scheme.Hom.resLE_comp_ι]; infer_instance
    exact IsOpenImmersion.of_comp _ ((U.ι ≫ f).opensRange).ι
  have hsurj : Surjective (f.resLE (U.ι ≫ f).opensRange U hle) := by
    refine ⟨fun ⟨y, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext ?_⟩⟩
    erw [Scheme.Hom.coe_resLE_apply]
    exact hx
  obtain ⟨x, hx⟩ := hU
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U _ ⟨x, hx⟩ ⟨f x, hle hx⟩ hle
    ((isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hoi, hsurj⟩)

/-- Biregularity over `V` is inherited by a base change, over the preimage of `V`. -/
private theorem isBiregular_preimage_of_isPullback {P' P Y₁ Y : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) {V : Y.Opens}
    (hV : IsBiregular g V) : IsBiregular m (p ⁻¹ᵁ V) := by
  have hUY : m ⁻¹ᵁ (p ⁻¹ᵁ V) = m ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    refine (inf_eq_left.2 ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  have H' := Scheme.Hom.isPullback_resLE H (US := V) (UT := g ⁻¹ᵁ V) (UX := p ⁻¹ᵁ V)
    le_rfl le_rfl hUY
  have hg : IsIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rwa [Scheme.Hom.resLE_eq_morphismRestrict]
  have := MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) H'.flip hg
  unfold IsBiregular
  rwa [← Scheme.Hom.resLE_eq_morphismRestrict]

/-- A base change `m` of `g` is biregular at every point lying over the biregular locus of `g`. -/
private theorem map_mem_biregularLocus_of_isPullback {P' P Y₁ Y : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) {x : P'}
    (hx : g (p' x) ∈ biregularLocus g) : m x ∈ biregularLocus m := by
  apply le_biregularLocus (isBiregular_preimage_of_isPullback H (isBiregular_biregularLocus g))
  change p (m x) ∈ biregularLocus g
  rwa [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]

/-- An open immersion `W ⟶ Y` through `g` base changes to an open immersion. -/
private theorem isOpenImmersion_ι_comp_of_isPullback {P' P Y₁ Y : Scheme.{u}}
    {m : P' ⟶ P} {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g)
    (W : Y₁.Opens) [IsOpenImmersion (W.ι ≫ g)] : IsOpenImmersion ((p' ⁻¹ᵁ W).ι ≫ m) := by
  have hUY : p' ⁻¹ᵁ W = m ⁻¹ᵁ ⊤ ⊓ p' ⁻¹ᵁ W := by rw [Scheme.Hom.preimage_top, top_inf_eq]
  have H' := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := ⊤) le_top le_top hUY
  have hg : IsOpenImmersion (g.resLE ⊤ W le_top) := by
    have e := Scheme.Hom.resLE_comp_ι g (U := ⊤) (V := W) le_top
    have : IsOpenImmersion (g.resLE ⊤ W le_top ≫ (⊤ : Y.Opens).ι) := by
      rw [e]; infer_instance
    exact IsOpenImmersion.of_comp _ (⊤ : Y.Opens).ι
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H'.flip hg
  rw [← Scheme.Hom.resLE_comp_ι m (U := ⊤) (V := p' ⁻¹ᵁ W) le_top]
  infer_instance

/-- Over a field, the second projection of a product with a nonempty scheme is surjective. -/
private theorem surjective_pullback_snd {k : Type u} [Field k] {X L : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) [Nonempty X] :
    Function.Surjective (pullback.snd sX sL) := fun l => by
  obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (f := sX) (g := sL)
    (Nonempty.some inferInstance) l (Subsingleton.elim _ _)
  exact ⟨p, hp⟩

/-- Linear equivalence is compatible with integral multiples. -/
private theorem linearlyEquivalent_zsmul {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] {D₁ D₂ : Divisor X} (h : D₁.LinearlyEquivalent D₂) (m : ℤ) :
    (m • D₁).LinearlyEquivalent (m • D₂) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ ^ m, ?_⟩
  rw [← smul_sub, hφ]
  ext E
  rw [DivisorWithCoeffs.coeff_smul, coeff_principalDivisor, coeff_principalDivisor,
    PrimeDivisor.ord_zpow]

/-- **A log discrepancy computed from one rational top form.** If `K = div(ω)` is a canonical
divisor with `mK` Cartier, then `a(E; X, 0) = 1 + ord_E(f^*ω) - (1/m) coeff_E(f^*(mK))` for every
divisor `(Y, f, E)` over `X` with `f` proper. -/
private theorem isLogDiscrepancy_of_isPullback {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {m : ℕ} (hm : 0 < m) (hKc : ((m : ℤ) • divisorOfForm ω).IsCartier) (D : DivisorOver k sX)
    (hD : IsProper D.f) {C' : Divisor D.Y}
    (hC' : haveI := D.isLocallyNoetherian; haveI := D.isNormal;
      ∃ hC, ((m : ℤ) • divisorOfForm ω).IsPullback D.f hC C') :
    MMP.Intersection.IsLogDiscrepancy sX n 0 D
      (1 + (D.ordPullback ω : ℝ) - (m : ℝ)⁻¹ * C'.coeff D.E) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨hX, hD, ω, hω, ⟨_, hK, fun Γ => rfl⟩, 1, fun _ => (m : ℝ)⁻¹,
    fun _ => (m : ℤ) • divisorOfForm ω, fun _ => C', fun _ => hKc, fun Γ => ?_, fun _ => hC', ?_⟩
  · rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, coeff_divisorOfForm, smul_eq_mul]
    simp [hm']
  · simp

end Product

end Proof_lem_mmp_indexb_product_terminal

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **A product of a terminal variety with `ℙ¹` is terminal.** If `Y` is a normal complex variety
with `K_Y` `ℚ`-Cartier and `(Y, 0)` terminal, then `Y × ℙ¹` is integral and normal, and it is a
terminal variety: its canonical divisor is `ℚ`-Cartier and `(Y × ℙ¹, 0)` is terminal. -/
@[mmp "lem_mmp_indexb_product_terminal"]
public theorem IsTerminalVariety.pullback_projectiveLine {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsTerminalVariety sY) :
    ∃ (_ : IsIntegral (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
      (_ : IsNormal (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))),
      IsTerminalVariety (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) := by
  open MMP.Mori Proof_lem_mmp_indexb_product_terminal
    Proof_lem_mmp_indexb_product_terminal.ExteriorForms
    Proof_lem_mmp_indexb_product_terminal.ProductLine MMP.Mori.CanonicalDivisorExistence in
  · obtain ⟨⟨⟨halg, hchar, hpY, -⟩, -⟩, hterm⟩ := hY
    have hYv : IsNormalVariety ℂ sY := hpY.1
    haveI : AlgebraicGeometry.IsVariety ℂ sY := hYv.1
    haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    obtain ⟨-, n, K, hK, hKq⟩ := hpY
    have hn := hK.topologicalKrullDim_eq
    have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hn
    -- the line and the product
    have hL := projectiveLine_isLine (k := ℂ)
    obtain ⟨-, -, hvL, -⟩ := MMP.Fourfold.smooth_geometricallyIrreducible_isVariety_dim_line _ hL
    haveI : IsIntegral (projectiveLine ℂ) := hvL.toIsIntegral
    obtain ⟨⟨-, hsurj, hPv, hdimP, -, -⟩, -, -, -⟩ := MMP.Fourfold.product_line_basic sY _ hYv hL
    haveI : IsIntegral (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))) := hPv.1.toIsIntegral
    haveI : IsNormal (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))) := hPv.2
    refine ⟨inferInstance, inferInstance, ?_⟩
    haveI : LocallyOfFiniteType (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) :=
      hPv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
    haveI : CompactSpace (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0}) :=
      QuasiCompact.compactSpace_of_compactSpace
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
    haveI : IsDominant (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      ⟨hsurj.surj.denseRange⟩
    haveI : Nonempty Y := ⟨genericPoint Y⟩
    haveI : IsDominant (pullback.snd sY (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      ⟨(surjective_pullback_snd sY _).denseRange⟩
    have hnP : topologicalKrullDim (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0}) =
        ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hdimP, hn]; rfl
    have hdP := toNat_trdeg_functionField_of_topologicalKrullDim_eq
      (sX := pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) hnP
    -- a top form on `Y`, the canonical divisor `K_Y` it cuts out, and a Cartier multiple `mK_Y`
    obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hYv hn
    have hω₀ : b () ≠ 0 := b.ne_zero ()
    have hωY : tprodForm sY (b ()) ≠ 0 := tprodOne_ne_zero hω₀
    have hlinY : (divisorOfForm (tprodForm sY (b ()))).LinearlyEquivalent K := by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYv hK hωY
    have hKY : (divisorOfForm (tprodForm sY (b ()))).IsCanonicalDivisor sY n :=
      hK.of_linearlyEquivalent hlinY
    obtain ⟨m, hm, hmK⟩ := QDivisor.isQCartier_iff_exists_pos.mp (by simpa using hKq)
    have hmKc : ((m : ℤ) • K).IsCartier := by
      rw [← QDivisor.isCartierDivisor_toQDivisor, map_zsmul]
      exact hmK
    have hmKYc : ((m : ℤ) • divisorOfForm (tprodForm sY (b ()))).IsCartier :=
      Divisor.IsCartier.of_linearlyEquivalent (linearlyEquivalent_zsmul hlinY m) hmKc
    -- the product form and the canonical divisor `K_P` of `P = Y × ℙ¹`
    obtain ⟨j₀, _, hjs₀, -⟩ :=
      exists_projectiveLine_chart (k := ℂ) (genericPoint (projectiveLine ℂ))
    have hωP := prodForm_ne_zero sY (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) rfl
      j₀ hjs₀ hdY hdP (b ()) hω₀
    obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor
      (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) hPv hnP
    have hKP : (divisorOfForm (prodForm sY (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
        rfl j₀ n (b ()))).IsCanonicalDivisor
          (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) (n + 1) :=
      hK₀.of_linearlyEquivalent
        (by simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hPv hK₀ hωP)
    have hmKPc := isCartier_zsmul_divisorOfForm_prodForm sY
      (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) rfl hYv hPv hK₀ j₀ hjs₀ hdY hdP
      (b ()) hω₀ (K := divisorOfForm (tprodForm sY (b ()))) (fun Γ => rfl) m hmKYc
    have hPpair : MMP.Mori.IsPair (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) 0 := by
      refine ⟨hPv, n + 1, _, hKP, ?_⟩
      rw [add_zero]
      refine ⟨m, by exact_mod_cast hm.ne', ?_⟩
      rw [← map_zsmul]
      exact QDivisor.isCartierDivisor_toQDivisor.mpr hmKPc
    -- a strong resolution `μ : W ⟶ Y` and its product `μ' : W × ℙ¹ ⟶ Y × ℙ¹`
    obtain ⟨W, μ, hWv, hμp, hμb, hWsm, hiso, -⟩ := MMP.Resolution.exists_isStrongResolution sY hYv.1
    haveI : IsProper μ := hμp.isProper
    obtain ⟨hWln, hWn⟩ :=
      MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWsm
    haveI : IsIntegral W := hWv.toIsIntegral
    have hWnv : IsNormalVariety ℂ (μ ≫ sY) := ⟨hWv, hWn⟩
    haveI : LocallyOfFiniteType (μ ≫ sY) := hWv.toLocallyOfFiniteType
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sY)
    haveI : IsDominant μ := hμb.isDominant
    have hnW : topologicalKrullDim W = n :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (μ ≫ sY)
        hμb).symm.trans hn
    have hdW := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := μ ≫ sY) hnW
    have hsm_le : smoothLocus sY ≤ biregularLocus μ := le_biregularLocus hiso
    obtain ⟨⟨-, hsurj', hW'v, hdimW', -, -⟩, hsing', -, -⟩ :=
      MMP.Fourfold.product_line_basic (μ ≫ sY) _ hWnv hL
    haveI : IsIntegral (pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) := hW'v.1.toIsIntegral
    haveI : IsNormal (pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) := hW'v.2
    haveI : LocallyOfFiniteType
        (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ μ ≫ sY) :=
      hW'v.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ μ ≫ sY)
    haveI : CompactSpace (pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0}) :=
      QuasiCompact.compactSpace_of_compactSpace
        (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ μ ≫ sY)
    haveI := hsurj'
    haveI : IsDominant (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      ⟨hsurj'.surj.denseRange⟩
    haveI : Nonempty W := ⟨genericPoint W⟩
    haveI : IsDominant (pullback.snd (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      ⟨(surjective_pullback_snd (μ ≫ sY) _).denseRange⟩
    have H := isPullback_map_fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) μ
    haveI hμ'p : IsProper (prodMap sY μ) := MorphismProperty.of_isPullback H.flip ‹IsProper μ›
    have hμ'b : IsBirationalMorphism (prodMap sY μ) := by
      obtain ⟨V, hV, hVo⟩ := hμb.exists_isOpenImmersion
      have := isOpenImmersion_ι_comp_of_isPullback H V
      obtain ⟨w, hw⟩ := hV
      obtain ⟨x, hx⟩ := (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))).surjective w
      refine isBirationalMorphism_of_isOpenImmersion_ι_comp _
        (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ⁻¹ᵁ V) ⟨x, ?_⟩
      change (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) x ∈ V
      rw [hx]
      exact hw
    haveI : IsDominant (prodMap sY μ) := hμ'b.isDominant
    have hcomp : prodMap sY μ ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY =
        pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ μ ≫ sY := by
      rw [← Category.assoc, map_comp_fst_eq, Category.assoc]
    have hW'nv : IsNormalVariety ℂ
        (prodMap sY μ ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) := by
      rwa [hcomp]
    have hW'sm : IsSmoothScheme
        (prodMap sY μ ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) := by
      rw [hcomp]
      have h1 : (singularLocus (μ ≫ sY) : Set W) = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        apply hx
        rw [hWsm]
        trivial
      rw [h1, Set.preimage_empty] at hsing'
      refine eq_top_iff.mpr fun x _ => ?_
      by_contra hx
      have hx' : x ∈ (singularLocus
          (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ μ ≫ sY) : Set _) := hx
      rw [hsing'] at hx'
      exact hx'
    haveI : LocallyOfFiniteType
        (prodMap sY μ ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) := by
      rw [hcomp]; infer_instance
    have hnW' : topologicalKrullDim
        (pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0}) =
        ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hdimW', hnW]; rfl
    have hdW' := toNat_trdeg_functionField_of_topologicalKrullDim_eq
      (sX := prodMap sY μ ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) hnW'
    -- the prime divisors of `W × ℙ¹` have log discrepancy `≥ 1`, `> 1` when exceptional
    have hF : ∀ (F : MMP.Mori.PrimeDivisor (pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))))
        (n' : ℕ) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
          n' 0 ⟨pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)), prodMap sY μ, hW'nv, hμ'b, F⟩
          a →
        1 ≤ a ∧ ((⟨pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)), prodMap sY μ, hW'nv, hμ'b,
          F⟩ : DivisorOver ℂ
            (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)).IsExceptional →
            1 < a) := by
      intro F n' a ha
      by_cases hFe : (⟨pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)), prodMap sY μ, hW'nv,
        hμ'b, F⟩ : DivisorOver ℂ
            (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)).IsExceptional
      swap
      · have := eq_one_of_not_isExceptional hPpair hFe ha
        exact ⟨this.ge, fun h => absurd h hFe⟩
      haveI := isSeparated_toTerminal hPv.1.toIsSeparated
      have h2 := (isExceptional_iff_two_le_coheight _).mp hFe
      -- the centre of `F` on `W` lies in the exceptional set of `μ`
      have hnot : μ (pullback.fst (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) F.genericPoint) ∉
          biregularLocus μ := fun hb => by
        have hc : Order.coheight (prodMap sY μ F.genericPoint) = 1 :=
          (MMP.Positivity.coheight_map_of_mem_biregularLocus (prodMap sY μ)
            (map_mem_biregularLocus_of_isPullback H hb)).trans F.coheight_genericPoint
        have h3 : (2 : ℕ∞) ≤ 1 := h2.trans_eq hc
        norm_num at h3
      obtain ⟨ι, hι, -, hhor, hgen⟩ := exists_preimagePrimeDivisor (μ ≫ sY) hWnv
      have hFι : F ∈ Set.range ι := by
        by_contra hF'
        apply hnot
        rw [hhor F hF', map_genericPoint_of_isDominant]
        exact hsm_le MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus'
      obtain ⟨E, rfl⟩ := hFι
      have hEη : μ E.genericPoint ∉ biregularLocus μ := by rwa [hgen E]
      -- `E` is exceptional over `Y`
      have hEx : (⟨W, μ, hWnv, hμb, E⟩ : DivisorOver ℂ sY).IsExceptional := by
        by_contra hne
        obtain ⟨Γ, hv⟩ :=
          MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hYv _ hne
        have hc : μ E.genericPoint = Γ.genericPoint :=
          (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hYv.1 hv).trans rfl
        apply hEη
        rw [hc]
        exact hsm_le (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hYv Γ)
      -- the log discrepancy of `E` over `Y`, computed from `ω_Y`
      obtain ⟨CW, hCW⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant μ hmKYc
      have haE := isLogDiscrepancy_of_isPullback hYv hωY hKY hm hmKYc ⟨W, μ, hWnv, hμb, E⟩
        inferInstance ⟨_, hCW⟩
      have h1E := hterm n _ _ hEx (by rwa [map_zero])
      -- the log discrepancy of `F = E × ℙ¹` over `P`, computed from the product form
      obtain ⟨CP, hCP⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant (prodMap sY μ) hmKPc
      have haF := isLogDiscrepancy_of_isPullback hPv hωP hKP hm hmKPc
        ⟨pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)), prodMap sY μ, hW'nv, hμ'b, ι E⟩
        hμ'p ⟨_, hCP⟩
      have hae := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha haF
      have hord : (⟨pullback (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)), prodMap sY μ, hW'nv, hμ'b,
          ι E⟩ : DivisorOver ℂ (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)).ordPullback
            (prodForm sY (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) rfl j₀ n (b ())) =
          (⟨W, μ, hWnv, hμb, E⟩ : DivisorOver ℂ sY).ordPullback (tprodForm sY (b ())) :=
        ordForm_pullback_prodForm sY μ hWnv j₀ hjs₀ hμb.functionFieldMap_bijective
          hμ'b.functionFieldMap_bijective hdY hdP hdW _ rfl hdW' (b ()) E (ι E) (hι E)
      have hFj : pullback.snd (μ ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) (ι E).genericPoint ∈
          j₀.opensRange := by
        rw [snd_genericPoint_eq_of_support_eq_preimage (μ ≫ sY) hWnv E (ι E) (hι E)]
        exact genericPoint_mem_opensRange j₀
      have hcoeff : CP.coeff (ι E) = CW.coeff E :=
        coeff_isPullback_prodMap sY μ hYv (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
          rfl j₀ hjs₀ hdY hdP (b ()) (fun Γ => rfl) (fun G => rfl) m hmKYc hCW hCP E (ι E)
          (hgen E) hFj
      have e1 : a = 1 + ((⟨W, μ, hWnv, hμb, E⟩ : DivisorOver ℂ sY).ordPullback
          (tprodForm sY (b ())) : ℝ) - (m : ℝ)⁻¹ * (CW.coeff E : ℝ) := by
        rw [hae, ← hord, ← hcoeff]
      rw [e1]
      exact ⟨h1E.le, fun _ => h1E⟩
    -- conclusion
    have hbound := fun (D : DivisorOver ℂ (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY))
        (n' : ℕ) (a : ℝ) (ha : MMP.Intersection.IsLogDiscrepancy
          (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) n' 0 D a) =>
      logDiscrepancy_bounds_of_smoothModel hPpair (prodMap sY μ) hW'nv hμ'b hW'sm hF D ha
    refine ⟨⟨⟨halg, hchar, hPpair, fun P => by simp⟩, fun n' D a ha => ?_⟩, fun n' D a hD ha => ?_⟩
    · rw [map_zero] at ha
      exact zero_lt_one.trans_le (hbound D n' a ha).1
    · rw [map_zero] at ha
      exact (hbound D n' a ha).2 hD

end MMP.Fourfold
