module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Chow.CycleClassDegree
import MMP.AlgebraicGeometry.CycleMap.Stacks.PushforwardInjective
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison

/-!
# Fundamental classes of subvarieties, and junctions extracting all low valuations

This file proves two results of the fourfold programme.

**Fundamental classes are nonzero.** Let `X` be a projective variety over `ℂ` and `A ⊆ X` an
irreducible closed subvariety of dimension `r`. Then the fundamental class `[A] ∈ H_{2r}(X, ℚ)` is
nonzero. The argument is Fulton's, read through the cycle map `cl : A_* → H_*`. Embed `X ⊆ ℙᴺ`
by a closed immersion `i`. Then `i_* [A] = cl([i(A)])`, and in `A_r ℙᴺ` the class `[i(A)]` is
`d [Lʳ]` with `d = ∫ c₁(𝒪(1))^r ∩ [i(A)] > 0`. For a linear subspace `L^{N-r}` with dual class
`u ∈ H^{2r}(ℙᴺ)`, `cl([i(A)] · [L^{N-r}]) = u ∩ cl([i(A)])` (Fulton, Corollary 19.2), and
`[i(A)] · [L^{N-r}] = d [L⁰]`. Pushing forward to a point, `cl` of a zero-cycle class determines
its degree, so `cl([A]) = 0` would force `d = 0`.

**Junctions extracting all low valuations are terminal.** Let `(X, B)` be a projective klt
fourfold pair and `(p, Θ)`, `p : Y ⟶ X`, a crepant junction of `(X, B)` extracting the whole
low-discrepancy set `I(X, B)` (`MMP.Fourfold.lowDiscrepancySet`), the finitely many normalized
divisorial valuations exceptional over `X` with `a(s; X, B) ≤ 1`. Then `(Y, Θ)` is a terminal
pair and every coefficient of `Θ` lies in `[0, 1)`. A divisor `(W, g, F)` over `Y` is a divisor
`(W, g ≫ p, F)` over `X`; since `K_Y + Θ = p^*(K_X + B)`, both have the same log discrepancy. If
`F` is exceptional over `Y`, its valuation is exceptional over `X` and is not in `I(X, B)`, whose
members have divisorial centres `E_s` on `Y`; so its log discrepancy is `> 1`. `Y` has a
canonical divisor: the canonical sheaf of its smooth locus `U` is invertible, hence `𝒪_U(K_U)`,
and the closure `K` of `K_U` in `Y` has `𝒪_Y(K)|_U ≅ 𝒪_U(K_U)`.

## Main results

* `MMP.Analytic.fundamentalClass_ne_zero`: `[A] ≠ 0` for `A ⊆ X`, `X` projective.
* `MMP.Fourfold.FourfoldCrepantJunction.isKltTerminalPair_of_coe_eq_lowDiscrepancySet`:
  `(Y, Θ)` is terminal with coefficients in `[0, 1)`.

## Implementation notes

`H_{2r}(X, ℚ)` is the Borel–Moore homology `MMP.Analytic.borelMooreHomology` of the complex
realization of `X`, and `[A]` is `MMP.Analytic.fundamentalClass x hx` for the generic point
`x` of `A`. Since `X(ℂ)` is compact for projective `X`, this is the singular homology of the
source. Projectivity cannot be dropped: the class of a point of the affine line is zero in
Borel–Moore homology. The class `[A]` needs `X` to be a complex scheme in Fulton's sense
(`MMP.IsComplexScheme`), which every projective variety is.

A crepant junction `MMP.Fourfold.FourfoldCrepantJunction` already carries that `(X, B)` is a
projective klt fourfold pair and that `I ⊆ I(X, B)`; the hypothesis here is the equality
`I = I(X, B)`. Terminality is `MMP.Fourfold.IsKltTerminalPair` on `Y` over `ℂ`, through the
structure morphism `p ≫ sX`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Corollary 19.2, §8.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Analytic

/-- The fundamental class `[A] ∈ H_{2r}(X, ℚ)` of an `r`-dimensional irreducible closed
subvariety `A = closure {x}` of a projective complex variety `X` is nonzero. -/
@[mmp "lem_oai4_c1_component_class_nonzero"]
public theorem fundamentalClass_ne_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [MMP.IsComplexScheme X]
    (hX : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))) {r : ℕ} (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = r) :
    fundamentalClass x hx ≠ 0 := by
  intro h
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hX
  haveI : Stacks.Ample.IsInvertibleModule X H := hH
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ hX.isProjective
  refine MMP.Chow.pointCycleClass_ne_zero H ((Stacks.AmpleBridge.isAmple_iff_isAmple X H).mpr hHa)
    x hx ?_
  refine MMP.Chow.pushforward_injective_of_isClosedEmbedding
    (TopCat.ofHom ⟨_, MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩)
    MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap
    MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.isClosedEmbedding
    MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.surjective _ ?_
  rwa [map_zero]

end MMP.Analytic

namespace MMP.Fourfold

open TopologicalSpace Opposite MMP.Mori

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The morphism `p` of a crepant junction is proper. -/
private theorem isProper_p (J : FourfoldCrepantJunction sX B I) : IsProper J.p :=
  isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism

/-- A divisor `(W, g, F)` over the source `Y` of a junction, with `g` proper, as the divisor
`(W, g ≫ p, F)` over `X`. -/
private noncomputable def compDivisorOver (J : FourfoldCrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) (hD : IsProper D.f) : DivisorOver ℂ sX where
  Y := D.Y
  f := D.f ≫ J.p
  isNormalVariety := by
    have := D.isNormalVariety
    rwa [Category.assoc]
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := D.isNormal
    haveI := D.isLocallyNoetherian
    haveI := isProper_p J
    exact isBirationalMorphism_comp_of_isBirational J.p D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism J.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

private theorem isProper_compDivisorOver (J : FourfoldCrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) (hD : IsProper D.f) : IsProper (compDivisorOver J D hD).f := by
  haveI := isProper_p J
  change IsProper (D.f ≫ J.p)
  infer_instance

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

section DivisorialRestrict

/-- In an irreducible space every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (Z : irreducibleComponents T) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))

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
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
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

/-- The unique irreducible component `univ` of an irreducible scheme `Y`. -/
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
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
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
  let e := RingEquiv.ofBijective (functionFieldMap U.ι)
    (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary U, trivial⟩)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
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
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
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
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The smooth locus of a variety is a smooth scheme over the base. -/
private theorem smooth_smoothLocus_ι {Z : Scheme.{0}} (s : Z ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType s] : Smooth ((smoothLocus s).ι ≫ s) := by
  rw [smoothLocus_eq_smoothLocus, ← Scheme.Hom.smoothLocus_eq_top_iff,
    ← Scheme.Hom.preimage_smoothLocus_eq]
  simp

/-- The source of a junction has a canonical divisor: the canonical sheaf of its smooth locus
`U` is invertible, hence `𝒪_U(K_U)` for a divisor `K_U` of `U`, and the closure `K` of `K_U` in
`Y` has `𝒪_Y(K)|_U ≅ 𝒪_U(K_U)`. -/
private theorem exists_isCanonicalDivisor (J : FourfoldCrepantJunction sX B I) :
    ∃ (n : ℕ) (K : Divisor J.Y), K.IsCanonicalDivisor J.sY n := by
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  haveI : MMP.Mori.IsVariety ℂ J.sY := hY.1
  haveI : LocallyOfFiniteType J.sY := hY.1.toLocallyOfFiniteType
  set U := smoothLocus J.sY
  have hgen : genericPoint J.Y ∈ U :=
    MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus'
  haveI : Nonempty U := ⟨⟨_, hgen⟩⟩
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  haveI hUvar : MMP.Mori.IsVariety ℂ (U.ι ≫ J.sY) :=
    Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι ℂ J.sY U
  haveI : Smooth (U.ι ≫ J.sY) := smooth_smoothLocus_ι J.sY
  have hUdim : topologicalKrullDim U = (4 : ℕ) :=
    (Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens ℂ J.sY U).trans
      (by exact_mod_cast J.dim_eq)
  haveI : SmoothOfRelativeDimension 4 (U.ι ≫ J.sY) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ 4 hUdim
  have hinv := Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ J.sY) 4
  have hM := Stacks.SheafOfModules.isInvertible_of_tensorInvertible
    (X := U.toScheme.toRingedSpace) (canonicalSheaf J.sY 4) (h := hinv)
  haveI : CompactSpace U.toScheme :=
    (hUvar.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (canonicalSheaf J.sY 4) := hM.toAlgebraicGeometry
  obtain ⟨DU, ⟨e⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
    (canonicalSheaf J.sY 4)
  let K : Divisor J.Y := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap U.ι) DU
  have hK : K.restrictOpen U = DU :=
    Finsupp.comapDomain_mapDomain _ (OpenWeilRestriction.primeDivisorMap_injective U.ι) DU
  haveI := isIso_divisorialSheafRestrictHom U K
  exact ⟨4, K, J.dim_eq, ⟨asIso (divisorialSheafRestrictHom U K) ≪≫ eqToIso (congrArg Divisor.divisorialSheaf hK) ≪≫ e⟩⟩

/-- The only irreducible component of an irreducible space is the whole space. -/
private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 :=
  (eq_univ_of_irreducibleComponents W).symm ▸ Set.mem_univ t

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
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
    rwa [← trdeg_functionField_eq_of_bijective sX f hf]
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero' {U : Scheme.{0}} [IsIntegral U]
    (hX : IsNormalVariety ℂ sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- The base of a junction is quasi-compact: it is projective over `ℂ`. -/
private theorem compactSpace_base (J : FourfoldCrepantJunction sX B I) : CompactSpace X := by
  have := isProper_of_isProjectiveMorphism _ J.isProjectiveVariety_base.isProjective
  exact QuasiCompact.compactSpace_of_compactSpace sX

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

/-- **Crepant transfer of log discrepancies.** A log discrepancy of `(W, g, F)` with respect to
`(Y, Θ)` is the log discrepancy of `(W, g ≫ p, F)` with respect to `(X, B)`. -/
private theorem isLogDiscrepancy_compDivisorOver (J : FourfoldCrepantJunction sX B I) {n : ℕ}
    {D : DivisorOver ℂ J.sY} {a : ℝ} (hD : IsProper D.f)
    (h : MMP.Intersection.IsLogDiscrepancy J.sY n (QDivisor.toRDivisor J.Θ) D a) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) (compDivisorOver J D hD) a := by
  obtain ⟨hY, -, -, -, ⟨KY, hKY, -⟩, -⟩ := id h
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  have hn : n = 4 := by exact_mod_cast hKY.topologicalKrullDim_eq.symm.trans J.dim_eq
  subst hn
  haveI := compactSpace_base J
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType J.sY := hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (J.p ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI := J.isBirationalMorphism.isDominant
  obtain ⟨-, n₀, K₀, hK₀, hQ⟩ := J.isKltPair.1.isPair
  have hn₀ : n₀ = 4 := by exact_mod_cast hK₀.topologicalKrullDim_eq.symm.trans J.dim_base
  subst hn₀
  obtain ⟨ω, hω, -⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK₀
  have hKXle : (divisorOfForm ω).LinearlyEquivalent K₀ := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK₀ hω
    rwa [one_smul] at this
  have hKXcan : (divisorOfForm ω).IsCanonicalDivisor sX 4 := hK₀.of_linearlyEquivalent hKXle
  have hQX : (Divisor.toQDivisor (divisorOfForm ω) + B).IsQCartier :=
    hQ.add_of_linearlyEquivalent hKXle.symm
  obtain ⟨m₀, hm₀, DX, hDX, hDXc⟩ := hQX.exists_pos
  have hω' : pullbackRationalPluriForms sX J.p ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero' hX J.isBirationalMorphism J.dim_base hω
  have hKYle : (divisorOfForm (pullbackRationalPluriForms sX J.p ω)).LinearlyEquivalent KY := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hKY hω'
    rwa [one_smul] at this
  have hKYcan : (divisorOfForm (pullbackRationalPluriForms sX J.p ω)).IsCanonicalDivisor J.sY 4 :=
    hKY.of_linearlyEquivalent hKYle
  have hcrep := J.isPullback_canonical_add_boundary ω hω (divisorOfForm ω)
    (fun Γ => coeff_divisorOfForm ω Γ) (divisorOfForm (pullbackRationalPluriForms sX J.p ω))
    (fun Γ => coeff_divisorOfForm _ Γ)
  obtain ⟨hBsupp, hpbQ⟩ := hcrep
  obtain ⟨DY, hDY, hDYpb⟩ := hpbQ m₀ hm₀ DX hDX hDXc
  have hDYc : DY.IsCartier := hDYpb.isCartier hDXc
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : CompactSpace D.Y :=
    (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨L, hL⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hDYc
  have h2 : MMP.Intersection.IsLogDiscrepancy J.sY 4 (QDivisor.toRDivisor J.Θ) D
      (1 + (D.ordPullback (pullbackRationalPluriForms sX J.p ω) : ℝ) -
        ∑ _i : Fin 1, (m₀ : ℝ)⁻¹ * (L.coeff D.E : ℝ)) := by
    refine ⟨hY, hD, _, hω', ⟨_, hKYcan, fun Γ => coeff_divisorOfForm _ Γ⟩, 1,
      fun _ => (m₀ : ℝ)⁻¹, fun _ => DY, fun _ => L, fun _ => hDYc, fun Γ => ?_,
      fun _ => ⟨_, hL⟩, rfl⟩
    exact ordForm_add_coeff_eq _ _ hm₀ hDY Γ
  have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.unique h h2
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) J.dim_base
  refine ⟨hX, isProper_compDivisorOver J D hD, ω, hω,
    ⟨_, hKXcan, fun Γ => coeff_divisorOfForm ω Γ⟩, 1, fun _ => (m₀ : ℝ)⁻¹, fun _ => DX,
    fun _ => L, fun _ => hDXc, fun Γ => ordForm_add_coeff_eq ω B hm₀ hDX Γ,
    fun _ => ⟨_, isPullback_comp hDYpb hL
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ J.p) DX)⟩, ?_⟩
  rw [heq]
  congr 3
  change D.E.ordForm (pullbackRationalPluriForms (J.p ≫ sX) D.f
    (pullbackRationalPluriForms sX J.p ω)) =
      D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ J.p) ω)
  rw [pullbackRationalPluriForms_comp J.p D.f
    (IsBirationalMorphism.functionFieldMap_bijective J.isBirationalMorphism)
    (IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism) hd ω]
  rfl

/-- The centre of a divisor exceptional over a normal variety has codimension at least two. -/
private theorem two_le_codimension_center_of_isExceptional {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (D : DivisorOver ℂ sY) (hE : D.IsExceptional) : 2 ≤ codimension D.center := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sY := hY.1.toIsSeparated
  have hsep : IsSeparated (Y ↘ ⊤_ Scheme) := by
    have : (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional at hE
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hE
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set Y), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc] at hE
  change 2 ≤ closedsCodimension (T := Y) ⟨(D.center : Set Y), D.center.isClosed⟩ at hE
  rwa [closedsCodimension_coe] at hE

/-- A prime divisor `Q` of the source `Y` of a junction, as the divisor `(Y, p, Q)` over `X`. -/
private def primeDivisorOver (J : FourfoldCrepantJunction sX B I) (Q : MMP.Mori.PrimeDivisor J.Y) :
    DivisorOver ℂ sX :=
  ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, Q⟩

/-- A divisor exceptional over `Y` does not have the valuation `ord_Q` of a prime divisor `Q` of
`Y`. -/
private theorem valuation_compDivisorOver_ne (J : FourfoldCrepantJunction sX B I)
    {D : DivisorOver ℂ J.sY} (hD : IsProper D.f) (hE : D.IsExceptional)
    (Q : MMP.Mori.PrimeDivisor J.Y) :
    (compDivisorOver J D hD).valuation ≠ (primeDivisorOver J Q).valuation := by
  intro hv
  have hY := J.isQFactorial.1
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := J.isBirationalMorphism.isDominant
  have hbij := IsBirationalMorphism.functionFieldMap_bijective J.isBirationalMorphism
  have hvY : D.valuation = (DivisorOver.ofPrimeDivisor ℂ hY Q).valuation := by
    ext h
    obtain ⟨g, rfl⟩ := hbij.2 h
    have := congrArg (fun v => v g) hv
    have hc : functionFieldMap (D.f ≫ J.p) g = functionFieldMap D.f (functionFieldMap J.p g) :=
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ g).symm
    change D.E.divisorialValuation (functionFieldMap (D.f ≫ J.p) g) =
      Q.divisorialValuation (functionFieldMap J.p g) at this
    change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap J.p g)) =
      Q.divisorialValuation (functionFieldMap (𝟙 J.Y) (functionFieldMap J.p g))
    rw [MMP.Mori.functionFieldMap_id_apply, ← hc, this]
  exact (two_le_codimension_center_of_isExceptional hY D hE |>
    (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hY D).mp) _ hvY

/-- **Strict transforms.** Every prime divisor `P` of `X` has a strict transform `Q` on `Y`, with
`ord_Q = ord_P` as valuations of `k(X)`. -/
private theorem exists_valuation_primeDivisorOver_eq (J : FourfoldCrepantJunction sX B I)
    (hX : IsNormalVariety ℂ sX) (P : MMP.Mori.PrimeDivisor X) :
    ∃ Q : MMP.Mori.PrimeDivisor J.Y,
      (primeDivisorOver J Q).valuation = (DivisorOver.ofPrimeDivisor ℂ hX P).valuation := by
  haveI := isProper_p J
  haveI := J.isBirationalMorphism.isDominant
  obtain ⟨y, hy, hcoh, -, -⟩ := MMP.Intersection.exists_preimage_of_coheight_eq_one J.p
    (IsBirationalMorphism.functionFieldMap_bijective J.isBirationalMorphism)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_⟩
  refine MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX _ P ?_
  change J.p (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh).genericPoint = _
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hy]

/-- A divisor exceptional over `Y` is exceptional over `X`. -/
private theorem isExceptionalValuation_compDivisorOver (J : FourfoldCrepantJunction sX B I)
    {D : DivisorOver ℂ J.sY} (hD : IsProper D.f) (hE : D.IsExceptional) :
    MMP.Intersection.IsExceptionalValuation ℂ sX (compDivisorOver J D hD).valuation := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  by_contra h
  have h2 : ¬ 2 ≤ codimension (compDivisorOver J D hD).center :=
    fun h2 => h ⟨_, isProper_compDivisorOver J D hD, rfl, h2⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at h2
  push Not at h2
  obtain ⟨P, hP⟩ := h2
  obtain ⟨Q, hQ⟩ := exists_valuation_primeDivisorOver_eq J hX P
  exact valuation_compDivisorOver_ne J hD hE Q (hP.trans hQ.symm)

/-- The log discrepancies of the extracted valuations lie in `(0, 1]`. -/
private theorem logDiscrepancy_mem_Ioc (J : FourfoldCrepantJunction sX B I) {a : I → ℚ}
    (ha : ∀ s : I, IsValuationLogDiscrepancy sX B s (a s)) (s : I) :
    0 < a s ∧ a s ≤ 1 := by
  obtain ⟨n, D, -, hv, hlog⟩ := ha s
  obtain ⟨-, a', ⟨n', D', -, hv', hlog'⟩, hle⟩ := J.subset_lowDiscrepancySet s.2
  have heq : ((a s : ℚ) : ℝ) = a' :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog hlog' (hv.trans hv'.symm)
  have hpos := J.isKltPair.2 n D _ hlog
  exact ⟨by exact_mod_cast hpos, by exact_mod_cast heq ▸ hle⟩

/-- The image of a divisor under a map of prime divisors has coefficient zero at a prime divisor
that is not the image of any prime divisor. -/
private theorem coeff_mapPrimeDivisors_eq_zero {R : Type*} [AddCommMonoid R] {X' Y' : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X' → Option (MMP.Mori.PrimeDivisor Y'))
    (D : DivisorWithCoeffs R X') (Γ : MMP.Mori.PrimeDivisor Y') (h : ∀ P, φ P ≠ some Γ) :
    (DivisorWithCoeffs.mapPrimeDivisors φ D).coeff Γ = 0 := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    rfl
  | add D₁ D₂ h₁ h₂ =>
    have := congrArg₂ (· + ·) h₁ h₂
    simp only [add_zero] at this
    rw [map_add]
    exact this
  | single P r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    cases hφ : φ P with
    | none => rfl
    | some Q =>
      change (Finsupp.single Q r) Γ = 0
      exact Finsupp.single_eq_of_ne (fun hQ => h P (by rw [hφ, hQ]))

/-- The strict transform `p⁻¹_* B` does not contain the exceptional divisors `E_s`. -/
private theorem coeff_inverseTransformDivisor_E (J : FourfoldCrepantJunction sX B I) (s : I) :
    (inverseTransformDivisor J.p B).coeff (J.E s) = 0 := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  refine coeff_mapPrimeDivisors_eq_zero _ _ _ fun P hP => ?_
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP).1
  have hE : (primeDivisorOver J (J.E s)).IsExceptional :=
    (J.isExceptional_iff _).mpr ⟨s, rfl⟩
  have h2 := two_le_codimension_center_of_isExceptional hX _ hE
  rw [MMP.Positivity.DivisorOver.codimension_center] at h2
  change 2 ≤ Order.coheight (J.p (J.E s).genericPoint) at h2
  rw [hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The coefficients of a klt boundary are `< 1`. -/
private theorem coeff_lt_one_of_isKltPair (J : FourfoldCrepantJunction sX B I)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P < 1 := by
  have hpair := J.isKltPair.1.isPair
  have hX : IsNormalVariety ℂ sX := hpair.1
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hprop : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f := by
    change IsProper (𝟙 X)
    infer_instance
  have hpos := J.isKltPair.2 n _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hprop)
  have heq := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha
  rw [heq] at hpos
  push_cast at hpos
  exact_mod_cast (by linarith : ((B.coeff P : ℚ) : ℝ) < 1)

/-- The image of a divisor `D` under a map `φ` of prime divisors has, at the image `Γ` of a single
prime divisor `P`, the coefficient of `D` at `P`. -/
private theorem coeff_mapPrimeDivisors_of_eq_some {R : Type*} [AddCommMonoid R]
    {X' Y' : Scheme.{0}} (φ : MMP.Mori.PrimeDivisor X' → Option (MMP.Mori.PrimeDivisor Y'))
    (D : DivisorWithCoeffs R X') {Γ : MMP.Mori.PrimeDivisor Y'} {P : MMP.Mori.PrimeDivisor X'}
    (hP : φ P = some Γ) (hinj : ∀ P', φ P' = some Γ → P' = P) :
    (DivisorWithCoeffs.mapPrimeDivisors φ D).coeff Γ = D.coeff P := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    rfl
  | add D₁ D₂ h₁ h₂ =>
    have := congrArg₂ (· + ·) h₁ h₂
    rw [map_add]
    exact this
  | single P' r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    change _ = (Finsupp.single P' r) P
    cases hφ : φ P' with
    | none =>
      have hne : P' ≠ P := fun h => by rw [h, hP] at hφ; cases hφ
      exact (Finsupp.single_eq_of_ne' hne).symm
    | some Q =>
      change (Finsupp.single Q r) Γ = (Finsupp.single P' r) P
      by_cases hQ : Q = Γ
      · subst hQ
        rw [hinj P' hφ, Finsupp.single_eq_same, Finsupp.single_eq_same]
      · have hne : P' ≠ P := fun h => hQ (by rw [h, hP] at hφ; exact (Option.some.inj hφ).symm)
        rw [Finsupp.single_eq_of_ne' hQ, Finsupp.single_eq_of_ne' hne]

/-- The strict transform `p⁻¹_* B` has coefficients in `[0, 1)`: those of the klt boundary `B`. -/
private theorem coeff_inverseTransformDivisor_mem_Ico (J : FourfoldCrepantJunction sX B I)
    (Γ : MMP.Mori.PrimeDivisor J.Y) :
    0 ≤ (inverseTransformDivisor J.p B).coeff Γ ∧ (inverseTransformDivisor J.p B).coeff Γ < 1 := by
  by_cases h : ∃ P, inverseTransformPrimeDivisor J.p P = some Γ
  · obtain ⟨P, hP⟩ := h
    have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hP).1
    have hinj : ∀ P', inverseTransformPrimeDivisor J.p P' = some Γ → P' = P := fun P' hP' =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hP').1.symm.trans hη)
    change 0 ≤ (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff Γ ∧
      (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff Γ < 1
    rw [coeff_mapPrimeDivisors_of_eq_some _ B hP hinj]
    exact ⟨J.isKltPair.1.nonneg P, coeff_lt_one_of_isKltPair J P⟩
  · push Not at h
    change 0 ≤ (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff Γ ∧
      (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff Γ < 1
    rw [coeff_mapPrimeDivisors_eq_zero _ B Γ h]
    norm_num

/-- The coefficients of the boundary of a junction lie in `[0, 1)`. -/
private theorem coeff_Θ_mem_Ico (J : FourfoldCrepantJunction sX B I) :
    ∀ Γ : MMP.Mori.PrimeDivisor J.Y, 0 ≤ J.Θ.coeff Γ ∧ J.Θ.coeff Γ < 1 := by
  classical
  obtain ⟨a, ha, hΘ⟩ := J.Θ_eq
  intro Γ
  have hsum : (∑ s : I, Finsupp.single (J.E s) (1 - a s) : QDivisor J.Y).coeff Γ =
      ∑ s : I, if J.E s = Γ then 1 - a s else 0 := by
    change (∑ s : I, Finsupp.single (J.E s) (1 - a s)) Γ = _
    rw [Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl fun s _ => Finsupp.single_apply
  rw [hΘ, DivisorWithCoeffs.coeff_add, hsum]
  by_cases hΓ : Γ ∈ Set.range J.E
  · obtain ⟨t, rfl⟩ := hΓ
    rw [coeff_inverseTransformDivisor_E, zero_add,
      Finset.sum_eq_single t (fun s _ hst => if_neg (fun h => hst (J.injective h)))
        (fun h => absurd (Finset.mem_univ t) h), if_pos rfl]
    have := logDiscrepancy_mem_Ioc J ha t
    constructor <;> linarith
  · rw [Finset.sum_eq_zero (fun s _ => if_neg (fun h => hΓ ⟨s, h⟩)), add_zero]
    exact coeff_inverseTransformDivisor_mem_Ico J Γ

/-- **Junctions extracting all low valuations are terminal.** If `(p, Θ)`, `p : Y ⟶ X`, is a
crepant junction of a projective klt fourfold pair `(X, B)` extracting the whole low-discrepancy
set `I(X, B)`, then `(Y, Θ)` is terminal and every coefficient of `Θ` lies in `[0, 1)`. -/
@[mmp "prop_oai4_terminal_chain_b"]
public theorem FourfoldCrepantJunction.isKltTerminalPair_of_coe_eq_lowDiscrepancySet
    (J : FourfoldCrepantJunction sX B I) (hI : (I : Set _) = lowDiscrepancySet sX B) :
    IsKltTerminalPair J.sY J.Θ ∧
      ∀ Γ : MMP.Mori.PrimeDivisor J.Y, 0 ≤ J.Θ.coeff Γ ∧ J.Θ.coeff Γ < 1 := by
  have hcoeff := coeff_Θ_mem_Ico J
  obtain ⟨n₀, K, hK⟩ := exists_isCanonicalDivisor J
  have hpair : MMP.Fourfold.IsPair J.sY J.Θ :=
    { isAlgClosed := inferInstance
      charZero := inferInstance
      isPair := ⟨J.isQFactorial.1, n₀, K, hK, isQCartier_of_isQFactorial _ J.isQFactorial _⟩
      nonneg := fun P => (hcoeff P).1 }
  refine ⟨⟨⟨hpair, fun n D a ha => ?_⟩, fun n D a hE ha => ?_⟩, hcoeff⟩
  · exact J.isKltPair.2 n _ a (isLogDiscrepancy_compDivisorOver J ha.2.1 ha)
  · have hD : IsProper D.f := ha.2.1
    by_contra hle
    push Not at hle
    have hmem : (compDivisorOver J D hD).valuation ∈ lowDiscrepancySet sX B :=
      ⟨isExceptionalValuation_compDivisorOver J hD hE, a,
        ⟨n, _, isProper_compDivisorOver J D hD, rfl, isLogDiscrepancy_compDivisorOver J hD ha⟩,
        hle⟩
    rw [← hI] at hmem
    exact valuation_compDivisorOver_ne J hD hE (J.E ⟨_, hmem⟩) (J.valuation_eq ⟨_, hmem⟩).symm

end MMP.Fourfold

end
