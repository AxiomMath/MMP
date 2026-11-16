module

public import MMP.AlgebraicGeometry.Resolution.BlowupChartCoordinates
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.LogDerivations
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.Morphisms.Birational.AntiAmpleExceptional
public import MMP.AlgebraicGeometry.Curves.DegreeEuler
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Exceptional curves, normalizations, and chart computations for blow-ups

This file collects several facts from Kollár's lectures on resolution of singularities.

*Divisorial sheaves.* On a normal integral locally Noetherian scheme, the sheaf `𝒪_X(D)` of a
Cartier divisor `D`, inside the sheaf of total quotient rings, is the divisorial sheaf of its Weil
divisor, inside the sheaf of rational functions: a section of either is a rational function, and
the two membership conditions agree because the order of a local equation of `D` along a prime
divisor is the coefficient of the Weil divisor.

*Surfaces.* Let `g : S ⟶ X` be a projective birational morphism of surfaces over a field `k`.
If `X` is normal and no integral projective curve of `S` is contracted by `g` to a point, then
every closed fibre of `g` is finite, so the finite-fibre locus of `g`, over which `g` is an
isomorphism, is all of `X`. If `S` and `X` are normal and quasi-projective and `D` is a Cartier
divisor on `S` with Weil divisor `F₁ - F₂`, where `F₁, F₂ ≥ 0` have no common component and
`0 ≠ F₁` is `g`-exceptional, then some `g`-exceptional curve `C ⊆ Supp F₁` has `(C · D) < 0`:
compare `D` with an effective Cartier divisor `W` such that `-W` is `g`-ample, along a component
`C` of `F₁` minimising the ratio of the coefficients of `W` and `F₁`.

*Normalization.* The normalization `g : X ⟶ Y` of a `k`-variety in a finite extension of `k(Y)`
is finite and surjective with normal source: over an affine open with ring `A`, it is the
spectrum of the integral closure of `A`.

*Dimension zero.* On a smooth scheme of dimension `0` over a field every point is the generic
point of a component and every local ring is a field, so an ideal sheaf nonzero on every
component is the unit ideal and has maximal order `0`; hence the identity functor is an order
reduction functor for ideals and for marked ideals.

*Charts of a blow-up.* On the chart `U_ℓ` of the blow-up `π : B_Z X → X` along generators
`x_1, …, x_r` of the centre, the chart transforms `π^*f_i / x_ℓ^m` of generators of a marked
ideal `(I, m)` with `π^*I ⊆ (π^*I_Z)^m` generate its birational transform; and if
`π^*f = y_ℓ^m g`, the derivatives of `f` and `g` are related by Kollár's formulas (3.75.1) and
(3.75.3).

## Main definitions

* `MMP.Intersection.totalQuotientToRationalFunctions`: a section of the sheaf `𝓜_X` of total
  quotient rings, read as a section of `MMP.Mori.rationalFunctionsPresheaf`.
* `MMP.Intersection.IsWeilDivisorOfCartier.sheafIsoDivisorialSheaf`: on a normal integral locally
  Noetherian scheme, `𝒪_X(D) ≅ 𝒪_X(D')` for a Cartier divisor `D` with Weil divisor `D'`.

## Main results

* `MMP.Intersection.IsWeilDivisorOfCartier.isCartier`
* `MMP.Intersection.IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf`
* `MMP.Resolution.isIso_of_forall_not_isContractedProjectiveCurve`
* `MMP.Resolution.exists_isContractedProjectiveCurve_of_isExceptional`
* `MMP.Resolution.exists_isContractedProjectiveCurve_degreeOn_neg`
* `MMP.Resolution.exists_isContractedProjectiveCurve_cartierCurveIntersection_neg`
* `MMP.Resolution.IsNormalizationInExtension.isFinite_and_surjective_and_isNormal`
* `MMP.Resolution.eq_top_and_maxOrder_eq_zero_of_topologicalKrullDim_eq_zero`
* `MMP.Resolution.isOrderReductionFunctor_identity_dim_zero`
* `MMP.Resolution.BlowupChartData.exists_birationalTransform_ideal_eq_span_chartTransform`
* `MMP.Resolution.Kollar.appLE_partialDerivative_eq_pow_mul_partialDerivative_of_ne`
* `MMP.Resolution.Kollar.appLE_partialDerivative_self_eq_pow_mul`

## Implementation notes

The negativity lemma is proved with Weil divisors that are Cartier and the additive degree
`MMP.Mori.Divisor.degreeOn`; the intersection number `cartierCurveIntersection D C` is identified
with the degree of the Weil divisor of `D` through
`MMP.Intersection.IsWeilDivisorOfCartier.sheafIsoDivisorialSheaf`. The integral divisor
`c W - w D` replaces the `ℚ`-divisor `W - (w / c) D`.

The chart transform `MMP.Resolution.BlowupChartData.chartTransform` lives in a localization, so
the generation statement provides sections of `𝒪(U_ℓ)` mapping to it, and reads ideals on every
affine open of `U_ℓ`. The derivative identities are stated on every affine open `W ⊆ U_ℓ` over
an affine open `W' ⊆ U`, for any `g` with `π^*f = y_ℓ^m g`. In (3.75.3) the middle sum is
`∑_{i ≠ ℓ} y_i ∂g/∂y_i`; Kollár's printed `y_ℓ ∑_{i ≠ ℓ} ∂g/∂y_i` is a misprint (for
`X = 𝔸²`, `Z = {0}`, `f = x_1`, `m = 1`, `ℓ = 2` it gives `y_1 - y_2 ≠ 0 = π^*(∂f/∂x_2)`).

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 2.11, 2.13, 2.16, 2.21,
  2.22, 3.60, 3.70, 3.75
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori Topology TopologicalSpace Opposite

variable {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]

/-- On an integral scheme, the generic point of an irreducible component specializes to the
generic point of `S`. -/
theorem componentGenericPoint_specializes_genericPoint (Z : irreducibleComponents S) :
    componentGenericPoint S Z ⤳ genericPoint S := by
  rw [specializes_iff_mem_closure, (isGenericPoint_componentGenericPoint S Z).def]
  exact Z.2.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _) (Set.mem_univ _)

/-- Specializing a germ at the generic point of the component back from `K(X)` recovers it. -/
theorem stalkSpecializes_componentGenericPoint_algebraMap (Z : irreducibleComponents S)
    (a : S.presheaf.stalk (componentGenericPoint S Z)) :
    S.presheaf.stalkSpecializes (componentGenericPoint_specializes_genericPoint Z)
      (algebraMap (S.presheaf.stalk (componentGenericPoint S Z)) S.functionField a) = a := by
  change (S.presheaf.stalkSpecializes _) ((S.presheaf.stalkSpecializes _) a) = a
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Moving a rational function to the generic point of the component and back is the
identity. -/
theorem stalkSpecializes_stalkSpecializes_genericPoint (Z : irreducibleComponents S)
    (c : S.functionField) :
    (S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes (Set.mem_univ _) :
      genericPoint S ⤳ componentGenericPoint S Z))
      (S.presheaf.stalkSpecializes (componentGenericPoint_specializes_genericPoint Z) c) = c := by
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The embedding of `K(X)` into the rational functions `MMP.Mori.RationalFunctions S`, the
product of the function fields of the irreducible components. -/
noncomputable def functionFieldToRationalFunctions : S.functionField →+* RationalFunctions S :=
  Pi.ringHom fun Z =>
    (S.presheaf.stalkSpecializes (componentGenericPoint_specializes_genericPoint Z)).hom

/-- The component at `Z` of the image of `c ∈ K(X)` in `RationalFunctions S` is `c`. -/
@[simp]
theorem evalFF_functionFieldToRationalFunctions (Z : irreducibleComponents S)
    (c : S.functionField) :
    MMP.Threefold.Mori.Helpers.evalFF Z (functionFieldToRationalFunctions c) = c :=
  stalkSpecializes_stalkSpecializes_genericPoint Z c

/-- On a normal integral Noetherian scheme the Weil divisor of a Cartier divisor is Cartier. -/
theorem IsWeilDivisorOfCartier.isCartier [IsNormal S] [CompactSpace S]
    {D : S.CartierDivisor} {D' : Divisor S}
    (h : IsWeilDivisorOfCartier D D') : D'.IsCartier := by
  intro x
  obtain ⟨f, U, hxU, g, hg, rfl⟩ := exists_isLocalEquationAt D x
  set c := totalQuotientStalkToFunctionField (genericPoint S)
    (S.totalQuotientSheaf.presheaf.germ U (genericPoint S)
      ((genericPoint_spec S).mem_open_set_iff U.isOpen |>.mpr ⟨x, Set.mem_univ _, hxU⟩)
      (g : _)) with hc
  have hc0 : c ≠ 0 :=
    totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt ⟨U, _, g, hg, rfl⟩
  refine ⟨U, hxU, Units.map functionFieldToRationalFunctions.toMonoidHom (Units.mk0 c hc0),
    fun E hE => ?_⟩
  have hη := genericPoint_mem_of_support_inter_nonempty E hE
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  change _ = S.ord (MMP.Threefold.Mori.Helpers.evalFF E.component
    (functionFieldToRationalFunctions c)) _
  rw [evalFF_functionFieldToRationalFunctions,
    ← ord_eq_coeff_of_isLocalEquationAt h E rfl ⟨U, hη, g, hg, rfl⟩, hc,
    ← totalQuotientStalkToFunctionField_stalkSpecializes
      ((genericPoint_spec S).specializes (Set.mem_univ (MMP.Mori.PrimeDivisor.genericPoint E))),
    TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- The value in `K(X)` of a section of `𝓜_X` is the same at every point. -/
theorem totalQuotientStalkToFunctionField_germ_eq {V : S.Opens}
    (σ : S.totalQuotientSheaf.obj.obj (op V)) {x y : S} (hx : x ∈ V) (hy : y ∈ V) :
    totalQuotientStalkToFunctionField x (S.totalQuotientSheaf.presheaf.germ V x hx σ) =
      totalQuotientStalkToFunctionField y (S.totalQuotientSheaf.presheaf.germ V y hy σ) := by
  have hg : genericPoint S ∈ V := (genericPoint_spec S).mem_open_set_iff V.isOpen |>.mpr
    ⟨x, Set.mem_univ _, hx⟩
  have key : ∀ z (hz : z ∈ V), totalQuotientStalkToFunctionField z
      (S.totalQuotientSheaf.presheaf.germ V z hz σ) = totalQuotientStalkToFunctionField
        (genericPoint S) (S.totalQuotientSheaf.presheaf.germ V (genericPoint S) hg σ) := by
    intro z hz
    rw [← totalQuotientStalkToFunctionField_stalkSpecializes
      ((genericPoint_spec S).specializes (Set.mem_univ z)),
      TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [key x hx, key y hy]

/-- Every rational function is a section of `𝓜_X` over every open. -/
theorem exists_totalQuotient_section (V : S.Opens) (c : S.functionField) :
    ∃ σ : S.totalQuotientSheaf.obj.obj (op V), ∀ (x : S) (hx : x ∈ V),
      totalQuotientStalkToFunctionField x (S.totalQuotientSheaf.presheaf.germ V x hx σ) = c := by
  have hloc : ∀ x : V, ∃ (W : S.Opens) (_ : W ≤ V) (_ : (x : S) ∈ W)
      (s : S.totalQuotientSheaf.obj.obj (op W)), ∀ (y : S) (hy : y ∈ W),
        totalQuotientStalkToFunctionField y (S.totalQuotientSheaf.presheaf.germ W y hy s) = c := by
    intro x
    obtain ⟨m, hm⟩ := (totalQuotientStalkToFunctionField_bijective (x : S)).2 c
    obtain ⟨W, hxW, s, rfl⟩ := S.totalQuotientSheaf.presheaf.germ_exist m
    refine ⟨W ⊓ V, inf_le_right, ⟨hxW, x.2⟩,
      S.totalQuotientSheaf.obj.map (homOfLE inf_le_left).op s, fun y hy => ?_⟩
    rw [TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf, ← hm]
    exact totalQuotientStalkToFunctionField_germ_eq s _ _
  choose W hWV hxW s hs using hloc
  have hcover : V ≤ iSup W := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩
  have hc : TopCat.Presheaf.IsCompatible S.totalQuotientSheaf.obj W s := by
    intro i j
    refine TopCat.Presheaf.section_ext S.totalQuotientSheaf _ _ _ fun z hz => ?_
    apply (totalQuotientStalkToFunctionField_bijective z).1
    rw [TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf,
      TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf, hs, hs]
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.totalQuotientSheaf W V
    (fun x => homOfLE (hWV x)) hcover s hc
  refine ⟨σ, fun x hx => ?_⟩
  have := hs ⟨x, hx⟩ x (hxW _)
  rw [← hσ ⟨x, hx⟩, TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf] at this
  exact this

/-- A section of `𝓜_X` over `V`, read in the sheaf `MMP.Mori.rationalFunctionsPresheaf` of
rational functions: its value in `K(X)`, at the generic point of each component meeting `V`. -/
noncomputable def totalQuotientToRationalFunctions (V : S.Opens)
    (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    ToType ((MMP.Mori.rationalFunctionsPresheaf S).obj (op V)) :=
  fun Z => S.presheaf.stalkSpecializes (componentGenericPoint_specializes_genericPoint Z.1)
    (totalQuotientStalkToFunctionField _ (S.totalQuotientSheaf.presheaf.germ V _ Z.2 σ))

/-- `totalQuotientToRationalFunctions V` is additive. -/
@[simp]
theorem totalQuotientToRationalFunctions_add (V : S.Opens)
    (σ τ : S.totalQuotientSheaf.obj.obj (op V)) :
    totalQuotientToRationalFunctions V (σ + τ) =
      totalQuotientToRationalFunctions V σ + totalQuotientToRationalFunctions V τ := by
  funext Z
  simp only [totalQuotientToRationalFunctions, map_add]
  rfl

/-- `totalQuotientToRationalFunctions V` commutes with the action of `Γ(S, V)`. -/
@[simp]
theorem totalQuotientToRationalFunctions_smul [IsNormal S] (V : S.Opens) (r : Γ(S, V))
    (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    totalQuotientToRationalFunctions V (r • σ) = r • totalQuotientToRationalFunctions V σ := by
  funext Z
  rw [MMP.Mori.rationalFunctions_smul_apply]
  simp only [totalQuotientToRationalFunctions, smul_totalQuotient_def, map_mul,
    germ_toTotalQuotient, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
    stalkSpecializes_componentGenericPoint_algebraMap]

/-- `totalQuotientToRationalFunctions` commutes with restriction along `W ≤ V`. -/
@[simp]
theorem totalQuotientToRationalFunctions_map {V W : S.Opens} (i : W ⟶ V)
    (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    totalQuotientToRationalFunctions W (S.totalQuotientSheaf.obj.map i.op σ) =
      (MMP.Mori.rationalFunctionsPresheaf S).map i.op (totalQuotientToRationalFunctions V σ) := by
  funext Z
  rw [MMP.Mori.rationalFunctionsPresheaf_map_apply]
  simp only [totalQuotientToRationalFunctions]
  rw [TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf]

/-- The valuation along a prime divisor `E` of the `E`-component of a unit `ψ` of
`RationalFunctions S` is `exp (E.ord ψ)`. -/
theorem valuation_component_eq_exp_ord [IsNormal S] (E : MMP.Mori.PrimeDivisor S)
    (ψ : (MMP.Mori.RationalFunctions S)ˣ) :
    E.valuation (MMP.Mori.RationalFunctions.component S E.component ψ) =
      WithZero.exp (E.ord ψ) := by
  rw [MMP.Mori.PrimeDivisor.ord, MMP.Mori.PrimeDivisor.ordHom]
  change _ = ((WithZero.unitsWithZeroEquiv (Units.map E.valuation.toMonoidHom
    (Units.map (MMP.Mori.RationalFunctions.component S E.component).toMonoidHom ψ)) :
      Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

/-- If `D'` is the Weil divisor of `D`, a section of `𝓜_X` over `V` is a section of `𝒪_X(D)`
exactly when, read as a rational function, it is a section of the divisorial sheaf of `D'`. -/
theorem IsWeilDivisorOfCartier.mem_lineBundleSections_iff_isDivisorialSection [IsNormal S]
    {D : S.CartierDivisor} {D' : Divisor S} (h : IsWeilDivisorOfCartier D D')
    (V : S.Opens) (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    σ ∈ lineBundleSections D V ↔
      D'.IsDivisorialSection V (totalQuotientToRationalFunctions V σ) := by
  by_cases hV : genericPoint S ∈ V
  · set c := totalQuotientStalkToFunctionField (genericPoint S)
      (S.totalQuotientSheaf.presheaf.germ V (genericPoint S) hV σ) with hc
    have hT : ∀ (x : S) (hx : x ∈ V), totalQuotientStalkToFunctionField x
        (S.totalQuotientSheaf.presheaf.germ V x hx σ) = c :=
      fun x hx => totalQuotientStalkToFunctionField_germ_eq σ hx hV
    have hrat : ∀ Z, totalQuotientToRationalFunctions V σ Z =
        S.presheaf.stalkSpecializes (componentGenericPoint_specializes_genericPoint Z.1) c := by
      intro Z
      simp only [totalQuotientToRationalFunctions, hT]
    by_cases hc0 : c = 0
    · constructor
      · intro _ E hE
        rw [hrat, hc0, map_zero]
        exact MMP.Mori.PrimeDivisor.OrdGE.zero _
      · intro _
        change ∀ (x : S) (hx : x ∈ V) (f : S.totalQuotientSheaf.presheaf.stalk x),
          IsLocalEquationAt D x f → _ ∈ _
        intro x hx f _
        have : S.totalQuotientSheaf.presheaf.germ V x hx σ = 0 :=
          (totalQuotientStalkToFunctionField_bijective x).1
            (by rw [hT, hc0, map_zero])
        rw [this, zero_mul]
        exact zero_mem _
    · haveI : Nonempty V := ⟨⟨_, hV⟩⟩
      rw [mem_lineBundleSections_iff_forall_zero_le_ord_add h V hc0 σ hT]
      unfold MMP.Mori.Divisor.IsDivisorialSection
      refine forall_congr' fun E => forall_congr' fun hE => ?_
      set ψ := Units.map functionFieldToRationalFunctions.toMonoidHom (Units.mk0 c hc0)
      have hv := valuation_component_eq_exp_ord E ψ
      rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at hv
      have hev : MMP.Threefold.Mori.Helpers.evalFF E.component (ψ : MMP.Mori.RationalFunctions S)
          = c := evalFF_functionFieldToRationalFunctions E.component c
      rw [hev] at hv
      have hne : MMP.Mori.RationalFunctions.component S E.component ψ ≠ 0 :=
        (ψ.isUnit.map (MMP.Mori.RationalFunctions.component S E.component)).ne_zero
      have hcomp : S.presheaf.stalkSpecializes
          (componentGenericPoint_specializes_genericPoint E.component) c =
            MMP.Mori.RationalFunctions.component S E.component ψ := rfl
      rw [hrat ⟨E.component, _⟩, hcomp]
      unfold MMP.Mori.PrimeDivisor.OrdGE
      rw [hv, WithZero.exp_le_exp]
      simp only [hne, false_or]
      omega
  · have hempty : ∀ x, x ∉ V := fun x hx =>
      hV ((genericPoint_spec S).mem_open_set_iff V.isOpen |>.mpr ⟨x, Set.mem_univ _, hx⟩)
    constructor
    · rintro - E ⟨y, -, hy⟩
      exact absurd hy (hempty y)
    · intro _
      change ∀ (x : S) (hx : x ∈ V) (f : S.totalQuotientSheaf.presheaf.stalk x),
        IsLocalEquationAt D x f → _ ∈ _
      intro x hx
      exact absurd hx (hempty x)

/-- On a normal integral scheme, reading sections of `𝓜_X` as rational functions is bijective. -/
theorem bijective_totalQuotientToRationalFunctions [IsNormal S] (V : S.Opens) :
    Function.Bijective (totalQuotientToRationalFunctions (S := S) V) := by
  constructor
  · intro σ τ hστ
    refine TopCat.Presheaf.section_ext S.totalQuotientSheaf V σ τ fun x hx => ?_
    obtain ⟨Z, hxZ⟩ := MMP.Mori.exists_mem_irreducibleComponents x
    have hZV : componentGenericPoint S Z ∈ V :=
      (MMP.Mori.genericPoint_mem_iff Z V).mpr ⟨x, hx, hxZ⟩
    have h1 := congrArg (fun φ => S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes
      (Set.mem_univ _) : genericPoint S ⤳ componentGenericPoint S Z) (φ ⟨Z, hZV⟩)) hστ
    simp only [totalQuotientToRationalFunctions,
      stalkSpecializes_stalkSpecializes_genericPoint] at h1
    apply (totalQuotientStalkToFunctionField_bijective x).1
    rw [totalQuotientStalkToFunctionField_germ_eq σ hx hZV,
      totalQuotientStalkToFunctionField_germ_eq τ hx hZV]
    exact h1
  · intro φ
    by_cases hV : ∃ Z : irreducibleComponents S, componentGenericPoint S Z ∈ V
    · obtain ⟨Z₀, hZ₀⟩ := hV
      obtain ⟨σ, hσ⟩ := exists_totalQuotient_section V (S.presheaf.stalkSpecializes
        ((genericPoint_spec S).specializes (Set.mem_univ _) :
          genericPoint S ⤳ componentGenericPoint S Z₀) (φ ⟨Z₀, hZ₀⟩))
      refine ⟨σ, funext fun Z => ?_⟩
      have : Subsingleton (irreducibleComponents S) :=
        MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents
      obtain ⟨Z, hZ⟩ := Z
      obtain rfl : Z = Z₀ := Subsingleton.elim _ _
      simp only [totalQuotientToRationalFunctions, hσ]
      rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
        TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    · exact ⟨0, funext fun Z => absurd ⟨Z.1, Z.2⟩ hV⟩

/-- On a normal integral locally Noetherian scheme, the sheaf `𝒪_X(D)` of a Cartier divisor `D`
(inside `𝓜_X`) is isomorphic to the divisorial sheaf of its Weil divisor `D'` (inside the sheaf
of rational functions), through `totalQuotientToRationalFunctions`. -/
noncomputable def IsWeilDivisorOfCartier.sheafIsoDivisorialSheaf [IsNormal S]
    {D : S.CartierDivisor} {D' : Divisor S} (h : IsWeilDivisorOfCartier D D') :
    MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf :=
  let f : ∀ V : S.Opens, Γ(MMP.CartierDivisor.sheaf D, V) →ₗ[Γ(S, V)]
      D'.divisorialSubmodule V := fun V =>
    { toFun := fun σ => ⟨totalQuotientToRationalFunctions V (MMP.CartierDivisorSheaf.sectionVal σ),
        (mem_lineBundleSections_iff_isDivisorialSection h V (MMP.CartierDivisorSheaf.sectionVal
            σ)).1 (MMP.CartierDivisor.sectionVal_mem_lineBundleSections σ)⟩
      map_add' := fun σ τ => Subtype.ext (totalQuotientToRationalFunctions_add V
          (MMP.CartierDivisorSheaf.sectionVal σ) (MMP.CartierDivisorSheaf.sectionVal τ))
      map_smul' := fun r σ => Subtype.ext (totalQuotientToRationalFunctions_smul V r
          (MMP.CartierDivisorSheaf.sectionVal σ)) }
  have hf : ∀ V, Function.Bijective (f V) := by
    intro V
    constructor
    · intro σ τ hστ
      exact MMP.CartierDivisorSheaf.sectionVal_injective
        ((bijective_totalQuotientToRationalFunctions V).1 (congrArg Subtype.val hστ))
    · intro φ
      obtain ⟨σ, hσ⟩ := (bijective_totalQuotientToRationalFunctions V).2 φ.1
      exact ⟨MMP.CartierDivisor.sectionOfMem
          ((mem_lineBundleSections_iff_isDivisorialSection h V σ).2 (hσ ▸ φ.2)),
        Subtype.ext hσ⟩
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective (f V.unop) (hf V.unop)).toModuleIso)
      (fun V W i => by
        ext σ
        exact Subtype.ext (totalQuotientToRationalFunctions_map i.unop
            (MMP.CartierDivisorSheaf.sectionVal σ))))

/-- On a normal integral locally Noetherian scheme, the sheaf `𝒪_X(D)` of a Cartier divisor is
isomorphic to the divisorial sheaf of its Weil divisor. -/
theorem IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf [IsNormal S]
    {D : S.CartierDivisor} {D' : Divisor S} (h : IsWeilDivisorOfCartier D D') :
    Nonempty (MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf) :=
  ⟨h.sheafIsoDivisorialSheaf⟩

end MMP.Intersection

namespace MMP.Resolution

section Surfaces

open MMP.Mori Topology TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A closed subset of a quasi-sober space all of whose points are closed has dimension at most
zero. -/
private lemma topologicalKrullDim_le_zero_of_forall_isClosed {T : Type*} [TopologicalSpace T]
    [QuasiSober T] {F : Set T} (hF : IsClosed F) (h : ∀ a ∈ F, IsClosed ({a} : Set T)) :
    topologicalKrullDim F ≤ 0 := by
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun Z Y hZY => ?_
  have hYirr : IsIrreducible (((↑) : F → T) '' (Y : Set F)) :=
    Y.2.image _ continuous_subtype_val.continuousOn
  have hYcl : IsClosed (((↑) : F → T) '' (Y : Set F)) :=
    hF.isClosedMap_subtype_val _ Y.3
  obtain ⟨η, hη⟩ := QuasiSober.sober hYirr hYcl
  obtain ⟨⟨η', hηF⟩, -, rfl⟩ := hη.mem
  have hsing : ((↑) : F → T) '' (Y : Set F) = {η'} := by
    rw [← hη.def, (h η' hηF).closure_eq]
  obtain ⟨z, hz⟩ := Z.2.nonempty
  intro y hy
  have hy' : (y : T) = η' := by
    have : (y : T) ∈ ((↑) : F → T) '' (Y : Set F) := ⟨y, hy, rfl⟩
    rwa [hsing] at this
  have hz' : (z : T) = η' := by
    have : (z : T) ∈ ((↑) : F → T) '' (Y : Set F) := ⟨z, hZY hz, rfl⟩
    rwa [hsing] at this
  rwa [show y = z from Subtype.ext (hy'.trans hz'.symm)]

/-- A fibre of dimension at most zero of a quasi-compact morphism locally of finite type is
finite. -/
private lemma finite_preimage_singleton_of_topologicalKrullDim_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) (h : topologicalKrullDim (f ⁻¹' {y}) ≤ 0) :
    (f ⁻¹' {y}).Finite := by
  have h' : topologicalKrullDim (f.fiber y) ≤ 0 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph]
    exact h
  have : IsLocallyNoetherian (CategoryTheory.Limits.pullback f (Y.fromSpecResidueField y)) :=
    LocallyOfFiniteType.isLocallyNoetherian (CategoryTheory.Limits.pullback.snd _ _)
  have : IsLocallyNoetherian (f.fiber y) := this
  have : IsLocallyArtinian (f.fiber y) := IsLocallyArtinian.of_topologicalKrullDim_le_zero h'
  have : DiscreteTopology (f.fiber y) :=
    (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mp inferInstance).2
  have : CompactSpace (f.fiber y) := inferInstance
  have : Finite (f.fiber y) := finite_of_compact_of_discrete
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (f.fiberHomeo y).toEquiv)

/-- The closure of a point `a` of an integral scheme `S` of dimension two which is neither closed
nor the generic point is a curve: its reduced closed subscheme has dimension one. -/
lemma topologicalKrullDim_curveSubschemeAt_eq_one {S : Scheme.{u}} [IsIntegral S]
    [CompactSpace S] (hSdim : topologicalKrullDim S = 2) {a : S} (hgen : a ≠ genericPoint S)
    (hna : ¬ IsClosed ({a} : Set S)) : topologicalKrullDim (curveSubschemeAt a) = 1 := by
  set W := curveSubschemeAt a
  set ι := curveSubschemeAtι a
  letI : PartialOrder S := specializationOrder S
  letI : PartialOrder W := specializationOrder W
  have : IsIntegral W :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have hrange : Set.range ι = closure ({a} : Set S) := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hind : IsInducing ι := ι.isClosedEmbedding.isInducing
  have hspec : ∀ p q : W, p ⤳ q ↔ ι p ⤳ ι q := fun p q => hind.specializes_iff.symm
  have hle : ∀ p q : W, p ≤ q ↔ ι p ≤ ι q := fun p q => hspec q p
  have hmono : StrictMono ι := fun p q hpq =>
    lt_of_le_not_ge ((hle p q).mp hpq.le) fun h => hpq.not_ge ((hle q p).mpr h)
  obtain ⟨a', ha'⟩ : a ∈ Set.range ι := hrange ▸ subset_closure rfl
  have hle_a : ∀ p : W, ι p ≤ a := fun p =>
    specializes_iff_mem_closure.mpr (hrange ▸ ⟨p, rfl⟩)
  have hlt : a < genericPoint S :=
    lt_of_le_of_ne ((genericPoint_spec S).specializes (Set.mem_univ a)) hgen
  have hS2 : Order.krullDim S = 2 := by
    rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hSdim]
  have hηle : (Order.height (genericPoint S) : WithBot ℕ∞) ≤ 2 :=
    hS2 ▸ Order.height_le_krullDim _
  have ha1 : Order.height a ≤ 1 := by
    have h1 := Order.height_add_one_le hlt
    have h2 : Order.height (genericPoint S) ≤ 2 := WithBot.coe_le_coe.mp hηle
    have h3 : Order.height a + 1 ≤ 1 + 1 := h1.trans h2
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h3
  refine le_antisymm ?_ ?_
  · rw [← Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim,
      Order.krullDim_eq_iSup_height_of_nonempty]
    refine WithBot.coe_le_coe.mpr (iSup_le fun p => ?_)
    exact (Order.height_le_height_apply_of_strictMono ι hmono p).trans
      ((Order.height_mono (hle_a p)).trans ha1)
  · rw [← Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim]
    refine Order.one_le_krullDim_iff.mpr ?_
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace ι
    obtain ⟨b, -, hb⟩ := (isClosed_univ (X := W)).exists_closed_singleton Set.univ_nonempty
    refine ⟨b, a', lt_of_le_of_ne ?_ ?_⟩
    · exact (hle b a').mpr (by rw [ha']; exact hle_a b)
    · rintro rfl
      apply hna
      rw [← ha', ← Set.image_singleton]
      exact ι.isClosedEmbedding.isClosedMap _ hb

/-- Let `g : S ⟶ X` be proper and `X` locally of finite type over `k`. The reduced closed
subscheme on the closure of a point `a` of `S` which `g` maps to a closed point `x` is proper over
`k`: it maps to the reduced point `{x}`, which is finite over `k`. -/
lemma isProper_curveSubschemeAtι_comp {k : Type u} [Field k] {S X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (g : S ⟶ X) [IsProper g] {x : X}
    (hx : IsClosed ({x} : Set X)) {a : S} (ha : closure ({a} : Set S) ⊆ g ⁻¹' {x}) :
    IsProper (curveSubschemeAtι a ≫ g ≫ sX) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({a} : Set S))
  set J := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have H : J ≤ I.map g := by
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    intro y hy
    exact closure_minimal (Set.image_subset_iff.mpr ha) hx hy
  have hφ := Scheme.IdealSheafData.subschemeMap_subschemeι I J g H
  have : IsProper (Scheme.IdealSheafData.subschemeMap I J g H ≫ J.subschemeι) := by
    rw [hφ]
    exact inferInstanceAs (IsProper (I.subschemeι ≫ g))
  have : IsProper (Scheme.IdealSheafData.subschemeMap I J g H) :=
    IsProper.of_comp _ J.subschemeι
  have : Subsingleton J.subscheme := by
    refine ⟨fun p q => J.subschemeι.isClosedEmbedding.injective ?_⟩
    have hr : Set.range J.subschemeι = {x} := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hp : J.subschemeι p ∈ Set.range J.subschemeι := ⟨p, rfl⟩
    have hq : J.subschemeι q ∈ Set.range J.subschemeι := ⟨q, rfl⟩
    rw [hr] at hp hq
    exact hp.trans hq.symm
  have : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsFinite (J.subschemeι ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  change IsProper (I.subschemeι ≫ g ≫ sX)
  rw [← Category.assoc, ← hφ, Category.assoc]
  infer_instance

/-- The generic point of an integral scheme of dimension two is not closed. -/
private lemma not_isClosed_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (hXdim : topologicalKrullDim X = 2) : ¬ IsClosed ({genericPoint X} : Set X) := by
  intro hc
  have : Subsingleton X := Set.subsingleton_univ_iff.mp <| by
    rw [← (genericPoint_spec X).def, hc.closure_eq]; exact Set.subsingleton_singleton
  have h0 := topologicalKrullDim_zero_of_discreteTopology X
  rw [hXdim] at h0
  exact absurd h0 (by decide)

/-- Let `g : S ⟶ X` be a proper birational morphism of integral surfaces over `k` contracting no
integral projective curve of `S` to a point. Then every closed fibre of `g` is finite: otherwise
it contains a non-closed point `a`, whose closure is a projective curve contracted by `g`. -/
private lemma finite_preimage_singleton_of_isClosed {k : Type u} [Field k] {S X : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} [IsIntegral S] [CompactSpace S]
    [IsIntegral X] [LocallyOfFiniteType sX] (hSdim : topologicalKrullDim S = 2)
    (hXdim : topologicalKrullDim X = 2) (g : S ⟶ X) [IsProper g] (hb : IsBirational g)
    (hg : g ≫ sX = sS)
    (hexc : ∀ C : ProperCurve sS, ¬ MMP.Resolution.IsContractedProjectiveCurve sS g C)
    {x : X} (hx : IsClosed ({x} : Set X)) : (g ⁻¹' {x}).Finite := by
  have hF : IsClosed (g ⁻¹' {x}) := hx.preimage g.continuous
  refine finite_preimage_singleton_of_topologicalKrullDim_le g x ?_
  by_contra hdim
  obtain ⟨a, haF, hna⟩ : ∃ a ∈ g ⁻¹' {x}, ¬ IsClosed ({a} : Set S) := by
    by_contra! h
    exact hdim (topologicalKrullDim_le_zero_of_forall_isClosed hF h)
  have hclF : closure ({a} : Set S) ⊆ g ⁻¹' {x} :=
    closure_minimal (Set.singleton_subset_iff.mpr haF) hF
  have hgen : a ≠ genericPoint S := by
    rintro rfl
    have heq : g (genericPoint S) = genericPoint X := by
      simpa [genericPoints_eq_singleton] using hb.bijOn.1 (by simp [genericPoints_eq_singleton])
    rw [← (haF : g (genericPoint S) = x), heq] at hx
    exact not_isClosed_genericPoint hXdim hx
  have hprop : IsProper (curveSubschemeAtι a ≫ sS) := by
    rw [← hg]; exact isProper_curveSubschemeAtι_comp sX g hx hclF
  let C : ProperCurve sS := ⟨a, topologicalKrullDim_curveSubschemeAt_eq_one hSdim hgen hna, hprop⟩
  refine hexc C ⟨?_, fun y hy => (hclF hy).trans (hclF (subset_closure rfl)).symm⟩
  have : IsIntegral C.scheme := MMP.Resolution.isIntegral_properCurve_scheme C
  exact isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral _ C.dim_eq, hprop⟩

/-- **A projective birational morphism of surfaces with no exceptional curve is an isomorphism.**
Let `g : S ⟶ X` be a projective birational morphism of surfaces over `k` with `X` normal, such
that no integral projective curve `C ⊆ S` has `g(C)` a point. Then `g` is an isomorphism. -/
@[mmp "lem_kr2a_birational_no_exceptional_curve_is_isomorphism"]
public theorem isIso_of_forall_not_isContractedProjectiveCurve {k : Type u} [Field k]
    {S X : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    (hS : AlgebraicGeometry.IsVariety k sS) (hSdim : topologicalKrullDim S = 2)
    (hX : AlgebraicGeometry.IsVariety k sX) (hXdim : topologicalKrullDim X = 2) [IsNormal X]
    (g : S ⟶ X) (hg : g ≫ sX = sS) (hproj : IsProjectiveMorphism g)
    (hbir : IsBirationalMorphism g)
    (hexc : ∀ C : ProperCurve sS, ¬ IsContractedProjectiveCurve sS g C) :
    IsIso g := by
  have := hS.toIsIntegral
  have := hX.toIsIntegral
  have := hS.toQuasiCompact
  have := hX.toQuasiCompact
  have := hX.toLocallyOfFiniteType
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsProper g := isProper_of_isProjectiveMorphism g hproj
  have hb : IsBirational g := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbir
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso g hb).1 this
  have htop : (⟨MMP.Resolution.Bridges.finiteFibreLocus g, hU⟩ : X.Opens) = ⊤ := by
    refine SetLike.coe_injective (Set.eq_univ_of_forall fun y => ?_)
    by_contra hy
    obtain ⟨x, hx, hxc⟩ := hU.isClosed_compl.exists_closed_singleton ⟨y, hy⟩
    exact hx (finite_preimage_singleton_of_isClosed hSdim hXdim g hb hg hexc hxc)
  exact (isBiregular_top_iff g).mp (htop ▸ hiso)

/-- The Weil divisor `[D]` of a Cartier divisor, computed by
`AlgebraicGeometry.cartierWeilDivisor`, is a Weil divisor of `D` in the sense of
`MMP.Intersection.IsWeilDivisorOfCartier`. -/
private lemma isWeilDivisorOfCartier_cartierWeilDivisor {S : Scheme.{u}} [IsIntegral S]
    [IsNoetherian S] (D : S.CartierDivisor) :
    MMP.Intersection.IsWeilDivisorOfCartier D (weilDivisorEquivFinsupp (cartierWeilDivisor D)) := by
  intro P
  have hcoh : Order.coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  haveI : Ring.KrullDimLE 1
      (S.presheaf.stalk (MMP.Intersection.primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le hcoh.le
  obtain ⟨N, hN⟩ :=
    MMP.Intersection.exists_isOrderAlong D (MMP.Intersection.primeDivisorSubvariety P)
  convert hN using 1
  have hN' := hN
  unfold MMP.Intersection.IsOrderAlong at hN'
  dsimp only [MMP.Intersection.primeDivisorSubvariety_genericPoint] at hN'
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, rfl⟩ := hN'
  change cartierMultiplicity D (MMP.Mori.PrimeDivisor.genericPoint P) = _
  rw [MMP.Intersection.cartierMultiplicity_eq_ord_of_isLocalEquationAt hg]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (S.presheaf.stalk _) S.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (S.presheaf.stalk _) S.functionField b =
      algebraMap (S.presheaf.stalk _) S.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rw [mul_comm]
    exact this
  have hTg := MMP.Intersection.totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := S.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a ha0, ord_algebraMap_stalk _ hcoh b hb0] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- If `𝒪_X(D)` is the divisorial sheaf of a Cartier Weil divisor `D'`, then the intersection
number of `D` with a projective curve is the degree of `D'` along it. -/
private lemma cartierCurveIntersection_eq_degreeOn {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsNormal S] [IsLocallyNoetherian S] [QuasiCompact sS]
    {D : S.CartierDivisor} {D' : Divisor S} (hD' : D'.IsCartier)
    (e : MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf) (C : ProperCurve sS)
    (hC : IsProjectiveMorphism (C.ι ≫ sS)) :
    cartierCurveIntersection D C = D'.degreeOn k sS C.ι C.dim_le hD' := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sS
  haveI hinv := hD'.isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule S (MMP.CartierDivisor.sheaf D) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hinv
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf D) := this
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf := hinv
  have hcurve : AlgebraicGeometry.IsCurve k (C.ι ≫ sS) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  have : AlgebraicGeometry.IsProjectiveVariety k (C.ι ≫ sS) :=
    { toIsVariety := hcurve.toIsVariety
      isProjective := hC }
  have : Stacks.Ample.IsInvertibleModule C.scheme
      ((Scheme.Modules.pullback C.ι).obj (MMP.CartierDivisor.sheaf D)) :=
    MMP.Mori.isInvertible_pullback_obj C.ι _
  unfold cartierCurveIntersection lineBundleCurveIntersection
  rw [MMP.Resolution.degree_eq_invertibleCurveDegree (C.ι ≫ sS) _ C.dim_le,
    ← MMP.Mori.degreeOn_eq_invertibleCurveDegree, MMP.Mori.degreeOn_eq_of_iso k sS C.ι C.dim_le e]
  rfl

open Stacks.HQuasiProjectiveDimensionOne in
/-- A prime divisor `P` of a surface whose image under `g` has smaller dimension is a
`g`-exceptional curve: some contracted projective curve has the generic point of `P`. -/
lemma exists_isContractedProjectiveCurve_of_isExceptional {k : Type u} [Field k]
    {S X : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    (hS : AlgebraicGeometry.IsVariety k sS) (hSdim : topologicalKrullDim S = 2)
    (hX : AlgebraicGeometry.IsVariety k sX) [IsIntegral S]
    (g : S ⟶ X) (hg : g ≫ sX = sS) (hproj : IsProjectiveMorphism g)
    (P : AlgebraicGeometry.PrimeDivisor S)
    (hP : topologicalKrullDim (closure (g.base '' P.support)) < topologicalKrullDim P.support) :
    ∃ C : ProperCurve sS, C.point = P.genericPoint ∧ IsContractedProjectiveCurve sS g C := by
  have : QuasiCompact sS := hS.toQuasiCompact
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : QuasiCompact sX := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsProper g := isProper_of_isProjectiveMorphism g hproj
  set a := P.genericPoint with ha
  have hsupp : P.support = closure ({a} : Set S) :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  have haP : a ∈ P.support := by rw [hsupp]; exact subset_closure rfl
  -- the closure of `g(P)` is nonempty and irreducible
  set F : Set X := closure (g.base '' P.support) with hF
  have hyF : g a ∈ F := subset_closure ⟨a, haP, rfl⟩
  have hFirr : IsIrreducible F := by
    rw [hF, hsupp]
    exact (isIrreducible_singleton.closure.image _ g.continuous.continuousOn).closure
  have hFne : 0 ≤ topologicalKrullDim F := by
    have : Nonempty (IrreducibleCloseds F) := ⟨⟨closure {⟨_, hyF⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  -- `a` is not closed, and not the generic point
  have hna : ¬ IsClosed ({a} : Set S) := by
    intro hcl
    have h1 : P.support = {a} := by rw [hsupp, hcl.closure_eq]
    have h2 : topologicalKrullDim P.support ≤ 0 := by
      rw [h1]; exact topologicalKrullDim_zero_of_discreteTopology _
    have := hP.trans_le h2
    exact absurd hFne (not_le.2 this)
  have hgen : a ≠ genericPoint S := by
    intro h
    have h1 : Order.coheight a = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
    rw [h, Order.coheight_eq_zero.2] at h1
    · exact absurd h1 (by decide)
    · exact fun b _ => genericPoint_specializes b
  have hdim1 := topologicalKrullDim_curveSubschemeAt_eq_one hSdim hgen hna
  -- `P` has dimension one
  have hPdim : topologicalKrullDim P.support = 1 := by
    have hrange : Set.range (curveSubschemeAtι a) = P.support := by
      rw [hsupp]
      change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    let e := ((curveSubschemeAtι a).isClosedEmbedding.isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr hrange)
    rw [← hdim1]
    exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm
  -- `g(a)` is a closed point
  have hx : IsClosed ({g a} : Set X) := by
    by_contra hnc
    obtain ⟨z, hzF, hz⟩ := isClosed_closure.exists_closed_singleton ⟨_, hyF⟩
    have hzy : z ≠ g a := fun h => hnc (h ▸ hz)
    have : IrreducibleSpace F := Subtype.irreducibleSpace hFirr
    have hzc : IsClosed ({⟨z, hzF⟩} : Set F) := by
      have : ({⟨z, hzF⟩} : Set F) = Subtype.val ⁻¹' {z} := by
        ext ⟨p, hp⟩; simp [Subtype.ext_iff]
      rw [this]; exact hz.preimage continuous_subtype_val
    have h1 : 1 ≤ topologicalKrullDim F := by
      refine Order.one_le_krullDim_iff.mpr ⟨⟨{⟨z, hzF⟩}, isIrreducible_singleton, hzc⟩,
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _,
        isClosed_univ⟩, ?_⟩
      refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) fun h => hzy ?_
      have : (⟨g a, hyF⟩ : F) ∈ ({⟨z, hzF⟩} : Set F) := by
        change _ ∈ (⟨{⟨z, hzF⟩}, isIrreducible_singleton, hzc⟩ : IrreducibleCloseds F)
        rw [h]; exact Set.mem_univ _
      exact (congrArg Subtype.val (Set.mem_singleton_iff.1 this)).symm
    have := hP.trans_le hPdim.le
    have h3 : topologicalKrullDim F < 1 := this
    exact absurd h1 (not_le.2 h3)
  have hfib : closure ({a} : Set S) ⊆ g.base ⁻¹' {g a} := by
    intro b hb
    have := image_closure_subset_closure_image g.continuous ⟨b, hb, rfl⟩
    rw [Set.image_singleton, hx.closure_eq] at this
    exact this
  have hprop : IsProper (curveSubschemeAtι a ≫ sS) := by
    rw [← hg]; exact isProper_curveSubschemeAtι_comp sX g hx hfib
  refine ⟨⟨a, ⟨hdim1, hprop⟩⟩, rfl, ?_, fun b hb => ?_⟩
  · exact isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one _ hdim1.le
  · exact hfib hb

/-- Let `F₁, F₂, W ≥ 0` be integral finitely supported functions, `F₁` and `F₂` with disjoint
supports, and let `P₀` be a point of the support of `F₁` minimising `W P / F₁ P` there. Then
`F₁ P₀ • W - W P₀ • (F₁ - F₂)` is nonnegative and vanishes at `P₀`. -/
private lemma zero_le_smul_sub_smul_and_apply_eq_zero {α : Type*} {F₁ F₂ W : α →₀ ℤ}
    (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) (hdisj : Disjoint F₁.support F₂.support) (hW : 0 ≤ W)
    {P₀ : α} (hP₀ : P₀ ∈ F₁.support)
    (hmin : ∀ P ∈ F₁.support, (W P₀ : ℚ) / F₁ P₀ ≤ W P / F₁ P) :
    0 ≤ F₁ P₀ • W - W P₀ • (F₁ - F₂) ∧ (F₁ P₀ • W - W P₀ • (F₁ - F₂)) P₀ = 0 := by
  have hF₂0 : ∀ P ∈ F₁.support, F₂ P = 0 := fun P hP =>
    Finsupp.notMem_support_iff.1 (Finset.disjoint_left.1 hdisj hP)
  have hpos : ∀ P ∈ F₁.support, 0 < F₁ P := fun P hP =>
    lt_of_le_of_ne (hF₁ P) (Ne.symm (Finsupp.mem_support_iff.1 hP))
  refine ⟨fun P => ?_, by simp [hF₂0 P₀ hP₀, mul_comm]⟩
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hP : P ∈ F₁.support
  · have hm := hmin P hP
    rw [div_le_div_iff₀ (by exact_mod_cast hpos P₀ hP₀) (by exact_mod_cast hpos P hP)] at hm
    have hm' : W P₀ * F₁ P ≤ W P * F₁ P₀ := by exact_mod_cast hm
    rw [hF₂0 P hP]
    nlinarith
  · rw [Finsupp.notMem_support_iff.1 hP]
    have := hF₂ P
    have := hW P
    have := hW P₀
    have := hF₁ P₀
    simp only [Finsupp.coe_zero, Pi.zero_apply] at *
    nlinarith

/-- **Negativity lemma, Weil-divisor form.** Let `g : S ⟶ X` be a projective birational morphism
of surfaces over `k`, `S` normal and `X` quasi-projective, and `F₁, F₂` effective Weil divisors
on `S` without common components such that `F₁ - F₂` is Cartier, `F₁ ≠ 0` and `F₁` is
`g`-exceptional. Then some `g`-exceptional curve `C ⊆ Supp F₁` has `deg_C (F₁ - F₂) < 0`. -/
theorem exists_isContractedProjectiveCurve_degreeOn_neg {k : Type u}
    [Field k] {S X : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    (hS : AlgebraicGeometry.IsVariety k sS) (hSdim : topologicalKrullDim S = 2) [IsNormal S]
    (hX : AlgebraicGeometry.IsVariety k sX)
    (hXqp : Stacks.HProjective.IsHQuasiProjective sX)
    [IsIntegral S] [IsLocallyNoetherian S]
    (g : S ⟶ X) (hg : g ≫ sX = sS) (hproj : IsProjectiveMorphism g)
    (hbir : IsBirationalMorphism g)
    (F₁ F₂ : Divisor S) (hD' : (F₁ - F₂).IsCartier)
    (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) (hdisj : Disjoint F₁.support F₂.support) (hF₁0 : F₁ ≠ 0)
    (hexc : IsExceptionalDivisorFor g F₁) :
    ∃ C : ProperCurve sS, IsContractedProjectiveCurve sS g C ∧
      (∃ P ∈ F₁.support, C.point ∈ P.support) ∧
        (F₁ - F₂).degreeOn k sS C.ι C.dim_le hD' < 0 := by
  classical
  have : QuasiCompact sS := hS.toQuasiCompact
  have : IsIntegral X := hX.toIsIntegral
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : IsProper g := isProper_of_isProjectiveMorphism g hproj
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) sX
  -- an effective Cartier divisor `W` with `-W` relatively ample
  obtain ⟨W, hW0, hW, hamp⟩ :=
    MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism
      hS hX hXqp hproj
      (MMP.Threefold.Resolution.exists_isFinite_morphismRestrict_of_isBirationalMorphism hbir)
  -- the component `P₀` of `F₁` minimising `W P / F₁ P`
  have hne : F₁.support.Nonempty := Finsupp.support_nonempty_iff.2 hF₁0
  obtain ⟨P₀, hP₀, hmin⟩ := F₁.support.exists_min_image (fun P => (W P : ℚ) / F₁ P) hne
  set c : ℤ := F₁ P₀
  set w : ℤ := W P₀
  have hc0 : 0 < c := lt_of_le_of_ne (hF₁ P₀) (Ne.symm (Finsupp.mem_support_iff.1 hP₀))
  have hw0 : 0 ≤ w := hW0 P₀
  -- the curve `C` with generic point that of `P₀`
  obtain ⟨C, hCpt, hC⟩ :=
    exists_isContractedProjectiveCurve_of_isExceptional hS hSdim hX g hg hproj P₀ (hexc P₀ hP₀)
  refine ⟨C, hC, ⟨P₀, hP₀, ?_⟩, ?_⟩
  · rw [hCpt, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  -- `(C · W) < 0`
  have hWneg : W.degreeOn k sS C.ι C.dim_le hW < 0 := by
    have := hW.neg.isInvertibleModule_divisorialSheaf
    have hpos : 0 < (-W).degreeOn k sS C.ι C.dim_le hW.neg :=
      MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hS g _ hamp C hC.2
    rw [Divisor.degreeOn_neg' k sS C.ι C.dim_le W hW] at hpos
    linarith
  -- the effective divisor `E = c W - w (F₁ - F₂)`, not containing `C`
  set E : Divisor S := c • W + -(w • (F₁ - F₂))
  have hEc : E.IsCartier := (hW.zsmul c).add (hD'.zsmul w).neg
  obtain ⟨hE0, hEP₀⟩ := sub_eq_add_neg (c • W) (w • (F₁ - F₂)) ▸
    zero_le_smul_sub_smul_and_apply_eq_zero hF₁ hF₂ hdisj hW0 hP₀ hmin
  have hEnn : 0 ≤ E.degreeOn k sS C.ι C.dim_le hEc := by
    obtain ⟨x, hx⟩ := MMP.Threefold.Mori.exists_ι_eq_point C.point
    refine (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sS C.ι C.dim_le E _ hE0
      ⟨x, ?_⟩).1
    change curveSubschemeAtι C.point x ∉ _
    rw [hx, hCpt]
    intro hmem
    obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
    have hQP : Q = P₀ :=
      MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support Q P₀ hxQ
    subst hQP
    exact hQ hEP₀
  have hlin : E.degreeOn k sS C.ι C.dim_le hEc =
      c * W.degreeOn k sS C.ι C.dim_le hW -
        w * (F₁ - F₂).degreeOn k sS C.ι C.dim_le hD' := by
    rw [Divisor.degreeOn_add k sS C.ι C.dim_le _ _ (hW.zsmul c) (hD'.zsmul w).neg,
      Divisor.degreeOn_neg' k sS C.ι C.dim_le _ (hD'.zsmul w),
      Divisor.degreeOn_zsmul' k sS C.ι C.dim_le W hW c,
      Divisor.degreeOn_zsmul' k sS C.ι C.dim_le _ hD' w]
    ring
  exact neg_of_mul_neg_right (by nlinarith) hw0

/-- **The exceptional positive part of a Cartier divisor is negative on some curve.** Let
`g : S ⟶ X` be a projective birational morphism of normal quasi-projective surfaces over `k` and
`D` a Cartier divisor on `S` whose Weil divisor is `F₁ - F₂`, where `F₁, F₂` are effective
without common components, `F₁ ≠ 0` and `F₁` is `g`-exceptional. Then there is a `g`-exceptional
curve `C ⊆ Supp F₁` with `(D · C) < 0`. -/
@[mmp "lem_kr2a_negativity_positive_part_exceptional"]
public theorem exists_isContractedProjectiveCurve_cartierCurveIntersection_neg {k : Type u}
    [Field k] {S X : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    (hS : AlgebraicGeometry.IsVariety k sS) (hSdim : topologicalKrullDim S = 2) [IsNormal S]
    (hSqp : Stacks.HProjective.IsHQuasiProjective sS)
    (hX : AlgebraicGeometry.IsVariety k sX) (hXdim : topologicalKrullDim X = 2) [IsNormal X]
    (hXqp : Stacks.HProjective.IsHQuasiProjective sX)
    [IsIntegral S] [IsNoetherian S]
    (g : S ⟶ X) (hg : g ≫ sX = sS) (hproj : IsProjectiveMorphism g)
    (hbir : IsBirationalMorphism g)
    (D : S.CartierDivisor) (F₁ F₂ : Divisor S)
    (hD : weilDivisorEquivFinsupp (cartierWeilDivisor D) = F₁ - F₂)
    (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) (hdisj : Disjoint F₁.support F₂.support) (hF₁0 : F₁ ≠ 0)
    (hexc : IsExceptionalDivisorFor g F₁) :
    ∃ C : ProperCurve sS, IsContractedProjectiveCurve sS g C ∧
      (∃ P ∈ F₁.support, C.point ∈ P.support) ∧ cartierCurveIntersection D C < 0 := by
  have : QuasiCompact sS := hS.toQuasiCompact
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  -- the Weil divisor `F₁ - F₂` of `D` is Cartier, with the same intersection numbers
  have hWD := isWeilDivisorOfCartier_cartierWeilDivisor D
  rw [hD] at hWD
  have hD' : (F₁ - F₂).IsCartier := hWD.isCartier
  obtain ⟨C, hC, hCF, hneg⟩ := exists_isContractedProjectiveCurve_degreeOn_neg hS hSdim hX hXqp
    g hg hproj hbir F₁ F₂ hD' hF₁ hF₂ hdisj hF₁0 hexc
  refine ⟨C, hC, hCF, ?_⟩
  rwa [cartierCurveIntersection_eq_degreeOn hD' hWD.sheafIsoDivisorialSheaf C hC.1]

end Surfaces

/-- If an injective ring map `j : B → L` identifies `B` with the integral closure of `A` in `L`,
compatibly with `φ : A → B`, and `L` is finite over the fraction field of `A`, then `φ` is
integral and `B` is integrally closed. -/
private theorem isIntegral_and_isIntegrallyClosed_of_range_eq {A B K L : Type*} [CommRing A]
    [IsDomain A] [CommRing B] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (φ : A →+* B) (j : B →+* L) (hj : Function.Injective j)
    (hφ : j.comp φ = algebraMap A L)
    (hrange : Set.range j = (integralClosure A L : Set L)) :
    φ.IsIntegral ∧ IsIntegrallyClosed B := by
  have hmem : ∀ b, j b ∈ integralClosure A L := fun b => by
    rw [← SetLike.mem_coe, ← hrange]; exact ⟨b, rfl⟩
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨p, hp, hpb⟩ := hmem b
    refine ⟨p, hp, hj ?_⟩
    rw [map_zero, Polynomial.hom_eval₂, hφ]
    exact hpb
  · let e : B ≃+* integralClosure A L :=
      RingEquiv.ofBijective (j.codRestrict (integralClosure A L).toSubring hmem)
        ⟨fun x y hxy => hj (congrArg Subtype.val hxy), fun ⟨y, hy⟩ => by
          rw [← SetLike.mem_coe, ← hrange] at hy
          obtain ⟨b, rfl⟩ := hy
          exact ⟨b, rfl⟩⟩
    haveI := integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) K (L := L)
    exact IsIntegrallyClosed.of_equiv e.symm

/-- Over a nonempty affine open `Y₀`, the map `𝒪(Y₀) → 𝒪(g⁻¹ Y₀)` of a normalization in a finite
extension is integral and `𝒪(g⁻¹ Y₀)` is integrally closed. -/
private theorem isIntegral_and_isIntegrallyClosed_app
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {L : Type u} [Field L]
    [Algebra Y.functionField L] [FiniteDimensional Y.functionField L]
    {g : X ⟶ Y} {ι : X.functionField ≃+* L}
    (h : MMP.Resolution.IsNormalizationInExtension sX sY L g ι)
    (Y₀ : Y.Opens) (hY₀ : IsAffineOpen Y₀) (hne : (Y₀ : Set Y).Nonempty) :
    (g.app Y₀).hom.IsIntegral ∧ IsIntegrallyClosed Γ(X, g ⁻¹ᵁ Y₀) := by
  haveI := h.isDominant
  haveI : Nonempty Y₀ := hne.to_subtype
  have hY : genericPoint Y ∈ Y₀ :=
    ((genericPoint_spec Y).mem_open_set_iff Y₀.isOpen).mpr (by simpa using hne)
  obtain ⟨x, hx⟩ := g.denseRange.exists_mem_open Y₀.isOpen hne
  have hXne : ((g ⁻¹ᵁ Y₀ : X.Opens) : Set X).Nonempty := ⟨x, hx⟩
  haveI : Nonempty (g ⁻¹ᵁ Y₀) := hXne.to_subtype
  have hX : genericPoint X ∈ g ⁻¹ᵁ Y₀ :=
    ((genericPoint_spec X).mem_open_set_iff (g ⁻¹ᵁ Y₀).isOpen).mpr (by simpa using hXne)
  haveI := functionField_isFractionRing_of_isAffineOpen Y Y₀ hY₀
  letI : Algebra Γ(Y, Y₀) L :=
    ((algebraMap Y.functionField L).comp (Y.presheaf.germ Y₀ (genericPoint Y) hY).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, Y₀) Y.functionField L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine isIntegral_and_isIntegrallyClosed_of_range_eq (K := Y.functionField) (g.app Y₀).hom
    (ι.toRingHom.comp (X.presheaf.germ (g ⁻¹ᵁ Y₀) (genericPoint X) hX).hom)
    (ι.injective.comp (X.germToFunctionField_injective (g ⁻¹ᵁ Y₀)))
    (RingHom.ext (h.map_germ Y₀ hY hX)) (h.range_germ Y₀ hY₀ hY hX)

/-- The normalization of a variety in a finite extension is an integral morphism. -/
private theorem isIntegralHom
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {L : Type u} [Field L]
    [Algebra Y.functionField L] [FiniteDimensional Y.functionField L]
    {g : X ⟶ Y} {ι : X.functionField ≃+* L}
    (h : MMP.Resolution.IsNormalizationInExtension sX sY L g ι) : IsIntegralHom g := by
  refine (isIntegralHom_iff g).mpr ⟨h.isAffineHom, fun Y₀ hY₀ => ?_⟩
  rcases (Y₀ : Set Y).eq_empty_or_nonempty with hemp | hne
  · obtain rfl : Y₀ = ⊥ := SetLike.coe_injective hemp
    haveI : Subsingleton Γ(X, g ⁻¹ᵁ ⊥) := by rw [Scheme.Hom.preimage_bot]; infer_instance
    exact fun _ => ⟨Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  · exact (isIntegral_and_isIntegrallyClosed_app h Y₀ hY₀ hne).1

/-- A normalization `g : X ⟶ Y` of a `k`-variety `Y` in a finite extension `L ⊇ k(Y)` is a finite
surjective morphism with normal source. -/
@[mmp "lem_kr2b_normalization_in_extension_finite"]
public theorem IsNormalizationInExtension.isFinite_and_surjective_and_isNormal
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {L : Type u} [Field L]
    [Algebra Y.functionField L] [FiniteDimensional Y.functionField L]
    {g : X ⟶ Y} {ι : X.functionField ≃+* L}
    (h : IsNormalizationInExtension sX sY L g ι) :
    IsFinite g ∧ Surjective g ∧ IsNormal X := by
  haveI := h.isDominant
  haveI := h.isVariety_source
  haveI := isIntegralHom h
  haveI : LocallyOfFiniteType (g ≫ sY) := h.comp_eq ▸ inferInstance
  haveI := locallyOfFiniteType_of_comp g sY
  refine ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType g).mpr ⟨‹_›, ‹_›⟩,
    ⟨Set.range_eq_univ.mp ?_⟩, ⟨fun x => inferInstance, fun x => ?_⟩⟩
  · rw [← g.isClosedMap.isClosed_range.closure_eq, g.denseRange.closure_range]
  · obtain ⟨Y₀, hY₀, hx, -⟩ := exists_isAffineOpen_mem_and_subset
      (show g x ∈ (⊤ : Y.Opens) from trivial)
    have hU := hY₀.preimage g
    haveI : Nonempty (g ⁻¹ᵁ Y₀) := ⟨⟨x, hx⟩⟩
    haveI := (isIntegral_and_isIntegrallyClosed_app h Y₀ hY₀ ⟨g x, hx⟩).2
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : g ⁻¹ᵁ Y₀)
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    exact isIntegrallyClosed_of_isLocalization _ _
      (Ideal.primeCompl_le_nonZeroDivisors (hU.primeIdealOf ⟨x, hx⟩).asIdeal)

section DimensionZero

/-- In a space of Krull dimension at most `0`, an irreducible closed set containing a point is
the closure of that point. -/
private lemma eq_closure_singleton {X : Type*} [TopologicalSpace X]
    (hX : topologicalKrullDim X ≤ 0) {x : X} {Z : Set X} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) (hx : x ∈ Z) : Z = closure {x} :=
  have hle : (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      TopologicalSpace.IrreducibleCloseds X) ≤ ⟨Z, hZ, hZc⟩ :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) hZc
  congrArg (·.1) ((Order.krullDim_nonpos_iff_forall_isMax.mp hX _ hle).antisymm hle)

/-- In a space of Krull dimension at most `0`, specialization is equality. -/
private lemma eq_of_specializes {X : Type*} [TopologicalSpace X] [T0Space X]
    (hX : topologicalKrullDim X ≤ 0) {a b : X} (hab : a ⤳ b) : a = b :=
  (hab.antisymm (specializes_iff_closure_subset.mpr (eq_closure_singleton hX
    isIrreducible_singleton.closure isClosed_closure
    (specializes_iff_closure_subset.mp hab (subset_closure rfl))).le)).eq

/-- In a space of Krull dimension at most `0`, the closure of a point is an irreducible
component. -/
private lemma closure_singleton_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    (hX : topologicalKrullDim X ≤ 0) (x : X) : closure {x} ∈ irreducibleComponents X :=
  eq_closure_singleton hX isIrreducible_irreducibleComponent isClosed_irreducibleComponent
    mem_irreducibleComponent ▸ irreducibleComponent_mem_irreducibleComponents x

/-- On a smooth scheme of dimension at most `0` over a field, every local ring is a field. -/
private lemma maximalIdeal_stalk_eq_bot {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (hX : topologicalKrullDim X ≤ 0) (x : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  haveI : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
    krullDimLE_of_coheight_le (by
      rw [Order.coheight_eq_zero.mpr fun _ h => (eq_of_specializes hX h).le]; rfl)
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mp Ring.KrullDimLE.isField_of_isDomain

/-- The order of the unit ideal of a local ring is `0`. -/
private lemma idealOrder_top {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊤ : Ideal R) = 0 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases j with _ | j
  · rfl
  · exact absurd (hj.trans (Ideal.pow_le_self (Nat.succ_ne_zero j)))
      (by simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)

/-- On a smooth scheme of dimension at most `0` over a field, an ideal sheaf nonzero at the
generic point of every irreducible component has unit stalks: the local rings are fields and
every point is generic. -/
private lemma stalk_eq_top_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hsm : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    (hX : topologicalKrullDim X ≤ 0) {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I)
    (x : X) : IdealSheafData.stalk I x = ⊤ := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  by_contra hne
  have hle := IsLocalRing.le_maximalIdeal hne
  rw [maximalIdeal_stalk_eq_bot sX hX x, le_bot_iff] at hle
  exact hI x (closure_singleton_mem_irreducibleComponents hX x) hle

/-- **Kollár 3.70.** Let `X` be a smooth, equidimensional scheme of finite type and of
dimension `0` over a field `k` of characteristic `0`, and `I ⊆ 𝒪_X` an ideal sheaf nonzero on
every irreducible component of `X`. Then `I = 𝒪_X`; in particular `maxord I = 0`. -/
@[mmp "lem_kr3c_ideal_trivial_dim_zero"]
public theorem eq_top_and_maxOrder_eq_zero_of_topologicalKrullDim_eq_zero {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hsm : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (_hequi : TopologicalSpace.Equidimensional X)
    (hX : topologicalKrullDim X = 0) (I : X.IdealSheafData) (hI : IsNonzeroAtGenericPoints I) :
    I = ⊤ ∧ maxOrder I = 0 := by
  have hst := stalk_eq_top_of_smooth sX hsm hX.le hI
  refine ⟨?_, le_antisymm (iSup₂_le fun x _ => by rw [multAt, hst x, idealOrder_top]) bot_le⟩
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  exact TopologicalSpace.Closeds.ext (Set.eq_empty_of_forall_notMem fun x hx =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support I x).1 (hst x) hx)

/-- A triple `(X, I, E)` with `dim X = 0` has maximal order `0`, below every marking `m ≥ 1`. -/
private lemma maxOrder_lt {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X}
    (ht : IsTriple sX I E) (hX : HasDimensionIn X {0}) {m : ℕ} (hm : 1 ≤ m) :
    maxOrder I < m := by
  obtain ⟨n, rfl, h⟩ := hX
  obtain ⟨hc, hsm, hft, hqc, heq, hI, -⟩ := ht
  have := hc; have := hft; have := hqc
  rw [(eq_top_and_maxOrder_eq_zero_of_topologicalKrullDim_eq_zero sX hsm heq h I hI).2]
  exact_mod_cast hm

/-- For every `m ≥ 1`, the identity functor `identityBlowupSequenceFunctor` is an order reduction
functor for ideals of order `m` on dimensions `{0}` and an order reduction functor for marked
ideals of order `m` on dimensions `{0}` (Kollár 3.70, the case `dim X = 0`). -/
@[mmp "lem_kr3c_order_reduction_ideals_dim_zero"]
public theorem isOrderReductionFunctor_identity_dim_zero (m : ℕ) (hm : 1 ≤ m) :
    (∃ B : OrderBlowupSequenceFunctor.{u} m (idealTriplesOfDim {0} m),
      B.toFun = identityBlowupSequenceFunctor _ _ ∧ IsOrderReductionFunctorIdeals m {0} B) ∧
    ∃ B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim {0} m),
      B.toFun = identityBlowupSequenceFunctor _ _ ∧ IsOrderReductionFunctorMarked m {0} B :=
  ⟨⟨⟨identityBlowupSequenceFunctor _ _, fun _ ht => ht.1, fun _ _ => trivial⟩, rfl,
    fun _ ht => maxOrder_lt ht.1 ht.2.1 hm,
    ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩,
  ⟨⟨identityBlowupSequenceFunctor _ _, fun _ ht => ht.1, fun _ _ => trivial⟩, rfl,
    fun _ ht => maxOrder_lt ht.1 ht.2.2 hm,
    ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩⟩

end DimensionZero

/-- Restricting twice is restricting once. -/
private lemma map_map_apply {Y : Scheme.{u}} {A B C : Y.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (s : Γ(Y, C)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom s) =
      (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  rfl

/-- A nonzerodivisor on an affine open stays one on every smaller open. -/
private theorem restrict_mem_nonZeroDivisors {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    {g : Γ(Y, W)} (hg : g ∈ nonZeroDivisors Γ(Y, W)) {O : Y.Opens} (h : O ≤ W) :
    Y.presheaf.map (homOfLE h).op g ∈ nonZeroDivisors Γ(Y, O) := by
  have key : ∀ x : Γ(Y, O), x * Y.presheaf.map (homOfLE h).op g = 0 → x = 0 := by
    intro x hx
    choose s hsO hps using fun p : O => hW.exists_basicOpen_le p (h p.2)
    refine Y.sheaf.eq_of_locally_eq' (fun p : O => Y.basicOpen (s p)) O (fun p => homOfLE (hsO p))
      (fun p hp => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hps ⟨p, hp⟩⟩) x 0 fun p => ?_
    have := hW.isLocalization_basicOpen (s p)
    have hreg := IsSMulRegular.of_isLocalization (S := Γ(Y, Y.basicOpen (s p)))
      (Submonoid.powers (s p)) (isRegular_iff_mem_nonZeroDivisors.mpr hg).left
    rw [map_zero]
    refine hreg ((mul_comm _ _).trans (Eq.trans ?_ (mul_zero _).symm))
    change Y.presheaf.map (homOfLE (hsO p)).op x *
      Y.presheaf.map (homOfLE (Y.basicOpen_le (s p))).op g = 0
    rw [← map_map_apply (hsO p) h, ← map_mul, hx, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm]), key⟩

/-- Division by a section which is a nonzerodivisor on each member of an affine cover, where
it is locally possible, is possible uniquely globally. -/
private theorem existsUnique_fraction_of_cover {Y : Scheme.{u}} {V : Y.Opens} {ι : Type*}
    (W : ι → Y.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hle : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i) (g f : Γ(Y, V))
    (hg : ∀ i, Y.presheaf.map (homOfLE (hle i)).op g ∈ nonZeroDivisors Γ(Y, W i))
    (hex : ∀ i, ∃ w : Γ(Y, W i),
      Y.presheaf.map (homOfLE (hle i)).op f = w * Y.presheaf.map (homOfLE (hle i)).op g) :
    ∃! y : Γ(Y, V), f = y * g := by
  choose w hw using hex
  have uniq : ∀ y y' : Γ(Y, V), f = y * g → f = y' * g → y = y' := by
    intro y y' h1 h2
    refine Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hle i)) hcover y y' fun i => ?_
    have e : Y.presheaf.map (homOfLE (hle i)).op y * Y.presheaf.map (homOfLE (hle i)).op g =
        Y.presheaf.map (homOfLE (hle i)).op y' * Y.presheaf.map (homOfLE (hle i)).op g := by
      rw [← map_mul, ← map_mul, ← h1, ← h2]
    exact (mul_cancel_right_mem_nonZeroDivisors (hg i)).mp e
  have compat : TopCat.Presheaf.IsCompatible Y.presheaf W w := by
    intro i j
    change Y.presheaf.map (homOfLE inf_le_left).op (w i) =
      Y.presheaf.map (homOfLE inf_le_right).op (w j)
    refine (mul_cancel_right_mem_nonZeroDivisors
      (restrict_mem_nonZeroDivisors (hW i) (hg i) inf_le_left)).mp ?_
    have e (x : Γ(Y, V)) : Y.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op
        (Y.presheaf.map (homOfLE (hle i)).op x) =
          Y.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
            (Y.presheaf.map (homOfLE (hle j)).op x) := by
      rw [map_map_apply, map_map_apply]
    rw [← map_mul, ← hw i, e, e g, ← map_mul, ← hw j]
  obtain ⟨y₀, hy, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hle i)) hcover w compat
  let y : Γ(Y, V) := y₀
  have hfy : f = y * g := by
    refine Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hle i)) hcover _ _ fun i => ?_
    change Y.presheaf.map (homOfLE (hle i)).op f = Y.presheaf.map (homOfLE (hle i)).op (y * g)
    rw [map_mul, hw i, show Y.presheaf.map (homOfLE (hle i)).op y = w i from hy i]
  exact ⟨y, hfy, fun y' hy' => uniq _ _ hy' hfy⟩

/-- The ideal of a quasi-coherent ideal sheaf on an affine open `V` is `J` as soon as it is the
extension of `J` on the members of a cover of `V` by basic opens. -/
private theorem ideal_eq_of_basicOpen_cover {Y : Scheme.{u}} (K : Y.IdealSheafData)
    (V : Y.affineOpens) (J : Ideal Γ(Y, V))
    (H : ∀ p ∈ V.1, ∃ r : Γ(Y, V), p ∈ Y.basicOpen r ∧
      K.ideal (Y.affineBasicOpen r) = J.map (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom) :
    K.ideal V = J := by
  choose r hr e using fun p : V.1 => H p.1 p.2
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun x hxV ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, ⟨x, hxV⟩, rfl⟩, hr ⟨x, hxV⟩⟩
  have inst := V.2.isLocalization_basicOpen
  refine Submodule.eq_of_isLocalized'_span _ hspan (fun i ↦ Γ(Y, Y.basicOpen i.1))
    (fun i ↦ Γ(Y, Y.basicOpen i.1))
    (fun i ↦ Algebra.linearMap Γ(Y, V.1) Γ(Y, Y.basicOpen i.1)) ?_
  rintro ⟨_, j, rfl⟩
  simp only [Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra]
  rw [K.map_ideal_basicOpen V (r j)]
  exact e j

/-- Cancelling a nonzerodivisor `t` in a colon ideal: `((g_i t) : (t)) = (g_i)`. -/
private theorem colon_span_mul_eq {R : Type*} [CommRing R] {ι : Type*} (g : ι → R) {t : R}
    (ht : t ∈ nonZeroDivisors R) :
    (Ideal.span (Set.range fun i => g i * t)).colon ((Ideal.span {t} : Ideal R) : Set R) =
      Ideal.span (Set.range g) := by
  have key : Ideal.span (Set.range fun i => g i * t) =
      Ideal.span {t} * Ideal.span (Set.range g) := by
    rw [Ideal.span_mul_span', Set.singleton_mul, ← Set.range_comp]
    congr 2
    funext i
    exact mul_comm _ _
  ext y
  rw [Submodule.mem_colon]
  constructor
  · intro hy
    have := hy t (Ideal.subset_span rfl)
    rw [key, smul_eq_mul, Ideal.mem_span_singleton_mul] at this
    obtain ⟨z, hz, hzy⟩ := this
    rwa [(mul_cancel_left_mem_nonZeroDivisors ht).mp (hzy.trans (mul_comm _ _))] at hz
  · intro hy b hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    rw [key, smul_eq_mul, show y * (c * t) = c * (t * y) by ring]
    exact Ideal.mul_mem_left _ c (Ideal.mul_mem_mul (Ideal.subset_span rfl) hy)

namespace BlowupChartData

section Chart

variable {X : Scheme.{u}} {Z : X.IdealSheafData} (c : BlowupChartData Z) (ℓ : Fin c.r)

/-- The standard chart `D_+(x_ℓ|_V)` over an affine open `V ⊆ U`. -/
private noncomputable abbrev stdChart (v : {V : X.affineOpens // V.1 ≤ c.U}) :
    (blowUp Z).affineOpens :=
  blowUpChartOpen Z v.1 ⟨_, c.restrict_mem_ideal v.1 v.2 ℓ⟩

private lemma stdChart_le (v : {V : X.affineOpens // V.1 ≤ c.U}) :
    (stdChart c ℓ v).1 ≤ c.chart ℓ :=
  le_iSup₂ (f := fun (V : X.affineOpens) (h : V.1 ≤ c.U) =>
    (blowUpChartOpen Z V ⟨_, c.restrict_mem_ideal V h ℓ⟩).1) v.1 v.2

private lemma chart_le_iSup_stdChart : c.chart ℓ ≤ ⨆ v, (stdChart c ℓ v).1 :=
  iSup₂_le fun V h => le_iSup (fun v => (stdChart c ℓ v).1) ⟨V, h⟩

private lemma restrict_chartPullback {D : (blowUp Z).Opens} (v : {V : X.affineOpens // V.1 ≤ c.U})
    (hD : D ≤ (stdChart c ℓ v).1) (f : Γ(X, c.U)) :
    ((blowUp Z).presheaf.map (homOfLE (hD.trans (stdChart_le c ℓ v))).op).hom
        (c.chartPullback ℓ f) =
      ((blowUpToBase Z).appLE v.1.1 D (hD.trans (blowUpChartOpen_le Z _ _))).hom
        ((X.presheaf.map (homOfLE v.2).op).hom f) := by
  have e1 := Scheme.Hom.appLE_map (blowUpToBase Z) (c.chart_le ℓ)
    (homOfLE (hD.trans (stdChart_le c ℓ v))).op
  have e2 := Scheme.Hom.map_appLE (blowUpToBase Z) (hD.trans (blowUpChartOpen_le Z v.1 _))
    (homOfLE v.2).op
  exact congrArg (fun φ => φ.hom f) (e1.trans e2.symm)

private lemma ideal_comap_eq_span {D : (blowUp Z).affineOpens}
    (v : {V : X.affineOpens // V.1 ≤ c.U}) (hD : D.1 ≤ (stdChart c ℓ v).1)
    (I : X.IdealSheafData) {s : ℕ} (f : Fin s → Γ(X, c.U))
    (hf : ∀ (V : X.affineOpens) (h : V.1 ≤ c.U),
      I.ideal V = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (f i))) :
    (I.comap (blowUpToBase Z)).ideal D = Ideal.span (Set.range fun i =>
      ((blowUp Z).presheaf.map (homOfLE (hD.trans (stdChart_le c ℓ v))).op).hom
        (c.chartPullback ℓ (f i))) := by
  rw [Stacks.IdealSheaf.ideal_comap_appLE I (blowUpToBase Z) v.1 D
    (hD.trans (blowUpChartOpen_le Z _ _)), hf v.1 v.2, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact (restrict_chartPullback c ℓ v hD (f i)).symm

private lemma ideal_comap_center_eq_span {D : (blowUp Z).affineOpens}
    (v : {V : X.affineOpens // V.1 ≤ c.U}) (hD : D.1 ≤ (stdChart c ℓ v).1) :
    (Z.comap (blowUpToBase Z)).ideal D = Ideal.span {
      ((blowUp Z).presheaf.map (homOfLE (hD.trans (stdChart_le c ℓ v))).op).hom
        (c.chartPullback ℓ (c.x ℓ))} := by
  rw [ideal_comap_eq_span c ℓ v hD Z c.x c.generates]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨j, rfl⟩
    obtain ⟨y, hy, -⟩ := c.existsUnique_chartFraction ℓ j
    simp only
    rw [hy, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rintro _ rfl
    exact Ideal.subset_span ⟨ℓ, rfl⟩

private lemma restrict_chartPullback_mem_nonZeroDivisors {D : (blowUp Z).Opens}
    (v : {V : X.affineOpens // V.1 ≤ c.U}) (hD : D ≤ (stdChart c ℓ v).1) :
    ((blowUp Z).presheaf.map (homOfLE (hD.trans (stdChart_le c ℓ v))).op).hom
        (c.chartPullback ℓ (c.x ℓ)) ∈ nonZeroDivisors Γ(blowUp Z, D) := by
  have h0 := blowUpChartMap_self_mem_nonZeroDivisors Z v.1 ⟨_, c.restrict_mem_ideal v.1 v.2 ℓ⟩
  rw [← restrict_chartPullback c ℓ v le_rfl] at h0
  have := restrict_mem_nonZeroDivisors (stdChart c ℓ v).2 h0 hD
  rwa [map_map_apply] at this

end Chart

open Scheme in
/-- **Kollár (3.60).** Let `c` give generators `x_1, …, x_r ∈ 𝒪_X(U)` of `I_Z|_U` and `U_ℓ` its
`ℓ`-th chart on the blow-up `π : B_ZX → X`. Let `(I, m)` be a marked ideal with
`π^*I ⊆ (π^*I_Z)^m`, and `f_1, …, f_s ∈ 𝒪_X(U)` generators of `I|_U`. Then there are sections
`g_i ∈ 𝒪_{B_ZX}(U_ℓ)` equal to the chart transforms `π^*f_i / x_ℓ^m` (the first entries of
`c.chartTransform ℓ (f i) m`), and on every affine open `V ⊆ U_ℓ` the first entry of the
birational transform `π⁻¹_{Z*}(I, m)` is the ideal generated by the restrictions of the `g_i`. -/
@[mmp "lem_kr3c_chart_transform_generates"]
public theorem exists_birationalTransform_ideal_eq_span_chartTransform {X : Scheme.{u}}
    {Z : X.IdealSheafData} (c : BlowupChartData Z) (ℓ : Fin c.r) (a : MarkedIdeal X)
    (ha : a.I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a.m)
    {s : ℕ} (f : Fin s → Γ(X, c.U))
    (hf : ∀ (V : X.affineOpens) (h : V.1 ≤ c.U),
      a.I.ideal V = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (f i))) :
    ∃ g : Fin s → Γ(blowUp Z, c.chart ℓ),
      (∀ i, algebraMap _ (Localization.Away (c.chartPullback ℓ (c.x ℓ))) (g i) =
        (c.chartTransform ℓ (f i) a.m).1) ∧
      ∀ (V : (blowUp Z).affineOpens) (h : V.1 ≤ c.chart ℓ),
        (a.birationalTransform Z).I.ideal V =
          Ideal.span (Set.range fun i => ((blowUp Z).presheaf.map (homOfLE h).op).hom (g i)) := by
  have hdiv : ∀ i, ∃ g : Γ(blowUp Z, c.chart ℓ),
      c.chartPullback ℓ (f i) = g * c.chartPullback ℓ (c.x ℓ) ^ a.m := by
    intro i
    refine (existsUnique_fraction_of_cover (fun v => (stdChart c ℓ v).1)
      (fun v => (stdChart c ℓ v).2) (stdChart_le c ℓ) (chart_le_iSup_stdChart c ℓ)
      (c.chartPullback ℓ (c.x ℓ) ^ a.m) (c.chartPullback ℓ (f i)) ?_ ?_).exists
    · intro v
      rw [map_pow]
      exact pow_mem (restrict_chartPullback_mem_nonZeroDivisors c ℓ v le_rfl) _
    · intro v
      have hmem := ha (stdChart c ℓ v) (by
        rw [ideal_comap_eq_span c ℓ v le_rfl a.I f hf]
        exact Ideal.subset_span ⟨i, rfl⟩)
      rw [IdealSheafData.ideal_pow, Pi.pow_apply, ideal_comap_center_eq_span c ℓ v le_rfl,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
      obtain ⟨w, hw⟩ := hmem
      exact ⟨w, by rw [map_pow]; exact hw.symm⟩
  choose g hg using hdiv
  refine ⟨g, fun i => ?_, fun V hV => ?_⟩
  · simp only [BlowupChartData.chartTransform]
    rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, ← hg i]
  · have hZa : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z) ^ a.m) :=
      Stacks.Divisors.isEffectiveCartierDivisor_pow
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z) a.m
    have hcol : (a.birationalTransform Z).I = IdealSheafData.colon (a.I.comap (blowUpToBase Z))
        (Z.comap (blowUpToBase Z) ^ a.m) (fg_ideal_of_isEffectiveCartierDivisor _ hZa) := by
      change idealColon _ _ = _
      unfold idealColon
      exact IdealSheafData.ofIdeals_ideal (IdealSheafData.colon (a.I.comap (blowUpToBase Z))
        (Z.comap (blowUpToBase Z) ^ a.m) (fg_ideal_of_isEffectiveCartierDivisor _ hZa))
    rw [hcol]
    refine ideal_eq_of_basicOpen_cover _ V _ fun p hp => ?_
    obtain ⟨v, hpv⟩ := TopologicalSpace.Opens.mem_iSup.mp (chart_le_iSup_stdChart c ℓ (hV hp))
    obtain ⟨r, hrle, hpr⟩ := V.2.exists_basicOpen_le (V := (stdChart c ℓ v).1 ⊓ V.1)
      ⟨p, hpv, hp⟩ hp
    have hD : ((blowUp Z).affineBasicOpen r).1 ≤ (stdChart c ℓ v).1 := hrle.trans inf_le_left
    refine ⟨r, hpr, ?_⟩
    rw [IdealSheafData.ideal_colon, IdealSheafData.ideal_pow, Pi.pow_apply,
      ideal_comap_eq_span c ℓ v hD a.I f hf, ideal_comap_center_eq_span c ℓ v hD,
      Ideal.span_singleton_pow, Ideal.map_span, ← Set.range_comp]
    have e : ∀ i, ((blowUp Z).presheaf.map (homOfLE (hD.trans (stdChart_le c ℓ v))).op).hom
        (c.chartPullback ℓ (f i)) =
        ((blowUp Z).presheaf.map (homOfLE (hD.trans (stdChart_le c ℓ v))).op).hom (g i) *
        ((blowUp Z).presheaf.map (homOfLE (hD.trans (stdChart_le c ℓ v))).op).hom
          (c.chartPullback ℓ (c.x ℓ)) ^ a.m := by
      intro i
      rw [hg i, map_mul, map_pow]
    simp only [e]
    rw [colon_span_mul_eq _ (pow_mem (restrict_chartPullback_mem_nonZeroDivisors c ℓ v hD) _)]
    congr 2
    funext i
    exact (map_map_apply _ _ _).symm

end BlowupChartData

namespace Kollar

open MMP.Flips.ResolutionInputs

/-- The pull-back `y_ℓ = π^*x_ℓ` is a nonzerodivisor on every open of the chart `U_ℓ`. -/
private theorem chartPullback_self_restrict_mem_nonZeroDivisors {X : Scheme.{u}}
    {Z : X.IdealSheafData} (c : BlowupChartData Z) (ℓ : Fin c.r) {O : (blowUp Z).Opens}
    (hO : O ≤ c.chart ℓ) :
    (blowUp Z).presheaf.map (homOfLE hO).op (c.chartPullback ℓ (c.x ℓ)) ∈
      nonZeroDivisors Γ(blowUp Z, O) := by
  let ι := {V : X.affineOpens // V.1 ≤ c.U}
  let a : ∀ (v : ι), Z.ideal v.1 := fun v => ⟨_, c.restrict_mem_ideal v.1 v.2 ℓ⟩
  let W : ι → (blowUp Z).Opens := fun v => (blowUpChartOpen Z v.1 (a v)).1
  have hchart : c.chart ℓ = ⨆ v, W v := iSup_subtype' (p := fun V : X.affineOpens => V.1 ≤ c.U)
    (f := fun V h => (blowUpChartOpen Z V ⟨_, c.restrict_mem_ideal V h ℓ⟩).1)
  have hWle : ∀ v, W v ≤ c.chart ℓ := fun v => hchart ▸ le_iSup W v
  have F1 : ∀ v : ι,
      (blowUp Z).presheaf.map (homOfLE (hWle v)).op (c.chartPullback ℓ (c.x ℓ)) =
        blowUpChartMap Z v.1 (a v) ((X.presheaf.map (homOfLE v.2).op) (c.x ℓ)) := by
    intro v
    have e1 := Scheme.Hom.appLE_map (blowUpToBase Z) (c.chart_le ℓ) (homOfLE (hWle v)).op
    have e2 := Scheme.Hom.map_appLE (blowUpToBase Z) (blowUpChartOpen_le Z v.1 (a v))
      (homOfLE v.2).op
    exact congrArg (fun φ => φ.hom (c.x ℓ)) (e1.trans e2.symm)
  set y := (blowUp Z).presheaf.map (homOfLE hO).op (c.chartPullback ℓ (c.x ℓ))
  have key : ∀ t : Γ(blowUp Z, O), t * y = 0 → t = 0 := by
    intro t ht
    have hcov : O ≤ ⨆ v, O ⊓ W v := by
      intro p hp
      have : p ∈ ⨆ v, W v := hchart ▸ hO hp
      obtain ⟨v, hv⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨v, hp, hv⟩
    refine (blowUp Z).sheaf.eq_of_locally_eq' (fun v => O ⊓ W v) O
      (fun v => homOfLE inf_le_left) hcov t 0 fun v => ?_
    have hreg := restrict_mem_nonZeroDivisors (blowUpChartOpen Z v.1 (a v)).2
      (blowUpChartMap_self_mem_nonZeroDivisors Z v.1 (a v)) (inf_le_right : O ⊓ W v ≤ W v)
    have hy : (blowUp Z).presheaf.map (homOfLE (inf_le_left : O ⊓ W v ≤ O)).op y =
        (blowUp Z).presheaf.map (homOfLE (inf_le_right : O ⊓ W v ≤ W v)).op
          (blowUpChartMap Z v.1 (a v) ↑(a v)) := by
      change _ = (blowUp Z).presheaf.map _ (blowUpChartMap Z v.1 (a v)
        ((X.presheaf.map (homOfLE v.2).op) (c.x ℓ)))
      rw [← F1, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp]
      rfl
    change (blowUp Z).presheaf.map (homOfLE (inf_le_left : O ⊓ W v ≤ O)).op t =
      (blowUp Z).presheaf.map (homOfLE (inf_le_left : O ⊓ W v ≤ O)).op 0
    rw [map_zero]
    refine (mul_cancel_right_mem_nonZeroDivisors hreg).mp ?_
    rw [zero_mul, ← hy, ← map_mul, ht, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun t ht => key t (by rwa [mul_comm]), key⟩

/-- The derivatives of the pulled-back base coordinates in a centre direction `j ≠ ℓ`:
`∂(π^*x_i)/∂y_j = y_ℓ` if `i = j`, and `0` otherwise. Indeed `π^*x_i = y_i y_ℓ` for `i ≤ r`,
`i ≠ ℓ`, and `π^*x_i = y_i` otherwise. -/
private theorem partialDerivative_chartPullback_coordinate {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData} (c : BlowupChartData Z) {n : ℕ}
    {x : Fin n → Γ(X, c.U)} (hrn : c.r ≤ n) (hcx : ∀ i : Fin c.r, c.x i = x (Fin.castLE hrn i))
    (ℓ : Fin c.r)
    (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
    (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ) {j : Fin c.r} (hjℓ : j ≠ ℓ) (i : Fin n) :
    partialDerivative hy W hW (Fin.castLE hrn j) (restrictSection W hW (c.chartPullback ℓ (x i))) =
      if Fin.castLE hrn j = i then restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) else 0 := by
  letI := MMP.Mori.sectionAlgebra (blowUpToBase Z ≫ sX) W.1
  have hjℓ' : Fin.castLE hrn j ≠ Fin.castLE hrn ℓ := fun h => hjℓ (Fin.castLE_injective hrn h)
  have hcoordℓ : chartCoordinates c x ℓ (Fin.castLE hrn ℓ) = c.chartPullback ℓ (c.x ℓ) := by
    rw [hcx ℓ]
    exact chartCoordinates_of_forall_ne c x hrn fun i hi h => hi (Fin.castLE_injective hrn h)
  have hcoord : ∀ i, Bridges.partialDerivation hy W hW (Fin.castLE hrn j)
      (restrictSection W hW (chartCoordinates c x ℓ i)) = if Fin.castLE hrn j = i then 1 else 0 :=
    Bridges.partialDerivative_restrictSection_coordinate hy W hW _
  change Bridges.partialDerivation hy W hW (Fin.castLE hrn j) _ = _
  by_cases h : ∃ i' : Fin c.r, i' ≠ ℓ ∧ Fin.castLE hrn i' = i
  · obtain ⟨i', hi', rfl⟩ := h
    rw [← hcx i', chartPullback_eq_chartFraction_mul c ℓ i', ← hcoordℓ,
      ← chartCoordinates_castLE_of_ne c x hrn hi', restrictSection, map_mul, ← restrictSection,
      ← restrictSection, Derivation.leibniz, hcoord, hcoord, if_neg hjℓ', hcoordℓ]
    split_ifs <;> simp
  · push Not at h
    rw [← chartCoordinates_of_forall_ne c x hrn h, hcoord, if_neg (h j hjℓ), if_neg (h j hjℓ)]

/-- **Kollár (3.75.1).** Let `x_1, …, x_n` be local coordinates on `U` whose first `r` generate
the centre `Z`, and `y = chartCoordinates c x ℓ` the coordinates of the chart `U_ℓ` of the
blow-up `π : B_Z X → X`. If `π^*f = y_ℓ^m g` with `m ≥ 1`, then for `j ≤ r`, `j ≠ ℓ`,
`π^*(∂f/∂x_j) = y_ℓ^{m-1} ∂g/∂y_j` on every affine open `W ⊆ U_ℓ` over an affine open
`W' ⊆ U`. -/
@[mmp "lem_kr3d_chart_derivative_index_below"]
public theorem appLE_partialDerivative_eq_pow_mul_partialDerivative_of_ne
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Z : X.IdealSheafData}
    (c : BlowupChartData Z) {n : ℕ} {x : Fin n → Γ(X, c.U)} (hx : IsLocalCoordinatesOn sX c.U x)
    (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
    (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
    {f : Γ(X, c.U)} {g : Γ(blowUp Z, c.chart ℓ)} {m : ℕ} (hm : 0 < m)
    (hfg : c.chartPullback ℓ f = c.chartPullback ℓ (c.x ℓ) ^ m * g)
    {j : Fin c.r} (hjℓ : j ≠ ℓ)
    (W' : X.affineOpens) (hW' : W'.1 ≤ c.U) (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ c.chart ℓ) (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1) :
    ((blowUpToBase Z).appLE W' W hWW').hom
        (partialDerivative hx W' hW' (Fin.castLE hrn j) (restrictSection W' hW' f)) =
      restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) ^ (m - 1) *
        partialDerivative hy W hW (Fin.castLE hrn j) (restrictSection W hW g) := by
  -- pull-backs to `W` are restrictions of chart pull-backs
  have hpb : ∀ (s : Γ(X, c.U)) (e : W.1 ≤ blowUpToBase Z ⁻¹ᵁ c.U),
      ((blowUpToBase Z).appLE c.U W.1 e).hom s = restrictSection W hW (c.chartPullback ℓ s) := by
    intro s e
    rw [BlowupChartData.chartPullback, restrictSection, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map]
  have hpb' : ((blowUpToBase Z).appLE W'.1 W.1 hWW').hom (restrictSection W' hW' f) =
      restrictSection W hW (c.chartPullback ℓ f) := by
    rw [← hpb f (hWW'.trans ((blowUpToBase Z).preimage_mono hW')), restrictSection,
      ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  letI := MMP.Mori.sectionAlgebra (blowUpToBase Z ≫ sX) W.1
  let D := Bridges.partialDerivation hy W hW (Fin.castLE hrn j)
  have hD : ∀ t, partialDerivative hy W hW (Fin.castLE hrn j) t = D t := fun _ => rfl
  have hxi := partialDerivative_chartPullback_coordinate c hrn hcx ℓ hy W hW hjℓ
  set yℓ := restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) with hyℓ
  have hDyℓ : D yℓ = 0 := by
    rw [← hD, hyℓ, hcx ℓ, hxi, if_neg fun h => hjℓ (Fin.castLE_injective hrn h)]
  -- the chain rule
  have hchain := MMP.Resolution.Kollar.partialDerivative_appLE_eq_sum (blowUpToBase Z) rfl hx hy
    W' hW' W hW hWW' (restrictSection W' hW' f) (Fin.castLE hrn j)
  simp_rw [hpb, hxi, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hD]
    at hchain
  rw [hpb', hfg, restrictSection, map_mul, map_pow, ← restrictSection, ← restrictSection,
    ← hyℓ, Derivation.leibniz, Derivation.leibniz_pow, hDyℓ] at hchain
  simp only [smul_zero, add_zero, smul_eq_mul] at hchain
  -- cancel `y_ℓ`
  have hreg : yℓ ∈ nonZeroDivisors Γ(blowUp Z, W.1) :=
    chartPullback_self_restrict_mem_nonZeroDivisors c ℓ hW
  refine (mul_cancel_right_mem_nonZeroDivisors hreg).mp ?_
  rw [← hchain, hD]
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_lt hm
  simp only [Nat.zero_add, Nat.add_sub_cancel, pow_succ]
  ring

section CenterChart

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (CommRingCat.of k)}
  {Z : X.IdealSheafData} (c : BlowupChartData Z) {n : ℕ} {x : Fin n → Γ(X, c.U)}

/-- Pulling back along `π` and restricting to `W ⊆ U_ℓ` is restriction of the chart pullback. -/
private theorem appLE_eq_restrictSection_chartPullback (ℓ : Fin c.r) (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ c.chart ℓ) (s : Γ(X, c.U)) (e : W.1 ≤ blowUpToBase Z ⁻¹ᵁ c.U) :
    ((blowUpToBase Z).appLE c.U W.1 e).hom s = restrictSection W hW (c.chartPullback ℓ s) := by
  rw [BlowupChartData.chartPullback, restrictSection, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map]

private theorem appLE_restrictSection (ℓ : Fin c.r) (W' : X.affineOpens) (hW' : W'.1 ≤ c.U)
    (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ) (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1)
    (s : Γ(X, c.U)) :
    ((blowUpToBase Z).appLE W'.1 W.1 hWW').hom (restrictSection W' hW' s) =
      restrictSection W hW (c.chartPullback ℓ s) := by
  rw [← appLE_eq_restrictSection_chartPullback c ℓ W hW s
    (hWW'.trans ((blowUpToBase Z).preimage_mono hW')), restrictSection,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem chartCoordinates_castLE_self (hrn : c.r ≤ n)
    (hcx : ∀ i : Fin c.r, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r) :
    chartCoordinates c x ℓ (Fin.castLE hrn ℓ) = c.chartPullback ℓ (c.x ℓ) := by
  rw [hcx ℓ]
  exact chartCoordinates_of_forall_ne c x hrn fun i hi h => hi (Fin.castLE_injective hrn h)

/-- `∂(π^*x_i)/∂y_ℓ` is `y_{i'}` if `i = i' ≤ r` with `i' ≠ ℓ`, `1` if `i = ℓ`, and `0` otherwise,
written so that it can be summed against. -/
private theorem partialDerivative_chartPullback_coordinate_self (hrn : c.r ≤ n)
    (hcx : ∀ i : Fin c.r, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
    (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
    (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ) (i : Fin n) :
    partialDerivative hy W hW (Fin.castLE hrn ℓ) (restrictSection W hW (c.chartPullback ℓ (x i))) =
      (∑ i' ∈ Finset.univ.erase ℓ, if Fin.castLE hrn i' = i then
          restrictSection W hW (chartCoordinates c x ℓ (Fin.castLE hrn i')) else 0) +
        if Fin.castLE hrn ℓ = i then 1 else 0 := by
  letI := MMP.Mori.sectionAlgebra (blowUpToBase Z ≫ sX) W.1
  have hcoord := Bridges.partialDerivative_restrictSection_coordinate hy W hW (Fin.castLE hrn ℓ)
  by_cases h : ∃ i' : Fin c.r, i' ≠ ℓ ∧ Fin.castLE hrn i' = i
  · obtain ⟨i', hi', rfl⟩ := h
    rw [← hcx i', chartPullback_eq_chartFraction_mul c ℓ i',
      ← chartCoordinates_castLE_self c hrn hcx ℓ,
      ← chartCoordinates_castLE_of_ne c x hrn hi', restrictSection, map_mul, ← restrictSection,
      ← restrictSection, ← Bridges.partialDerivation_apply, Derivation.leibniz,
      Bridges.partialDerivation_apply, Bridges.partialDerivation_apply, hcoord, hcoord]
    simp_rw [Fin.castLE_inj]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.mpr ⟨hi', Finset.mem_univ _⟩)]
    simp [hi'.symm]
  · push Not at h
    rw [← chartCoordinates_of_forall_ne c x hrn h, hcoord, Finset.sum_eq_zero, zero_add]
    exact fun i' hi' => if_neg (h i' (Finset.ne_of_mem_erase hi'))

/-- **The chain rule on the chart `U_ℓ` in the direction `y_ℓ`**:
`∂(π^*h)/∂y_ℓ = ∑_{i ≠ ℓ} y_i π^*(∂h/∂x_i) + π^*(∂h/∂x_ℓ)`. -/
private theorem partialDerivative_appLE_chart (hx : IsLocalCoordinatesOn sX c.U x) (hrn : c.r ≤ n)
    (hcx : ∀ i : Fin c.r, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
    (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
    (W' : X.affineOpens) (hW' : W'.1 ≤ c.U) (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ)
    (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1) (h : Γ(X, W')) :
    partialDerivative hy W hW (Fin.castLE hrn ℓ) (((blowUpToBase Z).appLE W'.1 W.1 hWW').hom h) =
      ∑ i ∈ Finset.univ.erase ℓ, restrictSection W hW (chartCoordinates c x ℓ (Fin.castLE hrn i)) *
          ((blowUpToBase Z).appLE W'.1 W.1 hWW').hom
            (partialDerivative hx W' hW' (Fin.castLE hrn i) h) +
        ((blowUpToBase Z).appLE W'.1 W.1 hWW').hom
          (partialDerivative hx W' hW' (Fin.castLE hrn ℓ) h) := by
  rw [Kollar.partialDerivative_appLE_eq_sum (blowUpToBase Z) rfl hx hy W' hW' W hW hWW']
  simp_rw [appLE_eq_restrictSection_chartPullback c ℓ W hW,
    partialDerivative_chartPullback_coordinate_self c hrn hcx ℓ hy, mul_add, Finset.mul_sum,
    mul_ite,
    mul_zero, mul_one]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_comm]

end CenterChart

/-- **Kollár (3.75.3), corrected.** Let `x_1, …, x_n` be local coordinates on `U` whose first `r`
generate the centre `Z`, and `y = chartCoordinates c x ℓ` the coordinates of the chart `U_ℓ` of
the blow-up `π : B_Z X → X`. If `π^*f = y_ℓ^m g` with `m ≥ 1`, then
`π^*(∂f/∂x_ℓ) = y_ℓ^{m-1} (y_ℓ ∂g/∂y_ℓ - ∑_{i ≤ r, i ≠ ℓ} y_i ∂g/∂y_i + m g)` on every affine
open `W ⊆ U_ℓ` over an affine open `W' ⊆ U`. -/
@[mmp "lem_kr3d_chart_derivative_index_center"]
public theorem appLE_partialDerivative_self_eq_pow_mul
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Z : X.IdealSheafData}
    (c : BlowupChartData Z) {n : ℕ} {x : Fin n → Γ(X, c.U)} (hx : IsLocalCoordinatesOn sX c.U x)
    (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
    (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
    {f : Γ(X, c.U)} {g : Γ(blowUp Z, c.chart ℓ)} {m : ℕ} (hm : 0 < m)
    (hfg : c.chartPullback ℓ f = c.chartPullback ℓ (c.x ℓ) ^ m * g)
    (W' : X.affineOpens) (hW' : W'.1 ≤ c.U) (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ c.chart ℓ) (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1) :
    ((blowUpToBase Z).appLE W' W hWW').hom
        (partialDerivative hx W' hW' (Fin.castLE hrn ℓ) (restrictSection W' hW' f)) =
      restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) ^ (m - 1) *
        (restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) *
            partialDerivative hy W hW (Fin.castLE hrn ℓ) (restrictSection W hW g) -
          ∑ i ∈ Finset.univ.erase ℓ,
            restrictSection W hW (chartCoordinates c x ℓ (Fin.castLE hrn i)) *
              partialDerivative hy W hW (Fin.castLE hrn i) (restrictSection W hW g) +
          (m : Γ(blowUp Z, W)) * restrictSection W hW g) := by
  letI := MMP.Mori.sectionAlgebra (blowUpToBase Z ≫ sX) W.1
  have hDyℓ : partialDerivative hy W hW (Fin.castLE hrn ℓ)
      (restrictSection W hW (c.chartPullback ℓ (c.x ℓ))) = 1 := by
    rw [← chartCoordinates_castLE_self c hrn hcx ℓ,
      Bridges.partialDerivative_restrictSection_coordinate, if_pos rfl]
  have key := partialDerivative_appLE_chart c hx hrn hcx ℓ hy W' hW' W hW hWW'
    (restrictSection W' hW' f)
  rw [Finset.sum_congr rfl fun i hi => by
      rw [Kollar.appLE_partialDerivative_eq_pow_mul_partialDerivative_of_ne c hx hrn hcx ℓ hy hm
        hfg (Finset.ne_of_mem_erase hi) W' hW' W hW hWW'],
    appLE_restrictSection c ℓ W' hW' W hW hWW', hfg, restrictSection, map_mul, map_pow,
    ← restrictSection, ← restrictSection, ← Bridges.partialDerivation_apply, Derivation.leibniz,
    Derivation.leibniz_pow, Bridges.partialDerivation_apply, Bridges.partialDerivation_apply,
    hDyℓ] at key
  rw [Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _, ← Finset.mul_sum] at key
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm.ne'
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one, Nat.add_sub_cancel] at key
  push_cast at key ⊢
  linear_combination -key

end Kollar

end MMP.Resolution
