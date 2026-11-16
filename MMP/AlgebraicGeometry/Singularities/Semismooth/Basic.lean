/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.DifferentialsDegreeGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.AutomorphismSchemeDimension
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.Picard.ClosedPointDegreeOne
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroDegreeZero

/-!
# Boundaries of degree zero on curves

A fact of FA Chapter 12 about the notions of `MMP.Foundations.Flips.Seminormal`.

On a smooth connected proper curve `C` of genus `g` over an algebraically closed field, a
boundary `Δ` with `deg(K_C + Δ) = 0` is either `0` with `g = 1`, or has degree `2` with `g = 0`,
in which case `⌊Δ⌋` consists of at most two points (proof of FA 12.2.11, case (12.2.11.3)).

## Main results

* `MMP.Flips.degreeOn_smoothLocus_eq_sum`: on a smooth proper curve over `k = k̄`, the degree
  of `𝒪_C(D)` is the sum of the coefficients of `D`.
* `MMP.Flips.curve_instances`: a smooth proper normal variety of dimension one over `k = k̄`
  is a smooth proper curve in the sense of Stacks.
* `MMP.Flips.h0_canonical_eq_genus`: `h⁰(K_C)` is the genus of `C`.
* `MMP.Flips.sum_coeff_canonical_eq`: `deg K_C = 2 h⁰(K_C) - 2`.
* `MMP.Flips.sum_principalDivisor_eq_zero`: a principal divisor has degree `0`.
* `MMP.Flips.QWeilDivisor.IsBoundary.degree_zero_curve_types`: the two types of boundaries of
  degree `-deg K_C` on a smooth proper curve.

## Implementation notes

FA works over `ℂ`. The curve statement is made over an algebraically closed field `k`: there
every prime divisor of `C` is a `k`-rational closed point, so the degree of a divisor is the sum
of its coefficients, and the genus is `h⁰(C, 𝒪_C(K_C))` for a canonical divisor `K_C`. Over a
field that is not algebraically closed the statement fails even with the true degree: `ℙ¹_ℂ`,
as a curve over `ℝ`, has `h⁰(K_C) = 0` and `deg_ℝ K_C = -4`, and the boundary `P + Q` with `P`,
`Q` two closed points of degree two. A smooth connected curve is a smooth normal variety of
dimension one (the dimension is part of `MMP.Mori.Divisor.IsCanonicalDivisor`), integral hence
connected.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.11
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Flips

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-! ### Riemann–Roch inputs on a smooth proper curve -/

/-- The generic point of a prime divisor of a curve is a closed point (as
`Stacks.EtaleCohomology.isClosed_singleton_genericPoint_of_isCurve`, whose module does not build
under this project's linters). -/
private theorem isClosed_singleton_genericPoint_of_isCurve' {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k g]
    (Z : MMP.Mori.PrimeDivisor X) :
    IsClosed ({Z.genericPoint} : Set X) := by
  refine Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)) fun h => ?_
  have h1 := Z.coheight_genericPoint
  rw [h, show genericPoint X = (⊤ : X) from rfl, Order.coheight_top] at h1
  exact zero_ne_one h1

section CurveInputs

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open scoped Classical in
private theorem boundary_sum_cases {α : Type*} (g : ℕ) (S : ℚ) (Δ : α →₀ ℚ)
    (hΔ : ∀ a, 0 ≤ Δ a ∧ Δ a ≤ 1) (hS : S = 2 * (g : ℚ) - 2)
    (hdeg : S + Δ.sum (fun _ a => a) = 0) :
    (g = 1 ∧ Δ = 0) ∨
      (g = 0 ∧ Δ.sum (fun _ a => a) = 2 ∧ (Δ.support.filter fun a => 1 ≤ Δ a).card ≤ 2) := by
  have hsum : Δ.sum (fun _ a => a) = ∑ a ∈ Δ.support, Δ a := rfl
  have hnn : 0 ≤ Δ.sum (fun _ a => a) := by
    rw [hsum]; exact Finset.sum_nonneg fun a _ => (hΔ a).1
  have hg : g ≤ 1 := by
    have : (g : ℚ) ≤ 1 := by linarith
    exact_mod_cast this
  interval_cases g
  · right
    have h2 : Δ.sum (fun _ a => a) = 2 := by push_cast at hS; linarith
    refine ⟨rfl, h2, ?_⟩
    have hle : ∑ a ∈ Δ.support.filter (fun a => 1 ≤ Δ a), Δ a ≤ ∑ a ∈ Δ.support, Δ a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => (hΔ a).1)
    have hge : ((Δ.support.filter fun a => 1 ≤ Δ a).card : ℚ) ≤
        ∑ a ∈ Δ.support.filter (fun a => 1 ≤ Δ a), Δ a := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      exact Finset.sum_le_sum fun a ha => by
        simpa using (Finset.mem_filter.1 ha).2
    have : ((Δ.support.filter fun a => 1 ≤ Δ a).card : ℚ) ≤ 2 := by
      rw [← h2, hsum]; exact hge.trans hle
    exact_mod_cast this
  · left
    have h0 : ∑ a ∈ Δ.support, Δ a = 0 := by push_cast at hS; rw [← hsum]; linarith
    refine ⟨rfl, ?_⟩
    rw [Finset.sum_eq_zero_iff_of_nonneg fun a _ => (hΔ a).1] at h0
    ext a
    by_cases ha : a ∈ Δ.support
    · simpa using h0 a ha
    · simpa using ha

private theorem isIso_ι_of_eq_top {X : Scheme.{u}} {U : X.Opens} (hU : U = ⊤) : IsIso U.ι := by
  subst hU; rw [← Scheme.topIso_hom]; infer_instance

private theorem topologicalKrullDim_opens_eq_of_eq_top {X : Scheme.{u}} {U : X.Opens} (hU : U = ⊤) :
    topologicalKrullDim U.toScheme = topologicalKrullDim X := by
  have := isIso_ι_of_eq_top hU
  exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso U.ι)).isHomeomorph

/-- On a smooth proper normal variety `C` of dimension one over `k = k̄`, the open subscheme
`U = ⊤` (typically the smooth locus) is a smooth proper curve over `k` in the sense of Stacks,
with `k ≅ Γ(U, 𝒪_U)`. -/
theorem curve_instances [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {U : C.Opens} (hU : U = ⊤) :
    AlgebraicGeometry.IsCurve k (U.ι ≫ sC) ∧ Smooth (U.ι ≫ sC) ∧ IsProper (U.ι ≫ sC) ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ sC).appTop) := by
  have := isIso_ι_of_eq_top hU
  have hV := hC.1
  have : Smooth sC := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sC hsm
  have hint : IsIntegral C := hV.toIsIntegral
  have : Nonempty U := by
    rw [hU]; exact ⟨⟨(inferInstance : Nonempty C).some, trivial⟩⟩
  have : IsIntegral U.toScheme := inferInstance
  have : QuasiCompact (U.ι ≫ sC) := inferInstance
  have : IsSeparated (U.ι ≫ sC) := inferInstance
  have : LocallyOfFiniteType (U.ι ≫ sC) := inferInstance
  have hvar : AlgebraicGeometry.IsVariety k (U.ι ≫ sC) := ⟨⟩
  have hcurve : AlgebraicGeometry.IsCurve k (U.ι ≫ sC) :=
    (AlgebraicGeometry.isCurve_iff k _).2
      ⟨hvar, (topologicalKrullDim_opens_eq_of_eq_top hU).trans hdim⟩
  have : IsProper (U.ι ≫ sC) := inferInstance
  exact ⟨hcurve, inferInstance, inferInstance, GenusOne.isIso_globalSections_of_isAlgClosed _⟩

private theorem degreeOn_canonical_eq [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsLocallyNoetherian C] [IsNormal C] [QuasiCompact sC]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) [IsProper ((smoothLocus sC).ι ≫ sC)]
    (hdim : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1) :
    K.degreeOn k sC (smoothLocus sC).ι hdim (MMP.Fourfold.isCartier_of_isSmoothScheme hsm K) =
      2 * (genus ((smoothLocus sC).ι ≫ sC) : ℤ) - 2 := by
  obtain ⟨hcurve, hsmooth, hprop, hiso⟩ := curve_instances hC hsm hp hK.1 hsm
  set pY := (smoothLocus sC).ι ≫ sC
  have := isIso_ι_of_eq_top hsm
  have := QuasiCompact.compactSpace_of_compactSpace sC
  have hKc := MMP.Fourfold.isCartier_of_isSmoothScheme hsm K
  have := hKc.isInvertibleModule_divisorialSheaf
  have := smoothOfRelativeDimension_one_of_isCurve k pY
  have := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials pY
  have hΩ : SheafOfModules.IsInvertible (smoothLocus sC).toScheme.presheaf
      (smoothLocus sC).toScheme.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials pY) :=
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one
      (smoothLocus sC).toScheme.toRingedSpace _
  let e : (Scheme.Modules.pullback (smoothLocus sC).ι).obj K.divisorialSheaf ≅
      Scheme.Hom.relativeDifferentials pY :=
    ((Scheme.Modules.restrictFunctorIsoPullback (smoothLocus sC).ι).app _).symm ≪≫ hK.iso ≪≫
      Scheme.Modules.exteriorPowerOneIsoSelf _
  change invertibleCurveDegree k pY hdim
    ((Scheme.Modules.pullback (smoothLocus sC).ι).obj K.divisorialSheaf) = _
  rw [invertibleCurveDegree_eq_of_iso k pY hdim e,
    invertibleCurveDegree_eq_curveDegree k pY hdim]
  exact curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two pY

private theorem image_top_eq_top {X : Scheme.{u}} {U : X.Opens} (hU : U = ⊤) : U.ι ''ᵁ ⊤ = ⊤ := by
  subst hU
  ext x
  simp

/-- Global sections of `M` and of its restriction to the open `U = ⊤` have the same dimension. -/
private theorem finrank_globalSectionsOver_restrict {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (M : X.Modules) {U : X.Opens} (hU : U = ⊤) :
    Module.finrank k ((globalSectionsOver (U.ι ≫ f)).obj (M.restrict U.ι)) =
      Module.finrank k ((globalSectionsOver f).obj M) := by
  let g : ((globalSectionsOver f).obj M) →ₗ[k]
      ((globalSectionsOver (U.ι ≫ f)).obj (M.restrict U.ι)) :=
    { toFun := fun s => (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom s
      map_add' := fun s t => map_add _ s t
      map_smul' := fun a (s : Γ(M, ⊤)) => by
        change (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom
            ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a) • s) =
          ((U.ι.appIso ⊤).inv (((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop).hom a)) •
            ((M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom s)
        refine (M.val.map_smul (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op _ s).trans ?_
        congr 1
        exact (congrArg (fun φ => φ.hom ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a)))
          (Scheme.Hom.app_appIso_inv U.ι ⊤)).symm }
  have hbij : Function.Bijective g := by
    have : IsIso (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op) := by
      have : (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤) = eqToHom (image_top_eq_top hU) :=
        Subsingleton.elim _ _
      rw [this, eqToHom_op, eqToHom_map]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso
      (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op)
  exact (LinearEquiv.ofBijective g hbij).finrank_eq.symm

/-- On a smooth proper curve over `k = k̄` with canonical divisor `K`, `h⁰(C, 𝒪_C(K))` is the
genus of `C` (computed on the smooth locus, which is all of `C`): `𝒪_C(K)` restricts to
`Ω_{C/k}`, and `h⁰(Ω_{C/k})` is the genus. -/
theorem h0_canonical_eq_genus [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) :
    K.h0 k sC = genus ((smoothLocus sC).ι ≫ sC) := by
  obtain ⟨hcurve, hsmooth, hprop, hiso⟩ := curve_instances hC hsm hp hK.1 hsm
  set pY := (smoothLocus sC).ι ≫ sC
  let e : K.divisorialSheaf.restrict (smoothLocus sC).ι ≅ Scheme.Hom.relativeDifferentials pY :=
    hK.iso ≪≫ Scheme.Modules.exteriorPowerOneIsoSelf _
  calc K.h0 k sC = Module.finrank k ((globalSectionsOver sC).obj K.divisorialSheaf) := rfl
    _ = Module.finrank k ((globalSectionsOver pY).obj
          (K.divisorialSheaf.restrict (smoothLocus sC).ι)) :=
        (finrank_globalSectionsOver_restrict sC _ hsm).symm
    _ = Module.finrank k ((globalSectionsOver pY).obj (Scheme.Hom.relativeDifferentials pY)) :=
        ((globalSectionsOver pY).mapIso e).toLinearEquiv.finrank_eq
    _ = Module.finrank k (cohomologyOverField k pY (Scheme.Hom.relativeDifferentials pY) 0) :=
        (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver pY _).finrank_eq.symm
    _ = genus pY := finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus pY

open MMP.Mori DivisorWithCoeffs in
/-- **Local equations of a prime divisor with an invertible ideal sheaf.** Near every point, the
ideal of `P` on an affine open `W` is generated by `f`, and the unit `φ` of `K(Y)` which is `f` on
the components meeting `W` and `1` elsewhere is a local equation of `P` on `W`. (Reproved from
`MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme`, whose local equation is not exported.) -/
private theorem exists_localEquation_of_isEffectiveCartierDivisor' {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf) (x : Y) :
    ∃ (W : Y.affineOpens) (_ : x ∈ (W : Y.Opens)) (f : Γ(Y, (W : Y.Opens)))
      (φ : (RationalFunctions Y)ˣ),
      P.idealSheaf.ideal W = Ideal.span {f} ∧
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) W φ ∧
      ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (W : Y.Opens)),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f := by
  classical
  haveI := P.integral
  have hsame : ∀ E : Mori.PrimeDivisor Y, E.genericPoint ∈ P.support → P = E := by
    intro E hE
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
    have hle : E.genericPoint ≤ P.genericPoint := specializes_iff_mem_closure.mpr hE
    by_contra hne
    have hlt : E.genericPoint < P.genericPoint := lt_of_le_not_ge hle fun h =>
      hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Specializes.antisymm (show E.genericPoint ⤳ P.genericPoint from h)
          (show P.genericPoint ⤳ E.genericPoint from hle)).eq.symm)
    have h2 := Order.coheight_add_one_le hlt
    rw [Mori.PrimeDivisor.coheight_genericPoint, Mori.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by decide)

  obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf hcart x
  have hgerm : ∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
      Ideal.span {(Y.presheaf.germ W y hy).hom f} := by
    intro y hy
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hy, hspan,
      Ideal.map_span, Set.image_singleton]
  have hnzd : ∀ y (hy : y ∈ W), (Y.presheaf.germ W y hy).hom f ∈
      nonZeroDivisors (Y.presheaf.stalk y) := fun y hy =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hW hf y hy
  let u : ∀ Z : irreducibleComponents Y, (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ :=
    fun Z => if h : componentGenericPoint Y Z ∈ W then
      (by
        letI := (RationalFunctions.isField_stalk Y Z).toField
        exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit)
      else 1
  let φ : (RationalFunctions Y)ˣ := (RationalFunctions.unitsEquiv Y).symm u
  have hφall : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f := by
    intro Z hZ
    change ((u Z : (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
      Y.presheaf.stalk (componentGenericPoint Y Z)) = _
    simp only [u]
    rw [dif_pos hZ]
    rfl
  refine ⟨⟨W, hW⟩, hxW, f, φ, hspan, ?_, hφall⟩
  rintro E ⟨y, hyE, hyW⟩
  have hηW : E.genericPoint ∈ W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
  have hZW : componentGenericPoint Y E.component ∈ W :=
    E.specializes_genericPoint.mem_open W.isOpen hηW
  have key : E.toComponent.hom ((Y.presheaf.germ W _ hηW).hom f) =
      (φ : RationalFunctions Y) E.component := by
    rw [hφall _ hZW]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  by_cases hEP : P = E
  · subst hEP
    rw [coeff_single_self]
    have hmem : P.genericPoint ∈ P.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hg0 := nonZeroDivisors.ne_zero (hnzd _ hηW)
    have hprime : Prime ((Y.presheaf.germ W _ hηW).hom f) := by
      rw [← Ideal.span_singleton_prime hg0, ← hgerm _ hηW]
      have hxr : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hmem
      obtain ⟨y', hy'⟩ := hxr
      rw [← hy', ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
      exact RingHom.ker_isPrime _
    exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
  · rw [coeff_single_of_ne hEP]
    have hnm : E.genericPoint ∉ P.support := fun h => hEP (hsame E h)
    have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
      P.idealSheaf _).2 hnm
    rw [hgerm _ hηW, Ideal.span_singleton_eq_top] at htop
    exact (E.ord_eq_zero_of_isUnit htop key).symm

open MMP.Mori DivisorWithCoeffs Stacks.AlgebraicGeometry.ReflexiveModules in
/-- On an open `V` carrying a rank-one dual basis of `𝒪_Y(P)` and a local equation `φ`, equal to
`f` there, the coordinate of the section `1` generates the same ideal as `f`. -/
private theorem span_evalAt_eq_span_of_isLocalEquation' {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y)
    (hD0 : 0 ≤ (Finsupp.single P 1 : Divisor Y)) (V : Y.Opens)
    (b : Stacks.SheafOfModules.DualBasisOne Y.sheaf.obj
      (structureSheafRing Y.toRingedSpace).property
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)) V)
    (f : Γ(Y, V)) (φ : (RationalFunctions Y)ˣ)
    (hloc : Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) V φ)
    (hφ : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ V),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ V _ hZ).hom f) :
    Ideal.span ({(evalAt (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y))
      (dualBasisCoord (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)) b)
      ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map
        (homOfLE le_top).op ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))))} :
        Set Γ(Y, V)) =
      Ideal.span {f} := by
  set c := evalAt _ (dualBasisCoord _ b)
      ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map (homOfLE le_top).op
        ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)))
  have h1 := smul_dualBasisSection b
    ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map (homOfLE le_top).op
      ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)))
  have inj : ∀ x y : Γ(Y, V),
      (∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
        (Y.presheaf.germ V _ Z.2).hom x = (Y.presheaf.germ V _ Z.2).hom y) → x = y :=
    fun x y h => toRationalFunctionsPresheaf_app_injective V (funext h)
  have E1 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      (Y.presheaf.germ V _ Z.2).hom c * (dualBasisSection _ b).1 Z = 1 := by
    intro Z
    exact congrArg
      (fun m : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) => m.1 Z) h1
  have hgsec : (Divisor.IsDivisorialSection (Finsupp.single P 1 : Divisor Y) V
      (fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1)) := by
    intro E hE
    have h0 : E.OrdGE (E.ord φ⁻¹) (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y)
        E.component) := Or.inr (E.valuation_component φ⁻¹).ge
    refine h0.mono (le_of_eq ?_)
    rw [PrimeDivisor.ord_inv, ← hloc E hE]
  let g : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) :=
    ⟨fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1, hgsec⟩
  have h2 := smul_dualBasisSection b g
  have E2 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 =
        (Y.presheaf.germ V _ Z.2).hom (evalAt _ (dualBasisCoord _ b) g) *
          (dualBasisSection _ b).1 Z := by
    intro Z
    exact (congrArg
      (fun m : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) => m.1 Z) h2).symm
  have E3 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 *
        (φ : RationalFunctions Y) Z.1 = 1 := by
    intro Z
    rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]
  have hhsec : (Divisor.IsDivisorialSection (0 : Divisor Y) V
      (fun Z => (φ : RationalFunctions Y) Z.1 * (dualBasisSection _ b).1 Z)) := by
    intro E hE
    have hψ : E.OrdGE (E.ord φ) ((φ : RationalFunctions Y) E.component) :=
      Or.inr (E.valuation_component φ).ge
    refine (hψ.mul ((dualBasisSection _ b).2 E hE)).mono (le_of_eq ?_)
    rw [← hloc E hE]
    simp
  obtain ⟨s', hs'⟩ := Divisor.IsDivisorialSection.exists_eq hhsec
  apply le_antisymm
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨evalAt _ (dualBasisCoord _ b) g, inj _ _ fun Z => ?_⟩
    rw [map_mul, ← hφ Z.1 Z.2]
    linear_combination (-(Y.presheaf.germ V _ Z.2).hom c) * E3 Z +
      ((Y.presheaf.germ V _ Z.2).hom c * (φ : RationalFunctions Y) Z.1) * E2 Z +
      ((φ : RationalFunctions Y) Z.1 *
        (Y.presheaf.germ V _ Z.2).hom (evalAt _ (dualBasisCoord _ b) g)) * E1 Z
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨s', inj _ _ fun Z => ?_⟩
    have hs'Z : (Y.presheaf.germ V _ Z.2).hom s' =
        (φ : RationalFunctions Y) Z.1 * (dualBasisSection _ b).1 Z := congrFun hs' Z
    rw [map_mul, hs'Z, ← hφ Z.1 Z.2]
    linear_combination (-(φ : RationalFunctions Y) Z.1) * E1 Z

open MMP.Mori DivisorWithCoeffs in
/-- **A point of a smooth curve over an algebraically closed field has degree one**: for a prime
divisor `P` of a smooth proper curve `C` over `k = k̄`, `deg 𝒪_C(P) = 1`. The zero scheme of the
section `1` of `𝒪_C(P)` is the reduced point `P`, whose ring of functions is `k`. -/
private theorem invertibleCurveDegree_divisorialSheaf_single_eq_one {k : Type u} [Field k]
    [IsAlgClosed k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sY]
    [Smooth sY] [IsProper sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (C : MMP.Mori.PrimeDivisor Y)
    (hD : MMP.Mori.Divisor.IsCartier (Finsupp.single C 1 : MMP.Mori.Divisor Y))
    (hdim : topologicalKrullDim Y ≤ 1)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y))] :
    invertibleCurveDegree k sY hdim
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) = 1 := by
  classical
  have : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsCurve k sY).toIsVariety.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hD0 : 0 ≤ (Finsupp.single C 1 : MMP.Mori.Divisor Y) :=
    Finsupp.single_nonneg.2 zero_le_one
  have hinv' : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) :=
    hD.isInvertibleModule_divisorialSheaf
  have hx : IsClosed ({C.genericPoint} : Set Y) :=
    isClosed_singleton_genericPoint_of_isCurve' sY C
  have hsupp : C.idealSheaf.support = TopologicalSpace.Closeds.closure ({C.genericPoint} : Set Y) :=
    SetLike.coe_injective (C.support_eq_closure)
  have : IsReduced C.idealSheaf.subscheme := by
    haveI := C.integral
    infer_instance
  have hPI : C.idealSheaf = (pointOfClosedPoint sY C.genericPoint hx).ker := by
    rw [ker_pointOfClosedPoint_eq_vanishingIdeal k sY hx]
    exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf := by
    rw [hPI]
    exact isEffectiveCartierDivisor_ker_pointOfClosedPoint k sY hx
  have hZ : AlgebraicGeometry.zeroScheme Y
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y))
      ((MMP.Mori.Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)) =
      C.idealSheaf := by
    have hloc : ∀ x : Y, ∃ V : Y.affineOpens, x ∈ (V : Y.Opens) ∧
        (AlgebraicGeometry.zeroScheme Y
          (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y))
          ((MMP.Mori.Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))).ideal V =
          C.idealSheaf.ideal V := by
      intro x
      obtain ⟨W, hxW, f, φ, hspan, hlocW, hφ⟩ :=
        exists_localEquation_of_isEffectiveCartierDivisor' C hcart x
      obtain ⟨V, hxV, hVW, ⟨b⟩⟩ := AlgebraicGeometry.exists_affineOpen_dualBasisOne_of_isInvertible
        (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) x hxW
      refine ⟨V, hxV, ?_⟩
      rw [AlgebraicGeometry.zeroScheme_ideal_eq_span_evalAt
        (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y))
        ((MMP.Mori.Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)) V b,
        ← C.idealSheaf.map_ideal hVW, hspan, Ideal.map_span, Set.image_singleton]
      exact span_evalAt_eq_span_of_isLocalEquation' C hD0 (V : Y.Opens) b
        (Y.presheaf.map (homOfLE hVW).op f) φ (hlocW.mono hVW) fun Z hZ => by
          rw [hφ Z (hVW hZ)]
          exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hVW) _ hZ f).symm
    choose U hxU hU using hloc
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top U
      (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩) hU
  have hs : (MMP.Mori.Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤) ≠ 0 := by
    intro h
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    let Z : irreducibleComponents Y :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    have h1 := congrArg (fun m : Γ(MMP.Mori.Divisor.divisorialSheaf
      (Finsupp.single C 1 : MMP.Mori.Divisor Y), ⊤) =>
        m.1 (⟨Z, trivial⟩ :
          {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ (⊤ : Y.Opens)})) h
    change (1 : Y.presheaf.stalk (componentGenericPoint Y Z)) = 0 at h1
    exact one_ne_zero h1
  have := isIso_ΓSpecIso_inv_comp_appTop_subschemeι_ker_pointOfClosedPoint k sY hx
  rw [invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one k sY hdim _
    (MMP.Mori.Divisor.divisorialSheafOneSection hD0) hs _ (hZ.trans hPI),
    finrank_globalSections_divisorSubscheme_eq_one k sY, Nat.cast_one]

open MMP.Mori DivisorWithCoeffs in
/-- On a smooth proper curve over `k = k̄`, the degree of `𝒪_C(D)` (along the smooth locus,
which is all of `C`) is the sum of the coefficients of `D`. -/
theorem degreeOn_smoothLocus_eq_sum [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsLocallyNoetherian C] [IsNormal C] [QuasiCompact sC]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdimC : topologicalKrullDim C = 1) [IsProper ((smoothLocus sC).ι ≫ sC)]
    (hdim : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1) (D : Divisor C) :
    D.degreeOn k sC (smoothLocus sC).ι hdim (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D) =
      D.sum fun _ a => a := by
  classical
  have hV := hC.1
  have : Smooth sC := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sC hsm
  have : AlgebraicGeometry.IsCurve k sC := (AlgebraicGeometry.isCurve_iff k sC).2 ⟨hV, hdimC⟩
  have := isIso_ι_of_eq_top hsm
  have := QuasiCompact.compactSpace_of_compactSpace sC
  let F : Divisor C →+ ℤ :=
    { toFun := fun E => E.degreeOn k sC (smoothLocus sC).ι hdim
        (MMP.Fourfold.isCartier_of_isSmoothScheme hsm E)
      map_zero' := Divisor.degreeOn_zero' k sC (smoothLocus sC).ι hdim
      map_add' := fun E E' => Divisor.degreeOn_add k sC (smoothLocus sC).ι hdim E E' _ _ }
  have hpt : ∀ P : Mori.PrimeDivisor C, F (Finsupp.single P 1) = 1 := by
    intro P
    have hc := MMP.Fourfold.isCartier_of_isSmoothScheme hsm (Finsupp.single P 1 : Divisor C)
    have := hc.isInvertibleModule_divisorialSheaf
    change invertibleCurveDegree k ((smoothLocus sC).ι ≫ sC) hdim
      ((Scheme.Modules.pullback (smoothLocus sC).ι).obj
        (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C))) = 1
    rw [invertibleCurveDegree_pullback_of_isIso (smoothLocus sC).ι sC hdim (le_of_eq hdimC)]
    exact invertibleCurveDegree_divisorialSheaf_single_eq_one sC P hc (le_of_eq hdimC)
  change F D = _
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [← Finsupp.smul_single_one, map_zsmul, hpt, smul_eq_mul, mul_one]

/-- On a smooth proper curve over `k = k̄` with canonical divisor `K`,
`∑ coeff(K) = 2 h⁰(K) - 2`. -/
theorem sum_coeff_canonical_eq [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) :
    (K.sum fun _ a => (a : ℚ)) = 2 * (K.h0 k sC : ℚ) - 2 := by
  obtain ⟨-, -, hprop, -⟩ := curve_instances hC hsm hp hK.1 hsm
  have : QuasiCompact sC := inferInstance
  have hdim : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1 :=
    le_of_eq ((topologicalKrullDim_opens_eq_of_eq_top hsm).trans hK.1)
  have h1 := degreeOn_smoothLocus_eq_sum hC hsm hp hK.1 hdim K
  have h2 := degreeOn_canonical_eq hC hsm hp hK hdim
  have h3 := h0_canonical_eq_genus hC hsm hp hK
  rw [h1] at h2
  rw [h3]
  have h4 : (K.sum fun _ a => (a : ℚ)) = (((K.sum fun _ a => a : ℤ)) : ℚ) := by
    simp [Finsupp.sum]
  rw [h4, h2]
  push_cast
  ring

/-- **A principal divisor on a smooth proper curve has degree zero**: on a smooth proper curve
over `k = k̄`, the coefficients of `div(φ)` sum to `0`. Its degree is the sum of its coefficients
(`MMP.Flips.degreeOn_smoothLocus_eq_sum`), and `𝒪_C(div φ) ≅ 𝒪_C` has degree `0`. -/
theorem sum_principalDivisor_eq_zero [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdimC : topologicalKrullDim C = 1) (φ : (RationalFunctions C)ˣ) :
    (MMP.Mori.principalDivisor φ).sum (fun _ a => a) = 0 := by
  obtain ⟨-, -, hprop, -⟩ := curve_instances hC hsm hp hdimC hsm
  have : QuasiCompact sC := inferInstance
  have hdim : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1 :=
    le_of_eq ((topologicalKrullDim_opens_eq_of_eq_top hsm).trans hdimC)
  have hc := MMP.Fourfold.isCartier_of_isSmoothScheme hsm (MMP.Mori.principalDivisor φ)
  have := hc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := C)).isInvertibleModule_divisorialSheaf
  rw [← degreeOn_smoothLocus_eq_sum hC hsm hp hdimC hdim,
    ← Divisor.degreeOn_zero' k sC (smoothLocus sC).ι hdim]
  exact degreeOn_eq_of_iso k sC (smoothLocus sC).ι hdim
    (Divisor.linearlyEquivalent_principalDivisor_zero φ).divisorialSheafIso

end CurveInputs

open scoped Classical in
/-- **Boundaries of degree zero on a curve** (proof of FA 12.2.11, case (12.2.11.3)). Let `C` be
a smooth connected proper curve of genus `g` over an algebraically closed field `k` and `Δ` a
boundary on `C` with `deg(K_C + Δ) = 0`. Then either `g = 1` and `Δ = 0`, or `g = 0`,
`deg Δ = 2` and `⌊Δ⌋` consists of at most two points.

`K_C` is a canonical divisor and `g = h⁰(C, 𝒪_C(K_C))`; the degree of a divisor is the sum of
its coefficients, every prime divisor of `C` being a `k`-rational point. The points of `⌊Δ⌋` are
the prime divisors with coefficient `≥ 1`. -/
@[mmp "lem_fa12a_degree_zero_curve_types"]
theorem QWeilDivisor.IsBoundary.degree_zero_curve_types [IsAlgClosed k] {C : Scheme.{u}}
    {sC : C ⟶ Spec (.of k)} [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC) {K : Divisor C}
    (hK : K.IsCanonicalDivisor sC 1)
    {Δ : QWeilDivisor C} (hΔ : Δ.IsBoundary sC)
    (hdeg : (K.sum fun _ a => (a : ℚ)) + Δ.sum (fun _ a => a) = 0) :
    (K.h0 k sC = 1 ∧ Δ = 0) ∨
      (K.h0 k sC = 0 ∧ Δ.sum (fun _ a => a) = 2 ∧
        (Δ.support.filter fun Γ => 1 ≤ Δ Γ).card ≤ 2) :=
  boundary_sum_cases (K.h0 k sC) _ Δ hΔ.2.2.2 (sum_coeff_canonical_eq hC hsm hp hK) hdeg

end MMP.Flips
