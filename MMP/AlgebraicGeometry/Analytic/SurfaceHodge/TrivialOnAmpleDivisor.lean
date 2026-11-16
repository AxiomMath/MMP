module

public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Vanishing.KodairaCharZero
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.UnitDual
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import MMP.AlgebraicGeometry.Analytic.LogObstructionCurveDegree
public import MMP.AlgebraicGeometry.Analytic.GAGA.Projective
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive

/-!
# Line bundles that are trivial on an ample divisor

Let `X` be a smooth projective variety of dimension `n ≥ 2` over an algebraically closed field `k`
of characteristic zero, `C ⊂ X` a prime divisor and `D` a divisor on `X` such that `C - D` and
`C + D` are ample (for instance `C ∈ |mA|` with `A` ample, `m ≫ 0`, and `D` numerically trivial).
If `𝒪_X(D)|_C ≅ 𝒪_C`, then `D ∼ 0`.

The proof is the one of the period-lattice step in the proof of Hodge symmetry for surfaces.
Kodaira vanishing gives `H¹(X, 𝒪_X(D - C)) = 0`, since `C - D` is ample, so restriction
`H⁰(X, 𝒪_X(D)) → H⁰(C, 𝒪_X(D)|_C) ≅ H⁰(C, 𝒪_C)` is onto and `𝒪_X(D)` has a nonzero section.
The same holds for `-D`, using `C + D` ample and `𝒪_X(-D)|_C ≅ (𝒪_X(D)|_C)^∨ ≅ 𝒪_C`. The divisors
of zeros `div φ + D ≥ 0` and `div ψ - D ≥ 0` of the two sections add up to the effective principal
divisor `div (φ ψ)`, which vanishes because a regular function on a proper variety is constant;
hence `div φ + D = 0`.

## Main results

* `MMP.Analytic.SurfaceHodge.linearlyEquivalent_zero_of_nontrivial_divisorialSubmodule`: on a
  proper normal variety, `h⁰(𝒪_X(D)) ≠ 0` and `h⁰(𝒪_X(-D)) ≠ 0` imply `D ∼ 0`.
* `MMP.Analytic.SurfaceHodge.nontrivial_divisorialSubmodule_of_pullback_iso_unit`: if `C - D`
  is ample and `𝒪_X(D)|_C ≅ 𝒪_C`, then `H⁰(X, 𝒪_X(D)) ≠ 0`.
* `MMP.Analytic.SurfaceHodge.nonempty_pullback_neg_iso_unit`: `𝒪_X(D)|_C ≅ 𝒪_C` implies
  `𝒪_X(-D)|_C ≅ 𝒪_C`.
* `MMP.Analytic.SurfaceHodge.linearlyEquivalent_zero_of_pullback_iso_unit`: if `C ± D` are ample
  and `𝒪_X(D)|_C ≅ 𝒪_C`, then `D ∼ 0`.
* `MMP.Analytic.SurfaceHodge.mem_range_map_one_of_pullback_iso_unit`: over `ℂ`, if `C ± D` is
  ample for every numerically trivial `D`, a class `v ∈ H¹(X^an, 𝒪)` whose exponential is the
  class of `L^an` for an invertible `L` with `L|_C ≅ 𝒪_C` lies in the image of `H¹(X^an, ℤ)`.

## Implementation notes

The restriction `𝒪_X(D)|_C` is the pullback `i^* 𝒪_X(D)` along the closed immersion
`i : C ⟶ X` of the reduced subscheme of `C`. No smoothness or connectedness of `C` is needed: only
`H⁰(C, 𝒪_C) ≠ 0`. The dimension bound `n ≥ 2` is the range `1 < n` of Kodaira vanishing.

In `MMP.Analytic.SurfaceHodge.mem_range_map_one_of_pullback_iso_unit` the exponential of `v` is
`H¹` of the second map of the exponential sequence
`MMP.Analytic.exists_shortExact_exponentialSequence`, read in `Pic(X^an)` through
`H¹(X^an, 𝒪^×) ≅ Pic(X^an)`. The line bundle with that class is taken algebraic, `L^an` with `L`
on `X`, so that its restriction to `C` is the algebraic one; every analytic line bundle on `X^an`
is of this form (GAGA).

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Theorem 2.47
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.Analytic.SurfaceHodge

section LineBundle

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- On a proper integral scheme over an algebraically closed field, every global function is a
constant. -/
private theorem scalarsToGlobalSections_bijective (f : X ⟶ Spec (.of k)) [IsProper f] :
    Function.Bijective (Mori.scalarsToGlobalSections k f) := by
  have hf : f.appTop.hom.Finite := finite_appTop_of_universallyClosed (f := f)
  have := (isField_of_universallyClosed (f := f)).isDomain
  refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
  have hiso : (Scheme.ΓSpecIso (.of k)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  exact (hf.comp hiso).to_isIntegral

/-- **An effective principal divisor on a proper normal variety is zero**: if `div ψ ≥ 0` then
`ψ` is a global regular function, hence a nonzero constant. -/
private theorem principalDivisor_eq_zero_of_nonneg (f : X ⟶ Spec (.of k)) [IsProper f]
    (ψ : (Mori.RationalFunctions X)ˣ) (h : 0 ≤ Mori.principalDivisor ψ) :
    Mori.principalDivisor ψ = 0 := by
  have hsec : (0 : Mori.Divisor X).IsDivisorialSection ⊤
      (fun Z => (ψ : Mori.RationalFunctions X) Z.1) := by
    intro E hE
    refine Or.inr ?_
    change WithZero.exp (-(0 : Mori.Divisor X).coeff E) ≤
      E.valuation ((ψ : Mori.RationalFunctions X) E.component)
    rw [E.valuation_component, WithZero.exp_le_exp]
    have := h E
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    rw [← Mori.DivisorWithCoeffs.coeff_apply, Mori.coeff_principalDivisor] at this
    simpa using this
  obtain ⟨r, hr⟩ := hsec.exists_eq
  obtain ⟨c, rfl⟩ := (scalarsToGlobalSections_bijective f).2 r
  have hc : c ≠ 0 := by
    rintro rfl
    obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
      ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
    have := congrFun hr ⟨Z, by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; trivial⟩
    rw [map_zero, map_zero] at this
    exact (ψ.isUnit.map (Mori.RationalFunctions.component (X := X) Z)).ne_zero this.symm
  refine Finsupp.ext fun E => ?_
  have hu : IsUnit (X.presheaf.germ ⊤ E.genericPoint trivial
      (Mori.scalarsToGlobalSections k f c)) :=
    ((IsUnit.mk0 c hc).map _).map _
  rw [Finsupp.coe_zero, Pi.zero_apply, ← Mori.DivisorWithCoeffs.coeff_apply,
    Mori.coeff_principalDivisor]
  refine E.ord_eq_zero_of_isUnit hu ?_
  have := congrFun hr ⟨E.component, trivial⟩
  rw [Mori.toRationalFunctionsPresheaf_app_apply] at this
  rw [← this]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _

/-- **A divisor `D` with `h⁰(𝒪_X(D)) ≠ 0` and `h⁰(𝒪_X(-D)) ≠ 0` is linearly equivalent to zero**
on a proper normal variety over an algebraically closed field: the divisors of zeros
`div φ + D` and `div ψ - D` of nonzero sections are effective with effective principal sum
`div (φ ψ)`, which is therefore zero, so both vanish. -/
theorem linearlyEquivalent_zero_of_nontrivial_divisorialSubmodule (f : X ⟶ Spec (.of k))
    [IsProper f] (D : Mori.Divisor X) (hD : Nontrivial (D.divisorialSubmodule ⊤))
    (hD' : Nontrivial ((-D).divisorialSubmodule ⊤)) : D.LinearlyEquivalent 0 := by
  obtain ⟨s, hs⟩ := exists_ne (0 : D.divisorialSubmodule ⊤)
  obtain ⟨t, ht⟩ := exists_ne (0 : (-D).divisorialSubmodule ⊤)
  set φ := (Mori.Divisor.isUnit_sectionToRationalFunctions hs).unit
  set ψ := (Mori.Divisor.isUnit_sectionToRationalFunctions ht).unit
  have h1 : 0 ≤ Mori.principalDivisor φ + D := Mori.Divisor.zeroDivisor_nonneg D s hs
  have h2 : 0 ≤ Mori.principalDivisor ψ + -D := Mori.Divisor.zeroDivisor_nonneg (-D) t ht
  have h3 : Mori.principalDivisor (φ * ψ) = 0 := by
    refine principalDivisor_eq_zero_of_nonneg f _ ?_
    rw [Mori.principalDivisor_mul]
    have := add_nonneg h1 h2
    rwa [add_add_add_comm, add_neg_cancel, add_zero] at this
  rw [Mori.principalDivisor_mul] at h3
  have h4 : Mori.principalDivisor φ + D = 0 := by
    refine le_antisymm ?_ h1
    rw [show Mori.principalDivisor φ + D = -(Mori.principalDivisor ψ + -D) by
      rw [neg_add, neg_neg, eq_neg_of_add_eq_zero_left h3]]
    exact neg_nonpos.mpr h2
  refine ⟨φ⁻¹, ?_⟩
  rw [Mori.principalDivisor_inv, sub_zero]
  exact (neg_eq_of_add_eq_zero_right h4).symm

end LineBundle

section Restriction

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k f]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

omit [IsAlgClosed k] [CharZero k] in
/-- On a smooth variety, `𝒪_X(-D)` is the dual of the invertible sheaf `𝒪_X(D)`. -/
noncomputable def negDivisorialSheafIsoDualSheaf (hsm : Mori.IsSmoothScheme f)
    (D : Mori.Divisor X) :
    (-D).divisorialSheaf ≅ Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf D.divisorialSheaf :=
  have hDc : D.IsCartier := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _
  have := hDc.isInvertibleModule_divisorialSheaf
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.sheaf.obj
    X.ringCatSheaf.property D.divisorialSheaf (-D).divisorialSheaf
    (hDc.divisorialSheafTensorIso (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) ≪≫
      eqToIso (congrArg Mori.Divisor.divisorialSheaf (add_neg_cancel D)) ≪≫
      Mori.Divisor.divisorialSheafZeroIso)

omit [IsAlgClosed k] [CharZero k] in
/-- `H¹(X, ℱ)` depends on `ℱ` only up to isomorphism. -/
private theorem subsingleton_cohomologyOverField_congr {Y : Scheme.{0}} (g : Y ⟶ Spec (.of k))
    {M N : Y.Modules} (e : M ≅ N) (i : ℕ) :
    Subsingleton (cohomologyOverField k g M i) ↔ Subsingleton (cohomologyOverField k g N i) :=
  ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom).mapIso
    (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived i).mapIso
      e)).toLinearEquiv.toEquiv.subsingleton_congr

/-- **Kodaira vanishing in degree one for divisors.** On a smooth projective variety of
dimension `n ≥ 2`, `H¹(X, 𝒪_X(-A)) = 0` for every ample Cartier divisor `A`. -/
private theorem subsingleton_cohomologyOverField_one_neg_of_isAmple
    (hsm : Mori.IsSmoothScheme f) {n : ℕ} (hn : topologicalKrullDim X = n) (hn2 : 2 ≤ n)
    (A : Mori.Divisor X) (hA : A.IsCartier) (hAa : A.IsAmple hA) :
    Subsingleton (cohomologyOverField k f (-A).divisorialSheaf 1) := by
  have := hA.isInvertibleModule_divisorialSheaf
  have hK := Mori.subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple f hsm n hn
    A.divisorialSheaf hAa 1 (by omega)
  have hK' : Subsingleton (cohomologyOverField k f
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A.divisorialSheaf) 1) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
      1).toEquiv.subsingleton_congr.mpr hK
  exact (subsingleton_cohomologyOverField_congr f (negDivisorialSheafIsoDualSheaf f hsm A) 1).mpr
    hK'

omit [IsAlgClosed k] [CharZero k] in
/-- `H⁰(C, ℳ) ≠ 0` for a module `ℳ ≅ 𝒪_C` on an integral scheme. -/
private theorem nontrivial_cohomologyOverField_zero_of_iso_unit {Y : Scheme.{0}} [IsIntegral Y]
    (g : Y ⟶ Spec (.of k)) (M : Y.Modules) (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Nontrivial (cohomologyOverField k g M 0) := by
  let e0 := ((SheafOfModules.evaluation Y.ringCatSheaf
    (op (⊤ : Y.Opens))).rightDerivedZeroIsoSelf.app M).toLinearEquiv
  let e1 := ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).mapIso e).toLinearEquiv
  have : Nontrivial ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).obj
      (SheafOfModules.unit Y.ringCatSheaf)) :=
    inferInstanceAs (Nontrivial Γ(Y, ⊤))
  exact (e0.trans e1).toEquiv.nontrivial

/-- **Lifting the trivialization from an ample divisor.** On a smooth projective variety of
dimension `n ≥ 2`, let `C` be a prime divisor and `D` a divisor with `C - D` ample and
`𝒪_X(D)|_C ≅ 𝒪_C`. Then `𝒪_X(D)` has a nonzero global section: `H¹(X, 𝒪_X(D - C)) = 0` by
Kodaira vanishing, so `H⁰(X, 𝒪_X(D)) → H⁰(C, 𝒪_X(D)|_C) ≅ H⁰(C, 𝒪_C) ≠ 0` is onto. -/
theorem nontrivial_divisorialSubmodule_of_pullback_iso_unit (hsm : Mori.IsSmoothScheme f)
    {n : ℕ} (hn : topologicalKrullDim X = n) (hn2 : 2 ≤ n) (C : Mori.PrimeDivisor X)
    (D : Mori.Divisor X)
    (hA : ∃ h : (Finsupp.single C 1 - D : Mori.Divisor X).IsCartier,
      (Finsupp.single C 1 - D : Mori.Divisor X).IsAmple h)
    (hD : Nonempty ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj D.divisorialSheaf ≅
      SheafOfModules.unit C.idealSheaf.subscheme.ringCatSheaf)) :
    Nontrivial (D.divisorialSubmodule ⊤) := by
  obtain ⟨hAc, hAa⟩ := hA
  obtain ⟨eC⟩ := hD
  have := C.integral
  have hH1 := subsingleton_cohomologyOverField_one_neg_of_isAmple f hsm hn hn2 _ hAc hAa
  have hsurj := Mori.Divisor.surjective_cohomologyOverFieldMap_restriction f inferInstance hsm
    (-(Finsupp.single C 1 - D)) C hH1
  rw [show -(Finsupp.single C (1 : ℤ) - D) + Finsupp.single C 1 = D by abel] at hsurj
  have hT := nontrivial_cohomologyOverField_zero_of_iso_unit (C.idealSheaf.subschemeι ≫ f) _ eC
  have hS := hsurj.nontrivial
  let e0 := ((SheafOfModules.evaluation X.ringCatSheaf
    (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app D.divisorialSheaf).toLinearEquiv
  exact @Equiv.nontrivial _ _ e0.toEquiv.symm hS

omit [IsAlgClosed k] [CharZero k] in
/-- If `𝒪_X(D)|_C ≅ 𝒪_C` then `𝒪_X(-D)|_C ≅ 𝒪_C`: on a smooth variety `𝒪_X(-D)` is the dual of
the invertible sheaf `𝒪_X(D)`, and pullback commutes with duals of finite locally free
modules. -/
theorem nonempty_pullback_neg_iso_unit (hsm : Mori.IsSmoothScheme f) (C : Mori.PrimeDivisor X)
    (D : Mori.Divisor X)
    (hD : Nonempty ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj D.divisorialSheaf ≅
      SheafOfModules.unit C.idealSheaf.subscheme.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj (-D).divisorialSheaf ≅
      SheafOfModules.unit C.idealSheaf.subscheme.ringCatSheaf) := by
  obtain ⟨eC⟩ := hD
  have hDc : D.IsCartier := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _
  have := hDc.isInvertibleModule_divisorialSheaf
  have hfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} D.divisorialSheaf :=
    have := Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible
      D.divisorialSheaf
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  have hiso := Stacks.Chow.pullbackDualMap_isIso C.idealSheaf.subschemeι D.divisorialSheaf hfl
  exact ⟨(Scheme.Modules.pullback C.idealSheaf.subschemeι).mapIso
      (negDivisorialSheafIsoDualSheaf f hsm D) ≪≫
    @asIso _ _ _ _ (Stacks.Chow.pullbackDualMap C.idealSheaf.subschemeι D.divisorialSheaf) hiso ≪≫
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafIsoOfIso eC).symm ≪≫
    Stacks.AlgebraicGeometry.ReflexiveModules.unitDualIso _⟩

/-- **A line bundle trivial on a curve with `C ± D` ample is trivial.** Let `X` be a smooth
projective variety of dimension `n ≥ 2` over an algebraically closed field of characteristic
zero, `C ⊂ X` a prime divisor and `D` a divisor on `X` such that `C - D` and `C + D` are ample
(for instance `C ∈ |mA|`, `m ≫ 0`, and `D` numerically trivial). If `𝒪_X(D)|_C ≅ 𝒪_C`, then
`D ∼ 0`, that is `𝒪_X(D) ≅ 𝒪_X`. -/
theorem linearlyEquivalent_zero_of_pullback_iso_unit (hsm : Mori.IsSmoothScheme f) {n : ℕ}
    (hn : topologicalKrullDim X = n) (hn2 : 2 ≤ n) (C : Mori.PrimeDivisor X)
    (D : Mori.Divisor X)
    (hA : ∃ h : (Finsupp.single C 1 - D : Mori.Divisor X).IsCartier,
      (Finsupp.single C 1 - D : Mori.Divisor X).IsAmple h)
    (hA' : ∃ h : (Finsupp.single C 1 + D : Mori.Divisor X).IsCartier,
      (Finsupp.single C 1 + D : Mori.Divisor X).IsAmple h)
    (hD : Nonempty ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj D.divisorialSheaf ≅
      SheafOfModules.unit C.idealSheaf.subscheme.ringCatSheaf)) :
    D.LinearlyEquivalent 0 := by
  have hA'' : ∃ h : (Finsupp.single C 1 - -D : Mori.Divisor X).IsCartier,
      (Finsupp.single C 1 - -D : Mori.Divisor X).IsAmple h := by
    rwa [sub_neg_eq_add]
  exact linearlyEquivalent_zero_of_nontrivial_divisorialSubmodule f D
    (nontrivial_divisorialSubmodule_of_pullback_iso_unit f hsm hn hn2 C D hA hD)
    (nontrivial_divisorialSubmodule_of_pullback_iso_unit f hsm hn hn2 C (-D) hA''
      (nonempty_pullback_neg_iso_unit f hsm C D hD))

end Restriction

section PicardZero

universe v' u' w'

variable {Cc : Type u'} [Category.{v'} Cc] {J : GrothendieckTopology Cc}
  (O : Ccᵒᵖ ⥤ CommRingCat.{w'})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify J AddCommGrpCat.{w'}]

/-- The Picard class of a trivial invertible sheaf is zero: `[ℳ] + [ℳ] = [ℳ ⊗ ℳ] = [ℳ]`. -/
private theorem classOf_eq_zero_of_iso_unit
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hM : Stacks.SheafOfModules.IsInvertible O hO M)
    (e : M ≅ SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.Picard.classOf O hO M hM = 0 := by
  have hMM := Stacks.SheafOfModules.isInvertible_tensorSheaf O hO M M
  have he := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff O hO _ _ hMM hM).2
    ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso e).app M ≪≫
      Stacks.SheafOfModules.tensorSheafLeftUnitor O hO M⟩
  exact add_eq_left.mp ((Stacks.SheafOfModules.Picard.classOf_tensor O hO M M hM hM hMM).trans he)

end PicardZero

section PeriodKernel

attribute [local instance] hasExt_of_enoughInjectives
  Stacks.Cohomology.Generators.picardGroupAddCommGroup
attribute [local implicit_reducible] TopCat.Sheaf

/-- **The period kernel.** Let `X` be a smooth projective complex variety of dimension `n ≥ 2`
and `C ⊂ X` a prime divisor such that `C - D` and `C + D` are ample for every numerically
trivial divisor `D`. Let `0 → ℤ → 𝒪 → 𝒪^× → 0` be the exponential sequence on `X^an`, and let
`v ∈ H¹(X^an, 𝒪)` be a class whose exponential, read in `Pic(X^an)`, is the class of `L^an` for an
invertible sheaf `L` on `X` with `L|_C ≅ 𝒪_C`. Then `v` lies in the image of `H¹(X^an, ℤ)`.

Indeed the obstruction of `L^an` is the boundary of `exp v`, which vanishes, so `L` has degree
zero on every curve; writing `L ≅ 𝒪_X(D)`, the divisor `D` is numerically trivial, so `D ∼ 0`
by `MMP.Analytic.SurfaceHodge.linearlyEquivalent_zero_of_pullback_iso_unit`. Hence
`exp v = [𝒪^an] = 0` and `v` comes from `H¹(X^an, ℤ)` by exactness. -/
theorem mem_range_map_one_of_pullback_iso_unit {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsProjectiveVariety ℂ sX]
    (hsm : Mori.IsSmoothScheme sX) [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {n : ℕ} (hn : topologicalKrullDim X = n) (hn2 : 2 ≤ n) (C : Mori.PrimeDivisor X)
    (hC : ∀ D : Mori.Divisor X, (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ sX →
      (∃ h : (Finsupp.single C 1 - D : Mori.Divisor X).IsCartier,
        (Finsupp.single C 1 - D : Mori.Divisor X).IsAmple h) ∧
      (∃ h : (Finsupp.single C 1 + D : Mori.Divisor X).IsCartier,
        (Finsupp.single C 1 + D : Mori.Divisor X).IsAmple h))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Nonempty ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj L ≅
      SheafOfModules.unit C.idealSheaf.subscheme.ringCatSheaf)) :
    haveI : IsProper sX := (AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine
      sX).2 (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ)) |>.isProper
    let E := exists_shortExact_exponentialSequence sX
    ∀ (hLan : Stacks.SheafOfModules.IsInvertible _ _ ((analytifyModule sX).obj L))
      (v : Sheaf.H ((sheafCompose _ (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)) 1),
      Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification sX)
        ((Stacks.Thickenings.sheafCohomologyOneExtEquiv _ _).addCommGroupIsoToAddEquiv.symm
          (Sheaf.H.map E.choose_spec.choose 1 v)) =
        Stacks.SheafOfModules.Picard.classOf _ _ ((analytifyModule sX).obj L) hLan →
      v ∈ Set.range (Sheaf.H.map E.choose 1) := by
  intro E hLan v hv
  let := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
  have hS := E.choose_spec.choose_spec.choose_spec.1
  have h1 : Stacks.Thickenings.cohomologyBoundary hS 1 (Sheaf.H.map E.choose_spec.choose 1 v) = 0 :=
    (Stacks.Thickenings.cohomology_exact_quotient hS 1 _).2 ⟨v, rfl⟩
  have h0 : picardObstruction (analytification sX) hS
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification sX)
        ((Stacks.Thickenings.sheafCohomologyOneExtEquiv _ _).addCommGroupIsoToAddEquiv.symm
          (Sheaf.H.map E.choose_spec.choose 1 v))) = 0 := by
    refine (picardObstruction_apply _ _ _).trans ?_
    refine (congrArg (fun z => Stacks.Thickenings.cohomologyBoundary hS 1
      ((Stacks.Thickenings.sheafCohomologyOneExtEquiv (analytification sX).carrier
        (Stacks.Cohomology.Generators.unitsSheaf (analytification sX))).hom z))
      ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
        (analytification sX)).symm_apply_apply _)).trans ?_
    refine (congrArg (Stacks.Thickenings.cohomologyBoundary hS 1) ?_).trans h1
    rw [← Iso.addCommGroupIsoToAddEquiv_apply]
    exact AddEquiv.apply_symm_apply _ _
  have h2 := Eq.subst (motive := fun x => picardObstruction (analytification sX) hS x = 0) hv h0
  have hX : IsProjective sX :=
    (AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine sX).2
      (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ))
  have hdeg := degreeOn_eq_zero_of_tmul_picardObstruction_eq_zero sX hX L (fun _ =>
    (congrArg (fun x => (1 : ℚ) ⊗ₜ[ℤ] x) h2).trans (TensorProduct.tmul_zero _ _))
  obtain ⟨D, ⟨eD⟩⟩ := Mori.exists_divisorialSheaf_iso_of_isInvertible L
  have hDc : D.IsCartier := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D
  have := hDc.isInvertibleModule_divisorialSheaf
  have hnum : (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ sX := by
    refine ⟨Mori.QDivisor.isQCartier_toQDivisor hDc, Mori.QDivisor.isQCartier_zero, ?_⟩
    intro Z i _ _ _ hZ
    rw [Mori.QDivisor.intersectionNumber_toQDivisor ℂ sX i hZ.le D hDc,
      MMP.Fourfold.intersectionNumber_zero sX i hZ.le]
    have h4 : D.degreeOn ℂ sX i hZ.le hDc = 0 :=
      (Mori.degreeOn_eq_of_iso ℂ sX i hZ.le eD).trans (hdeg Z i hZ.le)
    exact_mod_cast h4
  obtain ⟨hA, hA'⟩ := hC D hnum
  obtain ⟨eC⟩ := hL
  have hlin := linearlyEquivalent_zero_of_pullback_iso_unit sX hsm hn hn2 C D hA hA'
    ⟨(Scheme.Modules.pullback C.idealSheaf.subschemeι).mapIso eD ≪≫ eC⟩
  let eL : L ≅ SheafOfModules.unit X.ringCatSheaf :=
    eD.symm ≪≫ hlin.divisorialSheafIso ≪≫ Mori.Divisor.divisorialSheafZeroIso
  let eLan : (analytifyModule sX).obj L ≅ SheafOfModules.unit (ringCatSheaf sX) :=
    (analytifyModule sX).mapIso eL ≪≫ analytifyUnitIso sX
  have h5 := hv.trans (classOf_eq_zero_of_iso_unit _ _ _ hLan eLan)
  have h6 := (AddEquiv.map_eq_zero_iff _).1 ((AddEquiv.map_eq_zero_iff _).1 h5)
  exact (Stacks.Thickenings.cohomology_exact_middle hS 1 v).1 h6

end PeriodKernel

end MMP.Analytic.SurfaceHodge
