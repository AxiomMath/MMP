module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing
import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# Curves on surfaces and intersection matrices (KM §2.a, 3.41)

Positivity facts on curves used by the negativity lemma (KM 3.39) and the trichotomy of extremal
contractions: an ample Cartier divisor is positive on every proper curve, a prime divisor on a
smooth scheme is Cartier, and on a smooth surface a combination `A = ∑ aᵢ Cᵢ` of curves with
negative definite intersection matrix that is nonnegative on every `Cⱼ` has `aᵢ ≤ 0` (KM 3.41(1)).

## Main results

* `MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple`: an ample Cartier divisor is positive
  on every proper curve.
* `MMP.Threefold.Mori.isCartier_single_of_forall_uniqueFactorizationMonoid`: on a locally
  Noetherian normal scheme with factorial local rings, a prime divisor is Cartier; in particular
  (`MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme`) on a smooth scheme.
* `MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff`: an effective Cartier divisor has
  nonnegative degree on a curve not contained in its support, with equality iff they are disjoint.
* `MMP.Threefold.Mori.coeff_nonpos_of_negDef_of_intersectionNumber_nonneg`: KM 3.41(1).

## Implementation notes

Curves are proper curves `MMP.Mori.ProperCurve`, and "`f(C)` is a point" is
`MMP.Mori.ProperCurve.IsContractedBy`. Intersection numbers `(D · C)` of `ℚ`-Cartier
`ℚ`-divisors with curves need a proof that `D` is `ℚ`-Cartier. For a prime divisor on a smooth
surface that proof is `MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme`; where the
source's hypotheses make `D` `ℚ`-Cartier otherwise (a prime divisor on a `ℚ`-factorial variety),
the statement quantifies over that proof. The degree of an ample Cartier divisor `H` on a curve
is `MMP.Mori.degreeOn` of its invertible sheaf `𝒪_X(H)`. Points of `Ex(f)` are closed points,
the points of the variety in the sense of the source.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Proposition
  2.5, Lemmas 3.39 and 3.41
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori DivisorWithCoeffs

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Mori

variable {k : Type u} [Field k]

/-! ### Ample divisors and negative definite intersection matrices -/

/-- **Ample divisors are positive on curves.** Let `X` be a variety, `H` an ample Cartier divisor
on `X` and `C ⊆ X` a proper irreducible curve. Then `(H · C) = deg_C 𝒪_X(H) > 0`. -/
@[mmp "lem_km2a_ample_positive_on_curves"]
theorem degreeOn_cartierSheaf_pos_of_isAmple {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : Mori.IsVariety k sX) (H : X.CartierDivisor)
    (hamp : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf H))
    (C : ProperCurve sX) :
    0 < degreeOn k sX C.ι C.dim_le (MMP.CartierDivisor.sheaf H) := by
  haveI : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  haveI := hX.toIsSeparated
  haveI := hX.toLocallyOfFiniteType
  haveI := hX.toQuasiCompact
  haveI : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k (C.ι ≫ sX) C.dim_le _
    (isAmple_pullback_of_isFinite C.ι _
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).mpr hamp))

/-- The generic point of a prime divisor `E` lies in the support of a prime divisor `P` only if
`E = P` (both have codimension one). -/
theorem primeDivisor_eq_of_genericPoint_mem_support {U : Scheme.{u}} [IsLocallyNoetherian U]
    [IsNormal U] (P E : Mori.PrimeDivisor U) (hE : E.genericPoint ∈ P.support) : P = E := by
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

/-- If the stalk of the ideal sheaf of a prime divisor `P` at the generic point of a prime divisor
`E` is generated by a nonzerodivisor `g` whose image in the function field is `φ`, then the
coefficient of `E` in `1 · P` is `ord_E φ`. -/
theorem coeff_single_eq_ord_of_stalk_eq_span {U : Scheme.{u}} [IsLocallyNoetherian U]
    [IsNormal U] (P E : Mori.PrimeDivisor U) {g : U.presheaf.stalk E.genericPoint}
    (hg : IdealSheafData.stalk P.idealSheaf E.genericPoint = Ideal.span {g})
    (hnzd : g ∈ nonZeroDivisors (U.presheaf.stalk E.genericPoint)) {φ : (RationalFunctions U)ˣ}
    (key : E.toComponent.hom g = (φ : RationalFunctions U) E.component) :
    coeff (Finsupp.single P 1 : Divisor U) E = E.ord φ := by
  classical
  haveI := P.integral
  by_cases hEP : P = E
  · subst hEP
    rw [coeff_single_self]
    have hmem : P.genericPoint ∈ P.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hprime : Prime g := by
      rw [← Ideal.span_singleton_prime (nonZeroDivisors.ne_zero hnzd), ← hg]
      obtain ⟨y', hy'⟩ : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hmem
      rw [← hy', ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
      exact RingHom.ker_isPrime _
    exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
  · rw [coeff_single_of_ne hEP]
    have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
      P.idealSheaf _).2 fun h => hEP (primeDivisor_eq_of_genericPoint_mem_support P E h)
    rw [hg, Ideal.span_singleton_eq_top] at htop
    exact (E.ord_eq_zero_of_isUnit htop key).symm

/-- **Prime divisors are Cartier when the local rings are factorial.** On a locally Noetherian
normal scheme `U` whose stalks are unique factorization domains, the ideal sheaf of a prime divisor
`P` is an effective Cartier divisor, locally generated by one section `f`, and the rational
function `f` is a local equation of `1 · P`. -/
theorem isCartier_single_of_forall_uniqueFactorizationMonoid {U : Scheme.{u}}
    [IsLocallyNoetherian U] [IsNormal U]
    (hUFD : ∀ x : U, UniqueFactorizationMonoid (U.presheaf.stalk x)) (P : Mori.PrimeDivisor U) :
    Divisor.IsCartier (Finsupp.single P 1 : Divisor U) := by
  classical
  haveI := P.integral
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid P.idealSheaf
      P.codimension_one (fun x _ => hUFD x)
  intro x
  obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf hcart x
  have hnzd : ∀ y (hy : y ∈ W), (U.presheaf.germ W y hy).hom f ∈
      nonZeroDivisors (U.presheaf.stalk y) := fun y hy =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hW hf y hy
  let u : ∀ Z : irreducibleComponents U, (U.presheaf.stalk (componentGenericPoint U Z))ˣ :=
    fun Z => if h : componentGenericPoint U Z ∈ W then
      (by
        letI := (RationalFunctions.isField_stalk U Z).toField
        exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit)
      else 1
  let φ : (RationalFunctions U)ˣ := (RationalFunctions.unitsEquiv U).symm u
  refine ⟨W, hxW, φ, ?_⟩
  rintro E ⟨y, hyE, hyW⟩
  have hηW : E.genericPoint ∈ W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
  have hZW : componentGenericPoint U E.component ∈ W :=
    E.specializes_genericPoint.mem_open W.isOpen hηW
  have hφ : (φ : RationalFunctions U) E.component =
      (U.presheaf.germ W _ hZW).hom f := by
    change ((u E.component : (U.presheaf.stalk (componentGenericPoint U E.component))ˣ) :
      U.presheaf.stalk (componentGenericPoint U E.component)) = _
    simp only [u]
    rw [dif_pos hZW]
    rfl
  refine coeff_single_eq_ord_of_stalk_eq_span P E ?_ (hnzd _ hηW) ?_
  · rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf _ ⟨W, hW⟩ hηW, hspan,
      Ideal.map_span, Set.image_singleton]
  · rw [hφ]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- **Prime divisors on a smooth scheme are Cartier.** On a scheme `U` smooth over `k`, the local
rings are regular, hence unique factorization domains, so every prime divisor `P` is Cartier by
`MMP.Threefold.Mori.isCartier_single_of_forall_uniqueFactorizationMonoid`. -/
theorem isCartier_single_of_isSmoothScheme {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)}
    [IsLocallyNoetherian U] [IsNormal U] (hsm : IsSmoothScheme sU) (P : Mori.PrimeDivisor U) :
    Divisor.IsCartier (Finsupp.single P 1 : Divisor U) := by
  refine isCartier_single_of_forall_uniqueFactorizationMonoid (fun x => ?_) P
  have hx : x ∈ smoothLocus sU := by
    rw [hsm]
    trivial
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 hx
  haveI : Smooth (V.ι ≫ sU) := hV
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sU) ⟨x, hxV⟩
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (V.toScheme.presheaf.stalk ⟨x, hxV⟩)
  exact MulEquiv.uniqueFactorizationMonoid
    (V.stalkIso ⟨x, hxV⟩).commRingCatIsoToRingEquiv.toMulEquiv inferInstance

/-- **Prime divisors on a smooth scheme are `ℚ`-Cartier**, by
`MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme`. -/
theorem isQCartier_single_of_isSmoothScheme {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)}
    [IsLocallyNoetherian U] [IsNormal U] (hsm : IsSmoothScheme sU) (P : Mori.PrimeDivisor U) :
    (Divisor.toQDivisor (Finsupp.single P 1)).IsQCartier :=
  QDivisor.isQCartier_toQDivisor (isCartier_single_of_isSmoothScheme hsm P)

section EffectiveDegree

open Opposite Stacks.ModuleStalk

/-- For an effective divisor `D`, the map `𝒪_X → 𝒪_X(D)` factors as the map `𝒪_X → 𝒪_X(0)`
followed by the inclusion `𝒪_X(0) → 𝒪_X(D)`. -/
theorem structureSheafToDivisorialSheaf_eq_comp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} (hD : 0 ≤ D) :
    Divisor.structureSheafToDivisorialSheaf hD =
      Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor X)) ≫
        Divisor.divisorialSheafInclusion hD := by
  unfold Divisor.structureSheafToDivisorialSheaf
  refine Eq.trans ?_ (SheafOfModules.unitHomEquiv_symm_comp _ _).symm
  congr 1

/-- A morphism of `𝒪_X`-modules commutes with restriction of sections along `V ≤ U`. -/
theorem app_map_eq {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) {U V : X.Opens} (i : V ⟶ U)
    (t : Γ(F, U)) : f.app V (F.presheaf.map i.op t) = G.presheaf.map i.op (f.app U t) :=
  ConcreteCategory.congr_hom (f.mapPresheaf.naturality i.op) t

/-- A morphism of modules that is bijective on sections over every open inside `W` is bijective
on stalks at the points of `W`. -/
theorem bijective_mapFun_of_app_bijective_le {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    {W : X.Opens} {x : X} (hx : x ∈ W) (h : ∀ V : X.Opens, V ≤ W → Function.Bijective (f.app V)) :
    Function.Bijective (mapFun f x) := by
  constructor
  · intro m m' hmm'
    obtain ⟨U₁, h₁, t₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
    obtain ⟨U₂, h₂, t₂, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m'
    rw [mapFun_germ, mapFun_germ] at hmm'
    obtain ⟨V, hxV, i₁, i₂, hV⟩ := TopCat.Presheaf.germ_eq G.presheaf x h₁ h₂ _ _ hmm'
    have hxV' : x ∈ V ⊓ W := ⟨hxV, hx⟩
    let j : V ⊓ W ⟶ V := homOfLE inf_le_left
    have key : F.presheaf.map j.op (F.presheaf.map i₁.op t₁) =
        F.presheaf.map j.op (F.presheaf.map i₂.op t₂) := by
      apply (h (V ⊓ W) inf_le_right).1
      simp only [app_map_eq]
      exact congrArg (G.presheaf.map j.op) hV
    rw [← TopCat.Presheaf.germ_res_apply _ i₁ x hxV, ← TopCat.Presheaf.germ_res_apply _ j x hxV',
      ← TopCat.Presheaf.germ_res_apply _ i₂ x hxV, ← TopCat.Presheaf.germ_res_apply _ j x hxV', key]
  · intro n
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf n
    have hxU : x ∈ U ⊓ W := ⟨hU, hx⟩
    let j : U ⊓ W ⟶ U := homOfLE inf_le_left
    obtain ⟨t, ht⟩ := (h (U ⊓ W) inf_le_right).2 (G.presheaf.map j.op s)
    refine ⟨(F.presheaf.germ (U ⊓ W) x hxU).hom t, ?_⟩
    rw [mapFun_germ, ht, TopCat.Presheaf.germ_res_apply]

open scoped Stacks.ModuleStalk in
/-- If a morphism of modules `f : F ⟶ G` is bijective on sections over every open inside `W`,
then for `x ∈ W` the germ of `f s` lies in `𝔪_x G_x` iff the germ of `s` lies in `𝔪_x F_x`. -/
theorem mem_maximalSmul_germ_iff_of_app_bijective_le {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) {W : X.Opens} {x : X} (hx : x ∈ W)
    (h : ∀ V : X.Opens, V ≤ W → Function.Bijective (f.app V)) (s : Γ(F, ⊤)) :
    (G.presheaf.Γgerm x).hom (f.app ⊤ s) ∈ maximalSmul G x ↔
      (F.presheaf.Γgerm x).hom s ∈ maximalSmul F x := by
  rw [← mapFun_Γgerm f x s]
  exact (Stacks.NonvanishingPullback.mem_ideal_smul_top_iff_of_linearEquiv
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (LinearEquiv.ofBijective (map f x) (bijective_mapFun_of_app_bijective_le f hx h))
    ((F.presheaf.Γgerm x).hom s)).symm

/-- The canonical global section `1` of `𝒪_X(D)` for an effective divisor `D`. -/
noncomputable def oneSection {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (hD : 0 ≤ D) :
    Γ(D.divisorialSheaf, ⊤) :=
  (Divisor.structureSheafToDivisorialSheaf hD).app ⊤ (1 : Γ(X, ⊤))

/-- For an effective divisor `D`, the map `𝒪_X → 𝒪_X(D)` is bijective on sections over every
open set disjoint from the support of `D`. -/
theorem structureSheaf_app_bijective_of_le {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (hD : 0 ≤ D) (V : X.Opens) (hV : ∀ x ∈ V, x ∉ D.supp) :
    Function.Bijective ((Divisor.structureSheafToDivisorialSheaf hD).app V) := by
  rw [structureSheafToDivisorialSheaf_eq_comp hD, Scheme.Modules.Hom.comp_app]
  have h1 : Function.Bijective ((Divisor.structureSheafToDivisorialSheaf
      (le_refl (0 : Divisor X))).app V) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  have h2 : Function.Bijective ((Divisor.divisorialSheafInclusion hD).app V) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    exact Divisor.isIso_divisorialSheafInclusion_app hD (fun E ⟨x, hxE, hxU⟩ => by
      rw [DivisorWithCoeffs.coeff_zero]
      by_contra hne
      exact hV x hxU (DivisorWithCoeffs.support_subset_supp (Ne.symm hne) hxE))
  exact h2.comp h1

/-- The canonical section `1` of `𝒪_X(D)` does not vanish at points outside the support of `D`. -/
theorem mem_nonvanishingLocus_oneSection_of_notMem_supp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} (hD : 0 ≤ D) {x : X} (hx : x ∉ D.supp) :
    x ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf (oneSection hD) := fun hmem =>
  Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one X x _ rfl
    ((mem_maximalSmul_germ_iff_of_app_bijective_le (Divisor.structureSheafToDivisorialSheaf hD)
      (W := ⟨(D.supp : Set X)ᶜ, D.supp.isClosed.isOpen_compl⟩) hx
      (fun V hV => structureSheaf_app_bijective_of_le hD V (fun y hy => hV hy))
      (1 : Γ(X, ⊤))).1 hmem)

/-- The restriction of the canonical section `1` of `𝒪_X(D)` to an open `V` is the rational
function `1` on every component meeting `V`. -/
theorem oneSection_restrict_apply {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (hD : 0 ≤ D) (V : X.Opens)
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V}) :
    ((D.divisorialSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (oneSection hD) :
      D.divisorialSubmodule V).1) Z = 1 := by
  have e1 := congrFun (Divisor.coe_structureSheafToDivisorialSheaf_app hD ⊤ (1 : Γ(X, ⊤)))
    ⟨Z.1, trivial⟩
  change ((rationalFunctionsPresheaf X).map (homOfLE (le_top : V ≤ ⊤)).op
    (((oneSection hD : D.divisorialSubmodule ⊤)).1)) Z = 1
  rw [rationalFunctionsPresheaf_map_apply]
  exact e1.trans (map_one (X.presheaf.germ ⊤ (componentGenericPoint X Z.1) trivial).hom)

/-- A local equation `ψ` on `V` of an effective divisor `D` is a section of `𝒪_X` over `V`. -/
theorem isDivisorialSection_zero_of_isLocalEquation {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} (hD : 0 ≤ D) {V : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation V ψ) :
    (0 : Divisor X).IsDivisorialSection V
      (fun Z => (ψ : RationalFunctions X) Z.1 :
        ToType ((rationalFunctionsPresheaf X).obj (op V))) := by
  intro E' h'
  refine Or.inr ?_
  change WithZero.exp (-(DivisorWithCoeffs.coeff (0 : Divisor X) E')) ≤
    E'.valuation ((ψ : RationalFunctions X) E'.component)
  rw [DivisorWithCoeffs.coeff_zero, neg_zero, E'.valuation_component, WithZero.exp_le_exp,
    ← hψ E' h']
  exact hD E'

/-- If a section `a` over `V` agrees at the generic point of a prime divisor `E` with a rational
function `ψ` of positive order along `E`, then the germ of `a` at any `x ∈ E ∩ V` lies in `𝔪_x`. -/
theorem germ_mem_maximalIdeal_of_ord_pos {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {V : X.Opens} {x : X} (hxV : x ∈ V) (a : Γ(X, V)) {E : Mori.PrimeDivisor X}
    (hxE : x ∈ E.support) {ψ : (RationalFunctions X)ˣ} (hpos : 0 < E.ord ψ)
    (ha : ∀ hZ : componentGenericPoint X E.component ∈ V,
      X.presheaf.germ V (componentGenericPoint X E.component) hZ a =
        (ψ : RationalFunctions X) E.component) :
    (X.presheaf.germ V x hxV).hom a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have hspec : E.genericPoint ⤳ x := specializes_iff_mem_closure.mpr (by
    rw [← PrimeDivisor.support_eq_closure]
    exact hxE)
  have hη : E.genericPoint ∈ V := hspec.mem_open V.isOpen hxV
  by_contra hnm
  have hu' : IsUnit ((X.presheaf.germ V E.genericPoint hη).hom a) := by
    have := (IsLocalRing.notMem_maximalIdeal.mp hnm).map (X.presheaf.stalkSpecializes hspec).hom
    rwa [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] at this
  have hkey : E.toComponent.hom ((X.presheaf.germ V E.genericPoint hη).hom a) =
      (ψ : RationalFunctions X) E.component := by
    rw [← ha (E.componentGenericPoint_mem_of_nonempty ⟨x, hxE, hxV⟩)]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  have h0 := E.ord_eq_zero_of_isUnit hu' hkey
  omega

open scoped Stacks.ModuleStalk in
/-- For an effective Cartier divisor `D`, the canonical section `1` of `𝒪_X(D)` vanishes at every
point of the support of `D`. -/
theorem germ_oneSection_mem_maximalSmul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (hD : 0 ≤ D) (hC : D.IsCartier) {x : X} (hx : x ∈ D.supp) :
    (D.divisorialSheaf.presheaf.Γgerm x).hom (oneSection hD) ∈ maximalSmul D.divisorialSheaf x := by
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hx
  obtain ⟨V, hxV, ψ, hψ⟩ := hC x
  have hDE : 0 < D.coeff E := lt_of_le_of_ne (hD E) (Ne.symm hE)
  have hEψ : E.ord ψ = D.coeff E := (hψ E ⟨x, hxE, hxV⟩).symm
  let ψV : ToType ((rationalFunctionsPresheaf X).obj (op V)) :=
    fun Z => (ψ : RationalFunctions X) Z.1
  have hψV : (0 : Divisor X).IsDivisorialSection V ψV :=
    isDivisorialSection_zero_of_isLocalEquation hD hψ
  obtain ⟨a, ha⟩ := Divisor.IsDivisorialSection.exists_eq hψV
  let tV : D.divisorialSubmodule V :=
    ⟨fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1, by
      intro E' h'
      refine Or.inr ?_
      change WithZero.exp (-(D.coeff E')) ≤
        E'.valuation (((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E'.component)
      rw [E'.valuation_component, WithZero.exp_le_exp, PrimeDivisor.ord_inv, ← hψ E' h']⟩
  have hσ : D.divisorialSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (oneSection hD) =
      (a • tV : D.divisorialSubmodule V) := by
    apply Subtype.ext
    funext Z
    have h2 : X.presheaf.germ V _ Z.2 a = (ψ : RationalFunctions X) Z.1 := congrFun ha Z
    rw [oneSection_restrict_apply hD V Z]
    have hR : ((a • tV : D.divisorialSubmodule V).1) Z =
        X.presheaf.germ V _ Z.2 a * tV.1 Z := rationalFunctions_smul_apply a tV.1 Z
    rw [hR]
    change (1 : X.presheaf.stalk (componentGenericPoint X Z.1)) =
      X.presheaf.germ V _ Z.2 a * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1
    rw [h2]
    change (1 : X.presheaf.stalk (componentGenericPoint X Z.1)) =
      ((ψ : RationalFunctions X) * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) Z.1
    rw [← Units.val_mul, mul_inv_cancel]
    rfl
  have hma := germ_mem_maximalIdeal_of_ord_pos hxV a hxE (by rwa [hEψ])
    fun hZ => congrFun ha ⟨E.component, hZ⟩
  have hg : (D.divisorialSheaf.presheaf.Γgerm x).hom (oneSection hD) =
      (D.divisorialSheaf.presheaf.germ V x hxV).hom
        (D.divisorialSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (oneSection hD)) := by
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  rw [hg, hσ]
  have hs := Stacks.ModuleStalk.germ_smul D.divisorialSheaf x V hxV a tV
  refine (show (D.divisorialSheaf.presheaf.germ V x hxV).hom (a • tV) = _ from hs) ▸ ?_
  exact Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal hma _

section SectionDegree

variable {C X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X)
  [IsProper (i ≫ sX)] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1)
  (M : X.Modules) (σ : Γ(M, ⊤))
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]

/-- The nonvanishing locus of the pulled-back section on `C` is the preimage of that of `σ`. -/
theorem nonvanishingLocus_pullbackSection :
    Stacks.SheafOfModules.nonvanishingLocus (X := C.toRingedSpace)
      ((Scheme.Modules.pullback i).obj M)
      ((Stacks.NonvanishingSpelling.sectionsEquiv C ((Scheme.Modules.pullback i).obj M)).symm
        (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ)) =
      i ⁻¹' Stacks.Ample.nonvanishingLocus M σ :=
  (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq C _ _).trans
    (Stacks.NonvanishingPullback.preimage_nonvanishingLocus i M σ).symm

omit [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] in
/-- If `σ` does not vanish at some point of the image of `C`, then its pullback to `C` is a
nonzero global section. -/
theorem eval_pullbackSection_ne_zero (hc : ∃ c : C, i c ∈ Stacks.Ample.nonvanishingLocus M σ) :
    ((Stacks.NonvanishingSpelling.sectionsEquiv C ((Scheme.Modules.pullback i).obj M)).symm
        (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ)).eval (op ⊤) ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := hc
  have h1 : Stacks.NonvanishingPullback.pullbackGlobalSection i M σ = 0 :=
    (Equiv.apply_symm_apply
      (Stacks.NonvanishingSpelling.sectionsEquiv C ((Scheme.Modules.pullback i).obj M))
      (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ)).symm.trans
      ((Stacks.NonvanishingSpelling.sectionsEquiv_apply C
        ((Scheme.Modules.pullback i).obj M) _).trans h0)
  have h2 : i ⁻¹' Stacks.Ample.nonvanishingLocus M σ = Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback i).obj M)
      (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ) :=
    Stacks.NonvanishingPullback.preimage_nonvanishingLocus i M σ
  have h3 : Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback i).obj M)
      (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ) = ∅ := by
    rw [h1]
    exact Stacks.Ample.nonvanishingLocus_zero _
  rw [h3] at h2
  exact (h2 ▸ hc : c ∈ (∅ : Set C))

/-- If the canonical section `σ` of `M` does not vanish at the image of some point of the curve
`C`, the degree of `i^* M` is nonnegative. -/
theorem invertibleCurveDegree_pullback_nonneg
    (hc : ∃ c : C, i c ∈ Stacks.Ample.nonvanishingLocus M σ) :
    0 ≤ invertibleCurveDegree k (i ≫ sX) hdim ((Scheme.Modules.pullback i).obj M) := by
  have hL : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj M) := MMP.Mori.isInvertible_pullback_obj i M
  exact invertibleCurveDegree_nonneg_of_eval_top_ne_zero (hL := hL) k (i ≫ sX) hdim _ _
    (eval_pullbackSection_ne_zero i M σ hc)

/-- If moreover the canonical section vanishes at the image of some point of `C`, the degree of
`i^* M` is positive. -/
theorem invertibleCurveDegree_pullback_pos
    (hc : ∃ c : C, i c ∈ Stacks.Ample.nonvanishingLocus M σ)
    (hz : ∃ c : C, i c ∉ Stacks.Ample.nonvanishingLocus M σ) :
    0 < invertibleCurveDegree k (i ≫ sX) hdim ((Scheme.Modules.pullback i).obj M) := by
  have hL : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj M) := MMP.Mori.isInvertible_pullback_obj i M
  have hs := eval_pullbackSection_ne_zero i M σ hc
  refine invertibleCurveDegree_pos_of_nonempty_zeroScheme (hL := hL) k (i ≫ sX) hdim _ _ hs ?_
  refine nonempty_zeroScheme_subscheme_of_exists_notMem_nonvanishingLocus _ _ hs ?_
  obtain ⟨c, hc'⟩ := hz
  exact ⟨c, by rwa [nonvanishingLocus_pullbackSection]⟩

/-- If the canonical section does not vanish at the image of any point of `C`, `i^* M` is
trivial, of degree `0`. -/
theorem invertibleCurveDegree_pullback_eq_zero
    (hall : ∀ c : C, i c ∈ Stacks.Ample.nonvanishingLocus M σ) :
    invertibleCurveDegree k (i ≫ sX) hdim ((Scheme.Modules.pullback i).obj M) = 0 := by
  have hL : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj M) := MMP.Mori.isInvertible_pullback_obj i M
  have huniv : Stacks.SheafOfModules.nonvanishingLocus (X := C.toRingedSpace)
      ((Scheme.Modules.pullback i).obj M)
      ((Stacks.NonvanishingSpelling.sectionsEquiv C ((Scheme.Modules.pullback i).obj M)).symm
        (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ)) = Set.univ := by
    rw [nonvanishingLocus_pullbackSection]
    exact Set.eq_univ_of_forall hall
  have hiso := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ
    ((Scheme.Modules.pullback i).obj M) _ huniv
  let e := asIso ((SheafOfModules.unitHomEquiv ((Scheme.Modules.pullback i).obj M)).symm
      ((Stacks.NonvanishingSpelling.sectionsEquiv C ((Scheme.Modules.pullback i).obj M)).symm
        (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ)))
  rw [← invertibleCurveDegree_eq_of_iso k (i ≫ sX) hdim e]
  simp [invertibleCurveDegree]

end SectionDegree

section Effective

variable {C X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] (i : C ⟶ X) [IsProper (i ≫ sX)]
  [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1)

/-- The nonvanishing locus of the canonical section of `𝒪_X(D)`, for an effective Cartier divisor
`D`, is the complement of `Supp D`. -/
theorem nonvanishingLocus_oneSection {D : Divisor X} (hD : 0 ≤ D) (hC : D.IsCartier) :
    Stacks.Ample.nonvanishingLocus D.divisorialSheaf (oneSection hD) = (D.supp : Set X)ᶜ := by
  ext x
  exact ⟨fun hx hxs => hx (germ_oneSection_mem_maximalSmul hD hC hxs),
    mem_nonvanishingLocus_oneSection_of_notMem_supp hD⟩

/-- **The degree of an effective Cartier divisor on a curve.** Let `D` be an effective Cartier
divisor on a normal scheme `X` and `i : C ⟶ X` a curve (integral, proper over `k`) not contained in
`Supp D`. Then `deg_C 𝒪_X(D) ≥ 0`, with equality if and only if `C ∩ Supp D = ∅`. -/
theorem degreeOn_nonneg_and_eq_zero_iff (D : Divisor X) (hD : D.IsCartier) (heff : 0 ≤ D)
    (hne : ∃ c : C, i c ∉ D.supp) :
    0 ≤ D.degreeOn k sX i hdim hD ∧
      (D.degreeOn k sX i hdim hD = 0 ↔ ∀ c : C, i c ∉ D.supp) := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hD.isInvertibleModule_divisorialSheaf
  have hloc := nonvanishingLocus_oneSection heff hD
  obtain ⟨c, hc⟩ := hne
  have hc : ∃ c : C, i c ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf (oneSection heff) :=
    ⟨c, by rwa [hloc]⟩
  refine ⟨invertibleCurveDegree_pullback_nonneg sX i hdim _ _ hc, fun h0 c hcs => ?_,
    fun hall => invertibleCurveDegree_pullback_eq_zero sX i hdim _ _ fun c => by
      rw [hloc]
      exact hall c⟩
  exact (invertibleCurveDegree_pullback_pos sX i hdim _ _ hc
    ⟨c, by simpa [hloc] using hcs⟩).ne' h0

end Effective

end EffectiveDegree

/-- The linear algebra of KM 3.41(1): if `-N` is positive definite, the off-diagonal entries of
`N` are nonnegative and the sums `∑ᵢ aᵢ Nᵢⱼ` are nonnegative, then every `aᵢ ≤ 0`. -/
theorem le_zero_of_posDef_neg_of_offDiag_nonneg {r : ℕ} (N : Matrix (Fin r) (Fin r) ℝ)
    (hneg : (-N).PosDef) (hoff : ∀ i j, i ≠ j → 0 ≤ N i j) (a : Fin r → ℝ)
    (hA : ∀ j, 0 ≤ ∑ i, a i * N i j) : ∀ i, a i ≤ 0 := by
  classical
  set b : Fin r → ℝ := fun i => max (a i) 0 with hb
  set c : Fin r → ℝ := fun i => max (-a i) 0 with hc
  have hbc : ∀ i, b i = a i + c i ∧ (b i = 0 ∨ c i = 0) := by
    intro i
    simp only [hb, hc]
    rcases le_total (a i) 0 with h | h <;> simp [h]
  have hcol : ∀ j, b j ≠ 0 → 0 ≤ ∑ i, b i * N i j := by
    intro j hj
    have hcj : c j = 0 := (hbc j).2.resolve_left hj
    have : ∑ i, b i * N i j = ∑ i, a i * N i j + ∑ i, c i * N i j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [(hbc i).1, add_mul]
    rw [this]
    refine add_nonneg (hA j) (Finset.sum_nonneg fun i _ => ?_)
    by_cases hij : i = j
    · simp [hij, hcj]
    · exact mul_nonneg (le_max_right _ _) (hoff i j hij)
  have hq : 0 ≤ ∑ j, b j * ∑ i, b i * N i j := by
    refine Finset.sum_nonneg fun j _ => ?_
    by_cases hj : b j = 0
    · simp [hj]
    · exact mul_nonneg (le_max_right _ _) (hcol j hj)
  by_contra hcon
  push Not at hcon
  obtain ⟨i0, hi0⟩ := hcon
  have hbne : b ≠ 0 := fun h => by
    have := congrFun h i0
    simp [hb] at this
    linarith
  have hp := hneg.dotProduct_mulVec_pos hbne
  have : (dotProduct (star b) (Matrix.mulVec (-N) b) : ℝ) = - ∑ j, b j * ∑ i, b i * N i j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.neg_apply, star_trivial, Finset.mul_sum, mul_neg,
      Finset.sum_neg_distrib]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  linarith

/-- The generic point of a proper curve lies on its own closure. -/
theorem exists_ι_eq_point {X : Scheme.{u}} (x : X) :
    ∃ c : curveSubschemeAt x, curveSubschemeAtι x c = x := by
  have : x ∈ Set.range (curveSubschemeAtι x) := by
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact subset_closure rfl
  exact this

/-- The intersection number of a prime divisor on a smooth scheme with a proper curve not
contained in it is nonnegative. -/
theorem intersectionNumber_single_nonneg {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)}
    [QuasiCompact sU] [IsLocallyNoetherian U] [IsNormal U] (hsm : IsSmoothScheme sU)
    (P : Mori.PrimeDivisor U) (C : ProperCurve sU) (hC : C.point ∉ P.support) :
    0 ≤ ((Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sU C.ι C.dim_le
      (isQCartier_single_of_isSmoothScheme hsm P) : ℚ) := by
  classical
  haveI : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  haveI := C.isProper_ι_comp
  have hcart := isCartier_single_of_isSmoothScheme hsm P
  rw [QDivisor.intersectionNumber_toQDivisor k sU C.ι C.dim_le _ hcart
    (isQCartier_single_of_isSmoothScheme hsm P)]
  have heff : 0 ≤ (Finsupp.single P 1 : Divisor U) := by
    intro E
    by_cases h : P = E <;> simp [Finsupp.single_apply, h]
  obtain ⟨c, hc⟩ := exists_ι_eq_point C.point
  have hne : ∃ c : C.scheme, C.ι c ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor U) := by
    refine ⟨c, ?_⟩
    change curveSubschemeAtι C.point c ∉ _
    rw [hc]
    intro hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
    have hEP : E = P := by
      by_contra hne
      exact hE (coeff_single_of_ne (Ne.symm hne) 1)
    exact hC (hEP ▸ hxE)
  exact_mod_cast (degreeOn_nonneg_and_eq_zero_iff sU C.ι C.dim_le _ hcart heff hne).1

/-- **KM Lemma 3.41(1).** Let `U` be a smooth surface and `C₁, …, C_r` distinct proper
irreducible curves on `U` (the prime divisors `Pᵢ`, with `Cᵢ` the curve of generic point that of
`Pᵢ`), such that the intersection matrix `(Cᵢ · Cⱼ)` is symmetric and negative definite. Let
`A = ∑ aᵢ Cᵢ` with `aᵢ ∈ ℝ`, so that `(A · Cⱼ) = ∑ᵢ aᵢ (Cᵢ · Cⱼ)`, and assume `(A · Cⱼ) ≥ 0` for
every `j`. Then `aᵢ ≤ 0` for every `i`. The curves `Cᵢ` are Cartier on `U`
(`MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme`), which defines `(Cᵢ · Cⱼ)`. -/
@[mmp "lem_km2a_negative_definite_nonneg_on_curves_coefficients_nonpos"]
theorem coeff_nonpos_of_negDef_of_intersectionNumber_nonneg {U : Scheme.{u}}
    {sU : U ⟶ Spec (.of k)} [QuasiCompact sU] [IsLocallyNoetherian U] [IsNormal U]
    (hU : Mori.IsVariety k sU) (hsm : IsSmoothScheme sU) (hdim : topologicalKrullDim U = 2)
    {r : ℕ} (P : Fin r → Mori.PrimeDivisor U) (hP : Function.Injective P)
    (C : Fin r → ProperCurve sU) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (a : Fin r → ℝ)
    (hneg : (-(Matrix.of fun i j : Fin r =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sU (C j).ι
        (C j).dim_le (isQCartier_single_of_isSmoothScheme hsm (P i)) : ℝ))).PosDef)
    (hA : ∀ j, 0 ≤ ∑ i, a i *
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sU (C j).ι
        (C j).dim_le (isQCartier_single_of_isSmoothScheme hsm (P i)) : ℝ)) :
    ∀ i, a i ≤ 0 := by
  refine le_zero_of_posDef_neg_of_offDiag_nonneg _ hneg ?_ a hA
  intro i j hij
  have h := intersectionNumber_single_nonneg (k := k) hsm (P i) (C j) (by
    rw [hC j]
    intro hmem
    exact hij (hP (primeDivisor_eq_of_genericPoint_mem_support (P i) (P j) hmem)))
  change (0 : ℝ) ≤ ((_ : ℚ) : ℝ)
  exact_mod_cast h

end MMP.Threefold.Mori
