module

import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
public import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.ReducedSncBoundary
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.Vanishing.SncFundamentalInjectivity
public import MMP.AlgebraicGeometry.Vanishing.ReidFukuda
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.LogResolution.RoundUpPushforward
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.MorphismToRelativeProj

universe u

section

/-!
# Injectivity for an snc log canonical pair with a semiample adjoint difference

Let `V` be a smooth projective complex variety, `B` a `ℚ`-divisor with simple normal crossing
support and coefficients in `[0, 1]`, `M` a divisor with `M ∼_ℚ K_V + B + H` for a semiample `H`,
and `D ≥ 0` a divisor with `tH ∼_ℚ D + D'` (`t > 0`, `D' ≥ 0`) such that neither `Supp D` nor
`Supp D'` contains a stratum of `⌊B⌋`. Then `H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))` is injective.

Take an snc-preserving log resolution `g : V' ⟶ V` of `Supp (B + D + D')`; it is an isomorphism
over `U = V ∖ Supp (D + D')`, which contains the generic point of every stratum of `⌊B⌋`. Let
`Δ_Y` be the crepant boundary of `(V, B)` on `V'`. By the snc lower bound for discrepancies, an
exceptional prime of discrepancy `≤ -1` has as centre the generic point of a stratum of `⌊B⌋`,
which lies in `U`; so `coeff Δ_Y < 1` along exceptional primes. With `E = ⌈B_g⌉` the round-up of
the positive part of the discrepancy, `Γ = Δ_Y + E` has coefficients in `[0, 1]` and its
coefficient-one part consists of strict transforms of components of `⌊B⌋`. A general member `H'`
of the free system of `mH`, pulled back to `V'`, is reduced and snc with everything else, and for
small `ε > 0` the boundary `Δ = Γ + (ε/t) g^*(D + D') + ((1 - ε)/m) H'` is snc with coefficients
in `[0, 1]`, contains `Supp g^*D` in the support of its fractional part, has the same floor as
`Γ`, and `M' = g^*M + E ∼_ℚ K_{V'} + Δ`. Fundamental injectivity on `V'` gives the injectivity of
`H^q(V', 𝒪(M')) ⟶ H^q(V', 𝒪(M' + g^*D))`. The difference `M' - (K_{V'} + Δ)` is `ℚ`-linearly
trivial, hence nef, and no stratum of `⌊Δ⌋` lies in the exceptional set, so `Rⁱ g_* 𝒪(M') = 0`
for `i > 0` (Reid–Fukuda). Pulling back rational functions gives maps
`𝒪_V(M) ⟶ g_* 𝒪_{V'}(M')` and `𝒪_V(M + D) ⟶ g_* 𝒪_{V'}(M' + g^*D)` commuting with the inclusions,
the first an isomorphism since `E` vanishes along strict transforms; Leray then identifies the
injectivity on `V'` with that on `V`.

## Main results

* `MMP.Mori.injective_derivedCohomologyOverField_map_divisorialSheafInclusion_of_semiample`:
  the injectivity of `H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))`.

## Implementation notes

The comparison along `g` is a commutative square in the derived category of `V`: the map
`𝒪_V(M)[0] ⟶ Rg_*(𝒪_{V'}(M')[0])` is an isomorphism, because `𝒪_V(M) ⟶ g_* 𝒪_{V'}(M')` is one and
`𝒪_{V'}(M')` has no higher direct images. Only the higher direct images of `𝒪_{V'}(M')` are
needed. Those of `𝒪_{V'}(M' + g^*D)` are not, so the projection formula for `𝒪(M') ⊗ g^*𝒪(D)`
does not enter. The pull-back of `ℚ`-divisors along `g` is the `ℚ`-linear extension of the
Cartier pull-back of prime divisors, which is available because every divisor on the smooth `V`
is Cartier.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011],
  Theorem 6.1
* [F. Ambro, *Quasi-log varieties*][Ambro2003]
-/

namespace MMP.FourfoldProofs.MmpLcBpfSemiampleInjectivityProof

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

/-! ### The derived comparison along a morphism with acyclic target sheaf -/

section Derived

section SingleUnit

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
  [Rw.CommShift ℤ] [Rw.IsTriangulated]
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [EnoughInjectives A] [PreservesFiniteLimits w]

/-- The comparison `w(X)[0] ⟶ Rw(X[0])` given by the unit `α` of a right derived functor of a
left exact `w` is an isomorphism at an object `X` with `Rⁿw(X) = 0` for `n > 0`. -/
private theorem isIso_mapSingleQhIso_inv_comp_unit_app (hGE : ∀ X : A,
      (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : ∀ n : ℕ, 0 < n → Limits.IsZero ((w.rightDerived n).obj X)) :
    IsIso ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app X ≫
      α.app ((HomotopyCategory.singleFunctor A 0).obj X) ≫
        Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app X)) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h₁ : Limits.IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj X))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    have := hGE X
    have h₂ : Limits.IsZero ((DerivedCategory.homologyFunctor B n).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  · have := Stacks.DerivedFunctor.isIso_singleUnitHomology_app w Rw α hGE
      (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective w Rw α hres J hJ) X
    have e : (DerivedCategory.homologyFunctor B 0).map
        ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app X ≫
          α.app ((HomotopyCategory.singleFunctor A 0).obj X) ≫
            Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app X)) =
        (DerivedCategory.homologyFunctor B 0).map
            ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app X) ≫
          (Stacks.DerivedFunctor.singleUnitHomology w Rw α 0).app X ≫
            (DerivedCategory.homologyFunctor B 0).map
              (Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app X)) := by
      simp only [Functor.map_comp]
      rfl
    rw [e]
    infer_instance
  · have h₁ : Limits.IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj X))) :=
      DerivedCategory.isZero_of_isLE _ 0 n hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
    have h₂ : Limits.IsZero ((DerivedCategory.homologyFunctor B (m : ℤ)).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X))) :=
      (hX m (by exact_mod_cast hn)).of_iso
        ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α hres m).app X)
    exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

end SingleUnit

/-- **Leray**: `RΓ(X, Rf_* -) ≅ RΓ(Y, -)` over `k`, for `g : Y ⟶ X` and `X` over `k`. -/
private noncomputable def lerayIso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) :
    Stacks.Duality.derivedPushforward g ⋙ derivedGlobalSectionsOver sX ≅
      derivedGlobalSectionsOver (g ≫ sX) :=
  Functor.isoWhiskerLeft _ (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k sX) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.Duality.derivedPushforwardCompIso g sX) _ ≪≫
    (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k (g ≫ sX)).symm

/-- **Injectivity descends along a morphism with acyclic comparison.** Let `g : Y ⟶ X` be a
morphism of schemes over a field `k`, `ι : F₁ ⟶ F₂` a map of `𝒪_X`-modules and `ι' : G₁ ⟶ G₂`
one of `𝒪_Y`-modules, with maps `uᵢ : Fᵢ ⟶ g_* Gᵢ` such that `ι ≫ u₂ = u₁ ≫ g_* ι'`. If `u₁` is
an isomorphism, `Rⁱ g_* G₁ = 0` for `i > 0`, and `H^q(Y, ι')` is injective, then `H^q(X, ι)` is
injective. -/
private theorem injective_homology_map_of_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) {F₁ F₂ : X.Modules} (ι : F₁ ⟶ F₂) {G₁ G₂ : Y.Modules}
    (ι' : G₁ ⟶ G₂) (u₁ : F₁ ⟶ (Scheme.Modules.pushforward g).obj G₁)
    (u₂ : F₂ ⟶ (Scheme.Modules.pushforward g).obj G₂)
    (hcomm : ι ≫ u₂ = u₁ ≫ (Scheme.Modules.pushforward g).map ι') [IsIso u₁]
    (hvan : ∀ i : ℕ, 0 < i →
      Limits.IsZero (((Scheme.Modules.pushforward g).rightDerived i).obj G₁)) (q : ℤ)
    (hinj : Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map
      ((derivedGlobalSectionsOver (g ≫ sX)).map
        ((DerivedCategory.singleFunctor Y.Modules 0).map ι'))).hom) :
    Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map
      ((derivedGlobalSectionsOver sX).map
        ((DerivedCategory.singleFunctor X.Modules 0).map ι))).hom := by
  -- the comparison `g_*(-)[0] ⟶ Rg_*(-[0])`
  let su : Scheme.Modules.pushforward g ⋙ DerivedCategory.singleFunctor X.Modules 0 ⟶
      DerivedCategory.singleFunctor Y.Modules 0 ⋙ Stacks.Duality.derivedPushforward g :=
    (Stacks.DerivedFunctor.mapSingleQhIso (Scheme.Modules.pushforward g) 0).inv ≫
      Functor.whiskerLeft (HomotopyCategory.singleFunctor Y.Modules 0)
        ((Stacks.Duality.homotopyPushforward g).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))) ≫
      (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh Y.Modules 0)
        (Stacks.Duality.derivedPushforward g)).inv
  have hsu : IsIso (su.app G₁) := by
    have : PreservesFiniteLimits (Scheme.Modules.pushforward g) :=
      have : Limits.PreservesLimitsOfSize.{u, u} (Scheme.Modules.pushforward g) :=
        (Scheme.Modules.pullbackPushforwardAdjunction g).rightAdjoint_preservesLimits
      inferInstance
    exact isIso_mapSingleQhIso_inv_comp_unit_app (Scheme.Modules.pushforward g)
      (Stacks.Duality.derivedPushforward g) _
      (fun M => Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward g)
        ((DerivedCategory.singleFunctor _ 0).obj M) 0)
      (fun K => ⟨(Stacks.Injectives.kInjectiveResolutionFunctor Y.Modules).obj K,
        (Stacks.Injectives.kInjectiveResolutionInclusion Y.Modules).app K, inferInstance,
        inferInstance⟩) _ hvan
  let S := DerivedCategory.singleFunctor X.Modules 0
  let H := derivedGlobalSectionsOver sX ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) q
  -- `S ι ≫ S u₂ ≫ su G₂ = (S u₁ ≫ su G₁) ≫ Rg_*(ι'[0])`
  have hsq : S.map ι ≫ S.map u₂ ≫ su.app G₂ =
      (S.map u₁ ≫ su.app G₁) ≫ (Stacks.Duality.derivedPushforward g).map
        ((DerivedCategory.singleFunctor Y.Modules 0).map ι') := by
    rw [← Category.assoc, ← S.map_comp, hcomm, S.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact su.naturality ι'
  haveI : IsIso (S.map u₁ ≫ su.app G₁) :=
    @IsIso.comp_isIso _ _ _ _ _ (S.map u₁) (su.app G₁) (Functor.map_isIso S u₁) hsu
  have h1 : Function.Injective (H.map (S.map u₁ ≫ su.app G₁)).hom :=
    (ConcreteCategory.bijective_of_isIso (H.map (S.map u₁ ≫ su.app G₁))).1
  have h2 : Function.Injective (H.map ((Stacks.Duality.derivedPushforward g).map
      ((DerivedCategory.singleFunctor Y.Modules 0).map ι'))).hom := by
    set a := (DerivedCategory.singleFunctor Y.Modules 0).map ι'
    have hnat := (lerayIso sX g).hom.naturality a
    have e : H.map ((Stacks.Duality.derivedPushforward g).map a) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map ((lerayIso sX g).hom.app _) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map
            ((derivedGlobalSectionsOver (g ≫ sX)).map a) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map
            ((lerayIso sX g).inv.app _) := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← reassoc_of% hnat]
      simp [H]
    rw [e]
    refine ((ConcreteCategory.bijective_of_isIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map
        ((lerayIso sX g).inv.app _))).1.comp ?_)
    exact hinj.comp (ConcreteCategory.bijective_of_isIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map
        ((lerayIso sX g).hom.app _))).1
  have h3 : Function.Injective (H.map (S.map ι ≫ S.map u₂ ≫ su.app G₂)).hom := by
    rw [hsq, H.map_comp]
    exact h2.comp h1
  rw [H.map_comp] at h3
  exact Function.Injective.of_comp h3

end Derived

/-! ### Pulling back sections of divisorial sheaves along a dominant morphism -/

section PullbackSections

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

private theorem bijective_stalkSpecializes_of_eq {Z : Scheme.{u}} {x y : Z} (h : x ⤳ y)
    (hxy : y = x) : Function.Bijective (Z.presheaf.stalkSpecializes h).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

private theorem map_componentGenericPoint_eq (Z : irreducibleComponents Y) :
    componentGenericPoint X (pointComponent (g (componentGenericPoint Y Z))) =
      g (componentGenericPoint Y Z) := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
    MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]

/-- `𝒪_{X,g(η_Z)} ≅ 𝒪_{X,η}`: `g` maps the generic point of `Y` to that of `X`. -/
private noncomputable def stalkEquiv (Z : irreducibleComponents Y) :
    X.presheaf.stalk (g (componentGenericPoint Y Z)) ≃+*
      X.presheaf.stalk (componentGenericPoint X (pointComponent (g (componentGenericPoint Y Z)))) :=
  RingEquiv.ofBijective (stalkToRationalFunctions X (mem_pointComponent _)).hom
    (bijective_stalkSpecializes_of_eq _ (map_componentGenericPoint_eq g Z).symm)

/-- The pull-back `g^* : K(X) → K(Y)` of rational functions along a dominant morphism of
integral schemes. -/
private noncomputable def pullbackRat : RationalFunctions X →+* RationalFunctions Y :=
  Pi.ringHom fun Z => (g.stalkMap (componentGenericPoint Y Z)).hom.comp
    ((stalkEquiv g Z).symm.toRingHom.comp
      (RationalFunctions.component X (pointComponent (g (componentGenericPoint Y Z)))))

omit [IsIntegral Y] [IsDominant g] in
/-- On an integral scheme every irreducible component has its generic point in each nonempty
open. -/
private theorem componentGenericPoint_mem {U : X.Opens} (hU : (U : Set X).Nonempty)
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∈ U := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

omit [IsIntegral Y] [IsDominant g] in
/-- A section of `𝒦_X` over a nonempty open `U` of the integral scheme `X` is a rational
function. -/
private noncomputable def extendRat (U : X.Opens) (hU : (U : Set X).Nonempty) :
    (rationalFunctionsPresheaf X).obj (Opposite.op U) →+* RationalFunctions X :=
  (RingHom.pi fun Z => Pi.evalRingHom
    (fun Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U} =>
      X.presheaf.stalk (componentGenericPoint X Z.1)) ⟨Z, componentGenericPoint_mem hU Z⟩).comp
    (RingHom.id _)

/-- The pull-back of sections of `𝒦_X` over `U` to sections of `𝒦_Y` over `g⁻¹ U`. -/
private noncomputable def ratPullSec (U : X.Opens) :
    (rationalFunctionsPresheaf X).obj (Opposite.op U) →+*
      (rationalFunctionsPresheaf Y).obj (Opposite.op (g ⁻¹ᵁ U)) :=
  RingHom.pi fun Z' => (Pi.evalRingHom _ Z'.1).comp ((pullbackRat g).comp
    (extendRat U ⟨g (componentGenericPoint Y Z'.1), Z'.2⟩))

private theorem ratPullSec_apply (U : X.Opens)
    (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U))
    (Z' : {Z' : irreducibleComponents Y // componentGenericPoint Y Z' ∈ g ⁻¹ᵁ U}) :
    ratPullSec g U φ Z' = (g.stalkMap (componentGenericPoint Y Z'.1)).hom
      ((stalkEquiv g Z'.1).symm (φ ⟨pointComponent (g (componentGenericPoint Y Z'.1)),
        componentGenericPoint_mem ⟨g (componentGenericPoint Y Z'.1), Z'.2⟩ _⟩)) := rfl

/-- `ratPullSec` commutes with the restriction maps. -/
private theorem ratPullSec_map {U V : X.Opens} (i : V ⟶ U)
    (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U)) :
    ratPullSec g V ((rationalFunctionsPresheaf X).map i.op φ) =
      (rationalFunctionsPresheaf Y).map ((TopologicalSpace.Opens.map g.base).map i).op
        (ratPullSec g U φ) := by
  funext Z'
  rfl

/-- `ratPullSec` sends the germ of a regular function to the germ of its pull-back. -/
private theorem ratPullSec_toRationalFunctionsPresheaf (U : X.Opens) (r : Γ(X, U)) :
    ratPullSec g U ((toRationalFunctionsPresheaf X).app (Opposite.op U) r) =
      (toRationalFunctionsPresheaf Y).app (Opposite.op (g ⁻¹ᵁ U)) (g.app U r) := by
  funext Z'
  rw [ratPullSec_apply, toRationalFunctionsPresheaf_app_apply,
    toRationalFunctionsPresheaf_app_apply]
  have h1 : (stalkEquiv g Z'.1).symm
      ((X.presheaf.germ U (componentGenericPoint X (pointComponent _))
        (componentGenericPoint_mem ⟨g (componentGenericPoint Y Z'.1), Z'.2⟩ _)).hom r) =
      (X.presheaf.germ U (g (componentGenericPoint Y Z'.1)) Z'.2).hom r := by
    rw [RingEquiv.symm_apply_eq]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  rw [h1]
  exact Scheme.Hom.germ_stalkMap_apply g U _ Z'.2 r

variable [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]

/-- `ratPullSec` is linear over `g^♯ : Γ(X, U) → Γ(Y, g⁻¹ U)`. -/
private theorem ratPullSec_smul (U : X.Opens) (r : Γ(X, U))
    (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U)) :
    ratPullSec g U (r • φ) = g.app U r • ratPullSec g U φ := by
  change ratPullSec g U ((toRationalFunctionsPresheaf X).app (Opposite.op U) r * φ) =
    (toRationalFunctionsPresheaf Y).app (Opposite.op (g ⁻¹ᵁ U)) (g.app U r) * ratPullSec g U φ
  rw [map_mul, ratPullSec_toRationalFunctionsPresheaf]

/-- The map `𝒪_X(N) ⟶ g_* 𝒪_Y(N')` pulling back rational functions, for divisors `N`, `N'` such
that pulled-back sections of `𝒪_X(N)` are sections of `𝒪_Y(N')`. -/
private noncomputable def pullbackDivisorialHom (N : Divisor X) (N' : Divisor Y)
    (h : ∀ (U : X.Opens) (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U)),
      N.IsDivisorialSection U φ → N'.IsDivisorialSection (g ⁻¹ᵁ U) (ratPullSec g U φ)) :
    N.divisorialSheaf ⟶ (Scheme.Modules.pushforward g).obj N'.divisorialSheaf :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun φ := ⟨ratPullSec g U.unop φ.1, h U.unop φ.1 φ.2⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' a b := Subtype.ext (map_add _ _ _) }
      naturality U V i := by
        ext φ
        exact Subtype.ext (ratPullSec_map g i.unop φ.1) }
    fun U r φ => Subtype.ext (ratPullSec_smul g U.unop r φ.1)⟩

/-- The pull-back maps commute with the inclusions of divisorial sheaves. -/
private theorem divisorialSheafInclusion_comp_pullbackDivisorialHom {N₁ N₂ : Divisor X}
    {N₁' N₂' : Divisor Y} (hN : N₁ ≤ N₂) (hN' : N₁' ≤ N₂') (h₁ h₂) :
    Divisor.divisorialSheafInclusion hN ≫ pullbackDivisorialHom g N₂ N₂' h₂ =
      pullbackDivisorialHom g N₁ N₁' h₁ ≫
        (Scheme.Modules.pushforward g).map (Divisor.divisorialSheafInclusion hN') := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext φ
  exact Subtype.ext rfl

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- On units, `pullbackRat` is `MMP.Mori.pullbackRationalFunction`. -/
private theorem coe_pullbackRationalFunction [CompactSpace X] (u : (RationalFunctions X)ˣ)
    (hu : ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ (principalDivisor u).supp) :
    ((pullbackRationalFunction g u hu : (RationalFunctions Y)ˣ) : RationalFunctions Y) =
      pullbackRat g u := by
  funext Z
  have key := pullbackComponent_eq hu (Divisor.isLocalEquation_principalDivisor u ⊤)
    (Z := Z) trivial (mem_pointComponent _)
    (Units.map (stalkEquiv g Z).symm.toMonoidHom
      ((RationalFunctions.unitsEquiv X u) (pointComponent (g (componentGenericPoint Y Z)))))
    ((stalkEquiv g Z).apply_symm_apply _)
  change ((pullbackComponent g hu (Divisor.isLocalEquation_principalDivisor u ⊤) Z trivial :
    (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
      Y.presheaf.stalk (componentGenericPoint Y Z)) = _
  rw [key]
  rfl

/-- **Pulled-back sections.** If `N` is Cartier and `N' ≥ g^*N`, then the pull-back of a section
of `𝒪_X(N)` over `U` is a section of `𝒪_Y(N')` over `g⁻¹ U`: for `φ ≠ 0`, `div φ + N ≥ 0` on
`U`, so `g^*(div φ + N) = div(g^*φ) + g^*N ≥ 0` on `g⁻¹ U`. -/
private theorem isDivisorialSection_ratPullSec [CompactSpace X] [CompactSpace Y] {N : Divisor X}
    (hN : N.IsCartier) {N' E : Divisor Y} (hE : 0 ≤ E)
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp}
    (hpb : N.IsPullback g hB (N' - E)) (U : X.Opens)
    (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U)) (hφ : N.IsDivisorialSection U φ) :
    N'.IsDivisorialSection (g ⁻¹ᵁ U) (ratPullSec g U φ) := by
  intro F hF
  have hFU := F.componentGenericPoint_mem_of_nonempty hF
  have hU : (U : Set X).Nonempty := ⟨g (componentGenericPoint Y F.component), hFU⟩
  set φ₀ := extendRat U hU φ
  have hval : ratPullSec g U φ ⟨F.component, hFU⟩ = pullbackRat g φ₀ F.component := rfl
  rw [hval]
  by_cases h0 : φ₀ = 0
  · left
    rw [h0, map_zero]
    rfl
  -- `φ₀` is a unit of the field `K(X)`
  have hunit : IsUnit φ₀ := by
    have e := rationalFunctionsEquivFunctionField X
    have h : e φ₀ ≠ 0 := (map_ne_zero_iff e e.injective).mpr h0
    simpa using (isUnit_iff_ne_zero.mpr h).map e.symm
  set u := hunit.unit
  have hu : ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ (principalDivisor u).supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _ Z
  have hBs : ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ (principalDivisor u + N).supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _ Z
  have hpb' : (principalDivisor u + N).IsPullback g hBs
      (principalDivisor (pullbackRationalFunction g u hu) + (N' - E)) :=
    Divisor.IsPullback.add (Divisor.isCartier_principalDivisor u) hN hBs
      (Divisor.isPullback_principalDivisor u hu) hpb
  -- `div u + N ≥ 0` on `U`
  have heff : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ (U : Set X)).Nonempty →
      0 ≤ (principalDivisor u + N).coeff P := by
    intro P hP
    have hPφ := hφ P hP
    have hPu : φ ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩ =
        (u : RationalFunctions X) P.component := rfl
    rw [hPu] at hPφ
    rcases hPφ with h | h
    · exact absurd h (Units.ne_zero ((RationalFunctions.unitsEquiv X u) P.component))
    · rw [PrimeDivisor.valuation_component] at h
      rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
      have := WithZero.exp_le_exp.mp h
      omega
  have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn
    ((Divisor.isCartier_principalDivisor u).add hN) heff hpb' F hF
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, DivisorWithCoeffs.coeff_sub] at hnn
  have hEF := hE F
  right
  have hv : pullbackRat g φ₀ F.component =
      ((pullbackRationalFunction g u hu : (RationalFunctions Y)ˣ) : RationalFunctions Y)
        F.component := by
    rw [coe_pullbackRationalFunction]
    rfl
  rw [hv, PrimeDivisor.valuation_component]
  exact WithZero.exp_le_exp.mpr (by
    change (0 : ℤ) ≤ E.coeff F at hEF
    omega)

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X]
  [IsIntegral Y] [IsDominant g] in
/-- An irreducible space has a single irreducible component. -/
private theorem eq_of_irreducibleComponents {Z : Scheme.{u}} [IrreducibleSpace Z]
    (W W' : irreducibleComponents Z) : W = W' := by
  have h : ∀ W : irreducibleComponents Z, W.1 = Set.univ := fun W =>
    (irreducibleComponents_eq_singleton (X := Z) ▸ W.2 : W.1 ∈ ({Set.univ} : Set (Set Z)))
  exact Subtype.ext ((h W).trans (h W').symm)

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The comparison `𝒪_{X,η} ⟶ 𝒪_{Y,η}` used by `ratPullSec` at a component is bijective when
`g^♯ : 𝒪_{X,g(η_Y)} → 𝒪_{Y,η_Y}` is. -/
private theorem bijective_stalkMap_comp_stalkEquiv_symm
    (hbij : Function.Bijective (g.stalkMap (genericPoint Y)).hom) (Z' : irreducibleComponents Y) :
    Function.Bijective (fun a => (g.stalkMap (componentGenericPoint Y Z')).hom
      ((stalkEquiv g Z').symm a)) := by
  have h : ∀ y : Y, y = genericPoint Y → Function.Bijective (g.stalkMap y).hom := by
    rintro _ rfl; exact hbij
  exact (h _ (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z')).comp
    (stalkEquiv g Z').symm.bijective

/-- The valuation `v_P` is carried to `v_F` by a map of the factors of `𝒦` compatible with an
isomorphism `𝒪_{X,P} ≅ 𝒪_{Y,F}`. -/
private theorem valuation_map (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y)
    (φ : P.localRing ≃+* F.localRing)
    (T : X.presheaf.stalk (componentGenericPoint X P.component) →+*
      Y.presheaf.stalk (componentGenericPoint Y F.component))
    (hT : ∀ a, T (P.toComponent.hom a) = F.toComponent.hom (φ a))
    (x : X.presheaf.stalk (componentGenericPoint X P.component)) :
    F.valuation (T x) = P.valuation x := by
  let := P.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions P.genericPoint_mem_component
  have : Ring.KrullDimLE 1 P.localRing := krullDimLE_of_coheight_le P.coheight_genericPoint.le
  have := P.isDiscreteValuationRing_localRing
  let := F.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions F.genericPoint_mem_component
  have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
  have := F.isDiscreteValuationRing_localRing
  let eP := IsLocalization.algEquiv (nonZeroDivisors P.localRing)
    (X.presheaf.stalk (componentGenericPoint X P.component)) (FractionRing P.localRing)
  let eF := IsLocalization.algEquiv (nonZeroDivisors F.localRing)
    (Y.presheaf.stalk (componentGenericPoint Y F.component)) (FractionRing F.localRing)
  change Ring.ordFrac F.localRing (eF (T x)) = Ring.ordFrac P.localRing (eP x)
  have key := MMP.Positivity.ordFrac_map_of_ringEquiv (K := FractionRing P.localRing)
    (K' := FractionRing F.localRing) φ
    ((eF.toRingEquiv.toRingHom.comp T).comp eP.symm.toRingEquiv.toRingHom) (fun r => by
      have h1 : eP.symm (algebraMap _ (FractionRing P.localRing) r) = P.toComponent.hom r :=
        eP.symm.commutes r
      have h2 : eF (F.toComponent.hom (φ r)) = algebraMap _ (FractionRing F.localRing) (φ r) :=
        eF.commutes (φ r)
      simp only [RingHom.coe_comp, Function.comp_apply]
      change eF (T (eP.symm (algebraMap _ (FractionRing P.localRing) r))) = _
      rw [h1, hT, h2]) (eP x)
  simpa using key

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X]
  [IsIntegral Y] [IsDominant g] in
/-- The values of a section of `𝒦_X` at two equal components differ by the identification of
their stalks. -/
private theorem sec_apply_eq_stalkSpecializes {U : X.Opens}
    (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U))
    (Z₁ Z₂ : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) (h : Z₁ = Z₂)
    (hsp : componentGenericPoint X Z₁.1 ⤳ componentGenericPoint X Z₂.1) :
    φ Z₁ = (X.presheaf.stalkSpecializes hsp).hom (φ Z₂) := by
  subst h
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X]
  [IsIntegral Y] [IsDominant g] in
private theorem isIso_stalkSpecializes {Z : Scheme.{u}} {x y : Z} (hsp : x ⤳ y)
    (h : x = y) : IsIso (Z.presheaf.stalkSpecializes hsp) := by
  subst h; simp only [TopCat.Presheaf.stalkSpecializes_refl]; infer_instance

/-- **Valuations of pulled-back sections at a strict transform.** If the prime divisor `F` of
`Y` lies over the prime divisor `P` of `X` with `𝒪_{X,P} ≅ 𝒪_{Y,F}`, then `v_F(g^*φ) = v_P(φ)`. -/
private theorem valuation_ratPullSec {U : X.Opens}
    (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U)) (P : MMP.Mori.PrimeDivisor X)
    (hP : (P.support ∩ (U : Set X)).Nonempty) (F : MMP.Mori.PrimeDivisor Y)
    (hF : (F.support ∩ (g ⁻¹ᵁ U : Set Y)).Nonempty) (hFP : g F.genericPoint = P.genericPoint)
    (hiso : IsIso (g.stalkMap F.genericPoint)) :
    F.valuation (ratPullSec g U φ ⟨F.component, F.componentGenericPoint_mem_of_nonempty hF⟩) =
      P.valuation (φ ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩) := by
  have hFU := F.componentGenericPoint_mem_of_nonempty hF
  have hPU := P.componentGenericPoint_mem_of_nonempty hP
  set W := pointComponent (g (componentGenericPoint Y F.component))
  have hWU : componentGenericPoint X W ∈ U :=
    componentGenericPoint_mem ⟨_, P.genericPoint_mem_of_nonempty hP⟩ W
  have hsp : componentGenericPoint X W ⤳ componentGenericPoint X P.component := by
    rw [eq_of_irreducibleComponents W P.component]
  have key := sec_apply_eq_stalkSpecializes φ ⟨W, hWU⟩ ⟨P.component, hPU⟩
    (Subtype.ext (eq_of_irreducibleComponents _ _)) hsp
  -- the map of factors
  let T : X.presheaf.stalk (componentGenericPoint X P.component) →+*
      Y.presheaf.stalk (componentGenericPoint Y F.component) :=
    (g.stalkMap (componentGenericPoint Y F.component)).hom.comp
      ((stalkEquiv g F.component).symm.toRingHom.comp (X.presheaf.stalkSpecializes hsp).hom)
  have hTφ : ratPullSec g U φ ⟨F.component, hFU⟩ = T (φ ⟨P.component, hPU⟩) := by
    rw [ratPullSec_apply]
    simp only [T, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [← key]
  -- the isomorphism of local rings
  have hsp₂ : g F.genericPoint ⤳ P.genericPoint := hFP ▸ specializes_rfl
  have := isIso_stalkSpecializes hsp₂ hFP
  let ψ : P.localRing ≃+* F.localRing :=
    (asIso (X.presheaf.stalkSpecializes hsp₂ ≫ g.stalkMap F.genericPoint)).commRingCatIsoToRingEquiv
  have hT : ∀ a, T (P.toComponent.hom a) = F.toComponent.hom (ψ a) := by
    intro a
    have hsp₃ : g (componentGenericPoint Y F.component) ⤳ P.genericPoint :=
      (g.base.hom.map_specializes F.specializes_genericPoint).trans (hFP ▸ specializes_rfl)
    have h1 : (stalkEquiv g F.component).symm
        ((X.presheaf.stalkSpecializes hsp).hom (P.toComponent.hom a)) =
        (X.presheaf.stalkSpecializes hsp₃).hom a := by
      rw [RingEquiv.symm_apply_eq]
      change _ = (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes hsp₃).hom a)
      simp only [stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp_apply]
    simp only [T, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [h1]
    change _ = (Y.presheaf.stalkSpecializes _).hom ((g.stalkMap F.genericPoint).hom
      ((X.presheaf.stalkSpecializes hsp₂).hom a))
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]
  rw [hTφ]
  exact valuation_map P F ψ T hT _

/-- **The pull-back map is an isomorphism** when `g^♯` is bijective at the generic point and every
prime divisor `P` of `X` has a strict transform `F` on `Y`, with `𝒪_{X,P} ≅ 𝒪_{Y,F}` and
`coeff_F N' = coeff_P N`: a rational function on `g⁻¹ U` with poles bounded by `N'` has poles
bounded by `N` on `U`. -/
private theorem isIso_pullbackDivisorialHom
    (hbij : Function.Bijective (g.stalkMap (genericPoint Y)).hom) (N : Divisor X) (N' : Divisor Y)
    (h : ∀ (U : X.Opens) (φ : (rationalFunctionsPresheaf X).obj (Opposite.op U)),
      N.IsDivisorialSection U φ → N'.IsDivisorialSection (g ⁻¹ᵁ U) (ratPullSec g U φ))
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, ∃ F : MMP.Mori.PrimeDivisor Y,
      g F.genericPoint = P.genericPoint ∧ IsIso (g.stalkMap F.genericPoint) ∧
        N'.coeff F = N.coeff P) :
    IsIso (pullbackDivisorialHom g N N' h) := by
  refine (Scheme.Modules.Hom.isIso_iff_isIso_app).mpr fun U => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  by_cases hU : (U : Set X).Nonempty
  swap
  · have hs : ∀ φ φ' : N.divisorialSubmodule U, φ = φ' := fun φ φ' =>
      Subtype.ext (funext fun Z => (hU ⟨_, Z.2⟩).elim)
    have ht : ∀ ψ ψ' : N'.divisorialSubmodule (g ⁻¹ᵁ U), ψ = ψ' := fun ψ ψ' =>
      Subtype.ext (funext fun Z => (hU ⟨_, Z.2⟩).elim)
    exact ⟨fun a b _ => hs a b, fun ψ => ⟨0, ht _ _⟩⟩
  obtain ⟨Z'₀⟩ : Nonempty (irreducibleComponents Y) := ⟨pointComponent (genericPoint Y)⟩
  have hZ'₀ : componentGenericPoint Y Z'₀ ∈ g ⁻¹ᵁ U := by
    show g _ ∈ U
    rw [← map_componentGenericPoint_eq g Z'₀]
    exact componentGenericPoint_mem hU _
  have hT := bijective_stalkMap_comp_stalkEquiv_symm g hbij Z'₀
  have hall' : ∀ Z' : {Z' : irreducibleComponents Y // componentGenericPoint Y Z' ∈ g ⁻¹ᵁ U},
      Z' = ⟨Z'₀, hZ'₀⟩ := fun Z' => Subtype.ext (eq_of_irreducibleComponents _ _)
  have hZx : componentGenericPoint X (pointComponent (g (componentGenericPoint Y Z'₀))) ∈ U :=
    componentGenericPoint_mem hU _
  have hall : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      Z = ⟨pointComponent (g (componentGenericPoint Y Z'₀)), hZx⟩ :=
    fun Z => Subtype.ext (eq_of_irreducibleComponents _ _)
  constructor
  · intro φ φ' hφφ'
    have e := congrFun (congrArg Subtype.val hφφ') ⟨Z'₀, hZ'₀⟩
    change ratPullSec g U φ.1 ⟨Z'₀, hZ'₀⟩ = ratPullSec g U φ'.1 ⟨Z'₀, hZ'₀⟩ at e
    refine Subtype.ext (funext fun Z => ?_)
    rw [hall Z]
    exact hT.1 e
  · intro ψ
    obtain ⟨b, hb⟩ := hT.2 (ψ.1 ⟨Z'₀, hZ'₀⟩)
    -- the section `φ` over `U` with value `b`
    let φ : (rationalFunctionsPresheaf X).obj (Opposite.op U) := fun Z =>
      (X.presheaf.stalkSpecializes (show componentGenericPoint X Z.1 ⤳
        componentGenericPoint X (pointComponent (g (componentGenericPoint Y Z'₀))) by
          rw [eq_of_irreducibleComponents Z.1 (pointComponent _)])).hom b
    have hφb : φ ⟨pointComponent (g (componentGenericPoint Y Z'₀)), hZx⟩ = b := by
      simp only [φ, TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    have hpull : ratPullSec g U φ = ψ.1 := by
      funext Z'
      rw [hall' Z', ratPullSec_apply, hφb]
      exact hb
    have hφ : N.IsDivisorialSection U φ := by
      intro P hP
      obtain ⟨F, hFP, hiso, hcoeff⟩ := hD P
      have hF : (F.support ∩ (g ⁻¹ᵁ U : Set Y)).Nonempty := by
        refine ⟨F.genericPoint, ?_, ?_⟩
        · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl
        · show g _ ∈ U
          rw [hFP]
          exact P.genericPoint_mem_of_nonempty hP
      have hψF := ψ.2 F hF
      rw [hcoeff] at hψF
      have hv := valuation_ratPullSec g φ P hP F hF hFP hiso
      rw [hpull] at hv
      rcases hψF with h0 | hle
      · left
        have hb0 : b = 0 := by
          apply hT.1
          change _ = (g.stalkMap (componentGenericPoint Y Z'₀)).hom ((stalkEquiv g Z'₀).symm 0)
          rw [map_zero, map_zero, hb]
          have key : ∀ Z₁ Z₂ : {Z' : irreducibleComponents Y //
              componentGenericPoint Y Z' ∈ g ⁻¹ᵁ U}, Z₁ = Z₂ → ψ.1 Z₁ = 0 → ψ.1 Z₂ = 0 := by
            rintro _ _ rfl h; exact h
          exact key _ _ (hall' ⟨F.component, F.componentGenericPoint_mem_of_nonempty hF⟩) h0
        simp only [φ, hb0, map_zero]
      · right
        rwa [hv] at hle
    exact ⟨⟨φ, hφ⟩, Subtype.ext hpull⟩

/-- **Pull-back coefficients at a strict transform.** If the prime divisor `F` of `Y` lies over
the prime divisor `P` of `X` with `𝒪_{X,P} ≅ 𝒪_{Y,F}`, then `coeff_F(g^*N) = coeff_P N` for a
Cartier divisor `N`. -/
private theorem coeff_isPullback_of_isIso_stalkMap {N : Divisor X} (hN : N.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp} {N' : Divisor Y}
    (hpb : N.IsPullback g hB N') (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y)
    (hFP : g F.genericPoint = P.genericPoint) (hiso : IsIso (g.stalkMap F.genericPoint)) :
    N'.coeff F = N.coeff P := by
  obtain ⟨U, hPU, φ, hφ⟩ := hN P.genericPoint
  have hP : (P.support ∩ (U : Set X)).Nonempty := (P.genericPoint_mem_iff U).mp hPU
  have hF : (F.support ∩ (g ⁻¹ᵁ U : Set Y)).Nonempty :=
    (F.genericPoint_mem_iff (g ⁻¹ᵁ U)).mp (show g F.genericPoint ∈ U from hFP ▸ hPU)
  rw [hpb U φ hφ F hF, hφ P hP]
  -- the restriction of `φ` to `U`
  let φU : (rationalFunctionsPresheaf X).obj (Opposite.op U) :=
    fun Z => (φ : RationalFunctions X) Z.1
  have hv := valuation_ratPullSec g φU P hP F hF hFP hiso
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk (F.map_componentGenericPoint_mem g hF) (hB _)
    (mem_pointComponent _)
  have hpc := pullbackComponent_eq hB hφ (F.map_componentGenericPoint_mem g hF)
    (mem_pointComponent _) a ha
  have hval : ratPullSec g U φU ⟨F.component, F.componentGenericPoint_mem_of_nonempty hF⟩ =
      ((pullbackComponent g hB hφ F.component (F.map_componentGenericPoint_mem g hF) :
        (Y.presheaf.stalk (componentGenericPoint Y F.component))ˣ) :
          Y.presheaf.stalk (componentGenericPoint Y F.component)) := by
    rw [hpc, ratPullSec_apply]
    change _ = (g.stalkMap (componentGenericPoint Y F.component)).hom (a : _)
    congr 1
    rw [RingEquiv.symm_apply_eq]
    exact ha.symm
  rw [hval, PrimeDivisor.valuation_eq_exp_ordUnit] at hv
  have hv' : P.valuation (φU ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩) =
      WithZero.exp (P.ord φ) := PrimeDivisor.valuation_component P φ
  rw [hv'] at hv
  exact WithZero.exp_injective hv

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A birational morphism of integral schemes is bijective on stalks at the generic point. -/
private theorem bijective_stalkMap_genericPoint (hg : IsBirationalMorphism g) :
    Function.Bijective (g.stalkMap (genericPoint Y)).hom := by
  have e : ⇑(g.stalkMap (genericPoint Y)).hom = ⇑(functionFieldMap g) ∘
      ⇑(X.presheaf.stalkCongr
        (Inseparable.of_eq (map_genericPoint_of_isDominant g).symm)).inv.hom := by
    funext x
    simp only [functionFieldMap, Function.comp_apply]
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id_assoc]
  rw [e]
  exact hg.functionFieldMap_bijective.comp (ConcreteCategory.bijective_of_isIso _)

end PullbackSections

/-! ### The snc lower bound for discrepancies at the centre -/

section LowerBound

open MMP MMP.Mori MMP.Resolution MMP.Fourfold
open TopologicalSpace
open scoped WithZero

/-- The support of `∑_{E ∈ S} E` is `S`. -/
private theorem mem_support_sum_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (G : MMP.Mori.PrimeDivisor X) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- At a point `w` of a scheme, an snc divisor has at most `codim w` components through `w`:
their local equations are distinct members of a regular system of parameters. -/
private theorem card_le_coheight_of_isSNC {R : Type*} [Zero R] {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {D : DivisorWithCoeffs R X} (hD : D.IsSNC sX)
    (w : X) (J : Finset (MMP.Mori.PrimeDivisor X)) (hJ : J ⊆ D.support)
    (hw : ∀ G ∈ J, w ∈ G.support) : (J.card : ℕ∞) ≤ Order.coheight w := by
  obtain ⟨N, z, j, hz, hj, -⟩ := hD.2 w
  rw [coheight_eq_of_isRegularSystemOfParameters hz]
  have hinj : Function.Injective fun G : J => j ⟨G.1, hJ G.2, hw G.1 G.2⟩ := by
    intro G G' h
    have h' := congrArg Subtype.val (hj h)
    exact Subtype.ext h'
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_coe, Fintype.card_fin] at this
  exact_mod_cast this

/-- A member of a regular system of parameters is not in the ideal generated by members of
another index set. -/
private theorem notMem_span_image_of_notMem {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {m : ℕ} {w : Fin m → R} (hw : IsRegularSystemOfParameters w)
    {s : Set (Fin m)} {a : Fin m} (ha : a ∉ s) : w a ∉ Ideal.span (w '' s) := by
  classical
  intro hmem
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  set s' : Set R := w '' ({a}ᶜ : Set (Fin m)) with hs'
  have hspan : Ideal.span s' = IsLocalRing.maximalIdeal R := by
    rw [← hw.1]
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨l, -, rfl⟩; exact ⟨l, rfl⟩
    · rintro _ ⟨l, rfl⟩
      by_cases hl : l = a
      · subst hl
        refine Ideal.span_mono (Set.image_mono fun x hx => ?_) hmem
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl
        exact ha hx
      · exact Ideal.subset_span ⟨l, hl, rfl⟩
  have hfin : s'.Finite := Set.toFinite _
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) hfin
  rw [show Submodule.span R s' = IsLocalRing.maximalIdeal R from hspan] at hle
  have hcard : s'.ncard ≤ m - 1 := by
    rw [hs']
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_eq_toFinset_card']
    simp [Finset.card_compl]
  have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hw.2] at hrank
  have : (IsLocalRing.maximalIdeal R).spanFinrank = m := by exact_mod_cast hrank
  have := a.2
  omega

end LowerBound

/-! ### Free sections of a relatively free Cartier divisor -/

section FreeSectionsCopy

open MMP.Flips MMP.Intersection MMP.Fourfold

/-- An integral scheme is its own unique irreducible component. -/
private theorem univ_mem_irreducibleComponents (X : Scheme.{u}) [IsIntegral X] :
    (Set.univ : Set X) ∈ irreducibleComponents X := by
  rw [irreducibleComponents_eq_singleton]; rfl

/-- The order of `v⁻¹` is minus the order of `v`. -/
private theorem scheme_ord_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {v : X.functionField} (hv : v ≠ 0) (z : X) : X.ord v⁻¹ z = -X.ord v z := by
  have := Scheme.ord_mul (x := z) hv (inv_ne_zero hv)
  rw [mul_inv_cancel₀ hv, Scheme.ord_one] at this
  omega

section FreeSections

open Opposite

variable {Y : Scheme.{u}} [IsIntegral Y]

private theorem specializes_genericPoint (Z : irreducibleComponents Y) :
    componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem genericPoint_specializes (Z : irreducibleComponents Y) :
    genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

/-- A rational function `φ ∈ K(Y)`, read in every factor of `K(Y) = ∏_Z 𝒪_{Y,η_Z}`. -/
private noncomputable def toRationalFunctions : Y.functionField →+* RationalFunctions Y :=
  Pi.ringHom fun Z => (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom

private theorem stalkSpecializes_toRationalFunctions (Z : irreducibleComponents Y)
    (φ : Y.functionField) :
    (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom
      (toRationalFunctions φ Z) = φ := by
  change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom φ) = φ
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The unit of `K(Y) = ∏_Z 𝒪_{Y,η_Z}` defined by a non-zero rational function. -/
private noncomputable def unitOfFunction {φ : Y.functionField} (hφ : φ ≠ 0) :
    (RationalFunctions Y)ˣ :=
  Units.map (toRationalFunctions (Y := Y)).toMonoidHom (Units.mk0 φ hφ)

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes P.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The order along `P` of the unit of `K(Y)` defined by `φ ≠ 0` is `ord_{η_P}(φ)`. -/
private theorem ord_toRationalFunctions (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) (ψ : (RationalFunctions Y)ˣ) (hψ : (ψ : RationalFunctions Y) =
      toRationalFunctions φ) : P.ord ψ = Scheme.ord φ P.genericPoint := by
  have h2 := valuation_eq_inv_divisorialValuation P ((ψ : RationalFunctions Y) P.component)
  rw [hψ, stalkSpecializes_toRationalFunctions, ← hψ, P.valuation_component,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hφ, ← WithZero.exp_neg,
    neg_neg] at h2
  exact WithZero.exp_injective h2

private theorem ord_unitOfFunction (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) : P.ord (unitOfFunction hφ) = Scheme.ord φ P.genericPoint :=
  ord_toRationalFunctions P hφ _ rfl

/-- **Local equations of a relatively free Cartier divisor.** Let `E` be a Cartier divisor with
Weil divisor `B` on a normal integral locally Noetherian scheme, `f`-free for `f : Y ⟶ Z`. Every
`x ∈ Y` has an open `U' ∋ f(x)` and a unit `ψ` of `K(Y)` with `B + div ψ` effective on `f⁻¹U'`
and zero along every prime divisor through `x`: `ψ` is a section of `𝒪_Y(E)` over `f⁻¹U'`
generating it at `x`. -/
private theorem exists_isLocalEquation_of_isRelativelyFreeCartier {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Z) {E : Y.CartierDivisor}
    {B : Divisor Y} (hEB : MMP.Intersection.IsWeilDivisorOfCartier E B)
    (hfree : IsRelativelyFreeCartier f E)
    (x : Y) : ∃ U' : Z.Opens, f x ∈ U' ∧ ∃ ψ : (RationalFunctions Y)ˣ,
      (∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ f ⁻¹ᵁ U').Nonempty →
        0 ≤ B.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor Y, x ∈ P.support → B.coeff P + P.ord ψ = 0 := by
  classical
  set L := MMP.CartierDivisor.sheaf E
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hepiL : Epi (adj.counit.app L) := hfree
  have : Epi ((adj.homEquiv ((Scheme.Modules.pushforward f).obj L) L).symm
      (𝟙 ((Scheme.Modules.pushforward f).obj L))) := by
    rw [Stacks.Tag01VMVeryAmple.homEquiv_symm_id]; exact hepiL
  obtain ⟨V', -, bsec, hxb⟩ := Stacks.Tag01VMVeryAmple.exists_mem_nonvanishingLocusOn_of_epi_adjoint
    f (𝟙 ((Scheme.Modules.pushforward f).obj L)) x
  set W' := f ⁻¹ᵁ V' with hW'
  let b : Γ(L, W') := bsec
  have hxb' : x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L W' b := hxb
  obtain ⟨hxW', hgerm⟩ := hxb'
  set σ := MMP.CartierDivisorSheaf.sectionVal b
  -- a local equation of `E` at `x`, and `σ = r g⁻¹` with `r` a unit at `x`
  obtain ⟨U, hxU, g, hg⟩ := MMP.Intersection.exists_isLocalEquationOn E x
  set U1 := U ⊓ W'
  have hxU1 : x ∈ U1 := ⟨hxU, hxW'⟩
  have hg1 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE (inf_le_left : U1 ≤ U)) hg
  set g1 := MMP.Intersection.resUnit (homOfLE (inf_le_left : U1 ≤ U)) g
  set b1 : Γ(L, U1) := L.presheaf.map (homOfLE (inf_le_right : U1 ≤ W')).op b with hb1
  obtain ⟨r, hr⟩ := (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg1
      (MMP.CartierDivisorSheaf.sectionVal b1)).1
    (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b1)
  have hb1r : b1 = r • MMP.CartierDivisor.invSection hg1 :=
    MMP.CartierDivisorSheaf.sectionVal_injective hr.symm
  have hru : IsUnit (Y.presheaf.germ U1 x hxU1 r) := by
    by_contra hnu
    apply hgerm
    have h1 : L.presheaf.germ W' x hxW' b = L.presheaf.germ U1 x hxU1 b1 := by
      rw [hb1]
      exact (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) L.presheaf
        (homOfLE (inf_le_right : U1 ≤ W')) x hxU1 b).symm
    rw [h1, hb1r, Stacks.ModuleStalk.germ_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
  -- on `U2 = D(r)` the section `σ` is a unit of `𝓜_Y`
  set U2 := Y.basicOpen r
  have hU21 : U2 ≤ U1 := Y.basicOpen_le r
  have hU2W : U2 ≤ W' := hU21.trans inf_le_right
  have hxU2 : x ∈ U2 := (Scheme.mem_basicOpen Y r x hxU1).mpr hru
  set r2 : Γ(Y, U2) := Y.presheaf.map (homOfLE hU21).op r
  have hr2 : IsUnit r2 := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace r
  have hg2 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE hU21) hg1
  set g2 := MMP.Intersection.resUnit (homOfLE hU21) g1
  set σ2 := Y.totalQuotientSheaf.obj.map (homOfLE hU2W).op σ
  have hσ2 : σ2 = MMP.Intersection.toTotalQuotient U2 r2 * ((g2⁻¹ : _ˣ) : _) := by
    have h := congrArg (Y.totalQuotientSheaf.obj.map (homOfLE hU21).op) hr
    rw [map_mul, ← MMP.Intersection.toTotalQuotient_res] at h
    refine Eq.trans ?_ h.symm
    erw [hb1, MMP.CartierDivisorSheaf.sectionVal_map, MMP.Intersection.totalQuotient_map_map]
    rfl
  have hσ2u : IsUnit σ2 := by
    rw [hσ2]
    exact (hr2.map (MMP.Intersection.toTotalQuotient U2)).mul (Units.isUnit _)
  -- the rational function `φ` of `σ`
  set ξ := genericPoint Y
  have hξ : ∀ (O : Y.Opens) (y : Y), y ∈ O → ξ ∈ O := fun O y hy =>
    ((genericPoint_spec Y).specializes trivial : ξ ⤳ y).mem_open O.isOpen hy
  have hξW' : ξ ∈ W' := hξ W' x hxW'
  set φ := totalQuotientStalkToFunctionField ξ (Y.totalQuotientSheaf.presheaf.germ W' ξ hξW' σ)
  have hσgerm : ∀ (y : Y) (hy : y ∈ W'), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ W' y hy σ) = φ := by
    intro y hy
    have hsp : ξ ⤳ y := (genericPoint_spec Y).specializes trivial
    rw [← MMP.Intersection.totalQuotientStalkToFunctionField_stalkSpecializes hsp,
      TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hσ2germ : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy σ2) = φ := by
    intro y hy
    rw [TopCat.Presheaf.germ_res_apply]
    exact hσgerm y (hU2W hy)
  have hφ : φ ≠ 0 := by
    rw [← hσ2germ x hxU2]
    exact ((hσ2u.map (Y.totalQuotientSheaf.presheaf.germ U2 x hxU2).hom).map
      (totalQuotientStalkToFunctionField x).hom).ne_zero
  -- `B + div φ ≥ 0` on `W'`
  have : Nonempty W' := ⟨⟨x, hxW'⟩⟩
  have hge := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add hEB W' hφ σ
    hσgerm).1 (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b)
  -- `-B + div φ⁻¹ ≥ 0` on `U2`, as `σ⁻¹` is a section of `𝒪_Y(-E)` there
  have hnegEB : MMP.Intersection.IsWeilDivisorOfCartier (-E) (-B) := fun P => by
    have h := MMP.Intersection.isOrderAlong_primeDivisorOrder (-E) P
    rwa [map_neg, (hEB P).primeDivisorOrder_eq, ← DivisorWithCoeffs.coeff_neg] at h
  set τ : Y.totalQuotientSheaf.obj.obj (op U2) := (hσ2u.unit⁻¹).val
  have hτσ : τ * σ2 = 1 := hσ2u.val_inv_mul
  have hτmem : τ ∈ MMP.Intersection.lineBundleSections (-E) U2 := by
    refine (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg2.inv τ).2
      ⟨((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)), ?_⟩
    rw [inv_inv]
    have h1 : MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) *
        MMP.Intersection.toTotalQuotient U2 r2 = 1 := by
      rw [← map_mul, hr2.val_inv_mul, map_one]
    calc _ = (MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) * (g2 : _)) *
          (σ2 * τ) := by rw [mul_comm σ2 τ, hτσ, mul_one]
      _ = τ * ((MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) *
          MMP.Intersection.toTotalQuotient U2 r2) * ((g2 : _) * ((g2⁻¹ : _ˣ) : _))) := by
            rw [hσ2]; ring
      _ = τ := by rw [h1, Units.mul_inv, mul_one, mul_one]
  have hτgerm : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy τ) = φ⁻¹ := by
    intro y hy
    have h := congrArg (fun t => totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy t)) hτσ
    simp only [map_mul, map_one, hσ2germ y hy] at h
    exact eq_inv_of_mul_eq_one_left h
  have : Nonempty U2 := ⟨⟨x, hxU2⟩⟩
  have hle := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add hnegEB U2
    (inv_ne_zero hφ) τ hτgerm).1 hτmem
  -- the unit `ψ` of `K(Y)`
  let ψ : (RationalFunctions Y)ˣ := unitOfFunction hφ
  have hψ : ∀ P : MMP.Mori.PrimeDivisor Y, P.ord ψ = Scheme.ord φ P.genericPoint :=
    fun P => ord_unitOfFunction P hφ
  refine ⟨V', hxW', ψ, fun P hP => ?_, fun P hxP => ?_⟩
  · rw [hψ, add_comm]
    exact hge P hP
  · have h1 := hge P ⟨x, hxP, hxW'⟩
    have h2 := hle P ⟨x, hxP, hxU2⟩
    rw [scheme_ord_inv hφ, DivisorWithCoeffs.coeff_neg] at h2
    rw [hψ]
    omega

open MMP.Intersection

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
private theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{u}}
    [IsLocallyNoetherian X] {D : QDivisor X} {C : KCartierDivisor ℚ X}
    (hC : ∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P = C.sum fun E c => c * (primeDivisorOrder P E : ℚ)) {q : ℕ}
    (h : ∀ E, ∃ n : ℤ, ((q : ℚ) • C) E = n) {B : Divisor X}
    (hB : IsWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) h) B)
    (P : MMP.Mori.PrimeDivisor X) : (B.coeff P : ℚ) = q * D.coeff P := by
  classical
  have hc : ∀ E, ((Classical.choose (h E) : ℤ) : ℚ) = ((q : ℚ) • C) E := fun E =>
    (Classical.choose_spec (h E)).symm
  rw [← (hB P).primeDivisorOrder_eq, KCartierDivisor.realization, Finsupp.sum, map_sum,
    Int.cast_sum, hC P, Finsupp.sum, Finset.mul_sum]
  have hz : ∀ E ∈ C.support, E ∉ ((q : ℚ) • C).support →
      (q : ℚ) * (C E * (primeDivisorOrder P E : ℚ)) = 0 := fun E _ hE => by
    rw [Finsupp.notMem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hE
    rw [← mul_assoc, hE, zero_mul]
  rw [← Finset.sum_subset (Finsupp.support_smul (b := (q : ℚ)) (g := C)) hz]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, hc, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end FreeSections

/-- **A semiample `ℚ`-divisor has a free multiple.** If `H` is semiample over a field, some
`mH` is a divisor `H_m` with finitely many global sections of `𝒪(H_m)` without common zero. -/
private theorem exists_sections_of_isRelativelySemiample {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [TopologicalSpace.NoetherianSpace X] {H : QDivisor X}
    (hH : MMP.Fourfold.QDivisor.IsRelativelySemiample sX H) :
    ∃ (m : ℕ) (_ : 0 < m) (Hm : Divisor X), Divisor.toQDivisor Hm = (m : ℤ) • H ∧
      ∃ (t : Finset X) (s : t → Hm.divisorialSubmodule ⊤),
        ∀ x : X, ∃ (i : t) (hi : s i ≠ 0), x ∉ (Hm.zeroDivisor (s i) hi).supp := by
  classical
  obtain ⟨C, hC, m, hm, h, hfree⟩ := hH
  obtain ⟨Hm, hW⟩ := exists_isWeilDivisorOfCartier (KCartierDivisor.realization ((m : ℚ) • C) h)
  have hcoef := coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC h hW
  refine ⟨m, hm, Hm, ?_, ?_⟩
  · ext P
    change (Hm.coeff P : ℚ) = ((m : ℤ) • H) P
    rw [hcoef, Finsupp.smul_apply, zsmul_eq_mul]
    push_cast; rfl
  -- a generating section at each point
  have hsec : ∀ x : X, ∃ (σ : Hm.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      x ∉ (Hm.zeroDivisor σ hσ).supp := by
    intro x
    obtain ⟨U', hxU', ψ, hψ1, hψ2⟩ :=
      exists_isLocalEquation_of_isRelativelyFreeCartier sX hW hfree x
    have hall : ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ Hm.coeff P + P.ord ψ := by
      intro P
      refine hψ1 P ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, ?_⟩
      show sX P.genericPoint ∈ U'
      rwa [Subsingleton.elim (sX P.genericPoint) (sX x)]
    let σ : Hm.divisorialSubmodule ⊤ :=
      ⟨(rationalFunctionsPresheafTopEquiv X).symm ψ, fun P _ => by
        right
        change WithZero.exp (-Hm.coeff P) ≤ P.valuation ((ψ : RationalFunctions X) P.component)
        rw [PrimeDivisor.valuation_component]
        exact WithZero.exp_le_exp.mpr (by have := hall P; omega)⟩
    have hσψ : Divisor.sectionToRationalFunctions σ = ψ :=
      (rationalFunctionsPresheafTopEquiv X).apply_symm_apply _
    have hσ : σ ≠ 0 := by
      intro h0
      haveI : Nontrivial (RationalFunctions X) :=
        Pi.nontrivial_at ⟨Set.univ, univ_mem_irreducibleComponents X⟩
      refine (Units.ne_zero ψ) ?_
      rw [← hσψ, h0]
      exact map_zero (rationalFunctionsPresheafTopEquiv X)
    refine ⟨σ, hσ, fun hx => ?_⟩
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    have hu : (Divisor.isUnit_sectionToRationalFunctions hσ).unit = ψ := Units.ext hσψ
    rw [Divisor.zeroDivisor_eq, hu, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      add_comm] at hE
    exact hE (hψ2 E hxE)
  choose σ hσ hxσ using hsec
  -- a finite subcover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((Hm.zeroDivisor (σ x) (hσ x)).supp : Set X)ᶜ)
    (fun x => (Hm.zeroDivisor (σ x) (hσ x)).supp.isClosed.isOpen_compl)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxσ x⟩)
  refine ⟨t, fun i => σ i.1, fun x => ?_⟩
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨⟨y, hyt⟩, hσ y, hy⟩

end FreeSectionsCopy

/-! ### Arithmetic of `ℚ`-linear equivalence -/

section QLinearEquivalence

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]

/-- `ℚ`-linear equivalence is compatible with addition. -/
private theorem QLinearlyEquivalent.add {A₁ A₂ B₁ B₂ : QDivisor X}
    (h₁ : A₁.QLinearlyEquivalent A₂) (h₂ : B₁.QLinearlyEquivalent B₂) :
    (A₁ + B₁).QLinearlyEquivalent (A₂ + B₂) := by
  obtain ⟨m, hm, φ, hφ⟩ := h₁
  obtain ⟨n, hn, ψ, hψ⟩ := h₂
  refine ⟨m * n, Nat.mul_pos hm hn, φ ^ n * ψ ^ m, ?_⟩
  ext E
  have e1 := congrArg (fun D => DivisorWithCoeffs.coeff D E) hφ
  have e2 := congrArg (fun D => DivisorWithCoeffs.coeff D E) hψ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor,
    zsmul_eq_mul] at e1 e2 ⊢
  rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, PrimeDivisor.ord_pow, nsmul_eq_mul,
    nsmul_eq_mul]
  push_cast
  rw [← e1, ← e2]
  push_cast
  ring

/-- `ℚ`-linear equivalence is compatible with rational multiples. -/
private theorem QLinearlyEquivalent.smul (c : ℚ) {A₁ A₂ : QDivisor X}
    (h : A₁.QLinearlyEquivalent A₂) : (c • A₁).QLinearlyEquivalent (c • A₂) := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  refine ⟨c.den * m, Nat.mul_pos c.den_pos hm, φ ^ c.num, ?_⟩
  ext E
  have e1 := congrArg (fun D => DivisorWithCoeffs.coeff D E) hφ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
    Divisor.coeff_toQDivisor, coeff_principalDivisor, zsmul_eq_mul, smul_eq_mul] at e1 ⊢
  rw [PrimeDivisor.ord_zpow, smul_eq_mul]
  push_cast
  rw [← e1]
  have hc : (c.den : ℚ) * c = c.num := by
    rw [mul_comm]; exact Rat.mul_den_eq_num c
  linear_combination ((m : ℚ) * (A₁.coeff E - A₂.coeff E)) * hc

private theorem QLinearlyEquivalent.of_eq {A₁ A₂ : QDivisor X} (h : A₁ = A₂) :
    A₁.QLinearlyEquivalent A₂ := h ▸ MMP.Mori.QDivisor.QLinearlyEquivalent.refl A₁

end QLinearEquivalence

/-! ### Pull-backs of divisors to a variety over a smooth one -/

section PullbackAlgebra

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (g : Y ⟶ X) [IsDominant g]
  (hc : ∀ N : Divisor X, N.IsCartier)

/-- The pull-back `g^*N` of a divisor on `X`, all of whose divisors are Cartier. -/
private noncomputable def dpb (N : Divisor X) : Divisor Y :=
  N.pullback (hc N) (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g N)

private theorem isPullback_dpb (N : Divisor X) :
    N.IsPullback g (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g N)
      (dpb g hc N) :=
  Divisor.isPullback_pullback _ _

private theorem dpb_eq_of_isPullback {N : Divisor X} {N' : Divisor Y}
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp}
    (h : N.IsPullback g hB N') : dpb g hc N = N' :=
  (isPullback_dpb g hc N).eq (hc N) h

private theorem dpb_add (N₁ N₂ : Divisor X) : dpb g hc (N₁ + N₂) = dpb g hc N₁ + dpb g hc N₂ :=
  dpb_eq_of_isPullback g hc (Divisor.IsPullback.add (hc N₁) (hc N₂)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _)
    (isPullback_dpb g hc N₁) (isPullback_dpb g hc N₂))

private theorem dpb_zsmul (n : ℤ) (N : Divisor X) : dpb g hc (n • N) = n • dpb g hc N :=
  dpb_eq_of_isPullback g hc ((isPullback_dpb g hc N).zsmul (hc N) n
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _))

private theorem dpb_zero : dpb g hc 0 = 0 := by
  simpa using dpb_zsmul g hc 0 0

/-- `g^* div φ = div (g^*φ)`. -/
private theorem dpb_principalDivisor (φ : (RationalFunctions X)ˣ) :
    dpb g hc (principalDivisor φ) = principalDivisor (pullbackRationalFunction g φ
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _)) :=
  dpb_eq_of_isPullback g hc (Divisor.isPullback_principalDivisor φ _)

/-- The pull-back of an effective divisor is effective. -/
private theorem dpb_nonneg {N : Divisor X} (hN : 0 ≤ N) : 0 ≤ dpb g hc N := fun F =>
  MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) (hc N)
    (fun P _ => hN P) (isPullback_dpb g hc N) F
    ⟨F.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support F, trivial⟩

/-- `g^*` on `ℚ`-divisors: the `ℚ`-linear extension of `g^*` on prime divisors. -/
private noncomputable def qpb : QDivisor X →ₗ[ℚ] QDivisor Y :=
  Finsupp.linearCombination ℚ fun P => Divisor.toQDivisor (dpb g hc (Finsupp.single P 1))

private theorem qpb_toQDivisor (N : Divisor X) :
    qpb g hc (Divisor.toQDivisor N) = Divisor.toQDivisor (dpb g hc N) := by
  induction N using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero, dpb_zero g hc, map_zero]
  | add N₁ N₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, dpb_add, map_add]
  | single P n =>
    have e : Divisor.toQDivisor (Finsupp.single P n) = Finsupp.single P (n : ℚ) := by
      classical
      ext E
      rw [Divisor.coeff_toQDivisor]
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> simp
    have e2 : Finsupp.single P n = n • Finsupp.single P (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e, qpb, Finsupp.linearCombination_single, e2, dpb_zsmul, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℚ]

/-- The pull-back of an effective `ℚ`-divisor is effective. -/
private theorem qpb_nonneg {A : QDivisor X} (hA : 0 ≤ A) : 0 ≤ qpb g hc A := by
  classical
  intro F
  change (0 : ℚ) ≤ (qpb g hc A) F
  rw [qpb, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  refine mul_nonneg (hA P) ?_
  have := dpb_nonneg g hc (N := Finsupp.single P 1) (fun Q => by
    change (0 : ℤ) ≤ Finsupp.single P 1 Q
    rw [Finsupp.single_apply]; split_ifs <;> norm_num) F
  change (0 : ℚ) ≤ ((dpb g hc (Finsupp.single P 1)) F : ℚ)
  exact_mod_cast this

/-- `ℚ`-linear equivalence is preserved by `g^*`. -/
private theorem QLinearlyEquivalent.qpb {A₁ A₂ : QDivisor X} (h : A₁.QLinearlyEquivalent A₂) :
    (qpb g hc A₁).QLinearlyEquivalent (qpb g hc A₂) := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  refine ⟨m, hm, pullbackRationalFunction g φ
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _), ?_⟩
  rw [← map_sub, ← map_zsmul, hφ, qpb_toQDivisor, dpb_principalDivisor]

/-- The coefficient of `g^*N` vanishes along a prime divisor whose generic point maps off
`Supp N`: there `1` is a local equation of `N`. -/
private theorem coeff_dpb_eq_zero (N : Divisor X) (F : MMP.Mori.PrimeDivisor Y)
    (hF : g F.genericPoint ∉ N.supp) : (dpb g hc N).coeff F = 0 := by
  set U : X.Opens := (N.supp).compl
  have h1 : N.IsLocalEquation U 1 := by
    intro Q hQ
    rw [PrimeDivisor.ord_one]
    by_contra h
    obtain ⟨x, hxQ, hxU⟩ := hQ
    exact hxU (DivisorWithCoeffs.support_subset_supp h hxQ)
  have hFU : (F.support ∩ (g ⁻¹ᵁ U : Set Y)).Nonempty :=
    (F.genericPoint_mem_iff (g ⁻¹ᵁ U)).mp hF
  rw [isPullback_dpb g hc N U 1 h1 F hFU,
    pullbackComponent_eq _ h1 (F.map_componentGenericPoint_mem g hFU) (mem_pointComponent _) 1
      (by simp), map_one, PrimeDivisor.ordUnit_one]

/-- The coefficient of `g^*A` vanishes along a prime divisor whose generic point maps off
`Supp A`. -/
private theorem coeff_qpb_eq_zero (A : QDivisor X) (F : MMP.Mori.PrimeDivisor Y)
    (hF : g F.genericPoint ∉ A.supp) : (qpb g hc A).coeff F = 0 := by
  classical
  change (qpb g hc A) F = 0
  rw [qpb, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [Finsupp.smul_apply]
  have hP' : g F.genericPoint ∉ DivisorWithCoeffs.supp (Finsupp.single P (1 : ℤ)) := by
    intro h
    obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    have hQP : Q = P := by
      by_contra hne
      exact hQ (by simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hne])
    subst hQP
    exact hF (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hP) hxQ)
  have := coeff_dpb_eq_zero g hc _ F hP'
  rw [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply]
  change A P • ((dpb g hc (Finsupp.single P 1)).coeff F : ℚ) = 0
  rw [this, Int.cast_zero, smul_zero]

/-- A prime divisor along which `g^*A + g^*A'` has nonzero coefficient has generic point mapping
into the union of any finite set of prime divisors containing `Supp A ∪ Supp A'`. -/
private theorem mem_sup_support_of_coeff_qpb_add_ne_zero {A A' : QDivisor X}
    {S : Finset (MMP.Mori.PrimeDivisor X)} (hA : A.support ⊆ S) (hA' : A'.support ⊆ S)
    {F : MMP.Mori.PrimeDivisor Y} (hF : (qpb g hc A + qpb g hc A').coeff F ≠ 0) :
    g F.genericPoint ∈ S.sup fun E => (E.idealSheaf.support : Set X) := by
  have hsub : ∀ B : QDivisor X, B.support ⊆ S → g F.genericPoint ∈ B.supp →
      g F.genericPoint ∈ S.sup fun E => (E.idealSheaf.support : Set X) := by
    intro B hB hx
    obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    rw [Finset.sup_set_eq_biUnion]
    exact Set.mem_iUnion₂.2 ⟨Q, hB (Finsupp.mem_support_iff.mpr hQ), hxQ⟩
  by_contra hnot
  apply hF
  rw [DivisorWithCoeffs.coeff_add, coeff_qpb_eq_zero g hc _ F fun hx => hnot (hsub _ hA hx),
    coeff_qpb_eq_zero g hc _ F fun hx => hnot (hsub _ hA' hx), add_zero]

/-- The pull-back of a `ℚ`-divisor in the sense of `MMP.Mori.QDivisor.IsPullback` is `qpb`. -/
private theorem qpb_eq_of_isPullback {A : QDivisor X} {A' : QDivisor Y}
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ A.supp}
    (h : A.IsPullback g hB A') : qpb g hc A = A' := by
  obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor A
  obtain ⟨G', hG', hpb⟩ := h N hN G hG (hc G)
  have e1 : (N : ℤ) • qpb g hc A = (N : ℤ) • A' := by
    rw [← map_zsmul, ← hG, qpb_toQDivisor, dpb_eq_of_isPullback g hc hpb, hG']
  have hN' : ((N : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext F
  have := congrArg (fun D : QDivisor Y => D F) e1
  simp only [Finsupp.smul_apply, zsmul_eq_mul] at this
  exact mul_left_cancel₀ hN' this

/-- If `M ∼_ℚ A + H`, `tH ∼_ℚ D + D'` and `T ∼_ℚ g^*H_m` with `H_m = mH`, then for every `ε`,
`g^*M + E ∼_ℚ g^*A + E + (ε / t) g^*(D + D') + ((1 - ε) / m) T`. -/
private theorem qLinearlyEquivalent_dpb_add_perturbation {M D Hm : Divisor X}
    {A H D' : QDivisor X} {A' : QDivisor Y} {E HT : Divisor Y} {t : ℚ} {m : ℕ} (ε : ℚ)
    (hM : (Divisor.toQDivisor M).QLinearlyEquivalent (A + H)) (hA : qpb g hc A = A')
    (ht : t ≠ 0) (htH : (t • H).QLinearlyEquivalent (Divisor.toQDivisor D + D'))
    (hm : (m : ℚ) ≠ 0) (hHm : Divisor.toQDivisor Hm = (m : ℤ) • H)
    (hT : (Divisor.toQDivisor HT).QLinearlyEquivalent (qpb g hc (Divisor.toQDivisor Hm))) :
    (Divisor.toQDivisor (dpb g hc M + E)).QLinearlyEquivalent
      (A' + Divisor.toQDivisor E + (ε / t) • (qpb g hc (Divisor.toQDivisor D) + qpb g hc D') +
        ((1 - ε) / m) • Divisor.toQDivisor HT) := by
  have h1 := QLinearlyEquivalent.qpb g hc hM
  rw [qpb_toQDivisor, map_add, hA] at h1
  have h2 := QLinearlyEquivalent.qpb g hc (QLinearlyEquivalent.smul (ε / t) htH)
  rw [map_smul, map_smul, smul_smul, div_mul_cancel₀ ε ht] at h2
  have h3 := QLinearlyEquivalent.smul ((1 - ε) / m) hT
  rw [hHm, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
    div_mul_cancel₀ _ hm] at h3
  have h4 := QLinearlyEquivalent.add h2 h3.symm
  have h5 : qpb g hc H = ε • qpb g hc H + (1 - ε) • qpb g hc H := by
    rw [← add_smul]; simp
  rw [← h5] at h4
  rw [map_add]
  refine (QLinearlyEquivalent.add h1 (MMP.Mori.QDivisor.QLinearlyEquivalent.refl
    (Divisor.toQDivisor E))).trans ?_
  refine ((QLinearlyEquivalent.add (QLinearlyEquivalent.add
    (MMP.Mori.QDivisor.QLinearlyEquivalent.refl A') h4)
    (MMP.Mori.QDivisor.QLinearlyEquivalent.refl (Divisor.toQDivisor E)))).trans
    (QLinearlyEquivalent.of_eq ?_)
  rw [map_smul, map_add]
  abel

end PullbackAlgebra

/-! ### A general member of the free system -/

section GeneralMember

/-- A general linear combination of finitely many sections, one of them nonzero, is nonzero:
the coefficient vectors `c` with `∑ cᵢ sᵢ = 0` form a proper subspace of `kⁱ`, contained in the
kernel of a linear form `ℓ` with `ℓ(e_j) ≠ 0`. -/
private theorem exists_polynomial_sum_smul_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤) (j : ι)
    (hj : s j ≠ 0) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0 := by
  classical
  let p : Submodule k (ι → k) :=
    { carrier := {c | ∑ i, scalarsToGlobalSections k sX (c i) • s i = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at *
        rw [← Finset.smul_sum, hc, smul_zero] }
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    apply hj
    have : ∑ i, scalarsToGlobalSections k sX ((Pi.single j 1 : ι → k) i) • s i = 0 := h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp),
      Pi.single_eq_same, map_one, one_smul] at this
  obtain ⟨ℓ, hℓ, hp⟩ := Submodule.exists_le_ker_of_notMem hjp
  let Q : MvPolynomial ι k :=
    ∑ i, MvPolynomial.C (ℓ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c Q = ℓ c := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ ℓ c]
    simp [Q, MvPolynomial.eval_sum, mul_comm]
  refine ⟨Q, fun h => hℓ (by rw [← heval, h, map_zero]), fun c hc h0 => hc ?_⟩
  rw [heval]
  exact hp (show c ∈ p from h0)

open Classical in
/-- **A general member of a free system, pulled back.** Let `g : Y ⟶ X` be a smooth resolution of a
variety over an algebraically closed field of characteristic zero on which every divisor is
Cartier, `H_m` a divisor with finitely many global sections without common zero, and `∑_{E ∈ S} E`
a reduced snc divisor on `Y`. Then there is a reduced divisor `∑_{E ∈ T} E`, `T` disjoint from `S`,
`ℚ`-linearly equivalent to `g^*H_m`, with `∑_{E ∈ T ∪ S} E` snc. -/
private theorem exists_general_member {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (hX : AlgebraicGeometry.IsVariety k sX) {g : Y ⟶ X} (hg : IsSmoothResolution sX g)
    [IsDominant g] (hc : ∀ N : Divisor X, N.IsCartier) {Hm : Divisor X} (t : Finset X)
    (s : t → Hm.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : t) (hi : s i ≠ 0), x ∉ (Hm.zeroDivisor (s i) hi).supp)
    (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    ∃ T : Finset (MMP.Mori.PrimeDivisor Y),
      (Divisor.toQDivisor (∑ E ∈ T, Finsupp.single E (1 : ℤ))).QLinearlyEquivalent
        (qpb g hc (Divisor.toQDivisor Hm)) ∧ Disjoint T S ∧
      DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) := by
  classical
  obtain ⟨Q, hQ, hQT⟩ := exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC hX hg s hs S hS
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨j, hj, -⟩ := hs x
  obtain ⟨Q₁, hQ₁, hσ⟩ := exists_polynomial_sum_smul_ne_zero sX s j hj
  obtain ⟨c, hc'⟩ : ∃ c : t → k, MvPolynomial.eval c (Q * Q₁) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact mul_ne_zero hQ hQ₁ (MvPolynomial.funext fun c => by rw [h c, map_zero])
  rw [map_mul] at hc'
  have hσc := hσ c (right_ne_zero_of_mul hc')
  set σ := ∑ i, scalarsToGlobalSections k sX (c i) • s i
  have hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉
      (Hm.zeroDivisor σ hσc).supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _
  obtain ⟨T, hT, hTS, hsnc, -⟩ := hQT c (left_ne_zero_of_mul hc') hσc hB _
    (isPullback_dpb g hc (Hm.zeroDivisor σ hσc))
  refine ⟨T, ?_, hTS, hsnc⟩
  rw [← hT, ← qpb_toQDivisor]
  refine QLinearlyEquivalent.qpb g hc
    ⟨1, one_pos, (Divisor.isUnit_sectionToRationalFunctions hσc).unit, ?_⟩
  rw [Divisor.zeroDivisor_eq, map_add, add_sub_cancel_right, Nat.cast_one, one_smul]

end GeneralMember

/-! ### Resolutions, strict transforms and the crepant boundary -/

section ResolutionCopy

open TopologicalSpace MMP.Resolution MMP.Fourfold

/-- An irreducible closed subset maximal in a closed set of pure codimension one of a scheme is
the support of a prime divisor. -/
private theorem exists_primeDivisor_support_eq_of_maximal {Y : Scheme.{u}} {T : Closeds Y}
    (hT : IsPureCodimOne T) {W : IrreducibleCloseds Y}
    (hW : Maximal (fun V : IrreducibleCloseds Y => (V : Set Y) ⊆ T) W) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) = W := by
  have h1 := hT W hW
  rw [MMP.Flips.codimension_eq_coheight_genericPoint] at h1
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact W.isIrreducible.isGenericPoint_genericPoint_closure.trans W.isClosed.closure_eq

/-- An irreducible component of a closed set of pure codimension one of a scheme is the support of
a prime divisor. -/
private theorem exists_primeDivisor_support_eq {Y : Scheme.{u}} {T : Set Y} (hTc : IsClosed T)
    (hpure : IsPureCodimOne (⟨T, hTc⟩ : Closeds Y)) {W : Set Y} (hW : W ∈ componentsOf T) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) = W :=
  exists_primeDivisor_support_eq_of_maximal hpure
    (W := ⟨W, hW.1.1, Aux.isClosed_of_mem_componentsOf hTc hW⟩)
    ⟨hW.1.2, fun V hV hle => hW.2 ⟨V.isIrreducible, hV⟩ hle⟩

/-- **The components of an snc closed subset.** The prime divisors whose generic points lie on a
divisor `T` with simple normal crossings on a smooth scheme form a finite set whose reduced sum is
an snc divisor. -/
private theorem exists_finset_isSNC_of_isSNCClosedSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [NoetherianSpace Y] (hsm : IsSmoothScheme sY)
    {T : Set Y} (hT : IsSNCClosedSubset sY T) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y),
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ)) ∧
      (⋃ F ∈ S, (F.support : Set Y)) = T := by
  classical
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : LocallyOfFinitePresentation sY :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sY)).mpr inferInstance
  haveI : Smooth sY := Aux.smooth_of_isSmoothScheme' sY hsm
  have hT' := hT
  obtain ⟨hTc, hT0 | ⟨hpure, hfin, -⟩⟩ := hT'
  · refine ⟨∅, ?_, by simp [hT0]⟩
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
  have hinj : Set.InjOn (fun P : MMP.Mori.PrimeDivisor Y => (P.support : Set Y))
      {P | (P.support : Set Y) ∈ componentsOf T} := fun P _ Q _ hPQ =>
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ.le
  have hfinS : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ∈ componentsOf T}.Finite :=
    Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 fun _ hP => hP)) hinj
  set S := hfinS.toFinset with hSdef
  have hmemS : ∀ P, P ∈ S ↔ (P.support : Set Y) ∈ componentsOf T := fun P => by
    rw [hSdef, Set.Finite.mem_toFinset]; rfl
  have hU : (⋃ F ∈ S, (F.support : Set Y)) = T := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun F hF => ((hmemS F).1 hF).1.2)
      fun x hx => ?_
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hTc).2 hx)
    obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq hTc hpure hW
    exact Set.mem_iUnion₂.2 ⟨P, (hmemS P).2 (hP ▸ hW), hP ▸ hxW⟩
  have hreg : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y),
      IsRegularSystemOfParameters z := fun y => by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
    exact MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
  refine ⟨S, MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNC_reducedDivisorOf_of_isSNCClosedSubset
    sY hreg S (hU ▸ hT), hU⟩

section Crepant

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {f : Y ⟶ X}

/-- **The strict-transform part of the crepant boundary.** For a proper birational morphism
`f : Y ⟶ X` from a normal variety, a prime divisor `G` of `Y` that is not `f`-exceptional is the
birational transform `f⁻¹_* P` of a prime divisor `P` of `X`, and the crepant boundary `Δ_Y` has
`coeff_G(Δ_Y) = coeff_P(Δ)`. -/
private theorem exists_coeff_eq_of_not_isExceptional (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff G = Δ.coeff P ∧
      f G.genericPoint = P.genericPoint := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hG
  have hη : f G.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨P, neg_injective ((hΔY G).eq hd), hη⟩

/-- **The support of the crepant boundary.** For a proper birational morphism `f : Y ⟶ X` from a
normal variety, every prime divisor in the support of the crepant boundary `Δ_Y` is
`f`-exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨
      f G.genericPoint ∈ (Δ.support.sup fun E => (E.idealSheaf.support : Set X)) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hη⟩ := exists_coeff_eq_of_not_isExceptional hP hY hf hΔY hGe
    refine Or.inr ?_
    rw [hη, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc,
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

end Crepant

/-- **Valuative criterion at a divisor.** A proper birational morphism `f : Y ⟶ X` onto a normal
scheme is an isomorphism of local rings over the generic point of each prime divisor `Q` of `X`:
there is a prime divisor `E` of `Y` with `f(η_E) = η_Q` and `f^♯ : 𝒪_{X,η_Q} ≅ 𝒪_{Y,η_E}`. -/
private theorem exists_primeDivisor_isIso_stalkMap {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (f : Y ⟶ X)
    [IsProper f] (hf : IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor X) :
    ∃ E : MMP.Mori.PrimeDivisor Y,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- **A compatible canonical divisor on a smooth model.** For a birational morphism `g : Y ⟶ X`
from a smooth variety to a normal variety over a perfect field and a canonical divisor
`K = div ω`, `div (g^*ω)` is a canonical divisor of `Y`. -/
private theorem exists_isCanonicalDivisor_divisorOfForm_pullback {k : Type u} [Field k]
    [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {g : Y ⟶ X} [LocallyOfFiniteType (g ≫ sX)] (hY : IsNormalVariety k (g ≫ sX))
    (hYsm : IsSmoothScheme (g ≫ sX)) (hg : IsBirationalMorphism g)
    [IsDominant g] {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K ∧
      (divisorOfForm (pullbackRationalPluriForms sX g ω)).IsCanonicalDivisor (g ≫ sX) n := by
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (g ≫ sX) := hY.1
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hωK : divisorOfForm ω = K := Finsupp.ext fun Γ => by
    change (divisorOfForm ω).coeff Γ = K.coeff Γ
    rw [coeff_divisorOfForm, hω Γ]
  have hn := hK.topologicalKrullDim_eq
  have hdim : topologicalKrullDim Y = n := by
    rw [← hn]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg).symm
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hτ := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' g
    hg.functionFieldMap_bijective hd hω0
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (g ≫ sX) hYsm hdim
  refine ⟨ω, hω0, hωK, ?_⟩
  have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hτ
  rw [one_zsmul] at h
  exact hK₀.of_linearlyEquivalent h

end ResolutionCopy

/-! ### Restricting an snc divisor to an open subscheme -/

section OpenSNC

open MMP.Threefold.Mori.OpenRestriction MMP.Resolution

/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

/-- If the restriction `Δ|_U` of a divisor to an open `U` is snc, then `U ∩ Supp Δ` is a
divisor with simple normal crossings on `U`. -/
private theorem isSNCClosedSubset_preimage_of_isSNC_restrictOpen {R : Type*} [Zero R]
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {Δ : DivisorWithCoeffs R X}
    {U : X.Opens} (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX)) :
    IsSNCClosedSubset (U.ι ≫ sX)
      (U.ι ⁻¹' (Δ.support.sup fun E => (E.idealSheaf.support : Set X))) := by
  classical
  set R' := (Δ.restrictOpen U).support with hR
  have hsupp : (∑ E ∈ R', Finsupp.single E (1 : ℤ)).support = R' :=
    Finset.ext (mem_support_sum_single R')
  have hT : DivisorWithCoeffs.IsSNC (U.ι ≫ sX) (∑ E ∈ R', Finsupp.single E (1 : ℤ)) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq hsupp).mpr hsnc
  have h := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hT
  rw [hsupp] at h
  convert h using 1
  ext x
  rw [Finset.sup_set_eq_biUnion]
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨E, hE, hxE⟩
    obtain ⟨P, hP⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
      U.ι E x hxE
    refine ⟨P, ?_, ?_⟩
    · rw [hR, Finsupp.mem_support_iff]
      change Δ.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) ≠ 0
      rw [hP]
      exact Finsupp.mem_support_iff.mp hE
    · rw [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x, hP]
      exact hxE
  · rintro ⟨P, hP, hxP⟩
    refine ⟨OpenWeilRestriction.primeDivisorMap U.ι P, ?_, ?_⟩
    · rw [hR, Finsupp.mem_support_iff] at hP
      exact Finsupp.mem_support_iff.mpr hP
    · exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).2 hxP

end OpenSNC

/-! ### Nefness of a `ℚ`-linearly trivial difference -/

/-- A `ℚ`-divisor `ℚ`-linearly equivalent to another differs from it by a nef `ℚ`-divisor. -/
private theorem isNef_sub_of_qLinearlyEquivalent {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {D₁ D₂ : QDivisor X} (h : D₁.QLinearlyEquivalent D₂) :
    (D₁ - D₂).IsNef k sX := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  have hq : (D₁ - D₂).IsQCartier :=
    ⟨m, by exact_mod_cast hm.ne', principalDivisor φ, hφ.symm, Divisor.isCartier_principalDivisor φ⟩
  refine ⟨hq, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hq hm (principalDivisor φ)
    (Divisor.isCartier_principalDivisor φ) hφ.symm,
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX i hC.le _
      ⟨φ, by rw [sub_zero]⟩]
  simp

/-! ### The resolution -/

/-- A coefficient-one component of a `ℚ`-divisor is a stratum of its round-down. -/
private theorem isSNCStratum_support_of_coeff_eq_one {X : Scheme.{u}} (B : QDivisor X)
    {P : MMP.Mori.PrimeDivisor X} (hP : B.coeff P = 1) :
    MMP.Fourfold.IsSNCStratum B.roundDown (P.support : Set X) := by
  refine ⟨{P}, fun Q hQ => ?_, ⟨?_, ?_⟩, fun T hT hle => ?_⟩
  · rw [Finset.mem_singleton] at hQ
    subst hQ
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
      DivisorWithCoeffs.coeff_roundDown, hP]
    norm_num
  · exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P
  · simp
  · simpa using hT.2

/-- The generic point of a prime divisor not contained in `Supp A` lies off `Supp A`. -/
private theorem genericPoint_notMem_supp_of_not_subset {X : Scheme.{u}}
    {P : MMP.Mori.PrimeDivisor X} {A : QDivisor X} (hA : ¬ (P.support : Set X) ⊆ A.supp) :
    P.genericPoint ∉ A.supp := fun hmem => hA <| by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.mpr hmem) A.supp.isClosed

/-- If the components `T ⊆ Supp B` through `x₀` have coefficient one and their number is the
codimension of `x₀`, then the closure of `x₀` is a stratum of `⌊B⌋`. -/
private theorem isSNCStratum_closure_of_card_eq_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hB : B.IsSNC sX) {x₀ : X}
    {T : Finset (MMP.Mori.PrimeDivisor X)} (hTB : T ⊆ B.support)
    (hTx : ∀ G ∈ T, x₀ ∈ G.support) (hB1T : ∀ G ∈ T, B.coeff G = 1)
    (hcoh : Order.coheight x₀ = T.card) :
    MMP.Fourfold.IsSNCStratum B.roundDown (closure {x₀}) := by
  refine ⟨T, fun G hG => ?_, ⟨isIrreducible_singleton.closure, ?_⟩, fun W hW hle => ?_⟩
  · rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
      DivisorWithCoeffs.coeff_roundDown, hB1T G hG]
    norm_num
  · refine closure_minimal ?_ (isClosed_biInter fun G _ =>
      MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support G)
    simp only [Set.singleton_subset_iff, Set.mem_iInter]
    exact fun G hG => hTx G hG
  · obtain ⟨w, hw⟩ := QuasiSober.sober hW.1.closure isClosed_closure
    have hwW : x₀ ∈ closure {w} := by
      rw [hw.def]
      exact subset_closure (hle (subset_closure rfl))
    have hwT : ∀ G ∈ T, w ∈ G.support := by
      intro G hG
      have hcl : closure W ⊆ (G.support : Set X) := closure_minimal
        (hW.2.trans (Set.biInter_subset_of_mem hG))
        (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support G)
      exact hcl hw.mem
    have hcw := card_le_coheight_of_isSNC hB w T hTB hwT
    have hwx : w = x₀ := by
      by_contra hne
      have hsp : w ⤳ x₀ := specializes_iff_mem_closure.mpr hwW
      have hlt : x₀ < w := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun h =>
        hne (hsp.antisymm (Scheme.le_iff_specializes.mp h)).eq
      have hfin : Order.coheight w < ⊤ := by
        obtain ⟨N, z, -, hz, -, -⟩ := hB.2 w
        rw [coheight_eq_of_isRegularSystemOfParameters hz]
        exact ENat.coe_lt_top N
      have := Order.coheight_strictAnti hlt hfin
      rw [hcoh] at this
      exact absurd hcw (not_le.mpr this)
    rw [← hwx, hw.def]
    exact subset_closure

/-- If the point of `Spec 𝒪_{Y,σ}` cut out by `(z_j : j ∈ J')`, for a regular system of
parameters `z`, maps to `σ`, then `J'` contains every index. -/
private theorem mem_of_fromSpecStalk_span_image_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {σ : Y} {N : ℕ} {z : Fin N → Y.presheaf.stalk σ} (hz : IsRegularSystemOfParameters z)
    {J' : Set (Fin N)} (hprime : (Ideal.span (z '' J')).IsPrime)
    (hww : Y.fromSpecStalk σ ⟨Ideal.span (z '' J'), hprime⟩ = σ) (a : Fin N) : a ∈ J' := by
  by_contra ha
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hq : (⟨Ideal.span (z '' J'), hprime⟩ : PrimeSpectrum (Y.presheaf.stalk σ)) =
      IsLocalRing.closedPoint _ := by
    apply (Y.fromSpecStalk σ).isEmbedding.injective
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hww
  have hzG : z a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk σ) := by
    rw [← hz.1]
    exact Ideal.subset_span ⟨_, rfl⟩
  have hmax : Ideal.span (z '' J') = IsLocalRing.maximalIdeal _ :=
    congrArg PrimeSpectrum.asIdeal hq
  rw [← hmax] at hzG
  exact notMem_span_image_of_notMem hz ha hzG

private theorem add_ceil_max_neg_nonneg (x : ℚ) : 0 ≤ x + ⌈max (-x) 0⌉ := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right (by linarith)]
    simp [h]
  · rw [max_eq_left (by linarith)]
    linarith [Int.le_ceil (-x)]

private theorem add_ceil_max_neg_le_one {x : ℚ} (hx : x ≤ 1) : x + ⌈max (-x) 0⌉ ≤ 1 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right (by linarith)]
    simp [hx]
  · rw [max_eq_left (by linarith)]
    linarith [Int.ceil_lt_add_one (-x)]

private theorem eq_one_of_add_ceil_max_neg_eq_one {x : ℚ} (hx : x + ⌈max (-x) 0⌉ = 1) :
    x = 1 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right (by linarith)] at hx
    simpa using hx
  · rw [max_eq_left (by linarith)] at hx
    linarith [Int.ceil_lt_add_one (-x)]

/-- Finitely many perturbations `a i + (ε / t) b i` of values `a i < 1` stay `< 1` for some
`0 < ε < 1`. -/
private theorem exists_pos_lt_one_forall_add_div_mul_lt_one {ι : Type*} (S : Finset ι)
    (a b : ι → ℚ) (t : ℚ) :
    ∃ ε : ℚ, 0 < ε ∧ ε < 1 ∧ ∀ i ∈ S, a i < 1 → a i + ε / t * b i < 1 := by
  have h0 : ∀ᶠ ε in nhdsWithin (0 : ℚ) (Set.Ioi 0), 0 < ε := eventually_mem_nhdsWithin
  have h1 : ∀ᶠ ε in nhdsWithin (0 : ℚ) (Set.Ioi 0), ε < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℚ) < 1))
  have h2 : ∀ᶠ ε in nhdsWithin (0 : ℚ) (Set.Ioi 0),
      ∀ i ∈ S, a i < 1 → a i + ε / t * b i < 1 := by
    refine (Filter.eventually_all_finset S).2 fun i _ => ?_
    by_cases hi : a i < 1
    · have hc : Continuous fun ε : ℚ => a i + ε / t * b i := by fun_prop
      have := (hc.tendsto 0).eventually (eventually_lt_nhds (by simpa using hi))
      have h' : ∀ᶠ ε in nhdsWithin (0 : ℚ) (Set.Ioi 0), a i + ε / t * b i < 1 :=
        nhdsWithin_le_nhds this
      exact h'.mono fun ε hε _ => hε
    · exact Filter.Eventually.of_forall fun ε h => absurd h hi
  obtain ⟨ε, hε⟩ := (h0.and (h1.and h2)).exists
  exact ⟨ε, hε.1, hε.2.1, hε.2.2⟩

/-- A coefficient `γ + a d + b [F ∈ T]` of a perturbed boundary lies in `[0, 1]`, and equals one
only if `γ` does, when `γ, d` vanish off `S₀`, `T` is disjoint from `S₀`, `d` vanishes where
`γ = 1`, and the perturbation `γ + a d` stays below one where `γ < 1`. -/
private theorem perturbed_coeff_bounds {γ d a b : ℚ} {inS inT : Prop} [Decidable inT]
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hd0 : 0 ≤ d) (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hγS : γ ≠ 0 → inS) (hdS : d ≠ 0 → inS) (hTS : inT → ¬ inS) (hfloor : γ = 1 → d = 0)
    (hε : inS → γ < 1 → γ + a * d < 1) :
    0 ≤ γ + a * d + b * (if inT then 1 else 0) ∧ γ + a * d + b * (if inT then 1 else 0) ≤ 1 ∧
      (γ + a * d + b * (if inT then 1 else 0) = 1 → γ = 1) := by
  have hγd : ¬ inS → γ = 0 ∧ d = 0 := fun h => ⟨by_contra (h ∘ hγS), by_contra (h ∘ hdS)⟩
  by_cases hT : inT
  · obtain ⟨rfl, rfl⟩ := hγd (hTS hT)
    simp only [if_pos hT, mul_zero, mul_one, zero_add]
    exact ⟨hb0, hb1.le, fun h => by linarith⟩
  simp only [if_neg hT, mul_zero, add_zero]
  have had : 0 ≤ a * d := mul_nonneg ha hd0
  by_cases hS : inS
  · rcases hγ1.lt_or_eq with h | h
    · have := hε hS h
      exact ⟨by linarith, this.le, fun h' => by linarith⟩
    · rw [h, hfloor h]
      simp
  · obtain ⟨rfl, rfl⟩ := hγd hS
    simp

/-- Off `T`, a perturbed coefficient `γ + a d` with `0 ≤ γ`, `0 < a d` and `γ + a d < 1` has
nonzero fractional part. -/
private theorem fract_perturbed_coeff_ne_zero {γ d a b : ℚ} {inT : Prop} [Decidable inT]
    (hT : ¬ inT) (hγ0 : 0 ≤ γ) (ha : 0 < a) (hd : 0 < d) (h1 : γ + a * d < 1) :
    Int.fract (γ + a * d + b * (if inT then 1 else 0)) ≠ 0 := by
  have := mul_pos ha hd
  rw [if_neg hT, mul_zero, add_zero, Int.fract_eq_self.mpr ⟨by linarith, h1⟩]
  exact (by linarith : (0 : ℚ) < γ + a * d).ne'

/-- A stratum of `⌊Δ⌋` is not contained in `Ex(g)` when the coefficient-one components of `Δ`
lie in an snc family `S₀` containing every component of `Ex(g)`, and are not exceptional. -/
private theorem not_subset_exceptionalSet_of_isSNCStratum_roundDown {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [TopologicalSpace.NoetherianSpace Y]
    {sY : Y ⟶ Spec (.of k)} (g : Y ⟶ X)
    (hpure : MMP.Mori.IsPureCodimOne (MMP.Mori.exceptionalSet g))
    {S₀ : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsncS₀ : DivisorWithCoeffs.IsSNC sY (∑ E ∈ S₀, Finsupp.single E (1 : ℤ)))
    (hexS₀ : ∀ G : MMP.Mori.PrimeDivisor Y, G.genericPoint ∈ (exceptionalSet g : Set Y) → G ∈ S₀)
    {Δ : QDivisor Y} (hΔ0 : ∀ F, 0 ≤ Δ.coeff F) (hΔ1 : ∀ F, Δ.coeff F ≤ 1)
    (hS₀ : ∀ F, Δ.coeff F = 1 → F ∈ S₀)
    (hEx : ∀ F, Δ.coeff F = 1 → F.genericPoint ∉ (exceptionalSet g : Set Y))
    {S : Set Y} (hS : MMP.Fourfold.IsSNCStratum Δ.roundDown S) :
    ¬ S ⊆ (exceptionalSet g : Set Y) := by
  obtain ⟨J, hJ, hmax⟩ := hS
  intro hSE
  have hJΔ : ∀ F ∈ J, Δ.coeff F = 1 := by
    intro F hF
    have h := Finsupp.mem_support_iff.mp (hJ hF)
    rw [← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_roundDown] at h
    rcases (hΔ1 F).lt_or_eq with hlt | heq
    · exact absurd (Int.floor_eq_zero_iff.mpr ⟨hΔ0 F, hlt⟩) h
    · exact heq
  have hJS₀ : ∀ F ∈ J, F ∈ S₀ := fun F hF => hS₀ F (hJΔ F hF)
  -- the generic point `s` of `S`
  have hSirr := hmax.1.1
  have hScl : IsClosed S := by
    have hcl : closure S ⊆ S := hmax.2 ⟨hSirr.closure, closure_minimal hmax.1.2
      (isClosed_biInter fun F _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support F)⟩
      subset_closure
    exact closure_subset_iff_isClosed.mp hcl
  obtain ⟨σ, hσ⟩ := QuasiSober.sober hSirr hScl
  have hσS : σ ∈ S := hσ.mem
  have hσJ : ∀ F ∈ J, σ ∈ F.support := fun F hF => by
    have := hmax.1.2 hσS
    simp only [Set.mem_iInter] at this
    exact this F hF
  -- a component `G` of `Ex(g)` through `σ`
  obtain ⟨W, hW, hσW⟩ := Set.mem_sUnion.1 ((MMP.Resolution.Aux.finite_and_cover_componentsOf
    (isClosed_exceptionalSet g)).2 (hSE hσS))
  obtain ⟨G, hG⟩ := exists_primeDivisor_support_eq (isClosed_exceptionalSet g) hpure hW
  have hGE : G.genericPoint ∈ (exceptionalSet g : Set Y) := by
    have := MMP.Flips.primeDivisor_genericPoint_mem_support G
    rw [hG] at this
    exact hW.1.2 this
  have hGJ : G ∉ J := fun h => hEx G (hJΔ G h) hGE
  have hGS₀ : G ∈ S₀ := hexS₀ G hGE
  have hσG : σ ∈ G.support := by rw [hG]; exact hσW
  -- the local picture at `σ`
  obtain ⟨N, z, j, hz, hj, hI⟩ := hsncS₀.2 σ
  have hmemS : ∀ E ∈ S₀, σ ∈ E.support →
      E ∈ (∑ E ∈ S₀, Finsupp.single E (1 : ℤ)).support ∧ σ ∈ E.support := fun E hE hσE =>
    ⟨(mem_support_sum_single S₀ E).mpr hE, hσE⟩
  set J' : Set (Fin N) := Set.range fun F : J => j ⟨F.1, hmemS F.1 (hJS₀ F.1 F.2) (hσJ F.1 F.2)⟩
  have hGJ' : j ⟨G, hmemS G hGS₀ hσG⟩ ∉ J' := by
    rintro ⟨F, hF⟩
    have h2 : (F : MMP.Mori.PrimeDivisor Y) = G := congrArg Subtype.val (hj hF)
    exact hGJ (h2 ▸ F.2)
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hprime : (Ideal.span (z '' J')).IsPrime := by
    have h := MMP.Resolution.span_image_isPrime_of_isRegularSystemOfParameters hz J'.toFinset
    rwa [Set.coe_toFinset] at h
  set q : PrimeSpectrum (Y.presheaf.stalk σ) := ⟨Ideal.span (z '' J'), hprime⟩
  set w := Y.fromSpecStalk σ q
  have hwJ : ∀ F ∈ J, w ∈ F.support := by
    intro F hF
    have h := (MMP.Resolution.fromSpecStalk_mem_support_iff_stalk_le F.idealSheaf σ q).mpr
    refine h ?_
    rw [hI ⟨F, hmemS F (hJS₀ F hF) (hσJ F hF)⟩, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨_, ⟨⟨F, hF⟩, rfl⟩, rfl⟩
  have hwσ : w ⤳ σ := MMP.Resolution.fromSpecStalk_specializes_self σ q
  have hwS : closure {w} ⊆ S := by
    refine hmax.2 ⟨isIrreducible_singleton.closure, closure_minimal ?_
      (isClosed_biInter fun F _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support F)⟩
      ?_
    · simp only [Set.singleton_subset_iff, Set.mem_iInter]
      exact fun F hF => hwJ F hF
    · rw [← hσ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr
        (specializes_iff_mem_closure.mp hwσ)) isClosed_closure
  have hww : w = σ := by
    have h1 : w ∈ closure {σ} := by rw [hσ.def]; exact hwS (subset_closure rfl)
    exact (hwσ.antisymm (specializes_iff_mem_closure.mpr h1)).eq
  exact hGJ' (mem_of_fromSpecStalk_span_image_eq hz hprime hww _)

/-- Over the complement of `Supp D ∪ Supp D'`, the union of the components of `B`, `D` and `D'`
is the union of the components of `B`. -/
private theorem preimage_sup_support_union_eq {X : Scheme.{u}}
    [DecidableEq (MMP.Mori.PrimeDivisor X)] (B : QDivisor X) (D : Divisor X) (D' : QDivisor X) :
    Scheme.Opens.ι ((D.supp ⊔ D'.supp).compl : X.Opens) ⁻¹'
        ((B.support ∪ D.support ∪ D'.support).sup fun E => (E.idealSheaf.support : Set X)) =
      Scheme.Opens.ι ((D.supp ⊔ D'.supp).compl : X.Opens) ⁻¹'
        (B.support.sup fun E => (E.idealSheaf.support : Set X)) := by
  set U : X.Opens := (D.supp ⊔ D'.supp).compl
  ext x
  simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂, exists_prop]
  constructor
  · rintro ⟨P, hP, hxP⟩
    refine ⟨P, ?_, hxP⟩
    have hxU : U.ι x ∈ U := by
      have : U.ι x ∈ Set.range U.ι := ⟨x, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    rw [Finset.mem_union, Finset.mem_union] at hP
    rcases hP with (hP | hP) | hP
    · exact hP
    · exact absurd (Or.inl (DivisorWithCoeffs.support_subset_supp
        (Finsupp.mem_support_iff.mp hP) hxP)) hxU
    · exact absurd (Or.inr (DivisorWithCoeffs.support_subset_supp
        (Finsupp.mem_support_iff.mp hP) hxP)) hxU
  · rintro ⟨P, hP, hxP⟩
    exact ⟨P, Finset.mem_union_left _ (Finset.mem_union_left _ hP), hxP⟩

/-- For a crepant boundary `Δ_Y` of an snc pair `(X, B)` with coefficients at most one on a
smooth variety, every exceptional divisor has coefficient `< 1` in `Δ_Y`, provided `g` is
biregular at the generic point of every stratum of `⌊B⌋`. -/
private theorem coeff_lt_one_of_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hB : B.IsSNC sX)
    (hB1 : ∀ E, B.coeff E ≤ 1) {g : Y ⟶ X} (hY : IsNormalVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K B g hY hg ΔY)
    (hstr : ∀ x : X, MMP.Fourfold.IsSNCStratum B.roundDown (closure {x}) →
      x ∈ biregularLocus g)
    {F : MMP.Mori.PrimeDivisor Y} (hF : (⟨Y, g, hY, hg, F⟩ : DivisorOver k sX).IsExceptional) :
    ΔY.coeff F < 1 := by
  classical
  by_contra hge
  push Not at hge
  have hsncB : DivisorWithCoeffs.IsSNC sX (∑ E ∈ B.support, Finsupp.single E (1 : ℤ)) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq (Finset.ext (mem_support_sum_single _))).mpr hB
  obtain ⟨c, T', hc, hT', -, hcard, -, -, hineq⟩ := le_isDiscrepancy_of_isSNC hX hsm hK
    (subset_refl _) hsncB (fun E _ => hB1 E) _ hF (hΔY F)
  subst hT'
  set x₀ := g F.genericPoint
  set T := B.support.filter (fun G => x₀ ∈ G.support)
  change -1 + ∑ G ∈ T, (1 - B.coeff G) + ((c : ℚ) - T.card) ≤ -ΔY.coeff F at hineq
  have hsum0 : 0 ≤ ∑ G ∈ T, (1 - B.coeff G) :=
    Finset.sum_nonneg fun G _ => by linarith [hB1 G]
  have hcT : (T.card : ℚ) ≤ c := by exact_mod_cast hcard
  have hsumeq : ∑ G ∈ T, (1 - B.coeff G) = 0 := by linarith
  have hcTeq : (T.card : ℚ) = c := by linarith
  have hB1T : ∀ G ∈ T, B.coeff G = 1 := fun G hG => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun G _ => by linarith [hB1 G])).mp hsumeq G hG
    linarith
  have hS := isSNCStratum_closure_of_card_eq_coheight hB (Finset.filter_subset _ _)
    (fun G hG => (Finset.mem_filter.mp hG).2) hB1T (by rw [← hc]; exact_mod_cast hcTeq.symm)
  exact mem_exceptionalSet.mp (MMP.Positivity.support_subset_exceptionalSet F hF
    (MMP.Flips.primeDivisor_genericPoint_mem_support F)) (hstr x₀ hS)

/-- **The resolution data.** A projective birational `g : V' ⟶ V` from a smooth projective
variety, a canonical divisor `K'`, an snc boundary `Δ` on `V'` none of whose floor strata lies in
the exceptional set, an effective `g`-exceptional `E` vanishing at every strict transform, and
divisors `M' = g^*M + E`, `D₁ = g^*D` with `M' ∼_ℚ K' + Δ` and `Supp D₁ ⊆ Supp {Δ}`. -/
private theorem exists_resolution_data {V : Scheme.{0}}
    (f : V ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] {n : ℕ} {K : Divisor V}
    (hK : K.IsCanonicalDivisor f n)
    (B : QDivisor V) (hB : B.IsSNC f) (hB0 : ∀ E, 0 ≤ B.coeff E) (hB1 : ∀ E, B.coeff E ≤ 1)
    (H : QDivisor V) (hH : MMP.Fourfold.QDivisor.IsRelativelySemiample f H)
    (M : Divisor V)
    (hM : (Divisor.toQDivisor M).QLinearlyEquivalent (Divisor.toQDivisor K + B + H))
    (D : Divisor V) (hD : 0 ≤ D) (D' : QDivisor V) (hD' : 0 ≤ D') {t : ℚ} (ht : 0 < t)
    (htH : (t • H).QLinearlyEquivalent (Divisor.toQDivisor D + D'))
    (hDS : MMP.Fourfold.ContainsNoStratum B.roundDown (D.supp : Set V))
    (hD'S : MMP.Fourfold.ContainsNoStratum B.roundDown (D'.supp : Set V)) :
    ∃ (V' : Scheme.{0}) (_ : IsIntegral V') (_ : IsLocallyNoetherian V') (_ : IsNormal V')
      (_ : CompactSpace V') (g : V' ⟶ V) (_ : IsDominant g)
      (_ : MMP.Mori.IsProjectiveVariety ℂ (g ≫ f)),
      IsSmoothScheme (g ≫ f) ∧ IsProjective g ∧ IsBirationalMorphism g ∧
      ∃ (K' : Divisor V') (Δ : QDivisor V') (E M' D₁ : Divisor V'),
        K'.IsCanonicalDivisor (g ≫ f) n ∧ Δ.IsSNC (g ≫ f) ∧ (∀ F, 0 ≤ Δ.coeff F) ∧
        (∀ F, Δ.coeff F ≤ 1) ∧
        (∀ S : Set V', MMP.Fourfold.IsSNCStratum Δ.roundDown S →
          ¬ S ⊆ (exceptionalSet g : Set V')) ∧
        (Divisor.toQDivisor M').QLinearlyEquivalent (Divisor.toQDivisor K' + Δ) ∧
        0 ≤ D₁ ∧ D₁.support ⊆ Δ.fract.support ∧ 0 ≤ E ∧
        (∃ hBM, M.IsPullback g hBM (M' - E)) ∧ (∃ hBD, (M + D).IsPullback g hBD (M' + D₁ - E)) ∧
        ∀ P : MMP.Mori.PrimeDivisor V, ∃ F : MMP.Mori.PrimeDivisor V',
          g F.genericPoint = P.genericPoint ∧ IsIso (g.stalkMap F.genericPoint) ∧
            E.coeff F = 0 := by
  classical
  -- the variety `V`
  have hXv : AlgebraicGeometry.IsVariety ℂ f :=
    (inferInstance : MMP.Mori.IsProjectiveVariety ℂ f).toIsVariety
  haveI := hXv
  haveI : IsIntegral V := hXv.toIsIntegral
  haveI : LocallyOfFiniteType f := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact f := hXv.toQuasiCompact
  haveI : AlgebraicGeometry.IsNoetherian V := {}
  have hXn : IsNormalVariety ℂ f := ⟨hXv, inferInstance⟩
  have hcV : ∀ N : Divisor V, N.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  -- the snc-preserving log resolution of `Supp (B + D + D')`
  set Pset : Finset (MMP.Mori.PrimeDivisor V) := B.support ∪ D.support ∪ D'.support with hPset
  obtain ⟨V', g, hres, hpure, hsnc, hisoU⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset f hXn Pset
  haveI : IsProper g := hres.isProjective.isProper
  have hgb := hres.isBirationalMorphism
  have hgres : IsSmoothResolution f g := ⟨inferInstance, hgb, hres.isSmoothScheme⟩
  obtain ⟨hY, -, -⟩ := hgres.isNormalVariety hXn
  haveI : IsIntegral V' := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (g ≫ f) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ f)
  haveI : IsNormal V' := hY.2
  haveI : QuasiCompact (g ≫ f) := hY.1.toQuasiCompact
  haveI : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace (g ≫ f)
  haveI : AlgebraicGeometry.IsNoetherian V' := {}
  haveI : AlgebraicGeometry.IsVariety ℂ (g ≫ f) := hY.1
  haveI := hgb.isDominant
  have hsm' : IsSmoothScheme (g ≫ f) := hres.isSmoothScheme
  have hprojY : MMP.Mori.IsProjectiveVariety ℂ (g ≫ f) :=
    (MMP.Mori.isProjectiveVariety_iff ℂ (g ≫ f)).2 ⟨hres.isVariety_source,
      isProjectiveMorphism_of_isProjective_of_isAffine (g ≫ f) (hres.isProjective.comp
        ((MMP.Mori.isProjectiveVariety_iff ℂ f).1 inferInstance).2.isProjective)⟩
  have hcY : ∀ N : Divisor V', N.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm'
  -- the components `S₀` of `Ex(g) ∪ g⁻¹(Supp (B + D + D'))`
  obtain ⟨S₀, hsncS₀, hUS₀⟩ := exists_finset_isSNC_of_isSNCClosedSubset (g ≫ f) hsm' hsnc
  have hmemS₀ : ∀ G : MMP.Mori.PrimeDivisor V',
      G.genericPoint ∈ (exceptionalSet g : Set V') ∪
        g ⁻¹' (Pset.sup fun E => (E.idealSheaf.support : Set V)) → G ∈ S₀ := fun G hG => by
    rw [← hUS₀] at hG
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hG
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE
  -- `g` is an isomorphism over `U = V ∖ Supp (D + D')`
  set U : V.Opens := (D.supp ⊔ D'.supp).compl with hUdef
  have hgU : IsIso (g ∣_ U) := by
    refine hisoU U (MMP.Threefold.Resolution.isSmoothScheme_ι ℂ hsm U) ?_
    haveI : ∀ E : MMP.Mori.PrimeDivisor V,
        LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ f) := fun E =>
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := E.idealSheaf.subschemeι ≫ f)).mpr
        inferInstance
    have h := isSNCClosedSubset_preimage_of_isSNC_restrictOpen f (isSNC_restrictOpen f hB U)
    convert h using 1
    exact preimage_sup_support_union_eq B D D'
  -- the canonical divisors and the crepant boundary
  obtain ⟨ω, hω0, hωK, hK'⟩ :=
    exists_isCanonicalDivisor_divisorOfForm_pullback hXn hY hsm' hgb hK
  set K' := divisorOfForm (pullbackRationalPluriForms f g ω)
  have hBq : (Divisor.toQDivisor K + B).IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _
  have hPw : IsPairWith f n K B := ⟨hXn, hK, hBq⟩
  have hP : IsPair f B := hPw.isPair
  obtain ⟨ΔY, hΔY⟩ := (IsPair.existsUnique_isCrepantBoundary hP hK g hY hgb).1.exists
  obtain ⟨-, -, hBpb, hpbKB⟩ := IsPair.isPullback_of_isCrepantBoundary hP g hY hgb hK hK'
    (Or.inl ⟨ω, hω0, hωK, rfl⟩) hΔY
  have hqKB : qpb g hcV (Divisor.toQDivisor K + B) = Divisor.toQDivisor K' + ΔY :=
    qpb_eq_of_isPullback g hcV hpbKB
  -- the coefficients of `Δ_Y`
  have hUbir : U ≤ biregularLocus g := le_biregularLocus hgU
  have hexc : ∀ F : MMP.Mori.PrimeDivisor V',
      (⟨V', g, hY, hgb, F⟩ : DivisorOver ℂ f).IsExceptional → ΔY.coeff F < 1 := fun F hFe =>
    coeff_lt_one_of_isExceptional hXn hsm hK hB hB1 hY hgb hΔY (fun x hx => hUbir (by
      rintro (h | h)
      · exact hDS _ hx (closure_minimal (Set.singleton_subset_iff.mpr h) D.supp.isClosed)
      · exact hD'S _ hx (closure_minimal (Set.singleton_subset_iff.mpr h) D'.supp.isClosed))) hFe
  have hnexc : ∀ F : MMP.Mori.PrimeDivisor V',
      ¬ (⟨V', g, hY, hgb, F⟩ : DivisorOver ℂ f).IsExceptional →
        ∃ P : MMP.Mori.PrimeDivisor V, ΔY.coeff F = B.coeff P ∧
          g F.genericPoint = P.genericPoint :=
    fun F hF => exists_coeff_eq_of_not_isExceptional hPw hY hgb hΔY hF
  have hΔY1 : ∀ F, ΔY.coeff F ≤ 1 := by
    intro F
    by_cases hF : (⟨V', g, hY, hgb, F⟩ : DivisorOver ℂ f).IsExceptional
    · exact (hexc F hF).le
    · obtain ⟨P, hFP, -⟩ := hnexc F hF
      rw [hFP]
      exact hB1 P
  -- `E = ⌈B_g⌉` and `Γ = Δ_Y + E`
  set E : Divisor V' := ((-ΔY).mapCoeffs (max · 0) (by simp)).roundUp with hEdef
  have hEcoeff : ∀ F, E.coeff F = ⌈max (-ΔY.coeff F) 0⌉ := fun F => by
    rw [hEdef, DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_mapCoeffs,
      DivisorWithCoeffs.coeff_neg]
  have hE0 : 0 ≤ E := fun F => by
    change (0 : ℤ) ≤ E.coeff F
    rw [hEcoeff]
    exact Int.ceil_nonneg (le_max_right _ _)
  set Γ : QDivisor V' := ΔY + Divisor.toQDivisor E with hΓdef
  have hΓcoeff : ∀ F, Γ.coeff F = ΔY.coeff F + ⌈max (-ΔY.coeff F) 0⌉ := fun F => by
    rw [hΓdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hEcoeff]
  have hΓ0 : ∀ F, 0 ≤ Γ.coeff F := fun F => by
    rw [hΓcoeff]
    exact add_ceil_max_neg_nonneg _
  have hΓ1 : ∀ F, Γ.coeff F ≤ 1 := fun F => by
    rw [hΓcoeff]
    exact add_ceil_max_neg_le_one (hΔY1 F)
  have hΓeq1 : ∀ F, Γ.coeff F = 1 → ΔY.coeff F = 1 := fun F hF => by
    rw [hΓcoeff] at hF
    exact eq_one_of_add_ceil_max_neg_eq_one hF
  have hΓsupp : ∀ F, Γ.coeff F ≠ 0 → F ∈ S₀ := by
    intro F hF
    have hΔF : F ∈ ΔY.support := by
      rw [Finsupp.mem_support_iff]
      intro h0
      apply hF
      have h0' : ΔY.coeff F = 0 := h0
      rw [hΓcoeff, h0']
      simp
    refine hmemS₀ F ?_
    rcases genericPoint_mem_exceptionalSet_or_mem_of_mem_support hPw hY hgb hΔY hΔF with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at h ⊢
      obtain ⟨P, hP, hgP⟩ := h
      exact ⟨P, by rw [hPset]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hP), hgP⟩
  -- the pull-backs `g^*M`, `g^*D`, `g^*D'`
  set D₁ : Divisor V' := dpb g hcV D with hD₁def
  set Dq : QDivisor V' := qpb g hcV (Divisor.toQDivisor D) + qpb g hcV D' with hDqdef
  have hDq0 : 0 ≤ Dq := add_nonneg (qpb_nonneg g hcV (fun P => by
    change (0 : ℚ) ≤ (D P : ℚ); exact_mod_cast hD P)) (qpb_nonneg g hcV hD')
  have hDqsupp : ∀ F, Dq.coeff F ≠ 0 → F ∈ S₀ := fun F hF =>
    hmemS₀ F (Or.inr (mem_sup_support_of_coeff_qpb_add_ne_zero g hcV
      (fun Q hQ => by
        rw [hPset]
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [Finsupp.mem_support_iff] at hQ ⊢
        exact fun h => hQ (by
          change ((D Q : ℤ) : ℚ) = 0
          rw [h]
          rfl))
      (fun Q hQ => by
        rw [hPset]
        exact Finset.mem_union_right _ hQ) hF))
  -- on a floor component of `Γ`, the pull-back of `D + D'` vanishes
  -- a floor component of `Γ` has generic point off `Supp D ∪ Supp D'` and off `Ex(g)`
  have hfloorP : ∀ F, Γ.coeff F = 1 → ∃ P : MMP.Mori.PrimeDivisor V, B.coeff P = 1 ∧
      g F.genericPoint = P.genericPoint := by
    intro F hF
    have hΔF := hΓeq1 F hF
    have hFne : ¬ (⟨V', g, hY, hgb, F⟩ : DivisorOver ℂ f).IsExceptional := fun h =>
      (hexc F h).ne hΔF
    obtain ⟨P, hFP, hgP⟩ := hnexc F hFne
    exact ⟨P, hFP.symm.trans hΔF, hgP⟩
  have hfloorEx : ∀ F, Γ.coeff F = 1 → F.genericPoint ∉ (exceptionalSet g : Set V') := by
    intro F hF hFE
    obtain ⟨P, hBP, hgP⟩ := hfloorP F hF
    have hPS := isSNCStratum_support_of_coeff_eq_one B hBP
    have hPU : P.genericPoint ∈ U := by
      rintro (h | h)
      · exact genericPoint_notMem_supp_of_not_subset (A := Divisor.toQDivisor D)
          (by rw [Divisor.supp_toQDivisor]; exact hDS _ hPS)
          (by rw [Divisor.supp_toQDivisor]; exact h)
      · exact genericPoint_notMem_supp_of_not_subset (hD'S _ hPS) h
    exact mem_exceptionalSet.mp hFE (hgP ▸ hUbir hPU)
  have hfloor : ∀ F, Γ.coeff F = 1 → Dq.coeff F = 0 := by
    intro F hF
    obtain ⟨P, hFP, hgP⟩ := hfloorP F hF
    have hPS := isSNCStratum_support_of_coeff_eq_one B hFP
    have hnot : ∀ A : QDivisor V, ¬ (P.support : Set V) ⊆ A.supp →
        g F.genericPoint ∉ A.supp := fun A hA => by
      rw [hgP]
      exact genericPoint_notMem_supp_of_not_subset hA
    rw [hDqdef, DivisorWithCoeffs.coeff_add,
      coeff_qpb_eq_zero g hcV _ F (hnot _ (by rw [Divisor.supp_toQDivisor]; exact hDS _ hPS)),
      coeff_qpb_eq_zero g hcV _ F (hnot _ (hD'S _ hPS)), add_zero]
  -- a general member of the free system of `H`, pulled back
  obtain ⟨m, hm, Hm, hHm, t₀, sec, hsec⟩ := exists_sections_of_isRelativelySemiample f hH
  obtain ⟨T, hTlin, hTS, hTsnc⟩ := exists_general_member hXv hgres hcV t₀ sec hsec S₀ hsncS₀
  set HT : Divisor V' := ∑ E ∈ T, Finsupp.single E (1 : ℤ) with hHTdef
  have hHTcoeff : ∀ F, (HT.coeff F : ℚ) = if F ∈ T then 1 else 0 := fun F => by
    rw [hHTdef, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  -- the perturbation parameter
  obtain ⟨ε, hε0, hε1, hεF⟩ : ∃ ε : ℚ, 0 < ε ∧ ε < 1 ∧
      ∀ F ∈ S₀, Γ.coeff F < 1 → Γ.coeff F + ε / t * Dq.coeff F < 1 :=
    exists_pos_lt_one_forall_add_div_mul_lt_one S₀ Γ.coeff Dq.coeff t
  set Δ : QDivisor V' := Γ + (ε / t) • Dq + ((1 - ε) / m) • Divisor.toQDivisor HT with hΔdef
  have hΔcoeff : ∀ F, Δ.coeff F = Γ.coeff F + ε / t * Dq.coeff F +
      (1 - ε) / m * (if F ∈ T then 1 else 0) := fun F => by
    rw [hΔdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul,
      ← hHTcoeff]
    rfl
  have hTnot : ∀ F ∈ T, F ∉ S₀ := fun F hF hF' => Finset.disjoint_left.mp hTS hF hF'
  have htε : 0 ≤ ε / t := div_nonneg hε0.le ht.le
  have hmε : 0 ≤ (1 - ε) / m := div_nonneg (by linarith) (by positivity)
  have hmε1 : (1 - ε) / m < 1 := by
    rw [div_lt_one (by exact_mod_cast hm)]
    have : (1 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  have hΔb : ∀ F, 0 ≤ Δ.coeff F ∧ Δ.coeff F ≤ 1 ∧ (Δ.coeff F = 1 → Γ.coeff F = 1) := fun F => by
    rw [hΔcoeff]
    exact perturbed_coeff_bounds (hΓ0 F) (hΓ1 F) (hDq0 F) htε hmε hmε1 (hΓsupp F) (hDqsupp F)
      (hTnot F) (hfloor F) (hεF F)
  have hΔ0 : ∀ F, 0 ≤ Δ.coeff F := fun F => (hΔb F).1
  have hΔ1 : ∀ F, Δ.coeff F ≤ 1 := fun F => (hΔb F).2.1
  have hΔfloor : ∀ F, Δ.coeff F = 1 → Γ.coeff F = 1 := fun F => (hΔb F).2.2
  -- `Δ` is snc
  have hΔsnc : Δ.IsSNC (g ≫ f) := by
    refine hTsnc.of_support_subset fun F hF => ?_
    rw [mem_support_sum_single]
    have hF' : Δ.coeff F ≠ 0 := Finsupp.mem_support_iff.mp hF
    by_cases hFT : F ∈ T
    · exact Finset.mem_union_left _ hFT
    · refine Finset.mem_union_right _ ?_
      by_contra hFS
      apply hF'
      have h1 : Γ.coeff F = 0 := by by_contra h; exact hFS (hΓsupp F h)
      have h2 : Dq.coeff F = 0 := by by_contra h; exact hFS (hDqsupp F h)
      rw [hΔcoeff, if_neg hFT, h1, h2]
      ring
  -- `M' ∼_ℚ K' + Δ`
  have hlin : (Divisor.toQDivisor (dpb g hcV M + E)).QLinearlyEquivalent
      (Divisor.toQDivisor K' + Δ) :=
    (qLinearlyEquivalent_dpb_add_perturbation g hcV ε hM hqKB ht.ne' htH
      (by exact_mod_cast hm.ne') hHm hTlin).trans
      (QLinearlyEquivalent.of_eq (by rw [hΔdef, hΓdef, hDqdef]; abel))
  -- `Supp g^*D ⊆ Supp {Δ}`
  have hD₁supp : D₁.support ⊆ Δ.fract.support := by
    intro F hF
    have hF0 : D₁.coeff F ≠ 0 := Finsupp.mem_support_iff.mp hF
    have hFpos : (0 : ℚ) < D₁.coeff F := by
      have := dpb_nonneg g hcV hD F
      exact_mod_cast lt_of_le_of_ne this (Ne.symm hF0)
    have hDqF : 0 < Dq.coeff F := by
      rw [hDqdef, DivisorWithCoeffs.coeff_add, qpb_toQDivisor, Divisor.coeff_toQDivisor]
      have := qpb_nonneg g hcV hD' F
      change 0 ≤ (qpb g hcV D').coeff F at this
      linarith
    have hFS := hDqsupp F hDqF.ne'
    have hFT : F ∉ T := fun h => hTnot F h hFS
    have hΓF : Γ.coeff F < 1 := (hΓ1 F).lt_of_ne fun h => hDqF.ne' (hfloor F h)
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_fract,
      hΔcoeff]
    exact fract_perturbed_coeff_ne_zero hFT (hΓ0 F) (div_pos hε0 ht) hDqF (hεF F hFS hΓF)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, g, inferInstance, hprojY,
    hsm', hres.isProjective, hgb, K', Δ, E, dpb g hcV M + E, D₁, hK', hΔsnc, hΔ0, hΔ1,
    fun _ => not_subset_exceptionalSet_of_isSNCStratum_roundDown g hpure hsncS₀
      (fun G hG => hmemS₀ G (Or.inl hG)) hΔ0 hΔ1
      (fun F hF => hΓsupp F (by rw [hΔfloor F hF]; norm_num)) fun F hF => hfloorEx F (hΔfloor F hF),
    hlin, dpb_nonneg g hcV hD, hD₁supp, hE0,
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _, ?_⟩,
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g _, ?_⟩, ?_⟩
  · rw [add_sub_cancel_right]
    exact isPullback_dpb g hcV M
  · rw [show dpb g hcV M + E + D₁ - E = dpb g hcV (M + D) by rw [dpb_add]; abel]
    exact isPullback_dpb g hcV (M + D)
  · intro P
    obtain ⟨F, hFP, hFiso⟩ := exists_primeDivisor_isIso_stalkMap g hgb P
    refine ⟨F, hFP, hFiso, ?_⟩
    have hFne : ¬ (⟨V', g, hY, hgb, F⟩ : DivisorOver ℂ f).IsExceptional := by
      rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hXn]
      change ¬ 2 ≤ Order.coheight (g F.genericPoint)
      rw [hFP, P.coheight_genericPoint]
      norm_num
    obtain ⟨P', hFP', -⟩ := hnexc F hFne
    rw [hEcoeff, hFP', max_eq_right (by linarith [hB0 P']), Int.ceil_zero]

end MMP.FourfoldProofs.MmpLcBpfSemiampleInjectivityProof

end

section

/-!
# Injectivity for an snc log canonical pair with a semiample adjoint difference

Let `V` be a smooth projective complex variety and `B` a `ℚ`-divisor with simple normal crossing
support and coefficients in `[0, 1]`. The *lc strata* of `(V, B)` are `V` itself and the strata of
the reduced part `⌊B⌋`. Let `M` be a Cartier divisor with `M ∼_ℚ K_V + B + H` for a semiample
`ℚ`-divisor `H`, and let `D` be an effective Cartier divisor such that `tH ∼_ℚ D + D'` for some
rational `t > 0` and some effective `ℚ`-divisor `D'`, where neither `Supp D` nor `Supp D'`
contains an lc stratum. Then the map `H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))` induced by
`𝒪_V(M) ⊆ 𝒪_V(M + D)` is injective for every `q`.

## Main results

* `MMP.Mori.injective_derivedCohomologyOverField_map_divisorialSheafInclusion_of_semiample`:
  the injectivity of `H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))`.

## Implementation notes

* The lc strata of the snc pair `(V, B)` are the strata `MMP.Fourfold.IsSNCStratum` of the
  reduced part `⌊B⌋ = MMP.Mori.DivisorWithCoeffs.roundDown B`; the empty intersection gives `V`
  itself. "`D` contains no lc stratum" is `MMP.Fourfold.ContainsNoStratum ⌊B⌋ (Supp D)`.
* Semiampleness of `H` is `MMP.Fourfold.QDivisor.IsRelativelySemiample` over the base `Spec ℂ`.
* On the smooth variety `V` every Weil divisor is Cartier, so `M` and `D` are
  `MMP.Mori.Divisor`s; `K_V` is any `K` with `MMP.Mori.Divisor.IsCanonicalDivisor`.
* `H^q(V, ℱ)` for `q : ℤ` is the `q`-th cohomology of `derivedGlobalSectionsOver f` applied to
  `ℱ` placed in degree zero, and the map is the image of
  `MMP.Mori.Divisor.divisorialSheafInclusion` under these functors.
* The base is `ℂ`.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011],
  Theorem 6.1
* [F. Ambro, *Quasi-log varieties*][Ambro2003]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

open MMP.FourfoldProofs.MmpLcBpfSemiampleInjectivityProof in
/-- **Injectivity with a semiample adjoint difference** (Ambro, Fujino). Let `V` be a smooth
projective complex variety with canonical
divisor `K`, and `B` a `ℚ`-divisor with simple normal crossing support and coefficients in
`[0, 1]`. Let `M` be a divisor with `M ∼_ℚ K + B + H` for a semiample `ℚ`-divisor `H`, and `D` an
effective divisor with `tH ∼_ℚ D + D'` for a rational `t > 0` and an effective `ℚ`-divisor `D'`,
such that neither `Supp D` nor `Supp D'` contains a stratum of `⌊B⌋` (`V` included). Then
`H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))`, induced by `𝒪_V(M) ⊆ 𝒪_V(M + D)`, is injective for every
`q`. -/
@[mmp "thm_mmp_lc_bpf_semiample_injectivity"]
public theorem injective_derivedCohomologyOverField_map_divisorialSheafInclusion_of_semiample
    {V : Scheme.{0}}
    (f : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] {n : ℕ} {K : Divisor V}
    (hK : K.IsCanonicalDivisor f n)
    (B : QDivisor V) (hB : B.IsSNC f) (hB0 : ∀ E, 0 ≤ B.coeff E) (hB1 : ∀ E, B.coeff E ≤ 1)
    (H : QDivisor V) (hH : MMP.Fourfold.QDivisor.IsRelativelySemiample f H)
    (M : Divisor V)
    (hM : (Divisor.toQDivisor M).QLinearlyEquivalent (Divisor.toQDivisor K + B + H))
    (D : Divisor V) (hD : 0 ≤ D) (D' : QDivisor V) (hD' : 0 ≤ D') {t : ℚ} (ht : 0 < t)
    (htH : (t • H).QLinearlyEquivalent (Divisor.toQDivisor D + D'))
    (hDS : MMP.Fourfold.ContainsNoStratum B.roundDown (D.supp : Set V))
    (hD'S : MMP.Fourfold.ContainsNoStratum B.roundDown (D'.supp : Set V)) (q : ℤ) :
    Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) q).map
      ((derivedGlobalSectionsOver f).map
        ((DerivedCategory.singleFunctor V.Modules 0).map
          (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hD :
            M ≤ M + D))))).hom := by
  obtain ⟨V', _, _, _, _, g, _, _, hsm', hgp, hgb, K', Δ, E, M', D₁, hK', hΔ, hΔ0, hΔ1, hstrata,
    hM', hD₁, hD₁Δ, hE, ⟨hBM, hpbM⟩, ⟨hBD, hpbD⟩, hstrict⟩ :=
    exists_resolution_data f hsm hK B hB hB0 hB1 H hH M hM D hD D' hD' ht htH hDS hD'S
  haveI : IsIntegral V := (inferInstance : IsProjectiveVariety ℂ f).toIsVariety.toIsIntegral
  haveI : QuasiCompact f := (inferInstance : IsProjectiveVariety ℂ f).toIsVariety.toQuasiCompact
  haveI : QuasiCompact (g ≫ f) :=
    (inferInstance : MMP.Mori.IsProjectiveVariety ℂ (g ≫ f)).toIsVariety.toQuasiCompact
  have hcart : ∀ N : Divisor V, N.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  have hcart' : ∀ N : Divisor V', N.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm'
  have hbij := bijective_stalkMap_genericPoint g hgb
  have h₁ := isDivisorialSection_ratPullSec g (hcart M) hE hpbM
  have h₂ := isDivisorialSection_ratPullSec g (hcart (M + D)) hE hpbD
  have hiso : IsIso (pullbackDivisorialHom g M M' h₁) := by
    refine isIso_pullbackDivisorialHom g hbij M M' h₁ fun P => ?_
    obtain ⟨F, hFP, hFiso, hEF⟩ := hstrict P
    refine ⟨F, hFP, hFiso, ?_⟩
    have := coeff_isPullback_of_isIso_stalkMap g (hcart M) hpbM P F hFP hFiso
    rwa [DivisorWithCoeffs.coeff_sub, hEF, sub_zero] at this
  have hD₁le : M' ≤ M' + D₁ := le_add_of_nonneg_right hD₁
  have hcomm := divisorialSheafInclusion_comp_pullbackDivisorialHom g
    (le_add_of_nonneg_right hD : M ≤ M + D) hD₁le h₁ h₂
  have hvan : ∀ i : ℕ, 0 < i →
      Limits.IsZero (((Scheme.Modules.pushforward g).rightDerived i).obj M'.divisorialSheaf) :=
    fun i hi => MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_of_isNef_sub_canonical_add
      f (g ≫ f) hsm' g rfl hgp hgb K' hK' Δ hΔ hΔ0 hΔ1 hstrata M' (hcart' M')
      (isNef_sub_of_qLinearlyEquivalent (g ≫ f) hM') i hi
  have hinj := MMP.Mori.injective_derivedCohomologyOverField_map_divisorialSheafInclusion
    (g ≫ f) hsm' hK' Δ hΔ hΔ0 hΔ1 M' hM' D₁ hD₁ hD₁Δ q
  exact injective_homology_map_of_comp f g _ _ _ _ hcomm hvan q hinj

end MMP.Mori

end
