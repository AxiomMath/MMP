module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistSections
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.RegularSequence
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.AdjointEpi
import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange
import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimLocal
import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Cohomology.FormalFunctionsDegreeZero
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
import MMP.AlgebraicGeometry.Positivity.SurfaceNakaiCriterion
import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass
import StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZero
import StacksFrontier.AlgebraicGeometry.FormalFunctions.CompletionStalkLimit
import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal

/-!
# Line bundles along fibrations (FA 15.4.4, 15.12, 15.13)

Three statements about invertible sheaves along a fibration, from the abundance chapter of
Kollár et al.

* Let `φ : X ⟶ T` be a contraction of normal `k`-varieties (`φ` proper, `φ_* 𝒪_X = 𝒪_T`) and
  `L` an invertible sheaf on `X` such that `φ^* φ_* L ⟶ L` is surjective and `deg_C L = 0` on
  every proper curve `C` contracted by `φ`. Then `L ≅ φ^* M` for an invertible sheaf `M` on `T`.
* Let `g : (V, Δ_V) ⟶ W` be a log elliptic fiber space over a field of characteristic zero and
  `M` a Cartier divisor with `M = n₀ (K_V + Δ_V)`, `n₀ > 0`. Then `𝒪_V(M)` restricts to the
  trivial sheaf on the generic fibre `E_g = V_η`.
* Let `f : X ⟶ S` be a surjective morphism from a projective threefold to a normal projective
  surface whose fibres are curves, with generic point `η` of `S`. For invertible sheaves `A, B`
  on `S` and `H` on `X`, `(f^*A · f^*B · H) = (A · B) · deg_{κ(η)} (H|_{X_η})`.

## Main results

* `MMP.Flips.IsContraction.exists_isInvertible_pullback_iso`: descent of a relatively free,
  numerically trivial invertible sheaf (FA 15.4.4).
* `MMP.Flips.IsLogEllipticFiberSpace.isTrivial_pullback_fiberι_divisorialSheaf`: the log
  canonical bundle is trivial on the generic fibre (FA, proof of 15.12).
* `MMP.Flips.sheafIntersectionNumber_pullback_pullback_eq_mul_invertibleCurveDegree`: the
  intersection formula for two pulled-back surface divisors (FA, proof of 15.13).
* `MMP.Flips.genericFiberDegree_add`, `MMP.Flips.genericFiberDegree_nonneg`,
  `MMP.Flips.coeff_eq_zero_of_genericFiberDegree_eq_zero` and
  `MMP.Flips.genericFiberPointDegree_pos_of_map_genericPoint_eq`: the degree on the generic
  fibre is additive and nonnegative on effective divisors, and a horizontal prime divisor has
  positive degree, so an effective divisor of degree zero has no horizontal component.
* `MMP.Flips.fiberPrimeDivisor`, `MMP.Flips.mem_range_fiberPrimeDivisor` and
  `MMP.Flips.genericFiberPointDegree_fiberPrimeDivisor`: the prime divisors of the generic fibre
  `V_η` are the horizontal prime divisors of `V`, with the same residue degrees over `k(W)`.
* `MMP.Flips.invertibleCurveDegree_divisorialSheaf_eq_sum` and
  `MMP.Flips.invertibleCurveDegree_eq_genericFiberDegree`: on a smooth proper curve
  `deg 𝒪(∑ dᵢ Pᵢ) = ∑ dᵢ [κ(Pᵢ) : κ]`, so the degree of a restricted divisor on `V_η` is its
  degree on the generic fibre.
* `MMP.Flips.isCurve_fiberToSpecResidueField`, `MMP.Flips.smooth_fiberToSpecResidueField`,
  `MMP.Flips.geometricallyConnected_fiberToSpecResidueField`: the generic fibre of a contraction
  in characteristic zero, of dimension one, is a smooth geometrically connected curve.
* `MMP.Flips.exists_divisor_fiber_canonical`, `MMP.Flips.exists_divisor_fiber_pullback` and
  `MMP.Flips.two_mul_genus_sub_two_eq_genericFiberDegree`: divisors of `V` restrict to `V_η`,
  `K_V` restricting to a canonical divisor, so that `K_V · V_η = 2g - 2`.

## Implementation notes

All three are stated for invertible sheaves rather than Cartier divisors where the source allows
it; the divisor case is `𝒪(D)`.

*Descent.* Surjectivity of `φ^* φ_* L ⟶ L` is that the counit of
`Scheme.Modules.pullbackPushforwardAdjunction φ` at `L` is an epimorphism. The source factors the
morphism `X ⟶ 𝐏_T(φ_* L)` through `φ` by rigidity. Here one shows instead that every point of
`T` has a neighbourhood `V` with `L` trivial on `φ⁻¹V`: a section of `L` not vanishing at a point
of a fibre `X_t` over a closed point vanishes nowhere on `X_t`, since on a contracted curve a
nonzero section with a zero has positive degree and `X_t` is connected. Then `M = φ_* L` is
invertible and the counit is an isomorphism.

*Generic fibre.* The generic fibre is `Scheme.Hom.fiber g η`, and restriction is pullback along
`Scheme.Hom.fiberι g η`. It is a smooth proper geometrically connected curve over `k(W)` lying in
the smooth locus of `V`; `K_V` restricts to a divisor with sheaf `Ω¹_{E_g/k(W)}`, and the degree
of a restricted divisor is computed from its horizontal components. Then
`2g - 2 + Δ_V · E_g = 0` leaves genus zero, or genus one with `Δ_V` vertical.

*Intersection formula.* The source cuts `S` by general hyperplane sections. Here both sides are
computed from Euler characteristics: the Leray expansion and the projection formula reduce the
left side to twists of the higher direct images `Rⁱf_* (𝒪_X ⊗ H^{⊗ c})` on `S`, the top
coefficient of an Euler polynomial on `S` is the generic rank times `(A · B)`, and flat base
change to `Spec κ(η)` turns the alternating sum of generic ranks into `χ(X_η, H^{⊗ c}|_{X_η})`.
Higher direct images are the `ℕ`-indexed `Functor.rightDerived`, compared with
`Functor.rightDerivedPlus` by `Stacks.DerivedIndexing.rightDerivedIso`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.4.4,
  15.12, 15.13
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

/-! ### Pulling two surface divisors back through a curve fibration -/

section PullbackSurfaceIntersection

open MMP.Mori
open scoped TensorProduct

attribute [local instance] AlgebraicGeometry.SheafOfModules.isInvertible_pullback

private theorem isCoherent_rightDerived {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [IsLocallyNoetherian S] (G : X.Modules) [G.IsCoherent] (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived i).obj G).IsCoherent := by
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} S.Modules := HasDerivedCategory.standard _
  have := isWeakSerreClass_coherentModules S
  exact ObjectProperty.prop_of_iso (P := fun P : S.Modules => P.IsCoherent)
    ((Stacks.DerivedIndexing.rightDerivedIso.{u, u, u + 1, u + 1, u + 1, u + 1}
      (Scheme.Modules.pushforward f) i).app G).symm
    (ProperCoherenceWitness.higherDirectImageIsCoherent X S f inferInstance inferInstance G
      inferInstance i)

private theorem eulerCharacteristic_twistedSheaf_pullback_eq_finsum (k : Type u) [Field k]
    {X S : Scheme.{u}} (f : X ⟶ S) (sS : S ⟶ Spec (.of k)) [IsProper sS] [IsProper (f ≫ sS)]
    {d : ℕ} (L : Fin d → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (G : X.Modules) [hG : G.IsCoherent] (n : Fin d → ℤ) :
    haveI : IsProper f := IsProper.of_comp f sS
    haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
    @eulerCharacteristic k _ X (f ≫ sS) _
        (twistedSheaf G (fun j => (Scheme.Modules.pullback f).obj (L j)) n)
        (twistedSheaf_isCoherent _ _ n) =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * @eulerCharacteristic k _ S sS _
        (twistedSheaf (((Scheme.Modules.pushforward f).rightDerived i).obj G) L n)
        (@twistedSheaf_isCoherent S d _ L _ (isCoherent_rightDerived f G i) n) := by
  have : IsProper f := IsProper.of_comp f sS
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sS)
  have : (twistedSheaf G (fun j => (Scheme.Modules.pullback f).obj (L j)) n).IsCoherent :=
    twistedSheaf_isCoherent _ _ n
  rw [eulerCharacteristic_eq_finsum_higherDirectImage k f sS]
  refine finsum_congr fun i => ?_
  congr 1
  let T := twistedSheaf G (fun j => (Scheme.Modules.pullback f).obj (L j)) n
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} S.Modules := HasDerivedCategory.standard _
  have := isCoherent_rightDerived f G i
  have : (twistedSheaf (((Scheme.Modules.pushforward f).rightDerived i).obj G) L n).IsCoherent :=
    twistedSheaf_isCoherent _ _ n
  have : (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj T).IsCoherent :=
    ProperCoherenceWitness.higherDirectImageIsCoherent X S f inferInstance inferInstance T
      inferInstance i
  refine eulerCharacteristic_eq_of_iso k sS ?_
  exact ((Stacks.DerivedIndexing.rightDerivedIso.{u, u, u + 1, u + 1, u + 1, u + 1}
      (Scheme.Modules.pushforward f) i).app T).symm ≪≫
    (@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward f) _
      (Scheme.Modules.hasDerivedCategory X) (Scheme.Modules.hasDerivedCategory S) i).app T ≪≫
    Stacks.ProjectionFormula.higherDirectImageTwistedSheafIso f L G n i ≪≫
    twistedSheafIsoOfIso L ((@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _
      (Scheme.Modules.pushforward f) _ (Scheme.Modules.hasDerivedCategory X)
      (Scheme.Modules.hasDerivedCategory S) i).app G).symm n

private theorem finrank_sections_pullback_fromSpecResidueField {S : Scheme.{u}} (x : S)
    (F : S.Modules) [F.IsQuasicoherent] {U : S.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    Module.finrank (S.residueField x)
        ((moduleSpecΓFunctor (R := S.residueField x)).obj
          ((Scheme.Modules.pullback (S.fromSpecResidueField x)).obj F)) =
      Scheme.Modules.fiberRank F x := by
  have : ((Scheme.Modules.pullback (S.fromSpecStalk x)).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F
  let e1 := (moduleSpecΓFunctor (R := S.residueField x)).mapIso
    ((Scheme.Modules.pullbackComp (Spec.map (S.residue x)) (S.fromSpecStalk x)).app F).symm
  let e2 := quasicoherentPullbackSectionsIso _ _ (S.residue x)
    ((Scheme.Modules.pullback (S.fromSpecStalk x)).obj F)
  refine (e2 ≪≫ e1.symm).toLinearEquiv.finrank_eq.symm.trans ?_
  unfold Scheme.Modules.fiberRank
  let := fromSpecStalkPullbackModule F x
  let : Module (S.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.presheaf) F.val x
  let : Algebra (S.presheaf.stalk x) (S.residueField x) := (S.residue x).hom.toAlgebra
  obtain ⟨e, -⟩ := exists_fromSpecStalkSectionsStalkLinearEquiv F x hU hx
  have e' : (S.residueField x) ⊗[S.presheaf.stalk x]
      Γ((Scheme.Modules.pullback (S.fromSpecStalk x)).obj F, ⊤) ≃ₗ[S.residueField x]
      (S.residueField x) ⊗[S.presheaf.stalk x] (F.presheaf.stalk x) :=
    LinearEquiv.baseChange _ _ _ _ e
  exact e'.finrank_eq

private theorem finrank_cohomologyOverField_eq_finrank_sections_pullback {K : Type u} [Field K]
    {X S X' : Scheme.{u}} {f : X ⟶ S} {g : Spec (.of K) ⟶ S} {g' : X' ⟶ X}
    {p : X' ⟶ Spec (.of K)} (H : IsPullback g' p f g) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] (G : X.Modules) [G.IsQuasicoherent] (n : ℕ) :
    Module.finrank K (cohomologyOverField K p ((Scheme.Modules.pullback g').obj G) n) =
      Module.finrank K ((moduleSpecΓFunctor (R := .of K)).obj
        ((Scheme.Modules.pullback g).obj
          (((Scheme.Modules.pushforward f).rightDerived n).obj G))) := by
  have : QuasiCompact p := MorphismProperty.of_isPullback H inferInstance
  have : QuasiSeparated p := MorphismProperty.of_isPullback H inferInstance
  have : ((Scheme.Modules.pullback g').obj G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g' G
  let G' := (Scheme.Modules.pullback g').obj G
  let e₀ := Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso p G' n
  let e₁ : cohomologyOverField K p G' n ≅
      (moduleSpecΓFunctor (R := .of K)).obj
        (((Scheme.Modules.pushforward p).rightDerived n).obj G') :=
    (ModuleCat.restrictScalarsComp'App _ _ _
        (by rw [show p.appLE ⊤ ⊤ (by simp) = p.appTop from p.appLE_eq_app (U := ⊤)]; rfl) _) ≪≫
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of K)).inv.hom).mapIso e₀ ≪≫
      eqToIso (Stacks.Conormal.CotangentAppIso.moduleSpecΓFunctor_obj_eq _).symm
  obtain ⟨bc⟩ := Stacks.FormalFunctions.nonempty_pullbackHigherDirectImageIso H G n
  exact (e₁ ≪≫ (moduleSpecΓFunctor (R := .of K)).mapIso bc.symm).toLinearEquiv.finrank_eq

private theorem finrank_cohomologyOverField_fiber_genericPoint {X S : Scheme.{u}} [IsIntegral S]
    [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f] (G : X.Modules) [G.IsCoherent] (n : ℕ) :
    Module.finrank (S.residueField (genericPoint S))
        (cohomologyOverField (S.residueField (genericPoint S))
          (f.fiberToSpecResidueField (genericPoint S))
          ((Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj G) n) =
      Scheme.Modules.fiberRank (((Scheme.Modules.pushforward f).rightDerived n).obj G)
        (genericPoint S) := by
  have := AlgebraicGeometry.flat_fromSpecResidueField_genericPoint S
  have := isCoherent_rightDerived f G n
  obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (x := genericPoint S)
    (U := ⊤) (TopologicalSpace.Opens.mem_top _)
  rw [← finrank_sections_pullback_fromSpecResidueField (genericPoint S) _ hU hηU]
  exact finrank_cohomologyOverField_eq_finrank_sections_pullback
    (K := S.residueField (genericPoint S)) (IsPullback.of_hasPullback _ _) G n

/-- A sum over the subsets of `Fin 3`, split along the last coordinate. -/
private theorem sum_finset_fin_three_eq (g : (Fin 3 → ℤ) → ℤ) :
    ∑ T : Finset (Fin 3), (-1 : ℤ) ^ (3 - T.card) * g (fun j => if j ∈ T then 1 else 0) =
      ∑ T : Finset (Fin 2), (-1 : ℤ) ^ (2 - T.card) *
        (g ![if (0 : Fin 2) ∈ T then 1 else 0, if (1 : Fin 2) ∈ T then 1 else 0, 1] -
          g ![if (0 : Fin 2) ∈ T then 1 else 0, if (1 : Fin 2) ∈ T then 1 else 0, 0]) := by
  have h3 : ∀ T : Finset (Fin 3), (fun j => if j ∈ T then (1 : ℤ) else 0) =
      ![if (0 : Fin 3) ∈ T then 1 else 0, if (1 : Fin 3) ∈ T then 1 else 0,
        if (2 : Fin 3) ∈ T then 1 else 0] :=
    fun T => funext fun j => by fin_cases j <;> rfl
  simp_rw [h3]
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} from by decide,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  simp +decide
  ring

private theorem coeff_one_eq_coeff_homogeneousComponent {d : ℕ} (P : MvPolynomial (Fin d) ℚ) :
    P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) =
      (MvPolynomial.homogeneousComponent d P).coeff
        (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  rw [MvPolynomial.coeff_homogeneousComponent, ite_eq_left]
  rw [Finsupp.degree_eq_sum]
  simp

private theorem sum_eulerCharacteristic_twistedSheaf_eq_fiberRank_mul (k : Type u) [Field k]
    {S : Scheme.{u}} [IsIntegral S] (sS : S ⟶ Spec (.of k)) [IsProper sS] {d : ℕ}
    (hS : topologicalKrullDim S = d) (L : Fin d → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (F : S.Modules) (hF : F.IsCoherent) :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic k _ S sS _ (twistedSheaf F L (fun j => if j ∈ T then 1 else 0))
          (@twistedSheaf_isCoherent S d F L _ hF _) =
      (Scheme.Modules.fiberRank F (genericPoint S) : ℤ) *
        ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
          @eulerCharacteristic k _ S sS _
            (twistedSheaf (SheafOfModules.unit S.ringCatSheaf) L
              (fun j => if j ∈ T then 1 else 0))
            (@twistedSheaf_isCoherent S d _ L _
              (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sS) _) := by
  have hO := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sS
  obtain ⟨P, hPdeg, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k sS L F hF
  obtain ⟨Q, hQdeg, hQ⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k sS L _ hO
  have hdeg : ∀ (G : S.Modules) (R : MvPolynomial (Fin d) ℚ),
      (R = 0 ∨ (R.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp G)) → R.totalDegree ≤ d := by
    intro G R h
    rcases h with rfl | h
    · simp
    · have := h.trans ((topologicalKrullDim_subspace_le S _).trans hS.le)
      exact_mod_cast this
  have hcomp := MMP.Mori.homogeneousComponent_eulerPolynomial_eq_fiberRank_smul k sS d hS L F hF
    P Q hP hQ
  have key : ∀ (G : S.Modules) (hG : G.IsCoherent) (R : MvPolynomial (Fin d) ℚ),
      R.totalDegree ≤ d →
      (∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) R =
        ((@eulerCharacteristic k _ S sS _ (twistedSheaf G L n)
          (@twistedSheaf_isCoherent S d G L _ hG n) : ℤ) : ℚ)) →
      ((∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic k _ S sS _ (twistedSheaf G L (fun j => if j ∈ T then 1 else 0))
          (@twistedSheaf_isCoherent S d G L _ hG _) : ℤ) : ℚ) =
        (MvPolynomial.homogeneousComponent d R).coeff
          (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
    intro G hG R hR hRv
    rw [← coeff_one_eq_coeff_homogeneousComponent,
      ← MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one R hR]
    push_cast
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 1
    have h := hRv fun j => if j ∈ T then (1 : ℤ) else 0
    rw [show (fun j : Fin d => (((if j ∈ T then (1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun j : Fin d => if j ∈ T then (1 : ℚ) else 0 from
      funext fun j => by split_ifs <;> simp] at h
    exact h.symm
  apply Int.cast_injective (α := ℚ)
  rw [key F hF P (hdeg F P hPdeg) hP, Int.cast_mul, key _ hO Q (hdeg _ Q hQdeg) hQ, hcomp,
    MvPolynomial.coeff_smul, smul_eq_mul]
  push_cast
  rfl

open Stacks.SheafOfModules.Invertible in
/-- Isomorphic families of invertible modules give isomorphic folds, at every exponent. -/
private noncomputable def twistListFamilyIso {X : Scheme.{u}} {r : ℕ} (L M : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (e : ∀ j, L j ≅ M j) (n : Fin r → ℤ) (l : List (Fin r)) :
    ∀ {F G : X.Modules}, (F ≅ G) → (twistList L n l F ≅ twistList M n l G) := by
  induction l with
  | nil => exact fun ε => ε
  | cons j t ih =>
    exact fun ε => ih (tensorProductIso X.presheaf X.ringCatSheaf.2 ε
      (MMP.Mori.Twist.tensorPowerIsoOfIso (L j) (M j) (e j) (n j)))

/-- Isomorphic families of invertible modules give isomorphic twisted sheaves. -/
private noncomputable def twistedSheafFamilyIso {X : Scheme.{u}} {r : ℕ}
    (L M : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (e : ∀ j, L j ≅ M j) (n : Fin r → ℤ) {F G : X.Modules} (ε : F ≅ G) :
    twistedSheaf F L n ≅ twistedSheaf G M n :=
  twistListFamilyIso L M e n (List.finRange r) ε

/-- The Euler characteristic does not depend on which of two equal structure morphisms is
used. -/
private theorem eulerCharacteristic_congr_structureMap (k : Type u) [Field k] {W : Scheme.{u}}
    {p q : W ⟶ Spec (.of k)} (hpq : p = q) [IsProper p] [IsProper q] (G : W.Modules)
    (hG : G.IsCoherent) :
    @eulerCharacteristic k _ W p _ G hG = @eulerCharacteristic k _ W q _ G hG := by
  subst hpq
  rfl

/-- The intersection number against the whole scheme, as the alternating sum of the Euler
characteristics of the twists of `𝒪_X` by the modules themselves. -/
private theorem sheafIntersectionNumber_id_eq_sum (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (d : ℕ) (hd : topologicalKrullDim X ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    MMP.Mori.sheafIntersectionNumber k p (𝟙 X) d hd L =
      ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic k _ X p _
          (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) L (fun j => if j ∈ T then 1 else 0))
          (@twistedSheaf_isCoherent X d _ L _
            (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p) _) := by
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_eq_sum_eulerCharacteristic]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  have hO := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p
  have : (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) L
      (fun j => if j ∈ T then 1 else 0)).IsCoherent := twistedSheaf_isCoherent _ _ _
  have := isCoherent_twistedSheafUnitPullback k p (𝟙 X) L (fun j => if j ∈ T then 1 else 0)
  refine (eulerCharacteristic_eq_of_iso k (𝟙 X ≫ p) (twistedSheafFamilyIso _ L
    (fun j => (Scheme.Modules.pullbackId X).app (L j)) _ (Iso.refl _))).trans ?_
  exact eulerCharacteristic_congr_structureMap k (Category.id_comp p) _ _

private theorem sum_mul_finsum_eq {d N : ℕ} (s χX : Finset (Fin d) → ℤ)
    (a : ℕ → Finset (Fin d) → ℤ) (rk : ℕ → ℤ) (D : ℤ)
    (h1 : ∀ T, χX T = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * a i T) (h2 : ∀ T i, N ≤ i → a i T = 0)
    (h3 : ∀ i, ∑ T, s T * a i T = rk i * D) (h4 : ∀ i, N ≤ i → rk i = 0) :
    ∑ T, s T * χX T = (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * rk i) * D := by
  have e1 : ∀ T, ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * a i T =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * a i T := fun T =>
    finsum_eq_sum_of_support_subset _ fun i hi => by
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      exact hi (by rw [h2 T i (not_lt.mp h), mul_zero])
  have e2 : ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * rk i = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * rk i :=
    finsum_eq_sum_of_support_subset _ fun i hi => by
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      exact hi (by rw [h4 i (not_lt.mp h), mul_zero])
  simp_rw [h1, e1, e2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← h3 i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring

/-- **The twists of a sheaf by pulled-back invertible modules, through the higher direct
images.** For `f : X ⟶ S` over `k` with `S` integral of dimension `d` and `G` coherent on `X`,
the alternating sum over the `d`-fold indicator twists of `G` by `f^*L_1, …, f^*L_d` is the
intersection number `(L_1 ⋯ L_d · S)` times `∑ᵢ (-1)ⁱ rk_η Rⁱf_*G`. -/
private theorem sum_eulerCharacteristic_twistedSheaf_pullback_eq (k : Type u) [Field k]
    {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) (sS : S ⟶ Spec (.of k)) [IsProper sS]
    [IsProper (f ≫ sS)] {d : ℕ} (hS : topologicalKrullDim S = d) (L : Fin d → S.Modules)
    [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (G : X.Modules) [G.IsCoherent] :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic k _ X (f ≫ sS) _
          (twistedSheaf G (fun j => (Scheme.Modules.pullback f).obj (L j))
            (fun j => if j ∈ T then 1 else 0)) (twistedSheaf_isCoherent _ _ _) =
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Scheme.Modules.fiberRank
          (((Scheme.Modules.pushforward f).rightDerived i).obj G) (genericPoint S) : ℤ)) *
        ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
          @eulerCharacteristic k _ S sS _
            (twistedSheaf (SheafOfModules.unit S.ringCatSheaf) L
              (fun j => if j ∈ T then 1 else 0))
            (@twistedSheaf_isCoherent S d _ L _
              (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sS) _) := by
  have : IsProper f := IsProper.of_comp f sS
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedNat_pushforward f
  have hz : ∀ i, N ≤ i → Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj G) :=
    fun i hi => hN G (isQuasicoherent_of_isCoherent G) i hi
  refine sum_mul_finsum_eq (N := N) _ _
    (fun i T => @eulerCharacteristic k _ S sS _
      (twistedSheaf (((Scheme.Modules.pushforward f).rightDerived i).obj G) L
        (fun j => if j ∈ T then 1 else 0))
      (@twistedSheaf_isCoherent S d _ L _ (isCoherent_rightDerived f G i) _)) _ _
    (fun T => eulerCharacteristic_twistedSheaf_pullback_eq_finsum k f sS L G _)
    (fun T i hi => eulerCharacteristic_eq_zero_of_isZero k sS _ _
      (isZero_twistedSheaf_of_isZero L (hz i hi) _))
    (fun i => sum_eulerCharacteristic_twistedSheaf_eq_fiberRank_mul k sS hS L _
      (isCoherent_rightDerived f G i))
    (fun i hi => by
      rw [Scheme.Modules.fiberRank_eq_zero_of_subsingleton_stalk _ _
        (subsingleton_moduleStalk_of_isZero (hz i hi) _)]
      simp)

/-- Peeling the last factor of a three-term twist off and moving it onto the sheaf twisted. -/
private noncomputable def twistedSheafThreeIso {X : Scheme.{u}} (F A B H : X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![A, B, H] j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![A, B] j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![H] j)]
    (n : Fin 3 → ℤ) :
    twistedSheaf F ![A, B, H] n ≅
      twistedSheaf (twistedSheaf F ![H] ![n 2]) ![A, B] ![n 0, n 1] :=
  (twistListTensorIso ![A, B] ![n 0, n 1] (List.finRange 2) F _).symm

open Stacks.SheafOfModules.Invertible in
/-- **The degree on the generic fibre from generic ranks.** For a proper `f : X ⟶ S` onto an
integral scheme with generic point `η`, the alternating sums of the generic ranks of the higher
direct images of `H` and of `𝒪_X` differ by the degree of `H|_{X_η}`. -/
private theorem finsum_fiberRank_twist_sub_eq_invertibleCurveDegree {X S : Scheme.{u}}
    [IsIntegral S] [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (H : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![H] j)]
    (hfib : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1) :
    haveI := isProper_fiberToSpecResidueField f (genericPoint S)
    haveI : ∀ c : ℤ, (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![c]).IsCoherent :=
      fun _ => twistedSheaf_isCoherent _ _ _
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Scheme.Modules.fiberRank
        (((Scheme.Modules.pushforward f).rightDerived i).obj
          (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![1])) (genericPoint S) : ℤ)) -
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Scheme.Modules.fiberRank
        (((Scheme.Modules.pushforward f).rightDerived i).obj
          (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![0])) (genericPoint S) : ℤ) =
      invertibleCurveDegree (S.residueField (genericPoint S))
        (f.fiberToSpecResidueField (genericPoint S)) hfib
        ((Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj H) := by
  have : ∀ c : ℤ, (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![c]).IsCoherent :=
    fun c => twistedSheaf_isCoherent _ _ _
  simp_rw [← finrank_cohomologyOverField_fiber_genericPoint f]
  let e1 : (Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![1]) ≅
      (Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj H :=
    (Scheme.Modules.pullback (f.fiberι (genericPoint S))).mapIso
      (MMP.Mori.Twist.twistedSheafUnitIsoTensorPower ![H] H
          (fun i => eqToIso (Matrix.cons_val_fin_one H ![] i)) ![1] ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 H (by simp) ≪≫
        tensorPowerOneIso X.presheaf X.ringCatSheaf.2 H)
  let e0 : (Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![0]) ≅
      SheafOfModules.unit (f.fiber (genericPoint S)).ringCatSheaf :=
    (Scheme.Modules.pullback (f.fiberι (genericPoint S))).mapIso
      (twistedSheafCongrIso _ _ (by funext j; fin_cases j; rfl) ≪≫ twistedSheafZeroIso _ _) ≪≫
      Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso _
  simp_rw [finrank_cohomologyOverField_eq_of_iso _ _ e1,
    finrank_cohomologyOverField_eq_of_iso _ _ e0]
  rfl

open Stacks.SheafOfModules.Invertible in
/-- **Pulling two surface divisors through a curve fibration.** Let `f : X ⟶ S` be a surjective
morphism from a projective threefold to a normal projective surface over a field `k` of
characteristic zero (the structure morphism of `X` being `f ≫ sS`), with every fibre of dimension
one. For invertible sheaves `A, B` on `S` and `H` on `X`,
`(f^*A · f^*B · H · X) = (A · B · S) · deg_{κ(η)} (H|_{X_η})`, where `η` is the generic point of
`S` and `X_η` the generic fibre. -/
@[mmp "lem_mmp_fa15_pullback_surface_intersection"]
public theorem sheafIntersectionNumber_pullback_pullback_eq_mul_invertibleCurveDegree
    {k : Type u} [Field k] [CharZero k] {X S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (f : X ⟶ S)
    [Mori.IsProjectiveVariety k (f ≫ sS)] [Mori.IsProjectiveVariety k sS] [IsNormal S]
    (hX : topologicalKrullDim X = 3) (hS : topologicalKrullDim S = 2)
    (hf : Function.Surjective f) (hfib : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (A B : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B]
    (H : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H] :
    haveI : IsProper f := IsProper.of_comp f sS
    haveI := isProper_fiberToSpecResidueField f (genericPoint S)
    @sheafIntersectionNumber k _ X X (f ≫ sS) _ (𝟙 X) _ 3 hX.le
        ![(Scheme.Modules.pullback f).obj A, (Scheme.Modules.pullback f).obj B, H]
        (by intro j; fin_cases j <;> dsimp <;> infer_instance) =
      @sheafIntersectionNumber k _ S S sS _ (𝟙 S) _ 2 hS.le ![A, B]
          (by intro j; fin_cases j <;> dsimp <;> infer_instance) *
        invertibleCurveDegree (S.residueField (genericPoint S))
          (f.fiberToSpecResidueField (genericPoint S)) (hfib (genericPoint S)).le
          ((Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj H) := by
  have : IsProper f := IsProper.of_comp f sS
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  have hAB : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![A, B] j) := by
    intro j; fin_cases j <;> dsimp <;> infer_instance
  have hfAB : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback f).obj A, (Scheme.Modules.pullback f).obj B] j) := by
    intro j; fin_cases j <;> dsimp <;> infer_instance
  have hH : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![H] j) := by
    intro j; fin_cases j; dsimp; infer_instance
  have hL3 : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback f).obj A, (Scheme.Modules.pullback f).obj B, H] j) := by
    intro j; fin_cases j <;> dsimp <;> infer_instance
  have hOX := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (f ≫ sS)
  have hG : ∀ c : ℤ, (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![c]).IsCoherent :=
    fun c => twistedSheaf_isCoherent _ _ _
  rw [sheafIntersectionNumber_id_eq_sum, sheafIntersectionNumber_id_eq_sum]
  have hg : ∀ (T : Finset (Fin 2)) (c : ℤ),
      @eulerCharacteristic k _ X (f ≫ sS) _
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
          ![(Scheme.Modules.pullback f).obj A, (Scheme.Modules.pullback f).obj B, H]
          ![if (0 : Fin 2) ∈ T then 1 else 0, if (1 : Fin 2) ∈ T then 1 else 0, c])
        (twistedSheaf_isCoherent _ _ _) =
      @eulerCharacteristic k _ X (f ≫ sS) _
        (twistedSheaf (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![c])
          (fun j => (Scheme.Modules.pullback f).obj (![A, B] j))
          (fun j => if j ∈ T then 1 else 0))
        (@twistedSheaf_isCoherent X 2 _ _ _ (hG c) _) := by
    intro T c
    have := hG c
    have : (twistedSheaf (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![c])
          (fun j => (Scheme.Modules.pullback f).obj (![A, B] j))
          (fun j => if j ∈ T then 1 else 0)).IsCoherent := twistedSheaf_isCoherent _ _ _
    have : (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
          ![(Scheme.Modules.pullback f).obj A, (Scheme.Modules.pullback f).obj B, H]
          ![if (0 : Fin 2) ∈ T then 1 else 0, if (1 : Fin 2) ∈ T then 1 else 0, c]).IsCoherent :=
      twistedSheaf_isCoherent _ _ _
    exact eulerCharacteristic_eq_of_iso k (f ≫ sS)
      (twistedSheafThreeIso _ _ _ _ _ ≪≫
        twistedSheafFamilyIso _ _ (fun j => eqToIso (by fin_cases j <;> rfl)) _ (Iso.refl _) ≪≫
        twistedSheafCongrIso _ _ (by funext j; fin_cases j <;> rfl))
  refine (sum_finset_fin_three_eq (fun n => @eulerCharacteristic k _ X (f ≫ sS) _
    (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
      ![(Scheme.Modules.pullback f).obj A, (Scheme.Modules.pullback f).obj B, H] n)
    (twistedSheaf_isCoherent _ _ _))).trans ?_
  simp_rw [hg]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have := hG 1
  have := hG 0
  rw [sum_eulerCharacteristic_twistedSheaf_pullback_eq k f sS hS ![A, B]
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![1]),
    sum_eulerCharacteristic_twistedSheaf_pullback_eq k f sS hS ![A, B]
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) ![H] ![0])]
  rw [← finsum_fiberRank_twist_sub_eq_invertibleCurveDegree f H (hfib (genericPoint S)).le]
  ring

end PullbackSurfaceIntersection

/-! ### Descent of a relatively free, numerically trivial line bundle -/

section Descent

open Topology TopologicalSpace MMP.Mori MMP.Fourfold
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The closure of a point has the dimension of its reduced closed subscheme. -/
private theorem topologicalKrullDim_closure_singleton (y : X) :
    topologicalKrullDim (closure ({y} : Set X)) = topologicalKrullDim (curveSubschemeAt y) := by
  let e := (curveSubschemeAtι y).isClosedEmbedding.isEmbedding.toHomeomorph
  let e' := e.trans (Homeomorph.setCongr (range_curveSubschemeAtι y))
  exact (IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph).symm

/-- **Curves through a point avoiding a closed set.** Let `X` be locally Noetherian and locally
of finite type over a field, `p` a closed point, `η ⤳ p` and `Z ∋ p` a closed subset not
containing `η`. There is a point `y` with `η ⤳ y ⤳ p`, `y ∉ Z` and `{y}⁻` of dimension one. -/
private theorem exists_curve_of_specializes (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] {η p : X} (hηp : η ⤳ p) (hp : IsClosed ({p} : Set X)) {Z : Set X}
    (hZ : IsClosed Z) (hpZ : p ∈ Z) (hηZ : η ∉ Z) :
    ∃ y : X, η ⤳ y ∧ y ⤳ p ∧ y ∉ Z ∧ topologicalKrullDim (closure ({y} : Set X)) = 1 := by
  classical
  set R := X.presheaf.stalk p
  set g := X.fromSpecStalk p
  obtain ⟨Q, hQ⟩ := Stacks.Chow.exists_fromSpecStalk_eq hηp
  have hT : IsClosed (g ⁻¹' Z : Set (PrimeSpectrum R)) := hZ.preimage g.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hT
  have hQT : ¬ ((I : Set R) ⊆ Q.asIdeal) := fun h => hηZ (hQ ▸ hI.ge h)
  obtain ⟨a, haI, haQ⟩ := Set.not_subset.mp hQT
  have hgM : g (IsLocalRing.closedPoint R) = p := Scheme.fromSpecStalk_closedPoint
  have hQM : Q.asIdeal < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Q.isPrime.ne_top) fun h => hηZ ?_
    rw [← hQ, show Q = IsLocalRing.closedPoint R from PrimeSpectrum.ext h,
      Scheme.fromSpecStalk_closedPoint]
    exact hpZ
  obtain ⟨q, hq, hQq, hqM, haq, himm⟩ := exists_isPrime_le_lt_notMem_of_lt hQM haQ
  set qpt : PrimeSpectrum R := ⟨q, hq⟩
  have hyZ : g qpt ∉ Z := by
    intro h
    have h' : qpt ∈ (g ⁻¹' Z : Set (PrimeSpectrum R)) := h
    rw [hI] at h'
    exact haq (h' haI)
  have hyp : g qpt ⤳ p := Stacks.Chow.specializes_fromSpecStalk p qpt
  refine ⟨g qpt, ?_, hyp, hyZ, ?_⟩
  · rw [← hQ]
    exact ((PrimeSpectrum.le_iff_specializes Q qpt).mp hQq).map g.continuous
  · rw [topologicalKrullDim_closure_singleton]
    refine topologicalKrullDim_curveSubschemeAt_eq_one sX hyp
      (fun h => hyZ (by rw [h]; exact hpZ)) hp fun z hyz hzp => ?_
    obtain ⟨r, rfl⟩ := Stacks.Chow.exists_fromSpecStalk_eq hzp
    have hle : r ≤ qpt := (Stacks.Chow.fromSpecStalk_le_iff p).mp hyz
    have hqr : q ≤ r.asIdeal := (PrimeSpectrum.le_iff_specializes qpt r).mpr hle
    rcases eq_or_lt_of_le hqr with h | h
    · left
      congr 1
      exact PrimeSpectrum.ext h.symm
    · right
      have := himm r.asIdeal r.isPrime h (IsLocalRing.le_maximalIdeal r.isPrime.ne_top)
      rw [show r = IsLocalRing.closedPoint R from PrimeSpectrum.ext this]
      exact hgM

end Curves

/-- A closed subset of a quasi-sober space contained in a Noetherian subspace is the union of the
closures of finitely many of its points. -/
private theorem exists_finite_eq_biUnion_closure {T : Type*} [TopologicalSpace T] [QuasiSober T]
    {F N : Set T} [NoetherianSpace N] (hF : IsClosed F) (hFN : F ⊆ N) :
    ∃ E : Set T, E.Finite ∧ E ⊆ F ∧ F = ⋃ η ∈ E, closure ({η} : Set T) := by
  classical
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨∅, Set.finite_empty, Set.empty_subset _, by simp [Set.eq_empty_of_isEmpty F]⟩
  obtain ⟨S, hSf, -, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (hF.preimage continuous_subtype_val : IsClosed ((↑) ⁻¹' F : Set N))
  have hgen : ∀ t ∈ S, ∃ η : T, closure {η} = closure ((↑) '' t : Set T) := fun t ht =>
    QuasiSober.sober ((hSi t ht).image _ continuous_subtype_val.continuousOn).closure
      isClosed_closure
  choose! η hη using hgen
  have hsub : ∀ t ∈ S, closure ((↑) '' t : Set T) ⊆ F := fun t ht =>
    closure_minimal (by
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ ((↑) ⁻¹' F : Set N) := hS ▸ Set.mem_sUnion_of_mem hx ht
      exact this) hF
  refine ⟨η '' S, hSf.image _, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hsub t ht ((hη t ht) ▸ subset_closure rfl)
  · refine subset_antisymm (fun x hx => ?_) (Set.iUnion₂_subset ?_)
    · have hx' : (⟨x, hFN hx⟩ : N) ∈ ((↑) ⁻¹' F : Set N) := hx
      rw [hS] at hx'
      obtain ⟨t, ht, hxt⟩ := hx'
      exact Set.mem_biUnion (Set.mem_image_of_mem _ ht)
        ((hη t ht).symm ▸ subset_closure ⟨_, hxt, rfl⟩)
    · rintro _ ⟨t, ht, rfl⟩
      exact (hη t ht).symm ▸ hsub t ht

/-- The fibre of a quasi-compact morphism with locally Noetherian source over a closed point is
the union of the closures of finitely many of its points. -/
private theorem exists_finite_preimage_singleton_eq_biUnion_closure {W X : Scheme.{u}}
    (p : W ⟶ X) [QuasiCompact p] [IsLocallyNoetherian W] {v : X} (hv : IsClosed ({v} : Set X)) :
    ∃ E : Set W, E.Finite ∧ p ⁻¹' {v} = ⋃ η ∈ E, closure ({η} : Set W) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  have : CompactSpace (p ⁻¹ᵁ V : W.Opens) := isCompact_iff_compactSpace.mp <|
    QuasiCompact.isCompact_preimage (f := p) _ V.isOpen hV.isCompact
  have : IsNoetherian (p ⁻¹ᵁ V : W.Opens).toScheme := ⟨⟩
  have : NoetherianSpace ((p ⁻¹ᵁ V : W.Opens) : Set W) :=
    inferInstanceAs (NoetherianSpace (p ⁻¹ᵁ V : W.Opens).toScheme)
  obtain ⟨E, hE, -, hF⟩ := exists_finite_eq_biUnion_closure (N := ((p ⁻¹ᵁ V : W.Opens) : Set W))
    (hv.preimage p.continuous) fun x (hx : p x = v) => show p x ∈ V from hx ▸ hvV
  exact ⟨E, hE, hF⟩

/-- Let `g : S ⟶ X` be proper and `X` locally of finite type over `k`. The reduced closed
subscheme on the closure of a point `a` of `S` which `g` maps to a closed point `x` is proper over
`k`: it maps to the reduced point `{x}`, which is finite over `k`. -/
private lemma isProper_curveSubschemeAtι_comp {k : Type u} [Field k] {S X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (g : S ⟶ X) [IsProper g] {x : X}
    (hx : IsClosed ({x} : Set X)) {a : S} (ha : closure ({a} : Set S) ⊆ g ⁻¹' {x}) :
    IsProper (curveSubschemeAtι a ≫ g ≫ sX) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({a} : Set S))
  set J := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have H : J ≤ I.map g := by
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    intro y hy
    have hsub : g '' closure ({a} : Set S) ⊆ {x} := Set.image_subset_iff.mpr ha
    exact (closure_minimal hsub hx) hy
  have hφ := Scheme.IdealSheafData.subschemeMap_subschemeι I J g H
  have : IsProper (Scheme.IdealSheafData.subschemeMap I J g H ≫ J.subschemeι) := by
    rw [hφ]; exact inferInstanceAs (IsProper (I.subschemeι ≫ g))
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

/-- The degree of an invertible module on a proper curve depends only on the structure morphism
up to equality and on the module up to isomorphism. -/
private theorem invertibleCurveDegree_congr' (k : Type u) [Field k] {C : Scheme.{u}}
    {f f' : C ⟶ Spec (.of k)} [IsProper f] [IsProper f'] (h : f = f')
    (hdim : topologicalKrullDim C ≤ 1) {L L' : C.Modules}
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L'] (e : L ≅ L') :
    invertibleCurveDegree k f hdim L = invertibleCurveDegree k f' hdim L' := by
  subst h
  exact invertibleCurveDegree_eq_of_iso k f hdim e

/-- An invertible module with a nowhere vanishing global section is trivial. -/
private theorem nonempty_iso_unit_of_nonvanishingLocus_eq_univ {Y : Scheme.{u}} (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] (s : Γ(M, ⊤))
    (hs : Stacks.Ample.nonvanishingLocus M s = Set.univ) :
    Nonempty (M ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  have hiso := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ M
    ((Stacks.NonvanishingSpelling.sectionsEquiv Y M).symm s)
    ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq Y M s).trans hs)
  exact ⟨(asIso (M.unitHomEquiv.symm
    ((Stacks.NonvanishingSpelling.sectionsEquiv Y M).symm s))).symm⟩

variable {k : Type u} [Field k] {X T : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} {φ : X ⟶ T}

/-- **A section that does not vanish at the generic point of a contracted curve vanishes nowhere
on it.** Otherwise its pullback to the curve is a nonzero section with a zero, and the degree
of `L` on the curve is positive. -/
private theorem closure_subset_nonvanishingLocusOn (hφ : MMP.Flips.IsContraction k sT sX φ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : ∀ C : MMP.Mori.ProperCurve sX, C.IsContractedBy φ → C.degree k L = 0)
    {V : T.Opens} (s : Γ(L, φ ⁻¹ᵁ V)) {t : T} (ht : IsClosed ({t} : Set T))
    {c : X} (hc : topologicalKrullDim (closure ({c} : Set X)) = 1)
    (hct : closure ({c} : Set X) ⊆ φ ⁻¹' {t}) (hcs : c ∈ nonvanishingLocusOn L (φ ⁻¹ᵁ V) s) :
    closure ({c} : Set X) ⊆ nonvanishingLocusOn L (φ ⁻¹ᵁ V) s := by
  by_contra hns
  obtain ⟨z, hzc, hzN⟩ := Set.not_subset.mp hns
  have : IsProper φ := hφ.isProper
  have : AlgebraicGeometry.IsVariety k sT := hφ.isVariety_target
  have hprop : IsProper (curveSubschemeAtι c ≫ sX) := by
    rw [← hφ.comp_eq]
    exact isProper_curveSubschemeAtι_comp sT φ ht hct
  let C : ProperCurve sX := ⟨c, (topologicalKrullDim_closure_singleton c) ▸ hc, hprop⟩
  have hC0 : C.degree k L = 0 :=
    hdeg C fun x hx => (hct hx).trans (hct (subset_closure rfl)).symm
  have htV : t ∈ V := by
    rw [← (hct (subset_closure rfl) : φ c = t)]
    exact Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_subset L _ s hcs
  have hrange : Set.range C.ι ⊆ Set.range (φ ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι, range_curveSubschemeAtι]
    intro x hx
    change φ x ∈ V
    rw [(hct hx : φ x = t)]
    exact htV
  let i := IsOpenImmersion.lift (φ ⁻¹ᵁ V).ι C.ι hrange
  have hi : i ≫ (φ ⁻¹ᵁ V).ι = C.ι := IsOpenImmersion.lift_fac _ _ _
  have hiapp : ∀ x, (φ ⁻¹ᵁ V).ι (i x) = C.ι x := fun x => by rw [← Scheme.Hom.comp_apply, hi]
  have : IsProper (i ≫ (φ ⁻¹ᵁ V).ι ≫ sX) := by rw [← Category.assoc, hi]; infer_instance
  have : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have := MMP.Mori.isInvertible_pullback_obj (φ ⁻¹ᵁ V).ι L
  let σ := Stacks.NonvanishingLocusRestrict.restrictSection (φ ⁻¹ᵁ V) L s
  have hσ := Stacks.NonvanishingLocusRestrict.nonvanishingLocus_restrictSection (φ ⁻¹ᵁ V) L s
  obtain ⟨c', hc'⟩ : c ∈ Set.range C.ι := by
    rw [range_curveSubschemeAtι]
    exact subset_closure rfl
  obtain ⟨z', hz'⟩ : z ∈ Set.range C.ι := by
    rwa [range_curveSubschemeAtι]
  have h1 : i c' ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.AmpleLocallyClosed.pullbackModule (φ ⁻¹ᵁ V).ι L) σ := by
    rwa [hσ, Set.mem_preimage, hiapp, hc']
  have h2 : i z' ∉ Stacks.Ample.nonvanishingLocus
      (Stacks.AmpleLocallyClosed.pullbackModule (φ ⁻¹ᵁ V).ι L) σ := by
    rwa [hσ, Set.mem_preimage, hiapp, hz']
  have hpos := MMP.Threefold.Mori.invertibleCurveDegree_pullback_pos ((φ ⁻¹ᵁ V).ι ≫ sX) i
    C.dim_le ((Scheme.Modules.pullback (φ ⁻¹ᵁ V).ι).obj L) σ ⟨c', h1⟩ ⟨z', h2⟩
  have e : (Scheme.Modules.pullback C.ι).obj L ≅
      (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback (φ ⁻¹ᵁ V).ι).obj L) :=
    (Scheme.Modules.pullbackCongr hi.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp i (φ ⁻¹ᵁ V).ι).app L).symm
  have hdeq : C.degree k L = invertibleCurveDegree k (i ≫ (φ ⁻¹ᵁ V).ι ≫ sX) C.dim_le
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback (φ ⁻¹ᵁ V).ι).obj L)) :=
    invertibleCurveDegree_congr' k (by rw [← Category.assoc, hi]) C.dim_le e
  omega

/-- **An open set meeting a preconnected union of finitely many point closures contains it, as
soon as it contains each of those closures whose generic point it contains.** The closures
with generic point in `N` lie in `N`, the others miss `N`, and the two unions are closed. -/
private theorem biUnion_closure_subset_of_isPreconnected {Y : Type*} [TopologicalSpace Y]
    {E N : Set Y} (hE : E.Finite) (hF : IsPreconnected (⋃ η ∈ E, closure ({η} : Set Y)))
    (hN : IsOpen N) (hin : ∀ η ∈ E, η ∈ N → closure ({η} : Set Y) ⊆ N)
    {x₀ : Y} (hx₀ : x₀ ∈ ⋃ η ∈ E, closure ({η} : Set Y)) (hx₀N : x₀ ∈ N) :
    ⋃ η ∈ E, closure ({η} : Set Y) ⊆ N := by
  set A := ⋃ η ∈ {η ∈ E | η ∈ N}, closure ({η} : Set Y)
  set B := ⋃ η ∈ {η ∈ E | η ∉ N}, closure ({η} : Set Y)
  have hAN : A ⊆ N := Set.iUnion₂_subset fun η hη => hin η hη.1 hη.2
  have hBN : ∀ x ∈ B, x ∉ N := fun x hx hxN => by
    obtain ⟨η, ⟨-, hηN⟩, hxη⟩ := Set.mem_iUnion₂.mp hx
    exact hηN ((specializes_iff_mem_closure.mpr hxη).mem_open hN hxN)
  have hcover : ⋃ η ∈ E, closure ({η} : Set Y) ⊆ A ∪ B := by
    refine Set.iUnion₂_subset fun η hη x hx => ?_
    by_cases hηN : η ∈ N
    · exact Or.inl (Set.mem_biUnion ⟨hη, hηN⟩ hx)
    · exact Or.inr (Set.mem_biUnion ⟨hη, hηN⟩ hx)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hF A B
    ((hE.subset fun _ h => h.1).isClosed_biUnion fun _ _ => isClosed_closure)
    ((hE.subset fun _ h => h.1).isClosed_biUnion fun _ _ => isClosed_closure) hcover
    (Set.eq_empty_of_forall_notMem fun x ⟨_, hxA, hxB⟩ => hBN x hxB (hAN hxA)) with h | h
  · exact h.trans hAN
  · exact absurd hx₀N (hBN x₀ (h hx₀))

/-- **A section not vanishing at one point of a fibre over a closed point vanishes nowhere on
that fibre.** The fibre is connected and the union of finitely many point closures, and on each
of them the section vanishes nowhere as soon as it does not vanish at the generic point: else it
vanishes at a closed point, and on a contracted curve through that point and not at its generic
point, against `closure_subset_nonvanishingLocusOn`. -/
private theorem preimage_subset_nonvanishingLocusOn (hφ : MMP.Flips.IsContraction k sT sX φ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : ∀ C : MMP.Mori.ProperCurve sX, C.IsContractedBy φ → C.degree k L = 0)
    {V : T.Opens} (s : Γ(L, φ ⁻¹ᵁ V)) {t : T} (ht : IsClosed ({t} : Set T))
    {x₀ : X} (hx₀ : φ x₀ = t) (hs : x₀ ∈ nonvanishingLocusOn L (φ ⁻¹ᵁ V) s) :
    φ ⁻¹' {t} ⊆ nonvanishingLocusOn L (φ ⁻¹ᵁ V) s := by
  have : IsProper φ := hφ.isProper
  have : AlgebraicGeometry.IsVariety k sX := hφ.isVariety_source
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set N := nonvanishingLocusOn L (φ ⁻¹ᵁ V) s
  have hN : IsOpen N := Stacks.SectionPowerOpen.isOpen_nonvanishingLocusOn L _ s
  obtain ⟨E, hE, hFE⟩ := exists_finite_preimage_singleton_eq_biUnion_closure φ ht
  have hconn := (φ.isConnected_preimage_singleton_of_isIso_app hφ.isIso_app t).isPreconnected
  have hx₀F : x₀ ∈ φ ⁻¹' {t} := hx₀
  rw [hFE] at hconn hx₀F ⊢
  refine biUnion_closure_subset_of_isPreconnected hE hconn hN (fun η hηE hηN => ?_) hx₀F hs
  by_contra hns
  obtain ⟨y, hyη, hyN⟩ := Set.not_subset.mp hns
  obtain ⟨p, ⟨hpη, hpN⟩, hpc⟩ := nonempty_inter_closedPoints
    (Z := closure ({η} : Set X) ∩ Nᶜ) ⟨y, hyη, hyN⟩
    (isClosed_closure.inter hN.isClosed_compl).isLocallyClosed
  rw [mem_closedPoints_iff] at hpc
  obtain ⟨c, hηc, hcp, hcN, hc⟩ := exists_curve_of_specializes sX
    (specializes_iff_mem_closure.mpr hpη) hpc hN.isClosed_compl hpN (not_not.mpr hηN)
  have hcη : closure ({c} : Set X) ⊆ φ ⁻¹' {t} :=
    hFE ▸ (hηc.closure_subset).trans (Set.subset_biUnion_of_mem
      (u := fun η => closure ({η} : Set X)) hηE)
  exact hpN (closure_subset_nonvanishingLocusOn hφ L hdeg s ht hc hcη (not_not.mp hcN)
    (specializes_iff_mem_closure.mp hcp))

/-- **`L` is trivial over a neighbourhood of every closed point of `T`.** -/
private theorem exists_pullback_iso_unit_of_isClosed (hφ : MMP.Flips.IsContraction k sT sX φ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hfree : Epi ((Scheme.Modules.pullbackPushforwardAdjunction φ).counit.app L))
    (hdeg : ∀ C : MMP.Mori.ProperCurve sX, C.IsContractedBy φ → C.degree k L = 0)
    {t : T} (ht : IsClosed ({t} : Set T)) :
    ∃ V : T.Opens, t ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (φ ⁻¹ᵁ V).ι).obj L ≅
        SheafOfModules.unit (φ ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  have : IsProper φ := hφ.isProper
  obtain ⟨x₀, hx₀⟩ := (φ.isConnected_preimage_singleton_of_isIso_app hφ.isIso_app t).nonempty
  have hepi : Epi (((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ L).symm
      (𝟙 ((Scheme.Modules.pushforward φ).obj L))) := by
    rwa [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  obtain ⟨V, -, s₀, hs⟩ := Stacks.Tag01VMVeryAmple.exists_mem_nonvanishingLocusOn_of_epi_adjoint φ
    (𝟙 ((Scheme.Modules.pushforward φ).obj L)) x₀
  set s : Γ(L, φ ⁻¹ᵁ V) := (𝟙 ((Scheme.Modules.pushforward φ).obj L) :).app V s₀
  set N := nonvanishingLocusOn L (φ ⁻¹ᵁ V) s with hNdef
  have hF : φ ⁻¹' {t} ⊆ N := preimage_subset_nonvanishingLocusOn hφ L hdeg s ht hx₀ hs
  have hN : IsOpen N := Stacks.SectionPowerOpen.isOpen_nonvanishingLocusOn L _ s
  have hZ : IsClosed (φ '' Nᶜ) := φ.isClosedMap _ hN.isClosed_compl
  have htV : t ∈ V := by
    rw [← (hx₀ : φ x₀ = t)]
    exact Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_subset L _ s hs
  let V' : T.Opens := V ⊓ ⟨(φ '' Nᶜ)ᶜ, hZ.isOpen_compl⟩
  have htV' : t ∈ V' := ⟨htV, fun ⟨x, hx, hxt⟩ => hx (hF hxt)⟩
  have hle : φ ⁻¹ᵁ V' ≤ φ ⁻¹ᵁ V := fun x hx => hx.1
  let s' : Γ(L, φ ⁻¹ᵁ V') := L.presheaf.map (homOfLE hle).op s
  have hN' : nonvanishingLocusOn L (φ ⁻¹ᵁ V') s' = φ ⁻¹ᵁ V' := by
    rw [Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res]
    refine Set.inter_eq_left.mpr fun x hx => ?_
    by_contra hxN
    exact hx.2 ⟨x, hxN, rfl⟩
  let σ := Stacks.NonvanishingLocusRestrict.restrictSection (φ ⁻¹ᵁ V') L s'
  have hσ : Stacks.Ample.nonvanishingLocus
      (Stacks.AmpleLocallyClosed.pullbackModule (φ ⁻¹ᵁ V').ι L) σ = Set.univ := by
    rw [Stacks.NonvanishingLocusRestrict.nonvanishingLocus_restrictSection, hN']
    exact Set.eq_univ_of_forall fun x => x.2
  have := MMP.Mori.isInvertible_pullback_obj (φ ⁻¹ᵁ V').ι L
  exact ⟨V', htV', nonempty_iso_unit_of_nonvanishingLocus_eq_univ _ σ hσ⟩

/-- **`L` is trivial over a neighbourhood of every point of `T`.** -/
private theorem exists_pullback_iso_unit (hφ : MMP.Flips.IsContraction k sT sX φ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hfree : Epi ((Scheme.Modules.pullbackPushforwardAdjunction φ).counit.app L))
    (hdeg : ∀ C : MMP.Mori.ProperCurve sX, C.IsContractedBy φ → C.degree k L = 0) (t : T) :
    ∃ V : T.Opens, t ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (φ ⁻¹ᵁ V).ι).obj L ≅
        SheafOfModules.unit (φ ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  have : AlgebraicGeometry.IsVariety k sT := hφ.isVariety_target
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  obtain ⟨t₀, ht₀, hc⟩ :=
    (isClosed_closure (s := ({t} : Set T))).exists_closed_singleton ⟨t, subset_closure rfl⟩
  obtain ⟨V, hV, e⟩ := exists_pullback_iso_unit_of_isClosed hφ L hfree hdeg hc
  exact ⟨V, (specializes_iff_mem_closure.mpr ht₀).mem_open V.isOpen hV, e⟩

/-- The direct image of a module trivial over the preimages of an open cover is invertible. -/
private theorem isInvertible_pushforward (hφ : MMP.Flips.IsContraction k sT sX φ)
    (L : X.Modules)
    (h : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (φ ⁻¹ᵁ V).ι).obj L ≅
        SheafOfModules.unit (φ ⁻¹ᵁ V).toScheme.ringCatSheaf)) :
    SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2
      ((Scheme.Modules.pushforward φ).obj L) := by
  rw [isInvertible_iff_exists_restrict_iso_unit]
  intro t
  obtain ⟨V, hV, ⟨e⟩⟩ := h t
  refine ⟨V, hV, ⟨?_⟩⟩
  let ψ := φ ∣_ V
  have hψ : ∀ W, IsIso (ψ.app W) := fun W => by
    rw [morphismRestrict_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hφ.isIso_app _)
      (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage φ V W)).op).isIso_hom
  let O : V.toScheme.Modules := SheafOfModules.unit V.toScheme.ringCatSheaf
  let OX : (φ ⁻¹ᵁ V).toScheme.Modules := SheafOfModules.unit (φ ⁻¹ᵁ V).toScheme.ringCatSheaf
  let q : O ⟶ (Scheme.Modules.pushforward ψ).obj OX :=
    SheafOfModules.unitToPushforwardObjUnit ψ.toRingCatSheafHom
  have hq : IsIso q := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (ConcreteCategory.isIso_iff_bijective (ψ.app W)).mp (hψ W)
  exact (Stacks.LocalCohomology.schemePushforwardRestrictIso φ V).symm.app L ≪≫
    (Scheme.Modules.pushforward ψ).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback _).app L ≪≫ e) ≪≫ (asIso q).symm

/-- The counit is an isomorphism at a module trivial over the preimages of an open cover. -/
private theorem isIso_counit (hφ : MMP.Flips.IsContraction k sT sX φ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (φ ⁻¹ᵁ V).ι).obj L ≅
        SheafOfModules.unit (φ ⁻¹ᵁ V).toScheme.ringCatSheaf)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction φ).counit.app L) := by
  have hO : IsIso φ.toLRSHom.toHom.c := by
    have : ∀ U : (TopologicalSpace.Opens T)ᵒᵖ, IsIso (φ.c.app U) := fun U => hφ.isIso_app U.unop
    exact NatIso.isIso_of_isIso_app _
  have : IsProper φ := hφ.isProper
  have := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk _ fun x => ?_
  obtain ⟨V, hV, ⟨e⟩⟩ := h (φ x)
  set g := T.fromSpecStalk (φ x)
  have hrange : Set.range (Limits.pullback.fst φ g) ⊆ Set.range (φ ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change φ (Limits.pullback.fst φ g z) ∈ V
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
    have : g (Limits.pullback.snd φ g z) ∈ Set.range g := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open V.isOpen hV
  let j := IsOpenImmersion.lift (φ ⁻¹ᵁ V).ι (Limits.pullback.fst φ g) hrange
  have hj : j ≫ (φ ⁻¹ᵁ V).ι = Limits.pullback.fst φ g := IsOpenImmersion.lift_fac _ _ _
  have : (TopologicalSpace.Opens.map j.base).Final := Stacks.Topology.final_opensMap _
  have : (SheafOfModules.pushforward j.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
  let q : (Scheme.Modules.pullback j).obj (SheafOfModules.unit _) ⟶ SheafOfModules.unit _ :=
    SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom
  have : IsIso q := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  let e₁ : (Scheme.Modules.pullback (Limits.pullback.fst φ g)).obj L ≅
      SheafOfModules.unit _ :=
    (Scheme.Modules.pullbackCongr hj.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp j (φ ⁻¹ᵁ V).ι).app L).symm ≪≫
      (Scheme.Modules.pullback j).mapIso e ≪≫ asIso q
  let e' : (Scheme.Modules.pullback (Limits.pullback.fst φ g)).obj L ≅
      SheafOfModules.free PUnit :=
    e₁ ≪≫ (Limits.coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit _)).symm
  have hfin : ((Scheme.Modules.pullback (Limits.pullback.fst φ g)).obj L).IsFiniteType :=
    Stacks.SheafOfModules.Site.isFiniteType_of_iso
      (R := (Limits.pullback φ g).ringCatSheaf) e₁.symm inferInstance
  exact VectorBundleCodimensionOne.isIso_stalk_counit_of_iso_free φ hO L (φ x) PUnit e' hfin x
    (specializes_refl _)

/-- **A relatively free, numerically trivial line bundle descends** (FA 15.4.4). Let
`φ : X ⟶ T` be a proper morphism of normal `k`-varieties with `φ_* 𝒪_X = 𝒪_T`, and `L` an
invertible sheaf on `X` such that `φ^* φ_* L ⟶ L` is surjective and `deg_C L = 0` for every
proper curve `C ⊆ X` with `φ(C)` a point. Then `L ≅ φ^* M` for an invertible sheaf `M` on
`T`. -/
@[mmp "lem_fa15_free_numerically_trivial_descends"]
public theorem IsContraction.exists_isInvertible_pullback_iso {k : Type u} [Field k]
    {X T : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} {φ : X ⟶ T}
    (hφ : IsContraction k sT sX φ) [IsNormal X] [IsNormal T]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hfree : Epi ((Scheme.Modules.pullbackPushforwardAdjunction φ).counit.app L))
    (hdeg : ∀ C : Mori.ProperCurve sX, C.IsContractedBy φ → C.degree k L = 0) :
    ∃ (M : T.Modules) (_ : SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 M),
      Nonempty ((Scheme.Modules.pullback φ).obj M ≅ L) := by
  have h := exists_pullback_iso_unit hφ L hfree hdeg
  have := isIso_counit hφ L h
  exact ⟨(Scheme.Modules.pushforward φ).obj L, isInvertible_pushforward hφ L h,
    ⟨asIso ((Scheme.Modules.pullbackPushforwardAdjunction φ).counit.app L)⟩⟩

end Descent

/-! ### The log canonical bundle on the generic fibre of a log elliptic fiber space -/

section GenericFiberTorsion

open MMP.Mori MonoidalCategory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A morphism `g : V ⟶ W` to an integral scheme such that every `g.app U` is an isomorphism
(for instance `𝒪_W ≅ g_* 𝒪_V`) is dominant. -/
theorem isDominant_of_forall_isIso_app {V W : Scheme.{u}} (g : V ⟶ W) [IsIntegral W]
    (hg : ∀ U : W.Opens, IsIso (g.app U)) : IsDominant g := by
  constructor
  by_contra hd
  obtain ⟨U, hU, hne, hdisj⟩ : ∃ U : Set W, IsOpen U ∧ U.Nonempty ∧ Disjoint U (Set.range g) := by
    rw [DenseRange, dense_iff_closure_eq] at hd
    exact ⟨(closure (Set.range g))ᶜ, isClosed_closure.isOpen_compl,
      Set.nonempty_compl.mpr hd, disjoint_compl_left.mono_right subset_closure⟩
  let U' : W.Opens := ⟨U, hU⟩
  have hbot : g ⁻¹ᵁ U' = ⊥ := by
    ext x
    exact iff_of_false (fun hx => Set.disjoint_left.mp hdisj hx ⟨x, rfl⟩) id
  have : Nonempty U' := hne.to_subtype
  have e := (asIso (g.app U')).commRingCatIsoToRingEquiv
  have hs : Subsingleton Γ(V, g ⁻¹ᵁ U') := by
    rw [hbot]
    infer_instance
  exact not_subsingleton Γ(W, U') e.injective.subsingleton

/-- The generic fibre of a morphism from a normal scheme to an integral scheme is normal: its
local rings are local rings of the source. -/
theorem isNormal_genericFiber {V W : Scheme.{u}} (g : V ⟶ W) [IsNormal V] [IsIntegral W] :
    IsNormal (g.fiber (genericPoint W)) where
  stalk_isDomain p := by
    have := isIso_stalkMap_fiberι_genericPoint' g p
    exact Function.Injective.isDomain _
      (asIso ((g.fiberι _).stalkMap p)).commRingCatIsoToRingEquiv.symm.injective
  stalk_normal p := by
    have := isIso_stalkMap_fiberι_genericPoint' g p
    have := IsNormal.stalk_normal (X := V) ((g.fiberι _) p)
    exact IsIntegrallyClosed.of_equiv
      (asIso ((g.fiberι _).stalkMap p)).commRingCatIsoToRingEquiv

/-! ### Differentials along a morphism with bijective stalk maps -/

open Stacks.RelativeDifferentialStalkMap in
/-- For `f : X ⟶ Y` over `S` whose stalk maps are all isomorphisms (for instance the inclusion
of a generic fibre), the canonical map `f^* Ω_{Y/S} ⟶ Ω_{X/S}` is an isomorphism: on stalks it is
`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} Ω_{𝒪_{Y,f x}/𝒪_S} ⟶ Ω_{𝒪_{X,x}/𝒪_S}`, which is bijective when
`𝒪_{Y,f x} ⟶ 𝒪_{X,x}` is. -/
private theorem isIso_relativeDifferentialsMap_of_isIso_stalkMap {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (q : X ⟶ S) (hq : f ≫ g = q ≫ 𝟙 S)
    (hf : ∀ x, IsIso (f.stalkMap x)) :
    IsIso (Scheme.Hom.relativeDifferentialsMap f g q (𝟙 S) hq) := by
  obtain rfl : q = f ≫ g := by simpa using hq.symm
  classical
  set φ := Scheme.Hom.relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm
  have key : ∀ x : X, Function.Bijective (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom
      X.sheaf.presheaf x φ.val) := by
    intro x
    let R : Type u := ToType (S.presheaf.stalk (g.base (f.base x)))
    let A : Type u := ToType (Y.sheaf.presheaf.stalk (f.base x))
    let B : Type u := ToType (X.sheaf.presheaf.stalk x)
    let : Algebra R A := Scheme.Hom.algebraStalkMap g (f.base x)
    let : Algebra A B := (f.stalkMap x).hom.toAlgebra
    let : Algebra R B := Scheme.Hom.algebraStalkMap (f ≫ g) x
    have : IsScalarTower R A B := Scheme.Hom.isScalarTower_stalkMap f g x
    have hbij : Function.Bijective (algebraMap A B) :=
      (ConcreteCategory.isIso_iff_bijective (f.stalkMap x)).mp (hf x)
    have : Algebra.FormallySmooth A B :=
      .of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hbij)
    obtain ⟨e, -, hbridge⟩ := Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv f g x
    have hinj := KaehlerDifferential.mapBaseChange_injective R A B
    have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
      rw [← LinearMap.range_eq_top, eq_top_iff, ← KaehlerDifferential.span_range_derivation,
        Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hbij.2 b
      exact ⟨1 ⊗ₜ KaehlerDifferential.D R A a, by
        rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]⟩
    let eK := relativeDifferentialsStalkKaehlerEquiv (f ≫ g) x
    refine ⟨fun z₁ z₂ hz => e.injective (hinj ?_), fun w => ?_⟩
    · rw [hbridge, hbridge]
      exact congrArg eK hz
    · obtain ⟨t, ht⟩ := hsurj (eK w)
      refine ⟨e.symm t, eK.injective ?_⟩
      rw [← hbridge, e.apply_symm_apply, ht]
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := by
    have : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom) := fun x =>
      (ConcreteCategory.isIso_iff_bijective _).mpr (key x)
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (SheafOfModules.toSheaf X.ringCatSheaf) this
    (PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
      (R := X.ringCatSheaf))

/-! ### Regular points over a perfect field are smooth -/

open MMP.Mori in
/-- A point of a scheme locally of finite type over a perfect field `k` whose local ring is
regular lies in the smooth locus: the local ring is formally smooth over `k`. -/
private theorem mem_smoothLocus_of_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] : x ∈ smoothLocus sX := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hfs : letI := stalkAlgebra sX x; Algebra.FormallySmooth k (X.presheaf.stalk x) := by
    let := stalkAlgebra sX x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hU' : IsAffineOpen U := hU
    let x' : U := ⟨x, hxU⟩
    let := sectionAlgebra sX U
    have := finiteType_sectionAlgebra sX hU'
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x'
    have := isScalarTower_section_stalk sX U x'
    have := hU'.isLocalization_stalk x'
    set q := (hU'.primeIdealOf x').asIdeal
    have := Algebra.isSeparableExtension_of_perfectField k q.ResidueField
    have hs : Algebra.IsSmoothAt k q :=
      (Algebra.isSmoothAt_iff_isRegularLocalRing q (X.presheaf.stalk x)).mpr inferInstance
    exact Algebra.FormallySmooth.of_equiv
      ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (X.presheaf.stalk x)).restrictScalars k)
  rw [smoothLocus_eq_smoothLocus, Scheme.Hom.mem_smoothLocus]
  let f : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (sX x) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)
  have hiso : IsIso f := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨RingHom.injective _, fieldBaseStalkAlgebraMap_surjective (Subsingleton.elim _ _)⟩
  have hcomp : f ≫ sX.stalkMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) := by
    have hg := Scheme.Hom.germ_stalkMap sX ⊤ x (TopologicalSpace.Opens.mem_top _)
    erw [Category.assoc, hg]
    rfl
  rwa [← RingHom.FormallySmooth.respectsIso.cancel_left_isIso f, ← CommRingCat.hom_comp, hcomp]

open MMP.Mori in
/-- The smooth locus of a morphism locally of finite presentation is smooth. -/
private theorem smooth_smoothLocus_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth ((smoothLocus f).ι ≫ f) := by
  rw [smoothLocus_eq_smoothLocus, ← Scheme.Hom.smoothLocus_eq_top_iff,
    ← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Opens.ι_preimage_self]

/-! ### The canonical sheaf of a generic fibre -/

section Canonical

private theorem nonempty_iso_unit_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    [Nonempty X] (L : X.Modules) (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1) :
    Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.ModuleDescent.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L).mpr hL
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isInvertible_iff_exists_restrict_iso_unit X L).mp hinv x
  have hU : U = ⊤ := eq_top_iff.mpr fun y _ => (Subsingleton.elim y x) ▸ hxU
  subst hU
  have : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hj : inv (⊤ : X.Opens).ι ≫ (⊤ : X.Opens).ι = 𝟙 X := IsIso.inv_hom_id _
  refine ⟨(Scheme.Modules.pullbackId X).symm.app L ≪≫
    (Scheme.Modules.pullbackCongr hj).symm.app L ≪≫
    (Scheme.Modules.pullbackComp (inv (⊤ : X.Opens).ι) (⊤ : X.Opens).ι).symm.app L ≪≫
    (Scheme.Modules.pullback (inv (⊤ : X.Opens).ι)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).symm.app L ≪≫ e) ≪≫ ?_⟩
  exact @asIso _ _ _ _ _ (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u}
    (inv (⊤ : X.Opens).ι).toRingCatSheafHom)

open Stacks.SheafOfModules in
private theorem nonempty_pullback_relativeDifferentialForms_iso
    {k κ : Type u} [Field k] [Field κ] {E U : Scheme.{u}} [Nonempty E]
    (p : E ⟶ Spec (.of κ)) [Smooth p] [SmoothOfRelativeDimension 1 p]
    (c : Spec (.of κ) ⟶ Spec (.of k))
    (hc : ∃ d, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials c) d)
    (sU : U ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n sU]
    (ι : E ⟶ U) (hι : ∀ x, IsIso (ι.stalkMap x)) (hcomm : ι ≫ sU = p ≫ c) :
    Nonempty ((Scheme.Modules.pullback ι).obj (Scheme.Hom.relativeDifferentialForms sU n) ≅
      Scheme.Hom.relativeDifferentials p) := by
  obtain ⟨x₀⟩ := ‹Nonempty E›
  have hc' : ι ≫ sU = (p ≫ c) ≫ 𝟙 _ := by rw [hcomm, Category.comp_id]
  have h1 : IsIso (Scheme.Hom.relativeDifferentialsMap ι sU (p ≫ c) (𝟙 _) hc') :=
    isIso_relativeDifferentialsMap_of_isIso_stalkMap ι sU (p ≫ c) hc' hι
  have h2 := Scheme.Hom.isIso_relativeDifferentialFormsMap ι sU (p ≫ c) (𝟙 _) hc' h1 n
  let e1 := asIso (Scheme.Hom.relativeDifferentialFormsMap ι sU (p ≫ c) (𝟙 _) hc' n)
  obtain ⟨hz, hS⟩ := Scheme.Hom.toRelativeDifferentials_shortExact p c
    (Stacks.Smooth.formallySmoothScheme_of_smooth p)
  have h3 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials p) 1 :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials p 1
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials sU) n :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials sU n
  have h2r : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (p ≫ c)) n :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (@asIso _ _ _ _ _ h1)
      (Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_obj ι _ n)
  obtain ⟨d, hd⟩ := hc
  have h1r : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback p).obj (Scheme.Hom.relativeDifferentials c)) d :=
    Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_obj p _ d
  have hn : n = d + 1 := SheafOfModules.rank_add_of_shortExact _ hS d n 1 x₀
  subst hn
  have hdet := @Stacks.SheafOfModules.TopWedge.isIso_detComparison _ E.sheaf
    ((Scheme.Modules.pullback p).obj (Scheme.Hom.relativeDifferentials c))
    (Scheme.Hom.relativeDifferentials (p ≫ c)) (Scheme.Hom.relativeDifferentials p)
    (_root_.SheafOfModules.algebras _
      ((Scheme.Modules.pullback p).obj (Scheme.Hom.relativeDifferentials c)))
    (_root_.SheafOfModules.algebras _ (Scheme.Hom.relativeDifferentials (p ≫ c)))
    (_root_.SheafOfModules.algebras _ (Scheme.Hom.relativeDifferentials p)) _ _ hz hS.exact
    hS.mono_f hS.epi_g d 0 h1r h3
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials c).exteriorPower d) 1 := by
    simpa only [Nat.choose_self] using
      Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower _ d d
  obtain ⟨eN⟩ := nonempty_iso_unit_of_subsingleton _ this
  let eT : ((Scheme.Modules.pullback p).obj (Scheme.Hom.relativeDifferentials c)).exteriorPower d
      ≅ SheafOfModules.unit E.ringCatSheaf :=
    (Scheme.Modules.exteriorPowerPullbackIso p _ d).symm ≪≫
      (Scheme.Modules.pullback p).mapIso eN ≪≫
      @asIso _ _ _ _ _ (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u}
        p.toRingCatSheafHom)
  exact ⟨e1 ≪≫ eqToIso (by push_cast; rfl) ≪≫ (@asIso _ _ _ _ _ hdet).symm ≪≫
    whiskerRightIso eT _ ≪≫ λ_ _ ≪≫ eqToIso (by norm_num; rfl) ≪≫
    (_root_.SheafOfModules.algebras _
      (Scheme.Hom.relativeDifferentials p)).exteriorPowerOneIso⟩

end Canonical

/-! ### The degree of a divisor on a smooth proper curve -/

section CurveDegree

private theorem isIso_ι_of_eq_top {X : Scheme.{u}} {U : X.Opens} (hU : U = ⊤) : IsIso U.ι := by
  subst hU
  rw [← Scheme.topIso_hom]
  infer_instance

private theorem isClosed_singleton_genericPoint_of_isCurve' {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k g]
    (Z : MMP.Mori.PrimeDivisor X) :
    IsClosed ({Z.genericPoint} : Set X) := by
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsCurve k g).toIsVariety.toIsIntegral
  refine Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)) fun h => ?_
  have h1 := Z.coheight_genericPoint
  rw [h, show genericPoint X = (⊤ : X) from rfl, Order.coheight_top] at h1
  exact zero_ne_one h1

open MMP.Mori DivisorWithCoeffs in
/-- **Local equations of a prime divisor with an invertible ideal sheaf.** Near every point, the
ideal of `P` on an affine open `W` is generated by `f`, and the unit `φ` of `K(Y)` which is `f` on
the components meeting `W` and `1` elsewhere is a local equation of `P` on `W`. (Reproved from
`MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme`, whose local equation is not exported.) -/
private theorem exists_localEquation_of_isEffectiveCartierDivisor' {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf) (x : Y) :
    ∃ (W : Y.affineOpens) (_ : x ∈ (W : Y.Opens)) (f : Γ(Y, (W : Y.Opens)))
      (φ : (RationalFunctions Y)ˣ),
      P.idealSheaf.ideal W = Ideal.span {f} ∧
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) W φ ∧
      ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (W : Y.Opens)),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f := by
  classical
  have := P.integral
  have hsame : ∀ E : MMP.Mori.PrimeDivisor Y, E.genericPoint ∈ P.support → P = E := by
    intro E hE
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
    have hle : E.genericPoint ≤ P.genericPoint := specializes_iff_mem_closure.mpr hE
    by_contra hne
    have hlt : E.genericPoint < P.genericPoint := lt_of_le_not_ge hle fun h =>
      hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Specializes.antisymm (show E.genericPoint ⤳ P.genericPoint from h)
          (show P.genericPoint ⤳ E.genericPoint from hle)).eq.symm)
    have h2 := Order.coheight_add_one_le hlt
    rw [MMP.Mori.PrimeDivisor.coheight_genericPoint,
      MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
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
    rw [dite_eq_left hZ]
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
    rw [hφall E.component hZW]
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
      obtain ⟨y', hy'⟩ : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
        rwa [Scheme.IdealSheafData.range_subschemeι]
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
    [IsLocallyNoetherian Y] [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y)
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
        ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))) with hc
  have inj : ∀ x y : Γ(Y, V),
      (∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
        (Y.presheaf.germ V _ Z.2).hom x = (Y.presheaf.germ V _ Z.2).hom y) → x = y :=
    fun x y h => toRationalFunctionsPresheaf_app_injective V (funext h)
  have E1 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      (Y.presheaf.germ V _ Z.2).hom c * (dualBasisSection _ b).1 Z = 1 := fun Z =>
    congrArg (fun m : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) => m.1 Z)
      (smul_dualBasisSection b
        ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map (homOfLE le_top).op
          ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))))
  have hgsec : (Divisor.IsDivisorialSection (Finsupp.single P 1 : Divisor Y) V
      (fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1)) := by
    intro E hE
    have h0 : E.OrdGE (E.ord φ⁻¹) (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y)
        E.component) := Or.inr (E.valuation_component φ⁻¹).ge
    refine h0.mono (le_of_eq ?_)
    rw [PrimeDivisor.ord_inv, ← hloc E hE]
  let g : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) :=
    ⟨fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1, hgsec⟩
  have E2 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 =
        (Y.presheaf.germ V _ Z.2).hom (evalAt _ (dualBasisCoord _ b) g) *
          (dualBasisSection _ b).1 Z := fun Z =>
    (congrArg (fun m : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) => m.1 Z)
      (smul_dualBasisSection b g)).symm
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
/-- **The degree of a closed point of a normal proper curve**: for a prime divisor `P` of a normal
proper curve `C` over a field `k`, `deg 𝒪_C(P) = [κ(P) : k]`. -/
theorem invertibleCurveDegree_divisorialSheaf_single_eq_finrank {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sY]
    [IsProper sY] [IsLocallyNoetherian Y] [IsNormal Y] (C : MMP.Mori.PrimeDivisor Y)
    (hD : MMP.Mori.Divisor.IsCartier (Finsupp.single C 1 : MMP.Mori.Divisor Y))
    (hdim : topologicalKrullDim Y ≤ 1)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y))] :
    letI : Algebra k (Y.residueField C.genericPoint) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation C.genericPoint).hom.toAlgebra
    invertibleCurveDegree k sY hdim
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) =
      Module.finrank k (Y.residueField C.genericPoint) := by
  classical
  have : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsCurve k sY).toIsVariety.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hD0 : 0 ≤ (Finsupp.single C 1 : MMP.Mori.Divisor Y) :=
    Finsupp.single_nonneg.2 zero_le_one
  have hx : IsClosed ({C.genericPoint} : Set Y) :=
    isClosed_singleton_genericPoint_of_isCurve' sY C
  have hsupp : C.idealSheaf.support = TopologicalSpace.Closeds.closure ({C.genericPoint} : Set Y) :=
    SetLike.coe_injective (C.support_eq_closure)
  have : IsReduced C.idealSheaf.subscheme := by
    have := C.integral
    infer_instance
  have hcl : (⟨{C.genericPoint}, hx⟩ : TopologicalSpace.Closeds Y) =
      TopologicalSpace.Closeds.closure ({C.genericPoint} : Set Y) :=
    TopologicalSpace.Closeds.ext hx.closure_eq.symm
  have hPI : C.idealSheaf = Scheme.IdealSheafData.vanishingIdeal
      (⟨{C.genericPoint}, hx⟩ : TopologicalSpace.Closeds Y) := by
    rw [hcl]
    exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp
  have : IsDiscreteValuationRing (Y.presheaf.stalk C.genericPoint) :=
    C.isDiscreteValuationRing_localRing
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf := by
    rw [hPI]; exact isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hx
  have hinv := hD.isInvertibleModule_divisorialSheaf
  have hinv' : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) := hinv
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
  rw [invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one k sY hdim _
    (MMP.Mori.Divisor.divisorialSheafOneSection hD0) hs _ (hZ.trans hPI)]
  exact_mod_cast finrank_globalSections_vanishingIdeal_singleton sY hx

open MMP.Mori DivisorWithCoeffs in
/-- On a smooth proper curve `C` over a field `k`, the degree of `𝒪_C(D)` is
`∑ dᵢ [κ(Pᵢ) : k]` for `D = ∑ dᵢ Pᵢ`. -/
theorem invertibleCurveDegree_divisorialSheaf_eq_sum {k : Type u} [Field k]
    {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sC] [Smooth sC]
    [IsProper sC] [IsLocallyNoetherian C] [IsNormal C] (D : Divisor C)
    (hdim : topologicalKrullDim C ≤ 1)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 D.divisorialSheaf] :
    invertibleCurveDegree k sC hdim D.divisorialSheaf = D.sum fun P a => a *
      letI : Algebra k (C.residueField P.genericPoint) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop ≫ C.Γevaluation P.genericPoint).hom.toAlgebra
      (Module.finrank k (C.residueField P.genericPoint) : ℤ) := by
  classical
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have hsm : IsSmoothScheme sC := (isSmoothScheme_iff sC).mpr inferInstance
  have : QuasiCompact sC := inferInstance
  have := isIso_ι_of_eq_top hsm
  have hdim' : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1 := by
    rwa [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (smoothLocus sC).ι)).isHomeomorph]
  have : IsProper ((smoothLocus sC).ι ≫ sC) := inferInstance
  let F : Divisor C →+ ℤ :=
    { toFun := fun E => E.degreeOn k sC (smoothLocus sC).ι hdim'
        (MMP.Fourfold.isCartier_of_isSmoothScheme hsm E)
      map_zero' := Divisor.degreeOn_zero' k sC (smoothLocus sC).ι hdim'
      map_add' := fun E E' => Divisor.degreeOn_add k sC (smoothLocus sC).ι hdim' E E' _ _ }
  have hF : ∀ (E : Divisor C)
      [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 E.divisorialSheaf],
      F E = invertibleCurveDegree k sC hdim E.divisorialSheaf := by
    intro E _
    change invertibleCurveDegree k ((smoothLocus sC).ι ≫ sC) hdim'
      ((Scheme.Modules.pullback (smoothLocus sC).ι).obj E.divisorialSheaf) = _
    exact invertibleCurveDegree_pullback_of_isIso (smoothLocus sC).ι sC hdim' hdim _
  rw [← hF]
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun P _ => ?_
  have hc := MMP.Fourfold.isCartier_of_isSmoothScheme hsm (Finsupp.single P 1 : Divisor C)
  have := hc.isInvertibleModule_divisorialSheaf
  rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul, hF,
    invertibleCurveDegree_divisorialSheaf_single_eq_finrank sC P hc hdim]

end CurveDegree

/-! ### Coefficients of a pulled-back divisor -/

section Coeff

open Opposite MMP.Positivity

variable {Y' Y : Scheme.{u}} [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

private theorem ordUnit_eq_ord (E : MMP.Mori.PrimeDivisor Y')
    (u : (Y'.presheaf.stalk (componentGenericPoint Y' E.component))ˣ) :
    E.ordUnit u = Y'.ord ((componentToFunctionField E.component).hom u)
      E.genericPoint := by
  have hsub : Subsingleton (irreducibleComponents Y') := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let ψ : (RationalFunctions Y')ˣ := (RationalFunctions.unitsEquiv Y').symm
    fun Z => (Subsingleton.elim E.component Z) ▸ u
  have h1 : Units.map (RationalFunctions.component Y' E.component).toMonoidHom ψ = u :=
    congrFun ((RationalFunctions.unitsEquiv Y').apply_symm_apply
      (fun Z => (Subsingleton.elim E.component Z) ▸ u)) E.component
  rw [← h1, ← PrimeDivisor.ord_eq_ordUnit, ord_eq_ord_componentToFunctionField]
  rfl

omit [IsLocallyNoetherian Y'] [IsNormal Y'] [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem componentToFunctionField_stalkMap_apply (g : Y' ⟶ Y) [IsDominant g]
    (Z : irreducibleComponents Y') (W : irreducibleComponents Y)
    (hW : g (componentGenericPoint Y' Z) ∈ W.1)
    (a : Y.presheaf.stalk (g (componentGenericPoint Y' Z))) :
    (componentToFunctionField Z).hom ((g.stalkMap (componentGenericPoint Y' Z)).hom a) =
      functionFieldMap g ((componentToFunctionField W).hom
        ((stalkToRationalFunctions Y hW).hom a)) := by
  unfold functionFieldMap
  rw [CommRingCat.hom_comp, RingHom.comp_apply,
    show (componentToFunctionField Z) = Y'.presheaf.stalkSpecializes _ from rfl,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  congr 1
  simp only [TopCat.Presheaf.stalkCongr_hom, stalkToRationalFunctions]
  change _ = (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom
    ((Y.presheaf.stalkSpecializes _).hom a))
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]
  erw [TopCat.Presheaf.stalkSpecializes_comp_apply]

private theorem coeff_eq_of_isPullback {g : Y' ⟶ Y} [IsDominant g] {B : Divisor Y}
    (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', g (componentGenericPoint Y' Z) ∉ B.supp}
    {B' : Divisor Y'} (h : B.IsPullback g hB B') (E : MMP.Mori.PrimeDivisor Y')
    (P : MMP.Mori.PrimeDivisor Y) (heq : g E.genericPoint = P.genericPoint)
    [IsIso (g.stalkMap E.genericPoint)] : B'.coeff E = B.coeff P := by
  obtain ⟨U, hyU, φ, hφ⟩ := hBc P.genericPoint
  have hPU : (P.support ∩ (U : Set Y)).Nonempty :=
    ⟨P.genericPoint, PrimeDivisor.genericPoint_mem_support' P, hyU⟩
  have hE : (E.support ∩ ((g ⁻¹ᵁ U : Y'.Opens) : Set Y')).Nonempty :=
    ⟨E.genericPoint, PrimeDivisor.genericPoint_mem_support' E, by
      change g E.genericPoint ∈ U
      rw [heq]; exact hyU⟩
  rw [h U φ hφ E hE, hφ P hPU]
  have hZ := E.map_componentGenericPoint_mem g hE
  have hW := mem_pointComponent (g (componentGenericPoint Y' E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZ (hB _) hW
  rw [pullbackComponent_eq hB hφ hZ hW a ha, ordUnit_eq_ord,
    ord_eq_ord_componentToFunctionField]
  have hsub : Subsingleton (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hPW : P.component = pointComponent (g (componentGenericPoint Y' E.component)) :=
    Subsingleton.elim _ _
  rw [hPW, ← ha]
  change Scheme.ord ((componentToFunctionField E.component).hom
    ((g.stalkMap (componentGenericPoint Y' E.component)).hom ↑a)) E.genericPoint = _
  rw [componentToFunctionField_stalkMap_apply g E.component _ hW]
  exact ord_functionFieldMap_of_isIso g E P heq _

end Coeff

/-! ### The divisorial sheaf on an open subscheme -/

section OpenRestriction

open Opposite TopologicalSpace MMP.Fourfold

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

omit [IsLocallyNoetherian X] [IsNormal X] in
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

/-! ### Restricting divisorial sections to an open subscheme -/

section DivisorialRestrict

private theorem componentIndex_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' := by
  have : Subsingleton (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  exact Subtype.ext (Subsingleton.elim _ _)

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
  (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z.1))).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := componentIndex_eq Z Z'
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

omit [IsLocallyNoetherian X] [IsNormal X] [IsDominant U.ι] in
private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

omit [IsLocallyNoetherian X] [IsNormal X] [IsDominant U.ι] in
private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := genericPoint_specializes x
  exact hsp.mem_open V.isOpen hx

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
  ⟨topComponent U.toScheme, by rw [componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

omit [IsLocallyNoetherian X] [IsNormal X] in
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
    rw [ordGE_iff_evFF, ordGE_iff_evFF,
      evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
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
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨x, hx, hxe⟩ => by
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx⟩
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · exact fun h E' hE' => (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _, Scheme.Hom.germ_stalkMap_apply,
    ← CommRingCat.comp_apply (U.ι.appIso V).inv, Scheme.Hom.appIso_inv_app,
    TopCat.Presheaf.germ_res_apply]

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
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

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

end OpenRestriction

/-- On a smooth proper geometrically connected scheme `X` over a field `κ`, the constants
`κ ⟶ Γ(X, 𝒪_X)` are all the global functions. -/
theorem isIso_ΓSpecIso_inv_comp_appTop_of_smooth {κ : Type u} [Field κ] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of κ)) [Smooth p] [IsProper p] [GeometricallyConnected p] :
    IsIso ((Scheme.ΓSpecIso (.of κ)).inv ≫ p.appTop) := by
  have h := (isIso_globalSections_tfae_geometricallyConnected_irreducible_integral κ p
    (isGeometricallyNormal_of_smooth (k := κ) p)).out 1 2
  exact h.mpr inferInstance

/-! ### The generic fibre of a contraction -/

section ContractionFiber

variable {k : Type u} [Field k] {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sW : W ⟶ Spec (.of k)} {g : V ⟶ W} [IsIntegral W] (hg : IsContraction k sW sV g)

include hg

/-- The generic fibre of a contraction is a curve over `k(W)` as soon as it has dimension one. -/
theorem isCurve_fiberToSpecResidueField
    (hdim : topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1) :
    AlgebraicGeometry.IsCurve (W.residueField (genericPoint W))
      (g.fiberToSpecResidueField (genericPoint W)) := by
  have := hg.isVariety_source.toIsIntegral
  have := hg.isProper
  have : IsDominant g := isDominant_of_forall_isIso_app g hg.isIso_app
  have := AlgebraicGeometry.isProper_fiberToSpecResidueField g (genericPoint W)
  rw [AlgebraicGeometry.isCurve_iff]
  refine ⟨{ }, ?_⟩
  rw [(g.fiberHomeo (genericPoint W)).isHomeomorph.topologicalKrullDim_eq]
  exact hdim

/-- In characteristic zero, the generic fibre of a contraction of a normal variety is smooth over
`k(W)` as soon as it has dimension one (generic smoothness): it is a normal curve over a perfect
field. -/
theorem smooth_fiberToSpecResidueField [CharZero k] [IsNormal V]
    (hdim : topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1) :
    Smooth (g.fiberToSpecResidueField (genericPoint W)) := by
  have := isCurve_fiberToSpecResidueField hg hdim
  have := isNormal_genericFiber g
  let φ : CommRingCat.of k ⟶ W.residueField (genericPoint W) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ sW.appTop ≫ W.presheaf.germ ⊤ (genericPoint W) trivial ≫
      W.residue (genericPoint W)
  have : CharZero (W.residueField (genericPoint W)) :=
    (RingHom.charZero_iff φ.hom.injective).mp inferInstance
  have : PerfectField (W.residueField (genericPoint W)) := PerfectField.ofCharZero
  have : IsLocallyNoetherian (g.fiber (genericPoint W)) :=
    LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField (genericPoint W))
  exact smooth_of_isRegular_of_perfectField (W.residueField (genericPoint W)) _
    (isRegular_of_isNormal_of_topologicalKrullDim_le_one _
      (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := W.residueField (genericPoint W))
        (f := g.fiberToSpecResidueField (genericPoint W))).le)

/-- The generic fibre of a contraction is geometrically connected over `k(W)`, as
`g_* 𝒪_V = 𝒪_W`. -/
theorem geometricallyConnected_fiberToSpecResidueField :
    GeometricallyConnected (g.fiberToSpecResidueField (genericPoint W)) := by
  have := hg.isProper
  have := isIso_residue_genericPoint W
  have : IsIso g.c := by
    have := hg.isIso_app
    exact NatIso.isIso_of_isIso_app _
  exact Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_isIso_residue
    g _ this

/-- On a contraction of a normal variety in characteristic zero whose generic fibre `C` has
dimension one, the constants `k(W) ⟶ Γ(C, 𝒪_C)` are all the global functions of `C`. -/
theorem isIso_appTop_fiberToSpecResidueField [CharZero k] [IsNormal V]
    (hdim : topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1) :
    IsIso ((Scheme.ΓSpecIso (.of (W.residueField (genericPoint W)))).inv ≫
      (g.fiberToSpecResidueField (genericPoint W)).appTop) := by
  have := hg.isProper
  have := AlgebraicGeometry.isProper_fiberToSpecResidueField g (genericPoint W)
  have := smooth_fiberToSpecResidueField hg hdim
  have := geometricallyConnected_fiberToSpecResidueField hg
  exact isIso_ΓSpecIso_inv_comp_appTop_of_smooth (κ := W.residueField (genericPoint W)) _

/-- The restriction of `𝒪_V(M)` to the generic fibre of a contraction is invertible, `M` being
Cartier. -/
theorem isInvertible_pullback_fiberι_divisorialSheaf [IsLocallyNoetherian V] [IsNormal V]
    {M : Divisor V} (hMc : M.IsCartier) :
    SheafOfModules.IsInvertible (g.fiber (genericPoint W)).presheaf
      (g.fiber (genericPoint W)).ringCatSheaf.property
      ((Scheme.Modules.pullback (g.fiberι (genericPoint W))).obj M.divisorialSheaf) := by
  have := hg.isVariety_source.toQuasiCompact
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.property M.divisorialSheaf :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
      (MMP.Mori.Divisor.IsCartier.isInvertible_divisorialSheaf hMc)
  infer_instance

end ContractionFiber

/-! ### The generic fibre -/

section GenericFiber

variable {k : Type u} [Field k] {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sW : W ⟶ Spec (.of k)} {g : V ⟶ W} [IsIntegral W]

/-- The prime divisor of `V` whose generic point is the image of the generic point of a prime
divisor of the generic fibre `V_η`: the inclusion `V_η ⟶ V` preserves codimension. -/
noncomputable def fiberPrimeDivisor (g : V ⟶ W)
    (Q : MMP.Mori.PrimeDivisor (g.fiber (genericPoint W))) : MMP.Mori.PrimeDivisor V :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (g.fiberι _ Q.genericPoint)
    ((coheight_fiberι_genericPoint g _).trans Q.coheight_genericPoint)

/-- The generic point of `fiberPrimeDivisor g Q` is the image under `V_η ⟶ V` of the generic point
of `Q`. -/
theorem genericPoint_fiberPrimeDivisor
    (Q : MMP.Mori.PrimeDivisor (g.fiber (genericPoint W))) :
    (fiberPrimeDivisor g Q).genericPoint = g.fiberι _ Q.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- The generic point of `fiberPrimeDivisor g Q` is the image under `V_η ⟶ V` of the generic point
of `Q`, stated with `AlgebraicGeometry.PrimeDivisor.genericPoint`. -/
theorem genericPoint_fiberPrimeDivisor'
    (Q : MMP.Mori.PrimeDivisor (g.fiber (genericPoint W))) :
    AlgebraicGeometry.PrimeDivisor.genericPoint (fiberPrimeDivisor g Q) =
      g.fiberι _ (AlgebraicGeometry.PrimeDivisor.genericPoint Q) :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- Distinct prime divisors of the generic fibre give distinct prime divisors of `V`. -/
theorem fiberPrimeDivisor_injective : Function.Injective (fiberPrimeDivisor g) := by
  intro Q Q' hQ
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have := congrArg MMP.Mori.PrimeDivisor.genericPoint hQ
  rw [genericPoint_fiberPrimeDivisor, genericPoint_fiberPrimeDivisor] at this
  exact (g.fiberι _).isEmbedding.injective this

/-- The horizontal prime divisors, those whose generic point lies over `η`, are exactly those
coming from the generic fibre. -/
theorem mem_range_fiberPrimeDivisor {P : MMP.Mori.PrimeDivisor V}
    (hP : g P.genericPoint = genericPoint W) : P ∈ Set.range (fiberPrimeDivisor g) := by
  obtain ⟨q, hq⟩ : P.genericPoint ∈ Set.range (g.fiberι (genericPoint W)) := by
    rwa [Scheme.Hom.range_fiberι]
  have hc : Order.coheight q = 1 := by
    rw [← coheight_fiberι_genericPoint g q, hq]
    exact P.coheight_genericPoint
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne q hc, ?_⟩
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rwa [genericPoint_fiberPrimeDivisor', AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]

/-- The generic point of `fiberPrimeDivisor g Q` lies over the generic point of `W`. -/
theorem map_genericPoint_fiberPrimeDivisor
    (Q : MMP.Mori.PrimeDivisor (g.fiber (genericPoint W))) :
    g (fiberPrimeDivisor g Q).genericPoint = genericPoint W := by
  rw [genericPoint_fiberPrimeDivisor, ← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac,
    Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- A morphism to an affine scheme, precomposed with `Spec κ(x) ⟶ X`, is the spectrum of
evaluation of global sections at `x`. -/
private theorem fromSpecResidueField_comp' {X : Scheme.{u}} (x : X) {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) :
    X.fromSpecResidueField x ≫ f =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x) := by
  rw [← cancel_mono (Spec R).isoSpec.hom]
  change _ ≫ (Spec _).toSpecΓ = _ ≫ (Spec _).toSpecΓ
  conv_lhs => rw [Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Scheme.fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ_assoc, ← AlgebraicGeometry.Spec.map_comp]
  rw [← SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_comp, Spec.map_inj,
    Iso.hom_inv_id_assoc]
  rfl

/-- The residue field extension `κ(ξ)/κ(η)` at a point `ξ` of `V` over the generic point `η` of
`W` is the residue field extension of the generic fibre over `k(W)` at the corresponding point. -/
theorem finrank_residueField_fiber {x : V} {q : g.fiber (genericPoint W)}
    (hx : x = g.fiberι _ q) (hgx : g x = genericPoint W) :
    (letI := (g.residueFieldMap x).hom.toAlgebra;
      Module.finrank (W.residueField (g x)) (V.residueField x)) =
      letI : Algebra (W.residueField (genericPoint W))
          ((g.fiber (genericPoint W)).residueField q) :=
        ((Scheme.ΓSpecIso (.of (W.residueField (genericPoint W)))).inv ≫
          (g.fiberToSpecResidueField (genericPoint W)).appTop ≫
          (g.fiber (genericPoint W)).Γevaluation q).hom.toAlgebra
      Module.finrank (W.residueField (genericPoint W))
        ((g.fiber (genericPoint W)).residueField q) := by
  subst hx
  have := AlgebraicGeometry.isIso_residueFieldMap_of_isPreimmersion (g.fiberι (genericPoint W)) q
  let : Algebra (W.residueField (genericPoint W)) ((g.fiber (genericPoint W)).residueField q) :=
    ((Scheme.ΓSpecIso (.of (W.residueField (genericPoint W)))).inv ≫
      (g.fiberToSpecResidueField (genericPoint W)).appTop ≫
      (g.fiber (genericPoint W)).Γevaluation q).hom.toAlgebra
  let := (g.residueFieldMap (g.fiberι _ q)).hom.toAlgebra
  have key : (W.residueFieldCongr hgx).hom ≫ ((Scheme.ΓSpecIso
      (.of (W.residueField (genericPoint W)))).inv ≫
      (g.fiberToSpecResidueField (genericPoint W)).appTop ≫
      (g.fiber (genericPoint W)).Γevaluation q) =
      g.residueFieldMap (g.fiberι _ q) ≫ (g.fiberι _).residueFieldMap q := by
    apply Spec.map_injective
    rw [← cancel_mono (W.fromSpecResidueField (g (g.fiberι _ q)))]
    rw [Spec.map_comp (W.residueFieldCongr hgx).hom]
    erw [← fromSpecResidueField_comp' q (g.fiberToSpecResidueField (genericPoint W))]
    rw [Spec.map_comp (g.residueFieldMap _)]
    simp only [Category.assoc]
    rw [Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Scheme.Hom.fiber_fac]
  refine Algebra.finrank_eq_of_equiv_equiv (W.residueFieldCongr hgx).commRingCatIsoToRingEquiv
    (asIso ((g.fiberι _).residueFieldMap q)).commRingCatIsoToRingEquiv ?_
  ext z
  exact congrArg (fun φ => φ.hom z) key

/-- The residue degree of a closed point of the generic fibre over `k(W)` is the degree
`[κ(ξ) : k(W)]` of the corresponding horizontal prime divisor. -/
theorem genericFiberPointDegree_fiberPrimeDivisor
    (Q : MMP.Mori.PrimeDivisor (g.fiber (genericPoint W))) :
    letI : Algebra (W.residueField (genericPoint W))
        ((g.fiber (genericPoint W)).residueField Q.genericPoint) :=
      ((Scheme.ΓSpecIso (.of (W.residueField (genericPoint W)))).inv ≫
        (g.fiberToSpecResidueField (genericPoint W)).appTop ≫
        (g.fiber (genericPoint W)).Γevaluation Q.genericPoint).hom.toAlgebra
    genericFiberPointDegree g (fiberPrimeDivisor g Q) =
      Module.finrank (W.residueField (genericPoint W))
        ((g.fiber (genericPoint W)).residueField Q.genericPoint) := by
  rw [genericFiberPointDegree, ite_eq_left (map_genericPoint_fiberPrimeDivisor Q)]
  exact finrank_residueField_fiber (genericPoint_fiberPrimeDivisor Q)
    (map_genericPoint_fiberPrimeDivisor Q)

end GenericFiber

/-! ### The degree on the generic fibre -/

section Degree

variable {V W : Scheme.{u}} {g : V ⟶ W}

section Irreducible

variable [IrreducibleSpace W]

/-- The degree on the generic fibre as a `Finsupp.sum` over the coefficients. -/
theorem genericFiberDegree_eq_sum (D : QDivisor V) :
    genericFiberDegree g D = D.sum fun P c => c * genericFiberPointDegree g P := rfl

/-- The degree on the generic fibre is additive. -/
@[simp]
theorem genericFiberDegree_add (D D' : QDivisor V) :
    genericFiberDegree g (D + D') = genericFiberDegree g D + genericFiberDegree g D' := by
  simp only [genericFiberDegree_eq_sum]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- The degree on the generic fibre is `ℤ`-linear. -/
@[simp]
theorem genericFiberDegree_zsmul (m : ℤ) (D : QDivisor V) :
    genericFiberDegree g (m • D) = m * genericFiberDegree g D := by
  simp only [genericFiberDegree_eq_sum]
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [zsmul_eq_mul, mul_assoc]

/-- A divisor with nonnegative coefficients has nonnegative degree on the generic fibre. -/
theorem genericFiberDegree_nonneg {D : QDivisor V} (hD : ∀ P, 0 ≤ D.coeff P) :
    0 ≤ genericFiberDegree g D :=
  Finset.sum_nonneg fun P _ => mul_nonneg (hD P) (Nat.cast_nonneg _)

/-- A divisor of nonnegative coefficients and degree zero on the generic fibre has no horizontal
components. -/
theorem coeff_eq_zero_of_genericFiberDegree_eq_zero {D : QDivisor V}
    (hD : ∀ P, 0 ≤ D.coeff P) (h0 : genericFiberDegree g D = 0) {P : MMP.Mori.PrimeDivisor V}
    (hP : 0 < genericFiberPointDegree g P) : D.coeff P = 0 := by
  classical
  by_contra hne
  have hmem : P ∈ D.support := Finsupp.mem_support_iff.mpr hne
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun Q _ =>
    mul_nonneg (hD Q) (Nat.cast_nonneg (genericFiberPointDegree g Q))).mp h0 P hmem
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hne h2
  · exact hP.ne' (by exact_mod_cast h2)

end Irreducible

variable [IsIntegral W]

section Positive

variable [AlgebraicGeometry.IsCurve (W.residueField (genericPoint W))
    (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))]

/-- A closed point of the generic fibre has positive residue degree over `k(W)`. -/
private theorem genericFiberPointDegree_fiberPrimeDivisor_pos
    (Q : MMP.Mori.PrimeDivisor (g.fiber (genericPoint W))) :
    0 < genericFiberPointDegree g (fiberPrimeDivisor g Q) := by
  rw [genericFiberPointDegree_fiberPrimeDivisor Q]
  let : Algebra (W.residueField (genericPoint W))
      ((g.fiber (genericPoint W)).residueField Q.genericPoint) :=
    ((Scheme.ΓSpecIso (.of (W.residueField (genericPoint W)))).inv ≫
      (g.fiberToSpecResidueField (genericPoint W)).appTop ≫
      (g.fiber (genericPoint W)).Γevaluation Q.genericPoint).hom.toAlgebra
  have hft : LocallyOfFiniteType (g.fiberToSpecResidueField (genericPoint W)) :=
    IsProper.toLocallyOfFiniteType
  have hfin : Module.Finite (W.residueField (genericPoint W))
      ((g.fiber (genericPoint W)).residueField Q.genericPoint) :=
    @finite_residueField_over_field_of_isClosed _ _ _
    (g.fiberToSpecResidueField (genericPoint W)) hft Q.genericPoint
    (isClosed_singleton_genericPoint_of_isCurve' (k := W.residueField (genericPoint W))
      (g.fiberToSpecResidueField (genericPoint W)) Q)
  exact Module.finrank_pos

/-- **A horizontal prime divisor has positive degree on the generic fibre.** If `g` maps the
generic point of `P` to the generic point of `W`, then `P` comes from a closed point of the
generic fibre `V_η`, whose residue degree over `k(W)` is positive. -/
theorem genericFiberPointDegree_pos_of_map_genericPoint_eq {P : MMP.Mori.PrimeDivisor V}
    (hP : g P.genericPoint = genericPoint W) : 0 < genericFiberPointDegree g P := by
  obtain ⟨Q, rfl⟩ := mem_range_fiberPrimeDivisor hP
  exact genericFiberPointDegree_fiberPrimeDivisor_pos Q

end Positive

variable [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian (g.fiber (genericPoint W))] [IsNormal (g.fiber (genericPoint W))]
  [AlgebraicGeometry.IsCurve (W.residueField (genericPoint W))
    (g.fiberToSpecResidueField (genericPoint W))]
  [Smooth (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))]

/-- **The degree of the restriction of a divisor to the generic fibre.** If `D'` on `V_η` has the
coefficients of `D` along the horizontal prime divisors, `deg_{k(W)} 𝒪_{V_η}(D') = D · E_g`. -/
theorem invertibleCurveDegree_eq_genericFiberDegree (D : Divisor V)
    (D' : Divisor (g.fiber (genericPoint W)))
    (hD' : ∀ Q, D'.coeff Q = D.coeff (fiberPrimeDivisor g Q))
    (hdim : topologicalKrullDim (g.fiber (genericPoint W)) ≤ 1)
    [SheafOfModules.IsInvertible (g.fiber (genericPoint W)).presheaf
      (g.fiber (genericPoint W)).ringCatSheaf.2 D'.divisorialSheaf] :
    (invertibleCurveDegree (W.residueField (genericPoint W))
      (g.fiberToSpecResidueField (genericPoint W)) hdim D'.divisorialSheaf : ℚ) =
      genericFiberDegree g (Divisor.toQDivisor D) := by
  classical
  rw [invertibleCurveDegree_divisorialSheaf_eq_sum _ D' hdim, Finsupp.sum, Int.cast_sum,
    genericFiberDegree]
  have hsupp : D'.support = (Divisor.toQDivisor D).support.preimage (fiberPrimeDivisor g)
      fiberPrimeDivisor_injective.injOn := by
    ext Q
    rw [Finset.mem_preimage, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    change D'.coeff Q ≠ 0 ↔ (Divisor.toQDivisor D).coeff _ ≠ 0
    rw [hD' Q, Divisor.coeff_toQDivisor, Int.cast_ne_zero]
  rw [hsupp, ← Finset.sum_preimage (fiberPrimeDivisor g) _ fiberPrimeDivisor_injective.injOn _
    fun P _ hP => ?_]
  · refine Finset.sum_congr rfl fun Q _ => ?_
    rw [genericFiberPointDegree_fiberPrimeDivisor Q, Divisor.coeff_toQDivisor, ← hD' Q]
    push_cast
    rfl
  · rw [genericFiberPointDegree, ite_eq_right (fun h => hP (mem_range_fiberPrimeDivisor h)),
      Nat.cast_zero, mul_zero]

/-- **The canonical divisor has degree `2g - 2` on the generic fibre**: `K_V · E_g = 2g - 2`,
`K_V` restricting to a divisor of `E_g` whose sheaf is `Ω¹_{E_g/k(W)}`. -/
theorem two_mul_genus_sub_two_eq_genericFiberDegree {K : Divisor V}
    [GeometricallyConnected (g.fiberToSpecResidueField (genericPoint W))]
    (DK : Divisor (g.fiber (genericPoint W)))
    (hDK : ∀ Q, DK.coeff Q = K.coeff (fiberPrimeDivisor g Q))
    (eK : DK.divisorialSheaf ≅
      Scheme.Hom.relativeDifferentials (g.fiberToSpecResidueField (genericPoint W))) :
    2 * (genus (g.fiberToSpecResidueField (genericPoint W)) : ℚ) - 2 =
      genericFiberDegree g (Divisor.toQDivisor K) := by
  have hdim := (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
    (k := W.residueField (genericPoint W)) (f := g.fiberToSpecResidueField (genericPoint W))).le
  have : CompactSpace (g.fiber (genericPoint W)) :=
    QuasiCompact.compactSpace_of_compactSpace (g.fiberToSpecResidueField (genericPoint W))
  have := (MMP.Fourfold.isCartier_of_isSmoothScheme ((isSmoothScheme_iff
    (g.fiberToSpecResidueField (genericPoint W))).mpr inferInstance)
      DK).isInvertibleModule_divisorialSheaf
  have := isIso_ΓSpecIso_inv_comp_appTop_of_smooth (κ := W.residueField (genericPoint W))
    (g.fiberToSpecResidueField (genericPoint W))
  rw [← invertibleCurveDegree_eq_genericFiberDegree K DK hDK hdim,
    invertibleCurveDegree_eq_of_iso _ _ hdim eK,
    invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two]
  push_cast
  rfl

end Degree

/-- If `𝒪_X(D)` is trivial and every divisor of `X` is Cartier, `𝒪_X(m D)` is trivial for every
`m ≥ 1`. -/
theorem isTrivial_divisorialSheaf_nsmul {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hcart : ∀ D : Divisor X, D.IsCartier) {D : Divisor X}
    (hD : SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.property D.divisorialSheaf)
    {m : ℕ} (hm : 0 < m) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.property (m • D).divisorialSheaf := by
  obtain ⟨e⟩ := hD
  let e₀ : D.divisorialSheaf ≅ SheafOfModules.unit X.ringCatSheaf := e
  suffices Nonempty ((m • D).divisorialSheaf ≅ SheafOfModules.unit X.ringCatSheaf) from
    this.elim fun e' => ⟨e'⟩
  induction m, hm using Nat.le_induction with
  | base => exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_smul ℕ D)) ≪≫ e₀⟩
  | succ m hm ih =>
    obtain ⟨e'⟩ := ih
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul D m)) ≪≫
      ((hcart _).divisorialSheafTensorIso (hcart D)).symm ≪≫ tensorIso e' e₀ ≪≫ λ_ _⟩

/-! ### Restricting divisors of a contraction to the generic fibre -/

section RestrictToGenericFiber

variable {k : Type u} [Field k] [CharZero k] {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsLocallyNoetherian V] [IsNormal V] {n : ℕ} {K : Divisor V}
    {g : V ⟶ W} [IsIntegral W] (hg : IsContraction k sW sV g) (hK : K.IsCanonicalDivisor sV n)
    [IsLocallyNoetherian (g.fiber (genericPoint W))] [IsNormal (g.fiber (genericPoint W))]
    [IsIntegral (g.fiber (genericPoint W))]
    [AlgebraicGeometry.IsCurve (W.residueField (genericPoint W))
      (g.fiberToSpecResidueField (genericPoint W))]
    [Smooth (g.fiberToSpecResidueField (genericPoint W))]
    [IsProper (g.fiberToSpecResidueField (genericPoint W))]

include hg

omit [IsLocallyNoetherian V] [IsNormal V] [IsIntegral (g.fiber (genericPoint W))]
  [Smooth (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))] in
/-- The generic fibre lies in the smooth locus of `V`: its local rings are regular, being local
rings of the regular curve `V_η`. -/
private theorem fiberι_mem_smoothLocus (q : g.fiber (genericPoint W)) :
    g.fiberι _ q ∈ smoothLocus sV := by
  have := isRegularLocalRing_stalk_of_isNormal (g.fiber (genericPoint W))
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := W.residueField (genericPoint W))
      (f := g.fiberToSpecResidueField (genericPoint W))).le q
  have := isIso_stalkMap_fiberι_genericPoint' g q
  have : IsRegularLocalRing (V.presheaf.stalk (g.fiberι _ q)) := IsRegularLocalRing.of_ringEquiv
    (asIso ((g.fiberι _).stalkMap q)).commRingCatIsoToRingEquiv.symm
  have : PerfectField k := PerfectField.ofCharZero
  have := hg.isVariety_source.toLocallyOfFiniteType
  exact mem_smoothLocus_of_isRegularLocalRing sV _

/-- The inclusion of the generic fibre into the smooth locus of `V`. -/
private noncomputable def fiberToSmoothLocus :
    g.fiber (genericPoint W) ⟶ (smoothLocus sV).toScheme :=
  IsOpenImmersion.lift (smoothLocus sV).ι (g.fiberι (genericPoint W)) (by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact fiberι_mem_smoothLocus hg q)

omit [IsLocallyNoetherian V] [IsNormal V] [IsIntegral (g.fiber (genericPoint W))]
  [Smooth (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))] in
private theorem fiberToSmoothLocus_ι :
    fiberToSmoothLocus hg ≫ (smoothLocus sV).ι = g.fiberι (genericPoint W) :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsLocallyNoetherian V] [IsNormal V] [IsIntegral (g.fiber (genericPoint W))]
  [Smooth (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))] in
private theorem isIso_stalkMap_fiberToSmoothLocus (q : g.fiber (genericPoint W)) :
    IsIso ((fiberToSmoothLocus hg).stalkMap q) := by
  have h1 : IsIso ((fiberToSmoothLocus hg ≫ (smoothLocus sV).ι).stalkMap q) := by
    rw [fiberToSmoothLocus_ι hg]; exact isIso_stalkMap_fiberι_genericPoint' g q
  rw [Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (IsOpenImmersion.instIsIsoCommRingCatStalkMap (smoothLocus sV).ι _) h1

omit [IsLocallyNoetherian V] [IsNormal V]
  [Smooth (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))] in
private theorem nonempty_smoothLocus : Nonempty (smoothLocus sV) := by
  obtain ⟨q⟩ := (inferInstance : Nonempty (g.fiber (genericPoint W)))
  exact ⟨⟨_, fiberι_mem_smoothLocus hg q⟩⟩

omit [Smooth (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))] in
include hK in
/-- The smooth locus of the normal variety `V` of dimension `n` is smooth of relative
dimension `n` over `k`. -/
private theorem smoothOfRelativeDimension_smoothLocus :
    SmoothOfRelativeDimension n ((smoothLocus sV).ι ≫ sV) := by
  have := hg.isVariety_source.toIsIntegral
  have := hg.isVariety_source.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sV :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have := smooth_smoothLocus_ι sV
  have := nonempty_smoothLocus hg
  have := MMP.Fourfold.isDominant_ι_of_nonempty (smoothLocus sV)
  have hX : IsNormalVariety k sV := ⟨hg.isVariety_source, inferInstance⟩
  have : MMP.Mori.IsVariety k ((smoothLocus sV).ι ≫ sV) := (isNormalVariety_ι hX _).1
  exact MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ n
    ((topologicalKrullDim_opens_eq hX _).trans hK.1)

omit [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian (g.fiber (genericPoint W))]
  [IsNormal (g.fiber (genericPoint W))] [IsIntegral (g.fiber (genericPoint W))]
  [AlgebraicGeometry.IsCurve (W.residueField (genericPoint W))
    (g.fiberToSpecResidueField (genericPoint W))]
  [Smooth (g.fiberToSpecResidueField (genericPoint W))]
  [IsProper (g.fiberToSpecResidueField (genericPoint W))] in
/-- The differentials of the function field `k(W)` over `k` form a finite free module: `W` is
smooth over `k` at its generic point. -/
private theorem exists_isFiniteLocallyFreeOfRank_relativeDifferentials_residueField :
    ∃ d, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (W.fromSpecResidueField (genericPoint W) ≫ sW)) d := by
  have := hg.isVariety_target.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sW :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : PerfectField k := PerfectField.ofCharZero
  have hη : genericPoint W ∈ smoothLocus sW := mem_smoothLocus_of_isRegularLocalRing sW _
  have := smooth_smoothLocus_ι sW
  obtain ⟨V', hV', r, hr⟩ :=
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict
      (Scheme.Hom.relativeDifferentials ((smoothLocus sW).ι ≫ sW))
      (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials _) ⟨_, hη⟩
  have hrange : Set.range (W.fromSpecResidueField (genericPoint W)) ⊆
      Set.range (V'.ι ≫ (smoothLocus sW).ι) := by
    rw [Scheme.range_fromSpecResidueField]
    rintro _ rfl
    exact ⟨⟨⟨genericPoint W, hη⟩, hV'⟩, rfl⟩
  let j := IsOpenImmersion.lift (V'.ι ≫ (smoothLocus sW).ι)
    (W.fromSpecResidueField (genericPoint W)) hrange
  have hj : j ≫ V'.ι ≫ (smoothLocus sW).ι = W.fromSpecResidueField (genericPoint W) :=
    IsOpenImmersion.lift_fac _ _ _
  have hjs : ∀ s, IsIso (j.stalkMap s) := by
    intro s
    have h1 : IsIso ((j ≫ V'.ι ≫ (smoothLocus sW).ι).stalkMap s) := by
      rw [hj]
      have := isIso_residue_genericPoint W
      change IsIso ((Spec.map (W.residue (genericPoint W)) ≫
        W.fromSpecStalk (genericPoint W)).stalkMap s)
      rw [Scheme.Hom.stalkMap_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _
        (isIso_stalkMap_fromSpecStalk (genericPoint W) _)
        (IsOpenImmersion.instIsIsoCommRingCatStalkMap (Spec.map (W.residue (genericPoint W))) s)
    rw [Scheme.Hom.stalkMap_comp] at h1
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
      (IsOpenImmersion.instIsIsoCommRingCatStalkMap (V'.ι ≫ (smoothLocus sW).ι) _) h1
  have hc : j ≫ (V'.ι ≫ (smoothLocus sW).ι ≫ sW) =
      (W.fromSpecResidueField (genericPoint W) ≫ sW) ≫ 𝟙 _ := by
    rw [Category.comp_id, ← hj]
    simp only [Category.assoc]
  have e1 := isIso_relativeDifferentialsMap_of_isIso_stalkMap j
    (V'.ι ≫ (smoothLocus sW).ι ≫ sW) _ hc hjs
  have hc2 : V'.ι ≫ ((smoothLocus sW).ι ≫ sW) = (V'.ι ≫ (smoothLocus sW).ι ≫ sW) ≫ 𝟙 _ := by
    simp
  have e2 := isIso_relativeDifferentialsMap_of_isIso_stalkMap V'.ι
    ((smoothLocus sW).ι ≫ sW) _ hc2 (fun _ => inferInstance)
  have hr' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (V'.ι ≫ (smoothLocus sW).ι ≫ sW)) r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback V'.ι).app _ ≪≫ @asIso _ _ _ _ _ e2) hr
  exact ⟨r, SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (@asIso _ _ _ _ _ e1)
    (Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_obj j _ r)⟩

include hK in
/-- **The canonical divisor restricts to a canonical divisor of the generic fibre.** There is a
divisor on `V_η`, with the coefficients of `K_V` along the horizontal prime divisors, whose sheaf
is `Ω¹_{V_η/k(W)}`. -/
theorem exists_divisor_fiber_canonical :
    ∃ DK : Divisor (g.fiber (genericPoint W)),
      (∀ Q, DK.coeff Q = K.coeff (fiberPrimeDivisor g Q)) ∧
      Nonempty (DK.divisorialSheaf ≅
        Scheme.Hom.relativeDifferentials (g.fiberToSpecResidueField (genericPoint W))) := by
  have := hg.isVariety_source.toIsIntegral
  have := hg.isVariety_source.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sV :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : IsDominant g := isDominant_of_forall_isIso_app g hg.isIso_app
  have := nonempty_smoothLocus hg
  have := MMP.Fourfold.isDominant_ι_of_nonempty (smoothLocus sV)
  have := smooth_smoothLocus_ι sV
  have := smoothOfRelativeDimension_smoothLocus hg hK
  have hsm : IsSmoothScheme ((smoothLocus sV).ι ≫ sV) := (isSmoothScheme_iff _).mpr inferInstance
  have : CompactSpace V := by
    have := hg.isVariety_source.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sV
  have : IsNoetherian V := {}
  have : CompactSpace (smoothLocus sV) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : CompactSpace (g.fiber (genericPoint W)) :=
    QuasiCompact.compactSpace_of_compactSpace (g.fiberToSpecResidueField (genericPoint W))
  have : IsDominant (fiberToSmoothLocus hg) := by
    have : IsDominant (fiberToSmoothLocus hg ≫ (smoothLocus sV).ι) := by
      rw [fiberToSmoothLocus_ι hg]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion _ (smoothLocus sV).ι
  have hKU : Divisor.IsCartier (K.restrictOpen (smoothLocus sV)) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hB : ∀ Z, fiberToSmoothLocus hg (componentGenericPoint _ Z) ∉
      (K.restrictOpen (smoothLocus sV)).supp :=
    fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant _ _ Z
  refine ⟨Divisor.pullback (K.restrictOpen (smoothLocus sV)) hKU hB, fun Q => ?_, ?_⟩
  · have := isIso_stalkMap_fiberToSmoothLocus hg Q.genericPoint
    have hc : Order.coheight (fiberToSmoothLocus hg Q.genericPoint) = 1 := by
      rw [← coheight_eq_of_isOpenImmersion (smoothLocus sV).ι, ← Scheme.Hom.comp_apply,
        fiberToSmoothLocus_ι hg, coheight_fiberι_genericPoint]
      exact Q.coheight_genericPoint
    rw [coeff_eq_of_isPullback hKU (Divisor.isPullback_pullback hKU hB) Q
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc)
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm,
      DivisorWithCoeffs.coeff_restrictOpen]
    congr 1
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap, genericPoint_fiberPrimeDivisor',
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, ← Scheme.Hom.comp_apply,
      fiberToSmoothLocus_ι hg]
  · have hcomm : fiberToSmoothLocus hg ≫ (smoothLocus sV).ι ≫ sV =
        g.fiberToSpecResidueField (genericPoint W) ≫
          (W.fromSpecResidueField (genericPoint W) ≫ sW) := by
      rw [← Category.assoc, fiberToSmoothLocus_ι hg, ← hg.comp_eq,
        ← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc]
    obtain ⟨e1⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hKU
      (fiberToSmoothLocus hg) hB
    obtain ⟨e2⟩ := nonempty_divisorialSheaf_restrictOpen_iso K (smoothLocus sV)
    have : MMP.Mori.IsVariety (W.residueField (genericPoint W))
        (g.fiberToSpecResidueField (genericPoint W)) :=
      (inferInstance : AlgebraicGeometry.IsCurve (W.residueField (genericPoint W))
        (g.fiberToSpecResidueField (genericPoint W))).toIsVariety
    have : SmoothOfRelativeDimension 1 (g.fiberToSpecResidueField (genericPoint W)) :=
      MMP.Intersection.smoothOfRelativeDimension_of_isVariety
        (k := W.residueField (genericPoint W)) _ 1
        (by rw [AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
          (k := W.residueField (genericPoint W)) (f := g.fiberToSpecResidueField _)]; rfl)
    obtain ⟨e3⟩ := nonempty_pullback_relativeDifferentialForms_iso
      (κ := W.residueField (genericPoint W))
      (g.fiberToSpecResidueField (genericPoint W)) _
      (exists_isFiniteLocallyFreeOfRank_relativeDifferentials_residueField hg) _ n
      (fiberToSmoothLocus hg) (isIso_stalkMap_fiberToSmoothLocus hg) hcomm
    exact ⟨e1 ≪≫ (Scheme.Modules.pullback (fiberToSmoothLocus hg)).mapIso
      (e2 ≪≫ hK.iso) ≪≫ e3⟩

/-- A Cartier divisor `M` restricts to the generic fibre: the pull-back has the coefficients of
`M` along the horizontal prime divisors, and its sheaf is the restriction of `𝒪_V(M)`. -/
theorem exists_divisor_fiber_pullback {M : Divisor V} (hMc : M.IsCartier) :
    ∃ DM : Divisor (g.fiber (genericPoint W)),
      (∀ Q, DM.coeff Q = M.coeff (fiberPrimeDivisor g Q)) ∧
      Nonempty (DM.divisorialSheaf ≅
        (Scheme.Modules.pullback (g.fiberι (genericPoint W))).obj M.divisorialSheaf) := by
  have := hg.isVariety_source.toIsIntegral
  have : IsDominant g := isDominant_of_forall_isIso_app g hg.isIso_app
  have : CompactSpace V := by
    have := hg.isVariety_source.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sV
  have : CompactSpace (g.fiber (genericPoint W)) :=
    QuasiCompact.compactSpace_of_compactSpace (g.fiberToSpecResidueField (genericPoint W))
  have hB : ∀ Z, g.fiberι (genericPoint W) (componentGenericPoint _ Z) ∉ M.supp :=
    fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant _ _ Z
  refine ⟨M.pullback hMc hB, fun Q => ?_,
    MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hMc _ hB⟩
  have := isIso_stalkMap_fiberι_genericPoint' g Q.genericPoint
  exact coeff_eq_of_isPullback hMc (Divisor.isPullback_pullback hMc hB) Q _
    (genericPoint_fiberPrimeDivisor Q).symm

end RestrictToGenericFiber

/-! ### The log canonical bundle of a log elliptic fiber space on the generic fibre -/

section LogElliptic

variable {k : Type u} [Field k] [CharZero k] {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsLocallyNoetherian V] [IsNormal V] {n : ℕ} {K : Divisor V}
    {Δ : QDivisor V} {g : V ⟶ W} [IsIntegral W] (h : IsLogEllipticFiberSpace k sV sW n K Δ g)
    [IsLocallyNoetherian (g.fiber (genericPoint W))] [IsNormal (g.fiber (genericPoint W))]
    [IsIntegral (g.fiber (genericPoint W))]
    [AlgebraicGeometry.IsCurve (W.residueField (genericPoint W))
      (g.fiberToSpecResidueField (genericPoint W))]
    [Smooth (g.fiberToSpecResidueField (genericPoint W))]
    [IsProper (g.fiberToSpecResidueField (genericPoint W))]

include h

/-- **`𝒪_V(n₀(K_V + Δ_V))` is trivial on the generic fibre.** With `δ = Δ_V · E_g ≥ 0`,
`2g - 2 + δ = (K_V + Δ_V) · E_g = 0`. If `g = 0`, `𝒪_V(M)|_{E_g}` has degree
`n₀ (K_V + Δ_V) · E_g = 0`; if `g = 1`, then `δ = 0`, so `Δ_V` has no horizontal component,
`M|_{E_g} = n₀ K_V|_{E_g}`, and `𝒪_{E_g}(K_V|_{E_g}) ≅ Ω¹_{E_g/k(W)}` is trivial. -/
private theorem isTrivial_pullback_divisorialSheaf_of_isLogEllipticFiberSpace
    [GeometricallyConnected (g.fiberToSpecResidueField (genericPoint W))] {n₀ : ℕ}
    (hn₀ : 0 < n₀) {M : Divisor V}
    (hM : Divisor.toQDivisor M = (n₀ : ℤ) • (Divisor.toQDivisor K + Δ)) (hMc : M.IsCartier)
    [SheafOfModules.IsInvertible (g.fiber (genericPoint W)).presheaf
      (g.fiber (genericPoint W)).ringCatSheaf.property
      ((Scheme.Modules.pullback (g.fiberι (genericPoint W))).obj M.divisorialSheaf)] :
    SheafOfModules.IsTrivial (g.fiber (genericPoint W)).presheaf
      (g.fiber (genericPoint W)).ringCatSheaf.property
      ((Scheme.Modules.pullback (g.fiberι (genericPoint W))).obj M.divisorialSheaf) := by
  have hdim := (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
    (k := W.residueField (genericPoint W)) (f := g.fiberToSpecResidueField (genericPoint W))).le
  have hcart : ∀ D : Divisor (g.fiber (genericPoint W)), D.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme
      ((isSmoothScheme_iff (g.fiberToSpecResidueField (genericPoint W))).mpr inferInstance)
  have : CompactSpace (g.fiber (genericPoint W)) :=
    QuasiCompact.compactSpace_of_compactSpace (g.fiberToSpecResidueField (genericPoint W))
  obtain ⟨DK, hDK, ⟨eK⟩⟩ := exists_divisor_fiber_canonical h.isContraction h.isCanonicalDivisor
  obtain ⟨DM, hDM, ⟨eM⟩⟩ := exists_divisor_fiber_pullback h.isContraction hMc
  have := (hcart DM).isInvertibleModule_divisorialSheaf
  have hΔ : ∀ P, 0 ≤ Δ.coeff P := fun P => by
    have := (h.isLogVariety.isBoundary P).1
    rwa [QDivisor.coeff_toRDivisor, Rat.cast_nonneg] at this
  have h0 : genericFiberDegree g (Divisor.toQDivisor K) + genericFiberDegree g Δ = 0 := by
    rw [← genericFiberDegree_add]; exact h.genericFiberDegree_eq_zero
  have hK := two_mul_genus_sub_two_eq_genericFiberDegree DK hDK eK
  have hΔ0 := genericFiberDegree_nonneg (g := g) hΔ
  obtain ⟨hz, ho⟩ :=
    MMP.isTrivial_of_genus_eq_zero_and_isTrivial_relativeDifferentials_of_genus_eq_one
    (K := W.residueField (genericPoint W)) (g.fiberToSpecResidueField (genericPoint W))
  rcases Nat.lt_or_ge (genus (g.fiberToSpecResidueField (genericPoint W))) 1 with hg | hg
  · refine hz (Nat.lt_one_iff.mp hg) _ ?_
    have h2 : (invertibleCurveDegree (W.residueField (genericPoint W))
        (g.fiberToSpecResidueField (genericPoint W)) hdim DM.divisorialSheaf : ℚ) = 0 := by
      rw [invertibleCurveDegree_eq_genericFiberDegree M DM hDM hdim, hM,
        genericFiberDegree_zsmul, genericFiberDegree_add, h0, mul_zero]
    rw [← invertibleCurveDegree_eq_of_iso _ _ hdim eM]
    exact_mod_cast h2
  · have hg1 : genus (g.fiberToSpecResidueField (genericPoint W)) = 1 :=
      le_antisymm (by exact_mod_cast (by linarith :
        (genus (g.fiberToSpecResidueField (genericPoint W)) : ℚ) ≤ 1)) hg
    have hgΔ : genericFiberDegree g Δ = 0 := by
      rw [hg1] at hK
      norm_num at hK
      linarith
    have hDMK : DM = n₀ • DK := by
      ext Q
      have hc := congrArg (fun D : QDivisor V => D.coeff (fiberPrimeDivisor g Q)) hM
      simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
        Divisor.coeff_toQDivisor, coeff_eq_zero_of_genericFiberDegree_eq_zero hΔ hgΔ
          (genericFiberPointDegree_fiberPrimeDivisor_pos Q), add_zero, zsmul_eq_mul] at hc
      change DM.coeff Q = (n₀ • DK).coeff Q
      rw [hDM Q, DivisorWithCoeffs.coeff_smul, hDK Q, nsmul_eq_mul]
      exact_mod_cast hc
    obtain ⟨eΩ⟩ := ho hg1
    obtain ⟨e⟩ := isTrivial_divisorialSheaf_nsmul hcart ⟨eK ≪≫ eΩ⟩ hn₀
    exact ⟨eM.symm ≪≫ eqToIso (by rw [hDMK]) ≪≫ e⟩

end LogElliptic

/-- **The log canonical bundle is trivial on the generic fiber** (FA, proof of 15.12). Let
`g : (V, Δ_V) ⟶ W` be a log elliptic fiber space over a field `k` of characteristic zero, with
`K_V` a canonical divisor of `V`, and let `n₀ > 0` be such that `n₀ (K_V + Δ_V)` is a Cartier
divisor `M`. Then the restriction of `𝒪_V(M)` to the generic fiber `E_g` of `g` is isomorphic
to `𝒪_{E_g}`. -/
@[mmp "lem_fa15_generic_fiber_torsion"]
public theorem IsLogEllipticFiberSpace.isTrivial_pullback_fiberι_divisorialSheaf
    {k : Type u} [Field k] [CharZero k] {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsLocallyNoetherian V] [IsNormal V] {n : ℕ} {K : Divisor V}
    {Δ : QDivisor V} {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW n K Δ g)
    {n₀ : ℕ} (hn₀ : 0 < n₀) {M : Divisor V}
    (hM : Divisor.toQDivisor M = (n₀ : ℤ) • (Divisor.toQDivisor K + Δ)) (hMc : M.IsCartier) :
    haveI := h.isContraction.isVariety_target.toIsIntegral
    SheafOfModules.IsTrivial (g.fiber (genericPoint W)).presheaf
      (g.fiber (genericPoint W)).ringCatSheaf.property
      ((Scheme.Modules.pullback (g.fiberι (genericPoint W))).obj M.divisorialSheaf) := by
  have := h.isContraction.isVariety_target.toIsIntegral
  have := h.isContraction.isVariety_source.toIsIntegral
  have : IsDominant g := isDominant_of_forall_isIso_app g h.isContraction.isIso_app
  have := isCurve_fiberToSpecResidueField h.isContraction h.dim_genericFiber
  have := smooth_fiberToSpecResidueField h.isContraction h.dim_genericFiber
  have := geometricallyConnected_fiberToSpecResidueField h.isContraction
  have := isInvertible_pullback_fiberι_divisorialSheaf h.isContraction hMc
  have := h.isContraction.isProper
  have : IsProper (g.fiberToSpecResidueField (genericPoint W)) :=
    AlgebraicGeometry.isProper_fiberToSpecResidueField g _
  have := isNormal_genericFiber g
  have : IsLocallyNoetherian (g.fiber (genericPoint W)) :=
    LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField (genericPoint W))
  have := AlgebraicGeometry.isIntegral_fiber_genericPoint g
  exact isTrivial_pullback_divisorialSheaf_of_isLogEllipticFiberSpace h hn₀ hM hMc

end GenericFiberTorsion

end MMP.Flips

end
