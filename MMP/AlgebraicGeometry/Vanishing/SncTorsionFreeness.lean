module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.Cartier
import MMP.AlgebraicGeometry.Singularities.CyclicCover.UnramifiedOffZeroScheme
import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.ReducedSncBoundary
import MMP.AlgebraicGeometry.Divisor.QuasiProjectiveCartierSupport
import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisorSupport
import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackSheaf
import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackEffective
import MMP.AlgebraicGeometry.Divisor.OrderPullback
import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
import MMP.AlgebraicGeometry.Vanishing.SemiampleInjectivity
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Divisor.GeneralMemberAdjunction
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.Resolution.SmoothCentreBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Divisor.Arithmetic
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.SubschemeOver
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Bertini.FreeSystemIrreducible
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Bertini.GeneralHyperplane
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Divisor.SmallAffineMovingDivisors
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.ChangeOfField

/-!
# Associated points of higher direct images of snc adjoint sheaves

Let `f : V ⟶ X` be a projective morphism of complex projective varieties, with `V` smooth, let
`K_V` be a canonical divisor of `V`, and let `B` be a `ℚ`-divisor with simple normal crossing support and coefficients in `[0, 1]`. The
*lc strata* of `(V, B)` are `V` itself and the strata of the reduced part `⌊B⌋`. If `M` is a
Cartier divisor with `M - (K_V + B)` semiample over `X`, then every associated point of
`R^q f_* 𝒪_V(M)` is the generic point of the image `f(S)` of an lc stratum `S` of `(V, B)`.
This is Kollár's torsion-freeness theorem in Ambro's and Fujino's form for snc pairs.

## Main results

* `MMP.Mori.exists_isSNCStratum_closure_eq_image_of_isAssociatedPoint_rightDerived_pushforward`:
  every associated point of `R^q f_* 𝒪_V(M)` is the generic point of the image of an lc stratum.

## Implementation notes

* `V` and `X` carry structure morphisms `sV`, `sX` to `Spec ℂ`, and `f ≫ sX = sV` says that `f`
  is a morphism over `ℂ`.
* The lc strata are `MMP.Fourfold.IsSNCStratum` of `MMP.Mori.DivisorWithCoeffs.roundDown B`;
  the empty intersection gives `V` itself.
* Associated points are `Stacks.Divisors.IsAssociatedPoint` (Stacks 02OJ). "`x` is the generic
  point of `f(S)`" is `closure {x} = f '' S`; `f` is proper, so `f '' S` is closed and
  irreducible, and `x` is its generic point.
* Semiampleness over `X` is `MMP.Fourfold.QDivisor.IsRelativelySemiample f`.
* `R^q f_*` is the `q`-th right derived functor of `Scheme.Modules.pushforward f`, and
  `𝒪_V(M)` is `MMP.Mori.Divisor.divisorialSheaf`.
* The proof follows Fujino: assuming an associated point `x` that is no stratum image,
  the boundary is cleaned by blow-ups of strata of codimension at least two and by subtracting
  components, until semiample injectivity
  (`MMP.Mori.injective_derivedCohomologyOverField_map_divisorialSheafInclusion_of_semiample`)
  for a general hyperplane through `x` gives a contradiction. Its helpers are private, in the
  namespace `Proof_thm_mmp_lc_bpf_snc_torsion_free`.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011],
  Theorem 6.3
* [F. Ambro, *Quasi-log varieties*][Ambro2003]
* [J. Kollár, *Higher direct images of dualizing sheaves I*][Kollar1986]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

namespace Proof_thm_mmp_lc_bpf_snc_torsion_free

/-! ### The degenerate Leray sequence, in injectivity form -/

section Leray

open CategoryTheory.Limits

section Abstract

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
    [Abelian C] [EnoughInjectives A]

private noncomputable def delta (F : A ⥤ B) [F.Additive] : DeltaFunctor A B :=
  letI := HasDerivedCategory.standard A
  letI := HasDerivedCategory.standard B
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F

private noncomputable def dlt (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁ :=
  (delta F).δ hS n

private theorem map_g_dlt (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (F.rightDerived n).map S.g ≫ dlt F hS n = 0 :=
  (delta F).map_g_δ hS n

private theorem dlt_map_f (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : dlt F hS n ≫ (F.rightDerived (n + 1)).map S.f = 0 :=
  (delta F).δ_map_f hS n

private theorem exact_dlt₁ (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (ShortComplex.mk _ _ (map_g_dlt F hS n)).Exact :=
  (delta F).exact_δ₁ hS n

private theorem exact_dlt₂ (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (ShortComplex.mk _ _ (dlt_map_f F hS n)).Exact :=
  (delta F).exact_δ₂ hS n

private theorem dlt_naturality (F : A ⥤ B) [F.Additive] {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (F.rightDerived n).map φ.τ₃ ≫ dlt F hT n = dlt F hS n ≫ (F.rightDerived (n + 1)).map φ.τ₁ :=
  (delta F).δ_naturality hS hT φ n

private theorem exact_map_rightDerived (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) : (S.map (F.rightDerived n)).Exact :=
  (delta F).exact_map hS n

private theorem isZero_rightDerived_X₃ (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (p : ℕ) (h₂ : IsZero ((F.rightDerived p).obj S.X₂))
    (h₁ : IsZero ((F.rightDerived (p + 1)).obj S.X₁)) :
    IsZero ((F.rightDerived p).obj S.X₃) :=
  (exact_dlt₁ F hS p).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

private theorem isZero_rightDerived_X₂ (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (p : ℕ) (h₁ : IsZero ((F.rightDerived p).obj S.X₁))
    (h₃ : IsZero ((F.rightDerived p).obj S.X₃)) :
    IsZero ((F.rightDerived p).obj S.X₂) :=
  (exact_map_rightDerived F hS p).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

private theorem isIso_dlt (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) (h₁ : IsZero ((F.rightDerived n).obj S.X₂))
    (h₂ : IsZero ((F.rightDerived (n + 1)).obj S.X₂)) : IsIso (dlt F hS n) :=
  haveI : Mono (dlt F hS n) := (exact_dlt₁ F hS n).mono_g (h₁.eq_of_src _ _)
  haveI : Epi (dlt F hS n) := (exact_dlt₂ F hS n).epi_f (h₂.eq_of_tgt _ _)
  isIso_of_mono_of_epi _

private theorem epi_map_g (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) (h : IsZero ((F.rightDerived 1).obj S.X₁)) :
    Epi (F.map S.g) := by
  haveI : Epi ((F.rightDerived 0).map S.g) := (exact_dlt₁ F hS 0).epi_f (h.eq_of_tgt _ _)
  rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf S.g]
  infer_instance

section Pair

variable (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)

private noncomputable abbrev pairFst : ShortComplex B :=
  ShortComplex.mk ((F.rightDerived 0).map S.f) (cokernel.π _) (cokernel.condition _)

include hS in
private theorem pairFst_shortExact : (pairFst F (S := S)).ShortExact :=
  haveI : Mono ((F.rightDerived 0).map S.f) := (delta F).mono_map_f hS
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

private noncomputable abbrev pairSnd : ShortComplex B :=
  ShortComplex.mk
    (cokernel.desc ((F.rightDerived 0).map S.f) ((F.rightDerived 0).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero]))
    (dlt F hS 0)
    ((cancel_epi (cokernel.π ((F.rightDerived 0).map S.f))).1 (by
      rw [comp_zero, ← Category.assoc, cokernel.π_desc]
      exact map_g_dlt F hS 0))

private theorem pairSnd_shortExact (hI : IsZero ((F.rightDerived 1).obj S.X₂)) :
    (pairSnd F hS).ShortExact := by
  have hex := exact_dlt₁ F hS 0
  let φ : ShortComplex.mk _ _ (map_g_dlt F hS 0) ⟶ pairSnd F hS :=
    { τ₁ := cokernel.π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  have hex' : (pairSnd F hS).Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex
  have hm : Mono (pairSnd F hS).f :=
    (exact_map_rightDerived F hS 0).mono_cokernelDesc
  have he : Epi (pairSnd F hS).g := (exact_dlt₂ F hS 0).epi_f (hI.eq_of_tgt _ _)
  exact ShortComplex.ShortExact.mk' hex' hm he

end Pair

section Collapse

variable [EnoughInjectives B] (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]

private noncomputable abbrev presS (M : A) : ShortComplex A :=
  ShortComplex.mk (Injective.ι M) (cokernel.π _) (cokernel.condition _)

private theorem presS_shortExact (M : A) : (presS M).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- A morphism of injective presentations lying over `φ`. -/
private noncomputable def presMap {M M' : A} (φ : M ⟶ M') : presS M ⟶ presS M' where
  τ₁ := φ
  τ₂ := Injective.factorThru (φ ≫ Injective.ι M') (Injective.ι M)
  τ₃ := cokernel.map (Injective.ι M) (Injective.ι M') φ
    (Injective.factorThru (φ ≫ Injective.ι M') (Injective.ι M)) (by simp)
  comm₁₂ := by simp
  comm₂₃ := by simp

omit [PreservesFiniteLimits G] in
private theorem isZero_rightDerived_pairFst_X₃
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M)))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((G.rightDerived p).obj (pairFst F (S := presS M)).X₃) := by
  refine isZero_rightDerived_X₃ G (pairFst_shortExact F (presS_shortExact M)) p ?_ (h0 _ (by omega))
  exact (hFG _ inferInstance p hp).of_iso
    ((G.rightDerived p).mapIso ((F.rightDerivedZeroIsoSelf).app (Injective.under M)))

omit [PreservesFiniteLimits G] in
private theorem isZero_rightDerived_presS_X₃
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M)))
    (h1 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 1).obj M)))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj (presS M).X₃)) :=
  isZero_rightDerived_X₂ G (pairSnd_shortExact F (presS_shortExact M)
      (Functor.isZero_rightDerived_obj_injective_succ F 0 _)) p
    (isZero_rightDerived_pairFst_X₃ F G hFG M h0 p hp) (h1 p hp)

/-- `G(R⁰F(I)) ⟶ G(R⁰F(Q)) ⟶ G(R¹F(M)) ⟶ 0` is exact, for the injective presentation
`0 ⟶ M ⟶ I ⟶ Q ⟶ 0`. -/
private theorem exact_G_dlt
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M))) :
    ∃ hz : G.map ((F.rightDerived 0).map (presS M).g) ≫ G.map (dlt F (presS_shortExact M) 0) = 0,
      (ShortComplex.mk _ _ hz).Exact ∧ Epi (G.map (dlt F (presS_shortExact M) 0)) := by
  have hS := presS_shortExact M
  have hI : IsZero ((F.rightDerived 1).obj (presS M).X₂) :=
    Functor.isZero_rightDerived_obj_injective_succ F 0 _
  have hT := pairSnd_shortExact F hS hI
  have hFst := pairFst_shortExact F hS
  have hz : G.map ((F.rightDerived 0).map (presS M).g) ≫ G.map (dlt F hS 0) = 0 := by
    rw [← G.map_comp, map_g_dlt, G.map_zero]
  refine ⟨hz, ?_, ?_⟩
  · -- `G` of the short exact sequence `0 ⟶ C ⟶ R⁰F(Q) ⟶ R¹F(M) ⟶ 0` is short exact
    have hepi : Epi (G.map (pairSnd F hS).g) :=
      epi_map_g G hT (isZero_rightDerived_pairFst_X₃ F G hFG M h0 1 one_pos)
    have hGT : ((pairSnd F hS).map G).Exact :=
      hT.exact.map_of_mono_of_preservesKernel G hT.mono_f inferInstance
    have hπ : Epi (G.map (cokernel.π ((F.rightDerived 0).map (presS M).f))) :=
      epi_map_g G hFst (h0 1 one_pos)
    let ψ : ShortComplex.mk _ _ hz ⟶ (pairSnd F hS).map G :=
      { τ₁ := G.map (cokernel.π _)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          simp only [ShortComplex.map_f, Category.comp_id]
          rw [← G.map_comp, cokernel.π_desc]
        comm₂₃ := by simp }
    have : Epi ψ.τ₁ := hπ
    have : IsIso ψ.τ₂ := by dsimp [ψ]; infer_instance
    have : Mono ψ.τ₃ := by dsimp [ψ]; infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hGT
  · exact epi_map_g G hT (isZero_rightDerived_pairFst_X₃ F G hFG M h0 1 one_pos)

/-- `R⁰(G ∘ F) ≅ R⁰F ⋙ G`. -/
private noncomputable def zeroIso : (F ⋙ G).rightDerived 0 ≅ F.rightDerived 0 ⋙ G :=
  (F ⋙ G).rightDerivedZeroIsoSelf ≪≫ Functor.isoWhiskerRight F.rightDerivedZeroIsoSelf.symm G

/-- The comparison `R¹(G ∘ F)(M) ⟶ G(R¹F(M))` attached to the injective presentation of `M`. -/
private noncomputable def theta
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M))) :
    ((F ⋙ G).rightDerived 1).obj M ≅ G.obj ((F.rightDerived 1).obj M) := by
  have hS := presS_shortExact M
  have hX := exact_dlt₁ (F ⋙ G) hS 0
  haveI : Epi (dlt (F ⋙ G) hS 0) := (exact_dlt₂ (F ⋙ G) hS 0).epi_f
    ((Functor.isZero_rightDerived_obj_injective_succ (F ⋙ G) 0 _).eq_of_tgt _ _)
  have hY := exact_G_dlt F G hFG M h0
  haveI := hY.2.2
  refine
    { hom := hX.desc ((zeroIso F G).hom.app _ ≫ G.map (dlt F hS 0)) ?_
      inv := hY.2.1.desc ((zeroIso F G).inv.app _ ≫ dlt (F ⋙ G) hS 0) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · show ((F ⋙ G).rightDerived 0).map (presS M).g ≫
      ((zeroIso F G).hom.app _ ≫ G.map (dlt F hS 0)) = 0
    rw [(zeroIso F G).hom.naturality_assoc, Functor.comp_map, ← G.map_comp, map_g_dlt,
      G.map_zero, comp_zero]
  · show G.map ((F.rightDerived 0).map (presS M).g) ≫
      ((zeroIso F G).inv.app _ ≫ dlt (F ⋙ G) hS 0) = 0
    have hn : G.map ((F.rightDerived 0).map (presS M).g) ≫ (zeroIso F G).inv.app _ =
        (zeroIso F G).inv.app _ ≫ ((F ⋙ G).rightDerived 0).map (presS M).g :=
      (zeroIso F G).inv.naturality (presS M).g
    rw [← Category.assoc, hn, Category.assoc, map_g_dlt, comp_zero]
  · rw [← cancel_epi (dlt (F ⋙ G) hS 0), ← Category.assoc, hX.g_desc, Category.assoc,
      hY.2.1.g_desc, Iso.hom_inv_id_app_assoc, Category.comp_id]
  · rw [← cancel_epi (G.map (dlt F hS 0)), ← Category.assoc, hY.2.1.g_desc, Category.assoc,
      hX.g_desc, Iso.inv_hom_id_app_assoc, Category.comp_id]

private theorem dlt_comp_theta
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M))) :
    dlt (F ⋙ G) (presS_shortExact M) 0 ≫ (theta F G hFG M h0).hom =
      (zeroIso F G).hom.app _ ≫ G.map (dlt F (presS_shortExact M) 0) := by
  have hS := presS_shortExact M
  have hX := exact_dlt₁ (F ⋙ G) hS 0
  haveI : Epi (dlt (F ⋙ G) hS 0) := (exact_dlt₂ (F ⋙ G) hS 0).epi_f
    ((Functor.isZero_rightDerived_obj_injective_succ (F ⋙ G) 0 _).eq_of_tgt _ _)
  exact hX.g_desc _ _

private theorem theta_naturality
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    {M M' : A} (φ : M ⟶ M')
    (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M)))
    (h0' : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M'))) :
    (theta F G hFG M h0).hom ≫ G.map ((F.rightDerived 1).map φ) =
      ((F ⋙ G).rightDerived 1).map φ ≫ (theta F G hFG M' h0').hom := by
  have hS := presS_shortExact M
  have hS' := presS_shortExact M'
  haveI : Epi (dlt (F ⋙ G) hS 0) := (exact_dlt₂ (F ⋙ G) hS 0).epi_f
    ((Functor.isZero_rightDerived_obj_injective_succ (F ⋙ G) 0 _).eq_of_tgt _ _)
  have hF : (F.rightDerived 0).map (presMap φ).τ₃ ≫ dlt F hS' 0 =
      dlt F hS 0 ≫ (F.rightDerived 1).map φ := dlt_naturality F hS hS' (presMap φ) 0
  have hFG : ((F ⋙ G).rightDerived 0).map (presMap φ).τ₃ ≫ dlt (F ⋙ G) hS' 0 =
      dlt (F ⋙ G) hS 0 ≫ ((F ⋙ G).rightDerived 1).map φ :=
    dlt_naturality (F ⋙ G) hS hS' (presMap φ) 0
  rw [← cancel_epi (dlt (F ⋙ G) hS 0), ← Category.assoc, dlt_comp_theta, Category.assoc,
    ← G.map_comp, ← hF, G.map_comp, ← reassoc_of% hFG, dlt_comp_theta,
    (zeroIso F G).hom.naturality_assoc]
  rfl

/-- **The degenerate Leray sequence, in injectivity form.** Let `F` and `G` be left exact, with
`F` carrying injectives to `G`-acyclic objects, and let `φ : M ⟶ M'` be a morphism such that
`R^q F(M)` and `R^q F(M')` are `G`-acyclic for every `q ≤ j`. If `R^j(G ∘ F)(φ)` is a
monomorphism, then so is `G(R^j F(φ))`. -/
private theorem mono_map_rightDerived_of_mono
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I))) :
    ∀ (j : ℕ) {M M' : A} (φ : M ⟶ M'),
      (∀ q ≤ j, ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj M))) →
      (∀ q ≤ j, ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj M'))) →
      Mono (((F ⋙ G).rightDerived j).map φ) → Mono (G.map ((F.rightDerived j).map φ))
  | 0, M, M', φ, _, _, h => by
    have hnat := (zeroIso F G).hom.naturality φ
    simp only [Functor.comp_map] at hnat
    have : G.map ((F.rightDerived 0).map φ) =
        (zeroIso F G).inv.app M ≫ ((F ⋙ G).rightDerived 0).map φ ≫ (zeroIso F G).hom.app M' := by
      rw [hnat, Iso.inv_hom_id_app_assoc]
    rw [this]
    infer_instance
  | 1, M, M', φ, hM, hM', h => by
    have hnat := theta_naturality F G hFG φ (hM 0 (by omega)) (hM' 0 (by omega))
    have : G.map ((F.rightDerived 1).map φ) =
        (theta F G hFG M (hM 0 (by omega))).inv ≫ ((F ⋙ G).rightDerived 1).map φ ≫
          (theta F G hFG M' (hM' 0 (by omega))).hom := by
      rw [← hnat, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  | k + 2, M, M', φ, hM, hM', h => by
    have hS := presS_shortExact M
    have hS' := presS_shortExact M'
    have hQ : ∀ {N : A} (hN : ∀ q ≤ k + 2, ∀ p : ℕ, 0 < p →
          IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj N))),
        ∀ q ≤ k + 1, ∀ p : ℕ, 0 < p →
          IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj (presS N).X₃)) := by
      intro N hN q hq p hp
      rcases q with _ | q
      · exact isZero_rightDerived_presS_X₃ F G hFG N (hN 0 (by omega)) (hN 1 (by omega)) p hp
      · haveI := isIso_dlt F (presS_shortExact N) (q + 1)
          (Functor.isZero_rightDerived_obj_injective_succ F q _)
          (Functor.isZero_rightDerived_obj_injective_succ F (q + 1) _)
        exact (hN (q + 2) (by omega) p hp).of_iso
          ((G.rightDerived p).mapIso (asIso (dlt F (presS_shortExact N) (q + 1))))
    haveI := isIso_dlt (F ⋙ G) hS (k + 1)
      (Functor.isZero_rightDerived_obj_injective_succ _ k _)
      (Functor.isZero_rightDerived_obj_injective_succ _ (k + 1) _)
    haveI := isIso_dlt (F ⋙ G) hS' (k + 1)
      (Functor.isZero_rightDerived_obj_injective_succ _ k _)
      (Functor.isZero_rightDerived_obj_injective_succ _ (k + 1) _)
    haveI := isIso_dlt F hS (k + 1)
      (Functor.isZero_rightDerived_obj_injective_succ F k _)
      (Functor.isZero_rightDerived_obj_injective_succ F (k + 1) _)
    haveI := isIso_dlt F hS' (k + 1)
      (Functor.isZero_rightDerived_obj_injective_succ F k _)
      (Functor.isZero_rightDerived_obj_injective_succ F (k + 1) _)
    have hFGnat : ((F ⋙ G).rightDerived (k + 1)).map (presMap φ).τ₃ ≫ dlt (F ⋙ G) hS' (k + 1) =
        dlt (F ⋙ G) hS (k + 1) ≫ ((F ⋙ G).rightDerived (k + 2)).map φ :=
      dlt_naturality (F ⋙ G) hS hS' (presMap φ) (k + 1)
    have hFnat : (F.rightDerived (k + 1)).map (presMap φ).τ₃ ≫ dlt F hS' (k + 1) =
        dlt F hS (k + 1) ≫ (F.rightDerived (k + 2)).map φ :=
      dlt_naturality F hS hS' (presMap φ) (k + 1)
    have hχ : Mono (((F ⋙ G).rightDerived (k + 1)).map (presMap φ).τ₃) := by
      have : ((F ⋙ G).rightDerived (k + 1)).map (presMap φ).τ₃ =
          dlt (F ⋙ G) hS (k + 1) ≫ ((F ⋙ G).rightDerived (k + 2)).map φ ≫
            inv (dlt (F ⋙ G) hS' (k + 1)) := by
        rw [← Category.assoc, ← hFGnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [this]
      infer_instance
    have ih := mono_map_rightDerived_of_mono hFG (k + 1) (presMap φ).τ₃ (hQ hM) (hQ hM') hχ
    have : G.map ((F.rightDerived (k + 2)).map φ) =
        G.map (inv (dlt F hS (k + 1))) ≫ G.map ((F.rightDerived (k + 1)).map (presMap φ).τ₃) ≫
          G.map (dlt F hS' (k + 1)) := by
      rw [← G.map_comp, ← G.map_comp, hFnat, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance

end Collapse

end Abstract

section Concrete

open AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard in
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso in
/-- The direct image of an injective module has no higher cohomology. -/
private theorem isZero_Hgroup_pushforward_of_injective {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : Y.Modules) (hI : Injective I) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p ((Scheme.Modules.pushforward f).obj I)) := by
  have h := @Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic _ _
    f.toLRSHom.toShHom I hI ⊤
  have h' := (@Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _ _ _ _ _
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _ _ _ _ _ _).1 h p hp
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (O := X.ringCatSheaf) ⊤ p ((Scheme.Modules.pushforward f).obj I)).1 h'

/-- Global sections `Γ(X, -)` of the underlying abelian sheaf, on `X.Modules`. -/
private noncomputable abbrev globalSec (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat.{u} :=
  secF X.ringCatSheaf ⊤

private theorem globalSec_additive (X : Scheme.{u}) : (globalSec X).Additive :=
  inferInstanceAs (secF X.ringCatSheaf ⊤).Additive
private theorem globalSec_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (globalSec X) :=
  inferInstanceAs (PreservesFiniteLimits (secF X.ringCatSheaf ⊤))

attribute [local instance] globalSec_additive globalSec_preservesFiniteLimits

/-- **The degenerate Leray sequence for `Γ(Y, -) = Γ(X, f_* -)`, in injectivity form.** -/
private theorem mono_secF_map_rightDerived_of_mono {X Y : Scheme.{u}} (f : Y ⟶ X) (j : ℕ)
    {M M' : Y.Modules} (φ : M ⟶ M')
    (hM : ∀ q ≤ j, ∀ p : ℕ, 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (((Scheme.Modules.pushforward f).rightDerived q).obj M)))
    (hM' : ∀ q ≤ j, ∀ p : ℕ, 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (((Scheme.Modules.pushforward f).rightDerived q).obj M')))
    (h : Mono ((Hfunctor Y.ringCatSheaf ⊤ j).map φ)) :
    Mono ((secF X.ringCatSheaf ⊤).map (((Scheme.Modules.pushforward f).rightDerived j).map φ)) :=
  @mono_map_rightDerived_of_mono Y.Modules X.Modules AddCommGrpCat.{u}
    _ _ _ _ _ _ _ _ (Scheme.Modules.pushforward f) (globalSec X)
    (Stacks.SchemeCohomology.pushforward_additive f) inferInstance inferInstance inferInstance
    (isZero_Hgroup_pushforward_of_injective f) j M M' φ hM hM' h

end Concrete

/-! ### Hypercohomology and sheaf cohomology -/

section Bridge

open CategoryTheory.Limits Opposite
open scoped Stacks.SmallDerivedModel

/-- A natural isomorphism of additive functors induces one of their right derived functors. -/
private noncomputable def rightDerivedIsoOfIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- Sections of a sheaf of modules, read as an abelian group. -/
private noncomputable def secFIsoEvaluationForget (X : Scheme.{u}) (V : X.Opens) :
    secF X.ringCatSheaf V ≅ SheafOfModules.evaluation X.ringCatSheaf (op V) ⋙
      forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Injectivity on the hypercohomology of the injectivity theorems is injectivity on sheaf
cohomology. -/
private theorem mono_Hfunctor_map_of_injective {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) (q : ℕ)
    {M M' : V.Modules} (φ : M ⟶ M')
    (h : Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (q : ℤ)).map
      ((derivedGlobalSectionsOver sV).map ((DerivedCategory.singleFunctor V.Modules 0).map φ))).hom) :
    Mono ((Hfunctor V.ringCatSheaf ⊤ q).map φ) := by
  have e1 := Stacks.Duality.cohomologyOverFieldFunctorIsoDerivedCohomology ℂ sV q
  have h1 : Function.Injective ((cohomologyOverFieldFunctor ℂ sV q).map φ).hom := by
    have hn := e1.hom.naturality φ
    have : (cohomologyOverFieldFunctor ℂ sV q).map φ =
        ((cohomologyOverFieldFunctor ℂ sV q).map φ ≫ e1.hom.app M') ≫ e1.inv.app M' := by
      rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [this, hn]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp]
    exact ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (e1.app M').inv)).comp
      (h.comp ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (e1.app M).hom)))
  -- the classical right derived functor of evaluation, read on abelian groups
  set E := SheafOfModules.evaluation V.ringCatSheaf (op (⊤ : V.Opens))
  have h2 : Function.Injective ((E.rightDerived q).map φ).hom := h1
  let e2 : Hfunctor V.ringCatSheaf ⊤ q ≅ E.rightDerived q ⋙
      forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat :=
    rightDerivedIsoOfIso (secFIsoEvaluationForget V ⊤) q ≪≫ Functor.rightDerivedCompIso E _ q
  have hY : Mono ((E.rightDerived q ⋙
      forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat).map φ) := by
    rw [AddCommGrpCat.mono_iff_injective]
    exact h2
  have hn := e2.hom.naturality φ
  rw [AddCommGrpCat.mono_iff_injective] at hY ⊢
  intro a b hab
  have key : ∀ z, (e2.hom.app M') ((Hfunctor V.ringCatSheaf ⊤ q).map φ z) =
      ((E.rightDerived q ⋙ forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat).map
        φ) (e2.hom.app M z) := fun z => by
    rw [← ConcreteCategory.comp_apply, hn, ConcreteCategory.comp_apply]
  have h4 := congrArg (e2.hom.app M') hab
  rw [key, key] at h4
  have h5 := congrArg (e2.inv.app M) (hY h4)
  rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, e2.hom_inv_id_app M] at h5

end Bridge

/-! ### Derived functors and central endomorphisms -/

section Central

open CategoryTheory.Limits

/-- An endomorphism of the identity functor acts on a homological complex degree by degree. -/
private def endComplexOf {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} (τ : End (𝟭 C)) (K : HomologicalComplex C c) : K ⟶ K where
  f n := τ.asHom.app (K.X n)
  comm' i j _ := (τ.asHom.naturality (K.d i j)).symm

private lemma endComplexOf_f {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} (τ : End (𝟭 C)) (K : HomologicalComplex C c) (n : ι) :
    (endComplexOf τ K).f n = τ.asHom.app (K.X n) := rfl

private theorem homologyMap_endComplexOf {C : Type*} [Category* C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (σ : End (𝟭 C)) (L : HomologicalComplex C c) (i : ι) :
    HomologicalComplex.homologyMap (endComplexOf σ L) i = σ.asHom.app (L.homology i) := by
  have hc : HomologicalComplex.cyclesMap (endComplexOf σ L) i = σ.asHom.app (L.cycles i) := by
    rw [← cancel_mono (L.iCycles i), HomologicalComplex.cyclesMap_i, endComplexOf_f]
    simpa using σ.asHom.naturality (L.iCycles i)
  rw [← cancel_epi (L.homologyπ i), HomologicalComplex.homologyπ_naturality, hc]
  simpa using (σ.asHom.naturality (L.homologyπ i)).symm

/-- **Derived functors commute with central endomorphisms.** If an additive functor `G`
intertwines endomorphisms `τ` and `σ` of the identity functors, so do its right derived
functors. -/
private theorem rightDerived_map_app_eq {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasInjectiveResolutions A] (G : A ⥤ B) [G.Additive] (τ : End (𝟭 A))
    (σ : End (𝟭 B)) (h : ∀ N, G.map (τ.asHom.app N) = σ.asHom.app (G.obj N)) (n : ℕ) (M : A) :
    (G.rightDerived n).map (τ.asHom.app M) = σ.asHom.app ((G.rightDerived n).obj M) := by
  let P : InjectiveResolution M := injectiveResolution M
  have hι : P.ι ≫ endComplexOf τ P.cocomplex = (CochainComplex.single₀ _).map (τ.asHom.app M) ≫ P.ι := by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    simp only [CochainComplex.fromSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
      endComplexOf_f, CochainComplex.single₀_map_f_zero]
    exact τ.asHom.naturality (P.ι.f 0)
  rw [Functor.rightDerived_map_eq G n (τ.asHom.app M) (P := P) (Q := P) (endComplexOf τ P.cocomplex) hι]
  have hG : (G.mapHomologicalComplex (ComplexShape.up ℕ)).map (endComplexOf τ P.cocomplex) =
      endComplexOf σ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex) :=
    HomologicalComplex.hom_ext _ _ fun k => h (P.cocomplex.X k)
  rw [Functor.comp_map, hG]
  change _ ≫ HomologicalComplex.homologyMap _ n ≫ _ = _
  rw [homologyMap_endComplexOf]
  have hn : (P.isoRightDerivedObj G n).hom ≫ σ.asHom.app _ =
      σ.asHom.app _ ≫ (P.isoRightDerivedObj G n).hom := σ.asHom.naturality (P.isoRightDerivedObj G n).hom
  erw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

section Smul

open Opposite

/-- Direct image intertwines multiplication by a function with multiplication by its pull-back. -/
private theorem pushforward_map_smulEnd {X V : Scheme.{0}} (g : V ⟶ X) (b : X.sectionsRing) (N : V.Modules) :
    (Scheme.Modules.pushforward g).map ((Scheme.smulEnd V (g.appTop b)).asHom.app N) =
      (Scheme.smulEnd X b).asHom.app ((Scheme.Modules.pushforward g).obj N) := by
  ext W s
  change ((V.smulEnd _).asHom.app N).val.app (op (g ⁻¹ᵁ W)) s = ((X.smulEnd b).asHom.app _).val.app (op W) s
  simp only [Scheme.smulEnd]
  erw [Stacks.SheafOfModules.terminalSectionToEnd_apply, Stacks.SheafOfModules.terminalSectionToEnd_apply]
  have key : (ConcreteCategory.hom (V.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ W ≤ ⊤)).op))
        ((ConcreteCategory.hom g.appTop) b) =
      (ConcreteCategory.hom (g.app W)) ((ConcreteCategory.hom
        (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op)) b) :=
    (ConcreteCategory.congr_hom (g.naturality (homOfLE (le_top : W ≤ ⊤)).op) b).symm
  erw [key]
  rfl

end Smul

end Central

end Leray

/-- A `ℚ`-divisor `H` on `V` is *generated over `X`* (by `f`) if a positive multiple `m₀ H` is an
integral divisor whose sheaf is a quotient of the pull-back of a coherent sheaf on `X`. Relative
semiampleness gives this (`isGeneratedOver_of_isRelativelySemiample`), and it passes to
pull-backs. -/
private def IsGeneratedOver {V X : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ X)
    (H : QDivisor V) : Prop :=
  ∃ (m₀ : ℕ) (_ : 0 < m₀) (W₀ : Divisor V) (F : X.Modules), _root_.SheafOfModules.IsCoherent F ∧
    (∀ P, (W₀.coeff P : ℚ) = m₀ * H.coeff P) ∧
    ∃ π : (Scheme.Modules.pullback f).obj F ⟶ W₀.divisorialSheaf, Epi π

/-- A *model* over `X`: the data and hypotheses of the theorem for a source `V`. -/
private structure Model (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) where
  V : Scheme.{0}
  sV : V ⟶ Spec (.of ℂ)
  proj : MMP.Mori.IsProjectiveVariety ℂ sV
  smooth : IsSmoothScheme sV
  [ln : IsLocallyNoetherian V]
  [nrm : IsNormal V]
  f : V ⟶ X
  hfs : f ≫ sX = sV
  hfp : IsProjective f
  n : ℕ
  K : Divisor V
  hK : K.IsCanonicalDivisor sV n
  B : QDivisor V
  hB : B.IsSNC sV
  hB0 : ∀ E, 0 ≤ B E
  hB1 : ∀ E, B E ≤ 1
  M : Divisor V
  hM : M.IsCartier
  hsa : IsGeneratedOver f (Divisor.toQDivisor M - (Divisor.toQDivisor K + B))

attribute [local instance] Model.ln Model.nrm

/-- The source of a model is integral. -/
private theorem Model.isIntegral {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} (m : Model X sX) :
    IsIntegral m.V :=
  haveI := m.proj
  ((AlgebraicGeometry.isProjectiveVariety_iff ℂ m.sV).1 ‹_›).1.toIsIntegral

attribute [local instance] Model.isIntegral

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- `x` is an associated point of `R^q f_* 𝒪_V(M)` for the model `m`. -/
private def Model.IsAss (m : Model X sX) (q : ℕ) (x : X) : Prop :=
  Stacks.Divisors.IsAssociatedPoint
    (((Scheme.Modules.pushforward m.f).rightDerived q).obj m.M.divisorialSheaf) x

/-- The strata of a model whose image lies in `Δ`. -/
private def Model.bad (m : Model X sX) (Δ : Set X) : Set (Set m.V) :=
  {S | MMP.Fourfold.IsSNCStratum m.B.roundDown S ∧ m.f.base '' S ⊆ Δ}

/-- In a Noetherian space the maximal irreducible subsets of a closed set are finite in
number. -/
private theorem finite_maximal_irreducible_subset {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] (C : Set Y) (hC : IsClosed C) :
    {S : Set Y | Maximal (fun T : Set Y => IsIrreducible T ∧ T ⊆ C) S}.Finite := by
  classical
  obtain ⟨F, hF, hCF⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible (⟨C, hC⟩ : TopologicalSpace.Closeds Y)
  refine ((F.image (fun k : TopologicalSpace.Closeds Y => (k : Set Y))).finite_toSet).subset ?_
  intro S hS
  have hCeq : C = ⋃₀ ((F.image (fun k : TopologicalSpace.Closeds Y => (k : Set Y)) :
      Finset (Set Y)) : Set (Set Y)) := by
    have := congrArg (fun s : TopologicalSpace.Closeds Y => (s : Set Y)) hCF
    rw [show C = ((⟨C, hC⟩ : TopologicalSpace.Closeds Y) : Set Y) from rfl, this]
    ext y
    simp [TopologicalSpace.Closeds.coe_finset_sup]
  obtain ⟨z, hz, hSz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hS.1.1)
    (F.image (fun k : TopologicalSpace.Closeds Y => (k : Set Y)))
    (by intro z hz; simp only [Finset.mem_image] at hz; obtain ⟨k, -, rfl⟩ := hz; exact k.2)
    (hCeq ▸ hS.1.2)
  simp only [Finset.mem_image] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hkC : (k : Set Y) ⊆ C := by
    rw [hCeq]
    exact Set.subset_sUnion_of_mem (by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨k, hk, rfl⟩)
  have : S = k := le_antisymm hSz (hS.2 ⟨hF ⟨k, hk⟩, hkC⟩ hSz)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨k, hk, this.symm⟩

/-- A maximal irreducible subset of a closed set is closed. -/
private theorem isClosed_of_maximal_irreducible_subset {Y : Type*} [TopologicalSpace Y]
    {C S : Set Y} (hC : IsClosed C)
    (hS : Maximal (fun T : Set Y => IsIrreducible T ∧ T ⊆ C) S) : IsClosed S := by
  have : closure S = S :=
    le_antisymm (hS.2 ⟨hS.1.1.closure, closure_minimal hS.1.2 hC⟩ subset_closure) subset_closure
  exact this ▸ isClosed_closure

/-- The source of a model is a Noetherian space. -/
private theorem Model.noetherianSpace (m : Model X sX) : TopologicalSpace.NoetherianSpace m.V := by
  haveI := m.proj
  haveI : IsProper m.sV := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := m.sV))).isProper
  haveI : CompactSpace m.V := QuasiCompact.compactSpace_of_compactSpace m.sV
  haveI : IsNoetherian m.V := ⟨⟩
  infer_instance

/-- The strata of an snc model are finite in number. -/
private theorem Model.finite_strata (m : Model X sX) :
    {S : Set m.V | MMP.Fourfold.IsSNCStratum m.B.roundDown S}.Finite := by
  classical
  haveI := m.noetherianSpace
  refine ((m.B.roundDown.support.powerset.finite_toSet).biUnion fun J _ =>
    finite_maximal_irreducible_subset (⋂ E ∈ J, (E.support : Set m.V))
      (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed)).subset ?_
  rintro S ⟨J, hJ, hS⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_powerset.2 hJ)) hS

/-- The image of a stratum is closed. -/
private theorem Model.isClosed_image_stratum (m : Model X sX) {S : Set m.V}
    (hS : MMP.Fourfold.IsSNCStratum m.B.roundDown S) : IsClosed (m.f.base '' S) := by
  haveI : IsProper m.f := m.hfp.isProper
  obtain ⟨J, -, hS⟩ := hS
  exact m.f.isClosedMap _ (isClosed_of_maximal_irreducible_subset
    (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed) hS)

/-- On an integral Noetherian normal scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (A : Y.CartierDivisor) :
    ∃ w : Divisor Y, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian Y := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (Y.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (Y.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- A projective variety carries a Cartier divisor whose sheaf is ample. -/
private theorem exists_isAmple_cartierSheaf {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsProjectiveVariety ℂ sY) :
    ∃ H : Y.CartierDivisor, Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf H) := by
  haveI : IsIntegral Y := hY.toIsIntegral
  obtain ⟨L, hL, hLa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hY
  obtain ⟨H, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  exact ⟨H, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp
    ((Stacks.AmpleBridge.isAmple_iff_isAmple Y L).mpr hLa)⟩

/-- `𝒪(n • H) ≅ 𝒪(H)^{⊗ n}`. -/
private theorem sheaf_nsmul_iso {Y : Scheme.{0}} (H : Y.CartierDivisor)
    [Stacks.Ample.IsInvertibleModule Y (MMP.CartierDivisor.sheaf H)] (n : ℕ) :
    Nonempty (MMP.CartierDivisor.sheaf (n • H) ≅
      Stacks.Ample.tensorPowModule Y (MMP.CartierDivisor.sheaf H) (n : ℤ)) := by
  induction n with
  | zero =>
    exact ⟨eqToIso (by rw [zero_nsmul]) ≪≫
      (MMP.CartierDivisor.unitIsoSheafZero Y).symm ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso Y _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (by rw [succ_nsmul]) ≪≫
      (MMP.CartierDivisorSheaf.sheafMulIso (n • H) H).symm ≪≫
      MMP.CartierDivisorSheaf.tensorIso e
        (Stacks.Ample.tensorPowModuleOneIso Y _).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso Y _ (n : ℤ) 1 ≪≫ eqToIso (by push_cast; rfl)⟩

open Opposite RingedSpaceModuleAdjunction in
/-- **Hypersurfaces through a point avoiding finitely many others.** On a projective variety
with an ample Cartier divisor `H`, for a point `x` and a finite set `T` of points not in
`closure {x}`, some effective `A` with `𝒪(A) ≅ 𝒪(aH)` passes through `x` and avoids `T`. The set
`T` is nonempty, so that the section cutting out `A` is nonzero. -/
private theorem exists_isEffective_mem_support {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (H : Y.CartierDivisor)
    (hH : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf H)) (x : Y)
    (T : Set Y) (hT : T.Finite) (hTne : T.Nonempty) (hTx : ∀ y ∈ T, y ∉ closure {x}) :
    ∃ (a : ℕ) (A : Y.CartierDivisor), MMP.Intersection.IsEffective A ∧
      Nonempty (MMP.CartierDivisor.sheaf A ≅
        MMP.CartierDivisor.sheaf (a • H)) ∧
      x ∈ MMP.Intersection.cartierSupport A ∧
      ∀ y ∈ T, y ∉ MMP.Intersection.cartierSupport A := by
  haveI : IsIntegral Y := hY.toIsIntegral
  set L := MMP.CartierDivisor.sheaf H
  haveI : Stacks.Ample.IsInvertibleModule Y L := inferInstance
  obtain ⟨n, -, s, -, hTs, hsW⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite
      (L := L) hH hT ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩ hTx
  have hnvT : ∀ y ∈ T, y ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s := fun y hy =>
    (Stacks.AmpleTheory.coe_powNonvanishingOpen Y L n s) ▸ hTs hy
  have hnvW : Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s ⊆ (closure {x})ᶜ := fun y hy =>
    hsW ((Stacks.AmpleTheory.coe_powNonvanishingOpen Y L n s).symm ▸ hy)
  have : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property (Stacks.Ample.tensorPowModule Y L (n : ℤ)) :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  obtain ⟨y₀, hy₀⟩ := hTne
  have hne0 : s ≠ 0 := by
    intro h
    have := hnvT y₀ hy₀
    rw [h, Stacks.Ample.mem_nonvanishingLocus_iff] at this
    exact this (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme Y (Stacks.Ample.tensorPowModule Y L (n : ℤ)) ((Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y _ _).2 hreg
  have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme (Stacks.Ample.tensorPowModule Y L (n : ℤ)) _ hne0'
  have hnv : Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s =
      (zeroScheme Y (Stacks.Ample.tensorPowModule Y L (n : ℤ)) ((Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤))).supportSetᶜ := by
    rw [← hcompl]
    conv_lhs => rw [← hevaltop]
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Y _
        (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s)]
    rfl
  obtain ⟨D, hD, hDZ⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hZc
  have h1 := MMP.CartierDivisor.coe_support_subscheme hD
  rw [hDZ] at h1
  obtain ⟨e⟩ := sheaf_nsmul_iso H n
  refine ⟨n, D, hD, ⟨MMP.CartierDivisor.sheafIsoInvertibleSheaf D hD ≪≫ eqToIso (by rw [hDZ]) ≪≫
    (invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg).symm ≪≫ e.symm⟩, ?_, ?_⟩
  · show x ∈ (MMP.Intersection.cartierSupport D : Set Y)
    rw [← h1]
    by_contra hx
    have hx' : x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s := by rwa [hnv]
    exact hnvW hx' (subset_closure rfl)
  · intro y hy hyD
    have hyD' : y ∈ (MMP.Intersection.cartierSupport D : Set Y) := hyD
    rw [← h1] at hyD'
    have := hnvT y hy
    rw [hnv] at this
    exact this hyD'

/-- The Weil divisor of the pull-back of an effective Cartier divisor is effective, and its
support lies over the support of the divisor. -/
private theorem nonneg_and_supp_subset_of_isWeilDivisorOfCartier_pullback {Y Y' : Scheme.{0}}
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] (g : Y' ⟶ Y) (A : Y.CartierDivisor)
    (hA : MMP.Intersection.IsEffective A)
    (hAg : ¬ Set.range g ⊆ MMP.Intersection.cartierSupport A) (D : Divisor Y')
    (hD : MMP.Intersection.IsWeilDivisorOfCartier
      (MMP.CartierDivisor.pullback g A hAg) D) :
    0 ≤ D ∧ (D.supp : Set Y') ⊆ g.base ⁻¹' MMP.Intersection.cartierSupport A := by
  have hEff : MMP.Intersection.IsEffective (MMP.CartierDivisor.pullback g A hAg) :=
    MMP.CartierDivisor.isEffective_pullback g hA hAg
  refine ⟨fun P => ?_, fun y hy => ?_⟩
  · exact (hD P).nonneg_of_isEffective hEff
  · obtain ⟨P, hP, hyP⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.1 hy
    have hsub : (MMP.Intersection.primeDivisorSubvariety P).support ⊆
        MMP.Intersection.cartierSupport (MMP.CartierDivisor.pullback g A hAg) := by
      by_contra h
      exact hP ((hD P).eq_zero_of_not_subset h)
    exact MMP.CartierDivisor.cartierSupport_pullback_subset g A hAg (hsub hyP)

/-! ### Twisting by an ample sheaf -/

section Twist

open Stacks.Ample Stacks.ProjectionFormula Limits Opposite MMP.Intersection

attribute [local instance] globalSec_additive globalSec_preservesFiniteLimits

/-- An invertible module is finite locally free. -/
private theorem isFiniteLocallyFree_of_isInvertibleModule {Y : Scheme.{0}} (E : Y.Modules)
    [IsInvertibleModule Y E] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} E := by
  have h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank E 1 :=
    (Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      Y.toRingedSpace E).1 ‹_›
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 1

/-- A module generated by its global sections, all of which vanish, is zero. -/
private theorem isZero_of_isGeneratedByGlobalSections {Y : Scheme.{0}} {F : Y.Modules}
    (hF : SheafOfModules.IsGeneratedByGlobalSections F)
    (h0 : ∀ s : (globalSec Y).obj F, s = 0) : IsZero F := by
  obtain ⟨σ⟩ := hF
  have hev : ∀ (i : σ.I) (V : Y.Opensᵒᵖ), (σ.s i).eval V = 0 := by
    intro i V
    have h1 : (σ.s i).eval (op ⊤) = 0 := h0 _
    have h2 := (σ.s i).2 (homOfLE (le_top : V.unop ≤ ⊤)).op
    refine h2.symm.trans ?_
    change F.val.map _ ((σ.s i).eval (op ⊤)) = 0
    rw [h1, map_zero]
  haveI := σ.epi
  have hid : 𝟙 F = 0 := by
    refine (cancel_epi (F.freeHomEquiv.symm σ.s)).1 ?_
    refine (SheafOfModules.freeHomEquiv_symm_comp σ.s _).trans
      (Eq.trans ?_ (SheafOfModules.freeHomEquiv_symm_comp σ.s _).symm)
    congr 1
    funext i
    apply Subtype.ext
    funext V
    change (𝟙 F : F ⟶ F).val.app V ((σ.s i).eval V) = (0 : F ⟶ F).val.app V ((σ.s i).eval V)
    rw [hev i V, map_zero, map_zero]
  exact (IsZero.iff_id_eq_zero F).2 hid

/-- A module whose twist by a power of an invertible module is zero is zero. -/
private theorem isZero_of_isZero_tensorPowModule {Y : Scheme.{0}} (L : Y.Modules)
    [IsInvertibleModule Y L] (n : ℤ) {F : Y.Modules}
    (h : IsZero ((tensorRightInvertible Y (tensorPowModule Y L n)).obj F)) : IsZero F := by
  haveI := isFiniteLocallyFree_of_isInvertibleModule (tensorPowModule Y L (-n))
  have e : F ≅ (tensorRightInvertible Y (tensorPowModule Y L (-n))).obj
      ((tensorRightInvertible Y (tensorPowModule Y L n)).obj F) :=
    (MonoidalCategory.rightUnitor F).symm ≪≫
      MonoidalCategory.whiskerLeftIso F ((tensorPowModuleZeroIso Y L).symm ≪≫
        eqToIso (by rw [add_neg_cancel]) ≪≫ (tensorPowModuleAddIso Y L n (-n)).symm) ≪≫
      (MonoidalCategory.associator F _ _).symm
  exact ((tensorRightInvertible Y (tensorPowModule Y L (-n))).map_isZero h).of_iso e

/-- **Detecting monomorphisms by twisting.** On a locally Noetherian scheme with an ample
invertible module `L`, a morphism `ψ` of coherent modules is a monomorphism as soon as, for
arbitrarily large `n`, it induces an injection on the global sections of the twists by `L^n`:
the kernel is coherent, so its large twists are generated by their global sections, which
vanish. -/
private theorem mono_of_injective_twist {Y : Scheme.{0}} [IsLocallyNoetherian Y] (L : Y.Modules)
    [IsInvertibleModule Y L] (hL : IsAmple Y L) {F G : Y.Modules} (ψ : F ⟶ G)
    (hF : _root_.SheafOfModules.IsCoherent F) (hG : _root_.SheafOfModules.IsCoherent G)
    (h : ∀ n₀ : ℤ, ∃ n, n₀ ≤ n ∧ Function.Injective ((globalSec Y).map
      ((tensorRightInvertible Y (tensorPowModule Y L n)).map ψ))) :
    Mono ψ := by
  haveI hK : _root_.SheafOfModules.IsCoherent (kernel ψ) :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules hF hG ψ
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      L hL).2 (kernel ψ) (_root_.isQuasicoherent_of_isCoherent (M := kernel ψ))
      (_root_.SheafOfModules.IsCoherent.isFiniteType (M := kernel ψ))
  obtain ⟨n, hn, hinj⟩ := h n₀
  haveI := isFiniteLocallyFree_of_isInvertibleModule (tensorPowModule Y L n)
  have hgg : _root_.SheafOfModules.IsGeneratedByGlobalSections
      ((tensorRightInvertible Y (tensorPowModule Y L n)).obj (kernel ψ)) :=
    Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules Y (kernel ψ) _) (hn₀ n hn)
  have hz : IsZero ((tensorRightInvertible Y (tensorPowModule Y L n)).obj (kernel ψ)) := by
    refine isZero_of_isGeneratedByGlobalSections hgg fun s => ?_
    have hm : Mono ((globalSec Y).map
        ((tensorRightInvertible Y (tensorPowModule Y L n)).map (kernel.ι ψ))) := by
      haveI : PreservesFiniteLimits (tensorRightInvertible Y (tensorPowModule Y L n)) :=
        Stacks.ProjectionFormula.preservesFiniteLimits_tensorRight_of_isFiniteLocallyFree Y _
      haveI : Mono ((tensorRightInvertible Y (tensorPowModule Y L n)).map (kernel.ι ψ)) :=
        Functor.map_mono _ _
      exact Functor.map_mono _ _
    have hc : (globalSec Y).map
        ((tensorRightInvertible Y (tensorPowModule Y L n)).map (kernel.ι ψ)) ≫
        (globalSec Y).map ((tensorRightInvertible Y (tensorPowModule Y L n)).map ψ) = 0 := by
      rw [← Functor.map_comp, ← Functor.map_comp, kernel.condition, Functor.map_zero,
        Functor.map_zero]
    have h1 := ConcreteCategory.congr_hom hc s
    rw [ConcreteCategory.comp_apply] at h1
    have h2 := hinj (h1.trans (map_zero _).symm)
    exact (AddCommGrpCat.mono_iff_injective _).1 hm (h2.trans (map_zero _).symm)
  have hK0 : IsZero (kernel ψ) := isZero_of_isZero_tensorPowModule L n hz
  refine Preadditive.mono_of_cancel_zero _ fun g hg => ?_
  rw [← kernel.lift_ι ψ g hg, hK0.eq_of_tgt (kernel.lift ψ g hg) 0, zero_comp]

open scoped Stacks.SmallDerivedModel in
/-- The projection formula, in the indexing of the right derived functors of `f_*`. -/
private noncomputable def projectionFormulaNatIso {V Y : Scheme.{0}} (f : V ⟶ Y)
    (E : Y.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} E] (q : ℕ) :
    haveI := Stacks.SchemeCohomology.pushforward_additive f
    tensorRightInvertible V ((Scheme.Modules.pullback f).obj E) ⋙
        (Scheme.Modules.pushforward f).rightDerived q ≅
      (Scheme.Modules.pushforward f).rightDerived q ⋙ tensorRightInvertible Y E :=
  haveI := Stacks.SchemeCohomology.pushforward_additive f
  Functor.isoWhiskerLeft _ (Stacks.DerivedIndexing.rightDerivedIso _ q) ≪≫
    Stacks.ProjectionFormula.higherDirectImageTensorRightFiniteLocallyFreeIso f E q ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso _ q).symm _

/-- A diagram chase: a morphism transported along isomorphisms through two commutative squares. -/
private theorem eq_comp_of_squares {C : Type*} [Category C] {SM SMP SM'P SM' X Y : C}
    (mul : SM ≅ X) (mul' : SM' ≅ Y) (a : SM ⟶ SMP) (b : SMP ⟶ SM'P) (c : SM'P ⟶ SM')
    (b₀ : SM ⟶ SM') (a' : SM' ⟶ SM'P) (incl : X ⟶ Y) (hsq : a ≫ b = b₀ ≫ a')
    (hac : a' ≫ c = 𝟙 _) (hnat : b₀ ≫ mul'.hom = mul.hom ≫ incl) :
    incl = mul.inv ≫ a ≫ b ≫ c ≫ mul'.hom := by
  rw [reassoc_of% hsq, reassoc_of% hac, hnat, Iso.inv_hom_id_assoc]

/-- Twisting the inclusion `𝒪_V(M) ⊆ 𝒪_V(M')` by `𝒪_V(N)` is the inclusion
`𝒪_V(M + N) ⊆ 𝒪_V(M' + N)`. -/
private theorem divisorialSheafInclusion_add_eq {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {M M' N : Divisor V} (h : M ≤ M') (hM : M.IsCartier)
    (hM' : M'.IsCartier) (hN : N.IsCartier) (P : V.Modules) (e : N.divisorialSheaf ≅ P) :
    Divisor.divisorialSheafInclusion (add_le_add h le_rfl : M + N ≤ M' + N) =
      (hM.divisorialSheafTensorIso hN).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
          V.toRingedSpace.IsSheaf⟩).obj M.divisorialSheaf).map e.hom ≫
        (tensorRightInvertible V P).map (Divisor.divisorialSheafInclusion h) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
          V.toRingedSpace.IsSheaf⟩).obj M'.divisorialSheaf).map e.inv ≫
        (hM'.divisorialSheafTensorIso hN).hom := by
  have hT : (tensorRightInvertible V P).map (Divisor.divisorialSheafInclusion h) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
        V.toRingedSpace.IsSheaf⟩).map (Divisor.divisorialSheafInclusion h)).app P := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
        V.toRingedSpace.IsSheaf⟩).map (Divisor.divisorialSheafInclusion h)).app P ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
        V.toRingedSpace.IsSheaf⟩).obj M'.divisorialSheaf).map (𝟙 P) = _
    exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have hsq := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
    V.toRingedSpace.IsSheaf⟩).map (Divisor.divisorialSheafInclusion h)).naturality e.hom
  refine eq_comp_of_squares _ _ _ _ _ _ _ _ ((congrArg (_ ≫ ·) hT).trans hsq)
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg _ e.hom_inv_id).trans (CategoryTheory.Functor.map_id _ _)))
    (MMP.Mori.Divisor.map_divisorialSheafInclusion_comp_divisorialSheafTensorMul h N)

/-- The square of `divisorialSheafInclusion_add_eq`, rearranged. -/
private theorem comp_eq_comp_of_eq {C : Type*} [Category C] {SM SMP SM'P SM' X Y : C}
    (mul : SM ≅ X) (mul' : SM' ≅ Y) (a : SM ⟶ SMP) (b : SMP ⟶ SM'P) (e' : SM' ≅ SM'P)
    (incl : X ⟶ Y) (h : incl = mul.inv ≫ a ≫ b ≫ e'.inv ≫ mul'.hom) :
    (mul.inv ≫ a) ≫ b = incl ≫ mul'.inv ≫ e'.hom := by
  rw [h]; simp

/-- Injectivity on global sections is invariant under isomorphism of arrows. -/
private theorem injective_of_arrow_iso {f g : Arrow AddCommGrpCat.{0}} (e : f ≅ g)
    (hf : Function.Injective f.hom) : Function.Injective g.hom := by
  have : g.hom = e.inv.left ≫ f.hom ≫ e.hom.right := by simp
  rw [this]
  have h1 : Function.Injective e.inv.left :=
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)
  have h2 : Function.Injective e.hom.right :=
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)
  intro x y hxy
  simp only [ConcreteCategory.comp_apply] at hxy
  exact h1 (hf (h2 hxy))

/-- **Twisting by a pulled-back module, on global sections of the direct images.** If
`𝒪_V(N) ≅ f^*E` with `E` finite locally free, injectivity of `Γ(R^q f_*(𝒪(M + N) ⊆ 𝒪(M' + N)))`
gives injectivity of `Γ(R^q f_*(𝒪(M) ⊆ 𝒪(M')) ⊗ E)`, by the projection formula. -/
private theorem injective_globalSec_twist {V Y : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] (f : V ⟶ Y) (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} E] (q : ℕ)
    {M M' N : Divisor V} (h : M ≤ M') (hM : M.IsCartier) (hM' : M'.IsCartier) (hN : N.IsCartier)
    (e : N.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj E)
    (hinj : Function.Injective ((globalSec Y).map
      (((Scheme.Modules.pushforward f).rightDerived q).map
        (Divisor.divisorialSheafInclusion (add_le_add h le_rfl : M + N ≤ M' + N))))) :
    Function.Injective ((globalSec Y).map ((tensorRightInvertible Y E).map
      (((Scheme.Modules.pushforward f).rightDerived q).map
        (Divisor.divisorialSheafInclusion h)))) := by
  haveI := Stacks.SchemeCohomology.pushforward_additive f
  set S := Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
    V.toRingedSpace.IsSheaf⟩
  have hw := comp_eq_comp_of_eq (hM.divisorialSheafTensorIso hN) (hM'.divisorialSheafTensorIso hN)
    ((S.obj M.divisorialSheaf).map e.hom)
    ((tensorRightInvertible V ((Scheme.Modules.pullback f).obj E)).map
      (Divisor.divisorialSheafInclusion h)) ((S.obj M'.divisorialSheaf).mapIso e) _
    (divisorialSheafInclusion_add_eq h hM hM' hN _ e)
  let α : Arrow.mk (Divisor.divisorialSheafInclusion (add_le_add h le_rfl : M + N ≤ M' + N)) ≅
      Arrow.mk ((tensorRightInvertible V ((Scheme.Modules.pullback f).obj E)).map
        (Divisor.divisorialSheafInclusion h)) :=
    Arrow.isoMk ((hM.divisorialSheafTensorIso hN).symm ≪≫ (S.obj M.divisorialSheaf).mapIso e)
      ((hM'.divisorialSheafTensorIso hN).symm ≪≫ (S.obj M'.divisorialSheaf).mapIso e) hw
  let β : Arrow.mk (((Scheme.Modules.pushforward f).rightDerived q).map
        ((tensorRightInvertible V ((Scheme.Modules.pullback f).obj E)).map
          (Divisor.divisorialSheafInclusion h))) ≅
      Arrow.mk ((tensorRightInvertible Y E).map
        (((Scheme.Modules.pushforward f).rightDerived q).map
          (Divisor.divisorialSheafInclusion h))) :=
    Arrow.isoMk ((projectionFormulaNatIso f E q).app _) ((projectionFormulaNatIso f E q).app _)
      ((projectionFormulaNatIso f E q).hom.naturality (Divisor.divisorialSheafInclusion h)).symm
  exact injective_of_arrow_iso
    ((globalSec Y).mapArrow.mapIso
      (((Scheme.Modules.pushforward f).rightDerived q).mapArrow.mapIso α ≪≫ β)) hinj

/-- The direct images of `𝒪_V(M + N)`, for `𝒪_V(N) ≅ f^*E`, are the twists by `E` of those of
`𝒪_V(M)`. -/
private noncomputable def rightDerivedTwistIso {V Y : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] (f : V ⟶ Y) (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} E] (q : ℕ)
    {M N : Divisor V} (hM : M.IsCartier) (hN : N.IsCartier)
    (e : N.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj E) :
    haveI := Stacks.SchemeCohomology.pushforward_additive f
    ((Scheme.Modules.pushforward f).rightDerived q).obj (M + N).divisorialSheaf ≅
      Stacks.RelativeVeryAmple.tensorModules Y
        (((Scheme.Modules.pushforward f).rightDerived q).obj M.divisorialSheaf) E :=
  haveI := Stacks.SchemeCohomology.pushforward_additive f
  ((Scheme.Modules.pushforward f).rightDerived q).mapIso
      ((hM.divisorialSheafTensorIso hN).symm ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toRingedSpace.presheaf,
          V.toRingedSpace.IsSheaf⟩).obj M.divisorialSheaf).mapIso e) ≪≫
    (projectionFormulaNatIso f E q).app M.divisorialSheaf

/-- The pull-back of a module generated by global sections is generated by global sections. -/
private theorem isGeneratedByGlobalSections_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    {M : Z.Modules} (h : _root_.SheafOfModules.IsGeneratedByGlobalSections M) :
    _root_.SheafOfModules.IsGeneratedByGlobalSections ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨σ⟩ := h
  let p : _root_.SheafOfModules.free σ.I ⟶ (Scheme.Modules.pullback f).obj M :=
    (_root_.SheafOfModules.pullbackObjFreeIso _ σ.I).inv ≫ (Scheme.Modules.pullback f).map σ.π
  have hm : Epi ((Scheme.Modules.pullback f).map σ.π) :=
    @Functor.map_epi _ _ _ _ _
      (Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction f))
      _ _ σ.π σ.epi
  haveI : Epi p := @epi_comp _ _ _ _ _ _ inferInstance _ hm
  have hp : Epi ((_root_.SheafOfModules.freeHomEquiv ((Scheme.Modules.pullback f).obj M)).symm
      ((_root_.SheafOfModules.freeHomEquiv ((Scheme.Modules.pullback f).obj M)) p)) := by
    rw [Equiv.symm_apply_apply]; infer_instance
  exact ⟨⟨σ.I, ((Scheme.Modules.pullback f).obj M).freeHomEquiv p, hp⟩⟩

private theorem isLocalEquationAt_zero_one (Z : Scheme.{0}) (x : Z) :
    MMP.Intersection.IsLocalEquationAt (0 : Z.CartierDivisor) x 1 :=
  ⟨⊤, trivial, 1, MMP.Intersection.isLocalEquationOn_one _, by simp⟩

private theorem isPullback_zero {Y Z : Scheme.{0}} (g : Y ⟶ Z) :
    MMP.Intersection.IsPullback g (0 : Z.CartierDivisor) 0 := by
  refine ⟨fun η _ => ?_, fun y => ⟨1, 1,
    ⟨1, isLocalEquationAt_zero_one _ _, MMP.Intersection.isFraction_one_one_one _⟩,
    ?_, ?_, 1, isLocalEquationAt_zero_one _ _, ?_⟩⟩
  · simp [MMP.Intersection.cartierSupport]
  · simp
  · simp
  · simpa only [map_one] using MMP.Intersection.isFraction_one_one_one y

private theorem realization_congr {Y : Scheme.{0}} {c c' : KCartierDivisor ℚ Y}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e; rfl

/-- A `ℚ`-divisor `Q` on a smooth projective variety with `nQ` integral and globally generated
is semiample over every proper map `g` to a variety. -/
private theorem isRelativelySemiample_of_isGeneratedByGlobalSections {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sY] (hsm : IsSmoothScheme sY)
    [IsLocallyNoetherian Y] [IsNormal Y] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sZ] (g : Y ⟶ Z) (hg : g ≫ sZ = sY) [IsProper g]
    (Q : QDivisor Y) (n : ℕ) (hn : 0 < n) (D' : Divisor Y)
    (hQ : ∀ P, (D'.coeff P : ℚ) = n * Q.coeff P)
    (hgg : _root_.SheafOfModules.IsGeneratedByGlobalSections D'.divisorialSheaf) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample g Q := by
  classical
  obtain ⟨E, hE⟩ := (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2
    Y (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm) D'
  obtain ⟨e⟩ := MMP.Intersection.IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf hE
  haveI : IsProper sY := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sY))).isProper
  have : AlgebraicGeometry.IsVariety ℂ sY :=
    ((AlgebraicGeometry.isProjectiveVariety_iff ℂ sY).1 inferInstance).1
  have hfree : IsRelativelyFreeCartier g E := by
    have h := MMP.Mori.isRelativelyFreeCartier_of_isGeneratedByGlobalSections_add_pullback
      (sY := sZ) (f := g) hg E (B := 0) (B' := 0)
      (isPullback_zero g) (by
        rw [add_zero]
        exact Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso e.symm hgg)
    exact h
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (MMP.Intersection.isOrderAlong_primeDivisorOrder E P).unique (hE P), hQ P]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    refine ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, ?_⟩
    rw [realization_congr hc _ (fun D => ⟨(Finsupp.single E (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
    exact hfree

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
private theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{0}}
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

/-- The global sections of `G` vanishing at `x`, as a `ℂ`-subspace. -/
private def vanishingSubspace {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (G : Y.Modules) (x : Y) :
    Submodule ℂ (AlgebraicGeometry.globalSectionsOverField ℂ sY G) where
  carrier := {s | (G.presheaf.Γgerm x).hom s ∈ Stacks.ModuleStalk.maximalSmul G x}
  add_mem' {a b} ha hb :=
    (fun (u v : Γ(G, ⊤))
        (hu : (G.presheaf.Γgerm x).hom u ∈ Stacks.ModuleStalk.maximalSmul G x)
        (hv : (G.presheaf.Γgerm x).hom v ∈ Stacks.ModuleStalk.maximalSmul G x) =>
      Eq.mpr (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul G x)
        (map_add (G.presheaf.Γgerm x).hom u v)) (Submodule.add_mem _ hu hv)) a b ha hb
  zero_mem' :=
    Eq.mpr (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul G x)
      (map_zero (G.presheaf.Γgerm x).hom)) (Submodule.zero_mem _)
  smul_mem' c s hs :=
    (fun (a : Γ(Y, ⊤)) (u : Γ(G, ⊤))
        (hu : (G.presheaf.Γgerm x).hom u ∈ Stacks.ModuleStalk.maximalSmul G x) =>
      Eq.mpr (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul G x)
        (Stacks.ModuleStalk.Γgerm_smul G x a u)) (Submodule.smul_mem _ _ hu))
      (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sY.appLE ⊤ ⊤ (by simp)).hom c) s hs

/-- **A section vanishing at none of finitely many points.** An invertible module over `ℂ`
generated by its global sections has a global section vanishing at none of finitely many given
points: the sections vanishing at a point form a proper subspace, and a vector space over an
infinite field is not a finite union of proper subspaces. -/
private theorem exists_subset_nonvanishingLocus {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (G : Y.Modules) [IsInvertibleModule Y G]
    (hG : _root_.SheafOfModules.IsGeneratedByGlobalSections G) (T : Set Y) (hT : T.Finite) :
    ∃ σ : Γ(G, ⊤), T ⊆ Stacks.Ample.nonvanishingLocus G σ := by
  haveI : Finite T := hT
  have hne : ∀ x : T, vanishingSubspace sY G x ≠ ⊤ := by
    intro x htop
    obtain ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks _
      (generatesStalks_id_of_isGeneratedByGlobalSections G hG) x
    have hmem : (show AlgebraicGeometry.globalSectionsOverField ℂ sY G from i) ∈
        vanishingSubspace sY G x := htop ▸ Submodule.mem_top
    rw [Stacks.ProjectiveFromSections.nvCover, Stacks.NonvanishingOpen.mem_nonvanishingOpen,
      Stacks.Ample.mem_nonvanishingLocus_iff] at hi
    exact hi hmem
  obtain ⟨σ, hσ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hne
  exact ⟨σ, fun x hx => hσ ⟨x, hx⟩⟩

open RingedSpaceModuleAdjunction in
/-- **The divisor of a section.** A global section `σ` of an invertible module `G` on an integral
normal Noetherian scheme, nonvanishing at the points of a nonempty set `T`, is the divisor of zeros
of an effective Cartier divisor `Z` with `𝒪(Z) ≅ G` whose support misses `T`. -/
private theorem exists_divisor_of_section {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (G : Y.Modules) [IsInvertibleModule Y G] (σ : Γ(G, ⊤))
    (T : Set Y) (hTne : T.Nonempty) (hT : T ⊆ nonvanishingLocus G σ) :
    ∃ Z : Divisor Y, 0 ≤ Z ∧ Z.IsCartier ∧ Nonempty (Z.divisorialSheaf ≅ G) ∧
      ∀ y ∈ T, y ∉ Z.supp := by
  have : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property G :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  obtain ⟨y₀, hy₀⟩ := hTne
  have hne0 : σ ≠ 0 := by
    intro h
    have := hT hy₀
    rw [h, mem_nonvanishingLocus_iff] at this
    exact this (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop G σ).eval (op ⊤) = σ :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ σ
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop G σ).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop G σ) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme Y G ((Stacks.SheafOfModules.sectionsOfTop G σ).eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y _ _).2 hreg
  have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme G _ hne0'
  have hnv : nonvanishingLocus G σ =
      (zeroScheme Y G ((Stacks.SheafOfModules.sectionsOfTop G σ).eval (op ⊤))).supportSetᶜ := by
    rw [← hcompl]
    conv_lhs => rw [← hevaltop]
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Y _
        (Stacks.SheafOfModules.sectionsOfTop G σ)]
    rfl
  obtain ⟨A, hA0, hAc, ⟨eA⟩, hAsupp⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor _ hZc
  refine ⟨A, hA0, hAc, ⟨eA ≪≫ (invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg).symm⟩,
    fun x hx hxA => ?_⟩
  have hxσ : x ∈ nonvanishingLocus G σ := hT hx
  rw [hnv] at hxσ
  obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hxA
  have hPpos : 0 < A P := lt_of_le_of_ne (hA0 P) (Ne.symm hP)
  exact hxσ ((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hxP).mem_closed
    (zeroScheme Y G ((Stacks.SheafOfModules.sectionsOfTop G σ).eval (op ⊤))).support.isClosed
    (hAsupp P hPpos))

/-- A `ℚ`-divisor semiample over `X` is generated over `X`: the realization `E₀` of a free
multiple is a quotient of `f^* f_* 𝒪(E₀)`, and `f_* 𝒪(E₀)` is coherent. -/
private theorem isGeneratedOver_of_isRelativelySemiample {V X : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsLocallyNoetherian X] (f : V ⟶ X)
    [IsProper f] {H : QDivisor V} (hH : MMP.Fourfold.QDivisor.IsRelativelySemiample f H) :
    IsGeneratedOver f H := by
  obtain ⟨C, hC, m, hm, hint, hfree⟩ := hH
  set G := MMP.CartierDivisor.sheaf (KCartierDivisor.realization ((m : ℚ) • C) hint)
  obtain ⟨W₀, hW₀⟩ := exists_isWeilDivisorOfCartier (KCartierDivisor.realization ((m : ℚ) • C) hint)
  obtain ⟨eW₀⟩ := hW₀.nonempty_sheaf_iso_divisorialSheaf
  haveI hG : _root_.SheafOfModules.IsCoherent G :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible V _
  have hep : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G) := hfree
  exact ⟨m, hm, W₀, (Scheme.Modules.pushforward f).obj G,
    ProperCoherenceWitness.isCoherent_pushforward f G,
    coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hW₀,
    (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app G ≫ eW₀.hom,
    @epi_comp _ _ _ _ _ _ hep _ inferInstance⟩

/-- **Semiampleness of a twisted relatively semiample divisor.** Let `f : V ⟶ X` be a proper
morphism from a smooth projective variety, `L` an ample invertible module on `X` and `H` a
`ℚ`-divisor semiample over `X`. For `n ≫ 0` and every divisor `N` with `𝒪_V(N) ≅ f^*L^n`, the
`ℚ`-divisor `H + N` is semiample, and it is `ℚ`-linearly equivalent to an effective
`ℚ`-divisor whose support misses any prescribed finite set of points. -/
private theorem exists_semiample_twist {V X : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    [MMP.Mori.IsProjectiveVariety ℂ sV] (hsm : IsSmoothScheme sV) [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] [IsLocallyNoetherian X] (f : V ⟶ X) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) {H : QDivisor V}
    (hH : IsGeneratedOver f H) (T : Set V) (hT : T.Finite) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ N : Divisor V,
      Nonempty (N.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj (tensorPowModule X L (n : ℤ))) →
      MMP.Fourfold.QDivisor.IsRelativelySemiample sV (H + Divisor.toQDivisor N) ∧
      ∃ D' : QDivisor V, 0 ≤ D' ∧ (H + Divisor.toQDivisor N).QLinearlyEquivalent D' ∧
        ∀ v ∈ T, v ∉ D'.supp := by
  classical
  haveI : IsIntegral V := ((AlgebraicGeometry.isProjectiveVariety_iff ℂ sV).1 ‹_›).1.toIsIntegral
  haveI : IsProper sV := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sV))).isProper
  have hcart : ∀ D : Divisor V, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨m, hm, W₀, F, hFcoh, hcoef, π, hπ⟩ := hH
  haveI := hFcoh
  obtain ⟨c₀, hc₀⟩ :=
    (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      L hL).2 F (_root_.isQuasicoherent_of_isCoherent (M := F))
      (_root_.SheafOfModules.IsCoherent.isFiniteType (M := F))
  refine ⟨c₀.toNat, fun n hn N ⟨eN⟩ => ?_⟩
  haveI := (hcart N).isInvertibleModule_divisorialSheaf
  -- `𝒪_V(m N) ≅ f^*L^{nm}`
  obtain ⟨eP⟩ := (hcart N).nonempty_tensorPowModule_iso_divisorialSheaf_zsmul m
  have emN : ((m : ℤ) • N).divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (tensorPowModule X L ((n : ℤ) * (m : ℤ))) :=
    eP.symm ≪≫ Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso V _ _ eN m ≪≫
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f _ m).symm ≪≫
      (Scheme.Modules.pullback f).mapIso
        (Stacks.RelativeVeryAmple.tensorPowModulePowIso X L (n : ℤ) m)
  -- `𝒪_V(W₀ + m N)` is generated by its global sections
  set c : ℤ := (n : ℤ) * (m : ℤ)
  have hc : c₀ ≤ c := by
    have : (n : ℤ) ≤ c := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hm)
    omega
  haveI := isFiniteLocallyFree_of_isInvertibleModule
    ((Scheme.Modules.pullback f).obj (tensorPowModule X L c))
  have hgg₁ : _root_.SheafOfModules.IsGeneratedByGlobalSections
      (Stacks.RelativeVeryAmple.tensorModules V ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj (tensorPowModule X L c))) :=
    Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso
      (Stacks.RelativeVeryAmple.pullbackTensorModulesIso f F _)
      (isGeneratedByGlobalSections_pullback f
        (Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso
          (Stacks.AmplePullbackPart1.tensorIsoTensorModules X F _) (hc₀ c hc)))
  have hepi : Epi ((tensorRightInvertible V ((Scheme.Modules.pullback f).obj
      (tensorPowModule X L c))).map π) := by
    haveI := hπ
    exact Functor.map_epi _ _
  have hgg₂ : _root_.SheafOfModules.IsGeneratedByGlobalSections _ :=
    ⟨@_root_.SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ hgg₁.some _ hepi⟩
  have hW : _root_.SheafOfModules.IsGeneratedByGlobalSections
      (W₀ + (m : ℤ) • N).divisorialSheaf :=
    Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso
      (Stacks.RelativeVeryAmple.tensorModulesMapIso V (Iso.refl _) emN.symm ≪≫
        ((hcart W₀).divisorialSheafTensorIso (hcart _))) hgg₂
  have hcoefW : ∀ P, ((W₀ + (m : ℤ) • N).coeff P : ℚ) =
      m * (H + Divisor.toQDivisor N).coeff P := fun P => by
    have h1 := hcoef P
    have h2 := Divisor.coeff_toQDivisor N P
    simp only [DivisorWithCoeffs.coeff_apply] at h1 h2 ⊢
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Int.cast_add,
      Int.cast_mul, h1, ← h2]
    push_cast; ring
  haveI : AlgebraicGeometry.IsVariety ℂ (𝟙 (Spec (.of ℂ))) := ⟨⟩
  refine ⟨isRelativelySemiample_of_isGeneratedByGlobalSections sV hsm (𝟙 (Spec (.of ℂ))) sV
    (Category.comp_id _) _ m hm _ hcoefW hW, ?_⟩
  haveI := (hcart (W₀ + (m : ℤ) • N)).isInvertibleModule_divisorialSheaf
  obtain ⟨σ, hσ⟩ := exists_subset_nonvanishingLocus sV _ hW (insert (genericPoint V) T)
    (hT.insert _)
  obtain ⟨Z, hZ0, -, ⟨eZ⟩, hZT⟩ :=
    exists_divisor_of_section _ σ _ ⟨_, Set.mem_insert _ _⟩ hσ
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso eZ
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨(m : ℚ)⁻¹ • Divisor.toQDivisor Z, fun P => ?_, ⟨m, hm, φ⁻¹, ?_⟩, fun v hv hvs => ?_⟩
  · have h2 := Divisor.coeff_toQDivisor Z P
    simp only [DivisorWithCoeffs.coeff_apply] at h2
    rw [Finsupp.smul_apply, smul_eq_mul, h2, Finsupp.coe_zero, Pi.zero_apply]
    have : (0 : ℚ) ≤ (Z P : ℚ) := by exact_mod_cast hZ0 P
    positivity
  · ext P
    have h1 := hcoef P
    have h2 := Divisor.coeff_toQDivisor N P
    have h3 := Divisor.coeff_toQDivisor Z P
    have h4 := Divisor.coeff_toQDivisor (principalDivisor φ⁻¹) P
    have h5 := congrArg (fun D : Divisor V => D.coeff P) hφ
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      PrimeDivisor.ord_inv] at h5 h4
    simp only [DivisorWithCoeffs.coeff_apply] at h1 h2 h3 h4 h5 ⊢
    rw [h4]
    simp only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply, h2, h3, smul_eq_mul]
      at h5 ⊢
    have h5' : ((Z P : ℤ) : ℚ) - ((W₀ P : ℚ) + (m : ℚ) * (N P : ℚ)) = (P.ord φ : ℚ) := by
      exact_mod_cast h5
    rw [h1] at h5'
    rw [zsmul_eq_mul]
    push_cast
    field_simp
    linarith
  · have : v ∈ Z.supp := by
      obtain ⟨P, hP, hvP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hvs
      refine DivisorWithCoeffs.mem_supp_iff.2 ⟨P, fun h0 => hP ?_, hvP⟩
      have h3 := Divisor.coeff_toQDivisor Z P
      simp only [DivisorWithCoeffs.coeff_apply] at h0 h3 ⊢
      rw [Finsupp.smul_apply, h3, h0]
      simp
    exact hZT v (Set.mem_insert_of_mem _ hv) this

end Twist

/-- **Relative injectivity for pulled-back hypersurfaces.** If `A` is an effective Cartier
divisor on `X` linearly equivalent to a multiple of an ample `H`, whose pull-back `D` contains no
stratum, then `R^q f_* 𝒪_V(M) ⟶ R^q f_* 𝒪_V(M + D)` is a monomorphism. -/
private theorem Model.mono_rightDerived_map_inclusion (m : Model X sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (q : ℕ) (H : X.CartierDivisor)
    (hH : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf H)) (a : ℕ)
    (A : X.CartierDivisor) (hA : MMP.Intersection.IsEffective A)
    (hAH : Nonempty (MMP.CartierDivisor.sheaf A ≅
      MMP.CartierDivisor.sheaf (a • H)))
    (hAf : ¬ Set.range m.f ⊆ MMP.Intersection.cartierSupport A)
    (D : Divisor m.V)
    (hD : MMP.Intersection.IsWeilDivisorOfCartier
      (MMP.CartierDivisor.pullback m.f A hAf) D)
    (hD0 : 0 ≤ D) (hDS : MMP.Fourfold.ContainsNoStratum m.B.roundDown (D.supp : Set m.V)) :
    Mono (((Scheme.Modules.pushforward m.f).rightDerived q).map
      (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hD0 : m.M ≤ m.M + D))) := by
  classical
  haveI := m.proj
  haveI : IsProper m.sV := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := m.sV))).isProper
  haveI : CompactSpace m.V := QuasiCompact.compactSpace_of_compactSpace m.sV
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX := hX
  haveI : IsProper sX := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sX))).isProper
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsProper m.f := m.hfp.isProper
  haveI := Stacks.SchemeCohomology.pushforward_additive m.f
  set L := MMP.CartierDivisor.sheaf H
  have hcart : ∀ D : Divisor m.V, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme m.smooth
  -- `𝒪_V(D) ≅ f^*L^a`
  obtain ⟨eD⟩ : Nonempty (D.divisorialSheaf ≅
      (Scheme.Modules.pullback m.f).obj (Stacks.Ample.tensorPowModule X L (a : ℤ))) := by
    obtain ⟨e1⟩ := hD.nonempty_sheaf_iso_divisorialSheaf
    obtain ⟨eA⟩ := hAH
    obtain ⟨eaH⟩ := sheaf_nsmul_iso H a
    exact ⟨e1.symm ≪≫ MMP.CartierDivisor.pullbackSheafIso m.f A hAf ≪≫
      (Scheme.Modules.pullback m.f).mapIso (eA ≪≫ eaH)⟩
  -- the direct images are coherent
  have hcoh : ∀ (j : ℕ) (M' : Divisor m.V), _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward m.f).rightDerived j).obj M'.divisorialSheaf) := by
    intro j M'
    haveI : M'.divisorialSheaf.IsCoherent :=
      @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible m.V _ _
        (hcart M').isInvertibleModule_divisorialSheaf
    exact Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
      ((@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward m.f) _
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) j).app _).symm
      (ProperCoherenceWitness.higherDirectImageIsCoherent m.V X m.f inferInstance inferInstance _
        inferInstance j)
  -- Serre vanishing for the twists of the direct images
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ j ≤ q, ∀ p, 0 < p →
      Limits.IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.RelativeVeryAmple.tensorModules X
        (((Scheme.Modules.pushforward m.f).rightDerived j).obj m.M.divisorialSheaf)
        (Stacks.Ample.tensorPowModule X L (d : ℤ)))) ∧
      Limits.IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.RelativeVeryAmple.tensorModules X
        (((Scheme.Modules.pushforward m.f).rightDerived j).obj (m.M + D).divisorialSheaf)
        (Stacks.Ample.tensorPowModule X L (d : ℤ)))) := by
    have hS : ∀ (j : ℕ) (M' : Divisor m.V), ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p →
        Limits.IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.RelativeVeryAmple.tensorModules X
          (((Scheme.Modules.pushforward m.f).rightDerived j).obj M'.divisorialSheaf)
          (Stacks.Ample.tensorPowModule X L (d : ℤ)))) := fun j M' =>
      haveI := hcoh j M'
      Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist sX _ L hH
    choose e he using hS
    refine ⟨∑ j ∈ Finset.range (q + 1), (e j m.M + e j (m.M + D)), fun d hd j hj p hp =>
      ⟨he j m.M d p ?_ hp, he j (m.M + D) d p ?_ hp⟩⟩
    · exact le_trans (le_trans (Nat.le_add_right _ _) (Finset.single_le_sum
        (f := fun j => e j m.M + e j (m.M + D)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))) hd
    · exact le_trans (le_trans (Nat.le_add_left _ _) (Finset.single_le_sum
        (f := fun j => e j m.M + e j (m.M + D)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))) hd
  -- a point on every stratum
  obtain ⟨T, hT, hTS⟩ : ∃ T : Set m.V, T.Finite ∧
      ∀ S, MMP.Fourfold.IsSNCStratum m.B.roundDown S → ∃ v ∈ T, v ∈ S := by
    have hne : ∀ S ∈ {S : Set m.V | MMP.Fourfold.IsSNCStratum m.B.roundDown S}, S.Nonempty :=
      fun S ⟨_, _, hS⟩ => hS.1.1.nonempty
    choose! v hv using hne
    exact ⟨v '' {S | MMP.Fourfold.IsSNCStratum m.B.roundDown S}, m.finite_strata.image _,
      fun S hS => ⟨v S, ⟨S, hS, rfl⟩, hv S hS⟩⟩
  obtain ⟨n₂, hn₂⟩ := exists_semiample_twist m.sV m.smooth m.f L hH m.hsa T hT
  refine mono_of_injective_twist L hH _ (hcoh q m.M) (hcoh q (m.M + D)) fun n₀ => ?_
  set n' : ℕ := n₀.toNat + d₀ + n₂ with hn'
  refine ⟨((a + n' : ℕ) : ℤ), by omega, ?_⟩
  -- a divisor `N'` with `𝒪_V(N') ≅ f^*L^{n'}`
  obtain ⟨N', ⟨eN'⟩⟩ : ∃ N' : Divisor m.V, Nonempty (N'.divisorialSheaf ≅
      (Scheme.Modules.pullback m.f).obj (Stacks.Ample.tensorPowModule X L (n' : ℤ))) := by
    haveI : SheafOfModules.IsInvertible m.V.presheaf m.V.ringCatSheaf.2
        ((Scheme.Modules.pullback m.f).obj (Stacks.Ample.tensorPowModule X L (n' : ℤ))) :=
      InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
    obtain ⟨E', ⟨eE'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
      ((Scheme.Modules.pullback m.f).obj (Stacks.Ample.tensorPowModule X L (n' : ℤ)))
    obtain ⟨N', hN'⟩ := exists_isWeilDivisorOfCartier E'
    obtain ⟨e2⟩ := hN'.nonempty_sheaf_iso_divisorialSheaf
    exact ⟨N', ⟨e2.symm ≪≫ eE'.symm⟩⟩
  -- `N = D + N'`, with `𝒪_V(N) ≅ f^*L^{a + n'}`
  have eN : (D + N').divisorialSheaf ≅ (Scheme.Modules.pullback m.f).obj
      (Stacks.Ample.tensorPowModule X L ((a + n' : ℕ) : ℤ)) :=
    ((hcart D).divisorialSheafTensorIso (hcart N')).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso m.V eD eN' ≪≫
      (Stacks.RelativeVeryAmple.pullbackTensorModulesIso m.f _ _).symm ≪≫
      (Scheme.Modules.pullback m.f).mapIso (Stacks.Ample.tensorPowModuleAddIso X L a n' ≪≫
        eqToIso (by push_cast; rfl))
  haveI := isFiniteLocallyFree_of_isInvertibleModule
    (Stacks.Ample.tensorPowModule X L ((a + n' : ℕ) : ℤ))
  refine injective_globalSec_twist m.f _ q (le_add_of_nonneg_right hD0) (hcart _) (hcart _)
    (hcart (D + N')) eN ?_
  have key : ∀ (B : Divisor m.V) (_ : B = m.M + (D + N') + D) (h : m.M + (D + N') ≤ B),
      Function.Injective ((globalSec X).map (((Scheme.Modules.pushforward m.f).rightDerived q).map
        (Divisor.divisorialSheafInclusion h))) := by
    intro B hB h
    subst hB
    set MN := m.M + (D + N')
    set H'' : QDivisor m.V := Divisor.toQDivisor MN - (Divisor.toQDivisor m.K + m.B) with hH''def
    have hH'' : H'' = (Divisor.toQDivisor m.M - (Divisor.toQDivisor m.K + m.B)) +
        Divisor.toQDivisor (D + N') := by
      simp only [hH''def, MN, map_add]; abel
    obtain ⟨hsemi, -⟩ := hn₂ (a + n') (by omega) (D + N') ⟨eN⟩
    obtain ⟨-, D', hD'0, hD'lin, hD'T⟩ := hn₂ n' (by omega) N' ⟨eN'⟩
    have hsemi' : MMP.Fourfold.QDivisor.IsRelativelySemiample m.sV H'' := hH'' ▸ hsemi
    have htH : ((1 : ℚ) • H'').QLinearlyEquivalent (Divisor.toQDivisor D + D') := by
      obtain ⟨k, hk, φ, hφ⟩ := hD'lin
      refine ⟨k, hk, φ, ?_⟩
      rw [← hφ, one_smul, hH'']
      congr 1
      simp only [map_add]
      abel
    have hD'S : MMP.Fourfold.ContainsNoStratum m.B.roundDown (D'.supp : Set m.V) :=
      fun S hS hSD => by
        obtain ⟨v, hvT, hvS⟩ := hTS S hS
        exact hD'T v hvT (hSD hvS)
    have hinjH :=
      MMP.Mori.injective_derivedCohomologyOverField_map_divisorialSheafInclusion_of_semiample
        m.sV m.smooth m.hK m.B m.hB m.hB0 m.hB1 H'' hsemi' MN
        (by rw [show Divisor.toQDivisor m.K + m.B + H'' = Divisor.toQDivisor MN by
          simp only [hH''def]; abel]) D hD0 D' hD'0 (t := 1) one_pos htH hDS hD'S q
    have hmonoH := mono_Hfunctor_map_of_injective m.sV q _ hinjH
    have hv₁ : ∀ j ≤ q, ∀ p : ℕ, 0 < p → Limits.IsZero (Hgroup X.ringCatSheaf ⊤ p
        (((Scheme.Modules.pushforward m.f).rightDerived j).obj MN.divisorialSheaf)) :=
      fun j hj p hp => (hd₀ (a + n') (by omega) j hj p hp).1.of_iso
        ((Hfunctor X.ringCatSheaf ⊤ p).mapIso
          (rightDerivedTwistIso m.f _ j (hcart m.M) (hcart (D + N')) eN))
    have hv₂ : ∀ j ≤ q, ∀ p : ℕ, 0 < p → Limits.IsZero (Hgroup X.ringCatSheaf ⊤ p
        (((Scheme.Modules.pushforward m.f).rightDerived j).obj (MN + D).divisorialSheaf)) :=
      fun j hj p hp => (hd₀ (a + n') (by omega) j hj p hp).2.of_iso
        ((Hfunctor X.ringCatSheaf ⊤ p).mapIso
          (((Scheme.Modules.pushforward m.f).rightDerived j).mapIso
            (eqToIso (congrArg Divisor.divisorialSheaf
              (show MN + D = (m.M + D) + (D + N') by simp only [MN]; abel))) ≪≫
          rightDerivedTwistIso m.f _ j (hcart (m.M + D)) (hcart (D + N')) eN))
    exact (AddCommGrpCat.mono_iff_injective _).1
      (mono_secF_map_rightDerived_of_mono m.f q _ hv₁ hv₂ hmonoH)
  exact key _ (by abel) _

/-! ### Multiplication by a local equation on higher direct images -/

section LocalEquation

open Opposite

/-- Restriction to an open of the base carries monomorphisms of higher direct images to
monomorphisms (Stacks 01E5). -/
private theorem mono_restrict_rightDerived {X V : Scheme.{0}} (f : V ⟶ X) (U : X.Opens) (q : ℕ)
    {F F' : V.Modules} (φ : F ⟶ F') (h : Mono (((Scheme.Modules.pushforward f).rightDerived q).map φ)) :
    Mono (((Scheme.Modules.pushforward (f ∣_ U)).rightDerived q).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map φ)) := by
  obtain ⟨e⟩ : Nonempty (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ U)).rightDerived q ≅
      (Scheme.Modules.pushforward f).rightDerived q ⋙ Scheme.Modules.restrictFunctor U.ι) :=
    ⟨Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso f U q⟩
  have hn : ((Scheme.Modules.pushforward (f ∣_ U)).rightDerived q).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map φ) ≫ e.hom.app F' =
      e.hom.app F ≫ (Scheme.Modules.restrictFunctor U.ι).map
        (((Scheme.Modules.pushforward f).rightDerived q).map φ) := e.hom.naturality φ
  have : Mono (e.hom.app F ≫ (Scheme.Modules.restrictFunctor U.ι).map
        (((Scheme.Modules.pushforward f).rightDerived q).map φ)) := by
    haveI : Mono (e.hom.app F) := (inferInstance : Mono (e.app F).hom)
    infer_instance
  rw [← hn] at this
  exact mono_of_mono _ (e.hom.app F')

/-- A monomorphism of sheaves of modules is injective on sections. -/
private theorem injective_app_of_mono {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ]
    (V : X.Opens) : Function.Injective (φ.app V) := by
  have : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  have : Mono (((Scheme.Modules.toPresheaf X).map φ).app (op V)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- If multiplication by a function `a` vanishing at an associated point `x` of `G` were a
monomorphism on `G|_U`, an element of the stalk annihilated by `𝔪_x` would die. -/
private theorem false_of_mono_smulEnd {X : Scheme.{0}} (G : X.Modules) {x : X}
    (hx : Stacks.Divisors.IsAssociatedPoint G x) (U : X.Opens) (hxU : x ∈ U) (a : Γ(X, U))
    (ha : X.presheaf.germ U x hxU a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hmono : Mono ((Scheme.smulEnd U.toScheme (U.topIso.inv a)).asHom.app (G.restrict U.ι))) :
    False := by
  obtain ⟨m, hm⟩ := Stacks.Divisors.isAssociatedPoint_iff_forall_smul_eq_zero_iff.1 hx
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := (hm 1).1 (smul_zero _)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)
  have ham : X.presheaf.germ U x hxU a • m = 0 := (hm _).2 ha
  obtain ⟨W, hxW, s, rfl⟩ := G.presheaf.germ_exist (x := x) m
  have hW' : x ∈ W ⊓ U := ⟨hxW, hxU⟩
  set a' : Γ(X, W ⊓ U) := X.presheaf.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op a
  set s' : Γ(G, W ⊓ U) := G.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s
  have h1 : G.presheaf.germ (W ⊓ U) x hW' (a' • s') = 0 := by
    have e := PresheafOfModules.germ_smul (R := X.presheaf) (M := G.val) x (W ⊓ U) hW' a' s'
    erw [e]
    have ga : X.presheaf.germ (W ⊓ U) x hW' a' = X.presheaf.germ U x hxU a :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have gs : G.presheaf.germ (W ⊓ U) x hW' s' = G.presheaf.germ W x hxW s :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [ga]
    erw [gs]
    exact ham
  obtain ⟨W'', hxW'', i1, i2, h2⟩ := G.presheaf.germ_eq x hW' hW' (a' • s') 0
    (by rw [h1, map_zero])
  rw [map_zero] at h2
  set V0 : U.toScheme.Opens := U.ι ⁻¹ᵁ W''
  have hV0 : U.ι ''ᵁ V0 ≤ W'' := U.ι.image_preimage_le W''
  have hxV0 : x ∈ U.ι ''ᵁ V0 := ⟨⟨x, hxU⟩, hxW'', rfl⟩
  have hV0W : U.ι ''ᵁ V0 ≤ W ⊓ U := hV0.trans (leOfHom i1)
  set σ : Γ(G, U.ι ''ᵁ V0) := G.presheaf.map (homOfLE hV0W).op s'
  let φt : G.restrict U.ι ⟶ G.restrict U.ι :=
    (Scheme.smulEnd U.toScheme (U.topIso.inv a)).asHom.app (G.restrict U.ι)
  haveI : Mono φt := hmono
  have hσ : φt.app V0 σ = 0 := by
    have hr : (X.presheaf.map (homOfLE hV0W).op a' : Γ(X, U.ι ''ᵁ V0)) • σ = 0 := by
      have := (G.map_smul (homOfLE hV0W) a' s').symm
      simp only [σ]
      erw [this]
      have hfac : (homOfLE hV0W).op = i1.op ≫ (homOfLE hV0).op := rfl
      rw [hfac, Functor.map_comp, CategoryTheory.comp_apply, h2, map_zero]
    refine Eq.trans ?_ hr
    change ((Scheme.smulEnd U.toScheme (U.topIso.inv a)).asHom.app (G.restrict U.ι)).val.app (op V0) σ = _
    simp only [Scheme.smulEnd]
    erw [Stacks.SheafOfModules.terminalSectionToEnd_apply]
    have e2 : ∀ r : Γ(U.toScheme, V0), r • (show Γ(G.restrict U.ι, V0) from σ) =
        ((U.ι.appIso V0).inv r) • σ := fun r => rfl
    refine (e2 _).trans (congrArg (fun r => r • σ) ?_)
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    show X.presheaf.map _ (X.presheaf.map _ a) = X.presheaf.map _ (X.presheaf.map _ a)
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp]
    erw [← Functor.map_comp]
    exact congrArg (fun h => ConcreteCategory.hom (X.presheaf.map h) a) (Subsingleton.elim _ _)
  have hσ0 : σ = 0 := injective_app_of_mono φt V0 (hσ.trans (map_zero _).symm)
  apply hm0
  have : G.presheaf.germ (U.ι ''ᵁ V0) x hxV0 σ = G.presheaf.germ W x hxW s := by
    simp only [σ, s']
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  rw [← this, hσ0, map_zero]
  rfl

/-- The germ at `x ∈ V` of the section `r` of `𝒦` over `V`, read in the function field, is `r`. -/
private theorem totalQuotientStalkToFunctionField_germ_functionFieldToK' {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] {V : Y.Opens} {x : Y} (hx : x ∈ V)
    (r : Y.functionField) :
    totalQuotientStalkToFunctionField x (Y.totalQuotientSheaf.presheaf.germ V x hx
      (MMP.CartierDivisorPullback.functionFieldToK V r)) = r := by
  have h := MMP.CartierDivisorSheaf.resK_ofFunctionField (X := Y) (le_top : V ≤ ⊤) r
  change totalQuotientStalkToFunctionField x (Y.totalQuotientSheaf.presheaf.germ V x hx
    (MMP.CartierDivisorSheaf.ofFunctionField V r)) = r
  rw [← h, MMP.CartierDivisorSheaf.resK, TopCat.Presheaf.germ_res_apply]
  exact MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField r x

open MMP.CartierDivisorPullback in
/-- A pulled-back regular local equation of `A` is a local equation of the Weil divisor of
`f^*A`. -/
private theorem isLocalEquation_of_isWeilDivisorOfCartier_pullback {Y Y' : Scheme.{0}} [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] (g : Y' ⟶ Y) (A : Y.CartierDivisor)
    (hAg : ¬ Set.range g ⊆ MMP.Intersection.cartierSupport A) {U : Y.Opens}
    {f : (Y.totalQuotientSheaf.obj.obj (op U))ˣ} (hloc : MMP.Intersection.IsLocalEquationOn A U f)
    (hU : g (genericPoint Y') ∈ U) {a : (Y.presheaf.stalk (g (genericPoint Y')))ˣ}
    (ha : IsGermUnit f hU a) (D : MMP.Mori.Divisor Y')
    (hD : MMP.Intersection.IsWeilDivisorOfCartier (MMP.CartierDivisor.pullback g A hAg) D) :
    D.IsLocalEquation (g ⁻¹ᵁ U)
      (Units.map MMP.Intersection.functionFieldToRationalFunctions.toMonoidHom
        (pullbackGerm g a)) := by
  have hpull := MMP.CartierDivisor.isLocalEquationOn_pullback g A hAg hloc hU ha
  intro E hE
  have hy := MMP.Intersection.genericPoint_mem_of_support_inter_nonempty E hE
  have hat : MMP.Intersection.IsLocalEquationAt (MMP.CartierDivisor.pullback g A hAg) E.genericPoint
      (Y'.totalQuotientSheaf.presheaf.germ (g ⁻¹ᵁ U) _ hy
        (functionFieldToK (g ⁻¹ᵁ U) (pullbackGerm g a : Y'.functionField))) :=
    ⟨g ⁻¹ᵁ U, hy, Units.map (functionFieldToK (g ⁻¹ᵁ U)).toMonoidHom (pullbackGerm g a), hpull, rfl⟩
  have h1 := MMP.Intersection.ord_eq_coeff_of_isLocalEquationAt hD E rfl hat
  erw [totalQuotientStalkToFunctionField_germ_functionFieldToK'] at h1
  rw [← h1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  exact (MMP.Intersection.evalFF_functionFieldToRationalFunctions E.component _).symm

/-- On an open where `χ` is multiplication by the rational function `ψ = g`, the restriction of
`χ` is multiplication by `g` followed by the inclusion. -/
private theorem restrict_map_eq_smulEnd {V : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    {D₁ D₃ : Divisor V} (ψ : (RationalFunctions V)ˣ)
    (χ : D₁.divisorialSheaf ⟶ D₃.divisorialSheaf)
    (hχ : ∀ (W : V.Opens) (h : D₁.divisorialSubmodule W) Z,
      (χ.app W h).1 Z = (ψ : RationalFunctions V) Z.1 * h.1 Z)
    (U' : V.Opens) (g : Γ(V, U'))
    (hg : ∀ (Z : irreducibleComponents V) (hZ : componentGenericPoint V Z ∈ U'),
      (ψ : RationalFunctions V) Z = V.presheaf.germ U' _ hZ g)
    (hle : D₁ ≤ D₃) :
    (Scheme.Modules.restrictFunctor U'.ι).map χ =
      (Scheme.smulEnd U'.toScheme (U'.topIso.inv g)).asHom.app _ ≫
        (Scheme.Modules.restrictFunctor U'.ι).map (Divisor.divisorialSheafInclusion hle) := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext h
  erw [Scheme.Modules.Hom.comp_app]
  have hW : ∀ r : Γ(U'.toScheme, W), r • (show Γ((D₁.divisorialSheaf).restrict U'.ι, W) from h) =
      ((U'.ι.appIso W).inv r) • (show D₁.divisorialSubmodule (U'.ι ''ᵁ W) from h) := fun r => rfl
  have hs : Scheme.Modules.Hom.app (show (D₁.divisorialSheaf).restrict U'.ι ⟶
      (D₁.divisorialSheaf).restrict U'.ι from (Scheme.smulEnd U'.toScheme (U'.topIso.inv g)).asHom.app
      ((D₁.divisorialSheaf).restrict U'.ι)) W h =
      (V.presheaf.map (homOfLE (U'.ι_image_le W)).op g) •
        (show D₁.divisorialSubmodule (U'.ι ''ᵁ W) from h) := by
    change ((Scheme.smulEnd U'.toScheme (U'.topIso.inv g)).asHom.app
      ((D₁.divisorialSheaf).restrict U'.ι)).val.app (op W) h = _
    simp only [Scheme.smulEnd]
    erw [Stacks.SheafOfModules.terminalSectionToEnd_apply]
    refine (hW _).trans (congrArg (fun r => r • (show D₁.divisorialSubmodule (U'.ι ''ᵁ W) from h)) ?_)
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    show V.presheaf.map _ (V.presheaf.map _ g) = _
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl
  refine Eq.trans ?_ (congrArg (fun y => (Scheme.Modules.Hom.app
    ((Scheme.Modules.restrictFunctor U'.ι).map (Divisor.divisorialSheafInclusion hle)) W) y) hs).symm
  apply Subtype.ext
  funext Z
  refine (hχ (U'.ι ''ᵁ W) (show D₁.divisorialSubmodule (U'.ι ''ᵁ W) from h) Z).trans ?_
  change _ = ((V.presheaf.map (homOfLE (U'.ι_image_le W)).op g •
    (show D₁.divisorialSubmodule (U'.ι ''ᵁ W) from h) : D₁.divisorialSubmodule (U'.ι ''ᵁ W)) :
      ToType ((rationalFunctionsPresheaf V).obj (op (U'.ι ''ᵁ W)))) Z
  rw [Submodule.coe_smul, rationalFunctions_smul_apply, TopCat.Presheaf.germ_res_apply,
    ← hg Z.1 ((U'.ι_image_le W) Z.2)]

/-- The pulled-back function on `f⁻¹ U` is the global function of the restricted morphism. -/
private theorem topIso_inv_app_eq_appTop {X V : Scheme.{0}} (f : V ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (f ⁻¹ᵁ U).topIso.inv (f.app U a) = (f ∣_ U).appTop (U.topIso.inv a) := by
  rw [Scheme.Hom.appTop, morphismRestrict_app]
  simp only [Scheme.Opens.topIso_inv, eqToHom_op]
  erw [CategoryTheory.comp_apply, ← CategoryTheory.comp_apply (X.presheaf.map _) (f.app _),
    Scheme.Hom.naturality, CategoryTheory.comp_apply]
  erw [← CategoryTheory.comp_apply (V.presheaf.map _) (V.presheaf.map _),
    ← Functor.map_comp]
  exact congrArg (fun h => ConcreteCategory.hom (V.presheaf.map h) (f.app U a)) (Subsingleton.elim _ _)

end LocalEquation

/-- **A hypersurface through `x` kills the torsion at `x`.** -/
private theorem Model.not_mono_rightDerived_map_inclusion (m : Model X sX) (q : ℕ) (x : X)
    (hx : m.IsAss q x) (A : X.CartierDivisor)
    (hA : MMP.Intersection.IsEffective A)
    (hxA : x ∈ MMP.Intersection.cartierSupport A)
    (hAf : ¬ Set.range m.f ⊆ MMP.Intersection.cartierSupport A)
    (D : Divisor m.V)
    (hD : MMP.Intersection.IsWeilDivisorOfCartier
      (MMP.CartierDivisor.pullback m.f A hAf) D) (hD0 : 0 ≤ D) :
    ¬ Mono (((Scheme.Modules.pushforward m.f).rightDerived q).map
      (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hD0 : m.M ≤ m.M + D))) := by
  classical
  intro hmono
  -- a regular local equation `s` of `A` on a neighbourhood `U` of `x`
  obtain ⟨U, hxU, s, hu, hloc⟩ := hA x
  have hloc' : MMP.Intersection.IsLocalEquationOn A _ hu.unit := hloc
  -- `x ∈ |A|`, so the germ of `s` at `x` is not a unit
  have hsx : X.presheaf.germ U x hxU s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hloc1 : MMP.Intersection.IsLocalEquationAt A x
        (MMP.Intersection.stalkToTotalQuotient x (hunit.unit : X.presheaf.stalk x)) := by
      refine ⟨U, hxU, hu.unit, hloc', ?_⟩
      rw [IsUnit.unit_spec, IsUnit.unit_spec]
      exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU X.toTotalQuotientSheaf.hom s).symm
    have h1 := hloc1.mul_units hunit.unit⁻¹
    rw [← map_mul, Units.mul_inv, map_one] at h1
    exact MMP.Intersection.notMem_cartierSupport_of_isLocalEquationAt_one h1 hxA
  set F := m.M.divisorialSheaf
  set G := ((Scheme.Modules.pushforward m.f).rightDerived q).obj F
  set V' : m.V.Opens := m.f ⁻¹ᵁ U
  set R := (Scheme.Modules.pushforward (m.f ∣_ U)).rightDerived q
  have hφ := mono_restrict_rightDerived m.f U q _ hmono
  obtain ⟨e⟩ : Nonempty (R.obj ((Scheme.Modules.restrictFunctor V'.ι).obj F) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj G) :=
    ⟨(Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso m.f U q).app F⟩
  -- it suffices that multiplication by `s` is a monomorphism on `R^q (f ∣_ U)_* (𝒪_V(M)|_{f⁻¹U})`
  suffices hS : Mono ((Scheme.smulEnd U.toScheme (U.topIso.inv s)).asHom.app
      (R.obj ((Scheme.Modules.restrictFunctor V'.ι).obj F))) by
    refine false_of_mono_smulEnd G hx U hxU s hsx ?_
    let φG : G.restrict U.ι ⟶ G.restrict U.ι :=
      (Scheme.smulEnd U.toScheme (U.topIso.inv s)).asHom.app (G.restrict U.ι)
    let φR : R.obj ((Scheme.Modules.restrictFunctor V'.ι).obj F) ⟶
        R.obj ((Scheme.Modules.restrictFunctor V'.ι).obj F) :=
      (Scheme.smulEnd U.toScheme (U.topIso.inv s)).asHom.app _
    haveI : Mono φR := hS
    have hn : e.hom ≫ φG = φR ≫ e.hom := (Scheme.smulEnd U.toScheme (U.topIso.inv s)).asHom.naturality e.hom
    have h1 : Mono (e.hom ≫ φG) := by rw [hn]; infer_instance
    have h2 : Mono (e.inv ≫ e.hom ≫ φG) := inferInstance
    rw [Iso.inv_hom_id_assoc] at h2
    exact h2
  by_cases hη : m.f (genericPoint m.V) ∈ U
  · haveI := m.proj
    haveI : IsProper m.sV := (IsProjectiveMorphism.isProjective
      (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := m.sV))).isProper
    haveI : CompactSpace m.V := QuasiCompact.compactSpace_of_compactSpace m.sV
    obtain ⟨a, ha⟩ := MMP.CartierDivisor.exists_isGermUnit_of_not_range_subset
      m.f A hAf hloc' hη
    have hψ := isLocalEquation_of_isWeilDivisorOfCartier_pullback m.f A hAf hloc hη ha D hD
    set ψ : (RationalFunctions m.V)ˣ :=
      Units.map MMP.Intersection.functionFieldToRationalFunctions.toMonoidHom
        (MMP.CartierDivisorPullback.pullbackGerm m.f a) with hψdef
    set M' : Divisor m.V := m.M + D - MMP.Mori.principalDivisor ψ
    set N : Divisor m.V := m.M ⊔ M'
    have hM' : ∀ E : MMP.Mori.PrimeDivisor m.V, (E.support ∩ V').Nonempty → M'.coeff E = m.M.coeff E := by
      intro E hE
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
        ← hψ E hE]
      ring
    have hN1 : ∀ E : MMP.Mori.PrimeDivisor m.V, (E.support ∩ V').Nonempty → M'.coeff E = N.coeff E :=
      fun E hE => by
        change _ = m.M E ⊔ M' E
        rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply, hM' E hE, sup_idem]
    have hN2 : ∀ E : MMP.Mori.PrimeDivisor m.V, (E.support ∩ V').Nonempty → m.M.coeff E = N.coeff E :=
      fun E hE => by
        change _ = m.M E ⊔ M' E
        rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply, hM' E hE, sup_idem]
    have hmul : ∀ E : MMP.Mori.PrimeDivisor m.V, (m.M + D).coeff E = M'.coeff E + E.ord ψ := fun E => by
      rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, sub_add_cancel]
    set φ := Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hD0 : m.M ≤ m.M + D)
    set ν := (Divisor.divisorialSheafMulIso ψ hmul).hom ≫
      Divisor.divisorialSheafInclusion (le_sup_right : M' ≤ N)
    haveI : IsIso ((Scheme.Modules.restrictFunctor V'.ι).map
        (Divisor.divisorialSheafInclusion (le_sup_right : M' ≤ N))) :=
      Divisor.isIso_restrict_divisorialSheafInclusion _ hN1
    haveI : IsIso ((Scheme.Modules.restrictFunctor V'.ι).map
        (Divisor.divisorialSheafInclusion (le_sup_left : m.M ≤ N))) :=
      Divisor.isIso_restrict_divisorialSheafInclusion _ hN2
    haveI : IsIso ((Scheme.Modules.restrictFunctor V'.ι).map ν) := by
      simp only [ν, Functor.map_comp]
      infer_instance
    -- on `f⁻¹ U` the rational function `ψ` is the regular function `f^* s`
    have hg : ∀ (Z : irreducibleComponents m.V) (hZ : componentGenericPoint m.V Z ∈ V'),
        (ψ : RationalFunctions m.V) Z = m.V.presheaf.germ V' _ hZ (m.f.app U s) := by
      intro Z hZ
      have ha' : a.val = X.presheaf.germ U _ hη s := by
        apply MMP.CartierDivisorPullback.stalkToTotalQuotient_injective X
        refine ha.trans ?_
        rw [IsUnit.unit_spec]
        exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hη X.toTotalQuotientSheaf.hom s).symm
      change m.V.presheaf.stalkSpecializes _ ((m.f.stalkMap (genericPoint m.V)) a.val) = _
      rw [ha', Scheme.Hom.germ_stalkMap_apply]
      erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    have hB := restrict_map_eq_smulEnd ψ (φ ≫ ν) (fun _ _ _ => rfl) V' (m.f.app U s) hg
      (le_sup_left : m.M ≤ N)
    rw [topIso_inv_app_eq_appTop] at hB
    have hm1 : Mono (R.map ((Scheme.Modules.restrictFunctor V'.ι).map (φ ≫ ν))) := by
      rw [Functor.map_comp, Functor.map_comp]
      infer_instance
    let τV : (Scheme.Modules.restrictFunctor V'.ι).obj F ⟶
        (Scheme.Modules.restrictFunctor V'.ι).obj F :=
      (Scheme.smulEnd V'.toScheme ((m.f ∣_ U).appTop (U.topIso.inv s))).asHom.app _
    have hB' : (Scheme.Modules.restrictFunctor V'.ι).map (φ ≫ ν) =
        τV ≫ (Scheme.Modules.restrictFunctor V'.ι).map
          (Divisor.divisorialSheafInclusion (le_sup_left : m.M ≤ N)) := hB
    rw [hB', Functor.map_comp] at hm1
    have hm2 : Mono (R.map τV) := mono_of_mono _ (R.map ((Scheme.Modules.restrictFunctor V'.ι).map
      (Divisor.divisorialSheafInclusion (le_sup_left : m.M ≤ N))))
    have hC := rightDerived_map_app_eq (Scheme.Modules.pushforward (m.f ∣_ U))
      (Scheme.smulEnd V'.toScheme ((m.f ∣_ U).appTop (U.topIso.inv s)))
      (Scheme.smulEnd U.toScheme (U.topIso.inv s))
      (fun N => pushforward_map_smulEnd (m.f ∣_ U) (U.topIso.inv s) N) q
      ((Scheme.Modules.restrictFunctor V'.ι).obj F)
    have hm3 : Mono (R.map ((Scheme.smulEnd V'.toScheme ((m.f ∣_ U).appTop (U.topIso.inv s))).asHom.app
        ((Scheme.Modules.restrictFunctor V'.ι).obj F))) := hm2
    rw [hC] at hm3
    exact hm3
  · -- `f⁻¹ U` is empty
    haveI : IsEmpty V'.toScheme := ⟨fun y => hη
      ((((genericPoint_spec m.V).specializes (Set.mem_univ y.1)).map
        m.f.base.hom.continuous).mem_open U.isOpen y.2)⟩
    have hz : Limits.IsZero (R.obj ((Scheme.Modules.restrictFunctor V'.ι).obj F)) :=
      R.map_isZero (Stacks.Duality.ProperOverField.isZero_modules_of_isEmpty _)
    exact hz.mono _

/-! ### The boundary cleanup -/

/-- Associated points are local: an isomorphism of the restrictions to an open `U ∋ x` carries
the associated points of one module in `U` to those of the other. -/
private theorem isAssociatedPoint_of_restrict_iso {Y : Scheme.{0}} {G G' : Y.Modules} {x : Y}
    (hx : Stacks.Divisors.IsAssociatedPoint G x) (U : Y.Opens) (hxU : x ∈ U)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj G ≅
      (Scheme.Modules.restrictFunctor U.ι).obj G') :
    Stacks.Divisors.IsAssociatedPoint G' x := by
  have h1 := (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff
    U.ι G ⟨x, hxU⟩).2 hx
  have h2 := (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr e
    ⟨x, hxU⟩).1 h1
  exact (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff
    U.ι G' ⟨x, hxU⟩).1 h2

/-- Modules on `V` isomorphic over the preimage of an open `U ∋ x` have the same associated point
`x` in their higher direct images (Stacks 01E5). -/
private theorem isAssociatedPoint_rightDerived_of_restrict_iso {V Y : Scheme.{0}} (f : V ⟶ Y)
    (q : ℕ) {F F' : V.Modules} (U : Y.Opens)
    (eV : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F ≅
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F') {x : Y} (hxU : x ∈ U)
    (hx : Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward f).rightDerived q).obj F) x) :
    Stacks.Divisors.IsAssociatedPoint (((Scheme.Modules.pushforward f).rightDerived q).obj F') x :=
  isAssociatedPoint_of_restrict_iso hx U hxU
    (((Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso f U q).app
        F).symm ≪≫
      ((Scheme.Modules.pushforward (f ∣_ U)).rightDerived q).mapIso eV ≪≫
      (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso f U q).app F')

/-- An associated point of a higher direct image lies in the image of the morphism. -/
private theorem mem_range_of_isAssociatedPoint_rightDerived {V Y : Scheme.{0}} (f : V ⟶ Y)
    (hcl : IsClosed (Set.range f.base)) (q : ℕ) (F : V.Modules) {x : Y}
    (hx : Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward f).rightDerived q).obj F) x) : x ∈ Set.range f.base := by
  by_contra hxr
  let U : Y.Opens := ⟨(Set.range f.base)ᶜ, hcl.isOpen_compl⟩
  haveI : IsEmpty (f ⁻¹ᵁ U).toScheme := ⟨fun y => y.2 ⟨y.1, rfl⟩⟩
  obtain ⟨e⟩ : Nonempty (((Scheme.Modules.pushforward (f ∣_ U)).rightDerived q).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj F)) :=
    ⟨(Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso f U q).app F⟩
  have hz : Limits.IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj F)) :=
    (((Scheme.Modules.pushforward (f ∣_ U)).rightDerived q).map_isZero
      (Stacks.Duality.ProperOverField.isZero_modules_of_isEmpty _)).of_iso e.symm
  exact false_of_mono_smulEnd _ hx U hxr 0 (by simp) (hz.mono _)

/-- The model obtained by subtracting a component `E` of `⌊B⌋` from `B` and from `M`. -/
private noncomputable def Model.subtract (m : Model X sX) (E : MMP.Mori.PrimeDivisor m.V)
    (hE : m.B E = 1) : Model X sX where
  V := m.V
  sV := m.sV
  proj := m.proj
  smooth := m.smooth
  f := m.f
  hfs := m.hfs
  hfp := m.hfp
  n := m.n
  K := m.K
  hK := m.hK
  B := m.B - Finsupp.single E 1
  hB := m.hB.of_support_subset fun P hP => by
    rw [Finsupp.mem_support_iff] at hP ⊢
    intro h0
    apply hP
    by_cases hPE : P = E
    · subst hPE; simp [hE]
    · simp [Finsupp.single_apply, Ne.symm hPE, h0]
  hB0 := fun P => by
    by_cases hPE : P = E
    · subst hPE; simp [hE]
    · simpa [Finsupp.single_apply, Ne.symm hPE] using m.hB0 P
  hB1 := fun P => by
    by_cases hPE : P = E
    · subst hPE; simp [hE]
    · simpa [Finsupp.single_apply, Ne.symm hPE] using m.hB1 P
  M := m.M - Finsupp.single E 1
  hM := MMP.Fourfold.isCartier_of_isSmoothScheme m.smooth _
  hsa := by
    have : Divisor.toQDivisor (m.M - Finsupp.single E 1) -
        (Divisor.toQDivisor m.K + (m.B - Finsupp.single E 1)) =
        Divisor.toQDivisor m.M - (Divisor.toQDivisor m.K + m.B) := by
      rw [map_sub]
      have : Divisor.toQDivisor (Finsupp.single E (1 : ℤ)) = Finsupp.single E (1 : ℚ) := by
        ext P
        have h := Divisor.coeff_toQDivisor (Finsupp.single E (1 : ℤ)) P
        rw [h]
        simp only [DivisorWithCoeffs.coeff_apply]
        by_cases hPE : P = E
        · subst hPE; simp
        · simp [Finsupp.single_apply, Ne.symm hPE]
      rw [this]; abel
    rw [this]; exact m.hsa

/-- The strata of the reduced boundary after subtracting a component `E` of `⌊B⌋` are strata
before, other than `E` itself. -/
private theorem isSNCStratum_of_sub_single {V : Scheme.{0}} [IsIntegral V] {B : QDivisor V}
    {E : MMP.Mori.PrimeDivisor V} (hE : B E = 1) {S : Set V}
    (hS : MMP.Fourfold.IsSNCStratum (B - Finsupp.single E 1).roundDown S) :
    MMP.Fourfold.IsSNCStratum B.roundDown S ∧ S ≠ (E.support : Set V) := by
  classical
  obtain ⟨J', hJ', hSm⟩ := hS
  have hcoef : ∀ P, (B - Finsupp.single E 1).roundDown P = ⌊B P - if P = E then 1 else 0⌋ := by
    intro P
    have h := DivisorWithCoeffs.coeff_roundDown (B - Finsupp.single E 1) P
    simp only [DivisorWithCoeffs.coeff_apply] at h
    rw [h, Finsupp.sub_apply, Finsupp.single_apply]
    by_cases hPE : P = E
    · subst hPE; simp
    · simp [hPE, Ne.symm hPE]
  have hEJ : E ∉ J' := fun hEJ => by
    have := hJ' hEJ
    rw [Finsupp.mem_support_iff, hcoef] at this
    simp [hE] at this
  have hJsub : J' ⊆ B.roundDown.support := fun P hP => by
    have := hJ' hP
    have hPE : P ≠ E := by rintro rfl; exact hEJ hP
    rw [Finsupp.mem_support_iff, hcoef, if_neg hPE, sub_zero] at this
    rw [Finsupp.mem_support_iff]
    have h := DivisorWithCoeffs.coeff_roundDown B P
    simp only [DivisorWithCoeffs.coeff_apply] at h
    rwa [h]
  refine ⟨⟨J', hJsub, hSm⟩, fun hSE => ?_⟩
  rcases J'.eq_empty_or_nonempty with hJ0 | ⟨P, hP⟩
  · subst hJ0
    have hSu : S = Set.univ := le_antisymm (Set.subset_univ _)
      (hSm.2 ⟨IrreducibleSpace.isIrreducible_univ V, fun _ _ => by simp⟩ (Set.subset_univ _))
    have hη : genericPoint V ∈ (E.support : Set V) := hSE ▸ hSu ▸ Set.mem_univ _
    have h1 : E.genericPoint = genericPoint V := by
      have hsp1 : E.genericPoint ⤳ genericPoint V := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hη
      exact (hsp1.antisymm ((genericPoint_spec V).specializes (Set.mem_univ _))).eq
    have hmax : IsMax (genericPoint V) := fun y _ =>
      (genericPoint_spec V).specializes (Set.mem_univ y)
    have h2 := E.coheight_genericPoint
    rw [h1, Order.coheight_eq_zero.2 hmax] at h2
    exact zero_ne_one h2
  · have hPE : P ≠ E := by rintro rfl; exact hEJ hP
    have hEP : (E.support : Set V) ⊆ P.support := by
      rw [← hSE]
      exact fun y hy => Set.mem_iInter₂.1 (hSm.1.2 hy) P hP
    exact hPE (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
      (hEP (MMP.Flips.primeDivisor_genericPoint_mem_support E))).symm

/-- **Subtracting a component of `⌊B⌋` mapped away from `x`.** -/
private theorem Model.isAss_subtract (m : Model X sX) {E : MMP.Mori.PrimeDivisor m.V}
    (hE : m.B E = 1) (q : ℕ) {x : X} (hx : m.IsAss q x)
    (hxE : x ∉ m.f.base '' (E.support : Set m.V)) : (m.subtract E hE).IsAss q x := by
  classical
  haveI : IsProper m.f := m.hfp.isProper
  have hcl : IsClosed (m.f.base '' (E.support : Set m.V)) :=
    m.f.isClosedMap _ E.idealSheaf.support.isClosed
  let U : X.Opens := ⟨(m.f.base '' (E.support : Set m.V))ᶜ, hcl.isOpen_compl⟩
  have hle : m.M - Finsupp.single E 1 ≤ m.M := fun P => by
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    have : (0 : ℤ) ≤ Finsupp.single E 1 P := by
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
    linarith
  haveI hiso : IsIso ((Scheme.Modules.restrictFunctor (m.f ⁻¹ᵁ U).ι).map
      (Divisor.divisorialSheafInclusion hle)) :=
    Divisor.isIso_restrict_divisorialSheafInclusion hle fun P hP => by
      have hPE : P ≠ E := by
        rintro rfl
        obtain ⟨y, hyP, hyU⟩ := hP
        exact hyU ⟨y, hyP, rfl⟩
      rw [DivisorWithCoeffs.coeff_sub]
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hPE]
  exact isAssociatedPoint_rightDerived_of_restrict_iso m.f q U
    (asIso ((Scheme.Modules.restrictFunctor (m.f ⁻¹ᵁ U).ι).map
      (Divisor.divisorialSheafInclusion hle))).symm hxE hx

/-- **Associated points across a morphism that is an isomorphism over `U`.** If `p` is an
isomorphism over `f⁻¹ U ∋ x` and `F'` agrees with `p^*F` there, then `x` is associated to
`R^q (p ≫ f)_* F'` when it is to `R^q f_* F`. -/
private theorem isAssociatedPoint_rightDerived_comp {V V' Y : Scheme.{0}} (f : V ⟶ Y)
    (p : V' ⟶ V) (q : ℕ) (U : Y.Opens) (hp : IsIso (p ∣_ f ⁻¹ᵁ U)) {F : V.Modules}
    [Stacks.Ample.IsInvertibleModule V F] {F' : V'.Modules}
    (eF : (Scheme.Modules.restrictFunctor ((p ≫ f) ⁻¹ᵁ U).ι).obj F' ≅
      (Scheme.Modules.restrictFunctor ((p ≫ f) ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback p).obj F))
    {x : Y} (hxU : x ∈ U)
    (hx : Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward f).rightDerived q).obj F) x) :
    Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward (p ≫ f)).rightDerived q).obj F') x := by
  haveI := hp
  let e := p ∣_ f ⁻¹ᵁ U
  let G := (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F
  let e1 : (Scheme.Modules.restrictFunctor ((p ≫ f) ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback p).obj F) ≅ (Scheme.Modules.pullback e).obj G :=
    (Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫
      (Scheme.Modules.pullbackComp _ _).app F ≪≫
      eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj F)
        (morphismRestrict_ι p (f ⁻¹ᵁ U)).symm) ≪≫
      ((Scheme.Modules.pullbackComp e (f ⁻¹ᵁ U).ι).app F).symm ≪≫
      (Scheme.Modules.pullback e).mapIso ((Scheme.Modules.restrictFunctorIsoPullback _).app F).symm
  have hcomp : (p ≫ f) ∣_ U = e ≫ f ∣_ U := morphismRestrict_comp p f U
  refine isAssociatedPoint_of_restrict_iso hx U hxU
    (((Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso f U q).app
      F).symm ≪≫
      ((Scheme.Modules.pushforward (f ∣_ U)).rightDerived q).mapIso
        (asIso ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app G) ≪≫
          (Scheme.Modules.pushforward e).mapIso (e1.symm ≪≫ eF.symm)) ≪≫
      ((Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso
        e (f ∣_ U) q).app _).symm ≪≫
      eqToIso (congrArg (fun φ => ((Scheme.Modules.pushforward φ).rightDerived q).obj
        ((Scheme.Modules.restrictFunctor ((p ≫ f) ⁻¹ᵁ U).ι).obj F')) hcomp.symm) ≪≫
      (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso (p ≫ f) U
        q).app F')

/-- **Members of an snc divisor through a point.** If `x` lies on the members of `J ⊆ Supp D` of
an snc divisor `D` and its local ring has dimension at most `|J|`, then the members of `Supp D`
through `x` are those of `J`: their local equations are distinct members of a regular system of
parameters at `x`. -/
private theorem mem_of_isSNC_of_ringKrullDim_le {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {R : Type*} [Zero R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY)
    {J : Finset (MMP.Mori.PrimeDivisor Y)} (hJ : J ⊆ D.support) {x : Y}
    (hxJ : ∀ E ∈ J, x ∈ (E.support : Set Y))
    (hdim : ringKrullDim (Y.presheaf.stalk x) ≤ J.card) {P : MMP.Mori.PrimeDivisor Y}
    (hP : P ∈ D.support) (hxP : x ∈ (P.support : Set Y)) : P ∈ J := by
  classical
  by_contra hPJ
  obtain ⟨n, z, j, hz, hj, -⟩ := hD.2 x
  have hn : (n : WithBot ℕ∞) ≤ J.card := hz.2 ▸ hdim
  have hn' : n ≤ J.card := by exact_mod_cast hn
  have hmem : ∀ E ∈ insert P J, E ∈ D.support ∧ x ∈ (E.support : Set Y) := by
    intro E hE
    rcases Finset.mem_insert.1 hE with rfl | hE
    · exact ⟨hP, hxP⟩
    · exact ⟨hJ hE, hxJ E hE⟩
  let g : {E : MMP.Mori.PrimeDivisor Y // E ∈ insert P J} →
      {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ x ∈ E.support} :=
    fun E => ⟨E.1, hmem E.1 E.2⟩
  have hinj : Function.Injective (fun E => j (g E)) := fun a b h => by
    have h1 : (g a).1 = (g b).1 := congrArg Subtype.val (hj h)
    exact Subtype.ext h1
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, Finset.card_insert_of_notMem hPJ, Fintype.card_fin] at this
  omega

/-- At a prime divisor `H` over which `g` is a local isomorphism, onto the generic point of the
prime divisor `G` below, the pull-back of a Cartier divisor has the coefficient of `G`. -/
private theorem coeff_pullback_eq_of_isIso_stalkMap {Y Y' : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    [CompactSpace Y'] (g : Y' ⟶ Y) [IsDominant g] {D : Divisor Y} (hDc : D.IsCartier)
    (hD : ∀ Z : irreducibleComponents Y', g (componentGenericPoint Y' Z) ∉ D.supp)
    (H : MMP.Mori.PrimeDivisor Y') (G : MMP.Mori.PrimeDivisor Y)
    (heq : g H.genericPoint = G.genericPoint) [IsIso (g.stalkMap H.genericPoint)] :
    (D.pullback hDc hD).coeff H = D.coeff G := by
  obtain ⟨U, hU, φ, hφ⟩ := hDc G.genericPoint
  have hE : (H.support ∩ g ⁻¹ᵁ U).Nonempty :=
    ⟨H.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support H,
      show g H.genericPoint ∈ U from heq ▸ hU⟩
  rw [Divisor.isPullback_pullback hDc hD U φ hφ H hE,
    hφ G ⟨G.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support G, hU⟩]
  have hZ := H.map_componentGenericPoint_mem g hE
  have hW : g (componentGenericPoint Y' H.component) ∈ G.component.1 := by
    have h2 : (G.component : Set Y) = Set.univ := by
      have h1 : (G.component : Set Y) ∈ irreducibleComponents Y := G.component.2
      exact Set.eq_univ_of_univ_subset
        (h1.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))
    show _ ∈ (G.component : Set Y)
    rw [h2]; trivial
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZ (hD H.component) hW
  rw [pullbackComponent_eq hD hφ hZ hW a ha]
  exact MMP.Positivity.ordUnit_stalkMap_eq_ord H G heq φ hW a ha

/-- **One step of the boundary cleanup, for a stratum of codimension at least two.** The
stratum is blown up and the exceptional divisor subtracted. -/
private theorem Model.exists_step_blowUp (m : Model X sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (q : ℕ) (x : X) (hx : m.IsAss q x)
    (Δ : Set X) (hΔ : IsClosed Δ) (hxΔ : x ∉ Δ) (T : Set m.V)
    (J : Finset (MMP.Mori.PrimeDivisor m.V)) (hJ : J ⊆ m.B.roundDown.support) (hJ2 : 2 ≤ J.card)
    (hTm : Maximal (fun T : Set m.V => IsIrreducible T ∧
      T ⊆ ⋂ E ∈ J, (E.support : Set m.V)) T) (hTΔ : m.f.base '' T ⊆ Δ) :
    ∃ m' : Model X sX, m'.IsAss q x ∧ (m'.bad Δ).ncard < (m.bad Δ).ncard ∧
      ∀ S', MMP.Fourfold.IsSNCStratum m'.B.roundDown S' →
        ∃ S, MMP.Fourfold.IsSNCStratum m.B.roundDown S ∧ m'.f.base '' S' = m.f.base '' S := by
  classical
  haveI := m.proj
  haveI : IsProper m.f := m.hfp.isProper
  haveI hVvar : AlgebraicGeometry.IsVariety ℂ m.sV :=
    ((AlgebraicGeometry.isProjectiveVariety_iff ℂ m.sV).1 m.proj).1
  haveI : IsProper m.sV := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := m.sV))).isProper
  haveI : CompactSpace m.V := QuasiCompact.compactSpace_of_compactSpace m.sV
  -- the family of components of `Supp B`
  let S : {P : MMP.Mori.PrimeDivisor m.V // P ∈ m.B.support} → MMP.Mori.PrimeDivisor m.V :=
    Subtype.val
  have hS : Function.Injective S := Subtype.val_injective
  have hJB : ∀ E ∈ J, E ∈ m.B.support := fun E hE => by
    have := hJ hE
    rw [Finsupp.mem_support_iff] at this ⊢
    intro h0
    apply this
    have h := DivisorWithCoeffs.coeff_roundDown m.B E
    simp only [DivisorWithCoeffs.coeff_apply] at h
    rw [h, h0, Int.floor_zero]
  have hSNC : DivisorWithCoeffs.IsSNC m.sV (∑ j, Finsupp.single (S j) (1 : ℤ)) := by
    refine m.hB.of_support_subset fun P hP => ?_
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hP)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hj)]
    exact j.2
  let J' : Finset {P : MMP.Mori.PrimeDivisor m.V // P ∈ m.B.support} :=
    Finset.univ.filter (fun j => j.1 ∈ J)
  have hJ'card : J'.card = J.card :=
    Finset.card_bij (fun j _ => j.1) (fun j hj => (Finset.mem_filter.1 hj).2)
      (fun a _ b _ h => Subtype.ext h)
      (fun E hE => ⟨⟨E, hJB E hE⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hE⟩, rfl⟩)
  have hinter : (⋂ j ∈ J', ((S j).support : Set m.V)) = ⋂ E ∈ J, (E.support : Set m.V) := by
    ext y
    simp only [Set.mem_iInter, J', S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h E hE => h ⟨E, hJB E hE⟩ hE, fun h j hj => h j.1 hj⟩
  let W : MMP.Resolution.componentsOf (⋂ j ∈ J', ((S j).support : Set m.V)) :=
    ⟨T, hinter ▸ hTm⟩
  obtain ⟨hZ, hcodim, hsm', hisoU, E, S', hE, hEsm, hS'tr, hS'inj, hS'E, hsnc', himg, -⟩ :=
    MMP.Resolution.blowUp_snc_stratum m.sV hVvar m.smooth S hS hSNC J' (hJ'card ▸ hJ2) W
  generalize hIdef : MMP.Resolution.componentsFamily (⋂ j ∈ J', ((S j).support : Set m.V)) W = I
    at *
  have hTcl : IsClosed T := isClosed_of_maximal_irreducible_subset
    (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed) hTm
  have hIsupp : (I.support : Set m.V) = T := by
    rw [← hIdef, MMP.Resolution.componentsFamily, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hTcl.closure_eq
  have hirr : IsIrreducible (I.support : Set m.V) := hIsupp ▸ hTm.1.1
  have hc : (J.card : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ :
      TopologicalSpace.IrreducibleCloseds m.V) := by
    rw [← MMP.Mori.closedsCodimension_coe, ← hJ'card, ← hcodim]
    congr 1
    ext1
    change closure (W : Set m.V) = (I.support : Set m.V)
    rw [hIsupp]
    exact hTcl.closure_eq
  obtain ⟨hV'var, hV'sm, hpproj, hpbir, hpiso, hpv, -, -, -, E₂, hE₂, hcan⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_canonicalDivisor_picardGroup m.sV
      hVvar I ⟨m.smooth, hZ⟩ hirr hc hJ2
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ :
      TopologicalSpace.IrreducibleCloseds m.V) := hc ▸ by exact_mod_cast le_trans (by norm_num) hJ2
  have hEE : E₂ = E := MMP.Mori.PrimeDivisor.ext_idealSheaf (hE₂.trans hE.symm)
  subst hEE
  haveI : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  haveI : IsDominant (blowUpToBase I) := MMP.Threefold.Resolution.isDominant_blowUpToBase I hirr hc1
  haveI : Smooth (blowUpToBase I ≫ m.sV) := hV'sm
  haveI : IsLocallyNoetherian (blowUp I) :=
    MMP.Resolution.isLocallyNoetherian_of_smooth (blowUpToBase I ≫ m.sV)
  haveI : IsNormal (Spec (.of ℂ)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal (blowUp I) := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ m.sV)
  haveI hV'proj := hpv m.proj
  haveI : CompactSpace (blowUp I) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I ≫ m.sV)
  have hV'smooth : IsSmoothScheme (blowUpToBase I ≫ m.sV) := hsm'
  have hcart' : ∀ D : Divisor (blowUp I), D.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hV'smooth
  -- points off the centre
  have hEsupp : (E₂.support : Set (blowUp I)) = blowUpToBase I ⁻¹' T := by
    change (E₂.idealSheaf.support : Set (blowUp I)) = _
    rw [hE, Scheme.IdealSheafData.support_comap, ← hIsupp]
    rfl
  have hdown : ∀ H : MMP.Mori.PrimeDivisor (blowUp I), H ≠ E₂ →
      ∃ G : MMP.Mori.PrimeDivisor m.V, blowUpToBase I H.genericPoint = G.genericPoint ∧
        G.genericPoint ∉ T ∧ IsIso ((blowUpToBase I).stalkMap H.genericPoint) := by
    intro H hH
    have hnot : blowUpToBase I H.genericPoint ∉ (I.support : Set m.V) := fun hmem =>
      hH (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
        (by rwa [hEsupp, ← hIsupp]))
    have hcoh : Order.coheight (blowUpToBase I H.genericPoint) = 1 := by
      rw [MMP.Fourfold.SNCWeight.StratumBlowup.coheight_map_eq I hnot]
      exact H.coheight_genericPoint
    refine ⟨MMP.Fourfold.SNCWeight.StratumBlowup.primeOfCoheightOne _ hcoh,
      (MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_primeOfCoheightOne _ _).symm, ?_, ?_⟩
    · rw [MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_primeOfCoheightOne, ← hIsupp]
      exact hnot
    · exact MMP.isIso_stalkMap_of_mem_biregularLocus _
        (MMP.Fourfold.SNCWeight.StratumBlowup.mem_biregularLocus_of_notMem I hnot)
  obtain ⟨E₀, -⟩ := Finset.card_pos.1 (by omega : 0 < J.card)
  haveI : Nonempty (MMP.Mori.PrimeDivisor m.V) := ⟨E₀⟩
  choose! dn hdn using hdown
  -- the generic point of `T` has local dimension `|J|`
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hTm.1.1 hTcl
  have hξcoh : Order.coheight ξ = J.card := by
    have heq : (⟨I.support, hirr, I.support.isClosed⟩ : TopologicalSpace.IrreducibleCloseds m.V) =
        TopologicalSpace.IrreducibleCloseds.closureSingleton ξ := by
      ext1; change (I.support : Set m.V) = closure {ξ}; rw [hIsupp, hξ.def]
    rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton] at hc
    exact hc.symm
  -- the generic points of prime divisors are off `T`
  have hgenT : ∀ G : MMP.Mori.PrimeDivisor m.V, G.genericPoint ∉ T := by
    intro G hG
    have hsp : ξ ⤳ G.genericPoint := by
      rwa [specializes_iff_mem_closure, hξ.def]
    have h1 : Order.coheight ξ ≤ Order.coheight G.genericPoint := Order.coheight_anti hsp
    rw [hξcoh, G.coheight_genericPoint] at h1
    have : (J.card : ℕ∞) ≤ 1 := h1
    have : J.card ≤ 1 := by exact_mod_cast this
    omega
  -- the strict transforms lie over the components
  have hS'gen : ∀ j, blowUpToBase I (S' j).genericPoint = (S j).genericPoint := by
    intro j
    have hnot : (S j).genericPoint ∉ (I.support : Set m.V) := hIsupp ▸ hgenT (S j)
    obtain ⟨y, hy⟩ := MMP.Fourfold.SNCWeight.StratumBlowup.exists_preimage_of_notMem I hnot
    have hsupp := MMP.Mori.support_inverseTransformPrimeDivisor (hS'tr j)
    have hyS' : y ∈ ((S' j).support : Set (blowUp I)) := by
      rw [hsupp]
      refine MMP.Mori.preimage_subset_inverseTransform _ _ ⟨?_, ?_⟩
      · rw [hy]; exact MMP.Flips.primeDivisor_genericPoint_mem_support (S j)
      · rw [hy]; exact MMP.Fourfold.SNCWeight.StratumBlowup.mem_biregularLocus_of_notMem I hnot
    have hsp1 : (S' j).genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hyS'
    have hsp2 : blowUpToBase I (S' j).genericPoint ⤳ (S j).genericPoint :=
      hy ▸ hsp1.map (blowUpToBase I).base.hom.continuous
    have hmemS : blowUpToBase I (S' j).genericPoint ∈ ((S j).support : Set m.V) := by
      have h1 : ((S' j).support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (S j).support := by
        rw [hsupp]
        refine (IsClosed.closure_subset_iff ((S j).idealSheaf.support.isClosed.preimage
          (blowUpToBase I).base.hom.continuous)).2 fun z hz => hz.1
      exact h1 (MMP.Flips.primeDivisor_genericPoint_mem_support (S' j))
    have hsp3 : (S j).genericPoint ⤳ blowUpToBase I (S' j).genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hmemS
    exact (hsp2.antisymm hsp3).eq
  -- a non-exceptional prime over a component of `B` is its strict transform
  have hdnS : ∀ H, H ≠ E₂ → ∀ j, dn H = S j → H = S' j := by
    intro H hH j hj
    have h1 : blowUpToBase I H.genericPoint = blowUpToBase I (S' j).genericPoint := by
      rw [(hdn H hH).1, hj, hS'gen]
    have hnot : blowUpToBase I H.genericPoint ∉ (I.support : Set m.V) := by
      rw [(hdn H hH).1, hIsupp]; exact (hdn H hH).2.1
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.SNCWeight.StratumBlowup.eq_of_map_eq_of_notMem I hnot h1)
  have hdnS' : ∀ j, dn (S' j) = S j := by
    intro j
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hdn (S' j) (hS'E j)).1.symm.trans (hS'gen j))
  -- the pulled-back semiample `ℚ`-divisor
  obtain ⟨Q', hQ'semi, hQ'coeff⟩ : ∃ Q' : QDivisor (blowUp I),
      IsGeneratedOver (blowUpToBase I ≫ m.f) Q' ∧
      ∀ H, H ≠ E₂ → Q'.coeff H =
        (Divisor.toQDivisor m.M - (Divisor.toQDivisor m.K + m.B)).coeff (dn H) := by
    obtain ⟨m₀, hm₀, W₀, F, hFcoh, hcoef, π, hπ⟩ := m.hsa
    have hW₀c := MMP.Fourfold.isCartier_of_isSmoothScheme m.smooth W₀
    have hgen := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (blowUpToBase I) W₀
    have hm₀' : (m₀ : ℚ) ≠ 0 := by exact_mod_cast hm₀.ne'
    obtain ⟨e⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hW₀c (blowUpToBase I) hgen
    refine ⟨((m₀ : ℚ)⁻¹) • Divisor.toQDivisor (W₀.pullback hW₀c hgen),
      ⟨m₀, hm₀, W₀.pullback hW₀c hgen, F, hFcoh, fun P => ?_,
        (Scheme.Modules.pullbackComp (blowUpToBase I) m.f).inv.app F ≫
          (Scheme.Modules.pullback (blowUpToBase I)).map π ≫ e.inv, ?_⟩, fun H hH => ?_⟩
    · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
      field_simp
    · haveI := hπ
      haveI : Epi ((Scheme.Modules.pullback (blowUpToBase I)).map π) := Functor.map_epi _ _
      haveI : Epi ((Scheme.Modules.pullbackComp (blowUpToBase I) m.f).inv.app F) :=
        (inferInstance : Epi ((Scheme.Modules.pullbackComp (blowUpToBase I) m.f).app F).inv)
      exact epi_comp _ _
    · haveI := (hdn H hH).2.2
      rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
        coeff_pullback_eq_of_isIso_stalkMap (blowUpToBase I) hW₀c hgen H (dn H) (hdn H hH).1,
        hcoef, smul_eq_mul]
      field_simp
  -- the canonical divisor
  obtain ⟨hK', -⟩ := hcan m.n m.K m.hK
  set K' := m.K.pullback (MMP.Fourfold.isCartier_of_isSmoothScheme m.smooth m.K)
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (blowUpToBase I) m.K) +
    ((J.card : ℤ) - 1) • Finsupp.single E₂ 1 with hK'def
  have hK'coeff : ∀ H, H ≠ E₂ → K'.coeff H = m.K.coeff (dn H) := by
    intro H hH
    haveI := (hdn H hH).2.2
    rw [hK'def, DivisorWithCoeffs.coeff_add, coeff_pullback_eq_of_isIso_stalkMap (blowUpToBase I)
      _ _ H (dn H) (hdn H hH).1]
    simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hH]
  -- the strict transform of `B`
  let Bs : QDivisor (blowUp I) := ∑ j, m.B (S j) • Finsupp.single (S' j) (1 : ℚ)
  have hBsapp : ∀ H, Bs.coeff H = ∑ j, m.B (S j) * if S' j = H then 1 else 0 := by
    intro H
    simp only [Bs, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
  have hBs : ∀ H, H ≠ E₂ → Bs.coeff H = m.B.coeff (dn H) := by
    intro H hH
    rw [hBsapp]
    by_cases hmem : dn H ∈ m.B.support
    · have hH' := hdnS H hH ⟨dn H, hmem⟩ rfl
      rw [Finset.sum_eq_single ⟨dn H, hmem⟩ (fun j _ hj => by
          rw [if_neg (fun h => hj (hS'inj (h.trans hH'))), mul_zero])
        (by simp), if_pos hH'.symm, mul_one]
      rfl
    · rw [Finset.sum_eq_zero (fun j _ => ?_)]
      · rw [Finsupp.notMem_support_iff] at hmem
        simp only [DivisorWithCoeffs.coeff_apply]; exact hmem.symm
      · rw [if_neg, mul_zero]
        rintro rfl
        exact hmem (by rw [hdnS' j]; exact j.2)
  have hBsE : Bs.coeff E₂ = 0 := by
    rw [hBsapp]
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg (hS'E j), mul_zero]
  -- the new divisors
  let M' : Divisor (blowUp I) := (Divisor.toQDivisor K' + Bs + Q').roundUp
  let B' : QDivisor (blowUp I) := Divisor.toQDivisor M' - Divisor.toQDivisor K' - Q'
  have hsumH : ∀ H, H ≠ E₂ → (Divisor.toQDivisor K' + Bs + Q').coeff H = (m.M.coeff (dn H) : ℚ) := by
    intro H hH
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      hK'coeff H hH, hBs H hH, hQ'coeff H hH, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor]
    ring
  have hM'H : ∀ H, H ≠ E₂ → M'.coeff H = m.M.coeff (dn H) := by
    intro H hH
    rw [DivisorWithCoeffs.coeff_roundUp, hsumH H hH, Int.ceil_intCast]
  have hB'H : ∀ H, H ≠ E₂ → B'.coeff H = m.B.coeff (dn H) := by
    intro H hH
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
      Divisor.coeff_toQDivisor, hM'H H hH, hK'coeff H hH, hQ'coeff H hH,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      Divisor.coeff_toQDivisor]
    ring
  have hB'E : 0 ≤ B'.coeff E₂ ∧ B'.coeff E₂ < 1 := by
    have hM'E : (M'.coeff E₂ : ℚ) = ⌈(Divisor.toQDivisor K').coeff E₂ + Q'.coeff E₂⌉ := by
      rw [DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_add, hBsE, add_zero]
    have hB'E' : B'.coeff E₂ = ⌈(Divisor.toQDivisor K').coeff E₂ + Q'.coeff E₂⌉ -
        ((Divisor.toQDivisor K').coeff E₂ + Q'.coeff E₂) := by
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
        hM'E, Divisor.coeff_toQDivisor]
      ring
    rw [hB'E']
    have hlt := Int.ceil_lt_add_one ((Divisor.toQDivisor K').coeff E₂ + Q'.coeff E₂)
    exact ⟨sub_nonneg.2 (Int.le_ceil _), by linarith⟩
  let m' : Model X sX :=
    { V := blowUp I
      sV := blowUpToBase I ≫ m.sV
      proj := hV'proj
      smooth := hV'smooth
      f := blowUpToBase I ≫ m.f
      hfs := by rw [Category.assoc, m.hfs]
      hfp := by
        haveI : MMP.Mori.IsProjectiveVariety ℂ sX := hX
        haveI : IsProper sX := (IsProjectiveMorphism.isProjective
          (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sX))).isProper
        haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
        haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
        exact IsProjective.comp hpproj m.hfp
      n := m.n
      K := K'
      hK := hK'
      B := B'
      hB := hsnc'.of_support_subset fun H hH => by
        rw [Finsupp.mem_support_iff] at hH ⊢
        have hsum : ((Finsupp.single E₂ (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ)) H) =
            (if E₂ = H then 1 else 0) + ∑ j, if S' j = H then 1 else 0 := by
          simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
        rw [hsum]
        by_cases hHE : H = E₂
        · subst hHE
          rw [if_pos rfl, Finset.sum_eq_zero (fun j _ => if_neg (hS'E j))]
          norm_num
        · have hne : m.B (dn H) ≠ 0 := by
            have := hB'H H hHE
            simp only [DivisorWithCoeffs.coeff_apply] at this
            rwa [this] at hH
          have hmem : dn H ∈ m.B.support := Finsupp.mem_support_iff.2 hne
          have hH' := hdnS H hHE ⟨dn H, hmem⟩ rfl
          rw [if_neg (Ne.symm hHE), Finset.sum_eq_single ⟨dn H, hmem⟩
            (fun j _ hj => if_neg (fun h => hj (hS'inj (h.trans hH')))) (by simp),
            if_pos hH'.symm]
          norm_num
      hB0 := fun H => by
        by_cases hH : H = E₂
        · subst hH; exact hB'E.1
        · have := hB'H H hH
          simp only [DivisorWithCoeffs.coeff_apply] at this
          rw [this]; exact m.hB0 _
      hB1 := fun H => by
        by_cases hH : H = E₂
        · subst hH; exact hB'E.2.le
        · have := hB'H H hH
          simp only [DivisorWithCoeffs.coeff_apply] at this
          rw [this]; exact m.hB1 _
      M := M'
      hM := hcart' M'
      hsa := by
        have : Divisor.toQDivisor M' - (Divisor.toQDivisor K' + B') = Q' := by
          simp only [B']; abel
        rw [this]; exact hQ'semi }
  -- the components of `⌊B'⌋` are strict transforms of components of `⌊B⌋`
  have hflB : ∀ G ∈ m.B.roundDown.support, G ∈ m.B.support := fun G hG => by
    rw [Finsupp.mem_support_iff] at hG ⊢
    intro h0
    apply hG
    have h := DivisorWithCoeffs.coeff_roundDown m.B G
    simp only [DivisorWithCoeffs.coeff_apply] at h
    rw [h, h0, Int.floor_zero]
  have hflr : ∀ H ∈ B'.roundDown.support, H ≠ E₂ ∧ dn H ∈ m.B.roundDown.support := by
    intro H hH
    have hfl := DivisorWithCoeffs.coeff_roundDown B' H
    rw [Finsupp.mem_support_iff] at hH
    simp only [DivisorWithCoeffs.coeff_apply] at hfl
    by_cases hHE : H = E₂
    · exfalso
      subst hHE
      apply hH
      rw [hfl]
      have h1 := hB'E.1
      have h2 := hB'E.2
      simp only [DivisorWithCoeffs.coeff_apply] at h1 h2
      exact Int.floor_eq_zero_iff.2 ⟨h1, h2⟩
    · refine ⟨hHE, ?_⟩
      have := hB'H H hHE
      simp only [DivisorWithCoeffs.coeff_apply] at this
      rw [Finsupp.mem_support_iff]
      have h2 := DivisorWithCoeffs.coeff_roundDown m.B (dn H)
      simp only [DivisorWithCoeffs.coeff_apply] at h2
      rw [h2, ← this, ← hfl]
      exact hH
  have hflS : ∀ H (hH : H ∈ B'.roundDown.support),
      H = S' ⟨dn H, hflB _ (hflr H hH).2⟩ := fun H hH =>
    hdnS H (hflr H hH).1 ⟨dn H, hflB _ (hflr H hH).2⟩ rfl
  have hS'sub : ∀ j, ((S' j).support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (S j).support := by
    intro j
    rw [MMP.Mori.support_inverseTransformPrimeDivisor (hS'tr j)]
    exact (IsClosed.closure_subset_iff ((S j).idealSheaf.support.isClosed.preimage
      (blowUpToBase I).base.hom.continuous)).2 fun z hz => hz.1
  -- the snc divisor `E + ∑ S'_j`, indexed by `Option`
  let fam : Option {P : MMP.Mori.PrimeDivisor m.V // P ∈ m.B.support} →
      MMP.Mori.PrimeDivisor (blowUp I) := fun o => o.elim E₂ S'
  have hfam : Function.Injective fam := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exact absurd h.symm (hS'E b)
    · exact absurd h (hS'E a)
    · exact congrArg some (hS'inj h)
  have hsncfam : DivisorWithCoeffs.IsSNC (blowUpToBase I ≫ m.sV)
      (∑ o, Finsupp.single (fam o) (1 : ℤ)) := by
    rw [Fintype.sum_option]; exact hsnc'
  -- strata of `⌊B'⌋` have their generic points off `E`
  have hoff : ∀ S'' : Set (blowUp I), MMP.Fourfold.IsSNCStratum B'.roundDown S'' →
      ∃ η', IsGenericPoint η' S'' ∧ η' ∉ (E₂.support : Set (blowUp I)) := by
    intro S'' ⟨J'', hJ'', hSm⟩
    have hScl : IsClosed S'' := isClosed_of_maximal_irreducible_subset
      (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed) hSm
    obtain ⟨η', hη'⟩ := QuasiSober.sober hSm.1.1 hScl
    refine ⟨η', hη', fun hηE => ?_⟩
    have hηJ : ∀ H ∈ J'', η' ∈ (H.support : Set (blowUp I)) := fun H hH =>
      Set.mem_iInter₂.1 (hSm.1.2 hη'.mem) H hH
    have hJsupp : J'' ⊆ (Finsupp.single E₂ (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ)).support := by
      intro H hH
      have hH' := hflS H (hJ'' hH)
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.finset_sum_apply,
        Finsupp.single_apply, if_neg (Ne.symm (hflr H (hJ'' hH)).1)]
      rw [Finset.sum_eq_single ⟨dn H, hflB _ (hflr H (hJ'' hH)).2⟩
        (fun j _ hj => by rw [Finsupp.single_apply, if_neg (fun h => hj (hS'inj (h.trans hH')))])
        (by simp), Finsupp.single_apply, if_pos hH'.symm]
      norm_num
    have hdim : ringKrullDim ((blowUp I).presheaf.stalk η') ≤ J''.card := by
      rw [ringKrullDim_stalk_eq_coheight]
      rcases Nat.lt_or_ge J''.card 2 with hlt | h2
      · interval_cases hcard : J''.card
        · -- no components: `S'' = V'`
          obtain rfl : J'' = ∅ := Finset.card_eq_zero.1 hcard
          have hSu : S'' = Set.univ := le_antisymm (Set.subset_univ _)
            (hSm.2 ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ => by simp⟩ (Set.subset_univ _))
          have hmax : IsMax η' := fun y _ => by
            have : y ∈ S'' := hSu ▸ Set.mem_univ y
            rw [← hη'.def] at this
            exact specializes_iff_mem_closure.2 this
          rw [Order.coheight_eq_zero.2 hmax]
          simp
        · -- one component `H`: `S'' = H`
          obtain ⟨H, rfl⟩ := Finset.card_eq_one.1 hcard
          have hHirr : IsIrreducible (H.support : Set (blowUp I)) := by
            rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
            exact isIrreducible_singleton.closure
          have hSH : S'' = (H.support : Set (blowUp I)) :=
            le_antisymm (by simpa using hSm.1.2) (hSm.2 ⟨hHirr, by simp⟩ (by simpa using hSm.1.2))
          have hgH : IsGenericPoint H.genericPoint S'' := by
            rw [hSH, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
            exact isGenericPoint_closure
          rw [hη'.eq hgH, H.coheight_genericPoint]
          simp
      · let J3 : Finset (Option {P : MMP.Mori.PrimeDivisor m.V // P ∈ m.B.support}) :=
          Finset.univ.filter (fun o => fam o ∈ J'')
        have hJ3card : J3.card = J''.card :=
          Finset.card_bij (fun o _ => fam o) (fun o ho => (Finset.mem_filter.1 ho).2)
            (fun a _ b _ h => hfam h)
            (fun H hH => ⟨some ⟨dn H, hflB _ (hflr H (hJ'' hH)).2⟩,
              Finset.mem_filter.2 ⟨Finset.mem_univ _, by
                have e := hflS H (hJ'' hH)
                change S' _ ∈ J''
                rwa [← e]⟩,
              (hflS H (hJ'' hH)).symm⟩)
        have hinter3 : (⋂ o ∈ J3, ((fam o).support : Set (blowUp I))) =
            ⋂ H ∈ J'', (H.support : Set (blowUp I)) := by
          ext y
          simp only [Set.mem_iInter, J3, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h H hH
            have h1 := h (some ⟨dn H, hflB _ (hflr H (hJ'' hH)).2⟩) (by
              have e := hflS H (hJ'' hH)
              change S' _ ∈ J''
              rwa [← e])
            rwa [hflS H (hJ'' hH)]
          · intro h o ho
            exact h (fam o) ho
        obtain ⟨-, hcod, -⟩ := MMP.Resolution.blowUp_snc_stratum (blowUpToBase I ≫ m.sV)
          hV'var hV'smooth fam hfam hsncfam J3 (hJ3card ▸ h2) ⟨S'', hinter3 ▸ hSm⟩
        have hcl : TopologicalSpace.Closeds.closure S'' =
            ⟨(TopologicalSpace.IrreducibleCloseds.closureSingleton η' : Set (blowUp I)),
              (TopologicalSpace.IrreducibleCloseds.closureSingleton η').isClosed⟩ := by
          ext1
          change closure S'' = closure {η'}
          rw [hη'.def, hScl.closure_eq]
        change MMP.Mori.closedsCodimension (TopologicalSpace.Closeds.closure S'') = _ at hcod
        rw [hcl, MMP.Mori.closedsCodimension_coe,
          Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hJ3card] at hcod
        rw [hcod]
        norm_cast
    have hEsupp' : E₂ ∈ (Finsupp.single E₂ (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ)).support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.finset_sum_apply,
        Finsupp.single_apply, if_pos rfl,
        Finset.sum_eq_zero fun j _ => by rw [Finsupp.single_apply, if_neg (hS'E j)]]
      norm_num
    have := mem_of_isSNC_of_ringKrullDim_le (D := Finsupp.single E₂ (1 : ℤ) +
      ∑ j, Finsupp.single (S' j) (1 : ℤ)) hsnc' hJsupp hηJ hdim hEsupp' hηE
    exact (hflr E₂ (hJ'' this)).1 rfl
  -- strata of `⌊B'⌋` map onto strata of `⌊B⌋` other than `T`
  have himgS : ∀ S'' : Set (blowUp I), MMP.Fourfold.IsSNCStratum B'.roundDown S'' →
      MMP.Fourfold.IsSNCStratum m.B.roundDown (blowUpToBase I '' S'') ∧
        blowUpToBase I '' S'' ≠ T := by
    intro S'' hS''
    obtain ⟨η', hη', hηE⟩ := hoff S'' hS''
    obtain ⟨J'', hJ'', hSm⟩ := hS''
    have hpη : blowUpToBase I η' ∉ T := fun h => hηE (by rwa [hEsupp])
    have hpηI : blowUpToBase I η' ∉ (I.support : Set m.V) := hIsupp ▸ hpη
    have himgcl : blowUpToBase I '' S'' = closure {blowUpToBase I η'} := by
      rw [← hη'.def, ← (blowUpToBase I).isClosedMap.closure_image_eq_of_continuous
        (blowUpToBase I).base.hom.continuous, Set.image_singleton]
    have hJ₀ : J''.image dn ⊆ m.B.roundDown.support := by
      intro G hG
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.1 hG
      exact (hflr H (hJ'' hH)).2
    have hηJ : ∀ H ∈ J'', η' ∈ (H.support : Set (blowUp I)) := fun H hH =>
      Set.mem_iInter₂.1 (hSm.1.2 hη'.mem) H hH
    have hpJ₀ : ∀ G ∈ J''.image dn, blowUpToBase I η' ∈ (G.support : Set m.V) := by
      intro G hG
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.1 hG
      have e := hflS H (hJ'' hH)
      have hmem : η' ∈ ((S' ⟨dn H, hflB _ (hflr H (hJ'' hH)).2⟩).support : Set (blowUp I)) := by
        rw [← e]; exact hηJ H hH
      exact hS'sub _ hmem
    have hclosed : IsClosed (⋂ G ∈ J''.image dn, (G.support : Set m.V)) :=
      isClosed_biInter fun G _ => G.idealSheaf.support.isClosed
    refine ⟨⟨J''.image dn, hJ₀, ?_⟩, ?_⟩
    · rw [himgcl]
      refine ⟨⟨isIrreducible_singleton.closure, closure_minimal
        (Set.singleton_subset_iff.2 (Set.mem_iInter₂.2 hpJ₀)) hclosed⟩, ?_⟩
      intro Y ⟨hYirr, hYsub⟩ hle
      obtain ⟨y₀, hy₀⟩ := QuasiSober.sober hYirr.closure isClosed_closure
      have hY'sub : closure Y ⊆ ⋂ G ∈ J''.image dn, (G.support : Set m.V) :=
        closure_minimal hYsub hclosed
      have hsp : y₀ ⤳ blowUpToBase I η' := by
        rw [specializes_iff_mem_closure, hy₀.def]
        exact subset_closure (hle (subset_closure rfl))
      have hy₀T : y₀ ∉ (I.support : Set m.V) := fun h =>
        hpηI (hsp.mem_closed I.support.isClosed h)
      obtain ⟨y₀', hy₀'⟩ := MMP.Fourfold.SNCWeight.StratumBlowup.exists_preimage_of_notMem I hy₀T
      have hbir₀ := MMP.Fourfold.SNCWeight.StratumBlowup.mem_biregularLocus_of_notMem I hy₀T
      have hbirη := MMP.Fourfold.SNCWeight.StratumBlowup.mem_biregularLocus_of_notMem I hpηI
      have hsp' : y₀' ⤳ η' := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus _
        (hy₀' ▸ hbir₀) hbirη (hy₀' ▸ hsp)
      have hy₀'J : y₀' ∈ ⋂ H ∈ J'', (H.support : Set (blowUp I)) := by
        refine Set.mem_iInter₂.2 fun H hH => ?_
        have e := hflS H (hJ'' hH)
        rw [e, MMP.Mori.support_inverseTransformPrimeDivisor (hS'tr _)]
        refine MMP.Mori.preimage_subset_inverseTransform _ _ ⟨?_, ?_⟩
        · show blowUpToBase I y₀' ∈ _
          rw [hy₀']
          exact Set.mem_iInter₂.1 (hY'sub hy₀.mem) (dn H) (Finset.mem_image_of_mem _ hH)
        · show blowUpToBase I y₀' ∈ _
          rwa [hy₀']
      have hS''y : S'' ⊆ closure {y₀'} := by
        rw [← hη'.def]
        exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp'))
          isClosed_closure
      have hcl' : closure {y₀'} ⊆ S'' := hSm.2 ⟨isIrreducible_singleton.closure,
        closure_minimal (Set.singleton_subset_iff.2 hy₀'J)
          (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed)⟩ hS''y
      have hη'y : η' ⤳ y₀' := by
        rw [specializes_iff_mem_closure, hη'.def]
        exact hcl' (subset_closure rfl)
      have heq : y₀' = η' := (hsp'.antisymm hη'y).eq
      calc Y ⊆ closure Y := subset_closure
        _ = closure {y₀} := hy₀.def.symm
        _ = closure {blowUpToBase I η'} := by rw [← hy₀', heq]
    · rw [himgcl]
      intro h
      exact hpη (h ▸ subset_closure rfl)
  have hinjS : ∀ S₁ S₂ : Set (blowUp I), MMP.Fourfold.IsSNCStratum B'.roundDown S₁ →
      MMP.Fourfold.IsSNCStratum B'.roundDown S₂ →
      blowUpToBase I '' S₁ = blowUpToBase I '' S₂ → S₁ = S₂ := by
    intro S₁ S₂ h₁ h₂ h
    obtain ⟨η₁, hη₁, hη₁E⟩ := hoff S₁ h₁
    obtain ⟨η₂, hη₂, hη₂E⟩ := hoff S₂ h₂
    have hcl : ∀ (Sx : Set (blowUp I)) (ηx : blowUp I), IsGenericPoint ηx Sx →
        IsGenericPoint (blowUpToBase I ηx) (blowUpToBase I '' Sx) := fun Sx ηx hx => by
      rw [← hx.def, ← ((blowUpToBase I).isClosedMap.closure_image_eq_of_continuous
        (blowUpToBase I).base.hom.continuous _), Set.image_singleton]
      exact isGenericPoint_closure
    have heq : blowUpToBase I η₁ = blowUpToBase I η₂ :=
      (hcl S₁ η₁ hη₁).eq (h ▸ hcl S₂ η₂ hη₂)
    have hnot : blowUpToBase I η₁ ∉ (I.support : Set m.V) := fun hm =>
      hη₁E (by rwa [hEsupp, Set.mem_preimage, ← hIsupp])
    have := MMP.Fourfold.SNCWeight.StratumBlowup.eq_of_map_eq_of_notMem I hnot heq
    rw [← hη₁.def, ← hη₂.def, this]
  refine ⟨m', ?_, ?_, ?_⟩
  · -- the associated point survives: nothing changes over `X ∖ f(T)`
    have hcl : IsClosed (m.f.base '' T) := m.f.isClosedMap _ hTcl
    let U : X.Opens := ⟨(m.f.base '' T)ᶜ, hcl.isOpen_compl⟩
    have hxU : x ∈ U := fun h => hxΔ (hTΔ h)
    have hle : m.f ⁻¹ᵁ U ≤ I.support.compl := fun v hv hvI =>
      hv ⟨v, hIsupp ▸ hvI, rfl⟩
    have hp : IsIso (blowUpToBase I ∣_ m.f ⁻¹ᵁ U) :=
      Stacks.PicFinite.isIso_morphismRestrict_of_le _ hle
    have hMc := MMP.Fourfold.isCartier_of_isSmoothScheme m.smooth m.M
    haveI := hMc.isInvertibleModule_divisorialSheaf
    have hgenM := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant
      (blowUpToBase I) m.M
    obtain ⟨eMp⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hMc (blowUpToBase I)
      hgenM
    set Mp := m.M.pullback hMc hgenM
    have hagree : ∀ H : MMP.Mori.PrimeDivisor (blowUp I),
        (H.support ∩ ((blowUpToBase I ≫ m.f) ⁻¹ᵁ U)).Nonempty → M'.coeff H = Mp.coeff H := by
      intro H hH
      have hHE : H ≠ E₂ := by
        rintro rfl
        obtain ⟨y, hyE, hyU⟩ := hH
        rw [hEsupp] at hyE
        exact hyU ⟨_, hyE, rfl⟩
      haveI := (hdn H hHE).2.2
      rw [hM'H H hHE, coeff_pullback_eq_of_isIso_stalkMap (blowUpToBase I) hMc hgenM H (dn H)
        (hdn H hHE).1]
    have hmin1 : M' ⊓ Mp ≤ M' := inf_le_left
    have hmin2 : M' ⊓ Mp ≤ Mp := inf_le_right
    have hcoefmin : ∀ H, (M' ⊓ Mp).coeff H = M'.coeff H ⊓ Mp.coeff H := fun H => rfl
    haveI h1 : IsIso ((Scheme.Modules.restrictFunctor ((blowUpToBase I ≫ m.f) ⁻¹ᵁ U).ι).map
        (Divisor.divisorialSheafInclusion hmin1)) :=
      Divisor.isIso_restrict_divisorialSheafInclusion hmin1 fun H hH => by
        rw [hcoefmin, hagree H hH, inf_idem]
    haveI h2 : IsIso ((Scheme.Modules.restrictFunctor ((blowUpToBase I ≫ m.f) ⁻¹ᵁ U).ι).map
        (Divisor.divisorialSheafInclusion hmin2)) :=
      Divisor.isIso_restrict_divisorialSheafInclusion hmin2 fun H hH => by
        rw [hcoefmin, hagree H hH, inf_idem]
    exact isAssociatedPoint_rightDerived_comp m.f (blowUpToBase I) q U hp
      ((asIso ((Scheme.Modules.restrictFunctor ((blowUpToBase I ≫ m.f) ⁻¹ᵁ U).ι).map
        (Divisor.divisorialSheafInclusion hmin1))).symm ≪≫
        asIso ((Scheme.Modules.restrictFunctor ((blowUpToBase I ≫ m.f) ⁻¹ᵁ U).ι).map
          (Divisor.divisorialSheafInclusion hmin2)) ≪≫
        (Scheme.Modules.restrictFunctor ((blowUpToBase I ≫ m.f) ⁻¹ᵁ U).ι).mapIso eMp) hxU hx
  · -- fewer bad strata
    have hTbad : T ∈ m.bad Δ := ⟨⟨J, hJ, hTm⟩, hTΔ⟩
    have hfin : (m.bad Δ).Finite := m.finite_strata.subset fun S hS => hS.1
    calc (m'.bad Δ).ncard ≤ (m.bad Δ \ {T}).ncard := by
          refine Set.ncard_le_ncard_of_injOn (fun S'' => blowUpToBase I '' S'') ?_ ?_
            hfin.diff
          · intro S'' ⟨hS'', hS''Δ⟩
            refine ⟨⟨(himgS S'' hS'').1, ?_⟩, (himgS S'' hS'').2⟩
            have : m.f.base '' (blowUpToBase I '' S'') = (blowUpToBase I ≫ m.f).base '' S'' := by
              rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
            rwa [this]
          · intro S₁ h₁ S₂ h₂ h
            exact hinjS S₁ S₂ h₁.1 h₂.1 h
      _ < (m.bad Δ).ncard := Set.ncard_diff_singleton_lt_of_mem hTbad hfin
  · -- the new strata lie over old ones
    intro S'' hS''
    refine ⟨blowUpToBase I '' S'', (himgS S'' hS'').1, ?_⟩
    change (blowUpToBase I ≫ m.f).base '' S'' = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]

/-- **One step of the boundary cleanup.** A stratum mapping into the closed set `Δ ∌ x` is
removed, by subtracting a floor component or by blowing up the stratum. -/
private theorem Model.exists_step (m : Model X sX) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (q : ℕ) (x : X) (hx : m.IsAss q x)
    (Δ : Set X) (hΔ : IsClosed Δ) (hxΔ : x ∉ Δ) (T : Set m.V) (hT : T ∈ m.bad Δ) :
    ∃ m' : Model X sX, m'.IsAss q x ∧ (m'.bad Δ).ncard < (m.bad Δ).ncard ∧
      ∀ S', MMP.Fourfold.IsSNCStratum m'.B.roundDown S' →
        ∃ S, MMP.Fourfold.IsSNCStratum m.B.roundDown S ∧ m'.f.base '' S' = m.f.base '' S := by
  classical
  haveI : IsProper m.f := m.hfp.isProper
  obtain ⟨⟨J, hJ, hTm⟩, hTΔ⟩ := hT
  by_cases hJ0 : J = ∅
  · -- the stratum is `V`, mapped into `Δ ∌ x`
    exfalso
    subst hJ0
    have hT : T = Set.univ := by
      refine le_antisymm (Set.subset_univ _) (hTm.2 ⟨IrreducibleSpace.isIrreducible_univ m.V,
        by simp⟩ (Set.subset_univ _))
    have hxr := mem_range_of_isAssociatedPoint_rightDerived m.f
      (m.f.isClosedMap.isClosed_range) q _ hx
    obtain ⟨v, rfl⟩ := hxr
    exact hxΔ (hTΔ ⟨v, hT ▸ Set.mem_univ v, rfl⟩)
  by_cases hJ1 : J.card = 1
  · -- the stratum is a component `E` of `⌊B⌋`: subtract it
    obtain ⟨E, rfl⟩ := Finset.card_eq_one.1 hJ1
    have hEsupp : E ∈ m.B.roundDown.support := hJ (Finset.mem_singleton_self E)
    have hE : m.B E = 1 := by
      have h1 := m.hB1 E
      have h0 := m.hB0 E
      rw [Finsupp.mem_support_iff] at hEsupp
      have : ⌊m.B E⌋ ≠ 0 := by
        have h := DivisorWithCoeffs.coeff_roundDown m.B E
        simp only [DivisorWithCoeffs.coeff_apply] at h
        rwa [← h]
      have h2 : (1 : ℚ) ≤ m.B E := by
        by_contra hlt
        exact this (Int.floor_eq_zero_iff.2 ⟨h0, lt_of_not_ge hlt⟩)
      exact le_antisymm h1 h2
    have hTE : T = (E.support : Set m.V) := by
      have hEirr : IsIrreducible (E.support : Set m.V) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      refine le_antisymm (by simpa using hTm.1.2) (hTm.2 ⟨hEirr, by simp⟩ (by simpa using hTm.1.2))
    subst hTE
    refine ⟨m.subtract E hE, m.isAss_subtract hE q hx fun h => hxΔ (hTΔ h), ?_, ?_⟩
    · have hsub : (m.subtract E hE).bad Δ ⊆ m.bad Δ \ {(E.support : Set m.V)} := by
        intro S ⟨hS, hSΔ⟩
        obtain ⟨hS', hne⟩ := isSNCStratum_of_sub_single (V := m.V) hE hS
        exact ⟨⟨hS', hSΔ⟩, hne⟩
      have hfin : (m.bad Δ).Finite := m.finite_strata.subset fun S hS => hS.1
      calc ((m.subtract E hE).bad Δ).ncard ≤ (m.bad Δ \ {(E.support : Set m.V)}).ncard :=
            Set.ncard_le_ncard hsub (hfin.diff)
        _ < (m.bad Δ).ncard := Set.ncard_diff_singleton_lt_of_mem
            ⟨⟨{E}, hJ, hTm⟩, hTΔ⟩ hfin
    · intro S' hS'
      exact ⟨S', (isSNCStratum_of_sub_single (V := m.V) hE hS').1, rfl⟩
  · exact m.exists_step_blowUp hX q x hx Δ hΔ hxΔ T J hJ
      (by have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hJ0); omega) hTm hTΔ

/-- **The boundary cleanup.** After finitely many steps no stratum maps into `Δ`. -/
private theorem Model.exists_clean (m : Model X sX) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (q : ℕ) (x : X) (hx : m.IsAss q x)
    (Δ : Set X) (hΔ : IsClosed Δ) (hxΔ : x ∉ Δ) :
    ∃ m' : Model X sX, m'.IsAss q x ∧
      ∀ S', MMP.Fourfold.IsSNCStratum m'.B.roundDown S' →
        ¬ m'.f.base '' S' ⊆ Δ ∧
        ∃ S, MMP.Fourfold.IsSNCStratum m.B.roundDown S ∧ m'.f.base '' S' = m.f.base '' S := by
  induction h : (m.bad Δ).ncard using Nat.strong_induction_on generalizing m with
  | _ N ih =>
    by_cases hb : ∃ T, T ∈ m.bad Δ
    · obtain ⟨T, hT⟩ := hb
      obtain ⟨m₁, hx₁, hlt, himg₁⟩ := m.exists_step hX q x hx Δ hΔ hxΔ T hT
      obtain ⟨m₂, hx₂, h₂⟩ := ih _ (h ▸ hlt) m₁ hx₁ rfl
      refine ⟨m₂, hx₂, fun S' hS' => ⟨(h₂ S' hS').1, ?_⟩⟩
      obtain ⟨S₁, hS₁, he₁⟩ := (h₂ S' hS').2
      obtain ⟨S, hS, he⟩ := himg₁ S₁ hS₁
      exact ⟨S, hS, he₁.trans he⟩
    · push Not at hb
      exact ⟨m, hx, fun S' hS' => ⟨fun hsub => hb S' ⟨hS', hsub⟩, S', hS', rfl⟩⟩

/-- **The main case.** If no stratum image lies in `closure {x}`, then `x` is not an associated
point of `R^q f_* 𝒪_V(M)`. -/
private theorem Model.false_of_isAss (m : Model X sX) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (q : ℕ) (x : X) (hx : m.IsAss q x)
    (hZ : ∀ S, MMP.Fourfold.IsSNCStratum m.B.roundDown S → ¬ m.f.base '' S ⊆ closure {x}) :
    False := by
  classical
  haveI := m.proj
  haveI : CompactSpace m.V := by
    haveI : IsProper m.sV := (IsProjectiveMorphism.isProjective
      (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := m.sV))).isProper
    exact QuasiCompact.compactSpace_of_compactSpace m.sV
  obtain ⟨H, hH⟩ := exists_isAmple_cartierSheaf hX
  -- the generic points of the stratum images
  have hirr : ∀ {S : Set m.V}, MMP.Fourfold.IsSNCStratum m.B.roundDown S →
      IsIrreducible (m.f.base '' S) := fun {S} hS => by
    obtain ⟨J, -, hS⟩ := hS
    exact hS.1.1.image _ m.f.base.hom.continuous.continuousOn
  let η : Set m.V → X := fun S => if h : MMP.Fourfold.IsSNCStratum m.B.roundDown S then
    (hirr h).genericPoint else x
  have hη : ∀ {S}, (hS : MMP.Fourfold.IsSNCStratum m.B.roundDown S) →
      IsGenericPoint (η S) (m.f.base '' S) := fun {S} hS => by
    simp only [η, dif_pos hS]
    have := (hirr hS).isGenericPoint_genericPoint_closure
    rwa [(m.isClosed_image_stratum hS).closure_eq] at this
  set T : Set X := η '' {S | MMP.Fourfold.IsSNCStratum m.B.roundDown S}
  have hT : T.Finite := m.finite_strata.image η
  have hTx : ∀ y ∈ T, y ∉ closure {x} := by
    rintro _ ⟨S, hS, rfl⟩ hy
    refine hZ S hS ?_
    rw [← (hη hS).def]
    exact closure_minimal (Set.singleton_subset_iff.2 hy) isClosed_closure
  -- `V` itself is a stratum, so `f(V) ⊄ |A|`
  have hVS : MMP.Fourfold.IsSNCStratum m.B.roundDown Set.univ := by
    refine ⟨∅, Finset.empty_subset _, ⟨⟨IrreducibleSpace.isIrreducible_univ m.V, ?_⟩, fun T hT _ =>
      Set.subset_univ T⟩⟩
    simp
  obtain ⟨a, A, hAe, hAH, hxA, hTA⟩ :=
    exists_isEffective_mem_support hX H hH x T hT ⟨_, Set.univ, hVS, rfl⟩ hTx
  have hAf : ¬ Set.range m.f ⊆ MMP.Intersection.cartierSupport A := by
    intro h
    refine hTA _ ⟨Set.univ, hVS, rfl⟩ (h ?_)
    have := (hη hVS).mem
    rwa [Set.image_univ] at this
  obtain ⟨D, hD⟩ := exists_isWeilDivisorOfCartier (MMP.CartierDivisor.pullback m.f A hAf)
  obtain ⟨hD0, hDA⟩ := nonneg_and_supp_subset_of_isWeilDivisorOfCartier_pullback m.f A hAe hAf D hD
  have hDS : MMP.Fourfold.ContainsNoStratum m.B.roundDown (D.supp : Set m.V) := by
    intro S hS hSD
    obtain ⟨J, hJ, hSm⟩ := hS
    have hSc : IsClosed S := isClosed_of_maximal_irreducible_subset
      (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed) hSm
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hSm.1.1 hSc
    have hfξ : IsGenericPoint (m.f.base ξ) (m.f.base '' S) := by
      have := hξ.image m.f.base.hom.continuous
      rwa [(m.isClosed_image_stratum ⟨J, hJ, hSm⟩).closure_eq] at this
    have hgen := (hη ⟨J, hJ, hSm⟩).eq hfξ
    exact hTA _ ⟨S, ⟨J, hJ, hSm⟩, hgen⟩ (hDA (hSD hξ.mem))
  exact m.not_mono_rightDerived_map_inclusion q x hx A hAe hxA hAf D hD hD0
    (m.mono_rightDerived_map_inclusion hX q H hH a A hAe hAH hAf D hD hD0 hDS)

end Proof_thm_mmp_lc_bpf_snc_torsion_free

namespace MMP.Mori

open Proof_thm_mmp_lc_bpf_snc_torsion_free

/-- **Torsion-freeness of higher direct images** (Kollár, Ambro, Fujino). Let `f : V ⟶ X` be a
projective morphism of complex projective varieties, with `V` smooth and `K` a canonical
divisor of `V`, and let `B` be
a `ℚ`-divisor with snc support and coefficients in `[0, 1]`. If `M` is a Cartier divisor with
`M - (K + B)` semiample over `X`, then every associated point `x` of `R^q f_* 𝒪_V(M)` is the
generic point of `f(S)` for a stratum `S` of `⌊B⌋`, the whole of `V` included. -/
@[mmp "thm_mmp_lc_bpf_snc_torsion_free"]
public theorem exists_isSNCStratum_closure_eq_image_of_isAssociatedPoint_rightDerived_pushforward
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sV] (hVsm : IsSmoothScheme sV)
    [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ X) (hfs : f ≫ sX = sV)
    (hfp : IsProjective f)
    {n : ℕ} (K : Divisor V) (hK : K.IsCanonicalDivisor sV n)
    (B : QDivisor V) (hB : B.IsSNC sV) (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1)
    (M : Divisor V) (hM : M.IsCartier)
    (hsa : Fourfold.QDivisor.IsRelativelySemiample f
      (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)))
    (q : ℕ) (x : X)
    (hx : Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward f).rightDerived q).obj M.divisorialSheaf) x) :
    ∃ S : Set V, Fourfold.IsSNCStratum B.roundDown S ∧ closure {x} = f.base '' S := by
  have hX : MMP.Mori.IsProjectiveVariety ℂ sX := ‹_›
  have hV : MMP.Mori.IsProjectiveVariety ℂ sV := ‹_›
  haveI : IsIntegral V :=
    ((AlgebraicGeometry.isProjectiveVariety_iff ℂ sV).1 hV).1.toIsIntegral
  haveI : IsProper sV := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sV))).isProper
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsProper sX := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sX))).isProper
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsProper f := hfp.isProper
  let m : Model X sX := ⟨V, sV, hV, hVsm, f, hfs, hfp, n, K, hK, B, hB, hB0, hB1, M, hM,
    isGeneratedOver_of_isRelativelySemiample f hsa⟩
  by_contra hcon
  push Not at hcon
  -- the stratum images properly inside `closure {x}`
  set Δ : Set X := ⋃ S ∈ {S : Set V | MMP.Fourfold.IsSNCStratum B.roundDown S ∧
    f.base '' S ⊆ closure {x} ∧ x ∉ f.base '' S}, f.base '' S with hΔ
  have hΔc : IsClosed Δ :=
    (m.finite_strata.subset fun S hS => hS.1).isClosed_biUnion fun S hS =>
      m.isClosed_image_stratum hS.1
  have hxΔ : x ∉ Δ := by
    simp only [hΔ, Set.mem_iUnion, not_exists]
    exact fun S hS => hS.2.2
  obtain ⟨m', hx', h'⟩ := m.exists_clean hX q x hx Δ hΔc hxΔ
  refine m'.false_of_isAss hX q x hx' fun S' hS' hsub => ?_
  obtain ⟨hnot, S, hS, he⟩ := h' S' hS'
  have hSZ : f.base '' S ⊆ closure {x} := he ▸ hsub
  by_cases hxS : x ∈ f.base '' S
  · refine hcon S hS (le_antisymm ?_ hSZ)
    exact (closure_minimal (Set.singleton_subset_iff.2 hxS) (m.isClosed_image_stratum hS))
  · exact hnot (he ▸ Set.subset_biUnion_of_mem (u := fun S => f.base '' S) ⟨hS, hSZ, hxS⟩)

end MMP.Mori

end
