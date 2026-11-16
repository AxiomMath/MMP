module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.MinimalModel.DltModification
import MMP.AlgebraicGeometry.MMP.Surface.ComplementedLcSemiample
import MMP.AlgebraicGeometry.MMP.Threefold.LogMMP
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.Singularities.DltKltPerturbation
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
import MMP.AlgebraicGeometry.MMP.ConeTheorem.RayLength
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Singularities.PltDifferentCoefficients
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.FloorProgramInputs
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Singularities.DltFloorComplement
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.MMP.MinimalModel.WeakLcModelComparison
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Complemented dlt threefolds with a horizontal floor over a surface

Let `(X, B)` be an effective `ℚ`-factorial projective complex dlt threefold pair and
`f : X ⟶ Z` a projective morphism with connected fibres and `f_* 𝒪_X = 𝒪_Z` onto a normal
projective surface `Z`, such that `D = K_X + B` is `f`-nef. Suppose `A ≥ 0` is a `ℚ`-Cartier
divisor with `(X, B + A)` log canonical and `D + A ∼_ℚ f^*H` for a rational Cartier divisor `H`
on `Z`. If some component of `⌊B⌋` dominates `Z`, then `D` is `f`-semiample.

The proof runs the klt program for `D - t₀⌊B⌋` over `Z` for a small `t₀ > 0`. Every step is
`D`-trivial, and the horizontal floor component keeps the generic degree of `D - t₀⌊B⌋` on the
generic fibre negative, so the program ends with a Mori fibre space `Y ⟶ V` over `Z` with `V ⟶ Z`
birational and `m D_Y` pulled back from an invertible sheaf on `V`. On a crepant dlt modification
of `Y`, the strict transform `S` of the floor component dominates `V`; the complement restricts
to `S`, the complemented lc surface theorem makes `K_S + B_S` semiample over `Z`, and this
descends along the generically finite `S ⟶ V`.

## Main results

* `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent_of_dense`:
  the statement above.

## Implementation notes

* As in `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent`,
  "`D + A ∼_ℚ f^*H` for a rational Cartier divisor `H` on `Z`" is `D + A ∼_ℚ G` for a
  `ℚ`-divisor `G` on `X` with `𝒪_X(mG) ≅ f^* M` for some `m > 0` and an invertible
  `𝒪_Z`-module `M` (`M = 𝒪_Z(mH)`), and "`D` is `f`-semiample" is: some positive multiple of `D`
  is a Cartier divisor `L` with `f^* f_* 𝒪_X(L) → 𝒪_X(L)` surjective
  (`MMP.Fourfold.IsRelativelyFreeDivisor`).
* `f_* 𝒪_X = 𝒪_Z` is that `f.app U` is an isomorphism for every open `U` of `Z`.
* A component of `⌊B⌋` is a prime divisor `E` with `1 ≤ B_E`; it dominates `Z` when `f(E)` is
  dense in `Z`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

namespace Proof_thm_fourfold_complemented_threefold_horizontal_floor_good

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Fourfold

/-! ### Transport of relative freeness -/

section RelativelyFree

variable {X Y S : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

omit [IsIntegral X] [CompactSpace X] in
/-- Relative freeness only depends on the divisorial sheaf up to isomorphism. -/
private theorem isRelativelyFreeDivisor_of_iso (g : X ⟶ S) {D D' : Divisor X}
    (e : D.divisorialSheaf ≅ D'.divisorialSheaf) (h : IsRelativelyFreeDivisor g D) :
    IsRelativelyFreeDivisor g D' := by
  unfold IsRelativelyFreeDivisor at h ⊢
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction g).counit.naturality e.hom
  have : (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app D'.divisorialSheaf =
      inv ((Scheme.Modules.pushforward g ⋙ Scheme.Modules.pullback g).map e.hom) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app D.divisorialSheaf ≫
          e.hom := by
    rw [Functor.id_map] at hn
    rw [← hn, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

/-- Relative freeness is invariant under linear equivalence. -/
private theorem IsRelativelyFreeDivisor.of_linearlyEquivalent (g : X ⟶ S) {D D' : Divisor X}
    (hDD' : D.LinearlyEquivalent D') (h : IsRelativelyFreeDivisor g D) :
    IsRelativelyFreeDivisor g D' :=
  isRelativelyFreeDivisor_of_iso g hDD'.divisorialSheafIso h

variable [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- **The pull-back of a relatively free Cartier divisor is relatively free.** If `N` is a
Cartier divisor on `Y`, relatively free over `S` by `g`, and `q : X ⟶ Y` is dominant, then
`q^* N` is relatively free over `S` by `q ≫ g`: a relative section of `N` generating it at
`q x` pulls back to one generating `q^*N` at `x`. -/
private theorem IsRelativelyFreeDivisor.of_isPullback (q : X ⟶ Y) [IsDominant q] (g : Y ⟶ S)
    {N : Divisor Y} (hNc : N.IsCartier)
    {hN : ∀ T : irreducibleComponents X, q (componentGenericPoint X T) ∉ N.supp}
    {N' : Divisor X} (hpb : N.IsPullback q hN N') (hfree : IsRelativelyFreeDivisor g N) :
    IsRelativelyFreeDivisor (q ≫ g) N' := by
  apply isRelativelyFreeDivisor_of_forall_exists
  intro x
  obtain ⟨U, hU, ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree g hNc hfree (q x)
  set N₁ : Divisor Y := N + principalDivisor ψ with hN₁def
  have hN₁c : N₁.IsCartier := hNc.add (Divisor.isCartier_principalDivisor ψ)
  have hψ : ∀ T : irreducibleComponents X,
      q (componentGenericPoint X T) ∉ (principalDivisor ψ).supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant q _
  have hN₁ : ∀ T : irreducibleComponents X, q (componentGenericPoint X T) ∉ N₁.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant q _
  have hpb₁ : N₁.IsPullback q hN₁
      (N' + principalDivisor (pullbackRationalFunction q ψ hψ)) :=
    hpb.add hNc (Divisor.isCartier_principalDivisor ψ) hN₁ (Divisor.isPullback_principalDivisor ψ hψ)
  have hcoeff : ∀ P : MMP.Mori.PrimeDivisor X,
      N'.coeff P + P.ord (pullbackRationalFunction q ψ hψ) =
        (N' + principalDivisor (pullbackRationalFunction q ψ hψ)).coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  -- `q x` lies off the support of `N₁`
  have hx : q x ∉ (N₁.supp : Set Y) := by
    intro h
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    exact hP (by rw [hN₁def, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]; exact h2 P hxP)
  let W : Y.Opens := ⟨(N₁.supp : Set Y)ᶜ, (N₁.isClosed_supp).isOpen_compl⟩
  have hW : N₁.IsLocalEquation W 1 := fun P ⟨y, hyP, hyW⟩ => by
    rw [PrimeDivisor.ord_one]
    by_contra hP
    exact hyW (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hP, hyP⟩)
  refine ⟨U, hU, pullbackRationalFunction q ψ hψ, fun P hP => ?_, fun P hxP => ?_⟩
  · rw [hcoeff]
    exact coeff_nonneg_of_isPullback_of_isEffectiveOn hN₁c (V := g ⁻¹ᵁ U)
      (fun P' hP' => by
        rw [hN₁def, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]; exact h1 P' hP') hpb₁ P hP
  · rw [hcoeff]
    have hPW : (P.support ∩ q ⁻¹ᵁ W).Nonempty := ⟨x, hxP, hx⟩
    rw [hpb₁ W 1 hW P hPW]
    have hZ := P.map_componentGenericPoint_mem q hPW
    rw [pullbackComponent_eq hN₁ hW hZ (mem_pointComponent _) 1 (by simp), map_one,
      PrimeDivisor.ordUnit_one]

end RelativelyFree

/-! ### The steps of a program -/

/-- The facts about the `i`-th step `X_i → Z_i ← X_{i+1}` of a program used to move relative
freeness across it: `Z_i` is a normal variety, `f_i` is dominant, `f_i⁺` is proper, surjective and
birational from the normal variety `X_{i+1}` (over `ℂ` through `Z_i`), and both maps lie over the
base. -/
private theorem step_facts {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) :
    IsNormalVariety ℂ (P.sZ i) ∧ IsBirationalMorphism (P.f i) ∧ IsProper (P.fp i) ∧
      IsBirationalMorphism (P.fp i) ∧ IsNormalVariety ℂ (P.fp i ≫ P.sZ i) ∧
      P.f i ≫ P.gZ i = modelMap π P.πY i ∧ P.fp i ≫ P.gZ i = P.πY i := by
  have hstep := P.isElementaryDltStep i hi
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsSeparated (P.sZ i) := hZ.1.toIsSeparated
  haveI : QuasiCompact (P.sZ i) := hZ.1.toQuasiCompact
  haveI : IsNormal (P.Z i) := hZ.2
  have hfg := hstep.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
  rcases hstep.divisorial_or_flip with ⟨hfb, -, hiso, -⟩ | hflip
  · refine ⟨hZ, hfb, inferInstance, isBirationalMorphism_of_isIso _, ⟨?_, inferInstance⟩, hfg,
      hstep.comp_eq⟩
    have hv : MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) :=
      { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
        toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
    exact hv
  · obtain ⟨-, V, W, hV, hW, hle, hiso⟩ := hflip.isSmall_source
    obtain ⟨-, V', W', hV', hW', hle', hiso'⟩ := hflip.isSmall
    refine ⟨hZ, MMP.Flips.isBirationalMorphism_of_isIso_resLE (P.f i) V.compl W.compl
      (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V hV)
      (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension W hW) hle hiso, hflip.isProper,
      MMP.Flips.isBirationalMorphism_of_isIso_resLE (P.fp i) V'.compl W'.compl
      (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V' hV')
      (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension W' hW') hle' hiso', ?_, hfg,
      hstep.comp_eq⟩
    rw [hflip.isSmall.comp_eq]
    exact hflip.isNormalVariety_flip

/-- **A divisorial step is a morphism.** For a divisorial contraction `f_i` the map `φ_i` is the
birational morphism `f_i ≫ (f_i⁺)⁻¹ : X_i ⟶ X_{i+1}` over `ℂ`. -/
private theorem divisorial_step_facts {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) (hfb : IsBirationalMorphism (P.f i)) [IsIso (P.fp i)]
    (hmod : MMP.Flips.IsModificationOf (P.f i) (P.fp i) (P.φ i)) :
    P.φ i = (P.f i ≫ inv (P.fp i)).toRationalMap ∧
      (P.f i ≫ inv (P.fp i)) ≫ P.sY i = modelStr sX P.sY i ∧
      IsBirationalMorphism (P.f i ≫ inv (P.fp i)) := by
  have hstep := P.isElementaryDltStep i hi
  have hZ : IsNormalVariety ℂ (P.sZ i) :=
    hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZ.2
  haveI : IsProper (P.f i) := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
    |>.isContraction.isProper
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := Scheme.PartialMap.toRationalMap_surjective (P.φ i)
    have h2 : (P.φ i).compHom (P.fp i) = (P.f i).toRationalMap := hmod.2
    have hcc : ∀ (a : P.Y i ⟶ P.Z i) (b : P.Z i ⟶ P.Y i),
        ((P.φ i).compHom a).compHom b = (P.φ i).compHom (a ≫ b) := fun a b => by
      rw [← hψ, ← Scheme.RationalMap.compHom_toRationalMap,
        ← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
      rfl
    calc P.φ i = (P.φ i).compHom (P.fp i ≫ inv (P.fp i)) := by
            rw [IsIso.hom_inv_id, ← hψ, ← Scheme.RationalMap.compHom_toRationalMap,
              Scheme.PartialMap.compHom_id]
      _ = ((P.f i).toRationalMap).compHom (inv (P.fp i)) := by rw [← hcc, h2]
      _ = (P.f i ≫ inv (P.fp i)).toRationalMap := rfl
  · have hm1 := P.isRelativeDltModel (i + 1) (Order.add_one_le_of_lt hi)
    have hm0 := P.isRelativeDltModel i hi.le
    have hfg := hstep.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
    have h1 : P.πY i ≫ sS = P.sY i := hm1.comp_eq
    rw [← hm0.comp_eq, ← h1, ← hstep.comp_eq, ← hfg]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  · exact isBirationalMorphism_comp_of_isBirational (inv (P.fp i)) (P.f i)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
        (isBirationalMorphism_of_isIso _))
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)

/-- **Prime divisors along a step.** Every prime divisor `F'` of `X_{i+1}` lies, by `f_i⁺`, over
the generic point of a prime divisor `Q` of `Z_i` over which `f_i` maps the generic point of a
prime divisor `F` of `X_i`, and the coefficient of `F'` in the transform `(φ_i)_* D` is the
coefficient of `F` in `D`. For a flip both contractions are isomorphisms over an open subset of
`Z_i` containing the images of the points of codimension at most one; for a divisorial contraction
`φ_i` is the morphism `f_i ≫ (f_i⁺)⁻¹`. -/
private theorem step_coeff {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) (F' : MMP.Mori.PrimeDivisor (P.Y i)) :
    ∃ (F : MMP.Mori.PrimeDivisor (modelSeq X P.Y i)) (Q : MMP.Mori.PrimeDivisor (P.Z i)),
      P.f i F.genericPoint = Q.genericPoint ∧ P.fp i F'.genericPoint = Q.genericPoint ∧
      ∀ {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R (modelSeq X P.Y i)),
        MMP.Mori.RationalMap.transformDivisor (P.φ i) D F' = D F := by
  have hstep := P.isElementaryDltStep i hi
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  have hcon := hctr.isContraction
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZ.2
  haveI : IsProper (P.f i) := hcon.isProper
  have hXn : IsNormalVariety ℂ (P.f i ≫ P.sZ i) := by
    rw [hcon.comp_eq]; exact hctr.isNormalVariety_source
  rcases hstep.divisorial_or_flip with ⟨hfb, -, hiso, hmod⟩ | hflip
  · haveI := hiso
    obtain ⟨hφ, hgs, hgb⟩ := divisorial_step_facts P i hi hfb hmod
    set g := P.f i ≫ inv (P.fp i) with hg
    have hYn : IsNormalVariety ℂ (P.sY i) :=
      (P.isRelativeDltModel (i + 1) (Order.add_one_le_of_lt hi)).isQFactorial.1
    haveI : IsProper g := by rw [hg]; infer_instance
    obtain ⟨F, hF, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
      hYn (f := g) (hgs ▸ (P.isRelativeDltModel i hi.le).isQFactorial.1) hgb F'
    have hco : Order.coheight (P.fp i F'.genericPoint) = 1 := by
      rw [coheight_eq_of_isOpenImmersion (P.fp i), F'.coheight_genericPoint]
    have hQ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    refine ⟨F, AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, Eq.trans ?_ hQ.symm, hQ.symm,
      fun D => ?_⟩
    · rw [← hF, hg, ← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id]
    · rw [hφ]; exact htr D
  · obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ := MMP.Mori.exists_opens_isIso_of_isSmall
      hflip.isSmall_source hflip.isSmall
    haveI := hfV
    haveI := hfpV
    haveI := isSeparated_toTerminal_of_isNormalVariety hflip.isNormalVariety_flip
    have hfb := hflip.isSmall_source.isBirationalMorphism
    have hF'V : P.fp i F'.genericPoint ∈ V := hX'V _ F'.coheight_genericPoint.le
    obtain ⟨F, hFF'⟩ := MMP.Mori.exists_primeDivisor_genericPoint_eq (P.f i) (P.fp i) V F' hF'V
    have hco : Order.coheight (P.fp i F'.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus (P.fp i)
        ((isBiregular_iff_le_biregularLocus.mp hfpV) hF'V), F'.coheight_genericPoint]
    have hQ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    refine ⟨F, AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, hFF'.trans hQ.symm, hQ.symm,
      fun D => ?_⟩
    rw [MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZ hXn hfb V hXV hX'V
      hflip.isModificationOf.2 D]
    exact MMP.Mori.flipTransform_apply hZ hXn hfb V hXV hFF' D

/-- **Pull-backs along a step.** If `D₁ = f_i^* N` and `D₂ = (f_i⁺)^* N` for a Cartier divisor
`N` on `Z_i`, then `(φ_i)_* D₁ = D₂`: both `f_i` and `f_i⁺` are local isomorphisms over the generic
point of each prime divisor of `Z_i` they hit. -/
private theorem transformDivisor_eq_of_isPullback {X S : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X}
    (P : RelativeDltProgram sX sS π K B₀) (i : ℕ) (hi : (i : ℕ∞) < P.n)
    [IsIntegral (P.Z i)] [IsLocallyNoetherian (P.Z i)] [IsNormal (P.Z i)]
    {N : Divisor (P.Z i)} (hNc : N.IsCartier)
    {hN : ∀ T : irreducibleComponents (modelSeq X P.Y i), P.f i (componentGenericPoint _ T) ∉ N.supp}
    {hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp}
    {D₁ : Divisor (modelSeq X P.Y i)} {D₂ : Divisor (P.Y i)} (h₁ : N.IsPullback (P.f i) hN D₁)
    (h₂ : N.IsPullback (P.fp i) hN' D₂) :
    MMP.Mori.RationalMap.transformDivisor (P.φ i) D₁ = D₂ := by
  obtain ⟨-, hfb, -, hfpb, -, -, -⟩ := step_facts P i hi
  refine Finsupp.ext fun F' => ?_
  obtain ⟨F, Q, hF, hF', htr⟩ := step_coeff P i hi F'
  rw [htr]
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfb hF
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfpb hF'
  exact (MMP.Positivity.coeff_eq_of_isPullback F Q hF hNc h₁).trans
    (MMP.Positivity.coeff_eq_of_isPullback F' Q hF' hNc h₂).symm

/-- The transform along a step commutes with `Divisor.toQDivisor`. -/
private theorem transformDivisor_toQDivisor {X S : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X}
    (P : RelativeDltProgram sX sS π K B₀) (i : ℕ) (hi : (i : ℕ∞) < P.n)
    (D : Divisor (modelSeq X P.Y i)) :
    MMP.Mori.RationalMap.transformDivisor (P.φ i) (Divisor.toQDivisor D) =
      Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor (P.φ i) D) := by
  refine Finsupp.ext fun F' => ?_
  obtain ⟨F, Q, -, -, htr⟩ := step_coeff P i hi F'
  change MMP.Mori.RationalMap.transformDivisor (P.φ i) (Divisor.toQDivisor D) F' =
    ((MMP.Mori.RationalMap.transformDivisor (P.φ i) D F' : ℤ) : ℚ)
  rw [htr, htr]
  rfl

/-- **Canonical divisors along a step.** The transform `(φ_i)_* K_i` of the canonical divisor of
`X_i` is linearly equivalent to the canonical divisor `K_{i+1}` of `X_{i+1}`: it is a canonical
divisor, being the push-forward along the birational morphism `f_i ≫ (f_i⁺)⁻¹` for a divisorial
contraction, and the strict transform `(f_i⁺)⁻¹_* (f_i)_* K_i` for a flip. -/
private theorem transformDivisor_linearlyEquivalent_canonical {X S : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X}
    (P : RelativeDltProgram sX sS π K B₀) (i : ℕ) (hi : (i : ℕ∞) < P.n) :
    Divisor.LinearlyEquivalent
      (MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq K P.KY i)) (P.KY i) := by
  have hstep := P.isElementaryDltStep i hi
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  have hcon := hctr.isContraction
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZ.2
  haveI : IsProper (P.f i) := hcon.isProper
  have hm1 := P.isRelativeDltModel (i + 1) (Order.add_one_le_of_lt hi)
  have hm0 := P.isRelativeDltModel i hi.le
  have hYn : IsNormalVariety ℂ (P.sY i) := hm1.isQFactorial.1
  have hX0n : IsNormalVariety ℂ (modelStr sX P.sY i) := hm0.isQFactorial.1
  obtain ⟨n₀, hK₀⟩ := hm0.isCanonicalDivisor
  obtain ⟨n₁, hK₁⟩ := hm1.isCanonicalDivisor
  change (P.KY i).IsCanonicalDivisor (P.sY i) n₁ at hK₁
  suffices hcan : ∃ n : ℕ, Divisor.IsCanonicalDivisor (P.sY i) n
      (MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq K P.KY i)) by
    obtain ⟨n, hn⟩ := hcan
    exact MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (P.sY i) hYn hn hK₁
  have hXn : IsNormalVariety ℂ (P.f i ≫ P.sZ i) := by rw [hcon.comp_eq]; exact hX0n
  rcases hstep.divisorial_or_flip with ⟨hfb, -, hiso, hmod⟩ | hflip
  · haveI := hiso
    obtain ⟨hφ, hgs, hgb⟩ := divisorial_step_facts P i hi hfb hmod
    haveI : IsProper (P.f i ≫ inv (P.fp i)) := inferInstance
    haveI : IsDominant (P.f i ≫ inv (P.fp i)) := hgb.isDominant
    haveI : LocallyOfFiniteType (P.sY i) := hYn.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType ((P.f i ≫ inv (P.fp i)) ≫ P.sY i) := by
      rw [hgs]; exact hX0n.1.toLocallyOfFiniteType
    haveI : MMP.Mori.IsVariety ℂ (P.sY i) := hYn.1
    haveI : MMP.Mori.IsVariety ℂ (modelStr sX P.sY i) := hX0n.1
    have hn : n₀ = n₁ := by
      have h0 := hK₀.topologicalKrullDim_eq
      have h1 := hK₁.topologicalKrullDim_eq
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sY i)
        (modelStr sX P.sY i) hgb, h0] at h1
      exact_mod_cast h1
    subst hn
    refine ⟨n₀, ?_⟩
    rw [hφ]
    exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hYn (hgs ▸ hX0n) hgb hK₁
      (hgs ▸ hK₀)
  · obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ := MMP.Mori.exists_opens_isIso_of_isSmall
      hflip.isSmall_source hflip.isSmall
    haveI := hfV
    haveI := hfpV
    haveI := isSeparated_toTerminal_of_isNormalVariety hflip.isNormalVariety_flip
    have hfb := hflip.isSmall_source.isBirationalMorphism
    have hfpb := hflip.isSmall.isBirationalMorphism
    have hfps : P.fp i ≫ P.sZ i = P.sY i := hflip.isSmall.comp_eq
    have hc := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZ hXn
      (hfps ▸ hYn) hfb hfpb V hXV hX'V (n := n₀) (hcon.comp_eq ▸ hK₀)
    rw [hfps] at hc
    refine ⟨n₀, ?_⟩
    rw [MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZ hXn hfb V hXV hX'V
      hflip.isModificationOf.2]
    exact hc

/-- The divisor of an integral power of a rational function is the multiple of its divisor. -/
private theorem principalDivisor_zpow {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    [IsNormal X] (φ : (RationalFunctions X)ˣ) (k : ℤ) :
    principalDivisor (φ ^ k) = k • principalDivisor φ := by
  ext P
  rw [DivisorWithCoeffs.coeff_smul, MMP.Mori.coeff_principalDivisor,
    MMP.Mori.coeff_principalDivisor, PrimeDivisor.ord_zpow]

/-- Multiples of linearly equivalent divisors are linearly equivalent. -/
private theorem linearlyEquivalent_zsmul {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D D' : Divisor X} (h : D.LinearlyEquivalent D') (n : ℤ) :
    (n • D).LinearlyEquivalent (n • D') := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ ^ n, by rw [← smul_sub, hφ, principalDivisor_zpow]⟩

/-- A birational morphism of integral schemes induces a finite extension of function fields. -/
private theorem finite_functionField_of_isBirationalMorphism {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {q : Y ⟶ X} (hq : IsBirationalMorphism q) [IsDominant q] :
    letI := functionFieldMapAlgebra q; Module.Finite X.functionField Y.functionField := by
  letI := functionFieldMapAlgebra q
  exact Module.Finite.of_surjective (Algebra.linearMap X.functionField Y.functionField)
    hq.functionFieldMap_bijective.2

/-- The value of the relative curve form of a `ℚ`-Cartier `ℚ`-divisor on the class of a
contracted curve is the sum defining relative nefness. -/
private theorem relativeCurveForm_relativeClass {X S : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (π : X ⟶ S) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (D : QDivisor X) (h : D.IsQCartier) (C : ProperCurve sX) (hC : C.IsContractedBy π) :
    QDivisor.relativeCurveForm sX π D h (C.relativeClass π hC) =
      (D.associatedCartier h).sum fun E c =>
        (c : ℝ) * ((E : Divisor X).degreeOn ℂ sX C.ι C.dim_le E.2 : ℝ) := by
  simp only [QDivisor.relativeCurveForm, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun E _ => ?_
  haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  congr 1
  rw [ProperCurve.relativeClass, RelativeNumericalCurveClasses.degree_relativeNumericalClass]
  exact_mod_cast OneCycle.degree_cycle ℝ _ C

/-- **A relatively nef `ℚ`-divisor is nonnegative on the closed relative cone of curves.** -/
private theorem relativeCurveForm_nonneg_of_isRelativelyNef {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (π : X ⟶ S) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {D : QDivisor X} (hnef : D.IsRelativelyNef sX π) (h : D.IsQCartier)
    {u : RelativeNumericalCurveClasses sX π} (hu : u ∈ relativeClosedConeOfCurves sX π) :
    0 ≤ QDivisor.relativeCurveForm sX π D h u := by
  obtain ⟨h', hnefC⟩ := hnef
  have hgen : ∀ (C : ProperCurve sX) (hCπ : C.IsContractedBy π),
      0 ≤ QDivisor.relativeCurveForm sX π D h (C.relativeClass π hCπ) := fun C hCπ => by
    rw [relativeCurveForm_relativeClass]
    exact hnefC C hCπ
  have hsum : ∀ {ι : Type} (s : Finset ι) (g : ι →
      RelativeNumericalCurveClasses sX π →ₗ[ℝ] ℝ), (∀ E ∈ s, Continuous (g E)) →
      Continuous ⇑(∑ E ∈ s, g E) := fun s g hg => by
    rw [show ⇑(∑ E ∈ s, g E) = fun u => ∑ E ∈ s, g E u from
      funext fun u => LinearMap.sum_apply _ _ _]
    exact continuous_finsetSum _ hg
  have hcont : Continuous (QDivisor.relativeCurveForm sX π D h) := by
    simp only [QDivisor.relativeCurveForm, Finsupp.sum]
    refine hsum _ _ fun E _ => ?_
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    exact (RelativeNumericalCurveClasses.continuous_degree sX π _).const_smul _
  have hcl : IsClosed {u | 0 ≤ QDivisor.relativeCurveForm sX π D h u} :=
    isClosed_le continuous_const hcont
  have hsub : (relativeConeOfCurves sX π : Set (RelativeNumericalCurveClasses sX π)) ⊆
      {u | 0 ≤ QDivisor.relativeCurveForm sX π D h u} := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hCπ⟩, rfl⟩ := hx
      exact hgen C hCπ
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      exact add_nonneg hx hy
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hu
  exact closure_minimal hsub hcl hu

/-- The lowered boundary `B - t⌊B⌋` of an effective dlt boundary `B`, for `0 ≤ t ≤ 1`, is
effective and lies below `B`. -/
private theorem zero_le_sub_smul_roundDown {X : Scheme.{0}} {B : QDivisor X}
    (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ B - t • Divisor.toQDivisor B.roundDown ∧ B - t • Divisor.toQDivisor B.roundDown ≤ B := by
  have hc : ∀ P, (B - t • Divisor.toQDivisor B.roundDown) P = B P - t * ⌊B P⌋ := fun P => by
    change (B - t • Divisor.toQDivisor B.roundDown).coeff P = B.coeff P - t * ⌊B.coeff P⌋
    simp
  refine ⟨Finsupp.le_def.mpr fun P => ?_, Finsupp.le_def.mpr fun P => ?_⟩
  · obtain ⟨h0, h1⟩ := hB P
    change 0 ≤ (B - t • Divisor.toQDivisor B.roundDown) P
    rw [hc]
    change 0 ≤ B.coeff P - t * ⌊B.coeff P⌋
    have hfl : (⌊B.coeff P⌋ : ℚ) ≤ B.coeff P := Int.floor_le _
    rcases lt_or_eq_of_le h1 with h | h
    · have : ⌊B.coeff P⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h⟩
      simp [this, h0]
    · rw [h]; simp; linarith
  · obtain ⟨h0, -⟩ := hB P
    rw [hc]
    have : (0 : ℚ) ≤ ⌊B P⌋ := by exact_mod_cast Int.floor_nonneg.mpr h0
    nlinarith

/-- **Running the program.** For `0 ≤ t ≤ 1` the pair `(X, B - t⌊B⌋)` is dlt, and the
projective threefold program for it over `Z` exists: it has finitely many steps and ends with a
nef adjoint or with a fibre-type contraction. -/
private theorem exists_program
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X}
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown),
      P.IsProjective ∧ P.n ≠ ⊤ ∧
      (MMP.Flips.IsRelativelyNef ℂ (modelStr sX P.sY P.n.toNat) (modelMap f P.πY P.n.toNat)
          (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
            divisorSeq (B - t • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat)) ∨
        P.hasFinal) := by
  have hdlt : MMP.Intersection.IsDltPair sX B :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKB.1.2.1 B).mpr hKB
  obtain ⟨h0, hle⟩ := zero_le_sub_smul_roundDown hKB.2.1 ht0 ht1
  have hdlt' : MMP.Intersection.IsDltPair sX (B - t • Divisor.toQDivisor B.roundDown) :=
    hdlt.of_le sX h0 hle (isQCartier_of_isQFactorial sX hX _)
  obtain ⟨-, hP⟩ := projectiveLowerLogMMP_three
  obtain ⟨-, -, hex⟩ := hP X Z sX sZ f K _ hXp hZ hf hX3.le hX ⟨3, hKB.1.2.1⟩ hdlt'
  exact hex

/-- A step index `i` with `i + 1 ≤ n` is a step of the program: `i < n`. -/
private theorem lt_of_succ_le {i : ℕ} {n : ℕ∞} (hi : ((i + 1 : ℕ) : ℕ∞) ≤ n) : (i : ℕ∞) < n :=
  (ENat.coe_lt_coe.mpr i.lt_succ_self).trans_le hi

/-- The lowering parameter `t < 1/(2(6m+1))` of the program is below one. -/
private theorem lt_one_of_lt_floorBound {t : ℚ} {m : ℕ} (h : t < 1 / (2 * (6 * m + 1))) : t < 1 :=
  h.trans_le (div_le_one_of_le₀ (by linarith [(m.cast_nonneg : (0 : ℚ) ≤ m)]) (by positivity))

/-- The birational transforms `D_i` of a `ℚ`-divisor `D` on the models of a program:
`D_0 = D` and `D_{i+1} = (φ_i)_* D_i`. -/
private noncomputable def transformSeq {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀)
    (D : QDivisor X) : ∀ i, QDivisor (modelSeq X P.Y i)
  | 0 => D
  | i + 1 => MMP.Mori.RationalMap.transformDivisor (P.φ i) (transformSeq P D i)

/-- The invariant of the `(K + B)`-trivial program on its model `X_i`: `L_i` is a Cartier divisor
with `L_i ∼ m(K_i + B_i)`, where `B_i` is the transform of `B`; the adjoint `K_i + B_i` is nef over
the base; and `(X_i, B_i - T_i)` is an effective klt pair, `T_i` the transform of `⌊B⌋`. -/
private def NullInv {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}
    {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sZ f K B₀) (B : QDivisor X)
    (m : ℕ) (i : ℕ) (Li : Divisor (modelSeq X P.Y i)) : Prop :=
  Li.IsCartier ∧
    (∃ u : (RationalFunctions (modelSeq X P.Y i))ˣ, Divisor.toQDivisor Li =
      (m : ℤ) • (Divisor.toQDivisor (divisorSeq K P.KY i) + transformSeq P B i) +
        Divisor.toQDivisor (principalDivisor u)) ∧
    (∃ _ : QuasiCompact (modelStr sX P.sY i),
      (Divisor.toQDivisor (divisorSeq K P.KY i) + transformSeq P B i).IsRelativelyNef
        (modelStr sX P.sY i) (modelMap f P.πY i)) ∧
    0 ≤ transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i ∧
    IsKltPair (modelStr sX P.sY i) 3 (divisorSeq K P.KY i)
      (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i)

/-- Two divisors satisfying the invariant on the same model are linearly equivalent. -/
private theorem NullInv.linearlyEquivalent {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X} {B₀ : QDivisor X}
    {P : RelativeDltProgram sX sZ f K B₀} {B : QDivisor X} {m i : ℕ}
    {L L' : Divisor (modelSeq X P.Y i)} (h : NullInv P B m i L) (h' : NullInv P B m i L') :
    L.LinearlyEquivalent L' := by
  obtain ⟨-, ⟨u, hu⟩, -⟩ := h
  obtain ⟨-, ⟨u', hu'⟩, -⟩ := h'
  refine ⟨u / u', Divisor.toQDivisor_injective ?_⟩
  rw [map_sub, hu, hu', principalDivisor_div, map_sub]
  abel

/-- **The invariant on the first model.** -/
private theorem nullInv_zero
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hX : IsQFactorial sX) {K : Divisor X} {B : QDivisor X}
    (hKB : IsDltPair sX 3 K B) {f : X ⟶ Z}
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {m : ℕ} {L₀ : Divisor X} (hL₀ : Divisor.toQDivisor L₀ =
      (m : ℤ) • (Divisor.toQDivisor K + B)) (hL₀c : L₀.IsCartier) {B₀ : QDivisor X}
    (P : RelativeDltProgram sX sZ f K B₀) : NullInv P B m 0 L₀ := by
  have hdlt : MMP.Intersection.IsDltPair sX B :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKB.1.2.1 B).mpr hKB
  obtain ⟨h0, hle⟩ := zero_le_sub_smul_roundDown hKB.2.1 zero_le_one le_rfl
  rw [one_smul] at h0 hle
  have hdlt' := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKB.1.2.1 _).mp
    (hdlt.of_le sX h0 hle (isQCartier_of_isQFactorial sX hX _))
  refine ⟨hL₀c, ⟨1, ?_⟩, ⟨inferInstanceAs (QuasiCompact sX), hnef⟩, h0,
    hdlt'.isKltPair_iff_roundDown_eq_zero.mpr ?_⟩
  · rw [Mori.principalDivisor_one, map_zero, add_zero]
    exact hL₀
  · ext P
    change ⌊(B - Divisor.toQDivisor B.roundDown).coeff P⌋ = 0
    simp [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_roundDown]

/-- The transforms along a program are linear: `(D - tE)_i = D_i - t E_i`. -/
private theorem transformSeq_sub_smul {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀)
    (D E : QDivisor X) (t : ℚ) :
    ∀ i, transformSeq P (D - t • E) i = transformSeq P D i - t • transformSeq P E i
  | 0 => rfl
  | i + 1 => by
    simp only [transformSeq]
    rw [transformSeq_sub_smul P D E t i, map_sub]
    congr 1
    have h := (MMP.Mori.RationalMap.transformDivisorₗ ℚ (R := ℚ) (P.φ i)).map_smul t
      (transformSeq P E i)
    rwa [MMP.Mori.RationalMap.transformDivisorₗ_apply,
      MMP.Mori.RationalMap.transformDivisorₗ_apply] at h

/-- The transforms along a program are additive: `(D + E)_i = D_i + E_i`. -/
private theorem transformSeq_add {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀)
    (D E : QDivisor X) : ∀ i, transformSeq P (D + E) i = transformSeq P D i + transformSeq P E i
  | 0 => rfl
  | i + 1 => by
    simp only [transformSeq]
    rw [transformSeq_add P D E i]
    exact map_add _ _ _

/-- The boundaries of a program are the transforms of the initial boundary. -/
private theorem divisorSeq_eq_transformSeq {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → divisorSeq B₀ P.BY i = transformSeq P B₀ i
  | 0, _ => rfl
  | i + 1, hi => by
    have hi' : (i : ℕ∞) < P.n := lt_of_succ_le hi
    change P.BY i = MMP.Mori.RationalMap.transformDivisor (P.φ i) (transformSeq P B₀ i)
    rw [P.BY_eq i hi', divisorSeq_eq_transformSeq P i hi'.le]

/-- **Coefficients along the program.** Every prime divisor `F'` of a model `X_i`, `i ≤ n`, is the
transform of a prime divisor `F₀` of `X`: the coefficient of `F'` in the transform `D_i` of any
`ℚ`-divisor `D` is the coefficient of `F₀` in `D`. -/
private theorem transformSeq_coeff {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∀ F' : MMP.Mori.PrimeDivisor (modelSeq X P.Y i),
      ∃ F₀ : MMP.Mori.PrimeDivisor X, ∀ D : QDivisor X, transformSeq P D i F' = D F₀
  | 0, _, F' => ⟨F', fun _ => rfl⟩
  | i + 1, hi, F' => by
    have hi' : (i : ℕ∞) < P.n := lt_of_succ_le hi
    obtain ⟨F, -, -, -, htr⟩ := step_coeff P i hi' F'
    obtain ⟨F₀, hF₀⟩ := transformSeq_coeff P i hi'.le F
    exact ⟨F₀, fun D => (htr (transformSeq P D i)).trans (hF₀ D)⟩

/-- On a `ℚ`-factorial variety the curve form is linear in the divisor:
`F = aD + bE` gives `(F · z) = a (D · z) + b (E · z)`. -/
private theorem curveForm_eq_smul_add_smul {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (hX : IsQFactorial sX) {D E F : QDivisor X} (a b : ℚ) (hF : F = a • D + b • E)
    (hFq : F.IsQCartier) (hDq : D.IsQCartier) (hEq : E.IsQCartier) :
    QDivisor.curveForm sX F hFq =
      (a : ℝ) • QDivisor.curveForm sX D hDq + (b : ℝ) • QDivisor.curveForm sX E hEq := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
  rw [intersectionNumber_congr sX C.ι C.dim_le hFq (isQCartier_of_isQFactorial sX hX _) hF,
    QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le _ _ (isQCartier_of_isQFactorial sX hX _)
      (isQCartier_of_isQFactorial sX hX _),
    intersectionNumber_smul sX C.ι C.dim_le D hDq a, intersectionNumber_smul sX C.ι C.dim_le E hEq b]
  push_cast
  ring

/-- The curve form of a Cartier divisor `L ∼ m D + div u` on the class of a curve `C` is the
degree of `𝒪_X(L)` on `C`, and equals `m (D · C)`. -/
private theorem degree_eq_smul_curveForm {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (hX : IsQFactorial sX) {L : Divisor X} (hL : L.IsCartier) {D : QDivisor X} (m : ℕ)
    (u : (RationalFunctions X)ˣ)
    (hLD : Divisor.toQDivisor L = (m : ℤ) • D + Divisor.toQDivisor (principalDivisor u))
    (hDq : D.IsQCartier) (C : ProperCurve sX) :
    haveI := (Divisor.mem_cartierSubgroup.mp hL).isInvertibleModule_divisorialSheaf
    (C.degree ℂ L.divisorialSheaf : ℝ) =
      m * QDivisor.curveForm sX D hDq (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, ProperCurve.degree_divisorialSheaf C L hL]
  have hu : (principalDivisor u).IsCartier := Divisor.isCartier_principalDivisor u
  have h0 : (principalDivisor u).degreeOn ℂ sX C.ι C.dim_le hu = 0 :=
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hu ⟨u, by simp⟩
  have h1 := QDivisor.intersectionNumber_toQDivisor ℂ sX C.ι C.dim_le L hL
    (isQCartier_of_isQFactorial sX hX _)
  rw [intersectionNumber_congr sX C.ι C.dim_le (isQCartier_of_isQFactorial sX hX _)
      (isQCartier_of_isQFactorial sX hX _) hLD,
    QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le _ _ (isQCartier_of_isQFactorial sX hX _)
      (isQCartier_of_isQFactorial sX hX _),
    QDivisor.intersectionNumber_toQDivisor ℂ sX C.ι C.dim_le _ hu, h0] at h1
  have h2 : ((m : ℤ) • D).intersectionNumber ℂ sX C.ι C.dim_le
      (isQCartier_of_isQFactorial sX hX _) = m * D.intersectionNumber ℂ sX C.ι C.dim_le hDq := by
    rw [intersectionNumber_congr sX C.ι C.dim_le _ (isQCartier_of_isQFactorial sX hX _)
      (show ((m : ℤ) • D) = (m : ℚ) • D by rw [← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl),
      intersectionNumber_smul sX C.ι C.dim_le D hDq]
  rw [h2] at h1
  have : ((L.degreeOn ℂ sX C.ι C.dim_le hL : ℤ) : ℚ) =
      m * D.intersectionNumber ℂ sX C.ι C.dim_le hDq := by
    rw [← h1]; push_cast; ring
  exact_mod_cast this

/-- **The ray of a step is `(K + B)`-trivial.** On the `i`-th step the ray `R_i` is negative for
`K_i + B_i - T_i` (as `K_i + B_i` is nef), and the klt length bound `-(K_i + B_i - T_i) · C ≤ 6`
on a rational generator `C` together with `m (K_i + B_i) · C ∈ ℤ` and the choice of `t` force
`(K_i + B_i) · R_i = 0`: every contracted curve with class in `R_i` has `deg_C L_i = 0`. -/
private theorem ray_null_of
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {m : ℕ} (hm : 0 < m)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) ≤ P.n) (Li : Divisor (modelSeq X P.Y i))
    (hLi : NullInv P B m i Li)
    (R : Set (RelativeNumericalCurveClasses (modelStr sX P.sY i) (modelMap f P.πY i)))
    (hR : IsNegativeRelativeExtremalRayOf (modelStr sX P.sY i) (modelMap f P.πY i)
      (Divisor.toQDivisor (divisorSeq K P.KY i) +
        divisorSeq (B - t • Divisor.toQDivisor B.roundDown) P.BY i) R) :
    (∀ z ∈ R, z ≠ 0 → ((MMP.Fourfold.QDivisor.curveForm (modelStr sX P.sY i)
        (Divisor.toQDivisor (divisorSeq K P.KY i) +
          (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i))
        hLi.2.2.2.2.1.2.2).comp (relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i))) z
          < 0) ∧
      ∀ (C : ProperCurve (modelStr sX P.sY i)) (hC : C.IsContractedBy (modelMap f P.πY i)),
        C.relativeClass (modelMap f P.πY i) hC ∈ R →
          haveI := (Divisor.mem_cartierSubgroup.mp hLi.1).isInvertibleModule_divisorialSheaf
          C.degree ℂ Li.divisorialSheaf = 0 := by
  rcases id hLi with ⟨hLc, ⟨u, hu⟩, ⟨hqc, hnefi⟩, hΔ0, hklt⟩
  have hmod := P.isRelativeDltModel i hi
  haveI := hqc
  have hXi : IsQFactorial (modelStr sX P.sY i) := hmod.isQFactorial
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (modelStr sX P.sY i) := hPproj.2 i hi
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hPproj.1
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  set D : QDivisor (modelSeq X P.Y i) :=
    Divisor.toQDivisor (divisorSeq K P.KY i) + transformSeq P B i with hDdef
  set E : QDivisor (modelSeq X P.Y i) := Divisor.toQDivisor (divisorSeq K P.KY i) +
    (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i) with hEdef
  have hqD : D.IsQCartier := isQCartier_of_isQFactorial _ hXi D
  have hqE : E.IsQCartier := hklt.1.2.2
  obtain ⟨hqDt, hRray, hRneg⟩ := hR
  have hDt : Divisor.toQDivisor (divisorSeq K P.KY i) +
      divisorSeq (B - t • Divisor.toQDivisor B.roundDown) P.BY i = (1 - t) • D + t • E := by
    rw [divisorSeq_eq_transformSeq P i hi, transformSeq_sub_smul, hDdef, hEdef]
    module
  have hform : ∀ z, QDivisor.relativeCurveForm (modelStr sX P.sY i) (modelMap f P.πY i) _ hqDt z
      = (1 - t) * QDivisor.curveForm _ D hqD (relativeToAbsolute _ _ z) +
        t * QDivisor.curveForm _ E hqE (relativeToAbsolute _ _ z) := fun z => by
    rw [QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply,
      curveForm_eq_smul_add_smul _ hXi (1 - t) t hDt _ hqD hqE]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hDnn : ∀ z ∈ R, 0 ≤ QDivisor.curveForm _ D hqD (relativeToAbsolute _ _ z) :=
    fun z hz => by
      have := relativeCurveForm_nonneg_of_isRelativelyNef _ _ hnefi hqD (hRray.1.1 hz)
      rwa [QDivisor.relativeCurveForm_eq_comp] at this
  have ht1' : (t : ℝ) < 1 := by exact_mod_cast lt_one_of_lt_floorBound ht1
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  have hneg : ∀ z ∈ R, z ≠ 0 →
      QDivisor.curveForm _ E hqE (relativeToAbsolute _ _ z) < 0 := fun z hz hz0 => by
    have h1 := hRneg z hz hz0
    rw [hform] at h1
    have h2 := hDnn z hz
    nlinarith
  refine ⟨fun z hz hz0 => hneg z hz hz0, ?_⟩
  -- the absolute ray and its rational generator
  have hR'ext := isExtremalRay_image_relativeToAbsolute (modelStr sX P.sY i) sZ
    (modelMap f P.πY i) hmod.comp_eq hRray
  have hR'neg : ∀ w ∈ relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i) '' R,
      w ≠ 0 → QDivisor.curveForm _ E hqE w < 0 := by
    rintro _ ⟨z, hz, rfl⟩ hw
    exact hneg z hz fun h => hw (by rw [h, map_zero])
  obtain ⟨Tc, -, hR'eq, hpos, hle⟩ :=
    exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed
      (modelStr sX P.sY i) hklt hΔ0 ⟨hqE, hR'ext, hR'neg⟩
  have hTmem : OneCycle.numericalClass _ (Tc.cycle ℝ) ∈
      relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i) '' R := by
    rw [hR'eq]; exact ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨z₀, hz₀, hz₀eq⟩ := hTmem
  have hz₀0 : z₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz₀eq
    rw [← hz₀eq, map_zero] at hpos
    simp at hpos
  -- `(K_i + B_i) · T = 0`
  have hDT : QDivisor.curveForm _ D hqD (OneCycle.numericalClass _ (Tc.cycle ℝ)) = 0 := by
    have hnn := hDnn z₀ hz₀
    have hDtneg := hRneg z₀ hz₀ hz₀0
    rw [hform] at hDtneg
    rw [hz₀eq] at hnn hDtneg
    have hint := degree_eq_smul_curveForm _ hXi hLc m u hu hqD Tc
    by_contra hd
    have hdpos := lt_of_le_of_ne hnn (Ne.symm hd)
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hmd : (1 : ℝ) ≤ m * QDivisor.curveForm _ D hqD (OneCycle.numericalClass _ (Tc.cycle ℝ)) := by
      haveI := (Divisor.mem_cartierSubgroup.mp hLc).isInvertibleModule_divisorialSheaf
      rw [← hint]
      have h0 : (0 : ℝ) < (Tc.degree ℂ Li.divisorialSheaf : ℝ) := hint ▸ mul_pos hm' hdpos
      have h0' : (0 : ℤ) < Tc.degree ℂ Li.divisorialSheaf := by exact_mod_cast h0
      exact_mod_cast (show (1 : ℤ) ≤ Tc.degree ℂ Li.divisorialSheaf from h0')
    have htm : (t : ℝ) * (2 * (6 * m + 1)) < 1 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℚ) < 2 * (6 * m + 1))).mp ht1
      exact_mod_cast this
    have he : -QDivisor.curveForm _ E hqE (OneCycle.numericalClass _ (Tc.cycle ℝ)) ≤ 6 := by
      have := hle; push_cast at this; linarith
    nlinarith [mul_le_mul_of_nonneg_left hmd (sub_nonneg.mpr ht1'.le)]
  -- hence `K_i + B_i` vanishes on the ray
  obtain ⟨v, hv0, hRv⟩ := hRray.2
  have hz₀v : z₀ ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := hRv ▸ hz₀
  obtain ⟨c₀, hc₀, rfl⟩ := hz₀v
  have hc₀0 : c₀ ≠ 0 := by rintro rfl; exact hz₀0 (zero_smul _ _)
  have hDv : QDivisor.curveForm _ D hqD (relativeToAbsolute _ _ v) = 0 := by
    rw [← hz₀eq, map_smul, map_smul, smul_eq_mul] at hDT
    exact (mul_eq_zero.mp hDT).resolve_left hc₀0
  intro C hC hCR
  have hCv : C.relativeClass (modelMap f P.πY i) hC ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} :=
    hRv ▸ hCR
  obtain ⟨c, -, hcv⟩ := hCv
  have hint := degree_eq_smul_curveForm _ hXi hLc m u hu hqD C
  have hCcl : OneCycle.numericalClass _ (C.cycle ℝ) =
      relativeToAbsolute _ _ (C.relativeClass (modelMap f P.πY i) hC) := rfl
  rw [hCcl, ← hcv, map_smul, map_smul, hDv, smul_zero, mul_zero] at hint
  exact_mod_cast hint

/-- **The ray of a step is `(K + B)`-trivial**: `ray_null_of` for the ray `R_i` of the `i`-th
step. -/
private theorem ray_null
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {m : ℕ} (hm : 0 < m)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) < P.n) (Li : Divisor (modelSeq X P.Y i))
    (hLi : NullInv P B m i Li) :
    (∀ z ∈ P.R i, z ≠ 0 → ((MMP.Fourfold.QDivisor.curveForm (modelStr sX P.sY i)
        (Divisor.toQDivisor (divisorSeq K P.KY i) +
          (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i))
        hLi.2.2.2.2.1.2.2).comp (relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i))) z
          < 0) ∧
      ∀ (C : ProperCurve (modelStr sX P.sY i)) (hC : C.IsContractedBy (modelMap f P.πY i)),
        C.relativeClass (modelMap f P.πY i) hC ∈ P.R i →
          haveI := (Divisor.mem_cartierSubgroup.mp hLi.1).isInvertibleModule_divisorialSheaf
          C.degree ℂ Li.divisorialSheaf = 0 :=
  ray_null_of sX sZ hXp hX hX3 hB hKB hZ f hf hm ht0 ht1 P hPproj i hi.le Li hLi (P.R i)
    (P.isElementaryDltStep i hi).isNegativeRelativeRayContraction.isNegativeRelativeExtremalRayOf

/-- An invertible sheaf on a normal integral scheme is the divisorial sheaf of a Cartier divisor:
the divisor of a rational section is principal near every point, where the sheaf is trivial. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (LY : Y.Modules)
    [hLY : Stacks.Ample.IsInvertibleModule Y LY] :
    ∃ N : Divisor Y, N.IsCartier ∧ Nonempty (N.divisorialSheaf ≅ LY) := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property LY := hLY
  obtain ⟨N, ⟨eN⟩⟩ := exists_divisorialSheaf_iso_of_isInvertible LY
  refine ⟨N, fun z => ?_, ⟨eN⟩⟩
  obtain ⟨U, hzU, ⟨eU⟩⟩ :=
    (AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit Y LY).mp inferInstance z
  obtain ⟨ψ, hψ⟩ := exists_isLocalEquation_of_restrict_iso_unit
    ((Scheme.Modules.restrictFunctor U.ι).mapIso eN ≪≫ eU)
  exact ⟨U, hzU, ψ, hψ⟩

/-- **Cartier descent along a `(K + B)`-trivial ray.** Let `g : X_i ⟶ T`, `g_T : T ⟶ Z`, be the
contraction over `Z` of a `(K_i + B_i - tT_i)`-negative extremal ray `R` on which `L_i` has degree
zero. The relative contraction theorem for the klt pair `(X_i, B_i - T_i)` descends `L_i` to a
Cartier divisor `N` on `T` with `g^* N ∼ L_i`. -/
private theorem cartier_descent_of
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    {K : Divisor X} {B : QDivisor X} (f : X ⟶ Z) {m : ℕ} {t : ℚ}
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) ≤ P.n) (Li : Divisor (modelSeq X P.Y i))
    (hLi : NullInv P B m i Li)
    (R : Set (RelativeNumericalCurveClasses (modelStr sX P.sY i) (modelMap f P.πY i)))
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)} (g : modelSeq X P.Y i ⟶ T) (gT : T ⟶ Z)
    (hc : IsNegativeRelativeRayContraction (modelStr sX P.sY i) (modelMap f P.πY i) sT
      (Divisor.toQDivisor (divisorSeq K P.KY i) +
        divisorSeq (B - t • Divisor.toQDivisor B.roundDown) P.BY i) R g gT)
    (hneg : ∀ z ∈ R, z ≠ 0 → ((MMP.Fourfold.QDivisor.curveForm (modelStr sX P.sY i)
        (Divisor.toQDivisor (divisorSeq K P.KY i) +
          (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i))
        hLi.2.2.2.2.1.2.2).comp (relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i))) z
          < 0)
    (hdeg : ∀ (C : ProperCurve (modelStr sX P.sY i)) (hC : C.IsContractedBy (modelMap f P.πY i)),
        C.relativeClass (modelMap f P.πY i) hC ∈ R →
          haveI := (Divisor.mem_cartierSubgroup.mp hLi.1).isInvertibleModule_divisorialSheaf
          C.degree ℂ Li.divisorialSheaf = 0)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [IsDominant g] :
    ∃ (N : Divisor T) (hNc : N.IsCartier)
      (hN : ∀ T' : irreducibleComponents (modelSeq X P.Y i),
        g (componentGenericPoint _ T') ∉ N.supp),
      (N.pullback hNc hN).LinearlyEquivalent Li := by
  have hmod := P.isRelativeDltModel i hi
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have hset : IsProjectiveSetting ℂ (modelStr sX P.sY i) sZ (modelMap f P.πY i) :=
    ⟨inferInstance, inferInstance, hPproj.2 i hi, hPproj.1, hmod.comp_eq⟩
  obtain ⟨hR, -⟩ := hc.isNegativeRelativeExtremalRayOf.choose_spec
  have hF : IsNegativeExtremalFace ℝ (relativeClosedConeOfCurves (modelStr sX P.sY i)
      (modelMap f P.πY i) : Set (RelativeNumericalCurveClasses _ _))
      ((MMP.Fourfold.QDivisor.curveForm (modelStr sX P.sY i)
        (Divisor.toQDivisor (divisorSeq K P.KY i) +
          (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i))
        hLi.2.2.2.2.1.2.2).comp (relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i)))
      R := by
    obtain ⟨hRf, v, -, hRv⟩ := hR
    refine ⟨hRf, fun u hu w hw => ?_, hneg⟩
    rw [hRv] at hu hw ⊢
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hw
    exact ⟨a + b, add_nonneg ha hb, add_smul a b v⟩
  haveI := (Divisor.mem_cartierSubgroup.mp hLi.1).isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace hset
    hLi.2.2.2.2 hLi.2.2.2.1 hF hc.isRelativeContractionOfFace Li.divisorialSheaf hdeg
  haveI : Stacks.Ample.IsInvertibleModule T LZ := hLZ
  obtain ⟨N, hNc, ⟨eN⟩⟩ := exists_isCartier_divisorialSheaf_iso LZ
  have hN := map_componentGenericPoint_notMem_supp_of_isDominant g N
  obtain ⟨e'⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := N) hNc g hN
  exact ⟨N, hNc, hN, MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e' ≪≫ (Scheme.Modules.pullback g).mapIso eN ≪≫ e.symm)⟩

/-- **Cartier descent along a `(K + B)`-trivial step.** The relative contraction theorem for the
klt pair `(X_i, B_i - T_i)` descends `L_i` to a Cartier divisor `N` on `Z_i` with
`f_i^* N ∼ L_i`. -/
private theorem cartier_descent
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    {K : Divisor X} {B : QDivisor X} (f : X ⟶ Z) {m : ℕ} {t : ℚ}
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) < P.n) (Li : Divisor (modelSeq X P.Y i))
    (hLi : NullInv P B m i Li)
    (hneg : ∀ z ∈ P.R i, z ≠ 0 → ((MMP.Fourfold.QDivisor.curveForm (modelStr sX P.sY i)
        (Divisor.toQDivisor (divisorSeq K P.KY i) +
          (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i))
        hLi.2.2.2.2.1.2.2).comp (relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i))) z
          < 0)
    (hdeg : ∀ (C : ProperCurve (modelStr sX P.sY i)) (hC : C.IsContractedBy (modelMap f P.πY i)),
        C.relativeClass (modelMap f P.πY i) hC ∈ P.R i →
          haveI := (Divisor.mem_cartierSubgroup.mp hLi.1).isInvertibleModule_divisorialSheaf
          C.degree ℂ Li.divisorialSheaf = 0)
    [IsIntegral (P.Z i)] [IsLocallyNoetherian (P.Z i)] [IsNormal (P.Z i)]
    [CompactSpace (P.Z i)] :
    ∃ (N : Divisor (P.Z i)) (hNc : N.IsCartier)
      (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
        P.f i (componentGenericPoint _ T) ∉ N.supp),
      (N.pullback hNc hN).LinearlyEquivalent Li := by
  obtain ⟨-, hfb, -⟩ := step_facts P i hi
  haveI : IsDominant (P.f i) := hfb.isDominant
  exact cartier_descent_of sX sZ f P hPproj i hi.le Li hLi (P.R i) (P.f i) (P.gZ i)
    (P.isElementaryDltStep i hi).isNegativeRelativeRayContraction hneg hdeg

/-- The target `Z_i` of the `i`-th contraction lies over `ℂ` compatibly with the base:
`g_i ≫ s_S = s_{Z_i}`, since `f_i` is dominant and both restrict to `s_{X_i}` along it. -/
private theorem gZ_comp_sS {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) : P.gZ i ≫ sS = P.sZ i := by
  have hstep := P.isElementaryDltStep i hi
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  obtain ⟨hZn, hfb, -, -, -, hfg, -⟩ := step_facts P i hi
  haveI : IsIntegral (P.Z i) := hZn.1.toIsIntegral
  haveI : IsDominant (P.f i) := hfb.isDominant
  have hm0 := P.isRelativeDltModel i hi.le
  refine ext_of_isDominant_of_isSeparated (Limits.terminal.from _)
    (Limits.terminal.hom_ext _ _) (P.f i) ?_
  rw [← Category.assoc, hfg, hm0.comp_eq, hctr.isContraction.comp_eq]

/-- The target `Z_i` of the `i`-th contraction lies over `ℂ` compatibly with `X_{i+1}`:
`f_i⁺ ≫ s_{Z_i} = s_{X_{i+1}}`. -/
private theorem fp_comp_sZ {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) : P.fp i ≫ P.sZ i = P.sY i := by
  rw [← gZ_comp_sS P i hi, ← Category.assoc, (P.isElementaryDltStep i hi).comp_eq]
  exact (P.isRelativeDltModel (i + 1) (Order.add_one_le_of_lt hi)).comp_eq

/-- A Cartier divisor of nonnegative degree on every curve contracted by `f` is `f`-nef as an
`ℝ`-divisor. -/
private theorem isRelativelyNef_toRDivisor_of_degreeOn_nonneg {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ (L.degreeOn k sX C.ι C.dim_le hL : ℝ)) :
    MMP.Flips.IsRelativelyNef k sX f (Divisor.toRDivisor L) := by
  refine ⟨1, fun _ => 1, fun _ => L, fun _ => hL, by simp, fun C hC x hx => ?_⟩
  have hx' := MMP.Flips.isRIntersectionNumber_sum C (fun _ : Fin 1 => (1 : ℝ)) (fun _ => L)
    (fun _ => hL) (D := Divisor.toRDivisor L) (by simp)
  rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hx']
  simpa using h C hC

/-- An `f`-nef Cartier divisor has nonnegative degree on every curve contracted by `f`. -/
private theorem degreeOn_nonneg_of_isRelativelyNef {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : MMP.Flips.IsRelativelyNef k sX f (Divisor.toRDivisor L)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 ≤ (L.degreeOn k sX C.ι C.dim_le hL : ℝ) := by
  obtain ⟨m, r, L', hL', hD, hall⟩ := h
  have hx := MMP.Flips.isRIntersectionNumber_sum C r L' hL' hD
  have hx' := MMP.Flips.isRIntersectionNumber_sum C (fun _ : Fin 1 => (1 : ℝ)) (fun _ => L)
    (fun _ => hL) (D := Divisor.toRDivisor L) (by simp)
  have := hall C hC _ hx
  rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hx'] at this
  simpa using this

/-- A Cartier divisor `L` is the `ℝ`-Cartier pull-back of `N` along `f` when `L = f^* N`. -/
private theorem isRCartierPullback_toRDivisor {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {N : Divisor Y}
    (hNc : N.IsCartier) {hN : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ N.supp}
    {L : Divisor X} (h : N.IsPullback f hN L) :
    MMP.Flips.IsRCartierPullback f (Divisor.toRDivisor N) (Divisor.toRDivisor L) :=
  ⟨1, fun _ => 1, fun _ => N, fun _ => L, fun _ => hNc, by simp, fun _ => ⟨hN, h⟩, by simp⟩

/-- On a `ℚ`-factorial variety, a nef `ℚ`-divisor `D` has `(D · C) ≥ 0` on each contracted curve,
read through the curve form. -/
private theorem curveForm_nonneg_of_isRelativelyNef {X S : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (π : X ⟶ S) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    {D : QDivisor X} (hnef : D.IsRelativelyNef sX π) (h : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy π) :
    0 ≤ QDivisor.curveForm sX D h (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  have := hnef.2 C hC
  rw [← relativeCurveForm_relativeClass sX π D hnef.1 C hC, QDivisor.relativeCurveForm_eq_comp]
    at this
  exact this

/-- **Linear equivalences across a step.** If `L_i ∼ n(K_i + Γ_i)` for the transform `Γ_i` of a
`ℚ`-divisor `Γ` on `X`, and `f_i^* N ∼ L_i` for a Cartier divisor `N` on `Z_i`, then
`(f_i⁺)^* N ∼ n(K_{i+1} + Γ_{i+1})`: push the relation forward by `φ_i`, using
`(φ_i)_* f_i^* = (f_i⁺)^*`, `(φ_i)_* K_i ∼ K_{i+1}` and that `φ_i` transforms principal divisors
pulled back from `Z_i` into principal divisors. -/
private theorem exists_eq_smul_add_of_step {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) [IsIntegral (P.Z i)] [IsLocallyNoetherian (P.Z i)] [IsNormal (P.Z i)]
    [CompactSpace (P.Z i)] (Γ : QDivisor X) {n : ℕ} {Li : Divisor (modelSeq X P.Y i)}
    (hLi : ∃ u : (RationalFunctions (modelSeq X P.Y i))ˣ, Divisor.toQDivisor Li =
      (n : ℤ) • (Divisor.toQDivisor (divisorSeq K P.KY i) + transformSeq P Γ i) +
        Divisor.toQDivisor (principalDivisor u))
    (N : Divisor (P.Z i)) (hNc : N.IsCartier)
    (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
      P.f i (componentGenericPoint _ T) ∉ N.supp)
    (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp)
    (hNL : (N.pullback hNc hN).LinearlyEquivalent Li) :
    ∃ u : (RationalFunctions (modelSeq X P.Y (i + 1)))ˣ,
      Divisor.toQDivisor (N.pullback hNc hN') =
        (n : ℤ) • (Divisor.toQDivisor (divisorSeq K P.KY (i + 1)) + transformSeq P Γ (i + 1)) +
          Divisor.toQDivisor (principalDivisor u) := by
  obtain ⟨-, -, -, hfpb, -, -, -⟩ := step_facts P i hi
  haveI : IsDominant (P.fp i) := hfpb.isDominant
  have hpb := Divisor.isPullback_pullback hNc hN'
  obtain ⟨u, hu⟩ := hLi
  obtain ⟨a, ha⟩ := hNL
  obtain ⟨hZn, hfb, -, -, -, -, -⟩ := step_facts P i hi
  haveI : IsDominant (P.f i) := hfb.isDominant
  -- `n (K_i + Γ_i) = f_i^* N + div c` with `c = (u a)⁻¹ = f_i^* v`
  obtain ⟨v, hv, hvc⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfb (u * a)⁻¹
  have hv' := map_componentGenericPoint_notMem_supp_of_isDominant (P.fp i) (principalDivisor v)
  have hvC := Divisor.isCartier_principalDivisor v
  have hNv : ∀ T : irreducibleComponents (modelSeq X P.Y i),
      P.f i (componentGenericPoint _ T) ∉ (N + principalDivisor v).supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant (P.f i) _
  have hNv' : ∀ T : irreducibleComponents (P.Y i),
      P.fp i (componentGenericPoint _ T) ∉ (N + principalDivisor v).supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant (P.fp i) _
  have hp₁ := (Divisor.isPullback_pullback hNc hN).add hNc hvC hNv
    (Divisor.isPullback_principalDivisor v hv)
  have hp₂ := hpb.add hNc hvC hNv' (Divisor.isPullback_principalDivisor v hv')
  have htr := transformDivisor_eq_of_isPullback P i hi (hNc.add hvC) hp₁ hp₂
  rw [hvc] at htr
  obtain ⟨s, hs⟩ := transformDivisor_linearlyEquivalent_canonical P i hi
  have hsK : MMP.Mori.RationalMap.transformDivisor (P.φ i) (divisorSeq K P.KY i) =
      P.KY i + principalDivisor s := by rw [← hs]; abel
  have hfN : N.pullback hNc hN = Li + principalDivisor a := by rw [← ha]; abel
  have h1 : Divisor.toQDivisor (N.pullback hNc hN + principalDivisor (u * a)⁻¹) =
      (n : ℤ) • (Divisor.toQDivisor (divisorSeq K P.KY i) + transformSeq P Γ i) := by
    rw [MMP.Mori.principalDivisor_inv, MMP.Mori.principalDivisor_mul, hfN, map_add, map_neg,
      map_add, map_add, hu]
    abel
  have h2 := congrArg (MMP.Mori.RationalMap.transformDivisor (P.φ i)) h1
  rw [transformDivisor_toQDivisor P i hi, htr, map_add, map_zsmul, map_add,
    transformDivisor_toQDivisor P i hi, hsK, map_add] at h2
  show ∃ u' : (RationalFunctions (P.Y i))ˣ, Divisor.toQDivisor (N.pullback hNc hN') =
    (n : ℤ) • (Divisor.toQDivisor (P.KY i) +
      MMP.Mori.RationalMap.transformDivisor (P.φ i) (transformSeq P Γ i)) +
      Divisor.toQDivisor (principalDivisor u')
  refine ⟨s ^ (n : ℤ) * (pullbackRationalFunction (P.fp i) v hv')⁻¹, ?_⟩
  rw [eq_sub_of_add_eq h2, MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv, principalDivisor_zpow,
    map_add, map_neg, map_zsmul]
  simp only [smul_add]
  abel

/-- **The invariant passes to the next model.** If `f_i^* N ∼ L_i` for a Cartier divisor `N` on
`Z_i`, then `(f_i⁺)^* N` satisfies the invariant on `X_{i+1}`: it is `∼ m(K_{i+1} + B_{i+1})`
since the step is an isomorphism in codimension one over `Z_i` (or contracts one divisor), the
adjoint stays nef over the base since curves on `Z_i` lift to `X_i`, and `(X_{i+1}, B_{i+1} -
T_{i+1})` stays klt since the step is also a step of the `(K_i + B_i - T_i)`-program. -/
private theorem nullInv_succ
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {m : ℕ} (hm : 0 < m)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) < P.n) (Li : Divisor (modelSeq X P.Y i))
    (hLi : NullInv P B m i Li)
    (hneg : ∀ z ∈ P.R i, z ≠ 0 → ((MMP.Fourfold.QDivisor.curveForm (modelStr sX P.sY i)
        (Divisor.toQDivisor (divisorSeq K P.KY i) +
          (transformSeq P B i - transformSeq P (Divisor.toQDivisor B.roundDown) i))
        hLi.2.2.2.2.1.2.2).comp (relativeToAbsolute (modelStr sX P.sY i) (modelMap f P.πY i))) z
          < 0)
    [IsIntegral (P.Z i)] [IsLocallyNoetherian (P.Z i)] [IsNormal (P.Z i)]
    [CompactSpace (P.Z i)] (N : Divisor (P.Z i)) (hNc : N.IsCartier)
    (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
      P.f i (componentGenericPoint _ T) ∉ N.supp)
    (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp)
    (hNL : (N.pullback hNc hN).LinearlyEquivalent Li) :
    NullInv P B m (i + 1) (N.pullback hNc hN') := by
  obtain ⟨-, -, -, hfpb, -, -, -⟩ := step_facts P i hi
  haveI : IsDominant (P.fp i) := hfpb.isDominant
  have hpb := Divisor.isPullback_pullback hNc hN'
  -- `(f_i⁺)^* N ∼ m (K_{i+1} + B_{i+1})`: the step transforms `f_i^* N` into `(f_i⁺)^* N`,
  -- `K_i` into a divisor linearly equivalent to `K_{i+1}` and principal divisors into principal
  -- divisors
  have hlin : ∃ u : (RationalFunctions (modelSeq X P.Y (i + 1)))ˣ,
      Divisor.toQDivisor (N.pullback hNc hN') =
        (m : ℤ) • (Divisor.toQDivisor (divisorSeq K P.KY (i + 1)) + transformSeq P B (i + 1)) +
          Divisor.toQDivisor (principalDivisor u) := by
    exact exists_eq_smul_add_of_step P i hi B (hLi.2.1) N hNc hN hN' hNL
  -- the adjoint stays nef over the base: curves of `Z_i` over the base lift to `X_i`
  have hnef : ∃ _ : QuasiCompact (modelStr sX P.sY (i + 1)),
      (Divisor.toQDivisor (divisorSeq K P.KY (i + 1)) + transformSeq P B (i + 1)).IsRelativelyNef
        (modelStr sX P.sY (i + 1)) (modelMap f P.πY (i + 1)) := by
    obtain ⟨u', hu'⟩ := hlin
    obtain ⟨-, ⟨u, hu⟩, ⟨hqc, hnefi⟩, -, -⟩ := hLi
    obtain ⟨a, ha⟩ := hNL
    obtain ⟨hZn, hfb, hfpp, -, -, hfg, hfpg⟩ := step_facts P i hi
    have hm0 := P.isRelativeDltModel i hi.le
    have hm1 := P.isRelativeDltModel (i + 1) (Order.add_one_le_of_lt hi)
    have hX1 : IsNormalVariety ℂ (P.sY i) := hm1.isQFactorial.1
    haveI : QuasiCompact (P.sY i) := hX1.1.toQuasiCompact
    haveI : LocallyOfFiniteType (P.sY i) := hX1.1.toLocallyOfFiniteType
    haveI := hqc
    haveI : LocallyOfFiniteType (modelStr sX P.sY i) := hm0.isQFactorial.1.1.toLocallyOfFiniteType
    haveI : IsSeparated (P.sZ i) := hZn.1.toIsSeparated
    haveI : LocallyOfFiniteType (P.sZ i) := hZn.1.toLocallyOfFiniteType
    haveI : QuasiCompact (P.sZ i) := hZn.1.toQuasiCompact
    haveI : IsDominant (P.f i) := hfb.isDominant
    haveI : IsProper (P.f i) := (P.isElementaryDltStep i hi).isNegativeRelativeRayContraction
      |>.isNegativeExtremalContraction.isContraction.isProper
    haveI : Surjective (P.f i) :=
      surjective_of_isDominant_of_isClosed_range _ ((P.f i).isClosedMap.isClosed_range)
    haveI := hfpp
    have hfps := fp_comp_sZ P i hi
    haveI : QuasiCompact (P.fp i ≫ P.sZ i) := by rw [hfps]; infer_instance
    have hfsZ : P.f i ≫ P.sZ i = modelStr sX P.sY i := (P.isElementaryDltStep i hi)
      |>.isNegativeRelativeRayContraction.isNegativeExtremalContraction.isContraction.comp_eq
    have hpb0 := Divisor.isPullback_pullback hNc hN
    have hc0 : (N.pullback hNc hN).IsCartier := isCartier_of_isPullback (P.f i) hNc hpb0
    have hc1 : (N.pullback hNc hN').IsCartier := isCartier_of_isPullback (P.fp i) hNc hpb
    -- `f_i^* N ∼ m (K_i + B_i)` has nonnegative degrees over the base
    have hfN : Divisor.toQDivisor (N.pullback hNc hN) = (m : ℤ) • (Divisor.toQDivisor
        (divisorSeq K P.KY i) + transformSeq P B i) +
          Divisor.toQDivisor (principalDivisor (u * a)) := by
      rw [MMP.Mori.principalDivisor_mul, map_add, ← add_assoc, ← hu, ← map_add, ← ha]
      abel_nf
    have hdeg0 : ∀ C : ProperCurve (modelStr sX P.sY i), C.IsContractedBy (P.f i ≫ P.gZ i) →
        0 ≤ ((N.pullback hNc hN).degreeOn ℂ _ C.ι C.dim_le hc0 : ℝ) := fun C hC => by
      rw [hfg] at hC
      have h1 := degree_eq_smul_curveForm _ hm0.isQFactorial hc0 m (u * a) hfN hnefi.1 C
      rw [ProperCurve.degree_divisorialSheaf C _ hc0] at h1
      rw [h1]
      exact mul_nonneg (Nat.cast_nonneg _)
        (curveForm_nonneg_of_isRelativelyNef _ _ hnefi hnefi.1 C hC)
    -- so `N` is nef over the base, and so is `(f_i⁺)^* N`
    have hNnef := MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective (P.f i) hfsZ
      (P.gZ i) (isRCartierPullback_toRDivisor hNc hpb0)
      (isRelativelyNef_toRDivisor_of_degreeOn_nonneg hc0 hdeg0)
    have hpull := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Z) (P.gZ i) (P.πY i)
      (P.fp i) (by rw [Category.comp_id, hfpg]) hNnef (isRCartierPullback_toRDivisor hNc hpb)
    have hpull' : MMP.Flips.IsRelativelyNef ℂ (P.sY i) (P.πY i)
        (Divisor.toRDivisor (N.pullback hNc hN')) := by
      convert hpull <;> exact hfps.symm
    have hdeg1 := degreeOn_nonneg_of_isRelativelyNef hc1 hpull'
    -- hence `K_{i+1} + B_{i+1}` is nef over the base
    have hX1q : IsQFactorial (modelStr sX P.sY (i + 1)) := hm1.isQFactorial
    haveI : QuasiCompact (modelStr sX P.sY (i + 1)) := hX1.1.toQuasiCompact
    have hq1 := isQCartier_of_isQFactorial (modelStr sX P.sY (i + 1)) hX1q
      (Divisor.toQDivisor (divisorSeq K P.KY (i + 1)) + transformSeq P B (i + 1))
    refine ⟨inferInstance, hq1, fun C hC => ?_⟩
    rw [← relativeCurveForm_relativeClass (modelStr sX P.sY (i + 1)) (modelMap f P.πY (i + 1)) _
      hq1 C hC, QDivisor.relativeCurveForm_eq_comp]
    change 0 ≤ QDivisor.curveForm (modelStr sX P.sY (i + 1)) _ hq1
      (OneCycle.numericalClass _ (C.cycle ℝ))
    have h1 := degree_eq_smul_curveForm (modelStr sX P.sY (i + 1)) hX1q hc1 m u' hu' hq1 C
    rw [ProperCurve.degree_divisorialSheaf C _ hc1] at h1
    have h2 := (hdeg1 C hC).trans_eq h1
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    exact (mul_nonneg_iff_of_pos_left hm').mp h2
  -- the transform of the effective `B_i - T_i` is effective
  have heff : 0 ≤ transformSeq P B (i + 1) -
      transformSeq P (Divisor.toQDivisor B.roundDown) (i + 1) := by
    have h := DivisorWithCoeffs.mapPrimeDivisors_nonneg
      (MMP.Mori.RationalMap.transformPrimeDivisor (P.φ i))
      hLi.2.2.2.1
    rw [map_sub] at h
    exact h
  -- the step is a step of the `(K_i + B_i - T_i)`-program, which preserves klt pairs
  have hklt : IsKltPair (modelStr sX P.sY (i + 1)) 3 (divisorSeq K P.KY (i + 1))
      (transformSeq P B (i + 1) - transformSeq P (Divisor.toQDivisor B.roundDown) (i + 1)) := by
    obtain ⟨-, -, -, -, hklti⟩ := hLi
    obtain ⟨hZn, hfb, -, hfpb', -, -, -⟩ := step_facts P i hi
    have hm1 := P.isRelativeDltModel (i + 1) (Order.add_one_le_of_lt hi)
    have hX1q : IsQFactorial (modelStr sX P.sY (i + 1)) := hm1.isQFactorial
    haveI : IsAlgClosed ℂ := Complex.isAlgClosed
    -- `X_{i+1}` is a threefold with canonical divisor `K_{i+1}`
    obtain ⟨n₁, hK₁⟩ := hm1.isCanonicalDivisor
    haveI : MMP.Mori.IsVariety ℂ (P.sZ i) := hZn.1
    haveI : MMP.Mori.IsVariety ℂ (modelStr sX P.sY (i + 1)) := hX1q.1.1
    haveI : MMP.Mori.IsVariety ℂ (modelStr sX P.sY i) := hklti.1.1.1
    have hdim : topologicalKrullDim (modelSeq X P.Y (i + 1)) = 3 := by
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sZ i)
        (modelStr sX P.sY (i + 1)) hfpb', MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sZ i)
        (modelStr sX P.sY i) hfb]
      exact hklti.1.2.1.1
    have hn₁ : n₁ = 3 := by
      have := hK₁.1
      rw [hdim] at this
      exact_mod_cast this.symm
    subst hn₁
    -- `B_{i+1} - T_{i+1} ≤ B_{i+1} - t T_{i+1}`, the boundary of the program, which is dlt
    have hcoef := transformSeq_coeff P (i + 1) (Order.add_one_le_of_lt hi)
    have hBt := divisorSeq_eq_transformSeq P (i + 1) (Order.add_one_le_of_lt hi)
    rw [transformSeq_sub_smul] at hBt
    have hdlt : MMP.Intersection.IsDltPair (modelStr sX P.sY (i + 1)) (transformSeq P B (i + 1) -
        t • transformSeq P (Divisor.toQDivisor B.roundDown) (i + 1)) := hBt ▸ hm1.isDltPair
    have ht1' : t ≤ 1 := (lt_one_of_lt_floorBound ht1).le
    have hle : transformSeq P B (i + 1) - transformSeq P (Divisor.toQDivisor B.roundDown) (i + 1)
        ≤ transformSeq P B (i + 1) -
          t • transformSeq P (Divisor.toQDivisor B.roundDown) (i + 1) := by
      refine Finsupp.le_def.mpr fun F' => ?_
      obtain ⟨F₀, hF₀⟩ := hcoef F'
      simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hF₀, hF₀]
      have h0 : (0 : ℚ) ≤ Divisor.toQDivisor B.roundDown F₀ := by
        change (0 : ℚ) ≤ ((⌊B.coeff F₀⌋ : ℤ) : ℚ)
        exact_mod_cast Int.floor_nonneg.mpr (hKB.2.1 F₀).1
      nlinarith
    have hdltΔ := hdlt.of_le (modelStr sX P.sY (i + 1)) heff hle (isQCartier_of_isQFactorial _ hX1q _)
    have hdltΔ' := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (modelStr sX P.sY (i + 1)) hK₁ _).mp hdltΔ
    refine hdltΔ'.isKltPair_iff_roundDown_eq_zero.mpr ?_
    refine DivisorWithCoeffs.ext' fun F' => ?_
    obtain ⟨F₀, hF₀⟩ := hcoef F'
    have h3 : (transformSeq P B (i + 1) -
        transformSeq P (Divisor.toQDivisor B.roundDown) (i + 1)).coeff F' =
          B.coeff F₀ - ((⌊B.coeff F₀⌋ : ℤ) : ℚ) := by
      rw [DivisorWithCoeffs.coeff_sub]
      exact congrArg₂ (· - ·) (hF₀ B) (hF₀ _)
    rw [DivisorWithCoeffs.coeff_roundDown, h3]
    simp [Int.floor_sub_intCast]
  exact ⟨isCartier_of_isPullback (P.fp i) hNc hpb, hlin, hnef, heff, hklt⟩

/-- **One step of the program is `(K + B)`-trivial.** If `L_i` satisfies the invariant on `X_i`
and `i < n`, there is a Cartier divisor `N` on `Z_i` with `f_i^* N ∼ L_i`, and `(f_i⁺)^* N`
satisfies the invariant on `X_{i+1}`. -/
private theorem step_null
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {m : ℕ} (hm : 0 < m)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) < P.n) (Li : Divisor (modelSeq X P.Y i))
    (hLi : NullInv P B m i Li) :
    ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i)) (_ : IsNormal (P.Z i))
      (_ : CompactSpace (P.Z i)) (N : Divisor (P.Z i)) (hNc : N.IsCartier)
      (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
        P.f i (componentGenericPoint _ T) ∉ N.supp)
      (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp),
      (N.pullback hNc hN).LinearlyEquivalent Li ∧ NullInv P B m (i + 1) (N.pullback hNc hN') := by
  obtain ⟨hZn, hfb, -, hfpb, -, -, -⟩ := step_facts P i hi
  haveI : IsIntegral (P.Z i) := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZn.2
  haveI : QuasiCompact (P.sZ i) := hZn.1.toQuasiCompact
  haveI : CompactSpace (P.Z i) := QuasiCompact.compactSpace_of_compactSpace (P.sZ i)
  haveI : IsDominant (P.fp i) := hfpb.isDominant
  obtain ⟨hneg, hdeg⟩ := ray_null sX sZ hXp hX hX3 hB hKB hZ f hf hm ht0 ht1 P hPproj i hi Li hLi
  obtain ⟨N, hNc, hN, hNL⟩ := cartier_descent sX sZ f P hPproj i hi Li hLi hneg hdeg
  have hN' := map_componentGenericPoint_notMem_supp_of_isDominant (P.fp i) N
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, N, hNc, hN, hN', hNL,
    nullInv_succ sX sZ hXp hX hX3 hB hKB hZ f hf hm ht0 ht1 P hPproj i hi Li hLi hneg N hNc hN hN'
      hNL⟩

/-- **Every step of the program is `(K + B)`-trivial.** Run the program for
`K + B - t⌊B⌋` over `Z` with `0 < t < 1/(2(6m+1))`, where `m(K + B) = L₀` is Cartier. There are
Cartier divisors `L_i` on the models, `L_0 = L₀` and `L_i ∼ m(K_i + B_i)` where `B_i` is the
transform of `B`, such that across each step `L_i ∼ f_i^* N_i` and `L_{i+1} ∼ (f_i⁺)^* N_i` for a
Cartier divisor `N_i` on the target `Z_i` of the contraction. -/
private theorem program_null
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {m : ℕ} (hm : 0 < m) {L₀ : Divisor X} (hL₀ : Divisor.toQDivisor L₀ =
      (m : ℤ) • (Divisor.toQDivisor K + B)) (hL₀c : L₀.IsCartier)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (hPn : P.n ≠ ⊤) :
    ∃ L : ∀ i, Divisor (modelSeq X P.Y i), L 0 = L₀ ∧
      (∀ i : ℕ, (i : ℕ∞) ≤ P.n → NullInv P B m i (L i)) ∧
      ∀ i : ℕ, (i : ℕ∞) < P.n → ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i))
        (_ : IsNormal (P.Z i)) (_ : CompactSpace (P.Z i)) (N : Divisor (P.Z i)) (hNc : N.IsCartier),
        ∃ (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
            P.f i (componentGenericPoint _ T) ∉ N.supp)
          (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp),
          (N.pullback hNc hN).LinearlyEquivalent (L i) ∧
            (N.pullback hNc hN').LinearlyEquivalent (L (i + 1)) := by
  classical
  -- the invariant holds on every model
  have hex : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ Li, NullInv P B m i Li := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨L₀, nullInv_zero sX hX hKB hnef hL₀ hL₀c P⟩
    | succ i ih =>
      intro hi
      have hi' : (i : ℕ∞) < P.n := lt_of_succ_le hi
      obtain ⟨Li, hLi⟩ := ih hi'.le
      obtain ⟨_, _, _, _, N, hNc, hN, hN', -, hinv⟩ := step_null sX sZ hXp hX hX3 hB hKB hZ f hf
        hm ht0 ht1 P hPproj i hi' Li hLi
      exact ⟨_, hinv⟩
  let L : ∀ i, Divisor (modelSeq X P.Y i)
    | 0 => L₀
    | i + 1 => if h : ((i + 1 : ℕ) : ℕ∞) ≤ P.n then (hex (i + 1) h).choose else 0
  have hL : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → NullInv P B m i (L i) := by
    intro i hi
    cases i with
    | zero => exact nullInv_zero sX hX hKB hnef hL₀ hL₀c P
    | succ i =>
      change NullInv P B m (i + 1) (if h : ((i + 1 : ℕ) : ℕ∞) ≤ P.n then _ else 0)
      rw [dif_pos hi]
      exact (hex (i + 1) hi).choose_spec
  refine ⟨L, rfl, hL, fun i hi => ?_⟩
  obtain ⟨h1, h2, h3, h4, N, hNc, hN, hN', hNL, hinv⟩ := step_null sX sZ hXp hX hX3 hB hKB hZ f hf
    hm ht0 ht1 P hPproj i hi (L i) (hL i hi.le)
  exact ⟨h1, h2, h3, h4, N, hNc, hN, hN', hNL,
    hinv.linearlyEquivalent (hL (i + 1) (Order.add_one_le_of_lt hi))⟩

/-- **Semiampleness descends along the program.** If across every step `L_i ∼ f_i^* N_i` and
`L_{i+1} ∼ (f_i⁺)^* N_i` for Cartier divisors `N_i` on the targets `Z_i`, and a multiple of the
last `L_n` is relatively free over the base, then so is a multiple of `L_0`. -/
private theorem descend_program
    {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Z} {K : Divisor X}
    {B₀ : QDivisor X} (P : RelativeDltProgram sX sZ f K B₀) (hPproj : P.IsProjective)
    (hPn : P.n ≠ ⊤) (L : ∀ i, Divisor (modelSeq X P.Y i))
    (hLc : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → (L i).IsCartier)
    (hstep : ∀ i : ℕ, (i : ℕ∞) < P.n → ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i))
        (_ : IsNormal (P.Z i)) (_ : CompactSpace (P.Z i)) (N : Divisor (P.Z i)) (hNc : N.IsCartier),
        ∃ (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
            P.f i (componentGenericPoint _ T) ∉ N.supp)
          (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp),
          (N.pullback hNc hN).LinearlyEquivalent (L i) ∧
            (N.pullback hNc hN').LinearlyEquivalent (L (i + 1)))
    (hfree : ∃ k : ℕ, 0 < k ∧
      IsRelativelyFreeDivisor (modelMap f P.πY P.n.toNat) ((k : ℤ) • L P.n.toNat)) :
    ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor f ((k : ℤ) • L 0) := by
  have key : ∀ d j : ℕ, j + d = P.n.toNat → ∃ k : ℕ, 0 < k ∧
      IsRelativelyFreeDivisor (modelMap f P.πY j) ((k : ℤ) • L j) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      exact hfree
    | succ d ih =>
      intro j hj
      have hjn : (j : ℕ∞) < P.n := by
        rw [← ENat.coe_toNat hPn]
        exact_mod_cast (show j < P.n.toNat by omega)
      obtain ⟨k, hk, hkf⟩ := ih (j + 1) (by omega)
      obtain ⟨hZ, hfb, hfpp, hfpb, hYn, hfg, hfpg⟩ := step_facts P j hjn
      obtain ⟨_, _, _, _, N, hNc, hN, hN', h1, h2⟩ := hstep j hjn
      haveI : IsDominant (P.f j) := hfb.isDominant
      haveI : IsDominant (P.fp j) := hfpb.isDominant
      haveI := hfpp
      -- `k (f_j⁺)^* N` is relatively free over the base
      have hpb' := (Divisor.isPullback_pullback hNc hN').zsmul hNc (k : ℤ)
        (map_componentGenericPoint_notMem_supp_of_isDominant (P.fp j) _)
      have hfree' : IsRelativelyFreeDivisor (P.fp j ≫ P.gZ j)
          ((k : ℤ) • N.pullback hNc hN') := by
        rw [hfpg]
        exact IsRelativelyFreeDivisor.of_linearlyEquivalent _ (linearlyEquivalent_zsmul h2 (k : ℤ)).symm hkf
      -- so a multiple of `k N` is relatively free over the base
      obtain ⟨e, he, hef⟩ := exists_isRelativelyFreeDivisor_zsmul_of_isRelativelyFreeDivisor_pullback
        (P.fp j ≫ P.sZ j) (P.sZ j) hYn hZ (P.fp j) rfl
        (finite_functionField_of_isBirationalMorphism hfpb) (P.gZ j) (hNc.zsmul _) hpb' hfree'
      -- and its pull-back to `X_j`
      have hpb := ((Divisor.isPullback_pullback hNc hN).zsmul hNc (k : ℤ)
        (map_componentGenericPoint_notMem_supp_of_isDominant (P.f j) _)).zsmul (hNc.zsmul _)
        (e : ℤ) (map_componentGenericPoint_notMem_supp_of_isDominant (P.f j) _)
      have hfj := IsRelativelyFreeDivisor.of_isPullback (P.f j) (P.gZ j)
        ((hNc.zsmul _).zsmul _) hpb hef
      rw [hfg] at hfj
      refine ⟨e * k, Nat.mul_pos he hk, ?_⟩
      have hle := linearlyEquivalent_zsmul (linearlyEquivalent_zsmul h1 (k : ℤ)) (e : ℤ)
      rw [smul_smul, smul_smul] at hle
      rw [smul_smul] at hfj
      push_cast
      exact IsRelativelyFreeDivisor.of_linearlyEquivalent _ hle hfj
  exact key P.n.toNat 0 (by omega)

/-! ### The horizontal floor along the program -/

/-- The closure of the image `g(x)` of a point has dimension at most that of the closure of `x`:
transcendence degrees of residue fields only drop along `g`. -/
private theorem topologicalKrullDim_closure_map_le {V W : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (sW : W ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sV] [LocallyOfFiniteType sW] (g : V ⟶ W)
    (hg : g ≫ sW = sV) (x : V) :
    topologicalKrullDim (closure {g x} : Set W) ≤ topologicalKrullDim (closure {x} : Set V) := by
  rw [topologicalKrullDim_closure_singleton_eq_trdeg ℂ W sW,
    topologicalKrullDim_closure_singleton_eq_trdeg ℂ V sV, WithBot.coe_le_coe]
  exact Cardinal.toENat.monotone' (MMP.Flips.trdeg_residueField_add sV sW g hg x ▸ le_self_add)

/-- A prime divisor with dense image lies over the generic point of the integral target. -/
private theorem map_genericPoint_eq_of_dense_image {X Z : Scheme.{0}} [IsIntegral Z] (f : X ⟶ Z)
    (E : MMP.Mori.PrimeDivisor X) (hEd : Dense (f '' (E.support : Set X))) :
    f E.genericPoint = genericPoint Z := by
  have hcl : closure ({f E.genericPoint} : Set Z) = ⊤ := by
    refine Set.eq_univ_of_forall fun w => ?_
    have hsub : f '' (E.support : Set X) ⊆ closure {f E.genericPoint} := by
      rintro _ ⟨y, hy, rfl⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
      exact specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hy).map f.continuous)
    exact closure_minimal hsub isClosed_closure
      (by rw [hEd.closure_eq]; trivial : w ∈ closure (f '' (E.support : Set X)))
  exact ((genericPoint_spec Z).eq (show IsGenericPoint (f E.genericPoint) ⊤ from hcl)).symm

/-- **The horizontal floor along the program.** Let `E` be a prime divisor of `X` lying over the
generic point of the surface `Z`. Every model `X_i`, `i ≤ n`, has a prime divisor `E_i` over the
generic point of `Z` with the coefficients of `E`: the image of `η_{E_i}` in `Z_i` has closure of
dimension two, hence is the generic point of a prime divisor `Q` of the threefold `Z_i`, over
which `X_{i+1}` has a prime divisor. -/
private theorem exists_horizontal_floor {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hZ : Mori.IsProjectiveVariety ℂ sZ) (hZ2 : topologicalKrullDim Z = 2) {f : X ⟶ Z}
    {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sZ f K B₀)
    (hdim : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → topologicalKrullDim (modelSeq X P.Y i) = 3)
    (E : MMP.Mori.PrimeDivisor X) (hE : f E.genericPoint = genericPoint Z) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ Ei : MMP.Mori.PrimeDivisor (modelSeq X P.Y i),
      modelMap f P.πY i Ei.genericPoint = genericPoint Z ∧
        ∀ D : QDivisor X, transformSeq P D i Ei = D E
  | 0, _ => ⟨E, hE, fun _ => rfl⟩
  | i + 1, hi => by
    have hi' : (i : ℕ∞) < P.n := lt_of_succ_le hi
    obtain ⟨Ei, hEi, hcoef⟩ := exists_horizontal_floor hZ hZ2 P hdim E hE i hi'.le
    obtain ⟨hZn, hfb, hfpp, hfpb, hYn, hfg, hfpg⟩ := step_facts P i hi'
    haveI : IsIntegral (P.Z i) := hZn.1.toIsIntegral
    haveI : LocallyOfFiniteType (P.sZ i) := hZn.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
    haveI : IsNormal (P.Z i) := hZn.2
    haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
    haveI : IsIntegral Z := hZ.toIsVariety.toIsIntegral
    have hctr := (P.isElementaryDltStep i hi').isNegativeRelativeRayContraction
      |>.isNegativeExtremalContraction
    haveI : IsProper (P.f i) := hctr.isContraction.isProper
    haveI : IsDominant (P.f i) := hfb.isDominant
    have hfs : P.f i ≫ P.sZ i = modelStr sX P.sY i := hctr.isContraction.comp_eq
    have hgs := gZ_comp_sS P i hi'
    have hX0 : IsNormalVariety ℂ (modelStr sX P.sY i) :=
      (P.isRelativeDltModel i hi'.le).isQFactorial.1
    set y := P.f i Ei.genericPoint with hy
    have hgy : P.gZ i y = genericPoint Z := by
      rw [hy, ← Scheme.Hom.comp_apply, hfg]; exact hEi
    -- the closure of `y` has dimension two
    have h2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure {y} : Set (P.Z i)) := by
      have h := topologicalKrullDim_closure_map_le (P.sZ i) sZ (P.gZ i) hgs y
      have hZ' : topologicalKrullDim (closure {genericPoint Z} : Set Z) = 2 := by
        rw [(genericPoint_spec Z).def, ← hZ2]
        exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Z).isHomeomorph
      rwa [hgy, hZ'] at h
    -- `Z_i` is a threefold, so `y` has coheight one
    haveI : MMP.Mori.IsVariety ℂ (P.sZ i) := hZn.1
    haveI : MMP.Mori.IsVariety ℂ (modelStr sX P.sY i) := hX0.1
    have hdZ : topologicalKrullDim (P.Z i) = 3 := by
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sZ i)
        (modelStr sX P.sY i) hfb]
      exact hdim i hi'.le
    have hco := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (P.sZ i) y
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, topologicalKrullDim (closure {y} : Set (P.Z i)) = d :=
      ⟨_, topologicalKrullDim_closure_singleton_eq_trdeg ℂ (P.Z i) (P.sZ i) y⟩
    rw [hdZ, hd] at hco
    rw [hd] at h2
    have hco' : d + Order.coheight y = 3 := by
      have : ((d + Order.coheight y : ℕ∞) : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := by
        push_cast; exact hco
      exact WithBot.coe_injective this
    have h2' : (2 : ℕ∞) ≤ d := by
      have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by push_cast; exact h2
      exact WithBot.coe_le_coe.mp this
    have hc1 : Order.coheight y ≤ 1 := by
      by_contra hc
      have hc2 : (2 : ℕ∞) ≤ Order.coheight y := Order.add_one_le_of_lt (not_le.mp hc)
      have := add_le_add h2' hc2
      rw [hco'] at this
      exact absurd this (by norm_num)
    have hc1' : 1 ≤ Order.coheight y := by
      have := MMP.Flips.coheight_le_coheight_map (P.sZ i) (modelStr sX P.sY i) hZn.1 hX0.1
        (P.f i) hfs (by rw [hdZ]; exact hdim i hi'.le) Ei.genericPoint
      rwa [Ei.coheight_genericPoint] at this
    have hco1 : Order.coheight y = 1 := le_antisymm hc1 hc1'
    set Q : MMP.Mori.PrimeDivisor (P.Z i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco1
    have hQ : Q.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    -- a prime divisor of `X_{i+1}` over `Q`
    obtain ⟨E', hE', -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
        hZn (f := P.fp i) hYn hfpb Q
    obtain ⟨F, Q', hF, hF', htr⟩ := step_coeff P i hi' E'
    have hQQ : Q'.genericPoint = Q.genericPoint := hF'.symm.trans hE'
    have := Q.isDiscreteValuationRing_localRing
    have hFE : F = Ei := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_valuationRing hfb.functionFieldMap_bijective (y := Q.genericPoint)
        (hF.trans hQQ) hQ.symm)
    refine ⟨E', ?_, fun D => ?_⟩
    · change P.πY i E'.genericPoint = _
      rw [← hfpg, Scheme.Hom.comp_apply, hE', hQ, hgy]
    · change MMP.Mori.RationalMap.transformDivisor (P.φ i) (transformSeq P D i) E' = D E
      rw [htr, hFE, hcoef]

/-- Two distinct points of a `T₀` space, one specializing to the other, give a chain
`{b}⁻ ⊊ {a}⁻` of irreducible closed subsets: the space has dimension at least one. -/
private theorem one_le_topologicalKrullDim_of_specializes {T : Type*} [TopologicalSpace T]
    [T0Space T] {a b : T} (hab : a ⤳ b) (hne : a ≠ b) :
    (1 : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  let A : TopologicalSpace.IrreducibleCloseds T :=
    ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : TopologicalSpace.IrreducibleCloseds T :=
    ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hBA : B < A := by
    refine lt_of_le_of_ne (show closure {b} ⊆ closure {a} from closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hab)) isClosed_closure) ?_
    intro h
    have h' : closure ({b} : Set T) = closure {a} :=
      congrArg (fun S : TopologicalSpace.IrreducibleCloseds T => (S : Set T)) h
    exact hne (inseparable_iff_closure_eq.mpr h'.symm).eq
  let s : LTSeries (TopologicalSpace.IrreducibleCloseds T) :=
    ⟨1, ![B, A], fun i => by fin_cases i; exact hBA⟩
  exact_mod_cast Order.LTSeries.length_le_krullDim s

/-- **A fibre curve through the floor avoiding finitely many divisors.** Let `p : X ⟶ Z` be a
proper morphism from a threefold onto a surface, `E` a prime divisor of `X` over the generic
point of `Z`, and `S` a finite set of prime divisors. There are a closed point `x ∈ E` and a
generization `ξ ≠ x` of `x` with `{ξ}⁻` in the fibre of `p(x)`, lying on no divisor of `S`.

Each `Γ ∈ S` either maps to a proper closed subset of `Z`, or dominates `Z`, and then over a dense
open subset of `Z` its fibres are finite; outside these finitely many closed subsets choose a
closed point `z`, a closed point `x` of `E` over `z`, and `ξ` the generic point of a component of
the fibre through `x`, of dimension at least `dim X - dim Z = 1`. -/
private theorem exists_fibre_specialization {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) [CompactSpace X] (hXv : MMP.Mori.IsVariety ℂ sX)
    (hZv : MMP.Mori.IsVariety ℂ sZ) (p : X ⟶ Z) [IsProper p] (hp : p ≫ sZ = sX)
    (hX3 : topologicalKrullDim X = 3) (hZ2 : topologicalKrullDim Z = 2)
    (E : MMP.Mori.PrimeDivisor X) (hE : p E.genericPoint = genericPoint Z)
    (S : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ ξ x : X, ξ ⤳ x ∧ IsClosed ({x} : Set X) ∧ x ∈ (E.support : Set X) ∧
      (∀ Γ ∈ S, ξ ∉ (Γ.support : Set X)) ∧ ∀ y : X, ξ ⤳ y → p y = p ξ := by
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXv
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have hgenZ : ∀ z : Z, z ∈ closure ({genericPoint Z} : Set Z) := fun z => by
    rw [(genericPoint_spec Z).def]; trivial
  -- a point specializing to the generic point is the generic point
  have hgen_eq : ∀ w : Z, genericPoint Z ∈ closure ({w} : Set Z) → w = genericPoint Z := by
    intro w hw
    have hcl : closure ({w} : Set Z) = ⊤ := by
      refine Set.eq_univ_of_forall fun z => ?_
      exact closure_minimal (Set.singleton_subset_iff.mpr hw) isClosed_closure (hgenZ z)
    exact ((genericPoint_spec Z).eq (show IsGenericPoint w ⊤ from hcl)).symm
  haveI : IsDominant p := ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_forall fun z =>
    closure_mono (Set.singleton_subset_iff.mpr
      (show genericPoint Z ∈ Set.range p from ⟨_, hE⟩)) (hgenZ z))⟩
  -- (A) the bad locus of each prime divisor
  have hbad : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ W : Set Z, IsClosed W ∧ genericPoint Z ∉ W ∧
      ∀ a b : X, a ∈ (Γ.support : Set X) → a ⤳ b → a ≠ b → p a = p b → p b ∈ W := by
    intro Γ
    have hΓcl : (Γ.support : Set X) = closure {Γ.genericPoint} :=
      AlgebraicGeometry.PrimeDivisor.support_eq_closure Γ
    by_cases hΓ : p Γ.genericPoint = genericPoint Z
    · -- `Γ` dominates `Z`: over a dense open `V`, its fibres have dimension zero
      set x₀ := Γ.genericPoint
      haveI : IsIntegral (MMP.Mori.curveSubschemeAt x₀) :=
        MMP.Fourfold.isIntegral_subscheme_vanishingIdeal _ isIrreducible_singleton.closure
      set ι := MMP.Mori.curveSubschemeAtι x₀
      haveI hΓv : AlgebraicGeometry.IsVariety ℂ (ι ≫ sX) :=
        { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
          toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
      set q := ι ≫ p with hq
      have hqs : q ≫ sZ = ι ≫ sX := by rw [hq, Category.assoc, hp]
      have hgen : ι (genericPoint (MMP.Mori.curveSubschemeAt x₀)) = x₀ :=
        Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x₀
      haveI : IsDominant q := ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_forall fun z =>
        closure_mono (Set.singleton_subset_iff.mpr
          (show genericPoint Z ∈ Set.range q from
            ⟨genericPoint (MMP.Mori.curveSubschemeAt x₀), by
              rw [hq, Scheme.Hom.comp_apply, hgen, hΓ]⟩)) (hgenZ z))⟩
      have hdΓ : topologicalKrullDim (MMP.Mori.curveSubschemeAt x₀) = 2 := by
        rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq]
        have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x₀
        rw [Γ.coheight_genericPoint, hX3] at h
        obtain ⟨d, hd⟩ : ∃ d : ℕ∞, topologicalKrullDim (closure {x₀} : Set X) = d :=
          ⟨_, topologicalKrullDim_closure_singleton_eq_trdeg ℂ X sX x₀⟩
        rw [hd] at h ⊢
        have h' : d + 1 = 3 := by
          have : ((d + 1 : ℕ∞) : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := by
            push_cast; exact h
          exact WithBot.coe_injective this
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = d := ENat.ne_top_iff_exists.mp (by
          rintro rfl; simp at h')
        have hn : n + 1 = 3 := by exact_mod_cast h'
        obtain rfl : n = 2 := by omega
        rfl
      obtain ⟨-, ⟨V, hVd, hV⟩, -⟩ := MMP.topologicalKrullDim_fiber_of_isDominant ℂ (ι ≫ sX) sZ q hqs
      have hVgen : genericPoint Z ∈ V := by
        obtain ⟨v, hv⟩ := hVd.nonempty
        exact ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr ⟨v, trivial, hv⟩
      refine ⟨(V : Set Z)ᶜ, V.isOpen.isClosed_compl, fun h => h hVgen,
        fun a b ha hab hne hpab hbV => ?_⟩
      have hrange : Set.range ι = closure ({x₀} : Set X) := MMP.Mori.range_curveSubschemeAtι x₀
      have hb : b ∈ (Γ.support : Set X) := hab.mem_closed (hΓcl ▸ isClosed_closure) ha
      obtain ⟨a', rfl⟩ : a ∈ Set.range ι := hrange ▸ (hΓcl ▸ ha)
      obtain ⟨b', rfl⟩ : b ∈ Set.range ι := hrange ▸ (hΓcl ▸ hb)
      have hab' : a' ⤳ b' := ι.isClosedEmbedding.isInducing.specializes_iff.mp hab
      have hne' : a' ≠ b' := fun h => hne (h ▸ rfl)
      have hqa : a' ∈ ⇑q ⁻¹' {q b'} := by
        change (ι ≫ p) a' = (ι ≫ p) b'
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hpab
      let e := q.fiberHomeo (q b')
      set α := e.symm ⟨a', hqa⟩
      set β := e.symm ⟨b', rfl⟩
      have hαβ : α ⤳ β :=
        (Topology.IsInducing.subtypeVal.specializes_iff.mp hab').map e.symm.continuous
      have hαβne : α ≠ β := fun h => hne' (congrArg Subtype.val (e.symm.injective h))
      obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
        (closure {α}) isIrreducible_singleton.closure
      have hαC : α ∈ C := hsub (subset_closure rfl)
      have hβC : β ∈ C := hsub (specializes_iff_mem_closure.mp hαβ)
      have h1 := one_le_topologicalKrullDim_of_specializes (T := C) (a := ⟨α, hαC⟩)
        (b := ⟨β, hβC⟩) (Topology.IsInducing.subtypeVal.specializes_iff.mp hαβ)
        (fun h => hαβne (congrArg Subtype.val h))
      have h2 := hV (q b') (by
        change (ι ≫ p) b' ∈ V
        rw [Scheme.Hom.comp_apply]; exact hbV) C hC
      rw [hZ2, hdΓ] at h2
      have h3 : (1 : WithBot ℕ∞) + 2 ≤ topologicalKrullDim C + 2 := add_le_add h1 le_rfl
      rw [h2] at h3
      exact absurd h3 (by decide)
    · refine ⟨closure {p Γ.genericPoint}, isClosed_closure, fun h => hΓ (hgen_eq _ h),
        fun a b ha hab _ _ => ?_⟩
      have hb : b ∈ closure ({Γ.genericPoint} : Set X) :=
        hab.mem_closed isClosed_closure (hΓcl ▸ ha)
      exact specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hb).map p.continuous)
  choose W hWcl hWgen hWbad using hbad
  -- (B) a closed point `z` of `Z` outside the bad loci
  set W₀ : Set Z := ⋃ Γ ∈ S, W Γ with hW₀
  have hW₀cl : IsClosed W₀ := isClosed_biUnion_finset fun Γ _ => hWcl Γ
  have hW₀gen : genericPoint Z ∉ W₀ := by
    simp only [hW₀, Set.mem_iUnion, not_exists]
    exact fun Γ _ => hWgen Γ
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  obtain ⟨z, ⟨hzW, hzcl⟩⟩ := (jacobsonSpace_iff_locallyClosed.mp inferInstance) W₀ᶜ
    ⟨_, hW₀gen⟩ hW₀cl.isOpen_compl.isLocallyClosed
  -- (C) a closed point `x` of `E` over `z`
  have hEsurj : p '' (E.support : Set X) = Set.univ := by
    have hEcl : IsClosed (E.support : Set X) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    have hcl : IsClosed (p '' (E.support : Set X)) := p.isClosedMap _ hEcl
    refine Set.eq_univ_of_forall fun w => ?_
    refine closure_minimal (Set.singleton_subset_iff.mpr
      (show genericPoint Z ∈ p '' (E.support : Set X) from ⟨E.genericPoint, ?_, hE⟩)) hcl
      (hgenZ w)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hEz : IsClosed ((E.support : Set X) ∩ p ⁻¹' {z}) := by
    refine IsClosed.inter ?_ (hzcl.preimage p.continuous)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  obtain ⟨x, ⟨hxE, hxz⟩, hxcl⟩ := hEz.exists_closed_singleton (by
    obtain ⟨x, hx, hxz⟩ := (Set.eq_univ_iff_forall.mp hEsurj) z
    exact ⟨x, hx, hxz⟩)
  -- (D) a generization `ξ` of `x` in the fibre
  obtain ⟨hlow, -, -⟩ := MMP.topologicalKrullDim_fiber_of_isDominant ℂ sX sZ p hp
  have hxz' : x ∈ p ⁻¹' {z} := hxz
  let e := p.fiberHomeo z
  set β := e.symm ⟨x, hxz'⟩ with hβ
  obtain ⟨C, hC, hβC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {β} isIrreducible_singleton
  have hβC' : β ∈ C := hβC rfl
  obtain ⟨α, hα⟩ := QuasiSober.sober hC.prop
    (isClosed_of_mem_irreducibleComponents C hC)
  have hαβ : α ⤳ β := hα.specializes hβC'
  have hdimC := hlow z C hC
  rw [hX3, hZ2] at hdimC
  -- `α ≠ β`, as the component `C` has dimension at least one
  have h1 : IsClosed ({(⟨x, hxz'⟩ : p ⁻¹' {z})} : Set (p ⁻¹' {z})) := by
    have := hxcl.preimage (continuous_subtype_val (p := fun w => w ∈ p ⁻¹' {z}))
    convert this using 1
    ext w
    simp [Subtype.ext_iff]
  have hβcl : IsClosed ({β} : Set (p.fiber z)) := by
    have := e.symm.isClosedMap _ h1
    rwa [Set.image_singleton] at this
  have hne : α ≠ β := by
    intro h
    rw [h] at hα
    have hC1 : C = {β} := by rw [← hα.def, hβcl.closure_eq]
    have h0 : topologicalKrullDim C ≤ 0 := by
      rw [hC1]
      haveI : Subsingleton ({β} : Set (p.fiber z)) := Set.subsingleton_singleton.coe_sort
      haveI : DiscreteTopology ({β} : Set (p.fiber z)) := Subsingleton.discreteTopology
      exact topologicalKrullDim_zero_of_discreteTopology ({β} : Set (p.fiber z))
    have := hdimC.trans (add_le_add h0 (le_refl (2 : WithBot ℕ∞)))
    exact absurd this (by decide)
  set ξ : X := (e α).1 with hξdef
  have heβ : e β = ⟨x, hxz'⟩ := e.apply_symm_apply _
  have hξx : ξ ⤳ x := by
    have := (hαβ.map e.continuous).map continuous_subtype_val
    rwa [heβ] at this
  have hξne : ξ ≠ x := fun h => hne (e.injective (Subtype.ext (h.trans (congrArg Subtype.val
    heβ.symm))))
  have hξz : p ξ = z := (e α).2
  refine ⟨ξ, x, hξx, hxcl, hxE, fun Γ hΓ hξΓ => ?_, fun y hy => ?_⟩
  · have := hWbad Γ ξ x hξΓ hξx hξne (hξz.trans hxz.symm)
    exact hzW (Set.mem_biUnion hΓ (hxz ▸ this))
  · have hzy : p ξ ⤳ p y := hy.map p.continuous
    rw [hξz] at hzy ⊢
    have hmem : p y ∈ closure ({z} : Set Z) := specializes_iff_mem_closure.mp hzy
    rw [(show IsClosed ({z} : Set Z) from hzcl).closure_eq] at hmem
    exact hmem

/-! ### Log canonical pairs -/

/-- **Kollár–Mori log canonical pairs are log canonical.** For a threefold pair `(X, Δ)` with
`Δ ≥ 0` and `discrep(X, Δ) ≥ -1`, every log discrepancy of `(X, Δ)` is nonnegative: it is
`1 + a(E, X, Δ)`, with `a(E, X, Δ) ≥ discrep(X, Δ) ≥ -1` for `E` exceptional, and
`a(E, X, Δ) = -coeff_P Δ ≥ -1` when `E` has the valuation of a prime divisor `P` of `X`. -/
private theorem isLogCanonicalPair_of_isLcPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {Δ : QDivisor X}
    (h : IsLcPair sX 3 K Δ) (hΔ : 0 ≤ Δ) : MMP.Intersection.IsLogCanonicalPair sX Δ := by
  refine ⟨h.1.isPair, fun P => hΔ P, fun n D a ha => ?_⟩
  have hX := h.1.1
  obtain rfl : n = 3 := by
    have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
    rw [h.1.2.1.1] at h1
    exact_mod_cast h1.symm
  obtain ⟨d, hd⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1 D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hd ha]
  suffices hd1 : (-1 : ℝ) ≤ d by linarith
  by_cases hex : D.IsExceptional
  · have h1 : MMP.Mori.discrep sX 3 K Δ ≤ ((d : ℝ) : EReal) := sInf_le ⟨D, d, hex, hd, rfl⟩
    have h2 : (-1 : EReal) ≤ ((d : ℝ) : EReal) := h.2.trans h1
    have h3 : ((-1 : ℝ) : EReal) ≤ ((d : ℝ) : EReal) := by
      rwa [EReal.coe_neg, EReal.coe_one]
    exact EReal.coe_le_coe_iff.mp h3
  · obtain ⟨P, hP⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hex
    obtain ⟨d', hd'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1
      (DivisorOver.ofPrimeDivisor ℂ hX P)
    have hd'P := hd'.eq_neg_coeff_of_ofPrimeDivisor hX
    have hP1 := h.coeff_le_one (by norm_num) P
    have hl' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd'
      (show IsProper (𝟙 X) from inferInstance)
    have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd ha.2.1
    have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl hl' hP
    have : (d : ℝ) = d' := by linarith
    rw [this, hd'P]
    push_cast
    exact_mod_cast (by linarith : (-1 : ℚ) ≤ -Δ.coeff P)

/-- The support of an integral multiple of a divisor is contained in its support. -/
private theorem notMem_supp_zsmul {X : Scheme.{0}} {G : Divisor X} {x : X} (hx : x ∉ G.supp)
    (k : ℤ) : x ∉ (k • G).supp := by
  intro h
  obtain ⟨F, hF, hxF⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  refine hx (DivisorWithCoeffs.mem_supp_iff.mpr ⟨F, fun h0 => hF ?_, hxF⟩)
  rw [DivisorWithCoeffs.coeff_smul, h0, smul_zero]

/-- If the Cartier divisor `D` pulls back to `D'`, then `(1/n) D` pulls back to `(1/n) D'`. -/
private theorem isPullback_inv_smul_toQDivisor {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} {D : Divisor Y} (hDc : D.IsCartier)
    {hB : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ D.supp}
    {D' : Divisor X} (hp : D.IsPullback f hB D') {n : ℕ} (hn : 0 < n)
    (hB' : ∀ T : irreducibleComponents X,
      f (componentGenericPoint X T) ∉ ((n : ℚ)⁻¹ • Divisor.toQDivisor D).supp) :
    ((n : ℚ)⁻¹ • Divisor.toQDivisor D).IsPullback f hB'
      ((n : ℚ)⁻¹ • Divisor.toQDivisor D') := by
  intro m hm E hE hEc
  have hsub : ∀ x, x ∉ D.supp → x ∉ E.supp := fun x hx h => by
    obtain ⟨F, hF, hxF⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    refine hx (DivisorWithCoeffs.mem_supp_iff.mpr ⟨F, fun h0 => hF ?_, hxF⟩)
    have := congrArg (fun G : QDivisor Y => G.coeff F) hE
    simp [h0] at this
    exact_mod_cast this
  have hBE : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ E.supp :=
    fun T => hsub _ (hB T)
  refine ⟨E.pullback hEc hBE, ?_, Divisor.isPullback_pullback hEc hBE⟩
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : (n : ℤ) • E = (m : ℤ) • D := Divisor.toQDivisor_injective (by
    rw [map_zsmul, map_zsmul, hE, smul_comm (n : ℤ) (m : ℤ),
      ← Int.cast_smul_eq_zsmul ℚ (n : ℤ), smul_smul]
    simp [hn'])
  have h1 := (Divisor.isPullback_pullback hEc hBE).zsmul hEc (n : ℤ)
    (fun T => notMem_supp_zsmul (hBE T) _)
  have h2 := (hp.zsmul hDc (m : ℤ) (fun T => notMem_supp_zsmul (hB T) _)).of_eq key.symm
    (hB₂ := fun T => notMem_supp_zsmul (hBE T) _)
  have h3 : (n : ℤ) • E.pullback hEc hBE = (m : ℤ) • D' := h1.eq (hEc.zsmul _) h2
  have h4 := congrArg Divisor.toQDivisor h3
  rw [map_zsmul, map_zsmul] at h4
  calc Divisor.toQDivisor (E.pullback hEc hBE)
      = (n : ℚ)⁻¹ • ((n : ℤ) • Divisor.toQDivisor (E.pullback hEc hBE)) := by
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        simp [hn']
    _ = (m : ℤ) • ((n : ℚ)⁻¹ • Divisor.toQDivisor D') := by
        rw [h4, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul,
          mul_comm]

/-- `(1/n) D` is `ℚ`-Cartier for a Cartier divisor `D` and `n > 0`. -/
private theorem isQCartier_inv_smul_toQDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} (hD : D.IsCartier) {n : ℕ} (hn : 0 < n) :
    ((n : ℚ)⁻¹ • Divisor.toQDivisor D).IsQCartier :=
  ⟨n, by exact_mod_cast hn.ne', D, by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    simp [hn.ne'], hD⟩

/-- The push-forward of the divisor of a pulled-back top form along a proper birational morphism
of normal varieties is the divisor of the form: each prime divisor `P` of `X` is the image of a
prime divisor `E` of `Y` along which `f` is a local isomorphism, and `ord_E f^*ω = ord_P ω`. -/
private theorem transformDivisor_divisorOfForm_pullback {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)] [IsProper f] [IsDominant f]
    (hX : IsNormalVariety ℂ sX)
    (hY : IsNormalVariety ℂ (f ≫ sX)) (hf : IsBirationalMorphism f) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d)
    (ω : RationalPluriForms sX d 1) :
    MMP.Mori.RationalMap.transformDivisor (X := Y) f.toRationalMap
      (divisorOfForm (pullbackRationalPluriForms sX f ω)) = divisorOfForm ω := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, hE, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX (f := f) hY hf P
  haveI := hiso
  rw [htr]
  change E.ordForm _ = P.ordForm ω
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f
    hf.functionFieldMap_bijective hd E P hE ω

/-- **Crepant invariance of log canonicity along a proper birational morphism.** Let
`f : Y ⟶ X` be a proper birational morphism of normal varieties, with canonical divisors `K_X`,
`K_Y` such that `f_* K_Y = K_X`, and let `n(K_X + Δ) = L` and `n(K_Y + Δ_Y) = L'` with `L` Cartier
and `L' = f^* L`, so that `K_Y + Δ_Y = f^*(K_X + Δ)`. Then `(X, Δ)` and `(Y, Δ_Y)` have the same
discrepancies along divisors with the same valuation, and every divisor over one of them has the
valuation of a divisor over the other: one is log canonical if and only if the other is, given
effectivity of the boundary. -/
private theorem isLogCanonicalPair_iff_of_crepant {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (f : Y ⟶ X) [IsProper f] {sY : Y ⟶ Spec (.of ℂ)} (hfs : f ≫ sX = sY)
    (hY : IsNormalVariety ℂ sY) (hf : IsBirationalMorphism f)
    {n : ℕ} {KX : Divisor X} {KY : Divisor Y} (hKX : KX.IsCanonicalDivisor sX n)
    (hKY :
      haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      haveI : IsNormal Y := hY.2
      KY.IsCanonicalDivisor sY n)
    (htr : MMP.Mori.RationalMap.transformDivisor (X := Y) f.toRationalMap KY = KX)
    {Δ : QDivisor X} {ΔY : QDivisor Y} (hP : MMP.Mori.IsPair sX Δ) {nn : ℕ} (hnn : 0 < nn)
    {L : Divisor X} (hLc : L.IsCartier) (hL : (nn : ℤ) • (Divisor.toQDivisor KX + Δ) =
      Divisor.toQDivisor L) {L' : Divisor Y}
    (hL' : (nn : ℤ) • (Divisor.toQDivisor KY + ΔY) = Divisor.toQDivisor L')
    (hpb :
      haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      haveI : IsNormal Y := hY.2
      haveI : IsDominant f := hf.isDominant
      ∃ hB, L.IsPullback f hB L') :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsNormal Y := hY.2
    (MMP.Intersection.IsLogCanonicalPair sX Δ → 0 ≤ ΔY →
        MMP.Intersection.IsLogCanonicalPair sY ΔY) ∧
      (MMP.Intersection.IsLogCanonicalPair sY ΔY → 0 ≤ Δ →
        MMP.Intersection.IsLogCanonicalPair sX Δ) := by
  subst hfs
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : IsDominant f := hf.isDominant
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨hB, hpb⟩ := hpb
  have hnnQ : (nn : ℚ) ≠ 0 := by exact_mod_cast hnn.ne'
  have hinv : ∀ {W : Scheme.{0}} (D : QDivisor W) (G : Divisor W),
      (nn : ℤ) • D = Divisor.toQDivisor G → D = (nn : ℚ)⁻¹ • Divisor.toQDivisor G :=
    fun D G h => by
      rw [← h, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      simp [hnnQ]
  have hB' : ∀ T : irreducibleComponents Y, f (componentGenericPoint Y T) ∉
      ((nn : ℚ)⁻¹ • Divisor.toQDivisor L).supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier f
      (isQCartier_inv_smul_toQDivisor hLc hnn)
  have hpbQ : ∃ hB'' : ∀ T : irreducibleComponents Y, f (componentGenericPoint Y T) ∉
      (Divisor.toQDivisor KX + Δ).supp,
      (Divisor.toQDivisor KX + Δ).IsPullback f hB'' (Divisor.toQDivisor KY + ΔY) := by
    rw [hinv _ _ hL, hinv _ _ hL']
    exact ⟨hB', isPullback_inv_smul_toQDivisor hLc hpb hnn hB'⟩
  obtain ⟨hB'', hpbQ⟩ := hpbQ
  obtain ⟨hPY, hiff⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP f hY hf hKX hKY
    (Or.inr ⟨inferInstance, htr, hB'', hpbQ⟩)
  have hdX : topologicalKrullDim X = n := hKX.topologicalKrullDim_eq
  have hdY : topologicalKrullDim Y = n := hKY.topologicalKrullDim_eq
  refine ⟨fun hlc hΔY => ⟨hPY, fun P => hΔY P, fun d E a ha => ?_⟩,
    fun hlc hΔ => ⟨hP, fun P => hΔ P, fun d E' a ha => ?_⟩⟩
  · have hdn : d = n := by
      have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
      rw [hdY] at h1
      exact_mod_cast h1.symm
    rw [hdn] at ha
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hKY E
    rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hb ha]
    have hb' := (hiff E (MMP.Mori.compDivisorOver f hY hf E)
      (MMP.Mori.valuation_compDivisorOver f hY hf E) b).mp hb
    haveI : IsProper E.f := ha.2.1
    exact hlc.2.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb'
      (show IsProper (MMP.Mori.compDivisorOver f hY hf E).f by
        change IsProper (E.f ≫ f); infer_instance))
  · have hdn : d = n := by
      have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
      rw [hdX] at h1
      exact_mod_cast h1.symm
    rw [hdn] at ha
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hKX E'
    rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hb ha]
    obtain ⟨E, hE⟩ := MMP.Mori.exists_divisorOver_comap_eq hY hf E'
    obtain ⟨E₁, hE₁⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hY E
    have hb' := (hiff E₁.toDivisorOver E' (by rw [hE, ← hE₁]) b).mpr hb
    exact hlc.2.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb'
      E₁.isProper)

/-- **Log canonicity along a crepant step.** Let `n(K_i + Γ_i) ∼ L_i ∼ f_i^* N` for the transform
`Γ_i` of an effective `ℚ`-divisor `Γ`, with `N` Cartier on `Z_i`. If `(X_i, Γ_i)` is log canonical,
so is `(X_{i+1}, Γ_{i+1})`: both pairs are crepant over `(Z_i, Γ_Z)`, where for a rational top form
`ω` of `Z_i`, `Γ_Z = (1/n) (N + div v) - div ω` with `f_i^*(N + div v) = n(div(f_i^*ω) + Γ_i)`;
log canonicity passes from `X_i` to `Z_i` along `f_i` and back to `X_{i+1}` along `f_i⁺`. -/
private theorem isLogCanonicalPair_succ {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sS π K B₀) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) (hdim : topologicalKrullDim (modelSeq X P.Y i) = 3) (Γ : QDivisor X)
    (hΓ : 0 ≤ Γ) {nn : ℕ} (hnn : 0 < nn) {Li : Divisor (modelSeq X P.Y i)}
    (hLi : ∃ u : (RationalFunctions (modelSeq X P.Y i))ˣ, Divisor.toQDivisor Li =
      (nn : ℤ) • (Divisor.toQDivisor (divisorSeq K P.KY i) + transformSeq P Γ i) +
        Divisor.toQDivisor (principalDivisor u))
    [IsIntegral (P.Z i)] [IsLocallyNoetherian (P.Z i)] [IsNormal (P.Z i)] [CompactSpace (P.Z i)]
    (N : Divisor (P.Z i)) (hNc : N.IsCartier)
    (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
      P.f i (componentGenericPoint _ T) ∉ N.supp)
    (hNL : (N.pullback hNc hN).LinearlyEquivalent Li)
    (hlc : MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY i) (transformSeq P Γ i)) :
    MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY (i + 1)) (transformSeq P Γ (i + 1)) := by
  classical
  obtain ⟨hZn, hfb, hfpp, hfpb, -, -, -⟩ := step_facts P i hi
  have hm0 := P.isRelativeDltModel i hi.le
  have hm1 := P.isRelativeDltModel (i + 1) (Order.add_one_le_of_lt hi)
  have hX0n : IsNormalVariety ℂ (modelStr sX P.sY i) := hm0.isQFactorial.1
  have hX1n : IsNormalVariety ℂ (modelStr sX P.sY (i + 1)) := hm1.isQFactorial.1
  have hctr := (P.isElementaryDltStep i hi).isNegativeRelativeRayContraction
    |>.isNegativeExtremalContraction
  haveI : IsProper (P.f i) := hctr.isContraction.isProper
  haveI := hfpp
  have hfs : P.f i ≫ P.sZ i = modelStr sX P.sY i := hctr.isContraction.comp_eq
  have hfps : P.fp i ≫ P.sZ i = modelStr sX P.sY (i + 1) := fp_comp_sZ P i hi
  haveI : IsDominant (P.f i) := hfb.isDominant
  haveI : IsDominant (P.fp i) := hfpb.isDominant
  haveI : LocallyOfFiniteType (P.sZ i) := hZn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (modelStr sX P.sY i) := hX0n.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (modelStr sX P.sY (i + 1)) := hX1n.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (P.f i ≫ P.sZ i) := by
    rw [hfs]; exact hX0n.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (P.fp i ≫ P.sZ i) := by
    rw [hfps]; exact hX1n.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ (P.f i ≫ P.sZ i) := hfs ▸ hX0n.1
  haveI : MMP.Mori.IsVariety ℂ (P.sZ i) := hZn.1
  haveI : MMP.Mori.IsVariety ℂ (modelStr sX P.sY i) := hX0n.1
  haveI : MMP.Mori.IsVariety ℂ (modelStr sX P.sY (i + 1)) := hX1n.1
  -- dimensions
  have hdZ : topologicalKrullDim (P.Z i) = 3 := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sZ i)
      (modelStr sX P.sY i) hfb]
    exact hdim
  have hd1 : topologicalKrullDim (modelSeq X P.Y (i + 1)) = 3 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (P.sZ i)
      (modelStr sX P.sY (i + 1)) hfpb]
    exact hdZ
  have htrZ := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := P.sZ i) hdZ
  -- a rational top form `ω` on `Z_i` and its pull-backs
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (P.sZ i) hZn hdZ
  obtain ⟨ωZ, hωZ0, hωZ⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hZn hKZ
  have hdivZ : divisorOfForm ωZ = KZ := Finsupp.ext fun Q => hωZ Q
  have hω0 := MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero (P.f i)
    hfb.functionFieldMap_bijective htrZ hωZ0
  have hω0' := MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero (P.fp i)
    hfpb.functionFieldMap_bijective htrZ hωZ0
  set KW := divisorOfForm (pullbackRationalPluriForms (P.sZ i) (P.f i) ωZ) with hKW
  set KW' := divisorOfForm (pullbackRationalPluriForms (P.sZ i) (P.fp i) ωZ) with hKW'
  obtain ⟨n₀, hK₀⟩ := hm0.isCanonicalDivisor
  obtain rfl : n₀ = 3 := by
    have := hK₀.1; rw [hdim] at this; exact_mod_cast this.symm
  obtain ⟨n₁, hK₁⟩ := hm1.isCanonicalDivisor
  obtain rfl : n₁ = 3 := by
    have := hK₁.1; rw [hd1] at this; exact_mod_cast this.symm
  have hKWc : KW.IsCanonicalDivisor (modelStr sX P.sY i) 3 := by
    have hK₀' : Divisor.IsCanonicalDivisor (P.f i ≫ P.sZ i) 3 (divisorSeq K P.KY i) :=
      hfs ▸ hK₀
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul (hfs ▸ hX0n) hK₀' hω0
    rw [one_zsmul] at h
    exact hfs ▸ hK₀'.of_linearlyEquivalent h
  have hfps' : P.fp i ≫ P.sZ i = P.sY i := hfps
  have hX1n' : IsNormalVariety ℂ (P.sY i) := hX1n
  have hKWc' : Divisor.IsCanonicalDivisor (P.sY i) 3 KW' := by
    have hK₁' : Divisor.IsCanonicalDivisor (P.fp i ≫ P.sZ i) 3 (P.KY i) := hfps' ▸ hK₁
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul (hfps' ▸ hX1n') hK₁' hω0'
    rw [one_zsmul] at h
    exact hfps' ▸ hK₁'.of_linearlyEquivalent h
  -- the crepant relation `f_i^*(N + div v) = n (K_W + Γ_i)` on `X_i`, `K_W = div(f_i^* ω)`
  obtain ⟨u, hu⟩ := hLi
  obtain ⟨a, ha⟩ := hNL
  obtain ⟨s, hs⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor
    (modelStr sX P.sY i) hX0n hK₀ hKWc
  obtain ⟨v, hv, hvc⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfb
    (s ^ (nn : ℤ) * u * a)⁻¹
  have hvC := Divisor.isCartier_principalDivisor v
  set L₁ : Divisor (P.Z i) := N + principalDivisor v with hL₁
  have hL₁c : L₁.IsCartier := hNc.add hvC
  have hL₁N : ∀ T : irreducibleComponents (modelSeq X P.Y i),
      P.f i (componentGenericPoint _ T) ∉ L₁.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant (P.f i) _
  set L₁f : Divisor (modelSeq X P.Y i) :=
    N.pullback hNc hN + principalDivisor (pullbackRationalFunction (P.f i) v hv) with hL₁f
  have hp₁ : L₁.IsPullback (P.f i) hL₁N L₁f :=
    (Divisor.isPullback_pullback hNc hN).add hNc hvC hL₁N (Divisor.isPullback_principalDivisor v hv)
  have hrel : Divisor.toQDivisor L₁f =
      (nn : ℤ) • (Divisor.toQDivisor KW + transformSeq P Γ i) := by
    have hN' : N.pullback hNc hN = Li + principalDivisor a := by rw [← ha]; abel
    have hK' : divisorSeq K P.KY i = KW + principalDivisor s := by rw [← hs]; abel
    rw [hL₁f, hvc, MMP.Mori.principalDivisor_inv, MMP.Mori.principalDivisor_mul,
      MMP.Mori.principalDivisor_mul, principalDivisor_zpow, hN', map_add, map_add, map_neg, map_add, map_add,
      map_zsmul, hu, hK', map_add]
    simp only [smul_add]
    abel
  -- the boundary `Γ_Z = (1/n)(N + div v) - div ω` on `Z_i`
  have hnnQ : (nn : ℚ) ≠ 0 := by exact_mod_cast hnn.ne'
  set ΓZ : QDivisor (P.Z i) :=
    ((1 : ℚ) / nn) • Divisor.toQDivisor L₁ - Divisor.toQDivisor (divisorOfForm ωZ) with hΓZ
  have hZrel : (nn : ℤ) • (Divisor.toQDivisor (divisorOfForm ωZ) + ΓZ) =
      Divisor.toQDivisor L₁ := by
    rw [hΓZ, add_sub_cancel, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    rw [mul_one_div_cancel hnnQ, one_smul]
  have hbijf := hfb.functionFieldMap_bijective
  have hbijfp := hfpb.functionFieldMap_bijective
  have hΓZnn : 0 ≤ ΓZ := by
    refine Finsupp.le_def.mpr fun Q => ?_
    obtain ⟨F, hF, hiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZn (f := P.f i)
        (hfs ▸ hX0n) hfb Q
    have e1 : L₁f.coeff F = L₁.coeff Q := MMP.Positivity.coeff_eq_of_isPullback F Q hF hL₁c hp₁
    have e2 : KW.coeff F = Q.ordForm ωZ :=
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso (P.f i) hbijf htrZ F Q hF ωZ
    have e3 := congrArg (fun D : QDivisor (modelSeq X P.Y i) => D.coeff F) hrel
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul, Int.cast_natCast] at e3
    obtain ⟨F₀, hF₀⟩ := transformSeq_coeff P i hi.le F
    have hΓF : (0 : ℚ) ≤ (transformSeq P Γ i).coeff F := by
      rw [show (transformSeq P Γ i).coeff F = Γ F₀ from hF₀ Γ]; simpa using hΓ F₀
    change (0 : ℚ) ≤ ΓZ.coeff Q
    rw [hΓZ, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      Divisor.coeff_toQDivisor, smul_eq_mul]
    change (0 : ℚ) ≤ 1 / nn * (L₁.coeff Q : ℚ) - (Q.ordForm ωZ : ℚ)
    rw [← e1, ← e2, e3]
    field_simp
    linarith
  -- (A) `(Z_i, Γ_Z)` is log canonical, being crepant to `(X_i, Γ_i)` along `f_i`
  have hZpair : MMP.Mori.IsPair (P.sZ i) ΓZ :=
    ⟨hZn, 3, divisorOfForm ωZ, hdivZ ▸ hKZ, ⟨nn, by exact_mod_cast hnn.ne', L₁, hZrel.symm, hL₁c⟩⟩
  have hlcZ : MMP.Intersection.IsLogCanonicalPair (P.sZ i) ΓZ :=
    ((isLogCanonicalPair_iff_of_crepant (P.f i) hfs hX0n hfb (hdivZ ▸ hKZ) hKWc
      (transformDivisor_divisorOfForm_pullback (P.f i) hZn (hfs ▸ hX0n) hfb htrZ ωZ) hZpair hnn
      hL₁c hZrel hrel.symm ⟨hL₁N, hp₁⟩).2 hlc hΓZnn)
  -- (B) `(X_{i+1}, Γ_{i+1})` is crepant to `(Z_i, Γ_Z)` along `f_i⁺`
  haveI : LocallyOfFiniteType (P.sY i) := hX1n'.1.toLocallyOfFiniteType
  set Γ₁ : QDivisor (P.Y i) := transformSeq P Γ (i + 1) with hΓ₁
  have hL₁p := map_componentGenericPoint_notMem_supp_of_isDominant (P.fp i) L₁
  set L₁p : Divisor (P.Y i) := L₁.pullback hL₁c hL₁p with hL₁pdef
  have hpb₂ := Divisor.isPullback_pullback hL₁c hL₁p
  have hrel' : Divisor.toQDivisor L₁p = (nn : ℤ) • (Divisor.toQDivisor KW' + Γ₁) := by
    refine DivisorWithCoeffs.ext' fun F' => ?_
    obtain ⟨F, Q, hF, hF', htr⟩ := step_coeff P i hi F'
    haveI := isIso_stalkMap_of_map_eq_genericPoint hfb hF
    haveI := isIso_stalkMap_of_map_eq_genericPoint hfpb hF'
    have e1 : L₁p.coeff F' = L₁.coeff Q :=
      MMP.Positivity.coeff_eq_of_isPullback F' Q hF' hL₁c hpb₂
    have e2 : L₁f.coeff F = L₁.coeff Q := MMP.Positivity.coeff_eq_of_isPullback F Q hF hL₁c hp₁
    have e3 : KW'.coeff F' = Q.ordForm ωZ :=
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso (P.fp i) hbijfp htrZ F' Q hF' ωZ
    have e4 : KW.coeff F = Q.ordForm ωZ :=
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso (P.f i) hbijf htrZ F Q hF ωZ
    have e5 : Γ₁.coeff F' = (transformSeq P Γ i).coeff F := htr _
    have e6 := congrArg (fun D : QDivisor (modelSeq X P.Y i) => D.coeff F) hrel
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul, Int.cast_natCast] at e6 ⊢
    rw [e1, ← e2, e6, e3, ← e4, e5]
  have hΓ1 : 0 ≤ Γ₁ := by
    refine Finsupp.le_def.mpr fun F' => ?_
    obtain ⟨F₀, hF₀⟩ := transformSeq_coeff P (i + 1) (Order.add_one_le_of_lt hi) F'
    have h1 : Γ₁ F' = Γ F₀ := hF₀ Γ
    change (0 : ℚ) ≤ Γ₁ F'
    rw [h1]
    simpa using hΓ F₀
  exact (isLogCanonicalPair_iff_of_crepant (P.fp i) hfps' hX1n' hfpb (hdivZ ▸ hKZ) hKWc'
    (transformDivisor_divisorOfForm_pullback (P.fp i) hZn (hfps' ▸ hX1n') hfpb htrZ ωZ) hZpair
    hnn hL₁c hZrel hrel'.symm ⟨hL₁p, hpb₂⟩).1 hlcZ hΓ1

/-! ### Adjunction to a floor component -/

/-- The generic point of an integral scheme lies on no prime divisor. -/
private theorem genericPoint_notMem_support {C : Scheme.{0}} [IsIntegral C]
    (P : MMP.Mori.PrimeDivisor C) : genericPoint C ∉ (P.support : Set C) := by
  intro h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have h1 : P.genericPoint ⤳ genericPoint C := specializes_iff_mem_closure.mpr h
  have h2 : genericPoint C ⤳ P.genericPoint := (genericPoint_spec C).specializes trivial
  have heq : P.genericPoint = genericPoint C := (h1.antisymm h2).eq
  have hmax : Order.coheight (genericPoint C) = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial
  have := P.coheight_genericPoint
  rw [heq, hmax] at this
  exact zero_ne_one this

/-- The final stratum of an adjunction step does not contain the generic point: if `ι(j(t))` were
the generic point of `V`, the closed immersion `ι` would be onto, so `j(t)` would be the generic
point of `S`, which lies on no prime divisor. -/
private theorem genericPoint_notMem_range_of_isAdjunctionStep {V S T : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)} [IsIntegral V] {ι : S ⟶ V} [IsIntegral S] [IsClosedImmersion ι]
    {BS : QDivisor S} {j : T ⟶ S} {BT : QDivisor T} (h : IsAdjunctionStep (ι ≫ sV) BS j BT) :
    genericPoint V ∉ Set.range (j ≫ ι) := by
  obtain ⟨-, P, -, hPr, -⟩ := h
  rintro ⟨t, ht⟩
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hmem : genericPoint V ∈ Set.range ι := ⟨j t, ht⟩
  have huniv : Set.range ι = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    have hv : v ∈ closure ({genericPoint V} : Set V) := by
      rw [(genericPoint_spec V).def]; trivial
    exact hcl.closure_eq ▸ closure_mono (Set.singleton_subset_iff.mpr hmem) hv
  haveI : IsDominant ι := ⟨by rw [DenseRange, huniv]; exact dense_univ⟩
  have hgen : ι (genericPoint S) = genericPoint V := map_genericPoint_of_isDominant ι
  have hjt : j t = genericPoint S := ι.isClosedEmbedding.injective (ht.trans hgen.symm)
  exact genericPoint_notMem_support P (hjt ▸ (hPr ▸ ⟨t, rfl⟩ : j t ∈ (P.support : Set S)))

/-- **Adjunction to a floor component.** A prime divisor `S` with coefficient at least one in the
boundary of a dlt pair `(V, B)` is the image of an adjunction step `(V, B) ⇝ (T, B_T)`: the dlt
stratum `S` carries iterated adjunction data, and since `S` has codimension one the flag has
length one. -/
private theorem exists_isAdjunctionStep_of_one_le_coeff {V : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {B : QDivisor V}
    (hB : MMP.Intersection.IsDltPair sV B) (S : MMP.Mori.PrimeDivisor V) (hS : 1 ≤ B.coeff S) :
    ∃ (T : Scheme.{0}) (j : T ⟶ V) (BT : QDivisor T), IsAdjunctionStep sV B j BT ∧
      Set.range j.base = (S.support : Set V) := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have hSirr : IsIrreducible (S.support : Set V) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
  have hstr : IsDltStratum sV B (S.support : Set V) := by
    refine ⟨hB, {S}, Finset.singleton_nonempty _, by simpa using hS, ?_, ?_⟩
    · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
      exact hSirr.nonempty
    · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
      exact ⟨⟨hSirr, le_rfl⟩, fun T hT _ => hT.2⟩
  obtain ⟨⟨T, ι, BT, hrange, ⟨F⟩⟩, -⟩ := hstr.exists_isStratumAdjunctionPair_and_isDltPair.1
  have hηS : genericPoint V ∉ (S.support : Set V) := genericPoint_notMem_support S
  cases F with
  | refl h =>
    exfalso
    exact hηS (hrange ▸ ⟨genericPoint V, rfl⟩)
  | @step S₁ T₁ ι₁ BS₁ F' j BT₁ h =>
    cases F' with
    | refl h' =>
      refine ⟨T, j, BT, ?_, ?_⟩
      · rwa [Category.id_comp] at h
      · rwa [Category.comp_id] at hrange
    | @step S₂ T₂ ι₂ BS₂ F'' j' BT₂ h'' =>
      exfalso
      haveI := F''.isClosedImmersion
      obtain ⟨hT₂v, -, -, -, hj'ci, -⟩ := id h''
      haveI := hj'ci
      haveI := F''.isNormalVariety.1.toIsIntegral
      haveI : IsIntegral S₁ := hT₂v.1.toIsIntegral
      have hηW := genericPoint_notMem_range_of_isAdjunctionStep h''
      obtain ⟨-, P, -, hPr, -⟩ := h
      have hSW : (S.support : Set V) ⊆ Set.range (j' ≫ ι₂) := by
        rw [← hrange]; rintro _ ⟨t, rfl⟩; exact ⟨j t, rfl⟩
      have hwS : (j' ≫ ι₂) (genericPoint S₁) ∉ (S.support : Set V) := by
        rw [← hrange]; rintro ⟨t, ht⟩
        exact genericPoint_notMem_support P
          (hPr ▸ ⟨t, (j' ≫ ι₂).isClosedEmbedding.injective ht⟩)
      set ξ := (j' ≫ ι₂) (genericPoint S₁) with hξ
      have hWcl : Set.range (j' ≫ ι₂) = closure {ξ} := by
        rw [← MMP.Flips.closure_range_eq_closure_genericPoint (j' ≫ ι₂),
          (j' ≫ ι₂).isClosedEmbedding.isClosed_range.closure_eq]
      have hηS' : S.genericPoint ∈ (S.support : Set V) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      have h1 : ξ ⤳ S.genericPoint :=
        specializes_iff_mem_closure.mpr (hWcl ▸ hSW hηS')
      have h1' : ¬ S.genericPoint ⤳ ξ := fun h => hwS (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact specializes_iff_mem_closure.mp h)
      have h2 : genericPoint V ⤳ ξ := (genericPoint_spec V).specializes trivial
      have h2' : ¬ ξ ⤳ genericPoint V := fun h => hηW (hWcl ▸ specializes_iff_mem_closure.mp h)
      have hlt1 : S.genericPoint < ξ := lt_of_le_not_ge h1 h1'
      have hlt2 : ξ < genericPoint V := lt_of_le_not_ge h2 h2'
      have c1 := Order.coheight_add_one_le hlt1
      have c2 := Order.coheight_add_one_le hlt2
      rw [S.coheight_genericPoint] at c1
      have : (2 : ℕ∞) ≤ 1 := by
        calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
          _ ≤ Order.coheight (genericPoint V) + 1 + 1 := by gcongr; exact zero_le
          _ ≤ Order.coheight ξ + 1 := by gcongr
          _ ≤ 1 := c1
      exact absurd this (by decide)

/-! ### The complement along the program -/

/-- The complement `A` carried along the program: on the model `X_i`, a Cartier divisor `L'` with
`L' ∼ n(K_i + Γ_i)`, `Γ_i` the transform of `Γ`, and `𝒪(L') ≅ π_i^* M'`. -/
private def ComplementInv {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}
    {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sZ f K B₀) (Γ : QDivisor X)
    (M' : Z.Modules) (n : ℕ) (i : ℕ) (L' : Divisor (modelSeq X P.Y i)) : Prop :=
  L'.IsCartier ∧
    (∃ u : (RationalFunctions (modelSeq X P.Y i))ˣ, Divisor.toQDivisor L' =
      (n : ℤ) • (Divisor.toQDivisor (divisorSeq K P.KY i) + transformSeq P Γ i) +
        Divisor.toQDivisor (principalDivisor u)) ∧
    Nonempty (L'.divisorialSheaf ≅ (Scheme.Modules.pullback (modelMap f P.πY i)).obj M')

/-- **The complement passes to the next model.** Write `π_i^* M' = f_i^* (g_i^* M')` and
`g_i^* M' = 𝒪(N)` for a Cartier divisor `N` on `Z_i`; then `L' ∼ f_i^* N`, and `(f_i⁺)^* N`
satisfies the invariant on `X_{i+1}`. -/
private theorem complementInv_succ {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}
    {K : Divisor X} {B₀ : QDivisor X} (P : RelativeDltProgram sX sZ f K B₀) (Γ : QDivisor X)
    (M' : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M'] (n : ℕ) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) {L' : Divisor (modelSeq X P.Y i)} (h : ComplementInv P Γ M' n i L') :
    ∃ L'' : Divisor (modelSeq X P.Y (i + 1)), ComplementInv P Γ M' n (i + 1) L'' := by
  obtain ⟨hZn, hfb, -, hfpb, -, hfg, hfpg⟩ := step_facts P i hi
  haveI : IsIntegral (P.Z i) := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZn.2
  haveI : QuasiCompact (P.sZ i) := hZn.1.toQuasiCompact
  haveI : CompactSpace (P.Z i) := QuasiCompact.compactSpace_of_compactSpace (P.sZ i)
  haveI : IsDominant (P.f i) := hfb.isDominant
  haveI : IsDominant (P.fp i) := hfpb.isDominant
  obtain ⟨-, hu, ⟨e⟩⟩ := h
  haveI := MMP.Fourfold.isInvertibleModule_pullback (P.gZ i) M'
  obtain ⟨N, hNc, ⟨eN⟩⟩ :=
    exists_isCartier_divisorialSheaf_iso ((Scheme.Modules.pullback (P.gZ i)).obj M')
  have hN := map_componentGenericPoint_notMem_supp_of_isDominant (P.f i) N
  have hN' := map_componentGenericPoint_notMem_supp_of_isDominant (P.fp i) N
  obtain ⟨e₁⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := N) hNc (P.f i) hN
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := N) hNc (P.fp i) hN'
  have hNL : (N.pullback hNc hN).LinearlyEquivalent L' :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (e₁ ≪≫ (Scheme.Modules.pullback (P.f i)).mapIso eN ≪≫
        (Scheme.Modules.pullbackComp (P.f i) (P.gZ i)).app M' ≪≫
        eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj M') hfg) ≪≫ e.symm)
  exact ⟨N.pullback hNc hN', isCartier_of_isPullback (P.fp i) hNc
    (Divisor.isPullback_pullback hNc hN'), exists_eq_smul_add_of_step P i hi Γ hu N hNc hN hN' hNL,
    ⟨e₂ ≪≫ (Scheme.Modules.pullback (P.fp i)).mapIso eN ≪≫
      (Scheme.Modules.pullbackComp (P.fp i) (P.gZ i)).app M' ≪≫
      eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj M') hfpg)⟩⟩

/-- The divisor of the complement invariant is pulled back from the target of the step:
`L' ∼ f_i^* N` for a Cartier divisor `N` on `Z_i` with `𝒪(N) ≅ g_i^* M'`. -/
private theorem exists_pullback_linearlyEquivalent_of_complementInv {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {B₀ : QDivisor X} (P : RelativeDltProgram sX sZ f K B₀) (Γ : QDivisor X)
    (M' : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M'] (n : ℕ) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) {L' : Divisor (modelSeq X P.Y i)} (h : ComplementInv P Γ M' n i L') :
    ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i)) (_ : IsNormal (P.Z i))
      (_ : CompactSpace (P.Z i)) (N : Divisor (P.Z i)) (hNc : N.IsCartier)
      (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
        P.f i (componentGenericPoint _ T) ∉ N.supp),
      (N.pullback hNc hN).LinearlyEquivalent L' := by
  obtain ⟨hZn, hfb, -, -, -, hfg, -⟩ := step_facts P i hi
  haveI : IsIntegral (P.Z i) := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsNormal (P.Z i) := hZn.2
  haveI : QuasiCompact (P.sZ i) := hZn.1.toQuasiCompact
  haveI : CompactSpace (P.Z i) := QuasiCompact.compactSpace_of_compactSpace (P.sZ i)
  haveI : IsDominant (P.f i) := hfb.isDominant
  obtain ⟨-, -, ⟨e⟩⟩ := h
  haveI := MMP.Fourfold.isInvertibleModule_pullback (P.gZ i) M'
  obtain ⟨N, hNc, ⟨eN⟩⟩ :=
    exists_isCartier_divisorialSheaf_iso ((Scheme.Modules.pullback (P.gZ i)).obj M')
  have hN := map_componentGenericPoint_notMem_supp_of_isDominant (P.f i) N
  obtain ⟨e₁⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := N) hNc (P.f i) hN
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, N, hNc, hN,
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (e₁ ≪≫ (Scheme.Modules.pullback (P.f i)).mapIso eN ≪≫
        (Scheme.Modules.pullbackComp (P.f i) (P.gZ i)).app M' ≪≫
        eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj M') hfg) ≪≫ e.symm)⟩

/-- **The complement on every model.** From `K + B + A ∼_ℚ G` with `𝒪(m G) ≅ f^* M`: with
`𝒪(H₀) ≅ M` for a Cartier divisor `H₀` on `Z` and `n(K + B + A - G) = div φ`, the divisor
`L' = n L + m div φ ∼ f^*(n H₀)` satisfies the invariant on `X` with `M' = 𝒪(n H₀)`, and it passes
along the steps. -/
private theorem exists_complementInv {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsNormal Z] (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hconn : ∀ z : Z, _root_.IsConnected (f ⁻¹' {z})) {K : Divisor X} {B A : QDivisor X}
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    {B₀ : QDivisor X} (P : RelativeDltProgram sX sZ f K B₀) :
    ∃ (M' : Z.Modules) (_ : Stacks.Ample.IsInvertibleModule Z M') (n : ℕ), 0 < n ∧
      ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ L' : Divisor (modelSeq X P.Y i),
        ComplementInv P (B + A) M' n i L' := by
  haveI : IsIntegral Z := hZ.toIsVariety.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.toIsVariety.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : Surjective f := ⟨fun z => (hconn z).nonempty⟩
  haveI : IsDominant f := inferInstance
  obtain ⟨n₁, hn₁, φ, hφ⟩ := hDG
  obtain ⟨m₁, hm₁, L₁, hL₁, ⟨e₁⟩⟩ := hGM
  obtain ⟨H₀, hH₀c, ⟨eH₀⟩⟩ := exists_isCartier_divisorialSheaf_iso M
  have hH₀ := map_componentGenericPoint_notMem_supp_of_isDominant f H₀
  -- `L₁ ∼ f^* H₀`
  obtain ⟨eH₀'⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := H₀) hH₀c f hH₀
  obtain ⟨a, ha⟩ : (H₀.pullback hH₀c hH₀).LinearlyEquivalent L₁ :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (eH₀' ≪≫ (Scheme.Modules.pullback f).mapIso eH₀ ≪≫ e₁.symm)
  set H₁ : Divisor Z := (n₁ : ℤ) • H₀ with hH₁
  have hH₁c : H₁.IsCartier := hH₀c.zsmul _
  have hH₁ := map_componentGenericPoint_notMem_supp_of_isDominant f H₁
  have hpb₁ : H₁.pullback hH₁c hH₁ = (n₁ : ℤ) • H₀.pullback hH₀c hH₀ :=
    Divisor.IsPullback.pullback_eq hH₁c
      ((Divisor.isPullback_pullback hH₀c hH₀).zsmul hH₀c (n₁ : ℤ) hH₁)
  set L₀ : Divisor X := (n₁ : ℤ) • L₁ + (m₁ : ℤ) • principalDivisor φ with hL₀
  -- `L₀ ∼ f^* H₁`
  have hlin : (H₁.pullback hH₁c hH₁).LinearlyEquivalent L₀ := by
    refine ⟨a ^ (n₁ : ℤ) * φ ^ (-(m₁ : ℤ)), ?_⟩
    rw [hpb₁, hL₀, MMP.Mori.principalDivisor_mul]
    rw [principalDivisor_zpow, principalDivisor_zpow, neg_smul, ← ha, smul_sub]
    abel
  haveI : Stacks.Ample.IsInvertibleModule Z H₁.divisorialSheaf :=
    (Divisor.mem_cartierSubgroup.mp hH₁c).isInvertibleModule_divisorialSheaf
  obtain ⟨eH₁⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := H₁) hH₁c f hH₁
  refine ⟨H₁.divisorialSheaf, inferInstance, n₁ * m₁, Nat.mul_pos hn₁ hm₁, fun i => ?_⟩
  induction i with
  | zero =>
    have hL₁c : L₁.IsCartier := by
      have : L₁ = H₀.pullback hH₀c hH₀ + principalDivisor a⁻¹ := by
        rw [MMP.Mori.principalDivisor_inv, ← ha]; abel
      rw [this]
      exact (isCartier_of_isPullback f hH₀c (Divisor.isPullback_pullback hH₀c hH₀)).add
        (Divisor.isCartier_principalDivisor _)
    refine fun _ => ⟨L₀, (hL₁c.zsmul _).add ((Divisor.isCartier_principalDivisor φ).zsmul _),
      ⟨1, ?_⟩, ⟨hlin.symm.divisorialSheafIso ≪≫ eH₁⟩⟩
    rw [MMP.Mori.principalDivisor_one, map_zero, add_zero]
    change Divisor.toQDivisor L₀ = ((n₁ * m₁ : ℕ) : ℤ) • (Divisor.toQDivisor K + (B + A))
    rw [hL₀, map_add, map_zsmul, map_zsmul, hL₁, ← hφ, smul_smul, smul_smul]
    push_cast
    rw [mul_comm (m₁ : ℤ) (n₁ : ℤ), ← smul_add, sub_eq_add_neg, add_comm (Divisor.toQDivisor K + B + A),
      ← add_assoc, add_neg_cancel, zero_add, add_assoc]
  | succ i ih =>
    intro hi
    have hi' : (i : ℕ∞) < P.n := lt_of_succ_le hi
    obtain ⟨L', hL'⟩ := ih hi'.le
    exact complementInv_succ P (B + A) _ _ i hi' hL'

/-- **The program ends with a Mori fibre space.** The adjoint `K_n + B_n - tT_n` of the last model
is not nef over `Z`: on a general fibre curve `γ` of `X_n ⟶ Z` through a point of the transform
`E_n` of a horizontal component of `⌊B⌋`, not contained in the support of `A_n + tT_n`, the
divisor `A_n + tT_n` is positive while `K_n + B_n + A_n` is trivial. -/
private theorem endpoint_hasFinal
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (hZ2 : topologicalKrullDim Z = 2) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hconn : ∀ z : Z, _root_.IsConnected (f ⁻¹' {z}))
    (hO : ∀ U : Z.Opens, IsIso (f.app U))
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A)) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    (hE : ∃ E : Mori.PrimeDivisor X, 1 ≤ B.coeff E ∧ Dense (f '' (E.support : Set X)))
    {m : ℕ} (hm : 0 < m) {L₀ : Divisor X} (hL₀ : Divisor.toQDivisor L₀ =
      (m : ℤ) • (Divisor.toQDivisor K + B)) (hL₀c : L₀.IsCartier)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (hPn : P.n ≠ ⊤)
    (hPend : MMP.Flips.IsRelativelyNef ℂ (modelStr sX P.sY P.n.toNat) (modelMap f P.πY P.n.toNat)
          (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
            divisorSeq (B - t • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat)) ∨
        P.hasFinal)
    (L : ∀ i, Divisor (modelSeq X P.Y i)) (hL0 : L 0 = L₀)
    (hL : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → NullInv P B m i (L i))
    (hstep : ∀ i : ℕ, (i : ℕ∞) < P.n → ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i))
        (_ : IsNormal (P.Z i)) (_ : CompactSpace (P.Z i)) (N : Divisor (P.Z i)) (hNc : N.IsCartier),
        ∃ (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
            P.f i (componentGenericPoint _ T) ∉ N.supp)
          (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp),
          (N.pullback hNc hN).LinearlyEquivalent (L i) ∧
            (N.pullback hNc hN').LinearlyEquivalent (L (i + 1))) :
    P.hasFinal := by
  classical
  by_contra hfin
  have hnefR := hPend.resolve_right hfin
  have hn : (P.n.toNat : ℕ∞) ≤ P.n := ENat.coe_toNat_le_self _
  set n := P.n.toNat with hn_def
  have hmod := P.isRelativeDltModel n hn
  have hXq : IsQFactorial (modelStr sX P.sY n) := hmod.isQFactorial
  obtain ⟨hXv, hXproj⟩ := (Mori.isProjectiveVariety_iff ℂ _).mp (hPproj.2 n hn)
  haveI : IsProper (modelStr sX P.sY n) := isProper_of_isProjectiveMorphism _ hXproj
  haveI : QuasiCompact (modelStr sX P.sY n) := hXv.toQuasiCompact
  haveI : IsProper (modelMap f P.πY n) :=
    isProper_of_isProjectiveMorphism _ hmod.isProjectiveMorphism
  have hdims : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → topologicalKrullDim (modelSeq X P.Y i) = 3 :=
    fun i hi => (hL i hi).2.2.2.2.1.2.1.1
  have hZv : Mori.IsVariety ℂ sZ := ((Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
  haveI : IsIntegral Z := hZv.toIsIntegral
  -- the horizontal floor `E` and its transform `E_n`
  obtain ⟨E, hE1, hEd⟩ := hE
  obtain ⟨En, hEnZ, hEn⟩ := exists_horizontal_floor hZ hZ2 P hdims E
    (map_genericPoint_eq_of_dense_image f E hEd) n hn
  -- the complement on `X_n`
  obtain ⟨M', _, N, hN, hcomp⟩ := exists_complementInv sX sZ hZ f hconn hDG M hGM P
  obtain ⟨L', -, ⟨u, hu⟩, ⟨e⟩⟩ := hcomp n hn
  set D' : QDivisor (modelSeq X P.Y n) :=
    Divisor.toQDivisor (divisorSeq K P.KY n) + divisorSeq (B - t • (Divisor.toQDivisor B.roundDown)) P.BY n with hD'
  set A' : QDivisor (modelSeq X P.Y n) := transformSeq P A n + t • transformSeq P (Divisor.toQDivisor B.roundDown) n with hA'
  have hsum : D' + A' =
      Divisor.toQDivisor (divisorSeq K P.KY n) + transformSeq P (B + A) n := by
    rw [hD', hA', divisorSeq_eq_transformSeq P n hn, transformSeq_sub_smul, transformSeq_add]
    abel
  have hDq : D'.IsQCartier := isQCartier_of_isQFactorial _ hXq _
  have hAq' : A'.IsQCartier := isQCartier_of_isQFactorial _ hXq _
  have hDAq : (D' + A').IsQCartier := isQCartier_of_isQFactorial _ hXq _
  -- `K_n + B_n + A_n` is trivial on the curves over `Z`
  have h0 : ∀ γ : ProperCurve (modelStr sX P.sY n), γ.IsContractedBy (modelMap f P.πY n) →
      (D' + A').intersectionNumber ℂ (modelStr sX P.sY n) γ.ι γ.dim_le hDAq = 0 := by
    intro γ hγ
    refine intersectionNumber_eq_zero_of_isLocalEquation_preimage (modelStr sX P.sY n) hXq
      (modelMap f P.πY n) hDAq hN (L := L' + principalDivisor u⁻¹) ?_ ?_ γ hγ
    · rw [map_add, hu, hsum, MMP.Mori.principalDivisor_inv, map_neg]
      abel
    · intro z
      obtain ⟨U, hzU, ψ, hψ⟩ :=
        exists_isLocalEquation_preimage_of_iso_pullback (modelMap f P.πY n) M' e z
      refine ⟨U, hzU, ψ * u⁻¹, fun F hF => ?_⟩
      rw [DivisorWithCoeffs.coeff_add, hψ F hF, coeff_principalDivisor, PrimeDivisor.ord_mul]
  -- `K_n + B_n - tT_n` is nef over `Z` by assumption
  have hD'nef : D'.IsRelativelyNef (modelStr sX P.sY n) (modelMap f P.πY n) :=
    MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor hDq hnefR
  -- `A_n + tT_n ≥ 0`, positive along `E_n`
  have hT0 : ∀ F₀, (0 : ℚ) ≤ (Divisor.toQDivisor B.roundDown) F₀ := fun F₀ => by
    change (0 : ℚ) ≤ ((⌊B.coeff F₀⌋ : ℤ) : ℚ)
    exact_mod_cast Int.floor_nonneg.mpr (hKB.2.1 F₀).1
  have hA0 : ∀ F₀, (0 : ℚ) ≤ A F₀ := fun F₀ => by simpa using hA F₀
  have hA'0 : 0 ≤ A' := by
    refine Finsupp.le_def.mpr fun F => ?_
    obtain ⟨F₀, hF₀⟩ := transformSeq_coeff P n hn F
    change (0 : ℚ) ≤ (transformSeq P A n + t • transformSeq P (Divisor.toQDivisor B.roundDown) n) F
    rw [Finsupp.add_apply, Finsupp.smul_apply, hF₀, hF₀, smul_eq_mul]
    have := hA0 F₀
    have := hT0 F₀
    positivity
  -- a fibre curve through `E_n` not contained in `Supp (A_n + tT_n)`
  obtain ⟨ξ, x, hξx, hxcl, hxE, hξA, hξ⟩ := exists_fibre_specialization
    (modelStr sX P.sY n) sZ hXv hZv (modelMap f P.πY n) hmod.comp_eq (hdims n hn) hZ2 En hEnZ
    A'.support
  have hxA : x ∈ A'.supp := by
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨En, ?_, hxE⟩
    change (transformSeq P A n + t • transformSeq P (Divisor.toQDivisor B.roundDown) n) En ≠ 0
    rw [Finsupp.add_apply, Finsupp.smul_apply, hEn, hEn, smul_eq_mul]
    have h1 := hA0 E
    have h2 : (1 : ℚ) ≤ (Divisor.toQDivisor B.roundDown) E := by
      change (1 : ℚ) ≤ ((⌊B.coeff E⌋ : ℤ) : ℚ)
      exact_mod_cast Int.le_floor.mpr (by exact_mod_cast hE1)
    have : 0 < A E + t * (Divisor.toQDivisor B.roundDown) E := by nlinarith
    exact this.ne'
  have hξA' : ξ ∉ A'.supp := by
    intro h
    obtain ⟨F, hF, hξF⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    exact hξA F (Finsupp.mem_support_iff.mpr hF) hξF
  exact false_of_forall_intersectionNumber_add_eq_zero (modelStr sX P.sY n) (modelMap f P.πY n)
    hDq hAq' hDAq hD'nef hA'0 h0 hξx hxcl hxA hξA' hξ

/-! ### The floor surface -/

section FloorSurface

/-- The generic point of a prime divisor `P` lies outside the support of a divisor with vanishing
coefficient along `P`. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {X : Scheme.{0}} {R : Type*} [Zero R]
    {D : DivisorWithCoeffs R X} {P : MMP.Mori.PrimeDivisor X} (h : D.coeff P = 0) :
    P.genericPoint ∉ D.supp := by
  intro hP
  obtain ⟨F, hF, hPF⟩ := DivisorWithCoeffs.mem_supp_iff.mp hP
  obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hPF
  exact hF h

/-- A Cartier divisor is linearly equivalent to a Cartier divisor with vanishing coefficient along
a given prime divisor. -/
private theorem exists_linearlyEquivalent_coeff_eq_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ D' : Divisor X, D'.IsCartier ∧ D.LinearlyEquivalent D' ∧ D'.coeff P = 0 := by
  obtain ⟨φ, hφ⟩ := MMP.Positivity.PrimeDivisor.exists_ord_eq_one P
  refine ⟨D + principalDivisor (φ ^ (-D.coeff P)), hD.add (Divisor.isCartier_principalDivisor _),
    ⟨(φ ^ (-D.coeff P))⁻¹, ?_⟩, ?_⟩
  · rw [MMP.Mori.principalDivisor_inv]
    abel
  · rw [DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor, PrimeDivisor.ord_zpow, hφ]
    simp

/-- Linearly equivalent Cartier divisors have the same degree on a proper curve. -/
private theorem degreeOn_eq_of_linearlyEquivalent {k : Type} [Field k] {X C : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D D' : Divisor X}
    (hD : D.IsCartier) (hD' : D'.IsCartier) (h : D.LinearlyEquivalent D') :
    D.degreeOn k sX i hdim hD = D'.degreeOn k sX i hdim hD' := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := hD'.isInvertibleModule_divisorialSheaf
  change MMP.Mori.degreeOn k sX i hdim D.divisorialSheaf =
    MMP.Mori.degreeOn k sX i hdim D'.divisorialSheaf
  exact MMP.Mori.degreeOn_eq_of_iso k sX i hdim h.divisorialSheafIso

/-- In an integral scheme of finite type over `ℂ` of dimension `d`, a point whose closure has
dimension `d` is the generic point. -/
private theorem eq_genericPoint_of_topologicalKrullDim_closure_eq {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℂ)) [IsIntegral T] [LocallyOfFiniteType sT] {d : ℕ}
    (hT : topologicalKrullDim T = d) (x : T)
    (hx : topologicalKrullDim (closure ({x} : Set T)) = d) : x = genericPoint T := by
  letI : T.Over (Spec (.of ℂ)) := ⟨sT⟩
  haveI : LocallyOfFiniteType (T ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sT›
  have huniv : topologicalKrullDim (Set.univ : Set T) = d := by
    rw [← hT]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
  have h := MMP.Fourfold.ConductorBlowup.eq_of_subset_of_topologicalKrullDim_eq hT
    isClosed_closure isIrreducible_singleton.closure isClosed_univ
    (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _) hx huniv
  exact ((genericPoint_spec T).eq (show IsGenericPoint x ⊤ from h)).symm

end FloorSurface

/-- **Semiampleness of the base from the floor surface.** Let `Y` be a normal projective complex
threefold over a projective surface `Z` by `π`, with `π = g_T ∘ g` through a proper `g : Y ⟶ T` to
a normal surface `T`, let `(Y, B)` and `(Y, B + A)` be lc with `K + B` nef over `Z`, let
`m(K + B) ∼ L ∼ g^* M'` and `n'(K + B + A) ∼ L'` with `𝒪(L') ≅ π^* 𝓜` for an invertible `𝓜` on
`Z`, and let `E ⊆ Y` be a prime divisor dominating `Z`. If `e : V ⟶ Y` is a crepant dlt
modification of `(Y, B)` and `(S, B_S)` is obtained from `(V, B_V)` by adjunction to the strict
transform of `E`, then a positive multiple of `M'` is relatively free over `Z`: `(S, B_S)` is a
complemented lc surface over `Z` whose adjoint is `ℚ`-linearly equivalent to the pull-back of
`M' / m` along the generically finite `S ⟶ T`; it is semiample over `Z`, and this descends to
`T`. -/
private theorem floor_free {Y Z T V S : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    (hYp : Mori.IsProjectiveVariety ℂ sY) (hYn : MMP.Mori.IsNormalVariety ℂ sY)
    (hY3 : topologicalKrullDim Y = 3) (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (hZ2 : topologicalKrullDim Z = 2) (hTn : MMP.Mori.IsNormalVariety ℂ sT)
    (hT2 : topologicalKrullDim T = 2)
    {π : Y ⟶ Z} (hπ : π ≫ sZ = sY) {g : Y ⟶ T} {gT : T ⟶ Z} (hgπ : g ≫ gT = π)
    (hgs : gT ≫ sZ = sT) [IsProper g]
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY 3) {BY AY : QDivisor Y} (hAY : 0 ≤ AY)
    (hlcB : MMP.Intersection.IsLogCanonicalPair sY BY)
    (hlcBA : MMP.Intersection.IsLogCanonicalPair sY (BY + AY))
    (hnef : (Divisor.toQDivisor KY + BY).IsRelativelyNef sY π)
    {m : ℕ} (hm : 0 < m) {LY : Divisor Y} (hLYc : LY.IsCartier)
    (hLY : ∃ u : (RationalFunctions Y)ˣ, Divisor.toQDivisor LY =
      (m : ℤ) • (Divisor.toQDivisor KY + BY) + Divisor.toQDivisor (principalDivisor u))
    {M' : Divisor T} (hM'c : M'.IsCartier)
    (hM' : ∀ T' : irreducibleComponents Y, g (componentGenericPoint Y T') ∉ M'.supp)
    (hM'L : (M'.pullback hM'c hM').LinearlyEquivalent LY)
    (MC : Z.Modules) [Stacks.Ample.IsInvertibleModule Z MC] {n' : ℕ} (hn' : 0 < n')
    {L' : Divisor Y} (hL'c : L'.IsCartier)
    (hL' : ∃ u' : (RationalFunctions Y)ˣ, Divisor.toQDivisor L' =
      (n' : ℤ) • (Divisor.toQDivisor KY + (BY + AY)) + Divisor.toQDivisor (principalDivisor u'))
    (eL' : L'.divisorialSheaf ≅ (Scheme.Modules.pullback π).obj MC)
    (E : MMP.Mori.PrimeDivisor Y) (hEZ : π E.genericPoint = genericPoint Z)
    (e : V ⟶ Y) (he : MMP.Mori.IsBirationalMorphism e)
    (hVq : MMP.Fourfold.IsQFactorial (e ≫ sY)) {BV : QDivisor V}
    (heproj : IsProjectiveMorphism e) (hVdlt : MMP.Intersection.IsDltPair (e ≫ sY) BV)
    (hcb : MMP.Mori.IsCrepantBoundary sY 3 KY BY e hVq.1 he BV)
    (S₀ : MMP.Mori.PrimeDivisor V) (hS₀ : e S₀.genericPoint = E.genericPoint)
    (j : S ⟶ V) {BS : QDivisor S} (hadj : MMP.Fourfold.IsAdjunctionStep (e ≫ sY) BV j BS)
    (hjrange : Set.range j.base = (S₀.support : Set V)) :
    ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor gT ((k : ℤ) • M') := by
  classical
  -- instances
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : LocallyOfFiniteType sT := hTn.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ sY := hYn.1
  haveI : IsProper e := isProper_of_isProjectiveMorphism e heproj
  have hVn : MMP.Mori.IsNormalVariety ℂ (e ≫ sY) := hVq.1
  haveI : MMP.Mori.IsVariety ℂ (e ≫ sY) := hVn.1
  haveI : LocallyOfFiniteType (e ≫ sY) := hVn.1.toLocallyOfFiniteType
  haveI : QuasiCompact (e ≫ sY) := hVn.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (e ≫ sY)
  haveI : IsDominant e := he.isDominant
  obtain ⟨hSn, -, -, -, hci, -⟩ := id hadj
  haveI := hci
  haveI : IsIntegral S := hSn.1.toIsIntegral
  haveI : LocallyOfFiniteType (j ≫ e ≫ sY) := hSn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (j ≫ e ≫ sY)
  haveI : IsNormal S := hSn.2
  haveI : QuasiCompact (j ≫ e ≫ sY) := hSn.1.toQuasiCompact
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (j ≫ e ≫ sY)
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn'Q : (n' : ℚ) ≠ 0 := by exact_mod_cast hn'.ne'
  -- dimensions and generic points
  have hV3 : topologicalKrullDim V = 3 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (e ≫ sY) he]
    exact hY3
  have hS2 : topologicalKrullDim S = ((2 : ℕ) : WithBot ℕ∞) :=
    MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support (e ≫ sY) (n := 2)
      (by rw [hV3]; rfl) j S₀ hjrange
  have hjη : j (genericPoint S) = S₀.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j S₀ hjrange
  have hjeη : (j ≫ e) (genericPoint S) = E.genericPoint := by
    rw [Scheme.Hom.comp_apply, hjη, hS₀]
  have hgE : g E.genericPoint = genericPoint T := by
    have h1 := topologicalKrullDim_closure_map_le sT sZ gT hgs (g E.genericPoint)
    rw [← Scheme.Hom.comp_apply, hgπ, hEZ, (genericPoint_spec Z).def] at h1
    have hu : topologicalKrullDim (Set.univ : Set Z) = 2 := by
      rw [← hZ2]
      exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
    rw [hu] at h1
    have h2 := topologicalKrullDim_subspace_le T (closure {g E.genericPoint})
    rw [hT2] at h2
    exact eq_genericPoint_of_topologicalKrullDim_closure_eq sT (d := 2)
      (by rw [hT2]; rfl) _ (by rw [le_antisymm h2 h1]; rfl)
  set q : S ⟶ T := j ≫ e ≫ g with hq_def
  have hqη : q (genericPoint S) = genericPoint T := by
    rw [hq_def, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hjη, hS₀, hgE]
  haveI : IsDominant q := ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_forall
    fun w => closure_mono (Set.singleton_subset_iff.mpr
      (show genericPoint T ∈ Set.range q from ⟨_, hqη⟩))
      (by rw [(genericPoint_spec T).def]; trivial))⟩
  haveI : IsProper q := by rw [hq_def]; infer_instance
  haveI : Surjective q := by
    refine ⟨Set.range_eq_univ.mp ?_⟩
    have hcl : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
    rw [← hcl.closure_eq]
    exact q.denseRange.closure_range
  have hgsY : g ≫ sT = sY := by rw [← hgs, ← Category.assoc, hgπ, hπ]
  have hqs : q ≫ sT = j ≫ e ≫ sY := by rw [hq_def, Category.assoc, Category.assoc, hgsY]
  have hqf : q ≫ gT = (j ≫ e) ≫ π := by
    rw [hq_def, Category.assoc, Category.assoc, Category.assoc, hgπ]
  -- a rational top form on `Y` and the canonical divisor `K_V = div(e^* ω)` of `V`
  obtain ⟨ωY, hωY0, hωY⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYn hKY
  have hdivY : divisorOfForm ωY = KY := Finsupp.ext fun Q => hωY Q
  have htrY := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hY3
  have hωV0 := MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero e
    he.functionFieldMap_bijective htrY hωY0
  obtain ⟨KV₀, hKV₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (e ≫ sY) hVn hV3
  have hKV : (divisorOfForm (pullbackRationalPluriForms sY e ωY)).IsCanonicalDivisor
      (e ≫ sY) 3 := by
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hVn hKV₀ hωV0
    rw [one_zsmul] at h
    exact hKV₀.of_linearlyEquivalent h
  set KV := divisorOfForm (pullbackRationalPluriForms sY e ωY) with hKV_def
  -- the crepant pull-back of `m(K + B)`
  obtain ⟨hcB, hPV, -⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hlcB.1 e hVn he hKY hKV
    (Or.inl ⟨ωY, hωY0, hdivY, rfl⟩) hcb
  obtain ⟨u, hu⟩ := hLY
  have hD₁c : (LY - principalDivisor u).IsCartier := hLYc.sub (Divisor.isCartier_principalDivisor u)
  have hD₁ : Divisor.toQDivisor (LY - principalDivisor u) =
      (m : ℤ) • (Divisor.toQDivisor KY + BY) := by
    rw [map_sub, hu]
    abel
  obtain ⟨D₁V, hD₁V, hD₁Vc, hD₁B, hD₁p⟩ := hcB m hm _ hD₁ hD₁c
  -- the complement `A_V = e^* A` and its crepant relation on `V`
  obtain ⟨u', hu'⟩ := hL'
  have hG₁c : (L' - principalDivisor u').IsCartier := hL'c.sub (Divisor.isCartier_principalDivisor u')
  have hG₁ : Divisor.toQDivisor (L' - principalDivisor u') =
      (n' : ℤ) • (Divisor.toQDivisor KY + (BY + AY)) := by
    rw [map_sub, hu']
    abel
  have hG₁B := map_componentGenericPoint_notMem_supp_of_isDominant e (L' - principalDivisor u')
  have hG₁p := Divisor.isPullback_pullback hG₁c hG₁B
  have hG₁Vc := hG₁c.isCartier_pullback e hG₁B
  set G₁V := (L' - principalDivisor u').pullback hG₁c hG₁B with hG₁V_def
  set F : Divisor Y := (m : ℤ) • (L' - principalDivisor u') +
    (-(n' : ℤ)) • (LY - principalDivisor u) with hF_def
  have hFc : F.IsCartier := (hG₁c.zsmul _).add (hD₁c.zsmul _)
  have hFp : F.IsPullback e (map_componentGenericPoint_notMem_supp_of_isDominant e F)
      ((m : ℤ) • G₁V + (-(n' : ℤ)) • D₁V) :=
    Divisor.IsPullback.add (hG₁c.zsmul _) (hD₁c.zsmul _) _
      (hG₁p.zsmul hG₁c _ (map_componentGenericPoint_notMem_supp_of_isDominant e _))
      (hD₁p.zsmul hD₁c _ (map_componentGenericPoint_notMem_supp_of_isDominant e _))
  set FV : Divisor V := (m : ℤ) • G₁V + (-(n' : ℤ)) • D₁V with hFV_def
  have hFVc : FV.IsCartier := (hG₁Vc.zsmul _).add (hD₁Vc.zsmul _)
  have hF : Divisor.toQDivisor F = ((m * n' : ℕ) : ℤ) • AY := by
    ext P
    have h1 := congrArg (fun D : QDivisor Y => D.coeff P) hG₁
    have h2 := congrArg (fun D : QDivisor Y => D.coeff P) hD₁
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul, Int.cast_natCast] at h1 h2
    simp only [hF_def, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
    rw [h1, h2]
    ring
  have hF0 : ∀ P, 0 ≤ F.coeff P := fun P => by
    have h := congrArg (fun D : QDivisor Y => D.coeff P) hF
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h
    have hA : (0 : ℚ) ≤ AY.coeff P := (Finsupp.le_def.mp hAY) P
    have : (0 : ℚ) ≤ (F.coeff P : ℚ) := by rw [h]; positivity
    exact_mod_cast this
  have hFV0 : ∀ P, 0 ≤ FV.coeff P := fun P =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hFc (V := ⊤) (fun Q _ => hF0 Q)
      hFp P ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, by simp⟩
  have hmn' : 0 < m * n' := Nat.mul_pos hm hn'
  set AV : QDivisor V := ((m * n' : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor FV with hAV_def
  have hAV0 : 0 ≤ AV := Finsupp.le_def.mpr fun P => by
    have h := hFV0 P
    change (0 : ℚ) ≤ ((m * n' : ℕ) : ℚ)⁻¹ * (FV.coeff P : ℚ)
    have : (0 : ℚ) ≤ (FV.coeff P : ℚ) := by exact_mod_cast h
    positivity
  have hAVq : AV.IsQCartier := isQCartier_inv_smul_toQDivisor hFVc hmn'
  have hrelV' : Divisor.toQDivisor G₁V = (n' : ℤ) • (Divisor.toQDivisor KV + (BV + AV)) := by
    ext P
    have h1 := congrArg (fun D : QDivisor V => D.coeff P) hD₁V
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul, Int.cast_natCast] at h1
    simp only [hAV_def, hFV_def, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
    rw [h1]
    field_simp
    ring
  have hKBAV : Divisor.toQDivisor KV + BV + AV = (n' : ℚ)⁻¹ • Divisor.toQDivisor G₁V := by
    rw [hrelV', ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hn'Q,
      one_smul, add_assoc]
  -- `(V, B_V + A_V)` is lc, being crepant to `(Y, B + A)`
  have hBV0 : 0 ≤ BV := Finsupp.le_def.mpr fun P => hVdlt.1.2.1 P
  have hlcV : MMP.Intersection.IsLogCanonicalPair (e ≫ sY) (BV + AV) :=
    (isLogCanonicalPair_iff_of_crepant e rfl hVn he (hdivY ▸ hKY) hKV
      (transformDivisor_divisorOfForm_pullback e hYn hVn he htrY ωY) hlcBA.1 hn' hG₁c
      (by rw [hdivY]; exact hG₁.symm) hrelV'.symm ⟨hG₁B, hG₁p⟩).1 hlcBA (add_nonneg hBV0 hAV0)
  have hPV' : MMP.Fourfold.IsPair (e ≫ sY) BV :=
    ⟨inferInstance, inferInstance, hPV, hVdlt.1.2.1⟩
  -- (i) the complement on `S`: `K_S + B_S + A_S ∼_ℚ (1/n') (j ≫ e)^* L'`
  have hHq := isQCartier_inv_smul_toQDivisor hG₁c hn'
  have hgH := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier e hHq
  have hlinV : (Divisor.toQDivisor KV + BV + AV).QLinearlyEquivalent
      (((n' : ℚ)⁻¹ • Divisor.toQDivisor (L' - principalDivisor u')).pullback hHq hgH) := by
    rw [QDivisor.IsPullback.pullback_eq hHq (isPullback_inv_smul_toQDivisor hG₁c hG₁p hn' hgH),
      hKBAV]
  obtain ⟨hAS, hAS0, hASq, hlcS, hlinS⟩ :=
    MMP.Fourfold.IsAdjunctionStep.exists_isLogCanonicalPair_add_pullback (n := 2) hKV hPV' hVq
      hVdlt heproj hAV0 hAVq hlcV hHq hgH hlinV hadj
  -- (iii) the adjoint on `S`: `K_S + B_S ∼_ℚ (1/m) (j ≫ e)^* (m (K + B))`
  have h0q : (0 : QDivisor V).IsQCartier := ⟨1, one_ne_zero, 0, by simp, Divisor.isCartier_zero⟩
  have hlcV0 : MMP.Intersection.IsLogCanonicalPair (e ≫ sY) (BV + 0) := by
    rw [add_zero]; exact hVdlt.1
  have hH₀q := isQCartier_inv_smul_toQDivisor hD₁c hm
  have hgH₀ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier e hH₀q
  have hlinV0 : (Divisor.toQDivisor KV + BV + 0).QLinearlyEquivalent
      (((m : ℚ)⁻¹ • Divisor.toQDivisor (LY - principalDivisor u)).pullback hH₀q hgH₀) := by
    rw [QDivisor.IsPullback.pullback_eq hH₀q (isPullback_inv_smul_toQDivisor hD₁c hD₁p hm hgH₀),
      add_zero, hD₁V, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
      inv_mul_cancel₀ hmQ, one_smul]
  obtain ⟨hAS₀, -, -, hlcS0, hlinS0⟩ :=
    MMP.Fourfold.IsAdjunctionStep.exists_isLogCanonicalPair_add_pullback (n := 2) hKV hPV' hVq
      hVdlt heproj le_rfl h0q hlcV0 hH₀q hgH₀ hlinV0 hadj
  have h0pb : (0 : QDivisor V).pullback h0q hAS₀ = 0 := by
    refine QDivisor.IsPullback.pullback_eq h0q fun k _ D hD _ => ?_
    obtain rfl : D = 0 := Divisor.toQDivisor_injective (by simpa using hD)
    exact ⟨0, by simp, Divisor.isPullback_zero _⟩
  rw [h0pb, add_zero] at hlcS0
  -- a canonical divisor of `S`
  obtain ⟨KS, hKS⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (j ≫ e ≫ sY) hSn hS2
  have hcgS : ∀ T' : irreducibleComponents S,
      (j ≫ e) (componentGenericPoint S T') = E.genericPoint := fun T' => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjeη]
  -- the moved divisors, whose support does not contain `E`
  obtain ⟨G₂, hG₂c, hG₁G₂, hG₂E⟩ := exists_linearlyEquivalent_coeff_eq_zero hG₁c E
  obtain ⟨D₂, hD₂c, hD₁D₂, hD₂E⟩ := exists_linearlyEquivalent_coeff_eq_zero hD₁c E
  have hG₂B : ∀ T' : irreducibleComponents S, (j ≫ e) (componentGenericPoint S T') ∉ G₂.supp :=
    fun T' => by rw [hcgS]; exact genericPoint_notMem_supp_of_coeff_eq_zero hG₂E
  have hD₂B : ∀ T' : irreducibleComponents S, (j ≫ e) (componentGenericPoint S T') ∉ D₂.supp :=
    fun T' => by rw [hcgS]; exact genericPoint_notMem_supp_of_coeff_eq_zero hD₂E
  have hG₂q := isQCartier_inv_smul_toQDivisor hG₂c hn'
  have hD₂q := isQCartier_inv_smul_toQDivisor hD₂c hm
  have hG₂B' : ∀ T' : irreducibleComponents S, (j ≫ e) (componentGenericPoint S T') ∉
      ((n' : ℚ)⁻¹ • Divisor.toQDivisor G₂).supp := fun T' => by
    rw [hcgS]
    exact genericPoint_notMem_supp_of_coeff_eq_zero (by simp [hG₂E])
  have hD₂B' : ∀ T' : irreducibleComponents S, (j ≫ e) (componentGenericPoint S T') ∉
      ((m : ℚ)⁻¹ • Divisor.toQDivisor D₂).supp := fun T' => by
    rw [hcgS]
    exact genericPoint_notMem_supp_of_coeff_eq_zero (by simp [hD₂E])
  have hqlin : ∀ {G G' : Divisor Y} {k : ℕ}, 0 < k → G.LinearlyEquivalent G' →
      ((k : ℚ)⁻¹ • Divisor.toQDivisor G').QLinearlyEquivalent
        ((k : ℚ)⁻¹ • Divisor.toQDivisor G) := fun {G G' k} hk hGG' => by
    obtain ⟨φ, hφ⟩ := hGG'
    have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    refine MMP.Mori.QDivisor.QLinearlyEquivalent.symm ⟨k, hk, φ, ?_⟩
    rw [← smul_sub, ← map_sub, hφ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
      mul_inv_cancel₀ hkQ, one_smul]
  set G₂S := G₂.pullback hG₂c hG₂B with hG₂S_def
  have hG₂Sp := Divisor.isPullback_pullback hG₂c hG₂B
  have hG₂Sc : G₂S.IsCartier := hG₂c.isCartier_pullback (j ≫ e) hG₂B
  set D₂S := D₂.pullback hD₂c hD₂B with hD₂S_def
  have hD₂Sp := Divisor.isPullback_pullback hD₂c hD₂B
  have hD₂Sc : D₂S.IsCartier := hD₂c.isCartier_pullback (j ≫ e) hD₂B
  have hlinS' := hlinS KS hKS _ hG₂q hG₂B' (hqlin hn' hG₁G₂)
  rw [QDivisor.IsPullback.pullback_eq hG₂q (isPullback_inv_smul_toQDivisor hG₂c hG₂Sp hn' hG₂B')]
    at hlinS'
  have hlinS0' := hlinS0 KS hKS _ hD₂q hD₂B' (hqlin hm hD₁D₂)
  rw [QDivisor.IsPullback.pullback_eq hD₂q (isPullback_inv_smul_toQDivisor hD₂c hD₂Sp hm hD₂B'),
    h0pb, add_zero] at hlinS0'
  -- `K_S + B_S` is `ℚ`-Cartier and nef over `Z`
  obtain ⟨N₀, hN₀, φ, hφ⟩ := hlinS0'
  set FS : Divisor S := (N₀ : ℤ) • D₂S + (m : ℤ) • principalDivisor φ with hFS_def
  have hFSc : FS.IsCartier := (hD₂Sc.zsmul _).add ((Divisor.isCartier_principalDivisor φ).zsmul _)
  have hFS : Divisor.toQDivisor FS = ((m * N₀ : ℕ) : ℤ) • (Divisor.toQDivisor KS + BS) := by
    ext P
    have h1 := congrArg (fun D : QDivisor S => D.coeff P) hφ
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, zsmul_eq_mul, smul_eq_mul, Int.cast_natCast] at h1
    simp only [hFS_def, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul]
    have hinv : (m : ℚ) * (m : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hmQ
    linear_combination (-(m : ℚ)) * h1 - ((N₀ : ℚ) * (D₂S.coeff P : ℚ)) * hinv
  have hmN₀ : 0 < m * N₀ := Nat.mul_pos hm hN₀
  have hKSq : (Divisor.toQDivisor KS + BS).IsQCartier :=
    ⟨((m * N₀ : ℕ) : ℤ), by exact_mod_cast hmN₀.ne', FS, hFS, hFSc⟩
  have hKBq : (Divisor.toQDivisor KY + BY).IsQCartier :=
    ⟨(m : ℤ), by exact_mod_cast hm.ne', _, hD₁, hD₁c⟩
  have hD₂nef : MMP.Flips.IsRelativelyNef ℂ sY π (Divisor.toRDivisor D₂) :=
    isRelativelyNef_toRDivisor_of_degreeOn_nonneg hD₂c fun C hC => by
      rw [← degreeOn_eq_of_linearlyEquivalent sY C.ι C.dim_le hD₁c hD₂c hD₁D₂]
      have h1 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sY hnef hKBq C hC
      rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sY C.ι C.dim_le _ hKBq hm _ hD₁c hD₁]
        at h1
      have h2 : (0 : ℚ) ≤ ((LY - principalDivisor u).degreeOn ℂ sY C.ι C.dim_le hD₁c : ℚ) := by
        have hmQ' : (0 : ℚ) < m := by exact_mod_cast hm
        exact (div_nonneg_iff.mp h1).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hmQ')
      exact_mod_cast h2
  have hD₂Snef : MMP.Flips.IsRelativelyNef ℂ (j ≫ e ≫ sY) ((j ≫ e) ≫ π)
      (Divisor.toRDivisor D₂S) :=
    MMP.Flips.IsRelativelyNef.comp_of_isRCartierPullback (j ≫ e) (Category.assoc _ _ _) π rfl hD₂nef
      (isRCartierPullback_toRDivisor hD₂c hD₂Sp)
  have hnefS : (Divisor.toQDivisor KS + BS).IsRelativelyNef (j ≫ e ≫ sY) ((j ≫ e) ≫ π) :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (j ≫ e ≫ sY) hKSq
      fun C hC => by
        rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ _ C.ι C.dim_le _ hKSq hmN₀ FS hFSc
          hFS]
        have hlin : FS.LinearlyEquivalent ((N₀ : ℤ) • D₂S) :=
          ⟨φ ^ (m : ℤ), by rw [hFS_def, principalDivisor_zpow]; abel⟩
        rw [degreeOn_eq_of_linearlyEquivalent _ C.ι C.dim_le hFSc (hD₂Sc.zsmul _) hlin,
          MMP.Fourfold.degreeOn_zsmul (j ≫ e ≫ sY) C.ι C.dim_le D₂S hD₂Sc]
        have h1 := degreeOn_nonneg_of_isRelativelyNef hD₂Sc hD₂Snef C hC
        have h2 : (0 : ℚ) ≤ (D₂S.degreeOn ℂ (j ≫ e ≫ sY) C.ι C.dim_le hD₂Sc : ℚ) := by
          exact_mod_cast (show (0 : ℝ) ≤ _ from h1)
        have h3 : (0 : ℚ) ≤ (((N₀ : ℤ) * D₂S.degreeOn ℂ (j ≫ e ≫ sY) C.ι C.dim_le hD₂Sc : ℤ) : ℚ) := by
          push_cast
          exact mul_nonneg (Nat.cast_nonneg _) h2
        exact div_nonneg h3 (Nat.cast_nonneg _)
  -- the surface theorem on `S` over `Z`
  have hSproj : Mori.IsProjectiveVariety ℂ (j ≫ e ≫ sY) := by
    refine (Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hSn.1, ?_⟩
    obtain ⟨N, i, hi, hcomp⟩ := IsProjectiveMorphism.comp heproj
      ((Mori.isProjectiveVariety_iff ℂ sY).mp hYp).2
    haveI := hi
    exact ⟨N, j ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩
  obtain ⟨eG⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := G₂) hG₂c (j ≫ e) hG₂B
  have hG₂L' : G₂.LinearlyEquivalent L' :=
    hG₁G₂.symm.trans ⟨u'⁻¹, by rw [MMP.Mori.principalDivisor_inv]; abel⟩
  obtain ⟨m₁, hm₁, LS, hLS, hLSc, hLSfree⟩ :=
    MMP.Threefold.exists_isRelativelyFreeDivisor_of_isLogCanonicalPair_of_add_qLinearlyEquivalent
      (j ≫ e ≫ sY) sZ hSproj hKS hlcS0 hZ ((j ≫ e) ≫ π)
      (by simp only [Category.assoc, hπ]) hnefS hAS0 hASq hlinS' MC
      ⟨n', hn', G₂S, by
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        simp [hn'.ne', hG₂S_def],
        ⟨eG ≪≫ (Scheme.Modules.pullback (j ≫ e)).mapIso (hG₂L'.divisorialSheafIso ≪≫ eL') ≪≫
          (Scheme.Modules.pullbackComp (j ≫ e) π).app MC⟩⟩
  -- `D₂S ∼ q^* M'`
  have hM'q := map_componentGenericPoint_notMem_supp_of_isDominant q M'
  obtain ⟨eD⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := D₂) hD₂c (j ≫ e) hD₂B
  obtain ⟨eMg⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := M') hM'c g hM'
  obtain ⟨eMq⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (D := M') hM'c q hM'q
  have hD₂M : D₂.LinearlyEquivalent (M'.pullback hM'c hM') :=
    hD₁D₂.symm.trans (Divisor.LinearlyEquivalent.trans ⟨u⁻¹, by rw [MMP.Mori.principalDivisor_inv]; abel⟩
      hM'L.symm)
  have hψ : D₂S.LinearlyEquivalent (M'.pullback hM'c hM'q) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (eD ≪≫ (Scheme.Modules.pullback (j ≫ e)).mapIso (hD₂M.divisorialSheafIso ≪≫ eMg) ≪≫
        (Scheme.Modules.pullbackComp (j ≫ e) g).app M'.divisorialSheaf ≪≫
        eqToIso (congrArg (fun h => (Scheme.Modules.pullback h).obj M'.divisorialSheaf)
          (by rw [hq_def, Category.assoc])) ≪≫ eMq.symm)
  obtain ⟨ψ, hψ⟩ := hψ
  -- descent along `q : S ⟶ T`
  have hLTq := isQCartier_inv_smul_toQDivisor hM'c hm
  have hLTB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier q hLTq
  haveI : LocallyOfFiniteType (q ≫ sT) := hqs ▸ inferInstance
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q sT
  have hfin := MMP.Mori.finite_functionField_of_topologicalKrullDim_eq sT q
    (by rw [hS2, hT2]; rfl)
  obtain ⟨m₃, hm₃, MT, hMT, hMTc, hMTfree⟩ :=
    MMP.Fourfold.exists_isRelativelyFreeDivisor_of_pullback (j ≫ e ≫ sY) sT hSn hTn q hqs hfin gT
      _ hLTq ⟨m₁ * N₀ * m, by positivity,
        (m * N₀ : ℤ) • LS + (-(m₁ * N₀ : ℤ)) • principalDivisor ψ +
          (-(m₁ * m : ℤ)) • principalDivisor φ, by
        rw [QDivisor.IsPullback.pullback_eq hLTq
          (isPullback_inv_smul_toQDivisor hM'c (Divisor.isPullback_pullback hM'c hM'q) hm hLTB)]
        ext P
        have h1 := congrArg (fun D : QDivisor S => D.coeff P) hφ
        have h2 := congrArg (fun D : Divisor S => D.coeff P) hψ
        have h3 := congrArg (fun D : QDivisor S => D.coeff P) hLS
        simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
          DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, zsmul_eq_mul, smul_eq_mul,
          Int.cast_natCast] at h1 h3
        simp only [DivisorWithCoeffs.coeff_sub] at h2
        simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
          DivisorWithCoeffs.coeff_add, zsmul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_mul,
          Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
        have h2' : ((D₂S.coeff P : ℤ) : ℚ) - ((M'.pullback hM'c hM'q).coeff P : ℚ) =
            ((principalDivisor ψ).coeff P : ℚ) := by exact_mod_cast h2
        have hinv : (m : ℚ) * (m : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hmQ
        linear_combination ((m : ℚ) * N₀) * h3 + ((m₁ : ℚ) * N₀) * h2' + ((m₁ : ℚ) * m) * h1 +
          ((m₁ : ℚ) * N₀ * ((D₂S.coeff P : ℚ) - ((M'.pullback hM'c hM'q).coeff P : ℚ))) * hinv,
        ((hLSc.zsmul _).add ((Divisor.isCartier_principalDivisor ψ).zsmul _)).add
          ((Divisor.isCartier_principalDivisor φ).zsmul _), by
        rw [hqf]
        refine IsRelativelyFreeDivisor.of_linearlyEquivalent _ (D := (m * N₀ : ℤ) • LS)
          ⟨ψ ^ (m₁ * N₀ : ℤ) * φ ^ (m₁ * m : ℤ), ?_⟩
          (by exact_mod_cast isRelativelyFreeDivisor_nsmul _ hLSc hLSfree (m * N₀))
        rw [MMP.Mori.principalDivisor_mul, principalDivisor_zpow, principalDivisor_zpow]
        simp only [neg_smul]
        abel⟩
  refine ⟨m₃, hm₃, ?_⟩
  have hkey : (m₃ : ℤ) • M' = (m : ℤ) • MT := by
    apply Divisor.toQDivisor_injective
    ext P
    have h := congrArg (fun D : QDivisor T => D.coeff P) hMT
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul,
      Int.cast_natCast, Int.cast_mul] at h ⊢
    rw [h]
    field_simp
  rw [hkey]
  exact isRelativelyFreeDivisor_nsmul gT hMTc hMTfree m

/-- **The base of the final contraction is semiample over `Z`.** Let `g : X_n ⟶ T`, `g_T : T ⟶ Z`
be the final fibre-type contraction, and `M'` a Cartier divisor on `T` with `g^* M' ∼ L_n`. Then
`T` is a surface birational over `Z`, and some multiple of `M'` is relatively free over `Z`: the
transform of a horizontal component of `⌊B⌋` on a crepant dlt modification of `X_n` is a
complemented lc surface over `Z`, whose adjoint `g^* M' / m` restricted to it is semiample over
`Z`, and semiampleness descends along this surface, generically finite over `T`. -/
private theorem final_free
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (hZ2 : topologicalKrullDim Z = 2) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hconn : ∀ z : Z, _root_.IsConnected (f ⁻¹' {z}))
    (hO : ∀ U : Z.Opens, IsIso (f.app U))
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A)) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    (hE : ∃ E : Mori.PrimeDivisor X, 1 ≤ B.coeff E ∧ Dense (f '' (E.support : Set X)))
    {m : ℕ} (hm : 0 < m) {L₀ : Divisor X} (hL₀ : Divisor.toQDivisor L₀ =
      (m : ℤ) • (Divisor.toQDivisor K + B)) (hL₀c : L₀.IsCartier)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (hPn : P.n ≠ ⊤)
    (hPend : MMP.Flips.IsRelativelyNef ℂ (modelStr sX P.sY P.n.toNat) (modelMap f P.πY P.n.toNat)
          (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
            divisorSeq (B - t • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat)) ∨
        P.hasFinal)
    (L : ∀ i, Divisor (modelSeq X P.Y i)) (hL0 : L 0 = L₀)
    (hL : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → NullInv P B m i (L i))
    (hstep : ∀ i : ℕ, (i : ℕ∞) < P.n → ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i))
        (_ : IsNormal (P.Z i)) (_ : CompactSpace (P.Z i)) (N : Divisor (P.Z i)) (hNc : N.IsCartier),
        ∃ (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
            P.f i (componentGenericPoint _ T) ∉ N.supp)
          (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp),
          (N.pullback hNc hN).LinearlyEquivalent (L i) ∧
            (N.pullback hNc hN').LinearlyEquivalent (L (i + 1)))
    (hfin : P.hasFinal) [IsIntegral P.T] [IsLocallyNoetherian P.T] [IsNormal P.T]
    [CompactSpace P.T] [IsDominant P.g] (M' : Divisor P.T) (hM'c : M'.IsCartier)
    (hM' : ∀ T' : irreducibleComponents (modelSeq X P.Y P.n.toNat),
      P.g (componentGenericPoint _ T') ∉ M'.supp)
    (hM'L : (M'.pullback hM'c hM').LinearlyEquivalent (L P.n.toNat)) :
    ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor P.gT ((k : ℤ) • M') := by
  classical
  have hn : (P.n.toNat : ℕ∞) ≤ P.n := ENat.coe_toNat_le_self _
  set n := P.n.toNat with hn_def
  obtain ⟨-, hc, hdimT⟩ := P.final_spec hfin
  have hmod := P.isRelativeDltModel n hn
  obtain ⟨hXv, hXproj⟩ := (Mori.isProjectiveVariety_iff ℂ _).mp (hPproj.2 n hn)
  have hZv : Mori.IsVariety ℂ sZ := ((Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  have hdims : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → topologicalKrullDim (modelSeq X P.Y i) = 3 :=
    fun i hi => (hL i hi).2.2.2.2.1.2.1.1
  have hT := hc.isNegativeExtremalContraction.isNormalVariety_target
  haveI : LocallyOfFiniteType P.sT := hT.1.toLocallyOfFiniteType
  have hgπ : P.g ≫ P.gT = modelMap f P.πY n := hc.isRelativeContractionOfFace.comp_eq
  have hgs : P.gT ≫ sZ = P.sT := by
    refine ext_of_isDominant_of_isSeparated (Limits.terminal.from _)
      (Limits.terminal.hom_ext _ _) P.g ?_
    rw [← Category.assoc, hgπ, hmod.comp_eq, hc.isNegativeExtremalContraction.isContraction.comp_eq]
  -- the horizontal floor `E_n` of `X_n`
  obtain ⟨E, hE1, hEd⟩ := hE
  obtain ⟨En, hEnZ, hEn⟩ := exists_horizontal_floor hZ hZ2 P hdims E
    (map_genericPoint_eq_of_dense_image f E hEd) n hn
  -- (1) `T` is a surface over `Z`
  have hgTgen : P.gT (P.g En.genericPoint) = genericPoint Z := by
    rw [← Scheme.Hom.comp_apply, hgπ]; exact hEnZ
  have hgTdom : IsDominant P.gT := ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_forall
    fun w => closure_mono (Set.singleton_subset_iff.mpr
      (show genericPoint Z ∈ Set.range P.gT from ⟨_, hgTgen⟩))
      (by rw [(genericPoint_spec Z).def]; trivial))⟩
  have hgT : P.gT (genericPoint P.T) = genericPoint Z := map_genericPoint_of_isDominant P.gT
  have hT2 : topologicalKrullDim P.T = 2 := by
    have hclT : topologicalKrullDim (closure {genericPoint P.T} : Set P.T) =
        topologicalKrullDim P.T := by
      rw [(genericPoint_spec P.T).def]
      exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
    have hclZ : topologicalKrullDim (closure {genericPoint Z} : Set Z) = 2 := by
      rw [(genericPoint_spec Z).def, ← hZ2]
      exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
    have h1 := topologicalKrullDim_closure_map_le P.sT sZ P.gT hgs (genericPoint P.T)
    rw [hgT, hclZ, hclT] at h1
    have h3 : topologicalKrullDim P.T < 3 := by rw [← hdims n hn]; exact hdimT
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, topologicalKrullDim P.T = d :=
      ⟨_, hclT.symm.trans (topologicalKrullDim_closure_singleton_eq_trdeg ℂ P.T P.sT _)⟩
    rw [hd] at h1 h3 ⊢
    have h1' : (2 : ℕ∞) ≤ d := by
      have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by push_cast; exact h1
      exact WithBot.coe_le_coe.mp this
    have h3' : d < 3 := by
      have : (d : WithBot ℕ∞) < ((3 : ℕ∞) : WithBot ℕ∞) := by push_cast; exact h3
      exact WithBot.coe_lt_coe.mp this
    have hd2 : d = 2 := by
      refine le_antisymm ?_ h1'
      by_contra h
      have : (3 : ℕ∞) ≤ d := Order.add_one_le_of_lt (not_le.mp h)
      exact absurd (lt_of_lt_of_le h3' this) (lt_irrefl _)
    rw [hd2]
    rfl
  -- (2) the pairs `(X_i, B_i)` and `(X_i, B_i + A_i)` are log canonical
  have hlcB' : ∀ i : ℕ, (i : ℕ∞) ≤ P.n →
      MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY i) (transformSeq P B i) := by
    intro i
    induction i with
    | zero => exact fun _ => ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKB.1.2.1 B).mpr hKB).1
    | succ i ih =>
      intro hi
      have hi' : (i : ℕ∞) < P.n := lt_of_succ_le hi
      obtain ⟨_, _, _, _, N, hNc, hN, -, hNL, -⟩ := hstep i hi'
      exact isLogCanonicalPair_succ P i hi' (hdims i hi'.le) B hB hm (hL i hi'.le).2.1 N hNc hN
        hNL (ih hi'.le)
  have hlcB := hlcB' n hn
  obtain ⟨MC, hMC, n', hn', hcomp⟩ := exists_complementInv sX sZ hZ f hconn hDG M hGM P
  have hlcBA' : ∀ i : ℕ, (i : ℕ∞) ≤ P.n →
      MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY i) (transformSeq P (B + A) i) := by
    intro i
    induction i with
    | zero => exact fun _ => isLogCanonicalPair_of_isLcPair hlc (add_nonneg hB hA)
    | succ i ih =>
      intro hi
      have hi' : (i : ℕ∞) < P.n := lt_of_succ_le hi
      obtain ⟨L', hL'⟩ := hcomp i hi'.le
      obtain ⟨_, _, _, _, N, hNc, hN, hNL⟩ :=
        exists_pullback_linearlyEquivalent_of_complementInv P (B + A) MC n' i hi' hL'
      exact isLogCanonicalPair_succ P i hi' (hdims i hi'.le) (B + A) (add_nonneg hB hA) hn'
        hL'.2.1 N hNc hN hNL (ih hi'.le)
  have hlcBA := hlcBA' n hn
  -- (3) a crepant dlt modification `e : V ⟶ X_n` of `(X_n, B_n)`
  obtain ⟨V, _, _, _, e, he, hVq, BV, heproj, hVdlt, hcrep, hexc⟩ :=
    projectiveFloorProgramInputs_three.exists_crepant_dltModification (modelStr sX P.sY n)
      (hPproj.2 n hn) (hdims n hn) hlcB
  -- (4) the floor surface `S ⊆ V`, the strict transform of `E_n`, and its adjunction
  have hXnn : IsNormalVariety ℂ (modelStr sX P.sY n) := hmod.isQFactorial.1
  haveI : IsProper e := isProper_of_isProjectiveMorphism e heproj
  obtain ⟨S₀, hS₀, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXnn (f := e)
      hVq.1 he En
  have hK3 : Divisor.IsCanonicalDivisor (modelStr sX P.sY n) 3 (divisorSeq K P.KY n) :=
    (hL n hn).2.2.2.2.1.2.1
  have hBE : (transformSeq P B n).coeff En = 1 := by
    rw [show (transformSeq P B n).coeff En = B E from hEn B]
    exact le_antisymm (hKB.2.1 E).2 hE1
  have hS₀coef : 1 ≤ BV.coeff S₀ := by
    have hcb := hcrep (divisorSeq K P.KY n) hK3
    rw [MMP.Flips.coeff_eq_of_not_subset_of_isCrepantBoundary hcb S₀ (fun h =>
      MMP.Flips.map_genericPoint_ne_of_subset_exceptionalLocus hXnn hVq.1.1 he h En hS₀)]
    change (1 : ℚ) ≤ (MMP.Flips.birationalInverseTransform e he (transformSeq P B n)) S₀
    rw [MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hXnn e hVq.1.1 he _ hS₀]
    exact hBE.ge
  obtain ⟨TS, j, BS, hadj, hjrange⟩ := exists_isAdjunctionStep_of_one_le_coeff hVdlt S₀ hS₀coef
  -- (5) the complement, the surface theorem on `S`, and descent to `T`
  obtain ⟨L', hL'c, hL'u, ⟨eL'⟩⟩ := hcomp n hn
  obtain ⟨hLnc, hLnu, ⟨_, hnefn⟩, -, -⟩ := hL n hn
  rw [transformSeq_add] at hL'u hlcBA
  haveI : IsProper P.g := hc.isNegativeExtremalContraction.isContraction.isProper
  have hAn : 0 ≤ transformSeq P A n := Finsupp.le_def.mpr fun F => by
    obtain ⟨F₀, hF₀⟩ := transformSeq_coeff P n hn F
    rw [hF₀]
    exact (Finsupp.le_def.mp hA) F₀
  exact floor_free (hPproj.2 n hn) hXnn (hdims n hn) hZ hZ2 hT hT2 hmod.comp_eq hgπ hgs hK3 hAn
    hlcB hlcBA hnefn hm hLnc hLnu hM'c hM' hM'L MC hn' hL'c hL'u eL' En hEnZ e he hVq heproj hVdlt
    (hcrep _ hK3) S₀ hS₀ j hadj hjrange

/-- **The end of the program is semiample over the base.** The program for `K + B - t⌊B⌋` over
`Z` ends with a Mori fibre space `r : X_n ⟶ V` over `Z` with `V ⟶ Z` birational; the strict
transform of a horizontal component of `⌊B⌋` on a crepant dlt modification of `X_n` is a
complemented lc surface over `Z`, whose adjoint is semiample over `Z`, and this descends to `V`
and pulls back to `X_n`. -/
private theorem endpoint_free
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (hZ2 : topologicalKrullDim Z = 2) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hconn : ∀ z : Z, _root_.IsConnected (f ⁻¹' {z}))
    (hO : ∀ U : Z.Opens, IsIso (f.app U))
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A)) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    (hE : ∃ E : Mori.PrimeDivisor X, 1 ≤ B.coeff E ∧ Dense (f '' (E.support : Set X)))
    {m : ℕ} (hm : 0 < m) {L₀ : Divisor X} (hL₀ : Divisor.toQDivisor L₀ =
      (m : ℤ) • (Divisor.toQDivisor K + B)) (hL₀c : L₀.IsCartier)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1 / (2 * (6 * m + 1)))
    (P : RelativeDltProgram sX sZ f K (B - t • Divisor.toQDivisor B.roundDown))
    (hPproj : P.IsProjective) (hPn : P.n ≠ ⊤)
    (hPend : MMP.Flips.IsRelativelyNef ℂ (modelStr sX P.sY P.n.toNat) (modelMap f P.πY P.n.toNat)
          (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
            divisorSeq (B - t • Divisor.toQDivisor B.roundDown) P.BY P.n.toNat)) ∨
        P.hasFinal)
    (L : ∀ i, Divisor (modelSeq X P.Y i)) (hL0 : L 0 = L₀)
    (hL : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → NullInv P B m i (L i))
    (hstep : ∀ i : ℕ, (i : ℕ∞) < P.n → ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i))
        (_ : IsNormal (P.Z i)) (_ : CompactSpace (P.Z i)) (N : Divisor (P.Z i)) (hNc : N.IsCartier),
        ∃ (hN : ∀ T : irreducibleComponents (modelSeq X P.Y i),
            P.f i (componentGenericPoint _ T) ∉ N.supp)
          (hN' : ∀ T : irreducibleComponents (P.Y i), P.fp i (componentGenericPoint _ T) ∉ N.supp),
          (N.pullback hNc hN).LinearlyEquivalent (L i) ∧
            (N.pullback hNc hN').LinearlyEquivalent (L (i + 1))) :
    ∃ k : ℕ, 0 < k ∧
      IsRelativelyFreeDivisor (modelMap f P.πY P.n.toNat) ((k : ℤ) • L P.n.toNat) := by
  classical
  have hn : (P.n.toNat : ℕ∞) ≤ P.n := ENat.coe_toNat_le_self _
  -- the program ends with a fibre-type contraction `g : X_n ⟶ T` over `Z`
  have hfin : P.hasFinal := endpoint_hasFinal sX sZ hXp hX hX3 hB hKB hZ hZ2 f hf hfp hconn hO
    hnef hA hAq hlc hDG M hGM hE hm hL₀ hL₀c ht0 ht1 P hPproj hPn hPend L hL0 hL hstep
  obtain ⟨-, hc, -⟩ := P.final_spec hfin
  have hT := hc.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral P.T := hT.1.toIsIntegral
  haveI : LocallyOfFiniteType P.sT := hT.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian P.T := LocallyOfFiniteType.isLocallyNoetherian P.sT
  haveI : IsNormal P.T := hT.2
  haveI : QuasiCompact P.sT := hT.1.toQuasiCompact
  haveI : CompactSpace P.T := QuasiCompact.compactSpace_of_compactSpace P.sT
  haveI : IsDominant P.g := by
    haveI : IsProper P.g := hc.isNegativeExtremalContraction.isContraction.isProper
    have : IsSchemeTheoreticallyDominant P.g := ⟨by
      ext U : 2
      rw [Scheme.Hom.ker_apply]
      simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      haveI := hc.isNegativeExtremalContraction.isContraction.isIso_app U
      exact (RingHom.injective_iff_ker_eq_bot _).mp
        (ConcreteCategory.bijective_of_isIso (P.g.app U)).1⟩
    exact (isSchemeTheoreticallyDominant_iff_isDominant P.g).mp this
  -- the final ray is `(K + B)`-trivial, so `L_n ∼ g^* M'`
  have hLn := hL P.n.toNat hn
  obtain ⟨hneg, hdeg⟩ := ray_null_of sX sZ hXp hX hX3 hB hKB hZ f hf hm ht0 ht1 P hPproj _ hn _
    hLn P.finalRay hc.isNegativeRelativeExtremalRayOf
  obtain ⟨M', hM'c, hM', hM'L⟩ := cartier_descent_of sX sZ f P hPproj _ hn _ hLn P.finalRay
    P.g P.gT hc hneg hdeg
  -- a multiple of `M'` is relatively free over `Z`, and so is its pull-back
  obtain ⟨k, hk, hkfree⟩ := final_free sX sZ hXp hX hX3 hB hKB hZ hZ2 f hf hfp hconn hO
    hnef hA hAq hlc hDG M hGM hE hm hL₀ hL₀c ht0 ht1 P hPproj hPn hPend L hL0 hL hstep hfin M'
    hM'c hM' hM'L
  refine ⟨k, hk, ?_⟩
  have hpb := (Divisor.isPullback_pullback hM'c hM').zsmul hM'c (k : ℤ)
    (map_componentGenericPoint_notMem_supp_of_isDominant P.g _)
  have hfr := IsRelativelyFreeDivisor.of_isPullback P.g P.gT (hM'c.zsmul _) hpb hkfree
  rw [hc.isRelativeContractionOfFace.comp_eq] at hfr
  exact IsRelativelyFreeDivisor.of_linearlyEquivalent _ (linearlyEquivalent_zsmul hM'L k) hfr

private theorem solution
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (hZ2 : topologicalKrullDim Z = 2) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hconn : ∀ z : Z, _root_.IsConnected (f ⁻¹' {z}))
    (hO : ∀ U : Z.Opens, IsIso (f.app U))
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A)) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    (hE : ∃ E : Mori.PrimeDivisor X, 1 ≤ B.coeff E ∧ Dense (f '' (E.support : Set X))) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  obtain ⟨m, hm, L₀, hL₀, hL₀c⟩ := hKB.1.2.2.exists_pos
  set t : ℚ := 1 / (4 * (6 * m + 1)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 / (2 * (6 * m + 1)) := by
    have : (0 : ℚ) ≤ m := by positivity
    rw [ht]; apply one_div_lt_one_div_of_lt (by positivity); linarith
  obtain ⟨P, hPproj, hPn, hPend⟩ := exists_program sX sZ hXp hX hX3 hKB hZ f hf ht0.le
    (lt_one_of_lt_floorBound ht1).le
  obtain ⟨L, hL0, hL, hstep⟩ := program_null sX sZ hXp hX hX3 hB hKB hZ f hf hnef hm hL₀ hL₀c
    ht0 ht1 P hPproj hPn
  have hfree := endpoint_free sX sZ hXp hX hX3 hB hKB hZ hZ2 f hf hfp hconn hO hnef hA hAq hlc
    hDG M hGM hE hm hL₀ hL₀c ht0 ht1 P hPproj hPn hPend L hL0 hL hstep
  obtain ⟨k, hk, hkfree⟩ := descend_program P hPproj hPn L (fun i hi => (hL i hi).1) hstep hfree
  refine ⟨k * m, Nat.mul_pos hk hm, (k : ℤ) • L₀, ?_, hL₀c.zsmul _, by rwa [← hL0]⟩
  rw [map_zsmul, hL₀, smul_smul]
  push_cast
  rfl

end Proof_thm_fourfold_complemented_threefold_horizontal_floor_good

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Complemented dlt threefolds with a horizontal floor over a surface are good.** Let `(X, B)`
be an effective `ℚ`-factorial projective complex dlt threefold pair with canonical divisor `K`,
and let `f : X ⟶ Z` be a projective morphism with connected fibres and `f_* 𝒪_X = 𝒪_Z` onto a
normal projective surface `Z`, such that `K + B` is `f`-nef. Suppose `A ≥ 0` is a `ℚ`-Cartier
divisor with `(X, B + A)` lc and `K + B + A ∼_ℚ G`, where `𝒪_X(mG) ≅ f^* M` for some `m > 0` and
an invertible `𝒪_Z`-module `M`. If some prime divisor `E` with `1 ≤ B_E` dominates `Z`, then
`K + B` is `f`-semiample: some positive multiple `m' (K + B)` is a Cartier divisor `L` with
`f^* f_* 𝒪_X(L) → 𝒪_X(L)` surjective. -/
@[mmp "thm_fourfold_complemented_threefold_horizontal_floor_good"]
public theorem exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent_of_dense
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hX : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (hZ2 : topologicalKrullDim Z = 2) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hconn : ∀ z : Z, _root_.IsConnected (f ⁻¹' {z}))
    (hO : ∀ U : Z.Opens, IsIso (f.app U))
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A)) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    (hE : ∃ E : Mori.PrimeDivisor X, 1 ≤ B.coeff E ∧ Dense (f '' (E.support : Set X))) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L :=
          by revert X Z sX sZ hXp hX hX3 K B hB hKB hZ hZ2 f hf hfp hconn hO hnef A hA hAq hlc G hDG M hGM hE; first | exact Proof_thm_fourfold_complemented_threefold_horizontal_floor_good.solution | exact Proof_thm_fourfold_complemented_threefold_horizontal_floor_good.solution _ | exact Proof_thm_fourfold_complemented_threefold_horizontal_floor_good.solution _ _ | exact Proof_thm_fourfold_complemented_threefold_horizontal_floor_good.solution _ _ _ | exact Proof_thm_fourfold_complemented_threefold_horizontal_floor_good.solution _ _ _ _

