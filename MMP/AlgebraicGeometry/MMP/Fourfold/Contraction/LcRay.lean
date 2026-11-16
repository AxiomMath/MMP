module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Contraction.LcRelativeRay

/-!
# Contractions of negative extremal rays of projective lc fourfolds

Let `(X, B)` be a log canonical pair with rational boundary on a normal projective complex
fourfold `X`, with canonical divisor `K`, and put `D = K + B`. Every `D`-negative extremal ray `R`
of the closed cone of curves `NE̅(X)` has a contraction: a projective surjective morphism
`f : X ⟶ Z` onto a normal projective variety with `f_* 𝒪_X = 𝒪_Z`, contracting exactly the
integral curves whose classes lie in `R`, with relative Picard number `ρ(X/Z) = 1` and `-D`
`f`-ample. This is the contraction theorem for lc pairs; `ℚ`-factoriality is not needed.

## Main results

* `MMP.Fourfold.exists_isContractionOfRay_of_isNegativeExtremalRayOf`: the contraction of a
  `(K + B)`-negative extremal ray of a projective lc complex fourfold exists.

## Implementation notes

The conclusion lists the same conditions on `f` as the fields `isContractionOfRay`,
`isProjectiveVariety_target`, `relativePicardNumber_eq_one` and `hasRelativelyAmpleMultiple` of
`MMP.Fourfold.IsPermittedStep`, so the contraction found here is the `f` of a permitted step.
Normality of `Z` and `f_* 𝒪_X = 𝒪_Z` are fields of `MMP.Fourfold.IsContraction`.

## References

* [OAI4] the fourfold source, *The contraction exists*.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_prop_oai4_continuation_b

/-- The one-point base `Spec k` is a normal variety over `k`. -/
private theorem isNormalVariety_id_spec (k : Type) [Field k] :
    MMP.Mori.IsNormalVariety k (𝟙 (Spec (.of k))) :=
  ⟨{ toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance },
    isNormal_spec_of_isIntegrallyClosed k⟩

/-- The one-point base `Spec k` is a projective variety over `k`. -/
private theorem isProjectiveVariety_id_spec (k : Type) [Field k] :
    MMP.Mori.IsProjectiveVariety k (𝟙 (Spec (.of k))) :=
  (MMP.Mori.isProjectiveVariety_iff k _).mpr
    ⟨(isNormalVariety_id_spec k).1, isProjectiveMorphism_id _⟩

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Every proper curve of a `k`-scheme is contracted by its structure morphism. -/
private theorem isContractedBy_self (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

private theorem relativeOneCycles_self_eq_top : relativeOneCycles sX sX = ⊤ :=
  eq_top_iff.mpr fun Z _ => (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_self sX C

/-- Over the one-point base, `N₁(X/Spec k) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz => ?_, fun w => ?_⟩
  · obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hz)
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX w
    exact ⟨relativeNumericalClass sX sX ⟨Z, relativeOneCycles_self_eq_top sX ▸ trivial⟩, rfl⟩

/-- The natural map `N₁(X/Spec k) → N₁(X)` as a linear equivalence. -/
private noncomputable def relEquiv :
    RelativeNumericalCurveClasses sX sX ≃ₗ[ℝ] NumericalCurveClasses sX :=
  LinearEquiv.ofBijective _ (relativeToAbsolute_bijective sX)

private theorem degree_relEquiv (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX sX) :
    NumericalCurveClasses.degree sX L (relEquiv sX z) =
      RelativeNumericalCurveClasses.degree sX sX L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
  rfl

/-- The relative topology on `N₁(X/Spec k)` is induced from the numerical topology on `N₁(X)`. -/
private theorem isInducing_relEquiv : Topology.IsInducing (relEquiv sX) := by
  refine ⟨?_⟩
  simp only [RelativeNumericalCurveClasses.instTopologicalSpace,
    NumericalCurveClasses.instTopologicalSpace, induced_iInf, induced_compose]
  refine iInf_congr fun L => iInf_congr fun h => ?_
  congr 1
  exact funext fun z => (degree_relEquiv sX L z).symm

/-- The natural map carries `NE(X/Spec k)` onto `NE(X)`. -/
private theorem image_relativeConeOfCurves :
    relEquiv sX '' (relativeConeOfCurves sX sX : Set _) = coneOfCurves sX := by
  have h := congrArg SetLike.coe <| Submodule.map_span
    ((relEquiv sX).toLinearMap.restrictScalars NNReal)
    (Set.range fun C : {C : ProperCurve sX // C.IsContractedBy sX} => C.1.relativeClass sX C.2)
  rw [← Set.range_comp] at h
  refine h.trans ?_
  rw [← (Equiv.subtypeUnivEquiv (isContractedBy_self sX)).symm.surjective.range_comp]
  rfl

/-- `NE̅(X/Spec k)` is the preimage of `NE̅(X)` under the natural map. -/
private theorem relativeClosedConeOfCurves_eq_preimage :
    (relativeClosedConeOfCurves sX sX : Set (RelativeNumericalCurveClasses sX sX)) =
      relEquiv sX ⁻¹' (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) := by
  rw [coe_closedConeOfCurves, coe_relativeClosedConeOfCurves,
    (isInducing_relEquiv sX).closure_eq_preimage_closure_image, image_relativeConeOfCurves]

/-- The preimage of an extremal ray under a linear equivalence is an extremal ray of the
preimage cone. -/
private theorem isExtremalRay_preimage {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (e : V ≃ₗ[ℝ] W) {N R : Set W} (h : IsExtremalRay ℝ N R) :
    IsExtremalRay ℝ (e ⁻¹' N) (e ⁻¹' R) := by
  obtain ⟨⟨hRN, ⟨h0, hs⟩, hadd, hext⟩, v, hv, rfl⟩ := h
  refine ⟨⟨fun u hu => hRN hu, ⟨by simpa using h0, fun u hu c hc => ?_⟩,
    fun u hu w hw => ?_, fun u hu w hw huw => ?_⟩, e.symm v, by simpa using hv, ?_⟩
  · simpa using hs _ hu c hc
  · simpa using hadd _ hu _ hw
  · exact hext _ hu _ hw (by simpa using huw)
  · ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    refine exists_congr fun c => and_congr_right fun _ => ?_
    rw [← map_smul, LinearEquiv.symm_apply_eq]

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

private theorem relativeCurveForm_eq (D : QDivisor X) (h : D.IsQCartier)
    (z : RelativeNumericalCurveClasses sX sX) :
    QDivisor.relativeCurveForm sX sX D h z = QDivisor.curveForm sX D h (relEquiv sX z) := by
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, degree_relEquiv]

/-- A `D`-negative extremal ray of `NE̅(X)` is, through the natural map, a `D`-negative extremal
ray of `NE̅(X/Spec k)`. -/
private theorem isNegativeRelativeExtremalRayOf_preimage {D : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} (hR : IsNegativeExtremalRayOf sX D R) :
    IsNegativeRelativeExtremalRayOf sX sX D (relEquiv sX ⁻¹' R) := by
  obtain ⟨hD, hray, hneg⟩ := hR
  refine ⟨hD, ?_, fun u hu hu0 => ?_⟩
  · rw [relativeClosedConeOfCurves_eq_preimage]
    exact isExtremalRay_preimage (relEquiv sX) hray
  · rw [relativeCurveForm_eq]
    exact hneg _ hu ((LinearEquiv.map_ne_zero_iff _).mpr hu0)

private theorem solution {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z),
      IsContractionOfRay sX sZ R f ∧ MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        relativePicardNumberN1 sX f = 1 ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f := by
  obtain ⟨Z, sZ, c, g, hc, hface, -, hZ, hρ, hamp⟩ :=
    exists_isRelativeContractionOfFace_of_isNegativeRelativeExtremalRayOf hX
      (isProjectiveVariety_id_spec ℂ) (isNormalVariety_id_spec ℂ) sX (Category.comp_id sX) hdim hK hB
      (isNegativeRelativeExtremalRayOf_preimage sX hR)
  refine ⟨Z, sZ, c, ⟨hc, fun C => ?_⟩, hZ, hρ, hamp⟩
  rw [hface.isContractedBy_iff C (isContractedBy_self sX C)]
  rfl

end Proof_prop_oai4_continuation_b

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **The contraction exists.** Let `X` be a normal projective complex fourfold with canonical
divisor `K`, `(X, B)` a log canonical pair with `B` a `ℚ`-divisor, and `R` a `(K + B)`-negative
extremal ray of `NE̅(X)`. Then there is a contraction `f : X ⟶ Z` of `R` onto a normal projective
variety `Z` (so `f_* 𝒪_X = 𝒪_Z`), with `ρ(X/Z) = 1` and `-(K + B)` `f`-ample. -/
@[mmp "prop_oai4_continuation_b"]
public theorem exists_isContractionOfRay_of_isNegativeExtremalRayOf
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z),
      IsContractionOfRay sX sZ R f ∧ MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        relativePicardNumberN1 sX f = 1 ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f :=
          by revert X sX hX hdim K hK B hB R hR; first | exact Proof_prop_oai4_continuation_b.solution | exact Proof_prop_oai4_continuation_b.solution _ | exact Proof_prop_oai4_continuation_b.solution _ _ | exact Proof_prop_oai4_continuation_b.solution _ _ _ | exact Proof_prop_oai4_continuation_b.solution _ _ _ _

end MMP.Fourfold
