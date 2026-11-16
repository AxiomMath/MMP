module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgClosed.RayContraction
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization

/-!
# Fibre-type contractions of negative extremal rays are Mori fibre spaces

Let `k` be an algebraically closed field of characteristic zero and `(X, B)` a projective lc
fourfold pair over `k` with rational boundary, `D = K_X + B`. If `R` is a `D`-negative extremal
ray of `NE̅(X)` and `f : X ⟶ Z` is a contraction of `R` of fibre type (`dim Z < dim X`), then
`f` is a Mori fibre space structure on `(X, B)`: `Z` is a normal projective variety,
`ρ(X/Z) = 1` and `-D` is `f`-ample.

## Main results

* `MMP.Fourfold.IsContractionOfRay.isMoriFibreSpace_of_isFibreType`.
-/

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace Proof_lem_oai4_finite_existence_transfer_c

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

section Iso

variable {k : Type u} [Field k] {X Z Z' : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- The relative Picard number does not see an isomorphism of the target. -/
private theorem relativePicardNumberN1_comp_iso (f : X ⟶ Z) (e : Z ≅ Z') :
    relativePicardNumberN1 sX (f ≫ e.hom) = relativePicardNumberN1 sX f := by
  have key : pullbackNumericalClasses sX (f ≫ e.hom) = pullbackNumericalClasses sX f := by
    unfold pullbackNumericalClasses
    congr 1
    ext d
    constructor
    · rintro ⟨E, M, hM, ⟨σ⟩, rfl⟩
      haveI := MMP.Mori.isInvertible_pullback_obj e.hom M
      exact ⟨E, (Scheme.Modules.pullback e.hom).obj M, inferInstance,
        ⟨σ ≪≫ ((Scheme.Modules.pullbackComp f e.hom).app M).symm⟩, rfl⟩
    · rintro ⟨E, M, hM, ⟨σ⟩, rfl⟩
      haveI := MMP.Mori.isInvertible_pullback_obj e.inv M
      refine ⟨E, (Scheme.Modules.pullback e.inv).obj M, inferInstance, ⟨σ ≪≫ ?_⟩, rfl⟩
      exact (Scheme.Modules.pullback f).mapIso (((Scheme.Modules.pullbackId Z).app M).symm ≪≫
        (Scheme.Modules.pullbackCongr e.hom_inv_id.symm).app M ≪≫
        ((Scheme.Modules.pullbackComp e.hom e.inv).app M).symm) ≪≫
        (Scheme.Modules.pullbackComp f e.hom).app _
  unfold relativePicardNumberN1
  rw [key]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
/-- Relative ampleness of an invertible sheaf does not see an isomorphism of the target. -/
private theorem isRelativelyAmple_comp_iso (f : X ⟶ Z) (e : Z ≅ Z') (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    MMP.Mori.IsRelativelyAmple (f ≫ e.hom) L ↔ MMP.Mori.IsRelativelyAmple f L := by
  constructor
  · intro h y
    obtain ⟨V, hV, hyV, hA⟩ := h (e.hom y)
    exact ⟨e.hom ⁻¹ᵁ V, hV.preimage e.hom, hyV, hA⟩
  · intro h y
    obtain ⟨V, hV, hyV, hA⟩ := h (e.inv y)
    refine ⟨e.inv ⁻¹ᵁ V, hV.preimage e.inv, hyV, ?_⟩
    have hW : f ⁻¹ᵁ V = (f ≫ e.hom) ⁻¹ᵁ e.inv ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, Category.assoc, e.hom_inv_id, Category.comp_id]
    have key : ∀ U U' : X.Opens, U = U' →
        Stacks.Ample.IsAmple U.toScheme
          ((RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom).obj L) →
        Stacks.Ample.IsAmple U'.toScheme
          ((RingedSpaceModuleAdjunction.modulePullback U'.ι.toLRSHom.toShHom).obj L) := by
      rintro U _ rfl hU
      exact hU
    exact key _ _ hW hA

/-- Relative ampleness does not see an isomorphism of the target. -/
private theorem hasRelativelyAmpleMultiple_comp_iso (D : QDivisor X) (f : X ⟶ Z) (e : Z ≅ Z') :
    D.HasRelativelyAmpleMultiple (f ≫ e.hom) ↔ D.HasRelativelyAmpleMultiple f := by
  unfold QDivisor.HasRelativelyAmpleMultiple
  refine exists_congr fun m => and_congr_right fun _ => exists_congr fun L =>
    exists_congr fun hL => and_congr_right fun _ => ?_
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact isRelativelyAmple_comp_iso f e _

end Iso

/-- Two morphisms into an affine scheme agree once they agree after a morphism which is an
isomorphism on global sections. -/
private lemma eq_of_comp_eq_of_isIso_appTop {X Y W : Scheme.{u}} [IsAffine W] (g : X ⟶ Y)
    [IsIso g.appTop] {a b : Y ⟶ W} (hab : g ≫ a = g ≫ b) : a = b := by
  refine ext_of_isAffine ?_
  have := congrArg Scheme.Hom.appTop hab
  simp only [Scheme.Hom.comp_appTop] at this
  exact (cancel_mono _).1 this

private theorem solution : ∀ {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hdim : topologicalKrullDim X = 4)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sZ R f) (hft : hf.toIsContraction.IsFibreType),
    IsMoriFibreSpace sX sZ K B f := by
  intro k _ _ _ X Z _ _ _ _ sX sZ K B R f hX hdim hlc hK hR hf hft
  obtain ⟨Z', sZ', f', hc', hZ', hρ', ha'⟩ :=
    exists_isContractionOfRay_of_isNegativeExtremalRayOf_of_isAlgClosed hX hlc hK hdim hR
  have hRf (C : ProperCurve sX) (hC : OneCycle.numericalClass sX (C.cycle ℝ) ∈ R) :
      C.IsContractedBy f := (hf.isContractedBy_iff C).mpr hC
  have hRf' (C : ProperCurve sX) (hC : OneCycle.numericalClass sX (C.cycle ℝ) ∈ R) :
      C.IsContractedBy f' := (hc'.isContractedBy_iff C).mpr hC
  obtain ⟨u, hu, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hR.2.1 hRf hc'
  obtain ⟨v, hv, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hc'.isProjectiveMorphism
    hc'.comp_eq hR.2.1 hRf' hf
  have hu₃ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hR.2.1 hRf hf
  have hu₄ := existsUnique_comp_eq_of_isContractionOfRay hX hc'.isProjectiveMorphism
    hc'.comp_eq hR.2.1 hRf' hc'
  let eZ : Z' ≅ Z :=
    { hom := u
      inv := v
      hom_inv_id := hu₄.unique (by rw [← Category.assoc, hu, hv]) (Category.comp_id _)
      inv_hom_id := hu₃.unique (by rw [← Category.assoc, hv, hu]) (Category.comp_id _) }
  have hfe : f' ≫ eZ.hom = f := hu
  haveI : IsIso f'.appTop := hc'.isIso_app ⊤
  have hsZ : eZ.hom ≫ sZ = sZ' :=
    eq_of_comp_eq_of_isIso_appTop f' (by rw [hc'.comp_eq, ← Category.assoc, hfe, hf.comp_eq])
  have hZproj : IsProjectiveMorphism sZ :=
    IsProjectiveMorphism.of_iso eZ (Iso.refl _) (by rw [hsZ]; exact (Category.comp_id _).symm)
      hZ'.isProjective
  refine
    { isProjectiveVariety := hX
      isLogCanonicalPair := hlc
      isCanonicalDivisor := hK
      isContraction := hf.toIsContraction
      isProjectiveVariety_target := ?_
      relativePicardNumber_eq_one := ?_
      dim_lt := hft
      hasRelativelyAmpleMultiple := ?_ }
  · exact (MMP.Mori.isProjectiveVariety_iff k sZ).2 ⟨hf.isNormalVariety_target.1, hZproj⟩
  · rw [← hfe, relativePicardNumberN1_comp_iso, hρ']
  · rw [← hfe]
    exact (hasRelativelyAmpleMultiple_comp_iso _ f' eZ).mpr ha'

end Proof_lem_oai4_finite_existence_transfer_c

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Fibre-type contractions are Mori fibre spaces.** Let `k` be algebraically closed of
characteristic zero, `(X, B)` a projective lc fourfold pair over `k` with canonical divisor `K`,
`R` a `(K + B)`-negative extremal ray of `NE̅(X)` and `f : X ⟶ Z` a contraction of `R` of fibre
type. Then `f` is a Mori fibre space structure on `(X, B)`. -/
@[mmp "lem_oai4_finite_existence_transfer_c"]
public theorem IsContractionOfRay.isMoriFibreSpace_of_isFibreType {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hdim : topologicalKrullDim X = 4)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sZ R f) (hft : hf.toIsContraction.IsFibreType) :
    IsMoriFibreSpace sX sZ K B f :=
      by revert k X Z sX sZ K B R f hX hdim hlc hK hR hf hft; first | exact Proof_lem_oai4_finite_existence_transfer_c.solution | exact Proof_lem_oai4_finite_existence_transfer_c.solution _ | exact Proof_lem_oai4_finite_existence_transfer_c.solution _ _ | exact Proof_lem_oai4_finite_existence_transfer_c.solution _ _ _ | exact Proof_lem_oai4_finite_existence_transfer_c.solution _ _ _ _

end MMP.Fourfold

