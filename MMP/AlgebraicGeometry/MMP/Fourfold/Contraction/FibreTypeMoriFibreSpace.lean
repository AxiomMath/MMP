module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Contraction.LcRay
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization

/-!
# Fibre-type contractions of negative extremal rays are Mori fibre spaces

Let `(X, B)` be a log canonical pair with rational boundary on a normal projective complex
fourfold `X`, with canonical divisor `K`, and put `D = K + B`. If `R` is a `D`-negative extremal
ray of `NE̅(X)` and `f : X ⟶ Z` is a contraction of `R` of fibre type (`dim Z < dim X`), then `f`
is a Mori fibre space structure on `(X, B)`: `Z` is a normal projective variety,
`f_* 𝒪_X = 𝒪_Z`, `ρ(X/Z) = 1` and `-D` is `f`-ample. The point is that any contraction of `R`
agrees, up to a unique isomorphism of targets, with the one produced by the contraction theorem
`MMP.Fourfold.exists_isContractionOfRay_of_isNegativeExtremalRayOf`, which has these properties.

## Main results

* `MMP.Fourfold.isMoriFibreSpace_of_isContractionOfRay`: a fibre-type contraction of a
  `(K + B)`-negative extremal ray of a projective lc complex fourfold is a Mori fibre space.

## References

* [OAI4] the fourfold source, *Fibre-type contractions are Mori endpoints*.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace Proof_prop_oai4_continuation_c

/-- Two contractions of the same extremal ray of `NE̅(X)` agree up to an isomorphism of their
targets over `k`. -/
private theorem exists_isIso_comp_eq_of_isContractionOfRay {k : Type} [Field k]
    {X Z Z' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsProjectiveVariety k sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {sZ : Z ⟶ Spec (.of k)} {sZ' : Z' ⟶ Spec (.of k)} {f : X ⟶ Z} {f' : X ⟶ Z'}
    (hf : IsContractionOfRay sX sZ R f) (hf' : IsContractionOfRay sX sZ' R f') :
    ∃ φ : Z ⟶ Z', IsIso φ ∧ f ≫ φ = f' ∧ φ ≫ sZ' = sZ := by
  have factor {W W' : Scheme.{0}} {sW : W ⟶ Spec (.of k)} {sW' : W' ⟶ Spec (.of k)} {g : X ⟶ W}
      {g' : X ⟶ W'} (hg : IsContractionOfRay sX sW R g) (hg' : IsContractionOfRay sX sW' R g') :
      ∃! h : W ⟶ W', g ≫ h = g' :=
    existsUnique_comp_eq_of_isContractionOfRay hX hg'.isProjectiveMorphism hg'.comp_eq hR
      (fun C hC => (hg'.isContractedBy_iff C).mpr hC) hg
  obtain ⟨φ, hφ, -⟩ := factor hf hf'
  obtain ⟨ψ, hψ, -⟩ := factor hf' hf
  have hφi : IsIso φ :=
    ⟨ψ, (factor hf hf).unique (by rw [← Category.assoc, hφ, hψ]) (Category.comp_id f),
      (factor hf' hf').unique (by rw [← Category.assoc, hψ, hφ]) (Category.comp_id f')⟩
  have : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  have : IsIso f.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f.c fun U => hf.isIso_app U.unop
  refine ⟨φ, hφi, hφ, (MMP.existsUnique_comp_eq_of_isIso_c f sX fun _ _ _ =>
    Subsingleton.elim (α := PrimeSpectrum k) _ _).unique ?_ hf.comp_eq⟩
  rw [← Category.assoc, hφ, hf'.comp_eq]

/-- Relative ampleness of an invertible sheaf is invariant under composing the morphism with an
isomorphism of the target. -/
private theorem isRelativelyAmple_comp_isIso {X Y Y' : Scheme.{0}} {f : X ⟶ Y} (φ : Y ⟶ Y')
    [IsIso φ] {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
    (h : MMP.Mori.IsRelativelyAmple f M) : MMP.Mori.IsRelativelyAmple (f ≫ φ) M := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h ((inv φ) y)
  have hpre : (f ≫ φ) ⁻¹ᵁ ((inv φ) ⁻¹ᵁ V) = f ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have key : ∀ W : X.Opens, W = f ⁻¹ᵁ V → Stacks.Ample.IsAmple W.toScheme
      ((RingedSpaceModuleAdjunction.modulePullback W.ι.toLRSHom.toShHom).obj M) := by
    rintro W rfl
    exact hamp
  exact ⟨(inv φ) ⁻¹ᵁ V, hV.preimage (inv φ), hyV, key _ hpre⟩

/-- Having an `f`-ample multiple is invariant under composing `f` with an isomorphism of the
target. -/
private theorem hasRelativelyAmpleMultiple_comp_isIso {X Y Y' : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} {f : X ⟶ Y} (φ : Y ⟶ Y') [IsIso φ]
    (h : D.HasRelativelyAmpleMultiple f) : D.HasRelativelyAmpleMultiple (f ≫ φ) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact ⟨m, hm, L, hL, hLD, isRelativelyAmple_comp_isIso φ hamp⟩

/-- `(f ≫ φ)^* N¹(Y')_ℝ ⊆ f^* N¹(Y)_ℝ`: a pull-back along `f ≫ φ` is a pull-back along `f`. -/
private theorem pullbackNumericalClasses_comp_le {k : Type} [Field k] {X Y Y' : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y) (φ : Y ⟶ Y') :
    pullbackNumericalClasses sX (f ≫ φ) ≤ pullbackNumericalClasses sX f := by
  refine Submodule.span_mono ?_
  rintro d ⟨E, M, hM, ⟨e⟩, rfl⟩
  exact ⟨E, (Scheme.Modules.pullback φ).obj M, inferInstance,
    ⟨e ≪≫ ((Scheme.Modules.pullbackComp f φ).app M).symm⟩, rfl⟩

/-- Pulling back numerical classes is invariant under composing with an isomorphism of the
target. -/
private theorem pullbackNumericalClasses_comp_isIso {k : Type} [Field k] {X Y Y' : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y) (φ : Y ⟶ Y') [IsIso φ] :
    pullbackNumericalClasses sX (f ≫ φ) = pullbackNumericalClasses sX f :=
  (pullbackNumericalClasses_comp_le sX f φ).antisymm <| by
    simpa using pullbackNumericalClasses_comp_le sX (f ≫ φ) (inv φ)

private theorem solution : ∀
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hfib : hf.toIsContraction.IsFibreType),
    IsMoriFibreSpace sX sZ K B f := by
  intro X _ _ _ _ sX hX hdim K hK B hB R hR Z sZ f hf hfib
  obtain ⟨Z', sZ', f', hf', hZ', hρ, hamp⟩ :=
    exists_isContractionOfRay_of_isNegativeExtremalRayOf sX hX hdim hK hB hR
  obtain ⟨φ, _, rfl, rfl⟩ := exists_isIso_comp_eq_of_isContractionOfRay hX hR.choose_spec.1 hf' hf
  obtain ⟨n, i, hi, hic⟩ := hZ'.isProjective
  exact
    { isProjectiveVariety := hX
      isLogCanonicalPair := hB
      isCanonicalDivisor := ⟨4, hK⟩
      isContraction := hf.toIsContraction
      isProjectiveVariety_target := (AlgebraicGeometry.isProjectiveVariety_iff ℂ sZ).mpr
        ⟨hf.isNormalVariety_target.1, n, inv φ ≫ i, inferInstance, by
          rw [Category.assoc, hic, IsIso.inv_hom_id_assoc]⟩
      relativePicardNumber_eq_one := by
        rwa [relativePicardNumberN1, pullbackNumericalClasses_comp_isIso]
      dim_lt := hfib
      hasRelativelyAmpleMultiple := hasRelativelyAmpleMultiple_comp_isIso φ hamp }

end Proof_prop_oai4_continuation_c

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Fibre-type contractions are Mori fibre spaces.** Let `X` be a normal projective complex
fourfold with canonical divisor `K`, `(X, B)` a log canonical pair with `B` a `ℚ`-divisor, `R` a
`(K + B)`-negative extremal ray of `NE̅(X)`, and `f : X ⟶ Z` a contraction of `R` of fibre type.
Then `f` is a Mori fibre space structure on `(X, B)`. -/
@[mmp "prop_oai4_continuation_c"]
public theorem isMoriFibreSpace_of_isContractionOfRay
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hfib : hf.toIsContraction.IsFibreType) :
    IsMoriFibreSpace sX sZ K B f :=
      by revert X sX hX hdim K hK B hB R hR Z sZ f hf hfib; first | exact Proof_prop_oai4_continuation_c.solution | exact Proof_prop_oai4_continuation_c.solution _ | exact Proof_prop_oai4_continuation_c.solution _ _ | exact Proof_prop_oai4_continuation_c.solution _ _ _ | exact Proof_prop_oai4_continuation_c.solution _ _ _ _

end MMP.Fourfold
