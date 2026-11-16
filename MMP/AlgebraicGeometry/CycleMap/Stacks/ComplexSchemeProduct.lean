module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Variety.SmoothVarietyConstructions

/-!
# Products of complex schemes

If `X` and `Y` are complex schemes, with closed imbeddings `X ↪ M` and `Y ↪ N` into smooth
complex varieties, then the fibre product `X ×_{Spec ℂ} Y` is a complex scheme: it is of finite
type over `ℂ`, and `X × Y ↪ M × N` is a closed imbedding into the product `M × N`, which is a
smooth variety since `ℂ` is algebraically closed (`MMP.isSmoothVariety_pullback`).

## Main results

* `MMP.Chow.isComplexScheme_pullback`: the fibre product over `Spec ℂ` of two complex schemes is
  a complex scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace MMP.Chow

/-- The fibre product `X ×_{Spec ℂ} Y` of two complex schemes, over `ℂ` through the second
projection, is a complex scheme: closed imbeddings `X ↪ M`, `Y ↪ N` over `ℂ` into smooth
varieties give the closed imbedding `X × Y ↪ M × N` over `ℂ`, and `M × N` is a smooth variety. -/
instance isComplexScheme_pullback (X Y : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] :
    IsComplexScheme (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) where
  toLocallyOfFiniteType :=
    show LocallyOfFiniteType (pullback.snd _ _ ≫ Y ↘ Spec (.of ℂ)) from inferInstance
  toQuasiCompact := show QuasiCompact (pullback.snd _ _ ≫ Y ↘ Spec (.of ℂ)) from inferInstance
  exists_isClosedImmersion := by
    obtain ⟨M, _, _, i, hi, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
    obtain ⟨N, _, _, j, hj, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := Y)
    have hMN : IsSmoothVariety ℂ
        (pullback (M ↘ Spec (.of ℂ)) (N ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ)) := by
      have h := isSmoothVariety_pullback ℂ (M ↘ Spec (.of ℂ)) (N ↘ Spec (.of ℂ))
      rw [pullback.condition] at h
      exact h
    have e₁ : X ↘ Spec (.of ℂ) = i ≫ M ↘ Spec (.of ℂ) := hi.comp_over.symm
    have e₂ : Y ↘ Spec (.of ℂ) = j ≫ N ↘ Spec (.of ℂ) := hj.comp_over.symm
    have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
      ⟨fun f g hf hg ↦ by haveI := hf; haveI := hg; exact IsClosedImmersion.comp f g⟩
    have hφ := MorphismProperty.pullbackMap (P := @IsClosedImmersion) (i₁ := i) (i₂ := j)
      inferInstance inferInstance e₁ e₂
    refine ⟨pullback (M ↘ Spec (.of ℂ)) (N ↘ Spec (.of ℂ)), inferInstance, hMN, _, ⟨?_⟩, hφ⟩
    change pullback.map _ _ _ _ i j (𝟙 _) _ _ ≫ pullback.snd _ _ ≫ N ↘ Spec (.of ℂ) =
      pullback.snd _ _ ≫ Y ↘ Spec (.of ℂ)
    rw [pullback.lift_snd_assoc, Category.assoc, ← e₂]

end MMP.Chow
