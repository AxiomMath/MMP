module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionIdeal
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# The local coordinates of a point of a Stacks vector bundle

A morphism `u : W ⟶ 𝐕(ℰ)` over `X`, with structure morphism `h : W ⟶ X`, corresponds to a module
morphism `φ_u : ℰ ⟶ h_* 𝒪_W` (Stacks' `Scheme.Modules.vectorBundleHomEquiv`). Over an affine open
`V` of `X`, the function `u^♯ m` on `h⁻¹V` attached to a section `m ∈ Γ(ℰ, V)`, read as a
function on `π⁻¹V` (`MMP.Modules.totalSections`, `MMP.Modules.generator`), is `φ_u(m)`
(`MMP.Modules.appLE_totalSections_generator`).

## Main results

* `MMP.Modules.totalSections_eq_universalAlgebraMap`: on sections over an affine open `V`, the
  identification `Γ(V, Sym ℰ) ≅ Γ(π⁻¹V, 𝒪)` is the universal map of the relative spectrum.
* `MMP.Modules.appLE_totalSections_generator`: the pull-back along `u` of the function `m` on
  `π⁻¹V` is `φ_u(m)`.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace MMP.Modules

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent]

/-- The projection `π : 𝐕(ℰ) ⟶ X` is the structure morphism of the glued relative spectrum of
`Sym ℰ`. -/
lemma proj_eq_toBase : proj E =
    (Stacks.RelativeSpec.gluedSpectrum (Scheme.Modules.vectorBundleSituation X E)).toBase :=
  rfl

/-- Over an affine open `V` of `X`, the inclusion `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ)` is the chart of the
glued relative spectrum of `Sym ℰ` at `V`. -/
lemma specSectionsι_eq_chart (V : X.affineOpens) :
    specSectionsι E V =
      (Stacks.RelativeSpec.gluedSpectrum (Scheme.Modules.vectorBundleSituation X E)).chart V :=
  rfl

/-- **The chart sections of `𝐕(ℰ)` are the universal map of the relative spectrum**: the
identification `Γ(V, Sym ℰ) ≅ Γ(π⁻¹V, 𝒪)` of `MMP.Modules.totalSections` is the universal map
`Sym ℰ ⟶ π_* 𝒪_{𝐕(ℰ)}` on sections over `V`. -/
lemma totalSections_eq_universalAlgebraMap (V : X.affineOpens) :
    totalSections E V = (Stacks.RelativeSpec.universalAlgebraMap
      (Scheme.Modules.vectorBundleSituation X E)).right.app (op V.1) := by
  have h' : ((Stacks.RelativeSpec.gluedSpectrum
      (Scheme.Modules.vectorBundleSituation X E)).chartIsoPreimage V).hom ≫ (specIso E V).hom =
      𝟙 _ := by
    apply (cancel_mono (specSectionsι E V)).1
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (specIso_hom_specSectionsι E V)).trans
      (((Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage_hom_ι
      (Stacks.RelativeSpec.gluedSpectrum (Scheme.Modules.vectorBundleSituation X E)) V).trans
        (specSectionsι_eq_chart E V).symm).trans (Category.id_comp _).symm))
  have h : (specIso E V).hom = ((Stacks.RelativeSpec.gluedSpectrum
      (Scheme.Modules.vectorBundleSituation X E)).chartIsoPreimage V).inv :=
    (Iso.inv_ext h').symm
  refine Eq.trans ?_ (Stacks.RelativeSpec.universalAlgebraMap_app
    (Scheme.Modules.vectorBundleSituation X E) V).symm
  rw [totalSections, h]
  rfl

/-- **The functor of points of `𝐕(ℰ)` on sections**: for `u : W ⟶ 𝐕(ℰ)` over `X` with module
morphism `φ_u : ℰ ⟶ h_* 𝒪_W`, an affine open `V` of `X` and `m ∈ Γ(ℰ, V)`, the pull-back along `u`
of the function `m` on `π⁻¹V` is `φ_u(m) ∈ Γ(W, h⁻¹V)`. -/
theorem appLE_totalSections_generator {W : Over X}
    (u : W ⟶ Scheme.Modules.vectorBundleOver X (F := E)) (V : X.affineOpens) (m : Γ(E, V.1))
    (hle : W.hom ⁻¹ᵁ V.1 ≤ u.left ⁻¹ᵁ (proj E ⁻¹ᵁ V.1)) :
    u.left.appLE (proj E ⁻¹ᵁ V.1) (W.hom ⁻¹ᵁ V.1) hle (totalSections E V (generator E V.2 m)) =
      ((Scheme.Modules.vectorBundleHomEquiv E W u).val.app (op V.1)).hom m := by
  have F1 : (((Scheme.Modules.symmetricAlgebraSheafComparison E).hom.right.hom.app
      (op V.1)).hom (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X
        (Scheme.Modules.symmetricAlgebra X E) (Scheme.Modules.symmetricAlgebra_mul_comm X E) 1
        V.1 (((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V.1)) m))) =
      generator E V.2 m :=
    (Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl X _ _ 1 V.1 _).trans
      (Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl E V.2 m).symm
  have F2 : (Scheme.Modules.vectorBundlePushforwardIso X (F := E)).inv.right.hom.app (op V.1) =
      totalSections E V :=
    (totalSections_eq_universalAlgebraMap E V).symm
  have F3 : (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap u).right.hom.app (op V.1) =
      u.left.appLE (proj E ⁻¹ᵁ V.1) (W.hom ⁻¹ᵁ V.1) hle :=
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMapAux_app (proj E) u.left W.hom
      (Over.w u) V.1 hle
  have H : ((Scheme.Modules.vectorBundleHomEquiv E W u).val.app (op V.1)).hom m =
      ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap u).right.hom.app (op V.1)).hom
        (((Scheme.Modules.vectorBundlePushforwardIso X (F := E)).inv.right.hom.app
          (op V.1)).hom
          (((Scheme.Modules.symmetricAlgebraSheafComparison E).hom.right.hom.app (op V.1)).hom
            (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X (Scheme.Modules.symmetricAlgebra X E)
              (Scheme.Modules.symmetricAlgebra_mul_comm X E) 1 V.1
              (((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V.1)) m)))) :=
    (congrArg (fun φ ↦ (φ.val.app (op V.1)).hom m)
      (Scheme.Modules.vectorBundleHomEquiv_apply E W u)).trans rfl
  rw [H, F1, F2, F3]
  rfl

end MMP.Modules
