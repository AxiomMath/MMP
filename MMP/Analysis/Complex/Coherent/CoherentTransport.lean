module

public import MMP.Analysis.Complex.Coherent.ModuleTransport
public import MMP.AlgebraicGeometry.Analytic.Analytification

/-!
# Kernels of presentations of coherent sheaves, read on an open subset of `ℂⁿ`

Let `D ⊆ ℂⁿ` be open, `T` a coherent sheaf of `𝒪_D`-modules and `W` an open subset of `D`.
A morphism `f : 𝒪_Wᵖ ⟶ T|_W` is given by `p` sections of `T` over `W`, so its kernel is of
finite type by the definition of coherence. Along the equivalence between sheaves of
`𝒪_D|_W`-modules and sheaves of `𝒪_{W'}`-modules (`W' ⊆ ℂⁿ` the image of `W`), the kernel of
the transported morphism `𝒪_{W'}ᵖ ⟶ T|_{W'}` is the transport of the kernel of `f`, hence again
of finite type, and it is a subsheaf of `𝒪_{W'}ᵖ`. When `𝒪_{W'}ᵖ` is coherent, the kernel is
therefore a coherent subsheaf of `𝒪_{W'}ᵖ`.

## Main results

* `MMP.Analytic.isFiniteType_kernel_imageFreeIso_hom_comp`: the kernel of the transport of
  `f : 𝒪_Wᵖ ⟶ T|_W` is of finite type.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace MMP.Analytic

variable {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))} (W : Opens (TopCat.of D))

/-- The kernel of a morphism `𝒪_Wᵖ ⟶ T|_W` to the restriction of a coherent `𝒪_D`-module, read on
`W' ⊆ ℂⁿ`, is of finite type: it is the transport of a kernel of finite type by the second clause
of coherence of `T`, and the equivalence `imageModuleEquivalence W` preserves kernels. -/
theorem isFiniteType_kernel_imageFreeIso_hom_comp
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T) {p : ℕ}
    (f : SheafOfModules.free (Fin p) ⟶ T.over W) :
    SheafOfModules.IsFiniteType.{0} (Limits.kernel ((imageFreeIso W (Fin p)).hom ≫
      (imageModuleEquivalence W).functor.map f)) := by
  have hK : SheafOfModules.IsFiniteType.{0} (Limits.kernel f) := by
    have h := hT.2 W p ((T.over W).freeHomEquiv f)
    simp only [Equiv.symm_apply_apply] at h
    exact h
  haveI := isFiniteType_imageModuleEquivalence_functor_obj W (Limits.kernel f)
  haveI := MMP.isFiniteType_of_iso
    (Limits.PreservesKernel.iso (imageModuleEquivalence W).functor f)
  exact MMP.isFiniteType_of_iso (Limits.kernelIsIsoComp _ _).symm

end MMP.Analytic
