module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# The quotient uniformity on the image of a finite free module

Let `A` be a complete, first countable topological ring and `f : Aʳ → M` an `A`-linear map whose
kernel is closed. Then the image `f(Aʳ) ≅ Aʳ / ker f` carries the quotient uniformity: it is a
complete, Hausdorff, first countable uniform group, a topological `A`-module, and `f` is an open
quotient map onto it. Consequently every `A`-linear map `Aᵐ → f(Aʳ)` is continuous
(`LinearMap.continuous_on_pi`): the topology does not depend on the presentation.

This is how the sections of a coherent analytic sheaf over a polydisc receive their Fréchet
topology from a presentation by holomorphic functions.

## Main results

* `MMP.Topology.exists_uniformSpace_range_of_isClosed_ker`: the quotient uniformity on
  `LinearMap.range f`.

## References

* [Grauert–Remmert, *Theory of Stein spaces*, Chapter V, §6]
-/

@[expose] public section

namespace MMP.Topology

/-- **The quotient uniformity on an image.** For an `A`-linear map `f : Aʳ → M` with closed kernel
over a complete first countable topological ring `A`, the image of `f` carries a complete,
Hausdorff, first countable group uniformity for which it is a topological `A`-module and the
corestriction of `f` is an open quotient map: the quotient uniformity of `Aʳ / ker f`. -/
theorem exists_uniformSpace_range_of_isClosed_ker {A M : Type*} [Ring A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [FirstCountableTopology A]
    [AddCommGroup M] [Module A M] {r : ℕ} (f : (Fin r → A) →ₗ[A] M)
    (hf : IsClosed (LinearMap.ker f : Set (Fin r → A))) :
    ∃ U : UniformSpace (LinearMap.range f), @IsUniformAddGroup _ U _ ∧ @CompleteSpace _ U ∧
      @T2Space _ U.toTopologicalSpace ∧ @FirstCountableTopology _ U.toTopologicalSpace ∧
      @ContinuousSMul A _ _ _ U.toTopologicalSpace ∧
      @IsOpenQuotientMap _ _ _ U.toTopologicalSpace f.rangeRestrict := by
  let N := LinearMap.ker f
  let Q := (Fin r → A) ⧸ N
  let uQ : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Q := QuotientAddGroup.completeSpace_right (Fin r → A) N.toAddSubgroup
  have : IsClosed (N.toAddSubgroup : Set (Fin r → A)) := hf
  have : T2Space Q := inferInstanceAs (T2Space ((Fin r → A) ⧸ N.toAddSubgroup))
  have : FirstCountableTopology Q :=
    inferInstanceAs (FirstCountableTopology ((Fin r → A) ⧸ N.toAddSubgroup))
  let e : Q ≃ₗ[A] LinearMap.range f := f.quotKerEquivRange
  let U : UniformSpace (LinearMap.range f) := UniformSpace.comap e.symm uQ
  have hu : IsUniformInducing e.symm := ⟨rfl⟩
  have hemb : IsUniformEmbedding e.symm.toEquiv := ⟨hu, e.symm.injective⟩
  let hhomeo : (LinearMap.range f) ≃ₜ Q :=
    { toEquiv := e.symm.toEquiv
      continuous_toFun := hu.uniformContinuous.continuous
      continuous_invFun := by
        rw [hu.isInducing.continuous_iff]
        change Continuous (fun x => e.symm (e x))
        simp only [LinearEquiv.symm_apply_apply]
        exact continuous_id }
  have hfac : (f.rangeRestrict : (Fin r → A) → LinearMap.range f) =
      hhomeo.symm ∘ (QuotientAddGroup.mk : (Fin r → A) → (Fin r → A) ⧸ N.toAddSubgroup) :=
    funext fun x => (hhomeo.symm_apply_eq.2 (f.quotKerEquivRange_symm_apply_image x _).symm).symm
  refine ⟨U, IsUniformAddGroup.comap e.symm.toAddMonoidHom, (completeSpace_congr hemb).2 ‹_›,
    hhomeo.isEmbedding.t2Space, hhomeo.isInducing.firstCountableTopology,
    ContinuousSMul.induced e.symm.toLinearMap, ?_⟩
  rw [hfac]
  exact hhomeo.symm.isOpenQuotientMap.comp QuotientAddGroup.isOpenQuotientMap_mk

end MMP.Topology
