module

public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal

/-!
# Very ample multiples of an ample Cartier divisor

For an ample Cartier divisor `L` on a scheme `X` proper over a field `k`, the multiple `νL` is
very ample for every `ν ≫ 0`.

## Main results

* `MMP.Resolution.Bridges.eventually_isVeryAmpleDivisor_nsmul`: `νL` is very ample for `ν ≫ 0`.
* `MMP.Resolution.Bridges.hasImmersionTwistOver_of_isVeryAmple`,
  `MMP.Resolution.Bridges.isVeryAmple_of_isClosedImmersion` and
  `MMP.Resolution.Bridges.isVeryAmple_of_hasImmersionTwistOver`: the notion
  `MMP.Intersection.IsVeryAmple` against Stacks' immersion data
  `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`.
* `MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule`: the tensor power of an
  invertible module is Stacks' `Stacks.Ample.tensorPowModule`.

## Implementation notes

* Ampleness and very ampleness are the notions `MMP.Intersection.IsAmpleDivisor` and
  `MMP.Intersection.IsVeryAmpleDivisor`, stated through `MMP.CartierDivisor.sheaf`;
  `MMP.Resolution.Bridges.lineBundle_nsmul_iso_tensorPow` identifies `𝒪_X(νL)` with
  `𝒪_X(L)^{⊗ ν}`, and the library side is `Stacks.AmpleRelativeFiniteType.tfae_six` with
  `Stacks.AmpleBridge.isAmple_iff_isAmple`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution.Bridges

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

open MMP.Intersection (IsAmpleDivisor IsVeryAmpleDivisor)

open Stacks.Ample MonoidalCategory in
/-- The tensor power `L^{⊗ n}` of an invertible module is Stacks' `tensorPowModule L n`. -/
theorem nonempty_tensorPow_iso_tensorPowModule (Y : Scheme.{u}) (L : Y.Modules)
    [IsInvertibleModule Y L] (n : ℕ) :
    Nonempty (MMP.Intersection.Scheme.Modules.tensorPow L n ≅ tensorPowModule Y L (n : ℤ)) := by
  induction n with
  | zero => exact ⟨(tensorPowModuleZeroIso Y L).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(tensorIso e (tensorPowModuleOneIso Y L).symm : _ ⊗ L ≅ _) ≪≫
      tensorPowModuleAddIso Y L (n : ℤ) 1 ≪≫ eqToIso (by push_cast; rfl)⟩

open MMP.Intersection (ProjSpace)

/-- A very ample module is pinned to `𝒪(1)` along an immersion into Stacks' projective space. -/
theorem hasImmersionTwistOver_of_isVeryAmple (M N : X.Modules)
    (hva : MMP.Intersection.IsVeryAmple k M) (e : N ≅ M) :
    Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver (X ↘ Spec (.of k)) N := by
  obtain ⟨n, ι, hι, hover, ⟨e'⟩⟩ := hva
  refine ⟨n, ι ≫ (ProjSpace.isoProjectiveSpaceOver k n).hom, ?_, ?_, ⟨?_⟩⟩
  · have : IsClosedImmersion ι := hι
    infer_instance
  · rw [Category.assoc, ProjSpace.isoProjectiveSpaceOver_hom_fst, hover]
  · exact e ≪≫ e' ≪≫ (Scheme.Modules.pullback ι).mapIso
      (ProjSpace.twistOneIsoPullback k n).symm ≪≫
      (Scheme.Modules.pullbackComp ι (ProjSpace.isoProjectiveSpaceOver k n).hom).app _

/-- A closed immersion into Stacks' projective space over `k`, compatible with the structure
morphisms and pinning `𝒪(1)` to `N ≅ M`, makes `M` very ample. -/
theorem isVeryAmple_of_isClosedImmersion (M N : X.Modules) (e : M ≅ N) (n : ℕ)
    (i : X ⟶ projectiveSpaceOver n (Spec (.of k)))
    [IsClosedImmersion i] (hover : i ≫ Limits.pullback.fst _ _ = X ↘ Spec (.of k))
    (e' : N ≅ (Scheme.Modules.pullback i).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k)))) :
    MMP.Intersection.IsVeryAmple k M := by
  set E := ProjSpace.isoProjectiveSpaceOver k n
  have hfst : (i ≫ E.inv) ≫ ProjSpace.toSpec k (ULift.{u} (Fin (n + 1))) = X ↘ Spec (.of k) := by
    rw [Category.assoc, (Iso.inv_comp_eq _).2 (ProjSpace.isoProjectiveSpaceOver_hom_fst k n).symm,
      hover]
  refine ⟨n, i ≫ E.inv, inferInstance, hfst, ⟨?_⟩⟩
  have t1 : (Scheme.Modules.pullback E.inv).obj (ProjSpace.twistOne k (ULift.{u} (Fin (n + 1)))) ≅
      Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k)) :=
    (Scheme.Modules.pullback E.inv).mapIso (ProjSpace.twistOneIsoPullback k n).symm ≪≫
      (Scheme.Modules.pullbackComp E.inv E.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr E.inv_hom_id).app _ ≪≫ (Scheme.Modules.pullbackId _).app _
  exact e ≪≫ e' ≪≫ (Scheme.Modules.pullback i).mapIso t1.symm ≪≫
    (Scheme.Modules.pullbackComp i E.inv).app _

/-- Conversely, over a proper scheme an immersion into Stacks' projective space pinning `𝒪(1)`
makes the module very ample: the immersion is proper, hence a closed immersion. -/
theorem isVeryAmple_of_hasImmersionTwistOver [IsProper (X ↘ Spec (.of k))]
    (M N : X.Modules) (e : M ≅ N)
    (h : Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver (X ↘ Spec (.of k)) N) :
    MMP.Intersection.IsVeryAmple k M := by
  obtain ⟨n, i, hi, hover, ⟨e'⟩⟩ := h
  have : IsImmersion i := hi
  have : IsProper i := by
    have : IsProper (i ≫ Limits.pullback.fst _ _) := by rw [hover]; infer_instance
    exact IsProper.of_comp _ (Limits.pullback.fst _ _)
  have : IsClosedImmersion i :=
    IsClosedImmersion.of_isPreimmersion _ i.isClosedMap.isClosed_range
  exact isVeryAmple_of_isClosedImmersion k M N e n i hover e'

/-- **Every sufficiently high ample power on a proper scheme is very ample.** Let `X` be a proper
scheme over a field `k` and `L` an ample Cartier divisor. Then `νL` is very ample for all
`ν ≫ 0`. -/
@[mmp "lem_mmp_foundation_proper_ample_powers_very_ample"]
theorem eventually_isVeryAmpleDivisor_nsmul [IsProper (X ↘ Spec (.of k))]
    (L : X.CartierDivisor) (hL : IsAmpleDivisor k L) :
    ∀ᶠ ν : ℕ in Filter.atTop, IsVeryAmpleDivisor k (ν • L) := by
  classical
  set M := MMP.CartierDivisor.sheaf L with hM
  haveI hinv : Stacks.Ample.IsInvertibleModule X M :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso
      (Iso.refl (MMP.CartierDivisor.sheaf L)).symm (MMP.Mori.isInvertible_cartierSheaf L)
  obtain ⟨m, hm, hva⟩ := hL
  obtain ⟨eP⟩ := nonempty_tensorPow_iso_tensorPowModule X M m
  have h5 : ∃ d : ℕ, 1 ≤ d ∧ Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver
      (X ↘ Spec (.of k)) (Stacks.Ample.tensorPowModule X M (d : ℤ)) :=
    ⟨m, hm, hasImmersionTwistOver_of_isVeryAmple k _ _ hva eP.symm⟩
  have htfae := Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of k)) M
  have hample : Stacks.Ample.IsAmple X M := (htfae.out 5 1).1 h5
  obtain ⟨d₀, -, hd₀⟩ := (htfae.out 1 6).1 hample
  rw [Filter.eventually_atTop]
  refine ⟨d₀, fun ν hν => ?_⟩
  obtain ⟨eP'⟩ := nonempty_tensorPow_iso_tensorPowModule X M ν
  obtain ⟨eN⟩ := MMP.Resolution.Bridges.lineBundle_nsmul_iso_tensorPow L ν
  exact isVeryAmple_of_hasImmersionTwistOver k _ _ (eN ≪≫ eP') (hd₀ ν hν)

end MMP.Resolution.Bridges
