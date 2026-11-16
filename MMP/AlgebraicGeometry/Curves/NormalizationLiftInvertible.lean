module

public import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothModelOverPerfectField
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitzGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.NormalizationIsoRegularLocus
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle

/-!
# The normalization of a curve: lifting invertible sheaves, and smoothness

Let `C` be a reduced scheme of finite type over a field `k` of dimension at most one, and let
`ν : Cᵛ ⟶ C` be its normalization. Then `ν` is finite and is an isomorphism over the regular
locus of `C`, whose complement is a finite set of closed points; so every invertible sheaf on
`Cᵛ` descends along `ν` to an invertible sheaf on `C` ([Stacks, Tag 0C0T]).

Moreover, let `C` be a proper curve over a field `k`, with structure morphism `f : C ⟶ Spec k`,
and let `ν : Cᵛ ⟶ C` be its normalization. Then `Cᵛ` is again a curve over `k` through `ν ≫ f`;
it is normal of dimension one, hence regular, and over a perfect field regularity is smoothness.
So `ν ≫ f` is smooth, and the sheaf of differentials `Ω_{Cᵛ/k}` is invertible.

## Main results

* `MMP.Fourfold.liftsInvertible_normalization_of_topologicalKrullDim_le_one`: the
  normalization of a reduced curve over a field lifts invertible sheaves.
* `MMP.Fourfold.isCurve_normalization_comp`: `Cᵛ` is a curve over `k`.
* `MMP.Fourfold.smooth_normalization_comp`: over a perfect field `ν ≫ f` is smooth.
* `MMP.Fourfold.isInvertible_relativeDifferentials_normalization_comp`: over a perfect field
  `Ω_{Cᵛ/k}` is invertible.

## Implementation notes

The normalization is `AlgebraicGeometry.Scheme.normalization C h` for an arbitrary proof `h`
of the finiteness of irreducible components; by proof irrelevance it is the nonsingular
projective model `AlgebraicGeometry.normalizationModel'` of `C`, and the results are read off
from that model.

## References

* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0BY3](https://stacks.math.columbia.edu/tag/0BY3)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

universe u

namespace MMP.Fourfold

/-- **Invertible sheaves lift along the normalization of a reduced curve.** The normalization of
a reduced, quasi-compact scheme locally of finite type over a field, of dimension at most one,
is finite and an isomorphism over the regular locus, whose complement is a finite set of closed
points; so every invertible sheaf on the normalization descends. -/
theorem liftsInvertible_normalization_of_topologicalKrullDim_le_one {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced C] (hdim : topologicalKrullDim C ≤ 1)
    (h : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite) :
    LiftsInvertible (C.normalization h) := by
  have hNagata : IsNagataScheme C := isNagataScheme_of_locallyOfFiniteType_over_field k f
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsFinite (C.normalization h) := isFinite_normalizationOverField k f
  let U : C.Opens := ⟨regularLocus C, isOpen_regularLocus_of_isNagataScheme C hNagata hdim⟩
  haveI : IsIso (C.normalization h ∣_ U) :=
    isIso_morphismRestrict_normalization_of_subset_regularLocus h U le_rfl
  haveI : Finite ((U : Set C)ᶜ : Set C) :=
    (finite_singularLocus_of_compactSpace C hNagata hdim).to_subtype
  haveI : T1Space ((U : Set C)ᶜ : Set C) := by
    refine ⟨fun x => ?_⟩
    rw [show ({x} : Set ((U : Set C)ᶜ : Set C)) = Subtype.val ⁻¹' {x.1} from
      Set.ext fun y => Subtype.ext_iff]
    exact (isClosed_singleton_of_not_mem_regularLocus C hdim x.1 x.2).preimage
      continuous_subtype_val
  haveI : DiscreteTopology ((U : Set C)ᶜ : Set C) := Finite.instDiscreteTopology
  intro L hL
  obtain ⟨M, hM, e⟩ := Stacks.PicFinite.exists_isInvertible_modulePullback_iso
    (C.normalization h) U L hL
  exact ⟨M, hM, e⟩

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
  (h : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite)

/-- The normalization of a proper curve over `k` is a curve over `k`. -/
theorem isCurve_normalization_comp : IsCurve k (C.normalization h ≫ f) :=
  (normalizationModel' k f).isCurve

/-- Over a perfect field, the normalization of a proper curve is smooth over `k`. -/
theorem smooth_normalization_comp [PerfectField k] : Smooth (C.normalization h ≫ f) :=
  (normalizationModel' k f).smooth_structureMap

/-- The sheaf of differentials of the normalization of a proper curve over a perfect field is
invertible. -/
theorem isInvertible_relativeDifferentials_normalization_comp [PerfectField k] :
    SheafOfModules.IsInvertible _ _ (Scheme.Hom.relativeDifferentials (C.normalization h ≫ f)) :=
  haveI := isCurve_normalization_comp f h
  haveI := smooth_normalization_comp f h
  isInvertible_relativeDifferentials_of_isCurve (k := k) _

end MMP.Fourfold

end
