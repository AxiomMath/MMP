/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.SNCPullback
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension

/-!
# Field change preserves the snc triples

Let `(X, I, E) ∈ 𝒯^snc` over a field `K` and `σ : K → L` a field extension. Then the field
change `(X_L, p^*I, p⁻¹E)`, with `X_L = X ×_{Spec K} Spec L` and `p : X_L → X` the projection,
lies in `𝒯^snc` over `L`.

The scheme `X_L` is smooth and of finite type over `L` by base change, and `L` has
characteristic zero. The projection `p` is the base change of the flat morphism
`Spec L → Spec K`, so it is flat. For `y ∈ X_L` over `x ∈ X`, the closed fibre
`𝒪_{X_L,y} / 𝔪_x 𝒪_{X_L,y}` is the local ring at `y` of the fibre `p⁻¹(x)`, which is the
spectrum of `κ(x) ⊗_K L`. Since `κ(x)` is a finitely generated extension of `K` and `K` has
characteristic zero, `κ(x) ⊗_K L` is a regular ring: its regularity after every finitely generated
extension of `K` is detected after the finite purely inseparable ones, and these are trivial in
characteristic zero. The pull-back of the snc divisor and of the ideal then follow as for smooth
pull-back.

## Main results

* `MMP.Resolution.isRegularLocalRing_closedFibre_of_isRegular_fiber`: the closed fibre of a stalk
  map is regular when the fibre of the morphism is a regular scheme.
* `MMP.Resolution.isRegularRing_tensorProduct_of_charZero`: over a field of characteristic zero,
  `κ ⊗_K L` is regular for `κ` finitely generated over `K` and `L` any extension field.
* `MMP.Resolution.isRegular_fiber_pullback_fst`: the fibres of `X ×_{Spec K} Spec L → X` are
  regular, for `X` locally of finite type over `K` of characteristic zero.
* `MMP.Resolution.fieldChange_mem_sncTriples`: field change preserves `𝒯^snc`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.34.2, 3.35]
* [Stacks Project, Tag 0381](https://stacks.math.columbia.edu/tag/0381)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing MMP.Mori
open scoped TensorProduct

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- The closed fibre `𝒪_{Y,y} / 𝔪_{h(y)} 𝒪_{Y,y}` of the stalk map of `h : Y → X` at `y` is a
regular local ring when the fibre `h⁻¹(h(y))` is a regular scheme: it is the local ring of the
fibre at `y`. -/
theorem isRegularLocalRing_closedFibre_of_isRegular_fiber {X Y : Scheme.{u}} (h : Y ⟶ X) (y : Y)
    (hF : IsRegular (h.fiber (h y))) :
    letI := (h.stalkMap y).hom.toAlgebra
    IsRegularLocalRing (ClosedFibre (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)) := by
  let := (h.stalkMap y).hom.toAlgebra
  have hreg := ((isRegular_tfae (h.fiber (h y))).out 1 2).mp hF
  have := hreg.2 (h.asFiber y)
  exact IsRegularLocalRing.of_ringEquiv (quotientStalkEquivFiberStalk h y).symm

/-- Over a field `K` of characteristic zero, `κ ⊗_K L` is a regular ring for every finitely
generated field extension `κ/K` and every field extension `L/K`. -/
theorem isRegularRing_tensorProduct_of_charZero (K : Type u) (κ : Type u) (L : Type*) [Field K]
    [CharZero K] [Field κ] [Field L] [Algebra K κ] [Algebra K L] [Algebra.EssFiniteType K κ] :
    IsRegularRing (κ ⊗[K] L) := by
  refine (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    K L).mpr (fun K' _ _ _ _ => ?_) κ
  have hbij : Function.Bijective (algebraMap K K') :=
    ⟨(algebraMap K K').injective, IsPurelyInseparable.surjective_algebraMap_of_isSeparable K K'⟩
  let e : K' ≃ₐ[K] K := (AlgEquiv.ofBijective (Algebra.ofId K K') hbij).symm
  exact IsRegularRing.of_ringEquiv ((Algebra.TensorProduct.congr e AlgEquiv.refl).trans
    (Algebra.TensorProduct.lid K L)).toRingEquiv.symm

/-- For `X` locally of finite type over a field `K` of characteristic zero and `σ : K → L` a field
extension, the fibres of the projection `X ×_{Spec K} Spec L → X` are regular: the fibre over `x`
is the spectrum of `κ(x) ⊗_K L`. -/
theorem isRegular_fiber_pullback_fst {K L : Type u} [Field K] [CharZero K] [Field L]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] (σ : K →+* L)
    (x : X) : IsRegular ((pullback.fst sX (Spec.map (CommRingCat.ofHom σ))).fiber x) := by
  let h := pullback.fst sX (Spec.map (CommRingCat.ofHom σ))
  let : Algebra K L := σ.toAlgebra
  let : Algebra K (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : Algebra.EssFiniteType K (X.residueField x) := residueField_essFiniteType K sX x
  have hpaste : IsPullback (h.fiberToSpecResidueField x) (h.fiberι x ≫ pullback.snd _ _)
      (X.fromSpecResidueField x ≫ sX) (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsPullback.of_hasPullback h (X.fromSpecResidueField x)).flip.paste_vert
      (IsPullback.of_hasPullback sX (Spec.map (CommRingCat.ofHom σ)))
  rw [← SpecMap_algebraMap_residueField sX x] at hpaste
  exact IsRegular.of_iso (hpaste.isoPullback ≪≫ pullbackSpecIso K (X.residueField x) L)
    ((isRegular_spec_iff _).2 (isRegularRing_tensorProduct_of_charZero K (X.residueField x) L))

/-- **Field change preserves the domain `𝒯^snc`** (Kollár 3.34.2, 3.35). Let `(X, I, E) ∈ 𝒯^snc`
over `K` and `σ : K → L` a field extension. Then the field change `(X_L, p^*I, p⁻¹E)` lies in
`𝒯^snc` over `L`. -/
@[mmp "lem_kr3b_field_change_preserves_domain"]
theorem fieldChange_mem_sncTriples {t : FieldBlowupTriple.{u}} (ht : t ∈ sncTriples)
    {L : Type u} [Field L] (σ : t.k →+* L) : t.fieldChange σ ∈ sncTriples := by
  obtain ⟨hchar, hsm, hlft, hqc, hI, -, hE⟩ := ht
  have hcharL : CharZero L := (RingHom.charZero_iff σ.injective).mp hchar
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr inferInstance
  have : Smooth t.sX := (isSmoothScheme_iff _).1 hsm
  obtain ⟨hlftL, hqcL⟩ := t.fieldChange_finiteType σ
  let p := t.fieldChangeProj σ
  have hsmL : Smooth (t.fieldChange σ).sX :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange @Smooth).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹Smooth t.sX›
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let : Algebra t.k L := σ.toAlgebra
    exact (inferInstance : Module.Flat t.k L)
  have : Flat p :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange @Flat).of_isPullback
      (IsPullback.of_hasPullback _ _).flip ‹_›
  have : PerfectField (t.fieldChange σ).k := (PerfectField.ofCharZero : PerfectField L)
  have hY : IsSNCFamily (t.fieldChange σ).sX (fun i => (t.E.E i).comap p) :=
    isSNCFamily_comap_of_flat t.sX (t.fieldChange σ).sX p (fun y => Flat.stalkMap p y)
      (fun y => isRegularLocalRing_closedFibre_of_isRegular_fiber p y
        (isRegular_fiber_pullback_fst t.sX σ (p y))) hE
  show CharZero L ∧ IsSmoothScheme (t.fieldChange σ).sX ∧
    LocallyOfFiniteType (t.fieldChange σ).sX ∧ QuasiCompact (t.fieldChange σ).sX ∧
    IsNonzeroAtGenericPoints (t.I.comap p) ∧ (t.E.comap p).IsOrderedDivisor ∧
    (t.E.comap p).IsSNC (t.fieldChange σ).sX
  exact ⟨hcharL, (isSmoothScheme_iff _).2 hsmL, hlftL, hqcL,
    isNonzeroAtGenericPoints_comap_of_flat p hI,
    fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _
        (hY.exists_stalk_eq_span_parameter i),
      isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
        (hY.exists_stalk_eq_span_parameter i)⟩, hY⟩

end MMP.Resolution
